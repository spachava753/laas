package main

import (
	"context"
	"fmt"
	"net/netip"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

const realDockerEnv = "LAAS_GOLANG_DOCS_REAL_DOCKER"
const evalRootEnv = "LAAS_GOLANG_DOCS_ROOT"
const sidecarService = "harbor-docker-egress-control-sidecar"

type composeAction struct {
	Project string
	Action  string
}

// dnsAction recognizes only Harbor compose operations rooted in this eval
// directory. Startup and allowlist changes rebuild the sidecar's DNS rules;
// public/no-network changes and unrelated Docker commands are left untouched.
func dnsAction(args []string, root string) composeAction {
	if len(args) == 0 || args[0] != "compose" {
		return composeAction{}
	}
	project, dir := "", ""
	for i := 1; i < len(args); i++ {
		switch args[i] {
		case "--project-name", "--project-directory", "-f":
			if i+1 >= len(args) {
				return composeAction{}
			}
			flag := args[i]
			i++
			if flag == "--project-name" {
				project = args[i]
			}
			if flag == "--project-directory" {
				dir = args[i]
			}
		case "up", "exec":
			rel, err := filepath.Rel(root, dir)
			if err != nil || project == "" || dir == "" || !filepath.IsLocal(rel) {
				return composeAction{}
			}
			if args[i] == "up" {
				return composeAction{project, "up"}
			}
			for j := i + 1; j+2 < len(args); j++ {
				if args[j] == sidecarService && args[j+1] == "network-policy" && args[j+2] == "allow" {
					return composeAction{project, "allow"}
				}
			}
			return composeAction{}
		case "build", "down", "stop", "cp", "ps", "config", "logs":
			return composeAction{}
		}
	}
	return composeAction{}
}

// upstreamNameservers accepts only the resolver IPs recorded by Docker, never
// hostnames, port expressions, scoped addresses, or shell syntax.
func upstreamNameservers(text string) ([]netip.Addr, error) {
	addresses := []netip.Addr{}
	seen := map[netip.Addr]bool{}
	for _, line := range strings.Split(text, "\n") {
		if !strings.HasPrefix(line, "# ExtServers: [") || !strings.HasSuffix(line, "]") {
			continue
		}
		values := strings.TrimSuffix(strings.TrimPrefix(line, "# ExtServers: ["), "]")
		for _, value := range strings.Fields(values) {
			if strings.HasPrefix(value, "host(") && strings.HasSuffix(value, ")") {
				value = value[5 : len(value)-1]
			}
			address, err := netip.ParseAddr(value)
			if err != nil || address.Zone() != "" {
				return nil, fmt.Errorf("invalid Docker upstream DNS address")
			}
			if !seen[address] {
				addresses = append(addresses, address)
				seen[address] = true
			}
		}
	}
	return addresses, nil
}

func dnsRules(addresses []netip.Addr) string {
	var rules strings.Builder
	for _, address := range addresses {
		family := "ip"
		if address.Is6() {
			family = "ip6"
		}
		for _, protocol := range []string{"udp", "tcp"} {
			fmt.Fprintf(&rules, "insert rule inet gost_egress output %s daddr %s %s dport 53 return\n", family, address, protocol)
			fmt.Fprintf(&rules, "insert rule inet gost_egress egress %s daddr %s %s dport 53 accept\n", family, address, protocol)
		}
	}
	return rules.String()
}

// repairDNS modifies only this project's Harbor sidecar network namespace.
// It preserves the SNI allowlist and changes only DNS to configured upstreams;
// checking the existing policy prevents relaxing public or deny-all behavior.
func repairDNS(ctx context.Context, docker, project string) error {
	query := exec.CommandContext(ctx, docker, "ps", "-q", "--filter", "label=com.docker.compose.project="+project, "--filter", "label=com.docker.compose.service="+sidecarService)
	data, err := query.Output()
	if err != nil {
		return fmt.Errorf("could not locate Harbor DNS sidecar")
	}
	containers := strings.Fields(string(data))
	if len(containers) == 0 {
		return nil
	}
	if len(containers) != 1 {
		return fmt.Errorf("ambiguous Harbor DNS sidecar")
	}
	id := containers[0]
	policy, err := exec.CommandContext(ctx, docker, "exec", id, "network-policy", "show").Output()
	if err != nil {
		return fmt.Errorf("could not inspect sidecar policy")
	}
	if !strings.Contains(string(policy), "mode: controlled egress") || strings.Contains(string(policy), "(empty:") {
		return nil
	}
	resolver, err := exec.CommandContext(ctx, docker, "exec", id, "awk", "/^# ExtServers:/ {print}", "/etc/resolv.conf").Output()
	if err != nil {
		return fmt.Errorf("could not inspect Docker DNS configuration")
	}
	addresses, err := upstreamNameservers(string(resolver))
	if err != nil {
		return err
	}
	if len(addresses) == 0 {
		return nil
	}
	command := exec.CommandContext(ctx, docker, "exec", "-i", id, "nft", "--file", "-")
	command.Stdin = strings.NewReader(dnsRules(addresses))
	if err := command.Run(); err != nil {
		return fmt.Errorf("could not apply sidecar DNS exceptions")
	}
	return nil
}

// dockerShim delegates every command to the real Docker CLI. Only successful
// Harbor policy/start operations receive the narrow DNS compatibility fix.
// Argument lists are never logged because exec arguments can include secrets.
func dockerShim(ctx context.Context, args []string) error {
	docker := os.Getenv(realDockerEnv)
	if !filepath.IsAbs(docker) {
		return fmt.Errorf("real Docker path must be absolute")
	}
	command := exec.CommandContext(ctx, docker, args...)
	command.Stdin = os.Stdin
	command.Stdout = os.Stdout
	command.Stderr = os.Stderr
	if err := command.Run(); err != nil {
		return err
	}
	action := dnsAction(args, os.Getenv(evalRootEnv))
	if action.Project != "" {
		return repairDNS(ctx, docker, action.Project)
	}
	return nil
}

func harborCommand() ([]string, error) {
	if harbor, err := exec.LookPath("harbor"); err == nil {
		version, err := exec.Command(harbor, "--version").Output()
		if err != nil || strings.TrimSpace(string(version)) != harborVersion {
			return nil, fmt.Errorf("Harbor %s is required; use the pinned uvx fallback or install that version", harborVersion)
		}
		return []string{harbor}, nil
	}
	uvx, err := exec.LookPath("uvx")
	if err != nil {
		return nil, fmt.Errorf("install Harbor %s or put uvx on PATH", harborVersion)
	}
	return []string{uvx, "--from", "harbor==" + harborVersion, "harbor"}, nil
}

// runHarbor invokes Harbor as an external CLI, supplying absolute job paths.
// An ephemeral Docker shim in the child PATH implements the DNS workaround
// without importing Python, changing installed Harbor, or editing host rules.
func runHarbor(ctx context.Context, root string, args []string) error {
	root, err := filepath.Abs(root)
	if err != nil {
		return err
	}
	docker, err := exec.LookPath("docker")
	if err != nil {
		return err
	}
	docker, err = filepath.Abs(docker)
	if err != nil {
		return err
	}
	binary, err := os.Executable()
	if err != nil {
		return err
	}
	cache := filepath.Join(root, ".cache")
	if err := os.MkdirAll(cache, 0o755); err != nil {
		return err
	}
	shim, err := os.MkdirTemp(cache, "docker-shim-")
	if err != nil {
		return err
	}
	defer os.RemoveAll(shim)
	if err := os.Symlink(binary, filepath.Join(shim, "docker")); err != nil {
		return err
	}
	prefix, err := harborCommand()
	if err != nil {
		return err
	}
	arguments := append(prefix[1:], "run", "--env", "docker", "--jobs-dir", filepath.Join(root, "jobs"))
	arguments = append(arguments, args...)
	command := exec.CommandContext(ctx, prefix[0], arguments...)
	command.Env = append(os.Environ(), "PATH="+shim+string(os.PathListSeparator)+os.Getenv("PATH"), realDockerEnv+"="+docker, evalRootEnv+"="+root)
	command.Stdin = os.Stdin
	command.Stdout = os.Stdout
	command.Stderr = os.Stderr
	return command.Run()
}
