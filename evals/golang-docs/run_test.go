package main

import (
	"net/netip"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
)

func TestDNS(t *testing.T) {
	t.Run("upstream addresses", func(t *testing.T) {
		for _, test := range []struct {
			text string
			want []string
		}{
			{"nameserver 127.0.0.11\n", []string{}},
			{"# ExtServers: [172.17.0.1]\n", []string{"172.17.0.1"}},
			{"# ExtServers: [2001:4860:4860::8888 host(8.8.8.8)]", []string{"2001:4860:4860::8888", "8.8.8.8"}},
			{"# ExtServers: [8.8.8.8 8.8.8.8]", []string{"8.8.8.8"}},
		} {
			addresses, err := upstreamNameservers(test.text)
			if err != nil {
				t.Fatal(err)
			}
			actual := []string{}
			for _, address := range addresses {
				actual = append(actual, address.String())
			}
			if !reflect.DeepEqual(actual, test.want) {
				t.Fatalf("addresses %v != %v", actual, test.want)
			}
		}
		for _, value := range []string{"example.com", "8.8.8.8;", "fe80::1%eth0", "8.8.8.8:53"} {
			if _, err := upstreamNameservers("# ExtServers: [" + value + "]"); err == nil {
				t.Fatalf("accepted %q", value)
			}
		}
	})
	t.Run("DNS only", func(t *testing.T) {
		rules := strings.Split(strings.TrimSpace(dnsRules([]netip.Addr{netip.MustParseAddr("172.17.0.1"), netip.MustParseAddr("2001:4860:4860::8888")})), "\n")
		if len(rules) != 8 {
			t.Fatal("wrong rule count")
		}
		for _, rule := range rules {
			if !strings.Contains(rule, "dport 53 ") || !strings.HasPrefix(rule, "insert rule inet gost_egress ") || strings.Contains(rule, "443") {
				t.Fatalf("unsafe rule %q", rule)
			}
		}
	})
	t.Run("scoped lifecycle operations", func(t *testing.T) {
		root := filepath.Join(t.TempDir(), "evals")
		prefix := []string{"compose", "--project-name", "trial__env", "--project-directory", filepath.Join(root, "tasks/task/environment"), "-f", "compose.yaml"}
		for _, test := range []struct {
			args []string
			want string
		}{
			{[]string{"up", "--detach", "--wait"}, "up"},
			{[]string{"exec", "--no-TTY", sidecarService, "network-policy", "allow", "api.openai.com"}, "allow"},
			{[]string{"exec", "--no-TTY", sidecarService, "network-policy", "deny-all"}, ""},
			{[]string{"exec", "--no-TTY", sidecarService, "network-policy", "allow-all"}, ""},
			{[]string{"exec", "main", "echo", "network-policy", "allow"}, ""},
			{[]string{"build"}, ""},
		} {
			args := append(append([]string{}, prefix...), test.args...)
			if got := dnsAction(args, root); got.Action != test.want {
				t.Fatalf("action=%+v expected=%s", got, test.want)
			}
		}
		unrelated := []string{"compose", "--project-name", "other", "--project-directory", filepath.Dir(root), "up"}
		if dnsAction(unrelated, root).Project != "" {
			t.Fatal("unrelated Docker project intercepted")
		}
		if dnsAction([]string{"ps"}, root).Project != "" {
			t.Fatal("ordinary Docker command intercepted")
		}
	})
}
