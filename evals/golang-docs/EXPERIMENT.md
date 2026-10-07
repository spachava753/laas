# Codex documentation skill experiment

## Fixed protocol

Use Harbor 0.24.0 and Codex 0.156.1 with `openai/gpt-6-luna`, reasoning effort
`xhigh`, and web search disabled. A native Codex rollout confirmed the model,
effort, and CLI version. Each trial starts in a fresh container/session. No host
Codex configuration, other skills, reference answers, or past rollouts are loaded.

Run two attempts on each of the six development tasks, concurrency two, agent
timeout 900 seconds, verifier timeout 300 seconds. Keep source snapshots,
instructions, judge rubric/model, and network restrictions unchanged. Skill
availability is the only intended difference. Report exceptions separately; do
not turn infrastructure failures into documentation scores.

The development Oracle mean is **0.92875** from one restoration per task. It is a
probabilistic reference control, not an exact ceiling. The initial stopping rule
is within 0.02 of that mean, or two successive revisions gaining less than 0.01.
Start with at most three skill revisions; do not keep searching merely for a lucky
high judge draw. Prefer an earlier, simpler version when changes lack evidence.
Two attempts on six tasks are a small pilot, not a significance claim.

Inspect per-member scores, omissions, unsupported claims, and native transcripts.
Generalize lessons into documentation practice, never into repository-specific
answers. The skill must contain no dataset repositories, declaration identifiers,
literal task paths, upstream comment text, grading instructions, or target scores.
Its conventions are checked against the official [Go doc-comment guide](https://go.dev/doc/comment).

Freeze the selected skill before comparing baseline and skill-assisted holdout
runs. Do not tune from holdout output. Store raw jobs locally, and commit only
sanitized summaries, general observations, settings, and skill revisions.

## Runs

The connectivity/configuration smoke trial scored **0.51**. It is excluded from
the paired development baseline. It omitted public-contract qualifications and
added incidental implementation claims. The first completed development examples
show the same pattern: useful purpose statements, but incomplete restrictions,
ownership and option interactions. The initial skill emphasizes evidence-backed
contracts and a fact-by-fact review rather than signature narration.

The completed no-skill development baseline scored **0.5964** across 12 trials,
with zero exceptions. Task means ranged from **0.5775** to **0.6438**. Failures
included omitted preconditions and mutation/lifetime restrictions, missed copying
and option interactions, and extended descriptions that did not replace missing
core facts. Some semantically equivalent short purpose statements also scored
below their restored references, a reason not to treat this judge as infallible.

| Development condition | Trials | Exceptions | Mean |
| --- | ---: | ---: | ---: |
| No skill | 12 | 0 | 0.5964 |
| Skill v1 | 12 | 0 | 0.6067 |
| Skill v2 | 12 | 0 | 0.5816 |
| Skill v3 | 12 | 0 | 0.5680 |

Version 1 was read by Codex in all 12 trials. Its aggregate gain of **0.0103**
is small relative to between-attempt variation, and task-level changes were mixed.
It helped some field/operation descriptions, but still encouraged long incidental
claims and missed essential callback responsibilities. Version 2 strengthens
input/result data-flow tracing and a minimal-complete-contract drafting pass.
These are general practices, not answers or examples from the dataset.

Version 2 was read in all 12 trials but regressed to **0.5816**. More guidance
and a broader investigation checklist did not produce better scores. Version 3
cuts the skill to a compact evidence checklist, minimal-contract drafting, and
completeness review. A no-skill holdout job ran independently, with its output
sealed until development-only skill selection was complete.

Version 3 scored **0.5680**, below versions 1 and 2. The native command audit
found an explicit skill-file read in 11 of its 12 trials; skill availability was
consistent, but discovery does not guarantee that every agent reads the body.
Versions 1 and 2 each had an explicit read in all trials.

Development tuning stopped at this plateau: two successive revisions failed to
improve the development best by 0.01. **v1** from commit `931a47e` was restored
and frozen in commit `7803362` before inspecting holdout output. Its **0.0103** development gain is
small and selected from three variants, so it is not evidence of a reliable
improvement. The Oracle level was not reached.

| Holdout condition | Trials | Exceptions | Mean |
| --- | ---: | ---: | ---: |
| No skill | 12 | 0 | 0.5561 |
| Frozen skill v1 | 12 | 0 | 0.5125 |

Codex explicitly read the frozen skill in all 12 holdout trials. The holdout
change was **−0.0436**, not an improvement. No skill revisions were made after
opening holdout results. Across the six comparison jobs, **72 trials** completed
with zero exceptions; the separate configuration smoke adds one more trial.

**Conclusion: this skill has not demonstrated a general score improvement.**
Its best development gain did not transfer to the holdout. Keep the selected
revision as an experimental, general guidance artifact, not a proven upgrade.
Further work should use new development examples and human-reviewed comment
quality/calibration rather than repeatedly tuning against the now-open holdout.
In particular, investigate the judge's treatment of correct paraphrases and
code-supported additions before reading small score differences as quality gains.

Configuration, revision commits, skill hash, and job names are recorded in
`experiment.json`; sanitized aggregates are saved in `results/`. Raw rollouts,
candidates, references, and responses remain ignored. The skill leakage checks,
repository race tests, `go vet`, and `laas` pass. A newly generated standalone
verifier module also builds successfully. No commits were pushed and no jobs or
results were uploaded.

## GPT 6.1 Sol follow-up

At the user's request, repeat the no-skill versus frozen-v1 comparison with
`openai/gpt-6.1-sol` at `high` reasoning. Change only the agent model and effort
relative to the Luna experiment; the Decisions judge remains `gpt-6-luna`.
Use the same Codex version, two attempts per task, timeouts, and source snapshots.
Run all 12 tasks in each condition and report development and original holdout
separately. The skill is not revised or selected again. The original holdout has
already been opened, so this is a fixed-skill replication, not a new unseen test.

The two jobs may run concurrently, each with concurrency two. Settings and job
names are in `experiment-sol.json`. Results are pending.

## Reproduce

From the repository root, with the authorized key in the ignored `.env`:

```sh
go run ./evals/golang-docs run \
  -p evals/golang-docs/tasks -i 'jsonschema-*' \
  -a codex -m openai/gpt-6-luna \
  --ak version=0.156.1 --ak reasoning_effort=xhigh --ak web_search=disabled \
  --agent-timeout-multiplier 3 --env-file .env -k 2 -n 2 -y
```

For a skill-assisted run, add `--skills skills/golang-docs` and use a distinct
job name. Snapshot the skill before launching; never edit a revision while its
job may still be uploading it. The same refreshed-group launcher described in
the dataset README applies when the current IDE process cannot access Docker.

```sh
go run ./evals/golang-docs summarize --output <report.json> <job-directory>
```

Reported token/cost fields come from Harbor's native Codex trajectory conversion;
price estimates may not match the bill. Confidence and probability distributions
remain in ignored verifier responses. No results are uploaded.
