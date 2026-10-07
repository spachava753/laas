# Trace-based skill reflection

Previous skill revisions used manual comment/reference comparisons and selected
trace checks. They did not receive independent per-trace diagnoses. Do not treat
that earlier process as equivalent to the workflow below.

## Review one trace per fresh thread

Use GPT 6.1 Sol at high. Batch up to ten reviewer threads concurrently, but each
reviewer sees exactly one trace and has no previous review history. Stop/archive
workers after collecting their report; retain the report and thread ID locally.
Do not fork an agent's conversation or seed a reviewer with the tuning discussion.

Use `review-packet` to prepare a completed development trace, its observable
messages/tool calls/results, the agent-visible repository, task instructions, and
paired reference/candidate comments. The packet excludes scores, explicit condition
labels, other traces, host config, credentials, and private reasoning. A skill read
visible in the trace can still reveal its availability; do not claim full blinding. Secret-field and
string redaction is a precaution; never load an actual credential file to build a
packet. Task-specific code and reference text are allowed in the review packet,
not in the skill.

Review against source and the task, not just the reference. Ask for up to five
findings with trace-step and source-line evidence, observed behavior, inferred
cause, confidence, and a general remedy. A valid paraphrase or code-supported
addition is not an agent failure merely because its judge score was low.
Reviewers may report no material failure. They write only their report, not code
or a skill change, and must not inspect other jobs, scores, or holdout tasks.

## Initial buckets

1. Contract omission: material purpose, precondition, default, ownership,
   lifetime, or interaction missing from the comment.
2. Unsupported claim: contradiction or a promise the evidence does not establish.
3. Evidence gathering: relevant available evidence missed or misinterpreted.
4. Scope/tool failure: unrelated edits, invalid comment attachment, or failed tools.
5. Presentation: unclear hierarchy or verbosity that actually harms API use.
6. Reference/grader issue: wrong reference, unfair paraphrase scoring, or insufficient
   judge context. This normally calls for evaluator review, not a skill perturbation.

`no_material_failure` is a disposition, not another problem bucket. Findings can
have multiple causes; distinguish the visible symptom from the inferred cause.
Merge or split buckets only when evidence warrants it, not to manufacture a taxonomy.

## Aggregate before editing

Collect reports into a matrix of trace, task, bucket, evidence strength, and
recommended action. Count affected traces and distinct tasks separately, so three
repetitions of one task do not look like three independent general failures.
Check reports against the actual trace/source, resolve contradictions, and reject
remedies that contain task identifiers, reference wording, paths, or grading tricks.

Prioritize repeated, high-confidence, caller-visible problems. A score difference
alone is not enough. Keep grader disagreements separate from agent failures.
If the reviewers find that the comments are correct, investigate the evaluator
rather than forcing a skill update.

## Small controlled perturbations

For learning, start with two or three development tasks that exercise different
API forms. Run three fresh attempts per task, with and without the proposed skill
revision under identical settings. Use one change hypothesis per revision, such
as improving contract discovery, avoiding unsupported promises, or checking an
operation's own responsibilities. Describe the expected improvement before launch.

Review each materially flawed trace independently, including a correct comparison
where useful. Change only the general skill, not task instructions or the rubric
in the same comparison. Commit the hypothesis, revision, and sanitized result.
Expand to the full development set only after repeat evidence supports the change.
Freeze before validation; do not tune on the original holdout, which is now open.

The currently running Sol jobs remain fixed replications with two attempts on all
12 tasks. They are not skill-learning batches and are not changed halfway through.
The first reflection pilot reviews one completed trace per condition for three
development tasks (six fresh reviewer threads). Further repetitions belong to the
focused learning experiment, not a silent modification of the replication.

## First independent pilot

Six Sol/high reviewers completed one trace each for three development tasks,
with one no-skill and one frozen-skill trace per task. Scores and explicit condition
labels were withheld, but trace actions could reveal skill use. All workers were archived and stopped after collection.

Counts of traces with a finding (buckets can overlap):

| Bucket | Traces |
| --- | ---: |
| Contract omission | 2 |
| Unsupported claim | 1 |
| Evidence gathering | 0 |
| Scope/tool failure | 1, recovered |
| Presentation | 0 |
| Reference/grader issue | 3 |

There was also a narrow edge-case overstatement shared by a candidate and its
reference. Source-supported additions were often useful rather than mistakes.
Two reviewers found no material failure at all. The true omissions included a
constraint on combining dependent inputs and a side effect on a returned object.
The edit-verification defect recovered before completion.

The parent checked the cited implementation branches and tests for the reference
and omission findings. All six reviewers declined to recommend a skill change.
This supports **investigating reference/grader calibration before another broad
prompt rewrite**, not treating every low score as an agent failure. It does not
prove that every generated comment is correct or that the evaluator is always wrong.

Sanitized findings and reviewer IDs are in `results/reflection-sol-pilot.json`.
Raw packets and detailed reports remain ignored. The skill is unchanged.

## Commands

```sh
go run ./evals/golang-docs review-packet \
  --task <development-task> --trial <completed-trial> --output <fresh-packet>
bb thread spawn --project <project> --environment <environment> --parent-self \
  --provider pi --model openai-codex/gpt-6.1-sol --reasoning-level high \
  --prompt-file <packet>/reviewer-prompt.md --json
bb thread wait <reviewer-thread> --timeout 20m
bb thread output <reviewer-thread>
bb thread archive <reviewer-thread>
bb thread stop <reviewer-thread>
```

Raw reports and packets stay under the ignored cache. Commit only vetted generic
findings and counts; never copy task answers into the skill.
