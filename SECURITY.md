# Security Policy

## What this repository is

gov-tla is a set of TLA+ models of the procedural core of the United
States Constitution, with model-checker results, machine-checked proofs,
and the scripts that regenerate both. It is an exercise, not law.

**Nothing here is deployable.** There is no release, no service and no
packaged artifact. The scripts run TLC and TLAPS over the modules and
write results files; that is all they do.

So the usual notion of a security vulnerability, an exploitable defect in
software people run, mostly does not apply. What can go wrong here is a
claim that the evidence does not back.

## What we most want to hear about: evidence findings

The README says what each property is: checked by TLC at named constants,
proved by TLAPS under named hypotheses, or neither. The results files are
the evidence for those words. An **evidence finding** is any of:

- A property the README calls proved whose proof module does not
  establish it, or establishes it under a hypothesis the README does not
  state.
- A property the README calls checked whose row list does not run it, or
  runs it at constants that exclude the states that matter.
- A mutation the header says must break a property that does not break
  it, or a `Never…` witness that is not actually violated.
- A results file that does not regenerate byte for byte from the module,
  row list and pinned tools it names.
- A pin (`tools/*-PIN`) that does not name the tool CI actually ran.
- A place where a module departs from the constitutional text it claims
  to state in a way a reader would not notice from the header.

These get the same private handling and credit as a conventional
vulnerability would in a shipping project.

Conventional defects in the scripts, the workflow or the visualization
tools are welcome too, through the same channel; say that it is not an
evidence finding. Issues are off in this repository.

## How to report

Please do not open a public issue for an evidence finding until we have
had a chance to look at it.

Use GitHub's private vulnerability reporting for this repository: the
**Security** tab, then **Report a vulnerability**. This opens a private
advisory thread that only you and the maintainer can see.

Please include which module, results file or README statement the finding
is against and the commit you read it at; the claim you believe is wrong;
and why: a counterexample trace, a row that does not reproduce, a failing
obligation, or a written argument.

## What to expect

- Acknowledgement within **5 business days**.
- An initial assessment (agree, disagree, need more) within **15 business
  days** of acknowledgement.
- If the finding is confirmed, the module, results file or README is
  corrected in a commit that names the finding, and you are credited
  unless you ask not to be.
- If we disagree, you get a written reason. You are free to publish after
  the assessment window closes, whatever the outcome.

This is a single-maintainer project. The windows above are what can be
met honestly, not aspirations.

## Scope

In scope: everything tracked in this repository at the current default
branch.

Out of scope: the TLA+ tools, TLAPS and its backends, and the tla-kit
image CI runs them in. Report a problem in one of them to its upstream
project, and tell us as well, so the pin can be moved once upstream has a
fix. Nothing in them is patched here.
