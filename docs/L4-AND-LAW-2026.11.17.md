# How L4's account of law relates to gov-tla

> https://l4-documentation.readthedocs.io/en/latest/docs/returning-L4-and-law.html
>
> Write up an analysis of how the L4 documentation relates to gov-tla, as
> a derived doc.

(The maintainer's request of 2026.11.17.)

**2026.11.17** · derived · a reading of one external page set against this
repository, not a change to the specs · prepared by Claude at the
maintainer's request · source: *How L4 Approaches Law*, L4 documentation
(© 2023 SMU CCLAW, built with Sphinx 5.3.0), fetched 2026.11.17 · read
against commit `bf8e08f` on `main`: `specs/Constitution.tla` (sha256
`b31449a7bb6d…`), `specs/Elections.tla` (`87692583cde1…`),
`specs/Executive.tla` (`8c1d836f4408…`), `specs/Government.tla`
(`36200c8223b9…`), `specs/Judiciary.tla` (`08090cdddea2…`), `README.md`
and `docs/ASSESSMENT.md`

---

## 1. What this is

L4 is a domain-specific language for law, developed at the Centre for
Computational Law at Singapore Management University (SMU CCLAW). The page read
here, *How L4 Approaches Law*, is in its documentation's "Philosophy
Behind L4's Design" section. It sets out how L4 sees contracts and
legislation. This note summarises that page, then sets each of its claims
beside what gov-tla actually does, citing files.

It is *derived*: everything it says about L4 comes from that one page,
and everything it says about gov-tla comes from the files named above. It
does not use the L4 language reference, specification or papers. Nothing
was run. Quotations from the page are short and attributed. They belong
to their authors and are not covered by this repository's licences.

---

## 2. The page in brief

The page makes nine moves, in order.

1. **L4 is a specification language.** It is a "domain-specific
   modelling language", one kind of "specification language". Such
   languages are "used primarily for analyzing the properties of systems
   even before the systems are implemented or run". The page gives two
   examples: Alloy and **TLA+**.
2. **Law is attempted specification.** "The L4 approach considers
   contracts and legislation to be attempts at specification and models
   these attempts with a formal system." It makes three claims about
   that system:
   - "The behaviour of actors is regulated by rules which describe state
     transition systems. The transitions between states are themselves
     governed by decision rules."
   - Both kinds of rule reduce to first-order logic and "are recursively
     subject to meta-rules like priority ordering".
   - "The evaluation at run-time of decision elements to binary truth
     values is dependent on human input."
3. **Formal languages resolve ambiguity.** "A, B, C and D or E" has at
   least four readings. A formal language makes the drafter choose one,
   because a statement that is not well-formed triggers a compiler
   warning.
4. **Software practice carries over.** Some ambiguities are syntax errors.
   Misunderstandings are failures of requirements elicitation, which
   behaviour-driven development and unit testing can catch before signing.
   Type checking and totality analysis can detect under-specification.
   Version control fixes the "draft version" problem.
5. **Contracts are state machines.** The page cites Petri nets and BPMN
   for this.
6. **Terms resolve to truth values, and that is contested.** Its example
   is "No Vehicles In The Park". Parties "may disagree about the values of
   terms, and further disagree about the choice of logic". Negation as
   failure is one choice, and "vacuous truths may lead to state
   explosion". Unknown and undefined values call for "a ternary logic".
7. **Meta-rules rewrite rules.** Some are inside the text ("any reference
   to dollars shall mean United States Dollars"). Some act on it from
   outside ("any clause … which attempts to establish a non-compete shall
   be unenforceable"). The page compares these to compiler passes, OS
   access control and priority-ordered firewall rules.
8. **Static analysis can find loopholes at drafting time.** "It should be
   possible to identify, at the time of drafting, if a law or contract
   contains undesirable loopholes". The method it names is SAT solving.
9. **There are limits.** Such methods "cannot anticipate meta-rules
   operating outside the bounds of the system", such as a war of foreign
   occupation. Some vagueness is "inevitable, and, frequently,
   desirable". A test like "reasonable efforts" is a decision tree that
   "bottoms out and needs to call an external decider for input".

---

## 3. Where gov-tla already does what the page describes

gov-tla is an instance of the page's thesis in the language the page
names. The README's opening ("The Constitution is, for the most part, a
set of state machines gated by supermajorities") is the page's second move
applied to one text. The correspondence is close, claim by claim:

| L4's claim | gov-tla's counterpart | Where |
|---|---|---|
| Law is a state transition system | Each module is a `Spec` of `Init` and actions over the procedural state | every `specs/*.tla` |
| "Decision rules" govern transitions | Each action's guard. The method makes each property *local*: one guard decides it | `README.md`, "Local properties" |
| Decision elements are settled by "human input" at run time | Votes and choices are action parameters, chosen freely: `Impeach(p, ayes)`, `Convict(p, ayes, dq)` | `specs/Constitution.tla:511-535` |
| Meta-rules rewrite the rule system | Amendments rewrite the text edges. Courts sever statutory edges that a doctrine forbids. `M_UPHOLD` removes judicial review | `specs/Government.tla:17-20`, `:507-535`, `:132` |
| Rules collide and priority orders them | Doctrines (`Buckley`, `SeilaLaw`, `Bowsher`, `Chadha`, `Will`) decide which statutory edges stand | `specs/Government.tla:448-526` |
| Formalisation forces a reading of ambiguous text | The modules fix readings and say where, e.g. Amendment XII's last sentence read without Amendment XXII | `specs/Elections.tla:219-228` |
| Unit tests and BDD catch misunderstandings early | Every check has a mutation that must break exactly the properties it names, and a `Never…` witness for each behaviour the text allows | `README.md`, "Mutations" and "Witnesses" |
| Version control and structured data | Every results file is dated, names the tool version, and gives the sha256 of each module it covers | `results/`, `README.md`, "Evidence" |
| Static analysis finds loopholes before they bite | TLC explores every reachable state at small constants. TLAPS proves `Spec => []P` for all sizes | `README.md`, "Proofs" |

On the "loopholes" claim, gov-tla's results are more specific than the
page. The assessment found that the findings with real constitutional
content "all involve something changing while something else is pending"
(`docs/ASSESSMENT.md`, "Findings with substance"). Examples:

- disqualification checked at nomination but not again at confirmation
  (`M_VP_RECHECK`, `M_CHIEF_RECHECK`);
- Congress excepting a head of jurisdiction while an appeal on it is
  pending (*Ex parte McCardle*);
- the ten-day rule, which needs fairness on the clock rather than on a
  President who may not exist.

None of these is a property of one rule tree evaluated once. Each is a
property of an *interleaving*. So SAT solving over the decision rules, the
method the page names, would not find them. Exploring the state machine
does. The page itself calls law a state machine, so this does not
contradict it. It does sharpen it: the loopholes worth looking for are in
the transitions, not in the decision rules.

---

## 4. Where they differ

### 4.1 Purpose: drafting and running rules, or analysing one fixed text

L4 is for drafting, and for evaluating rules at run time with human
input. The rest of its documentation covers a spreadsheet interface,
transpilers and a backend. gov-tla drafts nothing and runs nothing. It
takes one text as fixed, models its procedure, and checks properties of
that model. The README says what that means: "None of these is a claim
about law or practice." The page's fourth move (catch misunderstandings
*before contract signing*) has no counterpart here. The Constitution was
signed in 1787. gov-tla's mutations look at the alternatives afterwards,
as real earlier law (the Articles of Confederation, *Chisholm*, *Humphrey's
Executor*) rather than as drafts.

### 4.2 The tie to the text

The page's way of resolving ambiguity is a compiler warning: the drafter
writes in L4, and ill-formed text is rejected. In gov-tla no tool checks
the link between a clause and a guard. That link is the provision tables
in the README and the module headers, and only a human reader checks
them. The fixed readings are the author's choices, stated in comments.
The assessment says so: the "Breaks under" matrix "records the module's
own choices, not facts about the law" (`docs/ASSESSMENT.md`, Limits 1).

L4's approach gives better assurance about clause-to-rule fidelity.
gov-tla's gives better assurance about what follows once a reading is
fixed.

### 4.3 Unknowns: a third truth value, or every value

The page argues for "a ternary logic" for unknown and undefined values.
gov-tla is two-valued throughout and handles unknowns by
**nondeterminism**:

- whether a House majority impeaches;
- whether the Senate disqualifies on conviction;
- whether a court hears a challenge;
- which elector is faithless.

Each of these is a free choice, and TLC explores every outcome. A safety
property that holds therefore holds *whatever* the external decider
decides. That is a stronger guarantee than a three-valued answer. But it
is silent on which decision is right, and that is exactly the question a
three-valued evaluator leaves open.

The two choices fit different jobs. A run-time evaluator has to report
"unknown" about a particular case. A model checker can quantify over every
way the unknown might resolve.

### 4.4 Open texture is left out on purpose

The page's examples of open texture ("vehicle", "reasonable efforts")
have constitutional counterparts, and gov-tla abstracts every one of them:

- **Grounds for impeachment.** `Impeach` checks only that `p` is
  impeachable, not already impeached, and has a House majority
  (`specs/Constitution.tla:511-516`). "Treason, Bribery, or other high
  Crimes and Misdemeanors" is not modelled.
- **Eligibility.** Age, residency and natural-born citizenship are
  folded into the constant `Eligible` (`specs/Constitution.tla:168`).
- **Who checks a qualification.** In `Elections.tla` it is checked where
  the office is taken (README, "Abstracted").

This is the page's "external decider", with one difference. In the
Constitution the decider is usually itself an actor in the state machine:
the House, the Senate, a court under `Review`. So the "human input" the
page puts outside the system is, in gov-tla, a transition inside it whose
content is unconstrained. Much of what the Constitution does is name who
decides and by what vote, while leaving the decision open, and gov-tla
models those procedural rules. The open standards themselves are outside
its scope.

### 4.5 Tools and properties

The page names SAT solving and talks about evaluating rules. It does not
mention temporal properties, model checking or proof. gov-tla's evidence
is of three kinds, and the README keeps them apart:

- **Checked**: TLC, every reachable state at given constants.
- **Proved**: TLAPS, every size the named assumptions admit.
- **Sampled**: simulation, never cited as a check.

Some of gov-tla's findings are about liveness, such as
`PresentedBillsResolve` needing fairness on the clock. The page's
framework, which evaluates decision rules, has no place for a property
like that.

### 4.6 "Vacuous truths" and state explosion

The page links vacuous truths to state explosion. gov-tla meets both,
in different senses:

- **Vacuous truth, as gov-tla means it**, is a safety property that holds
  only because the state it forbids is unreachable. The `Never…`
  witnesses exist to rule this out (`README.md`, "Witnesses").
- **State explosion** is real here. The Elections row list takes 71
  minutes in CI. The cause is the mutation × property × constants grid,
  not the logic chosen (`docs/MUTATION-MATRIX-FINDINGS-2026.11.17.md`,
  §2–3).

### 4.7 Rules from outside the system

The page grants that analysis "cannot anticipate meta-rules operating
outside the bounds of the system". gov-tla's version of this limit is its
"Abstracted" lists, plus one structural choice. `Government.tla` puts the
outermost meta-rule *inside* the model: Article V, the only route by
which the text changes (`TextFollowsArticleV`, `ArticleVStands`). Anything
beyond Article V is outside the model, as the page would predict. A
revolution, an occupation or a convention that exceeds its mandate cannot
be represented.

---

## 5. What the comparison suggests

These are possibilities. None is decided, and nothing here commits the
repository to them.

1. **Make the fixed readings switchable.** The page's point that parties
   "disagree about the choice of logic" maps onto gov-tla's fixed
   readings. A `Reading` constant, run through the row list the way `Mut`
   is, would show by TLC which properties depend on which reading. That
   turns an interpretive dispute into a row in the results file.
   `Elections.tla` already goes part way: `NeverThirdTermBySuccession`
   shows what one reading admits.
2. **Index each clause to its guard.** The README's provision tables are
   the nearest thing gov-tla has to L4's tie between text and rule. A
   machine-checked index (clause → identifiers, with a script failing on
   a named identifier that no longer exists) would protect the one link
   the method now leaves to human reading.
3. **Feed this back to the computational-law side.** gov-tla's evidence
   that the substantive findings are interleavings (§3) answers the
   page's loophole claim, and it is the most useful thing this repository
   could tell L4's authors.

---

## 6. Limits of this note

- One page of L4's documentation was read. L4's language reference,
  specification, transpilers and papers were not. Some of the differences
  in §4 may be closed elsewhere in L4: for example, L4 may have temporal
  or deontic constructs that this page does not mention. Each difference
  is stated as one between *this page* and gov-tla.
- The page is dated 2023. The L4 project may have moved on since.
- Every statement about gov-tla's results repeats what the committed
  results files and `docs/ASSESSMENT.md` say. Nothing was re-run.
