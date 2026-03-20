import Mathlib

noncomputable section

namespace SafeSlice

/-!
# Problem 5 — Certified Proposal Bank with Formal Filtering

Roadmap node: 4B parallel proposal bank with certified formal filtering.

A proposal bank collects candidate formalizations from diverse generators
(LLM agents, humans, solvers). Not every proposal survives compilation and
semantic validation. The certified bank retains only proposals that:

1. **Formalize** — the raw proposal compiles via an abstract compiler.
2. **Validate** — the compiled form satisfies a semantic acceptance criterion.

The key theorem (`soundRetention`) states that every member of the certified
bank genuinely satisfies the acceptance criterion — no unchecked proposals
leak through the filter.

Literature anchors:
- Human-Certified Module Repositories (Enyedi 2026): interface-disciplined
  module curation mirrors BoundaryOK + certified bank filtering.
- Theorem-Carrying Transactions (Ball et al. 2024): proofs travel with
  artifacts, checked at interface boundaries before composition.
-/

/-! ## Abstract compilation and validation interfaces

The proposal bank is parametric over:
- `Raw` : the type of raw proposal candidates
- `Compiled` : the type of successfully compiled forms
- `compile : Raw → Option Compiled` : the compilation function
- `validate : Compiled → Prop` : the semantic acceptance predicate

This lets the bank sit over Problem 3's `compileSlice`/`LocalForm` without
duplicating those definitions. -/

/-- A raw proposal pairs an identifier with a candidate. -/
structure RawProposal (PId Raw : Type*) where
  proposalId : PId
  candidate : Raw

/-- A formalized proposal pairs an identifier with a compiled form. -/
structure FormalizedProposal (PId Compiled : Type*) where
  proposalId : PId
  form : Compiled

/-! ## Formalization interface -/

/-- Try to compile each raw proposal. -/
def formalize {PId Raw Compiled : Type*}
    (compile : Raw → Option Compiled)
    (p : RawProposal PId Raw) :
    Option (FormalizedProposal PId Compiled) :=
  (compile p.candidate).map fun c => ⟨p.proposalId, c⟩

/-! ## Validation interface -/

/-- A `Validator` is a predicate on compiled forms. -/
abbrev Validator (Compiled : Type*) := Compiled → Prop

/-- A formalized proposal passes when the validator accepts its form. -/
def FormalizedProposal.passes {PId Compiled : Type*}
    (v : Validator Compiled)
    (fp : FormalizedProposal PId Compiled) : Prop :=
  v fp.form

/-! ## Certified bank predicate

A certified bank is a set of formalized proposals together with a proof
that every member passes the validator. -/

structure CertifiedBank (PId Compiled : Type*) where
  validator : Validator Compiled
  members : Set (FormalizedProposal PId Compiled)
  allPass : ∀ fp ∈ members, fp.passes validator

/-! ## Bank construction -/

section BankConstruction

variable {PId Raw Compiled : Type*}

/-- Compile all raw proposals, keeping only those that succeed. -/
def formalizeAll (compile : Raw → Option Compiled)
    (ps : List (RawProposal PId Raw)) :
    List (FormalizedProposal PId Compiled) :=
  ps.filterMap (formalize compile)

/-- Filter formalized proposals by a decidable acceptance test. -/
def filterByAccept
    (accept : FormalizedProposal PId Compiled → Bool)
    (fps : List (FormalizedProposal PId Compiled)) :
    List (FormalizedProposal PId Compiled) :=
  fps.filter accept

/-- Build a certified bank from a decidable test that is sound w.r.t. the
semantic validator. -/
def buildCertifiedBank
    (compile : Raw → Option Compiled)
    (v : Validator Compiled)
    (accept : FormalizedProposal PId Compiled → Bool)
    (sound : ∀ fp, accept fp = true → fp.passes v)
    (ps : List (RawProposal PId Raw)) :
    CertifiedBank PId Compiled where
  validator := v
  members := { fp | fp ∈ filterByAccept accept (formalizeAll compile ps) }
  allPass := by
    intro fp hfp
    simp only [filterByAccept, List.mem_filter, Set.mem_setOf_eq] at hfp
    exact sound fp hfp.2

end BankConstruction

/-! ## Sound retention theorem

The main theorem: every proposal retained in a certified bank genuinely
satisfies the validator. -/

theorem soundRetention {PId Compiled : Type*}
    (bank : CertifiedBank PId Compiled)
    (fp : FormalizedProposal PId Compiled)
    (hmem : fp ∈ bank.members) :
    fp.passes bank.validator :=
  bank.allPass fp hmem

/-! ## Formalization soundness

When compilation succeeds, the compiled form is produced by the compiler
applied to the original candidate. -/

theorem formalize_some_iff {PId Raw Compiled : Type*}
    (compile : Raw → Option Compiled)
    (p : RawProposal PId Raw)
    (fp : FormalizedProposal PId Compiled) :
    formalize compile p = some fp ↔
      ∃ c, compile p.candidate = some c ∧
           fp = ⟨p.proposalId, c⟩ := by
  simp only [formalize, Option.map_eq_some_iff]
  constructor
  · rintro ⟨c, hc, hfp⟩
    exact ⟨c, hc, hfp.symm⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩

end SafeSlice
