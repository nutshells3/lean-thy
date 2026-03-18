import Mathlib

noncomputable section

namespace SafeSlice

structure RawProposal (PId Raw : Type*) where
  proposalId : PId
  candidate : Raw

structure FormalizedProposal (PId Compiled : Type*) where
  proposalId : PId
  form : Compiled

def formalize {PId Raw Compiled : Type*}
    (compile : Raw → Option Compiled)
    (p : RawProposal PId Raw) :
    Option (FormalizedProposal PId Compiled) :=
  (compile p.candidate).map fun c => ⟨p.proposalId, c⟩

abbrev Validator (Compiled : Type*) := Compiled → Prop

def FormalizedProposal.passes {PId Compiled : Type*}
    (v : Validator Compiled)
    (fp : FormalizedProposal PId Compiled) : Prop :=
  v fp.form

structure CertifiedBank (PId Compiled : Type*) where
  validator : Validator Compiled
  members : Set (FormalizedProposal PId Compiled)
  allPass : ∀ fp ∈ members, fp.passes validator

section BankConstruction

variable {PId Raw Compiled : Type*}

def formalizeAll (compile : Raw → Option Compiled)
    (ps : List (RawProposal PId Raw)) :
    List (FormalizedProposal PId Compiled) :=
  ps.filterMap (formalize compile)

def filterByAccept
    (accept : FormalizedProposal PId Compiled → Bool)
    (fps : List (FormalizedProposal PId Compiled)) :
    List (FormalizedProposal PId Compiled) :=
  fps.filter accept

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

theorem soundRetention {PId Compiled : Type*}
    (bank : CertifiedBank PId Compiled)
    (fp : FormalizedProposal PId Compiled)
    (hmem : fp ∈ bank.members) :
    fp.passes bank.validator :=
  bank.allPass fp hmem

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
