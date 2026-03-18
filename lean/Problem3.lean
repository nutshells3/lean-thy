import Mathlib

noncomputable section

namespace SafeSlice

structure Bridge (Claim : Type _) where
  premises : Finset Claim
  conclusion : Claim
deriving DecidableEq

def Bridge.WellFormed {Claim : Type _} [DecidableEq Claim]
    (claims exports : Finset Claim) (b : Bridge Claim) : Prop :=
  b.premises ⊆ claims ∧ b.conclusion ∈ exports

structure SliceSyntax (SliceId Claim Question : Type _) where
  sliceId : SliceId
  ambientImports : Finset Claim
  carryImports : Finset Claim
  claims : Finset Claim
  exports : Finset Claim
  certifiedBridges : Finset (Bridge Claim)
  pendingBridges : Finset (Bridge Claim)
  blockedExports : Finset Claim
  clarificationHoles : Finset Question
deriving DecidableEq

def SliceSyntax.WellFormed
    {SliceId Claim Question : Type _} [DecidableEq Claim]
    (s : SliceSyntax SliceId Claim Question) : Prop :=
  s.ambientImports ⊆ s.claims ∧
    s.carryImports ⊆ s.claims ∧
    s.exports ⊆ s.claims ∧
    s.blockedExports ⊆ s.exports ∧
    Disjoint s.certifiedBridges s.pendingBridges ∧
    (∀ b ∈ s.certifiedBridges, b.WellFormed s.claims s.exports) ∧
    (∀ b ∈ s.pendingBridges, b.WellFormed s.claims s.exports)

structure LocalForm (SliceId Claim Question : Type _) [DecidableEq Claim] where
  raw : SliceSyntax SliceId Claim Question
  wellFormed : raw.WellFormed

namespace LocalForm

variable {SliceId Claim Question : Type _} [DecidableEq Claim]

def sliceId (f : LocalForm SliceId Claim Question) : SliceId :=
  f.raw.sliceId

def ambientImports (f : LocalForm SliceId Claim Question) : Finset Claim :=
  f.raw.ambientImports

def carryImports (f : LocalForm SliceId Claim Question) : Finset Claim :=
  f.raw.carryImports

def allImports (f : LocalForm SliceId Claim Question) : Finset Claim :=
  f.ambientImports ∪ f.carryImports

def claims (f : LocalForm SliceId Claim Question) : Finset Claim :=
  f.raw.claims

def exports (f : LocalForm SliceId Claim Question) : Finset Claim :=
  f.raw.exports

def certifiedBridges (f : LocalForm SliceId Claim Question) : Finset (Bridge Claim) :=
  f.raw.certifiedBridges

def pendingBridges (f : LocalForm SliceId Claim Question) : Finset (Bridge Claim) :=
  f.raw.pendingBridges

def blockedExports (f : LocalForm SliceId Claim Question) : Finset Claim :=
  f.raw.blockedExports

def clarificationHoles (f : LocalForm SliceId Claim Question) : Finset Question :=
  f.raw.clarificationHoles

def pendingConclusions (f : LocalForm SliceId Claim Question) : Finset Claim :=
  f.pendingBridges.image Bridge.conclusion

def availableExports (f : LocalForm SliceId Claim Question) : Finset Claim :=
  f.exports.filter fun c => c ∉ f.blockedExports ∧ c ∉ f.pendingConclusions

lemma availableExports_subset_exports (f : LocalForm SliceId Claim Question) :
    f.availableExports ⊆ f.exports := by
  intro c hc
  exact (Finset.mem_filter.mp hc).1

end LocalForm

open Classical in
def compileSlice
    {SliceId Claim Question : Type _} [DecidableEq Claim]
    (s : SliceSyntax SliceId Claim Question) : Option (LocalForm SliceId Claim Question) :=
  if h : s.WellFormed then some ⟨s, h⟩ else none

def BoundaryOK
    {SliceId Claim Question : Type _} [DecidableEq Claim]
    (left right : LocalForm SliceId Claim Question) : Prop :=
  right.carryImports ⊆ left.availableExports

section KernelStability

variable {SliceId Claim Question : Type _} [DecidableEq Claim]

theorem compileSlice_of_wellFormed (s : SliceSyntax SliceId Claim Question) (h : s.WellFormed) :
    ∃ f, compileSlice s = some f ∧ f.raw = s := by
  exact ⟨⟨s, h⟩, dif_pos h, rfl⟩

theorem compileSlice_none (s : SliceSyntax SliceId Claim Question) (h : ¬s.WellFormed) :
    compileSlice s = none := by
  exact dif_neg h

theorem compileSlice_raw (s : SliceSyntax SliceId Claim Question) (f : LocalForm SliceId Claim Question)
    (h : compileSlice s = some f) : f.raw = s := by
  simp only [compileSlice] at h
  split at h
  · simp at h; exact h ▸ rfl
  · simp at h

theorem BoundaryOK_of_empty_carry (left right : LocalForm SliceId Claim Question)
    (h : right.carryImports = ∅) : BoundaryOK left right := by
  unfold BoundaryOK
  rw [h]
  exact Finset.empty_subset _

theorem BoundaryOK_mono_left {l₁ l₂ right : LocalForm SliceId Claim Question}
    (hsub : l₁.availableExports ⊆ l₂.availableExports)
    (hok : BoundaryOK l₁ right) : BoundaryOK l₂ right :=
  Finset.Subset.trans hok hsub

end KernelStability

section CompositionClosure

variable {SliceId Claim Question : Type _} [DecidableEq Claim]

def ComposableChain (chain : List (LocalForm SliceId Claim Question)) : Prop :=
  chain.IsChain (fun l r => BoundaryOK l r)

theorem composableChain_nil :
    ComposableChain ([] : List (LocalForm SliceId Claim Question)) :=
  List.isChain_nil

theorem composableChain_singleton (f : LocalForm SliceId Claim Question) :
    ComposableChain [f] :=
  List.isChain_singleton f

theorem composableChain_append_singleton
    {chain : List (LocalForm SliceId Claim Question)}
    {f : LocalForm SliceId Claim Question}
    (hc : ComposableChain chain)
    (hb : ∀ last ∈ chain.getLast?, BoundaryOK last f) :
    ComposableChain (chain ++ [f]) := by
  unfold ComposableChain at *
  rw [List.isChain_append]
  exact ⟨hc, List.isChain_singleton f, fun a ha b hb' => by
    simp at hb'; subst hb'; exact hb a ha⟩

def chainExports (chain : List (LocalForm SliceId Claim Question)) : Finset Claim :=
  chain.foldr (fun f acc => f.availableExports ∪ acc) ∅

def chainExternalImports (chain : List (LocalForm SliceId Claim Question)) : Finset Claim :=
  match chain with
  | [] => ∅
  | f :: _ => f.ambientImports

theorem chainExports_append_singleton
    (chain : List (LocalForm SliceId Claim Question))
    (f : LocalForm SliceId Claim Question) :
    chainExports (chain ++ [f]) = chainExports chain ∪ f.availableExports := by
  induction chain with
  | nil => simp [chainExports]
  | cons a rest ih =>
    change a.availableExports ∪ chainExports (rest ++ [f]) =
      (a.availableExports ∪ chainExports rest) ∪ f.availableExports
    rw [ih, Finset.union_assoc]

end CompositionClosure

section FragmentBridge

variable {SliceId Claim Question : Type _} [DecidableEq Claim]

def FragmentContained (chain : List (LocalForm SliceId Claim Question)) : Prop :=
  ∀ f ∈ chain, f.availableExports ⊆ f.claims

def FragmentSound (chain : List (LocalForm SliceId Claim Question)) : Prop :=
  ∀ c ∈ chainExports chain, ∃ f ∈ chain, ∃ b ∈ f.certifiedBridges,
    b.conclusion = c

def FragmentComplete (chain : List (LocalForm SliceId Claim Question)) : Prop :=
  ∀ f ∈ chain, ∀ b ∈ f.certifiedBridges,
    b.conclusion ∈ chainExports chain

def FragmentAdmissible (chain : List (LocalForm SliceId Claim Question)) : Prop :=
  ComposableChain chain ∧
  FragmentContained chain ∧
  FragmentSound chain ∧
  FragmentComplete chain

theorem localForm_exports_contained (f : LocalForm SliceId Claim Question) :
    f.availableExports ⊆ f.claims :=
  fun _ hc => f.wellFormed.2.2.1 (f.availableExports_subset_exports hc)

theorem fragmentContained_of_localForms
    (chain : List (LocalForm SliceId Claim Question)) :
    FragmentContained chain :=
  fun f _ => localForm_exports_contained f

theorem fragmentAdmissible_nil :
    FragmentAdmissible ([] : List (LocalForm SliceId Claim Question)) :=
  ⟨composableChain_nil, fragmentContained_of_localForms _,
   fun _ hc => absurd hc (by simp [chainExports]),
   fun _ hf => absurd hf (by simp)⟩

theorem fragmentComplete_singleton (f : LocalForm SliceId Claim Question)
    (hblk : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.blockedExports)
    (hpnd : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.pendingConclusions) :
    FragmentComplete [f] := by
  intro g hg b hb
  simp [List.mem_singleton] at hg; subst hg
  simp only [chainExports, List.foldr]
  apply Finset.mem_union_left
  simp only [LocalForm.availableExports, Finset.mem_filter]
  exact ⟨(g.wellFormed.2.2.2.2.2.1 b hb).2, hblk b hb, hpnd b hb⟩

theorem fragmentSound_append_singleton
    (chain : List (LocalForm SliceId Claim Question))
    (f : LocalForm SliceId Claim Question)
    (hs : FragmentSound chain)
    (hcert : ∀ c ∈ f.availableExports, ∃ b ∈ f.certifiedBridges, b.conclusion = c) :
    FragmentSound (chain ++ [f]) := by
  intro c hc
  rw [chainExports_append_singleton] at hc
  rcases Finset.mem_union.mp hc with hc | hc
  · obtain ⟨g, hg, b, hb, heq⟩ := hs c hc
    exact ⟨g, List.mem_append_left _ hg, b, hb, heq⟩
  · obtain ⟨b, hb, heq⟩ := hcert c hc
    exact ⟨f, List.mem_append_right _ (List.mem_singleton.mpr rfl), b, hb, heq⟩

theorem fragmentComplete_append_singleton
    (chain : List (LocalForm SliceId Claim Question))
    (f : LocalForm SliceId Claim Question)
    (hcomp : FragmentComplete chain)
    (hblk : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.blockedExports)
    (hpnd : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.pendingConclusions) :
    FragmentComplete (chain ++ [f]) := by
  intro g hg b hb
  rw [chainExports_append_singleton]
  rcases List.mem_append.mp hg with hg | hg
  · exact Finset.mem_union_left _ (hcomp g hg b hb)
  · rw [List.mem_singleton] at hg
    apply Finset.mem_union_right
    have hb' : b ∈ f.certifiedBridges := hg ▸ hb
    simp only [LocalForm.availableExports, Finset.mem_filter]
    exact ⟨(f.wellFormed.2.2.2.2.2.1 b hb').2, hblk b hb', hpnd b hb'⟩

theorem fragmentAdmissible_append_singleton
    (chain : List (LocalForm SliceId Claim Question))
    (f : LocalForm SliceId Claim Question)
    (hadm : FragmentAdmissible chain)
    (hbound : ∀ last ∈ chain.getLast?, BoundaryOK last f)
    (hcert : ∀ c ∈ f.availableExports, ∃ b ∈ f.certifiedBridges, b.conclusion = c)
    (hblk : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.blockedExports)
    (hpnd : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.pendingConclusions) :
    FragmentAdmissible (chain ++ [f]) :=
  ⟨composableChain_append_singleton hadm.1 hbound,
   fragmentContained_of_localForms _,
   fragmentSound_append_singleton chain f hadm.2.2.1 hcert,
   fragmentComplete_append_singleton chain f hadm.2.2.2 hblk hpnd⟩

end FragmentBridge

section GlobalFormObject

variable {SliceId Claim Question : Type _} [DecidableEq Claim] [DecidableEq Question]

def chainClaims (chain : List (LocalForm SliceId Claim Question)) : Finset Claim :=
  chain.foldr (fun f acc => f.claims ∪ acc) ∅

def chainCertifiedBridges (chain : List (LocalForm SliceId Claim Question)) :
    Finset (Bridge Claim) :=
  chain.foldr (fun f acc => f.certifiedBridges ∪ acc) ∅

def chainPendingBridges (chain : List (LocalForm SliceId Claim Question)) :
    Finset (Bridge Claim) :=
  chain.foldr (fun f acc => f.pendingBridges ∪ acc) ∅

def chainBlockedExports (chain : List (LocalForm SliceId Claim Question)) :
    Finset Claim :=
  chain.foldr (fun f acc => f.blockedExports ∪ acc) ∅

def chainHoles [DecidableEq Question]
    (chain : List (LocalForm SliceId Claim Question)) : Finset Question :=
  chain.foldr (fun f acc => f.clarificationHoles ∪ acc) ∅

def chainSliceIds (chain : List (LocalForm SliceId Claim Question)) : List SliceId :=
  chain.map LocalForm.sliceId

structure GlobalForm (SliceId Claim Question : Type _)
    [DecidableEq Claim] [DecidableEq Question] where

  chain : List (LocalForm SliceId Claim Question)

  globalExports : Finset Claim

  externalImports : Finset Claim

  globalClaims : Finset Claim

  globalCertifiedBridges : Finset (Bridge Claim)

  globalPendingBridges : Finset (Bridge Claim)

  globalBlockedExports : Finset Claim

  globalHoles : Finset Question

  sliceIds : List SliceId

  admissible : FragmentAdmissible chain

  exports_consistent : globalExports = chainExports chain

  imports_consistent : externalImports = chainExternalImports chain

  claims_consistent : globalClaims = chainClaims chain

  bridges_consistent :
    globalCertifiedBridges = chainCertifiedBridges chain

  pending_consistent :
    globalPendingBridges = chainPendingBridges chain

  blocked_consistent :
    globalBlockedExports = chainBlockedExports chain

  holes_consistent : globalHoles = chainHoles chain

  sliceIds_consistent : sliceIds = chainSliceIds chain

def composeForms
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain) :
    GlobalForm SliceId Claim Question :=
  { chain := chain
    globalExports := chainExports chain
    externalImports := chainExternalImports chain
    globalClaims := chainClaims chain
    globalCertifiedBridges := chainCertifiedBridges chain
    globalPendingBridges := chainPendingBridges chain
    globalBlockedExports := chainBlockedExports chain
    globalHoles := chainHoles chain
    sliceIds := chainSliceIds chain
    admissible := hadm
    exports_consistent := rfl
    imports_consistent := rfl
    claims_consistent := rfl
    bridges_consistent := rfl
    pending_consistent := rfl
    blocked_consistent := rfl
    holes_consistent := rfl
    sliceIds_consistent := rfl }

theorem chainExports_subset_chainClaims
    (chain : List (LocalForm SliceId Claim Question)) :
    chainExports chain ⊆ chainClaims chain := by
  induction chain with
  | nil => simp [chainExports, chainClaims]
  | cons a rest ih =>
    intro c hc
    simp only [chainExports, List.foldr] at hc
    simp only [chainClaims, List.foldr]
    rcases Finset.mem_union.mp hc with hc | hc
    · exact Finset.mem_union_left _ (localForm_exports_contained a hc)
    · exact Finset.mem_union_right _ (ih hc)

theorem GlobalForm.exports_subset_claims (g : GlobalForm SliceId Claim Question) :
    g.globalExports ⊆ g.globalClaims := by
  rw [g.exports_consistent, g.claims_consistent]
  exact chainExports_subset_chainClaims g.chain

def GlobalForm.extend
    (g : GlobalForm SliceId Claim Question)
    (f : LocalForm SliceId Claim Question)
    (hbound : ∀ last ∈ g.chain.getLast?, BoundaryOK last f)
    (hcert : ∀ c ∈ f.availableExports, ∃ b ∈ f.certifiedBridges, b.conclusion = c)
    (hblk : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.blockedExports)
    (hpnd : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.pendingConclusions) :
    GlobalForm SliceId Claim Question :=
  composeForms (g.chain ++ [f])
    (fragmentAdmissible_append_singleton g.chain f g.admissible hbound hcert hblk hpnd)

def GlobalForm.isFullyResolved
    (g : GlobalForm SliceId Claim Question) : Prop :=
  g.globalPendingBridges = ∅ ∧
  g.globalBlockedExports = ∅ ∧
  g.globalHoles = ∅

def GlobalForm.unresolvedSummary
    (g : GlobalForm SliceId Claim Question) :
    Finset (Bridge Claim) × Finset Claim × Finset Question :=
  (g.globalPendingBridges, g.globalBlockedExports, g.globalHoles)

theorem composeForms_nil :
    (composeForms ([] : List (LocalForm SliceId Claim Question)) fragmentAdmissible_nil).globalExports = ∅ := by
  simp [composeForms, chainExports]

theorem composeForms_chain
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain) :
    (composeForms chain hadm).chain = chain := rfl

theorem restricted_global_formalizability
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain) :
    ∃ (g : GlobalForm SliceId Claim Question),
      g.chain = chain ∧
      g.globalExports = chainExports chain ∧
      g.globalExports ⊆ g.globalClaims ∧
      FragmentAdmissible g.chain ∧
      FragmentSound g.chain ∧
      FragmentComplete g.chain :=
  ⟨composeForms chain hadm, rfl, rfl,
   (composeForms chain hadm).exports_subset_claims,
   hadm, hadm.2.2.1, hadm.2.2.2⟩

section CrossSystemBridge

variable {SliceId Claim Question : Type _} [DecidableEq Claim] [DecidableEq Question]

def GlobalForm.IsabelleCompatible
    (g : GlobalForm SliceId Claim Question) : Prop :=
  FragmentAdmissible g.chain ∧
  g.globalExports ⊆ g.globalClaims ∧
  FragmentSound g.chain ∧
  FragmentComplete g.chain

theorem cross_system_global_bridge
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain) :
    ∃ (g : GlobalForm SliceId Claim Question),
      g.chain = chain ∧
      g.IsabelleCompatible :=
  ⟨composeForms chain hadm, rfl, hadm,
   (composeForms chain hadm).exports_subset_claims,
   hadm.2.2.1, hadm.2.2.2⟩

theorem cross_system_global_bridge_chain_identity
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain) :
    (composeForms chain hadm).chain = chain ∧
    (composeForms chain hadm).IsabelleCompatible :=
  ⟨rfl, hadm, (composeForms chain hadm).exports_subset_claims,
   hadm.2.2.1, hadm.2.2.2⟩

end CrossSystemBridge

section SemanticClosure

variable {SliceId Claim Question : Type _} [DecidableEq Claim] [DecidableEq Question]

theorem mem_chainCertifiedBridges
    {chain : List (LocalForm SliceId Claim Question)}
    {f : LocalForm SliceId Claim Question} {b : Bridge Claim}
    (hf : f ∈ chain) (hb : b ∈ f.certifiedBridges) :
    b ∈ chainCertifiedBridges chain := by
  induction chain with
  | nil => simp at hf
  | cons a rest ih =>
    simp only [chainCertifiedBridges, List.foldr]
    rcases List.mem_cons.mp hf with rfl | hf
    · exact Finset.mem_union_left _ hb
    · exact Finset.mem_union_right _ (ih hf)

theorem of_mem_chainCertifiedBridges
    {chain : List (LocalForm SliceId Claim Question)}
    {b : Bridge Claim}
    (hb : b ∈ chainCertifiedBridges chain) :
    ∃ f ∈ chain, b ∈ f.certifiedBridges := by
  induction chain with
  | nil => simp [chainCertifiedBridges] at hb
  | cons a rest ih =>
    simp only [chainCertifiedBridges, List.foldr] at hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact ⟨a, List.mem_cons_self .., hb⟩
    · obtain ⟨f, hf, hbf⟩ := ih hb
      exact ⟨f, List.mem_cons_of_mem _ hf, hbf⟩

theorem claims_subset_chainClaims
    {chain : List (LocalForm SliceId Claim Question)}
    {f : LocalForm SliceId Claim Question}
    (hf : f ∈ chain) :
    f.claims ⊆ chainClaims chain := by
  induction chain with
  | nil => simp at hf
  | cons a rest ih =>
    simp only [chainClaims, List.foldr]
    rcases List.mem_cons.mp hf with rfl | hf
    · exact Finset.subset_union_left
    · exact Finset.Subset.trans (ih hf) Finset.subset_union_right

theorem chainExternalImports_subset_chainClaims
    (chain : List (LocalForm SliceId Claim Question)) :
    chainExternalImports chain ⊆ chainClaims chain := by
  match chain with
  | [] => simp [chainExternalImports, chainClaims]
  | f :: rest =>
    simp only [chainExternalImports, chainClaims, List.foldr]
    exact Finset.Subset.trans f.wellFormed.1 Finset.subset_union_left

def GlobalForm.SemanticallyClosed
    (g : GlobalForm SliceId Claim Question) : Prop :=
  (∀ c ∈ g.globalExports,
      ∃ b ∈ g.globalCertifiedBridges, b.conclusion = c) ∧
  (∀ b ∈ g.globalCertifiedBridges,
      b.premises ⊆ g.globalClaims) ∧
  (∀ b ∈ g.globalCertifiedBridges,
      b.conclusion ∈ g.globalExports) ∧
  g.globalExports ⊆ g.globalClaims ∧
  g.externalImports ⊆ g.globalClaims

theorem globalSound_of_fragmentSound
    (chain : List (LocalForm SliceId Claim Question))
    (hs : FragmentSound chain) :
    ∀ c ∈ chainExports chain,
      ∃ b ∈ chainCertifiedBridges chain, b.conclusion = c := by
  intro c hc
  obtain ⟨f, hf, b, hb, heq⟩ := hs c hc
  exact ⟨b, mem_chainCertifiedBridges hf hb, heq⟩

theorem chainBridges_premises_subset_chainClaims
    (chain : List (LocalForm SliceId Claim Question)) :
    ∀ b ∈ chainCertifiedBridges chain,
      b.premises ⊆ chainClaims chain := by
  intro b hb
  obtain ⟨f, hf, hbf⟩ := of_mem_chainCertifiedBridges hb
  exact Finset.Subset.trans
    (f.wellFormed.2.2.2.2.2.1 b hbf).1
    (claims_subset_chainClaims hf)

theorem globalComplete_of_fragmentComplete
    (chain : List (LocalForm SliceId Claim Question))
    (hc : FragmentComplete chain) :
    ∀ b ∈ chainCertifiedBridges chain,
      b.conclusion ∈ chainExports chain := by
  intro b hb
  obtain ⟨f, hf, hbf⟩ := of_mem_chainCertifiedBridges hb
  exact hc f hf b hbf

theorem composeForms_semanticallyClosed
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain) :
    (composeForms chain hadm).SemanticallyClosed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · 
    intro c hc
    simp only [composeForms] at hc ⊢
    exact globalSound_of_fragmentSound chain hadm.2.2.1 c hc
  · 
    intro b hb
    simp only [composeForms] at hb ⊢
    exact chainBridges_premises_subset_chainClaims chain b hb
  · 
    intro b hb
    simp only [composeForms] at hb ⊢
    exact globalComplete_of_fragmentComplete chain hadm.2.2.2 b hb
  · 
    exact (composeForms chain hadm).exports_subset_claims
  · 
    simp only [composeForms]
    exact chainExternalImports_subset_chainClaims chain

theorem restricted_global_formalizability_semantic
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain) :
    ∃ (g : GlobalForm SliceId Claim Question),
      g.chain = chain ∧
      g.SemanticallyClosed ∧
      g.IsabelleCompatible :=
  ⟨composeForms chain hadm,
   rfl,
   composeForms_semanticallyClosed chain hadm,
   hadm,
   (composeForms chain hadm).exports_subset_claims,
   hadm.2.2.1, hadm.2.2.2⟩

end SemanticClosure

end GlobalFormObject

section ExplicitFragment

variable {SliceId Claim Question : Type _} [DecidableEq Claim] [DecidableEq Question]

def agentDerivableSupport
    {Context World : Type _}
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (w : World) : Set (Context × Finset Claim × Claim) :=
  {t | a_derives w t.1 t.2.1 t.2.2}

def tr1_on
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim)
    (w : World)
    (Tasks : Set (Context × Finset Claim × Claim)) : Prop :=
  ∀ t ∈ Tasks,
    (a_derives w t.1 t.2.1 t.2.2 ↔ f_derives w t.1 (t.2.1.image τ) (τ t.2.2))

def Frag
    {Context : Type _}
    (g : GlobalForm SliceId Claim Question) :
    Set (Context × Finset Claim × Claim) :=
  {t | t.2.2 ∈ g.globalExports}

structure FragTranslationAssumptions
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim)
    (w : World) where

  sound : ∀ c Γ φ, φ ∈ g.globalExports →
    a_derives w c Γ φ → f_derives w c (Γ.image τ) (τ φ)

  complete : ∀ c Γ φ, φ ∈ g.globalExports →
    f_derives w c (Γ.image τ) (τ φ) → a_derives w c Γ φ

  support_inhabited : ∀ φ ∈ g.globalExports,
    ∃ c Γ, a_derives w c Γ φ

theorem frag_inter_support_subset
    {Context World : Type _}
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (w : World) :
    (Frag g : Set (Context × Finset Claim × Claim)) ∩
      agentDerivableSupport a_derives w ⊆
        agentDerivableSupport a_derives w := by
  exact Set.inter_subset_right

theorem frag_exports_within_support
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim) (w : World)
    (h : FragTranslationAssumptions g a_derives f_derives τ w) :
    ∀ φ ∈ g.globalExports,
      ∃ c Γ, (⟨c, Γ, φ⟩ : Context × Finset Claim × Claim) ∈
        agentDerivableSupport a_derives w :=
  fun φ hφ => h.support_inhabited φ hφ

theorem constructive_tr1_on_frag
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim) (w : World)
    (h : FragTranslationAssumptions g a_derives f_derives τ w) :
    tr1_on a_derives f_derives τ w (Frag g) := by
  intro ⟨c, Γ, φ⟩ hmem
  simp only [Frag, Set.mem_setOf_eq] at hmem
  exact ⟨h.sound c Γ φ hmem, h.complete c Γ φ hmem⟩

def SupportedFrag
    {Context World : Type _}
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (w : World) : Set (Context × Finset Claim × Claim) :=
  {t | t.2.2 ∈ g.globalExports ∧ a_derives w t.1 t.2.1 t.2.2}

theorem supportedFrag_subset_agentDerivableSupport
    {Context World : Type _}
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (w : World) :
    SupportedFrag g a_derives w ⊆ agentDerivableSupport a_derives w :=
  fun _ ht => ht.2

theorem supportedFrag_subset_frag
    {Context World : Type _}
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (w : World) :
    SupportedFrag g a_derives w ⊆ Frag g :=
  fun _ ht => ht.1

theorem supportedFrag_eq_frag_inter_support
    {Context World : Type _}
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (w : World) :
    SupportedFrag g a_derives w = Frag g ∩ agentDerivableSupport a_derives w := by
  ext ⟨c, Γ, φ⟩
  simp only [SupportedFrag, Frag, agentDerivableSupport, Set.mem_setOf_eq,
             Set.mem_inter_iff]

theorem frag_conclusion_coverage
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim) (w : World)
    (h : FragTranslationAssumptions g a_derives f_derives τ w) :
    ∀ φ, (∃ c Γ, (⟨c, Γ, φ⟩ : Context × Finset Claim × Claim) ∈ Frag g) →
      ∃ c Γ, (⟨c, Γ, φ⟩ : Context × Finset Claim × Claim) ∈
        SupportedFrag g a_derives w := by
  intro φ ⟨_, _, hfrag⟩
  simp only [Frag, Set.mem_setOf_eq] at hfrag
  obtain ⟨c', Γ', hd⟩ := h.support_inhabited φ hfrag
  exact ⟨c', Γ', hfrag, hd⟩

theorem tr1_on_supportedFrag
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim) (w : World)
    (h : FragTranslationAssumptions g a_derives f_derives τ w) :
    tr1_on a_derives f_derives τ w (SupportedFrag g a_derives w) :=
  fun t ht => constructive_tr1_on_frag g a_derives f_derives τ w h t
    (supportedFrag_subset_frag g a_derives w ht)

theorem supportedFrag_nonempty_of_constructive
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim) (w : World)
    (h : FragTranslationAssumptions g a_derives f_derives τ w) :
    ∀ φ ∈ g.globalExports,
      ∃ c Γ, (⟨c, Γ, φ⟩ : Context × Finset Claim × Claim) ∈
        SupportedFrag g a_derives w := by
  intro φ hφ
  obtain ⟨c, Γ, hd⟩ := h.support_inhabited φ hφ
  exact ⟨c, Γ, hφ, hd⟩

theorem supportedFrag_admissible_package
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim) (w : World)
    (h : FragTranslationAssumptions g a_derives f_derives τ w) :
    SupportedFrag g a_derives w ⊆ agentDerivableSupport a_derives w ∧
    tr1_on a_derives f_derives τ w (SupportedFrag g a_derives w) ∧
    (∀ φ ∈ g.globalExports, ∃ c Γ,
      (⟨c, Γ, φ⟩ : Context × Finset Claim × Claim) ∈
        SupportedFrag g a_derives w) :=
  ⟨supportedFrag_subset_agentDerivableSupport g a_derives w,
   tr1_on_supportedFrag g a_derives f_derives τ w h,
   supportedFrag_nonempty_of_constructive g a_derives f_derives τ w h⟩

def fragment_admissible_for_7A_lite
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim)
    (w : World) : Prop :=
  FragmentAdmissible g.chain ∧
  g.SemanticallyClosed ∧
  (∀ φ ∈ g.globalExports, ∃ c Γ,
    (⟨c, Γ, φ⟩ : Context × Finset Claim × Claim) ∈
      agentDerivableSupport a_derives w) ∧
  tr1_on a_derives f_derives τ w (Frag g)

theorem support_admissible_from_constructive_assumptions
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim) (w : World)
    (h : FragTranslationAssumptions (composeForms chain hadm) a_derives f_derives τ w) :
    fragment_admissible_for_7A_lite (composeForms chain hadm) a_derives f_derives τ w :=
  ⟨hadm,
   composeForms_semanticallyClosed chain hadm,
   frag_exports_within_support (composeForms chain hadm) a_derives f_derives τ w h,
   constructive_tr1_on_frag (composeForms chain hadm) a_derives f_derives τ w h⟩

theorem cross_system_extract_admissible_set
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim) (w : World)
    (h : FragTranslationAssumptions (composeForms chain hadm) a_derives f_derives τ w) :
    let g := composeForms chain hadm
    let S := SupportedFrag g a_derives w
    S ⊆ agentDerivableSupport a_derives w ∧
    tr1_on a_derives f_derives τ w S ∧
    (∀ φ ∈ g.globalExports, ∃ c Γ,
      (⟨c, Γ, φ⟩ : Context × Finset Claim × Claim) ∈ S) :=
  supportedFrag_admissible_package (composeForms chain hadm) a_derives f_derives τ w h

end ExplicitFragment

section DeploymentFrontier

variable {SliceId Claim Question : Type _} [DecidableEq Claim]

structure TaskScope (Claim : Type _) where

  constructive : Finset Claim

  statistical : Finset Claim

structure DeploymentFrontier (SliceId Claim Question : Type _) [DecidableEq Claim] where

  chain : List (LocalForm SliceId Claim Question)

  scope : TaskScope Claim

def CertifiedFrontier (df : DeploymentFrontier SliceId Claim Question) : Prop :=
  FragmentAdmissible df.chain ∧
  df.scope.constructive ⊆ chainExports df.chain ∧
  Disjoint df.scope.constructive df.scope.statistical

def DeploymentFrontier.totalCoverage (df : DeploymentFrontier SliceId Claim Question) :
    Finset Claim :=
  df.scope.constructive ∪ df.scope.statistical

theorem certifiedFrontier_admissible
    (df : DeploymentFrontier SliceId Claim Question)
    (hcert : CertifiedFrontier df) :
    FragmentAdmissible df.chain :=
  hcert.1

theorem certifiedFrontier_constructive_covered
    (df : DeploymentFrontier SliceId Claim Question)
    (hcert : CertifiedFrontier df) :
    df.scope.constructive ⊆ chainExports df.chain :=
  hcert.2.1

theorem certifiedFrontier_of_admissible
    (chain : List (LocalForm SliceId Claim Question))
    (scope : TaskScope Claim)
    (hadm : FragmentAdmissible chain)
    (hcov : scope.constructive ⊆ chainExports chain)
    (hdisj : Disjoint scope.constructive scope.statistical) :
    CertifiedFrontier ⟨chain, scope⟩ :=
  ⟨hadm, hcov, hdisj⟩

theorem certifiedFrontier_extend
    (df : DeploymentFrontier SliceId Claim Question)
    (f : LocalForm SliceId Claim Question)
    (hcert : CertifiedFrontier df)
    (hbound : ∀ last ∈ df.chain.getLast?, BoundaryOK last f)
    (hscope : df.scope.constructive ⊆ chainExports df.chain ∪ f.availableExports)
    (hcertBr : ∀ c ∈ f.availableExports, ∃ b ∈ f.certifiedBridges, b.conclusion = c)
    (hblk : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.blockedExports)
    (hpnd : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.pendingConclusions) :
    CertifiedFrontier ⟨df.chain ++ [f], df.scope⟩ := by
  refine ⟨?_, ?_, hcert.2.2⟩
  · exact fragmentAdmissible_append_singleton df.chain f hcert.1 hbound hcertBr hblk hpnd
  · intro c hc
    rw [chainExports_append_singleton]
    exact hscope hc

end DeploymentFrontier

end SafeSlice
