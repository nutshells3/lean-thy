import Step8_AuditedSurrogateTheoremSchema

noncomputable section

namespace SafeSlice

/-!
# Step 9: Anytime-Valid Stopping Theorem
-/

structure ConfidenceSequence where
  lower : Nat → ℝ
  upper : Nat → ℝ

def csWellFormed (cs : ConfidenceSequence) : Prop :=
  ∀ n, cs.lower n ≤ cs.upper n

def csCoversAt (cs : ConfidenceSequence) (θ : ℝ) (n : Nat) : Prop :=
  cs.lower n ≤ θ ∧ θ ≤ cs.upper n

def fixedTimeValid (cs : ConfidenceSequence) (θ _alpha : ℝ) (n : Nat) : Prop :=
  csCoversAt cs θ n

def anytimeValid (cs : ConfidenceSequence) (θ _alpha : ℝ) : Prop :=
  ∀ n, csCoversAt cs θ n

theorem anytimeValidImpFixed {cs : ConfidenceSequence} {θ α : ℝ} {n : Nat}
    (hValid : anytimeValid cs θ α) :
    fixedTimeValid cs θ α n :=
  hValid n

theorem anytimeValidLowerBound {cs : ConfidenceSequence} {θ α : ℝ} {n : Nat}
    (hValid : anytimeValid cs θ α) :
    cs.lower n ≤ θ :=
  (hValid n).1

theorem anytimeValidUpperBound {cs : ConfidenceSequence} {θ α : ℝ} {n : Nat}
    (hValid : anytimeValid cs θ α) :
    θ ≤ cs.upper n :=
  (hValid n).2

def csExcludesAbove (cs : ConfidenceSequence) (threshold : ℝ) (n : Nat) : Prop :=
  cs.upper n < threshold

def csExcludesBelow (cs : ConfidenceSequence) (threshold : ℝ) (n : Nat) : Prop :=
  threshold < cs.lower n

theorem csStopUpperBoundSafe {cs : ConfidenceSequence} {θ α ηMax : ℝ} {t : Nat}
    (hValid : anytimeValid cs θ α) (hStop : cs.upper t < ηMax) :
    θ < ηMax := by
  have hUpper : θ ≤ cs.upper t := anytimeValidUpperBound hValid
  linarith

theorem csStopLowerBoundSafe {cs : ConfidenceSequence} {θ α ηMin : ℝ} {t : Nat}
    (hValid : anytimeValid cs θ α) (hStop : ηMin < cs.lower t) :
    ηMin < θ := by
  have hLower : cs.lower t ≤ θ := anytimeValidLowerBound hValid
  linarith

def csWidth (cs : ConfidenceSequence) (n : Nat) : ℝ :=
  cs.upper n - cs.lower n

def csWidthVanishing (cs : ConfidenceSequence) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, csWidth cs n < ε

theorem vanishingCsEventuallyStops {cs : ConfidenceSequence} {θ α ηMax : ℝ}
    (hValid : anytimeValid cs θ α) (hVanish : csWidthVanishing cs)
    (hBelow : θ < ηMax) :
    ∃ t, cs.upper t < ηMax := by
  let ε := ηMax - θ
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  rcases hVanish ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  have hWidth : csWidth cs N < ε := hN N le_rfl
  have hLower : cs.lower N ≤ θ := anytimeValidLowerBound hValid
  dsimp [csWidth, ε] at hWidth
  linarith

end SafeSlice
