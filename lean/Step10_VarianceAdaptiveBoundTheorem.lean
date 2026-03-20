import Step9_AnytimeValidStoppingTheorem

noncomputable section

namespace SafeSlice

/-!
# Step 10: Variance-Adaptive Bound Theorem
-/

abbrev HalfWidthFn := Nat → ℝ

def hwNonneg (width : HalfWidthFn) : Prop :=
  ∀ n, 0 ≤ width n

def hwVanishing (width : HalfWidthFn) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, width n < ε

def hoeffdingHalfWidth (b c : ℝ) : HalfWidthFn :=
  fun n => b * c / Real.sqrt (n + 1)

def empiricalBernsteinHalfWidth
    (b c₁ c₂ : ℝ) (varianceProxy : Nat → ℝ) : HalfWidthFn :=
  fun n => varianceProxy n * c₁ / Real.sqrt (n + 1) + b * c₂ / (n + 1)

def hwConfidenceSequence (center : Nat → ℝ) (width : HalfWidthFn) : ConfidenceSequence where
  lower := fun n => center n - width n
  upper := fun n => center n + width n

theorem hwConfidenceSequence_wellFormed {center : Nat → ℝ} {width : HalfWidthFn}
    (hNonneg : hwNonneg width) :
    csWellFormed (hwConfidenceSequence center width) := by
  intro n
  have hWidth : 0 ≤ width n := hNonneg n
  simp [hwConfidenceSequence]
  linarith

theorem hwConfidenceSequence_width {center : Nat → ℝ} {width : HalfWidthFn} {n : Nat} :
    csWidth (hwConfidenceSequence center width) n = 2 * width n := by
  simp [csWidth, hwConfidenceSequence, sub_eq_add_neg, add_left_comm, add_assoc]
  ring

theorem hwVanishing_imp_csWidthVanishing {center : Nat → ℝ} {width : HalfWidthFn}
    (hVanish : hwVanishing width) :
    csWidthVanishing (hwConfidenceSequence center width) := by
  intro ε hε
  have hHalf : 0 < ε / 2 := by linarith
  rcases hVanish (ε / 2) hHalf with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hWidth : width n < ε / 2 := hN n hn
  have hScaled : 2 * width n < ε := by linarith
  simpa [hwConfidenceSequence_width] using hScaled

def firstExclusion (cs : ConfidenceSequence) (threshold : ℝ)
    (hExists : ∃ n, cs.upper n < threshold) : Nat :=
  Nat.find hExists

theorem firstExclusionAttains {cs : ConfidenceSequence} {threshold : ℝ}
    (hExists : ∃ n, cs.upper n < threshold) :
    cs.upper (firstExclusion cs threshold hExists) < threshold :=
  Nat.find_spec hExists

theorem firstExclusion_le {cs : ConfidenceSequence} {threshold : ℝ}
    {t : Nat} (hStop : cs.upper t < threshold) :
    firstExclusion cs threshold ⟨t, hStop⟩ ≤ t :=
  Nat.find_min' _ hStop

theorem narrowerCsEarlierExclusion {center : Nat → ℝ} {adaptive baseline : HalfWidthFn}
    (hNarrow : ∀ n, adaptive n ≤ baseline n) {threshold : ℝ} {t : Nat}
    (hBaseline : (hwConfidenceSequence center baseline).upper t < threshold) :
    (hwConfidenceSequence center adaptive).upper t < threshold := by
  have hUpper :
      (hwConfidenceSequence center adaptive).upper t ≤
        (hwConfidenceSequence center baseline).upper t := by
    simp [hwConfidenceSequence, hNarrow t]
  linarith

theorem adaptiveEventuallyStops {center : Nat → ℝ} {width : HalfWidthFn}
    {θ α ηMax : ℝ}
    (hValid : anytimeValid (hwConfidenceSequence center width) θ α)
    (hVanish : hwVanishing width)
    (hBelow : θ < ηMax) :
    ∃ t, (hwConfidenceSequence center width).upper t < ηMax := by
  exact vanishingCsEventuallyStops
    hValid
    (hwVanishing_imp_csWidthVanishing hVanish)
    hBelow

end SafeSlice
