import Design3_OperationalStoppingPolicy

noncomputable section

namespace SafeSlice

/-!
# Design 4: Variance-Adaptive Stopping Policy
-/

def designFirstExclusion
    (upper : Nat → ℝ) (threshold : ℝ) (hExists : ∃ n, upper n < threshold) : Nat :=
  Nat.find hExists

theorem designFirstExclusionAttains
    {upper : Nat → ℝ} {threshold : ℝ} (hExists : ∃ n, upper n < threshold) :
    upper (designFirstExclusion upper threshold hExists) < threshold :=
  Nat.find_spec hExists

theorem designFirstExclusion_le
    {upper : Nat → ℝ} {threshold : ℝ} {t : Nat}
    (hStop : upper t < threshold) :
    designFirstExclusion upper threshold ⟨t, hStop⟩ ≤ t :=
  Nat.find_min' _ hStop

theorem designFirstExclusionNoLater
    {adaptiveUpper baselineUpper : Nat → ℝ} {threshold : ℝ}
    (hDom : ∀ t, adaptiveUpper t ≤ baselineUpper t)
    (hBaselineStops : ∃ t, baselineUpper t < threshold) :
    let hAdaptiveStops : ∃ t, adaptiveUpper t < threshold := by
      rcases hBaselineStops with ⟨t, hStop⟩
      exact ⟨t, lt_of_le_of_lt (hDom t) hStop⟩
    designFirstExclusion adaptiveUpper threshold hAdaptiveStops ≤
      designFirstExclusion baselineUpper threshold hBaselineStops := by
  let tBaseline :=
    designFirstExclusion baselineUpper threshold hBaselineStops
  let hAdaptiveStops : ∃ t, adaptiveUpper t < threshold := by
    rcases hBaselineStops with ⟨t, hStop⟩
    exact ⟨t, lt_of_le_of_lt (hDom t) hStop⟩
  have hBaselineAt : baselineUpper tBaseline < threshold :=
    designFirstExclusionAttains hBaselineStops
  have hAdaptiveAt : adaptiveUpper tBaseline < threshold := by
    have hLe := hDom tBaseline
    linarith
  simpa [tBaseline, hAdaptiveStops] using
    designFirstExclusion_le
      (upper := adaptiveUpper)
      (threshold := threshold)
      hAdaptiveAt

structure VarianceAdaptiveStoppingPolicy (Task Payload : Type*) where
  base : OperationalStoppingPolicy Task Payload
  adaptiveUpper : Nat → ℝ
  baselineUpper : Nat → ℝ
  dominates :
    ∀ t, adaptiveUpper t ≤ baselineUpper t
  adaptiveStops : ∃ t, adaptiveUpper t < base.etaMax
  baselineStops : ∃ t, baselineUpper t < base.etaMax

theorem adaptiveFirstExclusionNoLater {Task Payload : Type*}
    (policy : VarianceAdaptiveStoppingPolicy Task Payload) :
    designFirstExclusion
        policy.adaptiveUpper
        policy.base.etaMax
        policy.adaptiveStops ≤
      designFirstExclusion
        policy.baselineUpper
        policy.base.etaMax
        policy.baselineStops := by
  simpa using
    designFirstExclusionNoLater
      (hDom := policy.dominates)
      (hBaselineStops := policy.baselineStops)

end SafeSlice
