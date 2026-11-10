import JesseMath.Physics.YangMillsWeakCoupling

/-! Controls for the actual Haar Wilson density bounds. The positive statements preserve
threshold-before-volume quantifiers; the negative statement excludes zero sublevel scale. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace JesseMath.Physics.YangMillsUniformWeakCouplingTest

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (L : ℕ) [NeZero L],
      c ^ (4 * L ^ 4) ≤ haarVacuumSublevelMass L (δ * (6 * (L : ℝ) ^ 4)) :=
  exists_haar_sublevel_mass_volume_bound hδ

example : ∃ B : ℝ, ∀ (L : ℕ) [NeZero L] (β : ℝ), B ≤ β →
    (wilsonMeasure (gaugeHaarMeasure L) β).real
      {U | (1 / 100 : ℝ) * (L : ℝ) ^ 4 ≤ wilsonAction 1 U} < 1 / 1000 :=
  haarWilsonMeasure_density_tail_uniform (by norm_num) (by norm_num)

example : ∃ B : ℝ, ∀ (L : ℕ) [NeZero L] (β : ℝ), B ≤ β →
    (∫ U, wilsonAction 1 U ∂wilsonMeasure (gaugeHaarMeasure L) β) / (L : ℝ) ^ 4 <
      (1 / 100 : ℝ) := haarWilsonMeanActionDensity_uniform (by norm_num)

example (sizes : ℕ → ℕ) [∀ n, NeZero (sizes n)] (β : ℕ → ℝ)
    (hβ : Tendsto β atTop atTop) :
    Tendsto (fun n => (∫ U, wilsonAction 1 U
      ∂wilsonMeasure (gaugeHaarMeasure (sizes n)) (β n)) / (sizes n : ℝ) ^ 4)
      atTop (𝓝 0) := haarWilsonMeanActionDensity_tendsto_varying_volume sizes β hβ

theorem zero_scale_has_no_positive_product_bound :
    ¬ (∃ c : ℝ, 0 < c ∧ ∀ (L : ℕ) [NeZero L],
      c ^ (4 * L ^ 4) ≤ haarVacuumSublevelMass L 0) := by
  rintro ⟨c, hc, hb⟩
  have h := hb 1
  rw [haarVacuumSublevelMass_eq_zero_of_nonpos (by norm_num)] at h
  exact (not_le_of_gt (pow_pos hc _)) h

#assert_zfc_axioms

end JesseMath.Physics.YangMillsUniformWeakCouplingTest
