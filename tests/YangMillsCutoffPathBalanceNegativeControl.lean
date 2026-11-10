import JesseMath.Physics.YangMillsCutoffPathBalance

/-!
Negative controls for `YangMillsCutoffPathBalance`. Each theorem states a false strengthening
of the cutoff-path balance theorem and proves its negation on an explicit model built from
repository definitions: the canonical SU(2) Clause (0) cutoff path, the repository's fixed-volume
dyadic refinement, and the repository's own Haar bounds. The controls concern the composed
upper bound `exp(-β(ε-δ)) / c₁^(4 L⁴)`, not the actual Wilson tail itself.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace JesseMath.Physics.YangMillsCutoffPathBalanceNegativeControl

open JesseMath.Physics JesseMath.Physics.YangMillsCutoffPathBalance

/-- Explicit path: SU(2), blocking factor 13, one infrared block of unit size per direction, so
`a_K = 13^(-K)`, `L_K = 13^K` and `β_K = K c₀(13,2) + 1/24`. -/
abbrev P₀ : FixedVolumeCutoffPath :=
  clauseZeroCanonicalPath 13 1 (by norm_num) (by norm_num) one_pos 1 one_pos

theorem P₀_coupling_tendsto_atTop : Tendsto P₀.β atTop atTop :=
  clauseZeroCanonicalPath_coupling_tendsto_atTop 13 1 (by norm_num) (by norm_num) one_pos 1 one_pos

theorem fixedThreshold_exists :
    ∃ H : PathHaarMassBound P₀.toFixedVolumeGeometry, ∀ n, H.δ n = 1 / 2 :=
  exists_fixedThresholdPathHaarMassBound _ (by norm_num)

/-- The repository's fixed-threshold Haar ingredient on `P₀` at total threshold `δ = 1/2`. -/
def Hfix : PathHaarMassBound P₀.toFixedVolumeGeometry := Classical.choose fixedThreshold_exists

theorem Hfix_δ (n : ℕ) : Hfix.δ n = 1 / 2 := Classical.choose_spec fixedThreshold_exists n

/-- False strengthening 1: a diverging bare coupling, without the balance, makes the composed
total-action bound vanish for every Haar ingredient with `c₁ ≤ 1/2`. Rejected on `P₀`. -/
theorem coupling_divergence_without_balance_rejected :
    ¬ ∀ (P : FixedVolumeCutoffPath) (H : PathHaarMassBound P.toFixedVolumeGeometry),
        Tendsto P.β atTop atTop → (∀ n, H.c₁ n ≤ 1 / 2) →
          Tendsto (fun n => composedTailBound (P.sites n) (P.β n) 1 (H.δ n) (H.c₁ n))
            atTop (𝓝 0) := by
  intro hclaim
  let H₀ := Hfix.clip (1 / 2) (by norm_num)
  have hc : ∀ n, H₀.c₁ n ≤ 1 / 2 := fun n => PathHaarMassBound.clip_c₁_le _ _ _ n
  have hdiv := clauseZeroCanonicalPath_composedTailBound_tendsto_atTop 13 1 (by norm_num)
    (by norm_num) one_pos 1 one_pos H₀ (ε := 1) (cbar := 1 / 2) (by norm_num)
    (Eventually.of_forall hc)
  exact not_tendsto_nhds_of_tendsto_atTop hdiv 0 (hclaim P₀ H₀ P₀_coupling_tendsto_atTop hc)

/-- False strengthening 2: the repository's volume-uniform Haar constant, used at its extensive
thresholds `δ_n = η · 6 L_n⁴`, makes the fixed-target composed bound vanish along every path
with diverging coupling. Rejected on `P₀` with `η = 1/12`. -/
theorem extensive_haar_constant_rejected :
    ¬ ∀ (P : FixedVolumeCutoffPath), Tendsto P.β atTop atTop →
        ∀ H : PathHaarMassBound P.toFixedVolumeGeometry,
          (∀ n, H.δ n = (1 / 12 : ℝ) * (6 * (P.sites n : ℝ) ^ 4)) →
            Tendsto (fun n => composedTailBound (P.sites n) (P.β n) 1 (H.δ n) (H.c₁ n))
              atTop (𝓝 0) := by
  intro hclaim
  obtain ⟨H, c, -, -, -, hδ⟩ := exists_extensivePathHaarMassBound P₀.toFixedVolumeGeometry
    (η := 1 / 12) (by norm_num)
  exact extensiveHaarBound_not_tendsto_zero P₀ H (by norm_num) hδ 1
    (hclaim P₀ P₀_coupling_tendsto_atTop H hδ)

/-- The quartic-scale path on the geometry of `P₀`: `β_n = a_n^(-4)`, so `β_n a_n⁴ = 1`. -/
def P₁ : FixedVolumeCutoffPath where
  toFixedVolumeGeometry := P₀.toFixedVolumeGeometry
  β := fun n => 1 / P₀.a n ^ 4
  β_nonneg := fun n => (one_div_pos.mpr (pow_pos (P₀.a_pos n) 4)).le

/-- False strengthening 3: quartic coupling growth with the fixed constant `β_n a_n⁴ ≥ 1`
balances for every fixed-threshold Haar ingredient with `c₁ ≤ e^(-1)`. Rejected on `P₁`: the
critical value is `κ⋆ = 4 · 1⁴ · 1 / (1 - 1/2) = 8 > 1`. -/
theorem quartic_growth_below_threshold_rejected :
    ¬ ∀ (P : FixedVolumeCutoffPath) (H : PathHaarMassBound P.toFixedVolumeGeometry),
        (∀ n, 1 ≤ P.β n * P.a n ^ 4) → (∀ n, H.δ n = 1 / 2) →
          (∀ n, H.c₁ n ≤ Real.exp (-1)) →
            Tendsto (fun n => composedTailBound (P.sites n) (P.β n) 1 (H.δ n) (H.c₁ n))
              atTop (𝓝 0) := by
  intro hclaim
  let H₁ : PathHaarMassBound P₁.toFixedVolumeGeometry := Hfix.clip (Real.exp (-1)) (Real.exp_pos _)
  have hc : ∀ n, H₁.c₁ n ≤ Real.exp (-1) := fun n => PathHaarMassBound.clip_c₁_le _ _ _ n
  have hδ : ∀ n, H₁.δ n = 1 / 2 := Hfix_δ
  have hq : ∀ n, P₁.β n * P₁.a n ^ 4 = 1 := fun n => by
    show 1 / P₀.a n ^ 4 * P₀.a n ^ 4 = 1
    exact one_div_mul_cancel (pow_pos (P₀.a_pos n) 4).ne'
  have hside : P₁.side = 1 := by
    show ((1 : ℕ) : ℝ) * 1 = 1
    norm_num
  have hcrit : criticalQuarticCoefficient P₁.side 1 (1 / 2) (Real.exp (-1)) = 8 := by
    unfold criticalQuarticCoefficient
    rw [hside, one_div (Real.exp (-1)), ← Real.exp_neg, neg_neg, Real.log_exp]
    norm_num
  have hdiv := composedTailBound_tendsto_atTop_of_subcritical P₁ H₁ (ε := 1) (δ := 1 / 2)
    (cbar := Real.exp (-1)) (κ := 1) hδ (Eventually.of_forall hc) (by norm_num)
    (by rw [hcrit]; norm_num) (Eventually.of_forall fun n => (hq n).le)
  exact not_tendsto_nhds_of_tendsto_atTop hdiv 0
    (hclaim P₁ H₁ (fun n => (hq n).ge) hδ hc)

/-- One-loop-type path on the repository's fixed-volume dyadic refinement (`side = 1`):
`a_n = 2^(-n)`, `L_n = 2^n`, `β_n = n = log(1/a_n) / log 2`. -/
def Pdy : FixedVolumeCutoffPath where
  toFixedVolumeGeometry := dyadicGeometry 1 one_pos
  β := fun n => n
  β_nonneg := fun n => Nat.cast_nonneg n

theorem dyadicThreshold_exists :
    ∃ H : PathHaarMassBound Pdy.toFixedVolumeGeometry, ∀ n, H.δ n = 1 / 2 :=
  exists_fixedThresholdPathHaarMassBound _ (by norm_num)

/-- False strengthening 4: logarithmic (asymptotic-freedom-type) coupling growth balances the
fixed-threshold Haar entropy. Rejected on `Pdy` for every Haar ingredient with `c₁ ≤ 1/2`. -/
theorem logarithmic_growth_rejected :
    ¬ ∀ (P : FixedVolumeCutoffPath) (H : PathHaarMassBound P.toFixedVolumeGeometry),
        (∀ n, P.β n ≤ Real.log (1 / P.a n) / Real.log 2) → (∀ n, H.c₁ n ≤ 1 / 2) →
          Tendsto (fun n => composedTailBound (P.sites n) (P.β n) 1 (H.δ n) (H.c₁ n))
            atTop (𝓝 0) := by
  intro hclaim
  let H₂ := (Classical.choose dyadicThreshold_exists).clip (1 / 2) (by norm_num)
  have hc : ∀ n, H₂.c₁ n ≤ 1 / 2 := fun n => PathHaarMassBound.clip_c₁_le _ _ _ n
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hβ : ∀ n, Pdy.β n ≤ Real.log (1 / Pdy.a n) / Real.log 2 := fun n => by
    show (n : ℝ) ≤ Real.log (1 / (1 / 2 ^ n)) / Real.log 2
    rw [one_div_one_div, Real.log_pow, mul_div_assoc, div_self hlog2.ne', mul_one]
  have hdiv := composedTailBound_tendsto_atTop_of_logarithmic Pdy H₂ (ε := 1)
    (cbar := 1 / 2) 0 (1 / Real.log 2) (by norm_num) (Eventually.of_forall hc)
    (Eventually.of_forall fun n => by
      have h := hβ n
      rw [zero_add, one_div_mul_eq_div]
      exact h)
  exact not_tendsto_nhds_of_tendsto_atTop hdiv 0 (hclaim Pdy H₂ hβ hc)

/-- False strengthening 5: the product-box route supplies a constant per-link factor at the
fixed total threshold `δ = 1/2` along `P₀`, i.e. nonempty plaquette-controlling neighborhoods at
the scales `δ / (6 L_n⁴)` with Haar mass bounded below by a fixed `c > 0`. Rejected by
`boxFactor_tendsto_zero`. -/
theorem box_route_constant_factor_rejected :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n, ∃ K : Set SU2, K.Nonempty ∧
        (∀ a ∈ K, ∀ b ∈ K, ∀ c' ∈ K, ∀ d ∈ K,
          1 - (1 / 2 : ℝ) * (SU2.trace (a * b * c'⁻¹ * d⁻¹)).re <
            (1 / 2) / (6 * (P₀.sites n : ℝ) ^ 4)) ∧
        c ≤ SU2.haarProbability.real K := by
  rintro ⟨c, hc, hK⟩
  choose K hne hctrl hmass using hK
  have hη : ∀ n, (1 / 2 : ℝ) / (6 * (P₀.sites n : ℝ) ^ 4) * (6 * (P₀.sites n : ℝ) ^ 4) ≤ 1 / 2 :=
    fun n => (div_mul_cancel₀ _ (mul_pos (by norm_num)
      (pow_pos (P₀.sites_pos_real n) 4)).ne').le
  have hlim := boxFactor_tendsto_zero P₀.toFixedVolumeGeometry (δ := 1 / 2) (by norm_num)
    (fun n => (1 / 2 : ℝ) / (6 * (P₀.sites n : ℝ) ^ 4)) hη K hne hctrl
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hc)).exists
  exact absurd (hmass n) (not_le.mpr hn)

/-- False strengthening 6: a single-link Haar mass rate with exponent `p = 0`, i.e. masses
bounded below uniformly in the per-plaquette scale. Rejected by `SingleLinkHaarMassRate.p_pos`. -/
theorem zero_exponent_rate_rejected : ¬ ∃ R : SingleLinkHaarMassRate, R.p = 0 := by
  rintro ⟨R, hR⟩
  exact (R.p_pos).ne' hR

end JesseMath.Physics.YangMillsCutoffPathBalanceNegativeControl

#assert_zfc_axioms
