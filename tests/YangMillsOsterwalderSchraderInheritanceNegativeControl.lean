import JesseMath.Physics.YangMillsOsterwalderSchraderInheritance

/-!
# Negative controls for Osterwalder–Schrader inheritance of Wilson-loop limits

Each false strengthening below is refuted on an explicit model: a family of laws on the common
space `WilsonLoopSpace`, or the actual Wilson measure.

1. Nontriviality at every index does not pass to weak limits.
2. A time-mixing limit does not force time mixing at large indices.
3. Along the explicit asymptotically free dyadic path, no cutoff law is time mixing, so the
   `time_mixing` field cannot be inherited from cutoffs.
4. Reflection positivity is not automatic: a law on the common space violates it.
5. Osterwalder–Seiler positivity of the actual Wilson measure fails without the hypothesis
   that the functional depends only on the closed positive half-lattice.
6. Reflection positivity on all loops with dyadic time data does not imply the full
   `reflection_positive` condition: some regularity hypothesis such as
   `DyadicTimeApproximable` is needed.
7. Reflection positivity, reflection invariance and invariance under every dyadic time
   translation do not imply `DyadicTimeApproximable`, nor invariance under a rational
   translation: the regularity fields of `WilsonLimitRegularity` are independent questions.
8. Reflection positivity, every symmetry and time mixing do not imply nontriviality: the
   constant Dirac law has them all and is trivial.

Positive controls (`example`s) show the proved statements apply to concrete inputs.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped BoundedContinuousFunction

namespace JesseMath.Physics.YangMillsOsterwalderSchraderInheritanceNegativeControl

open YangMillsContinuumCompactness YangMillsRenormalizedObservableLimits
  YangMillsOsterwalderSchraderInheritance

/-! ### 1. Nontriviality is not a closed condition -/

/-- False strengthening: nontrivial laws at every index have a nontrivial weak limit. -/
theorem nontriviality_not_closed :
    ¬ ∀ (μs : ℕ → ProbabilityMeasure WilsonLoopSpace) (ν : ProbabilityMeasure WilsonLoopSpace),
      Tendsto μs atTop (𝓝 ν) → (∀ n, IsNontrivial (μs n)) → IsNontrivial ν := by
  intro h
  obtain ⟨hlim, hnt, hν, -, -⟩ := signLaw_family_counterexample
  exact hν (h _ _ hlim hnt)

/-- Positive control: the reverse direction is a theorem (nontriviality is open). -/
example (μs : ℕ → ProbabilityMeasure WilsonLoopSpace) (ν : ProbabilityMeasure WilsonLoopSpace)
    (h : Tendsto μs atTop (𝓝 ν)) (hν : IsNontrivial ν) : ∀ᶠ n in atTop, IsNontrivial (μs n) :=
  eventually_isNontrivial_of_tendsto h hν

/-! ### 2. Time mixing is not an open condition -/

/-- False strengthening: a time-mixing weak limit forces time mixing at all large indices. -/
theorem timeMixing_not_open :
    ¬ ∀ (μs : ℕ → ProbabilityMeasure WilsonLoopSpace) (ν : ProbabilityMeasure WilsonLoopSpace),
      Tendsto μs atTop (𝓝 ν) → IsTimeMixing ν → ∀ᶠ n in atTop, IsTimeMixing (μs n) := by
  intro h
  obtain ⟨hlim, -, -, hnm, hmix⟩ := signLaw_family_counterexample
  obtain ⟨n, hn⟩ := (h _ _ hlim hmix).exists
  exact hnm n hn

/-! ### 3. The actual cutoff laws never mix -/

/-- False strengthening: along the explicit asymptotically free dyadic path the joint
Wilson-loop laws are eventually time mixing, so that mixing could be inherited by limits. -/
theorem dyadic_cutoffs_not_eventually_mixing :
    ¬ ∀ᶠ n in atTop, IsTimeMixing (dyadicOneLoopPath.wilsonLoopLaw n) := by
  intro h
  obtain ⟨n, hn1, hn2⟩ := (h.and (eventually_ge_atTop 1)).exists
  exact dyadicOneLoopPath_wilsonLoopLaw_not_isTimeMixing n hn2 hn1

/-! ### 4. Reflection positivity is a genuine constraint -/

/-- The configuration equal to `1` on positive-time loops and `-1` on the others. -/
def signedConfig : WilsonLoopSpace := fun ℓ => if 0 < ℓ.base 0 then 1 else -1

theorem laterLoop_timeReflect_not_positive : ¬ (0 : ℚ) < laterLoop.timeReflect.base 0 := by
  simp [PhysicalRectangle.timeReflect, laterLoop]

/-- False strengthening: every law on the common space is reflection positive. -/
theorem reflectionPositivity_not_automatic :
    ¬ ∀ ν : ProbabilityMeasure WilsonLoopSpace, IsReflectionPositive ν := by
  intro h
  have hdep : DependsOnPositiveTime (loopTest unitClamp laterLoop) := by
    intro w w' hw
    simp only [loopTest_apply]
    rw [hw laterLoop (by simp [PhysicalRectangle.IsPositiveTime, laterLoop])]
  have hpos := h (diracProba signedConfig) (loopTest unitClamp laterLoop) hdep
  rw [integral_diracProba] at hpos
  have h1 : signedConfig laterLoop = 1 := by simp [signedConfig, laterLoop]
  have h2 : reflectObservables signedConfig laterLoop = -1 := by
    simp only [reflectObservables, signedConfig, laterLoop_timeReflect_not_positive, ite_false]
  simp only [loopTest_apply, h1, h2, unitClamp_of_mem (by norm_num : (-1 : ℝ) ≤ 1)
    (by norm_num : (1 : ℝ) ≤ 1), unitClamp_of_mem (by norm_num : (-1 : ℝ) ≤ -1)
    (by norm_num : (-1 : ℝ) ≤ 1)] at hpos
  norm_num at hpos

/-! ### 5. The positive-half hypothesis of Osterwalder–Seiler positivity is needed -/

/-- The plaquette at the origin of the side-two torus in the `(0, 1)` plane. -/
def p₀ : Plaquette 2 := originPlaquette 2

/-- A functional that is odd under the reflection. -/
def oddFunctional (U : GaugeConfig 2) : ℝ :=
  plaquetteAction U p₀ - plaquetteAction (reflectConfig U) p₀

theorem continuous_oddFunctional : Continuous oddFunctional :=
  (continuous_plaquetteAction p₀).sub
    ((continuous_plaquetteAction p₀).comp continuous_reflectConfig)

theorem oddFunctional_reflect (U : GaugeConfig 2) :
    oddFunctional (reflectConfig U) = -oddFunctional U := by
  simp only [oddFunctional, reflectConfig_reflectConfig]
  ring

theorem reflectPlaquette_p₀ : reflectPlaquette p₀ = ⟨-unitVec 2 0, 0, 1, by decide⟩ := by
  have hs : reflectSite (0 : Lattice4D 2) = 0 := by
    funext i
    simp [reflectSite]
  simp [reflectPlaquette, p₀, originPlaquette, hs]

/-- The reflected origin plaquette avoids the flipped link. -/
theorem plaquetteAction_flipLink_reflect :
    plaquetteAction (flipLink (⟨p₀.x, p₀.μ⟩ : Link 2)) (reflectPlaquette p₀) = 0 := by
  have hl : (⟨p₀.x, p₀.μ⟩ : Link 2) = ⟨0, 0⟩ := rfl
  have e1 : (⟨-unitVec 2 0, 0⟩ : Link 2) ≠ ⟨0, 0⟩ := by decide
  have e2 : (⟨shift (-unitVec 2 0) 0, 1⟩ : Link 2) ≠ ⟨0, 0⟩ := fun h =>
    absurd (congrArg Link.μ h) (by decide)
  have e3 : (⟨shift (-unitVec 2 0) 1, 0⟩ : Link 2) ≠ ⟨0, 0⟩ := by decide
  have e4 : (⟨-unitVec 2 0, 1⟩ : Link 2) ≠ ⟨0, 0⟩ := by decide
  have hhol : plaquetteHolonomy (flipLink (⟨p₀.x, p₀.μ⟩ : Link 2)) (reflectPlaquette p₀) = 1 := by
    rw [reflectPlaquette_p₀, hl]
    simp [plaquetteHolonomy, flipLink, e1, e2, e3, e4]
  rw [plaquetteAction_eq_one_sub_halfTraceRe, hhol]
  simp [halfTraceRe, SU2.trace_one]

theorem oddFunctional_flipLink : oddFunctional (flipLink ⟨p₀.x, p₀.μ⟩) = 2 := by
  rw [oddFunctional, plaquetteAction_reflectConfig, plaquetteAction_flipLink_reflect,
    plaquetteAction_flipLink (by norm_num)]
  norm_num

/-- False strengthening: Osterwalder–Seiler positivity of the actual Wilson measure holds for
every continuous functional, without the positive-half locality hypothesis. Refuted on the
side-two torus at coupling `1` by a functional that is odd under the reflection. -/
theorem wilson_reflection_positive_needs_locality :
    ¬ ∀ H : GaugeConfig 2 → ℝ, Continuous H →
      0 ≤ ∫ U, H (reflectConfig U) * H U
        ∂(wilsonProbability 2 1 zero_le_one : Measure (GaugeConfig 2)) := by
  intro h
  have hle := h oddFunctional continuous_oddFunctional
  simp only [oddFunctional_reflect, neg_mul] at hle
  have hpos : 0 < ∫ U, oddFunctional U * oddFunctional U
      ∂(wilsonProbability 2 1 zero_le_one : Measure (GaugeConfig 2)) := by
    rw [wilsonProbability_integral]
    unfold wilsonExpectation
    apply div_pos _ (wilsonPartition_pos _ zero_le_one (measurable_wilsonAction 1))
    apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := flipLink ⟨p₀.x, p₀.μ⟩)
    · exact (show Continuous (boltzmannWeight (L := 2) 1) from
        Real.continuous_exp.comp (continuous_wilsonAction 1).neg).mul
          (continuous_oddFunctional.mul continuous_oddFunctional)
    · exact HasCompactSupport.of_compactSpace _
    · intro U
      exact mul_nonneg (Real.exp_pos _).le (mul_self_nonneg _)
    · show boltzmannWeight 1 (flipLink ⟨p₀.x, p₀.μ⟩) *
          (oddFunctional (flipLink ⟨p₀.x, p₀.μ⟩) * oddFunctional (flipLink ⟨p₀.x, p₀.μ⟩)) ≠ 0
      rw [oddFunctional_flipLink]
      exact mul_ne_zero (Real.exp_pos _).ne' (by norm_num)
  rw [integral_neg] at hle
  linarith

/-! ### 6. Time-dyadic positivity does not give full positivity -/

/-- A positive-time loop at the non-dyadic time `1/3`. -/
def thirdLoop : PhysicalRectangle :=
  ⟨fun i => if i = 0 then 1 / 3 else 0, 1, 2, by decide, 1, 1, one_pos, one_pos⟩

theorem not_isTimeDyadic_thirdLoop : ¬ IsTimeDyadic thirdLoop := by
  rintro ⟨m, j, r, hj, -⟩
  have h0 : ((thirdLoop.base 0 : ℚ) : ℝ) = 1 / 3 := by simp [thirdLoop]
  rw [h0] at hj
  have h2 : (2 : ℝ) ^ m = 3 * j := by
    field_simp at hj
    linarith
  have hjpos : 0 < j := by
    have : (0 : ℝ) < 3 * j := by rw [← h2]; positivity
    exact_mod_cast (by linarith : (0 : ℝ) < j)
  have h2' : (2 : ℕ) ^ m = 3 * j.toNat := by
    have : ((2 : ℕ) ^ m : ℝ) = ((3 * j.toNat : ℕ) : ℝ) := by
      push_cast
      rw [h2, show ((j.toNat : ℕ) : ℝ) = (j : ℝ) from by exact_mod_cast Int.toNat_of_nonneg hjpos.le]
    exact_mod_cast this
  have hdvd : 3 ∣ 2 ^ m := ⟨j.toNat, h2'⟩
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  norm_num at this

theorem timeReflect_ne_of_positive {ℓ ℓ' : PhysicalRectangle} (hℓ : ℓ.IsPositiveTime)
    (hℓ' : ℓ'.IsPositiveTime) : ℓ.timeReflect ≠ ℓ' := by
  intro h
  have hb := congrArg (fun ρ : PhysicalRectangle => ρ.base 0) h
  simp only [PhysicalRectangle.timeReflect, Function.update_self] at hb
  have hR := ℓ.sideμ_pos
  unfold PhysicalRectangle.IsPositiveTime at hℓ hℓ'
  split_ifs at hb <;> linarith

open Classical in
/-- `-1` on the non-dyadic loop, `1` on every other loop. -/
def thirdConfig : WilsonLoopSpace := fun ℓ => if ℓ = thirdLoop then -1 else 1

theorem thirdLoop_positive : thirdLoop.IsPositiveTime := by
  simp [PhysicalRectangle.IsPositiveTime, thirdLoop]

/-- The Dirac law at `thirdConfig` is reflection positive on all loops with dyadic time data:
on positive-time dyadic loops the configuration and its reflection agree. -/
theorem thirdConfig_isReflectionPositiveOn_timeDyadic :
    IsReflectionPositiveOn {ℓ | IsTimeDyadic ℓ} (diracProba thirdConfig) := by
  intro F hF
  rw [integral_diracProba]
  have hagree : F (reflectObservables thirdConfig) = F thirdConfig := by
    apply hF
    rintro ℓ ⟨hd, hpos⟩
    have h1 : ℓ.timeReflect ≠ thirdLoop := timeReflect_ne_of_positive hpos thirdLoop_positive
    have h2 : ℓ ≠ thirdLoop := fun h => not_isTimeDyadic_thirdLoop (h ▸ hd)
    simp [reflectObservables, thirdConfig, h1, h2]
  rw [hagree]
  exact mul_self_nonneg _

/-- False strengthening: reflection positivity on all loops with dyadic time data implies the
full `reflection_positive` condition, without any regularity hypothesis. -/
theorem timeDyadic_positivity_not_sufficient :
    ¬ ∀ ν : ProbabilityMeasure WilsonLoopSpace,
      IsReflectionPositiveOn {ℓ | IsTimeDyadic ℓ} ν → IsReflectionPositive ν := by
  intro h
  have hfull := h _ thirdConfig_isReflectionPositiveOn_timeDyadic
  have hdep : DependsOnPositiveTime (loopTest unitClamp thirdLoop) := by
    intro w w' hw
    simp only [loopTest_apply]
    rw [hw thirdLoop thirdLoop_positive]
  have hpos := hfull (loopTest unitClamp thirdLoop) hdep
  rw [integral_diracProba] at hpos
  have h1 : thirdConfig thirdLoop = -1 := by simp [thirdConfig]
  have h2 : reflectObservables thirdConfig thirdLoop = 1 := by
    have hne : thirdLoop.timeReflect ≠ thirdLoop :=
      timeReflect_ne_of_positive thirdLoop_positive thirdLoop_positive
    simp [reflectObservables, thirdConfig, hne]
  simp only [loopTest_apply, h1, h2, unitClamp_of_mem (by norm_num : (-1 : ℝ) ≤ 1)
    (by norm_num : (1 : ℝ) ≤ 1), unitClamp_of_mem (by norm_num : (-1 : ℝ) ≤ -1)
    (by norm_num : (-1 : ℝ) ≤ 1)] at hpos
  norm_num at hpos

/-! ### Positive controls -/

/-- The proved positivity applies to a functional of one link of the positive half. -/
example : 0 ≤ ∫ U, halfTraceRe (reflectConfig U ⟨0, 1⟩) * halfTraceRe (U ⟨0, 1⟩)
    ∂(wilsonProbability 2 1 zero_le_one : Measure (GaugeConfig 2)) := by
  apply wilson_reflection_positive (M := 1) (by norm_num) 1 zero_le_one
    (fun U => halfTraceRe (U ⟨0, 1⟩))
    (continuous_halfTraceRe.comp (continuous_apply _))
  intro U U' h
  rw [h ⟨0, 1⟩ (by decide)]

/-- Every subsequential limit along the explicit dyadic path is reflection positive on loops
with dyadic time data, unconditionally. -/
example {φ : ℕ → ℕ} (hφ : StrictMono φ) {ν : ProbabilityMeasure WilsonLoopSpace}
    (hlim : Tendsto (fun n => dyadicOneLoopPath.wilsonLoopLaw (φ n)) atTop (𝓝 ν)) :
    IsReflectionPositiveOn {ℓ | IsTimeDyadic ℓ} ν :=
  dyadicOneLoopPath_limit_isReflectionPositiveOn hφ hlim

/-- The family used above is nontrivial at every index and not time mixing. -/
example : IsNontrivial (signLaw 1) ∧ ¬ IsTimeMixing (signLaw 1) :=
  ⟨isNontrivial_signLaw one_pos le_rfl, not_isTimeMixing_signLaw one_pos le_rfl⟩

/-! ### 7. Positivity and the dyadic symmetries do not force regularity -/

open Classical in
/-- Loops with dyadic time data read `1`, all others `-1`. -/
def dyadicIndicator : WilsonLoopSpace := fun ℓ => if IsTimeDyadic ℓ then 1 else -1

/-- The Dirac law at that configuration. -/
def dyadicIndicatorLaw : ProbabilityMeasure WilsonLoopSpace :=
  ⟨Measure.dirac dyadicIndicator, inferInstance⟩

theorem dyadicIndicatorLaw_toMeasure :
    (dyadicIndicatorLaw : Measure WilsonLoopSpace) = Measure.dirac dyadicIndicator := rfl

theorem isTimeDyadic_timeReflect_iff (ℓ : PhysicalRectangle) :
    IsTimeDyadic ℓ.timeReflect ↔ IsTimeDyadic ℓ :=
  ⟨fun h => by simpa only [timeReflect_timeReflect] using h.timeReflect, IsTimeDyadic.timeReflect⟩

theorem dyadicIndicator_of_timeDyadic {ℓ : PhysicalRectangle} (h : IsTimeDyadic ℓ) :
    dyadicIndicator ℓ = 1 := by
  simp [dyadicIndicator, h]

theorem dyadicIndicator_of_not_timeDyadic {ℓ : PhysicalRectangle} (h : ¬ IsTimeDyadic ℓ) :
    dyadicIndicator ℓ = -1 := by
  simp [dyadicIndicator, h]

theorem dyadicIndicator_timeReflect (ℓ : PhysicalRectangle) :
    dyadicIndicator ℓ.timeReflect = dyadicIndicator ℓ := by
  by_cases h : IsTimeDyadic ℓ
  · rw [dyadicIndicator_of_timeDyadic h,
      dyadicIndicator_of_timeDyadic ((isTimeDyadic_timeReflect_iff ℓ).mpr h)]
  · rw [dyadicIndicator_of_not_timeDyadic h,
      dyadicIndicator_of_not_timeDyadic (mt (isTimeDyadic_timeReflect_iff ℓ).mp h)]

theorem reflect_dyadicIndicator : reflectObservables dyadicIndicator = dyadicIndicator :=
  funext dyadicIndicator_timeReflect

theorem dyadicIndicatorLaw_reflectionPositive : IsReflectionPositive dyadicIndicatorLaw := by
  intro F _
  rw [dyadicIndicatorLaw_toMeasure, integral_dirac, reflect_dyadicIndicator]
  exact mul_self_nonneg _

theorem dyadicIndicatorLaw_reflect_invariant :
    (dyadicIndicatorLaw : Measure WilsonLoopSpace).map reflectObservables = dyadicIndicatorLaw := by
  rw [dyadicIndicatorLaw_toMeasure, Measure.map_dirac' continuous_reflectObservables.measurable,
    reflect_dyadicIndicator]

/-- Translations whose time component is a dyadic rational: the lattice translations of every
dyadic cutoff, and so every translation symmetry the limits are proved to have. -/
def IsDyadicShift (c : Fin 4 → ℚ) : Prop := ∃ (m : ℕ) (j : ℤ), (c 0 : ℝ) = j / 2 ^ m

theorem IsDyadicShift.neg {c : Fin 4 → ℚ} (hc : IsDyadicShift c) : IsDyadicShift (-c) := by
  obtain ⟨m, j, hj⟩ := hc
  refine ⟨m, -j, ?_⟩
  have hneg : (((-c) 0 : ℚ) : ℝ) = -((c 0 : ℚ) : ℝ) := by simp
  rw [hneg, hj]
  push_cast
  ring

theorem isTimeDyadic_translate {ℓ : PhysicalRectangle} (h : IsTimeDyadic ℓ) {c : Fin 4 → ℚ}
    (hc : IsDyadicShift c) : IsTimeDyadic (ℓ.translate c) := by
  obtain ⟨m, j, r, hj, hr⟩ := h
  obtain ⟨m', j', hj'⟩ := hc
  have h2m : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2m' : (2 : ℝ) ^ m' ≠ 0 := pow_ne_zero _ two_ne_zero
  refine ⟨m + m', j * 2 ^ m' + j' * 2 ^ m, r * 2 ^ m', ?_, fun hμ => ?_⟩
  · have hb : (((ℓ.translate c).base 0 : ℚ) : ℝ) = ((ℓ.base 0 : ℚ) : ℝ) + ((c 0 : ℚ) : ℝ) := by
      simp [PhysicalRectangle.translate]
    rw [hb, hj, hj', div_add_div _ _ h2m h2m', pow_add]
    push_cast
    ring
  · have hμ' : ℓ.μ = 0 := hμ
    change ((ℓ.sideμ : ℚ) : ℝ) = _
    rw [hr hμ', pow_add]
    push_cast
    rw [mul_div_mul_right _ _ h2m']

theorem translate_neg_translate (ℓ : PhysicalRectangle) (c : Fin 4 → ℚ) :
    (ℓ.translate c).translate (-c) = ℓ := by
  rcases ℓ with ⟨b, μ, ν, h, R, T, hR, hT⟩
  simp [PhysicalRectangle.translate]

theorem translate_dyadicIndicator {c : Fin 4 → ℚ} (hc : IsDyadicShift c) :
    translateObservables c dyadicIndicator = dyadicIndicator := by
  funext ℓ
  change dyadicIndicator (ℓ.translate c) = dyadicIndicator ℓ
  by_cases h : IsTimeDyadic ℓ
  · rw [dyadicIndicator_of_timeDyadic h, dyadicIndicator_of_timeDyadic (isTimeDyadic_translate h hc)]
  · have h' : ¬ IsTimeDyadic (ℓ.translate c) := fun h' =>
      h (by simpa only [translate_neg_translate] using isTimeDyadic_translate h' hc.neg)
    rw [dyadicIndicator_of_not_timeDyadic h, dyadicIndicator_of_not_timeDyadic h']

theorem dyadicIndicatorLaw_translate {c : Fin 4 → ℚ} (hc : IsDyadicShift c) :
    (dyadicIndicatorLaw : Measure WilsonLoopSpace).map (translateObservables c) =
      dyadicIndicatorLaw := by
  rw [dyadicIndicatorLaw_toMeasure, Measure.map_dirac' (continuous_translateObservables c).measurable,
    translate_dyadicIndicator hc]

/-- The unit square in the `(1, 2)` plane at the origin: dyadic time data. -/
def originLoop : PhysicalRectangle := ⟨fun _ => 0, 1, 2, by decide, 1, 1, one_pos, one_pos⟩

theorem originLoop_timeDyadic : IsTimeDyadic originLoop :=
  ⟨0, 0, 0, by simp [originLoop], fun h => absurd h (by decide)⟩

/-- The time translation by one third, not a dyadic shift. -/
def thirdShift : Fin 4 → ℚ := fun i => if i = 0 then 1 / 3 else 0

/-- The origin loop moved to time one third: positive time, not dyadic. -/
def thirdTimeLoop : PhysicalRectangle := originLoop.translate thirdShift

theorem thirdTimeLoop_base_zero : thirdTimeLoop.base 0 = 1 / 3 := by
  simp [thirdTimeLoop, originLoop, thirdShift, PhysicalRectangle.translate]

theorem thirdTimeLoop_positiveTime : thirdTimeLoop.IsPositiveTime := by
  unfold PhysicalRectangle.IsPositiveTime
  rw [thirdTimeLoop_base_zero]
  norm_num

theorem thirdTimeLoop_not_timeDyadic : ¬ IsTimeDyadic thirdTimeLoop := by
  rintro ⟨m, j, -, hj, -⟩
  rw [thirdTimeLoop_base_zero] at hj
  have h2 : (2 : ℝ) ^ m = 3 * j := by
    have hpos : (0 : ℝ) < 2 ^ m := by positivity
    push_cast at hj
    field_simp at hj
    linarith
  have hz : (2 : ℤ) ^ m = 3 * j := by exact_mod_cast h2
  have hdvd : (3 : ℤ) ∣ 2 ^ m := ⟨j, hz⟩
  have h32 : (3 : ℤ) ∣ 2 := Int.prime_three.dvd_of_dvd_pow hdvd
  omega

/-- The same law is not invariant under the translation by one third. Positivity and every
dyadic symmetry leave rational translation covariance an independent question. -/
theorem dyadicIndicatorLaw_not_third_invariant :
    (dyadicIndicatorLaw : Measure WilsonLoopSpace).map (translateObservables thirdShift) ≠
      dyadicIndicatorLaw := by
  intro h
  rw [dyadicIndicatorLaw_toMeasure,
    Measure.map_dirac' (continuous_translateObservables thirdShift).measurable] at h
  have hS : MeasurableSet ((fun v : WilsonLoopSpace => v originLoop) ⁻¹' {1}) :=
    measurable_pi_apply originLoop (measurableSet_singleton (1 : ℝ))
  have hev := congrArg (fun μ : Measure WilsonLoopSpace =>
    μ ((fun v : WilsonLoopSpace => v originLoop) ⁻¹' {1})) h
  simp only [Measure.dirac_apply' _ hS] at hev
  have h0 : translateObservables thirdShift dyadicIndicator originLoop = -1 :=
    dyadicIndicator_of_not_timeDyadic thirdTimeLoop_not_timeDyadic
  have h1 : dyadicIndicator originLoop = 1 := dyadicIndicator_of_timeDyadic originLoop_timeDyadic
  have hmem : dyadicIndicator ∈ (fun v : WilsonLoopSpace => v originLoop) ⁻¹' {1} := h1
  have hnot : translateObservables thirdShift dyadicIndicator ∉
      (fun v : WilsonLoopSpace => v originLoop) ⁻¹' {1} := fun hm => by
    have hm' : translateObservables thirdShift dyadicIndicator originLoop = 1 := hm
    rw [h0] at hm'
    norm_num at hm'
  rw [Set.indicator_of_notMem hnot, Set.indicator_of_mem hmem] at hev
  simp at hev

/-- The same law is not dyadically approximable: the loop at time one third reads `-1` while
every dyadic approximant reads `1`. -/
theorem dyadicIndicatorLaw_not_dyadicTimeApproximable :
    ¬ DyadicTimeApproximable dyadicIndicatorLaw := by
  intro h
  obtain ⟨seq, hseq, hlim, -⟩ := h thirdTimeLoop thirdTimeLoop_positiveTime
  rw [dyadicIndicatorLaw_toMeasure, ae_dirac_eq, Filter.eventually_pure] at hlim
  have hconst : (fun k => dyadicIndicator (seq k)) = fun _ => (1 : ℝ) :=
    funext fun k => dyadicIndicator_of_timeDyadic (hseq k).1
  rw [hconst, dyadicIndicator_of_not_timeDyadic thirdTimeLoop_not_timeDyadic] at hlim
  have h11 : (1 : ℝ) = -1 := tendsto_nhds_unique tendsto_const_nhds hlim
  norm_num at h11

/-- False strengthening: a reflection-positive, reflection-invariant law invariant under every
dyadic time translation is dyadically approximable. -/
theorem regularity_not_implied_by_positivity_and_dyadic_symmetries :
    ¬ ∀ ν : ProbabilityMeasure WilsonLoopSpace, IsReflectionPositive ν →
      (ν : Measure WilsonLoopSpace).map reflectObservables = ν →
      (∀ c, IsDyadicShift c → (ν : Measure WilsonLoopSpace).map (translateObservables c) = ν) →
      DyadicTimeApproximable ν := fun h =>
  dyadicIndicatorLaw_not_dyadicTimeApproximable (h _ dyadicIndicatorLaw_reflectionPositive
    dyadicIndicatorLaw_reflect_invariant fun _ hc => dyadicIndicatorLaw_translate hc)

/-- False strengthening: the same hypotheses force invariance under every rational translation. -/
theorem rational_translation_not_implied_by_positivity_and_dyadic_symmetries :
    ¬ ∀ ν : ProbabilityMeasure WilsonLoopSpace, IsReflectionPositive ν →
      (ν : Measure WilsonLoopSpace).map reflectObservables = ν →
      (∀ c, IsDyadicShift c → (ν : Measure WilsonLoopSpace).map (translateObservables c) = ν) →
      ∀ c : Fin 4 → ℚ, (ν : Measure WilsonLoopSpace).map (translateObservables c) = ν := fun h =>
  dyadicIndicatorLaw_not_third_invariant (h _ dyadicIndicatorLaw_reflectionPositive
    dyadicIndicatorLaw_reflect_invariant (fun _ hc => dyadicIndicatorLaw_translate hc) thirdShift)

/-! ### 8. Positivity, every symmetry and clustering do not force nontriviality -/

/-- Every loop reads `1`. -/
def constantConfig : WilsonLoopSpace := fun _ => 1

/-- The Dirac law at the constant configuration. -/
def constantLaw : ProbabilityMeasure WilsonLoopSpace :=
  ⟨Measure.dirac constantConfig, inferInstance⟩

theorem constantLaw_toMeasure :
    (constantLaw : Measure WilsonLoopSpace) = Measure.dirac constantConfig := rfl

theorem reflect_constantConfig : reflectObservables constantConfig = constantConfig := rfl

theorem translate_constantConfig (c : Fin 4 → ℚ) :
    translateObservables c constantConfig = constantConfig := rfl

theorem constantLaw_reflectionPositive : IsReflectionPositive constantLaw := by
  intro F _
  rw [constantLaw_toMeasure, integral_dirac, reflect_constantConfig]
  exact mul_self_nonneg _

theorem constantLaw_reflect_invariant :
    (constantLaw : Measure WilsonLoopSpace).map reflectObservables = constantLaw := by
  rw [constantLaw_toMeasure, Measure.map_dirac' continuous_reflectObservables.measurable,
    reflect_constantConfig]

theorem constantLaw_translate_invariant (c : Fin 4 → ℚ) :
    (constantLaw : Measure WilsonLoopSpace).map (translateObservables c) = constantLaw := by
  rw [constantLaw_toMeasure, Measure.map_dirac' (continuous_translateObservables c).measurable,
    translate_constantConfig]

theorem constantLaw_timeMixing : IsTimeMixing constantLaw := by
  intro F G
  simp only [constantLaw_toMeasure, integral_dirac, translate_constantConfig]
  exact tendsto_const_nhds

/-- The constant law is trivial: any two loops are independent. -/
theorem constantLaw_trivial : ¬ IsNontrivial constantLaw := by
  rintro ⟨ℓ, ℓ', -, hind⟩
  apply hind
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hs' : MeasurableSet ((fun w : WilsonLoopSpace => w ℓ) ⁻¹' s) :=
    (continuous_apply ℓ).measurable hs
  have ht' : MeasurableSet ((fun w : WilsonLoopSpace => w ℓ') ⁻¹' t) :=
    (continuous_apply ℓ').measurable ht
  rw [constantLaw_toMeasure, Measure.dirac_apply' _ (hs'.inter ht'), Measure.dirac_apply' _ hs',
    Measure.dirac_apply' _ ht']
  by_cases h1 : (1 : ℝ) ∈ s <;> by_cases h2 : (1 : ℝ) ∈ t <;>
    simp [Set.indicator, constantConfig, h1, h2]

/-- False strengthening: positivity, reflection and translation invariance and time mixing
imply nontriviality. -/
theorem nontriviality_not_implied_by_positivity_symmetries_and_mixing :
    ¬ ∀ ν : ProbabilityMeasure WilsonLoopSpace, IsReflectionPositive ν →
      (ν : Measure WilsonLoopSpace).map reflectObservables = ν →
      (∀ c : Fin 4 → ℚ, (ν : Measure WilsonLoopSpace).map (translateObservables c) = ν) →
      IsTimeMixing ν → IsNontrivial ν := fun h =>
  constantLaw_trivial (h _ constantLaw_reflectionPositive constantLaw_reflect_invariant
    constantLaw_translate_invariant constantLaw_timeMixing)

#assert_zfc_axioms

end JesseMath.Physics.YangMillsOsterwalderSchraderInheritanceNegativeControl
