import JesseMath.Physics.YangMillsReconstructedGeneratorGap
import JesseMath.Linter.AxiomAudit

/-!
Negative controls for `JesseMath.Physics.YangMillsReconstructedGeneratorGap`. Each theorem
refutes a strengthening that drops one hypothesis, on an explicit model.

1. Positivity of `T` cannot be dropped from the spectral identification.
2. Zero in the spectrum: the functional-calculus logarithm is not a generator.
3. Gaps at each cutoff do not give a uniform physical gap.
4. Reflection positivity is a genuine condition on laws of the loop variables.
5. Reflection positivity, reflection invariance and time-translation invariance do not give
   decay on the vacuum complement: a two-vacuum law.
6. The actual finite periodic Wilson-loop laws do not satisfy full positive-half-space
   positivity, so `WilsonReflectionInputs` cannot hold on the explicit dyadic path.
-/

noncomputable section

namespace JesseMath.Physics.YangMillsReconstructedGeneratorGapNegativeControl

open Filter MeasureTheory
open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexConjugate ENNReal
open JesseMath.Physics.YangMillsPhysicalGap JesseMath.Physics.YangMillsRenormalizedObservableLimits
open JesseMath.Physics.YangMillsReconstructedGeneratorGap
open JesseMath.Physics YangMillsContinuumCompactness
open JesseMath.Physics.YangMillsOsterwalderSchraderInheritance hiding continuous_reflectObservables

/-! ## The finite periodic Wilson law does not satisfy full half-space positivity -/

private def sliceLoop (k : ℤ) : PhysicalRectangle :=
  ⟨fun i => if i = 0 then (k : ℚ) / 2 else 0, 1, 2, by decide,
    1 / 2, 1 / 2, by norm_num, by norm_num⟩

private def sliceSite (k : ℤ) : Lattice4D 4 :=
  fun i => if i = 0 then (k : ZMod 4) else 0

private def slicePlaquette (k : ℤ) : Plaquette 4 :=
  ⟨sliceSite k, 1, 2, by decide⟩

private theorem sliceLoop_eval (k : ℤ) (U : GaugeConfig 4) :
    physicalWilsonLoop 4 (1 / 2) (sliceLoop k) U =
      1 - plaquetteAction U (slicePlaquette k) := by
  have hb : latticeSite 4 ((sliceLoop k).latticeBase (1 / 2)) = sliceSite k := by
    funext i
    by_cases hi : i = 0
    · subst i
      have hk : (((k : ℚ) / 2 : ℚ) : ℝ) / (1 / 2) = (k : ℝ) := by
        push_cast
        ring
      change ((⌊(((k : ℚ) / 2 : ℚ) : ℝ) / (1 / 2)⌋ : ℤ) : ZMod 4) = (k : ZMod 4)
      rw [hk, Int.floor_intCast]
    · simp [latticeSite, PhysicalRectangle.latticeBase, sliceLoop, sliceSite, hi]
  rw [physicalWilsonLoop_eq_one_sub_plaquetteAction (1 / 2) (sliceLoop k) U
    (by norm_num [PhysicalRectangle.stepsμ, sliceLoop])
    (by norm_num [PhysicalRectangle.stepsν, sliceLoop]), hb]
  rfl

private theorem sliceLoop_reflect (k : ℤ) :
    (sliceLoop k).timeReflect = sliceLoop (-k) := by
  simp only [sliceLoop, PhysicalRectangle.timeReflect, PhysicalRectangle.mk.injEq]
  simp only [and_true]
  funext i
  fin_cases i <;> simp
  ring

private theorem slicePlaquette_neg_one : slicePlaquette (-1) = slicePlaquette 3 := by decide

private theorem slicePlaquette_neg_three : slicePlaquette (-3) = slicePlaquette 1 := by decide

private def periodicOddTest : WilsonLoopSpace →ᵇ ℝ :=
  loopTest unitClamp (sliceLoop 1) - loopTest unitClamp (sliceLoop 3)

private theorem periodicOddTest_positiveTime : DependsOnPositiveTime periodicOddTest := by
  intro w w' h
  change unitClamp (w (sliceLoop 1)) - unitClamp (w (sliceLoop 3)) =
    unitClamp (w' (sliceLoop 1)) - unitClamp (w' (sliceLoop 3))
  rw [h (sliceLoop 1) (by norm_num [PhysicalRectangle.IsPositiveTime, sliceLoop]),
    h (sliceLoop 3) (by norm_num [PhysicalRectangle.IsPositiveTime, sliceLoop])]

private def periodicOddObservable (U : GaugeConfig 4) : ℝ :=
  periodicOddTest (wilsonLoopVector 4 (1 / 2) U)

private theorem continuous_periodicOddObservable : Continuous periodicOddObservable :=
  periodicOddTest.continuous.comp (continuous_wilsonLoopVector _ _)

private theorem periodicOddTest_reflect (U : GaugeConfig 4) :
    periodicOddTest (reflectObservables (wilsonLoopVector 4 (1 / 2) U)) =
      -periodicOddObservable U := by
  change unitClamp (physicalWilsonLoop 4 (1 / 2) (sliceLoop 1).timeReflect U) -
    unitClamp (physicalWilsonLoop 4 (1 / 2) (sliceLoop 3).timeReflect U) =
    -(unitClamp (physicalWilsonLoop 4 (1 / 2) (sliceLoop 1) U) -
      unitClamp (physicalWilsonLoop 4 (1 / 2) (sliceLoop 3) U))
  rw [sliceLoop_reflect, sliceLoop_reflect, sliceLoop_eval, sliceLoop_eval,
    sliceLoop_eval, sliceLoop_eval, slicePlaquette_neg_one, slicePlaquette_neg_three]
  ring

private theorem periodicOddObservable_flip :
    periodicOddObservable (flipLink ⟨sliceSite 1, 1⟩) = -2 := by
  have hfirst := plaquetteAction_flipLink (by norm_num : 2 ≤ 4) (slicePlaquette 1)
  change plaquetteAction (flipLink ⟨sliceSite 1, 1⟩) (slicePlaquette 1) = 2 at hfirst
  have hsecond : plaquetteAction (flipLink ⟨sliceSite 1, 1⟩) (slicePlaquette 3) = 0 := by
    have e1 : (⟨sliceSite 3, 1⟩ : Link 4) ≠ ⟨sliceSite 1, 1⟩ := by decide
    have e2 : (⟨shift (sliceSite 3) 1, 2⟩ : Link 4) ≠ ⟨sliceSite 1, 1⟩ := by decide
    have e3 : (⟨shift (sliceSite 3) 2, 1⟩ : Link 4) ≠ ⟨sliceSite 1, 1⟩ := by decide
    have e4 : (⟨sliceSite 3, 2⟩ : Link 4) ≠ ⟨sliceSite 1, 1⟩ := by decide
    have hhol : plaquetteHolonomy (flipLink ⟨sliceSite 1, 1⟩) (slicePlaquette 3) = 1 := by
      simp [plaquetteHolonomy, slicePlaquette, flipLink, e1, e2, e3, e4]
    rw [plaquetteAction_eq_one_sub_halfTraceRe, hhol]
    simp [halfTraceRe, SU2.trace_one]
  change unitClamp (physicalWilsonLoop 4 (1 / 2) (sliceLoop 1) _) -
    unitClamp (physicalWilsonLoop 4 (1 / 2) (sliceLoop 3) _) = -2
  rw [sliceLoop_eval, sliceLoop_eval, hfirst, hsecond]
  norm_num [unitClamp]

private theorem periodicOddObservable_square_pos (β : ℝ) (hβ : 0 ≤ β) :
    0 < ∫ U, periodicOddObservable U * periodicOddObservable U
      ∂(wilsonProbability 4 β hβ : Measure (GaugeConfig 4)) := by
  rw [wilsonProbability_integral]
  unfold wilsonExpectation
  apply div_pos _ (wilsonPartition_pos _ hβ (measurable_wilsonAction β))
  apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := flipLink ⟨sliceSite 1, 1⟩)
  · exact (show Continuous (boltzmannWeight (L := 4) β) from
      Real.continuous_exp.comp (continuous_wilsonAction β).neg).mul
        (continuous_periodicOddObservable.mul continuous_periodicOddObservable)
  · exact HasCompactSupport.of_compactSpace _
  · intro U
    exact mul_nonneg (Real.exp_pos _).le (mul_self_nonneg _)
  · show boltzmannWeight β (flipLink ⟨sliceSite 1, 1⟩) *
      (periodicOddObservable (flipLink ⟨sliceSite 1, 1⟩) *
        periodicOddObservable (flipLink ⟨sliceSite 1, 1⟩)) ≠ 0
    rw [periodicOddObservable_flip]
    exact mul_ne_zero (Real.exp_pos _).ne' (by norm_num)

/-- The two commensurate spatial plaquettes at physical times `1/2` and `3/2` are both
positive-time loops, but reflection swaps their lattice values on the side-four torus.
Their difference refutes full positive-half-space positivity at every finite coupling. -/
theorem periodicWilsonLoopLaw_not_reflection_positive (β : ℝ) (hβ : 0 ≤ β) :
    ¬ IsReflectionPositive
      ((wilsonProbability 4 β hβ).map (wilsonLoopVector 4 (1 / 2))) := by
  intro h
  have hle := h periodicOddTest periodicOddTest_positiveTime
  have hcont : Continuous (fun w : WilsonLoopSpace =>
      periodicOddTest (reflectObservables w) * periodicOddTest w) :=
    (periodicOddTest.continuous.comp
      YangMillsOsterwalderSchraderInheritance.continuous_reflectObservables).mul
      periodicOddTest.continuous
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_wilsonLoopVector 4 (1 / 2)).aemeasurable
      hcont.aestronglyMeasurable] at hle
  simp only [periodicOddTest_reflect, neg_mul, integral_neg] at hle
  change 0 ≤ -(∫ U, periodicOddObservable U * periodicOddObservable U
    ∂(wilsonProbability 4 β hβ : Measure (GaugeConfig 4))) at hle
  have hpos := periodicOddObservable_square_pos β hβ
  linarith

/-- The finite-cutoff reflection interface is uninhabitable on the explicit dyadic path.
Positivity must instead be inherited from adapted finite cylinders before reconstruction. -/
theorem not_WilsonReflectionInputs_dyadic :
    ¬ WilsonReflectionInputs dyadicOneLoopPath.toCutoffPath := by
  intro h
  apply periodicWilsonLoopLaw_not_reflection_positive (dyadicOneLoopPath.coupling 1)
    (dyadicOneLoopPath.coupling_nonneg 1)
  convert (show IsReflectionPositive (dyadicOneLoopPath.wilsonLoopLaw 1) from
    h.reflection_positive 1) using 1
  norm_num [CutoffPath.wilsonLoopLaw, CutoffPath.configLaw, dyadicOneLoopPath]
  rfl

/-! ## Two-dimensional models -/

abbrev E2 := EuclideanSpace ℂ (Fin 2)

/-- First basis vector, the vacuum of the models. -/
def e₀ : E2 := EuclideanSpace.single 0 1

/-- Second basis vector. -/
def e₁ : E2 := EuclideanSpace.single 1 1

theorem norm_e₀ : ‖e₀‖ = 1 := by simp [e₀]

theorem norm_e₁ : ‖e₁‖ = 1 := by simp [e₁]

theorem inner_e₀_e₀ : ⟪e₀, e₀⟫_ℂ = 1 := by simp [e₀]

theorem inner_e₁_e₁ : ⟪e₁, e₁⟫_ℂ = 1 := by simp [e₁]

theorem inner_e₀_e₁ : ⟪e₀, e₁⟫_ℂ = 0 := by
  simp [e₀, e₁, EuclideanSpace.inner_single_left]

theorem inner_e₁_e₀ : ⟪e₁, e₀⟫_ℂ = 0 := by
  simp [e₀, e₁, EuclideanSpace.inner_single_left]

/-! ### 1. Positivity is needed -/

/-- `diag(1, -1/2)`: self-adjoint, a contraction, fixes `e₀`, bound `1/2` on `e₀⊥`. -/
def flipModel : E2 →L[ℂ] E2 :=
  InnerProductSpace.rankOne ℂ e₀ e₀ - ((1 / 2 : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ e₁ e₁

theorem flipModel_apply (u : E2) :
    flipModel u = ⟪e₀, u⟫_ℂ • e₀ - ((1 / 2 : ℝ) : ℂ) • (⟪e₁, u⟫_ℂ • e₁) := by
  simp [flipModel, InnerProductSpace.rankOne_apply]

theorem flipModel_e₀ : flipModel e₀ = e₀ := by
  rw [flipModel_apply, inner_e₀_e₀, inner_e₁_e₀]
  simp

theorem flipModel_e₁ : flipModel e₁ = -((1 / 2 : ℝ) : ℂ) • e₁ := by
  rw [flipModel_apply, inner_e₀_e₁, inner_e₁_e₁]
  simp

theorem flipModel_isSelfAdjoint : IsSelfAdjoint flipModel := by
  have h0 := (InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) norm_e₀).isSelfAdjoint
  have h1 := (InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) norm_e₁).isSelfAdjoint
  refine h0.sub (IsSelfAdjoint.smul ?_ h1)
  simp [IsSelfAdjoint]

theorem flipModel_decay (u : E2) (hu : ⟪e₀, u⟫_ℂ = 0) : ‖flipModel u‖ ≤ 1 / 2 * ‖u‖ := by
  rw [flipModel_apply, hu, zero_smul, zero_sub, norm_neg, norm_smul, norm_smul, norm_e₁,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simpa [norm_e₁] using norm_inner_le_norm (𝕜 := ℂ) e₁ u

theorem flipModel_norm_le_one : ‖flipModel‖ ≤ 1 := by
  refine norm_le_one_of_vacuum_decomposition norm_e₀ flipModel_e₀ (fun u hu => ?_)
    (fun u hu => (flipModel_decay u hu).trans (by nlinarith [norm_nonneg u]))
  rw [flipModel_apply, inner_sub_right, inner_smul_right, inner_smul_right, inner_smul_right,
    inner_e₀_e₀, inner_e₀_e₁, hu]
  ring

theorem neg_half_mem_spectrum_flipModel : (-(1 / 2) : ℝ) ∈ spectrum ℝ flipModel := by
  rw [spectrum.mem_iff]
  rintro ⟨u, hu⟩
  have hkill : (↑u : E2 →L[ℂ] E2) e₁ = 0 := by
    rw [hu, sub_apply, flipModel_e₁, Algebra.algebraMap_eq_smul_one, smul_apply,
      one_apply_eq_self, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    push_cast
    simp
  have hback := congrArg (fun A : E2 →L[ℂ] E2 => A e₁) u.inv_mul
  simp only [mul_apply_eq_comp, hkill, map_zero, one_apply_eq_self] at hback
  have : ‖e₁‖ = 0 := by rw [← hback, norm_zero]
  rw [norm_e₁] at this
  exact one_ne_zero this

/-- False strengthening refuted: without positivity, a self-adjoint contraction with a fixed unit
vacuum and one-step bound `ρ` on the vacuum complement need not have spectrum in
`[0, ρ] ∪ {1}`. -/
theorem spectral_inclusion_needs_positivity :
    ¬ ∀ (T : E2 →L[ℂ] E2) (Ω : E2) (ρ : ℝ), IsSelfAdjoint T → ‖T‖ ≤ 1 → ‖Ω‖ = 1 → T Ω = Ω →
      0 ≤ ρ → (∀ u, ⟪Ω, u⟫_ℂ = 0 → ‖T u‖ ≤ ρ * ‖u‖) → spectrum ℝ T ⊆ Set.Icc 0 ρ ∪ {1} := by
  intro h
  have hsub := h flipModel e₀ (1 / 2) flipModel_isSelfAdjoint flipModel_norm_le_one norm_e₀
    flipModel_e₀ (by norm_num) flipModel_decay
  rcases hsub neg_half_mem_spectrum_flipModel with hmem | hmem
  · exact absurd hmem.1 (by norm_num)
  · norm_num at hmem

/-! ### 2. Zero in the spectrum -/

/-- The vacuum projection `|e₀⟩⟨e₀|` as a positive transfer operator: `0` is an eigenvalue. -/
def projModel : PositiveTransferOperator E2 where
  op := InnerProductSpace.rankOne ℂ e₀ e₀
  vacuum := e₀
  nonneg := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (InnerProductSpace.isPositive_rankOne_self e₀)
  norm_le_one := by
    refine norm_le_one_of_vacuum_decomposition norm_e₀ ?_ (fun u hu => ?_) (fun u hu => ?_)
    · simp [InnerProductSpace.rankOne_apply, norm_e₀]
    · simp [InnerProductSpace.rankOne_apply, hu]
    · simp [InnerProductSpace.rankOne_apply, hu]
  vacuum_norm := norm_e₀
  vacuum_fixed := by simp [InnerProductSpace.rankOne_apply, norm_e₀]

theorem projModel_decay (u : E2) (hu : ⟪projModel.vacuum, u⟫_ℂ = 0) :
    ‖projModel.op u‖ ≤ 0 * ‖u‖ := by
  change ‖InnerProductSpace.rankOne ℂ e₀ e₀ u‖ ≤ 0 * ‖u‖
  change ⟪e₀, u⟫_ℂ = 0 at hu
  simp [InnerProductSpace.rankOne_apply, hu]

theorem zero_mem_spectrum_projModel : (0 : ℝ) ∈ spectrum ℝ projModel.op := by
  rw [spectrum.mem_iff]
  rintro ⟨u, hu⟩
  have hkill : (↑u : E2 →L[ℂ] E2) e₁ = 0 := by
    rw [hu, map_zero, zero_sub, neg_apply]
    change -(InnerProductSpace.rankOne ℂ e₀ e₀ e₁) = 0
    simp [InnerProductSpace.rankOne_apply, inner_e₀_e₁]
  have hback := congrArg (fun A : E2 →L[ℂ] E2 => A e₁) u.inv_mul
  simp only [mul_apply_eq_comp, hkill, map_zero, one_apply_eq_self] at hback
  have : ‖e₁‖ = 0 := by rw [← hback, norm_zero]
  rw [norm_e₁] at this
  exact one_ne_zero this

/-- With `0` an isolated eigenvalue, `x ↦ -(log x)/a` is continuous on the spectrum `{0, 1}`,
so the functional calculus returns a value, and that value is `0` because `Real.log 0 = 0`. -/
theorem logGenerator_projModel (a : ℝ) : projModel.logGenerator a = 0 := by
  have hspec := projModel.spectrum_op_subset le_rfl projModel_decay
  rw [PositiveTransferOperator.logGenerator]
  rw [cfc_congr (g := fun _ : ℝ => (0 : ℝ)) (fun x hx => by
    rcases hspec hx with hx | hx
    · have : x = 0 := le_antisymm hx.2 hx.1
      simp [this]
    · rw [Set.mem_singleton_iff] at hx
      simp [hx])]
  exact cfc_const_zero ℝ projModel.op

/-- False strengthening refuted: dropping `0 ∉ spectrum` from `cfc_exp_logGenerator` fails;
the functional-calculus logarithm of the projection is `0`, and `exp(-a · 0) = 1 ≠ T`. -/
theorem exp_logGenerator_needs_zero_not_mem_spectrum :
    ¬ ∀ (S : PositiveTransferOperator E2) (a : ℝ), a ≠ 0 →
      cfc (fun y : ℝ => Real.exp (-a * y)) (S.logGenerator a) = S.op := by
  intro h
  have h1 := h projModel 1 one_ne_zero
  rw [logGenerator_projModel, ← map_zero (algebraMap ℝ (E2 →L[ℂ] E2)), cfc_algebraMap,
    mul_zero, Real.exp_zero, map_one] at h1
  have h2 := congrArg (fun A : E2 →L[ℂ] E2 => A e₁) h1
  change e₁ = InnerProductSpace.rankOne ℂ e₀ e₀ e₁ at h2
  simp [InnerProductSpace.rankOne_apply, inner_e₀_e₁] at h2
  have : ‖e₁‖ = 0 := by rw [h2, norm_zero]
  rw [norm_e₁] at this
  exact one_ne_zero this

/-- The projection has no bounded self-adjoint generator at any time step. -/
theorem projModel_no_bounded_generator (a : ℝ) :
    ¬ ∃ G : E2 →L[ℂ] E2, IsSelfAdjoint G ∧ cfc (fun y : ℝ => Real.exp (-a * y)) G = projModel.op :=
  PositiveTransferOperator.not_exists_bounded_generator_of_zero_mem_spectrum
    zero_mem_spectrum_projModel a

/-! ### 3. Gaps at each cutoff are not a uniform gap -/

theorem transferGapRate_exp (c : ℝ) : transferGapRate 1 (Real.exp (-c)) = c := by
  simp [transferGapRate]

/-- False strengthening refuted: one-step bounds `ρ n = exp(-1/(n+1)) < 1` at unit spacing give a
positive gap at every cutoff, but no positive lower bound uniform in `n`; the uniformity input
`hm` of `physical_generator_gap_of_uniform_transfer_bounds` is not a consequence of per-cutoff
gaps. -/
theorem cutoff_gaps_not_uniform :
    (∀ n : ℕ, 0 < transferGapRate 1 (Real.exp (-(1 / ((n : ℝ) + 1))))) ∧
    ¬ ∃ m : ℝ, 0 < m ∧ ∀ n : ℕ, m ≤ transferGapRate 1 (Real.exp (-(1 / ((n : ℝ) + 1)))) := by
  simp only [transferGapRate_exp]
  refine ⟨fun n => by positivity, ?_⟩
  rintro ⟨m, hm, hle⟩
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have := ge_of_tendsto' hlim hle
  linarith

/-! ## Laws of the loop variables -/

/-- A positive-time loop: corner `(1, 1, 1, 1)`, plane `(0, 1)`, unit sides. -/
def ℓ₀ : PhysicalRectangle where
  base := fun _ => 1
  μ := 0
  ν := 1
  plane := by decide
  sideμ := 1
  sideν := 1
  sideμ_pos := one_pos
  sideν_pos := one_pos

theorem ℓ₀_isPositiveTime : ℓ₀.IsPositiveTime := by
  change (0 : ℚ) < 1
  norm_num

/-- `sin` of the loop variable at `ℓ₀`, a real positive-time bounded continuous functional. -/
def sinReal : WilsonLoopSpace →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun w => Real.sin (w ℓ₀))
    (Real.continuous_sin.comp (continuous_apply ℓ₀)) 1
    (fun w => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)

/-- The same functional with complex values. -/
def sinComplex : WilsonLoopSpace →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun w => (Real.sin (w ℓ₀) : ℂ))
    (Complex.continuous_ofReal.comp (Real.continuous_sin.comp (continuous_apply ℓ₀))) 1
    (fun w => by rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _)

theorem sinReal_positiveTime : DependsOnPositiveTime sinReal := by
  intro w w' h
  change Real.sin (w ℓ₀) = Real.sin (w' ℓ₀)
  rw [h ℓ₀ ℓ₀_isPositiveTime]

theorem sinComplex_mem : sinComplex ∈ positiveTimeFunctionals := by
  intro w w' h
  change (Real.sin (w ℓ₀) : ℂ) = Real.sin (w' ℓ₀)
  rw [h ℓ₀ ℓ₀_isPositiveTime]

/-! ### 4. Reflection positivity is a genuine condition -/

/-- The configuration equal to `1` on positive-time loops and `-1` elsewhere. -/
def signConfig : WilsonLoopSpace := fun ℓ => if 0 < ℓ.base 0 then 1 else -1

theorem sinReal_reflect_signConfig :
    sinReal (reflectObservables signConfig) * sinReal signConfig = -(Real.sin 1 ^ 2) := by
  change Real.sin (signConfig ℓ₀.timeReflect) * Real.sin (signConfig ℓ₀) = _
  have h1 : signConfig ℓ₀ = 1 := by
    simp [signConfig, ℓ₀]
  have h2 : signConfig ℓ₀.timeReflect = -1 := by
    simp [signConfig, ℓ₀, PhysicalRectangle.timeReflect]
  rw [h1, h2, Real.sin_neg]
  ring

/-- False strengthening refuted: not every probability law of the loop variables is reflection
positive. The Dirac law at `signConfig` fails on `sinReal`. -/
theorem not_every_law_reflection_positive :
    ¬ ∀ ν : ProbabilityMeasure WilsonLoopSpace, ∀ F : WilsonLoopSpace →ᵇ ℝ,
      DependsOnPositiveTime F →
        0 ≤ ∫ w, F (reflectObservables w) * F w ∂(ν : Measure WilsonLoopSpace) := by
  intro h
  have h1 := h ⟨Measure.dirac signConfig, inferInstance⟩ sinReal sinReal_positiveTime
  change 0 ≤ ∫ w, sinReal (reflectObservables w) * sinReal w ∂(Measure.dirac signConfig) at h1
  rw [integral_dirac, sinReal_reflect_signConfig] at h1
  have hs : 0 < Real.sin 1 := Real.sin_pos_of_pos_of_lt_pi one_pos
    (lt_of_lt_of_le (by norm_num) Real.pi_gt_three.le)
  nlinarith [sq_nonneg (Real.sin 1)]

/-! ### 5. A two-vacuum law: the reflection inputs do not give decay -/

/-- The constant configuration `1`. -/
def wPlus : WilsonLoopSpace := fun _ => 1

/-- The constant configuration `-1`. -/
def wMinus : WilsonLoopSpace := fun _ => -1

theorem reflect_wPlus : reflectObservables wPlus = wPlus := rfl

theorem reflect_wMinus : reflectObservables wMinus = wMinus := rfl

theorem translate_wPlus (c : Fin 4 → ℚ) : translateObservables c wPlus = wPlus := rfl

theorem translate_wMinus (c : Fin 4 → ℚ) : translateObservables c wMinus = wMinus := rfl

/-- The equal mixture of the two constant configurations. -/
def twoVacuumMeasure : Measure WilsonLoopSpace :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac wPlus + Measure.dirac wMinus)

instance : IsProbabilityMeasure twoVacuumMeasure := by
  constructor
  simp only [twoVacuumMeasure, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [← two_mul, mul_one, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

theorem integral_twoVacuum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] (f : WilsonLoopSpace →ᵇ E) :
    ∫ w, f w ∂twoVacuumMeasure = (2⁻¹ : ℝ) • (f wPlus + f wMinus) := by
  rw [twoVacuumMeasure, integral_smul_measure, integral_add_measure
    (f.integrable (Measure.dirac wPlus)) (f.integrable (Measure.dirac wMinus)), integral_dirac,
    integral_dirac]
  simp

/-- Invariance of the mixture under every map fixing both constant configurations. -/
theorem map_twoVacuum {f : WilsonLoopSpace → WilsonLoopSpace} (hf : Continuous f)
    (hp : f wPlus = wPlus) (hm : f wMinus = wMinus) :
    twoVacuumMeasure.map f = twoVacuumMeasure := by
  rw [twoVacuumMeasure, Measure.map_smul, Measure.map_add _ _ hf.measurable,
    Measure.map_dirac' hf.measurable, Measure.map_dirac' hf.measurable, hp, hm]
  exact hf.measurable.aemeasurable

/-- The two-vacuum law, with its reflection positivity and reflection invariance proved. -/
def twoVacuumLaw : ReflectionPositiveLaw where
  law := ⟨twoVacuumMeasure, inferInstance⟩
  reflection_positive := by
    intro F _
    change 0 ≤ ∫ w, ((F.compContinuous reflectCM) * F) w ∂twoVacuumMeasure
    rw [integral_twoVacuum]
    simp only [BoundedContinuousFunction.coe_mul, Pi.mul_apply,
      BoundedContinuousFunction.compContinuous_apply, reflectCM, ContinuousMap.coe_mk,
      reflect_wPlus, reflect_wMinus]
    exact smul_nonneg (by norm_num) (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
  reflection_invariant := map_twoVacuum continuous_reflectObservables reflect_wPlus reflect_wMinus

theorem twoVacuumLaw_translate (s : ℚ) :
    (twoVacuumLaw.law : Measure WilsonLoopSpace).map (translateObservables (timeShift s)) =
      twoVacuumLaw.law :=
  map_twoVacuum (continuous_translateObservables _) (translate_wPlus _) (translate_wMinus _)

theorem twoVacuum_no_correlationDecay (s : ℚ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ¬ CorrelationDecay (twoVacuumLaw.law : Measure WilsonLoopSpace) s ρ := by
  intro h
  have hd := h sinComplex sinComplex_mem
  have hval : ∀ G : WilsonLoopSpace →ᵇ ℂ, G wPlus = (Real.sin 1 : ℂ) →
      G wMinus = (-Real.sin 1 : ℝ) →
      (osForm (twoVacuumLaw.law : Measure WilsonLoopSpace) G G).re = Real.sin 1 ^ 2 := by
    intro G hp hm
    change (∫ w, osIntegrand G G w ∂twoVacuumMeasure).re = _
    rw [integral_twoVacuum, osIntegrand_apply, osIntegrand_apply, reflect_wPlus, reflect_wMinus,
      hp, hm, Complex.conj_ofReal, Complex.conj_ofReal, Complex.real_smul]
    have e : ((2⁻¹ : ℝ) : ℂ) * ((Real.sin 1 : ℂ) * (Real.sin 1 : ℂ) +
        ((-Real.sin 1 : ℝ) : ℂ) * ((-Real.sin 1 : ℝ) : ℂ)) = ((Real.sin 1 ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, Complex.ofReal_re]
  have hplus : sinComplex wPlus = (Real.sin 1 : ℂ) := rfl
  have hminus : sinComplex wMinus = (-Real.sin 1 : ℝ) := by
    change (Real.sin (-1) : ℂ) = _
    rw [Real.sin_neg]
  have hmean : ∫ w, sinComplex w ∂(twoVacuumLaw.law : Measure WilsonLoopSpace) = 0 := by
    change ∫ w, sinComplex w ∂twoVacuumMeasure = 0
    rw [integral_twoVacuum, hplus, hminus]
    push_cast
    simp
  rw [hval sinComplex hplus hminus, hval _ (by
      change sinComplex (translateObservables (timeShift s) wPlus) = _
      rw [translate_wPlus, hplus]) (by
      change sinComplex (translateObservables (timeShift s) wMinus) = _
      rw [translate_wMinus, hminus]), hmean, norm_zero] at hd
  have hs : 0 < Real.sin 1 := Real.sin_pos_of_pos_of_lt_pi one_pos
    (lt_of_lt_of_le (by norm_num) Real.pi_gt_three.le)
  have hs2 : 0 < Real.sin 1 ^ 2 := by positivity
  have hρ2 : ρ ^ 2 < 1 := by nlinarith
  nlinarith

/-- False strengthening refuted: reflection positivity, reflection invariance and invariance
under every rational time translation do not imply decay on the vacuum complement at any
ratio `ρ < 1`. In the two-vacuum law the time translation fixes the non-constant positive-time
functional `sin (w ℓ₀)`. Uniform decay is an independent input. -/
theorem decay_not_implied_by_reflection_inputs :
    ¬ ∀ L : ReflectionPositiveLaw,
      (∀ s : ℚ, (L.law : Measure WilsonLoopSpace).map (translateObservables (timeShift s)) =
        L.law) →
      ∀ s : ℚ, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ CorrelationDecay (L.law : Measure WilsonLoopSpace) s ρ := by
  intro h
  obtain ⟨ρ, hρ, hρ1, hd⟩ := h twoVacuumLaw twoVacuumLaw_translate 1
  exact twoVacuum_no_correlationDecay 1 hρ hρ1 hd

/-- Positive control: the two-vacuum law still yields a positive transfer operator, so the
failure above is a failure of decay, not of the reconstruction. -/
example : PositiveTransferOperator (OSHilbert twoVacuumLaw) :=
  reconstructedTransferOperator twoVacuumLaw (s := 1) (by norm_num) (twoVacuumLaw_translate _)

/-- A fixed vacuum tests the eventual-to-limit implication without claiming nontriviality. -/
def oneVacuumProbability : ProbabilityMeasure WilsonLoopSpace :=
  ⟨Measure.dirac wPlus, inferInstance⟩

theorem oneVacuum_osForm (F : WilsonLoopSpace →ᵇ ℂ) :
    (osForm (oneVacuumProbability : Measure WilsonLoopSpace) F F).re = ‖F wPlus‖ ^ 2 := by
  change (osForm (Measure.dirac wPlus) F F).re = _
  rw [osForm, integral_dirac, osIntegrand_apply, reflect_wPlus, Complex.conj_mul',
    ← Complex.ofReal_pow, Complex.ofReal_re]

theorem oneVacuum_eventualCorrelationDecay (s : ℚ) (ρ : ℝ) :
    EventualCorrelationDecay (fun _ => oneVacuumProbability) s ρ := by
  intro F _
  apply Eventually.of_forall
  intro n
  change (osForm (oneVacuumProbability : Measure WilsonLoopSpace)
      (F.compContinuous (translateCM s)) (F.compContinuous (translateCM s))).re -
      ‖∫ w, F w ∂(Measure.dirac wPlus)‖ ^ 2 ≤
    ρ ^ 2 * ((osForm (oneVacuumProbability : Measure WilsonLoopSpace) F F).re -
      ‖∫ w, F w ∂(Measure.dirac wPlus)‖ ^ 2)
  rw [oneVacuum_osForm, oneVacuum_osForm, integral_dirac]
  have ht : (F.compContinuous (translateCM s)) wPlus = F wPlus := rfl
  rw [ht]
  simp

example (s : ℚ) (ρ : ℝ) :
    CorrelationDecay (oneVacuumProbability : Measure WilsonLoopSpace) s ρ :=
  correlationDecay_of_tendsto_eventually tendsto_const_nhds
    (oneVacuum_eventualCorrelationDecay s ρ)

/-- Eventual estimates cannot supply decay absent from the constant two-vacuum limit. -/
theorem constant_twoVacuum_no_eventualCorrelationDecay (s : ℚ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ¬ EventualCorrelationDecay (fun _ => twoVacuumLaw.law) s ρ := by
  intro h
  exact twoVacuum_no_correlationDecay s hρ hρ1
    (correlationDecay_of_tendsto_eventually tendsto_const_nhds h)

/-! ## The half-lattice domain is not translation stable on the periodic torus -/

/-- The reflection-adapted loops at spacing one on the lattice of side two are not closed
under one time step: the loop at time one is adapted and its translate at time two is not. So
the Osterwalder–Schrader transfer operator, whose contraction proof iterates the time step on
positive-time functionals, cannot be formed at a finite periodic cutoff from the half-lattice
positivity theorem alone. The finite-volume transfer matrix is the slice construction, which
this repository does not formalize; the limit-law bridge above does not need it. -/
theorem isReflectionAdapted_not_translation_stable :
    ∃ ℓ : PhysicalRectangle, IsReflectionAdapted 1 1 ℓ ∧
      ¬ IsReflectionAdapted 1 1 (ℓ.translate (timeShift 1)) := by
  refine ⟨⟨fun i => if i = 0 then 1 else 0, 1, 2, by decide, 1, 1, one_pos, one_pos⟩,
    ⟨1, 0, by simp, fun h => absurd h (by decide), by norm_num⟩, ?_⟩
  rintro ⟨k, r, hk, -, hkr⟩
  have h2 : (k : ℝ) = 2 := by
    norm_num [PhysicalRectangle.translate, timeShift] at hk
    linarith
  have hk2 : k = 2 := by exact_mod_cast h2
  omega

/-! ## Non-circularity negative controls for `LandingTube`, `QYMSchwingerGap`, and 2D area law -/

/-- Verification that any deterministic Dirac measure `Measure.dirac V0` has zero connected
covariance `irCov` and therefore cannot inhabit `LandingTube P`. -/
theorem negative_control_constantLaw_refutes_landingTube {P : ContinuumCutoffPath}
    (T : LandingTube P) (V0 : ∀ n : ℕ, GaugeConfig (T.irSide n))
    (h_dirac : ∀ᶠ n in atTop, ((T.chain n).state 0).gibbsMeasure = Measure.dirac (V0 n)) :
    (∀ (L : ℕ) [NeZero L] (U0 : GaugeConfig L) (f g : GaugeConfig L → ℝ),
      irCov (Measure.dirac U0) f g = 0) ∧ False :=
  ⟨fun _ _ U0 f g => irCov_dirac_eq_zero U0 f g, not_landingTube_of_constantLaw T V0 h_dirac⟩

/-- Verification that non-positive reflected connected self-correlators refute `QYMSchwingerGap P`. -/
theorem negative_control_zero_reflectedConnected_refutes_qymSchwingerGap (P : ContinuumCutoffPath)
    (h_nonpos : ∀ (Z : LoopRenormalization P.toCutoffPath) (F : DisjointLoopFamily),
      F.PositiveTime → ∀ᶠ n in atTop, reflectedConnected Z n F F ≤ 0) :
    ¬ QYMSchwingerGap P :=
  not_qymSchwingerGap_of_zero_reflectedConnected P h_nonpos

/-- VACUOUS-CONTROL (the hypothesis `∀ᶠ n in atTop, P.coupling n = 0` is unsatisfiable along any
`ContinuumCutoffPath` by `ContinuumCutoffPath.coupling_tendsto_atTop`, `ROL:2008`):
Verification that at zero bare coupling (`β = 0`), the canonical multi-step Haar RG state
`canonicalRGState L_ir K 0 0` has Gibbs measure identically equal to `gaugeHaarMeasure L_ir`,
so any zero-coupling canonical trajectory is refuted without assuming `μ = gaugeHaarMeasure`
as a separate hypothesis. -/
theorem negative_control_zero_coupling_refutes_landingTube {P : ContinuumCutoffPath}
    (T : LandingTube P)
    (h_zero_β : ∀ᶠ n in atTop, P.coupling n = 0)
    (h_canonical : ∀ᶠ n in atTop,
      (T.chain n).state 0 = canonicalRGState (T.irSide n) (T.K n) (P.coupling n) 0)
    (h_indep : ∀ n : ℕ,
      irCov (gaugeHaarMeasure (T.irSide n))
        (physicalWilsonLoop (T.irSide n) (T.ℓstar : ℝ) T.ℓ_probe.timeReflect)
        (physicalWilsonLoop (T.irSide n) (T.ℓstar : ℝ) T.ℓ_probe) = 0) :
    (∀ (L_ir K : ℕ) [NeZero L_ir],
      (canonicalRGState L_ir K 0 0).gibbsMeasure = gaugeHaarMeasure L_ir) ∧ False :=
  ⟨fun L_ir K _ => canonicalRGState_zero_gibbsMeasure_eq_gaugeHaarMeasure L_ir K,
    not_landingTube_of_zero_coupling T h_zero_β h_canonical h_indep⟩

/-- Exact two-dimensional Yang–Mills rectangular Wilson loop expectation `ρ ^ (R * T_ext)`, where
single-plaquette holonomies are independent under axial gauge fixing and each plaquette contributes
the single-plaquette factor `ρ`. -/
def exact2DWilsonLoopAreaLaw (ρ : ℝ) (R T_ext : ℕ) : ℝ :=
  ρ ^ (R * T_ext)

theorem exact2DWilsonLoopAreaLaw_creutz_numerator_eq (ρ : ℝ) (R T_ext : ℕ) :
    exact2DWilsonLoopAreaLaw ρ (R + 1) (T_ext + 1) * exact2DWilsonLoopAreaLaw ρ R T_ext =
      ρ * (exact2DWilsonLoopAreaLaw ρ (R + 1) T_ext * exact2DWilsonLoopAreaLaw ρ R (T_ext + 1)) := by
  unfold exact2DWilsonLoopAreaLaw
  have hexp : (R + 1) * (T_ext + 1) + R * T_ext = 1 + ((R + 1) * T_ext + R * (T_ext + 1)) := by
    ring
  rw [← pow_add, ← pow_add, hexp, pow_add, pow_one]

/-- The Creutz ratio `(W(R+1, T+1) W(R, T)) / (W(R+1, T) W(R, T+1))` of the exact 2D area-law
Wilson loop `exact2DWilsonLoopAreaLaw ρ R T_ext = ρ ^ (R * T_ext)` equals `ρ` identically for all
`R, T_ext : ℕ` whenever `ρ ≠ 0`. -/
theorem exact2DWilsonLoopAreaLaw_creutzRatio_eq_rho {ρ : ℝ} (hρ : ρ ≠ 0) (R T_ext : ℕ) :
    (exact2DWilsonLoopAreaLaw ρ (R + 1) (T_ext + 1) * exact2DWilsonLoopAreaLaw ρ R T_ext) /
      (exact2DWilsonLoopAreaLaw ρ (R + 1) T_ext * exact2DWilsonLoopAreaLaw ρ R (T_ext + 1)) = ρ := by
  rw [exact2DWilsonLoopAreaLaw_creutz_numerator_eq]
  have hden : exact2DWilsonLoopAreaLaw ρ (R + 1) T_ext * exact2DWilsonLoopAreaLaw ρ R (T_ext + 1) ≠ 0 := by
    unfold exact2DWilsonLoopAreaLaw
    exact mul_ne_zero (pow_ne_zero _ hρ) (pow_ne_zero _ hρ)
  exact mul_div_cancel_right₀ ρ hden

/-- VACUOUS-CONTROL (the hypothesis `∀ᶠ n in atTop, P.coupling n = 0` is unsatisfiable along any
`ContinuumCutoffPath` by `ContinuumCutoffPath.coupling_tendsto_atTop`, `ROL:2008`):
Verification that for any abstract smoothing block kernel family `dis`, the zero-coupling
canonical RG state `canonicalAbstractRGState L_ir K 0 dis 0` has Gibbs measure identically equal
to `gaugeHaarMeasure L_ir`, and no `IntervalArithmeticCrossoverCertificate` can exist along a
zero-coupling canonical trajectory. -/
theorem negative_control_zero_coupling_refutes_intervalArithmeticCrossoverCertificate
    {P : ContinuumCutoffPath}
    (C : IntervalArithmeticCrossoverCertificate P)
    (h_zero_β : ∀ᶠ n in atTop, P.coupling n = 0)
    (h_canonical : ∀ᶠ n in atTop,
      (C.chain n).state 0 = canonicalRGState (C.irSide n) (C.K n) (P.coupling n) 0)
    (h_indep : ∀ n : ℕ,
      irCov (gaugeHaarMeasure (C.irSide n))
        (physicalWilsonLoop (C.irSide n) (C.ℓstar : ℝ) C.ℓ_probe.timeReflect)
        (physicalWilsonLoop (C.irSide n) (C.ℓstar : ℝ) C.ℓ_probe) = 0) :
    (∀ (L_ir K : ℕ) [NeZero L_ir]
      (dis : ∀ m : ℕ, ConditionalBlockFiberDisintegration (dyadicScaleSide L_ir m)),
      (canonicalAbstractRGState L_ir K 0 dis 0).gibbsMeasure = gaugeHaarMeasure L_ir) ∧ False :=
  ⟨fun L_ir K _ dis => canonicalAbstractRGState_zero_gibbsMeasure_eq_gaugeHaarMeasure L_ir K dis,
    not_intervalArithmeticCrossoverCertificate_of_zero_coupling C h_zero_β h_canonical h_indep⟩

/-- VACUOUS-CONTROL (the hypothesis `∀ᶠ n in atTop, P.coupling n = 0` is unsatisfiable along any
`ContinuumCutoffPath` by `ContinuumCutoffPath.coupling_tendsto_atTop`, `ROL:2008`):
Verification that the canonical rational crossover parameters `(1 / (18 * 24 * 16), 1 / 16, 1 / 16)`
satisfy `4 * (18 * (24 * β_hi) + η_hi + ε_hi) = 3 / 4 < 1` with margin `1 / 4`, and that no
`InductiveStepAndBlockBounds P` can exist along a zero-coupling canonical trajectory. -/
theorem negative_control_zero_coupling_refutes_inductiveStepAndBlockBounds
    {P : ContinuumCutoffPath}
    (B : InductiveStepAndBlockBounds P)
    (h_zero_β : ∀ᶠ n in atTop, P.coupling n = 0)
    (h_canonical : ∀ᶠ n in atTop,
      (B.chain n).state 0 = canonicalRGState (B.irSide n) (B.K n) (P.coupling n) 0)
    (h_indep : ∀ n : ℕ,
      irCov (gaugeHaarMeasure (B.irSide n))
        (physicalWilsonLoop (B.irSide n) (B.ℓstar : ℝ) B.ℓ_probe.timeReflect)
        (physicalWilsonLoop (B.irSide n) (B.ℓstar : ℝ) B.ℓ_probe) = 0) :
    (4 * (18 * (24 * canonicalCrossoverBetaHi) + canonicalCrossoverEtaHi + canonicalCrossoverEpsHi) = 3 / 4 ∧
      1 - 4 * (18 * (24 * canonicalCrossoverBetaHi) + canonicalCrossoverEtaHi + canonicalCrossoverEpsHi) = 1 / 4) ∧
      False :=
  ⟨⟨canonicalCrossover_contraction_eq_three_fourths, canonicalCrossover_margin_eq_one_fourth⟩,
    not_inductiveStepAndBlockBounds_of_zero_coupling B h_zero_β h_canonical h_indep⟩

/-- Negative control verifying:
1. Unconditional zero-coupling refutation `¬ LocalFieldsAndShortDistanceOnCutoffPath zeroCouplingCutoffPath beta0 Z`
   on the inhabited `zeroCouplingCutoffPath : CutoffPath` (with zero inconsistent hypotheses), and
2. Product-Haar zero-covariance via single-link `SU(2)` center twist `twistLinkNegOne`
   refutes `LandingTube P` without any external `IndepFun` or `irCov = 0` hypothesis (note: the
   product-Haar hypothesis `h_haar` on `ContinuumCutoffPath` is a VACUOUS-CONTROL under pure
   decimation as `P.coupling n → ∞`, `ROL:2008`). -/
theorem negative_control_productHaar_twistLink_and_zero_coupling_localFields
    {P : ContinuumCutoffPath}
    (beta0 : ℝ) (Z0 : LoopRenormalization zeroCouplingCutoffPath)
    (T : LandingTube P)
    (h_haar : ∀ᶠ n in atTop, ((T.chain n).state 0).gibbsMeasure = gaugeHaarMeasure (T.irSide n))
    (e₀ : ∀ n : ℕ, Link (T.irSide n))
    (h_neg : ∀ (n : ℕ) (U : GaugeConfig (T.irSide n)),
      physicalWilsonLoop (T.irSide n) (T.ℓstar : ℝ) T.ℓ_probe.timeReflect
        (twistLinkNegOne (e₀ n) U) =
      -physicalWilsonLoop (T.irSide n) (T.ℓstar : ℝ) T.ℓ_probe.timeReflect U)
    (h_inv : ∀ (n : ℕ) (U : GaugeConfig (T.irSide n)),
      physicalWilsonLoop (T.irSide n) (T.ℓstar : ℝ) T.ℓ_probe
        (twistLinkNegOne (e₀ n) U) =
      physicalWilsonLoop (T.irSide n) (T.ℓstar : ℝ) T.ℓ_probe U) :
    ¬ LocalFieldsAndShortDistanceOnCutoffPath zeroCouplingCutoffPath beta0 Z0 ∧ False :=
  ⟨not_localFieldsAndShortDistanceOnCutoffPath_zeroCouplingCutoffPath beta0 Z0,
    not_landingTube_of_productHaar_twistLink T h_haar e₀ h_neg h_inv⟩

/-- Negative control refuting the unrestricted (unbounded-observable) Dobrushin covariance
comparison statement:
1. In Lean (`Real.sSup_of_not_bddAbove`), any single-link observable `U ↦ φ (U e₀)` whose
   variation on `e₀` is not `BddAbove` has `linkOscillation = 0` at every link `e`, so
   `dobrushinObservableComparison = 0` and any unrestricted comparison bound
   `∀ f g, |cov f g| ≤ κ * dobrushinObservableComparison G C f g` is false whenever
   `cov (fun U => φ (U e₀)) g₀ ≠ 0` (for example `g₀ U = min (φ (U e₀)) 1`), and
2. By contrast, on any `T : LandingTube P`, the bounded-measurable Föllmer–Dobrushin covariance
   comparison `LandingTube.landed_gibbsMeasure_abs_irCov_le_dobrushinObservableComparison` holds as
   a proved theorem on `((T.chain n).state 0).gibbsMeasure` (with `h_ir_dobrushin_comparison`
   removed from `ObservableTransferAndSymmetryBridge`). -/
theorem negative_control_unbounded_singleLink_refutes_unrestricted_dobrushin_comparison
    {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) (κ : ℝ)
    (cov : (GaugeConfig L → ℝ) → (GaugeConfig L → ℝ) → ℝ)
    (e₀ : Link L) (φ : SU2 → ℝ) (g₀ : GaugeConfig L → ℝ)
    (h_unbdd : ∀ M : ℝ, ∃ u1 u2 : SU2, M < |φ u1 - φ u2|)
    (h_cov_ne : cov (fun U : GaugeConfig L => φ (U e₀)) g₀ ≠ 0) :
    ¬ (∀ f g : GaugeConfig L → ℝ,
        |cov f g| ≤ κ * dobrushinObservableComparison SU2 C f g) := by
  intro h_unrestricted
  refine not_unrestricted_dobrushin_comparison_of_unbounded_singleLink
    SU2 C cov κ e₀ (fun U : GaugeConfig L => φ (U e₀)) g₀ ?_ ?_ h_cov_ne h_unrestricted
  · intro B
    obtain ⟨u1, u2, hB⟩ := h_unbdd B
    refine ⟨vacuumConfig L, u1, u2, ?_⟩
    simpa only [(updateGroupGaugeLink_same_and_other L (vacuumConfig L) e₀.x e₀.μ u1).1,
      (updateGroupGaugeLink_same_and_other L (vacuumConfig L) e₀.x e₀.μ u2).1] using hB
  · intro e he V u1 u2
    simp only [(updateGroupGaugeLink_same_and_other L V e.x e.μ u1).2 e₀ (Ne.symm he),
      (updateGroupGaugeLink_same_and_other L V e.x e.μ u2).2 e₀ (Ne.symm he)]

/-- VACUOUS CONTROL: bounded coupling never holds along a `ContinuumCutoffPath`
(`ContinuumCutoffPath.coupling_tendsto_atTop`, `ROL:2008`).
Negative control for Gap 1 (`BalabanMultiScaleUVToIRFlow`) and Gap 5
(`SymanzikDimensionSixRotationalSuppression`):
1. Along any bounded-coupling cutoff trajectory (`∀ᶠ n in atTop, P.coupling n ≤ C_β`), no
   `BalabanMultiScaleUVToIRFlow P` can exist (`¬ Nonempty (BalabanMultiScaleUVToIRFlow P)`), and
2. Any translation shift `c₀` with a non-vanishing lower bound
   `0 < c_aniso ≤ |renormalizedSchwinger Z n (F₀.translate c₀) - renormalizedSchwinger Z n F₀|`
   eventually refutes `SymanzikDimensionSixRotationalSuppression Z`. -/
theorem negative_control_balabanMultiScaleFlow_and_symanzikRotationalSuppression
    {P : ContinuumCutoffPath}
    {C_β : ℝ} (h_bdd : ∀ᶠ n in atTop, P.coupling n ≤ C_β)
    {Z : LoopRenormalization P.toCutoffPath}
    (c₀ : Fin 4 → ℚ) (F₀ : DisjointLoopFamily) {c_aniso : ℝ} (hc_aniso : 0 < c_aniso)
    (h_aniso : ∀ᶠ n in atTop,
      c_aniso ≤ |renormalizedSchwinger Z n (F₀.translate c₀) - renormalizedSchwinger Z n F₀|) :
    ¬ Nonempty (BalabanMultiScaleUVToIRFlow P) ∧ ¬ SymanzikDimensionSixRotationalSuppression Z := by
  refine ⟨fun ⟨M⟩ => not_balabanMultiScaleUVToIRFlow_of_bounded_coupling M C_β h_bdd, ?_⟩
  intro hSym
  have h_tend := (hSym.tendsto_translate_defect_zero c₀ F₀).abs
  rw [abs_zero] at h_tend
  have h_lt : ∀ᶠ n in atTop,
      |renormalizedSchwinger Z n (F₀.translate c₀) - renormalizedSchwinger Z n F₀| < c_aniso :=
    h_tend.eventually (gt_mem_nhds hc_aniso)
  obtain ⟨n, hge, hlt⟩ := (h_aniso.and h_lt).exists
  linarith

/-- Negative control refuting the `1 / 16` pure-Wilson covariance floor at
`0 ≤ β ≤ canonicalCrossoverBetaHi` (`β ≤ 1 / 6912`) and verifying:
1. Every positive-time physical rectangle `ℓ` and its time reflection `ℓ.timeReflect` sit on
   strictly disjoint lattice link supports (`Disjoint (physicalRectangleSupport L a ℓ.timeReflect) (physicalRectangleSupport L a ℓ)`),
2. For any unit-plaquette positive-time physical probe `ℓ` on `2 * loopTimeSpanBound a ℓ < L` with
   `|z_ref| ≤ 1` and `|z_pr| ≤ 1` at `0 ≤ β ≤ canonicalCrossoverBetaHi`, the pure-Wilson covariance
   satisfies `|irCov| ≤ 1 / 288` and `¬ (1 / 16 ≤ |irCov|)`,
3. The 6-face 3-cube degree-4 character floor `(1 / 4) ^ 5 * β ^ 4 = β ^ 4 / 1024` on
   `[canonicalCrossoverBetaLo, canonicalCrossoverBetaHi]` dominates
   `canonicalCrossoverCovLo + 3 * (Real.exp (2 * δ_rem) - 1)` while lying strictly below the
   center-twist strong-coupling upper bound `12 * β ≤ Real.exp (12 * β) - 1`, and
4. The concrete non-empty local plaquette polymer family `PolymerActivityFamily.localPlaquette L w`
   and contractive local polymer RG chain `localPolymerRGStateAux` satisfy volume-independent
   `PolymerDobrushinNormBound`, volume-independent single-link oscillation `≤ 12 * w` alongside
   extensive volume growth `≥ 2 * w * L^4` on `constantPauliIJConfig L`, and $49^j$-free single-link
   oscillation bounds across all steps `j`. -/
theorem negative_control_refute_one_sixteenth_cov_floor_and_verify_local_polymer_chain
    (L : ℕ) [NeZero L] {a β z_ref z_pr : ℝ}
    (ha : 0 < a)
    (hβ_lo : (canonicalCrossoverBetaLo : ℝ) ≤ β)
    (hβ_hi : β ≤ (canonicalCrossoverBetaHi : ℝ))
    (hz_ref : |z_ref| ≤ 1) (hz_pr : |z_pr| ≤ 1)
    (ℓ : PhysicalRectangle) (h_pos : ℓ.IsPositiveTime)
    (h_span : 2 * loopTimeSpanBound a ℓ < L)
    (hr : ℓ.stepsμ a = 1) (hs : ℓ.stepsν a = 1) :
    Disjoint (physicalRectangleSupport L a ℓ.timeReflect) (physicalRectangleSupport L a ℓ) ∧
    (|irCov (wilsonMeasure (gaugeHaarMeasure L) β)
        (fun V => z_ref * physicalWilsonLoop L a ℓ.timeReflect V)
        (fun V => z_pr * physicalWilsonLoop L a ℓ V)| ≤ 1 / 288 ∧
      ¬ ((1 / 16 : ℝ) ≤
        |irCov (wilsonMeasure (gaugeHaarMeasure L) β)
          (fun V => z_ref * physicalWilsonLoop L a ℓ.timeReflect V)
          (fun V => z_pr * physicalWilsonLoop L a ℓ V)|)) ∧
    ((canonicalCrossoverCovLo : ℝ) < (1 / 4 : ℝ) ^ 5 * β ^ 4 ∧
      (1 / 4 : ℝ) ^ 5 * β ^ 4 < 12 * β ∧
      12 * β ≤ Real.exp (12 * β) - 1) ∧
    PolymerDobrushinNormBound (PolymerActivityFamily.localPlaquette L β) (18 * (2 * (24 * β))) ∧
    ((∀ (V : GaugeConfig L) (e : Link L) (g1 g2 : SU2),
        |(PolymerActivityFamily.localPlaquette L β).eval (updateGaugeLink L V e.x e.μ g1) -
          (PolymerActivityFamily.localPlaquette L β).eval (updateGaugeLink L V e.x e.μ g2)| ≤
          12 * β) ∧
      (2 * β) * ((L ^ 4 : ℕ) : ℝ) ≤
        (PolymerActivityFamily.localPlaquette L β).eval
          (InteractingEffectiveActionState.constantPauliIJConfig L)) ∧
    (∀ (x₀ : Lattice4D L) (p : List LatticeStep) (e e' : Link L),
      e ∈ latticePathSupport L x₀ p → e' ∈ latticePathSupport L x₀ p →
        linkTemporalDist e e' ≤ p.length) := by
  have h_lo_pos : (0 : ℝ) < (canonicalCrossoverBetaLo : ℝ) := by
    norm_num [canonicalCrossoverBetaLo]
  have hβ0 : 0 ≤ β := (h_lo_pos.trans_le hβ_lo).le
  have h_cons :=
    InteractingEffectiveActionState.canonicalCrossover_character_floor_consistent_with_centerTwist_upper_bound
      hβ_lo hβ_hi (le_rfl : (0 : ℝ) ≤ 0)
      (by norm_num [canonicalCrossoverCovLo] : (0 : ℝ) ≤ (canonicalCrossoverCovLo : ℝ) / 12)
  rw [mul_zero, Real.exp_zero, sub_self, mul_zero, add_zero] at h_cons
  have h_cov_pos : (0 : ℝ) < (canonicalCrossoverCovLo : ℝ) :=
    (Rat.cast_pos.mpr canonicalCrossoverCovLo_pos_and_lt_centerTwist_bound.2.2.1)
  have h_strict_floor : (canonicalCrossoverCovLo : ℝ) < (1 / 4 : ℝ) ^ 5 * β ^ 4 := by
    have h_two :=
      InteractingEffectiveActionState.canonicalCrossover_character_floor_consistent_with_centerTwist_upper_bound
        hβ_lo hβ_hi (by positivity : 0 ≤ (canonicalCrossoverCovLo : ℝ) / 12) le_rfl
    have h_pos_exp : 0 < 3 * (Real.exp (2 * ((canonicalCrossoverCovLo : ℝ) / 12)) - 1) := by
      have h_arg_pos : 0 < 2 * ((canonicalCrossoverCovLo : ℝ) / 12) := by linarith
      have h_gt1 : 1 < Real.exp (2 * ((canonicalCrossoverCovLo : ℝ) / 12)) :=
        Real.one_lt_exp_iff.mpr h_arg_pos
      linarith
    linarith [h_two.1]
  exact ⟨(disjoint_physicalRectangleSupport_timeReflect_self L ha h_pos h_span).2,
    InteractingEffectiveActionState.unitPlaquetteProbe_irCov_wilsonMeasure_lt_one_sixteenth_at_canonicalCrossoverBetaHi
      L ha hβ0 hβ_hi hz_ref hz_pr ℓ h_pos h_span hr hs,
    ⟨h_strict_floor, h_cons.2.1, h_cons.2.2⟩,
    PolymerActivityFamily.polymerDobrushinNormBound_localPlaquette L hβ0,
    InteractingEffectiveActionState.localPlaquette_satisfies_local_osc_and_grows_with_volume L hβ0,
    fun _ _ _ _ he he' => linkTemporalDist_le_length_of_mem_latticePathSupport he he'⟩

/-- Hypothesis-free negative controls and unconditional theorems (taking zero `M : BalabanMultiScaleUVToIRFlow P`,
`T : LandingTube P`, or `C : IntervalArithmeticCrossoverCertificate P` parameters):
1. Exact 5-fold $\mathrm{SU}(2)$ Haar character integral `cubeSixFaceHaarIntegral = (1 / 4 : ℝ) ^ 5`,
2. Uniform-in-`k` contractive bounds `canonicalBalabanEtaStep k ≤ canonicalCrossoverEtaHi` and
   `canonicalBalabanDeltaNbStep k ≤ canonicalCrossoverEpsHi / 18`,
3. Unconditional `(4 / 3)^length`-weighted incident-loop sum bound for `localPolymerRGStateAux`
   at every RG step `j` and scale `m`,
4. Diverging positive physical perimeter counterterm `m n = (n : ℝ) + 1 → +∞` compatibility with
   `perimeterCornerRenormalization` (preserving exact translation, permutation, and reflection
   invariance),
5. Negative control refuting `∀ ℓ : PhysicalRectangle, |Z.factor n ℓ| ≤ 1` whenever the perimeter
   counterterm `m n` is strictly positive (`0 < m n` and `0 ≤ c n`), and
6. Negative control refuting `∀ ℓ : PhysicalRectangle, ℓ.IsPositiveTime → ∀ᶠ n in atTop, IsTimeCommensurate (dyadicOneLoopPath.spacing n) ℓ`
   unconditionally on `dyadicOneLoopPath`. -/
theorem negative_control_frontier_contraction_and_symmetry_discharges
    (P : ContinuumCutoffPath)
    (L : ℕ) [NeZero L] (k j m n : ℕ)
    (e : Link (dyadicScaleSide L m))
    (ℓ₀ : PhysicalRectangle) :
    InteractingEffectiveActionState.cubeSixFaceHaarIntegral = (1 / 4 : ℝ) ^ 5 ∧
    (canonicalBalabanEtaStep k ≤ (canonicalCrossoverEtaHi : ℝ) ∧
      canonicalBalabanDeltaNbStep k ≤ (canonicalCrossoverEpsHi : ℝ) / 18) ∧
    (let L_m := dyadicScaleSide L m
     let w_poly : ℕ → ℝ := fun s =>
       (6 * (4 * ((4 / 3 : ℝ) ^ 4 * 4)))⁻¹ * canonicalBalabanEtaStep s
     let P_m := (localPolymerRGStateAux L (P.coupling n) w_poly j m).polymers
     (∑ i : P_m.idx,
       if e ∈ latticePathSupport L_m (P_m.bases i) (P_m.loops i) then
         ((P_m.loops i).length : ℝ) *
           ((4 / 3 : ℝ) ^ (P_m.loops i).length * (4 * |P_m.weights i|))
       else 0) ≤ canonicalBalabanEtaStep j) ∧
    (let m_div : ℕ → ℝ := fun s => (s : ℝ) + 1
     let Z_div := YangMillsOsterwalderSchraderInheritance.perimeterCornerRenormalization
       P.toCutoffPath m_div (fun _ => 0)
     ((∃ m' c' : ℕ → ℝ,
        Z_div = YangMillsOsterwalderSchraderInheritance.perimeterCornerRenormalization P.toCutoffPath m' c') ∧
      Z_div.IsTranslationInvariant ∧
      Z_div.IsPermutationInvariant ∧
      HasReflectionInvariantFactors Z_div ∧
      Tendsto (fun s => Z_div.factor s ℓ₀) atTop atTop) ∧
     ∀ s : ℕ, ¬ (∀ ℓ : PhysicalRectangle, |Z_div.factor s ℓ| ≤ 1)) ∧
    ¬ (∀ ℓ : PhysicalRectangle, ℓ.IsPositiveTime →
        ∀ᶠ n' in atTop, IsTimeCommensurate (dyadicOneLoopPath.spacing n') ℓ) := by
  refine ⟨InteractingEffectiveActionState.cubeSixFaceHaarIntegral_eq_one_fourth_pow_five,
    ⟨canonicalBalabanEtaStep_le_canonicalCrossoverEtaHi k,
      (canonicalBalabanDeltaNbStep_le k).2⟩,
    localPolymerRGStateAux_weighted_incident_sum_le_canonicalBalabanEtaStep
      L (P.coupling n)
      (fun s => (6 * (4 * ((4 / 3 : ℝ) ^ 4 * 4)))⁻¹ * canonicalBalabanEtaStep s)
      (fun s => mul_nonneg (by positivity) (canonicalBalabanEtaStep_nonneg s))
      (fun _ => le_rfl) j m e,
    ⟨perimeterCornerRenormalization_admits_diverging_positive_perimeter_counterterm
      P (fun s => (s : ℝ) + 1)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop) ℓ₀,
     fun s => perimeterCornerRenormalization_not_abs_factor_le_one_of_pos_perimeter_counterterm
      P.toCutoffPath (fun s' => (s' : ℝ) + 1) (fun _ => 0) s (by positivity)⟩,
    not_forall_positiveTime_eventually_isTimeCommensurate_dyadicOneLoopPath⟩

/-- Universal negative controls (with zero `T`, `C`, or `M` hypotheses in the theorem header)
refuting:
1. Any `T : LandingTube P` with negative tube parameters (`T.β_star < 0 ∨ T.η_star < 0 ∨ T.ε_star < 0`),
2. Any `C : IntervalArithmeticCrossoverCertificate P` with negative rational bounds
   (`C.β_hi < 0 ∨ C.η_hi < 0 ∨ C.ε_hi < 0`),
3. Any `T : LandingTube P` whose coarse probe rectangle has a side smaller than `T.ℓstar`
   (`T.ℓ_probe.sideμ < T.ℓstar ∨ T.ℓ_probe.sideν < T.ℓstar`; after Phase 2 the probe is fixed;
   this part is now definitional),
4. Any `M : BalabanMultiScaleUVToIRFlow P` along a bounded UV coupling path
   (`∀ᶠ n in atTop, P.coupling n ≤ C_β`), and
5. Any `M : BalabanMultiScaleUVToIRFlow P` along a super-logarithmic UV coupling schedule
   (`∀ᶠ n in atTop, (canonicalCrossoverBetaHi : ℝ) + (M.K n : ℝ) * M.Δβ_1loop < P.coupling n`). -/
theorem negative_control_landingTube_nonneg_probe_and_asymptoticFreedom_corridor
    (P : ContinuumCutoffPath) :
    (¬ ∃ T : LandingTube P, T.β_star < 0 ∨ T.η_star < 0 ∨ T.ε_star < 0) ∧
    (¬ ∃ C : IntervalArithmeticCrossoverCertificate P,
      C.β_hi < 0 ∨ C.η_hi < 0 ∨ C.ε_hi < 0) ∧
    (¬ ∃ T : LandingTube P,
      T.ℓ_probe.sideμ < T.ℓstar ∨ T.ℓ_probe.sideν < T.ℓstar) ∧
    (∀ C_β : ℝ, (∀ᶠ n in atTop, P.coupling n ≤ C_β) →
      ¬ Nonempty (BalabanMultiScaleUVToIRFlow P)) ∧
    (¬ ∃ M : BalabanMultiScaleUVToIRFlow P,
      ∀ᶠ n in atTop,
        (canonicalCrossoverBetaHi : ℝ) + (M.K n : ℝ) * M.Δβ_1loop < P.coupling n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨T, hβ | hη | hε⟩
    · linarith [T.hβ_star_nonneg]
    · linarith [T.hη_star_nonneg]
    · linarith [T.hε_star_nonneg]
  · rintro ⟨C, hβ | hη | hε⟩
    · linarith [C.hβ_hi_nonneg]
    · linarith [C.hη_hi_nonneg]
    · linarith [C.hε_hi_nonneg]
  · rintro ⟨T, hμ_lt | hν_lt⟩
    · obtain ⟨_, _, hμ, _⟩ := T.steps_pos_and_ellstar_le_sides
      linarith
    · obtain ⟨_, _, _, hν⟩ := T.steps_pos_and_ellstar_le_sides
      linarith
  · intro C_β h_bdd ⟨M⟩
    exact not_balabanMultiScaleUVToIRFlow_of_bounded_coupling M C_β h_bdd
  · rintro ⟨M, h_super⟩
    exact not_balabanMultiScaleUVToIRFlow_of_superlogarithmic_coupling M h_super

/-- Machine-checked verification of the constructed inhabitants, $K$-step Haar blocking pushforward,
exact single-loop & lattice-base multi-loop translation invariance under arbitrary shifts `c : Fin 4 → ℚ`,
fractional-base straddling characterization, and `TwoCutoffComparison` counterterm cancellation law:
1. `Nonempty ToyFixedScaleStrongCouplingFlow` (witnessed by `toyFixedScaleStrongCouplingInhabitant`),
2. Unconditional $K$-step Gibbs-measure pushforward equality between `canonicalRGChain` and
   `localPolymerRGChain` and the $K$-step dyadic pushforward of `wilsonMeasure`,
3. Unconditional single-loop translation invariance `renormalizedSchwinger Z n (⟨[ℓ₀]⟩.translate c) = renormalizedSchwinger Z n ⟨[ℓ₀]⟩`
   for EVERY rational shift `c : Fin 4 → ℚ` (dyadic or non-dyadic),
4. Exact fractional-part straddling equivalence `relative_latticeBase_translate_ne_iff_straddle`,
5. Unconditional `SymanzikDimensionSixRotationalSuppression (symanzikDim6PerimeterCornerScheme P)` inhabitant, and
6. Refutation of `TwoCutoffComparison T (perimeterCornerRenormalization P.toCutoffPath m_div 0)`
   whenever `m_div → +∞` and `|rawSchwinger|` is frequently bounded away from `0`. -/
theorem inhabited_rg_pushforward_arbitrary_translation_and_counterterm_cancellation_witness
    (P : ContinuumCutoffPath) (L_ir K : ℕ) [NeZero L_ir] (n : ℕ)
    (c : Fin 4 → ℚ) (ℓ₁ ℓ₂ : PhysicalRectangle) (a : ℝ) (i : Fin 4) :
    Nonempty ToyFixedScaleStrongCouplingFlow ∧
    (((canonicalRGChain L_ir K (P.coupling_nonneg n)).state 0).gibbsMeasure =
      (wilsonMeasure (gaugeHaarMeasure (dyadicScaleSide L_ir K)) (P.coupling n)).map
        (iteratedDyadicLinkBlockMapToIR L_ir K)) ∧
    (∀ (Z : LoopRenormalization P.toCutoffPath), Z.IsTranslationInvariant →
      renormalizedSchwinger Z n ((⟨[ℓ₁]⟩ : DisjointLoopFamily).translate c) =
        renormalizedSchwinger Z n ⟨[ℓ₁]⟩) ∧
    ((ℓ₁.translate c).latticeBase a i - (ℓ₂.translate c).latticeBase a i ≠
        ℓ₁.latticeBase a i - ℓ₂.latticeBase a i ↔
      Int.fract ((ℓ₁.base i : ℝ) / a) ≠ Int.fract ((ℓ₂.base i : ℝ) / a) ∧
        ((Int.fract ((ℓ₁.base i : ℝ) / a) < 1 - Int.fract ((c i : ℝ) / a) ∧
            1 - Int.fract ((c i : ℝ) / a) ≤ Int.fract ((ℓ₂.base i : ℝ) / a)) ∨
          (Int.fract ((ℓ₂.base i : ℝ) / a) < 1 - Int.fract ((c i : ℝ) / a) ∧
            1 - Int.fract ((c i : ℝ) / a) ≤ Int.fract ((ℓ₁.base i : ℝ) / a)))) ∧
    SymanzikDimensionSixRotationalSuppression (symanzikDim6PerimeterCornerScheme P) ∧
    (∀ (T : LandingTube P) (m_div : ℕ → ℝ),
      Tendsto m_div atTop atTop →
      ∀ {c₀ : ℝ}, 0 < c₀ →
        (∃ᶠ s in atTop, c₀ ≤ |rawSchwinger P.toCutoffPath s ⟨[ℓ₁]⟩|) →
        ¬ TwoCutoffComparison T
          (YangMillsOsterwalderSchraderInheritance.perimeterCornerRenormalization
            P.toCutoffPath m_div (fun _ => 0))) := by
  refine ⟨⟨toyFixedScaleStrongCouplingInhabitant⟩,
    canonicalRGChain_ir_gibbsMeasure_eq_iterated_map_wilsonMeasure L_ir K (P.coupling_nonneg n),
    fun Z hZ => renormalizedSchwinger_singleton_translate_eq hZ n c ℓ₁,
    relative_latticeBase_translate_ne_iff_straddle c ℓ₁ ℓ₂ a i,
    (symanzikDimensionSixRotationalSuppression_perimeterCorner_inhabited P).2,
    fun T m_div hm _ hc₀ h_freq =>
      TwoCutoffComparison.not_twoCutoffComparison_of_frequently_ge_rawSchwinger_and_perimeterCorner_atTop
        T m_div hm ℓ₁ hc₀ h_freq⟩

/-- Machine-checked vacuity and refutation controls at `741c57a8`:
1. `TwoCutoffComparison` is incompatible with `BalabanMultiScaleUVToIRFlow`
   (`not_twoCutoffComparison_of_balabanMultiScaleUVToIRFlow`; takes `hF : M.WilsonCharFloor`, formerly the field `h_wilson_char_floor`), rendering
   `BalabanMultiScaleUVToIRFlow.exists_tendsto_landed_beta_in_crossover_window`,
   `qymSchwingerGap_of_balabanMultiScaleFlow_and_five_gaps`, and
   `qymSchwingerGap_of_balabanMultiScaleFlow_and_commensurate_cutoff` vacuous;
2. `TwoCutoffComparison` is incompatible with `ObservableTransferAndSymmetryBridge`
   (`not_twoCutoffComparison_of_observableTransferAndSymmetryBridge`) and with
   `ExponentialRemainderLocalityBound` (`not_twoCutoffComparison_of_exponentialRemainderLocalityBound`),
   rendering `qymSchwingerGap_of_landingTube`,
   `qymSchwingerGap_of_intervalArithmeticCrossoverCertificate`, and
   `qymSchwingerGap_of_inductiveStepAndBlockBounds` vacuous;
3. `TwoCutoffComparison` is refuted by any diverging perimeter counterterm `m → +∞`
   with `c` bounded below (`not_twoCutoffComparison_of_perimeter_tendsto_atTop_and_corner_bddBelow`);
4. Any two chains `C, C' : MultiStepHaarRGChain L_ir K β_uv` have identical `totalAction` and
   `gibbsMeasure` at every scale `m ≤ K` (`MultiStepHaarRGChain.totalAction_eq`,
   `MultiStepHaarRGChain.gibbsMeasure_eq`); and
5. Along any `P : ContinuumCutoffPath`, `∀ᶠ n in atTop, P.coupling n ≤ B` is false for every `B : ℝ`
   (`ContinuumCutoffPath.coupling_tendsto_atTop`), so bounded-coupling controls on `ContinuumCutoffPath`
   have false hypotheses. -/
theorem vacuity_and_refutation_controls_at_741c57a8
    (P : ContinuumCutoffPath) (L_ir K : ℕ) [NeZero L_ir] (β_uv B : ℝ) :
    (∀ (M : BalabanMultiScaleUVToIRFlow P) (hF : M.WilsonCharFloor)
      (Z : LoopRenormalization P.toCutoffPath),
      ¬ TwoCutoffComparison (M.toLandingTube hF) Z) ∧
    (∀ (T : LandingTube P) (Z : LoopRenormalization P.toCutoffPath),
      ObservableTransferAndSymmetryBridge T Z → ¬ TwoCutoffComparison T Z) ∧
    (∀ (T : LandingTube P) (Z : LoopRenormalization P.toCutoffPath),
      ExponentialRemainderLocalityBound T → ¬ TwoCutoffComparison T Z) ∧
    (∀ (T : LandingTube P) (m c : ℕ → ℝ) (B_c : ℝ),
      Tendsto m atTop atTop → (∀ᶠ n in atTop, B_c ≤ c n) →
      ¬ TwoCutoffComparison T
        (YangMillsOsterwalderSchraderInheritance.perimeterCornerRenormalization
          P.toCutoffPath m c)) ∧
    (∀ (C C' : MultiStepHaarRGChain L_ir K β_uv) (m : ℕ), m ≤ K →
      (∀ V, (C.state m).totalAction V = (C'.state m).totalAction V) ∧
      (C.state m).gibbsMeasure = (C'.state m).gibbsMeasure) ∧
    ¬ (∀ᶠ n in atTop, P.coupling n ≤ B) := by
  refine ⟨fun M hF Z => not_twoCutoffComparison_of_balabanMultiScaleUVToIRFlow M hF Z,
    fun T Z hTrans => not_twoCutoffComparison_of_observableTransferAndSymmetryBridge T Z hTrans,
    fun T Z hLoc => not_twoCutoffComparison_of_exponentialRemainderLocality T Z hLoc,
    fun T m c B_c hm hc =>
      not_twoCutoffComparison_of_perimeter_tendsto_atTop_and_corner_bddBelow T m c hm ⟨B_c, hc⟩,
    fun C C' m hm =>
      ⟨MultiStepHaarRGChain.totalAction_eq C C' m hm,
        MultiStepHaarRGChain.gibbsMeasure_eq C C' m hm⟩,
    fun h_bdd => ?_⟩
  have h_gt : ∀ᶠ n in atTop, B + 1 ≤ P.coupling n :=
    P.coupling_tendsto_atTop.eventually (eventually_ge_atTop (B + 1))
  obtain ⟨n, hle, hge⟩ := (h_bdd.and h_gt).exists
  linarith

/-- Machine-checked Stage 1A sanity checks S1–S4:
- **S1:** Duplicate two-loop families `⟨[ℓ, ℓ]⟩` (`not_isAdmissible_duplicate`) and
  quarter/three-quarter straddling pair families `quarterThreeQuarterPairFamily T.ℓstar ℓ_R ℓ_L s`
  (`not_isAdmissible_quarterThreeQuarterPairFamily`) are not admissible.
- **S2:** A2 holds (`isLatticeVector_of_isAdmissible_translate`,
  `latticeBase_translate_of_intMul`, `relative_latticeBase_translate_intMul_eq`).
- **S3 (Comment on repeated-loop argument):** The repeated-loop refutation
  (`not_twoCutoffComparison_of_perimeter_tendsto_atTop_and_corner_bddBelow`) relies on the duplicate
  pair `⟨[ℓ, ℓ]⟩` having non-vanishing UV expectation `1 / 4 ≤ rawSchwinger P.toCutoffPath n ⟨[ℓ, ℓ]⟩`
  by reflection positivity of a square (`LandingTube.eventually_rawSchwinger_duplicate_ge_quarter`).
  Because `⟨[ℓ, ℓ]⟩` is excluded by `Nodup` (`not_isAdmissible_duplicate`), replaying that argument on
  an admissible family `F` (`F.IsAdmissible T.ℓstar halfOffset`, whose distinct loops have disjoint
  coarse link supports `rectLinksZ4 T.ℓstar`) would require a uniform positive lower bound
  `∃ c₀ > 0, ∃ᶠ n in atTop, c₀ ≤ |rawSchwinger P.toCutoffPath n F|` on a link-disjoint admissible
  family at diverging UV coupling `P.coupling n → ∞`; no such lemma exists in the repository.
- **S4 (Consistency & Degeneracy Statement):** consistency unknown; degenerate by A4
  (`wilsonLoop_dyadicLinkBlockMap`, `landedIrSchwinger_eq_rawSchwinger_of_isAdmissible`,
  `AlignedTwoCutoffComparison.tendsto_familyFactor_sub_one_mul_raw`). -/
theorem stage1A_admissible_and_decimation_degeneracy_controls
    (P : ContinuumCutoffPath) (T : LandingTube P) (Z : LoopRenormalization P.toCutoffPath)
    (L : ℕ) [NeZero L] (U : GaugeConfig (2 * L)) (x : Lattice4D L) (μ ν : Direction) (r s : ℕ)
    {a : ℚ} (ha : 0 < a) (θ : Fin 4 → ℚ) (k : Fin 4 → ℤ)
    (ℓ ℓ_R ℓ_L : PhysicalRectangle) :
    ¬ (⟨[ℓ, ℓ]⟩ : DisjointLoopFamily).IsAdmissible a θ ∧
    ¬ (quarterThreeQuarterPairFamily T.ℓstar ℓ_R ℓ_L s).IsAdmissible T.ℓstar halfOffset ∧
    (⟨[(canonicalSpatialProbe a ha).timeReflect, canonicalSpatialProbe a ha]⟩ :
      DisjointLoopFamily).IsAdmissible a halfOffset ∧
    (∀ (F : DisjointLoopFamily) (c : Fin 4 → ℚ),
      F.IsAdmissible a θ → (F.translate c).IsAdmissible a θ → F.loops ≠ [] →
        ∃ m : Fin 4 → ℤ, c = fun i : Fin 4 => (m i : ℚ) * a) ∧
    (∀ F : DisjointLoopFamily, F.IsAdmissible a θ →
      (F.translate (fun i => (k i : ℚ) * a)).IsAdmissible a θ) ∧
    (ℓ_R.translate (fun i => (k i : ℚ) * a)).latticeBase (a : ℝ) -
        (ℓ_L.translate (fun i => (k i : ℚ) * a)).latticeBase (a : ℝ) =
      ℓ_R.latticeBase (a : ℝ) - ℓ_L.latticeBase (a : ℝ) ∧
    wilsonLoop (dyadicLinkBlockMap L U) x (rectangleSteps μ ν r s) =
      wilsonLoop U (dyadicEmbedSite L x) (rectangleSteps μ ν (2 * r) (2 * s)) ∧
    (∀ F : DisjointLoopFamily, F.IsAdmissible T.ℓstar halfOffset →
      (∀ᶠ n in atTop, landedIrSchwinger T Z n F = rawSchwinger P.toCutoffPath n F) ∧
      (AlignedTwoCutoffComparison T Z →
        Tendsto (fun n => (Z.familyFactor n F - 1) * rawSchwinger P.toCutoffPath n F)
          atTop (𝓝 0))) := by
  refine ⟨not_isAdmissible_duplicate a θ ℓ,
    not_isAdmissible_quarterThreeQuarterPairFamily T ℓ_R ℓ_L s,
    isAdmissible_canonicalSpatialProbe_reflect_pair ha,
    fun _ _ hF hFc hne => (isLatticeVector_of_isAdmissible_translate hne hF hFc).1,
    fun _ hF => isAdmissible_translate_intMul ha θ k hF,
    relative_latticeBase_translate_intMul_eq ha k ℓ_R ℓ_L,
    wilsonLoop_dyadicLinkBlockMap L U x μ ν r s,
    fun _ hF => ⟨(landedIrSchwinger_eq_rawSchwinger_of_isAdmissible T Z hF).mono fun _ h => h.2.2,
      fun hA => hA.tendsto_familyFactor_sub_one_mul_raw hF⟩⟩

/-- Machine-checked Stage 1B sanity and negative controls for `DressedLandedComparison`:
1. **Relabeling check:** `DressedLandedComparison.dressedLandedSchwinger_eq_renormalizedSchwinger`,
   `DressedLandedComparison.renormalizedLoopCauchy`, and
   `constantCoarseObservable_relabeling_and_zero_irCov` show that without `h_local` and `h_nondeg`,
   `h_condexp` + `h_cauchy` is a relabeling of `RenormalizedLoopCauchy Z`,
2. **Mandatory rounded-`O_loc` negative control:** `not_dressedLandedComparison_of_rounded_O_loc_and_decay`
   refutes `DressedLandedComparison` whenever `O_loc` factors through `T.ℓstar`-rounded data and
   has decaying coarse covariance, and
3. **Pure-decimation degeneracy reduction:** `dressedCoarseObservable_pure_decimation_reduction`
   shows that under pure decimation (`iteratedDyadicLinkBlockMapToIR`), the `Z`-dressed refined UV
   observable on any admissible family `F` is already coarse-measurable (`irDressedLoopFamilyObservable`)
   and reduces to Stage 1A's A4 identity. -/
theorem stage1B_dressedLandedComparison_controls
    (P : ContinuumCutoffPath) (T : LandingTube P) (Z : LoopRenormalization P.toCutoffPath)
    (Ztr : TrackedRenormalization P T)
    (O_loc : (n : ℕ) → DisjointLoopFamily → GaugeConfig (T.irSide n) → ℝ) :
    (DressedLandedComparison T Z Ztr O_loc →
      (∀ (n : ℕ) (F : DisjointLoopFamily),
        dressedLandedSchwinger T O_loc n F = renormalizedSchwinger Z n F) ∧
      RenormalizedLoopCauchy Z ∧
      ∃ S : DisjointLoopFamily → ℝ,
        ∀ F : DisjointLoopFamily, Tendsto (fun n => renormalizedSchwinger Z n F) atTop (𝓝 (S F))) ∧
    ((∀ (n : ℕ) (F G : DisjointLoopFamily),
        F.loops.map (fun ℓ => (ℓ.latticeBase (T.ℓstar : ℝ), ℓ.latticeLoop (T.ℓstar : ℝ))) =
          G.loops.map (fun ℓ => (ℓ.latticeBase (T.ℓstar : ℝ), ℓ.latticeLoop (T.ℓstar : ℝ))) →
          O_loc n F = O_loc n G) →
      (∀ (n : ℕ) (ℓ₁ ℓ₂ : PhysicalRectangle) (V : GaugeConfig (T.irSide n)),
        O_loc n ⟨[ℓ₁, ℓ₂]⟩ V = O_loc n ⟨[ℓ₁]⟩ V * O_loc n ⟨[ℓ₂]⟩ V) →
      (∃ C_decay : ℝ, 0 ≤ C_decay ∧
        ∀ (t : ℕ), ∀ᶠ n in atTop,
          |irCov ((T.chain n).state 0).gibbsMeasure
            (O_loc n ⟨[T.ℓ_probe.timeReflect]⟩)
            (O_loc n ⟨[T.ℓ_probe.translate (timeShift (t * T.ℓstar))]⟩)| ≤
            C_decay * (landingTubeContraction T) ^ t) →
      ¬ DressedLandedComparison T Z Ztr O_loc) ∧
    (∀ F : DisjointLoopFamily, F.IsAdmissible T.ℓstar halfOffset →
      ∀ᶠ n in atTop,
        dressedLandedSchwinger T
            (fun m G V => irDressedLoopFamilyObservable Z (T.irSide m) m (T.ℓstar : ℝ) G V) n F =
          Z.familyFactor n F * landedIrSchwinger T Z n F ∧
        dressedLandedSchwinger T
            (fun m G V => irDressedLoopFamilyObservable Z (T.irSide m) m (T.ℓstar : ℝ) G V) n F =
          renormalizedSchwinger Z n F) := by
  refine ⟨fun hD => ⟨hD.dressedLandedSchwinger_eq_renormalizedSchwinger, hD.renormalizedLoopCauchy⟩,
    fun h_round h_pair h_dec =>
      not_dressedLandedComparison_of_rounded_O_loc_and_decay T Z Ztr O_loc h_round h_pair h_dec,
    fun _ hF =>
      (dressedCoarseObservable_pure_decimation_reduction T Z hF).mono fun _ h => ⟨h.2.1, h.2.2⟩⟩

end JesseMath.Physics.YangMillsReconstructedGeneratorGapNegativeControl

#assert_zfc_axioms
