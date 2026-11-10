import JesseMath.Physics.YangMillsRenormalizedObservableLimits
import JesseMath.Physics.YangMillsOsterwalderSchraderInheritance
import JesseMath.Linter.AxiomAudit

/-! Controls for `YangMillsRenormalizedObservableLimits`.

Negative controls, each on an explicit model built from the actual Wilson measure or the
actual gauge action:
1. Open lattice lines are not gauge invariant; the closedness hypothesis is necessary.
2. Tightness does not give convergence: along a cutoff path with oscillating coupling
   (fixed lattice side `2`, fixed spacing `1`), the joint Wilson-loop laws of the actual model
   have no limit, so `WilsonLoopConvergenceObligation` fails for it.
3. Unbounded multiplicative renormalization destroys tightness of the actual renormalized
   laws, so the tail obligation cannot be dropped.
4. Compactness alone does not produce gauge-invariant holonomy laws.
5. At a fixed cutoff the joint law is not invariant under a physical translation that is not
   a lattice vector, so the commensurability hypothesis of the proved translation invariance
   cannot be dropped at the lattice level.
6. Unrenormalized physical plaquette averages converge along every continuum cutoff path, but
   to a Dirac law under which any two coordinates are independent; the analogue of the
   `nontrivial` obligation is false for them.

The path in control 2 is not a continuum cutoff path. Whether convergence holds along an
asymptotically free continuum path is open and is not decided here. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace JesseMath.Physics.YangMillsRenormalizedObservableLimitsNegativeControl

open YangMillsContinuumCompactness YangMillsRenormalizedObservableLimits
  YangMillsOsterwalderSchraderInheritance

/-- The central element `-1` of SU(2). -/
def minusIdentity : SU2 where
  mat := -1
  unitary := by simp
  det_one := by norm_num [Matrix.det_fin_two]

theorem minusIdentity_ne_one : minusIdentity ≠ 1 := by
  intro h
  have hm := congrArg (fun U : SU2 => U.mat 0 0) h
  change (-1 : ℂ) = 1 at hm
  norm_num at hm

theorem halfTraceRe_one : halfTraceRe (1 : SU2) = 1 := by
  simp [halfTraceRe, SU2.trace_one]

theorem halfTraceRe_minusIdentity : halfTraceRe minusIdentity = -1 := by
  have h : SU2.trace minusIdentity = -2 := by
    change Matrix.trace (-1 : Matrix (Fin 2) (Fin 2) ℂ) = -2
    rw [Matrix.trace_neg, Matrix.trace_one, Fintype.card_fin]
    norm_num
  simp [halfTraceRe, h]

theorem shift_zero_ne_zero (μ : Direction) : shift (0 : Lattice4D 2) μ ≠ 0 := by
  intro h
  have hμ := congrFun h μ
  simp [shift, unitVec] at hμ

/-! ### 1. Open lines are not gauge invariant -/

/-- A single link: an open lattice line on the side-two torus. -/
def openLine : List LatticeStep := [⟨0, true⟩]

theorem openLine_not_closed : pathTarget (0 : Lattice4D 2) openLine ≠ 0 := by
  simpa [openLine, stepTarget, shift] using shift_zero_ne_zero 0

/-- The trace of an open line changes under the actual gauge action. -/
theorem openLine_not_gaugeInvariant :
    ¬ ∀ (g : GaugeTransformation 2) (U : GaugeConfig 2),
      wilsonLoop (gaugeTransform g U) 0 openLine = wilsonLoop U 0 openLine := by
  intro h
  have hg := h (fun x => if x = 0 then minusIdentity else 1) (vacuumConfig 2)
  have hs : shift (0 : Lattice4D 2) 0 ≠ 0 := shift_zero_ne_zero 0
  have hlhs : wilsonLoop (gaugeTransform (fun x => if x = 0 then minusIdentity else 1)
      (vacuumConfig 2)) 0 openLine = -1 := by
    simp only [wilsonLoop, openLine, pathHolonomy_cons, pathHolonomy_nil, stepHolonomy_forward,
      mul_one]
    change halfTraceRe ((if (0 : Lattice4D 2) = 0 then minusIdentity else 1) * 1 *
      (if shift (0 : Lattice4D 2) 0 = 0 then minusIdentity else 1)⁻¹) = -1
    simp [hs, halfTraceRe_minusIdentity]
  have hrhs : wilsonLoop (vacuumConfig 2) 0 openLine = 1 := by
    simp only [wilsonLoop, openLine, pathHolonomy_cons, pathHolonomy_nil, stepHolonomy_forward,
      mul_one]
    exact halfTraceRe_one
  rw [hlhs, hrhs] at hg
  norm_num at hg

/-- Positive control: the closed unit rectangle is invariant for every gauge transformation. -/
example (g : GaugeTransformation 2) (U : GaugeConfig 2) :
    wilsonLoop (gaugeTransform g U) 0 (rectangleSteps 0 1 1 1) =
      wilsonLoop U 0 (rectangleSteps 0 1 1 1) :=
  wilsonLoop_gaugeTransform g U (pathTarget_rectangleSteps _ _ _ _ _)

/-! ### Shared model: the unit physical loop on the side-two torus at spacing one -/

/-- The unit physical square at the origin in the `(0, 1)` plane. -/
def unitLoop : PhysicalRectangle where
  base := fun _ => 0
  μ := 0
  ν := 1
  plane := by decide
  sideμ := 1
  sideν := 1
  sideμ_pos := one_pos
  sideν_pos := one_pos

/-- The plaquette it becomes at spacing one. -/
def unitPlaquette : Plaquette 2 := ⟨0, 0, 1, by decide⟩

theorem unitLoop_steps : unitLoop.stepsμ 1 = 1 ∧ unitLoop.stepsν 1 = 1 := by
  simp [PhysicalRectangle.stepsμ, PhysicalRectangle.stepsν, unitLoop]

theorem unitLoop_site : latticeSite 2 (unitLoop.latticeBase 1) = 0 := by
  funext i
  simp [latticeSite, PhysicalRectangle.latticeBase, unitLoop]

theorem unitLoop_wilsonLoop (U : GaugeConfig 2) :
    physicalWilsonLoop 2 1 unitLoop U = 1 - plaquetteAction U unitPlaquette := by
  rw [physicalWilsonLoop_eq_one_sub_plaquetteAction 1 unitLoop U unitLoop_steps.1
    unitLoop_steps.2]
  congr 2
  change (⟨latticeSite 2 (unitLoop.latticeBase 1), 0, 1, _⟩ : Plaquette 2) = ⟨0, 0, 1, _⟩
  rw [unitLoop_site]

/-- A configuration with a single flipped link and unit plaquette action `2`. -/
def flippedConfig : GaugeConfig 2 := fun e => if e = ⟨0, 0⟩ then minusIdentity else 1

theorem flippedConfig_plaquetteAction : plaquetteAction flippedConfig unitPlaquette = 2 := by
  have h1 : (⟨shift (0 : Lattice4D 2) 0, 1⟩ : Link 2) ≠ ⟨0, 0⟩ := by
    intro h
    have := congrArg Link.μ h
    exact absurd this (by decide)
  have h2 : (⟨shift (0 : Lattice4D 2) 1, 0⟩ : Link 2) ≠ ⟨0, 0⟩ := by
    intro h
    exact shift_zero_ne_zero 1 (congrArg Link.x h)
  have h3 : (⟨0, 1⟩ : Link 2) ≠ ⟨0, 0⟩ := by
    intro h
    have := congrArg Link.μ h
    exact absurd this (by decide)
  have hhol : plaquetteHolonomy flippedConfig unitPlaquette = minusIdentity := by
    change flippedConfig ⟨0, 0⟩ * flippedConfig ⟨shift 0 0, 1⟩ *
      (flippedConfig ⟨shift 0 1, 0⟩)⁻¹ * (flippedConfig ⟨0, 1⟩)⁻¹ = minusIdentity
    simp [flippedConfig, h1, h2, h3]
  have ht := halfTraceRe_minusIdentity
  unfold halfTraceRe at ht
  rw [plaquetteAction, hhol]
  linarith

/-- At zero coupling the actual Wilson law is product Haar measure. -/
theorem wilsonMeasure_zero (L : ℕ) [NeZero L] :
    wilsonMeasure (gaugeHaarMeasure L) 0 = gaugeHaarMeasure L := by
  have hw : ∀ U : GaugeConfig L, boltzmannWeight 0 U = 1 := by
    intro U
    simp [boltzmannWeight, wilsonAction]
  have hZ : wilsonPartition (gaugeHaarMeasure L) 0 = 1 := by
    simp [wilsonPartition, hw]
  rw [wilsonMeasure]
  simp only [hw, hZ, div_one, ENNReal.ofReal_one]
  exact withDensity_one

/-- The mean unit plaquette action under the actual Wilson law at coupling `β`. -/
def meanPlaquette (β : ℝ) : ℝ :=
  ∫ U, plaquetteAction U unitPlaquette ∂wilsonMeasure (gaugeHaarMeasure 2) β

/-- At zero coupling the mean plaquette action is strictly positive. -/
theorem meanPlaquette_zero_pos : 0 < meanPlaquette 0 := by
  rw [meanPlaquette, wilsonMeasure_zero]
  exact (continuous_plaquetteAction unitPlaquette).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun U => plaquetteAction_nonneg U unitPlaquette)
    (x := flippedConfig) (by rw [flippedConfig_plaquetteAction]; norm_num)

/-- The joint-law expectation of a clamp of the unit loop is `1 - meanPlaquette β`. -/
def clampUnitLoop : WilsonLoopSpace →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun w => max (-1) (min 1 (w unitLoop)), by fun_prop⟩ 2 (by
      intro x y
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have hx1 : -1 ≤ max (-1) (min 1 (x unitLoop)) := le_max_left _ _
      have hx2 : max (-1) (min 1 (x unitLoop)) ≤ 1 :=
        max_le (by norm_num) (min_le_left _ _)
      have hy1 : -1 ≤ max (-1) (min 1 (y unitLoop)) := le_max_left _ _
      have hy2 : max (-1) (min 1 (y unitLoop)) ≤ 1 :=
        max_le (by norm_num) (min_le_left _ _)
      rw [abs_le]
      constructor <;> linarith)

theorem clampUnitLoop_wilsonLoopVector (U : GaugeConfig 2) :
    clampUnitLoop (wilsonLoopVector 2 1 U) = 1 - plaquetteAction U unitPlaquette := by
  have hW := halfTraceRe_mem_Icc (pathHolonomy U (latticeSite 2 (unitLoop.latticeBase 1))
    (unitLoop.latticeLoop 1))
  change max (-1) (min 1 (physicalWilsonLoop 2 1 unitLoop U)) = _
  have hW' : physicalWilsonLoop 2 1 unitLoop U ∈ Set.Icc (-1 : ℝ) 1 := hW
  rw [min_eq_right hW'.2, max_eq_right hW'.1, unitLoop_wilsonLoop]

theorem expectation_clampUnitLoop {β : ℝ} (hβ : 0 ≤ β) :
    wilsonExpectation (gaugeHaarMeasure 2) β (fun U => clampUnitLoop (wilsonLoopVector 2 1 U)) =
      1 - meanPlaquette β := by
  have := wilsonMeasure_isProbabilityMeasure (gaugeHaarMeasure 2) hβ (measurable_wilsonAction β)
  simp only [clampUnitLoop_wilsonLoopVector]
  rw [← integral_wilsonMeasure (gaugeHaarMeasure 2) hβ (measurable_wilsonAction β),
    integral_sub (integrable_const 1)
      ((continuous_plaquetteAction unitPlaquette).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)),
    integral_const, smul_eq_mul, mul_one, probReal_univ, meanPlaquette]

/-! ### 2. Tightness does not give convergence -/

/-- Actual Wilson laws on the side-two torus at spacing one, with coupling `n` at even `n`
and `0` at odd `n`. -/
def oscillatingPath : CutoffPath where
  side _ := 2
  side_pos _ := by norm_num
  spacing _ := 1
  spacing_pos _ := one_pos
  coupling n := if Even n then (n : ℝ) else 0
  coupling_nonneg n := by
    split_ifs
    · exact Nat.cast_nonneg n
    · exact le_rfl

/-- Along the oscillating path the joint Wilson-loop laws do not converge. -/
theorem oscillatingPath_not_converges :
    ¬ ∃ ν, Tendsto oscillatingPath.wilsonLoopLaw atTop (𝓝 ν) := by
  rintro ⟨ν, hν⟩
  have hF := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν) clampUnitLoop
  simp only [CutoffPath.integral_wilsonLoopLaw] at hF
  have hE : ∀ n, wilsonExpectation (gaugeHaarMeasure (oscillatingPath.side n))
      (oscillatingPath.coupling n)
      (fun U => clampUnitLoop (wilsonLoopVector (oscillatingPath.side n)
        (oscillatingPath.spacing n) U)) = 1 - meanPlaquette (oscillatingPath.coupling n) :=
    fun n => expectation_clampUnitLoop (oscillatingPath.coupling_nonneg n)
  simp only [hE] at hF
  have hevenMono : StrictMono (fun k : ℕ => 2 * k) := fun a b h => by dsimp only; omega
  have hoddMono : StrictMono (fun k : ℕ => 2 * k + 1) := fun a b h => by dsimp only; omega
  have heven := hF.comp hevenMono.tendsto_atTop
  have hodd := hF.comp hoddMono.tendsto_atTop
  have hcoupEven : ∀ k : ℕ, oscillatingPath.coupling (2 * k) = ((2 * k : ℕ) : ℝ) := by
    intro k
    simp [oscillatingPath]
  have hcoupOdd : ∀ k : ℕ, oscillatingPath.coupling (2 * k + 1) = 0 := by
    intro k
    simp [oscillatingPath]
  have hβtop : Tendsto (fun k : ℕ => ((2 * k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hevenMono.tendsto_atTop
  have hmean : Tendsto (fun k : ℕ => 1 - meanPlaquette (((2 * k : ℕ) : ℝ))) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub ((haarWilsonMeanPlaquette_tendsto (L := 2) unitPlaquette).comp hβtop)
  have h1 : Tendsto (fun k : ℕ => 1 - meanPlaquette (oscillatingPath.coupling (2 * k))) atTop
      (𝓝 (1 - 0)) := by
    simpa only [hcoupEven] using hmean
  have h2 : Tendsto (fun k : ℕ => 1 - meanPlaquette (oscillatingPath.coupling (2 * k + 1)))
      atTop (𝓝 (1 - meanPlaquette 0)) := by
    simp only [hcoupOdd]
    exact tendsto_const_nhds
  have e1 := tendsto_nhds_unique heven h1
  have e2 := tendsto_nhds_unique hodd h2
  have hpos := meanPlaquette_zero_pos
  rw [e1] at e2
  linarith

/-- The false strengthening "tightness of the joint laws implies their convergence along
every cutoff path" is refuted on the actual model. -/
theorem convergence_obligation_not_automatic :
    ¬ ∀ P : CutoffPath, WilsonLoopConvergenceObligation P := by
  intro h
  exact oscillatingPath_not_converges ((wilsonLoopLaw_converges_iff oscillatingPath).mp
    (h oscillatingPath))

/-- Positive control: the same path still has subsequential limits. -/
example : ∃ (φ : ℕ → ℕ) (μ : ProbabilityMeasure BasedHolonomySpace), StrictMono φ ∧
    Tendsto (fun n => oscillatingPath.wilsonLoopLaw (φ n)) atTop (𝓝 (μ.map halfTraceVector)) := by
  obtain ⟨φ, μ, hφ, _, hW, _⟩ := oscillatingPath.exists_subsequential_limit
  exact ⟨φ, μ, hφ, hW⟩

/-! ### 3. Unbounded renormalization destroys tightness -/

/-- Actual Wilson laws at zero coupling on the side-two torus at spacing one. -/
def frozenPath : CutoffPath where
  side _ := 2
  side_pos _ := by norm_num
  spacing _ := 1
  spacing_pos _ := one_pos
  coupling _ := 0
  coupling_nonneg _ := le_rfl

/-- Renormalization constants `n + 1`, unbounded in the cutoff index. -/
def growingFactors : LoopRenormalization frozenPath where
  factor n _ := (n : ℝ) + 1
  factor_pos n _ := by positivity

/-- The actual Haar mass of configurations whose unit Wilson loop exceeds one half. -/
theorem haar_unitLoop_pos :
    0 < gaugeHaarMeasure 2 {U | (1 / 2 : ℝ) < physicalWilsonLoop 2 1 unitLoop U} := by
  have ho : IsOpen {U : GaugeConfig 2 | (1 / 2 : ℝ) < physicalWilsonLoop 2 1 unitLoop U} :=
    isOpen_lt continuous_const (continuous_physicalWilsonLoop 2 1 unitLoop)
  refine ho.measure_pos (gaugeHaarMeasure 2) ⟨vacuumConfig 2, ?_⟩
  simp only [Set.mem_ofPred_eq, unitLoop_wilsonLoop, plaquetteAction_vacuum]
  norm_num

theorem not_tailObligation_growingFactors : ¬ growingFactors.TailObligation := by
  intro hT
  set δ := gaugeHaarMeasure 2 {U | (1 / 2 : ℝ) < physicalWilsonLoop 2 1 unitLoop U}
  have hδpos : 0 < δ := haar_unitLoop_pos
  have hδtop : δ ≠ ∞ := measure_ne_top _ _
  obtain ⟨C, hC⟩ := hT unitLoop (δ / 2) (ENNReal.half_pos hδpos.ne')
  obtain ⟨n, hn⟩ := exists_nat_ge (2 * C)
  have hlaw := hC _ ⟨growingFactors.law n, ⟨n, rfl⟩, rfl⟩
  have hmeas : MeasurableSet {w : WilsonLoopSpace | C < |w unitLoop|} :=
    (isOpen_lt continuous_const (continuous_apply unitLoop).abs).measurableSet
  have hmv : Measurable (growingFactors.renormalizedVector n) :=
    ((growingFactors.continuous_rescale n).comp (continuous_wilsonLoopVector _ _)).measurable
  rw [LoopRenormalization.law_eq_map_renormalizedVector, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply hmv hmeas] at hlaw
  have hconfig : ((frozenPath.configLaw n : ProbabilityMeasure _) : Measure _) =
      gaugeHaarMeasure (frozenPath.side n) := by
    change wilsonMeasure (gaugeHaarMeasure 2) 0 = gaugeHaarMeasure 2
    exact wilsonMeasure_zero 2
  rw [hconfig] at hlaw
  have hδ' : gaugeHaarMeasure (frozenPath.side n) {U | (1 / 2 : ℝ) <
      physicalWilsonLoop (frozenPath.side n) (frozenPath.spacing n) unitLoop U} = δ := rfl
  have hsub : {U : GaugeConfig (frozenPath.side n) | (1 / 2 : ℝ) <
        physicalWilsonLoop (frozenPath.side n) (frozenPath.spacing n) unitLoop U} ⊆
      growingFactors.renormalizedVector n ⁻¹' {w | C < |w unitLoop|} := by
    intro U hU
    simp only [Set.mem_ofPred_eq] at hU
    change C < |((n : ℝ) + 1) *
      physicalWilsonLoop (frozenPath.side n) (frozenPath.spacing n) unitLoop U|
    have hpos : 0 < ((n : ℝ) + 1) *
        physicalWilsonLoop (frozenPath.side n) (frozenPath.spacing n) unitLoop U := by
      positivity
    rw [abs_of_pos hpos]
    nlinarith
  have hle := (measure_mono hsub).trans hlaw
  rw [hδ'] at hle
  have hhalf : δ / 2 < δ := ENNReal.half_lt_self hδpos.ne' hδtop
  exact absurd hle (not_le.mpr hhalf)

/-- Positive control: bounded constants do satisfy the tail obligation. -/
example : (LoopRenormalization.unrenormalized frozenPath).TailObligation :=
  LoopRenormalization.tailObligation_of_bounded _ fun _ => ⟨1, fun _ => le_rfl⟩

/-- The unit physical rectangle has dyadic side length `1 = 1 · 2⁻⁰`. -/
theorem unitLoop_isDyadicSide : IsDyadicSide unitLoop :=
  ⟨0, 1, one_pos, by simp [unitLoop]⟩

/-- Renormalization constants `n + 1` along the physical asymptotically free dyadic path
`dyadicOneLoopPath` (`L_n = 4^n`, `a_n = 2⁻ⁿ`, `β_n = (11/(3π²)) n log 2 → ∞`). -/
def dyadicGrowingFactors : LoopRenormalization dyadicOneLoopPath.toCutoffPath where
  factor n _ := (n : ℝ) + 1
  factor_pos n _ := by positivity

/-- Unbounded multiplicative renormalization fails `TailObligation` on the physical
asymptotically free path `dyadicOneLoopPath`, proved via the volume- and coupling-uniform
reflection-positivity lower bound `wilsonProbability_wilsonLoop_tail_ge_eighth`. -/
theorem not_tailObligation_dyadicGrowingFactors : ¬ dyadicGrowingFactors.TailObligation := by
  apply not_tailObligation_of_unbounded_of_loopNonconcentration dyadicGrowingFactors
    (loopNonconcentration_of_dyadic dyadicOneLoopPath dyadicOneLoopPath_isDyadic unitLoop_isDyadicSide)
  intro B
  obtain ⟨n, hn⟩ := exists_nat_ge B
  exact ⟨n, by change B < (n : ℝ) + 1; linarith⟩

/-- Multiplicative perimeter-renormalization factors `exp(c · |∂ℓ| / a_n)` along the
physical asymptotically free dyadic path `dyadicOneLoopPath`. -/
def perimeterScalingFactors (c : ℝ) : LoopRenormalization dyadicOneLoopPath.toCutoffPath where
  factor n ℓ := Real.exp (c * (2 * (ℓ.sideμ + ℓ.sideν)) / dyadicOneLoopPath.spacing n)
  factor_pos _ _ := Real.exp_pos _

/-- Along the physical asymptotically free path `dyadicOneLoopPath`, any positive
perimeter-renormalization constant `c > 0` makes the multiplicative factor
`Z_n(ℓ) = exp(c · |∂ℓ| / a_n)` diverge to `+∞`, destroying tightness of the renormalized
Wilson-loop laws on the actual model. -/
theorem not_tailObligation_perimeterScalingFactors {c : ℝ} (hc : 0 < c) :
    ¬ (perimeterScalingFactors c).TailObligation := by
  apply not_tailObligation_of_tendsto_atTop_of_dyadic dyadicOneLoopPath_isDyadic
    (perimeterScalingFactors c) unitLoop_isDyadicSide
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hmul : Tendsto (fun n : ℕ => c * 4 * (2 : ℝ) ^ n) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) hpow
  have hexp : Tendsto (fun n : ℕ => Real.exp (c * 4 * (2 : ℝ) ^ n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hmul
  refine hexp.congr fun n => ?_
  change Real.exp (c * 4 * (2 : ℝ) ^ n) =
    Real.exp (c * (2 * (unitLoop.sideμ + unitLoop.sideν)) / (1 / 2 : ℝ) ^ n)
  congr 1
  simp only [unitLoop, one_div, inv_pow, div_inv_eq_mul]
  ring

/-! ### 4. Compactness alone does not give gauge-invariant holonomy laws -/

/-- The diagonal element `diag(i, -i)`. -/
def diagI : SU2 where
  mat := !![Complex.I, 0; 0, -Complex.I]
  unitary := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  det_one := by
    rw [Matrix.det_fin_two_of]
    simp

/-- The rotation `[[0, 1], [-1, 0]]`. -/
def rotJ : SU2 where
  mat := !![0, 1; -1, 0]
  unitary := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  det_one := by
    rw [Matrix.det_fin_two_of]
    simp

theorem rotJ_conj_diagI_ne : rotJ * diagI * rotJ⁻¹ ≠ diagI := by
  intro h
  have hm := congrArg (fun U : SU2 => U.mat 0 0) h
  change (rotJ.mat * diagI.mat * Matrix.conjTranspose rotJ.mat) 0 0 = diagI.mat 0 0 at hm
  simp [rotJ, diagI, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] at hm
  have := congrArg Complex.im hm
  simp at this
  norm_num at this

/-- A probability law on the compact holonomy space concentrated at a non-central point. -/
def diracHolonomyLaw : ProbabilityMeasure BasedHolonomySpace := diracProba (fun _ => diagI)

theorem diracHolonomyLaw_not_gaugeInvariant : ¬ IsGaugeInvariantHolonomyLaw diracHolonomyLaw := by
  intro h
  have hm := congrArg ProbabilityMeasure.toMeasure (h rotJ)
  change (Measure.dirac (fun _ : PhysicalRectangle => diagI)).map (conjugateAll rotJ) =
    Measure.dirac (fun _ : PhysicalRectangle => diagI) at hm
  rw [Measure.map_dirac' (continuous_conjugateAll rotJ).measurable] at hm
  have hpt := injective_dirac hm
  have hℓ := congrFun hpt unitLoop
  exact rotJ_conj_diagI_ne hℓ

/-- Compactness and normalization alone do not force gauge invariance; the invariance of
every limit law comes from the actual Wilson law. -/
theorem compactness_does_not_imply_gauge_invariance :
    ¬ ∀ μ : ProbabilityMeasure BasedHolonomySpace, IsGaugeInvariantHolonomyLaw μ :=
  fun h => diracHolonomyLaw_not_gaugeInvariant (h diracHolonomyLaw)

/-- Positive control: every actual lattice law is gauge invariant. -/
example (P : CutoffPath) (n : ℕ) : IsGaugeInvariantHolonomyLaw (P.basedHolonomyLaw n) :=
  P.basedHolonomyLaw_isGaugeInvariant n

/-! ### 5. Translations that are not lattice vectors -/

/-- The unit square with corner `(1/2, 0, 0, 0)`; at spacing one it has the same lattice
corner as `unitLoop`. -/
def halfShiftedLoop : PhysicalRectangle where
  base := fun i => if i = 0 then 1 / 2 else 0
  μ := 0
  ν := 1
  plane := by decide
  sideμ := 1
  sideν := 1
  sideμ_pos := one_pos
  sideν_pos := one_pos

/-- Half a lattice spacing along direction `0`. -/
def halfStep : Fin 4 → ℚ := fun i => if i = 0 then 1 / 2 else 0

/-- The unit lattice vector along direction `0`, as an integer site. -/
def firstAxis : Fin 4 → ℤ := fun i => if i = 0 then 1 else 0

theorem halfShiftedLoop_latticeBase : halfShiftedLoop.latticeBase 1 = 0 := by
  funext i
  fin_cases i <;> norm_num [PhysicalRectangle.latticeBase, halfShiftedLoop, Int.floor_eq_zero_iff]

theorem unitLoop_latticeBase : unitLoop.latticeBase 1 = 0 := by
  funext i
  simp [PhysicalRectangle.latticeBase, unitLoop]

theorem translate_unitLoop_latticeBase : (unitLoop.translate halfStep).latticeBase 1 = 0 := by
  funext i
  fin_cases i <;> norm_num [PhysicalRectangle.latticeBase, PhysicalRectangle.translate, unitLoop,
    halfStep, Int.floor_eq_zero_iff]

theorem translate_halfShiftedLoop_latticeBase :
    (halfShiftedLoop.translate halfStep).latticeBase 1 = firstAxis := by
  funext i
  fin_cases i <;> norm_num [PhysicalRectangle.latticeBase, PhysicalRectangle.translate,
    halfShiftedLoop, halfStep, firstAxis]

/-- Two physical loops that discretize to the same lattice loop have equal Wilson loops. -/
theorem unitLoop_eq_halfShiftedLoop (U : GaugeConfig 2) :
    physicalWilsonLoop 2 1 unitLoop U = physicalWilsonLoop 2 1 halfShiftedLoop U := by
  unfold physicalWilsonLoop
  rw [unitLoop_latticeBase, halfShiftedLoop_latticeBase]
  rfl

/-- After the half-step translation they become distinct plaquettes, which the flipped
configuration separates. -/
theorem translated_loops_separated :
    physicalWilsonLoop 2 1 (unitLoop.translate halfStep) flippedConfig ≠
      physicalWilsonLoop 2 1 (halfShiftedLoop.translate halfStep) flippedConfig := by
  have hl1 : (unitLoop.translate halfStep).latticeLoop 1 = rectangleSteps 0 1 1 1 := by
    simp [PhysicalRectangle.latticeLoop, PhysicalRectangle.translate, PhysicalRectangle.stepsμ,
      PhysicalRectangle.stepsν, unitLoop]
  have hl2 : (halfShiftedLoop.translate halfStep).latticeLoop 1 = rectangleSteps 0 1 1 1 := by
    simp [PhysicalRectangle.latticeLoop, PhysicalRectangle.translate, PhysicalRectangle.stepsμ,
      PhysicalRectangle.stepsν, halfShiftedLoop]
  have hz : latticeSite 2 (0 : Fin 4 → ℤ) = 0 := by
    funext i
    simp [latticeSite]
  have h0 : physicalWilsonLoop 2 1 (unitLoop.translate halfStep) flippedConfig =
      1 - plaquetteAction flippedConfig unitPlaquette := by
    unfold physicalWilsonLoop
    rw [translate_unitLoop_latticeBase, hl1, hz]
    exact wilsonLoop_rectangleSteps_one_one flippedConfig unitPlaquette
  have hsite : latticeSite 2 firstAxis = shift (0 : Lattice4D 2) 0 := by
    funext i
    fin_cases i <;> simp [latticeSite, firstAxis, shift, unitVec]
  have hflat : plaquetteHolonomy flippedConfig ⟨shift (0 : Lattice4D 2) 0, 0, 1, by decide⟩ = 1 := by
    have e1 : (⟨shift (0 : Lattice4D 2) 0, 0⟩ : Link 2) ≠ ⟨0, 0⟩ := by
      intro h
      exact shift_zero_ne_zero 0 (congrArg Link.x h)
    have e2 : (⟨shift (shift (0 : Lattice4D 2) 0) 0, 1⟩ : Link 2) ≠ ⟨0, 0⟩ := by
      intro h
      have := congrArg Link.μ h
      exact absurd this (by decide)
    have e3 : (⟨shift (shift (0 : Lattice4D 2) 0) 1, 0⟩ : Link 2) ≠ ⟨0, 0⟩ := by
      intro h
      have hx := congrFun (congrArg Link.x h) 1
      simp [shift, unitVec] at hx
    have e4 : (⟨shift (0 : Lattice4D 2) 0, 1⟩ : Link 2) ≠ ⟨0, 0⟩ := by
      intro h
      have := congrArg Link.μ h
      exact absurd this (by decide)
    change flippedConfig ⟨shift 0 0, 0⟩ * flippedConfig ⟨shift (shift 0 0) 0, 1⟩ *
      (flippedConfig ⟨shift (shift 0 0) 1, 0⟩)⁻¹ * (flippedConfig ⟨shift 0 0, 1⟩)⁻¹ = 1
    simp [flippedConfig, e1, e2, e3, e4]
  have h1 : physicalWilsonLoop 2 1 (halfShiftedLoop.translate halfStep) flippedConfig = 1 := by
    unfold physicalWilsonLoop
    rw [translate_halfShiftedLoop_latticeBase, hsite, hl2]
    have := wilsonLoop_rectangleSteps_one_one flippedConfig
      ⟨shift (0 : Lattice4D 2) 0, 0, 1, by decide⟩
    rw [plaquetteAction_eq_one_sub_halfTraceRe, hflat, halfTraceRe_one] at this
    change wilsonLoop flippedConfig (shift 0 0) (rectangleSteps 0 1 1 1) = 1 - (1 - 1) at this
    linarith
  rw [h0, h1, flippedConfig_plaquetteAction]
  norm_num

/-- The false strengthening "every cutoff law is invariant under every rational translation"
is refuted on the actual zero-coupling law at spacing one. -/
theorem fixedCutoff_not_translation_invariant :
    ¬ ∀ (P : CutoffPath) (n : ℕ) (c : Fin 4 → ℚ),
      (P.wilsonLoopLaw n).map (translateObservables c) = P.wilsonLoopLaw n := by
  intro h
  have hinv := congrArg ProbabilityMeasure.toMeasure (h frozenPath 0 halfStep)
  set D : Set WilsonLoopSpace := {w | w unitLoop = w halfShiftedLoop} with hD
  have hDclosed : IsClosed D := isClosed_eq (continuous_apply _) (continuous_apply _)
  have hconfig : ((frozenPath.configLaw 0 : ProbabilityMeasure _) : Measure _) =
      gaugeHaarMeasure (frozenPath.side 0) := by
    change wilsonMeasure (gaugeHaarMeasure 2) 0 = gaugeHaarMeasure 2
    exact wilsonMeasure_zero 2
  have hmeasV := (continuous_wilsonLoopVector (frozenPath.side 0) (frozenPath.spacing 0)).measurable
  -- the untranslated law gives full mass to `D`
  have hfull : (frozenPath.wilsonLoopLaw 0 : Measure WilsonLoopSpace) Dᶜ = 0 := by
    rw [CutoffPath.wilsonLoopLaw, ProbabilityMeasure.toMeasure_map,
      Measure.map_apply hmeasV hDclosed.measurableSet.compl]
    have hempty : wilsonLoopVector (frozenPath.side 0) (frozenPath.spacing 0) ⁻¹' Dᶜ = ∅ := by
      ext U
      simp only [Set.mem_preimage, Set.mem_compl_iff, hD, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false, not_not]
      exact unitLoop_eq_halfShiftedLoop U
    rw [hempty, measure_empty]
  -- the translated law gives positive mass to the complement of `D`
  have hopen : IsOpen {U : GaugeConfig (frozenPath.side 0) |
      physicalWilsonLoop 2 1 (unitLoop.translate halfStep) U ≠
        physicalWilsonLoop 2 1 (halfShiftedLoop.translate halfStep) U} :=
    isOpen_ne_fun (continuous_physicalWilsonLoop 2 1 _) (continuous_physicalWilsonLoop 2 1 _)
  have hpos : 0 < gaugeHaarMeasure (frozenPath.side 0) {U : GaugeConfig (frozenPath.side 0) |
      physicalWilsonLoop 2 1 (unitLoop.translate halfStep) U ≠
        physicalWilsonLoop 2 1 (halfShiftedLoop.translate halfStep) U} :=
    hopen.measure_pos (gaugeHaarMeasure (frozenPath.side 0))
      ⟨flippedConfig, translated_loops_separated⟩
  have htrans : ((frozenPath.wilsonLoopLaw 0).map (translateObservables halfStep) :
      Measure WilsonLoopSpace) Dᶜ = gaugeHaarMeasure (frozenPath.side 0)
        {U : GaugeConfig (frozenPath.side 0) |
          physicalWilsonLoop 2 1 (unitLoop.translate halfStep) U ≠
            physicalWilsonLoop 2 1 (halfShiftedLoop.translate halfStep) U} := by
    rw [ProbabilityMeasure.toMeasure_map, CutoffPath.wilsonLoopLaw,
      ProbabilityMeasure.toMeasure_map,
      Measure.map_map (continuous_translateObservables halfStep).measurable hmeasV,
      Measure.map_apply ((continuous_translateObservables halfStep).measurable.comp hmeasV)
        hDclosed.measurableSet.compl, hconfig]
    rfl
  rw [hinv, hfull] at htrans
  exact absurd htrans.symm (ne_of_gt hpos)

/-- Positive control: lattice-vector translations are exact symmetries at every cutoff. -/
example (n : ℕ) (j : Fin 4 → ℤ) :
    (frozenPath.wilsonLoopLaw n).map (translateObservables (fun i => (j i : ℚ))) =
      frozenPath.wilsonLoopLaw n :=
  frozenPath.wilsonLoopLaw_translate n fun i => ⟨j i, by simp [frozenPath]⟩

/-- Positive control: coordinate permutations are exact symmetries at every cutoff. -/
example (P : CutoffPath) (n : ℕ) (σ : Equiv.Perm (Fin 4)) :
    (P.wilsonLoopLaw n).map (permuteObservables σ) = P.wilsonLoopLaw n :=
  P.wilsonLoopLaw_permute n σ

/-! ### 6. Convergence without nontriviality -/

/-- The collapsed limit makes every two coordinates independent. -/
theorem collapsed_limit_independent (R R' : PhysicalPlaquetteRegion) :
    ProbabilityTheory.IndepFun (fun w : PlaquetteAverageSpace => w R) (fun w => w R')
      ((diracProba (fun _ => (1 : ℝ)) : ProbabilityMeasure PlaquetteAverageSpace) :
        Measure PlaquetteAverageSpace) := by
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hs' : MeasurableSet ((fun w : PlaquetteAverageSpace => w R) ⁻¹' s) :=
    (continuous_apply R).measurable hs
  have ht' : MeasurableSet ((fun w : PlaquetteAverageSpace => w R') ⁻¹' t) :=
    (continuous_apply R').measurable ht
  change Measure.dirac _ _ = Measure.dirac _ _ * Measure.dirac _ _
  rw [Measure.dirac_apply' _ (hs'.inter ht'), Measure.dirac_apply' _ hs',
    Measure.dirac_apply' _ ht']
  by_cases h1 : (1 : ℝ) ∈ s <;> by_cases h2 : (1 : ℝ) ∈ t <;> simp [Set.indicator, h1, h2]

/-- Along every continuum cutoff path the unrenormalized plaquette averages converge for the
full sequence, yet their limit fails the nontriviality criterion: any two regions, however
separated, are independent. Convergence alone is not the missing input. -/
theorem plaquette_limit_converges_but_trivial (P : ContinuumCutoffPath) :
    Tendsto P.plaquetteAverageLaw atTop (𝓝 (diracProba (fun _ => (1 : ℝ)))) ∧
    ∀ R R' : PhysicalPlaquetteRegion,
      ProbabilityTheory.IndepFun (fun w : PlaquetteAverageSpace => w R) (fun w => w R')
        ((diracProba (fun _ => (1 : ℝ)) : ProbabilityMeasure PlaquetteAverageSpace) :
          Measure PlaquetteAverageSpace) :=
  ⟨P.plaquetteAverageLaw_tendsto, collapsed_limit_independent⟩

/-- Positive control: the explicit asymptotically free dyadic path is a continuum path. -/
example : Tendsto dyadicOneLoopPath.plaquetteAverageLaw atTop
    (𝓝 (diracProba (fun _ => (1 : ℝ)))) :=
  dyadicOneLoopPath.plaquetteAverageLaw_tendsto

#assert_zfc_axioms

end JesseMath.Physics.YangMillsRenormalizedObservableLimitsNegativeControl
