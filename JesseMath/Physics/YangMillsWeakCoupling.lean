import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.YangMillsHaar
import JesseMath.Physics.YangMillsWilsonMeasureBridge
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Weak-coupling concentration for the actual Haar Wilson law

A single SU(2) identity neighborhood gives an extensive product-Haar lower bound for the
partition function. Its entropy cost per site is independent of lattice size. This yields
action-density tail and mean concentration uniformly over every nonempty finite torus,
including arbitrarily varying volumes as the bare inverse coupling tends to infinity.
The neighborhood constant still depends on the positive density scale. No Gaussian rate,
conditional fiber oscillation, renormalization contraction, or continuum mass gap follows.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology

namespace JesseMath.Physics

variable {L : ℕ} [NeZero L]

instance gaugeHaarMeasure_isOpenPosMeasure (L : ℕ) [NeZero L] :
    IsOpenPosMeasure (gaugeHaarMeasure L) := by
  change IsOpenPosMeasure (Measure.pi (fun _ : Link L => SU2.haarProbability))
  infer_instance

/-- The actual product-Haar mass of the open action sublevel at fixed lattice size. -/
def haarVacuumSublevelMass (L : ℕ) [NeZero L] (δ : ℝ) : ℝ :=
  (gaugeHaarMeasure L).real {U | wilsonAction 1 U < δ}

theorem haarVacuumSublevelMass_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < haarVacuumSublevelMass L δ := by
  have ho : IsOpen {U : GaugeConfig L | wilsonAction 1 U < δ} :=
    isOpen_lt (continuous_wilsonAction 1) continuous_const
  have hn : ({U : GaugeConfig L | wilsonAction 1 U < δ} : Set _).Nonempty :=
    ⟨vacuumConfig L, by simpa only [mem_ofPred_eq, wilsonAction_vacuum] using hδ⟩
  exact ENNReal.toReal_pos (ne_of_gt (ho.measure_pos _ hn)) (measure_ne_top _ _)

theorem haarVacuumSublevelMass_le_one (δ : ℝ) : haarVacuumSublevelMass L δ ≤ 1 := by
  exact measureReal_le_one

/-- A positive vacuum neighborhood gives a denominator bound without an assumed prefactor. -/
theorem haarWilsonPartition_sublevel_lower {β δ : ℝ} (hβ : 0 ≤ β) :
    haarVacuumSublevelMass L δ * Real.exp (-(β * δ)) ≤
      wilsonPartition (gaugeHaarMeasure L) β := by
  have hs : MeasurableSet {U : GaugeConfig L | wilsonAction 1 U < δ} :=
    measurableSet_lt (measurable_wilsonAction 1) measurable_const
  have hi := wilsonWeight_integrable (gaugeHaarMeasure L) hβ (measurable_wilsonAction β)
  calc
    _ = ∫ _ in {U : GaugeConfig L | wilsonAction 1 U < δ},
        Real.exp (-(β * δ)) ∂gaugeHaarMeasure L := by
      simp [haarVacuumSublevelMass]
    _ ≤ ∫ U in {U : GaugeConfig L | wilsonAction 1 U < δ},
        boltzmannWeight β U ∂gaugeHaarMeasure L := by
      apply setIntegral_mono_on (integrable_const _) hi.integrableOn hs
      intro U hU
      apply Real.exp_le_exp.mpr
      rw [wilsonAction_eq_beta_mul_wilsonAction_one]
      exact neg_le_neg (mul_le_mul_of_nonneg_left hU.le hβ)
    _ ≤ _ := setIntegral_le_integral hi (Filter.Eventually.of_forall fun U =>
      (Real.exp_pos (-wilsonAction β U)).le)

/-- The real mass of a measurable event is its genuine normalized Boltzmann integral. -/
theorem haarWilsonMeasure_real_eq {β : ℝ} (hβ : 0 ≤ β)
    {A : Set (GaugeConfig L)} (hA : MeasurableSet A) :
    (wilsonMeasure (gaugeHaarMeasure L) β).real A =
      (∫ U in A, boltzmannWeight β U ∂gaugeHaarMeasure L) /
        wilsonPartition (gaugeHaarMeasure L) β := by
  rw [← integral_indicator_one hA,
    integral_wilsonMeasure (gaugeHaarMeasure L) hβ (measurable_wilsonAction β)]
  unfold wilsonExpectation
  congr 1
  rw [← integral_indicator hA]
  congr 1
  ext U
  by_cases hU : U ∈ A <;> simp [hU]

/-- Exponential action-tail suppression for the actual finite-volume Haar Wilson law. -/
theorem haarWilsonMeasure_action_tail {β δ ε : ℝ} (hβ : 0 ≤ β) (hδ : 0 < δ) :
    (wilsonMeasure (gaugeHaarMeasure L) β).real {U | ε ≤ wilsonAction 1 U} ≤
      Real.exp (-(β * (ε - δ))) / haarVacuumSublevelMass L δ := by
  have hA : MeasurableSet {U : GaugeConfig L | ε ≤ wilsonAction 1 U} :=
    measurableSet_le measurable_const (measurable_wilsonAction 1)
  have hi := wilsonWeight_integrable (gaugeHaarMeasure L) hβ (measurable_wilsonAction β)
  have hZ := wilsonPartition_pos (gaugeHaarMeasure L) hβ (measurable_wilsonAction β)
  have hc := haarVacuumSublevelMass_pos (L := L) hδ
  have hu : (∫ U in {U : GaugeConfig L | ε ≤ wilsonAction 1 U},
      boltzmannWeight β U ∂gaugeHaarMeasure L) ≤ Real.exp (-(β * ε)) := by
    calc
      _ ≤ ∫ _ in {U : GaugeConfig L | ε ≤ wilsonAction 1 U},
          Real.exp (-(β * ε)) ∂gaugeHaarMeasure L := by
        apply setIntegral_mono_on hi.integrableOn (integrable_const _) hA
        intro U hU
        apply Real.exp_le_exp.mpr
        rw [wilsonAction_eq_beta_mul_wilsonAction_one]
        exact neg_le_neg (mul_le_mul_of_nonneg_left hU hβ)
      _ ≤ Real.exp (-(β * ε)) := by
        simp only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
        exact mul_le_of_le_one_left (Real.exp_pos _).le measureReal_le_one
  rw [haarWilsonMeasure_real_eq hβ hA]
  calc
    _ ≤ Real.exp (-(β * ε)) / wilsonPartition (gaugeHaarMeasure L) β :=
      div_le_div_of_nonneg_right hu hZ.le
    _ ≤ Real.exp (-(β * ε)) /
        (haarVacuumSublevelMass L δ * Real.exp (-(β * δ))) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le
        (mul_pos hc (Real.exp_pos _)) (haarWilsonPartition_sublevel_lower hβ)
    _ = _ := by
      rw [mul_comm (haarVacuumSublevelMass L δ), div_mul_eq_div_div, ← Real.exp_sub]
      have he : -(β * ε) - -(β * δ) = -(β * (ε - δ)) := by ring
      rw [he]

/-- At each fixed lattice, the probability of any positive action threshold tends to zero.
This does not give a bound uniform in `L`, nor convergence to a specified gauge representative. -/
theorem haarWilsonMeasure_action_tail_tendsto {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun β : ℝ => (wilsonMeasure (gaugeHaarMeasure L) β).real
      {U | ε ≤ wilsonAction 1 U}) atTop (𝓝 0) := by
  have hexp : Tendsto (fun β : ℝ => Real.exp (-(β * (ε - ε / 2))) /
      haarVacuumSublevelMass L (ε / 2)) atTop (𝓝 0) := by
    have hm : Tendsto (fun β : ℝ => β * (ε - ε / 2)) atTop atTop :=
      tendsto_id.atTop_mul_const (by linarith)
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp hm).div_const
      (haarVacuumSublevelMass L (ε / 2))
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
    ((eventually_ge_atTop (0 : ℝ)).mono fun _ hβ =>
      haarWilsonMeasure_action_tail hβ (by linarith : 0 < ε / 2)) hexp

/-- The mean action is controlled by a small-action region plus its complementary tail.
The displayed factor `2 * card(Plaquette L)` records the finite-volume dependence. -/
theorem haarWilsonMeanAction_le {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 ≤ ε) :
    (∫ U, wilsonAction 1 U ∂wilsonMeasure (gaugeHaarMeasure L) β) ≤
      ε + (2 * (Fintype.card (Plaquette L) : ℝ)) *
        (wilsonMeasure (gaugeHaarMeasure L) β).real {U | ε ≤ wilsonAction 1 U} := by
  let μ := wilsonMeasure (gaugeHaarMeasure L) β
  have : IsProbabilityMeasure μ :=
    wilsonMeasure_isProbabilityMeasure (gaugeHaarMeasure L) hβ (measurable_wilsonAction β)
  have hA : MeasurableSet {U : GaugeConfig L | ε ≤ wilsonAction 1 U} :=
    measurableSet_le measurable_const (measurable_wilsonAction 1)
  have hi : Integrable (wilsonAction 1) μ := by
    apply wilsonObservable_integrable (gaugeHaarMeasure L) hβ (measurable_wilsonAction β)
      (measurable_wilsonAction 1)
    intro U
    rw [abs_of_nonneg (wilsonAction_nonneg (by norm_num) U)]
    simpa using wilsonAction_upper_bound (L := L) (β := 1) (by norm_num) U
  have hind : Integrable ({U : GaugeConfig L | ε ≤ wilsonAction 1 U}.indicator
      (fun _ => (1 : ℝ))) μ := (integrable_const 1).indicator hA
  calc
    _ ≤ ∫ U, ε + (2 * (Fintype.card (Plaquette L) : ℝ)) *
        {U : GaugeConfig L | ε ≤ wilsonAction 1 U}.indicator (fun _ => (1 : ℝ)) U ∂μ := by
      apply integral_mono hi ((integrable_const ε).add (hind.const_mul _))
      intro U
      change wilsonAction 1 U ≤ ε + (2 * (Fintype.card (Plaquette L) : ℝ)) *
        {U : GaugeConfig L | ε ≤ wilsonAction 1 U}.indicator (fun _ => (1 : ℝ)) U
      by_cases hU : ε ≤ wilsonAction 1 U
      · simp only [Set.indicator_of_mem (show U ∈ {U : GaugeConfig L | ε ≤ wilsonAction 1 U} from hU), mul_one]
        have hb := wilsonAction_upper_bound (L := L) (β := 1) (by norm_num) U
        linarith
      · simp only [Set.indicator_of_notMem (show U ∉ {U : GaugeConfig L | ε ≤ wilsonAction 1 U} from hU), mul_zero, add_zero]
        exact (lt_of_not_ge hU).le
    _ = _ := by
      rw [integral_add (integrable_const ε) (hind.const_mul _), integral_const_mul,
        integral_indicator_const 1 hA]
      simp [μ]

/-- The actual normalized mean Wilson action vanishes as coupling grows at fixed volume. -/
theorem haarWilsonMeanAction_tendsto :
    Tendsto (fun β : ℝ => ∫ U, wilsonAction 1 U
      ∂wilsonMeasure (gaugeHaarMeasure L) β) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun β =>
      lt_of_lt_of_le ha (integral_nonneg fun U => wilsonAction_nonneg (by norm_num) U)
  · intro b hb
    have ht := (haarWilsonMeasure_action_tail_tendsto (L := L)
      (show 0 < b / 2 by linarith)).const_mul (2 * (Fintype.card (Plaquette L) : ℝ))
    have hlim : Tendsto (fun β : ℝ => b / 2 + (2 * (Fintype.card (Plaquette L) : ℝ)) *
        (wilsonMeasure (gaugeHaarMeasure L) β).real {U | b / 2 ≤ wilsonAction 1 U})
        atTop (𝓝 (b / 2)) := by simpa using tendsto_const_nhds.add ht
    filter_upwards [eventually_ge_atTop (0 : ℝ),
      hlim.eventually_lt_const (show b / 2 < b by linarith)] with β hβ hlt
    exact lt_of_le_of_lt (haarWilsonMeanAction_le hβ (by linarith : 0 ≤ b / 2)) hlt

/-- A nonpositive strict sublevel is empty. In particular, positivity of a vacuum point
alone does not permit the preceding denominator argument at `δ = 0`. -/
theorem haarVacuumSublevelMass_eq_zero_of_nonpos {δ : ℝ} (hδ : δ ≤ 0) :
    haarVacuumSublevelMass L δ = 0 := by
  have hs : {U : GaugeConfig L | wilsonAction 1 U < δ} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro U hU
    have hn := wilsonAction_nonneg (L := L) (β := 1) (by norm_num) U
    exact (not_lt_of_ge (le_trans hδ hn)) hU
  simp [haarVacuumSublevelMass, hs]

/-- Quantitative mean-action bound with the actual torus factor `12 L⁴` displayed. -/
theorem haarWilsonMeanAction_exponential_bound {β δ ε : ℝ}
    (hβ : 0 ≤ β) (hδ : 0 < δ) (hε : 0 ≤ ε) :
    (∫ U, wilsonAction 1 U ∂wilsonMeasure (gaugeHaarMeasure L) β) ≤
      ε + 12 * (L : ℝ) ^ 4 *
        (Real.exp (-(β * (ε - δ))) / haarVacuumSublevelMass L δ) := by
  have hcard : (Fintype.card (Plaquette L) : ℝ) = 6 * (L : ℝ) ^ 4 := by
    exact_mod_cast card_plaquette_eq_six_mul_pow_four L
  calc
    _ ≤ ε + (2 * (Fintype.card (Plaquette L) : ℝ)) *
        (wilsonMeasure (gaugeHaarMeasure L) β).real {U | ε ≤ wilsonAction 1 U} :=
      haarWilsonMeanAction_le hβ hε
    _ ≤ ε + (2 * (Fintype.card (Plaquette L) : ℝ)) *
        (Real.exp (-(β * (ε - δ))) / haarVacuumSublevelMass L δ) := by
      gcongr
      exact haarWilsonMeasure_action_tail hβ hδ
    _ = _ := by rw [hcard]; ring

/-- Every actual local plaquette action is bounded by the total unit-coupling action. -/
theorem plaquetteAction_le_wilsonAction_one (U : GaugeConfig L) (p : Plaquette L) :
    plaquetteAction U p ≤ wilsonAction 1 U := by
  simpa [wilsonAction] using
    (Finset.single_le_sum (fun q (_ : q ∈ (Finset.univ : Finset (Plaquette L))) =>
      plaquetteAction_nonneg U q) (Finset.mem_univ p))

/-- Local gauge-invariant curvature observables vanish in mean on this fixed lattice.
No rate uniform in volume, field rescaling, or continuum limit is claimed. -/
theorem haarWilsonMeanPlaquette_tendsto (p : Plaquette L) :
    Tendsto (fun β : ℝ => ∫ U, plaquetteAction U p
      ∂wilsonMeasure (gaugeHaarMeasure L) β) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall fun β =>
    integral_nonneg fun U => plaquetteAction_nonneg U p) _ (haarWilsonMeanAction_tendsto (L := L))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with β hβ
  apply integral_mono
  · apply wilsonObservable_integrable (gaugeHaarMeasure L) hβ (measurable_wilsonAction β)
      (continuous_plaquetteAction p).measurable
    intro U
    simpa only [abs_of_nonneg (plaquetteAction_nonneg U p)] using plaquetteAction_le_two U p
  · apply wilsonObservable_integrable (gaugeHaarMeasure L) hβ (measurable_wilsonAction β)
      (measurable_wilsonAction 1)
    intro U
    rw [abs_of_nonneg (wilsonAction_nonneg (by norm_num) U)]
    exact wilsonAction_upper_bound (L := L) (β := 1) (by norm_num) U
  · exact fun U => plaquetteAction_le_wilsonAction_one U p

/-- A sufficient coupling threshold with the actual sublevel entropy loss displayed.
This is not a volume-uniform rate: `c = haarVacuumSublevelMass L δ` remains lattice-dependent. -/
theorem haarWilsonMeasure_action_tail_le_of_coupling {β δ ε η : ℝ}
    (hβ : 0 ≤ β) (hδ : 0 < δ) (hδε : δ < ε) (hη : 0 < η)
    (hrate : (Real.log (1 / haarVacuumSublevelMass L δ) + Real.log (1 / η)) /
      (ε - δ) ≤ β) :
    (wilsonMeasure (gaugeHaarMeasure L) β).real {U | ε ≤ wilsonAction 1 U} ≤ η := by
  have hc := haarVacuumSublevelMass_pos (L := L) hδ
  have hr := (div_le_iff₀ (sub_pos.mpr hδε)).mp hrate
  simp only [one_div, Real.log_inv] at hr
  apply (haarWilsonMeasure_action_tail hβ hδ).trans
  apply (div_le_iff₀ hc).mpr
  calc
    Real.exp (-(β * (ε - δ))) ≤
        Real.exp (Real.log η + Real.log (haarVacuumSublevelMass L δ)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = η * haarVacuumSublevelMass L δ := by
      rw [Real.exp_add, Real.exp_log hη, Real.exp_log hc]

/-- Conditional concentration along changing lattice volumes. The missing uniform input is
stated as an explicit entropy-versus-coupling divergence, not hidden in a constant. -/
theorem haarWilsonMeasure_action_tail_tendsto_varying_volume
    (sizes : ℕ → ℕ) [∀ n, NeZero (sizes n)] (β δ : ℕ → ℝ) (ε : ℝ)
    (hβ : ∀ n, 0 ≤ β n) (hδ : ∀ n, 0 < δ n)
    (hgain : Tendsto (fun n => β n * (ε - δ n) +
      Real.log (haarVacuumSublevelMass (sizes n) (δ n))) atTop atTop) :
    Tendsto (fun n => (wilsonMeasure (gaugeHaarMeasure (sizes n)) (β n)).real
      {U | ε ≤ wilsonAction 1 U}) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
    (Filter.Eventually.of_forall fun n => ?_)
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp hgain)
  calc
    _ ≤ Real.exp (-(β n * (ε - δ n))) / haarVacuumSublevelMass (sizes n) (δ n) :=
      haarWilsonMeasure_action_tail (hβ n) (hδ n)
    _ = Real.exp (-(β n * (ε - δ n) +
        Real.log (haarVacuumSublevelMass (sizes n) (δ n)))) := by
      rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _),
        Real.exp_log (haarVacuumSublevelMass_pos (hδ n)), div_eq_mul_inv]


/-- A single open identity neighborhood controls four-link plaquette action, independently
of the number of lattice sites. Its Haar mass is strictly positive. -/
theorem exists_haar_plaquette_neighborhood {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : Set SU2, IsOpen K ∧ (1 : SU2) ∈ K ∧ 0 < SU2.haarProbability.real K ∧
      ∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K, ∀ d ∈ K,
        1 - (1 / 2 : ℝ) * (SU2.trace (a * b * c⁻¹ * d⁻¹)).re < δ := by
  let A : (Fin 4 → SU2) → ℝ := fun v =>
    1 - (1 / 2 : ℝ) * (SU2.trace (v 0 * v 1 * (v 2)⁻¹ * (v 3)⁻¹)).re
  have hA : Continuous A := by
    dsimp [A, SU2.trace, Matrix.trace]
    fun_prop
  have hzero : A (fun _ => 1) = 0 := by
    simp only [A, inv_one, mul_one]
    have hm : (1 : SU2).mat = (1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl
    norm_num [SU2.trace, hm, Matrix.trace, Fin.sum_univ_two]
  have hopen : IsOpen {v | A v < δ} := isOpen_lt hA continuous_const
  obtain ⟨u, hu, hsub⟩ := isOpen_pi_iff'.mp hopen (fun _ => 1) (by simpa [hzero])
  let K : Set SU2 := ⋂ i, u i
  have hK : IsOpen K := isOpen_iInter_of_finite fun i => (hu i).1
  have hone : (1 : SU2) ∈ K := mem_iInter.mpr fun i => (hu i).2
  refine ⟨K, hK, hone,
    ENNReal.toReal_pos (ne_of_gt (hK.measure_pos _ ⟨1, hone⟩)) (measure_ne_top _ _), ?_⟩
  intro a ha b hb c hc d hd
  have hv : ![a, b, c, d] ∈ Set.univ.pi u := by
    intro i _
    fin_cases i <;>
      first | exact mem_iInter.mp ha _ | exact mem_iInter.mp hb _ |
        exact mem_iInter.mp hc _ | exact mem_iInter.mp hd _
  simpa [A] using hsub hv

/-- Product Haar gives an extensive lower bound on a small-action region. The base `c`
is independent of lattice size; its dependence on the target plaquette action is explicit
in the quantifier order. -/
theorem exists_haar_sublevel_mass_volume_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (L : ℕ) [NeZero L],
      c ^ (4 * L ^ 4) ≤ haarVacuumSublevelMass L (δ * (6 * (L : ℝ) ^ 4)) := by
  obtain ⟨K, hKo, hKone, hKpos, hK⟩ := exists_haar_plaquette_neighborhood hδ
  refine ⟨SU2.haarProbability.real K, hKpos, measureReal_le_one, ?_⟩
  intro L _
  have hlinks : Fintype.card (Link L) = 4 * L ^ 4 := by
    rw [Fintype.card_congr (linkEquiv L), Fintype.card_prod, card_lattice4D]
    simp [Direction, Nat.mul_comm]
  have hplaq : (Fintype.card (Plaquette L) : ℝ) = 6 * (L : ℝ) ^ 4 := by
    exact_mod_cast card_plaquette_eq_six_mul_pow_four L
  have hbox : (gaugeHaarMeasure L).real (Set.univ.pi fun _ : Link L => K) =
      SU2.haarProbability.real K ^ (4 * L ^ 4) := by
    change (Measure.pi (fun _ : Link L => SU2.haarProbability)
      (Set.univ.pi fun _ : Link L => K)).toReal = _
    rw [Measure.pi_pi]
    simp [Measure.real, ENNReal.toReal_pow, hlinks]
  rw [← hbox]
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro U hU
  change wilsonAction 1 U < δ * (6 * (L : ℝ) ^ 4)
  have hp : ∀ p : Plaquette L, plaquetteAction U p < δ := by
    intro p
    exact hK _ (hU _ (mem_univ _)) _ (hU _ (mem_univ _))
      _ (hU _ (mem_univ _)) _ (hU _ (mem_univ _))
  calc
    wilsonAction 1 U = ∑ p : Plaquette L, plaquetteAction U p := by simp [wilsonAction]
    _ < ∑ _ : Plaquette L, δ := by
      apply Finset.sum_lt_sum
      · intro p _; exact (hp p).le
      · exact ⟨⟨0, 0, 1, by decide⟩, Finset.mem_univ _, hp _⟩
    _ = _ := by simp [hplaq, mul_comm]

/-- Uniform entropy per site for the actual Haar Wilson law. `C` depends only on the
positive density scale `δ`, not on lattice size or coupling. Both bounds retain the
lattice site-count factor; no Hessian, RG, or physical mass-gap bound is asserted. -/
theorem exists_haarWilson_volume_bounds {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L] (β : ℝ), 0 ≤ β →
      Real.exp (-((C + β * δ) * (L : ℝ) ^ 4)) ≤
        wilsonPartition (gaugeHaarMeasure L) β ∧
      ∀ ε : ℝ, (wilsonMeasure (gaugeHaarMeasure L) β).real
        {U | ε * (L : ℝ) ^ 4 ≤ wilsonAction 1 U} ≤
          Real.exp (-((β * (ε - δ) - C) * (L : ℝ) ^ 4)) := by
  obtain ⟨c, hc, hc1, hmass⟩ := exists_haar_sublevel_mass_volume_bound
    (show 0 < δ / 6 by positivity)
  refine ⟨-4 * Real.log c, mul_nonneg_of_nonpos_of_nonpos (by norm_num)
    (Real.log_nonpos hc.le hc1), ?_⟩
  intro L _ β hβ
  have hV : 0 < (L : ℝ) ^ 4 := pow_pos (Nat.cast_pos.mpr (NeZero.pos L)) _
  have hδV : 0 < δ * (L : ℝ) ^ 4 := mul_pos hδ hV
  have hm : c ^ (4 * L ^ 4) ≤ haarVacuumSublevelMass L (δ * (L : ℝ) ^ 4) := by
    have he : δ / 6 * (6 * (L : ℝ) ^ 4) = δ * (L : ℝ) ^ 4 := by ring
    simpa only [he] using hmass L
  have hcPow : 0 < c ^ (4 * L ^ 4) := pow_pos hc _
  constructor
  · calc
      Real.exp (-((-4 * Real.log c + β * δ) * (L : ℝ) ^ 4)) =
          c ^ (4 * L ^ 4) * Real.exp (-(β * (δ * (L : ℝ) ^ 4))) := by
        rw [← Real.exp_log hcPow, Real.log_pow, ← Real.exp_add]
        congr 1
        push_cast
        ring
      _ ≤ haarVacuumSublevelMass L (δ * (L : ℝ) ^ 4) *
          Real.exp (-(β * (δ * (L : ℝ) ^ 4))) := by
        exact mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
      _ ≤ _ := haarWilsonPartition_sublevel_lower hβ
  · intro ε
    calc
      _ ≤ Real.exp (-(β * (ε * (L : ℝ) ^ 4 - δ * (L : ℝ) ^ 4))) /
          haarVacuumSublevelMass L (δ * (L : ℝ) ^ 4) :=
        haarWilsonMeasure_action_tail hβ hδV
      _ ≤ Real.exp (-(β * (ε * (L : ℝ) ^ 4 - δ * (L : ℝ) ^ 4))) /
          c ^ (4 * L ^ 4) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le hcPow hm
      _ = _ := by
        rw [← Real.exp_log hcPow, Real.log_pow, ← Real.exp_sub]
        congr 1
        push_cast
        ring

/-- A single coupling threshold suppresses action-density tails at every nonempty torus.
The lattice size is universally quantified after the threshold is chosen. -/
theorem haarWilsonMeasure_density_tail_uniform {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ B : ℝ, ∀ (L : ℕ) [NeZero L] (β : ℝ), B ≤ β →
      (wilsonMeasure (gaugeHaarMeasure L) β).real
        {U | ε * (L : ℝ) ^ 4 ≤ wilsonAction 1 U} < η := by
  obtain ⟨C, hC, hb⟩ := exists_haarWilson_volume_bounds (show 0 < ε / 2 by linarith)
  have hgain : Tendsto (fun β : ℝ => β * (ε - ε / 2) - C) atTop atTop :=
    tendsto_atTop.2 fun b => by
      have hm := tendsto_id.atTop_mul_const (show 0 < ε - ε / 2 by linarith)
      filter_upwards [hm.eventually (eventually_ge_atTop (b + C))] with β hβ
      simp only [id_eq] at hβ
      linarith
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp hgain
  have he : ∀ᶠ β : ℝ in atTop,
      0 ≤ β ∧ 0 ≤ β * (ε - ε / 2) - C ∧
        Real.exp (-(β * (ε - ε / 2) - C)) < η := by
    filter_upwards [eventually_ge_atTop (0 : ℝ),
      hgain.eventually (eventually_ge_atTop (0 : ℝ)), ht.eventually_lt_const hη]
      with β hβ hg ht
    exact ⟨hβ, hg, ht⟩
  obtain ⟨B, hB⟩ := eventually_atTop.1 he
  refine ⟨B, ?_⟩
  intro L _ β hβB
  obtain ⟨hβ, hg, ht⟩ := hB β hβB
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast (NeZero.one_le : 1 ≤ L)
  have hV : (1 : ℝ) ≤ (L : ℝ) ^ 4 := one_le_pow₀ hL
  apply lt_of_le_of_lt ((hb L β hβ).2 ε) ?_
  apply lt_of_le_of_lt (Real.exp_le_exp.mpr ?_) ht
  have hm := mul_le_mul_of_nonneg_left hV hg
  linarith

/-- Action density is bounded in mean by its small-density region and its tail. -/
theorem haarWilsonMeanActionDensity_le {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 ≤ ε) :
    (∫ U, wilsonAction 1 U ∂wilsonMeasure (gaugeHaarMeasure L) β) / (L : ℝ) ^ 4 ≤
      ε + 12 * (wilsonMeasure (gaugeHaarMeasure L) β).real
        {U | ε * (L : ℝ) ^ 4 ≤ wilsonAction 1 U} := by
  have hV : 0 < (L : ℝ) ^ 4 := pow_pos (Nat.cast_pos.mpr (NeZero.pos L)) _
  have hcard : (Fintype.card (Plaquette L) : ℝ) = 6 * (L : ℝ) ^ 4 := by
    exact_mod_cast card_plaquette_eq_six_mul_pow_four L
  apply (div_le_iff₀ hV).mpr
  have hb := haarWilsonMeanAction_le (L := L) hβ (mul_nonneg hε hV.le)
  rw [hcard] at hb
  convert hb using 1
  ring

/-- The mean action density tends to zero uniformly over all nonzero lattice sizes.
No separate entropy-growth hypothesis is needed for this normalized observable. -/
theorem haarWilsonMeanActionDensity_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, ∀ (L : ℕ) [NeZero L] (β : ℝ), B ≤ β →
      (∫ U, wilsonAction 1 U ∂wilsonMeasure (gaugeHaarMeasure L) β) / (L : ℝ) ^ 4 < ε := by
  obtain ⟨B, hB⟩ := haarWilsonMeasure_density_tail_uniform
    (show 0 < ε / 2 by linarith) (show 0 < ε / 24 by linarith)
  refine ⟨max B 0, ?_⟩
  intro L _ β hβ
  have hp := hB L β (le_trans (le_max_left _ _) hβ)
  have hm := haarWilsonMeanActionDensity_le (L := L)
    (le_trans (le_max_right _ _) hβ) (show 0 ≤ ε / 2 by linarith)
  linarith

/-- Arbitrarily varying nonzero volumes need no rate constraint for action-density
concentration, provided the bare inverse coupling diverges. -/
theorem haarWilsonMeanActionDensity_tendsto_varying_volume
    (sizes : ℕ → ℕ) [∀ n, NeZero (sizes n)] (β : ℕ → ℝ)
    (hβ : Tendsto β atTop atTop) :
    Tendsto (fun n => (∫ U, wilsonAction 1 U
      ∂wilsonMeasure (gaugeHaarMeasure (sizes n)) (β n)) / (sizes n : ℝ) ^ 4)
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n => lt_of_lt_of_le ha
      (div_nonneg (integral_nonneg fun U => wilsonAction_nonneg (by norm_num) U)
        (by positivity))
  · intro ε hε
    obtain ⟨B, hB⟩ := haarWilsonMeanActionDensity_uniform hε
    filter_upwards [hβ.eventually (eventually_ge_atTop B)] with n hn
    exact hB (sizes n) (β n) hn

/-- Candidate inverse-coupling envelope. This scalar definition supplies no Hessian,
Brascamp--Lieb inequality or estimate on a Wilson fiber integral. -/
noncomputable def brascampLiebWeakCouplingSubGaussianEnvelope (c_hess β : ℝ) : ℝ := c_hess / β

/-- For any supplied positive scalar `c_hess`, the candidate envelope
`brascampLiebWeakCouplingSubGaussianEnvelope c_hess β = c_hess / β`
is strictly positive for `0 < β`, antitone in `β`, bounded by `ε` whenever `c_hess / ε ≤ β`,
strictly smaller than the naive `12 β` fine-action Lipschitz ceiling for `max 1 c_hess ≤ β`,
and vanishes (`Tendsto ... atTop (𝓝 0)`) as `β → ∞`. -/
theorem brascampLiebWeakCouplingSubGaussianEnvelope_pos_and_tendsto_zero
    {c_hess : ℝ} (hc : 0 < c_hess) :
    (∀ {β : ℝ}, 0 < β → 0 < brascampLiebWeakCouplingSubGaussianEnvelope c_hess β) ∧
    (∀ {β₁ β₂ : ℝ}, 0 < β₁ → β₁ ≤ β₂ →
      brascampLiebWeakCouplingSubGaussianEnvelope c_hess β₂ ≤
        brascampLiebWeakCouplingSubGaussianEnvelope c_hess β₁) ∧
    (∀ {β ε : ℝ}, 0 < ε → c_hess / ε ≤ β →
      brascampLiebWeakCouplingSubGaussianEnvelope c_hess β ≤ ε) ∧
    (∀ {β : ℝ}, max 1 c_hess ≤ β →
      brascampLiebWeakCouplingSubGaussianEnvelope c_hess β < 12 * β) ∧
    Tendsto (fun β : ℝ => brascampLiebWeakCouplingSubGaussianEnvelope c_hess β) atTop (𝓝 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro β hβ
    exact div_pos hc hβ
  · intro β₁ β₂ hβ₁ h12
    exact div_le_div_of_nonneg_left hc.le hβ₁ h12
  · intro β ε hε hthresh
    have hβ : 0 < β := lt_of_lt_of_le (div_pos hc hε) hthresh
    rw [brascampLiebWeakCouplingSubGaussianEnvelope, div_le_iff₀ hβ]
    have h1 := (div_le_iff₀ hε).mp hthresh
    linarith
  · intro β hβ
    have hβ1 : 1 ≤ β := le_trans (le_max_left 1 c_hess) hβ
    have hβc : c_hess ≤ β := le_trans (le_max_right 1 c_hess) hβ
    have hβ_pos : 0 < β := lt_of_lt_of_le hc hβc
    have h1 : brascampLiebWeakCouplingSubGaussianEnvelope c_hess β ≤ 1 := by
      rw [brascampLiebWeakCouplingSubGaussianEnvelope, div_le_iff₀ hβ_pos]
      linarith
    linarith
  · apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
      exact lt_trans ha (div_pos hc hβ)
    · intro b hb
      filter_upwards [eventually_gt_atTop (c_hess / b)] with β hβ
      have hβ_pos : 0 < β := lt_trans (div_pos hc hb) hβ
      rw [brascampLiebWeakCouplingSubGaussianEnvelope, div_lt_iff₀ hβ_pos]
      have hcb : c_hess < β * b := (div_lt_iff₀ hb).mp hβ
      linarith

/-- Scalar recurrence candidate. Binding its contraction and innovation terms to
successive exact blocked measures remains a separate obligation. -/
noncomputable def multiStepCarriedForwardRemainderEnvelope
    (q_step η_prev c_hess β_step : ℝ) : ℝ :=
  q_step * η_prev + brascampLiebWeakCouplingSubGaussianEnvelope c_hess β_step

/-- One-step scalar invariant-region arithmetic under supplied innovation, coupling
and tube bounds. No RG trajectory, entry into the tube, or conditional-TV row sum
is constructed by this theorem. Iteration requires these premises at every step. -/
theorem multiStepCarriedForwardRemainderEnvelope_contractive_tube_and_dobrushin_landing
    {q_step η_prev η_star c_hess β_min β_step β_ir β_star : ℝ}
    (hq0 : 0 ≤ q_step) (hq1 : q_step < 1)
    (hη_prev0 : 0 ≤ η_prev) (hη_prev : η_prev ≤ η_star)
    (hc : 0 ≤ c_hess) (hβ_min : 0 < β_min) (hβ_step : β_min ≤ β_step)
    (h_innov : c_hess / β_min ≤ (1 - q_step) * η_star)
    (hβ_ir0 : 0 ≤ β_ir) (hβ_ir : β_ir ≤ β_star)
    (h_tube : 18 * β_star + η_star < 1) :
    0 < 1 - q_step ∧
    0 ≤ multiStepCarriedForwardRemainderEnvelope q_step η_prev c_hess β_step ∧
    multiStepCarriedForwardRemainderEnvelope q_step η_prev c_hess β_step ≤ η_star ∧
    0 ≤ 18 * β_ir + multiStepCarriedForwardRemainderEnvelope q_step η_prev c_hess β_step ∧
    18 * β_ir + multiStepCarriedForwardRemainderEnvelope q_step η_prev c_hess β_step ≤
      18 * β_star + η_star ∧
    18 * β_ir + multiStepCarriedForwardRemainderEnvelope q_step η_prev c_hess β_step < 1 := by
  have hβ_pos : 0 < β_step := lt_of_lt_of_le hβ_min hβ_step
  have h_div_nonneg : 0 ≤ brascampLiebWeakCouplingSubGaussianEnvelope c_hess β_step :=
    div_nonneg hc hβ_pos.le
  have h_div_mono :
      brascampLiebWeakCouplingSubGaussianEnvelope c_hess β_step ≤ c_hess / β_min :=
    div_le_div_of_nonneg_left hc hβ_min hβ_step
  have h_q_mul : q_step * η_prev ≤ q_step * η_star :=
    mul_le_mul_of_nonneg_left hη_prev hq0
  have h_nonneg : 0 ≤ multiStepCarriedForwardRemainderEnvelope q_step η_prev c_hess β_step := by
    dsimp [multiStepCarriedForwardRemainderEnvelope]
    have hqη : 0 ≤ q_step * η_prev := mul_nonneg hq0 hη_prev0
    linarith
  have h_le_star : multiStepCarriedForwardRemainderEnvelope q_step η_prev c_hess β_step ≤ η_star := by
    dsimp [multiStepCarriedForwardRemainderEnvelope]
    linarith
  refine ⟨sub_pos.mpr hq1, h_nonneg, h_le_star, by linarith, by linarith, by linarith⟩

#assert_zfc_axioms

end JesseMath.Physics
