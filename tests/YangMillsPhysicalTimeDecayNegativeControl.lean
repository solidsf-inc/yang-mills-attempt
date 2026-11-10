import JesseMath.Physics.YangMillsPhysicalTimeDecay
import JesseMath.Linter.AxiomAudit

/-!
Negative controls for `YangMillsPhysicalTimeDecay` on an explicit two-mode model. Each false
strengthening is stated as a `Prop` and refuted by a model that satisfies all of its premises.

1. `floorImpliesSurvivingExcitation_false`: a uniform physical floor plus strong convergence of
   the lattice evolutions does not give a surviving excitation. A fixed per-step factor `7 / 8` at
   the bare spacing `a_n = 1 / (n + 1)` satisfies every premise, and its limit annihilates the
   excited mode at every positive time.
2. `cutoffwiseContractionImpliesFloor_false`: a contraction at every cutoff does not give the
   uniform floor; the per-step factor `exp (-a_n²)` has physical rate `a_n → 0`.
3. `log_eight_sevenths_bare_step_has_no_finite_physical_rate`: read at the bare spacing,
   `log (8 / 7)` has physical rate `(n + 1) log (8 / 7)`, which converges to no real number.
4. `sevenEighths_admits_no_obligations`: no instance of `PhysicalTimeDecayObligations` has the
   constant per-step factor `7 / 8`.

These are models for the abstract interface, not Wilson transfer operators.
-/

noncomputable section

namespace JesseMath.Physics.YangMillsPhysicalTimeDecayNegativeControl

open JesseMath.Physics.YangMillsPhysicalTimeDecay JesseMath.Physics.YangMillsPhysicalGap Filter
open scoped Topology InnerProductSpace

abbrev TwoModes := EuclideanSpace ℂ (Fin 2)

def vacuum : TwoModes := EuclideanSpace.single 0 1

def excited : TwoModes := EuclideanSpace.single 1 1

theorem vacuum_norm : ‖vacuum‖ = 1 := by simp [vacuum]

theorem excited_norm : ‖excited‖ = 1 := by simp [excited]

theorem excited_ne_zero : excited ≠ 0 := by
  intro h
  have hn := excited_norm
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

theorem excited_orthogonal : ⟪vacuum, excited⟫_ℂ = 0 := by
  simp [vacuum, excited, EuclideanSpace.inner_single_left]

/-! ### 1. A fixed bare-step factor `7 / 8` -/

/-- The per-step factor `7 / 8` at every cutoff of the path `a_n = 1 / (n + 1)`. -/
def sevenEighthsStep (n : ℕ) : LatticeTransferStep TwoModes :=
  rankOneStep vacuum_norm (harmonicCutoffPath.spacing n) (harmonicCutoffPath.spacing_pos n) (7 / 8)

/-- The strong limit of these lattice evolutions: identity at `t = 0`, vacuum projection for
`t > 0`. -/
def collapsedLimit (t : ℝ) : TwoModes →L[ℂ] TwoModes :=
  rankOneTransfer vacuum (if t = 0 then 1 else 0)

theorem sevenEighthsStep_spacing (n : ℕ) :
    (sevenEighthsStep n).spacing = harmonicCutoffPath.spacing n := rfl

theorem sevenEighthsStep_vacuum (n : ℕ) : (sevenEighthsStep n).vacuum = vacuum := rfl

theorem sevenEighthsStep_contraction (n : ℕ) : (sevenEighthsStep n).StepContraction (7 / 8) :=
  rankOneStep_contraction vacuum_norm _ _ (by norm_num)

/-- The uniform floor holds: the spacings are at most `1`, so `m0 = log (8 / 7)` works. -/
theorem sevenEighths_uniform_floor :
    UniformPhysicalRateFloor (fun n => (sevenEighthsStep n).spacing)
      (fun _ => latticeRate (7 / 8)) := by
  have hc : 0 < latticeRate (7 / 8) := latticeRate_pos (by norm_num) (by norm_num)
  refine (fixed_rate_uniformFloor_iff_spacing_bounded hc
    (fun n => harmonicCutoffPath.spacing_pos n)).mpr ⟨1, fun n => ?_⟩
  show 1 / ((n : ℝ) + 1) ≤ 1
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The lattice evolutions converge strongly at every `t ≥ 0`. -/
theorem sevenEighths_strong_limit (t : ℝ) (ht : 0 ≤ t) (u : TwoModes) :
    Tendsto (fun n => (sevenEighthsStep n).evolution t u) atTop (𝓝 (collapsedLimit t u)) := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    have hev : ∀ n, (sevenEighthsStep n).evolution 0 u = u := fun n => by
      rw [(sevenEighthsStep n).evolution_zero, one_apply_eq_self]
    have hlim : collapsedLimit 0 u = u := by
      simp [collapsedLimit, rankOneTransfer_apply, excitedPart]
    simp only [hev, hlim]
    exact tendsto_const_nhds
  · have hN := elapsedSteps_tendsto_atTop harmonicCutoffPath hpos
    have hpow : Tendsto (fun n => ((7 / 8 : ℝ) ^ elapsedSteps (harmonicCutoffPath.spacing n) t))
        atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hN
    have hc : Tendsto (fun n =>
        (((7 / 8 : ℝ) ^ elapsedSteps (harmonicCutoffPath.spacing n) t : ℝ) : ℂ)) atTop
        (𝓝 ((0 : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto _).comp hpow
    have hlim : collapsedLimit t u =
        vacuumPart vacuum u + ((0 : ℝ) : ℂ) • excitedPart vacuum u := by
      simp [collapsedLimit, rankOneTransfer_apply, hpos.ne']
    rw [hlim]
    have hev : ∀ n, (sevenEighthsStep n).evolution t u = vacuumPart vacuum u +
        (((7 / 8 : ℝ) ^ elapsedSteps (harmonicCutoffPath.spacing n) t : ℝ) : ℂ) •
          excitedPart vacuum u := fun n =>
      rankOneStep_evolution_apply vacuum_norm _ _ (7 / 8) t u
    simp only [hev]
    exact tendsto_const_nhds.add (hc.smul_const (excitedPart vacuum u))

theorem collapsedLimit_annihilates_excited (t : ℝ) (ht : 0 < t) : collapsedLimit t excited = 0 := by
  simp [collapsedLimit, rankOneTransfer_apply, vacuumPart, excited_orthogonal, ht.ne']

/-- False strengthening: "a uniform physical floor and strong convergence of the lattice
evolutions give a vacuum-orthogonal vector that survives at every positive time". -/
def FloorImpliesSurvivingExcitation : Prop :=
  ∀ (S : ℕ → LatticeTransferStep TwoModes) (ρ : ℕ → ℝ) (T : ℝ → TwoModes →L[ℂ] TwoModes),
    (∀ n, 0 < ρ n) → (∀ n, (S n).StepContraction (ρ n)) →
    UniformPhysicalRateFloor (fun n => (S n).spacing) (fun n => latticeRate (ρ n)) →
    (∀ n, (S n).vacuum = vacuum) →
    (∀ t, 0 ≤ t → ∀ u, Tendsto (fun n => (S n).evolution t u) atTop (𝓝 (T t u))) →
    ∃ u : TwoModes, ⟪vacuum, u⟫_ℂ = 0 ∧ u ≠ 0 ∧ ∀ t, 0 < t → T t u ≠ 0

theorem floorImpliesSurvivingExcitation_false : ¬ FloorImpliesSurvivingExcitation := by
  intro h
  obtain ⟨u, hu, _, hsurv⟩ := h sevenEighthsStep (fun _ => 7 / 8) collapsedLimit
    (fun _ => by norm_num) sevenEighthsStep_contraction sevenEighths_uniform_floor
    sevenEighthsStep_vacuum sevenEighths_strong_limit
  apply hsurv 1 one_pos
  simp [collapsedLimit, rankOneTransfer_apply, vacuumPart, hu]

/-- The module's collapse theorem identifies the missing ingredient: this limit is not strongly
continuous at `t = 0`, because a strongly continuous limit of a fixed-factor family is trivial. -/
theorem collapsedLimit_not_strongly_continuous :
    ¬ ∀ u : TwoModes, Tendsto (fun t => collapsedLimit t u) (𝓝[>] 0) (𝓝 u) := by
  intro hcont
  have h := fixed_step_contraction_strongly_continuous_limit_is_trivial Set.univ dense_univ
    harmonicCutoffPath sevenEighthsStep sevenEighthsStep_spacing (by norm_num) (by norm_num)
    sevenEighthsStep_contraction collapsedLimit vacuum tendsto_const_nhds
    (fun t ht u _ => sevenEighths_strong_limit t ht.le u) hcont excited excited_orthogonal
  exact excited_ne_zero h

/-- The obligations exclude the fixed factor: their per-step factors tend to `1`. -/
theorem sevenEighths_admits_no_obligations :
    ¬ ∃ O : PhysicalTimeDecayObligations TwoModes, ∀ n, O.stepFactor n = 7 / 8 := by
  rintro ⟨O, hO⟩
  have h := O.stepFactor_tendsto_one
  rw [show O.stepFactor = fun _ => 7 / 8 from funext hO] at h
  have heq : (7 / 8 : ℝ) = 1 := tendsto_nhds_unique tendsto_const_nhds h
  norm_num at heq

/-! ### 2. Contraction at every cutoff without a floor -/

/-- Per-step factor `exp (-a_n²)` at the bare spacing `a_n = 1 / (n + 1)`. -/
def vanishingRateStep (n : ℕ) : LatticeTransferStep TwoModes :=
  rankOneStep vacuum_norm (harmonicCutoffPath.spacing n) (harmonicCutoffPath.spacing_pos n)
    (Real.exp (-(harmonicCutoffPath.spacing n ^ 2)))

/-- False strengthening: "a contraction factor below one at every cutoff gives the uniform
physical floor" (the uniformity claim without its hypothesis). -/
def CutoffwiseContractionImpliesFloor : Prop :=
  ∀ (S : ℕ → LatticeTransferStep TwoModes) (ρ : ℕ → ℝ),
    (∀ n, 0 < ρ n) → (∀ n, ρ n < 1) → (∀ n, (S n).StepContraction (ρ n)) →
    UniformPhysicalRateFloor (fun n => (S n).spacing) (fun n => latticeRate (ρ n))

theorem vanishingRate_physicalRate (n : ℕ) :
    physicalRate (vanishingRateStep n).spacing
      (latticeRate (Real.exp (-(harmonicCutoffPath.spacing n ^ 2)))) =
      harmonicCutoffPath.spacing n := by
  have hne : harmonicCutoffPath.spacing n ≠ 0 := (harmonicCutoffPath.spacing_pos n).ne'
  show physicalRate (harmonicCutoffPath.spacing n) _ = _
  unfold physicalRate latticeRate
  rw [Real.log_exp, neg_neg, sq, mul_div_cancel_right₀ _ hne]

theorem cutoffwiseContractionImpliesFloor_false : ¬ CutoffwiseContractionImpliesFloor := by
  intro h
  obtain ⟨m0, hm0, hle⟩ := h vanishingRateStep
    (fun n => Real.exp (-(harmonicCutoffPath.spacing n ^ 2)))
    (fun _ => Real.exp_pos _)
    (fun n => Real.exp_lt_one_iff.mpr (by
      have := harmonicCutoffPath.spacing_pos n
      nlinarith))
    (fun n => rankOneStep_contraction vacuum_norm _ _ (Real.exp_pos _).le)
  obtain ⟨n, hn⟩ := ((tendsto_order.1 harmonicCutoffPath.spacing_tendsto_zero).2 m0 hm0).exists
  have hb := hle n
  rw [vanishingRate_physicalRate n] at hb
  linarith

/-! ### 3. `log (8 / 7)` at the bare spacing -/

theorem log_eight_sevenths_bare_step_has_no_finite_physical_rate :
    ¬ ∃ m : ℝ, Tendsto (fun n => physicalRate (harmonicCutoffPath.spacing n) (Real.log (8 / 7)))
      atTop (𝓝 m) := by
  rintro ⟨m, hm⟩
  exact not_tendsto_nhds_of_tendsto_atTop
    (physicalRate_tendsto_atTop_of_spacing_tendsto_zero log_eight_sevenths_pos _
      harmonicCutoffPath.spacing_pos harmonicCutoffPath.spacing_tendsto_zero) m hm

end JesseMath.Physics.YangMillsPhysicalTimeDecayNegativeControl

#assert_zfc_axioms
