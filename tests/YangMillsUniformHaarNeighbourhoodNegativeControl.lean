import JesseMath.Physics.YangMillsUniformHaarNeighbourhood

/-! Negative controls for the volume law of the Haar vacuum sublevel mass.

The tempting strengthening `c(L, δ) ≥ c₁(δ)^N(L)` with a base `c₁(δ) > 0` independent of the lattice
size is false at every fixed total-action threshold `δ > 0`; Lean proves its negation from the
private-link upper bound. A scale-uniform single-link mass, a fixed-coupling version of the
fixed-threshold bound, fixed-coupling concentration of the actual Wilson law at a fixed total
threshold, and concentration under every divergent coupling schedule are refuted in the same
way. The positive statements below show the
hypotheses under which the uniform forms do hold: a per-plaquette (density) threshold, or a
coupling growing like `L⁴ log L`. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace JesseMath.Physics.YangMillsUniformHaarNeighbourhoodNegativeControl

/-- False strengthening refuted: no base `c₁ > 0` independent of `L` satisfies
`c₁ ^ N(L) ≤ c(L, δ)` for all tori at a fixed total threshold `δ`. -/
theorem no_volume_uniform_link_base {δ : ℝ} (hδ : 0 < δ) :
    ¬ ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (L : ℕ) [NeZero L], c₁ ^ (4 * L ^ 4) ≤ haarVacuumSublevelMass L δ := by
  rintro ⟨c₁, hc₁, hb⟩
  set β : ℕ → ℝ := fun n => -(4 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.log c₁) with hβ_def
  have hlin : ∀ n, β n ≤ -(4 * Real.log c₁) * (((n + 1 : ℕ) : ℕ) : ℝ) ^ 4 := fun n =>
    le_of_eq (by simp only [hβ_def]; ring)
  have ht := weakCouplingTailBound_tendsto_atTop_of_le_linear (ε := δ + 1) hδ (by linarith)
    (fun n => n + 1) (tendsto_add_atTop_nat 1) β hlin
  have hle : ∀ n : ℕ, weakCouplingTailBound (n + 1) (β n) (δ + 1) δ ≤ 1 := by
    intro n
    unfold weakCouplingTailBound
    rw [div_le_one (haarVacuumSublevelMass_pos hδ)]
    have he : Real.exp (-(β n * (δ + 1 - δ))) = c₁ ^ (4 * (n + 1) ^ 4) := by
      rw [← Real.exp_log (pow_pos hc₁ _), Real.log_pow]
      congr 1
      simp only [hβ_def]
      push_cast
      ring
    rw [he]
    exact hb (n + 1)
  obtain ⟨n, hn⟩ := (ht.eventually (eventually_ge_atTop 2)).exists
  linarith [hle n]

/-- False strengthening refuted: the single-link neighbourhood mass has no positive lower bound
uniform in the scale `η`, since `c₁(η) ≤ √(2η)`. -/
theorem no_scale_uniform_single_link_mass :
    ¬ ∃ κ : ℝ, 0 < κ ∧ ∀ η : ℝ, 0 < η → κ ≤ singleLinkMass η := by
  rintro ⟨κ, hκ, hb⟩
  have h1 := hb (κ ^ 2 / 4) (by positivity)
  have h2 := singleLinkMass_le_sqrt (η := κ ^ 2 / 4) (by positivity)
  have h3 : Real.sqrt (2 * (κ ^ 2 / 4)) < κ := by
    rw [Real.sqrt_lt' hκ]
    nlinarith
  linarith

/-- False strengthening refuted: at a fixed coupling `β ≥ 0` and fixed total threshold, the
bound `exp (-β (ε - δ)) / c(L, δ)` is not uniformly small in `L`; it diverges. -/
theorem fixed_coupling_bound_diverges {β ε δ : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε) (hβ : 0 ≤ β) :
    Tendsto (fun n : ℕ => weakCouplingTailBound (n + 1) β ε δ) atTop atTop :=
  weakCouplingTailBound_tendsto_atTop_of_le_linear hδ hδε (fun n => n + 1)
    (tendsto_add_atTop_nat 1) (fun _ => β) fun n => by
      have h1 : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      have h2 : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℕ) : ℝ) ^ 4 := one_le_pow₀ h1
      nlinarith

/-- Consequently no single fixed coupling makes the fixed-threshold bound at most `1` on every
torus. -/
theorem no_fixed_coupling_uniform_bound {β ε δ : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε) (hβ : 0 ≤ β) :
    ¬ ∀ (L : ℕ) [NeZero L], weakCouplingTailBound L β ε δ ≤ 1 := by
  intro h
  obtain ⟨n, hn⟩ :=
    ((fixed_coupling_bound_diverges hδ hδε hβ).eventually (eventually_ge_atTop 2)).exists
  linarith [h (n + 1)]

/-- False strengthening refuted for the actual Wilson law: no fixed coupling keeps the
fixed-threshold action tail at most `1/2` on every torus, since that tail tends to one. -/
theorem no_fixed_coupling_concentration {ε β : ℝ} (hε : 0 < ε) (hβ : 0 ≤ β) :
    ¬ ∀ (L : ℕ) [NeZero L], (wilsonMeasure (gaugeHaarMeasure L) β).real
      {U | ε ≤ wilsonAction 1 U} ≤ 1 / 2 := by
  intro h
  obtain ⟨n, hn⟩ := ((haarWilsonMeasure_action_tail_tendsto_one_fixed_coupling hε hβ).eventually
    (lt_mem_nhds (by norm_num : (3 / 4 : ℝ) < 1))).exists
  linarith [h (n + 1)]

/-- False strengthening refuted: unlike action densities (where any `β(L) → ∞` suffices, see
`haarWilsonMeanActionDensity_tendsto_varying_volume`), a fixed total threshold is not controlled
by every divergent coupling schedule. The schedule `β(L) = L^(1/64)` diverges, yet the actual
action tail tends to one. -/
theorem not_every_divergent_schedule_concentrates {ε : ℝ} (hε : 0 < ε) :
    ¬ ∀ β : ℕ → ℝ, (∀ n, 0 ≤ β n) → Tendsto β atTop atTop →
      Tendsto (fun n : ℕ => (wilsonMeasure (gaugeHaarMeasure (n + 1)) (β n)).real
        {U | ε ≤ wilsonAction 1 U}) atTop (𝓝 0) := by
  intro h
  set β : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) ^ (1 / 64 : ℝ) with hβ_def
  have hx : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hβ0 : ∀ n, 0 ≤ β n := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hβtop : Tendsto β atTop atTop := (tendsto_rpow_atTop (by norm_num)).comp hx
  have hgap : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (3 / 320 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hx
  have hslow : ∀ᶠ n in atTop, 2400 * (β n + 1) ≤ ((n + 1 : ℕ) : ℝ) ^ (1 / 40 : ℝ) := by
    filter_upwards [hgap.eventually (eventually_ge_atTop 4800)] with n hn
    have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have h0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hβ1 : 1 ≤ β n := Real.one_le_rpow h1 (by norm_num)
    have hsplit : ((n + 1 : ℕ) : ℝ) ^ (1 / 40 : ℝ) =
        β n * ((n + 1 : ℕ) : ℝ) ^ (3 / 320 : ℝ) := by
      rw [hβ_def, ← Real.rpow_add h0]
      norm_num
    rw [hsplit]
    nlinarith
  have hone := haarWilsonMeasure_action_tail_tendsto_one_of_le_rpow hε (by norm_num)
    (fun n => n + 1) (tendsto_add_atTop_nat 1) β hβ0 hslow
  have hzero := h β hβ0 hβtop
  have := tendsto_nhds_unique hone hzero
  norm_num at this

/-- With the per-plaquette (density) threshold the uniform base does exist, explicitly. -/
example : ∀ (L : ℕ) [NeZero L], ((1 / 400 : ℝ) ^ 2) ^ (4 * L ^ 4) ≤
    haarVacuumSublevelMass L (6 * (L : ℝ) ^ 4 * 1) := fun L _ =>
  by simpa using haarVacuumSublevelMass_density_ge L (δ := 1) (by norm_num) (by norm_num)

/-- With coupling growth of order `L⁴ log L` the fixed-threshold action tail does vanish. -/
example : Tendsto (fun n : ℕ => (wilsonMeasure (gaugeHaarMeasure (n + 1))
    ((8 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.log (2400 * ((n + 1 : ℕ) : ℝ) ^ 4 / 1) + n) /
      (2 - 1))).real {U | 2 ≤ wilsonAction 1 U}) atTop (𝓝 0) :=
  haarWilsonMeasure_action_tail_tendsto_schedule (ε := 2) (δ := 1) (by norm_num) (by norm_num)
    (by norm_num) (fun n => n) (fun n => Nat.cast_nonneg n) tendsto_natCast_atTop_atTop

#assert_zfc_axioms

end JesseMath.Physics.YangMillsUniformHaarNeighbourhoodNegativeControl
