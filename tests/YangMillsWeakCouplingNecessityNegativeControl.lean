import JesseMath.Physics.YangMillsWeakCouplingNecessity

/-!
# Negative controls for `YangMillsWeakCouplingNecessity`

Each theorem below states a false strengthening of a weak-coupling claim and proves its negation
on an explicit model of the actual SU(2) Wilson law: the canonical SU(2) Clause (0) cutoff path
`canonicalCutoffPath` (`b = 13`, one infrared block, `aIR = 1`), the explicit Haar ingredient (H),
or the structures of `YangMillsPhysicalBridges`. Two `example`s record the positive forms that do
hold with the hypotheses the module needs.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace JesseMath.Physics.YangMillsWeakCouplingNecessityNegativeControl

open JesseMath.Physics JesseMath.Physics.YangMillsCutoffPathBalance
  JesseMath.Physics.YangMillsWeakCouplingNecessity

/-- False strengthening: the canonical SU(2) Clause (0) path concentrates the total action at a
fixed threshold `ε > 0`. -/
theorem canonical_path_concentration_rejected {ε : ℝ} (hε : 0 < ε) :
    ¬ Tendsto (pathTail canonicalCutoffPath ε) atTop (𝓝 0) := by
  intro h0
  have h1 := clauseZero_wilsonTail_tendsto_one canonicalSchedule hε
  have h := tendsto_nhds_unique h0 h1
  norm_num at h

/-- False strengthening: a divergent bare coupling alone concentrates the total action along
every fixed-volume cutoff path. -/
theorem divergent_coupling_concentration_rejected :
    ¬ ∀ P : FixedVolumeCutoffPath, Tendsto P.β atTop atTop →
      Tendsto (pathTail P 1) atTop (𝓝 0) := fun h =>
  canonical_path_concentration_rejected one_pos
    (h canonicalCutoffPath canonicalCutoffPath_nondegenerate.2.1)

/-- False strengthening: some asymptotic-freedom coupling `β_n ≤ A + B log (1 / a_n)` with
`B > 0` concentrates the total action. -/
theorem logarithmic_coupling_concentration_rejected :
    ¬ ∃ (P : FixedVolumeCutoffPath) (A B : ℝ), 0 < B ∧
      (∀ n, P.β n ≤ A + B * Real.log (1 / P.a n)) ∧
      Tendsto (pathTail P 1) atTop (𝓝 0) := by
  rintro ⟨P, A, B, _, hlog, h0⟩
  have h1 := wilsonTail_tendsto_one_of_logarithmic P one_pos (Eventually.of_forall hlog)
  have h := tendsto_nhds_unique h0 h1
  norm_num at h

/-- False strengthening: on the canonical path some positive thresholds satisfy the gain
hypothesis `hgain` of `haarWilsonMeasure_action_tail_tendsto_varying_volume`. -/
theorem canonical_path_repository_gain_rejected {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧
      Tendsto (fun n => canonicalCutoffPath.β n * (ε - δ n) +
        Real.log (haarVacuumSublevelMass (canonicalCutoffPath.sites n) (δ n))) atTop atTop := by
  rintro ⟨δ, hδ, hgain⟩
  exact not_repositoryGain_of_logarithmic canonicalCutoffPath hε
    (Eventually.of_forall (clauseZero_coupling_le_log canonicalSchedule)) δ hδ hgain

/-- False strengthening: on the canonical path some ingredient (H) balances, i.e. its balance
exponent diverges, for some choice of thresholds and per-link factors. -/
theorem canonical_path_balance_rejected :
    ¬ ∃ H : PathHaarMassBound canonicalCutoffPath.toFixedVolumeGeometry,
      Tendsto (fun n => balanceExponent (canonicalCutoffPath.sites n) (canonicalCutoffPath.β n)
        1 (H.δ n) (H.c₁ n)) atTop atTop := by
  rintro ⟨H, hbal⟩
  exact not_balance_of_logarithmic canonicalCutoffPath H one_pos
    (Eventually.of_forall (clauseZero_coupling_le_log canonicalSchedule)) hbal

/-- False strengthening: ingredient (H) with a fixed threshold and a constant per-link factor
exists on the canonical path (the hypotheses of `wilsonTail_tendsto_zero_of_supercritical`). -/
theorem constant_factor_ingredient_rejected :
    ¬ ∃ (H : PathHaarMassBound canonicalCutoffPath.toFixedVolumeGeometry) (c : ℝ),
      ∀ n, H.δ n = 1 / 2 ∧ H.c₁ n = c := by
  rintro ⟨H, c, h⟩
  exact no_constant_factor_pathHaarMassBound _ ⟨H, 1 / 2, c, fun n => (h n).1, fun n => (h n).2⟩

/-- False strengthening: a volume-uniform influence family carries a coupling `β_next ≥ 1/18`. -/
theorem volume_uniform_family_weak_coupling_rejected :
    ¬ ∃ fam : YangMillsRGBridgeObstruction.VolumeUniformCoarseInfluenceFamily,
      1 / 18 ≤ (fam.contract 1).β_next := by
  rintro ⟨fam, h⟩
  have h' := volumeUniformFamily_coupling_lt fam 1
  linarith

/-- False strengthening: a unified blocking model at zero bare coupling has positive extracted
coupling. -/
theorem zero_coupling_model_positive_coupling_rejected :
    ¬ ∃ M : YangMillsPhysicalBridges.UnifiedPhysicalWilsonBlockingModel 2,
      M.β_uv = 0 ∧ 0 < M.influence.β_next := by
  rintro ⟨M, h0, hpos⟩
  rw [(unifiedModel_degenerate_of_zero_coupling M h0).1] at hpos
  exact lt_irrefl 0 hpos

/-- Positive form with the needed coupling growth: along the canonical geometry the explicit
schedule `β_n = (8 L_n⁴ log (2400 L_n⁴ / δ) + n) / (ε - δ)` concentrates the total action. -/
example : Tendsto (pathTail (haarSchedulePath canonicalCutoffPath.toFixedVolumeGeometry
    (ε := 1) (δ := 1 / 2) (by norm_num) (by norm_num) (by norm_num)) 1) atTop (𝓝 0) :=
  (haarSchedulePath_tail_tendsto_zero _ _ _ _).1

/-- Positive form at weak coupling: on the `2⁴` torus the unified blocking model is inhabited on
the actual Haar disintegration by models with positive extracted coupling above a threshold. -/
example : ∃ βthr : ℝ, 0 ≤ βthr ∧ ∀ β : ℝ, βthr < β →
    ∃ M : YangMillsPhysicalBridges.UnifiedPhysicalWilsonBlockingModel 2,
      M.dis = haarBlockDisintegration 2 ∧ M.β_uv = β ∧ 0 < M.influence.β_next ∧
      ∃ V : GaugeConfig 2, M.influence.β_next * wilsonAction 1 V + M.influence.K_next V ≠ 0 :=
  exists_nondegenerate_haarModel 2 le_rfl

#assert_zfc_axioms

end JesseMath.Physics.YangMillsWeakCouplingNecessityNegativeControl
