import JesseMath.Physics.YangMillsPhysicalGap

/-! Operator-level positive and negative controls. These are models for the
abstract bridge, not a Wilson transfer construction. -/

noncomputable section

namespace JesseMath.Physics.YangMillsPhysicalGapTest

open JesseMath.Physics.YangMillsPhysicalGap Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def modelEvolution (Ω : H) (m t : ℝ) : H →L[ℂ] H :=
  InnerProductSpace.rankOne ℂ Ω Ω + (Real.exp (-m * t) : ℂ) •
    (ContinuousLinearMap.id ℂ H - InnerProductSpace.rankOne ℂ Ω Ω)

theorem modelEvolution_apply (Ω u : H) (m t : ℝ) :
    modelEvolution Ω m t u = vacuumPart Ω u +
      (Real.exp (-m * t) : ℂ) • excitedPart Ω u := by
  rfl

theorem modelEvolution_zero (Ω u : H) (m : ℝ) : modelEvolution Ω m 0 u = u := by
  simp [modelEvolution_apply, excitedPart]

theorem modelEvolution_fixes_vacuum {Ω : H} (hΩ : ‖Ω‖ = 1) (m t : ℝ) :
    modelEvolution Ω m t Ω = Ω := by
  simp [modelEvolution_apply, excitedPart, vacuumPart_self hΩ]

theorem modelEvolution_excited {Ω : H} (hΩ : ‖Ω‖ = 1) (m t : ℝ) (u : H) :
    modelEvolution Ω m t (excitedPart Ω u) =
      (Real.exp (-m * t) : ℂ) • excitedPart Ω u := by
  have hp : vacuumPart Ω (excitedPart Ω u) = 0 := by
    simp [vacuumPart, excitedPart_orthogonal hΩ]
  rw [modelEvolution_apply, hp, excitedPart, hp, sub_zero, zero_add]

theorem modelEvolution_decay {Ω : H} (hΩ : ‖Ω‖ = 1) (m t : ℝ) (u : H) :
    ‖modelEvolution Ω m t (excitedPart Ω u)‖ =
      Real.exp (-m * t) * ‖excitedPart Ω u‖ := by
  rw [modelEvolution_excited hΩ, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem modelEvolution_semigroup {Ω : H} (hΩ : ‖Ω‖ = 1) (m t s : ℝ) (u : H) :
    modelEvolution Ω m (t + s) u = modelEvolution Ω m t (modelEvolution Ω m s u) := by
  have hp : modelEvolution Ω m t (vacuumPart Ω u) = vacuumPart Ω u := by
    simp [vacuumPart, map_smul, modelEvolution_fixes_vacuum hΩ]
  rw [modelEvolution_apply Ω u m (t + s), modelEvolution_apply Ω u m s,
    map_add, map_smul, hp, modelEvolution_excited hΩ]
  congr 1
  rw [← mul_smul, mul_add, Real.exp_add, Complex.ofReal_mul]
  congr 1
  ring

theorem modelEvolution_generator (Ω u : H) (m : ℝ) :
    HasDerivWithinAt (fun t : ℝ => modelEvolution Ω m t u)
      (-((m : ℂ) • excitedPart Ω u)) (Set.Ioi 0) 0 := by
  have he := ((hasDerivAt_id (0 : ℝ)).const_mul (-m)).exp.ofReal_comp
  have h := (he.smul_const (excitedPart Ω u)).const_add (vacuumPart Ω u)
  simpa [modelEvolution_apply] using h.hasDerivWithinAt

/-- All cutoff hypotheses are inhabited by a genuine continuous semigroup with
zero-energy vacuum and a nontrivial excited sector. Constant cutoff sequences
are sufficient here: this control checks the full composed contract. -/
theorem model_satisfies_composed_bridge {Ω : H} (hΩ : ‖Ω‖ = 1) (m : ℝ) :
    ∀ u : (⊤ : Submodule ℂ H), ⟪Ω, (u : H)⟫_ℂ = 0 →
      m * ‖(u : H)‖ ^ 2 ≤ (⟪(u : H), (m : ℂ) • excitedPart Ω u⟫_ℂ).re := by
  let generator : (⊤ : Submodule ℂ H) →ₗ[ℂ] H :=
    ((m : ℂ) • (ContinuousLinearMap.id ℂ H - InnerProductSpace.rankOne ℂ Ω Ω)).toLinearMap.comp
      (Submodule.subtype ⊤)
  have hg : ∀ u : (⊤ : Submodule ℂ H), generator u = (m : ℂ) • excitedPart Ω u := by
    intro u
    rfl
  have h := physical_generator_bound_of_cutoff_decay Set.univ (by simp)
    (fun _ => modelEvolution Ω m) (modelEvolution Ω m) (fun _ => Ω) Ω m
    ⊤ generator tendsto_const_nhds (fun _ => hΩ)
    (fun _ t _ => modelEvolution_fixes_vacuum hΩ m t)
    (fun _ _ _ _ => tendsto_const_nhds)
    (fun _ t _ u _ => (modelEvolution_decay hΩ m t u).le)
    (fun u => modelEvolution_zero Ω u m)
    (fun u => by rw [hg]; exact modelEvolution_generator Ω u m)
  simpa only [hg] using h.2

abbrev TwoModes := EuclideanSpace ℂ (Fin 2)

def vacuum : TwoModes := EuclideanSpace.single 0 1

def hidden : TwoModes := EuclideanSpace.single 1 1

theorem vacuum_norm : ‖vacuum‖ = 1 := by simp [vacuum]

theorem hidden_norm : ‖hidden‖ = 1 := by simp [hidden]

theorem hidden_orthogonal : ⟪vacuum, hidden⟫_ℂ = 0 := by
  simp [vacuum, hidden, EuclideanSpace.inner_single_left ]

theorem positive_model_has_an_excitation :
    modelEvolution vacuum 1 1 hidden = (Real.exp (-1) : ℂ) • hidden ∧
      ‖hidden‖ = 1 := by
  constructor
  · simp [modelEvolution_apply, excitedPart, vacuumPart, hidden_orthogonal]
  · exact hidden_norm

def observedSector : Set TwoModes := Set.range fun z : ℂ => z • vacuum

/-- Identity evolution passes an arbitrary positive decay target on the
observed vacuum sector. The sector has no information about its hidden mode. -/
theorem nondense_sector_passes_decay (m t : ℝ) :
    ∀ u ∈ observedSector,
      ‖(ContinuousLinearMap.id ℂ TwoModes) (excitedPart vacuum u)‖ ≤
        Real.exp (-m * t) * ‖excitedPart vacuum u‖ := by
  rintro _ ⟨z, rfl⟩
  have hp : vacuumPart vacuum (z • vacuum) = z • vacuum := by
    simp [vacuumPart, inner_self_eq_norm_sq_to_K, vacuum_norm]
  simp [excitedPart, hp]

/-- The omitted sector contains an actual nondecaying unit vector, so the
whole-space positive-rate conclusion is false. -/
theorem hidden_mode_rejects_decay :
    ¬ (‖(ContinuousLinearMap.id ℂ TwoModes) hidden‖ ≤ Real.exp (-1) * ‖hidden‖) := by
  simp only [ContinuousLinearMap.id_apply, hidden_norm, mul_one, not_le]
  exact Real.exp_lt_one_iff.mpr (by norm_num)

theorem observedSector_not_dense : ¬ Dense observedSector := by
  intro hd
  have h := dense_core_decay_limit_with_vacuum observedSector hd
    (fun _ => ContinuousLinearMap.id ℂ TwoModes) (ContinuousLinearMap.id ℂ TwoModes)
    (fun _ => vacuum) vacuum (Real.exp (-1)) tendsto_const_nhds
    (fun _ => vacuum_norm) (fun _ => rfl) (fun _ _ => tendsto_const_nhds)
    (fun _ u hu => by simpa using nondense_sector_passes_decay 1 1 u hu)
  exact hidden_mode_rejects_decay (h.2 hidden hidden_orthogonal)

end JesseMath.Physics.YangMillsPhysicalGapTest

#assert_zfc_axioms
