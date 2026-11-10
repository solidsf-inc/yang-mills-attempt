import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.LatticeYangMills
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Exact fine-link geometry for dyadic Wilson blocking

The two fine links assigned to each coarse link are distinct, and links assigned
to different coarse links never overlap. The complement equivalence accounts for
every remaining fine link. These are finite indexing statements; no measure or
renormalization estimate is assumed.
-/

namespace JesseMath.Physics.YangMillsBlockGeometry

/-- The first (`b = 0`) or second (`b = 1`) fine edge of a coarse link. -/
def dyadicFineLink (L : ℕ) (p : Link L × Fin 2) : Link (2 * L) where
  x := fun i => ((2 * (p.1.x i).val + if i = p.1.μ then p.2.val else 0 : ℕ) : ZMod (2 * L))
  μ := p.1.μ

@[simp] theorem dyadicFineLink_zero (L : ℕ) (e : Link L) :
    dyadicFineLink L (e, 0) =
      ⟨(fun i => ((2 * (e.x i).val : ℕ) : ZMod (2 * L))), e.μ⟩ := by
  simp [dyadicFineLink]

@[simp] theorem dyadicFineLink_one (L : ℕ) (e : Link L) :
    dyadicFineLink L (e, 1) =
      ⟨shift (fun i => ((2 * (e.x i).val : ℕ) : ZMod (2 * L))) e.μ, e.μ⟩ := by
  unfold dyadicFineLink
  congr 1
  funext i
  simp only [shift, Pi.add_apply, unitVec]
  split_ifs <;> simp

private theorem dyadicFineLink_coordinate_lt {L : ℕ} [NeZero L]
    (e : Link L) (b : Fin 2) (i : Fin 4) :
    2 * (e.x i).val + (if i = e.μ then b.val else 0) < 2 * L := by
  have hx := (e.x i).val_lt
  have hb := b.isLt
  split_ifs <;> omega

theorem dyadicFineLink_injective (L : ℕ) [NeZero L] :
    Function.Injective (dyadicFineLink L) := by
  rintro ⟨⟨x, μ⟩, s⟩ ⟨⟨y, ν⟩, t⟩ h
  have hμ : μ = ν := congrArg Link.μ h
  subst ν
  have hcoord (i : Fin 4) :
      2 * (x i).val + (if i = μ then s.val else 0) =
        2 * (y i).val + (if i = μ then t.val else 0) := by
    have hi := congrArg (fun e : Link (2 * L) => (e.x i).val) h
    simpa only [dyadicFineLink,
      ZMod.val_natCast_of_lt (dyadicFineLink_coordinate_lt ⟨x, μ⟩ s i),
      ZMod.val_natCast_of_lt (dyadicFineLink_coordinate_lt ⟨y, μ⟩ t i)] using hi
  have hs : s = t := by
    apply Fin.ext
    have hi := hcoord μ
    simp only [ite_true] at hi
    have hslt := s.isLt
    have htlt := t.isLt
    omega
  subst t
  have hxy : x = y := by
    funext i
    apply ZMod.val_injective L
    have hi := hcoord i
    omega
  subst y
  rfl

/-- Fine links not used in any coarse-link pair. -/
def unusedFineLinks (L : ℕ) := {e : Link (2 * L) // e ∉ Set.range (dyadicFineLink L)}

noncomputable instance (L : ℕ) [NeZero L] : Fintype (unusedFineLinks L) := by
  classical
  unfold unusedFineLinks
  infer_instance

/-- All fine links are either one of the disjoint pairs or an unused link. -/
noncomputable def dyadicFineLinkEquiv (L : ℕ) [NeZero L] :
    ((Link L × Fin 2) ⊕ unusedFineLinks L) ≃ Link (2 * L) := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective (dyadicFineLink L)
    (dyadicFineLink_injective L)) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range (dyadicFineLink L)))

@[simp] theorem dyadicFineLinkEquiv_inl (L : ℕ) [NeZero L] (p : Link L × Fin 2) :
    dyadicFineLinkEquiv L (Sum.inl p) = dyadicFineLink L p := rfl

@[simp] theorem dyadicFineLinkEquiv_inr (L : ℕ) [NeZero L] (e : unusedFineLinks L) :
    dyadicFineLinkEquiv L (Sum.inr e) = e.val := rfl

/-- A fine configuration is exactly its first links, second links and unused links. -/
noncomputable def dyadicConfigEquiv (L : ℕ) [NeZero L] (G : Type*) :
    (Link (2 * L) → G) ≃
      (((Link L → G) × (Link L → G)) × (unusedFineLinks L → G)) :=
  ((Equiv.arrowCongr (dyadicFineLinkEquiv L).symm (Equiv.refl G)).trans
    (Equiv.sumArrowEquivProdArrow (Link L × Fin 2) (unusedFineLinks L) G)).trans
    (Equiv.prodCongr
      (((Equiv.curry (Link L) (Fin 2) G).trans
        (Equiv.piCongrRight fun _ : Link L => finTwoArrowEquiv G)).trans
        (Equiv.arrowProdEquivProdArrow (Link L) (fun _ => G) (fun _ => G)))
      (Equiv.refl _))

@[simp] theorem dyadicConfigEquiv_first (L : ℕ) [NeZero L] {G : Type*}
    (U : Link (2 * L) → G) (e : Link L) :
    (dyadicConfigEquiv L G U).1.1 e = U (dyadicFineLink L (e, 0)) := rfl

@[simp] theorem dyadicConfigEquiv_second (L : ℕ) [NeZero L] {G : Type*}
    (U : Link (2 * L) → G) (e : Link L) :
    (dyadicConfigEquiv L G U).1.2 e = U (dyadicFineLink L (e, 1)) := rfl

@[simp] theorem dyadicConfigEquiv_unused (L : ℕ) [NeZero L] {G : Type*}
    (U : Link (2 * L) → G) (e : unusedFineLinks L) :
    (dyadicConfigEquiv L G U).2 e = U e.val := rfl

@[simp] theorem dyadicConfigEquiv_symm_first (L : ℕ) [NeZero L] {G : Type*}
    (p : ((Link L → G) × (Link L → G)) × (unusedFineLinks L → G)) (e : Link L) :
    (dyadicConfigEquiv L G).symm p (dyadicFineLink L (e, 0)) = p.1.1 e :=
  congrArg (fun q => q.1.1 e) ((dyadicConfigEquiv L G).apply_symm_apply p)

@[simp] theorem dyadicConfigEquiv_symm_second (L : ℕ) [NeZero L] {G : Type*}
    (p : ((Link L → G) × (Link L → G)) × (unusedFineLinks L → G)) (e : Link L) :
    (dyadicConfigEquiv L G).symm p (dyadicFineLink L (e, 1)) = p.1.2 e :=
  congrArg (fun q => q.1.2 e) ((dyadicConfigEquiv L G).apply_symm_apply p)

@[simp] theorem dyadicConfigEquiv_symm_unused (L : ℕ) [NeZero L] {G : Type*}
    (p : ((Link L → G) × (Link L → G)) × (unusedFineLinks L → G)) (e : unusedFineLinks L) :
    (dyadicConfigEquiv L G).symm p e.val = p.2 e :=
  congrArg (fun q => q.2 e) ((dyadicConfigEquiv L G).apply_symm_apply p)

theorem measurable_dyadicConfigEquiv (L : ℕ) [NeZero L] (G : Type*) [MeasurableSpace G] :
    Measurable (dyadicConfigEquiv L G) :=
  ((measurable_pi_iff.2 fun _ => measurable_pi_apply _).prodMk
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _)).prodMk
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _)

theorem measurable_dyadicConfigEquiv_symm (L : ℕ) [NeZero L]
    (G : Type*) [MeasurableSpace G] :
    Measurable (dyadicConfigEquiv L G).symm := by
  apply measurable_pi_iff.2
  intro e
  obtain ⟨i, rfl⟩ := (dyadicFineLinkEquiv L).surjective e
  rcases i with ⟨j, b⟩ | j
  · fin_cases b
    · have hm : Measurable
          (fun p : ((Link L → G) × (Link L → G)) × (unusedFineLinks L → G) => p.1.1 j) :=
        (measurable_pi_apply j).comp measurable_fst.fst
      convert hm using 1
      funext p
      exact dyadicConfigEquiv_symm_first L p j
    · have hm : Measurable
          (fun p : ((Link L → G) × (Link L → G)) × (unusedFineLinks L → G) => p.1.2 j) :=
        (measurable_pi_apply j).comp measurable_fst.snd
      convert hm using 1
      funext p
      exact dyadicConfigEquiv_symm_second L p j
  · simp only [dyadicFineLinkEquiv_inr, dyadicConfigEquiv_symm_unused]
    exact (measurable_pi_apply j).comp measurable_snd

/-- The configuration split preserves the product measurable structures. -/
noncomputable def dyadicConfigMeasurableEquiv (L : ℕ) [NeZero L]
    (G : Type*) [MeasurableSpace G] :
    (Link (2 * L) → G) ≃ᵐ
      (((Link L → G) × (Link L → G)) × (unusedFineLinks L → G)) where
  toEquiv := dyadicConfigEquiv L G
  measurable_toFun := measurable_dyadicConfigEquiv L G
  measurable_invFun := measurable_dyadicConfigEquiv_symm L G

/-- Fine-lattice midpoint vertex of a coarse link `e : Link L`, given by the base vertex of the
second fine edge `dyadicFineLink L (e, 1)`. -/
def dyadicMidpointVertex (L : ℕ) (e : Link L) : Lattice4D (2 * L) :=
  (dyadicFineLink L (e, 1)).x

/-- Every fine link emanating from the midpoint vertex `dyadicMidpointVertex L e` in a direction
`ν ≠ e.μ` transverse to `e.μ` has odd `e.μ`-coordinate `2 * (e.x e.μ).val + 1`, and therefore
never belongs to `Set.range (dyadicFineLink L)`. -/
theorem dyadicMidpointTransverseLink_not_mem_range (L : ℕ) [NeZero L]
    (e : Link L) (ν : Fin 4) (hν : ν ≠ e.μ) :
    (⟨dyadicMidpointVertex L e, ν⟩ : Link (2 * L)) ∉ Set.range (dyadicFineLink L) := by
  rintro ⟨⟨p, b⟩, h⟩
  have hμ : p.μ = ν := congrArg Link.μ h
  have hne : e.μ ≠ p.μ := by
    rw [hμ]
    exact hν.symm
  have hi := congrArg (fun f : Link (2 * L) => (f.x e.μ).val) h
  dsimp [dyadicMidpointVertex, dyadicFineLink] at hi
  simp only [hne, ↓reduceIte] at hi
  have hlt_p : 2 * (p.x e.μ).val + 0 < 2 * L := by
    have := (p.x e.μ).val_lt
    omega
  have hlt_e : 2 * (e.x e.μ).val + 1 < 2 * L := by
    have := (e.x e.μ).val_lt
    omega
  rw [ZMod.val_natCast_of_lt hlt_p, ZMod.val_natCast_of_lt hlt_e] at hi
  omega

/-- Canonical embedding of each transverse fine link at the midpoint vertex
`dyadicMidpointVertex L e` (`ν ≠ e.μ`) into the independent Haar fiber coordinates
`unusedFineLinks L`. -/
def dyadicMidpointTransverseUnusedLink (L : ℕ) [NeZero L]
    (e : Link L) (ν : Fin 4) (hν : ν ≠ e.μ) : unusedFineLinks L :=
  ⟨⟨dyadicMidpointVertex L e, ν⟩, dyadicMidpointTransverseLink_not_mem_range L e ν hν⟩

end JesseMath.Physics.YangMillsBlockGeometry

#assert_zfc_axioms
