import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.LatticeYangMills
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# The flat forest-slice curl form

Fine lattice `(ℤ/2L)⁴`, site `2n + s` with `s ∈ {0,1}⁴`. A link `(x, μ)` is a tree link when `s μ = 0`
and `s ν = 0` for every `ν < μ`, a selected second link when `s = e_μ`, and free otherwise, which
leaves 45 free links per cell. Functions on free links, extended by zero, carry the quadratic form
`Q(a) = ∑_p (curl a p)²`, whose matrix is `forestHessian L`.

Proved for every `L`: the matrix is symmetric, it represents the form, its entries vanish off the
conflict graph, and `Q(a) ≤ 24 ∑ a²`. The lower bound is in `YangMillsForestSliceHessian`.

Scope: flat background `W = I`, fine lattice spacing 1, no spacing factors, the quadratic curl form
only. It does not prove that this form is the second derivative of the SU(2) Wilson action.
-/

open JesseMath.Physics
open BigOperators

namespace JesseMath.Physics.YangMillsForestSliceHessian

/-! ## Links and the slice -/

/-- A parity vector `s ∈ {0,1}⁴`. -/
abbrev Cell := Fin 4 → Fin 2

/-- Parity of a coordinate; the modulus `2L` is even, so this is well defined. -/
def parityBit {L : ℕ} (z : ZMod (2 * L)) : Fin 2 :=
  ⟨z.val % 2, Nat.mod_lt _ (by norm_num)⟩

/-- The parity vector of a site. -/
def parityVec {L : ℕ} (x : Lattice4D (2 * L)) : Cell := fun i => parityBit (x i)

/-- Tree class: `s μ = 0` and `s ν = 0` for every `ν < μ`. -/
def IsTreeClass (s : Cell) (μ : Direction) : Prop := s μ = 0 ∧ ∀ ν, ν < μ → s ν = 0

/-- Selected class: `s = e_μ`. -/
def IsSelectedClass (s : Cell) (μ : Direction) : Prop := s μ = 1 ∧ ∀ ν, ν ≠ μ → s ν = 0

/-- Free class: neither tree nor selected. -/
def IsFreeClass (s : Cell) (μ : Direction) : Prop := ¬ IsTreeClass s μ ∧ ¬ IsSelectedClass s μ

instance (s : Cell) (μ : Direction) : Decidable (IsTreeClass s μ) := by
  unfold IsTreeClass; infer_instance
instance (s : Cell) (μ : Direction) : Decidable (IsSelectedClass s μ) := by
  unfold IsSelectedClass; infer_instance
instance (s : Cell) (μ : Direction) : Decidable (IsFreeClass s μ) := by
  unfold IsFreeClass; infer_instance

/-- Tree link of the first-odd-coordinate forest. -/
def IsTreeLink {L : ℕ} (e : Link (2 * L)) : Prop := IsTreeClass (parityVec e.x) e.μ

/-- Selected second link. -/
def IsSelectedLink {L : ℕ} (e : Link (2 * L)) : Prop := IsSelectedClass (parityVec e.x) e.μ

/-- Free link: neither tree nor selected. -/
def IsFreeLink {L : ℕ} (e : Link (2 * L)) : Prop := ¬ IsTreeLink e ∧ ¬ IsSelectedLink e

instance {L : ℕ} (e : Link (2 * L)) : Decidable (IsTreeLink e) := by
  unfold IsTreeLink; infer_instance
instance {L : ℕ} (e : Link (2 * L)) : Decidable (IsSelectedLink e) := by
  unfold IsSelectedLink; infer_instance
instance {L : ℕ} (e : Link (2 * L)) : Decidable (IsFreeLink e) := by
  unfold IsFreeLink; infer_instance

/-- The free links of the fine lattice. -/
abbrev FreeLink (L : ℕ) := { e : Link (2 * L) // IsFreeLink e }

/-- Extension of a slice function by zero to tree and selected links. -/
def extendByZero {L : ℕ} (a : FreeLink L → ℝ) (e : Link (2 * L)) : ℝ :=
  if h : IsFreeLink e then a ⟨e, h⟩ else 0

/-- Lattice curl on a plaquette `(x, μ, ν)`. -/
def latticeCurl {L : ℕ} (a : Link (2 * L) → ℝ) (p : Plaquette (2 * L)) : ℝ :=
  a ⟨p.x, p.μ⟩ + a ⟨shift p.x p.μ, p.ν⟩ - a ⟨shift p.x p.ν, p.μ⟩ - a ⟨p.x, p.ν⟩

/-- The coefficient `c_p(e)`: the curl of the indicator of `e`. -/
def plaquetteCoeff {L : ℕ} (p : Plaquette (2 * L)) (e : FreeLink L) : ℝ :=
  latticeCurl (extendByZero (Pi.single e 1)) p

section Finite

variable (L : ℕ) [NeZero L]

/-- The quadratic form `Q(a) = ∑_p (curl (ext a) p)²`. -/
noncomputable def forestForm (a : FreeLink L → ℝ) : ℝ :=
  ∑ p : Plaquette (2 * L), latticeCurl (extendByZero a) p ^ 2

/-- The Hessian `H e f = ∑_p c_p(e) c_p(f)`. -/
noncomputable def forestHessian : Matrix (FreeLink L) (FreeLink L) ℝ :=
  Matrix.of fun e f => ∑ p : Plaquette (2 * L), plaquetteCoeff p e * plaquetteCoeff p f

/-- Two distinct free links conflict when some plaquette contains both. -/
def conflictGraph : SimpleGraph (FreeLink L) where
  Adj e f := e ≠ f ∧ ∃ p : Plaquette (2 * L), plaquetteCoeff p e ≠ 0 ∧ plaquetteCoeff p f ≠ 0
  symm := ⟨fun _ _ h => ⟨h.1.symm, by
    obtain ⟨p, h1, h2⟩ := h.2
    exact ⟨p, h2, h1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end Finite

/-! ## Symmetry, the quadratic form, locality -/

section Basic

variable {L : ℕ} [NeZero L]

theorem forestHessian_isSymm : (forestHessian L).IsSymm := by
  ext e f
  simp [forestHessian, Matrix.transpose_apply, mul_comm]

theorem extendByZero_eq_sum (a : FreeLink L → ℝ) (ℓ : Link (2 * L)) :
    extendByZero a ℓ = ∑ e, a e * extendByZero (Pi.single e 1) ℓ := by
  unfold extendByZero
  by_cases h : IsFreeLink ℓ
  · simp only [h, dite_true]
    rw [Finset.sum_eq_single (⟨ℓ, h⟩ : FreeLink L)]
    · simp
    · intro e _ he
      simp [Ne.symm he]
    · simp
  · simp [h]

theorem latticeCurl_extend_eq_sum (a : FreeLink L → ℝ) (p : Plaquette (2 * L)) :
    latticeCurl (extendByZero a) p = ∑ e, a e * plaquetteCoeff p e := by
  unfold plaquetteCoeff latticeCurl
  rw [extendByZero_eq_sum a ⟨p.x, p.μ⟩, extendByZero_eq_sum a ⟨shift p.x p.μ, p.ν⟩,
    extendByZero_eq_sum a ⟨shift p.x p.ν, p.μ⟩, extendByZero_eq_sum a ⟨p.x, p.ν⟩]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem forestHessian_quadratic (a : FreeLink L → ℝ) :
    ∑ e, ∑ f, a e * forestHessian L e f * a f = forestForm L a := by
  unfold forestForm
  simp only [latticeCurl_extend_eq_sum, sq, Finset.sum_mul_sum]
  calc ∑ e, ∑ f, a e * forestHessian L e f * a f
      = ∑ e, ∑ f, ∑ p : Plaquette (2 * L),
          a e * plaquetteCoeff p e * (a f * plaquetteCoeff p f) := by
        refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
        simp only [forestHessian, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ = ∑ e, ∑ p : Plaquette (2 * L), ∑ f,
          a e * plaquetteCoeff p e * (a f * plaquetteCoeff p f) :=
        Finset.sum_congr rfl fun e _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem forestHessian_local {e f : FreeLink L} (h : forestHessian L e f ≠ 0) :
    e = f ∨ (conflictGraph L).Adj e f := by
  by_cases hef : e = f
  · exact Or.inl hef
  · refine Or.inr ⟨hef, ?_⟩
    obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact ⟨p, left_ne_zero_of_mul hp, right_ne_zero_of_mul hp⟩

end Basic

/-! ## Reindexing and the upper bound -/

section Reindex

variable {L : ℕ} [NeZero L]

theorem sum_link (g : Link (2 * L) → ℝ) :
    ∑ ℓ, g ℓ = ∑ x : Lattice4D (2 * L), ∑ μ : Direction, g ⟨x, μ⟩ := by
  rw [← Fintype.sum_prod_type' (f := fun (x : Lattice4D (2 * L)) (μ : Direction) => g ⟨x, μ⟩)]
  exact (linkEquiv (2 * L)).sum_comp (fun q => g ⟨q.1, q.2⟩)

theorem sum_plaquette (g : Plaquette (2 * L) → ℝ) :
    ∑ p, g p = ∑ x : Lattice4D (2 * L), ∑ P : PlaquettePlane, g ⟨x, P.1.1, P.1.2, P.2⟩ := by
  rw [← Fintype.sum_prod_type'
    (f := fun (x : Lattice4D (2 * L)) (P : PlaquettePlane) => g ⟨x, P.1.1, P.1.2, P.2⟩)]
  exact (plaqEquiv (2 * L)).sum_comp (fun q => g ⟨q.1, q.2.1.1, q.2.1.2, q.2.2⟩)

theorem sum_free_sq (a : FreeLink L → ℝ) :
    ∑ e, a e ^ 2 = ∑ ℓ, extendByZero a ℓ ^ 2 := by
  have hne : ∀ ℓ ∈ (Finset.univ : Finset (Link (2 * L))),
      extendByZero a ℓ ^ 2 ≠ 0 → IsFreeLink ℓ := by
    intro ℓ _ h
    by_contra hf
    exact h (by simp [extendByZero, hf])
  rw [← Finset.sum_filter_of_ne hne,
    Finset.sum_subtype (Finset.univ.filter IsFreeLink) (p := IsFreeLink) (by simp)
      (fun ℓ => extendByZero a ℓ ^ 2)]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [extendByZero, e.2]

theorem sum_shift (g : Lattice4D (2 * L) → ℝ) (μ : Direction) :
    ∑ x, g (shift x μ) = ∑ x, g x :=
  Equiv.sum_comp (Equiv.addRight (unitVec (2 * L) μ)) g

end Reindex

/-- Coordinate plane (0, 1). -/
def p01 : PlaquettePlane := ⟨(0, 1), by decide⟩
/-- Coordinate plane (0, 2). -/
def p02 : PlaquettePlane := ⟨(0, 2), by decide⟩
/-- Coordinate plane (0, 3). -/
def p03 : PlaquettePlane := ⟨(0, 3), by decide⟩
/-- Coordinate plane (1, 2). -/
def p12 : PlaquettePlane := ⟨(1, 2), by decide⟩
/-- Coordinate plane (1, 3). -/
def p13 : PlaquettePlane := ⟨(1, 3), by decide⟩
/-- Coordinate plane (2, 3). -/
def p23 : PlaquettePlane := ⟨(2, 3), by decide⟩

theorem sum_plane (f : PlaquettePlane → ℝ) :
    ∑ P, f P = f p01 + f p02 + f p03 + f p12 + f p13 + f p23 := by
  have h : (Finset.univ : Finset PlaquettePlane) = {p01, p02, p03, p12, p13, p23} := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem forestSlice_upper {L : ℕ} [NeZero L] (a : FreeLink L → ℝ) :
    forestForm L a ≤ 24 * ∑ e, a e ^ 2 := by
  set b := extendByZero a with hb
  let D : Direction → ℝ := fun μ => ∑ x : Lattice4D (2 * L), b ⟨x, μ⟩ ^ 2
  have hplane : ∀ P : PlaquettePlane,
      ∑ x : Lattice4D (2 * L), latticeCurl b ⟨x, P.1.1, P.1.2, P.2⟩ ^ 2
        ≤ 8 * D P.1.1 + 8 * D P.1.2 := by
    intro P
    have hμ : ∑ x : Lattice4D (2 * L), b ⟨shift x P.1.1, P.1.2⟩ ^ 2 = D P.1.2 :=
      sum_shift (fun x => b ⟨x, P.1.2⟩ ^ 2) P.1.1
    have hν : ∑ x : Lattice4D (2 * L), b ⟨shift x P.1.2, P.1.1⟩ ^ 2 = D P.1.1 :=
      sum_shift (fun x => b ⟨x, P.1.1⟩ ^ 2) P.1.2
    calc ∑ x : Lattice4D (2 * L), latticeCurl b ⟨x, P.1.1, P.1.2, P.2⟩ ^ 2
        ≤ ∑ x : Lattice4D (2 * L), (4 * b ⟨x, P.1.1⟩ ^ 2 + 4 * b ⟨shift x P.1.1, P.1.2⟩ ^ 2
            + 4 * b ⟨shift x P.1.2, P.1.1⟩ ^ 2 + 4 * b ⟨x, P.1.2⟩ ^ 2) := by
          refine Finset.sum_le_sum fun x _ => ?_
          simp only [latticeCurl]
          nlinarith [sq_nonneg (b ⟨x, P.1.1⟩ - b ⟨shift x P.1.1, P.1.2⟩),
            sq_nonneg (b ⟨x, P.1.1⟩ + b ⟨shift x P.1.2, P.1.1⟩),
            sq_nonneg (b ⟨x, P.1.1⟩ + b ⟨x, P.1.2⟩),
            sq_nonneg (b ⟨shift x P.1.1, P.1.2⟩ + b ⟨shift x P.1.2, P.1.1⟩),
            sq_nonneg (b ⟨shift x P.1.1, P.1.2⟩ + b ⟨x, P.1.2⟩),
            sq_nonneg (b ⟨shift x P.1.2, P.1.1⟩ - b ⟨x, P.1.2⟩)]
      _ = 8 * D P.1.1 + 8 * D P.1.2 := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hμ, hν]
          change 4 * D P.1.1 + 4 * D P.1.2 + 4 * D P.1.1 + 4 * D P.1.2 = _
          ring
  calc forestForm L a
      = ∑ P : PlaquettePlane, ∑ x : Lattice4D (2 * L),
          latticeCurl b ⟨x, P.1.1, P.1.2, P.2⟩ ^ 2 := by
        rw [forestForm, sum_plaquette, Finset.sum_comm]
    _ ≤ ∑ P : PlaquettePlane, (8 * D P.1.1 + 8 * D P.1.2) :=
        Finset.sum_le_sum fun P _ => hplane P
    _ = 24 * ∑ μ, D μ := by
        rw [sum_plane, Fin.sum_univ_four]
        simp only [p01, p02, p03, p12, p13, p23]
        ring
    _ = 24 * ∑ e, a e ^ 2 := by
        rw [sum_free_sq, sum_link, Finset.sum_comm]

/-! ## Sites as coarse point plus offset -/

section Site

variable {L : ℕ}

/-- The fine site `2n + t`. -/
def site (n : Fin 4 → ZMod L) (t : Fin 4 → ℕ) : Lattice4D (2 * L) :=
  fun i => ((2 * (n i).val + t i : ℕ) : ZMod (2 * L))

theorem shift_site (n : Fin 4 → ZMod L) (t : Fin 4 → ℕ) (α : Direction) :
    shift (site n t) α = site n (fun i => t i + if i = α then 1 else 0) := by
  funext i
  simp only [shift, site, Pi.add_apply, unitVec]
  split_ifs <;> simp [add_assoc]

theorem parityVec_site (n : Fin 4 → ZMod L) (t : Fin 4 → ℕ) :
    parityVec (site n t) = fun i => ⟨t i % 2, Nat.mod_lt _ (by norm_num)⟩ := by
  funext i
  apply Fin.ext
  simp only [parityVec, parityBit, site, ZMod.val_natCast]
  rw [Nat.mod_mod_of_dvd _ (Dvd.intro L rfl), Nat.mul_add_mod]

theorem site_injective [NeZero L] :
    Function.Injective
      (fun q : (Fin 4 → ZMod L) × Cell => site q.1 (fun i => (q.2 i).val)) := by
  rintro ⟨n, s⟩ ⟨n', s'⟩ h
  have key : ∀ i, 2 * (n i).val + (s i).val = 2 * (n' i).val + (s' i).val := by
    intro i
    have hi := congrFun h i
    simp only [site] at hi
    have lt1 : 2 * (n i).val + (s i).val < 2 * L := by
      have := ZMod.val_lt (n i); have := (s i).isLt; omega
    have lt2 : 2 * (n' i).val + (s' i).val < 2 * L := by
      have := ZMod.val_lt (n' i); have := (s' i).isLt; omega
    have := congrArg ZMod.val hi
    rwa [ZMod.val_natCast_of_lt lt1, ZMod.val_natCast_of_lt lt2] at this
  have hn : n = n' := by
    funext i
    apply ZMod.val_injective L
    have := key i; have := (s i).isLt; have := (s' i).isLt; omega
  have hs : s = s' := by
    funext i
    apply Fin.ext
    have := key i; have := (s i).isLt; have := (s' i).isLt; omega
  rw [hn, hs]

theorem site_bijective [NeZero L] :
    Function.Bijective
      (fun q : (Fin 4 → ZMod L) × Cell => site q.1 (fun i => (q.2 i).val)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨site_injective, ?_⟩
  simp only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  ring

theorem sum_site [NeZero L] (g : Lattice4D (2 * L) → ℝ) :
    ∑ x, g x = ∑ n : Fin 4 → ZMod L, ∑ s : Cell, g (site n (fun i => (s i).val)) := by
  rw [← Fintype.sum_prod_type'
    (f := fun (n : Fin 4 → ZMod L) (s : Cell) => g (site n (fun i => (s i).val)))]
  exact ((Equiv.ofBijective _ site_bijective).sum_comp g).symm

end Site

/-! ## Local keys and the local curl -/

/-- An offset in `ℕ⁴`, as a tuple so that the kernel compares it quickly. -/
abbrev Off := ℕ × ℕ × ℕ × ℕ

/-- An offset as a function. -/
def off (t : Off) : Fin 4 → ℕ := ![t.1, t.2.1, t.2.2.1, t.2.2.2]

/-- A parity vector as an offset. -/
def up (s : Cell) : Off := ((s 0).val, (s 1).val, (s 2).val, (s 3).val)

/-- Add one in direction `α`. -/
def bump (t : Off) (α : Direction) : Off :=
  (t.1 + (if α = 0 then 1 else 0), t.2.1 + (if α = 1 then 1 else 0),
    t.2.2.1 + (if α = 2 then 1 else 0), t.2.2.2 + (if α = 3 then 1 else 0))

/-- A local link key: offset and direction. -/
abbrev Key := Off × Direction

/-- Parity vector of an offset. -/
def parOff (t : Off) : Cell := fun i => ⟨off t i % 2, Nat.mod_lt _ (by norm_num)⟩

/-- A key vanishes when its offset mod 2 gives a tree or selected class. -/
def KeyVanishes (k : Key) : Prop := ¬ IsFreeClass (parOff k.1) k.2

instance (k : Key) : Decidable (KeyVanishes k) := by unfold KeyVanishes; infer_instance

theorem off_up (s : Cell) : off (up s) = fun i => (s i).val := by
  funext i; fin_cases i <;> rfl

theorem off_bump (t : Off) (α : Direction) :
    off (bump t α) = fun i => off t i + if i = α then 1 else 0 := by
  funext i
  fin_cases α <;> fin_cases i <;> simp [off, bump]

theorem parOff_up (s : Cell) : parOff (up s) = s := by
  funext i
  apply Fin.ext
  simp only [parOff, off_up]
  exact Nat.mod_eq_of_lt (s i).isLt

/-- The local curl at offset `t` in plane `P`. -/
def keyCurl (B : Key → ℝ) (t : Cell) (P : PlaquettePlane) : ℝ :=
  B (up t, P.1.1) + B (bump (up t) P.1.1, P.1.2) - B (bump (up t) P.1.2, P.1.1) - B (up t, P.1.2)

/-- The slice function read in the local keys at the coarse point `n`. -/
def localKey {L : ℕ} (a : FreeLink L → ℝ) (n : Fin 4 → ZMod L) (k : Key) : ℝ :=
  extendByZero a ⟨site n (off k.1), k.2⟩

theorem localKey_vanishes {L : ℕ} (a : FreeLink L → ℝ) (n : Fin 4 → ZMod L) (k : Key)
    (h : KeyVanishes k) : localKey a n k = 0 := by
  have hf : ¬ IsFreeLink (⟨site n (off k.1), k.2⟩ : Link (2 * L)) := by
    intro hf
    apply h
    have hpar : parityVec (site n (off k.1)) = parOff k.1 := parityVec_site n (off k.1)
    have hc : IsFreeClass (parityVec (site n (off k.1))) k.2 := hf
    rwa [hpar] at hc
  simp [localKey, extendByZero, hf]

theorem latticeCurl_site {L : ℕ} (a : FreeLink L → ℝ) (n : Fin 4 → ZMod L) (t : Cell)
    (P : PlaquettePlane) :
    latticeCurl (extendByZero a) ⟨site n (fun i => (t i).val), P.1.1, P.1.2, P.2⟩
      = keyCurl (localKey a n) t P := by
  simp only [latticeCurl, keyCurl, localKey, shift_site, off_bump, off_up]

end JesseMath.Physics.YangMillsForestSliceHessian

#assert_zfc_axioms
