import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.SparseInverseDecay
import JesseMath.Physics.YangMillsForestSliceForm
import Mathlib.Tactic

/-!
# Inverse decay for the flat forest-slice curl form

With the definitions of `YangMillsForestSliceForm`, proved for every `L`: `∑ a² ≤ 20 Q(a)`;
`forestHessian L` is invertible; its inverse has entries at most `20 (479/480) ^ d` in the distance
`d` of the conflict graph, and zero between different components; the same three statements for
`β • forestHessian L` with `β > 0`, with `20 / β`. Connectivity of the conflict graph is not proved
here, so the zero clause may be empty. The lower bound uses a table of plaquette fillings, whose
identities and weighted reuse constant the kernel checks.

Scope: this is the flat background `W = I` on the 45-link detail slice, with fine lattice spacing 1
and no spacing factors, for the quadratic curl form. It does not prove that this form is the second
derivative of the SU(2) Wilson action (not attempted here), does not treat curved backgrounds, and
gives no statement across scales or about the continuum.
-/

open JesseMath.Physics
open BigOperators

namespace JesseMath.Physics.YangMillsForestSliceHessian

/-! ## The filling table -/

/-- One face of a filling: base offset, plane and sign. -/
structure Face where
  t : Cell
  P : PlaquettePlane
  sign : ℤ

/-- One row: a free class and its filling. -/
structure Row where
  s : Cell
  μ : Direction
  faces : List Face

/-- Short constructor for table literals. -/
abbrev F := Face.mk

/-- Short constructor for table literals. -/
abbrev R := Row.mk

/-- The filling certificate: one row for each of the 45 free classes. -/
def fillingTable : List Row := [
  R ![0,0,1,0] 3 [F ![0,0,0,0] p23 (1)],
  R ![0,0,1,1] 2 [F ![0,0,0,0] p23 (-1), F ![0,0,1,0] p23 (-1)],
  R ![0,0,1,1] 3 [F ![0,0,0,1] p23 (1)],
  R ![0,1,0,0] 2 [F ![0,0,0,0] p12 (1)],
  R ![0,1,0,0] 3 [F ![0,0,0,0] p13 (1)],
  R ![0,1,0,1] 1 [F ![0,0,0,0] p13 (-1), F ![0,1,0,0] p13 (-1)],
  R ![0,1,0,1] 2 [F ![0,0,0,1] p12 (1)],
  R ![0,1,0,1] 3 [F ![0,0,0,1] p13 (1)],
  R ![0,1,1,0] 1 [F ![0,0,0,0] p12 (-1), F ![0,1,0,0] p12 (-1)],
  R ![0,1,1,0] 2 [F ![0,0,1,0] p12 (1)],
  R ![0,1,1,0] 3 [F ![0,0,1,0] p13 (1), F ![0,0,0,0] p23 (1)],
  R ![0,1,1,1] 1 [F ![0,0,0,1] p12 (-1), F ![0,1,0,1] p12 (-1), F ![0,0,0,0] p13 (-1), F ![0,1,0,0] p13 (-1)],
  R ![0,1,1,1] 2 [F ![0,0,1,1] p12 (1), F ![0,0,0,0] p23 (-1), F ![0,0,1,0] p23 (-1)],
  R ![0,1,1,1] 3 [F ![0,0,1,1] p13 (1), F ![0,0,0,1] p23 (1)],
  R ![1,0,0,0] 1 [F ![0,0,0,0] p01 (1)],
  R ![1,0,0,0] 2 [F ![0,0,0,0] p02 (1)],
  R ![1,0,0,0] 3 [F ![0,0,0,0] p03 (1)],
  R ![1,0,0,1] 0 [F ![0,0,0,0] p03 (-1), F ![1,0,0,0] p03 (-1)],
  R ![1,0,0,1] 1 [F ![0,0,0,1] p01 (1)],
  R ![1,0,0,1] 2 [F ![0,0,0,1] p02 (1)],
  R ![1,0,0,1] 3 [F ![0,0,0,1] p03 (1)],
  R ![1,0,1,0] 0 [F ![0,0,0,0] p02 (-1), F ![1,0,0,0] p02 (-1)],
  R ![1,0,1,0] 1 [F ![0,0,1,0] p01 (1)],
  R ![1,0,1,0] 2 [F ![0,0,1,0] p02 (1)],
  R ![1,0,1,0] 3 [F ![0,0,1,0] p03 (1), F ![0,0,0,0] p23 (1)],
  R ![1,0,1,1] 0 [F ![0,0,0,1] p02 (-1), F ![1,0,0,1] p02 (-1), F ![0,0,0,0] p03 (-1), F ![1,0,0,0] p03 (-1)],
  R ![1,0,1,1] 1 [F ![0,0,1,1] p01 (1)],
  R ![1,0,1,1] 2 [F ![0,0,1,1] p02 (1), F ![0,0,0,0] p23 (-1), F ![0,0,1,0] p23 (-1)],
  R ![1,0,1,1] 3 [F ![0,0,1,1] p03 (1), F ![0,0,0,1] p23 (1)],
  R ![1,1,0,0] 0 [F ![0,0,0,0] p01 (-1), F ![1,0,0,0] p01 (-1)],
  R ![1,1,0,0] 1 [F ![0,1,0,0] p01 (1)],
  R ![1,1,0,0] 2 [F ![0,1,0,0] p02 (1), F ![0,0,0,0] p12 (1)],
  R ![1,1,0,0] 3 [F ![0,1,0,0] p03 (1), F ![0,0,0,0] p13 (1)],
  R ![1,1,0,1] 0 [F ![0,0,0,1] p01 (-1), F ![1,0,0,1] p01 (-1), F ![0,0,0,0] p03 (-1), F ![1,0,0,0] p03 (-1)],
  R ![1,1,0,1] 1 [F ![0,1,0,1] p01 (1), F ![0,0,0,0] p13 (-1), F ![0,1,0,0] p13 (-1)],
  R ![1,1,0,1] 2 [F ![0,1,0,1] p02 (1), F ![0,0,0,1] p12 (1)],
  R ![1,1,0,1] 3 [F ![0,1,0,1] p03 (1), F ![0,0,0,1] p13 (1)],
  R ![1,1,1,0] 0 [F ![0,0,1,0] p01 (-1), F ![1,0,1,0] p01 (-1), F ![0,0,0,0] p02 (-1), F ![1,0,0,0] p02 (-1)],
  R ![1,1,1,0] 1 [F ![0,1,1,0] p01 (1), F ![0,0,0,0] p12 (-1), F ![0,1,0,0] p12 (-1)],
  R ![1,1,1,0] 2 [F ![0,1,1,0] p02 (1), F ![0,0,1,0] p12 (1)],
  R ![1,1,1,0] 3 [F ![0,1,1,0] p03 (1), F ![0,0,1,0] p13 (1), F ![0,0,0,0] p23 (1)],
  R ![1,1,1,1] 0 [F ![0,0,1,1] p01 (-1), F ![1,0,1,1] p01 (-1), F ![0,0,0,1] p02 (-1), F ![1,0,0,1] p02 (-1), F ![0,0,0,0] p03 (-1), F ![1,0,0,0] p03 (-1)],
  R ![1,1,1,1] 1 [F ![0,1,1,1] p01 (1), F ![0,0,0,1] p12 (-1), F ![0,1,0,1] p12 (-1), F ![0,0,0,0] p13 (-1), F ![0,1,0,0] p13 (-1)],
  R ![1,1,1,1] 2 [F ![0,1,1,1] p02 (1), F ![0,0,1,1] p12 (1), F ![0,0,0,0] p23 (-1), F ![0,0,1,0] p23 (-1)],
  R ![1,1,1,1] 3 [F ![0,1,1,1] p03 (1), F ![0,0,1,1] p13 (1), F ![0,0,0,1] p23 (1)]]

/-- The class of a row. -/
def Row.cls (r : Row) : Cell × Direction := (r.s, r.μ)

/-- The signed terms of a curl. -/
def curlTerms (t : Cell) (P : PlaquettePlane) (c : ℤ) : List (ℤ × Key) :=
  [(c, (up t, P.1.1)), (c, (bump (up t) P.1.1, P.1.2)),
    (-c, (bump (up t) P.1.2, P.1.1)), (-c, (up t, P.1.2))]

/-- All signed terms of a filling identity, with the target at coefficient `-1`. -/
def Row.terms (r : Row) : List (ℤ × Key) :=
  (-1, (up r.s, r.μ)) :: r.faces.flatMap fun f => curlTerms f.t f.P f.sign

/-- Total coefficient of a key in a list of terms. -/
def coef (l : List (ℤ × Key)) (k : Key) : ℤ :=
  (l.map fun x => if x.2 = k then x.1 else 0).sum

/-- Number of times a face slot occurs. -/
def slotCount (fs : List Face) (u : Cell × PlaquettePlane) : ℕ :=
  (fs.map fun f => if (f.t, f.P) = u then 1 else 0).sum

/-- Weighted reuse of a slot: the sum over rows using it of the row's number of faces. -/
def slotWeight (rows : List Row) (u : Cell × PlaquettePlane) : ℕ :=
  (rows.map fun r => r.faces.length * slotCount r.faces u).sum

theorem fillingTable_nodup : (fillingTable.map Row.cls).Nodup := by decide +kernel

theorem fillingTable_free : ∀ r ∈ fillingTable, IsFreeClass r.s r.μ := by decide +kernel

theorem fillingTable_cover :
    ∀ c : Cell × Direction, IsFreeClass c.1 c.2 → c ∈ fillingTable.map Row.cls := by
  decide +kernel

theorem fillingTable_signs : ∀ r ∈ fillingTable, ∀ f ∈ r.faces, f.sign * f.sign = 1 := by
  decide +kernel

/-- Every filling identity, key by key: each key either vanishes or has total coefficient zero. -/
theorem fillingTable_identities :
    ∀ r ∈ fillingTable, ∀ x ∈ r.terms, KeyVanishes x.2 ∨ coef r.terms x.2 = 0 := by
  decide +kernel

/-- The weighted reuse constant is at most 20. -/
theorem fillingTable_weight :
    ∀ u : Cell × PlaquettePlane, slotWeight fillingTable u ≤ 20 := by
  decide +kernel

/-- There are 45 free classes in a cell. -/
theorem sum_freeClass :
    (∑ s : Cell, ∑ μ : Direction, if IsFreeClass s μ then 1 else 0) = 45 := by
  decide +kernel

/-! ## From the table to real numbers -/

/-- Value of a list of signed terms. -/
def termSum (B : Key → ℝ) (l : List (ℤ × Key)) : ℝ :=
  (l.map fun x => (x.1 : ℝ) * B x.2).sum

theorem termSum_eq_sum_coef (B : Key → ℝ) (l : List (ℤ × Key)) (S : Finset Key)
    (hS : ∀ x ∈ l, x.2 ∈ S) :
    termSum B l = ∑ k ∈ S, (coef l k : ℝ) * B k := by
  induction l with
  | nil => simp [termSum, coef]
  | cons x l ih =>
    have hx : x.2 ∈ S := hS x (by simp)
    have ih' := ih fun y hy => hS y (by simp [hy])
    have hsplit : ∀ k, (coef (x :: l) k : ℝ) * B k
        = (if x.2 = k then (x.1 : ℝ) * B k else 0) + (coef l k : ℝ) * B k := by
      intro k
      simp only [coef, List.map_cons, List.sum_cons, Int.cast_add]
      split_ifs <;> simp [add_mul]
    simp only [hsplit, Finset.sum_add_distrib, ← ih']
    simp [termSum, hx]

/-- Terms whose keys all vanish or cancel sum to zero. -/
theorem termSum_eq_zero (B : Key → ℝ) (hB : ∀ k, KeyVanishes k → B k = 0) (l : List (ℤ × Key))
    (h : ∀ x ∈ l, KeyVanishes x.2 ∨ coef l x.2 = 0) : termSum B l = 0 := by
  rw [termSum_eq_sum_coef B l (l.map Prod.snd).toFinset (by
    intro x hx
    exact List.mem_toFinset.2 (List.mem_map.2 ⟨x, hx, rfl⟩))]
  refine Finset.sum_eq_zero fun k hk => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hk)
  rcases h x hx with hv | hc
  · simp [hB _ hv]
  · simp [hc]

theorem termSum_curlTerms (B : Key → ℝ) (t : Cell) (P : PlaquettePlane) (c : ℤ) :
    termSum B (curlTerms t P c) = (c : ℝ) * keyCurl B t P := by
  simp only [termSum, curlTerms, keyCurl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Int.cast_neg]
  ring

theorem termSum_row (B : Key → ℝ) (r : Row) :
    termSum B r.terms
      = - B (up r.s, r.μ) + (r.faces.map fun f => (f.sign : ℝ) * keyCurl B f.t f.P).sum := by
  have hfm : ∀ fs : List Face, termSum B (fs.flatMap fun f => curlTerms f.t f.P f.sign)
      = (fs.map fun f => (f.sign : ℝ) * keyCurl B f.t f.P).sum := by
    intro fs
    induction fs with
    | nil => simp [termSum]
    | cons f fs ih =>
      rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← ih, ← termSum_curlTerms]
      simp [termSum, List.sum_append]
  rw [Row.terms, ← hfm]
  simp [termSum]

/-- Cauchy-Schwarz for a list. -/
theorem list_sum_sq_le (l : List ℝ) : l.sum ^ 2 ≤ l.length * (l.map fun x => x ^ 2).sum := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin l.length)))
    (f := fun i => l[i.1])
  have h1 : (∑ i : Fin l.length, l[i.1]) = l.sum := Fin.sum_univ_getElem l
  have h2 : (∑ i : Fin l.length, l[i.1] ^ 2) = (l.map fun x => x ^ 2).sum :=
    Fin.sum_univ_fun_getElem l fun x => x ^ 2
  rw [h1, h2] at h
  simpa using h

/-- The contribution of one face list to the slot sum. -/
theorem sum_faces_eq (y : Cell × PlaquettePlane → ℝ) (fs : List Face) :
    (fs.map fun f => y (f.t, f.P)).sum = ∑ u, (slotCount fs u : ℝ) * y u := by
  induction fs with
  | nil => simp [slotCount]
  | cons f fs ih =>
    have hsplit : ∀ u, (slotCount (f :: fs) u : ℝ) * y u
        = (if (f.t, f.P) = u then y u else 0) + (slotCount fs u : ℝ) * y u := by
      intro u
      simp only [slotCount, List.map_cons, List.sum_cons, Nat.cast_add]
      split_ifs <;> simp [add_mul]
    simp only [hsplit, Finset.sum_add_distrib, ← ih]
    simp

/-- Swap of the row sum and the slot sum. -/
theorem sum_rows_eq (y : Cell × PlaquettePlane → ℝ) (rows : List Row) :
    (rows.map fun r => (r.faces.length : ℝ) * (r.faces.map fun f => y (f.t, f.P)).sum).sum
      = ∑ u, (slotWeight rows u : ℝ) * y u := by
  induction rows with
  | nil => simp [slotWeight]
  | cons r rows ih =>
    have hw : ∀ u, (slotWeight (r :: rows) u : ℝ)
        = (r.faces.length : ℝ) * slotCount r.faces u + slotWeight rows u := by
      intro u
      simp [slotWeight]
    rw [List.map_cons, List.sum_cons, ih, sum_faces_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by rw [hw]; ring

/-- One row: the filling identity and Cauchy-Schwarz. -/
theorem row_bound (B : Key → ℝ) (hB : ∀ k, KeyVanishes k → B k = 0) (r : Row)
    (hr : r ∈ fillingTable) :
    B (up r.s, r.μ) ^ 2
      ≤ (r.faces.length : ℝ) * (r.faces.map fun f => keyCurl B f.t f.P ^ 2).sum := by
  have hid : termSum B r.terms = 0 := termSum_eq_zero B hB _ (fillingTable_identities r hr)
  rw [termSum_row] at hid
  have htarget : B (up r.s, r.μ)
      = (r.faces.map fun f => (f.sign : ℝ) * keyCurl B f.t f.P).sum := by linarith
  rw [htarget]
  have hcs := list_sum_sq_le (r.faces.map fun f => (f.sign : ℝ) * keyCurl B f.t f.P)
  rw [List.length_map, List.map_map] at hcs
  refine hcs.trans (le_of_eq ?_)
  congr 2
  refine List.map_congr_left fun f hf => ?_
  have hs : ((f.sign : ℝ)) * (f.sign : ℝ) = 1 := by
    exact_mod_cast fillingTable_signs r hr f hf
  simp only [Function.comp_apply, mul_pow, sq (f.sign : ℝ), hs, one_mul]

/-- The bound in one coarse cell, for any key function vanishing on tree and selected keys. -/
theorem cell_bound (B : Key → ℝ) (hB : ∀ k, KeyVanishes k → B k = 0) :
    ∑ s : Cell, ∑ μ : Direction, B (up s, μ) ^ 2
      ≤ 20 * ∑ t : Cell, ∑ P : PlaquettePlane, keyCurl B t P ^ 2 := by
  let g : Cell × Direction → ℝ := fun c => B (up c.1, c.2) ^ 2
  let y : Cell × PlaquettePlane → ℝ := fun u => keyCurl B u.1 u.2 ^ 2
  have hlhs : ∑ s : Cell, ∑ μ : Direction, B (up s, μ) ^ 2
      = (fillingTable.map fun r => B (up r.s, r.μ) ^ 2).sum := by
    calc ∑ s : Cell, ∑ μ : Direction, B (up s, μ) ^ 2
        = ∑ c : Cell × Direction, g c := (Fintype.sum_prod_type' _).symm
      _ = ∑ c ∈ (fillingTable.map Row.cls).toFinset, g c := by
          refine (Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_).symm
          have hnf : ¬ IsFreeClass c.1 c.2 := fun hf =>
            hc (List.mem_toFinset.2 (fillingTable_cover c hf))
          have hv : KeyVanishes (up c.1, c.2) := by
            simp only [KeyVanishes, parOff_up]
            exact hnf
          simp [g, hB _ hv]
      _ = ((fillingTable.map Row.cls).map g).sum := List.sum_toFinset g fillingTable_nodup
      _ = _ := by rw [List.map_map]; rfl
  rw [hlhs]
  calc (fillingTable.map fun r => B (up r.s, r.μ) ^ 2).sum
      ≤ (fillingTable.map fun r =>
          (r.faces.length : ℝ) * (r.faces.map fun f => y (f.t, f.P)).sum).sum :=
        List.sum_le_sum fun r hr => row_bound B hB r hr
    _ = ∑ u, (slotWeight fillingTable u : ℝ) * y u := sum_rows_eq y fillingTable
    _ ≤ ∑ u, (20 : ℝ) * y u := by
        refine Finset.sum_le_sum fun u _ => ?_
        have hw : (slotWeight fillingTable u : ℝ) ≤ 20 := by
          exact_mod_cast fillingTable_weight u
        exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = 20 * ∑ t : Cell, ∑ P : PlaquettePlane, keyCurl B t P ^ 2 := by
        rw [← Finset.mul_sum, Fintype.sum_prod_type]

/-! ## The Poincare inequality and the count -/

theorem forestSlice_poincare {L : ℕ} [NeZero L] (a : FreeLink L → ℝ) :
    ∑ e, a e ^ 2 ≤ 20 * forestForm L a := by
  calc ∑ e, a e ^ 2
      = ∑ n : Fin 4 → ZMod L, ∑ s : Cell, ∑ μ : Direction, localKey a n (up s, μ) ^ 2 := by
        rw [sum_free_sq, sum_link, sum_site]
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun s _ => ?_
        simp only [localKey, off_up]
    _ ≤ ∑ n : Fin 4 → ZMod L,
          20 * ∑ t : Cell, ∑ P : PlaquettePlane, keyCurl (localKey a n) t P ^ 2 :=
        Finset.sum_le_sum fun n _ => cell_bound _ (localKey_vanishes a n)
    _ = 20 * forestForm L a := by
        rw [forestForm, sum_plaquette, sum_site, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        simp only [latticeCurl_site]

theorem card_freeLink (L : ℕ) [NeZero L] : Fintype.card (FreeLink L) = 45 * L ^ 4 := by
  have hreal : (Fintype.card (FreeLink L) : ℝ) = 45 * (L : ℝ) ^ 4 := by
    have hc : (Fintype.card (FreeLink L) : ℝ) = ∑ e : FreeLink L, (1 : ℝ) ^ 2 := by simp
    rw [hc]
    have := sum_free_sq (L := L) (fun _ => (1 : ℝ))
    rw [this, sum_link, sum_site]
    have hclass : ∀ (n : Fin 4 → ZMod L) (s : Cell) (μ : Direction),
        extendByZero (fun _ : FreeLink L => (1 : ℝ)) ⟨site n (fun i => (s i).val), μ⟩ ^ 2
          = ((if IsFreeClass s μ then 1 else 0 : ℕ) : ℝ) := by
      intro n s μ
      have hpar : parityVec (site n (fun i => (s i).val)) = s := by
        rw [parityVec_site]
        funext i
        apply Fin.ext
        exact Nat.mod_eq_of_lt (s i).isLt
      have hiff : IsFreeLink (⟨site n (fun i => (s i).val), μ⟩ : Link (2 * L))
          ↔ IsFreeClass s μ := by
        change IsFreeClass (parityVec (site n (fun i => (s i).val))) μ ↔ _
        rw [hpar]
      by_cases h : IsFreeClass s μ
      · simp [extendByZero, h, hiff.2 h]
      · simp [extendByZero, h, mt hiff.1 h]
    simp only [hclass]
    have hcount : (∑ s : Cell, ∑ μ : Direction, ((if IsFreeClass s μ then 1 else 0 : ℕ) : ℝ))
        = 45 := by
      exact_mod_cast sum_freeClass
    simp only [hcount, Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  exact_mod_cast hreal

/-! ## Decay of the inverse of the forest-slice matrix -/

section Decay

variable {L : ℕ} [NeZero L]

theorem forestHessian_lower (a : FreeLink L → ℝ) :
    (1 / 20 : ℝ) * ∑ e, a e ^ 2 ≤ ∑ e, ∑ f, a e * forestHessian L e f * a f := by
  rw [forestHessian_quadratic]
  linarith [forestSlice_poincare a]

theorem forestHessian_upper (a : FreeLink L → ℝ) :
    ∑ e, ∑ f, a e * forestHessian L e f * a f ≤ 24 * ∑ e, a e ^ 2 := by
  rw [forestHessian_quadratic]
  exact forestSlice_upper a

theorem decay_ratio : (1 - (1 / 20 : ℝ) / 24) = 479 / 480 := by norm_num

theorem forestHessian_isUnit_det : IsUnit (forestHessian L).det :=
  SparseInverseDecay.isUnit_det_of_lower _ (by norm_num) forestHessian_lower

/-- Entries of the inverse decay in conflict-graph distance. `SimpleGraph.dist` is `0` between
different components, so the second clause states separately that those entries vanish. -/
theorem forestHessian_inverse_decay (e f : FreeLink L) :
    |(forestHessian L)⁻¹ e f| ≤ 20 * (479 / 480 : ℝ) ^ (conflictGraph L).dist e f ∧
      (¬ (conflictGraph L).Reachable e f → (forestHessian L)⁻¹ e f = 0) := by
  obtain ⟨-, hdecay, hzero⟩ := SparseInverseDecay.inverse_entry_decay (conflictGraph L) (forestHessian L)
    forestHessian_isSymm (lo := 1 / 20) (hi := 24) (by norm_num) (by norm_num)
    forestHessian_lower forestHessian_upper (fun _ _ h => forestHessian_local h)
  refine ⟨?_, hzero e f⟩
  have h := hdecay e f
  rwa [decay_ratio, show (1 / (1 / 20) : ℝ) = 20 by norm_num] at h

/-- The matrix scaled by `β > 0` is invertible, and its inverse has the same decay with `20 / β`
and the same zeros between different components. -/
theorem forestHessian_scaled_inverse_decay {β : ℝ} (hβ : 0 < β) (e f : FreeLink L) :
    IsUnit (β • forestHessian L).det ∧
      |(β • forestHessian L)⁻¹ e f| ≤ (20 / β) * (479 / 480 : ℝ) ^ (conflictGraph L).dist e f ∧
      (¬ (conflictGraph L).Reachable e f → (β • forestHessian L)⁻¹ e f = 0) := by
  obtain ⟨hdet, hdecay, hzero⟩ := SparseInverseDecay.inverse_entry_decay_smul (conflictGraph L)
    (forestHessian L) forestHessian_isSymm (lo := 1 / 20) (hi := 24) (by norm_num) (by norm_num)
    forestHessian_lower forestHessian_upper (fun _ _ h => forestHessian_local h) hβ
  refine ⟨hdet, ?_, hzero e f⟩
  have h := hdecay e f
  rwa [decay_ratio, show (1 / (β * (1 / 20)) : ℝ) = 20 / β by field_simp] at h

end Decay

end JesseMath.Physics.YangMillsForestSliceHessian

#assert_zfc_axioms