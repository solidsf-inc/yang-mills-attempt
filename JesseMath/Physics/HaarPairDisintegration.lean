import Mathlib
import JesseMath.Linter.AxiomAudit

/-! Explicit Haar fibers for disjoint products of two group coordinates.
The kernel samples the first coordinate and unused coordinates independently,
then reconstructs the second coordinate as `h⁻¹ * v`. Reconstruction follows
from the Haar-preserving multiplicative shear, not an assumed disintegration. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory ProbabilityTheory.Kernel
open scoped ENNReal

namespace JesseMath.Physics.HaarPairDisintegration

section Split

variable {G Z : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
  [MeasurableInv G] [MeasurableSpace Z]
  (μ : Measure G) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  [IsMulLeftInvariant μ]

/-- Multiply each selected pair; unused coordinates do not enter the block. -/
def block (u : (G × G) × Z) : G := u.1.1 * u.1.2

/-- A first-coordinate sample and an unused-coordinate sample determine the fiber. -/
def rebuild (v : G) (r : G × Z) : (G × G) × Z := ((r.1, r.1⁻¹ * v), r.2)

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [MeasurableSpace Z] in
@[simp] theorem block_rebuild (v : G) (r : G × Z) : block (rebuild v r) = v := by
  simp [block, rebuild]

omit [MeasurableInv G] in
@[fun_prop] theorem measurable_block : Measurable (block (G := G) (Z := Z)) := by
  unfold block
  fun_prop

@[fun_prop] theorem measurable_rebuild : Measurable (fun p : G × (G × Z) => rebuild p.1 p.2) := by
  unfold rebuild
  fun_prop

@[fun_prop] theorem measurable_rebuild_left (v : G) : Measurable (rebuild (Z := Z) v) := by
  unfold rebuild
  fun_prop

/-- The normalized Haar fiber, including independent unused coordinates. -/
def fiberKernel : Kernel G ((G × G) × Z) where
  toFun v := (μ.prod ν).map (rebuild v)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.map_apply (measurable_rebuild_left _) hs]
    exact measurable_measure_prodMk_left (hs.preimage measurable_rebuild)

omit [IsMulLeftInvariant μ] in
@[simp] theorem fiberKernel_apply (v : G) :
    fiberKernel μ ν v = (μ.prod ν).map (rebuild v) := rfl

instance : IsMarkovKernel (fiberKernel μ ν) where
  isProbabilityMeasure v := by
    change IsProbabilityMeasure ((μ.prod ν).map (rebuild v))
    infer_instance

/-- Haar invariance proves the full change of variables, including the residual coordinates. -/
theorem measurePreserving_rebuild :
    MeasurePreserving (fun p : G × (G × Z) => rebuild p.1 p.2)
      (μ.prod (μ.prod ν)) ((μ.prod μ).prod ν) := by
  have h := (((measurePreserving_prod_inv_mul μ μ).comp measurePreserving_swap).prod
    (MeasurePreserving.id ν)).comp (measurePreserving_prodAssoc μ μ ν).symm
  exact h

/-- Integrating the explicit fiber against coarse Haar recovers fine product Haar. -/
theorem fiberKernel_comp : fiberKernel μ ν ∘ₘ μ = (μ.prod μ).prod ν := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp only [fiberKernel_apply, Measure.map_apply
    (measurable_rebuild_left _) hs]
  calc
    _ = ((μ.prod (μ.prod ν)).map (fun p : G × (G × Z) => rebuild p.1 p.2)) s := by
      rw [Measure.map_apply measurable_rebuild hs,
        Measure.prod_apply (hs.preimage measurable_rebuild)]
      rfl
    _ = _ := congrArg (fun m : Measure ((G × G) × Z) => m s)
      (measurePreserving_rebuild μ ν).map_eq

omit [IsMulLeftInvariant μ] in
/-- Every reconstructed fiber projects to its specified coarse configuration. -/
theorem map_block_fiberKernel (v : G) :
    (fiberKernel μ ν v).map block = Measure.dirac v := by
  rw [fiberKernel_apply, Measure.map_map measurable_block
    (measurable_rebuild_left _)]
  simp [Function.comp_def]

/-- The pair-product marginal of fine Haar is normalized coarse Haar. -/
theorem map_block : ((μ.prod μ).prod ν).map block = μ := by
  rw [← fiberKernel_comp μ ν, Measure.map_comp _ _ measurable_block]
  have hk : (fiberKernel μ ν).map block = Kernel.id := by
    ext v
    rw [Kernel.map_apply _ measurable_block, map_block_fiberKernel]
    rfl
  rw [hk]
  simp

/-- Explicit integral reconstruction for any nonnegative measurable observable. -/
theorem lintegral_fiberKernel (f : ((G × G) × Z) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u, f u ∂((μ.prod μ).prod ν)) = ∫⁻ v, ∫⁻ u, f u ∂fiberKernel μ ν v ∂μ := by
  rw [← fiberKernel_comp μ ν]
  exact Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable

/-- Joint reconstruction, retaining the block value alongside its fine configuration. -/
theorem graph_disintegration :
    μ ⊗ₘ fiberKernel μ ν = ((μ.prod μ).prod ν).map (fun u => (block u, u)) := by
  have hj : μ ⊗ₘ fiberKernel μ ν =
      (μ.prod (μ.prod ν)).map (fun p : G × (G × Z) => (p.1, rebuild p.1 p.2)) := by
    ext s hs
    rw [Measure.compProd_apply hs, Measure.map_apply (by fun_prop) hs,
      Measure.prod_apply (hs.preimage (by fun_prop))]
    apply lintegral_congr
    intro v
    rw [fiberKernel_apply, Measure.map_apply (measurable_rebuild_left _)
      (hs.preimage measurable_prodMk_left)]
    rfl
  have hg : Measurable (fun u : (G × G) × Z => (block u, u)) :=
    measurable_block.prodMk measurable_id
  rw [hj, ← (measurePreserving_rebuild μ ν).map_eq,
    Measure.map_map hg measurable_rebuild]
  congr 1
  funext p
  simp

end Split

section FiniteCoordinates

variable {I J F G : Type*} [MeasurableSpace G]

/-- Rewrite the two members of each pair as two disjoint index copies. -/
def pairIndexEquiv (I : Type*) : (I ⊕ I) ≃ I × Fin 2 :=
  (Equiv.boolProdEquivSum I).symm.trans
    ((Equiv.prodCongr finTwoEquiv.symm (Equiv.refl I)).trans (Equiv.prodComm _ _))

@[simp] theorem pairIndexEquiv_inl (i : I) : pairIndexEquiv I (.inl i) = (i, 0) := rfl
@[simp] theorem pairIndexEquiv_inr (i : I) : pairIndexEquiv I (.inr i) = (i, 1) := rfl

/-- All finite coordinates are partitioned into first links, second links and unused links. -/
def splitConfigEquiv (e : ((I × Fin 2) ⊕ J) ≃ F) :
    (F → G) ≃ᵐ (((I → G) × (I → G)) × (J → G)) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : F => G)
    ((Equiv.sumCongr (pairIndexEquiv I) (Equiv.refl J)).trans e)).symm.trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : (I ⊕ I) ⊕ J => G))).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ I => G)).prodCongr
      (MeasurableEquiv.refl (J → G)))

@[simp] theorem splitConfigEquiv_first (e : ((I × Fin 2) ⊕ J) ≃ F) (u : F → G) (i : I) :
    (splitConfigEquiv e u).1.1 i = u (e (.inl (i, 0))) := rfl

@[simp] theorem splitConfigEquiv_second (e : ((I × Fin 2) ⊕ J) ≃ F) (u : F → G) (i : I) :
    (splitConfigEquiv e u).1.2 i = u (e (.inl (i, 1))) := rfl

@[simp] theorem splitConfigEquiv_unused (e : ((I × Fin 2) ⊕ J) ≃ F) (u : F → G) (j : J) :
    (splitConfigEquiv e u).2 j = u (e (.inr j)) := rfl

variable [Fintype I] [Fintype J] [Fintype F]
  (μ : Measure G) [IsProbabilityMeasure μ]

/-- Reindexing independent Haar coordinates preserves their finite product measure. -/
theorem measurePreserving_splitConfigEquiv (e : ((I × Fin 2) ⊕ J) ≃ F) :
    MeasurePreserving (splitConfigEquiv (G := G) e) (Measure.pi fun _ : F => μ)
      (((Measure.pi fun _ : I => μ).prod (Measure.pi fun _ : I => μ)).prod
        (Measure.pi fun _ : J => μ)) := by
  exact ((measurePreserving_sumPiEquivProdPi (fun _ : I ⊕ I => μ)).prod
    (MeasurePreserving.id (Measure.pi fun _ : J => μ))).comp
      ((measurePreserving_sumPiEquivProdPi (fun _ : (I ⊕ I) ⊕ J => μ)).comp
        (measurePreserving_piCongrLeft (fun _ : F => μ)
          ((Equiv.sumCongr (pairIndexEquiv I) (Equiv.refl J)).trans e)).symm)

variable [Group G] [MeasurableMul₂ G] [MeasurableInv G] [IsMulLeftInvariant μ]

/-- Product along every selected disjoint pair. -/
def finitePairBlock (e : ((I × Fin 2) ⊕ J) ≃ F) (u : F → G) : I → G :=
  block (splitConfigEquiv e u)

omit [Fintype I] [Fintype J] [Fintype F] [MeasurableMul₂ G] [MeasurableInv G] in
@[simp] theorem finitePairBlock_apply (e : ((I × Fin 2) ⊕ J) ≃ F) (u : F → G) (i : I) :
    finitePairBlock e u i = u (e (.inl (i, 0))) * u (e (.inl (i, 1))) := by
  change (splitConfigEquiv e u).1.1 i * (splitConfigEquiv e u).1.2 i = _
  rw [splitConfigEquiv_first, splitConfigEquiv_second]

omit [Fintype I] [Fintype J] [Fintype F] [MeasurableInv G] in
@[fun_prop] theorem measurable_finitePairBlock (e : ((I × Fin 2) ⊕ J) ≃ F) :
    Measurable (finitePairBlock (G := G) e) :=
  measurable_block.comp (splitConfigEquiv e).measurable

/-- The explicit finite-product Haar fiber, transported back to the original link indices. -/
def finitePairKernel (e : ((I × Fin 2) ⊕ J) ≃ F) : Kernel (I → G) (F → G) :=
  (fiberKernel (Measure.pi fun _ : I => μ) (Measure.pi fun _ : J => μ)).map
    (splitConfigEquiv e).symm

instance (e : ((I × Fin 2) ⊕ J) ≃ F) : IsMarkovKernel (finitePairKernel μ e) :=
  IsMarkovKernel.map _ (splitConfigEquiv e).symm.measurable

omit [Fintype F] [IsMulLeftInvariant μ] in
/-- Sampling formula: independent first links and unused links, followed by reconstruction. -/
theorem finitePairKernel_apply (e : ((I × Fin 2) ⊕ J) ≃ F) (v : I → G) :
    finitePairKernel μ e v =
      ((Measure.pi fun _ : I => μ).prod (Measure.pi fun _ : J => μ)).map
        (fun r => (splitConfigEquiv e).symm (rebuild v r)) := by
  rw [finitePairKernel, Kernel.map_apply _ (splitConfigEquiv e).symm.measurable,
    fiberKernel_apply, Measure.map_map (splitConfigEquiv e).symm.measurable
      (measurable_rebuild_left v)]
  rfl

omit [Fintype F] [IsMulLeftInvariant μ] in
/-- The fiber is supported on the exact specified coarse configuration. -/
theorem finitePairKernel_supported [MeasurableSingletonClass (I → G)]
    (e : ((I × Fin 2) ⊕ J) ≃ F) (v : I → G) :
    ∀ᵐ u ∂finitePairKernel μ e v, finitePairBlock e u = v := by
  rw [finitePairKernel_apply]
  have hr : Measurable (fun r => (splitConfigEquiv e).symm (rebuild v r)) :=
    (splitConfigEquiv e).symm.measurable.comp (measurable_rebuild_left v)
  have hp : MeasurableSet {u | finitePairBlock e u = v} :=
    (measurable_finitePairBlock e) (measurableSet_singleton v)
  apply (ae_map_iff hr.aemeasurable hp).2
  exact Filter.Eventually.of_forall (fun r => by simp [finitePairBlock])

/-- The actual pair-product block sends fine product Haar to coarse product Haar. -/
theorem finitePairBlock_map (e : ((I × Fin 2) ⊕ J) ≃ F) :
    (Measure.pi fun _ : F => μ).map (finitePairBlock (G := G) e) =
      Measure.pi fun _ : I => μ := by
  change (Measure.pi fun _ : F => μ).map (block ∘ splitConfigEquiv e) = _
  rw [← Measure.map_map measurable_block (splitConfigEquiv e).measurable,
    (measurePreserving_splitConfigEquiv μ e).map_eq]
  exact map_block _ _

/-- Genuine joint disintegration of finite product Haar over the pair-product block. -/
theorem finitePairKernel_graph (e : ((I × Fin 2) ⊕ J) ≃ F) :
    (Measure.pi fun _ : I => μ) ⊗ₘ finitePairKernel μ e =
      (Measure.pi fun _ : F => μ).map (fun u => (finitePairBlock e u, u)) := by
  rw [finitePairKernel, Measure.compProd_map (splitConfigEquiv e).symm.measurable,
    graph_disintegration, ← (measurePreserving_splitConfigEquiv μ e).map_eq]
  have hg : Measurable (fun u : ((I → G) × (I → G)) × (J → G) => (block u, u)) :=
    measurable_block.prodMk measurable_id
  rw [Measure.map_map hg (splitConfigEquiv e).measurable]
  rw [Measure.map_map (measurable_id.prodMap (splitConfigEquiv e).symm.measurable)
    (hg.comp (splitConfigEquiv e).measurable)]
  congr 1
  funext u
  simp [Function.comp_def, finitePairBlock]

end FiniteCoordinates

end JesseMath.Physics.HaarPairDisintegration

#assert_zfc_axioms
