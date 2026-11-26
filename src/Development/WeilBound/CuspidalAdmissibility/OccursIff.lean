module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor

@[expose] public section

attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.t2Space_general_linear_group GlobalTheory.SplitFlip.secondCountable_GL

section -- merged from Development.WeilBound.CuspidalAdmissibility.CuspProjectionOrthogonality
section -- merged from Development.WeilBound.CuspidalAdmissibility.OccLocSpan
open GroundTheory.Automorphic.RestrictedTensor
open scoped TensorProduct

namespace PositivityTheory.TfC.OccursIff.Span

theorem span_core {ι : Type} {W : ι → Type} [∀ v, AddCommGroup (W v)] [∀ v, Module ℂ (W v)] (ξ : ∀ v, W v)
    {C W₁ W₂ H : Type} [AddCommGroup C] [Module ℂ C] [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂]
    [Module ℂ W₂] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : C ≃ₗ[ℂ] W₁ ⊗[ℂ] W₂)
    (Te : W₂ ≃ₗ[ℂ] restrictedTensor ξ) (Φ : C →ₗ[ℂ] H) (u : H)
    (h : ∀ a (x : ∀ v, W v) (hx : IsRestricted ξ x),
      inner ℂ (Φ (E.symm (a ⊗ₜ Te.symm ⟨PiTensorProduct.tprod ℂ x, tprod_mem_restrictedTensor hx⟩))) u = 0)
    (c : C) : inner ℂ (Φ c) u = 0 := by
  let Z : Submodule ℂ C :=
    { carrier := {c | inner ℂ (Φ c) u = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add (f := _), inner_add_left, ha, hb, add_zero]
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [map_zero, inner_zero_left]
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [map_smul, inner_smul_left, hx, mul_zero] }
  have hZ : ∀ c, c ∈ Z ↔ inner ℂ (Φ c) u = 0 := fun c => Iff.rfl
  have h2 : ∀ a (r : restrictedTensor ξ), E.symm (a ⊗ₜ Te.symm r) ∈ Z := by
    intro a r
    obtain ⟨r, hr⟩ := r
    induction hr using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        exact (hZ _).2 (h a x hx)
    | zero =>
        have e : (⟨0, Submodule.zero_mem _⟩ : restrictedTensor ξ) = 0 := rfl
        rw [e, map_zero, TensorProduct.tmul_zero, map_zero]
        exact Z.zero_mem
    | add y z hy hz ihy ihz =>
        have e : (⟨y + z, add_mem hy hz⟩ : restrictedTensor ξ) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
        rw [e, map_add (f := _), TensorProduct.tmul_add, map_add (f := _)]
        exact Z.add_mem ihy ihz
    | smul c y hy ihy =>
        have e : (⟨c • y, Submodule.smul_mem _ c hy⟩ : restrictedTensor ξ) = c • ⟨y, hy⟩ := rfl
        rw [e, map_smul, TensorProduct.tmul_smul, map_smul]
        exact Z.smul_mem c ihy
  have h3 : ∀ t : W₁ ⊗[ℂ] W₂, E.symm t ∈ Z := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Z.zero_mem
    | tmul a b =>
        have := h2 a (Te b)
        rwa [LinearEquiv.symm_apply_apply] at this
    | add s t hs ht => rw [map_add (f := _)]; exact Z.add_mem hs ht
  have := h3 (E c)
  rwa [LinearEquiv.symm_apply_apply] at this

end PositivityTheory.TfC.OccursIff.Span
end

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace PositivityTheory.TfC.CuspProjectionOrthogonality

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

abbrev cuspPart (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ))) : Submodule ℂ (CuspL2 μ) :=
  V.comap ((toLp μ : CuspL2 μ →L[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ)) :
    CuspL2 μ →ₗ[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ))

theorem isClosed_cuspPart (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ)))
    (hcl : IsClosed (V : Set (Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ)))) :
    IsClosed ((cuspPart μ V : Submodule ℂ (CuspL2 μ)) : Set (CuspL2 μ)) :=
  hcl.preimage (toLp μ).continuous

theorem isInvariant_cuspPart (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ)))
    (hinv : (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).IsInvariant V) :
    (cuspRepT μ).IsInvariant (cuspPart μ V) := by
  intro g v hv
  show toLp μ (cuspRepT μ g v) ∈ V
  rw [toLp_cuspRepT]
  exact hinv g _ hv

theorem isometry_toLp (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] :
    Isometry (toLp μ) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_toLp μ)

theorem isMinimal_cuspPart (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ)))
    (hle : V ≤ cuspidalL2 μ) (hcl : IsClosed (V : Set (Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ))))
    (hinv : (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).IsInvariant V) (hne : V ≠ ⊥)
    (hirr : ∀ V' ≤ V, IsClosed (V' : Set (Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ))) →
      (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).IsInvariant V' → V' = ⊥ ∨ V' = V) :
    (cuspRepT μ).IsMinimal (cuspPart μ V) := by
  refine ⟨isClosed_cuspPart μ V hcl, isInvariant_cuspPart μ V hinv, ?_, ?_⟩
  · obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    intro h
    let u0 : CuspL2 μ := ⟨u, hle hu⟩
    have hmem : u0 ∈ cuspPart μ V := hu
    rw [h, Submodule.mem_bot] at hmem
    exact hu0 (congrArg Subtype.val hmem)
  · intro U hUc hUi hUV
    set U' : Submodule ℂ (Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ)) :=
      U.map ((toLp μ : CuspL2 μ →L[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ)) :
        CuspL2 μ →ₗ[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ)) with hU'
    have hU'V : U' ≤ V := by
      rintro _ ⟨v, hv, rfl⟩
      exact hUV hv
    have hU'c : IsClosed (U' : Set (Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ))) := by
      rw [hU', Submodule.map_coe]
      exact (isometry_toLp μ).isClosedEmbedding.isClosedMap _ hUc
    have hU'i : (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).IsInvariant U' := by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨cuspRepT μ g v, hUi g v hv, rfl⟩
    rcases hirr U' hU'V hU'c hU'i with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      have : toLp μ v ∈ U' := ⟨v, hv, rfl⟩
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact toLp_injective μ (this.trans (map_zero (toLp μ)).symm)
    · right
      refine le_antisymm hUV fun v hv => ?_
      have : toLp μ v ∈ U' := by rw [h]; exact hv
      obtain ⟨v', hv', e⟩ := this
      rwa [← toLp_injective μ e]

section Family

variable (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
  (P : CuspidalAutomorphicRepresentation K n) (D : AdelicDecomposition P.toModule)

def clsL : P.carrier →ₗ[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ) :=
  ((toLp μ : CuspL2 μ →L[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ)) :
    CuspL2 μ →ₗ[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ)) ∘ₗ cuspVecL μ ∘ₗ P.carrier.subtype

theorem clsL_tau (h : AdelicGLn.FiniteAdelicGL K n) (c : P.carrier) :
    clsL μ P (P.toModule.τ h c) =
      rightRegularRep (rationalGLOne (K := K) (n := n)) μ (MultiplicityOne.finProj K n h) (clsL μ P c) := by
  show toLp μ (cuspVecL μ (finRepCusp K n h c)) = _
  rw [cuspToL2_finRepCusp μ h (P.le_central c.2), toLp_cuspRepT]
  rfl

variable {P} in
theorem equiv_symm_tmul_tau (h : AdelicGLn.FiniteAdelicGL K n) (a : D.toDecomposition.W₁)
    (b : D.toDecomposition.W₂) :
    D.toDecomposition.equiv.toLinearEquiv.symm (a ⊗ₜ D.toDecomposition.π₂ h b) =
      P.toModule.τ h (D.toDecomposition.equiv.toLinearEquiv.symm (a ⊗ₜ b)) := by
  set E := D.toDecomposition.equiv
  rw [LinearEquiv.symm_apply_eq]
  have key : E.toLinearEquiv (P.toModule.fullRep ((1 : FreeMonoid _), h) (E.toLinearEquiv.symm (a ⊗ₜ b))) =
      RestrictedTensor.outerTensor D.toDecomposition.π₁.rep D.toDecomposition.π₂ ((1 : FreeMonoid _), h)
        (E.toLinearEquiv (E.toLinearEquiv.symm (a ⊗ₜ b))) :=
    LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' ((1 : FreeMonoid _), h)) _
  rw [LinearEquiv.apply_symm_apply, RestrictedTensor.outerTensor_tmul] at key
  have hf : P.toModule.fullRep ((1 : FreeMonoid _), h) (E.toLinearEquiv.symm (a ⊗ₜ b)) =
      P.toModule.τ h (E.toLinearEquiv.symm (a ⊗ₜ b)) := by
    show P.toModule.gk.rep 1 (P.toModule.τ h _) = _
    rw [map_one, Module.End.one_apply]
  rw [hf] at key
  simp only [map_one, Module.End.one_apply] at key
  exact key.symm

variable {P} in
theorem tensorEquiv_symm_rep (h : AdelicGLn.FiniteAdelicGL K n)
    (t : RestrictedTensor.restrictedTensor D.finite.ξ) :
    D.finite.equiv.toLinearEquiv.symm (AdelicGLn.adelicTensorRep D.finite.π D.finite.ξ D.finite.mem_fixedVectors h t) =
      D.toDecomposition.π₂ h (D.finite.equiv.toLinearEquiv.symm t) :=
  LinearMap.congr_fun (D.finite.equiv.symm.toIntertwiningMap.isIntertwining' h) t


open Classical in
variable {P} in
def famL (w : HeightOneSpectrum (𝓞 K)) (x : ∀ v, D.finite.W v)
    (hx : RestrictedTensor.IsRestricted D.finite.ξ x) :
    D.finite.W w →ₗ[ℂ] RestrictedTensor.restrictedTensor D.finite.ξ :=
  LinearMap.codRestrict _ ((PiTensorProduct.tprod ℂ).toLinearMap x w) fun y => by
    rw [MultilinearMap.toLinearMap_apply]
    exact RestrictedTensor.tprod_mem_restrictedTensor (hx.update w y)

open Classical in
variable {P} in
theorem coe_famL (w : HeightOneSpectrum (𝓞 K)) (x : ∀ v, D.finite.W v)
    (hx : RestrictedTensor.IsRestricted D.finite.ξ x) (y : D.finite.W w) :
    (famL D w x hx y : PiTensorProduct ℂ D.finite.W) = PiTensorProduct.tprod ℂ (Function.update x w y) := by
  simp [famL, MultilinearMap.toLinearMap_apply]

variable {P} in
theorem famL_self (w : HeightOneSpectrum (𝓞 K)) (x : ∀ v, D.finite.W v)
    (hx : RestrictedTensor.IsRestricted D.finite.ξ x) :
    (famL D w x hx (x w) : PiTensorProduct ℂ D.finite.W) = PiTensorProduct.tprod ℂ x := by
  classical
  rw [coe_famL]
  congr 1
  exact Function.update_eq_self w x

variable {P} in
theorem famL_equivariant (w : HeightOneSpectrum (𝓞 K)) (x : ∀ v, D.finite.W v)
    (hx : RestrictedTensor.IsRestricted D.finite.ξ x) (g : GL (Fin n) (w.adicCompletion K))
    (y : D.finite.W w) :
    famL D w x hx (D.finite.π w g y) =
      AdelicGLn.adelicTensorRep D.finite.π D.finite.ξ D.finite.mem_fixedVectors
        (AdelicGLn.localEmbedding w g) (famL D w x hx y) := by
  classical
  apply Subtype.ext
  have hr : AdelicGLn.toRestricted K n (AdelicGLn.localEmbedding w g) =
      RestrictedProduct.mulSingle (fun v => GLnLocal.integralGL (v.adicCompletion K) n) w g :=
    (AdelicGLn.finiteRestrictedEquiv K n).apply_symm_apply _
  change _ = RestrictedTensor.tensorRep _ D.finite.π (AdelicGLn.toRestricted K n (AdelicGLn.localEmbedding w g))
    (famL D w x hx y : PiTensorProduct ℂ D.finite.W)
  calc (famL D w x hx (D.finite.π w g y) : PiTensorProduct ℂ D.finite.W)
      = PiTensorProduct.tprod ℂ (Function.update x w (D.finite.π w g y)) := coe_famL D w x hx _
    _ = PiTensorProduct.tprod ℂ (Function.update (Function.update x w y) w
          (D.finite.π w g (Function.update x w y w))) := by
        rw [Function.update_idem, Function.update_self]
    _ = RestrictedTensor.tensorRep (fun v => GLnLocal.integralGL (v.adicCompletion K) n) D.finite.π
          (RestrictedProduct.mulSingle (fun v => GLnLocal.integralGL (v.adicCompletion K) n) w g)
          (PiTensorProduct.tprod ℂ (Function.update x w y)) := by
        rw [RestrictedTensor.tensorRep_mulSingle_tprod]
    _ = _ := congrArg₂ (fun z t => RestrictedTensor.tensorRep
          (fun v => GLnLocal.integralGL (v.adicCompletion K) n) D.finite.π z t) hr.symm (coe_famL D w x hx y).symm

def famF (w : HeightOneSpectrum (𝓞 K)) (a : D.toDecomposition.W₁) (x : ∀ v, D.finite.W v)
    (hx : RestrictedTensor.IsRestricted D.finite.ξ x) :
    D.finite.W w →ₗ[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ) :=
  clsL μ P ∘ₗ D.toDecomposition.equiv.toLinearEquiv.symm.toLinearMap ∘ₗ
    TensorProduct.mk ℂ D.toDecomposition.W₁ D.toDecomposition.W₂ a ∘ₗ
    D.finite.equiv.toLinearEquiv.symm.toLinearMap ∘ₗ famL D w x hx

theorem famF_equivariant (w : HeightOneSpectrum (𝓞 K)) (a : D.toDecomposition.W₁) (x : ∀ v, D.finite.W v)
    (hx : RestrictedTensor.IsRestricted D.finite.ξ x) (g : GL (Fin n) (w.adicCompletion K))
    (y : D.finite.W w) :
    famF μ P D w a x hx (D.finite.π w g y) = rightRegularRep (rationalGLOne (K := K) (n := n)) μ
      (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) (famF μ P D w a x hx y) := by
  have h12 := (congrArg D.finite.equiv.toLinearEquiv.symm (famL_equivariant D w x hx g y)).trans
    (tensorEquiv_symm_rep D (AdelicGLn.localEmbedding w g) (famL D w x hx y))
  have h3 := congrArg (fun t => D.toDecomposition.equiv.toLinearEquiv.symm (a ⊗ₜ t)) h12
  have h4 := h3.trans (equiv_symm_tmul_tau D (AdelicGLn.localEmbedding w g) a
    (D.finite.equiv.toLinearEquiv.symm (famL D w x hx y)))
  exact (congrArg (clsL μ P) h4).trans (clsL_tau μ P _ _)

end Family

theorem inner_clsL_eq_zero (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (P : CuspidalAutomorphicRepresentation K n) (D : AdelicDecomposition P.toModule)
    (w : HeightOneSpectrum (𝓞 K)) (u : Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ))
    (h : ∀ a x hx y, inner ℂ (famF μ P D w a x hx y) u = 0) (c : P.carrier) :
    inner ℂ (clsL μ P c) u = 0 := by
  refine PositivityTheory.TfC.OccursIff.Span.span_core D.finite.ξ D.toDecomposition.equiv.toLinearEquiv
    D.finite.equiv.toLinearEquiv (clsL μ P) u (fun a x hx => ?_) c
  have e : famL D w x hx (x w) =
      ⟨PiTensorProduct.tprod ℂ x, RestrictedTensor.tprod_mem_restrictedTensor hx⟩ :=
    Subtype.ext (famL_self D w x hx)
  have e2 := congrArg (fun t => clsL μ P (D.toDecomposition.equiv.toLinearEquiv.symm
    (a ⊗ₜ D.finite.equiv.toLinearEquiv.symm t))) e
  exact e2 ▸ h a x hx (x w)

theorem occ_loccomp : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ))), V ≤ cuspidalL2 μ → IsClosed (V : Set (Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ))) → (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).IsInvariant V → V ≠ ⊥ → (∀ V' ≤ V, IsClosed (V' : Set (Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ))) → (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).IsInvariant V' → V' = ⊥ ∨ V' = V) → ∀ (w : HeightOneSpectrum (𝓞 K)), ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (π : Representation ℂ (GL (Fin n) (w.adicCompletion K)) W), GroundTheory.Automorphic.IsAdmissible π ∧ π.IsIrreducible ∧ ∃ F : Set (W →ₗ[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ)), (∀ f ∈ F, (∀ x, f x ∈ V) ∧ ∀ g x, f (π g x) = rightRegularRep (rationalGLOne (K := K) (n := n)) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) (f x)) ∧ ∀ u ∈ V, u ≠ 0 → ∃ f ∈ F, ∃ x, inner ℂ (f x) u ≠ 0 := by
  intro K _ _ n μ _ V hle hcl hinv hne hirr w
  have : CompleteSpace (cuspPart μ V) := (isClosed_cuspPart μ V hcl).completeSpace_coe
  have hV0 := isInvariant_cuspPart μ V hinv
  have hirr0 := UnitaryRep.isIrreducible_restrict_of_isMinimal (π := cuspRepT μ) hV0
    (isMinimal_cuspPart μ V hle hcl hinv hne hirr)
  have hD := CuspidalAutomorphicRepresentation.nonempty_adelicDecomposition_ofL2Summand
    (cuspPart μ V) hV0 hirr0
  set P := CuspidalAutomorphicRepresentation.ofL2Summand (cuspPart μ V) hV0 hirr0 with hP
  obtain ⟨D⟩ := hD
  have hmem : ∀ c : P.carrier, clsL μ P c ∈ V := fun c => c.2.2
  refine ⟨D.finite.W w, inferInstance, inferInstance, D.finite.π w, D.finite.isAdmissible w,
    D.finite.isIrreducible w, {f | ∃ a x hx, f = famF μ P D w a x hx}, ?_, ?_⟩
  · rintro f ⟨a, x, hx, rfl⟩
    exact ⟨fun y => hmem _, fun g y => famF_equivariant μ P D w a x hx g y⟩
  · intro u hu hu0
    by_contra hall
    push_neg at hall
    have h0 : ∀ a x hx y, inner ℂ (famF μ P D w a x hx y) u = 0 :=
      fun a x hx y => hall _ ⟨a, x, hx, rfl⟩ y
    have hc := inner_clsL_eq_zero μ P D w u h0
    let u0 : CuspL2 μ := ⟨u, hle hu⟩
    have hu0' : u0 ∈ (P.carrier.map (cuspVecL μ))ᗮ := by
      rw [Submodule.mem_orthogonal]
      rintro _ ⟨c, hc', rfl⟩
      exact hc ⟨c, hc'⟩
    have hmemV : u0 ∈ (P.carrier.map (cuspVecL μ)).topologicalClosure := by
      rw [hP, CuspidalAutomorphicRepresentation.topologicalClosure_map_ofL2Summand]
      exact hu
    rw [← Submodule.orthogonal_orthogonal_eq_closure] at hmemV
    have h1 := Submodule.inner_right_of_mem_orthogonal hu0' hmemV
    rw [inner_self_eq_zero] at h1
    exact hu0 (congrArg Subtype.val h1)

end PositivityTheory.TfC.CuspProjectionOrthogonality
end
end

section -- merged from Development.WeilBound.CuspidalAdmissibility.OccTrace
open MeasureTheory GroundTheory.Automorphic

namespace PositivityTheory.TfC.OccursIff.Trace

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {X : Type} [AddCommGroup X] [Module ℂ X]


omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G] in
theorem orbit_isLocallyConstant (ρ : Representation ℂ G X) (hρ : IsSmooth ρ) (v : X) :
    IsLocallyConstant fun g => ρ g v := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun h => g⁻¹ * h) ⁻¹' (stabilizerOf ρ v : Set G), (hρ v).preimage (by fun_prop), ?_, fun h hh => ?_⟩
  · show g⁻¹ * g ∈ stabilizerOf ρ v
    rw [inv_mul_cancel]
    exact one_mem _
  · have hh' : ρ (g⁻¹ * h) v = v := hh
    calc ρ h v = ρ g (ρ (g⁻¹ * h) v) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = ρ g v := by rw [hh']

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem exists_vec (m : Measure G) [m.IsHaarMeasure] (ρ : Representation ℂ G X) (hρ : IsSmooth ρ) (φ : G → ℂ)
    (hφ : IsLocallyConstant φ) (hφc : HasCompactSupport φ) (v : X) :
    ∃ a : X, ∀ l : Module.Dual ℂ X, l a = ∫ g, φ g * l (ρ g v) ∂m := by
  classical
  have hloc := orbit_isLocallyConstant ρ hρ v
  have hS : ((fun g => ρ g v) '' tsupport φ).Finite := by
    haveI : CompactSpace (tsupport φ) := isCompact_iff_compactSpace.1 hφc
    have h1 := (hloc.comp_continuous (continuous_subtype_val (p := (· ∈ tsupport φ)))).range_finite
    rwa [Set.range_comp, Subtype.range_coe] at h1
  set S := hS.toFinset
  let E : X → Set G := fun s => {g | ρ g v = s}
  have hE : ∀ s, MeasurableSet (E s) := fun s => (hloc.isOpen_fiber s).measurableSet
  have hφi : Integrable φ m := hφ.continuous.integrable_of_hasCompactSupport hφc
  refine ⟨∑ s ∈ S, (∫ g, (E s).indicator φ g ∂m) • s, fun l => ?_⟩
  have hpt : ∀ g, φ g * l (ρ g v) = ∑ s ∈ S, (E s).indicator φ g * l s := by
    intro g
    by_cases hg : φ g = 0
    · simp [hg, Set.indicator_apply]
    · have hgS : ρ g v ∈ S := hS.mem_toFinset.2 ⟨g, subset_tsupport φ hg, rfl⟩
      rw [Finset.sum_eq_single (ρ g v)]
      · simp [E]
      · intro s _ hs
        simp [E, Ne.symm hs]
      · intro h
        exact absurd hgS h
  have hfun : (fun g => φ g * l (ρ g v)) = fun g => ∑ s ∈ S, (E s).indicator φ g * l s := funext hpt
  rw [hfun, integral_finsetSum]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_smul, smul_eq_mul, integral_mul_const]
  · intro s _
    exact (hφi.indicator (hE s)).mul_const (l s)

theorem exists_integralOp (m : Measure G) [m.IsHaarMeasure] (ρ : Representation ℂ G X) (hρ : IsAdmissible ρ)
    (φ : G → ℂ) (hφ : IsLocallyConstant φ) (hφc : HasCompactSupport φ) :
    ∃ A : X →ₗ[ℂ] X, (∀ (v : X) (l : Module.Dual ℂ X), Integrable (fun g => φ g * l (ρ g v)) m ∧
      l (A v) = ∫ g, φ g * l (ρ g v) ∂m) ∧ FiniteDimensional ℂ (LinearMap.range A) := by
  classical
  have hint : ∀ v (l : Module.Dual ℂ X), Integrable (fun g => φ g * l (ρ g v)) m := fun v l =>
    (hφ.continuous.mul ((orbit_isLocallyConstant ρ hρ.1 v).comp l).continuous).integrable_of_hasCompactSupport
      hφc.mul_right
  choose A0 hA0 using exists_vec m ρ hρ.1 φ hφ hφc
  have huniq : ∀ a b : X, (∀ l : Module.Dual ℂ X, l a = l b) → a = b := fun a b h =>
    sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (a - b)).1 fun l => by rw [map_sub, h, sub_self])
  let A : X →ₗ[ℂ] X :=
    { toFun := A0
      map_add' := fun v v' => huniq _ _ fun l => by
        rw [map_add (f := _), hA0, hA0, hA0, ← integral_add (hint v l) (hint v' l)]
        congr 1
        funext g
        rw [map_add (f := _), map_add (f := _), mul_add]
      map_smul' := fun c v => huniq _ _ fun l => by
        rw [map_smul, hA0, hA0, RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        congr 1
        funext g
        rw [map_smul, map_smul, smul_eq_mul]
        ring }
  obtain ⟨K, hKc, hK⟩ := exists_forall_mul_left (R := ℂ) (E := ℂ)
    (show φ ∈ locallyConstantCompactSupport G ℂ ℂ from ⟨hφ, hφc⟩)
  refine ⟨A, fun v l => ⟨hint v l, hA0 v l⟩, ?_⟩
  haveI : FiniteDimensional ℂ (fixedVectors ρ (K : Subgroup G)) := hρ.2 K hKc K.isOpen
  refine Submodule.finiteDimensional_of_le (S₂ := fixedVectors ρ (K : Subgroup G)) ?_
  rintro _ ⟨v, rfl⟩ k hk
  refine huniq _ _ fun l => ?_
  have h1 := hA0 v (l ∘ₗ ρ k)
  rw [LinearMap.comp_apply] at h1
  show l (ρ k (A0 v)) = l (A0 v)
  rw [h1, hA0]
  have e : (fun g => φ g * (l ∘ₗ ρ k) (ρ g v)) = fun g => (fun h => φ (k⁻¹ * h) * l (ρ h v)) (k * g) := by
    funext g
    simp only [inv_mul_cancel_left, LinearMap.comp_apply]
    rw [← Module.End.mul_apply, ← map_mul]
  rw [e, integral_mul_left_eq_self (fun h => φ (k⁻¹ * h) * l (ρ h v)) k]
  congr 1
  funext g
  rw [hK k⁻¹ (inv_mem hk) g]

end PositivityTheory.TfC.OccursIff.Trace
end

section -- merged from Development.WeilBound.CuspidalAdmissibility.OccPair
open GroundTheory.Automorphic

namespace PositivityTheory.TfC.OccursIff.Pair

theorem conjDual_finite (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] :
    FiniteDimensional ℂ (E →ₗ⋆[ℂ] ℂ) ∧ Module.finrank ℂ (E →ₗ⋆[ℂ] ℂ) ≤ Module.finrank ℂ E := by
  let b := Module.finBasis ℂ E
  let e : (E →ₗ⋆[ℂ] ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
    { toFun := fun l i => l (b i)
      map_add' := fun l l' => by ext i; simp
      map_smul' := fun c l => by ext i; simp }
  have he : Function.Injective e := fun l l' h => b.ext fun i => congrFun h i
  haveI : FiniteDimensional ℂ (E →ₗ⋆[ℂ] ℂ) := Module.Finite.of_injective e he
  refine ⟨this, ?_⟩
  have h := LinearMap.finrank_le_finrank_of_injective he
  simpa using h

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem act_inv (π : Representation ℂ G Y) (g : G) (z : Y) : π g (π g⁻¹ z) = z := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem leftKer_eq_zero (π : Representation ℂ G Y) (hπi : π.IsIrreducible)
    (C : Y →ₗ[ℂ] Y →ₗ⋆[ℂ] ℂ) (hC : ∀ g x y, C (π g x) (π g y) = C x y) (hC0 : C ≠ 0) :
    ∀ a, C a = 0 → a = 0 := by
  let S : Subrepresentation π := ⟨LinearMap.ker C, fun g a ha => by
    rw [LinearMap.mem_ker] at ha ⊢
    refine LinearMap.ext fun z => ?_
    rw [← act_inv π g z, hC, ha]
    rfl⟩
  rcases hπi.eq_bot_or_eq_top S with h | h
  · intro a ha
    have h1 : a ∈ S.toSubmodule := LinearMap.mem_ker.2 ha
    rw [h] at h1
    exact (Submodule.mem_bot ℂ).1 h1
  · exfalso
    apply hC0
    refine LinearMap.ext fun a => ?_
    have h1 : a ∈ S.toSubmodule := by rw [h]; trivial
    exact LinearMap.mem_ker.1 h1

theorem eq_of_fixed (π : Representation ℂ G Y) (hπ : IsSmooth π) {U : Subgroup G} (hUc : IsCompact (U : Set G))
    (hUo : IsOpen (U : Set G)) (l l' : Y →ₗ⋆[ℂ] ℂ) (hl : ∀ u ∈ U, ∀ z, l (π u z) = l z)
    (hl' : ∀ u ∈ U, ∀ z, l' (π u z) = l' z) (h : ∀ z ∈ fixedVectors π U, l z = l' z) : l = l' := by
  have hk : ∀ m : Y →ₗ⋆[ℂ] ℂ, (∀ u ∈ U, ∀ z, m (π u z) = m z) → coinvariantsKer π U ≤ LinearMap.ker m := by
    intro m hm
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨k, v⟩, rfl⟩
    simp [hm k k.2 v]
  refine LinearMap.ext fun z => ?_
  have hs := sub_fixedProj_mem hπ hUc hUo z
  have e1 : l z = l (fixedProj π hπ hUc hUo z) := by
    rw [← sub_eq_zero, ← map_sub]; exact hk l hl hs
  have e2 : l' z = l' (fixedProj π hπ hUc hUo z) := by
    rw [← sub_eq_zero, ← map_sub]; exact hk l' hl' hs
  rw [e1, e2, h _ (fixedProj π hπ hUc hUo z).2]

theorem admissible_and_equiv (σ : Representation ℂ G X) (π : Representation ℂ G Y)
    (hσ : IsSmooth σ) (hσi : σ.IsIrreducible) (hπ : IsAdmissible π) (hπi : π.IsIrreducible)
    (B : X →ₗ[ℂ] Y →ₗ⋆[ℂ] ℂ) (hB : ∀ g x y, B (σ g x) (π g y) = B x y) (hB0 : B ≠ 0)
    (C : Y →ₗ[ℂ] Y →ₗ⋆[ℂ] ℂ) (hC : ∀ g x y, C (π g x) (π g y) = C x y) (hC0 : C ≠ 0) :
    IsAdmissible σ ∧ Nonempty (σ.Equiv π) := by
  have hker := leftKer_eq_zero π hπi C hC hC0
  have huniq : ∀ a a', C a = C a' → a = a' := fun a a' h =>
    sub_eq_zero.1 (hker _ (by rw [map_sub, h, sub_self]))
  have hex : ∀ x, ∃ a, C a = B x := by
    intro x
    obtain ⟨U, hUc, hUo, hxU⟩ := (isSmooth_iff_forall_exists σ).1 hσ x
    haveI : FiniteDimensional ℂ (fixedVectors π U) := hπ.2 U hUc hUo
    set E := fixedVectors π U with hE
    have hCinv : ∀ a ∈ E, ∀ u ∈ U, ∀ z, C a (π u z) = C a z := by
      intro a ha u hu z
      rw [← hC u a z, ha u hu]
    have hBinv : ∀ u ∈ U, ∀ z, B x (π u z) = B x z := by
      intro u hu z
      rw [← hB u x z, hxU u hu]
    let L : E →ₗ[ℂ] (E →ₗ⋆[ℂ] ℂ) :=
      { toFun := fun a => (C a).comp E.subtype
        map_add' := fun a a' => by ext z; simp
        map_smul' := fun c a => by ext z; simp }
    have hL : Function.Injective L := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro a ha
      have h0 : C a = 0 := eq_of_fixed π hπ.1 hUc hUo (C a) 0 (hCinv a a.2) (fun _ _ _ => rfl)
        (fun z hz => by
          have := LinearMap.congr_fun ha ⟨z, hz⟩
          simpa [L] using this)
      exact Subtype.ext (hker _ h0)
    obtain ⟨hfin, hle⟩ := conjDual_finite E
    have heq : Module.finrank ℂ E = Module.finrank ℂ (E →ₗ⋆[ℂ] ℂ) :=
      le_antisymm (LinearMap.finrank_le_finrank_of_injective hL) hle
    have hsurj : Function.Surjective L := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hL
    obtain ⟨a, ha⟩ := hsurj ((B x).comp E.subtype)
    refine ⟨a, eq_of_fixed π hπ.1 hUc hUo (C a) (B x) (hCinv a a.2) hBinv fun z hz => ?_⟩
    have := LinearMap.congr_fun ha ⟨z, hz⟩
    simpa [L] using this
  choose T0 hT0 using hex
  let T : X →ₗ[ℂ] Y :=
    { toFun := T0
      map_add' := fun x x' => huniq _ _ (by rw [hT0, map_add (f := _), map_add (f := _), hT0, hT0])
      map_smul' := fun c x => huniq _ _ (by rw [hT0, map_smul, map_smul, hT0, RingHom.id_apply]) }
  have hTint : ∀ g x, T (σ g x) = π g (T x) := by
    intro g x
    refine huniq _ _ ?_
    refine LinearMap.ext fun z => ?_
    show C (T0 (σ g x)) z = C (π g (T0 x)) z
    rw [hT0, ← act_inv π g z, hC, act_inv π g z, hT0, ← hB g x (π g⁻¹ z), act_inv π g z]
  let f : Representation.IntertwiningMap σ π := ⟨T, fun g => LinearMap.ext fun x => hTint g x⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x, B x ≠ 0 := by
    by_contra hcon
    exact hB0 (LinearMap.ext fun x => not_not.1 fun hx => hcon ⟨x, hx⟩)
  have hf0 : f ≠ 0 := by
    intro h
    apply hx₀
    have h1 : T0 x₀ = 0 := by
      have := congrArg (fun F : Representation.IntertwiningMap σ π => F x₀) h
      exact this
    rw [← hT0, h1, map_zero]
  haveI := hσi
  haveI := hπi
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with hb | h0
  · refine ⟨⟨hσ, fun U hUc hUo => ?_⟩, ⟨Representation.IntertwiningMap.ofBijective f hb⟩⟩
    haveI : FiniteDimensional ℂ (fixedVectors π U) := hπ.2 U hUc hUo
    exact Module.Finite.of_injective (fixedMap σ f U) (fixedMap_injective σ hb.1)
  · exact absurd h0 hf0

end PositivityTheory.TfC.OccursIff.Pair
end

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

namespace PositivityTheory.TfC.OccursIff

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

section Items

theorem exists_integralOp_of_admissible {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
    (m : Measure G) [m.IsHaarMeasure] {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (hρ : GroundTheory.Automorphic.IsAdmissible ρ) (φ : G → ℂ) (hφ : IsLocallyConstant φ) (hφc : HasCompactSupport φ) :
    ∃ A : X →ₗ[ℂ] X, (∀ (v : X) (l : Module.Dual ℂ X), Integrable (fun g => φ g * l (ρ g v)) m ∧
      l (A v) = ∫ g, φ g * l (ρ g v) ∂m) ∧ FiniteDimensional ℂ (LinearMap.range A) :=
  PositivityTheory.TfC.OccursIff.Trace.exists_integralOp m ρ hρ φ hφ hφc

theorem admissible_and_equiv_of_pairing {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (σ : Representation ℂ G X) (π : Representation ℂ G Y)
    (hσ : GroundTheory.Automorphic.IsSmooth σ) (hσi : σ.IsIrreducible)
    (hπ : GroundTheory.Automorphic.IsAdmissible π) (hπi : π.IsIrreducible)
    (B : X →ₗ[ℂ] Y →ₗ⋆[ℂ] ℂ) (hB : ∀ g x y, B (σ g x) (π g y) = B x y) (hB0 : B ≠ 0)
    (C : Y →ₗ[ℂ] Y →ₗ⋆[ℂ] ℂ) (hC : ∀ g x y, C (π g x) (π g y) = C x y) (hC0 : C ≠ 0) :
    GroundTheory.Automorphic.IsAdmissible σ ∧ Nonempty (σ.Equiv π) :=
  PositivityTheory.TfC.OccursIff.Pair.admissible_and_equiv σ π hσ hσi hπ hπi B hB hB0 C hC hC0

theorem exists_localComponent_family (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n)))
    [μ.IsHaarMeasure] (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ)))
    (hle : V ≤ cuspidalL2 μ) (hcl : IsClosed (V : Set (Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ))))
    (hinv : (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).IsInvariant V) (hne : V ≠ ⊥)
    (hirr : ∀ V' ≤ V, IsClosed (V' : Set (Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ))) →
      (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).IsInvariant V' → V' = ⊥ ∨ V' = V)
    (w : HeightOneSpectrum (𝓞 K)) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
      (π : Representation ℂ (GL (Fin n) (w.adicCompletion K)) W),
      GroundTheory.Automorphic.IsAdmissible π ∧ π.IsIrreducible ∧
      ∃ F : Set (W →ₗ[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ)),
        (∀ f ∈ F, (∀ x, f x ∈ V) ∧ ∀ g x, f (π g x) =
          rightRegularRep (rationalGLOne (K := K) (n := n)) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) (f x)) ∧
        ∀ u ∈ V, u ≠ 0 → ∃ f ∈ F, ∃ x, inner ℂ (f x) u ≠ 0 :=
  PositivityTheory.TfC.CuspProjectionOrthogonality.occ_loccomp K n μ V hle hcl hinv hne hirr w

end Items

theorem isSmooth_of_smIrr {G : Type} [Group G] [TopologicalSpace G] (σ : GlobalTheory.CuspRep.SmIrr G) :
    GroundTheory.Automorphic.IsSmooth σ.ρ := fun v => σ.smooth v

def pairL {X Y H : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (f' : X →ₗ[ℂ] H) (f : Y →ₗ[ℂ] H) : X →ₗ[ℂ] Y →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => inner ℂ (f y) (f' x))
    (fun x x' y => by simp)
    (fun c x y => by simp)
    (fun x y y' => by simp)
    (fun c x y => by simp [mul_comm])

theorem pairL_apply {X Y H : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (f' : X →ₗ[ℂ] H) (f : Y →ₗ[ℂ] H) (x : X) (y : Y) :
    pairL f' f x y = inner ℂ (f y) (f' x) := rfl

theorem pairL_invariant {G G' X Y H : Type} [Group G] [Group G'] [TopologicalSpace G'] [AddCommGroup X]
    [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : UnitaryRep G' H) (h : G → G') (σ : Representation ℂ G X) (π : Representation ℂ G Y)
    (f' : X →ₗ[ℂ] H) (f : Y →ₗ[ℂ] H) (hf' : ∀ g x, f' (σ g x) = R (h g) (f' x))
    (hf : ∀ g y, f (π g y) = R (h g) (f y)) (g : G) (x : X) (y : Y) :
    pairL f' f (σ g x) (π g y) = pairL f' f x y := by
  rw [pairL_apply, pairL_apply, hf, hf']
  exact UnitaryRep.inner_map_map _ _ _ _

theorem rhoL_def (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) (g : GL (Fin n) (w.adicCompletion K))
    (v : LL μ) :
    rhoL μ w g v = rightRegularRep (rationalGLOne (K := K) (n := n)) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) v :=
  rfl

end PositivityTheory.TfC.OccursIff

open PositivityTheory.TfC.OccursIff in
theorem PositivityTheory.TfC.OccursBasics_holds : UpperTheory.ConvolutionTheory.C.OccursBasics := by
  intro K _ _ n μ _ V w _ _ m _ hV
  obtain ⟨W, _, _, π, hπ, hπi, F, hF, hdense⟩ :=
    exists_localComponent_family K n μ V hV.le hV.closed hV.inv hV.ne_bot hV.irred w

  have key : ∀ σ : GlobalTheory.CuspRep.SmIrr (Gw n w), Occurs μ V w σ →
      GroundTheory.Automorphic.IsAdmissible σ.ρ ∧ Nonempty (σ.ρ.Equiv π) := by
    rintro σ ⟨f', hf'0, hf'V, hf'eq⟩
    obtain ⟨x₀, hx₀⟩ : ∃ x, f' x ≠ 0 := by
      by_contra h
      exact hf'0 (LinearMap.ext fun x => not_not.1 fun hx => h ⟨x, hx⟩)
    obtain ⟨f, hfF, z, hz⟩ := hdense (f' x₀) (hf'V x₀) hx₀
    have hfz : f z ≠ 0 := fun h => hz (by rw [h, inner_zero_left])
    refine admissible_and_equiv_of_pairing σ.ρ π (isSmooth_of_smIrr σ) σ.irred hπ hπi (pairL f' f) ?_ ?_
      (pairL f f) ?_ ?_
    · exact pairL_invariant (rightRegularRep (rationalGLOne (K := K) (n := n)) μ)
        (fun g => MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) σ.ρ π f' f
        (fun g x => (hf'eq g x).trans (rhoL_def μ w g _)) (hF f hfF).2
    · intro h
      apply hz
      have := LinearMap.congr_fun (LinearMap.congr_fun h x₀) z
      simpa [pairL_apply] using this
    · exact pairL_invariant (rightRegularRep (rationalGLOne (K := K) (n := n)) μ)
        (fun g => MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) π π f f
        (hF f hfF).2 (hF f hfF).2
    · intro h
      apply hfz
      have := LinearMap.congr_fun (LinearMap.congr_fun h z) z
      rw [pairL_apply, LinearMap.zero_apply, LinearMap.zero_apply, inner_self_eq_zero] at this
      exact this
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV.ne_bot
    obtain ⟨f, hfF, z, hz⟩ := hdense u hu hu0
    refine ⟨⟨W, π, fun v => hπ.1 v, hπi⟩, f, ?_, (hF f hfF).1, fun g x => (hF f hfF).2 g x⟩
    intro h
    apply hz
    rw [h, LinearMap.zero_apply, inner_zero_left]
  · intro σ σ' h h'
    obtain ⟨-, ⟨e⟩⟩ := key σ h
    obtain ⟨-, ⟨e'⟩⟩ := key σ' h'
    exact ⟨e.trans e'.symm⟩
  · intro σ h φ hφ
    obtain ⟨A, hA, hAf⟩ := exists_integralOp_of_admissible m σ.ρ (key σ h).1 φ hφ.1 hφ.2
    exact ⟨_, A, hA, hAf, rfl⟩
