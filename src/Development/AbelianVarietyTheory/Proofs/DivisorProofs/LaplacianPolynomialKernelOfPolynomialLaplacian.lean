module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothFunAndRightDerivEqLeftInvariantVectorFieStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothFunAndRightDerivEqLeftInvariantVectorField
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GlobalTheory.GlVec

theorem isSmoothFun_and_rightDeriv_eq_vecF : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (glH E a).IsSmoothFun (fun y : glG E a => f (toL y.1.val)) ∧ ∀ X : glL E a, ContDiffOn ℝ ∞ (vecF E a (toL X.1) f) (invSet E a) ∧ (glH E a).rightDeriv X (fun y : glG E a => f (toL y.1.val)) = fun y : glG E a => vecF E a (toL X.1) f (toL y.1.val) := by
  intro E _ _ _ a f hf
  let Tl : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Lie E a :=
    { toFun := fun x => toL x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap Tl
  have hT : ∀ x, T x = toL x := fun _ => rfl
  have hval : ∀ (g : glG E a) (Y : glL E a), ((g * (glH E a).expG Y : glG E a) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val
      = (g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * NormedSpace.exp (Y : Matrix (Fin a) (Fin a) (Cinf E)) := by
    intro g Y; rfl
  have hsm : (glH E a).IsSmoothFun (fun y : glG E a => f (toL y.1.val)) := by
    rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro g
    have hin : ContDiff ℝ ∞ (fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val *
        NormedSpace.exp (Y : Matrix (Fin a) (Fin a) (Cinf E)))) :=
      T.contDiff.comp (contDiff_const.mul ((GroundTheory.Automorphic.contDiff_exp ℝ _).comp (glL E a).subtypeL.contDiff))
    have := hf.comp_contDiff hin (fun Y => by
      rw [hT, ← hval g Y]; exact val_mem_invSet _)
    have e : (fun Y : glL E a => f (toL ((g * (glH E a).expG Y : glG E a) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val)) =
        f ∘ fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val *
          NormedSpace.exp (Y : Matrix (Fin a) (Fin a) (Cinf E))) := by
      funext Y; simp only [Function.comp_apply, hT, hval]
    rw [e]
    exact this
  refine ⟨hsm, fun X => ⟨?_, ?_⟩⟩
  · exact (hf.fderiv_of_isOpen isOpen_invSet (by simp)).clm_apply (rmul (toL X.1)).contDiff.contDiffOn
  · funext y
    have h1 := IsExpLieAlgebra.hasDerivAt_rightDeriv (glH E a) hsm X y
    have hy : toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val ∈ invSet E a := val_mem_invSet _
    have hfd : HasFDerivAt f (fderiv ℝ f (toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val))
        (toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val) :=
      ((hf.contDiffAt (isOpen_invSet.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
    have hc : HasDerivAt (fun t : ℝ => T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val *
        NormedSpace.exp (t • (X : Matrix (Fin a) (Fin a) (Cinf E)))))
        (T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * (X : Matrix (Fin a) (Fin a) (Cinf E)))) 0 := by
      have h2 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (X : Matrix (Fin a) (Fin a) (Cinf E)) (0 : ℝ)).const_mul
        (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val
      simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h2
      exact T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
    have hc' : HasDerivAt (fun t : ℝ => T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val *
        NormedSpace.exp (t • (X : Matrix (Fin a) (Fin a) (Cinf E))))) _ 0 := hc
    have h3 := (show HasFDerivAt f (fderiv ℝ f (toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val))
        (T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * NormedSpace.exp ((0:ℝ) • (X : Matrix (Fin a) (Fin a) (Cinf E))))) by
          simpa [hT] using hfd).comp_hasDerivAt (0 : ℝ) hc'
    exact h1.unique h3

end GlobalTheory.GlVec
end

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (glH E a).IsSmoothFun (fun y : glG E a => f (toL y.1.val)) ∧ ∀ X : glL E a, ContDiffOn ℝ ∞ (vecF E a (toL X.1) f) (invSet E a) ∧ (glH E a).rightDeriv X (fun y : glG E a => f (toL y.1.val)) = fun y : glG E a => vecF E a (toL X.1) f (toL y.1.val) := by
  first | exact @GlobalTheory.GlVec.isSmoothFun_and_rightDeriv_eq_vecF | exact GlobalTheory.GlVec.isSmoothFun_and_rightDeriv_eq_vecF | (intros; apply GlobalTheory.GlVec.isSmoothFun_and_rightDeriv_eq_vecF <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealBasisGlLieAlgebraSumSqElementary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealBasisGlLieAlgebraSumSqElementary
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GlobalTheory

theorem glBasis_sum_sq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (glL E a)), ∀ (A : Type) [Ring A] [Algebra ℝ A] (ρ : glL E a →ₗ[ℝ] A), ∑ k, ρ (b k) * ρ (b k) = ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a, (ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 + ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2) := by
  intro E _ _ _ a
  classical
  let b0 : Module.Basis (Σ _ : InfinitePlace E, Fin 2) ℝ (Cinf E) := Pi.basis fun _ => Complex.basisOneI
  have hb0 : ∀ w s, b0 ⟨w, s⟩ = Pi.single w (Complex.basisOneI s) := by
    intro w s; simp [b0]
  let b1 := b0.matrix (Fin a) (Fin a)
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hu : ∀ _ : Fin a × Fin a × (Σ _ : InfinitePlace E, Fin 2), IsUnit (Real.sqrt 2) :=
    fun _ => IsUnit.mk0 _ hs.ne'
  let b2 := (b1.isUnitSMul hu).map (Submodule.topEquiv (R := ℝ) (M := Matrix (Fin a) (Fin a) (Cinf E))).symm
  let e := Fintype.equivFin (Fin a × Fin a × (Σ _ : InfinitePlace E, Fin 2))
  refine ⟨_, b2.reindex e, ?_⟩
  intro A _ _ ρ
  let F : InfinitePlace E → Fin a → Fin a → A := fun w i j =>
    ρ ⟨Matrix.single i j (Pi.single w 1), Submodule.mem_top⟩ ^ 2 +
      ρ ⟨Matrix.single i j (Pi.single w Complex.I), Submodule.mem_top⟩ ^ 2
  let G : InfinitePlace E → A := fun w => ∑ i, ∑ j, F w i j
  have hsm : ∀ (r : ℝ) (X : Matrix (Fin a) (Fin a) (Cinf E)),
      ρ ⟨r • X, Submodule.mem_top⟩ = r • ρ ⟨X, Submodule.mem_top⟩ := by
    intro r X
    rw [← map_smul]; rfl
  have hb2 : ∀ i j w s, ρ (b2 (i, j, ⟨w, s⟩)) * ρ (b2 (i, j, ⟨w, s⟩)) =
      ρ ⟨Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩ ^ 2 +
      ρ ⟨Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩ ^ 2 := by
    intro i j w s
    have : b2 (i, j, ⟨w, s⟩) = ⟨Real.sqrt 2 • Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩ := by
      apply Subtype.ext
      simp [b2, b1, Module.Basis.isUnitSMul_apply, hb0]
    rw [this, hsm, smul_mul_smul, Real.mul_self_sqrt (by norm_num), two_smul, sq]
  have hL : ∑ k, ρ (b2.reindex e k) * ρ (b2.reindex e k) = ∑ w, (G w + G w) := by
    simp only [Module.Basis.reindex_apply]
    rw [Equiv.sum_comp e.symm (fun x => ρ (b2 x) * ρ (b2 x))]
    simp only [Fintype.sum_prod_type, Fintype.sum_sigma, Fin.sum_univ_two, hb2, Complex.coe_basisOneI,
      Matrix.cons_val_zero, Matrix.cons_val_one, G, F]
    simp only [← Finset.sum_add_distrib]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
    abel
  have hτ : ∀ τ : E →+* ℂ, ∀ i j,
      ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 +
        ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2 = F (InfinitePlace.mk τ) i j := by
    intro τ i j
    have hA1 : atEmb τ 1 = Pi.single (InfinitePlace.mk τ) 1 := by
      unfold atEmb; split_ifs <;> simp
    have hAI : ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2 =
        ρ ⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) Complex.I), Submodule.mem_top⟩ ^ 2 := by
      unfold atEmb
      split_ifs with h
      · rfl
      · have h1 : (⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) (starRingEnd ℂ Complex.I)), Submodule.mem_top⟩ : glL E a) =
            -⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) Complex.I), Submodule.mem_top⟩ := by
          apply Subtype.ext
          simp [Pi.single_neg, Matrix.single_neg]
        rw [h1, map_neg, neg_sq]
    simp only [F, hAI, hA1]
  have hR : ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
      (ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 +
        ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2) = ∑ w, (G w + G w) := by
    simp only [hτ]
    change ∑ τ : E →+* ℂ, G (InfinitePlace.mk τ) = _
    rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun τ => G (InfinitePlace.mk τ))]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => G w) (fun τ hτ' => by rw [(Finset.mem_filter.1 hτ').2]),
      Finset.sum_const, InfinitePlace.card_filter_mk_eq]
    have : w.mult = 2 := by
      simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]
    rw [this, two_smul]
  rw [hL, hR]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealBasisGlLieAlgebraSumSqElementaryStatement
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realBasis_glLieAlgebra_sum_sq_elementary : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (glL E a)), ∀ (A : Type) [Ring A] [Algebra ℝ A] (ρ : glL E a →ₗ[ℝ] A), ∑ k, ρ (b k) * ρ (b k) = ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a, (ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 + ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2) := by
  first | exact @GlobalTheory.glBasis_sum_sq | exact GlobalTheory.glBasis_sum_sq | (intros; apply GlobalTheory.glBasis_sum_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsRestrictionSmoothRightDerivEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsRestrictionSmoothRightDerivEq
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic NormedSpace
open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GlobalTheory.HCA

theorem glRes_smooth_rightDeriv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    ∀ φ : Sm E a, ∀ x, (glH E a).IsSmoothFun (glRes φ.1 x) ∧
      ∀ X : glL E a, (glH E a).rightDeriv X (glRes φ.1 x) = glRes (lie E a (toL X.1) φ).1 x := by
  intro E _ _ _ a φ x
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  have hT : ∀ M, T M = toL M := fun _ => rfl
  have key : ∀ (g : glG E a) (Y : glL E a), glRes φ.1 x (g * (glH E a).expG Y) =
      chart φ.1 x (T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E)))) := by
    intro g Y
    rw [hT]
    exact (chart_val φ.1 x ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) * ((glH E a).expG Y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ))).symm
  have hs : (glH E a).IsSmoothFun (glRes φ.1 x) := by
    rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro g
    have e : (fun Y : glL E a => glRes φ.1 x (g * (glH E a).expG Y)) =
        chart φ.1 x ∘ fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E))) :=
      funext (key g)
    rw [e]
    have h1 : ContDiff ℝ ∞ (fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E)))) :=
      T.contDiff.comp (contDiff_const.mul ((contDiff_exp ℝ _).comp (glL E a).subtypeL.contDiff))
    exact (φ.2 x).comp_contDiff h1 fun Y =>
      ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) * ((glH E a).expG Y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)).isUnit
  refine ⟨hs, fun X => funext fun g => ?_⟩
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (X : Matrix (Fin a) (Fin a) (Cinf E)) (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  have hc : HasDerivAt (fun t : ℝ => toL (((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) : Matrix (Fin a) (Fin a) (Cinf E)))
      (toL X.1) 0 := T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h0 : (((glH E a).expG ((0 : ℝ) • X) : glG E a) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) = 1 := by
    ext : 1
    simp
  have h3 := hasDerivAt_curve φ (x * infGL E a (g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ))
    (fun t => ((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)) (toL X.1) h0 hc
  have ef : (fun t : ℝ => glRes φ.1 x (g * (glH E a).expG (t • X))) = fun t : ℝ =>
      φ.1 (x * infGL E a (g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) *
        infGL E a ((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)) := by
    funext t
    simp only [glRes, Subgroup.coe_mul, map_mul, mul_assoc]
  have h4 := (glH E a).hasDerivAt_rightDeriv hs X g
  rw [ef] at h4
  exact h4.unique h3

end GlobalTheory.HCA

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsRestrictionSmoothRightDerivEqStatement
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ φ : Sm E a, ∀ x, (glH E a).IsSmoothFun (glRes φ.1 x) ∧ ∀ X : glL E a, (glH E a).rightDeriv X (glRes φ.1 x) = glRes (lie E a (toL X.1) φ).1 x := by
  first | exact @GlobalTheory.HCA.glRes_smooth_rightDeriv | exact GlobalTheory.HCA.glRes_smooth_rightDeriv | (intros; apply GlobalTheory.HCA.glRes_smooth_rightDeriv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplacianPolynomialKernelOfPolynomialLaplacian
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
noncomputable section

namespace GlobalTheory.HCA

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def glRho : glL E a →ₗ[ℝ] Module.End ℂ ((glH E a).smoothFuns (F := ℂ)) where
  toFun X := (glH E a).rightDerivEnd X
  map_add' X Y := by ext1 f; ext1; exact (glH E a).rightDeriv_add_left _ _ _
  map_smul' r X := by ext1 f; ext1; exact (glH E a).rightDeriv_smul_left r _ _


variable (E a) in
def glLap : Module.End ℂ ((glH E a).smoothFuns (F := ℂ)) :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
    ((glH E a).rightDerivEnd ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 +
      (glH E a).rightDerivEnd ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2)

theorem aeval_intertwine {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (Φ : M →ₗ[ℂ] N) (A : Module.End ℂ M) (B : Module.End ℂ N) (h : ∀ x, Φ (A x) = B (Φ x))
    (p : Polynomial ℂ) (x : M) : Φ (Polynomial.aeval A p x) = Polynomial.aeval B p (Φ x) := by
  have hp : ∀ n : ℕ, ∀ x, Φ ((A ^ n) x) = (B ^ n) (Φ x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]
  induction p using Polynomial.induction_on' with
  | add p q hp' hq' => simp only [map_add (f := _), LinearMap.add_apply, hp', hq']
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, hp]

theorem contDiffOn_finsum {ι : Type*} (s : Finset ι) (g : ι → Lie E a → ℂ)
    (hg : ∀ i ∈ s, ContDiffOn ℝ ∞ (g i) (invSet E a)) : ContDiffOn ℝ ∞ (∑ i ∈ s, g i) (invSet E a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact contDiffOn_const (c := (0 : ℂ))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hg i (Finset.mem_insert_self _ _)).add (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

theorem rightDeriv_glF {f : Lie E a → ℂ} (hf : ContDiffOn ℝ ∞ f (invSet E a)) (X : glL E a)
    (g : (glH E a).smoothFuns (F := ℂ)) (hg : g.1 = fun y : glG E a => f (toL y.1.val)) :
    ((glH E a).rightDerivEnd X g).1 = fun y : glG E a => vecF E a (toL X.1) f (toL y.1.val) := by
  rw [IsExpLieAlgebra.coe_rightDerivEnd, hg]
  exact ((GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).2 X).2

theorem glLap_glF {f : Lie E a → ℂ} (hf : ContDiffOn ℝ ∞ f (invSet E a))
    (g : (glH E a).smoothFuns (F := ℂ)) (hg : g.1 = fun y : glG E a => f (toL y.1.val)) :
    (glLap E a g).1 = (fun y : glG E a => lapF E a f (toL y.1.val)) ∧ ContDiffOn ℝ ∞ (lapF E a f) (invSet E a) := by
  have key : ∀ X : glL E a, ((glH E a).rightDerivEnd X ((glH E a).rightDerivEnd X g)).1 =
      fun y : glG E a => vecF E a (toL X.1) (vecF E a (toL X.1) f) (toL y.1.val) := fun X =>
    rightDeriv_glF ((GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).2 X).1 X _ (rightDeriv_glF hf X g hg)
  have hv : ∀ X : Lie E a, ContDiffOn ℝ ∞ (vecF E a X f) (invSet E a) := fun X =>
    ((GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).2 ⟨Matrix.of X, Submodule.mem_top⟩).1
  have hvv : ∀ X : Lie E a, ContDiffOn ℝ ∞ (vecF E a X (vecF E a X f)) (invSet E a) := fun X =>
    ((GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a _ (hv X)).2 ⟨Matrix.of X, Submodule.mem_top⟩).1
  refine ⟨?_, ?_⟩
  · simp only [glLap, LinearMap.sum_apply, LinearMap.add_apply, sq, Module.End.mul_apply,
      Submodule.coe_sum, Submodule.coe_add, key]
    funext y
    simp only [lapF, Finset.sum_apply, Pi.add_apply]
  · unfold lapF
    exact contDiffOn_finsum _ _ fun τ _ => contDiffOn_finsum _ _ fun i _ => contDiffOn_finsum _ _ fun j _ =>
      (hvv _).add (hvv _)

theorem glLap_pow_glF (k : ℕ) : ∀ {f : Lie E a → ℂ}, ContDiffOn ℝ ∞ f (invSet E a) →
    ∀ (g : (glH E a).smoothFuns (F := ℂ)), g.1 = (fun y : glG E a => f (toL y.1.val)) →
    ((glLap E a ^ k) g).1 = (fun y : glG E a => (lapF E a)^[k] f (toL y.1.val)) ∧
      ContDiffOn ℝ ∞ ((lapF E a)^[k] f) (invSet E a) := by
  induction k with
  | zero => intro f hf g hg; exact ⟨hg, hf⟩
  | succ k ih =>
    intro f hf g hg
    obtain ⟨h1, h2⟩ := glLap_glF hf g hg
    rw [pow_succ, Module.End.mul_apply, Function.iterate_succ_apply]
    exact ih h2 _ h1

theorem glLap_glRes (φ : Sm E a) (x : GA E a) :
    glLap E a ⟨glRes φ.1 x, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a φ x).1⟩ = ⟨glRes (lapOp E a φ).1 x, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a _ x).1⟩ := by
  have key : ∀ (i j : Fin a) (z : Cinf E) (ψ : Sm E a),
      (glH E a).rightDerivEnd ⟨Matrix.single i j z, Submodule.mem_top⟩ ⟨glRes ψ.1 x, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a ψ x).1⟩ =
        ⟨glRes (lieS E a i j z ψ).1 x, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a _ x).1⟩ := by
    intro i j z ψ
    apply Subtype.ext
    rw [IsExpLieAlgebra.coe_rightDerivEnd, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a ψ x).2, lieS_apply]
  apply Subtype.ext
  simp only [glLap, lapOp, LinearMap.sum_apply, LinearMap.add_apply, sq, Module.End.mul_apply,
    key, Submodule.coe_sum, Submodule.coe_add]
  funext y
  simp only [glRes, Finset.sum_apply, Pi.add_apply, Submodule.coe_sum, Submodule.coe_add]

theorem solG_of_polyLap : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ p : Polynomial ℂ, p ≠ 0 → ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (glL E a)) (P : Polynomial ℂ), P.Monic ∧ (∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (∀ y ∈ invSet E a, polyF E a p f y = 0) → (fun y : glG E a => f (toL y.1.val)) ∈ solG (glH E a) b P) ∧ ∀ φ : Sm E a, Polynomial.aeval (lapOp E a) p φ = 0 → ∀ x, glRes φ.1 x ∈ solG (glH E a) b P := by
  intro E _ _ _ a p hp
  obtain ⟨d, b, hb⟩ := GlobalTheory.T.exists_realBasis_glLieAlgebra_sum_sq_elementary E a
  have hΔ : (∑ i, (glH E a).rightDerivEnd (F := ℂ) (b i) * (glH E a).rightDerivEnd (F := ℂ) (b i)) = glLap E a := by
    rw [glLap]
    simp only [sq]
    exact hb _ (glRho E a)
  refine ⟨d, b, p * Polynomial.C p.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hp, ?_, ?_⟩
  · have hP : ∀ g, Polynomial.aeval (glLap E a) (p * Polynomial.C p.leadingCoeff⁻¹) g =
        p.leadingCoeff⁻¹ • Polynomial.aeval (glLap E a) p g := by
      intro g
      rw [Polynomial.aeval_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
    intro f hf h0
    rw [mem_solG]
    refine ⟨(GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).1, ?_⟩
    rw [hΔ, hP]
    have hk : ∀ k : ℕ, ((glLap E a ^ k) ⟨_, (GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).1⟩).1 =
        (fun y : glG E a => (lapF E a)^[k] f (toL y.1.val)) := fun k => (glLap_pow_glF k hf _ rfl).1
    suffices h : Polynomial.aeval (glLap E a) p ⟨_, (GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).1⟩ = 0 by rw [h, smul_zero]
    apply Subtype.ext
    rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum]
    funext y
    simp only [Finset.sum_apply, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, hk, Submodule.coe_zero,
      Pi.zero_apply]
    have := h0 _ (val_mem_invSet y.1)
    simpa only [polyF, Finset.sum_apply, Pi.smul_apply] using this
  · intro φ hφ x
    rw [mem_solG]
    refine ⟨(GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a φ x).1, ?_⟩
    rw [hΔ, Polynomial.aeval_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
    let Φ : Sm E a →ₗ[ℂ] (glH E a).smoothFuns (F := ℂ) :=
      { toFun := fun ψ => ⟨glRes ψ.1 x, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a ψ x).1⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have e := aeval_intertwine Φ (lapOp E a) (glLap E a) (fun ψ => (glLap_glRes ψ x).symm) p φ
    change p.leadingCoeff⁻¹ • Polynomial.aeval (glLap E a) p (Φ φ) = 0
    rw [← e, hφ, map_zero, smul_zero]

end GlobalTheory.HCA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplacianPolynomialKernelOfPolynomialLaplacianStatement
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laplacianPolynomialKernel_of_polynomial_laplacian : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ p : Polynomial ℂ, p ≠ 0 → ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (glL E a)) (P : Polynomial ℂ), P.Monic ∧ (∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (∀ y ∈ invSet E a, polyF E a p f y = 0) → (fun y : glG E a => f (toL y.1.val)) ∈ solG (glH E a) b P) ∧ ∀ φ : Sm E a, Polynomial.aeval (lapOp E a) p φ = 0 → ∀ x, glRes φ.1 x ∈ solG (glH E a) b P := by
  first | exact @GlobalTheory.HCA.solG_of_polyLap | exact GlobalTheory.HCA.solG_of_polyLap | (intros; apply GlobalTheory.HCA.solG_of_polyLap <;> assumption)
end
