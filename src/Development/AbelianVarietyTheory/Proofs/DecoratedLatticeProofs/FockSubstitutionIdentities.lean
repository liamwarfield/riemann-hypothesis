module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSubstitutionIdentities
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSubstitutionIdentities
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KJInf

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem sum_three_fintype_reverse {α β γ M : Type} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M] (f : α → β → γ → M) :
    ∑ x, ∑ y, ∑ z, f x y z = ∑ z, ∑ y, ∑ x, f x y z := by
  calc ∑ x, ∑ y, ∑ z, f x y z = ∑ x, ∑ z, ∑ y, f x y z := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, f x y z := Finset.sum_comm
    _ = ∑ z, ∑ y, ∑ x, f x y z := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum_four_fintype_permute {α β γ δ M : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid M] (f : α → β → γ → δ → M) :
    ∑ k, ∑ j, ∑ i, ∑ l, f k j i l = ∑ i, ∑ l, ∑ j, ∑ k, f k j i l := by
  calc ∑ k, ∑ j, ∑ i, ∑ l, f k j i l = ∑ i, ∑ j, ∑ k, ∑ l, f k j i l := sum_three_fintype_reverse _
    _ = ∑ i, ∑ j, ∑ l, ∑ k, f k j i l := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ j, ∑ k, f k j i l := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem mvZ_subY_comp (hab : a ≤ b) (g : ι → Matrix (Fin a) (Fin a) ℂ) (h y' : ι → Matrix (Fin b) (Fin b) ℂ) :
    (mvZ g h).comp (subY hab y') = (subY hab (fun τ => h τ * y' τ)).comp (lft g) := by
  apply MvPolynomial.algHom_ext
  intro v
  set_option synthInstance.maxHeartbeats 100000 in
    rw [AlgHom.comp_apply, AlgHom.comp_apply, subY, lft, aeval_X, aeval_X, map_sum, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, mvZ, subY, aeval_X, algHom_C, algebraMap_eq, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [sum_three_fintype_reverse]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem mvZ_mvZ_comp (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (h h' : ι → Matrix (Fin b) (Fin b) ℂ) :
    (mvZ g h).comp (mvZ g' h') = mvZ (fun τ => g' τ * g τ) (fun τ => h τ * h' τ) := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [AlgHom.comp_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, mvZ, aeval_X, algHom_C, algebraMap_eq, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [sum_four_fintype_permute]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem lft_lft_comp (g g' : ι → Matrix (Fin a) (Fin a) ℂ) :
    (lft g).comp (lft g') = lft (fun τ => g' τ * g τ) := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [AlgHom.comp_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, lft, aeval_X, algHom_C, algebraMap_eq, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem mvZ_one : mvZ (ι := ι) (a := a) (b := b) (fun _ => 1) (fun _ => 1) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [mvZ, Matrix.one_apply, apply_ite C, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem lft_one : lft (ι := ι) (a := a) (fun _ => 1) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [lft, Matrix.one_apply]

def scaleFP (t : ι → ℂ) : FP ι a b →ₐ[ℂ] FP ι a b :=
  aeval fun v => C (t v.1) * X v

theorem subY_smul (hab : a ≤ b) (t : ι → ℂ) (y' : ι → Matrix (Fin b) (Fin b) ℂ) :
    subY hab (fun τ => t τ • y' τ) = (scaleFP t).comp (subY hab y') := by
  apply MvPolynomial.algHom_ext
  intro v
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [subY, scaleFP, AlgHom.comp_apply, aeval_X, map_sum, map_mul, algHom_C,
    Matrix.smul_apply, smul_eq_mul, C_mul, algebraMap_eq]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

theorem scaleVariables_monomial (t : ι → ℂ) (m : (ι × Fin b × Fin a) →₀ ℕ) :
    scaleFP t (monomial m (1 : ℂ)) = (m.prod fun k n => t k.1 ^ n) • monomial m (1 : ℂ) := by
  rw [scaleFP, aeval_monomial, map_one, one_mul, ← C_mul', ← prod_X_pow_eq_monomial]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]

theorem jetL_monomial_one (c : ι → ℂ) (G : VCx ι a b → ℂ) (m : (ι × Fin b × Fin a) →₀ ℕ) :
    jetL c G (monomial m (1 : ℂ)) = jetC c G m := by
  have e : (monomial m (1 : ℂ) : FP ι a b) = basisMonomials (ι × Fin b × Fin a) ℂ m := by
    rw [coe_basisMonomials]
  rw [e, jetL, Module.Basis.constr_basis]

theorem jetL_comp_scale (c t : ι → ℂ) (G : VCx ι a b → ℂ) :
    (jetL c G).comp (scaleFP (a := a) (b := b) t).toLinearMap = jetL (fun τ => c τ * t τ) G := by
  refine (basisMonomials (ι × Fin b × Fin a) ℂ).ext fun m => ?_
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, coe_basisMonomials]
  rw [scaleVariables_monomial, map_smul, jetL_monomial_one, jetL_monomial_one, smul_eq_mul, jetC, jetC, ← mul_assoc]
  congr 1
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  ring

theorem evalAt_frDet (y : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) :
    evalAt y (frDet ℂ a τ : PY ι a) = (y τ).det := by
  rw [evalAt, frDet, RingHom.map_det]
  congr 1
  ext α s
  simp

theorem evalAt_mul_prod (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalAt y (F * ∏ τ, (frDet ℂ a τ : PY ι a)) = evalAt y F * ∏ τ, (y τ).det := by
  unfold evalAt
  rw [map_mul, map_prod]
  congr 1
  exact Finset.prod_congr rfl fun τ _ => evalAt_frDet y τ

theorem frDet_prod_ne_zero : (∏ τ, (frDet ℂ a τ : PY ι a)) ≠ 0 := by
  intro h
  have h1 : (1 : PY ι a) * ∏ τ, (frDet ℂ a τ : PY ι a) = 0 := by rw [one_mul, h]
  have h2 := congrArg (evalAt (fun _ : ι => (1 : Matrix (Fin a) (Fin a) ℂ))) h1
  rw [evalAt_mul_prod] at h2
  simp [evalAt] at h2

theorem eq_zero_of_invertible (F : PY ι a) (hF : ∀ y, IsInv y → evalAt y F = 0) : F = 0 := by
  have h0 : F * ∏ τ, (frDet ℂ a τ : PY ι a) = 0 := by
    apply MvPolynomial.funext
    intro x
    have key : eval x (F * ∏ τ, (frDet ℂ a τ : PY ι a)) =
        evalAt (fun τ => Matrix.of fun α s => x (τ, α, s)) (F * ∏ τ, (frDet ℂ a τ : PY ι a)) := rfl
    rw [map_zero, key, evalAt_mul_prod]
    by_cases hI : IsInv (fun τ => Matrix.of fun α s => x (τ, α, s))
    · rw [hF _ hI, zero_mul]
    · simp only [IsInv, not_forall] at hI
      obtain ⟨τ, hτ⟩ := hI
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) (by simpa using hτ), mul_zero]
  exact (mul_eq_zero.mp h0).resolve_right frDet_prod_ne_zero

theorem evalAt_lft_eq (g y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalAt y (lft g F) = evalAt (fun τ => g τ * y τ) F := by
  simp only [evalAt, lft]
  induction F using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, hp, aeval_X, eval_X, map_sum, eval_C, Matrix.mul_apply]

theorem substIdentities : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a ≤ b), (∀ (g : ι → Matrix (Fin a) (Fin a) ℂ) (h y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a), mvZ g h (subY hab y' F) = subY hab (fun τ => h τ * y' τ) (lft g F)) ∧ (∀ (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (h h' : ι → Matrix (Fin b) (Fin b) ℂ) (P : FP ι a b), mvZ g h (mvZ g' h' P) = mvZ (fun τ => g' τ * g τ) (fun τ => h τ * h' τ) P) ∧ (∀ P : FP ι a b, mvZ (fun _ => 1) (fun _ => 1) P = P) ∧ (∀ (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a), lft g (lft g' F) = lft (fun τ => g' τ * g τ) F) ∧ (∀ F : PY ι a, lft (fun _ => 1) F = F) ∧ (∀ (g y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a), evalAt y (lft g F) = evalAt (fun τ => g τ * y τ) F) ∧ (∀ F : PY ι a, (∀ y, IsInv y → evalAt y F = 0) → F = 0) ∧ ∀ (c t : ι → ℂ) (G : VCx ι a b → ℂ) (y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a), jetL c G (subY hab (fun τ => t τ • y' τ) F) = jetL (fun τ => c τ * t τ) G (subY hab y' F) := by
  intro ι _ a b hab
  refine ⟨fun g h y' F => ?_, fun g g' h h' P => ?_, fun P => ?_, fun g g' F => ?_, fun F => ?_,
    fun g y F => evalAt_lft_eq g y F, fun F hF => eq_zero_of_invertible F hF, fun c t G y' F => ?_⟩
  · have := DFunLike.congr_fun (mvZ_subY_comp hab g h y') F
    simpa only [AlgHom.comp_apply] using this
  · have := DFunLike.congr_fun (mvZ_mvZ_comp g g' h h') P
    simpa only [AlgHom.comp_apply] using this
  · rw [mvZ_one, AlgHom.id_apply]
  · have := DFunLike.congr_fun (lft_lft_comp g g') F
    simpa only [AlgHom.comp_apply] using this
  · rw [lft_one, AlgHom.id_apply]
  · rw [subY_smul, AlgHom.comp_apply, ← AlgHom.toLinearMap_apply, ← LinearMap.comp_apply, jetL_comp_scale]

end GlobalTheory.KJInf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSubstitutionIdentitiesStatement
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSubstitution_identities : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a ≤ b), (∀ (g : ι → Matrix (Fin a) (Fin a) ℂ) (h y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a), mvZ g h (subY hab y' F) = subY hab (fun τ => h τ * y' τ) (lft g F)) ∧ (∀ (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (h h' : ι → Matrix (Fin b) (Fin b) ℂ) (P : FP ι a b), mvZ g h (mvZ g' h' P) = mvZ (fun τ => g' τ * g τ) (fun τ => h τ * h' τ) P) ∧ (∀ P : FP ι a b, mvZ (fun _ => 1) (fun _ => 1) P = P) ∧ (∀ (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a), lft g (lft g' F) = lft (fun τ => g' τ * g τ) F) ∧ (∀ F : PY ι a, lft (fun _ => 1) F = F) ∧ (∀ (g y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a), evalAt y (lft g F) = evalAt (fun τ => g τ * y τ) F) ∧ (∀ F : PY ι a, (∀ y, IsInv y → evalAt y F = 0) → F = 0) ∧ ∀ (c t : ι → ℂ) (G : VCx ι a b → ℂ) (y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a), jetL c G (subY hab (fun τ => t τ • y' τ) F) = jetL (fun τ => c τ * t τ) G (subY hab y' F) := by
  first | exact @GlobalTheory.KJInf.substIdentities | exact GlobalTheory.KJInf.substIdentities | (intros; apply GlobalTheory.KJInf.substIdentities <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylDeterminantTwistTensorFiniteDimensionalStabl
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylDeterminantTwistTensorFiniteDimensionalStabl
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.KJInf.VnStable

variable {ι : Type} [Fintype ι] {a : ℕ}

theorem lft_rename (g : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) (p : MvPolynomial (Fin a × Fin a) ℂ) :
    lft g (rename (Prod.mk τ) p) = rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) p) := by
  have : (lft g).comp (rename (Prod.mk τ)) = (rename (Prod.mk τ)).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (n := a) (g τ)) := by
    apply MvPolynomial.algHom_ext
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      simp [lft, Formalism.GradedWeylDivisibility.rowAct, rename_X, aeval_X, map_sum]
  exact congrArg (fun φ : MvPolynomial (Fin a × Fin a) ℂ →ₐ[ℂ] PY ι a => φ p) this

theorem lft_ten (g : ι → Matrix (Fin a) (Fin a) ℂ) (f : ι → MvPolynomial (Fin a × Fin a) ℂ) :
    lft g (ten f) = ten (fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) (f τ)) := by
  simp only [ten, map_prod, lft_rename]

theorem lft_frDet (g : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) :
    lft g (frDet ℂ a τ : PY ι a) = (g τ).det • (frDet ℂ a τ : PY ι a) := by
  unfold frDet
  rw [AlgHom.map_det]
  have hM : (lft g).mapMatrix (Matrix.of fun α s : Fin a => (X (τ, α, s) : PY ι a)) =
      (g τ).map C * Matrix.of fun α s : Fin a => (X (τ, α, s) : PY ι a) := by
    ext α s
    simp [lft, Matrix.mul_apply]
  rw [hM, Matrix.det_mul, smul_eq_C_mul]
  congr 1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem prod_mem_prodS {A : Type} [CommRing A] [Algebra ℂ A] (s : Finset ι) (M : ι → Submodule ℂ A) (x : ι → A)
    (h : ∀ τ ∈ s, x τ ∈ M τ) : ∏ τ ∈ s, x τ ∈ ∏ τ ∈ s, M τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact Submodule.one_le.mp le_rfl
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact Submodule.mul_mem_mul (h i (Finset.mem_insert_self _ _))
      (ih fun τ hτ => h τ (Finset.mem_insert_of_mem hτ))

theorem fg_prodS {A : Type} [CommRing A] [Algebra ℂ A] (s : Finset ι) (M : ι → Submodule ℂ A)
    (h : ∀ τ, (M τ).FG) : (∏ τ ∈ s, M τ).FG := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  | insert i s hi ih => rw [Finset.prod_insert hi]; exact (h i).mul ih

theorem ten_mem_prod (lam : ι → DomWeight a) (f : ι → MvPolynomial (Fin a × Fin a) ℂ)
    (hf : ∀ τ, f τ ∈ delSq ℂ a (lam τ)) :
    ten f ∈ ∏ τ, (delSq ℂ a (lam τ)).map (rename (Prod.mk τ)).toLinearMap := by
  unfold ten
  exact prod_mem_prodS _ _ _ (fun τ _ => Submodule.mem_map_of_mem (hf τ))

theorem cspan_fd (lam : ι → DomWeight a) : FiniteDimensional ℂ (CSpan lam) := by
  have hP : (∏ τ, (delSq ℂ a (lam τ)).map (rename (Prod.mk τ)).toLinearMap).FG := by
    apply fg_prodS
    intro τ
    apply Submodule.FG.map
    haveI := (GlobalTheory.WeylUnitary.delSq_irreducible_unitary a (lam τ)).1
    exact (Submodule.fg_iff_finiteDimensional _).mpr inferInstance
  have hle : CSpan lam ≤ ∏ τ, (delSq ℂ a (lam τ)).map (rename (Prod.mk τ)).toLinearMap := by
    unfold CSpan
    rw [Submodule.span_le]
    rintro p ⟨f, hf, rfl⟩
    exact ten_mem_prod lam f hf
  haveI : FiniteDimensional ℂ ↥(∏ τ, ((delSq ℂ a (lam τ)).map (rename (Prod.mk τ)).toLinearMap : Submodule ℂ (PY ι a))) :=
    (Submodule.fg_iff_finiteDimensional _).mp hP
  exact Submodule.finiteDimensional_of_le hle

theorem lft_cspan (lam : ι → DomWeight a) (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    ∀ p ∈ CSpan lam, lft g p ∈ CSpan lam := by
  intro p hp
  unfold CSpan at hp ⊢
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    rw [lft_ten]
    exact Submodule.subset_span ⟨_, fun τ => (GlobalTheory.WeylUnitary.delSq_irreducible_unitary a (lam τ)).2.2.1 (g τ) (f τ) (hf τ), rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.KJInf.VnStable


open GlobalTheory.KJInf.VnStable in
theorem GlobalTheory.KJInf.vn_finiteDimensional_and_lft_mem : ∀ (ι : Type) [Fintype ι] (a : ℕ) (lam : ι → DomWeight a) (n : ι → ℕ),
    FiniteDimensional ℂ (Vn lam n) ∧ ∀ (g : ι → Matrix (Fin a) (Fin a) ℂ), ∀ F ∈ Vn lam n, lft g F ∈ Vn lam n := by
  intro ι _ a lam n
  haveI := cspan_fd lam
  refine ⟨?_, ?_⟩
  · unfold Vn; infer_instance
  · intro g F hF
    unfold Vn at hF ⊢
    obtain ⟨p, hp, rfl⟩ := hF
    have hD : lft g (∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ) = C (∏ τ, (g τ).det ^ n τ) * ∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ := by
      rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_pow, lft_frDet, smul_eq_C_mul, mul_pow, map_pow]
    refine ⟨(∏ τ, (g τ).det ^ n τ) • lft g p, Submodule.smul_mem _ _ (lft_cspan lam g p hp), ?_⟩
    simp only [LinearMap.mulRight_apply, map_mul, hD, smul_eq_C_mul]; ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylDeterminantTwistTensorFiniteDimensionalStablStatement
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable : ∀ (ι : Type) [Fintype ι] (a : ℕ) (lam : ι → DomWeight a) (n : ι → ℕ), FiniteDimensional ℂ (Vn lam n) ∧ ∀ (g : ι → Matrix (Fin a) (Fin a) ℂ), ∀ F ∈ Vn lam n, lft g F ∈ Vn lam n := by
  first | exact @GlobalTheory.KJInf.vn_finiteDimensional_and_lft_mem | exact GlobalTheory.KJInf.vn_finiteDimensional_and_lft_mem | (intros; apply GlobalTheory.KJInf.vn_finiteDimensional_and_lft_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPiTensorMvPolynomialEquivBlocks
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPiTensorMvPolynomialEquivBlocks
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.BlockPoly

variable (ι σ : Type) [Fintype ι] [DecidableEq ι]

noncomputable def blockMul :
    (ι → MvPolynomial σ ℂ) →ₘₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × σ) ℂ)).compLinearMap
    (fun τ => (rename (Prod.mk τ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (ι × σ) ℂ).toLinearMap)

theorem blockMul_apply (f : ι → MvPolynomial σ ℂ) :
    blockMul ι σ f = ∏ τ, rename (Prod.mk τ) (f τ) := by
  simp [blockMul]

noncomputable def expEquiv : (ι → σ →₀ ℕ) ≃ (ι × σ →₀ ℕ) :=
  Finsupp.equivFunOnFinite.symm.trans Finsupp.curryEquiv.symm

theorem expEquiv_apply (d : ι → σ →₀ ℕ) (a : ι) (b : σ) : expEquiv ι σ d (a, b) = d a b := by
  simp [expEquiv]

theorem sum_mapDomain_eq (d : ι → σ →₀ ℕ) :
    ∑ τ, (d τ).mapDomain (Prod.mk τ) = expEquiv ι σ d := by
  ext ⟨a, b⟩
  rw [expEquiv_apply, Finset.sum_apply', Finset.sum_eq_single a]
  · exact Finsupp.mapDomain_apply_of_injective (fun x y h => by simpa using h) _ _
  · intro τ _ hτ
    apply Finsupp.mapDomain_notin_range
    rintro ⟨c, hc⟩
    exact hτ (congrArg Prod.fst hc)
  · intro h; exact absurd (Finset.mem_univ a) h

theorem prod_rename_monomial (d : ι → σ →₀ ℕ) :
    ∏ τ, rename (Prod.mk τ) (monomial (d τ) (1 : ℂ)) = monomial (expEquiv ι σ d) 1 := by
  simp only [rename_monomial]
  rw [← monomial_sum_one, sum_mapDomain_eq]

noncomputable def blockEquiv :
    PiTensorProduct ℂ (fun _ : ι => MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
  (Basis.piTensorProduct (fun _ : ι => basisMonomials σ ℂ)).equiv
    (basisMonomials (ι × σ) ℂ) (expEquiv ι σ)

theorem blockEquiv_toLinearMap :
    (blockEquiv ι σ).toLinearMap = PiTensorProduct.lift (blockMul ι σ) := by
  refine (Basis.piTensorProduct (fun _ : ι => basisMonomials σ ℂ)).ext (fun p => ?_)
  rw [LinearEquiv.coe_coe, blockEquiv, Module.Basis.equiv_apply, Basis.piTensorProduct_apply,
    PiTensorProduct.lift.tprod, blockMul_apply]
  simp only [coe_basisMonomials]
  rw [prod_rename_monomial]

theorem blockEquiv_tprod (f : ι → MvPolynomial σ ℂ) :
    blockEquiv ι σ (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ) := by
  rw [← LinearEquiv.coe_coe, blockEquiv_toLinearMap, PiTensorProduct.lift.tprod, blockMul_apply]

theorem map_subtype_injective (U : ι → Submodule ℂ (MvPolynomial σ ℂ)) :
    Function.Injective (PiTensorProduct.map fun τ => (U τ).subtype) := by
  choose g hg using fun τ => LinearMap.exists_leftInverse_of_injective (U τ).subtype (U τ).ker_subtype
  have h : (PiTensorProduct.map g) ∘ₗ (PiTensorProduct.map fun τ => (U τ).subtype) =
      LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [hg]
    exact PiTensorProduct.map_id
  exact Function.LeftInverse.injective (g := PiTensorProduct.map g)
    (fun x => by simpa using LinearMap.congr_fun h x)

theorem exists_blockEquiv :
    ∀ (ι σ : Type) [Fintype ι] [DecidableEq ι], ∃ e : PiTensorProduct ℂ (fun _ : ι => MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ, (∀ f : ι → MvPolynomial σ ℂ, e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ)) ∧ ∀ U : ι → Submodule ℂ (MvPolynomial σ ℂ), Function.Injective (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) ∧ LinearMap.range (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) = Submodule.span ℂ {p | ∃ f : ι → MvPolynomial σ ℂ, (∀ τ, f τ ∈ U τ) ∧ p = ∏ τ, rename (Prod.mk τ) (f τ)} := by
  intro ι σ _ _
  refine ⟨blockEquiv ι σ, blockEquiv_tprod ι σ, fun U => ⟨?_, ?_⟩⟩
  · exact (blockEquiv ι σ).injective.comp (map_subtype_injective ι σ U)
  · rw [LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top, Submodule.map_span]
    congr 1
    ext p
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      refine ⟨fun τ => (g τ : MvPolynomial σ ℂ), fun τ => (g τ).2, ?_⟩
      simp [PiTensorProduct.map_tprod, blockEquiv_tprod]
    · rintro ⟨f, hf, rfl⟩
      refine ⟨PiTensorProduct.tprod ℂ (fun τ => (⟨f τ, hf τ⟩ : U τ)), ⟨_, rfl⟩, ?_⟩
      simp [PiTensorProduct.map_tprod, blockEquiv_tprod]

end GlobalTheory.BlockPoly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPiTensorMvPolynomialEquivBlocksStatement
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_piTensorMvPolynomialEquiv_blocks : ∀ (ι σ : Type) [Fintype ι] [DecidableEq ι], ∃ e : PiTensorProduct ℂ (fun _ : ι => MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ, (∀ f : ι → MvPolynomial σ ℂ, e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ)) ∧ ∀ U : ι → Submodule ℂ (MvPolynomial σ ℂ), Function.Injective (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) ∧ LinearMap.range (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) = Submodule.span ℂ {p | ∃ f : ι → MvPolynomial σ ℂ, (∀ τ, f τ ∈ U τ) ∧ p = ∏ τ, rename (Prod.mk τ) (f τ)} := by
  first | exact @GlobalTheory.BlockPoly.exists_blockEquiv | exact GlobalTheory.BlockPoly.exists_blockEquiv | (intros; apply GlobalTheory.BlockPoly.exists_blockEquiv <;> assumption)
end
end
