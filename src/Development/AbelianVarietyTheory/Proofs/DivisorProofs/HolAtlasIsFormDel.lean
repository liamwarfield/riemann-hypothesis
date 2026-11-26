module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormBlockEmbLeftInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtReprPullbackHolomorphicFderiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtReprPullbackHolomorphicFderiv
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm

variable {n : ℕ}

theorem differentiableAt_repr_map_toLin' {M : V n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {v : V n}
    (hM : ∀ i j, DifferentiableAt ℝ (fun w => M w i j) v) (γ : Alt n) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun w => (bas n).repr (ExteriorAlgebra.map (Matrix.toLin' (M w)) γ) S) v := by
  induction γ using ExteriorAlgebra.induction generalizing S with
  | algebraMap r =>
    simp only [AlgHom.commutes]
    exact differentiableAt_const _
  | ι x =>
    simp only [ExteriorAlgebra.map_apply_ι]
    let ℓ : (Fin n ⊕ Fin n → ℂ) →ₗ[ℂ] ℂ :=
      Finsupp.lapply S ∘ₗ (bas n).repr.toLinearMap ∘ₗ ExteriorAlgebra.ι ℂ
    have hu : DifferentiableAt ℝ (fun w => Matrix.toLin' (M w) x) v := by
      simp only [Matrix.toLin'_apply]
      refine differentiableAt_pi.2 fun i => ?_
      simp only [mulVec, dotProduct]
      exact DifferentiableAt.fun_sum fun j _ => (hM i j).mul_const _
    exact ((LinearMap.toContinuousLinearMap ℓ).restrictScalars ℝ).differentiableAt.comp v hu
  | mul a b ha hb =>
    have e : (fun w => (bas n).repr (ExteriorAlgebra.map (Matrix.toLin' (M w)) (a * b)) S) = fun w =>
        ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)), (bas n).repr (ExteriorAlgebra.map (Matrix.toLin' (M w)) a) p.1 *
          (bas n).repr (ExteriorAlgebra.map (Matrix.toLin' (M w)) b) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S :=
      funext fun w => by rw [map_mul, FormMul.repr_mul]
    rw [e]
    exact DifferentiableAt.fun_sum fun p _ => ((ha p.1).mul (hb p.2)).mul_const _
  | add a b ha hb =>
    simp only [map_add (f := _), Finsupp.add_apply]
    exact (ha S).add (hb S)

theorem differentiableAt_repr_pull_fderiv : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n}
    {v : ReciprocityTheory.L2DbarEstimates.V n}, ContDiffAt ℂ 2 φ v → ∀ (γ : GlobalTheory.CxForm.Alt n) (S : Finset (Fin (n + n))),
    DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (GlobalTheory.CxForm.pull (fderiv ℂ φ w) γ) S) v := by
  intro n φ v h γ S
  have hd : DifferentiableAt ℂ (fderiv ℂ φ) v :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he (b a : Fin n) : DifferentiableAt ℝ (fun w => fderiv ℂ φ w (coordVec b) a) v :=
    (((EuclideanSpace.proj a : V n →L[ℂ] ℂ).differentiableAt).comp v
      (hd.clm_apply (differentiableAt_const (coordVec b)))).restrictScalars ℝ
  have hc (b a : Fin n) : DifferentiableAt ℝ (fun w => conj (fderiv ℂ φ w (coordVec b) a)) v :=
    Complex.conjCLE.differentiableAt.comp v (he b a)
  refine differentiableAt_repr_map_toLin' (M := fun w => fromBlocks (of fun b a => fderiv ℂ φ w (coordVec b) a) 0 0
    (of fun b a => conj (fderiv ℂ φ w (coordVec b) a))) ?_ γ S
  rintro (i | i) (j | j)
  · simpa only [fromBlocks_apply₁₁, of_apply] using he i j
  · simp only [fromBlocks_apply₁₂, Matrix.zero_apply]; exact differentiableAt_const _
  · simp only [fromBlocks_apply₂₁, Matrix.zero_apply]; exact differentiableAt_const _
  · simpa only [fromBlocks_apply₂₂, of_apply] using hc i j

end GlobalTheory.CxForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtReprPullbackHolomorphicFderivStatement
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableAt_repr_pullback_holomorphic_fderiv : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n} {v : ReciprocityTheory.L2DbarEstimates.V n}, ContDiffAt ℂ 2 φ v → ∀ (γ : GlobalTheory.CxForm.Alt n) (S : Finset (Fin (n + n))), DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (GlobalTheory.CxForm.pull (fderiv ℂ φ w) γ) S) v := by
  first | exact @GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv | exact GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv | (intros; apply GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelPullbackFderivFormEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelPullbackFderivFormEqZero
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm.DelVanish

variable {n : ℕ}

theorem delAt_const (c : Alt n) (v : V n) : delAt (fun _ => c) v = 0 := by
  simp [delAt, coefwise]

theorem delAt_add {F G : V n → Alt n} {v : V n}
    (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    delAt (fun x => F x + G x) v = delAt F v + delAt G v := by
  have key (a : Fin n) : coefwise (fun f => del f v (coordVec a)) (fun x => F x + G x) =
      coefwise (fun f => del f v (coordVec a)) F + coefwise (fun f => del f v (coordVec a)) G := by
    simp only [coefwise, ← Finset.sum_add_distrib, ← add_smul]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [map_add (f := _), Finsupp.add_apply]
    rw [del_add (hF S) (hG S), ContinuousLinearMap.add_apply]
  simp only [delAt, key, mul_add, Finset.sum_add_distrib]

theorem repr_ι (x : Fin n ⊕ Fin n → ℂ) (S : Finset (Fin (n + n))) :
    (bas n).repr (ExteriorAlgebra.ι ℂ x) S =
      ∑ i, x i * (bas n).repr (ExteriorAlgebra.ι ℂ (Pi.single i 1)) S := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (Pi.single i (x i) : Fin n ⊕ Fin n → ℂ) = x i • Pi.single i 1 by
    ext j; simp [Pi.single_apply]]
  simp

theorem del_mul_const {f : V n → ℂ} {v : V n} (hf : DifferentiableAt ℝ f v) (k : ℂ) (e : V n) :
    del (fun w => f w * k) v e = del f v e * k := by
  rw [del_mul hf (differentiableAt_const k), del_const]; simp

theorem delAt_ι {u : V n → (Fin n ⊕ Fin n → ℂ)} {v : V n}
    (hu : ∀ i, DifferentiableAt ℝ (fun w => u w i) v) :
    delAt (fun w => ExteriorAlgebra.ι ℂ (u w)) v =
      ∑ a, dz a * ExteriorAlgebra.ι ℂ (fun i => del (fun w => u w i) v (coordVec a)) := by
  refine Finset.sum_congr rfl fun a _ => congrArg _ ((bas n).ext_elem fun S => ?_)
  have e : (fun x => (bas n).repr (ExteriorAlgebra.ι ℂ (u x)) S) = fun x =>
      ∑ i, u x i * (bas n).repr (ExteriorAlgebra.ι ℂ (Pi.single i 1)) S := funext fun x => repr_ι _ _
  rw [FormMul.repr_coefwise, repr_ι, e]
  rw [del_sum (fun i _ => (hu i).mul_const _), ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => del_mul_const (hu i) _ _

theorem sum_symm_dz_mul (s : Fin n → Fin n → ℂ) (hs : ∀ a b, s a b = s b a) :
    ∑ a, ∑ b, s a b • (dz a * dz b) = 0 := by
  set X := ∑ a, ∑ b, s a b • (dz a * dz b) with hX
  have h : X = -X := by
    conv_lhs => rw [hX, Finset.sum_comm]
    simp only [hX, ← Finset.sum_neg_distrib, ← smul_neg]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hs, dz, dz]
    congr 1
    apply eq_neg_of_add_eq_zero_left
    exact ExteriorAlgebra.ι_add_mul_swap _ _
  have h2 : (2 : ℂ) • X = 0 := by
    rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel X
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem delAt_pull_fderiv_ι {φ : V n → V n} {v : V n} (hφ : ContDiffAt ℂ 2 φ v) (m : Fin n ⊕ Fin n → ℂ) :
    delAt (fun w => pull (fderiv ℂ φ w) (ExteriorAlgebra.ι ℂ m)) v = 0 := by
  have hJ : DifferentiableAt ℂ (fderiv ℂ φ) v :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hE (b c : Fin n) : DifferentiableAt ℂ (fun w => fderiv ℂ φ w (coordVec b) c) v :=
    by
      have := (EuclideanSpace.proj (𝕜 := ℂ) c).differentiableAt.comp v
        (hJ.clm_apply (differentiableAt_const (coordVec b)))
      simpa [Function.comp_def] using this
  have hEr (b c : Fin n) : DifferentiableAt ℝ (fun w => fderiv ℂ φ w (coordVec b) c) v :=
    (hE b c).restrictScalars ℝ
  have hEc (b c : Fin n) : DifferentiableAt ℝ (fun w => conj (fderiv ℂ φ w (coordVec b) c)) v := by
    have := Complex.conjCLE.differentiableAt.comp v (hEr b c)
    simpa [Function.comp_def] using this
  have hdel (a b c : Fin n) : del (fun w => fderiv ℂ φ w (coordVec b) c) v (coordVec a) =
      fderiv ℂ (fderiv ℂ φ) v (coordVec a) (coordVec b) c := by
    have := del_clm_comp ((EuclideanSpace.proj c).comp (ContinuousLinearMap.apply ℂ (V n) (coordVec b)))
      (hJ.restrictScalars ℝ) (coordVec a)
    rw [del_eq_fderiv hJ] at this
    exact this
  have hdelc (a b c : Fin n) : del (fun w => conj (fderiv ℂ φ w (coordVec b) c)) v (coordVec a) = 0 := by
    rw [del_conj, dbar_eq_zero (hE b c)]; simp
  have hsymm : IsSymmSndFDerivAt ℂ φ v := hφ.isSymmSndFDerivAt (by simp)
  have hF : (fun w => pull (fderiv ℂ φ w) (ExteriorAlgebra.ι ℂ m)) = fun w => ExteriorAlgebra.ι ℂ
      (Sum.elim (fun b => ∑ c, fderiv ℂ φ w (coordVec b) c * m (.inl c))
        (fun b => ∑ c, conj (fderiv ℂ φ w (coordVec b) c) * m (.inr c))) := by
    funext w
    rw [pull, ExteriorAlgebra.map_apply_ι]
    congr 1
    funext i
    rcases i with b | b <;> simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  have hu : ∀ i, DifferentiableAt ℝ (fun w => Sum.elim (fun b => ∑ c, fderiv ℂ φ w (coordVec b) c * m (.inl c))
      (fun b => ∑ c, conj (fderiv ℂ φ w (coordVec b) c) * m (.inr c)) i) v := by
    rintro (b | b)
    · simpa using DifferentiableAt.fun_sum (u := Finset.univ) fun c _ => (hEr b c).mul_const (m (.inl c))
    · simpa using DifferentiableAt.fun_sum (u := Finset.univ) fun c _ => (hEc b c).mul_const (m (.inr c))
  set s : Fin n → Fin n → ℂ := fun a b => ∑ c, fderiv ℂ (fderiv ℂ φ) v (coordVec a) (coordVec b) c * m (.inl c)
    with hs
  have hw (a : Fin n) : (fun i => del (fun w => Sum.elim (fun b => ∑ c, fderiv ℂ φ w (coordVec b) c * m (.inl c))
      (fun b => ∑ c, conj (fderiv ℂ φ w (coordVec b) c) * m (.inr c)) i) v (coordVec a)) =
      ∑ b, s a b • Pi.single (Sum.inl b) 1 := by
    funext i
    rcases i with b | b
    · simp only [Sum.elim_inl]
      rw [del_sum (fun c _ => (hEr b c).mul_const _), ContinuousLinearMap.sum_apply]
      simp [del_mul_const (hEr _ _), hdel, Finset.sum_apply, Pi.single_apply, hs]
    · simp only [Sum.elim_inr]
      rw [del_sum (fun c _ => (hEc b c).mul_const _), ContinuousLinearMap.sum_apply]
      simp [del_mul_const (hEc _ _), hdelc, Finset.sum_apply, Pi.single_apply]
  rw [hF, delAt_ι hu]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hw, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
  exact sum_symm_dz_mul s fun a b => by simp only [hs, hsymm (coordVec a) (coordVec b)]

theorem delAt_pull_fderiv : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n} {v : ReciprocityTheory.L2DbarEstimates.V n},
    ContDiffAt ℂ 2 φ v → ∀ γ : GlobalTheory.CxForm.Alt n,
      GlobalTheory.CxForm.delAt (fun w => GlobalTheory.CxForm.pull (fderiv ℂ φ w) γ) v = 0 := by
  intro n φ v hφ γ
  have hD := fun γ S => GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv hφ γ S
  induction γ using ExteriorAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes]; exact delAt_const _ _
  | ι m => exact delAt_pull_fderiv_ι hφ m
  | mul a b ha hb =>
    obtain ⟨y, hy⟩ := FormMul.delAt_mul (hD a) (hD b)
    simp only [map_mul]
    rw [hy, ha, hb, zero_mul, mul_zero, add_zero]
  | add a b ha hb =>
    simp only [map_add (f := _)]
    rw [delAt_add (hD a) (hD b), ha, hb, add_zero]

end GlobalTheory.CxForm.DelVanish
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelPullbackFderivFormEqZeroStatement
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicDel_pullback_fderiv_form_eq_zero : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n} {v : ReciprocityTheory.L2DbarEstimates.V n}, ContDiffAt ℂ 2 φ v → ∀ γ : GlobalTheory.CxForm.Alt n, GlobalTheory.CxForm.delAt (fun w => GlobalTheory.CxForm.pull (fderiv ℂ φ w) γ) v = 0 := by
  first | exact @GlobalTheory.CxForm.DelVanish.delAt_pull_fderiv | exact GlobalTheory.CxForm.DelVanish.delAt_pull_fderiv | (intros; apply GlobalTheory.CxForm.DelVanish.delAt_pull_fderiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDifferentialOneFormCompHolomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDifferentialOneFormCompHolomorphic
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DelForm

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

theorem sum_coord_smul_coordVec {n : ℕ} (w : V n) : ∑ b, w b • coordVec b = w := by
  ext i
  simp [coordVec, Pi.single_apply]

theorem dOne_comp_holo {n : ℕ} {φ : V n → V n} {c : V n → ℂ} {v : V n}
    (hc : DifferentiableAt ℝ c (φ v)) (hφ : DifferentiableAt ℂ φ v) :
    dOne (fun w => c (φ w)) v = pull (fderiv ℂ φ v) (dOne c (φ v)) := by
  have key (a : Fin n) : del (fun w => c (φ w)) v (coordVec a) =
      ∑ b, fderiv ℂ φ v (coordVec a) b * del c (φ v) (coordVec b) := by
    rw [del_comp_holo hc hφ]
    conv_lhs => rw [← sum_coord_smul_coordVec (fderiv ℂ φ v (coordVec a))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul, smul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dOne, map_sum, map_smul, (pull_dz _ _).1, Finset.smul_sum, smul_smul, key, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]

end GlobalTheory.CxForm.DelForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDifferentialOneFormCompHolomorphicStatement
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicDifferentialOneForm_comp_holomorphic : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n} {c : ReciprocityTheory.L2DbarEstimates.V n → ℂ} {v : ReciprocityTheory.L2DbarEstimates.V n}, DifferentiableAt ℝ c (φ v) → DifferentiableAt ℂ φ v → GlobalTheory.CxForm.DelForm.dOne (fun w => c (φ w)) v = GlobalTheory.CxForm.pull (fderiv ℂ φ v) (GlobalTheory.CxForm.DelForm.dOne c (φ v)) := by
  first | exact @GlobalTheory.CxForm.DelForm.dOne_comp_holo | exact GlobalTheory.CxForm.DelForm.dOne_comp_holo | (intros; apply GlobalTheory.CxForm.DelForm.dOne_comp_holo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelLocReprContDiffOnTarget
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelLocReprContDiffOnTarget
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

noncomputable section

namespace GlobalTheory.CxForm.HolAtlas

open GlobalTheory.GoodMetric (coordVec)

theorem del_loc_repr_contDiffOn : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld), A.IsForm α → ∀ (i : A.ι) (S : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (GlobalTheory.CxForm.bas n).repr (A.loc (A.del α) i v) S) (A.e i).target := by
  intro M _ n A α hα i S
  have key : ∀ v ∈ (A.e i).target, (GlobalTheory.CxForm.bas n).repr (A.loc (A.del α) i v) S =
      ∑ a, ∑ T, GlobalTheory.del (fun x => (GlobalTheory.CxForm.bas n).repr (A.loc α i x) T) v (coordVec a) *
        (GlobalTheory.CxForm.bas n).repr (GlobalTheory.CxForm.dz a * GlobalTheory.CxForm.bas n T) S := by
    intro v hv
    have h1 : A.loc (A.del α) i v = GlobalTheory.CxForm.delAt (A.loc α i) v := by
      rw [GlobalTheory.CxForm.HolAtlas.loc, dite_eq_left hv]
      simp only [GlobalTheory.CxForm.HolAtlas.del, GlobalTheory.CxForm.HolAtlas.Pt.crd, GlobalTheory.CxForm.HolAtlas.Pt.ch, GlobalTheory.CxForm.HolAtlas.Pt.pt, (A.e i).right_inv hv]
    rw [h1, GlobalTheory.CxForm.delAt]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.CxForm.coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine ContDiffOn.congr ?_ key
  have ho := (A.e i).open_target
  refine ContDiffOn.sum fun a _ => ContDiffOn.sum fun T _ => ContDiffOn.mul ?_ contDiffOn_const
  have hf := hα.smooth i T
  have hd := hf.fderiv_of_isOpen ho (m := ∞) (by simp)
  have h1 : ContDiffOn ℝ ∞ (fun v => fderiv ℝ (fun x => (GlobalTheory.CxForm.bas n).repr (A.loc α i x) T) v (coordVec a))
      (A.e i).target := hd.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ∞ (fun v => fderiv ℝ (fun x => (GlobalTheory.CxForm.bas n).repr (A.loc α i x) T) v
      (Complex.I • coordVec a)) (A.e i).target := hd.clm_apply contDiffOn_const
  refine ((h1.sub (h2.const_smul Complex.I)).const_smul (1 / 2 : ℂ)).congr fun v _ => ?_
  rfl

end GlobalTheory.CxForm.HolAtlas
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelLocReprContDiffOnTargetStatement
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.del_loc_repr_contDiffOn_target : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld), A.IsForm α → ∀ (i : A.ι) (S : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (GlobalTheory.CxForm.bas n).repr (A.loc (A.del α) i v) S) (A.e i).target := by
  first | exact @GlobalTheory.CxForm.HolAtlas.del_loc_repr_contDiffOn | exact GlobalTheory.CxForm.HolAtlas.del_loc_repr_contDiffOn | (intros; apply GlobalTheory.CxForm.HolAtlas.del_loc_repr_contDiffOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDel
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DelForm

open GlobalTheory.CxForm

variable {n : ℕ}

theorem delAt_pull_comp {φ : V n → V n} {v : V n} (hφ : ContDiffAt ℂ 2 φ v) {β : V n → Alt n}
    (hβ : ∀ S, DifferentiableAt ℝ (fun u => (bas n).repr (β u) S) (φ v)) :
    delAt (fun w => pull (fderiv ℂ φ w) (β (φ w))) v = pull (fderiv ℂ φ v) (delAt β (φ v)) := by
  have hφ1 : DifferentiableAt ℂ φ v := hφ.differentiableAt two_ne_zero
  have e : (fun w => pull (fderiv ℂ φ w) (β (φ w))) =
      fun w => ∑ T, (bas n).repr (β (φ w)) T • pull (fderiv ℂ φ w) (bas n T) := funext fun w => by
    conv_lhs => rw [← (bas n).sum_repr (β (φ w))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [e, GlobalTheory.T.holomorphicDelOperatorAt_sum_smul_leibniz (fun T w => (bas n).repr (β (φ w)) T) (fun T w => pull (fderiv ℂ φ w) (bas n T))
    (fun T => (hβ T).comp v (hφ1.restrictScalars ℝ)) (fun T S => GlobalTheory.T.differentiableAt_repr_pullback_holomorphic_fderiv hφ (bas n T) S)]
  simp only [GlobalTheory.T.holomorphicDel_pullback_fderiv_form_eq_zero hφ, smul_zero, add_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [delAt_eq_sum_dOne β (φ v), map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [map_mul, GlobalTheory.T.holomorphicDifferentialOneForm_comp_holomorphic (c := fun u => (bas n).repr (β u) T) (hβ T) hφ1]

variable {M : Type} [TopologicalSpace M] {A : HolAtlas M n}

theorem del_compat {α : A.Fld} (hα : A.IsForm α) (x x' : A.Pt) (h : x.pt = x'.pt) :
    A.del α x = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (A.del α x') := by
  set φ : V n → V n := x'.ch ∘ x.ch.symm with hφdef
  have hW : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
    x.ch.isOpen_inter_preimage_symm x'.ch.open_source
  have hv : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source :=
    ⟨x.ch.map_source x.2, by simp only [mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩
  have hφ : ContDiffAt ℂ 2 φ x.crd := by
    have hd : DifferentiableOn ℂ φ (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) := A.holo x.1.1 x'.1.1
    have hs : ContDiffOn ℂ ∞ φ (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) := (contDiffOn_piLp 2).2 fun c =>
      ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ hW
        ((EuclideanSpace.proj c : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn hd)
    exact (hs.contDiffAt (hW.mem_nhds hv)).of_le (WithTop.coe_le_coe.2 le_top)
  have hφv : φ x.crd = x'.crd := by
    change x'.ch (x.ch.symm (x.ch x.pt)) = x'.ch x'.pt
    rw [x.ch.left_inv x.2]
    exact congrArg x'.ch h
  have hloc : A.loc α x.1.1 =ᶠ[𝓝 x.crd] fun w => pull (fderiv ℂ φ w) (A.loc α x'.1.1 (φ w)) := by
    filter_upwards [hW.mem_nhds hv] with w hw
    let p : A.Pt := ⟨(x.1.1, x.ch.symm w), x.ch.map_target hw.1⟩
    let p' : A.Pt := ⟨(x'.1.1, x.ch.symm w), hw.2⟩
    have hc := hα.compat p p' rfl
    have hp : p.crd = w := x.ch.right_inv hw.1
    rw [HolAtlas.loc, dite_eq_left hw.1]
    refine hc.trans ?_
    rw [hp, ← A.loc_crd α p']
    rfl
  show delAt (A.loc α x.1.1) x.crd = pull (fderiv ℂ φ x.crd) (delAt (A.loc α x'.1.1) x'.crd)
  rw [delAt_congr hloc, delAt_pull_comp hφ (fun S => hφv ▸ FormMul.differentiableAt_coef hα x' S), hφv]

theorem isForm_del : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld),
    A.IsForm α → A.IsForm (A.del α) :=
  fun A α hα => ⟨GlobalTheory.T.del_loc_repr_contDiffOn_target A α hα, fun x x' h => del_compat hα x x' h⟩

end GlobalTheory.CxForm.DelForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelStatement
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_isForm_del : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld), A.IsForm α → A.IsForm (A.del α) := by
  first | exact @GlobalTheory.CxForm.DelForm.isForm_del | exact GlobalTheory.CxForm.DelForm.isForm_del | (intros; apply GlobalTheory.CxForm.DelForm.isForm_del <;> assumption)
end
