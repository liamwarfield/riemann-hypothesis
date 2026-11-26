module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddAllOfThetaSumOnCover
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryRepresentativesExistVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHighestWeightKTypeMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointHarmonicHighestWeightMultiplicityOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockInnerProductPosDefCompactMatrixUnitAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockInnerProductPosDefCompactMatrixUnitAdjoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.FockMonoForm

open MvPolynomial

variable {σ : Type}

def fct (α : σ →₀ ℕ) : ℕ := α.prod fun _ k => k.factorial

theorem fct_pos (α : σ →₀ ℕ) : 0 < fct α := Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem fct_add_single (α : σ →₀ ℕ) (v : σ) : fct (α + Finsupp.single v 1) = (α v + 1) * fct α := by
  classical
  have hs : (α + Finsupp.single v 1).support ⊆ insert v α.support := by
    intro u hu
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply] at hu
    rw [Finset.mem_insert, Finsupp.mem_support_iff]
    by_cases h : v = u
    · exact Or.inl h.symm
    · right; simpa [h] using hu
  unfold fct
  rw [Finsupp.prod_of_support_subset _ hs _ (fun _ _ => Nat.factorial_zero),
    Finsupp.prod_of_support_subset α (Finset.subset_insert v α.support) _ (fun _ _ => Nat.factorial_zero),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v α.support),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v α.support)]
  have : ∀ u ∈ (insert v α.support).erase v,
      ((α + Finsupp.single v 1 : σ →₀ ℕ) u).factorial = (α u).factorial := by
    intro u hu
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hu).symm, add_zero]
  rw [Finset.prod_congr rfl this, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  ring

def form0 (P Q : MvPolynomial σ ℂ) : ℂ :=
  ∑ α ∈ Q.support, (fct α : ℂ) * (star (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α)

theorem fischerSumSupport_eq_sum_factorial_coeff (P Q : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (h : Q.support ⊆ s) :
    form0 P Q = ∑ α ∈ s, (fct α : ℂ) * (star (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α) := by
  unfold form0
  apply Finset.sum_subset h
  intro α _ hα
  rw [notMem_support_iff.mp hα]; simp

def form : MvPolynomial σ ℂ →ₗ⋆[ℂ] MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) form0
    (fun P P' Q => by
      rw [fischerSumSupport_eq_sum_factorial_coeff (P + P') Q Q.support subset_rfl, fischerSumSupport_eq_sum_factorial_coeff P Q Q.support subset_rfl,
        fischerSumSupport_eq_sum_factorial_coeff P' Q Q.support subset_rfl, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [MvPolynomial.coeff_add, star_add]; ring)
    (fun c P Q => by
      rw [fischerSumSupport_eq_sum_factorial_coeff (c • P) Q Q.support subset_rfl, fischerSumSupport_eq_sum_factorial_coeff P Q _ subset_rfl, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [coeff_smul, smul_eq_mul, star_mul']; simp only [Complex.star_def]; ring)
    (fun P Q Q' => by
      classical
      rw [fischerSumSupport_eq_sum_factorial_coeff P (Q + Q') (Q.support ∪ Q'.support) support_add,
        fischerSumSupport_eq_sum_factorial_coeff P Q (Q.support ∪ Q'.support) Finset.subset_union_left,
        fischerSumSupport_eq_sum_factorial_coeff P Q' (Q.support ∪ Q'.support) Finset.subset_union_right,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [MvPolynomial.coeff_add]; ring)
    (fun c P Q => by
      rw [fischerSumSupport_eq_sum_factorial_coeff P (c • Q) Q.support support_smul, fischerSumSupport_eq_sum_factorial_coeff P Q _ subset_rfl, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [coeff_smul, smul_eq_mul, RingHom.id_apply]; ring)

theorem form_eq (P Q : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (h : Q.support ⊆ s) :
    form P Q = ∑ α ∈ s, (fct α : ℂ) * (star (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α) := fischerSumSupport_eq_sum_factorial_coeff P Q s h

theorem form_symm (P Q : MvPolynomial σ ℂ) : form P Q = star (form Q P) := by
  classical
  rw [form_eq P Q (P.support ∪ Q.support) Finset.subset_union_right,
    form_eq Q P (P.support ∪ Q.support) Finset.subset_union_left, star_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp [star_mul', mul_comm]

theorem form_self (P : MvPolynomial σ ℂ) :
    form P P = ((∑ α ∈ P.support, (fct α : ℝ) * Complex.normSq (AddMonoidAlgebra.coeff P α) : ℝ) : ℂ) := by
  rw [form_eq P P P.support subset_rfl]
  push_cast
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]; rfl

theorem form_self_nonneg (P : MvPolynomial σ ℂ) : (form P P).im = 0 ∧ 0 ≤ (form P P).re := by
  rw [form_self, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, Finset.sum_nonneg fun α _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)⟩

theorem form_self_eq_zero (P : MvPolynomial σ ℂ) (h : form P P = 0) : P = 0 := by
  rw [form_self, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg (fun α _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))] at h
  ext α
  change P.coeff α = 0
  by_contra hne
  have := h α (mem_support_iff.mpr hne)
  rcases mul_eq_zero.mp this with h1 | h1
  · exact (Nat.cast_ne_zero.mpr (fct_pos α).ne') h1
  · exact hne (Complex.normSq_eq_zero.mp h1)

end GlobalTheory.FockMonoForm

end

noncomputable section

namespace GlobalTheory.FockMonoForm

open MvPolynomial

variable {σ : Type} [DecidableEq σ]

theorem form_monomial (γ δ : σ →₀ ℕ) (c d : ℂ) :
    form (monomial γ c) (monomial δ d) = if γ = δ then (fct δ : ℂ) * (star c * d) else 0 := by
  rw [form_eq _ _ {δ} support_monomial_subset, Finset.sum_singleton, coeff_monomial, coeff_monomial,
    if_pos rfl]
  split_ifs <;> simp

theorem form_X_mul (v : σ) (P Q : MvPolynomial σ ℂ) : form (X v * P) Q = form P (pderiv v Q) := by
  induction P using MvPolynomial.induction_on' with
  | monomial γ c =>
    induction Q using MvPolynomial.induction_on' with
    | monomial δ d =>
      rw [X, monomial_mul, pderiv_monomial, form_monomial, form_monomial, one_mul]
      by_cases hv : δ v = 0
      · rw [hv, if_neg]
        · simp
        · intro h
          have := congrArg (fun f : σ →₀ ℕ => f v) h
          simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
          omega
      · obtain ⟨α, rfl⟩ : ∃ α, δ = α + Finsupp.single v 1 :=
          ⟨δ - Finsupp.single v 1, (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hv))).symm⟩
        rw [add_tsub_cancel_right, add_comm (Finsupp.single v 1) γ]
        simp only [add_left_inj]
        rw [fct_add_single,
          Finsupp.add_apply, Finsupp.single_eq_same]
        split_ifs
        · push_cast; ring
        · rfl
    | add Q Q' hQ hQ' => rw [map_add (f := _), map_add (f := _), map_add (f := _), hQ, hQ']
  | add P P' hP hP' =>
    rw [mul_add, map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hP, hP']

theorem form_pderiv (v : σ) (P Q : MvPolynomial σ ℂ) : form (pderiv v P) Q = form P (X v * Q) := by
  rw [form_symm, ← form_X_mul, ← form_symm]

end GlobalTheory.FockMonoForm

end

noncomputable section

namespace GlobalTheory.LowestKType

open MvPolynomial GlobalTheory.FockMonoForm GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {n m : ℕ}

def FAdj (T S : Module.End ℂ (PolF D m n)) : Prop := ∀ P Q, form (T P) Q = form P (S Q)

theorem fadj_add {T S T' S' : Module.End ℂ (PolF D m n)} (h : FAdj T S) (h' : FAdj T' S') :
    FAdj (T + T') (S + S') := by
  intro P Q; simp only [LinearMap.add_apply, map_add (f := _), h P Q, h' P Q]

theorem fadj_mul {T S T' S' : Module.End ℂ (PolF D m n)} (h : FAdj T S) (h' : FAdj T' S') :
    FAdj (T * T') (S' * S) := by
  intro P Q; rw [Module.End.mul_apply, Module.End.mul_apply, h, h']

theorem fadj_neg {T S : Module.End ℂ (PolF D m n)} (h : FAdj T S) : FAdj (-T) (-S) := by
  intro P Q; simp only [LinearMap.neg_apply, map_neg, h P Q]

theorem fadj_sum {ι : Type} (s : Finset ι) (T S : ι → Module.End ℂ (PolF D m n))
    (h : ∀ i ∈ s, FAdj (T i) (S i)) : FAdj (∑ i ∈ s, T i) (∑ i ∈ s, S i) := by
  intro P Q
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.sum_apply, map_sum, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i hi => h i hi P Q

theorem fadj_X {_ : DecidableEq (FVar D m n)} (v : FVar D m n) :
    FAdj (LinearMap.mulLeft ℂ (X v)) (pderiv v).toLinearMap := fun P Q => form_X_mul v P Q

theorem fadj_d {_ : DecidableEq (FVar D m n)} (v : FVar D m n) :
    FAdj (pderiv v).toLinearMap (LinearMap.mulLeft ℂ (X v)) := fun P Q => form_pderiv v P Q

theorem kop_eq (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m) :
    kop w τ a b = ∑ j, (raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) a j *
      lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) b j +
        if a = b then (1 / 2 : ℂ) • 1 else 0) := by
  unfold kop fockT
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp

theorem fadj_term (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m) (j : Fin n) (h : Cpt w τ a b) :
    FAdj (raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) a j *
      lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) b j)
      (raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) b j *
      lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) a j) := by
  classical
  unfold Cpt at h
  unfold raiO lowO sgn
  by_cases ha : (a : ℕ) < w.p τ
  · have hb := h.mp ha
    simp [ha, hb]
    have h1 := @fadj_X D n m (fun a b => Classical.propDecidable (a = b)) (τ, a, j)
    have h2 := @fadj_d D n m (fun a b => Classical.propDecidable (a = b)) (τ, b, j)
    exact fadj_mul h1 h2
  · have hb : ¬ (b : ℕ) < w.p τ := fun hb => ha (h.mpr hb)
    simp [ha, hb]
    have h1 := @fadj_d D n m (fun a b => Classical.propDecidable (a = b)) (τ, a, j)
    have h2 := @fadj_X D n m (fun a b => Classical.propDecidable (a = b)) (τ, b, j)
    exact fadj_neg (fadj_mul h1 h2)

theorem fadj_half (a b : Fin m) :
    FAdj (D := D) (n := n) (m := m) (if a = b then (1 / 2 : ℂ) • 1 else 0) (if b = a then (1 / 2 : ℂ) • 1 else 0) := by
  intro P Q
  by_cases h : a = b
  · subst h
    simp only [if_true, LinearMap.smul_apply, Module.End.one_apply, LinearMap.map_smulₛₗ₂, map_smul]
    simp [Complex.conj_ofReal, map_ofNat]
  · simp [h, Ne.symm h]

theorem fockForm_kop_adjoint : ∀ (D : D7) (n m : ℕ), ∃ B : PolF D m n →ₗ⋆[ℂ] PolF D m n →ₗ[ℂ] ℂ,
    (∀ P, (B P P).im = 0 ∧ 0 ≤ (B P P).re) ∧ (∀ P, B P P = 0 → P = 0) ∧
      ∀ (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m), GlobalTheory.LowestKType.Cpt w τ a b →
        ∀ P Q, B (GlobalTheory.LowestKType.kop w τ a b P) Q = B P (GlobalTheory.LowestKType.kop w τ b a Q) := by
  intro D n m
  refine ⟨form, form_self_nonneg, form_self_eq_zero, fun w τ a b h P Q => ?_⟩
  rw [kop_eq, kop_eq]
  exact fadj_sum _ _ _ (fun j _ => fadj_add (fadj_term w τ a b j h) (fadj_half a b)) P Q

end GlobalTheory.LowestKType

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockInnerProductPosDefCompactMatrixUnitAdjointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockInnerProduct_posDef_compact_matrixUnit_adjoint : ∀ (D : D7) (n m : ℕ), ∃ B : PolF D m n →ₗ⋆[ℂ] PolF D m n →ₗ[ℂ] ℂ, (∀ P, (B P P).im = 0 ∧ 0 ≤ (B P P).re) ∧ (∀ P, B P P = 0 → P = 0) ∧ ∀ (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m), GlobalTheory.LowestKType.Cpt w τ a b → ∀ P Q, B (GlobalTheory.LowestKType.kop w τ a b P) Q = B P (GlobalTheory.LowestKType.kop w τ b a Q) := by
  first | exact @GlobalTheory.LowestKType.fockForm_kop_adjoint | exact GlobalTheory.LowestKType.fockForm_kop_adjoint | (intros; apply GlobalTheory.LowestKType.fockForm_kop_adjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleOfAnisotropicFormHighestWeightStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleOfAnisotropicFormHighestWeight
namespace GlobalTheory.DownLift

theorem abstract_irreducible_of_highestWeight (V : Type) [AddCommGroup V] [Module ℂ V]
    (U : Submodule ℂ V) (hfin : FiniteDimensional ℂ U) (J : Type) (E : J → Module.End ℂ V)
    (st : J → J) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (Hw : V → Prop)
    (hU : ∀ j, ∀ x ∈ U, E j x ∈ U) (han : ∀ x ∈ U, B x x = 0 → x = 0)
    (hadj : ∀ j x y, B (E j x) y = B x (E (st j) y)) (hst : ∀ j, st (st j) = j)
    (hex : ∀ T : Submodule ℂ V, T ≤ U → T ≠ ⊥ → (∀ j, ∀ x ∈ T, E j x ∈ T) →
      ∃ x ∈ T, x ≠ 0 ∧ Hw x)
    (hprop : ∀ x y, x ∈ U → y ∈ U → Hw x → Hw y → x ≠ 0 → ∃ c : ℂ, y = c • x)
    (S : Submodule ℂ V) (hSU : S ≤ U) (hS : S ≠ ⊥) (hSE : ∀ j, ∀ x ∈ S, E j x ∈ S) :
    S = U := by
  classical
  let P : Submodule ℂ V := U ⊓ ⨅ s : S, LinearMap.ker (B (s : V))
  have hP : ∀ y, y ∈ P ↔ y ∈ U ∧ ∀ s ∈ S, B s y = 0 := by
    intro y
    simp [P, Submodule.mem_iInf]
  have hPbot : P = ⊥ := by
    by_contra hne
    have hPE : ∀ j, ∀ x ∈ P, E j x ∈ P := by
      intro j y hy
      rw [hP] at hy ⊢
      refine ⟨hU j y hy.1, fun s hs => ?_⟩
      have h := hadj (st j) s y
      rw [hst] at h
      rw [← h]
      exact hy.2 _ (hSE _ _ hs)
    obtain ⟨y, hyP, hy0, hyw⟩ := hex P inf_le_left hne hPE
    obtain ⟨x, hxS, hx0, hxw⟩ := hex S hSU hS hSE
    rw [hP] at hyP
    obtain ⟨c, hc⟩ := hprop x y (hSU hxS) hyP.1 hxw hyw hx0
    have hyS : y ∈ S := hc ▸ S.smul_mem c hxS
    exact hy0 (han y hyP.1 (hyP.2 y hyS))
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSU
  let b := Module.finBasis ℂ S
  let φ : U →ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    LinearMap.pi fun i => (B (b i : V)).comp U.subtype
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    have hy' : ∀ i, B (b i : V) (y : V) = 0 := fun i => congrFun (LinearMap.mem_ker.mp hy) i
    have hyP : (y : V) ∈ P := by
      rw [hP]
      refine ⟨y.2, fun s hs => ?_⟩
      have h := congrArg (fun z : S => (z : V)) (b.sum_repr ⟨s, hs⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy', smul_zero]
    rw [hPbot, Submodule.mem_bot] at hyP
    rw [Submodule.mem_bot]
    exact Subtype.ext hyP
  have hle := LinearMap.finrank_le_finrank_of_injective hφ
  rw [Module.finrank_fin_fun] at hle
  exact Submodule.eq_of_le_of_finrank_le hSU hle

end GlobalTheory.DownLift
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrreducible_of_anisotropic_form_highestWeight : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (U : Submodule ℂ V), FiniteDimensional ℂ U → ∀ (J : Type) (E : J → Module.End ℂ V) (st : J → J) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (Hw : V → Prop), (∀ j, ∀ x ∈ U, E j x ∈ U) → (∀ x ∈ U, B x x = 0 → x = 0) → (∀ j x y, B (E j x) y = B x (E (st j) y)) → (∀ j, st (st j) = j) → (∀ T : Submodule ℂ V, T ≤ U → T ≠ ⊥ → (∀ j, ∀ x ∈ T, E j x ∈ T) → ∃ x ∈ T, x ≠ 0 ∧ Hw x) → (∀ x y, x ∈ U → y ∈ U → Hw x → Hw y → x ≠ 0 → ∃ c : ℂ, y = c • x) → ∀ S : Submodule ℂ V, S ≤ U → S ≠ ⊥ → (∀ j, ∀ x ∈ S, E j x ∈ S) → S = U := by
  first | exact @GlobalTheory.DownLift.abstract_irreducible_of_highestWeight | exact GlobalTheory.DownLift.abstract_irreducible_of_highestWeight | (intros; apply GlobalTheory.DownLift.abstract_irreducible_of_highestWeight <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSourceHighestWeightFockStableSubspace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSourceHighestWeightFockStableSubspace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.NHwExist

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LowestKType GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators MvPolynomial

variable {D : D7} {n m : ℕ}

lemma sop_eq (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) :
    (sop w τ a b : Module.End ℂ (PolF D m n)) =
      ∑ i, (raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) i a *
        lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) i b +
        if a = b then (1 / 2 : ℂ) • 1 else 0) := by
  classical
  unfold GlobalTheory.LowestKType.sop GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp

lemma term_lt (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) (i : Fin m) (hi : (i : ℕ) < w.p τ)
    (P : PolF D m n) :
    (raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) i a *
        lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) i b) P =
      X (τ, i, a) * pderiv (τ, i, b) P := by
  classical
  simp [raiO, lowO, sgn, hi]

lemma term_ge (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) (i : Fin m) (hi : ¬ (i : ℕ) < w.p τ)
    (P : PolF D m n) :
    (raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) i a *
        lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) i b) P =
      -(pderiv (τ, i, a) (X (τ, i, b) * P)) := by
  classical
  simp [raiO, lowO, sgn, hi]

lemma mono1 (u v : FVar D m n) (α : FVar D m n →₀ ℕ) (c : ℂ) :
    (X u * pderiv v (monomial α c) : PolF D m n) = monomial (Finsupp.single u 1 + (α - Finsupp.single v 1)) (c * α v) := by
  classical
  rw [pderiv_monomial, X, monomial_mul, one_mul]

lemma mono2 (u v : FVar D m n) (α : FVar D m n →₀ ℕ) (c : ℂ) :
    (pderiv u (X v * monomial α c) : PolF D m n) =
      monomial (Finsupp.single v 1 + α - Finsupp.single u 1) (c * ((Finsupp.single v 1 + α : FVar D m n →₀ ℕ) u)) := by
  classical
  rw [X, monomial_mul, one_mul, pderiv_monomial]

def lamM (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a : Fin n) (α : FVar D m n →₀ ℕ) : ℂ :=
  ∑ i : Fin m, ((if (i : ℕ) < w.p τ then (α (τ, i, a) : ℂ) else -((α (τ, i, a) : ℂ) + 1)) + 1 / 2)

lemma diag_X (v : FVar D m n) (α : FVar D m n →₀ ℕ) (c : ℂ) :
    (X v * pderiv v (monomial α c) : PolF D m n) = (α v : ℂ) • monomial α c := by
  classical
  rw [mono1]
  by_cases h : α v = 0
  · simp [h]
  · have : Finsupp.single v 1 + (α - Finsupp.single v 1) = α := by
      rw [add_comm]; exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h))
    rw [this, smul_monomial, smul_eq_mul, mul_comm]

lemma diag_D (v : FVar D m n) (α : FVar D m n →₀ ℕ) (c : ℂ) :
    (pderiv v (X v * monomial α c) : PolF D m n) = ((α v : ℂ) + 1) • monomial α c := by
  classical
  rw [mono2, add_tsub_cancel_left, smul_monomial]
  simp [Finsupp.single_apply]
  ring_nf

lemma sop_diag (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a : Fin n) (α : FVar D m n →₀ ℕ) (c : ℂ) :
    sop w τ a a (monomial α c : PolF D m n) = lamM w τ a α • monomial α c := by
  classical
  rw [sop_eq, LinearMap.sum_apply]
  unfold lamM
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.add_apply]
  by_cases hi : (i : ℕ) < w.p τ
  · rw [term_lt w τ a a i hi, diag_X]
    simp [hi, add_smul]
  · rw [term_ge w τ a a i hi, diag_D]
    simp [hi, add_smul, neg_smul]

lemma coeff_sop_diag (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a : Fin n) (P : PolF D m n)
    (β : FVar D m n →₀ ℕ) : AddMonoidAlgebra.coeff (sop w τ a a P) β = lamM w τ a β * AddMonoidAlgebra.coeff P β := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [sop_diag, coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

def gV (w : GlobalTheory.ExportSeries.Weight D n) (v : FVar D m n) : ℤ :=
  (if (v.2.1 : ℕ) < w.p v.1 then 1 else -1) * ((n : ℤ) - (v.2.2 : ℕ))

def ht (w : GlobalTheory.ExportSeries.Weight D n) (α : FVar D m n →₀ ℕ) : ℤ := ∑ v, gV w v * (α v : ℤ)

lemma ht_add (w : GlobalTheory.ExportSeries.Weight D n) (α β : FVar D m n →₀ ℕ) : ht w (α + β) = ht w α + ht w β := by
  unfold ht; simp [mul_add, Finset.sum_add_distrib]

lemma ht_single (w : GlobalTheory.ExportSeries.Weight D n) (u : FVar D m n) : ht w (Finsupp.single u 1) = gV w u := by
  classical
  unfold ht; simp [Finsupp.single_apply]

lemma ht_sub (w : GlobalTheory.ExportSeries.Weight D n) (α : FVar D m n →₀ ℕ) (v : FVar D m n) (h : 1 ≤ α v) :
    ht w (α - Finsupp.single v 1) = ht w α - gV w v := by
  have e : α - Finsupp.single v 1 + Finsupp.single v 1 = α := tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h)
  have h2 := congrArg (ht w) e
  rw [ht_add, ht_single] at h2
  linarith

lemma ht_move (w : GlobalTheory.ExportSeries.Weight D n) (α : FVar D m n →₀ ℕ) (u v : FVar D m n) (h : 1 ≤ α v) :
    ht w (Finsupp.single u 1 + (α - Finsupp.single v 1)) = ht w α + (gV w u - gV w v) := by
  rw [ht_add, ht_single, ht_sub w α v h]; ring

lemma sop_off_mono (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) (hab : a ≠ b)
    (α β : FVar D m n →₀ ℕ) (c : ℂ) (hβ : β ∈ (sop w τ a b (monomial α c : PolF D m n)).support) :
    ht w β = ht w α + ((b : ℕ) - (a : ℕ) : ℤ) := by
  classical
  rw [sop_eq, LinearMap.sum_apply] at hβ
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (support_sum hβ)
  rw [LinearMap.add_apply] at hi
  simp only [hab, if_false, LinearMap.zero_apply, add_zero] at hi
  by_cases hp : (i : ℕ) < w.p τ
  · rw [term_lt w τ a b i hp, mono1, support_monomial] at hi
    split_ifs at hi with h0
    · simp at hi
    · rw [Finset.mem_singleton] at hi
      subst hi
      have h1 : 1 ≤ α (τ, i, b) := by
        rcases Nat.eq_zero_or_pos (α (τ, i, b)) with h | h
        · simp [h] at h0
        · exact h
      rw [ht_move w α _ _ h1]
      simp [gV, hp]
  · rw [term_ge w τ a b i hp, support_neg, mono2, support_monomial] at hi
    split_ifs at hi with h0
    · simp at hi
    · rw [Finset.mem_singleton] at hi
      subst hi
      have hne : ((τ, i, b) : FVar D m n) ≠ (τ, i, a) := by
        intro h; apply hab; simp only [Prod.mk.injEq] at h; exact h.2.2.symm
      have hu : ((Finsupp.single ((τ, i, b) : FVar D m n) 1 + α : FVar D m n →₀ ℕ) (τ, i, a)) = α (τ, i, a) := by
        simp [Finsupp.single_apply, hne]
      rw [hu] at h0
      have h1 : 1 ≤ α (τ, i, a) := by
        rcases Nat.eq_zero_or_pos (α (τ, i, a)) with h | h
        · simp [h] at h0
        · exact h
      rw [add_tsub_assoc_of_le (Finsupp.single_le_iff.2 h1), ht_move w α _ _ h1]
      simp [gV, hp]

lemma sop_off (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) (hab : a ≠ b)
    (P : PolF D m n) (β : FVar D m n →₀ ℕ) (hβ : β ∈ (sop w τ a b P).support) :
    ∃ α ∈ P.support, ht w β = ht w α + ((b : ℕ) - (a : ℕ) : ℤ) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [as_sum P, map_sum] at hβ
  obtain ⟨α, hα, h⟩ := Finset.mem_biUnion.1 (support_sum hβ)
  exact ⟨α, hα, sop_off_mono w τ a b hab α β _ h⟩

def Pure (w : GlobalTheory.ExportSeries.Weight D n) (Q : PolF D m n) : Prop :=
  ∀ (τ : D.what₂.Tau) (a : Fin n), ∀ α ∈ Q.support, ∀ β ∈ Q.support, lamM w τ a α = lamM w τ a β

def wtZ (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a : Fin n) (α : FVar D m n →₀ ℕ) : ℤ :=
  ∑ i : Fin m, (if (i : ℕ) < w.p τ then (1 : ℤ) else -1) * (α (τ, i, a) : ℤ)

lemma ht_eq (w : GlobalTheory.ExportSeries.Weight D n) (α : FVar D m n →₀ ℕ) :
    ht w α = ∑ τ, ∑ a : Fin n, ((n : ℤ) - (a : ℕ)) * wtZ w τ a α := by
  unfold ht wtZ gV
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma lamM_eq (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a : Fin n) (α : FVar D m n →₀ ℕ) :
    lamM w τ a α = (wtZ w τ a α : ℂ) + ∑ i : Fin m, ((if (i : ℕ) < w.p τ then (0 : ℂ) else -1) + 1 / 2) := by
  unfold lamM wtZ
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

lemma ht_of_lam (w : GlobalTheory.ExportSeries.Weight D n) (α β : FVar D m n →₀ ℕ)
    (h : ∀ τ a, lamM w τ a α = lamM w τ a β) : ht w α = ht w β := by
  rw [ht_eq, ht_eq]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => ?_
  have h1 := h τ a
  rw [lamM_eq, lamM_eq, add_left_inj] at h1
  rw [Int.cast_inj.1 h1]

lemma purify (w : GlobalTheory.ExportSeries.Weight D n) (V : Submodule ℂ (PolF D m n))
    (hV : ∀ P ∈ V, ∀ (τ : D.what₂.Tau) (a b : Fin n), sop w τ a b P ∈ V) :
    ∀ (k : ℕ) (P : PolF D m n), P.support.card ≤ k → P ∈ V → ∀ α0 ∈ P.support,
      ∃ Q ∈ V, α0 ∈ Q.support ∧ Pure w Q := by
  classical
  intro k
  induction k with
  | zero =>
    intro P hc _ α0 hα0
    rw [Nat.le_zero, Finset.card_eq_zero] at hc
    simp [hc] at hα0
  | succ k ih =>
    intro P hc hPV α0 hα0
    by_cases hP : Pure w P
    · exact ⟨P, hPV, hα0, hP⟩
    simp only [Pure, not_forall] at hP
    obtain ⟨τ, a, α, hα, β, hβ, hne⟩ := hP
    obtain ⟨γ, hγ, hγne⟩ : ∃ γ ∈ P.support, lamM w τ a γ ≠ lamM w τ a α0 := by
      by_cases h : lamM w τ a α = lamM w τ a α0
      · exact ⟨β, hβ, fun h' => hne (h.trans h'.symm)⟩
      · exact ⟨α, hα, h⟩
    set R := sop w τ a a P - lamM w τ a γ • P with hR
    have hcoeff : ∀ δ, AddMonoidAlgebra.coeff R δ = (lamM w τ a δ - lamM w τ a γ) * AddMonoidAlgebra.coeff P δ := by
      intro δ; rw [hR, coeff_sub, coeff_smul, coeff_sop_diag, smul_eq_mul]; ring
    have hRV : R ∈ V := V.sub_mem (hV P hPV τ a a) (V.smul_mem _ hPV)
    have hsub : R.support ⊆ P.support.erase γ := by
      intro δ hδ
      rw [mem_support_iff, hcoeff] at hδ
      rw [Finset.mem_erase, mem_support_iff]
      refine ⟨fun h => ?_, fun h => hδ (by rw [h, mul_zero])⟩
      subst h; exact hδ (by rw [sub_self, zero_mul])
    have hcard : R.support.card ≤ k := by
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hγ] at this
      omega
    have hα0R : α0 ∈ R.support := by
      rw [mem_support_iff, hcoeff]
      exact mul_ne_zero (sub_ne_zero.2 (Ne.symm hγne)) (mem_support_iff.1 hα0)
    exact ih R hcard hRV α0 hα0R

lemma exists_F (V : Submodule ℂ (PolF D m n)) [FiniteDimensional ℂ V] :
    ∃ F : Finset (FVar D m n →₀ ℕ), ∀ P ∈ V, P.support ⊆ F := by
  classical
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional V).2 inferInstance
  refine ⟨s.biUnion fun P => P.support, fun P hP => ?_⟩
  rw [← hs] at hP
  induction hP using Submodule.span_induction with
  | mem x hx => exact Finset.subset_biUnion_of_mem (fun P : PolF D m n => P.support) hx
  | zero => simp
  | add x y _ _ hx hy => exact (support_add).trans (Finset.union_subset hx hy)
  | smul c x _ hx => exact (support_smul).trans hx

lemma pure_eigen (w : GlobalTheory.ExportSeries.Weight D n) (Q : PolF D m n) (hQ : Pure w Q) (α : FVar D m n →₀ ℕ)
    (hα : α ∈ Q.support) (τ : D.what₂.Tau) (a : Fin n) : sop w τ a a Q = lamM w τ a α • Q := by
  classical
  ext γ
  rw [coeff_sop_diag, coeff_smul, smul_eq_mul]
  by_cases hγ : AddMonoidAlgebra.coeff Q γ = 0
  · rw [hγ, mul_zero, mul_zero]
  · rw [hQ τ a γ (mem_support_iff.2 hγ) α hα]

end GlobalTheory.NHwExist


open GlobalTheory.NHwExist in
theorem GlobalTheory.exists_nHw_of_fockS_stable : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (V : Submodule ℂ (PolF D m n)), FiniteDimensional ℂ V → V ≠ ⊥ → (∀ P ∈ V, ∀ (τ : D.what₂.Tau) (a b : Fin n), GlobalTheory.LowestKType.sop w τ a b P ∈ V) → ∃ P ∈ V, P ≠ 0 ∧ ∃ lam : D.what₂.Tau → Fin n → ℂ, GlobalTheory.LowestKType.IsNHw w lam P := by
  classical
  intro D n m w V hfin hne hst
  obtain ⟨F, hF⟩ := exists_F V
  obtain ⟨B, hB⟩ : ∃ B : ℤ, ∀ α ∈ F, ht w α ≤ B :=
    ⟨∑ α ∈ F, |ht w α|, fun α hα =>
      (le_abs_self _).trans (Finset.single_le_sum (fun x _ => abs_nonneg (ht w x)) hα)⟩
  have key : ∀ k : ℕ, ∀ Q ∈ V, Pure w Q → ∀ α ∈ Q.support, B - ht w α ≤ k →
      ∃ P ∈ V, P ≠ 0 ∧ ∃ lam : D.what₂.Tau → Fin n → ℂ, GlobalTheory.LowestKType.IsNHw w lam P := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro Q hQ hpure α hα hk
      by_cases hr : ∀ (τ : D.what₂.Tau) (a b : Fin n), a < b → GlobalTheory.LowestKType.sop w τ a b Q = 0
      · refine ⟨Q, hQ, fun h => by simp [h] at hα, fun τ a => lamM w τ a α, hr, fun τ a => ?_⟩
        exact pure_eigen w Q hpure α hα τ a
      · simp only [not_forall] at hr
        obtain ⟨τ, a, b, hab, hne⟩ := hr
        obtain ⟨β, hβ⟩ : (GlobalTheory.LowestKType.sop w τ a b Q).support.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hne
        obtain ⟨α', hα', hht⟩ := sop_off w τ a b (ne_of_lt hab) Q β hβ
        have heq : ht w α' = ht w α := ht_of_lam w α' α (fun τ a => hpure τ a α' hα' α hα)
        obtain ⟨Q', hQ'V, hβQ', hpure'⟩ :=
          purify w V hst _ _ le_rfl (hst Q hQ τ a b) β hβ
        have hβB : ht w β ≤ B := hB β (hF Q' hQ'V hβQ')
        have hab' : (a : ℕ) < (b : ℕ) := hab
        exact ih (B - ht w β).toNat (by omega) Q' hQ'V hpure' β hβQ' (Int.self_le_toNat _)
  obtain ⟨P, hPV, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨α0, hα0⟩ : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hP0
  obtain ⟨Q, hQV, hα0Q, hpure⟩ := purify w V hst _ P le_rfl hPV α0 hα0
  exact key (B - ht w α0).toNat Q hQV hpure α0 hα0Q (Int.self_le_toNat _)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSourceHighestWeightFockStableSubspaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sourceHighestWeight_fock_stable_subspace : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (V : Submodule ℂ (PolF D m n)), FiniteDimensional ℂ V → V ≠ ⊥ → (∀ P ∈ V, ∀ (τ : D.what₂.Tau) (a b : Fin n), GlobalTheory.LowestKType.sop w τ a b P ∈ V) → ∃ P ∈ V, P ≠ 0 ∧ ∃ lam : D.what₂.Tau → Fin n → ℂ, GlobalTheory.LowestKType.IsNHw w lam P := by
  first | exact @GlobalTheory.exists_nHw_of_fockS_stable | exact GlobalTheory.exists_nHw_of_fockS_stable | (intros; apply GlobalTheory.exists_nHw_of_fockS_stable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryBasisGeneralLinearSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.LowestKType

theorem lowestKType_irreducible : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ (k : K) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r k) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → (∀ g : GlobalTheory.ExportSeries.GLR D n, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ k, r k = g) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ k, U.map (ρ k) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ S : Submodule ℂ (W →ₗ[ℂ] PolF D m n), (∀ ψ ∈ S, ∀ (k : K) (w' : W), ψ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ w')) → (∀ ψ ∈ S, ∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (ψ w') = 0) → (∀ ψ ∈ S, ∀ (τ : D.what₂.Tau) (a b : Fin m), ((a : ℕ) < w.p τ ↔ (b : ℕ) < w.p τ) → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single a b (1 : ℂ)) ∘ₗ ψ ∈ S) → S ≠ ⊥ → ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → (∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (φ w') = 0) → φ ∈ S := by
  intro D n m w BS K _ r hU1 hU2 W _ _ _ ρ hρ S hSeq hSharm hSstab hS0 φ hφeq hφharm
  classical
  have hinj : ∀ ψ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (x : W), ψ (ρ k x) = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ x)) →
      ψ ≠ 0 → Function.Injective ψ := by
    intro ψ hψ h0
    rw [← LinearMap.ker_eq_bot]
    rcases hρ (LinearMap.ker ψ) (fun k => Submodule.map_le_iff_le_comap.2 fun x hx => by
      simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
      rw [hψ, hx, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ext fun x => by
        have : x ∈ LinearMap.ker ψ := h ▸ Submodule.mem_top
        simpa using this) h0
  obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  have hseq := hSeq s hsS
  have hsinj := hinj s hseq hs0
  choose A hA using fun τ a b => GlobalTheory.T.unitary_representatives_exist_vector D n m w BS K r hU2 W ρ s hsinj hseq τ a b
  have hV0 : LinearMap.range s ≠ ⊥ := by rwa [Ne, LinearMap.range_eq_bot]
  have hVst : ∀ P ∈ LinearMap.range s, ∀ (τ : D.what₂.Tau) (a b : Fin n),
      GlobalTheory.LowestKType.sop w τ a b P ∈ LinearMap.range s := by
    rintro _ ⟨x, rfl⟩ τ a b
    exact ⟨A τ a b x, by simpa using LinearMap.congr_fun (hA τ a b s hseq) x⟩
  obtain ⟨P0, ⟨w0, rfl⟩, hP0, lam, hlam⟩ := GlobalTheory.T.exists_sourceHighestWeight_fock_stable_subspace D n m w _ inferInstance hV0 hVst
  have hw0 : w0 ≠ 0 := by rintro rfl; exact hP0 (map_zero s)
  have hN : ∀ φ' : W →ₗ[ℂ] PolF D m n,
      (∀ (k : K) (x : W), φ' (ρ k x) = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ' x)) →
      GlobalTheory.LowestKType.IsNHw w lam (φ' w0) := by
    intro φ' hφ'
    refine ⟨fun τ a b hab => ?_, fun τ a => ?_⟩
    · have h1 : s (A τ a b w0) = 0 := by
        rw [show s (A τ a b w0) = GlobalTheory.LowestKType.sop w τ a b (s w0) from LinearMap.congr_fun (hA τ a b s hseq) w0]
        exact hlam.1 τ a b hab
      have h2 : A τ a b w0 = 0 := hsinj (by rw [h1, map_zero])
      have h3 := LinearMap.congr_fun (hA τ a b φ' hφ') w0
      simp only [LinearMap.comp_apply, h2, map_zero] at h3
      exact h3.symm
    · have h1 : s (A τ a a w0) = s (lam τ a • w0) := by
        rw [show s (A τ a a w0) = GlobalTheory.LowestKType.sop w τ a a (s w0) from LinearMap.congr_fun (hA τ a a s hseq) w0,
          map_smul]
        exact hlam.2 τ a
      have h3 := LinearMap.congr_fun (hA τ a a φ' hφ') w0
      simp only [LinearMap.comp_apply, hsinj h1, map_smul] at h3
      exact h3.symm
  let J := {j : D.what₂.Tau × Fin m × Fin m // GlobalTheory.LowestKType.Cpt w j.1 j.2.1 j.2.2}
  let E : J → Module.End ℂ (W →ₗ[ℂ] PolF D m n) := fun j =>
    LinearMap.llcomp ℂ W (PolF D m n) (PolF D m n) (GlobalTheory.LowestKType.kop w j.1.1 j.1.2.1 j.1.2.2)
  have hE : ∀ j ψ, E j ψ = GlobalTheory.LowestKType.kop w j.1.1 j.1.2.1 j.1.2.2 ∘ₗ ψ := fun _ _ => rfl
  let st : J → J := fun j => ⟨(j.1.1, j.1.2.2, j.1.2.1), Iff.symm j.2⟩
  obtain ⟨B, hBpos, hBani, hBadj⟩ := GlobalTheory.T.fockInnerProduct_posDef_compact_matrixUnit_adjoint D n m
  let e := Module.finBasis ℂ W
  let BM : (W →ₗ[ℂ] PolF D m n) →ₗ⋆[ℂ] (W →ₗ[ℂ] PolF D m n) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun ψ χ => ∑ i, B (ψ (e i)) (χ (e i)))
      (fun ψ ψ' χ => by simp [Finset.sum_add_distrib])
      (fun c ψ χ => by simp [Finset.mul_sum])
      (fun ψ χ χ' => by simp [Finset.sum_add_distrib])
      (fun c ψ χ => by simp [Finset.mul_sum])
  have hBM : ∀ ψ χ, BM ψ χ = ∑ i, B (ψ (e i)) (χ (e i)) := fun _ _ => rfl
  have hBMani : ∀ ψ : W →ₗ[ℂ] PolF D m n, BM ψ ψ = 0 → ψ = 0 := by
    intro ψ h
    rw [hBM] at h
    have hre : ∑ i, (B (ψ (e i)) (ψ (e i))).re = 0 := by
      have := congrArg Complex.re h
      simpa [Complex.re_sum] using this
    have hz : ∀ i, B (ψ (e i)) (ψ (e i)) = 0 := fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => (hBpos (ψ (e i))).2)).1 hre i (Finset.mem_univ _)
      exact Complex.ext this (hBpos _).1
    exact e.ext fun i => by rw [hBani _ (hz i), LinearMap.zero_apply]
  have hBMadj : ∀ j ψ χ, BM (E j ψ) χ = BM ψ (E (st j) χ) := by
    intro j ψ χ
    simp only [hBM, hE, LinearMap.comp_apply]
    exact Finset.sum_congr rfl fun i _ => hBadj w _ _ _ j.2 _ _
  obtain ⟨d, hdφ, hds⟩ : ∃ d, (∀ i, (φ (e i)).totalDegree ≤ d) ∧ ∀ i, (s (e i)).totalDegree ≤ d :=
    ⟨Finset.univ.sup (fun i => (φ (e i)).totalDegree) ⊔ Finset.univ.sup (fun i => (s (e i)).totalDegree),
      fun i => le_sup_of_le_left (Finset.le_sup (f := fun i => (φ (e i)).totalDegree) (Finset.mem_univ i)),
      fun i => le_sup_of_le_right (Finset.le_sup (f := fun i => (s (e i)).totalDegree) (Finset.mem_univ i))⟩
  have hdeg : ∀ ψ : W →ₗ[ℂ] PolF D m n, (∀ i, (ψ (e i)).totalDegree ≤ d) →
      ∀ x, ψ x ∈ MvPolynomial.restrictTotalDegree (FVar D m n) ℂ d := by
    intro ψ hψ x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e.sum_repr x, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ ((MvPolynomial.mem_restrictTotalDegree _ _ _).2 (hψ i))
  let U : Submodule ℂ (W →ₗ[ℂ] PolF D m n) :=
    { carrier := {ψ | (∀ (k : K) (x : W), ψ (ρ k x) = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ x)) ∧
        (∀ x, GlobalTheory.LowestKType.IsHarm w (ψ x)) ∧ ∀ x, ψ x ∈ MvPolynomial.restrictTotalDegree (FVar D m n) ℂ d}
      add_mem' := by
        rintro ψ χ ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
        refine ⟨fun k x => by simp [h1, g1], fun x τ i l hi hl => ?_, fun x => add_mem (h3 x) (g3 x)⟩
        simp only [LinearMap.add_apply, map_add (f := _), h2 x τ i l hi hl, g2 x τ i l hi hl, add_zero]
      zero_mem' := ⟨fun k x => by simp, fun x τ i l _ _ => by simp, fun x => zero_mem _⟩
      smul_mem' := by
        rintro c ψ ⟨h1, h2, h3⟩
        refine ⟨fun k x => by simp [h1], fun x τ i l hi hl => ?_, fun x => Submodule.smul_mem _ c (h3 x)⟩
        simp only [LinearMap.smul_apply, map_smul, h2 x τ i l hi hl, smul_zero] }
  have hUfd : FiniteDimensional ℂ U := by
    let f : U →ₗ[ℂ] (Fin (Module.finrank ℂ W) → MvPolynomial.restrictTotalDegree (FVar D m n) ℂ d) :=
      { toFun := fun ψ i => ⟨(ψ : W →ₗ[ℂ] PolF D m n) (e i), ψ.2.2.2 (e i)⟩
        map_add' := fun _ _ => by ext; simp
        map_smul' := fun _ _ => by ext; simp }
    exact Module.Finite.of_injective f (fun ψ χ h => Subtype.ext (e.ext fun i => by
      have := congrArg (fun g => (g i : PolF D m n)) h
      simpa [f] using this))
  have hUst : ∀ j, ∀ ψ ∈ U, E j ψ ∈ U := by
    rintro ⟨⟨τ, a, b⟩, hab⟩ ψ ⟨h1, h2, h3⟩
    refine ⟨fun k x => ?_, fun x => ?_, fun x => ?_⟩
    · show GlobalTheory.LowestKType.kop w τ a b (ψ (ρ k x)) =
        GlobalTheory.ExportSeries.fockGL m w BS (r k) (GlobalTheory.LowestKType.kop w τ a b (ψ x))
      rw [h1, GlobalTheory.ExportSeries.fockGL_apply, GlobalTheory.ExportSeries.fockGL_apply, map_smul]
      congr 1
      exact (GlobalTheory.FockSubstComm.fockSubst_fockT D m n w.p _ τ _ _).symm
    · exact GlobalTheory.CompactHarm.fockT_compact_harm D n m w.p (ψ x) (h2 x) τ a b hab
    · exact (MvPolynomial.mem_restrictTotalDegree _ _ _).2
        (GlobalTheory.T.fockTargetMatrixUnit_compact_totalDegree_le D n m w τ a b hab d _ ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 (h3 x)))
  have hsU : s ∈ U := ⟨hseq, hSharm s hsS, hdeg s hds⟩
  have hφU : φ ∈ U := ⟨hφeq, hφharm, hdeg φ hdφ⟩
  have hKHw : ∀ x : W →ₗ[ℂ] PolF D m n, GlobalTheory.LowestKType.IsKHwMap w x → GlobalTheory.LowestKType.IsKHw w (x w0) :=
    fun x hxh => ⟨fun τ a b hab hlt => by simpa using LinearMap.congr_fun (hxh.1 τ a b hab hlt) w0,
      fun τ a => (hxh.2 τ a).imp fun c hc => by simpa using LinearMap.congr_fun hc w0⟩
  have key := GlobalTheory.T.isIrreducible_of_anisotropic_form_highestWeight (W →ₗ[ℂ] PolF D m n) U hUfd J E st BM (GlobalTheory.LowestKType.IsKHwMap w) hUst
    (fun x _ => hBMani x) hBMadj (fun j => rfl)
    (fun T hTU hT0 hTst => by
      haveI : FiniteDimensional ℂ T := Submodule.finiteDimensional_of_le hTU
      exact GlobalTheory.T.exists_highest_weight_K_type_map D n m w W T inferInstance hT0 (fun ψ hψ τ a b hab => hTst ⟨(τ, a, b), hab⟩ ψ hψ))
    (fun x y hx hy hxh hyh hx0 => by
      obtain ⟨c, hc⟩ := GlobalTheory.T.jointHarmonic_highestWeight_multiplicity_one D n m w lam (x w0) (y w0)
        (fun h => hw0 (hinj x hx.1 hx0 (h.trans (map_zero x).symm))) (hx.2.1 w0) (hy.2.1 w0)
        (hN x hx.1) (hN y hy.1) (hKHw x hxh) (hKHw y hyh)
      refine ⟨c, ?_⟩
      by_contra hne
      have h0 : y - c • x ≠ 0 := sub_ne_zero.2 hne
      have := hinj (y - c • x) (fun k z => by simp [hx.1, hy.1]) h0
        (show (y - c • x) w0 = (y - c • x) 0 by simp [hc])
      exact hw0 this)
  have hS'U : S ⊓ U = U := key (S ⊓ U) inf_le_right (by
      intro h
      apply hs0
      have : s ∈ S ⊓ U := ⟨hsS, hsU⟩
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this)
    (fun j ψ hψ => ⟨hSstab ψ hψ.1 j.1.1 j.1.2.1 j.1.2.2 j.2, hUst j ψ hψ.2⟩)
  have : φ ∈ S ⊓ U := by rw [hS'U]; exact hφU
  exact this.1

end GlobalTheory.LowestKType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryBasisGeneralLinearSeriesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_basis_general_linear_series : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ (k : K) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r k) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → (∀ g : GlobalTheory.ExportSeries.GLR D n, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ k, r k = g) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ k, U.map (ρ k) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ S : Submodule ℂ (W →ₗ[ℂ] PolF D m n), (∀ ψ ∈ S, ∀ (k : K) (w' : W), ψ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ w')) → (∀ ψ ∈ S, ∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (ψ w') = 0) → (∀ ψ ∈ S, ∀ (τ : D.what₂.Tau) (a b : Fin m), ((a : ℕ) < w.p τ ↔ (b : ℕ) < w.p τ) → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single a b (1 : ℂ)) ∘ₗ ψ ∈ S) → S ≠ ⊥ → ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → (∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (φ w') = 0) → φ ∈ S := by
  first | exact @GlobalTheory.LowestKType.lowestKType_irreducible | exact GlobalTheory.LowestKType.lowestKType_irreducible | (intros; apply GlobalTheory.LowestKType.lowestKType_irreducible <;> assumption)
end
