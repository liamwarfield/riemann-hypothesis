module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionWeightProjector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixCoefficientPolySimpleSubquotient

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDualWeylProductSpanOfFactorwiseDualWeyl
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDualWeylProductSpanOfFactorwiseDualWeyl
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HighWtEmb.NabInter

variable {k : Type} [Field k]

def mr {σ A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (L : A →ₗ[k] B)
    (F : MvPolynomial σ A) : MvPolynomial σ B :=
  ∑ m ∈ F.support, monomial m (L (AddMonoidAlgebra.coeff F m))

section
variable {σ A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (L : A →ₗ[k] B)

theorem coeff_mr (F : MvPolynomial σ A) (m : σ →₀ ℕ) : AddMonoidAlgebra.coeff (mr L F) m = L (AddMonoidAlgebra.coeff F m) := by
  classical
  simp only [mr, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]

theorem mr_add (F G : MvPolynomial σ A) : mr L (F + G) = mr L F + mr L G := by
  ext m; simp [coeff_mr]

theorem mr_smul (c : k) (F : MvPolynomial σ A) : mr L (c • F) = c • mr L F := by
  ext m; simp [coeff_mr, coeff_smul]

theorem mr_monomial (m : σ →₀ ℕ) (a : A) : mr L (monomial m a) = monomial m (L a) := by
  classical
  ext n; simp only [coeff_mr, coeff_monomial]; split_ifs <;> simp

theorem mr_C (a : A) : mr L (C a : MvPolynomial σ A) = C (L a) := mr_monomial L 0 a

theorem mr_map_mul (q : MvPolynomial σ k) (F : MvPolynomial σ A) :
    mr L (map (algebraMap k A) q * F) = map (algebraMap k B) q * mr L F := by
  classical
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coeff_mr, coeff_mul, coeff_map, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Algebra.smul_def (AddMonoidAlgebra.coeff q x.1) (AddMonoidAlgebra.coeff F x.2), LinearMap.map_smul, Algebra.smul_def]
end

theorem mr_C_mul_map {σ A : Type} [CommRing A] [Algebra k A] (L : A →ₗ[k] k) (c : A) (h : MvPolynomial σ k) :
    mr L (C c * map (algebraMap k A) h) = L c • h := by
  ext n
  simp only [coeff_mr, coeff_C_mul, coeff_map, coeff_smul, smul_eq_mul]
  rw [← Algebra.commutes, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_comm]

theorem commAlgEquiv_monomial_one {S₁ S₂ : Type} (m' : S₁ →₀ ℕ) :
    commAlgEquiv k S₁ S₂ (monomial m' 1) = C (monomial m' 1) := by
  rw [monomial_eq, monomial_eq, C_1, C_1, one_mul, one_mul]
  simp only [Finsupp.prod, map_prod, map_pow, commAlgEquiv_X]

theorem coeff_coeff_commAlgEquiv {S₁ S₂ : Type} (F : MvPolynomial S₁ (MvPolynomial S₂ k)) (β : S₂ →₀ ℕ) (m : S₁ →₀ ℕ) :
    AddMonoidAlgebra.coeff (AddMonoidAlgebra.coeff (commAlgEquiv k S₁ S₂ F) β) m = AddMonoidAlgebra.coeff (AddMonoidAlgebra.coeff F m) β := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial m' a =>
    have : (monomial m' a : MvPolynomial S₁ (MvPolynomial S₂ k)) = C a * monomial m' 1 := by
      rw [C_mul_monomial, mul_one]
    rw [this, map_mul, commAlgEquiv_C, commAlgEquiv_monomial_one, mul_comm, coeff_C_mul, coeff_map,
      ← this, coeff_monomial]
    rw [mul_comm, C_mul_monomial, mul_one, coeff_monomial]
    split_ifs <;> simp
  | add p q hp hq => simp [hp, hq]

end GlobalTheory.HighWtEmb.NabInter

namespace GlobalTheory.HighWtEmb.NabInter
variable {k : Type} [Field k]

theorem mr_aeval {σ τ' A : Type} [CommRing A] [Algebra k A] (L : A →ₗ[k] k) (g : σ → MvPolynomial τ' k)
    (F : MvPolynomial σ A) :
    mr L (aeval (fun v => map (algebraMap k A) (g v)) F) = aeval g (mr L F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    have h1 : aeval (fun v => map (algebraMap k A) (g v)) (monomial u (1 : A)) =
        map (algebraMap k A) (aeval g (monomial u (1 : k))) := by
      simp only [aeval_monomial, Finsupp.prod, map_prod, map_pow, map_one, one_mul, map_mul, map_X]
    have h2 : (monomial u a : MvPolynomial σ A) = C a * monomial u 1 := by rw [C_mul_monomial, mul_one]
    rw [h2, map_mul, aeval_C, h1, algebraMap_eq, mr_C_mul_map, ← h2, mr_monomial,
      show (monomial u (L a) : MvPolynomial σ k) = L a • monomial u 1 by rw [smul_monomial, smul_eq_mul, mul_one],
      map_smul]
  | add p q hp hq => rw [map_add (f := _), mr_add, hp, hq, mr_add, map_add (f := _)]

theorem colAddGen_eq_aeval (A : Type) [CommRing A] [Algebra k A] {r n : ℕ} (l j : Fin n) :
    colAddGen A (r := r) l j = aeval (fun v => map (algebraMap k A)
      ((if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) :
        MvPolynomial (Option (Fin r × Fin n)) k))) := by
  unfold colAddGen
  congr 1
  funext v
  split_ifs <;> simp

theorem rename_some_eq_aeval (A : Type) [CommRing A] [Algebra k A] {r n : ℕ} :
    (rename (R := A) (some : Fin r × Fin n → Option (Fin r × Fin n))) =
      aeval (fun v => map (algebraMap k A) (X (some v) : MvPolynomial (Option (Fin r × Fin n)) k)) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp

theorem dualWeyl_mr {A : Type} [CommRing A] [Algebra k A] (L : A →ₗ[k] k) (r n : ℕ) (ν : Fin n → ℕ)
    (F : MvPolynomial (Fin r × Fin n) A) (hF : F ∈ dualWeyl A r n ν) : mr L F ∈ dualWeyl k r n ν := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hF ⊢
  obtain ⟨h1, h2⟩ := hF
  refine ⟨?_, fun l j hlj => ?_⟩
  · intro d hd
    apply h1
    intro h0
    apply hd
    rw [coeff_mr, h0, map_zero]
  · have := congrArg (mr L) (h2 l j hlj)
    rw [colAddGen_eq_aeval (k := k), rename_some_eq_aeval (k := k), mr_aeval, mr_aeval] at this
    rw [colAddGen_eq_aeval (k := k), rename_some_eq_aeval (k := k)]
    simpa [Algebra.algebraMap_self, map_id] using this

end GlobalTheory.HighWtEmb.NabInter

namespace GlobalTheory.HighWtEmb.NabInter
variable {k : Type} [Field k]

theorem exists_proj {M : Type} [AddCommGroup M] [Module k M] (D : Submodule k M) :
    ∃ π : M →ₗ[k] M, (∀ f, π f ∈ D) ∧ ∀ f ∈ D, π f = f := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl D
  refine ⟨D.subtype ∘ₗ Submodule.projectionOnto D q hq, fun f => by simp, fun f hf => ?_⟩
  have := Submodule.projectionOnto_apply_left hq ⟨f, hf⟩
  simpa using congrArg Subtype.val this

def mrL {σ A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (L : A →ₗ[k] B) :
    MvPolynomial σ A →ₗ[k] MvPolynomial σ B where
  toFun := mr L
  map_add' := mr_add L
  map_smul' c F := by rw [mr_smul, RingHom.id_apply]

section
variable (N : ℕ) {ι : Type} [DecidableEq ι]

def splitEquiv (τ : ι) : BVar N ι ≃ OVar N τ ⊕ (Fin N × Fin N) where
  toFun p := if h : p.1 = τ then Sum.inr p.2 else Sum.inl ⟨p, h⟩
  invFun := Sum.elim Subtype.val (fun v => (τ, v))
  left_inv p := by
    obtain ⟨a, v⟩ := p
    by_cases h : a = τ
    · subst h; simp
    · simp [h]
  right_inv x := by
    rcases x with ⟨p, hp⟩ | v
    · simp [hp]
    · simp

def Ψ (τ : ι) :
    MvPolynomial (BVar N ι) k ≃ₐ[k] MvPolynomial (OVar N τ) (MvPolynomial (Fin N × Fin N) k) :=
  (renameEquiv k (splitEquiv N τ)).trans (sumAlgEquiv k _ _)

theorem Ψ_X_self (τ : ι) (v : Fin N × Fin N) : Ψ (k := k) N τ (X (τ, v)) = C (X v) := by
  simp [Ψ, splitEquiv]

theorem Ψ_X_ne (τ : ι) (p : BVar N ι) (h : p.1 ≠ τ) : Ψ (k := k) N τ (X p) = X ⟨p, h⟩ := by
  simp [Ψ, splitEquiv, h]

theorem Ψ_rename_self (τ : ι) (f : MvPolynomial (Fin N × Fin N) k) :
    Ψ N τ (rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) f) = C f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have := (Ψ (k := k) N τ).commutes a
    simpa [MvPolynomial.algebraMap_apply] using this
  | add p q hp hq => simp [hp, hq]
  | mul_X p v ih => simp [ih, Ψ_X_self]

theorem Ψ_rename_ne (τ σ : ι) (h : σ ≠ τ) (f : MvPolynomial (Fin N × Fin N) k) :
    Ψ N τ (rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) f) =
      map (algebraMap k (MvPolynomial (Fin N × Fin N) k))
        (rename (fun v : Fin N × Fin N => (⟨(σ, v), h⟩ : OVar N τ)) f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have := (Ψ (k := k) N τ).commutes a
    simpa [MvPolynomial.algebraMap_apply] using this
  | add p q hp hq => simp [hp, hq]
  | mul_X p v ih => simp [ih, Ψ_X_ne N τ (σ, v) h]

theorem Ψ_eq_toBlock (τ : ι) (P : MvPolynomial (BVar N ι) k) :
    Ψ N τ P = commAlgEquiv k (Fin N × Fin N) (OVar N τ) (toBlock k N τ P) := by
  have : (Ψ (k := k) N τ).toAlgHom = (commAlgEquiv k (Fin N × Fin N) (OVar N τ)).toAlgHom.comp (toBlock k N τ) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, v⟩
    by_cases h : a = τ
    · subst h; simp [toBlock, Ψ_X_self]
    · simp [toBlock, h, Ψ_X_ne N τ (a, v) h]
  exact congrArg (fun φ : MvPolynomial (BVar N ι) k →ₐ[k] _ => φ P) this

end

end GlobalTheory.HighWtEmb.NabInter

namespace GlobalTheory.HighWtEmb.NabInter
variable {k : Type} [Field k]

section
variable (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]

def E (τ : ι) (π : MvPolynomial (Fin N × Fin N) k →ₗ[k] MvPolynomial (Fin N × Fin N) k) :
    MvPolynomial (BVar N ι) k →ₗ[k] MvPolynomial (BVar N ι) k :=
  (Ψ N τ).symm.toLinearMap ∘ₗ mrL π ∘ₗ (Ψ N τ).toLinearMap

def gen (D : ι → Submodule k (MvPolynomial (Fin N × Fin N) k)) (T : Finset ι) :
    Set (MvPolynomial (BVar N ι) k) :=
  {Q | ∃ f : ι → MvPolynomial (Fin N × Fin N) k, (∀ σ ∈ T, f σ ∈ D σ) ∧
    Q = ∏ σ, rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) (f σ)}

theorem E_gen (D : ι → Submodule k (MvPolynomial (Fin N × Fin N) k)) (T : Finset ι) (τ : ι)
    (π : MvPolynomial (Fin N × Fin N) k →ₗ[k] MvPolynomial (Fin N × Fin N) k) (hπ : ∀ f, π f ∈ D τ)
    (Q : MvPolynomial (BVar N ι) k) (hQ : Q ∈ gen N D T) : E N τ π Q ∈ gen N D (insert τ T) := by
  obtain ⟨f, hf, rfl⟩ := hQ
  set A := ∏ σ ∈ Finset.univ.erase τ, rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) (f σ) with hAdef
  have hsplit : ∏ σ, rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) (f σ) =
      A * rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) (f τ) :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ τ)).symm
  have hA : ∃ q, Ψ N τ A = map (algebraMap k (MvPolynomial (Fin N × Fin N) k)) q := by
    refine Finset.prod_induction _ (fun x => ∃ q, Ψ N τ x = map (algebraMap k (MvPolynomial (Fin N × Fin N) k)) q)
      (fun a b ⟨qa, ha⟩ ⟨qb, hb⟩ => ⟨qa * qb, by rw [map_mul, ha, hb, map_mul]⟩) ⟨1, by simp⟩ ?_
    intro σ hσ
    exact ⟨_, Ψ_rename_ne N τ σ (Finset.ne_of_mem_erase hσ) (f σ)⟩
  obtain ⟨q, hq⟩ := hA
  refine ⟨Function.update f τ (π (f τ)), ?_, ?_⟩
  · intro σ hσ
    by_cases h : σ = τ
    · subst h; simp [hπ]
    · rw [Function.update_of_ne h]
      exact hf σ (by simpa [h] using hσ)
  · have hA' : ∏ σ ∈ Finset.univ.erase τ,
        rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) (Function.update f τ (π (f τ)) σ) = A := by
      refine Finset.prod_congr rfl fun σ hσ => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hσ)]
    have hR : ∏ σ, rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) (Function.update f τ (π (f τ)) σ) =
        A * rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) (π (f τ)) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ), Function.update_self, hA']
    rw [hR, hsplit]
    show (Ψ N τ).symm (mr π (Ψ N τ (A * rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) (f τ)))) =
      A * rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) (π (f τ))
    rw [map_mul, hq, Ψ_rename_self, mr_map_mul, mr_C, ← Ψ_rename_self N τ, ← hq, ← map_mul,
      AlgEquiv.symm_apply_apply]

theorem span_gen_empty (D : ι → Submodule k (MvPolynomial (Fin N × Fin N) k)) (P : MvPolynomial (BVar N ι) k) :
    P ∈ Submodule.span k (gen N D ∅) := by
  have hmulX : ∀ v : BVar N ι, ∀ Q ∈ Submodule.span k (gen N D ∅), Q * X v ∈ Submodule.span k (gen N D ∅) := by
    intro v Q hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨f, -, rfl⟩ := hQ
      refine Submodule.subset_span ⟨fun σ => f σ * (if σ = v.1 then X v.2 else 1), by simp, ?_⟩
      simp only [map_mul, Finset.prod_mul_distrib]
      congr 1
      simp only [apply_ite, rename_X, map_one]
      rw [Finset.prod_ite_eq']
      simp
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h1 : (1 : MvPolynomial (BVar N ι) k) ∈ gen N D ∅ := ⟨fun _ => 1, by simp, by simp⟩
    rw [show (C a : MvPolynomial (BVar N ι) k) = a • 1 by rw [smul_eq_C_mul, mul_one]]
    exact Submodule.smul_mem _ a (Submodule.subset_span h1)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p v ih => exact hmulX v p ih

theorem mem_span_gen_univ (D : ι → Submodule k (MvPolynomial (Fin N × Fin N) k)) (P : MvPolynomial (BVar N ι) k)
    (h : ∀ τ β, AddMonoidAlgebra.coeff (Ψ N τ P) β ∈ D τ) : P ∈ Submodule.span k (gen N D Finset.univ) := by
  choose π hπ1 hπ2 using fun τ => exists_proj (D τ)
  have key : ∀ T : Finset ι, P ∈ Submodule.span k (gen N D T) := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact span_gen_empty N D P
    | insert τ T hτ ih =>
      have hfix : E N τ (π τ) P = P := by
        show (Ψ N τ).symm (mr (π τ) (Ψ N τ P)) = P
        have : mr (π τ) (Ψ N τ P) = Ψ N τ P := by
          ext β
          rw [coeff_mr, hπ2 τ _ (h τ β)]
        rw [this, AlgEquiv.symm_apply_apply]
      rw [← hfix]
      have hle : Submodule.span k (gen N D T) ≤ (Submodule.span k (gen N D (insert τ T))).comap (E N τ (π τ)) :=
        Submodule.span_le.mpr fun Q hQ => Submodule.subset_span (E_gen N D T τ (π τ) (hπ1 τ) Q hQ)
      exact hle ih
  exact key Finset.univ

end

end GlobalTheory.HighWtEmb.NabInter

namespace GlobalTheory.HighWtEmb


open NabInter in
theorem mem_nabK_of_toBlock : ∀ (k : Type) [Field k] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ν : ι → Fin N → ℕ) (P : MvPolynomial (BVar N ι) k),
    (∀ τ, toBlock k N τ P ∈ dualWeyl (MvPolynomial (OVar N τ) k) N N (ν τ)) → P ∈ nabK k N ν := by
  intro k _ N ι _ _ ν P hP
  have h : ∀ τ β, AddMonoidAlgebra.coeff (Ψ N τ P) β ∈ dualWeyl k N N (ν τ) := by
    intro τ β
    have := dualWeyl_mr (lcoeff k β) N N (ν τ) _ (hP τ)
    convert this using 1
    ext m
    rw [Ψ_eq_toBlock, coeff_mr, lcoeff_apply, coeff_coeff_commAlgEquiv]
  have := mem_span_gen_univ N (fun τ => dualWeyl k N N (ν τ)) P h
  refine Submodule.span_mono ?_ this
  rintro Q ⟨f, hf, rfl⟩
  exact ⟨f, fun τ => hf τ (Finset.mem_univ τ), rfl⟩

end GlobalTheory.HighWtEmb

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDualWeylProductSpanOfFactorwiseDualWeylStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_dualWeylProductSpan_of_factorwise_dualWeyl : ∀ (k : Type) [Field k] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (ν : ι → Fin N → ℕ) (P : MvPolynomial (BVar N ι) k), (∀ τ, toBlock k N τ P ∈ dualWeyl (MvPolynomial (OVar N τ) k) N N (ν τ)) → P ∈ nabK k N ν := by
  first | exact @GlobalTheory.HighWtEmb.mem_nabK_of_toBlock | exact GlobalTheory.HighWtEmb.mem_nabK_of_toBlock | (intros; apply GlobalTheory.HighWtEmb.mem_nabK_of_toBlock <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionIntertwinesGroupAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionIntertwinesGroupAction
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem blockRed_rowAct (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι)
    (A : ι → Matrix (Fin N) (Fin N) (O ⧸ Ideal.span {ϖ})) (M : Matrix (Fin N) (Fin N) O)
    (hA : A τ = M.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) (f : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ (rowAct O M f) = blockSub (O ⧸ Ideal.span {ϖ}) N A (blockRed O N ϖ τ f) := by
  have h : (blockRed O N ϖ τ).comp (rowAct O M) =
      ((blockSub (O ⧸ Ideal.span {ϖ}) N A).restrictScalars O).comp (blockRed O N ϖ τ) := by
    apply MvPolynomial.algHom_ext
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, rowAct, blockRed, blockSub, aeval_X, map_sum, map_mul,
      hA, Matrix.map_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    rw [aeval_C]
    rfl
  exact congrArg (fun φ => φ f) h

end GlobalTheory.HighWtEmb

theorem GlobalTheory.HighWtEmb.redT_grp : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) (g : ι → GL (Fin N) O) (y : NablaT O N mu), redT O N mu ϖ (grp O N mu g y) = blockSub (O ⧸ Ideal.span {ϖ}) N (fun τ => (((g τ)⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O).map (Ideal.Quotient.mk (Ideal.span {ϖ}))) (redT O N mu ϖ y) := by
  intro O _ N ι _ _ mu ϖ g y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul]
    have h1 := (Formalism.CohomologicalDescent.RealLocalDeltaNabla.nabla_rep_tensor_product O ι (fun _ => N) (fun _ => N) (fun τ => res N (mu τ)) g m)
    simp only [GlobalTheory.ExpFrame.grp]
    rw [h1.1]
    simp only [redT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_prod, IsScalarTower.algebraMap_apply O (O ⧸ Ideal.span {ϖ}), AlgHom.commutes]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [h1.2 τ]
    exact blockRed_rowAct O N ϖ τ _ _ rfl _
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionIntertwinesGroupActionStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylTensorReduction_intertwines_group_action : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) (g : ι → GL (Fin N) O) (y : NablaT O N mu), redT O N mu ϖ (grp O N mu g y) = blockSub (O ⧸ Ideal.span {ϖ}) N (fun τ => (((g τ)⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O).map (Ideal.Quotient.mk (Ideal.span {ϖ}))) (redT O N mu ϖ y) := by
  first | exact @GlobalTheory.HighWtEmb.redT_grp | exact GlobalTheory.HighWtEmb.redT_grp | (intros; apply GlobalTheory.HighWtEmb.redT_grp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightFormOnSimpleSubquotient
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightFormOnSimpleSubquotient
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HighWtEmb

theorem exists_prodProj (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ) (z₀ : Gm)
    (hz : ∀ τ (a : alg O N lam), IsProj O N lam τ (w τ) a → a • z₀ = z₀) (s : Finset ι) :
    ∃ e : alg O N lam, e • z₀ = z₀ ∧ ∀ x : ∀ τ, dualWeyl O N N (res N (lam τ)),
      (e : Module.End O (NablaT O N lam)) (PiTensorProduct.tprod O x) =
        PiTensorProduct.tprod O (fun σ => if σ ∈ s then rowProj O N (res N (lam σ)) (w σ) (x σ) else x σ) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_smul _ _, fun x => by simp⟩
  | insert τ s hτ ih =>
    obtain ⟨e, he, hex⟩ := ih
    obtain ⟨p, hp, -⟩ := exists_unique_isProj O N ι lam τ (w τ)
    let pA : alg O N lam := ⟨p, Algebra.subset_adjoin (Or.inr ⟨τ, w τ, hp⟩)⟩
    refine ⟨pA * e, by rw [mul_smul, he]; exact hz τ pA hp, fun x => ?_⟩
    show p ((e : Module.End O (NablaT O N lam)) _) = _
    rw [hex]
    rw [hp _ (rowProj O N (res N (lam τ)) (w τ) (x τ)) (by simp [hτ, rowProj])]
    congr 1
    funext σ
    by_cases h : σ = τ
    · subst h; simp
    · simp [Function.update_of_ne h, h]

theorem prodProj_mul_eq_zero (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (w : ι → Fin N → ℕ) (e : Module.End O (NablaT O N lam))
    (he : ∀ x : ∀ τ, dualWeyl O N N (res N (lam τ)),
      e (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (fun σ => rowProj O N (res N (lam σ)) (w σ) (x σ)))
    (τ : ι) (v : Fin N → ℕ) (a : Module.End O (NablaT O N lam)) (ha : IsProj O N lam τ v a) (hv : v ≠ w τ) : e * a = 0 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply, LinearMap.zero_apply]
  rw [ha x (rowProj O N (res N (lam τ)) v (x τ)) (by simp [rowProj]), he]
  refine (PiTensorProduct.tprod O).map_coord_zero τ ?_
  simp only [Function.update_self]
  apply Subtype.ext
  simp only [rowProj, LinearMap.restrict_apply, ZeroMemClass.coe_zero]
  rw [weightedHomogeneousComponent_of_mem (weightedHomogeneousComponent_isWeightedHomogeneous _ _), if_neg hv.symm]


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_weightForm : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], SubQ O N lam ϖ Gm → ∀ (w : ι → Fin N → ℕ) (z₀ : Gm), z₀ ≠ 0 → (∀ τ (a : alg O N lam), IsProj O N lam τ (w τ) a → a • z₀ = z₀) → ∃ φ : Gm →+ O ⧸ Ideal.span {ϖ}, φ z₀ ≠ 0 ∧ (∀ (c : O) (z : Gm), φ (algebraMap O (alg O N lam) c • z) = Ideal.Quotient.mk (Ideal.span {ϖ}) c * φ z) ∧ ∀ τ (v : Fin N → ℕ) (a : alg O N lam), IsProj O N lam τ v a → v ≠ w τ → ∀ z, φ (a • z) = 0 := by
  intro O _ _ _ N ι _ _ lam ϖ hϖ Gm _ _ hSQ w z₀ hz0 hfix

  have hkill : ∀ z : Gm, algebraMap O (alg O N lam) ϖ • z = 0 := by
    obtain ⟨U, π, hπ, h0⟩ := hSQ
    intro z
    obtain ⟨x, rfl⟩ := hπ z
    rw [← map_smul]
    exact h0 _ x rfl
  letI iO : Module O Gm := Module.compHom Gm (algebraMap O (alg O N lam))
  have hT : Module.IsTorsionBySet O Gm (Ideal.span {ϖ} : Ideal O) :=
    (Module.isTorsionBySet_span_singleton_iff ϖ).2 fun z => hkill z
  haveI hmax : (Ideal.span {ϖ} : Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI kF : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  letI iK : Module (O ⧸ Ideal.span {ϖ}) Gm := hT.module
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (O ⧸ Ideal.span {ϖ}) hz0
  obtain ⟨e, he, hex⟩ := exists_prodProj O N ι lam Gm w z₀ hfix Finset.univ
  let φ : Gm →+ O ⧸ Ideal.span {ϖ} :=
    { toFun := fun z => f (e • z)
      map_zero' := by simp
      map_add' := fun y z => by simp [smul_add] }
  refine ⟨φ, ?_, fun c z => ?_, fun τ v a ha hv z => ?_⟩
  · show f (e • z₀) ≠ 0
    rw [he]; exact hf
  · show f (e • (algebraMap O (alg O N lam) c • z)) = _ * f (e • z)
    rw [← mul_smul, ← Algebra.commutes, mul_smul]
    have : algebraMap O (alg O N lam) c • (e • z) = (Ideal.Quotient.mk (Ideal.span {ϖ}) c) • (e • z) := rfl
    rw [this, map_smul, smul_eq_mul]
  · show f (e • (a • z)) = 0
    have h0 : e * a = 0 := by
      apply Subtype.ext
      exact prodProj_mul_eq_zero O N ι lam w (e : Module.End O (NablaT O N lam))
        (fun x => by rw [hex]; simp) τ v a ha hv
    rw [← mul_smul, h0, zero_smul, map_zero]

end GlobalTheory.HighWtEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightFormOnSimpleSubquotientStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightForm_on_simple_subquotient : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], SubQ O N lam ϖ Gm → ∀ (w : ι → Fin N → ℕ) (z₀ : Gm), z₀ ≠ 0 → (∀ τ (a : alg O N lam), IsProj O N lam τ (w τ) a → a • z₀ = z₀) → ∃ φ : Gm →+ O ⧸ Ideal.span {ϖ}, φ z₀ ≠ 0 ∧ (∀ (c : O) (z : Gm), φ (algebraMap O (alg O N lam) c • z) = Ideal.Quotient.mk (Ideal.span {ϖ}) c * φ z) ∧ ∀ τ (v : Fin N → ℕ) (a : alg O N lam), IsProj O N lam τ v a → v ≠ w τ → ∀ z, φ (a • z) = 0 := by
  first | exact @GlobalTheory.HighWtEmb.exists_weightForm | exact GlobalTheory.HighWtEmb.exists_weightForm | (intros; apply GlobalTheory.HighWtEmb.exists_weightForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftDualWeylTensorReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftDualWeylTensorReduction
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem blockRed_eq_rename (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι)
    (g : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ g = rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι))
      (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [blockRed, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, blockRed, aeval_X, map_X, rename_X] at hp ⊢

theorem redT_tprod (O : Type) [CommRing O] (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O)
    (x : ∀ τ, dualWeyl O N N (res N (mu τ))) :
    redT O N mu ϖ (PiTensorProduct.tprod O x) =
      ∏ τ, rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι))
        (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (x τ : MvPolynomial (Fin N × Fin N) O)) := by
  unfold redT
  rw [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply]
  exact blockRed_eq_rename O N ϖ τ _

end GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem nabK_lift : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (mu : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (mu τ))) → GlobalTheory.HighWt.BaseChange →
    ∀ P ∈ nabK (O ⧸ Ideal.span {ϖ}) N (fun τ => res N (mu τ)), ∃ y : NablaT O N mu, redT O N mu ϖ y = P := by
  intro O _ _ _ N ι _ _ mu ϖ hϖ hanti hBC P hP
  unfold nabK at hP
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨f, hf, rfl⟩ := hP
    have hl : ∀ τ, ∃ g ∈ dualWeyl O N N (res N (mu τ)),
        MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) g = f τ :=
      fun τ => (hBC O ϖ hϖ N (res N (mu τ)) (hanti τ)).1 (f τ) (hf τ)
    choose g hg hgf using hl
    refine ⟨PiTensorProduct.tprod O (fun τ => (⟨g τ, hg τ⟩ : dualWeyl O N N (res N (mu τ)))), ?_⟩
    rw [redT_tprod]
    exact Finset.prod_congr rfl fun τ _ => by rw [hgf τ]
  | zero => exact ⟨0, map_zero _⟩
  | add P Q _ _ hP hQ =>
    obtain ⟨y, rfl⟩ := hP
    obtain ⟨z, rfl⟩ := hQ
    exact ⟨y + z, map_add _ _ _⟩
  | smul c P _ hP =>
    obtain ⟨y, rfl⟩ := hP
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨c • y, ?_⟩
    rw [LinearMap.map_smul, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]

end GlobalTheory.HighWtEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftDualWeylTensorReductionStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_dualWeylTensorReduction : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (mu τ))) → GlobalTheory.HighWt.BaseChange → ∀ P ∈ nabK (O ⧸ Ideal.span {ϖ}) N (fun τ => res N (mu τ)), ∃ y : NablaT O N mu, redT O N mu ϖ y = P := by
  first | exact @GlobalTheory.HighWtEmb.nabK_lift | exact GlobalTheory.HighWtEmb.nabK_lift | (intros; apply GlobalTheory.HighWtEmb.nabK_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulTopOfDualWeylTensorReductionEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulTopOfDualWeylTensorReductionEqZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HighWtEmb

theorem exists_basis_reduction_linearIndependent : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → GlobalTheory.HighWt.BaseChange →
    ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∃ (n : ℕ) (b : Module.Basis (Fin n) O (dualWeyl O N N ν)),
      LinearIndependent (O ⧸ Ideal.span {ϖ})
        (fun i => MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b i : MvPolynomial (Fin N × Fin N) O)) := by
  intro O _ _ _ ϖ hϖ hBC N ν hν
  haveI := GlobalTheory.NablaFin.dualWeyl_finite O N ν
  haveI : Module.Free O (dualWeyl O N N ν) := Module.free_of_finite_type_torsion_free'
  let b := (Module.Free.chooseBasis O (dualWeyl O N N ν)).reindex (Fintype.equivFin _)
  refine ⟨_, b, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  choose c hc using fun j => Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ}) (a j)
  let g : dualWeyl O N N ν := ∑ j, c j • b j
  have hg : MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (g : MvPolynomial (Fin N × Fin N) O) = 0 := by
    rw [← ha]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [g, Submodule.coe_sum, Submodule.coe_smul, map_sum, MvPolynomial.smul_eq_C_mul, map_mul, map_C, hc]
  obtain ⟨h, hh, hgh⟩ := (hBC O ϖ hϖ N ν hν).2 g g.2 hg
  have hgh' : g = ϖ • (⟨h, hh⟩ : dualWeyl O N N ν) := Subtype.ext (by simpa using hgh)
  have hci : c i = ϖ * b.repr ⟨h, hh⟩ i := by
    have h2 := congrArg (fun x => b.repr x i) hgh'
    simp only [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul] at h2
    rw [← h2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [g, map_sum, Finsupp.single_apply]
  rw [← hc i, hci, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ), zero_mul]

theorem exists_dual_family (k : Type) [Field k] (σ : Type) (κ : Type) [DecidableEq κ] (v : κ → MvPolynomial σ k)
    (hv : LinearIndependent k v) : ∃ ψ : κ → (MvPolynomial σ k →ₗ[k] k), ∀ i l, ψ l (v i) = if i = l then 1 else 0 := by
  let B := Module.Basis.span hv
  refine ⟨fun l => (LinearMap.exists_extend (B.coord l)).choose, fun i l => ?_⟩
  have h := (LinearMap.exists_extend (B.coord l)).choose_spec
  have hvi : v i ∈ Submodule.span k (Set.range v) := Submodule.subset_span ⟨i, rfl⟩
  have h1 := LinearMap.congr_fun h ⟨v i, hvi⟩
  have hBi : B i = ⟨v i, hvi⟩ := Module.Basis.span_apply hv i
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
  rw [h1, ← hBi, B.coord_apply, B.repr_self, Finsupp.single_apply]

theorem curry_sum_mapDomain {ι σ : Type} [Fintype ι] [DecidableEq ι] (F : ι → σ →₀ ℕ) (τ : ι) :
    (∑ ρ, Finsupp.mapDomain (fun s : σ => ((ρ, s) : ι × σ)) (F ρ)).curry τ = F τ := by
  classical
  ext s
  rw [Finsupp.curry_apply, Finsupp.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_single τ]
  · exact Finsupp.mapDomain_apply_of_injective (fun _ _ h => congrArg Prod.snd h) _ _
  · intro ρ _ hρ
    apply Finsupp.mapDomain_notin_range
    rintro ⟨t, ht⟩
    exact hρ (congrArg Prod.fst ht)
  · simp

theorem exists_prod_functional : ∀ (k : Type) [CommRing k] (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type)
    (φ : ι → (MvPolynomial σ k →ₗ[k] k)), ∃ Φ : MvPolynomial (ι × σ) k →ₗ[k] k,
      ∀ f : ι → MvPolynomial σ k, Φ (∏ τ, rename (fun s : σ => ((τ, s) : ι × σ)) (f τ)) = ∏ τ, φ τ (f τ) := by
  intro k _ ι _ _ σ φ
  classical
  let w : ((ι × σ) →₀ ℕ) → k := fun M => ∏ τ, φ τ (monomial (M.curry τ) 1)
  let Φ := (MvPolynomial.basisMonomials (ι × σ) k).constr k w
  have hmono : ∀ M c, Φ (monomial M c) = c * w M := by
    intro M c
    have : (monomial M c : MvPolynomial (ι × σ) k) = c • (MvPolynomial.basisMonomials (ι × σ) k M) := by
      rw [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul, Module.Basis.constr_basis, smul_eq_mul]
  have hφ : ∀ τ m c, φ τ (monomial m c) = c * φ τ (monomial m 1) := by
    intro τ m c
    rw [← smul_eq_mul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
  refine ⟨Φ, fun f => ?_⟩
  have h1 : ∀ τ, rename (fun s : σ => ((τ, s) : ι × σ)) (f τ) =
      ∑ m ∈ (f τ).support, monomial (Finsupp.mapDomain (fun s : σ => ((τ, s) : ι × σ)) m) (AddMonoidAlgebra.coeff (f τ) m) := by
    intro τ
    conv_lhs => rw [as_sum (f τ)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, rename_monomial]
  have h2 : ∀ τ, φ τ (f τ) = ∑ m ∈ (f τ).support, AddMonoidAlgebra.coeff (f τ) m * φ τ (monomial m 1) := by
    intro τ
    conv_lhs => rw [as_sum (f τ)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => hφ τ m _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.prod_congr rfl (fun τ _ => h1 τ), Finset.prod_congr rfl (fun τ _ => h2 τ), Finset.prod_univ_sum,
    Finset.prod_univ_sum, map_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [← monomial_sum_prod, hmono]
  simp only [w, curry_sum_mapDomain, Finset.prod_mul_distrib]

theorem linearIndependent_prod_rename : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    (v : ∀ τ, κ τ → MvPolynomial σ k), (∀ τ, LinearIndependent k (v τ)) →
    LinearIndependent k (fun p : (∀ τ, κ τ) => ∏ τ, rename (fun s : σ => ((τ, s) : ι × σ)) (v τ (p τ))) := by
  intro k _ ι _ _ σ κ _ v hv
  classical
  choose ψ hψ using fun τ => exists_dual_family k σ (κ τ) (v τ) (hv τ)
  rw [Fintype.linearIndependent_iff]
  intro a ha l
  obtain ⟨Φ, hΦ⟩ := exists_prod_functional k ι σ (fun τ => ψ τ (l τ))
  have h := congrArg Φ ha
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at h
  simp only [map_smul, hΦ, hψ, smul_eq_mul] at h
  rw [Finset.sum_eq_single l] at h
  · simpa using h
  · intro p _ hp
    obtain ⟨τ, hτ⟩ : ∃ τ, p τ ≠ l τ := by
      by_contra hc
      push_neg at hc
      exact hp (funext hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ), mul_zero]
  · simp

theorem blockRed_eq (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι) (g : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ g = rename (fun s : Fin N × Fin N => ((τ, s) : BVar N ι)) (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [blockRed, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp => simp [hp, blockRed] at *

theorem mem_smul_top_of_redT_eq_zero : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (mu : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (mu τ))) → GlobalTheory.HighWt.BaseChange →
    ∀ y : NablaT O N mu, redT O N mu ϖ y = 0 → y ∈ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu)) := by
  intro O _ _ _ N ι _ _ mu ϖ hϖ hanti hBC y hy
  haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  have hb := fun τ => exists_basis_reduction_linearIndependent O ϖ hϖ hBC N (res N (mu τ)) (hanti τ)
  choose n b hli using hb
  let B := Basis.piTensorProduct b
  have hred : ∀ p, redT O N mu ϖ (B p) = ∏ τ, rename (fun s : Fin N × Fin N => ((τ, s) : BVar N ι))
      (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ (p τ) : MvPolynomial (Fin N × Fin N) O)) := by
    intro p
    simp only [B, Basis.piTensorProduct_apply, redT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, AlgHom.toLinearMap_apply]
    exact Finset.prod_congr rfl fun τ _ => blockRed_eq O N ϖ τ _
  have hL := linearIndependent_prod_rename (O ⧸ Ideal.span {ϖ}) ι (Fin N × Fin N) (fun τ => Fin (n τ))
    (fun τ i => MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ i : MvPolynomial (Fin N × Fin N) O)) hli
  rw [Fintype.linearIndependent_iff] at hL
  have hy' : ∑ p, Ideal.Quotient.mk (Ideal.span {ϖ}) (B.repr y p) • ∏ τ, rename (fun s : Fin N × Fin N => ((τ, s) : BVar N ι))
      (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ (p τ) : MvPolynomial (Fin N × Fin N) O)) = 0 := by
    rw [← hy]
    conv_rhs => rw [← B.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [LinearMap.map_smul, hred]
    exact algebraMap_smul (O ⧸ Ideal.span {ϖ}) (B.repr y p) _
  have hc := hL _ hy'
  rw [← B.sum_repr y]
  refine Submodule.sum_mem _ fun p _ => ?_
  have hp : B.repr y p ∈ Ideal.span {ϖ} := Ideal.Quotient.eq_zero_iff_mem.mp (hc p)
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hp
  rw [← hd, mul_comm, mul_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ) Submodule.mem_top

end GlobalTheory.HighWtEmb

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulTopOfDualWeylTensorReductionEqZeroStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_smul_top_of_dualWeylTensorReduction_eq_zero : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (mu τ))) → GlobalTheory.HighWt.BaseChange → ∀ y : NablaT O N mu, redT O N mu ϖ y = 0 → y ∈ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu)) := by
  first | exact @GlobalTheory.HighWtEmb.mem_smul_top_of_redT_eq_zero | exact GlobalTheory.HighWtEmb.mem_smul_top_of_redT_eq_zero | (intros; apply GlobalTheory.HighWtEmb.mem_smul_top_of_redT_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleSubquotientEmbedsDualWeylReductionMaxWeigh
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb


set_option maxHeartbeats 1000000 in
theorem embeds_of_maxWeight : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → GlobalTheory.HighWt.BaseChange → GlobalTheory.HighWt.CoefIn O N lam → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], IsSimpleModule (alg O N lam) Gm → SubQ O N lam ϖ Gm → ∀ w : ι → Fin N → ℕ, (∀ τ, Antitone (w τ)) → GlobalTheory.HighWt.JointWt O N lam Gm w → (∀ w' : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w) → Embeds O N lam (GlobalTheory.HighWt.extW N w) ϖ Gm := by
  intro O _ _ _ _ N ι _ _ lam ϖ hϖ hlam hBC hC Gm _ _ hS hSQ w hw hJ hmax
  obtain ⟨z₀, hz₀, hfix⟩ := hJ
  obtain ⟨φ, hφ0, hφc, hφp⟩ := GlobalTheory.T.exists_weightForm_on_simple_subquotient O N ι lam ϖ hϖ Gm hSQ w z₀ hz₀ hfix
  obtain ⟨Pz, hPc, hPg, hPp, hPn, hPz0⟩ :=
    GlobalTheory.T.exists_matrixCoefficientPoly_simpleSubquotient O N ι lam ϖ hϖ hlam hC Gm hSQ w hmax φ z₀ hφ0 hfix hφc hφp
  have hmuA : ∀ τ, Antitone (res N (GlobalTheory.HighWt.extW N w τ)) := fun τ => by
    rw [GlobalTheory.HighWt.res_extW]; exact hw τ
  have hle : (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w))) ≤
      LinearMap.ker (redT O N (GlobalTheory.HighWt.extW N w) ϖ) := by
    refine Submodule.smul_le.2 fun r hr n _ => ?_
    rw [LinearMap.mem_ker, map_smul]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq, map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ϖ), mul_zero, map_zero, zero_mul]
  set L := (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w))).liftQ
    (redT O N (GlobalTheory.HighWt.extW N w) ϖ) hle with hL
  have hLmk : ∀ y, L (Submodule.Quotient.mk y) = redT O N (GlobalTheory.HighWt.extW N w) ϖ y := fun y => rfl
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, hL, Submodule.ker_liftQ_eq_bot]
    intro y hy
    exact GlobalTheory.T.mem_smul_top_of_dualWeylTensorReduction_eq_zero O N ι (GlobalTheory.HighWt.extW N w) ϖ hϖ hmuA hBC y hy
  have hsurj : ∀ z, ∃ q, L q = Pz z := by
    intro z
    have h1 : Pz z ∈ nabK (O ⧸ Ideal.span {ϖ}) N (fun τ => res N (GlobalTheory.HighWt.extW N w τ)) := by
      have e : (fun τ => res N (GlobalTheory.HighWt.extW N w τ)) = w := funext fun τ => GlobalTheory.HighWt.res_extW N w τ
      rw [e]
      haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
      letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
      exact GlobalTheory.T.mem_dualWeylProductSpan_of_factorwise_dualWeyl (O ⧸ Ideal.span {ϖ}) N ι w (Pz z) (hPn z)
    obtain ⟨y, hy⟩ := GlobalTheory.T.exists_lift_dualWeylTensorReduction O N ι (GlobalTheory.HighWt.extW N w) ϖ hϖ hmuA hBC _ h1
    exact ⟨Submodule.Quotient.mk y, hy⟩
  choose q hq using hsurj
  have hsm : ∀ (a : alg O N lam) (z : Gm), Pz z = 0 → Pz (a • z) = 0 := by
    rintro ⟨a, ha⟩
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      intro z hz
      rcases hx with ⟨g, rfl⟩ | ⟨τ, v, hp⟩
      · have e : (⟨grp O N lam g, Algebra.subset_adjoin (Or.inl ⟨g, rfl⟩)⟩ : alg O N lam) = grpA O N lam g := rfl
        rw [e, hPg, hz, map_zero]
      · rw [hPp τ v _ hp, hz, map_zero]
    | algebraMap c =>
      intro z hz
      have e : (⟨algebraMap O _ c, Subalgebra.algebraMap_mem _ c⟩ : alg O N lam) = algebraMap O (alg O N lam) c := rfl
      rw [e, hPc, hz, mul_zero]
    | add x y hx hy ihx ihy =>
      intro z hz
      have e : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : alg O N lam) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [e, add_smul, map_add (f := _), ihx z hz, ihy z hz, add_zero]
    | mul x y hx hy ihx ihy =>
      intro z hz
      have e : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : alg O N lam) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, mul_smul]
      exact ihx _ (ihy z hz)
  let K : Submodule (alg O N lam) Gm :=
    { carrier := {z | Pz z = 0}
      add_mem' := fun {a b} ha hb => by simp only [Set.mem_setOf_eq, map_add (f := _)] at *; rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun a z hz => hsm a z hz }
  have hK : K = ⊥ := by
    haveI : IsSimpleOrder (Submodule (alg O N lam) Gm) := (isSimpleModule_iff _ _).1 hS
    rcases IsSimpleOrder.eq_bot_or_eq_top K with h | h
    · exact h
    · exfalso
      have : z₀ ∈ K := h ▸ Submodule.mem_top
      exact hPz0 this
  let ψ : Gm →+ NablaT O N (GlobalTheory.HighWt.extW N w) ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w))) :=
    { toFun := q
      map_zero' := hLinj (by rw [hq, map_zero, map_zero])
      map_add' := fun a b => hLinj (by rw [hq, map_add (f := _), map_add (f := _), hq, hq]) }
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : Pz (a - b) = 0 := by
      rw [map_sub, ← hq a, ← hq b]
      exact sub_eq_zero.2 (congrArg L hab)
    have h2 : a - b ∈ K := h1
    rw [hK, Submodule.mem_bot] at h2
    exact sub_eq_zero.1 h2
  · intro c z
    apply hLinj
    change L (q _) = L (c • q z)
    rw [hq, hPc, LinearMap.map_smul, hq, Algebra.smul_def, MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq]
  · intro g z y hzy
    apply hLinj
    change L (q _) = _
    have hzy' : q z = Submodule.Quotient.mk y := hzy
    rw [hq, hLmk, GlobalTheory.T.dualWeylTensorReduction_intertwines_group_action, hPg, ← hq z, hzy', hLmk]
  · intro τ v a a' ha ha' z y hzy
    apply hLinj
    change L (q _) = _
    have hzy' : q z = Submodule.Quotient.mk y := hzy
    rw [hq, hLmk, GlobalTheory.T.dualWeylTensorReduction_weightProjector O N ι _ ϖ τ v a' ha', hPp τ v a ha, ← hq z, hzy', hLmk]

end GlobalTheory.HighWtEmb

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleSubquotientEmbedsDualWeylReductionMaxWeighStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simple_subquotient_embeds_dualWeyl_reduction_maxWeight : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → GlobalTheory.HighWt.BaseChange → GlobalTheory.HighWt.CoefIn O N lam → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], IsSimpleModule (alg O N lam) Gm → SubQ O N lam ϖ Gm → ∀ w : ι → Fin N → ℕ, (∀ τ, Antitone (w τ)) → GlobalTheory.HighWt.JointWt O N lam Gm w → (∀ w' : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w) → Embeds O N lam (GlobalTheory.HighWt.extW N w) ϖ Gm := by
  first | exact @GlobalTheory.HighWtEmb.embeds_of_maxWeight | exact GlobalTheory.HighWtEmb.embeds_of_maxWeight | (intros; apply GlobalTheory.HighWtEmb.embeds_of_maxWeight <;> assumption)
end
