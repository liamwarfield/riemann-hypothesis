module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorDualRepDualHighestWeightAtEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZariskiDenseRationalPointsDefiniteUnitaryCharZer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualUpperTriangularEigenvecto
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualUpperTriangularEigenvecto
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.AlgWtF.DDHwT

section Fam

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K]


open Classical in
def fam (τ : L →+* K) (B : GL (Fin n) K) : (L →+* K) → GL (Fin n) K := fun σ =>
  if σ = τ then B else if σ = τ.comp (IsCMField.complexConj L : L →+* L) then inside₂ K n B else 1

theorem fam_conj (τ : L →+* K) (B : GL (Fin n) K) (h : τ.comp (IsCMField.complexConj L : L →+* L) ≠ τ)
    (σ : L →+* K) : ((fam τ B (σ.comp (IsCMField.complexConj L : L →+* L)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.transpose (((fam τ B σ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hcc : ∀ σ' : L →+* K, (σ'.comp (IsCMField.complexConj L : L →+* L)).comp (IsCMField.complexConj L : L →+* L) = σ' := by
    intro σ'
    ext x
    simp [IsCMField.complexConj_apply_apply]
  have hinj : ∀ σ₁ σ₂ : L →+* K, σ₁.comp (IsCMField.complexConj L : L →+* L) = σ₂.comp (IsCMField.complexConj L : L →+* L) → σ₁ = σ₂ := by
    intro σ₁ σ₂ e
    rw [← hcc σ₁, e, hcc]
  by_cases h1 : σ = τ
  · subst h1
    simp only [fam, h, if_false, if_true]
    rfl
  · by_cases h2 : σ = τ.comp (IsCMField.complexConj L : L →+* L)
    · subst h2
      simp only [fam, hcc, if_true, h]
      simp [inside₂]
    · have h3 : σ.comp (IsCMField.complexConj L : L →+* L) ≠ τ := by
        intro e; apply h2; rw [← e, hcc]
      have h4 : σ.comp (IsCMField.complexConj L : L →+* L) ≠ τ.comp (IsCMField.complexConj L : L →+* L) :=
        fun e => h1 (hinj _ _ e)
      simp [fam, h1, h2, h3, h4]

theorem fam_eval (τ : L →+* K) (B : GL (Fin n) K) :
    (fun p : (L →+* K) × Fin n × Fin n => ((fam τ B p.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.2.1 p.2.2) =
      Formalism.L2.NX.evPtF (IsCMField.complexConj L : L →+* L) τ B := by
  funext p
  simp only [fam, Formalism.L2.NX.evPtF]
  split_ifs <;> simp_all [inside₂, Matrix.one_apply]

end Fam

section Eig

open Formalism.L2.DIV

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K]

theorem bVVfun_mem (lam : ι → DomWeight n) (j : VVIdx lam) : bVVfun K lam j ∈ VV K lam := by
  rw [← (bVVfun_spec K lam).2]
  exact Submodule.subset_span ⟨j, rfl⟩

def wOf (lam : ι → DomWeight n) (u : VVIdx lam → K) : Pol K ι n := ∑ j, u j • bVVfun K lam j

theorem wOf_mem (lam : ι → DomWeight n) (u : VVIdx lam → K) : wOf lam u ∈ VV K lam :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bVVfun_mem lam j)

theorem wOf_ne (lam : ι → DomWeight n) (u : VVIdx lam → K) (hu : u ≠ 0) : wOf lam u ≠ 0 := by
  intro h0
  apply hu
  funext j
  exact Fintype.linearIndependent_iff.mp (bVVfun_spec K lam).1 u h0 j

theorem wOf_eig (lam : ι → DomWeight n) (M : ι → Matrix (Fin n) (Fin n) K)
    (hMV : ∀ F ∈ VV K lam, Formalism.GradedWeylDivisibility.blockAct K M F ∈ VV K lam) (c χ : K) (hc : c ≠ 0) (u : VVIdx lam → K)
    (h : ∀ i, ∑ j, c * DDHw.coord lam i (Formalism.GradedWeylDivisibility.blockAct K M (bVVfun K lam j)) * u j = χ * u i) :
    Formalism.GradedWeylDivisibility.blockAct K M (wOf lam u) = (c⁻¹ * χ) • wOf lam u := by
  classical
  set w := wOf lam u with hw
  set F : VV K lam := ⟨_, hMV w (wOf_mem lam u)⟩ with hF
  have hco : ∀ i, (bVV K lam).repr F i = c⁻¹ * χ * u i := by
    intro i
    have e1 : c * DDHw.coord lam i (Formalism.GradedWeylDivisibility.blockAct K M w) = χ * u i := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h i, hw, wOf, map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, map_smul, smul_eq_mul]
      ring
    have e2 : DDHw.coord lam i (Formalism.GradedWeylDivisibility.blockAct K M w) = (bVV K lam).repr F i := DDHw.coord_spec lam i F
    rw [← e2, mul_assoc, ← e1, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hsum := congrArg Subtype.val ((bVV K lam).sum_repr F)
  rw [Submodule.coe_sum] at hsum
  simp only [Submodule.coe_smul, bVV_coe, hco] at hsum
  show (F : Pol K ι n) = _
  rw [← hsum, hw, wOf, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]

theorem blockAct_mem [DecidableEq ι] (lam : ι → DomWeight n) (τ₀ : ι) (B : GL (Fin n) K) (F : Pol K ι n)
    (hF : F ∈ VV K lam) :
    Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) F ∈ VV K lam := by
  set g : ι → GL (Fin n) K := fun τ => if τ = τ₀ then B else 1 with hg
  have hgM : (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose) =
      fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1 := by
    funext τ
    by_cases h : τ = τ₀ <;> simp [hg, h]
  have hdet : detTwK lam g ≠ 0 := by
    unfold detTwK
    exact Finset.prod_ne_zero_iff.2 fun τ _ => Units.ne_zero _
  have e : actP lam g F = detTwK lam g •
      Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) F := by
    rw [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, trAct, hgM]
  have h1 := polyAction_mem_VV lam g hF
  rw [e] at h1
  exact (Submodule.smul_mem_iff _ hdet).1 h1

end Eig

section Main

open Formalism.L2.DIV
open scoped Matrix

theorem hw_eigvec_transport : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (K : Type) [Field K] [CharZero K] (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb →
    ∀ (τ₀ : ι) (mu : Fin n → ℤ),
      NX.HWAtF (IsCMField.complexConj L : L →+* L) (GlobalTheory.AlgWtF.wtRepF emb lam).dual (emb τ₀) mu →
      ∃ w : Formalism.L2.DIV.Pol K ι n, w ∈ Formalism.L2.DIV.VV K lam ∧ w ≠ 0 ∧
        ∀ B : GL (Fin n) K, (B : Matrix (Fin n) (Fin n) K).BlockTriangular id →
          Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) w =
            ((detPow K n B (lam τ₀).detShift)⁻¹ * ∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a) • w := by
  intro L _ _ _ n ι _ _ K _ _ emb lam hd τ₀ mu hH
  classical
  obtain ⟨ι', _, _, b', P', hP', v, hv, hB⟩ := hH
  have hinj := hd.1
  have hcm := hd.2
  set bD := DDHw.bDD (K := K) lam with hbD
  set Q : Matrix ι' (VVIdx lam) K := b'.toMatrix bD with hQ
  set Q' : Matrix (VVIdx lam) ι' K := bD.toMatrix b' with hQ'
  have hQQ : Q * Q' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hQQ' : Q' * Q = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hrat : ∀ a a', ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2))
        (P' a a' - ∑ i, ∑ j, MvPolynomial.C (Q a i * Q' j a') * DDHw.tenPF emb lam i j) = 0 := by
    intro a a' γ₀ hγ
    obtain ⟨γ, rfl⟩ := ratHom_surjective L n γ₀ hγ
    have hm : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        ((ratHom (L := L) (n := n) γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
      rw [show ratHom (L := L) (n := n) γ = ratFun γ from rfl, ← incGL_ratFun γ]
      rfl
    have h1 := congrFun (congrFun (hP' γ _ hm) a) a'
    have h2 : LinearMap.toMatrix b' b' ((wtRepF emb lam).dual γ) =
        Q * LinearMap.toMatrix bD bD ((wtRepF emb lam).dual γ) * Q' :=
      (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b' bD b' bD _).symm
    rw [hbD, DDHw.dd_toMatrix, DDHw.tenRepF_toMatrix emb lam γ _ hm] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, ← h1, h2, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, Matrix.mul_apply, Finset.sum_mul]
    rw [sub_eq_zero, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    erw [Matrix.mul_apply]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  set u : VVIdx lam → K := Q' *ᵥ v with hu
  have hu0 : u ≠ 0 := by
    intro h0
    apply hv
    have e : Q *ᵥ u = v := by rw [hu, Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]
    rw [← e, h0, Matrix.mulVec_zero]
  refine ⟨wOf lam u, wOf_mem lam u, wOf_ne lam u hu0, fun B hBt => ?_⟩
  have hne : (emb τ₀).comp (IsCMField.complexConj L : L →+* L) ≠ emb τ₀ := fun h' => hcm τ₀ τ₀ h'.symm
  set T : Matrix (VVIdx lam) (VVIdx lam) K := Matrix.of fun i j =>
    MvPolynomial.eval (NX.evPtF (IsCMField.complexConj L : L →+* L) (emb τ₀) B) (DDHw.tenPF emb lam i j) with hT
  have hev : ∀ a a', MvPolynomial.eval (NX.evPtF (IsCMField.complexConj L : L →+* L) (emb τ₀) B) (P' a a') =
      ∑ i, ∑ j, Q a i * Q' j a' * T i j := by
    intro a a'
    have h0 := GlobalTheory.T.zariskiDense_rationalPoints_definiteUnitary_charZero L n K _ (hrat a a') (fam (emb τ₀) B) (fam_conj _ B hne)
    rw [fam_eval, map_sub, sub_eq_zero] at h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h0, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, hT, Matrix.of_apply]
  have hmat : (Matrix.of fun a a' => MvPolynomial.eval (NX.evPtF (IsCMField.complexConj L : L →+* L) (emb τ₀) B) (P' a a')) =
      Q * T * Q' := by
    ext a a'
    rw [Matrix.of_apply, hev, Matrix.mul_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  set χ : K := ∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a with hχ
  have hTu : T *ᵥ u = χ • u := by
    have h1 := hB B hBt
    rw [hmat] at h1
    have e : Q' *ᵥ ((Q * T * Q') *ᵥ v) = T *ᵥ u := by
      rw [hu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ', Matrix.one_mul]
    rw [← e, h1, Matrix.mulVec_smul]
  set c : K := detPow K n B (lam τ₀).detShift with hc
  have hc0 : c ≠ 0 := by
    rw [hc, detPow]
    exact Units.ne_zero _
  have hM : (fun τ => (Matrix.of fun a b => NX.evPtF (DDHw.cL L) (emb τ₀) B (emb τ, a, b)).transpose) =
      fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1 := by
    funext τ
    split_ifs with hτ
    · rw [hτ, DDHw.evPtF_self]
    · rw [DDHw.evPtF_other _ _ _ _ (fun h' => hτ (hinj h')) (hcm τ τ₀), Matrix.transpose_one]
  have hTe : ∀ i j, T i j = c * DDHw.coord lam i
      (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) (bVVfun K lam j)) := by
    intro i j
    rw [hT, Matrix.of_apply, DDHw.tenPF_eval]
    erw [DDHw.detTwistPolynomial_eval_embeddingPoint emb hd lam τ₀ B]
    rw [← hM]
  refine wOf_eig lam _ (blockAct_mem lam τ₀ B) c χ hc0 u fun i => ?_
  have := congrFun hTu i
  simp only [Matrix.mulVec, dotProduct, hTe, Pi.smul_apply, smul_eq_mul] at this
  exact this

end Main

end GlobalTheory.AlgWtF.DDHwT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualUpperTriangularEigenvectoStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highestWeight_doubleDual_upperTriangular_eigenvector : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (K : Type) [Field K] [CharZero K] (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb →
    ∀ (τ₀ : ι) (mu : Fin n → ℤ),
      NX.HWAtF (IsCMField.complexConj L : L →+* L) (GlobalTheory.AlgWtF.wtRepF emb lam).dual (emb τ₀) mu →
      ∃ w : Formalism.L2.DIV.Pol K ι n, w ∈ Formalism.L2.DIV.VV K lam ∧ w ≠ 0 ∧
        ∀ B : GL (Fin n) K, (B : Matrix (Fin n) (Fin n) K).BlockTriangular id →
          Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) w =
            ((detPow K n B (lam τ₀).detShift)⁻¹ * ∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a) • w := by
  first | exact @GlobalTheory.AlgWtF.DDHwT.hw_eigvec_transport | exact GlobalTheory.AlgWtF.DDHwT.hw_eigvec_transport | (intros; apply GlobalTheory.AlgWtF.DDHwT.hw_eigvec_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NablaSqUpperEigenvectorWeightEqHighest
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NablaSqUpperEigenvectorWeightEqHighest
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

open scoped Matrix

namespace GlobalTheory.HwEigen

theorem rowAct_transvection_eq_eval (K : Type) [Field K] (n : ℕ) (a b : Fin n) (hab : a ≠ b) (s : K)
    (f : MvPolynomial (Fin n × Fin n) K) :
    Formalism.GradedWeylDivisibility.rowAct K (n := n) (Matrix.transvection a b s)ᵀ f =
      (Formalism.GradedWeylDivisibility.rowGen K a b f).eval (MvPolynomial.C s) := by
  have h : (Polynomial.evalRingHom (MvPolynomial.C s)).comp (Formalism.GradedWeylDivisibility.rowGen K (n := n) a b).toRingHom =
      (Formalism.GradedWeylDivisibility.rowAct K (n := n) (Matrix.transvection a b s)ᵀ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [Formalism.GradedWeylDivisibility.rowGen, Formalism.GradedWeylDivisibility.rowAct]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Formalism.GradedWeylDivisibility.rowGen,
        Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, Polynomial.coe_evalRingHom]
      simp [Matrix.transvection, Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply,
        Matrix.single_apply, add_mul, Finset.sum_add_distrib]
      split_ifs with hv
      · rw [Finset.sum_eq_single a]
        · simp only [hv, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, and_self, if_true]
          exact mul_comm _ _
        · intro c _ hc
          simp [Ne.symm hc]
        · simp
      · simp [Ne.symm hv]
  exact (congrArg (fun φ => φ f) h).symm

end GlobalTheory.HwEigen

namespace GlobalTheory.HwEigen

theorem sqAct_smul' (K : Type) [Field K] (n : ℕ) (lam : DomWeight n) (B : GL (Fin n) K) (c : K)
    (f : MvPolynomial (Fin n × Fin n) K) : sqAct K n lam B (c • f) = c • sqAct K n lam B f := by
  unfold sqAct
  rw [map_smul, smul_comm]

theorem rowDiv_eq_zero_of_fixed (K : Type) [Field K] [Infinite K] (n : ℕ) (a b : Fin n) (hab : a ≠ b)
    (f : MvPolynomial (Fin n × Fin n) K)
    (hfix : ∀ s : K, Formalism.GradedWeylDivisibility.rowAct K (n := n) (Matrix.transvection a b s)ᵀ f = f)
    (k : ℕ) (hk : 1 ≤ k) : Formalism.GradedWeylDivisibility.rowDiv K a b k f = 0 := by
  have hP : Formalism.GradedWeylDivisibility.rowGen K a b f - Polynomial.C f = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem (f := fun s : K => (MvPolynomial.C s : MvPolynomial (Fin n × Fin n) K))
      (MvPolynomial.C_injective _ _)
    intro s
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C]
    rw [← rowAct_transvection_eq_eval K n a b hab s, hfix s, sub_self]
  have h := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k) hP
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_zero] at h
  rw [if_neg (by omega), sub_zero] at h
  exact h

theorem mu_eq_of_upper_eigen : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam0 : DomWeight n) (mu : Fin n → ℤ)
    (f : MvPolynomial (Fin n × Fin n) K), f ∈ nablaSq K n lam0 → f ≠ 0 →
    (∀ B : GL (Fin n) K, (B : Matrix (Fin n) (Fin n) K).BlockTriangular id →
      sqAct K n lam0 B f = (∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a) • f) → mu = lam0.w := by
  intro K _ _ n lam0 mu f hf hf0 hB
  haveI : Infinite K := inferInstance

  have hkill : ∀ a b : Fin n, a < b → ∀ k : ℕ, 1 ≤ k → Formalism.GradedWeylDivisibility.rowDiv K a b k f = 0 := by
    intro a b hab k hk
    have hne : a ≠ b := ne_of_lt hab
    apply rowDiv_eq_zero_of_fixed K n a b hne f _ k hk
    intro s
    have hdet : (Matrix.transvection a b s).det = 1 := Matrix.det_transvection_of_ne a b hne s
    let B : GL (Fin n) K := Matrix.nonsingInvUnit _ (by rw [hdet]; exact isUnit_one)
    have hBv : (B : Matrix (Fin n) (Fin n) K) = Matrix.transvection a b s := rfl
    have hent : ∀ i j, (B : Matrix (Fin n) (Fin n) K) i j = (if i = j then 1 else 0) + (if a = i ∧ b = j then s else 0) := by
      intro i j
      rw [hBv]
      simp [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have htri : (B : Matrix (Fin n) (Fin n) K).BlockTriangular id := by
      intro i j hij
      rw [hent]
      have h1 : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
      have h2 : ¬ (a = i ∧ b = j) := by
        rintro ⟨rfl, rfl⟩
        exact lt_asymm hab hij
      simp [h1, h2]
    have hdiag : ∀ i, (B : Matrix (Fin n) (Fin n) K) i i = 1 := by
      intro i
      rw [hent]
      have h2 : ¬ (a = i ∧ b = i) := by
        rintro ⟨rfl, h⟩
        exact hne h.symm
      simp [h2]
    have h := hB B htri
    simp only [hdiag, one_zpow, Finset.prod_const_one, one_smul] at h
    have hdp : detPow K n B lam0.detShift = 1 := by
      unfold detPow
      have : Matrix.GeneralLinearGroup.det B = 1 := by
        ext
        simp [Matrix.GeneralLinearGroup.val_det_apply, hBv, hdet]
      rw [this, one_zpow, Units.val_one]
    unfold sqAct at h
    rw [hdp, one_smul, hBv] at h
    exact h

  obtain ⟨c, hc⟩ := Formalism.GradedWeylDivisibility.hwLine K n n le_rfl lam0.natW (PI.WGB.natW_anti_A lam0) f hf hkill
  have he : extremal K n lam0 ≠ 0 := Formalism.GradedWeylDivisibility.hwNe K n n le_rfl lam0.natW
  have hce : f = c • extremal K n lam0 := hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hf0 (by rw [hce, zero_smul])

  funext i
  let d : Fin n → K := Function.update (fun _ => 1) i 2
  have hdd : (Matrix.diagonal d).det = 2 := by
    rw [Matrix.det_diagonal, Finset.prod_eq_single i]
    · simp [d]
    · intro j _ hj
      simp [d, hj]
    · simp
  let B : GL (Fin n) K := Matrix.nonsingInvUnit _ (by rw [hdd]; exact isUnit_iff_ne_zero.mpr two_ne_zero)
  have hBv : (B : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d := rfl
  have htri : (B : Matrix (Fin n) (Fin n) K).BlockTriangular id := by
    rw [hBv]; exact Matrix.blockTriangular_diagonal d
  have h := hB B htri
  rw [hce, sqAct_smul', GlobalTheory.AlgWtF.DDHw.sqAct_upper K n lam0 B htri, smul_smul, smul_smul] at h
  have h2 := smul_left_injective K he h
  have hprod : ∀ m : Fin n → ℤ, (∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ m a) = (2 : K) ^ m i := by
    intro m
    rw [Finset.prod_eq_single i]
    · simp [hBv, d]
    · intro j _ hj
      simp [hBv, d, hj]
    · simp
  simp only [hprod] at h2
  have h3 : ((2 : K) ^ lam0.w i) = (2 : K) ^ mu i := by
    have := h2
    rw [mul_comm] at this
    exact (mul_right_cancel₀ hc0 this)
  have h4 : (((2 : ℚ) ^ lam0.w i : ℚ) : K) = (((2 : ℚ) ^ mu i : ℚ) : K) := by
    rw [Rat.cast_zpow, Rat.cast_zpow, Rat.cast_ofNat]
    exact h3
  have h5 := Rat.cast_injective h4
  exact (zpow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num) h5).symm

end GlobalTheory.HwEigen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NablaSqUpperEigenvectorWeightEqHighestStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nablaSq_upperEigenvector_weight_eq_highest : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam0 : DomWeight n) (mu : Fin n → ℤ)
    (f : MvPolynomial (Fin n × Fin n) K), f ∈ nablaSq K n lam0 → f ≠ 0 →
    (∀ B : GL (Fin n) K, (B : Matrix (Fin n) (Fin n) K).BlockTriangular id →
      sqAct K n lam0 B f = (∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a) • f) → mu = lam0.w := by
  first | exact @GlobalTheory.HwEigen.mu_eq_of_upper_eigen | exact GlobalTheory.HwEigen.mu_eq_of_upper_eigen | (intros; apply GlobalTheory.HwEigen.mu_eq_of_upper_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpecialisationCoefficientSpaceToDualWeyl
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpecialisationCoefficientSpaceToDualWeyl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.SpecFactor

open MvPolynomial

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι] {n : ℕ}

noncomputable def specAt (τ₀ : ι) (y : ι × Fin n × Fin n → K) :
    Formalism.L2.DIV.Pol K ι n →ₐ[K] MvPolynomial (Fin n × Fin n) K :=
  MvPolynomial.aeval fun v => if v.1 = τ₀ then MvPolynomial.X v.2 else MvPolynomial.C (y v)

theorem eval_specAt (τ₀ : ι) (y : ι × Fin n × Fin n → K) (z : Fin n × Fin n → K) (w : Formalism.L2.DIV.Pol K ι n) :
    MvPolynomial.eval z (specAt τ₀ y w) =
      MvPolynomial.eval (fun v => if v.1 = τ₀ then z v.2 else y v) w := by
  have h : (MvPolynomial.eval z).comp (specAt τ₀ y).toRingHom =
      MvPolynomial.eval (fun v : ι × Fin n × Fin n => if v.1 = τ₀ then z v.2 else y v) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [specAt]
    · intro v
      by_cases hv : v.1 = τ₀ <;> simp [specAt, hv]
  exact congrArg (fun f : Formalism.L2.DIV.Pol K ι n →+* K => f w) h

theorem exists_specAt_ne [Infinite K] (τ₀ : ι) (w : Formalism.L2.DIV.Pol K ι n) (hw : w ≠ 0) :
    ∃ y, specAt τ₀ y w ≠ 0 := by
  by_contra h
  push_neg at h
  apply hw
  apply MvPolynomial.funext
  intro z
  have := congrArg (MvPolynomial.eval (fun v : Fin n × Fin n => z (τ₀, v))) (h z)
  rw [eval_specAt, map_zero] at this
  rw [map_zero, ← this]
  congr 2
  funext v
  split_ifs with hv
  · obtain ⟨a, b⟩ := v; simp only at hv; subst hv; rfl
  · rfl

theorem specAt_blockEmb (τ₀ : ι) (y : ι × Fin n × Fin n → K) (τ : ι) (F : MvPolynomial (Fin n × Fin n) K) :
    specAt τ₀ y (Formalism.GradedWeylDivisibility.blockEmb K τ F) =
      if τ = τ₀ then F else MvPolynomial.C (MvPolynomial.eval (fun v => y (τ, v)) F) := by
  unfold specAt Formalism.GradedWeylDivisibility.blockEmb
  rw [MvPolynomial.aeval_rename]
  split_ifs with h
  · subst h
    simp only [Function.comp_def, if_true]
    exact MvPolynomial.aeval_X_left_apply F
  · simp only [Function.comp_def, h, if_false]
    have hh : (MvPolynomial.aeval (R := K) fun x : Fin n × Fin n => (MvPolynomial.C (y (τ, x)) : MvPolynomial (Fin n × Fin n) K)).toRingHom =
        MvPolynomial.C.comp (MvPolynomial.eval fun v => y (τ, v)) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro v; simp
    exact congrArg (fun f : MvPolynomial (Fin n × Fin n) K →+* MvPolynomial (Fin n × Fin n) K => f F) hh

end GlobalTheory.SpecFactor

namespace GlobalTheory.SpecFactor

open MvPolynomial

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem specAt_mem (lam : ι → DomWeight n) (τ₀ : ι) (y : ι × Fin n × Fin n → K) (P : Formalism.L2.DIV.Pol K ι n)
    (hP : P ∈ Formalism.L2.DIV.VV K lam) : specAt τ₀ y P ∈ nablaSq K n (lam τ₀) := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    rw [map_prod]
    simp only [specAt_blockEmb]
    rw [Fintype.prod_eq_mul_prod_compl τ₀, if_pos rfl, mul_comm]
    have : ∏ i ∈ ({τ₀}ᶜ : Finset ι), (if i = τ₀ then F i else
        MvPolynomial.C (MvPolynomial.eval (fun v => y (i, v)) (F i))) =
        MvPolynomial.C (∏ i ∈ ({τ₀}ᶜ : Finset ι), MvPolynomial.eval (fun v => y (i, v)) (F i)) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [if_neg (by simpa using hi)]
    rw [this, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (hF τ₀)
  | zero => simp
  | add x z _ _ hx hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hz
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem specAt_blockAct (τ₀ : ι) (y : ι × Fin n × Fin n → K) (M : Matrix (Fin n) (Fin n) K)
    (P : Formalism.L2.DIV.Pol K ι n) :
    specAt τ₀ y (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then M else 1) P) =
      Formalism.GradedWeylDivisibility.rowAct K M (specAt τ₀ y P) := by
  have h : (specAt τ₀ y).comp (Formalism.GradedWeylDivisibility.blockAct K (n := n) (fun τ => if τ = τ₀ then M else 1)) =
      (Formalism.GradedWeylDivisibility.rowAct K M).comp (specAt τ₀ y) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, a, b⟩
    by_cases hτ : τ = τ₀
    · subst hτ
      simp [specAt, Formalism.GradedWeylDivisibility.blockAct, Formalism.GradedWeylDivisibility.rowAct]
    · set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.blockAct, specAt, MvPolynomial.aeval_X, hτ, if_false, map_sum, map_mul,
        MvPolynomial.aeval_C, Matrix.one_apply]
      rw [Finset.sum_eq_single a]
      · simp [hτ]
      · intro c _ hc; simp [Ne.symm hc]
      · simp
  exact congrArg (fun f : Formalism.L2.DIV.Pol K ι n →ₐ[K] MvPolynomial (Fin n × Fin n) K => f P) h

end GlobalTheory.SpecFactor

theorem GlobalTheory.specialise_factor : ∀ (K : Type) [Field K] [Infinite K] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (lam : ι → DomWeight n) (τ₀ : ι) (w : Formalism.L2.DIV.Pol K ι n), w ∈ Formalism.L2.DIV.VV K lam → w ≠ 0 →
    ∃ φ : Formalism.L2.DIV.Pol K ι n →ₗ[K] MvPolynomial (Fin n × Fin n) K, φ w ≠ 0 ∧
      (∀ P ∈ Formalism.L2.DIV.VV K lam, φ P ∈ nablaSq K n (lam τ₀)) ∧
      ∀ (M : Matrix (Fin n) (Fin n) K) (P : Formalism.L2.DIV.Pol K ι n),
        φ (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then M else 1) P) = Formalism.GradedWeylDivisibility.rowAct K M (φ P) := by
  intro K _ _ n ι _ _ lam τ₀ w _ hw
  obtain ⟨y, hy⟩ := GlobalTheory.SpecFactor.exists_specAt_ne τ₀ w hw
  exact ⟨(GlobalTheory.SpecFactor.specAt τ₀ y).toLinearMap, hy,
    fun P hP => GlobalTheory.SpecFactor.specAt_mem lam τ₀ y P hP,
    fun M P => GlobalTheory.SpecFactor.specAt_blockAct τ₀ y M P⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpecialisationCoefficientSpaceToDualWeylStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specialisation_coefficientSpace_to_dualWeyl : ∀ (K : Type) [Field K] [Infinite K] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (lam : ι → DomWeight n) (τ₀ : ι) (w : Formalism.L2.DIV.Pol K ι n), w ∈ Formalism.L2.DIV.VV K lam → w ≠ 0 →
    ∃ φ : Formalism.L2.DIV.Pol K ι n →ₗ[K] MvPolynomial (Fin n × Fin n) K, φ w ≠ 0 ∧
      (∀ P ∈ Formalism.L2.DIV.VV K lam, φ P ∈ nablaSq K n (lam τ₀)) ∧
      ∀ (M : Matrix (Fin n) (Fin n) K) (P : Formalism.L2.DIV.Pol K ι n),
        φ (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then M else 1) P) = Formalism.GradedWeylDivisibility.rowAct K M (φ P) := by
  first | exact @GlobalTheory.specialise_factor | exact GlobalTheory.specialise_factor | (intros; apply GlobalTheory.specialise_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualCoefficientSpaceUnique
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.AlgWtF.DDHw

theorem dd_hw_unique : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → ∀ (τ₀ : ι) (mu : Fin n → ℤ),
      NX.HWAtF (IsCMField.complexConj L : L →+* L) (GlobalTheory.AlgWtF.wtRepF emb lam).dual (emb τ₀) mu → mu = (lam τ₀).w := by
  intro L _ _ _ n ι _ K _ _ emb lam hd τ₀ mu h
  classical
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  obtain ⟨w, hwV, hw0, hB⟩ := GlobalTheory.T.highestWeight_doubleDual_upperTriangular_eigenvector L n ι K emb lam hd τ₀ mu h
  obtain ⟨φ, hφ0, hφV, hφA⟩ := GlobalTheory.T.exists_specialisation_coefficientSpace_to_dualWeyl K n ι lam τ₀ w hwV hw0
  refine GlobalTheory.T.nablaSq_upperEigenvector_weight_eq_highest K n (lam τ₀) mu (φ w) (hφV w hwV) hφ0 fun B hBt => ?_
  have hc0 : detPow K n B (lam τ₀).detShift ≠ 0 := by
    rw [detPow]; exact Units.ne_zero _
  rw [sqAct, ← hφA, hB B hBt, map_smul, smul_smul, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

end GlobalTheory.AlgWtF.DDHw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualCoefficientSpaceUniqueStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highestWeight_doubleDual_coefficientSpace_unique : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → ∀ (τ₀ : ι) (mu : Fin n → ℤ),
      NX.HWAtF (IsCMField.complexConj L : L →+* L) (GlobalTheory.AlgWtF.wtRepF emb lam).dual (emb τ₀) mu → mu = (lam τ₀).w := by
  first | exact @GlobalTheory.AlgWtF.DDHw.dd_hw_unique | exact GlobalTheory.AlgWtF.DDHw.dd_hw_unique | (intros; apply GlobalTheory.AlgWtF.DDHw.dd_hw_unique <;> assumption)
end
