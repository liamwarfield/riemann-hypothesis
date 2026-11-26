module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SgSmul
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem ex_prod' {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → Wt n) :
    ∏ a ∈ s, ex (f a) = ex (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [(cfBasic n).2.1]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, (cfBasic n).1]

private theorem ex_pow' {n : ℕ} (x : Wt n) (k : ℕ) : ex x ^ k = ex (k • x) := by
  induction k with
  | zero => simp [(cfBasic n).2.1]
  | succ k ih => rw [pow_succ, ih, ← (cfBasic n).1, succ_nsmul]

private theorem sg_smul' {n : ℕ} (w : Equiv.Perm (Fin n)) (f : FR n) :
    sg w • f = (((Equiv.Perm.sign w : ℤ) : FR n)) * f := by
  rw [sg, Int.cast_smul_eq_zsmul, zsmul_eq_mul]

theorem UpperTheory.RealTr.denom :
    ∀ (n : ℕ) (t : ℝ), alt (t • rhoV n) = ex (t • rhoV n) * ∏ p ∈ posP n, (1 - ex (-(t • rt p.1 p.2))) := by
  intro n t
  classical
  set Y : Fin n → FR n := fun a => ex (-(t • (Pi.single a (1 : ℝ) : Wt n))) with hY
  set c : Wt n := fun _ => t * (((n : ℝ) - 1) / 2) with hc
  have hA : alt (t • rhoV n) = ex c * (Matrix.vandermonde Y).transpose.det := by
    rw [Matrix.det_apply, Finset.mul_sum, alt]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hprod : ex c * ∏ i, (Matrix.vandermonde Y).transpose (w i) i = ex ((t • rhoV n) ∘ ⇑w) := by
      simp only [Matrix.transpose_apply, Matrix.vandermonde_apply, hY, ex_pow', ex_prod',
        ← (cfBasic n).1]
      congr 1
      funext b
      simp [Finset.sum_apply, Pi.single_apply, rhoV]
      ring
    rw [mul_smul_comm, hprod, sg_smul', Units.smul_def, zsmul_eq_mul]
  have h1 : ∀ a b : Fin n, 1 - ex (-(t • rt a b)) = ex (t • (Pi.single b (1 : ℝ) : Wt n)) * (Y b - Y a) := by
    intro a b
    rw [mul_sub, hY]
    simp only
    rw [← (cfBasic n).1, ← (cfBasic n).1, add_neg_cancel, (cfBasic n).2.1]
    congr 2
    rw [rt, smul_sub]
    abel
  have h2 : ∏ p ∈ posP n, (1 - ex (-(t • rt p.1 p.2))) =
      ∏ i, ∏ j ∈ Finset.Ioi i, (1 - ex (-(t • rt i j))) := by
    unfold posP
    rw [Finset.prod_filter, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  have h3 : ex (t • rhoV n) * ∏ i, ∏ j ∈ Finset.Ioi i, ex (t • (Pi.single j (1 : ℝ) : Wt n)) = ex c := by
    simp only [ex_prod', ← (cfBasic n).1]
    congr 1
    funext k
    simp [Finset.sum_apply, Pi.single_apply, rhoV]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_gt_eq_Iio,
      Fin.card_Iio, nsmul_eq_mul, hc]
    ring
  rw [h2, hA, Matrix.det_transpose, Matrix.det_vandermonde, ← h3]
  simp_rw [h1, Finset.prod_mul_distrib]
  ring
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfMulSum
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private def tenPiS {J V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T : J → Submodule ℂ V) : Submodule ℂ (Ten J V) where
  carrier := {x | ∀ j, x j ∈ T j}
  add_mem' {x y} hx hy j := by simpa using (T j).add_mem (hx j) (hy j)
  zero_mem' j := by simp
  smul_mem' c x hx j := by simpa using (T j).smul_mem c (hx j)

private def tenPiE {J V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T : J → Submodule ℂ V) : tenPiS T ≃ₗ[ℂ] Π j, T j where
  toFun x j := ⟨x.1 j, x.2 j⟩
  invFun y := ⟨WithLp.toLp 2 fun j => (y j).1, fun j => (y j).2⟩
  map_add' x y := by ext j; simp
  map_smul' c x := by ext j; simp
  left_inv x := by ext j; simp
  right_inv y := by ext j; simp

private theorem cf_mul_sum {n : ℕ} {J : Type} (c₀ : FR n) (η : J → Wt n) (s : Finset J) (μ : Wt n) :
    cf (c₀ * ∑ j ∈ s, ex (η j)) μ = ∑ j ∈ s, cf c₀ (μ - η j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cf]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, mul_add, ((cfBasic n).2.2.2.1 _ _ 1 μ).1, ih,
      mul_comm c₀ (ex (η j)), (cfBasic n).2.2.2.2.1]

theorem UpperTheory.RealTr.tenCh :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ (J : Type) [Fintype J] [DecidableEq J] (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n), ClifMod c η → ∀ c₀, IsCh F S 1 c₀ → ∃ S' : Submodule ℂ (Ten J V), FiniteDimensional ℂ S' ∧ Stb (dg F c) S' ∧ IsCh (dg F c) S' 1 (c₀ * ∑ j, ex (η j)) := by
  intro n V _ _ F hF S hS hSt J _ _ c η hc c₀ hch
  refine ⟨tenPiS (fun _ => S), ?_, ?_, ?_⟩
  · exact Module.Finite.equiv (tenPiE (fun _ : J => S)).symm
  · intro a b x hx j
    have h : (dg F c a b x) j = F a b (x j) + ∑ k, spn c a b j k • x k := rfl
    rw [h]
    exact S.add_mem (hSt a b _ (hx j)) (S.sum_mem fun k _ => S.smul_mem _ (hx k))
  · intro μ
    have hdiag : ∀ (x : Ten J V) a j, (dg F c a a x) j = F a a (x j) + (η j a : ℂ) • x j := by
      intro x a j
      have h : (dg F c a a x) j = F a a (x j) + ∑ k, spn c a a j k • x k := rfl
      rw [h, hc.diag a]
      simp [Matrix.diagonal_apply]
    have hset : wsp (dg F c) μ ⊓ tenPiS (fun _ => S) = tenPiS (fun j => wsp F (μ - η j) ⊓ S) := by
      ext x
      constructor
      · rintro ⟨hw, hx⟩ j
        refine ⟨fun a => ?_, hx j⟩
        have h1 : (dg F c a a x) j = (μ a : ℂ) • x j := by
          have := congrArg (fun y : Ten J V => y j) (hw a)
          simpa using this
        rw [hdiag] at h1
        have h2 : F a a (x j) = (μ a : ℂ) • x j - (η j a : ℂ) • x j := eq_sub_of_add_eq h1
        rw [h2, ← sub_smul]
        simp
      · intro hx
        refine ⟨fun a => ?_, fun j => (hx j).2⟩
        ext j
        have h1 : F a a (x j) = (((μ - η j) a : ℝ) : ℂ) • x j := (hx j).1 a
        rw [hdiag, h1, ← add_smul]
        simp
    have hfin : ∀ j, FiniteDimensional ℂ ↥(wsp F (μ - η j) ⊓ S) :=
      fun j => Submodule.finiteDimensional_inf_right _ _
    have hfin' : FiniteDimensional ℂ ↥(tenPiS fun j => wsp F (μ - η j) ⊓ S) :=
      Module.Finite.equiv (tenPiE _).symm
    rw [hset, (trAdd (Ten J V) 1).2.2.2 _ hfin', LinearEquiv.finrank_eq (tenPiE _),
      Module.finrank_pi_fintype, cf_mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hch, (trAdd V 1).2.2.2 _ (hfin j)]
end
end
