module

public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingAdmissibleFacts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalPol
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CapelliLink

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame

abbrev Letter (O : Type) [CommRing O] (N : ℕ) (ι : Type) : Type :=
  (ι → GL (Fin N) O) ⊕ (ι × (Fin N → ℕ))

def evalE (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) :
    FreeAlgebra O (Letter O N ι) →ₐ[O] Module.End O (NablaT O N lam) :=
  FreeAlgebra.lift O (Sum.elim (grp O N lam) fun p => P p.1 p.2)

def evalPol (O : Type) [CommRing O] (N : ℕ) :
    FreeAlgebra O (Fin N × Fin N) →ₐ[O] Module.End O (MvPolynomial (Fin N × Fin N) O) :=
  FreeAlgebra.lift O fun p => Formalism.GradedWeylDivisibility.rowDivL O p.1 p.2 1

end GlobalTheory.CapelliLink

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationOperatorFormulaGroupAndProjectors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationOperatorFormulaGroupAndProjectors
set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.PolarFormula

theorem weight_rowW_le_colSum {N : ℕ} (d : Fin N × Fin N →₀ ℕ) (c : Fin N) :
    Finsupp.weight (rowW N N) d c ≤ ∑ s, Finsupp.weight (colW N N) d s := by
  classical
  have h2 : ∑ c', Finsupp.weight (rowW N N) d c' = ∑ s, Finsupp.weight (colW N N) d s := by
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add (f := _), Pi.add_apply, Finset.sum_add_distrib, hf, hg]
    | single v k => simp [Finsupp.weight_apply, rowW, colW, Finsupp.sum_single_index, Pi.single_apply]
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)).trans h2.le

theorem sum_rowComp {O : Type} [CommRing O] {N : ℕ} (ν : Fin N → ℕ) (M : ℕ) (hM : ∑ s, ν s ≤ M)
    (f : MvPolynomial (Fin N × Fin N) O) (hf : IsWeightedHomogeneous (colW N N) f ν) :
    ∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
      weightedHomogeneousComponent (rowW N N) w f = f := by
  classical
  ext d
  rw [coeff_sum]
  simp_rw [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    rw [Fintype.mem_piFinset]
    intro c
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have e := hf (Ne.symm hne)
    calc _ ≤ _ := weight_rowW_le_colSum d c
      _ = ∑ s, ν s := by rw [e]
      _ ≤ M := hM

theorem comp_of_rowZ {O : Type} [CommRing O] {N : ℕ} (H : Fin N → ℤ) (h : MvPolynomial (Fin N × Fin N) O)
    (hh : IsWeightedHomogeneous (GlobalTheory.LvT.KerLat.rowZ N N) h H) (w : Fin N → ℕ) :
    weightedHomogeneousComponent (rowW N N) w h = if (fun c => (w c : ℤ)) = H then h else 0 := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  by_cases hd : AddMonoidAlgebra.coeff h d = 0
  · split_ifs <;> simp [hd]
  · have e := hh hd
    have key : Finsupp.weight (rowW N N) d = w ↔ (fun c => (w c : ℤ)) = H := by
      rw [← e]
      constructor
      · intro hw; funext c; rw [GlobalTheory.LvT.KerLat.weight_rowZ, hw]
      · intro hw; funext c
        have := congrFun hw c
        rw [GlobalTheory.LvT.KerLat.weight_rowZ] at this
        exact_mod_cast this.symm
    by_cases hw : (fun c => (w c : ℤ)) = H
    · rw [if_pos (key.mpr hw), if_pos hw]
    · rw [if_neg (mt key.mp hw), if_neg hw, AddMonoidAlgebra.coeff_zero] <;> rfl

theorem eq_zero_of_rowZ_neg {O : Type} [CommRing O] {N : ℕ} (H : Fin N → ℤ) (h : MvPolynomial (Fin N × Fin N) O)
    (hh : IsWeightedHomogeneous (GlobalTheory.LvT.KerLat.rowZ N N) h H) (c : Fin N) (hc : H c < 0) : h = 0 := by
  ext d
  simp only [AddMonoidAlgebra.coeff_zero, Pi.zero_apply]
  by_contra hd
  have e := congrFun (hh hd) c
  rw [GlobalTheory.LvT.KerLat.weight_rowZ] at e
  omega

theorem rowZ_of_rowW {O : Type} [CommRing O] {N : ℕ} (w : Fin N → ℕ) (h : MvPolynomial (Fin N × Fin N) O)
    (hh : IsWeightedHomogeneous (rowW N N) h w) :
    IsWeightedHomogeneous (GlobalTheory.LvT.KerLat.rowZ N N) h (fun c => (w c : ℤ)) := by
  intro d hd
  funext c
  rw [GlobalTheory.LvT.KerLat.weight_rowZ, hh hd]

theorem rowAct_transvection {O : Type} [CommRing O] {N : ℕ} (a b : Fin N) (f : MvPolynomial (Fin N × Fin N) O) :
    rowAct O (n := N) (Matrix.transvection b a (1 : O)) f = (rowGen O a b f).eval 1 := by
  have e : (rowAct O (n := N) (Matrix.transvection b a (1 : O))).toRingHom =
      (Polynomial.evalRingHom (1 : MvPolynomial (Fin N × Fin N) O)).comp (rowGen O a b).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [rowAct, rowGen]
    · intro v
      simp [rowAct, rowGen, Matrix.transvection, Matrix.one_apply, Matrix.single_apply, Finset.sum_add_distrib,
        add_mul, ite_and]
      by_cases hv : v.1 = b
      · simp [hv]
      · simp [hv, Ne.symm hv]
  exact congrArg (fun φ : MvPolynomial (Fin N × Fin N) O →+* MvPolynomial (Fin N × Fin N) O => φ f) e

end GlobalTheory.PolarFormula

namespace GlobalTheory.PolarFormula

theorem comp_rowAct_transvection {O : Type} [CommRing O] {N : ℕ} (a b : Fin N) (hab : a ≠ b) (w : Fin N → ℕ)
    (h : MvPolynomial (Fin N × Fin N) O) (hh : IsWeightedHomogeneous (rowW N N) h w) :
    weightedHomogeneousComponent (rowW N N) (w + Pi.single a 1 - Pi.single b 1)
      (rowAct O (n := N) (Matrix.transvection b a (1 : O)) h) = rowDiv O a b 1 h := by
  classical
  have hZ := rowZ_of_rowW w h hh
  rw [rowAct_transvection, Polynomial.eval_eq_sum_range' (n := (rowGen O a b h).natDegree + 2) (by omega)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [one_pow, mul_one, map_sum]
  have hk : ∀ k ∈ Finset.range ((rowGen O a b h).natDegree + 2),
      weightedHomogeneousComponent (rowW N N) (w + Pi.single a 1 - Pi.single b 1) ((rowGen O a b h).coeff k) =
        if k = 1 then rowDiv O a b 1 h else 0 := by
    intro k _
    have hs := GlobalTheory.LvT.KerLat.rowDiv_shift O _ a b k h hZ
    change weightedHomogeneousComponent _ _ (rowDiv O a b k h) = _
    rw [comp_of_rowZ _ _ hs]
    by_cases hk1 : k = 1
    · subst hk1
      by_cases hb : 1 ≤ w b
      · rw [if_pos, if_pos rfl]
        funext c
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply]
        by_cases hca : c = a
        · subst hca; simp [hab]
        · by_cases hcb : c = b
          · subst hcb; simp [hca]; omega
          · simp [hca, hcb]
      · have h0 : rowDiv O a b 1 h = 0 :=
          eq_zero_of_rowZ_neg _ _ hs b (by simp [Pi.single_apply, Ne.symm hab]; omega)
        simp [h0]
    · rw [if_neg hk1, if_neg]
      intro he
      have := congrFun he a
      simp [Pi.single_apply, hab] at this
      omega
  rw [Finset.sum_congr rfl hk, Finset.sum_ite_eq', if_pos (by simp)]

end GlobalTheory.PolarFormula

namespace GlobalTheory.PolarFormula

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink

theorem polar_formula : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (τ : ι) (M : ℕ) (a b : Fin N), ∃ F : FreeAlgebra O (Letter O N ι), ∀ (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)), (∀ σ, Antitone (res N (lam σ))) → (∀ σ w, IsProj O N lam σ w (P σ w)) → ∑ c : Fin N, lam τ c ≤ M → ∀ x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ)), ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)), (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O a b 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧ evalE O N lam P F (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y) := by
  intro O _ N ι _ _ τ M a b
  by_cases hab : a = b
  · subst hab
    refine ⟨∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
      (w a : O) • FreeAlgebra.ι O (Sum.inr (τ, w)), ?_⟩
    intro lam P _ hP hM x
    refine ⟨⟨rowDiv O a a 1 (x τ), Formalism.GradedWeylDivisibility.rowDivStable O N N _ a a 1 _ (x τ).2⟩, rfl, ?_⟩
    have hcol := ((rowdiv_mem_dualWeyl_iff O N N _ _).mp (x τ).2).1
    let cmp : (Fin N → ℕ) → dualWeyl O N N (res N (lam τ)) := fun w =>
      ⟨weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O),
        Formalism.GradedWeylDivisibility.dualWeylRowGraded O N N _ w _ (x τ).2⟩
    have hPx : ∀ w, P τ w (PiTensorProduct.tprod O x) =
        PiTensorProduct.tprod O (Function.update x τ (cmp w)) :=
      fun w => hP τ w x (cmp w) rfl
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [evalE, map_sum, map_smul, FreeAlgebra.lift_ι_apply, Sum.elim_inr, LinearMap.sum_apply,
      Finset.sum_apply, LinearMap.smul_apply, hPx]
    have hsum : (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        (w a : O) • PiTensorProduct.tprod O (Function.update x τ (cmp w))) =
        ∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
          PiTensorProduct.tprod O (Function.update x τ ((w a : O) • cmp w)) := by
      apply Finset.sum_congr rfl
      intro w _
      exact ((PiTensorProduct.tprod O).map_update_smul x τ (w a : O) (cmp w)).symm
    rw [hsum]
    rw [← MultilinearMap.map_update_sum]
    congr 2
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    conv_rhs => rw [← sum_rowComp _ M hM _ hcol]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show rowDiv O a a 1 (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O)) =
        rowDivL O a a 1 (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O)) from rfl, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [rowDivL_apply, (GlobalTheory.ValCmp.rowDiv_rowWeight O N N w _
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)).2 a 1, Nat.choose_one_right,
      Nat.cast_smul_eq_nsmul]
  · let gt : GL (Fin N) O := ⟨Matrix.transvection b a (-1), Matrix.transvection b a 1,
        by rw [Matrix.transvection_mul_transvection_same b a (Ne.symm hab)]; simp,
        by rw [Matrix.transvection_mul_transvection_same b a (Ne.symm hab)]; simp⟩
    let g : ι → GL (Fin N) O := Pi.mulSingle τ gt
    refine ⟨∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
      FreeAlgebra.ι O (Sum.inr (τ, w + Pi.single a 1 - Pi.single b 1)) * FreeAlgebra.ι O (Sum.inl g) *
        FreeAlgebra.ι O (Sum.inr (τ, w)), ?_⟩
    intro lam P _ hP hM x
    refine ⟨⟨rowDiv O a b 1 (x τ), Formalism.GradedWeylDivisibility.rowDivStable O N N _ a b 1 _ (x τ).2⟩, rfl, ?_⟩
    have hcol := ((rowdiv_mem_dualWeyl_iff O N N _ _).mp (x τ).2).1
    let cmp : (Fin N → ℕ) → dualWeyl O N N (res N (lam τ)) → dualWeyl O N N (res N (lam τ)) := fun w v =>
      ⟨weightedHomogeneousComponent (rowW N N) w (v : MvPolynomial (Fin N × Fin N) O),
        Formalism.GradedWeylDivisibility.dualWeylRowGraded O N N _ w _ v.2⟩
    have hPz : ∀ w (z : ∀ σ, dualWeyl O N N (res N (lam σ))), P τ w (PiTensorProduct.tprod O z) =
        PiTensorProduct.tprod O (Function.update z τ (cmp w (z τ))) :=
      fun w z => hP τ w z (cmp w (z τ)) rfl
    have hg : ∀ z : ∀ σ, dualWeyl O N N (res N (lam σ)), grp O N lam g (PiTensorProduct.tprod O z) =
        PiTensorProduct.tprod O (Function.update z τ (Formalism.UG.dualWeylRep O N N _ gt (z τ))) := by
      intro z
      unfold grp
      rw [(Formalism.CohomologicalDescent.RealLocalDeltaNabla.nabla_rep_tensor_product O ι (fun _ => N) (fun _ => N) (fun σ => res N (lam σ)) g z).1]
      congr 1
      funext σ
      by_cases hσ : σ = τ
      · subst hσ; simp [g]
      · simp [g, hσ, Pi.mulSingle_eq_of_ne hσ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [evalE, map_sum, map_mul, FreeAlgebra.lift_ι_apply, Sum.elim_inr, Sum.elim_inl, LinearMap.sum_apply,
      Finset.sum_apply, Module.End.mul_apply, hPz, hg, Function.update_self, Function.update_idem]
    rw [← MultilinearMap.map_update_sum]
    congr 2
    apply Subtype.ext
    simp only [Submodule.coe_sum]
    conv_rhs => rw [← sum_rowComp _ M hM _ hcol]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show rowDiv O a b 1 (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O)) =
        rowDivL O a b 1 (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O)) from rfl, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [rowDivL_apply]
    exact comp_rowAct_transvection a b hab w _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)

end GlobalTheory.PolarFormula
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationOperatorFormulaGroupAndProjectorsStatement
open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisationOperator_formula_groupAndProjectors : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (τ : ι) (M : ℕ) (a b : Fin N), ∃ F : FreeAlgebra O (Letter O N ι), ∀ (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)), (∀ σ, Antitone (res N (lam σ))) → (∀ σ w, IsProj O N lam σ w (P σ w)) → ∑ c : Fin N, lam τ c ≤ M → ∀ x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ)), ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)), (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O a b 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧ evalE O N lam P F (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y) := by
  first | exact @GlobalTheory.PolarFormula.polar_formula | exact GlobalTheory.PolarFormula.polar_formula | (intros; apply GlobalTheory.PolarFormula.polar_formula <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliCoeffDualWeylEqCoeffProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliCoeffDualWeylEqCoeffProd
open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink

noncomputable section

namespace GlobalTheory.CapelliCoeffs

open Polynomial

def entry (O : Type) [CommRing O] (N : ℕ) (α : Equiv.Perm (Fin N)) (k : Fin N) :
    Polynomial (FreeAlgebra O (Fin N × Fin N)) :=
  C (FreeAlgebra.ι O (α k, k)) + if α k = k then X - C (((k : ℕ) : FreeAlgebra O (Fin N × Fin N))) else 0

def capPoly (O : Type) [CommRing O] (N : ℕ) : Polynomial (FreeAlgebra O (Fin N × Fin N)) :=
  ∑ α : Equiv.Perm (Fin N), (((Equiv.Perm.sign α : ℤˣ) : ℤ) : Polynomial (FreeAlgebra O (Fin N × Fin N))) *
    (List.ofFn (entry O N α)).prod

theorem ofFn_intertwine {R S M M' : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module S M'] (ψ : M →+ M') : ∀ {m : ℕ} (g : Fin m → Module.End R M)
    (g' : Fin m → Module.End S M'), (∀ k x, ψ (g k x) = g' k (ψ x)) →
    ∀ x, ψ ((List.ofFn g).prod x) = (List.ofFn g').prod (ψ x)
  | 0, g, g', _, x => by simp
  | m + 1, g, g', h, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply,
      Module.End.mul_apply, h 0, ofFn_intertwine ψ (fun k => g k.succ) (fun k => g' k.succ) (fun k => h k.succ)]

theorem capDet_intertwine {R S M M' : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module S M'] {n : ℕ} (ψ : M →+ M') (E : Fin n → Fin n → Module.End R M)
    (E' : Fin n → Fin n → Module.End S M') (h : ∀ i j x, ψ (E i j x) = E' i j (ψ x)) (u : ℤ) (x : M) :
    ψ (Formalism.BranchingDeterminantCap.capDet E u x) = Formalism.BranchingDeterminantCap.capDet E' u (ψ x) := by
  unfold Formalism.BranchingDeterminantCap.capDet Formalism.BranchingDeterminantCap.bmPi Formalism.BranchingDeterminantCap.bmM
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun α _ => ?_
  congr 1
  refine ofFn_intertwine ψ _ _ (fun k y => ?_) x
  simp only [Formalism.BranchingDeterminantCap.bmF, LinearMap.sub_apply, map_sub, h]
  split_ifs
  · simp [Module.End.intCast_apply, map_zsmul]
  · simp

theorem capDet_dualWeyl_domain (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ν : Fin N → ℕ)
    (hν : Antitone ν) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν) (u : ℤ) :
    Formalism.BranchingDeterminantCap.capDet (fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1) u f =
      ((∏ j : Fin N, (u + ((j : ℕ) : ℤ) - (ν j : ℤ)) : ℤ) : O) • f := by
  let K := FractionRing O
  let φ : O →+* K := algebraMap O K
  have hφ : Function.Injective φ := IsFractionRing.injective O K
  have hg := Formalism.GradedWeylDivisibility.dualWeylMap O K φ N N ν f hf
  have h1 := GlobalTheory.BrCompare.capDet_dualWeyl (K := K) hν u hg
  have e : (fun i j => GlobalTheory.Mem.Gelf.rowE K N N i j) = fun a b => Formalism.GradedWeylDivisibility.rowDivL K a b 1 := by
    funext a b
    exact LinearMap.ext fun P => (GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv K N N a b P).1
  rw [e] at h1
  have h2 := capDet_intertwine (MvPolynomial.map φ).toAddMonoidHom (fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1)
    (fun a b => Formalism.GradedWeylDivisibility.rowDivL K a b 1) (fun i j x => (Formalism.GradedWeylDivisibility.lclosedeq_rowDiv_map φ i j 1 x).symm) u f
  apply MvPolynomial.map_injective φ hφ
  have h3 := h2.trans h1
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at h3
  rw [h3, Int.cast_smul_eq_zsmul K, Int.cast_smul_eq_zsmul O, map_zsmul]

theorem eval_capPoly (O : Type) [CommRing O] (N : ℕ) {M : Type} [AddCommGroup M] [Module O M]
    (Φ : FreeAlgebra O (Fin N × Fin N) →ₐ[O] Module.End O M) (v : ℤ) (L : ℕ)
    (hL : (capPoly O N).natDegree < L) :
    ∑ i ∈ Finset.range L, (v ^ i) • Φ ((capPoly O N).coeff i) =
      ((-1 : ℤ) ^ N) • Formalism.BranchingDeterminantCap.capDet (fun a b => Φ (FreeAlgebra.ι O (a, b))) (-v) := by
  have hc : ∀ a : Module.End O M, Commute ((RingHom.id _) a) (v : Module.End O M) :=
    fun a => (Int.cast_commute v a).symm
  let ev := Polynomial.eval₂RingHom' (RingHom.id (Module.End O M)) (v : Module.End O M) hc
  let Ψ := Polynomial.mapRingHom (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M)
  have key : ev (Ψ (capPoly O N)) = ∑ i ∈ Finset.range L, (v ^ i) • Φ ((capPoly O N).coeff i) := by
    show eval₂ (RingHom.id _) (v : Module.End O M) (map (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M)
      (capPoly O N)) = _
    rw [eval₂_eq_sum_range' _ (lt_of_le_of_lt natDegree_map_le hL)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_map, RingHom.id_apply, ← Int.cast_pow, zsmul_eq_mul']
    rfl
  rw [← key]
  unfold capPoly Formalism.BranchingDeterminantCap.capDet Formalism.BranchingDeterminantCap.bmPi Formalism.BranchingDeterminantCap.bmM
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hev : ∀ p, ev p = p.eval₂ (RingHom.id _) (v : Module.End O M) := fun _ => rfl
  have hΨ : ∀ p, Ψ p = p.map (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M) := fun _ => rfl
  have e : (List.ofFn fun k => ev (Ψ (entry O N α k))) =
      (List.ofFn fun k => Formalism.BranchingDeterminantCap.bmF (fun a b => Φ (FreeAlgebra.ι O (a, b))) (-v) k (α k) (id k)).map Neg.neg := by
    rw [List.map_ofFn]
    congr 1
    funext k
    rw [hev, hΨ]
    simp only [Function.comp_apply, entry, Formalism.BranchingDeterminantCap.bmF, id]
    split_ifs
    · simp only [Polynomial.map_add (f := _), Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval₂_add,
        Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, RingHom.id_apply, map_natCast, RingHom.coe_coe, Polynomial.map_natCast,
        Polynomial.eval₂_natCast]
      push_cast
      abel
    · simp
  rw [show (⇑ev ∘ ⇑Ψ ∘ entry O N α) = fun k => ev (Ψ (entry O N α k)) from rfl, e, List.prod_map_neg, List.length_ofFn, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  exact (Int.cast_commute _ _).left_comm _

theorem coeff_eq_of_int (P : Type) [CommRing P] [IsDomain P] [CharZero P] (L : ℕ) (a b : ℕ → P)
    (h : ∀ v : ℤ, ∑ i ∈ Finset.range L, (v : P) ^ i * a i = ∑ i ∈ Finset.range L, (v : P) ^ i * b i) :
    ∀ i < L, a i = b i := by
  intro i hi
  let Q : Polynomial P := ∑ j ∈ Finset.range L, monomial j (a j - b j)
  have hQ : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (Int.cast_injective (α := P)))
    rintro _ ⟨v, rfl⟩
    have hv := h v
    simp only [Set.mem_setOf_eq, IsRoot, Q, eval_finsetSum, eval_monomial]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hv
    rw [← hv]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have := congrArg (fun q : Polynomial P => q.coeff i) hQ
  simp only [Q, finsetSum_coeff, coeff_monomial, coeff_zero] at this
  simp only [Finsupp.single_apply] at this
  rw [Finset.sum_eq_single i (fun j _ hj => if_neg hj) (fun h' => absurd (Finset.mem_range.2 hi) h'), if_pos rfl] at this
  exact sub_eq_zero.1 this

end GlobalTheory.CapelliCoeffs

namespace GlobalTheory.CapelliCoeffs

open Polynomial

theorem capelli_coeff_dualWeyl : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ),
    ∃ F : ℕ → FreeAlgebra O (Fin N × Fin N), ∀ ν : Fin N → ℕ, Antitone ν →
      ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν, ∀ k : ℕ,
        evalPol O N (F k) f = (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((ν a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • f := by
  intro O _ _ _ N
  refine ⟨fun k => (capPoly O N).coeff k, fun ν hν f hf k => ?_⟩
  set p : Polynomial ℤ := ∏ a : Fin N, (X + C (((ν a : ℤ) - (a : ℕ) : ℤ))) with hpdef
  set L := (capPoly O N).natDegree + N + 1 with hLdef
  have hp : p.natDegree ≤ N := by
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum fun a _ => (natDegree_X_add_C (((ν a : ℤ) - (a : ℕ) : ℤ))).le).trans ?_
    simp
  have hE : (fun a b => evalPol O N (FreeAlgebra.ι O (a, b))) = fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1 := by
    funext a b
    simp [evalPol]
  by_cases hk : k < L
  · refine coeff_eq_of_int (MvPolynomial (Fin N × Fin N) O) L
      (fun i => evalPol O N ((capPoly O N).coeff i) f) (fun i => ((p.coeff i : ℤ) : O) • f) (fun v => ?_) k hk
    have hA := eval_capPoly O N (evalPol O N) v L (by omega)
    rw [hE] at hA
    have hB := capDet_dualWeyl_domain O N ν hν f hf (-v)
    have e1 : ∑ i ∈ Finset.range L, ((v : MvPolynomial (Fin N × Fin N) O)) ^ i * evalPol O N ((capPoly O N).coeff i) f =
        (∑ i ∈ Finset.range L, (v ^ i) • evalPol O N ((capPoly O N).coeff i)) f := by
      rw [LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.smul_apply, ← Int.cast_pow, ← zsmul_eq_mul]
    have e2 : ∑ i ∈ Finset.range L, ((v : MvPolynomial (Fin N × Fin N) O)) ^ i * (((p.coeff i : ℤ) : O) • f) =
        (p.eval v) • f := by
      rw [eval_eq_sum_range' (n := L) (by omega), Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Int.cast_pow, ← zsmul_eq_mul, Int.cast_smul_eq_zsmul, smul_smul, mul_comm]
    have e3 : p.eval v = (-1 : ℤ) ^ N * ∏ j : Fin N, (-v + ((j : ℕ) : ℤ) - (ν j : ℤ)) := by
      rw [hpdef, eval_prod]
      have : ((-1 : ℤ) ^ N) = ∏ _j : Fin N, (-1 : ℤ) := by simp
      rw [this, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [eval_add, eval_X, eval_C]
      ring
    rw [e1, e2, hA, LinearMap.smul_apply, hB, e3, Int.cast_smul_eq_zsmul, smul_smul]
  · have h1 : (capPoly O N).coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have h2 : p.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    show evalPol O N ((capPoly O N).coeff k) f = _
    rw [h1, h2, map_zero]
    simp

end GlobalTheory.CapelliCoeffs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliCoeffDualWeylEqCoeffProdStatement
open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliCoeff_dualWeyl_eq_coeff_prod : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ), ∃ F : ℕ → FreeAlgebra O (Fin N × Fin N), ∀ ν : Fin N → ℕ, Antitone ν → ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν, ∀ k : ℕ, evalPol O N (F k) f = (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((ν a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • f := by
  first | exact @GlobalTheory.CapelliCoeffs.capelli_coeff_dualWeyl | exact GlobalTheory.CapelliCoeffs.capelli_coeff_dualWeyl | (intros; apply GlobalTheory.CapelliCoeffs.capelli_coeff_dualWeyl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleModuleLinkageDualWeylLatticeReduction
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CapelliLink

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD

theorem pure_step {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] (τ : ι)
    (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam))
    (Fab : Fin N × Fin N → FreeAlgebra O (Letter O N ι))
    (hF : ∀ (p : Fin N × Fin N) (x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ))),
      ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)),
        (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O p.1 p.2 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧
        evalE O N lam P (Fab p) (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y))
    (Φ : FreeAlgebra O (Fin N × Fin N)) :
    ∀ x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ)), ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)),
      (y : MvPolynomial (Fin N × Fin N) O) = evalPol O N Φ (x τ : MvPolynomial (Fin N × Fin N) O) ∧
      evalE O N lam P (FreeAlgebra.lift O Fab Φ) (PiTensorProduct.tprod O x) =
        PiTensorProduct.tprod O (Function.update x τ y) := by
  induction Φ using FreeAlgebra.induction with
  | grade0 r =>
    intro x
    refine ⟨r • x τ, ?_, ?_⟩
    · rw [AlgHom.commutes, Module.algebraMap_end_apply]; rfl
    · rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, MultilinearMap.map_update_smul,
        Function.update_eq_self]
      rfl
  | grade1 p =>
    intro x
    obtain ⟨y, hy, he⟩ := hF p x
    refine ⟨y, ?_, ?_⟩
    · rw [hy]; simp [evalPol]
    · rw [FreeAlgebra.lift_ι_apply]; exact he
  | mul Φ₁ Φ₂ h₁ h₂ =>
    intro x
    obtain ⟨y₂, hy₂, he₂⟩ := h₂ x
    obtain ⟨y₁, hy₁, he₁⟩ := h₁ (Function.update x τ y₂)
    refine ⟨y₁, ?_, ?_⟩
    · rw [hy₁, Function.update_self, hy₂, map_mul, Module.End.mul_apply]
    · rw [map_mul, map_mul, Module.End.mul_apply, he₂, he₁, Function.update_idem]
  | add Φ₁ Φ₂ h₁ h₂ =>
    intro x
    obtain ⟨y₁, hy₁, he₁⟩ := h₁ x
    obtain ⟨y₂, hy₂, he₂⟩ := h₂ x
    refine ⟨y₁ + y₂, ?_, ?_⟩
    · rw [Submodule.coe_add, hy₁, hy₂, map_add (f := _), LinearMap.add_apply]
    · rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, he₁, he₂, MultilinearMap.map_update_add]

theorem scalar_of {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] (τ : ι)
    (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam))
    (Fab : Fin N × Fin N → FreeAlgebra O (Letter O N ι))
    (hF : ∀ (p : Fin N × Fin N) (x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ))),
      ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)),
        (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O p.1 p.2 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧
        evalE O N lam P (Fab p) (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y))
    (Φ : FreeAlgebra O (Fin N × Fin N)) (c : O)
    (hΦ : ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)), evalPol O N Φ f = c • f) :
    evalE O N lam P (FreeAlgebra.lift O Fab Φ) = c • (1 : Module.End O (NablaT O N lam)) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  obtain ⟨y, hy, he⟩ := pure_step τ lam P Fab hF Φ x
  have hyc : y = c • x τ := Subtype.ext (by rw [hy, hΦ _ (x τ).2]; rfl)
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, he, hyc,
    MultilinearMap.map_update_smul, Function.update_eq_self]
  simp

def evalA (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) (hP : ∀ σ w, IsProj O N lam σ w (P σ w)) :
    FreeAlgebra O (Letter O N ι) →ₐ[O] alg O N lam :=
  FreeAlgebra.lift O (Sum.elim (grpA O N lam) fun p =>
    ⟨P p.1 p.2, Algebra.subset_adjoin (Or.inr ⟨p.1, p.2, hP p.1 p.2⟩)⟩)

theorem evalA_coe (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) (hP : ∀ σ w, IsProj O N lam σ w (P σ w))
    (Φ : FreeAlgebra O (Letter O N ι)) :
    ((evalA O N lam P hP Φ : alg O N lam) : Module.End O (NablaT O N lam)) = evalE O N lam P Φ := by
  have h : (alg O N lam).val.comp (evalA O N lam P hP) = evalE O N lam P := by
    apply FreeAlgebra.hom_ext
    funext p
    rcases p with g | p
    · simp [evalA, evalE, grpA]
    · simp [evalA, evalE]
  exact DFunLike.congr_fun h Φ

theorem compat {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] {lam mu : ι → ℕ → ℕ} {ϖ : O}
    {Gm : Type} [AddCommGroup Gm] [Module (alg O N lam) Gm]
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) (hP : ∀ σ w, IsProj O N lam σ w (P σ w))
    (Q : ι → (Fin N → ℕ) → Module.End O (NablaT O N mu)) (hQ : ∀ σ w, IsProj O N mu σ w (Q σ w))
    (ψ : Gm →+ (NablaT O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu))))
    (h2 : ∀ (c : O) z, ψ (algebraMap O (alg O N lam) c • z) = c • ψ z)
    (h3 : ∀ g z y, ψ z = Submodule.Quotient.mk y →
      ψ (grpA O N lam g • z) = Submodule.Quotient.mk (grp O N mu g y))
    (h4 : ∀ τ w (a : alg O N lam) (a' : Module.End O (NablaT O N mu)), IsProj O N lam τ w a →
      IsProj O N mu τ w a' → ∀ z y, ψ z = Submodule.Quotient.mk y → ψ (a • z) = Submodule.Quotient.mk (a' y))
    (Φ : FreeAlgebra O (Letter O N ι)) :
    ∀ z y, ψ z = Submodule.Quotient.mk y →
      ψ (evalA O N lam P hP Φ • z) = Submodule.Quotient.mk (evalE O N mu Q Φ y) := by
  induction Φ using FreeAlgebra.induction with
  | grade0 r =>
    intro z y h
    rw [AlgHom.commutes, AlgHom.commutes, h2, h, Module.algebraMap_end_apply, Submodule.Quotient.mk_smul]
  | grade1 p =>
    intro z y h
    rcases p with g | ⟨σ, w⟩
    · simp only [evalA, evalE, FreeAlgebra.lift_ι_apply, Sum.elim_inl]; exact h3 g z y h
    · simp only [evalA, evalE, FreeAlgebra.lift_ι_apply, Sum.elim_inr]
      exact h4 σ w _ (Q σ w) (hP σ w) (hQ σ w) z y h
  | mul Φ₁ Φ₂ h₁ h₂ =>
    intro z y h
    rw [map_mul, map_mul, mul_smul, Module.End.mul_apply]
    exact h₁ _ _ (h₂ z y h)
  | add Φ₁ Φ₂ h₁ h₂ =>
    intro z y h
    rw [map_add (f := _), map_add (f := _), add_smul, map_add (f := _), LinearMap.add_apply, h₁ z y h, h₂ z y h, Submodule.Quotient.mk_add]

theorem dvd_of_smul_eq_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V : Type}
    [AddCommGroup V] [Module O V] {ϖ : O} (hϖ : Irreducible ϖ) (d : O) (y : V)
    (hne : (Submodule.Quotient.mk y : V ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O V)) ≠ 0)
    (h0 : d • (Submodule.Quotient.mk y : V ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O V)) = 0) : ϖ ∣ d := by
  by_contra hd
  have hu : IsUnit d := by
    by_contra hnu
    have hm : d ∈ IsLocalRing.maximalIdeal O := hnu
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hm
    exact hd hm
  obtain ⟨u, rfl⟩ := hu
  apply hne
  have h1 := congrArg (fun q => (↑u⁻¹ : O) • q) h0
  simpa [smul_smul] using h1

theorem int_dvd_of {O : Type} [CommRing O] {ϖ : O} (hϖ : ¬ IsUnit ϖ) {l : ℕ} (hl : l.Prime)
    (hϖl : ϖ ∣ (l : O)) (d : ℤ) (hd : ϖ ∣ (d : O)) : (l : ℤ) ∣ d := by
  by_contra h
  have hc : IsCoprime (l : ℤ) d := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h' : Nat.Coprime l d.natAbs := (Nat.Prime.coprime_iff_not_dvd hl).2 (fun h' => h (Int.natCast_dvd.2 h'))
    simpa [Int.gcd] using h'
  obtain ⟨u, v, huv⟩ := hc
  have h1 : ϖ ∣ ((u * l + v * d : ℤ) : O) := by
    push_cast
    exact dvd_add (dvd_mul_of_dvd_right hϖl _) (dvd_mul_of_dvd_right hd _)
  rw [huv, Int.cast_one] at h1
  exact hϖ (isUnit_of_dvd_one h1)


set_option synthInstance.maxHeartbeats 400000 in
theorem linkage : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type)
    [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (l : ℕ) (ϖ : O), l.Prime → Irreducible ϖ →
    ϖ ∣ (l : O) → (∀ τ, Antitone (res N (lam τ))) → (∀ τ, Antitone (res N (mu τ))) →
    ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm → SubQ O N lam ϖ Gm →
    Embeds O N lam mu ϖ Gm → ∀ τ,
    (∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))) =
      ∏ a : Fin N, (Polynomial.X + Polynomial.C (((mu τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l)) := by
  intro O _ _ _ _ N ι _ _ lam mu l ϖ hl hϖ hϖl hlam hmu Gm _ _ _ hSub hEmb τ
  obtain ⟨U, π, hπ, -⟩ := hSub
  obtain ⟨ψ, hψ, h2, h3, h4⟩ := hEmb
  choose P hP _ using fun σ w => GlobalTheory.T.existsUnique_dualWeylWeightProjector O N ι lam σ w
  choose Q hQ _ using fun σ w => GlobalTheory.T.existsUnique_dualWeylWeightProjector O N ι mu σ w
  obtain ⟨M, hM⟩ : ∃ M, M = ∑ c : Fin N, lam τ c + ∑ c : Fin N, mu τ c := ⟨_, rfl⟩
  choose Fab hFab using fun p : Fin N × Fin N => GlobalTheory.T.polarisationOperator_formula_groupAndProjectors O N ι τ M p.1 p.2
  obtain ⟨Fk, hFk⟩ := GlobalTheory.T.capelliCoeff_dualWeyl_eq_coeff_prod O N
  have hscal : ∀ (nu : ι → ℕ → ℕ) (R : ι → (Fin N → ℕ) → Module.End O (NablaT O N nu)),
      (∀ σ, Antitone (res N (nu σ))) → (∀ σ w, IsProj O N nu σ w (R σ w)) → ∑ c : Fin N, nu τ c ≤ M → ∀ k,
      evalE O N nu R (FreeAlgebra.lift O Fab (Fk k)) =
        (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((nu τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • 1 := by
    intro nu R hnu hR hb k
    apply scalar_of τ nu R Fab (fun p x => hFab p nu R hnu hR hb x)
    intro f hf
    exact hFk (res N (nu τ)) (hnu τ) f hf k
  obtain ⟨z, hz⟩ := exists_ne (0 : Gm)
  obtain ⟨u, rfl⟩ := hπ z
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (ψ (π u))
  have hne : (Submodule.Quotient.mk y : NablaT O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu))) ≠ 0 := by
    rw [hy]; intro h; apply hz; apply hψ; rw [h, map_zero]
  have key : ∀ k, ϖ ∣ ((((∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k -
      (∏ a : Fin N, (Polynomial.X + Polynomial.C (((mu τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ)) : O) := by
    intro k
    apply dvd_of_smul_eq_zero hϖ _ y hne
    have hL := hscal lam P hlam hP (by omega) k
    have hMu := hscal mu Q hmu hQ (by omega) k
    have hc := compat P hP Q hQ ψ h2 h3 h4 (FreeAlgebra.lift O Fab (Fk k)) (π u) y hy.symm
    have hA : evalA O N lam P hP (FreeAlgebra.lift O Fab (Fk k)) • π u =
        algebraMap O (alg O N lam) (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • π u := by
      have hu' : evalA O N lam P hP (FreeAlgebra.lift O Fab (Fk k)) • u =
          algebraMap O (alg O N lam) (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • u := by
        apply Subtype.ext
        change ((evalA O N lam P hP _ : alg O N lam) : Module.End O _) (u : NablaT O N lam) =
          ((algebraMap O (alg O N lam) _ : alg O N lam) : Module.End O _) (u : NablaT O N lam)
        rw [evalA_coe, hL, LinearMap.smul_apply, Module.End.one_apply, Subalgebra.coe_algebraMap,
          Module.algebraMap_end_apply]
      rw [← π.map_smul, hu', π.map_smul]
    rw [hA, h2, hMu, ← hy] at hc
    rw [Int.cast_sub, sub_smul, sub_eq_zero, hc]
    simp [Submodule.Quotient.mk_smul]
  have hmap : ∀ nu : ι → ℕ → ℕ,
      (∏ a : Fin N, (Polynomial.X + Polynomial.C (((nu τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))) =
        (∏ a : Fin N, (Polynomial.X + Polynomial.C (((nu τ a : ℤ) - (a : ℕ) : ℤ)))).map (Int.castRingHom (ZMod l)) := by
    intro nu; simp [Polynomial.map_prod]
  rw [hmap lam, hmap mu]
  ext k
  rw [Polynomial.coeff_map, Polynomial.coeff_map, eq_intCast, eq_intCast, ZMod.intCast_eq_intCast_iff_dvd_sub, ← neg_sub]
  exact dvd_neg.2 (int_dvd_of hϖ.not_isUnit hl hϖl _ (key k))

end GlobalTheory.CapelliLink

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleModuleLinkageDualWeylLatticeReductionStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simpleModule_linkage_dualWeylLattice_reduction : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (l : ℕ) (ϖ : O), l.Prime → Irreducible ϖ → ϖ ∣ (l : O) → (∀ τ, Antitone (res N (lam τ))) → (∀ τ, Antitone (res N (mu τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm → SubQ O N lam ϖ Gm → Embeds O N lam mu ϖ Gm → ∀ τ, (∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))) = ∏ a : Fin N, (Polynomial.X + Polynomial.C (((mu τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l)) := by
  first | exact @GlobalTheory.CapelliLink.linkage | exact GlobalTheory.CapelliLink.linkage | (intros; apply GlobalTheory.CapelliLink.linkage <;> assumption)
end
