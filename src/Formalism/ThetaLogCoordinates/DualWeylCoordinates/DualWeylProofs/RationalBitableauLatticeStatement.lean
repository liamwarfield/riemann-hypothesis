module

public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.TransposeVariables
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.ABridge
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQHW

@[expose] public section

section -- merged from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QnEvalMap
section -- merged from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.CoeffTransposeVariables
open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

theorem qn_coeff_X_pderiv {σ : Type*} (i : σ) (f : MvPolynomial σ ℚ) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (X i * pderiv i f) m = (m i : ℚ) * AddMonoidAlgebra.coeff f m := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial s c =>
    have h : X i * pderiv i (monomial s c) = (s i : ℚ) • monomial s c := by
      rw [pderiv_monomial]
      by_cases hs : s i = 0
      · simp [hs]
      · have h1 : Finsupp.single i 1 + (s - Finsupp.single i 1) = s :=
          add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hs))
        rw [X, monomial_mul, h1, smul_monomial, one_mul, smul_eq_mul, mul_comm]
    rw [h, coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with hsm
    · rw [hsm]
    · simp
  | add p q hp hq => rw [map_add (f := _), mul_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

def qn_wt {n : ℕ} (m : Fin n × Fin n →₀ ℕ) : Fin n → ℤ := fun a => ((∑ l : Fin n, m (l, a) : ℕ) : ℤ)

theorem qn_coeff_E (n : ℕ) (a : Fin n) (f : MvPolynomial (Fin n × Fin n) ℚ) (m : Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (glOps ℚ n (rowLetters n) Set.univ a a f) m = (qn_wt m a : ℚ) * AddMonoidAlgebra.coeff f m := by
  rw [qn_E_eq, qn_D_apply, coeff_sum]
  simp only [qn_coeff_X_pderiv]
  rw [← Finset.sum_mul]
  simp [qn_wt]

theorem qn_mem_weightSp (n : ℕ) (w : Fin n → ℤ) (z : MvPolynomial (Fin n × Fin n) ℚ) :
    z ∈ weightSp (glOps ℚ n (rowLetters n) Set.univ) w ↔
      ∀ a, glOps ℚ n (rowLetters n) Set.univ a a z = (w a : ℚ) • z := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]

theorem qn_monomial_mem (n : ℕ) (m : Fin n × Fin n →₀ ℕ) (c : ℚ) :
    monomial m c ∈ weightSp (glOps ℚ n (rowLetters n) Set.univ) (qn_wt m) := by
  classical
  rw [qn_mem_weightSp]
  intro a
  ext m'
  rw [qn_coeff_E, coeff_smul, coeff_monomial, smul_eq_mul]
  split_ifs with h
  · rw [h]
  · simp

theorem qn_weightSp_coeff (n : ℕ) (w : Fin n → ℤ) (z : MvPolynomial (Fin n × Fin n) ℚ)
    (hz : z ∈ weightSp (glOps ℚ n (rowLetters n) Set.univ) w) (m : Fin n × Fin n →₀ ℕ) (hm : qn_wt m ≠ w) :
    AddMonoidAlgebra.coeff z m = 0 := by
  rw [qn_mem_weightSp] at hz
  by_contra hne
  apply hm
  funext a
  have h := congrArg (AddMonoidAlgebra.coeff · m) (hz a)
  rw [qn_coeff_E, coeff_smul, smul_eq_mul] at h
  have := mul_right_cancel₀ hne h
  exact_mod_cast this

theorem qn_otherWts_coeff (n : ℕ) (lam : Fin n → ℤ) (z : MvPolynomial (Fin n × Fin n) ℚ)
    (hz : z ∈ otherWts (glOps ℚ n (rowLetters n) Set.univ) lam) (m : Fin n × Fin n →₀ ℕ) (hm : qn_wt m = lam) :
    AddMonoidAlgebra.coeff z m = 0 := by
  have hle : otherWts (glOps ℚ n (rowLetters n) Set.univ) lam ≤ LinearMap.ker (lcoeff ℚ m) := by
    unfold otherWts
    refine iSup₂_le fun mu hmu => ?_
    intro y hy
    rw [LinearMap.mem_ker, lcoeff_apply]
    exact qn_weightSp_coeff n mu y hy m (by rw [hm]; exact fun h => hmu h.symm)
  have := hle hz
  rwa [LinearMap.mem_ker, lcoeff_apply] at this

theorem qn_mem_otherWts (n : ℕ) (lam : Fin n → ℤ) (g : MvPolynomial (Fin n × Fin n) ℚ)
    (hg : ∀ m ∈ g.support, qn_wt m ≠ lam) : g ∈ otherWts (glOps ℚ n (rowLetters n) Set.univ) lam := by
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  unfold otherWts
  exact Submodule.mem_iSup_of_mem (qn_wt m) (Submodule.mem_iSup_of_mem (hg m hm) (qn_monomial_mem n m _))

theorem qn_swap_apply {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a l : Fin n) :
    (Finsupp.mapDomain Prod.swap m) (a, l) = m (l, a) :=
  Finsupp.mapDomain_apply_of_injective Prod.swap_injective m (l, a)

theorem coeff_transposeVariables (n : ℕ) (g : MvPolynomial (Fin n × Fin n) ℚ) (m : Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (transposeVariables ℚ n g) (Finsupp.mapDomain Prod.swap m) = AddMonoidAlgebra.coeff g m :=
  coeff_rename_mapDomain Prod.swap Prod.swap_injective g m

theorem qn_mem_otherWts' (n : ℕ) (ν : Fin n → ℕ) (g : MvPolynomial (Fin n × Fin n) ℚ)
    (hg : weightedHomogeneousComponent (rowW n n) ν (transposeVariables ℚ n g) = 0) :
    g ∈ otherWts (glOps ℚ n (rowLetters n) Set.univ) (fun a => (ν a : ℤ)) := by
  classical
  refine qn_mem_otherWts n _ g fun m hm hwt => ?_
  have h1 := congrArg (AddMonoidAlgebra.coeff · (Finsupp.mapDomain Prod.swap m)) hg
  have hw : Finsupp.weight (rowW n n) (Finsupp.mapDomain Prod.swap m) = ν := by
    funext a
    rw [lehw_weight_rowW, rowDeg]
    simp only [qn_swap_apply]
    have := congrFun hwt a
    simp only [qn_wt] at this
    exact_mod_cast this
  rw [coeff_weightedHomogeneousComponent, if_pos hw, coeff_transposeVariables] at h1
  exact (mem_support_iff.mp hm) (by simpa using h1)

theorem qn_otherWts_coeff' (n : ℕ) (ν : Fin n → ℕ) (z : MvPolynomial (Fin n × Fin n) ℚ)
    (hz : z ∈ otherWts (glOps ℚ n (rowLetters n) Set.univ) (fun a => (ν a : ℤ))) :
    AddMonoidAlgebra.coeff (transposeVariables ℚ n z) (lhwline_mnu (le_refl n) ν) = 0 := by
  classical
  have h := coeff_transposeVariables n (transposeVariables ℚ n z) (lhwline_mnu (le_refl n) ν)
  rw [transposeVariables_involutive] at h
  rw [← h]
  refine qn_otherWts_coeff n _ z hz _ ?_
  funext a
  simp only [qn_wt, qn_swap_apply, lhwline_mnu_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    have : a.val ≠ b.val := fun h => hb (Fin.ext h).symm
    simp [this]
  · simp

theorem qn_rowNu (n : ℕ) (ν : Fin n → ℕ) : rowNu (r := n) ν = ν := by
  funext a
  simp [rowNu]

theorem qn_eval_eq_coeff (n : ℕ) (ν : Fin n → ℕ) (F : MvPolynomial (Fin n × Fin n) ℚ)
    (hF : IsWeightedHomogeneous (colW n n) F ν) :
    eval (idFrame ℚ n n) F = AddMonoidAlgebra.coeff F (lhwline_mnu (le_refl n) ν) := by
  have hD : ∀ (a : Fin n) (j : Fin n), a.val ≠ j.val → idFrame ℚ n n (a, j) = 0 := by
    intro a j h
    simp [idFrame, h]
  rw [lhwline_diag (le_refl n) ν F hF (idFrame ℚ n n) hD]
  have : ∏ v, idFrame ℚ n n v ^ (lhwline_mnu (le_refl n) ν) v = 1 := by
    refine Finset.prod_eq_one fun v _ => ?_
    obtain ⟨a, j⟩ := v
    rw [lhwline_mnu_apply]
    by_cases h : a.val = j.val
    · simp [idFrame, h]
    · simp [h]
  rw [this, mul_one]

theorem qn_colHom (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ) (F : MvPolynomial (Fin n × Fin n) R)
    (hF : F ∈ dualWeyl R n n ν) : IsWeightedHomogeneous (colW n n) F ν :=
  (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hF).1

theorem qn_comp (n : ℕ) (ν : Fin n → ℕ) (hν : Antitone ν) (F : MvPolynomial (Fin n × Fin n) ℚ)
    (hF : F ∈ dualWeyl ℚ n n ν) :
    weightedHomogeneousComponent (rowW n n) ν F = eval (idFrame ℚ n n) F • hw ℚ (le_refl n) ν := by
  classical
  set G := weightedHomogeneousComponent (rowW n n) ν F with hGdef
  have hG : G ∈ dualWeyl ℚ n n ν := dualWeylRowGraded ℚ n n ν _ F hF
  have hGh : IsWeightedHomogeneous (rowW n n) G (rowNu (r := n) ν) := by
    rw [qn_rowNu]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  obtain ⟨c, hc⟩ := hwLine ℚ n n (le_refl n) ν hν G hG
    (fun a b hab k hk => lehw_kill (le_refl n) ν hν G hG hGh a b hab k hk)
  have hHW := hwRowWeight ℚ n n (le_refl n) ν hν
  rw [qn_rowNu] at hHW
  have hH1 : AddMonoidAlgebra.coeff (hw ℚ (le_refl n) ν) (lhwline_mnu (le_refl n) ν) = 1 := by
    rw [← qn_eval_eq_coeff n ν _ (qn_colHom ℚ n ν _ (hwMem ℚ n n (le_refl n) ν hν))]
    exact lehw_eval_idFrame_hw (le_refl n) ν
  have hwt : Finsupp.weight (rowW n n) (lhwline_mnu (le_refl n) ν) = ν :=
    hHW (by rw [hH1]; exact one_ne_zero)
  have h1 : AddMonoidAlgebra.coeff F (lhwline_mnu (le_refl n) ν) = c := by
    have e : AddMonoidAlgebra.coeff F (lhwline_mnu (le_refl n) ν) = AddMonoidAlgebra.coeff G (lhwline_mnu (le_refl n) ν) := by
      rw [hGdef, coeff_weightedHomogeneousComponent, if_pos hwt]
    rw [e, hc, coeff_smul, hH1, smul_eq_mul, mul_one]
  rw [qn_eval_eq_coeff n ν F (qn_colHom ℚ n ν F hF), h1, hc]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section -- merged from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QnFactRowDivDiag
open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

theorem qn_rowDiv_zero (n : ℕ) (a b : Fin n) (F : MvPolynomial (Fin n × Fin n) ℚ) :
    rowDiv ℚ a b 0 F = F := by
  unfold rowDiv
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have h : (Polynomial.evalRingHom (0 : MvPolynomial (Fin n × Fin n) ℚ)).comp
      (rowGen ℚ (r := n) (n := n) a b).toRingHom =
      RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowGen]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rowGen, aeval_X,
        Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C, RingHom.id_apply]
      split_ifs <;> simp
  have h2 := RingHom.congr_fun h F
  simpa using h2

theorem qn_natsmul (n : ℕ) (k : ℕ) (p : MvPolynomial (Fin n × Fin n) ℚ) :
    p * ((k : MvPolynomial (Fin n × Fin n) ℚ) + 1) = ((k + 1 : ℕ) : ℚ) • p := by
  rw [MvPolynomial.smul_eq_C_mul, mul_comm]
  congr 1
  simp

theorem qn_rowDiv_succ (n : ℕ) (a b : Fin n) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    ((k + 1 : ℕ) : ℚ) • rowDiv ℚ a b (k + 1) (transposeVariables ℚ n f) = rowDiv ℚ a b k (transposeVariables ℚ n (qn_D n a b f)) := by
  unfold rowDiv
  rw [← qn_deriv_rowGen n a b hab f, Polynomial.coeff_derivative, qn_natsmul]

theorem qn_rowDiv_succ_diag (n : ℕ) (a : Fin n) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    ((k + 1 : ℕ) : ℚ) • rowDiv ℚ a a (k + 1) (transposeVariables ℚ n f) =
      rowDiv ℚ a a k (transposeVariables ℚ n (qn_D n a a f - (k : ℚ) • f)) := by
  unfold rowDiv
  rw [map_sub, map_smul, map_sub, map_smul, ← qn_deriv_rowGen_diag n a f, Polynomial.coeff_sub,
    Polynomial.coeff_smul, add_mul, one_mul, Polynomial.coeff_add]
  cases k with
  | zero =>
    rw [Polynomial.coeff_X_mul_zero, Polynomial.coeff_derivative]
    simp
  | succ m =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, Polynomial.coeff_derivative]
    simp only [MvPolynomial.smul_eq_C_mul, map_natCast, Nat.cast_add, Nat.cast_one, map_add (f := _), map_one]
    ring

theorem qn_fact_rowDiv (n : ℕ) (a b : Fin n) (hab : a ≠ b) (k : ℕ) :
    ∀ f : MvPolynomial (Fin n × Fin n) ℚ,
    (k.factorial : ℚ) • rowDiv ℚ a b k (transposeVariables ℚ n f) =
      transposeVariables ℚ n (((glOps ℚ n (rowLetters n) Set.univ a b) ^ k) f) := by
  induction k with
  | zero =>
    intro f
    simp [qn_rowDiv_zero]
  | succ k ih =>
    intro f
    rw [Nat.factorial_succ, Nat.cast_mul, mul_comm ((k + 1 : ℕ) : ℚ), mul_smul, qn_rowDiv_succ n a b hab k f,
      ih, pow_succ, Module.End.mul_apply, qn_E_eq]

theorem qn_T_divPowE (n : ℕ) (a b : Fin n) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    transposeVariables ℚ n (divPowE (glOps ℚ n (rowLetters n) Set.univ) a b k f) = rowDiv ℚ a b k (transposeVariables ℚ n f) := by
  have hk : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  rw [divPowE, LinearMap.smul_apply, map_smul, ← qn_fact_rowDiv n a b hab k f, smul_smul,
    inv_mul_cancel₀ hk, one_smul]

theorem qn_fact_rowDiv_diag (n : ℕ) (a : Fin n) (k : ℕ) :
    ∀ f : MvPolynomial (Fin n × Fin n) ℚ,
    (k.factorial : ℚ) • rowDiv ℚ a a k (transposeVariables ℚ n f) =
      transposeVariables ℚ n ((((List.range k).map fun j : ℕ => glOps ℚ n (rowLetters n) Set.univ a a -
        (j : ℚ) • (1 : Module.End ℚ (MvPolynomial (Fin n × Fin n) ℚ))).prod) f) := by
  induction k with
  | zero =>
    intro f
    simp [qn_rowDiv_zero]
  | succ k ih =>
    intro f
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
      Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, qn_E_eq, ← ih,
      Nat.factorial_succ, Nat.cast_mul, mul_comm ((k + 1 : ℕ) : ℚ), mul_smul, qn_rowDiv_succ_diag]

theorem qn_T_binomE (n : ℕ) (a : Fin n) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    transposeVariables ℚ n (binomE (glOps ℚ n (rowLetters n) Set.univ) a k f) = rowDiv ℚ a a k (transposeVariables ℚ n f) := by
  have hk : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  rw [binomE, LinearMap.smul_apply, map_smul, ← qn_fact_rowDiv_diag n a k f, smul_smul,
    inv_mul_cancel₀ hk, one_smul]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section -- merged from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QnInterlacedLowerTri
open MvPolynomial

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility
open scoped MonomialOrder

theorem qn_interlaced_lowerTri {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (h : Interlaced m) : LowerTri m := by
  have key : ∀ k : ℕ, ∀ s : Fin n, s.val = k → ∀ a : Fin r, a.val < k → m (a, s) = 0 := by
    intro k
    induction k with
    | zero =>
      intro s _ a ha
      omega
    | succ k ih =>
      intro s hs a ha
      have hl : k < n := by
        have := s.isLt
        omega
      have hI := h ⟨k, hl⟩ s (by simp [hs]) a
      have hR : (∑ b : Fin r with b < a, m (b, (⟨k, hl⟩ : Fin n))) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        have hba : b.val < a.val := hb
        exact ih ⟨k, hl⟩ rfl b (by omega)
      rw [hR, add_zero, Nat.le_zero, Finset.sum_eq_zero_iff] at hI
      exact hI a (by simp)
  intro a s has
  exact key s.val s rfl a has

theorem qn_lowerTriIntegral : LowerTriIntegral := by
  classical
  intro r n ν
  haveI := (colLex r n).wellFoundedLT_syn
  obtain ⟨b, hbB, hbdeg⟩ := sSBasis ℤ r n ν
  have hBmem : ∀ i, intQ r n (b i) ∈ dualWeyl ℚ r n ν := by
    intro i
    rw [← span_map_weightBasis_eq_dualWeyl (K := ℚ) hbB]
    apply Submodule.subset_span
    exact ⟨i, by rw [algebraMap_int_eq]; rfl⟩
  suffices H : ∀ s : (colLex r n).syn, ∀ Q : MvPolynomial (Fin r × Fin n) ℚ,
      (colLex r n).toSyn ((colLex r n).degree Q) = s → Q ∈ dualWeyl ℚ r n ν →
      (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, AddMonoidAlgebra.coeff Q e = z) →
      ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, Q = intQ r n Q' by
    intro Q hQ hint
    exact H _ Q rfl hQ hint
  intro s
  induction s using WellFoundedLT.induction with
  | ind s ih =>
    intro Q hs hQ hint
    by_cases hQ0 : Q = 0
    · exact ⟨0, by rw [hQ0, map_zero]⟩
    set m := (colLex r n).degree Q with hm
    have hInt : Interlaced m := leadInterlaced ℚ r n ν Q hQ hQ0
    have hLT : LowerTri m := qn_interlaced_lowerTri m hInt
    have hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t := by
      have hhom : IsWeightedHomogeneous (colW r n) Q ν :=
        (mem_weightedHomogeneousSubmodule _ _ _ _).1 (Submodule.mem_inf.1 hQ).1
      have hw : Finsupp.weight (colW r n) m = ν :=
        hhom ((colLex r n).leadingCoeff_ne_zero_iff.2 hQ0)
      intro t
      rw [← hw]
      simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_prod_type, colW, Pi.single_apply]
    let mi : ssIdx r n ν := ⟨m, hInt, hcol⟩
    obtain ⟨hbd, hblc, -⟩ := hbdeg mi
    set B := intQ r n (b mi) with hB
    have hBmap : B = map (Int.castRingHom ℚ) (b mi) := rfl
    have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
    have hBsupp : B.support = (b mi).support := by
      rw [hBmap]
      exact support_map_of_injective _ hinj
    have hBdeg : (colLex r n).degree B = m := by
      have h1 : (colLex r n).degree (b mi) = m := hbd
      rw [← h1]
      unfold MonomialOrder.degree
      rw [hBsupp]
    have hBlc : (colLex r n).leadingCoeff B = 1 := by
      unfold MonomialOrder.leadingCoeff
      rw [hBdeg, hBmap, coeff_map]
      have h1 : (colLex r n).degree (b mi) = m := hbd
      have h2 : (b mi).coeff ((colLex r n).degree (b mi)) = 1 := hblc
      rw [h1] at h2
      rw [h2, map_one]
    obtain ⟨z, hz⟩ := hint m hLT
    have hlcQ : (colLex r n).leadingCoeff Q = (z : ℚ) := hz
    set Q1 := Q - (colLex r n).leadingCoeff Q • B with hQ1
    have hQ1mem : Q1 ∈ dualWeyl ℚ r n ν :=
      Submodule.sub_mem _ hQ (Submodule.smul_mem _ _ (hBmem mi))
    have hQ1int : ∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z' : ℤ, AddMonoidAlgebra.coeff Q1 e = z' := by
      intro e he
      obtain ⟨w, hw⟩ := hint e he
      refine ⟨w - z * (b mi).coeff e, ?_⟩
      rw [hQ1, coeff_sub, coeff_smul, hw, hlcQ, hBmap, coeff_map]
      push_cast
      simp [smul_eq_mul]
    have hfinal : ∀ Q1' : MvPolynomial (Fin r × Fin n) ℤ, Q1 = intQ r n Q1' →
        ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, Q = intQ r n Q' := by
      intro Q1' h
      refine ⟨Q1' + z • b mi, ?_⟩
      rw [map_add (f := _), map_zsmul, ← h, ← hB, hQ1, hlcQ, Int.cast_smul_eq_zsmul]
      abel
    by_cases hQ10 : Q1 = 0
    · exact hfinal 0 (by rw [hQ10, map_zero])
    · have hlt := lcassem_sub_lt (colLex r n) (hBdeg.trans hm) hBlc hQ10
      obtain ⟨Q1', h⟩ := ih _ (by rw [← hs]; exact hlt) Q1 rfl hQ1mem hQ1int
      exact hfinal Q1' h

end Formalism.InvariantFactorPaths.ColumnFamilies
end

section -- merged from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QnPtEmpty
open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

def qn_pt (n : ℕ) (D : Finset (Fin n × Fin n)) : Fin n × Fin n → MvPolynomial (Fin n × Fin n) ℚ :=
  open Classical in
  fun v => (if v.1 = v.2 then 1 else 0) + (if v ∈ D then X v else 0)

def qn_IntS (n : ℕ) : Subring (MvPolynomial (Fin n × Fin n) ℚ) :=
  (MvPolynomial.map (σ := Fin n × Fin n) (Int.castRingHom ℚ)).range

theorem qn_pt_step (n : ℕ) (D : Finset (Fin n × Fin n)) (a s : Fin n) (hw : (a, s) ∉ D)
    (hs : ∀ c, (s, c) ∉ D) (F : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (qn_pt n (insert (a, s) D)) F =
      Polynomial.eval₂ (aeval (qn_pt n D)).toRingHom (X (a, s)) (rowGen ℚ s a F) := by
  classical
  have h : (aeval (qn_pt n (insert (a, s) D))).toRingHom =
      (Polynomial.eval₂RingHom (aeval (qn_pt n D)).toRingHom (X (a, s))).comp (rowGen ℚ s a).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowGen, algebraMap_eq, Polynomial.algebraMap_apply]
    · rintro ⟨b, c⟩
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        rowGen, aeval_X, Polynomial.coe_eval₂RingHom]
      by_cases hb : b = a
      · subst hb
        by_cases hc : c = s
        · subst hc
          simp [qn_pt, hw, hs]
        · have h1 : (b, c) ≠ (b, s) := by simp [hc]
          have h2 : s ≠ c := fun h => hc h.symm
          simp [qn_pt, hs, h1, h2, hc]
      · have h1 : (b, c) ≠ (a, s) := by simp [hb]
        simp [qn_pt, h1, hb]
  exact congrArg (fun φ => φ F) h

theorem qn_pt_empty (n : ℕ) (F : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (qn_pt n ∅) F = C (eval (idFrame ℚ n n) F) := by
  have h : (aeval (qn_pt n ∅)).toRingHom = (C : ℚ →+* MvPolynomial (Fin n × Fin n) ℚ).comp (eval (idFrame ℚ n n)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [algebraMap_eq]
    · rintro ⟨b, c⟩
      by_cases hbc : b = c
      · subst hbc; simp [qn_pt, idFrame]
      · have : b.val ≠ c.val := fun h => hbc (Fin.ext h)
        simp [qn_pt, idFrame, hbc, this]
  exact congrArg (fun φ => φ F) h

theorem qn_X_mem (n : ℕ) (v : Fin n × Fin n) : (X v : MvPolynomial (Fin n × Fin n) ℚ) ∈ qn_IntS n :=
  ⟨X v, by simp⟩

theorem qn_int_pt (n : ℕ) (W : Set (MvPolynomial (Fin n × Fin n) ℚ))
    (hW : ∀ F ∈ W, ∀ (a b : Fin n) (k : ℕ), a ≠ b → rowDiv ℚ a b k F ∈ W)
    (hev : ∀ F ∈ W, ∃ z : ℤ, eval (idFrame ℚ n n) F = z) (D : Finset (Fin n × Fin n)) :
    (∀ x ∈ D, x.2 < x.1) → ∀ F ∈ W, aeval (qn_pt n D) F ∈ qn_IntS n := by
  classical
  induction D using Finset.induction_on_min_value (fun x : Fin n × Fin n => x.1) with
  | empty =>
    intro _ F hF
    obtain ⟨z, hz⟩ := hev F hF
    rw [qn_pt_empty, hz]
    exact ⟨C z, by simp⟩
  | insert w D hw hmin ih =>
    obtain ⟨a, s⟩ := w
    intro hD F hF
    have hsa : s < a := hD (a, s) (Finset.mem_insert_self _ _)
    have hs : ∀ c, (s, c) ∉ D := by
      intro c hc
      have := hmin (s, c) hc
      exact absurd hsa (not_lt.mpr this)
    have ih' := ih (fun x hx => hD x (Finset.mem_insert_of_mem hx))
    rw [qn_pt_step n D a s hw hs, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Subring.sum_mem _ fun k _ => ?_
    exact Subring.mul_mem _ (ih' _ (hW F hF s a k (ne_of_lt hsa))) (Subring.pow_mem _ (qn_X_mem n _) _)

def qn_low (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter fun v => v.2 < v.1

def qn_off {n : ℕ} (m : Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ := m.filter fun v => v.2 < v.1

theorem qn_prod_pt (n : ℕ) (m : Fin n × Fin n →₀ ℕ) :
    (∏ i, qn_pt n (qn_low n) i ^ m i) = open Classical in if LowerTri m then monomial (qn_off m) 1 else 0 := by
  classical
  split_ifs with h
  · rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
    refine Finset.prod_congr rfl fun i _ => ?_
    obtain ⟨a, c⟩ := i
    rcases lt_trichotomy a c with hac | hac | hac
    · have h0 : m (a, c) = 0 := h a c hac
      have h1 : ¬ c < a := not_lt.mpr hac.le
      simp [h0, qn_off, Finsupp.filter_apply, h1]
    · subst hac
      simp [qn_pt, qn_low, qn_off, Finsupp.filter_apply]
    · have h1 : a ≠ c := ne_of_gt hac
      simp [qn_pt, qn_low, qn_off, Finsupp.filter_apply, hac, h1]
  · unfold LowerTri at h
    push Not at h
    obtain ⟨a, c, hac, hne⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ (a, c)) ?_
    have hac' : a < c := hac
    have h1 : ¬ c < a := not_lt.mpr hac'.le
    have h2 : a ≠ c := ne_of_lt hac'
    simp [qn_pt, qn_low, h1, h2, hne]

theorem qn_off_inj {n : ℕ} (ν : Fin n → ℕ) (m e : Fin n × Fin n →₀ ℕ) (hm : LowerTri m) (he : LowerTri e)
    (hmc : ∀ t : Fin n, ∑ a : Fin n, m (a, t) = ν t) (hec : ∀ t : Fin n, ∑ a : Fin n, e (a, t) = ν t)
    (h : qn_off m = qn_off e) : m = e := by
  classical
  have hoff : ∀ a c : Fin n, a ≠ c → m (a, c) = e (a, c) := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h1 | h1
    · rw [hm a c h1, he a c h1]
    · have := DFunLike.congr_fun h (a, c)
      simpa [qn_off, Finsupp.filter_apply, h1] using this
  ext ⟨a, c⟩
  by_cases hac : a = c
  · subst hac
    have h1 := hmc a
    have h2 := hec a
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at h1 h2
    have h3 : ∑ x ∈ Finset.univ.erase a, m (x, a) = ∑ x ∈ Finset.univ.erase a, e (x, a) :=
      Finset.sum_congr rfl fun x hx => hoff x a (Finset.ne_of_mem_erase hx)
    omega
  · exact hoff a c hac

theorem qn_coeff_pt (n : ℕ) (ν : Fin n → ℕ) (F : MvPolynomial (Fin n × Fin n) ℚ)
    (hF : IsWeightedHomogeneous (colW n n) F ν) (e : Fin n × Fin n →₀ ℕ) (he : LowerTri e)
    (hec : ∀ t : Fin n, ∑ a : Fin n, e (a, t) = ν t) :
    AddMonoidAlgebra.coeff (aeval (qn_pt n (qn_low n)) F) (qn_off e) = AddMonoidAlgebra.coeff F e := by
  classical
  rw [aeval_def, eval₂_eq', coeff_sum]
  simp only [algebraMap_eq, coeff_C_mul, qn_prod_pt]
  rw [Finset.sum_eq_single e]
  · rw [if_pos he, coeff_monomial, if_pos rfl, mul_one]
  · intro m hm hne
    split_ifs with hl
    · rw [coeff_monomial, if_neg, mul_zero]
      intro hoff
      apply hne
      refine qn_off_inj ν m e hl he ?_ hec hoff
      intro t
      rw [← lhwline_weight_col, hF (mem_support_iff.mp hm)]
    · simp
  · intro h
    rw [notMem_support_iff.mp h, zero_mul]

theorem qn_tri (n : ℕ) (ν : Fin n → ℕ) (W : Set (MvPolynomial (Fin n × Fin n) ℚ))
    (hW : ∀ F ∈ W, ∀ (a b : Fin n) (k : ℕ), a ≠ b → rowDiv ℚ a b k F ∈ W)
    (hev : ∀ F ∈ W, ∃ z : ℤ, eval (idFrame ℚ n n) F = z)
    (hcol : ∀ F ∈ W, IsWeightedHomogeneous (colW n n) F ν) :
    ∀ F ∈ W, ∀ e : Fin n × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, AddMonoidAlgebra.coeff F e = z := by
  classical
  intro F hF e he
  by_cases hec : ∀ t : Fin n, ∑ a : Fin n, e (a, t) = ν t
  · rw [← qn_coeff_pt n ν F (hcol F hF) e he hec]
    obtain ⟨G, hG⟩ := qn_int_pt n W hW hev (qn_low n) (fun x hx => (Finset.mem_filter.mp hx).2) F hF
    refine ⟨AddMonoidAlgebra.coeff G (qn_off e), ?_⟩
    rw [← hG, coeff_map]
    rfl
  · refine ⟨0, ?_⟩
    rw [Int.cast_zero]
    by_contra hne
    apply hec
    intro t
    rw [← lhwline_weight_col, hcol F hF hne]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

def qn_InZ (n : ℕ) (ν : Fin n → ℕ) (x : MvPolynomial (Fin n × Fin n) ℚ) : Prop :=
  ∃ Y ∈ dualWeyl ℤ n n ν, transposeVariables ℚ n x = map (Int.castRingHom ℚ) Y

theorem qn_eval_map (n : ℕ) (Y : MvPolynomial (Fin n × Fin n) ℤ) :
    eval (idFrame ℚ n n) (map (Int.castRingHom ℚ) Y) = ((eval (idFrame ℤ n n) Y : ℤ) : ℚ) := by
  have h : (eval (idFrame ℚ n n)).comp (map (Int.castRingHom ℚ)) =
      (Int.castRingHom ℚ).comp (eval (idFrame ℤ n n)) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro v
      simp only [RingHom.coe_comp, Function.comp_apply, map_X, eval_X, idFrame]
      split_ifs <;> simp
  exact congrArg (fun φ => φ Y) h

theorem qn_InZ_UZ (n : ℕ) (ν : Fin n → ℕ) (u : Module.End ℚ (MvPolynomial (Fin n × Fin n) ℚ))
    (hu : u ∈ UZmon (glOps ℚ n (rowLetters n) Set.univ)) :
    ∀ x, qn_InZ n ν x → qn_InZ n ν (u x) := by
  unfold UZmon at hu
  induction hu using Submonoid.closure_induction with
  | mem g hg =>
    rintro x ⟨Y, hY, hx⟩
    rcases hg with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · exact ⟨rowDiv ℤ a b k Y, rowDivStable ℤ n n ν a b k Y hY, by
        rw [qn_T_divPowE n a b hab, hx, lclosedeq_rowDiv_map]⟩
    · exact ⟨rowDiv ℤ a a k Y, rowDivStable ℤ n n ν a a k Y hY, by
        rw [qn_T_binomE, hx, lclosedeq_rowDiv_map]⟩
  | one => intro x hx; exact hx
  | mul g h _ _ ihg ihh => intro x hx; exact ihg _ (ihh x hx)

theorem qn_InZ_span (n : ℕ) (ν : Fin n → ℕ) {ι : Type} (P : ι → MvPolynomial (Fin n × Fin n) ℤ)
    (h1 : ∀ i, transposeVariables ℤ n (P i) ∈ dualWeyl ℤ n n ν) (x : MvPolynomial (Fin n × Fin n) ℚ)
    (hx : x ∈ Submodule.span ℤ (Set.range fun i => map (Int.castRingHom ℚ) (P i))) : qn_InZ n ν x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨_, h1 i, qn_T_map n (P i)⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨Y1, h1, e1⟩ := hx
    obtain ⟨Y2, h2, e2⟩ := hy
    exact ⟨Y1 + Y2, Submodule.add_mem _ h1 h2, by rw [map_add (f := _), map_add (f := _), e1, e2]⟩
  | smul c x _ hx =>
    obtain ⟨Y1, h1, e1⟩ := hx
    exact ⟨c • Y1, Submodule.smul_mem _ _ h1, by rw [map_zsmul, map_zsmul, e1]⟩

theorem qn_main (n : ℕ) (ν : Fin n → ℕ) (hν : Antitone ν) {ι : Type}
    (P : ι → MvPolynomial (Fin n × Fin n) ℤ) (i0 : ι)
    (h1 : ∀ i, transposeVariables ℤ n (P i) ∈ dualWeyl ℤ n n ν)
    (h2 : dualWeyl ℤ n n ν ≤ Submodule.span ℤ (Set.range fun i => transposeVariables ℤ n (P i)))
    (h3 : eval (idFrame ℤ n n) (transposeVariables ℤ n (P i0)) = 1) :
    (Submodule.span ℤ (Set.range fun i => map (Int.castRingHom ℚ) (P i)) :
        Set (MvPolynomial (Fin n × Fin n) ℚ)) =
      {x | x ∈ Submodule.span ℚ (Set.range fun i => map (Int.castRingHom ℚ) (P i)) ∧
        x ∈ Nabla (O := ℤ) (glOps ℚ n (rowLetters n) Set.univ) (fun a => (ν a : ℤ))
          (map (Int.castRingHom ℚ) (P i0))} := by
  classical
  set v := map (Int.castRingHom ℚ) (P i0) with hv
  have hTv : transposeVariables ℚ n v = map (Int.castRingHom ℚ) (transposeVariables ℤ n (P i0)) := qn_T_map n (P i0)
  have hTvmem : transposeVariables ℚ n v ∈ dualWeyl ℚ n n ν := by
    rw [hTv]; exact dualWeylMap ℤ ℚ _ n n ν _ (h1 i0)
  have hTvev : eval (idFrame ℚ n n) (transposeVariables ℚ n v) = 1 := by
    rw [hTv, qn_eval_map, h3, Int.cast_one]
  ext x
  simp only [SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · intro hx
    refine ⟨Submodule.span_le_restrictScalars ℤ ℚ _ hx, ?_⟩
    intro u hu
    obtain ⟨Y, hY, hy⟩ := qn_InZ_UZ n ν u hu x (qn_InZ_span n ν P h1 x hx)
    refine ⟨eval (idFrame ℤ n n) Y, ?_⟩
    apply qn_mem_otherWts'
    have hYQ : transposeVariables ℚ n (u x) ∈ dualWeyl ℚ n n ν := by
      rw [hy]; exact dualWeylMap ℤ ℚ _ n n ν _ hY
    rw [map_sub, map_smul, map_sub, map_smul, qn_comp n ν hν _ hYQ, qn_comp n ν hν _ hTvmem, hTvev, hy,
      qn_eval_map, one_smul, eq_intCast, sub_self]
  · rintro ⟨hxQ, hxN⟩
    have hxD : transposeVariables ℚ n x ∈ dualWeyl ℚ n n ν := by
      have hle : Submodule.span ℚ (Set.range fun i => map (Int.castRingHom ℚ) (P i)) ≤
          (dualWeyl ℚ n n ν).comap (transposeVariables ℚ n).toLinearMap := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        show transposeVariables ℚ n (map (Int.castRingHom ℚ) (P i)) ∈ dualWeyl ℚ n n ν
        rw [qn_T_map]
        exact dualWeylMap ℤ ℚ _ n n ν _ (h1 i)
      exact hle hxQ
    set W : Set (MvPolynomial (Fin n × Fin n) ℚ) :=
      {F | ∃ y, F = transposeVariables ℚ n y ∧ transposeVariables ℚ n y ∈ dualWeyl ℚ n n ν ∧
        y ∈ Nabla (O := ℤ) (glOps ℚ n (rowLetters n) Set.univ) (fun a => (ν a : ℤ)) v} with hWdef
    have hW : ∀ F ∈ W, ∀ (a b : Fin n) (k : ℕ), a ≠ b → rowDiv ℚ a b k F ∈ W := by
      rintro F ⟨y, rfl, hyD, hyN⟩ a b k hab
      refine ⟨divPowE (glOps ℚ n (rowLetters n) Set.univ) a b k y, (qn_T_divPowE n a b hab k y).symm, ?_, ?_⟩
      · rw [qn_T_divPowE n a b hab]
        exact rowDivStable ℚ n n ν a b k _ hyD
      · intro u hu
        have hg : divPowE (glOps ℚ n (rowLetters n) Set.univ) a b k ∈
            UZmon (glOps ℚ n (rowLetters n) Set.univ) :=
          Submonoid.subset_closure (Or.inl ⟨a, b, k, hab, rfl⟩)
        exact hyN (u * divPowE (glOps ℚ n (rowLetters n) Set.univ) a b k) (Submonoid.mul_mem _ hu hg)
    have hev : ∀ F ∈ W, ∃ z : ℤ, eval (idFrame ℚ n n) F = z := by
      rintro F ⟨y, rfl, hyD, hyN⟩
      obtain ⟨c, hc⟩ := hyN 1 (Submonoid.one_mem _)
      refine ⟨c, ?_⟩
      have h := qn_otherWts_coeff' n ν _ hc
      rw [Module.End.one_apply, map_sub, map_smul, coeff_sub, coeff_smul,
        ← qn_eval_eq_coeff n ν _ (qn_colHom ℚ n ν _ hyD), ← qn_eval_eq_coeff n ν _ (qn_colHom ℚ n ν _ hTvmem),
        hTvev, smul_eq_mul, mul_one, eq_intCast, sub_eq_zero] at h
      exact h
    have hcol : ∀ F ∈ W, IsWeightedHomogeneous (colW n n) F ν := by
      rintro F ⟨y, rfl, hyD, _⟩
      exact qn_colHom ℚ n ν _ hyD
    have htri := qn_tri n ν W hW hev hcol (transposeVariables ℚ n x) ⟨x, rfl, hxD, hxN⟩
    obtain ⟨Q', hQ'⟩ := qn_lowerTriIntegral n n ν (transposeVariables ℚ n x) hxD htri
    have hQ'' : transposeVariables ℚ n x = map (Int.castRingHom ℚ) Q' := hQ'
    have hQmem : Q' ∈ dualWeyl ℤ n n ν := (dualWeylIntRat n n ν Q').mpr (hQ'' ▸ hxD)
    have hQs := h2 hQmem
    set φ : MvPolynomial (Fin n × Fin n) ℤ →ₗ[ℤ] MvPolynomial (Fin n × Fin n) ℚ :=
      (intQ n n).comp (transposeVariables ℤ n).toLinearMap with hφ
    have hφx : φ Q' = x := by
      show map (Int.castRingHom ℚ) (transposeVariables ℤ n Q') = x
      rw [← qn_T_map, ← hQ'', transposeVariables_involutive]
    have hx := Submodule.mem_map_of_mem (f := φ) hQs
    rw [Submodule.map_span, hφx] at hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    show _ = map (Int.castRingHom ℚ) (transposeVariables ℤ n (transposeVariables ℤ n (P i)))
    rw [transposeVariables_involutive]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section -- merged from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.EvalIdBracketCanonical
open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

def qn_delta (n : ℕ) : MvPolynomial (Fin n × Fin n) ℤ := lpMinor ℤ n (le_refl n) (le_refl n)

theorem qn_T_det (n : ℕ) : transposeVariables ℤ n (genMat ℤ n).det = qn_delta n := by
  unfold qn_delta lpMinor transposeVariables
  rw [AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext p q
  simp [genMat]

theorem qn_full (n : ℕ) (J : Fin n → Fin n) :
    ∃ ε : ℤ, initMinor ℤ J (le_refl n) = ε • qn_delta n := by
  classical
  set M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℤ) :=
    Matrix.of fun p q : Fin n => X (Fin.castLE (le_refl n) p, Fin.castLE (le_refl n) q) with hM
  have h1 : initMinor ℤ J (le_refl n) = (M.submatrix J id).det := rfl
  by_cases hJ : Function.Injective J
  · have hb : Function.Bijective J := Finite.injective_iff_bijective.mp hJ
    refine ⟨((Equiv.Perm.sign (Equiv.ofBijective J hb) : ℤˣ) : ℤ), ?_⟩
    have h2 := Matrix.det_permute (Equiv.ofBijective J hb) M
    rw [h1]
    have h3 : M.submatrix J id = M.submatrix (Equiv.ofBijective J hb) id := rfl
    rw [h3, h2, zsmul_eq_mul]
    simp [qn_delta, lpMinor, hM]
  · refine ⟨0, ?_⟩
    rw [zero_smul, h1]
    unfold Function.Injective at hJ
    push Not at hJ
    obtain ⟨p, p', hpp, hne⟩ := hJ
    exact Matrix.det_zero_of_row_eq hne (by funext q; simp [Matrix.submatrix, hpp])

theorem qn_full' (n s : ℕ) (hs : s ≤ n) (J : Fin s → Fin n) (h : s = n) :
    ∃ ε : ℤ, initMinor ℤ J hs = ε • qn_delta n := by
  subst h
  exact qn_full s J

theorem qn_divide (n : ℕ) [NeZero n] (ν' : Fin n → ℕ) :
    dualWeyl ℤ n n (fun t => ν' t + 1) ≤
      (dualWeyl ℤ n n ν').map (LinearMap.mulLeft ℤ (qn_delta n)) := by
  classical
  rw [standardMonomialSpanDomain ℤ n n _, Submodule.span_le]
  rintro f ⟨K, sz, hsz, I, hshape, rfl⟩
  have h1 : 0 < shapeDeg sz (lastIdx n) := by rw [hshape]; exact Nat.succ_pos _
  unfold shapeDeg at h1
  obtain ⟨k0, hk0⟩ := Finset.card_pos.mp h1
  have hk0' : (lastIdx n).val < sz k0 := (Finset.mem_filter.mp hk0).2
  have hsz0 : sz k0 = n := by
    have := hsz k0
    have h2 : (lastIdx n).val = n - 1 := rfl
    omega
  obtain ⟨ε, hε⟩ := qn_full' n (sz k0) (hsz k0) (I k0) hsz0
  have hrest : (∏ k ∈ Finset.univ.erase k0, initMinor ℤ (I k) (hsz k)) ∈ dualWeyl ℤ n n ν' := by
    refine dualWeyl_of_eq (dualWeyl_prod (Finset.univ.erase k0) (fun k => initW n (sz k))
      (fun k => initMinor ℤ (I k) (hsz k)) (fun k _ => initMinor_mem (I k) (hsz k))) ?_
    have h3 := sum_initW_eq_shapeDeg (n := n) sz
    rw [hshape, ← Finset.add_sum_erase _ _ (Finset.mem_univ k0)] at h3
    funext t
    have h4 := congrFun h3 t
    have h5 : initW n (sz k0) t = 1 := by
      unfold initW
      rw [hsz0, if_pos t.isLt]
    rw [Pi.add_apply, h5] at h4
    omega
  refine ⟨ε • ∏ k ∈ Finset.univ.erase k0, initMinor ℤ (I k) (hsz k), Submodule.smul_mem _ _ hrest, ?_⟩
  rw [LinearMap.mulLeft_apply]
  unfold bideterminant
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k0), hε, mul_smul_comm, smul_mul_assoc]

theorem qn_divideN (n : ℕ) [NeZero n] (ν0 : Fin n → ℕ) {ι : Type} (Q : ι → MvPolynomial (Fin n × Fin n) ℤ)
    (h : dualWeyl ℤ n n ν0 ≤ Submodule.span ℤ (Set.range Q)) (N : ℕ) :
    dualWeyl ℤ n n (fun t => ν0 t + N) ≤ Submodule.span ℤ (Set.range fun i => qn_delta n ^ N * Q i) := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    intro f hf
    obtain ⟨g, hg, rfl⟩ := qn_divide n (fun t => ν0 t + N) hf
    have hx := Submodule.mem_map_of_mem (f := LinearMap.mulLeft ℤ (qn_delta n)) (ih hg)
    rw [Submodule.map_span] at hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by simp only [LinearMap.mulLeft_apply]; ring⟩

def qn_nu {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Fin n → ℕ :=
  fun t => (mu t + ((-(mu (lastIdx n))).toNat : ℤ)).toNat

theorem qn_le_last {n : ℕ} [NeZero n] (a : Fin n) : a ≤ lastIdx n := by
  have h2 : (lastIdx n).val = n - 1 := rfl
  have := a.isLt
  exact Fin.le_def.mpr (by omega)

theorem qn_nu_eq {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    qn_nu mu = fun t => qa_nu mu t + (mu (lastIdx n)).toNat := by
  funext t
  have h := hmu (qn_le_last t)
  unfold qn_nu qa_nu
  omega

theorem qn_nu_cast {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    (fun a => ((qn_nu mu a : ℕ) : ℤ)) = fun a => mu a + ((-(mu (lastIdx n))).toNat : ℤ) := by
  funext t
  have h := hmu (qn_le_last t)
  unfold qn_nu
  omega

theorem qn_nu_anti {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) : Antitone (qn_nu mu) := by
  intro a b hab
  have h := hmu hab
  unfold qn_nu
  omega

theorem qn_T_brkPol {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    transposeVariables ℤ n (brkPol mu I) = qn_delta n ^ (mu (lastIdx n)).toNat * qa_P ℤ I := by
  rw [qa_brkPol_eq, map_mul, map_pow, qn_T_det]
  congr 1
  exact transposeVariables_involutive ℤ n (qa_P ℤ I)

theorem bracket_mem_dualWeyl {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    transposeVariables ℤ n (brkPol mu I) ∈ dualWeyl ℤ n n (qn_nu mu) := by
  rw [qn_T_brkPol]
  have h1 : qn_delta n ∈ dualWeyl ℤ n n (initW n n) :=
    initMinor_mem (R := ℤ) (fun p : Fin n => Fin.castLE (le_refl n) p) (le_refl n)
  refine dualWeyl_of_eq (dualWeyl_mul (dualWeyl_pow h1 (mu (lastIdx n)).toNat) (tableauBideterminant_mem_dualWeyl ℤ hmu I)) ?_
  rw [qn_nu_eq hmu]
  funext t
  simp [initW]
  ring

theorem dualWeyl_le_span_bracket {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    dualWeyl ℤ n n (qn_nu mu) ≤ Submodule.span ℤ (Set.range fun I : TIdx mu => transposeVariables ℤ n (brkPol mu I)) := by
  rw [qn_nu_eq hmu]
  simp only [qn_T_brkPol]
  exact qn_divideN n (qa_nu mu) (fun I : TIdx mu => qa_P ℤ I) (le_of_eq (dualWeyl_eq_span_tableauBideterminant ℤ hmu)) _

theorem eval_id_bracket_canonical {n : ℕ} [NeZero n] (mu : Fin n → ℤ) :
    eval (idFrame ℤ n n) (transposeVariables ℤ n (brkPol mu (canT mu))) = 1 := by
  rw [qn_T_brkPol, map_mul, map_pow]
  have h1 : eval (idFrame ℤ n n) (qn_delta n) = 1 := eval_idPoint_lpMinor ℤ n (le_refl n) (le_refl n)
  rw [h1, one_pow, one_mul]
  unfold qa_P
  rw [map_prod]
  refine Finset.prod_eq_one fun c _ => ?_
  have h2 : initMinor ℤ (qa_row (canT mu) c) (colH_le mu c) =
      lpMinor ℤ (colH mu c) (colH_le mu c) (colH_le mu c) := by
    unfold initMinor lpMinor
    congr 1
    ext p q
    simp [qa_row, qa_can_emb]
  rw [h2]
  exact eval_idPoint_lpMinor ℤ (colH mu c) (colH_le mu c) (colH_le mu c)

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

open MvPolynomial

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem highest_weight_corollary_two : RationalBitableauLatticeStatement := by
  intro n _ mu hmu
  have h := qn_main n (qn_nu mu) (qn_nu_anti hmu) (fun I : TIdx mu => brkPol mu I) (canT mu)
    (fun I => bracket_mem_dualWeyl hmu I) (dualWeyl_le_span_bracket hmu) (eval_id_bracket_canonical mu)
  rw [qn_nu_cast hmu] at h
  exact h

end Formalism.InvariantFactorPaths.ColumnFamilies
