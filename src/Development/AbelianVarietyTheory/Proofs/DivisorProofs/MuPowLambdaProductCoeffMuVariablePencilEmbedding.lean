module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeCountGenerates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffPolynomialConjugationDerivMemShapeSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisationDvrTensorSeparableFinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMPencil
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PencilOptionEquivLeftRenameSome
open MvPolynomial

namespace GlobalTheory

theorem pencil_optionEquivLeft_rename_some {τ : Type} (a : MvPolynomial τ ℂ) :
    MvPolynomial.optionEquivLeft ℂ τ (MvPolynomial.rename some a) = Polynomial.C a := by
  induction a using MvPolynomial.induction_on with
  | C r => simp [MvPolynomial.optionEquivLeft_C]
  | add p q hp hq => simp [map_add (f := _), hp, hq]
  | mul_X p x hp => simp [map_mul, hp, MvPolynomial.optionEquivLeft_X_some]

theorem pencil_natDegree_det_le_rowSum {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial R)) (d : ι → ℕ) (h : ∀ i j, (M i j).natDegree ≤ d i) :
    M.det.natDegree ≤ ∑ i, d i := by
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro g _
  calc (Equiv.Perm.sign g • ∏ i, M (g i) i).natDegree ≤ (∏ i, M (g i) i).natDegree := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign g) with sg | sg
        · rw [sg, one_smul]
        · rw [sg, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ i, (M (g i) i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i, d (g i) := Finset.sum_le_sum fun i _ => h _ _
    _ = ∑ i, d i := Equiv.sum_comp g d

theorem pencil_map_entry {τ : Type} (a b : MvPolynomial τ ℂ) :
    MvPolynomial.optionEquivLeft ℂ τ
      (MvPolynomial.X none * MvPolynomial.rename some a + MvPolynomial.rename some b) =
      Polynomial.X * Polynomial.C a + Polynomial.C b := by
  simp [map_add (f := _), map_mul, MvPolynomial.optionEquivLeft_X_none, pencil_optionEquivLeft_rename_some]

theorem pencil_det_adjugate_coeff :
    ∀ {τ : Type} {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι (MvPolynomial τ ℂ)),
      let Z : Matrix ι ι (MvPolynomial (Option τ) ℂ) := fun i j =>
        MvPolynomial.X none * MvPolynomial.rename some (A i j) + MvPolynomial.rename some (B i j);
      (∀ k, Fintype.card ι < k → (MvPolynomial.optionEquivLeft ℂ τ (Z.det)).coeff k = 0) ∧
      (MvPolynomial.optionEquivLeft ℂ τ (Z.det)).coeff (Fintype.card ι) = A.det ∧
      ∀ k i j, Fintype.card ι ≤ k →
        (MvPolynomial.optionEquivLeft ℂ τ (Z.adjugate j i)).coeff k = 0 := by
  intro τ ι _ _ A B Z
  set e : MvPolynomial (Option τ) ℂ →+* Polynomial (MvPolynomial τ ℂ) :=
    (MvPolynomial.optionEquivLeft ℂ τ).toRingEquiv.toRingHom with he
  have hZ : e.mapMatrix Z = (Polynomial.X : Polynomial (MvPolynomial τ ℂ)) • A.map Polynomial.C +
      B.map Polynomial.C := by
    refine Matrix.ext fun i j => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Z, he]
    exact pencil_map_entry (A i j) (B i j)
  have hdet : MvPolynomial.optionEquivLeft ℂ τ Z.det =
      ((Polynomial.X : Polynomial (MvPolynomial τ ℂ)) • A.map Polynomial.C + B.map Polynomial.C).det := by
    rw [← hZ, ← RingHom.map_det]; rfl
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [hdet]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((Polynomial.natDegree_det_X_add_C_le A B).trans_lt hk)
  · rw [hdet, Polynomial.coeff_det_X_add_C_card]
  · intro k i j hk
    have hadj : MvPolynomial.optionEquivLeft ℂ τ (Z.adjugate j i) =
        (((Polynomial.X : Polynomial (MvPolynomial τ ℂ)) • A.map Polynomial.C +
          B.map Polynomial.C).updateRow i (Pi.single j 1)).det := by
      have := congrFun (congrFun (RingHom.map_adjugate e Z) j) i
      rw [RingHom.mapMatrix_apply, Matrix.map_apply] at this
      change e (Z.adjugate j i) = _
      rw [this, hZ, Matrix.adjugate_apply]
    rw [hadj]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hcard : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    refine lt_of_le_of_lt (pencil_natDegree_det_le_rowSum _ (fun r => if r = i then 0 else 1) ?_) ?_
    · intro r c
      by_cases hr : r = i
      · subst hr
        simp only [Matrix.updateRow_self, if_true]
        by_cases hc : c = j
        · subst hc; simp
        · simp [Pi.single_apply, hc]
      · simp only [Matrix.updateRow_ne hr, if_neg hr, Matrix.add_apply, Matrix.smul_apply,
          Matrix.map_apply, smul_eq_mul]
        compute_degree
    · have : (∑ r, if r = i then 0 else 1 : ℕ) = Fintype.card ι - 1 := by
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one,
          Finset.filter_ne' , Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      omega

end GlobalTheory
end

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory

theorem coefM_pencil : GlobalTheory.PsCo.Cw2a.T_coefM_pencil := by
  intro n L I _ _ A0 B0
  have h := pencil_det_adjugate_coeff (τ := Fin L ⊕ EntIdx n) A0 B0
  simpa only [coefM, muM, inM, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    Polynomial.lcoeff_apply, AlgEquiv.toLinearMap_apply, AlgHom.coe_coe] using h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaMonomialCoeffDualNumberProductEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAllOnesProdOneAddMul
open MvPolynomial

namespace GlobalTheory

theorem coeff_allOnes_prod_one_add_mul {σ : Type} {L : ℕ} (m : Fin L → MvPolynomial σ ℂ)
    (a : MvPolynomial σ ℂ) :
    AddMonoidAlgebra.coeff (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ ((∏ i, (1 + MvPolynomial.X (Sum.inl i) *
        MvPolynomial.rename Sum.inr (m i))) * MvPolynomial.rename Sum.inr a))
      (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ)) = (∏ i, m i) * a := by
  have hr : ∀ q : MvPolynomial σ ℂ, sumAlgEquiv ℂ (Fin L) σ (rename Sum.inr q) = C q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C r => simp [sumAlgEquiv_C_inl]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p c hp => rw [map_mul, map_mul, hp, rename_X, sumAlgEquiv_X_inr, map_mul]
  have hx : ∀ i : Fin L, sumAlgEquiv ℂ (Fin L) σ (X (Sum.inl i)) = X i := fun i =>
    sumAlgEquiv_X_inl ℂ (Fin L) σ i
  have cmC : ∀ {τ : Type} (n : τ →₀ ℕ) (p : MvPolynomial τ (MvPolynomial σ ℂ)) (c : MvPolynomial σ ℂ),
      AddMonoidAlgebra.coeff (p * C c) n = AddMonoidAlgebra.coeff p n * c := by
    intro τ n p c; rw [mul_comm, coeff_C_mul, mul_comm]
  set e : Fin L →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ) with he
  have hmono : ∀ t : Finset (Fin L),
      AddMonoidAlgebra.coeff (∏ i ∈ t, (X i * C (m i) : MvPolynomial (Fin L) (MvPolynomial σ ℂ))) e =
        if t = Finset.univ then ∏ i, m i else 0 := by
    intro t
    rw [Finset.prod_mul_distrib, ← map_prod, cmC]
    have hX : (∏ i ∈ t, (X i : MvPolynomial (Fin L) (MvPolynomial σ ℂ))) =
        monomial (∑ i ∈ t, Finsupp.single i 1) 1 := by
      rw [monomial_sum_one]; rfl
    rw [hX, coeff_monomial]
    by_cases ht : t = Finset.univ
    · subst ht
      have : (∑ i ∈ (Finset.univ : Finset (Fin L)), Finsupp.single i 1) = e := by
        ext j; simp [he, Finsupp.finsetSum_apply, Finsupp.single_apply]
      simp [this]
    · obtain ⟨j, hj⟩ : ∃ j, j ∉ t := by
        by_contra h; push_neg at h; exact ht (Finset.eq_univ_iff_forall.mpr h)
      have : (∑ i ∈ t, Finsupp.single i 1) ≠ e := by
        intro h
        have := congrArg (fun f => f j) h
        simp [he, Finsupp.finsetSum_apply, Finsupp.single_apply, hj] at this
      simp [this, ht]
  rw [map_mul, hr, cmC, map_prod]
  simp_rw [map_add (f := _), map_one, map_mul, hr, hx]
  rw [Finset.prod_one_add, coeff_sum, Finset.sum_eq_single Finset.univ]
  · rw [hmono]; simp
  · intro t _ ht; rw [hmono, if_neg ht]
  · intro h; exact absurd (Finset.mem_powerset.mpr (Finset.Subset.refl _)) h

end GlobalTheory
end

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem t_exL_dual : T_exL_dual := by
  intro n L m a
  exact GlobalTheory.coeff_allOnes_prod_one_add_mul (σ := EntIdx n) m a

end GlobalTheory.PsCo.Cw2a
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DMDetbPEqZero
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem modeDerivation_det_eq_zero : GlobalTheory.PsCo.Cw2a.T_dM_detb := by
  intro n ε x
  let Mx : Matrix (Fin n) (Fin n) (Poly n) := Matrix.of fun a b => X (Sum.inr (a, b))
  let W : Matrix (Fin n) (Fin n) (Poly n) := (barM ε (Matrix.single x.1.2 x.1.1 1)).map C
  have hD : ∀ i j, dM ε x (Mx i j) = (Mx * W - W * Mx) i j := by
    intro i j
    simp only [dM, dZ, Mx, W, Matrix.of_apply, mkDerivation_X, Sum.elim_inr, Matrix.sub_apply,
      Matrix.mul_apply, Matrix.map_apply, Finset.sum_sub_distrib]
  have key := GlobalTheory.T.derivation_det_eq_double_sum_adjugate_entry (dM ε x) Mx
  have hdet : detbP n = Mx.det := rfl
  rw [hdet, key]
  simp_rw [hD]
  have htr : ∑ i, ∑ j, Mx.adjugate j i * (Mx * W - W * Mx) i j
      = Matrix.trace (Mx.adjugate * (Mx * W - W * Mx)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [Finset.sum_comm]
  rw [htr, Matrix.mul_sub, Matrix.trace_sub, ← Matrix.mul_assoc Mx.adjugate Mx W, Matrix.adjugate_mul,
    ← Matrix.mul_assoc Mx.adjugate W Mx, Matrix.trace_mul_comm (Mx.adjugate * W) Mx,
    ← Matrix.mul_assoc Mx Mx.adjugate W, Matrix.mul_adjugate, sub_self]

end GlobalTheory.PsCo.Cw2a
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TDualProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualProdLogDerivModSq
open MvPolynomial

namespace GlobalTheory

theorem dualProd_logDeriv_modSq : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] (δ : Derivation K R R) {N : ℕ} (e f : Fin N → R) (I : Ideal R), (∀ i, δ (e i) = 0) → (∀ i, e i ^ 2 ∈ I) → δ (∏ i, (1 + e i * f i)) - (∏ i, (1 + e i * f i)) * ∑ i, e i * δ (f i) ∈ I := by
  intro K R _ _ _ δ N
  induction N with
  | zero => intro e f I _ _; simp
  | succ n ih =>
    intro e f I he he2
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
    have h := ih (fun i => e i.succ) (fun i => f i.succ) I (fun i => he _) (fun i => he2 _)
    set P := ∏ i : Fin n, (1 + e i.succ * f i.succ)
    set S := ∑ i : Fin n, e i.succ * δ (f i.succ)
    have key : δ ((1 + e 0 * f 0) * P) - (1 + e 0 * f 0) * P * (e 0 * δ (f 0) + S)
        = (1 + e 0 * f 0) * (δ P - P * S) - e 0 ^ 2 * (f 0 * P * δ (f 0)) := by
      simp only [Derivation.leibniz, map_add (f := _), Derivation.map_one_eq_zero, he 0, smul_eq_mul]
      ring
    rw [key]
    exact I.sub_mem (I.mul_mem_left _ h) (I.mul_mem_right _ (he2 0))

end GlobalTheory
end

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem t_dual_prod : T_dual_prod := by
  intro A _ _ D L la m J hD hsq
  exact GlobalTheory.dualProd_logDeriv_modSq (K := ℂ) D la m J hD hsq

end GlobalTheory.PsCo.Cw2a
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DMBlockEntries
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem dM_X_inl_entry {n : ℕ} (ε : Fin n → Bool) (x : Mode ε) (a b : Fin n) :
    dM ε x (X (Sum.inl (a, b))) =
      (if x.1.1 = b then X (Sum.inl (a, x.1.2)) else 0) - (if a = x.1.2 then X (Sum.inl (x.1.1, b)) else 0) := by
  classical
  simp only [dM, dZ, mkDerivation_X, Sum.elim_inl]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single x.1.2]
    · by_cases h : x.1.1 = b <;> simp [Matrix.single_apply, h]
    · intro c _ hc
      simp [Matrix.single_apply, Ne.symm hc]
    · simp
  · rw [Finset.sum_eq_single x.1.1]
    · by_cases h : a = x.1.2
      · simp [Matrix.single_apply, h]
      · simp [Matrix.single_apply, h, Ne.symm h]
    · intro c _ hc
      simp [Matrix.single_apply, Ne.symm hc]
    · simp

theorem dM_block_entries : BlockDeterminantCondition := by
  intro n ε a b hab
  classical
  cases ha : ε a with
  | true =>
    refine ⟨fun x y => if x.1.1 = b ∧ y = ⟨(a, x.1.2), ha, x.2.2⟩ then 1 else 0, fun x => ?_⟩
    have hne : a ≠ x.1.2 := by
      intro h
      have := x.2.2
      rw [← h, ha] at this
      exact Bool.noConfusion this
    rw [dM_X_inl_entry, if_neg hne, sub_zero, Finset.sum_eq_single (⟨(a, x.1.2), ha, x.2.2⟩ : Mode ε)]
    · by_cases h : x.1.1 = b <;> simp [h]
    · intro y _ hy
      simp [hy]
    · simp
  | false =>
    have hb : ε b = false := by rw [← hab, ha]
    refine ⟨fun x y => if a = x.1.2 ∧ y = ⟨(x.1.1, b), x.2.1, hb⟩ then -1 else 0, fun x => ?_⟩
    have hne : x.1.1 ≠ b := by
      intro h
      have := x.2.1
      rw [h, hb] at this
      exact Bool.noConfusion this
    rw [dM_X_inl_entry, if_neg hne, zero_sub, Finset.sum_eq_single (⟨(x.1.1, b), x.2.1, hb⟩ : Mode ε)]
    · by_cases h : a = x.1.2 <;> simp [h]
    · intro y _ hy
      simp [hy]
    · simp

end GlobalTheory.PsCo.Cw2a
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BarMSingle
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.DMComm

variable {n : ℕ}

theorem barM_single (ε : Fin n → Bool) (x : Mode ε) :
    barM ε (Matrix.single x.1.2 x.1.1 1) = Matrix.single x.1.1 x.1.2 1 := by
  obtain ⟨⟨a, b⟩, ha, hb⟩ := x
  ext i j
  simp only [barM, Matrix.single_apply]
  by_cases h : b = j ∧ a = i
  · obtain ⟨rfl, rfl⟩ := h
    simp only at ha hb
    simp [sg, ha, hb]
  · have h' : ¬ (a = i ∧ b = j) := fun h2 => h ⟨h2.2, h2.1⟩
    simp [h, h']

theorem dM_inl (ε : Fin n → Bool) (x : Mode ε) (i j : Fin n) :
    dM ε x (X (Sum.inl (i, j))) = (if j = x.1.1 then X (Sum.inl (i, x.1.2)) else 0)
      - (if i = x.1.2 then X (Sum.inl (x.1.1, j)) else 0) := by
  simp only [dM, dZ, mkDerivation_X, Sum.elim_inl, Finset.sum_sub_distrib]
  congr 1
  · by_cases h : j = x.1.1
    · subst h
      simp [Matrix.single_apply, apply_ite]
    · simp [Matrix.single_apply, h, Ne.symm h]
  · by_cases h : i = x.1.2
    · subst h
      simp [Matrix.single_apply, apply_ite]
    · simp [Matrix.single_apply, h, Ne.symm h]

theorem dM_inr (ε : Fin n → Bool) (x : Mode ε) (i j : Fin n) :
    dM ε x (X (Sum.inr (i, j))) = (if j = x.1.2 then X (Sum.inr (i, x.1.1)) else 0)
      - (if i = x.1.1 then X (Sum.inr (x.1.2, j)) else 0) := by
  simp only [dM, dZ, mkDerivation_X, Sum.elim_inr, Finset.sum_sub_distrib, barM_single]
  congr 1
  · by_cases h : j = x.1.2
    · subst h
      simp [Matrix.single_apply, apply_ite]
    · simp [Matrix.single_apply, h, Ne.symm h]
  · by_cases h : i = x.1.1
    · subst h
      simp [Matrix.single_apply, apply_ite]
    · simp [Matrix.single_apply, h, Ne.symm h]

theorem mode_ne (ε : Fin n → Bool) (w x : Mode ε) : x.1.2 ≠ w.1.1 := by
  intro h
  have h1 := x.2.2
  rw [h, w.2.1] at h1
  exact absurd h1 (by simp)

theorem dM_comm_X (ε : Fin n → Bool) (w x : Mode ε) (v : (Fin n × Fin n) ⊕ (Fin n × Fin n)) :
    dM ε w (dM ε x (X v)) = dM ε x (dM ε w (X v)) := by
  have h1 := mode_ne ε w x
  have h2 := mode_ne ε x w
  have h3 := h1.symm
  have h4 := h2.symm
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · simp only [dM_inl, map_sub, apply_ite (dM ε w), apply_ite (dM ε x), map_zero, h1, h2, h3, h4, if_false]
    split_ifs <;> simp_all
  · simp only [dM_inr, map_sub, apply_ite (dM ε w), apply_ite (dM ε x), map_zero, h1, h2, h3, h4, if_false]
    split_ifs <;> simp_all

theorem dM_comm : GlobalTheory.PsCo.Cw2a.T_dM_comm := by
  intro n ε w x P
  have h : ⁅dM ε w, dM ε x⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro v
    rw [Derivation.commutator_apply, dM_comm_X, sub_self]
    rfl
  have h2 := congrArg (fun D : Derivation ℂ (Poly n) (Poly n) => D P) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using h2

end GlobalTheory.PsCo.DMComm
end

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.PsCo.Pc1.A

theorem dM_comm : ∀ {n : ℕ} (ε : Fin n → Bool) (w x : Mode ε) (P : Poly n), dM ε w (dM ε x P) = dM ε x (dM ε w P) :=
  GlobalTheory.PsCo.DMComm.dM_comm

theorem coefM_dMu : ∀ {n L : ℕ} (ε : Fin n → Bool) (x : Mode ε) (k : ℕ) (s : PolyM n L),
    coefM n L k (dMu L ε x s) = dL L ε x (coefM n L k s) :=
  GlobalTheory.PsCo.Cw2a.coefM_dMu

theorem coefM_pencil : ∀ {n L : ℕ} {I : Type} [Fintype I] [DecidableEq I] (A0 B0 : Matrix I I (PolyL n L)),
    let Z : Matrix I I (PolyM n L) := fun x y => muM n L * inM n L (A0 x y) + inM n L (B0 x y)
    (∀ k, Fintype.card I < k → coefM n L k Z.det = 0) ∧ coefM n L (Fintype.card I) Z.det = A0.det ∧
      ∀ k x y, Fintype.card I ≤ k → coefM n L k (Z.adjugate y x) = 0 :=
  GlobalTheory.coefM_pencil

end GlobalTheory.PsCo.Pc1.A

end
end

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.PsCo.Pc1.A

variable {n L : ℕ}

section Obj

variable (ε : Fin n → Bool) (L : ℕ)

def i2 : Poly n →ₐ[ℂ] PolyM n L := (inM n L).comp (inL n L)

def Zm (A0 B0 : Matrix (Mode ε) (Mode ε) (PolyL n L)) : Matrix (Mode ε) (Mode ε) (PolyM n L) :=
  fun x y => muM n L * inM n L (A0 x y) + inM n L (B0 x y)

def JL : Ideal (PolyL n L) := Ideal.span (Set.range fun i : Fin L => laL n i ^ 2)

def JM : Ideal (PolyM n L) := Ideal.span (Set.range fun i : Fin L => inM n L (laL n i) ^ 2)

end Obj

section Key

variable {n L : ℕ} (ε : Fin n → Bool)

def pencilDerivativePartMatrix (L : ℕ) : Matrix (Mode ε) (Mode ε) (PolyL n L) := fun x y => inL n L (OmP ε x y)

def pencilConstantPartMatrix (c : Fin L → Mode ε → Mode ε → ℂ) : Matrix (Mode ε) (Mode ε) (PolyL n L) :=
  fun x y => ∑ i, laL n i * C (c i x y)

def dualNumberFactorsProduct (m : Fin L → Poly n) : PolyL n L := ∏ i, (1 + laL n i * inL n L (m i))

def pencilDeterminantWeight (M : ℕ) (m : Fin L → Poly n) : PolyL n L := inL n L (detbP n ^ M) * dualNumberFactorsProduct m

end Key

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma pderiv_mu_lambdaPoly_lemma_5 (f : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L) :
    pderiv none (_root_.GlobalTheory.PsCo.Pc1.A.inM n L f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [_root_.GlobalTheory.PsCo.Pc1.A.inM]
  | add p q hp hq => simp [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Derivation.leibniz, hp, smul_eq_mul, map_add (f := _)]
    simp [_root_.GlobalTheory.PsCo.Pc1.A.inM, pderiv_X]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma pderiv_mu_muVariable_lemma_6 : pderiv none (_root_.GlobalTheory.PsCo.Pc1.A.muM n L) = 1 := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.muM, pderiv_X]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma pencilModeDerivation_lambdaPoly_lemma_7 (x : _root_.GlobalTheory.PsCo.Pc1.Mode ε) (f : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L) :
    _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε x (_root_.GlobalTheory.PsCo.Pc1.A.inM n L f) =
      _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.dL L ε x f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [_root_.GlobalTheory.PsCo.Pc1.A.inM]
  | add p q hp hq => simp [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Derivation.leibniz, hp, smul_eq_mul, map_add (f := _)]
    simp [_root_.GlobalTheory.PsCo.Pc1.A.dMu, _root_.GlobalTheory.PsCo.Pc1.A.inM, mkDerivation_X]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma lambdaModeDerivation_entryPoly_lemma_8 (x : _root_.GlobalTheory.PsCo.Pc1.Mode ε) (P : _root_.GlobalTheory.PsCo.Pc1.Poly n) :
    _root_.GlobalTheory.PsCo.Pc1.A.dL L ε x (_root_.GlobalTheory.PsCo.Pc1.A.inL n L P) =
      _root_.GlobalTheory.PsCo.Pc1.A.inL n L (_root_.GlobalTheory.PsCo.Pc1.dM ε x P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [_root_.GlobalTheory.PsCo.Pc1.A.inL]
  | add p q hp hq => simp [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Derivation.leibniz, hp, smul_eq_mul, map_add (f := _)]
    simp [_root_.GlobalTheory.PsCo.Pc1.A.dL, _root_.GlobalTheory.PsCo.Pc1.A.inL, mkDerivation_X]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma pencilModeDerivation_muVariable_lemma_9 (x : _root_.GlobalTheory.PsCo.Pc1.Mode ε) :
    _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε x (_root_.GlobalTheory.PsCo.Pc1.A.muM n L) = 0 := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.dMu, _root_.GlobalTheory.PsCo.Pc1.A.muM, mkDerivation_X]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma lambdaModeDerivation_variable_lemma_10 (x : _root_.GlobalTheory.PsCo.Pc1.Mode ε) (i : Fin L) :
    _root_.GlobalTheory.PsCo.Pc1.A.dL L ε x (_root_.GlobalTheory.PsCo.Pc1.A.laL n i) = 0 := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.dL, _root_.GlobalTheory.PsCo.Pc1.A.laL, mkDerivation_X]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma modeDerivation_offDiagonalEntry_lemma_21 (x j : _root_.GlobalTheory.PsCo.Pc1.Mode ε) :
    _root_.GlobalTheory.PsCo.Pc1.dM ε x (X (Sum.inl j.1)) = 0 := by
  obtain ⟨⟨r, c⟩, hr, hc⟩ := j
  obtain ⟨⟨a, b⟩, ha, hb⟩ := x
  simp only [_root_.GlobalTheory.PsCo.Pc1.dM, _root_.GlobalTheory.PsCo.Pc1.dZ, mkDerivation_X, Sum.elim_inl,
    Matrix.single_apply]
  have h1 : a ≠ c := fun h => by simp_all
  have h2 : b ≠ r := fun h => by simp_all
  simp [h1, h2]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma modeDerivation_offDiagonalBlockSqNorm_lemma_19 (x : _root_.GlobalTheory.PsCo.Pc1.Mode ε) :
    _root_.GlobalTheory.PsCo.Pc1.dM ε x (_root_.GlobalTheory.PsCo.Pc1.rP ε) =
      ∑ j, X (Sum.inl j.1) * _root_.GlobalTheory.PsCo.Pc1.OmP ε x j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [_root_.GlobalTheory.PsCo.Pc1.rP, _root_.GlobalTheory.PsCo.Pc1.OmP, map_sum, Derivation.leibniz,
    modeDerivation_offDiagonalEntry_lemma_21]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma pencilModeDerivation_embedding_lemma_16 (x : _root_.GlobalTheory.PsCo.Pc1.Mode ε) (s : _root_.GlobalTheory.PsCo.Pc1.Poly n) :
    _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε x (_root_.GlobalTheory.PsCo.Pc1.A.i2 L s) =
      _root_.GlobalTheory.PsCo.Pc1.A.i2 L (_root_.GlobalTheory.PsCo.Pc1.dM ε x s) := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.i2, pencilModeDerivation_lambdaPoly_lemma_7, lambdaModeDerivation_entryPoly_lemma_8]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma lambdaPoly_mem_lambdaSquaresIdealPolyM_lemma_20 {g : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L}
    (hg : g ∈ _root_.GlobalTheory.PsCo.Pc1.A.JL L) :
    _root_.GlobalTheory.PsCo.Pc1.A.inM n L g ∈ _root_.GlobalTheory.PsCo.Pc1.A.JM L := by
  have h : Ideal.map (_root_.GlobalTheory.PsCo.Pc1.A.inM n L) (_root_.GlobalTheory.PsCo.Pc1.A.JL (n := n) L) =
      _root_.GlobalTheory.PsCo.Pc1.A.JM L := by
    simp only [_root_.GlobalTheory.PsCo.Pc1.A.JL, _root_.GlobalTheory.PsCo.Pc1.A.JM, Ideal.map_span, ← Set.range_comp]
    simp [Function.comp_def, map_pow]
  exact h ▸ Ideal.mem_map_of_mem _ hg

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma weight_modeDerivation_sub_mem_lemma_11 (M : ℕ) (m : Fin L → _root_.GlobalTheory.PsCo.Pc1.Poly n)
    (c : Fin L → _root_.GlobalTheory.PsCo.Pc1.Mode ε → _root_.GlobalTheory.PsCo.Pc1.Mode ε → ℂ)
    (hc : ∀ l x, _root_.GlobalTheory.PsCo.Pc1.dM ε x (m l) = ∑ y, C (c l x y) * X (Sum.inl y.1))
    (i : _root_.GlobalTheory.PsCo.Pc1.Mode ε) :
    _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε i (_root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight M m)) +
        _root_.GlobalTheory.PsCo.Pc1.A.muM n L *
          _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε i (_root_.GlobalTheory.PsCo.Pc1.A.i2 L (_root_.GlobalTheory.PsCo.Pc1.rP ε)) *
          _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight M m) -
      _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight M m) *
        ∑ j, _root_.GlobalTheory.PsCo.Pc1.A.Zm ε L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix ε L) (_root_.GlobalTheory.PsCo.Pc1.A.pencilConstantPartMatrix ε c) i j *
          _root_.GlobalTheory.PsCo.Pc1.A.i2 L (X (Sum.inl j.1)) ∈ _root_.GlobalTheory.PsCo.Pc1.A.JM L := by
  have hP0 := _root_.GlobalTheory.PsCo.Cw2a.t_dual_prod (_root_.GlobalTheory.PsCo.Pc1.A.dL L ε i)
    (fun l => _root_.GlobalTheory.PsCo.Pc1.A.laL n l)
    (fun l => _root_.GlobalTheory.PsCo.Pc1.A.inL n L (m l)) (_root_.GlobalTheory.PsCo.Pc1.A.JL L)
    (fun l => lambdaModeDerivation_variable_lemma_10 ε i l) (fun l => Ideal.subset_span ⟨l, rfl⟩)
  have hk : _root_.GlobalTheory.PsCo.Pc1.dM ε i (_root_.GlobalTheory.PsCo.Pc1.detbP n) = 0 :=
    _root_.GlobalTheory.PsCo.Cw2a.modeDerivation_det_eq_zero ε i
  have hdM : _root_.GlobalTheory.PsCo.Pc1.dM ε i (_root_.GlobalTheory.PsCo.Pc1.detbP n ^ M) = 0 := by
    simp [Derivation.leibniz_pow, hk]
  have hE : _root_.GlobalTheory.PsCo.Pc1.A.dL L ε i (_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight M m) =
      _root_.GlobalTheory.PsCo.Pc1.A.inL n L (_root_.GlobalTheory.PsCo.Pc1.detbP n ^ M) *
        _root_.GlobalTheory.PsCo.Pc1.A.dL L ε i (_root_.GlobalTheory.PsCo.Pc1.A.dualNumberFactorsProduct m) := by
    rw [_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight, Derivation.leibniz, lambdaModeDerivation_entryPoly_lemma_8, hdM]
    simp
  have hB : ∑ j, _root_.GlobalTheory.PsCo.Pc1.A.pencilConstantPartMatrix ε c i j * _root_.GlobalTheory.PsCo.Pc1.A.inL n L (X (Sum.inl j.1)) =
      ∑ l, _root_.GlobalTheory.PsCo.Pc1.A.laL n l *
        _root_.GlobalTheory.PsCo.Pc1.A.dL L ε i (_root_.GlobalTheory.PsCo.Pc1.A.inL n L (m l)) := by
    simp only [_root_.GlobalTheory.PsCo.Pc1.A.pencilConstantPartMatrix, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [lambdaModeDerivation_entryPoly_lemma_8, hc, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp [_root_.GlobalTheory.PsCo.Pc1.A.inL, mul_assoc]
  have hA : ∑ j, _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix ε L i j) *
        _root_.GlobalTheory.PsCo.Pc1.A.i2 L (X (Sum.inl j.1)) =
      _root_.GlobalTheory.PsCo.Pc1.A.i2 L (_root_.GlobalTheory.PsCo.Pc1.dM ε i (_root_.GlobalTheory.PsCo.Pc1.rP ε)) := by
    rw [modeDerivation_offDiagonalBlockSqNorm_lemma_19]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, _root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix, _root_.GlobalTheory.PsCo.Pc1.A.i2, mul_comm]
  have hsplit : ∑ j, _root_.GlobalTheory.PsCo.Pc1.A.Zm ε L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix ε L) (_root_.GlobalTheory.PsCo.Pc1.A.pencilConstantPartMatrix ε c) i j *
        _root_.GlobalTheory.PsCo.Pc1.A.i2 L (X (Sum.inl j.1)) =
      _root_.GlobalTheory.PsCo.Pc1.A.muM n L * ∑ j, _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix ε L i j) *
          _root_.GlobalTheory.PsCo.Pc1.A.i2 L (X (Sum.inl j.1)) +
        _root_.GlobalTheory.PsCo.Pc1.A.inM n L
          (∑ j, _root_.GlobalTheory.PsCo.Pc1.A.pencilConstantPartMatrix ε c i j * _root_.GlobalTheory.PsCo.Pc1.A.inL n L (X (Sum.inl j.1))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [_root_.GlobalTheory.PsCo.Pc1.A.Zm, add_mul, Finset.sum_add_distrib, Finset.mul_sum, map_sum, map_mul, mul_assoc]
    rfl
  rw [hsplit, pencilModeDerivation_embedding_lemma_16, hA, hB, pencilModeDerivation_lambdaPoly_lemma_7, hE]
  have key : _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.inL n L (_root_.GlobalTheory.PsCo.Pc1.detbP n ^ M) *
          _root_.GlobalTheory.PsCo.Pc1.A.dL L ε i (_root_.GlobalTheory.PsCo.Pc1.A.dualNumberFactorsProduct m)) +
        _root_.GlobalTheory.PsCo.Pc1.A.muM n L *
          _root_.GlobalTheory.PsCo.Pc1.A.i2 L (_root_.GlobalTheory.PsCo.Pc1.dM ε i (_root_.GlobalTheory.PsCo.Pc1.rP ε)) *
          _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight M m) -
      _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight M m) *
        (_root_.GlobalTheory.PsCo.Pc1.A.muM n L *
            _root_.GlobalTheory.PsCo.Pc1.A.i2 L (_root_.GlobalTheory.PsCo.Pc1.dM ε i (_root_.GlobalTheory.PsCo.Pc1.rP ε)) +
          _root_.GlobalTheory.PsCo.Pc1.A.inM n L (∑ l, _root_.GlobalTheory.PsCo.Pc1.A.laL n l *
            _root_.GlobalTheory.PsCo.Pc1.A.dL L ε i (_root_.GlobalTheory.PsCo.Pc1.A.inL n L (m l)))) =
      _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.inL n L (_root_.GlobalTheory.PsCo.Pc1.detbP n ^ M) *
        (_root_.GlobalTheory.PsCo.Pc1.A.dL L ε i (_root_.GlobalTheory.PsCo.Pc1.A.dualNumberFactorsProduct m) -
          _root_.GlobalTheory.PsCo.Pc1.A.dualNumberFactorsProduct m * ∑ l, _root_.GlobalTheory.PsCo.Pc1.A.laL n l *
            _root_.GlobalTheory.PsCo.Pc1.A.dL L ε i (_root_.GlobalTheory.PsCo.Pc1.A.inL n L (m l)))) := by
    simp only [_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight, map_mul, map_sub]
    ring
  rw [key]
  exact lambdaPoly_mem_lambdaSquaresIdealPolyM_lemma_20 (Ideal.mul_mem_left _ _ hP0)

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma optionEquivLeft_rename_some_eq_C_lemma_23 (a : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L) :
    optionEquivLeft ℂ _ (rename some a) = Polynomial.C a := by
  have h : ((optionEquivLeft ℂ (Fin L ⊕ _root_.GlobalTheory.PsCo.Pc1.A.EntIdx n)).toAlgHom.comp (rename some)) =
      (Polynomial.CAlgHom : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L →ₐ[ℂ] _) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [optionEquivLeft_X_some]
  exact congrArg (fun f => f a) h

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma muCoeff_lambdaPoly_mul_lemma_18 (a : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L) (F : _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.A.coefM n L k (_root_.GlobalTheory.PsCo.Pc1.A.inM n L a * F) =
      a * _root_.GlobalTheory.PsCo.Pc1.A.coefM n L k F := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.coefM, _root_.GlobalTheory.PsCo.Pc1.A.inM, optionEquivLeft_rename_some_eq_C_lemma_23]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma lambdaCoeff_mul_variable_sq_lemma_22 (G : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L) (i : Fin L) :
    _root_.GlobalTheory.PsCo.Pc1.A.exL n L (G * _root_.GlobalTheory.PsCo.Pc1.A.laL n i ^ 2) = 0 := by
  simp only [_root_.GlobalTheory.PsCo.Pc1.A.exL, _root_.GlobalTheory.PsCo.Pc1.A.laL, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, map_mul, map_pow, sumAlgEquiv_X_inl]
  simp only [LinearMap.coe_restrictScalars, MvPolynomial.lcoeff_apply]
  rw [X_pow_eq_monomial, coeff_mul_monomial', if_neg]
  intro h
  have := h i
  simp [_root_.GlobalTheory.PsCo.Pc1.A.allOnes] at this

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma coeff_eq_zero_of_mem_lambdaSquares_lemma_12 {g : _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L}
    (hg : g ∈ _root_.GlobalTheory.PsCo.Pc1.A.JM L) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k g) = 0 := by
  rw [_root_.GlobalTheory.PsCo.Pc1.A.JM, Ideal.mem_span_range_iff_exists_fun] at hg
  obtain ⟨f, rfl⟩ := hg
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [← map_pow, mul_comm, muCoeff_lambdaPoly_mul_lemma_18, mul_comm, lambdaCoeff_mul_variable_sq_lemma_22]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma sumAlgEquiv_rename_inr_eq_C_lemma_25 (s : _root_.GlobalTheory.PsCo.Pc1.Poly n) :
    sumAlgEquiv ℂ (Fin L) (_root_.GlobalTheory.PsCo.Pc1.A.EntIdx n) (rename Sum.inr s) = C s := by
  have h := sumAlgEquiv_comp_rename_inr ℂ (Fin L) (_root_.GlobalTheory.PsCo.Pc1.A.EntIdx n)
  exact congrArg (fun f => f s) h

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma extractCoeff_inl_mul (s : _root_.GlobalTheory.PsCo.Pc1.Poly n) (G : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L) :
    _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.inL n L s * G) =
      s * _root_.GlobalTheory.PsCo.Pc1.A.exL n L G := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.exL, _root_.GlobalTheory.PsCo.Pc1.A.inL, sumAlgEquiv_rename_inr_eq_C_lemma_25, coeff_C_mul]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma coeff_pderiv_mu_lemma_13 (F : _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k (pderiv none F)) =
      (k + 1 : _root_.GlobalTheory.PsCo.Pc1.Poly n) *
        _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L (k + 1) F) := by
  rw [_root_.GlobalTheory.PsCo.Cw2a.t_coefM_pderiv]
  simp only [Algebra.smul_def, map_add (f := _), map_natCast, map_one, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [show ((k : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L) + 1) =
      _root_.GlobalTheory.PsCo.Pc1.A.inL n L ((k : _root_.GlobalTheory.PsCo.Pc1.Poly n) + 1) by simp, extractCoeff_inl_mul]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma coeff_embedding_mul_lemma_14 (s : _root_.GlobalTheory.PsCo.Pc1.Poly n) (F : _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k (_root_.GlobalTheory.PsCo.Pc1.A.i2 L s * F)) =
      s * _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k F) := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.i2, muCoeff_lambdaPoly_mul_lemma_18, extractCoeff_inl_mul]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma coeff_modeDerivation_lemma_15 {ε : Fin n → Bool} (x : _root_.GlobalTheory.PsCo.Pc1.Mode ε)
    (F : _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k (_root_.GlobalTheory.PsCo.Pc1.A.dMu L ε x F)) =
      _root_.GlobalTheory.PsCo.Pc1.dM ε x
        (_root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k F)) := by
  rw [_root_.GlobalTheory.PsCo.Cw2a.coefM_dMu, _root_.GlobalTheory.PsCo.Cw2a.exL_dL_holds]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma muCoeff_zero_mu_mul_lemma_26 (F : _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L) :
    _root_.GlobalTheory.PsCo.Pc1.A.coefM n L 0 (_root_.GlobalTheory.PsCo.Pc1.A.muM n L * F) = 0 := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.coefM, _root_.GlobalTheory.PsCo.Pc1.A.muM]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma muCoeff_succ_mu_mul_lemma_27 (F : _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.A.coefM n L (k + 1) (_root_.GlobalTheory.PsCo.Pc1.A.muM n L * F) =
      _root_.GlobalTheory.PsCo.Pc1.A.coefM n L k F := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.coefM, _root_.GlobalTheory.PsCo.Pc1.A.muM]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma coeff_mu_mul_lemma_17 (F : _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k (_root_.GlobalTheory.PsCo.Pc1.A.muM n L * F)) =
      _root_.GlobalTheory.PsCo.Pc1.prev
        (fun k => _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k F)) k := by
  cases k with
  | zero => simp [muCoeff_zero_mu_mul_lemma_26, _root_.GlobalTheory.PsCo.Pc1.prev]
  | succ k => simp [muCoeff_succ_mu_mul_lemma_27, _root_.GlobalTheory.PsCo.Pc1.prev]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma shift_const_mul_lemma_4 (s : _root_.GlobalTheory.PsCo.Pc1.Poly n) (f : ℕ → _root_.GlobalTheory.PsCo.Pc1.Poly n) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.prev (fun k => s * f k) k = s * _root_.GlobalTheory.PsCo.Pc1.prev f k := by
  cases k <;> simp [_root_.GlobalTheory.PsCo.Pc1.prev]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma koszulRecursion_solvable_of_product_lemma (M : ℕ) (m : Fin L → _root_.GlobalTheory.PsCo.Pc1.Poly n)
    (c : Fin L → _root_.GlobalTheory.PsCo.Pc1.Mode ε → _root_.GlobalTheory.PsCo.Pc1.Mode ε → ℂ)
    (hc : ∀ l x, _root_.GlobalTheory.PsCo.Pc1.dM ε x (m l) = ∑ y, C (c l x y) * X (Sum.inl y.1)) :
    ∃ p q, _root_.GlobalTheory.PsCo.Pc1.IsKoszul ε p q ∧
      p (_root_.GlobalTheory.PsCo.Pc1.nMode ε) = _root_.GlobalTheory.PsCo.Pc1.topP ε M (∏ l, m l) := by
  set Z := _root_.GlobalTheory.PsCo.Pc1.A.Zm ε L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix ε L) (_root_.GlobalTheory.PsCo.Pc1.A.pencilConstantPartMatrix ε c) with hZ
  set w := _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight M m) with hw
  set a : _root_.GlobalTheory.PsCo.Pc1.Mode ε → _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L :=
    fun j => _root_.GlobalTheory.PsCo.Pc1.A.i2 L (X (Sum.inr j.1)) with ha
  set b : _root_.GlobalTheory.PsCo.Pc1.Mode ε → _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L :=
    fun j => _root_.GlobalTheory.PsCo.Pc1.A.i2 L (X (Sum.inl j.1)) with hb
  have h1 : ∀ i j, pderiv none (Z i j) = _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε i (a j) := by
    intro i j
    simp [hZ, ha, _root_.GlobalTheory.PsCo.Pc1.A.Zm, Derivation.leibniz, pderiv_mu_lambdaPoly_lemma_5, pderiv_mu_muVariable_lemma_6,
      _root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix, _root_.GlobalTheory.PsCo.Pc1.A.i2, pencilModeDerivation_lambdaPoly_lemma_7,
      lambdaModeDerivation_entryPoly_lemma_8, _root_.GlobalTheory.PsCo.Pc1.OmP]
  have h2 : ∀ h i j, _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε h (Z i j) = _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε i (Z h j) := by
    intro h i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hZ, _root_.GlobalTheory.PsCo.Pc1.A.Zm, Derivation.leibniz, pencilModeDerivation_muVariable_lemma_9,
      pencilModeDerivation_lambdaPoly_lemma_7, _root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix, lambdaModeDerivation_entryPoly_lemma_8,
      _root_.GlobalTheory.PsCo.Pc1.A.pencilConstantPartMatrix, map_add, map_sum, lambdaModeDerivation_variable_lemma_10, smul_zero, add_zero, smul_eq_mul,
      mul_zero]
    simp only [MvPolynomial.derivation_C, mul_zero, smul_zero, zero_add, add_zero, Finset.sum_const_zero, map_zero,
      smul_eq_mul, _root_.GlobalTheory.PsCo.Pc1.OmP]
    rw [_root_.GlobalTheory.PsCo.DMComm.dM_comm ε h i]
  have h3 : pderiv none w = 0 := pderiv_mu_lambdaPoly_lemma_5 _
  have h5 : _root_.GlobalTheory.PsCo.Pc1.A.i2 L (_root_.GlobalTheory.PsCo.Pc1.rP ε) = ∑ j, b j * a j := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hb, ha, _root_.GlobalTheory.PsCo.Pc1.rP, map_sum]
  have hmem := _root_.GlobalTheory.weighted_det_divergence_mem_ideal (fun x => _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε x) (pderiv none)
    (_root_.GlobalTheory.PsCo.Pc1.A.JM L) Z a b w (_root_.GlobalTheory.PsCo.Pc1.A.muM n L)
    (_root_.GlobalTheory.PsCo.Pc1.A.i2 L (_root_.GlobalTheory.PsCo.Pc1.rP ε)) h1 h2 h3
    (fun i => weight_modeDerivation_sub_mem_lemma_11 ε M m c hc i) h5
  obtain ⟨d1, d2, d3⟩ := _root_.GlobalTheory.coefM_pencil (_root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix ε L)
    (_root_.GlobalTheory.PsCo.Pc1.A.pencilConstantPartMatrix ε c)
  have e1 : ∀ k, Fintype.card (_root_.GlobalTheory.PsCo.Pc1.Mode ε) < k → _root_.GlobalTheory.PsCo.Pc1.A.coefM n L k Z.det = 0 := d1
  have e2 : _root_.GlobalTheory.PsCo.Pc1.A.coefM n L (Fintype.card (_root_.GlobalTheory.PsCo.Pc1.Mode ε)) Z.det =
      (_root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix ε L).det := d2
  have e3 : ∀ k x y, Fintype.card (_root_.GlobalTheory.PsCo.Pc1.Mode ε) ≤ k →
      _root_.GlobalTheory.PsCo.Pc1.A.coefM n L k (Z.adjugate y x) = 0 := d3
  have hN : _root_.GlobalTheory.PsCo.Pc1.nMode ε = Fintype.card (_root_.GlobalTheory.PsCo.Pc1.Mode ε) := rfl
  refine ⟨fun k => _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k (w * Z.det)),
    fun x k => _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k (w * ∑ j, Z.adjugate j x * a j)),
    ⟨fun k => ?_, fun k hk => ?_, fun x k hk => ?_⟩, ?_⟩
  · have hk := coeff_eq_zero_of_mem_lambdaSquares_lemma_12 hmem k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_add (f := _), map_sum, coeff_pderiv_mu_lemma_13, coeff_embedding_mul_lemma_14, coeff_modeDerivation_lemma_15, mul_assoc,
      pencilModeDerivation_embedding_lemma_16, coeff_mu_mul_lemma_17, shift_const_mul_lemma_4] at hk
    simp only [← mul_assoc] at hk ⊢
    linear_combination hk
  · rw [hN] at hk
    simp only [hw, muCoeff_lambdaPoly_mul_lemma_18]
    rw [e1 k hk, mul_zero, map_zero]
  · rw [hN] at hk
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [hw, ha, _root_.GlobalTheory.PsCo.Pc1.A.i2, AlgHom.comp_apply]
    rw [mul_comm (Z.adjugate j x), ← mul_assoc, ← map_mul, muCoeff_lambdaPoly_mul_lemma_18, e3 k x j hk, mul_zero, map_zero]
  · have hdet : (_root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix ε L).det =
        _root_.GlobalTheory.PsCo.Pc1.A.inL n L (_root_.GlobalTheory.PsCo.Pc1.OmP ε).det := by
      rw [AlgHom.map_det]; rfl
    simp only [hN, hw, muCoeff_lambdaPoly_mul_lemma_18]
    rw [e2, hdet]
    have hprod := _root_.GlobalTheory.PsCo.Cw2a.t_exL_dual (L := L) m
      (_root_.GlobalTheory.PsCo.Pc1.detbP n ^ M * (_root_.GlobalTheory.PsCo.Pc1.OmP ε).det)
    rw [show _root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight M m * _root_.GlobalTheory.PsCo.Pc1.A.inL n L (_root_.GlobalTheory.PsCo.Pc1.OmP ε).det =
        (∏ i, (1 + _root_.GlobalTheory.PsCo.Pc1.A.laL n i * _root_.GlobalTheory.PsCo.Pc1.A.inL n L (m i))) *
          _root_.GlobalTheory.PsCo.Pc1.A.inL n L
            (_root_.GlobalTheory.PsCo.Pc1.detbP n ^ M * (_root_.GlobalTheory.PsCo.Pc1.OmP ε).det) by
      simp only [_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight, _root_.GlobalTheory.PsCo.Pc1.A.dualNumberFactorsProduct, map_mul]; ring, hprod]
    simp only [_root_.GlobalTheory.PsCo.Pc1.topP]
    ring

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma shift_zero_lemma_2 (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.prev (fun _ => (0 : _root_.GlobalTheory.PsCo.Pc1.Poly n)) k = 0 := by
  cases k <;> simp [_root_.GlobalTheory.PsCo.Pc1.prev]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma shift_add_lemma_3 (f g : ℕ → _root_.GlobalTheory.PsCo.Pc1.Poly n) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.prev (fun k => f k + g k) k =
      _root_.GlobalTheory.PsCo.Pc1.prev f k + _root_.GlobalTheory.PsCo.Pc1.prev g k := by
  cases k <;> simp [_root_.GlobalTheory.PsCo.Pc1.prev]


open MvPolynomial in
variable {n L : ℕ} in
theorem _root_.GlobalTheory.PsCo.Pc1.A.stAlg : _root_.GlobalTheory.PsCo.Pc1.StAlg := by
  intro n ε M P hP
  have hP' : P ∈ Submodule.span ℂ (Submonoid.closure
      {P : _root_.GlobalTheory.PsCo.Pc1.Poly n | ∃ a b, ε a = ε b ∧ P = X (Sum.inl (a, b))} : Set _) := by
    rw [← Algebra.adjoin_eq_span]
    exact hP
  clear hP
  induction hP' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hx
    have hgen : ∀ i : Fin l.length, ∃ c : _root_.GlobalTheory.PsCo.Pc1.Mode ε → _root_.GlobalTheory.PsCo.Pc1.Mode ε → ℂ,
        ∀ x, _root_.GlobalTheory.PsCo.Pc1.dM ε x (l.get i) = ∑ y, C (c x y) * X (Sum.inl y.1) := by
      intro i
      obtain ⟨a, b, hab, he⟩ := hl _ (List.get_mem l i)
      rw [he]
      exact _root_.GlobalTheory.PsCo.Cw2a.dM_block_entries ε a b hab
    choose c hc using hgen
    obtain ⟨p, q, hpq, htop⟩ := koszulRecursion_solvable_of_product_lemma ε M (fun i => l.get i) c hc
    refine ⟨p, q, hpq, ?_⟩
    rw [htop, ← Fin.prod_ofFn, List.ofFn_get]
  | zero =>
    refine ⟨fun _ => 0, fun _ _ => 0, ⟨fun k => ?_, fun _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩
    · simp [shift_zero_lemma_2]
    · simp [_root_.GlobalTheory.PsCo.Pc1.topP]
  | add x y _ _ hx hy =>
    obtain ⟨p₁, q₁, ⟨r₁, s₁, t₁⟩, e₁⟩ := hx
    obtain ⟨p₂, q₂, ⟨r₂, s₂, t₂⟩, e₂⟩ := hy
    refine ⟨fun k => p₁ k + p₂ k, fun x k => q₁ x k + q₂ x k,
      ⟨fun k => ?_, fun k hk => ?_, fun x k hk => ?_⟩, ?_⟩
    · have h₁ := r₁ k
      have h₂ := r₂ k
      simp only [map_add (f := _), shift_add_lemma_3, mul_add, Finset.sum_add_distrib] at h₁ h₂ ⊢
      linear_combination h₁ + h₂
    · simp [s₁ k hk, s₂ k hk]
    · simp [t₁ x k hk, t₂ x k hk]
    · simp only [e₁, e₂, _root_.GlobalTheory.PsCo.Pc1.topP]
      ring
  | smul r x _ hx =>
    obtain ⟨p₁, q₁, ⟨r₁, s₁, t₁⟩, e₁⟩ := hx
    refine ⟨fun k => C r * p₁ k, fun x k => C r * q₁ x k,
      ⟨fun k => ?_, fun k hk => ?_, fun x k hk => ?_⟩, ?_⟩
    · have h₁ := r₁ k
      simp only [Derivation.leibniz, MvPolynomial.derivation_C, smul_zero, add_zero, smul_eq_mul, shift_const_mul_lemma_4]
      simp only [mul_add, Finset.sum_add_distrib] at h₁ ⊢
      have hc : ∀ x : _root_.GlobalTheory.PsCo.Pc1.Mode ε,
          _root_.GlobalTheory.PsCo.Pc1.dM ε x (_root_.GlobalTheory.PsCo.Pc1.rP ε) *
              (C r * _root_.GlobalTheory.PsCo.Pc1.prev (q₁ x) k) =
            C r * (_root_.GlobalTheory.PsCo.Pc1.dM ε x (_root_.GlobalTheory.PsCo.Pc1.rP ε) *
              _root_.GlobalTheory.PsCo.Pc1.prev (q₁ x) k) := fun _ => by ring
      simp only [mul_zero, Finset.sum_const_zero, add_zero, hc, ← Finset.mul_sum]
      linear_combination C r * h₁
    · simp [s₁ k hk]
    · simp [t₁ x k hk]
    · simp only [e₁, _root_.GlobalTheory.PsCo.Pc1.topP, smul_eq_C_mul]
      ring

end GlobalTheory.PsCo.Pc1.A

end
end
