module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.DetDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointShapeGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicHighestWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecondStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroEquivariantPairingHasForm
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
open scoped TensorProduct

namespace GlobalTheory.FockSplit

def jR (P Q R S : ℕ) : Ln P Q R 0 → Ln P Q R S := fun v => (v.1, Sum.elim Sum.inl (fun e => e.elim0) v.2)

def jS (P Q R S : ℕ) : Ln P Q 0 S → Ln P Q R S := fun v => (v.1, Sum.elim (fun e => e.elim0) Sum.inr v.2)

variable {P Q R S : ℕ}

theorem jR_injective : Function.Injective (jR P Q R S) := by
  rintro ⟨a, c | c⟩ ⟨a', c' | c'⟩ h
  · simp only [jR, Sum.elim_inl, Prod.mk.injEq, Sum.inl.injEq] at h; rw [h.1, h.2]
  · exact c'.elim0
  · exact c.elim0
  · exact c.elim0

theorem jS_injective : Function.Injective (jS P Q R S) := by
  rintro ⟨a, c | c⟩ ⟨a', c' | c'⟩ h
  · exact c.elim0
  · exact c.elim0
  · exact c'.elim0
  · simp only [jS, Sum.elim_inr, Prod.mk.injEq, Sum.inr.injEq] at h; rw [h.1, h.2]

theorem linePos_jR (l : Ln P Q R 0) : linePos (jR P Q R S l) = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> first | exact c.elim0 | rfl

theorem linePos_jS (l : Ln P Q 0 S) : linePos (jS P Q R S l) = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> first | exact c.elim0 | rfl

theorem jR_ne_jS (k : Ln P Q R 0) (m : Ln P Q 0 S) : jR P Q R S k ≠ jS P Q R S m := by
  rcases k with ⟨a, c | c⟩ <;> rcases m with ⟨a', e | e⟩
  · exact e.elim0
  · simp [jR, jS]
  · exact c.elim0
  · exact c.elim0

section General

variable {R' S' : ℕ} (j : Ln P Q R' S' → Ln P Q R S)

theorem pderiv_rename_eq_zero {σ τ : Type*} (i : σ → τ) (v : τ) (hv : ∀ m, i m ≠ v) (g : MvPolynomial σ ℂ) :
    pderiv v (rename i g) = 0 := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p m hp => simp [hp, pderiv_X, Pi.single_apply, hv m]

theorem pderiv_rename_mul (hj : Function.Injective j) (k : Ln P Q R' S') (f : Pol P Q R' S') (G : Pol P Q R S)
    (hG : pderiv (j k) G = 0) : pderiv (j k) (rename j f * G) = rename j (pderiv k f) * G := by
  rw [Derivation.leibniz, hG, smul_zero, zero_add, pderiv_rename hj, smul_eq_mul, mul_comm]

theorem raiB_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    raiB (j l) (rename j f * G) = rename j (raiB l f) * G := by
  unfold raiB; rw [hpos l]
  split_ifs
  · simp [mul_assoc]
  · simp [pderiv_rename_mul j hj l f G (hG l)]

theorem lowB_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    lowB (j l) (rename j f * G) = rename j (lowB l f) * G := by
  unfold lowB; rw [hpos l]
  split_ifs
  · simp [pderiv_rename_mul j hj l f G (hG l)]
  · simp [mul_assoc]

theorem omE_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l l' : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    omE (j l) (j l') (rename j f * G) = rename j (omE l l' f) * G := by
  simp only [omE, LinearMap.add_apply, Module.End.mul_apply, lowB_rename_mul j hj hpos l' f G hG,
    raiB_rename_mul j hj hpos l _ G hG, hj.eq_iff]
  split_ifs <;> simp [add_mul, smul_mul_assoc]

end General

theorem fockAct1_Eab_mul (a b : Ix P Q) (f : Pol P Q R 0) (g : Pol P Q 0 S) :
    fockAct1 P Q R S (Eab a b) (rename (jR P Q R S) f * rename (jS P Q R S) g) =
      rename (jR P Q R S) (fockAct1 P Q R 0 (Eab a b) f) * rename (jS P Q R S) g +
        rename (jR P Q R S) f * rename (jS P Q R S) (fockAct1 P Q 0 S (Eab a b) g) := by
  rw [fockAct1_Eab, fockAct1_Eab, fockAct1_Eab]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.add_apply, Fintype.sum_sum_type, Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add,
    map_sum, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    exact omE_rename_mul (jR P Q R S) jR_injective linePos_jR (a, .inl c) (b, .inl c) f _
      (fun k => pderiv_rename_eq_zero _ _ (fun m => (jR_ne_jS k m).symm) g)
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm, mul_comm (rename _ f)]
    exact omE_rename_mul (jS P Q R S) jS_injective linePos_jS (a, .inr c) (b, .inr c) g _
      (fun k => pderiv_rename_eq_zero _ _ (fun m => jR_ne_jS m k) f)

end GlobalTheory.FockSplit

namespace GlobalTheory.FockSplit

variable {P Q R S : ℕ}

end GlobalTheory.FockSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionUpperLeftCommutesEmbedding
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.FirstBlock

section General

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]

theorem der_aeval {σ : Type} [Fintype σ] [DecidableEq σ] (d : Derivation K A A) (z : σ → A)
    (G : MvPolynomial σ K) : d (aeval z G) = ∑ i, aeval z (pderiv i G) * d (z i) := by
  induction G using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have e : ∀ i, aeval z (pderiv i (p * X n)) * d (z i) =
        (if n = i then aeval z p * d (z i) else 0) + z n * (aeval z (pderiv i p) * d (z i)) := by
      intro i
      by_cases hi : n = i
      · subst hi
        simp [Derivation.leibniz]; ring
      · simp [Derivation.leibniz, hi, pderiv_X, Pi.single_apply]; ring
    simp only [e, Finset.sum_add_distrib]
    simp [hp, Finset.mul_sum]

theorem der_prod {ι : Type} [DecidableEq ι] (d : Derivation K A A) (s : Finset ι) (f : ι → A) :
    d (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * d (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz, ih, Finset.erase_insert ha,
      smul_eq_mul, smul_eq_mul, add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : a ≠ i := fun e => ha (e ▸ hi)
    rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)),
      mul_assoc]

theorem der_det {n : Type} [Fintype n] [DecidableEq n] (d : Derivation K A A) (M : Matrix n n A) :
    d M.det = ∑ i, (M.updateRow i fun j => d (M i j)).det := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.det_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.smul_sum, Units.smul_def, Units.smul_def, map_zsmul, der_prod,
    ← Equiv.sum_comp σ (fun i => ∏ x, (M.updateRow i fun j => d (M i j)) (σ x) x)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Matrix.updateRow_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Matrix.updateRow_ne (fun e => (Finset.mem_erase.1 hj).1 (σ.injective e))]

end General

variable {P Q R : ℕ}

noncomputable def rowDer (Q R : ℕ) (a a' : Fin P) : Derivation ℂ (Pol P Q R 0) (Pol P Q R 0) :=
  ∑ c : Fin R, (X (Sum.inl a, Sum.inl c) : Pol P Q R 0) • pderiv (Sum.inl a', Sum.inl c)

theorem rowDer_apply (a a' : Fin P) (F : Pol P Q R 0) :
    rowDer Q R a a' F = ∑ c : Fin R, X (Sum.inl a, Sum.inl c) * pderiv (Sum.inl a', Sum.inl c) F := by
  have := map_sum (Derivation.coeFnAddMonoidHom (R := ℂ) (A := Pol P Q R 0) (M := Pol P Q R 0))
    (fun c : Fin R => (X (Sum.inl a, Sum.inl c) : Pol P Q R 0) • pderiv (Sum.inl a', Sum.inl c)) Finset.univ
  have h2 := congrFun this F
  rw [Finset.sum_apply] at h2
  exact h2

theorem rowDer_X_inl_inl (a a' i : Fin P) (c : Fin R) :
    rowDer Q R a a' (X (Sum.inl i, Sum.inl c)) = if i = a' then X (Sum.inl a, Sum.inl c) else 0 := by
  rw [rowDer_apply]
  by_cases h : i = a' <;> simp [pderiv_X, Pi.single_apply, h]

theorem rowDer_w (a a' : Fin P) (b : Fin Q) (c : Fin R) :
    rowDer Q R a a' (X (Sum.inr b, Sum.inl c)) = 0 := by
  rw [rowDer_apply]
  simp [pderiv_X, Pi.single_apply]

theorem rowDer_mR (a a' i : Fin P) (b : Fin Q) :
    rowDer Q R a a' (mR P Q R i b) = if i = a' then mR P Q R a b else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mR, map_sum, Derivation.leibniz, rowDer_X_inl_inl, rowDer_w, smul_eq_mul]
  split_ifs <;> simp [mul_comm]

theorem rowDer_detR (h : P ≤ R) (a a' : Fin P) :
    rowDer Q R a a' (detR P Q R h) = if a = a' then detR P Q R h else 0 := by
  rw [detR, der_det, Finset.sum_eq_single a']
  · simp only [Matrix.of_apply, rowDer_X_inl_inl, if_true]
    split_ifs with e
    · subst e
      congr 1
      exact Matrix.updateRow_eq_self _ _
    · exact Matrix.det_updateRow_eq_zero (M := Matrix.of fun a c : Fin P =>
        (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)) e
  · intro i _ hi
    simp only [Matrix.of_apply, rowDer_X_inl_inl, if_neg hi]
    exact Matrix.det_eq_zero_of_row_eq_zero i (by simp)
  · simp

theorem act_eq (a a' : Fin P) (F : Pol P Q R 0) :
    fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inl a')) F =
      rowDer Q R a a' F + (if a = a' then (R : ℂ) / 2 else 0) • F := by
  have hpp : ∀ c : Fin R, omE (p := P) (q := Q) (r := R) (s := 0) (Sum.inl a, Sum.inl c) (Sum.inl a', Sum.inl c) F =
      X (Sum.inl a, Sum.inl c) * pderiv (Sum.inl a', Sum.inl c) F + (if a = a' then (1 / 2 : ℂ) else 0) • F := by
    intro c
    simp only [omE, raiB, lowB, linePos]
    by_cases e : a = a' <;> simp [e]
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, rowDer_apply]
  simp only [hpp, Finset.sum_add_distrib, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  split_ifs
  · congr 2; ring
  · simp

theorem act_first_block : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a a' : Fin P) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inl a')) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inl a) (Sum.inl a') G) := by
  intro P Q R h k a a' G
  have hk : rowDer Q R a a' (detR P Q R h ^ k) = (if a = a' then (k : ℂ) else 0) • detR P Q R h ^ k := by
    rw [Derivation.leibniz_pow, rowDer_detR]
    split_ifs
    · rcases k with _ | k
      · simp
      · rw [Nat.cast_smul_eq_nsmul, Nat.add_sub_cancel, smul_eq_mul, ← pow_succ]
    · simp
  have hG : rowDer Q R a a' (aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) G) =
      ∑ b, mR P Q R a b * aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) (pderiv (a', b) G) := by
    rw [der_aeval, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [rowDer_mR, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [mul_comm]
  have he : ∀ H, embR P Q R h k H =
      aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) H * detR P Q R h ^ k := fun H => rfl
  have ho : opR P Q R k (Sum.inl a) (Sum.inl a') G =
      ∑ b, X (a, b) * pderiv (a', b) G + (if a = a' then (k : ℂ) + (R : ℂ) / 2 else 0) • G := by
    by_cases e : a = a' <;> simp [opR, LinearMap.sum_apply, e]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [act_eq, he, he, ho, Derivation.leibniz, hk, hG, map_add (f := _), map_sum, map_smul]
  simp only [map_mul, aeval_X, smul_eq_mul, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [mul_comm (detR P Q R h ^ k)]
  split_ifs
  · module
  · simp

end GlobalTheory.CharPair.FirstBlock
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointMixedLower
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.SDown

theorem pderiv_aeval_sum {σ δ : Type} [Fintype σ] [DecidableEq σ] (f : σ → MvPolynomial δ ℂ) (i : δ)
    (G : MvPolynomial σ ℂ) : pderiv i (aeval f G) = ∑ u, pderiv i (f u) * aeval f (pderiv u G) := by
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _), aeval_X, hp, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single k]
      · simp [mul_comm]
      · intro b _ hb
        rw [pderiv_X_of_ne hb.symm]; simp
      · simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

theorem derivation_finset_prod {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [DecidableEq ι]
    (D : Derivation R A A) (f : ι → A) (s : Finset ι) :
    D (∏ j ∈ s, f j) = ∑ i ∈ s, ∏ j ∈ s, Function.update f i (D (f i)) j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.prod_insert ha,
      Function.update_self]
    have h1 : ∏ j ∈ s, Function.update f a (D (f a)) j = ∏ j ∈ s, f j := by
      refine Finset.prod_congr rfl fun j hj => ?_
      exact Function.update_of_ne (by rintro rfl; exact ha hj) _ _
    have h2 : ∀ i ∈ s, ∏ j ∈ insert a s, Function.update f i (D (f i)) j =
        f a * ∏ j ∈ s, Function.update f i (D (f i)) j := by
      intro i hi
      rw [Finset.prod_insert ha, Function.update_of_ne (by rintro rfl; exact ha hi)]
    rw [h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, smul_eq_mul, smul_eq_mul]
    ring

theorem derivation_det {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : Type*} [Fintype n] [DecidableEq n]
    (D : Derivation R A A) (M : Matrix n n A) :
    D M.det = ∑ i, (M.updateRow i fun j => D (M i j)).det := by
  have key : ∀ B : Matrix n n A, B.det = ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, B i (σ i) := by
    intro B
    rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, map_sum]
  simp_rw [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, derivation_finset_prod, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Units.smul_def]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · subst hj
    simp [Matrix.updateRow_self]
  · rw [Function.update_of_ne hj, Matrix.updateRow_ne hj]

theorem derivation_sum_apply {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} (s : Finset ι)
    (D : ι → Derivation R A A) (x : A) : (∑ t ∈ s, D t) x = ∑ t ∈ s, D t x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

variable {P Q S : ℕ}

theorem pderiv_u_mS (a : Fin P) (c : Fin S) (a0 : Fin P) (b0 : Fin Q) :
    pderiv ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (mS P Q S a0 b0) =
      if a0 = a then X (Sum.inr b0, Sum.inr c) else 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp [mS, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem pderiv_t_mS (b : Fin Q) (c : Fin S) (a0 : Fin P) (b0 : Fin Q) :
    pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) (mS P Q S a0 b0) =
      if b0 = b then X (Sum.inl a0, Sum.inr c) else 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp [mS, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem pderiv_u_detS (h : Q ≤ S) (a : Fin P) (c : Fin S) :
    pderiv ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (detS P Q S h) = 0 := by
  classical
  rw [detS, derivation_det]
  refine Finset.sum_eq_zero fun i _ => Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
  simp [pderiv_X, Pi.single_apply]

theorem sum_X_pderiv_detS (h : Q ≤ S) (b b' : Fin Q) :
    ∑ c : Fin S, X ((Sum.inr b', Sum.inr c) : Ln P Q 0 S) * pderiv (Sum.inr b, Sum.inr c) (detS P Q S h) =
      if b' = b then detS P Q S h else 0 := by
  classical
  let Dd : Derivation ℂ (Pol P Q 0 S) (Pol P Q 0 S) :=
    ∑ c : Fin S, (X (Sum.inr b', Sum.inr c) : Pol P Q 0 S) • pderiv (Sum.inr b, Sum.inr c)
  have hD : ∀ p, Dd p = ∑ c : Fin S, X ((Sum.inr b', Sum.inr c) : Ln P Q 0 S) * pderiv (Sum.inr b, Sum.inr c) p := by
    intro p; simp only [Dd, derivation_sum_apply, Derivation.smul_apply, smul_eq_mul]
  rw [← hD, detS, derivation_det]
  have hrow : ∀ i j : Fin Q, Dd ((Matrix.of fun b c : Fin Q => (X (Sum.inr b, Sum.inr (Fin.castLE h c)) : Pol P Q 0 S)) i j) =
      if i = b then X (Sum.inr b', Sum.inr (Fin.castLE h j)) else 0 := by
    intro i j
    rw [hD]
    by_cases hi : i = b
    · subst hi; simp [pderiv_X, Pi.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']
    · simp [pderiv_X, Pi.single_apply, hi]
  simp_rw [hrow]
  rw [Finset.sum_eq_single b]
  · simp only [if_true]
    split_ifs with hb
    · subst hb
      congr 1
      ext i j
      by_cases hi : i = b' <;> simp [Matrix.updateRow_apply, hi]
    · refine Matrix.det_zero_of_row_eq hb ?_
      ext j
      simp [Matrix.updateRow_apply, Ne.symm hb]
  · intro i _ hi
    refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
    simp [hi]
  · simp

end GlobalTheory.CharPair.SDown

namespace GlobalTheory.CharPair.SDown

variable {P Q S : ℕ}

theorem pderiv_u_aeval (a : Fin P) (c : Fin S) (H : Mdl P Q) :
    pderiv ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) H) =
      ∑ b0 : Fin Q, X (Sum.inr b0, Sum.inr c) * aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (pderiv (a, b0) H) := by
  classical
  rw [pderiv_aeval_sum, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [pderiv_u_mS]
  · intro a0 _ ha0; simp [pderiv_u_mS, ha0]
  · simp

theorem pderiv_t_aeval (b : Fin Q) (c : Fin S) (H : Mdl P Q) :
    pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) (aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) H) =
      ∑ a0 : Fin P, X (Sum.inl a0, Sum.inr c) * aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (pderiv (a0, b) H) := by
  classical
  rw [pderiv_aeval_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a0 _ => ?_
  rw [Finset.sum_eq_single b]
  · simp [pderiv_t_mS]
  · intro b0 _ hb0; simp [pderiv_t_mS, hb0]
  · simp

end GlobalTheory.CharPair.SDown

namespace GlobalTheory.CharPair.SDown

variable {P Q S : ℕ}

theorem rhs_eq (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inl a) G) =
      (∑ a0 : Fin P, ∑ b0 : Fin Q, mS P Q S a0 b0 *
          aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (pderiv (a0, b) (pderiv (a, b0) G)) +
        ((S + k' : ℕ) : ℂ) • aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (pderiv (a, b) G)) *
        detS P Q S h ^ k' := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [embS, opS, mulM, derM, LinearMap.sum_apply, map_sum, Module.End.mul_apply]

theorem key (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    ∑ c : Fin S, pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) (pderiv (Sum.inl a, Sum.inr c) (embS P Q S h k' G)) =
      embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inl a) G) := by
  classical
  rw [rhs_eq]
  set m : Fin P × Fin Q → Pol P Q 0 S := fun ab => mS P Q S ab.1 ab.2 with hm
  set D := detS P Q S h with hDdef
  have hE : embS P Q S h k' G = aeval m G * D ^ k' := by simp [embS, hm, hDdef]
  have step1 : ∀ c : Fin S, pderiv ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (embS P Q S h k' G) =
      ∑ b0 : Fin Q, X (Sum.inr b0, Sum.inr c) * aeval m (pderiv (a, b0) G) * D ^ k' := by
    intro c
    rw [hE, Derivation.leibniz, Derivation.leibniz_pow, hDdef, pderiv_u_detS, hm, pderiv_u_aeval]
    simp only [mul_zero, smul_zero, zero_add, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b0 _ => ?_
    ring
  have step2 : ∀ (c : Fin S) (b0 : Fin Q),
      pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) (X (Sum.inr b0, Sum.inr c) * aeval m (pderiv (a, b0) G) * D ^ k') =
        (if b0 = b then aeval m (pderiv (a, b) G) * D ^ k' else 0) +
        X (Sum.inr b0, Sum.inr c) * (∑ a0 : Fin P, X (Sum.inl a0, Sum.inr c) *
            aeval m (pderiv (a0, b) (pderiv (a, b0) G))) * D ^ k' +
        aeval m (pderiv (a, b0) G) * ((k' : Pol P Q 0 S) * D ^ (k' - 1)) *
          (X (Sum.inr b0, Sum.inr c) * pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) D) := by
    intro c b0
    rw [Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow, hm, pderiv_t_aeval, pderiv_X, Pi.single_apply]
    simp only [smul_eq_mul, nsmul_eq_mul, Prod.mk.injEq, Sum.inr.injEq, and_true]
    by_cases hb : b0 = b
    · subst hb
      simp only [if_true]
      ring
    · simp only [hb, if_false]
      ring
  have hT1 : ∑ c : Fin S, ∑ b0 : Fin Q, X ((Sum.inr b0, Sum.inr c) : Ln P Q 0 S) * (∑ a0 : Fin P, X (Sum.inl a0, Sum.inr c) *
      aeval m (pderiv (a0, b) (pderiv (a, b0) G))) * D ^ k' =
      ∑ a0 : Fin P, ∑ b0 : Fin Q, mS P Q S a0 b0 * aeval m (pderiv (a0, b) (pderiv (a, b0) G)) * D ^ k' := by
    simp only [mS, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b0 _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a0 _ => Finset.sum_congr rfl fun c _ => by ring
  have hT3 : ∑ c : Fin S, ∑ b0 : Fin Q, aeval m (pderiv (a, b0) G) * ((k' : Pol P Q 0 S) * D ^ (k' - 1)) *
      (X ((Sum.inr b0, Sum.inr c) : Ln P Q 0 S) * pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) D) =
      (k' : Pol P Q 0 S) * aeval m (pderiv (a, b) G) * D ^ k' := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have e : ∀ b0 : Fin Q, ∑ c : Fin S, X ((Sum.inr b0, Sum.inr c) : Ln P Q 0 S) * pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) D =
        if b0 = b then D else 0 := fun b0 => by rw [hDdef]; exact sum_X_pderiv_detS h b b0
    simp only [e, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rcases k' with _ | k
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]; ring
  have hT0 : ∑ c : Fin S, ∑ b0 : Fin Q, (if b0 = b then aeval m (pderiv (a, b) G) * D ^ k' else 0) =
      (S : Pol P Q 0 S) * aeval m (pderiv (a, b) G) * D ^ k' := by
    simp [Finset.sum_ite_eq', mul_assoc]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [step1, map_sum, step2, Finset.sum_add_distrib]
  rw [hT0, hT1, hT3, Nat.cast_smul_eq_nsmul ℂ, nsmul_eq_mul, add_mul, Finset.sum_mul]
  simp only [Finset.sum_mul]
  push_cast
  ring

end GlobalTheory.CharPair.SDown

namespace GlobalTheory.CharPair

end GlobalTheory.CharPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionLowerLeftCommutesEmbedding
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

noncomputable section

namespace GlobalTheory.CharPair.Down

variable {P Q R : ℕ}

theorem pderiv_pderiv_comm {σ : Type} (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  have h0 : ⁅(pderiv i : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)),
      (pderiv j : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have := congrArg (fun D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) => D f) h0
  simpa [Derivation.commutator_apply, sub_eq_zero] using this

theorem pderiv_s_mR (a' a : Fin P) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inl a', Sum.inl c) (mR P Q R a b) =
      if a' = a then X (Sum.inr b, Sum.inl c) else 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp [mR, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  rcases eq_or_ne a' a with rfl | ha
  · simp
  · simp [ha, Ne.symm ha]

theorem pderiv_w_mR (b' : Fin Q) (a : Fin P) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b', Sum.inl c) (mR P Q R a b) =
      if b' = b then X (Sum.inl a, Sum.inl c) else 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp [mR, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  rcases eq_or_ne b' b with rfl | hb
  · simp
  · simp [hb, Ne.symm hb]

theorem embR_eq (h : P ≤ R) (k : ℕ) (G : Mdl P Q) :
    embR P Q R h k G = aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) G * detR P Q R h ^ k := by
  simp [embR]

theorem derivation_det_eq_zero {σ : Type} {n : ℕ} (d : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (hM : ∀ i j, d (M i j) = 0) : d M.det = 0 := by
  have e : M.det = aeval (fun ij : Fin n × Fin n => M ij.1 ij.2)
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ)) := by
    rw [← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext i j; simp [Matrix.mvPolynomialX]
  rw [e, ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.derivation_aeval_eq]
  simp [hM]

def blockR (h : P ≤ R) : Matrix (Fin P) (Fin P) (Pol P Q R 0) :=
  Matrix.of fun a c : Fin P => (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)

theorem detR_eq (h : P ≤ R) : detR P Q R h = (blockR (Q := Q) h).det := rfl

theorem pderiv_w_detR (h : P ≤ R) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b, Sum.inl c) (detR P Q R h) = 0 := by
  classical
  rw [detR_eq]
  apply derivation_det_eq_zero
  intro i j
  simp [blockR, pderiv_X, Pi.single_apply]

theorem pderiv_s_detR (h : P ≤ R) (a : Fin P) (c : Fin R) :
    pderiv (Sum.inl a, Sum.inl c) (detR P Q R h) =
      ∑ j : Fin P, if Fin.castLE h j = c then (blockR (Q := Q) h).adjugate j a else 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [detR_eq, Matrix.det_eq_sum_mul_adjugate_row _ a, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hadj : pderiv (Sum.inl a, Sum.inl c) ((blockR (Q := Q) h).adjugate j a) = 0 := by
    rw [Matrix.adjugate_apply]
    apply derivation_det_eq_zero
    intro i j'
    rw [Matrix.updateRow_apply]
    split_ifs with hi
    · simp [Pi.single_apply]; split_ifs <;> simp
    · simp [blockR, pderiv_X, Pi.single_apply, hi]
  rw [Derivation.leibniz, hadj]
  simp [blockR, pderiv_X, Pi.single_apply, eq_comm]
  done

theorem sum_s_pderiv_detR (h : P ≤ R) (a' a : Fin P) :
    ∑ c : Fin R, X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h) =
      if a' = a then detR P Q R h else 0 := by
  classical
  have e : ∀ c : Fin R, X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h) =
      ∑ j : Fin P, if Fin.castLE h j = c then blockR (Q := Q) h a' j * (blockR (Q := Q) h).adjugate j a
        else 0 := by
    intro c
    rw [pderiv_s_detR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · simp [blockR, hj]
    · simp
  rw [Finset.sum_congr rfl fun c _ => e c, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Matrix.mul_apply, Matrix.mul_adjugate, detR_eq]
  simp [Matrix.one_apply]

abbrev phiR (P Q R : ℕ) : Mdl P Q →ₐ[ℂ] Pol P Q R 0 := aeval fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2

theorem pderiv_s_phiR (a : Fin P) (c : Fin R) (H : Mdl P Q) :
    pderiv (Sum.inl a, Sum.inl c) (phiR P Q R H) =
      ∑ b' : Fin Q, phiR P Q R (pderiv (a, b') H) * X (Sum.inr b', Sum.inl c) := by
  classical
  rw [ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.derivation_aeval_eq, Fintype.sum_prod_type]
  simp only [pderiv_s_mR, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

theorem pderiv_w_phiR (b : Fin Q) (c : Fin R) (H : Mdl P Q) :
    pderiv (Sum.inr b, Sum.inl c) (phiR P Q R H) =
      ∑ a' : Fin P, phiR P Q R (pderiv (a', b) H) * X (Sum.inl a', Sum.inl c) := by
  classical
  rw [ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.derivation_aeval_eq, Fintype.sum_prod_type]
  simp only [pderiv_w_mR, mul_ite, mul_zero]
  simp [Finset.sum_ite_eq]

theorem pderiv_w_detR_pow (h : P ≤ R) (k : ℕ) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b, Sum.inl c) (detR P Q R h ^ k) = 0 := by
  rw [Derivation.leibniz_pow, pderiv_w_detR]; simp

theorem pderiv_w_s_detR_pow (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b, Sum.inl c) (pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k)) = 0 := by
  rw [pderiv_pderiv_comm, pderiv_w_detR_pow]; simp

theorem sum_s_pderiv_detR_pow (h : P ≤ R) (k : ℕ) (a' a : Fin P) :
    ∑ c : Fin R, X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k) =
      if a' = a then (k : Pol P Q R 0) * detR P Q R h ^ k else 0 := by
  classical
  simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
  have e : ∀ c : Fin R, X (Sum.inl a', Sum.inl c) *
      ((k : Pol P Q R 0) * (detR P Q R h ^ (k - 1) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h))) =
      (k : Pol P Q R 0) * detR P Q R h ^ (k - 1) *
        (X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h)) := fun c => by ring
  rw [Finset.sum_congr rfl fun c _ => e c, ← Finset.mul_sum, sum_s_pderiv_detR]
  split_ifs
  · rcases k with _ | k
    · simp
    · simp [pow_succ]; ring
  · simp

theorem omE_down (a : Fin P) (b : Fin Q) (c : Fin R) (f : Pol P Q R 0) :
    omE ((Sum.inr b, Sum.inl c) : Ln P Q R 0) (Sum.inl a, Sum.inl c) f =
      -(pderiv (Sum.inr b, Sum.inl c) (pderiv (Sum.inl a, Sum.inl c) f)) := by
  simp [omE, raiB, lowB, linePos]

theorem partial_derivative_weight_space_formula (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (c : Fin R) (G : Mdl P Q) :
    pderiv (Sum.inr b, Sum.inl c) (pderiv (Sum.inl a, Sum.inl c) (phiR P Q R G * detR P Q R h ^ k)) =
      (∑ b' : Fin Q, (∑ a' : Fin P, phiR P Q R (pderiv (a', b) (pderiv (a, b') G)) *
          X (Sum.inl a', Sum.inl c)) * X (Sum.inr b', Sum.inl c)) * detR P Q R h ^ k
        + phiR P Q R (pderiv (a, b) G) * detR P Q R h ^ k
        + ∑ a' : Fin P, phiR P Q R (pderiv (a', b) G) *
          (X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k)) := by
  classical
  have hw : pderiv (Sum.inr b, Sum.inl c) (∑ b' : Fin Q, phiR P Q R (pderiv (a, b') G) *
      X (Sum.inr b', Sum.inl c)) = (∑ b' : Fin Q, (∑ a' : Fin P, phiR P Q R (pderiv (a', b) (pderiv (a, b') G)) *
          X (Sum.inl a', Sum.inl c)) * X (Sum.inr b', Sum.inl c)) + phiR P Q R (pderiv (a, b) G) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Derivation.leibniz, pderiv_w_phiR, pderiv_X, smul_eq_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun b' _ => by ring
    · simp only [Pi.single_apply, Prod.mk.injEq, Sum.inr.injEq, and_true, mul_ite, mul_one, mul_zero]
      simp
  rw [Derivation.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, Derivation.leibniz, Derivation.leibniz,
    pderiv_s_phiR, hw, pderiv_w_phiR, pderiv_w_s_detR_pow, pderiv_w_detR_pow]
  simp only [smul_eq_mul, mul_zero, add_zero]
  rw [Finset.mul_sum, Finset.sum_congr rfl fun a' _ => (by ring :
    pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k) * (phiR P Q R (pderiv (a', b) G) * X (Sum.inl a', Sum.inl c)) =
      phiR P Q R (pderiv (a', b) G) * (X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k)))]
  ring

theorem opR_down (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    opR P Q R k (Sum.inr b) (Sum.inl a) G =
      -(∑ a' : Fin P, ∑ b' : Fin Q, X (a', b') * pderiv (a', b) (pderiv (a, b') G)
        + ((R + k : ℕ) : ℂ) • pderiv (a, b) G) := by
  simp [opR, LinearMap.sum_apply, Module.End.mul_apply]

theorem sum_A (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    ∑ c : Fin R, (∑ b' : Fin Q, (∑ a' : Fin P, phiR P Q R (pderiv (a', b) (pderiv (a, b') G)) *
          X (Sum.inl a', Sum.inl c)) * X (Sum.inr b', Sum.inl c)) * detR P Q R h ^ k =
      (∑ a' : Fin P, ∑ b' : Fin Q, mR P Q R a' b' * phiR P Q R (pderiv (a', b) (pderiv (a, b') G))) *
        detR P Q R h ^ k := by
  rw [← Finset.sum_mul]
  congr 1
  simp only [mR, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext b'; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem sum_C (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    ∑ c : Fin R, ∑ a' : Fin P, phiR P Q R (pderiv (a', b) G) *
        (X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k)) =
      phiR P Q R (pderiv (a, b) G) * ((k : Pol P Q R 0) * detR P Q R h ^ k) := by
  classical
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_s_pderiv_detR_pow, mul_ite, mul_zero]
  simp

theorem embR_eq' (h : P ≤ R) (k : ℕ) (G : Mdl P Q) :
    embR P Q R h k G = phiR P Q R G * detR P Q R h ^ k := embR_eq h k G

end GlobalTheory.CharPair.Down

namespace GlobalTheory.CharPair


open GlobalTheory.CharPair.Down in
theorem fockAct1_embR_inr_inl (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    fockAct1 P Q R 0 (Eab (Sum.inr b) (Sum.inl a)) (embR P Q R h k G) =
      embR P Q R h k (opR P Q R k (Sum.inr b) (Sum.inl a) G) := by
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rw [embR_eq', embR_eq', opR_down]
  simp only [omE_down, partial_derivative_weight_space_formula, Finset.sum_neg_distrib, Finset.sum_add_distrib, sum_A, sum_C,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_neg, map_add (f := _), map_sum, map_mul, map_smul, phiR, aeval_X]
  rw [nsmul_eq_mul, Algebra.smul_def, map_natCast]
  push_cast
  ring

end GlobalTheory.CharPair
end
end

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.RealLift.Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem hasExp_div (τ : ∀ w : InfinitePlace F, EmbOver E w) {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (fun w => m w - m' w) := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : piInf (τ w) (z : AE F E) / (‖piInf (τ w) (z : AE F E)‖ : ℂ) ≠ 0 := by
    have h0 : piInf (τ w) (z : AE F E) ≠ 0 := by
      intro e
      have := congrArg (piInf (τ w)) z.mul_inv
      rw [map_mul, e, zero_mul, map_one] at this
      exact zero_ne_one this
    exact div_ne_zero h0 (by exact_mod_cast norm_ne_zero_iff.2 h0)
  rw [zpow_sub₀ this]

section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

theorem map_atPl (p : ∀ i, V i →ₗ[ℂ] W i) (w : ι) (L : Module.End ℂ (V w)) (L' : Module.End ℂ (W w))
    (h : p w ∘ₗ L = L' ∘ₗ p w) : PiTensorProduct.map p ∘ₗ atPl w L = atPl w L' ∘ₗ PiTensorProduct.map p := by
  unfold atPl
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  congr 1
  funext i
  by_cases hi : i = w
  · subst hi; simp [h]
  · simp [Function.update_of_ne hi]

theorem map_sumPl (p : ∀ i, V i →ₗ[ℂ] W i) (L : ∀ i, Module.End ℂ (V i)) (L' : ∀ i, Module.End ℂ (W i))
    (h : ∀ i, p i ∘ₗ L i = L' i ∘ₗ p i) : PiTensorProduct.map p ∘ₗ sumPl L = sumPl L' ∘ₗ PiTensorProduct.map p := by
  apply LinearMap.ext; intro x
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sumPl, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun (map_atPl p i (L i) (L' i) (h i)) x

end Tensor

theorem i_locfin : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)), (∀ i, GlobalTheory.RealLift.LocFin (L i)) → GlobalTheory.RealLift.LocFin (GlobalTheory.RealLift.sumPl L) := GlobalTheory.T.isLocallyFinite_piTensorSumOfFactorOperators

theorem i_expact : ∀ (F : Type) [Field F] [NumberField F] (κ V : Type) [Fintype κ] [AddCommGroup V] [Module ℂ V] (Φ : V →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (L : Module.End ℂ V) (om : Multiplicative ℝ →* Module.End ℂ ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)), GlobalTheory.RealLift.LocFin L → (∀ t, ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, l ∘ₗ om t ∈ (GlobalTheory.WeilM.adeleClass F).adm κ) → (∀ T, GlobalTheory.RealLift.SD (fun t => om (Multiplicative.ofAdd t)) (Φ T) (Φ (L T))) → ∃ U : Module.End ℂ V, GlobalTheory.RealLift.IsExp L U ∧ ∀ T, GlobalTheory.RealLift.SA (om (Multiplicative.ofAdd 1)) (Φ T) (Φ (U T)) := GlobalTheory.T.weakExponential_action_on_fockVectors

theorem i_actslaws : GlobalTheory.RealLift.ActsLaws := GlobalTheory.T.archActionReadings_compatible

theorem i_derex : GlobalTheory.RealLift.DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist

theorem i_fockex : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives

theorem i_vacline : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives

theorem i_polrange : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws

theorem i_genex : GlobalTheory.RealLift.GenEx := GlobalTheory.T.oneParamSubgroup_generators_exist

theorem i_lineex : GlobalTheory.RealLift.LineEx := GlobalTheory.T.unitaryLieElements_generate_oneParamLines

theorem i_kline : GlobalTheory.RealLift.LineEx → GlobalTheory.RealLift.KLine := GlobalTheory.T.maximalCompact_oneParameterLines_of_lieLines

theorem i_liescalar : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar := GlobalTheory.T.lieScalar_of_prints_derEx_vacLine

theorem i_liesecond : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar → GlobalTheory.RealLift.LieSecond := GlobalTheory.T.lieSecond_of_prints_derEx_fockEx_vacLine_lieScalar

theorem i_liefirst : GlobalTheory.RealLift.LieSecond → GlobalTheory.RealLift.LieFirst := GlobalTheory.T.lieFirst_of_lieSecond'

theorem i_frameex : GlobalTheory.RealLift.FrameEx := GlobalTheory.T.cartanEigen_orthonormalFrame_exists

theorem i_parity : GlobalTheory.RealLift.Parity := GlobalTheory.T.realLift_parity

section Helpers

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

theorem atPl_eq (w : ι) (L : Module.End ℂ (V w)) :
    atPl w L = PiTensorProduct.mapMultilinear ℂ V V (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L) := rfl

theorem atPl_add (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L + L') = atPl w L + atPl w L' := by
  simp only [atPl_eq, MultilinearMap.map_update_add]

theorem atPl_smul (w : ι) (c : ℂ) (L : Module.End ℂ (V w)) : atPl w (c • L) = c • atPl w L := by
  simp only [atPl_eq, MultilinearMap.map_update_smul, RingHom.id_apply]

theorem atPl_one (w : ι) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  rw [atPl_eq, show Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w 1 = fun i => LinearMap.id by
    funext i; by_cases h : i = w
    · subst h; simp; rfl
    · simp [Function.update_of_ne h]]
  exact PiTensorProduct.map_id

theorem atPl_zero (w : ι) : atPl w (0 : Module.End ℂ (V w)) = 0 := by
  simp only [atPl_eq, MultilinearMap.map_update_zero]

end Helpers

section Exp

variable {V V' Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup Z] [Module ℂ Z]

theorem pow_comm {q : V →ₗ[ℂ] Z} {L : Module.End ℂ V} {L0 : Module.End ℂ Z} (h : q ∘ₗ L = L0 ∘ₗ q) (n : ℕ) (v : V) :
    q ((L ^ n) v) = (L0 ^ n) (q v) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih, ← LinearMap.comp_apply, h,
      LinearMap.comp_apply]

theorem exp_equiv {q : V →ₗ[ℂ] Z} {q' : V' →ₗ[ℂ] Z} {L U : Module.End ℂ V} {L' U' : Module.End ℂ V'} {L0 : Module.End ℂ Z}
    (hU : IsExp L U) (hU' : IsExp L' U') (h : q ∘ₗ L = L0 ∘ₗ q) (h' : q' ∘ₗ L' = L0 ∘ₗ q') {v : V} {v' : V'}
    (e : q v = q' v') : q (U v) = q' (U' v') := by
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (q (U v) - q' (U' v'))).1 fun l => ?_)
  rw [map_sub, sub_eq_zero]
  have a := hU v (l ∘ₗ q)
  have b := hU' v' (l ∘ₗ q')
  simp only [LinearMap.comp_apply, pow_comm h, pow_comm h', e] at a b
  exact a.unique b

end Exp

theorem locFin_fock1 (P Q R S : ℕ) (X : Mat P Q) (hX : IsKC X) (c : ℂ) :
    LocFin (fockAct1 P Q R S X + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).1 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs X hX y hy) (W.smul_mem c hy)⟩

theorem locFin_fock2 (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩

section Side

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
  (N : InfinitePlace F → GKMod R S) (p : ∀ w, Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] (N w).V)
  (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] Tens F P Q R S)

include Φ in
theorem pol_eq (hrange : LinearMap.range Φ = M.Pol B.ψ B.emb) {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol B.ψ B.emb) :
    ∃ T, f = Φ T := by
  rw [← hrange] at hf
  obtain ⟨T, rfl⟩ := hf
  exact ⟨T, rfl⟩

end Side

section SideW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
  (N : InfinitePlace F → GKMod R S) (p : ∀ w, Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] (N w).V)
  (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] Tens F P Q R S)

end SideW

theorem zero_mem_upq (R S : ℕ) : (0 : Mat R S) ∈ upq R S := by simp [upq]

end GlobalTheory.RealLift.Main
