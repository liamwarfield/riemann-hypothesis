module

public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.EqEmptyIffSplit
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LatticeCountingFormula

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.WedgeSplitTan
noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

open B2

section Split

variable {r K : ℕ} {P : Type*} [CommRing P]

lemma wedge_split_tan (x : Fin (r + K) → P) (hx : ∀ a : Fin r, x (Fin.castAdd K a) = 0)
    (pl : Finset (Fin r) → P) (tn : Finset (Fin K) → P) (J : Finset (Fin (r + K))) :
    wedgeR x (fun J => pl (Jp J) * tn (Jt J)) J = pl (Jp J) * wedgeR (fun b => x (Fin.natAdd r b)) tn (Jt J) := by
  unfold wedgeR
  rw [sum_split, Finset.sum_eq_zero (fun a _ => by rw [hx]; simp), zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  beta_reduce
  rw [Jp_erase_na, Jt_erase_na, card_filter_na]; ring

lemma contr_split_tan (x : Fin (r + K) → P) (hx : ∀ a : Fin r, x (Fin.castAdd K a) = 0)
    (pl : Finset (Fin r) → P) (tn : Finset (Fin K) → P) (J : Finset (Fin (r + K))) :
    contrR x (fun J => pl (Jp J) * tn (Jt J)) J = pl (Jp J) * contrR (fun b => x (Fin.natAdd r b)) tn (Jt J) := by
  unfold contrR
  rw [sum_split, Finset.sum_eq_zero (fun a _ => by rw [hx]; simp), zero_add, Finset.mul_sum, Jt_compl]
  refine Finset.sum_congr rfl fun b _ => ?_
  beta_reduce
  rw [Jp_insert_na, Jt_insert_na, card_filter_na]; ring

lemma wedge_split_pl (x : Fin (r + K) → P) (hx : ∀ b : Fin K, x (Fin.natAdd r b) = 0)
    (pl : Finset (Fin r) → P) (tn : Finset (Fin K) → P) (htn : ∀ J'', J'' ≠ ∅ → tn J'' = 0)
    (J : Finset (Fin (r + K))) :
    wedgeR x (fun J => pl (Jp J) * tn (Jt J)) J = wedgeR (fun a => x (Fin.castAdd K a)) pl (Jp J) * tn (Jt J) := by
  unfold wedgeR
  rw [sum_split, Finset.sum_eq_zero (s := Jt J) (fun a _ => by rw [hx]; simp), add_zero, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  beta_reduce
  rw [Jp_erase_ca, Jt_erase_ca, card_filter_ca]
  by_cases h : Jt J = ∅
  · rw [h]; simp only [Finset.card_empty, add_zero]; ring
  · rw [htn _ h]; simp

lemma contr_split_pl (x : Fin (r + K) → P) (hx : ∀ b : Fin K, x (Fin.natAdd r b) = 0)
    (pl : Finset (Fin r) → P) (tn : Finset (Fin K) → P) (htn : ∀ J'', J'' ≠ ∅ → tn J'' = 0)
    (J : Finset (Fin (r + K))) :
    contrR x (fun J => pl (Jp J) * tn (Jt J)) J = contrR (fun a => x (Fin.castAdd K a)) pl (Jp J) * tn (Jt J) := by
  unfold contrR
  rw [sum_split, Finset.sum_eq_zero (s := Jt (univ \ J)) (fun a _ => by rw [hx]; simp), add_zero, Finset.sum_mul,
    Jp_compl]
  refine Finset.sum_congr rfl fun a _ => ?_
  beta_reduce
  rw [Jp_insert_ca, Jt_insert_ca, card_filter_ca]
  by_cases h : Jt J = ∅
  · rw [h]; simp only [Finset.card_empty, add_zero]; ring
  · rw [htn _ h]; simp

end Split

section S2

variable {N r K : ℕ} (R : Type) [CommRing R]

def PLc (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (j : ℕ) (J' : Finset (Fin r)) :
    MvPolynomial (Fin N × Fin (r + K)) R := rename (plVar (K := K)) (Kcol R (plPart mu) c j J')

def TNc (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (j : ℕ) (J'' : Finset (Fin K)) :
    MvPolynomial (Fin N × Fin (r + K)) R := rename (tanVar (r := r)) (Kcol R (tanPart mu) c j J'')

lemma PLc_succ (mu : Fin (N + 1) → Fin (r + K) → ℤ) (hdom : ∀ i, Dominant (mu i)) (c : ℤ) (j : ℕ) (h : j < N) :
    PLc R mu c (j + 1) = colStep c (min (colH (mu ⟨j, by omega⟩) c) r) (min (colH (mu ⟨j + 1, by omega⟩) c) r)
      (fun a => X (⟨j, h⟩, Fin.castAdd K a)) (PLc R mu c j) := by
  funext J'
  unfold PLc
  simp only [Kcol, dif_pos h]
  have := colStep_map (rename (plVar (K := K)) : MvPolynomial (Fin N × Fin r) R →ₐ[R] _).toRingHom c
    (colH (plPart mu ⟨j, by omega⟩) c) (colH (plPart mu ⟨j + 1, by omega⟩) c) (letVec R ⟨j, h⟩)
    (Kcol R (plPart mu) c j) J'
  refine this.trans ?_
  have e1 : colH (plPart mu ⟨j, by omega⟩) c = min (colH (mu ⟨j, by omega⟩) c) r := colH_pl (hdom _) c
  have e2 : colH (plPart mu ⟨j + 1, by omega⟩) c = min (colH (mu ⟨j + 1, by omega⟩) c) r := colH_pl (hdom _) c
  rw [e1, e2]
  congr 1
  funext a; simp [letVec, plVar]

lemma TNc_succ (mu : Fin (N + 1) → Fin (r + K) → ℤ) (hdom : ∀ i, Dominant (mu i)) (c : ℤ) (j : ℕ) (h : j < N) :
    TNc R mu c (j + 1) = colStep c (colH (mu ⟨j, by omega⟩) c - r) (colH (mu ⟨j + 1, by omega⟩) c - r)
      (fun b => X (⟨j, h⟩, Fin.natAdd r b)) (TNc R mu c j) := by
  funext J'
  unfold TNc
  simp only [Kcol, dif_pos h]
  have := colStep_map (rename (tanVar (r := r)) : MvPolynomial (Fin N × Fin K) R →ₐ[R] _).toRingHom c
    (colH (tanPart mu ⟨j, by omega⟩) c) (colH (tanPart mu ⟨j + 1, by omega⟩) c) (letVec R ⟨j, h⟩)
    (Kcol R (tanPart mu) c j) J'
  refine this.trans ?_
  have e1 : colH (tanPart mu ⟨j, by omega⟩) c = colH (mu ⟨j, by omega⟩) c - r := colH_tan (hdom _) c
  have e2 : colH (tanPart mu ⟨j + 1, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c - r := colH_tan (hdom _) c
  rw [e1, e2]
  congr 1
  funext a; simp [letVec, tanVar]

lemma PLc_zero (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (J' : Finset (Fin r)) :
    PLc R mu c 0 J' = extOne J' :=
  extOne_map (rename (plVar (K := K)) : MvPolynomial (Fin N × Fin r) R →ₐ[R] _).toRingHom J'

lemma TNc_zero (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (J' : Finset (Fin K)) :
    TNc R mu c 0 J' = extOne J' :=
  extOne_map (rename (tanVar (r := r)) : MvPolynomial (Fin N × Fin K) R →ₐ[R] _).toRingHom J'

lemma colStep_same {k : ℕ} {P : Type*} [CommRing P] (c : ℤ) (a b : ℕ) (hab : a = b) (x : Fin k → P)
    (Kv : Finset (Fin k) → P) : colStep c a b x Kv = Kv := by
  subst hab; unfold colStep; simp

lemma TNc_card (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (H : ColOK LL mu c)
    (hdom : ∀ i, Dominant (mu i)) (hc : 1 ≤ c) (j : ℕ) (hj : j ≤ N) :
    ∀ J'', TNc R mu c j J'' ≠ 0 → J''.card = colH (mu ⟨j, by omega⟩) c - r := by
  classical
  induction j with
  | zero =>
    intro J hJ
    rw [TNc_zero] at hJ
    have : J = ∅ := by by_contra hne; exact hJ (by unfold extOne; rw [if_neg hne])
    rw [this, H.start hc]; simp
  | succ j ih =>
    intro J hJ
    have h : j < N := hj
    have ih' := ih (by omega)
    rw [TNc_succ R mu hdom c j h] at hJ
    unfold colStep at hJ
    split_ifs at hJ with h1 h3
    · obtain ⟨_, hN⟩ := H.rise j h (by omega)
      obtain ⟨m, hm, _, hK⟩ := wedgeR_ne _ _ _ hJ
      have := ih' _ hK
      rw [Finset.card_erase_of_mem hm] at this
      have := Finset.card_pos.mpr ⟨m, hm⟩
      omega
    · obtain ⟨_, hP⟩ := H.fall j h (by omega)
      obtain ⟨m, hm, _, hK⟩ := contrR_ne _ _ _ hJ
      have := ih' _ hK
      rw [Finset.card_insert_of_notMem hm] at this
      omega
    · have := ih' _ hJ; omega

lemma condUS_vec (LL : LiftLetters (Fin N)) (i : Fin N) (m : Fin (r + K)) (hv : LL.vec i = true) :
    condUS LL i m ↔ r ≤ m.val := by unfold condUS; simp [hv]

lemma condUS_cov (LL : LiftLetters (Fin N)) (i : Fin N) (m : Fin (r + K)) (hv : LL.vec i = false) :
    condUS LL i m ↔ m.val < r := by unfold condUS; simp [hv]

lemma nomL_X (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (i : Fin N) (m : Fin (r + K))
    (h : condUS LL i m ↔ IsCostly mu c i) : nomL R LL mu c i m = X (i, m) := by
  unfold nomL; rw [if_pos h]

lemma nomL_0 (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (i : Fin N) (m : Fin (r + K))
    (h : ¬ (condUS LL i m ↔ IsCostly mu c i)) : nomL R LL mu c i m = 0 := by
  unfold nomL; rw [if_neg h]

theorem SgW_eq (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (H : ColOK LL mu c)
    (hdom : ∀ i, Dominant (mu i)) (j : ℕ) (hj : j ≤ N) :
    SgW R LL mu c j = fun J => PLc R mu c j (Jp J) * TNc R mu c j (Jt J) := by
  classical
  induction j with
  | zero =>
    funext J
    simp only [SgW, PLc_zero, TNc_zero]
    unfold extOne
    by_cases hJ : J = ∅
    · subst hJ; simp [Jp, Jt]
    · rw [if_neg hJ]
      have := (eq_empty_iff_split J).not.mp hJ
      by_cases h1 : Jp J = ∅
      · rw [if_neg (fun h2 => this ⟨h1, h2⟩)]; simp
      · rw [if_neg h1]; simp
  | succ j ih =>
    have h : j < N := hj
    have ih' := ih (by omega)
    funext J
    simp only [SgW, dif_pos h]
    rw [ih', PLc_succ R mu hdom c j h, TNc_succ R mu hdom c j h]
    have hci := costly_iff mu c j h
    have hca : ∀ a : Fin r, (Fin.castAdd K a).val < r := fun a => by simp
    have hna : ∀ b : Fin K, r ≤ (Fin.natAdd r b).val := fun b => by simp
    have htn0 : 1 ≤ c → colH (mu ⟨j, by omega⟩) c ≤ r → ∀ J'', J'' ≠ ∅ → TNc R mu c j J'' = 0 := by
      intro hc hr J'' hne
      by_contra hh
      have := TNc_card R LL mu c H hdom hc j (by omega) J'' hh
      exact hne (Finset.card_eq_zero.mp (by omega))
    by_cases h1 : colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c
    · obtain ⟨hv, hN⟩ := H.rise j h h1
      have cc : IsCostly mu c ⟨j, h⟩ ↔ r ≤ colH (mu ⟨j, by omega⟩) c := by
        rw [hci]; constructor
        · rintro (⟨_, x⟩ | ⟨x, _⟩) <;> omega
        · intro x; exact Or.inl ⟨h1, x⟩
      by_cases hc : 1 ≤ c
      · by_cases hr : r ≤ colH (mu ⟨j, by omega⟩) c
        · rw [colStep_same c _ _ (by omega) _ (PLc R mu c j)]
          simp only [colStep, if_pos h1, if_pos hc,
            if_pos (show colH (mu ⟨j, by omega⟩) c - r < colH (mu ⟨j + 1, by omega⟩) c - r by omega)]
          rw [wedge_split_tan _ (fun a => nomL_0 R LL mu c _ _ (by
            rw [condUS_vec LL _ _ hv, cc]; have := hca a; intro e; have := e.mpr hr; omega))]
          congr 2
          funext b
          exact nomL_X R LL mu c _ _ (by rw [condUS_vec LL _ _ hv, cc]; exact iff_of_true (hna b) hr)
        · rw [colStep_same c _ _ (by omega) _ (TNc R mu c j)]
          simp only [colStep, if_pos h1, if_pos hc,
            if_pos (show min (colH (mu ⟨j, by omega⟩) c) r < min (colH (mu ⟨j + 1, by omega⟩) c) r by omega)]
          rw [wedge_split_pl _ (fun b => nomL_0 R LL mu c _ _ (by
            rw [condUS_vec LL _ _ hv, cc]; intro e; exact hr (e.mp (hna b)))) _ _ (htn0 hc (by omega))]
          congr 2
          funext a
          exact nomL_X R LL mu c _ _ (by
            rw [condUS_vec LL _ _ hv, cc]; exact iff_of_false (by have := hca a; omega) hr)
      · have hd := H.dual hc j (by omega)
        rw [colStep_same c _ _ (by omega) _ (PLc R mu c j)]
        simp only [colStep, if_pos h1, if_neg hc,
          if_pos (show colH (mu ⟨j, by omega⟩) c - r < colH (mu ⟨j + 1, by omega⟩) c - r by omega)]
        rw [contr_split_tan _ (fun a => nomL_0 R LL mu c _ _ (by
          rw [condUS_vec LL _ _ hv, cc]; have := hca a; intro e; have := e.mpr (by omega); omega))]
        congr 2
        funext b
        exact nomL_X R LL mu c _ _ (by rw [condUS_vec LL _ _ hv, cc]; exact iff_of_true (hna b) (by omega))
    · by_cases h3 : colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c
      · obtain ⟨hv, hP⟩ := H.fall j h h3
        have cc : IsCostly mu c ⟨j, h⟩ ↔ colH (mu ⟨j, by omega⟩) c ≤ r := by
          rw [hci]; constructor
          · rintro (⟨x, _⟩ | ⟨_, x⟩) <;> omega
          · intro x; exact Or.inr ⟨h3, x⟩
        by_cases hc : 1 ≤ c
        · by_cases hr : colH (mu ⟨j, by omega⟩) c ≤ r
          · rw [colStep_same c _ _ (by omega) _ (TNc R mu c j)]
            simp only [colStep, if_neg h1, if_pos h3, if_pos hc,
              if_neg (show ¬ min (colH (mu ⟨j, by omega⟩) c) r < min (colH (mu ⟨j + 1, by omega⟩) c) r by omega),
              if_pos (show min (colH (mu ⟨j + 1, by omega⟩) c) r < min (colH (mu ⟨j, by omega⟩) c) r by omega)]
            rw [contr_split_pl _ (fun b => nomL_0 R LL mu c _ _ (by
              rw [condUS_cov LL _ _ hv, cc]; have := hna b; intro e; have := e.mpr hr; omega)) _ _ (htn0 hc hr)]
            congr 2
            funext a
            exact nomL_X R LL mu c _ _ (by rw [condUS_cov LL _ _ hv, cc]; exact iff_of_true (hca a) hr)
          · rw [colStep_same c _ _ (by omega) _ (PLc R mu c j)]
            simp only [colStep, if_neg h1, if_pos h3, if_pos hc,
              if_neg (show ¬ colH (mu ⟨j, by omega⟩) c - r < colH (mu ⟨j + 1, by omega⟩) c - r by omega),
              if_pos (show colH (mu ⟨j + 1, by omega⟩) c - r < colH (mu ⟨j, by omega⟩) c - r by omega)]
            rw [contr_split_tan _ (fun a => nomL_0 R LL mu c _ _ (by
              rw [condUS_cov LL _ _ hv, cc]; intro e; exact hr (e.mp (hca a))))]
            congr 2
            funext b
            exact nomL_X R LL mu c _ _ (by
              rw [condUS_cov LL _ _ hv, cc]; exact iff_of_false (by have := hna b; omega) hr)
        · have hd := H.dual hc j (by omega)
          have hd' := H.dual hc (j + 1) (by omega)
          rw [colStep_same c _ _ (by omega) _ (PLc R mu c j)]
          simp only [colStep, if_neg h1, if_pos h3, if_neg hc,
            if_neg (show ¬ colH (mu ⟨j, by omega⟩) c - r < colH (mu ⟨j + 1, by omega⟩) c - r by omega),
            if_pos (show colH (mu ⟨j + 1, by omega⟩) c - r < colH (mu ⟨j, by omega⟩) c - r by omega)]
          rw [wedge_split_tan _ (fun a => nomL_0 R LL mu c _ _ (by
            rw [condUS_cov LL _ _ hv, cc]; intro e; have := e.mp (hca a); omega))]
          congr 2
          funext b
          exact nomL_X R LL mu c _ _ (by
            rw [condUS_cov LL _ _ hv, cc]; exact iff_of_false (by have := hna b; omega) (by omega))
      · have e : colH (mu ⟨j, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c := by omega
        rw [colStep_same c _ _ e, colStep_same c _ _ (by rw [e]), colStep_same c _ _ (by rw [e])]

theorem plTanCol_eq_SgW (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (H : ColOK LL mu c)
    (hdom : ∀ i, Dominant (mu i)) (J : Finset (Fin (r + K))) : plTanCol R mu c J = SgW R LL mu c N J := by
  rw [SgW_eq R LL mu c H hdom N le_rfl]; rfl

end S2

end Formalism.MainNotions.LemmaBAlt
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftedColumnMultidegree
noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section Deg

variable {R : Type*} [CommRing R] {N k : ℕ}

def HomD (d : Fin N → ℕ) (F : MvPolynomial (Fin N × Fin k) R) : Prop :=
  ∀ m ∈ F.support, ∀ i, multideg m i = d i

lemma HomD.zero (d : Fin N → ℕ) : HomD d (0 : MvPolynomial (Fin N × Fin k) R) := by
  intro m hm
  simp at hm

lemma HomD.add {d : Fin N → ℕ} {F G : MvPolynomial (Fin N × Fin k) R} (hF : HomD d F) (hG : HomD d G) :
    HomD d (F + G) := by
  intro m hm i
  rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
  · exact hF m h i
  · exact hG m h i

lemma HomD.sum {ι' : Type*} {d : Fin N → ℕ} (s : Finset ι') (F : ι' → MvPolynomial (Fin N × Fin k) R)
    (h : ∀ a ∈ s, HomD d (F a)) : HomD d (∑ a ∈ s, F a) := by
  exact Finset.sum_induction F (HomD d) (fun a b ha hb => ha.add hb) (HomD.zero d) h

lemma multideg_add (a b : Fin N × Fin k →₀ ℕ) (i : Fin N) : multideg (a + b) i = multideg a i + multideg b i := by
  simp only [multideg, Finsupp.add_apply, Finset.sum_add_distrib]

lemma HomD.mul {d d' : Fin N → ℕ} {F G : MvPolynomial (Fin N × Fin k) R} (hF : HomD d F) (hG : HomD d' G) :
    HomD (d + d') (F * G) := by
  intro m hm i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul F G hm)
  rw [multideg_add, hF a ha i, hG b hb i, Pi.add_apply]

lemma HomD.one : HomD (0 : Fin N → ℕ) (1 : MvPolynomial (Fin N × Fin k) R) := by
  intro m hm i
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
  split_ifs at hm with h
  · subst h
    simp [multideg]
  · exact absurd rfl hm

lemma HomD.pow {d : Fin N → ℕ} {F : MvPolynomial (Fin N × Fin k) R} (hF : HomD d F) (Q : ℕ) :
    HomD (Q • d) (F ^ Q) := by
  induction Q with
  | zero => rw [pow_zero, zero_smul]; exact HomD.one
  | succ n ih => rw [pow_succ, succ_nsmul]; exact ih.mul hF

lemma HomD.sign {d : Fin N → ℕ} {F : MvPolynomial (Fin N × Fin k) R} (hF : HomD d F) (n : ℕ) :
    HomD d ((-1) ^ n * F) := by
  have h1 : HomD (0 : Fin N → ℕ) (-1 : MvPolynomial (Fin N × Fin k) R) := by
    intro m hm
    rw [MvPolynomial.support_neg] at hm
    exact HomD.one m hm
  have h2 := (h1.pow n).mul hF
  rwa [smul_zero, zero_add] at h2

def eI (i : Fin N) : Fin N → ℕ := fun i' => if i' = i then 1 else 0

lemma colStep_HomD (c : ℤ) (hP hN : ℕ) (hne : hP ≠ hN) (i : Fin N) (d : Fin N → ℕ)
    (x : Fin k → MvPolynomial (Fin N × Fin k) R) (Kv : Finset (Fin k) → MvPolynomial (Fin N × Fin k) R)
    (hx : ∀ b, HomD (eI i) (x b)) (hK : ∀ J, HomD d (Kv J)) (J : Finset (Fin k)) :
    HomD (eI i + d) (colStep c hP hN x Kv J) := by
  have hw : HomD (eI i + d) (wedgeR x Kv J) := by
    unfold wedgeR
    exact HomD.sum _ _ fun m _ => ((hx m).sign _).mul (hK _)
  have hc : HomD (eI i + d) (contrR x Kv J) := by
    unfold contrR
    exact HomD.sum _ _ fun m _ => ((hx m).sign _).mul (hK _)
  unfold colStep
  split_ifs
  all_goals first | exact hw | exact hc | exact (hne (by omega)).elim


open Classical in
def dgS (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (j : ℕ) (s : ℤ) : Fin N → ℕ :=
  fun i => if i.val < j ∧ IsUsed mu c i then p ^ (s - pos i).toNat else 0

private theorem pow_toNat_mul_pow_toNat_eq_of_le (p : ℕ) {u v w : ℤ} (h1 : u ≤ v) (h2 : v ≤ w) :
    p ^ (w - v).toNat * p ^ (v - u).toNat = p ^ (w - u).toNat := by
  rw [← pow_add]
  congr 1
  omega

private theorem dgS_eq_zero_of_none_used (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (j : ℕ) (s : ℤ)
    (h : ∀ i : Fin N, i.val < j → ¬ IsUsed mu c i) : dgS p pos mu c j s = 0 := by
  funext i
  simp only [dgS, Pi.zero_apply]
  rw [if_neg]
  rintro ⟨h1, h2⟩
  exact h i h1 h2

private theorem dgS_succ_eq_of_not_used (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (j : ℕ) (hj : j < N)
    (hu : ¬ IsUsed mu c ⟨j, hj⟩) (s : ℤ) : dgS p pos mu c (j + 1) s = dgS p pos mu c j s := by
  funext i
  simp only [dgS]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso
    apply h2
    refine ⟨?_, h1.2⟩
    by_cases h : i.val < j
    · exact h
    · have e : i = ⟨j, hj⟩ := Fin.ext (show i.val = j by have := h1.1; omega)
      subst e
      exact absurd h1.2 hu
  · exfalso
    exact h1 ⟨Nat.lt_succ_of_lt h2.1, h2.2⟩
  · rfl

private theorem eI_eq_dgS_succ_of_first_used (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (j : ℕ) (hj : j < N)
    (hu : IsUsed mu c ⟨j, hj⟩) (h : ∀ i : Fin N, i.val < j → ¬ IsUsed mu c i) :
    eI ⟨j, hj⟩ + 1 • (0 : Fin N → ℕ) = dgS p pos mu c (j + 1) (pos ⟨j, hj⟩) := by
  funext i
  simp only [Pi.add_apply, smul_zero, Pi.zero_apply, add_zero, eI, dgS]
  by_cases hij : i.val = j
  · have e : i = ⟨j, hj⟩ := Fin.ext hij
    subst e
    simp [hu]
  · have hne : i ≠ ⟨j, hj⟩ := fun e => hij (by rw [e])
    rw [if_neg hne, if_neg]
    rintro ⟨h1, h2⟩
    exact h i (by omega) h2

private theorem eI_add_pow_smul_dgS_eq_dgS_succ_of_used (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (j : ℕ) (hj : j < N)
    (sl : ℤ) (hu : IsUsed mu c ⟨j, hj⟩) (hsl : sl ≤ pos ⟨j, hj⟩)
    (hle : ∀ i : Fin N, i.val < j → IsUsed mu c i → pos i ≤ sl) :
    eI ⟨j, hj⟩ + p ^ (pos ⟨j, hj⟩ - sl).toNat • dgS p pos mu c j sl = dgS p pos mu c (j + 1) (pos ⟨j, hj⟩) := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, eI, dgS]
  by_cases hij : i.val = j
  · have e : i = ⟨j, hj⟩ := Fin.ext hij
    subst e
    simp [hu]
  · have hne : i ≠ ⟨j, hj⟩ := fun e => hij (by rw [e])
    rw [if_neg hne, zero_add]
    by_cases hU : IsUsed mu c i
    · by_cases hlt : i.val < j
      · rw [if_pos ⟨hlt, hU⟩, if_pos ⟨by omega, hU⟩]
        exact pow_toNat_mul_pow_toNat_eq_of_le p (hle i hlt hU) hsl
      · rw [if_neg (fun h => hlt h.1), if_neg (fun h => by have := h.1; omega)]
        simp
    · rw [if_neg (fun h => hU h.2), if_neg (fun h => hU h.2)]
      simp

private theorem pow_smul_dgS_eq_dgS_of_le (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (j : ℕ) (s sl : ℤ)
    (hsl : sl ≤ s) (hle : ∀ i : Fin N, i.val < j → IsUsed mu c i → pos i ≤ sl) :
    p ^ (s - sl).toNat • dgS p pos mu c j sl = dgS p pos mu c j s := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, dgS]
  split_ifs with h
  · exact pow_toNat_mul_pow_toNat_eq_of_le p (hle i h.1 h.2) hsl
  · simp

private theorem homD_KKs_and_slot_properties (p : ℕ) (x : Fin N → Fin k → MvPolynomial (Fin N × Fin k) R) (pos : Fin N → ℤ)
    (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (hmono : Monotone pos) (hx : ∀ i b, HomD (eI i) (x i b)) (j : ℕ) :
    j ≤ N →
      ((KKs p x pos mu c j).2 = none →
        (∀ i : Fin N, i.val < j → ¬ IsUsed mu c i) ∧ ∀ J, HomD 0 ((KKs p x pos mu c j).1 J)) ∧
      (∀ sl, (KKs p x pos mu c j).2 = some sl →
        (∃ i₀ : Fin N, i₀.val < j ∧ IsUsed mu c i₀ ∧ pos i₀ = sl) ∧
        (∀ i : Fin N, i.val < j → IsUsed mu c i → pos i ≤ sl) ∧
        ∀ J, HomD (dgS p pos mu c j sl) ((KKs p x pos mu c j).1 J)) := by
  induction j with
  | zero =>
    intro _
    refine ⟨fun _ => ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun J => ?_⟩, fun sl hsl => ?_⟩
    · simp only [KKs, extOne]
      split_ifs
      · exact HomD.one
      · exact HomD.zero _
    · simp [KKs] at hsl
  | succ j ih =>
    intro hj
    have hjN : j < N := hj
    obtain ⟨ihN, ihS⟩ := ih (Nat.le_of_lt hjN)
    have hmax : ∀ i : Fin N, i.val < j + 1 → pos i ≤ pos ⟨j, hjN⟩ :=
      fun i hi => hmono (Fin.le_iff_val_le_val.2 (Nat.lt_succ_iff.1 hi))
    by_cases heq : colH (mu ⟨j, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c
    · have hu : ¬ IsUsed mu c ⟨j, hjN⟩ := fun h => h heq
      have hK : KKs p x pos mu c (j + 1) = KKs p x pos mu c j := by
        simp only [KKs, dif_pos hjN, if_pos heq]
      rw [hK]
      refine ⟨fun hn => ?_, fun sl hs => ?_⟩
      · obtain ⟨h1, h2⟩ := ihN hn
        refine ⟨fun i hi hU => ?_, h2⟩
        by_cases hij : i.val = j
        · have e : i = ⟨j, hjN⟩ := Fin.ext hij
          subst e
          exact hu hU
        · exact h1 i (by omega) hU
      · obtain ⟨⟨i₀, hi₀, hU₀, he₀⟩, h2, h3⟩ := ihS sl hs
        refine ⟨⟨i₀, by omega, hU₀, he₀⟩, fun i hi hU => ?_, ?_⟩
        · by_cases hij : i.val = j
          · have e : i = ⟨j, hjN⟩ := Fin.ext hij
            subst e
            exact absurd hU hu
          · exact h2 i (by omega) hU
        · intro J
          rw [dgS_succ_eq_of_not_used p pos mu c j hjN hu sl]
          exact h3 J
    · have hu : IsUsed mu c ⟨j, hjN⟩ := heq
      cases hst : (KKs p x pos mu c j).2 with
      | none =>
        obtain ⟨h1, h2⟩ := ihN hst
        have hK : KKs p x pos mu c (j + 1) =
            (colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (x ⟨j, hjN⟩)
              (powC 1 (KKs p x pos mu c j).1), some (pos ⟨j, hjN⟩)) := by
          simp only [KKs, dif_pos hjN, if_neg heq, hst]
        rw [hK]
        refine ⟨fun hn => by simp at hn, fun sl hs => ?_⟩
        simp at hs
        subst hs
        refine ⟨⟨⟨j, hjN⟩, by simp, hu, rfl⟩, fun i hi _ => hmax i hi, fun J => ?_⟩
        rw [← eI_eq_dgS_succ_of_first_used p pos mu c j hjN hu h1]
        exact colStep_HomD c _ _ heq ⟨j, hjN⟩ _ _ _ (hx ⟨j, hjN⟩) (fun J => (h2 J).pow 1) J
      | some sl0 =>
        obtain ⟨⟨i₀, hi₀, hU₀, he₀⟩, h2, h3⟩ := ihS sl0 hst
        have hK : KKs p x pos mu c (j + 1) =
            (colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (x ⟨j, hjN⟩)
              (powC (p ^ (pos ⟨j, hjN⟩ - sl0).toNat) (KKs p x pos mu c j).1), some (pos ⟨j, hjN⟩)) := by
          simp only [KKs, dif_pos hjN, if_neg heq, hst]
        rw [hK]
        refine ⟨fun hn => by simp at hn, fun sl hs => ?_⟩
        simp at hs
        subst hs
        have hsl : sl0 ≤ pos ⟨j, hjN⟩ := by rw [← he₀]; exact hmax i₀ (by omega)
        refine ⟨⟨⟨j, hjN⟩, by simp, hu, rfl⟩, fun i hi _ => hmax i hi, fun J => ?_⟩
        rw [← eI_add_pow_smul_dgS_eq_dgS_succ_of_used p pos mu c j hjN sl0 hu hsl h2]
        exact colStep_HomD c _ _ heq ⟨j, hjN⟩ _ _ _ (hx ⟨j, hjN⟩) (fun J => (h3 J).pow _) J

theorem ZZ_HomD (p : ℕ) (x : Fin N → Fin k → MvPolynomial (Fin N × Fin k) R) (pos : Fin N → ℤ)
    (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (hmono : Monotone pos) (hx : ∀ i b, HomD (eI i) (x i b))
    (j : ℕ) (hj : j ≤ N) :
    ∀ s : ℤ, (∀ i : Fin N, i.val < j → IsUsed mu c i → pos i ≤ s) → ∀ J,
      HomD (dgS p pos mu c j s) (ZZ p x pos mu c j s J) := by
  intro s hs J
  obtain ⟨hN', hS⟩ := homD_KKs_and_slot_properties p x pos mu c hmono hx j hj
  cases hst : (KKs p x pos mu c j).2 with
  | none =>
    obtain ⟨h1, h2⟩ := hN' hst
    have hZ : ZZ p x pos mu c j s J = (KKs p x pos mu c j).1 J := by simp only [ZZ, hst]
    rw [hZ, dgS_eq_zero_of_none_used p pos mu c j s h1]
    exact h2 J
  | some sl =>
    obtain ⟨⟨i₀, hi₀, hU₀, he₀⟩, h2, h3⟩ := hS sl hst
    have hZ : ZZ p x pos mu c j s J = powC (p ^ (s - sl).toNat) (KKs p x pos mu c j).1 J := by
      simp only [ZZ, hst]
    have hsl : sl ≤ s := by rw [← he₀]; exact hs i₀ hi₀ hU₀
    rw [hZ, ← pow_smul_dgS_eq_dgS_of_le p pos mu c j s sl hsl h2]
    exact (h3 J).pow _

end Deg

section Clause2

variable (p f : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p f) O] {N k : ℕ}

lemma XC_HomD (i : Fin N) (a : Fin k) (t : KK O) :
    HomD (eI i) (X (i, a) * C t : MvPolynomial (Fin N × Fin k) (KK O)) := by
  intro m hm i'
  rw [mul_comm, MvPolynomial.C_mul_X_eq_monomial] at hm
  have hm' := Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hm)
  subst hm'
  by_cases h : i' = i
  · subst h
    simp [multideg, eI, Finsupp.single_apply]
  · simp [multideg, eI, Finsupp.single_apply, h, Ne.symm h]

lemma letG_HomD (LL : LiftLetters (Fin N)) (g : Matrix (Fin k) (Fin k) (WF p f)) (i : Fin N) (b : Fin k) :
    HomD (eI i) (letG p f (O := O) LL g i b) := by
  unfold letG
  split_ifs
  · exact HomD.sum _ _ fun a _ => by apply XC_HomD
  · exact HomD.sum _ _ fun a _ => by apply XC_HomD

theorem lifted_column_multidegree (LL : LiftLetters (Fin N)) (g : Matrix (Fin k) (Fin k) (WF p f)) (z : ℤ)
    (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (hmono : Monotone LL.pos) (hz : ∀ i, LL.pos i ≤ z)
    (J : Finset (Fin k)) (m : Fin N × Fin k →₀ ℕ) (hm : m ∈ (KKc p f (O := O) LL g z mu c J).support) (i : Fin N)
    (hi : IsUsed mu c i) : multideg m i = p ^ (z - LL.pos i).toNat := by
  rw [KKc_eq] at hm
  have H := ZZ_HomD p (letG p f (O := O) LL g) LL.pos mu c hmono (fun i b => by apply letG_HomD) N le_rfl z
    (fun i _ _ => hz i) J m hm i
  rw [H]
  simp [dgS, i.isLt, hi]

end Clause2

end Formalism.MainNotions.LemmaBAlt
end
end

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

theorem canonical_translate_jet_identity (D : Formalism.BasicNotions.D7) : CanonicalTranslateJetIdentity D := by
  intro p f _ O _ _ _ _ S hp5 hf hsq N r K _ _ _ LL B z hK hmono hz P g hg c hpos J
  have H : ColOK LL P.mu c := colOK_of_path LL B hK P c
  refine ⟨column_kernel_components_integral p f LL g hg z P.mu c J, fun m hm i hi => lifted_column_multidegree p f LL g z P.mu c hmono hz J m hm i hi,
    fun g' hg' => lifted_column_order p f (frobCong p f hf) S hsq LL g g' hg hg' z P.mu c H hmono hz hpos J, ?_,
    column_order_le_two_power p (by omega) LL.pos z hmono hz P.mu c hpos⟩
  exact lifted_column_congruence p f S LL g hg z P.mu c hmono hz hpos (SgVanish_of LL P.mu c H)
    (fun J => plTanCol_eq_SgW O LL P.mu c H P.dom J) J

end Formalism.MainNotions.LemmaBAlt
