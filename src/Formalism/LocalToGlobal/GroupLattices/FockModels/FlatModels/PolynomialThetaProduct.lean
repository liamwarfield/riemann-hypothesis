module

public import Formalism.LocalToGlobal.GroupLattices.FockModels.ElementaryDivisorBasis
public import Formalism.SharpRestriction.GrowthBounds.ObjSeg

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.LetterB
section -- merged from Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.Letter
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

def genM (R : Type) [CommRing R] (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :=
  Matrix.of fun a s => X (a, s)

def Nv (R : Type) [CommRing R] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  if vec then X (c, 0) else (genM R m).adjugate (Fin.last m) c

def theta (R : Type) [CommRing R] (m : ℕ) (vec : Bool) :
    MvPolynomial (Fin (m + 1)) R →ₐ[R] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  aeval (Nv R m vec)

def act {R : Type} [CommRing R] {m : ℕ} (vec : Bool) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  if vec then g else g.adjugate.transpose

theorem genM_map_rowAct (R : Type) [CommRing R] (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    (genM R m).map (rowAct R g) = (g.map C) * genM R m := by
  ext a s
  simp only [Matrix.map_apply, genM, Matrix.of_apply, Matrix.mul_apply, rowAct, MvPolynomial.aeval_X]

theorem rowAct_Nv (R : Type) [CommRing R] (m : ℕ) (vec : Bool) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (c : Fin (m + 1)) :
    rowAct R g (Nv R m vec c) = ∑ b, C (act vec g c b) * Nv R m vec b := by
  cases vec with
  | true =>
    simp only [Nv, act, ↓reduceIte, rowAct, MvPolynomial.aeval_X]
  | false =>
    simp only [Nv, act, Bool.false_eq_true, ↓reduceIte]
    have h1 : (rowAct R g) ((genM R m).adjugate (Fin.last m) c) =
        ((genM R m).map (rowAct R g)).adjugate (Fin.last m) c :=
      congrFun (congrFun (RingHom.map_adjugate (rowAct R g).toRingHom (genM R m)) (Fin.last m)) c
    have h2 := RingHom.map_adjugate (MvPolynomial.C : R →+* MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) g
    simp only [RingHom.mapMatrix_apply] at h2
    rw [h1, genM_map_rowAct, Matrix.adjugate_mul_distrib, Matrix.mul_apply, ← h2]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.map_apply, Matrix.transpose_apply, mul_comm]

def lin {R : Type} [CommRing R] {k : ℕ} (M : Matrix (Fin k) (Fin k) R) :
    MvPolynomial (Fin k) R →ₐ[R] MvPolynomial (Fin k) R :=
  aeval fun c => ∑ b, C (M c b) * X b

theorem rowAct_theta (R : Type) [CommRing R] (m : ℕ) (vec : Bool) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (P : MvPolynomial (Fin (m + 1)) R) :
    rowAct R g (theta R m vec P) = theta R m vec (lin (act vec g) P) := by
  have h : (rowAct R g).comp (theta R m vec) = (theta R m vec).comp (lin (act vec g)) := by
    apply MvPolynomial.algHom_ext
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, theta, lin, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq]
    exact rowAct_Nv R m vec g c
  exact AlgHom.congr_fun h P

def psiM (R : Type) [CommRing R] (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1)) R) :=
  Matrix.of fun a s => (if a = s then X (Fin.last m) else 0) - (if a = Fin.last m ∧ s ≠ Fin.last m then X s else 0)

theorem psiM_apply (R : Type) [CommRing R] (m : ℕ) (a s : Fin (m + 1)) : psiM R m a s =
    (if a = s then X (Fin.last m) else 0) - (if a = Fin.last m ∧ s ≠ Fin.last m then X s else 0) := rfl

def psi (R : Type) [CommRing R] (m : ℕ) (vec : Bool) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) R →ₐ[R] MvPolynomial (Fin (m + 1)) R :=
  aeval fun v => if vec then (if v.2 = 0 then X v.1 else 0) else psiM R m v.1 v.2

def qf (R : Type) [CommRing R] (m : ℕ) (vec : Bool) : MvPolynomial (Fin (m + 1)) R :=
  if vec then 1 else X (Fin.last m) ^ (m - 1)

theorem psiM_det (R : Type) [CommRing R] (m : ℕ) : (psiM R m).det = X (Fin.last m) ^ (m + 1) := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [psiM_apply, Finset.prod_const]
  · intro i j h
    have hij : i < j := OrderDual.toDual_lt_toDual.mp h
    have h1 : i ≠ j := ne_of_lt hij
    have h2 : i ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le hij (Fin.le_last j))
    simp [psiM_apply, h1, h2]

theorem psi_Nv (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (hm : 1 ≤ m) (vec : Bool) (c : Fin (m + 1)) :
    psi R m vec (Nv R m vec c) = qf R m vec * X c := by
  cases vec with
  | true => simp [psi, Nv, qf]
  | false =>
    simp only [Nv, qf, Bool.false_eq_true, ↓reduceIte]
    have hmap : (genM R m).map (psi R m false) = psiM R m := by
      ext a s
      simp [genM, psi]
    have h1 : (psi R m false) ((genM R m).adjugate (Fin.last m) c) =
        ((genM R m).map (psi R m false)).adjugate (Fin.last m) c :=
      congrFun (congrFun (RingHom.map_adjugate (psi R m false).toRingHom (genM R m)) (Fin.last m)) c
    rw [h1, hmap]
    have ht : (X (Fin.last m) : MvPolynomial (Fin (m + 1)) R) ≠ 0 := MvPolynomial.X_ne_zero _
    have hrow : ∀ s, ∑ a, (psiM R m).adjugate (Fin.last m) a * psiM R m a s =
        if Fin.last m = s then X (Fin.last m) ^ (m + 1) else 0 := by
      intro s
      have k := congrFun (congrFun (Matrix.adjugate_mul (psiM R m)) (Fin.last m)) s
      rw [Matrix.mul_apply, psiM_det] at k
      rw [k, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    have hsum : ∀ s, ∑ a, (psiM R m).adjugate (Fin.last m) a * psiM R m a s =
        (psiM R m).adjugate (Fin.last m) s * X (Fin.last m) -
          (if s ≠ Fin.last m then (psiM R m).adjugate (Fin.last m) (Fin.last m) * X s else 0) := by
      intro s
      simp only [psiM_apply, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
      congr 1
      by_cases hs : s = Fin.last m
      · simp [hs]
      · simp [hs]
    have hlast : (psiM R m).adjugate (Fin.last m) (Fin.last m) = X (Fin.last m) ^ m := by
      have e := (hsum (Fin.last m)).symm.trans (hrow (Fin.last m))
      simp only [ne_eq, not_true_eq_false, ↓reduceIte, sub_zero] at e
      apply mul_right_cancel₀ ht
      rw [e, pow_succ]
    by_cases hc : c = Fin.last m
    · subst hc
      rw [hlast, ← pow_succ]
      congr 1
      omega
    · have e := (hsum c).symm.trans (hrow c)
      have hc' : Fin.last m ≠ c := Ne.symm hc
      simp only [hc, hc', ne_eq, not_false_eq_true, ↓reduceIte] at e
      rw [hlast, sub_eq_zero] at e
      apply mul_right_cancel₀ ht
      rw [e]
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring

end Formalism.L2.G.Model
end
end

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

def Hd (R : Type) [CommRing R] (k d : ℕ) : Submodule R (MvPolynomial (Fin k) R) :=
  restrictSupport R {μ | ∑ c, μ c = d}

theorem mem_Hd {R : Type} [CommRing R] {k d : ℕ} {P : MvPolynomial (Fin k) R} :
    P ∈ Hd R k d ↔ ∀ μ ∈ P.support, ∑ c, μ c = d := by
  simp only [Hd, MvPolynomial.mem_restrictSupport_iff, Set.subset_def, Finset.mem_coe, Set.mem_setOf_eq]

theorem Hd_one (R : Type) [CommRing R] (k : ℕ) : (1 : MvPolynomial (Fin k) R) ∈ Hd R k 0 := by
  rw [mem_Hd]
  intro μ hμ
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hμ
  split_ifs at hμ with h0
  · subst h0
    simp
  · exact absurd rfl hμ

theorem Hd_X (R : Type) [CommRing R] (k : ℕ) (a : R) (c : Fin k) : C a * X c ∈ Hd R k 1 := by
  rw [mem_Hd]
  intro μ hμ
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X'] at hμ
  split_ifs at hμ with h0
  · subst h0
    simp [Finsupp.single_apply]
  · simp at hμ

theorem Hd_mul {R : Type} [CommRing R] {k a b : ℕ} {P Q : MvPolynomial (Fin k) R} (hP : P ∈ Hd R k a)
    (hQ : Q ∈ Hd R k b) : P * Q ∈ Hd R k (a + b) := by
  classical
  rw [mem_Hd] at hP hQ ⊢
  intro μ hμ
  obtain ⟨a1, ha1, b1, hb1, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul P Q hμ)
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, hP a1 ha1, hQ b1 hb1]

theorem Hd_prod {R : Type} [CommRing R] {k : ℕ} {J : Type} (s : Finset J) (δ : J → ℕ)
    (q : J → MvPolynomial (Fin k) R) (h : ∀ i ∈ s, q i ∈ Hd R k (δ i)) :
    ∏ i ∈ s, q i ∈ Hd R k (∑ i ∈ s, δ i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty, Finset.sum_empty]
    exact Hd_one R k
  · intro j s hj ih h
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact Hd_mul (h j (Finset.mem_insert_self j s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

def nuL (m d : ℕ) (vec : Bool) : Fin (m + 1) → ℕ :=
  fun t => if vec then (if t = 0 then d else 0) else (if t = Fin.last m then 0 else d)

theorem nuOf_letterWt (m : ℕ) (hm : 1 ≤ m) (d : ℕ) (vec : Bool) : nuOf (letterWt m d vec) = nuL m d vec := by
  funext t
  unfold nuOf letterWt nuL
  have hl : (Fin.last m : Fin (m + 1)) ≠ 0 := by
    intro h
    have h2 := congrArg Fin.val h
    simp at h2
    omega
  cases vec
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases ht : t = Fin.last m
    · subst ht
      simp
    · simp [ht]
  · simp only [↓reduceIte]
    by_cases ht : t = 0
    · subst ht
      simp [hl]
    · simp [ht, hl]

theorem nuL_smul (m d : ℕ) (vec : Bool) : nuL m d vec = d • nuL m 1 vec := by
  funext t
  cases vec <;> simp [nuL] <;> split_ifs <;> simp

def s0 (m : ℕ) (vec : Bool) : ℕ := if vec then 1 else m

theorem Nv_false_eq (R : Type) [CommRing R] (m : ℕ) (c : Fin (m + 1)) :
    Nv R m false c = (-1) ^ ((c : ℕ) + m) * initMinor R c.succAbove (Nat.le_succ m) := by
  unfold Nv
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.val_last, Fin.succAbove_last]
  unfold initMinor genM
  rfl

theorem Nv_true_eq (R : Type) [CommRing R] (m : ℕ) (c : Fin (m + 1)) :
    Nv R m true c = initMinor R (fun _ : Fin 1 => c) (Nat.succ_le_succ (Nat.zero_le m)) := by
  rw [lcminor_initMinor_eq, Fintype.sum_subsingleton _ 1]
  simp [Nv, MvPolynomial.X]

theorem Nv_mem (R : Type) [CommRing R] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    Nv R m vec c ∈ dualWeyl R (m + 1) (m + 1) (nuL m 1 vec) := by
  cases vec
  · rw [Nv_false_eq]
    have hmem : initMinor R c.succAbove (Nat.le_succ m) ∈ dualWeyl R (m + 1) (m + 1) (nuL m 1 false) := by
      rw [mem_dualWeyl_iff]
      refine ⟨?_, fun l j hlj => initMinor_invariant _ _ l j hlj⟩
      have e : nuL m 1 false = initW (m + 1) m := by
        funext t
        simp only [nuL, initW, Bool.false_eq_true, ↓reduceIte]
        by_cases ht : t = Fin.last m
        · subst ht
          simp
        · have h1 : (t : ℕ) < m := Fin.val_lt_last ht
          simp [ht, h1]
      rw [e]
      exact initMinor_isWeightedHomogeneous _ _
    have e2 : ((-1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) ^ ((c : ℕ) + m)) *
        initMinor R c.succAbove (Nat.le_succ m) =
        ((-1 : R) ^ ((c : ℕ) + m)) • initMinor R c.succAbove (Nat.le_succ m) := by
      rw [Algebra.smul_def]
      simp
    rw [e2]
    exact Submodule.smul_mem _ _ hmem
  · rw [Nv_true_eq, mem_dualWeyl_iff]
    refine ⟨?_, fun l j hlj => initMinor_invariant _ _ l j hlj⟩
    have e : nuL m 1 true = initW (m + 1) 1 := by
      funext t
      simp only [nuL, initW, ↓reduceIte]
      by_cases ht : t = 0
      · subst ht
        simp
      · have h1 : ¬ (t : ℕ) < 1 := by
          intro h
          apply ht
          ext
          first
            | (rw [Fin.val_zero]; omega)
            | (simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]; omega)
            | (norm_num; omega)
        simp [ht, h1]
    rw [e]
    exact initMinor_isWeightedHomogeneous _ _

theorem dw_pow {R : Type} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) R}
    (hf : f ∈ dualWeyl R r n ν) (a : ℕ) : f ^ a ∈ dualWeyl R r n (a • ν) := by
  induction a with
  | zero =>
    have e : (0 : ℕ) • ν = 0 := by
      funext t
      simp
    rw [pow_zero, e]
    exact one_mem_dualWeyl
  | succ a ih =>
    have e : (a + 1) • ν = a • ν + ν := by
      funext t
      simp [add_mul]
    rw [pow_succ, e]
    exact Formalism.GradedWeylDivisibility.dualWeyl_mul ih hf

theorem dw_prod {R : Type} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ} {J : Type} (s : Finset J)
    (f : J → MvPolynomial (Fin r × Fin n) R) (a : J → ℕ) (hf : ∀ i, f i ∈ dualWeyl R r n ν) :
    ∏ i ∈ s, f i ^ a i ∈ dualWeyl R r n ((∑ i ∈ s, a i) • ν) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · have e : (∑ i ∈ (∅ : Finset J), a i) • ν = 0 := by
      funext t
      simp
    rw [Finset.prod_empty, e]
    exact one_mem_dualWeyl
  · intro j s hj ih
    have e : (∑ i ∈ insert j s, a i) • ν = a j • ν + (∑ i ∈ s, a i) • ν := by
      funext t
      simp [Finset.sum_insert hj, add_mul]
    rw [Finset.prod_insert hj, e]
    exact Formalism.GradedWeylDivisibility.dualWeyl_mul (dw_pow (hf j) (a j)) ih

theorem theta_Hd_le (R : Type) [CommRing R] (m d : ℕ) (vec : Bool) :
    (Hd R (m + 1) d).map (theta R m vec).toLinearMap ≤ dualWeyl R (m + 1) (m + 1) (nuL m d vec) := by
  classical
  intro y hy
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.1 hy
  rw [mem_Hd] at hP
  set_option synthInstance.maxHeartbeats 100000 in
    rw [AlgHom.toLinearMap_apply, P.as_sum, map_sum]
  refine Submodule.sum_mem _ (fun μ hμ => ?_)
  unfold theta
  rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  apply Submodule.smul_mem
  have hsum : ∑ i ∈ μ.support, μ i = d := by
    rw [← hP μ hμ]
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)
  have hmem := dw_prod μ.support (fun i => Nv R m vec i) (fun i => μ i) (fun i => Nv_mem R m vec i)
  rw [hsum, ← nuL_smul] at hmem
  unfold Finsupp.prod
  exact hmem

theorem exists_succAbove {m : ℕ} (I : Fin m → Fin (m + 1)) (hI : StrictMono I) :
    ∃ c : Fin (m + 1), I = c.succAbove := by
  classical
  have hinj := hI.injective
  have hcard : (Finset.univ \ Finset.univ.image I).card = 1 := by
    first
      | rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_image_of_injective _ hinj]
      | rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_image_of_injective _ hinj]
    simp
  obtain ⟨c, hc⟩ := Finset.card_eq_one.1 hcard
  refine ⟨c, (StrictMono.range_inj hI (Fin.strictMono_succAbove c)).1 ?_⟩
  rw [Fin.range_succAbove]
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl⟩ hy
    have h1 : I y ∈ Finset.univ \ Finset.univ.image I := by
      rw [hc, hy]
      exact Finset.mem_singleton_self _
    simp at h1
  · intro hx
    by_contra hne
    have h1 : x ∈ Finset.univ \ Finset.univ.image I := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_image, true_and]
      intro hex
      apply hne
      simpa using hex
    rw [hc] at h1
    exact hx (Finset.mem_singleton.1 h1)

theorem minor_pre (R : Type) [CommRing R] (m : ℕ) (hm : 1 ≤ m) (vec : Bool) (s : ℕ) (hs : s ≤ m + 1)
    (I : Fin s → Fin (m + 1)) (hI : StrictMono I) (h : s = 0 ∨ s = s0 m vec) :
    ∃ q ∈ Hd R (m + 1) (if s = 0 then 0 else 1), theta R m vec q = initMinor R I hs := by
  rcases h with rfl | hs0
  · refine ⟨1, ?_, ?_⟩
    · simpa using Hd_one R (m + 1)
    · rw [map_one]
      unfold initMinor
      simp [Matrix.det_isEmpty]
  · cases vec
    · simp only [s0, Bool.false_eq_true, ↓reduceIte] at hs0
      subst hs0
      obtain ⟨c, rfl⟩ := exists_succAbove I hI
      refine ⟨MvPolynomial.C ((-1 : R) ^ ((c : ℕ) + s)) * X c, ?_, ?_⟩
      · rw [if_neg (by omega)]
        exact Hd_X R (s + 1) _ c
      · unfold theta
        rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Nv_false_eq, MvPolynomial.algebraMap_eq,
          ← mul_assoc, map_pow, map_neg, map_one, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]
    · simp only [s0, ↓reduceIte] at hs0
      subst hs0
      refine ⟨X (I 0), ?_, ?_⟩
      · rw [if_neg one_ne_zero]
        simpa using Hd_X R (m + 1) 1 (I 0)
      · unfold theta
        rw [MvPolynomial.aeval_X, Nv_true_eq]
        have hI2 : (fun _ : Fin 1 => I 0) = I := funext fun i => by rw [Subsingleton.elim i 0]
        rw [hI2]

theorem shape_sizes (m : ℕ) (hm : 1 ≤ m) (d : ℕ) (vec : Bool) {K : ℕ} (sz : Fin K → ℕ)
    (hshape : shapeDeg (n := m + 1) sz = nuL m d vec) :
    (∀ k, sz k = 0 ∨ sz k = s0 m vec) ∧ ∑ k, (if sz k = 0 then 0 else 1) = d := by
  classical
  have hA : ∀ t : Fin (m + 1), (Finset.univ.filter fun k : Fin K => t.val < sz k).card = nuL m d vec t := by
    intro t
    rw [← hshape]
    rfl
  have hl : (0 : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have h2 := congrArg Fin.val h
    simp at h2
    omega
  have hz : ((0 : Fin (m + 1)) : ℕ) = 0 := by simp
  have hsum : ∑ k, (if sz k = 0 then 0 else 1) = (Finset.univ.filter fun k : Fin K => ((0 : Fin (m + 1)) : ℕ) < sz k).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : sz k = 0 <;> simp [h, Nat.pos_iff_ne_zero, Fin.val_zero]
  have h0 : (Finset.univ.filter fun k : Fin K => ((0 : Fin (m + 1)) : ℕ) < sz k).card = d := by
    rw [hA 0]
    cases vec <;> simp [nuL, hl]
  refine ⟨?_, hsum.trans h0⟩
  intro k
  cases vec
  · simp only [s0, Bool.false_eq_true, ↓reduceIte]
    have hlast : (Finset.univ.filter fun k : Fin K => m < sz k).card = 0 := by
      have h1 := hA (Fin.last m)
      simpa [nuL] using h1
    have hle : sz k ≤ m := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hlast
      exact not_lt.1 (hlast (Finset.mem_univ k))
    have hne : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
      intro h
      have h2 := congrArg Fin.val h
      simp at h2
      omega
    have hm1 : (Finset.univ.filter fun k : Fin K => m - 1 < sz k).card = d := by
      have h1 := hA ⟨m - 1, by omega⟩
      simpa [nuL, hne] using h1
    have hsub : (Finset.univ.filter fun k : Fin K => m - 1 < sz k) ⊆
        (Finset.univ.filter fun k : Fin K => ((0 : Fin (m + 1)) : ℕ) < sz k) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      omega
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [h0, hm1])
    by_cases hk : sz k = 0
    · left
      exact hk
    · right
      have hk0 : k ∈ Finset.univ.filter fun k : Fin K => ((0 : Fin (m + 1)) : ℕ) < sz k := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [← heq] at hk0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk0
      omega
  · simp only [s0, ↓reduceIte]
    have hne : (⟨1, by omega⟩ : Fin (m + 1)) ≠ 0 := by
      intro h
      have h2 := congrArg Fin.val h
      simp at h2
    have h1 : (Finset.univ.filter fun k : Fin K => 1 < sz k).card = 0 := by
      have h3 := hA ⟨1, by omega⟩
      simpa [nuL, hne] using h3
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
    have h4 := h1 (Finset.mem_univ k)
    omega

theorem theta_Hd (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (hm : 1 ≤ m) (d : ℕ) (vec : Bool) :
    (Hd R (m + 1) d).map (theta R m vec).toLinearMap = dualWeyl R (m + 1) (m + 1) (nuL m d vec) := by
  apply le_antisymm (theta_Hd_le R m d vec)
  obtain ⟨b, hb, h2⟩ := sSBasis R (m + 1) (m + 1) (nuL m d vec)
  rw [← hb.2.1, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨-, -, K, sz, hsz, I, hshape, hI, hbi⟩ := h2 i
  obtain ⟨hs1, hs2⟩ := shape_sizes m hm d vec sz hshape
  have hq := fun k => minor_pre R m hm vec (sz k) (hsz k) (I k) (hI k) (hs1 k)
  choose q hq1 hq2 using hq
  refine ⟨∏ k, q k, ?_, ?_⟩
  · rw [← hs2]
    exact Hd_prod Finset.univ _ q fun k _ => hq1 k
  · show theta R m vec (∏ k, q k) = b i
    rw [map_prod, hbi]
    unfold bideterminant
    exact Finset.prod_congr rfl fun k _ => hq2 k

end Formalism.L2.G.Model
end
end

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

theorem lin_comp {R : Type} [CommRing R] {k : ℕ} (M N : Matrix (Fin k) (Fin k) R) (P : MvPolynomial (Fin k) R) :
    lin M (lin N P) = lin (N * M) P := by
  simp only [lin]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  apply congrArg (fun F : MvPolynomial (Fin k) R →ₐ[R] MvPolynomial (Fin k) R => F P)
  congr 1
  funext i
  simp only [map_sum, map_mul, aeval_C, aeval_X,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, MvPolynomial.algebraMap_eq]

theorem lin_one {R : Type} [CommRing R] {k : ℕ} (P : MvPolynomial (Fin k) R) : lin (1 : Matrix (Fin k) (Fin k) R) P = P := by
  simp [lin, Matrix.one_apply]

theorem mono_eq {R : Type} [CommRing R] {σ : Type} [Fintype σ] (μ : σ →₀ ℕ) :
    (monomial μ (1 : R)) = ∏ v, X v ^ μ v := by
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod_fintype]
  intro i
  exact pow_zero _

theorem scaleHd {R : Type} [CommRing R] {k d : ℕ} (q : MvPolynomial (Fin k) R) (P : MvPolynomial (Fin k) R)
    (hP : P ∈ Hd R k d) : aeval (fun c => q * X c) P = q ^ d * P := by
  classical
  simp only [Hd, MvPolynomial.mem_restrictSupport_iff] at hP
  conv_lhs => rw [MvPolynomial.as_sum P]
  conv_rhs => rw [MvPolynomial.as_sum P]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hd : ∑ c, μ c = d := hP hμ
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), MvPolynomial.algebraMap_eq]
  ring

theorem lin_smul {R : Type} [CommRing R] {k d : ℕ} (a : R) (M : Matrix (Fin k) (Fin k) R)
    (P : MvPolynomial (Fin k) R) (hP : P ∈ Hd R k d) : lin (a • M) P = a ^ d • lin M P := by
  classical
  simp only [Hd, MvPolynomial.mem_restrictSupport_iff] at hP
  simp only [lin]
  conv_lhs => rw [MvPolynomial.as_sum P]
  conv_rhs => rw [MvPolynomial.as_sum P]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hd : ∑ c, μ c = d := hP hμ
  have e : ∀ c, (∑ b, C ((a • M) c b) * X b : MvPolynomial (Fin k) R) = C a * ∑ b, C (M c b) * X b := by
    intro c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, MvPolynomial.C_mul, mul_assoc]
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [e, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_pow]
  ring

theorem lin_Hd {R : Type} [CommRing R] {k d : ℕ} (M : Matrix (Fin k) (Fin k) R)
    (P : MvPolynomial (Fin k) R) (hP : P ∈ Hd R k d) : lin M P ∈ Hd R k d := by
  unfold Hd at hP
  rw [restrictSupport_eq_span] at hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, hμ, rfl⟩ := hx
    have hμ' : ∑ c, μ c = d := hμ
    beta_reduce
    rw [mono_eq, map_prod, ← hμ']
    apply Hd_prod
    intro c _
    rw [map_pow]
    have h1 : lin M (X c) ∈ Hd R k 1 := by
      simp only [lin, aeval_X]
      exact Submodule.sum_mem _ fun b _ => Hd_X R k _ b
    have h2 := Hd_prod (Finset.range (μ c)) (fun _ => 1) (fun _ => lin M (X c)) (fun _ _ => h1)
    simpa using h2
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem map_Nv {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    map f (Nv R m vec c) = Nv R' m vec c := by
  simp only [Nv]
  cases vec
  · simp only [Bool.false_eq_true, if_false]
    have h1 : (MvPolynomial.map f).mapMatrix (genM R m) = genM R' m := by
      ext i j
      simp [genM]
    rw [← h1, ← RingHom.map_adjugate]
    rfl
  · simp

theorem map_theta {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (m : ℕ) (vec : Bool)
    (P : MvPolynomial (Fin (m + 1)) R) : map f (theta R m vec P) = theta R' m vec (map f P) := by
  simp only [theta, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq]
  rw [MvPolynomial.map_eval₂]
  congr 2
  funext c
  exact map_Nv f m vec c

theorem map_Hd {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {k d : ℕ}
    (P : MvPolynomial (Fin k) R) (hP : P ∈ Hd R k d) : map f P ∈ Hd R' k d := by
  simp only [Hd, MvPolynomial.mem_restrictSupport_iff] at hP ⊢
  exact (Finset.coe_subset.mpr (MvPolynomial.support_map_subset f P)).trans hP

section Multi

variable {S : Type} [Fintype S] [DecidableEq S]

def embS (R : Type) [CommRing R] {k : ℕ} (s : S) : MvPolynomial (Fin k) R →ₐ[R] MvPolynomial (S × Fin k) R :=
  rename fun c => (s, c)

def Th0 (R : Type) [CommRing R] (m : ℕ) (vec : S → Bool) :
    MvPolynomial (S × Fin (m + 1)) R →ₐ[R] MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) R :=
  aeval fun v => blockEmb R v.1 (Nv R m (vec v.1) v.2)

theorem Th0_emb (R : Type) [CommRing R] (m : ℕ) (vec : S → Bool) (s : S) (P : MvPolynomial (Fin (m + 1)) R) :
    Th0 R m vec (embS R s P) = blockEmb R s (theta R m (vec s) P) := by
  simp only [Th0, embS, MvPolynomial.aeval_rename, theta]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

def Lin {R : Type} [CommRing R] {k : ℕ} (N : S → Matrix (Fin k) (Fin k) R) :
    MvPolynomial (S × Fin k) R →ₐ[R] MvPolynomial (S × Fin k) R :=
  aeval fun v => ∑ b, C (N v.1 v.2 b) * X (v.1, b)

theorem Lin_emb {R : Type} [CommRing R] {k : ℕ} (N : S → Matrix (Fin k) (Fin k) R) (s : S)
    (P : MvPolynomial (Fin k) R) : Lin N (embS R s P) = embS R s (lin (N s) P) := by
  simp only [Lin, embS, lin, MvPolynomial.aeval_rename]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  apply congrArg (fun F : MvPolynomial (Fin k) R →ₐ[R] MvPolynomial (S × Fin k) R => F P)
  congr 1
  funext c
  simp [Function.comp]

theorem Lin_comp {R : Type} [CommRing R] {k : ℕ} (M N : S → Matrix (Fin k) (Fin k) R)
    (P : MvPolynomial (S × Fin k) R) : Lin M (Lin N P) = Lin (fun s => N s * M s) P := by
  simp only [Lin]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  apply congrArg (fun F : MvPolynomial (S × Fin k) R →ₐ[R] MvPolynomial (S × Fin k) R => F P)
  congr 1
  funext i
  simp only [map_sum, map_mul, aeval_C, aeval_X,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, MvPolynomial.algebraMap_eq]

theorem Lin_one {R : Type} [CommRing R] {k : ℕ} (P : MvPolynomial (S × Fin k) R) :
    Lin (fun _ : S => (1 : Matrix (Fin k) (Fin k) R)) P = P := by
  simp [Lin, Matrix.one_apply]

theorem mem_Pol {R : Type} [CommRing R] {k : ℕ} {d : S → ℕ} {F : MvPolynomial (S × Fin k) R} :
    F ∈ Pol R k d ↔ ∀ μ ∈ F.support, ∀ i, multideg μ i = d i := by
  exact Iff.rfl

theorem Pol_one (R : Type) [CommRing R] (k : ℕ) : (1 : MvPolynomial (S × Fin k) R) ∈ Pol R k (0 : S → ℕ) := by
  rw [mem_Pol]
  intro μ hμ i
  classical
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hμ
  split_ifs at hμ with h
  · subst h
    simp [multideg]
  · exact absurd rfl hμ

theorem Pol_mul {R : Type} [CommRing R] {k : ℕ} {a b : S → ℕ} {P Q : MvPolynomial (S × Fin k) R}
    (hP : P ∈ Pol R k a) (hQ : Q ∈ Pol R k b) : P * Q ∈ Pol R k (a + b) := by
  rw [mem_Pol] at hP hQ ⊢
  intro μ hμ i
  classical
  obtain ⟨a', ha, b', hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hμ)
  have e1 := hP a' ha i
  have e2 := hQ b' hb i
  simp only [multideg] at e1 e2 ⊢
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, e1, e2]

theorem Pol_prod {R : Type} [CommRing R] {k : ℕ} {J : Type} (s : Finset J) (δ : J → S → ℕ)
    (q : J → MvPolynomial (S × Fin k) R) (h : ∀ i ∈ s, q i ∈ Pol R k (δ i)) :
    ∏ i ∈ s, q i ∈ Pol R k (∑ i ∈ s, δ i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using (Pol_one (S := S) R k)
  · intro j s hj ih h
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact Pol_mul (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem emb_Pol {R : Type} [CommRing R] {k a : ℕ} (s : S) (P : MvPolynomial (Fin k) R) (hP : P ∈ Hd R k a) :
    embS R s P ∈ Pol R k (Pi.single s a : S → ℕ) := by
  rw [mem_Pol]
  intro μ hμ i
  have hinj : Function.Injective fun c : Fin k => (s, c) := fun a b h => (Prod.mk.inj h).2
  simp only [embS] at hμ
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hμ
  obtain ⟨ν, hν, rfl⟩ := hμ
  simp only [Hd, MvPolynomial.mem_restrictSupport_iff] at hP
  have hd : ∑ c, ν c = a := hP hν
  simp only [multideg]
  by_cases hi : i = s
  · subst hi
    simp only [Pi.single_eq_same]
    rw [← hd]
    exact Finset.sum_congr rfl fun c _ => Finsupp.mapDomain_apply_of_injective hinj ν c
  · rw [Pi.single_eq_of_ne hi]
    exact Finset.sum_eq_zero fun c _ => Finsupp.mapDomain_notin_range _ _
      (by rintro ⟨c', hc'⟩; exact hi (congrArg Prod.fst hc').symm)

theorem prod_emb_Pol {R : Type} [CommRing R] {k : ℕ} (d : S → ℕ) (P : S → MvPolynomial (Fin k) R)
    (hP : ∀ s, P s ∈ Hd R k (d s)) : ∏ s, embS R s (P s) ∈ Pol R k d := by
  have := Pol_prod Finset.univ (fun s => (Pi.single s (d s) : S → ℕ)) (fun s => embS R s (P s))
    (fun s _ => emb_Pol s (P s) (hP s))
  rwa [Finset.univ_sum_single] at this

def partS {k : ℕ} (μ : S × Fin k →₀ ℕ) (s : S) : Fin k →₀ ℕ := Finsupp.equivFunOnFinite.symm fun c => μ (s, c)

theorem mono_factor (R : Type) [CommRing R] {k : ℕ} (μ : S × Fin k →₀ ℕ) :
    (monomial μ (1 : R)) = ∏ s, embS R s (monomial (partS μ s) 1) := by
  rw [mono_eq, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [mono_eq, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  simp [embS, partS]

theorem partS_Hd (R : Type) [CommRing R] {k : ℕ} (d : S → ℕ) (μ : S × Fin k →₀ ℕ) (hμ : ∀ i, multideg μ i = d i)
    (s : S) : (monomial (partS μ s) (1 : R)) ∈ Hd R k (d s) := by
  classical
  simp only [Hd, MvPolynomial.mem_restrictSupport_iff]
  intro ν hν
  have := MvPolynomial.support_monomial_subset hν
  rw [Finset.mem_singleton] at this
  subst this
  show ∑ c, partS μ s c = d s
  rw [← hμ s]
  simp [partS, multideg]

theorem scalePol {R : Type} [CommRing R] {k : ℕ} {d : S → ℕ} (Q : S → MvPolynomial (S × Fin k) R)
    (F : MvPolynomial (S × Fin k) R) (hF : F ∈ Pol R k d) :
    aeval (fun v : S × Fin k => Q v.1 * X v) F = (∏ s, Q s ^ d s) * F := by
  classical
  rw [mem_Pol] at hF
  conv_lhs => rw [MvPolynomial.as_sum F]
  conv_rhs => rw [MvPolynomial.as_sum F]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hd : ∀ s, ∑ c, μ (s, c) = d s := fun s => hF μ hμ s
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), MvPolynomial.algebraMap_eq]
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Fintype.prod_prod_type (fun v => Q v.1 ^ μ v)]
  simp only [Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem Lin_Pol {R : Type} [CommRing R] {k : ℕ} {d : S → ℕ} (N : S → Matrix (Fin k) (Fin k) R)
    (F : MvPolynomial (S × Fin k) R) (hF : F ∈ Pol R k d) : Lin N F ∈ Pol R k d := by
  unfold Pol at hF
  rw [restrictSupport_eq_span] at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, hμ, rfl⟩ := hx
    beta_reduce
    rw [mono_factor, map_prod]
    simp only [Lin_emb]
    exact prod_emb_Pol d _ fun s => lin_Hd _ _ (partS_Hd R d μ hμ s)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem Lin_smul {R : Type} [CommRing R] {k : ℕ} {d : S → ℕ} (a : S → R) (M : S → Matrix (Fin k) (Fin k) R)
    (F : MvPolynomial (S × Fin k) R) (hF : F ∈ Pol R k d) :
    Lin (fun s => a s • M s) F = (∏ s, a s ^ d s) • Lin M F := by
  classical
  rw [mem_Pol] at hF
  simp only [Lin]
  conv_lhs => rw [MvPolynomial.as_sum F]
  conv_rhs => rw [MvPolynomial.as_sum F]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hd : ∀ s, ∑ c, μ (s, c) = d s := fun s => hF μ hμ s
  have e : ∀ v : S × Fin k, (∑ b, C ((a v.1 • M v.1) v.2 b) * X (v.1, b) : MvPolynomial (S × Fin k) R) =
      C (a v.1) * ∑ b, C (M v.1 v.2 b) * X (v.1, b) := by
    intro v
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, MvPolynomial.C_mul, mul_assoc]
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [e, mul_pow, Finset.prod_mul_distrib]
  rw [Fintype.prod_prod_type (fun v => C (a v.1) ^ μ v)]
  simp only [Finset.prod_pow_eq_pow_sum, hd]
  rw [MvPolynomial.smul_eq_C_mul, map_prod]
  simp only [MvPolynomial.C_pow]
  ring

def Ps0 (R : Type) [CommRing R] (m : ℕ) (vec : S → Bool) :
    MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) R →ₐ[R] MvPolynomial (S × Fin (m + 1)) R :=
  aeval fun v => embS R v.1 (psi R m (vec v.1) (X v.2))

theorem Ps0_block (R : Type) [CommRing R] (m : ℕ) (vec : S → Bool) (s : S)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :
    Ps0 R m vec (blockEmb R s F) = embS R s (psi R m (vec s) F) := by
  simp only [Ps0, blockEmb, MvPolynomial.aeval_rename]
  rw [← AlgHom.comp_apply, MvPolynomial.aeval_unique ((embS R s).comp (psi R m (vec s)))]
  rfl

theorem polynomial_theta_product (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (hm : 1 ≤ m) (vec : S → Bool) (d : S → ℕ)
    (F : MvPolynomial (S × Fin (m + 1)) R) (hF : F ∈ Pol R (m + 1) d) :
    Ps0 R m vec (Th0 R m vec F) = (∏ s, (embS R s (qf R m (vec s))) ^ d s) * F := by
  have h1 : (Ps0 R m vec).comp (Th0 R m vec) =
      aeval fun v : S × Fin (m + 1) => embS R v.1 (qf R m (vec v.1)) * X v := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, Th0, aeval_X, Ps0_block, psi_Nv R m hm, map_mul]
    simp [embS]
  rw [← scalePol _ _ hF, ← h1]
  rfl

theorem qf_ne (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (vec : Bool) : qf R m vec ≠ 0 := by
  simp only [qf]
  cases vec <;> simp [MvPolynomial.X_ne_zero]

theorem Th0_inj (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (hm : 1 ≤ m) (vec : S → Bool) (d : S → ℕ)
    (F G : MvPolynomial (S × Fin (m + 1)) R) (hF : F ∈ Pol R (m + 1) d) (hG : G ∈ Pol R (m + 1) d)
    (h : Th0 R m vec F = Th0 R m vec G) : F = G := by
  have h1 := polynomial_theta_product R m hm vec d F hF
  have h2 := polynomial_theta_product R m hm vec d G hG
  rw [h, h2] at h1
  refine (mul_left_cancel₀ ?_ h1).symm
  apply Finset.prod_ne_zero_iff.2
  intro s _
  apply pow_ne_zero
  intro h0
  apply qf_ne R m (vec s)
  have hinj : Function.Injective (fun c : Fin (m + 1) => (s, c)) := fun a b h => (Prod.mk.inj h).2
  exact rename_injective _ hinj (by rw [map_zero]; exact h0)

end Multi

end Formalism.L2.G.Model
