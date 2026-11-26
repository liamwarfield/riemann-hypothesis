module

public import GroundTheory.AutomorphicForms.HarishChandraCentre.Injective
public import GroundTheory.AutomorphicForms.HarishChandraCentre.VermaCoordEqZeroOfMemNPlusU
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EMulSubMulCapelliMatrixPow

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.HarishChandraCentre.Capelli
namespace GroundTheory.Automorphic.HarishChandra

variable {n : ℕ}

noncomputable def capelliMatrix : Matrix (Fin n) (Fin n) (U n) := fun i j => e (i, j)

noncomputable def capelli (k : ℕ) : U n := Matrix.trace (capelliMatrix ^ k)

theorem e_mul_sub_mul_capelliMatrix_pow (a b : Fin n) (k : ℕ) (c d : Fin n) :
    e (a, b) * (capelliMatrix ^ k) c d - (capelliMatrix ^ k) c d * e (a, b) =
      (if b = c then (capelliMatrix ^ k) a d else 0) -
        (if d = a then (capelliMatrix ^ k) c b else 0) :=
  _root_.UpperTheory.Reformulated.B.Qk36.e_mul_sub_mul_capelliMatrix_pow a b k c d

theorem capelli_mem_center (k : ℕ) : capelli (n := n) k ∈ Subalgebra.center ℂ (U n) := by
  apply mem_center_of_commute_e
  rintro ⟨a, b⟩
  rw [← sub_eq_zero]
  simp only [capelli, Matrix.trace, Matrix.diag]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp_rw [e_mul_sub_mul_capelliMatrix_pow]
  simp [Finset.sum_sub_distrib]

theorem capelliMatrix_pow_succ_apply (m : ℕ) (c d : Fin n) :
    (capelliMatrix ^ (m + 1)) c d = ∑ i : Fin m → Fin n,
      word (List.ofFn fun t : Fin (m + 1) => ((Fin.cons c i : Fin (m + 1) → Fin n) t,
        (Fin.snoc i d : Fin (m + 1) → Fin n) t)) := by
  induction m generalizing c with
  | zero =>
    rw [Fintype.sum_unique]
    simp [capelliMatrix, word, List.ofFn_succ, Fin.snoc]
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih, Finset.mul_sum]
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Fin n).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk]
    rw [← Fin.cons_snoc_eq_snoc_cons, List.ofFn_succ, word_cons]
    simp [capelliMatrix]

theorem capelli_eq_sum_word (k : ℕ) :
    capelli (n := n) (k + 1) = ∑ i : Fin (k + 1) → Fin n,
      word (List.ofFn fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))) := by
  rw [capelli, Matrix.trace]
  simp only [Matrix.diag, capelliMatrix_pow_succ_apply]
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin n).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.consEquiv_apply]
  congr 2
  funext t
  congr 1
  induction t using Fin.lastCases with
  | last => simp [finRotate_apply]
  | cast s => simp [finRotate_apply, Fin.coeSucc_eq_succ]

end GroundTheory.Automorphic.HarishChandra
end

section -- merged from GroundTheory.AutomorphicForms.HarishChandraCentre.LeadingTerm
namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

noncomputable abbrev polyLE (n d : ℕ) : Submodule ℂ (MvPolynomial (Fin n) ℂ) := restrictTotalDegree (Fin n) ℂ d

theorem mem_polyLE {d : ℕ} {p : MvPolynomial (Fin n) ℂ} : p ∈ polyLE n d ↔ p.totalDegree ≤ d := by
  rw [polyLE, mem_restrictTotalDegree]

theorem polyLE_mono {d d' : ℕ} (h : d ≤ d') : polyLE n d ≤ polyLE n d' :=
  fun _ hp => mem_polyLE.2 ((mem_polyLE.1 hp).trans h)

theorem sum_diagExp_le (m : Fin n × Fin n →₀ ℕ) :
    ((diagExp m).sum fun _ e => e) ≤ m.degree := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [diagExp_apply]
  exact Finset.single_le_sum (f := fun j => m (i, j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem hcProjLin_canon_mem_polyLE {d : ℕ} {m : Fin n × Fin n →₀ ℕ} (hm : m.degree ≤ d) :
    hcProjLin (canon m) ∈ polyLE n d := by
  by_cases h : IsDiagExp m
  · rw [hcProjLin_canon_of_isDiagExp h, mem_polyLE]
    exact (totalDegree_monomial_le _ _).trans ((sum_diagExp_le m).trans hm)
  · rw [hcProjLin_canon_of_not h]
    exact Submodule.zero_mem _

theorem hcProjLin_mem_polyLE {d : ℕ} {u : U n} (hu : u ∈ filt d) : hcProjLin u ∈ polyLE n d := by
  have hu' : u ∈ Submodule.span ℂ {u | ∃ m : Fin n × Fin n →₀ ℕ, (∀ a ∈ m.support, True) ∧
      0 ≤ m.degree ∧ m.degree ≤ d ∧ canon m = u} := filt_le_canonSpan d hu
  clear hu
  induction hu' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, -, -, hm, rfl⟩ := hx
    exact hcProjLin_canon_mem_polyLE hm
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

noncomputable def diagMain (w : List (Fin n × Fin n)) : MvPolynomial (Fin n) ℂ := by
  classical
  exact if ∀ a ∈ w, a.1 = a.2 then (w.map fun a => X a.1).prod else 0

theorem diagExp_add (m m' : Fin n × Fin n →₀ ℕ) : diagExp (m + m') = diagExp m + diagExp m' := by
  ext i; simp

theorem diagExp_single (i : Fin n) : diagExp (Finsupp.single (i, i) 1) = Finsupp.single i 1 := by
  ext j
  rw [diagExp_apply, Finsupp.single_apply, Finsupp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem monomial_diagExp_toFinsupp (w : List (Fin n × Fin n)) (hw : ∀ a ∈ w, a.1 = a.2) :
    monomial (diagExp (Multiset.toFinsupp (w : Multiset (Fin n × Fin n)))) (1 : ℂ) =
      (w.map fun a => X a.1).prod := by
  induction w with
  | nil =>
    have : diagExp (Multiset.toFinsupp (([] : List (Fin n × Fin n)) : Multiset (Fin n × Fin n))) = 0 := by
      ext; simp
    rw [this, monomial_zero', C_1]
    simp
  | cons a w ih =>
    rw [show ((a :: w : List _) : Multiset _) = {a} + (w : Multiset (Fin n × Fin n)) by simp,
      Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, diagExp_add,
      show a = (a.1, a.1) from Prod.ext rfl (hw a (List.mem_cons_self ..)).symm, diagExp_single,
      ← one_mul (1 : ℂ), ← monomial_mul, ih fun b hb => hw b (List.mem_cons_of_mem _ hb),
      List.map_cons, List.prod_cons, ← pow_one (X a.1), X_pow_eq_monomial]

theorem hcProjLin_word_sub_mem (w : List (Fin n × Fin n)) :
    hcProjLin (word w) - diagMain w ∈ polyLE n (w.length - 1) := by
  classical
  set M := Multiset.toFinsupp (w : Multiset (Fin n × Fin n))
  have h1 := hcProjLin_mem_polyLE (word_sub_canon_mem_filt w)
  rw [map_sub] at h1
  have h2 : hcProjLin (canon M) = diagMain w := by
    by_cases hw : ∀ a ∈ w, a.1 = a.2
    · have hd : IsDiagExp M := by
        intro a ha
        have : a ∈ w := by
          by_contra h'
          apply ha
          rw [Multiset.toFinsupp_apply]
          exact Multiset.count_eq_zero.2 (fun hm => h' (Multiset.mem_coe.1 hm))
        exact hw a this
      rw [hcProjLin_canon_of_isDiagExp hd, monomial_diagExp_toFinsupp w hw, diagMain, if_pos hw]
    · have hd : ¬ IsDiagExp M := by
        push Not at hw
        obtain ⟨a, ha, hne⟩ := hw
        intro hd
        refine hne (hd a ?_)
        rw [Multiset.toFinsupp_apply]
        exact (Multiset.count_pos.2 (Multiset.mem_coe.2 ha)).ne'
      rw [hcProjLin_canon_of_not hd, diagMain, if_neg hw]
  rwa [h2] at h1

theorem const_of_forall_rotate {k : ℕ} {i : Fin (k + 1) → Fin n}
    (h : ∀ t, i t = i (finRotate (k + 1) t)) (t : Fin (k + 1)) : i t = i 0 := by
  induction t using Fin.induction with
  | zero => rfl
  | succ t ih =>
    have := h (Fin.castSucc t)
    rw [finRotate_apply, Fin.coeSucc_eq_succ] at this
    rw [← this, ih]

theorem diagMain_capelliWord {k : ℕ} (i : Fin (k + 1) → Fin n) :
    diagMain (List.ofFn fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))) =
      ∑ c : Fin n, if i = (fun _ => c) then X c ^ (k + 1) else 0 := by
  classical
  by_cases h : ∀ t, i t = i (finRotate (k + 1) t)
  · have hc := const_of_forall_rotate h
    have hall : ∀ a ∈ List.ofFn (fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))),
        a.1 = a.2 := by
      intro a ha
      obtain ⟨t, rfl⟩ := List.mem_ofFn.1 ha
      exact h t
    rw [diagMain, if_pos hall, List.map_ofFn, List.prod_ofFn]
    rw [Finset.sum_eq_single (i 0)]
    · rw [if_pos (funext hc)]
      simp only [Function.comp_apply, hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · intro c _ hc'
      rw [if_neg]
      intro he
      exact hc' (by rw [he])
    · simp
  · have hnot : ¬ ∀ a ∈ List.ofFn (fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))),
        a.1 = a.2 := by
      intro hall
      exact h fun t => hall _ (List.mem_ofFn.2 ⟨t, rfl⟩)
    rw [diagMain, if_neg hnot]
    refine (Finset.sum_eq_zero fun c _ => ?_).symm
    rw [if_neg]
    rintro rfl
    exact h fun t => rfl

theorem sum_diagMain_capelliWord (k : ℕ) :
    ∑ i : Fin (k + 1) → Fin n,
      diagMain (List.ofFn fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))) =
        psum (Fin n) ℂ (k + 1) := by
  classical
  simp_rw [diagMain_capelliWord]
  rw [Finset.sum_comm, psum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ (fun _ => c), if_pos (Finset.mem_univ _)]

theorem hcProjLin_capelli_sub_mem (k : ℕ) :
    hcProjLin (capelli (n := n) (k + 1)) - psum (Fin n) ℂ (k + 1) ∈ polyLE n k := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [capelli_eq_sum_word, map_sum, ← sum_diagMain_capelliWord, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  have := hcProjLin_word_sub_mem (List.ofFn fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t)))
  rwa [List.length_ofFn, Nat.add_sub_cancel] at this

theorem translate_X (c : Fin n → ℂ) (i : Fin n) : translate c (X i) = X i + C (c i) := by
  simp [translate]

theorem translate_C (c : Fin n → ℂ) (a : ℂ) : translate c (C a) = C a := by
  simp [translate]

theorem mul_X_mem_polyLE {d : ℕ} {p : MvPolynomial (Fin n) ℂ} (hp : p ∈ polyLE n d) (i : Fin n) :
    p * X i ∈ polyLE n (d + 1) := by
  rw [mem_polyLE] at *
  exact (totalDegree_mul p (X i)).trans (by rw [totalDegree_X]; omega)

theorem mul_C_mem_polyLE {d : ℕ} {p : MvPolynomial (Fin n) ℂ} (hp : p ∈ polyLE n d) (a : ℂ) :
    p * C a ∈ polyLE n d := by
  rw [mem_polyLE] at *
  exact (totalDegree_mul p (C a)).trans (by rw [totalDegree_C]; omega)

theorem translate_sub_mem_polyLE (c : Fin n → ℂ) :
    ∀ (d : ℕ) (p : MvPolynomial (Fin n) ℂ), p ∈ polyLE n d → translate c p - p ∈ polyLE n (d - 1) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    rw [mem_polyLE, Nat.le_zero, totalDegree_eq_zero_iff_eq_C] at hp
    rw [hp, translate_C, sub_self]
    exact Submodule.zero_mem _
  | succ d ih =>
    intro p hp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [p.as_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun s hs => ?_
    have hsd : (s.sum fun _ e => e) ≤ d + 1 := by
      have := mem_polyLE.1 hp
      rw [totalDegree] at this
      exact (Finset.le_sup hs).trans this
    by_cases hs0 : s = 0
    · rw [hs0, monomial_zero', translate_C, sub_self]
      exact Submodule.zero_mem _
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hs0
    set s' := s - Finsupp.single i 1
    have hss : s = s' + Finsupp.single i 1 := by
      rw [tsub_add_cancel_of_le]
      intro j
      by_cases hj : j = i
      · subst hj; simp [Nat.one_le_iff_ne_zero.2 hi]
      · simp [Ne.symm hj]
    have hs'd : (s'.sum fun _ e => e) ≤ d := by
      have : (s.sum fun _ e => e) = (s'.sum fun _ e => e) + 1 := by
        rw [hss, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
          Finsupp.sum_single_index rfl]
      omega
    have hmono : monomial s (AddMonoidAlgebra.coeff p s) = monomial (s' + Finsupp.single i 1) (AddMonoidAlgebra.coeff p s) := by
      rw [← hss]
    rw [hmono, monomial_add_single, pow_one, map_mul, translate_X]
    set m' := monomial s' (AddMonoidAlgebra.coeff p s)
    have hm' : m' ∈ polyLE n d := mem_polyLE.2 ((totalDegree_monomial_le _ _).trans hs'd)
    have hT : translate c m' - m' ∈ polyLE n (d - 1) := ih m' hm'
    have hT' : translate c m' ∈ polyLE n d := by
      have := Submodule.add_mem _ (polyLE_mono (Nat.sub_le d 1) hT) hm'
      rwa [sub_add_cancel] at this
    have : translate c m' * (X i + C (c i)) - m' * X i =
        (translate c m' - m') * X i + translate c m' * C (c i) := by ring
    rw [this, Nat.add_sub_cancel]
    refine Submodule.add_mem _ ?_ (mul_C_mem_polyLE hT' _)
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      have hs'0 : s' = 0 := by
        ext j
        have : (s'.sum fun _ e => e) = 0 := Nat.le_zero.1 hs'd
        rw [Finsupp.sum, Finset.sum_eq_zero_iff] at this
        by_contra hj
        exact hj (this j (Finsupp.mem_support_iff.2 hj))
      simp only [m', hs'0, monomial_zero', translate_C, sub_self, zero_mul]
      exact Submodule.zero_mem _
    · have := mul_X_mem_polyLE hT i
      rwa [Nat.sub_add_cancel hd] at this

theorem psum_mem_polyLE (k : ℕ) : psum (Fin n) ℂ k ∈ polyLE n k := by
  rw [psum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [mem_polyLE]
  exact (totalDegree_pow _ _).trans (by rw [totalDegree_X, mul_one])

theorem totalDegree_harishChandraHom_capelli_sub (k : ℕ) :
    (harishChandraHom (⟨capelli (k + 1), capelli_mem_center _⟩ : Subalgebra.center ℂ (U n)) -
      psum (Fin n) ℂ (k + 1)).totalDegree < k + 1 := by
  rw [harishChandraHom_apply]
  set P := hcProjLin (capelli (n := n) (k + 1))
  have h1 : P - psum (Fin n) ℂ (k + 1) ∈ polyLE n k := hcProjLin_capelli_sub_mem k
  have hP : P ∈ polyLE n (k + 1) := by
    have := Submodule.add_mem _ (polyLE_mono (Nat.le_succ k) h1) (psum_mem_polyLE (k + 1))
    rwa [sub_add_cancel] at this
  have h2 := translate_sub_mem_polyLE (-rhoVec n) (k + 1) P hP
  rw [Nat.add_sub_cancel] at h2
  have : translate (-rhoVec n) P - psum (Fin n) ℂ (k + 1) =
      (translate (-rhoVec n) P - P) + (P - psum (Fin n) ℂ (k + 1)) := by ring
  rw [this]
  exact Nat.lt_succ_of_le (mem_polyLE.1 (Submodule.add_mem _ h2 h1))

end GroundTheory.Automorphic.HarishChandra
end

section -- merged from GroundTheory.AutomorphicForms.HarishChandraCentre.Symmetric
namespace GroundTheory.Automorphic.HarishChandra

open MvPolynomial Finset

variable {n : ℕ}

noncomputable abbrev psumFin (k : Fin n) : MvPolynomial (Fin n) ℂ := psum (Fin n) ℂ ((k : ℕ) + 1)

theorem esymm_mem_adjoin_psum (k : ℕ) (hk : k ≤ n) :
    esymm (Fin n) ℂ k ∈ Algebra.adjoin ℂ (Set.range (psumFin (n := n))) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  set A := Algebra.adjoin ℂ (Set.range (psumFin (n := n)))
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [esymm_zero]; exact A.one_mem
  have hps : ∀ j, 1 ≤ j → j ≤ n → psum (Fin n) ℂ j ∈ A := by
    intro j hj1 hjn
    refine Algebra.subset_adjoin ⟨⟨j - 1, by omega⟩, ?_⟩
    show psum (Fin n) ℂ (j - 1 + 1) = psum (Fin n) ℂ j
    rw [Nat.sub_add_cancel hj1]
  have hsum : (k : MvPolynomial (Fin n) ℂ) * esymm (Fin n) ℂ k ∈ A := by
    rw [mul_esymm_eq_sum]
    refine A.mul_mem (A.pow_mem (A.neg_mem A.one_mem) _) (A.sum_mem fun a ha => ?_)
    rw [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
    exact A.mul_mem (A.mul_mem (A.pow_mem (A.neg_mem A.one_mem) _) (ih a.1 ha.2 (by omega)))
      (hps a.2 (by omega) (by omega))
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have e : esymm (Fin n) ℂ k =
      (k : ℂ)⁻¹ • ((k : MvPolynomial (Fin n) ℂ) * esymm (Fin n) ℂ k) := by
    rw [← map_natCast (C : ℂ →+* MvPolynomial (Fin n) ℂ) k, smul_eq_C_mul, ← mul_assoc, ← C_mul,
      inv_mul_cancel₀ hk', C_1, one_mul]
  rw [e]
  exact A.smul_mem hsum _

theorem aeval_mem_of_forall_mem {A : Subalgebra ℂ (MvPolynomial (Fin n) ℂ)}
    (f : Fin n → MvPolynomial (Fin n) ℂ) (hf : ∀ i, f i ∈ A) (F : MvPolynomial (Fin n) ℂ) :
    aeval f F ∈ A := by
  induction F using MvPolynomial.induction_on with
  | C r => rw [aeval_C]; exact A.algebraMap_mem r
  | add p q hp hq => rw [map_add (f := _)]; exact A.add_mem hp hq
  | mul_X p i hp => rw [map_mul, aeval_X]; exact A.mul_mem hp (hf i)

theorem mem_adjoin_psum_of_isSymmetric {p : MvPolynomial (Fin n) ℂ} (hp : p.IsSymmetric) :
    p ∈ Algebra.adjoin ℂ (Set.range (psumFin (n := n))) := by
  obtain ⟨F, hF⟩ := esymmAlgHom_fin_surjective ℂ (le_refl n) ⟨p, hp⟩
  have e := congrArg Subtype.val hF
  rw [esymmAlgHom_apply] at e
  have e' : aeval (fun i : Fin n => esymm (Fin n) ℂ ((i : ℕ) + 1)) F = p := e
  rw [← e']
  exact aeval_mem_of_forall_mem _ (fun i => esymm_mem_adjoin_psum _ (by omega)) F

def TopClose (k : ℕ) (a b : MvPolynomial (Fin n) ℂ) : Prop :=
  a.totalDegree ≤ k ∧ b.totalDegree ≤ k ∧ (a = b ∨ (a - b).totalDegree < k)

theorem TopClose.one : TopClose (n := n) 0 1 1 := by
  refine ⟨by simp, by simp, Or.inl rfl⟩

theorem TopClose.mul {k l : ℕ} {a b a' b' : MvPolynomial (Fin n) ℂ} (h : TopClose k a b)
    (h' : TopClose l a' b') : TopClose (k + l) (a * a') (b * b') := by
  obtain ⟨ha, hb, hab⟩ := h
  obtain ⟨ha', hb', hab'⟩ := h'
  refine ⟨(totalDegree_mul _ _).trans (add_le_add ha ha'),
    (totalDegree_mul _ _).trans (add_le_add hb hb'), ?_⟩
  by_cases e : a = b ∧ a' = b'
  · left; rw [e.1, e.2]
  right
  have key : a * a' - b * b' = (a - b) * a' + b * (a' - b') := by ring
  rw [key]
  refine lt_of_le_of_lt (totalDegree_add _ _) (max_lt ?_ ?_)
  · rcases hab with h1 | h1
    · rw [h1, sub_self, zero_mul, totalDegree_zero]
      rcases hab' with h2 | h2
      · exact absurd ⟨h1, h2⟩ e
      · omega
    · exact lt_of_le_of_lt (totalDegree_mul _ _) (by omega)
  · rcases hab' with h1 | h1
    · rw [h1, sub_self, mul_zero, totalDegree_zero]
      rcases hab with h2 | h2
      · exact absurd ⟨h2, h1⟩ e
      · omega
    · exact lt_of_le_of_lt (totalDegree_mul _ _) (by omega)

theorem TopClose.pow {k : ℕ} {a b : MvPolynomial (Fin n) ℂ} (h : TopClose k a b) (c : ℕ) :
    TopClose (c * k) (a ^ c) (b ^ c) := by
  induction c with
  | zero => simpa using TopClose.one
  | succ c ih =>
    rw [pow_succ, pow_succ, Nat.succ_mul]
    exact ih.mul h

theorem TopClose.prod {ι : Type*} (s : Finset ι) (k : ι → ℕ) (a b : ι → MvPolynomial (Fin n) ℂ)
    (h : ∀ i ∈ s, TopClose (k i) (a i) (b i)) :
    TopClose (∑ i ∈ s, k i) (∏ i ∈ s, a i) (∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using TopClose.one
  | insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi, sum_insert hi]
    exact (h i (mem_insert_self _ _)).mul (ih fun j hj => h j (mem_insert_of_mem hj))

theorem isHomogeneous_psum (k : ℕ) : (psum (Fin n) ℂ k).IsHomogeneous k := by
  unfold psum
  exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i k

def psumWt (c : Fin n →₀ ℕ) : ℕ := ∑ i ∈ c.support, c i * ((i : ℕ) + 1)

theorem symmetric_le_adjoin (q : Fin n → MvPolynomial (Fin n) ℂ) (hq : ∀ k, (q k).IsSymmetric)
    (hdeg : ∀ k, (q k - psum (Fin n) ℂ ((k : ℕ) + 1)).totalDegree < (k : ℕ) + 1) (d : ℕ) :
    ∀ p : MvPolynomial (Fin n) ℂ, p.IsSymmetric → p.totalDegree ≤ d →
      p ∈ Algebra.adjoin ℂ (Set.range q) := by
  set B := Algebra.adjoin ℂ (Set.range q)
  have hBsym : ∀ r ∈ B, r.IsSymmetric := by
    have : B ≤ symmetricSubalgebra (Fin n) ℂ :=
      Algebra.adjoin_le (by rintro _ ⟨k, rfl⟩; exact hq k)
    exact fun r hr => this hr
  have hclose : ∀ i : Fin n, TopClose ((i : ℕ) + 1) (psumFin i) (q i) := by
    intro i
    have h1 : (psumFin i).totalDegree ≤ (i : ℕ) + 1 :=
      (isHomogeneous_psum _).totalDegree_le
    refine ⟨h1, ?_, Or.inr ?_⟩
    · have : q i = psumFin i + (q i - psumFin i) := by ring
      rw [this]
      exact (totalDegree_add _ _).trans (max_le h1 (hdeg i).le)
    · rw [← neg_sub, totalDegree_neg]; exact hdeg i
  induction d with
  | zero =>
    intro p _ hp
    rw [totalDegree_eq_zero_iff_eq_C.1 (show p.totalDegree = 0 by omega)]
    exact B.algebraMap_mem _
  | succ d ih =>
    intro p hp hpd
    obtain ⟨F, rfl⟩ : ∃ F, aeval psumFin F = p := by
      have := mem_adjoin_psum_of_isSymmetric hp
      rw [Algebra.adjoin_range_eq_range_aeval] at this
      exact this
    set P : (Fin n →₀ ℕ) → MvPolynomial (Fin n) ℂ := fun c => c.prod fun i k => psumFin i ^ k
    set Q : (Fin n →₀ ℕ) → MvPolynomial (Fin n) ℂ := fun c => c.prod fun i k => q i ^ k
    have hPhom : ∀ c, (P c).IsHomogeneous (psumWt c) := by
      intro c
      simp only [P, Finsupp.prod, psumWt]
      refine IsHomogeneous.prod _ _ _ fun i _ => ?_
      rw [mul_comm]
      exact (isHomogeneous_psum _).pow _
    have hPQ : ∀ c, TopClose (psumWt c) (P c) (Q c) := by
      intro c
      simp only [P, Q, Finsupp.prod, psumWt]
      exact TopClose.prod _ _ _ _ fun i _ => (hclose i).pow (c i)
    have hF : aeval psumFin F = ∑ c ∈ F.support, AddMonoidAlgebra.coeff F c • P c := by
      conv_lhs => rw [F.as_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine sum_congr rfl fun c _ => ?_
      rw [aeval_monomial, Algebra.smul_def]
    set S := F.support.filter fun c => psumWt c = d + 1
    set r := ∑ c ∈ S, AddMonoidAlgebra.coeff F c • Q c
    have hr : r ∈ B := by
      refine B.sum_mem fun c _ => B.smul_mem ?_ _
      simp only [Q, Finsupp.prod]
      exact B.prod_mem fun i _ => B.pow_mem (Algebra.subset_adjoin ⟨i, rfl⟩) _
    have htop : homogeneousComponent (d + 1) (aeval psumFin F) = ∑ c ∈ S, AddMonoidAlgebra.coeff F c • P c := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hF, map_sum, sum_filter]
      refine sum_congr rfl fun c _ => ?_
      rw [map_smul, homogeneousComponent_of_mem (hPhom c)]
      by_cases h : psumWt c = d + 1
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (Ne.symm h), if_neg h, smul_zero]
    have hlow : (aeval psumFin F - homogeneousComponent (d + 1) (aeval psumFin F)).totalDegree ≤ d := by
      set p := aeval psumFin F
      rw [totalDegree, Finset.sup_le_iff]
      intro m hm
      rw [mem_support_iff, coeff_sub, coeff_homogeneousComponent] at hm
      have hm' : m ∈ p.support := by
        rw [mem_support_iff]; intro h0; rw [h0] at hm; simp at hm
      have h1 := le_totalDegree hm'
      by_cases hd : m.degree = d + 1
      · rw [if_pos hd, sub_self] at hm; exact absurd rfl hm
      · have : (m.sum fun _ e => e) = m.degree := by
          rfl
        rw [this] at h1 ⊢
        omega
    have hdiff : (∑ c ∈ S, AddMonoidAlgebra.coeff F c • P c - r).totalDegree ≤ d := by
      rw [← sum_sub_distrib]
      refine totalDegree_finsetSum_le fun c hc => ?_
      rw [← smul_sub]
      refine (totalDegree_smul_le _ _).trans ?_
      have hwc : psumWt c = d + 1 := (mem_filter.1 hc).2
      rcases (hPQ c).2.2 with h | h
      · rw [h, sub_self, totalDegree_zero]; exact Nat.zero_le _
      · rw [hwc] at h; omega
    have hkey : (aeval psumFin F - r).totalDegree ≤ d := by
      have : aeval psumFin F - r = (aeval psumFin F - homogeneousComponent (d + 1) (aeval psumFin F))
          + (∑ c ∈ S, AddMonoidAlgebra.coeff F c • P c - r) := by rw [htop]; ring
      rw [this]
      exact (totalDegree_add _ _).trans (max_le hlow hdiff)
    have hsym : (aeval psumFin F - r).IsSymmetric :=
      (symmetricSubalgebra (Fin n) ℂ).sub_mem hp (hBsym r hr)
    have := B.add_mem (ih _ hsym hkey) hr
    rwa [sub_add_cancel] at this

theorem adjoin_eq_symmetricSubalgebra (q : Fin n → MvPolynomial (Fin n) ℂ)
    (hq : ∀ k, (q k).IsSymmetric)
    (hdeg : ∀ k, (q k - psum (Fin n) ℂ ((k : ℕ) + 1)).totalDegree < (k : ℕ) + 1) :
    Algebra.adjoin ℂ (Set.range q) = symmetricSubalgebra (Fin n) ℂ := by
  apply le_antisymm
  · exact Algebra.adjoin_le (by rintro _ ⟨k, rfl⟩; exact hq k)
  · intro p hp
    exact symmetric_le_adjoin q hq hdeg _ p hp le_rfl

end GroundTheory.Automorphic.HarishChandra
end

namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

theorem harishChandraHom_mem_symmetricSubalgebra (z : Subalgebra.center ℂ (U n)) :
    harishChandraHom z ∈ symmetricSubalgebra (Fin n) ℂ :=
  harishChandraHom_isSymmetric z

noncomputable def capelliCenter (k : ℕ) : Subalgebra.center ℂ (U n) :=
  ⟨capelli (k + 1), capelli_mem_center _⟩

theorem adjoin_harishChandraHom_capelli :
    Algebra.adjoin ℂ (Set.range fun k : Fin n => harishChandraHom (capelliCenter (n := n) k)) =
      symmetricSubalgebra (Fin n) ℂ :=
  adjoin_eq_symmetricSubalgebra _ (fun _ => harishChandraHom_isSymmetric _)
    (fun k => totalDegree_harishChandraHom_capelli_sub k)

theorem range_harishChandraHom :
    (harishChandraHom (n := n)).range = symmetricSubalgebra (Fin n) ℂ := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact harishChandraHom_isSymmetric z
  · rw [← adjoin_harishChandraHom_capelli, Algebra.adjoin_le_iff]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, rfl⟩

noncomputable def harishChandraEquiv :
    Subalgebra.center ℂ (U n) ≃ₐ[ℂ] symmetricSubalgebra (Fin n) ℂ :=
  (AlgEquiv.ofInjective harishChandraHom harishChandraHom_injective).trans
    (Subalgebra.equivOfEq _ _ range_harishChandraHom)

@[simp] theorem harishChandraEquiv_apply (z : Subalgebra.center ℂ (U n)) :
    (harishChandraEquiv z : MvPolynomial (Fin n) ℂ) = harishChandraHom z := rfl

end GroundTheory.Automorphic.HarishChandra
