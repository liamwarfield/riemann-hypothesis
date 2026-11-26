module

public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas
public import Formalism.GradedWeylDivisibility.StatementB

@[expose] public section

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylRowDivStable
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem rowDiv_add_fock_space_tableaux (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f g : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (f + g) = rowDiv R a b k f + rowDiv R a b k g := by
  unfold rowDiv
  rw [map_add (f := _), Polynomial.coeff_add]

private theorem rowDiv_smul_fock_space_tableaux (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (c : R) (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (c • f) = c • rowDiv R a b k f := by
  unfold rowDiv
  rw [map_smul, Polynomial.coeff_smul]

theorem weylModuleRowDividedPowerStable : WeylRowDivStable := by
  unfold WeylRowDivStable
  intro R _ r n hn ν a b k f hf
  let L : MvPolynomial (Fin r × Fin n) R →ₗ[R] MvPolynomial (Fin r × Fin n) R :=
    { toFun := rowDiv R a b k
      map_add' := rowDiv_add_fock_space_tableaux R a b k
      map_smul' := rowDiv_smul_fock_space_tableaux R a b k }
  have key : weyl R r n hn ν ≤ (weyl R r n hn ν).comap L := by
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    exact Submodule.subset_span ⟨(a, b, k) :: w, rfl⟩
  exact key hf

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCdegLemmas
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lcdeg_degreeOf_X_le {σ R : Type*} [CommRing R] [DecidableEq σ] (i j : σ) :
    degreeOf i (X j : MvPolynomial σ R) ≤ if j = i then 1 else 0 := by
  rw [degreeOf_eq_sup]
  refine Finset.sup_le fun m hm => ?_
  have hm' : m ∈ (monomial (Finsupp.single j 1) (1 : R)).support := hm
  obtain rfl := Finset.mem_singleton.mp (support_monomial_subset hm')
  rw [Finsupp.single_apply]

theorem lcdeg_degreeOf_aeval_le {σ τ R : Type*} [CommRing R] (f : σ → MvPolynomial τ R)
    (p : MvPolynomial σ R) (c : τ) (d : ℕ)
    (h : ∀ m ∈ p.support, ∑ v ∈ m.support, m v * degreeOf c (f v) ≤ d) :
    degreeOf c (aeval f p) ≤ d := by
  classical
  rw [aeval_def, eval₂_eq]
  have key : ∀ m ∈ p.support, degreeOf c (algebraMap R (MvPolynomial τ R) (AddMonoidAlgebra.coeff p m) *
      ∏ v ∈ m.support, f v ^ m v) ≤ d := by
    intro m hm
    rw [algebraMap_eq]
    refine (degreeOf_C_mul_le _ _ _).trans ?_
    exact (degreeOf_prod_le _ _ _).trans
      ((Finset.sum_le_sum fun v _ => degreeOf_pow_le _ _ _).trans (h m hm))
  clear h
  generalize p.support = s at key ⊢
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (degreeOf_add_le _ _ _).trans (max_le (key a (Finset.mem_insert_self _ _))
      (ih fun m hm => key m (Finset.mem_insert_of_mem hm)))

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylDominanceOf
open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem sum_fin_filter_lt_eq_range {N : ℕ} (G : ℕ → ℕ) (k : ℕ) :
    ∑ a : Fin N with a.val < k, G a.val = ∑ i ∈ Finset.range (min N k), G i := by
  rw [Finset.sum_filter]
  refine (Fin.sum_univ_eq_sum_range (fun i => if i < k then G i else 0) N).trans ?_
  show ∑ i ∈ Finset.range N, (if i < k then G i else 0) = _
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem rowNu_partial_sum {r n : ℕ} (ν : Fin n → ℕ) (hnr : n ≤ r) (k : ℕ) :
    (∑ a : Fin r with a.val < k, rowNu (r := r) ν a) = ∑ t : Fin n with t.val < k, ν t := by
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℕ, G = fun i => if h : i < n then ν ⟨i, h⟩ else 0 := ⟨_, rfl⟩
  have h1 : (∑ a : Fin r with a.val < k, rowNu (r := r) ν a) =
      ∑ a : Fin r with a.val < k, G a.val :=
    Finset.sum_congr rfl fun a _ => by subst hG; rfl
  have h2 : (∑ t : Fin n with t.val < k, ν t) = ∑ t : Fin n with t.val < k, G t.val :=
    Finset.sum_congr rfl fun t _ => by subst hG; simp [t.isLt]
  rw [h1, h2, sum_fin_filter_lt_eq_range, sum_fin_filter_lt_eq_range]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hi hi'
    simp only [Finset.mem_range] at hi hi'
    have hin : ¬ i < n := by omega
    rw [hG]
    simp [hin]

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCssytLemmas
open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lcssyt_shapeDeg_cons {n K : ℕ} (h : ℕ) (sz : Fin K → ℕ) (t : Fin n) :
    shapeDeg (Fin.cons h sz : Fin (K + 1) → ℕ) t = (if t.val < h then 1 else 0) + shapeDeg sz t := by
  unfold shapeDeg
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem lcssyt_consSz {n K h : ℕ} (hh : h ≤ n) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) :
    ∀ k : Fin (K + 1), (Fin.cons h sz : Fin (K + 1) → ℕ) k ≤ n := by
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa using hh
  · simpa using hsz i

def lcssyt_consI {r K h : ℕ} (sz : Fin K → ℕ) (c : Fin h → Fin r) (I : ∀ k, Fin (sz k) → Fin r) :
    ∀ k : Fin (K + 1), Fin ((Fin.cons h sz : Fin (K + 1) → ℕ) k) → Fin r :=
  fun k => Fin.cases (motive := fun k => Fin ((Fin.cons h sz : Fin (K + 1) → ℕ) k) → Fin r) c I k

theorem lcssyt_bidetExp_cons {r n K h : ℕ} (hh : h ≤ n) (c : Fin h → Fin r) (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    bidetExp (Fin.cons h sz : Fin (K + 1) → ℕ) (lcssyt_consSz hh sz hsz) (lcssyt_consI sz c I) =
      colExp c hh + bidetExp sz hsz I := by
  unfold bidetExp
  rw [Fin.sum_univ_succ]
  rfl

theorem lcssyt_consI_strictMono {r K h : ℕ} (sz : Fin K → ℕ) (c : Fin h → Fin r) (I : ∀ k, Fin (sz k) → Fin r)
    (hc : StrictMono c) (hI : ∀ k, StrictMono (I k)) : ∀ k, StrictMono (lcssyt_consI sz c I k) := by
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · exact hc
  · exact hI i

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowGraded
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem dualWeylModuleRowGraded : DualWeylRowGraded := by
  classical
  intro R _ r n ν μ f hf
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf ⊢
  obtain ⟨hcol, hadd⟩ := hf
  refine ⟨?_, fun l j hlj => ?_⟩
  · intro d hd
    rw [coeff_weightedHomogeneousComponent] at hd
    split_ifs at hd with h
    · exact hcol hd
    · exact absurd rfl hd
  · let w' : Option (Fin r × Fin n) → (Fin r → ℕ) := fun o => Option.elim o 0 (rowW r n)
    have key : ∀ F : Fin r × Fin n → MvPolynomial (Option (Fin r × Fin n)) R,
        (∀ v, IsWeightedHomogeneous w' (F v) (rowW r n v)) → ∀ φ : MvPolynomial (Fin r × Fin n) R,
        weightedHomogeneousComponent w' μ (aeval F φ) =
          aeval F (weightedHomogeneousComponent (rowW r n) μ φ) := by
      intro F hF φ
      refine MvPolynomial.induction_on' φ (fun u a => ?_) (fun p q hp hq => ?_)
      · have hm : IsWeightedHomogeneous w' (aeval F (monomial u a)) (Finsupp.weight (rowW r n) u) := by
          rw [aeval_monomial, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, algebraMap_eq]
          have := (isWeightedHomogeneous_C w' a).mul
            (IsWeightedHomogeneous.prod u.support (fun i => F i ^ u i) (fun i => u i • rowW r n i)
              fun i _ => (hF i).pow (u i))
          rwa [zero_add] at this
        have hm0 : IsWeightedHomogeneous (rowW r n) (monomial u a) (Finsupp.weight (rowW r n) u) :=
          isWeightedHomogeneous_monomial _ _ _ rfl
        rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm),
          weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm0)]
        split_ifs <;> simp
      · simp only [map_add (f := _), hp, hq]
    let G : Fin r × Fin n → MvPolynomial (Option (Fin r × Fin n)) R := fun v =>
      if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)
    have hG : ∀ v, IsWeightedHomogeneous w' (G v) (rowW r n v) := by
      intro v
      simp only [G]
      split_ifs
      · refine (isWeightedHomogeneous_X R w' (some v)).add ?_
        have := (isWeightedHomogeneous_X R w' none).mul (isWeightedHomogeneous_X R w' (some (v.1, l)))
        rw [show w' none = 0 from rfl, zero_add] at this
        exact this
      · exact isWeightedHomogeneous_X R w' (some v)
    have hGs : ∀ v, IsWeightedHomogeneous w' ((fun v : Fin r × Fin n =>
        (X (some v) : MvPolynomial (Option (Fin r × Fin n)) R)) v) (rowW r n v) :=
      fun v => isWeightedHomogeneous_X R w' (some v)
    have hA : colAddGen R (r := r) l j = aeval G := rfl
    have hB : (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) =
        aeval (fun v : Fin r × Fin n => (X (some v) : MvPolynomial (Option (Fin r × Fin n)) R)) := by
      ext v; simp
    have h1 := hadd l j hlj
    rw [hA, hB] at h1 ⊢
    rw [← key G hG, ← key _ hGs, h1]

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWRaise
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem rowGen_X (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    rowGen R a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  rw [rowGen, aeval_X]

theorem rowGen_lpMinor (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (hab : a < b)
    (m : ℕ) (hr : m ≤ r) (hn : m ≤ n) :
    rowGen R a b (lpMinor R m hr hn) = Polynomial.C (lpMinor R m hr hn) := by
  classical
  unfold lpMinor
  rw [AlgHom.map_det, RingHom.map_det]
  set N : Matrix (Fin m) (Fin m) (MvPolynomial (Fin r × Fin n) R) :=
    Matrix.of fun p q : Fin m => (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)
    with hN
  by_cases hb : b.val < m
  · have ha : a.val < m := lt_trans hab hb
    set i : Fin m := ⟨b.val, hb⟩ with hi
    set j : Fin m := ⟨a.val, ha⟩ with hj
    have hij : i ≠ j := by
      intro h
      have := congrArg Fin.val h
      simp [hi, hj] at this
      exact absurd this (Fin.val_ne_of_ne (ne_of_lt hab)).symm
    have hM : (rowGen R a b).toRingHom.mapMatrix N =
        Matrix.updateRow ((Polynomial.C : MvPolynomial (Fin r × Fin n) R →+* _).mapMatrix N) i
          (((Polynomial.C : MvPolynomial (Fin r × Fin n) R →+* _).mapMatrix N) i +
            (Polynomial.X : Polynomial (MvPolynomial (Fin r × Fin n) R)) • ((Polynomial.C : MvPolynomial (Fin r × Fin n) R →+* _).mapMatrix N) j) := by
      ext p q
      by_cases hp : p = i
      · subst hp
        have h1 : Fin.castLE hr i = b := Fin.ext (by simp [hi])
        have h2 : Fin.castLE hr j = a := Fin.ext (by simp [hj])
        simp [hN, Matrix.updateRow_apply, rowGen_X, h1, h2, smul_eq_mul]
      · have h1 : Fin.castLE hr p ≠ b := by
          intro h
          apply hp
          exact Fin.ext (by have := congrArg Fin.val h; simpa [hi] using this)
        simp [hN, Matrix.updateRow_apply, rowGen_X, h1, hp]
    change ((rowGen R a b).toRingHom.mapMatrix N).det = _
    rw [hM, Matrix.det_updateRow_add_smul_self _ hij]
  · have hM : (rowGen R a b).toRingHom.mapMatrix N =
        (Polynomial.C : MvPolynomial (Fin r × Fin n) R →+* _).mapMatrix N := by
      ext p q
      have h1 : Fin.castLE hr p ≠ b := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [hN, rowGen_X, h1]
    change ((rowGen R a b).toRingHom.mapMatrix N).det = _
    rw [hM]

theorem rowGen_hw (R : Type*) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (a b : Fin r) (hab : a < b) :
    rowGen R a b (hw R hn ν) = Polynomial.C (hw R hn ν) := by
  simp only [hw, map_prod, map_pow, rowGen_lpMinor R a b hab]

theorem highestWeightVectorRaising : HWRaise := by
  intro R _ r n hn ν a b k hab hk
  unfold rowDiv
  rw [rowGen_hw R hn ν a b hab, Polynomial.coeff_C, if_neg (by omega)]

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.PeelLead
section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCpleadLemmas
open MvPolynomial
open scoped MonomialOrder

noncomputable section

namespace Formalism.GradedWeylDivisibility

private lemma pairW_apply {r n : ℕ} (l j : Fin n) (v : Fin r × Fin n) (b : Fin r)
    (t : Fin n) :
    pairW l j v (b, t) = if v.2 = j then (if (v.1, l) = (b, t) then 1 else 0)
      else (if v = (b, t) then 1 else 0) := by
  classical
  unfold pairW
  split_ifs <;> simp_all [Finsupp.single_apply]

theorem lcplead_weight_apply {r n : ℕ} (l j : Fin n) (hlj : l ≠ j) (d : Fin r × Fin n →₀ ℕ)
    (b : Fin r) (t : Fin n) :
    Finsupp.weight (pairW l j) d (b, t) =
      if t = l then d (b, l) + d (b, j) else if t = j then 0 else d (b, t) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, pairW_apply, smul_eq_mul]
  split_ifs with h1 h2
  · subst h1
    rw [Fintype.sum_eq_add (b, t) (b, j) (by simp [hlj])]
    · simp [hlj]
    · rintro ⟨a, s⟩ ⟨ha1, ha2⟩
      by_cases hs : s = j <;> simp_all [Prod.ext_iff]
  · subst h2
    refine Finset.sum_eq_zero fun x _ => ?_
    obtain ⟨a, s⟩ := x
    by_cases hs : s = t <;> simp_all [Prod.ext_iff]
  · rw [Fintype.sum_eq_single (b, t)]
    · simp [h2]
    · rintro ⟨a, s⟩ hx
      have h1' : l ≠ t := Ne.symm h1
      by_cases hs : s = j <;> simp_all [Prod.ext_iff]

section
variable {B : Type*} [CommRing B] {r n : ℕ} {l j : Fin n}

theorem lcplead_hom_row (hlj : l ≠ j) {ω : Fin r × Fin n →₀ ℕ} {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support)
    (b : Fin r) : m (b, l) + m (b, j) = ω (b, l) := by
  rw [← hg (mem_support_iff.mp hm), lcplead_weight_apply l j hlj m b l, if_pos rfl]

theorem lcplead_hom_off (hlj : l ≠ j) {ω : Fin r × Fin n →₀ ℕ} {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support)
    (b : Fin r) (t : Fin n) (htl : t ≠ l) (htj : t ≠ j) : m (b, t) = ω (b, t) := by
  rw [← hg (mem_support_iff.mp hm), lcplead_weight_apply l j hlj m b t, if_neg htl, if_neg htj]

private lemma support_eq_of_pairW_homogeneous_of_erase_eq (hlj : l ≠ j) (a0 : Fin r) {ω : Fin r × Fin n →₀ ℕ}
    {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m m' : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support)
    (hm' : m' ∈ g.support) (h1 : m' (a0, l) = m (a0, l))
    (h2 : (m'.erase (a0, l)).erase (a0, j) = (m.erase (a0, l)).erase (a0, j)) : m' = m := by
  ext v
  by_cases hv1 : v = (a0, l)
  · rw [hv1, h1]
  by_cases hv2 : v = (a0, j)
  · have e1 := lcplead_hom_row hlj hg hm a0
    have e2 := lcplead_hom_row hlj hg hm' a0
    rw [hv2]; omega
  have := congrArg (fun f => f v) h2
  simpa [Finsupp.erase_ne hv1, Finsupp.erase_ne hv2] using this

theorem lcplead_coeff_peel (hlj : l ≠ j) (a0 : Fin r) {ω : Fin r × Fin n →₀ ℕ}
    {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support) :
    AddMonoidAlgebra.coeff (peel l j a0 (m (a0, l)) g) ((m.erase (a0, l)).erase (a0, j)) = AddMonoidAlgebra.coeff g m := by
  classical
  unfold peel
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single m]
  · simp
  · intro m' hm' hne
    rw [Finset.mem_filter] at hm'
    rw [if_neg]
    intro heq
    exact hne (support_eq_of_pairW_homogeneous_of_erase_eq hlj a0 hg hm hm'.1 hm'.2 heq)
  · intro hnot
    exact (hnot (Finset.mem_filter.mpr ⟨hm, rfl⟩)).elim

theorem lcplead_mem_support_peel (a0 : Fin r) (k : ℕ) {g : MvPolynomial (Fin r × Fin n) B}
    {p : Fin r × Fin n →₀ ℕ} (hp : p ∈ (peel l j a0 k g).support) :
    ∃ m ∈ g.support, m (a0, l) = k ∧ p = (m.erase (a0, l)).erase (a0, j) := by
  classical
  unfold peel at hp
  obtain ⟨m, hm, hpm⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hp)
  rw [Finset.mem_filter] at hm
  exact ⟨m, hm.1, hm.2, Finset.mem_singleton.mp (support_monomial_subset hpm)⟩

theorem lcplead_recon (hlj : l ≠ j) (a0 : Fin r) {ω : Fin r × Fin n →₀ ℕ}
    {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support) :
    m = Finsupp.single (a0, l) (m (a0, l)) + Finsupp.single (a0, j) (ω (a0, l) - m (a0, l)) +
      (m.erase (a0, l)).erase (a0, j) := by
  have h := lcplead_hom_row hlj hg hm a0
  have hne : ((a0, l) : Fin r × Fin n) ≠ (a0, j) := by simp [hlj]
  ext v
  simp only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.erase_apply]
  by_cases h1 : v = (a0, l)
  · subst h1; simp [hne, Ne.symm hlj]
  · by_cases h2 : v = (a0, j)
    · subst h2; simp [hne]; omega
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

end

theorem lcplead_cmIdx_val {r n : ℕ} (b : Fin r) (t : Fin n) :
    ((cmIdx r n (b, t) : Fin (n * r)) : ℕ) = b + r * t := by
  simp [cmIdx, finProdFinEquiv]

theorem lcplead_cmIdx_lt {r n : ℕ} {b a0 : Fin r} {t l : Fin n}
    (h : cmIdx r n (b, t) < cmIdx r n (a0, l)) : t < l ∨ (t = l ∧ b < a0) := by
  have h' : (b : ℕ) + r * t < a0 + r * l := by
    have := Fin.lt_def.mp h
    rwa [lcplead_cmIdx_val, lcplead_cmIdx_val] at this
  rcases lt_trichotomy (t : ℕ) l with h1 | h1 | h1
  · exact Or.inl (Fin.lt_def.mpr h1)
  · refine Or.inr ⟨Fin.ext h1, Fin.lt_def.mpr ?_⟩
    rw [h1] at h'
    exact Nat.lt_of_add_lt_add_right h'
  · exfalso
    have h2 := Nat.mul_le_mul_left r (show (l : ℕ) + 1 ≤ t from h1)
    have h3 := a0.isLt
    rw [Nat.mul_add, mul_one] at h2
    omega

end Formalism.GradedWeylDivisibility
end
end

open MvPolynomial
open scoped MonomialOrder

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem toLex_lt_of_eq_of_lt_at {N : ℕ} {a b : Fin N →₀ ℕ} (i : Fin N)
    (h1 : ∀ i', i' < i → a i' = b i') (h2 : a i < b i) : toLex a < toLex b := by
  exact Finsupp.lex_def.2 ⟨i, h1, h2⟩

private theorem domCongr_cmIdx_apply_eq {r n : ℕ} (m : Fin r × Fin n →₀ ℕ)
    (x : Fin r × Fin n) :
    Finsupp.domCongr (cmIdx r n) m (cmIdx r n x) = m x := by
  simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]

private theorem toSyn_le_toSyn_degree_of_mem_support {σ R : Type*} [CommSemiring R] (M : MonomialOrder σ)
    {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : d ∈ f.support) :
    M.toSyn d ≤ M.toSyn (M.degree f) := by
  exact M.le_degree hd

theorem sliceLeading : PeelLead := by
  unfold PeelLead
  intro B _ _ r n l j hlj a0 ω g K hg hω hK htop
  have hlj' : l ≠ j := ne_of_lt hlj
  have hd : (colLex r n).degree (peel l j a0 K g) ∈
      (peel l j a0 K g).support :=
    (colLex r n).degree_mem_support hK
  obtain ⟨m0, hm0, hm0K, hd_eq⟩ := lcplead_mem_support_peel a0 K hd
  have hm0_eq := lcplead_recon hlj' a0 hg hm0
  rw [hm0K, ← hd_eq] at hm0_eq
  rw [← hm0_eq]
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hm0
  have hup : ∀ m ∈ g.support, (colLex r n).toSyn m ≤ (colLex r n).toSyn m0 := by
    intro m hm
    rcases lt_trichotomy (m (a0, l)) K with hlt | heq | hgt
    · apply le_of_lt
      apply colLex_lt_iff.2
      refine toLex_lt_of_eq_of_lt_at (cmIdx r n (a0, l)) ?_ ?_
      · intro i' hi'
        obtain ⟨⟨b, t⟩, rfl⟩ := (cmIdx r n).surjective i'
        rw [domCongr_cmIdx_apply_eq, domCongr_cmIdx_apply_eq]
        rcases lcplead_cmIdx_lt hi' with ht | ⟨ht, hb⟩
        · have htl : t ≠ l := ne_of_lt ht
          have htj : t ≠ j := ne_of_lt (lt_trans ht hlj)
          rw [lcplead_hom_off hlj' hg hm b t htl htj,
            lcplead_hom_off hlj' hg hm0 b t htl htj]
        · rw [ht]
          have h1 := lcplead_hom_row hlj' hg hm b
          have h2 := lcplead_hom_row hlj' hg hm0 b
          have h3 := hω b hb
          omega
      · rw [domCongr_cmIdx_apply_eq, domCongr_cmIdx_apply_eq, hm0K]
        exact hlt
    · have hc := lcplead_coeff_peel hlj' a0 hg hm
      rw [heq] at hc
      have he : (m.erase (a0, l)).erase (a0, j) ∈ (peel l j a0 K g).support := by
        rw [mem_support_iff, hc]
        exact mem_support_iff.1 hm
      have hle := toSyn_le_toSyn_degree_of_mem_support (colLex r n) he
      have hm_eq := lcplead_recon hlj' a0 hg hm
      rw [heq] at hm_eq
      rw [hm_eq, hm0_eq]
      simp only [map_add (f := _)]
      exact add_le_add le_rfl hle
    · exfalso
      have hc := lcplead_coeff_peel hlj' a0 hg hm
      simp only [htop _ hgt, AddMonoidAlgebra.coeff_zero] at hc
      exact mem_support_iff.1 hm hc.symm
  exact (colLex r n).toSyn.injective
    (le_antisymm (hup _ ((colLex r n).degree_mem_support hg0))
      (toSyn_le_toSyn_degree_of_mem_support (colLex r n) hm0))

end Formalism.GradedWeylDivisibility
end
end
