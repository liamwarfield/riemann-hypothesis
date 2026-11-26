module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
public import Formalism.RealPlaceAnalysis.StatementE
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMeasureOfBoundedMoments
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesEvalTsumOpenPolydiscProperties

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MapDofIterate
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.InvDerMap

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

theorem map_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ R) :
    MvPowerSeries.map φ (pderiv i f) = pderiv i (MvPowerSeries.map φ f) := by
  ext m
  simp [coeff_map, coeff_pderiv]

theorem map_ev_axis {d : ℕ} (g : PS R 2 d) :
    MvPowerSeries.map φ (ev (n := 1) ![pt R d 0, 0] g) =
      ev (n := 1) ![pt S d 0, 0] (MvPowerSeries.map φ g) := by
  unfold ev
  have h : HasSubst (fun p : Fin 2 × Fin d => (![pt R d 0, 0] : Fin 2 → Pt R 1 d) p.1 p.2) := by
    apply hasSubst_of_constantCoeff_zero
    rintro ⟨j, i⟩
    fin_cases j <;> simp [pt]
  rw [MvPowerSeries.map_subst h]
  congr 1
  funext ⟨j, i⟩
  fin_cases j <;> simp [pt]

theorem map_Dof {d : ℕ} (F : Fin d → PS R 2 d) (u : Fin d → R) (f : PS R 1 d) :
    MvPowerSeries.map φ (Dof F u f) =
      Dof (fun i => MvPowerSeries.map φ (F i)) (fun i => φ (u i)) (MvPowerSeries.map φ f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Dof, map_sum, map_mul, map_C, map_ev_axis, map_pderiv]

theorem map_Dof_iterate {d : ℕ} (F : Fin d → PS R 2 d) (u : Fin d → R) (n : ℕ) (f : PS R 1 d) :
    MvPowerSeries.map φ ((Dof F u)^[n] f) =
      (Dof (fun i => MvPowerSeries.map φ (F i)) (fun i => φ (u i)))^[n] (MvPowerSeries.map φ f) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_Dof, ih]

end GlobalTheory.InvDerMap

namespace GlobalTheory

theorem map_dmonOf (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ) (F : Fin d → PS R 2 d)
    (ι : Type) [Fintype ι] (u : ι → Fin d → R) (m : ι →₀ ℕ) (f : PS R 1 d) :
    MvPowerSeries.map φ (DmonOf F u m f) =
      DmonOf (fun i => MvPowerSeries.map φ (F i)) (fun l i => φ (u l i)) m (MvPowerSeries.map φ f) := by
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, List.foldr_cons, InvDerMap.map_Dof_iterate, ih]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QdetTopThreeOrders
open Finset

namespace GlobalTheory.CapelliTop
variable {A : Type} [Ring A] {n : ℕ}

def oprod (S : Finset (Fin n)) (e : Fin n → A) : A :=
  (List.ofFn fun k => if k ∈ S then e k else 1).prod

theorem prod_add_expand [Algebra ℂ A] (c : Fin n → ℂ) (e : Fin n → A) :
    (List.ofFn fun k => c k • (1 : A) + e k).prod =
      ∑ S : Finset (Fin n), (∏ k ∈ Sᶜ, c k) • oprod S e := by
  have h := (MultilinearMap.mkPiAlgebraFin ℂ n A).map_add_univ e (fun k => c k • (1 : A))
  simp only [MultilinearMap.mkPiAlgebraFin_apply] at h
  have h0 : (fun k => c k • (1 : A) + e k) = e + fun k => c k • (1 : A) := by
    funext k; simp [add_comm]
  rw [h0, h]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h1 := (MultilinearMap.mkPiAlgebraFin ℂ n A).map_smul_univ (fun k => if k ∈ S then 1 else c k)
    (fun k => if k ∈ S then e k else 1)
  simp only [MultilinearMap.mkPiAlgebraFin_apply] at h1
  have h2 : S.piecewise e (fun k => c k • (1 : A)) =
      fun k => (if k ∈ S then (1 : ℂ) else c k) • (if k ∈ S then e k else 1) := by
    funext k; by_cases hk : k ∈ S <;> simp [hk]
  rw [h2, h1, oprod]
  congr 1
  rw [← Finset.prod_mul_prod_compl S, Finset.prod_eq_one (s := S) (fun k hk => by simp [hk]), one_mul]
  exact Finset.prod_congr rfl fun k hk => by simp [Finset.mem_compl.1 hk]

theorem list_ite {ι : Type} (p : ι → Prop) [DecidablePred p] (e : ι → A) (l : List ι) :
    (l.map fun k => if p k then e k else 1).prod = ((l.filter fun k => decide (p k)).map e).prod := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

theorem oprod_eq (S : Finset (Fin n)) (e : Fin n → A) (l : List (Fin n)) (hl : l.Pairwise (· < ·))
    (h : ∀ k, k ∈ l ↔ k ∈ S) : oprod S e = (l.map e).prod := by
  rw [oprod, List.ofFn_eq_map, list_ite]
  congr 2
  have h1 : ((List.finRange n).filter fun k => decide (k ∈ S)).Pairwise (· < ·) :=
    (List.pairwise_lt_finRange n).filter _
  exact h1.eq_of_mem_iff hl (fun k => by simp [h])

def subdet (E : Fin n → Fin n → A) (S : Finset (Fin n)) : A :=
  ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ k, k ∉ S → σ k = k),
    ((Equiv.Perm.sign σ : ℤ) : A) * oprod S (fun k => E (σ k) k)

theorem qdet_expand [Algebra ℂ A] (E : Fin n → Fin n → A) (u : ℂ) :
    Formalism.REAL.qdet E u = ∑ S : Finset (Fin n), (∏ k ∈ Sᶜ, (u - (k : ℂ))) • subdet E S := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  have h : ∀ σ : Equiv.Perm (Fin n),
      (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod =
      ∑ S : Finset (Fin n), (∏ k ∈ Sᶜ, (if σ k = k then u - (k : ℂ) else 0)) •
        oprod S (fun k => E (σ k) k) := by
    intro σ
    rw [← prod_add_expand]
    congr 2
    funext k
    by_cases hk : σ k = k <;> simp [Formalism.REAL.Tm, hk, Algebra.algebraMap_eq_smul_one]
  simp_rw [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [subdet, Finset.smul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_smul_comm]
  split_ifs with hσ
  · congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [if_pos (hσ k (Finset.mem_compl.1 hk))]
  · push Not at hσ
    obtain ⟨k, hk, hk'⟩ := hσ
    rw [Finset.prod_eq_zero (Finset.mem_compl.2 hk) (if_neg hk'), zero_smul]

theorem subdet_empty (E : Fin n → Fin n → A) : subdet E ∅ = 1 := by
  have : univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ k, k ∉ (∅ : Finset (Fin n)) → σ k = k) = {1} := by
    ext σ; simp [Equiv.ext_iff]
  rw [subdet, this, Finset.sum_singleton, oprod_eq _ _ [] (by simp) (by simp)]
  simp

theorem subdet_single (E : Fin n → Fin n → A) (i : Fin n) : subdet E {i} = E i i := by
  have : univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ k, k ∉ ({i} : Finset (Fin n)) → σ k = k) = {1} := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro h
      ext k
      by_cases hk : k = i
      · subst hk
        by_contra hne
        have hne' : σ k ≠ k := fun h' => hne (by simp [h'])
        exact hne' (σ.injective (h _ hne'))
      · simp [h k hk]
    · rintro rfl; simp
  rw [subdet, this, Finset.sum_singleton, oprod_eq _ _ [i] (by simp) (by simp)]
  simp

theorem subdet_pair (E : Fin n → Fin n → A) (i j : Fin n) (hij : i < j) :
    subdet E {i, j} = E i i * E j j - E j i * E i j := by
  have hne : i ≠ j := hij.ne
  have : univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ k, k ∉ ({i, j} : Finset (Fin n)) → σ k = k) =
      {1, Equiv.swap i j} := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_singleton, mem_insert, not_or]
    constructor
    · intro h
      have key : ∀ k, k = i ∨ k = j → σ k = i ∨ σ k = j := by
        intro k hk
        by_contra hc
        have h1 := σ.injective (h _ (not_or.1 hc))
        rw [h1] at hc
        exact hc hk
      have hinj : σ i ≠ σ j := σ.injective.ne hne
      rcases key i (Or.inl rfl) with hi | hi <;> rcases key j (Or.inr rfl) with hj | hj
      · exact absurd (hi.trans hj.symm) hinj
      · left
        refine Equiv.ext fun k => ?_
        by_cases h1 : k = i
        · simp [h1, hi]
        by_cases h2 : k = j
        · simp [h2, hj]
        simp [h k ⟨h1, h2⟩]
      · right
        refine Equiv.ext fun k => ?_
        by_cases h1 : k = i
        · simp [h1, hi]
        by_cases h2 : k = j
        · simp [h2, hj]
        rw [h k ⟨h1, h2⟩, Equiv.swap_apply_of_ne_of_ne h1 h2]
      · exact absurd (hi.trans hj.symm) hinj
    · rintro (rfl | rfl) k hk
      · simp
      · exact Equiv.swap_apply_of_ne_of_ne hk.1 hk.2
  have h1 : (1 : Equiv.Perm (Fin n)) ≠ Equiv.swap i j := fun h => hne (Equiv.swap_eq_one_iff.1 h.symm)
  rw [subdet, this, Finset.sum_pair h1, oprod_eq _ _ [i, j] (by simp [hij]) (by simp),
    oprod_eq _ _ [i, j] (by simp [hij]) (by simp), Equiv.Perm.sign_swap hne]
  simp [sub_eq_add_neg]

theorem sum_split {M : Type} [AddCommMonoid M] (F : Finset (Fin n) → M) :
    ∑ S, F S = F ∅ + ∑ i, F {i} + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F {i, j} +
      ∑ S ∈ univ.filter (fun S : Finset (Fin n) => 3 ≤ S.card), F S := by
  have h0 : univ.filter (fun S : Finset (Fin n) => S.card = 0) = {∅} := by
    ext S; simp
  have h1 : ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card = 1), F S = ∑ i, F {i} := by
    symm
    refine Finset.sum_bij (fun i _ => {i}) (by simp) (by simp) ?_ (by simp)
    intro S hS
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 (mem_filter.1 hS).2
    exact ⟨a, mem_univ _, rfl⟩
  have h2 : ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card = 2), F S =
      ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F {i, j} := by
    rw [Finset.sum_sigma']
    symm
    refine Finset.sum_bij (fun p _ => {p.1, p.2}) ?_ ?_ ?_ (by simp)
    · rintro ⟨i, j⟩ hp
      have : i < j := by simpa using hp
      simp [Finset.card_pair this.ne]
    · rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' h
      have a1 : i < j := by simpa using hp
      have a2 : i' < j' := by simpa using hp'
      have h' : ({i, j} : Finset (Fin n)) = {i', j'} := h
      have b1 : i ∈ ({i', j'} : Finset (Fin n)) := h' ▸ by simp
      have b2 : j ∈ ({i', j'} : Finset (Fin n)) := h' ▸ by simp
      have b3 : i' ∈ ({i, j} : Finset (Fin n)) := h' ▸ by simp
      simp only [mem_insert, mem_singleton] at b1 b2 b3
      have : i = i' ∧ j = j' := by omega
      obtain ⟨rfl, rfl⟩ := this
      rfl
    · intro S hS
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (mem_filter.1 hS).2
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨⟨a, b⟩, by simpa using h, rfl⟩
      · exact ⟨⟨b, a⟩, by simpa using h, Finset.pair_comm _ _⟩
  have h0' : F ∅ = ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card = 0), F S := by
    rw [h0, Finset.sum_singleton]
  rw [← h1, ← h2, h0']
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rcases hc : S.card with _ | _ | _ | m <;> simp

end GlobalTheory.CapelliTop

namespace GlobalTheory
open CapelliTop

theorem qdet_top_three_orders :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), ∃ Rm : ℕ → A, ∀ u : ℂ,
      Formalism.REAL.qdet E u = (∏ l : Fin n, (u - (l : ℂ))) • (1 : A) +
        ∑ i : Fin n, (∏ l ∈ univ.erase i, (u - (l : ℂ))) • E i i +
        ∑ i : Fin n, ∑ j ∈ univ.filter (fun j => i < j),
          (∏ l ∈ (univ.erase i).erase j, (u - (l : ℂ))) • (E i i * E j j - E j i * E i j) +
        ∑ d ∈ range (n - 2), u ^ d • Rm d := by
  intro A _ _ n E
  let p : Finset (Fin n) → Polynomial ℂ := fun S => ∏ k ∈ Sᶜ, (Polynomial.X - Polynomial.C (k : ℂ))
  refine ⟨fun d => ∑ S ∈ univ.filter (fun S : Finset (Fin n) => 3 ≤ S.card),
    (p S).coeff d • subdet E S, fun u => ?_⟩
  rw [qdet_expand, sum_split]
  congr 1
  · congr 1
    · congr 1
      · rw [subdet_empty, Finset.compl_empty]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [subdet_single, Finset.compl_singleton]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
      rw [subdet_pair E i j (mem_filter.1 hj).2]
      congr 2
      ext k; simp [and_comm]
  · simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hS3 := (mem_filter.1 hS).2
    have hle : S.card ≤ n := by simpa using Finset.card_le_univ S
    have hdeg : (p S).natDegree < n - 2 := by
      have : (p S).natDegree = Sᶜ.card := Polynomial.natDegree_finsetProd_X_sub_C_eq_card _ _
      rw [this, Finset.card_compl, Fintype.card_fin]
      omega
    have hev : (p S).eval u = ∏ k ∈ Sᶜ, (u - (k : ℂ)) := by
      simp [p, Polynomial.eval_prod]
    rw [← hev, Polynomial.eval_eq_sum_range' hdeg, Finset.sum_smul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_smul, mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLeadingMinorsGeOfLeRank
namespace GlobalTheory

theorem exists_mem_valuation_le_of_mem_span {C : Type} [Field C] (v : Valuation C NNReal)
    {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) {M : Type} [AddCommGroup M]
    [Module O M] (A : Set M) (φ : M →ₗ[O] O) {x : M} (hx : x ∈ Submodule.span O A)
    (h0 : v (algebraMap O C (φ x)) ≠ 0) :
    ∃ a ∈ A, v (algebraMap O C (φ x)) ≤ v (algebraMap O C (φ a)) := by
  by_contra hne
  push Not at hne
  have key : ∀ y ∈ Submodule.span O A,
      v (algebraMap O C (φ y)) < v (algebraMap O C (φ x)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem a ha => exact hne a ha
    | zero => simpa using pos_iff_ne_zero.mpr h0
    | add a b _ _ ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      exact v.map_add_lt ha hb
    | smul o a _ ha =>
      rw [map_smul, smul_eq_mul, map_mul, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv.map_le_one o)) ha
  exact lt_irrefl _ (key x hx)

theorem exists_leading_minors_ge_of_le_rank {C : Type} [Field C] (v : Valuation C NNReal)
    {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) {r : ℕ} (A : Set (Fin r → O))
    {c : O} (hc : c ≠ 0) (hA : ∀ x : Fin r → O, c • x ∈ Submodule.span O A) :
    ∀ n : ℕ, n ≤ r → ∃ t : ℕ → Fin r → O, (∀ i, i < n → t i ∈ A) ∧
      ∀ (m : ℕ) (hm : m ≤ r), m ≤ n → v (algebraMap O C c) ^ m ≤
        v (algebraMap O C (Matrix.of fun a i : Fin m => t i (Fin.castLE hm a)).det) := by
  have hvc : v (algebraMap O C c) ≠ 0 := by
    rw [Ne, v.zero_iff]
    intro h
    exact hc (hv.hom_inj (by rw [h, map_zero]))
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    intro m hm h0
    obtain rfl : m = 0 := Nat.le_zero.mp h0
    simp
  | succ n ih =>
    intro hn
    obtain ⟨t, htA, ht⟩ := ih (Nat.le_of_succ_le hn)
    let coef : Fin (n + 1) → O := fun a => (-1) ^ ((a : ℕ) + n) *
      (Matrix.of fun b i : Fin n => t i (Fin.castLE hn (a.succAbove b))).det
    let φ : (Fin r → O) →ₗ[O] O :=
      ∑ a : Fin (n + 1), coef a • LinearMap.proj (Fin.castLE hn a)
    have hφ : ∀ x, φ x = ∑ a : Fin (n + 1), coef a * x (Fin.castLE hn a) := by
      intro x
      simp [φ, LinearMap.sum_apply]
    have hdet : ∀ x, (Matrix.of fun a i : Fin (n + 1) =>
        Function.update t n x i (Fin.castLE hn a)).det = φ x := by
      intro x
      rw [hφ, Matrix.det_succ_column _ (Fin.last n)]
      refine Finset.sum_congr rfl fun a _ => ?_
      have : (Matrix.of fun a i : Fin (n + 1) =>
          Function.update t n x i (Fin.castLE hn a)).submatrix a.succAbove
          (Fin.last n).succAbove =
          Matrix.of fun b i : Fin n => t i (Fin.castLE hn (a.succAbove b)) := by
        ext b i
        simp [Function.update_of_ne (Nat.ne_of_lt i.isLt)]
      rw [this]
      simp only [coef, Matrix.of_apply, Fin.val_last, Function.update_self]
      ring
    have hval : φ (c • Pi.single (Fin.castLE hn (Fin.last n)) 1) =
        c * (Matrix.of fun a i : Fin n => t i (Fin.castLE (Nat.le_of_succ_le hn) a)).det := by
      rw [map_smul, smul_eq_mul, hφ, Finset.sum_eq_single (Fin.last n)]
      · congr 1
        simp only [coef, Pi.single_eq_same, mul_one, Fin.val_last, Fin.succAbove_last]
        rw [← two_mul, pow_mul]
        simp only [even_two, Even.neg_pow, one_pow, one_mul]
        rfl
      · intro b _ hb
        rw [Pi.single_eq_of_ne (fun h => hb (Fin.castLE_injective hn h)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hlow : v (algebraMap O C c) ^ (n + 1) ≤
        v (algebraMap O C (φ (c • Pi.single (Fin.castLE hn (Fin.last n)) 1))) := by
      rw [hval, map_mul, map_mul, pow_succ']
      exact mul_le_mul_right (ht n _ le_rfl) _
    obtain ⟨a, haA, ha⟩ := exists_mem_valuation_le_of_mem_span v hv A φ (hA _)
      (ne_of_gt (lt_of_lt_of_le (pow_pos (pos_iff_ne_zero.mpr hvc) _) hlow))
    refine ⟨Function.update t n a, ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · rw [Function.update_of_ne (Nat.ne_of_lt h)]
        exact htA i h
      · rw [Function.update_self]
        exact haA
    · intro m hm hmn
      rcases Nat.lt_or_eq_of_le hmn with h | rfl
      · have h' : m ≤ n := Nat.lt_succ_iff.mp h
        have : (Matrix.of fun b i : Fin m => Function.update t n a i (Fin.castLE hm b)) =
            Matrix.of fun b i : Fin m => t i (Fin.castLE hm b) := by
          ext b i
          simp [Function.update_of_ne (Nat.ne_of_lt (lt_of_lt_of_le i.isLt h'))]
        rw [this]
        exact ht m hm h'
      · rw [hdet]
        exact hlow.trans ha

theorem exists_leading_minors_ge :
    ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C],
      v.Integers O → ∀ (r : ℕ) (A : Set (Fin r → O)) (c : O), c ≠ 0 →
      (∀ x : Fin r → O, c • x ∈ Submodule.span O A) →
      ∃ t : Fin r → Fin r → O, (∀ i, t i ∈ A) ∧ ∀ s : Fin r,
        v (algebraMap O C c) ^ (s.val + 1) ≤
          v (algebraMap O C (Matrix.of fun a i : Fin (s.val + 1) =>
            t (Fin.castLE s.isLt i) (Fin.castLE s.isLt a)).det) := by
  intro C _ v O _ _ hv r A c hc hA
  obtain ⟨t, htA, ht⟩ := exists_leading_minors_ge_of_le_rank v hv A hc hA r le_rfl
  exact ⟨fun i => t i, fun i => htA i i.isLt, fun s => ht (s.val + 1) s.isLt s.isLt⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEllipticFunctionMulProdEqXy
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEllipticFunctionMulProdEqXy
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.EllipticModel

theorem exists_mul_prod_eq_xy (q : ℕ) [Fact q.Prime] (M : Mdl q) (φ : ℂ → ℂ) (hM : M.Ok) (hφ : Ell M.L φ) :
    ∃ (m : ℕ) (P : Fin m → ℂ) (A B : Polynomial ℂ),
      (∀ i, P i ∉ M.L.lattice ∧ meromorphicOrderAt φ (P i) < 0) ∧
      ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀,
        φ z * (∏ i, (Polynomial.X - Polynomial.C (M.x (P i)))).eval (M.x z) =
          A.eval (M.x z) + B.eval (M.x z) * M.y z := by
  obtain ⟨m, P, A, B, hP, h⟩ := GlobalTheory.EllipticPoles.exists_mul_prod_eq M.L φ hφ
  have hc : M.c ≠ 0 := hM.1
  set r : ℂ := M.ι.symm (M.W.b₂ / 12) with hr
  set a₁ : ℂ := M.ι.symm M.W.a₁ with ha₁
  set a₃ : ℂ := M.ι.symm M.W.a₃ with ha₃
  have hx : ∀ z, M.L.weierstrassP z = M.c ^ 2 * (M.x z + r) := by
    intro z
    simp only [Mdl.x, ← hr]
    field_simp
    ring
  have hy : ∀ z, M.L.derivWeierstrassP z = M.c ^ 3 * (2 * M.y z + a₁ * M.x z + a₃) := by
    intro z
    simp only [Mdl.y, ← ha₁, ← ha₃]
    field_simp
    ring
  let g : Polynomial ℂ := Polynomial.C (M.c ^ 2) * (Polynomial.X + Polynomial.C r)
  let k : ℂ := ((M.c ^ 2) ^ m)⁻¹
  refine ⟨m, P,
    Polynomial.C k * (A.comp g + B.comp g * Polynomial.C (M.c ^ 3) *
      (Polynomial.C a₁ * Polynomial.X + Polynomial.C a₃)),
    Polynomial.C k * (B.comp g * Polynomial.C (2 * M.c ^ 3)), hP, fun z₀ => ?_⟩
  filter_upwards [h z₀] with z hz
  have hg : g.eval (M.x z) = M.L.weierstrassP z := by
    rw [hx z]; simp [g]
  have hprod : ∏ i, (M.L.weierstrassP z - M.L.weierstrassP (P i)) =
      (M.c ^ 2) ^ m * ∏ i, (M.x z - M.x (P i)) := by
    have : ∀ i, M.L.weierstrassP z - M.L.weierstrassP (P i) = M.c ^ 2 * (M.x z - M.x (P i)) := by
      intro i; rw [hx z, hx (P i)]; ring
    simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hk : k * (M.c ^ 2) ^ m = 1 := inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hc))
  rw [hprod, hy z] at hz
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_comp, hg]
  linear_combination k * hz - (φ z * ∏ i, (M.x z - M.x (P i))) * hk

end GlobalTheory.EllipticModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEllipticFunctionMulProdEqXyStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ellipticFunction_mul_prod_eq_xy : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (φ : ℂ → ℂ), M.Ok → Ell M.L φ → ∃ (m : ℕ) (P : Fin m → ℂ) (A B : Polynomial ℂ), (∀ i, P i ∉ M.L.lattice ∧ meromorphicOrderAt φ (P i) < 0) ∧ ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀, φ z * (∏ i, (Polynomial.X - Polynomial.C (M.x (P i)))).eval (M.x z) = A.eval (M.x z) + B.eval (M.x z) * M.y z := by
  first | exact @GlobalTheory.EllipticModel.exists_mul_prod_eq_xy | exact GlobalTheory.EllipticModel.exists_mul_prod_eq_xy | (intros; apply GlobalTheory.EllipticModel.exists_mul_prod_eq_xy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesEvalTsumUnitDiscPropertiesStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesEvalTsumUnitDiscPropertiesAlt
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem powerSeriesEvalTsum_unitDisc_properties : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (x : K), ‖x‖ < 1 → (∀ f : PowerSeries K, Bdd f → PowerSeriesHasSumAt f x (ev1 f x)) ∧ (∀ f g : PowerSeries K, Bdd f → Bdd g → ev1 (f + g) x = ev1 f x + ev1 g x ∧ ev1 (f - g) x = ev1 f x - ev1 g x ∧ ev1 (f * g) x = ev1 f x * ev1 g x) ∧ (∀ a : K, ev1 (PowerSeries.C a) x = a) ∧ ev1 PowerSeries.X x = x ∧ (∀ P : Polynomial K, Bdd (P : PowerSeries K) ∧ ev1 (P : PowerSeries K) x = P.eval x) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → PowerSeries K), (∀ i ∈ t, Bdd (f i)) → ev1 (∏ i ∈ t, f i) x = ∏ i ∈ t, ev1 (f i) x) ∧ (∀ f : PowerSeries K, Intg f → ‖ev1 f x‖ ≤ 1 ∧ ‖ev1 f x - PowerSeries.coeff 0 f‖ ≤ ‖x‖ ∧ ‖ev1 f x - PowerSeries.coeff 0 f - PowerSeries.coeff 1 f * x‖ ≤ ‖x‖ ^ 2) ∧ (∀ (f g : PowerSeries K), Intg g → PowerSeries.constantCoeff g = 0 → Bdd f → ev1 (f.subst g) x = ev1 f (ev1 g x)) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (g h : PowerSeries K), Bdd F → Intg g → Intg h → PowerSeries.constantCoeff g = 0 → PowerSeries.constantCoeff h = 0 → ev1 (MvPowerSeries.subst (![g, h] : Fin 2 → MvPowerSeries Unit K) F) x = ev F ![ev1 g x, ev1 h x]) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (y : K), ‖y‖ < 1 → Intg F → Intg (shift1 F y) ∧ ev1 (shift1 F y) x = ev F ![x, y]) ∧ (∀ f : PowerSeries K, ev1 f 0 = PowerSeries.coeff 0 f) := by
  intro K _ _ _ x hx
  have A := GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, BetaSesquilinearity, B9, lowerOffDiagonalCoeff⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  obtain ⟨C1, C2, C3, C4, C5, C6, C7, C8⟩ := GlobalTheory.T.mvPowerSeriesEvalTsum_openPolydisc_properties K Unit (fun _ => x) (fun _ => hx)
  have hev : ∀ (f : PowerSeries K) (t : K), ev1 f t = ev f (fun _ : Unit => t) := A.2.1
  have P1 : ∀ f : PowerSeries K, Bdd f → PowerSeriesHasSumAt f x (ev1 f x) := by
    intro f hf
    rw [A.2.2.1, hev]
    exact C1 f hf
  have P2 : ∀ f g : PowerSeries K, Bdd f → Bdd g → ev1 (f + g) x = ev1 f x + ev1 g x ∧
      ev1 (f - g) x = ev1 f x - ev1 g x ∧ ev1 (f * g) x = ev1 f x * ev1 g x := by
    intro f g hf hg
    simp only [hev]
    exact C2 f g hf hg
  have P3 : ∀ a : K, ev1 (PowerSeries.C a) x = a := by
    intro a
    rw [hev]
    exact C3 a
  have P4 : ev1 PowerSeries.X x = x := by
    rw [hev]
    exact C4 ()
  have hBddX : Bdd (PowerSeries.X : PowerSeries K) := (B3 _ 0).2.2 (B5 ()).1
  have hBddP : ∀ P : Polynomial K, Bdd (P : PowerSeries K) := by
    intro P
    rw [(lowerOffDiagonalCoeff _).2]
    refine ⟨∑ i ∈ P.support, ‖P.coeff i‖, fun m => ?_⟩
    rw [Polynomial.coeff_coe]
    by_cases hm : m ∈ P.support
    · exact Finset.single_le_sum (f := fun i => ‖P.coeff i‖) (fun i _ => norm_nonneg _) hm
    · have h0 : P.coeff m = 0 := by simpa using hm
      rw [h0, norm_zero]
      exact Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have P5 : ∀ P : Polynomial K, Bdd (P : PowerSeries K) ∧ ev1 (P : PowerSeries K) x = P.eval x := by
    intro P
    refine ⟨hBddP P, ?_⟩
    refine Polynomial.induction_on P ?_ ?_ ?_
    · intro a
      rw [Polynomial.coe_C, P3, Polynomial.eval_C]
    · intro p q hp hq
      rw [Polynomial.coe_add, (P2 _ _ (hBddP p) (hBddP q)).1, hp, hq, Polynomial.eval_add]
    · intro m a ih
      have e : (Polynomial.C a * Polynomial.X ^ (m + 1) : Polynomial K) =
          (Polynomial.C a * Polynomial.X ^ m) * Polynomial.X := by ring
      rw [e, Polynomial.coe_mul, Polynomial.coe_X, (P2 _ _ (hBddP _) hBddX).2.2, ih, P4]
      simp
  have P6 : ∀ (ι : Type) (t : Finset ι) (f : ι → PowerSeries K), (∀ i ∈ t, Bdd (f i)) →
      ev1 (∏ i ∈ t, f i) x = ∏ i ∈ t, ev1 (f i) x := by
    intro ι t f hf
    classical
    induction t using Finset.induction_on with
    | empty =>
      have h1 : (1 : PowerSeries K) = PowerSeries.C 1 := by simp
      rw [Finset.prod_empty, Finset.prod_empty, h1, P3]
    | @insert j s hj ih =>
      have hs : ∀ i ∈ s, Bdd (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert hj, Finset.prod_insert hj,
        (P2 _ _ (hf j (Finset.mem_insert_self j s)) ((B6 ι s f).2 hs).1).2.2, ih hs]
  have P7 : ∀ f : PowerSeries K, Intg f → ‖ev1 f x‖ ≤ 1 ∧
      ‖ev1 f x - PowerSeries.coeff 0 f‖ ≤ ‖x‖ ∧
      ‖ev1 f x - PowerSeries.coeff 0 f - PowerSeries.coeff 1 f * x‖ ≤ ‖x‖ ^ 2 := by
    have hI : ∀ f : PowerSeries K, Intg f → ‖ev1 f x‖ ≤ 1 := fun f hf => by
      rw [hev]
      exact (C5 f hf).1
    have hsh : ∀ f : PowerSeries K, Intg f →
        Intg (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f) ∧
        ev1 f x = PowerSeries.coeff 0 f +
          x * ev1 (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f) x := by
      intro f hf
      have hg : Intg (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f) := by
        rw [(lowerOffDiagonalCoeff _).1]
        intro m
        rw [PowerSeries.coeff_mk]
        exact (lowerOffDiagonalCoeff f).1.mp hf (m + 1)
      refine ⟨hg, ?_⟩
      have hgb := (B3 _ 0).2.2 hg
      have e : ev1 f x = ev1 ((PowerSeries.X * PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f) +
          PowerSeries.C (PowerSeries.constantCoeff f)) x :=
        congrArg (fun F => ev1 F x) (PowerSeries.eq_X_mul_shift_add_const f)
      rw [e, (P2 _ _ (B2 _ _ hBddX hgb).2.2
        (show Bdd (PowerSeries.C (PowerSeries.constantCoeff f)) from (B4 _).1)).1, (P2 _ _ hBddX hgb).2.2, P4, P3,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      ring
    intro f hf
    obtain ⟨hg, e1⟩ := hsh f hf
    obtain ⟨hh, e2⟩ := hsh _ hg
    rw [PowerSeries.coeff_mk, zero_add] at e2
    refine ⟨hI f hf, ?_, ?_⟩
    · rw [e1, add_sub_cancel_left, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hI _ hg)
    · have key : ∀ a b d : K, a + x * (b + x * d) - a - b * x = x ^ 2 * d := by
        intro a b d
        ring
      rw [e1, e2, key, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hI _ hh)
  have P8 : ∀ (f g : PowerSeries K), Intg g → PowerSeries.constantCoeff g = 0 → Bdd f →
      ev1 (f.subst g) x = ev1 f (ev1 g x) := by
    intro f g hg h0 hf
    rw [hev (f.subst g), hev g]
    exact C8 g f hg h0 hf
  have P9 : ∀ (F : MvPowerSeries (Fin 2) K) (g h : PowerSeries K), Bdd F → Intg g → Intg h →
      PowerSeries.constantCoeff g = 0 → PowerSeries.constantCoeff h = 0 →
      ev1 (MvPowerSeries.subst (![g, h] : Fin 2 → MvPowerSeries Unit K) F) x =
        ev F ![ev1 g x, ev1 h x] := by
    intro F g h hF hg hh hg0 hh0
    rw [hev, C7 (Fin 2) ![g, h] F (fun j => by fin_cases j; exacts [hg, hh])
      (fun j => by fin_cases j; exacts [hg0, hh0]) hF]
    congr 1
    funext j
    fin_cases j <;> simp [hev]
  have product_first_zeroth_parts : ∀ (F : MvPowerSeries (Fin 2) K) (y : K), ‖y‖ < 1 → Intg F →
      Intg (shift1 F y) ∧ ev1 (shift1 F y) x = ev F ![x, y] := by
    intro F y hy hF
    have hs : ∀ i, Small ((![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) i) := by
      intro i
      fin_cases i
      · exact B5 ()
      · exact (B4 y).2.2 hy
    have hFb : Bdd F := ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K (Fin 2)).2.2.1 F 0).2.2 hF
    have D := GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K (Fin 2) Unit _ F hs hFb
    rw [A.2.2.2.2.1 F y]
    refine ⟨D.2.2.1 hF, ?_⟩
    rw [hev, C6 (Fin 2) _ F hs hFb]
    congr 1
    funext j
    fin_cases j
    · exact C4 ()
    · exact C3 y
  have product_first_partition : ∀ f : PowerSeries K, ev1 f 0 = PowerSeries.coeff 0 f := by
    intro f
    unfold ev1
    rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
    simp
  exact ⟨P1, P2, P3, P4, P5, P6, P7, P8, P9, product_first_zeroth_parts, product_first_partition⟩

end GlobalTheory.ConvSer
end

open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (x : K), ‖x‖ < 1 → (∀ f : PowerSeries K, Bdd f → PowerSeriesHasSumAt f x (ev1 f x)) ∧ (∀ f g : PowerSeries K, Bdd f → Bdd g → ev1 (f + g) x = ev1 f x + ev1 g x ∧ ev1 (f - g) x = ev1 f x - ev1 g x ∧ ev1 (f * g) x = ev1 f x * ev1 g x) ∧ (∀ a : K, ev1 (PowerSeries.C a) x = a) ∧ ev1 PowerSeries.X x = x ∧ (∀ P : Polynomial K, Bdd (P : PowerSeries K) ∧ ev1 (P : PowerSeries K) x = P.eval x) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → PowerSeries K), (∀ i ∈ t, Bdd (f i)) → ev1 (∏ i ∈ t, f i) x = ∏ i ∈ t, ev1 (f i) x) ∧ (∀ f : PowerSeries K, Intg f → ‖ev1 f x‖ ≤ 1 ∧ ‖ev1 f x - PowerSeries.coeff 0 f‖ ≤ ‖x‖ ∧ ‖ev1 f x - PowerSeries.coeff 0 f - PowerSeries.coeff 1 f * x‖ ≤ ‖x‖ ^ 2) ∧ (∀ (f g : PowerSeries K), Intg g → PowerSeries.constantCoeff g = 0 → Bdd f → ev1 (f.subst g) x = ev1 f (ev1 g x)) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (g h : PowerSeries K), Bdd F → Intg g → Intg h → PowerSeries.constantCoeff g = 0 → PowerSeries.constantCoeff h = 0 → ev1 (MvPowerSeries.subst (![g, h] : Fin 2 → MvPowerSeries Unit K) F) x = ev F ![ev1 g x, ev1 h x]) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (y : K), ‖y‖ < 1 → Intg F → Intg (shift1 F y) ∧ ev1 (shift1 F y) x = ev F ![x, y]) ∧ (∀ f : PowerSeries K, ev1 f 0 = PowerSeries.coeff 0 f) := by
  first | exact @GlobalTheory.ConvSer.powerSeriesEvalTsum_unitDisc_properties | exact GlobalTheory.ConvSer.powerSeriesEvalTsum_unitDisc_properties | (intros; apply GlobalTheory.ConvSer.powerSeriesEvalTsum_unitDisc_properties <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorEqZeroOfForallGeometricPoint
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem exists_algHom_ker_eq_of_isMaximal (F B : Type) [Field F] [IsAlgClosed F] [CommRing B]
    [Algebra F B] [Module.Finite F B] (m : Ideal B) [m.IsMaximal] :
    ∃ ψ : B →ₐ[F] F, ∀ b, ψ b = 0 → b ∈ m := by
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  have hb : Function.Bijective (algebraMap F (B ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : F ≃ₐ[F] (B ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId F (B ⧸ m)) hb
  refine ⟨(e.symm : (B ⧸ m) →ₐ[F] F).comp (Ideal.Quotient.mkₐ F m), fun b h => ?_⟩
  have h' : e.symm (Ideal.Quotient.mk m b) = 0 := h
  rw [map_eq_zero_iff _ e.symm.injective] at h'
  exact Ideal.Quotient.eq_zero_iff_mem.mp h'

theorem tensor_eq_zero_of_forall_geometric_point :
    ∀ (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] [IsReduced (TensorProduct O F A)] (M : Type) [AddCommGroup M] [Module O M] [Module.Flat O M] (t : TensorProduct O A M), (∀ φ : A →ₐ[O] F, TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[O] M) t = 0) → t = 0 := by
  intro O F _ _ _ _ hinj A _ _ _ _ _ M _ _ _ t ht
  classical
  haveI : IsArtinianRing (TensorProduct O F A) := IsArtinianRing.of_finite F _
  have hpt : ∀ m : MaximalSpectrum (TensorProduct O F A),
      ∃ ψ : TensorProduct O F A →ₐ[F] F, ∀ b, ψ b = 0 → b ∈ m.asIdeal := fun m =>
    haveI := m.isMaximal
    exists_algHom_ker_eq_of_isMaximal F _ m.asIdeal
  choose ψ hψ using hpt
  let φ : MaximalSpectrum (TensorProduct O F A) → (A →ₐ[O] F) := fun m =>
    ((ψ m).restrictScalars O).comp Algebra.TensorProduct.includeRight
  let L : A →ₗ[O] (MaximalSpectrum (TensorProduct O F A) → F) :=
    LinearMap.pi fun m => (φ m).toLinearMap
  have hR : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[O] TensorProduct O F A) :=
    Algebra.TensorProduct.includeRight_injective hinj
  have hL : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    apply hR
    rw [map_zero]
    have hmem : (Algebra.TensorProduct.includeRight a : TensorProduct O F A) ∈
        Ideal.jacobson (⊥ : Ideal (TensorProduct O F A)) := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      rintro J ⟨-, hJ⟩
      exact hψ ⟨J, hJ⟩ _ (congrFun ha ⟨J, hJ⟩)
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := TensorProduct O F A)
    have h2 := Ideal.pow_mem_pow hmem n
    rw [hn] at h2
    exact IsNilpotent.eq_zero ⟨n, by simpa using h2⟩
  have hLM : Function.Injective (L.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap L hL
  haveI : Fintype (MaximalSpectrum (TensorProduct O F A)) := Fintype.ofFinite _
  apply hLM
  rw [map_zero]
  apply (TensorProduct.piLeft O M (fun _ : MaximalSpectrum (TensorProduct O F A) => F)).injective
  rw [map_zero]
  funext m
  have key : ∀ s : TensorProduct O A M,
      TensorProduct.piLeft O M (fun _ : MaximalSpectrum (TensorProduct O F A) => F)
        (L.rTensor M s) m
      = TensorProduct.map (φ m).toLinearMap (LinearMap.id : M →ₗ[O] M) s := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [L, TensorProduct.piLeft]
    | add s s' h h' => rw [map_add (f := _), map_add (f := _), Pi.add_apply, h, h', map_add (f := _)]
  rw [key, ht]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinorsDisjointColumnsHarmonic
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem _root_.GlobalTheory.minorHarm_pderiv_comm {σ k : Type*} [CommRing k] (i j : σ)
    (p : MvPolynomial σ k) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  have h : ⁅MvPolynomial.pderiv (R := k) i, MvPolynomial.pderiv (R := k) j⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro n
    rw [Derivation.commutator_apply, MvPolynomial.pderiv_X, MvPolynomial.pderiv_X]
    by_cases hj : j = n <;> by_cases hi : i = n <;>
      simp [Pi.single_apply, hj, hi]
  have := DFunLike.congr_fun h p
  rw [Derivation.commutator_apply] at this
  simpa [sub_eq_zero] using this

theorem _root_.GlobalTheory.minorHarm_pderiv_eq_zero {σ k : Type*} [CommRing k] {S : Set σ}
    {p : MvPolynomial σ k} (hp : p ∈ MvPolynomial.supported k S) {v : σ} (hv : v ∉ S) :
    MvPolynomial.pderiv v p = 0 := by
  classical
  rw [MvPolynomial.supported_eq_adjoin_X] at hp
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact MvPolynomial.pderiv_X_of_ne (fun h => hv (h ▸ hs))
  | algebraMap r => rw [MvPolynomial.algebraMap_eq, MvPolynomial.pderiv_C]
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
  | mul x y _ _ hx hy => rw [MvPolynomial.pderiv_mul, hx, hy]; simp

private theorem pderiv_mem_supported' {σ k : Type*} [CommRing k] {S : Set σ}
    {p : MvPolynomial σ k} (hp : p ∈ MvPolynomial.supported k S) (w : σ) :
    MvPolynomial.pderiv w p ∈ MvPolynomial.supported k S := by
  classical
  rw [MvPolynomial.supported_eq_adjoin_X] at hp ⊢
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    rw [MvPolynomial.pderiv_X]
    by_cases h : w = s
    · subst h; simp only [Pi.single_eq_same]; exact Subalgebra.one_mem _
    · rw [Pi.single_eq_of_ne' h]; exact Subalgebra.zero_mem _
  | algebraMap r =>
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.pderiv_C]; exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hx hy
  | mul x y hx' hy' hx hy =>
    rw [MvPolynomial.pderiv_mul]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx hy') (Subalgebra.mul_mem _ hx' hy)

theorem _root_.GlobalTheory.minors_disjoint_columns_harmonic :
    ∀ (k : Type) [CommRing k] (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ) (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ) (P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k), P = (∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s) → ∀ τ τ' : T, (∀ i i', col τ i ≠ col τ' i') → ∀ (i : Fin (r τ)) (i' : Fin (r τ')), ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : T, Fin (r τ)), b) (MvPolynomial.pderiv ((⟨τ', i'⟩ : Σ τ : T, Fin (r τ)), b) P) = 0 := by
  intro k _ T _ _ r n col m P hP τ τ' hdisj i i'
  let S : Set ((Σ τ : T, Fin (r τ)) × Fin n) := {x | ∃ c, col x.1.1 c = x.2}
  have hPS : P ∈ MvPolynomial.supported k S := by
    rw [hP]
    refine Subalgebra.prod_mem _ fun σ _ => Subalgebra.prod_mem _ fun s _ => ?_
    refine Subalgebra.pow_mem _ ?_ _
    rw [Matrix.det_apply]
    refine Subalgebra.sum_mem _ fun π _ => ?_
    rw [Units.smul_def]
    refine Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun a _ => ?_) _
    rw [Matrix.of_apply, MvPolynomial.supported_eq_adjoin_X]
    exact Algebra.subset_adjoin ⟨_, ⟨_, rfl⟩, rfl⟩
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : ∃ c, col τ c = b
  · obtain ⟨c, rfl⟩ := hb
    have hnot : ((⟨τ', i'⟩ : Σ τ : T, Fin (r τ)), col τ c) ∉ S := by
      rintro ⟨c', hc'⟩
      exact hdisj c c' hc'.symm
    rw [_root_.GlobalTheory.minorHarm_pderiv_eq_zero hPS hnot, map_zero]
  · have hnot : ((⟨τ, i⟩ : Σ τ : T, Fin (r τ)), b) ∉ S := hb
    exact _root_.GlobalTheory.minorHarm_pderiv_eq_zero
      (pderiv_mem_supported' hPS _) hnot

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfCongrJet
set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.JetOnly

variable {k : Type} [CommRing k] {d : ℕ}

theorem coeff_Dof_congr (F : Fin d → PS k 2 d) (v : Fin d → k) (n : ℕ) (f g : PS k 1 d)
    (h : ∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n + 1 → coeff mo f = coeff mo g)
    (mo : Fin 1 × Fin d →₀ ℕ) (hmo : mo.degree ≤ n) :
    coeff mo (Dof F v f) = coeff mo (Dof F v g) := by
  classical
  unfold Dof
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = mo := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : p.1.degree + p.2.degree = mo.degree := by rw [← hp', map_add (f := _)]
  rw [coeff_pderiv, coeff_pderiv, h]
  rw [map_add (f := _), Finsupp.degree_single]
  omega

theorem coeff_iterate_Dof_congr (F : Fin d → PS k 2 d) (v : Fin d → k) (r : ℕ) :
    ∀ (n : ℕ) (f g : PS k 1 d),
      (∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n + r → coeff mo f = coeff mo g) →
      ∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n →
        coeff mo ((Dof F v)^[r] f) = coeff mo ((Dof F v)^[r] g) := by
  induction r with
  | zero => intro n f g h mo hmo; exact h mo hmo
  | succ r ih =>
    intro n f g h mo hmo
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih n _ _ (coeff_Dof_congr F v (n + r) f g h) mo hmo

theorem coeff_foldr_Dof_congr (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k) (m : ι → ℕ)
    (f g : PS k 1 d) (L : List ι) :
    ∀ n : ℕ,
      (∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n + (L.map m).sum → coeff mo f = coeff mo g) →
      ∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n →
        coeff mo (L.foldr (fun l s => (Dof F (u l))^[m l] s) f) =
          coeff mo (L.foldr (fun l s => (Dof F (u l))^[m l] s) g) := by
  induction L with
  | nil => intro n h mo hmo; exact h mo hmo
  | cons l L ih =>
    intro n h mo hmo
    rw [List.foldr_cons, List.foldr_cons]
    refine coeff_iterate_Dof_congr F (u l) (m l) n _ _ (ih (n + m l) fun mo' h' => h mo' ?_) mo hmo
    rw [List.map_cons, List.sum_cons]
    omega

theorem coeff_DmonOf_congr (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (m : ι →₀ ℕ) (f g : PS k 1 d) (n : ℕ)
    (h : ∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n + m.degree → coeff mo f = coeff mo g)
    (mo : Fin 1 × Fin d →₀ ℕ) (hmo : mo.degree ≤ n) :
    coeff mo (DmonOf F u m f) = coeff mo (DmonOf F u m g) := by
  unfold DmonOf
  refine coeff_foldr_Dof_congr F u m f g _ n (fun mo' h' => h mo' ?_) mo hmo
  rwa [Finset.sum_map_toList, ← Finsupp.degree_eq_sum] at h'

end GlobalTheory.JetOnly

namespace GlobalTheory

theorem constantCoeff_DmonOf_congr_jet :
    ∀ (k : Type) [CommRing k] (d : ℕ) (F : Fin d → PS k 2 d) (ι : Type) [Fintype ι]
      (u : ι → Fin d → k) (m : ι →₀ ℕ) (f g : PS k 1 d),
      (∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ m.degree → coeff mo f = coeff mo g) →
      constantCoeff (DmonOf F u m f) = constantCoeff (DmonOf F u m g) := by
  intro k _ d F ι _ u m f g h
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]
  exact JetOnly.coeff_DmonOf_congr F u m f g 0 (fun mo h' => h mo (by simpa using h')) 0 (by simp)

end GlobalTheory
end
