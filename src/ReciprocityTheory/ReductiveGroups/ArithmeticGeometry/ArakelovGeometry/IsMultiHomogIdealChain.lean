module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsHomogeneousGrL
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AbsProdSubProdSubLinLe
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.SupportSubsetMonoBox
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem le_of_mem_support_mHom {a : K → ℕ} {f : MRing ι} (hf : f ∈ mHom ι a) {m : (Σ k, ι k) →₀ ℕ}
    (hm : m ∈ f.support) (p : Σ k, ι k) : m p ≤ a p.1 := by
  classical
  revert m
  induction hf using Submodule.span_induction with
  | mem s hs =>
    intro m hm
    rw [← hs m hm p.1]
    exact Finset.single_le_sum (f := fun i => m ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
    · exact hx h
    · exact hy h
  | smul c x _ hx =>
    intro m hm
    exact hx (MvPolynomial.support_smul hm)

theorem finite_monoBox (a : K → ℕ) :
    {m : (Σ k, ι k) →₀ ℕ | ∀ p, m p ≤ a p.1}.Finite := by
  have hfin : (Set.pi Set.univ fun p : (Σ k, ι k) => Set.Iic (a p.1)).Finite :=
    Set.Finite.pi fun p => Set.finite_Iic _
  refine (hfin.preimage (Finsupp.equivFunOnFinite.injective.injOn)).subset ?_
  intro m hm p _
  exact hm p

def monoBox (a : K → ℕ) : Finset ((Σ k, ι k) →₀ ℕ) := (finite_monoBox (ι := ι) a).toFinset

theorem support_subset_monoBox {a : K → ℕ} {f : MRing ι} (hf : f ∈ mHom ι a) :
    f.support ⊆ monoBox a := by
  intro m hm
  simp only [monoBox, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact fun p => le_of_mem_support_mHom hf hm p

theorem finite_mPiece (J : Ideal (MRing ι)) (a : K → ℕ) {p : ℕ} (hp : 0 < p)
    (hpJ : (p : MRing ι) ∈ J) : Finite (mPiece J a) := by
  classical
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  let g : (monoBox (ι := ι) a → Fin (q + 1)) → MRing ι ⧸ J := fun c =>
    Ideal.Quotient.mk J (∑ m : monoBox (ι := ι) a,
      MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (((c m : ℕ) : ℤ)))
  have hsub : (mPiece J a : Set (MRing ι ⧸ J)) ⊆ Set.range g := by
    intro x hx
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
    have hq : (0 : ℤ) < ((q + 1 : ℕ) : ℤ) := by omega
    refine ⟨fun m => ⟨((AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) % ((q + 1 : ℕ) : ℤ)).toNat, ?_⟩, ?_⟩
    · have h0 := Int.emod_nonneg (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) hq.ne'
      have h1 := Int.emod_lt_of_pos (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) hq
      omega
    · show Ideal.Quotient.mk J (∑ m : monoBox (ι := ι) a, MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ)
          ((((AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ)) =
        Ideal.Quotient.mk J f
      rw [Ideal.Quotient.eq]
      have hf' : f = ∑ m : monoBox (ι := ι) a,
          MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) := by
        rw [Finset.sum_coe_sort (monoBox a) (fun m => MvPolynomial.monomial m (AddMonoidAlgebra.coeff f m))]
        conv_lhs => rw [MvPolynomial.as_sum f]
        refine Finset.sum_subset (support_subset_monoBox hf) (fun m _ hm => ?_)
        simp only [MvPolynomial.mem_support_iff, ne_eq, not_not] at hm
        simp [hm]
      have hP : ((q + 1 : ℕ) : MRing ι) ∈ J := hpJ
      have hdiff : ∀ m : monoBox (ι := ι) a, MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ)
          ((((AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ) -
          MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) ∈ J := by
        intro m
        have h0 := Int.emod_nonneg (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) hq.ne'
        rw [Int.toNat_of_nonneg h0, ← map_sub, Int.emod_def]
        have e : AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ) - ((q + 1 : ℕ) : ℤ) *
            (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ) / ((q + 1 : ℕ) : ℤ)) -
            AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ) =
            ((q + 1 : ℕ) : ℤ) * (-(AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ) / ((q + 1 : ℕ) : ℤ))) := by
          ring
        rw [e, ← MvPolynomial.C_mul_monomial, map_natCast]
        exact J.mul_mem_right _ hP
      have e2 : (∑ m : monoBox (ι := ι) a, MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ)
          ((((AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ)) - f =
          ∑ m : monoBox (ι := ι) a, (MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ)
          ((((AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ) -
          MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ))) := by
        rw [Finset.sum_sub_distrib, ← hf']
      rw [e2]
      exact Ideal.sum_mem _ fun m _ => hdiff m
  exact ((Set.finite_range g).subset hsub).to_subtype

theorem card_mPiece_pos (J : Ideal (MRing ι)) (a : K → ℕ) {p : ℕ} (hp : 0 < p)
    (hpJ : (p : MRing ι) ∈ J) : 0 < Nat.card (mPiece J a) := by
  haveI := finite_mPiece J a hp hpJ
  exact Nat.card_pos

theorem card_mPiece_irrel {q : Ideal (MRing ι)} {k : K} (hk : ∀ i, (X ⟨k, i⟩ : MRing ι) ∈ q)
    {a : K → ℕ} (ha : 0 < a k) : Nat.card (mPiece q a) = 1 := by
  classical
  have hmem : ∀ f ∈ mHom ι a, f ∈ q := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem s hs =>
      rw [MvPolynomial.as_sum s]
      refine Ideal.sum_mem _ fun m hm => ?_
      have hsum := hs m hm k
      obtain ⟨i, hi⟩ : ∃ i, 0 < m ⟨k, i⟩ := by
        by_contra hc
        push_neg at hc
        have h0 : ∑ i, m ⟨k, i⟩ = 0 := Finset.sum_eq_zero fun i _ => by have := hc i; omega
        omega
      have e : MvPolynomial.monomial m (AddMonoidAlgebra.coeff s m) =
          MvPolynomial.X ⟨k, i⟩ * MvPolynomial.monomial (m - Finsupp.single ⟨k, i⟩ 1) (AddMonoidAlgebra.coeff s m) := by
        rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
          add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hi)]
      rw [e]
      exact q.mul_mem_right _ (hk i)
    | zero => exact q.zero_mem
    | add x y _ _ hx hy => exact q.add_mem hx hy
    | smul c x _ hx => exact Submodule.smul_of_tower_mem q c hx
  have hzero : ∀ x : mPiece q a, x = 0 := by
    rintro ⟨x, hx⟩
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
    apply Subtype.ext
    show Ideal.Quotient.mk q f = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmem f hf)
  haveI : Unique (mPiece q a) := ⟨⟨0⟩, hzero⟩
  exact Nat.card_unique

theorem card_mPiece_mono {J J' : Ideal (MRing ι)} (h : J ≤ J') (a : K → ℕ) [Finite (mPiece J a)] :
    Nat.card (mPiece J' a) ≤ Nat.card (mPiece J a) := by
  have hmap : ∀ x ∈ mPiece J a, Ideal.Quotient.factor h x ∈ mPiece J' a := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨g, hg, ?_⟩
    show Ideal.Quotient.mk J' g = Ideal.Quotient.factor h (Ideal.Quotient.mk J g)
    rw [Ideal.Quotient.factor_mk]
  refine Nat.card_le_card_of_surjective (fun x => ⟨Ideal.Quotient.factor h x, hmap x x.2⟩) ?_
  rintro ⟨y, hy⟩
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hy
  refine ⟨⟨Ideal.Quotient.mk J g, Submodule.mem_map.mpr ⟨g, hg, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  show Ideal.Quotient.factor h (Ideal.Quotient.mk J g) = Ideal.Quotient.mk J' g
  rw [Ideal.Quotient.factor_mk]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section Scalar

theorem abs_prod_le_pow {α : Type*} (s : Finset α) (y : α → ℝ) {Y : ℝ} (hy : ∀ i ∈ s, |y i| ≤ Y) :
    |∏ i ∈ s, y i| ≤ Y ^ s.card := by
  rw [Finset.abs_prod]
  calc ∏ i ∈ s, |y i| ≤ ∏ _i ∈ s, Y := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hy
    _ = Y ^ s.card := Finset.prod_const Y

theorem card_filter_lt_add_gt {α : Type*} [LinearOrder α] (s : Finset α) {i : α} (hi : i ∈ s) :
    (s.filter (· < i)).card + (s.filter (i < ·)).card ≤ s.card - 1 := by
  rw [← Finset.card_erase_of_mem hi, ← Finset.card_union_of_disjoint
    (Finset.disjoint_filter.mpr fun j _ h1 h2 => lt_asymm h1 h2)]
  refine Finset.card_le_card fun j hj => ?_
  simp only [Finset.mem_union, Finset.mem_filter] at hj
  rw [Finset.mem_erase]
  rcases hj with ⟨hj, h⟩ | ⟨hj, h⟩
  · exact ⟨ne_of_lt h, hj⟩
  · exact ⟨ne_of_gt h, hj⟩

theorem prod_sub_eq_sum {α : Type*} [LinearOrder α] (s : Finset α) (y ε : α → ℝ) :
    ∏ i ∈ s, y i - ∏ i ∈ s, (y i - ε i) =
      ∑ i ∈ s, ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j := by
  have h := Finset.prod_add_ordered s y (fun i => -ε i)
  simp only [← sub_eq_add_neg] at h
  rw [h]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

theorem abs_prod_sub_prod_le {α : Type*} [LinearOrder α] (s : Finset α) (y ε : α → ℝ) {Y E : ℝ}
    (hY : 1 ≤ Y) (hE : 0 ≤ E) (hy : ∀ i ∈ s, |y i| ≤ Y) (hε : ∀ i ∈ s, |ε i| ≤ E) :
    |∏ i ∈ s, y i - ∏ i ∈ s, (y i - ε i)| ≤ s.card * E * (Y + E) ^ (s.card - 1) := by
  rw [prod_sub_eq_sum]
  have hYE : 1 ≤ Y + E := by linarith
  calc |∑ i ∈ s, ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j|
      ≤ ∑ i ∈ s, |ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, E * (Y + E) ^ (s.card - 1) := Finset.sum_le_sum fun i hi => ?_
    _ = s.card * E * (Y + E) ^ (s.card - 1) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [abs_mul, abs_mul]
  have h1 : |∏ j ∈ s with j < i, (y j - ε j)| ≤ (Y + E) ^ (s.filter (· < i)).card :=
    abs_prod_le_pow _ _ fun j hj => by
      have hj' := (Finset.mem_filter.mp hj).1
      exact (abs_sub _ _).trans (add_le_add (hy j hj') (hε j hj'))
  have h2 : |∏ j ∈ s with i < j, y j| ≤ (Y + E) ^ (s.filter (i < ·)).card :=
    abs_prod_le_pow _ _ fun j hj => (hy j (Finset.mem_filter.mp hj).1).trans (by linarith)
  have hc := card_filter_lt_add_gt s hi
  calc |ε i| * |∏ j ∈ s with j < i, (y j - ε j)| * |∏ j ∈ s with i < j, y j|
      ≤ E * (Y + E) ^ (s.filter (· < i)).card * (Y + E) ^ (s.filter (i < ·)).card := by
        gcongr
        exact hε i hi
    _ = E * (Y + E) ^ ((s.filter (· < i)).card + (s.filter (i < ·)).card) := by rw [pow_add]; ring
    _ ≤ E * (Y + E) ^ (s.card - 1) := by gcongr <;> first | exact hYE | omega

theorem abs_prod_sub_prod_sub_lin_le {α : Type*} [LinearOrder α] (s : Finset α) (y ε : α → ℝ) {Y E : ℝ}
    (hY : 1 ≤ Y) (hE : 0 ≤ E) (hy : ∀ i ∈ s, |y i| ≤ Y) (hε : ∀ i ∈ s, |ε i| ≤ E) :
    |∏ i ∈ s, y i - ∏ i ∈ s, (y i - ε i) -
        ∑ i ∈ s, ε i * (∏ j ∈ s with j < i, y j) * ∏ j ∈ s with i < j, y j| ≤
      s.card * ((s.card - 1 : ℕ) : ℝ) * E ^ 2 * (Y + E) ^ (s.card - 2) := by
  rw [prod_sub_eq_sum, ← Finset.sum_sub_distrib]
  have hYE : 1 ≤ Y + E := by linarith
  calc |∑ i ∈ s, (ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j -
          ε i * (∏ j ∈ s with j < i, y j) * ∏ j ∈ s with i < j, y j)|
      ≤ ∑ i ∈ s, |ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j -
          ε i * (∏ j ∈ s with j < i, y j) * ∏ j ∈ s with i < j, y j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, ((s.card - 1 : ℕ) : ℝ) * E ^ 2 * (Y + E) ^ (s.card - 2) :=
        Finset.sum_le_sum fun i hi => ?_
    _ = s.card * ((s.card - 1 : ℕ) : ℝ) * E ^ 2 * (Y + E) ^ (s.card - 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [show ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j -
      ε i * (∏ j ∈ s with j < i, y j) * ∏ j ∈ s with i < j, y j =
      -(ε i * (∏ j ∈ s with j < i, y j - ∏ j ∈ s with j < i, (y j - ε j)) *
        ∏ j ∈ s with i < j, y j) by ring, abs_neg, abs_mul, abs_mul]
  set a := (s.filter (· < i)).card
  set b := (s.filter (i < ·)).card
  have h1 := abs_prod_sub_prod_le (s.filter (· < i)) y ε hY hE
    (fun j hj => hy j (Finset.mem_filter.mp hj).1) (fun j hj => hε j (Finset.mem_filter.mp hj).1)
  have h2 : |∏ j ∈ s with i < j, y j| ≤ (Y + E) ^ b :=
    abs_prod_le_pow _ _ fun j hj => (hy j (Finset.mem_filter.mp hj).1).trans (by linarith)
  have hc := card_filter_lt_add_gt s hi
  have has : (a : ℝ) ≤ ((s.card - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_add_right a b).trans hc
  rcases Nat.eq_zero_or_pos a with ha | ha
  · have : (s.filter (· < i)) = ∅ := Finset.card_eq_zero.mp ha
    rw [this, Finset.prod_empty, Finset.prod_empty, sub_self, abs_zero, mul_zero, zero_mul]
    positivity
  calc |ε i| * |∏ j ∈ s with j < i, y j - ∏ j ∈ s with j < i, (y j - ε j)| * |∏ j ∈ s with i < j, y j|
      ≤ E * (a * E * (Y + E) ^ (a - 1)) * (Y + E) ^ b := by
        gcongr
        exact hε i hi
    _ = a * E ^ 2 * (Y + E) ^ (a - 1 + b) := by rw [pow_add]; ring
    _ ≤ ((s.card - 1 : ℕ) : ℝ) * E ^ 2 * (Y + E) ^ (s.card - 2) := by
        gcongr <;> first | exact hYE | omega | exact has

end Scalar

theorem prod_update_split {n : ℕ} (g : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    ∏ j, Function.update g i t j = t * (∏ j with j < i, g j) * ∏ j with i < j, g j := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ i), mul_assoc, ← Finset.prod_union
    (Finset.disjoint_filter.mpr fun j _ h1 h2 => lt_asymm h1 h2)]
  congr 2
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · intro h
    rcases lt_or_gt_of_ne h with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ne_of_lt h
    · exact ne_of_gt h

section Geo

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev uv (k : K) : K → ℤ := Pi.single k 1

def SymmAt (n : ℕ) (V : Ideal (MRing ι)) : Prop :=
  ∀ (a : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)), geoNum n V (a ∘ σ) = geoNum n V a

theorem geoNum_snoc (n : ℕ) (V : Ideal (MRing ι)) (u : Fin n → K → ℤ) (b : K → ℤ) :
    geoNum (n + 1) V (Fin.snoc u b) = ∑ k, b k * geoNum (n + 1) V (Fin.snoc u (uv k)) := by
  simp only [geoNum, Fin.snoc_last, Fin.init_snoc]
  split_ifs with h
  · refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp [uv, Pi.single_apply]
  · simp

theorem geoNum_update (n : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt n V) (v : Fin n → K → ℤ)
    (i : Fin n) (z : K → ℤ) :
    geoNum n V (Function.update v i z) = ∑ k, z k * geoNum n V (Function.update v i (uv k)) := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    set σ := Equiv.swap i (Fin.last m)
    have key : ∀ w : K → ℤ, geoNum (m + 1) V (Function.update v i w) =
        geoNum (m + 1) V (Fin.snoc (Fin.init (v ∘ σ)) w) := by
      intro w
      rw [← hS (Function.update v i w) σ, Function.update_comp_equiv]
      rw [show σ.symm i = Fin.last m by simp [σ]]
      conv_lhs => rw [← Fin.snoc_init_self (v ∘ σ)]
      rw [Fin.update_snoc_last]
    rw [key z, geoNum_snoc]
    simp_rw [key]

def geoML (n : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt n V) :
    (Fin n → K → ℤ) →ₘₗ[ℤ] ℤ where
  toFun := geoNum n V
  map_update_add' := by
    intro inst m i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    rw [geoNum_update n V hS m i (x + y), geoNum_update n V hS m i x, geoNum_update n V hS m i y,
      ← Finset.sum_add_distrib]
    simp [add_mul]
  map_update_smul' := by
    intro inst m i c x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    rw [geoNum_update n V hS m i (c • x), geoNum_update n V hS m i x, RingHom.id_apply,
      smul_eq_mul, Finset.mul_sum]
    simp [mul_assoc]

theorem geoNum_expand (n : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt n V) (v : Fin n → K → ℤ) :
    geoNum n V v = ∑ r : Fin n → K, (∏ i, v i (r i)) * geoNum n V (fun i => uv (r i)) := by
  have h1 : v = fun i => ∑ k, v i k • uv k := by
    funext i
    ext k'
    simp [Finset.sum_apply, Pi.single_apply]
  have := (geoML n V hS).map_sum (fun i k => v i k • uv k)
  conv_lhs => rw [h1]
  change geoML n V hS _ = _
  rw [this]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  simp only [RingHom.id_apply]
  rfl

def nrm (z : K → ℤ) : ℝ := ∑ k, |(z k : ℝ)|

theorem abs_le_nrm (z : K → ℤ) (k : K) : |(z k : ℝ)| ≤ nrm z :=
  Finset.single_le_sum (f := fun k => |(z k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)

theorem nrm_nonneg (z : K → ℤ) : 0 ≤ nrm z := Finset.sum_nonneg fun _ _ => abs_nonneg _

def coefB (n : ℕ) (V : Ideal (MRing ι)) : ℝ :=
  ∑ r : Fin n → K, |(geoNum n V (fun i => uv (r i)) : ℝ)|

theorem coefB_nonneg (n : ℕ) (V : Ideal (MRing ι)) : 0 ≤ coefB n V :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem geoNum_expand_real (n : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt n V) (v : Fin n → K → ℤ) :
    (geoNum n V v : ℝ) =
      ∑ r : Fin n → K, (∏ i, (v i (r i) : ℝ)) * (geoNum n V (fun i => uv (r i)) : ℝ) := by
  rw [geoNum_expand n V hS v]
  push_cast
  rfl

theorem geoNum_shift_est (n : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt n V) (x c : K → ℤ) :
    |(geoNum n V (fun _ => x) : ℝ) - geoNum n V (fun _ => x - c)| ≤
      coefB n V * (n * nrm c * (nrm x + 1 + nrm c) ^ (n - 1)) := by
  rw [geoNum_expand_real n V hS, geoNum_expand_real n V hS, ← Finset.sum_sub_distrib, coefB,
    Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [← sub_mul, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := abs_prod_sub_prod_le (Finset.univ : Finset (Fin n)) (fun i => (x (r i) : ℝ))
    (fun i => (c (r i) : ℝ)) (Y := nrm x + 1) (E := nrm c) (by linarith [nrm_nonneg x]) (nrm_nonneg c)
    (fun i _ => (abs_le_nrm x _).trans (by linarith)) (fun i _ => abs_le_nrm c _)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  simp only [Pi.sub_apply, Int.cast_sub]
  exact this

theorem geoNum_update_eq_snoc (m : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt (m + 1) V) (x e : K → ℤ)
    (i : Fin (m + 1)) :
    geoNum (m + 1) V (Function.update (fun _ => x) i e) = geoNum (m + 1) V (Fin.snoc (fun _ => x) e) := by
  rw [← hS _ (Equiv.swap i (Fin.last m)), Function.update_comp_equiv]
  rw [show (Equiv.swap i (Fin.last m)).symm i = Fin.last m by simp]
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · simp [Fin.snoc_castSucc]

theorem geoNum_diff_est (m : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt (m + 1) V) (x : K → ℤ) (b : K) :
    |(geoNum (m + 1) V (fun _ => x) : ℝ) - geoNum (m + 1) V (fun _ => x - uv b) -
        (m + 1) * geoNum (m + 1) V (Fin.snoc (fun _ => x) (uv b))| ≤
      coefB (m + 1) V * ((m + 1) * m * (nrm x + 2) ^ (m + 1 - 2)) := by
  have hlin : ((m + 1 : ℕ) : ℝ) * geoNum (m + 1) V (Fin.snoc (fun _ => x) (uv b)) =
      ∑ i : Fin (m + 1), (geoNum (m + 1) V (Function.update (fun _ => x) i (uv b)) : ℝ) := by
    have h : ∀ i : Fin (m + 1), (geoNum (m + 1) V (Function.update (fun _ => x) i (uv b)) : ℝ) =
        geoNum (m + 1) V (Fin.snoc (fun _ => x) (uv b)) := fun i => by
      rw [geoNum_update_eq_snoc m V hS x (uv b) i]
    rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  push_cast at hlin
  rw [hlin, geoNum_expand_real (m + 1) V hS (fun _ => x),
    geoNum_expand_real (m + 1) V hS (fun _ => x - uv b),
    Finset.sum_congr rfl fun i _ => geoNum_expand_real (m + 1) V hS (Function.update (fun _ => x) i (uv b))]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, coefB, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [← Finset.sum_mul, ← sub_mul, ← sub_mul, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := abs_prod_sub_prod_sub_lin_le (Finset.univ : Finset (Fin (m + 1))) (fun i => (x (r i) : ℝ))
    (fun i => (uv b (r i) : ℝ)) (Y := nrm x + 1) (E := 1) (by linarith [nrm_nonneg x]) zero_le_one
    (fun i _ => (abs_le_nrm x _).trans (by linarith))
    (fun i _ => by simp only [uv, Pi.single_apply]; split_ifs <;> simp)
  simp only [Finset.card_univ, Fintype.card_fin, one_pow, mul_one] at this
  rw [show nrm x + 1 + 1 = nrm x + 2 by ring] at this
  have e1 : (∏ i, (((x - uv b) (r i) : ℤ) : ℝ)) = ∏ i, ((x (r i) : ℝ) - (uv b (r i) : ℝ)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [Pi.sub_apply]
  have e2 : ∀ i, (∏ j, ((Function.update (fun _ => x) i (uv b) j (r j) : ℤ) : ℝ)) =
      (uv b (r i) : ℝ) * (∏ j with j < i, (x (r j) : ℝ)) * ∏ j with i < j, (x (r j) : ℝ) := by
    intro i
    rw [← prod_update_split]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [e1, Finset.sum_congr rfl fun i _ => e2 i]
  push_cast at this
  exact this

end Geo

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.LengthLocQuotEqZero
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

variable {R : Type*} [CommRing R]

theorem length_loc_add {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂] (g : M₀ →ₗ[R] M₁) (h : M₁ →ₗ[R] M₂)
    (hg : Function.Injective g) (hh : Function.Surjective h) (ex : Function.Exact g h)
    (P : Ideal R) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M₁) =
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M₀) +
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M₂) := by
  exact Module.length_eq_add_of_exact _ _ (LocalizedModule.map_injective _ g hg)
    (LocalizedModule.map_surjective _ h hh) (LocalizedModule.map_exact _ g h ex)

theorem length_loc_step (I q : Ideal R) (f : R) (hq : ∀ g, g ∈ q ↔ g * f ∈ I) (P : Ideal R)
    [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ I)) =
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ q)) +
        Module.length (Localization.AtPrime P)
          (LocalizedModule P.primeCompl (R ⧸ (I ⊔ Ideal.span {f}))) := by
  let g : (R ⧸ q) →ₗ[R] (R ⧸ I) :=
    Submodule.mapQ q I (LinearMap.mulRight R f) (by intro x hx; exact (hq x).mp hx)
  let π : (R ⧸ I) →ₗ[R] (R ⧸ (I ⊔ Ideal.span {f})) :=
    Submodule.mapQ I (I ⊔ Ideal.span {f}) LinearMap.id (by intro x hx; exact Ideal.mem_sup_left hx)
  have hg : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    change Submodule.Quotient.mk (p := I) (x * f) = 0 at hz
    rw [Submodule.Quotient.mk_eq_zero] at hz
    change Submodule.Quotient.mk (p := q) x = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact (hq x).mpr hz
  have hπ : Function.Surjective π := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hex : Function.Exact g π := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change Submodule.Quotient.mk (p := I ⊔ Ideal.span {f}) y = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hb
      refine ⟨Submodule.Quotient.mk r, ?_⟩
      change Submodule.Quotient.mk (p := I) (r * f) = Submodule.Quotient.mk (a + r * f)
      rw [Submodule.Quotient.eq]
      simpa using I.neg_mem ha
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change Submodule.Quotient.mk (p := I) (x * f) = Submodule.Quotient.mk y at hx
      rw [Submodule.Quotient.eq] at hx
      have e : y = x * f - (x * f - y) := by ring
      rw [e]
      exact Submodule.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨x, rfl⟩))
        (Ideal.mem_sup_left hx)
  exact length_loc_add g π hg hπ hex P

theorem length_loc_quot_eq_zero (q P : Ideal R) [P.IsPrime] (h : ¬ q ≤ P) :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ q)) = 0 := by
  obtain ⟨s, hsq, hsP⟩ := IsConcreteLE.not_le_iff_exists.mp h
  rw [Module.length_eq_zero_iff]
  refine subsingleton_of_forall_eq 0 (fun z => ?_)
  induction z using LocalizedModule.induction_on with
  | h m t =>
    rw [← LocalizedModule.zero_mk t, LocalizedModule.mk_eq]
    refine ⟨⟨s, hsP⟩, ?_⟩
    rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def]
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
    rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact q.mul_mem_right _ hsq

theorem length_loc_quot_self (P : Ideal R) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ P)) = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_toSpanSingleton_surjective]
  have hne : ∀ (r : R) (t : P.primeCompl),
      LocalizedModule.mk (Ideal.Quotient.mk P r) t = 0 → r ∈ P := by
    intro r t h0
    rw [← LocalizedModule.zero_mk t, LocalizedModule.mk_eq] at h0
    obtain ⟨u, hu⟩ := h0
    rw [smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, smul_zero, Ideal.Quotient.eq_zero_iff_mem] at hu
    rcases Ideal.IsPrime.mem_or_mem ‹P.IsPrime› hu with h1 | h1
    · exact absurd h1 u.2
    · rcases Ideal.IsPrime.mem_or_mem ‹P.IsPrime› h1 with h2 | h2
      · exact absurd h2 t.2
      · exact h2
  constructor
  · refine ⟨⟨LocalizedModule.mk (Ideal.Quotient.mk P 1) 1, 0, fun h0 => ?_⟩⟩
    exact ‹P.IsPrime›.ne_top ((Ideal.eq_top_iff_one P).mpr (hne 1 1 h0))
  · intro x hx y
    induction x using LocalizedModule.induction_on with
    | h m t =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
      have hr : r ∈ P.primeCompl := fun hrP => hx (by
        rw [(Ideal.Quotient.eq_zero_iff_mem.mpr hrP), LocalizedModule.zero_mk])
      induction y using LocalizedModule.induction_on with
      | h m' t' =>
        obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective m'
        refine ⟨Localization.mk (r' * t) (t' * ⟨r, hr⟩), ?_⟩
        rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
        refine ⟨1, ?_⟩
        simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def,
          Ideal.Quotient.algebraMap_eq, ← map_mul]
        congr 1
        ring

theorem length_loc_top (P : Ideal R) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ (⊤ : Ideal R))) = 0 := by
  apply length_loc_quot_eq_zero
  intro h
  exact ‹P.IsPrime›.ne_top (top_le_iff.mp h)

theorem length_loc_chain (P : Ideal R) [P.IsPrime] : ∀ (N : ℕ) (F : Fin (N + 1) → Ideal R)
    (f : Fin N → R) (q : Fin N → Ideal R), F (Fin.last N) = ⊤ →
    (∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧ (q j).IsPrime ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) →
    (∀ j, q j ≤ P → q j = P) →
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ F 0)) =
      ((∑ j : Fin N, if q j = P then 1 else 0 : ℕ) : ℕ∞) := by
  intro N
  induction N with
  | zero =>
    intro F f q hlast _ _
    rw [show F 0 = F (Fin.last 0) from rfl, hlast, length_loc_top]
    simp
  | succ N ih =>
    intro F f q hlast hj hmin
    have htail := ih (fun j => F j.succ) (fun j => f j.succ) (fun j => q j.succ)
      (by simpa only [Fin.succ_last] using hlast)
      (fun j => by simpa only [Fin.castSucc_succ] using hj j.succ)
      (fun j => hmin j.succ)
    obtain ⟨h1, _, h3⟩ := hj 0
    rw [Fin.castSucc_zero] at h1 h3
    rw [length_loc_step (F 0) (q 0) (f 0) h3 P, ← h1, htail, Fin.sum_univ_succ]
    by_cases hq : q 0 = P
    · rw [ite_eq_left hq, hq, length_loc_quot_self]
      push_cast
      ring
    · rw [ite_eq_right hq, length_loc_quot_eq_zero _ _ (fun h => hq (hmin 0 h))]
      simp

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem natCast_mem_of_charOf (W : Ideal (MRing ι)) : ((charOf W : ℕ) : MRing ι) ∈ W := by
  show (((Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs : ℕ) : MRing ι) ∈ W
  have hg := Submodule.IsPrincipal.generator_mem (W.comap (C : ℤ →+* MRing ι))
  have hn : (((Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs : ℕ) : ℤ) ∈
      W.comap (C : ℤ →+* MRing ι) := by
    obtain ⟨u, hu⟩ : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) ∣
        ((Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs : ℤ) :=
      Int.dvd_natAbs.2 dvd_rfl
    rw [hu]
    exact Ideal.mul_mem_right u _ hg
  have h := Ideal.mem_comap.1 hn
  rwa [map_natCast] at h

theorem charOf_ne_zero_of_mem {W : Ideal (MRing ι)} {p : ℕ} (hp : p ≠ 0)
    (hpW : (p : MRing ι) ∈ W) : charOf W ≠ 0 := by
  intro h0
  have hp' : (p : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, map_natCast]; exact hpW
  have hg0 : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) = 0 := Int.natAbs_eq_zero.1 h0
  obtain ⟨s, hs⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator _).1 hp'
  rw [hg0, smul_zero] at hs
  exact hp (by exact_mod_cast hs)

theorem charOf_eq_of_mem {W : Ideal (MRing ι)} (hW : W.IsPrime) {p : ℕ} (hp : p.Prime)
    (hpW : (p : MRing ι) ∈ W) : charOf W = p := by
  have hp' : (p : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, map_natCast]; exact hpW
  have hdvd := (Submodule.IsPrincipal.mem_iff_generator_dvd _).1 hp'
  have hd : charOf W ∣ p := Int.natAbs_dvd_natAbs.2 hdvd
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h1
  · exfalso
    have hu : IsUnit (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))) :=
      Int.isUnit_iff_natAbs_eq.2 h1
    have h1m : (1 : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) :=
      (Submodule.IsPrincipal.mem_iff_generator_dvd _).2 hu.dvd
    rw [Ideal.mem_comap, map_one] at h1m
    exact hW.ne_top ((Ideal.eq_top_iff_one _).2 h1m)
  · exact h1

theorem isMultiHomogIdeal_chain {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)} {f : Fin N → MRing ι}
    {c : Fin N → K → ℕ} (h0 : IsMultiHomogIdeal (F 0))
    (hj : ∀ j : Fin N, IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j}) :
    ∀ j : Fin (N + 1), IsMultiHomogIdeal (F j) := by
  intro j
  induction j using Fin.induction with
  | zero => exact h0
  | succ i ih =>
    obtain ⟨S, hS, hSe⟩ := ih
    refine ⟨S ∪ {f i}, ?_, ?_⟩
    · rintro g (hg | hg)
      · exact hS g hg
      · rw [Set.mem_singleton_iff.1 hg]; exact ⟨c i, (hj i).1⟩
    · rw [(hj i).2, hSe, Ideal.span_union]

theorem le_chain {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)} {f : Fin N → MRing ι}
    (hj : ∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j}) :
    ∀ j : Fin (N + 1), F 0 ≤ F j := by
  intro j
  induction j using Fin.induction with
  | zero => exact le_rfl
  | succ i ih => rw [hj i]; exact ih.trans le_sup_left

theorem card_mPiece_top (a : K → ℕ) : Nat.card (mPiece (⊤ : Ideal (MRing ι)) a) = 1 := by
  have : Subsingleton (MRing ι ⧸ (⊤ : Ideal (MRing ι))) := Ideal.Quotient.subsingleton_iff.2 rfl
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨0⟩⟩

theorem card_mPiece_chain (a : K → ℕ) : ∀ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι))
    (f : Fin N → MRing ι) (c : Fin N → K → ℕ) (q : Fin N → Ideal (MRing ι)),
    IsMultiHomogIdeal (F 0) → F (Fin.last N) = ⊤ →
    (∀ j : Fin N, IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) →
    (∀ j k, c j k ≤ a k) →
    Nat.card (mPiece (F 0) a) = ∏ j, Nat.card (mPiece (q j) (a - c j)) := by
  intro N
  induction N with
  | zero =>
    intro F f c q h0 hlast hj ha
    have : F 0 = ⊤ := hlast
    rw [this, card_mPiece_top, Fin.prod_univ_zero]
  | succ N ih =>
    intro F f c q h0 hlast hj ha
    have htail := ih (fun j => F j.succ) (fun j => f j.succ) (fun j => c j.succ)
      (fun j => q j.succ)
      (isMultiHomogIdeal_chain h0 (fun j => ⟨(hj j).1, (hj j).2.1⟩) 1)
      (by simpa [Fin.succ_last] using hlast)
      (fun j => by
        have h := hj j.succ
        rwa [← Fin.succ_castSucc] at h)
      (fun j => ha j.succ)
    obtain ⟨h1, h2, h3⟩ := hj 0
    rw [Fin.castSucc_zero] at h2 h3
    rw [card_mPiece_step h0 h1 h3 (ha 0), ← h2, Fin.prod_univ_succ, mul_comm]
    rw [htail]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
