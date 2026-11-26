module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesSubstCoeffSubMemIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderProdSubProd
namespace GlobalTheory.OrderProductDifference

open MvPowerSeries

theorem order_prod_sub_prod {R τ ι : Type} [CommRing R] (s : Finset ι)
    (a b : ι → MvPowerSeries τ R) (k : ι → ℕ)
    (ha : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) ≤ MvPowerSeries.order (a i))
    (hb : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) ≤ MvPowerSeries.order (b i))
    (hab : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (a i - b i)) :
    ∑ i ∈ s, ((k i : ℕ) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by
  classical
  revert ha hb hab
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert j s hj ih =>
    intro ha hb hab
    have ih' := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
      (fun i hi => hb i (Finset.mem_insert_of_mem hi))
      (fun i hi => hab i (Finset.mem_insert_of_mem hi))
    have key : ∏ i ∈ insert j s, a i - ∏ i ∈ insert j s, b i
        = a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by
      rw [Finset.prod_insert hj, Finset.prod_insert hj]; ring
    have hbs : ∑ i ∈ s, ((k i : ℕ) : ℕ∞) ≤ MvPowerSeries.order (∏ i ∈ s, b i) :=
      le_trans (Finset.sum_le_sum fun i hi => hb i (Finset.mem_insert_of_mem hi))
        (MvPowerSeries.le_order_prod _ _)
    rw [key, Finset.sum_insert hj]
    refine le_trans ?_ MvPowerSeries.min_order_le_add
    refine le_min ?_ ?_
    · calc ((k j : ℕ) : ℕ∞) + ∑ i ∈ s, ((k i : ℕ) : ℕ∞) + 1
          = (k j : ℕ∞) + (∑ i ∈ s, ((k i : ℕ) : ℕ∞) + 1) := by rw [add_assoc]
        _ ≤ MvPowerSeries.order (a j) + MvPowerSeries.order (∏ i ∈ s, a i - ∏ i ∈ s, b i) :=
          add_le_add (ha j (Finset.mem_insert_self _ _)) ih'
        _ ≤ _ := MvPowerSeries.le_order_mul
    · calc ((k j : ℕ) : ℕ∞) + ∑ i ∈ s, ((k i : ℕ) : ℕ∞) + 1
          = ((k j : ℕ∞) + 1) + ∑ i ∈ s, ((k i : ℕ) : ℕ∞) := by rw [add_right_comm]
        _ ≤ MvPowerSeries.order (a j - b j) + MvPowerSeries.order (∏ i ∈ s, b i) :=
          add_le_add (hab j (Finset.mem_insert_self _ _)) hbs
        _ ≤ _ := MvPowerSeries.le_order_mul

theorem target : ∀ {R τ ι : Type} [inst : CommRing R] (s : Finset ι) (a b : ι → MvPowerSeries τ R) (k : ι → ℕ), (∀ i ∈ s, (↑(k i) : ℕ∞) ≤ MvPowerSeries.order (a i)) → (∀ i ∈ s, (↑(k i) : ℕ∞) ≤ MvPowerSeries.order (b i)) → (∀ i ∈ s, (↑(k i) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (a i - b i)) → ∑ i ∈ s, (↑(k i) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (∏ i ∈ s, a i - ∏ i ∈ s, b i) :=
  fun s a b k ha hb hab => order_prod_sub_prod s a b k ha hb hab

end GlobalTheory.OrderProductDifference
end

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.SubstMod

theorem order_prod_sub_prod {R τ ι : Type} [CommRing R] (s : Finset ι)
    (a b : ι → MvPowerSeries τ R) (k : ι → ℕ)
    (ha : ∀ i ∈ s, (k i : ℕ∞) ≤ (a i).order) (hb : ∀ i ∈ s, (k i : ℕ∞) ≤ (b i).order)
    (hab : ∀ i ∈ s, (k i : ℕ∞) + 1 ≤ (a i - b i).order) :
    (∑ i ∈ s, (k i : ℕ∞)) + 1 ≤ (∏ i ∈ s, a i - ∏ i ∈ s, b i).order := by
  first
  | exact @_root_.GlobalTheory.OrderProductDifference.target
  | exact _root_.GlobalTheory.OrderProductDifference.target
  | (apply _root_.GlobalTheory.OrderProductDifference.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrderProductDifference.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrderProductDifference.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrderProductDifference.target ..)

theorem order_pow_sub_pow {R τ : Type} [CommRing R] (u l : MvPowerSeries τ R)
    (hu : constantCoeff u = 0) (hl : constantCoeff l = 0) (hul : (2 : ℕ∞) ≤ (u - l).order)
    (n : ℕ) : (n : ℕ∞) + 1 ≤ (u ^ n - l ^ n).order := by
  have := order_prod_sub_prod (Finset.range n) (fun _ => u) (fun _ => l) (fun _ => 1)
    (fun _ _ => by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hu)
    (fun _ _ => by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hl)
    (fun _ _ => by simpa [one_add_one_eq_two] using hul)
  simpa [Finset.prod_const] using this

theorem order_monoProd_sub {R σ τ : Type} [CommRing R] (u l : σ → MvPowerSeries τ R)
    (hu : ∀ s, constantCoeff (u s) = 0) (hl : ∀ s, constantCoeff (l s) = 0)
    (hul : ∀ s, (2 : ℕ∞) ≤ (u s - l s).order) (α : σ →₀ ℕ) :
    (α.degree : ℕ∞) + 1 ≤
      ((α.prod fun s e => u s ^ e) - α.prod fun s e => l s ^ e).order := by
  have := order_prod_sub_prod α.support (fun s => u s ^ α s) (fun s => l s ^ α s) α
    (fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (hu s))
    (fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (hl s))
    (fun s _ => order_pow_sub_pow _ _ (hu s) (hl s) (hul s) _)
  rw [Finsupp.degree_apply]
  push_cast
  exact this

theorem subst_coeff_sub_mem : ∀ {B Q σ τ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype σ]
    (N : Ideal B) (u ℓ : σ → MvPowerSeries τ B), (∀ s, constantCoeff (u s) = 0) →
    (∀ s (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (u s) = coeff β (ℓ s)) →
    ∀ (m : ℕ) (c : MvPowerSeries σ Q), (∀ α : σ →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) →
    ∀ (w : τ →₀ ℕ), w.degree = m →
      ∃ r ∈ N, coeff w (subst (up Q u) c) - coeff w (subst (up Q ℓ) c) = algebraMap B Q r := by
  intro B Q σ τ _ _ _ _ N u ℓ hu hl m c hc w hw
  have hℓ : ∀ s, constantCoeff (ℓ s) = 0 := fun s => by
    rw [← coeff_zero_eq_constantCoeff_apply, ← hl s 0 (by simp), coeff_zero_eq_constantCoeff_apply,
      hu s]
  have hul : ∀ s, (2 : ℕ∞) ≤ (u s - ℓ s).order := fun s =>
    nat_le_order (n := 2) fun β hβ => by
      rw [map_sub, hl s β (by omega), sub_self]
  have hU : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero fun s => by
    simp [up, hu s]
  have hL : HasSubst (up Q ℓ) := hasSubst_of_constantCoeff_zero fun s => by
    simp [up, hℓ s]
  rw [coeff_subst hU, coeff_subst hL,
    ← finsum_sub_distrib (coeff_subst_finite hU c w) (coeff_subst_finite hL c w)]
  refine finsum_induction (fun x : Q => ∃ r ∈ N, x = algebraMap B Q r) ⟨0, N.zero_mem, by simp⟩
    (fun x y ⟨r, hr, hx⟩ ⟨t, ht, hy⟩ => ⟨r + t, N.add_mem hr ht, by rw [hx, hy, map_add (f := _)]⟩)
    fun α => ?_
  have hprod : ∀ v : σ → MvPowerSeries τ B, (α.prod fun s e => up Q v s ^ e) =
      map (algebraMap B Q) (α.prod fun s e => v s ^ e) := by
    intro v
    simp only [up, Finsupp.prod, map_prod, map_pow]
  rw [hprod u, hprod ℓ, coeff_map, coeff_map, smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub,
    ← map_sub]
  by_cases h : α.degree < m
  · obtain ⟨b, hb, hcb⟩ := hc α h
    exact ⟨b * _, N.mul_mem_right _ hb, by rw [hcb, map_mul]⟩
  · have h0 : coeff w ((α.prod fun s e => u s ^ e) - α.prod fun s e => ℓ s ^ e) = 0 := by
      refine coeff_of_lt_order (lt_of_lt_of_le ?_ (order_monoProd_sub u ℓ hu hℓ hul α))
      have : w.degree ≤ α.degree := by omega
      exact_mod_cast Nat.lt_succ_of_le this
    exact ⟨0, N.zero_mem, by rw [h0, map_zero, mul_zero]⟩

end GlobalTheory.SubstMod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffFormalGroupLawEvalPointsOfDegreeLeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffFormalGroupLawEvalPointsOfDegreeLeOne
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.QLog.OpLin

variable {R : Type} [CommRing R]

theorem degree_eq_one {σ : Type} [Fintype σ] {D : σ →₀ ℕ} (h : D.degree = 1) :
    ∃ s, D = Finsupp.single s 1 := by
  classical
  have hsum := h
  rw [Finsupp.degree_eq_sum] at hsum
  obtain ⟨s, hs⟩ : ∃ s, D s ≠ 0 := by
    by_contra hc
    push_neg at hc
    simp [hc] at hsum
  refine ⟨s, ?_⟩
  have hle : ∀ t, t ≠ s → D s + D t ≤ 1 := fun t ht => by
    rw [← hsum, ← Finset.sum_pair (Ne.symm ht)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  ext t
  by_cases ht : t = s
  · subst ht
    have : D t ≤ 1 := h ▸ Finsupp.le_degree t D
    simp only [Finsupp.single_eq_same]
    omega
  · have := hle t ht
    simp only [Finsupp.single_apply, if_neg (Ne.symm ht)]
    omega

theorem le_order_prod_pow {σ τ : Type} {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) (D : σ →₀ ℕ) :
    (D.degree : ℕ∞) ≤ (D.prod fun s e => a s ^ e).order := by
  refine le_trans ?_ (le_order_prod _ _)
  rw [Finsupp.degree_apply, Nat.cast_sum]
  exact Finset.sum_le_sum fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (ha s)

theorem coeff_subst_of_degree_le_one {σ τ : Type} [Fintype σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ R} (hf : constantCoeff f = 0)
    {β : τ →₀ ℕ} (hβ : β.degree ≤ 1) :
    coeff β (subst a f) = ∑ s, coeff (Finsupp.single s 1) f * coeff β (a s) := by
  classical
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [coeff_subst hs]
  have hsupp : (Function.support fun D : σ →₀ ℕ =>
      coeff D f • coeff β (D.prod fun s e => a s ^ e)) ⊆
      ((Finset.univ.image fun s : σ => Finsupp.single s 1 : Finset (σ →₀ ℕ)) : Set (σ →₀ ℕ)) := by
    intro D hD
    rw [Function.mem_support] at hD
    have h0 : D ≠ 0 := by
      rintro rfl
      apply hD
      rw [coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
    have h1 : D.degree ≤ 1 := by
      by_contra hlt
      push_neg at hlt
      apply hD
      rw [coeff_of_lt_order (lt_of_lt_of_le ?_ (le_order_prod_pow ha D)), smul_zero]
      exact_mod_cast lt_of_le_of_lt hβ hlt
    have h2 : D.degree = 1 := by
      have : D.degree ≠ 0 := fun h => h0 ((Finsupp.degree_eq_zero_iff D).1 h)
      omega
    obtain ⟨s, rfl⟩ := degree_eq_one h2
    simp
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_image (fun s _ t _ h => Finsupp.single_left_injective one_ne_zero h)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finsupp.prod_single_index (by simp), pow_one, smul_eq_mul]

end GlobalTheory.QLog.OpLin

namespace GlobalTheory.QLog.OpLin

variable {B O : Type} [CommRing B] [CommRing O] {d : ℕ}

theorem coeff_inl {θ : B →+* O} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : IsLift θ μ)
    (i j : Fin d) : coeff (Finsupp.single (Sum.inl j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have h := congrArg (coeff (Finsupp.single j 1)) (congrFun hμ.unit i)
  simp only [op, at2] at h
  rw [coeff_subst_of_degree_le_one (by rintro (s | s) <;> simp) (hμ.const i)
    (by simp), Fintype.sum_sum_type] at h
  simpa [coeff_X, Finsupp.single_left_inj one_ne_zero, eq_comm] using h

theorem coeff_inr {θ : B →+* O} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : IsLift θ μ)
    (i j : Fin d) : coeff (Finsupp.single (Sum.inr j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have h := congrArg (coeff (Finsupp.single (Sum.inr j) 1)) (hμ.comm i)
  simp only [swap, at2] at h
  rw [coeff_subst_of_degree_le_one (by rintro (s | s) <;> simp) (hμ.const i)
    (by simp), Fintype.sum_sum_type] at h
  rw [← h, ← coeff_inl hμ i j]
  simp [coeff_X, Finsupp.single_left_inj one_ne_zero]

theorem coeff_op_of_degree_le_one : ∀ {B O : Type} [CommRing B] [CommRing O] (θ : B →+* O) {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}, IsLift θ μ → ∀ {τ : Type}
    (u v : Fin d → MvPowerSeries τ B), (∀ j, constantCoeff (u j) = 0) →
    (∀ j, constantCoeff (v j) = 0) → ∀ (i : Fin d) (β : τ →₀ ℕ), β.degree ≤ 1 →
    coeff β (op μ u v i) = coeff β (u i + v i) := by
  intro B O _ _ θ d μ hμ τ u v hu hv i β hβ
  classical
  simp only [op, at2]
  rw [coeff_subst_of_degree_le_one (by rintro (s | s); exacts [hu s, hv s]) (hμ.const i) hβ,
    Fintype.sum_sum_type, map_add]
  simp [coeff_inl hμ, coeff_inr hμ]

end GlobalTheory.QLog.OpLin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffFormalGroupLawEvalPointsOfDegreeLeOneStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_formalGroupLawEvalPoints_of_degree_le_one : ∀ {B O : Type} [CommRing B] [CommRing O] (θ : B →+* O) {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}, IsLift θ μ → ∀ {τ : Type} (u v : Fin d → MvPowerSeries τ B), (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ (i : Fin d) (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (op μ u v i) = coeff β (u i + v i) := by
  first | exact @GlobalTheory.QLog.OpLin.coeff_op_of_degree_le_one | exact GlobalTheory.QLog.OpLin.coeff_op_of_degree_le_one | (intros; apply GlobalTheory.QLog.OpLin.coeff_op_of_degree_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffProdPowSecondAddThirdThreeGroups
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffProdPowSecondAddThirdThreeGroups
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.BinomRight

theorem prod_monomial' {R σ ι : Type} [CommRing R] (s : Finset ι) (n : ι → σ →₀ ℕ) (c : ι → R) :
    ∏ i ∈ s, (monomial (n i) (c i) : MvPowerSeries σ R) =
      monomial (∑ i ∈ s, n i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [monomial_zero_eq_C]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, ih, monomial_mul_monomial, Finset.sum_insert hj, Finset.prod_insert hj]

theorem add_pow_X' {R σ : Type} [CommRing R] (u v : σ) (k : ℕ) :
    ((X u + X v : MvPowerSeries σ R)) ^ k =
      ∑ j ∈ Finset.range (k + 1),
        monomial (Finsupp.single u j + Finsupp.single v (k - j)) (k.choose j : R) := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [X_pow_eq, X_pow_eq, monomial_mul_monomial, ← map_natCast (C (σ := σ) (R := R)),
    ← monomial_zero_eq_C, monomial_mul_monomial, add_zero]
  simp only [one_mul]

end GlobalTheory.BinomRight

namespace GlobalTheory.BinomRight

variable {R : Type} [CommRing R] {d : ℕ}

def expo (α : Fin d ⊕ Fin d →₀ ℕ) (J : Fin d → ℕ) : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ :=
  (∑ i, Finsupp.single (Sum.inl i) (α (Sum.inl i))) +
    ∑ i, (Finsupp.single (Sum.inr (Sum.inl i)) (J i) +
      Finsupp.single (Sum.inr (Sum.inr i)) (α (Sum.inr i) - J i))

theorem expo_inl (α : Fin d ⊕ Fin d →₀ ℕ) (J : Fin d → ℕ) (i : Fin d) :
    expo α J (Sum.inl i) = α (Sum.inl i) := by
  classical
  simp [expo, Finsupp.single_apply]

theorem expo_inr_inl (α : Fin d ⊕ Fin d →₀ ℕ) (J : Fin d → ℕ) (i : Fin d) :
    expo α J (Sum.inr (Sum.inl i)) = J i := by
  classical
  simp [expo, Finsupp.single_apply]

theorem expo_inr_inr (α : Fin d ⊕ Fin d →₀ ℕ) (J : Fin d → ℕ) (i : Fin d) :
    expo α J (Sum.inr (Sum.inr i)) = α (Sum.inr i) - J i := by
  classical
  simp [expo, Finsupp.single_apply]
  rw [Finset.sum_eq_single i (fun x _ hx => by simp [hx]) (by simp)]
  simp

theorem prod_eq_sum (α : Fin d ⊕ Fin d →₀ ℕ) :
    (α.prod fun s k => (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) s) ^ k) =
      ∑ J ∈ Fintype.piFinset (fun i => Finset.range (α (Sum.inr i) + 1)),
        monomial (expo α J) (∏ i, ((α (Sum.inr i)).choose (J i) : R)) := by
  classical
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, x1, x2, x3, X_pow_eq, add_pow_X', prod_monomial']
  rw [Finset.prod_univ_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [prod_monomial', monomial_mul_monomial, Finset.prod_const_one, one_mul, expo]

end GlobalTheory.BinomRight

namespace GlobalTheory.BinomRight

variable {R : Type} [CommRing R] {d : ℕ}

theorem sumElim_eq_expo_iff (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ) (J : Fin d → ℕ)
    (hJ : ∀ i, J i ≤ α (Sum.inr i)) :
    Finsupp.sumElim a (Finsupp.sumElim b e) = expo α J ↔
      α = Finsupp.sumElim a (b + e) ∧ J = ⇑b := by
  constructor
  · intro h
    have h1 := fun i => DFunLike.congr_fun h (Sum.inl i)
    have h2 := fun i => DFunLike.congr_fun h (Sum.inr (Sum.inl i))
    have h3 := fun i => DFunLike.congr_fun h (Sum.inr (Sum.inr i))
    simp only [expo_inl, expo_inr_inl, expo_inr_inr, Finsupp.sumElim_apply, Sum.elim_inl,
      Sum.elim_inr] at h1 h2 h3
    have hJb : J = ⇑b := funext fun i => (h2 i).symm
    refine ⟨Finsupp.ext fun s => ?_, hJb⟩
    rcases s with i | i
    · simp [h1 i]
    · have := h3 i; have := hJ i; have := h2 i
      simp only [Finsupp.sumElim_apply, Sum.elim_inr, Finsupp.add_apply]
      omega
  · rintro ⟨rfl, rfl⟩
    refine Finsupp.ext fun s => ?_
    rcases s with i | i | i
    · simp [expo_inl]
    · simp [expo_inr_inl]
    · simp [expo_inr_inr]

end GlobalTheory.BinomRight

namespace GlobalTheory.BinomRight

theorem coeff_prod_pow_second_add_third_threeGroups {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ)
    (a b e : Fin d →₀ ℕ) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e))
        (α.prod fun s k => (Sum.elim x1
          (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) s) ^ k) =
      if α = Finsupp.sumElim a (b + e) then (∏ i, ((b + e) i).choose (b i) : R) else 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [prod_eq_sum, map_sum]
  simp only [coeff_monomial]
  have hmem : ∀ J ∈ Fintype.piFinset (fun i => Finset.range (α (Sum.inr i) + 1)),
      ∀ i, J i ≤ α (Sum.inr i) := fun J hJ i =>
    Nat.lt_succ_iff.1 (Finset.mem_range.1 (Fintype.mem_piFinset.1 hJ i))
  by_cases hα : α = Finsupp.sumElim a (b + e)
  · rw [if_pos hα]
    have hb : ⇑b ∈ Fintype.piFinset (fun i => Finset.range (α (Sum.inr i) + 1)) := by
      refine Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 ?_
      rw [hα]; simp
    rw [Finset.sum_eq_single_of_mem (⇑b) hb]
    · rw [if_pos ((sumElim_eq_expo_iff α a b e _ (hmem _ hb)).2 ⟨hα, rfl⟩)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hα]; simp
    · intro J hJ hJb
      rw [if_neg fun h => hJb ((sumElim_eq_expo_iff α a b e J (hmem J hJ)).1 h).2]
  · rw [if_neg hα]
    refine Finset.sum_eq_zero fun J hJ => ?_
    rw [if_neg fun h => hα ((sumElim_eq_expo_iff α a b e J (hmem J hJ)).1 h).1]

end GlobalTheory.BinomRight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffProdPowSecondAddThirdThreeGroupsStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_prod_pow_x1_x2_add_x3 : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) s) ^ k) = if α = Finsupp.sumElim a (b + e) then (∏ i, ((b + e) i).choose (b i) : R) else 0 := by
  first | exact @GlobalTheory.BinomRight.coeff_prod_pow_second_add_third_threeGroups | exact GlobalTheory.BinomRight.coeff_prod_pow_second_add_third_threeGroups | (intros; apply GlobalTheory.BinomRight.coeff_prod_pow_second_add_third_threeGroups <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEvalTwoGroupsThreeGroupsEqZeroOfNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEvalTwoGroupsThreeGroupsEqZeroOfNeZero
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory

theorem coeff_at2_x1_x2_eq_zero_of_third_ne_zero {R : Type} [CommRing R] {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ) (he : e ≠ 0) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x1 x2) = 0 := by
  classical
  let g : Fin d ⊕ Fin d → Fin d ⊕ (Fin d ⊕ Fin d) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
  have hg : (Sum.elim x1 x2 : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = X ∘ g := by
    funext s; rcases s with s | s <;> rfl
  have h1 : at2 c x1 x2 = rename g c := by
    rw [rename_eq_subst, ← hg]; rfl
  rw [h1]
  apply coeff_rename_eq_zero
  rintro ⟨v, hv⟩
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra h; push_neg at h; exact he (Finsupp.ext h)
  apply hi
  have h2 := congrArg (fun w : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ => w (Sum.inr (Sum.inr i))) hv
  rw [Finsupp.mapDomain_notin_range] at h2
  · simpa using h2.symm
  · rintro ⟨s, hs⟩; rcases s with s | s <;> simp [g] at hs

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEvalTwoGroupsThreeGroupsEqZeroOfNeZeroStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_evalTwoGroups_threeGroups_eq_zero_of_ne_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), e ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x1 x2) = 0 := by
  first | exact @GlobalTheory.coeff_at2_x1_x2_eq_zero_of_third_ne_zero | exact GlobalTheory.coeff_at2_x1_x2_eq_zero_of_third_ne_zero | (intros; apply GlobalTheory.coeff_at2_x1_x2_eq_zero_of_third_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffProdPowFirstAddSecondThreeGroups
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffProdPowFirstAddSecondThreeGroups
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.BinomLeft

variable {R : Type} [CommRing R] {d : ℕ}

theorem natCast_eq_monomial {σ : Type} (n : ℕ) : ((n : ℕ) : MvPowerSeries σ R) = monomial 0 (n : R) := by
  rw [monomial_zero_eq_C_apply, map_natCast]

theorem pow_threeGroupsFirst_add_second_expansion (i : Fin d) (k : ℕ) :
    ((x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) ^ k =
      ∑ j ∈ Finset.range (k + 1),
        monomial (Finsupp.single (Sum.inl i) j + Finsupp.single (Sum.inr (Sum.inl i)) (k - j)) (k.choose j : R) := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [x1, x2, X_pow_eq, monomial_mul_monomial, one_mul, natCast_eq_monomial, add_zero, mul_one]

theorem expo_iff (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ) (p : Fin d → ℕ)
    (hp : ∀ i, p i ≤ α (Sum.inl i)) :
    Finsupp.sumElim a (Finsupp.sumElim b e) =
        (∑ i, (Finsupp.single (Sum.inl i) (p i) + Finsupp.single (Sum.inr (Sum.inl i)) (α (Sum.inl i) - p i))) +
          ∑ i, Finsupp.single (Sum.inr (Sum.inr i)) (α (Sum.inr i)) ↔
      α = Finsupp.sumElim (a + b) e ∧ p = ⇑a := by
  classical
  have hv : ∀ s, ((∑ i, (Finsupp.single (Sum.inl i) (p i) + Finsupp.single (Sum.inr (Sum.inl i)) (α (Sum.inl i) - p i))) +
          ∑ i, Finsupp.single (Sum.inr (Sum.inr i)) (α (Sum.inr i)) : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ) s =
        Sum.elim p (Sum.elim (fun i => α (Sum.inl i) - p i) (fun i => α (Sum.inr i))) s := by
    intro s
    rcases s with i | i | i
    · simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
    · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj, Ne.symm hj]) (by simp)]
      simp
    · simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  constructor
  · intro h
    have h1 : ∀ i, a i = p i := fun i => by
      have := DFunLike.congr_fun h (Sum.inl i); rw [hv] at this; simpa using this
    have h2 : ∀ i, b i = α (Sum.inl i) - p i := fun i => by
      have := DFunLike.congr_fun h (Sum.inr (Sum.inl i)); rw [hv] at this; simpa using this
    have h3 : ∀ i, e i = α (Sum.inr i) := fun i => by
      have := DFunLike.congr_fun h (Sum.inr (Sum.inr i)); rw [hv] at this; simpa using this
    refine ⟨?_, funext fun i => (h1 i).symm⟩
    ext s
    rcases s with i | i
    · have := hp i; have := h1 i; have := h2 i; simp; omega
    · simp [h3 i]
  · rintro ⟨rfl, rfl⟩
    ext s
    rw [hv]
    rcases s with i | i | i <;> simp

theorem coeff_prod_pow_add (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e))
        (α.prod fun s k => (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) x3 s) ^ k) =
      if α = Finsupp.sumElim (a + b) e then (∏ i, ((a + b) i).choose (a i) : R) else 0 := by
  classical
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, pow_threeGroupsFirst_add_second_expansion]
  rw [Finset.prod_univ_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [x3, X_pow_eq, prod_monomial, Finset.sum_mul, monomial_mul_monomial, mul_one, map_sum,
    coeff_monomial, Finset.prod_const_one]
  have hmem : ∀ p ∈ Fintype.piFinset fun i => Finset.range (α (Sum.inl i) + 1), ∀ i, p i ≤ α (Sum.inl i) := by
    intro p hp i
    have := Fintype.mem_piFinset.1 hp i
    rw [Finset.mem_range] at this
    omega
  split_ifs with hα
  · rw [Finset.sum_congr rfl fun p hp => by rw [if_congr (expo_iff α a b e p (hmem p hp)) rfl rfl]]
    simp only [hα, true_and]
    rw [Finset.sum_ite_eq']
    rw [if_pos]
    · simp
    · rw [Fintype.mem_piFinset]
      intro i
      simp only [Finset.mem_range, Finsupp.sumElim_apply, Sum.elim_inl, Finsupp.coe_add, Pi.add_apply]
      omega
  · refine Finset.sum_eq_zero fun p hp => ?_
    rw [if_neg]
    intro h
    exact hα ((expo_iff α a b e p (hmem p hp)).1 h).1

end GlobalTheory.BinomLeft
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffProdPowFirstAddSecondThreeGroupsStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_prod_pow_first_add_second_threeGroups : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) x3 s) ^ k) = if α = Finsupp.sumElim (a + b) e then (∏ i, ((a + b) i).choose (a i) : R) else 0 := by
  first | exact @GlobalTheory.BinomLeft.coeff_prod_pow_add | exact GlobalTheory.BinomLeft.coeff_prod_pow_add | (intros; apply GlobalTheory.BinomLeft.coeff_prod_pow_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSecondThirdEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSecondThirdEqZero
open MvPowerSeries

set_option autoImplicit false

namespace GlobalTheory.Katz

theorem coeff_at2_x2_x3_eq_zero_of_first_ne_zero {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (a b e : Fin d →₀ ℕ) (ha : a ≠ 0) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x2 x3) = 0 := by
  classical
  have hX : ∀ s, Sum.elim (x2 (R := R) (d := d)) x3 s
      = X (Sum.elim (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inr i)) s) := by
    intro s; cases s <;> rfl
  have hs : HasSubst (Sum.elim (x2 (R := R) (d := d)) x3) :=
    hasSubst_of_constantCoeff_zero fun s => by rw [hX]; exact constantCoeff_X _
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push_neg at h; exact ha (Finsupp.ext h)
  unfold at2
  rw [coeff_subst hs]
  apply finsum_eq_zero_of_forall_eq_zero
  intro α
  have key : ∃ β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, β (Sum.inl i) = 0 ∧
      (α.prod fun s k => (Sum.elim (x2 (R := R) (d := d)) x3 s) ^ k) = monomial β 1 := by
    unfold Finsupp.prod
    refine Finset.prod_induction _ (fun f => ∃ β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ,
      β (Sum.inl i) = 0 ∧ f = monomial β 1) ?_ ?_ ?_
    · rintro f g ⟨β, hβ, rfl⟩ ⟨γ, hγ, rfl⟩
      exact ⟨β + γ, by simp [hβ, hγ], by rw [monomial_mul_monomial, one_mul]⟩
    · exact ⟨0, rfl, (monomial_zero_one).symm⟩
    · intro s _
      refine ⟨Finsupp.single (Sum.elim (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inr i)) s) (α s), ?_, ?_⟩
      · cases s <;> simp
      · dsimp only
        rw [hX, X_pow_eq]
  obtain ⟨β, hβ, hp⟩ := key
  rw [hp, coeff_monomial_ne, smul_zero]
  intro h
  apply hi
  have := congrArg (fun w => w (Sum.inl i)) h
  simpa [hβ] using this

end GlobalTheory.Katz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSecondThirdEqZeroStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_second_third_eq_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), a ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x2 x3) = 0 := by
  first | exact @GlobalTheory.Katz.coeff_at2_x2_x3_eq_zero_of_first_ne_zero | exact GlobalTheory.Katz.coeff_at2_x2_x3_eq_zero_of_first_ne_zero | (intros; apply GlobalTheory.Katz.coeff_at2_x2_x3_eq_zero_of_first_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryDegreePartCocycleModIdeal
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.CobRel
theorem coeff_subst_sub_mem :
    ∀ {B Q σ τ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype σ]
      (N : Ideal B) (u ℓ : σ → MvPowerSeries τ B), (∀ s, constantCoeff (u s) = 0) →
      (∀ s (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (u s) = coeff β (ℓ s)) →
      ∀ (m : ℕ) (c : MvPowerSeries σ Q),
        (∀ α : σ →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) →
        ∀ (w : τ →₀ ℕ), w.degree = m → ∃ r ∈ N,
          coeff w (MvPowerSeries.subst (QLog.up (Q := Q) u) c) -
            coeff w (MvPowerSeries.subst (QLog.up (Q := Q) ℓ) c) = algebraMap B Q r := by
  intro B Q σ τ _ _ _ _ N u ℓ hu hlin m c hc w hw
  have hℓ : ∀ s, constantCoeff (ℓ s) = 0 := fun s => by
    simpa only [coeff_zero_eq_constantCoeff_apply, hu s] using (hlin s 0 (by simp)).symm
  have horder : ∀ s, (2 : ℕ∞) ≤ (u s - ℓ s).order := fun s =>
    nat_le_order (n := 2) fun β hβ => by
      rw [map_sub, hlin s β (by omega), sub_self]
  have huSubst : HasSubst (QLog.up (Q := Q) u) :=
    hasSubst_of_constantCoeff_zero fun s => by simp [QLog.up, hu s]
  have hℓSubst : HasSubst (QLog.up (Q := Q) ℓ) :=
    hasSubst_of_constantCoeff_zero fun s => by simp [QLog.up, hℓ s]
  rw [coeff_subst huSubst, coeff_subst hℓSubst,
    ← finsum_sub_distrib (coeff_subst_finite huSubst c w) (coeff_subst_finite hℓSubst c w)]
  refine finsum_induction (fun x : Q => ∃ r ∈ N, x = algebraMap B Q r)
    ⟨0, N.zero_mem, by simp⟩
    (fun x y ⟨r, hr, hx⟩ ⟨t, ht, hy⟩ => ⟨r + t, N.add_mem hr ht, by rw [hx, hy, map_add]⟩)
    fun α => ?_
  have hprod (v : σ → MvPowerSeries τ B) :
      (α.prod fun s e => QLog.up (Q := Q) v s ^ e) =
        MvPowerSeries.map (algebraMap B Q) (α.prod fun s e => v s ^ e) := by
    simp only [QLog.up, Finsupp.prod, map_prod, map_pow]
  rw [hprod u, hprod ℓ, coeff_map, coeff_map, smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub,
    ← map_sub]
  by_cases h : α.degree < m
  · obtain ⟨b, hb, hcb⟩ := hc α h
    exact ⟨b * _, N.mul_mem_right _ hb, by rw [hcb, map_mul]⟩
  · have hmono := GlobalTheory.SubstMod.order_monoProd_sub u ℓ hu hℓ horder α
    have hdegree : w.degree < α.degree + 1 := by omega
    have hzero : coeff w ((α.prod fun s e => u s ^ e) - α.prod fun s e => ℓ s ^ e) = 0 :=
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hdegree) hmono)
    exact ⟨0, N.zero_mem, by rw [hzero, map_zero, mul_zero]⟩

theorem coeff_op_of_degree_le_one : ∀ {B O : Type} [CommRing B] [CommRing O] (θ : B →+* O) {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}, IsLift θ μ → ∀ {τ : Type} (u v : Fin d → MvPowerSeries τ B), (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ (i : Fin d) (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (op μ u v i) = coeff β (u i + v i) := GlobalTheory.T.coeff_formalGroupLawEvalPoints_of_degree_le_one

theorem coeff_prod_addLeft : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) x3 s) ^ k) = if α = Finsupp.sumElim (a + b) e then (∏ i, ((a + b) i).choose (a i) : R) else 0 := GlobalTheory.T.coeff_prod_pow_first_add_second_threeGroups

theorem coeff_prod_addRight : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) s) ^ k) = if α = Finsupp.sumElim a (b + e) then (∏ i, ((b + e) i).choose (b i) : R) else 0 := GlobalTheory.T.coeff_prod_pow_x1_x2_add_x3

theorem coeff_evalTwoGroups_second_third_eq_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), a ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x2 x3) = 0 := GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_second_third_eq_zero

theorem coeff_evalTwoGroups_first_second_eq_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), e ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x1 x2) = 0 := GlobalTheory.T.coeff_evalTwoGroups_threeGroups_eq_zero_of_ne_zero

end GlobalTheory.CobRel

namespace GlobalTheory.CobRel

theorem degree_sumElim3 {d : ℕ} (a b e : Fin d →₀ ℕ) :
    (Finsupp.sumElim a (Finsupp.sumElim b e)).degree = a.degree + b.degree + e.degree := by
  simp [Finsupp.degree_eq_sum, Fintype.sum_sum_type, add_assoc]

theorem x_hasSubst {R : Type} [CommRing R] {d : ℕ} (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)
    (hu : ∀ j, constantCoeff (u j) = 0) (hv : ∀ j, constantCoeff (v j) = 0) :
    HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]

end GlobalTheory.CobRel

namespace GlobalTheory.CobRel

theorem cocycle_rel_mod : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (m : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) Q), (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) → In N (cob2 (QLog.up (Q := Q) μ) c) → ∀ n : Fin d →₀ ℕ, n.degree = m → ∀ a b : Fin d →₀ ℕ, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n → ∃ r ∈ N, (∏ i, Nat.choose ((a + b) i) (a i) : Q) * coeff (Finsupp.sumElim (a + b) (n - (a + b))) c - (∏ i, Nat.choose ((n - a) i) (b i) : Q) * coeff (Finsupp.sumElim a (n - a)) c = algebraMap B Q r := by
  intro B O Q _ _ _ _ θ d μ hμ N m c hc hcob n hn a b ha _ hab hab'
  set e := n - (a + b) with he_def
  have he : e ≠ 0 := fun h => hab' (le_antisymm hab (tsub_eq_zero_iff_le.1 h))
  have hbe : b + e = n - a := by
    ext i
    have := hab i
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Pi.sub_apply, he_def] at this ⊢
    omega
  have hn' : a + b + e = n := by
    ext i
    have := hab i
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Pi.sub_apply, he_def] at this ⊢
    omega
  set w : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ := Finsupp.sumElim a (Finsupp.sumElim b e) with hw_def
  have hw : w.degree = m := by
    rw [← hn, ← hn', hw_def, degree_sumElim3, map_add (f := _), map_add (f := _)]
  have hX : ∀ (R : Type) [CommRing R] (j : Fin d),
      constantCoeff (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 ∧
      constantCoeff (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 ∧
      constantCoeff (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 := fun R _ j => by
    simp [x1, x2, x3]
  have hop : ∀ (R : Type) [CommRing R] (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
      (∀ i, constantCoeff (ν i) = 0) → ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ i,
      constantCoeff (op ν u v i) = 0 := fun R _ ν hν u v hu hv i =>
    constantCoeff_subst_eq_zero (x_hasSubst u v hu hv) (fun s => by cases s <;> simp [hu, hv]) (hν i)
  have hmapop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B),
      (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ i,
      map (algebraMap B Q) (op μ u v i) = op (QLog.up (Q := Q) μ) (fun j => map (algebraMap B Q) (u j))
        (fun j => map (algebraMap B Q) (v j)) i := fun u v hu hv i => by
    simp only [op, at2, QLog.up]
    rw [map_subst (x_hasSubst u v hu hv)]
    congr 1
    funext s
    cases s <;> rfl
  have hmX : ∀ j, (map (algebraMap B Q) (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B) = x1 j) ∧
      (map (algebraMap B Q) (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B) = x2 j) ∧
      (map (algebraMap B Q) (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B) = x3 j) := fun j => by
    simp [x1, x2, x3, map_X]

  have hc2 : ∀ s, constantCoeff (Sum.elim (op μ x1 x2) x3 s) = 0 := by
    intro s
    cases s with
    | inl i => exact hop B μ hμ.const _ _ (fun j => (hX B j).1) (fun j => (hX B j).2.1) i
    | inr i => exact (hX B i).2.2
  have hd2 : ∀ s (β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ), β.degree ≤ 1 →
      coeff β (Sum.elim (op μ x1 x2) x3 s) = coeff β (Sum.elim (fun i => x1 i + x2 i) x3 s) := by
    intro s β hβ
    cases s with
    | inl i => exact coeff_op_of_degree_le_one θ hμ _ _ (fun j => (hX B j).1) (fun j => (hX B j).2.1) i β hβ
    | inr i => rfl
  obtain ⟨r2, hr2, h2⟩ := coeff_subst_sub_mem N _ _ hc2 hd2 m c hc w hw
  have hu2 : QLog.up (Q := Q) (Sum.elim (op μ x1 x2) x3) = Sum.elim (op (QLog.up (Q := Q) μ) x1 x2) x3 := by
    funext s
    cases s with
    | inl i =>
      simp only [QLog.up, Sum.elim_inl]
      rw [hmapop _ _ (fun j => (hX B j).1) (fun j => (hX B j).2.1)]
      simp only [(hmX _).1, (hmX _).2.1]
    | inr i => simp only [QLog.up, Sum.elim_inr]; exact (hmX i).2.2
  have hl2 : QLog.up (Q := Q) (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) x3) =
      Sum.elim (fun i => x1 i + x2 i) x3 := by
    funext s
    cases s with
    | inl i => simp only [QLog.up, Sum.elim_inl, map_add (f := _), (hmX i).1, (hmX i).2.1]
    | inr i => simp only [QLog.up, Sum.elim_inr]; exact (hmX i).2.2
  rw [hu2, hl2] at h2
  have hv2 : coeff w (MvPowerSeries.subst (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) Q)) x3) c) =
      (∏ i, ((a + b) i).choose (a i) : Q) * coeff (Finsupp.sumElim (a + b) e) c := by
    rw [coeff_subst (x_hasSubst _ _ (fun j => by simp [(hX Q j).1, (hX Q j).2.1]) (fun j => (hX Q j).2.2)),
      finsum_eq_single _ (Finsupp.sumElim (a + b) e)]
    · rw [hw_def, coeff_prod_addLeft, ite_eq_left rfl, smul_eq_mul, mul_comm]
    · intro α hα
      rw [hw_def, coeff_prod_addLeft, ite_eq_right hα, smul_zero]

  have hc3 : ∀ s, constantCoeff (Sum.elim x1 (op μ x2 x3) s) = 0 := by
    intro s
    cases s with
    | inl i => exact (hX B i).1
    | inr i => exact hop B μ hμ.const _ _ (fun j => (hX B j).2.1) (fun j => (hX B j).2.2) i
  have hd3 : ∀ s (β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ), β.degree ≤ 1 →
      coeff β (Sum.elim x1 (op μ x2 x3) s) = coeff β (Sum.elim x1 (fun i => x2 i + x3 i) s) := by
    intro s β hβ
    cases s with
    | inl i => rfl
    | inr i => exact coeff_op_of_degree_le_one θ hμ _ _ (fun j => (hX B j).2.1) (fun j => (hX B j).2.2) i β hβ
  obtain ⟨r3, hr3, h3⟩ := coeff_subst_sub_mem N _ _ hc3 hd3 m c hc w hw
  have hu3 : QLog.up (Q := Q) (Sum.elim x1 (op μ x2 x3)) = Sum.elim x1 (op (QLog.up (Q := Q) μ) x2 x3) := by
    funext s
    cases s with
    | inl i => simp only [QLog.up, Sum.elim_inl]; exact (hmX i).1
    | inr i =>
      simp only [QLog.up, Sum.elim_inr]
      rw [hmapop _ _ (fun j => (hX B j).2.1) (fun j => (hX B j).2.2)]
      simp only [(hmX _).2.1, (hmX _).2.2]
  have hl3 : QLog.up (Q := Q) (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B))) =
      Sum.elim x1 (fun i => x2 i + x3 i) := by
    funext s
    cases s with
    | inl i => simp only [QLog.up, Sum.elim_inl]; exact (hmX i).1
    | inr i => simp only [QLog.up, Sum.elim_inr, map_add (f := _), (hmX i).2.1, (hmX i).2.2]
  rw [hu3, hl3] at h3
  have hv3 : coeff w (MvPowerSeries.subst (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) Q))) c) =
      (∏ i, ((b + e) i).choose (b i) : Q) * coeff (Finsupp.sumElim a (b + e)) c := by
    rw [coeff_subst (x_hasSubst _ _ (fun j => (hX Q j).1) (fun j => by simp [(hX Q j).2.1, (hX Q j).2.2])),
      finsum_eq_single _ (Finsupp.sumElim a (b + e))]
    · rw [hw_def, coeff_prod_addRight, ite_eq_left rfl, smul_eq_mul, mul_comm]
    · intro α hα
      rw [hw_def, coeff_prod_addRight, ite_eq_right hα, smul_zero]

  obtain ⟨k, hk, hk'⟩ := hcob w
  have hsplit : coeff w (cob2 (QLog.up (Q := Q) μ) c) = coeff w (at2 c x2 x3) -
      coeff w (MvPowerSeries.subst (Sum.elim (op (QLog.up (Q := Q) μ) x1 x2) x3) c) +
      coeff w (MvPowerSeries.subst (Sum.elim x1 (op (QLog.up (Q := Q) μ) x2 x3)) c) - coeff w (at2 c x1 x2) := by
    simp only [cob2, map_sub, map_add (f := _)]; rfl
  rw [hsplit, hw_def, coeff_evalTwoGroups_second_third_eq_zero c a b e ha, coeff_evalTwoGroups_first_second_eq_zero c a b e he, ← hw_def] at hk'
  rw [hbe] at hv3
  refine ⟨-k - r2 + r3, N.add_mem (N.sub_mem (N.neg_mem hk) hr2) hr3, ?_⟩
  rw [map_add (f := _), map_sub, map_neg, ← hk', ← h2, ← h3, hv2, hv3]
  ring

end GlobalTheory.CobRel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryDegreePartCocycleModIdealStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_degree_part_cocycle_mod_ideal : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (m : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) Q), (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) → In N (cob2 (up Q μ) c) → ∀ n : Fin d →₀ ℕ, n.degree = m → ∀ a b : Fin d →₀ ℕ, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n → ∃ r ∈ N, (∏ i, Nat.choose ((a + b) i) (a i) : Q) * coeff (Finsupp.sumElim (a + b) (n - (a + b))) c - (∏ i, Nat.choose ((n - a) i) (b i) : Q) * coeff (Finsupp.sumElim a (n - a)) c = algebraMap B Q r := by
  first | exact @GlobalTheory.CobRel.cocycle_rel_mod | exact GlobalTheory.CobRel.cocycle_rel_mod | (intros; apply GlobalTheory.CobRel.cocycle_rel_mod <;> assumption)
end
