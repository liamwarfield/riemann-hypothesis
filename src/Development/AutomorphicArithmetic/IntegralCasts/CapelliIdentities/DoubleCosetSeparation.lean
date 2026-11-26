module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupportDcos

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SeparableOfNewtonPolygon
private lemma val_nat_le_one {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) (m : ℕ) : w (m : L) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ]
    exact w.map_add_le ih (by simp)

private lemma exists_peak {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (n : ℕ) (t : ℕ → Γ)
    (h0 : ∀ k ≤ n, 0 < t k) (hc : ∀ k, k + 2 ≤ n → t k * t (k + 2) < t (k + 1) * t (k + 1)) :
    ∃ j ≤ n, ∀ k ≤ n, k ≠ j → k + 1 ≠ j → t k < t j := by
  classical
  have hex : ∃ j, n ≤ j ∨ t (j + 1) < t j := ⟨n, Or.inl le_rfl⟩
  set j := Nat.find hex with hj
  have hjn : j ≤ n := Nat.find_min' hex (Or.inl le_rfl)
  have hlo : ∀ k < j, t k ≤ t (k + 1) := fun k hk =>
    not_lt.1 fun h => Nat.find_min hex hk (Or.inr h)
  have hlo' : ∀ k, k + 1 < j → t k < t (k + 1) := by
    intro k hk
    have h1 := hc k (by omega)
    have h2 : t (k + 1) * t (k + 1) ≤ t (k + 1) * t (k + 2) :=
      mul_le_mul_of_nonneg_left (hlo (k + 1) hk) zero_le
    exact lt_of_mul_lt_mul_right (h1.trans_le h2) zero_le
  have hhi : ∀ k, j ≤ k → k < n → t (k + 1) < t k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro h
      rcases Nat.find_spec hex with h' | h'
      · omega
      · exact h'
    | succ k hk ih =>
      intro h
      have h1 := hc k (by omega)
      have h2 : t (k + 1) * t (k + 1) ≤ t k * t (k + 1) :=
        mul_le_mul_of_nonneg_right (ih (by omega)).le zero_le
      exact lt_of_mul_lt_mul_left (h1.trans_le h2) zero_le
  have hle : ∀ k ≤ j, t k ≤ t j := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self => exact le_rfl
    | of_succ k hk ih => exact (hlo k hk).trans ih
  have hgt : ∀ k, j + 1 ≤ k → k ≤ n → t k < t j := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro h; exact hhi j le_rfl (by omega)
    | succ k hk ih => intro h; exact (hhi k (by omega) (by omega)).trans (ih (by omega))
  refine ⟨j, hjn, fun k hk h1 h2 => ?_⟩
  rcases lt_or_gt_of_ne h1 with h | h
  · exact (hlo' k (by omega)).trans_le (hle _ (by omega))
  · exact hgt k h hk

private lemma no_double_zero {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) (n : ℕ) (b : ℕ → L) (h0 : ∀ k ≤ n, b k ≠ 0)
    (hc : ∀ k, k + 2 ≤ n → w (b k * b (k + 2)) < w (b (k + 1) * b (k + 1)))
    (h1 : ∑ k ∈ Finset.range (n + 1), b k = 0)
    (h2 : ∑ k ∈ Finset.range (n + 1), (k : L) * b k = 0) : False := by
  have hpos : ∀ k ≤ n, 0 < w (b k) := fun k hk => zero_lt_iff.2 ((map_ne_zero w).2 (h0 k hk))
  obtain ⟨j, hjn, hj⟩ := exists_peak n (fun k => w (b k)) hpos
    (fun k hk => by simpa only [map_mul] using hc k hk)
  have hs : ∑ k ∈ Finset.range (n + 1), (((k + 1 : ℕ) : L) - (j : L)) * b k = 0 := by
    have : ∀ k : ℕ, (((k + 1 : ℕ) : L) - (j : L)) * b k = (k : L) * b k + (1 - (j : L)) * b k := by
      intro k; push_cast; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, mul_zero, add_zero]
  have hjj : (((j + 1 : ℕ) : L) - (j : L)) * b j = b j := by push_cast; ring
  have key := w.map_sum_eq_of_lt (s := Finset.range (n + 1))
    (f := fun k => (((k + 1 : ℕ) : L) - (j : L)) * b k) (j := j)
    (Finset.mem_range.2 (by omega)) (by
      intro k hk
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hk
      rw [hjj]
      by_cases hkj : k + 1 = j
      · rw [hkj, sub_self, zero_mul, map_zero]
        exact hpos j hjn
      · rw [map_mul]
        refine lt_of_le_of_lt ?_ (hj k (by omega) hk.2 hkj)
        exact mul_le_of_le_one_left zero_le
          (w.map_sub_le (val_nat_le_one w _) (val_nat_le_one w _)))
  rw [hs, hjj, map_zero] at key
  exact (hpos j hjn).ne key

private lemma exists_extension {K L Γ : Type} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (f : K →+* L) :
    ∃ A : ValuationSubring L, ∀ x y : K, v x < v y → A.valuation (f x) < A.valuation (f y) := by
  obtain ⟨A, h, hA⟩ := IsLocalRing.exists_factor_valuationRing
    (f.comp v.valuationSubring.subtype)
  refine ⟨A, fun x y hxy => ?_⟩
  have hy : 0 < v y := lt_of_le_of_lt zero_le hxy
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  have hlt : v (x / y) < 1 := by
    rw [map_div₀]
    exact (div_lt_one₀ hy).2 hxy
  let z : v.valuationSubring := ⟨x / y, hlt.le⟩
  have hz : z ∈ IsLocalRing.maximalIdeal v.valuationSubring :=
    (Valuation.mem_maximalIdeal_iff _ _).2 hlt
  haveI : IsLocalRing A.toSubring := inferInstanceAs (IsLocalRing A)
  have hz' := (A.valuation_lt_one_iff _).1 (map_nonunit
    ((f.comp v.valuationSubring.subtype).codRestrict A.toSubring h) z hz)
  have hz'' : A.valuation (f (x / y)) < 1 := hz'
  rw [map_div₀, map_div₀] at hz''
  exact (div_lt_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 ((map_ne_zero f).2 hy0)))).1 hz''

private lemma tail_succ {Γ : Type} [CommMonoid Γ] {n : ℕ} (γ : Fin n → Γ) (k : ℕ) (hk : k < n) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), γ i =
      γ ⟨k, hk⟩ * ∏ i ∈ Finset.univ.filter (fun i : Fin n => k + 1 ≤ i.val), γ i := by
  rw [← Finset.prod_insert (by simp)]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

theorem UpperTheory.separable_of_newton_polygon :
    ∀ {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (n : ℕ) (γ : Fin n → Γ),
        StrictMono γ → (∀ i, γ i ≠ 0) → ∀ p : Polynomial K, p.Monic → p.natDegree = n →
        (∀ k ≤ n, v (p.coeff k) = ∏ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), γ i) → p.Separable := by
  intro K Γ _ _ v n γ hγ hγ0 p _ hn hv
  have hv0 : ∀ k ≤ n, v (p.coeff k) ≠ 0 := fun k hk => by
    rw [hv k hk]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hγ0 i
  have ha0 : ∀ k ≤ n, p.coeff k ≠ 0 := fun k hk => (map_ne_zero v).1 (hv0 k hk)
  have hstep : ∀ k (hk : k < n), v (p.coeff k) = γ ⟨k, hk⟩ * v (p.coeff (k + 1)) := fun k hk => by
    rw [hv k hk.le, hv (k + 1) hk, tail_succ γ k hk]
  have hconc : ∀ k, k + 2 ≤ n →
      v (p.coeff k * p.coeff (k + 2)) < v (p.coeff (k + 1) * p.coeff (k + 1)) := by
    intro k hk
    have e1 := hstep k (by omega)
    have e2 := hstep (k + 1) (by omega)
    have hlt : γ ⟨k, by omega⟩ < γ ⟨k + 1, by omega⟩ := hγ (by simp [Fin.lt_def])
    have hp : 0 < v (p.coeff (k + 1)) * v (p.coeff (k + 2)) :=
      mul_pos (zero_lt_iff.2 (hv0 _ (by omega))) (zero_lt_iff.2 (hv0 _ hk))
    calc v (p.coeff k * p.coeff (k + 2))
        = γ ⟨k, by omega⟩ * (v (p.coeff (k + 1)) * v (p.coeff (k + 2))) := by
          rw [map_mul, e1, mul_assoc]
      _ < γ ⟨k + 1, by omega⟩ * (v (p.coeff (k + 1)) * v (p.coeff (k + 2))) :=
          mul_lt_mul_of_pos_right hlt hp
      _ = v (p.coeff (k + 1) * p.coeff (k + 1)) := by
          rw [map_mul, mul_left_comm, ← e2]
  rw [Polynomial.separable_def,
    Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K)]
  intro r
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨hp, hd⟩ := hcon
  set f := algebraMap K (AlgebraicClosure K) with hf
  obtain ⟨A, hA⟩ := exists_extension v f
  have hr : r ≠ 0 := by
    rintro rfl
    rw [← Polynomial.coeff_zero_eq_aeval_zero'] at hp
    exact ha0 0 (Nat.zero_le _) ((map_eq_zero _).1 hp)
  refine no_double_zero A.valuation n (fun k => f (p.coeff k) * r ^ k)
    (fun k hk => mul_ne_zero ((map_ne_zero f).2 (ha0 k hk)) (pow_ne_zero _ hr)) ?_ ?_ ?_
  · intro k hk
    have e1 : f (p.coeff k) * r ^ k * (f (p.coeff (k + 2)) * r ^ (k + 2)) =
        f (p.coeff k * p.coeff (k + 2)) * r ^ (2 * k + 2) := by rw [map_mul]; ring
    have e2 : f (p.coeff (k + 1)) * r ^ (k + 1) * (f (p.coeff (k + 1)) * r ^ (k + 1)) =
        f (p.coeff (k + 1) * p.coeff (k + 1)) * r ^ (2 * k + 2) := by rw [map_mul]; ring
    rw [e1, e2, map_mul A.valuation, map_mul A.valuation]
    exact mul_lt_mul_of_pos_right (hA _ _ (hconc k hk))
      (zero_lt_iff.2 ((map_ne_zero _).2 (pow_ne_zero _ hr)))
  · rw [Polynomial.aeval_eq_sum_range, hn] at hp
    simpa only [Algebra.smul_def] using hp
  · have hX : Polynomial.aeval r (Polynomial.derivative p * Polynomial.X) = 0 := by rw [map_mul, hd, zero_mul]
    have hcoeff : ∀ k : ℕ, (Polynomial.derivative p * Polynomial.X).coeff k = (k : K) * p.coeff k := by
      intro k
      cases k with
      | zero => simp
      | succ k => rw [Polynomial.coeff_mul_X, Polynomial.coeff_derivative]; push_cast; ring
    have hdeg : (Polynomial.derivative p * Polynomial.X).natDegree < n + 1 := by
      rw [Nat.lt_succ_iff, Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [hcoeff, Polynomial.coeff_eq_zero_of_natDegree_lt (hn ▸ hk), mul_zero]
    rw [Polynomial.aeval_eq_sum_range' hdeg] at hX
    simpa only [hcoeff, Algebra.smul_def, map_mul, map_natCast, mul_assoc] using hX
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsOpenValuationLtOne
open ValuativeRel

private lemma UpperTheory.isOpen_of_add_small {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsValuativeTopology k] (s : Set k)
    (hs : ∀ x ∈ s, ∀ z, valuation k z < 1 → x + z ∈ s) : IsOpen s := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff]
  refine ⟨1, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hs x hx z (by simpa using hz)

private lemma UpperTheory.isOpen_valuation_le_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsValuativeTopology k] : IsOpen {x : k | valuation k x ≤ 1} :=
  UpperTheory.isOpen_of_add_small _ fun _ hx _ hz => (valuation k).map_add_le hx hz.le

private lemma UpperTheory.isOpen_setOf_valuation_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsValuativeTopology k] : IsOpen {x : k | valuation k x < 1} :=
  UpperTheory.isOpen_of_add_small _ fun _ hx _ hz => (valuation k).map_add_lt hx hz

private lemma UpperTheory.isClosed_valuation_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsValuativeTopology k] : IsClosed {x : k | valuation k x < 1} := by
  rw [← isOpen_compl_iff]
  refine UpperTheory.isOpen_of_add_small _ fun x hx z hz h => hx ?_
  have h' : valuation k (x + z - z) < 1 := (valuation k).map_sub_lt h hz
  simpa using h'

theorem UpperTheory.iwahori_subgroup_open :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
        (S : Set (Matrix.GeneralLinearGroup (Fin n) k)),
        (∀ g : Matrix.GeneralLinearGroup (Fin n) k, g ∈ S ↔
          (∀ i j, ValuativeRel.valuation k (g.val i j) ≤ 1) ∧ (∀ i j, ValuativeRel.valuation k ((g⁻¹).val i j) ≤ 1) ∧
            ∀ i j, j < i → ValuativeRel.valuation k (g.val i j) < 1) →
        IsOpen S ∧ IsCompact S := by
  intro k _ _ _ _ n S hS
  have c1 : ∀ i j, Continuous fun g : Matrix.GeneralLinearGroup (Fin n) k => g.val i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have c2 : ∀ i j, Continuous fun g : Matrix.GeneralLinearGroup (Fin n) k => (g⁻¹).val i j :=
    fun i j => Units.continuous_coe_inv.matrix_elem i j
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  constructor
  · have e : S = (⋂ i, ⋂ j, (fun g : Matrix.GeneralLinearGroup (Fin n) k => g.val i j) ⁻¹'
          {x : k | valuation k x ≤ 1}) ∩
        ((⋂ i, ⋂ j, (fun g : Matrix.GeneralLinearGroup (Fin n) k => (g⁻¹).val i j) ⁻¹'
          {x : k | valuation k x ≤ 1}) ∩
        ⋂ i, ⋂ j, ⋂ (_ : j < i), (fun g : Matrix.GeneralLinearGroup (Fin n) k => g.val i j) ⁻¹'
          {x : k | valuation k x < 1}) := by
      ext g
      rw [hS]
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      rfl
    rw [e]
    refine IsOpen.inter ?_ (IsOpen.inter ?_ ?_)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (UpperTheory.isOpen_valuation_le_one k).preimage (c1 i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (UpperTheory.isOpen_valuation_le_one k).preimage (c2 i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        isOpen_iInter_of_finite fun _ => (UpperTheory.isOpen_setOf_valuation_lt_one k).preimage (c1 i j)
  · let M : Set (Matrix (Fin n) (Fin n) k) :=
      Set.univ.pi fun _ => Set.univ.pi fun _ => {x : k | valuation k x ≤ 1}
    have hM : IsCompact M := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      IsNonarchimedeanLocalField.isCompact_closedBall k 1
    have hP : IsCompact (M ×ˢ (MulOpposite.op '' M)) :=
      hM.prod (hM.image MulOpposite.continuous_op)
    have hK := (Units.isClosedEmbedding_embedProduct
      (α := Matrix (Fin n) (Fin n) k)).isCompact_preimage hP
    have hC : IsClosed (⋂ i, ⋂ j, ⋂ (_ : j < i),
        (fun g : Matrix.GeneralLinearGroup (Fin n) k => g.val i j) ⁻¹'
          {x : k | valuation k x < 1}) :=
      isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        (UpperTheory.isClosed_valuation_lt_one k).preimage (c1 i j)
    convert hK.inter_right hC using 1
    ext g
    rw [hS]
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_prod]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨fun i _ j _ => h1 i j, (g⁻¹).val, fun i _ j _ => h2 i j, rfl⟩, h3⟩
    · rintro ⟨⟨h1, m, hm, hme⟩, h3⟩
      have hm' : m = (g⁻¹).val := MulOpposite.op_injective hme
      subst hm'
      exact ⟨fun i j => h1 i trivial j trivial, fun i j => hm i trivial j trivial, h3⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CharpolyCoeffValuation
private theorem UpperTheory.valuation_perm_term {K Γ ι : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) (σ : Equiv.Perm ι) :
    v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) = ∏ i, v (M (σ i) i) := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, map_prod]

private theorem UpperTheory.valuation_det_le_one_of_entries_le_one' {K Γ ι : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K)
    (h1 : ∀ i j, v (M i j) ≤ 1) : v M.det ≤ 1 := by
  rw [Matrix.det_apply]
  refine v.map_sum_le fun σ _ => ?_
  rw [UpperTheory.valuation_perm_term]
  exact Finset.prod_le_one' fun i _ => h1 _ _

private theorem UpperTheory.val_det_eq_one_iff {K Γ ι : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Fintype ι] [DecidableEq ι] [LinearOrder ι] (M : Matrix ι ι K)
    (h1 : ∀ i j, v (M i j) ≤ 1) (h2 : ∀ i j, j < i → v (M i j) < 1) :
    v M.det = 1 ↔ ∀ i, v (M i i) = 1 := by
  have hlt : ∀ (σ : Equiv.Perm ι) (j : ι), v (M (σ j) j) < 1 →
      v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) < 1 := by
    intro σ j hj
    rw [UpperTheory.valuation_perm_term, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (Finset.prod_le_one' fun i _ => h1 _ _)) hj
  have hσ : ∀ σ : Equiv.Perm ι, σ ≠ 1 → v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) < 1 := by
    intro σ hσ
    have : ∃ j, j < σ j := by
      by_contra hcon
      push Not at hcon
      apply hσ
      ext i
      induction i using WellFoundedLT.induction with
      | _ i ih =>
        rcases (hcon i).lt_or_eq with h | h
        · exact σ.injective (ih _ h)
        · exact h
    obtain ⟨j, hj⟩ := this
    exact hlt σ j (h2 _ _ hj)
  constructor
  · intro h i
    by_contra hne
    have hi : v (M i i) < 1 := lt_of_le_of_ne (h1 _ _) hne
    refine absurd h (ne_of_lt ?_)
    rw [Matrix.det_apply]
    refine v.map_sum_lt one_ne_zero fun σ _ => ?_
    by_cases h' : σ = 1
    · exact hlt σ i (by simpa [h'] using hi)
    · exact hσ σ h'
  · intro h
    have h0 : v (Equiv.Perm.sign (1 : Equiv.Perm ι) • ∏ i, M ((1 : Equiv.Perm ι) i) i) = 1 := by
      rw [UpperTheory.valuation_perm_term]
      exact Finset.prod_eq_one fun i _ => h i
    rw [Matrix.det_apply, v.map_sum_eq_of_lt (Finset.mem_univ 1), h0]
    intro σ hσ'
    rw [h0]
    exact hσ σ (by simpa using hσ')

private theorem UpperTheory.prod_lt_of_strictMono {Γ ι : Type} [LinearOrderedCommGroupWithZero Γ]
    [LinearOrder ι] (f : ι → Γ) (hf : StrictMono f) (h0 : ∀ i, 0 < f i) (S T : Finset ι)
    (hc : S.card = T.card) (hne : S ≠ T) (hT : ∀ i j, i ∉ T → j ∈ T → i < j) :
    ∏ i ∈ S, f i < ∏ i ∈ T, f i := by
  have hc' : (S \ T).card = (T \ S).card := Finset.card_sdiff_comm hc
  have hS : (S \ T).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub hc.ge)
  have hT' : (T \ S).Nonempty := by
    rw [← Finset.card_pos, ← hc', Finset.card_pos]
    exact hS
  obtain ⟨c, hcm, hcmax⟩ := Finset.exists_max_image (S \ T) id hS
  have key : ∏ i ∈ S \ T, f i < ∏ i ∈ T \ S, f i := by
    calc ∏ i ∈ S \ T, f i ≤ ∏ _i ∈ S \ T, f c :=
          Finset.prod_le_prod' fun i hi => hf.monotone (hcmax i hi)
      _ = ∏ _i ∈ T \ S, f c := by simp [hc']
      _ < _ := Finset.prod_lt_prod_of_nonempty₀ (fun _ _ => h0 c)
          (fun i hi => hf (hT _ _ (Finset.mem_sdiff.1 hcm).2 (Finset.mem_sdiff.1 hi).1)) hT'
  rw [← Finset.prod_inter_mul_prod_diff S T, ← Finset.prod_inter_mul_prod_diff T S,
    Finset.inter_comm T S]
  exact mul_lt_mul_of_pos_left key (Finset.prod_pos fun i _ => h0 i)

theorem UpperTheory.charpoly_coeff_valuation :
    ∀ {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (n : ℕ)
        (M : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
        (∀ i j, v (M i j) ≤ 1) → (∀ i j, j < i → v (M i j) < 1) → v M.det = 1 →
        StrictMono (fun i => v (d i)) → (∀ i, d i ≠ 0) →
        ∀ k ≤ n, v ((Matrix.diagonal d * M).charpoly.coeff k) =
          ∏ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), v (d i) := by
  intro K Γ _ _ v n M d h1 h2 hdet hmono hd k hk
  have hdiag := (UpperTheory.val_det_eq_one_iff v M h1 h2).1 hdet
  have hminor : ∀ S : Finset (Fin n),
      v ((Matrix.diagonal d * M).submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det
        = (∏ i ∈ S, v (d i)) *
          v (M.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det := by
    intro S
    have : (Matrix.diagonal d * M).submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)
        = Matrix.of fun i j : S => d i *
          (M.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)) i j := by
      ext i j
      simp
    rw [this, Matrix.det_mul_column, map_mul, map_prod, Finset.prod_coe_sort S fun i => v (d i)]
  set T := Finset.univ.filter (fun i : Fin n => k ≤ i.val) with hT
  have hcard : T.card = n - k := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i : Fin n => k ≤ i.val)
    have h' : (Finset.univ.filter fun i : Fin n => ¬ k ≤ i.val).card = k := by
      simp only [not_le]
      rw [Fin.card_filter_val_lt, min_eq_right hk]
    rw [h', Finset.card_univ, Fintype.card_fin, ← hT] at h
    omega
  have hTval : v ((Matrix.diagonal d * M).submatrix (Subtype.val : T → Fin n)
      (Subtype.val : T → Fin n)).det = ∏ i ∈ T, v (d i) := by
    rw [hminor, (UpperTheory.val_det_eq_one_iff v
      (M.submatrix (Subtype.val : T → Fin n) (Subtype.val : T → Fin n)) (fun i j => h1 _ _)
      (fun i j h => h2 _ _ h)).2 fun i => hdiag _, mul_one]
  have hc := Matrix.charpoly_coeff_eq_sum_minors (Matrix.diagonal d * M) (n - k) (by simp)
  rw [Fintype.card_fin, Nat.sub_sub_self hk] at hc
  have hmem : T ∈ Finset.powersetCard (n - k) (Finset.univ : Finset (Fin n)) := by
    simp [hcard]
  rw [hc, map_mul, map_pow, v.map_neg, map_one, one_pow, one_mul, v.map_sum_eq_of_lt hmem, hTval]
  intro S hS
  rw [hTval, hminor]
  simp only [Finset.mem_sdiff, Finset.mem_powersetCard, Finset.mem_singleton] at hS
  refine lt_of_le_of_lt
    (mul_le_of_le_one_right' (UpperTheory.valuation_det_le_one_of_entries_le_one' v _ fun i j => h1 _ _)) ?_
  refine UpperTheory.prod_lt_of_strictMono (fun i => v (d i)) hmono
    (fun i => zero_lt_iff.2 ((v.ne_zero_iff).2 (hd i))) S T (hS.1.2.trans hcard.symm) hS.2 ?_
  intro i j hi hj
  simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi hj
  exact Fin.lt_def.2 (lt_of_lt_of_le hi hj)
end

open ValuativeRel Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.Reformulated.B.DoubleCosetSeparation.mem_iw {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (g : GL (Fin n) k) :
    g ∈ GlobalTheory.SmGL.iwahori k (Fin n) ↔
      (∀ i j, valuation k (g.val i j) ≤ 1) ∧ (∀ i j, valuation k ((g⁻¹).val i j) ≤ 1) ∧
        ∀ i j, j < i → valuation k (g.val i j) < 1 := by
  constructor
  · intro hg
    have key : ∀ h ∈ GlobalTheory.SmGL.iwahori k (Fin n), ∀ i j, valuation k (h.val i j) ≤ 1 := by
      rintro _ ⟨h, -, rfl⟩ i j
      exact (h.val i j).2
    exact ⟨key g hg, key _ (inv_mem hg), (GlobalTheory.SmGL.mem_iwahori.1 hg).2⟩
  · rintro ⟨h1, h2, h3⟩
    let A : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, h1 i j⟩
    let B : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
    have hA : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
    have hB : (algebraMap 𝒪[k] k).mapMatrix B = (g⁻¹).val := rfl
    have inj : Function.Injective
        ((algebraMap 𝒪[k] k).mapMatrix : Matrix (Fin n) (Fin n) 𝒪[k] → Matrix (Fin n) (Fin n) k) :=
      Matrix.map_injective Subtype.val_injective
    let h : GL (Fin n) 𝒪[k] := ⟨A, B, inj (by rw [map_mul, hA, hB, map_one]; exact g.mul_inv),
      inj (by rw [map_mul, hA, hB, map_one]; exact g.inv_mul)⟩
    have hh : GeneralLinearGroup.map (algebraMap 𝒪[k] k) h = g := Units.ext hA
    refine ⟨h, (GlobalTheory.SmGL.mem_borel _).2 fun i j hij => ?_, hh⟩
    show IsLocalRing.residue 𝒪[k] (A i j) = 0
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
    exact (h3 i j hij).ne

private theorem UpperTheory.Reformulated.B.DoubleCosetSeparation.det_iw {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {g : GL (Fin n) k} (hg : g ∈ GlobalTheory.SmGL.iwahori k (Fin n)) :
    valuation k g.val.det = 1 := by
  obtain ⟨h, -, rfl⟩ := hg
  have h1 : (GeneralLinearGroup.map (algebraMap 𝒪[k] k) h).val.det = algebraMap 𝒪[k] k h.val.det :=
    ((algebraMap 𝒪[k] k).map_det h.val).symm
  rw [h1, ← (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact (GeneralLinearGroup.det h).isUnit

private theorem UpperTheory.Reformulated.B.DoubleCosetSeparation.sep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (ϖ : kˣ) (hϖ : valuation k (ϖ : k) < 1) (x : Fin n → ℤ)
    (hx : StrictAnti x) {a b : GL (Fin n) k} (ha : a ∈ GlobalTheory.SmGL.iwahori k (Fin n))
    (hb : b ∈ GlobalTheory.SmGL.iwahori k (Fin n)) :
    (a * GlobalTheory.SmGL.diagT k (Fin n) (fun i => ϖ ^ x i) * b).val.charpoly.Separable := by
  have hM := mul_mem hb ha
  obtain ⟨h1, -, h3⟩ := (mem_iw _).1 hM
  have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have hs : StrictMono fun i => valuation k ((ϖ ^ x i : kˣ) : k) := by
    intro i j hij
    simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
    exact zpow_lt_zpow_right_of_lt_one₀ h0 hϖ (hx hij)
  rw [Units.val_mul, Units.val_mul, mul_assoc, Matrix.charpoly_mul_comm, mul_assoc, ← Units.val_mul,
    GlobalTheory.SmGL.val_diagT]
  exact UpperTheory.separable_of_newton_polygon (valuation k) n _ hs (fun i => (map_ne_zero _).2 (Units.ne_zero _)) _ (Matrix.charpoly_monic _) (by simp)
    (UpperTheory.charpoly_coeff_valuation (valuation k) n _ _ h1 h3 (det_iw hM) hs fun i => Units.ne_zero _)

private theorem UpperTheory.Reformulated.B.DoubleCosetSeparation.supp {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (I : Subgroup G) (hc : IsCompact (I : Set G)) (t : G) (f : G → ℂ)
    (hf : ∀ y, f y ≠ 0 → ∃ a ∈ I, ∃ b ∈ I, y = a * t * b) : HasCompactSupport f := by
  have hK : IsCompact ((fun p : G × G => p.1 * t * p.2) '' ((I : Set G) ×ˢ (I : Set G))) :=
    (hc.prod hc).image (by fun_prop)
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra h
  obtain ⟨a, ha, b, hb, rfl⟩ := hf y h
  exact hy ⟨(a, b), ⟨ha, hb⟩, rfl⟩

theorem UpperTheory.Reformulated.B.DoubleCosetSeparation.dcosSep :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.DcosSep := by
  intro E _ _ _ n w ϖ hϖ x hx
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  obtain ⟨hop, hc⟩ := UpperTheory.iwahori_subgroup_open (w.adicCompletion E) n
    (GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin n)) fun g => mem_iw g
  have hne : ∀ t y, GlobalTheory.BCT.dcos n w t y ≠ 0 ↔
      ∃ a ∈ GlobalTheory.BCT.iwGL n w, ∃ b ∈ GlobalTheory.BCT.iwGL n w, y = a * t * b := by
    intro t y
    unfold GlobalTheory.BCT.dcos
    split_ifs with h
    · simp [h]
    · simp [h]
  refine ⟨⟨GlobalTheory.BCT.iwGL n w, hop, ?_, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨h, -, rfl⟩
    have hO : ∀ z : 𝒪[w.adicCompletion E], (z : w.adicCompletion E) ∈ Formalism.UG.Ov E w := by
      intro z
      have hz : valuation (w.adicCompletion E) (z : w.adicCompletion E) ≤ 1 := z.2
      have := (Valuation.vle_one_iff (valuation _)).2 hz
      exact (Valuation.vle_one_iff (Valued.v)).1 this
    let φ : 𝒪[w.adicCompletion E] →+* Formalism.UG.Ov E w := (Subring.subtype _).codRestrict _ hO
    show _ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w)
    exact ⟨GeneralLinearGroup.map φ h, Units.ext rfl⟩
  · exact supp (G := GL (Fin n) (w.adicCompletion E)) _ hc (GlobalTheory.BCT.tdiag ϖ x) _ fun y hy => (hne _ y).1 hy
  · intro k hk y
    classical
    unfold GlobalTheory.BCT.dcos
    refine ⟨if_congr ⟨?_, ?_⟩ rfl rfl, if_congr ⟨?_, ?_⟩ rfl rfl⟩
    · rintro ⟨a, ha, b, hb, h⟩
      exact ⟨k⁻¹ * a, mul_mem (inv_mem hk) ha, b, hb, by rw [mul_assoc, mul_assoc, ← mul_assoc a, ← h]; simp⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨k * a, mul_mem hk ha, b, hb, by simp only [mul_assoc]⟩
    · rintro ⟨a, ha, b, hb, h⟩
      exact ⟨a, ha, b * k⁻¹, mul_mem hb (inv_mem hk), by rw [← mul_assoc, ← h]; simp⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b * k, mul_mem hb hk, by simp only [mul_assoc]⟩
  · intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (hne _ y).1 hy
    refine sep ϖ ?_ x hx ha hb
    have h0 : Valued.v (ϖ : w.adicCompletion E) ≠ 0 := by simp
    have h1 : Valued.v (ϖ : w.adicCompletion E) < 1 := by
      unfold Formalism.UG.ordL at hϖ
      rw [dite_eq_right h0] at hϖ
      rw [← WithZero.coe_unzero h0, ← WithZero.coe_one, WithZero.coe_lt_coe, ← Multiplicative.toAdd_lt]
      rw [toAdd_one]
      omega
    exact (Valuation.vlt_one_iff (valuation _)).1 ((Valuation.vlt_one_iff Valued.v).2 h1)
