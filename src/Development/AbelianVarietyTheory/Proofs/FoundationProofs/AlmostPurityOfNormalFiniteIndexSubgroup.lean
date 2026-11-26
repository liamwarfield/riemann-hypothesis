module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerAutomorphismMovesIntegersAlmostUnit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastEqOneOfCoprimeStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedFieldAlmostEtaleOfMovesIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeparatingFamilySumClosedUnderProd
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeparatingFamilySumClosedUnderProd
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory

theorem sepFamily_prod : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (F : Subfield L) (ι : Type) (s : Finset ι) (x y : ι → L), (∀ j ∈ s, x j ∈ F ∧ y j ∈ F ∧ v (x j) ≤ 1 ∧ v (y j) ≤ 1) → ∃ (n : ℕ) (a b : Fin n → L), (∀ i, a i ∈ F ∧ b i ∈ F ∧ v (a i) ≤ 1 ∧ v (b i) ≤ 1) ∧ ∀ σ : G, ∑ i, a i * σ • b i = ∏ j ∈ s, (x j - σ • y j) := by
  intro L _ v G _ _ F ι s x y hs
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, fun _ => 1, fun _ => 1, fun _ => ⟨F.one_mem, F.one_mem, by simp, by simp⟩,
      fun σ => by simp⟩
  | insert j s hj ih =>
    obtain ⟨n, a, b, hab, hsum⟩ := ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))
    obtain ⟨hxF, hyF, hxv, hyv⟩ := hs j (Finset.mem_insert_self j s)
    refine ⟨n + n, Fin.append (fun i => x j * a i) (fun i => - a i),
      Fin.append b (fun i => y j * b i), ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        obtain ⟨h1, h2, h3, h4⟩ := hab i
        exact ⟨F.mul_mem hxF h1, h2, by rw [map_mul]; exact mul_le_one' hxv h3, h4⟩
      · simp only [Fin.append_right]
        obtain ⟨h1, h2, h3, h4⟩ := hab i
        exact ⟨F.neg_mem h1, F.mul_mem hyF h2, by rw [Valuation.map_neg]; exact h3,
          by rw [map_mul]; exact mul_le_one' hyv h4⟩
    · intro σ
      rw [Finset.prod_insert hj, ← hsum σ, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, smul_mul']
      have e1 : ∑ i, x j * a i * σ • b i = x j * ∑ i, a i * σ • b i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      have e2 : ∑ i, -a i * (σ • y j * σ • b i) = -(σ • y j * ∑ i, a i * σ • b i) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [e1, e2]; ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeparatingFamilySumClosedUnderProdStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separating_family_sum_closed_under_prod : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (F : Subfield L) (ι : Type) (s : Finset ι) (x y : ι → L), (∀ j ∈ s, x j ∈ F ∧ y j ∈ F ∧ v (x j) ≤ 1 ∧ v (y j) ≤ 1) → ∃ (n : ℕ) (a b : Fin n → L), (∀ i, a i ∈ F ∧ b i ∈ F ∧ v (a i) ≤ 1 ∧ v (b i) ≤ 1) ∧ ∀ σ : G, ∑ i, a i * σ • b i = ∏ j ∈ s, (x j - σ • y j) := by
  first | exact @GlobalTheory.sepFamily_prod | exact GlobalTheory.sepFamily_prod | (intros; apply GlobalTheory.sepFamily_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedFieldAlmostEtaleOfMovesIntegers
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

open Topology

lemma exists_lt_one_lt_pow (r : ℝ≥0) (hr : r < 1) (k : ℕ) : ∃ t : ℝ≥0, t < 1 ∧ r < t ^ k := by
  have hopen : IsOpen {t : ℝ≥0 | r < t ^ k} := isOpen_lt continuous_const (continuous_pow k)
  have hmem : {t : ℝ≥0 | r < t ^ k} ∈ 𝓝 (1 : ℝ≥0) := hopen.mem_nhds (by simpa using hr)
  obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds hmem ⟨0, zero_lt_one⟩
  obtain ⟨t, hlt, ht1⟩ := exists_between hl
  exact ⟨t, ht1, hsub ⟨hlt, ht1.le⟩⟩

lemma smul_mem_fix {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]
    (N : Subgroup G) [hN : N.Normal] (g : G) {y : L} (hy : y ∈ Fix L N) : g • y ∈ Fix L N := by
  intro n
  have hc : g⁻¹ * (n : G) * g ∈ N := by
    have := hN.conj_mem (n : G) n.2 g⁻¹
    simpa using this
  have h1 : (g⁻¹ * (n : G) * g) • y = y := hy ⟨_, hc⟩
  show (n : G) • g • y = g • y
  calc (n : G) • g • y = g • ((g⁻¹ * (n : G) * g) • y) := by
        simp only [mul_smul, smul_inv_smul]
    _ = g • y := by rw [h1]

lemma fix_smul {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]
    (N : Subgroup G) {y : L} (hy : y ∈ Fix L N) {σ : G} (hσ : σ ∈ N) : σ • y = y :=
  hy ⟨σ, hσ⟩

theorem almostSep_of_moves : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.Normal →
    N.FiniteIndex → (∀ σ : G, σ ∉ N → Moves v (Fix L N) σ) → AlmostSep v N := by
  intro L _ v G _ _ hv N hN hfi hmov r hr
  classical
  haveI : Finite (G ⧸ N) := inferInstance
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  set s : Finset (G ⧸ N) := Finset.univ.erase 1 with hs
  obtain ⟨t, ht1, hrt⟩ := exists_lt_one_lt_pow r hr s.card
  have hex : ∀ q : G ⧸ N, ∃ y : L, y ∈ Fix L N ∧ v y ≤ 1 ∧ (q ≠ 1 → t < v (q.out • y - y)) := by
    intro q
    by_cases hq : q = 1
    · exact ⟨0, zero_mem _, by simp, fun h => absurd hq h⟩
    · have hout : q.out ∉ N := by
        intro hm
        apply hq
        rw [← QuotientGroup.out_eq' q]
        exact (QuotientGroup.eq_one_iff _).2 hm
      obtain ⟨y, hyF, hyv, hyt⟩ := hmov _ hout t ht1
      exact ⟨y, hyF, hyv, fun _ => hyt⟩
  choose y hyF hyv hyt using hex
  let x : G ⧸ N → L := fun q => q.out • y q
  have hxF : ∀ q, x q ∈ Fix L N := fun q => smul_mem_fix N _ (hyF q)
  have hxv : ∀ q, v (x q) ≤ 1 := fun q => by simp only [x, hv]; exact hyv q
  obtain ⟨n, a, b, hab, hsum⟩ := GlobalTheory.T.separating_family_sum_closed_under_prod L v G (Fix L N) (G ⧸ N) s x y
    (fun j _ => ⟨hxF j, hyF j, hxv j, hyv j⟩)
  refine ⟨n, a, b, ∏ q ∈ s, (x q - y q), ?_, ?_⟩
  · refine
      { a_mem := fun i => (hab i).1
        b_mem := fun i => (hab i).2.1
        c_mem := ?_
        a_le := fun i => (hab i).2.2.1
        b_le := fun i => (hab i).2.2.2
        c_le := ?_
        sum_in := ?_
        sum_out := ?_ }
    · exact prod_mem fun q _ => sub_mem (hxF q) (hyF q)
    · rw [map_prod]
      refine Finset.prod_le_one₀ (fun _ _ => zero_le) fun q _ => ?_
      exact (Valuation.map_sub v _ _).trans (max_le (hxv q) (hyv q))
    · intro σ hσ
      rw [hsum σ]
      refine Finset.prod_congr rfl fun q _ => ?_
      rw [fix_smul N (hyF q) hσ]
    · intro σ hσ
      rw [hsum σ]
      have hq : (σ : G ⧸ N) ∈ s := by
        rw [hs, Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        intro h
        exact hσ ((QuotientGroup.eq_one_iff σ).1 h)
      refine Finset.prod_eq_zero hq ?_
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul N σ
      simp only [x]
      rw [hm, mul_smul, fix_smul N (hyF _) m.2, sub_self]
  · rw [map_prod]
    calc r < t ^ s.card := hrt
      _ = ∏ _q ∈ s, t := by rw [Finset.prod_const]
      _ ≤ ∏ q ∈ s, v (x q - y q) := by
        refine Finset.prod_le_prod₀ (fun _ _ => zero_le) fun q hq => ?_
        exact (hyt q (Finset.ne_of_mem_erase hq)).le

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedFieldAlmostEtaleOfMovesIntegersStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedFieldAlmostEtale_of_moves_integers : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.Normal → N.FiniteIndex → (∀ σ : G, σ ∉ N → Moves v (Fix L N) σ) → AlmostSep v N := by
  first | exact @GlobalTheory.AlmostEt.almostSep_of_moves | exact GlobalTheory.AlmostEt.almostSep_of_moves | (intros; apply GlobalTheory.AlmostEt.almostSep_of_moves <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostPurityMovesIntegersOfNeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootFixedSubfieldOfAlmostEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulApproxPowOfAlmostEtaleSeparatingFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationFrobeniusSumSubLeNatCastPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationFrobeniusSumSubLeNatCastPrime
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem frob_sum_sub_le (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ) (hp : p.Prime)
    (ι : Type) (s : Finset ι) (x : ι → L) (hx : ∀ i ∈ s, v (x i) ≤ 1) :
    v ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) ≤ v (p : L) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [zero_pow hp.ne_zero]
  | insert a s ha ih =>
    have hxa : v (x a) ≤ 1 := hx a (Finset.mem_insert_self a s)
    have hxs : ∀ i ∈ s, v (x i) ≤ 1 := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hS : v (∑ i ∈ s, x i) ≤ 1 := by
      have : (∑ i ∈ s, x i) ∈ v.integer :=
        Subring.sum_mem _ (fun i hi => (Valuation.mem_integer_iff v _).2 (hxs i hi))
      exact (Valuation.mem_integer_iff v _).1 this
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp
      (⟨x a, (Valuation.mem_integer_iff v _).2 hxa⟩ : v.integer)
      ⟨∑ i ∈ s, x i, (Valuation.mem_integer_iff v _).2 hS⟩
    have hr' : (x a + ∑ i ∈ s, x i) ^ p = x a ^ p + (∑ i ∈ s, x i) ^ p + (p : L) * (x a * (∑ i ∈ s, x i) * (r : L)) := by
      have := congrArg (fun z : v.integer => (z : L)) hr
      push_cast at this
      rw [this]; ring
    have hrle : v (x a * (∑ i ∈ s, x i) * (r : L)) ≤ 1 := by
      rw [Valuation.map_mul, Valuation.map_mul]
      have hr1 : v (r : L) ≤ 1 := (Valuation.mem_integer_iff v _).1 r.2
      calc v (x a) * v (∑ i ∈ s, x i) * v (r : L) ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by simp
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hr']
    have heq : x a ^ p + (∑ i ∈ s, x i) ^ p + (p : L) * (x a * (∑ i ∈ s, x i) * (r : L)) - (x a ^ p + ∑ i ∈ s, x i ^ p)
        = (p : L) * (x a * (∑ i ∈ s, x i) * (r : L)) + ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) := by ring
    rw [heq]
    refine (Valuation.map_add v _ _).trans (max_le ?_ (ih hxs))
    rw [Valuation.map_mul]
    calc v (p : L) * v (x a * (∑ i ∈ s, x i) * (r : L)) ≤ v (p : L) * 1 := by gcongr
      _ = v (p : L) := mul_one _

theorem frob_sum_sub_le' : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ (ι : Type) (s : Finset ι) (x : ι → L), (∀ i ∈ s, v (x i) ≤ 1) →
      v ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) ≤ v (p : L) :=
  fun L _ v p hp ι s x hx => frob_sum_sub_le L v p hp ι s x hx

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationFrobeniusSumSubLeNatCastPrimeStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_frobenius_sum_sub_le_natCast_prime : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ (ι : Type) (s : Finset ι) (x : ι → L), (∀ i ∈ s, v (x i) ≤ 1) → v ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) ≤ v (p : L) := by
  first | exact @GlobalTheory.AlmostEt.frob_sum_sub_le' | exact GlobalTheory.AlmostEt.frob_sum_sub_le' | (intros; apply GlobalTheory.AlmostEt.frob_sum_sub_le' <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulApproxPowOfAlmostEtaleSeparatingFamily
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem cpow_mul_approx_pow_of_isSep :
    ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)] (θ : ℝ≥0), θ ≤ 1 → (∀ u ∈ Fix L (⊤ : Subgroup G), ∃ w ∈ Fix L (⊤ : Subgroup G), v (u - w ^ p) ≤ θ * v u) → ∀ (n : ℕ) (a b : Fin n → L) (c : L), IsSep v N a b c → ∀ x ∈ Fix L N, v x ≤ 1 → ∃ w ∈ Fix L N, v (c ^ p * x - w ^ p) ≤ max θ (v (p : L)) := by
  intro L _ v p hp G _ _ hv N _ θ hθ hroot n a b c hs x hx hx1
  have frob := GlobalTheory.T.valuation_frobenius_sum_sub_le_natCast_prime L v p hp
  have trfix := GlobalTheory.T.cosetRepresentativeTrace_fixed_properties L v G hv N
  have memN : ∀ y : L, y ∈ Fix L N ↔ ∀ g ∈ N, g • y = y := by
    intro y
    constructor
    · intro h g hg; exact h ⟨g, hg⟩
    · intro h g; exact h g g.2
  have memTop : ∀ y : L, y ∈ Fix L (⊤ : Subgroup G) ↔ ∀ g : G, g • y = y := by
    intro y
    constructor
    · intro h g; exact h ⟨g, Subgroup.mem_top g⟩
    · intro h g; exact h g
  set q₀ : G ⧸ N := ((1 : G) : G ⧸ N) with hq₀
  have hout : ∀ q : G ⧸ N, q.out ∈ N ↔ q = q₀ := fun q => by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [hq₀, QuotientGroup.eq, mul_one, inv_mem_iff]
  set T : Fin n → L := fun i => cosetTrace N (b i ^ p * x) with hTdef
  have hbx : ∀ i, b i ^ p * x ∈ Fix L N := fun i =>
    Subfield.mul_mem _ (Subfield.pow_mem _ (hs.b_mem i) p) hx
  have hT : ∀ i, (∀ g : G, g • T i = T i) ∧ v (T i) ≤ 1 := fun i => by
    obtain ⟨h1, h2, -⟩ := trfix _ (hbx i)
    refine ⟨h1, h2 ?_⟩
    rw [map_mul, map_pow]
    exact mul_le_one' (pow_le_one' (hs.b_le i) p) hx1
  choose w hwmem hwle using fun i => hroot (T i) ((memTop _).2 (hT i).1)
  have hwθ : ∀ i, v (T i - w i ^ p) ≤ θ := fun i =>
    le_trans (hwle i) (mul_le_of_le_one_right zero_le' (hT i).2)
  have hw1 : ∀ i, v (w i) ≤ 1 := fun i => by
    have : v (w i ^ p) ≤ 1 := by
      have e : w i ^ p = T i - (T i - w i ^ p) := by ring
      rw [e]
      exact Valuation.map_sub_le v (hT i).2 (le_trans (hwθ i) hθ)
    rw [map_pow] at this
    exact (pow_le_one_iff_of_nonneg zero_le' hp.ne_zero).1 this
  set W : L := ∑ i, a i * w i with hWdef
  have hWmem : W ∈ Fix L N := by
    refine Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (hs.a_mem i) ?_
    exact (memN _).2 fun g _ => (memTop _).1 (hwmem i) g
  refine ⟨W, hWmem, ?_⟩

  have key1 : ∑ i, a i ^ p * T i = ∑ q : G ⧸ N, (∑ i, (a i * q.out • b i) ^ p) * q.out • x := by
    simp only [hTdef, cosetTrace, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul', smul_pow', mul_pow]
    ring
  have key2 : c ^ p * x = ∑ q : G ⧸ N, (∑ i, a i * q.out • b i) ^ p * q.out • x := by
    rw [Finset.sum_eq_single q₀]
    · rw [hs.sum_in _ ((hout q₀).2 rfl), (memN x).1 hx _ ((hout q₀).2 rfl)]
    · intro q _ hq
      rw [hs.sum_out _ (fun h => hq ((hout q).1 h)), zero_pow hp.ne_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have bound1 : v (c ^ p * x - ∑ i, a i ^ p * T i) ≤ v (p : L) := by
    rw [key1, key2, ← Finset.sum_sub_distrib]
    apply Valuation.map_sum_le
    intro q _
    rw [← sub_mul, map_mul]
    have h1 : v (q.out • x) ≤ 1 := by rw [hv]; exact hx1
    have h2 := frob (Fin n) Finset.univ (fun i => a i * q.out • b i)
      (fun i _ => by rw [map_mul, hv]; exact mul_le_one' (hs.a_le i) (hs.b_le i))
    calc _ ≤ v (p : L) * 1 := mul_le_mul' h2 h1
      _ = _ := mul_one _
  have bound2 : v (∑ i, a i ^ p * T i - ∑ i, a i ^ p * w i ^ p) ≤ θ := by
    rw [← Finset.sum_sub_distrib]
    apply Valuation.map_sum_le
    intro i _
    rw [← mul_sub, map_mul]
    calc _ ≤ 1 * θ := mul_le_mul' (by rw [map_pow]; exact pow_le_one' (hs.a_le i) p) (hwθ i)
      _ = θ := one_mul θ
  have bound3 : v (∑ i, a i ^ p * w i ^ p - W ^ p) ≤ v (p : L) := by
    have h := frob (Fin n) Finset.univ (fun i => a i * w i)
      (fun i _ => by rw [map_mul]; exact mul_le_one' (hs.a_le i) (hw1 i))
    simp only [mul_pow] at h
    rw [Valuation.map_sub_swap]
    exact h
  have e : c ^ p * x - W ^ p = (c ^ p * x - ∑ i, a i ^ p * T i)
      + (∑ i, a i ^ p * T i - ∑ i, a i ^ p * w i ^ p) + (∑ i, a i ^ p * w i ^ p - W ^ p) := by ring
  rw [e]
  refine Valuation.map_add_le v (Valuation.map_add_le v ?_ ?_) ?_
  · exact le_trans bound1 (le_max_right _ _)
  · exact le_trans bound2 (le_max_left _ _)
  · exact le_trans bound3 (le_max_right _ _)

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulApproxPowOfAlmostEtaleSeparatingFamilyStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_mul_approx_pow_of_almostEtaleSeparatingFamily : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)] (θ : ℝ≥0), θ ≤ 1 → (∀ u ∈ Fix L (⊤ : Subgroup G), ∃ w ∈ Fix L (⊤ : Subgroup G), v (u - w ^ p) ≤ θ * v u) → ∀ (n : ℕ) (a b : Fin n → L) (c : L), IsSep v N a b c → ∀ x ∈ Fix L N, v x ≤ 1 → ∃ w ∈ Fix L N, v (c ^ p * x - w ^ p) ≤ max θ (v (p : L)) := by
  first | exact @GlobalTheory.AlmostEt.cpow_mul_approx_pow_of_isSep | exact GlobalTheory.AlmostEt.cpow_mul_approx_pow_of_isSep | (intros; apply GlobalTheory.AlmostEt.cpow_mul_approx_pow_of_isSep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootFixedSubfieldOfAlmostEtale
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem approxRoot_fix_of_almostSep : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ),
    p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L],
    (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.FiniteIndex → AlmostSep v N →
    ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ApproxRoot p v (Fix L N) := by
  intro L _ v p hp hp0 hp1 G _ _ hinv N hN hsep hroot
  haveI : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  obtain ⟨θ, hθ1, hθ⟩ := hroot
  set θ₀ : ℝ≥0 := max θ (v (p : L)) with hθ₀
  have hθ₀1 : θ₀ < 1 := max_lt hθ1 hp1
  obtain ⟨s, hs0, hs1⟩ := exists_between hθ₀1
  set r : ℝ≥0 := s ^ (((p + 1 : ℕ) : ℝ)⁻¹) with hr
  have hrpow : r ^ (p + 1) = s := NNReal.rpow_inv_natCast_pow s (by omega)
  have hr1 : r < 1 := NNReal.rpow_lt_one hs1 (by positivity)
  have hrs : θ₀ < r ^ (p + 1) := hrpow ▸ hs0
  have hrpos : 0 < r ^ (p + 1) := lt_of_le_of_lt bot_le hrs
  obtain ⟨n, a, b, c, hc, hrc⟩ := hsep r hr1
  refine ⟨θ₀ / r ^ (p + 1), (div_lt_one hrpos).2 hrs, ?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · refine ⟨0, zero_mem _, ?_⟩
    simp [hx0, hp.ne_zero]
  obtain ⟨d, hdF, hd0, hdr, hd1⟩ :=
    GlobalTheory.T.exists_pth_power_scale_thin_shell L v p hp _ ⟨θ, hθ1, hθ⟩ hp0 hp1 r hr1 x hx0
  have hdN : d ∈ Fix L N := fun σ => hdF ⟨σ.1, Subgroup.mem_top _⟩
  have hx'N : x * d ^ p ∈ Fix L N := mul_mem hx (pow_mem hdN p)
  obtain ⟨w, hwN, hw⟩ :=
    GlobalTheory.T.pow_mul_approx_pow_of_almostEtaleSeparatingFamily L v p hp G hinv N θ hθ1.le hθ n a b c hc (x * d ^ p) hx'N hd1
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hrc
    exact (not_lt.2 (bot_le : (⊥ : ℝ≥0) ≤ r)) hrc
  refine ⟨w / (c * d), div_mem hwN (mul_mem hc.c_mem hdN), ?_⟩
  have key : x - (w / (c * d)) ^ p = (c ^ p * (x * d ^ p) - w ^ p) / (c ^ p * d ^ p) := by
    have hD0 : c ^ p * d ^ p ≠ 0 := mul_ne_zero (pow_ne_zero _ hc0) (pow_ne_zero _ hd0)
    rw [eq_div_iff hD0, div_pow, mul_pow, sub_mul, div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero _ hc0) (pow_ne_zero _ hd0))]
    ring
  have hD : 0 < v (c ^ p * d ^ p) := by
    rw [Valuation.pos_iff]
    exact mul_ne_zero (pow_ne_zero _ hc0) (pow_ne_zero _ hd0)
  rw [key, map_div₀, div_le_iff₀ hD]
  have hvx : v (x * d ^ p) = v x * v d ^ p := by rw [map_mul, map_pow]
  have hbig : r ^ (p + 1) ≤ v c ^ p * (v x * v d ^ p) := by
    rw [pow_succ, ← hvx]
    exact mul_le_mul' (pow_le_pow_left₀ bot_le hrc.le p) hdr.le
  calc v (c ^ p * (x * d ^ p) - w ^ p) ≤ θ₀ := hw
    _ = θ₀ / r ^ (p + 1) * r ^ (p + 1) := (div_mul_cancel₀ _ hrpos.ne').symm
    _ ≤ θ₀ / r ^ (p + 1) * (v c ^ p * (v x * v d ^ p)) := by gcongr
    _ = θ₀ / r ^ (p + 1) * v x * v (c ^ p * d ^ p) := by
      rw [map_mul, map_pow, map_pow]; ring

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootFixedSubfieldOfAlmostEtaleStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approxPthRoot_fixedSubfield_of_almostEtale : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.FiniteIndex → AlmostSep v N → ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ApproxRoot p v (Fix L N) := by
  first | exact @GlobalTheory.AlmostEt.approxRoot_fix_of_almostSep | exact GlobalTheory.AlmostEt.approxRoot_fix_of_almostSep | (intros; apply GlobalTheory.AlmostEt.approxRoot_fix_of_almostSep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitOfCoprimeOrder
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitOfCoprimeOrder
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem moves_top_of_coprime_order : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 →
    ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) →
    ∀ σ : G, (∀ x ∈ F, σ • x = x) → ∀ l : ℕ, Nat.Coprime l p → σ ^ l = 1 →
    (∃ y : L, σ • y ≠ y) → Moves v ⊤ σ := by
  intro L _ v p hp F hF hp0 hp1 G _ _ hv σ hσF l hl hσl ⟨y, hy⟩ r hr
  obtain ⟨d, hdF, _hd0, hrx, hx1⟩ :=
    GlobalTheory.T.exists_pth_power_scale_thin_shell L v p hp F hF hp0 hp1 r hr (σ • y - y) (sub_ne_zero.mpr hy)
  set x := (σ • y - y) * d ^ p with hxdef
  refine ⟨x, Subfield.mem_top x, hx1, ?_⟩
  by_contra hle
  push_neg at hle
  have hfix : ∀ j : ℕ, (σ ^ j) • d = d := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, mul_smul, hσF d hdF, ih]
  have hterm : ∀ j : ℕ, (σ ^ j) • x = ((σ ^ (j + 1)) • y - (σ ^ j) • y) * d ^ p := by
    intro j
    rw [hxdef, smul_mul', smul_pow', hfix, smul_sub, pow_succ, mul_smul]
  have hsum : ∑ j ∈ Finset.range l, (σ ^ j) • x = 0 := by
    simp_rw [hterm]
    rw [← Finset.sum_mul, Finset.sum_range_sub (fun j => (σ ^ j) • y), hσl, one_smul, pow_zero,
      one_smul, sub_self, zero_mul]
  have hstep : ∀ j : ℕ, v ((σ ^ j) • x - x) ≤ r := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (σ ^ (j + 1)) • x - x = σ • ((σ ^ j) • x - x) + (σ • x - x) := by
        rw [smul_sub, pow_succ', mul_smul]; ring
      rw [e]
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ hle)
      rw [hv]; exact ih
  have hlx : (l : L) * x = ∑ j ∈ Finset.range l, (x - (σ ^ j) • x) := by
    rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1 : v ((l : L) * x) ≤ r := by
    rw [hlx]
    apply Valuation.map_sum_le
    intro j _
    rw [← Valuation.map_neg, neg_sub]
    exact hstep j
  rw [map_mul, GlobalTheory.T.valuation_natCast_eq_one_of_coprime' L v p l hp1 hl, one_mul] at h1
  exact absurd (lt_of_lt_of_le hrx h1) (lt_irrefl _)

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitOfCoprimeOrderStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movesIntegersAlmostUnit_of_coprime_order : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ σ : G, (∀ x ∈ F, σ • x = x) → ∀ l : ℕ, Nat.Coprime l p → σ ^ l = 1 → (∃ y : L, σ • y ≠ y) → Moves v ⊤ σ := by
  first | exact @GlobalTheory.AlmostEt.moves_top_of_coprime_order | exact GlobalTheory.AlmostEt.moves_top_of_coprime_order | (intros; apply GlobalTheory.AlmostEt.moves_top_of_coprime_order <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLagrangeResolventOfPGroupFaithful
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSurjHomZmodOfIsPGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSurjHomZmodOfIsPGroup
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_surj_hom_zmod_of_isPGroup :
    ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] [Nontrivial G],
      IsPGroup p G → ∃ χ : G →* Multiplicative (ZMod p), Function.Surjective χ := by
  intro p hp G _ _ _ hG
  obtain ⟨n, hn, hc⟩ := hG.nontrivial_iff_card.1 inferInstance
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) p (n := m)
    (by rw [hc]; exact pow_dvd_pow p (Nat.le_succ m))
  have hi : K.index = p := by
    have := K.card_mul_index
    rw [hK, hc, pow_succ] at this
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos m) this
  haveI : K.Normal := Subgroup.normal_of_index_eq_minFac_card (by
    rw [hi, hc, hp.out.pow_minFac (Nat.succ_ne_zero m)])
  let e : (G ⧸ K) ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq (p := p) (by rw [← hi]; rfl) (by simp)
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' K), ?_⟩
  exact e.surjective.comp (QuotientGroup.mk'_surjective K)

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSurjHomZmodOfIsPGroupStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_surjective_hom_zmod_of_isPGroup : ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] [Nontrivial G], IsPGroup p G → ∃ χ : G →* Multiplicative (ZMod p), Function.Surjective χ := by
  first | exact @GlobalTheory.AlmostEt.exists_surj_hom_zmod_of_isPGroup | exact GlobalTheory.AlmostEt.exists_surj_hom_zmod_of_isPGroup | (intros; apply GlobalTheory.AlmostEt.exists_surj_hom_zmod_of_isPGroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLagrangeResolventOfPGroupFaithful
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_lagrange_resolvent : ∀ (L : Type) [Field L] (p : ℕ), p.Prime → ∀ (G : Type) [Group G]
    [MulSemiringAction G L] [Finite G] [Nontrivial G] [FaithfulSMul G L], IsPGroup p G →
    ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) →
    ∃ (σ : G) (α : L), α ≠ 0 ∧ σ • α = ζ * α ∧ ∀ g : G, g • α ^ p = α ^ p := by
  intro L _ p hp G _ _ _ _ _ hG ζ hζ hfix
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  classical
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_surjective_hom_zmod_of_isPGroup p G hG
  set ψ : G → L := fun g => ζ ^ (Multiplicative.toAdd (χ g)).val with hψdef
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hmod : ∀ n : ℕ, ζ ^ n = ζ ^ (n % p) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n p, pow_add, pow_mul, hζp, one_pow, one_mul]
  have hψmul : ∀ a b, ψ (a * b) = ψ a * ψ b := by
    intro a b
    simp only [hψdef, map_mul, toAdd_mul, ZMod.val_add, ← pow_add]
    exact (hmod _).symm
  have hψp : ∀ g, ψ g ^ p = 1 := by
    intro g; simp only [hψdef]; rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow]
  have hψne : ∀ g, ψ g ≠ 0 := fun g h => by
    have := hψp g; rw [h, zero_pow hp.ne_zero] at this; exact zero_ne_one this
  have hψfix : ∀ g h : G, g • ψ h = ψ h := fun g h => by simp only [hψdef, smul_pow', hfix]
  let f : G → (L →* L) := fun g => (MulSemiringAction.toRingHom G L g : L →* L)
  have hf : Function.Injective f := by
    intro g h hgh
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro x
    exact DFunLike.congr_fun hgh x
  have hli : LinearIndependent L (fun g : G => ((f g : L →* L) : L → L)) :=
    (linearIndependent_monoidHom L L).comp f hf
  have hex : ∃ x : L, ∑ g : G, ψ g⁻¹ * (g • x) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : ∑ g : G, ψ g⁻¹ • ((f g : L →* L) : L → L) = 0 := by
      funext x
      simpa [f, Finset.sum_apply] using hcon x
    exact hψne _ ((Fintype.linearIndependent_iff.mp hli) (fun g => ψ g⁻¹) h0 1)
  obtain ⟨x, hx⟩ := hex
  set α := ∑ g : G, ψ g⁻¹ * (g • x) with hα
  have hact : ∀ h : G, h • α = ψ h * α := by
    intro h
    rw [hα, Finset.smul_sum, Finset.mul_sum]
    simp only [smul_mul', hψfix, smul_smul]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => ?_)
    simp only [Equiv.coe_mulLeft]
    have e : ψ h * ψ h⁻¹ = 1 := by
      rw [← hψmul, mul_inv_cancel]; simp [hψdef]
    rw [mul_inv_rev, hψmul g⁻¹ h⁻¹]
    linear_combination (-(ψ g⁻¹ * ((h * g) • x))) * e
  obtain ⟨σ, hσ⟩ := hχ (Multiplicative.ofAdd 1)
  refine ⟨σ, α, hx, ?_, ?_⟩
  · rw [hact σ]
    congr 1
    simp [hψdef, hσ, ZMod.val_one]
  · intro g
    rw [smul_pow', hact g, mul_pow, hψp, one_mul]

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLagrangeResolventOfPGroupFaithfulStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lagrange_resolvent_of_pGroup_faithful : ∀ (L : Type) [Field L] (p : ℕ), p.Prime → ∀ (G : Type) [Group G] [MulSemiringAction G L] [Finite G] [Nontrivial G] [FaithfulSMul G L], IsPGroup p G → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) → ∃ (σ : G) (α : L), α ≠ 0 ∧ σ • α = ζ * α ∧ ∀ g : G, g • α ^ p = α ^ p := by
  first | exact @GlobalTheory.AlmostEt.exists_lagrange_resolvent | exact GlobalTheory.AlmostEt.exists_lagrange_resolvent | (intros; apply GlobalTheory.AlmostEt.exists_lagrange_resolvent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormalSubgroupNotMovesUniformBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormalSubgroupNotMovesUniformBound
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

variable {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]

theorem not_moves_top_iff (v : Valuation L ℝ≥0) (σ : G) :
    ¬ Moves v ⊤ σ ↔ ∃ r : ℝ≥0, r < 1 ∧ ∀ x : L, v x ≤ 1 → v (σ • x - x) ≤ r := by
  unfold Moves
  push_neg
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun x hx => h x (Subfield.mem_top x) hx⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun x _ hx => h x hx⟩

def smallSubgroup (v : Valuation L ℝ≥0) (hv : ∀ (g : G) (x : L), v (g • x) = v x) : Subgroup G where
  carrier := {σ | ¬ Moves v ⊤ σ}
  one_mem' := by
    show ¬ Moves v ⊤ (1 : G)
    rw [not_moves_top_iff]
    exact ⟨0, zero_lt_one, fun x _ => by simp⟩
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [Set.mem_setOf_eq, not_moves_top_iff] at hσ hτ ⊢
    obtain ⟨r, hr, h1⟩ := hσ
    obtain ⟨s, hs, h2⟩ := hτ
    refine ⟨max r s, max_lt hr hs, fun x hx => ?_⟩
    have hτx : v (τ • x) ≤ 1 := by rw [hv]; exact hx
    have e : (σ * τ) • x - x = (σ • (τ • x) - τ • x) + (τ • x - x) := by
      rw [mul_smul]; ring
    rw [e]
    exact (v.map_add _ _).trans (max_le_max (h1 _ hτx) (h2 _ hx))
  inv_mem' := by
    intro σ hσ
    simp only [Set.mem_setOf_eq, not_moves_top_iff] at hσ ⊢
    obtain ⟨r, hr, h1⟩ := hσ
    refine ⟨r, hr, fun x hx => ?_⟩
    have hy : v (σ⁻¹ • x) ≤ 1 := by rw [hv]; exact hx
    have e : σ⁻¹ • x - x = -(σ • (σ⁻¹ • x) - σ⁻¹ • x) := by
      rw [smul_inv_smul]; ring
    rw [e, Valuation.map_neg]
    exact h1 _ hy

theorem smallSubgroup_normal (v : Valuation L ℝ≥0) (hv : ∀ (g : G) (x : L), v (g • x) = v x) :
    (smallSubgroup v hv).Normal := by
  constructor
  intro σ hσ g
  change ¬ Moves v ⊤ σ at hσ
  change ¬ Moves v ⊤ (g * σ * g⁻¹)
  rw [not_moves_top_iff] at hσ ⊢
  obtain ⟨r, hr, h1⟩ := hσ
  refine ⟨r, hr, fun x hx => ?_⟩
  have hy : v (g⁻¹ • x) ≤ 1 := by rw [hv]; exact hx
  have e : (g * σ * g⁻¹) • x - x = g • (σ • (g⁻¹ • x) - g⁻¹ • x) := by
    rw [smul_sub, mul_smul, mul_smul, smul_inv_smul]
  rw [e, hv]
  exact h1 _ hy

theorem exists_normal_not_moves_uniform :
    ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L]
      [Finite G], (∀ (g : G) (x : L), v (g • x) = v x) →
      ∃ N : Subgroup G, N.Normal ∧ (∀ σ : G, σ ∈ N ↔ ¬ Moves v ⊤ σ) ∧
        ∃ i : ℝ≥0, i < 1 ∧ ∀ τ ∈ N, ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ i := by
  intro L _ v G _ _ _ hv
  refine ⟨smallSubgroup v hv, smallSubgroup_normal v hv, fun σ => Iff.rfl, ?_⟩
  have hc : ∀ τ : G, ∃ r : ℝ≥0, r < 1 ∧
      (¬ Moves v ⊤ τ → ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ r) := by
    intro τ
    by_cases h : Moves v ⊤ τ
    · exact ⟨0, zero_lt_one, fun h' => absurd h h'⟩
    · obtain ⟨r, hr, h1⟩ := (not_moves_top_iff v τ).1 h
      exact ⟨r, hr, fun _ => h1⟩
  choose f hf1 hf2 using hc
  letI := Fintype.ofFinite G
  refine ⟨Finset.univ.sup f, ?_, ?_⟩
  · rw [Finset.sup_lt_iff zero_lt_one]
    exact fun τ _ => hf1 τ
  · intro τ hτ x hx
    exact (hf2 τ hτ x hx).trans (Finset.le_sup (f := f) (Finset.mem_univ τ))

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormalSubgroupNotMovesUniformBoundStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_subgroup_not_moves_uniform_bound : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] [Finite G], (∀ (g : G) (x : L), v (g • x) = v x) → ∃ N : Subgroup G, N.Normal ∧ (∀ σ : G, σ ∈ N ↔ ¬ Moves v ⊤ σ) ∧ ∃ i : ℝ≥0, i < 1 ∧ ∀ τ ∈ N, ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ i := by
  first | exact @GlobalTheory.AlmostEt.exists_normal_not_moves_uniform | exact GlobalTheory.AlmostEt.exists_normal_not_moves_uniform | (intros; apply GlobalTheory.AlmostEt.exists_normal_not_moves_uniform <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitDistanceFixedSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitDistanceFixedSubfield
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

open Polynomial

theorem moves_fix_of_moves : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L] [Finite G], (∀ (g : G) (x : L), v (g • x) = v x) →
    ∀ (N : Subgroup G) (i : ℝ≥0), i < 1 → (∀ τ ∈ N, ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ i) →
    ∀ σ : G, Moves v ⊤ σ → Moves v (Fix L N) σ := by
  intro L _ v G _ _ _ hinv N i hi hN σ hσ r hr
  classical
  by_contra hcon
  push_neg at hcon
  haveI := Fintype.ofFinite G
  set n := Fintype.card N with hn_def
  have hn : n ≠ 0 := Fintype.card_ne_zero
  set t : ℝ≥0 := max i (r ^ ((n : ℝ)⁻¹)) with ht_def
  have ht1 : t < 1 := max_lt hi (NNReal.rpow_lt_one hr (by positivity))
  have hrt : r ≤ t ^ n := by
    calc r = (r ^ ((n : ℝ)⁻¹)) ^ n := (NNReal.rpow_inv_natCast_pow r hn).symm
      _ ≤ t ^ n := pow_le_pow_left₀ zero_le (le_max_right _ _) n
  obtain ⟨x, -, hx1, hxt⟩ := hσ t ht1

  have hfac : ∀ τ : N, v (x - σ • ((τ : G) • x)) = v (σ • x - x) := by
    intro τ
    have h1 : v (σ • x - σ • ((τ : G) • x)) < v (x - σ • x) := by
      rw [← smul_sub, hinv, Valuation.map_sub_swap, Valuation.map_sub_swap v x]
      exact lt_of_le_of_lt (le_trans (hN τ τ.2 x hx1) (le_max_left _ _)) hxt
    have h2 : x - σ • ((τ : G) • x) = (x - σ • x) + (σ • x - σ • ((τ : G) • x)) := by ring
    rw [h2, Valuation.map_add_eq_of_lt_left v h1, Valuation.map_sub_swap]

  set P : L[X] := ∏ τ : N, (X - C ((τ : G) • x)) with hP_def
  have hint : ∀ τ : N, (τ : G) • x ∈ v.integer := fun τ => by
    rw [Valuation.mem_integer_iff, hinv]; exact hx1
  set Q : (v.integer)[X] := ∏ τ : N, (X - C (⟨(τ : G) • x, hint τ⟩ : v.integer)) with hQ_def
  have hPQ : P = Q.map (v.integer.subtype) := by
    simp [hP_def, hQ_def, Polynomial.map_prod]
  have hcint : ∀ k, v (P.coeff k) ≤ 1 := by
    intro k
    rw [hPQ, coeff_map]
    exact (Q.coeff k).2
  have hcfix : ∀ k, P.coeff k ∈ Fix L N := by
    intro k m
    have hmap : P.map (MulSemiringAction.toRingHom G L (m : G)) = P := by
      rw [hP_def, Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C, MulSemiringAction.toRingHom_apply, smul_smul]
      exact Fintype.prod_equiv (Equiv.mulLeft m) _ _ (fun τ => by simp)
    have := congrArg (fun p => p.coeff k) hmap
    have h' : (m : G) • P.coeff k = P.coeff k := by simpa [coeff_map] using this
    exact h'
  have hPx : P.eval x = 0 := by
    rw [hP_def, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)
  have hPσx : (P.map (MulSemiringAction.toRingHom G L σ)).eval x = ∏ τ : N, (x - σ • ((τ : G) • x)) := by
    simp [hP_def, Polynomial.map_prod, eval_prod]

  have hdiff : v ((P.map (MulSemiringAction.toRingHom G L σ) - P).eval x) ≤ r := by
    rw [eval_eq_sum, Polynomial.sum_def]
    apply Valuation.map_sum_le
    intro k _
    rw [map_mul, map_pow, coeff_sub, coeff_map, MulSemiringAction.toRingHom_apply]
    calc v (σ • P.coeff k - P.coeff k) * v x ^ k ≤ r * 1 :=
          mul_le_mul' (hcon _ (hcfix k) (hcint k)) (pow_le_one₀ zero_le hx1)
      _ = r := mul_one r
  rw [eval_sub, hPx, sub_zero, hPσx, map_prod] at hdiff
  simp only [hfac, Finset.prod_const, Finset.card_univ] at hdiff
  have := pow_lt_pow_left₀ hxt zero_le hn
  exact absurd (lt_of_le_of_lt (hdiff.trans hrt) this) (lt_irrefl _)

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitDistanceFixedSubfieldStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movesIntegersAlmostUnitDistance_fixedSubfield : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] [Finite G], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) (i : ℝ≥0), i < 1 → (∀ τ ∈ N, ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ i) → ∀ σ : G, Moves v ⊤ σ → Moves v (Fix L N) σ := by
  first | exact @GlobalTheory.AlmostEt.moves_fix_of_moves | exact GlobalTheory.AlmostEt.moves_fix_of_moves | (intros; apply GlobalTheory.AlmostEt.moves_fix_of_moves <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostPurityMovesIntegersOfNeOne
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem moves_of_ne_one : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L] [Finite G] [FaithfulSMul G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) → ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ∀ σ : G, σ ≠ 1 → Moves v ⊤ σ := by
  intro L _ v p hp hp0 hp1 G _ _ _ _ hinv ζ hζ hζfix hroot σ hσ
  obtain ⟨N, hNn, hNmem, i, hi, hNi⟩ := GlobalTheory.T.exists_normal_subgroup_not_moves_uniform_bound L v G hinv
  by_contra hmov
  have hσN : σ ∈ N := (hNmem σ).2 hmov
  have hfixN : ∀ τ ∈ N, ∀ x ∈ Fix L N, τ • x = x := fun τ hτ x hx => hx ⟨τ, hτ⟩
  have hdesc : ∀ τ : G, τ ∉ N → Moves v (Fix L N) τ := fun τ hτ =>
    GlobalTheory.T.movesIntegersAlmostUnitDistance_fixedSubfield L v G hinv N i hi hNi τ (by_contra fun h => hτ ((hNmem τ).2 h))
  have hsep : AlmostSep v N := GlobalTheory.T.fixedFieldAlmostEtale_of_moves_integers L v G hinv N hNn inferInstance hdesc
  have hF : ApproxRoot p v (Fix L N) := GlobalTheory.T.approxPthRoot_fixedSubfield_of_almostEtale L v p hp hp0 hp1 G hinv N inferInstance hsep hroot
  have hpg : IsPGroup p N := by
    intro τ
    set n := orderOf (τ : G) with hn
    have hn0 : n ≠ 0 := (orderOf_pos (τ : G)).ne'
    set k := n.factorization p
    refine ⟨k, ?_⟩
    have hcop : Nat.Coprime (n / p ^ k) p := (Nat.coprime_ordCompl hp hn0).symm
    have hτ' : ((τ : G) ^ (p ^ k)) ∈ N := N.pow_mem τ.2 _
    by_contra hne
    have hne' : (τ : G) ^ (p ^ k) ≠ 1 := by
      intro h; apply hne; ext; simpa using h
    have hl : ((τ : G) ^ (p ^ k)) ^ (n / p ^ k) = 1 := by
      rw [← pow_mul, Nat.mul_div_cancel' (Nat.ordProj_dvd n p), hn, pow_orderOf_eq_one]
    obtain ⟨y, hy⟩ : ∃ y : L, ((τ : G) ^ (p ^ k)) • y ≠ y := by
      by_contra h
      push_neg at h
      exact hne' (eq_of_smul_eq_smul (α := L) (fun y => by rw [h y, one_smul]))
    exact (hNmem _).1 hτ' (GlobalTheory.T.movesIntegersAlmostUnit_of_coprime_order L v p hp (Fix L N) hF hp0 hp1 G hinv _ (hfixN _ hτ') _ hcop hl ⟨y, hy⟩)
  haveI : Nontrivial N := ⟨⟨⟨σ, hσN⟩, 1, fun h => hσ (congrArg Subtype.val h)⟩⟩
  haveI : FaithfulSMul N L := ⟨fun {a b} h => Subtype.ext (eq_of_smul_eq_smul (α := L) h)⟩
  obtain ⟨σ₀, α, hα0, hσα, hαp⟩ := GlobalTheory.T.exists_lagrange_resolvent_of_pGroup_faithful L p hp N hpg ζ hζ (fun g => hζfix g)
  have hαF : α ^ p ∈ Fix L N := fun g => hαp g
  exact (hNmem _).1 σ₀.2 (GlobalTheory.T.kummer_automorphism_moves_integers_almost_unit L v p hp (Fix L N) hF hp0 hp1 G (σ₀ : G) (hfixN _ σ₀.2) ζ α hζ hα0 hαF hσα)

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostPurityMovesIntegersOfNeOneStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.almostPurity_moves_integers_of_ne_one : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L] [Finite G] [FaithfulSMul G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) → ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ∀ σ : G, σ ≠ 1 → Moves v ⊤ σ := by
  first | exact @GlobalTheory.AlmostEt.moves_of_ne_one | exact GlobalTheory.AlmostEt.moves_of_ne_one | (intros; apply GlobalTheory.AlmostEt.moves_of_ne_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostPurityOfNormalFiniteIndexSubgroup
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem mem_Fix_iff {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]
    (N : Subgroup G) (x : L) : x ∈ Fix L N ↔ ∀ h : G, h ∈ N → h • x = x :=
  ⟨fun hx h hh => hx ⟨h, hh⟩, fun hx m => hx m.1 m.2⟩

noncomputable instance quotFixAction {L : Type} [Field L] {G : Type} [Group G]
    [MulSemiringAction G L] (U : Subgroup G) [U.Normal] :
    MulSemiringAction (G ⧸ U) (Fix L U) :=
  inferInstanceAs (MulSemiringAction (G ⧸ U) (FixedPoints.subring L U))

theorem quot_smul_coe {L : Type} [Field L] {G : Type} [Group G]
    [MulSemiringAction G L] (U : Subgroup G) [U.Normal] (g : G) (x : Fix L U) :
    (((g : G ⧸ U) • x : Fix L U) : L) = g • (x : L) := rfl

end GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem almostSep_of_normal_finiteIndex : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ),
    p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L],
    (∀ (g : G) (x : L), v (g • x) = v x) → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) →
    ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ∀ U : Subgroup G, U.Normal → U.FiniteIndex →
    (∀ h : G, h ∉ U → ∃ x ∈ Fix L U, h • x ≠ x) → AlmostSep v U := by
  intro L _ v p hp hp0 hp1 G _ _ hv ζ hζ hζG hroot U hU hUfin hfaith
  refine GlobalTheory.T.fixedFieldAlmostEtale_of_moves_integers L v G hv U hU hUfin ?_
  intro σ hσ
  let L' := ↥(Fix L U)
  let v' : Valuation L' ℝ≥0 := v.comap (Fix L U).subtype
  have hv'x : ∀ x : L', v' x = v (x : L) := fun x => rfl
  haveI : Finite (G ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
  haveI : FaithfulSMul (G ⧸ U) L' := by
    refine ⟨fun {q₁ q₂} h => ?_⟩
    induction q₁ using QuotientGroup.induction_on with | H g₁ => ?_
    induction q₂ using QuotientGroup.induction_on with | H g₂ => ?_
    rw [QuotientGroup.eq]
    by_contra hne
    obtain ⟨x, hx, hmov⟩ := hfaith _ hne
    apply hmov
    have h1 := congrArg Subtype.val (h ⟨x, hx⟩)
    rw [quot_smul_coe, quot_smul_coe] at h1
    rw [mul_smul, ← h1, ← mul_smul, inv_mul_cancel, one_smul]
  have hpcast : ((p : L') : L) = (p : L) := map_natCast (Fix L U).subtype p
  have hζU : ζ ∈ Fix L U := (mem_Fix_iff U ζ).2 fun h _ => hζG h
  let ζ' : L' := ⟨ζ, hζU⟩
  have hζ' : IsPrimitiveRoot ζ' p :=
    (IsPrimitiveRoot.map_iff_of_injective (f := (Fix L U).subtype) Subtype.val_injective).1 hζ
  have hmain := GlobalTheory.T.almostPurity_moves_integers_of_ne_one L' v' p hp (by rw [hv'x, hpcast]; exact hp0)
    (by rw [hv'x, hpcast]; exact hp1) (G ⧸ U)
    (by
      intro q x
      induction q using QuotientGroup.induction_on with | H g => ?_
      rw [hv'x, hv'x, quot_smul_coe, hv])
    ζ' hζ'
    (by
      intro q
      induction q using QuotientGroup.induction_on with | H g => ?_
      exact Subtype.ext (by rw [quot_smul_coe]; exact hζG g))
    (by
      obtain ⟨θ, hθ, hθu⟩ := hroot
      refine ⟨θ, hθ, fun u hu => ?_⟩
      have hu' : (u : L) ∈ Fix L (⊤ : Subgroup G) := by
        refine (mem_Fix_iff _ _).2 fun g _ => ?_
        have := congrArg Subtype.val (((mem_Fix_iff _ u).1 hu) (g : G ⧸ U) trivial)
        rwa [quot_smul_coe] at this
      obtain ⟨w, hw, hwu⟩ := hθu _ hu'
      have hwU : w ∈ Fix L U := (mem_Fix_iff U w).2 fun h _ => (mem_Fix_iff _ w).1 hw h trivial
      refine ⟨⟨w, hwU⟩, ?_, ?_⟩
      · refine (mem_Fix_iff _ _).2 fun q _ => ?_
        induction q using QuotientGroup.induction_on with | H g => ?_
        exact Subtype.ext (by rw [quot_smul_coe]; exact (mem_Fix_iff _ w).1 hw g trivial)
      · rw [hv'x, hv'x]
        exact hwu)
    (σ : G ⧸ U) (by rwa [Ne, QuotientGroup.eq_one_iff])
  intro r hr
  obtain ⟨x, -, hx1, hxr⟩ := hmain r hr
  refine ⟨(x : L), x.2, hx1, ?_⟩
  rw [hv'x, AddSubgroupClass.coe_sub, quot_smul_coe] at hxr
  exact hxr

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostPurityOfNormalFiniteIndexSubgroupStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.almostPurity_of_normal_finiteIndex_subgroup : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) → ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ∀ U : Subgroup G, U.Normal → U.FiniteIndex → (∀ h : G, h ∉ U → ∃ x ∈ Fix L U, h • x ≠ x) → AlmostSep v U := by
  first | exact @GlobalTheory.AlmostEt.almostSep_of_normal_finiteIndex | exact GlobalTheory.AlmostEt.almostSep_of_normal_finiteIndex | (intros; apply GlobalTheory.AlmostEt.almostSep_of_normal_finiteIndex <;> assumption)
end
