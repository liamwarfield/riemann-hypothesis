module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltNormUltrametricEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorGaussNormUltrametric
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltraSumLe
namespace GlobalTheory.UltrametricSum

theorem ultra_sum_le {R : Type} [inst : CommRing R] (a : R → ℝ) (h0 : a (0 : R) = (0 : ℝ))
    (hadd : ∀ (x y : R), a (x + y) ≤ Max.max (a x) (a y)) {ι : Type} (s : Finset ι) (f : ι → R)
    (c : ℝ) (hc : (0 : ℝ) ≤ c) (h : ∀ i ∈ s, a (f i) ≤ c) : a (∑ i ∈ s, f i) ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, h0]; exact hc
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (hadd _ _).trans (max_le (h j (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

end GlobalTheory.UltrametricSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorGaussNormUltrametric
namespace GlobalTheory.WittGauss
open WittVector

def scaleCoeff (p : ℕ) {S : Type} [CommRing S] (t : S) (x : WittVector p S) : WittVector p S :=
  WittVector.mk p fun n => t ^ p ^ n * x.coeff n

theorem ghostComponent_scaleCoeff (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (t : S)
    (x : WittVector p S) (n : ℕ) :
    ghostComponent n (scaleCoeff p t x) = t ^ p ^ n * ghostComponent n x := by
  simp only [ghostComponent_apply, aeval_wittPolynomial, scaleCoeff, WittVector.coeff_mk,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have h : i + (n - i) = n := by
    have := Finset.mem_range.1 hi
    omega
  rw [mul_pow, ← pow_mul, ← pow_add, h]
  ring

theorem map_scaleCoeff (p : ℕ) [Fact p.Prime] {S S' : Type} [CommRing S] [CommRing S']
    (f : S →+* S') (t : S) (x : WittVector p S) :
    WittVector.map f (scaleCoeff p t x) = scaleCoeff p (f t) (WittVector.map f x) := by
  ext n
  simp [scaleCoeff, WittVector.map_coeff]

theorem teichmuller_mul_rat (p : ℕ) [Fact p.Prime] {S : Type} (t : MvPolynomial S ℚ)
    (x : WittVector p (MvPolynomial S ℚ)) : teichmuller p t * x = scaleCoeff p t x := by
  apply (ghostMap.bijective_of_invertible p (MvPolynomial S ℚ)).1
  ext1 n
  simp only [map_mul, ghostMap_apply, ghostComponent_teichmuller, ghostComponent_scaleCoeff]

theorem teichmuller_mul_int (p : ℕ) [Fact p.Prime] {S : Type} (t : MvPolynomial S ℤ)
    (x : WittVector p (MvPolynomial S ℤ)) : teichmuller p t * x = scaleCoeff p t x := by
  refine WittVector.map_injective (MvPolynomial.map (Int.castRingHom ℚ))
    (MvPolynomial.map_injective _ Int.cast_injective) ?_
  rw [map_mul, map_teichmuller, map_scaleCoeff, teichmuller_mul_rat]

theorem teichmuller_mul_eq (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (t : S)
    (x : WittVector p S) : teichmuller p t * x = scaleCoeff p t x := by
  obtain ⟨t, rfl⟩ := MvPolynomial.counit_surjective S t
  obtain ⟨x, rfl⟩ := WittVector.map_surjective (p := p)
    (MvPolynomial.counit S) (MvPolynomial.counit_surjective S) x
  have := congrArg (WittVector.map (MvPolynomial.counit S)) (teichmuller_mul_int p t x)
  rwa [map_mul, map_teichmuller, map_scaleCoeff] at this

section
variable {R : Type} [CommRing R] (a : R → ℝ) (hb : ∀ x, 0 ≤ a x ∧ a x ≤ 1) (h0 : a 0 = 0)
  (h1 : a 1 = 1) (hm : ∀ x y, a (x * y) = a x * a y) (ha : ∀ x y, a (x + y) ≤ max (a x) (a y))

include h0 ha in
theorem sum_le {ι : Type} (s : Finset ι) (f : ι → R) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i ∈ s, a (f i) ≤ c) : a (∑ i ∈ s, f i) ≤ c := by
  first
  | exact @_root_.GlobalTheory.UltrametricSum.ultra_sum_le
  | exact _root_.GlobalTheory.UltrametricSum.ultra_sum_le
  | (apply _root_.GlobalTheory.UltrametricSum.ultra_sum_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricSum.ultra_sum_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricSum.ultra_sum_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricSum.ultra_sum_le ..)

include hb h1 hm in
theorem neg_eq (x : R) : a (-x) = a x := by
  have h : a (-1) * a (-1) = 1 := by rw [← hm]; simpa using h1
  have h' : a (-1) = 1 := by nlinarith [(hb (-1)).1, (hb (-1)).2]
  rw [← neg_one_mul, hm, h', one_mul]

include h1 hm in
theorem pow_eq (x : R) (k : ℕ) : a (x ^ k) = a x ^ k := by
  induction k with
  | zero => simpa using h1
  | succ k ih => rw [pow_succ, hm, ih, pow_succ]

def weightRing (c : ℝ) (hc : 0 ≤ c) : Subring (Polynomial R) where
  carrier := {f | ∀ k, a (f.coeff k) ≤ c ^ k}
  zero_mem' k := by simpa [h0] using pow_nonneg hc k
  one_mem' k := by
    rw [Polynomial.coeff_one]
    split_ifs with h
    · simp [h, h1]
    · simpa [h0] using pow_nonneg hc k
  add_mem' {f g} hf hg k := by
    rw [Polynomial.coeff_add]
    exact (ha _ _).trans (max_le (hf k) (hg k))
  neg_mem' {f} hf k := by
    rw [Polynomial.coeff_neg, neg_eq a hb h1 hm]
    exact hf k
  mul_mem' {f g} hf hg k := by
    rw [Polynomial.coeff_mul]
    refine sum_le a h0 ha _ _ _ (pow_nonneg hc k) fun ij hij => ?_
    have e : ij.1 + ij.2 = k := by simpa using hij
    rw [hm, ← e, pow_add]
    exact mul_le_mul (hf _) (hg _) (hb _).1 (pow_nonneg hc _)

include hb h0 h1 hm ha in
theorem weight_add (p : ℕ) [Fact p.Prime] (c : ℝ) (hc : 0 ≤ c) (x y : WittVector p R)
    (hx : ∀ i, a (x.coeff i) ≤ c ^ p ^ i) (hy : ∀ i, a (y.coeff i) ≤ c ^ p ^ i) (n : ℕ) :
    a ((x + y).coeff n) ≤ c ^ p ^ n := by
  have key : ∀ z : WittVector p R, (∀ i, a (z.coeff i) ≤ c ^ p ^ i) →
      ∃ Z : WittVector p (weightRing a hb h0 h1 hm ha c hc),
        WittVector.map (weightRing a hb h0 h1 hm ha c hc).subtype Z =
          teichmuller p Polynomial.X * WittVector.map Polynomial.C z := by
    intro z hz
    refine ⟨WittVector.mk p fun i => ⟨Polynomial.X ^ p ^ i * Polynomial.C (z.coeff i), ?_⟩, ?_⟩
    · intro k
      rw [mul_comm, Polynomial.coeff_C_mul_X_pow]
      split_ifs with h
      · rw [h]; exact hz i
      · simpa [h0] using pow_nonneg hc k
    · rw [teichmuller_mul_eq]
      ext1 i
      simp [scaleCoeff, WittVector.map_coeff]
  obtain ⟨X, hX⟩ := key x hx
  obtain ⟨Y, hY⟩ := key y hy
  have h : WittVector.map (weightRing a hb h0 h1 hm ha c hc).subtype (X + Y) =
      scaleCoeff p Polynomial.X (WittVector.map Polynomial.C (x + y)) := by
    rw [← teichmuller_mul_eq, map_add (f := _), map_add (f := _), mul_add, hX, hY]
  have h2 := congrArg (fun z => WittVector.coeff z n) h
  simp only [WittVector.map_coeff, scaleCoeff, WittVector.coeff_mk] at h2
  have h3 := ((X + Y).coeff n).2 (p ^ n)
  change a (((weightRing a hb h0 h1 hm ha c hc).subtype ((X + Y).coeff n)).coeff _) ≤ _ at h3
  rwa [h2, mul_comm, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at h3

include hb h0 h1 hm ha in
theorem weight_add_trunc (p : ℕ) [Fact p.Prime] (c : ℝ) (hc : 0 ≤ c) (x y : WittVector p R)
    (n : ℕ) (hx : ∀ i ≤ n, a (x.coeff i) ≤ c ^ p ^ i) (hy : ∀ i ≤ n, a (y.coeff i) ≤ c ^ p ^ i) :
    a ((x + y).coeff n) ≤ c ^ p ^ n := by
  have key : ∀ z : WittVector p R, (∀ i ≤ n, a (z.coeff i) ≤ c ^ p ^ i) →
      ∃ z' : WittVector p R, truncate (n + 1) z = truncate (n + 1) z' ∧
        ∀ i, a (z'.coeff i) ≤ c ^ p ^ i := by
    intro z hz
    refine ⟨WittVector.mk p fun i => if i ≤ n then z.coeff i else 0, ?_, fun i => ?_⟩
    · ext i
      simp only [coeff_truncate, WittVector.coeff_mk, if_pos (Nat.lt_succ_iff.1 i.2)]
    · rw [WittVector.coeff_mk]
      split_ifs with h
      · exact hz i h
      · simpa [h0] using pow_nonneg hc _
  obtain ⟨x', hx1, hx2⟩ := key x hx
  obtain ⟨y', hy1, hy2⟩ := key y hy
  have h : truncate (n + 1) (x + y) = truncate (n + 1) (x' + y') := by
    rw [map_add (f := _), map_add (f := _), hx1, hy1]
  have h2 := congrArg (TruncatedWittVector.coeff (Fin.last n)) h
  rw [coeff_truncate, coeff_truncate, Fin.val_last] at h2
  rw [h2]
  exact weight_add a hb h0 h1 hm ha p c hc x' y' hx2 hy2 n

end

theorem root_pow (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (t ^ ((1 : ℝ) / (p : ℝ) ^ n)) ^ p ^ n = t := by
  rw [one_div, ← Nat.cast_pow]
  exact Real.rpow_inv_natCast_pow ht (pow_ne_zero _ hp.out.ne_zero)

theorem pow_root (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (t ^ p ^ n) ^ ((1 : ℝ) / (p : ℝ) ^ n) = t := by
  rw [one_div, ← Nat.cast_pow]
  exact Real.pow_rpow_inv_natCast ht (pow_ne_zero _ hp.out.ne_zero)

theorem coeff_eq_of_dvd (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    [PerfectRing R p] (x y : WittVector p R) (n : ℕ)
    (h : (p : WittVector p R) ^ (n + 1) ∣ x - y) : x.coeff n = y.coeff n := by
  have h1 := (mem_span_p_pow_iff_le_coeff_eq_zero (x - y) (n + 1)).1 (Ideal.mem_span_singleton.2 h)
  have h2 := (mem_ker_truncate (n + 1) (x - y)).2 h1
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h2
  have h3 := congrArg (TruncatedWittVector.coeff (Fin.last n)) h2
  rwa [coeff_truncate, coeff_truncate, Fin.val_last] at h3

theorem gaussNorm_ultrametric_submul : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (a : R → ℝ), (∀ x, 0 ≤ a x ∧ a x ≤ 1) → a 0 = 0 → a 1 = 1 → (∀ x y, a (x * y) = a x * a y) → (∀ x y, a (x + y) ≤ max (a x) (a y)) → ∀ r : ℝ, 0 < r → r < 1 → ∀ N : WittVector l R → ℝ, (∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ (∀ x, N (-x) = N x) ∧ ∀ x y, N (x * y) ≤ N x * N y := by
  intro l hl R _ _ _ a hb h0 h1 hm ha r hr0 hr1 N hN
  have hexp : ∀ n : ℕ, (0 : ℝ) < 1 / (l : ℝ) ^ n := fun n => by
    have : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
    positivity
  have hle1 : ∀ (x : WittVector l R) (n : ℕ),
      a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n ≤ 1 := fun x n =>
    mul_le_one₀ (Real.rpow_le_one (hb _).1 (hb _).2 (hexp n).le) (pow_nonneg hr0.le _)
      (pow_le_one₀ hr0.le hr1.le)
  have hge : ∀ (x : WittVector l R) (n : ℕ),
      a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n ≤ N x := fun x n => by
    rw [hN]
    exact le_ciSup (f := fun n : ℕ => a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n)
      ⟨1, by rintro _ ⟨m, rfl⟩; exact hle1 x m⟩ n
  have hle : ∀ (x : WittVector l R) (c : ℝ),
      (∀ n, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n ≤ c) → N x ≤ c := fun x c h => by
    rw [hN]; exact ciSup_le h
  have hnn : ∀ x, 0 ≤ N x := fun x =>
    (mul_nonneg (Real.rpow_nonneg (hb _).1 _) (pow_nonneg hr0.le _)).trans (hge x 0)
  have hadd : ∀ x y, N (x + y) ≤ max (N x) (N y) := by
    intro x y
    refine hle _ _ fun n => ?_
    set c := max (N x) (N y) with hc
    have hc0 : 0 ≤ c := (hnn x).trans (le_max_left _ _)
    have hrn : 0 < r ^ n := pow_pos hr0 n
    have key : ∀ z : WittVector l R, N z ≤ c → ∀ i ≤ n, a (z.coeff i) ≤ (c / r ^ n) ^ l ^ i := by
      intro z hz i hi
      rw [← root_pow l i _ (hb (z.coeff i)).1]
      refine pow_le_pow_left₀ (Real.rpow_nonneg (hb _).1 _) ?_ _
      rw [le_div_iff₀ hrn]
      refine le_trans ?_ ((hge z i).trans hz)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1.le hi)
        (Real.rpow_nonneg (hb _).1 _)
    have h := weight_add_trunc a hb h0 h1 hm ha l (c / r ^ n) (by positivity) x y n
      (key x (le_max_left _ _)) (key y (le_max_right _ _))
    rw [← le_div_iff₀ hrn, ← pow_root l n (c / r ^ n) (by positivity)]
    exact Real.rpow_le_rpow (hb _).1 h (hexp n).le
  have hzero : N 0 = 0 := by
    refine le_antisymm (hle _ _ fun n => ?_) (hnn _)
    rw [WittVector.zero_coeff, h0, Real.zero_rpow (hexp n).ne', zero_mul]
  have hte : ∀ (u : R) (k : ℕ), N (teichmuller l u * (l : WittVector l R) ^ k) ≤ a u * r ^ k := by
    intro u k
    refine hle _ _ fun n => ?_
    by_cases h : n = k
    · subst h
      rw [teichmuller_mul_pow_coeff, pow_eq a h1 hm, pow_root l n _ (hb _).1]
    · rw [teichmuller_mul_pow_coeff_of_ne _ h, h0, Real.zero_rpow (hexp n).ne', zero_mul]
      exact mul_nonneg (hb _).1 (pow_nonneg hr0.le _)
  have hroot : ∀ (x : WittVector l R) (i : ℕ),
      a (((_root_.frobeniusEquiv R l).symm ^ i) (x.coeff i)) * r ^ i ≤ N x := by
    intro x i
    have e : ∀ (i : ℕ) (u : R), (((_root_.frobeniusEquiv R l).symm ^ i) u) ^ l ^ i = u := by
      intro i
      induction i with
      | zero => intro u; simp
      | succ i ih =>
        intro u
        rw [pow_succ', RingAut.mul_apply, pow_succ', pow_mul, frobeniusEquiv_symm_pow_p, ih]
    have := hge x i
    rwa [← e i (x.coeff i), pow_eq a h1 hm, pow_root l i _ (hb _).1] at this
  have hmul : ∀ x y, N (x * y) ≤ N x * N y := by
    intro x y
    refine hle _ _ fun n => ?_
    have hx := dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x n
    have hy := dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff y n
    have hxy : ∀ x' y' : WittVector l R, (l : WittVector l R) ^ (n + 1) ∣ x - x' →
        (l : WittVector l R) ^ (n + 1) ∣ y - y' → (x * y).coeff n = (x' * y').coeff n := by
      intro x' y' h h'
      refine coeff_eq_of_dvd l _ _ n ?_
      have : x * y - x' * y' = (x - x') * y + x' * (y - y') := by ring
      rw [this]
      exact dvd_add (h.mul_right _) (h'.mul_left _)
    rw [hxy _ _ hx hy]
    refine (hge _ n).trans ?_
    have hc : 0 ≤ N x * N y := mul_nonneg (hnn x) (hnn y)
    rw [Finset.sum_mul_sum]
    refine sum_le N hzero hadd _ _ _ hc fun i _ => sum_le N hzero hadd _ _ _ hc fun j _ => ?_
    rw [mul_mul_mul_comm, ← map_mul, ← pow_add]
    refine (hte _ _).trans ?_
    rw [hm, pow_add, mul_mul_mul_comm]
    exact mul_le_mul (hroot x i) (hroot y j) (mul_nonneg (hb _).1 (pow_nonneg hr0.le _)) (hnn x)
  have hneg : ∀ x, N (-x) ≤ N x := fun x => by
    rw [← neg_one_mul]
    refine (hmul _ _).trans ?_
    exact mul_le_of_le_one_left (hnn x) (hle _ _ (hle1 _))
  refine ⟨hadd, fun x => le_antisymm (hneg x) ?_, hmul⟩
  simpa using hneg (-x)

end GlobalTheory.WittGauss
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorGaussNormUltrametricStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_vector_gauss_norm_ultrametric : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (a : R → ℝ), (∀ x, 0 ≤ a x ∧ a x ≤ 1) → a 0 = 0 → a 1 = 1 → (∀ x y, a (x * y) = a x * a y) → (∀ x y, a (x + y) ≤ max (a x) (a y)) → ∀ r : ℝ, 0 < r → r < 1 → ∀ N : WittVector l R → ℝ, (∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ (∀ x, N (-x) = N x) ∧ ∀ x y, N (x * y) ≤ N x * N y := by
  first | exact @GlobalTheory.WittGauss.gaussNorm_ultrametric_submul | exact GlobalTheory.WittGauss.gaussNorm_ultrametric_submul | (intros; apply GlobalTheory.WittGauss.gaussNorm_ultrametric_submul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorGaussNormMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorGaussNormMul
namespace GlobalTheory

namespace WittGaussMul

theorem exists_lt_bound (f : ℕ → ℝ) (B : ℝ) (hB : 0 < B) (i : ℕ) (h : ∀ k < i, f k < B) :
    ∃ c, 0 ≤ c ∧ c < B ∧ ∀ k < i, f k ≤ c := by
  induction i with
  | zero => exact ⟨0, le_rfl, hB, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ i ih =>
    obtain ⟨c, hc0, hcB, hc⟩ := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    refine ⟨max c (f i), le_max_of_le_left hc0, max_lt hcB (h i (Nat.lt_succ_self i)), ?_⟩
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact le_max_of_le_left (hc k hk)
    · exact le_max_right _ _

theorem exists_first_max (f : ℕ → ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hf : ∀ n, f n ≤ r ^ n) (hpos : 0 < ⨆ n, f n) :
    ∃ i, f i = (⨆ n, f n) ∧ ∀ k < i, f k < ⨆ n, f n := by
  classical
  have hb : BddAbove (Set.range f) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (hf n).trans (pow_le_one₀ hr0.le hr1.le)⟩
  have hle : ∀ n, f n ≤ ⨆ n, f n := fun n => le_ciSup hb n
  have hex : ∃ i, f i = ⨆ n, f n := by
    by_contra hne
    push Not at hne
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hpos hr1
    obtain ⟨c, -, hcB, hc⟩ := exists_lt_bound f _ hpos M
      (fun k _ => lt_of_le_of_ne (hle k) (hne k))
    have : (⨆ n, f n) ≤ max c (r ^ M) := by
      refine ciSup_le fun n => ?_
      rcases lt_or_ge n M with h | h
      · exact le_max_of_le_left (hc n h)
      · exact le_max_of_le_right ((hf n).trans (pow_le_pow_of_le_one hr0.le hr1.le h))
    exact absurd (max_lt hcB hM) (not_lt.mpr this)
  exact ⟨Nat.find hex, Nat.find_spec hex,
    fun k hk => lt_of_le_of_ne (hle k) (Nat.find_min hex hk)⟩

end WittGaussMul


open WittGaussMul in
theorem witt_gaussNorm_mul : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (a : R → ℝ), (∀ x, 0 ≤ a x ∧ a x ≤ 1) → a 0 = 0 → a 1 = 1 → (∀ x y, a (x * y) = a x * a y) → (∀ x y, a (x + y) ≤ max (a x) (a y)) → ∀ r : ℝ, 0 < r → r < 1 → ∀ N : WittVector l R → ℝ, (∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ x y, N (x * y) = N x * N y := by
  intro l hl R _ _ _ a h01 h0 h1 hmul hadd r hr0 hr1 N hN x y
  obtain ⟨Nadd, Nneg, Nmul⟩ := GlobalTheory.T.witt_vector_gauss_norm_ultrametric l R a h01 h0 h1 hmul hadd r hr0 hr1 N hN
  set T : WittVector l R → ℕ → ℝ := fun x n => a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n
    with hT
  have hN' : ∀ x, N x = ⨆ n, T x n := hN
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hexp : ∀ n : ℕ, (0 : ℝ) < 1 / (l : ℝ) ^ n := fun n => by positivity
  have hT0 : ∀ x n, 0 ≤ T x n := fun x n =>
    mul_nonneg (Real.rpow_nonneg (h01 _).1 _) (pow_pos hr0 n).le
  have hTr : ∀ x n, T x n ≤ r ^ n := fun x n =>
    mul_le_of_le_one_left (pow_pos hr0 n).le
      (Real.rpow_le_one (h01 _).1 (h01 _).2 (hexp n).le)
  have hTN : ∀ x n, T x n ≤ N x := fun x n => by
    rw [hN']
    exact le_ciSup (f := T x)
      ⟨1, by rintro _ ⟨n, rfl⟩; exact (hTr x n).trans (pow_le_one₀ hr0.le hr1.le)⟩ n
  have hN0 : ∀ x, 0 ≤ N x := fun x => (hT0 x 0).trans (hTN x 0)
  have hTz : ∀ x n, x.coeff n = 0 → T x n = 0 := fun x n h => by
    simp only [hT, h, h0, Real.zero_rpow (hexp n).ne', zero_mul]
  have hpow : ∀ w (n : ℕ), a (w ^ n) = a w ^ n := fun w n => by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hTp : ∀ (u : WittVector l R) (n : ℕ), T (u * (l : WittVector l R) ^ n) n
      = a (u.coeff 0) * r ^ n := fun u n => by
    have h := WittVector.mul_pow_charP_coeff_succ u (m := 0) (n := n)
    rw [zero_add] at h
    simp only [hT, h, hpow]
    congr 1
    have := Real.pow_rpow_inv_natCast (h01 (u.coeff 0)).1 (pow_pos hl.out.pos n).ne'
    simpa using this
  have key : ∀ x, 0 < N x → ∃ (i : ℕ) (x0 u : WittVector l R),
      x = x0 + u * (l : WittVector l R) ^ i ∧ N x0 < N x ∧
      N (u * (l : WittVector l R) ^ i) ≤ N x ∧ a (u.coeff 0) * r ^ i = N x := by
    intro x hx
    obtain ⟨i, hi, hlt⟩ := exists_first_max (T x) r hr0 hr1 (hTr x) (by rw [← hN']; exact hx)
    rw [← hN'] at hi hlt
    have hmem : WittVector.tail i x ∈ Ideal.span {((l : WittVector l R) ^ i)} := by
      rw [WittVector.mem_span_p_pow_iff_le_coeff_eq_zero]
      intro m hm
      simp [WittVector.tail, WittVector.select, WittVector.coeff_mk, not_le.mpr hm]
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨i, WittVector.init i x, u, ?_, ?_, ?_, ?_⟩
    · rw [hu, WittVector.init_add_tail]
    · obtain ⟨c, hc0, hcB, hc⟩ := exists_lt_bound (T x) _ hx i hlt
      refine lt_of_le_of_lt ?_ hcB
      rw [hN']
      refine ciSup_le fun n => ?_
      rcases lt_or_ge n i with h | h
      · have : (WittVector.init i x).coeff n = x.coeff n := by
          simp [WittVector.init, WittVector.select, WittVector.coeff_mk, h]
        have h2 : T (WittVector.init i x) n = T x n := by simp only [hT, this]
        rw [h2]; exact hc n h
      · rw [hTz]
        · exact hc0
        · simp [WittVector.init, WittVector.select, WittVector.coeff_mk, not_lt.mpr h]
    · rw [hu, hN' (WittVector.tail i x)]
      refine ciSup_le fun n => ?_
      rcases lt_or_ge n i with h | h
      · rw [hTz]
        · exact hN0 x
        · simp [WittVector.tail, WittVector.select, WittVector.coeff_mk, not_le.mpr h]
      · have : (WittVector.tail i x).coeff n = x.coeff n := by
          simp [WittVector.tail, WittVector.select, WittVector.coeff_mk, h]
        have h2 : T (WittVector.tail i x) n = T x n := by simp only [hT, this]
        rw [h2]; exact hTN x n
    · rw [← hTp, hu, ← hi]
      have : (WittVector.tail i x).coeff i = x.coeff i := by
        simp [WittVector.tail, WittVector.select, WittVector.coeff_mk]
      simp only [hT, this]
  refine le_antisymm (Nmul x y) ?_
  rcases (hN0 x).eq_or_lt with hx | hx
  · rw [← hx, zero_mul]; exact hN0 _
  rcases (hN0 y).eq_or_lt with hy | hy
  · rw [← hy, mul_zero]; exact hN0 _
  obtain ⟨i, x0, u, hxe, hx0, hu, hui⟩ := key x hx
  obtain ⟨j, y0, v, hye, hy0, hv, hvj⟩ := key y hy
  have hmain : N x * N y ≤ N ((u * v) * (l : WittVector l R) ^ (i + j)) := by
    refine le_trans (le_of_eq ?_) (hTN _ (i + j))
    rw [hTp, WittVector.mul_coeff_zero, hmul, ← hui, ← hvj]
    ring
  have hrest : N (x0 * y + (u * (l : WittVector l R) ^ i) * y0) < N x * N y := by
    refine lt_of_le_of_lt (Nadd _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Nmul _ _) (mul_lt_mul_of_pos_right hx0 hy)
    · refine lt_of_le_of_lt (Nmul _ _) ?_
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hu (hN0 _)) (mul_lt_mul_of_pos_left hy0 hx)
  have heq : (u * v) * (l : WittVector l R) ^ (i + j)
      = x * y + -(x0 * y + (u * (l : WittVector l R) ^ i) * y0) := by
    have : x * y = x0 * y + (u * (l : WittVector l R) ^ i) * (y0 + v * (l : WittVector l R) ^ j) := by
      rw [← hye, ← add_mul, ← hxe]
    rw [this]; ring
  have h3 := Nadd (x * y) (-(x0 * y + (u * (l : WittVector l R) ^ i) * y0))
  rw [← heq, Nneg] at h3
  rcases le_max_iff.mp (hmain.trans h3) with h | h
  · exact h
  · exact absurd hrest (not_lt.mpr h)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorGaussNormMulStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittVector_gaussNorm_mul : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (a : R → ℝ), (∀ x, 0 ≤ a x ∧ a x ≤ 1) → a 0 = 0 → a 1 = 1 → (∀ x y, a (x * y) = a x * a y) → (∀ x y, a (x + y) ≤ max (a x) (a y)) → ∀ r : ℝ, 0 < r → r < 1 → ∀ N : WittVector l R → ℝ, (∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ x y, N (x * y) = N x * N y := by
  first | exact @GlobalTheory.witt_gaussNorm_mul | exact GlobalTheory.witt_gaussNorm_mul | (intros; apply GlobalTheory.witt_gaussNorm_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris
noncomputable section
namespace GlobalTheory.GaussExt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc Filter Topology
open scoped Formalism.Per

theorem exists_ext_loc {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R)
    [IsLocalization M S] (N : R → ℝ) (h0 : ∀ x, 0 ≤ N x)
    (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y)) (hneg : ∀ x, N (-x) = N x)
    (hmul : ∀ x y, N (x * y) = N x * N y) (hM : ∀ m ∈ M, N m ≠ 0) :
    ∃ N' : S → ℝ, (∀ x, 0 ≤ N' x) ∧ (∀ x y, N' (x + y) ≤ max (N' x) (N' y)) ∧ (∀ x, N' (-x) = N' x) ∧
      (∀ x y, N' (x * y) = N' x * N' y) ∧ ∀ a, N' (algebraMap R S a) = N a := by
  have hpos : ∀ m : M, 0 < N m := fun m => lt_of_le_of_ne (h0 _) (hM m m.2).symm
  have hinj : ∀ a b : R, algebraMap R S a = algebraMap R S b → N a = N b := by
    intro a b h
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M S).1 h
    have := congrArg N hc
    rw [hmul, hmul] at this
    exact mul_left_cancel₀ (hpos c).ne' this
  let N' : S → ℝ := fun z => N (IsLocalization.sec M z).1 / N (IsLocalization.sec M z).2
  have key : ∀ (z : S) (a : R) (b : M), z * algebraMap R S b = algebraMap R S a → N' z = N a / N b := by
    intro z a b h
    have h1 := IsLocalization.sec_spec M z
    have h2 : algebraMap R S ((IsLocalization.sec M z).1 * b) =
        algebraMap R S (a * (IsLocalization.sec M z).2) := by
      rw [map_mul, map_mul, ← h1, ← h]; ring
    have h3 := hinj _ _ h2
    rw [hmul, hmul] at h3
    simp only [N']
    rw [div_eq_div_iff (hpos _).ne' (hpos _).ne', h3]
  refine ⟨N', fun x => div_nonneg (h0 _) (h0 _), fun x y => ?_, fun x => ?_, fun x y => ?_, fun a => ?_⟩
  · obtain ⟨⟨a, b⟩, hx⟩ := IsLocalization.surj M x
    obtain ⟨⟨c, d⟩, hy⟩ := IsLocalization.surj M y
    simp only at hx hy
    rw [key x (a * d) (b * d) (by simp only [Submonoid.coe_mul, map_mul, ← hx]; ring),
      key y (c * b) (b * d) (by simp only [Submonoid.coe_mul, map_mul, ← hy]; ring),
      key (x + y) (a * d + c * b) (b * d)
        (by simp only [Submonoid.coe_mul, map_mul, map_add (f := _), ← hx, ← hy]; ring),
      max_div_div_right (h0 _)]
    exact div_le_div_of_nonneg_right (hadd _ _) (h0 _)
  · obtain ⟨⟨a, b⟩, hx⟩ := IsLocalization.surj M x
    simp only at hx
    rw [key x a b hx, key (-x) (-a) b (by rw [map_neg, ← hx]; ring), hneg]
  · obtain ⟨⟨a, b⟩, hx⟩ := IsLocalization.surj M x
    obtain ⟨⟨c, d⟩, hy⟩ := IsLocalization.surj M y
    simp only at hx hy
    rw [key x a b hx, key y c d hy, key (x * y) (a * c) (b * d)
        (by simp only [Submonoid.coe_mul, map_mul, ← hx, ← hy]; ring), Submonoid.coe_mul, hmul, hmul,
      mul_div_mul_comm]
  · have h1 : N 1 = 1 := by
      have := hmul 1 1
      rw [mul_one] at this
      exact (mul_left_cancel₀ (hM 1 M.one_mem) (by rw [mul_one]; exact this)).symm
    rw [key _ a 1 (by simp), Submonoid.coe_one, h1, div_one]

theorem exists_ext_compl {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (p : ℕ) (N : A → ℝ)
    (h0 : ∀ x, 0 ≤ N x ∧ N x ≤ 1)
    (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y)) (hneg : ∀ x, N (-x) = N x)
    (hmul : ∀ x y, N (x * y) = N x * N y) (hp : N p < 1)
    (hd : ∀ (x : B) (k : ℕ), ∃ (s : A) (z : B), x = f s + (p : B) ^ k * z)
    (hr : ∀ (s : A) (k : ℕ), (p : B) ^ k ∣ f s → (p : A) ^ k ∣ s) :
    ∃ N' : B → ℝ, (∀ x, 0 ≤ N' x ∧ N' x ≤ 1) ∧ (∀ x y, N' (x + y) ≤ max (N' x) (N' y)) ∧
      (∀ x, N' (-x) = N' x) ∧ (∀ x y, N' (x * y) = N' x * N' y) ∧ ∀ a, N' (f a) = N a := by
  have hpow : ∀ (k : ℕ) (z : A), N ((p : A) ^ k * z) ≤ N p ^ k := by
    intro k
    induction k with
    | zero => intro z; simpa using (h0 z).2
    | succ k ih =>
      intro z
      rw [pow_succ', mul_assoc, hmul, pow_succ']
      exact mul_le_mul_of_nonneg_left (ih z) (h0 _).1
  have hle : ∀ (k : ℕ) (s t : A), (p : B) ^ k ∣ f s - f t → N s ≤ N t + N p ^ k := by
    intro k s t h
    rw [← map_sub] at h
    obtain ⟨z, hz⟩ := hr _ _ h
    have h1 : s = t + (p : A) ^ k * z := by rw [← hz]; ring
    have h2 := hadd t ((p : A) ^ k * z)
    rw [← h1] at h2
    have h3 := hpow k z
    have h4 := (h0 t).1
    have h5 := pow_nonneg (h0 p).1 k
    exact h2.trans (max_le (by linarith) (by linarith))
  have hdist : ∀ (k : ℕ) (s t : A), (p : B) ^ k ∣ f s - f t → dist (N s) (N t) ≤ N p ^ k := by
    intro k s t h
    have h1 := hle k s t h
    have h2 := hle k t s (by rw [← neg_sub]; exact h.neg_right)
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  have hlim : Tendsto (fun k : ℕ => N p ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (h0 _).1 hp
  have hs : ∀ x : B, ∃ s : ℕ → A, ∀ k, (p : B) ^ k ∣ x - f (s k) := by
    intro x
    choose s z h using hd x
    exact ⟨s, fun k => ⟨z k, by rw [sub_eq_iff_eq_add', ← h k]⟩⟩
  have hex : ∀ x : B, ∃ t : ℝ, ∀ s : ℕ → A, (∀ k, (p : B) ^ k ∣ x - f (s k)) →
      Tendsto (fun k => N (s k)) atTop (𝓝 t) := by
    intro x
    obtain ⟨s, hs⟩ := hs x
    have hc : CauchySeq fun k => N (s k) :=
      cauchySeq_of_le_tendsto_0' (fun k => N p ^ k) (fun n m h => hdist n _ _ (by
        have := ((pow_dvd_pow _ h).trans (hs m)).sub (hs n)
        convert this using 1; ring)) hlim
    obtain ⟨t, ht⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨t, fun s' hs' => ht.congr_dist (squeeze_zero (fun _ => dist_nonneg) (fun k => hdist k _ _ ?_) hlim)⟩
    have := (hs' k).sub (hs k)
    convert this using 1; ring
  choose N' hN' using hex
  refine ⟨N', fun x => ?_, fun x y => ?_, fun x => ?_, fun x y => ?_, fun a => ?_⟩
  · obtain ⟨s, hs⟩ := hs x
    exact ⟨ge_of_tendsto' (hN' x s hs) fun k => (h0 _).1, le_of_tendsto' (hN' x s hs) fun k => (h0 _).2⟩
  · obtain ⟨s, hx⟩ := hs x
    obtain ⟨t, hy⟩ := hs y
    refine le_of_tendsto_of_tendsto' (hN' (x + y) (fun k => s k + t k) fun k => ?_)
      ((hN' x s hx).max (hN' y t hy)) fun k => hadd _ _
    have := (hx k).add (hy k)
    convert this using 1; rw [map_add (f := _)]; ring
  · obtain ⟨s, hx⟩ := hs x
    refine tendsto_nhds_unique (hN' (-x) (fun k => -s k) fun k => ?_) (by simpa only [hneg] using hN' x s hx)
    have := (hx k).neg_right
    convert this using 1; rw [map_neg]; ring
  · obtain ⟨s, hx⟩ := hs x
    obtain ⟨t, hy⟩ := hs y
    refine tendsto_nhds_unique (hN' (x * y) (fun k => s k * t k) fun k => ?_)
      (by simpa only [hmul] using (hN' x s hx).mul (hN' y t hy))
    have := ((hx k).mul_right y).add ((hy k).mul_left (f (s k)))
    convert this using 1; rw [map_mul]; ring
  · exact tendsto_nhds_unique (hN' (f a) (fun _ => a) fun k => by simp) tendsto_const_nhds

theorem pow_le_factorial {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] (N : R → ℝ)
    (h0 : ∀ x, 0 ≤ N x ∧ N x ≤ 1) (h1 : N 1 = 1)
    (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y))
    (hmul : ∀ x y, N (x * y) = N x * N y) (hp : N p < 1) (n : ℕ) :
    N p ^ n ≤ N (n.factorial : R) := by
  have hpow : ∀ k : ℕ, N ((p : R) ^ k) = N p ^ k := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  have hcop : ∀ m : ℕ, ¬ p ∣ m → 1 ≤ N m := by
    intro m hm
    have hc : IsCoprime (p : R) (m : R) :=
      Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm)
    obtain ⟨a, b, hab⟩ := hc
    have h2 := hadd (a * p) (b * m)
    rw [hab, h1, hmul, hmul] at h2
    rcases le_max_iff.1 h2 with h | h
    · nlinarith [h0 a, h0 p]
    · nlinarith [h0 b, h0 m]
  obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd n.factorial_ne_zero p
    (Fact.out : p.Prime).ne_one
  have hen : e ≤ n := by
    have h2 : e ≤ padicValNat p n.factorial :=
      ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) n.factorial_ne_zero).1 ⟨m, he⟩
    have h3 := Nat.Prime.sub_one_mul_multiplicity_factorial (n := n) (Fact.out : p.Prime)
    rw [← Nat.padicValNat_def] at h3
    have h4 : 1 ≤ p - 1 := by have := (Fact.out : p.Prime).two_le; omega
    have h5 := Nat.mul_le_mul_right (padicValNat p n.factorial) h4
    omega
  rw [he, Nat.cast_mul, Nat.cast_pow, hmul, hpow]
  exact (pow_le_pow_of_le_one (h0 _).1 (h0 _).2 hen).trans
    (le_mul_of_one_le_right (pow_nonneg (h0 _).1 _) (hcop m hm))

variable {l : ℕ} [Fact l.Prime]

theorem untilt_zero : (0 : Per.Fl l).untilt = 0 := by
  rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]

theorem norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [GlobalTheory.RingBasics.norm_eq_val, PadicComplex.valuation_p]
  simp

theorem norm_coeff_zero_le (x : Per.Ainf l) (hx : Per.θ l x = 0) :
    ‖(((x.coeff 0).untilt : Per.OC l) : ℂ_[l])‖ ≤ (l : ℝ)⁻¹ := by
  have h := WittVector.mk_fontaineTheta x
  rw [← PreTilt.mk_untilt_eq_coeff_zero, show WittVector.fontaineTheta (Per.OC l) l x = 0 from hx,
    map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem, ← pow_one (Ideal.span _),
    GlobalTheory.RingBasics.mem_span_pow_OC, pow_one, norm_l] at h
  exact h

theorem exists_gauss_acris (l : ℕ) [Fact l.Prime] (r : ℝ) (hr : (l : ℝ)⁻¹ ≤ r) (hr1 : r < 1) :
    ∃ N : Per.Acris l → ℝ, (∀ x, 0 ≤ N x ∧ N x ≤ 1) ∧ (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧
      (∀ x, N (-x) = N x) ∧ (∀ x y, N (x * y) = N x * N y) ∧
      ∀ a : Per.Ainf l, N (algebraMap (Per.Ainf l) (Per.Acris l) a) =
        ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hr0 : 0 < r := (inv_pos.2 hl).trans_le hr
  let a : Per.Fl l → ℝ := fun x => ‖((x.untilt : Per.OC l) : ℂ_[l])‖
  have a01 : ∀ x, 0 ≤ a x ∧ a x ≤ 1 := fun x => ⟨norm_nonneg _, (GlobalTheory.RingBasics.mem_OC _).1 (x.untilt).2⟩
  have a0 : a 0 = 0 := by simp only [a, untilt_zero]; simp
  have a1 : a 1 = 1 := by simp [a]
  have amul : ∀ x y, a (x * y) = a x * a y := by intro x y; simp [a]
  have aadd : ∀ x y, a (x + y) ≤ max (a x) (a y) := fun x y => (GlobalTheory.T.untilt_norm_ultrametric_eq_zero l x y).1
  obtain ⟨N, hN⟩ : ∃ N : Per.Ainf l → ℝ,
      ∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n := ⟨_, fun _ => rfl⟩
  obtain ⟨Nadd, Nneg, -⟩ := GlobalTheory.T.witt_vector_gauss_norm_ultrametric l (Per.Fl l) a a01 a0 a1 amul aadd r hr0 hr1 N hN
  have Nmul := GlobalTheory.T.wittVector_gaussNorm_mul l (Per.Fl l) a a01 a0 a1 amul aadd r hr0 hr1 N hN
  have he : ∀ n : ℕ, (0 : ℝ) < 1 / (l : ℝ) ^ n := fun n => by positivity
  have ht0 : ∀ (y : Per.Fl l) (n : ℕ), 0 ≤ a y ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n := fun y n =>
    mul_nonneg (Real.rpow_nonneg (a01 y).1 _) (pow_nonneg hr0.le _)
  have ht1 : ∀ (y : Per.Fl l) (n : ℕ), a y ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n ≤ r ^ n := fun y n =>
    mul_le_of_le_one_left (pow_nonneg hr0.le _) (Real.rpow_le_one (a01 y).1 (a01 y).2 (he n).le)
  have rank_lt_alt : ∀ x, 0 ≤ N x ∧ N x ≤ 1 := fun x => by
    rw [hN]
    exact ⟨Real.iSup_nonneg fun n => ht0 _ n,
      ciSup_le fun n => (ht1 _ n).trans (pow_le_one₀ hr0.le hr1.le)⟩
  have Nker : ∀ x, Per.θ l x = 0 → N x ≤ r := fun x hx => by
    rw [hN]
    refine ciSup_le fun n => ?_
    rcases n with _ | n
    · simpa using (norm_coeff_zero_le x hx).trans hr
    · exact (ht1 _ _).trans (pow_le_of_le_one hr0.le hr1.le n.succ_ne_zero)
  have Nl : N (l : Per.Ainf l) = r := by
    rw [hN]
    have hterm : ∀ n : ℕ, a ((l : Per.Ainf l).coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n =
        if n = 1 then r else 0 := by
      intro n
      rw [WittVector.coeff_p]
      split_ifs with h
      · rw [a1, h, Real.one_rpow, one_mul, pow_one]
      · rw [a0, Real.zero_rpow (he n).ne', zero_mul]
    simp only [hterm]
    refine le_antisymm (ciSup_le fun n => by split_ifs; exacts [le_rfl, hr0.le]) ?_
    refine le_ciSup_of_le ⟨r, ?_⟩ 1 (by simp)
    rintro _ ⟨n, rfl⟩
    dsimp only
    split_ifs
    exacts [le_rfl, hr0.le]
  have N1 : N 1 = 1 := by
    have := Nmul l 1
    rw [mul_one, Nl] at this
    exact (mul_left_cancel₀ hr0.ne' (by rw [mul_one]; exact this)).symm
  have Npow : ∀ (x : Per.Ainf l) (k : ℕ), N (x ^ k) = N x ^ k := by
    intro x k
    induction k with
    | zero => simpa using N1
    | succ k ih => rw [pow_succ, Nmul, ih, pow_succ]
  obtain ⟨M, M0, Madd, Mneg, Mmul, MN⟩ := exists_ext_loc (S := Per.AinfP l)
    (Submonoid.powers (l : Per.Ainf l)) N (fun x => (rank_lt_alt x).1) Nadd Nneg Nmul (by
      rintro _ ⟨k, rfl⟩
      dsimp only
      rw [Npow, Nl]
      exact pow_ne_zero _ hr0.ne')
  have M1 : ∀ s ∈ Per.Acris0 l, M s ≤ 1 := by
    let B : Subalgebra (Per.Ainf l) (Per.AinfP l) :=
      { carrier := {s | M s ≤ 1}
        mul_mem' := fun {x y} hx hy => by
          have hx' : M x ≤ 1 := hx
          have hy' : M y ≤ 1 := hy
          have : M (x * y) ≤ 1 := by rw [Mmul]; exact mul_le_one₀ hx' (M0 y) hy'
          exact this
        add_mem' := fun {x y} hx hy => by
          have hx' : M x ≤ 1 := hx
          have hy' : M y ≤ 1 := hy
          exact (Madd x y).trans (max_le hx' hy')
        algebraMap_mem' := fun y => by
          have : M (algebraMap (Per.Ainf l) (Per.AinfP l) y) ≤ 1 := by rw [MN]; exact (rank_lt_alt y).2
          exact this }
    have hB : Per.Acris0 l ≤ B := by
      refine GlobalTheory.RingIface.Acris0_le_of_dividedPowers l B fun x n y hx h => ?_
      have h1 := congrArg M h
      rw [Mmul, ← map_natCast (algebraMap (Per.Ainf l) (Per.AinfP l)), ← map_pow, MN, MN, Npow] at h1
      have h2 := pow_le_factorial l N rank_lt_alt N1 Nadd Nmul (by rw [Nl]; exact hr1) n
      rw [Nl] at h2
      have h3 : N x ^ n ≤ r ^ n := pow_le_pow_left₀ (rank_lt_alt x).1 (Nker x hx) n
      have h4 : 0 < r ^ n := pow_pos hr0 n
      have h6 : M y ≤ 1 := by
        by_contra h5
        push Not at h5
        nlinarith
      exact h6
    exact fun s hs => hB hs
  obtain ⟨-, -, hd, hv⟩ := acris_basic l
  obtain ⟨Q, Q01, Qadd, Qneg, Qmul, QM⟩ := exists_ext_compl
    (algebraMap (Per.Acris0 l) (Per.Acris l)) l (fun s : Per.Acris0 l => M (s : Per.AinfP l))
    (fun s => ⟨M0 _, M1 _ s.2⟩) (fun x y => Madd _ _) (fun x => Mneg _) (fun x y => Mmul _ _)
    (by
      have : ((l : Per.Acris0 l) : Per.AinfP l) = algebraMap (Per.Ainf l) (Per.AinfP l) l := by simp
      rw [this, MN, Nl]
      exact hr1) hd (fun s k => (hv s k).1)
  refine ⟨Q, Q01, Qadd, Qneg, Qmul, fun x => ?_⟩
  have h : algebraMap (Per.Ainf l) (Per.Acris l) x =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) :=
    GlobalTheory.RingIface.tower l x
  rw [h, QM, Subalgebra.coe_algebraMap, MN, hN]

end GlobalTheory.GaussExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcrisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gauss_norm_extension_acris : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ), (l : ℝ)⁻¹ ≤ r → r < 1 → ∃ N : Per.Acris l → ℝ, (∀ x, 0 ≤ N x ∧ N x ≤ 1) ∧ (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ (∀ x, N (-x) = N x) ∧ (∀ x y, N (x * y) = N x * N y) ∧ ∀ a : Per.Ainf l, N (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n := by
  first | exact @GlobalTheory.GaussExt.exists_gauss_acris | exact GlobalTheory.GaussExt.exists_gauss_acris | (intros; apply GlobalTheory.GaussExt.exists_gauss_acris <;> assumption)
end
