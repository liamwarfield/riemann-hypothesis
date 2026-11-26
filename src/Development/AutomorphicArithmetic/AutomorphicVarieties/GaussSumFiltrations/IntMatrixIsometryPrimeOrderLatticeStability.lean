module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IntMatrixIsometryPrimeOrderLatticeStability
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.IsoP

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem pow_eq_one {p : ℕ} {S : Matrix κ κ ℤ} (h : ∑ i ∈ Finset.range p, S ^ i = 0) : S ^ p = 1 := by
  have := geom_sum_mul S p
  rw [h, zero_mul] at this
  exact (sub_eq_zero.mp this.symm)

theorem map_pow_eq (S : Matrix κ κ ℤ) (n : ℕ) : (S.map (Int.cast : ℤ → F)) ^ n = (S ^ n).map (Int.cast : ℤ → F) := by
  show ((Int.castRingHom F).mapMatrix S) ^ n = (Int.castRingHom F).mapMatrix (S ^ n)
  rw [map_pow]

theorem iter_eq (A : Matrix κ κ F) (n : ℕ) (x : κ → F) : (fun x => A *ᵥ x)^[n] x = (A ^ n) *ᵥ x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', Matrix.mulVec_mulVec]

theorem mem_LL (x : κ → F) : x ∈ LL F κ ↔ ∀ i, x i ∈ integralClosure ℤ F := by
  simp [LL, AddSubgroup.mem_pi]

theorem mulVec_LL (M : Matrix κ κ ℤ) {x : κ → F} (hx : x ∈ LL F κ) : (M.map (Int.cast : ℤ → F)) *ᵥ x ∈ LL F κ := by
  rw [mem_LL] at hx ⊢
  intro i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (hx j)

theorem mulVec_aL (M : Matrix κ κ ℤ) (a : F) {x : κ → F} (hx : x ∈ aL κ a) : (M.map (Int.cast : ℤ → F)) *ᵥ x ∈ aL κ a := by
  simp only [aL, AddSubgroup.mem_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨_, mulVec_LL M hy, ?_⟩
  simp [Matrix.mulVec_smul]

theorem pow_mulVec_fix (A : Matrix κ κ F) {x : κ → F} (hx : A *ᵥ x = x) (n : ℕ) : (A ^ n) *ᵥ x = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hx, ih]

theorem prime_not_dvd_of_neg_one_pow_mul_modEq_one {p : ℕ} (hp : p.Prime) {t : ℕ} {k : ℕ} (h : (-1) ^ k * (t : ℤ) ≡ 1 [ZMOD p]) : ¬ (p : ℤ) ∣ t := by
  intro hd
  have h2 := Int.modEq_iff_dvd.mp h
  have h3 : (p : ℤ) ∣ 1 := by
    have h4 := dvd_add h2 (dvd_mul_of_dvd_right hd ((-1) ^ k))
    simpa using h4
  have h5 : p ∣ 1 := by exact_mod_cast h3
  exact hp.not_dvd_one h5

private theorem sum_pow_map_intCast_eq_zero {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]
    {p : ℕ} {S : Matrix κ κ ℤ} (cyc : ∑ i ∈ Finset.range p, S ^ i = 0) :
    ∑ i ∈ Finset.range p, (S.map (Int.cast : ℤ → F)) ^ i = 0 := by
  simp only [map_pow_eq]
  have e := congrArg (Int.castRingHom F).mapMatrix cyc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at e
  exact e

theorem isometry_order_p : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → (∀ x y : κ → F, BF G ((S.map (Int.cast : ℤ → F)) *ᵥ x) ((S.map (Int.cast : ℤ → F)) *ᵥ y) = BF G x y ∧ QF G ((S.map (Int.cast : ℤ → F)) *ᵥ x) = QF G x) ∧ (∀ x : κ → F, (fun x => (S.map (Int.cast : ℤ → F)) *ᵥ x)^[p] x = x ∧ ((S.map (Int.cast : ℤ → F)) *ᵥ x = x → x = 0) ∧ ((S.map (Int.cast : ℤ → F)) *ᵥ x ∈ dualL F G ↔ x ∈ dualL F G) ∧ ∀ a : F, ((S.map (Int.cast : ℤ → F)) *ᵥ x ∈ aL κ a ↔ x ∈ aL κ a)) ∧ (∀ (N : ℕ) (x : κ → F), 0 < N → N.Coprime p → x ∈ aL κ (N : F)⁻¹ → (S.map (Int.cast : ℤ → F)) *ᵥ x - x ∈ aL κ (N : F) → x ∈ aL κ (N : F)) ∧ ¬ (p : ℤ) ∣ t := by
  intro F _ _ p hp κ _ _ G S t hL
  obtain ⟨_, _, iso, cyc, _, cong⟩ := hL
  have hφ : ∀ M : Matrix κ κ ℤ, M.map (Int.cast : ℤ → F) = (Int.castRingHom F).mapMatrix M := fun _ => rfl
  have hsum0 := sum_pow_map_intCast_eq_zero (F := F) cyc
  set S' : Matrix κ κ F := S.map (Int.cast : ℤ → F) with hS'
  have hpow : S' ^ p = 1 := by
    rw [hS', map_pow_eq, pow_eq_one cyc]
    simp
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  have hinv : ∀ y : κ → F, S' *ᵥ ((S ^ (p - 1)).map (Int.cast : ℤ → F) *ᵥ y) = y := by
    intro y
    rw [← map_pow_eq, Matrix.mulVec_mulVec, ← pow_succ', hp1, hpow, Matrix.one_mulVec]
  have hinv' : ∀ y : κ → F, (S ^ (p - 1)).map (Int.cast : ℤ → F) *ᵥ (S' *ᵥ y) = y := by
    intro y
    rw [← map_pow_eq, Matrix.mulVec_mulVec, ← pow_succ, hp1, hpow, Matrix.one_mulVec]
  have hsum : ∑ i ∈ Finset.range p, S' ^ i = 0 := hsum0
  have hBF : ∀ x y : κ → F, BF G (S' *ᵥ x) (S' *ᵥ y) = BF G x y := by
    intro x y
    have key : S'ᵀ * G.map (Int.cast : ℤ → F) * S' = G.map (Int.cast : ℤ → F) := by
      rw [hS', ← Matrix.transpose_map]
      simp only [hφ]
      rw [← map_mul, ← map_mul, iso]
    unfold BF
    rw [← Matrix.vecMul_transpose S' x, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, key]
  have memD : ∀ y : κ → F, y ∈ dualL F G ↔ ∀ l ∈ LL F κ, ∃ n : ℤ, Algebra.trace ℚ F (BF G y l) = n :=
    fun _ => Iff.rfl
  refine ⟨fun x y => ⟨hBF x y, ?_⟩, fun x => ⟨?_, ?_, ?_, ?_⟩, ?_, prime_not_dvd_of_neg_one_pow_mul_modEq_one hp cong⟩
  · unfold QF
    rw [hBF]
  · rw [iter_eq, hpow, Matrix.one_mulVec]
  · intro hx
    have e : ∑ i ∈ Finset.range p, S' ^ i *ᵥ x = 0 := by
      rw [← Matrix.sum_mulVec, hsum, Matrix.zero_mulVec]
    simp only [pow_mulVec_fix S' hx, Finset.sum_const, Finset.card_range] at e
    rw [← Nat.cast_smul_eq_nsmul F] at e
    have hp0 : (p : F) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    exact (smul_eq_zero.mp e).resolve_left hp0
  · rw [memD, memD]
    constructor
    · intro h l hl
      have h' := h _ (mulVec_LL S hl)
      rwa [hBF] at h'
    · intro h l hl
      have h' := h _ (mulVec_LL (S ^ (p - 1)) hl)
      rwa [← hBF, hinv] at h'
  · intro a
    constructor
    · intro h
      have h' := mulVec_aL (S ^ (p - 1)) a h
      rwa [hinv'] at h'
    · intro h
      exact mulVec_aL S a h
  · intro N x hN hcop hx hz
    have hstep : ∀ i : ℕ, S' ^ i *ᵥ x - x ∈ aL κ (N : F) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have e : S' ^ (i + 1) *ᵥ x - x = S' *ᵥ (S' ^ i *ᵥ x - x) + (S' *ᵥ x - x) := by
          rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
          abel
        rw [e]
        exact add_mem (mulVec_aL S _ ih) hz
    have hpx : (p : F) • x ∈ aL κ (N : F) := by
      have h0 : ∑ i ∈ Finset.range p, (S' ^ i *ᵥ x - x) = -((p : F) • x) := by
        rw [Finset.sum_sub_distrib, ← Matrix.sum_mulVec, hsum, Matrix.zero_mulVec, Finset.sum_const,
          Finset.card_range, zero_sub, Nat.cast_smul_eq_nsmul]
      have hs := AddSubgroup.sum_mem (aL κ (N : F)) (t := Finset.range p) (fun i _ => hstep i)
      rw [h0] at hs
      exact neg_mem_iff.mp hs
    have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    have hNx : (N : F) ^ 2 • x ∈ aL κ (N : F) := by
      simp only [aL, AddSubgroup.mem_map] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨y, hy, ?_⟩
      simp only [DistribSMul.toAddMonoidHom_apply, smul_smul]
      rw [pow_two, mul_assoc, mul_inv_cancel₀ hN0, mul_one]
    obtain ⟨u, v, huv⟩ : IsCoprime (p : ℤ) ((N : ℤ) ^ 2) := by
      have hc : Nat.Coprime p (N ^ 2) := Nat.Coprime.pow_right 2 hcop.symm
      exact_mod_cast Nat.isCoprime_iff_coprime.mpr hc
    have hx' : x = u • ((p : F) • x) + v • ((N : F) ^ 2 • x) := by
      rw [← Int.cast_smul_eq_zsmul F, ← Int.cast_smul_eq_zsmul F, smul_smul, smul_smul, ← add_smul]
      have e : (u : F) * p + (v : F) * (N : F) ^ 2 = 1 := by exact_mod_cast huv
      rw [e, one_smul]
    rw [hx']
    exact add_mem (zsmul_mem hpx u) (zsmul_mem hNx v)

end GlobalTheory.HilbertThetaSeries.IsoP

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intMatrix_isometry_prime_order_lattice_stability : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → (∀ x y : κ → F, BF G ((S.map (Int.cast : ℤ → F)) *ᵥ x) ((S.map (Int.cast : ℤ → F)) *ᵥ y) = BF G x y ∧ QF G ((S.map (Int.cast : ℤ → F)) *ᵥ x) = QF G x) ∧ (∀ x : κ → F, (fun x => (S.map (Int.cast : ℤ → F)) *ᵥ x)^[p] x = x ∧ ((S.map (Int.cast : ℤ → F)) *ᵥ x = x → x = 0) ∧ ((S.map (Int.cast : ℤ → F)) *ᵥ x ∈ dualL F G ↔ x ∈ dualL F G) ∧ ∀ a : F, ((S.map (Int.cast : ℤ → F)) *ᵥ x ∈ aL κ a ↔ x ∈ aL κ a)) ∧ (∀ (N : ℕ) (x : κ → F), 0 < N → N.Coprime p → x ∈ aL κ (N : F)⁻¹ → (S.map (Int.cast : ℤ → F)) *ᵥ x - x ∈ aL κ (N : F) → x ∈ aL κ (N : F)) ∧ ¬ (p : ℤ) ∣ t := by
  first | exact @GlobalTheory.HilbertThetaSeries.IsoP.isometry_order_p | exact GlobalTheory.HilbertThetaSeries.IsoP.isometry_order_p | (intros; apply GlobalTheory.HilbertThetaSeries.IsoP.isometry_order_p <;> assumption)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPosGramQuadFormTotallyPositiveProperness
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.TPos

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem reAt_eq (v : InfinitePlace F) (x : F) :
    reAt v x = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  unfold reAt
  have h := InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x
  rw [← h, Complex.ofReal_re]

theorem abs_reAt (v : InfinitePlace F) (x : F) : |reAt v x| = v x := by
  rw [reAt_eq, ← InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal v), Real.norm_eq_abs]

theorem reAt_QF {κ : Type} [Fintype κ] (G : Matrix κ κ ℤ) (x : κ → F) (v : InfinitePlace F) :
    reAt v (QF G x) =
      (fun i => reAt v (x i)) ⬝ᵥ (G.map (Int.cast : ℤ → ℝ)) *ᵥ (fun i => reAt v (x i)) / 2 := by
  set φ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) with hφ
  have hx : (fun i => reAt v (x i)) = φ ∘ x := by
    funext i
    simp [reAt_eq, hφ]
  have hG : (G.map (Int.cast : ℤ → ℝ)) = (G.map (Int.cast : ℤ → F)).map φ := by
    ext i j
    simp
  rw [hx, hG, reAt_eq, ← hφ]
  unfold QF BF
  rw [map_div₀, map_ofNat, RingHom.map_dotProduct]
  congr 2
  funext i
  exact RingHom.map_mulVec φ _ x i

theorem posDef_lower {κ : Type} [Fintype κ] (M : Matrix κ κ ℝ) (hM : M.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : κ → ℝ, c * ∑ i, y i ^ 2 ≤ y ⬝ᵥ M *ᵥ y := by
  classical
  rcases isEmpty_or_nonempty κ with hκ | ⟨⟨i0⟩⟩
  · refine ⟨1, one_pos, fun y => ?_⟩
    simp [dotProduct]
  set f : (κ → ℝ) → ℝ := fun y => y ⬝ᵥ M *ᵥ y with hf
  have hfc : Continuous f := by
    simp only [hf, dotProduct, Matrix.mulVec]
    fun_prop
  have hpos : ∀ y : κ → ℝ, y ≠ 0 → 0 < f y := by
    intro y hy
    have := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hy
    simpa [hf] using this
  set S : Set (κ → ℝ) := {y | ∑ i, y i ^ 2 = 1} with hS
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_eq (by fun_prop) continuous_const
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, fun y hy => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs]
      have h1 : y i ^ 2 ≤ ∑ j, y j ^ 2 :=
        Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [show ∑ j, y j ^ 2 = 1 from hy] at h1
      exact (sq_le_one_iff_abs_le_one _).mp h1
  have hSn : S.Nonempty := ⟨Pi.single i0 1, by simp [hS, Pi.single_apply]⟩
  obtain ⟨y0, hy0S, hmin⟩ := hSc.exists_isMinOn hSn hfc.continuousOn
  have hy0 : y0 ≠ 0 := by
    rintro rfl
    simp [hS] at hy0S
  refine ⟨f y0, hpos y0 hy0, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    simp
  set s := ∑ i, y i ^ 2 with hs
  have hs0 : 0 < s := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    have h1 : y i ^ 2 ≤ s :=
      Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hi' : y i ≠ 0 := by simpa using hi
    have : 0 < y i ^ 2 := by positivity
    linarith
  set t := Real.sqrt s with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr hs0
  have htt : t ^ 2 = s := Real.sq_sqrt hs0.le
  have hz : t⁻¹ • y ∈ S := by
    simp only [hS, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [← Finset.mul_sum, ← hs, inv_pow, htt, inv_mul_cancel₀ hs0.ne']
  have hfz : f (t⁻¹ • y) = (t ^ 2)⁻¹ * f y := by
    simp only [hf, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have := hmin hz
  simp only [Set.mem_setOf_eq] at this
  rw [hfz, htt] at this
  have h2 := mul_le_mul_of_nonneg_left this hs0.le
  rw [← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul] at h2
  linarith [mul_comm s (f y0)]

end GlobalTheory.TPos


open GlobalTheory.TPos in
theorem GlobalTheory.HilbertThetaSeries.qf_totPos_proper : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ]
    (G : Matrix κ κ ℤ), EvenPos G → (∀ x : κ → F, x ≠ 0 → TP (QF G x)) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ (x : κ → F) v, c * ∑ i, reAt v (x i) ^ 2 ≤ reAt v (QF G x)) ∧
      ∀ (a ξ : F), {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}.Finite := by
  intro F _ _ _ κ _ _ G hG
  have hM : (G.map (Int.cast : ℤ → ℝ)).PosDef := hG.1
  obtain ⟨c, hc, hcb⟩ := posDef_lower _ hM
  have key : ∀ (x : κ → F) v, (c / 2) * ∑ i, reAt v (x i) ^ 2 ≤ reAt v (QF G x) := by
    intro x v
    rw [reAt_QF]
    have := hcb (fun i => reAt v (x i))
    linarith
  have hinj : ∀ (v : InfinitePlace F) (y : F), reAt v y = 0 → y = 0 := by
    intro v y h
    rw [reAt_eq] at h
    exact (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)).injective (by simpa using h)
  refine ⟨?_, ⟨c / 2, by positivity, key⟩, ?_⟩
  · intro x hx v
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have hyi : reAt v (x i) ≠ 0 := fun h => hi (hinj v _ h)
    have h1 : reAt v (x i) ^ 2 ≤ ∑ j, reAt v (x j) ^ 2 :=
      Finset.single_le_sum (f := fun j => reAt v (x j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : 0 < reAt v (x i) ^ 2 := by positivity
    have h3 := mul_pos (half_pos hc) (lt_of_lt_of_le h2 h1)
    have := key x v
    linarith
  · intro a ξ
    by_cases ha : a = 0
    · apply (Set.finite_singleton (0 : κ → F)).subset
      rintro x ⟨hx, -⟩
      unfold aL at hx
      obtain ⟨z, -, rfl⟩ := AddSubgroup.mem_map.mp hx
      simp [ha]
    set B : ℝ := ∑ v : InfinitePlace F, Real.sqrt (reAt v ξ / (c / 2)) / v a with hB
    set T : Set F := {y : F | IsIntegral ℤ y ∧ ∀ φ : F →+* ℂ, ‖φ y‖ ≤ B} with hT
    have hTf : T.Finite := NumberField.Embeddings.finite_of_norm_le F ℂ B
    apply ((Set.Finite.pi (t := fun _ : κ => T) (fun _ => hTf)).image (fun z => a • z)).subset
    rintro x ⟨hx, hxξ⟩
    unfold aL at hx
    obtain ⟨z, hz, rfl⟩ := AddSubgroup.mem_map.mp hx
    refine ⟨z, fun i _ => ?_, rfl⟩
    unfold LL at hz
    have hzi := (AddSubgroup.mem_pi _).mp hz i (Set.mem_univ _)
    refine ⟨hzi, fun φ => ?_⟩
    rw [← NumberField.InfinitePlace.apply]
    set w := InfinitePlace.mk φ
    have hxi : (DistribSMul.toAddMonoidHom (κ → F) a z) i = a * z i := by simp
    have hwa : 0 < w a := (InfinitePlace.pos_iff).mpr ha
    have hk := key (DistribSMul.toAddMonoidHom (κ → F) a z) w
    rw [hxξ] at hk
    have h1 : reAt w ((DistribSMul.toAddMonoidHom (κ → F) a z) i) ^ 2 ≤
        ∑ j, reAt w ((DistribSMul.toAddMonoidHom (κ → F) a z) j) ^ 2 :=
      Finset.single_le_sum (f := fun j => reAt w ((DistribSMul.toAddMonoidHom (κ → F) a z) j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : reAt w ((DistribSMul.toAddMonoidHom (κ → F) a z) i) ^ 2 ≤ reAt w ξ / (c / 2) := by
      rw [le_div_iff₀ (half_pos hc)]
      nlinarith
    have h3 := Real.abs_le_sqrt h2
    rw [abs_reAt, hxi, map_mul] at h3
    have h4 : w (z i) ≤ Real.sqrt (reAt w ξ / (c / 2)) / w a := by
      rw [le_div_iff₀ hwa]
      linarith [mul_comm (w a) (w (z i))]
    refine h4.trans ?_
    exact Finset.single_le_sum (f := fun v : InfinitePlace F => Real.sqrt (reAt v ξ / (c / 2)) / v a)
      (fun v _ => div_nonneg (Real.sqrt_nonneg _) (apply_nonneg v a)) (Finset.mem_univ w)

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenPosGram_quadForm_totallyPositive_properness : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → (∀ x : κ → F, x ≠ 0 → TP (QF G x)) ∧ (∃ c : ℝ, 0 < c ∧ ∀ (x : κ → F) v, c * ∑ i, reAt v (x i) ^ 2 ≤ reAt v (QF G x)) ∧ ∀ (a ξ : F), {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}.Finite := by
  first | exact @GlobalTheory.HilbertThetaSeries.qf_totPos_proper | exact GlobalTheory.HilbertThetaSeries.qf_totPos_proper | (intros; apply GlobalTheory.HilbertThetaSeries.qf_totPos_proper <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.GenByTranslationsInversions
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.GeneratorMatrix

theorem matId {F : Type} [Field F] (a b c d δ τ e s : F) (hδ : δ ≠ 0) (hs : s ≠ 0) (he : e ≠ 0)
    (hc : c = s - τ * δ * a) (hdet : a * d - b * c = e) :
    !![a, b; c, d] = !![0, -δ⁻¹; δ, 0] * !![1, τ / δ; 0, 1] * !![0, -(-δ)⁻¹; -δ, 0] * !![1, a / s; 0, 1]
      * !![0, -(s / e)⁻¹; s / e, 0] * !![1, (d + τ * δ * b) * e / s; 0, 1] * !![e, 0; 0, 1] := by
  subst hc
  simp only [Matrix.mul_fin_two]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> field_simp
  all_goals first | ring1 | linear_combination -hdet | linear_combination δ * τ * hdet

variable {F : Type} [Field F] [NumberField F]

theorem exists_place (p : ℕ) (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal :=
  _root_.UpperTheory.Reformulated.B.Qk8.exists_place p hp

theorem ne_zero_of_pUnit {p : ℕ} {w : HeightOneSpectrum (𝓞 F)} (hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) {x : F}
    (h : PUnit p x) : x ≠ 0 := by
  intro hx; have := h w hw; rw [hx, map_zero] at this; exact zero_ne_one this

theorem val_wm (c : Fˣ) : ((wm c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, -(c : F)⁻¹; (c : F), 0] := by
  simp [wm]

theorem val_aff (y : Fˣ) (x : F) : ((aff y x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(y : F), x; 0, 1] := rfl

end GlobalTheory.HilbertThetaSeries.GeneratorMatrix

namespace GlobalTheory.HilbertThetaSeries


open GlobalTheory.HilbertThetaSeries.GeneratorMatrix in
theorem gen_by_translations_inversions : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → ∀ γ : GL (Fin 2) F, InG p δ γ → ∃ (b₁ b₂ b₃ : F) (c₁ c₂ c₃ ε : Fˣ), PInt p (δ * b₁) ∧ PInt p (δ * b₂) ∧ PInt p (δ * b₃) ∧ PUnit p (c₁ / δ) ∧ PUnit p (c₂ / δ) ∧ PUnit p (c₃ / δ) ∧ TP (ε : F) ∧ γ = wm c₁ * aff 1 b₁ * wm c₂ * aff 1 b₂ * wm c₃ * aff 1 b₃ * aff ε 0 := by
  intro F _ _ _ p hp δ hδ γ hγ
  classical
  obtain ⟨hA, hB, hC, hD, hE, hT⟩ := hγ
  obtain ⟨w₀, hw₀⟩ := exists_place (F := F) p hp
  have hδ0 : δ ≠ 0 := by
    intro h; have := hδ w₀ hw₀; rw [h, map_zero] at this; exact WithZero.exp_ne_zero this.symm
  have hdet : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = γ.val.det := (Matrix.det_fin_two _).symm
  have he0 : γ.val.det ≠ 0 := ne_zero_of_pUnit hw₀ hE
  have hI : Ideal.span {((p : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  set S := (Ideal.finite_factors hI).toFinset with hS
  have hmem : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → w ∈ S := by
    intro w hw
    rw [hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
    exact hw
  obtain ⟨τ, hτ⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun w => w.asIdeal) (fun _ => 1)
    (fun w _ => w.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun w => if w.1.valuation F (γ.val 1 0 / δ) = 1 then 0 else 1)
  set a := γ.val 0 0 with ha
  set b := γ.val 0 1 with hb
  set c := γ.val 1 0 with hc
  set d := γ.val 1 1 with hd
  set e := γ.val.det with he
  set t : F := algebraMap (𝓞 F) F τ with ht
  set s := c + t * δ * a with hs
  have hsd : s / δ = c / δ + t * a := by rw [hs]; field_simp
  have hu : PUnit p (s / δ) := by
    intro w hw
    have hτw := hτ w (hmem w hw)
    simp only [pow_one] at hτw
    rw [hsd]
    by_cases h1 : w.valuation F (c / δ) = 1
    · rw [if_pos h1, sub_zero] at hτw
      have htlt : w.valuation F t < 1 := (w.valuation_lt_one_iff_mem τ).mpr hτw
      have : w.valuation F (t * a) < 1 := by
        rw [map_mul]
        calc w.valuation F t * w.valuation F a ≤ w.valuation F t * 1 := mul_le_mul' le_rfl (hA w hw)
          _ < 1 := by rw [mul_one]; exact htlt
      rw [Valuation.map_add_eq_of_lt_left _ (h1 ▸ this), h1]
    · rw [if_neg h1] at hτw
      have hclt : w.valuation F (c / δ) < 1 := lt_of_le_of_ne (hC w hw) h1
      have hav : w.valuation F a = 1 := by
        by_contra hne
        have halt : w.valuation F a < 1 := lt_of_le_of_ne (hA w hw) hne
        have hE' := hE w hw
        have hx : e = a * d - (δ * b) * (c / δ) := by rw [← hdet]; field_simp
        have h1' : w.valuation F (a * d) < 1 := by
          rw [map_mul]
          calc w.valuation F a * w.valuation F d ≤ w.valuation F a * 1 := mul_le_mul' le_rfl (hD w hw)
            _ < 1 := by rw [mul_one]; exact halt
        have h2' : w.valuation F ((δ * b) * (c / δ)) < 1 := by
          rw [map_mul]
          calc w.valuation F (δ * b) * w.valuation F (c / δ) ≤ 1 * w.valuation F (c / δ) := mul_le_mul' (hB w hw) le_rfl
            _ < 1 := by rw [one_mul]; exact hclt
        have : w.valuation F e < 1 := by
          rw [hx]; exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1' h2')
        rw [hE'] at this; exact lt_irrefl _ this
      have htm : w.valuation F (t - 1) < 1 := by
        have := (w.valuation_lt_one_iff_mem (K := F) (τ - 1)).mpr hτw
        simpa [ht] using this
      have htv : w.valuation F t = 1 := by
        have : t = 1 + (t - 1) := by ring
        rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact htm), map_one]
      have hta : w.valuation F (t * a) = 1 := by rw [map_mul, htv, hav, mul_one]
      rw [Valuation.map_add_eq_of_lt_right _ (hta ▸ hclt), hta]
  have hs0 : s ≠ 0 := by
    intro h0; exact ne_zero_of_pUnit hw₀ hu (by rw [h0, zero_div])
  refine ⟨t / δ, a / s, (d + t * δ * b) * e / s, Units.mk0 δ hδ0, -Units.mk0 δ hδ0,
    Units.mk0 (s / e) (div_ne_zero hs0 he0), Units.mk0 e he0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw; rw [mul_div_cancel₀ _ hδ0]; exact w.valuation_le_one τ
  · intro w hw
    have : δ * (a / s) = a / (s / δ) := by field_simp
    rw [this, map_div₀, hu w hw, div_one]; exact hA w hw
  · intro w hw
    have : δ * ((d + t * δ * b) * e / s) = (d + t * (δ * b)) * e / (s / δ) := by field_simp
    rw [this, map_div₀, hu w hw, div_one, map_mul, hE w hw, mul_one]
    refine Valuation.map_add_le _ (hD w hw) ?_
    rw [map_mul]
    calc w.valuation F t * w.valuation F (δ * b) ≤ 1 * 1 :=
          mul_le_mul' (w.valuation_le_one τ) (hB w hw)
      _ = 1 := one_mul 1
  · intro w hw; rw [Units.val_mk0, div_self hδ0, map_one]
  · intro w hw; rw [Units.val_neg, Units.val_mk0, neg_div, div_self hδ0, Valuation.map_neg, map_one]
  · intro w hw
    have : s / e / δ = s / δ / e := by ring
    rw [Units.val_mk0, this, map_div₀, hu w hw, hE w hw, div_one]
  · rw [Units.val_mk0]; exact hT
  · refine Units.ext ?_
    simp only [Units.val_mul, val_wm, val_aff, Units.val_neg, Units.val_mk0, Units.val_one]
    rw [Matrix.eta_fin_two (γ : Matrix (Fin 2) (Fin 2) F)]
    exact matId a b c d δ t e s hδ0 hs0 he0 (by rw [hs]; ring) hdet

end GlobalTheory.HilbertThetaSeries
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.FiniteNarrowIdeleClassesAndUnitsModSquares
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.NarrowCls

theorem exists_finset_mod_sq {G : Type} [CommGroup G] [Group.FG G] :
    ∃ E : Finset G, ∀ g : G, ∃ e ∈ E, ∃ h : G, g = e * h ^ 2 := by
  classical
  let H : Subgroup G := (powMonoidHom 2 : G →* G).range
  have hfin : Finite (G ⧸ H) := by
    apply CommGroup.finite_of_fg_torsion
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    refine (isOfFinOrder_iff_pow_eq_one).2 ⟨2, by norm_num, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨g, rfl⟩
  haveI := Fintype.ofFinite (G ⧸ H)
  refine ⟨Finset.univ.image (fun q : G ⧸ H => q.out), fun g => ?_⟩
  refine ⟨(g : G ⧸ H).out, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  have h1 : ((g : G ⧸ H).out : G ⧸ H) = (g : G ⧸ H) := Quotient.out_eq' _
  rw [QuotientGroup.eq] at h1
  obtain ⟨h, hh⟩ := h1
  refine ⟨h, ?_⟩
  simp only [powMonoidHom_apply] at hh
  rw [hh, mul_inv_cancel_left]

variable {F : Type} [Field F] [NumberField F]

def finIdele : (Af F)ˣ →* Ideles F :=
  Units.map
    { toFun := fun x => (((1 : InfiniteAdeleRing F), x) : AdeleRing (𝓞 F) F)
      map_one' := rfl
      map_mul' := fun x y => Prod.ext (mul_one 1).symm rfl }

def finClass : (Af F)ˣ →* ClassGroup (𝓞 F) := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf F).comp finIdele

theorem eq_of_finClass_eq_one (z : (Af F)ˣ) (hz : finClass z = 1) :
    ∃ (k : Fˣ) (u : (Af F)ˣ), (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) ∧
      z = Units.map (algebraMap F (Af F)).toMonoidHom k * u := by
  obtain ⟨k, u', hu', he⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff F (finIdele z)).1 hz
  have hsnd := congrArg (ReciprocityTheory.Neutral.Bridge.HCFR.sndU F) he
  rw [map_mul] at hsnd
  have hinv : ReciprocityTheory.Neutral.Bridge.HCFR.sndU F u' * ReciprocityTheory.Neutral.Bridge.HCFR.sndU F u'⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : ReciprocityTheory.Neutral.Bridge.HCFR.sndU F u'⁻¹ * ReciprocityTheory.Neutral.Bridge.HCFR.sndU F u' = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  refine ⟨k, ⟨_, _, hinv, hinv'⟩, ?_, ?_⟩
  · intro w
    exact (ReciprocityTheory.Neutral.Bridge.HCFR.rayUnits_top_iff F u').1 hu' w
  · ext1
    exact hsnd

variable [IsTotallyReal F]

theorem reAt_eq (v : InfinitePlace F) (x : F) :
    reAt v x = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply]
  exact Complex.ofReal_re _


open Classical in
def sgn (k : Fˣ) : InfinitePlace F → Bool := fun v => decide (0 < reAt v (k : F))

theorem tp_of_sgn_eq (k σ : Fˣ) (h : sgn k = sgn σ) : TP ((k * σ⁻¹ : Fˣ) : F) := by
  intro v
  have hv := congrFun h v
  simp only [sgn, decide_eq_decide] at hv
  rw [reAt_eq] at hv ⊢
  set e := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)
  have hk : e (k : F) ≠ 0 := (map_ne_zero e).2 k.ne_zero
  have hs : e (σ : F) ≠ 0 := (map_ne_zero e).2 σ.ne_zero
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  rcases lt_or_gt_of_ne hs with h1 | h1
  · have h2 : e (k : F) < 0 := by
      rcases lt_or_gt_of_ne hk with h3 | h3
      · exact h3
      · exact absurd (hv.1 h3) (not_lt.2 h1.le)
    exact mul_pos_of_neg_of_neg h2 (inv_lt_zero.2 h1)
  · exact mul_pos (hv.2 h1) (inv_pos.2 h1)

theorem narrowClass_unitsSq_finite : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
    (∃ Y : Finset (Af F)ˣ, ∀ z : (Af F)ˣ, ∃ y ∈ Y, ∃ (ξ : Fˣ) (u : (Af F)ˣ), TP (ξ : F) ∧
      (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) ∧ z = Units.map (algebraMap F (Af F)).toMonoidHom ξ * y * u) ∧
    ∃ E : Finset (𝓞 F)ˣ, ∀ ε : (𝓞 F)ˣ, ∃ e ∈ E, ∃ η : (𝓞 F)ˣ, ε = e * η ^ 2 := by
  intro F _ _ _
  classical
  refine ⟨?_, ?_⟩
  · let Y0 : Finset (Af F)ˣ := Finset.univ.image
      (fun c : ClassGroup (𝓞 F) => if h : ∃ y, finClass y = c then h.choose else 1)
    let S : Finset Fˣ := Finset.univ.image
      (fun b : InfinitePlace F → Bool => if h : ∃ σ : Fˣ, sgn σ = b then h.choose else 1)
    let ι := Units.map (algebraMap F (Af F)).toMonoidHom
    refine ⟨(S ×ˢ Y0).image (fun p => ι p.1 * p.2), fun z => ?_⟩
    have hc : ∃ y, finClass y = finClass z := ⟨z, rfl⟩
    set y0 := hc.choose with hy0
    have hy0c : finClass y0 = finClass z := hc.choose_spec
    have hy0m : y0 ∈ Y0 := by
      refine Finset.mem_image.2 ⟨finClass z, Finset.mem_univ _, ?_⟩
      rw [dite_eq_left hc]
    obtain ⟨k, u, hu, hk⟩ := eq_of_finClass_eq_one (z * y0⁻¹) (by rw [map_mul, map_inv, hy0c, mul_inv_cancel])
    have hs : ∃ σ : Fˣ, sgn σ = sgn k := ⟨k, rfl⟩
    set σ := hs.choose with hσ
    have hσs : sgn σ = sgn k := hs.choose_spec
    have hσm : σ ∈ S := by
      refine Finset.mem_image.2 ⟨sgn k, Finset.mem_univ _, ?_⟩
      rw [dite_eq_left hs]
    refine ⟨ι σ * y0, Finset.mem_image.2 ⟨(σ, y0), Finset.mem_product.2 ⟨hσm, hy0m⟩, rfl⟩,
      k * σ⁻¹, u, tp_of_sgn_eq k σ hσs.symm, hu, ?_⟩
    have hz : z = ι k * u * y0 := by rw [← hk, inv_mul_cancel_right]
    show z = ι (k * σ⁻¹) * (ι σ * y0) * u
    rw [← mul_assoc, ← map_mul, inv_mul_cancel_right, mul_right_comm]
    exact hz
  · haveI : Group.FG (𝓞 F)ˣ := Group.fg_iff_monoid_fg.2 inferInstance
    exact exists_finset_mod_sq

end GlobalTheory.HilbertThetaSeries.NarrowCls

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_narrowIdeleClasses_and_units_mod_squares : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], (∃ Y : Finset (Af F)ˣ, ∀ z : (Af F)ˣ, ∃ y ∈ Y, ∃ (ξ : Fˣ) (u : (Af F)ˣ), TP (ξ : F) ∧ (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) ∧ z = Units.map (algebraMap F (Af F)).toMonoidHom ξ * y * u) ∧ ∃ E : Finset (𝓞 F)ˣ, ∀ ε : (𝓞 F)ˣ, ∃ e ∈ E, ∃ η : (𝓞 F)ˣ, ε = e * η ^ 2 := by
  first | exact @GlobalTheory.HilbertThetaSeries.NarrowCls.narrowClass_unitsSq_finite | exact GlobalTheory.HilbertThetaSeries.NarrowCls.narrowClass_unitsSq_finite | (intros; apply GlobalTheory.HilbertThetaSeries.NarrowCls.narrowClass_unitsSq_finite <;> assumption)
end
end
