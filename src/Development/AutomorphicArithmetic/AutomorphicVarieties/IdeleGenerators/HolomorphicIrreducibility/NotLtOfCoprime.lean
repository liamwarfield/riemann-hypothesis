module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.TorsionOrderFrobenius.ContinuousKap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ChebQ

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.TorsionOrderFrobenius.IsFrobSq
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal UpperTheory.V.Base

private theorem pow_cong {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω} (ha : A.valuation a ≤ 1)
    (hb : A.valuation b ≤ 1) (h : A.valuation (a - b) < 1) (m : ℕ) : A.valuation (a ^ m - b ^ m) < 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show a ^ (m + 1) - b ^ (m + 1) = a ^ m * (a - b) + (a ^ m - b ^ m) * b by ring]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (pow_le_one' ha m)) h
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hb) ih

private theorem isFrob_sq {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] {A : ValuationSubring Ω}
    {q : ℕ} {g : G k Ω} (hg : IsFrob (F := k) A q g) : IsFrob (F := k) A (q ^ 2) (g * g) := by
  refine ⟨Subgroup.mul_mem _ hg.1 hg.1, fun x hx => ?_⟩
  have hgx : A.valuation (g x) ≤ 1 :=
    (A.valuation_le_one_iff _).2 ((apply_mem_iff_of_mem_Dec (F := k) hg.1 x).2 ((A.valuation_le_one_iff _).1 hx))
  have h1 := hg.2 _ hgx
  have h2 := pow_cong A hgx (b := x ^ q) (by rw [map_pow]; exact pow_le_one' hx _) (hg.2 x hx) q
  have h3 := Valuation.map_add_lt A.valuation h1 h2
  rw [sub_add_sub_cancel, ← pow_mul, ← sq] at h3
  rw [AlgEquiv.mul_apply]
  exact h3

theorem UpperTheory.V.Sd.Tw.inert :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω],
        Module.finrank ℚ K = 2 → ∀ (p : ℕ), p.Prime → ∀ (A : ValuationSubring Ω), A.valuation (p : Ω) < 1 →
        Ine (F := ℚ) A ≤ galOf ℚ K Ω → ∀ t : G ℚ Ω, IsFrob (F := ℚ) A p t → t ∉ galOf ℚ K Ω →
        ∃ w : HeightOneSpectrum (𝓞 K), IsPlaceOver A w ∧ w.asIdeal = Ideal.span {(p : 𝓞 K)} ∧
          ∀ s : G K Ω, galEmb ℚ K Ω s = t * t → IsFrob (F := K) A (normV w) s := by
  intro K Ω _ _ _ _ _ _ hK p hp A hA hI t ht htK
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  obtain ⟨h1, h2, h3, -⟩ := UpperTheory.V.Base.places K Ω p A
  obtain ⟨w, hw⟩ := h1 fun h => (h2 h).2 hA
  have hpw : (p : 𝓞 K) ∈ w.asIdeal := (h3 w hw).1 hA
  have hle : Ideal.span {(p : 𝓞 K)} ≤ w.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hpw
  have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, hK]
  have hn : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hq : normV w = p ^ 2 := by
    obtain ⟨j, hj, e⟩ := (Nat.dvd_prime_pow hp).1 (hN ▸ Ideal.absNorm_dvd_absNorm_of_le hle)
    interval_cases j
    · exact absurd (Ideal.absNorm_eq_one_iff.1 (by simpa using e)) w.isPrime.ne_top
    · exfalso
      obtain ⟨φ, hφ⟩ := ReciprocityTheory.Gal.exists_isFrob hw
      rw [hn, e, pow_one] at hφ
      have hφ' : IsFrob (F := ℚ) A p (galEmb ℚ K Ω φ) := ⟨hφ.1, hφ.2⟩
      have h := hI (inv_mul_mem_Ine_of_isFrob hφ' ht)
      exact htK (by simpa using (galOf ℚ K Ω).mul_mem (galEmb_mem ℚ K Ω φ) h)
    · rw [hn, e]
  refine ⟨w, hw, ?_, fun s hs => ?_⟩
  · obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
    have e := congrArg Ideal.absNorm hJ
    rw [map_mul, hN, ← hn, hq] at e
    have hJ1 : Ideal.absNorm J = 1 := by
      have := pow_pos hp.pos 2
      exact (Nat.mul_eq_left this.ne').1 e.symm
    rw [hJ, Ideal.absNorm_eq_one_iff.1 hJ1, Ideal.mul_top]
  · have h := isFrob_sq ht
    rw [← hs, ← hq] at h
    exact ⟨h.1, h.2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.TorsionOrderFrobenius.QuadMu
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Base

namespace UpperTheory.V.Sd.Tw

private def Fx {Ω : Type} [Field Ω] (s : Ω →+* Ω) (a : ℤ) : Prop := ∀ δ : Ω, δ ^ 2 = (a : Ω) → s δ = δ

section
variable {Ω : Type} [Field Ω] {s : Ω →+* Ω}

private theorem fx_of {a : ℤ} {x : Ω} (hx : x ^ 2 = (a : Ω)) (hs : s x = x) : Fx s a := by
  intro δ hδ
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hδ.trans hx.symm) with h | h
  · rw [h, hs]
  · rw [h, map_neg, hs]

private theorem fx_mul [IsAlgClosed Ω] {a b : ℤ} (ha : Fx s a) (hb : Fx s b) : Fx s (a * b) := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (a : Ω) two_pos
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (b : Ω) two_pos
  refine fx_of (x := α * β) ?_ ?_
  · rw [mul_pow, hα, hβ]
    push_cast
    ring
  · rw [map_mul, ha α hα, hb β hβ]

private theorem fx_one : Fx s 1 := fx_of (x := 1) (by simp) (map_one s)

private theorem fx_pow [IsAlgClosed Ω] {a : ℤ} (ha : Fx s a) (k : ℕ) : Fx s (a ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact fx_one
  | succ k ih =>
    rw [pow_succ]
    exact fx_mul ih ha

private theorem fx_four : Fx s 4 := by
  refine fx_of (x := 2) ?_ (map_ofNat s 2)
  push_cast
  norm_num

variable {M : ℕ}

private theorem fix_dvd (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) {n : ℕ} (hn : n ∣ M) {ζ : Ω} (hζ : ζ ^ n = 1) :
    s ζ = ζ := by
  obtain ⟨k, rfl⟩ := hn
  exact h ζ (by rw [pow_mul, hζ, one_pow])

private theorem fx_neg_one (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) (h4 : 4 ∣ M) : Fx s (-1) := by
  intro δ hδ
  apply fix_dvd h h4
  rw [show δ ^ 4 = (δ ^ 2) ^ 2 by ring, hδ]
  push_cast
  norm_num

private theorem fx_two [IsAlgClosed Ω] (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) (h8 : 8 ∣ M) : Fx s 2 := by
  intro δ hδ
  have hδ' : δ ^ 2 = 2 := by
    rw [hδ]
    push_cast
    rfl
  by_cases h2 : (2 : Ω) = 0
  · have : δ = 0 := by
      rw [h2] at hδ'
      exact pow_eq_zero_iff (two_ne_zero) |>.1 hδ'
    rw [this, map_zero]
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Ω) two_pos
  obtain ⟨t, ht⟩ : ∃ t : Ω, 2 * t = 1 := ⟨2⁻¹, mul_inv_cancel₀ h2⟩
  obtain ⟨η, hη⟩ : ∃ η : Ω, η = (1 + i) * δ * t := ⟨_, rfl⟩
  have hη2 : η ^ 2 = i := by
    rw [hη]
    linear_combination (1 + i) ^ 2 * t ^ 2 * hδ' + 2 * t ^ 2 * hi + i * (2 * t + 1) * ht
  have hsi : s i = i := by
    apply fix_dvd h h8
    rw [show i ^ 8 = (i ^ 2) ^ 4 by ring, hi]
    norm_num
  have hsη : s η = η := by
    apply fix_dvd h h8
    rw [show η ^ 8 = ((η ^ 2) ^ 2) ^ 2 by ring, hη2, hi]
    norm_num
  have hδη : δ = η * (1 - i) := by
    rw [hη]
    linear_combination (-δ) * ht + δ * t * hi
  rw [hδη, map_mul, map_sub, map_one, hsη, hsi]

private theorem fx_odd [IsAlgClosed Ω] [CharZero Ω] (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) (n : ℕ) :
    n % 2 = 1 → n ∣ M → ∃ a : ℤ, a % 4 = 1 ∧ a.natAbs = n ∧ Fx s a := by
  induction n using Nat.recOnMul with
  | zero =>
    intro h0
    simp at h0
  | one =>
    intro _ _
    exact ⟨1, rfl, rfl, fx_one⟩
  | prime p hp =>
    intro hodd hpM
    haveI := Fact.mk hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      simp at hodd
    haveI : NeZero ((p : ℕ) : Ω) := ⟨by exact_mod_cast hp.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
    obtain ⟨⟨x, hx⟩, hσ⟩ := UpperTheory.V.CF.gauss Ω p ζ hp2 hζ
    have hsζ : s ζ = ζ := fix_dvd h hpM hζ.pow_eq_one
    have hsx : s x = x := by
      have := (hσ x hx).2 s 1 (by rw [pow_one]; exact hsζ)
      simpa using this
    refine ⟨UpperTheory.V.CF.pStar p, ?_, ?_, fx_of hx hsx⟩
    · unfold UpperTheory.V.CF.pStar
      rcases Nat.even_or_odd (p / 2) with he | ho
      · rw [he.neg_one_pow, one_mul]
        obtain ⟨j, hj⟩ := he
        omega
      · rw [ho.neg_one_pow, neg_one_mul]
        obtain ⟨j, hj⟩ := ho
        omega
    · simp [UpperTheory.V.CF.pStar, Int.natAbs_mul, Int.natAbs_pow]
  | mul a b iha ihb =>
    intro hodd hab
    have ho := Nat.odd_mul.1 (Nat.odd_iff.2 hodd)
    obtain ⟨x, hx1, hx2, hx3⟩ := iha (Nat.odd_iff.1 ho.1) (dvd_trans (dvd_mul_right a b) hab)
    obtain ⟨y, hy1, hy2, hy3⟩ := ihb (Nat.odd_iff.1 ho.2) (dvd_trans (dvd_mul_left b a) hab)
    refine ⟨x * y, ?_, ?_, fx_mul hx3 hy3⟩
    · rw [Int.mul_emod, hx1, hy1]
      norm_num
    · rw [Int.natAbs_mul, hx2, hy2]

private theorem fx_disc [IsAlgClosed Ω] [CharZero Ω] {d : ℤ} (hd0 : d ≠ 0) (hd : d % 4 = 0 ∨ d % 4 = 1)
    (h : ∀ ζ : Ω, ζ ^ d.natAbs = 1 → s ζ = ζ) : Fx s d := by
  obtain ⟨k, m, hm, hdk⟩ := Nat.exists_eq_two_pow_mul_odd (Int.natAbs_ne_zero.2 hd0)
  obtain ⟨a, ha4, ham, hfa⟩ :=
    fx_odd h m (Nat.odd_iff.1 hm) (by rw [hdk]; exact dvd_mul_left m _)
  have hda : d = 2 ^ k * a ∨ d = -(2 ^ k * a) := by
    apply Int.natAbs_eq_natAbs_iff.1
    rw [Int.natAbs_mul, ham, hdk]
    simp
  have h4 : 2 ≤ k → 4 ∣ d.natAbs := fun hk => by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [hdk, pow_add]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by norm_num) _) _
  have hpk : 2 ≤ k → Fx s (2 ^ k) := fun hk => by
    rcases Nat.eq_or_lt_of_le hk with hk2 | hk3
    · rw [← hk2]
      have e : (2 : ℤ) ^ 2 = 4 := by norm_num
      rw [e]
      exact fx_four
    · apply fx_pow (fx_two h ?_)
      have h3 : 3 ≤ k := hk3
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h3
      rw [hdk, pow_add]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by norm_num) _) _
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · simp at hda
      rcases hda with rfl | rfl
      · exact hfa
      · omega
    · exfalso
      simp at hda
      omega
  · rcases hda with rfl | rfl
    · exact fx_mul (hpk hk) hfa
    · rw [neg_eq_neg_one_mul]
      exact fx_mul (fx_neg_one h (h4 hk)) (fx_mul (hpk hk) hfa)

end

private theorem exists_sq_sub_trace_mul_eq_rat_of_finrank_two {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (x : K) : ∃ r : ℚ, x ^ 2 - algebraMap ℚ K (Algebra.trace ℚ K x) * x = algebraMap ℚ K r := by
  classical
  let b := Module.finBasisOfFinrankEq ℚ K hK
  set M := Algebra.leftMulMatrix b x with hM
  have hnd : M.charpoly.natDegree = 2 := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have h2 : M.charpoly.coeff 2 = 1 := by
    have := (Matrix.charpoly_monic M).leadingCoeff
    rwa [Polynomial.leadingCoeff, hnd] at this
  have htr : Algebra.trace ℚ K x = -M.charpoly.coeff 1 := by
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_eq_neg_charpoly_coeff]
    rfl
  have hzero : Polynomial.aeval x M.charpoly = 0 := by
    apply Algebra.leftMulMatrix_injective b
    rw [← Polynomial.aeval_algHom_apply, map_zero]
    exact Matrix.aeval_self_charpoly M
  rw [Polynomial.aeval_eq_sum_range, hnd] at hzero
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one, h2,
    one_smul, Algebra.smul_def, mul_one, map_one, one_mul] at hzero
  refine ⟨-M.charpoly.coeff 0, ?_⟩
  rw [htr, map_neg, map_neg]
  linear_combination hzero

private theorem two_mul_mul_sub_trace_eq_rat_of_finrank_two {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (x y : K) : 2 * x * y - algebraMap ℚ K (Algebra.trace ℚ K x) * y
      - algebraMap ℚ K (Algebra.trace ℚ K y) * x
      = algebraMap ℚ K (Algebra.trace ℚ K (x * y) - Algebra.trace ℚ K x * Algebra.trace ℚ K y) := by
  obtain ⟨r1, h1⟩ := exists_sq_sub_trace_mul_eq_rat_of_finrank_two hK (x + y)
  obtain ⟨r2, h2⟩ := exists_sq_sub_trace_mul_eq_rat_of_finrank_two hK x
  obtain ⟨r3, h3⟩ := exists_sq_sub_trace_mul_eq_rat_of_finrank_two hK y
  simp only [map_add (f := _)] at h1
  have hE : 2 * x * y - algebraMap ℚ K (Algebra.trace ℚ K x) * y
      - algebraMap ℚ K (Algebra.trace ℚ K y) * x = algebraMap ℚ K (r1 - r2 - r3) := by
    rw [map_sub, map_sub, ← h1, ← h2, ← h3]
    ring
  have e2 : 2 * x * y - algebraMap ℚ K (Algebra.trace ℚ K x) * y
      - algebraMap ℚ K (Algebra.trace ℚ K y) * x
      = (2 : ℚ) • (x * y) - Algebra.trace ℚ K x • y - Algebra.trace ℚ K y • x := by
    simp only [Algebra.smul_def, map_ofNat]
    ring
  have hT := congrArg (Algebra.trace ℚ K) hE
  rw [e2, Algebra.trace_algebraMap, hK, map_sub, map_sub, map_smul, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, nsmul_eq_mul] at hT
  rw [hE]
  congr 1
  push_cast at hT
  linarith

private theorem sub_smul_mul_sub_smul_eq_zero_of_quadratic {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) :
    (discr K % 4 = 0 ∨ discr K % 4 = 1) ∧ ∃ δ : K, δ ^ 2 = (discr K : K) ∧
      ∀ x : K, ∃ a b : ℚ, 2 * x * δ = (a : K) * δ + (b : K) := by
  classical
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank, hK]
  set bb := (integralBasis K).reindex (Fintype.equivFinOfCardEq hcard) with hbb
  have hint : ∀ i, IsIntegral ℤ (bb i) := fun i => by
    rw [hbb, Module.Basis.reindex_apply, integralBasis_apply]
    exact RingOfIntegers.isIntegral_coe _
  have hD : ((discr K : ℤ) : ℚ) = Algebra.discr ℚ bb := by
    rw [coe_discr, hbb, Module.Basis.coe_reindex, Algebra.discr_reindex]
  rw [Algebra.discr_def, Matrix.det_fin_two] at hD
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply] at hD
  have hone : (bb.repr 1 0) • bb 0 + (bb.repr 1 1) • bb 1 = 1 := by
    have := bb.sum_repr 1
    rwa [Fin.sum_univ_two] at this
  have hi0 := hint 0
  have hi1 := hint 1
  generalize bb.repr 1 0 = c0 at hone
  generalize bb.repr 1 1 = c1 at hone
  generalize bb 0 = x0 at hone hD hi0
  generalize bb 1 = x1 at hone hD hi1
  rw [mul_comm x1 x0] at hD
  have tr1 : Algebra.trace ℚ K 1 = 2 := by
    rw [← map_one (algebraMap ℚ K), Algebra.trace_algebraMap, hK]
    norm_num
  have R0 : Algebra.trace ℚ K x0
      = c0 * Algebra.trace ℚ K (x0 * x0) + c1 * Algebra.trace ℚ K (x0 * x1) := by
    have h : x0 = c0 • (x0 * x0) + c1 • (x0 * x1) := by
      calc x0 = x0 * 1 := (mul_one _).symm
        _ = x0 * (c0 • x0 + c1 • x1) := by rw [hone]
        _ = _ := by rw [mul_add, mul_smul_comm, mul_smul_comm]
    conv_lhs => rw [h]
    rw [map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have R1 : Algebra.trace ℚ K x1
      = c0 * Algebra.trace ℚ K (x0 * x1) + c1 * Algebra.trace ℚ K (x1 * x1) := by
    have h : x1 = c0 • (x0 * x1) + c1 • (x1 * x1) := by
      calc x1 = 1 * x1 := (one_mul _).symm
        _ = (c0 • x0 + c1 • x1) * x1 := by rw [hone]
        _ = _ := by rw [add_mul, smul_mul_assoc, smul_mul_assoc]
    conv_lhs => rw [h]
    rw [map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have R2 : 2 = c0 * Algebra.trace ℚ K x0 + c1 * Algebra.trace ℚ K x1 := by
    have := congrArg (Algebra.trace ℚ K) hone
    rw [map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul, tr1] at this
    exact this.symm
  have errorNonneg := two_mul_mul_sub_trace_eq_rat_of_finrank_two hK x0 x0
  have E11 := two_mul_mul_sub_trace_eq_rat_of_finrank_two hK x1 x1
  have bivariateExponentMonomial := two_mul_mul_sub_trace_eq_rat_of_finrank_two hK x0 x1
  simp only [map_sub, map_mul] at errorNonneg E11 bivariateExponentMonomial
  have hZ : ∀ y : K, IsIntegral ℤ y → ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ K y := fun y hy => by
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace (L := ℚ) hy)
    exact ⟨n, by rw [← hn]; simp⟩
  obtain ⟨n0, hn0⟩ := hZ x0 hi0
  obtain ⟨n1, hn1⟩ := hZ x1 hi1
  obtain ⟨m01, hm01⟩ := hZ (x0 * x1) (hi0.mul hi1)
  obtain ⟨δ, hδd⟩ : ∃ δ : K, δ = algebraMap ℚ K (Algebra.trace ℚ K x1) * x0
      - algebraMap ℚ K (Algebra.trace ℚ K x0) * x1 := ⟨_, rfl⟩
  have htd : Algebra.trace ℚ K δ = 0 := by
    rw [hδd, map_sub, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul, smul_eq_mul,
      smul_eq_mul]
    ring
  have hsecond : ∀ x : K, ∃ a b : ℚ, 2 * x * δ = (a : K) * δ + (b : K) := by
    intro x
    have E := two_mul_mul_sub_trace_eq_rat_of_finrank_two hK x δ
    rw [htd, map_zero, zero_mul, sub_zero, mul_zero, sub_zero] at E
    refine ⟨Algebra.trace ℚ K x, Algebra.trace ℚ K (x * δ), ?_⟩
    have hc : ∀ r : ℚ, (r : K) = algebraMap ℚ K r := fun r => by simp
    rw [hc, hc]
    linear_combination E
  generalize Algebra.trace ℚ K (x0 * x0) = T00 at R0 errorNonneg hD
  generalize Algebra.trace ℚ K (x1 * x1) = T11 at R1 E11 hD
  generalize Algebra.trace ℚ K (x0 * x1) = T01 at R0 R1 bivariateExponentMonomial hD hm01
  generalize Algebra.trace ℚ K x0 = t0 at R0 R2 errorNonneg bivariateExponentMonomial hn0 hδd
  generalize Algebra.trace ℚ K x1 = t1 at R1 R2 E11 bivariateExponentMonomial hn1 hδd
  have hQ : t1 ^ 2 * T00 - 2 * t0 * t1 * T01 + t0 ^ 2 * T11 = 2 * ((discr K : ℤ) : ℚ) := by
    rw [hD, R0, R1]
    rw [R0, R1] at R2
    linear_combination (-(T00 * T11 - T01 * T01)) * R2
  have hsq : δ ^ 2 = ((discr K : ℤ) : K) := by
    have hQ' := congrArg (algebraMap ℚ K) hQ
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_ofNat, map_intCast] at hQ'
    rw [hδd]
    linear_combination (algebraMap ℚ K t1 ^ 2 / 2) * errorNonneg
      - (algebraMap ℚ K t0 * algebraMap ℚ K t1) * bivariateExponentMonomial + (algebraMap ℚ K t0 ^ 2 / 2) * E11
      + (1 / 2 : K) * hQ'
  obtain ⟨ν, hνd⟩ : ∃ ν : K, ν = x0 * (algebraMap ℚ K t1 - x1) * ((algebraMap ℚ K t0 - x0) * x1) :=
    ⟨_, rfl⟩
  have hν : δ ^ 2 = (algebraMap ℚ K t0 * algebraMap ℚ K t1 - algebraMap ℚ K T01) ^ 2 - 4 * ν := by
    rw [hδd, hνd]
    linear_combination (-((algebraMap ℚ K t1 * x0 + algebraMap ℚ K t0 * x1 - 2 * x0 * x1)
      + algebraMap ℚ K t0 * algebraMap ℚ K t1 - algebraMap ℚ K T01)) * bivariateExponentMonomial
  have hIc : ∀ n : ℤ, IsIntegral ℤ (algebraMap ℚ K (n : ℚ)) := fun n => by
    have := isIntegral_algebraMap (R := ℤ) (A := K) (x := n)
    simpa using this
  have hνint : IsIntegral ℤ ν := by
    have ha0 := hIc n0
    have ha1 := hIc n1
    rw [hn0] at ha0
    rw [hn1] at ha1
    rw [hνd]
    exact (hi0.mul (ha1.sub hi1)).mul ((ha0.sub hi0).mul hi1)
  have hνq : ν = algebraMap ℚ K (((t0 * t1 - T01) ^ 2 - ((discr K : ℤ) : ℚ)) / 4) := by
    simp only [map_div₀, map_sub, map_pow, map_mul, map_intCast, map_ofNat]
    linear_combination (1 / 4 : K) * hν - (1 / 4 : K) * hsq
  obtain ⟨q, hq⟩ : ∃ n : ℤ, (n : ℚ) = ((t0 * t1 - T01) ^ 2 - ((discr K : ℤ) : ℚ)) / 4 := by
    have h1 : IsIntegral ℤ (((t0 * t1 - T01) ^ 2 - ((discr K : ℤ) : ℚ)) / 4) :=
      (isIntegral_algebraMap_iff ).1 (hνq ▸ hνint)
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
    exact ⟨n, by rw [← hn]; simp⟩
  rw [← hn0, ← hn1, ← hm01] at hq
  have hDZ : discr K = (n0 * n1 - m01) ^ 2 - 4 * q := by
    have : ((discr K : ℤ) : ℚ) = (((n0 * n1 - m01) ^ 2 - 4 * q : ℤ) : ℚ) := by
      push_cast
      linear_combination 4 * hq
    exact_mod_cast this
  refine ⟨?_, δ, hsq, hsecond⟩
  rw [hDZ]
  generalize n0 * n1 - m01 = σ
  rcases Int.even_or_odd σ with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · left
    have e : (k + k) ^ 2 - 4 * q = 4 * (k * k - q) := by ring
    rw [e]
    simp
  · right
    have e : (2 * k + 1) ^ 2 - 4 * q = 4 * (k * k + k - q) + 1 := by ring
    rw [e]
    generalize k * k + k - q = X
    omega

theorem quadMu (K Ω : Type) [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
    (hK : Module.finrank ℚ K = 2) (s : G ℚ Ω) (hs : ∀ ζ : Ω, ζ ^ (discr K).natAbs = 1 → s ζ = ζ) : s ∈ galOf ℚ K Ω := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨hd4, δ, hδ, hx⟩ := sub_smul_mul_sub_smul_eq_zero_of_quadratic hK
  have hD : discr K ≠ 0 := NumberField.discr_ne_zero K
  obtain ⟨δ', hδ'⟩ : ∃ δ' : Ω, δ' = algebraMap K Ω δ := ⟨_, rfl⟩
  have hδ'2 : δ' ^ 2 = ((discr K : ℤ) : Ω) := by
    rw [hδ', ← map_pow, hδ, map_intCast]
  have hsδ : s δ' = δ' := fx_disc (s := (s : Ω →+* Ω)) hD hd4 (fun ζ hζ => hs ζ hζ) δ' hδ'2
  have hδ0 : δ' ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero, eq_comm, Int.cast_eq_zero] at hδ'2
    exact hD hδ'2
  rw [mem_galOf]
  intro x
  obtain ⟨a, b, hab⟩ := hx x
  have hab' : 2 * algebraMap K Ω x * δ' = (a : Ω) * δ' + (b : Ω) := by
    have := congrArg (algebraMap K Ω) hab
    simpa [map_mul, map_add (f := _), map_ratCast, map_ofNat, hδ'] using this
  have hs2 := congrArg s hab'
  rw [map_mul, map_mul, map_add (f := _), map_mul, map_ratCast, map_ratCast, hsδ, map_ofNat] at hs2
  have h0 : (2 * δ') * (s (algebraMap K Ω x) - algebraMap K Ω x) = 0 := by
    linear_combination hs2 - hab'
  rcases mul_eq_zero.1 h0 with h0 | h0
  · exact absurd h0 (mul_ne_zero two_ne_zero hδ0)
  · exact sub_eq_zero.1 h0

end UpperTheory.V.Sd.Tw
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Base

namespace UpperTheory.V.Sd.Tw

section

variable {Ω : Type} [Field Ω]

private theorem not_lt_of_coprime (A : ValuationSubring Ω) {q n : ℕ} (hq : A.valuation (q : Ω) < 1) (h : q.Coprime n) :
    ¬ A.valuation (n : Ω) < 1 := by
  intro hn
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (1 : Ω) = (a : Ω) * q + (b : Ω) * n := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab.symm
  have h1 : ∀ (a : ℤ) (x : Ω), A.valuation x < 1 → A.valuation ((a : Ω) * x) < 1 := fun a x hx => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A a))) hx
  have := Valuation.map_add_lt A.valuation (h1 a _ hq) (h1 b _ hn)
  rw [← e, map_one] at this
  exact lt_irrefl _ this

variable [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem cls_frob {A : ValuationSubring Ω} {q N : ℕ} [NeZero N] (hq : A.valuation (q : Ω) < 1) (h : q.Coprime N)
    {t : G ℚ Ω} (ht : IsFrob (F := ℚ) A q t) : Chr.cls ℚ Ω N t = ZMod.unitOfCoprime q h := by
  refine (Chr.clsFacts ℚ Ω N).2.2.1 t _ fun ζ hζ => ?_
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod q hζ]
  refine eq_of_pow_eq_one A (not_lt_of_coprime A hq h) ?_ ?_
    (ht.2 ζ (valuation_eq_one_of_pow_eq_one A (NeZero.ne N) hζ).le)
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

private theorem cyc_frob {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {q : ℕ} (hp : q.Prime) (hq : A.valuation (q : Ω) < 1)
    (h : q.Coprime l) {t : G ℚ Ω} (ht : IsFrob (F := ℚ) A q t) : ((cycBar ℚ Ω l t : (Qbar l)ˣ) : Qbar l) = q := by
  haveI : Fact q.Prime := ⟨hp⟩
  obtain ⟨v, hv⟩ := (places ℚ Ω q A).1 fun hA => ((places ℚ Ω q A).2.1 hA).2 hq
  have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun hm =>
    not_lt_of_coprime A hq h (((places ℚ Ω l A).2.2.1 v hv).2 hm)
  have e : ((cycZ ℚ Ω l t : ℤ_[l]ˣ) : ℤ_[l]) = (q : ℤ_[l]) :=
    PadicInt.ext_of_toZModPow.mp fun n => cycZ_toZModPow_eq hl hv ht.2 n
  change ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) ((cycZ ℚ Ω l t : ℤ_[l]ˣ) : ℤ_[l]) = _
  rw [e, map_natCast]

private theorem continuous_cyc (l : ℕ) [Fact l.Prime] :
    Continuous fun t : G ℚ Ω => ((cycBar ℚ Ω l t : (Qbar l)ˣ) : Qbar l) :=
  ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val).comp
    ((Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l))

variable (K : Type) [Field K] [NumberField K] [Algebra K Ω]

omit [IsAlgClosure ℚ Ω] in
private theorem cc_notMem [_root_.NumberField.IsTotallyComplex K] {c : G ℚ Ω} (hc : Sd.IsCC c) : c ∉ galOf ℚ K Ω := by
  obtain ⟨j, hj⟩ := hc
  intro h
  refine IsTotallyComplex.complexEmbedding_not_isReal (j.comp (algebraMap K Ω)) ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := hj (algebraMap K Ω x)
  rw [h x] at this
  exact this.symm

omit [IsAlgClosure ℚ Ω] in
private theorem cc_sq {c : G ℚ Ω} (hc : Sd.IsCC c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := hc
  ext x
  apply j.injective
  rw [AlgEquiv.mul_apply, hj, hj, Complex.conj_conj, AlgEquiv.one_apply]

private theorem exists_chi [IsAlgClosure K Ω] (hK : Module.finrank ℚ K = 2) (N : ℕ) [NeZero N] (hN : N = (discr K).natAbs) :
    (Chr.cls ℚ Ω N).ker ≤ galOf ℚ K Ω ∧ ∃ χ : (ZMod N)ˣ →* ℂˣ, χ ^ 2 = 1 ∧
      ∀ t : G ℚ Ω, t ∉ galOf ℚ K Ω → χ (Chr.cls ℚ Ω N t) = -1 := by
  classical
  have hker : (Chr.cls ℚ Ω N).ker ≤ galOf ℚ K Ω := fun s hs => quadMu K Ω hK s fun ζ hζ => by
    rw [← hN] at hζ
    rw [Chr.cls_spec N s ζ hζ, MonoidHom.mem_ker.1 hs, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
  have hi : (galOf ℚ K Ω).index = 2 := (galEmbTop ℚ K Ω).2.2.trans hK
  let δ : G ℚ Ω →* ℂˣ := MonoidHom.mk' (fun s => if s ∈ galOf ℚ K Ω then 1 else -1) fun a b => by
    by_cases ha : a ∈ galOf ℚ K Ω <;> by_cases hb : b ∈ galOf ℚ K Ω <;>
      simp [Subgroup.mul_mem_iff_of_index_two hi, ha, hb]
  have hδ : (Chr.cls ℚ Ω N).ker ≤ δ.ker := fun s hs => if_pos (hker hs)
  have hs := (Chr.clsOnto Ω N).1
  have e : ∀ t, (Chr.cls ℚ Ω N).liftOfSurjective hs ⟨δ, hδ⟩ (Chr.cls ℚ Ω N t) = δ t := fun t =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ t
  refine ⟨hker, (Chr.cls ℚ Ω N).liftOfSurjective hs ⟨δ, hδ⟩, MonoidHom.ext fun u => ?_, fun t ht => (e t).trans (if_neg ht)⟩
  obtain ⟨t, rfl⟩ := hs u
  rw [MonoidHom.pow_apply, e]
  change (if t ∈ galOf ℚ K Ω then (1 : ℂˣ) else -1) ^ 2 = 1
  split_ifs <;> simp

private theorem ver_of_frob [IsAlgClosure K Ω] (hK : Module.finrank ℚ K = 2) {l : ℕ} [Fact l.Prime] (κ : G K Ω →* (Qbar l)ˣ)
    (hκ : Continuous κ) (T : ℕ) (hT : T ≠ 0)
    (H : ∀ (q : ℕ) (A : ValuationSubring Ω) (t : G ℚ Ω) (s : G K Ω), q.Prime → ¬ q ∣ T → A.valuation (q : Ω) < 1 →
      IsFrob (F := ℚ) A q t → t ∉ galOf ℚ K Ω → galEmb ℚ K Ω s = t * t →
      (κ s : Qbar l) * (cycBar ℚ Ω l t : (Qbar l)ˣ) = -1)
    (s : G K Ω) (t : G ℚ Ω) (ht : t ∉ galOf ℚ K Ω) (hs : galEmb ℚ K Ω s = t * t) : κ s = -(cycBar ℚ Ω l t)⁻¹ := by
  obtain ⟨hemb, hopen, hi⟩ := galEmbTop ℚ K Ω
  have hsq : ∀ t : G ℚ Ω, ∃ s, galEmb ℚ K Ω s = t * t := fun t => by
    have := Subgroup.mul_self_mem_of_index_two (hi.trans hK) t
    rw [← range_galEmb] at this
    exact this
  choose g hg using hsq
  have hgc : Continuous g := hemb.continuous_iff.2 ((continuous_id.mul continuous_id).congr fun t => (hg t).symm)
  have hcl : IsClosed {t : G ℚ Ω | (κ (g t) : Qbar l) * (cycBar ℚ Ω l t : (Qbar l)ˣ) = -1} :=
    isClosed_eq ((Units.continuous_val.comp (hκ.comp hgc)).mul (continuous_cyc l)) continuous_const
  have key : (κ (g t) : Qbar l) * (cycBar ℚ Ω l t : (Qbar l)ˣ) = -1 := by
    by_contra hne
    obtain ⟨q, A, φ, hq, hqT, hA, hφ, h1, h2⟩ := ML.chebQ Ω _
      (hcl.isOpen_compl.inter ((galOf ℚ K Ω).isClosed_of_isOpen hopen).isOpen_compl) ⟨t, hne, ht⟩ T hT
    exact h1 (H q A φ (g φ) hq hqT hA hφ h2 (hg φ))
  rw [hemb.injective ((hg t).trans hs.symm)] at key
  rw [← mul_left_inj (cycBar ℚ Ω l t), neg_mul, inv_mul_cancel]
  exact Units.ext key

end

end UpperTheory.V.Sd.Tw

open UpperTheory.V.Sd.Tw in
theorem UpperTheory.V.Sd.twist :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Sd.Twist := by
  intro hP K Ω _ _ _ _ _ _ _ hK l hl hl2 hld ι c hc
  haveI : IsAlgClosure K Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  set N := (discr K).natAbs with hN
  have hN3 : 3 ≤ N := by
    have := abs_discr_gt_two (K := K) (by omega)
    rw [Int.abs_eq_natAbs] at this
    omega
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hker, χ, hχ2, hχ⟩ := exists_chi (Ω := Ω) K hK N hN
  have hχ1 : χ (-1) = -1 := by
    rw [← (Chr.clsFacts ℚ Ω N).2.2.2.1 c hc]
    exact hχ c (cc_notMem K hc)
  obtain ⟨Y, a, τ, hYa, ha1, ha0, hYu, ⟨m, hm0, hml, hm⟩, hYv⟩ := hecke K hK l hl.out hl2 hld N hN3 χ hχ2 hχ1
  obtain ⟨art, hart⟩ : ∃ art : Ideles K →* Gab K Ω, IsGlobalArtin art := hP.litN.aut.art K Ω
  obtain ⟨κ, hκ, hL⟩ := hart.exists_isLAdicOf ι (isAlgPos_of_isAlg hYa)
  have hNd : ∀ v : HeightOneSpectrum (𝓞 K), ((discr K : ℤ) : 𝓞 K) ∉ v.asIdeal → (N : 𝓞 K) ∉ v.asIdeal := fun v hv h => by
    apply hv
    rcases Int.natAbs_eq (discr K) with e | e
    · rw [e, Int.cast_natCast]
      exact h
    · rw [e, Int.cast_neg, Int.cast_natCast]
      exact neg_mem h
  have hnat : ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 K)), IsPlaceOver A w → ∀ n : ℤ,
      ¬ A.valuation (n : Ω) < 1 → (n : 𝓞 K) ∉ w.asIdeal := fun A w hw n hn h => by
    have := (hw (n : 𝓞 K)).2 h
    exact hn (by simpa using this)
  have hnat' : ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 K)), IsPlaceOver A w → ∀ n : ℕ,
      ¬ A.valuation (n : Ω) < 1 → (n : 𝓞 K) ∉ w.asIdeal := fun A w hw n hn => by
    simpa using hnat A w hw n (by simpa using hn)
  have hver := ver_of_frob K hK κ hκ (l * N) (mul_ne_zero hl.out.ne_zero (NeZero.ne N)) fun q A t s hq hqT hA ht htK hs => by
    have hc' := (Nat.Prime.coprime_iff_not_dvd hq).2 hqT
    have hql := hc'.coprime_mul_right_right
    have hqN := hc'.coprime_mul_left_right
    have hAN := not_lt_of_coprime A hA hqN
    obtain ⟨w, hw, hwq, hfr⟩ := inert K Ω hK q hq A hA (((Chr.clsFacts ℚ Ω N).2.2.2.2 A hAN).trans hker) t ht htK
    rw [hL.frob_unr hart (Or.inl (hnat' A w hw l (not_lt_of_coprime A hA hql))) (hYu w (hnat' A w hw N hAN)) hw (hfr s hs),
      hYv q hqN w hwq, ← cls_frob hA hqN ht, hχ t htK, cyc_frob hq hA hql ht]
    have hq0 : (q : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
    simp [hq0]
  refine ⟨κ, hκ, ⟨art, Y, a, τ, hart, isAlgPos_of_isAlg hYa, hL, ha1, ha0, fun v hv => hYu v (hNd v hv)⟩,
    fun s s' h => ?_, hver, fun A hAl hAd s hs => ?_, m, hm0, hml, fun A hAl s hs => ?_⟩
  · have hi : (galOf ℚ K Ω).index = 2 := (galEmbTop ℚ K Ω).2.2.trans hK
    have h1 : galEmb ℚ K Ω s * c ∉ galOf ℚ K Ω := fun h' =>
      cc_notMem K hc (((galOf ℚ K Ω).mul_mem_cancel_left (galEmb_mem ℚ K Ω s)).1 h')
    have h2 : c⁻¹ = c := inv_eq_of_mul_eq_one_right (cc_sq hc)
    have h3 : cycBar ℚ Ω l c = -1 := by
      have h4 : cycZ ℚ Ω l c = -1 := IsConjOm.cyc (E := ℚ) (show IsConjOm c.toRingEquiv from hc)
      change Units.map _ (cycZ ℚ Ω l c) = -1
      rw [h4]
      exact Units.ext (by simp)
    rw [← map_mul, hver (s * s') _ h1 (by rw [map_mul, h, h2]; simp only [mul_assoc]), map_mul, h3, mul_neg_one, inv_neg, neg_neg]
    rfl
  · by_cases hA : A = ⊤
    · rw [((places K Ω l A).2.1 hA).1, Subgroup.mem_bot] at hs
      rw [hs, map_one]
    · obtain ⟨w, hw⟩ := (places K Ω l A).1 hA
      exact (hL.unr_iff hart (Or.inl (hnat' A w hw l hAl)) hw).2 (hYu w (hNd w (hnat A w hw _ hAd))) s hs
  · by_cases hA : A = ⊤
    · rw [((places K Ω l A).2.1 hA).1, Subgroup.mem_bot] at hs
      rw [hs, map_one, one_pow]
    · obtain ⟨w, hw⟩ := (places K Ω l A).1 hA
      obtain ⟨x, hx, e⟩ := (hL.ine_image hart (Or.inl (hnat' A w hw l hAl)) hw _).1 ⟨s, hs, rfl⟩
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, ← e, ← map_pow, ← Units.val_pow_eq_pow_val, hm w x hx]
      simp
