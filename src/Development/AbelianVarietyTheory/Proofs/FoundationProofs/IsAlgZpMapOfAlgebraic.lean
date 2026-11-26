module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueNormalizedCyclotomicTrace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantDivQIntegerQExpansions
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusPowerReductionCongruence

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgebraicNumberCongrModPrimePowStatement
open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicNumber_congr_mod_prime_pow :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime]
      (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl],
      IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ IsInt (p := p) (j x)) →
      ∀ (k : ℕ) (e : Ωl), IsInt (p := p) e → IsAlgZp (p := p) e →
      ∃ a ∈ A, Cong (p := p) k e (j a) := by
  intro Ω _ _ _ p hp A Ωl _ _ hclo j hA k e he halg
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hcong : ∃ a : Ω, IsInt (p := p) (j a) ∧ Cong (p := p) k e (j a) := by
    obtain ⟨P, hP0, hP⟩ := halg
    have : CharZero Ωl := Basic.charZero_of_isClo hclo
    have hpne : (p : Ωl) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    obtain ⟨v, hv, _, hp0, hp1⟩ := GlobalTheory.K5.exists_valuation_isInt p Ωl hclo
    set φ : ℤ_[p] →+* Ωl := (algebraMap (O0 p) Ωl).comp (algebraMap ℤ_[p] (O0 p)) with hφ
    have hPe : P.eval₂ φ e = 0 := by rwa [aeval_def, eval₂_map] at hP
    have hφint : ∀ x, v (φ x) ≤ 1 := fun x => (hv _).2 isIntegral_algebraMap
    have hc0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP0
    have hc : φ P.leadingCoeff ≠ 0 := by
      rw [PadicInt.unitCoeff_spec hc0, map_mul, map_pow, map_natCast]
      exact mul_ne_zero ((Units.isUnit _).map φ).ne_zero (pow_ne_zero _ hpne)
    have hvc : 0 < v (φ P.leadingCoeff) := (Valuation.pos_iff v).2 hc
    obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one
      (mul_pos hvc (pow_pos (pow_pos hp0 k) P.natDegree)) hp1
    have hpk : v (p : Ωl) ^ k ≤ 1 := pow_le_one₀ zero_le hp1.le
    have hN' : v (p : Ωl) ^ N < v (φ P.leadingCoeff) :=
      hN.trans_le (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hpk))
    obtain ⟨Q, R, hdeg, hQR⟩ := Dense.exists_approx P N
    have hsmall : ∀ y : Ωl, v y ≤ 1 → v ((p : Ωl) ^ N * y) ≤ v (p : Ωl) ^ N := by
      intro y hy
      rw [map_mul, map_pow]
      exact mul_le_of_le_one_right zero_le hy
    have hco : φ P.leadingCoeff = (Q.coeff P.natDegree : Ωl) + (p : Ωl) ^ N * φ (R.coeff P.natDegree) := by
      have := congrArg (fun (S : ℤ_[p][X]) => φ (S.coeff P.natDegree)) hQR
      simp only [coeff_add, coeff_C_mul, coeff_map, map_add (f := _), map_mul, eq_intCast, map_intCast] at this
      rw [map_pow, map_natCast] at this
      exact this
    have hvQ : v (Q.coeff P.natDegree : Ωl) = v (φ P.leadingCoeff) := by
      rw [eq_sub_of_add_eq hco.symm]
      exact Valuation.map_sub_eq_of_lt_left v ((hsmall _ (hφint _)).trans_lt hN')
    have hQ0 : Q.coeff P.natDegree ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero, map_zero] at hvQ
      exact hvc.ne hvQ
    have hdeg' : Q.natDegree = P.natDegree := natDegree_eq_of_le_of_coeff_ne_zero hdeg hQ0
    have hRe : v (R.eval₂ φ e) ≤ 1 := by
      rw [eval₂_eq_sum_range]
      refine Valuation.map_sum_le v fun i _ => ?_
      rw [map_mul, map_pow]
      exact (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le ((hv _).2 he))).trans (hφint _)
    have hQe : Q.eval₂ (Int.castRingHom Ωl) e = -((p : Ωl) ^ N * R.eval₂ φ e) := by
      rw [hQR, eval₂_add, eval₂_mul, eval₂_C, eval₂_map, map_pow, map_natCast,
        RingHom.ext_int (φ.comp _) (Int.castRingHom Ωl)] at hPe
      exact eq_neg_of_add_eq_zero_left hPe
    obtain ⟨a, ha⟩ := Dense.exists_near_root v j e (v (p : Ωl) ^ k) Q (by
      rw [hQe, Valuation.map_neg, leadingCoeff, hdeg', hvQ]
      exact (hsmall _ hRe).trans_lt hN)
    refine ⟨a, (hv _).1 ?_, (e - j a) / (p : Ωl) ^ k, (hv _).1 ?_, ?_⟩
    · rw [show j a = e - (e - j a) by ring]
      exact Valuation.map_sub_le v ((hv _).2 he) (ha.le.trans hpk)
    · rw [map_div₀, map_pow]
      exact div_le_one_of_le₀ ha.le zero_le
    · field_simp
  obtain ⟨a, ha, hc⟩ := hcong
  exact ⟨a, (hA a).2 ha, hc⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalAutFixingTowerParamOfStabilizes
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalAutFixingTowerParamOfStabilizes
noncomputable section

namespace GlobalTheory.Glue.CuspUp

open GlobalTheory.K5 GlobalTheory.KZ Polynomial
open scoped NNReal

section Local

variable {p : ℕ} [hp : Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]
  {v : Valuation Ωl ℝ≥0}

theorem v_alg_le (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) (b : O0 p) : v (algebraMap (O0 p) Ωl b) ≤ 1 :=
  (hv _).2 isIntegral_algebraMap

theorem v_alg_lt_iff (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) (h1 : v (p : Ωl) < 1) (b : O0 p) :
    v (algebraMap (O0 p) Ωl b) < 1 ↔ (p : O0 p) ∣ b := by
  obtain ⟨_, hd, hirr⟩ := completed_laurent_isDVR p
  constructor
  · intro hb
    rw [← Ideal.mem_span_singleton, ← hirr.maximalIdeal_eq]
    intro hu
    obtain ⟨c, hc⟩ := hu.exists_right_inv
    have h2 : v (algebraMap (O0 p) Ωl b) * v (algebraMap (O0 p) Ωl c) = 1 := by
      rw [← map_mul, ← map_mul, hc, map_one, map_one]
    exact absurd h2 (mul_lt_one_of_nonneg_of_lt_one_left zero_le hb (v_alg_le hv c)).ne
  · rintro ⟨c, rfl⟩
    rw [map_mul, map_mul, map_natCast]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 (v_alg_le hv c)

theorem exists_red : ∃ φ : O0 p →+* LaurentSeries (ZMod p),
    φ (qO p) = HahnSeries.single (1 : ℤ) (1 : ZMod p) ∧ ∀ b, φ b = 0 ↔ (p : O0 p) ∣ b := by
  obtain ⟨e, he⟩ := exists_completedLaurent_quot_prime_equiv_laurentFp p
  refine ⟨e.toRingHom.comp (Ideal.Quotient.mk _), he, fun b => ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  exact e.map_eq_zero_iff

theorem isInt_qq (T : K5.Tower p Ωl) (n : ℕ) : IsIntegral (O0 p) (T.qq n) := by
  refine IsIntegral.of_pow (pow_pos hp.out.pos n) ?_
  rw [Basic.qq_pow]
  exact isIntegral_algebraMap

theorem v_aeval_le (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) (T : K5.Tower p Ωl) (n : ℕ) (f : (O0 p)[X]) :
    v (aeval (T.qq n) f) ≤ 1 :=
  (hv _).2 (IsIntegral.of_mem_of_fg _ (isInt_qq T n).fg_adjoin_singleton _
    (aeval_mem_adjoin_singleton _ _))

theorem orth (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (f : (O0 p)[X]) (hf : f.natDegree < p ^ n)
    (hlt : v (aeval (T.qq n) f) < 1) : C (p : O0 p) ∣ f := by
  obtain ⟨φ, hq, hφ⟩ := exists_red (p := p)
  have h2 := GlobalTheory.aeval_qq_pow_sub_lt_one p Ωl h v hv h1 T n f hf
  have h3 : v (aeval (T.qq n) f ^ (p ^ n)) < 1 := by
    rw [map_pow]; exact pow_lt_one₀ zero_le hlt (pow_pos hp.out.pos n).ne'
  have h4 := v.map_sub_lt h3 h2
  rw [sub_sub_cancel, v_alg_lt_iff hv h1, ← hφ] at h4
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, hq] at h4
  have h5 := GlobalTheory.laurent_pow_indep_over_prime_pow_powers p n (fun i => φ (f.coeff i)) h4
  rw [C_dvd_iff_dvd_coeff]
  intro i
  by_cases hi : i < p ^ n
  · exact (hφ _).1 (h5 i hi)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact dvd_zero _

theorem res (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (f : (O0 p)[X]) (hf : f.natDegree < p ^ n)
    (halg : IsAlgebraic ℤ (aeval (T.qq n) f)) : ∃ m : ℤ, v (aeval (T.qq n) f - m) < 1 := by
  obtain ⟨φ, hq, hφ⟩ := exists_red (p := p)
  have h2 := GlobalTheory.aeval_qq_pow_sub_lt_one p Ωl h v hv h1 T n f hf
  have hy := v_aeval_le hv T n f
  set y := aeval (T.qq n) f
  set b := ∑ i ∈ Finset.range (p ^ n), f.coeff i ^ (p ^ n) * qO p ^ i
  have hroot : ∃ P : ℤ[X], P.map (Int.castRingHom (ZMod p)) ≠ 0 ∧ (p : O0 p) ∣ aeval b P := by
    haveI : CharZero Ωl := Basic.charZero_of_isClo h
    let z := y ^ p ^ n
    obtain ⟨Q, hQ, hQz⟩ := halg.pow (p ^ n)
    let P := Q.primPart
    have hPz : aeval z P = 0 := by
      have hc : Q.content ≠ 0 := fun hc => hQ (Polynomial.content_eq_zero_iff.mp hc)
      rw [Q.eq_C_content_mul_primPart, map_mul, aeval_C] at hQz
      exact (mul_eq_zero.mp hQz).resolve_left (by simpa using hc)
    refine ⟨P, ?_, (v_alg_lt_iff hv h1 _).1 ?_⟩
    · intro hP
      have hd : ∀ i, (p : ℤ) ∣ P.coeff i := by
        intro i
        have hi := congrArg (fun R => R.coeff i) hP
        simp only [coeff_map, coeff_zero, eq_intCast] at hi
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hi
      have hu := (Polynomial.isPrimitive_primPart Q) (p : ℤ) ((C_dvd_iff_dvd_coeff _ _).2 hd)
      have := Int.isUnit_iff.1 hu
      have := hp.out.two_le
      omega
    · let b' := algebraMap (O0 p) Ωl b
      have hz : v z ≤ 1 := by
        dsimp [z]
        rw [map_pow]
        exact pow_le_one₀ zero_le hy
      let zi : v.integer := ⟨z, hz⟩
      let bi : v.integer := ⟨b', v_alg_le hv b⟩
      obtain ⟨d, hd⟩ := Polynomial.sub_dvd_eval_sub zi bi (P.map (Int.castRingHom v.integer))
      have hev (w : v.integer) :
          v.integer.subtype ((P.map (Int.castRingHom v.integer)).eval w) = aeval (w : Ωl) P := by
        rw [Polynomial.eval_map, aeval_def]
        have hw := Polynomial.hom_eval₂ P (Int.castRingHom v.integer) v.integer.subtype w
        rw [show v.integer.subtype.comp (Int.castRingHom v.integer) = algebraMap ℤ Ωl from
          RingHom.ext_int _ _] at hw
        exact hw
      have hd' := congrArg v.integer.subtype hd
      rw [map_sub, map_mul, map_sub, hev, hev] at hd'
      change aeval z P - aeval b' P = (z - b') * (d : Ωl) at hd'
      rw [hPz, zero_sub, neg_eq_iff_eq_neg] at hd'
      have hmap : algebraMap (O0 p) Ωl (aeval b P) = aeval b' P := by
        rw [aeval_def, aeval_def, Polynomial.hom_eval₂]
        congr 1
        exact RingHom.ext_int _ _
      rw [hmap, hd', Valuation.map_neg, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h2 d.2
  obtain ⟨P, hP0, hP⟩ := hroot
  obtain ⟨c, hc⟩ := GlobalTheory.laurentSeries_eq_C_of_root (ZMod p) (φ b) ⟨_, hP0, by
    rw [← (hφ _).2 hP, eval₂_map, aeval_def, hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _⟩
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective c
  refine ⟨m, ?_⟩
  have h3 : v (algebraMap (O0 p) Ωl (b - (m : O0 p) ^ p ^ n)) < 1 := by
    let C' : ZMod p →+* LaurentSeries (ZMod p) := HahnSeries.C
    change φ b = C' (m : ZMod p) at hc
    rw [v_alg_lt_iff hv h1, ← hφ, φ.map_sub, hc, φ.map_pow, map_intCast φ,
      ← map_intCast C', ← C'.map_pow, ZMod.pow_card_pow, sub_self]
  have hm : v (m : Ωl) ≤ 1 := (hv _).2 (Basic.isInt_intCast m)
  let y' : v.integer := ⟨y - m, v.map_sub_le hy hm⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp.out y' (m : v.integer) n
  have hr' := congrArg (Subtype.val) hr
  simp only [y'] at hr'
  push_cast at hr'
  have h4 : v ((p : Ωl) * (y - m) * m * r) < 1 := by
    rw [mul_assoc, mul_assoc, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 (y' * ((m : v.integer) * r)).2
  have h5 := v.map_sub_lt (v.map_add_lt h2 h3) h4
  have h6 : y ^ p ^ n - algebraMap (O0 p) Ωl b + algebraMap (O0 p) Ωl (b - (m : O0 p) ^ p ^ n) -
      (p : Ωl) * (y - m) * m * r = (y - m) ^ p ^ n := by
    rw [map_sub, map_pow, map_intCast]
    rw [sub_add_cancel] at hr'
    linear_combination hr'
  rw [h6, map_pow] at h5
  exact lt_of_pow_lt_pow_left₀ (p ^ n) zero_le_one (by rwa [one_pow])

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem approx (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (j : Ω →+* Ωl) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x, v (j x) ≤ 1 → v (j (s x)) ≤ 1)
    (N : ℕ) : ∀ (f : (O0 p)[X]) (a : Ω), f.natDegree < p ^ n → aeval (T.qq n) f = j a →
      v (j (s a - a)) ≤ v (p : Ωl) ^ N := by
  haveI := Basic.charZero_of_isClo h
  haveI : CharZero Ω := algebraRat.charZero Ω
  induction N with
  | zero =>
    intro f a _ ha
    have h2 := v_aeval_le hv T n f
    rw [ha] at h2
    rw [map_sub, pow_zero]
    exact v.map_sub_le (hs a h2) h2
  | succ N ih =>
    intro f a hf ha
    have halg : IsAlgebraic ℤ a :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨m, hm⟩ := res h hv h1 T n f hf (ha ▸ halg.algHom j.toIntAlgHom)
    have hf' : (f - C (m : O0 p)).natDegree < p ^ n := by rwa [natDegree_sub_C]
    obtain ⟨g, hg⟩ := orth h hv h1 T n _ hf' (by simpa using hm)
    have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hpl : (p : Ωl) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hpO : (p : O0 p) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have h3 := ih g ((a - m) / p) (by rwa [hg, natDegree_C_mul hpO] at hf') (by
      have := congrArg (aeval (T.qq n)) hg
      simp only [map_sub, map_mul, aeval_C, map_intCast, map_natCast, ha] at this
      rw [map_div₀, map_sub, map_intCast, map_natCast, this, mul_div_cancel_left₀ _ hpl])
    have h4 : s a - a = p * (s ((a - m) / p) - (a - m) / p) := by
      rw [map_div₀, map_sub, map_intCast, map_natCast]; field_simp; ring
    rw [h4, map_mul, map_mul, map_natCast, pow_succ']
    exact mul_le_mul_right h3 _

theorem fixed (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (j : Ω →+* Ωl) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x, v (j x) ≤ 1 → v (j (s x)) ≤ 1)
    (f : (O0 p)[X]) (d : O0 p) (hd : d ≠ 0) (a : Ω)
    (ha : aeval (T.qq n) f = algebraMap (O0 p) Ωl d * j a) : s a = a := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨_, hdv, hirr⟩ := completed_laurent_isDVR p
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hirr
  have hpos := pow_pos hp.out.pos n
  have hmon : (X ^ (p ^ n) - C (qO p)).Monic := monic_X_pow_sub_C _ hpos.ne'
  have hdeg : ((C (↑u⁻¹ : O0 p) * f) %ₘ (X ^ (p ^ n) - C (qO p))).natDegree < p ^ n := by
    have := natDegree_modByMonic_lt (C (↑u⁻¹ : O0 p) * f) hmon (fun h0 => by
      have := congrArg natDegree h0
      rw [natDegree_X_pow_sub_C _, natDegree_one] at this
      omega)
    rwa [natDegree_X_pow_sub_C _] at this
  have hev : aeval (T.qq n) ((C (↑u⁻¹ : O0 p) * f) %ₘ (X ^ (p ^ n) - C (qO p))) = j ((p : Ω) ^ m * a) := by
    rw [aeval_modByMonic_eq_self_of_root (by simp [Basic.qq_pow]), map_mul, aeval_C, ha, ← mul_assoc,
      ← map_mul, Units.inv_mul_cancel_left]
    simp
  have h0 : v (j (s ((p : Ω) ^ m * a) - (p : Ω) ^ m * a)) = 0 := by
    by_contra hne
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (pos_iff_ne_zero.2 hne) h1
    exact absurd (approx h hv h1 T n j s hs N _ _ hdeg hev) (not_le.2 hN)
  rw [v.zero_iff, map_eq_zero, sub_eq_zero, map_mul, map_pow, map_natCast] at h0
  exact mul_left_cancel₀ (pow_ne_zero m (by exact_mod_cast hp.out.ne_zero)) h0

theorem up (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (j : Ω →+* Ωl) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x, v (j x) ≤ 1 → v (j (s x)) ≤ 1) :
    ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x) := by
  haveI := h.clo
  haveI := h.alg
  haveI := Basic.charZero_of_isClo h
  haveI : FaithfulSMul (O0 p) Ωl := (faithfulSMul_iff_algebraMap_injective _ _).2 h.inj
  letI : Algebra (FractionRing (O0 p)) Ωl := FractionRing.liftAlgebra (O0 p) Ωl
  haveI : IsScalarTower (O0 p) (FractionRing (O0 p)) Ωl := FractionRing.isScalarTower_liftAlgebra _ _
  haveI : Algebra.IsAlgebraic (FractionRing (O0 p)) Ωl :=
    (IsFractionRing.comap_isAlgebraic_iff (A := O0 p) (K := FractionRing (O0 p))).1 h.alg
  let K := IntermediateField.adjoin (FractionRing (O0 p)) {T.qq n}
  have hfix : ∀ a : Ω, j a ∈ Set.range (algebraMap K Ωl) → s a = a := by
    rintro a ⟨⟨y, hy⟩, rfl : y = j a⟩
    rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _), Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨f, hf⟩ := hy
    obtain ⟨d, hd, hdf⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (O0 p)) f
    refine fixed h hv h1 T n j s hs
      (IsLocalization.integerNormalization (nonZeroDivisors (O0 p)) f) d (nonZeroDivisors.ne_zero hd) a ?_
    rw [← aeval_map_algebraMap (FractionRing (O0 p)), hdf, ← Algebra.smul_def, ← hf,
      ← algebraMap_smul (FractionRing (O0 p)) d f, map_smul, algebraMap_smul]
    rfl
  obtain ⟨g, hg⟩ := GlobalTheory.exists_algEquiv_inducing_of_forall_conj Ω Ωl K j s (GlobalTheory.exists_algEquiv_apply_eq_of_fixes_preimage_base Ω Ωl K j s hfix)
  refine ⟨(g.restrictScalars (FractionRing (O0 p))).restrictScalars (O0 p), ?_, hg⟩
  exact g.commutes ⟨T.qq n, IntermediateField.mem_adjoin_simple_self _ _⟩

end Local

theorem exists_gal_fix_qq_of_stab {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl] (h : IsClo p Ωl) (j : Ω →+* Ωl)
    (hA : ∀ x, x ∈ A ↔ IsInt (p := p) (j x)) (T : GlobalTheory.K5.Tower p Ωl) (n : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (hs : Stab A s) :
    ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x) := by
  obtain ⟨_, hdvr, hirr⟩ := completed_laurent_isDVR p
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [hirr.maximalIdeal_eq]
    exact GlobalTheory.T.unramified_integers_adic_complete p
  haveI := h.alg
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr (O0 p) Ωl h.inj
  have h1 : v (p : Ωl) < 1 := by
    haveI := Basic.charZero_of_isClo h
    have hle : v (p : Ωl) ≤ 1 := by
      rw [← map_natCast (algebraMap (O0 p) Ωl)]
      exact (hv _).2 isIntegral_algebraMap
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hi : v (p : Ωl)⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
    have hp0 : (p : Ωl) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact Basic.not_cong_one_zero h 1 one_ne_zero
      ⟨(p : Ωl)⁻¹, (hv _).1 hi, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩
  exact up h hv h1 T n j s fun x hx => (hv _).2 ((hA _).1 ((hs x).2 ((hA _).2 ((hv _).1 hx))))

end GlobalTheory.Glue.CuspUp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalAutFixingTowerParamOfStabilizesStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_aut_fixing_tower_param_of_stabilizes : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ GlobalTheory.K5.IsInt (p := p) (j x)) → ∀ (T : GlobalTheory.K5.Tower p Ωl) (n : ℕ) (s : Ω ≃ₐ[ℚ] Ω), Stab A s → ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x) := by
  first | exact @GlobalTheory.Glue.CuspUp.exists_gal_fix_qq_of_stab | exact GlobalTheory.Glue.CuspUp.exists_gal_fix_qq_of_stab | (intros; apply GlobalTheory.Glue.CuspUp.exists_gal_fix_qq_of_stab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgClosureAutomorphismRestrictingLocal
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.CuspDown

theorem exists_restrict : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ IsInt (p := p) (j x)) → ∀ g : Gal p Ωl, ∃ s : Ω ≃ₐ[ℚ] Ω, Stab A s ∧ ∀ x, g (j x) = j (s x) := by
  intro Ω _ _ _ p _ A Ωl _ _ hC j hA g
  haveI : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hC
  letI : Algebra Ω Ωl := j.toAlgebra
  haveI : IsScalarTower ℚ Ω Ωl := IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ Ωl), eq_ratCast (algebraMap ℚ Ω), map_ratCast]
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let gq : Ωl ≃ₐ[ℚ] Ωl := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun x => by
    simp only [eq_ratCast, AlgEquiv.coe_toRingEquiv, RingEquiv.coe_toEquiv, AlgEquiv.coe_ringEquiv]
    exact map_ratCast g x)
  have hc : ∀ x, g (j x) = j (gq.restrictNormal Ω x) := fun x => by
    have := AlgEquiv.restrictNormal_commutes gq Ω x
    rw [RingHom.algebraMap_toAlgebra] at this
    rw [this]; rfl
  refine ⟨gq.restrictNormal Ω, fun x => ?_, hc⟩
  rw [hA, hA, ← hc]
  constructor
  · intro h
    have := GlobalTheory.K5.Basic.isInt_gal g.symm h
    rwa [AlgEquiv.symm_apply_apply] at this
  · exact GlobalTheory.K5.Basic.isInt_gal g

end GlobalTheory.CuspDown
end

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Glue

theorem isAlgZp_map_of_algebraic : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl] (j : Ω →+* Ωl) (x : Ω), IsAlgZp (p := p) (j x) := by
  intro Ω _ _ _ p _ Ωl _ _ j x
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have hz : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 hx
  obtain ⟨P, hP, hPx⟩ := hz
  refine ⟨P.map (Int.castRingHom ℤ_[p]), ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hP
  · rw [Polynomial.map_map, Polynomial.aeval_def, Polynomial.eval₂_map]
    have e1 : (algebraMap (O0 p) Ωl).comp ((algebraMap ℤ_[p] (O0 p)).comp (Int.castRingHom ℤ_[p])) = j.comp (algebraMap ℤ Ω) := RingHom.ext_int _ _
    rw [e1, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hPx, map_zero]

theorem zt_prim_and_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (l n : ℕ), 0 < l → IsPrimitiveRoot (zt ε l n) (l ^ n) ∧ zt ε l (n + 1) ^ l = zt ε l n := by
  intro Ω _ _ _ ε l n hl
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hkey : ∀ m : ℕ, ε (zt ε l m) = Complex.exp (2 * Real.pi * Complex.I / ((l ^ m : ℕ) : ℂ)) := by
    intro m
    have hN : l ^ m ≠ 0 := pow_ne_zero _ hl.ne'
    have hw : Complex.exp (2 * Real.pi * Complex.I * (((1 / (l : ℚ) ^ m : ℚ)) : ℂ)) =
        Complex.exp (2 * Real.pi * Complex.I / ((l ^ m : ℕ) : ℂ)) := by
      congr 1; push_cast; ring
    haveI : NeZero ((l ^ m : ℕ) : Ω) := ⟨by exact_mod_cast hN⟩
    haveI : NeZero (l ^ m) := ⟨hN⟩
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hz' : IsPrimitiveRoot (ε z) (l ^ m) := hz.map_of_injective ε.injective
    have hp := Complex.isPrimitiveRoot_exp (l ^ m) hN
    obtain ⟨i, -, hi⟩ := hz'.eq_pow_of_pow_eq_one hp.pow_eq_one
    have hex : ∃ y, ε y = Complex.exp (2 * Real.pi * Complex.I * (((1 / (l : ℚ) ^ m : ℚ)) : ℂ)) :=
      ⟨z ^ i, by rw [map_pow, hi, hw]⟩
    show ε (Function.invFun ε _) = _
    rw [Function.invFun_eq hex, hw]
  refine ⟨?_, ?_⟩
  · rw [← IsPrimitiveRoot.map_iff_of_injective (f := ε) ε.injective, hkey]
    exact Complex.isPrimitiveRoot_exp _ (pow_ne_zero _ hl.ne')
  · apply ε.injective
    rw [map_pow, hkey, hkey, ← Complex.exp_nat_mul]
    congr 1
    have : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
    push_cast
    field_simp
    ring

theorem exists_cusp_embedding : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ∃ (Ωl : Type) (_ : Field Ωl) (_ : Algebra (O0 p) Ωl), IsClo p Ωl ∧ ∃ (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl), IsCusp ε A T j := by
  intro Ω _ _ _ ε X _ p _ _ A hA
  let Ωl := AlgebraicClosure (FractionRing (O0 p))
  have hcl : IsClo p Ωl := GlobalTheory.K5.Basic.isClo_algebraicClosure p
  haveI : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hcl
  haveI : IsAlgClosed Ωl := hcl.clo
  let j0 : Ω →+* Ωl := (IsAlgClosed.lift : Ω →ₐ[ℚ] Ωl).toRingHom
  have hBexists : ∃ B : ValuationSubring Ω, (p : Ω) ∈ B.nonunits ∧
      ∀ x, x ∈ B ↔ IsInt (p := p) (j0 x) := by
    obtain ⟨v, hv, _, _, hp⟩ := GlobalTheory.K5.exists_valuation_isInt p Ωl hcl
    let w := v.comap j0
    refine ⟨w.valuationSubring, ?_, fun x => ?_⟩
    · rw [ValuationSubring.mem_nonunits_iff, ← map_one w.valuationSubring.valuation,
        ← w.isEquiv_valuation_valuationSubring.lt_iff_lt, map_one]
      change v (j0 (p : Ω)) < 1
      rw [map_natCast]
      exact hp
    · rw [Valuation.mem_valuationSubring_iff]
      exact hv (j0 x)
  obtain ⟨B, hBp, hB⟩ := hBexists
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_algEquiv_map_valuationSubring_over_prime p A B hA hBp
  let j : Ω →+* Ωl := j0.comp σ.toRingEquiv.toRingHom
  have hint : ∀ x, x ∈ A ↔ IsInt (p := p) (j x) := fun x => (hσ x).symm.trans (hB _)
  have hl : 0 < p := (Fact.out : p.Prime).pos
  let T0 := (GlobalTheory.K5.Basic.nonempty_tower hcl).some
  let T : GlobalTheory.K5.Tower p Ωl :=
    { ζ := fun n => j (zt ε p n), qq := T0.qq,
      prim := fun n => (zt_prim_and_pow ε p n hl).1.map_of_injective j.injective,
      ζpow := fun n => by simp only [← map_pow, (zt_prim_and_pow ε p n hl).2],
      q0 := T0.q0, qpow := T0.qpow }
  have hdown : ∀ g : Gal p Ωl, ∃ s : Ω ≃ₐ[ℚ] Ω, Stab A s ∧ ∀ x, g (j x) = j (s x) := by
    exact GlobalTheory.CuspDown.exists_restrict p A Ωl hcl j hint
  refine ⟨Ωl, inferInstance, inferInstance, hcl, T, j, ?_⟩
  exact { int := hint, alg := isAlgZp_map_of_algebraic p Ωl j, root := fun n => rfl,
          dense := GlobalTheory.T.exists_algebraicNumber_congr_mod_prime_pow p A Ωl hcl j hint, down := hdown,
          up := fun n s hs => GlobalTheory.T.exists_local_aut_fixing_tower_param_of_stabilizes p A Ωl hcl j hint T n s hs }

end GlobalTheory.Glue
