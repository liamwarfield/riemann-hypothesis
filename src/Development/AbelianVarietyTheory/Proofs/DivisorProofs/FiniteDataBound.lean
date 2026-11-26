module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathLocalTotalTensorMemCoefficientField
public import Development.AutomorphicArithmetic.DivisorFrames.IsIntegralLocalGridTensorOfLevelChar
public import Development.AutomorphicArithmetic.LocalEmbeddings.FlipInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorUnfoldingIntegralValuationLossBound

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.AbsHcExponentLeAndAbsCenterLeOfSizeRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

theorem UpperTheory.abs_hc_exponent_le_and_abs_center_le_of_sizeRows :
    ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → HostHyp D → (∀ τ l, |(((D.hc τ).e l : ℚ) : ℝ)| ≤ 4 * large₂.sc.b) ∧ ∀ τ i, 1 ≤ i → i ≤ D.R.m → |((cen D 1 τ i : ℤ) : ℝ)| ≤ 2 * large₂.sc.b := by
  intro D large₂ hS hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hb, he, -⟩ := hS
  have hbpos : 0 < large₂.sc.b := by
    have := large₂.Sc_pos
    have : (0 : ℝ) ≤ (↑D.R.m + 1) * ↑(gap D 1) := by positivity
    linarith
  refine ⟨fun τ l => ?_, fun τ i hi him => ?_⟩
  · obtain ⟨hb0, he0⟩ := he τ l
    have hg := ((hH.gap τ l).1)
    have ht : (0 : ℚ) ≤ ((D.R.t : ℚ) + 3) / 2 := by positivity
    have hepos : (0 : ℚ) ≤ (D.hc τ).e l := by linarith
    have hepos' : (0 : ℝ) ≤ (((D.hc τ).e l : ℚ) : ℝ) := by exact_mod_cast hepos
    rw [abs_of_nonneg hepos']
    exact he0
  · set G := GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0 with hG
    have hcen : cen D 1 τ i = ⌊G.mid i⌋ := rfl
    have hmid : G.mid i = G.a i + (G.ga : ℚ) / 2 := G.mid_eq hi
    have ha : G.a i = (G.v 2 : ℚ) + 1 / 2 + ((G.m : ℚ) + 1 - i) * G.ga := rfl
    have hm : G.m = D.R.m := rfl
    have hga : G.ga = gap D 1 := rfl
    have hv : 0 ≤ G.v 2 ∧ ((G.v 2 : ℚ) : ℝ) ≤ large₂.Sc := by
      by_cases hk : 0 < D.R.k - 1
      · have hv2 : G.v 2 = ⌊(D.hc τ).v ⟨0, hk⟩⌋ := by
          simp [hG, GlobalTheory.SignedHC.GridData.ofHCParam, GlobalTheory.SignedHC.GridData.extend, hk]
        obtain ⟨h0, h1⟩ := large₂.cloud_v τ ⟨0, hk⟩
        have h0' : (0 : ℚ) ≤ (D.hc τ).v ⟨0, hk⟩ := by exact_mod_cast h0
        refine ⟨?_, ?_⟩
        · rw [hv2]
          exact Int.floor_nonneg.mpr h0'
        · rw [hv2]
          have hfl : ((⌊(D.hc τ).v ⟨0, hk⟩⌋ : ℤ) : ℚ) ≤ (D.hc τ).v ⟨0, hk⟩ := Int.floor_le _
          have hfl' : ((((⌊(D.hc τ).v ⟨0, hk⟩⌋ : ℤ) : ℚ)) : ℝ) ≤ (((D.hc τ).v ⟨0, hk⟩ : ℚ) : ℝ) := by
            exact_mod_cast hfl
          linarith
      · have hv2 : G.v 2 = 0 := by
          simp [hG, GlobalTheory.SignedHC.GridData.ofHCParam, GlobalTheory.SignedHC.GridData.extend, hk]
        rw [hv2]
        refine ⟨le_rfl, ?_⟩
        simpa using large₂.Sc_pos.le
    obtain ⟨hv0, hv1⟩ := hv
    have hi' : (1 : ℚ) ≤ i := by exact_mod_cast hi
    have him' : (i : ℚ) ≤ D.R.m := by exact_mod_cast him
    have hga0 : (0 : ℚ) ≤ G.ga := by positivity
    have hv0' : (0 : ℚ) ≤ G.v 2 := by exact_mod_cast hv0
    have hmid0 : 0 ≤ G.mid i := by
      rw [hmid, ha, hm]
      have : (0 : ℚ) ≤ ((D.R.m : ℚ) + 1 - i) * G.ga := mul_nonneg (by linarith) hga0
      linarith
    have hmid1 : ((G.mid i : ℚ) : ℝ) ≤ large₂.sc.b := by
      have e1 : ((G.mid i : ℚ) : ℝ) = ((G.v 2 : ℚ) : ℝ) + 1 / 2 + (((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ)) + (gap D 1 : ℝ) / 2 := by
        rw [hmid, ha, hm, hga]
        push_cast
        ring
      have hgr : (0 : ℝ) ≤ (gap D 1 : ℝ) := by positivity
      have hir : (1 : ℝ) ≤ i := by exact_mod_cast hi
      have : ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) + (gap D 1 : ℝ) / 2 ≤ ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) := by
        nlinarith
      linarith
    have hf0 : 0 ≤ cen D 1 τ i := by
      rw [hcen]
      exact Int.floor_nonneg.mpr hmid0
    have hf1 : ((cen D 1 τ i : ℤ) : ℝ) ≤ large₂.sc.b := by
      rw [hcen]
      have hfl : ((⌊G.mid i⌋ : ℤ) : ℚ) ≤ G.mid i := Int.floor_le _
      have hfl' : ((((⌊G.mid i⌋ : ℤ) : ℚ)) : ℝ) ≤ ((G.mid i : ℚ) : ℝ) := by exact_mod_cast hfl
      have : (((⌊G.mid i⌋ : ℤ)) : ℝ) = ((((⌊G.mid i⌋ : ℤ) : ℚ)) : ℝ) := by push_cast; rfl
      linarith
    have hf0' : (0 : ℝ) ≤ ((cen D 1 τ i : ℤ) : ℝ) := by exact_mod_cast hf0
    rw [abs_of_nonneg hf0']
    linarith
end

section -- merged from Development.AutomorphicArithmetic.LocalEmbeddings.FlipVal
section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ExistsPowLocKMulInfEqOneOfLevelLeTwo
open NumberField IsDedekindDomain

section
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

private theorem locK_eq_one_of_two (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.LevelLe v 2) (y : Lˣ)
    (h2 : v.valuation L (y : L) = 1) (h1 : v.valuation L ((y : L) - 1) ≤ WithZero.exp (-2 : ℤ)) :
    χ.locK v y = 1 := by
  have hval : ∀ k : L, Valued.v (algebraMap L (v.adicCompletion L) k) = v.valuation L k := fun k =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  refine h (atFin v y) ((hval _).trans h2) ?_
  have : ((atFin v y : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 =
      algebraMap L (v.adicCompletion L) ((y : L) - 1) := by
    rw [map_sub, map_one]; rfl
  rw [this, hval]
  simpa using h1

private theorem exists_pow_sub_one_mem_two (v : HeightOneSpectrum (𝓞 L)) :
    ∃ m : ℕ, 0 < m ∧ ∀ r : 𝓞 L, r ∉ v.asIdeal → r ^ m - 1 ∈ v.asIdeal ^ 2 := by
  have hfin : Finite (𝓞 L ⧸ v.asIdeal ^ 2) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero 2 v.ne_bot)
  have hmax := v.isMaximal
  refine ⟨Nat.card (𝓞 L ⧸ v.asIdeal ^ 2)ˣ, Nat.card_pos, fun r hr => ?_⟩
  have h0 : IsUnit (Ideal.Quotient.mk (v.asIdeal ^ 2) r) := by
    obtain ⟨y, i, hi, e⟩ := hmax.exists_inv hr
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk (v.asIdeal ^ 2) (y * (1 + i))) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (v.asIdeal ^ 2)), Ideal.Quotient.eq]
    have : r * (y * (1 + i)) - 1 = -(i ^ 2) := by
      linear_combination (1 + i) * e
    rw [this]
    exact neg_mem (Ideal.pow_mem_pow hi 2)
  have h1 := congrArg Units.val (pow_card_eq_one' (x := h0.unit))
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
  rwa [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h1

private theorem exists_pow_locK_two (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.LevelLe v 2) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : Lˣ, v.valuation L (u : L) = 1 → χ.locK v u ^ m = 1 := by
  obtain ⟨m, hm, hpow⟩ := exists_pow_sub_one_mem_two v
  refine ⟨m, hm, fun u hu => ?_⟩
  obtain ⟨r, s, hs, hsr⟩ := (intAt_iff (P := v) (u : L)).2 hu.le
  have hsv : v.valuation L (algebraMap (𝓞 L) L s) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hs]
  have hr : r ∉ v.asIdeal := by
    rw [← HeightOneSpectrum.intValuation_eq_one_iff, ← HeightOneSpectrum.valuation_of_algebraMap (K := L)]
    show v.valuation L (algebraMap (𝓞 L) L r) = 1
    rw [← hsr, map_mul, hsv, hu, one_mul]
  have hs0 : algebraMap (𝓞 L) L s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hsv
    exact zero_ne_one hsv
  have hle : ∀ t : 𝓞 L, t ∉ v.asIdeal →
      v.valuation L (algebraMap (𝓞 L) L (t ^ m - 1)) ≤ WithZero.exp (-2 : ℤ) := by
    intro t ht
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    have h2 := (HeightOneSpectrum.intValuation_le_pow_iff_mem v _ 2).2 (hpow t ht)
    simpa using h2
  rw [← map_pow]
  apply locK_eq_one_of_two χ h
  · rw [Units.val_pow_eq_pow_val, map_pow, hu, one_pow]
  · have hu' : ((u ^ m : Lˣ) : L) - 1 = (algebraMap (𝓞 L) L (r ^ m - 1) -
        algebraMap (𝓞 L) L (s ^ m - 1)) / (algebraMap (𝓞 L) L s) ^ m := by
      simp only [map_sub, map_pow, map_one, Units.val_pow_eq_pow_val]
      rw [eq_div_iff (pow_ne_zero _ hs0), ← hsr]
      ring
    rw [hu', map_div₀, map_pow, hsv, one_pow, div_one]
    exact le_trans (Valuation.map_sub _ _ _) (max_le (hle r hr) (hle s hs))

end

open Formalism.L2.Host in
theorem UpperTheory.exists_pow_locK_mul_inf_eq_one_of_levelLe_two :
    ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ v, v ∉ S → χ.UnrAt v) → (∀ v, χ.LevelLe v 2) → ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ), ∃ (M : ℕ) (z : Eˣ), 0 < M ∧ P.valuation E (z : E) = P.valuation E (k : E) ^ M ∧ (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E (z : E) = 1) ∧ χ.locK P k ^ M * χ.inf z = 1 := by
  intro E _ _ χ S hS hlev P k
  classical
  obtain ⟨h, a, hh, haP, haQ⟩ := GlobalTheory.TamePow.exists_gen P
  obtain ⟨c, hc⟩ : ∃ c : ℤ, P.valuation E (k : E) = WithZero.exp c :=
    ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 k.ne_zero)).symm⟩
  choose mf hmf hmu using fun v => exists_pow_locK_two χ (hlev v)
  have hPS : P ∈ S ∪ {P} := by simp
  obtain ⟨N, hN⟩ : ∃ N, N = ∏ v ∈ (S ∪ {P}).erase P, mf v := ⟨_, rfl⟩
  have hNpos : 0 < N := by
    rw [hN]
    exact Finset.prod_pos (fun v _ => hmf v)
  have hrule := Formalism.L2.Host.HChar.productRule χ (S ∪ {P})
    (fun v hv => hS v (fun h' => hv (Finset.mem_union_left _ h'))) a
  have hfin : ∏ᶠ (v) (_ : v ∉ S ∪ {P}), χ.val v ^ ordF v a = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [finprod_eq_if]
    split_ifs with hv
    · rfl
    · have hvP : v ≠ P := fun e => hv (by simp [e])
      have h0 : ordF v a = 0 := by
        simp [Formalism.L2.Host.ordF, haQ v hvP]
      rw [h0, zpow_zero]
  rw [hfin, mul_one, ← Finset.mul_prod_erase (S ∪ {P}) (fun v => χ.locK v a) hPS, ← mul_assoc] at hrule
  have hrest : (∏ v ∈ (S ∪ {P}).erase P, χ.locK v a) ^ N = 1 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro v hv
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem mf hv
    rw [hN, hd, pow_mul, hmu v a (haQ v (Finset.ne_of_mem_erase hv)), one_pow]
  have hA : (χ.inf a * χ.locK P a) ^ N = 1 := by
    have hp := congrArg (fun z => z ^ N) hrule
    rw [mul_pow, hrest, mul_one, one_pow] at hp
    exact hp
  have hw : P.valuation E ((k ^ h * a ^ c : Eˣ) : E) = 1 := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, map_mul, map_pow,
      map_zpow₀, hc, haP, ← WithZero.exp_nsmul, ← WithZero.exp_zsmul, ← WithZero.exp_add,
      WithZero.exp_eq_one]
    simp only [nsmul_eq_mul, smul_eq_mul]
    ring
  have hwm := hmu P _ hw
  rw [map_mul, map_pow, map_zpow] at hwm
  have htpos : 0 < mf P * N := Nat.mul_pos (hmf P) hNpos
  refine ⟨h * (mf P * N), a ^ (-(c * ((mf P * N : ℕ) : ℤ))), Nat.mul_pos hh htpos, ?_, ?_, ?_⟩
  · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, haP, hc, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul,
      WithZero.exp_inj]
    simp only [nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring
  · intro Q hQ
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, haQ Q hQ, one_zpow]
  · rw [map_zpow]
    have e1 : χ.locK P k ^ (((h * (mf P * N) : ℕ)) : ℤ) * χ.locK P a ^ (c * ((mf P * N : ℕ) : ℤ)) = 1 := by
      have hp := congrArg (fun z => z ^ N) hwm
      simp only [one_pow] at hp
      rw [← hp, ← pow_mul, ← zpow_natCast, mul_zpow, ← zpow_natCast (χ.locK P k) h, ← zpow_mul,
        ← zpow_mul]
      congr 2 <;> push_cast <;> ring
    have e2 : χ.inf a ^ (c * ((mf P * N : ℕ) : ℤ)) * χ.locK P a ^ (c * ((mf P * N : ℕ) : ℤ)) = 1 := by
      rw [← mul_zpow, show c * ((mf P * N : ℕ) : ℤ) = (N : ℤ) * (c * mf P) by push_cast; ring,
        zpow_mul, zpow_natCast, hA, one_zpow]
    rw [← zpow_natCast, eq_inv_of_mul_eq_one_left e1, zpow_neg, eq_inv_of_mul_eq_one_left e2,
      inv_inv, inv_mul_cancel]
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.IsIntegralCmTypeUnitaryPartMulAbsNormPow
open NumberField IsDedekindDomain

private lemma isIntegral_pow_div_mul_pow (a b : ℂ) (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (n : ℤ) (M : ℕ) (hn : n.natAbs ≤ M) :
    IsIntegral ℤ ((a / b) ^ n * (a * b) ^ M) := by
  have hbk : ∀ k : ℕ, b ^ k * b⁻¹ ^ k = 1 := fun k => by rw [← mul_pow, mul_inv_cancel₀ hb0, one_pow]
  have hak : ∀ k : ℕ, a ^ k * a⁻¹ ^ k = 1 := fun k => by rw [← mul_pow, mul_inv_cancel₀ ha0, one_pow]
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp only [Int.natAbs_natCast] at hn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    have e : (a / b) ^ (k : ℤ) * (a * b) ^ (k + d) = a ^ (k + k + d) * b ^ d * (b ^ k * b⁻¹ ^ k) := by
      rw [zpow_natCast, div_eq_mul_inv]
      ring
    rw [e, hbk, mul_one]
    exact (ha.pow _).mul (hb.pow _)
  · simp only [Int.natAbs_neg, Int.natAbs_natCast] at hn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    have e : (a / b) ^ (-(k : ℤ)) * (a * b) ^ (k + d) = a ^ d * b ^ (k + k + d) * (a ^ k * a⁻¹ ^ k) := by
      rw [zpow_neg, ← inv_zpow, inv_div, zpow_natCast, div_eq_mul_inv]
      ring
    rw [e, hak, mul_one]
    exact (ha.pow _).mul (hb.pow _)

private lemma div_abs_sq_eq_div_conj (a : ℂ) (ha0 : a ≠ 0) :
    (a / ((‖a‖ : ℝ) : ℂ)) ^ 2 = a / (starRingEnd ℂ) a := by
  have hn : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, norm_eq_zero]
    exact ha0
  have hc : (starRingEnd ℂ) a ≠ 0 := (map_ne_zero _).mpr ha0
  rw [div_pow, ← Complex.mul_conj' a]
  field_simp

private lemma span_eq_pow_of_valuation_supported_at (E : Type) [Field E] [NumberField E]
    (P : HeightOneSpectrum (𝓞 E)) (h : ℕ) (a : 𝓞 E) (ha : a ≠ 0)
    (h1 : P.valuation E (a : E) = WithZero.exp (-(h : ℤ)))
    (h2 : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E (a : E) = 1) :
    Ideal.span {a} = P.asIdeal ^ h := by
  have h1' : P.intValuation a = WithZero.exp (-(h : ℤ)) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    exact h1
  have h2' : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.intValuation a = 1 := by
    intro Q hQ
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    exact h2 Q hQ
  obtain ⟨J, hJ⟩ := (P.intValuation_le_pow_iff_dvd a h).mp h1'.le
  rw [hJ]
  suffices hJt : J = ⊤ by rw [hJt, Ideal.mul_top]
  by_contra hne
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
  have hspan0 : Ideal.span {a} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact ha
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hJ
    exact hspan0 hJ
  have hM0 : M ≠ ⊥ := fun hb => hJ0 (le_bot_iff.mp (hb ▸ hJM))
  let Q : HeightOneSpectrum (𝓞 E) := ⟨M, hM.isPrime, hM0⟩
  have hQJ : Q.asIdeal ∣ J := Ideal.dvd_iff_le.mpr hJM
  by_cases hQP : Q = P
  · have hPJ : P.asIdeal ∣ J := hQP ▸ hQJ
    have hdvd : P.asIdeal ^ (h + 1) ∣ Ideal.span {a} := by
      rw [hJ, pow_succ]
      exact mul_dvd_mul_left _ hPJ
    have hv := (P.intValuation_le_pow_iff_dvd a (h + 1)).mpr hdvd
    rw [h1', WithZero.exp_le_exp] at hv
    push_cast at hv
    omega
  · have hlt : Q.intValuation a < 1 := by
      rw [Q.intValuation_lt_one_iff_dvd, hJ]
      exact dvd_mul_of_dvd_right hQJ _
    rw [h2' Q hQP] at hlt
    exact lt_irrefl _ hlt

private lemma absNorm_span_sq_eq_prod_embeddings_sq (E : Type) [Field E] [NumberField E] (a : 𝓞 E) :
    ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℂ) ^ 2 = (∏ σ : E →+* ℂ, σ (a : E)) ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have h1 : ((((Algebra.norm ℤ) a).natAbs : ℕ) : ℂ) ^ 2 = (((Algebra.norm ℤ a : ℤ)) : ℂ) ^ 2 := by
    rw [← Int.cast_natCast, ← Int.cast_pow, Int.natAbs_sq, Int.cast_pow]
  rw [h1]
  congr 1
  have h2 : (((Algebra.norm ℤ a : ℤ)) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ (a : E)) := by
    rw [← Algebra.coe_norm_int]
    simp
  rw [h2, Algebra.norm_eq_prod_embeddings ℚ ℂ]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ (fun σ => rfl)

theorem UpperTheory.isIntegral_cmType_unitaryPart_mul_absNorm_pow :
    ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), Function.Injective (Sum.elim φ fun i => ComplexEmbedding.conjugate (φ i)) → ∀ (n : I → ℤ) (M : ℕ), (∀ i, (n i).natAbs ≤ M) → ∀ (P : HeightOneSpectrum (𝓞 E)) (h : ℕ) (z : Eˣ), P.valuation E (z : E) = WithZero.exp (-(h : ℤ)) → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E (z : E) = 1) → IsIntegral ℤ ((∏ i, (φ i (z : E) / ((‖φ i (z : E)‖ : ℝ) : ℂ)) ^ n i) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (h * M)) := by
  intro E _ _ I _ φ hinj n M hn P h z hP hQ
  classical
  have hle : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (z : E) ≤ 1 := by
    intro v
    by_cases hv : v = P
    · subst hv
      rw [hP, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    · rw [hQ v hv]
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (z : E) hle
  have hza : (z : E) = (a : E) := ha.symm
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact z.ne_zero ha.symm
  have hspan := span_eq_pow_of_valuation_supported_at E P h a ha0 (by rw [← hza]; exact hP) (fun Q hQP => by rw [← hza]; exact hQ Q hQP)
  have hnorm : ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (2 * h) = (∏ σ : E →+* ℂ, σ (a : E)) ^ 2 := by
    rw [← absNorm_span_sq_eq_prod_embeddings_sq E a, hspan, map_pow]
    push_cast
    ring
  have haE : (a : E) ≠ 0 := hza ▸ z.ne_zero
  have hint : ∀ σ : E →+* ℂ, IsIntegral ℤ (σ (a : E)) := fun σ =>
    (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
  have hw0 : ∀ i, φ i (a : E) ≠ 0 := fun i => (map_ne_zero _).mpr haE
  have hwc0 : ∀ i, (starRingEnd ℂ) (φ i (a : E)) ≠ 0 := fun i => (map_ne_zero _).mpr (hw0 i)
  have hzp : ∀ (x : ℂ) (k : ℤ), (x ^ k) ^ 2 = (x ^ 2) ^ k := fun x k => by
    rw [← zpow_natCast, ← zpow_natCast x, ← zpow_mul, ← zpow_mul, mul_comm]
  rw [hza]
  apply IsIntegral.of_pow (n := 2) two_pos
  have e1 : ((∏ i, (φ i (a : E) / ((‖φ i (a : E)‖ : ℝ) : ℂ)) ^ n i) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (h * M)) ^ 2
      = (∏ i, (φ i (a : E) / (starRingEnd ℂ) (φ i (a : E))) ^ n i) * ((∏ σ : E →+* ℂ, σ (a : E)) ^ 2) ^ M := by
    rw [mul_pow, ← Finset.prod_pow, ← hnorm]
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      rw [hzp, div_abs_sq_eq_div_conj _ (hw0 i)]
    · ring
  let e : I ⊕ I ↪ (E →+* ℂ) := ⟨Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i)), hinj⟩
  have hsplit : ∏ σ : E →+* ℂ, σ (a : E)
      = (∏ i, φ i (a : E) * (starRingEnd ℂ) (φ i (a : E))) * ∏ σ ∈ Finset.univ \ Finset.univ.map e, σ (a : E) := by
    rw [← Finset.prod_sdiff (Finset.subset_univ (Finset.univ.map e)), Finset.prod_map, Fintype.prod_sum_type,
      ← Finset.prod_mul_distrib, mul_comm]
    rfl
  rw [e1, hsplit]
  have e2 : (∏ i, (φ i (a : E) / (starRingEnd ℂ) (φ i (a : E))) ^ n i) *
      (((∏ i, φ i (a : E) * (starRingEnd ℂ) (φ i (a : E))) * ∏ σ ∈ Finset.univ \ Finset.univ.map e, σ (a : E)) ^ 2) ^ M
      = (∏ i, (φ i (a : E) / (starRingEnd ℂ) (φ i (a : E))) ^ n i * (φ i (a : E) * (starRingEnd ℂ) (φ i (a : E))) ^ (2 * M))
        * (∏ σ ∈ Finset.univ \ Finset.univ.map e, σ (a : E)) ^ (2 * M) := by
    simp only [Finset.prod_mul_distrib, Finset.prod_pow]
    ring
  rw [e2]
  apply IsIntegral.mul
  · apply IsIntegral.prod
    intro i _
    exact isIntegral_pow_div_mul_pow _ _ (hint (φ i)) (hint (ComplexEmbedding.conjugate (φ i))) (hw0 i) (hwc0 i) (n i) (2 * M)
      (by have := hn i; omega)
  · apply IsIntegral.pow
    apply IsIntegral.prod
    intro σ _
    exact hint σ
end

open NumberField IsDedekindDomain
open Formalism.DivisionValues (vw)

namespace UpperTheory.FlipVal

theorem vw_ge {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {y : K} (hy : y ≠ 0) {q : ℕ} (hq : q ≠ 0)
    (n : ℕ) (h : IsIntegral ℤ ((q : K) ^ n * y)) : -((n : ℤ) * vw w (q : K)) ≤ vw w y := by
  have hq' : (q : K) ≠ 0 := by exact_mod_cast hq
  have h0 : 0 ≤ vw w ((q : K) ^ n * y) := by
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = (q : K) ^ n * y := ⟨⟨_, h⟩, rfl⟩
    rw [← ha, vw, ← FractionalIdeal.coeIdeal_span_singleton]
    exact FractionalIdeal.count_coe_nonneg K w _
  rw [vw, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_pow,
    FractionalIdeal.count_mul K w (pow_ne_zero _ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hq'))
      (FractionalIdeal.spanSingleton_ne_zero_iff.2 hy), FractionalIdeal.count_pow] at h0
  unfold vw
  linarith

theorem vw_nat_nonneg {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (q : ℕ) : 0 ≤ vw w (q : K) := by
  rw [← map_natCast (algebraMap (𝓞 K) K), vw, ← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg K w _

theorem vw_absNorm {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 K))
    (P : HeightOneSpectrum (𝓞 E)) (h : ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    vw w ((Ideal.absNorm P.asIdeal : ℕ) : K) = 0 := by
  have hfin : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hmax := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 E ⧸ P.asIdeal) (ringChar (𝓞 E ⧸ P.asIdeal))
  have h1 : Ideal.absNorm P.asIdeal = Formalism.EigenvalueLevelCeiling.plc P ^ (n : ℕ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hn]; rfl
  have h2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 K) ∉ w.asIdeal := by
    rw [h1, Nat.cast_pow]; exact fun h' => h (w.isPrime.mem_of_pow_mem _ h')
  have h3 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 K) ≠ 0 := fun h' => h2 (h' ▸ zero_mem _)
  rw [← map_natCast (algebraMap (𝓞 K) K), vw, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K w (by simpa using h3)]
  by_contra h4
  refine h2 ((Ideal.dvd_span_singleton).1 ?_)
  exact (Associates.count_ne_zero_iff_dvd (by simpa using h3) w.irreducible).1 (by exact_mod_cast h4)

theorem val_int {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ v, v ∉ S → χ.UnrAt v) (hl : ∀ v, χ.LevelLe v 2) {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (hφ : Function.Injective (Sum.elim φ fun i => ComplexEmbedding.conjugate (φ i))) (n : I → ℤ) (hn : χ.HasInf φ n)
    (M : ℕ) (hM : ∀ i, (n i).natAbs ≤ M) (P : HeightOneSpectrum (𝓞 E)) :
    IsIntegral ℤ (((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ M * (χ.val P : ℂ)) ∧
      IsIntegral ℤ (((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ M * (χ.val P : ℂ)⁻¹) := by
  obtain ⟨h, z, h0, hP, hQ, H⟩ := UpperTheory.exists_pow_locK_mul_inf_eq_one_of_levelLe_two E χ S hS hl P (Formalism.L2.Host.unif P)
  have hu : P.valuation E (Formalism.L2.Host.unif P : E) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _).symm.trans (Formalism.L2.Host.unif_spec P)
  rw [hu, ← WithZero.exp_nsmul, show h • (-1 : ℤ) = -(h : ℤ) by simp] at hP
  have H' : (χ.val P : ℂ) ^ h * ∏ i, (φ i (z : E) / ((‖φ i (z : E)‖ : ℝ) : ℂ)) ^ n i = 1 := by
    rw [← hn z]; exact congrArg Units.val H
  constructor
  · refine IsIntegral.of_pow h0 ?_
    have := UpperTheory.isIntegral_cmType_unitaryPart_mul_absNorm_pow E I φ hφ (fun i => -n i) M (fun i => by simpa using hM i) P h z hP hQ
    simp only [zpow_neg, Finset.prod_inv_distrib] at this
    rwa [← eq_inv_of_mul_eq_one_left H', mul_comm, mul_comm h, pow_mul, ← mul_pow] at this
  · refine IsIntegral.of_pow h0 ?_
    have := UpperTheory.isIntegral_cmType_unitaryPart_mul_absNorm_pow E I φ hφ n M hM P h z hP hQ
    rwa [eq_inv_of_mul_eq_one_right H', mul_comm, mul_comm h, pow_mul, ← inv_pow, ← mul_pow] at this

end UpperTheory.FlipVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlipsLossBoundedAtExceptionalPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

section SlopeTestRemainingChoices

open ValuativeRel UpperTheory.FlipInt UpperTheory.FlipVal

private theorem psi_int {D : D7} {w : Pl D.host.E} {ψ : AddChar (Kw w) Circle} (hc : HasConductor ψ 1) (n : ℕ) (x : Kw w)
    (hx : valuation (Kw w) ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1) : IsIntegral ℤ (ψ x : ℂ) := by
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))
  set q := Ideal.absNorm w.asIdeal
  have hq0 : q ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot
  have hq : Valued.v ((q : ℕ) : Kw w) ≤ WithZero.exp (-1 : ℤ) := by
    have hmem : ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal ^ 1 := by rw [pow_one]; exact Ideal.absNorm_mem w.asIdeal
    have h2 : Valued.v ((q : ℕ) : Kw w) = w.intValuation ((q:ℕ) : 𝓞 D.host.E) := by
      rw [← map_natCast (algebraMap (𝓞 D.host.E) (Kw w))]
      exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.E) w _).trans
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _)
    rw [h2]
    have := (w.intValuation_le_pow_iff_mem ((q:ℕ) : 𝓞 D.host.E) 1).2 hmem
    simpa using this
  have hu : Valued.v ((unifAt w : (Kw w)ˣ) : Kw w) = WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec w
  have hx' : Valued.v ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1 := by
    have := (e ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) 1).1 (by rw [map_one]; exact hx)
    rwa [map_one] at this
  have hNx : Valued.v (((q ^ n : ℕ) : Kw w) * x) ≤ 1 := by
    refine le_trans ?_ hx'
    rw [map_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Nat.cast_pow, map_pow, hu]
    gcongr
  have hNx2 : valuation (Kw w) (((q ^ n : ℕ) : Kw w) * x) ≤ valuation (Kw w) 1 :=
    (e (((q ^ n : ℕ) : Kw w) * x) 1).2 (by rw [map_one]; exact hNx)
  have h1 : ψ ((q ^ n) • x) = 1 := by
    rw [nsmul_eq_mul]
    exact (hc 1).2 (by simp) _ hNx2
  refine IsIntegral.of_pow (Nat.pos_of_ne_zero (pow_ne_zero n hq0)) ?_
  rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, h1, Circle.coe_one]
  exact isIntegral_one

private theorem emb_inj (D : D7) : Function.Injective
    (Sum.elim (Formalism.L2.Host.embTau D) fun i => ComplexEmbedding.conjugate (Formalism.L2.Host.embTau D i)) := by
  have h1 : Function.Injective (Formalism.L2.Host.embTau D) := GlobalTheory.Survey.EmbeddingValuationsAnti.embTau_injective D
  have h2 : ∀ τ τ', ComplexEmbedding.conjugate (Formalism.L2.Host.embTau D τ) ≠ Formalism.L2.Host.embTau D τ' := fun τ τ' h =>
    GlobalTheory.Survey.EmbeddingValuationsAnti.embTau_ne_bar D τ τ' ((RingHom.ext fun _ => rfl).trans h)
  refine h1.sumElim (fun a b h => h1 (star_injective h)) fun a b h => h2 b a h.symm

private theorem lev_two {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {v : HeightOneSpectrum (𝓞 E)}
    (h : χ.LevelLe v 1) : χ.LevelLe v 2 :=
  fun x hx h' => h x hx (h'.trans (WithZero.exp_le_exp.2 (by norm_num)))

private theorem nu_int {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀)
    (large₂ : SizeData₂ D) (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (hH : HostHyp D) (hc : sc.cGap = 1) (t : T) (w : Pl D.host.E)
    {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) :
    ((locGrid G t w).nu i j (unifAt w) : ℂ) ∈ Lo (Ideal.absNorm w.asIdeal) (2 * ⌊8 * large₂.sc.b⌋₊) ∧
      ((locGrid G t w).nu i j (unifAt w)⁻¹ : ℂ) ∈ Lo (Ideal.absNorm w.asIdeal) (2 * ⌊8 * large₂.sc.b⌋₊) := by
  classical
  obtain ⟨b1, b2⟩ := UpperTheory.abs_hc_exponent_le_and_abs_center_le_of_sizeRows D large₂ hS hH
  have h12 := (GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS).2.2.2.2.2.2.2
  have e1 : (((locGrid G t w).nu i j (unifAt w) : ℂˣ) : ℂ) =
      ((L.C.mu0 ⟨j, hj⟩).val w : ℂ) * ((L.xiH t).val w : ℂ) * (((G.ch.chiH (D.R.m - i)).val w : ℂ))⁻¹ := by
    simp only [Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Units.val_div_eq_div_val, div_eq_mul_inv]
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  have hμ := L.C.isMu0 ⟨j, hj⟩
  obtain ⟨n, hn, hinf⟩ := GlobalTheory.Chain.StepVac.hasInfQ_tau hμ.inf
  have hg0 : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ≠ 0 := by
    exact_mod_cast mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  obtain ⟨m1, m2⟩ := val_int (L.C.mu0 ⟨j, hj⟩) (Formalism.L2.DIV.primesOf ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E))
    (fun v hv => hμ.unr v fun k hk => hv (by
      rw [Formalism.L2.DIV.mem_primesOf, and_iff_right hg0, Nat.cast_mul, v.isPrime.mul_mem_iff_mem_or_mem]
      fin_cases k
      exacts [Or.inl hk, Or.inr hk])) (fun v => lev_two (hμ.tame v)) (Formalism.L2.Host.embTau D) (emb_inj D) n hinf
    ⌊8 * large₂.sc.b⌋₊ (fun τ => Nat.le_floor (by
      have h1 := hn τ
      simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
      have h2 : (n τ : ℝ) = 2 * -(((D.hc τ).e ⟨j, hj⟩ : ℚ) : ℝ) := by exact_mod_cast h1
      have h3 := b1 τ ⟨j, hj⟩
      rw [Nat.cast_natAbs, Int.cast_abs, h2, abs_mul, abs_neg, abs_two]
      linarith)) w
  have hi1 : 1 ≤ D.R.m - i := by omega
  have hi2 : D.R.m - i ≤ D.R.m := by omega
  obtain ⟨c1, c2⟩ := val_int (G.ch.chiH (D.R.m - i)) (G.pl.S0.biUnion (Formalism.L2.Host.aboveF (L := D.host.E) D.host.F))
    (fun v hv => G.ch.unr _ hi1 hi2 v fun h => hv (Finset.mem_biUnion.2 ⟨_, h, by simp [Formalism.L2.Host.aboveF]⟩))
    (fun v => by
      by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
      · rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
        · exact lev_two (G.ch.lev0 _ hi1 hi2 v h).1
        · exact (G.ch.lev1 _ hi1 hi2 v h).1
      · exact fun x hx _ => G.ch.unr _ hi1 hi2 v h x hx) (Formalism.L2.Host.embTau D) (emb_inj D) _ (G.ch.inf _ hi1 hi2)
    ⌊8 * large₂.sc.b⌋₊ (fun τ => Nat.le_floor (by
      have h3 := b2 τ _ hi1 hi2
      rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_mul, abs_mul, Int.cast_ofNat, abs_two, hc]
      linarith)) w
  obtain ⟨N, hN, hord⟩ := hL.xi_fin t
  have hx : ((L.xiH t).val w : ℂ) ^ N = 1 := by
    have h1 : ((L.xiH t) ^ N).val w = 1 := by rw [show (L.xiH t) ^ N = 1 from hord]; rfl
    have h2 : ((L.xiH t) ^ N).val w = (L.xiH t).val w ^ N := rfl
    rw [← Units.val_pow_eq_pow_val, ← h2, h1, Units.val_one]
  have x1 : IsIntegral ℤ ((L.xiH t).val w : ℂ) := IsIntegral.of_pow hN (by rw [hx]; exact isIntegral_one)
  have x2 : IsIntegral ℤ ((L.xiH t).val w : ℂ)⁻¹ := IsIntegral.of_pow hN (by rw [inv_pow, hx, inv_one]; exact isIntegral_one)
  rw [map_inv, Units.val_inv_eq_inv_val, e1, two_mul]
  refine ⟨Lo_mul (Lo_mul (b := 0) (mem_Lo.2 m1) (Lo_zero x1)) (mem_Lo.2 c2), ?_⟩
  rw [mul_inv, mul_inv, inv_inv]
  exact Lo_mul (Lo_mul (b := 0) (mem_Lo.2 m2) (Lo_zero x2)) (mem_Lo.2 c1)

end SlopeTestRemainingChoices

theorem _root_.GlobalTheory.T.flips_loss_bounded_at_exceptional_places : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ c₁ : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK →
      ∀ (t : T) (Φ : ch.G.Datum) (P : Pl D.host.E), P ∈ locPl ch.G t → ∀ w : PlL D,
        (P ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal) →
        ∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) (c₁ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * large₂.sc.b * (cosExp ch.G P : ℝ) *
          (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ)) := by
  refine ⟨0, fun CF _ => ⟨56, fun ε => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc hF t Φ w hw la hla z
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hg := (Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w hw
  have hadm := GivenAdm.givenStage_isAdmissible hL ch.S.B t Φ hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hq : resCard (Kw w) = Ideal.absNorm w.asIdeal := GlobalTheory.LFun.SatBoundGL.resCard_completion w
  have hq0 : resCard (Kw w) ≠ 0 := by rw [hq]; exact Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot
  have hgap : ch.sc.cGap = 1 := by rw [show ch.sc = _ from hsc]
  have hfl : ∀ x ∈ flipOrder D.R.m, x.1 < D.R.m ∧ x.2 < D.R.m ∧
      CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G t w).nu x.1 x.2) ∧ ¬ IsUnram ((locGrid ch.G t w).nu x.1 x.2) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    have hs := hg.square i hi j hj
    have e := (locGrid ch.G t w).alpha_div_beta i j
    exact ⟨hi, hj, by rw [← e]; exact hs.condν, by rw [← e]; exact hs.ram⟩

  let K : Subfield ℂ := D.what₂.embLL.fieldRange
  have hK : ∀ y, y ∈ Set.range D.what₂.embLL → y ∈ K := fun y hy => RingHom.mem_fieldRange.2 hy
  have hmu : ∀ j x, ((R.toLevCh.C.mu0 j).loc w x : ℂ) ∈ K := fun j x => hK _ (hF.chars.mu0 j w x)
  have hxi : ∀ x, ((R.toLevCh.xiH t).loc w x : ℂ) ∈ K := fun x => hK _ (hF.chars.xi t w x)
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, ((ch.G.ch.chiH i).loc w x : ℂ) ∈ K :=
    fun i a b x => hK _ (hF.chars.chi i a b w x)
  have habs : ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ K :=
    GlobalTheory.TflipField.apow_half_mem K w (hK _ (hF.sqrt w (.inr ⟨t, hw⟩)))
  have hψ := GlobalTheory.TflipField.psiAt_mem (W := ch.W) K (fun z hz => hK _ (hF.roots t w hw z hz)) h00.cond
  obtain ⟨y, hy⟩ : ∃ y, D.what₂.embLL y = Tflip ch.W ch.S.B t Φ w z :=
    RingHom.mem_fieldRange.1 (GlobalTheory.TflipField.flips_mem K h00.unif h00.cond h00.one_le habs hψ (flipOrder D.R.m)
      (givenStage t w ch.S.B Φ)
      (fun x hx => ⟨(hfl x hx).2.2.1, (hfl x hx).2.2.2, GlobalTheory.TflipField.nu_mem K t w hmu hxi hchi (hfl x hx).1 (hfl x hx).2.1⟩)
      (canFlip_flipOrder _).1 (fun X => GivenAdm.givenLevel_open hL hw X) hadm.tensor
      (GlobalTheory.TflipField.givenStage_mem K ch.S.B t Φ w hmu hxi) z)

  have key : Tflip ch.W ch.S.B t Φ w z ∈ UpperTheory.FlipInt.Lo (resCard (Kw w)) (0 + (flipOrder D.R.m).length *
      (depthAt ch.G w * bigN D * (3 * (2 * ⌊8 * large₂.sc.b⌋₊) + 8 * bigN D))) := by
    refine UpperTheory.FlipInt.flips_mem h00.unif h00.cond h00.one_le hq0 (psi_int h00.cond _) (flipOrder D.R.m)
      (givenStage t w ch.S.B Φ) 0 (fun x hx => ?_) (canFlip_flipOrder _).1 (fun X => GivenAdm.givenLevel_open hL hw X) hadm
      (fun z => UpperTheory.FlipInt.Lo_zero (UpperTheory.isIntegral_localGrid_tensor_of_levelChar hL ch.S.B t Φ w z)) z
    obtain ⟨hi, hj, h1, h2⟩ := hfl x hx
    have h3 := nu_int ch.G hL large₂ hS.size hS.host hgap t w hi hj
    rw [← hq] at h3
    refine ⟨h1, h2, h3.1, h3.2, ?_⟩
    change D.R.r + (x.2 + 1) * D.R.t + (x.1 + 1) * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have a1 : (x.2 + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
    have a2 : (x.1 + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
    have a3 : D.R.r ≤ D.R.k + D.R.m := by unfold Ranks.r; omega
    rw [mul_add, mul_add]; omega
  rw [zero_add, (canFlip_flipOrder _).2.1, UpperTheory.FlipInt.mem_Lo, ← hy, ← map_natCast D.what₂.embLL, ← map_pow, ← map_mul] at key
  replace key := (isIntegral_algHom_iff D.what₂.embLL.toIntAlgHom D.what₂.embLL.injective).1 key
  refine ⟨y, hy, ?_⟩
  by_cases hy0 : y = 0
  · exact Or.inl hy0
  refine Or.inr ?_
  have h1 := UpperTheory.FlipVal.vw_ge la hy0 hq0 _ key
  have h2 : -(((D.R.m ^ 2 * (depthAt ch.G w * bigN D * (3 * (2 * ⌊8 * large₂.sc.b⌋₊) + 8 * bigN D)) : ℕ) : ℝ) *
      (vw la ((resCard (Kw w) : ℕ) : D.what₂.LL) : ℝ)) ≤ (vw la y : ℝ) := by exact_mod_cast h1
  refine le_trans (neg_le_neg ?_) h2
  by_cases hW : w ∈ ch.G.pl.W0
  · have hd : depthAt ch.G w = cosExp ch.G w := by
      rw [depthAt, max_eq_left]
      rw [cosExp, if_pos hW]
      exact ch.G.pl.depth_pos _ _
    obtain ⟨s1, -, s2, -, -, -, -, s3⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS.size
    have s2' : (1 : ℝ) ≤ bigN D := by exact_mod_cast s2
    have s4 : (⌊8 * large₂.sc.b⌋₊ : ℝ) ≤ 8 * large₂.sc.b := Nat.floor_le (by linarith)
    have s5 : (0 : ℝ) ≤ (vw la ((resCard (Kw w) : ℕ) : D.what₂.LL) : ℝ) := by
      exact_mod_cast UpperTheory.FlipVal.vw_nat_nonneg la _
    refine mul_le_mul_of_nonneg_right ?_ s5
    rw [hd]
    push_cast
    have s6 : 3 * (2 * (⌊8 * large₂.sc.b⌋₊ : ℝ)) + 8 * bigN D ≤ 56 * (bigN D * large₂.sc.b) := by nlinarith
    calc _ ≤ (D.R.m : ℝ) ^ 2 * ((cosExp ch.G w : ℝ) * bigN D * (56 * (bigN D * large₂.sc.b))) := by gcongr
      _ = _ := by ring
  · have h0 : vw la ((resCard (Kw w) : ℕ) : D.what₂.LL) = 0 := by
      rw [hq]; exact UpperTheory.FlipVal.vw_absNorm la w (hla.resolve_left hW)
    rw [h0]; simp
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.FunDat

section Val

variable {D : D7}

theorem lossLe_one (w : PlL D) : LossLe w 1 0 := ⟨1, map_one _, Or.inr (by simp [Formalism.DivisionValues.ValuationRepresentative.vw_one])⟩

theorem lossLe_mul {w : PlL D} {z z' : ℂ} {a a' : ℝ} (h : LossLe w z a) (h' : LossLe w z' a') :
    LossLe w (z * z') (a + a') := by
  obtain ⟨y, rfl, hy⟩ := h
  obtain ⟨y', rfl, hy'⟩ := h'
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases h0 : y = 0
  · exact Or.inl (by simp [h0])
  by_cases h0' : y' = 0
  · exact Or.inl (by simp [h0'])
  rcases hy with h1 | h1
  · exact absurd h1 h0
  rcases hy' with h2 | h2
  · exact absurd h2 h0'
  refine Or.inr ?_
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ h0 h0', Int.cast_add]
  linarith

theorem lossLe_prod {w : PlL D} {ι : Type*} (s : Finset ι) (z : ι → ℂ) (a : ι → ℝ) (h : ∀ i ∈ s, LossLe w (z i) (a i)) :
    LossLe w (∏ i ∈ s, z i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lossLe_one w
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact lossLe_mul (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem loss_mono {dl : PlL D → ℝ} {B B' : ℝ} (h : Loss dl B) (hB : B ≤ B') : Loss dl B' :=
  ⟨h.1, h.2.1, fun s => (h.2.2 s).trans hB⟩

end Val

section Sum

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

def dlD (K : ℝ) (w : PlL D) : ℝ := ∑ P ∈ G.pl.W0, K * (cosExp G P : ℝ) * (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ)

theorem sum_cosExp_le : ∑ P ∈ G.pl.W0, (cosExp G P : ℝ) * Real.log (resCard (Kw P) : ℕ) ≤ 2 * sig G := by
  classical
  have hinj : Set.InjOn G.pl.w (G.pl.S0 : Set (Pl D.host.F)) := fun v hv v' hv' h =>
    (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv'))
  rw [Places.W0, Finset.sum_image hinj, sig, Finset.mul_sum]
  refine Finset.sum_le_sum fun v hv => ?_
  obtain ⟨h1, -⟩ := depthAt_w G hv
  rw [h1, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw]
  have h2 := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.log_absNorm_le (G.pl.w v)
  rw [G.pl.under_w hv] at h2
  have h3 : (0 : ℝ) ≤ (G.pl.depth sc v : ℝ) := by positivity
  calc (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm (G.pl.w v).asIdeal : ℕ)
      ≤ (G.pl.depth sc v : ℝ) * (2 * Real.log (Ideal.absNorm v.asIdeal)) := mul_le_mul_of_nonneg_left h2 h3
    _ = _ := by ring

theorem loss_dlD {K : ℝ} (hK : 0 ≤ K) : Loss (dlD G K) (2 * K * sig G) := by
  classical
  refine ⟨fun w => Finset.sum_nonneg fun P _ => mul_nonneg (by positivity) ?_, ?_, fun s => ?_⟩
  · exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w _
  · refine ((G.pl.W0.finite_toSet.biUnion fun P _ =>
      ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.finite_vw_ne (K := D.what₂.LL) (resCard (Kw P))
        (ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.resCard_ne P))).subset fun w hw => ?_
    by_contra h
    refine hw (Finset.sum_eq_zero fun P hP => ?_)
    have : vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) = 0 := by
      by_contra h'
      exact h (Set.mem_biUnion hP h')
    simp [this]
  · have h1 : ∑ w ∈ s, lw w * dlD G K w =
        ∑ P ∈ G.pl.W0, K * (cosExp G P : ℝ) * ∑ w ∈ s, lw w * (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ) := by
      simp only [dlD, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun w _ => by ring
    have h2 : ∑ w ∈ s, lw w * dlD G K w ≤ ∑ P ∈ G.pl.W0, K * (cosExp G P : ℝ) * Real.log (resCard (Kw P) : ℕ) := by
      rw [h1]
      exact Finset.sum_le_sum fun P _ => mul_le_mul_of_nonneg_left
        (Formalism.EigenvalueLevelCeiling.sum_lw_vw_natCast_le s _ (ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.resCard_ne P)) (by positivity)
    calc ∑ w ∈ s, lw w * dlD G K w ≤ _ := h2
      _ = K * ∑ P ∈ G.pl.W0, (cosExp G P : ℝ) * Real.log (resCard (Kw P) : ℕ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun P _ => by ring
      _ ≤ K * (2 * sig G) := mul_le_mul_of_nonneg_left (sum_cosExp_le G) hK
      _ = 2 * K * sig G := by ring

end Sum

end GlobalTheory.FunDat

end

noncomputable section

namespace GlobalTheory.FunDat

section Cases

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem away_cases {t : T} {w : PlL D} (hA : Away G t w) {P : Pl D.host.E} (hl : P ∈ locPl G t) :
    P ∈ G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := by
  classical
  by_cases hP : P ∈ G.pl.W0
  · exact Or.inl hP
  have hQ : P ∈ L.Q t := by
    rcases Finset.mem_union.1 hl with h | h
    · exact absurd h hP
    · exact h
  refine Or.inr ?_
  rcases hA P hQ with h | h
  · exfalso
    rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact G.pl.levelPlace_ne_basePlace t P hQ h
    · exact hP (by
        rw [G.pl.w_Q t P hQ h]
        exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h)))
  · exact h _ (Formalism.EigenvalueLevelCeiling.plc_prime P) (Formalism.EigenvalueLevelCeiling.plc_mem P)

theorem sum_locPl (t : T) (K : ℝ) (w : PlL D) :
    ∑ v : locPl G t, K * (cosExp G v : ℝ) * (vw w ((resCard (Kw (v : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ) = dlD G K w := by
  classical
  rw [Finset.sum_coe_sort (locPl G t) fun P => K * (cosExp G P : ℝ) * (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ), dlD]
  refine (Finset.sum_subset Finset.subset_union_left fun P _ hn => ?_).symm
  simp [(depthAt_of_notMem G hn).1]

end Cases

theorem finDatK_of (hA : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ c₁ : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK →
      ∀ (t : T) (Φ : ch.G.Datum) (P : Pl D.host.E), P ∈ locPl ch.G t → ∀ w : PlL D,
        (P ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal) →
        ∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) (c₁ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * large₂.sc.b * (cosExp ch.G P : ℝ) *
          (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ))) (hB : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ c₂ : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK →
      ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t) (w : PlL D),
        ((P : Pl D.host.E) ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal) →
        ∀ c : ℝ, 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
        ∀ X Y, LossLe w ((ch.S.term t Φ β P).datum X Y) (c + c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (cosExp ch.G P : ℝ) *
          (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ))) : FinDatK := by
  obtain ⟨CFa, hA⟩ := hA
  obtain ⟨CFb, hB⟩ := hB
  refine ⟨max CFa CFb, fun CF hCF => ?_⟩
  obtain ⟨c₁, hA⟩ := hA CF ((le_max_left _ _).trans hCF)
  obtain ⟨c₂, hB⟩ := hB CF ((le_max_right _ _).trans hCF)
  refine ⟨max 2 (2 * (max c₁ 0 + max c₂ 0)), fun ε C hC => ?_⟩
  obtain ⟨xa, hA⟩ := hA ε
  obtain ⟨xb, hB⟩ := hB ε
  refine ⟨max xa xb, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hIs hSc hF => ?_⟩
  have hA := hA D large₂ hε ((le_max_left _ _).trans hx) Γ Pl0 T A Ks R F s ch hIs hSc hF
  have hB := hB D large₂ hε ((le_max_right _ _).trans hx) Γ Pl0 T A Ks R F s ch hIs hSc hF
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hf : (1 : ℝ) ≤ D.R.f := by
    have h1 : D.R.m ≤ D.R.f := D.R.m_le_f
    have h2 := D.R.two_le_m
    exact_mod_cast (show 1 ≤ D.R.f by omega)
  set K0 : ℝ := max c₁ 0 + max c₂ 0 with hK0
  have hK0' : 0 ≤ K0 := add_nonneg (le_max_right _ _) (le_max_right _ _)
  set M : ℝ := (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  set K : ℝ := K0 * M * large₂.sc.b with hK
  have hK' : 0 ≤ K := mul_nonneg (mul_nonneg hK0' hM0) (by linarith)
  have hC2 : 2 * K0 ≤ C := (le_max_right _ _).trans hC
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 2).trans ((le_max_left _ _).trans hC)
  have hsig := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.sig_nonneg ch.G
  have hlb : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg hb
  have hbound : 2 * K * sig ch.G ≤ D.R.m * bOne ch.G C large₂.sc.b := by
    have h1 : 2 * K0 * sig ch.G ≤ C * D.R.f * (Real.log large₂.sc.b + sig ch.G) := by
      have h2 : 2 * K0 * sig ch.G ≤ C * sig ch.G := mul_le_mul_of_nonneg_right hC2 hsig
      have h3 : C * sig ch.G ≤ C * D.R.f * (Real.log large₂.sc.b + sig ch.G) := by
        have h4 : sig ch.G ≤ D.R.f * (Real.log large₂.sc.b + sig ch.G) := by nlinarith
        calc C * sig ch.G ≤ C * (D.R.f * (Real.log large₂.sc.b + sig ch.G)) := mul_le_mul_of_nonneg_left h4 hC0
          _ = _ := by ring
      linarith
    have h5 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hM0 (by linarith : (0 : ℝ) ≤ large₂.sc.b))
    calc 2 * K * sig ch.G = 2 * K0 * sig ch.G * (M * large₂.sc.b) := by rw [hK]; ring
      _ ≤ C * D.R.f * (Real.log large₂.sc.b + sig ch.G) * (M * large₂.sc.b) := h5
      _ = D.R.m * bOne ch.G C large₂.sc.b := by rw [bOne, hM]; ring
  refine ⟨dlD ch.G K, loss_mono (loss_dlD ch.G hK') hbound, fun t w hAw Φ β hβ x y => ?_⟩
  have key : ∀ v : locPl ch.G t, LossLe w ((ch.S.term t Φ β v).datum (ch.S.colAt t v x) (ch.S.rowAt t v y))
      (K * (cosExp ch.G v : ℝ) * (vw w ((resCard (Kw (v : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ)) := by
    intro v
    have hcase := away_cases ch.G hAw v.2
    set e : ℝ := (cosExp ch.G v : ℝ) with he
    set q : ℝ := (vw w ((resCard (Kw (v : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ) with hq
    have he0 : 0 ≤ e := by positivity
    have hq0 : 0 ≤ q := by
      rw [hq]; exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w _
    have hX : 0 ≤ M * large₂.sc.b * e * q := mul_nonneg (mul_nonneg (mul_nonneg hM0 (by linarith)) he0) hq0
    set c : ℝ := max c₁ 0 * M * large₂.sc.b * e * q with hc
    have hc0 : 0 ≤ c := by
      have : c = max c₁ 0 * (M * large₂.sc.b * e * q) := by rw [hc]; ring
      rw [this]; exact mul_nonneg (le_max_right _ _) hX
    have h1 : ∀ z, LossLe w (Tflip ch.W ch.S.B t Φ v z) c := fun z => (hA t Φ v v.2 w hcase z).mono (by
      have e1 : c₁ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * large₂.sc.b * e * q = c₁ * (M * large₂.sc.b * e * q) := by rw [hM]; ring
      have e2 : c = max c₁ 0 * (M * large₂.sc.b * e * q) := by rw [hc]; ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX)
    refine (hB t Φ β hβ v w hcase c hc0 h1 _ _).mono ?_
    have e3 : c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * e * q ≤ max c₂ 0 * M * large₂.sc.b * e * q := by
      have hY : 0 ≤ M * e * q := mul_nonneg (mul_nonneg hM0 he0) hq0
      calc c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * e * q = c₂ * (M * e * q) := by rw [hM]; ring
        _ ≤ max c₂ 0 * (M * e * q) := mul_le_mul_of_nonneg_right (le_max_left _ _) hY
        _ ≤ max c₂ 0 * (M * e * q) * large₂.sc.b := le_mul_of_one_le_right (mul_nonneg (le_max_right _ _) hY) hb
        _ = max c₂ 0 * M * large₂.sc.b * e * q := by ring
    calc c + c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * e * q ≤ c + max c₂ 0 * M * large₂.sc.b * e * q := by linarith
      _ = K * e * q := by rw [hc, hK, hK0]; ring
  have hP := lossLe_prod Finset.univ _ _ fun v _ => key v
  rw [sum_locPl ch.G t K w] at hP
  exact hP

end GlobalTheory.FunDat

end
