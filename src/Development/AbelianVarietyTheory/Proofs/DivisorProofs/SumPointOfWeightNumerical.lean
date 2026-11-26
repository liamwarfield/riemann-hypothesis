module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeBoundEveryPrime

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.SmallVdSum
open NumberField Formalism.HC

theorem UpperTheory.KR.small_vd_sum :
    ∀ {φ : Frame} (H : HostAx φ), (∑ p ∈ H.small, (1 + H.vdH p / 2) * Real.log p ≤ 3 / 2 * Real.logb 2 H.QS) ∧ 2 ∈ H.small ∧
      ∀ r : ℕ, r.Prime → r ∉ H.small → r ≠ H.q → r ≠ H.d → ¬ (r : ℤ) ∣ discr H.E := by
  intro φ H
  obtain ⟨hsm, -, -, -, -⟩ := UpperTheory.cmDatum_discriminantDepth_bounds H
  refine ⟨?_, H.two_mem_small, ?_⟩
  · have hQ0 : H.QS ≠ 0 := H.QS_ne_zero
    have hlogQ : Real.log (H.QS : ℝ) = ∑ p ∈ H.small, (padicValNat p H.QS : ℝ) * Real.log p := by
      show _ = ∑ p ∈ H.QS.primeFactors, (padicValNat p H.QS : ℝ) * Real.log p
      have hprod : (H.QS : ℝ) = ∏ p ∈ H.QS.primeFactors, (p : ℝ) ^ (H.QS.factorization p) := by
        conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hQ0]
        rw [Finsupp.prod, Nat.support_factorization]
        push_cast
        rfl
      rw [hprod, Real.log_prod]
      · apply Finset.sum_congr rfl
        intro p hp
        rw [Real.log_pow, Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp),
          ← Nat.padicValNat_def]
      · intro p hp
        exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)
    have hlog2 : Real.log (H.QS : ℝ) ≤ Real.logb 2 H.QS := by
      rw [Real.logb]
      have hl0 : 0 ≤ Real.log (H.QS : ℝ) := Real.log_natCast_nonneg _
      have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h2' : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9
        linarith
      rw [le_div_iff₀ h2]
      nlinarith
    calc ∑ p ∈ H.small, (1 + H.vdH p / 2) * Real.log p
        ≤ ∑ p ∈ H.small, 3 / 2 * ((padicValNat p H.QS : ℝ) * Real.log p) := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨hpp, hpd⟩ := (H.mem_small_iff).mp hp
          haveI := Fact.mk hpp
          have hv1 : (1 : ℝ) ≤ padicValNat p H.QS := by
            exact_mod_cast (by simpa only [Nat.padicValNat_def] using one_le_padicValNat_of_dvd hQ0 hpd)
          have hvd := (hsm p hp).1
          have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 2 * padicValNat p H.QS - 1 - H.vdH p / 2) hlp]
      _ = 3 / 2 * Real.log H.QS := by rw [hlogQ, Finset.mul_sum]
      _ ≤ 3 / 2 * Real.logb 2 H.QS := by linarith
  · intro r hr hrs hrq hrd hdvd
    have h : r ∣ H.QS * H.q * H.d := (H.der.discr_primes).1 r hr hdvd
    rcases (Nat.Prime.dvd_mul hr).mp h with h1 | h1
    · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
      · exact hrs ((H.mem_small_iff).mpr ⟨hr, h2⟩)
      · exact hrq ((Nat.prime_dvd_prime_iff_eq hr H.q_prime).mp h2)
    · exact hrd ((Nat.prime_dvd_prime_iff_eq hr H.d_prime).mp h1)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsBigSmallFactorBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsBigSmallFactorBounds
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSpread IsSmall sumSmallSpread)
open GlobalTheory.AllWt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum.ThetaExp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

open Classical

theorem thA_big (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : i < Dw.p) :
    thA Dw u n (τ.1, i) = (u τ ⟨i, by omega⟩ - u τ ⟨Dw.p - 1, by omega⟩ + 1).toNat := by
  simp only [thA, wtOf_big _ _ τ i hi, shift, dif_pos (show 0 < Dw.p by omega), Pi.add_apply, GlobalTheory.FlatLine.parWt]
  congr 1; ring

theorem thA_small (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : i < Dw.q) (hp : 0 < Dw.p) :
    thA Dw u n (conjEmb τ.1, i) =
      (u τ ⟨Dw.p - 1, by omega⟩ - u τ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ - 1 - 2 * ((n / 2 : ℕ) : ℤ)).toNat := by
  simp only [thA, wtOf_small _ _ τ i hi, shift, dif_pos hp, Pi.add_apply, GlobalTheory.FlatLine.parWt]
  congr 1; ring

theorem thA_out (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : E →+* ℂ) (i : ℕ) (h : Dw.mult τ ≤ i) : thA Dw u n (τ, i) = 0 := by
  unfold Datum.mult at h
  simp only [thA, wtOf]
  split_ifs at h ⊢ <;> first | omega | simp

theorem psi_or_conj (τ : E →+* ℂ) : (∃ τ' : Psi H, τ = τ'.1) ∨ ∃ τ' : Psi H, τ = conjEmb τ'.1 := by
  by_cases h : τ (H.rt : E) = H.rt0
  · exact Or.inl ⟨⟨τ, h⟩, rfl⟩
  · exact Or.inr ⟨⟨conjEmb τ, conj_mem h⟩, (AllWt.conjEmb_conjEmb τ).symm⟩

theorem mult_psi (τ : Psi H) : Dw.mult τ.1 = Dw.p := by unfold Datum.mult; rw [if_pos τ.2]

theorem mult_conj (τ : Psi H) : Dw.mult (conjEmb τ.1) = Dw.q := by unfold Datum.mult; rw [if_neg (conj_not_mem τ)]

theorem tele_real (f : ℕ → ℝ) (K : ℕ) :
    ∑ j ∈ Finset.range K, ((j : ℝ) + 1) * (f j - f (j + 1)) = ∑ j ∈ Finset.range K, (f j - f K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring

theorem thA_anti (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (hanti : ∀ τ, Antitone (u τ)) (hp : 0 < Dw.p) (τ : E →+* ℂ) :
    Antitone fun i => thA Dw u n (τ, i) := by
  apply antitone_nat_of_succ_le
  intro i
  by_cases hm : Dw.mult τ ≤ i + 1
  · simp only [thA_out u n τ (i + 1) hm]; exact Nat.zero_le _
  rcases psi_or_conj (H := H) τ with ⟨τ', rfl⟩ | ⟨τ', rfl⟩
  · rw [mult_psi] at hm
    simp only [thA_big u n τ' (i + 1) (by omega), thA_big u n τ' i (by omega)]
    apply Int.toNat_le_toNat
    have := hanti τ' (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨i + 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
    linarith
  · rw [mult_conj] at hm
    simp only [thA_small u n τ' (i + 1) (by omega) hp, thA_small u n τ' i (by omega) hp]
    apply Int.toNat_le_toNat
    have := hanti τ' (show (⟨Dw.p + (Dw.q - 1 - (i + 1)), by omega⟩ : Fin (Dw.p + Dw.q)) ≤
      ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from Fin.mk_le_mk.2 (by omega))
    linarith

theorem thA_le (u : GlobalTheory.AllWt.Weight Dw) (n B : ℕ) (hB : ∀ τ i, |u τ i| ≤ B) (hp : 0 < Dw.p) (x : (E →+* ℂ) × ℕ) :
    thA Dw u n x ≤ 2 * B + 1 := by
  obtain ⟨τ, i⟩ := x
  by_cases hm : Dw.mult τ ≤ i
  · rw [thA_out u n τ i hm]; omega
  rcases psi_or_conj (H := H) τ with ⟨τ', rfl⟩ | ⟨τ', rfl⟩
  · rw [mult_psi] at hm
    rw [thA_big u n τ' i (by omega), Int.toNat_le]
    have h1 := abs_le.1 (hB τ' ⟨i, by omega⟩)
    have h2 := abs_le.1 (hB τ' ⟨Dw.p - 1, by omega⟩)
    push_cast; linarith
  · rw [mult_conj] at hm
    rw [thA_small u n τ' i (by omega) hp, Int.toNat_le]
    have h1 := abs_le.1 (hB τ' ⟨Dw.p + (Dw.q - 1 - i), by omega⟩)
    have h2 := abs_le.1 (hB τ' ⟨Dw.p - 1, by omega⟩)
    omega

theorem thA_le_conj (u : GlobalTheory.AllWt.Weight Dw) (n B : ℕ) (hB : ∀ τ i, |u τ i| ≤ B) (hp : 0 < Dw.p) (τ : Psi H) (i : ℕ) :
    thA Dw u n (conjEmb τ.1, i) ≤ 2 * B := by
  by_cases hm : Dw.mult (conjEmb τ.1) ≤ i
  · rw [thA_out u n _ i hm]; omega
  rw [mult_conj] at hm
  rw [thA_small u n τ i (by omega) hp, Int.toNat_le]
  have h1 := abs_le.1 (hB τ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩)
  have h2 := abs_le.1 (hB τ ⟨Dw.p - 1, by omega⟩)
  omega

theorem sum_lieFactorRank_mul_exponentGap_eq (a : (E →+* ℂ) × ℕ → ℕ) (τ : E →+* ℂ) (ha : Antitone fun i => a (τ, i))
    (hm : a (τ, Dw.mult τ) = 0) (K : ℕ) (hK : K ≤ Dw.mult τ) :
    ∑ j : Fin (Dw.mult τ), (if (j : ℕ) < K then ((rk (⟨τ, j⟩ : Lt1 Dw) * gap Dw a ⟨τ, j⟩ : ℕ) : ℝ) else 0) =
      ∑ j ∈ Finset.range K, ((a (τ, j) : ℝ) - a (τ, K)) := by
  rw [← tele_real (fun j => (a (τ, j) : ℝ)) K]
  have step : ∀ j : Fin (Dw.mult τ),
      (if (j : ℕ) < K then ((rk (⟨τ, j⟩ : Lt1 Dw) * gap Dw a ⟨τ, j⟩ : ℕ) : ℝ) else 0) =
        (fun j : ℕ => if j < K then ((j : ℝ) + 1) * ((a (τ, j) : ℝ) - a (τ, j + 1)) else 0) (j : ℕ) := by
    intro j
    simp only []
    split_ifs with hj
    · have hg : gap Dw a ⟨τ, j⟩ = a (τ, j) - a (τ, (j : ℕ) + 1) := by
        unfold gap
        simp only [rk]
        split_ifs with h
        · rfl
        · have e : (j : ℕ) + 1 = Dw.mult τ := by omega
          rw [e, hm]
      rw [hg, Nat.cast_mul, Nat.cast_sub (ha (Nat.le_succ _))]
      simp only [rk]; push_cast; ring
    · rfl
  rw [Finset.sum_congr rfl (fun j _ => step j),
    Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < K then ((j : ℝ) + 1) * ((a (τ, j) : ℝ) - a (τ, j + 1)) else 0),
    ← Finset.sum_filter]
  congr 1
  ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega

theorem card_psi (F : ℕ) (hF : Module.finrank ℚ E = 2 * F) :
    (Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).card = F ∧
      (Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0)).card = F := by
  have hc : (Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0)).card =
      (Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).card := by
    apply Finset.card_bij (fun τ _ => conjEmb τ)
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      exact conj_mem hτ
    · intro a _ b _ h
      rw [← AllWt.conjEmb_conjEmb a, h, AllWt.conjEmb_conjEmb]
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact ⟨conjEmb b, by simpa using conj_not_mem (H := H) ⟨b, hb⟩, AllWt.conjEmb_conjEmb b⟩
  have ht := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)
  rw [Finset.card_univ, NumberField.Embeddings.card E ℂ, hF] at ht
  omega


open Classical in
theorem big_le (u : GlobalTheory.AllWt.Weight Dw) (k n B : ℕ) (hk : 2 ≤ k) (hkp : k ≤ Dw.p + 1) (hanti : ∀ τ, Antitone (u τ))
    (hz : ∀ τ (i : Fin (Dw.p + Dw.q)), (i : ℕ) + 2 = k → u τ i = 0) (hB : ∀ τ i, |u τ i| ≤ B) (τ : E →+* ℂ) :
    ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f ∧ f.1 = τ), gap Dw (thA Dw u n) f ≤ B + 1 := by
  have hp : 0 < Dw.p := by omega
  by_cases h : InPsi H τ
  · obtain ⟨τ', rfl⟩ : ∃ τ' : Psi H, τ = τ'.1 := ⟨⟨τ, h⟩, rfl⟩
    have hlt : k - 2 < Dw.mult τ'.1 := by rw [mult_psi]; omega
    have e := sum_gap_row (Dw := Dw) (thA_anti u n hanti hp) τ'.1 ⟨k - 2, hlt⟩
    have e2 : Finset.univ.filter (fun f : Lt1 Dw => GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f ∧ f.1 = τ'.1) =
        Finset.univ.filter (fun f : Lt1 Dw => f.1 = τ'.1 ∧ k - 2 < rk f) := by
      refine Finset.filter_congr fun f _ => ?_
      unfold GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, by omega⟩
      · rintro ⟨h3, h2⟩
        exact ⟨⟨h3 ▸ h, by omega⟩, h3⟩
    rw [e2]
    refine le_of_eq_of_le (by convert e) ?_
    show thA Dw u n (τ'.1, k - 2) ≤ B + 1
    rw [thA_big u n τ' (k - 2) (by omega), hz τ' ⟨k - 2, by omega⟩ (by show k - 2 + 2 = k; omega), Int.toNat_le]
    have h2 := abs_le.1 (hB τ' ⟨Dw.p - 1, by omega⟩)
    omega
  · rw [Finset.sum_eq_zero]
    · omega
    · intro f hf
      have hf' := (Finset.mem_filter.1 hf).2
      exact absurd (hf'.2 ▸ hf'.1.1) h

theorem cloud_eq (u : GlobalTheory.AllWt.Weight Dw) (k n : ℕ) (hk : 2 ≤ k) (hkp : k ≤ Dw.p + 1) (hanti : ∀ τ, Antitone (u τ))
    (hz : ∀ τ (i : Fin (Dw.p + Dw.q)), (i : ℕ) + 2 = k → u τ i = 0) (τ : Psi H) :
    ∑ j ∈ Finset.range (k - 2), ((thA Dw u n (τ.1, j) : ℝ) - thA Dw u n (τ.1, k - 2)) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin (Dw.p + Dw.q) => (i : ℕ) + 2 < k), (u τ i : ℝ) := by
  have val : ∀ i (hi : i < Dw.p), (thA Dw u n (τ.1, i) : ℝ) =
      (u τ ⟨i, by omega⟩ : ℝ) - (u τ ⟨Dw.p - 1, by omega⟩ : ℝ) + 1 := by
    intro i hi
    have h := hanti τ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p - 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
    have h2 : ((thA Dw u n (τ.1, i) : ℕ) : ℤ) = u τ ⟨i, by omega⟩ - u τ ⟨Dw.p - 1, by omega⟩ + 1 := by
      rw [thA_big u n τ i hi, Int.toNat_of_nonneg (by omega)]
    exact_mod_cast h2
  symm
  refine Finset.sum_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    have := (Finset.mem_filter.1 hi).2
    exact Finset.mem_range.2 (by omega)
  · intro i _ j _ h
    exact Fin.ext h
  · intro j hj
    have := Finset.mem_range.1 hj
    exact ⟨⟨j, by omega⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, by show j + 2 < k; omega⟩, rfl⟩
  · intro i hi
    have := (Finset.mem_filter.1 hi).2
    rw [val i (by omega), val (k - 2) (by omega), hz τ ⟨k - 2, by omega⟩ (by show k - 2 + 2 = k; omega)]
    simp


open Classical in
theorem row_le (u : GlobalTheory.AllWt.Weight Dw) (k n B : ℕ) (Sg : ℝ) (hk : 2 ≤ k) (hkp : k ≤ Dw.p + 1) (hu : WtBd Dw k n u B Sg)
    (τ : E →+* ℂ) :
    ∑ j : Fin (Dw.mult τ), (if IsSmall (⟨τ, j⟩ : Lt1 Dw) ∨ IsSpread k (⟨τ, j⟩ : Lt1 Dw) then
      ((rk (⟨τ, j⟩ : Lt1 Dw) * gap Dw (thA Dw u n) ⟨τ, j⟩ : ℕ) : ℝ) else 0) ≤
      if τ (H.rt : E) = H.rt0 then Sg else 2 * (Dw.q : ℝ) * B := by
  obtain ⟨hanti, hz, -, hB, hS⟩ := hu
  have hp : 0 < Dw.p := by omega
  have key := sum_lieFactorRank_mul_exponentGap_eq (Dw := Dw) (thA Dw u n) τ (thA_anti u n hanti hp τ) (thA_out u n τ _ le_rfl)
  rcases psi_or_conj (H := H) τ with ⟨τ', rfl⟩ | ⟨τ', rfl⟩
  · rw [if_pos τ'.2]
    refine le_of_eq_of_le ?_ (hS τ')
    rw [← cloud_eq u k n hk hkp hanti hz τ', ← key (k - 2) (by rw [mult_psi]; omega)]
    refine Finset.sum_congr rfl fun j _ => if_congr ?_ rfl rfl
    have h : InPsi H τ'.1 := τ'.2
    simp only [IsSmall, IsSpread, h, not_true, false_or, true_and, rk]
    omega
  · rw [if_neg (conj_not_mem τ')]
    have h : ¬ InPsi H (conjEmb τ'.1) := conj_not_mem τ'
    have key2 := key _ le_rfl
    simp only [Fin.is_lt, if_true, thA_out u n _ _ le_rfl] at key2
    simp only [IsSmall, h, not_false_iff, true_or, if_true]
    rw [key2, mult_conj]
    calc _ ≤ ∑ j ∈ Finset.range Dw.q, (2 * (B : ℝ)) := Finset.sum_le_sum fun j _ => by
          have : ((thA Dw u n (conjEmb τ'.1, j) : ℕ) : ℝ) ≤ ((2 * B : ℕ) : ℝ) :=
            Nat.cast_le.2 (thA_le_conj u n B hB hp τ' j)
          push_cast at this ⊢; linarith
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem expBd_thA : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H), ∀ (F k m n B : ℕ) (Sg : ℝ) (u : GlobalTheory.AllWt.Weight Dw), Shape Dw F k m → k ≤ Dw.p + 1 → WtBd Dw k n u B Sg → ExpBd Dw k (gap Dw (thA Dw u n)) (B + 1) (F * (Sg + 2 * Dw.q * B)) (2 * B + 1) := by
  intro E _ _ _ H Dw F k m n B Sg u hsh hkp hu
  obtain ⟨-, -, -, -, hk, hF⟩ := hsh
  have hp : 0 < Dw.p := by omega
  refine ⟨by positivity, fun τ => ?_, ?_, fun f => ?_⟩
  · exact_mod_cast big_le u k n B hk hkp hu.1 hu.2.1 hu.2.2.2.1 τ
  · unfold sumSmallSpread
    rw [Finset.sum_filter, Fintype.sum_sigma, Nat.cast_sum]
    calc _ ≤ ∑ τ : E →+* ℂ, (if τ (H.rt : E) = H.rt0 then Sg else 2 * (Dw.q : ℝ) * B) :=
          Finset.sum_le_sum fun τ _ => by
            refine le_of_eq_of_le ?_ (row_le u k n B Sg hk hkp hu τ)
            rw [Nat.cast_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            split_ifs <;> simp
      _ = _ := by
          rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, (card_psi F hF).1, (card_psi F hF).2]
          simp only [nsmul_eq_mul]; ring
  · exact (Nat.sub_le _ _).trans (thA_le u n B hu.2.2.2.1 hp _)

end GlobalTheory.RefSum.ThetaExp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsBigSmallFactorBoundsStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaExponents_bigSmallFactorBounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H), ∀ (F k m n B : ℕ) (Sg : ℝ) (u : GlobalTheory.AllWt.Weight Dw), Shape Dw F k m → k ≤ Dw.p + 1 → WtBd Dw k n u B Sg → ExpBd Dw k (gap Dw (thA Dw u n)) (B + 1) (F * (Sg + 2 * Dw.q * B)) (2 * B + 1) := by
  first | exact @GlobalTheory.RefSum.ThetaExp.expBd_thA | exact GlobalTheory.RefSum.ThetaExp.expBd_thA | (intros; apply GlobalTheory.RefSum.ThetaExp.expBd_thA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedPrimeLogSumOscillationBoundLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPrimesInvPredLeLoglog
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPrimesInvPredLeLoglog
namespace GlobalTheory.PrimeRecipSum
open Finset

theorem sum_inv_pred_small (y : ℕ) (hy : y ≤ 8) :
    ∑ p ∈ (range (y + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1) ≤ 23 / 12 := by
  have hsub : (range (y + 1)).filter Nat.Prime ⊆ (range 9).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hnn : ∀ p ∈ (range 9).filter Nat.Prime, p ∉ (range (y + 1)).filter Nat.Prime →
      (0:ℝ) ≤ 1 / ((p : ℝ) - 1) := by
    intro p hp _
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2.two_le
    exact div_nonneg (by norm_num) (by linarith)
  refine (sum_le_sum_of_subset_of_nonneg hsub hnn).trans ?_
  have e : (range 9).filter Nat.Prime = {2, 3, 5, 7} := by decide
  rw [e]
  norm_num

theorem inv_pred_le_of_sqrt_lt (y s p : ℕ) (hy : 2 ≤ y) (hs : y < (s + 1) * (s + 1))
    (hp : Nat.Prime p) (hps : s < p) :
    1 / ((p : ℝ) - 1) ≤ 2 / Real.log y * (Real.log p / ((p : ℝ) - 1)) := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have ha : (0:ℝ) < (p:ℝ) - 1 := by linarith
  have hl : 0 < Real.log (y:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hyp : y ≤ p ^ 2 := by
    have := Nat.mul_le_mul (show s + 1 ≤ p from hps) (show s + 1 ≤ p from hps)
    rw [sq]; omega
  have hy' : (y:ℝ) ≤ (p:ℝ) ^ 2 := by exact_mod_cast hyp
  have hL : Real.log y ≤ 2 * Real.log p := by
    have := Real.log_le_log (by positivity) hy'
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  rw [div_mul_div_comm, div_le_div_iff₀ ha (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hL ha.le]

theorem sum_inv_pred_le : ∀ y : ℕ, 3 ≤ y →
    ∑ p ∈ (Finset.range (y + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1)
      ≤ 7 * Real.log (Real.log y) + 6 := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
  intro hy3
  have hy3' : (3:ℝ) ≤ y := by exact_mod_cast hy3
  have hl1 : 1 ≤ Real.log (y:ℝ) := by
    have he := Real.exp_one_lt_d9
    have := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ y)
    rwa [Real.log_exp] at this
  have hll : 0 ≤ Real.log (Real.log y) := Real.log_nonneg hl1
  rcases le_or_gt y 8 with hy8 | hy8
  · have := sum_inv_pred_small y hy8
    linarith
  set s := Nat.sqrt y with hs_def
  have hs3 : 3 ≤ s := by rw [hs_def, Nat.le_sqrt]; omega
  have hsy : s < y := Nat.sqrt_lt_self (by omega)
  have hss : s * s ≤ y := Nat.sqrt_le y
  have hys : y < (s + 1) * (s + 1) := Nat.lt_succ_sqrt y
  have ih' := ih s hsy hs3
  have hsplit : ∑ p ∈ (range (y + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1)
      = ∑ p ∈ (range (s + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1)
        + ∑ p ∈ ((range (y + 1)).filter Nat.Prime).filter (fun p => ¬ p ≤ s),
            1 / ((p : ℝ) - 1) := by
    rw [← sum_filter_add_sum_filter_not ((range (y + 1)).filter Nat.Prime) (fun p => p ≤ s)]
    congr 1
    apply sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [mem_filter, mem_range]
    exact ⟨fun ⟨⟨_, h2⟩, h3⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨by omega, h2⟩, by omega⟩⟩
  have hl2 : 2 < Real.log (y:ℝ) := by
    have he : Real.exp 2 < 9 := by
      have := Real.exp_one_lt_d9
      have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [e2]; nlinarith [Real.exp_pos 1]
    have h9 : (9:ℝ) ≤ y := by exact_mod_cast (by omega : 9 ≤ y)
    have := Real.log_lt_log (Real.exp_pos 2) (by linarith : Real.exp 2 < y)
    rwa [Real.log_exp] at this
  have htail : ∑ p ∈ ((range (y + 1)).filter Nat.Prime).filter (fun p => ¬ p ≤ s),
      1 / ((p : ℝ) - 1) ≤ 2 / Real.log y * (Real.log y + 2.2) := by
    have hc : (0:ℝ) ≤ 2 / Real.log y := div_nonneg (by norm_num) (by linarith)
    calc _ ≤ ∑ p ∈ ((range (y + 1)).filter Nat.Prime).filter (fun p => ¬ p ≤ s),
            2 / Real.log y * (Real.log p / ((p : ℝ) - 1)) := by
          apply sum_le_sum
          intro p hp
          simp only [mem_filter, mem_range] at hp
          exact inv_pred_le_of_sqrt_lt y s p (by omega) hys hp.1.2 (by omega)
      _ = 2 / Real.log y * ∑ p ∈ ((range (y + 1)).filter Nat.Prime).filter (fun p => ¬ p ≤ s),
            Real.log p / ((p : ℝ) - 1) := by rw [mul_sum]
      _ ≤ 2 / Real.log y * ∑ p ∈ (range (y + 1)).filter Nat.Prime,
            Real.log p / ((p : ℝ) - 1) := by
          apply mul_le_mul_of_nonneg_left _ hc
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro p hp _
          have h2 : (2:ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2.two_le
          exact div_nonneg (Real.log_natCast_nonneg p) (by linarith)
      _ ≤ 2 / Real.log y * (Real.log y + 2.2) :=
          mul_le_mul_of_nonneg_left (GlobalTheory.PrimeLogSum.sum_log_div_pred_le y) hc
  have hfrac : 2 / Real.log y * (Real.log y + 2.2) ≤ 4.2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    linarith
  have hslog : 0 < Real.log (s:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < s))
  have hslog2 : 2 * Real.log (s:ℝ) ≤ Real.log y := by
    have h : ((s:ℝ)) ^ 2 ≤ y := by
      have : s ^ 2 ≤ y := by rw [sq]; exact hss
      exact_mod_cast this
    have hs0 : (0:ℝ) < s := by exact_mod_cast (by omega : 0 < s)
    have := Real.log_le_log (by positivity) h
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hlls : Real.log (Real.log s) ≤ Real.log (Real.log y) - Real.log 2 := by
    rw [← Real.log_div (by linarith) (by norm_num)]
    exact Real.log_le_log hslog (by linarith)
  have hlog2 := Real.log_two_gt_d9
  rw [hsplit]
  linarith

end GlobalTheory.PrimeRecipSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPrimesInvPredLeLoglogStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_primes_inv_pred_le_loglog : ∀ y : ℕ, 3 ≤ y → ∑ p ∈ (Finset.range (y + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1) ≤ 7 * Real.log (Real.log y) + 6 := by
  first | exact @GlobalTheory.PrimeRecipSum.sum_inv_pred_le | exact GlobalTheory.PrimeRecipSum.sum_inv_pred_le | (intros; apply GlobalTheory.PrimeRecipSum.sum_inv_pred_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedPrimeLogSumOscillationBoundLe
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.SumBound

open Finset

theorem sum_log_le (M : ℕ) :
    ∑ p ∈ (range (M + 1)).filter Nat.Prime, Real.log p ≤ M * Real.log 4 := by
  have h := primorial_le_four_pow M
  unfold primorial at h
  have h' : (∏ p ∈ (range (M + 1)).filter Nat.Prime, (p:ℝ)) ≤ (4:ℝ) ^ M := by
    rw [← Nat.cast_prod]
    exact_mod_cast h
  have hpos : ∀ p ∈ (range (M + 1)).filter Nat.Prime, (0:ℝ) < (p:ℝ) := by
    intro p hp
    have := (mem_filter.1 hp).2.pos
    positivity
  have := Real.log_le_log (Finset.prod_pos hpos) h'
  rw [Real.log_prod (fun p hp => (hpos p hp).ne')] at this
  simpa [Real.log_pow] using this

theorem eOf_nonneg (F N k m : ℕ) (Mb Sm : ℝ) (vd : ℕ → ℝ) (M : ℕ) (S₀ R : Finset ℕ) (hMb : 0 ≤ Mb) (hSm : 0 ≤ Sm)
    (hvd : ∀ q, 0 ≤ vd q) (p : ℕ) (hp : p.Prime) : 0 ≤ eOf F N k m Mb Sm vd M S₀ R p := by
  have hv := hvd p
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
  unfold eOf eSmall
  split_ifs with h1 h2 h3 h4
  · exact le_rfl
  · positivity
  · positivity
  · have hM : (1:ℝ) ≤ M := by
      have : 2 ≤ M := le_trans hp.two_le (not_lt.1 h1)
      exact_mod_cast (show 1 ≤ M by omega)
    have hl : 0 ≤ Real.logb p M := Real.logb_nonneg (by linarith) hM
    positivity
  · positivity

theorem point_le (F N k m M : ℕ) (Mb Sm : ℝ) (vd : ℕ → ℝ) (large₂ : ℝ) (S₀ R : Finset ℕ) (hMb : 0 ≤ Mb) (hSm : 0 ≤ Sm)
    (hvd : ∀ q, 0 ≤ vd q) (hLg : 1 ≤ large₂) (hLM : Real.log M ≤ large₂)
    (hRq : ∀ q ∈ R, N * Real.log q / ((q : ℝ) - 1) ≤ m * large₂) (p : ℕ) (hp : p.Prime) (hpM : p ≤ M) :
    eOf F N k m Mb Sm vd M S₀ R p * Real.log p ≤
      (if p ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd p / 2) * Real.log p) else 0) + (if p ∈ R then (F * m * Mb + Sm) * large₂ else 0)
      + (6 * F * m * Mb + Sm) * (Real.log p / ((p : ℝ) - 1)) + Real.log p
      + (if m * p < k then F * m * Mb * large₂ / 2 * (1 / ((p : ℝ) - 1)) + 2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂
          else 0) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have hlp1 : Real.log p ≤ (p:ℝ) - 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < p by linarith); linarith
  have ht0 : 0 ≤ Real.log p / ((p:ℝ) - 1) := div_nonneg hlp.le hp1.le
  have ht1 : Real.log p / ((p:ℝ) - 1) ≤ 1 := (div_le_one hp1).2 hlp1
  have hMr : (p:ℝ) ≤ M := by exact_mod_cast hpM
  have hlpM : Real.log p ≤ Real.log M := Real.log_le_log (by linarith) hMr
  have hF : (0:ℝ) ≤ F := Nat.cast_nonneg _
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hX : 0 ≤ (F:ℝ) * m * Mb := by positivity
  have hA : 0 ≤ ((F:ℝ) * m * Mb + Sm) * large₂ := by nlinarith
  have hinv : 0 ≤ 1 / ((p:ℝ) - 1) := by positivity
  have hv := hvd p
  have hI2 : 0 ≤ (if p ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd p / 2) * Real.log p) else 0) := by
    split_ifs
    · positivity
    · exact le_rfl
  have hIR : 0 ≤ (if p ∈ R then ((F:ℝ) * m * Mb + Sm) * large₂ else 0) := by split_ifs <;> linarith
  have hIk : 0 ≤ (if m * p < k then (F:ℝ) * m * Mb * large₂ / 2 * (1 / ((p : ℝ) - 1))
      + 2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂ else 0) := by
    split_ifs
    · have h1 : 0 ≤ (F:ℝ) * m * Mb * large₂ / 2 * (1 / ((p : ℝ) - 1)) :=
        mul_nonneg (div_nonneg (mul_nonneg hX (by linarith)) (by norm_num)) hinv
      have h2 : 0 ≤ 2 * (F:ℝ) * (m + 1) * (N : ℝ) ^ 2 * large₂ :=
        mul_nonneg (by positivity) (by linarith)
      linarith
    · exact le_rfl
  have hB : 0 ≤ (6 * (F:ℝ) * m * Mb + Sm) * (Real.log p / ((p : ℝ) - 1)) :=
    mul_nonneg (by positivity) ht0
  have hXt : 0 ≤ (F:ℝ) * m * Mb * (Real.log p / ((p : ℝ) - 1)) := mul_nonneg hX ht0
  have hnM : ¬ M < p := by omega
  unfold eOf
  rw [if_neg hnM]
  by_cases h2 : p ∈ S₀
  · rw [if_pos h2, if_pos h2]
    have e : ((F:ℝ) * m * Mb + Sm) * ((1 + vd p / 2) * Real.log p) = ((F:ℝ) * m * (1 + vd p / 2) * Mb + Sm) * Real.log p + Sm * (vd p / 2 * Real.log p) := by ring
    have e0 : 0 ≤ Sm * (vd p / 2 * Real.log p) := by positivity
    linarith
  · rw [if_neg h2]
    by_cases hR : p ∈ R
    · rw [if_pos hR]
      simp only [h2, hR, ↓reduceIte] at hI2 hIR ⊢
      have e : ((F:ℝ) * N * Mb + Sm) / ((p:ℝ) - 1) * Real.log p
          = F * Mb * (N * Real.log p / ((p:ℝ) - 1)) + Sm * (Real.log p / ((p:ℝ) - 1)) := by ring
      rw [e]
      have f1 : (F:ℝ) * Mb * (N * Real.log p / ((p:ℝ) - 1)) ≤ F * Mb * (m * large₂) :=
        mul_le_mul_of_nonneg_left (hRq p hR) (by positivity)
      have f2 : Sm * (Real.log p / ((p:ℝ) - 1)) ≤ Sm * large₂ := by nlinarith
      nlinarith
    · rw [if_neg hR]
      simp only [h2, hR, ↓reduceIte, add_zero, zero_add] at hI2 hIR ⊢
      by_cases hk : m * p < k
      · rw [if_pos hk, if_pos hk]
        unfold eSmall
        have hlb : Real.logb p M * Real.log p = Real.log M := by
          rw [Real.logb, div_mul_cancel₀ _ hlp.ne']
        have e : (((F:ℝ) * m * Mb * (4 + Real.logb p M / 2) + Sm) / ((p:ℝ) - 1)
            + F * (m + 1) * (N:ℝ) ^ 2 * (Real.logb p M + 1) + 1) * Real.log p
            = (4 * F * m * Mb + Sm) * (Real.log p / ((p:ℝ) - 1))
              + F * m * Mb / 2 * (Real.logb p M * Real.log p) * (1 / ((p:ℝ) - 1))
              + F * (m + 1) * (N:ℝ) ^ 2 * (Real.logb p M * Real.log p + Real.log p) + Real.log p := by ring
        rw [e, hlb]
        have g1 : (F:ℝ) * m * Mb / 2 * Real.log M * (1 / ((p:ℝ) - 1))
            ≤ F * m * Mb * large₂ / 2 * (1 / ((p:ℝ) - 1)) := by
          have : (F:ℝ) * m * Mb / 2 * Real.log M ≤ F * m * Mb * large₂ / 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right this hinv
        have hQ : 0 ≤ (F:ℝ) * (m + 1) * (N:ℝ) ^ 2 := by positivity
        have g2 : (F:ℝ) * (m + 1) * (N:ℝ) ^ 2 * (Real.log M + Real.log p)
            ≤ F * (m + 1) * (N:ℝ) ^ 2 * (2 * large₂) :=
          mul_le_mul_of_nonneg_left (by linarith) hQ
        have g0 : (4 * (F:ℝ) * m * Mb + Sm) * (Real.log p / ((p:ℝ) - 1))
            ≤ (6 * F * m * Mb + Sm) * (Real.log p / ((p:ℝ) - 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) ht0
        linarith
      · rw [if_neg hk, if_neg hk]
        have e : ((6 * (F:ℝ) * m * Mb + Sm) / ((p:ℝ) - 1) + 1) * Real.log p
            = (6 * F * m * Mb + Sm) * (Real.log p / ((p:ℝ) - 1)) + Real.log p := by ring
        rw [e]
        linarith

end GlobalTheory.SumBound

namespace GlobalTheory.SumBound

open Finset

theorem sum_ite_const (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (c : ℝ) :
    ∑ q ∈ s, (if P q then c else 0) = (s.filter P).card * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

theorem primeSum_eOf : ∀ (F N k m M : ℕ) (Mb Sm : ℝ) (vd : ℕ → ℝ) (large₂ ll : ℝ) (S₀ R : Finset ℕ), 0 ≤ Mb → 0 ≤ Sm → (∀ q, 0 ≤ vd q) →
    N + 1 = k + m → m ≤ k → 1 ≤ m → 1 ≤ large₂ → 1 ≤ ll → Real.log M ≤ large₂ → Real.log N ≤ large₂ → ∑ q ∈ S₀, (1 + vd q / 2) * Real.log q ≤ 3 / 2 * large₂ →
    Real.log (Real.log k) ≤ ll → R.card ≤ 2 → (∀ q ∈ R, N * Real.log q / ((q : ℝ) - 1) ≤ m * large₂) →
    PrimeSum ((Finset.range (M + 1)).filter Nat.Prime)
      (fun p => if p.Prime then eOf F N k m Mb Sm vd M S₀ R p else 0)
      (40 * ((F * m * Mb + Sm) * large₂ * ll + F * (N : ℝ) ^ 3 * large₂ + M)) := by
  intro F N k m M Mb Sm vd large₂ ll S₀ R hMb hSm hvd hNk hmk hm1 hLg hll hLM hLN hvdL hllk hRc hRq
  set S := (Finset.range (M + 1)).filter Nat.Prime with hS
  refine ⟨fun q hq => (mem_filter.1 hq).2, fun q => ?_, fun q hq => ?_, ?_⟩
  · beta_reduce
    split_ifs with h
    · exact eOf_nonneg F N k m Mb Sm vd M S₀ R hMb hSm hvd q h
    · exact le_rfl
  · beta_reduce
    split_ifs with h
    · have hqM : M < q := by
        by_contra hc
        exact hq (mem_filter.2 ⟨mem_range.2 (by omega), h⟩)
      unfold eOf; rw [if_pos hqM]
    · rfl

  have hF : (0:ℝ) ≤ F := Nat.cast_nonneg _
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hMn : (0:ℝ) ≤ M := Nat.cast_nonneg _
  have hX : 0 ≤ (F:ℝ) * m * Mb := by positivity
  have hA : 0 ≤ ((F:ℝ) * m * Mb + Sm) * large₂ := by nlinarith
  set A := ((F:ℝ) * m * Mb + Sm) * large₂ with hAdef
  set K := S.filter (fun q => m * q < k) with hK
  have step1 : ∑ q ∈ S, (if q.Prime then eOf F N k m Mb Sm vd M S₀ R q else 0) * Real.log q ≤
      ∑ q ∈ S, ((if q ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd q / 2) * Real.log q) else 0) + (if q ∈ R then A else 0)
      + (6 * F * m * Mb + Sm) * (Real.log q / ((q : ℝ) - 1)) + Real.log q
      + (if m * q < k then F * m * Mb * large₂ / 2 * (1 / ((q : ℝ) - 1)) + 2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂
          else 0)) := by
    apply Finset.sum_le_sum
    intro q hq
    have hqp := (mem_filter.1 hq).2
    have hqM : q ≤ M := by have := mem_range.1 (mem_filter.1 hq).1; omega
    rw [if_pos hqp]
    exact point_le F N k m M Mb Sm vd large₂ S₀ R hMb hSm hvd hLg hLM hRq q hqp hqM
  simp only [Finset.sum_add_distrib] at step1
  have t4 : ∑ q ∈ S, (if q ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd q / 2) * Real.log q) else 0) ≤ 3 / 2 * A := by
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    have h1 : ∑ q ∈ S.filter (fun q => q ∈ S₀), (1 + vd q / 2) * Real.log q ≤ ∑ q ∈ S₀, (1 + vd q / 2) * Real.log q :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (mem_filter.1 hx).2) fun q _ _ =>
        mul_nonneg (by have := hvd q; positivity) (Real.log_natCast_nonneg q)
    have h2 := mul_le_mul_of_nonneg_left (h1.trans hvdL) (show 0 ≤ (F:ℝ) * m * Mb + Sm by positivity)
    rw [hAdef]; linarith
  generalize (∑ q ∈ S, (if q ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd q / 2) * Real.log q) else 0)) = W₀ at step1 t4
  rw [sum_ite_const, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at step1

  have cR : ((S.filter (fun q => q ∈ R)).card : ℝ) ≤ 2 := by
    have : (S.filter (fun q => q ∈ R)).card ≤ R.card :=
      Finset.card_le_card (fun x hx => (mem_filter.1 hx).2)
    exact_mod_cast this.trans hRc
  have hmert : ∑ q ∈ S, Real.log q / ((q : ℝ) - 1) ≤ Real.log M + 2.2 :=
    GlobalTheory.PrimeLogSum.sum_log_div_pred_le M
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
  have hth : ∑ q ∈ S, Real.log q ≤ 3 * M := by
    have := sum_log_le M
    have h2 : (M:ℝ) * Real.log 4 ≤ M * 3 := mul_le_mul_of_nonneg_left hlog4 hMn
    linarith
  have hKS : ∀ q ∈ K, q.Prime ∧ m * q < k := fun q hq =>
    ⟨(mem_filter.1 (mem_filter.1 hq).1).2, (mem_filter.1 hq).2⟩
  have hrec : ∑ q ∈ K, 1 / ((q : ℝ) - 1) ≤ 13 * ll := by
    by_cases hk3 : 3 ≤ k
    · have sub : K ⊆ (Finset.range (k + 1)).filter Nat.Prime := by
        intro q hq
        obtain ⟨hp, hqk⟩ := hKS q hq
        refine mem_filter.2 ⟨mem_range.2 ?_, hp⟩
        have : q ≤ m * q := Nat.le_mul_of_pos_left q (by omega)
        omega
      have h1 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => 1 / ((q : ℝ) - 1)) sub (fun q hq _ => by
        have : (2:ℝ) ≤ q := by exact_mod_cast (mem_filter.1 hq).2.two_le
        have : (0:ℝ) < (q:ℝ) - 1 := by linarith
        positivity)
      have h2 := GlobalTheory.T.sum_primes_inv_pred_le_loglog k hk3
      linarith
    · have : K = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro q hq
        obtain ⟨hp, hqk⟩ := hKS q hq
        have : 2 ≤ m * q := le_trans hp.two_le (Nat.le_mul_of_pos_left q (by omega))
        omega
      rw [this, Finset.sum_empty]; linarith
  have hcard : (K.card : ℝ) * ((m:ℝ) + 1) ≤ 2 * N := by
    have sub : K ⊆ Finset.Icc 1 ((k - 1) / m) := by
      intro q hq
      obtain ⟨hp, hqk⟩ := hKS q hq
      refine Finset.mem_Icc.2 ⟨hp.one_lt.le, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega)]
      rw [Nat.mul_comm]; omega
    have h1 : K.card ≤ (k - 1) / m := by
      have := Finset.card_le_card sub
      simpa using this
    have h2 : K.card * m ≤ k - 1 := le_trans (Nat.mul_le_mul_right m h1) (Nat.div_mul_le_self _ _)
    have h3 : K.card ≤ K.card * m := Nat.le_mul_of_pos_right _ (by omega)
    have h4 : K.card * (m + 1) ≤ 2 * N := by rw [Nat.mul_succ]; omega
    exact_mod_cast h4

  have hLg0 : (0:ℝ) ≤ large₂ := by linarith
  have hll0 : (0:ℝ) ≤ ll := by linarith
  have t1 : (6 * (F:ℝ) * m * Mb + Sm) * ∑ q ∈ S, Real.log q / ((q : ℝ) - 1)
      ≤ (6 * (F:ℝ) * m * Mb + Sm) * (3.2 * large₂) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have t2 : (F:ℝ) * m * Mb * large₂ / 2 * ∑ q ∈ K, 1 / ((q : ℝ) - 1) ≤ (F:ℝ) * m * Mb * large₂ / 2 * (13 * ll) :=
    mul_le_mul_of_nonneg_left hrec (by positivity)
  have t3 : (K.card : ℝ) * (2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂) ≤ 2 * F * (N:ℝ) ^ 2 * large₂ * (2 * N) := by
    have e : (K.card : ℝ) * (2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂)
        = 2 * F * (N:ℝ) ^ 2 * large₂ * ((K.card : ℝ) * ((m:ℝ) + 1)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hcard (by positivity)
  have t5 : ((S.filter (fun q => q ∈ R)).card : ℝ) * A ≤ 2 * A := mul_le_mul_of_nonneg_right cR hA
  have t6 : A ≤ A * ll := le_mul_of_one_le_right hA hll
  have hSL : 0 ≤ Sm * large₂ := mul_nonneg hSm hLg0
  have t7 : (F:ℝ) * m * Mb * large₂ ≤ A := by rw [hAdef]; linarith
  have t8 : (F:ℝ) * m * Mb * large₂ * ll ≤ A * ll := mul_le_mul_of_nonneg_right t7 hll0
  have t9 : (6 * (F:ℝ) * m * Mb + Sm) * (3.2 * large₂) ≤ 96 / 5 * A := by rw [hAdef]; norm_num; linarith
  have t10 : 0 ≤ (F:ℝ) * (N:ℝ) ^ 3 * large₂ := by positivity
  clear_value A
  linarith

end GlobalTheory.SumBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedPrimeLogSumOscillationBoundLeStatement
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedPrimeLogSum_oscillationBound_le : ∀ (F N k m M : ℕ) (Mb Sm : ℝ) (vd : ℕ → ℝ) (large₂ ll : ℝ) (S₀ R : Finset ℕ), 0 ≤ Mb → 0 ≤ Sm → (∀ q, 0 ≤ vd q) → N + 1 = k + m → m ≤ k → 1 ≤ m → 1 ≤ large₂ → 1 ≤ ll → Real.log M ≤ large₂ → Real.log N ≤ large₂ → ∑ q ∈ S₀, (1 + vd q / 2) * Real.log q ≤ 3 / 2 * large₂ → Real.log (Real.log k) ≤ ll → R.card ≤ 2 → (∀ q ∈ R, N * Real.log q / ((q : ℝ) - 1) ≤ m * large₂) → PrimeSum ((Finset.range (M + 1)).filter Nat.Prime) (fun p => if p.Prime then eOf F N k m Mb Sm vd M S₀ R p else 0) (40 * ((F * m * Mb + Sm) * large₂ * ll + F * (N : ℝ) ^ 3 * large₂ + M)) := by
  first | exact @GlobalTheory.SumBound.primeSum_eOf | exact GlobalTheory.SumBound.primeSum_eOf | (intros; apply GlobalTheory.SumBound.primeSum_eOf <;> assumption)
end
end

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.RefSum

theorem len_mul_total_le {T F m q N B Sg b l x C₁ C₂ K U : ℝ} (hT : 1 ≤ T) (hF : 1 ≤ F) (hm : 1 ≤ m) (hq : q ≤ m)
    (hB : 0 ≤ B) (hb : 1 ≤ b) (hl : 1 ≤ l) (hx : 1 ≤ x) (h1 : 0 ≤ C₁) (h2 : 0 ≤ C₂) (hK : 0 ≤ K)
    (a1 : T * (B + 1) ≤ C₁ * b) (a2 : T * Sg ≤ C₁ * b) (a3 : T * N ^ 3 ≤ C₂ * b) (a4 : F * m * b * l * x ≤ C₂ * U) :
    T * (40 * ((F * m * (B + 1) + F * (Sg + 2 * q * B)) * (K * l) * (K * x) + F * N ^ 3 * (K * l) + (2 * B + 1))) ≤
      40 * (4 * C₁ * K ^ 2 + C₂ * K + 2 * C₁) * C₂ * U := by
  have hcb : 0 ≤ C₁ * b := by positivity
  have b1 : T * B ≤ C₁ * b := by nlinarith
  have b2 : q * (T * B) ≤ m * (C₁ * b) := mul_le_mul hq b1 (by positivity) (by positivity)
  have b3 : m * (T * (B + 1)) ≤ m * (C₁ * b) := mul_le_mul_of_nonneg_left a1 (by positivity)
  have b4 : C₁ * b ≤ m * (C₁ * b) := le_mul_of_one_le_left hcb hm
  have b5 : T * (m * (B + 1) + (Sg + 2 * q * B)) ≤ 4 * (m * (C₁ * b)) := by nlinarith
  have c1 : T * (m * (B + 1) + (Sg + 2 * q * B)) * (F * (K * l) * (K * x)) ≤
      4 * (m * (C₁ * b)) * (F * (K * l) * (K * x)) := mul_le_mul_of_nonneg_right b5 (by positivity)
  have hmx : 1 ≤ m * x := one_le_mul_of_one_le_of_one_le hm hx
  have c2 : T * N ^ 3 * (F * (K * l)) ≤ C₂ * b * (F * (K * l)) := mul_le_mul_of_nonneg_right a3 (by positivity)
  have c3 : C₂ * b * (F * (K * l)) ≤ C₂ * b * (F * (K * l)) * (m * x) := le_mul_of_one_le_right (by positivity) hmx
  have hall : 1 ≤ F * l * (m * x) := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hF hl) hmx
  have c4 : C₁ * b ≤ C₁ * b * (F * l * (m * x)) := le_mul_of_one_le_right hcb hall
  have c5 : T * (2 * B + 1) ≤ 2 * (C₁ * b) := by nlinarith
  have c6 : (4 * C₁ * K ^ 2 + C₂ * K + 2 * C₁) * (F * m * b * l * x) ≤ (4 * C₁ * K ^ 2 + C₂ * K + 2 * C₁) * (C₂ * U) :=
    mul_le_mul_of_nonneg_left a4 (by positivity)
  nlinarith

theorem log_top_le {T B b l C₁ C₂ : ℝ} (hT : 1 ≤ T) (hB : 0 ≤ B) (hb : 1 ≤ b) (hl : 1 ≤ l) (h1 : 0 ≤ C₁)
    (a1 : T * (B + 1) ≤ C₁ * b) (a2 : Real.log b ≤ C₂ * l) : Real.log (2 * B + 1) ≤ (2 * C₁ + C₂ + 1) * l := by
  have b1 : B + 1 ≤ C₁ * b := by nlinarith
  have b2 : Real.log (2 * B + 1) ≤ Real.log ((2 * C₁ + 1) * b) := Real.log_le_log (by positivity) (by nlinarith)
  rw [Real.log_mul (by positivity) (by positivity)] at b2
  have b3 : Real.log (2 * C₁ + 1) ≤ 2 * C₁ + 1 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  nlinarith

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem sumAt_of_sizes {PP C₁ C₂ : ℝ} (h1 : 0 ≤ C₁) (h2 : 0 ≤ C₂) (u1 : GlobalTheory.AllWt.Weight (dat p i))
    (hw : WtAt p i PP C₁ u1) (hn : NumAt p i PP C₂) :
    GlobalTheory.RefSum.SumAt p i PP
      (40 * (4 * C₁ * (2 * C₁ + C₂ + 1) ^ 2 + C₂ * (2 * C₁ + C₂ + 1) + 2 * C₁) * C₂) u1 := by
  obtain ⟨hs, hk, B, Sg, hwt, a1, a2, hT1⟩ := hw
  obtain ⟨hl, hb, n1, hx, n2, n3, n4, n5, n6, n7⟩ := hn
  have hT1' : (1 : ℝ) ≤ lenT p i PP := by exact_mod_cast hT1
  have hexp := GlobalTheory.T.thetaExponents_bigSmallFactorBounds _ _ (dat p i) D.R.f D.R.k D.R.m (nCol (dat p i)) B Sg u1 hs hk hwt
  have hd : p.T.Q.H.d = D.host.d := p.fw.laws.pins.1.1
  have htwo := GlobalTheory.CharDepth.twoPlaces_host D p.T.Q.H hd
  have hvd : ∀ q, 0 ≤ D.host.vdH q := D.host.vdH_nonneg
  obtain ⟨hsum, h2S, hunr⟩ := UpperTheory.KR.small_vd_sum D.host.toHostAx
  have hN : (dat p i).p + (dat p i).q = D.R.r := by
    have := hs.1
    unfold Ranks.r
    omega
  have hF : (1 : ℝ) ≤ D.R.f := by
    have hn : 0 < D.R.n := D.R.ord_pos
    exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast hs.2.2.2.1
  have hq : ((dat p i).q : ℝ) ≤ D.R.m := by exact_mod_cast hs.2.1
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  set K : ℝ := 2 * C₁ + C₂ + 1 with hK
  have hK1 : 1 ≤ K := by linarith
  have hK2 : C₂ ≤ K := by linarith
  have hKl : C₂ * L.sc.L ≤ K * L.sc.L := mul_le_mul_of_nonneg_right hK2 (by linarith)
  have hnum := GlobalTheory.T.weightedPrimeLogSum_oscillationBound_le D.R.f D.R.r D.R.k D.R.m (2 * B + 1) (B + 1) (D.R.f * (Sg + 2 * (dat p i).q * B))
    D.host.vdH (K * L.sc.L) (K * Real.log (Real.log L.sc.x)) D.host.small {D.host.q, D.host.d} hexp.1
    ((Nat.cast_nonneg _).trans hexp.2.2.1) hvd (hN ▸ hs.1) hs.2.2.1 hs.2.2.2.1
    (one_le_mul_of_one_le_of_one_le hK1 hl) (one_le_mul_of_one_le_of_one_le hK1 hx)
    (by push_cast; exact log_top_le hT1' hB hb hl h1 a1 n1) (n4.trans hKl)
    (hsum.trans (mul_le_mul_of_nonneg_left (n5.trans hKl) (by norm_num)))
    (n3.trans (mul_le_mul_of_nonneg_right hK2 (by linarith))) Finset.card_le_two
    (fun q hq => (n7 q hq).trans (by nlinarith))
  refine ⟨_, _, _, hnum, ?_, fun q hqp _ => ?_⟩
  · push_cast
    exact len_mul_total_le hT1' hF hm hq hB hb hl hx h1 h2 (by linarith) a1 a2 n6 n2
  · have := GlobalTheory.T.depthOscillation_le_bound_every_prime _ _ (dat p i) _ (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c D.R.f D.R.k D.R.m (2 * B + 1) (B + 1) _ _ hs hexp
      D.host.vdH D.host.small {D.host.q, D.host.d} hvd (fun r _ hr => (htwo r hr).2.1) h2S (by simp [hd])
      (fun r hr hr2 hrR => hunr r hr hr2
        (fun h => hrR (by simp [h])) (fun h => hrR (by simp [h]))) q
    rw [hN] at this
    simpa only [if_pos hqp.out] using this

end Point

end GlobalTheory.RefSum

end
