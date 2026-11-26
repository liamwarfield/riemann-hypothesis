module

public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PrimeRpowNegLevelLe

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.DfcHigh
noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

variable {D : D7} {L : SizeData₂ D}


open Classical in
def dropI (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : ℝ :=
  if L.sc.x ^ (-L.sc.eps) < Sig X K a b p then 1 else 0

theorem dropI_nonneg (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : 0 ≤ dropI X K a b p := by
  unfold dropI; split_ifs <;> norm_num

theorem WReq_iff (X : Inst D L) (K : Consts) (a b : HH D → ℤ) :
    WReq X K a b ↔ ∑ p ∈ candF D L K, Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) ≤
      L.sc.x ^ (-9 : ℝ) := Iff.rfl

theorem mem_candF {K : Consts} {p : ℕ} (h : Cand D L K p) : p ∈ candF D L K := by
  classical
  unfold candF
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_ceil.2 h.2.1), h⟩

theorem cand_of_mem {K : Consts} {p : ℕ} (h : p ∈ candF D L K) : Cand D L K p := by
  classical
  unfold candF at h
  exact (Finset.mem_filter.1 h).2

theorem lp_nonneg (p : ℕ) : 0 ≤ Real.log p / p := div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

theorem lifts_card (D : D7) : (SizeData₂.lifts D).card = D.R.m := by unfold SizeData₂.lifts; simp

def Dfc (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : ℝ :=
  (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s) -
    ((∑ j ∈ SizeData₂.lifts D, gainP X K a b p j) - tauP X K a b p - ioP X K a b p)

theorem io_le (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) {a b : HH D → ℤ} (h : InWin L a b)
    (hSig : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p) (p : ℕ) :
    Real.log p * ioP X K a b p ≤
      (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) *
        (((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) := by
  classical
  have ha := sc_one_lt_a L.sc
  unfold ioP
  split_ifs with hne hc hc
  · have hC := cand_of_mem hc
    have hp := hC.1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hs := hSig p hC
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hsup : (VV X K a b p).sup' hne (fun t0 => Sv X K a b p t0) ≤
        2 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a / p := by
      apply Finset.sup'_le
      intro t0 _
      refine le_trans (sv_le X K hK P h p hp hC.2.1 t0) ?_
      rw [div_le_div_iff_of_pos_right hp0]
      have hN : (Nv X p t0 : ℝ) ≤ (D.host.TT.card : ℝ) := by
        unfold Nv topsOn
        exact_mod_cast Finset.card_filter_le _ _
      have hm : (0 : ℝ) ≤ 2 * (D.R.m : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_left hN hm
      exact mul_le_mul_of_nonneg_right this (by linarith)
    have h1 : 2 * Sig X K a b p * (VV X K a b p).sup' hne (fun t0 => Sv X K a b p t0) ≤
        2 * Sig X K a b p * (2 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a / p) :=
      mul_le_mul_of_nonneg_left hsup (by linarith)
    have h2 := mul_le_mul_of_nonneg_left h1 hl
    refine le_trans h2 ?_
    have hd := dropI_nonneg X K a b p
    have h3 : 0 ≤ Real.log p / p * dropI X K a b p * (((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) := by
      have := lp_nonneg p
      positivity
    have e : Real.log p * (2 * Sig X K a b p * (2 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a / p)) =
        Real.log p / p * Sig X K a b p * (4 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) := by
      field_simp
      ring
    rw [e]
    linarith
  · exact absurd (mem_candF (cand_of_VV_ne X K a b p (Finset.nonempty_iff_ne_empty.1 hne))) hc
  · have hC := cand_of_mem hc
    have := hSig p hC
    have := dropI_nonneg X K a b p
    have := lp_nonneg p
    rw [mul_zero]
    positivity
  · simp

theorem not_singular_of_central {p : ℕ} (h : IsResidueClassZero D p) : ¬ IsSg D p := by
  intro h'
  unfold IsResidueClassZero at h
  unfold IsSg at h'
  rw [h] at h'
  cases h'

theorem TTP_subset (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : TTP X K a b p ⊆ D.host.TT := by
  unfold TTP
  split_ifs
  · exact Finset.Subset.refl _
  · exact Finset.filter_subset _ _

theorem sdiff_le (X : Inst D L) (K : Consts) {a b : HH D → ℤ}
    (hSig : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p)
    (A3 A4 PS : Finset ℕ) (badf : ℕ → ℝ)
    (hA3 : ∀ p : ℕ, p.Prime → IsResidueClassZero D p → (p : ℝ) < L.sc.X' →
      (addOrderOf (hP D p) : ℝ) < L.sc.x ^ (L.sc.eps / 4) → p ∈ A3)
    (hA4 : ∀ p : ℕ, p.Prime → (p : ℝ) < L.sc.X' → InBand D K L.sc p → p ∈ A4)
    (hPS : ∀ p, Cand D L K p → p ∈ PS)
    (hbad : ∀ p, Cand D L K p →
      ((D.host.TT \ D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ goodReps X p)).card : ℝ) ≤ badf p)
    (hbad0 : ∀ p, 0 ≤ badf p) (p : ℕ) (hp : p.Prime) (hc0 : IsResidueClassZero D p) :
    Real.log p / p * ((D.host.TT \ TTP X K a b p).card : ℝ) ≤
      (if p ∈ A3 then Real.log p / p else 0) * (D.host.TT.card : ℝ) +
      (if p ∈ A4 then Real.log p / p else 0) * (D.host.TT.card : ℝ) +
      (if p ∈ PS then Real.log p / p * badf p else 0) +
      (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) * (D.host.TT.card : ℝ) := by
  classical
  have hlp := lp_nonneg p
  have hN : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
  have t3 : 0 ≤ (if p ∈ A3 then Real.log p / p else 0) * (D.host.TT.card : ℝ) := by
    split_ifs <;> positivity
  have t4 : 0 ≤ (if p ∈ A4 then Real.log p / p else 0) * (D.host.TT.card : ℝ) := by
    split_ifs <;> positivity
  have t2 : 0 ≤ (if p ∈ PS then Real.log p / p * badf p else 0) := by
    split_ifs
    · exact mul_nonneg hlp (hbad0 p)
    · exact le_rfl
  have t8 : 0 ≤ (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) *
      (D.host.TT.card : ℝ) := by
    split_ifs with hc
    · have := hSig p (cand_of_mem hc)
      have := dropI_nonneg X K a b p
      positivity
    · simp
  have hall : ((D.host.TT \ TTP X K a b p).card : ℝ) ≤ (D.host.TT.card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  have hall' := mul_le_mul_of_nonneg_left hall hlp
  by_cases hX : (p : ℝ) < L.sc.X'
  · by_cases ho : (addOrderOf (hP D p) : ℝ) < L.sc.x ^ (L.sc.eps / 4)
    · rw [if_pos (hA3 p hp hc0 hX ho)] at t3 ⊢
      linarith
    · by_cases hb : L.sc.p0 D.R.k ≤ (p : ℝ) ∧ InBand D K L.sc p
      · rw [if_pos (hA4 p hp hX hb.2)] at t4 ⊢
        linarith
      · have hC : Cand D L K p := ⟨hp, hX, hc0, not_lt.1 ho, fun h1 h2 => hb ⟨h1, h2⟩⟩
        have hs := hSig p hC
        by_cases hd : Sig X K a b p ≤ L.sc.x ^ (-L.sc.eps)
        · have hVV : VV X K a b p = goodReps X p := by unfold VV; rw [if_pos ⟨hC, hd⟩]
          have hT : TTP X K a b p = D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ goodReps X p) := by
            unfold TTP
            rw [if_neg (by
              intro h
              rcases h with h | h
              · exact not_singular_of_central hc0 h
              · linarith), hVV]
          rw [hT, if_pos (hPS p hC)] at *
          have := mul_le_mul_of_nonneg_left (hbad p hC) hlp
          linarith
        · have hdI : dropI X K a b p = 1 := by unfold dropI; rw [if_pos (not_le.1 hd)]
          rw [if_pos (mem_candF hC), hdI] at t8 ⊢
          have : Real.log p / p * (D.host.TT.card : ℝ) ≤
              Real.log p / p * (2 * 1 + 4 * Sig X K a b p) * (D.host.TT.card : ℝ) := by
            have h1 : Real.log p / p ≤ Real.log p / p * (2 * 1 + 4 * Sig X K a b p) := by nlinarith
            exact mul_le_mul_of_nonneg_right h1 hN
          linarith
  · have hT : TTP X K a b p = D.host.TT := by
      unfold TTP
      rw [if_pos (Or.inr (not_lt.1 hX))]
    rw [hT, Finset.sdiff_self, Finset.card_empty, Nat.cast_zero, mul_zero]
    linarith

theorem dfc_le (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (C bo : ℝ) {a b : HH D → ℤ} (h : InWin L a b) (hG : GainBoundAt X K C bo a b)
    (p : ℕ) (hp : p.Prime) (hc0 : IsResidueClassZero D p) (hpX : (p : ℝ) ≤ L.sc.X'' D.R.n) (hlo : 0 ≤ lo K L C bo p) :
    Dfc X K a b p ≤ (D.R.m : ℝ) * (((D.host.TT \ TTP X K a b p).card : ℝ) * (3 * L.sc.a / p)) +
      (D.R.m : ℝ) * ((D.host.TT.card : ℝ) * lo K L C bo p) + (D.R.m : ℝ) * fl D L.sc C p + ioP X K a b p := by
  classical
  have g := (hG p hp (Or.inl hc0) hpX).2
  have hsub := TTP_subset X K a b p
  have hj : ∀ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s ≤
      ∑ s ∈ TTP X K a b p, (askG X a b p j s - lo K L C bo p) +
        (((D.host.TT \ TTP X K a b p).card : ℝ) * (3 * L.sc.a / p) + (D.host.TT.card : ℝ) * lo K L C bo p) := by
    intro j hjl
    rw [← Finset.sum_sdiff hsub, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have h1 : ∑ s ∈ D.host.TT \ TTP X K a b p, askG X a b p j s ≤
        ((D.host.TT \ TTP X K a b p).card : ℝ) * (3 * L.sc.a / p) := by
      rw [← nsmul_eq_mul]
      apply Finset.sum_le_card_nsmul
      intro s hs
      exact (ask_bounds P X h p hp j hjl s (Finset.mem_sdiff.1 hs).1).2
    have h2 : ((TTP X K a b p).card : ℝ) * lo K L C bo p ≤ (D.host.TT.card : ℝ) * lo K L C bo p := by
      apply mul_le_mul_of_nonneg_right _ hlo
      exact_mod_cast Finset.card_le_card hsub
    linarith
  have hs := Finset.sum_le_sum hj
  rw [Finset.sum_add_distrib, Finset.sum_const, lifts_card, nsmul_eq_mul] at hs
  unfold Dfc
  linarith

theorem dfc_high (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) {a b : HH D → ℤ} (h : InWin L a b)
    (p : ℕ) (hpX : L.sc.X'' D.R.n < (p : ℝ)) :
    Dfc X K a b p ≤ (D.R.m : ℝ) * ((D.host.TT.card : ℝ) *
      (if (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L) then thW D L.sc * L.sc.w'' D.R.n + L.Sc else 0)) := by
  classical
  have hVV : VV X K a b p = ∅ := by
    by_contra hne
    have hC := cand_of_VV_ne X K a b p hne
    have := X'_le_X'' L.sc D.R.n (n_pos D)
    have := hC.2.1
    linarith
  have hg : ∀ j, gainP X K a b p j = 0 := by
    intro j; unfold gainP; rw [if_pos (Or.inr hpX)]
  have ht : tauP X K a b p = 0 := by unfold tauP; rw [if_pos hVV]
  have hi : ioP X K a b p = 0 := by
    unfold ioP; rw [dite_eq_right (by rw [hVV]; simp)]
  unfold Dfc
  rw [ht, hi]
  simp only [hg, Finset.sum_const_zero, sub_zero]
  have hj : ∀ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s ≤ (D.host.TT.card : ℝ) *
      (if (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L) then thW D L.sc * L.sc.w'' D.R.n + L.Sc else 0) := by
    intro j hjl
    rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro s hs
    exact ask_high P X h p hpX j hjl s hs
  have hs := Finset.sum_le_card_nsmul _ _ _ hj
  rw [lifts_card, nsmul_eq_mul] at hs
  exact hs

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
end

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

variable {D : D7} {L : SizeData₂ D}

def lX (s : Scale) : ℝ := Real.log s.X' * (1 + Real.log s.X')

structure PrimeSumNumericFacts (D : D7) (L : SizeData₂ D) (K : Consts) (C bo : ℝ) : Prop where

  one_le_card_tops : (1 : ℝ) ≤ (D.host.TT.card : ℝ)

  n1 : c1 L C * (L.sc.X'' D.R.n + 2) ≤ L.sc.a / L.sc.x / 40

  n1' : cfl D L.sc C * (L.sc.X'' D.R.n + 2) ≤ L.sc.a / L.sc.x / 40

  n2 : Real.log 4 * L.sc.p0 D.R.k * c2 L C ≤ L.sc.a / L.sc.x / 40

  n3 : Real.log 4 * L.sc.X' * c3 L C bo ≤ 3 / 2 * (L.sc.a / L.sc.x)

  n4 : lX L.sc * c4 K L C ≤ L.sc.a / L.sc.x / 40

  n5 : 120 ≤ L.sc.x

  n7 : L.sc.x ^ (-2 + L.sc.eps) ≤ 1 / L.sc.x / 120

  n9 : (L.sc.X'' D.R.n * thS L + 2) * (Real.log (2 * L.sc.X'' D.R.n) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc)) ≤
    L.sc.a / L.sc.x / 40

theorem first_constant_nonneg (L : SizeData₂ D) (C : ℝ) (hC : 0 ≤ C) : 0 ≤ c1 L C := by
  unfold c1 cG
  have := L.Sc_pos
  have := L.etaSz_pos
  have ha := sc_one_lt_a L.sc
  exact mul_nonneg (mul_nonneg hC (by linarith)) (Real.log_nonneg (by linarith))

theorem second_constant_nonneg (L : SizeData₂ D) (C : ℝ) (hC : 0 ≤ C) : 0 ≤ c2 L C := by
  unfold c2
  have hk := k_ge D
  have hx := sc_x_pos L.sc
  have ha := sc_one_lt_a L.sc
  have hlx := logx_nonneg L.sc
  have hb' := sc_b'_nonneg L.sc
  have h1 : 0 ≤ C * (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) hb') hlx
  have h2 : 0 ≤ C * Real.log L.sc.x * (L.sc.a * ((((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4)⁻¹)) :=
    mul_nonneg (mul_nonneg hC hlx) (mul_nonneg (by linarith) (by positivity))
  linarith

theorem fourth_constant_nonneg (K : Consts) (hK : 0 ≤ K.La) (L : SizeData₂ D) (C : ℝ) (hC : 0 ≤ C) : 0 ≤ c4 K L C := by
  unfold c4
  have hk := k_ge D
  have ha := sc_one_lt_a L.sc
  have hLa := La_nonneg K hK L.sc
  have hP0 := p0_pos D L.sc
  exact mul_nonneg (mul_nonneg hC (logx_nonneg _))
    (add_nonneg (div_nonneg (mul_nonneg hLa (by linarith)) (by linarith)) (div_nonneg (by linarith) hP0.le))

theorem cfl_nonneg (D : D7) (s : Scale) (C : ℝ) (hC : 0 ≤ C) : 0 ≤ cfl D s C := by
  unfold cfl
  have hla : 0 ≤ Real.log s.a := Real.log_nonneg (sc_one_lt_a s).le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (add_nonneg (mul_nonneg (by positivity) hla) (by positivity))

theorem one_le_X' (s : Scale) : 1 ≤ s.X' := by
  unfold Scale.X'; exact Real.one_le_exp (Real.rpow_nonneg (sc_x_pos s).le _)

structure Sets (X : Inst D L) (K : Consts) (A3 A4 PS : Finset ℕ) (badf : ℕ → ℝ) : Prop where
  hA3 : ∀ p : ℕ, p.Prime → IsResidueClassZero D p → (p : ℝ) < L.sc.X' →
      (addOrderOf (hP D p) : ℝ) < L.sc.x ^ (L.sc.eps / 4) → p ∈ A3
  hA4 : ∀ p : ℕ, p.Prime → (p : ℝ) < L.sc.X' → InBand D K L.sc p → p ∈ A4
  hPS : ∀ p, Cand D L K p → p ∈ PS
  hPSsub : PS ⊆ prB L.sc.X'
  hbad : ∀ p, Cand D L K p →
      ((D.host.TT \ D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ goodReps X p)).card : ℝ) ≤ badf p
  hbad0 : ∀ p, 0 ≤ badf p
  s3 : ∑ p ∈ A3, Real.log p / p ≤ L.sc.x ^ (-hG L.sc + L.sc.eps)
  s4 : ∑ p ∈ A4, Real.log p / p ≤ L.sc.x ^ (-1 : ℝ)
  s2 : ∑ p ∈ PS, Real.log p / p * badf p ≤ (D.host.TT.card : ℝ) * L.sc.x ^ (-2 + L.sc.eps)

def E1 (X : Inst D L) (K : Consts) (C bo : ℝ) (a b : HH D → ℤ) (A3 A4 PS : Finset ℕ) (badf : ℕ → ℝ) (p : ℕ) : ℝ :=
  (if p ∈ prB (L.sc.X'' D.R.n + 1) then (1 : ℝ) else 0) *
      ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * c1 L C + (D.R.m : ℝ) * cfl D L.sc C) +
  (if p ∈ prB (L.sc.p0 D.R.k) then Real.log p else 0) * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * c2 L C) +
  (if p ∈ prB L.sc.X' then Real.log p else 0) * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * c3 L C bo) +
  (if p ∈ prB L.sc.X' then Real.log p / p else 0) * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * c4 K L C) +
  (if p ∈ A3 then Real.log p / p else 0) * (3 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) +
  (if p ∈ A4 then Real.log p / p else 0) * (3 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) +
  (if p ∈ PS then Real.log p / p * badf p else 0) * (3 * (D.R.m : ℝ) * L.sc.a) +
  (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) *
      (4 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a)

theorem low_le (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) (C bo : ℝ) (hC : 0 ≤ C) (hbo : 0 ≤ bo)
    {a b : HH D → ℤ} (h : InWin L a b) (hG : GainBoundAt X K C bo a b)
    (hSig : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p)
    {A3 A4 PS : Finset ℕ} {badf : ℕ → ℝ} (T : Sets X K A3 A4 PS badf)
    (p : ℕ) (hp : p.Prime) (hc0 : IsResidueClassZero D p) (hpX : (p : ℝ) ≤ L.sc.X'' D.R.n) :
    Real.log p * max 0 (Dfc X K a b p) ≤ E1 X K C bo a b A3 A4 PS badf p := by
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have ha := sc_one_lt_a L.sc
  have hm : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
  obtain ⟨hlo0, hlo⟩ := lo_bounds K hK.1 L C bo hC hbo p hp hc0
  obtain ⟨hfl0, hfl⟩ := fl_bounds D L.sc C hC p hp
  have hio := io_le X K hK P h hSig p
  have hsd := sdiff_le X K hSig A3 A4 PS badf T.hA3 T.hA4 T.hPS T.hbad T.hbad0 p hp hc0
  have hd := dfc_le P X K C bo h hG p hp hc0 hpX hlo0
  have m1 : p ∈ prB (L.sc.X'' D.R.n + 1) := mem_prB.2 ⟨hp, by linarith⟩
  have hsd0 : 0 ≤ Real.log p / p * ((D.host.TT \ TTP X K a b p).card : ℝ) :=
    mul_nonneg (lp_nonneg p) (Nat.cast_nonneg _)
  have hiob : 0 ≤ (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) *
        (((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) := by
    split_ifs with hc
    · have := hSig p (cand_of_mem hc)
      have := dropI_nonneg X K a b p
      have := lp_nonneg p
      positivity
    · simp
  have k1 := mul_le_mul_of_nonneg_left hsd (by positivity : (0 : ℝ) ≤ 3 * (D.R.m : ℝ) * L.sc.a)
  have k2 := mul_le_mul_of_nonneg_left hlo (mul_nonneg hm hN)
  have k3 := mul_le_mul_of_nonneg_left hfl hm
  have k4 := mul_le_mul_of_nonneg_left hd hl
  have k10 : 0 ≤ 3 * (D.R.m : ℝ) * L.sc.a * (Real.log p / p * ((D.host.TT \ TTP X K a b p).card : ℝ)) :=
    mul_nonneg (by positivity) hsd0
  have k20 : 0 ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (Real.log p * lo K L C bo p) :=
    mul_nonneg (mul_nonneg hm hN) (mul_nonneg hl hlo0)
  have k30 : 0 ≤ (D.R.m : ℝ) * (Real.log p * fl D L.sc C p) := mul_nonneg hm (mul_nonneg hl hfl0)
  have e : Real.log p * ((D.R.m : ℝ) * (((D.host.TT \ TTP X K a b p).card : ℝ) * (3 * L.sc.a / p)) +
      (D.R.m : ℝ) * ((D.host.TT.card : ℝ) * lo K L C bo p) + (D.R.m : ℝ) * fl D L.sc C p + ioP X K a b p) =
      3 * (D.R.m : ℝ) * L.sc.a * (Real.log p / p * ((D.host.TT \ TTP X K a b p).card : ℝ)) +
      (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (Real.log p * lo K L C bo p) +
      (D.R.m : ℝ) * (Real.log p * fl D L.sc C p) + Real.log p * ioP X K a b p := by ring
  rw [e] at k4
  rw [mul_max_of_nonneg _ _ hl, mul_zero]
  unfold E1
  rw [if_pos m1]
  apply max_le <;> linarith

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
