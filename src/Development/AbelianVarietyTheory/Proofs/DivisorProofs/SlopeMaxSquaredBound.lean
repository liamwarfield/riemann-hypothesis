module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogSupNormLossLeLinearInWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogSupNormLossLeLinearInWeight
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.LamSize

theorem one_le_fdeg_of_cm (E : Type) [Field E] [NumberField E] [IsCMField E] : 1 ≤ fdeg E := by
  have h : Module.finrank ℚ E = 2 * fdeg E := by rw [fdeg, IsTotallyComplex.finrank E]; omega
  have := Module.finrank_pos (R := ℚ) (M := E)
  omega

theorem one_le_dE_field (E : Type) [Field E] [NumberField E] : 1 ≤ dE E := by
  unfold dE
  have h := Int.one_le_abs (NumberField.discr_ne_zero E)
  rw [← Int.cast_abs]
  exact_mod_cast h

theorem neg_log_epStar_le (f M d w : ℝ) (hf : 1 ≤ f) (hM : 1 ≤ M) (hd : 1 ≤ d) (hw : 1 ≤ w) :
    0 < epStar (2 * M * Real.sqrt d) f w 1 ∧ epStar (2 * M * Real.sqrt d) f w 1 ≤ 1 ∧
      -Real.log (epStar (2 * M * Real.sqrt d) f w 1) ≤
        Real.log 2 + Real.log M + 1 / 2 * Real.log d + Real.log f + Real.log w := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hpi := Real.pi_gt_three
  have hsd : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact hd
  have hfw : 1 ≤ f * w := one_le_mul_of_one_le_of_one_le hf hw
  set A := 2 * M * Real.sqrt d * f * w with hA
  have hA1 : 1 ≤ A := by
    have h1 : 1 ≤ M * Real.sqrt d := one_le_mul_of_one_le_of_one_le hM hsd
    have : A = 2 * (M * Real.sqrt d) * (f * w) := by rw [hA]; ring
    rw [this]; nlinarith
  have hA0 : 0 < A := by linarith
  have hB : 0 < 2 * M * Real.sqrt d * (f * w + 2) * 1 * Real.log 2 := by positivity
  have hlow : 1 / A ≤ epStar (2 * M * Real.sqrt d) f w 1 := by
    unfold epStar
    refine le_min ((div_le_one hA0).2 hA1) ?_
    rw [div_le_div_iff₀ hA0 hB]
    have hMd : 0 < 2 * M * Real.sqrt d := by positivity
    have key : (f * w + 2) * Real.log 2 ≤ Real.pi * (f * w) := by nlinarith
    have : 1 * (2 * M * Real.sqrt d * (f * w + 2) * 1 * Real.log 2) = (2 * M * Real.sqrt d) * ((f * w + 2) * Real.log 2) := by ring
    rw [this]
    have : Real.pi * A = (2 * M * Real.sqrt d) * (Real.pi * (f * w)) := by rw [hA]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left key hMd.le
  have he0 : 0 < epStar (2 * M * Real.sqrt d) f w 1 := lt_of_lt_of_le (by positivity) hlow
  refine ⟨he0, min_le_left _ _, ?_⟩
  have h1 : Real.log (1 / A) ≤ Real.log (epStar (2 * M * Real.sqrt d) f w 1) :=
    Real.log_le_log (by positivity) hlow
  rw [one_div, Real.log_inv] at h1
  have hlA : Real.log A = Real.log 2 + Real.log M + 1 / 2 * Real.log d + Real.log f + Real.log w := by
    rw [hA, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_sqrt (by linarith)]
    ring
  linarith

theorem log_radius_le (E : Type) [Field E] [NumberField E] [IsCMField E] (r d M : ℕ) (w L : ℝ)
    (hr : 1 ≤ r) (hd : 1 ≤ d) (hM : 1 ≤ M) (hL : 1 ≤ L) (hw : 1 ≤ w)
    (hfr : Real.log (fdeg E * r) ≤ L) (hlM : Real.log M ≤ 30 * L) (hdE : Real.log (dE E) ≤ 4 * fdeg E * L)
    (hld : Real.log d ≤ 4 * L) (hlw : Real.log w ≤ 2 * L) :
    1 ≤ 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E) (Real.sqrt (epsLev E d M w) / Real.sqrt (fdeg E)))
      (3 * frameRadius w r / 5) ∧
    Real.log (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E) (Real.sqrt (epsLev E d M w) / Real.sqrt (fdeg E)))
      (3 * frameRadius w r / 5)) ≤ (4 * fdeg E + 32) * L := by
  have hf1 := one_le_fdeg_of_cm E
  have hf' : (1 : ℝ) ≤ fdeg E := by exact_mod_cast hf1
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hdE1 := one_le_dE_field E
  obtain ⟨he0, he1, hne⟩ := neg_log_epStar_le (fdeg E) M d w hf' hM' hd' hw
  have hepsdef : epsLev E d M w = epStar (2 * M * Real.sqrt d) (fdeg E) w 1 := rfl
  rw [← hepsdef] at he0 he1 hne
  obtain ⟨hX0, hX⟩ := GlobalTheory.room_log_radius (fdeg E) r (dE E) (epsLev E d M w) w hf1 hr hdE1 he0 hw
  set X := 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E) (Real.sqrt (epsLev E d M w) / Real.sqrt (fdeg E)))
    (3 * frameRadius w r / 5) with hXdef
  clear_value X
  have hle : Real.log (epsLev E d M w) ≤ 0 := Real.log_nonpos he0.le he1
  have hn : (1 : ℝ) ≤ (fdeg E : ℝ) * r := one_le_mul_of_one_le_of_one_le hf' hr'
  have a1 : 0 ≤ Real.log (dE E) := Real.log_nonneg hdE1
  have a2 : 0 ≤ Real.log w := Real.log_nonneg hw
  have a3 : 0 ≤ Real.log (fdeg E : ℝ) := Real.log_nonneg hf'
  have a4 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr'
  have a5 : 0 ≤ Real.log ((fdeg E : ℝ) * r) := Real.log_nonneg hn
  have a6 : 0 ≤ Real.log (1600 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have a7 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hM'
  have a8 : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd'
  have hmul : Real.log ((fdeg E : ℝ) * r) = Real.log (fdeg E : ℝ) + Real.log r :=
    Real.log_mul (by positivity) (by positivity)
  have hc : Real.log (1600 / 3 : ℝ) ≤ 7 := by
    have h1 : Real.log (1600 / 3 : ℝ) ≤ Real.log ((2 : ℝ) ^ 10) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h1
    have := Real.log_two_lt_d9
    push_cast at h1
    linarith
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hfdL : 0 ≤ (fdeg E : ℝ) * L := by positivity
  have hX1 : 0 ≤ Real.log X := by rw [hX]; linarith
  refine ⟨?_, ?_⟩
  · by_contra hc'
    have := Real.log_neg hX0 (not_le.1 hc')
    linarith
  · rw [hX]
    have : (4 * (fdeg E : ℝ) + 32) * L = 4 * ((fdeg E : ℝ) * L) + 32 * L := by ring
    rw [this]
    linarith

theorem lamSup_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r q d M : ℕ) (Om s t L : ℝ), 1 ≤ r → 1 ≤ d → 1 ≤ M → 1 ≤ L → 0 ≤ s → 0 ≤ t → Real.log (fdeg E * r) ≤ L → Real.log M ≤ 30 * L → Real.log (dE E) ≤ 4 * fdeg E * L → Real.log d ≤ 4 * L → Real.log (s + t + 1) ≤ 2 * L → lamSup E r q d M Om s t ≤ ((1 + |Om|) / 2 + L + (2 * q + 1) * (6 * fdeg E + 48) * L) * (s + t) := by
  intro E _ _ _ r q d M Om s t L hr hd hM hL hs ht hfr hlM hdE hld hlw
  have hw : (1 : ℝ) ≤ s + t + 1 := by linarith
  obtain ⟨hX1, hXle⟩ := log_radius_le E r d M (s + t + 1) L hr hd hM hL hw hfr hlM hdE hld hlw
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hcm : cmLen E r q d M (s + t + 1) = (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E)
      (Real.sqrt (epsLev E d M (s + t + 1)) / Real.sqrt (fdeg E))) (3 * frameRadius (s + t + 1) r / 5)) ^ (2 * q + 1) := rfl
  unfold lamSup
  rw [hcm]
  set X := 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E)
      (Real.sqrt (epsLev E d M (s + t + 1)) / Real.sqrt (fdeg E))) (3 * frameRadius (s + t + 1) r / 5) with hXdef
  clear_value X
  have hX0 : 0 < X := by linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  unfold Formalism.L2.LamCM.pDeg
  push_cast
  set K : ℝ := 2 * (q : ℝ) + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  set Y := K * Real.log X with hY
  have hY0 : 0 ≤ Y := mul_nonneg hK0 hlX
  have hYle : Y ≤ K * ((4 * fdeg E + 32) * L) := mul_le_mul_of_nonneg_left hXle hK0
  have hlr : Real.log r ≤ L := by
    have hf' : (1 : ℝ) ≤ fdeg E := by exact_mod_cast one_le_fdeg_of_cm E
    have : Real.log (r : ℝ) ≤ Real.log ((fdeg E : ℝ) * r) :=
      Real.log_le_log (by positivity) (le_mul_of_one_le_left (by positivity) hf')
    linarith
  have a4 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr'
  have hst : 0 ≤ s + t := by linarith
  have c1 : s * (Real.log r + Y) ≤ (s + t) * (L + Y) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) hst
  have c2 : (3 / 2 * Y) * (s + t) ≤ (K * (6 * fdeg E + 48) * L) * (s + t) := by
    refine mul_le_mul_of_nonneg_right ?_ hst
    have : K * (6 * (fdeg E : ℝ) + 48) * L = 3 / 2 * (K * ((4 * fdeg E + 32) * L)) := by ring
    rw [this]; linarith
  nlinarith

end GlobalTheory.LamSize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogSupNormLossLeLinearInWeightStatement
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanLogSupNormLoss_le_linear_in_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r q d M : ℕ) (Om s t L : ℝ), 1 ≤ r → 1 ≤ d → 1 ≤ M → 1 ≤ L → 0 ≤ s → 0 ≤ t → Real.log (fdeg E * r) ≤ L → Real.log M ≤ 30 * L → Real.log (dE E) ≤ 4 * fdeg E * L → Real.log d ≤ 4 * L → Real.log (s + t + 1) ≤ 2 * L → lamSup E r q d M Om s t ≤ ((1 + |Om|) / 2 + L + (2 * q + 1) * (6 * fdeg E + 48) * L) * (s + t) := by
  first | exact @GlobalTheory.LamSize.lamSup_le | exact GlobalTheory.LamSize.lamSup_le | (intros; apply GlobalTheory.LamSize.lamSup_le <;> assumption)
end
end

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.LamCore

theorem absA_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) {B : ℝ} (hB : 0 ≤ B) (h : ∀ τ k, |(laOf Dw a n τ k : ℝ)| ≤ B) :
    ((GlobalTheory.LevGeo.absA Dw a : ℕ) : ℝ) ≤ (Module.finrank ℚ E : ℝ) * (((Dw.p + Dw.q : ℕ) : ℝ) * B) := by
  have hn : (0 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have key : ∀ (b : E →+* ℂ) (i : ℕ), i < Dw.mult b → (a (b, i) : ℝ) ≤ B := by
    intro b i hi
    by_cases hb : b (H.rt : E) = H.rt0
    · have hp : i < Dw.p := by simpa [Datum.mult, hb] using hi
      have := h ⟨b, hb⟩ ⟨i, by omega⟩
      simp only [laOf, weightOf, ite_eq_left hp, Int.cast_add, Int.cast_natCast] at this
      linarith [le_abs_self ((a (b, i) : ℝ) + ((n / 2 : ℕ) : ℝ))]
    · have hq : i < Dw.q := by simpa [Datum.mult, hb] using hi
      have := h ⟨conjEmb b, conj_mem hb⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩
      have e1 : ¬ (Dw.p + (Dw.q - 1 - i) < Dw.p) := by omega
      have e2 : Dw.q - 1 - (Dw.p + (Dw.q - 1 - i) - Dw.p) = i := by omega
      simp only [laOf, weightOf, ite_eq_right e1, e2, AllWt.conjEmb_conjEmb, Int.cast_sub, Int.cast_neg, Int.cast_natCast] at this
      linarith [neg_abs_le (-(a (b, i) : ℝ) - ((n / 2 : ℕ) : ℝ))]
  unfold GlobalTheory.LevGeo.absA
  rw [Nat.cast_sum, ← NumberField.Embeddings.card E ℂ, ← nsmul_eq_mul, ← Finset.card_univ]
  refine Finset.sum_le_card_nsmul _ _ _ fun b _ => ?_
  rw [Nat.cast_sum]
  refine (Finset.sum_le_card_nsmul _ _ B fun (i : Fin (Dw.mult b)) _ => key b (i : Fin (Dw.mult b)) i.2).trans ?_
  rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hB
  have : Dw.mult b ≤ Dw.p + Dw.q := by unfold Datum.mult; split_ifs <;> omega
  exact_mod_cast this

theorem collect {f r q L b X x Om w lam sc rd : ℝ} (hf : 8 ≤ f) (hr : 1 ≤ r) (_hq0 : 0 ≤ q) (hq : q ≤ r) (hL : 10 ≤ L)
    (hLx : L ≤ x) (hb : 1 ≤ b) (hZ : f * r * L ≤ X) (hOm : |Om| ≤ 3 * L) (hw0 : 0 ≤ w) (hw : w ≤ 10 * (f * r) * b)
    (h1 : lam ≤ ((1 + |Om|) / 2 + 2 * L + (2 * q + 1) * (6 * f + 48) * (2 * L)) * w)
    (h2 : sc ≤ 250 * f ^ 2 * r ^ 2 * (2 * L)) (h3 : rd ≤ 217 * (f * r * L) ^ 2) :
    2 * lam + 2 * sc + rd ≤ x ^ 4 * X ^ 2 * b := by
  have hfr : 1 ≤ f * r := by nlinarith
  have hZ0 : L ≤ f * r * L := by nlinarith
  have hfrX : f * r ≤ X := by nlinarith
  have hX : 1 ≤ X := hfr.trans hfrX
  have a1 : (2 * q + 1) * (6 * f + 48) ≤ (3 * r) * (12 * f) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have a2 : (2 * q + 1) * (6 * f + 48) * (2 * L) ≤ 72 * (f * r * L) := by nlinarith
  have a3 : (1 + |Om|) / 2 + 2 * L + (2 * q + 1) * (6 * f + 48) * (2 * L) ≤ 76 * X := by linarith
  have a4 : w ≤ 10 * X * b := hw.trans (by gcongr)
  have a5 : lam ≤ 76 * X * (10 * X * b) := h1.trans (mul_le_mul a3 a4 hw0 (by positivity))
  have a6 : (f * r * L) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by linarith) hZ 2
  have a7 : (f * r) * (f * r * L) ≤ X * X := mul_le_mul hfrX hZ (by linarith) (by linarith)
  have a8 : X ^ 2 ≤ X ^ 2 * b := le_mul_of_one_le_right (by positivity) hb
  have a9 : (10 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) (hL.trans hLx) 4
  have a10 : 10 ^ 4 * (X ^ 2 * b) ≤ x ^ 4 * (X ^ 2 * b) := mul_le_mul_of_nonneg_right a9 (by positivity)
  have a11 : 0 ≤ X ^ 2 * b := by positivity
  nlinarith

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem ne_bot_of_form {K K' R W : Type} [Field K] [NumberField K] [Field K'] [AddCommGroup R] [Module K R] [AddCommGroup W]
    [Module K W] [Module K' W] {C C' : Submodule K R} (hC : C' = C) [Module (𝓞 K) C'] {M : Submodule (𝓞 K) C'}
    (hs : Submodule.span K (M : Set C') = ⊤) {WK : Submodule K W} (e : C ≃ₗ[K] WK) {n : ℕ} {b : Fin n → W} (hb : ∀ k, b k ∈ WK)
    (hsp : Submodule.span K' (Set.range b) = ⊤) {y : W} (hy : y ≠ 0) : M ≠ ⊥ := by
  subst hC
  rintro rfl
  rw [Submodule.bot_coe, Submodule.span_zero_singleton] at hs
  have h3 : ∀ k, b k = 0 := fun k => by
    have h1 : e.symm ⟨b k, hb k⟩ ∈ (⊥ : Submodule K C') := by rw [hs]; exact Submodule.mem_top
    rw [Submodule.mem_bot, LinearEquiv.map_eq_zero_iff] at h1
    exact congrArg Subtype.val h1
  have h4 : Submodule.span K' (Set.range b) ≤ ⊥ := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact h3 k)
  exact hy (h4 (by rw [hsp]; exact Submodule.mem_top))


set_option maxHeartbeats 1000000 in
theorem latW_ne_bot (h : GramAt p i) : latW (p.T.U ((i : ℕ) + 1)) (Gk p i) ≠ ⊥ := by
  obtain ⟨-, -, hg, -, -, hs⟩ := h
  obtain ⟨y, -, hy⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hg
  obtain ⟨n, b, hb, -, -, -, hsp⟩ := p.fw.ks i
  exact ne_bot_of_form (cuspW_wtZ _ _) hs (p.fw.e i) hb hsp hy


set_option maxHeartbeats 1000000 in
theorem slopeMax_le (h6 : GlobalTheory.Published.TamagawaSpecialUnitary) {PP A : ℝ} (hR : RecTied D L) (hG : GramAt p i)
    (hN : HostNum D L PP A 1) (hW : WtNum p i PP) :
    slopeMax_sq (nrmK p.fw i) (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) ≤ L.sc.x ^ (2 * A + 4) * L.sc.b := by
  have hj : Formalism.L2.Pj.InR D ((i : ℕ) + 1) := ⟨by omega, i.2⟩
  obtain ⟨hLaws, hnorm⟩ := GlobalTheory.LevGeo.laws_of_coreJ D p.T _ p.fw.laws hj
  have hn : normW (p.T.U ((i : ℕ) + 1)) (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) (GlobalTheory.LevGeo.coreDict p.T.toCore ((i : ℕ) + 1))
      (Gk p i) = nrmK p.fw i := by
    funext σ f; exact hnorm _ σ f
  obtain ⟨_, χ, hχ, hOm, -, -⟩ := GlobalTheory.T.logPeriod_eq_kroneckerCharacter_logPeriod_of_host D L p.T.Q p.fw.laws.pins.1 p.Del p.h0
  have hgood : GoodW (p.T.U ((i : ℕ) + 1)) (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1))
      (GlobalTheory.LevGeo.coreDict p.T.toCore ((i : ℕ) + 1)) (Gk p i) := ⟨by rw [hn]; exact hG.2.2.2.1, hG.2.2.2.2⟩
  have main := GlobalTheory.T.kronecker_character_frame_third h6 D _ _ _ _ _ _ _ _ hLaws χ hχ (wtA (p.κ i)) (p.κ i).n hW.dom hgood (latW_ne_bot p i hG)
  rw [hn] at main
  refine main.trans ?_
  rw [hOm, p.fw.laws.pins.2.1.1, hW.cols]
  obtain ⟨-, hL, hLx, -⟩ := hN.big
  have hfd : fdeg D.host.E = D.R.f := by unfold fdeg; rw [hN.deg]; omega
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hN.f8
  have hr2 : 2 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hnV : (1 : ℝ) ≤ D.R.nV := by exact_mod_cast (by unfold Ranks.nV; omega : 1 ≤ D.R.nV)
  have hbL : L.sc.b = Real.exp L.sc.L := rfl
  have hb : 1 ≤ L.sc.b := by rw [hbL]; exact Real.one_le_exp (by linarith)
  have hx0 : 0 < L.sc.x := by linarith
  have hXb : L.sc.x ^ A ≤ L.sc.b := by simpa using hN.room
  have hP := hN.poly.2.2
  have hfr : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
  have hZ : (D.R.f : ℝ) * D.R.r * L.sc.L ≤ L.sc.x ^ A :=
    le_trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hnV) (by linarith)) hP
  have ht : ((fdeg D.host.E * D.R.r * D.R.nV : ℕ) : ℝ) ≤ L.sc.b := by
    rw [hfd]; push_cast
    exact (le_mul_of_one_le_right (by positivity) (by linarith)).trans (hP.trans hXb)
  have hs : ((GlobalTheory.LevGeo.absA (dat p i) (wtA (p.κ i)) : ℕ) : ℝ) ≤ 8 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
    have := absA_le (dat p i) (wtA (p.κ i)) (p.κ i).n (by positivity) hW.up
    rw [hW.sig.2.2, hN.deg] at this
    push_cast at this
    linarith
  have hs0 : (0 : ℝ) ≤ ((GlobalTheory.LevGeo.absA (dat p i) (wtA (p.κ i)) : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ ((fdeg D.host.E * D.R.r * D.R.nV : ℕ) : ℝ) := Nat.cast_nonneg _
  generalize ((GlobalTheory.LevGeo.absA (dat p i) (wtA (p.κ i)) : ℕ) : ℝ) = s at *
  generalize ((fdeg D.host.E * D.R.r * D.R.nV : ℕ) : ℝ) = t at *
  have hbb : L.sc.b ≤ (D.R.f : ℝ) * D.R.r * L.sc.b := le_mul_of_one_le_left (by linarith) hfr
  have hw : s + t + 1 ≤ 10 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by linarith
  have hlw : Real.log (s + t + 1) ≤ 2 * (2 * L.sc.L) := by
    refine (Real.log_le_log (by linarith) hw).trans ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity), hbL, Real.log_exp]
    linarith [hN.logfr.1, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)]
  have hg : ∀ k, 0 < D.host.g k := fun k => (D.host.g_prime k).pos
  have hM : 1 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_pos (hg 0) (hg 1)
  have hlM : Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ≤ 30 * (2 * L.sc.L) := by
    push_cast
    rw [Real.log_mul (by exact_mod_cast (hg 0).ne') (by exact_mod_cast (hg 1).ne')]
    linarith [hN.logg 0, hN.logg 1]
  have hd : 1 ≤ D.host.d := by rw [← p.fw.laws.pins.1.1]; exact p.T.Q.H.d_prime.pos
  have hl1 : Real.log ((fdeg D.host.E : ℝ) * D.R.r) ≤ 2 * L.sc.L := by rw [hfd]; linarith [hN.logfr.1]
  have hl2 : Real.log (dE D.host.E) ≤ 4 * (fdeg D.host.E : ℝ) * (2 * L.sc.L) := by
    rw [hfd]; unfold dE
    have : 0 ≤ (D.R.f : ℝ) * L.sc.L := by positivity
    linarith [hN.disc]
  have hl3 : Real.log (D.host.d : ℝ) ≤ 4 * (2 * L.sc.L) := by linarith [hN.logd]
  have n1 := (GlobalTheory.T.supremum_constant_log_bound D.host.E D.R.r D.host.d _ (s + t + 1) (2 * L.sc.L) hr2 hd hM (by linarith) (by linarith)
    hl1 hlM hl2 hl3 hlw).2
  have n2 := GlobalTheory.T.meanLogSupNormLoss_le_linear_in_weight D.host.E D.R.r (dat p i).q D.host.d _ (ofRecord D L p.Del p.h0).logOm s t (2 * L.sc.L) (by omega) hd hM
    (by linarith) hs0 ht0 hl1 hlM hl2 hl3 hlw
  have n3 := (log_rd_le_fieldSz _).trans (hR.core_size_le p (by linarith))
  rw [hfd] at n1 n2
  have hq : ((dat p i).q : ℝ) ≤ D.R.r := by exact_mod_cast (by have := hW.sig.2.2; omega : (dat p i).q ≤ D.R.r)
  have e : L.sc.x ^ (2 * A + 4) = L.sc.x ^ 4 * (L.sc.x ^ A) ^ 2 := by
    rw [Real.rpow_add hx0, mul_comm 2 A, Real.rpow_mul hx0.le, mul_comm]
    norm_cast
  rw [e]
  exact collect hf hr (Nat.cast_nonneg _) hq hL hLx hb hZ hW.om (add_nonneg hs0 ht0) (by linarith) n2 n1 n3

theorem lamCore : GlobalTheory.CovTop.Hypotheses2 → Gram → Lifts fun Fm x _ ι p i _ A =>
    slopeMax_sq (nrmK p.fw i) (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) ≤ (Fm.L x ι).sc.x ^ A * (Fm.L x ι).sc.b := by
  intro hP hG
  refine Closed.imp (Closed.and hG (Closed.and (GlobalTheory.CovTop.Sizes.hostN 1) GlobalTheory.T.weight_bound_holds)) ?_
  rintro eps Fm CH - ⟨⟨_, -, h1⟩, ⟨A, hA, h2⟩, ⟨_, -, h3⟩⟩
  obtain ⟨x0, h⟩ := h1.and (h2.and h3)
  refine ⟨2 * A + 4, by linarith, x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨a, b, c⟩ := h x hx hle ι p hp
  exact slopeMax_le p i hP.p6 hp.2 (a i) (b i) (c i)

end GlobalTheory.CovTop.LamCore

end
