module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentsPeterssonOrthogonalAndMasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMul
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPointOfSize
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.MeanTop

namespace GlobalTheory.RefSum.DivWt

section Free

variable {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N) (h : W.Hyp) (hd : W.IsDiv)
include h hd


omit [Fintype ι] in
theorem antitone (τ : ι) : Antitone (W.u1 τ) := fun a b hab => by
  have hab' : (a : ℕ) ≤ b := hab
  have := (W.div_gap_sum h hd τ (b - a) a b (by omega)).1
  linarith

theorem mul_abs_le (τ : ι) (a : Fin N) : (W.T : ℝ) * |(W.u1 τ a : ℝ)| ≤ 2 * W.b := by
  have h1 := (divided_entries ι N W h hd τ a).1
  have h2 : ((W.T : ℝ) + W.Dd + 1) * |(W.u1 τ a : ℝ)| ≤ |(W.u τ a : ℝ)| + W.c0 + 4 * N := by exact_mod_cast h1
  have h3 := h.h5 τ a
  have h4 : 0 ≤ ((W.Dd : ℝ) + 1) * |(W.u1 τ a : ℝ)| := by positivity
  linarith


omit [Fintype ι] in
theorem mul_cloud_le (τ : ι) (a : Fin N) (ha : (a : ℕ) < W.kc) : (W.T : ℝ) * (W.u1 τ a : ℝ) ≤ W.S + 2 * N := by
  have hk := h.kc_lt
  have hp := h.p_lt
  let c : Fin N := ⟨W.kc - 1, by omega⟩
  have hc : (c : ℕ) + 1 = W.kc := by simp only [c]; omega
  obtain ⟨h1, h2⟩ := W.div_gap_sum h hd τ (c - a) a c (by omega)
  have h3 : (((c : ℕ) - a : ℕ) : ℤ) ≤ N := by omega
  rw [(hd τ).1 c hc, sub_zero] at h1 h2
  rw [h.anchor τ c hc] at h2
  have h4 : 0 ≤ ((W.Dd : ℤ) + 1) * W.u1 τ a := by positivity
  have h5 : (W.T : ℤ) * W.u1 τ a ≤ W.u τ a + 2 * N := by linarith
  have h6 : (W.T : ℝ) * (W.u1 τ a : ℝ) ≤ (W.u τ a : ℝ) + 2 * N := by exact_mod_cast h5
  linarith [(h.h3cloud τ a ha).2]

end Free

theorem nCol_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) :
    nCol Dw ≤ Module.finrank ℚ E * (Dw.p + Dw.q) * (2 * (Dw.p + Dw.q) + 8) + 8 := by
  have h1 : ∑ f : Lt1 Dw, 2 * rk f ≤ Fintype.card (Lt1 Dw) * (2 * (Dw.p + Dw.q)) := by
    rw [← Finset.card_univ, ← smul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun f _ => ?_
    have h := rk_le f
    have : Dw.mult f.1 ≤ Dw.p + Dw.q := by rw [Datum.mult]; split_ifs <;> omega
    omega
  have h2 := Nat.mul_le_mul_right (2 * (Dw.p + Dw.q) + 8) (card_Lt1_le_finrank_mul (Dw := Dw))
  rw [mul_add (Fintype.card (Lt1 Dw))] at h2
  unfold nCol
  omega

theorem gap_num {PP T X h g f r : ℝ} (hT : 0 < T) (hX : 60 ≤ X) (hf : 1 ≤ f) (hr : 1 ≤ r) (hP : f * r ^ 2 ≤ PP)
    (h1 : PP * X * T ≤ h) (h2 : h ≤ 2 * T * g) : 2 * f * r * (2 * r + 8) + 8 + 1 ≤ g := by
  have a : PP * X ≤ 2 * g := le_of_mul_le_mul_right (by linarith) hT
  have b1 : 1 ≤ f * r := one_le_mul_of_one_le_of_one_le hf hr
  have b2 : f * r ≤ f * r ^ 2 := by nlinarith
  have c : PP * 60 ≤ PP * X := mul_le_mul_of_nonneg_left hX (by linarith)
  nlinarith

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem wtAt_of_wtNum {PP : ℝ} (h : WtNum p i PP) (hP : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ PP) (hi : (i : ℕ) + 1 < D.R.m)
    (u1 : GlobalTheory.AllWt.Weight (dat p i)) (hq : Quo p i PP u1) : WtAt p i PP 802 u1 := by
  obtain ⟨h0, S, eta, hS, he, hSe, -, hh0, hH⟩ := h.hyp hi
  have H := hH u1
  have hd := (quo_iff p i PP h0 S eta u1).1 hq
  obtain ⟨hp, hq', hr⟩ := h.sig
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hrr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hf : 2 ≤ D.R.f := D.R.two_le_m.trans D.R.m_le_f
  simp only [Ranks.sigW] at hp hq'
  have hT1 : 4 * GlobalTheory.CompHt.dimFlag (dat p i) + 4 ≤ lenT p i PP := H.h1
  have hD : 1 ≤ GlobalTheory.CompHt.dimFlag (dat p i) := by
    rw [h.dim]; exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  obtain ⟨τ0⟩ : Nonempty (Psi p.T.Q.H) := (Nat.card_pos_iff.1 (by rw [h.card]; omega)).1
  have han : (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ0 : ℝ) ≤ 4 * L.sc.b := by
    unfold anchor
    rw [dite_eq_left (by omega)]
    exact (le_abs_self _).trans (h.up τ0 _)
  have hlow := h.low τ0
  have hw : 4 * ((eta + S + (((dat p i).p + (dat p i).q : ℕ) : ℝ)) + S + ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) +
      2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ)) + 20 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (lenT p i PP : ℝ) ≤
      (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ0 : ℝ) := H.h3w τ0
  have hc0 : (0 : ℝ) ≤ ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) := by exact_mod_cast (cZero_spec D _).2.1
  have hrows := h.what₂.1
  have e1 : ∀ τ a, (lenT p i PP : ℝ) * |(u1 τ a : ℝ)| ≤ 2 * (4 * L.sc.b) := mul_abs_le _ H hd
  have e2 : ∀ τ (a : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) < D.R.k - 1 →
      (lenT p i PP : ℝ) * (u1 τ a : ℝ) ≤ S + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) := mul_cloud_le _ H hd
  have e3 : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (b : ℕ) = (dat p i).p →
      h0 ≤ 2 * (lenT p i PP : ℤ) * (u1 τ a - u1 τ b) := fun τ a b hab hb =>
    ((divided_gaps _ _ _ H hd τ a b hab).2.1 hb).1
  have e4 : ∀ τ, Antitone (u1 τ) := antitone _ H hd
  have e5 : ∀ τ (a : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = D.R.k - 1 → u1 τ a = 0 := fun τ => (hd τ).1
  have hn := nCol_le (dat p i)
  rw [GlobalTheory.PinNum.finrank_host D, hr] at hn
  rw [hr] at hw
  simp only [hr] at e2
  unfold WtAt
  clear H hd hH hq h
  have hT : (1 : ℝ) ≤ lenT p i PP := by exact_mod_cast (by omega : 1 ≤ lenT p i PP)
  have hT' : 1 ≤ lenT p i PP := by omega
  generalize lenT p i PP = T at *
  generalize (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ0 : ℝ) = w at *
  generalize ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) = c at *
  have hf' : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hr' : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.k ≤ D.R.r)
  have hD' : (1 : ℝ) ≤ GlobalTheory.CompHt.dimFlag (dat p i) := by exact_mod_cast hD
  have hkP : (D.R.k : ℝ) ≤ PP := by nlinarith
  have hTb : (T : ℝ) ≤ 4 * L.sc.b := by nlinarith
  have hb : 0 ≤ L.sc.b := by linarith
  refine ⟨⟨by omega, by omega, by omega, by omega, by omega, GlobalTheory.PinNum.finrank_host D⟩, by omega,
    ⌊8 * L.sc.b / T⌋₊, D.R.k * (S + 2 * D.R.r) / T, ⟨e4, fun τ a ha => e5 τ a (by omega), fun τ a b ha hb' => ?_,
      fun τ a => ?_, fun τ => ?_⟩, ?_, ?_, hT'⟩
  · have g1 : (h0 : ℝ) ≤ 2 * (T : ℝ) * ((u1 τ a - u1 τ b : ℤ) : ℝ) := by exact_mod_cast e3 τ a b (by omega) hb'
    have hX : (60 : ℝ) ≤ D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * GlobalTheory.CompHt.dimFlag (dat p i) := by
      calc (60 : ℝ) ≤ 5 * 2 ^ 2 * 2 ^ 2 * 5 * 1 := by norm_num
        _ ≤ _ := by gcongr; linarith
    have g2 := gap_num (by linarith) hX (by linarith) (by linarith) hP (le_of_eq_of_le (by ring) hh0) g1
    have g3 : ((nCol (dat p i) : ℕ) : ℝ) ≤ 2 * D.R.f * D.R.r * (2 * D.R.r + 8) + 8 := by exact_mod_cast hn
    have g4 : ((nCol (dat p i) : ℕ) : ℝ) + 1 ≤ ((u1 τ a - u1 τ b : ℤ) : ℝ) := by linarith
    exact_mod_cast g4
  · have g1 : ((|u1 τ a|.toNat : ℕ) : ℝ) = |(u1 τ a : ℝ)| := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (abs_nonneg _), Int.cast_abs]
    have g2 : |u1 τ a|.toNat ≤ ⌊8 * L.sc.b / T⌋₊ := by
      refine Nat.le_floor ?_
      rw [g1, le_div_iff₀ (by linarith)]
      linarith [e1 τ a]
    exact Int.toNat_le.1 g2
  · rw [le_div_iff₀ (by linarith), Finset.sum_mul]
    refine (Finset.sum_le_card_nsmul _ _ (S + 2 * D.R.r) fun a ha => ?_).trans ?_
    · have := (Finset.mem_filter.1 ha).2
      linarith [e2 τ a (by omega)]
    · rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have : (Finset.univ.filter (fun a : Fin ((dat p i).p + (dat p i).q) => (a : ℕ) + 2 < D.R.k)).card ≤
          (Finset.range D.R.k).card :=
        Finset.card_le_card_of_injOn (fun a => (a : ℕ))
          (fun a ha => by have := (Finset.mem_filter.1 ha).2; simp only [Finset.coe_range, Set.mem_Iio]; omega)
          (fun a _ b _ e => Fin.ext e)
      rw [Finset.card_range] at this
      exact_mod_cast this
  · have g1 : ((⌊8 * L.sc.b / T⌋₊ : ℕ) : ℝ) ≤ 8 * L.sc.b / T := Nat.floor_le (by positivity)
    rw [le_div_iff₀ (by linarith)] at g1
    linarith
  · rw [mul_div_cancel₀ _ (by linarith)]
    have g1 : (D.R.k : ℝ) * S ≤ PP * (S + eta) := mul_le_mul hkP (by linarith) hS (by linarith)
    have g2 : (D.R.r : ℝ) * D.R.k ≤ L.sc.b := by
      refine le_trans ?_ hrows
      calc (D.R.r : ℝ) * D.R.k = 1 ^ 2 * D.R.r * 1 * D.R.k * 1 ^ 3 := by ring
        _ ≤ _ := by gcongr <;> linarith
    linarith

theorem le_PP {P : ParameterChoice' D L} (T : ParamsT D L P) : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ T.PP := by
  have h1 : D.R.f * D.R.r ^ 2 ≤ T.nWn := le_trans (by nlinarith [Nat.zero_le (D.R.f * D.R.r)]) T.nW_lo.1
  exact le_trans (by exact_mod_cast h1) T.nW_le

end GlobalTheory.RefSum.DivWt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchorBoundStatement
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.AnchorRd

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem anchor_eq (P : ParameterChoice' D L) (t : D.what₂.Tau) (τ : Psi p.T.Q.H) (hτ : τ.1 = DV.tauEmb D t) :
    (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) =
      ⌊Formalism.L2.NTheta.lamAt (D.hc t) (D.R.k - 2) + (D.hc t).e i -
        (((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - ((D.R.k - 2 : ℕ) + 1)) - ((D.R.t : ℚ) + 1) / 2⌋ +
        (((p.κ i).n / 2 : ℕ) : ℤ) := by
  have hk := D.R.m_add_three_le_k
  have hmain := GlobalTheory.CovTop.WtRead.main D p.T p.fw.laws i (p.κ i)
  have hsw : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) := by simp only [Ranks.sigW]; omega
  have hpq : (dat p i).p = (D.R.sigW ((i : ℕ) + 1)).1 := hmain.1
  have hlt : D.R.k - 1 - 1 < (dat p i).p + (dat p i).q := by omega
  have hj : D.R.k - 2 < (D.R.sigW ((i : ℕ) + 1)).1 := by omega
  obtain ⟨-, hnn⟩ := GlobalTheory.RecGaps.bigEnt p P i t (D.R.k - 2) hj
  unfold anchor
  rw [dite_eq_left hlt, GlobalTheory.CovTop.WtRead.laOf_big D p.T p.fw.laws i (p.κ i) t τ hτ _ ⟨D.R.k - 2, hj⟩ (by simp; omega),
    (p.fw.kap i t).1 ⟨D.R.k - 2, hj⟩]
  rw [GlobalTheory.RecGaps.sig_Wc]
  unfold aPl
  rw [if_pos hj, Int.toNat_of_nonneg hnn]

theorem abs_anchor_sub_le (P : ParameterChoice' D L) (t : D.what₂.Tau) (τ : Psi p.T.Q.H) (hτ : τ.1 = DV.tauEmb D t) :
    |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ) - (((D.hc t).e i : ℚ) : ℝ)| ≤
      L.Sc + D.R.nV + D.R.m + D.R.t + 2 := by
  have hk := D.R.m_add_three_le_k
  have ha := anchor_eq p i P t τ hτ
  have hn : (p.κ i).n = D.R.nV := (p.fw.kap i t).2.2
  have hv : Formalism.L2.NTheta.lamAt (D.hc t) (D.R.k - 2) = (D.hc t).v ⟨D.R.k - 2, by omega⟩ := by
    unfold Formalism.L2.NTheta.lamAt; rw [dite_eq_left (by omega)]
  have hc := L.cloud_v t ⟨D.R.k - 2, by omega⟩
  have hsw : ((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - ((D.R.k - 2 : ℕ) + 1) = (i : ℚ) + 1 := by
    rw [show (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) by simp only [Ranks.sigW]; omega,
      Nat.cast_sub (by omega : 2 ≤ D.R.k)]
    push_cast; ring
  rw [hsw, hv] at ha
  rw [ha, hn]
  have h1 := Int.floor_le ((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2)
  have h2 := Int.lt_floor_add_one ((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2)
  have h1' : ((⌊(D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2⌋ : ℤ) : ℝ) ≤
      (((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2 : ℚ) : ℝ) := by
    exact_mod_cast h1
  have h2' : (((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2 : ℚ) : ℝ) <
      ((⌊(D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2⌋ : ℤ) : ℝ) + 1 := by
    exact_mod_cast h2
  have hnv : ((D.R.nV / 2 : ℕ) : ℝ) ≤ D.R.nV := by exact_mod_cast Nat.div_le_self _ _
  have hnv0 : (0 : ℝ) ≤ ((D.R.nV / 2 : ℕ) : ℝ) := by positivity
  have hi : ((i : ℕ) : ℝ) + 1 ≤ D.R.m := by exact_mod_cast i.2
  have ht : (0 : ℝ) ≤ D.R.t := by positivity
  rw [Int.cast_add, Int.cast_natCast]
  push_cast at h1' h2'
  rw [abs_le]
  constructor <;> linarith [hc.1, hc.2]


set_option maxHeartbeats 1000000 in
theorem anchorAt_of {PP A : ℝ} (P : ParameterChoice' D L) (hw : WtNum p i PP) (hh : HostNum D L PP A 1) : AnchorAt p i 100 := by
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  obtain ⟨hp, hq, hcard, -, -, E, hE, -⟩ := GlobalTheory.CovTop.WtRead.main D p.T p.fw.laws i (p.κ i)
  have hL10 := hh.big.2.1
  have hLx := hh.big.2.2.1
  have hll := hh.big.2.2.2
  have hxA : 1 ≤ L.sc.x ^ A := Real.one_le_rpow (by linarith) (by linarith [hh.poly.1])
  have hb : L.sc.x ^ A ≤ L.sc.b := by simpa using hh.room
  have hb1 : 1 ≤ L.sc.b := hxA.trans hb
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hh.f8
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hunit := hw.unit
  have hom := hw.om
  have hanc : ∀ τ, |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ)| ≤ 4 * L.sc.b := by
    intro τ
    unfold anchor
    split_ifs with h
    · exact hw.up τ _
    · simp only [Int.cast_zero, abs_zero]; linarith

  have hpr : ((dat p i).p : ℝ) + (dat p i).q = D.R.r := by
    rw [hp, hq]; exact_mod_cast GlobalTheory.CovTop.WtRead.sigW_add D i
  have hp0 : (0 : ℝ) ≤ (dat p i).p := by positivity
  have hq0 : (0 : ℝ) ≤ (dat p i).q := by positivity
  have hcr : |((dat p i).p : ℝ) - (dat p i).q| ≤ D.R.r := abs_le.2 ⟨by linarith, by linarith⟩
  have hqm : ((dat p i).q : ℝ) ≤ D.R.m := by
    rw [hq]; exact_mod_cast (by simp only [Ranks.sigW]; omega : (D.R.sigW ((i : ℕ) + 1)).2 ≤ D.R.m)
  have hc_eq : ((D.R.k : ℝ) + (((i : ℕ) + 1 : ℕ) : ℝ) - 1) - ((D.R.m : ℝ) - (((i : ℕ) + 1 : ℕ) : ℝ)) =
      ((dat p i).p : ℝ) - (dat p i).q := by
    rw [hp, hq]
    simp only [Ranks.sigW]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring

  have hmainS : mainT p i = ∑ t : D.what₂.Tau, (((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) *
      (ofRecord D L p.Del p.h0).logOm := by
    show ∑ ρ : RPl D.R, (((D.R.k : ℝ) + (((i : ℕ) + 1 : ℕ) : ℝ) - 1) - ((D.R.m : ℝ) - (((i : ℕ) + 1 : ℕ) : ℝ))) *
      (ofRecord D L p.Del p.h0).w ((i : ℕ) + 1) ρ * (ofRecord D L p.Del p.h0).logOm = _
    rw [hc_eq, ← (tauPl_bijective D).sum_comp (fun t => (((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) *
      (ofRecord D L p.Del p.h0).logOm)]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    congr 2
    simp only [NumDatum.w, NumDatum.eQ]
    rw [dite_eq_left ⟨by omega, by omega⟩]
    congr 3
  have hancS : ∑ τ : Psi p.T.Q.H, (((dat p i).p : ℝ) - (dat p i).q) *
      ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm =
      ∑ t : D.what₂.Tau, (((dat p i).p : ℝ) - (dat p i).q) *
        ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm :=
    (Equiv.sum_comp E (fun τ => (((dat p i).p : ℝ) - (dat p i).q) *
      ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm)).symm
  have hcardT : (Fintype.card D.what₂.Tau : ℝ) = D.R.f := by exact_mod_cast Formalism.MainNotions.Lnk.card_Tau D

  have hne : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by rw [Formalism.MainNotions.Lnk.card_Tau]; have := hh.f8; omega)
  obtain ⟨t0⟩ := hne
  have hw'' : L.sc.w'' D.R.n ≤ 8 * L.sc.b := by
    have a1 := hw.low (E t0)
    have a2 := (abs_le.1 (hanc (E t0))).2
    linarith
  have hr2k : (D.R.r : ℝ) ≤ 2 * D.R.k := by exact_mod_cast (by unfold Ranks.r; omega : D.R.r ≤ 2 * D.R.k)
  have hSc0 : 0 ≤ L.Sc := L.Sc_pos.le
  have hrS : (D.R.r : ℝ) * L.Sc ≤ 16 * L.sc.b := by
    have a1 := P.kS_le
    have a2 : (D.R.r : ℝ) * L.Sc ≤ 2 * D.R.k * L.Sc := mul_le_mul_of_nonneg_right hr2k hSc0
    linarith
  have hnV : (D.R.nV : ℝ) = D.R.r + D.R.t := by unfold Ranks.nV; push_cast; ring
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : D.R.m ≤ D.R.r)
  have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
  have hrnV : (D.R.r : ℝ) * D.R.nV ≤ L.sc.b := by
    have a1 := hh.poly.2.2
    have e0 : (0 : ℝ) ≤ (D.R.r : ℝ) * D.R.nV := by positivity
    have a2 : (D.R.r : ℝ) * D.R.nV * 1 ≤ (D.R.r : ℝ) * D.R.nV * (D.R.f * L.sc.L) :=
      mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) e0
    calc (D.R.r : ℝ) * D.R.nV = (D.R.r : ℝ) * D.R.nV * 1 := by ring
      _ ≤ (D.R.r : ℝ) * D.R.nV * (D.R.f * L.sc.L) := a2
      _ = D.R.f * D.R.r * D.R.nV * L.sc.L := by ring
      _ ≤ L.sc.x ^ A := a1
      _ ≤ L.sc.b := hb
  have hB : (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) ≤ 20 * L.sc.b := by
    have e1 : (D.R.r : ℝ) * (D.R.nV + D.R.m + D.R.t + 2) ≤ 4 * ((D.R.r : ℝ) * D.R.nV) := by
      calc (D.R.r : ℝ) * (D.R.nV + D.R.m + D.R.t + 2) ≤ (D.R.r : ℝ) * (4 * D.R.nV) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 4 * ((D.R.r : ℝ) * D.R.nV) := by ring
    calc (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) =
          (D.R.r : ℝ) * L.Sc + (D.R.r : ℝ) * (D.R.nV + D.R.m + D.R.t + 2) := by ring
      _ ≤ 16 * L.sc.b + 4 * L.sc.b := add_le_add hrS (by linarith)
      _ = 20 * L.sc.b := by ring
  refine ⟨?_, ?_, hh.poly.2.2.trans hb⟩
  · rw [hmainS, hancS, ← Finset.sum_sub_distrib]
    have hterm : ∀ t : D.what₂.Tau, |(((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) *
        (ofRecord D L p.Del p.h0).logOm - (((dat p i).p : ℝ) - (dat p i).q) *
        ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm| ≤
        (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) * (3 * L.sc.L) := by
      intro t
      have a1 := abs_anchor_sub_le p i P t (E t) (hE t)
      rw [show (((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) * (ofRecord D L p.Del p.h0).logOm -
          (((dat p i).p : ℝ) - (dat p i).q) * ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) *
          (ofRecord D L p.Del p.h0).logOm = -((((dat p i).p : ℝ) - (dat p i).q) *
          (((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) - (((D.hc t).e i : ℚ) : ℝ)) *
          (ofRecord D L p.Del p.h0).logOm) by ring, abs_neg, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hcr a1 (abs_nonneg _) (by positivity)) hom (abs_nonneg _) (by positivity)
    calc _ ≤ ∑ t : D.what₂.Tau, (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) * (3 * L.sc.L) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => hterm t)
      _ = D.R.f * ((D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2)) * (3 * L.sc.L) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardT]; ring
      _ ≤ D.R.f * (20 * L.sc.b) * (3 * L.sc.L) := by gcongr
      _ ≤ 100 * unitE p := by
          rw [hunit]
          have e1 : (0 : ℝ) ≤ D.R.f * L.sc.b * L.sc.L := by positivity
          have e2 : D.R.f * L.sc.b * L.sc.L * 1 ≤ D.R.f * L.sc.b * L.sc.L * (D.R.m * Real.log (Real.log L.sc.x)) :=
            mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le (by linarith) hll) e1
          have e3 : (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) =
              D.R.f * L.sc.b * L.sc.L * (D.R.m * Real.log (Real.log L.sc.x)) := by ring
          have e4 : (D.R.f : ℝ) * (20 * L.sc.b) * (3 * L.sc.L) = 60 * (D.R.f * L.sc.b * L.sc.L * 1) := by ring
          rw [e3, e4]
          linarith
  · have hsum : ∑ τ : Psi p.T.Q.H, |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ)| ≤
        D.R.f * (4 * L.sc.b) := by
      calc _ ≤ ∑ τ : Psi p.T.Q.H, 4 * L.sc.b := Finset.sum_le_sum fun τ _ => hanc τ
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, nsmul_eq_mul]
    calc (∑ τ : Psi p.T.Q.H, |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ)|) *
          ((dat p i).q : ℝ) * L.sc.L ≤ D.R.f * (4 * L.sc.b) * D.R.m * L.sc.L := by gcongr
      _ ≤ 100 * unitE p := by
          rw [hunit]
          have e1 : (0 : ℝ) ≤ D.R.f * L.sc.b * D.R.m * L.sc.L := by positivity
          have e2 : D.R.f * L.sc.b * D.R.m * L.sc.L * 1 ≤ D.R.f * L.sc.b * D.R.m * L.sc.L * Real.log (Real.log L.sc.x) :=
            mul_le_mul_of_nonneg_left hll e1
          have e3 : (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) =
              D.R.f * L.sc.b * D.R.m * L.sc.L * Real.log (Real.log L.sc.x) := by ring
          have e4 : (D.R.f : ℝ) * (4 * L.sc.b) * D.R.m * L.sc.L = 4 * (D.R.f * L.sc.b * D.R.m * L.sc.L * 1) := by ring
          rw [e3, e4]
          linarith

end GlobalTheory.CovTop.AnchorRd

namespace GlobalTheory.CovTop

end GlobalTheory.CovTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogRatioUpperBound
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.MeasUp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem le_exp_of_log_le {y L : ℝ} (hy : 0 ≤ y) (h : Real.log y ≤ L) : y ≤ Real.exp L := by
  rcases hy.eq_or_lt with h0 | h0
  · rw [← h0]; exact (Real.exp_pos L).le
  · exact (Real.log_le_iff_le_exp h0).1 h

theorem kapQ_inl (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) {p q : ℕ} (hp : p = D.R.k + i)
    (hq : q = D.R.m - ((i : ℕ) + 1)) (a : Fin p) :
    Formalism.L2.NTheta.kapQ (D.hc t) p q (Sum.inl a) + (D.hc t).e i = GlobalTheory.CovTop.WtShape.ent D i t a := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have ha := a.2
  have e0 : Formalism.L2.NTheta.lamAt (D.hc t) a = DV.sigPar D t a := rfl
  unfold Formalism.L2.NTheta.kapQ GlobalTheory.CovTop.WtShape.ent
  simp only [Sum.elim_inl]
  rw [if_pos (by omega), e0]
  subst hp hq
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  rw [hr, Nat.cast_sub (by omega : 1 ≤ D.R.k + D.R.m), Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ D.R.m)]
  push_cast
  ring

theorem kapQ_inr (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) {p q : ℕ} (hp : p = D.R.k + i)
    (hq : q = D.R.m - ((i : ℕ) + 1)) (c : Fin q) :
    Formalism.L2.NTheta.kapQ (D.hc t) p q (Sum.inr c) + (D.hc t).e i = GlobalTheory.CovTop.WtShape.ent D i t (p + c) := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have hc := c.2
  have e0 : Formalism.L2.NTheta.lamAt (D.hc t) (p + c) = DV.sigPar D t (p + c) := rfl
  unfold Formalism.L2.NTheta.kapQ GlobalTheory.CovTop.WtShape.ent
  simp only [Sum.elim_inr]
  rw [if_neg (by omega), e0]
  subst hp hq
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  rw [hr, Nat.cast_sub (by omega : 1 ≤ D.R.k + D.R.m), Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ D.R.m)]
  push_cast
  ring

theorem abs_wt_le (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) {p q : ℕ} (hp : p = D.R.k + i)
    (hq : q = D.R.m - ((i : ℕ) + 1)) {B : ℝ}
    (hB : ∀ n, n < D.R.r → |((GlobalTheory.CovTop.WtShape.ent D i t n : ℚ) : ℝ)| ≤ B) (a : Fin p ⊕ Fin q) :
    |((Formalism.L2.NTheta.kapW (D.hc t) p q a : ℤ) : ℝ) + (((D.hc t).e i : ℚ) : ℝ)| ≤ B + 1 := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  obtain ⟨n, hn, hx⟩ : ∃ n, n < D.R.r ∧
      Formalism.L2.NTheta.kapQ (D.hc t) p q a + (D.hc t).e i = GlobalTheory.CovTop.WtShape.ent D i t n := by
    cases a with
    | inl a => exact ⟨a, by have := a.2; omega, kapQ_inl D i t hp hq a⟩
    | inr c => exact ⟨p + c, by have := c.2; omega, kapQ_inr D i t hp hq c⟩
  have h1 : ((Formalism.L2.NTheta.kapW (D.hc t) p q a : ℤ) : ℝ) ≤ (Formalism.L2.NTheta.kapQ (D.hc t) p q a : ℝ) := by
    unfold Formalism.L2.NTheta.kapW
    exact_mod_cast Int.floor_le _
  have h2 : (Formalism.L2.NTheta.kapQ (D.hc t) p q a : ℝ) < ((Formalism.L2.NTheta.kapW (D.hc t) p q a : ℤ) : ℝ) + 1 := by
    have h := Int.lt_floor_add_one (Formalism.L2.NTheta.kapQ (D.hc t) p q a)
    have h' : ((Formalism.L2.NTheta.kapQ (D.hc t) p q a : ℚ) : ℝ) <
        (((⌊Formalism.L2.NTheta.kapQ (D.hc t) p q a⌋ : ℤ) : ℚ) : ℝ) + 1 := by
      have := (Rat.cast_lt (K := ℝ)).2 h
      rw [Rat.cast_add, Rat.cast_one] at this
      exact this
    rw [Rat.cast_intCast] at h'
    exact h'
  have h3 : (Formalism.L2.NTheta.kapQ (D.hc t) p q a : ℝ) + (((D.hc t).e i : ℚ) : ℝ) =
      ((GlobalTheory.CovTop.WtShape.ent D i t n : ℚ) : ℝ) := by
    rw [← hx]; push_cast; ring
  obtain ⟨b1, b2⟩ := abs_le.1 (hB n hn)
  rw [abs_le]
  constructor <;> linarith

theorem wtSize_le (D : D7) (i : Fin D.R.m) {B : ℝ}
    (hB : ∀ t n, n < D.R.r → |((GlobalTheory.CovTop.WtShape.ent D i t n : ℚ) : ℝ)| ≤ B) :
    GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i ≤ D.R.f * D.R.r * (B + 1) := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize
  calc _ ≤ ∑ _τ : D.what₂.Tau, (D.R.r : ℝ) * (B + 1) := Finset.sum_le_sum fun τ _ => ?_
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]; ring
  have hs : (Wc D i).sig (TH.tauE D τ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have s1 : ((Wc D i).sig (TH.tauE D τ)).1 = D.R.k + i := by rw [hs]; rfl
  have s2 : ((Wc D i).sig (TH.tauE D τ)).2 = D.R.m - ((i : ℕ) + 1) := by rw [hs]; rfl
  calc _ ≤ ∑ _a : Fin ((Wc D i).sig (TH.tauE D τ)).1 ⊕ Fin ((Wc D i).sig (TH.tauE D τ)).2, (B + 1) :=
        Finset.sum_le_sum fun a _ => abs_wt_le D i τ s1 s2 (hB τ) a
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, s1, s2]
      congr 1
      rw [hr]; push_cast [show (i : ℕ) + 1 ≤ D.R.m by omega, show 1 ≤ D.R.k + D.R.m by omega]; ring

end GlobalTheory.CovTop.MeasUp

namespace GlobalTheory.CovTop.MeasUp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem abs_ent_le {PP : ℝ} (hW : WtNum p i PP) (t : D.what₂.Tau) (n : ℕ) (hn : n < D.R.r) :
    |((GlobalTheory.CovTop.WtShape.ent D i t n : ℚ) : ℝ)| ≤ 4 * L.sc.b := by
  have hp := p.fw.laws.pins.1
  let τ : Psi p.T.Q.H := ⟨DV.tauEmb D t, hp.2.2.2 t⟩
  let k : Fin ((dat p i).p + (dat p i).q) := ⟨n, by rw [GlobalTheory.CovTop.WtShape.dat_rank p i]; exact hn⟩
  have e := GlobalTheory.CovTop.WtShape.laOf_read p i τ t rfl k
  have h := hW.up τ k
  rw [← e, Rat.cast_intCast]
  exact h

theorem sizes_two {PP A PP' : ℝ} (P : ParameterChoice' D L) (hH : HostNum D L PP A 2) (hW : ∀ j, WtNum p j PP') :
    GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D (2 * L.sc.L) := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hrR : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hnV : (0 : ℝ) ≤ D.R.nV := Nat.cast_nonneg _
  obtain ⟨hL10, -⟩ := hH.big.2
  obtain ⟨hlfr, hlnV⟩ := hH.logfr
  set Lc := L.sc.L with hLc
  have hb : L.sc.b = Real.exp Lc := rfl
  have hfr : (D.R.f : ℝ) * D.R.r ≤ Real.exp Lc := le_exp_of_log_le (by positivity) hlfr
  have hnVe : (D.R.nV : ℝ) ≤ Real.exp Lc := le_exp_of_log_le hnV hlnV
  have hE0 : 0 < Real.exp Lc := Real.exp_pos _
  have hE1 : Lc + 1 ≤ Real.exp Lc := Real.add_one_le_exp _
  have e2 : Real.exp (2 * Lc) = Real.exp Lc * Real.exp Lc := by rw [two_mul, Real.exp_add]
  refine ⟨?_, fun j => ?_, ?_, ?_⟩
  · rw [e2]
    exact mul_le_mul hfr hnVe hnV hE0.le
  · have hw := wtSize_le D j (abs_ent_le p j (hW j))
    rw [e2, ← hb]
    rw [← hb] at hE1 hfr
    have h1 : (D.R.f : ℝ) * D.R.r * (4 * L.sc.b + 1) ≤ L.sc.b * (5 * L.sc.b) :=
      mul_le_mul hfr (by linarith) (by linarith) (by linarith)
    have h5 : 5 ≤ L.sc.b * L.sc.b := by nlinarith
    have h6 : L.sc.b * (5 * L.sc.b) ≤ (L.sc.b * L.sc.b) ^ 2 := by nlinarith
    linarith
  · have g0 : (0 : ℝ) < (D.host.g 0 : ℝ) := by exact_mod_cast (D.host.g_prime 0).pos
    have g1 : (0 : ℝ) < (D.host.g 1 : ℝ) := by exact_mod_cast (D.host.g_prime 1).pos
    rw [Real.log_mul g0.ne' g1.ne']
    linarith [hH.logg 0, hH.logg 1]
  · have h1 := Formalism.BasicNotions.log_rdE_le_scL P
    have h2 : |dlogL D 1| ≤ Lc := by
      rw [← L.logDerivative_at_one_eq]; exact P.logDerivative_le_power
    linarith

theorem ratAt_pos_le (hOM : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D) {PP A PP' : ℝ} (P : ParameterChoice' D L)
    (hH : HostNum D L PP A 2) (hW : ∀ j, WtNum p j PP') :
    0 < ratAt p i ∧ Real.log (ratAt p i) ≤ 244 * unitE p := by
  obtain ⟨-, hd, h2⟩ := hOM D _ p.R.toLevCh _ p.charW.base.lev i p.R.triv
  obtain ⟨h0, ht, -, hb⟩ := h2 _ _ (p.charW.base.models.νW i)
  have hr : 0 < ratAt p i :=
    mul_pos (ENNReal.toReal_pos h0 ht) (Finset.prod_pos fun τ _ => zero_lt_one.trans_le (hd τ))
  refine ⟨hr, ?_⟩
  have hB := (hb _ (sizes_two p P hH hW)).2.2
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hrR : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hnV1 : (1 : ℝ) ≤ D.R.nV := by
    have : 1 ≤ D.R.nV := by unfold Ranks.nV; omega
    exact_mod_cast this
  obtain ⟨-, hL10, -, hll⟩ := hH.big
  obtain ⟨-, -, hpoly⟩ := hH.poly
  have hroom := hH.room
  rw [Real.rpow_two] at hroom

  have hr_le : (D.R.r : ℝ) ≤ L.sc.x ^ A := by
    refine le_trans ?_ hpoly
    have a1 : (D.R.r : ℝ) ≤ (D.R.f : ℝ) * D.R.r := le_mul_of_one_le_left (by linarith) (by linarith)
    have a2 : (D.R.f : ℝ) * D.R.r ≤ (D.R.f : ℝ) * D.R.r * D.R.nV := le_mul_of_one_le_right (by positivity) hnV1
    have a3 : (D.R.f : ℝ) * D.R.r * D.R.nV ≤ (D.R.f : ℝ) * D.R.r * D.R.nV * L.sc.L :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    linarith
  have hr2 : (D.R.r : ℝ) ^ 2 ≤ L.sc.b := (pow_le_pow_left₀ (by linarith) hr_le 2).trans hroom
  have hu : unitE p = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := (hW i).unit
  rw [hu]
  have hL0 : 0 ≤ L.sc.L := by linarith
  have hfL : 0 ≤ (D.R.f : ℝ) * L.sc.L := by positivity
  have c1 : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L := by
    have := mul_le_mul_of_nonneg_left hr2 hfL
    nlinarith
  have hb1 : 0 ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L := by
    have : 0 < L.sc.b := Real.exp_pos _
    positivity
  have c2 : (D.R.f : ℝ) * L.sc.b * L.sc.L ≤ (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := by
    have h1 : (1 : ℝ) ≤ D.R.m * Real.log (Real.log L.sc.x) := by nlinarith
    have := mul_le_mul_of_nonneg_left h1 hb1
    nlinarith
  have e3 : (122 : ℝ) * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (2 * L.sc.L)) = 244 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L) := by
    ring
  have e4 : ratAt p i = GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i (p.R.νW i) (p.R.fdW i) := rfl
  rw [e4]
  linarith

end GlobalTheory.CovTop.MeasUp

namespace GlobalTheory.CovTop.MeasRd

end GlobalTheory.CovTop.MeasRd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTraitCharacterGroupFinrankLeGenusThree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTraitCharacterGroupFinrankLeGenusThree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem Trait.finrank_le : ∀ (g n : ℕ), 2 ≤ n → ∀ (F : SFam g n (zetaAway n)) (T : Trait F),
    Module.finrank ℤ T.D.toPre.X ≤ g := by
  intro g n hn F T
  have hn0 : n ≠ 0 := by omega
  have hζ : IsUnit (zetaAway n) := by rw [← cycBase_ζ hn0]; exact Units.isUnit _
  have hd : SmoothOfRelativeDimension g F.univ.A.hom :=
    GlobalTheory.SiegSharpCover.smoothDim F.univ hn hζ (isUnit_natCast hn0)
  have hA : SmoothOfRelativeDimension g T.A.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback T.cart.1 hd
  have e : T.A.g = g :=
    H1.dim_unique _ T.A.smoothDim hA ((η[T.A.A]).left (IsLocalRing.closedPoint _))
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have h := GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U
  omega

theorem Trait.finrank_le_of_three_le : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)), 3 ≤ n → ∀ T : Trait F,
    Module.finrank ℤ T.D.toPre.X ≤ g :=
  fun g n F hn T => Trait.finrank_le g n (by omega) F T

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTraitCharacterGroupFinrankLeGenusThreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelTrait_characterGroup_finrank_le_genus_of_three_le : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)), 3 ≤ n → ∀ T : Trait F, Module.finrank ℤ T.D.toPre.X ≤ g := by
  first | exact @GlobalTheory.Poinc.Trait.finrank_le_of_three_le | exact GlobalTheory.Poinc.Trait.finrank_le_of_three_le | (intros; apply GlobalTheory.Poinc.Trait.finrank_le_of_three_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusPullbackAndVanishIntoLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusPullbackAndVanishIntoLocus
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocusPull

theorem exists_gen_of_nonzeroLocus_eq_top {Y : Scheme.{0}} {M : LB Y} (s : M.Sec) (h : ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤) :
    ∃ t : LB.Gen M, t.IsGen := by
  have hu : ∀ j, IsUnit (s.f j) := fun j =>
    Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      have hy' : y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s := h ▸ trivial
      exact (Y.mem_basicOpen _ y hy).1 ((GlobalTheory.mem_nonzeroLocus_iff_basicOpen s hy).1 hy')
  exact ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j)⟩

theorem isLocus_pull {X Y : Scheme.{0}} (f : Y ⟶ X) {c : Pic X} {V : X.Opens} (h : IsLocus c V) :
    IsLocus (GlobalTheory.CechPic.pull f c) (f ⁻¹ᵁ V) := by
  obtain ⟨L, hL, s, rfl, rfl⟩ := h
  exact ⟨_, pull_isLB hL f, GlobalTheory.secPull s f, rfl, GlobalTheory.nonzeroLocus_secPull s f⟩

theorem pull_eq_zero_of_isLocus {X Y : Scheme.{0}} (f : Y ⟶ X) {c : Pic X} {V : X.Opens} (h : IsLocus c V)
    (hf : ∀ y, f y ∈ V) : GlobalTheory.CechPic.pull f c = 0 := by
  obtain ⟨L, hL, s, rfl, rfl⟩ := h
  have htop : ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull s f) = ⊤ := by
    rw [GlobalTheory.nonzeroLocus_secPull]
    exact top_unique fun y _ => hf y
  exact (cls_eq_zero_iff (pull_isLB hL f)).2 (exists_gen_of_nonzeroLocus_eq_top _ htop)

theorem locus_pull :
    (∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (c : Pic X) (V : X.Opens), IsLocus c V → IsLocus (GlobalTheory.CechPic.pull f c) (f ⁻¹ᵁ V)) ∧ (∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (c : Pic X) (V : X.Opens), IsLocus c V → (∀ y, f y ∈ V) → GlobalTheory.CechPic.pull f c = 0) :=
  ⟨fun _ _ f _ _ h => isLocus_pull f h, fun _ _ f _ _ h hf => pull_eq_zero_of_isLocus f h hf⟩

end GlobalTheory.LocusPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusPullbackAndVanishIntoLocusStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus : (∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (c : Pic X) (V : X.Opens), IsLocus c V → IsLocus (GlobalTheory.CechPic.pull f c) (f ⁻¹ᵁ V)) ∧ (∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (c : Pic X) (V : X.Opens), IsLocus c V → (∀ y, f y ∈ V) → GlobalTheory.CechPic.pull f c = 0) := by
  first | exact @GlobalTheory.LocusPull.locus_pull | exact GlobalTheory.LocusPull.locus_pull | (intros; apply GlobalTheory.LocusPull.locus_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataRescaleCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataRescaleCoboundary
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

theorem rescale_tau_val {R' : Type} [CommRing R'] [IsDomain R'] (D : DegPre R') (g : D.X → (FractionRing R')ˣ)
    (a b : D.X) {z : (TK R').left} {J : ((TK R').left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) :
    val ((rescale D g).tau a b) (𝟙 _) z J =
      gm (𝟙 (TK R').left) z ⊤ (unitOn (g (a + b))) * (gm (𝟙 (TK R').left) z ⊤ (unitOn (g a)))⁻¹ *
        (gm (𝟙 (TK R').left) z ⊤ (unitOn (g b)))⁻¹ * val (D.tau a b) (𝟙 _) z J := by
  have hJ' : Good (rescale D g).P.L z J := hJ
  unfold DegPre.tau
  simp only [val_mul hJ', val_mul hJ, val_inv]
  erw [val_inv, val_inv, val_inv]
  have e1 : ∀ χ, val ((rescale D g).psi χ) (𝟙 _) z J = gm (𝟙 (TK R').left) z ⊤ (unitOn (g χ)) * val (D.psi χ) (𝟙 _) z J :=
    fun χ => GlobalTheory.UU.val_scaleGen _ _ _ hJ
  have e2 : val (rescale D g).rigK (𝟙 _) z J = val D.rigK (𝟙 _) z J := rfl
  erw [e1 (a + b), e1 a, e1 b, e2]
  simp only [mul_inv]
  ac_rfl

theorem half_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f f' : D.X → D.X → (FractionRing R')ˣ) (g : D.X → (FractionRing R')ˣ), Half Q ρ D e f → (∀ a b, f a b = g (a + b) * (g a)⁻¹ * (g b)⁻¹ * f' a b) → Half Q ρ (rescale D g) e f' := by
  intro R _ _ R' _ _ Q ρ D e f f' g h hf
  obtain ⟨β, β₂, w, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  refine ⟨β, β₂, w, h₁, h₂, h₃, h₄, h₅, fun κ hκ a b z J J' hJ hJ' => ?_⟩
  have H := h₆ κ hκ a b z J J' hJ hJ'
  have E := rescale_tau_val D g a b hJ'
  have key : ∀ x y : D.X, gm (𝟙 (TK R').left) z ⊤ (unitOn (f x y)) = gm (𝟙 (TK R').left) z ⊤ (unitOn (g (x + y))) *
      (gm (𝟙 (TK R').left) z ⊤ (unitOn (g x)))⁻¹ * (gm (𝟙 (TK R').left) z ⊤ (unitOn (g y)))⁻¹ *
        gm (𝟙 (TK R').left) z ⊤ (unitOn (f' x y)) := fun x y => by
    rw [hf x y]; simp only [unitOn, map_mul, map_inv]
  erw [E]
  refine Eq.trans ?_ H
  erw [key a b]
  ac_rfl

end GlobalTheory.PolDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataRescaleCoboundaryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refinesPolarisedData_rescale_coboundary : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f f' : D.X → D.X → (FractionRing R')ˣ) (g : D.X → (FractionRing R')ˣ), Half Q ρ D e f → (∀ a b, f a b = g (a + b) * (g a)⁻¹ * (g b)⁻¹ * f' a b) → Half Q ρ (rescale D g) e f' := by
  first | exact @GlobalTheory.PolDeg.half_rescale | exact GlobalTheory.PolDeg.half_rescale | (intros; apply GlobalTheory.PolDeg.half_rescale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesUniqueIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesUniqueIso
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem cls_eq_evc_id {S : Scheme.{0}} {A T : Over S} {M : LB (A ⊗ T).left} (hM : M.IsLB) :
    cls M hM = evc hM (fst A T) (snd A T ≫ 𝟙 T) := by
  rw [Category.comp_id, evc, lift_fst_snd, Over.id_left, pull_id]

theorem cls_trans {S : Scheme.{0}} {A B B' B'' : Over S} {P : LB (A ⊗ B).left} {P' : LB (A ⊗ B').left}
    {Q : LB (A ⊗ B'').left} (hP : P.IsLB) (hP' : P'.IsLB) (hQ : Q.IsLB) (x : B ⟶ B') (y : B' ⟶ B'')
    (hx : LBIso P (ev P' (fst A B) (snd A B ≫ x))) (hy : LBIso P' (ev Q (fst A B') (snd A B' ≫ y))) :
    LBIso P (ev Q (fst A B) (snd A B ≫ x ≫ y)) := by
  refine (cls_eq_iff hP (pull_isLB hQ _)).1 ?_
  rw [(cls_eq_iff hP (pull_isLB hP' _)).2 hx, cls_ev hP', cls_ev hQ, evc,
    (cls_eq_iff hP' (pull_isLB hQ _)).2 hy, cls_ev hQ, pull_evc, lift_fst, lift_snd_assoc, Category.assoc]

theorem rep_unique (S : Scheme.{0}) (A B B' S' : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left)
    (b' : B' ⟶ S') (P' : LB (A ⊗ B').left) (h : Rep A b P) (h' : Rep A b' P') :
    ∃ e : B ≅ B', e.hom ≫ b' = b ∧ Same A P P' (𝟙 B) e.hom := by
  have hP := h.fam.isLB
  have hP' := h'.fam.isLB
  obtain ⟨x, ⟨hxb, hxP⟩, -⟩ := h'.univ B b P h.fam
  obtain ⟨y, ⟨hyb, hyP⟩, -⟩ := h.univ B' b' P' h'.fam
  have idB : LBIso P (ev P (fst A B) (snd A B ≫ 𝟙 B)) :=
    (cls_eq_iff hP (pull_isLB hP _)).1 (cls_eq_evc_id hP)
  have idB' : LBIso P' (ev P' (fst A B') (snd A B' ≫ 𝟙 B')) :=
    (cls_eq_iff hP' (pull_isLB hP' _)).1 (cls_eq_evc_id hP')
  have hxy : x ≫ y = 𝟙 B :=
    (h.univ B b P h.fam).unique ⟨by rw [Category.assoc, hyb, hxb], cls_trans hP hP' hP x y hxP hyP⟩
      ⟨Category.id_comp _, idB⟩
  have hyx : y ≫ x = 𝟙 B' :=
    (h'.univ B' b' P' h'.fam).unique ⟨by rw [Category.assoc, hxb, hyb], cls_trans hP' hP hP' y x hyP hxP⟩
      ⟨Category.id_comp _, idB'⟩
  exact ⟨⟨x, y, hxy, hyx⟩, hxb, (same_id_iff hP hP' x).2 hxP⟩

end GlobalTheory.DualCon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesUniqueIsoStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representsAdditiveLineBundleFamilies_unique_iso : ∀ (S : Scheme.{0}) (A B B' S' : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (b' : B' ⟶ S') (P' : LB (A ⊗ B').left), Rep A b P → Rep A b' P' → ∃ e : B ≅ B', e.hom ≫ b' = b ∧ Same A P P' (𝟙 B) e.hom := by
  first | exact @GlobalTheory.DualCon.rep_unique | exact GlobalTheory.DualCon.rep_unique | (intros; apply GlobalTheory.DualCon.rep_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimUniqueOfIsoGrp
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem relDim_unique_of_iso_grp : ∀ (S : Scheme.{0}), Nonempty S → ∀ (X Y : Over S) [GrpObj X] (f : X ⟶ Y), IsIso f → ∀ g g' : ℕ, SmoothOfRelativeDimension g X.hom → SmoothOfRelativeDimension g' Y.hom → g = g' := by
  intro S hS X Y _ f hf g g' hg hg'
  obtain ⟨s⟩ := hS
  have : IsIso f.left := (Over.forget S).map_isIso f
  have sq : CommSq f.left X.hom Y.hom (𝟙 S) := ⟨by rw [Over.w f, Category.comp_id]⟩
  have h2 : SmoothOfRelativeDimension g' X.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback (IsPullback.of_horiz_isIso sq) hg'
  exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique X.hom hg h2 ((η[X]).left s)

end GlobalTheory
end
end
