module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormPeakAtInjectiveChartFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLevelGroupDataSameCovolume
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportMumfordBundleIso

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelWeightGapL1CardBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelWeightGapL1CardBound
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.ModelWtGap

def colRot (p q : ℕ) (a : Fin (p + q)) : Fin (p + q) :=
  if h : (a : ℕ) < q then ⟨p + a, by omega⟩ else ⟨a - q, by omega⟩

theorem colRot_val (p q : ℕ) (a : Fin (p + q)) :
    (colRot p q a : ℕ) = if (a : ℕ) < q then p + a else a - q := by
  unfold colRot
  split_ifs <;> rfl

theorem colRot_bijective (p q : ℕ) : Function.Bijective (colRot p q) := by
  refine Finite.injective_iff_bijective.1 fun a b h => ?_
  have h1 := congrArg Fin.val h
  rw [colRot_val, colRot_val] at h1
  have := a.2
  have := b.2
  apply Fin.ext
  split_ifs at h1 <;> omega

theorem model_weight_gap_l1_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ (u1 : GlobalTheory.AllWt.Weight Dw) (g : ℝ), (∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 → g ≤ (u1 τ a : ℝ) - u1 τ b) → ∀ k : U.Comp, (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ (U.X k).p0 → g ≤ (modelWt U (wtOf Dw u1 0) k τ a : ℝ) - modelWt U (wtOf Dw u1 0) k τ b) ∧ (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (modelWt U (wtOf Dw u1 0) k τ b : ℝ) - modelWt U (wtOf Dw u1 0) k τ a) ∧ (∑ τ, ∑ a, |(modelWt U (wtOf Dw u1 0) k τ a : ℝ)|) = GlobalTheory.CovHt.l1 u1 ∧ (U.X k).Ψ.card = Nat.card (GlobalTheory.AllWt.Psi H) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hp hq u1 g hg k
  obtain rfl := hU.1
  obtain ⟨hp0, hΨ⟩ := hU.2.1 k
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hrel : ∀ ρ : E →+* ℂ, ρ (H.rt : E) = H.rt0 → relab c σ ρ (H.rt : E) = H.rt0 := fun ρ h =>
    (congrArg σ (Subtype.ext h)).trans hσ0
  let e : Psi H → (U.X k).Ψ := fun ρ => ⟨relab c σ ρ.1, (hΨ _).2 (hrel _ ρ.2)⟩
  have hsurj : Function.Surjective (relab (E := E) c σ) := Finite.injective_iff_surjective.1 (relab_injective σ)
  have he : Function.Bijective e := by
    refine ⟨fun a b h => Subtype.ext (relab_injective σ (congrArg Subtype.val h)), fun τ => ?_⟩
    obtain ⟨ρ, hρ⟩ := hsurj τ.1
    have hρΨ : ρ (H.rt : E) = H.rt0 := by
      by_contra hn
      have h3 := hrel _ (GlobalTheory.AllWt.conj_mem hn)
      rw [relab_conj, hρ] at h3
      exact GlobalTheory.AllWt.conj_not_mem ⟨τ.1, (hΨ _).1 τ.2⟩ h3
    exact ⟨⟨ρ, hρΨ⟩, Subtype.ext hρ⟩
  have hval : ∀ (ρ : Psi H) (a : Fin (Dw.p + Dw.q)),
      modelWt U (wtOf Dw u1 0) k (e ρ) a = u1 ρ (colRot Dw.p Dw.q a) := by
    rintro ρ ⟨a, ha⟩
    by_cases h : a < Dw.q
    · rw [modelWt_wtOf_small U u1 0 k hp0 ρ (e ρ).2 a h ha]
      congr 1
      apply Fin.ext
      rw [colRot_val]
      simp [h]
    · obtain ⟨i, rfl⟩ : ∃ i, a = Dw.q + i := ⟨a - Dw.q, by omega⟩
      rw [modelWt_wtOf_big U u1 0 k hp0 ρ (e ρ).2 i (by omega) ha]
      congr 1
      apply Fin.ext
      rw [colRot_val]
      simp
  refine ⟨fun τ a b hab hb => ?_, fun τ a b ha hb => ?_, ?_, ?_⟩
  · obtain ⟨ρ, rfl⟩ := he.2 τ
    rw [hval, hval]
    apply hg
    rw [colRot_val, colRot_val]
    rw [hp0] at hb
    split_ifs <;> omega
  · obtain ⟨ρ, rfl⟩ := he.2 τ
    rw [hval, hval]
    apply hg
    rw [colRot_val, colRot_val]
    split_ifs <;> omega
  · unfold GlobalTheory.CovHt.l1
    rw [← he.sum_comp]
    refine Finset.sum_congr (by congr) fun ρ _ => ?_
    simp only [hval]
    exact (colRot_bijective Dw.p Dw.q).sum_comp fun i => |(u1 ρ i : ℝ)|
  · rw [Nat.card_eq_of_bijective e he, Nat.card_eq_fintype_card, Fintype.card_coe]

end GlobalTheory.ModelWtGap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelWeightGapL1CardBoundStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_weight_gap_l1_card_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ (u1 : GlobalTheory.AllWt.Weight Dw) (g : ℝ), (∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 → g ≤ (u1 τ a : ℝ) - u1 τ b) → ∀ k : U.Comp, (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ (U.X k).p0 → g ≤ (modelWt U (wtOf Dw u1 0) k τ a : ℝ) - modelWt U (wtOf Dw u1 0) k τ b) ∧ (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (modelWt U (wtOf Dw u1 0) k τ b : ℝ) - modelWt U (wtOf Dw u1 0) k τ a) ∧ (∑ τ, ∑ a, |(modelWt U (wtOf Dw u1 0) k τ a : ℝ)|) = GlobalTheory.CovHt.l1 u1 ∧ (U.X k).Ψ.card = Nat.card (GlobalTheory.AllWt.Psi H) := by
  first | exact @GlobalTheory.ModelWtGap.model_weight_gap_l1_card | exact GlobalTheory.ModelWtGap.model_weight_gap_l1_card | (intros; apply GlobalTheory.ModelWtGap.model_weight_gap_l1_card <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLowerBoundBergmanFunctionOnComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLowerBoundBergmanFunctionOnComponent
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.BergLower

open MeasureTheory ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem le_div_of_mean {β a I v S m J N : ℝ≥0∞} (ha0 : a ≠ 0) (hat : a ≠ ⊤) (hS0 : S ≠ 0) (hv : v ≠ ⊤)
    (hI : v = 0 → I = 0) (hβ : β * I ≤ a * v) (hJ : J * S = I) (hm : v ≤ m * S) (hN : N ≤ m⁻¹ * J) :
    β ≤ a / N := by
  rw [ENNReal.le_div_iff_mul_le (Or.inr ha0) (Or.inr hat)]
  by_cases h0 : v = 0
  · have hJ0 : J = 0 := by
      rw [hI h0] at hJ
      exact (mul_eq_zero.1 hJ).resolve_right hS0
    rw [hJ0, mul_zero, nonpos_iff_eq_zero] at hN
    simp [hN]
  · have h1 : N * v ≤ I := by
      calc N * v ≤ (m⁻¹ * J) * (m * S) := by gcongr
        _ = (m⁻¹ * m) * (J * S) := by ring
        _ ≤ 1 * I := by
          rw [hJ]
          gcongr
          exact ENNReal.inv_mul_le_one m
        _ = I := one_mul _
    have h2 : β * N * v ≤ a * v := by
      rw [mul_assoc]
      exact le_trans (by gcongr) hβ
    exact (ENNReal.mul_le_mul_iff_left h0 hv).1 h2

theorem pnorm_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {P : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hP : P x ≠ 0) : 0 < X.pnorm la P x := by
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i h => by
    have := (hx τ).2 i
    rw [h] at this
    simp at this
  unfold Data.pnorm
  exact mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _)

theorem le_bergOn : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E) (Z : Comp Xo c) (y : FPt (U σ).X), (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ D.R.r) ∈ framesOn (U σ) Z → ∀ β : ENNReal, (∀ (x0 : Frame ((U σ).X y.1).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd ((U σ).X y.1)))), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth ((U σ).X y.1) x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet ((U σ).X y.1) x0 FF → ∃ P ∈ ((U σ).X y.1).SS (modelWt (U σ) G y.1), P y.2.1 ≠ 0 ∧ β * ∫⁻ z in FF, ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X y.1) x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0) ≤ ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P y.2.1 ^ 2) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0 FF) → β ≤ bergOn (U σ) (D.sp.W j) (dict σ) Z G y := by
  intro D j H Dw l Xo c U dict hL σ hσ G Z y hy β hβ
  classical
  have hU : IsUnf (U σ) := hL.unf σ hσ
  obtain ⟨Kf, th, hr, -, -, hDU, -⟩ := hL.dictU σ hσ
  have hdom : ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom := Formalism.L2.Pj.dict_dom_of hDU
  have hex : ∀ (X : Data D.host.E D.R.r), ∃ x0, IsOrth X x0 ∧ ∃ FF, IsFundSet X x0 FF := fun X => by
    choose P _ hG using X.signature
    exact ⟨fun τ => P τ, fun τ => hG τ, GlobalTheory.MetricWeightTest.exists_fundSet_orth X (fun τ => hG τ)⟩
  choose x0 hx0 FF hFF using fun k => hex ((U σ).X k)
  obtain ⟨P, hP, hPy, hle⟩ := hβ (x0 y.1) (FF y.1) (hx0 _) (hFF _)
  set la := modelWt (U σ) G with hla
  obtain ⟨hS0, hST, hI⟩ := GlobalTheory.LevGeo.adelicProb_mul_volFund D j H Dw l Xo c U dict hL σ hσ x0 FF
    (fun k => ⟨hx0 k, hFF k⟩)
  set Q : Frame ((U σ).X y.1).Ψ D.R.r → ℂ := ((U σ).X y.1).dom.indicator P with hQ
  have hQP : ∀ x ∈ ((U σ).X y.1).dom, ((U σ).X y.1).pnorm (la y.1) Q x = ((U σ).X y.1).pnorm (la y.1) P x :=
    fun x hx => by unfold Data.pnorm; rw [hQ, Set.indicator_of_mem hx]
  have hQS : Q ∈ ((U σ).X y.1).SS (la y.1) :=
    (GlobalTheory.DomCongr.bddSec_cusp_congr D.host.E D.R.r _ _ P Q (fun x hx => (Set.indicator_of_mem hx _).symm)).2 hP
  set P' : Formalism.L2.Pj.FDSec (U σ).X := Function.update (fun _ => 0) y.1 Q with hP'
  have hP'y : P' y.1 = Q := Function.update_self _ _ _
  have hP'n : ∀ k, k ≠ y.1 → P' k = 0 := fun k hk => Function.update_of_ne hk _ _
  have hP'S : ∀ k, P' k ∈ ((U σ).X k).SS (la k) := fun k => by
    by_cases hk : k = y.1
    · subst hk; rw [hP'y]; exact hQS
    · rw [hP'n k hk]
      exact (ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds (E := D.host.E) D.R.r ((U σ).X k) (la k) (la k) 0).1.1
  have hP'0 : ∀ k, ∀ x ∉ ((U σ).X k).dom, P' k x = 0 := fun k x hx => by
    by_cases hk : k = y.1
    · subst hk; rw [hP'y]; exact Set.indicator_of_notMem hx _
    · rw [hP'n k hk]; rfl
  have hP'm : P' ∈ Formalism.L2.Pj.holSub (U σ).X la := Formalism.L2.Pj.holCusp_mem_holSub _ _ hP'S
  have hsf : ∀ k, ((U σ).X k).IsSec (la k) (P' k) := fun k => (hP'S k).1.1
  have hJ := hI (fun k x => ENNReal.ofReal (((U σ).X k).pnorm (la k) (P' k) x ^ 2))
    (fun k => ENNReal.measurable_ofReal.comp ((GlobalTheory.PeterssonCompare.measurable_pnorm _ _
      (hsf k).1.continuousOn (hP'0 k)).pow_const 2))
    (fun k γ hγ x hx => by simp only [GlobalTheory.PeterssonCompare.pnorm_lact _ (hsf k) hγ hx])
    (fun k b hb x hx => by simp only [FrameDegreeData.pnorm_rmul _ _ _ (hsf k).2.1 x hx b hb])
  rw [Finset.sum_eq_single y.1 (f := fun k => ∫⁻ z in FF k, ENNReal.ofReal (((U σ).X k).pnorm (la k) (P' k)
      (cpt ((U σ).X k) (x0 k) z) ^ 2) ∂(muF ((U σ).X k) (x0 k)))
      (fun k _ hk => by simp [hP'n k hk, Formalism.L2.Pj.pnorm_zero])
    (fun h => absurd (Finset.mem_univ _) h), hP'y,
    setLIntegral_congr_fun (hFF y.1).1 (g := fun z => ENNReal.ofReal (((U σ).X y.1).pnorm (la y.1) P
      (cpt ((U σ).X y.1) (x0 y.1) z) ^ 2)) (fun z hz => by simp only [hQP _ ((hFF y.1).2.1 hz)])] at hJ
  have hM := hI (fun k _ => if k = y.1 then 1 else 0) (fun _ => measurable_const) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
  rw [Finset.sum_eq_single y.1 (f := fun k => ∫⁻ z in FF k, (if k = y.1 then (1 : ℝ≥0∞) else 0)
      ∂(muF ((U σ).X k) (x0 k))) (fun k _ hk => by simp [hk]) (fun h => absurd (Finset.mem_univ _) h),
    if_pos rfl, setLIntegral_one] at hM
  set Cl := classesOver (D.sp.W j) (dict σ) (framesOn (U σ) Z) with hCl
  have hm : ∫⁻ q : AutQ (D.sp.W j), (if (dict σ q.out).1 = y.1 then (1 : ℝ≥0∞) else 0) ∂(muQ1 (D.sp.W j)) ≤
      muQ1 (D.sp.W j) Cl := by
    refine le_trans (lintegral_mono fun q => ?_) (lintegral_indicator_one_le Cl)
    split_ifs with hq
    · have : q ∈ Cl := by
        have h1 := hdom q.out
        show dict σ q.out ∈ framesOn (U σ) Z
        generalize dict σ q.out = z at hq h1
        obtain ⟨k, x⟩ := z
        obtain rfl : k = y.1 := hq
        exact GlobalTheory.FramesUnion.framesOn_of_mem D.host.E H Dw l Xo c D.R.r U σ hU Z _ _ x h1 hy
      simp [this]
    · exact zero_le
  have hN : petE (D.sp.W j) (dict σ) (muOn (U σ) (D.sp.W j) (dict σ) Z) la P' ^ 2 ≤ (muQ1 (D.sp.W j) Cl)⁻¹ *
      ∫⁻ q : AutQ (D.sp.W j), ENNReal.ofReal (((U σ).X (dict σ q.out).1).pnorm (la (dict σ q.out).1)
        (P' (dict σ q.out).1) (dict σ q.out).2 ^ 2) ∂(muQ1 (D.sp.W j)) := by
    have e : petE (D.sp.W j) (dict σ) (muOn (U σ) (D.sp.W j) (dict σ) Z) la P' ^ 2 =
        ∫⁻ q : AutQ (D.sp.W j), ‖ptN la P' (dict σ q.out)‖ₑ ^ 2 ∂(muOn (U σ) (D.sp.W j) (dict σ) Z) := by
      have := lintegral_rpow_eNorm_eq_rpow_eLpNorm' (μ := muOn (U σ) (D.sp.W j) (dict σ) Z)
        (f := fun q : AutQ (D.sp.W j) => ptN la P' (dict σ q.out)) (q := 2) (by norm_num)
      simpa [petE, ENNReal.rpow_natCast] using this.symm
    rw [e]
    show ∫⁻ q, _ ∂((muQ1 (D.sp.W j) Cl)⁻¹ • (muQ1 (D.sp.W j)).restrict Cl) ≤ _
    rw [lintegral_smul_measure, smul_eq_mul]
    refine mul_le_mul_right
      (le_trans (lintegral_mono' Measure.restrict_le_self le_rfl) (le_of_eq (lintegral_congr fun q => ?_))) _
    rw [Real.enorm_eq_ofReal (ptN_nonneg _ _ _), ← ENNReal.ofReal_pow (ptN_nonneg _ _ _)]
    rfl
  have hpos := pnorm_pos ((U σ).X y.1) (la y.1) y.2.2 hPy
  have hpt : ENNReal.ofReal (ptN la P' ⟨y.1, y.2.1⟩) ^ 2 =
      ENNReal.ofReal (((U σ).X y.1).pnorm (la y.1) P y.2.1 ^ 2) := by
    rw [ENNReal.ofReal_pow hpos.le]
    show ENNReal.ofReal (((U σ).X y.1).pnorm (la y.1) (P' y.1) y.2.1) ^ 2 = _
    rw [hP'y, hQP _ y.2.2]
  refine le_trans ?_ (le_iSup₂_of_le (f := fun P (_ : P ∈ Formalism.L2.Pj.holSub (U σ).X la) =>
    ENNReal.ofReal (ptN la P ⟨y.1, y.2.1⟩) ^ 2 /
      petE (D.sp.W j) (dict σ) (muOn (U σ) (D.sp.W j) (dict σ) Z) la P ^ 2) P' hP'm le_rfl)
  rw [hpt]
  refine le_div_of_mean (ENNReal.ofReal_pos.2 (pow_pos hpos 2)).ne' ENNReal.ofReal_ne_top hS0
    (ne_top_of_le_ne_top hST (Finset.single_le_sum (f := fun k => muF ((U σ).X k) (x0 k) (FF k))
      (fun _ _ => zero_le) (Finset.mem_univ y.1)))
    (fun h => setLIntegral_measure_zero _ _ h) hle hJ ?_ hN
  rw [← hM]
  gcongr

end GlobalTheory.BergLower
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLowerBoundBergmanFunctionOnComponentStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_lower_bound_bergmanFunction_on_component : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E) (Z : Comp Xo c) (y : FPt (U σ).X), (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ D.R.r) ∈ framesOn (U σ) Z → ∀ β : ENNReal, (∀ (x0 : Frame ((U σ).X y.1).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd ((U σ).X y.1)))), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth ((U σ).X y.1) x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet ((U σ).X y.1) x0 FF → ∃ P ∈ ((U σ).X y.1).SS (modelWt (U σ) G y.1), P y.2.1 ≠ 0 ∧ β * ∫⁻ z in FF, ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X y.1) x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0) ≤ ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P y.2.1 ^ 2) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0 FF) → β ≤ bergOn (U σ) (D.sp.W j) (dict σ) Z G y := by
  first | exact @GlobalTheory.BergLower.le_bergOn | exact GlobalTheory.BergLower.le_bergOn | (intros; apply GlobalTheory.BergLower.le_bergOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepCongruenceElementSeparatesChartBallThickFram
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepCongruenceElementSeparatesChartBallThickFram
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

noncomputable section

namespace GlobalTheory.ThickSep

open ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates Module Submodule
open scoped ComplexConjugate Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def scl (X : Data E r) (s : X.Ψ → ℝ) : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) where
  toFun u τ := ((s τ : ℝ) : ℂ) • u τ
  map_add' u v := by funext τ; simp [smul_add]
  map_smul' c u := by
    funext τ
    simp only [Pi.smul_apply, RingHom.id_apply]
    exact smul_comm ((s τ : ℝ) : ℂ) c (u τ)

theorem gI_scl (X : Data E r) (x : Frame X.Ψ r) (s t : X.Ψ → ℝ) (u v : X.Ψ → Fin r → ℂ) :
    MajorantOperators.gI x (scl X s u) (scl X t v) = ∑ τ, s τ * t τ * (X.Hf x τ (u τ) (v τ)).re := by
  unfold MajorantOperators.gI
  refine Finset.sum_congr rfl fun τ _ => ?_
  show (X.Hf x τ (((s τ : ℝ) : ℂ) • u τ) (((t τ : ℝ) : ℂ) • v τ)).re = _
  rw [UnipotentCoefficientShift.Hf_smul_left, UnipotentCoefficientShift.Hf_smul_right, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, Complex.re_ofReal_mul]

def Qf (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) : ℝ :=
  ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)

theorem firstMinimumSq_le_weightedMajorantQuadraticForm (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {w : Fin r → E}
    (hw : w ∈ X.Λ) (hw0 : w ≠ 0) : X.firstMinimumSq x ≤ Qf X x w := by
  refine csInf_le ⟨0, ?_⟩ ⟨w, hw, hw0, rfl⟩
  rintro _ ⟨u, -, -, rfl⟩
  exact Finset.sum_nonneg fun τ _ =>
    mul_nonneg (TwoSidedBoostBounds.c_pos X τ).le (MajorantOperators.maj_nonneg hx τ _)

theorem Hf_refl_self (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (a : Fin r → ℂ) :
    (X.Hf x τ ((2 : ℂ) • X.jp x τ a) ((2 : ℂ) • X.jp x τ a)).re = 4 * X.maj x τ a := by
  rw [UnipotentCoefficientShift.Hf_smul_right, UnipotentCoefficientShift.Hf_smul_left, Data.Hf_eq_jp, X.hermC_jp_jp hx,
    ← Data.Hf_eq_jp, X.Hf_self hx, show (starRingEnd ℂ) 2 = 2 from map_ofNat _ 2]
  simp
  ring

theorem exists_short (X : Data E r) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (hsd : EqCovol.IsSelfDualTr X) (hl : 0 < X.firstMinimumSq x) :
    ∃ v : Fin (2 * fdeg E * r) → Fin r → E, (∀ i, v i ∈ X.Λ) ∧ LinearIndependent ℚ v ∧
      ∃ φ : (Fin r → E) →+ EuclideanSpace ℝ (Fin (2 * fdeg E * r)),
        (∀ u, ‖φ u‖ ^ 2 = Qf X x u) ∧
        ∀ i, ‖φ (v i)‖ ^ 2 ≤ (((2 * fdeg E * r : ℕ) : ℝ) ^ 2 / √(X.firstMinimumSq x)) ^ 2 := by
  classical
  obtain ⟨b, hb⟩ := ShortVectors.exists_basis X.Λ X.Λ_fg X.Λ_span
  have hcard : Fintype.card X.Ψ = fdeg E := QuadraticCoefficientForms.card_Psi (X := X)
  have hfr : finrank ℝ (X.Ψ → Fin r → ℂ) = 2 * fdeg E * r := by
    rw [Module.finrank_pi_fintype, ← hcard]
    simp [Module.finrank_pi_fintype]
    ring
  obtain ⟨θ, hθ⟩ := ThickPoint.exists_euclidean_real hfr (ThickPoint.majForm X x hx)
    ⟨fun u v => MajorantOperators.gI_comm hx u v⟩ (fun u => by
      rw [ThickPoint.majForm_apply, MajorantOperators.gI_self hx]
      exact Finset.sum_nonneg fun τ _ => MajorantOperators.maj_nonneg hx τ _)
  have hc : ∀ τ : X.Ψ, 0 < X.c τ := fun τ => TwoSidedBoostBounds.c_pos X τ
  let sc : X.Ψ → ℝ := fun τ => √(X.c τ)
  let si : X.Ψ → ℝ := fun τ => (√(X.c τ))⁻¹
  have hss : ∀ τ, sc τ * si τ = 1 := fun τ =>
    mul_inv_cancel₀ (Real.sqrt_pos.2 (hc τ)).ne'
  have hsc : ∀ τ, sc τ * sc τ = X.c τ := fun τ => Real.mul_self_sqrt (hc τ).le
  have hsi : ∀ τ, si τ * si τ = (X.c τ)⁻¹ := fun τ => by
    simp only [si, ← mul_inv, Real.mul_self_sqrt (hc τ).le]
  let φ : (Fin r → E) →+ EuclideanSpace ℝ (Fin (2 * fdeg E * r)) :=
    ((θ.comp (scl X sc)).toAddMonoidHom).comp (ThickPoint.embHom X)
  let ψ : (Fin r → E) →+ EuclideanSpace ℝ (Fin (2 * fdeg E * r)) :=
    ((θ.comp (scl X si)).toAddMonoidHom).comp (ThickPoint.reflHom X x)
  have hφψ : ∀ u w, inner ℝ (φ u) (ψ w) = (ThickPoint.traceFormOf X.Gm u w : ℝ) := by
    intro u w
    show inner ℝ (θ (scl X sc _)) (θ (scl X si _)) = _
    rw [hθ, ThickPoint.majForm_apply, gI_scl, ← ThickPoint.pair_eq X x hx u w]
    unfold MajorantOperators.gI
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hss, one_mul]
  have hφ : ∀ u, ‖φ u‖ ^ 2 = Qf X x u := by
    intro u
    rw [← real_inner_self_eq_norm_sq]
    show inner ℝ (θ (scl X sc _)) (θ (scl X sc _)) = _
    rw [hθ, ThickPoint.majForm_apply, gI_scl]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hsc]
    show X.c τ * (X.Hf x τ (Data.emb τ.1 u) (Data.emb τ.1 u)).re = _
    rw [X.Hf_self hx, Complex.ofReal_re]
  have hψ : ∀ w, ‖ψ ((-X.ξ0) • w)‖ ^ 2 = Qf X x w := by
    intro w
    rw [← real_inner_self_eq_norm_sq]
    show inner ℝ (θ (scl X si _)) (θ (scl X si _)) = _
    rw [hθ, ThickPoint.majForm_apply, gI_scl]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hsi]
    show (X.c τ)⁻¹ * (X.Hf x τ ((2 : ℂ) • X.jp x τ (Data.emb τ.1 ((-X.ξ0) • w)))
      ((2 : ℂ) • X.jp x τ (Data.emb τ.1 ((-X.ξ0) • w)))).re = _
    rw [Hf_refl_self X hx]
    have he : Data.emb τ.1 ((-X.ξ0) • w) = (τ.1 (-X.ξ0)) • Data.emb τ.1 w := by
      funext a; simp [Data.emb]
    rw [he, UnipMove.DeltaValuation.maj_smul, Complex.normSq_eq_norm_sq, map_neg, norm_neg]
    have hcτ : X.c τ = 2 * ‖τ.1 X.ξ0‖ := rfl
    have h0 := hc τ
    rw [hcτ] at h0 ⊢
    field_simp
    ring
  obtain ⟨v, hv, hli, hle⟩ := ThickPoint.transference_pair b (ThickPoint.traceFormOf X.Gm)
    (ThickPoint.traceFormOf_isSymm X.Gm_herm) (ThickPoint.traceFormOf_nondegenerate X.Gm_herm X.Gm_det)
    φ ψ hφψ (√(X.firstMinimumSq x)) (Real.sqrt_pos.2 hl) (by
      intro u hu hk
      have hξ : -X.ξ0 ≠ 0 := neg_ne_zero.2 X.ξ0_ne
      obtain ⟨w, rfl⟩ : ∃ w, u = (-X.ξ0) • w :=
        ⟨(-X.ξ0)⁻¹ • u, by rw [smul_smul, mul_inv_cancel₀ hξ, one_smul]⟩
      have hw0 : w ≠ 0 := by rintro rfl; exact hu (smul_zero _)
      have hw : w ∈ X.Λ := by
        refine (hsd w).2 fun y hy => ?_
        obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 ((hb y).2 hy)
        choose k hk using hk
        refine ⟨∑ j, c j * k j, ?_⟩
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← HermitianTraceFormVanishing.herm_smul_left, ← ThickPoint.traceFormOf_apply, map_sum]
        simp only [map_zsmul, hk]
        simp
      rw [Real.sq_sqrt hl.le, hψ]
      exact firstMinimumSq_le_weightedMajorantQuadraticForm X hx hw hw0)
  exact ⟨v, fun i => (hb _).1 (hv i), hli, φ, hφ, hle⟩

theorem maj_le_four (X : Data E r) {x : Frame X.Ψ r} (hx : ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x)
    {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ) {z z' : V (nd X)}
    (hz : (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100) (hz' : (r : ℝ) ^ 2 * ‖z'‖ ≤ 1 / 100)
    {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (heq : lact γ (cpt X x z) = rmul (cpt X x z') b) (τ : X.Ψ) (v : Fin r → E) :
    X.maj x τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v)) ≤
      4 * X.maj x τ (Data.emb τ.1 v) := by
  have h1 := (GlobalTheory.ChartGraph.maj_cpt_le_two E r X x z' hx hz' τ
    (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v))).2
  have h2 := (GlobalTheory.ChartGraph.maj_cpt_le_two E r X x z hx hz τ (Data.emb τ.1 v)).1
  have e1 : X.maj (cpt X x z') τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v)) =
      X.maj (cpt X x z) τ (Data.emb τ.1 v) := by
    rw [← GlobalTheory.ChartMult.maj_rmul_any X _ hb, ← heq, GlobalTheory.ChartMult.emb_mulVec',
      GlobalTheory.MajInv.maj_lact X hγ]
  rw [e1] at h1
  linarith

theorem Qf_le_four (X : Data E r) {x : Frame X.Ψ r} (hx : ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x)
    {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ) {z z' : V (nd X)}
    (hz : (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100) (hz' : (r : ℝ) ^ 2 * ‖z'‖ ≤ 1 / 100)
    {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (heq : lact γ (cpt X x z) = rmul (cpt X x z') b) (v : Fin r → E) :
    Qf X x ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) ≤ 4 * Qf X x v := by
  unfold Qf
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  have := mul_le_mul_of_nonneg_left (maj_le_four X hx hγ hz hz' hb heq τ v)
    (TwoSidedBoostBounds.c_pos X τ).le
  linarith

theorem Qf_nsmul (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (M : ℕ) (w : Fin r → E) :
    Qf X x (M • w) = (M : ℝ) ^ 2 * Qf X x w := by
  unfold Qf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have he : Data.emb τ.1 (M • w) = ((M : ℝ) : ℂ) • Data.emb τ.1 w := by
    funext a; simp [Data.emb, nsmul_eq_mul]
  rw [he, UnipotentCoefficientShift.maj_smul hx]
  ring

theorem deep_cong_chart_sep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (M : ℕ) (x : Frame X.Ψ r), GlobalTheory.EqCovol.IsSelfDualTr X → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → 100 * ((X.Ψ.card : ℝ) * r) ^ 4 ≤ (M : ℝ) * X.firstMinimumSq x → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → (∀ v ∈ X.Λ, ∃ w ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec v - v = M • w) → ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1 := by
  intro E _ _ _ r X M x hsd hx hM γ hγ hcong z z' hz hz' b hb heq
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact Units.ext (Matrix.ext fun i => i.elim0)
  have hdom : x ∈ X.dom := ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.dom_of_orth X hx
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hsm : ∀ w : V (nd X), ‖w‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → (r : ℝ) ^ 2 * ‖w‖ ≤ 1 / 100 := by
    intro w hw
    calc (r : ℝ) ^ 2 * ‖w‖ ≤ (r : ℝ) ^ 2 * (1 / (100 * (r : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
      _ = 1 / 100 := by field_simp
  have hcard : (X.Ψ.card : ℝ) = fdeg E := by
    rw [← QuadraticCoefficientForms.card_Psi (X := X), Fintype.card_coe]
  have hf : (1 : ℝ) ≤ fdeg E := by
    have := QuadraticCoefficientForms.card_Psi_pos (X := X)
    rw [QuadraticCoefficientForms.card_Psi (X := X)] at this
    exact_mod_cast this
  set P : ℝ := (fdeg E : ℝ) * r with hP
  have hP1 : 1 ≤ P := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  rw [hcard] at hM
  have hP4 : 1 ≤ P ^ 4 := one_le_pow₀ hP1
  have hla : 0 < X.firstMinimumSq x := by
    by_contra h
    push_neg at h
    have := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg M) h
    nlinarith
  obtain ⟨v, hvΛ, hli, φ, hφ, hvs⟩ := exists_short X x hdom hsd hla
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v i ≠ v i := by
    by_contra hall
    push_neg at hall
    apply hne
    have hcv : Fintype.card (Fin (2 * fdeg E * r)) = finrank ℚ (Fin r → E) := by
      rw [Fintype.card_fin, Module.finrank_pi_fintype, ShortVectors.finrank_eq]
      simp
      ring
    have hfN : 0 < fdeg E := by
      have := QuadraticCoefficientForms.card_Psi_pos (X := X)
      rwa [QuadraticCoefficientForms.card_Psi (X := X)] at this
    haveI : Nonempty (Fin (2 * fdeg E * r)) := ⟨⟨0, by positivity⟩⟩
    let B := basisOfLinearIndependentOfCardEqFinrank hli hcv
    have hlin : (Matrix.mulVecLin (γ : Matrix (Fin r) (Fin r) E)).restrictScalars ℚ =
        LinearMap.id := B.ext fun j => by
      simp [B, hall j]
    refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun y => ?_))
    have := LinearMap.congr_fun hlin y
    simpa using this
  obtain ⟨w, hwΛ, hw⟩ := hcong (v i) (hvΛ i)
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [smul_zero, sub_eq_zero] at hw
    exact hi hw
  have h1 : (M : ℝ) ^ 2 * X.firstMinimumSq x ≤ ‖φ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v i - v i)‖ ^ 2 := by
    rw [hφ, hw, Qf_nsmul X hdom]
    exact mul_le_mul_of_nonneg_left (firstMinimumSq_le_weightedMajorantQuadraticForm X hdom hwΛ hw0) (by positivity)
  have h2 : ‖φ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v i)‖ ≤ 2 * ‖φ (v i)‖ := by
    have h := Qf_le_four X hx hγ (hsm z hz) (hsm z' hz') hb heq (v i)
    rw [← hφ, ← hφ] at h
    have : ‖φ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v i)‖ ^ 2 ≤ (2 * ‖φ (v i)‖) ^ 2 := by
      rw [mul_pow]; linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 this
  have h3 : ‖φ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v i - v i)‖ ≤ 3 * ‖φ (v i)‖ := by
    rw [map_sub]
    have := norm_sub_le (φ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v i)) (φ (v i))
    linarith
  have h4 : ‖φ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v i - v i)‖ ^ 2 ≤ 9 * ‖φ (v i)‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) h3 2
    rw [mul_pow] at this
    linarith
  have h5 := hvs i
  have hK : (((2 * fdeg E * r : ℕ) : ℝ) ^ 2 / √(X.firstMinimumSq x)) ^ 2 = 16 * P ^ 4 / X.firstMinimumSq x := by
    rw [div_pow, Real.sq_sqrt hla.le, hP]
    push_cast
    ring
  rw [hK] at h5
  have h6 : (M : ℝ) ^ 2 * X.firstMinimumSq x ≤ 9 * (16 * P ^ 4 / X.firstMinimumSq x) := by linarith
  have h7 : ((M : ℝ) * X.firstMinimumSq x) ^ 2 ≤ 144 * P ^ 4 := by
    have := mul_le_mul_of_nonneg_right h6 hla.le
    rw [mul_assoc 9, div_mul_cancel₀ _ hla.ne'] at this
    nlinarith
  have h8 : (100 * P ^ 4) ^ 2 ≤ ((M : ℝ) * X.firstMinimumSq x) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hM 2
  nlinarith

end GlobalTheory.ThickSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepCongruenceElementSeparatesChartBallThickFramStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deep_congruence_element_separates_chart_ball_thick_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (M : ℕ) (x : Frame X.Ψ r), GlobalTheory.EqCovol.IsSelfDualTr X → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → 100 * ((X.Ψ.card : ℝ) * r) ^ 4 ≤ (M : ℝ) * X.firstMinimumSq x → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → (∀ v ∈ X.Λ, ∃ w ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec v - v = M • w) → ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1 := by
  first | exact @GlobalTheory.ThickSep.deep_cong_chart_sep | exact GlobalTheory.ThickSep.deep_cong_chart_sep | (intros; apply GlobalTheory.ThickSep.deep_cong_chart_sep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualAndPrincipalCongruenceOrbitsOfGoodLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualAndPrincipalCongruenceOrbitsOfGoodLevel
noncomputable section

namespace GlobalTheory.EqCovol.CongrOrb

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory GlobalTheory.EqCovol
open scoped Matrix nonZeroDivisors


set_option maxHeartbeats 800000 in
theorem selfDual_and_congr_free (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H)
    (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ)
    (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (hq : 1 ≤ Dw.q) (k : U.Comp) :
    GlobalTheory.EqCovol.IsSelfDualTr (U.X k) ∧ ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, ∃ γ' : GL (Fin r) E,
      IsUStab (U.X k).Gm (U.X k).Λ γ' ∧
      (∀ v ∈ (U.X k).Λ, ∃ w ∈ (U.X k).Λ, (γ' : Matrix (Fin r) (Fin r) E).mulVec v - v = l.M' • w) ∧
      ∃ b ∈ Bor (U.X k).Ψ r, lact γ x = rmul (lact γ' x) b := by
  classical
  obtain ⟨hr, hty, -, h4, -, g, e, F, ik, φ, hef, hun⟩ := hU
  obtain ⟨φ0, hφe⟩ : ∃ φ0 : (F.Di (ik k)).La →ₗ[𝓞 E] (Fin r → E), ∀ a, φ0 a = (φ k a : Fin r → E) :=
    ⟨(U.X k).Λ.subtype ∘ₗ (φ k).toLinearMap, fun _ => rfl⟩
  have hΛ : LinearMap.range φ0 = (U.X k).Λ := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      rw [hφe]
      exact (φ k a).2
    · intro hy
      exact ⟨(φ k).symm ⟨y, hy⟩, by rw [hφe, LinearEquiv.apply_symm_apply]⟩
  have hlat : Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧
      (∀ a b, cc ((U.X k).Gm a b) = (U.X k).Gm b a) ∧ (U.X k).Gm.det ≠ 0 ∧
      ∀ x y, (((F.Di (ik k)).EF x y : ℤ) : ℚ) =
        Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ0 x) (φ0 y)) := by
    refine ⟨fun a b hab => ?_, ?_, (U.X k).Gm_herm, (U.X k).Gm_det, fun x y => ?_⟩
    · rw [hφe, hφe] at hab
      exact (φ k).injective (Subtype.ext hab)
    · rw [← LinearMap.coe_range, hΛ]
      exact (U.X k).Λ_span
    · rw [hφe, hφe]
      exact hef k x y
  have hξ := (U.X k).ξ0_im
  have hξ' : cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    unfold cc at hξ ⊢
    rw [map_neg, hξ]
  have hneg : ∀ τ ∈ (U.X k).Ψ, (τ (U.X k).ξ0).im < 0 := by
    obtain ⟨x, hx⟩ := GlobalTheory.UnifFamily.dom_nonempty (U.X k)
    obtain ⟨Pm, h1, h2, -⟩ := hun k ⟨x, hx⟩
    exact GlobalTheory.FrameSign.im_neg_of_isPeriod E H Dw l c σ g e _ r (U.X k) (φ k) hσ hr (hty k).1 (hty k).2 (hef k)
      x hx Pm h1 h2 (by omega)
  obtain ⟨m, hm, ht⟩ := GlobalTheory.T.transvection_mem_principalCongruenceGroup E H l _ r _ _ φ0 hξ hlat
  have hi := GlobalTheory.T.principalLevelGroup_finiteIndex_unitaryStabiliser E H l _ r _ _ φ0 hξ hlat
  have hf := GlobalTheory.T.principalGroup_acts_freely_on_flags E H l _ r _ _ φ0 hξ hlat (U.X k).Ψ (U.X k).p0 (hty k).2
  have hmem : ∀ γ : GL (Fin r) E, γ ∈ princ l (U.X k).Gm (F.Di (ik k)) φ0 ↔ IsUStab (U.X k).Gm (U.X k).Λ γ ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di (ik k)).La), ∃ b : (F.Di (ik k)).La,
        (γ : Matrix (Fin r) (Fin r) E).mulVec (φ k a : Fin r → E) =
          (φ k a : Fin r → E) + (l.M : ℕ) • (φ k b : Fin r → E)) ∧
      ∀ a : (F.Di (ik k)).La, ∃ b : (F.Di (ik k)).La,
        (γ : Matrix (Fin r) (Fin r) E).mulVec (φ k a : Fin r → E) =
          (φ k a : Fin r → E) + (l.A : ℕ) • (φ k b : Fin r → E) := by
    intro γ
    simp only [← hφe]
    rw [← hΛ]
    exact Iff.rfl
  have hs : ∀ γ ∈ princ l (U.X k).Gm (F.Di (ik k)) φ0, IsUStab (U.X k).Gm (U.X k).Λ γ :=
    fun γ hγ => ((hmem γ).1 hγ).1
  rw [hΛ] at hi ht
  set Y := reGrp (U.X k) _ m hs hi hf hm (ht _ (U.X k).κ0_xi) with hYdef
  have hL : GlobalTheory.EqCovol.IsLevGrp l Y := by
    intro γ
    refine (hmem γ).trans (and_congr Iff.rfl (and_congr ?_ ?_))
    · have hI : (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (U.X k).Λ =
          (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di (ik k)).La)).map φ0 := by
        rw [Submodule.map_smul'', Submodule.map_top, hΛ]
      show _ ↔ ∀ x ∈ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (U.X k).Λ, ∃ y ∈ (U.X k).Λ, _
      rw [hI]
      simp only [← hφe]
      rw [← hΛ]
      constructor
      · rintro h _ ⟨a, ha, rfl⟩
        obtain ⟨b, hb⟩ := h a ha
        exact ⟨_, ⟨b, rfl⟩, sub_eq_iff_eq_add'.2 hb⟩
      · intro h a ha
        obtain ⟨_, ⟨b, rfl⟩, hb⟩ := h _ ⟨a, ha, rfl⟩
        exact ⟨b, sub_eq_iff_eq_add'.1 hb⟩
    · show _ ↔ ∀ x ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, _
      simp only [← hφe]
      rw [← hΛ]
      constructor
      · rintro h _ ⟨a, rfl⟩
        obtain ⟨b, hb⟩ := h a
        exact ⟨_, ⟨b, rfl⟩, sub_eq_iff_eq_add'.2 hb⟩
      · intro h a
        obtain ⟨_, ⟨b, rfl⟩, hb⟩ := h _ ⟨a, rfl⟩
        exact ⟨b, sub_eq_iff_eq_add'.1 hb⟩
  have hS : GlobalTheory.EqCovol.IsSelfDualTr (U.X k) := by
    intro x
    have hd := (GlobalTheory.HermModel.rank_integral_selfDual E H _ r _ _ φ0 hξ' hlat).2.2.2 x
    show x ∈ (U.X k).Λ ↔ ∀ y ∈ (U.X k).Λ, ∃ n : ℤ,
      Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm x y) = n
    rw [← hΛ, ← hd]
    constructor
    · rintro h _ ⟨y, rfl⟩
      exact h y
    · exact fun h y => h _ ⟨y, rfl⟩
  have hSY : GlobalTheory.EqCovol.IsSelfDualTr Y := hS
  have orb : ∀ x ∈ (U.X k).dom, ∀ x' ∈ (U.X k).dom,
      (∃ γ ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r, x' = rmul (lact γ x) b) →
      ∃ γ ∈ Y.Γ, ∃ b ∈ Bor Y.Ψ r, x' = rmul (lact γ x) b := by
    intro x hx x' hx'
    rintro ⟨γ, hγ, b, hb, hxx⟩
    obtain ⟨t, hx0, hu, -⟩ := (h4 k k ⟨x, hx⟩ ⟨x', hx'⟩).2 ⟨γ, hγ, b, hb, by rw [← hxx]⟩
    obtain ⟨Pm, hPm, -, hxP, hd, -⟩ := hun k ⟨x, hx⟩
    obtain ⟨Pm', hPm', -, hxP', hd', -⟩ := hun k ⟨x', hx'⟩
    refine fib_single e F hσ hr (ik k) Y (φ k) (hty k)
      (fun _ _ => rfl) (hef k) hmem hneg ⟨x, hx⟩ ⟨x', hx'⟩ Pm Pm' _ _ hPm hPm'
      (hxP.symm.trans (hx0.symm.trans hxP')) hd hd' fun τ i => ?_
    obtain ⟨cf, hcf, htri, hcomb⟩ := hu τ i
    refine ⟨cf, by rw [hcf]; exact Units.isUnit _, htri, ?_⟩
    rw [hxP] at hcomb
    exact hcomb
  refine ⟨hS, fun γ hγ x hx => ?_⟩
  have hxg : lact γ x ∈ (U.X k).dom := Formalism.L2.Pj.dom_lact _ hx ((U.X k).Γ_stab γ hγ)
  obtain ⟨γ', hγ', b', hb', e'⟩ := orb x hx _ hxg
    ⟨γ, hγ, ExtFPf.oneF (U.X k), ExtFPf.oneF_mem (U.X k), (ExtFPf.rmul_oneF (U.X k) _).symm⟩
  obtain ⟨hU', hc⟩ := (GlobalTheory.EqCovol.mem_iff_congr_lcm E H l r Y hL hSY γ').1 hγ'
  exact ⟨γ', hU', hc, b', hb', e'⟩

end GlobalTheory.EqCovol.CongrOrb

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

theorem GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k : U.Comp, GlobalTheory.EqCovol.IsSelfDualTr (U.X k) ∧ ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, ∃ γ' : GL (Fin r) E, IsUStab (U.X k).Gm (U.X k).Λ γ' ∧ (∀ v ∈ (U.X k).Λ, ∃ w ∈ (U.X k).Λ, (γ' : Matrix (Fin r) (Fin r) E).mulVec v - v = l.M' • w) ∧ ∃ b ∈ Bor (U.X k).Ψ r, lact γ x = rmul (lact γ' x) b := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU _ _ hq k
  exact GlobalTheory.EqCovol.CongrOrb.selfDual_and_congr_free E H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hq k
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualAndPrincipalCongruenceOrbitsOfGoodLevelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_and_principalCongruence_orbits_of_goodLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k : U.Comp, GlobalTheory.EqCovol.IsSelfDualTr (U.X k) ∧ ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, ∃ γ' : GL (Fin r) E, IsUStab (U.X k).Gm (U.X k).Λ γ' ∧ (∀ v ∈ (U.X k).Λ, ∃ w ∈ (U.X k).Λ, (γ' : Matrix (Fin r) (Fin r) E).mulVec v - v = l.M' • w) ∧ ∃ b ∈ Bor (U.X k).Ψ r, lact γ x = rmul (lact γ' x) b := by
  first | exact @GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf | exact GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf | (intros; apply GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitriangularChartMemDomainSmallBall
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitriangularChartMemDomainSmallBall
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

namespace GlobalTheory.ChartDomain


open NumberField in
theorem _root_.GlobalTheory.ChartDomain.cpt_mem_dom_of_norm_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x →
    ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom := by
  intro E _ _ _ r X x z hx hz
  have hsmall : (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 := by
    by_cases hr : (r : ℝ) = 0
    · simp [hr]
    · have hpos : 0 < (r : ℝ) ^ 2 := by positivity
      calc (r : ℝ) ^ 2 * ‖z‖ ≤ (r : ℝ) ^ 2 * (1 / (100 * (r : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hz hpos.le
        _ = 1 / 100 := by field_simp
  exact (_root_.GlobalTheory.dmin_rmul_near_one X x hx (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X z) (norm_nonneg z) hsmall
    (fun τ a b => _root_.GlobalTheory.ChartNearOne.nmat_entry_le X z τ a b)).1

end GlobalTheory.ChartDomain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitriangularChartMemDomainSmallBallStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitriangularChart_mem_domain_small_ball : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)), IsOrth X x → ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → cpt X x z ∈ X.dom := by
  first | exact @GlobalTheory.ChartDomain.cpt_mem_dom_of_norm_le | exact GlobalTheory.ChartDomain.cpt_mem_dom_of_norm_le | (intros; apply GlobalTheory.ChartDomain.cpt_mem_dom_of_norm_le <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.ThickBerg

open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

theorem cpt_mem_dom_small : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)), IsOrth X x → ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) →
    cpt X x z ∈ X.dom := GlobalTheory.T.unitriangularChart_mem_domain_small_ball

theorem ball_injects : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r),
    GoodEmb c σ → IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q →
    ∀ (k : U.Comp) (x : Frame (U.X k).Ψ r), IsOrth (U.X k) x →
    100 * (((U.X k).Ψ.card : ℝ) * r) ^ 4 ≤ (l.M' : ℝ) * (U.X k).firstMinimumSq x →
    ∀ γ ∈ (U.X k).Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (nd (U.X k)), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) →
      ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor (U.X k).Ψ r,
      lact γ (cpt (U.X k) x z) = rmul (cpt (U.X k) x z') b → γ = 1 := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hl hp hq k x hx hM γ hγ z z' hz hz' b hb he
  obtain ⟨hsd, horb⟩ := GlobalTheory.T.selfDual_and_principalCongruence_orbits_of_goodLevel E H Dw l Xo c σ r U hσ hU hl hp hq k
  have hwd : cpt (U.X k) x z ∈ (U.X k).dom := cpt_mem_dom_small E r (U.X k) x z hx hz
  obtain ⟨γ', hγ'U, hγ'c, b', hb', he'⟩ := horb γ hγ _ hwd
  have h1 : lact γ' (cpt (U.X k) x z) =
      rmul (cpt (U.X k) x z') (rmul b (ExtFPf.invF (U.X k) b')) := by
    have e1 := congrArg (fun w => rmul w (ExtFPf.invF (U.X k) b')) (he'.symm.trans he)
    simp only [ExtFPf.rmul_assoc, ExtFPf.rmul_invF _ hb', ExtFPf.rmul_oneF] at e1
    exact e1
  have hγ'1 : γ' = 1 := GlobalTheory.T.deep_congruence_element_separates_chart_ball_thick_frame E r (U.X k) l.M' x hsd hx hM γ' hγ'U hγ'c z z' hz hz' _
    (ExtFPf.mul_mem _ hb (ExtFPf.invF_mem _ hb')) h1
  subst hγ'1
  rw [FundSetPf.lact_one] at he'
  exact (U.X k).Γ_free γ hγ _ hwd b' hb' he'

theorem modelWt_shape : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r),
    GoodEmb c σ → IsUnf U → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ (u1 : GlobalTheory.AllWt.Weight Dw) (g : ℝ),
    (∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 → g ≤ (u1 τ a : ℝ) - u1 τ b) → ∀ k : U.Comp,
    (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ (U.X k).p0 →
      g ≤ (modelWt U (wtOf Dw u1 0) k τ a : ℝ) - modelWt U (wtOf Dw u1 0) k τ b) ∧
    (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 →
      g ≤ (modelWt U (wtOf Dw u1 0) k τ b : ℝ) - modelWt U (wtOf Dw u1 0) k τ a) ∧
    (∑ τ, ∑ a, |(modelWt U (wtOf Dw u1 0) k τ a : ℝ)|) = l1 u1 ∧
    (U.X k).Ψ.card = Nat.card (Psi H) := GlobalTheory.T.model_weight_gap_l1_card_bound

theorem orth_transfer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (y : Frame X.Ψ r), y ∈ X.dom → ∃ x, IsOrth X x ∧ X.firstMinimumSq x = X.firstMinimumSq y ∧
    ∀ P ∈ X.SS la, P x ≠ 0 → P y ≠ 0 ∧ X.pnorm la P y = X.pnorm la P x := by
  intro E _ _ _ r X la y hy
  obtain ⟨x, hx, b, hb, rfl⟩ := ReciprocityTheory.ChartRestriction.G.AR.Up.ortho_holds r X y hy
  have hxd := ReciprocityTheory.ChartRestriction.G.AR.Up.KU.orth_dom X hx
  refine ⟨x, hx, (firstMinimumSq_rightBorel X hxd hb).symm, fun P hP hPx =>
    ⟨?_, FrameDegreeData.pnorm_rmul X la P hP.1.1.2.1 x hxd b hb⟩⟩
  rw [hP.1.1.2.1 x hxd b hb]
  refine mul_ne_zero ?_ hPx
  unfold bchar
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  have h := (hb τ).1
  rw [Matrix.det_of_upperTriangular ((ExtFPf.upper_iff X b τ).mp (hb τ).2)] at h
  exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)

theorem nums (a l C0 PP T D b uE : ℝ) (ha : 1 ≤ a) (hl : 10 ≤ l) (hlC : C0 ≤ l) (hPP : (a * l) ^ 12 ≤ PP)
    (hT : (a * l) ^ 24 ≤ T) (hD : 1 ≤ D) (hrows : PP * T * D ^ 2 * l ≤ b) (hbu : b ≤ uE) :
    T * a ^ 8 ≤ uE ∧ C0 * a ^ 8 ≤ T ∧ 100 * a ^ 4 ≤ b := by
  have h1 : 1 ≤ a * l := by nlinarith
  have hal8 : a ^ 8 ≤ (a * l) ^ 12 :=
    calc a ^ 8 ≤ (a * l) ^ 8 := pow_le_pow_left₀ (by linarith) (by nlinarith) 8
      _ ≤ (a * l) ^ 12 := pow_le_pow_right₀ h1 (by norm_num)
  have hPP' : a ^ 8 ≤ PP := hal8.trans hPP
  have hT1 : 1 ≤ T := (one_le_pow₀ h1).trans hT
  have hPP0 : 0 ≤ PP := (by positivity : (0 : ℝ) ≤ a ^ 8).trans hPP'
  have hDl : 1 ≤ D ^ 2 * l := by nlinarith [one_le_pow₀ (n := 2) hD]
  have hTPP : T * PP ≤ b := by
    have h2 : T * PP ≤ PP * T * D ^ 2 * l := by
      have h3 : 0 ≤ PP * T := mul_nonneg hPP0 (by linarith)
      nlinarith
    linarith
  refine ⟨?_, ?_, ?_⟩
  · calc T * a ^ 8 ≤ T * PP := mul_le_mul_of_nonneg_left hPP' (by linarith)
      _ ≤ uE := hTPP.trans hbu
  · have h4 : a ^ 8 * l ≤ (a * l) ^ 24 := by
      rw [mul_pow]
      exact mul_le_mul (pow_le_pow_right₀ ha (by norm_num)) (le_self_pow₀ (by linarith) (by norm_num))
        (by linarith) (by positivity)
    have h5 : C0 * a ^ 8 ≤ l * a ^ 8 := mul_le_mul_of_nonneg_right hlC (by positivity)
    linarith
  · have h12 : 100 * a ^ 4 ≤ (a * l) ^ 12 := by
      rw [mul_pow]
      have h6 : (100 : ℝ) ≤ l ^ 12 :=
        calc (100 : ℝ) ≤ 10 ^ 12 := by norm_num
          _ ≤ l ^ 12 := pow_le_pow_left₀ (by norm_num) hl 12
      have h7 : a ^ 4 ≤ a ^ 12 := pow_le_pow_right₀ ha (by norm_num)
      have h8 : 0 ≤ a ^ 4 := by positivity
      nlinarith
    have h9 : PP ≤ T * PP := le_mul_of_one_le_left hPP0 hT1
    linarith

end GlobalTheory.ThickBerg
