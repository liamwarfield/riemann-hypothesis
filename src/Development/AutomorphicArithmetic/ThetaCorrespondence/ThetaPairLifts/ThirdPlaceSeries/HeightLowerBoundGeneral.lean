module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarryingSectionOrders
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPointOfWeightNumerical
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HeightAddLogNonneg
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TwistedFlatBundleRanks
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsConstantTwistOfThinDivisor
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PageSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DividedWeightStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumPtOfSize
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadingStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSectionBoundedByBergmanKernel
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BergmanKernelThinPartEstimate
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspFormBoundedOnFrames
set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section
namespace GlobalTheory.ThinTwist
theorem twist_thin_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → ∀ f ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (GlobalTheory.RefSum.GOf p i u1), ∃ g ∈ cuspOn Y.U Z (wtOf (dat p i) u1 0), ∃ K : ℝ, 0 < K ∧ ∀ z : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r, z ∈ framesOn (Y.U σ) Z → ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) z = K * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) z := by
  intro hP _ _ hS hFD
  have R := _root_.GlobalTheory.T.weight_conditions_at_index'
  have F := _root_.GlobalTheory.T.abs_flat_c1_add_logOm_le_and_logSum_badPrimes_le hFD
  have Q := _root_.GlobalTheory.RefSum.QuoShape.quo_shape_dom_lastPos_weight_eq hS
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine (R.and (F.and Q)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩, ⟨C3, h3, e3⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and (e2.and e3)
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hA, hB, hC⟩ := hx0 x hx hle ι p hp
  obtain ⟨hL, -, -, -, hj, -⟩ := hA i hi
  have hFl := (hB i hi Y hY).2.2.1
  intro u1 hq Z σ hσ _ _ f hf
  obtain ⟨-, -, -, -, -, -, -, -, hG⟩ := hC i hi u1 hq
  rw [hG] at hf ⊢
  exact _root_.GlobalTheory.ThinTwist.exists_constant_twist_of_thin_divisor hP p.T _ Y _ _ hL hj hY.1 hFl u1 _ _ Z σ hσ hf
end GlobalTheory.ThinTwist
theorem _root_.GlobalTheory.T.cusp_form_bounded_on_frames_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → ∀ f ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (GlobalTheory.RefSum.GOf p i u1), ∃ g ∈ cuspOn Y.U Z (wtOf (dat p i) u1 0), ∃ K : ℝ, 0 < K ∧ ∀ z : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r, z ∈ framesOn (Y.U σ) Z → ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) z = K * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) z := _root_.GlobalTheory.ThinTwist.twist_thin_alt_alt
end
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CardMulSuccLeTwoMulNcolCopy
set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace UpperTheory.Dv.Thin
theorem covers_and_of_covers_of_imp_alt {Q₁ Q₂ Q₃ : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
    (i : Fin (Fm.D x ι).R.m) (_Y : Cov p i) (PP C : ℝ), Prop}
    (h₁ : _root_.GlobalTheory.CovTop.CoversCondition Q₁) (h₂ : _root_.GlobalTheory.CovTop.CoversCondition Q₂)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (Y : Cov p i) (PP C C' : ℝ),
      Q₁ Fm x hx ι p i Y PP C → Q₂ Fm x hx ι p i Y PP C' → (i : ℕ) + 1 < (Fm.D x ι).R.m → GoodCov p i Y →
        Q₃ Fm x hx ι p i Y PP C) : _root_.GlobalTheory.CovTop.CoversCondition Q₃ := by
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine (h₁.and h₂).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨C, hC, h1⟩, ⟨C', _, h2⟩⟩ := hh
  obtain ⟨a, h3⟩ := h1.and h2
  exact ⟨C, hC, a, fun x hx hle ι p hp i hi Y hY =>
    h Fm x hx ι p i Y _ C C' ((h3 x hx hle ι p hp).1 i hi Y hY) ((h3 x hx hle ι p hp).2 i hi Y hY) hi hY⟩
private theorem card_mul_succ_le_two_mul_ncol_copy {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) :
    Fintype.card (Psi H) * (Dw.p + Dw.q) * (Dw.p + Dw.q + 1) ≤ 2 * GlobalTheory.RefSum.nCol Dw := by
  refine le_trans ?_ (Nat.mul_le_mul_left 2 GlobalTheory.RefSum.sum_le_nCol)
  have h1 : ∀ m : ℕ, ∑ i : Fin m, 2 * (i.val + 1) = m * (m + 1) := fun m => by
    induction m with
    | zero => simp
    | succ m ih => rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last, ih]; ring
  rw [Fintype.sum_sigma]
  simp only [h1]
  rw [GlobalTheory.RawThetaSup.sum_emb_eq H, Finset.mul_sum, mul_assoc, ← Finset.card_univ, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [Datum.mult, if_pos τ.2, Datum.mult, if_neg (conj_not_mem τ)]
  nlinarith [sq_nonneg ((Dw.p : ℤ) - Dw.q)]
private theorem one_le_dimension_function_copy {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (hp : 1 ≤ Dw.p) (hne : 0 < Fintype.card (Psi H)) {a : (E →+* ℂ) × ℕ → ℕ} (h : LastPos Dw a) :
    1 ≤ Formalism.L2.Pj.DF Dw a := by
  obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hne
  have hm : 0 < Dw.mult τ.1 := by rw [Datum.mult, if_pos τ.2]; exact hp
  refine (h τ.1 τ.2 hm).trans_le ?_
  unfold Formalism.L2.Pj.DF
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ : E →+* ℂ => ∑ i : Fin (Dw.mult τ), a (τ, i))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ.1))
  exact Finset.single_le_sum (f := fun i : Fin (Dw.mult τ.1) => a (τ.1, i)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ ⟨Dw.mult τ.1 - 1, by omega⟩)
private theorem frn_le_pow_of_bounds_copy {f r n t : ℝ} (ht : 11 ≤ t) (hf0 : 0 ≤ f) (hr0 : 0 ≤ r) (hf : f ≤ t) (hr : r ≤ t)
    (hn : n ≤ 2 * r * (f * r) + 8 * (f * r) + 8) : f * r * n ≤ t ^ 150 := by
  have h1 : n ≤ 2 * t * (t * t) + 8 * (t * t) + 8 := hn.trans (by gcongr)
  have h2 : n ≤ t ^ 4 := by
    have : 11 * t ^ 3 ≤ t ^ 4 := by rw [pow_succ' t 3]; gcongr
    have : 11 * t ^ 2 ≤ t ^ 3 := by rw [pow_succ' t 2]; gcongr
    nlinarith
  calc f * r * n ≤ f * r * t ^ 4 := by gcongr
    _ ≤ t * t * t ^ 4 := by gcongr
    _ = t ^ 6 := by ring
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
set_option maxHeartbeats 1000000 in
theorem cover_dimension_size_bounds_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → (Dom (GlobalTheory.RefSum.aOf p i u1) (GlobalTheory.RefSum.nCol (dat p i)) ∧ LastPos (dat p i) (GlobalTheory.RefSum.aOf p i u1) ∧ Nonempty (ErrX (Fm.D x ι))) ∧ 1000 ≤ (Fm.L x ι).sc.b ∧ (Fm.D x ι).R.r ≤ GlobalTheory.RefSum.nCol (dat p i) ∧ (Fm.D x ι).R.f * (Fm.D x ι).R.r * ((Fm.D x ι).R.r + 1) ≤ 2 * GlobalTheory.RefSum.nCol (dat p i) ∧ ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * GlobalTheory.RefSum.nCol (dat p i) ≤ (Fm.L x ι).sc.b ∧ (Fm.D x ι).host.rdE ^ 7 ≤ (Fm.L x ι).sc.b ∧ (Fm.L x ι).sc.b ^ 16 ≤ (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) ∧ (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) ≤ (Fm.L x ι).sc.b ^ 70 ∧ 1 ≤ Formalism.L2.Pj.DF (dat p i) (GlobalTheory.RefSum.aOf p i u1) ∧ ((Formalism.L2.Pj.DF (dat p i) (GlobalTheory.RefSum.aOf p i u1) : ℕ) : ℝ) ≤ (Fm.L x ι).sc.b ^ 2 ∧ (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) * (Fm.L x ι).sc.b ≤ (Y.d.l₂.M : ℝ) := by
  intro hS
  refine (Formalism.MainNotions.Closed.and (Formalism.MainNotions.Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 6) _root_.GlobalTheory.CovTop.WtShape.wtN_z)
    (_root_.GlobalTheory.RefSum.QuoShape.quo_shape_dom_lastPos_weight_eq hS)).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨⟨A, -, h1⟩, ⟨C2, -, h2⟩⟩, ⟨C3, -, h3⟩⟩ := hh
  obtain ⟨a, ha⟩ := h1.and (h2.and h3)
  refine ⟨0, le_rfl, a, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  have hN : HostNum (Fm.D x ι) (Fm.L x ι) (Fm.parT x hx ι).PP A 6 := (ha x hx hle ι p hp).1 i
  have hW : WtNum p i (Fm.parT x hx ι).PP := (ha x hx hle ι p hp).2.1 i
  obtain ⟨q1, -, q3, q4, q5, q6, q7, q8, -⟩ := (ha x hx hle ι p hp).2.2 i hi u1 hu
  have S := Fm.sizes x hx ι
  obtain ⟨-, -, -, -, -, sC, sQD, -, -, -, -, -, -, -, -, -, -, -, -, -, sG, -⟩ := S
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := sQD
  have a1 := (Fm.D x ι).R.two_le_m
  have a2 := (Fm.D x ι).R.m_add_three_le_k
  have a3 : (Fm.D x ι).R.r + 5 ≤ (Fm.D x ι).R.t := (Fm.D x ι).R.rank_add_five_le
  have a4 : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.k := (Fm.D x ι).R.f_le_k
  have a5 : (Fm.D x ι).R.k ≤ (Fm.D x ι).R.r ∧ (Fm.D x ι).R.m ≤ (Fm.D x ι).R.r ∧ 6 ≤ (Fm.D x ι).R.r := by
    unfold Formalism.BasicNotions.Ranks.r; omega
  have hf8 := hN.f8
  have hL10 : 10 ≤ (Fm.L x ι).sc.L := hN.big.2.1
  have hfR : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
  have hrR : (6 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast a5.2.2
  have ht : (11 : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : 11 ≤ (Fm.D x ι).R.t)
  have hft : ((Fm.D x ι).R.f : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.t)
  have hrt : ((Fm.D x ι).R.r : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : (Fm.D x ι).R.r ≤ (Fm.D x ι).R.t)
  have hb : 1000 ≤ (Fm.L x ι).sc.b := by
    have e1 : Real.exp 10 ≤ (Fm.L x ι).sc.b := Real.exp_le_exp.2 hL10
    have e2 : (2 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 := by gcongr; linarith [Real.add_one_le_exp 1]
    rw [← Real.exp_nat_mul] at e2
    norm_num at e2
    linarith
  have hb1 : 1 ≤ (Fm.L x ι).sc.b := by linarith
  have hc : (Fm.D x ι).host.rdE ≤ szCond (Fm.L x ι) := by
    unfold szCond
    exact UpperTheory.Ram.Rd.rdE_le_cond _
  have hc1 : (1 : ℝ) ≤ szCond (Fm.L x ι) := h1.trans hc
  have hsb : Real.sqrt (Fm.L x ι).sc.b ≤ (Fm.L x ι).sc.b :=
    Real.sqrt_le_iff.2 ⟨by linarith, le_self_pow₀ hb1 (by norm_num)⟩
  have hrdb : (Fm.D x ι).host.rdE ^ 7 ≤ (Fm.L x ι).sc.b := by
    have e1 : (Fm.D x ι).host.rdE ^ 7 ≤ szCond (Fm.L x ι) ^ 36 * ((Fm.D x ι).R.t : ℝ) ^ 150 :=
      (pow_le_pow_left₀ (by linarith) hc 7).trans ((pow_le_pow_right₀ hc1 (by norm_num)).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith))))
    exact (e1.trans sC).trans hsb
  have htb : ((Fm.D x ι).R.t : ℝ) ^ 150 ≤ (Fm.L x ι).sc.b :=
    ((le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc1)).trans sC).trans hsb
  have hcard : Fintype.card (Psi p.T.Q.H) = (Fm.D x ι).R.f := Nat.card_eq_fintype_card.symm.trans hW.card
  have hcol := card_mul_succ_le_two_mul_ncol_copy (dat p i)
  rw [hcard, q3] at hcol
  have h2r := GlobalTheory.RefSum.NumPt.two_mul_rank_le_nCol (dat p i)
  rw [q3] at h2r
  have hnle : (GlobalTheory.RefSum.nCol (dat p i) : ℝ) ≤ 2 * (Fm.D x ι).R.r * ((Fm.D x ι).R.f * (Fm.D x ι).R.r) +
      8 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r) + 8 := by exact_mod_cast GlobalTheory.LiftGaps.nCol_le p i _ _ _ hW hN
  have hfrn : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * GlobalTheory.RefSum.nCol (dat p i) ≤ (Fm.L x ι).sc.b :=
    (frn_le_pow_of_bounds_copy ht (by positivity) (by positivity) hft hrt hnle).trans htb
  have hk : (1 : ℝ) ≤ (Fm.D x ι).R.k := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.k)
  have hg : ∀ k, (Fm.L x ι).sc.b ^ 8 ≤ ((Fm.D x ι).host.g k : ℝ) := fun k =>
    (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_left (by linarith) hk) 8).trans (sG k k).1
  have hg' : ∀ k, ((Fm.D x ι).host.g k : ℝ) ≤ (Fm.L x ι).sc.b ^ 35 := fun k => by
    have h0 : (0 : ℝ) < (Fm.D x ι).host.g k := by exact_mod_cast ((Fm.D x ι).host.g_prime k).pos
    unfold Formalism.BasicNotions.Scale.b
    rw [← Real.exp_nat_mul, ← Real.log_le_iff_le_exp h0]
    push_cast
    linarith only [hN.logg k, hL10]
  have hev : Even (GlobalTheory.RefSum.nCol (dat p i)) := q7.2
  have hDF := (GlobalTheory.RefSum.thA_dominant_lastPos_degree _ _ (dat p i) u1 (GlobalTheory.RefSum.nCol (dat p i)) _ q1 hev q4 q5 q6).2.2.2.2
  rw [hN.deg, q3, Nat.mul_div_cancel_left _ two_pos] at hDF
  refine ⟨⟨q7, q8, ⟨(Fm.ex x hx ι).errX⟩⟩, hb, by omega, hcol, hfrn, hrdb, ?_, ?_,
    one_le_dimension_function_copy _ q1 (by rw [hcard]; omega) q8, hDF.trans ?_, GlobalTheory.ThetaSizeBounds.level_ge p i Y hY (by linarith)⟩
  · push_cast
    rw [show 16 = 8 + 8 from rfl, pow_add]
    exact mul_le_mul (hg 0) (hg 1) (by positivity) (by positivity)
  · push_cast
    rw [show 70 = 35 + 35 from rfl, pow_add]
    exact mul_le_mul (hg' 0) (hg' 1) (by positivity) (by positivity)
  · have h5 : (5 : ℝ) ≤ GlobalTheory.RefSum.nCol (dat p i) := by exact_mod_cast (by omega : 5 ≤ GlobalTheory.RefSum.nCol (dat p i))
    have h6 : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * 5 ≤ (Fm.L x ι).sc.b :=
      (mul_le_mul_of_nonneg_left h5 (by positivity)).trans hfrn
    calc ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (2 * (2 * (Fm.L x ι).sc.b) + 1)
        ≤ ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (5 * (Fm.L x ι).sc.b) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * 5 * (Fm.L x ι).sc.b := by ring
      _ ≤ (Fm.L x ι).sc.b * (Fm.L x ι).sc.b := mul_le_mul_of_nonneg_right h6 (by linarith)
      _ = _ := by ring
set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.thin_divisor_pivot_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 < (Fm.L x ι).sc.b → ∃ f ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (GlobalTheory.RefSum.GOf p i u1), rdU (Y.U σ) f y.1 y.2.1 ≠ 0 ∧ ∀ z : FPt (Y.U σ).X, (⟨z.1, z.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → Real.exp (-(2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) / (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E ^ 2 * ((Y.U σ).X y.1).la1 y.2.1 ^ 2) / 1250)) * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) ⟨z.1, z.2.1⟩ ≤ ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) ⟨y.1, y.2.1⟩ := by
  intro _ _ _ hS _
  refine _root_.UpperTheory.Dv.Thin.covers_and_of_covers_of_imp_alt (_root_.UpperTheory.Dv.Thin.cover_dimension_size_bounds_alt hS) (_root_.GlobalTheory.ThetaSizeBounds.run_params_alt hS) ?_
  intro eps Fm x hx ι p i Y PP C C' hA hB hi hY u1 hu Z σ hσ y hy hM
  obtain ⟨⟨hD, hLP, ⟨EX⟩⟩, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := hA u1 hu
  obtain ⟨r1, -, -, r4⟩ := hB
  obtain ⟨hrun, -⟩ := r4 _ s8 s9
  have hj : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨by omega, hi.le⟩
  have hl : p.T.Q.l.M = (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 := p.fw.laws.toLawsM.pins.2.1.1
  obtain ⟨⟨α, hα1, hα2⟩, -⟩ := GlobalTheory.HalfGen.half_principal_and_split _ p.T.toCore p.fw.laws.toLawsM EX
  obtain ⟨φ, hφ, hg⟩ := cover_transport _ p.T _ Y _ _ p.fw.laws hj hY.1 _ _ hD σ hσ
  have hd := hφ ⟨y.1, y.2.1⟩ y.2.2
  have hσ' : GoodEmb p.T.Q.c (Y.resEmb σ) := Y.good_resEmb hσ
  have hla : ((p.T.U ((i : ℕ) + 1) (Y.resEmb σ)).X (φ ⟨y.1, y.2.1⟩).1).la1 (φ ⟨y.1, y.2.1⟩).2 =
      ((Y.U σ).X y.1).la1 y.2.1 := congrArg Real.sqrt hd.2
  have h0 : 0 ≤ ((Y.U σ).X y.1).firstMinimumSq y.2.1 := ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_nonneg _ y.2.2
  have hs1 : (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 ≤ 1 := by
    have h1 := (mul_le_mul_of_nonneg_right s10 h0).trans hM.le
    rw [mul_right_comm] at h1
    exact le_of_mul_le_mul_right (h1.trans_eq (one_mul _).symm) (by linarith only [s1])
  obtain ⟨f, hf, hf0, hfz⟩ := core_ratio (GlobalTheory.LevGeo.laws_core _ p.T _ p.fw.laws hj) α hα1 hα2 hD hLP s1 s2 s3 s4 s5
    (by rw [hl]; exact s6) (by rw [hl]; exact s7) s9 (by rw [hl]; exact hrun) r1 hσ' (φ ⟨y.1, y.2.1⟩).1
    (φ ⟨y.1, y.2.1⟩).2 hd.1 (by rw [hl, hd.2]; exact hs1)
  obtain ⟨g, hg', hgy⟩ := hg f hf
  refine ⟨g, hg', (hgy ⟨y.1, y.2.1⟩ y.2.2).2.mpr hf0, fun z hz => ?_⟩
  rw [(hgy ⟨z.1, z.2.1⟩ z.2.2).1, (hgy ⟨y.1, y.2.1⟩ y.2.2).1, ← hla]
  exact hfz ⟨(φ ⟨z.1, z.2.1⟩).1, (φ ⟨z.1, z.2.1⟩).2, (hφ ⟨z.1, z.2.1⟩ z.2.2).1⟩
end UpperTheory.Dv.Thin
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.ThinBerg
open MeasureTheory
open scoped ENNReal
end GlobalTheory.ThinBerg
namespace GlobalTheory.ThinBerg
open MeasureTheory
theorem bergman_kernel_bound_thin_part_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 < (Fm.L x ι).sc.b → ENNReal.ofReal (Real.exp (-(2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) / (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E ^ 2 * ((Y.U σ).X y.1).la1 y.2.1 ^ 2) / 625))) ≤ bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  intro h1 h2 h3 h4 h5
  have hT := _root_.GlobalTheory.T.thin_divisor_pivot_bound_alt h1 h2 h3 h4 h5
  have hW := _root_.GlobalTheory.T.cusp_form_bounded_on_frames_alt_alt h1 h2 h3 h4 h5
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at hT hW ⊢
  refine Closed.imp (Closed.and hT hW) ?_
  rintro eps Fm CH - ⟨⟨C1, hC1, a1, H1⟩, ⟨C2, hC2, a2, H2⟩⟩
  refine ⟨C1, hC1, max a1 a2, fun x hx hle ι p hp i hi Y hY u1 hu Z σ hσ y hyZ hth => ?_⟩
  obtain ⟨f, hf, hfy, hfb⟩ := H1 x hx ((le_max_left _ _).trans hle) ι p hp i hi Y hY u1 hu Z σ hσ y hyZ hth
  obtain ⟨g, hg, K, hK, hgK⟩ := H2 x hx ((le_max_right _ _).trans hle) ι p hp i hi Y hY u1 hu Z σ hσ y hyZ f hf
  obtain ⟨th, hr, -, hDU⟩ := hY.1.dictU σ hσ
  have hd := Formalism.L2.Pj.dict_dom_of hDU
  clear H1 H2
  have he : ∀ φ : ℝ, Real.exp (-(φ / 625)) = Real.exp (-(φ / 1250)) ^ 2 := fun φ => by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [he]
  have hgW : g ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtOf (dat p i) u1 0) := cuspOn_le _ _ _ hg
  have hgS : g ∈ suppOn Z := (Submodule.mem_inf.1 hg).2
  have hP := (mem_cuspW.1 hgW).2 σ hσ
  have hfy' : 0 < ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) ⟨y.1, y.2.1⟩ :=
    pnorm_pos' _ _ y.2.2 hfy
  have hgy : ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) ⟨y.1, y.2.1⟩ =
      K * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) ⟨y.1, y.2.1⟩ := hgK _ hyZ
  refine le_bergOn_of_ratio (Y.U σ) _ (Y.dict σ) hd Z _ y _ hP (Real.exp_pos _) ?_ ?_
  · rw [hgy]; exact mul_pos hK hfy'
  · intro z
    by_cases hz : (⟨z.1, z.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z
    · rw [hgK _ hz, hgy]
      have := hfb z hz
      nlinarith
    · have h0 : rdU (Y.U σ) g z.1 z.2.1 = 0 := rdU_eq_zero (Y.U σ) hgS hz
      have hz0 : ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) ⟨z.1, z.2.1⟩ = 0 := by
        simp only [ptN, Data.pnorm, h0, norm_zero, zero_mul]
      rw [hz0, mul_zero]
      exact ptN_nonneg _ _ _
end GlobalTheory.ThinBerg
end
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bergman_kernel_thin_part_estimate_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 < (Fm.L x ι).sc.b → ENNReal.ofReal (Real.exp (-(2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) / (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E ^ 2 * ((Y.U σ).X y.1).la1 y.2.1 ^ 2) / 625))) ≤ bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  first | exact @_root_.GlobalTheory.ThinBerg.bergman_kernel_bound_thin_part_alt | exact _root_.GlobalTheory.ThinBerg.bergman_kernel_bound_thin_part_alt | (intros; apply _root_.GlobalTheory.ThinBerg.bergman_kernel_bound_thin_part_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BergmanKernelThickPartEstimate
set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.ThickBerg
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory
set_option maxHeartbeats 4000000 in
theorem exp_neg_B_le_bergOn_of_mem_framesOn : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ B : ℝ, 0 ≤ B ∧ lenT p i PP * B ≤ C * unitE p ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Fm.L x ι).sc.b ≤ (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 → ENNReal.ofReal (Real.exp (-B)) ≤ bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  intro _ _ _ hS _
  obtain ⟨C0, hC0, hpeak⟩ := GlobalTheory.T.exists_cusp_form_peak_at_injective_chart_frame
  have hnum := _root_.GlobalTheory.T.torus_length_lower_bound_quotient' hS
  refine (((hnum.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt (max 10 C0))).and _root_.GlobalTheory.CovTop.WtShape.wtN_z).and hS).imp
    fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨C2, hC2, hN⟩, ⟨A, -, hH⟩⟩, ⟨C3, -, hW⟩⟩, ⟨C4, -, hSz⟩⟩ := h
  refine ⟨C0 * (C2 + 1), by positivity, ?_⟩
  obtain ⟨x0, hall⟩ := ((hN.and hH).and hW).and hSz
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY u1 hu1 => ?_⟩
  obtain ⟨⟨⟨hN, hH⟩, hW⟩, hSz⟩ := hall x hx hle ι p hp
  obtain ⟨hZ24, hu⟩ := hN i hi
  obtain ⟨hTl1, hgap⟩ := hu u1 hu1
  have hHi := hH i
  have hWi := hW i
  have hSi := hSz i
  have hsig := hWi.sig
  have hm3 := (Fm.D x ι).R.m_add_three_le_k
  simp only [Ranks.sigW] at hsig
  have hp1 : 1 ≤ (dat p i).p := by omega
  have hq1 : 1 ≤ (dat p i).q := by omega
  have hf1 : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by have := hHi.f8; omega : 1 ≤ (Fm.D x ι).R.f)
  have hr1 : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r)
  have hD1 : (1 : ℝ) ≤ (dimFlag (dat p i) : ℝ) := by
    rw [hWi.dim]
    have h2 : 1 ≤ (Fm.D x ι).R.r.choose 2 := Nat.choose_pos (by omega)
    have h8 := hHi.f8
    exact_mod_cast (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))
  have hzb : zBase (Fm.L x ι) = ((Fm.D x ι).R.f * (Fm.D x ι).R.r) * (Fm.L x ι).sc.L := rfl
  obtain ⟨hA8, hC08, h100⟩ := nums ((Fm.D x ι).R.f * (Fm.D x ι).R.r) (Fm.L x ι).sc.L C0 _ _ _ _ _
    (one_le_mul_of_one_le_of_one_le hf1 hr1) hHi.big.2.1 ((le_max_right _ _).trans hHi.big.1)
    (hzb ▸ hHi.ppLow) (hzb ▸ hZ24) hD1 hWi.what₂.2 hSi.2.1
  have hl10 : 0 ≤ l1 u1 := by unfold l1; positivity
  refine ⟨C0 * (l1 u1 + ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ^ 8), by positivity, ?_, fun Z σ hσ y hy hb => ?_⟩
  · have e : (lenT p i (Fm.parT x hx ι).PP : ℝ) * (C0 * (l1 u1 + ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ^ 8)) =
        C0 * ((lenT p i (Fm.parT x hx ι).PP : ℝ) * l1 u1 + (lenT p i (Fm.parT x hx ι).PP : ℝ) * ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ^ 8) := by ring
    rw [e, mul_add C0 C2 1, mul_one]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hTl1 hA8) hC0]
  · have hL := GlobalTheory.LawsDeep.levLaws _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, i.2⟩ hY.1
    have hg0 : ∀ q : ℕ, q.Prime → p.T.Q.l.GoodAt q :=
      Formalism.L2.Pj.goodAt_of_two_primes p.fw.laws.pins.2.1.1 ((Fm.D x ι).host.g_prime 0) ((Fm.D x ι).host.g_prime 1)
        (Fm.D x ι).host.g_ne
    have hg : ∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hY.1.lev.1.2.1 hg0
    have hU := hL.unf σ hσ
    have hM' : Y.d.l₂.M' = Y.d.l₂.M := by rw [Level.M', hY.1.lev.2, Nat.lcm_one_right]
    refine GlobalTheory.T.cuspForm_lower_bound_bergmanFunction_on_component (Fm.D x ι) ((i : ℕ) + 1) _ _ _ Y.d.Xo₂ Y.d.c₂ Y.U Y.dict hL σ hσ _ Z y hy _
      (fun x0 FF hx0 hFF => ?_)
    obtain ⟨x1, hx1, hla, htr⟩ := orth_transfer _ _ ((Y.U σ).X y.1)
      (modelWt (Y.U σ) (wtOf (dat p i) u1 0) y.1) y.2.1 y.2.2
    obtain ⟨hg1, hg2, hl1, hcard⟩ := modelWt_shape _ _ _ _ _ _ σ _ (Y.U σ) hσ hU hp1 hq1 u1
      (lenT p i (Fm.parT x hx ι).PP) (fun τ a b hab => by exact_mod_cast hgap τ a b hab) y.1
    have hcf : (((Y.U σ).X y.1).Ψ.card : ℝ) = (Fm.D x ι).R.f := by
      rw [hcard]; exact_mod_cast hWi.card
    have hball := ball_injects _ _ _ _ _ _ σ _ (Y.U σ) hσ hU hg hp1 hq1 y.1 x1 hx1 (by
      rw [hcf, hM', hla]; exact h100.trans hb)
    have hp0 := (hU.2.1 y.1).1
    have hr := hU.1
    obtain ⟨P, hP, hPx, hle⟩ := hpeak _ _ ((Y.U σ).X y.1) (modelWt (Y.U σ) (wtOf (dat p i) u1 0) y.1) x1
      (by rw [hp0]; exact hq1) (by rw [hp0, hr]; exact Nat.lt_add_of_pos_left hp1) hx1
      (fun τ a b hab hb0 => by rw [hcf]; exact hC08.trans (hg1 τ a b hab hb0))
      (fun τ a b ha hb' => by rw [hcf]; exact hC08.trans (hg2 τ a b ha hb')) hball x0 FF hx0 hFF
    obtain ⟨hPy, hpn⟩ := htr P hP hPx
    refine ⟨P, hP, hPy, ?_⟩
    rw [hpn]
    rw [hl1, hcf] at hle
    exact hle
end GlobalTheory.ThickBerg
end
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_neg_B_le_bergOn_of_la1sq_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ B : ℝ, 0 ≤ B ∧ lenT p i PP * B ≤ C * unitE p ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Fm.L x ι).sc.b ≤ (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 → ENNReal.ofReal (Real.exp (-B)) ≤ bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  first | exact @_root_.GlobalTheory.ThickBerg.exp_neg_B_le_bergOn_of_mem_framesOn | exact _root_.GlobalTheory.ThickBerg.exp_neg_B_le_bergOn_of_mem_framesOn | (intros; apply _root_.GlobalTheory.ThickBerg.exp_neg_B_le_bergOn_of_mem_framesOn <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovHt.KeySection
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.ThetaConst GlobalTheory.EtaForm
section Free
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
end Free
theorem theta_function_le_bergman_kernel_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C =>
    ∀ u1, Quo p i PP u1 → ∃ β : ℝ, 0 ≤ β ∧ lenT p i PP * β ≤ C * unitE p ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂)
      (xs : Fin ((dat p i).p + (dat p i).q) → LatMod (dat p i) (5 ^ 4)) (f : Rul Y.d.Xo₂ Y.d.c₂),
      Submodule.span (𝓞 (Fm.D x ι).host.E) (Set.range xs) = ⊤ →
      IsTauRule Y.d.Xo₂ Y.d.c₂ 5 (fun _ : Unit => 1) (fun _ => xs) f → ∀ σ, GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X,
      (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z →
        homN (Y.U σ) (xiR (Fm.D x ι)) (wtZ 0 (2 * ((dat p i).p + (dat p i).q))) (f ^ 2) ⟨y.1, y.2.1⟩ ≤ Real.exp β ∧
        ENNReal.ofReal (homN (Y.U σ) (xiR (Fm.D x ι)) (wtZ 0 (2 * ((dat p i).p + (dat p i).q))) (f ^ 2) ⟨y.1, y.2.1⟩) ^ 3 ≤
          ENNReal.ofReal (Real.exp β) *
            bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  intro hP hH hD hS hF
  refine Closed.imp (Closed.and (_root_.GlobalTheory.T.eta_bound_length_unit_alt hS) (Closed.and (_root_.GlobalTheory.T.bergman_kernel_thin_part_estimate_alt hP hH hD hS hF) (_root_.GlobalTheory.T.exp_neg_B_le_bergOn_of_la1sq_bound hP hH hD hS hF))) ?_
  rintro eps Fm CH - ⟨⟨C₁, c₁, h₁⟩, ⟨_, -, h₂⟩, ⟨C₃, c₃, h₃⟩⟩
  obtain ⟨x0, h⟩ := h₁.and (h₂.and h₃)
  refine ⟨C₁ + C₃, add_nonneg c₁ c₃, x0, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := h x hx hle ι p hp
  obtain ⟨a1, a2, a3, a4⟩ := h₁ i hi Y hY
  obtain ⟨B, b1, b2, b3⟩ := h₃ i hi Y hY u1 hu
  have hb : 1 ≤ (Fm.L x ι).sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [(Fm.L x ι).sc.one_lt_alt]) _)
  obtain ⟨r1, r2⟩ := a4 1 le_rfl (by push_cast; exact one_le_pow₀ hb)
  refine ⟨_ + B, add_nonneg a2 b1, by rw [mul_add, add_mul]; exact add_le_add a3 b2, fun Z xs f hs hf σ hσ y hy => ?_⟩
  have d := GlobalTheory.T.normSq_thetaConstant_spanning_classes_le_exp _ _ _ _ _ _ σ _ (Y.U σ) (xiR (Fm.D x ι)) hσ (hY.1.unf σ hσ) 5 (by decide) (by norm_num) xs f hs hf
    _ _ _ _ r1 (Or.inr a1) ⟨y.1, y.2.1⟩ y.2.2
  have e2 := h₂ i hi Y hY u1 hu Z σ hσ y hy
  have e3 := b3 Z σ hσ y hy
  have e4 := r2 (((Y.U σ).X y.1).firstMinimumSq y.2.1)
  have ha := homN_nonneg (Y.U σ) (xiR (Fm.D x ι)) (wtZ 0 (2 * ((dat p i).p + (dat p i).q))) (f ^ 2) ⟨y.1, y.2.1⟩
  unfold ReciprocityTheory.ChartRestriction.G.I2.phiFD Data.la1 at d
  unfold Data.la1 at e2
  dsimp only at d
  generalize homN (Y.U σ) (xiR (Fm.D x ι)) (wtZ 0 (2 * ((dat p i).p + (dat p i).q))) (f ^ 2) ⟨y.1, y.2.1⟩ = a at d ha ⊢
  generalize bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y = G at e2 e3 ⊢
  generalize GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 = P
    at d a2 ⊢
  generalize hφ : 2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) /
    (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E ^ 2 * Real.sqrt (((Y.U σ).X y.1).firstMinimumSq y.2.1) ^ 2) = φ at d e2
  have φ0 : 0 ≤ φ := by rw [← hφ]; positivity
  have key : ∀ s t : ℝ, a ≤ Real.exp s → 3 * s ≤ P + B + t → ENNReal.ofReal (Real.exp t) ≤ G →
      ENNReal.ofReal a ^ 3 ≤ ENNReal.ofReal (Real.exp (P + B)) * G := fun s t h1 h2 h3 => by
    refine le_trans ?_ (mul_le_mul_right h3 _)
    rw [← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal ((pow_le_pow_left₀ ha h1 3).trans ?_)
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by exact_mod_cast h2)
  have d0 : a ≤ Real.exp (P / 625) := d.trans (Real.exp_le_exp.2 (by split_ifs <;> push_cast <;> linarith))
  refine ⟨d0.trans (Real.exp_le_exp.2 (by linarith)), ?_⟩
  rcases lt_or_ge ((Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1) (Fm.L x ι).sc.b with h | h
  · rw [if_pos (e4 h)] at d
    exact key _ _ d (by push_cast; linarith) (e2 h)
  · exact key _ _ d0 (by linarith) (e3 h)
set_option maxHeartbeats 1000000 in
theorem cover_height_section_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → (_root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧ ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (θ : Rul Y.d.Xo₂ Y.d.c₂) (e : HeightOneSpectrum (𝓞 Y.d.c₂.F) →₀ ℝ) (t : (Y.d.c₂.F →+* ℂ) → ℝ), Carries Y.U Z u1 (uPrime (dat p i) u1) θ ∧ (∀ (la : HeightOneSpectrum (𝓞 Y.d.c₂.F)) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Y.d.Xo₂ Y.d.c₂ T io, y.IsAlg → (∃ (G' : WTZ (Fm.D x ι).host.E), ∃ f ∈ cuspOn Y.U Z G', evI y f ≠ 0) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧ InfBd Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) (wtOf (dat p i) ((8 : ℤ) • (u1 - uPrime (dat p i) u1)) 0) 8 θ t ∧ cost e t ≤ cc) := by
  intro hP hH hD hS hF
  refine Closed.imp (Closed.and (_root_.GlobalTheory.CovHt.KeySection.theta_function_le_bergman_kernel_alt hP hH hD hS hF) (Closed.and hF (Closed.and hS
    (Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 1) _root_.GlobalTheory.CovTop.WtShape.wtN_z)))) ?_
  rintro eps Fm CH - ⟨⟨C₁, c₁, h₁⟩, ⟨_, -, h₂⟩, ⟨_, -, h₃⟩, ⟨_, -, h₄⟩, ⟨_, -, h₅⟩⟩
  obtain ⟨x0, h⟩ := h₁.and (h₂.and (h₃.and (h₄.and h₅)))
  refine ⟨C₁ + 10, by linarith, x0, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h x hx hle ι p hp
  obtain ⟨β, b1, b2, b3⟩ := h₁ i hi Y hY u1 hu
  have hN := h₄ i
  have hW := h₅ i
  have hL := GlobalTheory.LawsDeep.laws_deep _ p.T _ Y _ _ p.fw.laws ⟨by omega, by omega⟩ hY.1
  have hM : 5 ^ 4 ∣ Y.d.l₂.M := by
    rw [hY.1.lev.1.2.1, hY.1.pd]
    exact ((pow_dvd_pow_of_dvd (by norm_num : 5 ∣ 15) 4).trans
      (pow_dvd_pow 15 (GlobalTheory.ThetaSteep.four_le_expL hN.big.2.1))).mul_left _
  have hL1 : 1 ≤ (Fm.L x ι).sc.L := by linarith [hN.big.2.1]
  have hf : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast le_trans (by norm_num) hN.f8
  have hr : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hW.sig.2.2 ▸ hL.pos
  have hPP : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hN.ppLow
  have hT : lenT p i (Fm.parT x hx ι).PP * (Fm.parT x hx ι).PP ≤ unitE p := by
    have hD : (1 : ℝ) ≤ dimFlag (dat p i) := by
      rw [hW.dim]
      have m2 := (Fm.D x ι).R.two_le_m
      have k3 := (Fm.D x ι).R.m_add_three_le_k
      have f8 := hN.f8
      exact_mod_cast Nat.mul_pos (by omega) (Nat.choose_pos (by unfold Ranks.r; omega))
    refine le_trans ?_ (hW.what₂.2.trans (h₃ i).2.1)
    rw [mul_comm, mul_assoc _ _ (Fm.L x ι).sc.L]
    exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD) hL1)
  have hu0 : 0 ≤ (lenT p i (Fm.parT x hx ι).PP : ℝ) * β := by positivity
  refine ⟨β / 2 + 10 * (Fm.parT x hx ι).PP, by positivity, by linarith, fun Z => ?_⟩
  obtain ⟨S, hS⟩ := exists_twist (h₂ i hi Y hY) Z (hasPts Y.U hL.pos hL.good hL.unf Z)
    (12 * (((dat p i).p + (dat p i).q : ℕ) : ℤ))
  obtain ⟨θ, e, t, k1, k2, k3, k4⟩ := exists_section Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict hL hM Z
    S u1 β _ (b3 Z)
  refine ⟨θ, e, t, k1, fun la T io e₀ ho y hy _ => k2 la T io e₀ ho y hy, k3, ?_⟩
  have hc := twist_cost_le hf hr hL1 (Nat.cast_nonneg (dat p i).p) (Nat.cast_nonneg (dat p i).q)
    (by exact_mod_cast hW.sig.2.2) hW.om hN.ppLow
  rw [k4, hS, ← Nat.card_eq_fintype_card, hW.card, hW.sig.2.2]
  push_cast
  linarith
end GlobalTheory.CovHt.KeySection
end
end
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_bounded_by_bergman_kernel_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → (_root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧ ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (θ : Rul Y.d.Xo₂ Y.d.c₂) (e : HeightOneSpectrum (𝓞 Y.d.c₂.F) →₀ ℝ) (t : (Y.d.c₂.F →+* ℂ) → ℝ), Carries Y.U Z u1 (uPrime (dat p i) u1) θ ∧ (∀ (la : HeightOneSpectrum (𝓞 Y.d.c₂.F)) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Y.d.Xo₂ Y.d.c₂ T io, y.IsAlg → (∃ (G' : WTZ (Fm.D x ι).host.E), ∃ f ∈ cuspOn Y.U Z G', evI y f ≠ 0) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧ InfBd Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) (wtOf (dat p i) ((8 : ℤ) • (u1 - uPrime (dat p i) u1)) 0) 8 θ t ∧ cost e t ≤ cc) := by
  first | exact @_root_.GlobalTheory.CovHt.KeySection.cover_height_section_bound_alt | exact _root_.GlobalTheory.CovHt.KeySection.cover_height_section_bound_alt | (intros; apply _root_.GlobalTheory.CovHt.KeySection.cover_height_section_bound_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefinedSumWeightOfSizeLe
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefCoreOfSumPt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefCoreOfSumPt
set_option synthInstance.maxHeartbeats 200000

section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
theorem GlobalTheory.RefSum.refCore_of_size_sumPt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.SumPtAlt → _root_.GlobalTheory.RefSum.ReferenceCore := by
  intro hS hSum
  refine Closed.imp (Closed.and hSum (Closed.and (_root_.GlobalTheory.T.quotient_weight_gap_bounds' hS) (_root_.GlobalTheory.T.jetNum_nCol_lenT_bounds_of_quo hS))) ?_
  rintro eps Fm CH - ⟨⟨C1, hC1, h1⟩, ⟨C2, -, h2⟩, C3, hC3, h3⟩
  refine ⟨C1 + C3, add_nonneg hC1 hC3, (h1.and (h2.and h3)).imp fun x0 h x hx hle ι p hp i hi u1 hu => ?_⟩
  obtain ⟨k1, k2, k3⟩ := h x hx hle ι p hp
  obtain ⟨S, e, s, hP, hs, hO⟩ := k1 i hi u1 hu
  obtain ⟨-, -, -, -, -, -, hD, hL, -⟩ := k2 i hi u1 hu
  obtain ⟨hJ, hr, hg⟩ := k3 i hi u1 hu
  have hI : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨by omega, hi.le⟩
  refine ⟨_, _, _, primeSum_add_pair hP (Fm.D x ι).host.g (Fm.D x ι).host.g_prime, by rw [mul_add, add_mul]; exact add_le_add hs hg,
    fun q hq => ?_⟩
  by_cases hq' : q ∈ Finset.univ.image (Fm.D x ι).host.g
  · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hq'
    refine (GlobalTheory.T.supLatticeReferenceExponent_thetaWeight_level_le_one _ p.T.toCore p.fw.laws.toLawsM (Fm.ex x hx ι).errX _ hI _ _ _ hD hL sum_le_nCol hr hJ k).trans
      (EReal.coe_le_coe_iff.2 ?_)
    simp only [if_pos hq']
    linarith [hP.2.1 ((Fm.D x ι).host.g k)]
  · haveI := Fact.mk hq
    have hne : ∀ k, q ≠ (Fm.D x ι).host.g k := fun k h => hq' (Finset.mem_image.2 ⟨k, Finset.mem_univ _, h.symm⟩)
    refine (GlobalTheory.T.baseLocusExponent_le_oscillation_nonTypePrime _ p.T.toCore p.fw.laws.toLawsM (Fm.ex x hx ι).errX _ hI _ _ _ hD hL sum_le_nCol hr hJ q hne _
      (hO q hne)).trans (EReal.coe_le_coe_iff.2 ?_)
    simp only [if_neg hq', add_zero, le_refl]
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefCoreOfSumPtStatement
set_option synthInstance.maxHeartbeats 200000

section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reference_core_of_size_and_sum_point : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.SumPtAlt → _root_.GlobalTheory.RefSum.ReferenceCore := by
  first | exact @_root_.GlobalTheory.RefSum.refCore_of_size_sumPt | exact _root_.GlobalTheory.RefSum.refCore_of_size_sumPt | (intros; apply _root_.GlobalTheory.RefSum.refCore_of_size_sumPt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefThetaOfRefCore
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefThetaOfRefCore
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
namespace GlobalTheory.RefSum
theorem refTheta_of_refCore_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.ReferenceCore → _root_.GlobalTheory.RefSum.ReferenceTheta := by
  intro hS hR
  have hW := _root_.GlobalTheory.T.quotient_weight_gap_bounds' hS
  refine Closed.imp (Closed.and hR hW) ?_
  intro eps Fm CH inst H
  obtain ⟨⟨C, hC, a, h⟩, _, _, b, h'⟩ := H
  refine ⟨C, hC, max a b, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  obtain ⟨S, e, s, hPS, hT, hq⟩ := h x hx ((le_max_left _ _).trans hle) ι p hp i hi u1 hu
  have hD := (h' x hx ((le_max_right _ _).trans hle) ι p hp i hi u1 hu).2.2.2.2.2.2.1
  refine ⟨S, e, s, hPS, hT, fun q hq' => le_trans ?_ (hq q hq')⟩
  exact refExp_vp_cover_le _ p.T _ Y _ _ p.fw.laws ⟨by omega, by omega⟩ hY.1 _ _ hD _ q hq'
end GlobalTheory.RefSum
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefThetaOfRefCoreStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refTheta_of_size_refCore : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.ReferenceCore → _root_.GlobalTheory.RefSum.ReferenceTheta := by
  first | exact @_root_.GlobalTheory.RefSum.refTheta_of_refCore_alt | exact _root_.GlobalTheory.RefSum.refTheta_of_refCore_alt | (intros; apply _root_.GlobalTheory.RefSum.refTheta_of_refCore_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefinedSumWeightOfRefinedTheta
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LogSumBadPrimesLe
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
namespace GlobalTheory.BadLog
variable {D : D7} {L : SizeData₂ D}
theorem logSum_badPrimes_le_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p _ Y _ C => logSum (badPrimes p.T.Q.H Y.d.l₂) ≤ C * zBase (Fm.L x ι) :=
  fun h => Closed.imp h fun Fm _ _ _ => ⟨2 * |Fm.CYL| + 17, by positivity, 0, fun x hx _ ι p _ i _ Y hY => by
    obtain ⟨a, b⟩ := log_level_le (Fm.params x hx ι)
    rw [Fm.params_CYL] at b
    exact (logSum_le_log a fun q hq => dvd_of_mem_badPrimes p.fw.laws.pins hY.1 hq).trans b⟩
end GlobalTheory.BadLog
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
namespace GlobalTheory.RefSum.ToWeight
theorem refinedSum_weight_of_refinedTheta_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.RefSum.ReferenceTheta → _root_.GlobalTheory.RefSum.ReferenceWeight := fun hP hS hF hT =>
  Closed.imp (Closed.and (Closed.and hT (_root_.GlobalTheory.BadLog.logSum_badPrimes_le_alt hS))
      (Closed.and hF (Closed.and (_root_.GlobalTheory.T.lenT_zBase_unitE_nCol_bounds hS) (_root_.GlobalTheory.T.quotient_weight_gap_bounds' hS))))
    fun Fm _ _ ⟨⟨⟨C₁, h₁, hT⟩, C₂, h₂, hB⟩, ⟨_, _, hF⟩, ⟨_, _, hZ⟩, _, _, hW⟩ => by
      obtain ⟨x0, h⟩ := ((hT.and hB).and hF).and (hZ.and hW)
      refine ⟨C₁ + (30 + C₂), by positivity, x0, fun x hx hle ι p hp i hi Y hY u1 hq => ?_⟩
      obtain ⟨⟨⟨hT, hB⟩, hF⟩, hZ, hW⟩ := h x hx hle ι p hp
      obtain ⟨S, e, s, hS, hs, he⟩ := hT i hi Y hY u1 hq
      obtain ⟨z1, z2, z3, z4, z5, z6⟩ := hZ i
      obtain ⟨w1, w2, -, -, -, -, -, -, w3⟩ := hW i hi u1 hq
      have hB := hB i hi Y hY
      have hm : 2 * ((nCol (dat p i) / 2 : ℕ) : ℝ) ≤ nCol (dat p i) := by exact_mod_cast Nat.mul_div_le _ 2
      have hsz := size_le (by exact_mod_cast z5) (by exact_mod_cast z6) z2 (Nat.cast_nonneg _) hm z4 z3 h₂ hB
      refine ⟨_, _, _, primeSum_add (Fm.D x ι).host.E (B := badPrimes p.T.Q.H Y.d.l₂)
        (a := ((nCol (dat p i) / 2 : ℕ) : ℝ) * ((Fm.D x ι).R.f * (Fm.D x ι).R.r)) hS badPrimes_prime (by positivity), ?_,
        fun q hq' => ?_⟩
      · have a1 := mul_le_mul_of_nonneg_left hsz (Nat.cast_nonneg (lenT p i (Fm.parT x hx ι).PP))
        have a2 := mul_le_mul_of_nonneg_left z1 (show (0 : ℝ) ≤ 30 + C₂ by positivity)
        unfold zBase at a2
        linarith
      · refine (_root_.GlobalTheory.T.reference_exponent_valuation_bound hP _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, hi.le⟩ hY.1 w1 w2 ⟨_, hF i hi Y hY⟩ u1
          (shift (dat p i) u1 (nCol (dat p i))) (nCol (dat p i) / 2) (1 / 2500) q hq').trans ?_
        rw [EReal.coe_add]
        exact add_le_add (w3 ▸ he q hq') le_rfl
end GlobalTheory.RefSum.ToWeight
end
end
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refW_of_prints_size_flatDeg_refTheta : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.RefSum.ReferenceTheta → _root_.GlobalTheory.RefSum.ReferenceWeight := by
  first | exact @_root_.GlobalTheory.RefSum.ToWeight.refinedSum_weight_of_refinedTheta_alt | exact _root_.GlobalTheory.RefSum.ToWeight.refinedSum_weight_of_refinedTheta_alt | (intros; apply _root_.GlobalTheory.RefSum.ToWeight.refinedSum_weight_of_refinedTheta_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumPtOfSize
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtPtOfSize
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtPtOfSize
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.MeanTop
namespace GlobalTheory.RefSum.DivWt
section Free
variable {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N) (h : W.Hyp) (hd : W.IsDiv)
include h hd
end Free
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem wtPt_of_wtN_alt (h : _root_.GlobalTheory.CovTop.LiftWeightNumerator) : _root_.GlobalTheory.RefSum.WtPtAlt :=
  Closed.imp h fun Fm _ _ ⟨_, _, a, h⟩ => ⟨802, by norm_num, a, fun x hx hle ι p hp i hi u1 hq =>
    wtAt_of_wtNum p i (h x hx hle ι p hp i) (le_PP (Fm.parT x hx ι)) hi u1 hq⟩
theorem wt_pt_of_cov_size : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.WtPtAlt := fun _ => _root_.GlobalTheory.RefSum.DivWt.wtPt_of_wtN_alt _root_.GlobalTheory.T.lift_weight_numerator
end GlobalTheory.RefSum.DivWt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtPtOfSizeStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_pt_of_size : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.WtPtAlt := by
  first | exact @_root_.GlobalTheory.RefSum.DivWt.wt_pt_of_cov_size | exact _root_.GlobalTheory.RefSum.DivWt.wt_pt_of_cov_size | (intros; apply _root_.GlobalTheory.RefSum.DivWt.wt_pt_of_cov_size <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumPtOfSizes
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumPtOfSizes
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.RefSum
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
theorem sumPt_of_sizes_alt : _root_.GlobalTheory.RefSum.WtPtAlt → _root_.GlobalTheory.RefSum.NumPtAlt → _root_.GlobalTheory.RefSum.SumPtAlt := fun hw hn =>
  Closed.imp (Closed.and hw hn) fun _ _ _ ⟨⟨C₁, h1, e1⟩, C₂, h2, e2⟩ =>
    ⟨40 * (4 * C₁ * (2 * C₁ + C₂ + 1) ^ 2 + C₂ * (2 * C₁ + C₂ + 1) + 2 * C₁) * C₂, by positivity,
      (e1.and e2).imp fun _ h x hx hle ι p hp i hi u1 hu =>
        sumAt_of_sizes p i h1 h2 u1 ((h x hx hle ι p hp).1 i hi u1 hu) ((h x hx hle ι p hp).2 i hi)⟩
end GlobalTheory.RefSum
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumPtOfSizesStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_pt_of_wt_pt_num_pt : _root_.GlobalTheory.RefSum.WtPtAlt → _root_.GlobalTheory.RefSum.NumPtAlt → _root_.GlobalTheory.RefSum.SumPtAlt := by
  first | exact @_root_.GlobalTheory.RefSum.sumPt_of_sizes_alt | exact _root_.GlobalTheory.RefSum.sumPt_of_sizes_alt | (intros; apply _root_.GlobalTheory.RefSum.sumPt_of_sizes_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumPtOfSizeStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numerical_point_statement_of_size : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.NumPtAlt := by
  first | exact @_root_.GlobalTheory.RefSum.NumSizes.numPt_of_size' | exact _root_.GlobalTheory.RefSum.NumSizes.numPt_of_size' | (intros; apply _root_.GlobalTheory.RefSum.NumSizes.numPt_of_size' <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumPtOfSize
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.RefSum
theorem sumPt_of_size_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.SumPtAlt := fun h => _root_.GlobalTheory.T.sum_pt_of_wt_pt_num_pt (_root_.GlobalTheory.T.weight_pt_of_size h) (_root_.GlobalTheory.T.numerical_point_statement_of_size h)
end GlobalTheory.RefSum
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumPtOfSizeStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_pt_of_size : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.SumPtAlt := by
  first | exact @_root_.GlobalTheory.RefSum.sumPt_of_size_alt | exact _root_.GlobalTheory.RefSum.sumPt_of_size_alt | (intros; apply _root_.GlobalTheory.RefSum.sumPt_of_size_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
namespace GlobalTheory.RefSum
theorem refinedSum_weight_of_size_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.RefSum.ReferenceWeight :=
  fun hP _ hS hF => _root_.GlobalTheory.T.refW_of_prints_size_flatDeg_refTheta hP hS hF (_root_.GlobalTheory.T.refTheta_of_size_refCore hS (_root_.GlobalTheory.T.reference_core_of_size_and_sum_point hS (_root_.GlobalTheory.T.sum_pt_of_size hS)))
end GlobalTheory.RefSum
end
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refW_of_prints_deepGood_size_flatDeg : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.RefSum.ReferenceWeight := by
  first | exact @_root_.GlobalTheory.RefSum.refinedSum_weight_of_size_alt | exact _root_.GlobalTheory.RefSum.refinedSum_weight_of_size_alt | (intros; apply _root_.GlobalTheory.RefSum.refinedSum_weight_of_size_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeightOfSteps
set_option synthInstance.maxHeartbeats 200000

section
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.CovHt.HtTopG
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} {p : PtAt ex Csz} {i : Fin D.R.m} {Y : Cov p i}
end Point
theorem height_of_meanAll_bound : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovHt.ShortAlt → _root_.GlobalTheory.CovHt.GeometricCondition → _root_.GlobalTheory.CovHt.MultiplicityConstantCondition → _root_.GlobalTheory.CovHt.ErrorBudgetCondition →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → D.R.m ^ 2 ≤ D.R.k → ∀ j : ℕ, 1 ≤ j → j < D.R.m → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → Y.d.l₂.M'.primeFactors.card ≤ 15 → MeanAll Y.U (xiR D) (ell D) C) →
    _root_.GlobalTheory.CovTop.HeightCondition := by
  intro hPX hP hDG hSz hDg hSh hGe hMu hBu hDS
  obtain ⟨C0, h0, hDS⟩ := hDS
  refine Closed.imp ((((((hDG.and hSz).and hDg).and hSh).and hGe).and hMu).and hBu) ?_
  intro eps Fm CH _ hF
  obtain ⟨⟨⟨⟨⟨⟨⟨C1, -, a1⟩, ⟨C2, -, a2⟩⟩, ⟨C3, -, a3⟩⟩, ⟨C4, c4, a4⟩⟩, ⟨C5, -, a5⟩⟩, ⟨C6, c6, a6⟩⟩, ⟨C7, c7, a7⟩⟩ := hF
  refine ⟨C4 + C6 + C7 + C0 * C7, by positivity, ?_⟩
  obtain ⟨x0, hall⟩ := ((((((a1.and a2).and a3).and a4).and a5).and a6).and a7)
  refine ⟨x0, fun x hx hle ι p hp i hm Y hY u1 hq => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩ := hall x hx hle ι p hp
  have hDGa := b1 i hm Y hY
  obtain ⟨hb1, hbE, -, -, -, -, hρ⟩ := b2 i
  have hU : 0 ≤ unitE p := by linarith
  have hρ1 : rhoB (dat p i) u1 < 1 := ((hρ hm).2 u1 hq).2.2.1
  have hBu := b7 i hm Y hY u1 hq
  exact _root_.GlobalTheory.CovHt.HtTopG.heightAt_eq_of_cover hPX hP hY.1 (_root_.GlobalTheory.CovHt.cover_height_comparison hP _ _ _ _ _ _) h0 c4 c6 c7 hU
    (hDS _ p.T p.fw.laws (Formalism.BasicNotions.ParameterChoice'.m_sq_le_k (Fm.params x hx ι)) ((i : ℕ) + 1) (by omega) hm Y _ _ hY.1 hBu.1) hDGa.2.2.2.2.2.2.1 hρ1
    (b3 i hm Y hY u1 hq) (b4 i hm Y hY u1 hq) (b5 i hm Y hY u1 hq) (b6 i hm Y hY u1 hq) hBu
end GlobalTheory.CovHt.HtTopG
end
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BudgetStatement
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BudgetAltAlt
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.CovHt.BudgetPf
section Point
open _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
theorem budget_alt : (∀ M, _root_.GlobalTheory.CovTop.HostNAlt M) → _root_.GlobalTheory.CovTop.LiftWeightNumerator → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovHt.ErrorBudgetCondition := fun hH hW _ =>
  Closed.imp (Closed.and (hH 1) hW) fun _ _ _ ⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ => by
    obtain ⟨x0, h⟩ := h1.and h2
    exact ⟨83400, by norm_num, x0, fun x hx hle ι p hp i hi Y hY u1 hq =>
      budgetAt p i ((h x hx hle ι p hp).1 i) ((h x hx hle ι p hp).2 i) hi Y hY u1 hq⟩
end GlobalTheory.CovHt.BudgetPf
end
end

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
theorem _root_.GlobalTheory.T.budget_of_hostN_of_liftWeight_of_size : (∀ M, _root_.GlobalTheory.CovTop.HostNAlt M) → _root_.GlobalTheory.CovTop.LiftWeightNumerator → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovHt.ErrorBudgetCondition := by
  first | exact @_root_.GlobalTheory.CovHt.BudgetPf.budget_alt | exact _root_.GlobalTheory.CovHt.BudgetPf.budget_alt | (intros; apply _root_.GlobalTheory.CovHt.BudgetPf.budget_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultCOfRefW
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultCOfRefW
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.CovMult
open GlobalTheory.SlopeRec GlobalTheory.FlatLine GlobalTheory.RefSum
section Places
variable {K : Type} [Field K] [NumberField K]
end Places
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
theorem multC_of_refW_alt : _root_.GlobalTheory.RefSum.ReferenceWeight → (_root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧ ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (θ : Rul Y.d.Xo₂ Y.d.c₂) (e : HeightOneSpectrum (𝓞 Y.d.c₂.F) →₀ ℝ) (t : (Y.d.c₂.F →+* ℂ) → ℝ), Carries Y.U Z u1 (uPrime (dat p i) u1) θ ∧ (∀ (la : HeightOneSpectrum (𝓞 Y.d.c₂.F)) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Y.d.Xo₂ Y.d.c₂ T io, y.IsAlg → (∃ (G' : WTZ (Fm.D x ι).host.E), ∃ f ∈ cuspOn Y.U Z G', evI y f ≠ 0) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧ InfBd Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) (wtOf (dat p i) ((8 : ℤ) • (u1 - uPrime (dat p i) u1)) 0) 8 θ t ∧ cost e t ≤ cc) → _root_.GlobalTheory.CovHt.MultiplicityConstantCondition := by
  intro hR hK
  refine Closed.imp (Closed.and hR hK) fun _ _ _ ⟨⟨C₁, h₁, hR⟩, C₂, h₂, hK⟩ => ⟨C₁ + C₂, add_nonneg h₁ h₂, ?_⟩
  refine (hR.and hK).imp fun _ h x hx hle ι p hp i hi Y hY u1 hu => ?_
  obtain ⟨hR, hK⟩ := h x hx hle ι p hp
  obtain ⟨S, a, s, hS, hs, ha⟩ := hR i hi Y hY u1 hu
  obtain ⟨cc, hc0, hc, hZ⟩ := hK i hi Y hY u1 hu
  have hs0 : 0 ≤ s := (Finset.sum_nonneg fun q _ => mul_nonneg (hS.2.1 q) (Real.log_natCast_nonneg q)).trans hS.2.2.2
  exact ⟨cc + s, add_nonneg hc0 hs0, budget_add hs hc, fun Z => mult_of hY.1.unf hS ha (hZ Z)⟩
end GlobalTheory.CovMult
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultCOfRefWStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carrying_section_integral_frame_alt : _root_.GlobalTheory.RefSum.ReferenceWeight → (_root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧ ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (θ : Rul Y.d.Xo₂ Y.d.c₂) (e : HeightOneSpectrum (𝓞 Y.d.c₂.F) →₀ ℝ) (t : (Y.d.c₂.F →+* ℂ) → ℝ), Carries Y.U Z u1 (uPrime (dat p i) u1) θ ∧ (∀ (la : HeightOneSpectrum (𝓞 Y.d.c₂.F)) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Y.d.Xo₂ Y.d.c₂ T io, y.IsAlg → (∃ (G' : WTZ (Fm.D x ι).host.E), ∃ f ∈ cuspOn Y.U Z G', evI y f ≠ 0) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧ InfBd Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) (wtOf (dat p i) ((8 : ℤ) • (u1 - uPrime (dat p i) u1)) 0) 8 θ t ∧ cost e t ≤ cc) → _root_.GlobalTheory.CovHt.MultiplicityConstantCondition := by
  first | exact @_root_.GlobalTheory.CovMult.multC_of_refW_alt | exact _root_.GlobalTheory.CovMult.multC_of_refW_alt | (intros; apply _root_.GlobalTheory.CovMult.multC_of_refW_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open GlobalTheory.CovTop GlobalTheory.BigTop
namespace SelfIntersectionVolumeEstimates
set_option maxHeartbeats 1000000 in
theorem height_lower_bound_general_alt : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.CovHt.HypothesesH → GlobalTheory.CompanionTheory.Ar.Plug.DeepStR → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.HeightCondition :=
  fun hSB hX hGD hQ hP hH hD hG hS hDg hF => _root_.GlobalTheory.CovHt.HtTopG.height_of_meanAll_bound hSB hP hG hS hDg (_root_.GlobalTheory.T.covering_short_of_deep_size_flatDeg hP hG hS hF) (_root_.GlobalTheory.T.covHt_geom_of_siegel_toroidal_semiAbelian hX hGD hQ hP hH.sieg hX.ks hX.lie hG hS) (_root_.GlobalTheory.T.carrying_section_integral_frame_alt (_root_.GlobalTheory.T.refW_of_prints_deepGood_size_flatDeg hP hG hS hF) (_root_.GlobalTheory.T.exists_section_bounded_by_bergman_kernel_alt hP hH hG hS hF)) (_root_.GlobalTheory.T.budget_of_hostN_of_liftWeight_of_size _root_.GlobalTheory.T.hostN_forall _root_.GlobalTheory.T.lift_weight_numerator hS) hD
end SelfIntersectionVolumeEstimates
end
end
