module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExtendByZeroConstMul
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormSectionEqFlagDomainNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormSectionEqFlagDomainNorm
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm.Comparison₂

theorem isReduced_cAt {K : Type} [Field K] (σ : K →+* ℂ) : IsReduced (CAt σ) :=
  inferInstanceAs (IsReduced ℂ)

theorem cabs_mul {K : Type} [Field K] {σ : K →+* ℂ} (z w : CAt σ) : cabs (z * w) = cabs z * cabs w :=
  norm_mul (show ℂ from z) (show ℂ from w)

theorem cabs_wchar {K : Type} [Field K] {σ : K →+* ℂ} {ι : Type} [Fintype ι] (e : ι → ℕ) (t : ι → (CAt σ)ˣ) :
    cabs (wchar e t) = ∏ i, cabs (t i : CAt σ) ^ e i := by
  have h := norm_prod (α := ℂ) Finset.univ (fun i => (show ℂ from (t i : CAt σ)) ^ e i)
  exact h.trans (Finset.prod_congr rfl fun i _ => norm_pow (α := ℂ) _ _)

theorem cabs_unit_pos {K : Type} [Field K] {σ : K →+* ℂ} (u : (CAt σ)ˣ) : 0 < cabs (u : CAt σ) :=
  norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) u)

theorem cabs_conjAlg {K : Type} [Field K] (σ : K →+* ℂ) (z : CAt σ) : cabs (conjAlg σ z) = cabs z :=
  Complex.norm_conj (show ℂ from z)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem baseNorm_pos (Dw : Datum H) {x : ℝ} (hx : 0 < x) (i : Ix Dw) : 0 < baseNorm Dw x i := by
  cases i with
  | none => exact one_pos
  | some p => exact Real.sqrt_pos.2 (by positivity)

theorem prod_baseNorm (Dw : Datum H) {x : ℝ} (hx : 0 < x) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    ∏ i, (baseNorm Dw x i)⁻¹ ^ ex Dw a n i = Formalism.L2.PjFree.lieFac Dw x a := by
  classical
  have hp : 0 < 2 * Real.pi * x := by positivity
  have hs : (Real.sqrt (2 * Real.pi * x))⁻¹ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * x)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp, ← Real.exp_neg]
    congr 1; ring
  rw [Fintype.prod_option]
  simp only [baseNorm, ex, inv_one, one_pow, one_mul, hs, ← Real.exp_nat_mul]
  rw [← Real.exp_sum, Formalism.L2.PjFree.lieFac, ← Finset.sum_mul]
  congr 1
  rw [Fintype.sum_sigma]
  ring

theorem ptNorm_eq_pnorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → FnNe Xo c fn ∧ (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ k (x : ((U σ).X k).dom) (t : Ix Dw → (CAt σ)ˣ) (y : FrPt Xo c (CAt σ)), FrBor t ((U σ).un k x) y → ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f y = Formalism.L2.PjFree.lieFac Dw xR a * ((U σ).X k).pnorm (Formalism.L2.PjFree.laU (U σ) a n k) (Formalism.L2.PjFree.rdU (U σ) f k) x.1) ∧ ∀ (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((starRingEnd ℂ).comp σ))), FrMap (conjAlg σ) y y' → ∀ a n, ∀ f ∈ sec Xo c a n, ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((starRingEnd ℂ).comp σ) (fn ((starRingEnd ℂ).comp σ)) (ex Dw a n) f y' = ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f y := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn hx hP
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, hWD, -, -, -, hwt⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  have hgood : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ y i, fn σ y i ≠ 0 := by
    intro σ hσ y i
    obtain ⟨k, x, t, hx1, ht⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r (U σ) hσ (hU σ hσ)).2 y
    have h := hP.1 σ hσ k x hx1 t y ht i
    rw [← abs_pos, h]
    exact mul_pos (cabs_unit_pos _) (baseNorm_pos Dw hx i)
  refine ⟨fun σ y i => ?_, fun σ hσ k x t y ht a n hd f hf => ?_, fun σ y y' hm a n f hf => ?_⟩
  · by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
    · exact hgood σ hσ y i
    · have hσ' : Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
        have h := Formalism.L2.PjFree.goodEmb_goodOf c σ
        rwa [Formalism.L2.PjFree.goodOf, if_neg hσ] at h
      obtain ⟨y', hy'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c _ _ (conjAlg σ) y
      rw [← abs_pos, ← hP.2 σ y y' hy' i, abs_pos]
      exact hgood _ hσ' y' i
  · obtain ⟨x', hx', -, ⟨t', ht'⟩, hpn⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r (U σ) hσ (hU σ hσ)).1 k x
    have htt := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)).2.1 t' t _ _ _ ht' ht
    have hfn := hP.1 σ hσ k x' hx' _ y htt
    have hev := hwt (CAt σ) (isReduced_cAt σ) a n f hf _ _ _ htt
    rw [hpn _ _ ((hU σ hσ).2.2.2.2.1 a n hd f hf k)]
    have hrd : ‖Formalism.L2.PjFree.rdU (U σ) f k x'.1‖ = cabs (evR Xo c f ((U σ).un k x')) := by
      have e : Formalism.L2.PjFree.rdU (U σ) f k x'.1 = Formalism.L2.PjFree.toC (evR Xo c f ((U σ).un k x')) :=
        dif_pos x'.2
      rw [e]; rfl
    rw [hrd, ← prod_baseNorm Dw hx a n]
    change cabs (evR Xo c f y) * _ = _
    rw [hev, cabs_mul, cabs_wchar, mul_right_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hfn i, ← mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (cabs_unit_pos _).ne', one_mul]
  · have := isReduced_cAt σ
    have hev := evR_frMap hWD f hf.1 (conjAlg σ) y (hT _ y) y' hm
    change cabs (evR Xo c f y') * _ = cabs (evR Xo c f y) * _
    rw [hev, cabs_conjAlg]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [hP.2 σ y y' hm i]

end GlobalTheory.FrameNorm.Comparison₂
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormSectionEqFlagDomainNormStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointwise_norm_section_eq_flagDomain_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → FnNe Xo c fn ∧ (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ k (x : ((U σ).X k).dom) (t : Ix Dw → (CAt σ)ˣ) (y : FrPt Xo c (CAt σ)), FrBor t ((U σ).un k x) y → ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f y = Formalism.L2.PjFree.lieFac Dw xR a * ((U σ).X k).pnorm (Formalism.L2.PjFree.laU (U σ) a n k) (Formalism.L2.PjFree.rdU (U σ) f k) x.1) ∧ ∀ (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((starRingEnd ℂ).comp σ))), FrMap (conjAlg σ) y y' → ∀ a n, ∀ f ∈ sec Xo c a n, ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((starRingEnd ℂ).comp σ) (fn ((starRingEnd ℂ).comp σ)) (ex Dw a n) f y' = ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f y := by
  first | exact @GlobalTheory.FrameNorm.Comparison₂.ptNorm_eq_pnorm | exact GlobalTheory.FrameNorm.Comparison₂.ptNorm_eq_pnorm | (intros; apply GlobalTheory.FrameNorm.Comparison₂.ptNorm_eq_pnorm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountableFractionRingMvPolynomial
open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.GenericReading

theorem countable_of_fg_top {K L : Type} [Field K] [Countable K] [Field L] [Algebra K L]
    (h : (⊤ : IntermediateField K L).FG) : Countable L := by
  obtain ⟨s, hs⟩ := h
  have h1 := IntermediateField.cardinalMk_adjoin_le K (s : Set L)
  rw [hs, Cardinal.mk_congr (IntermediateField.topEquiv (F := K) (E := L)).toEquiv] at h1
  refine Cardinal.mk_le_aleph0_iff.1 (h1.trans (max_le (max_le ?_ ?_) le_rfl))
  · exact Cardinal.mk_le_aleph0
  · exact Cardinal.mk_le_aleph0

theorem countable_fractionRing_mvPolynomial (ι L : Type) [Countable ι] [Field L] [Countable L] :
    Countable (FractionRing (MvPolynomial ι L)) := by
  have h : Countable (MvPolynomial ι L) := by
    refine Cardinal.mk_le_aleph0_iff.1 (MvPolynomial.cardinalMk_le_max.trans (max_le (max_le ?_ ?_) le_rfl))
    · exact Cardinal.mk_le_aleph0
    · exact Cardinal.mk_le_aleph0
  refine Cardinal.mk_le_aleph0_iff.1 ?_
  rw [FractionRing.cardinalMk]
  exact Cardinal.mk_le_aleph0

theorem embedding_read_at_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (h : GenFrEx Xo c) (Z : Comp Xo c), Nonempty (Om Z →ₐ[c.F] CAt σ) ∧ ∀ φ : Om Z →ₐ[c.F] CAt σ, ∃ (k : U.Comp) (x : (U.X k).dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y' := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU h Z
  refine ⟨?_, fun φ => ?_⟩
  · have hfin : FiniteDimensional ℚ c.F := c.fin
    have hcF : Countable c.F := Cardinal.mk_le_aleph0_iff.1 (by
      simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)
    have hk : Countable (kap Z) := countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c).1 Z)
    have hO : Countable (Om Z) := countable_fractionRing_mvPolynomial _ _
    let _ : Algebra c.F ℂ := σ.toAlgebra
    exact GlobalTheory.nonempty_algHom_complex_of_countable c.F (Om Z)
  · obtain ⟨y', hy⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c (Om Z)
      (CAt σ) φ (genFr h Z)
    obtain ⟨k, x, t, ht⟩ := hU.2.2.1 y'
    exact ⟨k, x, y', t, hy, ht⟩

end GlobalTheory.GenericReading
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.BirationalOfFormRatiosFullTrdeg
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.BirationalOfFormRatiosFullTrdeg
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg

theorem birSt_of_ratios_trdeg :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c), ∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF), ((∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j) ≠ 0 ∧ Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k => evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) / evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j))) = WeightFamilies.dimY D j) → BIRSt h j hj hG G) ∧ (BigAt h j hj hG G → BIRSt h j hj hG G) := by
  intro D T h j hj hG ka wL wF G
  have htr := (GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q h.pins.2.2.2 j hj).2
  have hint := GlobalTheory.Reg.intFormSt_holds D T h j hj hG wL _ G.w
  exact ⟨fun hB => birSt_of h j hj hG htr G hB hint,
    fun hBig => birSt_of_big h j hj hG htr G hBig hint⟩

end GlobalTheory.Reg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.BirationalOfFormRatiosFullTrdegStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.birational_of_formRatios_full_trdeg : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c), ∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF), ((∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j) ≠ 0 ∧ Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k => evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) / evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j))) = WeightFamilies.dimY D j) → BIRSt h j hj hG G) ∧ (BigAt h j hj hG G → BIRSt h j hj hG G) := by
  first | exact @GlobalTheory.Reg.birSt_of_ratios_trdeg | exact GlobalTheory.Reg.birSt_of_ratios_trdeg | (intros; apply GlobalTheory.Reg.birSt_of_ratios_trdeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NotGoodConj
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm.Existence

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem not_good_conj (σ : c.F →+* ℂ) (h : Formalism.L2.PjFree.GoodEmb c σ) :
    ¬ Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
  intro h'
  have h1 : (starRingEnd ℂ) H.rt0 = H.rt0 := by
    have e : (starRingEnd ℂ) ((σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) = H.rt0 := h'
    unfold Formalism.L2.PjFree.GoodEmb at h
    rwa [h] at e
  have h2 : H.rt0.im = 0 := Complex.conj_eq_iff_im.mp h1
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  simp only [sq, Complex.mul_re, Complex.neg_re, Complex.natCast_re] at hre
  rw [h2] at hre
  nlinarith [mul_self_nonneg H.rt0.re]

theorem good_conj (σ : c.F →+* ℂ) (h : ¬ Formalism.L2.PjFree.GoodEmb c σ) :
    Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
  have := Formalism.L2.PjFree.goodEmb_goodOf c σ
  unfold Formalism.L2.PjFree.goodOf at this
  rwa [if_neg h] at this

theorem cabs_mul {K : Type} [Field K] {σ : K →+* ℂ} (a b : CAt σ) : cabs (a * b) = cabs a * cabs b :=
  norm_mul (show ℂ from a) (show ℂ from b)

theorem cabs_one {K : Type} [Field K] {σ : K →+* ℂ} : cabs (1 : CAt σ) = 1 :=
  norm_one (α := ℂ)

theorem cabs_unit_pos {K : Type} [Field K] {σ : K →+* ℂ} (a : (CAt σ)ˣ) : 0 < cabs (a : CAt σ) := by
  have h : cabs (a : CAt σ) * cabs ((a⁻¹ : (CAt σ)ˣ) : CAt σ) = 1 := by
    rw [← cabs_mul, Units.mul_inv, cabs_one]
  have h0 : 0 ≤ cabs (a : CAt σ) := norm_nonneg _
  refine lt_of_le_of_ne h0 fun e => ?_
  rw [← e, zero_mul] at h
  exact zero_ne_one h

theorem baseNorm_pos {x : ℝ} (hx : 0 < x) (i : Ix Dw) : 0 < baseNorm Dw x i := by
  cases i with
  | none => exact one_pos
  | some j => exact Real.sqrt_pos.mpr (by have := Real.pi_pos; positivity)

theorem cabs_eq {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) {k k'} (x : (U.X k).dom) (x' : (U.X k').dom) (t t' : Ix Dw → (CAt σ)ˣ)
    (y : FrPt Xo c (CAt σ)) (hx : IsUnitFr (U.X k) x.1) (hx' : IsUnitFr (U.X k') x'.1)
    (h : FrBor t (U.un k x) y) (h' : FrBor t' (U.un k' x') y) (i : Ix Dw) :
    cabs (t i : CAt σ) = cabs (t' i : CAt σ) := by
  have hi : FrBor t'⁻¹ y (U.un k' x') :=
    (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k' x') y y).2.2.2 t' h'
  have hc : FrBor (t'⁻¹ * t) (U.un k x) (U.un k' x') :=
    (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) y (U.un k' x')).2.2.1 t t'⁻¹ h hi
  have h1 : cabs ((t'⁻¹ * t) i : CAt σ) = 1 := by
    cases i with
    | none => exact GlobalTheory.T.unitFrames_generatorRatio_modulus_one E H Dw l Xo c σ r U hσ hU k k' x x' _ hx hx' hc
    | some j => exact GlobalTheory.T.cabs_frBor_eq_one_of_unitFr E H Dw l Xo c σ r U hσ hU k k' x x' _ hx hx' hc j
  have e : (t i : CAt σ) = (t' i : CAt σ) * ((t'⁻¹ * t) i : CAt σ) := by
    rw [← Units.val_mul, Pi.mul_apply, Pi.inv_apply, mul_inv_cancel_left]
  rw [e, cabs_mul, h1, mul_one]

theorem exists_good {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) {xR : ℝ} (hx : 0 < xR) :
    ∃ G : FrPt Xo c (CAt σ) → Ix Dw → ℝ, (∀ y i, 0 < G y i) ∧
      ∀ k (z : (U.X k).dom), IsUnitFr (U.X k) z.1 → ∀ (t : Ix Dw → (CAt σ)ˣ) (y : FrPt Xo c (CAt σ)),
        FrBor t (U.un k z) y → ∀ i, G y i = cabs (t i : CAt σ) * baseNorm Dw xR i := by
  choose k x t hu hb using (GlobalTheory.T.exists_unit_gram_frame_borel_change E H Dw l Xo c σ r U hσ hU).2
  refine ⟨fun y i => cabs (t y i : CAt σ) * baseNorm Dw xR i,
    fun y i => mul_pos (cabs_unit_pos _) (baseNorm_pos hx i), ?_⟩
  intro k' z hz t' y hy i
  show _ * _ = _
  rw [cabs_eq U hσ hU (x y) z (t y) t' y (hu y) hz (hb y) hy i]

theorem transport {P : (c.F →+* ℂ) → Prop} (G : ∀ σ : c.F →+* ℂ, P σ → FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    {σ τ : c.F →+* ℂ} (e : τ = σ) (hσ : P σ) (hτ : P τ) (φ : CAt σ →ₐ[c.F] CAt τ)
    (hφ : ∀ z : CAt σ, (show ℂ from φ z) = (show ℂ from z)) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt τ))
    (h : FrMap φ y y') : G τ hτ y' = G σ hσ y := by
  subst e
  have h1 : φ = AlgHom.id c.F (CAt τ) := AlgHom.ext hφ
  subst h1
  have u := GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ (AlgHom.id c.F (CAt τ)) y
  rw [u.1 _ _ h u.2.1]

theorem exists_pinned : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ xR : ℝ, 0 < xR → ∃ fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ, FnPin U xR fn ∧ FnNe Xo c fn := by
  classical
  intro E _ _ _ H Dw l Xo c r U hU xR hx
  choose G hpos hpin using fun (σ : c.F →+* ℂ) (hσ : Formalism.L2.PjFree.GoodEmb c σ) =>
    exists_good (U σ) hσ (hU σ hσ) hx
  choose bc hbc using fun (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) =>
    GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ (conjAlg σ) y
  refine ⟨fun σ y => if h : Formalism.L2.PjFree.GoodEmb c σ then G σ h y else G _ (good_conj σ h) (bc σ y), ⟨?_, ?_⟩, ?_⟩
  · intro σ hσ k z hz t y hy i
    simp only [dif_pos hσ]
    rw [abs_of_pos (hpos σ hσ y i)]
    exact hpin σ hσ k z hz t y hy i
  · intro σ y y' hy i
    by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
    · have hn := not_good_conj σ hσ
      simp only [dif_pos hσ, dif_neg hn]
      have hm : FrMap ((conjAlg ((starRingEnd ℂ).comp σ)).comp (conjAlg σ)) y (bc _ y') :=
        frMap_trans (Xo := Xo) (c := c) _ _ _ _ _ y y' _ hy (hbc _ y')
      have e : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ :=
        RingHom.ext fun a => Complex.conj_conj (σ a)
      rw [transport G e hσ (good_conj _ hn) _ (fun z => Complex.conj_conj (show ℂ from z)) y _ hm]
    · have hg := good_conj σ hσ
      simp only [dif_pos hg, dif_neg hσ]
      rw [(GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ (conjAlg σ) y).1 _ _ hy (hbc σ y)]
  · intro σ y i
    by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
    · simp only [dif_pos hσ]
      exact (hpos σ hσ y i).ne'
    · simp only [dif_neg hσ]
      exact (hpos _ _ _ i).ne'

end GlobalTheory.FrameNorm.Existence
end
