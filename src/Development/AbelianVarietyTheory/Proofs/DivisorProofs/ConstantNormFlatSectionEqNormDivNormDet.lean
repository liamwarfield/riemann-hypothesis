module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRanksDegreesAddWithMasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentsPeterssonOrthogonalAndMasses
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionOfLogGrowth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVariety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantNormFlatSectionEqNormDivNormDet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantNormFlatSectionEqNormDivNormDet
open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.DefPt.ArchVal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem exists_homN_eq {σ : c.F →+* ℂ} (U : Unf Xo c σ r) {ξ : ℝ} (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hξ : ∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ξ) (hpq : 1 ≤ Dw.p + Dw.q) {G : WTZ E} (hG : G.2 = 0) {f : Rul Xo c}
    (hf : f ∈ secZ Xo c (exZ Dw G)) {Z : Comp Xo c} {y : FrPt Xo c (CAt σ)} (hy : LiesOn Z y) {N : ℝ}
    (hN : GlobalTheory.LamT.IsMetric y N fun _ => 1) :
    ∃ z ∈ framesOn U Z, homN U ξ G f z = ‖toC (evR Xo c f y)‖ := by
  obtain ⟨k, x, t, hx, ht⟩ := GlobalTheory.LamT.exists_ortho_frBor E H Dw l Xo c σ r U hU y
  refine ⟨⟨k, x.1⟩, ⟨x.2, liesOn_frBor ht hy⟩, ?_⟩
  obtain ⟨g, hg0, hgd, hchg⟩ := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) y y).1 t).1 ht
  have hξ0 : 0 < ξ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← hξ k τ]
    exact norm_pos_iff.2 ((map_ne_zero τ).2 (U.X k).ξ0_ne)
  have hκ : 0 < 2 * Real.pi * ξ := by positivity
  have hm0 := GlobalTheory.OrthoMetric.isMetric_of_isOrtho E H Dw l Xo c σ r U ξ hσ hU hpq k x (hξ k) hx
  have hm1 := GlobalTheory.MetricChange.isMetric_frChg E H Dw l Xo c σ (U.un k x) y 1 _
    (fun b => Matrix.transpose (show Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ from g b))
    (show ℂ from (t none : CAt σ)) (Units.ne_zero (M₀ := ℂ) (t none)) hchg hm0
  obtain ⟨-, hGr⟩ := GlobalTheory.LamT.MetUniq.isMetric_unique E H Dw l Xo c σ y _ _ _ _ hN hm1
  have hsome : ∀ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ),
      ‖toC (t (some p) : CAt σ)‖ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * ξ)) := by
    rintro ⟨τ, i⟩
    have hs : (Real.sqrt (2 * Real.pi * ξ))⁻¹ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * ξ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hκ, ← Real.exp_neg]
      congr 1; ring
    rw [← hgd τ i, ← hs]
    exact GlobalTheory.LamT.OrthoBound.norm_diag_of_triangular
      (Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ)) _ hκ
      (fun i j hij => hg0 τ j i hij) (congrFun hGr τ).symm i
  haveI : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  have hev := GlobalTheory.evR_frBor_of_mem_secZ GlobalTheory.lawsFieldsSeparately.2.1 Xo c _ hf (CAt σ) t _ _ ht
  have hw : ‖toC ((∏ i, t i ^ exZ Dw G i : (CAt σ)ˣ) : CAt σ)‖ = lieFacZ Dw ξ G := by
    have e : ‖toC ((∏ i, t i ^ exZ Dw G i : (CAt σ)ˣ) : CAt σ)‖ = ∏ i, ‖toC (t i : CAt σ)‖ ^ exZ Dw G i := by
      show ‖((∏ i, (show Ix Dw → ℂˣ from t) i ^ exZ Dw G i : ℂˣ) : ℂ)‖ = _
      rw [Units.coe_prod, norm_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [Units.val_zpow_eq_zpow_val, norm_zpow]; rfl
    rw [e, Fintype.prod_option]
    simp only [hsome, exZ, hG, zpow_zero, one_mul, ← Real.rpow_intCast, ← Real.exp_mul]
    rw [← Real.exp_sum, lieFacZ, ← Finset.mul_sum, Fintype.sum_sigma]
    congr 1; ring
  have hrd : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := dif_pos x.2
  rw [homN, ptN, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ hx),
    hev, ← hw]
  show _ * ‖rdU U f k x.1‖ = _
  rw [hrd]
  exact (norm_mul (toC _) (toC _)).symm

theorem cInf_eq {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {ξ : ℝ} (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hξ : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ) (hpq : 1 ≤ Dw.p + Dw.q) {Z : Comp Xo c}
    {la : GlobalTheory.AllWt.Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U ξ Z la δ) {σ : c.F →+* ℂ}
    {y : FrPt Xo c (CAt σ)} (hy : LiesOn Z y) {N : ℝ} (hN : GlobalTheory.LamT.IsMetric y N fun _ => 1) :
    s.cInf σ = ‖toC (evR Xo c s.sig y)‖ := by
  have key : ∀ σ' : c.F →+* ℂ, goodOf c σ = σ' → ∀ y' : FrPt Xo c (CAt σ'), LiesOn Z y' →
      (GlobalTheory.LamT.IsMetric y' N fun _ => 1) → s.cInf σ = ‖toC (evR Xo c s.sig y')‖ := by
    rintro _ rfl y' hy' hN'
    have hg := goodEmb_goodOf c σ
    obtain ⟨z, hz, e⟩ := exists_homN_eq (U _) hg (hU _ hg) (hξ _ hg) hpq (G := wtOf Dw la 0) rfl s.sig_mem hy' hN'
    rw [← e, s.homN_eq hz]
  by_cases hσ : GoodEmb c σ
  · exact key σ (if_pos hσ) y hy hN
  · have hB := GlobalTheory.lawsFieldsSeparately.2.1
    obtain ⟨y', hy'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c (CAt σ)
      (CAt ((starRingEnd ℂ).comp σ)) (FrameNorm.conjAlg σ) y
    have hm' := GlobalTheory.LamT.isMetric_conj E H Dw l Xo c σ y y' N (fun _ => 1) hpq hy' hN
    have h1 : (fun b : E →+* ℂ => ((1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)).map (starRingEnd ℂ)) =
        fun _ => 1 := funext fun b => Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1] at hm'
    haveI : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
    have hev := evR_frMap (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1 s.sig s.sig_mem.1
      (FrameNorm.conjAlg σ) y (GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c (CAt σ) y) y' hy'
    rw [key _ (if_neg hσ) y' (liesOn_frMap hy' hy) hm', hev]
    exact Complex.norm_conj _

theorem cInf_eq_norm_div_norm_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ) (b : c.F), b ≠ 0 → (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) → ∀ σ, s.cInf σ = ‖σ b‖ / ‖(P.X σ τ.1).det‖ := by
  intro E _ _ _ H Dw l Xo c r U ξ hD Z P τ s b _ hb σ
  obtain ⟨-, hX, hA⟩ := P.arch σ
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c c.F (CAt σ)
    (Algebra.ofId c.F (CAt σ)) P.y₀
  have hu : ∀ τ', IsUnit (M := ℂ) (P.X σ τ').det := fun τ' => (hX τ').isUnit
  obtain ⟨y, hy⟩ := (GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c (CAt σ) (fun τ' => (P.X σ τ')ᵀ) 1 z).1
    (fun τ' => show IsUnit (M := ℂ) ((P.X σ τ')ᵀ).det from (Matrix.det_transpose (P.X σ τ')).symm ▸ hu τ') isUnit_one
  have hon : LiesOn Z y := fun q => by
    have e : ptF y = ptF z := by
      apply Limits.pullback.hom_ext
      · rw [ptF, Limits.pullback.lift_fst, ptF, Limits.pullback.lift_fst, hy.1]
      · rw [ptF, Limits.pullback.lift_snd, ptF, Limits.pullback.lift_snd]
    rw [e]
    exact liesOn_frMap hz P.on q
  have h : toC (evR Xo c s.sig y) * (P.X σ τ.1).det = σ b := hb (CAt σ) z y (P.X σ) 1 hu isUnit_one hz hy
  rw [cInf_eq hD.unf hD.xi (hD.p.trans (Nat.le_add_right _ _)) s hon (hA z y hz hy), ← h, norm_mul,
    mul_div_cancel_right₀ _ (norm_ne_zero_iff.2 (hX τ.1))]

end GlobalTheory.DefPt.ArchVal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantNormFlatSectionEqNormDivNormDetStatement
open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantNorm_flatSection_eq_norm_div_norm_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ) (b : c.F), b ≠ 0 → (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) → ∀ σ, s.cInf σ = ‖σ b‖ / ‖(P.X σ τ.1).det‖ := by
  first | exact @GlobalTheory.DefPt.ArchVal.cInf_eq_norm_div_norm_det | exact GlobalTheory.DefPt.ArchVal.cInf_eq_norm_div_norm_det | (intros; apply GlobalTheory.DefPt.ArchVal.cInf_eq_norm_div_norm_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumComponentDegreesDivLeLatticeSlope
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentDegreesSumLeTotalDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentDegreesSumLeTotalDegree
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

namespace GlobalTheory.Proof.componentDegrees_sum_le_total_degree

theorem degOn_sum_le : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ G : WTZ D.host.E, GoodW U (xiR D) V dict G → rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G ∧ (∑ᶠ Z : Comp Xo c, degOn U (xiR D) V dict Z G) ≤ degW U (xiR D) V dict G := by
  intro D H Dw l Xo c r U V dict hc G hG
  haveI : Finite (Comp Xo c) := finite_comp
  have hS : Splits U G := GlobalTheory.T.cuspForms_supLattice_split_over_components D H Dw l Xo c r U V dict (fun σ hσ => (hc.2 σ hσ).1) G
  have hO := GlobalTheory.T.components_peterssonOrthogonal_and_masses D H Dw l Xo c r U V dict hc G
  have hA : Adds U V dict G := GlobalTheory.T.component_ranks_degrees_add_with_masses D H Dw l Xo c r U V dict G hS hO.1
  obtain ⟨-, hr, -, -, hd⟩ := hA.2 hG
  refine ⟨hr, ?_⟩
  rw [hd]
  haveI : Fintype (Comp Xo c) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  refine Finset.sum_le_sum fun Z _ => ?_
  have hlog : (∑ σ : c.F →+* ℂ, Real.log (mass U V dict Z σ)) ≤ 0 :=
    Finset.sum_nonpos fun σ _ => Real.log_nonpos (hO.2.1 Z σ).1 (hO.2.1 Z σ).2
  have hq : ((∑ σ : c.F →+* ℂ, Real.log (mass U V dict Z σ)) / (Module.finrank ℚ c.F : ℝ)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hlog (Nat.cast_nonneg _)
  have hk : (0:ℝ) ≤ (rankOn U Z G : ℝ) / 2 := by positivity
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hk hq]

end GlobalTheory.Proof.componentDegrees_sum_le_total_degree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentDegreesSumLeTotalDegreeStatement
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.componentDegrees_sum_le_total_degree : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ G : WTZ D.host.E, GoodW U (xiR D) V dict G → rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G ∧ (∑ᶠ Z : Comp Xo c, degOn U (xiR D) V dict Z G) ≤ degW U (xiR D) V dict G := by
  first | exact @GlobalTheory.Proof.componentDegrees_sum_le_total_degree.degOn_sum_le | exact GlobalTheory.Proof.componentDegrees_sum_le_total_degree.degOn_sum_le | (intros; apply GlobalTheory.Proof.componentDegrees_sum_le_total_degree.degOn_sum_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumComponentDegreesDivLeLatticeSlope
noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop

namespace GlobalTheory.CovSum

theorem two_le_rdE (D : D7) : 2 ≤ D.host.rdE := by
  have h1 : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
    (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1
  have hq : (2 : ℝ) ≤ D.host.q := by
    have := D.host.qd_big.1
    exact_mod_cast (by omega : 2 ≤ D.host.q)
  have hd : (2 : ℝ) ≤ D.host.d := by
    have := D.host.qd_big.2
    exact_mod_cast (by omega : 2 ≤ D.host.d)
  have h4 : (2 : ℝ) ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d) := by
    rw [Real.le_sqrt' (by norm_num)]; nlinarith
  linarith

theorem log_two_le (D : D7) (K : Type) [Field K] [NumberField K] (φ : D.host.E →+* K) :
    Real.log 2 ≤ Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ) := by
  letI : Algebra D.host.E K := φ.toAlgebra
  refine le_trans ?_ (GlobalTheory.FieldSize.log_finrank_rootDiscr_le_of_tower D.host.E K).2
  have h := Real.log_le_log (by norm_num) (two_le_rdE D)
  have hpos : (0 : ℝ) < |((discr D.host.E : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero D.host.E)
  unfold Formalism.BasicNotions.Host.rdE at h
  rw [Real.log_rpow (by simpa using hpos)] at h
  simpa [div_eq_inv_mul] using h

theorem slope_sq_nonneg_of_rk_zero {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (hL : L.FG)
    (h0 : Formalism.HN.rkK L = 0) (hK : Real.log 2 ≤ Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ)) : 0 ≤ slope_sq N L := by
  letI : StarRing K := starRingOfComm
  unfold slope_sq
  split_ifs with h
  · obtain ⟨-, h2, -⟩ := Formalism.HN.plLat K V _ h.some.2.1.1 h.some.2.1.2 (fun v => (h.some.2.2 v).1) L hL
    rw [h0, mul_zero] at h2
    unfold Formalism.HN.rk at h2
    unfold Formalism.HN.muDef Formalism.HN.slope Formalism.F.slope
    rw [h2]
    simp only [Nat.cast_zero, div_zero, mul_zero]
    linarith
  · exact le_rfl

theorem isComplexData {D : D7} (T : Core D) (hQ : T.Q.Pins) {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) :
    GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => D.sp.W j) Y.dict := by
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [h.lev.1.2.1, hQ.2.1.1]
  refine ⟨h.lev.2, fun σ hσ => ⟨h.unf σ hσ, ?_, (GlobalTheory.FinalJoin2.volPairEx_and_finVol D (D.sp.W j) (D.sp.W_sig j)).2,
    h.xiAbs σ hσ⟩⟩
  obtain ⟨th, hr, h1, h2⟩ := h.dictU σ hσ
  exact ⟨Y.Kf, th, hr, hM ▸ h.levelK, h1, h2⟩

theorem sum_deg_div_le_mu : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), Y.GoodAt (wtOf (T.Q.Dw j) la 0) → Finite (Comp Y.d.Xo₂ Y.d.c₂) → (∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) → 2 * ((∑ᶠ Z, Y.degC la Z) / ∑ᶠ Z, Y.rkC la Z) ≤ Y.mu (wtOf (T.Q.Dw j) la 0) := by
  intro D T j Y e o hT _ hY _ _ la hG hfin _
  obtain ⟨h1, h2⟩ := GlobalTheory.T.componentDegrees_sum_le_total_degree D _ _ _ _ _ _ Y.U (fun _ => D.sp.W j) Y.dict (isComplexData _ hT.pins Y hY) _ hG
  have h3 : (∑ᶠ Z, Y.rkC la Z) = (rankW Y.U (wtOf (T.Q.Dw j) la 0) : ℝ) := by
    haveI := Fintype.ofFinite (Comp Y.d.Xo₂ Y.d.c₂)
    rw [h1, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.cast_sum]
  rw [h3]
  rcases Nat.eq_zero_or_pos (rankW Y.U (wtOf (T.Q.Dw j) la 0)) with h0 | h0
  · rw [h0, Nat.cast_zero, div_zero, mul_zero]
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    set_option synthInstance.maxHeartbeats 200000 in
      exact slope_sq_nonneg_of_rk_zero _ _ hG.2.1 h0 (log_two_le D _ (τ.codRestrict Y.d.c₂.F (Y.d.c₂.conj τ)))
  · have hp : (0 : ℝ) < rankW Y.U (wtOf (T.Q.Dw j) la 0) := by exact_mod_cast h0
    rw [degW_eq] at h2
    rw [← mul_div_assoc, div_le_iff₀ hp]
    change 2 * (∑ᶠ Z, degOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) ≤
      slopeW_sq Y.U (xiR D) (fun _ => D.sp.W j) Y.dict (wtOf (T.Q.Dw j) la 0) * _
    linarith

end GlobalTheory.CovSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumComponentDegreesDivLeLatticeSlopeStatement
open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_component_degrees_div_le_latticeSlope : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → ∀ (la : Weight (T.Q.Dw j)), Y.GoodAt (wtOf (T.Q.Dw j) la 0) → Finite (Comp Y.d.Xo₂ Y.d.c₂) → (∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) → 2 * ((∑ᶠ Z, Y.degC la Z) / ∑ᶠ Z, Y.rkC la Z) ≤ Y.mu (wtOf (T.Q.Dw j) la 0) := by
  first | exact @GlobalTheory.CovSum.sum_deg_div_le_mu | exact GlobalTheory.CovSum.sum_deg_div_le_mu | (intros; apply GlobalTheory.CovSum.sum_deg_div_le_mu <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDomainLiftPolarizedVariety
noncomputable section

namespace GlobalTheory.SiegPt

section Algebra

open Polynomial IsLocalRing

end Algebra

section Level

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp unitOn omegaStd IsGrpPullback LBIso pushPt)

theorem sec_bijective {O C : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [Algebra O C]
    [IsFractionRing O C] (X : Over (Sp O)) [IsProper X.hom]
    (e : Over.mk (Geo.Tor.spMap (algebraMap O C)) ⟶ 𝟙_ (Over (Sp O))) :
    Function.Bijective fun x : 𝟙_ (Over (Sp O)) ⟶ X => e ≫ x := by
  have he : e.left = Geo.Tor.spMap (algebraMap O C) := (Category.comp_id _).symm.trans (Over.w e)
  have hE : ValuativeCriterion.Existence X.hom := by
    have h : UniversallyClosed X.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hU : ValuativeCriterion.Uniqueness X.hom := IsSeparated.valuativeCriterion X.hom
  let S : (Over.mk (Geo.Tor.spMap (algebraMap O C)) ⟶ X) → ValuativeCommSq X.hom := fun z =>
    { R := O, K := C, i₁ := z.left, i₂ := 𝟙 _, commSq := ⟨(Over.w z).trans (Category.comp_id _).symm⟩ }
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have h₁ : Geo.Tor.spMap (algebraMap O C) ≫ x.left = (e ≫ x).left := congrArg (· ≫ x.left) he.symm
    have h₂ : Geo.Tor.spMap (algebraMap O C) ≫ y.left = (e ≫ x).left :=
      (congrArg (· ≫ y.left) he.symm).trans (congrArg Over.Hom.left hxy.symm)
    have := (hU (S (e ≫ x))).elim ⟨x.left, h₁, Over.w x⟩ ⟨y.left, h₂, Over.w y⟩
    exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l this)
  · obtain ⟨⟨l, h1, h2⟩⟩ := hE (S z)
    refine ⟨Over.homMk l h2, Over.OverMorphism.ext ?_⟩
    show e.left ≫ l = z.left
    rw [he]
    exact h1

theorem exists_secHom {O C : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [Algebra O C]
    [IsFractionRing O C] {Q : Out.PolAV (Sp O)}
    {Q' : Out.PolAV (Sp C)} {ψ : Q'.A.left ⟶ Q.A.left}
    (H : IsGrpPullback Q'.A Q.A (Geo.Tor.spMap (algebraMap O C)) ψ) (hw' : LBIso Q'.L (Q.L.pull ψ)) :
    ∃ ρ : (𝟙_ (Over (Sp O)) ⟶ Q.A) →* (𝟙_ (Over (Sp C)) ⟶ Q'.A), Function.Bijective ρ ∧
      ∀ (n : ℕ) x y (u : Oˣ), x ^ n = 1 → y ^ n = 1 →
        Out.WeilIs Q'.A Q'.L n (ρ x) (ρ y) (unitOn (Units.map (algebraMap O C).toMonoidHom u)) →
        Out.WeilIs Q.A Q.L n x y (unitOn u) := by
  have := Q.isAb.comm
  have := Q.isAb.proper
  have hG : Out.GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  let β := algebraMap O C
  obtain ⟨b, hb⟩ := UnifPoint.exists_pointEquiv H
  let e : Over.mk (Geo.Tor.spMap β) ⟶ 𝟙_ (Over (Sp O)) := Over.homMk (Geo.Tor.spMap β) (Category.comp_id _)
  let r : (𝟙_ (Over (Sp O)) ⟶ Q.A) →* (Over.mk (Geo.Tor.spMap β) ⟶ Q.A) :=
    MonoidHom.mk' (fun x => e ≫ x) fun x y => MonObj.comp_mul _ _ _
  have hρ : ∀ x, (b.symm (r x)).left ≫ ψ = Geo.Tor.spMap β ≫ x.left := fun x => by
    rw [← hb, b.apply_symm_apply]; rfl
  refine ⟨b.symm.toMonoidHom.comp r, b.symm.bijective.comp (sec_bijective Q.A e), fun n x y u hx hy hw => ?_⟩
  obtain ⟨c, hc, -⟩ := LevelCompare.weil_existsUnique Q n x y hx hy
  have h₁ := CommPairing.weilIs_pull hG Q.isAb Q.isLB e hc
  have h₂ := (weilIs_grpPullback_of_comm _ _ Q.A Q'.A _ ψ Q.L Q'.L Q.isLB Q'.isLB H hw' _ n _ _
    (pushPt H.1.w _) (pushPt H.1.w _) _ rfl rfl).1 hw
  have h₃ : Out.WeilIs Q.A Q.L n (e ≫ x) (e ≫ y) (unitOn (Units.map β.toMonoidHom u)) :=
    UnifPoint.weilIs_congr (Category.id_comp _) (hρ x) (hρ y) h₂
  have h₄ := CommutatorPairing.weilIs_unique hG Q.isAb Q.isLB h₁ h₃
  obtain ⟨w, rfl⟩ : ∃ w : Oˣ, unitOn w = c :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom.toMonoidHom c,
      Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of O)) c.val)⟩
  have e' : Units.map e.left.appTop.hom.toMonoidHom (unitOn w) = unitOn (Units.map β.toMonoidHom w) :=
    Units.ext (congrArg (fun q => q.hom w.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
  have inj : Function.Injective (unitOn (R := C)) :=
    Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv.injective
  have h₅ := congrArg Units.val (inj (e'.symm.trans h₄))
  obtain rfl : w = u := Units.ext (IsFractionRing.injective O C h₅)
  exact hc

theorem exists_level {O C : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [IsAlgClosed C] [Algebra O C]
    [IsFractionRing O C] (P : Out.PolAV (Sp O)) (h M : ℕ) (ze : Oˣ) (hg : P.g = h) (hM : IsUnit (M : O))
    (hz : IsPrimitiveRoot (algebraMap O C ze) M) :
    ∃ lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp O)) ⟶ P.A), (∀ x y, lev (x + y) = lev x * lev y) ∧
      (∀ x, lev x ^ M = 1) ∧ ∀ x y, Out.WeilIs P.A P.L M (lev x) (lev y) (unitOn (ze ^ omegaStd x y)) := by
  subst hg
  have hM' : (M : C) ≠ 0 := by
    have := (hM.map (algebraMap O C)).ne_zero
    rwa [map_natCast] at this
  haveI : NeZero M := ⟨fun h0 => hM' (by rw [h0, Nat.cast_zero])⟩
  obtain ⟨P', g, hg, hgg, hmul, tw, htw⟩ :=
    GlobalTheory.laws_without_cohomology.2.2.1 _ _ (Geo.Tor.spMap (algebraMap O C)) P
  have hp : IsGrpPullback P'.A P.A (Geo.Tor.spMap (algebraMap O C)) g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [show x₀ = Out.toBase hg.w x from Over.OverMorphism.ext hx,
      show y₀ = Out.toBase hg.w y from Over.OverMorphism.ext hy, ← hmul]
    rfl⟩
  obtain ⟨ρ, hρ, hw⟩ := exists_secHom hp (Geo.Tor.LBIso.symm ⟨tw, htw⟩)
  obtain ⟨lev⟩ := nonempty_level_of_isAlgClosed C P' M (Units.map (algebraMap O C).toMonoidHom ze) hM'
    (IsPrimitiveRoot.coe_units_iff.1 hz)
  rw [← hgg]
  have := P'.isAb.comm
  choose t ht using fun a : Fin P'.g ⊕ Fin P'.g → ℤ =>
    hρ.2 (LevelCompare.homOfBasis lev (Multiplicative.ofAdd (fun j => (a j : ZMod M))))
  have tors : ∀ a, t a ^ M = 1 := fun a => hρ.1 (by rw [map_pow, ht, map_one, LevelCompare.hom_pow])
  refine ⟨t, fun a b => hρ.1 ?_, tors, fun a b => hw M _ _ _ (tors a) (tors b) ?_⟩
  · rw [map_mul, ht, ht, ht, ← map_mul, ← ofAdd_add]
    exact congrArg _ (congrArg _ (funext fun j => Int.cast_add _ _))
  · rw [ht, ht, map_zpow]
    have w := LevelCompare.pairing_of_basis lev a b
    unfold unitOn at w ⊢
    rw [map_zpow]
    exact w

end Level

section Main

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj

end Main

end GlobalTheory.SiegPt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianKeyValueNormOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianKeyValueNormOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.AbKey

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (u : Γ(X, U)ˣ) :
    res h (res h' u) = res (h.trans h') u := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem exists_unit_sec {X : Scheme.{0}} (L : LB X) (F : X ⟶ X) (hF : F = 𝟙 X) (t : LB.Gen (L.pull F)) (ht : t.IsGen) :
    ∃ s : H0 L 1, ∀ j, IsUnit (s.f j) := by
  subst hF
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0
  refine ⟨⟨fun j => (res (le j) (t.s fun _ => j 0)).val, fun i j => ?_⟩, fun j => Units.isUnit _⟩
  have h := congrArg (res (inf_le_inf (le i) (le j))) (ht (fun _ => i 0) (fun _ => j 0))
  replace h := h.trans (map_mul (res (inf_le_inf (le i) (le j))) _ _)
  have e : res (inf_le_inf (le i) (le j)) ((L.pull (𝟙 X)).g (fun _ => i 0) (fun _ => j 0)) =
      (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ))).g i j := by
    simp only [LB.pull, LB.LinComb, Fintype.prod_unique, Nat.cast_one, zpow_one]
    exact res_res' _ _ _
  have h' : res inf_le_left (res (le i) (t.s fun _ => i 0)) =
      (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ))).g i j *
        res inf_le_right (res (le j) (t.s fun _ => j 0)) := by
    refine ((res_res' _ _ _).trans (res_res' _ _ _).symm).trans (h.trans ?_)
    exact congrArg₂ (· * ·) e ((res_res' _ _ _).trans (res_res' _ _ _).symm)
  exact congrArg Units.val h'

theorem norm_th_one {V : Type} [CommRing V] [IsDomain V] {D : DegPre V} {C : Type} [NormedField C]
    [Algebra (FractionRing V) C] {N : NumD C} (ν : NumOf D C N) (hν : ν.IntN) (hg : D.P.g = 0) : ‖N.th 1‖ = 1 := by
  haveI : IsIso D.P.A.hom := GlobalTheory.ZM.Model.isIso_of_dim_zero D.P.A D.P.isAb (hg ▸ D.P.smoothDim)
  have he : eSec D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w η[D.P.A]
  have he' : D.P.A.hom ≫ eSec D.P.A = 𝟙 _ := by
    rw [← cancel_mono D.P.A.hom, Category.assoc, Category.id_comp]
    exact (congrArg _ he).trans (Category.comp_id _)
  obtain ⟨s, hs⟩ := exists_unit_sec D.P.L (D.P.A.hom ≫ eSec D.P.A) he'
    (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.P.A.hom)
    (DVR.pullGen_isGen _ _ _ _ D.rig_gen _)
  obtain ⟨r, hr⟩ := ν.th_gen s
  have hu : ∀ j, IsUnit (ν.th.f j) := fun j => isUnit_of_mul_isUnit_right (hr j ▸ hs j)
  obtain ⟨S, hS, hI⟩ := hν
  obtain ⟨x₀, hx, hU⟩ := hI (ν.eA 1)
  have h := congrArg norm (ν.th_eq 1)
  have hT : (TF (R := V) C).hom = spMap S.subtype ≫ x₀ ≫ D.P.A.hom := by
    rw [← Over.w (ν.eA 1), ← hx, Category.assoc]
  have hT' : (TF (R := V) C).hom ≫ eSec D.P.A = (ν.eA 1).left := by
    rw [← Over.w (ν.eA 1), Category.assoc]
    exact (congrArg _ he').trans (Category.comp_id _)
  have h1 : ‖sF ν.th (ν.eA 1).left ν.J‖ = 1 := by
    unfold sF
    have := UnitNorm.norm_valF_unit hS x₀ (LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left)
      fun _ => ν.J ((ν.eA 1).left ≫ 𝟙 _)) (fun y hy => Set.mem_iInter.2 fun _ => by
        rw [Category.comp_id]; exact hU hy) _ (hu _)
    rw [hx] at this
    exact this
  have h2 : ‖vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := V) C).hom ν.J‖ = 1 := by
    unfold vF
    have := UnitNorm.norm_valF_unit hS (x₀ ≫ D.P.A.hom) (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A)
      fun _ => ν.J ((TF (R := V) C).hom ≫ eSec D.P.A)) (fun y hy => Set.mem_iInter.2 fun _ => by
        rw [hT']
        change ((x₀ ≫ D.P.A.hom) ≫ eSec D.P.A) y ∈ D.P.L.U _
        have e : (x₀ ≫ D.P.A.hom) ≫ eSec D.P.A = x₀ :=
          (Category.assoc _ _ _).trans ((congrArg _ he').trans (Category.comp_id _))
        rw [e]; exact hU hy) _ (Units.isUnit (D.rig.s _))
    rw [← hT] at this
    exact this
  rwa [norm_mul, h1, h2, _root_.mul_one] at h

theorem sec_unique {X : Scheme.{0}} {L : LB X} (t : H0 L 1) {a b : L.Sec}
    (ha : ∀ i : L.ι, ∀ h : LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) ≤ L.U i, t.f (fun _ => i) = resG _ h (a.f i))
    (hb : ∀ i : L.ι, ∀ h : LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) ≤ L.U i, t.f (fun _ => i) = resG _ h (b.f i)) :
    a = b := by
  have key : a.f = b.f := funext fun i => by
    have h : LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) ≤ L.U i := LB.wchart_le L _ _ 0
    have h' : L.U i ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := fun y hy => Set.mem_iInter.2 fun _ => hy
    have e := congrArg (resG _ h') ((ha i h).symm.trans (hb i h))
    have r : ∀ z : Γ(X, L.U i), resG _ h' (resG _ h z) = z := fun z => by
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      exact (congrArg (fun f => (X.presheaf.map f).hom z) (Subsingleton.elim _ (𝟙 _))).trans (by rw [X.presheaf.map_id]; rfl)
    rwa [r, r] at e
  cases a; cases b; cases key; rfl

theorem exists_bKey : ∀ κ : Rule, Rule4 κ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] (D : DegPre V) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D C N), ν.IntN → ∀ vB : Fin D.P.g → (epsR V ⟶ D.P.A), IsLieBasis vB → ∃ k : C, BKey κ ν vB k ∧ ‖k‖ = 1 := by
  intro κ hκ V _ _ _ _ D C _ _ _ _ hC N ν hν vB hv
  by_cases hg : D.P.g = 0
  · have h := norm_th_one ν hν hg
    have h0 : N.th 1 ≠ 0 := fun e => by simp [e] at h
    refine ⟨(N.th 1 ^ 8)⁻¹, ⟨fun _ => mul_inv_cancel₀ (pow_ne_zero _ h0), fun hg' => by omega⟩, by
      rw [norm_inv, norm_pow, h, one_pow, inv_one]⟩
  by_cases hex : ∃ th : D.P.L.Sec, (∀ s : Sp V, ∃ x : D.P.A.left, D.P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th) ∧
      ∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i,
        ν.th.f (fun _ => i) = resG _ h (th.f i)
  · obtain ⟨th, hth, hf⟩ := hex
    obtain ⟨u, hu⟩ := hκ.2.2.2 V ⟨D.P, Nat.one_le_iff_ne_zero.2 hg, D.rig, D.rig_gen, th, hth, vB, hv⟩
    refine ⟨toF V C u, ⟨fun e => (hg e).elim, fun _ _ th' _ _ x hf' hx => ?_⟩, ?_⟩
    · obtain rfl := sec_unique ν.th hf hf'
      exact hu C _ x hx
    · have h1 : ‖toF V C u‖ ≤ 1 := hC.1 _
      have h2 : ‖toF V C ↑u⁻¹‖ ≤ 1 := hC.1 _
      have h3 : ‖toF V C u‖ * ‖toF V C ↑u⁻¹‖ = 1 := by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
      nlinarith [norm_nonneg (toF V C u), norm_nonneg (toF V C ↑u⁻¹)]
  · exact ⟨1, ⟨fun e => (hg e).elim, fun _ _ th hth _ _ hf _ => (hex ⟨th, hth, hf⟩).elim⟩, norm_one⟩

end GlobalTheory.MBLow.AbKey

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianKeyValueNormOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianKeyValue_norm_one : ∀ κ : Rule, Rule4 κ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] (D : DegPre V) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D C N), ν.IntN → ∀ vB : Fin D.P.g → (epsR V ⟶ D.P.A), IsLieBasis vB → ∃ k : C, BKey κ ν vB k ∧ ‖k‖ = 1 := by
  first | exact @GlobalTheory.MBLow.AbKey.exists_bKey | exact GlobalTheory.MBLow.AbKey.exists_bKey | (intros; apply GlobalTheory.MBLow.AbKey.exists_bKey <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreconnectedComplexPointsOpenVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreconnectedComplexPointsOpenVariety
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CxPts

namespace GlobalTheory.CxConn

variable {F : Type} [Field F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {σ : F →+* ℂ} {d : ℕ}

theorem exists_algX_eq [IsProper p] [GeometricallyIntegral p] (a : Γ(Y, ⊤)) : ∃ c : F, algX p ⊤ c = a := by
  have : IsIso p.appTop := ProperFunctions.isIso_appTop_of_field p
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso p.appTop).2 a
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 b
  exact ⟨c, congrArg (fun g : Γ(Sp F, ⊤) ⟶ Γ(Y, ⊤) => g ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c))
    (p.appLE_eq_app (U := ⊤))⟩

theorem eq_of_holoOn_univ [SmoothOfRelativeDimension d p] [IsProper p] [GeometricallyIntegral p]
    (hp : IsProjOver p) (R : AnRead p σ d) {f : CxPts p σ → ℂ} (hf : R.HoloOn univ f) (y z : CxPts p σ) :
    f y = f z := by
  have hs : (fun _ : (Out.Inh.trivLB Y).ι => f) ∈ R.holSec (Out.Inh.trivLB Y) := by
    refine ⟨⟨fun i j w hi hj => ?_, fun i w h => (h mem_ptsIn_top).elim⟩, fun i => hf.mono (subset_univ _)⟩
    have e : gv p σ (Out.Inh.trivLB Y) i j w = 1 :=
      (ev_eq (mem_ptsIn_inf.2 ⟨hi, hj⟩) _).trans (map_one _)
    rw [e, one_mul]
  obtain ⟨x, hx⟩ := (AnRead.bijective_valC hp R (Out.Inh.trivLB_isLB Y)).2 ⟨_, hs⟩
  let L : ((Out.Inh.trivLB Y).ι → CxPts p σ → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun s => s PUnit.unit y - s PUnit.unit z
      map_add' := fun s t => add_sub_add_comm _ _ _ _
      map_smul' := fun c s => (mul_sub c _ _).symm }
  have h := SecC.val_mem_of (M := LinearMap.ker L) (fun s => by
    obtain ⟨c, hc⟩ := exists_algX_eq (p := p) (s.f PUnit.unit)
    have e (w : CxPts p σ) : secVal p σ s PUnit.unit w = σ c :=
      (congrArg (fun a => ev p σ ⊤ a w) hc.symm).trans (ev_algX mem_ptsIn_top c)
    change secVal p σ s PUnit.unit y - secVal p σ s PUnit.unit z = 0
    rw [e, e, sub_self]) x
  have e : SecC.val x = fun _ : (Out.Inh.trivLB Y).ι => f := congrArg Subtype.val hx
  rw [e] at h
  exact sub_eq_zero.1 h

theorem exists_holoOn_univ_of_local {R : AnRead p σ d} {A : Set (CxPts p σ)} (hA : Dense A) {u : CxPts p σ → ℂ}
    (h : ∀ y, ∃ (T : Set (CxPts p σ)) (f : CxPts p σ → ℂ), IsOpen T ∧ y ∈ T ∧ R.HoloOn T f ∧ EqOn f u (T ∩ A)) :
    ∃ f, R.HoloOn univ f ∧ EqOn f u A := by
  choose T f hT hy hf he using h
  refine ⟨fun y => f y y, AnRead.holoOn_of_cover (T := T) hT (fun y _ => ⟨y, hy y⟩)
    fun y => ((hf y).mono inter_subset_right).congr fun z hz => ?_, fun y hS => he y ⟨hy y, hS⟩⟩
  have ho := (hT z).inter (hT y)
  have e : EqOn (f z) (f y) (T z ∩ T y ∩ A) := fun w hw =>
    (he z ⟨hw.1.1, hw.2⟩).trans (he y ⟨hw.1.2, hw.2⟩).symm
  exact e.of_subset_closure (((hf z).mono inter_subset_left).continuousOn ho)
    (((hf y).mono inter_subset_right).continuousOn ho) inter_subset_left (hA.open_subset_closure_inter ho)
    ⟨hy z, hz.2⟩

theorem exists_local_extension [GeometricallyIntegral p] [LocallyOfFiniteType p] (R : AnRead p σ d) {W : Y.Opens}
    (hW : (W : Set Y).Nonempty) {u : CxPts p σ → ℂ} (hu : R.HoloOn (ptsIn p σ W) u) {C : ℝ}
    (hC : ∀ y, ‖u y‖ ≤ C) (y : CxPts p σ) :
    ∃ (T : Set (CxPts p σ)) (f : CxPts p σ → ℂ), IsOpen T ∧ y ∈ T ∧ R.HoloOn T f ∧ EqOn f u (T ∩ ptsIn p σ W) := by
  have : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton p
  obtain ⟨i, hi⟩ := R.cover y
  set c := R.chart i
  obtain ⟨φ, hφ, hφW⟩ := CxPtsDense.exists_ne_zero_basicOpen_le c.affine
    ⟨_, mem_ptsIn.1 (c.source_subset hi)⟩ hW
  have hD : Dense (ptsIn p σ (Y.basicOpen φ)) := by
    refine (CxPtsDense.nonempty_and_dense_of_geometricallyIntegral p σ).2 _ (nonempty_iff_ne_empty.2 fun h => hφ ?_)
    exact (basicOpen_eq_bot_iff φ).1 (Opens.ext h)
  have hin {z} (hz : z ∈ c.e.source) : z ∈ ptsIn p σ (Y.basicOpen φ) ↔ ev p σ c.U φ z ≠ 0 :=
    mem_ptsIn_basicOpen (c.source_subset hz) φ
  obtain ⟨v, hv, he⟩ := GlobalTheory.LogExt.riemann_extension_log _ c.e.target (ev p σ c.U φ ∘ c.e.symm) (u ∘ c.e.symm)
    c.e.open_target ((c.holo c.U φ).mono fun b hb => ⟨hb, c.source_subset (c.e.map_target hb)⟩)
    ((hu i).mono fun b hb => ⟨hb.1, ptsIn_mono hφW ((hin (c.e.map_target hb.1)).2 hb.2)⟩)
    (fun b hb => by
      have hs := c.e.map_target hb
      have h₁ := hD.open_subset_closure_inter c.e.open_source hs
      have h₂ := (c.e.continuousAt hs).continuousWithinAt.mem_closure_image h₁
      rw [c.e.right_inv hb] at h₂
      refine closure_mono ?_ h₂
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨c.e.map_source hz.1, ?_⟩
      rw [Function.comp_apply, c.e.left_inv hz.1]
      exact (hin hz.1).1 hz.2)
    fun b _ => ⟨C, 0, Eventually.of_forall fun b' _ => by rw [pow_zero, mul_one]; exact hC _⟩
  have hf : R.HoloOn c.e.source (v ∘ c.e) := by
    have := AnRead.holoOn_of_chart (R := R) (S := univ) (f := v ∘ c.e) c
      ((hv.mono inter_subset_left).congr fun b hb => congrArg v (c.e.right_inv hb.1))
    rwa [inter_univ] at this
  refine ⟨c.e.source, v ∘ c.e, c.e.open_source, hi, hf, ?_⟩
  have ho := c.e.open_source.inter (isOpen_ptsIn (p := p) (σ := σ) W)
  have e : EqOn (v ∘ c.e) u (c.e.source ∩ ptsIn p σ W ∩ ptsIn p σ (Y.basicOpen φ)) := fun z hz => by
    have := he (x := c.e z) ⟨c.e.map_source hz.1.1, by
      rw [Function.comp_apply, c.e.left_inv hz.1.1]; exact (hin hz.1.1).1 hz.2⟩
    simpa only [c.e.left_inv hz.1.1, Function.comp_apply] using this
  exact e.of_subset_closure ((hf.mono inter_subset_left).continuousOn ho)
    ((hu.mono inter_subset_right).continuousOn ho) inter_subset_left (hD.open_subset_closure_inter ho)

theorem isPreconnected_ptsIn_of_isProjOver (d : ℕ) [SmoothOfRelativeDimension d p] [IsProper p]
    [GeometricallyIntegral p] (hp : IsProjOver p) (W : Y.Opens) : IsPreconnected (ptsIn p σ W) := by
  refine isPreconnected_of_forall_constant fun g hg y hy z hz => ?_
  have hW : (W : Set Y).Nonempty := ⟨_, mem_ptsIn.1 hy⟩
  let R := AnRead.all (p := p) (σ := σ) (D := d)
  let κ : Bool → ℂ := fun b => if b then 1 else 0
  have hu : R.HoloOn (ptsIn p σ W) (κ ∘ g) := fun i b hb => by
    have h₁ : ContinuousAt (g ∘ (R.chart i).e.symm) b :=
      (hg.continuousAt ((isOpen_ptsIn W).mem_nhds hb.2)).comp ((R.chart i).e.continuousAt_symm hb.1)
    have h₂ : ∀ᶠ b' in 𝓝 b, (g ∘ (R.chart i).e.symm) b' = (g ∘ (R.chart i).e.symm) b :=
      h₁.eventually ((isOpen_discrete _).mem_nhds (mem_singleton _))
    refine ((differentiableAt_const (κ ((g ∘ (R.chart i).e.symm) b))).congr_of_eventuallyEq
      (h₂.mono fun b' hb' => congrArg κ hb')).differentiableWithinAt
  have hC (w) : ‖(κ ∘ g) w‖ ≤ 1 := by
    simp only [Function.comp_apply, κ]
    split_ifs <;> simp
  obtain ⟨f, hf, he⟩ := exists_holoOn_univ_of_local
    ((CxPtsDense.nonempty_and_dense_of_geometricallyIntegral p σ).2 W hW) (exists_local_extension R hW hu hC)
  have e : κ (g y) = κ (g z) := (he hy).symm.trans ((eq_of_holoOn_univ hp R hf y z).trans (he hz))
  revert e
  cases g y <;> cases g z <;> simp [κ]

theorem isPreconnected_ptsIn : ∀ (F : Type) [Field F] [NumberField F] (B : GlobalTheory.ProjVar.Var F) (e : F →+* ℂ)
    (W : B.X.Opens), IsPreconnected (GlobalTheory.CxPts.ptsIn B.str e W) :=
  fun _ _ _ B _ W => isPreconnected_ptsIn_of_isProjOver B.dim B.isProjOver W

end GlobalTheory.CxConn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreconnectedComplexPointsOpenVarietyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPreconnected_complexPoints_open_variety : ∀ (F : Type) [Field F] [NumberField F] (B : GlobalTheory.ProjVar.Var F) (e : F →+* ℂ) (W : B.X.Opens), IsPreconnected (GlobalTheory.CxPts.ptsIn B.str e W) := by
  first | exact @GlobalTheory.CxConn.isPreconnected_ptsIn | exact GlobalTheory.CxConn.isPreconnected_ptsIn | (intros; apply GlobalTheory.CxConn.isPreconnected_ptsIn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataValuesIsoTransportFormsLevelsFam
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataValuesIsoTransportFormsLevelsFam
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow.TrNum

section
variable {O O' : Type} [CommRing O] [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : NumD.Hom f N N')

theorem img_mul (g h : N.Gt) : I.img (g * h) = I.img g * I.img h :=
  ((I.rel_iff _ _).1 ((I.rel_img g).mul (I.rel_img h))).symm

theorem img_pow (g : N.Gt) (n : ℕ) : I.img (g ^ n) = I.img g ^ n :=
  ((I.rel_iff _ _).1 ((I.rel_img g).pow n)).symm

theorem img_io (y : N.X) : I.img (N.io y) = N'.io (I.e y) :=
  ((I.rel_iff _ _).1 (I.rel_io y)).symm

def imgQ {k : ℕ} (p : N.QT k) : N'.QT k :=
  ⟨(Multiplicative.ofAdd (I.e p.1.1.toAdd), I.img p.1.2), by
    have h : p.1.2 ^ k = N.io p.1.1.toAdd := p.2
    change I.img p.1.2 ^ k = N'.io (I.e p.1.1.toAdd)
    rw [← img_pow, h, img_io]⟩

theorem imgQ_mul {k : ℕ} (p q : N.QT k) : imgQ I (p * q) = imgQ I p * imgQ I q :=
  Subtype.ext (Prod.ext (congrArg Multiplicative.ofAdd (map_add I.e p.1.1.toAdd q.1.1.toAdd)) (img_mul I p.1.2 q.1.2))

theorem qEq_imgQ (hi : Function.Injective I.img) {k : ℕ} (p q : N.QT k) :
    N'.QEq (imgQ I p) (imgQ I q) ↔ N.QEq p q := by
  constructor
  · rintro ⟨z, h1, h2⟩
    obtain ⟨z, rfl⟩ := I.e.surjective z
    refine ⟨z, I.e.injective ?_, hi ?_⟩
    · rw [map_add (f := _), map_nsmul]; exact h1
    · rw [img_mul, img_io]; exact h2
  · rintro ⟨z, h1, h2⟩
    refine ⟨I.e z, ?_, ?_⟩
    · change I.e q.1.1.toAdd = I.e p.1.1.toAdd + k • I.e z
      rw [h1, map_add (f := _), map_nsmul]
    · change I.img q.1.2 = I.img p.1.2 * N'.io (I.e z)
      rw [h2, img_mul, img_io]

theorem imgQ_surjective (hi : Function.Bijective I.img) {k : ℕ} : Function.Surjective (imgQ I (k := k)) := by
  intro p'
  obtain ⟨g, hg⟩ := hi.2 p'.1.2
  have h : p'.1.2 ^ k = N'.io p'.1.1.toAdd := p'.2
  refine ⟨⟨(Multiplicative.ofAdd (I.e.symm p'.1.1.toAdd), g), ?_⟩, Subtype.ext (Prod.ext ?_ hg)⟩
  · change g ^ k = N.io (I.e.symm p'.1.1.toAdd)
    apply hi.1
    rw [img_pow, img_io, hg, h, AddEquiv.apply_symm_apply]
  · change Multiplicative.ofAdd (I.e (I.e.symm p'.1.1.toAdd)) = p'.1.1
    rw [AddEquiv.apply_symm_apply]; rfl

def formImg {k : ℕ} (β : N.Form k) : N'.Form k where
  be := β.be.compl₁₂ I.e.symm.toIntLinearEquiv.toLinearMap I.e.symm.toIntLinearEquiv.toLinearMap
  symm y z := β.symm _ _
  pos y hy := β.pos (I.e.symm y) (fun h => hy (by simpa using congrArg I.e h))
  dvd y z := β.dvd _ _

end

variable {F F' : Type} [Field F] [Field F'] {e : F ≃+* F'} {N : NumD F} {N' : NumD F'} (I : NumD.Hom (e : F →+* F') N N')

theorem units_bij (e : F ≃+* F') : Function.Bijective (Units.map (e : F →+* F').toMonoidHom) :=
  (Units.mapEquiv e.toMulEquiv).bijective

theorem img_bijective (hφ : Function.Bijective I.φ) (hh : ∀ x, I.h x = 1) : Function.Bijective I.img := by
  have hu := units_bij e
  constructor
  · intro g g' h
    have a := I.rel_img g
    have b := I.rel_img g'
    rw [h] at a
    refine NumD.Gt.ext (hφ.1 (a.1.symm.trans b.1)) (funext fun χ => hu.1 ?_)
    have a2 := a.2 χ
    have b2 := b.2 χ
    simp only [hh, _root_.mul_one] at a2 b2
    exact a2.symm.trans b2
  · intro g'
    obtain ⟨b, hb⟩ := hφ.2 g'.b
    choose s hs using fun χ => hu.2 (g'.s (I.e χ))
    refine ⟨⟨b, s, fun χ χ' => hu.1 ?_⟩, ((I.rel_iff _ _).1 ⟨hb.symm, fun χ => ?_⟩).symm⟩
    · have a := I.θ_eq (N.c χ) (N.c χ') b
      simp only [hh, _root_.mul_one] at a
      rw [map_mul, map_mul, hs, hs, hs, ← a, ← I.c_eq, ← I.c_eq, hb, map_add (f := _)]
      exact g'.mult _ _
    · simp only [hh, _root_.mul_one]
      exact (hs χ).symm

theorem transport : ∀ (F F' : Type) [Field F] [Field F'] (e : F ≃+* F') (N : NumD F) (N' : NumD F') (I : NumD.Hom (e : F →+* F') N N'), Function.Bijective I.φ → (∀ x, I.h x = 1) → I.lam = 1 → (∀ (k : ℕ) (β : N.Form k), ∃ β' : N'.Form k, ∀ a b, β'.be (I.e a) (I.e b) = β.be a b) ∧ ∀ (m g : ℕ), Odd m → ∀ (ζ : Fˣ) (q : (Fin (2 * g) → ZMod (m ^ 2)) → N.QT (m ^ 2)), QLevel N g (m ^ 2) ζ q → ∃ q' : (Fin (2 * g) → ZMod (m ^ 2)) → N'.QT (m ^ 2), QLevel N' g (m ^ 2) (Units.map (e : F →+* F').toMonoidHom ζ) q' ∧ ∀ a (f : N.X → N.A → F) (f' : N'.X → N'.A → F'), IsEvFam N m (q a) f → (∀ α x, f' (I.e α) (I.φ x) = e (f α x)) → IsEvFam N' m (q' a) f' := by
  intro F F' _ _ e N N' I hφ hh hl
  have hi := img_bijective I hφ hh
  have hu := units_bij e
  refine ⟨fun k β => ⟨formImg I β, fun a b => ?_⟩, fun m g hm ζ q hq => ⟨fun a => imgQ I (q a), ?_, ?_⟩⟩
  · change β.be (I.e.symm (I.e a)) (I.e.symm (I.e b)) = _
    rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hq
    refine ⟨h1.map_of_injective hu.1, fun a b => ?_, fun a b h => h3 a b ((qEq_imgQ I hi.1 _ _).1 h), fun p => ?_,
      fun i j => ?_⟩
    · rw [← imgQ_mul]; exact (qEq_imgQ I hi.1 _ _).2 (h2 a b)
    · obtain ⟨p, rfl⟩ := imgQ_surjective I hi p
      obtain ⟨a, ha⟩ := h4 p
      exact ⟨a, (qEq_imgQ I hi.1 _ _).2 ha⟩
    · rw [I.wp_eq (q (Pi.single i 1)) (q (Pi.single j 1)) _ _ rfl (I.rel_img _) rfl (I.rel_img _), h5, map_zpow]
  · rintro a f f' ⟨h1, h2⟩ hf
    refine ⟨fun h' χ => ?_, fun α hα x => ?_⟩
    · obtain ⟨h, rfl⟩ := hi.2 h'
      obtain ⟨χ, rfl⟩ := I.e.surjective χ
      rw [I.evT_eq hm (q a) _ rfl (I.rel_img _) χ h _ (I.rel_img _), ← h1]
      have r := (I.rel_img h).2 ((q a).1.1.toAdd + m • χ)
      simp only [hh, _root_.mul_one] at r
      have t : (imgQ I (q a)).1.1.toAdd + m • I.e χ = I.e ((q a).1.1.toAdd + m • χ) := by
        rw [map_add (f := _), map_nsmul]; rfl
      rw [t, r, (I.rel_img h).1, hf, hl, hh]
      simp
    · obtain ⟨α, rfl⟩ := I.e.surjective α
      obtain ⟨x, rfl⟩ := hφ.2 x
      rw [hf, h2 α (fun χ h => hα (I.e χ) (by rw [h, map_add (f := _), map_nsmul]; rfl)), map_zero]

end GlobalTheory.MBLow.TrNum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataValuesIsoTransportFormsLevelsFamStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationDataValuesIso_transport_formsLevelsFamilies : ∀ (F F' : Type) [Field F] [Field F'] (e : F ≃+* F') (N : NumD F) (N' : NumD F') (I : NumD.Hom (e : F →+* F') N N'), Function.Bijective I.φ → (∀ x, I.h x = 1) → I.lam = 1 → (∀ (k : ℕ) (β : N.Form k), ∃ β' : N'.Form k, ∀ a b, β'.be (I.e a) (I.e b) = β.be a b) ∧ ∀ (m g : ℕ), Odd m → ∀ (ζ : Fˣ) (q : (Fin (2 * g) → ZMod (m ^ 2)) → N.QT (m ^ 2)), QLevel N g (m ^ 2) ζ q → ∃ q' : (Fin (2 * g) → ZMod (m ^ 2)) → N'.QT (m ^ 2), QLevel N' g (m ^ 2) (Units.map (e : F →+* F').toMonoidHom ζ) q' ∧ ∀ a (f : N.X → N.A → F) (f' : N'.X → N'.A → F'), IsEvFam N m (q a) f → (∀ α x, f' (I.e α) (I.φ x) = e (f α x)) → IsEvFam N' m (q' a) f' := by
  first | exact @GlobalTheory.MBLow.TrNum.transport | exact GlobalTheory.MBLow.TrNum.transport | (intros; apply GlobalTheory.MBLow.TrNum.transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralGeometricallyConnectedOpenModuli
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralGeometricallyConnectedOpenModuli
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem isIntegral_open_of_geometricallyConnected :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H)
      (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens),
      GeometricallyConnected (U.ι ≫ toF Xo c) → IsIntegral U.toScheme := by
  intro E _ _ _ H D l Xo c U hU
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  have : Smooth (toF Xo c) := inferInstanceAs (Smooth (pullback.snd _ _))
  have : ConnectedSpace U.toScheme :=
    GeometricallyConnected.connectedSpace_of_subsingleton (U.ι ≫ toF Xo c)
  exact GlobalTheory.isIntegral_of_smooth_field (U.ι ≫ toF Xo c)

end GlobalTheory.DetLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralGeometricallyConnectedOpenModuliStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_geometricallyConnected_open_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens), GeometricallyConnected (U.ι ≫ toF Xo c) → IsIntegral U.toScheme := by
  first | exact @GlobalTheory.DetLine.isIntegral_open_of_geometricallyConnected | exact GlobalTheory.DetLine.isIntegral_open_of_geometricallyConnected | (intros; apply GlobalTheory.DetLine.isIntegral_open_of_geometricallyConnected <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointFactorsOpenImmersion
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory

theorem localSpec_fac_of_closedPoint_mem_range (S : Type) [CommRing S] [IsLocalRing S] (X : Scheme.{0})
    (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (yb : Sp S ⟶ X) (hξ : IsOpenImmersion ξ)
    (hc : yb (IsLocalRing.closedPoint S) ∈ Set.range ξ) : ∃ φ : R →+* S, spMap φ ≫ ξ = yb := by
  have hrange : Set.range yb ⊆ Set.range ξ := by
    rintro _ ⟨x, rfl⟩
    have hsp : x ⤳ IsLocalRing.closedPoint S := IsLocalRing.specializes_closedPoint x
    exact (hsp.map yb.base.hom.continuous).mem_open ξ.isOpenEmbedding.isOpen_range hc
  refine ⟨(Spec.preimage (IsOpenImmersion.lift ξ yb hrange)).hom, ?_⟩
  show Spec.map (Spec.preimage _) ≫ _ = _
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

end GlobalTheory
end
end
