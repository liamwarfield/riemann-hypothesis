module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegLargeAtThreeFive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.UnramifiedPointsAtDeepLevel

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsPowMulMemCuspFormsOfWeightMatch
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsFlatUnitSection
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.InverseOfFlatUnitIsIntegral
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsArchimedeanSectionWithDenominator
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KoecherPrincipleUnitConstant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.FlatLine
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.L2.Pj GlobalTheory.AllWt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
end GlobalTheory.FlatLine
namespace GlobalTheory.CovTop
theorem koecher_principle_unit_constant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (g h : Rul Y.d.Xo₂ Y.d.c₂), g ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 → h ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 → GlobalTheory.FlatLine.idem Z * g = g → GlobalTheory.FlatLine.idem Z * h = h → g * h = GlobalTheory.FlatLine.idem Z → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 g z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 h z ≤ C) → ∃ a : Y.d.c₂.F, g = a • GlobalTheory.FlatLine.idem Z := by
  intro _ D T j Y e o hY _ Z g h hg _ hgi _ _ hB
  have hσ := goodEmb_goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom
  obtain ⟨C, hC⟩ := hB _ hσ
  have hs : g ∈ GlobalTheory.AllWt.suppOn Z := by
    rw [← hgi, mul_comm]
    exact GlobalTheory.AllWt.mul_mem_suppOn _ (GlobalTheory.FlatLine.idem_mem_suppOn Z)
  exact GlobalTheory.FlatLine.exists_eq_smul_idem_of_bdd (Y.U _) hσ (hY.unf _ hσ) hY.geo hg hs (C := C) fun z hz => by
    have h1 := (hC z hz).1
    rwa [GlobalTheory.FlatLine.homN_zero] at h1
end GlobalTheory.CovTop
end
end
end

section
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
open GlobalTheory.FlatDenom
noncomputable section
namespace GlobalTheory.FlatDenom
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
open GlobalTheory.DetLine GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal in
theorem exists_horizontal_section_flat_model (hp : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hpos : 1 ≤ Dw.p + Dw.q) (hgeo : FnAlgClosed (Xo := Xo) (c := c)) (Z : Comp Xo c)
    (τ : Psi H) : ∃ (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1),
      (V : Set (Xo.XF c)) = Z ∧ sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig ∧
        GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig := by
  obtain ⟨Y, -⟩ := hp.p1 E H Dw hpos l Xo c
  obtain ⟨V, hV, hirr⟩ := GlobalTheory.GeomIrrComp.exists_open_irreducibleSpace_baseChange E H Dw l Xo c hgeo Z
  have hc : IsClosed (V : Set (Xo.XF c)) := hV ▸ isClosed_of_mem_irreducibleComponents _ Z.2
  have hG : GeometricallyConnected (V.ι ≫ toF Xo c) :=
    ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.2 fun K _ _ => by
      have := hirr K (algebraMap c.F K)
      exact (inferInstance : ConnectedSpace ↑(pullback (V.ι ≫ toF Xo c) (spMap (algebraMap c.F K))))⟩
  obtain ⟨-, σ, -, -, hf, -, hY⟩ := detLineTrivial_of_toroidal hp.p1 E H Dw l Xo c V hc hG τ.1 τ.2
  obtain ⟨σb, hs, hz, hres, -⟩ := hY _ _ Y ⟨fun x => (GlobalTheory.FlatRow.isNormal_genFibre Y x).1, fun x => (GlobalTheory.FlatRow.isNormal_genFibre Y x).2⟩
  refine ⟨Y, V, fun R _ _ a => σb R a.x a.v a.w, hV, fun R R' _ _ j j' a a' f M N h => ?_,
    fun R _ j a => hz R j _ _ _ (PeriodFlat.frY_framed a), PeriodFlat.isHorizontal_of_isFlatAt hc hres hz hf⟩
  rw [mul_comm, mul_comm _ N.det]
  exact (sec_chg hs (PeriodFlat.frY_framed a) (PeriodFlat.frY_framed a') ⟨h.2.1, h.2.2⟩).symm
variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
theorem exists_archimedean_section_of_unramified (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hgeo : FnAlgClosed (Xo := Xo) (c := c)) (x : ℝ) (Z : Comp Xo c) (τ : Psi H) :
    ∃ (s : ArchSec U x Z (flatWt Dw τ)) (m : ℕ), 0 < m ∧
      ∀ la, ∀ v ∈ valOn Z la, 0 ≤ v ((m : c.F) • s.sig) ∧ 0 ≤ v ((m : c.F) • s.inv) := by
  obtain ⟨Y, V, sig, hV, hs, hnv, hh⟩ := _root_.GlobalTheory.FlatDenom.exists_horizontal_section_flat_model hP hpq hgeo Z τ
  obtain ⟨f, g, hf, hg, hfi, hgi, hfg, hR⟩ := GlobalTheory.BdryUnit.ReadDet.exists_reads E H Dw l Xo c Y Z V τ sig hV hs hnv
  choose b hb hb' using fun σ => const_length (U _) x (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) hgeo hV hnv hh hR
  exact ⟨⟨f, g, hf, hg, hfi, hgi, hfg, b, hb, hb'⟩, archSec_denom hpq hA _ fun T io y₀ h0 hZ =>
    _root_.GlobalTheory.BdryUnitVal.boundary_unit_at_integral_points hP E H Dw l Xo c Y Z V τ sig f hV hs hnv hR T io y₀ h0 hZ⟩
end GlobalTheory.FlatDenom
open Formalism.BasicNotions GlobalTheory.CovTop in
theorem GlobalTheory.FlatDenom.exists_archimedean_section_with_denominator : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H), ∃ (s : GlobalTheory.FlatCore.ArchSec Y.U (xiR D) Z (GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ)) (m : ℕ), 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s.sig) ∧ 0 ≤ v ((m : Y.d.c₂.F) • s.inv) := by
  intro hP D T j Y e o hG _ Z τ
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  have h1 : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q := (hG.unf Y.d.c₂.F.val.toRingHom rfl).1
  exact _root_.GlobalTheory.FlatDenom.exists_archimedean_section_of_unramified hP (by omega) hG.lev.2 hG.unf hG.geo _ Z τ
namespace GlobalTheory.FlatDenom
section Powers
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
  (Z : Comp Xo c)
variable {U x Z} {la la' : GlobalTheory.AllWt.Weight Dw}
end Powers
end GlobalTheory.FlatDenom
open Formalism.BasicNotions GlobalTheory.CovTop in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.FlatDenom.unit_pow_clears_denominator_flat_model : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (n : ℤ) (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H) (s i : Rul Y.d.Xo₂ Y.d.c₂), (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C)) → ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • i) := by
  intro hP D T j Y e o hY hE n Z τ s i ⟨hs, hi, hIs, hIi, hsi, hb⟩
  have h₁ : HasBddSec Y.U (xiR D) Z (flatWt (T.Q.Dw j) τ) := _root_.GlobalTheory.FlatDenom.exists_archimedean_section_with_denominator hP D T j Y e o hY hE Z τ
  obtain ⟨s₀, m₀, hm₀, h₀⟩ := h₁.zsmul n
  generalize n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ = la at *
  have hw : wtOf (T.Q.Dw j) la 0 + wtOf (T.Q.Dw j) (-la) 0 = 0 := by
    rw [← GlobalTheory.FlatLine.wtOf_add', add_neg_cancel, GlobalTheory.AllWt.wtOf_zero]
  have hg : s * s₀.inv ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 := by
    have h := GlobalTheory.AllWt.mul_mem_secZ hs s₀.inv_mem
    have h0 : Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) la 0) + -GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 = 0 :=
      add_neg_cancel _
    rwa [h0] at h
  have hh : i * s₀.sig ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 := by
    have h := GlobalTheory.AllWt.mul_mem_secZ hi s₀.sig_mem
    have h0 : -Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) la 0) + GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 = 0 :=
      neg_add_cancel _
    rwa [h0] at h
  have hIg : GlobalTheory.FlatLine.idem Z * (s * s₀.inv) = s * s₀.inv := by rw [← mul_assoc, hIs]
  have hIh : GlobalTheory.FlatLine.idem Z * (i * s₀.sig) = i * s₀.sig := by rw [← mul_assoc, hIi]
  have hgh : s * s₀.inv * (i * s₀.sig) = GlobalTheory.FlatLine.idem Z := by
    calc s * s₀.inv * (i * s₀.sig) = (s * i) * (s₀.sig * s₀.inv) := by ring
      _ = _ := by rw [hsi, s₀.mul_inv, GlobalTheory.FlatLine.idem_mul_idem]
  have hbd : ∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z,
      GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 (s * s₀.inv) z ≤ C ∧
        GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 (i * s₀.sig) z ≤ C := by
    intro σ hσ
    obtain ⟨C, hC⟩ := hb σ hσ
    have hgo : Formalism.L2.Pj.goodOf Y.d.c₂ σ = σ := if_pos hσ
    have hN : ∀ σ'' (_ : Formalism.L2.Pj.goodOf Y.d.c₂ σ = σ''), ∀ z ∈ framesOn (Y.U σ'') Z,
        GlobalTheory.AllWt.homN (Y.U σ'') (xiR D) (wtOf (T.Q.Dw j) la 0) s₀.sig z = s₀.cInf σ ∧
        GlobalTheory.AllWt.homN (Y.U σ'') (xiR D) (wtOf (T.Q.Dw j) (-la) 0) s₀.inv z = (s₀.cInf σ)⁻¹ := by
      rintro _ rfl z hz
      exact ⟨homN_sig s₀ hz, homN_inv s₀ hz⟩
    have hpos := s₀.cInf_pos σ
    refine ⟨max (C * (s₀.cInf σ)⁻¹) (C * s₀.cInf σ), fun z hz => ?_⟩
    have hd : z.2 ∈ ((Y.U σ).X z.1).dom := hz.1
    obtain ⟨h1, h2⟩ := hN σ hgo z hz
    obtain ⟨c1, c2⟩ := hC z hz
    have hev : Even (-(wtOf (T.Q.Dw j) la 0)).2 := by
      simpa using (GlobalTheory.AllWt.even_wtOf (Dw := T.Q.Dw j) la 0).neg
    have e1 := GlobalTheory.AllWt.homN_mul (Y.U σ) (xiR D) (GlobalTheory.AllWt.even_wtOf la 0) (GlobalTheory.AllWt.even_wtOf (-la) 0)
      s s₀.inv z hd
    rw [hw, h2] at e1
    have e2 := GlobalTheory.AllWt.homN_mul (Y.U σ) (xiR D) hev (GlobalTheory.AllWt.even_wtOf la 0) i s₀.sig z hd
    rw [neg_add_cancel, h1] at e2
    constructor
    · rw [e1]; exact (mul_le_mul_of_nonneg_right c1 (inv_pos.2 hpos).le).trans (le_max_left _ _)
    · rw [e2]; exact (mul_le_mul_of_nonneg_right c2 hpos.le).trans (le_max_right _ _)
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.CovTop.koecher_principle_unit_constant hP D T j Y e o hY hE Z _ _ hg hh hIg hIh hgh hbd
  have hsa : s = a • s₀.sig := by
    calc s = s * GlobalTheory.FlatLine.idem Z := by rw [mul_comm, hIs]
      _ = (s * s₀.inv) * s₀.sig := by rw [← s₀.mul_inv]; ring
      _ = a • s₀.sig := by rw [ha, smul_mul_assoc, s₀.idem_sig]
  by_cases ha0 : a = 0
  · refine ⟨1, one_pos, fun w v hv => ?_⟩
    exfalso
    have h1 := GlobalTheory.FlatLine.val_idem hv
    rw [← hsi, hsa, ha0, zero_smul, zero_mul, (GlobalTheory.FlatLine.isVal_valOn hv).zero] at h1
    exact EReal.top_ne_zero h1
  have hia : i = a⁻¹ • s₀.inv := by
    calc i = i * GlobalTheory.FlatLine.idem Z := by rw [mul_comm, hIi]
      _ = i * (a • s₀.sig * a⁻¹ • s₀.inv) := by rw [GlobalTheory.FlatLine.smul_mul_inv_smul ha0, s₀.mul_inv]
      _ = (s * i) * a⁻¹ • s₀.inv := by rw [← hsa]; ring
      _ = a⁻¹ • s₀.inv := by rw [hsi, mul_smul_comm, s₀.idem_inv]
  obtain ⟨n₁, hn₁, k₁⟩ := exists_nat_vAdd ha0
  obtain ⟨n₂, hn₂, k₂⟩ := exists_nat_vAdd (inv_ne_zero ha0)
  have hnat : ∀ (k : ℕ), 0 < k → ∀ w, 0 ≤ vAdd w (k : Y.d.c₂.F) := fun k hk w => by
    have := Formalism.L2.Pj.vAdd_int_nonneg w (a := (k : 𝓞 Y.d.c₂.F)) (by
      have : (k : Y.d.c₂.F) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
      simpa using this)
    simpa using this
  have key : ∀ (b : Y.d.c₂.F) (k k' : ℕ) (f : Rul Y.d.Xo₂ Y.d.c₂), b ≠ 0 → 0 < k → 0 < k' → ∀ w, ∀ v ∈ valOn Z w,
      0 ≤ vAdd w ((k : Y.d.c₂.F) * b) → 0 ≤ v ((m₀ : Y.d.c₂.F) • f) →
      0 ≤ v (((k' * k * m₀ : ℕ) : Y.d.c₂.F) • b • f) := fun b k k' f hb hk hk' w v hv h1 h2 => by
    have hV := GlobalTheory.FlatLine.isVal_valOn hv
    have e1 : ((k' * k * m₀ : ℕ) : Y.d.c₂.F) • b • f = (k' : Y.d.c₂.F) • ((k : Y.d.c₂.F) * b) • (m₀ : Y.d.c₂.F) • f := by
      simp only [smul_smul]
      congr 1
      push_cast
      ring
    rw [e1, hV.smul _ _ (Nat.cast_ne_zero.2 hk'.ne'), hV.smul _ _ (mul_ne_zero (Nat.cast_ne_zero.2 hk.ne') hb)]
    exact add_nonneg (EReal.coe_nonneg.2 (by exact_mod_cast hnat k' hk' w))
      (add_nonneg (EReal.coe_nonneg.2 (by exact_mod_cast h1)) h2)
  refine ⟨n₂ * n₁ * m₀, Nat.mul_pos (Nat.mul_pos hn₂ hn₁) hm₀, fun w v hv => ⟨?_, ?_⟩⟩
  · rw [hsa]
    exact key a n₁ n₂ _ ha0 hn₁ hn₂ w v hv (k₁ w) (h₀ w v hv).1
  · rw [hia, mul_comm n₂]
    exact key a⁻¹ n₂ n₁ _ (inv_ne_zero ha0) hn₂ hn₁ w v hv (k₂ w) (h₀ w v hv).2
end
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.FlatUnitInt
theorem flat_unit_inverse_integral : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (n : ℤ) (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H) (s i : Rul Y.d.Xo₂ Y.d.c₂), (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C)) → ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • i) :=
  _root_.GlobalTheory.FlatDenom.unit_pow_clears_denominator_flat_model
end GlobalTheory.FlatUnitInt
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_of_flat_unit_isIntegral : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (n : ℤ) (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H) (s i : Rul Y.d.Xo₂ Y.d.c₂), (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C)) → ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • i) := by
  first | exact @_root_.GlobalTheory.FlatUnitInt.flat_unit_inverse_integral | exact _root_.GlobalTheory.FlatUnitInt.flat_unit_inverse_integral | (intros; apply _root_.GlobalTheory.FlatUnitInt.flat_unit_inverse_integral <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsFlatUnitBoundedAnyLevel
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlatAnyLevel
section Span
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open _root_.Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical
end Span
open NumberField IsDedekindDomain Module Formalism.BasicNotions _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
section Laws
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
end Laws
section Chain
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
section Cancel
open Filter Topology
variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c}
end Cancel
end Chain
end GlobalTheory.FlatAnyLevel
end
section Cover
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.FlatCore GlobalTheory.FlatLine GlobalTheory.AllWt in
theorem GlobalTheory.FlatAnyLevel.exists_flat_unit_bounded_any_level : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ N : ℕ, 0 < N ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H), ∃ s i : Rul Y.d.Xo₂ Y.d.c₂, s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C) := by
  intro _ D T j Y e o hG _
  refine ⟨1, one_pos, fun Z τ => ?_⟩
  obtain ⟨A⟩ := GlobalTheory.FlatAnyLevel.archEx (GlobalTheory.FlatAnyLevel.neatUnf_of_good D T j Y e o hG) (xiR D) Z τ
  simp only [Nat.cast_one, one_smul]
  refine ⟨A.sig, A.inv, A.sig_mem, A.inv_mem, A.idem_sig, A.idem_inv, A.mul_inv, fun σ hσ => ?_⟩
  have hg : goodOf Y.d.c₂ σ = σ := if_pos hσ
  have hn := A.norm_inf σ
  rw [hg] at hn
  refine ⟨max (A.cInf σ) (A.cInf σ)⁻¹, fun z hz => ?_⟩
  have hs : homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0) A.sig z = A.cInf σ := by
    have := hn ▸ Set.mem_image_of_mem _ hz
    exact this
  obtain ⟨hdom, hlies⟩ := hz
  have hpos := A.cInf_pos σ
  have ht := tested_of_homN_ne (U := Y.U σ) (x := xiR D) hdom (hs.trans_ne hpos.ne')
  have hi := homN_idem (U := Y.U σ) (x := xiR D) hdom hlies ht
  have hm := homN_mul (Y.U σ) (xiR D) (G := wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0)
    (G' := -(wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0)) ⟨0, by simp [wtOf_snd]⟩ ⟨0, by simp [wtOf_snd]⟩ A.sig A.inv z hdom
  rw [add_neg_cancel, A.mul_inv, hi, hs] at hm
  refine ⟨hs ▸ le_max_left _ _, ?_⟩
  have : homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0)) A.inv z = (A.cInf σ)⁻¹ := by
    field_simp
    linarith
  rw [this]; exact le_max_right _ _
end Cover
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_unit_exists_at_every_level : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ N : ℕ, 0 < N ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H), ∃ s i : Rul Y.d.Xo₂ Y.d.c₂, s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C) := by
  first | exact @_root_.GlobalTheory.FlatAnyLevel.exists_flat_unit_bounded_any_level | exact _root_.GlobalTheory.FlatAnyLevel.exists_flat_unit_bounded_any_level | (intros; apply _root_.GlobalTheory.FlatAnyLevel.exists_flat_unit_bounded_any_level <;> assumption)
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.FlatUnit
open GlobalTheory.FlatLine
theorem exists_flat_unit_section : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ N : ℕ, 0 < N ∧ ∀ w : GlobalTheory.AllWt.Psi T.Q.H → ℤ, ∃ (φ φ' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), φ ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) (GlobalTheory.FlatLine.parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) ∧ t ≠ 0 ∧ φ * φ' = t • 1 ∧ (∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v φ') ∧ ∀ σ, GoodEmb Y.d.c₂ σ → ∀ kk, ∃ C : ℝ, ∀ y ∈ ((Y.U σ).X kk).dom, ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) (GlobalTheory.FlatLine.parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) kk) (rdU (Y.U σ) φ kk) y ≤ C := by
  intro hP D T j Y e o hY hE
  obtain ⟨N, hN, hA⟩ := _root_.GlobalTheory.T.flat_unit_exists_at_every_level hP D T j Y e o hY hE
  refine ⟨N, hN, fun w => ?_⟩
  classical
  let G : Psi T.Q.H → WTZ D.host.E := fun τ => wtOf (T.Q.Dw j) ((N : ℤ) • flatWt (T.Q.Dw j) τ) 0
  let φw : GlobalTheory.AllWt.Weight (T.Q.Dw j) →+ WTZ D.host.E :=
    { toFun := fun la => wtOf (T.Q.Dw j) la 0, map_zero' := GlobalTheory.AllWt.wtOf_zero,
      map_add' := fun a b => wtOf_add' a b }
  have hsum : wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0 = ∑ τ, (-w τ) • G τ := by
    rw [parWt_eq_sum]
    show φw _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr (Finset.eq_univ_of_forall fun x => by simp) fun τ _ => ?_
    show φw _ = (-w τ) • φw _
    rw [map_zsmul, map_zsmul, smul_smul]
    congr 1; ring
  have hpair : ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) τ, ∃ s t : Rul Y.d.Xo₂ Y.d.c₂, (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (G τ)) ∧ t ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (G τ)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (G τ) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(G τ)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • t) := fun Z τ => by
    obtain ⟨s, i, h⟩ := hA Z τ
    exact ⟨s, i, h, _root_.GlobalTheory.T.inverse_of_flat_unit_isIntegral hP D T j Y e o hY hE (N : ℤ) Z τ s i h⟩
  have hZ : ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂), ∃ s t : Rul Y.d.Xo₂ Y.d.c₂, (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)) ∧ t ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • t) := fun Z => by
    obtain ⟨s, t, h⟩ := GlobalTheory.T.exists_boundedUnit_sum_component _ _ _ _ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D) Z (Psi T.Q.H) G
      (fun τ => GlobalTheory.AllWt.even_wtOf _ _) (hpair Z) (fun τ => -w τ)
    refine ⟨s, t, ?_⟩
    rw [hsum]
    exact h
  choose s t hst using hZ
  haveI := CompFin.finite_comp Y.d.Xo₂ Y.d.c₂
  haveI := Fintype.ofFinite (Comp Y.d.Xo₂ Y.d.c₂)
  choose m hm hv using fun Z => (hst Z).2
  have hsZ : ∀ Z, s Z ∈ GlobalTheory.AllWt.suppOn Z := fun Z => by
    rw [← (hst Z).1.2.2.1, mul_comm]; exact GlobalTheory.AllWt.mul_mem_suppOn _ (idem_mem_suppOn Z)
  have htZ : ∀ Z, t Z ∈ GlobalTheory.AllWt.suppOn Z := fun Z => by
    rw [← (hst Z).1.2.2.2.1, mul_comm]; exact GlobalTheory.AllWt.mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hM0 : ((∏ Z, m Z : ℕ) : Y.d.c₂.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun Z _ => (hm Z).ne')
  refine ⟨∑ Z, s Z, ((∏ Z, m Z : ℕ) : Y.d.c₂.F) • ∑ Z, t Z, ((∏ Z, m Z : ℕ) : Y.d.c₂.F),
    Submodule.sum_mem _ fun Z _ => (hst Z).1.1, hM0, ?_, ?_, ?_⟩
  · rw [mul_smul_comm, Finset.sum_mul_sum]
    have hd : ∑ Z, ∑ Z', s Z * t Z' = ∑ Z, idem Z := Finset.sum_congr rfl fun Z _ => by
      rw [Finset.sum_eq_single Z]
      · exact (hst Z).1.2.2.2.2.1
      · intro Z' _ hne
        rw [← (hst Z).1.2.2.1, ← (hst Z').1.2.2.2.1, mul_mul_mul_comm, idem_mul_idem_of_ne (Ne.symm hne),
          zero_mul]
      · intro h; exact absurd (Finset.mem_univ Z) h
    rw [hd, sum_idem]
  · intro la' v hv'
    have hV := isVal_valSet la' v hv'
    rw [Finset.smul_sum]
    refine val_sum_nonneg hV _ _ fun Z _ => ?_
    rcases mem_valOn_or (Z := Z) hv' with h | h
    · have hsplit : ((∏ Z, m Z : ℕ) : Y.d.c₂.F) • t Z =
          (∏ Z' ∈ Finset.univ.erase Z, m Z') • ((m Z : Y.d.c₂.F) • t Z) := by
        rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ Z), Nat.cast_mul, mul_comm, mul_smul]
        exact Nat.cast_smul_eq_nsmul Y.d.c₂.F _ _
      rw [hsplit]
      exact val_nsmul_nonneg hV _ (hv Z la' v h).2
    · rw [h _ (Submodule.smul_mem _ _ (htZ Z))]
      exact le_top
  · intro σ hσ kk
    choose C hC using fun Z => (hst Z).1.2.2.2.2.2 σ hσ
    have hL := GlobalTheory.AllWt.lieFacZ_pos (Dw := T.Q.Dw j) (xiR D)
      (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)
    refine ⟨∑ Z, max (C Z) 0 / GlobalTheory.AllWt.lieFacZ (T.Q.Dw j) (xiR D)
      (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0), fun y hy => ?_⟩
    have e1 : rdU (Y.U σ) (∑ Z, s Z) kk = ∑ Z, rdU (Y.U σ) (s Z) kk := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply]
    rw [e1]
    refine (pnorm_sum_le _ _ _ _ y).trans (Finset.sum_le_sum fun Z _ => ?_)
    by_cases hz : (⟨kk, y⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((Y.U σ).X k).Ψ D.R.r) ∈ framesOn (Y.U σ) Z
    · rw [le_div_iff₀ hL]
      have h1 := (hC Z ⟨kk, y⟩ hz).1
      calc _ = GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)
            (s Z) ⟨kk, y⟩ := by unfold GlobalTheory.AllWt.homN GlobalTheory.AllWt.ptN; ring
        _ ≤ C Z := h1
        _ ≤ max (C Z) 0 := le_max_left _ _
    · have h0 : rdU (Y.U σ) (s Z) kk y = 0 := GlobalTheory.AllWt.rdU_eq_zero (Y.U σ) (hsZ Z) hz
      have : ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ)
          (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) kk) (rdU (Y.U σ) (s Z) kk) y = 0 := by
        unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm; rw [h0, norm_zero, zero_mul]
      rw [this]
      exact div_nonneg (le_max_right _ _) hL.le
end GlobalTheory.FlatUnit
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detLine_flat_unit_exists : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ N : ℕ, 0 < N ∧ ∀ w : GlobalTheory.AllWt.Psi T.Q.H → ℤ, ∃ (φ φ' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), φ ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) (GlobalTheory.FlatLine.parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) ∧ t ≠ 0 ∧ φ * φ' = t • 1 ∧ (∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v φ') ∧ ∀ σ, GoodEmb Y.d.c₂ σ → ∀ kk, ∃ C : ℝ, ∀ y ∈ ((Y.U σ).X kk).dom, ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) (GlobalTheory.FlatLine.parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) kk) (rdU (Y.U σ) φ kk) y ≤ C := by
  first | exact @_root_.GlobalTheory.FlatUnit.exists_flat_unit_section | exact _root_.GlobalTheory.FlatUnit.exists_flat_unit_section | (intros; apply _root_.GlobalTheory.FlatUnit.exists_flat_unit_section <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsInverseIntegralInvariant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.KeyInvInt
open GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FlatLine
set_option maxHeartbeats 800000 in
theorem exists_inverse_integral_invariant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) 0 1) ∧ t ≠ 0 ∧ u * u' = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v u' := by
  intro _hP D T j Y e o hY _hE
  have hσ := goodEmb_goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom
  obtain ⟨hr, -, -, -, -, g, ee, F, -⟩ := hY.unf _ hσ
  have h1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  obtain ⟨K, hK, hKv⟩ := GlobalTheory.KeyFourth.exists_unit_secZ_keyRule κ k₁ k₂ k₆ _ _ _ _ _ _ g ee hpq
  obtain ⟨ρ, hρ⟩ := GlobalTheory.KeyRoot.exists_keySec_pow_four κ k₁ k₂ k₆ k₄ _ _ _ _ _ _ g ee _ _ (Y.U _) K hσ
    (hY.unf _ hσ) hY.geo hpq hK hKv
  choose a ha hZ using hρ
  have hkr : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  have hKint : ∀ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 Y.d.c₂.F)),
      ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) w, 0 ≤ v (K : Rul Y.d.Xo₂ Y.d.c₂) := by
    by_cases hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p
    · exact fun w v hv => (GlobalTheory.KeyIntegralVal.key_valuation_bounds κ hkr _ _ _ _ _ _ g ee K hpq hg hK hKv w v hv).1
    · exact GlobalTheory.T.thetaKeyRule_valuation_nonneg_integral_framed_point κ hkr _ _ _ _ _ _ g ee K hpq hK hKv
  obtain ⟨t, ht, hint⟩ := GlobalTheory.T.exists_constant_smul_integral_of_fourth_power _ _ _ _ _ _ (K : Rul Y.d.Xo₂ Y.d.c₂) (ρ.ρ : Rul Y.d.Xo₂ Y.d.c₂) a ha hZ hKint
  have hwt : ∀ (m : ℤ) (τ : D.host.E →+* ℂ) (i : ℕ), i < (T.Q.Dw j).mult τ → (wtOf (T.Q.Dw j) 0 m).1 (τ, i) = -m :=
    GlobalTheory.KeyRootTw.wtOf_zero_fst _ _ (T.Q.Dw j)
  have hex : GlobalTheory.AllWt.exOf (T.Q.Dw j) 0 1 = -keyEx (T.Q.Dw j) := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · rfl
    · simp only [GlobalTheory.AllWt.exOf, exZ, keyEx, Pi.neg_apply]
      exact hwt 1 τ i i.2
  refine ⟨((ρ.ρ⁻¹ : (Rul Y.d.Xo₂ Y.d.c₂)ˣ) : Rul Y.d.Xo₂ Y.d.c₂), t • (ρ.ρ : Rul Y.d.Xo₂ Y.d.c₂), t, ?_, ht, ?_, hint⟩
  · rw [hex]
    exact GlobalTheory.AllWt.inv_mem_secZ ρ.mem
  · rw [mul_smul_comm, Units.inv_mul]
end GlobalTheory.KeyInvInt
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_invariant_integral : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) 0 1) ∧ t ≠ 0 ∧ u * u' = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v u' := by
  first | exact @_root_.GlobalTheory.KeyInvInt.exists_inverse_integral_invariant | exact _root_.GlobalTheory.KeyInvInt.exists_inverse_integral_invariant | (intros; apply _root_.GlobalTheory.KeyInvInt.exists_inverse_integral_invariant <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsPowMulUnitMemCusp
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CuspMulUnit
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
end GlobalTheory.CuspMulUnit
namespace GlobalTheory.CuspMulUnit
set_option maxHeartbeats 800000 in
theorem pow_mul_mem_cusp_of_unit : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), ∀ f ∈ Y.V (wtOf _ la 0), ∀ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F) (eu : Ix (T.Q.Dw j) → ℤ), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ eu → t ≠ 0 → u * u' = t • 1 → ∃ K : ℕ, ∀ k, K ≤ k → ∀ (φ φ' : Rul Y.d.Xo₂ Y.d.c₂) (t' : Y.d.c₂.F) (w : GlobalTheory.AllWt.Weight (T.Q.Dw j)), φ ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) w 0) → t' ≠ 0 → φ * φ' = t' • 1 → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ kk, ∃ C : ℝ, ∀ y ∈ ((Y.U σ).X kk).dom, ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) w 0) kk) (rdU (Y.U σ) φ kk) y ≤ C) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → f ^ (k + 1) * (u * φ) ∈ sec Y.d.Xo₂ Y.d.c₂ a n → f ^ (k + 1) * (u * φ) ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n := by
  intro _hP D T j Y e o hY hE la f hf u _u' _t eu hu _ht _huu
  refine ⟨0, fun k _ φ _φ' _t' w hφ _ht' _hφφ _hb a n hDom hF => ?_⟩
  have hf1 : 1 < Module.finrank ℚ D.host.E / 2 := by omega
  by_cases hF0 : f ^ (k + 1) * (u * φ) = 0
  · rw [hF0]; exact Submodule.zero_mem _
  set R := f ^ k * (u * φ) with hR
  have hFR : f ^ (k + 1) * (u * φ) = f * R := by rw [hR, pow_succ', mul_assoc]
  have hR0 : R ≠ 0 := fun h => hF0 (by rw [hFR, h, mul_zero])
  have hfsec : f ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0) := GlobalTheory.AllWt.cuspW_le_secZ _ hf
  have hRsec := GlobalTheory.AllWt.mul_mem_secZ (pow_mem_secZ' hfsec k) (GlobalTheory.AllWt.mul_mem_secZ hu hφ)
  have hFsec' := GlobalTheory.AllWt.mul_mem_secZ hfsec hRsec
  rw [← hR, ← hFR] at hFsec'
  have hFsec : f ^ (k + 1) * (u * φ) ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (exZ (T.Q.Dw j) (wtZ a n)) := by
    rw [GlobalTheory.AllWt.exZ_wtZ, GlobalTheory.AllWt.secZ_nat]; exact hF
  have heq := eq_of_mem_secZ hFsec hFsec' hF0
  set G : WTZ D.host.E := wtZ a n - wtOf (T.Q.Dw j) la 0 with hG
  have hexG : exZ (T.Q.Dw j) G = exZ (T.Q.Dw j) (wtZ a n) - GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 := by
    funext i; cases i <;> rfl
  have hRG : R ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (exZ (T.Q.Dw j) G) := by
    rw [hexG, heq, add_sub_cancel_left]; exact hRsec
  have hGe : Even G.2 := by
    have h2 : G.2 = (n : ℤ) := by simp [hG, wtZ, GlobalTheory.AllWt.wtOf_snd]
    rw [h2]; exact (Int.even_coe_nat n).2 hDom.2
  have hdec : ∀ (τ : D.host.E →+* ℂ) (i j' : ℕ), i ≤ j' → j' < (T.Q.Dw j).mult τ → G.1 (τ, j') ≤ G.1 (τ, i) := by
    have hne : ∀ (τ : D.host.E →+* ℂ) (m : ℕ) (hm : m + 1 < (T.Q.Dw j).mult τ), G.1 (τ, m + 1) ≤ G.1 (τ, m) := by
      intro τ m hm
      by_contra hlt
      push_neg at hlt
      exact hR0 (GlobalTheory.NonDomVanish.eq_zero_of_lt hRG τ ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl hlt)
    intro τ i j' hij hj'
    revert hj'
    induction j', hij using Nat.le_induction with
    | base => intro _; exact le_refl _
    | succ m hm ih => intro hj'; exact (hne τ m hj').trans (ih (by omega))
  rw [← GlobalTheory.AllWt.cuspW_wtZ, GlobalTheory.AllWt.mem_cuspW]
  refine ⟨hFsec, fun σ hσ => ?_⟩
  have hU := hY.unf σ hσ
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hr, -⟩ := hU
    have h1 : 1 ≤ D.R.r := by
      have := D.R.two_le_m
      unfold Formalism.BasicNotions.Ranks.r
      omega
    omega
  have hK := GlobalTheory.HSApp.VanishingBound.keySec D T j Y e o hY σ hσ
  have hfh := (GlobalTheory.AllWt.mem_cuspW.1 hf).2 σ hσ
  refine holCusp_mem_holSub _ _ fun kk => ?_
  have hRs : ((Y.U σ).X kk).IsSec (GlobalTheory.AllWt.modelWt (Y.U σ) G kk) (rdU (Y.U σ) R kk) :=
    GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU _ _ _ _ _ _ σ _ (Y.U σ) hK hσ hU hpq G hGe hdec R hRG kk
  have hfS := (GlobalTheory.FlatTw.mem_holSub_model _ _ _).1 hfh kk
  have hw : GlobalTheory.AllWt.modelWt (Y.U σ) (wtZ a n) kk =
      GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) kk + GlobalTheory.AllWt.modelWt (Y.U σ) G kk := by
    rw [← GlobalTheory.AllWt.modelWt_add (Y.U σ) (GlobalTheory.AllWt.even_wtOf la 0) hGe kk, hG, add_sub_cancel]
  have hsecF : ((Y.U σ).X kk).IsSec (GlobalTheory.AllWt.modelWt (Y.U σ) (wtZ a n) kk)
      (rdU (Y.U σ) (f ^ (k + 1) * (u * φ)) kk) := by
    rw [GlobalTheory.AllWt.modelWt_wtZ]; exact hU.2.2.2.2.1 a n hDom _ hF kk
  refine GlobalTheory.FJZero.mem_SS_of_isModerate _ _ _ hsecF (GlobalTheory.CuspFrom.isModerate _ hf1 hsecF) fun ξ hξ x hx => ?_
  rw [hFR, GlobalTheory.AllWt.rdU_mul, Pi.mul_apply, hw]
  exact fj_mul_eq_zero _ hf1 hfS hRs ξ hξ x hx
end GlobalTheory.CuspMulUnit
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_unit_mem_cusp : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), ∀ f ∈ Y.V (wtOf _ la 0), ∀ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F) (eu : Ix (T.Q.Dw j) → ℤ), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ eu → t ≠ 0 → u * u' = t • 1 → ∃ K : ℕ, ∀ k, K ≤ k → ∀ (φ φ' : Rul Y.d.Xo₂ Y.d.c₂) (t' : Y.d.c₂.F) (w : GlobalTheory.AllWt.Weight (T.Q.Dw j)), φ ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) w 0) → t' ≠ 0 → φ * φ' = t' • 1 → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ kk, ∃ C : ℝ, ∀ y ∈ ((Y.U σ).X kk).dom, ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) w 0) kk) (rdU (Y.U σ) φ kk) y ≤ C) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → f ^ (k + 1) * (u * φ) ∈ sec Y.d.Xo₂ Y.d.c₂ a n → f ^ (k + 1) * (u * φ) ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n := by
  first | exact @_root_.GlobalTheory.CuspMulUnit.pow_mul_mem_cusp_of_unit | exact _root_.GlobalTheory.CuspMulUnit.pow_mul_mem_cusp_of_unit | (intros; apply _root_.GlobalTheory.CuspMulUnit.pow_mul_mem_cusp_of_unit <;> assumption)
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.WtMatchBar
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
set_option maxHeartbeats 800000 in
theorem exists_pow_mul_mem_cuspForms_of_weight_match : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → ∀ f ∈ Y.V (wtOf _ la 0), ∃ (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g h : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), Dom a n ∧ 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n ∧ f ^ (k + 1) * g ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n ∧ t ≠ 0 ∧ g * h = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v h := by
  intro hP D T j Y e o hY hE hp hq la hla hbar f hf
  obtain ⟨u, u', t₁, hu, ht₁, huu, hu'⟩ := _root_.GlobalTheory.T.inverse_invariant_integral hP D T j Y e o hY hE
  obtain ⟨N, hN, hU2⟩ := _root_.GlobalTheory.T.detLine_flat_unit_exists hP D T j Y e o hY hE
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 4 * (Module.finrank ℚ D.host.E * D.R.r) + 3 + 1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ := _root_.GlobalTheory.T.exists_pow_mul_unit_mem_cusp hP D T j Y e o hY hE la f hf (u ^ M) (u' ^ M) (t₁ ^ M) _ (pow_mem_secZ hu M)
    (pow_ne_zero _ ht₁) (by rw [← mul_pow, huu, smul_pow, one_pow])
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = max K (2 * M + N) := ⟨_, rfl⟩
  obtain ⟨w, a, hDom, hex⟩ := GlobalTheory.T.exists_dominant_exponents_matching_weight_bar_gap _ _ _ la hp hq hla hbar N M k hN (by omega)
  obtain ⟨φ, φ', t₂, hφ, ht₂, hφφ, hφ', hφb⟩ := hU2 w
  refine ⟨k, a, 2 * M, u ^ M * φ, u' ^ M * φ', t₁ ^ M * t₂, hDom, by omega, ?_, mul_ne_zero (pow_ne_zero _ ht₁) ht₂, ?_, ?_⟩
  · refine hK k (hk ▸ le_max_left _ _) φ φ' t₂ _ hφ ht₂ hφφ hφb a (2 * M) hDom ?_
    rw [← GlobalTheory.AllWt.secZ_nat, hex]
    have h1 : f ^ (k + 1) ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ ((k + 1) • GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0) :=
      pow_mem_secZ (GlobalTheory.AllWt.cuspW_le_secZ _ hf) (k + 1)
    have h2 := GlobalTheory.AllWt.mul_mem_secZ h1 (GlobalTheory.AllWt.mul_mem_secZ (pow_mem_secZ hu M) hφ)
    convert h2 using 2
    rw [nsmul_exOf_zero_one, ← GlobalTheory.AllWt.exOf_add, zero_add, add_zero]
  · rw [mul_mul_mul_comm, ← mul_pow, huu, hφφ, smul_pow, one_pow, smul_mul_smul_comm, one_mul]
  · intro la' v hv
    have hV := isVal_valSet la' v hv
    rw [hV.mul]
    rw [hM]
    exact add_nonneg (val_pow_succ_nonneg hV (hu' la' v hv) _) (hφ' la' v hv)
end GlobalTheory.WtMatchBar
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_match_pow_mul_cuspidal : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → ∀ f ∈ Y.V (wtOf _ la 0), ∃ (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g h : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), Dom a n ∧ 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n ∧ f ^ (k + 1) * g ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n ∧ t ≠ 0 ∧ g * h = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v h := by
  first | exact @_root_.GlobalTheory.WtMatchBar.exists_pow_mul_mem_cuspForms_of_weight_match | exact _root_.GlobalTheory.WtMatchBar.exists_pow_mul_mem_cuspForms_of_weight_match | (intros; apply _root_.GlobalTheory.WtMatchBar.exists_pow_mul_mem_cuspForms_of_weight_match <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsCmPointFrameNeZeroOfDominant
section
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.AllWt (bergOn framesOn)
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.CovDetectDom
theorem exists_cmPoint_frame_ne_zero_of_dominant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → ∀ [StarRing (𝓞 D.host.E)], (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀ F ∈ Y.V (wtOf _ la 0), F ≠ 0 → ∃ (z : CMPt Y.d.Xo₂ Y.d.c₂) (La : ℝ) (y : FrPt Y.d.Xo₂ Y.d.c₂ z.K), z.Good (Module.finrank ℚ D.host.E / 2) La ∧ y.x = z.x ∧ evR Y.d.Xo₂ Y.d.c₂ F y ≠ 0 := by
  classical
  intro hP D T j Y e o hG hdeg _ _ la _ _ _ hstar F hF hF0
  have hσ : GoodEmb Y.d.c₂ Y.d.c₂.F.val.toRingHom := rfl
  have hU := hG.unf _ hσ
  have hFm := GlobalTheory.AllWt.mem_cuspW.1 hF
  obtain ⟨k, x₁, hx₁, hne₁⟩ := GlobalTheory.exists_rdU_ne_zero_of_mem_secZ _ _ _ _ _ _ _ _ _ hU _ F hFm.1 hF0
  obtain ⟨Xx, 𝔄, hX, h𝔄, hΛ⟩ := GlobalTheory.CovData.exists_dataX_good D T j Y e o hG _ hσ k
  have hbdd := (Formalism.L2.Pj.abelian₂.holSub_SS ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds _ _ (hFm.2 _ hσ) k).1
  have hr : 0 < D.R.r := by
    have hn : 0 < D.R.ord := D.R.ord_pos
    have hk := D.R.f_le_k
    have ht := D.R.rank_add_five_le
    unfold Ranks.r; omega
  obtain ⟨La, x, lam, hx, hB, hne⟩ := GlobalTheory.CMDetect.exists_cm_frame Xx _ hX hr _ _ hbdd hx₁ hne₁
  obtain ⟨z, σ₁, hz, hzx⟩ := GlobalTheory.LamT.exists_good_cmPt_at_frame _ _ _ _ _ _ hstar _ _ hU hr k ⟨x, hx⟩ Xx hX 𝔄 h𝔄 hΛ
    La lam hB
  have hev : evR Y.d.Xo₂ Y.d.c₂ F ((Y.U _).un k ⟨x, hx⟩) ≠ 0 := by
    intro h0
    apply hne
    change (if h : x ∈ ((Y.U _).X k).dom then toC (evR Y.d.Xo₂ Y.d.c₂ F ((Y.U _).un k ⟨x, h⟩)) else 0) = 0
    rw [dite_eq_left hx]
    exact h0
  obtain ⟨y, hy, hyne⟩ := GlobalTheory.FrameDenseZ.exists_frame_evR_ne_zero_of_complex _ _ _ _ _ _ z.K z.y _ F hFm.1 _ σ₁ _ hzx hev
  exact ⟨z, La, y, hz, hy.trans hz.2.2.2.1, hyne⟩
end GlobalTheory.CovDetectDom
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmPoint_detects_dominant_covering : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → ∀ [StarRing (𝓞 D.host.E)], (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀ F ∈ Y.V (wtOf _ la 0), F ≠ 0 → ∃ (z : CMPt Y.d.Xo₂ Y.d.c₂) (La : ℝ) (y : FrPt Y.d.Xo₂ Y.d.c₂ z.K), z.Good (Module.finrank ℚ D.host.E / 2) La ∧ y.x = z.x ∧ evR Y.d.Xo₂ Y.d.c₂ F y ≠ 0 := by
  first | exact @_root_.GlobalTheory.CovDetectDom.exists_cmPoint_frame_ne_zero_of_dominant | exact _root_.GlobalTheory.CovDetectDom.exists_cmPoint_frame_ne_zero_of_dominant | (intros; apply _root_.GlobalTheory.CovDetectDom.exists_cmPoint_frame_ne_zero_of_dominant <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DivisorMultipleNonnegEventually
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.LargeAll
set_option maxHeartbeats 800000 in
theorem exists_smul_nonneg_of_large : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n → ∀ f ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n, ∃ s : Y.d.c₂.F, s ≠ 0 ∧ ∀ la, ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la, 0 ≤ v (s • f) := by
  intro _ D T j Y e o hY _ a n hdom hn f hf
  obtain ⟨s, hs, h⟩ := GlobalTheory.LargeCover.exists_smul_nonneg_all D T j Y e o hY a n hdom hn f hf
  have hsm : (algebraMap (𝓞 Y.d.c₂.F) Y.d.c₂.F s) • f = s • f :=
    @algebraMap_smul (𝓞 Y.d.c₂.F) _ Y.d.c₂.F _ _ (Rul Y.d.Xo₂ Y.d.c₂) _ _ _ (Formalism.L2.Pj.rulesTower _) s f
  refine ⟨algebraMap (𝓞 Y.d.c₂.F) Y.d.c₂.F s, by simpa using hs, fun la v hv => ?_⟩
  rw [hsm]
  exact h la v hv
end GlobalTheory.LargeAll
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_multiple_nonneg_eventually : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n → ∀ f ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n, ∃ s : Y.d.c₂.F, s ≠ 0 ∧ ∀ la, ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la, 0 ≤ v (s • f) := by
  first | exact @_root_.GlobalTheory.LargeAll.exists_smul_nonneg_of_large | exact _root_.GlobalTheory.LargeAll.exists_smul_nonneg_of_large | (intros; apply _root_.GlobalTheory.LargeAll.exists_smul_nonneg_of_large <;> assumption)
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
noncomputable section
namespace GlobalTheory.CovTop.GoodDom
set_option maxHeartbeats 1000000 in
theorem weight_lattice_fg_on_domain : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) →
    FiniteDimensional Y.d.c₂.F (Y.V (wtOf _ la 0)) → (GlobalTheory.AllWt.latW Y.U (wtOf _ la 0)).FG := by
  intro hP D T j Y e o hG hE hp hq la hA hb hfd
  letI := T.Q.H.starRing
  refine GlobalTheory.fg_of_integral_functionals Y.d.c₂.F (Y.V (wtOf _ la 0)) _ fun x hx => ?_
  obtain ⟨z, La, y, hz, hyx, hne⟩ := _root_.GlobalTheory.T.cmPoint_detects_dominant_covering hP D T j Y e o hG hE hp hq la hA hb (fun _ => rfl) x.1 x.2
    (fun h => hx (Subtype.ext h))
  obtain ⟨N, hN, hint⟩ := GlobalTheory.T.exists_frame_denominator_dominant_weight_cm _ _ _ _ _ _ z _ La hz y hyx hp hq la hA hb
  refine ⟨z.K, inferInstance, inferInstance, inferInstance,
    { toFun := fun F => N * evR Y.d.Xo₂ Y.d.c₂ F.1 y
      map_add' := fun F G => ?_
      map_smul' := fun s F => ?_ }, mul_ne_zero hN hne, fun F hF => hint F.1 (GlobalTheory.AllWt.cuspW_le_secZ _ F.2) hF⟩
  · rw [← mul_add]
    exact congrArg _ (evalAt_add _ _ F.1 G.1 y)
  · have e1 : evR Y.d.Xo₂ Y.d.c₂ (s • F).1 y = algebraMap Y.d.c₂.F z.K s * evR Y.d.Xo₂ Y.d.c₂ F.1 y :=
      evalAt_smul _ _ s F.1 y
    rw [e1, RingHom.id_apply, Algebra.smul_def, mul_left_comm]
set_option maxHeartbeats 800000 in
theorem weight_lattice_span_on_domain : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ),
    Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) →
    Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.latW Y.U (wtOf _ la 0) : Set (Y.V (wtOf _ la 0))) = ⊤ := by
  intro hP D T j Y e o hY hE hp hq la hA hb
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨k, a, n, g, h, t, hdom, hn, hmem, ht, hgh, hh⟩ := _root_.GlobalTheory.T.weight_match_pow_mul_cuspidal hP D T j Y e o hY hE hp hq la hA hb f.1 f.2
  obtain ⟨s, hs, hsv⟩ := _root_.GlobalTheory.T.divisor_multiple_nonneg_eventually hP D T j Y e o hY hE a n hdom hn _ hmem
  have key : ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la',
      0 ≤ v ((s * t) • ((f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1))) := by
    intro la' v hv
    have hV := isVal_valSet la' v hv
    have e1 : (s • ((f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1) * g)) * h = (s * t) • ((f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1)) := by
      rw [smul_mul_assoc, mul_assoc, hgh, mul_smul_comm, mul_one, smul_smul]
    rw [← e1, hV.mul]
    exact add_nonneg (hsv la' v hv) (hh la' v hv)
  obtain ⟨s', hs', h'⟩ := GlobalTheory.SupFull.exists_smul_nonneg_of_pow (valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂))
    (fun la => isVal_valSet la) {(f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1)}
    (by rintro g' rfl; exact ⟨s * t, mul_ne_zero hs ht, key⟩) (f : Rul Y.d.Xo₂ Y.d.c₂) k
    (Submodule.subset_span rfl)
  have hmem' : s' • f ∈ GlobalTheory.AllWt.latW Y.U (wtOf _ la 0) :=
    GlobalTheory.AllWt.mem_supLat.2 fun la v hv => h' la v hv
  rw [← inv_smul_smul₀ hs' f]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem')
open MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH in
set_option maxHeartbeats 2000000 in
private theorem exists_semilinear_L2_independent {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {r : ℕ} {D : D7} (hS : Out.SecBaseChangeSt) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ)
    (hσ : GoodEmb c σ) (hU : IsUnf (U σ)) (V : HSp D)
    (dict : Formalism.L2.Theta.GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : Formalism.L2.Theta.GA D V → ℂ)
    (hmu1 : ∀ g, ‖mu g‖ = 1) (hm : Formalism.L2.Pj.AdelMeas U σ V dict mu) (hae : Formalism.L2.Pj.AeDom U σ V dict mu)
    (hd : ∀ g, (dict g).2 ∈ ((U σ).X (dict g).1).dom)
    (hunit : ∀ g τ i, ‖dmin ((U σ).X (dict g).1).Gm (dict g).2 τ i‖ = 1) (G : WTZ E) (x : ℝ) :
    ∃ Φ : GlobalTheory.AllWt.cuspW Xo c U G →+ Lp ℂ 2 (muQ1 V), (∀ (a : c.F) f, Φ (a • f) = σ a • Φ f) ∧
      (∀ f : GlobalTheory.AllWt.cuspW Xo c U G, GlobalTheory.AllWt.petAt (U σ) x V dict (muQ1 V) G (f : Rul Xo c) = ‖Φ f‖) ∧
      ∀ (n : ℕ) (e : Fin n → GlobalTheory.AllWt.cuspW Xo c U G), LinearIndependent c.F e →
        LinearIndependent ℂ (fun i => Φ (e i)) := by
  have hhol : ∀ f : GlobalTheory.AllWt.cuspW Xo c U G,
      rdU (U σ) (f : Rul Xo c) ∈ holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) := fun f =>
    (GlobalTheory.AllWt.mem_cuspW.1 f.2).2 σ hσ
  have heq : ∀ P : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G),
      eLpNorm (onQ V (adel V dict mu P)) 2 (muQ1 V) =
        GlobalTheory.AllWt.petE V dict (muQ1 V) (GlobalTheory.AllWt.modelWt (U σ) G) P := by
    intro P
    unfold GlobalTheory.AllWt.petE
    have hp : ∀ q : AutQ V, ‖mu q.out * (P : FDSec (U σ).X) (dict q.out).1 (dict q.out).2‖ =
        GlobalTheory.AllWt.ptN (GlobalTheory.AllWt.modelWt (U σ) G) P (dict q.out) := by
      intro q
      rw [norm_mul, hmu1, one_mul, GlobalTheory.AllWt.ptN,
        pnorm_eq_of_unit _ _ _ _ (hunit q.out)]
    have hf := aesm_of_holSub hm _ P.2
    have hg := hf.norm.congr (Filter.Eventually.of_forall hp)
    have hh := eLpNorm_congr_norm_ae (p := 2) hf hg (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_of_nonneg (GlobalTheory.AllWt.ptN_nonneg _ _ _)]
      exact hp q)
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by simp) hg] at hh
    simpa using hh
  have hmem : ∀ P : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G),
      MemLp (onQ V (adel V dict mu (P : FDSec (U σ).X))) 2 (muQ1 V) := fun P =>
    by
      change eLpNorm _ _ _ < ⊤
      rw [heq P]
      exact lt_top_iff_ne_top.2 (GlobalTheory.AllWt.petE_ne_top V dict (muQ1 V) prob_le_one hd P.2)
  let L : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) →ₗ[ℂ] Lp ℂ 2 (muQ1 V) :=
    { toFun := fun P => (hmem P).toLp _
      map_add' := fun P Q => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (by rw [Submodule.coe_add, map_add (f := _), map_add (f := _)]))
      map_smul' := fun a P => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (by rw [Submodule.coe_smul, map_smul, map_smul])) }
  have hL : ∀ P, L P = (hmem P).toLp _ := fun _ => rfl
  let R : GlobalTheory.AllWt.cuspW Xo c U G → holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) := fun f => ⟨_, hhol f⟩
  have hRadd : ∀ f g, R (f + g) = R f + R g := fun f g => Subtype.ext (by
    show rdU (U σ) ((f + g : GlobalTheory.AllWt.cuspW Xo c U G) : Rul Xo c) = rdU (U σ) (f : Rul Xo c) + rdU (U σ) (g : Rul Xo c)
    rw [Submodule.coe_add, map_add (f := _)])
  have hRsm : ∀ (a : c.F) f, R (a • f) = σ a • R f := fun a f => Subtype.ext (by
    show rdU (U σ) ((a • f : GlobalTheory.AllWt.cuspW Xo c U G) : Rul Xo c) = σ a • rdU (U σ) (f : Rul Xo c)
    rw [Submodule.coe_smul, map_smulₛₗ])
  let cf : ℝ := GlobalTheory.AllWt.lieFacZ Dw x G
  have hcf : 0 < cf := GlobalTheory.AllWt.lieFacZ_pos x G
  refine ⟨AddMonoidHom.mk' (fun f => (cf : ℂ) • L (R f)) (fun f g => by rw [hRadd, map_add (f := _), smul_add]),
    fun a f => ?_, fun f => ?_, fun n e he => ?_⟩
  · show (cf : ℂ) • L (R (a • f)) = σ a • ((cf : ℂ) • L (R f))
    rw [hRsm, map_smul, smul_comm]
  · show _ = ‖(cf : ℂ) • L (R f)‖
    rw [norm_smul, hL, Lp.norm_toLp, heq, Complex.norm_real, Real.norm_of_nonneg hcf.le]
    rfl
  · have hb : LinearIndependent c.F (fun i => (e i : Rul Xo c)) :=
      he.map' (GlobalTheory.AllWt.cuspW Xo c U G).subtype (Submodule.ker_subtype _)
    have hc := GlobalTheory.reading_linearIndependent_secZ hS (U σ) hU _ n _
      (fun i => GlobalTheory.AllWt.cuspW_le_secZ G (e i).2) hb
    rw [Fintype.linearIndependent_iff] at hc ⊢
    intro w hw
    refine hc w ?_
    have h1 : (cf : ℂ) • L (∑ i, w i • R (e i)) = 0 := by
      have hw' : ∑ i, w i • ((cf : ℂ) • L (R (e i))) = 0 := hw
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.smul_sum, ← hw']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [L.map_smul]
      exact smul_comm _ _ _
    have h2 : L (∑ i, w i • R (e i)) = 0 :=
      (smul_eq_zero.1 h1).resolve_left (Complex.ofReal_ne_zero.2 hcf.ne')
    have h3 : onQ V (adel V dict mu ((∑ i, w i • R (e i) : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G)) :
        FDSec (U σ).X)) =ᵐ[muQ1 V] 0 := by
      refine (MemLp.coeFn_toLp (hmem _)).symm.trans ?_
      rw [← hL, h2]
      exact Lp.coeFn_zero _ _ _
    have h4 := hae _ _ (∑ i, w i • R (e i)).2 h3
    have h5 : ((∑ i, w i • R (e i) : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G)) : FDSec (U σ).X) =
        ∑ i, w i • rdU (U σ) (e i : Rul Xo c) := by
      rw [Submodule.coe_sum]
      rfl
    rw [h5] at h4
    funext k z
    by_cases hz : z ∈ ((U σ).X k).dom
    · exact h4 k z hz
    · simp [Finset.sum_apply, rdU, hz]
set_option maxHeartbeats 2000000 in
private theorem hasGram_nrm_of_good (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hY : Y.Good e o)
    (G : WTZ D.host.E) : GlobalTheory.AllWt.HasGram (Y.nrm G) := by
  haveI := GlobalTheory.Deep.finiteDimensional_V_of_good D T j Y e o hY G
  refine GlobalTheory.HSApp.hasGram_of_inner Y.d.c₂.F (Y.V G) (Y.nrm G) fun v => ?_
  have hσ' : GoodEmb Y.d.c₂ (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) := Formalism.L2.Pj.goodEmb_goodOf _ _
  have hd : ∀ g, (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) g).2 ∈
      ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding)).X (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) g).1).dom :=
    fun g => ((hY.dictU _ hσ').choose_spec.choose_spec.2).2.2.2.1 g
  have hex := exists_semilinear_L2_independent GlobalTheory.abelianSchemeLaws_all.1.secBaseChange Y.U _ hσ' (hY.unf _ hσ')
    (D.sp.W j) (Y.dict _) (fun _ => (1 : ℂ)) (fun _ => norm_one)
    (adelMeas_of_aut Y.d.Xo₂ Y.d.c₂ (U := Y.U) (σ := _) (GlobalTheory.PetDef.adelAut_good Y hY _ hσ'))
    (GlobalTheory.PetDef.aeDom_good Y hY _ hσ') hd (hY.unit _ hσ') G (xiR D)
  refine ⟨_, inferInstance, inferInstance, Classical.choose hex, ?_, fun x => (Classical.choose_spec hex).2.1 x,
    (Classical.choose_spec hex).2.2⟩
  by_cases h : GoodEmb Y.d.c₂ v.embedding
  · left
    intro a x
    refine ((Classical.choose_spec hex).1 a x).trans ?_
    exact congrArg (· • Classical.choose hex x) (congrArg (fun τ : Y.d.c₂.F →+* ℂ => τ a) (ite_eq_left h))
  · right
    intro a x
    refine ((Classical.choose_spec hex).1 a x).trans ?_
    exact congrArg (· • Classical.choose hex x) (congrArg (fun τ : Y.d.c₂.F →+* ℂ => τ a) (ite_eq_right h))
set_option maxHeartbeats 1000000 in
theorem covering_regular_at_domain : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Y.GoodAt (wtOf _ la 0) ∧ ∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ la 0) := by
  intro hP D T hL j hp hq hE _ Y e o hY la hA hb
  have hfd := GlobalTheory.Deep.finiteDimensional_V_of_good D T.toCore j Y e o hY (wtOf _ la 0)
  have hG : Y.GoodAt (wtOf _ la 0) :=
    ⟨hasGram_nrm_of_good D T.toCore j Y e o hY _, _root_.GlobalTheory.CovTop.GoodDom.weight_lattice_fg_on_domain hP D T.toCore j Y e o hY hE hp hq la hA hb hfd,
      _root_.GlobalTheory.CovTop.GoodDom.weight_lattice_span_on_domain hP D T.toCore j Y e o hY hE hp hq la hA hb⟩
  exact ⟨hG, fun Z => goodOn_of_goodAt D T.toCore j Y e o hY hE Z _ hG⟩
end GlobalTheory.CovTop.GoodDom
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_domain_lattice_regularity : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Y.GoodAt (wtOf _ la 0) ∧ ∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ la 0) := by
  first | exact @_root_.GlobalTheory.CovTop.GoodDom.covering_regular_at_domain | exact _root_.GlobalTheory.CovTop.GoodDom.covering_regular_at_domain | (intros; apply _root_.GlobalTheory.CovTop.GoodDom.covering_regular_at_domain <;> assumption)
end
