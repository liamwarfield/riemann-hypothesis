module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentLeOscillationNonTypePrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetsOnCopiesAny
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.PowGerm GlobalTheory.PtTie GlobalTheory.RefSum
open GlobalTheory.ThetaLeast

open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.JetsLevelZero

theorem jets_on_copies_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∀ (C : IntegralChartA3 Xo c T io y),
    FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (n : ℕ), 1 ≤ n → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G')
    (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (q D : ℕ), 4 * D + 4 ≤ q → (D : ℝ) * M0 < q →
  ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f →
    ∃ (s : Fam D'.toPre F q) (σ' : U'.toUnifPre.SecGF F q) (g : PS F n (chD C.ch)) (lam : F),
      NuGe D' (sumQ pD.xe Q) F v q s 0 ∧ U'.toUnifPre.ExpandsG F q σ' s ∧
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' g ∧
      lam ≠ 0 ∧ (∃ ρ : ℚ, v lam = (ρ : WithTop ℚ) ∧ (ρ : ℝ) ≤ (D : ℝ) ^ 2 * Φ / q) ∧
      ∀ e : Fin n × Fin (chD C.ch) →₀ ℕ, e.degree ≤ D →
        MvPowerSeries.coeff e g = MvPowerSeries.coeff e (lam • MvPowerSeries.map (algebraMap T.Fr F) f) := by
  obtain ⟨L1, L2, -, L4, -⟩ := GlobalTheory.firstFiveLaws
  have TB := GlobalTheory.twistBaseChange_and_valuation_statements.1
  intro E _ _ _ H Dw l Xo c inst hstar
  obtain rfl : inst = H.starRing := starSt E H inst hstar
  letI := H.starRing
  intro T io y C htr P ϖ hϖ Q hQ Φ M0 r b hΦ0 hΦ hM n _ D' A' G' _ _ pD pA pG U' PU F _ _ _ _ _ v hv q D hq hD f hf
  choose f₀ hf₀ using hf
  obtain ⟨τ, hτ, htrunc, hgerm⟩ := frameNSt_holds E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hu := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n (chD C.ch) pG C.xT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C)
  obtain ⟨r', b', h1, h2⟩ := GlobalTheory.PowJets.exists_basis_bounds pD.xe Q (Q_zero hϖ P.D hQ) (RoundingSumAlt.Q_nonneg hϖ hQ) Φ M0 b hΦ hM
  have hD' : (D : ℝ) * max M0 0 < q := by
    rcases le_total M0 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact_mod_cast (by omega : 0 < q)
    · rwa [max_eq_left h]
  obtain ⟨s, σ', g, lam, a1, a2, a3, a4, a5, a6⟩ := GlobalTheory.UnifJets.jets L1 L2 L4 TB T.V ϖ hϖ D' A' G' U' (Fin n × Fin (chD C.ch))
    (zV pG C.xT) hu τ hτ (htrunc htr) (sumQ pD.xe Q) (GlobalTheory.QBox.main T.V ϖ hϖ n P.D D' pD Q hQ) Φ (max M0 0) r' b' hΦ0
    (le_max_right _ _) h1 h2 F v hv q D hq hD' (fun e => f₀ e)
  refine ⟨s, σ', g, lam, a1, a2, (hgerm F q σ' g).2 a3, a4, a5, fun e he => ?_⟩
  rw [a6 e he, map_smul, MvPowerSeries.coeff_map, ← hf₀ e, smul_eq_mul, ← IsScalarTower.algebraMap_apply]
  rfl

theorem rPoint_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (_I : TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a) (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z)))
    (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G']
    (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n)
    (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → 1 ≤ n →
  ∀ (α : 𝓞 E) (N Dg : ℕ), α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) → IsUnit ((N : ℕ) : T.V) →
    4 * Dg + 4 ≤ N → (Dg : ℝ) * M0 < N →
  ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 → ThFrame D' ϖ F θ →
    PullAl D' F oD' α 1 N θ θα →
  ∀ (I : Type) [Fintype I] (Pi : I → MvPolynomial (LtN Dw n) F) (a : I → F), (∀ i, 0 ≤ v (a i)) →
    (∑ i, a i • Pi i).totalDegree ≤ Dg → ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f → ∀ gm : ℚ,
    letI := io.toAlgebra
    v (nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * N) (MvPowerSeries.map (algebraMap T.Fr F) f) (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (∑ i, a i • Pi i)) = (gm : WithTop ℚ) →
    ∃ (i : I) (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F)
      (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (σ' : U'.toUnifPre.SecGF F (1 * N)) (h : PS F n (chD C.ch)) (ρ : ℚ),
      w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D' F (1 * N) p w ζ ∧ QkToAkU U'.toUnifPre F (1 * N) p x ∧
      (∀ k, x ≫ pA.pr k ≫ P.oA.act (star α) = 1) ∧ PhiRel D'.toPre F (1 * N) p w θα t₀ ∧ Fam.IsSmul D'.toPre F ζ t₀ t ∧
      U'.toUnifPre.ExpandsG F (1 * N) σ' t ∧ IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (1 * N) σ' h ∧
      v (nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * N) h (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (Pi i)) = (ρ : WithTop ℚ) ∧
      (ρ : ℝ) ≤ gm + (Dg : ℝ) ^ 2 * Φ / N := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have hT := GlobalTheory.twistBaseChange_and_valuation_statements.1
  intro E _ _ _ H Dw l Xo c
  let _ := H.starRing
  intro T io y C hFT P hP ϖ hϖ Q hQ F _ _ _ _ _ _ v hv I Φ M0 r b hΦ hb hbw n D' A' G' _ _ pD pA pG U' PU _ oD' hx hoD hn
    α N Dg hα hcop hu hN hM θ θα hθ hθF hθα J _ Pi a ha hdeg f hf gm hval
  let _ := io.toAlgebra
  have hN1 : 1 ≤ 1 * N := by omega
  obtain ⟨s, σ', g, lam, hs, hσ', hg, -, ⟨ρl, hlam, hρl⟩, hjet⟩ :=
    jets_on_copies_any E H Dw l Xo c (fun _ => rfl) T io y C hFT P ϖ hϖ Q hQ Φ M0 r b hΦ hb hbw n hn D' A' G'
      pD pA pG U' PU F v hv (1 * N) Dg (by omega) (by rwa [Nat.one_mul]) f hf
  obtain ⟨m, p, x, w, ζ, t, cf, e1, e2, e3, e4, e5, e6⟩ := GlobalTheory.SmallTranslate.span_pow h1 h2 h3 h4 h5 hT T.V E H C.I.G P Dw ϖ hϖ Q hQ F v hv I
    n D' A' G' pD pA pG U' PU oD' hx hoD α N (by omega) hα hcop hu θ θα hθ hθF hθα s hs
  obtain ⟨τ, hτ, hτT, hiff⟩ := GlobalTheory.PowGerm.frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hz := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n _ pG C.xT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C)
  obtain ⟨huniq, hlin, hex⟩ := GlobalTheory.GermBasic.main T.V D' A' G' U' _ _ hz τ hτ F (1 * N)
  have hbij := (GlobalTheory.expandsG_bijective_of_dvr h1 h2 h4 hT T.V D' A' G' U' F (1 * N) hN1).2
  choose σ hσ using fun j => (hbij (t j)).exists
  choose h hh using fun j => hex (hτT hFT) (σ j)
  have hsum : g = ∑ j, cf j • h j := by
    let σ₀ : U'.toUnifPre.SecGF F (1 * N) := GlobalTheory.ExpansionLinear.secComb
      (fun j => Out.scal (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj G')).left (cf j)) σ
    have k1 := GlobalTheory.GroupExpansionLinear.expandsG_sum T.V D' A' G' U' F (1 * N) m cf σ t σ₀ hσ (fun _ => rfl)
    rw [← e6] at k1
    have k2 : σ' = σ₀ := (hbij s).unique hσ' k1
    exact huniq σ' _ _ ((hiff F _ σ' g).1 hg) (hlin m cf σ h σ' hh (fun _ => by rw [k2]; rfl))
  obtain ⟨n1, n2, n3⟩ := GlobalTheory.PowGerm.nabJet _ _ _ C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * N) n
    (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
  have k1 := n1 (∑ i, a i • Pi i) _ _ (fun e he => hjet e (he.trans hdeg))
  have k2 := n2 (∑ i, a i • Pi i) Unit (fun _ => lam) (fun _ => MvPowerSeries.map (algebraMap T.Fr F) f)
  rw [Finset.univ_unique, Finset.sum_singleton, Finset.sum_singleton] at k2
  have k3 := n2 (∑ i, a i • Pi i) (Fin m) cf h
  rw [← hsum, k1, k2, Finset.sum_congr rfl fun j _ => congrArg (cf j * ·) (n3 (h j) J a Pi)] at k3
  have k4 := congrArg v k3
  rw [v.map_mul, hlam] at k4
  obtain ⟨i, j, ρ, hρ, hle⟩ := GlobalTheory.SmallTranslate.exists_term_le v a cf _ ha e5 (ρl + gm)
    (k4.symm.trans (by rw [WithTop.coe_add]; exact congrArg _ hval))
  obtain ⟨t₀, ht₀, ht⟩ := e4 j
  refine ⟨i, p j, w j, ζ j, x j, t₀, t j, σ j, h j, ρ, (e3 j).1, (e3 j).2.1, (e3 j).2.2, e1 j, e2 j, ht₀, ht, hσ j,
    (hiff F _ _ _).2 (hh j), hρ, ?_⟩
  rw [Nat.one_mul] at hρl
  have : (ρ : ℝ) ≤ ρl + gm := by exact_mod_cast hle
  linarith

end GlobalTheory.JetsLevelZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfThetaRuleLeLocalValueCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueIntegralGermFramePowerCharZeroStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueIntegralGermFramePowerCharZero
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.FramePower

theorem exists_nabValN_eq_of_map {R K O : Type} [CommRing R] [Algebra ℚ R] [CommRing K] [Algebra ℚ K] [Algebra R K]
    [CommRing O] [StarRing O] {d : ℕ} (B : FB R d O) (h : PS R 2 d) (hc : MvPowerSeries.constantCoeff h = 0)
    (w0 : O) (k k' : ℕ) {n : ℕ} (g : PS R n d) :
    ∃ g' : PS R n d, ∀ {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → K) (P : MvPolynomial Ix K),
      nabValN B K (FB.toK K h) w0 k (FB.toK K g) cp u P = nabValN B K (FB.toK K h) w0 k' (FB.toK K g') cp u P := by
  have gC : GP (comp1 (B.actK R w0) (pt R (n := 1) d 0)) :=
    gp_comp1 _ _ (GlobalTheory.GaugeBaseChange.gp_actK B w0) (gp_pt 0)
  have cL : MvPowerSeries.constantCoeff (B.hL R h w0) = 0 := gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc
  have eL : MvPowerSeries.map (algebraMap R K) (B.hL R h w0) = B.hL K (FB.toK K h) w0 := by
    unfold FB.hL
    rw [GlobalTheory.GaugeBaseChange.map_ev_two _ _ _ (gp_pt _) gC, GlobalTheory.QuadDeriv.baseChange_comp1 _ _ _ (gp_pt _),
      GlobalTheory.QuadDeriv.baseChange_pt]
    have := GlobalTheory.GaugeBaseChange.baseChange_actK B (Algebra.ofId R K) w0
    exact congrArg (fun t => ev (n := 1) ![pt K d 0, comp1 t (pt K d 0)] (FB.toK K h)) this
  set S : PS R n d := ∑ b : Fin n, ev (n := n) ![pt R d b] (B.hL R h w0) with hS
  have gp : ∀ b : Fin n, ∀ j : Fin 1, GP ((![pt R d b] : Fin 1 → Pt R n d) j) := by
    intro b j; fin_cases j; exact gp_pt b
  have cS : MvPowerSeries.constantCoeff S = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum]
    exact Finset.sum_eq_zero fun b _ => gt_const_ev _ (gp b) _ cL
  have eS : MvPowerSeries.map (algebraMap R K) S =
      ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K (FB.toK K h) w0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.QuadDeriv.map_ev _ _ (gp b), eL]
    congr 1
    funext j; fin_cases j
    exact GlobalTheory.QuadDeriv.baseChange_pt _ _
  have cm : ∀ m : ℕ, MvPowerSeries.constantCoeff ((m : R) • S) = 0 := fun m => by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, cS, mul_zero]
  have em : ∀ m : ℕ, FB.expS K ((m : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K (FB.toK K h) w0)) =
      FB.toK K (FB.expS R ((m : R) • S)) := fun m => by
    rw [FB.toK.eq_1 K (FB.expS R _), GlobalTheory.GaugeBaseChange.map_expS _ _ (cm m), MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul,
      map_mul, MvPowerSeries.map_C, map_natCast (algebraMap R K), eS]
  refine ⟨g * FB.expS R ((k : R) • S - (k' : R) • S), fun cp u P => ?_⟩
  unfold nabValN
  rw [em, em, FB.toK, FB.toK, FB.toK, FB.toK, ← map_mul, ← map_mul, _root_.mul_assoc,
    ← gt_expS_add _ _ (by rw [map_sub, cm, cm, sub_zero]) (cm k'), sub_add_cancel]

end GlobalTheory.FramePower


open GlobalTheory.FramePower in
theorem GlobalTheory.FramePower.exists_nabValN_eq_of_harmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), CharZero (IsLocalRing.ResidueField T.V) → letI := io.toAlgebra; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n k k' : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f → ∃ f' : PS T.Fr n (chD C.ch), IsIntPS T f' ∧ nabValN C.ch.B T.Fr C.ch.h H.w0 k f (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) = nabValN C.ch.B T.Fr C.ch.h H.w0 k' f' (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  have hstar : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  intro T io y C hchar
  letI := io.toAlgebra
  intro a n k k' P hP f hf
  obtain ⟨B, hBT, hB⟩ := GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound E H Dw l Xo c hstar T io y C
  obtain ⟨hg, -, heig, -⟩ := hB B hBT
  obtain ⟨hF, hA, -⟩ := C.gen.1
  obtain ⟨e1, e2, -⟩ := hBT
  have eF : B.FK T.Fr = C.ch.B.FK T.Fr := by
    funext i
    change MvPowerSeries.map _ (B.G.F i) = MvPowerSeries.map _ (C.ch.B.G.F i)
    rw [GlobalTheory.ChartBiext.toK_self, hF, e1]
  have eA : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := by
    intro a
    funext i
    change MvPowerSeries.map _ (B.A.act a i) = MvPowerSeries.map _ (C.ch.B.A.act a i)
    rw [GlobalTheory.ChartBiext.toK_self, hA, e2]
  letI : Algebra ℚ T.V := (IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) (g := Int.castRingHom T.V) (by
    rintro ⟨z, hz⟩
    have h0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
    rw [← residue_ne_zero_iff_isUnit]
    simpa using h0)).toAlgebra
  obtain ⟨h0, hh0⟩ := GlobalTheory.canonGauge_exists T.V (chD C.ch) (𝓞 E) T.V B
  have hh1 : B.IsCanonGauge T.Fr (FB.toK T.Fr h0) :=
    GlobalTheory.GaugeBaseChange.isCanonGauge_map B (Algebra.ofId T.V T.Fr) hh0
  choose g hg' using hf
  have ef : f = FB.toK T.Fr (g : PS T.V n (chD C.ch)) := by
    ext m
    exact (hg' m).symm.trans (MvPowerSeries.coeff_map (algebraMap T.V T.Fr) m (g : PS T.V n (chD C.ch))).symm
  obtain ⟨g', hgg⟩ := exists_nabValN_eq_of_map (K := T.Fr) B h0 (GlobalTheory.GaugeBaseChange.const_of_axis hh0.ax0)
    H.w0 k k' (g : PS T.V n (chD C.ch))
  have key := GlobalTheory.nabValN_harmonic_gauge_independent T.V (chD C.ch) (𝓞 E) T.Fr B (gaugeOf C) (FB.toK T.Fr h0) hg hh1
    (E →+* ℂ) Dw.mult ComplexEmbedding.conjugate (InPsi H) (fun τ => io.comp (embK c τ)) (fun τ => by ext x; simp)
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or H)
    (fun τ a => by
      rw [RingHom.comp_apply, RingHom.comp_apply, hstar]
      congr 1
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq, IsCMField.complexEmbedding_complexConj])
    (fun σ τ hne => by
      have hex : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E) := by
        by_contra hc
        push Not at hc
        exact hne (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => by simpa using hc a))
      obtain ⟨a, ha⟩ := hex
      refine ⟨a, ?_⟩
      have h0 : embK c σ a - embK c τ a ≠ 0 := by
        rw [sub_ne_zero]
        intro h1
        apply ha
        rw [← embK_coe c, ← embK_coe c, h1]
      rw [RingHom.comp_apply, RingHom.comp_apply, ← map_sub]
      exact (Ne.isUnit h0).map _)
    C.ch.uvec heig n (MvPolynomial.map io P) (ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map io hP.1.1) H.w0
  refine ⟨FB.toK T.Fr g', fun m => ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩, ?_⟩
  rw [← GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eF eA, ← GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eF eA]
  refine (key k f).trans (Eq.trans ?_ (key k' _).symm)
  rw [ef]
  exact hgg _ _ _
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.PowGerm GlobalTheory.PtTie GlobalTheory.RefSum
open GlobalTheory.ThetaLeast

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_value_integral_germ_frame_power_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), CharZero (IsLocalRing.ResidueField T.V) → letI := io.toAlgebra; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n k k' : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f → ∃ f' : PS T.Fr n (chD C.ch), IsIntPS T f' ∧ nabValN C.ch.B T.Fr C.ch.h H.w0 k f (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) = nabValN C.ch.B T.Fr C.ch.h H.w0 k' f' (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) := by
  first | exact @GlobalTheory.FramePower.exists_nabValN_eq_of_harmonic | exact GlobalTheory.FramePower.exists_nabValN_eq_of_harmonic | (intros; apply GlobalTheory.FramePower.exists_nabValN_eq_of_harmonic <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueTranslateDivisorLevelIntegralChartStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueTranslateDivisorLevelIntegralChart
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.DivLevel
open GlobalTheory.ConjPull GlobalTheory.OneOrder GlobalTheory.AlphaForm

theorem isVtOver_of_isNormPull_dvd {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (L : RigLB A)
    (φ ψ : A ⟶ A) [IsMonHom ψ] (N M m : ℕ) (hm : M * M = N * m)
    (hN : ψ ≫ φ = 𝟙 A ^ M) {T : Over S} (ok : (T ⟶ A) → Prop) (t : T ⟶ A) (ho : ok t) (ht : t ^ (M * M) = 1)
    (s : LB.Sec (LPow A L.L 1 T)) (hh : LB.Sec (LPow A L.L (N : ℤ) T)) (Fs : LB.Sec (LPow A L.L ((M : ℤ) ^ 2) T))
    (h₁ : IsTransPull A L φ N s (t ≫ ψ) hh) (h₂ : IsNormPull A L ψ ((M : ℤ) ^ 2) (N : ℤ) hh Fs) :
    IsVtOver A L M ok s (t ^ M) Fs := by
  have hL := L.isLB
  obtain ⟨s₀, ⟨α₀, α, gα₀, nα, cα, tα⟩, hb, U, hU, aU⟩ := h₁
  obtain ⟨β₀, β, gβ₀, nβ, cβ, tβ⟩ := h₂
  obtain ⟨u', g, sl, hv⟩ := exists_symLift_pull hL ψ β₀ gβ₀ t U hU hb (m := m) (by rw [← hm]; exact ht)
  have hUp := hU.pt_eq
  have e₀ : ψ.left ≫ φ.left = (mulA A M).left := by rw [← Over.comp_left, hN]
  have ha : eSec A ≫ ψ.left = eSec A := by simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨κ₀, gκ₀, vκ₀⟩ := exists_gen hL (φ' := ![𝟙 A.left, (mulA A M).left]) (ε' := ![(M : ℤ) ^ 2, -1])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₀, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ β₀ (LB.pullGen L.L _ _ α₀ ψ.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ gβ₀ (DVR.pullGen_isGen _ _ _ _ gα₀ _))
  have e₁ : (snd T A).left ≫ (mulA A M).left = (snd T A ^ M).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨κ, gκ, vκ⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ M).left]) (ε' := ![(M : ℤ) ^ 2, -1])
    (fun U _ f => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e₁, Category.comp_id])
    (LB.pullGen L.L ![𝟙 A.left, (mulA A M).left] ![(M : ℤ) ^ 2, -1] κ₀ (snd T A).left)
    (DVR.pullGen_isGen _ _ _ _ gκ₀ _)
  obtain ⟨s₁, tκ, -⟩ := existsUnique_isTwistPull S A L.L hL T (mulT A T M) (snd T A ^ M) (lift_snd _ _)
    ((M : ℤ) ^ 2) 1 κ gκ s
  refine ⟨t, κ₀, κ, s₁, ⟨t, u', g⟩, rfl, ho, gκ₀, corr_of_val hL fun y J hJ => ?_,
    corr_of_val hL fun y J hJ => vκ _ _ y J hJ, tκ, by rw [pow_two M, hm]; exact sl, Geo.Tor.twist_of_val hL g fun z J hJ => ?_⟩
  · have a₁ := val_corr hJ nα (𝟙 _)
    have a₂ := val_corr hJ nβ (𝟙 _)
    have vr : ∀ k : ℤ, val (rigPow A L.L L.rig k) (𝟙 _) y J = val (L := L.L) L.rig (𝟙 _) y J ^ k :=
      fun k => map_zpow _ _ _
    rw [val_pull hJ, val_mul hJ, vr, vr] at a₁ a₂
    rw [val_pull hJ, vκ₀ _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, ha, a₁, a₂, val_mul hJ, vr]
    refine Eq.trans ?_ (congrArg _ (val_inv _ _).symm)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
    module
  · have c₁ : endOver A T ψ ≫ translPt A (t ≫ ψ) = translPt A t ≫ ψ := by
      rw [translPt_eq, translPt_eq, MonObj.comp_mul, MonObj.mul_comp, lift_fst_assoc, lift_snd, Category.assoc]
    have c₂ : endOver A T ψ ≫ translT A U.pt ≫ snd T A = translPt A t ≫ ψ := by
      rw [hUp, translT, lift_snd, c₁]
    have c₃ : endOver A T ψ ≫ translT A U.pt ≫ endOver A T φ = translT A t ≫ mulT A T M := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [translT, mulT]
      · have : endOver A T φ ≫ snd T A = snd T A ≫ φ := lift_snd _ _
        rw [Category.assoc, Category.assoc, this, ← Category.assoc (translT A U.pt), ← Category.assoc, c₂,
          Category.assoc, hN, mulT, Category.assoc, lift_snd, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id,
          translT, lift_snd]
    have c₆ : translT A t ≫ snd T A = translPt A t := lift_snd _ _
    rw [twist_val tβ _ z hJ, twist_val aU _ z hJ, twist_val tα _ z hJ]
    dsimp only
    rw [twist_val tκ _ z hJ, hv _ _ z J hJ, vκ _ _ z J hJ, val_corr hJ cα, val_corr hJ cβ, val_pull hJ, val_pull hJ,
      val_pull hJ, vκ₀ _ _ z J hJ, val_mul hJ, val_pull hJ]
    simp only [Category.id_comp, ← Over.comp_left, Category.assoc, c₂, c₃, c₆]
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
    rw [_root_.mul_assoc _ _⁻¹, inv_mul_cancel_left]

theorem isVtOver_conj_pull_dvd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l), letI := H.starRing; ∀ (F : Type) [Field F] [IsAlgClosed F] (xF : Sp F ⟶ Xo.X) (α : 𝓞 E) (N k : ℕ), l.M = N * k → α * star α = (N : 𝓞 E) → l.Mb ≤ Ideal.span {star α} → ∀ (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo xF))) (b : ptO Xo xF ⟶ Xo.univ.t.G) (hh : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (N : ℤ) (ptO Xo xF))), b ≫ Xo.univ.t.act.act (star α) = 1 → IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) N s b hh → ∃ Fs : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo xF)), IsNormPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act ((k : 𝓞 E) * star α)) ((l.M : ℤ) ^ 2) (N : ℤ) hh Fs ∧ IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) s (b ≫ Xo.univ.t.act.act α) Fs := by
  intro E _ _ _ H Dw l Xo F _ _ xF α N k hk hα hMb s b hh hb h
  letI := H.starRing
  have := UnivPol.isLocallyNoetherian Xo
  have hom := Xo.univ.t.act.hom
  have := hom α
  have := hom ((k : 𝓞 E) * star α)
  have hL := Xo.univ.t.PP.isLB
  have hβ' : ((k : 𝓞 E) * star α) * star ((k : 𝓞 E) * star α) = ((k * l.M : ℕ) : 𝓞 E) := by
    rw [star_mul, star_star, star_natCast, hk]
    push_cast
    rw [← hα]
    ring
  have hαβ : α * ((k : 𝓞 E) * star α) = (l.M : 𝓞 E) := by
    rw [hk]
    push_cast
    rw [← hα]
    ring
  have hM : 0 < l.M := l.odd.pos
  have hg := PullGenG.hasGen_pull Xo.univ.t.PP Xo.univ.t.cub Xo.univ.t.act.toRingAct H.w0 ((k : 𝓞 E) * star α)
    (k * l.M) hβ' (Xo.univ.t.adj _) Xo.univ.t.prim N
  have hMM : l.M * l.M = N * (k * l.M) := by rw [← _root_.mul_assoc, ← hk]
  obtain ⟨β, hβ⟩ := hg.gen hL (K' := Fin 2) ![𝟙 Xo.univ.t.G.left, (Xo.univ.t.act.act ((k : 𝓞 E) * star α)).left]
    ![(l.M : ℤ) ^ 2, -(N : ℤ)] (by rw [pow_two, ← Nat.cast_mul, hMM]; rfl)
  obtain ⟨Fs, hFs⟩ := TransPullEx.exists_isNormPull Xo.univ.t.PP (Xo.univ.t.act.act ((k : 𝓞 E) * star α)) _ _ β hβ hh
  refine ⟨Fs, hFs, ?_⟩
  have hbM : b ^ l.M = 1 := by
    rw [hk, pow_mul, h.pow_eq_one, one_pow]
  have hkill : ∀ x : 𝓞 E, star α ∣ x → b ≫ Xo.univ.t.act.act x = 1 := by
    rintro _ ⟨d, rfl⟩
    have := hom d
    rw [Xo.univ.t.act.mul, ← Category.assoc, hb, MonObj.one_comp]
  obtain ⟨-, I, -⟩ := Xo.univ.geom F xF (Spec.preimage (xF ≫ Xo.s)).hom (Spec.map_preimage _).symm
  obtain ⟨a, ha⟩ := (I.onto l.M hM b).1 hbM
  have hr : I.ev (l.M * l.M) a ^ l.M = b := (I.tower l.M l.M hM hM a).trans ha
  have hz : ∀ x : 𝓞 E, I.ev (l.M * l.M) a ≫ Xo.univ.t.act.act ((l.M : 𝓞 E) * x) = b ≫ Xo.univ.t.act.act x :=
    fun x => by rw [Xo.univ.t.act.mul, ← Category.assoc, comp_act_natCast, hr]
  obtain ⟨m, hm, e, he, hme⟩ := Submodule.mem_sup.1 (l.coprime.ge (Submodule.mem_top (x := (1 : 𝓞 E))))
  obtain ⟨t, ht, ho⟩ : ∃ t : ptO Xo xF ⟶ Xo.univ.t.G, t ≫ Xo.univ.t.act.act ((k : 𝓞 E) * star α) = b ∧
      KilledBy Xo (l.Mb ^ 2) t := by
    refine ⟨I.ev (l.M * l.M) a ≫ Xo.univ.t.act.act (α * e), ?_, fun x hx => ?_⟩
    · rw [Category.assoc, ← Xo.univ.t.act.mul, mul_right_comm, hαβ, hz]
      have h1 : b ≫ Xo.univ.t.act.act (m + e) = b := by rw [hme, Xo.univ.t.act.one, Category.comp_id]
      rwa [Xo.univ.t.act.add, MonObj.comp_mul, hkill m (Ideal.mem_span_singleton.1 (hMb hm)), _root_.one_mul] at h1
    · have h1 : e * x ∈ Ideal.span {(l.M : 𝓞 E) * star α} := by
        have h2 := Ideal.mul_mem_mul he hx
        rw [pow_two, ← _root_.mul_assoc, mul_comm (Ideal.map _ l.Mb) l.Mb, l.prod] at h2
        rw [← Ideal.span_singleton_mul_span_singleton]
        exact Ideal.mul_mono_right hMb h2
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 h1
      rw [Category.assoc, ← Xo.univ.t.act.mul, _root_.mul_assoc, hd,
        show α * ((l.M : 𝓞 E) * star α * d) = (l.M : 𝓞 E) * (star α * (α * d)) by ring, hz]
      exact hkill _ ⟨_, rfl⟩
  have hN : Xo.univ.t.act.act ((k : 𝓞 E) * star α) ≫ Xo.univ.t.act.act α = 𝟙 _ ^ l.M := by
    rw [← Xo.univ.t.act.mul, mul_comm, hαβ, ← comp_act_natCast Xo.univ.t.act, Category.id_comp]
  have htM : t ^ l.M = b ≫ Xo.univ.t.act.act α := by
    rw [← ht, Category.assoc, hN, MonObj.comp_pow, Category.comp_id]
  rw [← htM]
  refine isVtOver_of_isNormPull_dvd Xo.univ.t.PP _ _ N l.M _ hMM hN _ t ho ?_ s hh Fs (ht.symm ▸ h) hFs
  rw [pow_mul, htM, ← MonObj.pow_comp, hbM, MonObj.one_comp]

theorem alphaForm_at_point_dvd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra c.F F] (yF : FrPt Xo c F) (α : 𝓞 E) (N : ℕ), N ∣ l.M → α * star α = (N : 𝓞 E) → l.Mb ≤ Ideal.span {star α} → ∀ (n : ℕ) (b : Fin n → (ptO Xo yF.x ⟶ Xo.univ.t.G)) (hh : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (N : ℤ) (ptO Xo yF.x))), (∀ i, b i ≫ Xo.univ.t.act.act (star α) = 1) → (∀ i, IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) N yF.s (b i) (hh i)) → ∃ (xx : Fin n → Dw.La) (Fs : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo yF.x))), (∀ i, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) yF.s (levPt Xo yF.x (xx i)) (Fs i)) ∧ ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∑ m ∈ Pp.support, algebraMap c.F F (Pp.coeff m) * ∏ i, nab yF (N : ℤ) (hh i) (colOf m i) = algebraMap c.F F (nrm Dw c a α) * thExpr Xo c nab yF Pp Fs := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab F _ _ _ yF α N ⟨k, hk'⟩ hα hMb n b hh hb hT
  choose Fs hN hV using fun i => isVtOver_conj_pull_dvd E H Dw l Xo F yF.x α N k hk' hα hMb yF.s (b i) (hh i) (hb i) (hT i)
  have hk : ∀ i, KilledBy Xo l.Mb (b i ≫ Xo.univ.t.act.act α) := by
    intro i x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 (hMb hx)
    haveI := Xo.univ.t.act.hom (α * y)
    rw [Category.assoc, ← Xo.univ.t.act.mul, show α * (y * star α) = star α * (α * y) by ring,
      Xo.univ.t.act.mul, ← Category.assoc, hb i, MonObj.one_comp]
  choose xx hxx using fun i => GlobalTheory.T.exists_levelPoint_eq_of_killedByHalfLevel E H Dw l Xo c F yF _ (hk i)
  refine ⟨xx, Fs, fun i => (hxx i) ▸ hV i, fun a Pp hP => ?_⟩
  by_cases h0 : Pp = 0
  · subst h0
    simp [thExpr]
  have hβ : ((k : 𝓞 E) * star α) * star ((k : 𝓞 E) * star α) = ((k * l.M : ℕ) : 𝓞 E) := by
    rw [star_mul, star_star, star_natCast, hk']
    push_cast
    rw [← hα]
    ring
  have hαβ : α * ((k : 𝓞 E) * star α) = (l.M : 𝓞 E) := by
    rw [hk']
    push_cast
    rw [← hα]
    ring
  have hch := GlobalTheory.T.harmonic_value_normalised_pullback_chain_rule E H Dw l Xo c nab hnab F yF ((k : 𝓞 E) * star α) (k * l.M) N ((l.M : ℤ) ^ 2) hβ
    (by rw [← _root_.mul_assoc, ← hk']; push_cast; ring) n hh Fs hN a Pp hP
  have hM : (l.M : c.F) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  unfold thExpr
  rw [hch, ← _root_.mul_assoc, ← _root_.mul_assoc, ← map_mul, ← map_mul, totalDegree_harm c hP h0,
    mul_right_comm, nrm_mul_nrm Dw c a α _ l.M hαβ, mul_inv_cancel₀ (pow_ne_zero _ hM), map_one, _root_.one_mul]


set_option maxHeartbeats 1600000 in
theorem harmonicValue_translate_dvd_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (α : 𝓞 E) (N : ℕ), N ∣ l.M → α * star α = (N : 𝓞 E) → l.Mb ≤ Ideal.span {star α} → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), ThFrame D' ϖ F θ → PullAl D' F oD' α 1 N θ θα → ∀ (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (q : ℕ) (e : 1 * N = q) (_ : N = q) (σ' : U'.toUnifPre.SecGF F q) (h : PS F n (chD C.ch)), w.IsGen → FinOrd D' F (1 * N) p w ζ → QkToAkU U'.toUnifPre F (1 * N) p x → PhiRel D'.toPre F (1 * N) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → U'.toUnifPre.ExpandsG F q σ' (PowGerm.famCast (Dp := D'.toPre) (F := F) e t) → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' h → (∀ k, x ≫ pA.pr k ≫ P.oA.act (star α) = 1) → letI := io.toAlgebra; ∃ (xx : Fin n → Dw.La) (u : F), v u = 0 ∧ ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∀ f, IsThRule Xo c nab xx Pp f → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 q h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) = u * algebraMap T.Fr F (io (nrm Dw c a α) * evI y f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab T io y C P htors ϖ hϖ F _ _ _ _ _ _ v hv n D' A' G' _ _ pD pA pG U' PU _ oD' hx ho
    α N hN hα hMb θ θα hθ hθα p w ζ x t₀ t q e₀ hNq σ' h hw hfo hq hphi hsm hexp hgerm hkill
  subst hNq
  have hodd : Odd N := Odd.of_dvd_nat l.odd hN
  letI := io.toAlgebra
  letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  let φ : T.Fr →ₐ[c.F] F := { algebraMap T.Fr F with commutes' := fun _ => rfl }
  have hφ : φ.toRingHom = algebraMap T.Fr F := rfl
  have hM : 1 ≤ N := hodd.pos
  obtain ⟨yF, hyF⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c T.Fr F φ y.1
  obtain ⟨τ, hτ, hEL, -⟩ := frame1St_holds E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT
    C.eT C.wPT C.chartT C.frameT C.primT
  obtain ⟨θ₁, θα₁, hθ₁, hθα₁, hone⟩ := GlobalTheory.OneColTranslate.oneColumn_translate E H Dw l Xo c T io y.1 C.I P ϖ hϖ F φ hφ
    yF hyF α N hodd hα
  obtain ⟨u, p₁, w₁, ζ₁, r₀, r, σ₁, S, hu, hS, htS, hcol⟩ := translate_eq_box E H Dw l Xo c T io y C P htors ϖ hϖ F v hv
    n D' A' G' pD pA pG U' PU oD' hx ho α N hM hα θ₁ θα₁ hθ₁ hθα₁ θ θα hθ hθα p w ζ x t₀ t N (one_mul _) hw hfo hq
    hphi hsm
  rw [htS] at hexp
  have hone' := fun i => hone (p₁ i) (w₁ i) (ζ₁ i) (x ≫ pA.pr i) (r₀ i) (r i) (σ₁ i) (hcol i).1 (hcol i).2.1
    (hcol i).2.2.1 (by rw [Category.assoc]; exact hkill i) (hcol i).2.2.2.1 (hcol i).2.2.2.2.1 (hcol i).2.2.2.2.2
  choose u₁ b hs σ₀ hu₁ hb htp htie hσ using hone'
  obtain ⟨xx, Fs, hFs, hal⟩ := alphaForm_at_point_dvd E H Dw l Xo c nab hnab F yF α N hN hα hMb n b hs hb htp
  refine ⟨xx, u * ∏ i, u₁ i, ?_, fun a Pp hPp f hf' => ?_⟩
  · rw [v.map_mul, hu, zero_add]
    refine val_prod_eq_zero v _ _ fun i => ?_
    obtain ⟨m, hm, hm'⟩ := hu₁ i
    exact ColumnSplit.val_eq_zero_of_pow_eq_one v hm hm'
  · set m := Pp.totalDegree with hm
    choose a₀ ha₀ using fun i => exists_jetAt P.U.toUnifPre F (κ := Fin 1 × Fin (chD C.ch)) C.xT m (τ m) (hτ m) N (σ₀ i)
    choose a₁ ha₁ using fun i => exists_jetAt P.U.toUnifPre F (κ := Fin 1 × Fin (chD C.ch)) C.xT m (τ m) (hτ m) N (σ₁ i)
    choose f₀ hf₀ using fun i => GlobalTheory.ChartCmp.FrameRatio.psJet_surj m (a₀ i)
    have ha : ∀ i, a₁ i = algebraMap F _ (u₁ i) * a₀ i := fun i =>
      jetAt_smul P.U.toUnifPre F m (C.xT m) (τ m) N (σ₀ i) (σ₁ i) (u₁ i) _ _ (hσ i) (ha₀ i) (ha₁ i)
    have hj := psJet_of_box P C.actT C.xT C.eT C.wPT τ hτ hEL n D' A' G' pD pA pG U' PU F N hM m σ₁ _ a₁ σ' S u h
      (fun i => (hcol i).2.2.2.2.2) ha₁ hS hexp hgerm
    have hj' : psJet m h = psJet m (∑ _i : Fin 1, (u * ∏ i, u₁ i) • boxSer f₀) := by
      rw [GermBasic.psJet_sum, Fin.sum_univ_one, BoxGerm.psJet_boxSer, hj]
      simp only [ha, hf₀, map_mul, AlgHom.commutes, Finset.prod_mul_distrib, map_prod, _root_.mul_assoc]
    have h1 : (∑ j ∈ Pp.support, algebraMap c.F F (Pp.coeff j) * ∏ i, nab yF (N : ℤ) (hs i) (colOf j i)) =
        nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 N (boxSer f₀)
          (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
          (MvPolynomial.map (algebraMap c.F F) Pp) := by
      open GlobalTheory.GermValuationJetHarmonics GlobalTheory.ChartPush in
      obtain ⟨x', e', h₁, h₂, h₃, h₄, h₅⟩ := exists_chart_baseChange φ hyF C.ch
      rw [hφ] at h₁ h₂ h₃ h₄ h₅
      have hg := RawChartBaseChange.isCanonGauge_mapFB (algebraMap T.Fr F) C.ch.B C.ch.h C.ch.gauge
      let CF : ChartAt Xo c yF := ⟨C.ch.d, FBMap.mapFB (algebraMap T.Fr F) C.ch.B, fun ℓ j => algebraMap T.Fr F (C.ch.uvec ℓ j),
        x', e', C.ch.wP, MvPowerSeries.map (algebraMap T.Fr F) C.ch.h, h₁, h₂, C.ch.prim, hg, h₃⟩
      have hG : ∀ i, JetD yF CF.d CF.x CF.B.A.act CF.e CF.wP N (hs i) m (f₀ i) := fun i =>
        jet_of_val ((isChart_iff yF _ _ _ _ _).1 h₁) h₂.gen C.ch.prim.1 m
          fun z J hJ => by
            have hf : JetAt P.U.toUnifPre m (C.xT m) (τ m) F N (σ₀ i) (psJet m (f₀ i)) := by rw [hf₀]; exact ha₀ i
            obtain ⟨p, p₀, p₁, p₂, hp⟩ := frames_tied C m (spMap (jetCoef (algebraMap T.Fr F) (Fin 1 × Fin (chD C.ch)) m))
            obtain ⟨zF, z₁, z₂, hz⟩ := hf
            have hLG : P.U.LG.L.IsLB := P.U.LG.isLB
            obtain ⟨J₂, hJ₂⟩ := DegPull.exists_good' hLG z
            obtain ⟨J', hJ'⟩ := DegPull.exists_good' C.I.t'.PP.isLB z
            obtain ⟨J₃, hJ₃, hv, hw⟩ := exists_good_cast (L' := C.I.t'.PP.L) (Φ := C.I.m2.φ)
              (congrArg RigLB.L P.bundle).symm z J₂ hJ₂
            obtain ⟨A, k₁, k₂⟩ := hp z J J₃ J' hJ hJ₃ hJ'
            have ec : spMap (jetCoef (algebraMap T.Fr F) (Fin 1 × Fin (chD C.ch)) m) ≫
                spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin (chD C.ch)) m) =
                spMap (jetCoef (algebraMap T.V F) (Fin 1 × Fin (chD C.ch)) m) := by
              rw [spMap_spMap, jetCoef_comp, ← IsScalarTower.algebraMap_eq]
            rw [ec] at p₂ k₂
            obtain ⟨b₁, b₂⟩ := ptSec_base (t := Xo.univ.t) m (x' m)
            have key := (htie i).2 _ p zF _ (z₂.trans p₂.symm) (b₁.trans ((h₄ m).trans p₁.symm)) (z₁.trans b₂.symm) (by
                rw [← Category.assoc, p₀]
                refine (congrArg (· ≫ spMap (algebraMap T.Fr F)) b₂).trans ?_
                exact RawChartGermBC.spMap_comp_eq _ _ _ _
                  (RingHom.ext fun s => (jetBC_algebraMap (algebraMap T.Fr F) _ m s).symm))
              z J J₂ (J' p) hJ hJ₂ (hJ' p)
            rw [hw] at key
            have k₃ := (val_corr hJ₂ (corr_of_val hLG (hEL m))
              (spMap (jetCoef (algebraMap T.V F) (Fin 1 × Fin (chD C.ch)) m))).trans ((hv _ _ _ _).trans k₂)
            exact (alg_tie key (hz z J₂ hJ₂) k₁ k₃).trans
              (congrArg (fun v => gs (𝟙 _) z ⊤ (toΓ _ (psJet m (f₀ i))) * (v ^ N).val) (h₅ m z J hJ).symm)
      have hh := GlobalTheory.OrderGerm.ord_holds E H Dw l Xo c nab hnab F yF CF N n m hs f₀ hG a Pp hPp
        (fun j hj => (MvPolynomial.le_totalDegree hj).trans le_rfl)
      refine hh.symm.trans ?_
      exact (nabValN_columns (algebraMap c.F F) C.ch.B _ (HarmCopies.const_eq_zero hg) N n f₀
        (fun ℓ j => algebraMap T.Fr F (C.ch.uvec ℓ j)) Pp).symm
    have h2 := hal a Pp hPp
    have h3 : algebraMap T.Fr F (evI y f) = thExpr Xo c nab yF Pp Fs := by
      first
        | exact GlobalTheory.PtTie.evI_eq_thExpr_ext (chartIndep2_of_glob GlobalTheory.firstFiveLaws.1.globalFns) E H Dw l Xo c nab hnab T
            io y F φ hφ yF hyF a n xx Pp hPp Fs hFs f hf'
        | exact GlobalTheory.PtTie.evI_eq_thExpr_ext E H Dw l Xo c nab hnab T io y F φ hφ yF hyF a n xx Pp hPp Fs hFs f hf'
    have h0 := nabJet T.Fr (chD C.ch) (𝓞 E) C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 N n
      (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2)
      (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
    have h4 := h0.2.1 (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) (Fin 1) (fun _ => u * ∏ i, u₁ i)
      (fun _ => boxSer f₀)
    have hdeg : (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp).totalDegree ≤ m :=
      Finset.sup_mono (MvPolynomial.support_map_subset _ _)
    have h5 := h0.1 (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) h _
      fun e he => HarmInvA.coeff_eq_of_psJet hj' (he.trans hdeg)
    rw [h5, h4, Fin.sum_univ_one, map_mul, h3]
    congr 1
    exact h1.symm.trans h2

theorem val_nonneg_of_isIntegral {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {x : F} (hx : IsIntegral ℤ x) :
    0 ≤ v x :=
  (Valuation.integer.integers (AddValuation.toValuation v)).mem_of_integral hx.tower_top


set_option maxHeartbeats 1600000 in
theorem harmonicValue_translate_dvd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G), P.TorsionIso → CharZero (IsLocalRing.ResidueField T.V) → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (IsLocalRing.maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (IsLocalRing.maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (α : 𝓞 E) (N : ℕ), N ∣ l.M → α * star α = (N : 𝓞 E) → l.Mb ≤ Ideal.span {star α} → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), ThFrame D' ϖ F θ → PullAl D' F oD' α 1 N θ θα → ∀ (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (σ' : U'.toUnifPre.SecGF F (1 * N)) (h : PS F n (chD C.ch)), w.IsGen → ζ ≠ 0 → FinOrd D' F (1 * N) p w ζ → QkToAkU U'.toUnifPre F (1 * N) p x → PhiRel D'.toPre F (1 * N) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → U'.toUnifPre.ExpandsG F (1 * N) σ' t → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (1 * N) σ' h → (∀ k, x ≫ pA.pr k ≫ P.oA.act (star α) = 1) → letI := io.toAlgebra; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∃ (xx : Fin n → Dw.La) (u : F), 0 ≤ v u ∧ ∀ f, IsThRule Xo c nab xx Pp f → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * N) h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) = u * algebraMap T.Fr F (evI y f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab T io y C _ P htors _ ϖ hϖ Q _ F _ _ _ _ _ _ v hv n D' A' G' _ _ pD pA pG U' PU _ oD' hx ho
    α N hN hα hMb θ θα hθ hθα p w ζ x t₀ t σ' h hw _ hfo hq hphi hsm hexp hgerm hkill a Pp hPp
  obtain ⟨xx, u, hu, hval⟩ := harmonicValue_translate_dvd_unit E H Dw l Xo c nab hnab T io y C P htors ϖ hϖ F v hv
    n D' A' G' pD pA pG U' PU oD' hx ho α N hN hα hMb θ θα hθ hθα p w ζ x t₀ t (1 * N) rfl (one_mul N).symm σ' h
    hw hfo hq hphi hsm hexp hgerm hkill
  refine ⟨xx, u * algebraMap T.Fr F (io (nrm Dw c a α)), ?_, fun f hf => ?_⟩
  · rw [v.map_mul, hu, zero_add]
    refine val_nonneg_of_isIntegral v (map_isIntegral_int _ (map_isIntegral_int _ ?_))
    exact IsIntegral.prod _ fun τ _ => (map_isIntegral_int _ (Algebra.IsIntegral.isIntegral α)).pow _
  · rw [hval a Pp hPp f hf, map_mul, _root_.mul_assoc]

end GlobalTheory.DivLevel
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.PowGerm GlobalTheory.PtTie GlobalTheory.RefSum
open GlobalTheory.ThetaLeast

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicValue_translate_divisor_level_integral_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G), P.TorsionIso → CharZero (IsLocalRing.ResidueField T.V) → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (IsLocalRing.maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (IsLocalRing.maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (α : 𝓞 E) (N : ℕ), N ∣ l.M → α * star α = (N : 𝓞 E) → l.Mb ≤ Ideal.span {star α} → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), ThFrame D' ϖ F θ → PullAl D' F oD' α 1 N θ θα → ∀ (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (σ' : U'.toUnifPre.SecGF F (1 * N)) (h : PS F n (chD C.ch)), w.IsGen → ζ ≠ 0 → FinOrd D' F (1 * N) p w ζ → QkToAkU U'.toUnifPre F (1 * N) p x → PhiRel D'.toPre F (1 * N) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → U'.toUnifPre.ExpandsG F (1 * N) σ' t → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (1 * N) σ' h → (∀ k, x ≫ pA.pr k ≫ P.oA.act (star α) = 1) → letI := io.toAlgebra; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∃ (xx : Fin n → Dw.La) (u : F), 0 ≤ v u ∧ ∀ f, IsThRule Xo c nab xx Pp f → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * N) h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) = u * algebraMap T.Fr F (evI y f) := by
  first | exact @GlobalTheory.DivLevel.harmonicValue_translate_dvd | exact GlobalTheory.DivLevel.harmonicValue_translate_dvd | (intros; apply GlobalTheory.DivLevel.harmonicValue_translate_dvd <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfThetaRuleLeLocalValueCharZero
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.PowGerm GlobalTheory.PtTie GlobalTheory.RefSum
open GlobalTheory.ThetaLeast

namespace GlobalTheory.JetsLevelZero

theorem iInf_thRule_le_nuLocOf_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G), P.TorsionIso → CharZero (IsLocalRing.ResidueField T.V) → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (r : ℕ) (Φ M0 : ℝ), GlobalTheory.PtTie.ShortBasis Q r Φ M0 → ∀ (α : 𝓞 E) (q : ℕ), α * star α = ((q : ℕ) : 𝓞 E) → q ∣ l.M → l.Mb ≤ Ideal.span {star α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ), 1 ≤ n → 0 < e → 4 * DF Dw a + 4 ≤ q → (DF Dw a : ℝ) * M0 < q → ∀ P₁ ∈ harmA (Dw := Dw) c a n, (⨅ (f : Rul Xo c) (_ : ∃ x : Fin n → Dw.La, IsThRule Xo c nab x P₁ f), nval T.V e (evI y f)) ≤ GlobalTheory.FactorDepth.nuLocOf C e l.M (MvPolynomial.map io P₁) + (((DF Dw a : ℝ) ^ 2 * Φ / q / e : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab T io y C hTr P hP hchar ϖ hϖ Q hQ r Φ M0 hSB α q hα hqM hMb a n e hn he h4 hM0 P₁ hP₁
  obtain ⟨hΦ, b, hb, hb'⟩ := hSB
  have hth : ThValTot Xo c nab :=
    GlobalTheory.thValTot_of_chartIndep GlobalTheory.firstFiveLaws.1 GlobalTheory.chartIndependence_unconditional E H Dw l Xo c nab hnab
  letI := io.toAlgebra
  obtain ⟨F, _, _, _, _, _, _, v, hv, hvx⟩ : ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : CharZero F)
      (_ : Algebra T.Fr F) (_ : Algebra T.V F) (_ : IsScalarTower T.V T.Fr F) (v : AddValuation F (WithTop ℚ)),
      ValOver ϖ F v ∧ ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ) := by
    obtain ⟨v, hv⟩ := GlobalTheory.ValClosure.exists_valuation_closure T.V ϖ hϖ
    exact ⟨AlgebraicClosure T.Fr, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, v, hv⟩
  obtain ⟨TI⟩ := GlobalTheory.T.nonempty_tateIsometry_integralFramedPoint_chart E H Dw l Xo c T io y C P F
  obtain ⟨D', A', G', _, _, pD, pA, pG, U', PU, _, oD', hx, hact, hθ⟩ :=
    (GlobalTheory.T.exists_productData_copies_trivialisation_valuation E H Dw l Xo c T io y C P ϖ hϖ).2 n
  have hq0 : 0 < q := by omega
  obtain ⟨θ, θα, hθ1, hθ2, hθ3⟩ := hθ F v hv Q hQ α q hq0 hα
  have hcop : ∃ u u' : 𝓞 E, u * α + u' * star α = 1 := by
    have h1 := l.coprime
    have h2 : l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ Ideal.span {α} := by
      refine (Ideal.map_mono hMb).trans ?_
      rw [Ideal.map_span, Set.image_singleton]
      have h3 : (H.bar : 𝓞 E →+* 𝓞 E) (star α) = α := star_star α
      rw [h3]
    have h4' : Ideal.span {star α} ⊔ Ideal.span {α} = ⊤ := top_le_iff.1 (h1 ▸ sup_le_sup hMb h2)
    rw [sup_comm, ← Ideal.span_insert, Ideal.eq_top_iff_one, Ideal.mem_span_pair] at h4'
    exact h4'
  have hu : IsUnit ((q : ℕ) : T.V) := by
    refine (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_
    rw [map_natCast]
    exact Nat.cast_ne_zero.2 hq0.ne'
  have hdeg1 : P₁.totalDegree ≤ DF Dw a := by
    have key : ∀ m ∈ P₁.support, (m.sum fun _ e => e) = DF Dw a := by
      intro m hm
      rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, DF]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => hP₁.1.2.2 m hm τ i
    exact Finset.sup_le fun m' hm' => (key m' hm').le
  unfold nuLocOf
  refine le_iInf_add_coe fun f => le_iInf_add_coe fun hf => ?_
  obtain ⟨f', hf', hff'⟩ := GlobalTheory.T.harmonic_value_integral_germ_frame_power_charZero E H Dw l Xo c T io y C hchar a n l.M q P₁ hP₁ f hf
  set Pp : MvPolynomial (LtN Dw n) T.Fr := MvPolynomial.map io P₁ with hPp
  set x0 := nabValN C.ch.B T.Fr C.ch.h H.w0 l.M f (fun ℓ : LtN Dw n => ℓ.2.2)
    (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp with hx0def
  by_cases hx0 : x0 = 0
  · rw [hx0, nval_zero, EReal.top_add_coe]; exact le_top
  have hx0' : x0 = nabValN C.ch.B T.Fr C.ch.h H.w0 q f' (fun ℓ : LtN Dw n => ℓ.2.2)
      (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp := hff'
  have hmap : (∑ _i : Fin 1, algebraMap T.Fr F (algebraMap T.V T.Fr 1) •
      MvPolynomial.map ((algebraMap T.Fr F).comp io) P₁) = MvPolynomial.map (algebraMap T.Fr F) Pp := by
    rw [Fin.sum_univ_one, map_one, map_one, one_smul, hPp, MvPolynomial.map_map]
  have hdeg : (MvPolynomial.map (algebraMap T.Fr F) Pp).totalDegree ≤ DF Dw a :=
    (Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans
      ((Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans hdeg1)
  have hval := nabValN_algebraMap T.Fr F _ _ C.ch.B C.ch.h (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cc_h C.ch.gauge) H.w0 q n f'
    (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp
  obtain ⟨i, p, w, ζ, x, t₀, t, σ', h, ρ, h1, h2, h3, h4', h5, h6, h7, h8, h9, hρ, hle⟩ :=
    GlobalTheory.JetsLevelZero.rPoint_any E H Dw l Xo c T io y C hTr P hP ϖ hϖ Q hQ F v hv TI Φ M0 r b hΦ hb hb' n D' A' G' pD pA pG U' PU
      oD' hx hact hn α q (DF Dw a) hα hcop hu h4 hM0 θ θα hθ1 hθ2 hθ3 (Fin 1)
      (fun _ => MvPolynomial.map ((algebraMap T.Fr F).comp io) P₁)
      (fun _ => algebraMap T.Fr F (algebraMap T.V T.Fr 1)) (fun _ => val_algebraMap_nonneg T v hvx _)
      (by rw [hmap]; exact hdeg) f' hf' ((vV T.V x0 : ℤ) : ℚ)
      (by rw [hmap, Nat.one_mul, hval, ← hx0']; exact hvx x0 hx0)
  obtain ⟨xx, u, hu0, hrel⟩ := GlobalTheory.T.harmonicValue_translate_divisor_level_integral_chart E H Dw l Xo c nab hnab T io y C hTr P hP hchar ϖ hϖ Q hQ
    F v hv n D' A' G' pD pA pG U' PU oD' hx hact α q hqM hα hMb θ θα hθ2 hθ3 p w ζ x t₀ t σ' h
    h1 h2 h3 h4' h6 h7 h8 h9 h5 a P₁ hP₁
  obtain ⟨g, hg, -⟩ := existsUnique_thRule Xo c nab hth xx hP₁
  have hgv := hrel g hg
  rw [hgv] at hρ
  have hε' : 0 ≤ v u := hu0
  exact (iInf₂_le g ⟨xx, hg⟩).trans (nval_le_of_val T v hvx hx0 hε' hρ hle e)

end GlobalTheory.JetsLevelZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfThetaRuleLeLocalValueCharZeroStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iInf_thetaRule_le_localValue_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G), P.TorsionIso → CharZero (IsLocalRing.ResidueField T.V) → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (r : ℕ) (Φ M0 : ℝ), GlobalTheory.PtTie.ShortBasis Q r Φ M0 → ∀ (α : 𝓞 E) (q : ℕ), α * star α = ((q : ℕ) : 𝓞 E) → q ∣ l.M → l.Mb ≤ Ideal.span {star α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ), 1 ≤ n → 0 < e → 4 * DF Dw a + 4 ≤ q → (DF Dw a : ℝ) * M0 < q → ∀ P₁ ∈ harmA (Dw := Dw) c a n, (⨅ (f : Rul Xo c) (_ : ∃ x : Fin n → Dw.La, IsThRule Xo c nab x P₁ f), nval T.V e (evI y f)) ≤ GlobalTheory.FactorDepth.nuLocOf C e l.M (MvPolynomial.map io P₁) + (((DF Dw a : ℝ) ^ 2 * Φ / q / e : ℝ) : EReal) := by
  first | exact @GlobalTheory.JetsLevelZero.iInf_thRule_le_nuLocOf_charZero | exact GlobalTheory.JetsLevelZero.iInf_thRule_le_nuLocOf_charZero | (intros; apply GlobalTheory.JetsLevelZero.iInf_thRule_le_nuLocOf_charZero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicPolyLocalInvariantNonposChar0
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicPolyLocalInvariantNonposChar0
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth

namespace GlobalTheory.ResZeroDepth

theorem exists_harmA_nuLocOf_nonpos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∃ P₁ ∈ harmA (Dw := Dw) c a n, ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), CharZero (IsLocalRing.ResidueField T.V) → ∀ e k : ℕ, 0 < e → GlobalTheory.FactorDepth.nuLocOf C e k (MvPolynomial.map io P₁) ≤ 0 := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro a n ha hn
  classical
  have hcard : Fintype.card (Lt1 Dw) ≤ n := by
    refine le_trans ?_ hn
    rw [Fintype.card_eq_sum_ones]
    exact Finset.sum_le_sum fun f _ => by unfold rk; omega
  have hdom : Formalism.L2.Pj.DomW Dw a := fun τ i j hij => ha τ hij
  have hinj : Function.Injective (Formalism.L2.Pj.colP Dw hcard) := fun p q h =>
    (Fintype.equivFin _).injective (Fin.castLE_injective hcard h)
  refine ⟨MvPolynomial.map (Int.castRingHom c.F)
      (Formalism.L2.Pj.Crude.Pmin Dw.mult n (Formalism.L2.Pj.colP Dw hcard) fun τ i => a (τ, i)),
    Formalism.L2.Pj.Crude.Pmin_mem Dw.mult n c.F _ _ _ _ _ (fun τ _ => Formalism.L2.Pj.conj_ne_self_of_CM τ) hinj hdom, ?_⟩
  intro T io y C hres e k _
  letI := io.toAlgebra
  have hmap : MvPolynomial.map io (MvPolynomial.map (Int.castRingHom c.F)
      (Formalism.L2.Pj.Crude.Pmin Dw.mult n (Formalism.L2.Pj.colP Dw hcard) fun τ i => a (τ, i))) =
      Formalism.L2.Pj.P1 Dw T a hcard := by
    rw [MvPolynomial.map_map, RingHom.ext_int (io.comp _) (Int.castRingHom T.Fr)]
    rfl
  obtain ⟨-, f, hf, -, hv⟩ := Formalism.L2.Pj.crude_val C.ch.B C.ch.h C.ch.gauge H.w0 k C.ch.uvec
    (Formalism.L2.Pj.satDir_of Formalism.L2.Pj.chart_saturated C) a n hdom hcard
  rw [hmap]
  refine le_trans (iInf_le_of_le f (iInf_le_of_le hf (le_of_eq (congrArg (Formalism.L2.Pj.nval T.V e) hv)))) ?_
  set N := Formalism.L2.Pj.fact1 Dw a hcard with hN
  have hN0 : N ≠ 0 := by
    rw [hN]; unfold Formalism.L2.Pj.fact1
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hu : IsUnit ((N : ℕ) : T.V) := by
    refine (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_
    rw [map_natCast]
    exact Nat.cast_ne_zero.2 hN0
  have hne : ((N : ℕ) : T.Fr) ≠ 0 := by
    rw [← map_natCast (algebraMap T.V T.Fr)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hu.ne_zero
  have hv0 : Formalism.L2.Pj.vV T.V ((N : ℕ) : T.Fr) = 0 := by
    rw [← map_natCast (algebraMap T.V T.Fr)]
    exact GlobalTheory.RefSum.GlobalPoly.vV_of_isUnit T hu
  rw [Formalism.L2.Pj.nval_of_ne hne, hv0]
  simp

end GlobalTheory.ResZeroDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicPolyLocalInvariantNonposChar0Statement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harmonicPoly_localInvariant_nonpos_char0 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∃ P₁ ∈ harmA (Dw := Dw) c a n, ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), CharZero (IsLocalRing.ResidueField T.V) → ∀ e k : ℕ, 0 < e → GlobalTheory.FactorDepth.nuLocOf C e k (MvPolynomial.map io P₁) ≤ 0 := by
  first | exact @GlobalTheory.ResZeroDepth.exists_harmA_nuLocOf_nonpos | exact GlobalTheory.ResZeroDepth.exists_harmA_nuLocOf_nonpos | (intros; apply GlobalTheory.ResZeroDepth.exists_harmA_nuLocOf_nonpos <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JetsCharZero

theorem num_le (dF R N r g0 g1 cst : ℝ) (hR : 0 ≤ R) (hN : 0 ≤ N) (hr : 0 ≤ r) (hg0 : 0 < g0) (hle : g0 ≤ g1)
    (h : R * N ^ 3 * (r * N / 4 + 2 * dF ^ 2) / g0 ≤ cst) : dF ^ 2 * (R * N ^ 3) / g1 ≤ cst := by
  have hX : 0 ≤ R * N ^ 3 := by positivity
  refine le_trans ?_ h
  calc dF ^ 2 * (R * N ^ 3) / g1 ≤ dF ^ 2 * (R * N ^ 3) / g0 := div_le_div_of_nonneg_left (by positivity) hg0 hle
    _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hg0.le
        have : dF ^ 2 ≤ r * N / 4 + 2 * dF ^ 2 := by nlinarith [sq_nonneg dF, mul_nonneg hr hN]
        nlinarith [mul_le_mul_of_nonneg_left this hX]

theorem exists_thRule_value_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G), P.TorsionIso → CharZero (IsLocalRing.ResidueField T.V) → ∀ (φ : ℝ), GlobalTheory.SlopeRec.HasPhi y φ → ∀ (α : 𝓞 E) (q : ℕ), α * star α = ((q : ℕ) : 𝓞 E) → q ∣ l.M → l.Mb ≤ Ideal.span {star α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∑ f : Lt1 Dw, 2 * rk f ≤ n → 1 ≤ n → ∀ (N cst : ℝ), ((Module.finrank ℚ E * Dw.q : ℕ) : ℝ) ≤ N → 4 * DF Dw a + 4 ≤ q → (DF Dw a : ℝ) * (2 * Real.sqrt N) < q → (DF Dw a : ℝ) ^ 2 * ((|(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) / (2 * Module.finrank ℚ E) * N ^ 3) / q ≤ cst → ∃ f ∈ thGen Xo c nab a n, evI y f ≠ 0 ∧ (vV T.V (evI y f) : ℝ) ≤ cst * φ := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab T io y C hTr P hP hch φ hφ α q hα hq hMb a n hanti hs hn N cst hρN h4 hM0 hcst
  obtain ⟨P₁, hP₁, hB⟩ := GlobalTheory.T.exists_harmonicPoly_localInvariant_nonpos_char0 E H Dw l Xo c a n hanti hs
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  obtain ⟨⟨Q, hQ⟩, -⟩ := GlobalTheory.PowData.exists_powData E H Dw l Xo c T io y C P ϖ hϖ
  obtain ⟨ρ, hρ, hSB⟩ := GlobalTheory.ShortPhi.exists_shortBasis E H Dw l Xo c T io y φ hφ C P ϖ hϖ Q hQ
  set R : ℝ := |(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E) / (2 * Module.finrank ℚ E) with hR
  have hR0 : 0 ≤ R := by positivity
  have hρN' : (ρ : ℝ) ≤ N := le_trans (by exact_mod_cast hρ) hρN
  have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := hρ0.trans hρN'
  have hM0' : (DF Dw a : ℝ) * (2 * Real.sqrt ρ) < q := lt_of_le_of_lt (by gcongr) hM0
  have hup := GlobalTheory.T.iInf_thetaRule_le_localValue_charZero E H Dw l Xo c nab hnab T io y C hTr P hP hch ϖ hϖ Q hQ ρ _ _ hSB α q hα hq hMb a n 1 hn one_pos h4
    hM0' P₁ hP₁
  have hloc := hB T io y C hch 1 l.M one_pos
  have hφ0 := hφ.nonneg
  have hq0 : (0 : ℝ) < q := by
    have h : 0 < q := by omega
    exact_mod_cast h
  set B : ℝ := (DF Dw a : ℝ) ^ 2 * (R * (ρ : ℝ) ^ 3 * φ) / q / ((1 : ℕ) : ℝ) with hBdef
  have hBle : B ≤ cst * φ := by
    rw [hBdef, Nat.cast_one, div_one]
    calc (DF Dw a : ℝ) ^ 2 * (R * (ρ : ℝ) ^ 3 * φ) / q ≤ (DF Dw a : ℝ) ^ 2 * (R * N ^ 3 * φ) / q := by gcongr
      _ = (DF Dw a : ℝ) ^ 2 * (R * N ^ 3) / q * φ := by ring
      _ ≤ cst * φ := by gcongr
  have hinf : (⨅ (f : Rul Xo c) (_ : ∃ x : Fin n → Dw.La, IsThRule Xo c nab x P₁ f), nval T.V 1 (evI y f)) ≤
      ((B : ℝ) : EReal) := by
    refine hup.trans ?_
    calc _ ≤ (0 : EReal) + ((B : ℝ) : EReal) := add_le_add hloc le_rfl
      _ = _ := zero_add _
  by_contra hne
  push_neg at hne
  have hlow : (((⌊B⌋ + 1 : ℤ) : ℝ) : EReal) ≤
      ⨅ (f : Rul Xo c) (_ : ∃ x : Fin n → Dw.La, IsThRule Xo c nab x P₁ f), nval T.V 1 (evI y f) := by
    refine le_iInf₂ fun f ⟨x, hx⟩ => ?_
    have hf : f ∈ thGen Xo c nab a n := ⟨x, P₁, hP₁, hx⟩
    by_cases h0 : evI y f = 0
    · rw [h0, nval_zero]; exact le_top
    have h1 := hne f hf h0
    rw [nval_of_ne h0, Nat.cast_one, div_one, EReal.coe_le_coe_iff]
    have h2 : B < (vV T.V (evI y f) : ℝ) := lt_of_le_of_lt hBle h1
    have h3 : ⌊B⌋ < vV T.V (evI y f) := Int.floor_lt.2 h2
    exact_mod_cast h3
  have h5 := EReal.coe_le_coe_iff.1 (hlow.trans hinf)
  push_cast at h5
  linarith [Int.lt_floor_add_one B]

end GlobalTheory.JetsCharZero

end
