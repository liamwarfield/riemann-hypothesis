module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniformisedChartAfterValuationRingExt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsExtensionAllModelsUniformized

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledThetaLatticeLeSupLatticeEveryWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledThetaLatticeLeSupLatticeEveryWeight
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PlaceTop

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem vLa_int_mul_natCast {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (n : ℕ)
    (hs : a * (n : 𝓞 K) ≠ 0) :
    vLa la ((a * (n : 𝓞 K) : 𝓞 K) : K) = vLa la (a : K) + vLa la (n : K) := by
  have ha : (a : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr (left_ne_zero_of_mul hs)
  have hn : (n : K) ≠ 0 := by
    have : n ≠ 0 := by
      rintro rfl
      exact hs (by simp)
    exact Nat.cast_ne_zero.2 this
  have e : ((a * (n : 𝓞 K) : 𝓞 K) : K) = (a : K) * (n : K) := by
    show algebraMap (𝓞 K) K _ = _
    rw [map_mul, map_natCast]
  rw [e, Crude.crv_vLa_mul la ha hn]

theorem thetaScalar_ne_zero {D : D7} (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) {j : ℕ}
    (w : WeightFamilies.Wt D j) : GlobalTheory.RunIn.sOf B hinj EX w ≠ 0 := by
  have hn : ∀ i, EX.piG i * piBarO EX i = (D.host.g i : 𝓞 D.host.E) := fun i => by
    apply Subtype.ext
    exact EX.piG_norm i
  have hn' : ∀ i, iE D hinj B (EX.piG i) * iE D hinj B (piBarO EX i) ≠ 0 := fun i => by
    rw [← map_mul, hn, map_natCast]
    exact Nat.cast_ne_zero.2 (D.host.g_prime i).ne_zero
  refine mul_ne_zero ?_ ?_
  · unfold nnW
    exact Finset.prod_ne_zero_iff.2 fun i _ =>
      mul_ne_zero (pow_ne_zero _ (left_ne_zero_of_mul (hn' i))) (pow_ne_zero _ (right_ne_zero_of_mul (hn' i)))
  · refine Nat.cast_ne_zero.2 ?_
    unfold pPow
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ D.host.hyp.1.ne_zero))
      (pow_ne_zero _ D.host.hyp.2.1.ne_zero)

theorem thInt_of_oriented (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (hO : Oriented T EX) (w : WeightFamilies.Wt D j) :
    GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w := by
  have hs := thetaScalar_ne_zero (recB h.toLawsCore) hinj EX w
  refine Pf.WWc_le_Mlat (recPJ h j hj) _ hs w ?_
  intro G hG la y
  have hG' : G.1 ∈ Submodule.span (𝓞 T.Q.c.F) (T.th j w) := hG
  refine (Pf.le_val_of_mem_span (isVal_vAt (y : T.PtA j la)) (fun g hg => ?_) _ hG').trans
    (recPJ_vAt_inc h j hj la y w G).ge
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) (GlobalTheory.T.thetaGenerator_place_valuation_bound D T h j hj hinj EX hO w g hg la y)
  have h1 := GlobalTheory.T.ramified_prime_loss_le_valuation_prime_power D T.Q.c.F la j w _ _ le_rfl le_rfl
  have h2 := vLa_int_mul_natCast (K := T.Q.c.F) la (nnW (recB h.toLawsCore) hinj EX w) _ hs
  have h3 : ((vAdd la ((GlobalTheory.RunIn.sOf (recB h.toLawsCore) hinj EX w : 𝓞 (recB h.toLawsCore).KO) :
      (recB h.toLawsCore).KO) : ℤ) : ℝ) = _ := congrArg (fun z : ℤ => (z : ℝ)) h2
  rw [h3, Int.cast_add]
  exact neg_le_neg ((add_comm _ _).le.trans (add_le_add le_rfl h1))

end GlobalTheory.PlaceTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledThetaLatticeLeSupLatticeEveryWeightStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledThetaLattice_le_supLattice_every_weight : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D), Oriented T EX → ∀ w : WeightFamilies.Wt D j, GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w := by
  first | exact @GlobalTheory.PlaceTop.thInt_of_oriented | exact GlobalTheory.PlaceTop.thInt_of_oriented | (intros; apply GlobalTheory.PlaceTop.thInt_of_oriented <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvROfFrMapFromTest
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteExtUniformisedChartRationalTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteExtIntegralChartUniformisedModel
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteExtIntegralChartUniformisedModel
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem GlobalTheory.PlaceInt.exists_ext_intChart_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), T.FinRes → ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (y' : IntFr Xo c T' (iT.comp io)) (C' : IntegralChartA3 Xo c T' (iT.comp io) y'), IsExt y iT e y' ∧ T'.FinRes ∧ Good3 C' := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y hT
  obtain ⟨T', io', y', e, hA, he, hU, φ, hv, hφ⟩ := GlobalTheory.T.exists_extension_all_models_uniformized E H Dw l Xo c T io y hT
  obtain ⟨iT, hiT⟩ : ∃ iT : T.Fr →+* T'.Fr,
      (letI := io.toAlgebra; letI := io'.toAlgebra; φ.toRingHom) = iT := ⟨_, rfl⟩
  have hio : io' = iT.comp io := by
    subst hiT
    letI := io.toAlgebra
    letI := io'.toAlgebra
    exact RingHom.ext fun a => (φ.commutes a).symm
  have hv' : ∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a := by
    intro a
    by_cases ha : a = 0
    · subst ha
      simp [vV]
    · rw [← hiT]
      exact hv a ha
  subst hio
  obtain ⟨C', hC'⟩ := GlobalTheory.IntChartTrunc.intChart_frTrunc_exists E H Dw l Xo c hstar T' (iT.comp io) y'
  exact ⟨T', iT, e, y', C', ⟨he, hv', φ, hiT, hφ⟩, hA, hC', hU C'.I⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteExtIntegralChartUniformisedModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteExt_integralChart_uniformisedModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), T.FinRes → ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (y' : IntFr Xo c T' (iT.comp io)) (C' : IntegralChartA3 Xo c T' (iT.comp io) y'), IsExt y iT e y' ∧ T'.FinRes ∧ Good3 C' := by
  first | exact @GlobalTheory.PlaceInt.exists_ext_intChart_unif | exact GlobalTheory.PlaceInt.exists_ext_intChart_unif | (intros; apply GlobalTheory.PlaceInt.exists_ext_intChart_unif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteExtUniformisedChartRationalTorsion
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlacePrep

theorem exists_good_chart_allRat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), T.FinRes → ∀ M : ℕ, 0 < M → ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (y' : IntFr Xo c T' (iT.comp io)) (C' : IntegralChartA3 Xo c T' (iT.comp io) y'), IsExt y iT e y' ∧ T'.FinRes ∧ Good3 C' ∧ AllRat Xo (xOf y') M := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y hfin M hM
  obtain ⟨T₁, i₁, e₁, y₁, C₁, hext₁, hfin₁, hgood₁⟩ := GlobalTheory.T.exists_finiteExt_integralChart_uniformisedModel E H Dw l Xo c hstar T io y hfin
  obtain ⟨L, _, _, hL, hrat⟩ := (GlobalTheory.T.torsion_rational_over_finite_extension_level_structure E H Dw l Xo T₁.Fr (xOf y₁) M hM).1
  obtain ⟨T₂, i₂, e₂, ψ, φ, he₂, hv₂, hψ, -, hfin₂⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T₁ L
  obtain ⟨⟨y₂, hext₂⟩, hy⟩ := GlobalTheory.T.exists_integralFramedPoint_baseChange_cdvr_transitive E H Dw l Xo c T₁ T₂ (i₁.comp io) y₁ i₂ e₂ he₂ hv₂
  have hx₂ := (hy y₂ hext₂).1
  obtain ⟨C₂, hgood₂⟩ := GlobalTheory.T.exists_uniformised_chart_after_valuation_ring_ext E H Dw l Xo c hstar T₁ (i₁.comp io) y₁ C₁ hgood₁ T₂ i₂ e₂ y₂ hext₂
  have htr := ((GlobalTheory.T.exists_integralFramedPoint_baseChange_cdvr_transitive E H Dw l Xo c T T₁ io y i₁ e₁ hext₁.1 hext₁.2.1).2 y₁ hext₁).2 T₂ i₂ e₂ y₂ hext₂
  have hrat₂ := ((GlobalTheory.T.torsion_rational_over_finite_extension_level_structure E H Dw l Xo L _ M hM).2 hrat).1 T₂.Fr ψ.toRingHom
  have hi : i₂ = ψ.toRingHom.comp (algebraMap T₁.Fr L) := RingHom.ext fun a => (hψ a).symm
  have hsp : spMap ψ.toRingHom ≫ spMap (algebraMap T₁.Fr L) ≫ xOf y₁ = xOf y₂ := by
    rw [hx₂, hi, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    rfl
  rw [hsp] at hrat₂
  exact ⟨T₂, i₂.comp i₁, e₂ * e₁, y₂, C₂, htr, hfin₂ hfin₁, hgood₂, hrat₂⟩

end GlobalTheory.PlacePrep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteExtUniformisedChartRationalTorsionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteExt_uniformisedChart_rationalTorsion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), T.FinRes → ∀ M : ℕ, 0 < M → ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (y' : IntFr Xo c T' (iT.comp io)) (C' : IntegralChartA3 Xo c T' (iT.comp io) y'), IsExt y iT e y' ∧ T'.FinRes ∧ Good3 C' ∧ AllRat Xo (xOf y') M := by
  first | exact @GlobalTheory.PlacePrep.exists_good_chart_allRat | exact GlobalTheory.PlacePrep.exists_good_chart_allRat | (intros; apply GlobalTheory.PlacePrep.exists_good_chart_allRat <;> assumption)
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem GlobalTheory.PlaceInt.evR_of_frMap_fromTest {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (f : Rul Xo c)
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {K₁ K₂ : Type} [CommRing K₁] [Algebra c.F K₁] [CommRing K₂] [Algebra c.F K₂] (φ : K₁ →ₐ[c.F] K₂)
    (y₁ : FrPt Xo c K₁) (hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y₁)
    (y₂ : FrPt Xo c K₂) (hm : FrMap φ y₁ y₂) : evR Xo c f y₂ = φ (evR Xo c f y₁) := by
  obtain ⟨p, ψ, y', hy'⟩ := hT
  unfold evR
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hWD f hf p ψ y' y₁ hy',
    ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hWD f hf p (φ.comp ψ) y' y₂ (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ψ φ hy' hm)]
  rfl


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.PlaceInt.short_value_on_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [StarRing (𝓞 E)], d.IsLev → IsNab d.Xo₂ d.c₂ d.nab₂ → ∀ m₀ : ℕ, (∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ ^ m₀ = 1) → ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → ∀ (x0 : Fin n → Dw.La) (g : Rul Xo c), g ∈ sec Xo c w n → IsShortRule Xo c d Λ N x0 P g → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), T.FinRes → ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (io₂ : d.c₂.F →+* T'.Fr) (y₂ : IntFr d.Xo₂ d.c₂ T' io₂) (C : IntegralChartA3 d.Xo₂ d.c₂ T' io₂ y₂) (ζ : T'.Fr) (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO d.Xo₂ (xOf y₂) ⟶ d.Xo₂.univ.t.G)) (tp : (Fin n → LevQ Dw d.l₂) → Fin n → (ptO d.Xo₂ (xOf y₂) ⟶ d.Xo₂.univ.t.G)) (F : (Fin n → LevQ Dw d.l₂) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow d.Xo₂.univ.t.G d.Xo₂.univ.t.PP.L ((N : ℤ) ^ 2) (ptO d.Xo₂ (xOf y₂)))), 0 < e ∧ (∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) ∧ T'.FinRes ∧ (∀ a : c.F, io₂ (d.eF a) = iT (io a)) ∧ Good3 C ∧ AllRat d.Xo₂ (xOf y₂) (N ^ 2) ∧ ζ ^ m₀ = 1 ∧ (∀ i, InZh d.Xo₂ Λ N (z i)) ∧ GeoInj d.Xo₂ (xOf y₂) z ∧ (∀ q b, tp q b ^ N = levPt d.Xo₂ (xOf y₂) (levRep (q b)) ∧ ∃ j : ℕ, KilledBy d.Xo₂ (d.l₂.Mb ^ j) (tp q b)) ∧ (∀ q i b, IsUUOver d.Xo₂.univ.t.G d.Xo₂.univ.t.PP N (sOf1 y₂) (z i b) (tp q b) (F q i b)) ∧ (letI := io₂.toAlgebra; iT (evI y g) = ζ * (io₂ ((d.eF (betaH (Dw := Dw) c Λ))⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : d.c₂.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw d.l₂) : d.c₂.F))⁻¹ * ((N : d.c₂.F) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree)⁻¹) * ∑ᶠ q : Fin n → LevQ Dw d.l₂, io₂ (d.w x0 q) * ∑ i, hv d.Xo₂ d.c₂ d.nab₂ y₂.1 (N ^ 2) (fun b => sqN d.Xo₂ N (F q i b)) (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P))) := by
  intro E _ _ _ H Dw l Xo c n d _ hlev hnab m₀ hm₀ Λ N hU hT hL w P hP x0 g hg hsh T io y hfin
  have laws : Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨T₁, i₁, e₁, y₁, io₁, z₁, ⟨he₁, hv₁, φ₁, hφ₁, hm₁⟩, hfin₁, hio₁, hover⟩ :=
    GlobalTheory.T.exists_finiteExtension_integralFramedPoint_lift_cover E H Dw l Xo c n d hlev T io y hfin
  have hN : 0 < N := hL.1.pos
  obtain ⟨T₂, i₂, e₂, z₂, C, ⟨he₂, hv₂, φ₂, hφ₂, hm₂⟩, hfin₂, hgood, hrat⟩ :=
    GlobalTheory.T.exists_finiteExt_uniformisedChart_rationalTorsion E H Dw d.l₂ d.Xo₂ d.c₂ hnab.1 T₁ io₁ z₁ hfin₁ (N ^ 2) (pow_pos hN 2)
  letI a0 : Algebra c.F T.Fr := io.toAlgebra
  letI a1 : Algebra c.F T₁.Fr := (i₁.comp io).toAlgebra
  letI b1 : Algebra d.c₂.F T₁.Fr := io₁.toAlgebra
  letI b2 : Algebra d.c₂.F T₂.Fr := (i₂.comp io₁).toAlgebra
  obtain ⟨z, tp, F, hz, hinj, htp, hF⟩ :=
    (GlobalTheory.RatData.exists_thetaVal_data E H Dw d.l₂ d.Xo₂ d.c₂ T₂.Fr z₂.1).2 n Λ N hU hL hrat
  obtain ⟨k, _, _, jk, -⟩ : ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (jk : T₂.Fr →+* k), True :=
    ⟨AlgebraicClosure T₂.Fr, inferInstance, inferInstance, algebraMap _ _, trivial⟩
  letI ak : Algebra c.F k := ((jk.comp i₂).comp (i₁.comp io)).toAlgebra
  letI bk : Algebra d.c₂.F k := (jk.comp (i₂.comp io₁)).toAlgebra
  let ψ₁ : T₁.Fr →ₐ[c.F] k := { jk.comp i₂ with commutes' := fun _ => rfl }
  let ψ₂ : T₂.Fr →ₐ[d.c₂.F] k := { jk with commutes' := fun _ => rfl }
  obtain ⟨yk, hyk⟩ := GlobalTheory.FramedBaseChange.exists_frMap laws E H Dw l Xo c _ _ ψ₁ y₁.1
  obtain ⟨zk, hzk⟩ := GlobalTheory.FramedBaseChange.exists_frMap laws E H Dw d.l₂ d.Xo₂ d.c₂ _ _ ψ₂ z₂.1
  have hc1 : ∀ a : c.F, algebraMap d.c₂.F T₁.Fr (d.eF a) = algebraMap c.F T₁.Fr a := hio₁
  have hck : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a =>
    congrArg (fun t => jk (i₂ t)) (hio₁ a)
  have hoverk : FrOver d zk yk :=
    (GlobalTheory.frames_lift_to_cover laws E H Dw l Xo c n d).2.1 T₁.Fr hc1 k hck ψ₁ (ψ₂.comp φ₂)
      (by
        show jk.comp φ₂.toRingHom = jk.comp i₂
        rw [hφ₂])
      y₁.1 z₁.1 yk zk hover hyk (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans φ₂ ψ₂ hm₂ hzk)
  obtain ⟨v, hv, hev⟩ := hsh k hck yk zk hoverk
  have hPh := ((GlobalTheory.PlaceInt.eF_transfer E H Dw l Xo c n d Λ).2.1 w P hP).1.1
  have hval := GlobalTheory.T.shortThetaValue_field_eq_map_subfield_data E H Dw d.l₂ d.Xo₂ d.c₂ hnab.1 d.nab₂ hnab n Λ N hU hT hL w _ hPh (d.w x0) _
    T₂.Fr k ψ₂ z₂.1 zk hzk z tp F hz hinj htp hF v hv
  have e1 : evR Xo c g yk = (ψ₁.comp φ₁) (evR Xo c g y.1) :=
    GlobalTheory.PlaceInt.evR_of_frMap_fromTest (GlobalTheory.Frames.algebraic_laws laws.secBaseChange E H Dw l Xo c).2.2.1 g hg.1 _ y.1 y.2.1 yk
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans φ₁ ψ₁ hm₁ hyk)
  have e2 : evR d.Xo₂ d.c₂ d.cδ zk = ψ₂ (evR d.Xo₂ d.c₂ d.cδ z₂.1) :=
    GlobalTheory.PlaceInt.evR_of_frMap_fromTest (GlobalTheory.Frames.algebraic_laws laws.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂).2.2.1 d.cδ hlev.2.2.2.2.2.2.2.1.1 _ z₂.1 z₂.2.1 zk hzk
  refine ⟨T₂, i₂.comp i₁, e₂ * e₁, i₂.comp io₁, z₂, C, evR d.Xo₂ d.c₂ d.cδ z₂.1, z, tp, F, Nat.mul_pos he₂ he₁, ?_, hfin₂,
    fun a => congrArg i₂ (hio₁ a), hgood, hrat, hm₀ _ _, hz, hinj, htp, hF, ?_⟩
  · intro a
    rw [RingHom.comp_apply, hv₂, hv₁]
    push_cast
    ring
  · apply jk.injective
    rw [e1, e2, hval, ← map_mul] at hev
    have e3 : jk ((i₂.comp i₁) (evI y g)) = (ψ₁.comp φ₁) (evR Xo c g y.1) := by
      show jk (i₂ (i₁ (evR Xo c g y.1))) = jk (i₂ (φ₁.toRingHom (evR Xo c g y.1)))
      rw [hφ₁]
    rw [e3, hev]
    rfl
end
