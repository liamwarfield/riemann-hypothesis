module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompLawsModelRootBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginPointCompare
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsHolomorphicDiscAvoidingPole
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscComponentGrowth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationAtPrimeIsDiscreteValuationRingOfHeigStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginWeightSection
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginWeightSection
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.VsReg

theorem le_exp_mul_pow_of_log_le {P r A B : ℝ} {M : ℕ} (hP : 0 < P) (hr : 1 ≤ r) (hB : B ≤ M)
    (h : Real.log P ≤ A + B * Real.log r) : P ≤ Real.exp A * r ^ M := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hl : 0 ≤ Real.log r := Real.log_nonneg hr
  have h1 : Real.log P ≤ A + (M : ℝ) * Real.log r := by nlinarith
  calc P = Real.exp (Real.log P) := (Real.exp_log hP).symm
    _ ≤ Real.exp (A + (M : ℝ) * Real.log r) := Real.exp_le_exp.2 h1
    _ = Real.exp A * r ^ M := by rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hr0]

theorem sing_prod_le_rW_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (n : RootIx Dw → ℤ), ∀ w₀ ∈ mcPts (mCoordIdeal RM.y), ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ᶠ w in 𝓝 w₀, w ∈ mcPts (mCoordIdeal RM.y) → ∀ x : Or.Re.R.X, SameOrbit (Or.Re.R.lift x x) w → Or.Re.π x ∈ Sys.open' → ∏ r, (Or.sing r).h w ^ n r ≤ C * ReciprocityTheory.AnForm.P.rW Sys.L Sys.s (Or.Re.π x) ^ M := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or n w₀ hw₀
  let f : CMType H → Fin (Dw.p + Dw.q) → ℝ := fun τ i => -(n (τ, i) : ℝ)
  let cf : RootIx Dw → ℝ := fun r => GlobalTheory.CompanionTheory.Ar.Small.Fund.fundCo (f r.1) r.2
  let Bf : RootIx Dw → ℝ := fun r => |Real.log ((Or.Re.ref (some r)).h w₀)| + 1
  let T : Set ((Σ k, RM.ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  have hb : ∀ r : RootIx Dw, ∀ᶠ w in 𝓝[T] w₀, |Real.log ((Or.Re.ref (some r)).h w)| ≤ Bf r := by
    intro r
    have hc : ContinuousWithinAt (Or.Re.ref (some r)).h T w₀ :=
      (Or.Re.ref_smooth (some r)).continuousOn w₀ hw₀.1
    have hc' : ContinuousWithinAt (fun w => |Real.log ((Or.Re.ref (some r)).h w)|) T w₀ :=
      (hc.log ((Or.Re.ref (some r)).pos w₀ hw₀.1).ne').abs
    exact (hc'.tendsto.eventually (Iio_mem_nhds (lt_add_one _))).mono fun _ h => le_of_lt h
  have hall : ∀ᶠ w in 𝓝 w₀, w ∈ T → ∀ r : RootIx Dw, |Real.log ((Or.Re.ref (some r)).h w)| ≤ Bf r :=
    eventually_nhdsWithin_iff.1 (Filter.eventually_all.2 hb)
  let A : ℝ := ∑ r, |cf r| * Bf r
  let Bc : ℝ := ∑ r, |cf r| * |Sys.C₅|
  refine ⟨Real.exp A, ⌈Bc⌉₊, (Real.exp_pos _).le, ?_⟩
  filter_upwards [hall] with w hw hwm x hso hop
  have hwT : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := hwm.1
  have hbd := hw hwT

  have hsum : ∀ τ i, Real.log ((Or.Re.ref (some (τ, i))).h w) + Sys.ph (some (τ, i)) (Or.Re.π x) =
      -∑ k ∈ Finset.Iic i, Real.log ((Or.sing (τ, k)).h w) := by
    intro τ i
    have e := Or.fund_sing τ i x hop
    have hdeg : (Or.Re.ref (some (τ, i))).a = -∑ k ∈ Finset.Iic i, (Or.sing (τ, k)).a := by
      rw [Or.fund_deg τ i]
      simp only [Or.sing_deg]
    have b := OrArch.log_add_sum_of_sameOrbit (Finset.Iic i) (fun k => Or.sing (τ, k)) hdeg hso hwT
    linarith
  have e2 := GlobalTheory.CompanionTheory.Ar.Small.Fund.sum_neg_mul_eq_sum_fundCo f
    (fun r => Real.log ((Or.sing r).h w))
    (fun r => Real.log ((Or.Re.ref (some r)).h w) + Sys.ph (some r) (Or.Re.π x)) hsum
  have hlog : Real.log (∏ r, (Or.sing r).h w ^ n r) =
      ∑ r : RootIx Dw, -f r.1 r.2 * Real.log ((Or.sing r).h w) := by
    rw [Real.log_prod fun r _ => zpow_ne_zero _ ((Or.sing r).pos _ hwT).ne']
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Real.log_zpow]
    simp [f]

  set L : ℝ := Real.log (ReciprocityTheory.AnForm.P.rW Sys.L Sys.s (Or.Re.π x)) with hL
  have hre : Real.exp 1 ≤ ReciprocityTheory.AnForm.P.rW Sys.L Sys.s (Or.Re.π x) := by
    have := Sys.norm_le (Or.Re.π x)
    unfold ReciprocityTheory.AnForm.P.rW
    linarith
  have hr1 : 1 ≤ ReciprocityTheory.AnForm.P.rW Sys.L Sys.s (Or.Re.π x) :=
    le_trans (Real.one_le_exp zero_le_one) hre
  have hL1 : 1 ≤ L := (Real.le_log_iff_exp_le (lt_of_lt_of_le one_pos hr1)).2 hre
  have hph : ∀ r : RootIx Dw, |Sys.ph (some r) (Or.Re.π x)| ≤ |Sys.C₅| * L := by
    intro r
    obtain ⟨h1, h2⟩ := (Sys.sing (some r)).2.2.2 (Or.Re.π x) hop
    have hC : Sys.C₅ ≤ |Sys.C₅| := le_abs_self _
    have hC0 : 0 ≤ |Sys.C₅| := abs_nonneg _
    rw [abs_le]
    constructor <;> nlinarith
  have hle : Real.log (∏ r, (Or.sing r).h w ^ n r) ≤ A + Bc * L := by
    rw [hlog, e2]
    have : A + Bc * L = ∑ r, |cf r| * (Bf r + |Sys.C₅| * L) := by
      simp only [A, Bc, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [this]
    refine Finset.sum_le_sum fun r _ => ?_
    have h3 : |Real.log ((Or.Re.ref (some r)).h w) + Sys.ph (some r) (Or.Re.π x)| ≤
        Bf r + |Sys.C₅| * L := (abs_add_le _ _).trans (add_le_add (hbd r) (hph r))
    calc cf r * (Real.log ((Or.Re.ref (some r)).h w) + Sys.ph (some r) (Or.Re.π x))
        ≤ |cf r * (Real.log ((Or.Re.ref (some r)).h w) + Sys.ph (some r) (Or.Re.π x))| := le_abs_self _
      _ = |cf r| * |Real.log ((Or.Re.ref (some r)).h w) + Sys.ph (some r) (Or.Re.π x)| := abs_mul _ _
      _ ≤ |cf r| * (Bf r + |Sys.C₅| * L) := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  exact le_exp_mul_pow_of_log_le (Finset.prod_pos fun r _ => zpow_pos ((Or.sing r).pos _ hwT) _)
    hr1 (Nat.le_ceil _) hle

end GlobalTheory.CompanionTheory.Ar.VsReg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginWeightSectionStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_weight_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (n : RootIx Dw → ℤ), ∀ w₀ ∈ mcPts (mCoordIdeal RM.y), ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ᶠ w in 𝓝 w₀, w ∈ mcPts (mCoordIdeal RM.y) → ∀ x : Or.Re.R.X, SameOrbit (Or.Re.R.lift x x) w → Or.Re.π x ∈ Sys.open' → ∏ r, (Or.sing r).h w ^ n r ≤ C * ReciprocityTheory.AnForm.P.rW Sys.L Sys.s (Or.Re.π x) ^ M := by
  first | exact @GlobalTheory.CompanionTheory.Ar.VsReg.sing_prod_le_rW_pow | exact GlobalTheory.CompanionTheory.Ar.VsReg.sing_prod_le_rW_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.VsReg.sing_prod_le_rW_pow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginExistsForm
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginExistsForm
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.OffForm

open AlgebraicGeometry CategoryTheory MvPolynomial GlobalTheory.CompanionTheory.Ar.Small.RepAt GlobalTheory.CompanionTheory.Ar.AlgPoly

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {y : (Σ k, J k) → Ω} {w : (Σ k, J k) → ℂ}

theorem valAt_ratio (hw : CoordsAt ξ y z w) (c : ∀ k, J k) (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) (p : Σ k, J k) :
    ValAt ξ z (y p / y ⟨p.1, c p.1⟩) (w p / w ⟨p.1, c p.1⟩) := by
  obtain ⟨k, i⟩ := p
  obtain ⟨r, hr, e⟩ := (hw.2 k (c k) (hc k)).2 i
  show ValAt ξ z _ (w ⟨k, i⟩ / w ⟨k, c k⟩)
  rw [e, mul_div_cancel_right₀ _ (hc k).ne_zero]
  exact hr

theorem valAt_aeval (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (c : ∀ k, J k)
    (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) (g : MRing J) :
    ValAt ξ z (aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) g)
      (aeval (fun p : Σ k, J k => w p / w ⟨p.1, c p.1⟩) g) := by
  induction g using MvPolynomial.induction_on with
  | C n => simpa using valAt_intCast hz n
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _)]
    exact valAt_add ha hb
  | mul_X a p ha =>
    rw [map_mul, map_mul, aeval_X, aeval_X]
    exact valAt_mul ha (valAt_ratio hw c hc p)

theorem aeval_form_ratio {L : Type} [Field L] (v : (Σ k, J k) → L) (c : ∀ k, J k) (hv : ∀ k, v ⟨k, c k⟩ ≠ 0)
    {G : MRing J} {d : K → ℕ} (hG : IsMultiHomog G d) :
    aeval v G = aeval (fun p : Σ k, J k => v p / v ⟨p.1, c p.1⟩) G * ∏ k, v ⟨k, c k⟩ ^ d k := by
  have h := GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.aeval_scaled_homog (fun p : Σ k, J k => v p / v ⟨p.1, c p.1⟩)
    (fun k => v ⟨k, c k⟩) hG
  rw [← h]
  congr 2
  funext p
  exact (div_mul_cancel₀ _ (hv p.1)).symm

theorem unitAt_of_valAt (hz : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (ha : ValAt ξ z a r) (hr : r ≠ 0) :
    unitAt ξ ⟨centre z, hz⟩ a := by
  obtain ⟨h, s, hs, hsr⟩ := valAt_iff.1 ha
  have hu : IsUnit s := GlobalTheory.CompanionTheory.Ar.CxVal.isUnit _ (by rw [show (Scheme.stalkClosedPointTo z).hom s = r from hsr]; exact hr)
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  have e : a * genMap ξ ⟨centre z, hz⟩ t = 1 := by
    have := congrArg (genMap ξ ⟨centre z, hz⟩) ht
    rwa [map_mul, map_one, hs] at this
  refine ⟨left_ne_zero_of_mul_eq_one e, ⟨s, hs⟩, ⟨t, ?_⟩⟩
  exact eq_inv_of_mul_eq_one_right e

theorem unitAt_div {p : Cpt ξ} {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a / b) := by
  refine ⟨div_ne_zero ha.1 hb.1, ?_, ?_⟩
  · rw [div_eq_mul_inv]
    exact mul_mem ha.2.1 hb.2.2
  · rw [inv_div, div_eq_mul_inv]
    exact mul_mem hb.2.1 ha.2.2

theorem unitAt_of_forms (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (c : ∀ k, J k)
    (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) {d : K → ℕ} {G Hf : MRing J} (hG : IsMultiHomog G d) (hH : IsMultiHomog Hf d)
    {ε : Ω} (hHy : aeval y Hf ≠ 0) (hGy : aeval y G = ε * aeval y Hf) (hGw : aeval w G ≠ 0) (hHw : aeval w Hf ≠ 0) :
    unitAt ξ ⟨centre z, hz⟩ ε := by
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (hc k)).1
  have hw0 : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have uG := unitAt_of_valAt hz (valAt_aeval hz hw c hc G) (by
    intro h0
    apply hGw
    rw [aeval_form_ratio w c hw0 hG, h0, zero_mul])
  have uH := unitAt_of_valAt hz (valAt_aeval hz hw c hc Hf) (by
    intro h0
    apply hHw
    rw [aeval_form_ratio w c hw0 hH, h0, zero_mul])
  have hM : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
  have e : ε = aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G /
      aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) Hf := by
    rw [aeval_form_ratio y c hy hG, aeval_form_ratio y c hy hH, ← mul_assoc] at hGy
    have h1 := mul_right_cancel₀ hM hGy
    rw [h1, mul_div_cancel_right₀ _ uH.1]
  rw [e]
  exact unitAt_div uG uH

end GlobalTheory.CompanionTheory.Ar.Small.OffForm


open GlobalTheory.CompanionTheory.Ar.Small.OffForm in
theorem GlobalTheory.CompanionTheory.RootForm.exists_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (GlobalTheory.CompanionTheory.Ar.CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (GlobalTheory.CompanionTheory.Ar.CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx), ∃ f : MRing RM.ι, Small.IsFormOff (mCoordIdeal RM.y) f ∧ ∀ w ∈ mcPts (mCoordIdeal RM.y), MvPolynomial.aeval w f ≠ 0 → ∀ x : Or.Re.R.X, SameOrbit (Or.Re.R.lift x x) w → Or.Re.π x ∈ Sys.open' := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or
  obtain ⟨cc, hch⟩ := Or.𝔐.tie.cover ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
  have hy : ∀ k, RM.y ⟨k, cc k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hch.1 k (Finset.mem_univ k)
  have ya : Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) = RM.y ⟨Or.k₀, cc Or.k₀⟩ := by
    rw [← Or.y_eq, Equiv.apply_symm_apply]
  have ht0 : (∏ r, ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _
      (smul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) (Or.lines r).1)
  have hε : Or.g Fx.sE * Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) ^ Fx.q' /
      (∏ r, ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r)) ≠ 0 := by
    refine div_ne_zero (mul_ne_zero ((map_ne_zero Or.g).2 Fx.sE_ne) (pow_ne_zero _ ?_)) ht0
    rw [ya]
    exact hy _
  obtain ⟨d, G, Hf, hG, hH, hHy, hGy⟩ := RM.birational (Or.g Fx.sE * Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) ^ Fx.q' /
      (∏ r, ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r)))
  have hGy0 : MvPolynomial.aeval RM.y G ≠ 0 := by
    rw [hGy]
    exact mul_ne_zero hε hHy
  have hform := GlobalTheory.CompanionTheory.Ar.AlgPoly.form_mul (GlobalTheory.CompanionTheory.Ar.AlgPoly.form_mul hG hH)
    (GlobalTheory.CompanionTheory.Ar.Small.RepAt.form_mono cc fun _ => 1)
  refine ⟨G * Hf * GlobalTheory.CompanionTheory.Ar.Small.RepAt.mono cc (fun _ => 1), ⟨⟨_, hform⟩, fun hm => ?_⟩, fun w hw hf x hso => ?_⟩
  · have h := GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.aeval_scaled RM.y (fun _ => 1) (G * Hf * GlobalTheory.CompanionTheory.Ar.Small.RepAt.mono cc (fun _ => 1))
    have h0 : mConeMap RM.y (G * Hf * GlobalTheory.CompanionTheory.Ar.Small.RepAt.mono cc (fun _ => 1)) = 0 := hm
    rw [h0, map_zero] at h
    simp only [mul_one] at h
    rw [map_mul, map_mul, GlobalTheory.CompanionTheory.Ar.Small.RepAt.aeval_mono] at h
    exact mul_ne_zero (mul_ne_zero hGy0 hHy) (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)) h
  obtain ⟨cs, hcs, he⟩ := hso
  have hw' : Or.Re.R.lift x x ∈ mcPts (mCoordIdeal RM.y) := Or.Re.R.mem x x (Or.Re.R.mem_U x)
  have hf' : MvPolynomial.aeval (Or.Re.R.lift x x) (G * Hf * GlobalTheory.CompanionTheory.Ar.Small.RepAt.mono cc (fun _ => 1)) ≠ 0 := by
    have h := GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.aeval_scaled_homog w cs hform
    have e2 : Or.Re.R.lift x x = fun p => w p * cs p.1 := by
      rw [he]
      funext p
      exact mul_comm _ _
    rw [e2, h]
    exact mul_ne_zero hf (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hcs k))
  rw [map_mul, map_mul, GlobalTheory.CompanionTheory.Ar.Small.RepAt.aeval_mono] at hf'
  have hGw := left_ne_zero_of_mul (left_ne_zero_of_mul hf')
  have hHw := right_ne_zero_of_mul (left_ne_zero_of_mul hf')
  have hcc : ∀ k, IsUnit (Or.Re.R.lift x x ⟨k, cc k⟩) := fun k => IsUnit.mk0 _ (by
    have := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hf') k (Finset.mem_univ k)
    simpa using this)
  obtain ⟨z, hz, hco⟩ := (mem_mcPts_iff_exists_coordsAt Or.𝔐.X RM.Ω Or.𝔐.ξ RM.K RM.ι RM.y Or.𝔐.tie _).1 hw'
  have hch' := GlobalTheory.CompanionTheory.Ar.Small.RepAt.inChart_of_coords hz hco cc hcc
  have gens : ∀ r, (Or.Fl.rootLat r).IsGenAt ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) • Or.e r) :=
    fun r => ⟨smul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) (Or.lines r).1,
      (Or.lines r).2 _ trivial cc hch'⟩
  have ht := GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.tens_isGenAt (fun r => -Fx.n r) gens
  have hchi : InChart Or.𝔐.ξ (fun i' => Or.g (Fx.yf i')) (Or.ix.symm (cc Or.k₀)) ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ := by
    refine ⟨?_, fun j => ?_⟩
    · show Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) ≠ 0
      rw [ya]
      exact hy _
    · show Or.g (Fx.yf j) / Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) ∈ _
      rw [ya, ← Or.y_eq]
      exact Lat.block_ratio_mem hch' Or.k₀ (Or.ix j)
  have heff := (Or.eff ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ (fun r hr => GlobalTheory.CompanionTheory.Ar.Small.RepAt.not_inFibre hz hr) _ _ hchi ht).2
  have hu := unitAt_of_forms hz hco cc hcc hG hH hHy hGy hGw hHw
  exact (Or.interior x z hco).1 (not_not.1 fun h => heff h hu)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginExistsFormStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_exists_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx), ∃ f : MRing RM.ι, Small.IsFormOff (mCoordIdeal RM.y) f ∧ ∀ w ∈ mcPts (mCoordIdeal RM.y), MvPolynomial.aeval w f ≠ 0 → ∀ x : Or.Re.R.X, SameOrbit (Or.Re.R.lift x x) w → Or.Re.π x ∈ Sys.open' := by
  first | exact @GlobalTheory.CompanionTheory.RootForm.exists_form | exact GlobalTheory.CompanionTheory.RootForm.exists_form | (intros; apply GlobalTheory.CompanionTheory.RootForm.exists_form <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscOrbitBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscOrbitBound
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
namespace GlobalTheory.CompanionTheory.Ar.Plug.Disc

open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.FinHolAtlas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem orbit_symm {u w : (Σ k, ι k) → ℂ} (h : SameOrbit u w) : SameOrbit w u := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]

theorem orbit_trans {u v w : (Σ k, ι k) → ℂ} (h : SameOrbit u v) (h' : SameOrbit v w) :
    SameOrbit u w := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := h'
  exact ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), by funext p; simp [mul_assoc]⟩

theorem orbit_cross {u w : (Σ k, ι k) → ℂ} (h : SameOrbit u w) (k : K) (a b : ι k) :
    u ⟨k, a⟩ * w ⟨k, b⟩ = u ⟨k, b⟩ * w ⟨k, a⟩ := by
  obtain ⟨c, hc, rfl⟩ := h
  simp only []
  ring

theorem orbit_of_cross {u w : (Σ k, ι k) → ℂ} (hu : ∀ k, ∃ i, u ⟨k, i⟩ ≠ 0)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0)
    (h : ∀ k (a b : ι k), u ⟨k, a⟩ * w ⟨k, b⟩ = u ⟨k, b⟩ * w ⟨k, a⟩) : SameOrbit u w := by
  choose l hl using hw
  refine ⟨fun k => u ⟨k, l k⟩ / w ⟨k, l k⟩, fun k => ?_, ?_⟩
  · refine div_ne_zero (fun h0 => ?_) (hl k)
    obtain ⟨i, hi⟩ := hu k
    have := h k i (l k)
    rw [h0, zero_mul] at this
    exact (mul_ne_zero hi (hl k)) this
  · funext ⟨k, a⟩
    have := h k a (l k)
    simp only []
    field_simp [hl k]
    linear_combination this

theorem affCoord_orbit {u w : (Σ k, ι k) → ℂ} (h : SameOrbit u w) (p : (k : K) → ι k) :
    affCoord p u = affCoord p w := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  simp only [affCoord]
  exact mul_div_mul_left _ _ (hc q.1)

section Atlas

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem continuousAt_of_chart {F : Type} [TopologicalSpace F] (A : FinHolAtlas e X) {g : X → F}
    {x : X} (j : Fin A.n) (hj : x ∈ (A.chart j).source)
    (h : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j x)) : ContinuousAt g x := by
  have h1 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
    ContinuousAt.comp h ((A.chart j).continuousAt hj)
  refine h1.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem chart_mem (A : FinHolAtlas e X) {U : Set X} {x : X} (hx : x ∈ U) (j : Fin A.n)
    (hj : x ∈ (A.chart j).source) :
    A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
  ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩

theorem analyticAt_comp {e' : ℕ} {Y : Type} [TopologicalSpace Y] {B : FinHolAtlas e' Y}
    {A : FinHolAtlas e X} {h : Y → X} (hh : HoloMap B A h) {V : Set X} {G : X → ℂ}
    (hG : A.HoloOn V G) {y₀ : Y} (hy : h y₀ ∈ V) (j : Fin B.n)
    (hj : y₀ ∈ (B.chart j).source) :
    AnalyticAt ℂ (G ∘ h ∘ (B.chart j).symm) (B.chart j y₀) := by
  obtain ⟨k, hk⟩ := A.cover (h y₀)
  have hv := (B.chart j).map_source hj
  have hl := (B.chart j).left_inv hj
  have h1 : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart j).symm) (B.chart j y₀) :=
    hh.2 j k _ ⟨hv, by simpa [hl] using hk⟩
  have h2 : AnalyticAt ℂ (G ∘ (A.chart k).symm) (A.chart k (h y₀)) :=
    hG k _ (chart_mem A hy k hk)
  have h2' : AnalyticAt ℂ (G ∘ (A.chart k).symm)
      ((A.chart k ∘ h ∘ (B.chart j).symm) (B.chart j y₀)) := by
    simpa [hl] using h2
  have h3 := h2'.comp h1
  refine h3.congr ?_
  have hc : ContinuousAt (h ∘ (B.chart j).symm) (B.chart j y₀) :=
    hh.1.continuousAt.comp ((B.chart j).continuousAt_symm hv)
  have hs : (A.chart k).source ∈ 𝓝 ((h ∘ (B.chart j).symm) (B.chart j y₀)) := by
    simpa [hl] using (A.chart k).open_source.mem_nhds hk
  filter_upwards [hc.tendsto hs] with v hv'
  exact congrArg G ((A.chart k).left_inv hv')

end Atlas

variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem lift_continuousAt (R : AnLogRes P J e) (x : R.X) {y : R.X} (hy : y ∈ R.U x) :
    ContinuousAt (R.lift x) y := by
  obtain ⟨j, hj⟩ := R.A.cover y
  refine continuousAt_pi.2 fun p => ?_
  refine continuousAt_of_chart R.A j hj ?_
  exact (R.holo x p j _ (chart_mem R.A hy j hj)).continuousAt

theorem tendsto_center (R : AnLogRes P J e) (hJ : ∀ z, z ∉ mcPts J)
    {Zf : ℂ → (Σ k, ι k) → ℂ} (hZ : ContinuousAt Zf 0) (hZ0 : ∀ k, ∃ i, Zf 0 ⟨k, i⟩ ≠ 0)
    {x : ℂ → R.X} (hx : ∀ᶠ z in 𝓝 (0 : ℂ), SameOrbit (R.lift (x z) (x z)) (Zf z))
    {x₀ : R.X} (h0 : SameOrbit (R.lift x₀ x₀) (Zf 0)) : Tendsto x (𝓝 0) (𝓝 x₀) := by
  rw [tendsto_iff_ultrafilter]
  intro F hF
  have hxs : Tendsto x F (𝓝 (F.map x).lim) := (F.map x).le_nhds_lim
  set xs := (F.map x).lim with hxsdef
  have hU : ∀ᶠ z in (F : Filter ℂ), x z ∈ R.U xs :=
    hxs.eventually ((R.isOpen_U xs).mem_nhds (R.mem_U xs))
  have hl : Tendsto (fun z => R.lift xs (x z)) F (𝓝 (R.lift xs xs)) :=
    (lift_continuousAt R xs (R.mem_U xs)).tendsto.comp hxs
  have hZF : Tendsto Zf F (𝓝 (Zf 0)) := hZ.tendsto.mono_left hF
  have horb : ∀ᶠ z in (F : Filter ℂ), SameOrbit (R.lift xs (x z)) (Zf z) := by
    filter_upwards [hU, hF hx] with z h1 h2
    exact orbit_trans (R.compat xs (x z) (x z) ⟨h1, R.mem_U _⟩) h2
  have hcross : ∀ k (a b : ι k), R.lift xs xs ⟨k, a⟩ * Zf 0 ⟨k, b⟩ =
      R.lift xs xs ⟨k, b⟩ * Zf 0 ⟨k, a⟩ := by
    intro k a b
    have t1 : Tendsto (fun z => R.lift xs (x z) ⟨k, a⟩ * Zf z ⟨k, b⟩) F
        (𝓝 (R.lift xs xs ⟨k, a⟩ * Zf 0 ⟨k, b⟩)) :=
      ((tendsto_pi_nhds.1 hl) _).mul ((tendsto_pi_nhds.1 hZF) _)
    have t2 : Tendsto (fun z => R.lift xs (x z) ⟨k, b⟩ * Zf z ⟨k, a⟩) F
        (𝓝 (R.lift xs xs ⟨k, b⟩ * Zf 0 ⟨k, a⟩)) :=
      ((tendsto_pi_nhds.1 hl) _).mul ((tendsto_pi_nhds.1 hZF) _)
    refine tendsto_nhds_unique_of_eventuallyEq t1 t2 ?_
    filter_upwards [horb] with z hz
    exact orbit_cross hz k a b
  have hfin : SameOrbit (R.lift xs xs) (Zf 0) :=
    orbit_of_cross (R.mem xs xs (R.mem_U xs)).1 hZ0 hcross
  have : xs = x₀ := R.inj xs x₀ (hJ _) (orbit_trans hfin (orbit_symm h0))
  rw [← this]
  exact hxs

theorem chart_differentiable (R : AnLogRes P J e) (hJ : ∀ z, z ∉ mcPts J)
    {Zf : ℂ → (Σ k, ι k) → ℂ}
    (hZ : ∀ q, ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun w => Zf w q) z)
    {x : ℂ → R.X} {x₀ : R.X} (hx : ∀ᶠ z in 𝓝 (0 : ℂ), SameOrbit (R.lift (x z) (x z)) (Zf z))
    (h0 : SameOrbit (R.lift x₀ x₀) (Zf 0)) (ht : Tendsto x (𝓝 0) (𝓝 x₀)) (j : Fin R.A.n)
    (hj : x₀ ∈ (R.A.chart j).source) :
    ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun w => R.A.chart j (x w)) z := by
  classical
  choose p hp using (R.mem x₀ x₀ (R.mem_U x₀)).1
  have hv₀ := chart_mem R.A (R.mem_U x₀) j hj
  have hl := (R.A.chart j).left_inv hj
  let a : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun v => affCoord p (R.lift x₀ ((R.A.chart j).symm v))
  have hcoord : ∀ q, AnalyticAt ℂ (fun v => R.lift x₀ ((R.A.chart j).symm v) q) (R.A.chart j x₀) :=
    fun q => R.holo x₀ q j _ hv₀
  have hden : ∀ k, R.lift x₀ ((R.A.chart j).symm (R.A.chart j x₀)) ⟨k, p k⟩ ≠ 0 := by
    intro k
    rw [hl]
    exact hp k
  have ha : AnalyticAt ℂ a (R.A.chart j x₀) := by
    refine analyticAt_pi_iff.2 fun q => ?_
    exact (hcoord q).div (hcoord _) (hden q.1)
  have hker : ((fderiv ℂ a (R.A.chart j x₀) : (Fin e → ℂ) →L[ℂ] ((Σ k, ι k) → ℂ)) :
      (Fin e → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ)).ker = ⊥ :=
    R.immersion x₀ (hJ _) p hp j hj
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  let ρc : ((Σ k, ι k) → ℂ) →L[ℂ] (Fin e → ℂ) := LinearMap.toContinuousLinearMap ρ
  let b : (Fin e → ℂ) → (Fin e → ℂ) := fun v => ρc (a v)
  have hb : ContDiffAt ℂ 1 b (R.A.chart j x₀) :=
    ρc.contDiff.contDiffAt.comp _ ha.contDiffAt
  have hb' : HasFDerivAt b
      ((ContinuousLinearEquiv.refl ℂ (Fin e → ℂ) : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ)) :
        (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) (R.A.chart j x₀) := by
    have h1 := ρc.hasFDerivAt.comp (R.A.chart j x₀) ha.differentiableAt.hasFDerivAt
    refine HasFDerivAt.congr_fderiv h1 (ContinuousLinearMap.ext fun v => ?_)
    exact LinearMap.congr_fun hρ v
  have hn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  let Inv := hb.localInverse hb' hn
  have hInv : ContDiffAt ℂ 1 Inv (b (R.A.chart j x₀)) := hb.to_localInverse hb' hn
  have hleft : ∀ᶠ v in 𝓝 (R.A.chart j x₀), Inv (b v) = v :=
    (hb.hasStrictFDerivAt' hb' hn).eventually_left_inverse
  let c : ℂ → Fin e → ℂ := fun z => ρc (affCoord p (Zf z))
  have hZp : ∀ k, Zf 0 ⟨k, p k⟩ ≠ 0 := by
    obtain ⟨d, -, hd⟩ := h0
    intro k h
    exact hp k (by rw [hd]; simp [h])
  have hall : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ q, DifferentiableAt ℂ (fun w => Zf w q) z :=
    eventually_all.2 hZ
  have hDen : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ k, Zf z ⟨k, p k⟩ ≠ 0 := by
    refine eventually_all.2 fun k => ?_
    exact (hZ ⟨k, p k⟩).self_of_nhds.continuousAt.eventually_ne (hZp k)
  have hcd : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ c z := by
    filter_upwards [hall, hDen] with z h1 h2
    refine ρc.differentiableAt.comp z (differentiableAt_pi.2 fun q => ?_)
    exact (h1 q).div (h1 _) (h2 q.1)
  have hc0 : c 0 = b (R.A.chart j x₀) := by
    show ρc (affCoord p (Zf 0)) = ρc (affCoord p (R.lift x₀ ((R.A.chart j).symm (R.A.chart j x₀))))
    rw [hl, affCoord_orbit h0]
  have hcc : ContinuousAt c 0 := hcd.self_of_nhds.continuousAt
  have hInvd : ∀ᶠ y in 𝓝 (c 0), DifferentiableAt ℂ Inv y := by
    rw [hc0]
    exact (hInv.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hdiff : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun w => Inv (c w)) z := by
    filter_upwards [hcc.tendsto.eventually hInvd, hcd] with z h1 h2
    exact h1.comp z h2
  have hchart : Tendsto (fun z => R.A.chart j (x z)) (𝓝 0) (𝓝 (R.A.chart j x₀)) :=
    ((R.A.chart j).continuousAt hj).tendsto.comp ht
  have heq : ∀ᶠ z in 𝓝 (0 : ℂ), R.A.chart j (x z) = Inv (c z) := by
    filter_upwards [hchart.eventually hleft, ht.eventually ((R.A.chart j).open_source.mem_nhds hj),
      ht.eventually ((R.isOpen_U x₀).mem_nhds (R.mem_U x₀)), hx] with z h1 h2 h3 h4
    have hbz : b (R.A.chart j (x z)) = c z := by
      show ρc (affCoord p (R.lift x₀ ((R.A.chart j).symm (R.A.chart j (x z))))) =
        ρc (affCoord p (Zf z))
      rw [(R.A.chart j).left_inv h2,
        affCoord_orbit (orbit_trans (R.compat x₀ (x z) (x z) ⟨h3, R.mem_U _⟩) h4)]
    rw [← hbz, h1]
  filter_upwards [hdiff, heq.eventually_nhds] with z h1 h2
  exact h1.congr_of_eventuallyEq h2

theorem exists_lower_bound {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0)
    (hne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), g z ≠ 0) :
    ∃ (c : ℝ) (m : ℕ), 0 < c ∧ ∀ᶠ z in 𝓝 (0 : ℂ), c * ‖z‖ ^ m ≤ ‖g z‖ := by
  have hnot : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), g z = 0 := by
    intro h
    have h1 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = 0 := h.filter_mono nhdsWithin_le_nhds
    obtain ⟨z, hz1, hz2⟩ := (hne.and h1).exists
    exact hz1 hz2
  obtain ⟨m, f, hf, hf0, hgf⟩ := hg.exists_eventuallyEq_pow_smul_nonzero_iff.2 hnot
  refine ⟨‖f 0‖ / 2, m, by positivity, ?_⟩
  have hlt : ∀ᶠ z in 𝓝 (0 : ℂ), ‖f 0‖ / 2 < ‖f z‖ :=
    hf.continuousAt.norm.eventually (lt_mem_nhds (by
      have : 0 < ‖f 0‖ := norm_pos_iff.2 hf0
      linarith))
  filter_upwards [hgf, hlt] with z h1 h2
  rw [h1, norm_smul, norm_pow, sub_zero, mul_comm]
  exact mul_le_mul_of_nonneg_left h2.le (by positivity)

end GlobalTheory.CompanionTheory.Ar.Plug.Disc

namespace GlobalTheory.CompanionTheory.Ar.Plug

open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.FinHolAtlas GlobalTheory.CompanionTheory.Ar.Plug.Disc

theorem rW_le_log_disc : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : PB.AnSys D σ) (P : Ideal (MRing ι)) (Re : PB.Realis S P), Re.J = ⊤ → ∀ Zf : ℂ → (Σ k, ι k) → ℂ, (∀ p, DifferentiableOn ℂ (fun z => Zf z p) (Metric.ball 0 1)) → (∀ z ∈ Metric.ball (0 : ℂ) 1, Zf z ∈ mcPts P) → (∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ∀ x : Re.R.X, SameOrbit (Re.R.lift x x) (Zf z) → Re.π x ∈ S.open') → ∃ C ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → ∀ x : Re.R.X, SameOrbit (Re.R.lift x x) (Zf z) → ReciprocityTheory.AnForm.P.rW S.L S.s (Re.π x) ≤ C * (1 + |Real.log ‖z‖|) := by
  intro K _ ι _ D σ S P Re hJ Zf hZ hmem hopen
  have hJ' : ∀ z, z ∉ mcPts Re.J := by
    intro z hz
    have := hz.2 1 (by rw [hJ]; trivial)
    simp at this
  have h0b : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  obtain ⟨x₀, h0⟩ := Re.R.surj (Zf 0) (hmem 0 h0b) (hJ' _)
  have hex : ∀ z, ∃ x : Re.R.X, z ∈ Metric.ball (0 : ℂ) 1 → SameOrbit (Re.R.lift x x) (Zf z) := by
    intro z
    by_cases hz : z ∈ Metric.ball (0 : ℂ) 1
    · obtain ⟨x, hx⟩ := Re.R.surj (Zf z) (hmem z hz) (hJ' _)
      exact ⟨x, fun _ => hx⟩
    · exact ⟨x₀, fun h => absurd h hz⟩
  choose x hxs using hex
  have hball : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ Metric.ball (0 : ℂ) 1 := Metric.ball_mem_nhds _ one_pos
  have hx : ∀ᶠ z in 𝓝 (0 : ℂ), SameOrbit (Re.R.lift (x z) (x z)) (Zf z) := hball.mono hxs
  have hZd : ∀ q, ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun w => Zf w q) z := fun q => by
    filter_upwards [hball] with z hz
    exact (hZ q).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  have hZc : ContinuousAt Zf 0 := continuousAt_pi.2 fun q => (hZd q).self_of_nhds.continuousAt
  have ht : Tendsto x (𝓝 0) (𝓝 x₀) := tendsto_center Re.R hJ' hZc (hmem 0 h0b).1 hx h0
  obtain ⟨j, hj⟩ := Re.R.A.cover x₀
  have hv := chart_differentiable Re.R hJ' hZd hx h0 ht j hj
  have hH : AnalyticAt ℂ (S.s (Re.π x₀) ∘ Re.π ∘ (Re.R.A.chart j).symm) (Re.R.A.chart j x₀) :=
    analyticAt_comp Re.holo (S.sec.1 (Re.π x₀)) (S.L.mem_U _) j hj
  have hvt : Tendsto (fun z => Re.R.A.chart j (x z)) (𝓝 0) (𝓝 (Re.R.A.chart j x₀)) :=
    ((Re.R.A.chart j).continuousAt hj).tendsto.comp ht
  have hsrc : ∀ᶠ z in 𝓝 (0 : ℂ), x z ∈ (Re.R.A.chart j).source :=
    ht.eventually ((Re.R.A.chart j).open_source.mem_nhds hj)
  have hg : AnalyticAt ℂ (fun z => S.s (Re.π x₀) (Re.π (x z))) 0 := by
    refine Complex.analyticAt_iff_eventually_differentiableAt.2 ?_
    filter_upwards [hv, hvt.eventually hH.eventually_analyticAt, hsrc.eventually_nhds] with z h1 h2 h3
    have h4 := (h2.differentiableAt.comp z h1)
    refine h4.congr_of_eventuallyEq ?_
    filter_upwards [h3] with w hw
    simp [(Re.R.A.chart j).left_inv hw]
  have hyt : Tendsto (fun z => Re.π (x z)) (𝓝 0) (𝓝 (Re.π x₀)) :=
    (Re.holo.1.tendsto x₀).comp ht
  have hLU : ∀ᶠ z in 𝓝 (0 : ℂ), Re.π (x z) ∈ S.L.U (Re.π x₀) :=
    hyt.eventually ((S.L.isOpen_U _).mem_nhds (S.L.mem_U _))
  have hkey : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → S.s (Re.π x₀) (Re.π (x z)) ≠ 0 ∧
      logNormSec S.L S.s (Re.π (x z)) = Real.log ‖S.s (Re.π x₀) (Re.π (x z))‖ -
        S.L.φ (Re.π x₀) (Re.π (x z)) := by
    filter_upwards [hball, hLU] with z hz hU hz0
    have hop : S.s (Re.π (x z)) (Re.π (x z)) ≠ 0 := hopen z hz hz0 (x z) (hxs z hz)
    have hsec := S.sec.2 (Re.π x₀) (Re.π (x z)) (Re.π (x z)) ⟨hU, S.L.mem_U _⟩
    have hne : S.s (Re.π x₀) (Re.π (x z)) ≠ 0 := by
      intro h
      rw [h, norm_zero, zero_mul] at hsec
      exact (mul_pos (norm_pos_iff.2 hop) (Real.exp_pos _)).ne hsec
    refine ⟨hne, ?_⟩
    rw [logNormSec, ← hsec, Real.log_mul (norm_ne_zero_iff.2 hne) (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), S.s (Re.π x₀) (Re.π (x z)) ≠ 0 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hkey] with z hz hz0
    exact (hz hz0).1
  obtain ⟨c, m, hc, hlow⟩ := exists_lower_bound hg hne
  have hφ : ContinuousAt (S.L.φ (Re.π x₀)) (Re.π x₀) := by
    obtain ⟨k, hk⟩ := S.A.cover (Re.π x₀)
    refine continuousAt_of_chart S.A k hk ?_
    have h1 := S.potL.1 (Re.π x₀) k
    refine h1.continuousOn.continuousAt ?_
    exact ((S.A.chart k).isOpen_inter_preimage_symm (S.L.isOpen_U _)).mem_nhds
      (chart_mem S.A (S.L.mem_U _) k hk)
  have hbd : ∀ᶠ z in 𝓝 (0 : ℂ), S.L.φ (Re.π x₀) (Re.π (x z)) < S.L.φ (Re.π x₀) (Re.π x₀) + 1 :=
    (hφ.tendsto.comp hyt).eventually_lt_const (lt_add_one _)
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff.1 (hkey.and (hlow.and (hbd.and hball)))
  set A : ℝ := Real.exp 1 + 2 * |Real.log c| + 2 * (|S.L.φ (Re.π x₀) (Re.π x₀)| + 1) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A + 2 * m, min ε 1, lt_min hε one_pos, ?_⟩
  intro z hz0 hzε y hy
  have hz1 : ‖z‖ < 1 := hzε.trans_le (min_le_right _ _)
  have hzb : z ∈ Metric.ball (0 : ℂ) 1 := by simpa using hz1
  have hne0 : z ≠ 0 := norm_pos_iff.1 hz0
  obtain ⟨h1, h2, h3, -⟩ := hall (y := z) (by simpa using hzε.trans_le (min_le_left _ _))
  obtain ⟨h1a, h1b⟩ := h1 hne0
  have hyx : y = x z := Re.R.inj y (x z) (hJ' _) (orbit_trans hy (orbit_symm (hxs z hzb)))
  subst hyx
  rw [ReciprocityTheory.AnForm.P.rW, h1b]
  have hlog : Real.log c + m * Real.log ‖z‖ ≤ Real.log ‖S.s (Re.π x₀) (Re.π (x z))‖ := by
    have := Real.log_le_log (by positivity) h2
    rwa [Real.log_mul hc.ne' (by positivity), Real.log_pow] at this
  have hlz : Real.log ‖z‖ = -|Real.log ‖z‖| := by
    rw [abs_of_nonpos (Real.log_nonpos hz0.le hz1.le), neg_neg]
  have hL : 0 ≤ |Real.log ‖z‖| := abs_nonneg _
  have hc1 := neg_abs_le (Real.log c)
  have hc2 := le_abs_self (S.L.φ (Re.π x₀) (Re.π x₀))
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [hlz] at hlog
  nlinarith [mul_nonneg hA0 hL, mul_nonneg hm hL]

end GlobalTheory.CompanionTheory.Ar.Plug
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscOrbitBoundStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_disc_orbit_bound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : PB.AnSys D σ) (P : Ideal (MRing ι)) (Re : PB.Realis S P), Re.J = ⊤ → ∀ Zf : ℂ → (Σ k, ι k) → ℂ, (∀ p, DifferentiableOn ℂ (fun z => Zf z p) (Metric.ball 0 1)) → (∀ z ∈ Metric.ball (0 : ℂ) 1, Zf z ∈ mcPts P) → (∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ∀ x : Re.R.X, SameOrbit (Re.R.lift x x) (Zf z) → Re.π x ∈ S.open') → ∃ C ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → ∀ x : Re.R.X, SameOrbit (Re.R.lift x x) (Zf z) → ReciprocityTheory.AnForm.P.rW S.L S.s (Re.π x) ≤ C * (1 + |Real.log ‖z‖|) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.rW_le_log_disc | exact GlobalTheory.CompanionTheory.Ar.Plug.rW_le_log_disc | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.rW_le_log_disc <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscRatioGrowth
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrPointAnalyticDisc
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrPointAnalyticDisc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.dvr_point_analytic_disc : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W : X.Opens) (x : Cpt ξ) (N : X.Opens) (f : Ω), LocallyOfFiniteType s → IsCptGen ξ → genPt ξ ∈ W → x.1 ∉ W → x.1 ∈ N → IsDiscreteValuationRing (regAt ξ x) → f ∉ regAt ξ x → ∃ (V : X.Opens) (hV : IsAffineOpen V) (ψ : (Fin 1 → ℂ) → (Γ(X, V) →+* ℂ)) (r : (Fin 1 → ℂ) → ℂ) (C : ℝ), V ≤ N ∧ IsHolPts (ball 0 1) ψ ∧ (∀ z ∈ ball (0 : Fin 1 → ℂ) 1, spMap (ψ z) ≫ hV.fromSpec ≫ s = spMap σ ∧ genPt ξ ⤳ centre (spMap (ψ z) ≫ hV.fromSpec)) ∧ ∀ z ∈ punct 1 1 1, ⊤ ≤ (spMap (ψ z) ≫ hV.fromSpec) ⁻¹ᵁ W ∧ ValAt ξ (spMap (ψ z) ≫ hV.fromSpec) f (r z) ∧ r z ≠ 0 ∧ ‖(r z)⁻¹‖ ≤ C * ‖z 0‖ := by
  first | exact @PositivityTheory.Xgn.exists_holomorphic_disc_avoiding_pole | exact PositivityTheory.Xgn.exists_holomorphic_disc_avoiding_pole
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrPointAnalyticDiscStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_point_analytic_disc : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W : X.Opens) (x : Cpt ξ) (N : X.Opens) (f : Ω), LocallyOfFiniteType s → IsCptGen ξ → genPt ξ ∈ W → x.1 ∉ W → x.1 ∈ N → IsDiscreteValuationRing (regAt ξ x) → f ∉ regAt ξ x → ∃ (V : X.Opens) (hV : IsAffineOpen V) (ψ : (Fin 1 → ℂ) → (Γ(X, V) →+* ℂ)) (r : (Fin 1 → ℂ) → ℂ) (C : ℝ), V ≤ N ∧ IsHolPts (ball 0 1) ψ ∧ (∀ z ∈ ball (0 : Fin 1 → ℂ) 1, spMap (ψ z) ≫ hV.fromSpec ≫ s = spMap σ ∧ genPt ξ ⤳ centre (spMap (ψ z) ≫ hV.fromSpec)) ∧ ∀ z ∈ punct 1 1 1, ⊤ ≤ (spMap (ψ z) ≫ hV.fromSpec) ⁻¹ᵁ W ∧ ValAt ξ (spMap (ψ z) ≫ hV.fromSpec) f (r z) ∧ r z ≠ 0 ∧ ‖(r z)⁻¹‖ ≤ C * ‖z 0‖ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.dvr_point_analytic_disc | exact GlobalTheory.CompanionTheory.Relay.dvr_point_analytic_disc | (intros; apply GlobalTheory.CompanionTheory.Relay.dvr_point_analytic_disc <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscRatioGrowth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc

open GlobalTheory.CompanionTheory.Ar.CptModel

theorem val_mul_eq {R K : Type} [CommRing R] [Field K] {φ₀ : R →+* K} (hξ : IsCptGen (pt φ₀)) (φ : R →+* ℂ)
    {g h : R} (h0 : φ₀ h ≠ 0) {r : ℂ} (hv : ValAt (pt φ₀) (pt φ) (φ₀ g / φ₀ h) r) : r * φ h = φ g := by
  obtain ⟨hsp, s, hs, rfl⟩ := hv
  let c : Cpt (pt φ₀) := ⟨centre (pt φ), hsp⟩
  have e : s * tS c.1 h = tS c.1 g := by
    apply hξ.inj c
    rw [map_mul, genMap_toStalk, genMap_toStalk]
    refine (congrArg (· * φ₀ h) hs).trans ?_
    exact div_mul_cancel₀ _ h0
  have k : ∀ a : R, (Scheme.stalkClosedPointTo (pt φ)).hom (tS c.1 a) = φ a := fun a => by
    have := genMap_toStalk φ (self (pt φ)) a
    rw [genMap_self] at this
    exact this
  rw [← k h, ← k g, ← e]
  exact (map_mul _ _ _).symm

theorem ne_zero_of_top_le {R K : Type} [CommRing R] [Field K] (φ : R →+* K) (f : R)
    (hW : ⊤ ≤ (pt φ) ⁻¹ᵁ (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens)) : φ f ≠ 0 := by
  have h1 : genPt (pt φ) ∈ (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens) :=
    hW (show IsLocalRing.closedPoint K ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) from trivial)
  have h2 : f ∉ (genPt (pt φ)).asIdeal := h1
  rw [genPt_asIdeal] at h2
  exact h2

theorem isDVR_regAt {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K]
    {φ : R →+* K} (hξ : IsCptGen (pt φ)) (x : Cpt (pt φ)) (h1 : x.1.asIdeal.height = 1) :
    IsDiscreteValuationRing (regAt (pt φ) x) := by
  haveI : (x.1 : PrimeSpectrum R).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have hd := GlobalTheory.T.isDiscreteValuationRing_localization_of_height_eq_one' R x.1.asIdeal h1
  have key : ∀ (q : PrimeSpectrum R), Nonempty (Localization.AtPrime q.asIdeal ≃+* (Spec.structureSheaf R).presheaf.stalk q) :=
    fun q => ⟨(IsLocalization.algEquiv q.asIdeal.primeCompl _ _).toRingEquiv⟩
  obtain ⟨e⟩ := key x.1
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (e.trans (CPoint.regAtEquivStalk hξ x))

end GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc

namespace GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc

open GlobalTheory.CompanionTheory.Ar.CptModel

theorem exists_pole_prime {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] (t : K) (ht : ∀ a : R, algebraMap R K a ≠ t) :
    ∃ p : Ideal R, p.IsPrime ∧ p.height = 1 ∧ ∀ a c : R, c ∉ p → t * algebraMap R K c ≠ algebraMap R K a := by
  by_contra hcon
  push Not at hcon
  let e : FractionRing R ≃ₐ[R] K := FractionRing.algEquiv R K
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_eq_algebraMap_of_integral_at_height_one_primes R (e.symm t) fun q hq h1 => by
    obtain ⟨a, c, hc, hac⟩ := hcon q hq h1
    refine ⟨a, c, hc, e.injective ?_⟩
    rw [map_mul, e.apply_symm_apply, e.commutes, e.commutes]
    exact hac
  have h2 : e (algebraMap R (FractionRing R) a) = t := by rw [ha, e.apply_symm_apply]
  rw [e.commutes] at h2
  exact ht a h2

theorem exists_cpt {R K : Type} [CommRing R] [Field K] (φ : R →+* K) (hφ : Function.Injective φ) (p : Ideal R)
    (hp : p.IsPrime) : ∃ x : Cpt (pt φ), x.1.asIdeal = p := by
  have hsp : genPt (pt φ) ⤳ ((⟨p, hp⟩ : PrimeSpectrum R) : Spec (CommRingCat.of R)) := by
    refine (PrimeSpectrum.le_iff_specializes (genPt (pt φ) : PrimeSpectrum R) ⟨p, hp⟩).1 ?_
    show (genPt (pt φ)).asIdeal ≤ p
    rw [genPt_asIdeal, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact ⟨⟨_, hsp⟩, rfl⟩

theorem exists_ringHom {R S : Type} [CommRing R] [CommRing S]
    (f : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) : ∃ c : R →+* S, spMap c = f :=
  ⟨(Spec.preimage f).hom, Spec.map_preimage f⟩

theorem exists_disc {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K]
    [Algebra ℚ R] [Algebra.FiniteType ℚ R] [Algebra R K] [IsFractionRing R K] (f : R) (hf : algebraMap R K f ≠ 0)
    (t : K) (x : Cpt (pt (algebraMap R K))) (hxf : f ∈ x.1.asIdeal) (hx1 : x.1.asIdeal.height = 1)
    (hxt : t ∉ regAt (pt (algebraMap R K)) x) :
    ∃ (φ : (Fin 1 → ℂ) → (R →+* ℂ)) (r : (Fin 1 → ℂ) → ℂ) (C : ℝ), IsHolPts (Metric.ball 0 1) φ ∧
      ∀ z ∈ punct 1 1 1, ⊤ ≤ (pt (φ z)) ⁻¹ᵁ (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens) ∧
        ValAt (pt (algebraMap R K)) (pt (φ z)) t (r z) ∧ r z ≠ 0 ∧ ‖(r z)⁻¹‖ ≤ C * ‖z 0‖ := by
  have hξ : IsCptGen (pt (algebraMap R K)) := isCptGen_fractionRing
  have hgW : genPt (pt (algebraMap R K)) ∈
      (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens) := by
    show f ∉ (genPt (pt (algebraMap R K))).asIdeal
    rw [genPt_asIdeal]
    exact hf
  have hxW : x.1 ∉ (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens) := fun hm => (show f ∉ x.1.asIdeal from hm) hxf
  have hlft : LocallyOfFiniteType (spMap (algebraMap ℚ R)) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  obtain ⟨V, hV, ψ, r, C, -, hhol, -, hz⟩ := GlobalTheory.T.dvr_point_analytic_disc ℚ (algebraMap ℚ ℂ) (Spec (CommRingCat.of R))
    (spMap (algebraMap ℚ R)) K (pt (algebraMap R K)) (PrimeSpectrum.basicOpen f) x ⊤ t hlft hξ hgW hxW trivial
    (isDVR_regAt hξ x hx1) hxt
  obtain ⟨c, hc⟩ := exists_ringHom (S := Γ(Spec (CommRingCat.of R), V)) hV.fromSpec
  have hy : ∀ w, spMap (ψ w) ≫ hV.fromSpec = pt ((ψ w).comp c) := fun w => by
    rw [← hc]
    exact (Spec.map_comp _ _).symm
  refine ⟨fun z => (ψ z).comp c, r, C, ⟨hhol.1, fun a => hhol.2 (c a)⟩, fun z hzp => ?_⟩
  have := hz z hzp
  rwa [hy] at this

theorem disc_of_pole {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K]
    [Algebra ℚ R] [Algebra.FiniteType ℚ R] [Algebra R K] [IsFractionRing R K] (g h b : R)
    (hh : algebraMap R K h ≠ 0) (hb : algebraMap R K b ≠ 0)
    (ht : ∀ a : R, algebraMap R K a ≠ algebraMap R K g / algebraMap R K h) :
    ∃ (ψ : ℂ → (R →+* ℂ)) (C : ℝ), (∀ a : R, DifferentiableOn ℂ (fun z => ψ z a) (Metric.ball 0 1)) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ψ z b ≠ 0 ∧ ψ z h ≠ 0 ∧ ‖ψ z h‖ ≤ C * ‖z‖ * ‖ψ z g‖ := by
  have hξ : IsCptGen (pt (algebraMap R K)) := isCptGen_fractionRing
  obtain ⟨p, hp, hp1, hpole⟩ := exists_pole_prime _ ht
  have hhp : h ∈ p := by
    by_contra hn
    exact hpole g h hn (div_mul_cancel₀ _ hh)
  obtain ⟨x, rfl⟩ := exists_cpt (algebraMap R K) (IsFractionRing.injective R K) p hp
  have hnt : algebraMap R K g / algebraMap R K h ∉ regAt (pt (algebraMap R K)) x := by
    intro hm
    obtain ⟨a, c, hc, -, e⟩ := (mem_regAt_iff _ x _).1 hm
    exact hpole a c hc e
  obtain ⟨φ, r, C, hhol, hz⟩ := exists_disc (K := K) (b * h) (by rw [map_mul]; exact mul_ne_zero hb hh) _ x
    (Ideal.mul_mem_left _ b hhp) hp1 hnt
  have hd : ∀ z : ℂ, ‖(fun _ => z : Fin 1 → ℂ)‖ = ‖z‖ := fun z => pi_norm_const z
  refine ⟨fun z => φ fun _ => z, C, fun a => ?_, fun z hz1 hz0 => ?_⟩
  · have h1 : DifferentiableOn ℂ (fun (z : ℂ) (_ : Fin 1) => z) (Metric.ball 0 1) :=
      (differentiable_pi.2 fun _ => differentiable_id).differentiableOn
    refine (hhol.2 a).comp h1 fun z hz1 => ?_
    rw [mem_ball_zero_iff] at hz1 ⊢
    rwa [hd]
  · have hmem : (fun _ => z : Fin 1 → ℂ) ∈ punct 1 1 1 := by
      refine ⟨?_, fun _ _ => hz0⟩
      rw [mem_ball_zero_iff] at hz1 ⊢
      rwa [hd]
    obtain ⟨hW, hval, hr0, hbd⟩ := hz _ hmem
    have hbh := ne_zero_of_top_le _ _ hW
    rw [map_mul] at hbh
    have e := val_mul_eq hξ _ hh hval
    have hz0' := right_ne_zero_of_mul hbh
    refine ⟨left_ne_zero_of_mul hbh, hz0', ?_⟩
    have e2 : φ (fun _ => z) h = (r fun _ => z)⁻¹ * φ (fun _ => z) g := by
      rw [← e]
      field_simp
    show ‖φ (fun _ => z) h‖ ≤ C * ‖z‖ * ‖φ (fun _ => z) g‖
    rw [e2, norm_mul]
    exact mul_le_mul_of_nonneg_right hbd (norm_nonneg _)

theorem pole_disc : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω), A.FG → Algebra.Smooth ℚ A → (∀ x : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ x * b = a) → ∀ g h b : A, (h : Ω) ≠ 0 → (b : Ω) ≠ 0 → (g : Ω) / h ∉ A → ∃ (ψ : ℂ → (A →+* ℂ)) (C : ℝ), (∀ a : A, DifferentiableOn ℂ (fun z => ψ z a) (Metric.ball 0 1)) ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ψ z b ≠ 0 ∧ ψ z h ≠ 0 ∧ ‖ψ z h‖ ≤ C * ‖z‖ * ‖ψ z g‖ := by
  intro Ω _ _ A hFG hSm hfrac g h b hh hb ht
  haveI : Algebra.FiniteType ℚ A := (Subalgebra.fg_iff_finiteType A).1 hFG
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℚ A
  haveI : IsIntegrallyClosed A := GlobalTheory.isIntegrallyClosed_of_smooth ℚ A
  haveI : IsFractionRing A Ω := IsFractionRing.of_field A Ω fun z => by
    obtain ⟨a, ha, c, hc, hc0, e⟩ := hfrac z
    have hc0' : algebraMap A Ω ⟨c, hc⟩ ≠ 0 := hc0
    exact ⟨⟨a, ha⟩, ⟨c, hc⟩, eq_div_of_mul_eq hc0' e⟩
  refine disc_of_pole (K := Ω) g h b hh hb fun a e => ht ?_
  have e' : (a : Ω) = (g : Ω) / h := e
  rw [← e']
  exact a.2

end GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscRatioGrowthStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_disc_ratio_growth : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω), A.FG → Algebra.Smooth ℚ A → (∀ x : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ x * b = a) → ∀ g h b : A, (h : Ω) ≠ 0 → (b : Ω) ≠ 0 → (g : Ω) / h ∉ A → ∃ (ψ : ℂ → (A →+* ℂ)) (C : ℝ), (∀ a : A, DifferentiableOn ℂ (fun z => ψ z a) (Metric.ball 0 1)) ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ψ z b ≠ 0 ∧ ψ z h ≠ 0 ∧ ‖ψ z h‖ ≤ C * ‖z‖ * ‖ψ z g‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc.pole_disc | exact GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc.pole_disc | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc.pole_disc <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormSectionCount
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem cusp_mem_chartLatNm : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : _root_.GlobalTheory.CompanionTheory.Ar.Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw), ∀ f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0), ∃ N : ℕ, 0 < N ∧ (N : (T.M B b).Ω) * (gauge Rd u * Rd.φ (evC h Z f)) ∈ chartLatNm (T.M B b).y (degOf (T.M B b) u) 1 := by
  intro hG E _ _ _ H Dw l Xo c r U h e hL x hx Y _ T o B b Fr Z Rd u f hf
  obtain ⟨R, w, hw, hval⟩ := GlobalTheory.T.comp_laws_model_root_bound hG E H Dw l Xo c r U h e hL x hx _ _ Y _ _ _ _ _ Fr Z Rd u f hf
  obtain ⟨f₀, hf₀, hint⟩ := GlobalTheory.T.root_origin_exists_form E H Dw l Xo c _ _ Y _ _ _ _ (o.toTowerOrigin.Or B b)
  obtain ⟨hJ, inst, hsm⟩ := o.smooth B b
  refine GlobalTheory.T.holomorphic_disc_component_growth GlobalTheory.T.holomorphic_disc_ratio_growth _ _ _ (T.M B b).y (degOf (T.M B b) u) _
    (fun z => R * ∏ r, ((o.toTowerOrigin.Or B b).sing r).h z ^ nOf u (some r)) w f₀ (T.M B b).birational hsm hw hf₀
    hval ?_
  intro Zf hol hmem hne
  have hJ' : (o.toTowerOrigin.Or B b).Re.J = ⊤ := hJ
  obtain ⟨C₁, ρ₁, hρ₁, hb⟩ := GlobalTheory.T.holomorphic_disc_orbit_bound _ _ _ _ _ _ (o.toTowerOrigin.Or B b).Re hJ' Zf hol hmem
    (fun z hz hz0 x' hx' => hint _ (hmem z hz) (hne z hz hz0) x' hx')
  obtain ⟨C₂, M, hC₂, hev⟩ := GlobalTheory.T.root_origin_weight_section E H Dw l Xo c _ _ Y _ _ _ _ (o.toTowerOrigin.Or B b)
    (fun r => nOf u (some r)) (Zf 0) (hmem 0 (by simp))
  have hcont : ContinuousAt Zf 0 := by
    refine continuousAt_pi.2 fun p => ?_
    exact (hol p).continuousOn.continuousAt (Metric.ball_mem_nhds _ one_pos)
  obtain ⟨ρ₂, hρ₂, hball⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually hev)
  refine ⟨|R| * C₂ * C₁ ^ M, min ρ₁ (min ρ₂ 1), M, lt_min hρ₁ (lt_min hρ₂ one_pos), fun z hz0 hz => ?_⟩
  have hz₁ : ‖z‖ < ρ₁ := hz.trans_le (min_le_left _ _)
  have hz₂ : ‖z‖ < ρ₂ := hz.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hz₃ : ‖z‖ < 1 := hz.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hzb : z ∈ Metric.ball (0 : ℂ) 1 := by simpa using hz₃
  have hz00 : z ≠ 0 := norm_pos_iff.1 hz0
  have hnot : Zf z ∉ mcPts (o.toTowerOrigin.Or B b).Re.J := by
    rw [hJ']
    intro hm
    have := hm.2 1 trivial
    simp at this
  obtain ⟨x', hx'⟩ := (o.toTowerOrigin.Or B b).Re.R.surj (Zf z) (hmem z hzb) hnot
  have hop := hint _ (hmem z hzb) (hne z hzb hz00) x' hx'
  have h1 := hball (by simpa using hz₂) (hmem z hzb) x' hx' hop
  have h2 := hb z hz0 hz₁ x' hx'
  have h3 : 0 ≤ ReciprocityTheory.AnForm.P.rW ((o.toTowerOrigin.Sys b).L) ((o.toTowerOrigin.Sys b).s)
      ((o.toTowerOrigin.Or B b).Re.π x') := by
    have := (o.toTowerOrigin.Sys b).norm_le ((o.toTowerOrigin.Or B b).Re.π x')
    have he := Real.exp_pos 1
    unfold ReciprocityTheory.AnForm.P.rW
    linarith
  have hpos : 0 ≤ ∏ r, ((o.toTowerOrigin.Or B b).sing r).h (Zf z) ^ nOf u (some r) :=
    Finset.prod_nonneg fun r _ => (zpow_pos (((o.toTowerOrigin.Or B b).sing r).pos _ (hmem z hzb).1) _).le
  calc R * ∏ r, ((o.toTowerOrigin.Or B b).sing r).h (Zf z) ^ nOf u (some r)
      ≤ |R| * ∏ r, ((o.toTowerOrigin.Or B b).sing r).h (Zf z) ^ nOf u (some r) :=
        mul_le_mul_of_nonneg_right (le_abs_self R) hpos
    _ ≤ |R| * (C₂ * (C₁ * (1 + |Real.log ‖z‖|)) ^ M) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) (abs_nonneg R)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 M) hC₂
    _ = |R| * C₂ * C₁ ^ M * (1 + |Real.log ‖z‖|) ^ M := by rw [mul_pow]; ring

end GlobalTheory.CompanionTheory.Ar.Plug
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormSectionCountStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_norm_section_count : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw), ∀ f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0), ∃ N : ℕ, 0 < N ∧ (N : (T.M B b).Ω) * (gauge Rd u * Rd.φ (evC h Z f)) ∈ chartLatNm (T.M B b).y (degOf (T.M B b) u) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.cusp_mem_chartLatNm | exact GlobalTheory.CompanionTheory.Ar.Plug.cusp_mem_chartLatNm | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.cusp_mem_chartLatNm <;> assumption)
end
