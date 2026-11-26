module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem evR_eq_map_of_test_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hL : EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {g : Rul Xo c} (hg : g ∈ sec Xo c a n) {S : Type} [CommRing S] [Algebra c.F S] (p : TRing c.F)
    (φ : p.R →ₐ[c.F] S) (y : FrPt Xo c p.R) (w : FrPt Xo c S) (hw : FrMap φ y w) :
    evR Xo c g w = φ (g p y) := by
  have h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, φ, y, hw⟩
  unfold evR evalAt
  rw [dite_eq_left h]
  exact hL.wd g hg.1 S _ p _ φ _ y w h.choose_spec.choose_spec.choose_spec hw

theorem sec_eq_zero_of_generic_values :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ sec Xo c a n, (∀ Z, evC h Z g = 0) → g = 0 := by
  intro E _ _ _ H Dw l Xo c hL h hA a n g hg h0
  have hfield : ∀ (L : Type) [Field L] [Algebra c.F L] (w : FrPt Xo c L), evR Xo c g w = 0 := by
    intro L _ _ w
    obtain ⟨C, ψ, z, t', hz, hb⟩ := hA L w
    letI : Algebra c.F C.R := C.R.algebra
    obtain ⟨q, χ, y₀, hy₀⟩ := hL.test C.R C.y
    have h1 : evR Xo c g C.yg = 0 := by
      rw [hL.wt a n g hg _ C.t _ _ (hL.test _ _) (hL.test _ _) C.bor]
      have := h0 C.Z
      unfold evC at this
      rw [this, mul_zero]
    have h2 : χ (g q y₀) = 0 := by
      rw [evR_eq_map_of_test_point hL hg q (C.R.val.comp χ) y₀ C.yg
        (frMap_trans _ _ _ _ _ _ _ _ hy₀ C.gen)] at h1
      exact Subtype.ext h1
    have h3 : evR Xo c g z = 0 := by
      rw [evR_eq_map_of_test_point hL hg q (ψ.comp χ) y₀ z (frMap_trans _ _ _ _ _ _ _ _ hy₀ hz), AlgHom.comp_apply,
        h2, map_zero]
    rw [hL.wt a n g hg _ t' _ _ (hL.test _ _) (hL.test _ _) hb, h3, mul_zero]
  funext p y
  have hred : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  show g p y = 0
  refine IsNilpotent.eq_zero ?_
  rw [nilpotent_iff_mem_prime]
  intro P hP
  let φ : p.R →ₐ[c.F] P.ResidueField := IsScalarTower.toAlgHom c.F p.R P.ResidueField
  obtain ⟨w, hw⟩ := hL.bc _ _ φ y
  have h4 := hfield _ w
  rw [evR_eq_map_of_test_point hL hg p φ y w hw] at h4
  exact Ideal.algebraMap_residueField_eq_zero.1 h4

end GlobalTheory.Reg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValuesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_eq_zero_of_genericFramedPoint_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ sec Xo c a n, (∀ Z, evC h Z g = 0) → g = 0 := by
  first | exact @GlobalTheory.Reg.sec_eq_zero_of_generic_values | exact GlobalTheory.Reg.sec_eq_zero_of_generic_values | (intros; apply GlobalTheory.Reg.sec_eq_zero_of_generic_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NaturalRuleValueBaseChangeOfIsReduced
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NaturalRuleValueBaseChangeOfIsReduced
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem GlobalTheory.Reg.evR_baseChange_of_isReduced :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → ∀ (S T : Type) [CommRing S] [IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → evR Xo c f z = φ (evR Xo c f y) := by
  intro E _ _ _ H Dw l Xo c hL a n f hf S T _ _ _ _ _ φ y z hm
  have hT1 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y := hL.test S y
  have hT2 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := by
    obtain ⟨p, ψ, y', hy'⟩ := hT1
    exact ⟨p, φ.comp ψ, y', frMap_trans (Xo := Xo) (c := c) _ _ _ ψ φ y' y z hy' hm⟩
  unfold evR evalAt
  rw [dite_eq_left hT2, dite_eq_left hT1]
  exact hL.wd f hf.1 T _ _ _ _ _ _ z hT2.choose_spec.choose_spec.choose_spec
    (frMap_trans (Xo := Xo) (c := c) _ _ _ _ φ _ y z hT1.choose_spec.choose_spec.choose_spec hm)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NaturalRuleValueBaseChangeOfIsReducedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.naturalRule_value_baseChange_of_isReduced : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → ∀ (S T : Type) [CommRing S] [IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → evR Xo c f z = φ (evR Xo c f y) := by
  first | exact @GlobalTheory.Reg.evR_baseChange_of_isReduced | exact GlobalTheory.Reg.evR_baseChange_of_isReduced | (intros; apply GlobalTheory.Reg.evR_baseChange_of_isReduced <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsValuationSubringComapEqNonunits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_valuationSubring_comap_eq_nonunits {K L : Type} [Field K] [Field L] (f : K →+* L)
    (U : ValuationSubring K) :
    ∃ W : ValuationSubring L, W.comap f = U ∧ ∀ x ∈ U.nonunits, f x ∈ W.nonunits := by
  classical
  obtain ⟨W, hW, hloc⟩ := IsLocalRing.exists_factor_valuationRing (f.comp U.subtype)
  refine ⟨W, ?_, ?_⟩
  · ext x
    rw [ValuationSubring.mem_comap]
    constructor
    · intro hx
      by_contra hxU
      have hx0 : x ≠ 0 := fun h => hxU (h ▸ U.zero_mem)
      have hinv : x⁻¹ ∈ U := (U.mem_or_inv_mem x).resolve_left hxU
      have hnu : ¬ IsUnit (⟨x⁻¹, hinv⟩ : U) := by
        intro hu
        obtain ⟨⟨y, hy⟩, hyx⟩ := isUnit_iff_exists_inv.mp hu
        have hyx' : x⁻¹ * y = 1 := congrArg Subtype.val hyx
        have : y = x := by
          calc y = x * (x⁻¹ * y) := by rw [← _root_.mul_assoc, mul_inv_cancel₀ hx0, _root_.one_mul]
            _ = x := by rw [hyx', _root_.mul_one]
        exact hxU (this ▸ hy)
      apply hnu
      apply (hloc.map_nonunit (⟨x⁻¹, hinv⟩ : U))
      refine isUnit_iff_exists_inv.mpr ⟨⟨f x, hx⟩, ?_⟩
      apply Subtype.ext
      change f x⁻¹ * f x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    · intro hx
      exact hW ⟨x, hx⟩
  · intro x hx
    obtain ⟨hxU, hmax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp hx
    have hfx : f x ∈ W := hW ⟨x, hxU⟩
    have key : (⟨f x, hfx⟩ : W) ∈ IsLocalRing.maximalIdeal W := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply (IsLocalRing.mem_maximalIdeal _).mp hmax
      exact hloc.map_nonunit (⟨x, hxU⟩ : U) hu
    exact (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mpr ⟨hfx, key⟩

theorem exists_prime_natCast_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ la.asIdeal := by
  classical
  have hbot : la.asIdeal ≠ ⊥ := la.ne_bot
  have hprime : la.asIdeal.IsPrime := la.isPrime
  have main : ∀ n : ℕ, (n : 𝓞 K) ∈ la.asIdeal → n ≠ 0 → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ la.asIdeal := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn hn0
      have hn1 : n ≠ 1 := by
        rintro rfl
        exact hprime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using hn))
      obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd hn1
      rw [Nat.cast_mul] at hn
      rcases hprime.mem_or_mem hn with h | h
      · exact ⟨p, hp, h⟩
      · have hm0 : m ≠ 0 := by rintro rfl; simp at hn0
        refine ih m ?_ h hm0
        calc m = 1 * m := (_root_.one_mul m).symm
          _ < p * m := Nat.mul_lt_mul_of_pos_right hp.one_lt (Nat.pos_of_ne_zero hm0)
  exact main _ (Ideal.absNorm_mem la.asIdeal) (by rwa [Ne, Ideal.absNorm_eq_zero_iff])

theorem modelAt_of_good_level : PartI → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (Xo : ∀ l : Level H, Moduli Dw l) (l : Level H) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)), (∀ p : ℕ, p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p) → ModelAt (Xo l) c la := by
  intro hI E _ _ _ H Dw hpq Xo l c la hgood
  obtain ⟨-, hI⟩ := hI
  obtain ⟨Y, hY, -⟩ := hI E H Dw hpq Xo
  unfold ModelAt
  obtain ⟨p, hp, hpla⟩ := exists_prime_natCast_mem la
  obtain ⟨W, hcomap, hnon⟩ :=
    exists_valuationSubring_comap_eq_nonunits c.F.val.toRingHom (la.valuation c.F).valuationSubring
  have hlt : la.valuation c.F (p : c.F) < 1 := by
    have h := (la.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).mpr hpla
    exact_mod_cast h
  have hp0 : (p : c.F) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro hinv
    rw [Valuation.mem_valuationSubring_iff, map_inv₀] at hinv
    have hpos : 0 < la.valuation c.F (p : c.F) :=
      zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hp0)
    exact absurd ((inv_le_one₀ hpos).mp hinv) (not_le.mpr hlt)
  have hW : (p : ℂ) ∈ W.nonunits := by
    have h := hnon _ hpU
    rwa [map_natCast] at h
  let i : Idx H p := ⟨l, c, hgood p hp hpla⟩
  rw [← hcomap]
  exact ⟨Y p W hp hW i, ((hY p W hp hW).1.1 i).2.2.1⟩

end GlobalTheory.Reg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IdemMulMemCusp
noncomputable section

namespace GlobalTheory.Reg.IdemCusp

section Model

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsIdemFn (X : Data E r) (χ : Frame X.Ψ r → ℂ) : Prop :=
  (∀ x ∈ X.dom, χ x = 0 ∨ χ x = 1) ∧ DifferentiableOn ℂ χ X.dom ∧
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, χ (rmul x b) = χ x) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, χ (lact γ x) = χ x

theorem flow_const (X : Data E r) {χ : Frame X.Ψ r → ℂ} (hχ : IsIdemFn X χ)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℝ) :
    χ (X.flow ξ (fun τ => (s τ : ℂ)) x) = χ x := by
  have hpath : Continuous fun t : ℝ => CuspCoefficientFlow.flowL X ξ (fun τ => t * s τ) x :=
    ((CuspCoefficientFlow.cont_flowL X ξ).comp
      (continuous_pi fun τ => continuous_id.mul continuous_const)).clm_apply continuous_const
  have hin : ∀ t : ℝ, CuspCoefficientFlow.flowL X ξ (fun τ => t * s τ) x ∈ X.dom := fun t => by
    rw [CuspCoefficientFlow.flowL_apply]
    exact (FlowCoefficientBounds.flow_real X hξ hx (fun τ => t * s τ) 0).1
  set g : ℝ → ℂ := fun t => χ (CuspCoefficientFlow.flowL X ξ (fun τ => t * s τ) x) with hg
  have hcont : Continuous g := hχ.2.1.continuousOn.comp_continuous hpath hin
  have hzo : ∀ t : ℝ, g t = 0 ∨ g t = 1 := fun t => hχ.1 _ (hin t)

  have hre : Continuous fun t => (g t).re := Complex.continuous_re.comp hcont
  have hsame : g 1 = g 0 := by
    by_contra hne
    have hhalf : (1 / 2 : ℝ) ∈ Set.uIcc (g 0).re (g 1).re := by
      rcases hzo 0 with h0 | h0 <;> rcases hzo 1 with h1 | h1 <;>
        simp_all <;> norm_num
    obtain ⟨t, -, ht⟩ := intermediate_value_uIcc hre.continuousOn hhalf
    rcases hzo t with h | h <;> simp [h] at ht
  have h1 : g 1 = χ (X.flow ξ (fun τ => (s τ : ℂ)) x) := by
    simp only [hg, CuspCoefficientFlow.flowL_apply, one_mul]
  have h0 : g 0 = χ x := by
    simp only [hg, CuspCoefficientFlow.flowL_apply, zero_mul, Complex.ofReal_zero]
    exact congrArg χ (EmbeddingHermitianPairs.flow_zero X ξ x)
  rw [← h1, hsame, h0]

theorem fj_mul (X : Data E r) {χ : Frame X.Ψ r → ℂ} (hχ : IsIdemFn X χ) (la : Wt X.Ψ r)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.fj la ξ 0 (χ * P) x = χ x * X.fj la ξ 0 P x := by
  unfold Data.fj
  split_ifs
  · simp only [Pi.mul_apply, flow_const X hχ hξ hx, mul_assoc, integral_const_mul]
    ring
  · simp
  · simp

theorem mul_mem_SS (X : Data E r) {χ : Frame X.Ψ r → ℂ} (hχ : IsIdemFn X χ) (la : Wt X.Ψ r)
    {P : Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) : χ * P ∈ X.SS la := by
  simp only [Data.SS, Set.mem_ofPred_eq] at hP ⊢
  obtain ⟨⟨⟨hd, hB, hΓ⟩, C, hC⟩, hcusp⟩ := hP
  refine ⟨⟨⟨hχ.2.1.mul hd, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩, C, fun x hx => ?_⟩,
    fun ξ hξ x hx => ?_⟩
  · simp only [Pi.mul_apply]
    rw [hχ.2.2.1 x hx b hb, hB x hx b hb]
    ring
  · simp only [Pi.mul_apply]
    rw [hχ.2.2.2 γ hγ x hx, hΓ γ hγ x hx]
    ring
  · have hnorm : X.pnorm la (χ * P) x = ‖χ x‖ * X.pnorm la P x := by
      simp only [Data.pnorm, Pi.mul_apply, norm_mul, mul_assoc]
    have h1 : ‖χ x‖ ≤ 1 := by
      rcases hχ.1 x hx with h | h <;> simp [h]
    have h0 : 0 ≤ X.pnorm la P x := by
      unfold Data.pnorm
      positivity
    rw [hnorm]
    exact (mul_le_of_le_one_left h0 h1).trans (hC x hx)
  · rw [fj_mul X hχ la hξ P hx, hcusp ξ hξ x hx, mul_zero]

def mulL {ι : Type} (X : ι → Data E r) (χ : Formalism.L2.PjFree.FDSec X) :
    Formalism.L2.PjFree.FDSec X →ₗ[ℂ] Formalism.L2.PjFree.FDSec X where
  toFun P := fun k => χ k * P k
  map_add' P Q := by
    funext k x
    simp [mul_add]
  map_smul' a P := by
    funext k x
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem mul_mem_holSub {ι : Type} (X : ι → Data E r) (la : ∀ k, Wt (X k).Ψ r)
    (χ : Formalism.L2.PjFree.FDSec X) (hχ : ∀ k, IsIdemFn (X k) (χ k)) {P : Formalism.L2.PjFree.FDSec X}
    (hP : P ∈ Formalism.L2.PjFree.holSub X la) : (fun k => χ k * P k) ∈ Formalism.L2.PjFree.holSub X la := by
  have hle : (Formalism.L2.PjFree.holSub X la).map (mulL X χ) ≤ Formalism.L2.PjFree.holSub X la := by
    unfold Formalism.L2.PjFree.holSub
    rw [Submodule.map_span_le]
    intro Q hQ
    exact Submodule.subset_span fun k => mul_mem_SS (X k) (hχ k) (la k) (hQ k)
  exact hle (Submodule.mem_map_of_mem hP)

theorem chi_zero (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : X.χ 0 γ = 1 := by
  have hsq : X.χ 0 γ * X.χ 0 γ = X.χ 0 γ := by
    have h := X.χ_add 0 0 γ hγ
    rw [add_zero] at h
    exact h.symm
  obtain ⟨n, hn, hpow⟩ := X.χ_fin 0
  have hne : X.χ 0 γ ≠ 0 := by
    intro h0
    have h := hpow γ hγ
    rw [h0, zero_pow hn.ne'] at h
    exact zero_ne_one h
  exact mul_left_cancel₀ hne (by rw [hsq, mul_one])

theorem isIdemFn_of_isSec (X : Data E r) {χ : Frame X.Ψ r → ℂ} (h : X.IsSec 0 χ) (hi : χ * χ = χ) :
    IsIdemFn X χ := by
  obtain ⟨hd, hB, hΓ⟩ := h
  refine ⟨fun x _ => ?_, hd, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have hx2 : χ x * χ x = χ x := congrFun hi x
    by_cases h0 : χ x = 0
    · exact Or.inl h0
    · exact Or.inr (mul_left_cancel₀ h0 (by rw [hx2, mul_one]))
  · rw [hB x hx b hb]
    simp [bchar]
  · rw [hΓ γ hγ x hx, chi_zero X hγ, one_mul]

end Model

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

section Read

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem rdU_mul (U : Formalism.L2.PjFree.Unf Xo c σ r) (f g : Rul Xo c) :
    Formalism.L2.PjFree.rdU U (f * g) = fun k => Formalism.L2.PjFree.rdU U f k * Formalism.L2.PjFree.rdU U g k := by
  funext k x
  simp only [Formalism.L2.PjFree.rdU, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply]
  by_cases h : x ∈ (U.X k).dom
  · simp only [dif_pos h]
    unfold Formalism.L2.PjFree.toC evR evalAt
    split_ifs with h1
    · exact map_mul _ _ _
    · exact (mul_zero _).symm
  · simp only [dif_neg h, mul_zero]

theorem laU_zero (U : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) : Formalism.L2.PjFree.laU U 0 0 k = 0 := by
  unfold Formalism.L2.PjFree.laU
  funext τ j
  simp

end Read

theorem idem_mul_mem_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ χ ∈ sec Xo c 0 0, χ * χ = χ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ Formalism.L2.PjFree.cusp Xo c U a n, χ * g ∈ Formalism.L2.PjFree.cusp Xo c U a n := by
  intro E _ _ _ H Dw l Xo c r U hU χ hχ hi a n g hg
  have hχ' := hχ
  unfold sec secW at hχ'
  obtain ⟨hχn, hχw⟩ := hχ'
  unfold Formalism.L2.PjFree.cusp at hg ⊢
  obtain ⟨hgs, hgc⟩ := Submodule.mem_inf.mp hg
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  ·
    have hgs' := hgs
    unfold sec secW at hgs' ⊢
    obtain ⟨hgn, hgw⟩ := hgs'
    refine ⟨fun p q φ y z hyz => ?_, fun p t y y' hyy => ?_⟩
    · show χ q z * g q z = φ (χ p y * g p y)
      rw [hχn p q φ y z hyz, hgn p q φ y z hyz, map_mul]
    · show χ p y' * g p y' = _ * (χ p y * g p y)
      rw [hχw p t y y' hyy, hgw p t y y' hyy]
      have h1 : wchar (ex Dw 0 0) t = 1 := by simp [wchar, ex]
      rw [h1]
      ring
  ·
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hgc ⊢
    intro σ hσ
    have hsec := (hU σ hσ).2.2.2.2.1 0 0 (by unfold Formalism.L2.Pj.Dom; simp [antitone_const]) χ hχ
    rw [rdU_mul]
    refine mul_mem_holSub (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) (Formalism.L2.PjFree.rdU (U σ) χ)
      (fun k => ?_) (hgc σ hσ)
    apply isIdemFn_of_isSec
    · have hk := hsec k
      rwa [laU_zero] at hk
    · have hk := congrFun (rdU_mul (U σ) χ χ) k
      rw [hi] at hk
      exact hk.symm

end GlobalTheory.Reg.IdemCusp
end
end
