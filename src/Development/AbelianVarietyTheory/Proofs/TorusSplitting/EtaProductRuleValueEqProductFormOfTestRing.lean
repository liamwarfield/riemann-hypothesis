module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UnitaryDatumNumbersForSupBounds
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaProductRuleValueEqProductFormOfTestRing
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaProductRuleValueEqProductFormOfTestRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.EtaForm

attribute [local instance] Over.cartesianMonoidalCategory in
set_option autoImplicit false in
theorem _root_.GlobalTheory.EtaForm.etaValAt_evR_of_fromTest : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (R : ℕ), Odd R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → _root_.GlobalTheory.EtaForm.LatMod Dw (R ^ 4)) (f : _root_.Formalism.L2.Pj.Rul Xo c), _root_.GlobalTheory.EtaForm.IsEtaRule Xo c R cf xs f → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : _root_.Formalism.L2.Pj.FrPt Xo c S), _root_.Formalism.L2.Pj.FromTest (K := c.F) (fun S _ _ => _root_.Formalism.L2.Pj.FrPt Xo c S) (fun φ y z => _root_.Formalism.L2.Pj.FrMap φ y z) y → _root_.GlobalTheory.EtaForm.EtaValAt Xo c R cf xs y (_root_.Formalism.L2.Pj.evR Xo c f y) ∧ ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (z : _root_.Formalism.L2.Pj.FrPt Xo c S'), _root_.Formalism.L2.Pj.FrMap φ y z → _root_.GlobalTheory.EtaForm.EtaValAt Xo c R cf xs z (φ (_root_.Formalism.L2.Pj.evR Xo c f y)) := by
  intro E _ _ _ H Dw l Xo c R hR J _ n cf xs f hf S _ _ y hy
  have hlaws := _root_.GlobalTheory.EtaForm.etaValAt_existsUnique_natural _root_.GlobalTheory.firstFiveLaws.1
    E H Dw l Xo c R hR J n cf xs
  have transport : ∀ (S₀ S₁ : Type) [CommRing S₀] [Algebra c.F S₀] [CommRing S₁] [Algebra c.F S₁]
      (φ : S₀ →ₐ[c.F] S₁) (y₀ : _root_.Formalism.L2.Pj.FrPt Xo c S₀) (y₁ : _root_.Formalism.L2.Pj.FrPt Xo c S₁) (v : S₀),
      _root_.Formalism.L2.Pj.FrMap φ y₀ y₁ → _root_.GlobalTheory.EtaForm.EtaValAt Xo c R cf xs y₀ v →
        _root_.GlobalTheory.EtaForm.EtaValAt Xo c R cf xs y₁ (φ v) := by
    intro S₀ S₁ _ _ _ _ φ y₀ y₁ v hφ hv
    obtain ⟨w, hw, -⟩ := hlaws.1 S₁ y₁
    rwa [hlaws.2 S₀ S₁ φ y₀ y₁ hφ v w hv hw]
  have key : ∃ (p : _root_.Formalism.L2.Pj.TRing c.F) (φ : p.R →ₐ[c.F] S) (y₀ : _root_.Formalism.L2.Pj.FrPt Xo c p.R),
      _root_.Formalism.L2.Pj.FrMap φ y₀ y ∧ _root_.Formalism.L2.Pj.evR Xo c f y = φ (f p y₀) := by
    refine ⟨hy.choose, hy.choose_spec.choose, hy.choose_spec.choose_spec.choose,
      hy.choose_spec.choose_spec.choose_spec, ?_⟩
    unfold _root_.Formalism.L2.Pj.evR _root_.Formalism.L2.Pj.evalAt
    rw [dite_eq_left hy]
  obtain ⟨p, φ, y₀, hφ, hval⟩ := key
  have h₀ : _root_.GlobalTheory.EtaForm.EtaValAt Xo c R cf xs y₀ (f p y₀) := hf p y₀
  refine ⟨hval ▸ transport _ _ φ y₀ y _ hφ h₀, ?_⟩
  intro S' _ _ ψ z hz
  rw [hval]
  exact transport _ _ (ψ.comp φ) y₀ z _ (_root_.GlobalTheory.FramedBaseChange.trans φ ψ hφ hz) h₀

end GlobalTheory.EtaForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaProductRuleValueEqProductFormOfTestRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaProductRule_value_eq_productForm_of_testRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : ℕ), Odd R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod Dw (R ^ 4)) (f : Rul Xo c), IsEtaRule Xo c R cf xs f → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y → EtaValAt Xo c R cf xs y (evR Xo c f y) ∧ ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (z : FrPt Xo c S'), FrMap φ y z → EtaValAt Xo c R cf xs z (φ (evR Xo c f y)) := by
  first | exact @GlobalTheory.EtaForm.etaValAt_evR_of_fromTest | exact GlobalTheory.EtaForm.etaValAt_evR_of_fromTest | (intros; apply GlobalTheory.EtaForm.etaValAt_evR_of_fromTest <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.IntegralThetaSectionExistsAndBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.IntegralThetaSectionExistsAndBaseChange
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

open GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg.ChartInhab GlobalTheory.Reg.LiftUnique in
theorem intSec_baseChange {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V']
    [Algebra c.F (FractionRing V)] [Algebra c.F (FractionRing V')] (φ : V →+* V')
    (ψ : FractionRing V →ₐ[c.F] FractionRing V') (y : FrPt Xo c (FractionRing V)) (y' : FrPt Xo c (FractionRing V'))
    (G : SAB H (Sp V)) (G' : SAB H (Sp V')) (m : SABMap G' G (spMap φ)) (I : IntSec Xo V y.x y.s G)
    (hψ : ∀ a, ψ (algebraMap V _ a) = algebraMap V' _ (φ a)) (hm : FrMap ψ y y') :
    Nonempty (IntSec Xo V' y'.x y'.s G') := by
  obtain ⟨t, m1, m2, θ, w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩ := I
  obtain ⟨hx, -, pm, hs, hf, ha⟩ := hm
  obtain ⟨t', ⟨n⟩⟩ : ∃ t' : SAB H (Sp (FractionRing V')), Nonempty (SABMap t' t (spMap ψ.toRingHom)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap ψ.toRingHom) t
    exact ⟨_, ⟨m⟩⟩
  have hι : ψ.toRingHom.comp (algebraMap V (FractionRing V)) = (algebraMap V' (FractionRing V')).comp φ :=
    RingHom.ext hψ
  have hio : spMap (algebraMap V' (FractionRing V')) ≫ spMap φ =
      spMap ψ.toRingHom ≫ spMap (algebraMap V (FractionRing V)) := by
    rw [← FrBC.spMap_comp', ← FrBC.spMap_comp', hι]
  obtain ⟨w0, r0⟩ := exists_rigIso n
  obtain ⟨m1', e₁, -⟩ := exists_comp_rig m1 n y'.x hx a1 r0
  obtain ⟨m2', e₂, -⟩ := exists_comp_rig m2 n _ hio a2 r0
  have T₀ := (FrUniq.tie_iff m1 m2 θ y.s).1 ⟨w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩
  have T₁ := FrUniq.tie_pull m1 m2 θ y.s n m1' m2' hx hio e₁ e₂ y'.s pm hs hf (fun Z r z j hz => by
    have hle := FramedBaseChange.chart_le pm hs (fun _ => j)
    rw [← ha _ hle, gs_appLE pm _ _ hle r z hz]) T₀
  obtain ⟨w1', w2', σ', s1', θ2', r1, r2, i1, i2, p2, hg⟩ := (FrUniq.tie_iff m1' m2' θ y'.s).2 T₁
  obtain ⟨m', e₃⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m m2'
  obtain ⟨w, θ', rw', iw⟩ := pull_sec G G' m θ
  have pw : PullSec m.φ θ (thfPull G.PP.L m.φ θ) := fun _ _ => rfl
  obtain ⟨w', r', i'⟩ := FrBC.exists_isoMaps_cancel m m' m2' rfl e₃ rw' r2 iw pw i2 p2
  exact ⟨⟨t', m1', m', θ', w1', w', σ', s1', _, r1, r', i1, i', fun _ _ => rfl, hg⟩⟩

theorem intSec_exists_and_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), letI := io.toAlgebra; ∃ G : SAB H (Sp T.V), Nonempty (IntSec Xo T.V y.1.x y.1.s G)) ∧ ∀ (V V' : Type) [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [Algebra c.F (FractionRing V)] [Algebra c.F (FractionRing V')] (φ : V →+* V') (ψ : FractionRing V →ₐ[c.F] FractionRing V') (y : FrPt Xo c (FractionRing V)) (y' : FrPt Xo c (FractionRing V')) (G : SAB H (Sp V)) (G' : SAB H (Sp V')) (_ : SABMap G' G (spMap φ)) (_ : IntSec Xo V y.x y.s G), (∀ a, ψ (algebraMap V _ a) = algebraMap V' _ (φ a)) → FrMap ψ y y' → Nonempty (IntSec Xo V' y'.x y'.s G') := by
  intro E _ _ _ H Dw l Xo c
  refine ⟨fun T io y => ?_, fun V V' _ _ _ _ _ _ φ ψ y y' G G' m I hψ hm =>
    intSec_baseChange φ ψ y y' G G' m I hψ hm⟩
  obtain ⟨G, t', m1, m2, -, θ, -, w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩ := y.2.2
  exact ⟨G, ⟨⟨t', m1, m2, θ, w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩⟩⟩

end GlobalTheory.EtaVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.IntegralThetaSectionExistsAndBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralThetaSection_exists_and_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), letI := io.toAlgebra; ∃ G : SAB H (Sp T.V), Nonempty (IntSec Xo T.V y.1.x y.1.s G)) ∧ ∀ (V V' : Type) [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [Algebra c.F (FractionRing V)] [Algebra c.F (FractionRing V')] (φ : V →+* V') (ψ : FractionRing V →ₐ[c.F] FractionRing V') (y : FrPt Xo c (FractionRing V)) (y' : FrPt Xo c (FractionRing V')) (G : SAB H (Sp V)) (G' : SAB H (Sp V')) (_ : SABMap G' G (spMap φ)) (_ : IntSec Xo V y.x y.s G), (∀ a, ψ (algebraMap V _ a) = algebraMap V' _ (φ a)) → FrMap ψ y y' → Nonempty (IntSec Xo V' y'.x y'.s G') := by
  first | exact @GlobalTheory.EtaVal.intSec_exists_and_baseChange | exact GlobalTheory.EtaVal.intSec_exists_and_baseChange | (intros; apply GlobalTheory.EtaVal.intSec_exists_and_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.FullLinearLevelEqExpPeriodsComplexPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.FullLinearLevelEqExpPeriodsComplexPoint
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace LevelPeriods

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem exists_periods (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (Fu.Di i) ty Pm) (N : ℕ) (hN : 0 < N)
    (ev : LatMod Dw N → (ptO Xo (Fu.u i Pm) ⟶ Xo.univ.t.G)) (hev : IsFullLev Xo N (Fu.u i Pm) ev) :
    ∃ a : LatMod Dw N → (Fu.Di i).La, (∀ q, ev q = Fu.ex i Pm ((N : ℂ)⁻¹ • Pm (a q)) ∧ ev q ^ N = 1) ∧
      ∀ (n : ℕ) (z : Fin n → LatMod Dw N), Submodule.span (𝓞 E) (Set.range z) = ⊤ → ∀ u : (Fu.Di i).La,
        ∃ (cf : Fin n → 𝓞 E) (v : (Fu.Di i).La), u = ∑ b, cf b • a (z b) + N • v := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  let f : (Fin g → ℂ) →+ Additive (ptO Xo (Fu.u i Pm) ⟶ Xo.univ.t.G) :=
    AddMonoidHom.mk' (fun z => Additive.ofMul (Fu.ex i Pm z)) fun z w => congrArg Additive.ofMul (Fu.ex_add i Pm hP z w)
  let e : LatMod Dw N →+ Additive (ptO Xo (Fu.u i Pm) ⟶ Xo.univ.t.G) :=
    AddMonoidHom.mk' (fun q => Additive.ofMul (ev q)) fun a b => congrArg Additive.ofMul (hev.1 a b)
  have hker : ∀ z, f z = 0 ↔ z ∈ Pm.range := fun z => Fu.ex_ker i Pm hP z
  have hNN : ∀ z : Fin g → ℂ, N • ((N : ℂ)⁻¹ • z) = z := fun z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  have hNN' : ∀ z : Fin g → ℂ, (N : ℂ)⁻¹ • (N • z) = z := fun z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
  have hpow : ∀ q, ev q ^ N = 1 := FullLevel.pow_eq_one Xo hev
  have hex : ∀ q, ∃ a, e q = f ((N : ℂ)⁻¹ • Pm a) := fun q => by
    obtain ⟨z, hz⟩ := Fu.ex_onto i Pm hP (ev q)
    have hz' : f z = e q := congrArg Additive.ofMul hz
    have h0 : N • e q = 0 := congrArg Additive.ofMul (hpow q)
    rw [← hz', ← map_nsmul, hker] at h0
    obtain ⟨a, ha⟩ := h0
    exact ⟨a, by rw [ha, hNN', hz']⟩
  choose a ha using hex
  refine ⟨a, fun q => ⟨congrArg Additive.toMul (ha q), hpow q⟩, fun n z hz u => ?_⟩
  have hu : N • f ((N : ℂ)⁻¹ • Pm u) = 0 := by
    rw [← map_nsmul, hNN, hker]
    exact ⟨u, rfl⟩
  obtain ⟨q, hq⟩ := FullLevel.onto_of_local Xo GlobalTheory.firstFiveLaws.1 hN hev (Fu.ex i Pm ((N : ℂ)⁻¹ • Pm u))
    (congrArg Additive.toMul hu)
  have hq' : e q = f ((N : ℂ)⁻¹ • Pm u) := congrArg Additive.ofMul hq
  obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hz ▸ Submodule.mem_top : q ∈ Submodule.span (𝓞 E) (Set.range z))
  have hlin : ∀ (o : 𝓞 E) r, e (o • r) = f ((N : ℂ)⁻¹ • Pm (o • a r)) := fun o r => by
    have h1 : (N : ℂ)⁻¹ • Pm (o • a r) = fun k => ty k (o : E) * ((N : ℂ)⁻¹ • Pm (a r)) k := by
      funext k
      simp only [Pi.smul_apply, smul_eq_mul, hP.1]
      ring
    have h2 : ev r = Fu.ex i Pm ((N : ℂ)⁻¹ • Pm (a r)) := congrArg Additive.toMul (ha r)
    refine congrArg Additive.ofMul (?_ : ev (o • r) = Fu.ex i Pm _)
    rw [h1, Fu.ex_lin i Pm hP, hev.2.1, h2]
  have hsum : e q = f ((N : ℂ)⁻¹ • Pm (∑ b, cf b • a (z b))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hcf, map_sum, map_sum, Finset.smul_sum, map_sum]
    exact Finset.sum_congr rfl fun b _ => hlin _ _
  have h0 : f ((N : ℂ)⁻¹ • Pm (u - ∑ b, cf b • a (z b))) = 0 := by
    rw [map_sub, smul_sub, map_sub, ← hq', ← hsum, sub_self]
  obtain ⟨v, hv⟩ := (hker _).1 h0
  refine ⟨cf, v, ?_⟩
  have h1 : N • v = u - ∑ b, cf b • a (z b) := hP.2.1 (by rw [map_nsmul, hv, hNN])
  rw [h1, add_sub_cancel]

end LevelPeriods

theorem fullLevel_eq_exp_periods :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (y : FrPt Xo c (CAt σ)), IsPeriod (Fu.Di i) ty Pm → y.x = Fu.u i Pm → ∀ (N : ℕ), 0 < N → ∀ ev : LatMod Dw N → (ptO Xo y.x ⟶ Xo.univ.t.G), IsFullLev Xo N y.x ev → ∃ a : LatMod Dw N → (Fu.Di i).La, (∀ q, (ev q).left = (Fu.ex i Pm ((N : ℂ)⁻¹ • Pm (a q))).left ∧ ev q ^ N = 1) ∧ ∀ (n : ℕ) (z : Fin n → LatMod Dw N), Submodule.span (𝓞 E) (Set.range z) = ⊤ → ∀ u : (Fu.Di i).La, ∃ (cf : Fin n → 𝓞 E) (v : (Fu.Di i).La), u = ∑ b, cf b • a (z b) + N • v := by
  intro E _ _ _ H Dw l Xo c σ g ty Fu i Pm y hP hy N hN ev hev
  obtain ⟨x, _, _, _, _, _, _, _⟩ := y
  dsimp only at hy ev hev ⊢
  subst hy
  obtain ⟨a, h1, h2⟩ := LevelPeriods.exists_periods Fu i Pm hP N hN ev hev
  exact ⟨a, fun q => ⟨congrArg CommaMorphism.left (h1 q).1, (h1 q).2⟩, h2⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.FullLinearLevelEqExpPeriodsComplexPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullLinearLevel_eq_exp_periods_complexPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (y : FrPt Xo c (CAt σ)), IsPeriod (Fu.Di i) ty Pm → y.x = Fu.u i Pm → ∀ (N : ℕ), 0 < N → ∀ ev : LatMod Dw N → (ptO Xo y.x ⟶ Xo.univ.t.G), IsFullLev Xo N y.x ev → ∃ a : LatMod Dw N → (Fu.Di i).La, (∀ q, (ev q).left = (Fu.ex i Pm ((N : ℂ)⁻¹ • Pm (a q))).left ∧ ev q ^ N = 1) ∧ ∀ (n : ℕ) (z : Fin n → LatMod Dw N), Submodule.span (𝓞 E) (Set.range z) = ⊤ → ∀ u : (Fu.Di i).La, ∃ (cf : Fin n → 𝓞 E) (v : (Fu.Di i).La), u = ∑ b, cf b • a (z b) + N • v := by
  first | exact @GlobalTheory.fullLevel_eq_exp_periods | exact GlobalTheory.fullLevel_eq_exp_periods | (intros; apply GlobalTheory.fullLevel_eq_exp_periods <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsHeisenbergLiftsSpanLatticeClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsHeisenbergLiftsSpanLatticeClasses
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem exists_qkPt_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] (G : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) G), P.TorsionIso → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → ∀ (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (ev : M → (TFK (R := V) F ⟶ P.A.A)), (∀ a b, ev (a + b) = ev a * ev b) → (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ (letI := H.starRing; P.oA.act o : P.A.A ⟶ P.A.A)) → (∀ a, ev a ^ N = 1) → (∀ u, u ^ N = 1 → ∃ a, ev a = u) → ∃ pt : M → QkPt P.D.toPre F N, (∀ a, P.ToA F N (pt a) (ev a)) ∧ ∀ (n : ℕ) (z : Fin n → M), Submodule.span (𝓞 E) (Set.range z) = ⊤ → ∀ a : P.D.toPre.X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range fun b => (pt (z b)).y), ∃ t : P.D.toPre.X, a = u + N • t := by
  intro E _ _ _ H V _ _ _ _ hc G P hT F _ _ _ N hN M _ _ ev hadd hsm hpow hsurj
  letI := H.starRing
  open GlobalTheory.TorusExt in
  obtain ⟨f, hto, hon, heq, hfa, hfs, -⟩ := hT F N hN
  have hB := P.D.tau_bimult
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  letI := GlobalTheory.TorusExt.gtGroup P.D.toPre F
  let iotaLocal : P.D.toPre.X →+ GtPtF P.D.toPre F := AddMonoidHom.mk'
    (fun x => (GlobalTheory.TorusExt.exists_iota (F := F) hB x).choose) (by
      intro x x'
      obtain ⟨b, v⟩ := (GlobalTheory.TorusExt.isIota_iff_val _ _).1 (GlobalTheory.TorusExt.exists_iota (F := F) hB x).choose_spec
      obtain ⟨b', v'⟩ := (GlobalTheory.TorusExt.isIota_iff_val _ _).1 (GlobalTheory.TorusExt.exists_iota (F := F) hB x').choose_spec
      obtain ⟨b'', v''⟩ := (GlobalTheory.TorusExt.isIota_iff_val _ _).1 (GlobalTheory.TorusExt.exists_iota (F := F) hB (x + x')).choose_spec
      refine (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 ((GlobalTheory.TorusExt.isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', cPoint_add], fun χ y J hJ => ?_⟩)
      have sym01 (a b c : TF (R := V) F ⟶ P.D.toPre.P.A) :
          th P.D.toPre y J a b c = th P.D.toPre y J b a c := by
        have e := (val_corr hJ P.D.toPre.cub.cubeSymmetric_swap_first (lift a (lift b c)).left).trans
          (val_cub P.D.toPre.cub (lift a (lift b c)) hJ _ _ _)
        refine e.trans ?_
        congr 1 <;> simp [x3]
      have sym12 (a b c : TF (R := V) F ⟶ P.D.toPre.P.A) :
          th P.D.toPre y J a b c = th P.D.toPre y J a c b := by
        have e := (val_corr hJ P.D.toPre.cub.cubeSymmetric_swap_last (lift a (lift b c)).left).trans
          (val_cub P.D.toPre.cub (lift a (lift b c)) hJ _ _ _)
        refine e.trans ?_
        congr 1 <;> simp [x3]
      rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', sym01, sym12]
      exact tau_mul (𝟙 (TF (R := V) F)) hJ hB x x' χ)
  have hi (x : P.D.toPre.X) : GtPtF.IsIota x (iotaLocal x) := (GlobalTheory.TorusExt.exists_iota hB x).choose_spec
  have hn (p : QkPt P.D.toPre F N) : N • p.g = iotaLocal p.y := by
    obtain ⟨h, hn, hi'⟩ := p.eq
    exact ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hn).symm.trans (GlobalTheory.TorusExt.isIota_unique hi' (hi p.y))
  choose pt hpt using fun a => hon (ev a) (hpow a)
  refine ⟨pt, fun a => (hto _ _).2 (hpt a).symm, fun n z hz y => ?_⟩
  have yadd : ∀ a b, ∃ t : P.D.toPre.X, (pt (a + b)).y = (pt a).y + (pt b).y + N • t := fun a b => by
    let q : QkPt P.D.toPre F N := ⟨(pt a).y + (pt b).y, (pt a).g + (pt b).g,
      iotaLocal ((pt a).y + (pt b).y), (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 (by
        rw [nsmul_add, hn, hn, map_add]), hi _⟩
    have e := hfa _ _ _ (show QkAdd (pt a) (pt b) q from
      ⟨q, rfl, (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl, qk_equiv_refl hB q⟩)
    rw [hpt, hpt, ← hadd, ← hpt] at e
    obtain ⟨t, ht, -⟩ := (heq _ _).1 e
    exact ⟨t, ht⟩
  have ysm : ∀ (o : 𝓞 E) a, ∃ t : P.D.toPre.X, (pt (o • a)).y = o • (pt a).y + N • t := fun o a => by
    obtain ⟨q, hq⟩ := qkAct_exists hG hB P.oD o (pt a)
    obtain ⟨r, hr, hact, he⟩ := hq
    have e := hfs _ _ _ (show QkAct P.oD o (pt a) r from ⟨r, hr, hact, qk_equiv_refl hB r⟩)
    rw [hpt, ← hsm, ← hpt] at e
    obtain ⟨t, ht, -⟩ := (heq _ _).1 e
    exact ⟨t, by simpa [hr] using ht⟩
  have key : ∀ m ∈ Submodule.span (𝓞 E) (Set.range z),
      ∃ u ∈ Submodule.span (𝓞 E) (Set.range fun b => (pt (z b)).y), ∃ t : P.D.toPre.X, (pt m).y = u + N • t := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact ⟨_, Submodule.subset_span ⟨b, rfl⟩, 0, by rw [smul_zero, add_zero]⟩
    | zero =>
      obtain ⟨t, ht⟩ := ysm 0 0
      rw [zero_smul, zero_smul] at ht
      exact ⟨0, Submodule.zero_mem _, t, ht⟩
    | add a b _ _ ha hb =>
      obtain ⟨u, hu, t, ht⟩ := ha
      obtain ⟨u', hu', t', ht'⟩ := hb
      obtain ⟨s, hs⟩ := yadd a b
      exact ⟨u + u', Submodule.add_mem _ hu hu', t + t' + s, by
        rw [hs, ht, ht', smul_add, smul_add]; abel⟩
    | smul o a _ ha =>
      obtain ⟨u, hu, t, ht⟩ := ha
      obtain ⟨s, hs⟩ := ysm o a
      exact ⟨o • u, Submodule.smul_mem _ o hu, o • t + s, by
        rw [hs, ht, smul_add, smul_add, smul_comm o N t, add_assoc]⟩
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨g, hg⟩ := (GlobalTheory.UT.gt_onto_divisible_kernel GlobalTheory.firstFiveLaws V _ hA P.D F).2.1 N hN
    (iotaLocal y)
  let p : QkPt P.D.toPre F N :=
    ⟨y, g, iotaLocal y, hg, hi y⟩
  have hp : f p ^ N = 1 := by
    obtain ⟨w, hw⟩ := P.U.ext
    exact ((hto p _).2 rfl w hw).1
  obtain ⟨m, hm⟩ := hsurj _ hp
  obtain ⟨s, hs, -⟩ := (heq (pt m) p).1 ((hpt m).trans hm)
  obtain ⟨u, hu, t, ht⟩ := key m (hz ▸ Submodule.mem_top)
  refine ⟨u, hu, t + s, ?_⟩
  have hs' : y = (pt m).y + N • s := hs
  rw [hs', ht, smul_add, add_assoc]

end GlobalTheory.EtaVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsHeisenbergLiftsSpanLatticeClassesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenbergLifts_span_latticeClasses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] (G : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) G), P.TorsionIso → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → ∀ (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (ev : M → (TFK (R := V) F ⟶ P.A.A)), (∀ a b, ev (a + b) = ev a * ev b) → (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ (letI := H.starRing; P.oA.act o : P.A.A ⟶ P.A.A)) → (∀ a, ev a ^ N = 1) → (∀ u, u ^ N = 1 → ∃ a, ev a = u) → ∃ pt : M → QkPt P.D.toPre F N, (∀ a, P.ToA F N (pt a) (ev a)) ∧ ∀ (n : ℕ) (z : Fin n → M), Submodule.span (𝓞 E) (Set.range z) = ⊤ → ∀ a : P.D.toPre.X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range fun b => (pt (z b)).y), ∃ t : P.D.toPre.X, a = u + N • t := by
  first | exact @GlobalTheory.EtaVal.exists_qkPt_span | exact GlobalTheory.EtaVal.exists_qkPt_span | (intros; apply GlobalTheory.EtaVal.exists_qkPt_span <;> assumption)
end
end
