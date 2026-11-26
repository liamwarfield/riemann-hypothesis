module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTRph
public import Formalism.LocalToGlobal.IndefiniteReal.PrimitivePackageFullHecke
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Rescale
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RightActionThreeFamilies
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActMass
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeNC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOnto
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict
open Formalism.L2.SG.ProjRows Formalism.MainNotions.S
open scoped InnerProductSpace

namespace Formalism.L2.SG.EvalTOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem rows_eq_hom
    (hL : ∀ v, Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)))
    (z : L2X X) (hz : z ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) :
    ∃ Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re, Φ (X.B.tens X.B.w) = z := by
  have hB := Formalism.L2.SG.Closed.RowsBij_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec X.B.e X.B.Re
    X.B.Re_spec X.B.H X.B.σ X.dv X.B.w (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (Formalism.L2.SG.EvalTRph.isFdeg_dv X) (fun v => (X.low v).1) hL X.Rph X.Rph_spec X.B.Hs X.B.σs X.B.tens
    X.B.tens_spec
  have hz' : z ∈ LinearMap.range (Formalism.L2.SG.RowsDef.evAt X.B.I X.B.μf X.B.fund X.B.σs X.B.R X.B.Re
      (X.B.tens X.B.w)) := by
    rw [hB.2]; exact hz
  obtain ⟨S, hS⟩ := hz'
  exact ⟨S, S.2, hS⟩

variable {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (E : Submodule ℂ (MMap M)) (G : GoodOp X)
  (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec)

variable {X M E G ι t v₀}

end Formalism.L2.SG.EvalTOnto

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTIn
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def cutStd : Formalism.FourierDecayAlt.LE.Cut where
  χ := chiStd
  smooth := isCut0_chiStd.1
  zero x hx := Real.smoothTransition.zero_of_nonpos (by linarith)
  one x hx := Real.smoothTransition.one_of_one_le (by linarith)
  nonneg _ := Real.smoothTransition.nonneg _
  le_one _ := Real.smoothTransition.le_one _

theorem isCut0_cut (c : Formalism.FourierDecayAlt.LE.Cut) : Formalism.FourierDecayAlt.C6.IsCut0 c.χ :=
  ⟨c.smooth, ⟨1 / 2, by norm_num, fun x hx => c.zero x hx.le⟩, c.one⟩

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)

abbrev parE (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (u u' : D.what₂.Word) (de de' : ℕ → ℝ) (j : Fin (nfE D)) :
    Formalism.FourierDecayAlt.M.Par :=
  ⟨D.R.k, D.R.rS, ((D.mem u).A.T : ℝ), ((D.mem u').A.T : ℝ),
    ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place (plE D j)).u de, ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place (plE D j)).u de'⟩

def carrierInT (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ) : CarrierIn X u u' :=
  carrierIn X C u u' e he hv CA de de' l grid grid1 fc c.χ
    (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1)) ν' m₀
    (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j) (ν' j) (m₀ j) (Θ j) (TP j)) A₀

end Formalism.L2.SG.Pf.CarrierT
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTReg
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace Formalism.L2.SG.EvalTReg

section Abs

open Formalism.MainNotions.LeviCoordinates

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G}

theorem reg_toLp (h : rr_FD μ Γ D) {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}
    (hR : rr_IsReg μ Γ D R) (f0 : G → ℂ) (hinv : ∀ γ ∈ Γ, ∀ y, f0 (γ * y) = f0 y)
    (hm : MemLp f0 2 (μ.restrict D)) (g : G) :
    ((R g (hm.toLp f0) : Lp ℂ 2 (μ.restrict D)) : G → ℂ) =ᵐ[μ.restrict D] fun x => f0 (x * g) := by
  have hmap := rr_map h g
  have h3 : ∀ᵐ x ∂(μ.restrict D), (hm.toLp f0 : G → ℂ) (rr_rep (Γ : Set G) D (x * g)) =
      f0 (rr_rep (Γ : Set G) D (x * g)) := by
    refine ae_of_ae_map (p := fun y => (hm.toLp f0 : G → ℂ) y = f0 y) hmap.1 ?_
    rw [hmap.2]
    exact hm.coeFn_toLp
  filter_upwards [hR g (hm.toLp f0), h3] with x a1 a2
  rw [a1, a2]
  obtain ⟨γ, hγ, e1, -⟩ := rr_rep_spec h (x * g)
  rw [e1, hinv γ hγ]

end Abs

section X

open Formalism.BasicNotions Formalism.MainNotions.LeviCoordinates Formalism.L2.SG.RowDict Formalism.L2.SG.Pf

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem reg_toLp_X (f0 : X.B.I.GA → ℂ) (hinv : ∀ γ ∈ X.B.I.GFset, ∀ y, f0 (γ * y) = f0 y)
    (hm : MemLp f0 2 (muX X)) (y : X.B.I.GA) :
    ((X.B.R y (hm.toLp f0) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x => f0 (x * y) := by
  have := X.B.sf
  have := X.B.haar
  have := gf_secondCountable X.B.I
  have := muf_right X
  have := rr_muA_sigmaFinite X.B.I X.B.μf
  have := rr_muA_left X.B.I X.B.μf
  have := rr_muA_right X.B.I X.B.μf
  exact reg_toLp (rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec)
    (rr_IsReg_of X.B.I X.B.μf X.B.fund X.B.R X.B.R_spec) f0 hinv hm y

end X

section Polar

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

end Polar

section Transfer

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}
  {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {t : GA D (D.sp.Y 0)} {c : ℝ}

end Transfer

end Formalism.L2.SG.EvalTReg

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ToTermAct
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.NormCut Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Act

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem eq_isoG {g : Gam X u'} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X (g : X.B.I.GA) β) :
    β = Formalism.L2.SG.Pf.Act.isoG g := by
  apply LinearEquiv.ext
  intro y
  apply Formalism.L2.SG.Pf.Act.inclCrd_inj
  rw [Formalism.L2.SG.Pf.Act.isoG_spec, ← Formalism.L2.SG.Pf.LatDictK.ratLink_incl X hx y]

theorem kB_mem (q : {Λ // Λ ∈ Y.what₂ u'}) (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) :
    Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') q.1 γ.1 ∈ X.B.I.Kset := by
  unfold Formalism.L2.SG.Pf.SatGramActL.kB
  rw [Formalism.L2.SG.Pf.Act.aK_eq]
  exact γ.2


variable (Y) in
theorem isoG_lift (q : {Λ // Λ ∈ Y.what₂ u'}) (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) :
    RatLink X (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1) ∧
      Formalism.L2.SG.Pf.Act.isoG γ.1 ∈ Formalism.L2.SG.Saturated.AutF q.1 (lf D (X.Fu u')) := by
  obtain ⟨β, hx, hβ⟩ :=
    Formalism.L2.SG.Pf.SatGramActL.betaLift_holds D X u' (Y.what₂ u') (Y.cs u') q.1 q.2 γ.1 (kB_mem q γ)
  have e := eq_isoG hx
  subst e
  exact ⟨hx, hβ⟩


variable (Y) in
def act (q : {Λ // Λ ∈ Y.what₂ u'}) (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) (t : PackageTie2.TT Y u u') : PackageTie2.TT Y u u' :=
  Formalism.L2.SG.Pf.SatGramActR.tmap (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1)
    Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y q γ).1 t

theorem toTerm_act (q : {Λ // Λ ∈ Y.what₂ u'}) (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) (t : PackageTie2.TT Y u u') :
    (act Y q γ t).toTerm = t.toTerm :=
  Formalism.L2.SG.Pf.SatGramActR.toTerm_tmap _ _ _ _ t

theorem iota_act (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC) (q : {Λ // Λ ∈ Y.what₂ u'})
    (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) (t : PackageTie2.TT Y u u') (ht : t.lam' = q.1) :
    iotaOf Y.TR (Y.cs u) (Y.cs u') (act Y q γ t) =
      iotaOf Y.TR (Y.cs u) (Y.cs u') t * (levi Y.TR (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') q.1 γ.1))⁻¹ := by
  have hβt : Formalism.L2.SG.Pf.Act.isoG γ.1 ∈ Formalism.L2.SG.Saturated.AutF t.lam' (lf D (X.Fu u')) := by
    rw [ht]; exact (isoG_lift Y q γ).2
  have hkt : Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1 ∈ X.B.I.Kset := by
    rw [ht]; exact kB_mem q γ
  unfold act
  rw [Formalism.L2.SG.Pf.SatGramRep.iotaOf_of_mk (hIR D X Y u u') (Formalism.L2.SG.Pf.SatGramActR.tmap (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1) Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y q γ).1 t)
    (Formalism.L2.SG.Pf.SatGramActR.rmul (γ.1 : X.B.I.GA) _ (isoG_lift Y q γ).1 hβt t.rep)
    (Formalism.L2.SG.Pf.SatGramActR.tmap_cls _ _ _ _ t hβt)]
  rw [Formalism.L2.SG.Pf.SatGramRep.iotaOf_of_mk (hIR D X Y u u') t t.rep (Quot.out_eq t.cls).symm]
  have e2 : ((((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((γ.1 : X.B.I.GA)⁻¹).2 *
      (((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')) =
      (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1)⁻¹ := by
    have eg : (γ.1 : X.B.I.GA).2 = (iotaF X u' γ.1 : X.B.I.Gf) := rfl
    rw [Prod.snd_inv, eg]
    unfold Formalism.L2.SG.Pf.SatGramActL.kB
    group
  have hG1 : Good X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
      ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.rep.1.1) :=
    Formalism.L2.SG.Closed.AdmPar_holds (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') t
  have hG2 : Good X (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1) :=
    Formalism.L2.SG.Pf.SatGramActL.satGramActLIota_kB_good (Y.cs u') t.lam' γ.1 hkt
  show levi Y.TR (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
      ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) (t.rep.1.1 * (γ.1 : X.B.I.GA)⁻¹)) = _
  rw [Formalism.L2.SG.Pf.SatGramActR.kOf_mul_right, e2, levi_mul Y.TR hG1 (good_inv X hG2), levi_inv Y.TR hG2]
  have hq2 : Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1 = Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') q.1 γ.1 := by
    rw [ht]
  rw [hq2]

theorem amp_act (hB : Formalism.L2.SG.Pf.SatGramActL.ChiNBiAll) (hAR : Formalism.L2.SG.Pf.SatGramRep.AmpRepNC)
    (hOI : OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (q : {Λ // Λ ∈ Y.what₂ u'})
    (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) (t : PackageTie2.TT Y u u') (ht : t.lam' = q.1) :
    amp Y (act Y q γ t) = (amp Y t).comp (X.piU u' ((γ.1 : X.B.I.GA).1)⁻¹) := by
  have hβt : Formalism.L2.SG.Pf.Act.isoG γ.1 ∈ Formalism.L2.SG.Saturated.AutF t.lam' (lf D (X.Fu u')) := by
    rw [ht]; exact (isoG_lift Y q γ).2
  have hkt : Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1 ∈ X.B.I.Kset := by
    rw [ht]; exact kB_mem q γ
  have hF := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u'
  have hft := Formalism.L2.SG.Pf.SatGramActL.fundOf_spec hF t
  have hΩ : IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') t.lam t.lam'
      (Formalism.L2.SG.Pf.SatGramActR.rmul (γ.1 : X.B.I.GA) _ (isoG_lift Y q γ).1 hβt t.rep).1.2) (FundOf t) := by
    have e := Formalism.L2.SG.Pf.SatGramActR.roset_mul_aut (X := X) (F0 := X.Fu u) (Λ := t.lam) hβt t.rep.1.2
    convert hft using 2
    exact e
  show ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (act Y q γ t) =
    (ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t).comp (X.piU u' ((γ.1 : X.B.I.GA).1)⁻¹)
  unfold act
  rw [Formalism.L2.SG.Pf.SatGramRep.ampN_of_mk (Y.FN u) (Y.FN u') (hAR D X Y u u') hF hOI (Formalism.L2.SG.Pf.SatGramActR.tmap (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1) Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y q γ).1 t)
    (Formalism.L2.SG.Pf.SatGramActR.rmul (γ.1 : X.B.I.GA) _ (isoG_lift Y q γ).1 hβt t.rep)
    (Formalism.L2.SG.Pf.SatGramActR.tmap_cls _ _ _ _ t hβt) (FundOf t) hΩ]
  rw [Formalism.L2.SG.Pf.SatGramRep.ampN_of_mk (Y.FN u) (Y.FN u') (hAR D X Y u u') hF hOI t t.rep
    (Quot.out_eq t.cls).symm (FundOf t) hft]
  have e2 : ((((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((γ.1 : X.B.I.GA)⁻¹).2 *
      (((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')) =
      (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1)⁻¹ := by
    have eg : (γ.1 : X.B.I.GA).2 = (iotaF X u' γ.1 : X.B.I.Gf) := rfl
    rw [Prod.snd_inv, eg]
    unfold Formalism.L2.SG.Pf.SatGramActL.kB
    group
  have hκ := Formalism.L2.SG.Pf.SatGramActL.ChiLeft.kBB_mem Y u u' t.mem t.mem' t.rep
  have eχ : chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
      ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) (t.rep.1.1 * (γ.1 : X.B.I.GA)⁻¹)) =
      chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
        ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.rep.1.1) := by
    rw [Formalism.L2.SG.Pf.SatGramActR.kOf_mul_right, e2]
    exact Formalism.L2.SG.Pf.SatGramActR.chiNR_holds hB D X u' ((Y.cs u').h ((Y.cs u').base t.lam')) γ.1 _ hκ hkt
  show ((scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) •
      (chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
        ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) (t.rep.1.1 * (γ.1 : X.B.I.GA)⁻¹)) •
        (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
         OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf t) (X.Wu u) (X.Wu u')
          (t.rep.1.1.1 * ((γ.1 : X.B.I.GA).1)⁻¹))) = _
  rw [eχ, Formalism.L2.SG.Pf.SatGramActR.ooR_holds D X u u' γ.1 (FundOf t) t.rep.1.1.1]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_comp]

theorem fib_gam (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) {s s' : PackageTie2.TT Y u u'} (h : s.toTerm = s'.toTerm) :
    ∃ γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') ⟨s.lam', s.mem'⟩, s' = act Y ⟨s.lam', s.mem'⟩ γ s := by
  obtain ⟨c, hc, hg, hfix, n, hn, ν, hν, he⟩ := Formalism.L2.SG.Pf.FibreCounting.fib_c h
  have hst := Formalism.L2.SG.Pf.FibreCounting.stabF_of_fix (X.Fu u') hc hfix
  obtain ⟨g, hgq⟩ := (Formalism.L2.SG.Pf.Act.gamL_autLz_bij (Y.cs u') Y.hK hN ⟨s.lam', s.mem'⟩).2
    ⟨Formalism.L2.SG.Pf.Act.indW c hst, Formalism.L2.SG.Pf.Act.indW_mem s.lam' c hst hg⟩
  have hW : (Formalism.L2.SG.Pf.Act.indW (Formalism.L2.SG.Pf.Act.isoG g.1) (Formalism.L2.SG.Pf.Act.isoG_stab g.1) :
      Formalism.MainNotions.S.WbQ D (X.Fu u') → Formalism.MainNotions.S.WbQ D (X.Fu u')) = Formalism.L2.SG.Pf.Act.indW c hst :=
    congrArg Subtype.val hgq
  have hq : ∀ y ∈ perpS (VS D) (X.Fu u').X, c y - Formalism.L2.SG.Pf.Act.isoG g.1 y ∈ (X.Fu u').X := by
    intro y hy
    have e := congrFun hW.symm (Submodule.Quotient.mk ⟨y, hy⟩)
    rw [Formalism.L2.SG.Pf.Act.indW_mk, Formalism.L2.SG.Pf.Act.indW_mk, Submodule.Quotient.eq] at e
    simpa using e
  have hfixg : ∀ a, Formalism.L2.SG.Pf.Act.isoG g.1 ((X.Fu u').fvec a) = (X.Fu u').fvec a := by
    intro a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [FlagG.fvec, Fin.snoc_last]
      rw [X.flagZVector u']
      exact Formalism.L2.SG.Pf.Act.isoG_fix g.1 _ (Or.inr rfl)
    · simp only [FlagG.fvec, Fin.snoc_castSucc]
      rw [X.Fu_e u']
      exact Formalism.L2.SG.Pf.Act.isoG_e g.1 i
  have hA : IsAutLam (VS D) s.lam' c := ⟨hc, hg⟩
  have hA' : IsAutLam (VS D) s.lam' (Formalism.L2.SG.Pf.Act.isoG g.1) :=
    ⟨(Formalism.L2.SG.Pf.Act.isoG_stab g.1).1, Formalism.L2.SG.Pf.Act.isoG_lat (Y.cs u') ⟨s.lam', s.mem'⟩ g⟩
  have hm := Formalism.L2.SG.Pf.FibreCounting.nlam_of_sub (X.Fu u') hA hA' hfix hfixg hq

  have hkinv : colD ((Y.cs u').h ((Y.cs u').base s.lam')) (iotaF X u' g.1⁻¹ * (Y.cs u').h ((Y.cs u').base s.lam'))
      ∈ X.B.I.Kset := by
    rw [← Formalism.L2.SG.Pf.Act.aK_eq]
    have h1 := K_inv X.B.I (kB_mem (Y := Y) ⟨s.lam', s.mem'⟩ g)
    unfold Formalism.L2.SG.Pf.SatGramActL.kB at h1
    rw [map_inv]
    convert h1 using 1
    push_cast
    group
  let γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') ⟨s.lam', s.mem'⟩ := ⟨g.1⁻¹, hkinv⟩
  have hxg := (isoG_lift Y ⟨s.lam', s.mem'⟩ g).1
  have hxi : RatLink X (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG g.1)⁻¹ := by
    have := Formalism.L2.SG.Pf.ratLink_inv X hxg
    simpa [γ] using this
  have hiso : Formalism.L2.SG.Pf.Act.isoG γ.1 = (Formalism.L2.SG.Pf.Act.isoG g.1)⁻¹ := (eq_isoG hxi).symm
  refine ⟨γ, ?_⟩
  have hl : s.lam = s'.lam := (Formalism.L2.SG.Pf.FibreCounting.fib_dec h).1
  have hl' : s.lam' = s'.lam' := Formalism.L2.SG.Pf.FibreCounting.lam'_eq h
  have hβt : Formalism.L2.SG.Pf.Act.isoG γ.1 ∈ Formalism.L2.SG.Saturated.AutF s.lam' (lf D (X.Fu u')) :=
    (isoG_lift Y ⟨s.lam', s.mem'⟩ γ).2
  have hcls := Formalism.L2.SG.Pf.SatGramActR.tmap_cls (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1)
    Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y ⟨s.lam', s.mem'⟩ γ).1 s hβt

  set G := Formalism.L2.SG.Pf.Act.isoG g.1 with hG
  have hGA : G⁻¹ ∈ Formalism.L2.SG.Saturated.AutF s.lam' (lf D (X.Fu u')) := by rw [← hiso]; exact hβt
  have hν2 : G⁻¹ * ν * G⁻¹⁻¹ ∈ NLam s.lam' (lf D (X.Fu u')) :=
    Formalism.L2.SG.Pf.SatGramActL.nlam_conj hGA hν
  have hν3 : (G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹ ∈ NLam s.lam' (lf D (X.Fu u')) :=
    Formalism.L2.SG.Pf.nlamPf_mul hν2 (Formalism.L2.SG.Pf.nlamPf_inv hm)
  rcases s' with ⟨k, hk, k', hk', q'⟩
  simp only at hl hl' he
  subst hl hl'
  show (⟨s.lam, hk, s.lam', hk', q'⟩ : PackageTie2.TT Y u u') =
    ⟨s.lam, s.mem, s.lam', s.mem', (Formalism.L2.SG.Pf.SatGramActR.tmap (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1)
      Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y ⟨s.lam', s.mem'⟩ γ).1 s).cls⟩
  rw [hcls]
  congr 1
  rw [← Quot.out_eq q']
  refine (Quot.sound ⟨n, hn, (G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹, hν3, ?_⟩).symm
  show GTerm.lin (⟨s.lam, hk, s.lam', hk', q'⟩ : PackageTie2.TT Y u u') =
    n * (GTerm.lin s * (Formalism.L2.SG.Pf.Act.isoG γ.1)⁻¹) * ((G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹)
  rw [he, hiso]
  group

end Act

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeZhatTr
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.EnergyCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)

theorem normSq_cTorBase (g : ℝ) :
    star (-(Complex.I * (g : ℂ)) / (2 * (Real.pi : ℂ))) * (-(Complex.I * (g : ℂ)) / (2 * (Real.pi : ℂ))) =
      (((g / (2 * Real.pi)) ^ 2 : ℝ) : ℂ) := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have := Real.pi_pos; exact mul_ne_zero two_ne_zero (by exact_mod_cast this.ne')
  set a : ℝ := g / (2 * Real.pi) with ha
  have hk : -(Complex.I * (g : ℂ)) / (2 * (Real.pi : ℂ)) = -Complex.I * (a : ℂ) := by
    rw [ha]; push_cast; field_simp
  rw [hk, star_mul', star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_pow]
  linear_combination (-(a : ℂ) ^ 2) * Complex.I_sq

theorem zhatTr_carrierOf (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
      Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀))) :
    (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).FromX →
    0 < (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).S.g →
    ∀ (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) (cv : Fin (D.R.rS + 1) → ℂ), cv ∈ GoodV u u' →
      RealObj.Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (Formalism.MainNotions.S.uMat g) = Matrix.diagonal cv →
      trG (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) g ∈
          Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS ∧
        Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (T ((tauE X e).symm v)).base.z (T ((tauE X e).symm v)).base.z'
          (trG (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) g) =
          Matrix.diagonal (Fin.snoc (α := fun _ => ℂ)
            (Formalism.L2.SG.Pf.Carrier.EnergyPlace.phiQ
              (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo) rfl cv).1
            (Formalism.L2.SG.Pf.Carrier.EnergyPlace.phiQ
              (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo) rfl cv).2) ∧
        Formalism.L2.SG.Pf.Carrier.EnergyPlace.phiQ
                  (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo) rfl cv ∈
          Formalism.FourierDecayAlt.JF.QDom D.R.k D.R.rS (T ((tauE X e).symm v)).base.z (T ((tauE X e).symm v)).base.z' := by
  intro hFX hg v g cv hcv hZ
  obtain ⟨hQ, hz, hz', -⟩ := hFX v
  set gg : ℕ := D.host.g 0 * D.host.g 1 with hgg
  set κ : ℂ := -(Complex.I * ((gg : ℝ) : ℂ)) / (2 * (Real.pi : ℂ)) with hκ
  have hTr : Bridge.TrHyp (PtRepPf.frU X u v) (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v))
      (fun a => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  have hTr' : Bridge.TrHyp (PtRepPf.frU X u' v) (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v))
      (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) (fun a => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  refine ⟨Bridge.delta_GV hTr (uMat_unitary g), ?_, ?_⟩
  · have hz2 : (T ((tauE X e).symm v)).base.z = Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u) := hz
    have hz2' : (T ((tauE X e).symm v)).base.z' = Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u') := hz'
    rw [hz2, hz2']
    have h1 := Bridge.zhat_cs hTr hTr' (sc := 1) one_ne_zero (Formalism.MainNotions.S.uMat g)
    have h1' : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u))
        (Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u'))
        (trG (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) g) =
        Matrix.diagonal (fun a => star (Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) 1 a)) *
          RealObj.Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (Formalism.MainNotions.S.uMat g) *
          Matrix.diagonal (Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) 1) := h1
    rw [h1', hZ, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    show _ = Matrix.diagonal (Fin.snoc (α := fun _ : Fin (D.R.rS + 1) => ℂ)
      (fun a : Fin D.R.rS => ((((gg : ℝ) / (2 * Real.pi)) ^ (2 * (D.R.rS - a.val)) : ℝ) : ℂ) * cv ⟨a.val, by omega⟩)
      (cv ⟨D.R.rS, by omega⟩))
    congr 1
    funext a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [Fin.snoc_last, Bridge.lam_last, star_one, one_mul, mul_one]
      rfl
    · rw [Fin.snoc_castSucc]
      have hl : Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) 1 (Fin.castSucc i) = κ ^ (D.R.rS - i.val) := by
        unfold Bridge.lam
        rw [dite_eq_left (show ((Fin.castSucc i : Fin (D.R.rS + 1)) : ℕ) < D.R.rS from i.2)]
        simp [cTor, hκ]
      rw [hl, star_pow]
      have hcv' : cv (Fin.castSucc i) = cv ⟨i.val, by omega⟩ := rfl
      rw [hcv', show (star κ) ^ (D.R.rS - i.val) * cv ⟨i.val, by omega⟩ * κ ^ (D.R.rS - i.val) =
        (star κ * κ) ^ (D.R.rS - i.val) * cv ⟨i.val, by omega⟩ by ring, hκ, normSq_cTorBase, ← Complex.ofReal_pow,
        ← pow_mul]
  · have hg0 : (0 : ℝ) < gg := by exact_mod_cast hg
    refine ⟨fun a => ?_, ?_⟩
    · show ((((gg : ℝ) / (2 * Real.pi)) ^ (2 * (D.R.rS - a.val)) : ℝ) : ℂ) * cv ⟨a.val, by omega⟩ ≠ 0
      refine mul_ne_zero ?_ (hcv.1 _)
      have : (0 : ℝ) < (gg : ℝ) / (2 * Real.pi) := div_pos hg0 (by positivity)
      exact_mod_cast (pow_pos this _).ne'
    · rw [(hT _).1, (hT _).2]
      show ((D.mem u).A.T : ℝ) * ((D.mem u').A.T : ℝ) < Complex.normSq (cv ⟨D.R.rS, by omega⟩)
      have hG := hcv.2
      unfold Gv at hG
      rw [Dl_diagonal cv _ le_rfl, Dl_diagonal cv _ (Nat.le_succ _),
        Formalism.L2.SG.Pf.CarrierTop.prod_castLE_succ cv, norm_mul] at hG
      have hP : 0 < ‖∏ i : Fin D.R.rS, cv (Fin.castLE (Nat.le_succ D.R.rS) i)‖ :=
        norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hcv.1 _)
      have hlast : cv (Fin.last D.R.rS) = cv ⟨D.R.rS, by omega⟩ := rfl
      rw [hlast] at hG
      rw [Complex.normSq_eq_norm_sq]
      unfold Tw at hG
      nlinarith [sq_nonneg ‖∏ i : Fin D.R.rS, cv (Fin.castLE (Nat.le_succ D.R.rS) i)‖]

end Formalism.L2.SG.Pf.Carrier
end
end
