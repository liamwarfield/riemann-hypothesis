module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnifOfRead
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoAtChosen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatSmallGenStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpAlgAlt
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
def ExpAlgAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f, rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ (n : ℕ) (a : Fin n → NX.KB p.Sx ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w))
        (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
        p.nexp.eF ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) (Nat.le_add_left _ _) j.2 f =
          ∑ k, a k ⊗ₜ[p.Sx.Ks] g k ∧
        ∀ k, IsAlgebraic ℚ (ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (a k))
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpAlgOfSerAlg
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
def SerAlgAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
      ∃ (n : ℕ) (z : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)), (∀ k, IsAlgebraic ℚ (z k)) ∧
        ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, z k • evW p.nexp p.v₀ j (g k).val
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem expAlg_of_serAlg_alt (hS : _root_.GlobalTheory.BigOn.Exp.SerAlgAlt) : _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt := by
  unfold _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt _root_.GlobalTheory.BigOn.Exp.SerAlgAlt _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine hS.imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP f hf => ?_⟩
  obtain ⟨n, z, g, hz, hsum⟩ := hx0 x hx hle i p hp hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hp.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  refine exists_algExp p.nexp p.v₀ hρ _ j _ hU hW (Z.vec j) hK _ z g hz ?_
  rw [← hsum, ← hf]
  exact (smul_inv_smul₀ hN.1 _).symm
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
def SerRefAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∃ ν₀ : ℂ, IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν₀ ∧ RatBase (rdAt p w j hρ ν₀) ∧
    ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
      P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
        ∃ (n : ℕ) (z : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)), (∀ k, IsAlgebraic ℚ (z k)) ∧
          ν₀ • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, z k • evW p.nexp p.v₀ j (g k).val
theorem serAlg_of_serRef_scaleRoot (hR : _root_.GlobalTheory.BigOn.Exp.SerRefAlt) (hS : _root_.GlobalTheory.BigOn.Exp.ScaleRootAltBis) : _root_.GlobalTheory.BigOn.Exp.SerAlgAlt := by
  unfold _root_.GlobalTheory.BigOn.Exp.SerAlgAlt _root_.GlobalTheory.BigOn.Exp.SerRefAlt _root_.GlobalTheory.BigOn.Exp.ScaleRootAltBis _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine (Formalism.MainNotions.Closed.and hR hS).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h.1.and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP => ?_⟩
  obtain ⟨a1, a2⟩ := hx0 x hx hle i p hp
  obtain ⟨ν₀, hN₀, hR₀, hexp⟩ := a1 hm w hw j ρ hρ ν hpin hN hR0
  obtain ⟨n, z, g, hz, hsum⟩ := hexp s h P hd hP
  by_cases hθ : ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = 0
  · refine ⟨0, Fin.elim0, Fin.elim0, fun k => Fin.elim0 k, ?_⟩
    rw [hθ, smul_zero, Finset.univ_eq_empty, Finset.sum_empty]
  · obtain ⟨m, hm0, hpow⟩ := a2 hm w hw j ρ ρ hρ hρ ν₀ ν hpin hpin ⟨rfl, rfl, rfl, rfl, rfl⟩ hN₀ hN hR₀ hR0 s h P hd hP hθ
    have h0 : ν₀ ≠ 0 := hN₀.1
    have hζ : (ν / ν₀) ^ m = 1 := by rw [div_pow, hpow, div_self (pow_ne_zero _ h0)]
    refine ⟨n, fun k => ν / ν₀ * z k, g, fun k => ?_, ?_⟩
    · have hmem : ∀ y : ℂ, y ∈ algebraicClosure ℚ ℂ ↔ IsAlgebraic ℚ y := fun y => mem_algebraicClosure_iff
      exact (hmem _).1 (mul_mem ((hmem _).2 (isAlgebraic_of_pow_eq_one hm0 hζ)) ((hmem _).2 (hz k)))
    · conv_lhs => rw [← div_mul_cancel₀ ν h0]
      rw [mul_smul, hsum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul]
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScaleRootOfPrint
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScaleRootOfPrint
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
theorem scaleRoot_of_hypothesis_alt (_ : GlobalTheory.Published.CuspRapidDecay) (_ : GlobalTheory.Published.GlobalArtinReciprocity) (_ : GlobalTheory.Published.RayClassFieldSt)
    (_ : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat) : _root_.GlobalTheory.BigOn.Exp.ScaleRootAltBis := by
  unfold _root_.GlobalTheory.BigOn.Exp.ScaleRootAltBis _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  refine ⟨0, fun x hx _ i p _ _ w _ j ρ ρ' hρ hρ' ν ν' _ _ hSB hN hN' _ _ s h P _ _ _ => ?_⟩
  obtain ⟨-, c, hc, n, hn, hνn⟩ := hN
  obtain ⟨-, c', hc', m, hm, hν'm⟩ := hN'
  rw [hSB.2.2.2.1] at hc'
  obtain ⟨k, hk, hkk⟩ := isScale_pow_eq p.R p.v₀ _ hc hc'
  refine ⟨n * m * k, Nat.mul_ne_zero (Nat.mul_ne_zero hn hm) hk, ?_⟩
  have e1 : ν' ^ (n * m * k) = (ν' ^ m) ^ (n * k) := by rw [← pow_mul]; ring_nf
  have e2 : ν ^ (n * m * k) = (ν ^ n) ^ (m * k) := by rw [← pow_mul]; ring_nf
  have e3 : c' ^ (n * m * k) = c ^ (n * m * k) := by
    rw [show n * m * k = k * (n * m) by ring, pow_mul c', pow_mul c, hkk]
  rw [e1, e2, hν'm, hνn, ← pow_mul, ← pow_mul, mul_pow, mul_pow,
    show m * (n * k) = n * m * k by ring, show n * (m * k) = n * m * k by ring, e3]
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScaleRootOfPrintStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scale_root_of_reciprocity_inputs : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.ScaleRootAltBis := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.scaleRoot_of_hypothesis_alt | exact _root_.GlobalTheory.BigOn.Exp.scaleRoot_of_hypothesis_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.scaleRoot_of_hypothesis_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesUnit
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjRoot
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpConj
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpOneLevel
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormSmulTheta
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
section CorePart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open GlobalTheory.SeriesTie GlobalTheory.SeriesTie.BaseRat GlobalTheory.BigOn.Exp
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
namespace GlobalTheory.SerSmall
variable {D : D7}
section Comb
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  (j : Fin D.R.m)
variable {YS v₀ j}
end Comb
section Main
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
end Main
end GlobalTheory.SerSmall
end CorePart
section PointPart
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
namespace GlobalTheory.SerSmall
section Core
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
end Core
section Level
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}
end Level
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt
set_option maxHeartbeats 3200000 in
theorem fw_eq_zero_or_exists_norm_algComb (hP : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hRF : GlobalTheory.Published.RayClassFieldSt)
    (hS : GlobalTheory.SerStd.SeriesRatS) {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (hR : p.PointConditions')
    (hM : More p) (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m) (h0 : RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j)
    (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (b : Bool) (h : RealPin p.R p.cG ρ)
    (hχ : ∀ q, (((ρ.B t j b).G.P.chi q : ℂˣ) : ℂ) ∈ (Formalism.L2.Host.embLL0 (Fm.D x i)).fieldRange) :
    (∀ y ∈ (p.R.FW j).WK, y = 0) ∨ ∃ ν, IsNorm p.R p.v₀ (ρ.B t j b) ν ∧ ∀ s g P, ρ.IsDatum t j b s g P →
      P ∈ ρ.lat t j b (smallInt (Fm.D x i)) g → SmallComb p.nexp p.v₀ j (ν • ρ.theta t j b g P) := by
  obtain ⟨c', w, hw, hfr, B', hv⟩ := exists_framed_half hP h0.size (GlobalTheory.Core5.of_core h0.core) (geoHalf p) h0.unif
    (_root_.GlobalTheory.UnframePt.inGeo_geoHalf_of_ratHyp0 hP Fm x hx i p hR hM t j h0)
  letI iA : Algebra (setCE p.T c').Q.c.F (Fm.D x i).what₂.LL := p.alg
  have hV' : (setCE p.T c').V ((j : ℕ) + 1) (setCE p.T c').σ₀ = Wc (Fm.D x i) j :=
    B'.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ (setCE p.T c').toCore.good_σ₀
  have hU' : (fullHeckeRealDatMovedReadings p.R w).toRealDat.LUnif := GlobalTheory.T.uniformisationLaws_centralMovedReadings p.R.toRealDat w hw h0.unif
  have hG : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsGrp (F2 p) :=
    ⟨h0.core.grp.red_R, h0.core.grp.red_L, h0.core.grp.levels, h0.core.grp.record, h0.core.grp.chiW⟩
  have c := h0.core
  have hF : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsFam := { c.fam with }
  have hMo : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsModels := { c.models with }
  have hCh : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsChain := { c.chain with }
  have hTh : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsThP := { c.thP with }
  have hC : GlobalTheory.Hk3.Core (fullHeckeRealDatMovedReadings p.R w).toRealDat (F2 p) := ⟨c.lev, hG, hF, hMo, hCh, hTh⟩
  have hph : (fun k => cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) ((fullHeckeRealDatMovedReadings p.R w).phs k)) = fun _ => (1 : ℂ) :=
    funext fun k => by
      show cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) (p.R.phs k) = 1
      rw [p.phsOne k, map_one]
  have hRat : RatHyp (setCE p.T c') (fullHeckeRealDatMovedReadings p.R w) (F2 p) B'.κ B'.v₀ B'.O t j hV' := by
    refine ⟨h0.size, h0.host, h0.std, B'.fw.laws, hC, hU', ⟨B'.fw⟩,
      ⟨B'.fw.laws, B'.fw.alg_eq, B'.fw.kap, B'.fw.hv₀, B'.fw.chiR, B'.fw.x0⟩, h0.io, h0.guard, h0.fin, B'.pins j, ?_,
      hfr j hV', h0.galois, h0.small, h0.inUse, h0.low⟩
    rw [hph]
    exact B'.phase j hU'
  have hpin' : RealPin (fullHeckeRealDatMovedReadings p.R w) p.cG ρ :=
    ⟨h.psi, h.inf, h.cartT, h.onbS, h.onbT, h.latS, h.latT, h.frS, h.frT, h.vac, h.Pg, h.grp, h.mu0, h.eta, h.delta, h.deltaPl,
      h.ap, h.am⟩
  have hsp : (Fm.D x i).host.cls (Fm.D x i).host.pde = PrimeClass.splitK ∧
      (Fm.D x i).host.cls (Fm.D x i).host.pde' = PrimeClass.splitK :=
    ⟨(Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.1, (Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.2⟩
  have H := core_cases (T := setCE p.T c') (Rl := fullHeckeRealDatMovedReadings p.R w) hA hRF hS (GlobalTheory.UnframeForms.movedYS p.nexp w) hρ b hpin' hRat hsp hχ
  rw [hv] at H
  rcases H with H | ⟨ν, hN, H⟩
  · exact Or.inl H
  · exact Or.inr ⟨ν, hN, fun s g P hd hl => smallComb_of_moved p.nexp w p.v₀ j (H s g P hd hl)⟩
theorem norm_smul_theta_alt (hP : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hRF : GlobalTheory.Published.RayClassFieldSt)
    (hS : GlobalTheory.SerStd.SeriesRatS) : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ ν' : ℂ, IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
    ∃ (a : ℂ) (φ : GA (Fm.D x i) (Wc (Fm.D x i) j) → ℂ), (∃ m : ℕ, m ≠ 0 ∧ a ^ m = 1) ∧ SmallComb p.nexp p.v₀ j φ ∧
      ν' • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = a • φ := by
  have hL := _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt
  have hT := _root_.GlobalTheory.BigOn.Exp.twAdm_alt
  unfold _root_.GlobalTheory.BigOn.Exp.LowerBoundAtPlace at hL
  unfold _root_.GlobalTheory.BigOn.Exp.TwAdmAlt at hT
  refine (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hL hT).imp fun Fm x hx i p hp hM w _ j h => ?_
  intro ρ hρ ν hpin hlev hR0 s g P hd hl ν' hN
  rcases _root_.GlobalTheory.SerSmall.fw_eq_zero_or_exists_norm_algComb hP hA hRF hS Fm x hx i p hp hM _ j
    (_root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt Fm x hx i p hp hM _ h.2.2.2 h.1 j) ρ hρ _ hpin (chi_mem_small hM.2.2 hρ hlev _ j _) with H | ⟨ν₁, hN₁, H⟩
  · have h0 := GlobalTheory.SerRefPt.theta_eq_zero p.nexp p.v₀ hρ _ j _ H hR0 hd
    exact ⟨1, 0, ⟨1, one_ne_zero, one_pow 1⟩, SmallComb.zero, by rw [h0, smul_zero, smul_zero]⟩
  · obtain ⟨ζ, hζ, e⟩ := exists_root_of_isNorm p.R p.v₀ _ hN₁ hN
    exact ⟨ζ, _, hζ, H s g P hd hl, by rw [e, mul_smul]⟩
theorem one_expansion_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
      ∃ c : ℂ, (∃ m : ℕ, m ≠ 0 ∧ c ^ m = 1) ∧
        ∃ (n : ℕ) (b : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
          ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, b k • evW p.nexp p.v₀ j (g k).val ∧
          ∑ k, τ (b k) • evW p.nexp p.v₀ j (g k).val =
            c • (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P) := by
  intro hP hA hRF hS
  refine (_root_.GlobalTheory.SerSmall.norm_smul_theta_alt hP hA hRF hS).imp fun Fm x hx i p _ _ w _ j H => ?_
  intro ρ hρ ν hpin hlev hN hR0 s h P hd hl τ hτ
  obtain ⟨a, φ, ⟨m, hm, ha⟩, ⟨n, z, g, hz, rfl⟩, e⟩ := H ρ hρ ν hpin hlev hR0 s h P hd hl ν hN
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at ha
    exact zero_ne_one ha
  have hz' : ∀ k, τ (z k) = z k := fun k => by
    obtain ⟨y, hy⟩ := hz k
    rw [← hy]
    exact hτ y
  refine ⟨τ a / a, ⟨m, hm, by rw [div_pow, ← map_pow, ha, map_one, div_one]⟩, n, fun k => a * z k, g, ?_, ?_⟩
  · rw [e, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_smul _ _ _
  · rw [e, smul_smul, div_mul_cancel₀ _ ha0, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul, hz', smul_smul]
end GlobalTheory.SerSmall
end PointPart
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpOneLevel
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
theorem expOne_level_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
      ∃ c : ℂ, (∃ m : ℕ, m ≠ 0 ∧ c ^ m = 1) ∧
        ∃ (n : ℕ) (b : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
          ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, b k • evW p.nexp p.v₀ j (g k).val ∧
          ∑ k, τ (b k) • evW p.nexp p.v₀ j (g k).val =
            c • (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P) :=
  _root_.GlobalTheory.SerSmall.one_expansion_alt
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpOneLevelStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_datum_normalized_rational_base_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
      ∃ c : ℂ, (∃ m : ℕ, m ≠ 0 ∧ c ^ m = 1) ∧
        ∃ (n : ℕ) (b : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
          ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, b k • evW p.nexp p.v₀ j (g k).val ∧
          ∑ k, τ (b k) • evW p.nexp p.v₀ j (g k).val =
            c • (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P) := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.expOne_level_alt | exact _root_.GlobalTheory.BigOn.Exp.expOne_level_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.expOne_level_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpZero
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
def ExpZeroAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p _ j => ∀ τ : ℂ ≃+* ℂ,
  (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
  ∀ (n : ℕ) (c : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
    ∑ k, c k • evW p.nexp p.v₀ j (g k).val = 0 → ∑ k, τ (c k) • evW p.nexp p.v₀ j (g k).val = 0
theorem bigOn_expZero : _root_.GlobalTheory.BigOn.Exp.ExpZeroAlt := by
  unfold _root_.GlobalTheory.BigOn.Exp.ExpZeroAlt _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, fun x hx _ i p hr hm w _ j τ hτ n c g h0 => ?_⟩⟩⟩
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  exact conj_sum_zero _ _ _ _ _ _ _ _ _ _ p.nexp p.v₀ j hU hW (Z.vec j) hK τ hτ n c g h0
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpConj
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.BigOn.Exp
theorem expConj_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f, rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∀ (n : ℕ) (a : Fin n → NX.KB p.Sx ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w))
        (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
        p.nexp.eF ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) (Nat.le_add_left _ _) j.2 f =
          ∑ k, a k ⊗ₜ[p.Sx.Ks] g k →
      ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
        ∃ c : ℂ, (∃ m : ℕ, m ≠ 0 ∧ c ^ m = 1) ∧
          ∑ k, τ (ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (a k)) • evW p.nexp p.v₀ j (g k).val =
            c • ∑ k, ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (a k) • evW p.nexp p.v₀ j (g k).val := by
  intro h1 h2 h3 h4
  have hO := _root_.GlobalTheory.T.real_datum_normalized_rational_base_alt h1 h2 h3 h4
  have hZ := _root_.GlobalTheory.BigOn.Exp.bigOn_expZero
  unfold _root_.GlobalTheory.BigOn.Exp.ExpZeroAlt at hZ
  refine (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hO hZ).imp fun Fm x hx i p _ _ w _ j H => ?_
  intro ρ hρ ν hpin hL hN hR0 s h P hd hP f hf n a g hfe τ hfix
  obtain ⟨a1, a2⟩ := H
  obtain ⟨c, hc, n', b, g', hb, hbc⟩ := a1 ρ hρ ν hpin hL hN hR0 s h P hd hP τ hfix
  have hν : ν ≠ 0 := hN.1
  have hsum : ∑ k, ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (a k) • evW p.nexp p.v₀ j (g k).val =
      ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P := by
    rw [← hf]
    change _ = ν • ν⁻¹ • evK p.nexp p.v₀ hρ _ j _ (p.nexp.eF _ _ _ (Nat.le_add_left _ _) j.2 f)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [smul_inv_smul₀ hν, hfe, map_sum]
    rfl
  have h0 := a2 τ hfix (n + n')
    (Fin.append (fun k => ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (a k)) (fun k => -b k))
    (Fin.append g g') (by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, neg_smul, Finset.sum_neg_distrib]
      rw [hsum, hb, add_neg_cancel])
  rw [Fin.sum_univ_add] at h0
  simp only [Fin.append_left, Fin.append_right, map_neg, neg_smul, Finset.sum_neg_distrib] at h0
  refine ⟨c, hc, ?_⟩
  rw [hsum, ← hbc]
  exact add_neg_eq_zero.1 h0
end GlobalTheory.BigOn.Exp
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpConjStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_datum_rational_normalization_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f, rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∀ (n : ℕ) (a : Fin n → NX.KB p.Sx ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w))
        (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
        p.nexp.eF ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) (Nat.le_add_left _ _) j.2 f =
          ∑ k, a k ⊗ₜ[p.Sx.Ks] g k →
      ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
        ∃ c : ℂ, (∃ m : ℕ, m ≠ 0 ∧ c ^ m = 1) ∧
          ∑ k, τ (ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (a k)) • evW p.nexp p.v₀ j (g k).val =
            c • ∑ k, ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (a k) • evW p.nexp p.v₀ j (g k).val := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.expConj_alt | exact _root_.GlobalTheory.BigOn.Exp.expConj_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.expConj_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpAlgStatement
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpAlgAltAlt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointCases
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointCases
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.SerRefCore
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SerRefPt
section Core
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
end Core
end GlobalTheory.SerRefPt
namespace GlobalTheory.SerRefPt
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt
set_option maxHeartbeats 3200000 in
theorem fw_eq_zero_or_exists_norm_algComb (hP : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hRF : GlobalTheory.Published.RayClassFieldSt)
    (hS : GlobalTheory.SerStd.SeriesRatS) {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (hR : p.PointConditions')
    (hM : More p) (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m) (h0 : RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j)
    (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (b : Bool) (h : RealPin p.R p.cG ρ) :
    (∀ y ∈ (p.R.FW j).WK, y = 0) ∨ ∃ ν, IsNorm p.R p.v₀ (ρ.B t j b) ν ∧ ∀ s g P, ρ.IsDatum t j b s g P →
      P ∈ ρ.lat t j b (smallInt (Fm.D x i)) g → AlgComb p.nexp p.v₀ j (ν • ρ.theta t j b g P) := by
  obtain ⟨c', w, hw, hfr, B', hv⟩ := exists_framed_half hP h0.size (GlobalTheory.Core5.of_core h0.core) (geoHalf p) h0.unif
    (_root_.GlobalTheory.UnframePt.inGeo_geoHalf_of_ratHyp0 hP Fm x hx i p hR hM t j h0)
  letI iA : Algebra (setCE p.T c').Q.c.F (Fm.D x i).what₂.LL := p.alg
  have hV' : (setCE p.T c').V ((j : ℕ) + 1) (setCE p.T c').σ₀ = Wc (Fm.D x i) j :=
    B'.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ (setCE p.T c').toCore.good_σ₀
  have hU' : (fullHeckeRealDatMovedReadings p.R w).toRealDat.LUnif := GlobalTheory.T.uniformisationLaws_centralMovedReadings p.R.toRealDat w hw h0.unif
  have hG : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsGrp (F2 p) :=
    ⟨h0.core.grp.red_R, h0.core.grp.red_L, h0.core.grp.levels, h0.core.grp.record, h0.core.grp.chiW⟩
  have c := h0.core
  have hF : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsFam := { c.fam with }
  have hMo : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsModels := { c.models with }
  have hCh : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsChain := { c.chain with }
  have hTh : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsThP := { c.thP with }
  have hC : GlobalTheory.Hk3.Core (fullHeckeRealDatMovedReadings p.R w).toRealDat (F2 p) := ⟨c.lev, hG, hF, hMo, hCh, hTh⟩
  have hph : (fun k => cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) ((fullHeckeRealDatMovedReadings p.R w).phs k)) = fun _ => (1 : ℂ) :=
    funext fun k => by
      show cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) (p.R.phs k) = 1
      rw [p.phsOne k, map_one]
  have hRat : RatHyp (setCE p.T c') (fullHeckeRealDatMovedReadings p.R w) (F2 p) B'.κ B'.v₀ B'.O t j hV' := by
    refine ⟨h0.size, h0.host, h0.std, B'.fw.laws, hC, hU', ⟨B'.fw⟩,
      ⟨B'.fw.laws, B'.fw.alg_eq, B'.fw.kap, B'.fw.hv₀, B'.fw.chiR, B'.fw.x0⟩, h0.io, h0.guard, h0.fin, B'.pins j, ?_,
      hfr j hV', h0.galois, h0.small, h0.inUse, h0.low⟩
    rw [hph]
    exact B'.phase j hU'
  have hpin' : RealPin (fullHeckeRealDatMovedReadings p.R w) p.cG ρ :=
    ⟨h.psi, h.inf, h.cartT, h.onbS, h.onbT, h.latS, h.latT, h.frS, h.frT, h.vac, h.Pg, h.grp, h.mu0, h.eta, h.delta, h.deltaPl,
      h.ap, h.am⟩
  have hsp : (Fm.D x i).host.cls (Fm.D x i).host.pde = PrimeClass.splitK ∧
      (Fm.D x i).host.cls (Fm.D x i).host.pde' = PrimeClass.splitK :=
    ⟨(Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.1, (Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.2⟩
  have H := core_cases (T := setCE p.T c') (Rl := fullHeckeRealDatMovedReadings p.R w) hA hRF hS (GlobalTheory.UnframeForms.movedYS p.nexp w) hρ b hpin' hRat hsp
  rw [hv] at H
  rcases H with H | ⟨ν, hN, H⟩
  · exact Or.inl H
  · exact Or.inr ⟨ν, hN, fun s g P hd hl => algComb_of_moved p.nexp w p.v₀ j (H s g P hd hl)⟩
theorem serRef_of_reciprocity_ray_class : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.SerRefAlt := by
  intro hP hA hRF hS
  have hL := _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt
  have hT := _root_.GlobalTheory.BigOn.Exp.twAdm_alt
  unfold _root_.GlobalTheory.BigOn.Exp.LowerBoundAtPlace at hL
  unfold _root_.GlobalTheory.BigOn.Exp.TwAdmAlt at hT
  unfold _root_.GlobalTheory.BigOn.Exp.SerRefAlt
  refine (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hL hT).imp fun Fm x hx i p hp hM w _ j h => ?_
  intro ρ hρ ν hpin hN hR0
  refine ⟨ν, hN, hR0, fun s g P hd hl => ?_⟩
  rcases _root_.GlobalTheory.SerRefPt.fw_eq_zero_or_exists_norm_algComb hP hA hRF (GlobalTheory.SerStd.seriesRatS_of hS) Fm x hx i p hp hM _ j
    (_root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt Fm x hx i p hp hM _ h.2.2.2 h.1 j) ρ hρ _ hpin with H | ⟨ν₁, hN₁, H⟩
  · have h0 := theta_eq_zero p.nexp p.v₀ hρ _ j _ H hR0 hd
    have h1 : AlgComb p.nexp p.v₀ j (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) g P) := by
      rw [h0, smul_zero]
      exact AlgComb.zero
    exact h1
  · obtain ⟨ζ, hζ, e⟩ := exists_root_of_isNorm p.R p.v₀ _ hN₁ hN
    have h1 : AlgComb p.nexp p.v₀ j (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) g P) := by
      rw [e, mul_smul]
      exact (H s g P hd hl).smul hζ
    exact h1
end GlobalTheory.SerRefPt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointCasesStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_ref_of_decay_artin_ray_seriesRat : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.SerRefAlt := by
  first | exact @_root_.GlobalTheory.SerRefPt.serRef_of_reciprocity_ray_class | exact _root_.GlobalTheory.SerRefPt.serRef_of_reciprocity_ray_class | (intros; apply _root_.GlobalTheory.SerRefPt.serRef_of_reciprocity_ray_class <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem expAlg_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt := fun h1 h2 h3 h4 =>
  _root_.GlobalTheory.BigOn.Exp.expAlg_of_serAlg_alt (_root_.GlobalTheory.BigOn.Exp.serAlg_of_serRef_scaleRoot (_root_.GlobalTheory.T.series_ref_of_decay_artin_ray_seriesRat h1 h2 h3 h4) (_root_.GlobalTheory.T.scale_root_of_reciprocity_inputs h1 h2 h3 h4))
end GlobalTheory.BigOn.Exp
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expAlg_of_cusp_decay_and_reciprocity : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.expAlg_alt | exact _root_.GlobalTheory.BigOn.Exp.expAlg_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.expAlg_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjRoot
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
theorem conjRoot_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f, rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ c : ℂ, (∃ n : ℕ, n ≠ 0 ∧ c ^ n = 1) ∧
        rdAt p w j hρ' ν f = c • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P := by
  intro p1 p2 p3 p4
  have hA := _root_.GlobalTheory.T.expAlg_of_cusp_decay_and_reciprocity p1 p2 p3 p4
  have hB := _root_.GlobalTheory.T.real_datum_rational_normalization_alt p1 p2 p3 p4
  unfold _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt at hA
  unfold _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine (Formalism.MainNotions.Closed.and hA hB).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h.1.and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ ρ' hρ hρ' ν ν' hpin hlev hpin' hSB hN hN' hR0 hR0' s h P hd hP f hf => ?_⟩
  obtain ⟨a1, a2⟩ := hx0 x hx hle i p hp
  obtain ⟨n, a, g, hfe, halg⟩ := a1 hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP f hf
  obtain ⟨τ, hτ⟩ := exists_aut_alg (ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w))
    (ρ'.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w))
  have hfix : ∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y := by
    intro y
    have h1 := hρ.e_LL0 ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) y
    have h2 := hρ'.e_LL0 ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) y
    have hy : IsAlgebraic ℚ (Formalism.L2.Host.embLL0 (Fm.D x i) y) :=
      ((Algebra.IsAlgebraic.isAlgebraic y).algHom (Formalism.L2.Host.embLL0 (Fm.D x i)).toRatAlgHom)
    rw [← h1] at hy ⊢
    rw [hτ _ hy, h2, h1]
  obtain ⟨c, hc, hsum⟩ := a2 hm w hw j ρ hρ ν hpin hlev hN hR0 s h P hd hP f hf n a g hfe τ hfix
  refine ⟨c, hc, ?_⟩
  rw [← hf]
  have key : ∀ (ρ₀ : Setup (Fm.D x i).ntw) (hρ₀ : ρ₀.Good), rdAt p w j hρ₀ ν f =
      ν⁻¹ • ∑ k, ρ₀.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (a k) • evW p.nexp p.v₀ j (g k).val := by
    intro ρ₀ hρ₀
    change ν⁻¹ • evK p.nexp p.v₀ hρ₀ _ j _ (p.nexp.eF _ _ _ (Nat.le_add_left _ _) j.2 f) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hfe, map_sum]
    rfl
  rw [key ρ' hρ', key ρ hρ, smul_comm, ← hsum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hτ _ (halg k)]
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjRootStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_ratio_realization_same_dual_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f, rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ c : ℂ, (∃ n : ℕ, n ≠ 0 ∧ c ^ n = 1) ∧
        rdAt p w j hρ' ν f = c • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.conjRoot_alt | exact _root_.GlobalTheory.BigOn.Exp.conjRoot_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.conjRoot_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoordRange
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem coordRange_alt : _root_.GlobalTheory.BigOn.Exp.CoordinateRangeCondition := by
  unfold _root_.GlobalTheory.BigOn.Exp.CoordinateRangeCondition _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, fun x hx _ i p hr hm w _ j ρ hρ ν μ hν f f' hf hff => ?_⟩⟩⟩
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  exact exists_coord_of_indep _ _
    (GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ _ j _ ν hν hU hW (Z.vec j) hK) hf hff
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesUnit
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
namespace GlobalTheory.BigOn.Exp
theorem seriesUnit_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f f', rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      rdAt p w j hρ' ν' f' = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ u : FractionRing ((Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)), (∃ n : ℕ, n ≠ 0 ∧ u ^ n = 1) ∧ f' = u • f := by
  intro h1 h2 h3 h4
  have hI := _root_.GlobalTheory.BigOn.Exp.readInj_alt
  have hS := _root_.GlobalTheory.T.scale_root_of_reciprocity_inputs h1 h2 h3 h4
  have hC := _root_.GlobalTheory.T.norm_ratio_realization_same_dual_alt h1 h2 h3 h4
  have hR := _root_.GlobalTheory.BigOn.Exp.coordRange_alt
  unfold _root_.GlobalTheory.BigOn.Exp.ReadInjAlt at hI
  unfold _root_.GlobalTheory.BigOn.Exp.ScaleRootAltBis at hS
  unfold _root_.GlobalTheory.BigOn.Exp.CoordinateRangeCondition at hR
  unfold _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at hI hS hC hR ⊢
  refine Closed.imp (Closed.and (Closed.and (Closed.and hI hS) hC) hR) ?_
  intro eps Fm CH _ h
  obtain ⟨x0, hx0⟩ := _root_.GlobalTheory.BigTop.EventuallyAtPoints.and (_root_.GlobalTheory.BigTop.EventuallyAtPoints.and (_root_.GlobalTheory.BigTop.EventuallyAtPoints.and h.1.1.1 h.1.1.2) h.1.2) h.2
  refine ⟨x0, ?_⟩
  intro x hx hle i p hp hm w hw j ρ ρ' hρ hρ' ν ν' hpin hlev hpin' hSB hN hN' hR0 hR0' s h P hd hP f f' hf hf'
  obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := hx0 x hx hle i p hp
  have hν : ν ≠ 0 := hN.1
  have hν' : ν' ≠ 0 := hN'.1
  have inj' := a1 hm w hw j ρ' hρ' ν hν
  have inj := a1 hm w hw j ρ hρ ν hν
  by_cases hf0 : f = 0
  · subst hf0
    have h0 : rdAt p w j hρ' ν' f' = rdAt p w j hρ' ν' 0 := by
      rw [hf', ← hf, map_zero, map_zero]
    have := a1 hm w hw j ρ' hρ' ν' hν' h0
    exact ⟨1, ⟨1, one_ne_zero, one_pow 1⟩, by rw [this, smul_zero]⟩
  · have hθ : ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P ≠ 0 := by
      intro h0
      apply hf0
      apply inj
      rw [hf, h0, map_zero]
    obtain ⟨n, hn, hnn⟩ := a2 hm w hw j ρ ρ' hρ hρ' ν ν' hpin hpin' hSB hN hN' hR0 hR0' s h P hd hP hθ
    obtain ⟨c, ⟨m, hm0, hcm⟩, hc⟩ := a3 hm w hw j ρ ρ' hρ hρ' ν ν' hpin hlev hpin' hSB hN hN' hR0 hR0' s h P hd hP f hf
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow hm0] at hcm
      exact zero_ne_one hcm
    have hap := fun ν₁ g =>
      realRd_apply p.nexp p.v₀ hρ' ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ν₁ g
    have key : rdAt p w j hρ' ν f' = (ν' * ν⁻¹ * c⁻¹) • rdAt p w j hρ' ν f := by
      rw [hc, ← hf', smul_smul]
      have e1 := hap ν f'
      have e2 := hap ν' f'
      simp only [rdAt]
      rw [e1, e2, smul_smul]
      congr 1
      field_simp
    obtain ⟨u, hu⟩ := a4 hm w hw j ρ' hρ' ν _ hν f f' hf0 key
    refine ⟨u, ⟨n * m, mul_ne_zero hn hm0, ?_⟩, ?_⟩
    · apply (ρ'.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w)).injective
      rw [map_pow, map_one, hu, mul_pow, mul_pow, pow_mul ν', hnn, ← pow_mul, inv_pow, inv_pow,
        mul_inv_cancel₀ (pow_ne_zero _ hν), mul_comm n m, pow_mul c, hcm]
      simp
    · apply inj'
      rw [key, map_smulₛₗ, hu]
end GlobalTheory.BigOn.Exp
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesUnitStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_ratio_realization_same_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f f', rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      rdAt p w j hρ' ν' f' = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ u : FractionRing ((Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)), (∃ n : ℕ, n ≠ 0 ∧ u ^ n = 1) ∧ f' = u • f := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.seriesUnit_alt | exact _root_.GlobalTheory.BigOn.Exp.seriesUnit_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.seriesUnit_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)
end Point
def SeriesUnitLAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f f', rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      rdAt p w j hρ' ν' f' = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ u : FractionRing ((Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)), (∃ n : ℕ, n ≠ 0 ∧ u ^ n = 1) ∧ f' = u • f
theorem conjBase_of_readInj_latSmallGen_seriesUnit (hI : _root_.GlobalTheory.BigOn.Exp.ReadInjAlt) (hG : _root_.GlobalTheory.BigOn.Exp.LatticeHasSmallGenerators) (hU : _root_.GlobalTheory.BigOn.Exp.SeriesUnitLAlt) : _root_.GlobalTheory.BigOn.Exp.ConjugateBase := by
  unfold _root_.GlobalTheory.BigOn.Exp.ConjugateBase _root_.GlobalTheory.BigOn.Exp.ReadInjAlt _root_.GlobalTheory.BigOn.Exp.LatticeHasSmallGenerators _root_.GlobalTheory.BigOn.Exp.SeriesUnitLAlt _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine ((Formalism.MainNotions.Closed.and hI hG).and hU).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := (h.1.1.and h.1.2).and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ ρ' hρ hρ' ν ν' hpin hS hN hR hF => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3⟩ := hx0 x hx hle i p hp
  have hL : ρ.LevelOf (Fm.D x i).nexp := levelOf_of_sameBut hm.2.2 hρ' hρ hF.1.1 hpin hS.symm hF.2.2.2
  exact le_antisymm
    (baseLat_le p w j (a1 hm w hw j) (a2 hm w hw j) (a3 hm w hw j) ρ ρ' hρ hρ' ν ν' hpin hL hF.1.1 hS hN hF.2.1 hR.1 hF.2.2.1.1)
    (baseLat_le p w j (a1 hm w hw j) (a2 hm w hw j) (a3 hm w hw j) ρ' ρ hρ' hρ ν' ν hF.1.1 hF.2.2.2 hpin hS.symm hF.2.1 hN hF.2.2.1.1 hR.1)
theorem conjBase_of_cusp_decay_and_reciprocity : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.ConjugateBase := fun h1 h2 h3 h4 =>
  _root_.GlobalTheory.BigOn.Exp.conjBase_of_readInj_latSmallGen_seriesUnit _root_.GlobalTheory.BigOn.Exp.readInj_alt _root_.GlobalTheory.T.latSmallGen' (_root_.GlobalTheory.T.norm_ratio_realization_same_alt h1 h2 h3 h4)
end GlobalTheory.BigOn.Exp
end
end
