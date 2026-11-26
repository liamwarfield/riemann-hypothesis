module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.LsSetresAvgW
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetPf
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolHinfPf
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full

theorem hinfConjC_holds : HinfConjC := by
  intro D X u h hh Ω hΩ
  obtain ⟨h1, hmul, hinvN⟩ := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  let N : Subgroup X.B.I.Ginf :=
    Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.subOf (X.NinfU u) h1 (fun x hx y hy => (hmul x hx y hy).1) hinvN
  have hNc : IsClosed (N : Set X.B.I.Ginf) := Formalism.L2.SG.Pf.Vanish2.ninf_closed X.B.I X.eR (X.zR u)
  have hH : IsHaarOnSet X.B.I (N : Set X.B.I.Ginf) (X.muN u) := X.muN_haar u
  have hHa := Formalism.L2.SG.Pf.haarOnSet_isHaar_inst X.B.I N hNc (X.muN u) hH
  obtain ⟨_, h0, hc, hl⟩ := hH
  have hfin : IsFiniteMeasureOnCompacts (X.muN u) := ⟨hHa.2.1⟩
  have hconj : ∀ g ∈ Hinf X u, ∀ n ∈ X.NinfU u, g * n * g⁻¹ ∈ X.NinfU u := fun g hg n hn => by
    have hi : g⁻¹ ∈ Hinf X u := (Hinf X u).inv_mem hg
    have hfix : ∀ v, ∀ x ∈ fixSet X u, (uMat (g⁻¹ v)).mulVec (rv X.B.I v x) = rv X.B.I v x := hi
    have := Formalism.L2.SG.CovariantRepresentation.ninf_conj X u g⁻¹ (fun v a => hfix v _ (Or.inl (Or.inl ⟨a, rfl⟩)))
      (fun v => hfix v _ (Or.inr rfl)) hn
    simpa using this
  have hcont : ∀ g : X.B.I.Ginf, Continuous fun s : X.B.I.Ginf => g * s * g⁻¹ := fun g =>
    (continuous_const.mul continuous_id).mul continuous_const

  obtain ⟨K0, hK0c, hK0n⟩ := exists_compact_mem_nhds (1 : X.B.I.Ginf)
  have hK0pos : 0 < X.muN u K0 := by
    have hpos := hHa.2.2 (interior K0) isOpen_interior ⟨1, mem_interior_iff_mem_nhds.2 hK0n, h1⟩
    exact lt_of_lt_of_le hpos (measure_mono interior_subset)
  let K : Set X.B.I.Ginf :=
    (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2 * p.1⁻¹) '' ((Hinf X u : Set X.B.I.Ginf) ×ˢ K0)
  have hKc : IsCompact K :=
    ((Formalism.L2.SG.Pf.hinf_compact X u).prod hK0c).image
      ((continuous_fst.mul continuous_snd).mul continuous_fst.inv)
  have hK0K : K0 ⊆ K := fun k hk => ⟨(1, k), ⟨(Hinf X u).one_mem, hk⟩, by simp⟩
  have hKpos : 0 < X.muN u K := lt_of_lt_of_le hK0pos (measure_mono hK0K)
  have hKfin : X.muN u K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKinv : ∀ g ∈ Hinf X u, (fun s => g * s * g⁻¹) ⁻¹' K = K := by
    intro g hg
    ext x
    constructor
    · rintro ⟨⟨a, k⟩, ⟨ha, hk⟩, hx⟩
      refine ⟨(g⁻¹ * a, k), ⟨(Hinf X u).mul_mem ((Hinf X u).inv_mem hg) ha, hk⟩, ?_⟩
      have hx' : a * k * a⁻¹ = g * x * g⁻¹ := hx
      show g⁻¹ * a * k * (g⁻¹ * a)⁻¹ = x
      calc g⁻¹ * a * k * (g⁻¹ * a)⁻¹ = g⁻¹ * (a * k * a⁻¹) * g := by group
        _ = x := by rw [hx']; group
    · rintro ⟨⟨a, k⟩, ⟨ha, hk⟩, hx⟩
      refine ⟨(g * a, k), ⟨(Hinf X u).mul_mem hg ha, hk⟩, ?_⟩
      have hx' : a * k * a⁻¹ = x := hx
      show g * a * k * (g * a)⁻¹ = g * x * g⁻¹
      calc g * a * k * (g * a)⁻¹ = g * (a * k * a⁻¹) * g⁻¹ := by group
        _ = g * x * g⁻¹ := by rw [hx']

  have key : ∀ g ∈ Hinf X u, (X.muN u).map (fun s => g * s * g⁻¹) = X.muN u := by
    intro g hg
    have hm : Measurable fun s : X.B.I.Ginf => g * s * g⁻¹ := (hcont g).measurable
    have hpre : ∀ S : Set X.B.I.Ginf, (fun s => g * s * g⁻¹) ⁻¹' S = (fun s => g⁻¹ * s * g⁻¹⁻¹) '' S := by
      intro S
      exact (congrFun (Set.image_eq_preimage_of_inverse (f := fun s => g⁻¹ * s * g⁻¹⁻¹)
        (g := fun s => g * s * g⁻¹) (fun s => by show g * (g⁻¹ * s * g⁻¹⁻¹) * g⁻¹ = s; group)
        (fun s => by show g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s; group)) S).symm
    have hν0 : (X.muN u).map (fun s => g * s * g⁻¹) ≠ 0 := by
      intro hz
      apply h0
      have := congrArg (fun m : Measure X.B.I.Ginf => m Set.univ) hz
      simp only [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this
      exact Measure.measure_univ_eq_zero.1 this
    have hνc : (X.muN u).map (fun s => g * s * g⁻¹) (N : Set X.B.I.Ginf)ᶜ = 0 := by
      rw [Measure.map_apply hm hNc.measurableSet.compl]
      exact measure_mono_null (t := (N : Set X.B.I.Ginf)ᶜ) (fun ⦃s⦄ hs hsN => hs (hconj g hg s hsN)) hc
    have hνi : ∀ t ∈ N, ((X.muN u).map (fun s => g * s * g⁻¹)).map (fun x => t * x) =
        (X.muN u).map (fun s => g * s * g⁻¹) := by
      intro t ht
      have ht' : g⁻¹ * t * g⁻¹⁻¹ ∈ X.NinfU u := hconj g⁻¹ ((Hinf X u).inv_mem hg) t ht
      rw [Measure.map_map (measurable_const_mul t) hm]
      have e : (fun x => t * x) ∘ (fun s => g * s * g⁻¹) =
          (fun s => g * s * g⁻¹) ∘ (fun x => (g⁻¹ * t * g⁻¹⁻¹) * x) := by
        funext s
        show t * (g * s * g⁻¹) = g * (g⁻¹ * t * g⁻¹⁻¹ * s) * g⁻¹
        group
      rw [e, ← Measure.map_map hm (measurable_const_mul _), hl _ ht']
    have hνf : IsFiniteMeasureOnCompacts ((X.muN u).map (fun s => g * s * g⁻¹)) := ⟨fun C hC => by
      rw [Measure.map_apply hm hC.isClosed.measurableSet, hpre]
      exact (hC.image (hcont _)).measure_lt_top⟩
    obtain ⟨c, _, hceq⟩ := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.haar_unique N hNc (X.muN u)
      ((X.muN u).map (fun s => g * s * g⁻¹)) h0 hc hl hfin hνc hνi hνf
    have hK' : (X.muN u).map (fun s => g * s * g⁻¹) K = X.muN u K := by
      rw [Measure.map_apply hm hKc.isClosed.measurableSet, hKinv g hg]
    rw [hceq, Measure.smul_apply, smul_eq_mul] at hK'
    have hc1 : c = 1 := (ENNReal.mul_left_inj hKpos.ne' hKfin).1 (hK'.trans (one_mul _).symm)
    rw [hceq, hc1, one_smul]
  have hinv' : h⁻¹ ∈ Hinf X u := (Hinf X u).inv_mem hh
  have e : (fun s => h * s * h⁻¹) '' Ω = (fun s => h⁻¹ * s * h⁻¹⁻¹) ⁻¹' Ω :=
    congrFun (Set.image_eq_preimage_of_inverse (f := fun s => h * s * h⁻¹) (g := fun s => h⁻¹ * s * h⁻¹⁻¹)
      (fun s => by show h⁻¹ * (h * s * h⁻¹) * h⁻¹⁻¹ = s; group)
      (fun s => by show h * (h⁻¹ * s * h⁻¹⁻¹) * h⁻¹ = s; group)) Ω
  rw [e, ← Measure.map_apply (hcont _).measurable hΩ, key _ hinv']

end Formalism.L2.SG.Pf.IdMeet
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolGcPf
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut
open Matrix

section Conj

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter)

theorem gam_mem_GF (γ : Gam X u) : (γ : X.B.I.GA) ∈ X.B.I.GFset := (Subgroup.mem_inf.1 γ.2).1

theorem gam_fst_mem (γ : Gam X u) : (γ : X.B.I.GA).1 ∈ Hinf X u :=
  (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.2).2).1

theorem iotaF_coe (γ : Gam X u) : ((iotaF X u γ : Hfin X u) : X.B.I.Gf) = (γ : X.B.I.GA).2 := rfl

theorem gc_conj_sub (γ : Gam X u) (h : Hfin X u) (κ : Ku X u hK) (s : X.B.I.Ginf)
    (hs : s ∈ GcS X u hK ((h : X.B.I.Gf) * X.xu u)) :
    (γ : X.B.I.GA).1 * s * (γ : X.B.I.GA).1⁻¹ ∈
      GcS X u hK ((iotaF X u γ * h * (κ : Hfin X u) : Hfin X u) * X.xu u) := by
  rw [mem_gcS] at hs ⊢
  obtain ⟨ν, hG, rfl, hN, hF, hk⟩ := hs
  refine ⟨(γ : X.B.I.GA) * ν * (γ : X.B.I.GA)⁻¹, ?_, rfl, ?_, ?_, ?_⟩
  · exact (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).mul_mem
      ((Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).mul_mem (gam_mem_GF X u γ) hG)
      ((Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).inv_mem (gam_mem_GF X u γ))
  · have hH := gam_fst_mem X u γ
    have he : ∀ v a, uMat ((γ : X.B.I.GA).1 v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
      fun v a => hH v _ (Or.inl (Or.inl ⟨a, rfl⟩))
    have hz : ∀ v, uMat ((γ : X.B.I.GA).1 v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) :=
      fun v => hH v _ (Or.inr rfl)
    refine (Formalism.L2.SG.CovariantRepresentation.ninf_conj_iff X u (γ : X.B.I.GA).1 he hz _).2 ?_
    have : (γ : X.B.I.GA).1⁻¹ * ((γ : X.B.I.GA) * ν * (γ : X.B.I.GA)⁻¹).1 * (γ : X.B.I.GA).1 = ν.1 := by
      simp only [Prod.fst_mul, Prod.fst_inv]; group
    rw [this]; exact hN
  · have := (nfinConj_holds X u (iotaF X u γ) ν.2 hF).1
    rw [iotaF_coe] at this
    simpa only [Prod.snd_mul, Prod.snd_inv] using this
  · have hκ : (X.xu u)⁻¹ * ((κ : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.K2 := κ.2
    have e : (((iotaF X u γ * h * (κ : Hfin X u) : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ * ((γ : X.B.I.GA) * ν * (γ : X.B.I.GA)⁻¹).2 *
        (((iotaF X u γ * h * (κ : Hfin X u) : Hfin X u) : X.B.I.Gf) * X.xu u) =
        ((X.xu u)⁻¹ * ((κ : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ *
          (((h : X.B.I.Gf) * X.xu u)⁻¹ * ν.2 * ((h : X.B.I.Gf) * X.xu u)) *
          ((X.xu u)⁻¹ * ((κ : Hfin X u) : X.B.I.Gf) * X.xu u) := by
      simp only [Subgroup.coe_mul, iotaF_coe, Prod.snd_mul, Prod.snd_inv]
      group
    rw [e]
    exact hK.2.1 _ (hK.2.1 _ (hK.2.2.1 _ hκ) _ hk) _ hκ

end Conj

theorem gcConjC_holds : GcConjC := by
  intro D X u hK γ h κ
  ext s
  constructor
  · intro hs
    have e : (iotaF X u γ⁻¹ * (iotaF X u γ * h * (κ : Hfin X u)) * ((κ⁻¹ : Ku X u hK) : Hfin X u) : Hfin X u) = h := by
      rw [map_inv, InvMemClass.coe_inv]; group
    have := gc_conj_sub X u hK γ⁻¹ (iotaF X u γ * h * (κ : Hfin X u)) κ⁻¹ s hs
    rw [e] at this
    refine ⟨_, this, ?_⟩
    simp only [InvMemClass.coe_inv, Prod.fst_inv]
    group
  · rintro ⟨t, ht, rfl⟩
    exact gc_conj_sub X u hK γ h κ t ht

theorem isSFund_conj {D : D7} (X : HidaSetting D) (S : Set X.B.I.Ginf) (Ω : Set X.B.I.Ginf)
    (hΩ : IsSFund X.B.I S Ω) (a : X.B.I.Ginf) :
    IsSFund X.B.I ((fun s => a * s * a⁻¹) '' S) ((fun y => a * y) '' Ω) := by
  have hpre : (fun y => a * y) '' Ω = {x | a⁻¹ * x ∈ Ω} := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨a⁻¹ * x, hx, by group⟩
  rw [hpre]
  refine ⟨(measurable_const_mul a⁻¹) hΩ.1, fun x => ?_, fun x hx s' hs' hsx => ?_⟩
  · obtain ⟨s, hs, hsx⟩ := hΩ.2.1 (a⁻¹ * x)
    refine ⟨a * s * a⁻¹, ⟨s, hs, rfl⟩, ?_⟩
    show a⁻¹ * (a * s * a⁻¹ * x) ∈ Ω
    have : a⁻¹ * (a * s * a⁻¹ * x) = s * (a⁻¹ * x) := by group
    rwa [this]
  · obtain ⟨s, hs, rfl⟩ := hs'
    have h2 : s * (a⁻¹ * x) ∈ Ω := by
      have : a⁻¹ * (a * s * a⁻¹ * x) = s * (a⁻¹ * x) := by group
      have h := hsx; simp only [Set.mem_ofPred_eq] at h; rwa [this] at h
    have := hΩ.2.2 _ hx s hs h2
    rw [this]; group

theorem nocol_fund_exists {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (ρ : (Y.cs u).Cl) : ∃ Ω, IsSFund X.B.I (Formalism.L2.SG.TermOp.KExpCut.NOcol (X.Fu u) (Y.cs u) ρ) Ω := by
  have hL := ((Y.rowsOK u).1 _ ((Y.cs u).lam_mem ρ)).1.1
  have := Formalism.L2.SG.Pf.ROsub_discrete X (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) hL 1
  obtain ⟨Ω, hΩ⟩ := Formalism.L2.SG.Pf.isSFund_of_discrete X.B.I
    (Formalism.L2.SG.Pf.ROsub X (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) 1)
  refine ⟨Ω, ?_⟩
  have e : ((Formalism.L2.SG.Pf.ROsub X (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) 1 :
      Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) = Formalism.L2.SG.TermOp.KExpCut.NOcol (X.Fu u) (Y.cs u) ρ := by
    ext y
    show y ∈ ROset X (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) 1 ↔ _
    constructor
    · rintro ⟨x, n, h1, h2, h3, -⟩
      exact ⟨x, n, h1, h2, h3⟩
    · rintro ⟨x, n, h1, h2, h3⟩
      exact ⟨x, n, h1, h2, h3, by simpa using h3⟩
  rwa [e] at hΩ

theorem gcFundC_holds : GcFundC := by
  intro D X Y u h
  obtain ⟨ρ, ⟨γ, κ, rfl⟩, -⟩ := Y.colReps u h
  obtain ⟨Ω, hΩ⟩ := nocol_fund_exists Y u ρ
  rw [nocolEqC_holds D X Y u ρ] at hΩ
  rw [gcConjC_holds D X u Y.hK γ ((Y.cs u).h ρ) κ]
  exact ⟨_, isSFund_conj X _ Ω hΩ _⟩

end Formalism.L2.SG.Pf.IdMeet
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolFundPf
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

section Gen

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem muN_preimage (a : X.B.I.Ginf) (ha : a ∈ X.NinfU u) {A : Set X.B.I.Ginf} (hA : MeasurableSet A) :
    X.muN u {y | a * y ∈ A} = X.muN u A := by
  have h := Measure.map_apply (μ := X.muN u) (measurable_const_mul a) hA
  rw [(X.muN_haar u).2.2.2 a ha] at h
  exact h.symm

end Gen

theorem fundMeasEqC_holds : FundMeasEqC := by
  intro D X u Γ Ω Ω' hsub hc hΩ hΩ'
  have hcs : (Γ : Set X.B.I.Ginf).Countable := Set.countable_coe_iff.1 hc
  have hun : ∀ (P : Set X.B.I.Ginf), IsSFund X.B.I Γ P → ∀ n, ∀ a ∈ (Γ : Set X.B.I.Ginf), ∀ a' ∈ (Γ : Set X.B.I.Ginf),
      a * n ∈ P → a' * n ∈ P → a = a' := by
    intro P hP n a ha a' ha' h1 h2
    have h3 : (a' * a⁻¹) * (a * n) ∈ P := by simpa [mul_assoc] using h2
    have := hP.2.2 _ h1 _ (Γ.mul_mem ha' (Γ.inv_mem ha)) h3
    exact (mul_inv_eq_one.1 this).symm
  rw [Formalism.L2.SG.TermOp.IdBlocks.measure_decomp (Γ : Set X.B.I.Ginf) Ω Ω' (X.muN u) hcs hΩ.1 hΩ'.1 hΩ'.2.1
      (hun Ω' hΩ'),
    Formalism.L2.SG.TermOp.IdBlocks.measure_decomp (Γ : Set X.B.I.Ginf) Ω' Ω (X.muN u) hcs hΩ'.1 hΩ.1 hΩ.2.1 (hun Ω hΩ)]
  have hterm : ∀ a : (Γ : Set X.B.I.Ginf),
      X.muN u (Ω ∩ {n | (a : X.B.I.Ginf) * n ∈ Ω'}) =
        X.muN u (Ω' ∩ {m | ((a : X.B.I.Ginf))⁻¹ * m ∈ Ω}) := by
    intro a
    have hS : MeasurableSet (Ω' ∩ {m | ((a : X.B.I.Ginf))⁻¹ * m ∈ Ω}) :=
      hΩ'.1.inter ((measurable_const_mul _) hΩ.1)
    rw [← muN_preimage X u (a : X.B.I.Ginf) (hsub a.2) hS]
    congr 1
    ext n
    simp [and_comm]
  simp_rw [hterm]
  let e : (Γ : Set X.B.I.Ginf) ≃ (Γ : Set X.B.I.Ginf) :=
    ⟨fun a => ⟨(a : X.B.I.Ginf)⁻¹, Γ.inv_mem a.2⟩, fun a => ⟨(a : X.B.I.Ginf)⁻¹, Γ.inv_mem a.2⟩,
      fun a => by simp, fun a => by simp⟩
  exact e.tsum_eq (fun b : (Γ : Set X.B.I.Ginf) => X.muN u (Ω' ∩ {m | (b : X.B.I.Ginf) * m ∈ Ω}))

theorem indexVolC_holds : IndexVolC := by
  intro D X u Γ Γ' Ω hle hsub hc hk hΩ
  set H : Subgroup Γ := Γ'.subgroupOf Γ with hH
  have : H.FiniteIndex := ⟨hk⟩
  have : Finite (Γ ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (Γ ⧸ H) := Fintype.ofFinite _
  let r : Γ ⧸ H → Γ := fun q => Quotient.out q
  have hr : ∀ q, ((r q : Γ) : Γ ⧸ H) = q := fun q => Quotient.out_eq q
  let A : Γ ⧸ H → Set X.B.I.Ginf := fun q => {y | ((r q : Γ) : X.B.I.Ginf) * y ∈ Ω}
  have hA : ∀ q, MeasurableSet (A q) := fun q => (measurable_const_mul _) hΩ.1

  have key : ∀ (a b : Γ) (y : X.B.I.Ginf), (a : X.B.I.Ginf) * y ∈ Ω → (b : X.B.I.Ginf) * y ∈ Ω → a = b := by
    intro a b y ha hb
    have h3 : ((b : X.B.I.Ginf) * (a : X.B.I.Ginf)⁻¹) * ((a : X.B.I.Ginf) * y) ∈ Ω := by
      simpa [mul_assoc] using hb
    have := hΩ.2.2 _ ha _ (Γ.mul_mem b.2 (Γ.inv_mem a.2)) h3
    exact Subtype.ext (mul_inv_eq_one.1 this).symm
  refine ⟨⋃ q, A q, ⟨MeasurableSet.iUnion hA, ?_, ?_⟩, ?_⟩
  · intro x
    obtain ⟨s, hs, hsx⟩ := hΩ.2.1 x
    let sΓ : Γ := ⟨s, hs⟩
    have hq : (r (sΓ : Γ ⧸ H))⁻¹ * sΓ ∈ H := QuotientGroup.eq.1 (hr _)
    refine ⟨(((r (sΓ : Γ ⧸ H))⁻¹ * sΓ : Γ) : X.B.I.Ginf), Subgroup.mem_subgroupOf.1 hq, ?_⟩
    refine Set.mem_iUnion.2 ⟨(sΓ : Γ ⧸ H), ?_⟩
    show ((r (sΓ : Γ ⧸ H) : Γ) : X.B.I.Ginf) * ((((r (sΓ : Γ ⧸ H))⁻¹ * sΓ : Γ) : X.B.I.Ginf) * x) ∈ Ω
    simpa [mul_assoc, sΓ] using hsx
  · intro x hx s hs hsx
    obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hsx
    let sΓ : Γ := ⟨s, hle hs⟩
    have hp0 : ((r p : Γ) : X.B.I.Ginf) * (s * x) ∈ Ω := hp
    have hp' : ((r p * sΓ : Γ) : X.B.I.Ginf) * x ∈ Ω := by
      simpa [mul_assoc, sΓ] using hp0
    have e1 : r p * sΓ = r q := key _ _ x hp' hq
    have e2 : sΓ = (r p)⁻¹ * r q := by rw [← e1]; group
    have hmem : (r p)⁻¹ * r q ∈ H := by
      rw [← e2]; exact Subgroup.mem_subgroupOf.2 hs
    have hpq : p = q := by
      have := QuotientGroup.eq.2 hmem
      rw [hr, hr] at this
      exact this
    subst hpq
    have : sΓ = 1 := by rw [e2]; group
    exact congrArg Subtype.val this
  · have hdisj : Pairwise (Function.onFun Disjoint A) := by
      intro p q hpq
      refine Set.disjoint_left.2 fun y hy1 hy2 => hpq ?_
      have := key _ _ y hy1 hy2
      rw [← hr p, ← hr q, this]
    rw [measure_iUnion hdisj hA, tsum_fintype]
    have hterm : ∀ q, X.muN u (A q) = X.muN u Ω := fun q =>
      muN_preimage X u _ (hsub (r q).2) hΩ.1
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end Formalism.L2.SG.Pf.IdMeet
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolColPf
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.PoincareInHH.Cut

theorem gcS_sub {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) :
    ((GcS X u hK c : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) ⊆ X.NinfU u := by
  intro s hs
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hs
  exact (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 hγ).2).1

theorem isSFund_conjImg {D : D7} (X : HidaSetting D) (S S' : Set X.B.I.Ginf) (Ω : Set X.B.I.Ginf) (c : X.B.I.Ginf)
    (hS : ∀ s, s ∈ S' ↔ ∃ t ∈ S, c * t * c⁻¹ = s) (hΩ : IsSFund X.B.I S Ω) :
    IsSFund X.B.I S' ((fun s => c * s * c⁻¹) '' Ω) := by
  have himg : (fun s => c * s * c⁻¹) '' Ω = (fun s => c⁻¹ * s * c) ⁻¹' Ω := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨c⁻¹ * x * c, hx, by group⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [himg]
    exact ((measurable_const_mul c⁻¹).mul_const c) hΩ.1
  · intro x
    obtain ⟨t, ht, htx⟩ := hΩ.2.1 (c⁻¹ * x * c)
    refine ⟨c * t * c⁻¹, (hS _).2 ⟨t, ht, rfl⟩, ?_⟩
    exact ⟨t * (c⁻¹ * x * c), htx, by group⟩
  · intro x hx s hs hsx
    obtain ⟨ω, hω, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := (hS s).1 hs
    rw [himg] at hsx
    have h1 : t * ω ∈ Ω := by
      have e : c⁻¹ * (c * t * c⁻¹ * (c * ω * c⁻¹)) * c = t * ω := by group
      have h0 : c⁻¹ * (c * t * c⁻¹ * (c * ω * c⁻¹)) * c ∈ Ω := hsx
      rw [e] at h0
      exact h0
    have := hΩ.2.2 ω hω t ht h1
    rw [this]; group

theorem volColC_of (h1 : NOinfEqC) (h2 : NOcolEqC) (h3 : GcCountC) (h4 : FundMeasEqC) (h5 : IndexVolC)
    (h6 : IndexTransferC) (h7 : ConjUC) (h8 : GcFundC) (h9 : GcConjC) (h10 : HinfConjC) : VolColC := by
  intro D X Y u ρ Ω hΩ
  let Γ : Hfin X u → Subgroup X.B.I.Ginf := fun h => GcS X u Y.hK ((h : X.B.I.Gf) * X.xu u)
  let U : Hfin X u → Subgroup X.B.I.Gf := fun h => UcS X u Y.hK ((h : X.B.I.Gf) * X.xu u)
  have hsub : ∀ h, ((Γ h : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) ⊆ X.NinfU u := fun h => gcS_sub X u Y.hK _
  have hcnt : ∀ h, Countable (Γ h) := fun h => h3 D X u Y.hK _
  let Ωh : Hfin X u → Set X.B.I.Ginf := fun h => Classical.choose (h8 D X Y u h)
  have hΩh : ∀ h, IsSFund X.B.I (Γ h) (Ωh h) := fun h => Classical.choose_spec (h8 D X Y u h)
  let F : Hfin X u → ℝ≥0∞ := fun h => X.muN u (Ωh h)
  have hF : ∀ h Ω', IsSFund X.B.I (Γ h) Ω' → X.muN u Ω' = F h := fun h Ω' hΩ' =>
    h4 D X u (Γ h) Ω' (Ωh h) (hsub h) (hcnt h) hΩ' (hΩh h)

  have hratio : ∀ g h : Hfin X u,
      F g * ((Γ h).relIndex (Γ g) : ℝ≥0∞) = F h * ((Γ g).relIndex (Γ h) : ℝ≥0∞) := by
    intro g h
    have hne1 : (Γ h ⊓ Γ g).relIndex (Γ g) ≠ 0 := by
      rw [Subgroup.inf_relIndex_right, (h6 D X u Y.hK g h).1]; exact (h6 D X u Y.hK g h).2
    have hne2 : (Γ g ⊓ Γ h).relIndex (Γ h) ≠ 0 := by
      rw [Subgroup.inf_relIndex_right, (h6 D X u Y.hK h g).1]; exact (h6 D X u Y.hK h g).2
    obtain ⟨Ω1, hΩ1, hμ1⟩ := h5 D X u (Γ g) (Γ h ⊓ Γ g) (Ωh g) inf_le_right (hsub g) (hcnt g) hne1 (hΩh g)
    obtain ⟨Ω2, hΩ2, hμ2⟩ := h5 D X u (Γ h) (Γ g ⊓ Γ h) (Ωh h) inf_le_right (hsub h) (hcnt h) hne2 (hΩh h)
    rw [inf_comm] at hΩ2
    have hc : Countable ↥(Γ h ⊓ Γ g) := by
      exact Set.countable_coe_iff.2 ((Set.countable_coe_iff.1 (hcnt g)).mono (fun x hx => (Subgroup.mem_inf.1 hx).2))
    have heq := h4 D X u (Γ h ⊓ Γ g) Ω1 Ω2 (fun x hx => hsub g (Subgroup.mem_inf.1 hx).2) hc hΩ1 hΩ2
    rw [hμ1, hμ2, Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right] at heq
    rw [mul_comm, heq, mul_comm]

  have hU : ∀ g h : Hfin X u, U (g * h) = (U h).map (MulAut.conj (g : X.B.I.Gf)).toMonoidHom := by
    intro g h
    have := h7 D X u Y.hK g ((h : X.B.I.Gf) * X.xu u)
    simp only [U, Subgroup.coe_mul, mul_assoc]
    exact this
  have hinj : ∀ g : Hfin X u, Function.Injective (MulAut.conj (g : X.B.I.Gf)).toMonoidHom :=
    fun g => (MulAut.conj (g : X.B.I.Gf)).injective
  have hidx : ∀ g h : Hfin X u, (U (g * h)).relIndex (U g) = (U h).relIndex (U 1) := by
    intro g h
    have e := hU g 1
    rw [mul_one] at e
    rw [hU g h, e, Subgroup.relIndex_map_map_of_injective _ _ (hinj g)]
  have hidx' : ∀ g h : Hfin X u, (U g).relIndex (U (g * h)) = (U 1).relIndex (U h) := by
    intro g h
    have e := hU g 1
    rw [mul_one] at e
    rw [hU g h, e, Subgroup.relIndex_map_map_of_injective _ _ (hinj g)]
  have hG : ∀ g h : Hfin X u, (Γ h).relIndex (Γ g) = (U h).relIndex (U g) := fun g h => (h6 D X u Y.hK g h).1
  have hGne : ∀ g h : Hfin X u, (Γ h).relIndex (Γ g) ≠ 0 := fun g h => by
    rw [hG]; exact (h6 D X u Y.hK g h).2

  have hmul : ∀ g h : Hfin X u, F (g * h) * F 1 = F g * F h := by
    intro g h
    have E1 := hratio g (g * h)
    have E2 := hratio 1 h
    set A : ℕ := (U h).relIndex (U 1) with hA
    set B : ℕ := (U 1).relIndex (U h) with hB
    have hA1 : (Γ (g * h)).relIndex (Γ g) = A := by
      rw [hG, hA, hidx g h]
    have hB1 : (Γ g).relIndex (Γ (g * h)) = B := by
      rw [hG, hB, hidx' g h]
    have hA2 : (Γ h).relIndex (Γ 1) = A := by rw [hG]
    have hB2 : (Γ 1).relIndex (Γ h) = B := by rw [hG]
    have hA0 : A ≠ 0 := by rw [← hA2]; exact hGne 1 h
    have hB0 : B ≠ 0 := by rw [← hB2]; exact hGne h 1
    rw [hA1, hB1] at E1
    rw [hA2, hB2] at E2
    have hAB0 : ((A : ℝ≥0∞) * B) ≠ 0 := mul_ne_zero (by exact_mod_cast hA0) (by exact_mod_cast hB0)
    have hABt : ((A : ℝ≥0∞) * B) ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top A) (ENNReal.natCast_ne_top B)
    refine (ENNReal.mul_left_inj hAB0 hABt).1 ?_
    calc F (g * h) * F 1 * (A * B) = (F (g * h) * B) * (F 1 * A) := by ring
      _ = (F g * A) * (F h * B) := by rw [← E1, E2]
      _ = F g * F h * (A * B) := by ring

  have hinv : ∀ (γ : Gam X u) (h : Hfin X u) (κ : Ku X u Y.hK), F (iotaF X u γ * h * (κ : Hfin X u)) = F h := by
    intro γ h κ
    set c : X.B.I.Ginf := (γ : X.B.I.GA).1 with hc
    have hcH : c ∈ Hinf X u := (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.2).2).1
    have hset := h9 D X u Y.hK γ h κ
    have hS : ∀ s, s ∈ ((Γ (iotaF X u γ * h * (κ : Hfin X u)) : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) ↔
        ∃ t ∈ ((Γ h : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf), c * t * c⁻¹ = s := by
      intro s
      have := Set.ext_iff.1 hset s
      simpa [Γ] using this
    have hfund := isSFund_conjImg X _ _ (Ωh h) c hS (hΩh h)
    rw [← hF _ _ hfund]
    exact h10 D X u c hcH (Ωh h) (hΩh h).1

  have hfin : (Set.range F).Finite := by
    refine (Set.finite_range (fun ρ : (Y.cs u).Cl => F ((Y.cs u).h ρ))).subset ?_
    rintro _ ⟨h, rfl⟩
    obtain ⟨ρ, ⟨γ, κ, hh⟩, -⟩ := Y.colReps u h
    exact ⟨ρ, by rw [hh, hinv]⟩

  have hconst : ∀ h, F h = F 1 := by
    intro h
    have E := hratio 1 h
    have ha : (Γ h).relIndex (Γ 1) ≠ 0 := hGne 1 h
    have hb : (Γ 1).relIndex (Γ h) ≠ 0 := hGne h 1
    have ha' : ((Γ h).relIndex (Γ 1) : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
    have hb' : ((Γ 1).relIndex (Γ h) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb
    by_cases h0 : F 1 = 0
    · rw [h0, zero_mul] at E
      rcases mul_eq_zero.1 E.symm with e | e
      · rw [e, h0]
      · exact absurd e hb'
    by_cases ht : F 1 = ⊤
    · rw [ht, ENNReal.top_mul ha'] at E
      rcases ENNReal.mul_eq_top.1 E.symm with ⟨-, e⟩ | ⟨e, -⟩
      · exact absurd e (ENNReal.natCast_ne_top _)
      · rw [e, ht]

    have hpos : ∀ k, F k ≠ 0 ∧ F k ≠ ⊤ := by
      intro k
      have Ek := hratio 1 k
      have hak : ((Γ k).relIndex (Γ 1) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hGne 1 k
      have hbk : ((Γ 1).relIndex (Γ k) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hGne k 1
      constructor
      · intro e; rw [e, zero_mul] at Ek
        rcases mul_eq_zero.1 Ek with e' | e'
        · exact h0 e'
        · exact hak e'
      · intro e; rw [e, ENNReal.top_mul hbk] at Ek
        rcases ENNReal.mul_eq_top.1 Ek with ⟨-, e'⟩ | ⟨e', -⟩
        · exact ENNReal.natCast_ne_top _ e'
        · exact ht e'
    let q : Hfin X u → ℝ := fun k => (F k).toReal / (F 1).toReal
    have hF1 : 0 < (F 1).toReal := ENNReal.toReal_pos h0 ht
    have hq : ∀ g k, q (g * k) = q g * q k := by
      intro g k
      have := congrArg ENNReal.toReal (hmul g k)
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at this
      simp only [q]
      field_simp
      linarith [this]
    have hqpow : ∀ n : ℕ, q (h ^ n) = q h ^ n := by
      intro n
      induction n with
      | zero => simp [q, hF1.ne']
      | succ n ih => rw [pow_succ, hq, ih, pow_succ]
    have hqpos : 0 < q h := div_pos (ENNReal.toReal_pos (hpos h).1 (hpos h).2) hF1
    have hq1 : q h = 1 := by
      by_contra hne
      have hinjq : Function.Injective (fun n : ℕ => q h ^ n) := pow_right_injective₀ hqpos hne
      have hrange : (Set.range (fun n : ℕ => q h ^ n)).Finite := by
        refine ((hfin.image (fun x : ℝ≥0∞ => x.toReal / (F 1).toReal))).subset ?_
        rintro _ ⟨n, rfl⟩
        exact ⟨F (h ^ n), ⟨h ^ n, rfl⟩, by simp only [q] at hqpow; exact hqpow n⟩
      exact Set.infinite_range_of_injective hinjq hrange
    have : (F h).toReal = (F 1).toReal := by
      have := hq1; simp only [q] at this
      field_simp at this; linarith
    exact (ENNReal.toReal_eq_toReal_iff' (hpos h).2 ht).1 this

  have hρ : IsSFund X.B.I (Γ ((Y.cs u).h ρ)) Ω := by
    have := h2 D X Y u ρ
    rw [this] at hΩ
    exact hΩ
  have h1' : IsSFund X.B.I (Γ 1) (Y.FN u) := by
    have e := h1 D X u Y.hK
    have hFN := Y.FN_fund u
    rw [e] at hFN
    simpa [Γ] using hFN
  rw [hF _ _ hρ, hF _ _ h1', hconst]

end Formalism.L2.SG.Pf.IdMeet
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetPhasePf
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full

theorem idMeetPhaseC_of (hK : IdMeetKeyC) : IdMeetPhaseC := by
  intro D X Y u hneat _ ρ t hid hmeet
  obtain ⟨-, hlin⟩ := hK D X Y u hneat ρ ρ t hid hmeet
  have hR : RatLink X t.pt t.lin := t.rep.2.1
  have hN : t.pt.1 ∈ X.NinfU u := Formalism.L2.SG.Pf.nLamNinf_holds D X u _ t.pt t.lin hR hlin
  have hNf : t.pt.2 ∈ X.NfinU u := Formalism.L2.SG.Pf.nLamNfin_holds D X u _ t.pt t.lin hR hlin
  obtain ⟨h1, hmul, hinv⟩ := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  obtain ⟨-, hchi, -⟩ := Formalism.L2.SG.Pf.nilradical_conj_level' D X Y u ρ t.pt t.lin hlin hR
  have hprod := Formalism.L2.SG.Pf.psiProd_all D X u t.pt (ratLink_mem X hR) hN hNf
  refine ⟨hinv _ hN, ?_⟩
  have hψ1 : X.psiInfU u 1 = 1 := by
    have h11 := (hmul 1 h1 1 h1).2
    rw [mul_one] at h11
    have hn := Formalism.L2.SG.RealObj.InfCut.norm_psiInfU X u 1
    have h0 : X.psiInfU u 1 ≠ 0 := by
      intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
    exact mul_left_cancel₀ h0 (h11.symm.trans (mul_one _).symm)
  have hinvψ : X.psiInfU u t.pt.1⁻¹ * X.psiInfU u t.pt.1 = 1 := by
    rw [← (hmul _ (hinv _ hN) _ hN).2, inv_mul_cancel, hψ1]
  have hconj : starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) = X.psiInfU u t.pt.1 := by
    have hn := Formalism.L2.SG.RealObj.InfCut.norm_psiInfU X u t.pt.1⁻¹
    have hz : starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) = (X.psiInfU u t.pt.1⁻¹)⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]; simp
    rw [hz, inv_eq_of_mul_eq_one_right hinvψ]
  show X.chi2 ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)) *
    starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) = 1
  rw [hchi, hconj, mul_comm]
  exact hprod

end Formalism.L2.SG.Pf.IdMeet
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetOnePf
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

section Gen

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem nlam_iff_of_rel {Λ : Submodule (𝓞 D.host.E) (VS D).V} {p q : GCar X u u F0 F0 Λ Λ}
    (h : GRel X u u F0 F0 Λ Λ p q) : p.1.2 ∈ NLam Λ (lf D F0) ↔ q.1.2 ∈ NLam Λ (lf D F0) := by
  obtain ⟨n, hn, n', hn', hq⟩ := h
  let H := NLamSub Λ (lf D F0)
  rw [hq]
  constructor
  · intro hp
    exact H.mul_mem (H.mul_mem hn hp) hn'
  · intro hq'
    have e : p.1.2 = n⁻¹ * (n * p.1.2 * n') * n'⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hn) hq') (H.inv_mem hn')

theorem nlam_out_iff {Λ : Submodule (𝓞 D.host.E) (VS D).V} (p : GCar X u u F0 F0 Λ Λ) :
    (Quot.out (Quot.mk (GRel X u u F0 F0 Λ Λ) p)).1.2 ∈ NLam Λ (lf D F0) ↔ p.1.2 ∈ NLam Λ (lf D F0) := by
  have key : ∀ a b : GCar X u u F0 F0 Λ Λ, Relation.EqvGen (GRel X u u F0 F0 Λ Λ) a b →
      (a.1.2 ∈ NLam Λ (lf D F0) ↔ b.1.2 ∈ NLam Λ (lf D F0)) := by
    intro a b hab
    induction hab with
    | rel a b h => exact nlam_iff_of_rel h
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  exact key _ _ (Quot.eqvGen_exact (Quot.out_eq (Quot.mk (GRel X u u F0 F0 Λ Λ) p)))

theorem isId_of_lin {t : GTerm X u u F0 F0 what₂ what₂} (h : t.lin ∈ NLam t.lam (lf D F0)) : t.isId := by
  unfold GTerm.isId Formalism.L2.SG.FourParts.termIsId Formalism.L2.SG.FourParts.IsIdT
  refine ⟨t.frame, ⟨t.rep.2.2.2.2, rfl⟩, ?_⟩
  unfold Formalism.L2.SG.FourParts.IsIdF
  have hi : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hf : mapLF t.lin (lf D F0) = _ := dif_pos hi
  rw [show t.frame = mapLF t.lin (lf D F0) from rfl, hf]
  refine ⟨t.lin, h, fun a => rfl, ?_⟩
  have hz : (mapFlag t.lin hi (lf D F0).fl).z = t.lin (lf D F0).fl.z := rfl
  show t.lin (lf D F0).fl.z - (mapFlag t.lin hi (lf D F0).fl).z ∈ _
  rw [hz, sub_self]
  exact zero_mem _

end Gen

theorem idMeetOneC_of (hK : IdMeetKeyC) : IdMeetOneC := by
  intro D X Y u hneat _
  refine ⟨fun ρ ρ' t hid hm => (hK D X Y u hneat ρ ρ' t hid hm).1, ?_, ?_⟩
  · intro ρ t t' hid hid' hm hm'
    have h1 := (hK D X Y u hneat ρ ρ t hid hm).2
    have h2 := (hK D X Y u hneat ρ ρ t' hid' hm').2
    obtain ⟨hl, hl', -⟩ := hm
    obtain ⟨hr, hr', -⟩ := hm'
    obtain ⟨lam, mem, lam', mem', cls⟩ := t
    obtain ⟨lam₂, mem₂, lam₂', mem₂', cls₂⟩ := t'
    simp only at hl hl' hr hr'
    subst hl hl' hr hr'
    have h1' : (Quot.out cls).1.2 ∈ Formalism.L2.SG.Pf.NLamSub ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) := h1
    have h2' : (Quot.out cls₂).1.2 ∈ Formalism.L2.SG.Pf.NLamSub ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) := h2
    have hrel : GRel X u u (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) (Quot.out cls) (Quot.out cls₂) :=
      ⟨(Quot.out cls₂).1.2 * ((Quot.out cls).1.2)⁻¹,
        Subgroup.mul_mem _ h2' (Subgroup.inv_mem _ h1'), 1, Formalism.L2.SG.Pf.nlam_one _ _, by group⟩
    have hs := Quot.sound hrel
    have hc : cls = cls₂ := (Quot.out_eq cls).symm.trans (hs.trans (Quot.out_eq cls₂))
    subst hc
    rfl
  · intro ρ
    have hΛ := (Y.cs u).lam_mem ρ
    let t : GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) :=
      idGTerm X ((Y.cs u).lamOf ρ) hΛ ((Y.rowsOK u).1 _ hΛ)
    have hlin : t.lin ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) :=
      (nlam_out_iff _).2 (Formalism.L2.SG.Pf.nlam_one _ _)
    refine ⟨t, isId_of_lin hlin, rfl, rfl, ?_⟩
    exact (Formalism.L2.SG.Pf.nilradical_conj_level' D X Y u ρ t.pt t.lin hlin t.rep.2.1).1

end Formalism.L2.SG.Pf.IdMeet
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolPf
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

theorem roinf_eq_nocol {D : D7} {X : HidaSetting D} (Y : Full X) {u : D.what₂.Word} (ρ : (Y.cs u).Cl)
    (t : GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)) (hl : t.lam = (Y.cs u).lamOf ρ)
    (hl' : t.lam' = (Y.cs u).lamOf ρ) (hγ : t.lin ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u))) :
    ROinf t = Formalism.L2.SG.TermOp.KExpCut.NOcol (X.Fu u) (Y.cs u) ρ := by
  ext y
  unfold ROinf ROset Formalism.L2.SG.TermOp.KExpCut.NOcol
  rw [hl, hl']
  constructor
  · rintro ⟨x, n, hx, hy, hn, -⟩
    exact ⟨x, n, hx, hy, hn⟩
  · rintro ⟨x, n, hx, hy, hn⟩
    refine ⟨x, n, hx, hy, hn, ?_⟩
    let H := NLamSub ((Y.cs u).lamOf ρ) (lf D (X.Fu u))
    exact H.mul_mem (H.mul_mem (H.inv_mem hγ) hn) hγ

theorem idMeetVolC_of (hK : IdMeetKeyC) (hV : VolColC) : IdMeetVolC := by
  intro D X Y u hN hF ρ t ht hm
  obtain ⟨-, hlin⟩ := hK D X Y u hN ρ ρ t ht hm
  have hR := roinf_eq_nocol Y ρ t hm.1.symm hm.2.1.symm hlin
  have hex : ∃ Ω, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROinf t) Ω := hF t
  unfold FundOf
  rw [dite_eq_left hex]
  apply hV D X Y u ρ
  rw [← hR]
  exact hex.choose_spec

end Formalism.L2.SG.Pf.IdMeet
end
end

noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.IdMeet

theorem volColC_holds : VolColC :=
  volColC_of noinfEqC_holds nocolEqC_holds gcCountC_holds fundMeasEqC_holds indexVolC_holds indexTransferC_holds
    conjUC_holds gcFundC_holds gcConjC_holds hinfConjC_holds

theorem idMeetOneC_holds : IdMeetOneC := idMeetOneC_of idMeetKeyC_holds

theorem idMeetPhaseC_holds : IdMeetPhaseC := idMeetPhaseC_of idMeetKeyC_holds

theorem idMeetVolC_holds : IdMeetVolC := idMeetVolC_of idMeetKeyC_holds volColC_holds

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHClosed
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut

namespace Formalism.L2.SG.Pf

theorem foldOKC_holds_of (hS : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), KsetSplit X u)
    (hN : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), UnipotentConjugateInLevel X u)
    (hL : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), RatLevi X u)
    (hP : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), PsiProd X u)
    (hU : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), IUnfold X u hK) :
    Formalism.L2.SG.Full.FoldOKC := by
  intro D X Y u hKL hW
  exact foldOK_of_steps X u Y.hK hKL (foldReadyX_holds X) (hS D X u) (hN D X u) (hL D X u) (hP D X u) hW
    (sratFund_holds X u) (Formalism.L2.SG.Closed.MultPoly_holds X) (hU D X u Y.hK)

theorem inHHC_holds_of (hS : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), KsetSplit X u)
    (hN : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), UnipotentConjugateInLevel X u)
    (hL : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), RatLevi X u)
    (hP : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), PsiProd X u)
    (hFB : ∀ (D : D7) (X : HidaSetting D), FundBridge X)
    (hPM : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), PserMeas X u hK)
    (hRph : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), PserRph X u hK)
    (hRF : ∀ (D : D7) (X : HidaSetting D), ArchimedeanConvolutionFixesInvariantL2 X) (hEF : ∀ (D : D7) (X : HidaSetting D), IdempotentFixesInvariantL2 X) :
    Formalism.L2.SG.Full.InHHC := by
  intro D X Y u hI hOK
  have hR := foldReadyX_holds X
  have hKL := Formalism.L2.SG.Closed.level_subgroup_properties X
  exact inHH_of X u Y.hK hR
    (@Formalism.L2.SG.Closed.fold_L2_first X.B.I.GA _ _ _ hR.1 hR.2.1 hR.2.2.1 _ hR.2.2.2.1 (X.B.I.muA X.B.μf)
      (@muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar))
    (@Formalism.L2.SG.Closed.fold_L2_second X.B.I.GA _ _ _ hR.1 hR.2.1 hR.2.2.1 _ hR.2.2.2.1 (X.B.I.muA X.B.μf)
      (@muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar))
    (hFB D X) hOK (phProps_closed X u Y.hK (hS D X u) (hN D X u) (hL D X u) (hP D X u))
    (poincare_well_defined X u Y.hK (hS D X u) (hN D X u)) (hPM D X u Y.hK) (hRph D X u Y.hK) hI (hRF D X) (hEF D X)
    hKL (level_subgroup_measurable X Y.hK hKL)

theorem inHHC_holds_of' (hS : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), KsetSplit X u)
    (hN : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), UnipotentConjugateInLevel X u)
    (hL : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), RatLevi X u)
    (hP : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), PsiProd X u)
    (hRph : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), PserRph X u hK) :
    Formalism.L2.SG.Full.InHHC :=
  inHHC_holds_of hS hN hL hP (fun _ X => fundBridge_holds X) (fun _ X u hK => pserMeas_holds X u hK) hRph
    (fun _ X => regular_fixes_invariant_L2 X) (fun _ X => idempotent_fixes_invariant_L2 X)

theorem inHHC_holds_of'' (hS : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), KsetSplit X u)
    (hN : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), UnipotentConjugateInLevel X u)
    (hL : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), RatLevi X u)
    (hP : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), PsiProd X u) :
    Formalism.L2.SG.Full.InHHC :=
  inHHC_holds_of' hS hN hL hP fun _ X u hK => pserRph_holds X u hK

theorem inHHC_holds : Formalism.L2.SG.Full.InHHC :=
  inHHC_holds_of'' (fun _ X u => ksetSplit_holds X u) (fun _ X u => unipotent_in_level X u)
    (fun _ X u => ratLevi_holds X u) (fun _ X u => psiProd_holds X u)

end Formalism.L2.SG.Pf
end
end

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.Pf Formalism.L2.SG.TermOp.Vanish

namespace Formalism.L2.SG.Closed

section Steps

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)

theorem PsiDd_holds : Formalism.L2.SG.Pf.PsiDd X := Formalism.L2.SG.Pf.psiDd_holds X
theorem unipotent_in_level_subgroup : Formalism.L2.SG.PoincareInHH.Cut.UnipotentConjugateInLevel X u := Formalism.L2.SG.Pf.Level.unipotent_in_level_of_psi (PsiDd_holds X)
theorem RatLevi_holds : Formalism.L2.SG.PoincareInHH.Cut.RatLevi X u := Formalism.L2.SG.Pf.ratLevi_holds X u
theorem KsetSplit_holds : Formalism.L2.SG.PoincareInHH.Cut.KsetSplit X u := Formalism.L2.SG.Pf.ksetSplit_holds X u
theorem NeatKu_holds (hK : X.LevelSubgroupCharacter) : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u hK := Formalism.L2.SG.PoincareInHH.Cut.neatKu_of_gamUnipKu (X := X) (u := u) (hK := hK)
  (hL := Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X u) (hU := Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X u hK)

end Steps

theorem HFiniteC_holds : HFiniteC := fun _ X u => Formalism.L2.SG.Pf.hFinite_holds X u
theorem nilradical_conj_level : NilradicalConjLevel := Formalism.L2.SG.Pf.nilradical_conj_level'
theorem ChiTrivialC_holds : ChiTrivialC := Formalism.L2.SG.Pf.chiTrivialC_outright
theorem AvgCore_holds : AvgCore := Formalism.L2.SG.TermOp.Vanish.avgCore

theorem SlabCoverC_holds : Formalism.L2.SG.Pf.Slab.SlabCoverC :=
  Formalism.L2.SG.Pf.SlabCoverPf.slab_covering_of_strong_approx Formalism.L2.SG.Pf.SlabNDensePf.nilradical_strong_approximation nilradical_conj_level
    (fun _ X u => RatLevi_holds X u) (fun _ X => PsiDd_holds X)

theorem KExpansionC_holds : KExpansionC :=
  Formalism.L2.SG.Pf.kExpansionC_holds_of SlabCoverC_holds Formalism.L2.SG.Pf.RegroupPf.regroupC_all
    (fun _ X Y u => NeatKu_holds X u Y.hK) (fun _ X => Formalism.L2.SG.Pf.fundBridge_holds X)
    (fun _ X u hK => Formalism.L2.SG.Pf.pserMeas_holds X u hK)

theorem PuLinearC_holds : PuLinearC := Formalism.L2.SG.Pf.puLinearC

theorem FundExistsC_holds : FundExistsC := Formalism.L2.SG.Pf.fundExistsC_holds

theorem OOFundIndepC_holds : OOFundIndepC := Formalism.L2.SG.Pf.ooFundIndepC_of_nconj Formalism.L2.SG.Pf.nilradical_conj_level'

theorem AmpWellDefC_holds : AmpWellDefC := Formalism.L2.SG.Pf.ampWellDefC_of_nconj Formalism.L2.SG.Pf.nilradical_conj_level'

theorem VolPosC_holds : VolPosC := Formalism.L2.SG.Pf.volPosC_of'' Formalism.L2.SG.Pf.noCofiniteC_holds HFiniteC_holds

theorem LemmaVC_holds : LemmaVC := Formalism.L2.SG.Pf.lemmaVC_of_rest Formalism.L2.SG.TermOp.Vanish.avgCore Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds
  Formalism.L2.SG.NonRelPf.nonRelCharC_holds

theorem OOIntAllC_holds (h : Formalism.L2.SG.Pf.OOLintSumC) : OOIntAllC := Formalism.L2.SG.Pf.ooIntAllC_holds_of h

theorem AbsConvC_holds (h : Formalism.L2.SG.Pf.OOLintSumC) : AbsConvC := Formalism.L2.SG.Pf.absConvC_holds_of h

theorem FoldOKC_holds (hFL : Formalism.L2.SG.Pf.FinLeviC) : FoldOKC :=
  Formalism.L2.SG.Pf.foldOKC_holds_of (fun _ X u => KsetSplit_holds X u) (fun _ X u => unipotent_in_level_subgroup X u)
    (fun _ X u => RatLevi_holds X u) Formalism.L2.SG.Pf.psiProd_all
    (Formalism.L2.SG.Pf.iUnfoldAll_of hFL Formalism.L2.SG.Pf.noCocompactC_holds Formalism.L2.SG.Pf.SlabNDensePf.nilradical_strong_approximation)

theorem InHHC_holds : InHHC := Formalism.L2.SG.Pf.inHHC_holds

theorem NeatC_holds : Formalism.L2.SG.TermOp.IdBlocks.NeatC := fun _ X Y u => NeatKu_holds X u Y.hK

theorem IdCellDiagC_holds : IdCellDiagC :=
  Formalism.L2.SG.Pf.idCellDiagC_of_steps3 Formalism.L2.SG.Pf.nLamNinf_holds VolPosC_holds Formalism.L2.SG.Pf.idMeetOneC_holds
    Formalism.L2.SG.Pf.idMeetPhaseC_holds Formalism.L2.SG.Pf.idMeetVolC_holds NeatC_holds

end Formalism.L2.SG.Closed
