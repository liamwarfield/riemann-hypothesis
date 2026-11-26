module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.NilpotentMeasureRecursion
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.WuDefiniteHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptedBasisEveryPlace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKu
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.VanishingOrbitalPoints
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarNMove
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataColumns

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLeaves
noncomputable section

open MeasureTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace Formalism.L2.SG.Pf.MassDataX

theorem hinfCompact_holds : MassDataMassesW.HinfCompact :=
  PIW.MassDataColumns.hinfCompact_of Formalism.L2.SG.Closed.AdBridgeIso_holds Formalism.L2.SG.Pf.MeasInfW.measure_isomorphism_at_infinity
    Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_recursion (fun X u => Formalism.L2.SG.Pf.hinf_compact X u)

theorem finHA_eq_eFin {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf) :
    finHA X hb x = Formalism.L2.SG.Pf.Meas.eFin X.B.I hb x := rfl

theorem kCompactOpen_holds : MassDataMassesW.KCompactOpen := by
  intro D X
  have hb := Formalism.L2.SG.Closed.AdBridgeIso_holds X.B.I
  have hs : Function.Surjective (finHA X hb) := by
    intro y
    obtain ⟨x, hx⟩ := (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).surjective y
    exact ⟨x, by rw [finHA_eq_eFin]; exact hx⟩
  have himg : ((MassDataMassesW.KX X : Subgroup _) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) =
      Formalism.L2.SG.Pf.Meas.eFin X.B.I hb '' X.B.I.Kset := by
    rw [MassDataMassesW.KX, PIW.MassDataColumns.kf_eq_image X hb hs]
    rfl
  rw [himg]
  exact ⟨(Formalism.L2.SG.Closed.AutKCompact_holds X.B.I).image (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).continuous,
    (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).isOpenMap _ (Formalism.L2.SG.Pf.kset_open X.B.I)⟩

theorem dc_finite_mono {G : Type} [Group G] (Γ K' K : Subgroup G) (h : K' ≤ K)
    (hf : Finite (DoubleCoset.Quotient (Γ : Set G) (K' : Set G))) :
    Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) := by
  haveI : Finite (Quotient (DoubleCoset.setoid (Γ : Set G) (K' : Set G))) := hf
  have hr : ∀ a b : G, (DoubleCoset.setoid (Γ : Set G) (K' : Set G)) a b → (DoubleCoset.setoid (Γ : Set G) (K : Set G)) a b := by
    intro a b hab
    rw [DoubleCoset.rel_iff] at hab ⊢
    obtain ⟨x, hx, y, hy, hxy⟩ := hab
    exact ⟨x, hx, y, h hy, hxy⟩
  show Finite (Quotient (DoubleCoset.setoid (Γ : Set G) (K : Set G)))
  refine Finite.of_surjective (Quotient.map' id hr) ?_
  intro q
  induction q using Quotient.inductionOn' with
  | h a => exact ⟨Quotient.mk'' a, rfl⟩

theorem hermitian_level_le {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) :
    PIW.MassDataColumns.unitaryLevelClosureSubgroup X hb u ≤ MassDataMassesW.KH X u := by
  rw [PIW.MassDataColumns.unitaryLevelClosureSubgroup, Subgroup.closure_le]
  rintro ⟨h, hh⟩ hk
  obtain ⟨y, ⟨k, hk2, rfl⟩, hy⟩ := hk
  show h ∈ MassDataMassesW.KX X
  have hy' : finHA X hb (X.xu u) * finHA X hb k * (finHA X hb (X.xu u))⁻¹ = h := hy
  rw [← hy']
  have hxu : finHA X hb (X.xu u) ∈ MassDataMassesW.KX X :=
    (PIW.MassDataColumns.finHA_mem_Kf_iff X hb _).2 (X.xu_K u)
  have hkK : finHA X hb k ∈ MassDataMassesW.KX X :=
    (PIW.MassDataColumns.finHA_mem_Kf_iff X hb _).2 ((Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 k hk2)
  exact (MassDataMassesW.KX X).mul_mem ((MassDataMassesW.KX X).mul_mem hxu hkK) ((MassDataMassesW.KX X).inv_mem hxu)

theorem classFinite_holds : MassDataMassesW.ClassFinite := by
  intro D X u
  have hb := Formalism.L2.SG.Closed.AdBridgeIso_holds X.B.I
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hF := Formalism.L2.SG.Closed.ClassFin_holds X u hK
  have hc := PIW.MassDataColumns.class_sets_equal_card X hb hK u (Formalism.L2.SG.Closed.AdBridgeGF_holds X.B.I)
    (Formalism.L2.SG.Closed.level_subgroup_properties X)
  have hne : Nonempty (Formalism.L2.SG.ColsDim.Classes (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u) (Formalism.L2.SG.PoincareInHH.PoincareSetting.Ku X u hK)) := inferInstance
  haveI : Finite (Formalism.L2.SG.ColsDim.Classes (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u) (Formalism.L2.SG.PoincareInHH.PoincareSetting.Ku X u hK)) := hF
  have hfin : Finite (PIW.MassDataColumns.ClsHA X hb u) := by
    have hpos : 0 < Nat.card (Formalism.L2.SG.ColsDim.Classes (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u) (Formalism.L2.SG.PoincareInHH.PoincareSetting.Ku X u hK)) :=
      Nat.card_pos
    exact Nat.finite_of_card_ne_zero (hc ▸ hpos.ne')
  exact dc_finite_mono _ _ _ (hermitian_level_le X hb u) hfin

end Formalism.L2.SG.Pf.MassDataX
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXColumns
namespace Formalism.L2.SG.Pf.MassDataX

open Formalism.L2.SG.TypedSets

theorem inColumnsAt_holds :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn),
      InColumnsAt X hb hK FdN FdN' u u' X0 L A :=
  massDataColumns_of' Formalism.L2.SG.Closed.AdBridgeIso_holds Formalism.L2.SG.Closed.AdBridgeGF_holds
    Formalism.L2.SG.Closed.AdBridgeK_holds
    (fun X u hK => Formalism.L2.SG.PoincareInHH.Cut.neatKu_of_gamUnipKu X u hK
      (Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X u) (Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X u hK))
    (fun X u hK => Formalism.L2.SG.Closed.ClassFin_holds X u hK)
    (fun I hb => ⟨Formalism.L2.SG.Pf.Meas.eFin I hb, fun _ => rfl⟩)
    (fun X => Formalism.L2.SG.Pf.level_subgroup_compact_open X)
    Formalism.L2.SG.Closed.AutKCompact_holds
    Formalism.L2.SG.Pf.MeasInfW.measure_isomorphism_at_infinity Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_recursion
    (fun X u => Formalism.L2.SG.Pf.hinf_compact X u)

end Formalism.L2.SG.Pf.MassDataX
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RepAtTup
noncomputable section

namespace Formalism.L2.SG.Pf.FibPart

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def RepIn (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) : Prop :=
  ∃ F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z,
    Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls F'

def Pre : Prop :=
  (∀ p, Agree δ M p) ∧ (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] ∧ PrimeHyp D u (Tu D u') ∧
    PairVal.NormRepExists D u u' F0 what₂ ∧ IsRowReps D F0 what₂ ∧ EligRel u u' F0 what₂

def TupFun : Prop :=
  Pre M δ u u' F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (Z : PairVal.MatR D),
    EligAt γ w → AtMat w Z → RepIn u u' F0 what₂ γ Z → locT M δ γ = tupZ M δ u u' Z

def RepAtTup : Prop :=
  Pre M δ u u' F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)),
    Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 → ∀ Z : PairVal.MatR D, AtMat w Z → EligAt γ w →
      locT M δ γ = tupZ M δ u u' Z → RepIn u u' F0 what₂ γ Z

def OrbZT : Prop :=
  Pre M δ u u' F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (Z : PairVal.MatR D),
    EligAt γ w → AtMat w Z → RepIn u u' F0 what₂ γ Z →
      (PairVal.orbT D u u' F0 what₂ γ (zT γ)).encard = (PairVal.orbT D u u' F0 what₂ γ Z).encard

end Steps

end Formalism.L2.SG.Pf.FibPart
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaRep
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem repG_holds : RepG u u' F0 what₂ := by
  intro hC γ Z hZ
  obtain ⟨w, hγ, -⟩ := hZ
  have hN := normRepExists_ctx hC
  obtain ⟨⟨hgen, hG⟩, hat⟩ := hγ
  obtain ⟨y, hy⟩ := hN γ w hat (eligRel_holds γ w ⟨⟨hgen, hG⟩, hat⟩) hgen
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
  have hn : nrep γ = some hex.choose := dif_pos hex
  have hrep : repF γ = hex.choose.2.1 := by unfold repF; rw [hn]
  obtain ⟨⟨hPD, hmk⟩, -⟩ := hex.choose_spec
  refine ⟨⟨hex.choose.2.1, hPD⟩, hrep.symm, hmk, ?_⟩
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 γ.lam hrow
  have hrel := (hEq ⟨hex.choose.2.1, hPD⟩ (Quot.out γ.cls)).1 (hmk.trans (Quot.out_eq γ.cls).symm)
  have e := Formalism.L2.SG.Pf.g_value_function _ _ _ _ _ hrel
  exact fun h0 => hG (e.symm.trans h0)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefDens
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DensCong : Prop :=
  ∀ (F E : Type) {_ : Field F} {_ : ValuativeRel F} {_ : TopologicalSpace F} {_ : CommRing E} {_ : Algebra F E}
    {_ : TopologicalSpace E} {_ : MeasurableSpace E} (M : Loc.Model F E) (V : Type) {_ : AddCommGroup V}
    {_ : Module E V} (H : Loc.HermSp M V) (ϖ : 𝒪[F]) (abelian₂ : Submodule M.L.O V) (ι : Type) {_ : Fintype ι}
    {_ : DecidableEq ι} (G A : Matrix ι ι E),
    (∀ i j, A i j ∈ M.L.O) → (∃ y ∈ M.L.O, A.det * y = 1) →
      H.dens ϖ abelian₂ ((A.map M.L.cj).transpose * G * A) = H.dens ϖ abelian₂ G

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

def GaPlusTh : Prop :=
  (∀ p, Agree δ M p) → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → PrimeHyp D u (Tu D u') →
  ∀ (w w' : Point D.host.E (D.R.rS + 1)) (Z Z' : PairVal.MatR D), kind w = kind w' → AtMat w Z → AtMat w' Z' →
  ∀ p, FCount.thZ M δ u u' w Z p ≠ none → FCount.thZ M δ u u' w Z p = FCount.thZ M δ u u' w' Z' p →
    ∃ A : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ i j, A i j ∈ (M p).L.O) ∧ (∃ y ∈ (M p).L.O, A.det * y = 1) ∧
      CntLocal.GaPlus M δ p (CntLocal.Tn u) (CntLocal.Tn u') Z' =
        (A.map (M p).L.cj).transpose * CntLocal.GaPlus M δ p (CntLocal.Tn u) (CntLocal.Tn u') Z * A

end Steps

theorem densTh_of {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : CntLocal.LocSp D M} {u u' : D.what₂.Word}
    (hC : DensCong) (hG : GaPlusTh M δ u u') : FCount.DensTh M δ L u u' := by
  intro hA hT hPH ϖ _ w w' Z Z' hk hZ hZ' p hne heq
  obtain ⟨A, hAO, hAd, hGa⟩ := hG hA hT hPH w w' Z Z' hk hZ hZ' p hne heq
  unfold CntLocal.densP
  rw [hGa]
  exact (hC (D.s.atP p).Fp (D.s.atP p).Ep (M p) (L.V p) (L.H p) (ϖ p) (CntLocal.lattice₂ L p (VS D).L0)
    (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (CntLocal.GaPlus M δ p (CntLocal.Tn u) (CntLocal.Tn u') Z) A hAO hAd).symm

end Formalism.L2.SG.Pf.Coef
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NotDvdDiff
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem not_dvd_diff (v : HeightOneSpectrum (𝓞 D.host.F)) (i : Fin 2)
    (hv : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  have hp := D.host.g_prime i
  obtain ⟨he, -⟩ := Formalism.L2.SG.Pf.TypedLoc.tower_ef D.host.F D.host.E hp (D.nd.g_split i) v hv
  have hvq : v.asIdeal ∈ (Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 D.host.F) := by
    rw [Formalism.L2.SG.Pf.TypedLoc.primesOver_eq D.host.F hp]; exact ⟨v, hv, rfl⟩
  have : v.asIdeal.LiesOver (Ideal.span {((D.host.g i : ℕ) : ℤ)}) := hvq.2
  have : v.asIdeal.IsPrime := v.isPrime
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp)] at he
  rw [not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain]
  exact he

theorem diff_avoid (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ∃ t ∈ differentIdeal ℤ (𝓞 D.host.F), algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∉ P.asIdeal := by
  have hPp := P.isPrime
  let v : HeightOneSpectrum (𝓞 D.host.F) :=
    ⟨P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.IsPrime.comap _, by
      intro hb
      apply P.ne_bot
      have hg0 : ((gS D : ℕ) : 𝓞 D.host.F) ∈ P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
        rw [Ideal.mem_comap, map_natCast]; exact hP
      rw [hb, Ideal.mem_bot] at hg0
      exfalso
      have : (gS D : ℕ) ≠ 0 := by
        unfold Lat.gS; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
      exact this (by exact_mod_cast hg0)⟩
  have hgi : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    have hg : ((gS D : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
      show _ ∈ P.asIdeal.comap _
      rw [Ideal.mem_comap, map_natCast]; exact hP
    unfold Lat.gS at hg
    rw [Nat.cast_mul] at hg
    rcases v.isPrime.mem_or_mem hg with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hgi
  have hnd := not_dvd_diff v i hi
  by_contra hc
  push Not at hc
  exact hnd (Ideal.dvd_iff_le.2 fun t ht => hc t ht)

end Formalism.L2.SG.Pf.FibD
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrGlobOfFull
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardPiOfUnique
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.FrameGlobalPatching

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem card_pi_of_unique {ι : Type*} {α : ι → Type*} (T : Finset ι) (h : ∀ i ∉ T, Nonempty (Unique (α i))) :
    Nat.card (∀ i, α i) = ∏ᶠ i, Nat.card (α i) := by
  haveI : ∀ i : {i // i ∉ T}, Unique (α i) := fun i => (h i.1 i.2).some
  rw [Nat.card_congr (Equiv.piEquivPiSubtypeProd (fun i => i ∈ T) α), Nat.card_prod,
    Nat.card_unique (α := ∀ i : {i // i ∉ T}, α i), mul_one, Nat.card_pi]
  rw [finprod_eq_prod_of_mulSupport_subset (s := T)]
  · exact (Finset.prod_coe_sort T (fun i => Nat.card (α i)))
  · intro i hi
    by_contra hT
    haveI := (h i hT).some
    exact hi Nat.card_unique

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def LocFullC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
  ∀ Z : PairVal.MatR D, AtMat w' Z →
  ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    ZhatL (lf D F0) F'₂ = Z →
    (∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (φ p) (φ' p)) →
    ∀ p, ∀ M ∈ locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p),
      ∃ Λ' : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsFullLattice D.host.E Λ' ∧ M = lattice₂ D Zd.M p Λ'

variable {Zd u u' F0 what₂}

theorem patchC_of (hP : LatPatch) (hL : LocFullC Zd u u' F0 what₂) : PatchC Zd u u' F0 what₂ := by
  intro γ w hγ w' hG' hk Z hZ F'₂ φ φ' hF hT hC
  obtain ⟨Λ₀, hΛ₀, hfin⟩ := hC
  have hfull := hL γ w hγ w' hG' hk Z hZ F'₂ φ φ' hF hT
  set S : ∀ p : PlF D, Set (Submodule (Zd.M p).L.O (Vp D p)) :=
    fun p => locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p) with hS
  have hex : ∀ f : ∀ p, S p, ∃! Λ : Submodule (𝓞 D.host.E) (VS D).V,
      Submodule.IsFullLattice D.host.E Λ ∧ ∀ p, lattice₂ D Zd.M p Λ = (f p).1 := fun f =>
    hP D Zd Λ₀ hΛ₀ (fun p => (f p).1) (fun p => hfull p _ (f p).2)
      (hfin.subset fun p hp hS' => hp (Set.mem_singleton_iff.1 ((Set.ext_iff.1 hS' (f p).1).1 (f p).2)))
  let e : GlobSet Zd γ F'₂ φ φ' ≃ ∀ p, S p :=
    { toFun := fun Λ p => ⟨lattice₂ D Zd.M p Λ.1, Λ.2.2 p⟩
      invFun := fun f => ⟨(hex f).choose, (hex f).choose_spec.1.1, fun p => by
        rw [(hex f).choose_spec.1.2 p]; exact (f p).2⟩
      left_inv := fun Λ => by
        apply Subtype.ext
        exact (hex _).unique (hex _).choose_spec.1 ⟨Λ.2.1, fun p => rfl⟩
      right_inv := fun f => by
        funext p
        exact Subtype.ext ((hex f).choose_spec.1.2 p) }
  rw [Nat.card_congr e]
  obtain ⟨T, hTs⟩ := hfin.exists_finset
  refine card_pi_of_unique (α := fun p => S p) T (fun p hp => ?_)
  have hsing : S p = {lattice₂ D Zd.M p Λ₀} := by
    by_contra hne
    exact hp ((hTs p).2 hne)
  rw [hsing]
  exact ⟨Set.uniqueSingleton _⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching
end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}

theorem patchC_of_full (hL : LocFullC Zd u u' F0 what₂) : PatchC Zd u u' F0 what₂ :=
  patchC_of Formalism.L2.SG.Pf.LocalDenominators.latPatch_holds hL

end Formalism.L2.SG.Pf.FrameGlobalPatching
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdN
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem bwdN_zorth : F0.z ∈ orth (VS D) (Xsp (lf D F0)) :=
  (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
    rw [BwdNA.hsw (VS D) F0.z x]
    have h := NMoveP.hT_f_X F0 (Fin.last D.R.rS) hx
    rw [NMoveP.fvecL] at h
    rw [h, star_zero]

theorem bwdN_znotX : F0.z ∉ Xsp (lf D F0) := by
  intro h
  have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 (bwdN_zorth (F0 := F0)) F0.z h
  rw [F0.z_norm, neg_eq_zero] at h0
  have hT := (D.mem u).A.T_prime.ne_zero
  exact hT (Nat.cast_eq_zero.1 h0)

variable (u u' F0 what₂)

set_option maxHeartbeats 1000000 in
theorem bwdN_holds : BwdN Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hmem₂
  obtain ⟨hΛ₂, hloc₂⟩ := hmem₂
  obtain ⟨-, hT2, hφ⟩ := hS
  have hrow := hC.2.1.1 γ.lam γ.mem
  have : Submodule.IsFullLattice D.host.E γ.lam := hrow.1.1
  have ht1 := fun p => (hT2 p).1
  have hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a) := fun p a =>
    BwdNP.unit_of_frame Zd p γ (ht1 p).1.2.1 a
  have hSDl : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p γ.lam) := fun p => (ht1 p).1.1
  have hSDl₂ : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ₂) := fun p => (hloc₂ p).1.1.1
  have hpr : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f := fun p => (ht1 p).1.2.1.1
  have hpr₂ : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := fun p => (hloc₂ p).1.1.2.1.1
  have hLset : ∀ p, (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f =
      (locH Zd p).Lset (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := fun p => by
    have h := (hloc₂ p).2.1
    rw [hφ p] at h
    rw [← h]
    exact (Set.image_id _).symm
  have hSD := BwdNP.sd_of_loc Zd (Λ := γ.lam) inferInstance hSDl
  have hSD₂ := BwdNP.sd_of_loc Zd (Λ := Λ₂) inferInstance hSDl₂
  set X := Xsp (lf D F0) with hXdef
  have hXiso : ∀ x ∈ X, ∀ y ∈ X, (VS D).hT x y = 0 := fun x hx y hy => NMoveP.hT_X_X F0 hx hy
  have hXX : ∀ {w : (VS D).V}, w ∈ orth (VS D) (orth (VS D) X) → w ∈ X := fun {w} hw =>
    BwdNA.mem_of_orth_orth (VS D) X fun v hv => by
      rw [BwdNA.hsw (VS D) v w, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, star_zero]
  have hXo := BwdNA.X_le_orth (VS D) X hXiso
  have hL : ∀ x ∈ Λ₂, x ∈ orth (VS D) X → ∃ y ∈ γ.lam, y - x ∈ X := fun x hx hxo => by
    obtain ⟨w, hw, hxw⟩ := BwdNA.dual_sum (VS D) γ.lam inferInstance hSD (orth (VS D) X) x
      (fun m hmΛ hmU => BwdNP.pair_int Zd γ hSDl (fun p => (hLset p).symm.subset) hx hxo hmΛ hmU)
    refine ⟨w, hw, ?_⟩
    have h2 := X.neg_mem (hXX hxw)
    rwa [neg_sub] at h2
  have hL' : ∀ y ∈ γ.lam, y ∈ orth (VS D) X → ∃ x ∈ Λ₂, x ∈ orth (VS D) X ∧ y - x ∈ X := fun y hy hyo => by
    obtain ⟨w, hw, hyw⟩ := BwdNA.dual_sum (VS D) Λ₂ inferInstance hSD₂ (orth (VS D) X) y
      (fun m hmΛ hmU => BwdNP.pair_int Zd γ hSDl₂ (fun p => (hLset p).subset) hy hyo hmΛ hmU)
    have hX1 := hXX hyw
    refine ⟨w, hw, ?_, hX1⟩
    have e : w = y - (y - w) := by abel
    rw [e]
    exact (orth (VS D) X).sub_mem hyo (hXo hX1)
  have hXm : ∀ x ∈ X, x ∈ Λ₂ ↔ x ∈ γ.lam := fun x hx =>
    ⟨BwdNP.memX Zd γ hpr₂ hpr inferInstance hu hx, BwdNP.memX Zd γ hpr hpr₂ inferInstance hu hx⟩
  have hy := BwdNP.exists_y Zd γ (Λ₂ := Λ₂) inferInstance hSD₂ hpr₂ hu bwdN_znotX
  have htr : ∃ c : D.host.E, IsIntegral ℤ c ∧ c + star c = 1 := by
    obtain ⟨c, hc⟩ := D.host.exists_trace_one
    refine ⟨(c : D.host.E), RingOfIntegers.isIntegral_coe c, ?_⟩
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host)]
    exact hc
  obtain ⟨n, hiso, hnX, hnz, hno, himg⟩ := BwdNA.main (VS D) X hXiso F0.z bwdN_zorth γ.lam Λ₂
    inferInstance inferInstance hSD hSD₂ hXm
    (BwdNP.z_mem Zd γ (Λ := γ.lam) inferInstance hpr) (BwdNP.z_mem Zd γ (Λ := Λ₂) inferInstance hpr₂) hL hL' hy htr
  refine ⟨n, ⟨hiso, fun j x hx => ?_, hno, fun a => hnX _ (Submodule.subset_span ⟨a, rfl⟩), hnz⟩, himg⟩
  have hxX : x ∈ X := Submodule.span_mono (Set.image_subset_range _ _) hx
  rw [hnX x hxX, sub_self]
  exact zero_mem _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end
