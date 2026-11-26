module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalFactorizationOfWeilDualPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelHeightFinitePlaceDoublingEmbeddingLeOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchingTranslatesBottom
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairTranslate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselAwayPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairScalar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairIdentity
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChartParahoricLevelStabiliserHeight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceTwistSchwartzBruhat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRightOfRapidDecayUnramifi
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRightOfRapidDecayUnramifi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.Core.Rk.IP

theorem eulerRight_of_unramifiedDoubling : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.UnramifiedDoublingGL →
    ∀ D : D7, GlobalTheory.Core.Rk.IP.EulerRight D := by
  intro p2 p6 D
  have hU := GlobalTheory.InertZeta.unramDoublingInert
  have hPBi : ParamBoundOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := GlobalTheory.T.sphericalParameterBound_nonsplit_places hU D
  have hPB : ParamBoundOn D (fun _ => True) := by
    intro A L hL v _
    by_cases h : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v
    · exact GlobalTheory.Core.Rk.BdSplit.paramBound_split D A L hL v h
    · exact hPBi A L hL v h
  have hLZ : LocalZetaOn D (fun _ => True) := by
    intro A L hL χ b hχ hr v _
    by_cases h : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v
    · exact GlobalTheory.Core.Rk.IP.localZetaOn_split p6 D A L hL χ b hχ hr v h
    · exact GlobalTheory.LocZetaInertAd.localZetaOn_inert hU D hPBi A L hL χ b hχ hr v h
  exact GlobalTheory.Core.Rk.EulerProd.eulerRight p2 D (GlobalTheory.T.doublingSphericalFactorization_of_weilDualPair GlobalTheory.weilRepresentationUnitaryPair D) hLZ hPB

end GlobalTheory.Core.Rk.IP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRightOfRapidDecayUnramifiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingEulerProductFarRight_of_rapidDecay_unramified : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, GlobalTheory.Core.Rk.IP.EulerRight D := by
  first | exact @GlobalTheory.Core.Rk.IP.eulerRight_of_unramifiedDoubling | exact GlobalTheory.Core.Rk.IP.eulerRight_of_unramifiedDoubling | (intros; apply GlobalTheory.Core.Rk.IP.eulerRight_of_unramifiedDoubling <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightFunProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightFunProperties
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP
variable {D : D7} (A : HSp D) (L : Lat A) (a : GL (Fin A.rank) (AE D))

theorem hgtL_eq_prod (hL : IsSelfDualC A L) (ha : IsMaj A a) (g : GA D A) : hgtL A L a g = (∏ w, hgtArch D.sp.cm.sig (dblSp A).gram w (Formalism.UG.bc (compInf _ _ w) a)
      (ioH _ D.sp.cm.sig (gram_hdbl A) (projArch D.sp.cm.sig A.gram w g, 1))) *
      ∏ᶠ v, hgtFin D.sp.cm.sig (dblSp A).gram L v (ioH _ D.sp.cm.sig (gram_hdbl A) (proj D.sp.cm.sig A.gram v g, 1)) := by
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A L a hL ha
  simpa only [hgtL, io, proj_ioH, projArch_ioH, map_one] using
    hI.hgtAd_eq (isCMExt_host D) (io A (g, 1))

theorem isOpen_openOff (hL : IsSelfDualC A L) (Sf : Finset (FinPl D)) : IsOpen (openOff A L Sf) := by
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  let H : Subgroup (GA D A) := ⨅ (v) (_ : v ∉ Sf), (stabLoc D.sp.cm.sig A.gram L v).comap (proj D.sp.cm.sig A.gram v)
  have hH : (H : Set (GA D A)) = openOff A L Sf := by
    ext g
    simp [H, openOff, Subgroup.mem_iInf, Subgroup.mem_comap]
  rw [← hH]
  refine Subgroup.isOpen_mono (H₁ := levelOpen D.sp.cm.sig A.gram L) (fun g hg => ?_) (isOpen_levelOpen _ _ _)
  simp only [H, Subgroup.mem_iInf, Subgroup.mem_comap]
  exact fun v _ => (mem_levelOpen.1 hg) v

theorem continuous_hgtL (hL : IsSelfDualC A L) (ha : IsMaj A a) : Continuous (hgtL A L a) := by
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  haveI := t2Space_adeleRing' (F := D.host.F)
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A L a hL ha
  exact (hI.continuous_hgtH continuous_absE (isCompact_KAd (isCMExt_host D))).comp
    ((continuous_io A).comp (continuous_id.prodMk continuous_const))

theorem hgtL_le_one (hL : IsSelfDualC A L) (ha : IsMaj A a) (g : GA D A) : hgtL A L a g ≤ 1 := by
  rw [hgtL_eq_prod A L a hL ha g]
  refine mul_le_one' (Finset.prod_le_one' fun w _ => ?_) ?_
  · have := GlobalTheory.T.doublingHeightAtRealPlace_le_one D A a ha w (projArch D.sp.cm.sig A.gram w g)
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW] using this
  · by_cases hf : (Function.mulSupport fun v => hgtFin D.sp.cm.sig (dblSp A).gram L v
        (ioH _ D.sp.cm.sig (gram_hdbl A) (proj D.sp.cm.sig A.gram v g, 1))).Finite
    · rw [finprod_eq_prod _ hf]
      exact Finset.prod_le_one' fun v _ => GlobalTheory.T.siegelHeightFinitePlace_doublingEmbedding_le_one D A L hL v _
    · rw [finprod_of_infinite_mulSupport hf]

theorem hgtL_eq_prod_off (hL : IsSelfDualC A L) (ha : IsMaj A a) (Sf : Finset (FinPl D)) (g : GA D A)
    (hg : g ∈ openOff A L Sf) : (hgtL A L a g : ℝ) = (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW A a w (projArch D.sp.cm.sig A.gram w g)) *
      ∏ v ∈ Sf, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v (proj D.sp.cm.sig A.gram v g) := by
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  rw [hgtL_eq_prod A L a hL ha g]
  have hsub : (Function.mulSupport fun v => hgtFin D.sp.cm.sig (dblSp A).gram L v
      (ioH _ D.sp.cm.sig (gram_hdbl A) (proj D.sp.cm.sig A.gram v g, 1))) ⊆ (Sf : Set (FinPl D)) := by
    intro v hv
    by_contra hvS
    exact hv (hgtH_of_mem (continuous_absEv v) (isCompact_KFin v)
      ((ioH_mem_KFin (gram_hdbl A)).2 ⟨hg v hvS, one_mem _⟩))
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  push_cast
  rfl

theorem hgtL_props : ∀ (D : D7) (A : HSp D) (L : Lat A) (a : GL (Fin A.rank) (AE D)), IsSelfDualC A L → IsMaj A a → Continuous (hgtL A L a) ∧ (∀ g, 0 < hgtL A L a g ∧ hgtL A L a g ≤ 1) ∧ ∀ (Sf : Finset (FinPl D)), IsOpen (openOff A L Sf) ∧ ∀ g ∈ openOff A L Sf, (hgtL A L a g : ℝ) = (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW A a w (projArch D.sp.cm.sig A.gram w g)) * ∏ v ∈ Sf, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v (proj D.sp.cm.sig A.gram v g) := by
  intro D A L a hL ha
  exact ⟨continuous_hgtL A L a hL ha, fun g => ⟨hgtH_pos _, hgtL_le_one A L a hL ha g⟩,
    fun Sf => ⟨isOpen_openOff A L hL Sf, fun g hg => hgtL_eq_prod_off A L a hL ha Sf g hg⟩⟩

end GlobalTheory.Core.Rk.IP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightFunPropertiesStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledLatticeHeightFun_properties : ∀ (D : D7) (A : HSp D) (L : Lat A) (a : GL (Fin A.rank) (AE D)), IsSelfDualC A L → IsMaj A a → Continuous (hgtL A L a) ∧ (∀ g, 0 < hgtL A L a g ∧ hgtL A L a g ≤ 1) ∧ ∀ (Sf : Finset (FinPl D)), IsOpen (openOff A L Sf) ∧ ∀ g ∈ openOff A L Sf, (hgtL A L a g : ℝ) = (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW A a w (projArch D.sp.cm.sig A.gram w g)) * ∏ v ∈ Sf, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v (proj D.sp.cm.sig A.gram v g) := by
  first | exact @GlobalTheory.Core.Rk.IP.hgtL_props | exact GlobalTheory.Core.Rk.IP.hgtL_props | (intros; apply GlobalTheory.Core.Rk.IP.hgtL_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselCompatibility
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

theorem GlobalTheory.MiTop.levFn_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    {LL : Type} [CommRing LL] (hc : Formalism.BasicNotions.CMData F E) (J : Matrix (Fin n) (Fin n) E)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : Formalism.L2.DIV.LevDat E LL n) {x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ Formalism.L2.DIV.lev hc J β L) (hy : y ∈ Formalism.L2.DIV.lev hc J β L) :
    Formalism.L2.DIV.levFn β L (x * y * x⁻¹) = Formalism.L2.DIV.levFn β L y := by
  have e := congrArg (Formalism.L2.DIV.levChar hc J β L)
    (show (⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : Formalism.L2.DIV.lev hc J β L)⁻¹ : Formalism.L2.DIV.lev hc J β L) =
      ⟨x * y * x⁻¹, _⟩ from rfl)
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at e
  exact e.symm

namespace GlobalTheory.MiTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end GlobalTheory.MiTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCoefficientSplitsLocalFactorTwistPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCoefficientSplitsLocalFactorTwistPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwistCoef

theorem conj_unit {u : ℂˣ} (h : ‖(u : ℂ)‖ = 1) : conj (u : ℂ) = ((u⁻¹ : ℂˣ) : ℂ) := by
  have hu : (u : ℂ) ≠ 0 := u.ne_zero
  rw [Units.val_inv_eq_inv_val, Complex.inv_def, Complex.normSq_eq_norm_sq, h]
  simp

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

theorem datum_inv_conj (μ : kˣ →* ℂˣ) (hμ : ∀ d, ‖(μ d : ℂ)‖ = 1) (z : Matrix (A ⊕ D) (A ⊕ D') k) :
    datum μ⁻¹ z = conj (datum μ z) := by
  unfold datum
  split_ifs with h
  · have h1 : ‖(((μ (Units.mk0 _ h.det_ne))⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
      simp [Units.val_inv_eq_inv_val, norm_inv, hμ]
    rw [conj_unit h1]
    simp
  · simp

theorem om_datum_inv_conj (μ : kˣ →* ℂˣ) (hμ : ∀ d, ‖(μ d : ℂ)‖ = 1) (y : GL (A ⊕ D') k)
    (z : Matrix (A ⊕ D) (A ⊕ D') k) :
    GlobalTheory.SplitWeil.om μ⁻¹ y (1 : GL (A ⊕ D) k) (datum μ⁻¹) z =
      conj (GlobalTheory.SplitWeil.om μ y (1 : GL (A ⊕ D) k) (datum μ) z) := by
  unfold GlobalTheory.SplitWeil.om
  rw [datum_inv_conj μ hμ]
  simp only [map_mul, Complex.conj_ofReal, conj_unit (hμ _), MonoidHom.inv_apply]
  simp

end Local

end GlobalTheory.TwistCoef

namespace GlobalTheory.TwistCoef

section IP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] {m n : Type} [Fintype m] [Fintype n]

theorem ip_conj (ν : Measure k) (F G : Matrix m n k → ℂ) :
    GlobalTheory.SplitWeil.ip ν (fun z => conj (F z)) (fun z => conj (G z)) = conj (GlobalTheory.SplitWeil.ip ν F G) := by
  unfold GlobalTheory.SplitWeil.ip
  rw [← integral_conj]
  congr 1
  funext z
  simp [map_mul]

end IP

theorem coef_split : ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s k φ ι → ∀ μT : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μT y = Circle.toUnits (c.chT (k + 1) x)) → ∀ [MeasurableSpace (Fv D.host.F v)] [BorelSpace (Fv D.host.F v)] (ν : Measure (Fv D.host.F v)), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ cf : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → ℂ, (∀ g, cf g = GlobalTheory.SplitWeil.ip ν (GlobalTheory.SplitWeil.om μT g (1 : GL (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fv D.host.F v)) (datum μT)) (datum μT)) → ∀ P (x : GA D s.V), gAt s.V (.inl v) x = 1 → ∀ y, coefW p.ω m X (p.pt P) (x * ι y) * conj (cf 1) = coefW p.ω m X (p.pt P) x * conj (cf y) := by
  intro D hgap c w hw k hk s s' hs hs' p hp m X hX PP hPP v φ hφ ι hι μT hμT _ _ ν hν cf hcf P x hx
  obtain ⟨-, hch'⟩ := GlobalTheory.TwistChart.charts_at_twist D c w hw (k + 1) hk s' hs' PP hPP
  obtain ⟨⟨e, he⟩, -, ⟨ι', hι'⟩, hμ⟩ := hch' v φ hφ
  obtain ⟨μS, -, hμS⟩ := hμ (c.chS (k + 1))
  obtain ⟨U, hU1, -⟩ := GlobalTheory.TwistChart.unit_section φ he
  have hunit : ∀ d, ‖(μT d : ℂ)‖ = 1 := fun d => by
    rw [hμT (U d) d ⟨e, he, (hU1 d).1, (hU1 d).2⟩]
    exact Circle.norm_coe _
  have hlift : LiftsChar φ PP μT (w.ξ PP) :=
    (GlobalTheory.T.splitPlaceChart_parahoric_level_stabiliser_height D c w hw k hk.le s hs PP hPP v φ hφ).2.2.2.1 k hk μT (Or.inr hμT)
  obtain ⟨hW, hΦ, T, hT0, -, hTω, hC⟩ :=
    GlobalTheory.T.linearModel_splitPlace_twist_schwartzBruhat D hgap c w hw k hk s s' hs hs' p hp PP hPP v φ hφ ι ι' hι hι' μS μT μT hμS hμT hlift P m X hX
  obtain ⟨C, hC⟩ := hC ν hν x hx
  have key : ∀ y, coefW p.ω m X (p.pt P) (x * ι y) = C * conj (cf y) := by
    intro y
    have h1 : p.ω (x * ι y, 1) = p.ω (x, 1) * p.ω (ι y, ι' 1) := by
      rw [map_one, ← map_mul]
      simp
    unfold coefW
    rw [h1, ← hT0]
    simp only [Module.End.mul_apply]
    rw [hTω, hC, hcf, ← ip_conj]
    congr 2
    · funext z
      simp [GlobalTheory.ParHecke.omTwo, om_datum_inv_conj _ hunit]
    · funext z
      exact datum_inv_conj _ hunit z
  intro y
  have h0 := key 1
  rw [map_one, mul_one] at h0
  rw [key y, h0]
  ring

end GlobalTheory.TwistCoef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCoefficientSplitsLocalFactorTwistPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilCoefficient_splits_localFactor_twistPlace : ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s k φ ι → ∀ μT : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μT y = Circle.toUnits (c.chT (k + 1) x)) → ∀ [MeasurableSpace (Fv D.host.F v)] [BorelSpace (Fv D.host.F v)] (ν : Measure (Fv D.host.F v)), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ cf : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → ℂ, (∀ g, cf g = GlobalTheory.SplitWeil.ip ν (GlobalTheory.SplitWeil.om μT g (1 : GL (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fv D.host.F v)) (datum μT)) (datum μT)) → ∀ P (x : GA D s.V), gAt s.V (.inl v) x = 1 → ∀ y, coefW p.ω m X (p.pt P) (x * ι y) * conj (cf 1) = coefW p.ω m X (p.pt P) x * conj (cf y) := by
  first | exact @GlobalTheory.TwistCoef.coef_split | exact GlobalTheory.TwistCoef.coef_split | (intros; apply GlobalTheory.TwistCoef.coef_split <;> assumption)
end
end
