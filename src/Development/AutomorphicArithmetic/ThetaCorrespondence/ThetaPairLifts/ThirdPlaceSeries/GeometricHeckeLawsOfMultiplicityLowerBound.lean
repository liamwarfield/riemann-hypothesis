module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.MvAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameParamRecordLe
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Imports

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricHeckeLawsOfMultiplicityLowerBound
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeGeometricOfMultiplicityLowerBound
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
namespace GlobalTheory.HeightCounting.HeckeLaw
theorem hecke_geometric_of_multiplicity_lower_bound_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (i : (Dof x).ntw.Tw) (b : Bool) (j : Fin (Dof x).R.m), GlobalTheory.GeoTie.HeckeGeo l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) b j := by
  intro hP hS hL
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  refine ((ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev)).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  intro P x l i b j
  obtain ⟨hHo, -⟩ := H.1 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := H.2 (w.st x.o.Z) hO
  have hfin : Finite (TupU w.I (usedOf w.I T P.Wt)) := by
    have hs : ({τ | τ = (Formalism.L2.DIV.mu0F (X := B.fields) (tuOf w.I (usedOf w.I T P.Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T P.Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T P.Wt)).finite_toSet
    exact hs.to_subtype
  let X := GlobalTheory.TwInputs.RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo hfin hHo hStd hSize
  have hC := X.char
  have hSb : ∀ Q ∈ x.m.z.R.Sb, Q ∈ (Dof x).ntw.S0 i := by
    intro Q hQ
    have hA : x.m.z.R.Sb = x.m.z.R.Pg := x.m.z.pins.char.allPl
    obtain ⟨k, hk⟩ := l.b.ser.ex.good.Pg i j b Q (by rw [l.b.ser.ex.pin.Pg]; exact hA ▸ hQ)
    exact (Dof x).ntw.placesOver_subset_exceptional i k hk
  exact GlobalTheory.GeoTie.CuspLev.heckeGeo_of_levels l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) b j l.b.ser.ex
    (x.m.z.geo.fw.evaluates_of_lUnif x.m.intersectionNumber_baseChange.prim.unif) hC.lev hC.models.HW x.m.intersectionNumber_baseChange.prim.unif
    (l.rat.In.ks _ (Nat.le_add_left _ _) j.2) (fun hV => GlobalTheory.HeckeSupReal.readsCusp_realSide hP.decay hS.hkRead (Dof x) X j hV)
    (fun Q hQs hQ => GlobalTheory.SplitOffS0.main l.b.ser.ex.good i _ hSb Q hQs hQ) hS.hkTr
    (fun Q hQ => delAt_mem w x.o.Z x.m.z i Q hQ)
end GlobalTheory.HeightCounting.HeckeLaw
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeGeo_at_levelB1_states : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (i : (Dof x).ntw.Tw) (b : Bool) (j : Fin (Dof x).R.m), GlobalTheory.GeoTie.HeckeGeo l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) b j := by
  first | exact @_root_.GlobalTheory.HeightCounting.HeckeLaw.hecke_geometric_of_multiplicity_lower_bound_alt | exact _root_.GlobalTheory.HeightCounting.HeckeLaw.hecke_geometric_of_multiplicity_lower_bound_alt | (intros; apply _root_.GlobalTheory.HeightCounting.HeckeLaw.hecke_geometric_of_multiplicity_lower_bound_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
theorem GlobalTheory.HeightCounting.Up.geoLaws_at_levelB1_states : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (i : (Dof x).ntw.Tw), GlobalTheory.GeoTie.GeoLaws l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) := by
  intro hP hS hL
  have hH := _root_.GlobalTheory.T.heckeGeo_at_levelB1_states hP hS hL
  refine hH.trans (StepW.of_all fun K B f T w _ _ hw P x l i => ?_)
  have hint := (Dof x).nth.iC_int i
  refine ⟨?_, ?_, ?_, hw P x l i, ?_, ?_, ?_⟩
  · intro b j
    exact GlobalTheory.PointsDetectAlg.detects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hint b j
  · intro b j
    exact GlobalTheory.GeoTie.supDescent_side _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hint b j
  · intro b j f
    exact l.b.ser.sup i _ b _ _ f
  · intro b j
    exact GlobalTheory.T.heckeQuotient_integral_framed_point_complete_field hS.hkInt _ _ _ _ _ _ _ _ _ _ _ x.m.z.geo.κ x.m.z.geo.v₀ x.m.z.geo.fw _ _ hint b j
  · intro j k Pl hk
    obtain ⟨hHP, -⟩ := GlobalTheory.T.isSplitHeckePrimeOffLevel_of_heckeIndexPlace _ _ x.m.z.geo.fw.laws i k Pl hk
    obtain ⟨n, hn⟩ := GlobalTheory.HeckeCount.card_hkKer_const _ _ _ _ (x.m.z.core.Q.Xo ((j : ℕ) + 1)) x.m.z.core.Q.c Pl.asIdeal
      (GlobalTheory.GeoTie.charAt Pl) k (GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 hHP)
    exact ⟨n, fun b z => hn _ z.1⟩
  · intro j hj b
    exact l.b.ser.off i j b (fun h => hj (Finset.mem_Icc.2 h))
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geoLaws_iC_at_levelB1_of_serN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (i : (Dof x).ntw.Tw), GlobalTheory.GeoTie.GeoLaws l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.geoLaws_at_levelB1_states | exact _root_.GlobalTheory.HeightCounting.Up.geoLaws_at_levelB1_states | (intros; apply _root_.GlobalTheory.HeightCounting.Up.geoLaws_at_levelB1_states <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SphericalLocalComponentAtSmallPlaces
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SphericalLocalComponentAwayFromLevel
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000
section SphOffSec
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult
namespace GlobalTheory.RowSphOff
end GlobalTheory.RowSphOff
end SphOffSec
namespace GlobalTheory.RowSphOff
theorem spherical_localComponent_away_from_level_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (σ : (w.st Z).toD7.what₂.FT) (s : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E), (∀ k : Fin 2, s.w ∉ placesOver (w.st Z).toD7.host.E ((w.st Z).toD7.host.g k)) → ∃ τ, IsLocS (repOf Y σ).S s τ ∧ GlobalTheory.SmGL.IsSpherical τ.ρ := by
  intro hPr
  refine evG_all fun K => lg_all K fun B f T _ => ?_
  intro hKP w hpin Z Wt hX z p0 Y hH hEx hGeo hGrp hGA σ s hoff
  obtain ⟨h, hh⟩ := levS_of_kO_conj _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins s hoff
  obtain ⟨φ, hφS, hφ0, hφfix⟩ := exists_fixed_of_level _ _ _ _ _ _ _ z.R z.F p0 Y σ
    {κ | ReciprocityTheory.Aut.TrivOutside {s.v} κ ∧ h⁻¹ * s.loc _ κ * h ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalRealSubfield (w.st Z).toD7.host.E)) (Fin (w.st Z).toD7.R.r)}
    (fun b κ hκ => hh b κ hκ.1 hκ.2)
  obtain ⟨τ, hτ⟩ := exists_isLocS_rows hPr.hc hPr.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ s
  refine ⟨τ, hτ, ?_⟩
  obtain ⟨x, hx, e⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq _ s h
  have hmul : ∀ (a b : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r) (g : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r → ℂ),
      NG.rt _ _ (a * b) g = NG.rt _ _ a (NG.rt _ _ b g) := by
    intro a b g
    funext c
    simp [NG.rt, mul_assoc]
  have hone : ∀ g : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r → ℂ, NG.rt _ _ 1 g = g := by
    intro g
    funext c
    simp [NG.rt]
  have hT : ∀ a b : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r, ReciprocityTheory.Aut.TrivOutside {s.v} a →
      ReciprocityTheory.Aut.TrivOutside {s.v} b → ReciprocityTheory.Aut.TrivOutside {s.v} (a * b) :=
    fun a b ha hb v hv => by
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, ha v hv, hb v hv, mul_one]
  refine fixed_kO_ne_bot _ _ (repOf Y σ) s τ hτ (NG.rt _ _ x⁻¹ φ) ((repOf Y σ).stable _ φ hφS) ?_ ?_
  · intro h0
    apply hφ0
    rw [← hone φ, ← mul_inv_cancel x, hmul, h0, map_zero]
  · intro κ hκ hk
    have h1 := hφfix (x * κ * x⁻¹) ⟨hT _ _ (hT _ _ hx hκ) (GlobalTheory.RowLevelSplit.trivOutside_inv hx), by
      rw [map_mul, map_mul, map_inv, e, show h⁻¹ * (h * s.loc _ κ * h⁻¹) * h = s.loc _ κ by group]
      exact hk⟩
    rw [← hmul, show κ * x⁻¹ = x⁻¹ * (x * κ * x⁻¹) by group, hmul, h1]
end GlobalTheory.RowSphOff
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spherical_loc_comp_at_split_place_off_g : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (σ : (w.st Z).toD7.what₂.FT) (s : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E), (∀ k : Fin 2, s.w ∉ placesOver (w.st Z).toD7.host.E ((w.st Z).toD7.host.g k)) → ∃ τ, IsLocS (repOf Y σ).S s τ ∧ GlobalTheory.SmGL.IsSpherical τ.ρ := by
  first | exact @_root_.GlobalTheory.RowSphOff.spherical_localComponent_away_from_level_alt | exact _root_.GlobalTheory.RowSphOff.spherical_localComponent_away_from_level_alt | (intros; apply _root_.GlobalTheory.RowSphOff.spherical_localComponent_away_from_level_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocRecUnrFrobEigLe
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowSphSmall
open GlobalTheory.CuspRep.ParLaws GlobalTheory.LocLanglands
theorem reciprocity_unramified_and_norm_frobenius_eigenvalue_le (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {E Ω : Type} [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : Formalism.ConjugateSelfDual.IsPlaceOver A w)
    {n : ℕ} (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E))) (hs : GlobalTheory.SmGL.IsSpherical σ.ρ)
    (hu : GlobalTheory.SmGL.IsUnitarisable σ.ρ) :
    (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls σ)).unr ∧
      ∀ α ∈ (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls σ)).frobEig, ‖α‖ ≤ ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  have H := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  have hunr : (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls σ)).unr := (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical H σ).2 hs
  refine ⟨hunr, ?_⟩
  obtain ⟨α, hα⟩ := _root_.UpperTheory.One.M.exists_hasSatake_of_unr_alt H hunr
  rw [_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake H hα, GlobalTheory.WeilDeligne.WD.frobEig_diag]
  have h1 := GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake E w n (GlobalTheory.SplitRead.Irr.ofIrrRep σ) α hα hu
  have h2 : GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w n
      ((Finset.univ.val.map fun i => (α i : ℂ)).map (·⁻¹)) := by
    have := GlobalTheory.RowSatakeBound.finite_residue w
    exact GlobalTheory.SatakeInv.isUnitarySatake_map_inv _ _ _ _ h1
  intro b hb
  apply h2.norm_le
  simpa [Multiset.map_map, Function.comp_def] using hb
end GlobalTheory.RowSphSmall
section FormSec
namespace GlobalTheory.RowSphSmall
end GlobalTheory.RowSphSmall
end FormSec
namespace GlobalTheory.RowSphSmall
end GlobalTheory.RowSphSmall
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowSphSmall
theorem spherical_localComponent_of_small_prime_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, OverRows fun _ _ _ _ w Z _ _ z _ Y =>
    ∀ Rw, _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw → ∀ σ, RowLoc (w.st Z).toD7 Rw σ := by
  intro hP hL
  refine EvG.imp (_root_.GlobalTheory.T.exists_spherical_loc_comp_at_split_place_off_g hP) fun K _ _ _ _ hK => large₂.imp hK fun B f T _ H => ?_
  intro hKP w hpin Z Wt hX z p0 Y hH hEx hGeo hGrp hGA Rw hPar σ w' hsplit hoff
  have H' := H hKP w hpin Z Wt hX z p0 Y hH hEx hGeo hGrp hGA σ
  obtain ⟨s, rfl⟩ := GlobalTheory.OffBad.splitPlace_of_isSplitPl _ w' hsplit
  obtain ⟨τ, hloc, hsph⟩ := H' s hoff
  obtain ⟨Bf, k1, k2, k3, k4⟩ := exists_form_rowRepR hP.hc hP.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ
  have hunit := isUnitarisable_of_isLocS (repOf Y σ) Bf k1 k2 k3 k4 s τ hloc
  have he := hPar.row.1 σ s τ hloc
  obtain ⟨hu, hb⟩ := _root_.GlobalTheory.RowSphSmall.reciprocity_unramified_and_norm_frobenius_eigenvalue_le hL ((w.st Z).toD7.nd.plOm.2 s.w) τ hsph hunit
  rw [← he] at hu hb
  have hu' := (hPar.T.unr _ _).2 hu
  refine ⟨hu', fun α hα => ?_⟩
  rw [hPar.T.frobEig _ _ hu'] at hα
  have h1 := hb α hα
  have hq : (1 : ℝ) < ((Formalism.ConjugateSelfDual.normV s.w : ℕ) : ℝ) := by exact_mod_cast GlobalTheory.WeilDeligne.one_lt_normV s.w
  have hrt : (((w.st Z).toD7.R.r : ℝ) - 1) / 2 < (((w.st Z).toD7.R.t : ℝ) - 1) / 2 := by
    have := (w.st Z).toD7.R.rank_add_five_le
    have h2 : (w.st Z).toD7.R.r < (w.st Z).toD7.R.t := by unfold Ranks.r; omega
    have h3 : ((w.st Z).toD7.R.r : ℝ) < ((w.st Z).toD7.R.t : ℝ) := by exact_mod_cast h2
    linarith
  calc ‖α‖ ≤ ((Formalism.ConjugateSelfDual.normV s.w : ℕ) : ℝ) ^ ((((w.st Z).toD7.R.r : ℝ) - 1) / 2) := h1
    _ < ((Formalism.ConjugateSelfDual.normV s.w : ℕ) : ℝ) ^ ((((w.st Z).toD7.R.t : ℝ) - 1) / 2) := Real.rpow_lt_rpow_of_exponent_lt hq hrt
    _ = ((Ideal.absNorm s.w.asIdeal : ℕ) : ℝ) ^ ((((w.st Z).toD7.R.t : ℝ) - 1) / 2) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rfl
end GlobalTheory.RowSphSmall
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_of_par_in_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ Rw, _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw → ∀ σ, RowLoc (w.st Z).toD7 Rw σ := by
  first | exact @_root_.GlobalTheory.RowSphSmall.spherical_localComponent_of_small_prime_alt | exact _root_.GlobalTheory.RowSphSmall.spherical_localComponent_of_small_prime_alt | (intros; apply _root_.GlobalTheory.RowSphSmall.spherical_localComponent_of_small_prime_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MClassMapD
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MDzLabLP
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
open GlobalTheory.WeilDeligne GlobalTheory.SerSys.LabDepth in
theorem labLP_isLabel_and_actK_fix : Green → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D) (L : ∀ k, LabelDatum (D.host.g k)), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → GlobalTheory.HeightCounting.LabTrue D T → GlobalTheory.SerSys.LabTie D L → DiscreteGroups.sglob.DzType.Rt.LabParamLe D.R.nV D L rc → ∀ k v (π : QRep (D.host.g k) D.R.r), IrrSm π → fixK1 π.ρ ≠ ⊥ → IsLabel D k (D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π)) ∧ ∀ y ∈ fixK1 π.ρ, actK π.ρ (D.ntypes.eSer k (D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π))) y = y := by
  intro hG hL D T I rc L hRc hLT hLab hP k v π hπ hfix
  let S : Sys (D.host.g k) := OfLabel.ofLabel (L k) (Bridge.five_le D k) hG
  have hSe : ∀ n f, S.e n f = eSerC (L k) n f := fun _ _ => rfl
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hfix
  obtain ⟨f, hf⟩ : ∃ f, actK π.ρ (S.e D.R.r f) y ≠ 0 := by
    obtain ⟨T', hT'⟩ := S.sum D.R.r
    by_contra hcon
    push Not at hcon
    apply hy0
    rw [← LabLoc.actK_one_of_mem π.ρ hy, ← hT', LabLoc.actK_finset_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun f _ => hcon f
  have hne : S.e D.R.r f ≠ 0 := fun e => hf (by rw [e]; simp [actK])
  obtain ⟨hm, hd, h0⟩ := S.label _ f hne
  have hine : D.naut.inePol (rc k v D.R.r π) (D.ntypes.tg k v) =
      ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (D.ntypes.teichC k x)).prod := by
    rw [← (hLab k).1]
    exact hP k v D.R.r (DiscreteGroups.sglob.DzType.Rt.r_le_nV D) π hπ f ⟨y, hy, hf⟩
  have hSet : TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) :=
    .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
      (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
  have htame : (T.e _ (rc k v D.R.r π)).tame := by
    obtain ⟨σ, hiso, hσ⟩ := exists_pull D I k v π hπ hfix
    rw [hRc k v D.R.r σ π hiso]
    first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, hl⟩ := hOpn) | obtain ⟨a, ha, ε, -, hl⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
    refine tame_of_isTameWD ((fun hx => haveI := UpperTheory.One.M.charZero_compl (D.naut.plGw k v); _root_.UpperTheory.One.M.LawsM.depth hl _ (UpperTheory.One.M.good_of_fixed ⟨_, ⟨D.host.g_prime k⟩, I.i k v, I.cont k v⟩ _ hx) hx : _ → _) ?_)
    exact GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep σ).some.symm hσ
  have hlab : D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π) = f := by
    have e1 : (Formalism.CyclotomicNorms.rootsBar f).map (fun x => X - C (D.ntypes.teichC k x)) =
        ((Formalism.CyclotomicNorms.rootsBar f).map (D.ntypes.teichC k)).map (fun a => X - C a) := by
      rw [Multiset.map_map]; rfl
    rw [hLT k v, WD.lab_eq_iff_of_tame hSet htame, ← T.inePol _ _ _ (D.ntypes.tg_gen k v).1, hine, e1,
      roots_multiset_prod_X_sub_C]
    exact ⟨hm, rfl⟩
  refine ⟨hlab ▸ ⟨hm, hd, h0⟩, fun z hz => ?_⟩
  rw [hlab, (hLab k).2 f, ← hSe]
  refine DiscreteGroups.sglob.DzType.Rt.actK_e_eq_self_le _ S (L k).teich (fun n π => D.naut.inePol (rc k v n π) (D.ntypes.tg k v)) D.R.nV ?_
    (hP k v) D.R.r (DiscreteGroups.sglob.DzType.Rt.r_le_nV D) π hπ f hm h0 ?_ z hz
  · rw [(hLab k).1]
    exact fun x hx y hy e => D.ntypes.teichC_inj k x y hx hy e
  · rw [(hLab k).1]; exact hine
end DiscreteGroups.sglob.DzType.Rt
end
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.SerSys
open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical
variable {g : ℕ} [Fact g.Prime]
end GlobalTheory.SerSys
end
end
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
theorem exists_isRc_isClassMapD_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (I : Ident D), ∃ rc : GlobalTheory.SerSys.Corr D, _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc ∧ ∀ k v, GlobalTheory.SerSys.IsClassMapD D.naut.lpDim (rc k v) := by
  intro hL D T I
  obtain ⟨rc, hrc⟩ := _root_.GlobalTheory.TypeRec.Model.exists_isRc_alt hL T I
  refine ⟨rc, hrc, fun k v n π hπ => ?_⟩
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  obtain ⟨σ, e⟩ := GlobalTheory.TypeRec.Model.exists_pull I k v π hπ
  refine ⟨?_, fun π' hπ' hg => ?_⟩
  · rw [← T.dim, hrc k v n σ π e]
    exact H.dim _
  · obtain ⟨σ', e', hσ'⟩ := GlobalTheory.SerSys.LabDepth.exists_pull D I k v π' hπ' hg
    have hg' : UpperTheory.Zero.LLC.Good (GlobalTheory.LocLanglands.cls σ') :=
      haveI := charZero_compl (D.naut.plGw k v)
      good_cls_of_fixed ⟨_, ⟨D.host.g_prime k⟩, I.i k v, I.cont k v⟩ σ' hσ'
    constructor
    · intro hr
      have h2 := congrArg (T.e _) hr
      rw [hrc k v n σ π e, hrc k v n σ' π' e'] at h2
      obtain ⟨f⟩ := pull_iso_of_cls_eq I k v σ σ' (_root_.UpperTheory.One.M.LawsM.inj H _ _ hg' h2)
      exact ⟨e.some ≪≫ f ≪≫ e'.some.symm⟩
    · rintro ⟨f⟩
      apply (T.e _).injective
      rw [hrc k v n σ π e, hrc k v n σ π' ⟨f.symm ≪≫ e.some⟩]
end UpperTheory.One.M
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
namespace DiscreteGroups.sglob.DzType.Rt
open GlobalTheory.TypeRec GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem typeLab_of_local_m_alt : Green → GlobalTheory.Published.ZelevinskyPolynomialRing → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), GlobalTheory.HeightCounting.LabTrue D T → _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → GlobalTheory.SerSys.LabTie D L → (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) → GlobalTheory.LabPin.TypeLab D rep := by
  intro hG hZ hDZ hL D T Rw rep L hLab hRow hDep hLT hTame
  obtain ⟨I⟩ := GlobalTheory.T.nonempty_typePlaceCompletionIdent D
  obtain ⟨rc, hrc, hcls⟩ := _root_.UpperTheory.One.M.exists_isRc_isClassMapD_alt hL D T I
  obtain ⟨cp, hcomp, hcp⟩ := _root_.GlobalTheory.T.exists_comp_irrSm_locR_eq_rc hL D T I rc hrc Rw rep hRow hDep
  have hP : DiscreteGroups.sglob.DzType.Rt.LabParamLe D.R.nV D L rc := DiscreteGroups.sglob.DzType.Rt.labParamLe_of D L rc hG (_root_.GlobalTheory.T.tame_gen_support_compat_of_is_rc hZ hL D T I rc hrc)
    (fun k => GlobalTheory.T.depthZeroSupercuspidal_cuspidalModule (D.host.g k))
    (fun k v => by
      obtain ⟨κ, hκ⟩ := hTame k v
      exact _root_.DiscreteGroups.sglob.DzType.Rt.tame_param_le_of_tame_coupled hDZ hL D T I rc hrc L k v κ hκ)
  have hfix : ∀ σ k v, fixK1 (cp σ k v).ρ ≠ ⊥ := by
    intro σ k v
    obtain ⟨s, τ, hsw, hloc, hfx⟩ := hDep σ k v
    have hT := hRow.1 σ s τ hloc
    have key : ∀ (w : PlE D.host) (hw : w = D.naut.plGw k v)
        (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (w.adicCompletion D.host.E))),
        T.e w (Rw.locR σ w) = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls τ) →
        GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (w.adicCompletion D.host.E) (Fin D.R.r)) ≠ ⊥ →
        fixK1 (cp σ k v).ρ ≠ ⊥ := by
      intro w hw τ hT hfx
      subst hw
      have h1 := hrc k v D.R.r τ (pull I k v τ) ⟨CategoryTheory.Iso.refl _⟩
      have h2 : rc k v D.R.r (pull I k v τ) = rc k v D.R.r (cp σ k v) := by
        rw [← (hcp σ k v).2]
        exact (T.e _).injective (h1.trans hT.symm)
      obtain ⟨e⟩ := (((hcls k v) D.R.r (cp σ k v) (hcp σ k v).1).2 (pull I k v τ) (GlobalTheory.TypeRec.Model.irrSm_pull I k v τ)
        (GlobalTheory.LabPin.principalCongruence_fixed_vector_rational_local_field I k v τ hfx)).1 h2.symm
      exact GlobalTheory.LabPin.principalCongruenceFixedVectors_ne_bot_of_iso e (GlobalTheory.LabPin.principalCongruence_fixed_vector_rational_local_field I k v τ hfx)
    exact key s.w hsw τ hT hfx
  intro σ k v
  have hlab : D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r (cp σ k v)) := by
    rw [Rw.lab_eq, (hcp σ k v).2]
  obtain ⟨h1, h2⟩ := _root_.DiscreteGroups.sglob.DzType.Rt.labLP_isLabel_and_actK_fix hG hL D T I rc L hrc hLab hLT hP k v (cp σ k v) (hcp σ k v).1 (hfix σ k v)
  show IsLabel D k (D.nd.lab k σ v) ∧ ∀ s : SplitPlace D.host.E, s.w = D.naut.plGw k v → SerFix (rep σ) s (D.ntypes.eSer k (D.nd.lab k σ v))
  rw [hlab]
  exact ⟨h1, fun s hs => GlobalTheory.T.depthZeroIdentity_finiteType_of_typePrimeComponent D I rep cp hcomp σ k v _ h2 s hs⟩
end DiscreteGroups.sglob.DzType.Rt
end
section
namespace GlobalTheory.LabPin
end GlobalTheory.LabPin
namespace GlobalTheory.LabPin
end GlobalTheory.LabPin
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisConjPlaceDual
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DepthZeroTameAlt
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf GlobalTheory.PRep GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end
theorem conjDualParamF_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (w w' : PlE D.host) (c : D.nd.Om ≃+* D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) →
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') →
    ∀ (κ : w.adicCompletion D.host.E ≃+* w'.adicCompletion D.host.E), Continuous κ →
    (∀ x : D.host.E, κ (algebraMap D.host.E _ x) = algebraMap D.host.E _ (D.host.conj x)) →
    ∀ (n : ℕ) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E)))
      (σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w'.adicCompletion D.host.E))) (e : σ.V ≃ₗ[ℂ] σ'.V),
    (∀ g a, e (σ.ρ (GlobalTheory.TypeTame.invTranspose n g) a) = σ'.ρ (Matrix.GeneralLinearGroup.map κ.toRingHom g) (e a)) →
    Good (GlobalTheory.LocLanglands.cls σ) →
    ∃ (b : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w) (Fin n → ℂ)) (b' : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w') (Fin n → ℂ)),
      GlobalTheory.WeilDeligne.WD.mk b = (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls σ)).lpDual ∧
      GlobalTheory.WeilDeligne.WD.mk b' = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w') (GlobalTheory.LocLanglands.cls σ') ∧
      b.N = b'.N ∧ ∀ (τ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w)) (τ' : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w')),
        (∀ z, c ((τ : GE D.nd) z) = (τ' : GE D.nd) (c z)) → b.ρ τ = b'.ρ τ' := by
  intro hL D w w' c hc hA κ hκ hκE n σ σ' e he hg
  let π₁ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E)) :=
    ⟨σ.V, σ.ρ.comp (GlobalTheory.TypeTame.invTranspose n),
      fun v => (σ.smooth v).preimage (GlobalTheory.TypeTame.continuous_invTranspose n),
      GlobalTheory.GelfandKazhdan.isIrreducible_comp _ (fun g => ⟨_, GlobalTheory.TypeTame.invTranspose_invTranspose n g⟩) σ.irr⟩
  have ha : GlobalTheory.PRep.IsAdmissible σ.ρ := (UpperTheory.Zero.LLC.Pr.bz _).1 (Fin n) σ.V σ.ρ σ.smooth σ.irr
  have hE := GlobalTheory.GelfandKazhdan.equiv_contra _ n σ.V σ.ρ ha σ.irr
  have hr := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)
  obtain ⟨b, b', h1, h2, h3, h4⟩ := _root_.UpperTheory.One.M.New.field hL hr
    (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w')) c (D.host.conj : D.host.E →+* D.host.E) κ
    (fun z => (hA z).symm) hc hκ hκE n π₁ σ' e he (good_contra σ π₁ hE hg)
  first | (have hOpn := UpperTheory.One.M.opn _ (hr); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := hr
  exact ⟨b, b', h1.trans (_root_.UpperTheory.One.M.LawsM.dual H n σ π₁ hg hE), h2, h3, h4⟩
end UpperTheory.One.M
end
end
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ConjPlaceDual
theorem depthZero_tame_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), LabAll D P.T → ConjDual D := by
  intro hPr hL D P hLab i PI k v w' hc
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := hLab
  obtain ⟨c, hc1, hc2, hc3⟩ := hγ2 k v w' hc
  have hw'g : w' ∈ placesOver D.host.E (D.host.g k) := by
    have h0 := D.naut.plGw_over k v
    simp only [placesOver, Set.mem_setOf_eq] at h0 ⊢
    exact (hc _ _ (by simp)).1 h0
  rw [hγ3 k w' hw'g, hγ3 k _ (D.naut.plGw_over k v), hγ1 k v]
  obtain ⟨s, hs⟩ := GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, v⟩
  have hc3' : ∀ y, γ k w' (c y) = c (D.ntypes.tg k v y) := hc3
  clear hγ1 hγ2 hγ3
  generalize D.naut.plGw k v = w at hs hc hc2 ⊢
  subst hs
  obtain ⟨hsw', -⟩ := GlobalTheory.TypeTame.conjSP_w_of_isConjPl D s w' (conjPl_symm D hc)
  subst hsw'
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV (P.H.av.rep i PI) s
  obtain ⟨κ, σ', e, hκ, hκc, hσ', he⟩ := GlobalTheory.T.splitPlaceLocalComponent_conj_eq_inverseTranspose D D.R.nV (P.H.av.rep i PI) s σ hσ
  have hloc : ∀ w, D.naut.locV i PI w = D.nbc.locAU (D.nd.j i)
      (P.H.au.cls (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i PI)) w := fun w =>
    by rw [D.nbc.embAV_loc, P.H.emb]
  have hA := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i PI) s σ hσ
  have hA' := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i PI) _ σ' hσ'
  rw [← hloc] at hA hA'
  obtain ⟨b, b', hb, hb', hN, hρ⟩ := _root_.UpperTheory.One.M.conjDualParamF_alt hL D s.w (GlobalTheory.TypeTame.conjSP s).w c hc1 hc2 κ hκ hκc D.R.nV σ σ' e he
    (_root_.UpperTheory.One.M.good_cls_of_isLocS_av P i PI s σ hσ)
  rw [← hA] at hb
  rw [← hA'] at hb'
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.weilDeligneDualTransport_monodromy_dim_wild D _ _ c hc1 hc2 _ _ D.R.nV b b' hb hb' hN hρ
  have h4 := GlobalTheory.T.weilDeligneLabel_transportDual_inverseRoots D k _ _ c hc1 hc2 _ _ D.R.nV b b' hb hb' hN hρ _ _ hc3'
  refine ⟨fun hm => (P.T.mono0 _ _).2 (h1 ((P.T.mono0 _ _).1 hm)), fun ht σ₁ hσ₁ hw₁ => ?_, h4⟩
  rw [P.T.inePol _ _ σ₁ hσ₁, ← P.T.dim]
  refine h3 (fun σ₂ hσ₂ hw₂ => ?_) σ₁ hσ₁ hw₁
  rw [← P.T.inePol _ _ σ₂ hσ₂, P.T.dim]
  exact ht σ₂ hσ₂ hw₂
end GlobalTheory.ConjPlaceDual
end
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ConjPlaceDual
end GlobalTheory.ConjPlaceDual
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjDual_of_labAll : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), LabAll D P.T → ConjDual D := by
  first | exact @_root_.GlobalTheory.ConjPlaceDual.depthZero_tame_alt | exact _root_.GlobalTheory.ConjPlaceDual.depthZero_tame_alt | (intros; apply _root_.GlobalTheory.ConjPlaceDual.depthZero_tame_alt <;> assumption)
end
end
end
