module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfAtSmallPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameLiftsBasisDeRhamHomologyModHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormClearDenominatorsAwayFromPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormClearDenominatorsAwayFromPlace
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.Clear


set_option maxHeartbeats 800000 in
theorem clear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (G : WTZ E) (f : cuspW Xo c U G) (m : HeightOneSpectrum (𝓞 c.F) → ℝ), (Function.support m).Finite → (∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, ((m w : ℝ) : EReal) ≤ v f) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (k : ℤ), (∀ v ∈ valSet Xo c (algCls Xo c) la, ((k : ℝ) : EReal) ≤ v f) → ∃ s : c.F, s ≠ 0 ∧ vLa la s = -k ∧ ∃ g ∈ latW U G, (g : Rul Xo c) = s • (f : Rul Xo c) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro r U G f m hm hmv la k hk
  classical
  set ρ : HeightOneSpectrum (𝓞 c.F) → ℝ := Function.update m la (k : ℝ) with hρ
  have hsupp : (Function.support ρ).Finite := by
    refine (hm.insert la).subset ?_
    intro w hw
    by_cases h : w = la
    · exact Or.inl h
    · right
      simpa [hρ, Function.mem_support, Function.update_of_ne h] using hw
  obtain ⟨a, ha0, hala, hapos⟩ := GlobalTheory.RefSum.ScalApprox.exists_scal c.F ρ hsupp la
  have hρla : ρ la = (k : ℝ) := by simp [hρ]
  have hvla : vAdd la a = -k := by
    rw [hρla, Int.floor_intCast] at hala
    exact_mod_cast hala
  have hle : ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, ((ρ w : ℝ) : EReal) ≤ v (f : Rul Xo c) := by
    intro w v hv
    by_cases h : w = la
    · subst h; rw [hρla]; exact hk v hv
    · rw [show ρ w = m w by simp [hρ, Function.update_of_ne h]]; exact hmv w v hv
  refine ⟨a, ha0, hvla, ⟨a • f, (cuspW Xo c U G).smul_mem a f.2⟩, ?_, rfl⟩
  show _ ∈ GlobalTheory.AllWt.supLat _
  rw [GlobalTheory.AllWt.mem_supLat]
  intro w v hv
  show 0 ≤ v (a • (f : Rul Xo c))
  rw [(isVal_valSet w v hv).smul a _ ha0]
  have h1 : (0 : EReal) ≤ (((vAdd w a : ℤ) : ℝ) : EReal) + ((ρ w : ℝ) : EReal) := by
    rw [← EReal.coe_add]; exact_mod_cast hapos w
  exact h1.trans (add_le_add le_rfl (hle w v hv))

end GlobalTheory.RefSum.Clear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormClearDenominatorsAwayFromPlaceStatement
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_clear_denominators_away_from_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (G : WTZ E) (f : cuspW Xo c U G) (m : HeightOneSpectrum (𝓞 c.F) → ℝ), (Function.support m).Finite → (∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, ((m w : ℝ) : EReal) ≤ v f) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (k : ℤ), (∀ v ∈ valSet Xo c (algCls Xo c) la, ((k : ℝ) : EReal) ≤ v f) → ∃ s : c.F, s ≠ 0 ∧ vLa la s = -k ∧ ∃ g ∈ latW U G, (g : Rul Xo c) = s • (f : Rul Xo c) := by
  first | exact @GlobalTheory.RefSum.Clear.clear | exact GlobalTheory.RefSum.Clear.clear | (intros; apply GlobalTheory.RefSum.Clear.clear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmoothProjectiveModificationOfNonempty
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmoothProjectiveModificationOfNonempty
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory

theorem isIntegral_of_nonempty_modif : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (U : Y.Opens) (d : ℕ)
    (M : Modif p U d), (U : Set Y).Nonempty → IsIntegral M.X := by
  intro F _ Y _ p U d M hU
  have hUi : IsIrreducible (U : Set Y) :=
    ⟨hU, (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible.open_subset U.isOpen (Set.subset_univ _)⟩
  have := M.iso
  let g : (U : Scheme) ⟶ M.X := inv (M.σ ∣_ U) ≫ (M.σ ⁻¹ᵁ U).ι
  have hrange : Set.range g.base = ((M.σ ⁻¹ᵁ U : M.X.Opens) : Set M.X) := by
    have hs : Function.Surjective (inv (M.σ ∣_ U)).base := (inv (M.σ ∣_ U)).surjective
    simp only [g, Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp, hs.range_eq,
      Set.image_univ]
    exact Scheme.Opens.range_ι _
  have hopn : IsIrreducible ((M.σ ⁻¹ᵁ U : M.X.Opens) : Set M.X) := by
    rw [← hrange, ← Set.image_univ]
    have : IrreducibleSpace (U : Scheme) := Subtype.irreducibleSpace hUi
    exact (IrreducibleSpace.isIrreducible_univ (U : Scheme)).image _ g.base.hom.continuous.continuousOn
  have hcl : IsIrreducible (Set.univ : Set M.X) := by
    rw [← M.dense.closure_eq]; exact hopn.closure
  have : IrreducibleSpace M.X := irreducibleSpace_def _ |>.mpr hcl
  have : Smooth M.str := SmoothOfRelativeDimension.smooth d _
  exact isIntegral_of_smooth_field M.str

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmoothProjectiveModificationOfNonemptyStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_smoothProjectiveModification_of_nonempty : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (U : Y.Opens) (d : ℕ)
    (M : Modif p U d), (U : Set Y).Nonempty → IsIntegral M.X := by
  first | exact @GlobalTheory.isIntegral_of_nonempty_modif | exact GlobalTheory.isIntegral_of_nonempty_modif | (intros; apply GlobalTheory.isIntegral_of_nonempty_modif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleValueAtPointNeZeroIffMemNonzeroLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleValueAtPointNeZeroIffMemNonzeroLocus
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

noncomputable section

namespace GlobalTheory.ValNe

theorem evalPt_eq_stalkClosedPointTo {Y : Scheme.{0}} {V : Type} [CommRing V] [IsLocalRing V] (x : Sp V ⟶ Y) (W : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (g : Γ(Y, W)) (hy : x (IsLocalRing.closedPoint V) ∈ W) :
    (Scheme.stalkClosedPointTo (R := CommRingCat.of V) x).hom (GlobalTheory.Vanishing.ger _ hy g) = TangentOrigin.evalPt x W h g := by
  have key := Scheme.germ_stalkClosedPointTo (R := CommRingCat.of V) x W hy
  have := congrArg (fun φ => φ.hom g) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  refine this.trans ?_
  simp only [TangentOrigin.evalPt, Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, CommRingCat.hom_comp, RingHom.comp_apply, Category.assoc]
  congr!

theorem val_ofSec_ne_zero_iff : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (q : Y ⟶ Sp K) (L : LB Y) (σ : L.Sec) (z : Sp K ⟶ Y) (i : L.ι) (hi : ⊤ ≤ z ⁻¹ᵁ L.U i), (H0.val (p := q) z i le_top hi (H0.ofSec q ⊤ σ) ≠ 0 ↔ z (IsLocalRing.closedPoint K) ∈ nonzeroLocus σ) := by
  intro K _ Y q L σ z i hi
  have hy : z (IsLocalRing.closedPoint K) ∈ L.U i := hi (Set.mem_univ _)
  have e : H0.val (p := q) z i le_top hi (H0.ofSec q ⊤ σ) = TangentOrigin.evalPt z _ hi (σ.f i) :=
    H0.val_ofSec z i le_top hi σ
  rw [e, ← evalPt_eq_stalkClosedPointTo z (L.U i) hi (σ.f i) hy, ← isUnit_iff_ne_zero,
    isUnit_map_iff, GlobalTheory.Vanishing.isUnit_ger_iff σ hy]

end GlobalTheory.ValNe
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleValueAtPointNeZeroIffMemNonzeroLocusStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleValueAtPoint_ne_zero_iff_mem_nonzeroLocus : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (q : Y ⟶ Sp K) (L : LB Y) (σ : L.Sec) (z : Sp K ⟶ Y) (i : L.ι) (hi : ⊤ ≤ z ⁻¹ᵁ L.U i), (H0.val (p := q) z i le_top hi (H0.ofSec q ⊤ σ) ≠ 0 ↔ z (IsLocalRing.closedPoint K) ∈ nonzeroLocus σ) := by
  first | exact @GlobalTheory.ValNe.val_ofSec_ne_zero_iff | exact GlobalTheory.ValNe.val_ofSec_ne_zero_iff | (intros; apply GlobalTheory.ValNe.val_ofSec_ne_zero_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionOverFieldEqOfClosedPointImageEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionOverFieldEqOfClosedPointImageEq
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem section_eq_of_point_eq : ∀ (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Sp K) (z z' : Sp K ⟶ X), z ≫ q = 𝟙 _ → z' ≫ q = 𝟙 _ → z (IsLocalRing.closedPoint K) = z' (IsLocalRing.closedPoint K) → z = z' := by
  intro K _ X q z z' hz hz' hpt
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective z
  obtain ⟨⟨p', ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective z'
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hz hz' hpt ⊢
  have e : p = p' := by
    have h1 := (Scheme.Hom.comp_apply _ _ _).symm.trans (hpt.trans (Scheme.Hom.comp_apply _ _ _))
    rwa [Scheme.fromSpecResidueField_apply, Scheme.fromSpecResidueField_apply] at h1
  subst e
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (X.fromSpecResidueField p ≫ q)
  rw [Category.assoc, ← hχ, ← Spec.map_comp, ← Spec.map_id, Spec.map_inj] at hz hz'
  have hφ : ∀ c, φ.hom (χ.hom c) = c := fun c => congrArg (fun g => g.hom c) hz
  have hψ : ∀ c, ψ.hom (χ.hom c) = c := fun c => congrArg (fun g => g.hom c) hz'
  have hsurj : Function.Surjective χ.hom := by
    intro y
    refine ⟨φ.hom y, φ.hom.injective ?_⟩
    rw [hφ]
  have : φ = ψ := by
    ext y
    obtain ⟨c, rfl⟩ := hsurj y
    rw [hφ, hψ]
  rw [this]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionOverFieldEqOfClosedPointImageEqStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_over_field_eq_of_closedPoint_image_eq : ∀ (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Sp K) (z z' : Sp K ⟶ X), z ≫ q = 𝟙 _ → z' ≫ q = 𝟙 _ → z (IsLocalRing.closedPoint K) = z' (IsLocalRing.closedPoint K) → z = z' := by
  first | exact @GlobalTheory.section_eq_of_point_eq | exact GlobalTheory.section_eq_of_point_eq | (intros; apply GlobalTheory.section_eq_of_point_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityTransportsComponentToItself
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityTransportsComponentToItself
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lact_one_self {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (y : Frame Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  show ((↑(1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ) = y τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]; rfl

theorem isTransp_one : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (k : (uAt r v i).Comp), IsTransp p r i v ψ 1 k k 1 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hm r h ho i v ψ k
  have hl := h.laws v
  obtain ⟨-, hA, -, -, -, -, hj⟩ := GlobalTheory.PinNum.numerics_of_pins D (r.used v).full.Q hl.p.pins
  obtain ⟨hpq, hr, -⟩ := hj ((i : ℕ) + 1) ⟨by omega, by omega⟩
  have hL := GlobalTheory.FullLevelAction.actLev_levFull D (r.used v).full.Q ((i : ℕ) + 1) (by rw [hpq]; exact hr) hA
  refine ⟨GlobalTheory.LevelCusp.isMatch_of_isUStab _ ⟨fun x y => by simp, fun x => by simp⟩, fun x hx => ?_, fun w => ?_⟩
  · have e : castFrame (rfl : ((uAt r v i).X k).Ψ = ((uAt r v i).X k).Ψ) (lact 1 x) = x := by
      rw [lact_one_self]; rfl
    refine ⟨by rw [e]; exact hx, 1, ?_⟩
    have ey : (uAt r v i).un k ⟨castFrame (rfl : ((uAt r v i).X k).Ψ = ((uAt r v i).X k).Ψ) (lact 1 x), by rw [e]; exact hx⟩ =
        (uAt r v i).un k ⟨x, hx⟩ := congrArg _ (Subtype.ext e)
    have hf := hL.func 1 _ ((uAt r v i).un k ⟨x, hx⟩) ((uAt r v i).un k ⟨x, hx⟩)
      (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩))
      (hL.one _ _) (Formalism.L2.Pj.mvPt_spec hL.total 1 _)
    have hy : (uAt r v i).un k ⟨x, hx⟩ =
        mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩) :=
      (GlobalTheory.LevelLawsCompare.frMap_id_iff _ _).1 hf
    rw [ey]
    exact (congrArg (FrBor 1 ((uAt r v i).un k ⟨x, hx⟩)) hy).mp (GlobalTheory.ShFam.Descent.frBor_one _)
  · have hw : Matrix.mulVec ((1 : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)
        (w : Fin D.R.r → D.host.E) ∈ ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.lattice₂ D ((uAt r v i).X k).Λ := by
      rw [Units.val_one, Matrix.one_mulVec]; exact w.2
    refine ⟨hw, ?_⟩
    calc Submodule.Quotient.mk ⟨_, hw⟩ = Submodule.Quotient.mk w :=
          congrArg _ (Subtype.ext (Matrix.one_mulVec _))
      _ = ψ k ((ψ k).symm (Submodule.Quotient.mk w)) := ((ψ k).apply_symm_apply _).symm
      _ = _ := rfl
end GlobalTheory.ShareOn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityTransportsComponentToItselfStatement
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.identity_transports_component_to_itself : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (k : (uAt r v i).Comp), IsTransp p r i v ψ 1 k k 1 := by
  first | exact @GlobalTheory.ShareOn.isTransp_one | exact GlobalTheory.ShareOn.isTransp_one | (intros; apply GlobalTheory.ShareOn.isTransp_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombinationIffOfSameVecs
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem isCombination_pull_iff {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] (x : Sp R ⟶ S') (y : Sp R ⟶ S)
    (hy : y = x ≫ f) {n : ℕ} (a : Fin n → R) (V : Fin n → (Sp (DualNumber R) ⟶ G'.left))
    (hV : ∀ k, V k ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x)
    (U : Fin n → (Sp (DualNumber R) ⟶ G.left)) (hU : ∀ k, V k ≫ φ = U k)
    (w : FramedFlatCoordinates.epsAt x ⟶ G') (w' : FramedFlatCoordinates.epsAt y ⟶ G) (hw : w.left ≫ φ = w'.left) :
    FramedFlatCoordinates.IsCombination x a V w ↔ FramedFlatCoordinates.IsCombination y a U w' := by
  subst hy
  obtain rfl : U = fun k => V k ≫ φ := funext fun k => (hU k).symm
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h (FramedFlatCoordinates.epsAt x) (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  obtain rfl : w' = e w := Over.OverMorphism.ext (hw.symm.trans (he _).symm)
  have sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (k : Fin n) (u : FramedFlatCoordinates.epsAt x ⟶ G'), u.left = spMap (epsScaleR (a k)) ≫ V k ↔
      (e u).left = spMap (epsScaleR (a k)) ≫ V k ≫ φ := fun k u => by
    rw [he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _,
      fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR (a k)) ≫ ·) (hV k)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (sc (a k)))
  have pr : ∀ u : Fin n → (FramedFlatCoordinates.epsAt x ⟶ G'), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod :=
    fun u => by rw [map_list_prod, List.map_ofFn]; rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun i => e (u i), fun i => (hR _ _).1 (hu i), pr u⟩
  · rintro ⟨u, hu, hw⟩
    refine ⟨fun i => e.symm (u i), fun i => (hR _ _).2 (by rw [e.apply_symm_apply]; exact hu i), e.injective ?_⟩
    rw [pr]
    simp only [MulEquiv.apply_symm_apply]
    exact hw

theorem isCombination_iff_of_sameVecs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (x : Sp R ⟶ Xo.XF c) (x' : Sp R' ⟶ Xo.XF c) (n : ℕ) (v : Fin n → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)) (vb : Fin n → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)) (v' : Fin n → (epsAt (x' ≫ toX Xo c) ⟶ Xo.univ.t.G)) (vb' : Fin n → (epsAt ((x' ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)), x' = spMap g ≫ x → SameVecs Y x v vb → SameVecs Y x' v' vb' → ∀ (a : Fin n → R') (i : Fin n), FramedFlatCoordinates.IsCombination (x' ≫ toX Xo c) a (fun k => spMap (Chart.dualMapR g) ≫ (v k).left) (v' i) ↔ FramedFlatCoordinates.IsCombination ((x' ≫ Y.jQ) ≫ genι Y) a (fun k => spMap (Chart.dualMapR g) ≫ (vb k).left) (vb' i) := by
  intro E _ _ _ H D l Xo c O _ β Y R R' _ _ g x x' n v vb v' vb' hx h h' a i
  choose v₁ h₁ h₂ using h
  obtain ⟨w, hw₁, hw₂⟩ := h' i
  have hV : ∀ k, (spMap (Chart.dualMapR g) ≫ (v₁ k).left) ≫ Y.oF.t.G.hom =
      spMap (algebraMap R' (DualNumber R')) ≫ x' := fun k => by
    subst hx
    exact Over.w (DetExtendZero.epsMap g x ≫ v₁ k)
  refine (isCombination_pull_iff Y.m0.toSABMap.cart x' _ rfl a _ hV _ (fun k => ?_) w _ hw₁).symm.trans
    (isCombination_pull_iff Y.m.cart x' _ (Category.assoc _ _ _) a _ hV _ (fun k => ?_) w _ hw₂)
  · exact (Category.assoc _ _ _).trans (congrArg (spMap (Chart.dualMapR g) ≫ ·) (h₁ k))
  · exact (Category.assoc _ _ _).trans (congrArg (spMap (Chart.dualMapR g) ≫ ·) (h₂ k))

end GlobalTheory.DetLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrCentre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical

namespace GlobalTheory.DvrCentre

theorem exists_complete_dvr_centre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (M : RatModel o Ω) (z : M.Z), ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
    (_ : CharZero V) (ξ : Sp V ⟶ M.Z), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧
    ξ (IsLocalRing.closedPoint V) = z ∧ ∃ w, ξ w = genericPoint M.Z := by
  intro o Ω _ _ _ hA M z
  have hΩ : CharZero Ω := hA.char
  by_cases hz : z = genericPoint M.Z
  · subst hz
    have : CharZero (PowerSeries Ω) := charZero_of_injective_ringHom (PowerSeries.C_injective (R := Ω))
    have hc : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries Ω)) (PowerSeries Ω) := by
      first
      | infer_instance
      | (rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance)
    refine ⟨PowerSeries Ω, inferInstance, inferInstance, inferInstance, this,
      spMap (PowerSeries.C (R := Ω)) ≫ M.pt, hc, ?_, IsLocalRing.closedPoint _, ?_⟩
    · exact M.pt_apply _
    · exact M.pt_apply _
  · have : IsDedekindDomain o := hA.ded
    have : IsLocallyNoetherian M.Z := by
      have := M.lft
      exact LocallyOfFiniteType.isLocallyNoetherian M.s
    let S := M.Z.presheaf.stalk z
    have hS : CharZero S := (M.stalkHom z).charZero

    have hgen : M.Z.fromSpecStalk z (⊥ : PrimeSpectrum S) = genericPoint M.Z := by
      have h1 : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk z) := by
        rw [Scheme.range_fromSpecStalk]
        exact genericPoint_specializes z
      obtain ⟨q, hq⟩ := h1
      have h2 : (⊥ : PrimeSpectrum S) ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
      have h3 := h2.map (M.Z.fromSpecStalk z).continuous
      rw [hq] at h3
      exact (h3.antisymm (genericPoint_specializes _)).eq
    have hne : (⊥ : Ideal S) ≠ IsLocalRing.maximalIdeal S := by
      intro e
      apply hz
      have : (⊥ : PrimeSpectrum S) = IsLocalRing.closedPoint S := PrimeSpectrum.ext e
      rw [← hgen, this, Scheme.fromSpecStalk_closedPoint]
    obtain ⟨O, _, hO, hO', hO'', φ, h1, h2⟩ :=
      GlobalTheory.exists_complete_discreteValuationRing_ker_eq (S := S) (⊥ : Ideal S) hne
    have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h1
    have : CharZero O := charZero_of_injective_ringHom hφ
    refine ⟨O, inferInstance, hO, hO', this, spMap φ ≫ M.Z.fromSpecStalk z, hO'', ?_, (⊥ : PrimeSpectrum O), ?_⟩
    · refine (Scheme.Hom.comp_apply _ _ _).trans
        (Eq.trans (congrArg (M.Z.fromSpecStalk z) ?_) (Scheme.fromSpecStalk_closedPoint (x := z)))
      exact IsLocalRing.comap_closedPoint φ
    · refine (Scheme.Hom.comp_apply _ _ _).trans (Eq.trans (congrArg (M.Z.fromSpecStalk z) ?_) hgen)
      exact PrimeSpectrum.ext h1

end GlobalTheory.DvrCentre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NvalNonnegIff
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverInt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}

theorem nval_nonneg_iff {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] {e : ℕ} (he : 0 < e) (x : K') :
    0 ≤ nval V e x ↔ (x ≠ 0 → 0 ≤ vV V x) := by
  by_cases hx : x = 0
  · subst hx; simp [nval_zero]
  rw [nval_of_ne hx, EReal.coe_nonneg, le_div_iff₀ (by exact_mod_cast he), zero_mul]
  simp only [ne_eq, hx, not_false_eq_true, forall_const]
  norm_cast

theorem intAt_iff {Xo : Moduli Dw l} {c : Coeff l} (f : Rul Xo c) :
    IntAt Xo c f ↔ ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg →
      evI y f ≠ 0 → 0 ≤ vV T.V (evI y f) := by
  constructor
  · intro h T io y hy hne
    obtain ⟨la, e, ho⟩ := GlobalTheory.AlgLawsCompare.exists_overLa T io hy
    have := h la _ ⟨PtV.mk (PY := Unit) (lies := fun _ _ _ _ => True) la ho y hy () trivial, rfl⟩
    exact (nval_nonneg_iff ho.1 _).1 this hne
  · rintro h la _ ⟨⟨q, T, ι, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
    exact (nval_nonneg_iff ho.1 _).2 (h T ι y hy)

theorem pull_intAt_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → ((Dw.p ≠ Dw.q ∧ l.A = 1) ∨ GlobalTheory.ClsVal.Cmp.OverBase d) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d f g → (IntAt d.Xo₂ d.c₂ g ↔ IntAt Xo c f) := by
  intro E _ _ _ H Dw l Xo c d hpq hlev hO a n f hf g hg hP
  rw [intAt_iff, intAt_iff]
  constructor
  · intro hG T io y hy hne
    obtain ⟨T', iT, e, y', io₂, y₂, ⟨he, hv, φ, hφ, hm⟩, hfin, hio, hover⟩ :=
      GlobalTheory.CoverPoint.exists_ext_lift_to_cover E H Dw l Xo c 0 d hlev T io y hy
    have h1 : evI y₂ g = evI y' f := by
      letI := (iT.comp io).toAlgebra
      letI := io₂.toAlgebra
      exact GlobalTheory.CoverDown.evR_eq_of_pull hf hg hP (fun a => hio a) hover
    have h2 : evI y' f = iT (evI y f) := by
      letI := io.toAlgebra
      letI := (iT.comp io).toAlgebra
      have := GlobalTheory.SupLawProbe.evR_map (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 φ y.1
        (GlobalTheory.TransferCompare.allTest_framed Xo c T.Fr y.1) y'.1 hm
      show evR Xo c f y'.1 = iT (evR Xo c f y.1)
      rw [this]
      exact DFunLike.congr_fun hφ _
    have key := hG T' io₂ y₂ hfin (by rw [h1, h2]; exact (map_ne_zero iT).2 hne)
    rw [h1, h2, hv] at key
    exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast he)).1 key
  · intro hF T io₂ y₂ hy hne
    obtain ⟨y, hyalg, -, hval⟩ := GlobalTheory.CoverDown.exists_intFr_below E H Dw l Xo c d hpq hlev hO T io₂ y₂ hy
    rw [hval a n f hf g hg hP] at hne ⊢
    exact hF T _ y hyalg hne

end GlobalTheory.CoverInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtDualNumberTermValueSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtDualNumberTermValueSmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.JcSmul

theorem valR_const_mul {F A : Type} [Field F] [CommRing A] [Algebra F A] {Y : Scheme.{0}} (r : Sp A ⟶ Y)
    (π : Y ⟶ Sp F) (h : r ≫ π = spMap (algebraMap F A)) (U : Y.Opens) (z : F) (f : Γ(Y, U)) :
    valR r U (resTop U (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z)) * f) =
      algebraMap F A z * valR r U f := by
  unfold valR
  by_cases hU : ⊤ ≤ r ⁻¹ᵁ U
  · rw [dite_eq_left hU, dite_eq_left hU, map_mul, map_mul]
    congr 1
    have e : (r.appLE U ⊤ hU).hom (resTop U (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z))) =
        (r ≫ π).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z) := by
      simp only [resTop]
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, Scheme.Hom.comp_appTop,
        CommRingCat.hom_comp, RingHom.comp_apply]
      exact congrArg (fun g : Γ(Y, ⊤) ⟶ Γ(Sp A, ⊤) => g.hom (π.appTop.hom _)) (Scheme.Hom.appLE_eq_app r (U := ⊤))
    rw [e, h]
    have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap F A))
    have := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z)) n
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    simp
  · rw [dite_eq_right hU, dite_eq_right hU, mul_zero]

theorem jc_smul : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) {k : ℕ} (s : Fam D F k) (a : F) (gm : GtPt D (TE R F)) (α : N.X),
    jc ν (a • s) gm α = TrivSqZeroExt.inl a * jc ν s gm α := by
  intro R _ _ D F _ _ N ν k s a gm α
  have e : (lift (Over.homMk (spMap (algebraMap F (DualNumber F))) rfl : TE R F ⟶ TF (R := R) F) gm.b).left ≫
      (fst (TF (R := R) F) D.P.A).left = spMap (algebraMap F (DualNumber F)) := by
    rw [← Over.comp_left, lift_fst]
    rfl
  unfold jc sE
  rw [← _root_.mul_assoc]
  congr 1
  have h2 : (TrivSqZeroExt.inl a : DualNumber F) = algebraMap F (DualNumber F) a := rfl
  rw [h2]
  exact valR_const_mul _ _ e _ a _

end GlobalTheory.JcSmul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtDualNumberTermValueSmulStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtDualNumberTermValue_smul : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) {k : ℕ} (s : Fam D F k) (a : F) (gm : GtPt D (TE R F)) (α : N.X),
    jc ν (a • s) gm α = TrivSqZeroExt.inl a * jc ν s gm α := by
  first | exact @GlobalTheory.JcSmul.jc_smul | exact GlobalTheory.JcSmul.jc_smul | (intros; apply GlobalTheory.JcSmul.jc_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierInversionSchwartzAdelic
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

noncomputable section

namespace GlobalTheory.TamFourier

theorem fourier_inversion_tamagawa : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ], ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ → ∀ Φ ∈ schA F κ, ∀ x, ∫ y, (∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ) * ψ (y ⬝ᵥ x) ∂μ = Φ (-x) := by
  intro F _ _ hF ψ hψ κ _ inst hB μ hμ Φ hΦ x
  have hFT : ∀ H ∈ schA F κ, (fun y : κ → AF F => ∫ z, H z * ψ (z ⬝ᵥ y) ∂μ) ∈ schA F κ :=
    GlobalTheory.T.adelicFourier_mem_schwartz_totallyReal F hF ψ hψ κ μ hμ.1
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hinst : inst = MeasurableSpace.pi := by
    rw [hB.measurable_eq]
    exact (Pi.borelSpace (ι := κ) (X := fun _ => AF F)).measurable_eq.symm
  subst hinst
  set N := Fintype.card κ
  let e : κ ≃ Fin N := Fintype.equivFin κ
  obtain ⟨lam, hlam⟩ := GlobalTheory.SWQ.exists_isLam F hF ψ hψ
  obtain ⟨ν, hν⟩ := GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one F
  let a : Fin N → F := fun _ => 1 / 2
  have hC : GlobalTheory.SWQ.Ctx ψ lam ν a := ⟨hF, hψ, hlam, hν, fun _ => by norm_num [a]⟩
  have hμeq := GlobalTheory.T.tamagawa_adelicHaar_eq_map_product_measure F κ N e ν hν μ hμ
  let T : (Fin N → AF F) ≃ₜ+ (κ → AF F) := GlobalTheory.PoissonReindex.reidx e
  let Tm : (Fin N → AF F) ≃ᵐ (κ → AF F) := T.toHomeomorph.toMeasurableEquiv
  have hTm : ∀ u, Tm u = T u := fun _ => rfl
  have key : ∀ (H : (κ → AF F) → ℂ) (y' : Fin N → AF F),
      ∫ z, H z * ψ (z ⬝ᵥ T y') ∂μ = GlobalTheory.SWQ.Fo ψ ν a (fun u => H (T u)) y' := by
    intro H y'
    have hm : μ = Measure.map Tm (GlobalTheory.SWQ.muV N ν) := hμeq
    rw [hm, integral_map_equiv]
    simp only [GlobalTheory.SWQ.Fo, hTm, a, GlobalTheory.PoissonReindex.Bd_half, T, GlobalTheory.PoissonReindex.dot_reidx]
  set G : (κ → AF F) → ℂ := fun y => ∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ with hG
  set Φ' : (Fin N → AF F) → ℂ := fun u => Φ (T u) with hΦ'
  have hG' : (fun u => G (T u)) = GlobalTheory.SWQ.Fo ψ ν a Φ' := funext fun u => key Φ u
  have hGG : (fun u => (∫ z, G z * ψ (z ⬝ᵥ T u) ∂μ)) = GlobalTheory.SWQ.Fo ψ ν a (GlobalTheory.SWQ.Fo ψ ν a Φ') := by
    rw [← hG']
    exact funext fun u => key G u
  have hΦs : Φ' ∈ schA F (Fin N) := GlobalTheory.PoissonReindex.mem_schA_reidx e hΦ
  have hGs : G ∈ schA F κ := hFT Φ hΦ
  have hGGs : (fun y : κ → AF F => ∫ z, G z * ψ (z ⬝ᵥ y) ∂μ) ∈ schA F κ := hFT G hGs
  have hD1 : GlobalTheory.SWQ.Decay Φ' := GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ' hΦs
  have hD2 : GlobalTheory.SWQ.Decay (GlobalTheory.SWQ.Fo ψ ν a Φ') := by
    rw [← hG']
    exact GlobalTheory.SchwartzDecay.decay_of_mem_schA F N _ (GlobalTheory.PoissonReindex.mem_schA_reidx e hGs)
  have hD3 : GlobalTheory.SWQ.Decay (GlobalTheory.SWQ.Fo ψ ν a (GlobalTheory.SWQ.Fo ψ ν a Φ')) := by
    rw [← hGG]
    exact GlobalTheory.SchwartzDecay.decay_of_mem_schA F N _ (GlobalTheory.PoissonReindex.mem_schA_reidx e hGGs)
  have hinv := GlobalTheory.SWQ.fourier_inversion F N ψ lam ν a hC Φ' hD1 hD2 hD3
  have hx : T (T.symm x) = x := T.apply_symm_apply x
  have h1 := congrFun hGG (T.symm x)
  rw [hinv, hx] at h1
  have hcomm : ∀ y : κ → AF F, y ⬝ᵥ x = x ⬝ᵥ y := fun y => dotProduct_comm y x
  calc ∫ y, G y * ψ (y ⬝ᵥ x) ∂μ = ∫ z, G z * ψ (z ⬝ᵥ x) ∂μ := rfl
    _ = GlobalTheory.SWQ.Da (-1) Φ' (T.symm x) := h1
    _ = Φ (-x) := by
      simp only [GlobalTheory.SWQ.Da, hΦ', neg_one_smul, map_neg, hx]

end GlobalTheory.TamFourier

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorLiftsToDegenerationPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanLift

theorem isLocalRing_dualNumber (R : Type) [CommRing R] [IsLocalRing R] : IsLocalRing (DualNumber R) :=
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

theorem dualMap_over {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    spMap (dualMap f) ≫ (epsR R).hom = spMap (algebraMap R' (DualNumber R')) ≫ spMap f := by
  show spMap _ ≫ spMap _ = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem redE_over (R : Type) [CommRing R] : redE R ≫ (epsR R).hom = 𝟙 _ := by
  show spMap _ ≫ spMap _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 2

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {I : Ideal R} [IsAdicComplete I R]
  {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem exists_tan (U : UnifPre I D A G) (y : epsR R ⟶ G) (hy : IsTangent y) :
    ∃ gm : GtPt D.toPre (epsR R), TanRel U y gm ∧ GtTan gm ∧ IsTangent gm.b := by
  have hL := D.toPre.P.isLB
  have := isLocalRing_dualNumber R
  have : Module.Finite R (DualNumber R) := inferInstanceAs (Module.Finite R (R × R))
  have := isAdicComplete_map_of_finite I (DualNumber R)
  obtain ⟨g, hg⟩ := IntegralGt.exists_gtPt U (φ := algebraMap R (DualNumber R)) y
  have hz := fun e => hg e _ (thick R I e ≫ redE R) (eSec (thickObj R I e G))
    ((UnitValue.eSec_fGl (G := G) e).trans ((congrArg (thick R I e ≫ ·) hy.symm).trans (Category.assoc _ _ _).symm))
  have hb : redE R ≫ g.b.left = η[D.toPre.P.A].left := hom_ext_of_isHausdorff I fun e =>
    (Category.assoc _ _ _).symm.trans ((hz e).1.symm.trans (UnitValue.eSec_pGl U e))
  refine ⟨g, fun e => ?_, ?_, hb⟩
  · have w : (spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ y.left) ≫ G.hom =
        spMap (algebraMap _ (DualNumber (R ⧸ I ^ (e + 1)))) ≫ thick R I e := by
      rw [Category.assoc, Over.w y]; exact dualMap_over _
    have h₁ : pullback.lift _ _ w ≫ (fstG I e G).left = _ := pullback.lift_fst _ _ _
    obtain ⟨h₂, h₃⟩ := hg e _ _ _ h₁
    refine ⟨_, h₁, h₂, fun χ => corr_of_val hL fun z J hJ => ?_⟩
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    rw [Category.id_comp, Category.id_comp]
    exact h₃ χ z J hJ
  · obtain ⟨o, ho⟩ := FormalValue.exists_isZero D.toPre (baseOver (Sp R))
    have hob : o.b.left = redE R ≫ g.b.left := by
      rw [hb, ho.1]
      exact (congrArg (· ≫ η[D.toPre.P.A].left)
        ((Category.comp_id _).symm.trans (Over.w (toUnit (baseOver (Sp R)))))).trans (Category.id_comp _)
    have e₁ := TorusCoord.comp_eq_of_left g.b o.b (redE R) (𝟙 _) (hob.symm.trans (Category.id_comp _).symm)
    refine ⟨o, ho, hob, fun χ => RedTotal.corr_of_levels I hL (fun W _ f => ?_) (o.isGen χ)
      (DVR.pullGen_isGen _ _ _ _ (g.isGen χ) _) fun e z J hJ => ?_⟩
    · exact Finset.prod_congr rfl fun k _ => congrArg (fun q => f q ^ DegPre.gtε k)
        ((e₁.1 χ k).trans ((Category.id_comp _).trans (congrFun (TorusCoord.gtφT_eq o.b χ) k).symm)).symm
    · refine ((val_corr hJ (ho.2 χ) _).trans (val_one _)).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      refine Eq.trans ?_ ((hz e).2 χ z J hJ)
      have := (val_corr hJ ((U.gt e).t_unit χ) (𝟙 _)).trans (val_one _)
      rw [val_pull hJ, Category.id_comp] at this
      exact this.symm

end GlobalTheory.MBLow.TanLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldImageOpenImmersion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldImageOpenImmersion
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LogKS.FieldImage

variable {Z Z' : Scheme.{0}} (φ : Z' ⟶ Z) [IsOpenImmersion φ]

def appEquiv (O : Z.Opens) (h : O ≤ φ.opensRange) : Γ(Z, O) ≃+* Γ(Z', φ ⁻¹ᵁ O) :=
  haveI := Scheme.Hom.isIso_app φ O h
  (asIso (φ.app O)).commRingCatIsoToRingEquiv

theorem appEquiv_apply (O : Z.Opens) (h : O ≤ φ.opensRange) (f : Γ(Z, O)) :
    appEquiv φ O h f = (φ.app O).hom f := rfl

theorem app_res {W W' : Z.Opens} (h : W' ≤ W) (f : Γ(Z, W)) :
    (φ.app W').hom (resG Z h f) = resG Z' (Scheme.Hom.preimage_mono φ h) ((φ.app W).hom f) := by
  have := congrArg (fun g => g.hom f) (Scheme.Hom.naturality φ (homOfLE h).op)
  simpa [resG] using this


open Classical in
def push (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)) (O : Z.Opens) (f : Γ(Z, O)) : Γ(Z, O) :=
  if h : O ≤ φ.opensRange then (appEquiv φ O h).symm (d (φ ⁻¹ᵁ O) ((φ.app O).hom f)) else 0

theorem app_push (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)) (O : Z.Opens) (h : O ≤ φ.opensRange)
    (f : Γ(Z, O)) : (φ.app O).hom (push φ d O f) = d (φ ⁻¹ᵁ O) ((φ.app O).hom f) := by
  rw [push, dite_eq_left h, ← appEquiv_apply φ O h, RingEquiv.apply_symm_apply]

theorem le_range {W₀ : Z'.Opens} {O : Z.Opens} (hO : O ≤ φ ''ᵁ W₀) : O ≤ φ.opensRange :=
  hO.trans (Scheme.Hom.image_le_opensRange φ W₀)

theorem preimage_le {W₀ : Z'.Opens} {O : Z.Opens} (hO : O ≤ φ ''ᵁ W₀) : φ ⁻¹ᵁ O ≤ W₀ := by
  have := Scheme.Hom.preimage_mono φ hO
  rwa [Scheme.Hom.preimage_image_eq] at this

theorem inj_app {O : Z.Opens} (h : O ≤ φ.opensRange) : Function.Injective (φ.app O).hom :=
  (appEquiv φ O h).injective

theorem isField_push (W₀ : Z'.Opens) (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)) (hd : IsField W₀ d) :
    IsField (φ ''ᵁ W₀) (push φ d) := by
  obtain ⟨hadd, hmul, hres⟩ := hd
  refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_⟩
  · apply inj_app φ (le_range φ hW)
    rw [map_add (f := _), app_push φ d W (le_range φ hW), app_push φ d W (le_range φ hW),
      app_push φ d W (le_range φ hW), map_add, hadd _ (preimage_le φ hW)]
  · apply inj_app φ (le_range φ hW)
    rw [map_add (f := _), map_mul, map_mul, app_push φ d W (le_range φ hW), app_push φ d W (le_range φ hW),
      app_push φ d W (le_range φ hW), map_mul, hmul _ (preimage_le φ hW)]
  · have hW' : W' ≤ φ ''ᵁ W₀ := h.trans hW
    apply inj_app φ (le_range φ hW')
    rw [app_push φ d W' (le_range φ hW'), app_res, app_res, app_push φ d W (le_range φ hW),
      hres _ _ _ (preimage_le φ hW)]

end GlobalTheory.LogKS.FieldImage

theorem GlobalTheory.LogKS.isField_image : ∀ (Z Z' : Scheme.{0}) (φ : Z' ⟶ Z) [IsOpenImmersion φ] (W₀ : Z'.Opens) (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)), IsField W₀ d → ∃ d₂ : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField (φ ''ᵁ W₀) d₂ ∧ ∀ (O : Z.Opens), O ≤ φ ''ᵁ W₀ → ∀ f : Γ(Z, O), (φ.app O).hom (d₂ O f) = d (φ ⁻¹ᵁ O) ((φ.app O).hom f) := by
  intro Z Z' φ _ W₀ d hd
  exact ⟨FieldImage.push φ d, FieldImage.isField_push φ W₀ d hd,
    fun O hO f => FieldImage.app_push φ d O (FieldImage.le_range φ hO) f⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldImageOpenImmersionStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vectorField_image_openImmersion : ∀ (Z Z' : Scheme.{0}) (φ : Z' ⟶ Z) [IsOpenImmersion φ] (W₀ : Z'.Opens) (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)), IsField W₀ d → ∃ d₂ : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField (φ ''ᵁ W₀) d₂ ∧ ∀ (O : Z.Opens), O ≤ φ ''ᵁ W₀ → ∀ f : Γ(Z, O), (φ.app O).hom (d₂ O f) = d (φ ⁻¹ᵁ O) ((φ.app O).hom f) := by
  first | exact @GlobalTheory.LogKS.isField_image | exact GlobalTheory.LogKS.isField_image | (intros; apply GlobalTheory.LogKS.isField_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundStatementHolds
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel.BoundProof

section Gen

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem actV_mem_latT (a : Λ) {y : P.V} (hy : y ∈ P.latT) : P.actV a y ∈ P.latT :=
  (P.mem_latT_iff _).2 fun t => by
    obtain ⟨c, hc⟩ := (P.mem_latT_iff y).1 hy (P.actT (star a) t)
    exact ⟨c, by rw [hc, P.pairV_act]; rfl⟩

theorem pairV_inclT_mem {u : P.V} (hu : u ∈ P.latT) (y : O ⊗[ℤ_[p]] P.T) :
    P.pairV u (P.inclT y) ∈ (algebraMap O C).range := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]⟩
  | tmul c t =>
    obtain ⟨b, hb⟩ := (P.mem_latT_iff u).1 hu t
    refine ⟨c * b, ?_⟩
    have e : (algebraMap O C c ⊗ₜ[ℤ_[p]] t : P.V) = algebraMap O C c • ((1 : C) ⊗ₜ[ℤ_[p]] t) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [P.inclT_tmul, e, map_smul, smul_eq_mul, map_mul, hb]

end Gen

section Gen2

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem pairV_bLie_inclT (x : LieG P.Gt) (y : O ⊗[ℤ_[p]] P.T) :
    P.pairV (P.bLie x) (P.inclT y) = algebraMap O C ((P.al y).1 x) := by
  rw [pairV_bLie_eq_evLie, P.alC_inclT, Point.inclOm, TensorProduct.mk_apply, evLie,
    LinearMap.liftBaseChange_tmul, one_smul]
  rfl

end Gen2

section Discr

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E))

end Discr

end GlobalTheory.FlatModel.BoundProof

namespace GlobalTheory.FlatModel

end GlobalTheory.FlatModel
end
end
