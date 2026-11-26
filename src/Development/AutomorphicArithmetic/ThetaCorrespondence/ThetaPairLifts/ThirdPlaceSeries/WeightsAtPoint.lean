module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ErrorBudgetCondition
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatement
public import Formalism.LocalToGlobal.TieTwRecOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPoint
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPoint
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.QuoWt
section Pt
open IsDedekindDomain _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Pt
theorem weights_at_point_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → 1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 ∧ (∀ u1, Quo p i PP u1 → u1 = (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) ∧ (∀ τ, StrictAnti ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ) ∧ StrictAnti (CompHt.uPrime (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ)) ∧ (∃ w : Psi p.T.Q.H → ℤ, (∀ τ, |w τ| ≤ 3 * ((Fm.D x ι).R.r : ℤ)) ∧ uM p i = (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP) + GlobalTheory.FlatLine.parWt (dat p i) w) ∧ ∀ s : ℕ, s ≤ 3 → ∀ τ, Antitone (uM p i τ + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ) ∧ Antitone (((lenT p i PP + CompHt.dimFlag (dat p i) + (if s = 0 then 3 else 4) : ℕ) : ℤ) • (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ - (uM p i τ + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ)) := by
  intro _
  have hw : _root_.GlobalTheory.CovTop.LiftWeightNumerator := _root_.GlobalTheory.T.lift_weight_numerator
  have hh : _root_.GlobalTheory.CovTop.HostNAlt 1 := _root_.GlobalTheory.CovTop.Sizes.hostN_alt 1
  unfold _root_.GlobalTheory.CovTop.LiftWeightNumerator _root_.GlobalTheory.CovTop.LiftsCondition at hw
  unfold _root_.GlobalTheory.CovTop.HostNAlt _root_.GlobalTheory.CovTop.LiftsCondition at hh
  unfold _root_.GlobalTheory.CovTop.LiftsCondition
  refine Closed.imp (Closed.and hw hh) ?_
  intro eps Fm CH _ h
  obtain ⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩ := h
  refine ⟨0, le_rfl, max x1 x2, fun x hx hle ι p hp i hi => ?_⟩
  exact atPoint p i _ _ _ hi (h1 x hx ((le_max_left _ _).trans hle) ι p hp i)
    (h2 x hx ((le_max_right _ _).trans hle) ι p hp i)
end GlobalTheory.QuoWt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPointStatement
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_parameter_strict_antitone_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → 1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 ∧ (∀ u1, Quo p i PP u1 → u1 = (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) ∧ (∀ τ, StrictAnti ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ) ∧ StrictAnti (CompHt.uPrime (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ)) ∧ (∃ w : Psi p.T.Q.H → ℤ, (∀ τ, |w τ| ≤ 3 * ((Fm.D x ι).R.r : ℤ)) ∧ uM p i = (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP) + GlobalTheory.FlatLine.parWt (dat p i) w) ∧ ∀ s : ℕ, s ≤ 3 → ∀ τ, Antitone (uM p i τ + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ) ∧ Antitone (((lenT p i PP + CompHt.dimFlag (dat p i) + (if s = 0 then 3 else 4) : ℕ) : ℤ) • (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ - (uM p i τ + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ)) := by
  first | exact @_root_.GlobalTheory.QuoWt.weights_at_point_alt | exact _root_.GlobalTheory.QuoWt.weights_at_point_alt | (intros; apply _root_.GlobalTheory.QuoWt.weights_at_point_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ServTIff
set_option synthInstance.maxHeartbeats 200000

section
open Module NumberField IsDedekindDomain
noncomputable section
namespace GlobalTheory.Cp
open _root_.Formalism _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Rows
section Col
variable {X : Formalism.L2.Col.Fields} {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 X.K G Pl0 I0 Ty T m} {P1 : Subgroup G} {ψ1 : P1 →* X.Kˣ}
end Col
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
@[reducible] def SquareIntegrableColumns.toS {T : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex} (K : _root_.GlobalTheory.Cp.SquareIntegrableColumns T P) : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P where
  X := K.X
  e := K.e
  c := K.c.toS
  Sp := K.Sp
  colTie := K.colTie
  kerTie := K.kerTie
  wTie := K.wTie
  lvTie := K.lvTie
  sgTie := K.sgTie
  v0 := K.v0
  TU := K.TU
  xiVal := K.xiVal
  trIv := K.trIv
  famEq := K.famEq
  gEq := K.gEq
  plEq := K.plEq
  i0Eq := K.i0Eq
  tEq := K.tEq
  muTie := K.muTie
  ok1 := K.ok1
@[reducible] def SquareIntegrableColumns.ofS {T : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex} (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) : _root_.GlobalTheory.Cp.SquareIntegrableColumns T P where
  X := K.X
  e := K.e
  c := ColRec3.ofS K.c
  Sp := K.Sp
  colTie := K.colTie
  kerTie := K.kerTie
  wTie := K.wTie
  lvTie := K.lvTie
  sgTie := K.sgTie
  v0 := K.v0
  TU := K.TU
  xiVal := K.xiVal
  trIv := K.trIv
  famEq := K.famEq
  gEq := K.gEq
  plEq := K.plEq
  i0Eq := K.i0Eq
  tEq := K.tEq
  muTie := K.muTie
  ok1 := K.ok1
theorem serv_t_iff_formalism_serv_t (𝒞 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒞) : _root_.GlobalTheory.Cp.SelectionServed 𝒞 sel ↔ _root_.Formalism.L2.G.ServT.SelectionServed 𝒞 sel :=
  ⟨fun h => ⟨h.twU, h.pdv⟩, fun h => ⟨h.twU, h.pdv⟩⟩
end GlobalTheory.Cp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000
section Slot
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ)
def OriginData (K : Ctx) {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) {D : D7} (Wt : Set B.places.Pl) (nch : NChoice D) : Prop :=
  ∃ (P : Pre2 K w) (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x), (ListSt cDep x ∧ SatU P) ∧ Wt = P.Wt ∧ Kept l.c.ch nch
def extensionWithOrigin : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun K B f T w Z Wt p0 t nch n xd c => _root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep K B f T w Z Wt p0 t nch n xd c ×
  PLift (_root_.GlobalTheory.HeightCounting.Up.OriginData hL cDep K w Wt nch)
def GeometricNormExtension : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun K B f T w Z Wt p0 t nch n xd c => _root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep K B f T w Z Wt p0 t nch n xd c × PLift (GoodO (w.D Z) nch xd)
def SpectralFiniteness : Prop := AllSt fun K _ _ _ w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (S : SExt) (Γ : GeoP), (ListSt cDep x ∧ SatU P) →
  ∃ (Z : w.Lt) (v : Lv3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch
def SecondNonvanishing : Prop := ∀ (S : SExt) (Γ : GeoP), Pass KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s) fun K B f T =>
  ∃ w : ColW B f T, Start K B f T w ∧ Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.GeometricNormExtension hL cDep) S Γ).s K B f T w
end Slot
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists)
def FirstStageExists : Prop := AllSt fun _ _ _ _ _ P x => IsEmpty x.o.N.nd.Loc →
  ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x') ∧ SameGal (Dof x) (Dof x')
def ThirdStageExists : Prop := AllSt fun _ B _ T _ _ x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (s : B.places.Pl → (Dof x).ntw.Tw),
  (∀ v, ∃ b, ReadsAt (D := Dof x) (s v) b v) → (∀ v, s (B.places.conj v) = s v) →
  ∃ c : _root_.GlobalTheory.HeightCounting.HeightCountingCharacterData l.mt l.b T.k T.psi, c.ch.twI = s
def MoveToBase : Prop := StepW Start fun K B' f' _ w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' →
  HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ →
  ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x → ∀ (P' : Pre2 K w'), Ext P.z P'.z → ∀ x' : St P', _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x' → SameGal (Dof x) (Dof x') →
    ∃ x'' : St P', Nonempty (_root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x'') ∧ Carried (Dof x) (Dof x'') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x''
end GlobalTheory.HeightCounting.Up
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesUnder
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesUnder
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
namespace GlobalTheory.Fam.QJPlaces
theorem places_under_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads →
    Function.Injective (fun i => (J.G i).q.v) ∧ ∀ i, (J.G i).q.v = (J.pl i).under (𝓞 (I.rec7 l Z).host.F) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ _ t J hJ
  have hund : ∀ i, (J.G i).q.v = (J.pl i).under (𝓞 (I.rec7 l Z).host.F) := by
    intro i
    obtain ⟨ε, hε, he⟩ := (J.G i).q.above
    exact (GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G i).idem hε he).symm
  refine ⟨fun i j hij => ?_, hund⟩
  have h1 : (J.pl i).under (𝓞 (I.rec7 l Z).host.F) = (J.pl j).under (𝓞 (I.rec7 l Z).host.F) := by
    have := hij
    simp only at this
    rw [hund i, hund j] at this
    exact this
  exact hJ.inj (hW.pk.sel _ _ ⟨t, J.mem i⟩ ⟨t, J.mem j⟩ h1)
end GlobalTheory.Fam.QJPlaces
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesUnderStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_local_data_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads →
    Function.Injective (fun i => (J.G i).q.v) ∧ ∀ i, (J.G i).q.v = (J.pl i).under (𝓞 (I.rec7 l Z).host.F) := by
  first | exact @_root_.GlobalTheory.Fam.QJPlaces.places_under_alt | exact _root_.GlobalTheory.Fam.QJPlaces.places_under_alt | (intros; apply _root_.GlobalTheory.Fam.QJPlaces.places_under_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSubgroupAtPlace
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevProd
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
theorem step_index_le_s_alt (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (i : Fin J.r) {j : ℕ} (hj : j + 2 ≤ B.R.m) : j ≤ (J.G i).s := by
  have h1 := (J.G i).hs
  change (J.G i).s + 1 + 1 = B.R.m at h1
  omega
def localHomProduct (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →* ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
  Pi.monoidHom fun i => GlobalTheory.LevIdx.locHom (J.G i).q _ ((J.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega))
def levelSubgroupAtPlace (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) (i : Fin J.r) :
    Subgroup (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
  prX (Cgrp (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev j ((J.G i).s - j + 1) (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega)).J
    ((J.E i).rep j ((J.G i).s - j) (Nat.add_sub_cancel' (_root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj)) (α i)))
def quadraticTwistAtPlace (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop := fun v => ∃ i, (J.G i).q.v = v
def relaxedLevelSubgroup (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  (J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J)) ⊓ GfC _ ⊓
    (Subgroup.pi Set.univ fun i => KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)).comap (_root_.GlobalTheory.LevProd.localHomProduct J j hj)
def upperLevelSubgroup (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (j : ℕ) (hj : j + 2 ≤ B.R.m) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  if h : ∃ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads ∧ Nonempty (J.Ch j) then
    _root_.GlobalTheory.LevProd.relaxedLevelSubgroup h.choose_spec.choose j hj h.choose_spec.choose_spec.2.some
  else ⊥
theorem upperLevelSubgroup_le_GfC (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (j : ℕ) (hj : j + 2 ≤ B.R.m) : _root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj ≤ GfC _ := by
  unfold _root_.GlobalTheory.LevProd.upperLevelSubgroup
  split_ifs
  · intro g hg
    exact (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).2
  · exact bot_le
theorem wt_eq_inv_measure_levelSubgroupAtPlace {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) (i : Fin J.r) :
    (J.E i).wt j (α i) = ((((J.E i).m j (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i)).toReal⁻¹ : ℝ) : ℂ) :=
  (J.E i).wt_mid j ((J.G i).s - j) (Nat.add_sub_cancel' (_root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj)) (α i)
end GlobalTheory.LevProd
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Prm1
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx _root_.Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
end
@[reducible] def parametersOfDependence (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL :=
  _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
end GlobalTheory.Mem.Top.Bl
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatVal
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatVal
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.FlatVal
variable {D : D7} {L : SizeData₂ D}
theorem flat_val_alt : _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict ∧ (∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q) ∧ GlobalTheory.FlatLine.FlatExists Y.U (xiR (Fm.D x ι)) ∧ (∀ τ, |GlobalTheory.FlatLine.c1 Y.U (xiR (Fm.D x ι)) τ + (((dat p i).p : ℝ) - (dat p i).q) / 2 * (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤ 3 * (dat p i).q * (Fm.L x ι).sc.L) ∧ GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes p.T.Q.H Y.d.l₂) ≤ 40 * (Fm.L x ι).sc.L := by
  intro hF
  refine Closed.imp (Closed.and hF (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0)) ?_
  rintro eps Fm CH _ ⟨⟨C, -, h1⟩, A, -, h2⟩
  obtain ⟨x0, h⟩ := h1.and h2
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨a, b⟩ := h x hx hle ι p hp
  have hN := b i
  have hD : GlobalTheory.FlatLine.FlatDegree Y.U _ _ := a i hi Y hY
  have hT := p.fw.laws
  have hj : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨by omega, hi.le⟩
  have hpos := Inhab.rank_pos _ hT.pins _ hj
  refine ⟨isComplexData hT hj hY.1, (GlobalTheory.LawsDeep.laws_deep _ _ _ Y _ _ hT hj hY.1).good, hD.flatExists, fun τ => ?_, ?_⟩
  · rw [hD.c1_eq (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Y.d.Xo₂ Y.d.c₂ hpos).1, hT.pins.1.1]
    have e : ∀ u v : ℝ, -u - v + u = -v := fun u v => by ring
    rw [e, abs_neg, abs_mul, Nat.abs_cast, mul_comm 3, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_log_sub_lrd_le hN) (Nat.cast_nonneg _)
  · exact (GlobalTheory.BadLog.logSum_le_log (GlobalTheory.BadLog.log_level_le (Fm.params x hx ι)).1
      fun q hq => GlobalTheory.BadLog.dvd_of_mem_badPrimes hT.pins hY.1 hq).trans (log_level_le (Fm.params x hx ι) hN)
end GlobalTheory.CovTop.FlatVal
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatValStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_flat_c1_add_logOm_le_and_logSum_badPrimes_le : _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict ∧ (∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q) ∧ GlobalTheory.FlatLine.FlatExists Y.U (xiR (Fm.D x ι)) ∧ (∀ τ, |GlobalTheory.FlatLine.c1 Y.U (xiR (Fm.D x ι)) τ + (((dat p i).p : ℝ) - (dat p i).q) / 2 * (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤ 3 * (dat p i).q * (Fm.L x ι).sc.L) ∧ GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes p.T.Q.H Y.d.l₂) ≤ 40 * (Fm.L x ι).sc.L := by
  first | exact @_root_.GlobalTheory.CovTop.FlatVal.flat_val_alt | exact _root_.GlobalTheory.CovTop.FlatVal.flat_val_alt | (intros; apply _root_.GlobalTheory.CovTop.FlatVal.flat_val_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalMultiplicityFamily
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
variable {x : St P} (L : LocAll (lay0 (Dof x)))
variable (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x)

set_option maxHeartbeats 8000000 in
noncomputable def yStructureLocal : NExpRealS (datL x L).R (datL x L).cG (SL L l.rat) := by
  let Y : NExpRealS (datL x L).R (datL x L).cG (ratL L l.rat.S) := {
    fi := by with_unfolding_all exact (l.b.YS.fi :)
    geq := by with_unfolding_all exact (l.b.YS.geq :)
    rho := by with_unfolding_all exact (l.b.YS.rho :)
    chi := by with_unfolding_all exact (l.b.YS.chi :)
    eF := by
      intro i j b h1 h2
      with_unfolding_all exact (l.b.YS.eF i j b h1 h2 :)
    bsup := by
      intro i j b h1 h2
      with_unfolding_all exact (l.b.YS.bsup i j b h1 h2 :)
    act := by
      intro i j b h1 h2 g y
      with_unfolding_all exact (l.b.YS.act i j b h1 h2 g y :) }
  with_unfolding_all exact (Y :)

noncomputable def heckeHeightData : NExpRealH x.m.z.R x.m.z.cG l.rat.S l.b.YS where
  hL := l.rat.In.hL
  hs := l.b.Bs.hs
  cHk := fun i b k Q => algebraMap ((Dof x).ntw.O i) (FractionRing ((Dof x).ntw.O i)) (l.b.Bs.cHk i b Q) ^ k
  cHk_zero := fun i b Q => pow_zero _
  cHk_unit := fun i b Q =>
    ((l.b.Bs.cHk i b Q).isUnit.map (algebraMap ((Dof x).ntw.O i) (FractionRing ((Dof x).ntw.O i)))).pow 1
  cHk_pow := fun i b k Q => by simp only [pow_one]
  hkEq := by rw [l.b.eF]; exact l.b.Bs.hkEq

noncomputable def localHeckeHeightData : NExpRealH (datL x L).R (datL x L).cG (SL L l.rat) (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) := by
  let Y : NExpRealS (datL x L).R (datL x L).cG (ratL L l.rat.S) := by
    with_unfolding_all exact (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l :)
  let H : NExpRealH (datL x L).R (datL x L).cG (ratL L l.rat.S) Y := {
    hL := by with_unfolding_all exact ((heckeHeightData l).hL :)
    hs := by with_unfolding_all exact ((heckeHeightData l).hs :)
    cHk := by with_unfolding_all exact ((heckeHeightData l).cHk :)
    cHk_zero := by with_unfolding_all exact ((heckeHeightData l).cHk_zero :)
    cHk_unit := by with_unfolding_all exact ((heckeHeightData l).cHk_unit :)
    cHk_pow := by with_unfolding_all exact ((heckeHeightData l).cHk_pow :)
    hkEq := by
      intro i j b h1 h2 k Q y hQ hsplit hk
      with_unfolding_all exact ((heckeHeightData l).hkEq i j b h1 h2 k Q y hQ hsplit hk :) }
  with_unfolding_all exact (H :)

noncomputable def psiVectorLocal : ∀ i : Fin (DL x L).R.m, principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (DL x L) i) (DL x L).R.nV :=
  fun i => (by with_unfolding_all exact ((rowPsi (a := x.o.Z) (oL x L).Z (l.mt.ad.PV ((i)))) : _))
noncomputable def characterChoiceLocal : NChoice (DL x L) := { l.c.ch with }
noncomputable def localCharacterTupleAgreement : TupTied (DL x L) (cfD x L) (characterChoiceLocal L l) :=
  { l.c.tp with }
noncomputable def localMultiplicityFamily : MtFam (DL x L) := fun μ j h1 h2 =>
  { l.mt.M μ j h1 h2 with }
noncomputable def placeMapLocal : HeightOneSpectrum (𝓞 (maximalRealSubfield (DL x L).host.E)) → PlE (DL x L).host := (by with_unfolding_all exact (l.Pq :))
noncomputable def localEigenvalueDegree : ℕ → (DL x L).what₂.FT → ℕ → PlE (DL x L).host → ↥(DL x L).LL0 := (by with_unfolding_all exact (l.rat.In.eig :))
noncomputable def smallPlaceSet : Finset (PlE (DL x L).host) := (by with_unfolding_all exact (l.rat.In.Sb :))
theorem twist_ok_local : ∀ v, TwistedAt (DL x L) v → IntegralHeckeForms.TwOK ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).twI v) ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).k' v) ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).Q v)
    (((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).psi' v).comp ((DL x L).ntw.art ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).twI v) ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).Q v))) := by
  intro v hv
  with_unfolding_all exact (l.c.ok v hv :)

set_option maxHeartbeats 8000000 in
theorem thetaTie_yStructureLocal_nonempty : Nonempty (GlobalTheory.GeoTie.ThetaTie (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.fw (DL x L).nth) := by
  let Y : NExpRealS (datL x L).R (datL x L).cG (ratL L l.rat.S) := by
    with_unfolding_all exact (yStructureLocal L l :)
  with_unfolding_all change Nonempty (GlobalTheory.GeoTie.ThetaTie Y (datL x L).geo.fw (DL x L).nth)
  obtain ⟨g⟩ := l.b.geo
  refine ⟨{ side := ?_, isUnramified₂ := ?_ }⟩
  · intro i j b
    let side := g.side (by with_unfolding_all exact (i :)) (by with_unfolding_all exact (j :)) b
    refine { pt := ?_, cover := ?_, ev_eq := ?_, fmUr := ?_, hk := ?_, hk_none := ?_ }
    · with_unfolding_all exact (side.pt :)
    · intro z
      with_unfolding_all exact (side.cover z :)
    · intro f y
      with_unfolding_all exact (side.ev_eq f y :)
    · intro f
      with_unfolding_all exact (side.fmUr f :)
    · intro k P hP
      with_unfolding_all exact (side.hk k P hP :)
    · intro k P hP y hy c
      with_unfolding_all exact (side.hk_none k P hP y hy c :)
  · intro i
    with_unfolding_all exact (g.isUnramified₂ i :)

theorem kept_characterChoiceLocal : Kept l.c.ch (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) :=
  ⟨sameGaloisL L, twistDataAgreeAcrossCoefficients_localized L, sameFormsL L, (by with_unfolding_all exact ((HEq.refl (Dof x).ntwbr) :)), (by with_unfolding_all exact ((HEq.refl l.c.ch.twI) :)), (by with_unfolding_all exact ((HEq.refl l.c.ch.sd) :)),
    (by with_unfolding_all exact ((HEq.refl l.c.ch.Q) :)), (by with_unfolding_all exact ((HEq.refl l.c.ch.k') :)), (by with_unfolding_all exact ((HEq.refl l.c.ch.psi') :))⟩
theorem yStructureLocal_fi_e_heq : ∀ i y, HEq (((_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l).fi i).e y) y := (by with_unfolding_all exact (l.b.fi :))
end GlobalTheory.HeightCounting.Fin3
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatSmallGenAltAlt
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
theorem latSmallGen_alt : _root_.GlobalTheory.BigOn.Exp.LatticeHasSmallGenerators := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  refine ⟨0, fun x hx _ i p hR hM w _ j ρ hρ hpin h P hP => ?_⟩
  have hL := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hio : IoExt (R2 p) := hR.ioExt
  have hBo : BaseOf (R2 p) j (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) :=
    by
      have h0 := baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
      exact { h0 with }
  exact coefLat_le_span hC ⟨fw2 p⟩ hio j (hL.2.2.2.2.2.2.1 j) _ (hρ.base _ j _) hBo (hρ.isCoefRing _ _)
    (smallInt_isCoefRing _) _ hP
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizeAltBis
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizeAltBis
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
namespace GlobalTheory.CovTop.SizeRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem size_of_alt (h1 : _root_.GlobalTheory.CovTop.HostNAlt 1) (h2 : _root_.GlobalTheory.CovTop.LiftWeightNumerator) : _root_.GlobalTheory.CovTop.SizeCondition := by
  refine (Closed.and h1 h2).imp fun Fm CH _ h => ?_
  obtain ⟨⟨A, hA, hH⟩, _, _, hW⟩ := h
  refine ⟨A + 2, by linarith, ?_⟩
  obtain ⟨x0, h⟩ := hH.and hW
  exact ⟨x0, fun x hx hle ι p hp i => sizeAt_of p i ((h x hx hle ι p hp).1 i) ((h x hx hle ι p hp).2 i)⟩
theorem size_alt_bis : _root_.GlobalTheory.CovTop.SizeCondition := _root_.GlobalTheory.CovTop.SizeRows.size_of_alt (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 1) _root_.GlobalTheory.CovTop.WtShape.wtN_z
end GlobalTheory.CovTop.SizeRows
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizeAltBisStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cov_size_bound : _root_.GlobalTheory.CovTop.SizeCondition := by
  first | exact @_root_.GlobalTheory.CovTop.SizeRows.size_alt_bis | exact _root_.GlobalTheory.CovTop.SizeRows.size_alt_bis | (intros; apply _root_.GlobalTheory.CovTop.SizeRows.size_alt_bis <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieTwRecOf
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT
namespace Formalism.L2.Top4
open Formalism.L2.Top3
section StageB
abbrev SelectionBundle (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel) (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel) (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel) (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    _root_.Formalism.IndefR.RealTBAlt ((sel Fm hc).2 x hx h i) (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp
      (_root_.Formalism.L2.Top4.IndefiniteScaleAtPoint sel selP selDH Fm hc x hx h i) (selS Fm hc x hx h i)
variable {𝒜 : FamClass} {sel : _root_.Formalism.L2.TwistSelection 𝒜} {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel} {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP}
def kernelChoiceOfSelection (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC) : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel :=
  fun Fm hc x hx h i => by
    exact { Ks := (selB Fm hc x hx h i).T.Q.c.F }
def indefiniteRealisationChoiceOfSelection (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC) : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) :=
  fun Fm hc x hx h i => (selB Fm hc x hx h i).Q
def SingleMapCondition (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x)
    (i : Fm.Ix x) : Prop :=
  let B := selB Fm hc x hx h i
  letI := B.alg
  ∀ j, Formalism.IndefR.FWT.OneMapRowR B.T B.Q.Rl.toRealDat B.κ B.v₀ B.O (Formalism.IndefR.phEff B.Q.Rl) j
end StageB
section TwPl
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem real_t_tw_pl_eq (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Q.Rl.twPl = P.S0.Tw :=
  tw_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0
theorem tie_tw_rec_of_real_rec {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks} (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q)
    (hs : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → w ∈ L.supp) : TieTwRec L P.S0.Tw := by
  intro y hy
  rw [← _root_.Formalism.L2.Top4.real_t_tw_pl_eq Q] at hy
  have h := (Qr.tw_iff (D.plEq.symm y)).1 (by simpa using hy)
  exact ⟨hs _ h, h⟩
end TwPl
end Formalism.L2.Top4
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithAtProperty
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.RowEx
open Formalism.L2.Host (HChar)
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
namespace GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
def extensionWithAtProperty (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (A : AtP) : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun K B f T w Z Wt p0 t nch n xd c =>
  N K B f T w Z Wt p0 t nch n xd c × PLift (A K B f T)
end GlobalTheory.Mem.LiteralAutomorphy
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FiniteTOf
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 16000000

section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S
namespace Formalism.L2.Top4Wire2
variable {𝒜 : FamClass} {sel : _root_.Formalism.L2.TwistSelection 𝒜} {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel}
  {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP} {selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel}
def DefRowsFAlt (selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK) {eps : ℝ} (Fm : FamP eps)
    (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) [IsTotallyComplex (Fm.D x i).what₂.LL]
    (C CH : ℝ) : Prop :=
  ∀ (hok1 : (selP Fm hc x hx h i).1.A3.fam3.Ok3 1) (hsep : (selP Fm hc x hx h i).1.A3.fam3.TypesSep3)
    (hP : CovolumeOntoIsometryConditions (selI Fm hc x hx h i).Rl (faceT (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp (_root_.Formalism.L2.Top4.IndefiniteScaleAtPoint sel selP selDH Fm hc x hx h i)) (selI Fm hc x hx h i).sEE (hkCan (selP Fm hc x hx h i).1.A3) C CH) (hI : PassIn3 (selI Fm hc x hx h i).Rl (faceT (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp (_root_.Formalism.L2.Top4.IndefiniteScaleAtPoint sel selP selDH Fm hc x hx h i)) C CH)
    (lam0 C0 ce Sw C1 : ℝ) (H : NumFactsAt Fm x i (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2 lam0 C0 ce Sw C1)
    (NuC : ∀ w, Submodule (𝓞 (Fm.D x i).what₂.LL) (Fin (((selC Fm hc x hx h i).c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).Zs).a w) → (Fm.D x i).what₂.LL))
    (I : DivisionCompatibilityDataThreeSided (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps (selP Fm hc x hx h i).1.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).Zs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).core.base.toIndefData
      (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).core.cols.toIndefData (Fm.ex x hx i).p0 ((selC Fm hc x hx h i).c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).Zs)),
    DivTied3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps (selP Fm hc x hx h i).1.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).Zs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).core.base.toIndefData
      (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).core.cols.toIndefData (Fm.ex x hx i).p0 (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).core.cols.col NuC I →
    HEq I (selP Fm hc x hx h i).1.I → ∀ u, RowsU (selC Fm hc x hx h i).c (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI) (RecNums.ofNum (ofRecord (Fm.D x i) (Fm.L x i) (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2) (Equiv.refl _)
          (letterOf (Fm.D x i) (Fm.L x i) (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2 u) ((Fm.D x i).mem u).A.T (Fm.L x i).Nc lam0 C0 ce Fm.Csz Sw C1 (H u)) (I.wU u) (Cons.nuOf (Fm.L x i) u (I.eNu u))
theorem finite_T_of_squareIntegrableColumns {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {T : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex}
    (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) : Finite P.T := by
  rw [K.tEq]
  exact ((Finset.finite_toSet K.TU).insert _).to_subtype
end Formalism.L2.Top4Wire2
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesInjective
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesInjective
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl
namespace GlobalTheory.TopVol.TwistPlaces
theorem places_injective_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → Function.Injective fun i => (J.G i).q.v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ _ t J hJ i i' hv
  have hv : (J.G i).q.v = (J.G i').q.v := hv
  have und : ∀ n, (J.pl n).under (𝓞 (I.rec7 l Z).host.F) = (J.G n).q.v := fun n => by
    obtain ⟨ε, hε, hε'⟩ := (J.G n).q.above
    exact GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G n).idem hε hε'
  have hs : ∀ n, I.sel (J.G n).q.v = J.pl n := fun n => by
    rw [← und n]
    exact sel_under hW.tr.ok.sel_ok ((hW.tq.Q t _).1 (J.mem n))
  apply hJ.inj
  rw [← hs i, ← hs i', hv]
end GlobalTheory.TopVol.TwistPlaces
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesInjectiveStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_q_v_of_reads : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → Function.Injective fun i => (J.G i).q.v := by
  first | exact @_root_.GlobalTheory.TopVol.TwistPlaces.places_injective_alt | exact _root_.GlobalTheory.TopVol.TwistPlaces.places_injective_alt | (intros; apply _root_.GlobalTheory.TopVol.TwistPlaces.places_injective_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedBy
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.LevZero
open GlobalTheory.ChainOnto (Com)
variable {D : D7}
section Common
variable {c : Comm D} {v : VCom c}
end Common
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
abbrev datZero_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Formalism.L2.DIV.LevDat D.host.E ℂ (Yc D 0).rank :=
  W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)
def levelZeroState (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : StAt (Yc D 0) where
  par := (_root_.GlobalTheory.BaseChain.stageOfSpaceY W 0).par
  M := (_root_.GlobalTheory.BaseChain.stageOfSpaceY W 0).M
  Λ := (_root_.GlobalTheory.Fam.pk_z W).ΛY 0
  β := (_root_.GlobalTheory.Fam.pk_z W).βY 0
  L := _root_.GlobalTheory.LevZero.datZero_alt W
  ν := (_root_.GlobalTheory.BaseChain.stageOfSpaceY W 0).ν
  fd := (_root_.GlobalTheory.BaseChain.stageOfSpaceY W 0).fd
variable {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word}
structure PlacedByLocalGroups (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (v : VCom f.c) (o : TDat f.c k ι) {n : ℕ} (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) : Prop where
  cis : f.c.Is
  vis : v.Is
  tie : _root_.GlobalTheory.Fam.CommutingVectorTie f v
  shape : ShapeOff v o
  pin : GPin G
  read : _root_.GlobalTheory.Fam.LocalGroupReading f G pl
  bot : _root_.GlobalTheory.MiTop.LocalBottomCompatibility f B v o G
set_option maxHeartbeats 1000000 in
def frameAtTranslate (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (a₀ a : GA D (D.sp.X 0)) :
    GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) :=
  finE (D.sp.Y 0) (_root_.GlobalTheory.MiTop.translationElement f B a₀ a) * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0)
set_option maxHeartbeats 1000000 in
def StabiliserCondition (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (a₀ a : GA D (D.sp.X 0)) : Prop :=
  ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a)) ↔
    ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset)
end GlobalTheory.LevZero
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepBeforeLastEqSSucc
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.PenBridge
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n]
end Local
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)}
  {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
  {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
theorem eq_s_succ_of_succ_eq_m (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) {j : ℕ} (hj : j + 1 = B.R.m) (i : Fin J.r) : j = (J.G i).s + 1 := by
  have h1 : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
  omega
def frameAtLevel (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) :
    Frame (J.G i).k ((I.rec7 l Z).sp.X j).rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1)) := by
  subst e
  exact (J.G i).FX _ le_rfl
def reductionHomAtLevel (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →*
      GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k :=
  (toSum0 (J.G i).k _).toMonoidHom.comp (GlobalTheory.LevIdx.locHom (J.G i).q _ (_root_.GlobalTheory.PenBridge.frameAtLevel J j i e))
def reductionHomAtLastLevel (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 1 = B.R.m) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →*
      ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k) :=
  MonoidHom.pi fun i => _root_.GlobalTheory.PenBridge.reductionHomAtLevel J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)
def finitePlaceCondition (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (p : GlobalTheory.FinPl.Pl (I.rec7 l Z)) : Prop := ∃ i, (J.G i).q.v = p
end GlobalTheory.PenBridge
end
namespace GlobalTheory.PenBridge
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n]
end Local
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)}
  {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
  {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
theorem int_in_frame_at_level (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) :
    IntIn (J.G i).q ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.frameAtLevel J j i e) (a.g.x j).L := by
  subst e
  exact fun y => (J.G i).latX _ le_rfl y
theorem rd_at_apply (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :
    _root_.GlobalTheory.PenBridge.reductionHomAtLevel J j i e g = toSum0 (J.G i).k _ (GlobalTheory.LevIdx.locHom (J.G i).q _ (_root_.GlobalTheory.PenBridge.frameAtLevel J j i e) g) := rfl
end GlobalTheory.PenBridge
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColNone
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
namespace GlobalTheory.QPl
variable {D : D7} {c : Comm D} {v : VCom c} {t : Tup c}
end GlobalTheory.QPl
namespace GlobalTheory.Fam
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
def QuadraticExtensionData.eps {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (α : J.Ch j) : GA (I.rec7 l Z) (Yc (I.rec7 l Z) j) →₀ ℂ :=
  if (∃ ρ, j + 2 * ρ + 2 = (I.rec7 l Z).R.m) ∨ j = 0 then J.wt j α • conv (List.ofFn fun i => (J.E i).εL j (α i)) else 0
variable (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t)
def columnChoiceOfCoefficients (kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)))
    (dd : ∀ t j, (J t).Ch j → (J t).Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ)
    (S : ∀ t j, GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j)
    (s : ∀ t j, (J t).Ch j → ℂ) (cV cK : W.P.T → ℕ → ℂ) (cP : W.P.T → ℂ) (t : W.P.T) :
    ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t)) where
  kom := kom t
  Ch := (J t).Ch
  dd := dd t
  e := fun j α => (s t j α • (J t).eps j α).mapDomain (· * a.g.b j)
  eT := fun n _ β => (s t n β • Finsupp.single (1 : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') ((J t).wt n β)).mapDomain (· * a.g.bT)
  Ram := fun j => {φ | (J t).A.RamL (J t).ι j φ}
  S := S t
  rd := fun j α φ y => if hj : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j hj ((J t).ι j α) φ y else 0
  cV := cV t
  cK := cK t
  cP := cP t
def trivialColumnChoice (t : W.P.T) : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t)) where
  kom := fun _ => 1
  Ch := fun _ => Empty
  dd := fun _ α => α.elim
  e := fun _ α => α.elim
  eT := fun _ _ α => α.elim
  Ram := fun _ => ∅
  S := fun _ φ => φ
  rd := fun _ α => α.elim
  cV := 0
  cK := 0
  cP := 0
def familyOfRowColumnChoices (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t)))
    (hCh : ∀ t, (col t).Ch = (J t).Ch) (t : W.P.T) : GlobalTheory.QPl.QFam a.v ((a.fam row col).t t) where
  χ := _root_.GlobalTheory.Fam.chrK_alt W t
  r := (J t).r
  Q := fun i => ((J t).E i).toAt
  eqv := fun j => Equiv.cast (congrFun (hCh t) j)
end GlobalTheory.Fam
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TruePack
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.MiS GlobalTheory.Mem GlobalTheory.Mem.Col2
namespace GlobalTheory.Fam
inductive TruePackAlt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}, _root_.GlobalTheory.MiS.RealPackAlt ex → Prop
  | mk {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
      {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
      {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) :
      _root_.GlobalTheory.Fam.AllFamilyConditions W → TruePackAlt W
def RealPackageCondition {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  (_root_.GlobalTheory.MiS.packageCoefficientSpace W).MIstar2 (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs) W.Q.sEE
end GlobalTheory.Fam
end
end
end
