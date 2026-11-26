module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSISel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposes
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ErrorBudgetCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEigenvalueLowerBoundOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatesOfRationalThetaLiftFromCharacterisatio
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitenessInputsRealData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SecOfDm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnifOfRead
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnifOfRead
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel
noncomputable section
namespace GlobalTheory.LevelUnif
open GlobalTheory.LocMod.PinEx GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum GlobalTheory.SplitWeil GlobalTheory.SymChain
open GlobalTheory.FinPl (SplitPt)
open _root_.Formalism.L2.NTheta (IsIdemAt)
section Elem
variable {κ : Type} [CommRing κ] {r : ℕ}
end Elem
section Local
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)
  {PP : Pl D.host.E} (h : IsIdemAt q.e PP) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
end Local
section Levels
variable {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ}
end Levels
section Gen
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word}
theorem valuation_uniformizer_sub_q_lt (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) {v : VCom f.c} {N : ℕ} (G : Fin N → GLoc v) (pl : Fin N ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) (hR : _root_.GlobalTheory.Fam.LocalGroupReading f G pl)
    (hP : GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg) (n : Fin N) :
    valuation (G n).k ((((G n).S.ϖ : (G n).kˣ) : (G n).k) - ((Formalism.L2.Col.qOf (pl n).1 : ℕ) : (G n).k)) <
      valuation (G n).k (((G n).S.ϖ : (G n).kˣ) : (G n).k) := by
  have hid : ∀ i, IsIdemAt (G i).q.e (pl i).1 := fun i => (hR.idem i).1
  have hq : ∀ i, ∃ t : (G i).kˣ, IsUnif t ∧ (t : (G i).k) = ((Formalism.L2.Col.qOf (pl i).1 : ℕ) : (G i).k) := fun i => by
    obtain ⟨-, hi, hd⟩ := place_facts (G i).q (hid i)
    obtain ⟨t, h1, h2⟩ := GlobalTheory.WeilCondUnif.isUnif_of (pl i).1 ((G i).q.pr.comp (incA D)) hi hd (norm_notMem_sq (hP.1 _ (pl i).2))
    exact ⟨t, h1, h2.trans (map_natCast _ _)⟩
  choose t ht htq using hq
  choose α hα using fun i => exists_res (G i).q (hid i) (G i).S.cond (G i).S.unif
  choose β hβ using fun i => exists_res (G i).q (hid i) (G i).S.cond (ht i)
  obtain ⟨ψ₀, -, h0, π, hπ, hH, hχ⟩ := W.Q.charW.base.grp.levels
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hrS : D.R.rS = D.R.m / 2 - 1 := rfl
  have hA : ∀ c, ψ₀ (pl n).1 c = β n c := fun c => by
    let i : Fin D.R.r := ⟨0, by omega⟩
    let j : Fin D.R.r := ⟨1, by omega⟩
    have hij : i ≠ j := fun e => zero_ne_one (congrArg Fin.val e)
    have hE : ∀ a : Fin D.R.r, ¬ supEdge a a := fun a h => by unfold supEdge at h; omega
    let x : G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r := Pi.mulSingle (pl n) (elem hij c)
    have hx : x ∈ (P0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ψ₀).H :=
      single_mem _ _ (unipCol_le _ 0 0 (elem_mem_unipCol hij zero_lt_one c 0 0 one_ne_zero))
    obtain ⟨hx', e1⟩ := chi_of_eq h0 x hx
    have e2 : (((P0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ψ₀).chi ⟨x, hx⟩ : ℂˣ) : ℂ) = ∏ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, ψ₀ PP.1 (edgeSum supEdge (x PP)) := by
      unfold P0 LevelP.ofLocal
      rw [MonoidHom.finsetProd_apply, Units.coe_prod]
      rfl
    have e3 := W.Q.signs (fun PP => (G (pl.symm PP)).q.e) (fun PP => by
      have := hid (pl.symm PP)
      rwa [pl.apply_symm_apply] at this) ⟨(_root_.GlobalTheory.Fam.pk_z W).eG.symm x, hx'⟩
    have e4 : (((P0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ψ₀).chi ⟨x, hx⟩ : ℂˣ) : ℂ) = _ := (congrArg Units.val e1).symm.trans e3
    rw [e2, ← pl.prod_comp, ← pl.prod_comp, prod_single pl (fun m => ψ₀ (pl m).1) supEdge hE hij rfl] at e4
    rw [e4, ← prod_single pl β supEdge hE hij rfl n c]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [pl.symm_apply_apply, psiAt_eq (G m).q (G m).char]
    change _ = β m (edgeSum supEdge (x (pl m)))
    rw [edgeSum_eq_supSum, ← Function.surjInv_eq Ideal.Quotient.mk_surjective (Formalism.IndefR.Mi.supSum (x (pl m)).val), ← hβ,
      Units.val_inv_eq_inv_val, htq, MulEquiv.apply_symm_apply]
    refine congrArg (fun y => ((G m).S.ψ y : ℂ)) ?_
    change ((G m).q.pr.comp (incA D)) _ = _
    rw [map_mul, map_inv₀, map_natCast]
    rfl
  have hC : ∀ c, ψ₀ (pl n).1 c = α n c := fun c => by
    let i : Fin D.R.r := ⟨D.R.rS, by omega⟩
    let j : Fin D.R.r := ⟨D.R.rS + 1, by omega⟩
    have hij : i ≠ j := fun e => by have := congrArg Fin.val e; simp [i, j] at this
    have hE : ∀ a : Fin D.R.r, ¬ symEdge D.R.rS D.R.k a a := fun a h => by unfold symEdge at h; omega
    have hEij : symEdge D.R.rS D.R.k i j := Or.inl ⟨rfl, by show D.R.rS + 1 ≠ _; omega, by show D.R.rS + 1 ≠ _; omega⟩
    let y : G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r := Pi.mulSingle (pl n) (elem hij c)
    have hy : y ∈ (PsharpSym (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r D.R.rS D.R.k ψ₀).H :=
      single_mem _ _ (elem_mem_unipCol hij (Nat.lt_succ_self _) c _ _ (by show D.R.rS + 1 ≠ _; omega))
    let g : G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r := reord π.symm y
    have hgy : ∀ PP a b, (y PP).val a b = (g PP).val (π a) (π b) := fun PP a b => by
      change _ = (y PP).val (π.symm (π a)) (π.symm (π b))
      rw [π.symm_apply_apply, π.symm_apply_apply]
    have hre : reord π g = y := funext fun PP => Units.ext (Matrix.ext fun a b => (hgy PP a b).symm)
    have hg : g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := (hH g).2 (hre ▸ hy)
    choose x hx using (hR.lev g).1.1 hg
    have e1 := (hR.lev g).2 hg x hx
    have e2 : (_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨g, hg⟩ = (PsharpSym (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r D.R.rS D.R.k ψ₀).chi ⟨y, hy⟩ :=
      (hχ g hg (hre ▸ hy)).trans (congrArg _ (Subtype.ext hre))
    have e3 : (((PsharpSym (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r D.R.rS D.R.k ψ₀).chi ⟨y, hy⟩ : ℂˣ) : ℂ) =
        ∏ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, ψ₀ PP.1 (edgeSum (symEdge D.R.rS D.R.k) (y PP)) := by
      unfold PsharpSym LevelP.ofLocal
      rw [MonoidHom.finsetProd_apply, Units.coe_prod]
      rfl
    rw [← e2, e1, ← pl.prod_comp, prod_single pl (fun m => ψ₀ (pl m).1) _ hE hij hEij, Units.coe_prod] at e3
    rw [← e3, ← prod_single pl α _ hE hij hEij n c]
    refine Finset.prod_congr rfl fun m _ => ?_
    have h1 := (G m).hs
    have h2 := (G m).S.odd
    have hρ : D.R.rS = (G m).S.ρ := by omega
    let e : Fin D.R.k ⊕ Fin ((G m).s + 1) ≃ Fin D.R.r := finSumFinEquiv.trans (finCongr (by omega))
    have he : ∀ a, (e a).val = framePos _ _ a := by rintro (a | a) <;> simp [e, framePos]
    have := sym_chr (G m).S (prO (G m).q) e he (hρ ▸ hπ) (g (pl m)) (y (pl m)) (hgy _) (α m) (hα m) (x m)
      fun a b => hx m a b _ _ (he a) (he b)
    rw [← hρ] at this
    exact this
  rw [← htq]
  exact near_of_res (G n).q (hid n) (G n).S.cond (G n).S.unif (ht n) fun z =>
    Circle.coe_injective ((hα n z).trans (((hC _).symm.trans (hA _)).trans (hβ n z).symm))
end Gen
theorem int_and_unif_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ n : Fin a.n, (∀ x : (I.rec7 l Z).host.E, (ofSplit (a.G n).q).pr x ∈ 𝒪[(a.G n).k] ↔ Formalism.L2.Col.IntAt (a.pl n).1 x) ∧ valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k)) < valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _ _ n
  have hR := (ha.tie (fun t => (GlobalTheory.Fam.TopLocFac.nonempty_rowCh (D := I.rec7 l Z) _ _ u a.g W.Q.stdChar t).some)
    fun t => (GlobalTheory.Fam.TopLocFac.nonempty_colCh (D := I.rec7 l Z) u _).some).2
  have h2 := _root_.GlobalTheory.LevelUnif.valuation_uniformizer_sub_q_lt (D := I.rec7 l Z) _ _ _ hR hW.lev.1 n
  exact ⟨(place_facts (a.G n).q (hR.idem n).1).2.1, h2⟩
end GlobalTheory.LevelUnif
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnifOfReadStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_commutation_twist_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ n : Fin a.n, (∀ x : (I.rec7 l Z).host.E, (ofSplit (a.G n).q).pr x ∈ 𝒪[(a.G n).k] ↔ Formalism.L2.Col.IntAt (a.pl n).1 x) ∧ valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k)) < valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) := by
  first | exact @_root_.GlobalTheory.LevelUnif.int_and_unif_alt | exact _root_.GlobalTheory.LevelUnif.int_and_unif_alt | (intros; apply _root_.GlobalTheory.LevelUnif.int_and_unif_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FinXRowOfGap
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Top4 Formalism.L2.SG.JoinSI Formalism.L2.SG.PackageTie2
namespace Formalism.L2.SG.JoinSISel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section At
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
end At
abbrev IndefiniteRealisationSelection (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel) (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel) (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP) (selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel) (selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    _root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin (R := (sel Fm hc).2 x hx h i) (S := selS Fm hc x hx h i) (Q := selI Fm hc x hx h i)
variable {𝒜 : FamClass} {sel : _root_.Formalism.L2.TwistSelection 𝒜} {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel}
  {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP} {selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel} {selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK}
theorem closed_finX_of_gapHyp (hFXC : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC)
    (hG : Closed 𝒜 fun Fm _ => ∀ hc : 𝒜 Fm, _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm hc fun x _ _ i => Formalism.L2.SG.ConcreteSettingExists.GapHyp (Fm.D x i)) :
    Closed 𝒜 fun Fm _ => ∀ hc : 𝒜 Fm, _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm hc fun x hx h i => FinX (selS Fm hc x hx h i).Y :=
  hG.imp fun Fm _ _ H hc => by
    obtain ⟨x0, H'⟩ := H hc
    exact ⟨x0, fun x hx h hx0 i => hFXC _ (selS Fm hc x hx h i).toSTies (H' x hx h hx0 i)⟩
end Formalism.L2.SG.JoinSISel
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedPrim
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod
namespace GlobalTheory.MiTop
section Prim
open GlobalTheory.FinPl
variable {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
variable {v : VCom c} {o : TDat c k ι}
end Prim
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
def PlacedPrimitiveConditions : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
    (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg),
    f.c.Is ∧ v.Is ∧ _root_.GlobalTheory.Fam.CommutingVectorTie f v ∧ ShapeOff v o ∧ GPin G ∧ _root_.GlobalTheory.Fam.LocalGroupReading f G pl ∧ _root_.GlobalTheory.MiTop.LocalBottomCompatibility f B v o G ∧ TopPrim v o
variable {f B}
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Fire
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Fire
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FireAtRealisation
theorem fire_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S), B.Q.Rl.toRealDat.ExAt ∧ JEvBar B.T B.Q.Rl.toRealDat B.κ ∧ GeoAct B.T B.Q.Rl.toRealDat B.κ B.v₀ ∧ EvInj B.T B.Q.Rl.toRealDat B.v₀ := by
  intro h1 h2 h3 h4 D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B
  have c := B.Q.charW.base
  exact ⟨GlobalTheory.T.intertwinersAndLifts_exist_at_choices h1 h2 h3 h4 D _ _ _ _ _ _ c.lev c.fam c.models c.grp.record B.Q.host c.chain c.thP,
    GlobalTheory.ConjReading.jEvBar B.T _ B.κ B.v₀ B.O c.lev c.models B.fw B.pins,
    GlobalTheory.GeometricAction.geoAct B.T _ B.κ B.v₀ B.O c.lev c.models B.fw B.pins B.equivAll,
    GlobalTheory.EvalAtUnitVectorFinal.evInj_of_isModels_of_tie B.T _ B.κ B.v₀ c.models B.fw⟩
end GlobalTheory.FireAtRealisation
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FireStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_scale_theta_equality_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S), B.Q.Rl.toRealDat.ExAt ∧ JEvBar B.T B.Q.Rl.toRealDat B.κ ∧ GeoAct B.T B.Q.Rl.toRealDat B.κ B.v₀ ∧ EvInj B.T B.Q.Rl.toRealDat B.v₀ := by
  first | exact @_root_.GlobalTheory.FireAtRealisation.fire_alt | exact _root_.GlobalTheory.FireAtRealisation.fire_alt | (intros; apply _root_.GlobalTheory.FireAtRealisation.fire_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMore
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMore
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.VacTheta
theorem main_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j, j + 1 ≤ B.R.m → IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.g.vac j) ∧ IsLatVac (heisO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _) (stdHom _ _) (a.g.vac j) ∧ IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha hTr j hj
  have hv := hTr.pinX.vc j (by omega)
  refine ⟨hv.2.theta, hv.2.lat, ?_⟩
  exact (GlobalTheory.HeisComb.main _ (_root_.GlobalTheory.Fam.pk_z W).ψ _ _).2.2.1 (a.v.dT j) (a.g.vac j) hv.2.theta
    (isFinComb_of_combAt (ha.vis.atT j).1) hv.1
end GlobalTheory.Fam.VacTheta
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_chain_descent_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j, j + 1 ≤ B.R.m → IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.g.vac j) ∧ IsLatVac (heisO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _) (stdHom _ _) (a.g.vac j) ∧ IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j)) := by
  first | exact @_root_.GlobalTheory.Fam.VacTheta.main_alt_alt | exact _root_.GlobalTheory.Fam.VacTheta.main_alt_alt | (intros; apply _root_.GlobalTheory.Fam.VacTheta.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadInj
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadInj
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
theorem readInj_alt : _root_.GlobalTheory.BigOn.Exp.ReadInjAlt := by
  unfold _root_.GlobalTheory.BigOn.Exp.ReadInjAlt _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, fun x hx _ i p hr hm w _ j ρ hρ ν hν => ?_⟩⟩⟩
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  exact (GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ _ j _ ν hν hU hW (Z.vec j) hK).injective
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadInjStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.read_injective : _root_.GlobalTheory.BigOn.Exp.ReadInjAlt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.readInj_alt | exact _root_.GlobalTheory.BigOn.Exp.readInj_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.readInj_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AllRows
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top
namespace GlobalTheory.Fc
structure AllRowsAlt (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) (N : FamClass → Prop)
    (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType) : Prop where
  hn4 : Lg1 KP Q Q' fun S => R0.ClassCountBoundAtConstructedPoints S Lk
  jOn : Lg1 KP Q Q' fun S => R0.JInvariantConditionAtConstructedPoints S Lk
  hInstR : Lg1 KP Q Q' fun S => ClassTwoEntries.InstanceRankAtConstructedPoints S Lk
  aC2 : Lg1 KP Q Q' fun S => ClassTwoEntries.DivisionSecondComplementAtConstructedPoints S Lk
  aP10 : Lg1 KP Q Q' fun S => AllBundlePointProperties.LevelPrimeColumnValuationsAtBundlePoints S Lk
  aAtG : Lg1 KP Q Q' fun S => AllBundlePointProperties.ArithmeticConditionAtBundlePoints S Lk
  aPt0 : Lg1 KP Q Q' fun S => PeriodEntriesOverColumns.ReferenceChainEvaluationAtBundlePoints S Lk
  aPtTw : Lg1 KP Q Q' fun S => PeriodEntriesOverColumns.TwistedPointAtBundlePoints S Lk
  aPer0 : Lg1 KP Q Q' fun S => PeriodEntriesOverColumns.PeriodAtZeroAtBundlePoints S Lk
  aPerTw : Lg1 KP Q Q' fun S => PeriodEntriesOverColumns.TwistedPeriodAtBundlePoints S Lk
  tie : Lg1 KP Q Q' fun S => PeriodEntriesOverColumns.Row_tie S Lk
  hRB : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotRowBoundCondition S Lk
  hTw : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotTwistCondition S Lk
  hPA : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition S Lk
  hLamP : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotLambdaPrimeCondition S Lk
  hDivG : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotDivisorCondition S Lk
  hDcPtG : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotDecompositionPointCondition S Lk
  selJ : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotSelectionJumpCondition S Lk
  sLp : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotLpCondition S Lk
  sO : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotOrderCondition S Lk
  hServ : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotServiceCondition S Lk
  zL : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotZeroLocusCondition S Lk
  hTF : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotTorsionFreeCondition S Lk
  c30 : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.CountsIrreducibilityConstants' S Lk
  rRows : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotDefiniteRowsCondition DR S Lk
  nRest : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotNormCondition S Lk N
end GlobalTheory.Fc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ICBaseFactorOfRows
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ICBaseFactorOfRows
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BigTop.Fun
theorem iC_base_factor_of_rows_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → Function.Injective ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0) ∧ ∀ (t : Tup p) (y : Fin ((Df p).dQ t) → D.what₂.LL), (p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (cpt p.P.A3.fam3.base3.v0.embedding (((p.S false).ι t).mulVec y)) = (p.R.toCx3 p.F).iC p.F.cr false t (cpt p.P.A3.fam3.base3.v0.embedding y) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  have h2 := (hCx.what₂ false).1
  have hr := hCx.ratMu false
  refine ⟨h2.1, fun t y => ?_⟩
  have hspec := relMat_spec ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0)
    ((p.R.toCx3 p.F).iC p.F.cr false t)
    (fun k => by rw [← (h2.2.1 t).2]; exact LinearMap.mem_range_self _ _)
  show (p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0
      (cpt p.P.A3.fam3.base3.v0.embedding ((kMat p.P.A3.fam3.base3.v0.embedding ((p.R.toCx3 p.F).rowMatC p.F.cr false t)).mulVec y)) = _
  rw [cpt_mulVec, kMat_map _ (hr t)]
  exact hspec _
end GlobalTheory.BigTop.Fun
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ICBaseFactorOfRowsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iC_iota_mulVec_eq_iC : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → Function.Injective ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0) ∧ ∀ (t : Tup p) (y : Fin ((Df p).dQ t) → D.what₂.LL), (p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (cpt p.P.A3.fam3.base3.v0.embedding (((p.S false).ι t).mulVec y)) = (p.R.toCx3 p.F).iC p.F.cr false t (cpt p.P.A3.fam3.base3.v0.embedding y) := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.iC_base_factor_of_rows_alt | exact _root_.GlobalTheory.BigTop.Fun.iC_base_factor_of_rows_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.iC_base_factor_of_rows_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuoShape
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuoShape
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.RefSum.QuoShape
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem quo_shape_dom_lastPos_weight_eq : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → 1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ (dat p i).p + (dat p i).q = (Fm.D x ι).R.r ∧ (∀ τ, Antitone (u1 τ)) ∧ (∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = (dat p i).p → (b : ℕ) = (dat p i).p → (nCol (dat p i) : ℤ) + 1 ≤ u1 τ a - u1 τ b) ∧ (∀ τ a, |(u1 τ a : ℝ)| ≤ 2 * (Fm.L x ι).sc.b) ∧ Dom (aOf p i u1) (nCol (dat p i)) ∧ LastPos (dat p i) (aOf p i u1) ∧ GOf p i u1 = wtOf (dat p i) (u1 + parWt (dat p i) (shift (dat p i) u1 (nCol (dat p i)))) ((nCol (dat p i) / 2 : ℕ) : ℤ) := fun _ =>
  Formalism.MainNotions.Closed.imp _root_.GlobalTheory.T.lift_weight_numerator fun Fm _ _ ⟨C, h0, a, h⟩ => ⟨C, h0, a, fun x hx hle ι p hp i hi u1 hq => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := shape_at p i
      ((one_le_pow₀ (SizeTZ.one_le_zBase _)).trans (SizeTZ.pow_le_PP (Fm.parT x hx ι))) (h x hx hle ι p hp i) hi u1 hq
    have hev : Even (nCol (dat p i)) := even_iff_two_dvd.2 (Dvd.dvd.trans (by norm_num) eight_dvd_nCol)
    obtain ⟨b1, b2, b3, -⟩ := GlobalTheory.T.thetaExponents_dominant_lastEntry_one_degree _ _ (dat p i) u1 (nCol (dat p i)) _ a1 hev a4 a5 a6
    exact ⟨a1, a2, a3, a4, a5, a6, b1, b3, b2⟩⟩
end GlobalTheory.RefSum.QuoShape
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuoShapeStatement
set_option synthInstance.maxHeartbeats 200000

section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_weight_gap_bounds' : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → 1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ (dat p i).p + (dat p i).q = (Fm.D x ι).R.r ∧ (∀ τ, Antitone (u1 τ)) ∧ (∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = (dat p i).p → (b : ℕ) = (dat p i).p → (nCol (dat p i) : ℤ) + 1 ≤ u1 τ a - u1 τ b) ∧ (∀ τ a, |(u1 τ a : ℝ)| ≤ 2 * (Fm.L x ι).sc.b) ∧ Dom (aOf p i u1) (nCol (dat p i)) ∧ LastPos (dat p i) (aOf p i u1) ∧ GOf p i u1 = wtOf (dat p i) (u1 + parWt (dat p i) (shift (dat p i) u1 (nCol (dat p i)))) ((nCol (dat p i) / 2 : ℕ) : ℤ) := by
  first | exact @_root_.GlobalTheory.RefSum.QuoShape.quo_shape_dom_lastPos_weight_eq | exact _root_.GlobalTheory.RefSum.QuoShape.quo_shape_dom_lastPos_weight_eq | (intros; apply _root_.GlobalTheory.RefSum.QuoShape.quo_shape_dom_lastPos_weight_eq <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EV0MemGoodF
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EV0MemGoodF
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BigTop.Fun
theorem eV0_mem_goodF_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → ∀ (t : Tup p) (y : Fin ((Df p).nV t) → D.what₂.LL), eV0 p t y ∈ (p.P.A3.A.fam.R t).goodF p.P.A3.A.fam.X := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ t y
  set B := p.P.A3.A.fam.R t
  set F := p.P.A3.A.fam
  obtain ⟨u, hu⟩ := Formalism.IndefR.CxPass.PassRep.range_vE_le B F.X p.P.P0 p.P.ψ0 ⟨y, rfl⟩
  have hrange : LinearMap.range (B.vE ⟨F.X, ⊥, 1⟩).mulVecLin =
      LinearMap.range (B.S.gaMat B.r (goodAt F.X ⊥ 1)).mulVecLin :=
    (image_idempotent_spec _ _ (B.S.gaMat B.r (goodAt F.X ⊥ 1))).2
  obtain ⟨z, hz⟩ : (B.vE ⟨F.X, ⊥, 1⟩).mulVecLin u ∈ LinearMap.range (B.S.gaMat B.r (goodAt F.X ⊥ 1)).mulVecLin :=
    hrange ▸ ⟨u, rfl⟩
  refine ⟨B.S.basis.equivFun.symm z, B.S.basis.equivFun.injective ?_⟩
  rw [← CSD.gaMat_mulVec_equivFun, LinearEquiv.apply_symm_apply]
  simp only [Matrix.mulVecLin_apply] at hu hz
  rw [hz, hu]
  show _ = B.S.basis.equivFun (B.S.basis.equivFun.symm ((B.vE (F.lvl p.P.P0 p.P.ψ0)).mulVecLin y))
  rw [LinearEquiv.apply_symm_apply]
  rfl
end GlobalTheory.BigTop.Fun
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EV0MemGoodFStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eV0_mem_goodF' : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → ∀ (t : Tup p) (y : Fin ((Df p).nV t) → D.what₂.LL), eV0 p t y ∈ (p.P.A3.A.fam.R t).goodF p.P.A3.A.fam.X := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.eV0_mem_goodF_alt | exact _root_.GlobalTheory.BigTop.Fun.eV0_mem_goodF_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.eV0_mem_goodF_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeepLatticeEqLevelLatticeOfCovers
set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.TypeLattice
section Forms
open NumberField Formalism.BasicNotions _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.LevPull (CongMod)
open GlobalTheory.LevDesc (transl)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBC
end Forms
end GlobalTheory.CovTop.TypeLattice
namespace GlobalTheory.CovTop.TypeLattice
section Point
open NumberField Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Pj _root_.Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.BigTop GlobalTheory.AllWt
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed grpHR latN chiHR genChar transl)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU)
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
end Point
section Main
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.LevDesc (TypeFrame grpHR latN)
theorem exists_psi_latDeep_eq_latN_of_covers : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∃ (fr : TypeFrame (dat p i) Y.d.l₂) (ψ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.Sq (Fm.D x ι).host, AddChar (ZMod ((Fm.D x ι).host.g v.1)) Y.d.c₂.F), (∀ v, ψ v ≠ 1) ∧ GlobalTheory.LevDesc.IsTypeLevel Y.d.l₂ ∧ latDeep p i Y = latN fr Y.U (Gk p i) ψ ∧ Real.log (Nat.card (grpHR fr)) ≤ 45 * zBase (Fm.L x ι) ^ 2 := by
  intro _ _ _
  refine _root_.GlobalTheory.CovTop.CovSz.covers_of_lifts_alt (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0) ?_
  intro eps Fm x hx ι p i C _ hN _ Y hY
  obtain ⟨fr, ψ, h1, h2, h3⟩ := latDeep_eq_latN p i Y hY.1
  exact ⟨fr, ψ, h1, h2, h3, log_card_le p i Y hY hN _⟩
end Main
end GlobalTheory.CovTop.TypeLattice
end
end
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
theorem _root_.GlobalTheory.T.exists_psi_isTypeLevel_latDeep_eq_latN : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∃ (fr : TypeFrame (dat p i) Y.d.l₂) (ψ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.Sq (Fm.D x ι).host, AddChar (ZMod ((Fm.D x ι).host.g v.1)) Y.d.c₂.F), (∀ v, ψ v ≠ 1) ∧ GlobalTheory.LevDesc.IsTypeLevel Y.d.l₂ ∧ latDeep p i Y = latN fr Y.U (Gk p i) ψ ∧ Real.log (Nat.card (grpHR fr)) ≤ 45 * zBase (Fm.L x ι) ^ 2 := by
  first | exact @_root_.GlobalTheory.CovTop.TypeLattice.exists_psi_latDeep_eq_latN_of_covers | exact _root_.GlobalTheory.CovTop.TypeLattice.exists_psi_latDeep_eq_latN_of_covers | (intros; apply _root_.GlobalTheory.CovTop.TypeLattice.exists_psi_latDeep_eq_latN_of_covers <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Hyps
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT
namespace GlobalTheory.Fc
open GlobalTheory.Cp
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure HypsAlt (N : FamClass → Prop) (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType) : Type 1 where
  𝒜 : FamClass
  σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜
  cT : ℝ → ℝ → ℝ
  hEx : MinkDiv → UpperTheory.Top.ExS 𝒜 cT
  hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm
  hRB : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((_root_.GlobalTheory.Fc.familySelection σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows ((_root_.GlobalTheory.Fc.selectionBundleOfRawSelection σ) Fm hc x hx h i)
  hTw : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((_root_.GlobalTheory.Fc.familySelection σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.TieTwRec (Fm.L x i) ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm hc x hx h i).1.S0.Tw
  hPA : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (_root_.GlobalTheory.Fc.familySelection σ Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.IndefR.Links.PrimRows3 (_root_.GlobalTheory.Fc.selectionBundleOfRawSelection σ Fm hc x hx h i).Q.Rl (_root_.GlobalTheory.Fc.selectionBundleOfRawSelection σ Fm hc x hx h i).Q.F ∧ (_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ Fm hc x hx h i).1.A3.fam3.TypesSep3
  hLamP : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((_root_.GlobalTheory.Fc.familySelection σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.Rows.RowsHoldLam3 ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm hc x hx h i).1
  hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((_root_.GlobalTheory.Fc.familySelection σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      DivRows3G ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm hc x hx h i).1
  hDcPtG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((_root_.GlobalTheory.Fc.familySelection σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      DcPtG ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm hc x hx h i).1
  hTu : Closed (WithTw (WithSm (WithChN 𝒜))) fun {eps} Fm _ => cT eps Fm.CYL ≤ Fm.CTu → TuSize Fm
  hn4 : Closed (WithTw (WithSm (WithChN 𝒜))) fun Fm _ => ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
      StandardLattice.ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev
  hLit : LitThin
  hWu : Formalism.L2.SG.Pf.WuDecayOfGap
  hRF : Formalism.L2.SG.RowsDef.RowsFinDim
  hTF : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3
  c30 : List ℝ → Formalism.MainNotions.S.CountingConstants
  hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A
  sTy : Formalism.L2.SG.RowsPos.TypeP
  sNG : Formalism.L2.SG.RowsPos.RowNGP
  sM : Formalism.L2.SG.RowsPos.RowMainEqP
  sLp : Formalism.L2.SG.ThmSOwn.LoopRowS 3 (D3 3 𝒜) (fun Fm hc => ⟨((_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc)).1, fun x hx h i => ((_root_.GlobalTheory.Fc.spectralConditionOfRawSelection σ) Fm (d3_a hc) x hx h i).toSTies⟩)
  sO : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, Formalism.L2.SG.ThmSOwn.TheoremSSelected Fm 3
      ⟨((_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc)).1, fun x hx h i => ((_root_.GlobalTheory.Fc.spectralConditionOfRawSelection σ) Fm (d3_a hc) x hx h i).toSTies⟩
  h30 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.S.CountE.CountAllPointsClass Formalism.L2.SG.ThmSOwn.PLevT' Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb
  hInstR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((_root_.GlobalTheory.Fc.familySelection σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep (Fm.D x i) ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) ((Fm.D x i).sp.Y 0).rank
  selJ : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (_root_.GlobalTheory.Fc.familySelection σ Fm hc).1 ≤ x) (i : Fm.Ix x),
      _root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin (R := (_root_.GlobalTheory.Fc.familySelection σ Fm hc).2 x hx h i) (S := _root_.GlobalTheory.Fc.spectralConditionOfRawSelection σ Fm hc x hx h i) (Q := (_root_.GlobalTheory.Fc.selectionBundleOfRawSelection σ Fm hc x hx h i).Q)
  jOn : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ((Fm.D x i).what₂.V0 (Fm.D x i).what₂.mu0).map ((Fm.D x i).what₂.iota (Fm.D x i).what₂.mu0) = ⊤
  hMt : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (μ : (Fm.D x i).what₂.Tup) (a : NumberField.RingOfIntegers (Fm.D x i).what₂.LL),
      ∀ y ∈ ((Fm.D x i).what₂.Mtilde μ).carrier, (Fm.D x i).what₂.embLL (a : (Fm.D x i).what₂.LL) • y ∈ ((Fm.D x i).what₂.Mtilde μ).carrier
  rRows : _root_.GlobalTheory.Fc.R1.SelectionDefiniteRows DR 𝒜 σ
  aPt0 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u
  aPtTw : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPointIntegral (Fm.D x i) (Fm.ex x hx i).tw
  aPer0 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (Fm.D x i)
  aPerTw : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw
  aP10 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT (Fm.X x i) (Fm.ex x hx i).tw u
  aAtG : Closed (D3 3 𝒜) fun Fm _ => ∃ C1 : ℝ, (∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1
  aC2 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm
  hServ : _root_.GlobalTheory.Cp.SelectionServed (D3 3 𝒜) fun Fm hc => (_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc)
  cIc : ℝ
  hcI : 0 < cIc
  irrC : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i),
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.CountAllRows A (Formalism.L2.GlobalTheoryTheory.ConcN.epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f)
  zL : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, ∃ xr : ℝ, ∀ x (hx : Fm.x1 < x) (h : ((_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc)).1 ≤ x), xr ≤ x →
      ∀ (i : Fm.Ix x) (k : Fin (Fm.D x i).R.m),
        Function.Surjective (Formalism.L2.DIV.lPrj (Fm.D x i) ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.A3.A ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.P0
          ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.ψ0 (((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.A3.fam3.toSub2 ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.Zs) k
          ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.A3.A.μ0).mulVec
  tie : Closed (D3 3 𝒜) fun Fm _ => RealPlaceSecondLayerConditions Fm
  hU : ∀ D, MassRatioUnderVolume D
  hG : ∀ D, GenusMassVolumes.GenusMassAt D 2
  nRest : N (D3 3 𝒜)
end GlobalTheory.Fc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjMemRowsIff
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjMemRowsIff
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.FamTrace.Rows
open GlobalTheory.FinPl
section Gen
variable {D : D7}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Gen
section Loc
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Loc
section Real
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem mem_rJ_iff_finE_mem_St_and_block_mem (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (y : GA D (Yc D 0)) (hy : y ∈ GfC (Yc D 0)) :
    (show GA D (D.sp.Y 0) from y) ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ finE (Yc D 0) y ∈ St ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ∧
      (fun PP : (_root_.GlobalTheory.Fam.pk_z W).Pg => upperLeftBlock (r_le_Y 0) (redFn ((_root_.GlobalTheory.Fam.pk_z W).βY 0) PP.1 (finE (Yc D 0) y))) ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := by
  have hn : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _)]
    simp [Formalism.BasicNotions.Ranks.rankY]
  have key := (GlobalTheory.LevYZero.lev_datY_zero (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) _ D.R.r D.R.t (r_le_Y 0) hn (_root_.GlobalTheory.Fam.pk_z W).Pg (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi
    (fun _ => 1) rfl (finE (Yc D 0) y) (GlobalTheory.LevSplit.finE_mem_UA _ y)).1
  exact Iff.trans ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩ key
set_option maxHeartbeats 1000000 in
theorem main_alt_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) (u : D.what₂.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (ha : a.Is)
    (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t)))
    (x : GA D (Yc D 0)) (hx : x ∈ GfC (Yc D 0)) :
    (show GA D (D.sp.Y 0) from (a.g.b 0)⁻¹ * x * a.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ _root_.GlobalTheory.FamTrace.InLevelGroupOfY a x := by
  obtain ⟨hV, hG⟩ := ha.tie row col
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hb : a.g.b 0 ∈ GfC (Yc D 0) := by
    have h1 := ha.vis.b 0
    rw [hV.b 0] at h1
    exact h1
  have hsd := hW.bot.hyp.2.2.2.1.lev.βY 0 hm
  have hΛ := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hsd
  obtain ⟨c, hβ, -⟩ := hsd
  have hoff := GlobalTheory.StMoves.moves_conj_iff x (hV.moves 0 hm (fun p => p ∉ a.v.gP) fun _ h => h)
  choose e he hM using fun i => hG.frame i 0 ((a.G i).s + 1) (Nat.zero_add _)
  have hex : ∀ i, ∃ m, (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m := fun i =>
    ⟨_, (eq_coordHom_iff _ (a.G i).q.pr _ _ ((a.G i).FY 0 _ (Nat.zero_add _)).βγ ((a.G i).FY 0 _ (Nat.zero_add _)).γβ x _).2 rfl⟩
  have hloc := fun i m (hmat : (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m) hst =>
    red_iff (a.G i).q (hG.idem i).1 (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (a.g.b 0) x (a.G i).hs (a.G i).S _ (e i) (he i) (hM i) (r_le_Y 0) m hmat hst
  rw [_root_.GlobalTheory.FamTrace.Rows.mem_rJ_iff_finE_mem_St_and_block_mem W _ (mul_mem (mul_mem (inv_mem hb) hx) hb), (hG.lev _).1]
  constructor
  · rintro ⟨hst, hred⟩
    refine ⟨hoff.1 (moves_mono (fun _ _ => trivial) ((movesLocal D _ _ hΛ _).2 ((st_iff _ _ _ hβ hΛ _).1 hst))), ?_⟩
    exact fun i m hmat => (hloc i m hmat hst).1 (hred i)
  · rintro ⟨h1, h2⟩
    have hst : finE (Yc D 0) ((a.g.b 0)⁻¹ * x * a.g.b 0) ∈ St ((_root_.GlobalTheory.Fam.pk_z W).βY 0) := by
      refine (st_iff _ _ _ hβ hΛ _).2 fun v => ?_
      by_cases hv : v ∈ a.v.gP
      · obtain ⟨i, rfl⟩ := (ha.gpin.places v).1 hv
        obtain ⟨m, hmat⟩ := hex i
        have hR : ((a.G i).S.T (Fin D.R.t)).Regular := GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _
        exact moves_of_stab (a.G i).q (hG.idem i).1 (Yc D 0) _ _ hβ hΛ (a.g.b 0) x _ _
          ((e i).symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) 0 _ (Nat.zero_add _))) (hM i) m hmat
          ((hR.2.2 0 _ (Nat.zero_add _)).2.2 (h2 i m hmat))
      · exact moves_mono (fun p hp => by rw [hp]; exact hv) (hoff.2 h1)
    refine ⟨hst, fun i => ?_⟩
    obtain ⟨m, hmat⟩ := hex i
    exact (hloc i m hmat hst).2 (h2 i m hmat)
end Real
end GlobalTheory.FamTrace.Rows
theorem GlobalTheory.FamTrace.conj_mem_rows_iff_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ x ∈ GfC ((I.rec7 l Z).sp.Y 0), ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * x * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ _root_.GlobalTheory.FamTrace.InLevelGroupOfY a x) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha _ row col _ x hx
  exact _root_.GlobalTheory.FamTrace.Rows.main_alt_alt W hA.pk u a ha row col x hx
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjMemRowsIffStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_final_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ x ∈ GfC ((I.rec7 l Z).sp.Y 0), ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * x * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ _root_.GlobalTheory.FamTrace.InLevelGroupOfY a x) := by
  first | exact @_root_.GlobalTheory.FamTrace.conj_mem_rows_iff_alt | exact _root_.GlobalTheory.FamTrace.conj_mem_rows_iff_alt | (intros; apply _root_.GlobalTheory.FamTrace.conj_mem_rows_iff_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LamLowOfPublished
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FinitenessInputsRealDataThree
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FinitenessInputsRealData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
namespace GlobalTheory.LowRowAdel
theorem adelC_of_siegelWeil_of_doubling_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent →
    _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → AdelC R F := by
  intro hCusp hWS _hSWc hDbl hUnr hBZ hFD D G _ _ Pl0 T A Ks _ _ _ R F hL hStd
  have hHM : GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts.HarmonicModule :=
    GlobalTheory.HarmModule.harmonicModule_of GlobalTheory.FockDecay.harmonicDecay GlobalTheory.CartanInt.coshIntegral
  have hLoc : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock := GlobalTheory.SingleBlock.localIntegralSingleBlock
  have hPM : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D := GlobalTheory.PlaceTensor.placeModels D
  exact GlobalTheory.T.adelicLift_scalar_of_innerProductFormula R F (GlobalTheory.T.adelicLift_mem_cuspForm_multiplicitySpace hCusp R F) (GlobalTheory.T.finiteDatum_sourceLevelCharacter_law hLoc R F hPM)
    (GlobalTheory.T.twistedThetaLift_innerProductFormula_of_hypotheses hCusp hWS (_root_.ResidueKilled.sec_of_dm hDbl) R F hL)
    (GlobalTheory.T.fockVector_matrixCoefficient_formula hHM R F hPM) (deltaNorm_all D)
    (GlobalTheory.T.finiteZetaIntegral_eulerProduct_of_partialL R F (GlobalTheory.T.finiteZetaIntegral_thetaLift_eq_partialLValue hCusp hBZ hUnr R F)) (GlobalTheory.T.thetaLevelIndex_mul_schwartzNorm_formula hLoc R F hPM)
    (GlobalTheory.T.unitaryMassLowerBound_of_orthonormalLatticeFrames D hStd) (GlobalTheory.T.formalDegreeRealPlaceUpperBound_of_harishChandra hFD R F)
end GlobalTheory.LowRowAdel
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelC_of_parameter_choice_stdV : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → AdelC R F := by
  first | exact @_root_.GlobalTheory.LowRowAdel.adelC_of_siegelWeil_of_doubling_alt | exact _root_.GlobalTheory.LowRowAdel.adelC_of_siegelWeil_of_doubling_alt | (intros; apply _root_.GlobalTheory.LowRowAdel.adelC_of_siegelWeil_of_doubling_alt <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
namespace GlobalTheory.LowRow
theorem lamLow_closing_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  intro hCusp hWS hSWC hDM hUD hBZ hFD D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s b C CH
    hOk hSep hChar hEx hPrim hPhs hStd fw hBar hIo hPins hOne hTie hSizes hLow hNum hPar hStdV
  have hAd : AdelC R.toRealDat F.lv2 :=
    _root_.GlobalTheory.T.adelC_of_parameter_choice_stdV hCusp hWS hSWC hDM hUD hBZ hFD R.toRealDat F.lv2 hPar hStdV
  have hCore := (GlobalTheory.T.splitPart_baseLinks_of_primitiveRows R F s hOk hSep hChar hEx hPrim hPhs).1
  have hPT : PrimeToHost R.toRealDat A3.A.μ0 :=
    GlobalTheory.T.badPlacesPrimeToHost_baseTuple R.toRealDat F.lv2 (GlobalTheory.Core5.of_core hCore)
  exact GlobalTheory.T.liftEigenvalueLowerBound_of_weakCharacterisation GlobalTheory.T.conjugatesOfRationalThetaLift_from_characterisation T R F κ v₀ O s b C CH hOk hSep hChar hEx hPrim hPhs hStd fw hBar
    hIo hPins hOne hTie hSizes hLow hNum hAd hPT
end GlobalTheory.LowRow
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteness_inputs_real_data_three_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  first | exact @_root_.GlobalTheory.LowRow.lamLow_closing_alt | exact _root_.GlobalTheory.LowRow.lamLow_closing_alt | (intros; apply _root_.GlobalTheory.LowRow.lamLow_closing_alt <;> assumption)
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
namespace GlobalTheory.BigTop
theorem lamLow_of_hypotheses_alt_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent →
    _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.FormalDegreeCompactDual → _root_.GlobalTheory.BigTop.LambdaLowerBound₂ := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine (Formalism.MainNotions.DIV.closed_Csz_ge FamHyp 8).imp ?_
  intro eps Fm CH _ h8
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.thetaLift_weightSizes_eventually_along_family eps Fm
  refine ⟨x0, fun x hx hle i p hp C => ?_⟩
  have hS : ∀ j, Sizes (Fm.D x i) j (Fm.L x i).sc.b := hx0 x hx hle i
  refine _root_.GlobalTheory.T.finiteness_inputs_real_data_three_alt h1 h2 h3 h4 h5 h6 h7 (T := p.T) (R := p.R) (F := p.F) p.κ p.v₀ p.O 1 (Fm.L x i).sc.b C CH
    hp.ok hp.sep p.charW hp.exAt hp.prim p.phsOne p.stdChar p.fw p.bar hp.ioExt p.pins (fun j => (hp.oneMap j).1) p.phase hS
    ?_ ?_ ⟨_, ⟨Fm.params x hx i⟩⟩ p.stdV
  · intro j
    have := GlobalTheory.T.hookLogSum_sub_sizeTerm_le_lowerBound (Fm.D x i) (Fm.L x i) p.Del p.h0 Fm.Csz j h8 (hS j)
    exact this
  · intro j
    show _ - C * 0 ≤ _
    rw [mul_zero, sub_zero]
    exact le_rfl
end GlobalTheory.BigTop
end
end
end
