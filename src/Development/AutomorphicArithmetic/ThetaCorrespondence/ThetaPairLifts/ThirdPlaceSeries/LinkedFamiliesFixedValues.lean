module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLocPin
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCanonicalModuleSuccessor
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
structure TiedDataSAlt (ex : Extra D L hT Gi Gl K Y cX) where
  host : Host.HostTied D
  level : Host.LevelTied D
  cols : Forms.ColsTiedSym D
  full : Forms.ColsFullS cols
  extra : Forms.ColsExtraTiedS full ex
  provA : TH.ProvA
  theta : Theta.AllTied D ex.th provA
  twIn : TwIn D
  n : _root_.Formalism.L2.NTiedAllAlt D ex.nch twIn
  frameN : Host.SameFrameN host n.gal.fr.jE
  thetaChr : Host.ThetaChrTied D n.cf ex.nch n.tp ex.th
  chrVal : Host.ValLL0 D n.cf
  chrDt : Host.DtTied D n.cf
  chrN : Host.NCharTied D n.cf ex.nch n.tp
  chrGal : Host.NGalChrTied D n.cf ex.nch n.tp
  chrPsi : Host.PsiChoiceCompatible D n.cf ex.nch n.tp
  sameChr : JoinChr.SameChr theta.T thetaChr
  what₂ : Rows.RowsCompatible D host n.cf n.tp
  inK : Y.Lev → ℕ → Prop
  geo : Geo.GeoTiedP Y inK
  tw : Forms.SymmetricTwistedColumnsAtPrimes n.tp cols ex.tw
  emt : Rows.EMtTied D cols tw
  g : G.GroupCompatibilityAll D hT ex.cmp
  herm_eq : g.herm = full.1.to0
  forms_eq : g.forms = fun u => (cols.forms u).to0
def ExtraDataSelfDual (ex : Extra D L hT Gi Gl K Y cX) : Prop := Nonempty (_root_.Formalism.L2.TiedDataSAlt ex)
end
def SecondChernLinkedClass : FamClass := fun {_} Fm =>
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.ExtraDataSelfDual (Fm.ex x hx i)
def LinkedFamiliesFixedValues' : FamClass := Formalism.MainNotions.WithPage _root_.Formalism.L2.SecondChernLinkedClass
def LinkedFamiliesAligned' : FamClass := fun {_} Fm =>
  _root_.Formalism.L2.LinkedFamiliesFixedValues' Fm ∧ Formalism.MainNotions.DIV.Align.SmallFirstModulusBelowScale Fm ∧
    Formalism.MainNotions.TameDistinctF Fm
end Formalism.L2
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in
structure NAtData (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) :
    Type 1 where
  nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D cf nch tp
  all : _root_.GlobalTheory.HeightCounting.NAllCAlt D nch
  chr_eq : (⟨all.cf, all.tp⟩ : Σ c : CharFrame D, TupTied D c nch) = ⟨cf, tp⟩
  host : HostTied D
  frameN : ∀ x, all.gal.fr.jE x = host.fr.j x
  chrN : NCharTied D cf nch tp
  chrGal : NGalChrTied D cf nch tp
  Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host
  Pq_over : ∀ v, NG.OverPl (Pq v) v
  pq : ∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hadm : NX.AdmTw D i k Q ψ),
    (all.exp.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf D Pq Q ∧ (all.exp.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf D Pq (D.ntw.pD i)
  jE_eq : HEq nt.jE all.gal.fr.jE
  mt_eq : HEq (mtL nt.L nt.M) all.gal.mt
  Pq_eq : HEq nt.Pq Pq
  low : 2 ∈ nt.low ∧ AbsolutelyIrreducibleSpan.q0 D ∈ nt.low ∧ (NumberField.discr D.host.E).natAbs.primeFactors ⊆ nt.low ∧
    (Ideal.absNorm D.host.ccK).primeFactors ⊆ nt.low
  split : GlobalTheory.SplitCoef.OSplit D
  ratIn : RatIn nt.D nt.S
  ratIn_hL : ratIn.hL = nt.hL
  ratIn_eig : ratIn.eig = nt.eig
  ratIn_θ : ratIn.θ = nt.θ
  depth : RowDepth nt.D nt.rep
section Rows
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in
structure NormRealisationData {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D}
    (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) : Type 1 where
  kKs : Ks →+* ↥D.LL0
  hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x
  nexp : NExpRealS R cG (ratDatR R cG kKs hk)
  hecke : NExpRealH R cG (ratDatR R cG kKs hk) nexp
  grp : GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG)
  rowLoc : _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt a.all.gal.lp R.θ Y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (fun _ => R.e0) Y.eFT
  S_eq : HEq (ratL a.nt.L a.nt.S) (ratDatR R cG kKs hk)
  hL_eq : HEq a.nt.hL hecke.hL
  rep_eq : HEq a.nt.rep fun σ : D.what₂.FT => principalLevelFrame.rowRepR R.θ (Y.eFT σ)
end Rows
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
structure NormChoiceCore (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}
    (t : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) : Type 1 where
  a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL (w.D Z) (TC.cf w.I w.l Z) nch n.tp
  row : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData (D := (w.st Z).toD7) a t.r.z.R t.r.z.F t.r.z.cG t.r.Y
  sel : Set.range a.Pq = Set.range w.I.sel
abbrev NormChoiceExtension (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Type 2 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (_ : ThData (w.D Z)),
    _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n → Type 1
def normChoiceOfExtension (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (E : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) : NCondition := fun K B f T w Z Wt p0 t nch n xd =>
  Σ c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n, E K B f T w Z Wt p0 t nch n xd c
end GlobalTheory.Mem.Top.Bl
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.NRows
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy
structure RowsAAlt (D : D7) : Prop where
  tieLab : SumRepresentations.tieLab D
  hecke : HeckeSplitOne D
  tie0 : SumRepresentations.tie0 D
  a2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D
  an1 : T2.SumRepresentations.StrongMultiplicityOneCuspidalSums D.nd D.naut
  an2 : T2.SumRepresentations.IsobaricMultiplicityOne D.nd D.naut
  a5 : SumRepresentations.adm5 D
  temp : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D
  g4p : _root_.Formalism.MainNotions.SumRepresentations.CuspidalGaloisUnramified' D
  gsp : ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)
def SummandsSuffice (D : D7) : Prop :=
  _root_.Formalism.MainNotions.SumRepresentations.AdmAtAlt D → SumRepresentations.tieLab D → RowSize D → HeckeSplitOne D → (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) →
    ThetaOne D → _root_.Formalism.MainNotions.SumRepresentations.CuspidalGaloisUnramified' D → _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D
structure LinkedData (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) : Type 1 where
  P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D
  X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp
  agree : GlobalTheory.NJoin.Agree X P.M P.rep
  e0read : GoodIdempotentReadsAsGoodTypeProjector X
structure LinkedDataNamed {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (T : _root_.GlobalTheory.NRows.LinkedData hL D) : Prop where
  hypO : SumRepresentations.hypO D
  c1 : GlobalDatumCompatibility D
  bc : SphericalInertData.Conclusion1 D
  lam : LamUsed D
  isot : SumRepresentations.adm8 D
  ser : GlobalTheory.TypeLeaf.SerLoc D
  typeNZ : ∀ j t, GlobalTheory.DownLift.TypeNZ T.X.R j t
structure LinkedInputs (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) : Type 1 extends toRowSideFamily : _root_.GlobalTheory.NRows.LinkedData hL D where
  named : _root_.GlobalTheory.NRows.LinkedDataNamed toRowSideFamily
structure PointConditions' (D : D7) : Prop where
  a : _root_.GlobalTheory.NRows.RowsAAlt D
  b : RowsB D
  c : RowsC D
  typeNZ : ∀ i, TypeNZRec D.nd D.naut i
  rank : ∀ L : SizeData₂ D, TwistedPlaces.adm3 L
namespace Inputs
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (I : _root_.GlobalTheory.NRows.LinkedInputs hL D)
include I
theorem _root_.GlobalTheory.NRows.LinkedInputs.hypO : SumRepresentations.hypO D := I.named.hypO
theorem _root_.GlobalTheory.NRows.LinkedInputs.c1 : GlobalDatumCompatibility D := I.named.c1
theorem _root_.GlobalTheory.NRows.LinkedInputs.bc : SphericalInertData.Conclusion1 D := I.named.bc
theorem _root_.GlobalTheory.NRows.LinkedInputs.lam : LamUsed D := I.named.lam
theorem _root_.GlobalTheory.NRows.LinkedInputs.isot : SumRepresentations.adm8 D := I.named.isot
theorem _root_.GlobalTheory.NRows.LinkedInputs.ser : GlobalTheory.TypeLeaf.SerLoc D := I.named.ser
theorem _root_.GlobalTheory.NRows.LinkedInputs.typeNZ : ∀ j t, GlobalTheory.DownLift.TypeNZ I.X.R j t := I.named.typeNZ
theorem _root_.GlobalTheory.NRows.LinkedInputs.e0loc : GoodIdempotentFixesLocalisationForms D := goodIdempotentFixes_of_onlySeriesOfLabelActs I.ser
set_option linter.unusedSectionVars false in
theorem _root_.GlobalTheory.NRows.LinkedInputs.mtPar : MtParTie D.nd D.naut D.ntypes := D.mtpar_tie
theorem _root_.GlobalTheory.NRows.LinkedInputs.adm1 : SumRepresentations.adm1 D := base_change_automorphic_of D I.bc I.c1
theorem _root_.GlobalTheory.NRows.LinkedInputs.admAt (a : _root_.GlobalTheory.NRows.RowsAAlt D) (b : RowsB D) : _root_.Formalism.MainNotions.SumRepresentations.AdmAtAlt D :=
  ⟨⟨a.tie0, I.hypO, I.adm1, a.a2, b.a3, b.a4, a.a5⟩, a.temp⟩
theorem _root_.GlobalTheory.NRows.LinkedInputs.Conclusion1 (h : _root_.GlobalTheory.NRows.SummandsSuffice D) (a : _root_.GlobalTheory.NRows.RowsAAlt D) (b : RowsB D) : _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D :=
  h (I.admAt a b) a.tieLab b.rowSize a.hecke I.lam.loc b.thetaOne a.g4p
end Inputs
end GlobalTheory.NRows
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisSide
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisSide
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.RowModCanon
open MeasureTheory _root_.Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.PeterssonHilbertSpace
open scoped InnerProductSpace
end GlobalTheory.RowModCanon
namespace GlobalTheory.RowModCanon
open MeasureTheory Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev
  Formalism.IndefR.Links Formalism.IndefR.RecTie
set_option maxHeartbeats 1000000 in
theorem main_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (j : Fin D.R.m) (j' : ℕ)
    (hj : j.1 + 1 = j'), ∃ Y : RowMod D P.rep j', GlobalTheory.NJoin.IsCanon X j hj Y := by
  intro hH hC hL D P X hA j j' hj
  subst hj
  have hmod := X.given.core.models
  have hθ := hmod.inf
  have hν := hmod.νW j
  have hHaar : (X.R.νW j).IsHaarMeasure := hν.1.1
  have hFD := hν.2
  have hSig : (Wc D j).SigOK := D.sp.W_sig _
  have hSA : SchurAll D := fun V _ S θ M J χ μ 𝓕 => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
  have hHA : HCAll D := fun V _ S θ M J χ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1
  have hStd : GlobalTheory.Mem.R3.StdFrame hA.hF (X.PW j) := hA.stdW j
  have hcc := GlobalTheory.T.unitary_congruence_conj_contains_congruence D.host.E D.R.r
  obtain ⟨hlin, hherm, hpos⟩ := GlobalTheory.FinTypesRows.minf_sesq (M := X.R.MW j (sg0 D X.A)) (θ := X.R.θ) (X.R.νW j) (X.R.fdW j)
    (X.PW j) hSA hSig hθ hHaar hFD
  have hT := X.recR.tied.lift
  have hLev := GlobalTheory.FinTypesRows.levOK_levS (X.PW j) hStd (X.R.βW j) (X.R.datWp j (X.R.levL X.F false (sg0 D X.A)))
  set c : ℝ := (∏ ρ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D X.A) ρ) : ℚ) : ℝ)) * (RealDat.nP X.F false)⁻¹ with hcdef
  have hc : 0 < c := mul_pos (Finset.prod_pos fun ρ _ => by exact_mod_cast GlobalTheory.Mem.EasyInputs.dimOK D j (sg0 D X.A) ρ)
    (inv_pos.2 (RealDat.nP_pos false))
  have hSm := GlobalTheory.Mem.EasyInputs.smAll D (Wc D j) _ (X.R.MW j (sg0 D X.A))
  have hex : ∀ x ∈ principalLevelFrame.Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)), ∀ y ∈ principalLevelFrame.Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)),
      ∃ b, Mult.IsMultIP (X.R.MW j (sg0 D X.A)) (X.R.νW j) (X.R.fdW j) x y b := by
    intro x hx y hy
    obtain ⟨N, -, hx', hy'⟩ := GlobalTheory.FinTypesRows.exists_common (X.PW j) hx hy
    exact hSA _ hSig _ X.R.θ _ _ _ _ _ hθ hHaar hFD x hx' y hy'
  let φ : D.what₂.Mj (j.1 + 1) →ₗ[ℂ] Mult.MMap (X.R.MW j (sg0 D X.A)) :=
    (PiTensorProduct.lift : Mult.MMap (X.R.MW j (sg0 D X.A)) ≃ₗ[ℂ] _).symm.toLinearMap ∘ₗ
      (Submodule.subtype ((toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj).Wc j)) ∘ₗ (X.IL.jMj j).toLinearMap
  have hφ : ∀ y, PiTensorProduct.lift (φ y) = (X.IL.jMj j y).1 := by
    intro y
    exact LinearEquiv.apply_symm_apply _ _
  have hgood : ∀ y, φ y ∈ Mult.goodPart X.R.θ (X.R.MW j (sg0 D X.A)) (levS _ (X.R.βW j) (X.R.datWp j (X.R.levL X.F false (sg0 D X.A))))
      (levChi _ (X.R.βW j) (X.R.datWp j (X.R.levL X.F false (sg0 D X.A)))) (X.R.eWf j (sg0 D X.A)) := by
    intro y
    obtain ⟨a, ha, hay⟩ := (X.IL.jMj j y).2
    have : φ y = a := by
      show PiTensorProduct.lift.symm (X.IL.jMj j y).1 = a
      rw [← hay]
      exact LinearEquiv.symm_apply_apply _ _
    rw [this]
    exact ha
  have hmem : ∀ y, φ y ∈ principalLevelFrame.Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)) := fun y =>
    principalLevelFrame.mult_le_Minf hLev (Mult.goodPart_le _ _ _ _ _ (hgood y))
  refine ⟨{ A := Mult.MMap (X.R.MW j (sg0 D X.A))
            ρ := principalLevelFrame.actM (X.PW j) (X.R.MW j (sg0 D X.A))
            C := principalLevelFrame.Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A))
            B := fun x y => (c : ℂ) * Mult.ipM (X.R.MW j (sg0 D X.A)) (X.R.νW j) (X.R.fdW j) x y
            lin := fun x hx y hy z hz c' => by
              rw [hlin x hx y hy z hz c']
              ring
            herm := fun x hx y hy => by
              rw [map_mul, Complex.conj_ofReal, ← hherm x hx y hy]
            pos := fun x hx hx0 => by
              rw [Complex.re_ofReal_mul]
              exact mul_pos hc (hpos x hx hx0)
            stab := fun h x hx => GlobalTheory.FinTypesRows.minf_stable (X.PW j) hcc h hx
            inv := fun h x hx y hy => by
              rw [GlobalTheory.T.schur_pairing_invariant_under_standard_group D (Wc D j) _ X.R.θ (X.R.MW j (sg0 D X.A)) D.R.r (X.PW j) (X.R.νW j) (X.R.fdW j) hSA hSig hθ
                hHaar hFD h x hx y hy]
            smooth := fun x hx => GlobalTheory.FinTypesRows.minf_smooth (X.PW j) hx
            adm := fun N hN => GlobalTheory.FinTypesRows.minf_adm (X.PW j) hHA hSig hθ (GlobalTheory.FinTypesRows.levN_open (X.PW j) hStd) N hN
            φ := φ
            φ_mem := hmem
            φ_inner := fun x y => by
              beta_reduce
              rw [hT.mj j x y]
              change (∏ τ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D X.A) τ) : ℚ) : ℂ)) *
                Mult.ipM (X.R.MW j (sg0 D X.A)) (ENNReal.ofReal (RealDat.nP X.F false)⁻¹ • X.R.νW j) (X.R.fdW j) (φ x) (φ y) = _
              rw [ipM_smul_measure _ hSm _ _ (inv_nonneg.2 (RealDat.nP_pos false).le) _ _ (hex _ (hmem x) _ (hmem y)), hcdef]
              push_cast
              ring
            isot := fun σ y => by
              rw [hT.isot j σ y, X.recR.prtWE j σ, principalLevelFrame.isotIn_iso _ _ (hA.rep_iso σ)]
              constructor
              · rintro ⟨a, ha, hay⟩
                have e : φ y = a := by
                  show PiTensorProduct.lift.symm (X.IL.jMj j y).1 = a
                  rw [← hay]
                  exact LinearEquiv.symm_apply_apply _ _
                rw [e]
                exact (Submodule.mem_inf.1 ha).2
              · intro h
                exact ⟨φ y, Submodule.mem_inf.2 ⟨hgood y, h⟩, hφ y⟩ }, LinearMap.id, c, Function.injective_id, hc, Submodule.map_id _, fun h x => rfl, fun x _ y _ => rfl,
            fun y => hφ y⟩
end GlobalTheory.RowModCanon
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisSideStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_canonical_module_at_successor : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (j : Fin D.R.m) (j' : ℕ) (hj : j.1 + 1 = j'), ∃ Y : RowMod D P.rep j', GlobalTheory.NJoin.IsCanon X j hj Y := by
  first | exact @_root_.GlobalTheory.RowModCanon.main_alt_alt | exact _root_.GlobalTheory.RowModCanon.main_alt_alt | (intros; apply _root_.GlobalTheory.RowModCanon.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTameMuPlGw
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTameMuPlGw
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.PendOf.isTame_reading_mu_at_split_plGw : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu := by
  intro hL D P S hS i k v hw
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hjj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hc := hS.mu i _ hw j hjj
  have hc' : IsComp (P.tp.tup (D.nd.mu i) j) (D.naut.plGw k v) ((P.tp.tup (D.nd.mu i) j).loc (D.naut.plGw k v)) :=
    ⟨GlobalTheory.HeckeComp.smooth_loc _ _, fun _ => rfl⟩
  rw [GlobalTheory.HeckeComp.eq_of_isComp hc' hc]
  exact GlobalTheory.MuTameQS.isTame_loc (GlobalTheory.MuTameQS.tameAt_mul ((P.cf.isMu0 j).tame _) (P.tp.xi_tame _ _))
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTameMuPlGwStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_weil_mu_tame_of_is_true
    (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : GlobalTheory.SplitRead.Reading P.T) :
    _root_.GlobalTheory.NPin.IsFaithfulReading P S →
      ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)),
        GlobalTheory.SplitWeil.IsTame (S i (D.naut.plGw k v) hw).mu :=
  _root_.GlobalTheory.PendOf.isTame_reading_mu_at_split_plGw hL D P S
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodOffSQ
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodOffSQ
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.OffSQ
theorem good_off_SQ_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → w ∉ D.nd.S i ∧ w ∉ D.nd.Q i := by
  intro hL D P X hA _ _ i w hG
  have hlev := X.recR.base.lev
  have hmu : D.nd.mu i = D.what₂.muAt (D.nd.w i) := by
    rcases D.what₂.muAt_or (D.nd.w i) with h | h
    · exact absurd h (D.nd.w_tw i)
    · rw [h, D.nd.mu_w i]
  have hxi := X.recR.tupXi (D.nd.mu i) (Or.inr ⟨D.nd.w i, hmu⟩)
  have hunr : (X.R.xiH (X.tupT (D.nd.mu i))).UnrAt w := by
    by_contra hn
    rcases (hlev.Q_ram _ w).1 hn with h | ⟨PP, hPP, hc⟩
    · exact (hG w (Or.inr h)).1 rfl
    · exact (hG PP (Or.inr hPP)).2 hc
  rw [hxi, D.nd.mu_w i, X.Tp.xi_tw, D.nd.w_l i] at hunr
  have hψ := X.Tp.psi_is (D.nd.w i) (D.nd.w_tw i)
  rw [D.nd.w_l i] at hψ
  set δ := X.R.C.delAt (D.nd.l i) with hδdef
  set ψ := X.Tp.psi (D.nd.w i) with hψdef
  set p := if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde with hpdef
  have hd : IsDelta (H := D.host) p δ := by
    rw [hδdef, hpdef, CharFrame.delAt]
    split_ifs
    exacts [X.R.C.isDel', X.R.C.isDel]
  have hmul : ∀ x, (δ * ψ).loc w x = δ.loc w x * ψ.loc w x := fun _ => rfl
  have hnp : ¬ OverP D.host p w := by
    intro hw
    obtain ⟨a, ha⟩ := hψ.ord
    have h15 : 15 ∣ D.nd.l i ^ a := by
      refine (hd.ine w hw (D.nd.l i ^ a)).1 fun x hx => ?_
      have h1 : δ.loc w x * ψ.loc w x = 1 := (hmul x).symm.trans (hunr x hx)
      have h2 : ψ.loc w x ^ (D.nd.l i ^ a) = 1 := by
        have := congrArg (fun ξ : HChar D.host.E => ξ.loc w x) ha
        simpa [HChar.loc] using this
      have h3 : (δ.loc w x * ψ.loc w x) ^ (D.nd.l i ^ a) = 1 := by rw [h1, one_pow]
      rwa [mul_pow, h2, mul_one] at h3
    have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
    have h3 : 3 = D.nd.l i := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1
      (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    have h5 : 5 = D.nd.l i := (Nat.prime_dvd_prime_iff_eq (by norm_num) hl).1
      ((show (5 : ℕ).Prime by norm_num).dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    omega
  have hng : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k) := by
    intro k hw
    have hs : GlobalTheory.Mem.Chr.SplitsC D.host.E (D.host.g k) := D.nd.g_split k
    rcases (GlobalTheory.BigOn.Inhab.overP_iff (D.host.g_prime k) hs (X.R.C.P.pb_over k) w).1 hw with h | ⟨w', h, hc⟩
    · exact (hG w (Or.inl ((hlev.Pg w).2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).1 rfl
    · exact (hG w' (Or.inl ((hlev.Pg w').2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).2 hc
  refine ⟨fun hS => ?_, fun hQ => ?_⟩
  · rcases ((D.nd.S_def i w).1 hS).1 with h | h | h
    · exact hng 0 h
    · exact hng 1 h
    · exact hnp h
  · rw [P.Q_eq i] at hQ
    refine (hψ.ram w).1 ?_ hQ
    intro x hx
    have h1 : δ.loc w x * ψ.loc w x = 1 := (hmul x).symm.trans (hunr x hx)
    rw [hd.unr w hnp x hx, one_mul] at h1
    exact h1
end GlobalTheory.OffSQ
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodOffSQStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_place_not_mem_S_and_Q_of_tieLab :
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
      (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
      (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep),
      _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D →
      Formalism.MainNotions.SumRepresentations.tieLab D →
      ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)),
        GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → w ∉ D.nd.S i ∧ w ∉ D.nd.Q i :=
  _root_.GlobalTheory.OffSQ.good_off_SQ_alt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MapMemISupIsLinAt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum GlobalTheory.ThetaLoc
variable {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
  (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
  {TauV Fm C : Type} [AddCommGroup TauV] [Module ℂ TauV]
  [AddCommGroup Fm] [Module ℂ Fm] [AddCommGroup C] [Module ℂ C]
  (fV : Fm →ₗ[ℂ] (Formalism.L2.Theta.GA D V → TauV)) (yv : C →ₗ[ℂ] (Formalism.L2.Theta.GA D W → ℂ))
  (νV : Measure (Formalism.L2.Theta.GA D V)) (𝓕V : Set (Formalism.L2.Theta.GA D V)) (νW : Measure (Formalism.L2.Theta.GA D W)) (𝓕W : Set (Formalism.L2.Theta.GA D W))
variable (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) {G : Type} [Monoid G] (ω : G →* Module.End ℂ (WO V W → ℂ))
end GlobalTheory.ThetaTri
end
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum GlobalTheory.ThetaLoc
variable {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
  (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
  {TauV Fm C : Type} [AddCommGroup TauV] [Module ℂ TauV]
  [AddCommGroup Fm] [Module ℂ Fm] [AddCommGroup C] [Module ℂ C]
  (fV : Fm →ₗ[ℂ] (Formalism.L2.Theta.GA D V → TauV)) (yv : C →ₗ[ℂ] (Formalism.L2.Theta.GA D W → ℂ))
  (νV : Measure (Formalism.L2.Theta.GA D V)) (𝓕V : Set (Formalism.L2.Theta.GA D V)) (νW : Measure (Formalism.L2.Theta.GA D W))
  (𝓕W : Set (Formalism.L2.Theta.GA D W)) (c : ℂ)
variable (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) {G : Type} [Monoid G]
  (ω : G →* Module.End ℂ (WO V W → ℂ))
end GlobalTheory.ThetaTri
end
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ThetaLoc
open scoped TensorProduct
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}
def eWloc_alt (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) : (X.R.cV j).W ≃ₗ[ℂ] (P.M.loc i).wt.W := by
  have key : ∀ (k : ℕ) (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m),
      (X.R.cV j).W ≃ₗ[ℂ] (P.M (D.nd.mu i) k p1 p2).wt.W := by
    rintro k rfl p1 p2
    exact A.eW _ hμ j
  exact key _ hj _ _
def formToVectorMap (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) →ₗ[ℂ] (Formalism.L2.Theta.GA D (Vc D j) → (X.R.cV j).W) :=
  (X.R.cV j).ext ∘ₗ
    { toFun := fun F k => (_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm
        ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k))
      map_add' := fun F F' => by funext k; simp
      map_smul' := fun c F => by funext k; simp }
def canonicalEmbedding' {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) :
    Y.A →ₗ[ℂ] Formalism.IndefR.Mult.MMap (X.R.MW j (sg0 D X.A)) :=
  Classical.choose hc
def canonicalConstant {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) : ℝ :=
  Classical.choose (Classical.choose_spec hc)
def thetaEvaluationMap {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) :
    ↥Y.C →ₗ[ℂ] (Formalism.L2.Theta.GA D (Wc D j) → ℂ) :=
  LinearMap.applyₗ (PiTensorProduct.map (fun τ => (lowT (X.R.MW j (sg0 D X.A)) τ).subtype)
      (kUnit (X.R.MW j (sg0 D X.A)))) ∘ₗ
    (PiTensorProduct.lift : Formalism.IndefR.Mult.MMap (X.R.MW j (sg0 D X.A)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc ∘ₗ Y.C.subtype
def standardWeilRepresentation (A : GlobalTheory.NJoin.Agree X P.M P.rep) (j : Fin D.R.m) (t : X.T) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ (WO (Vc D j) (Wc D j) → ℂ) :=
  (X.R.ωP j t).comp ((A.PV j).ψ.prodMap (X.PW j).ψ)
def OmegaSubmoduleAtLocal (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    Submodule ℂ ((X.R.cV j).W →ₗ[ℂ] (WO (Vc D j) (Wc D j) → ℂ)) :=
  OmSub (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) X.R.ψ
    (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i)))
def canonicalPairingValue (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i))
    (φ : (X.R.cV j).W →ₗ[ℂ] (WO (Vc D j) (Wc D j) → ℂ))
    (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) (y : ↥Y.C) : ℂ :=
  lamV (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) (_root_.GlobalTheory.ThetaTri.canonicalConstant hc : ℂ) φ F y
def standardSchwartzFunctionMap (j : Fin D.R.m) (t : X.T) : (X.R.cV j).W →ₗ[ℂ] (WO (Vc D j) (Wc D j) → ℂ) :=
  pureTensorO X.R.ψ X.R.θ (Vc D j) (Wc D j) (fun _ => 1) (cart (X.R.MW j (sg0 D X.A))) (X.R.BV j)
    (onb (X.R.MW j (sg0 D X.A))) (X.R.vP j t) ∘ₗ X.R.ioP j (kUnit (X.R.MW j (sg0 D X.A)))
end GlobalTheory.ThetaTri
end
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum GlobalTheory.ThetaLoc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n r : ℕ}
theorem map_mem_iSup_range_isLinAt {Θ Ω : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup Ω] [Module ℂ Ω]
    (ω₁ : GAf E n × GAf E r →* Module.End ℂ Θ) (ω₂ : GAf E n × GAf E r →* Module.End ℂ Ω)
    (P : Θ → Prop) (Q : Ω → Prop) (T : Θ →ₗ[ℂ] Ω) (hT : ∀ p f, P f → T (ω₁ p f) = ω₂ p (T f))
    (hTQ : ∀ f, P f → Q (T f)) (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ) {f : Θ}
    (hf : f ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ)
      (_ : IsLinAt ω₁ s μ η ι ∧ ∀ Φ, P (ι Φ)), LinearMap.range ι) :
    T f ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Ω)
      (_ : IsLinAt ω₂ s μ η ι ∧ ∀ Φ, Q (ι Φ)), LinearMap.range ι := by
  have hle : (⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ)
      (_ : IsLinAt ω₁ s μ η ι ∧ ∀ Φ, P (ι Φ)), LinearMap.range ι).map T ≤
      ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Ω)
      (_ : IsLinAt ω₂ s μ η ι ∧ ∀ Φ, Q (ι Φ)), LinearMap.range ι := by
    rw [Submodule.map_iSup]
    refine iSup_le fun ι => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hι => ?_
    rw [← LinearMap.range_comp]
    exact le_iSup₂_of_le (T ∘ₗ ι) ⟨isLinAt_comp ω₁ ω₂ P T hT s μ η ι hι.2 hι.1, fun Φ => hTQ _ (hι.2 Φ)⟩ le_rfl
  exact hle (Submodule.mem_map_of_mem hf)
theorem mem_iSup_range_isLinAt_valAct1 {Θ B : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup B] [Module ℂ B]
    [FiniteDimensional ℂ B] (ω : GAf E n × GAf E r →* Module.End ℂ Θ) (P : Θ → Prop) (Q : (B →ₗ[ℂ] Θ) → Prop)
    (hQ : ∀ β f, P f → Q (single1 β f))
    (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ) (φ : B →ₗ[ℂ] Θ)
    (hφ : ∀ b, φ b ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ)
      (_ : IsLinAt ω s μ η ι ∧ ∀ Φ, P (ι Φ)), LinearMap.range ι) :
    φ ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] (B →ₗ[ℂ] Θ))
      (_ : IsLinAt (valAct1 ω) s μ η ι ∧ ∀ Φ, Q (ι Φ)), LinearMap.range ι := by
  let bB := Module.finBasis ℂ B
  rw [eq_sum_single1 bB φ]
  refine Submodule.sum_mem _ fun l _ => ?_
  exact _root_.GlobalTheory.ThetaTri.map_mem_iSup_range_isLinAt ω (valAct1 ω) P Q (single1 (bB.coord l))
    (fun p f _ => single1_valAct1 ω _ p f) (fun f hf => hQ _ f hf) s μ η (hφ _)
variable {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
  (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
  {TauV Fm C : Type} [AddCommGroup TauV] [Module ℂ TauV]
  [AddCommGroup Fm] [Module ℂ Fm] [AddCommGroup C] [Module ℂ C]
  (fV : Fm →ₗ[ℂ] (Formalism.L2.Theta.GA D V → TauV)) (yv : C →ₗ[ℂ] (Formalism.L2.Theta.GA D W → ℂ))
  (νV : Measure (Formalism.L2.Theta.GA D V)) (𝓕V : Set (Formalism.L2.Theta.GA D V)) (νW : Measure (Formalism.L2.Theta.GA D W))
  (𝓕W : Set (Formalism.L2.Theta.GA D W)) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ)
  (ω : GAf E n × GAf E r →* Module.End ℂ (WO V W → ℂ))
end GlobalTheory.ThetaTri
end
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ThetaLoc
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}
def omegaMapAtLocal (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ ↥(_root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ) :=
  omSub (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) X.R.ψ (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i)))
def canonicalPairingMap (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    ↥(_root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ) →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) →ₗ[ℂ] ↥Y.C →ₗ⋆[ℂ] ℂ :=
  lam (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) (_root_.GlobalTheory.ThetaTri.canonicalConstant hc : ℂ) X.R.ψ (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i)))
end GlobalTheory.ThetaTri
end
end
end
