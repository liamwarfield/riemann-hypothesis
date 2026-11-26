module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FourMulRootLt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefDualPair

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open Formalism.IndefR.FWT GlobalTheory.RealGeo

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}

abbrev setCd (c : CDHaar) : Late B C := { b with G := { b.G with cd := c } }

theorem lawsM_tr {T : Core a.D} (h : LawsM T) : LawsM (core b T) := by
  have key : ∀ c : CDHaar, c = a.G.cd → LawsM (core (setCd b c) T) := by
    rintro _ rfl
    constructor
    case pins => exact (by with_unfolding_all exact (h.pins :))
    case half => exact (by with_unfolding_all exact (h.half :))
    case evalWD => exact (by with_unfolding_all exact (h.evalWD :))
    case unf => exact (by with_unfolding_all exact (h.unf :))
    case unTest => exact (by with_unfolding_all exact (h.unTest :))
    case chiTriv => exact (by with_unfolding_all exact (h.chiTriv :))
    case dictU => exact (by with_unfolding_all exact (h.dictU :))
    case spaceW => exact (by with_unfolding_all exact (h.spaceW :))
    case levelK => exact (by with_unfolding_all exact (h.levelK :))
    case xiAbs => exact (by with_unfolding_all exact (h.xiAbs :))
    case muUnit => exact (by with_unfolding_all exact (h.muUnit :))
    case muCont => exact (by with_unfolding_all exact (h.muCont :))
    case finVol => exact (by with_unfolding_all exact (h.finVol :))
    case cuspFD => exact (by with_unfolding_all exact (h.cuspFD :))
    case supDef => exact (by with_unfolding_all exact (h.supDef :))
    case cuspidalL2Subspace => exact (by with_unfolding_all exact (h.cuspidalL2Subspace :))
    case l2Def => exact (by with_unfolding_all exact (h.l2Def :))
    case unitIndep => exact (by with_unfolding_all exact (h.unitIndep :))
    case ptNe => exact (by with_unfolding_all exact (h.ptNe :))
  exact (by with_unfolding_all exact ((key b.G.cd (cd_eq _ _)) :))

theorem lawsJ_tr {T : CoreJ a.D} (h : LawsJ T) : LawsJ (coreJ b T) := by
  constructor
  case toLawsM => exact (by with_unfolding_all exact ((lawsM_tr b h.toLawsM) :))
  case cUnit => exact (by with_unfolding_all exact (h.cUnit :))
  case muVal => exact (by with_unfolding_all exact (h.muVal :))
  case muConj => exact (by with_unfolding_all exact (h.muConj :))
  case intAll => exact (by with_unfolding_all exact (h.intAll :))
  case modelW => exact (by with_unfolding_all exact (h.modelW :))
  case familyUniformisationBasePointOrthogonal => exact (by with_unfolding_all exact (h.familyUniformisationBasePointOrthogonal :))
  case kfHalf => exact (by with_unfolding_all exact (h.kfHalf :))
  case adPin => exact (by with_unfolding_all exact (h.adPin :))

variable {A : FamIn a.D.what₂.LL G Pl0 T0 a.D.R.m}

section Theta

variable {T : Core a.D} [iK : Algebra T.Q.c.F a.D.what₂.LL] {R : RealDat a.D A T.Q.c.F} {i : Fin a.D.R.m} {Tp : Type} {tup : Tp → T0}

def omDat (O : OMDat T R i Tp tup) :
    @OMDat b.D G _ _ Pl0 T0 (famM b A) (core b T) ((@alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) iK)) ((@real B C a b G ‹Group G› ‹Fintype G› Pl0 T0 (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (inferInstance) iK A R)) ((i)) Tp tup :=
  @OMDat.mk b.D G _ _ Pl0 T0 (famM b A) (core b T) ((by with_unfolding_all exact ((alg b iK) :))) ((by with_unfolding_all exact ((real b R) :))) ((by with_unfolding_all exact (i :))) Tp tup
    (c' := (by with_unfolding_all exact (O.c' :)))
    (hle := (by with_unfolding_all exact (O.hle :)))
    (jL := (by with_unfolding_all exact (O.jL :)))
    (hV := (by with_unfolding_all exact (O.hV :)))
    (c0' := (by with_unfolding_all exact (O.c0' :)))
    (lev := (by with_unfolding_all exact (O.lev :)))
    (dδ := (by with_unfolding_all exact (O.dδ :)))
    (Cl' := (by with_unfolding_all exact (O.Cl' :)))
    (fCl := (by with_unfolding_all exact (O.fCl :)))
    (bad := (by with_unfolding_all exact (O.bad :)))
    (Lh := (by with_unfolding_all exact (O.Lh :)))
    (La := (by with_unfolding_all exact (O.La :)))
    (Nc := (by with_unfolding_all exact (O.Nc :)))
    (gam := (by with_unfolding_all exact (O.gam :)))
    (vol := (by with_unfolding_all exact (O.vol :)))
    (ep := (by with_unfolding_all exact (O.ep :)))
    (B := (by with_unfolding_all exact (O.B :)))
    (epF := (by with_unfolding_all exact (O.epF :)))
    (io := (by with_unfolding_all exact (O.io :)))
    (hw := (by with_unfolding_all exact (O.hw :)))
    (φ := (by with_unfolding_all exact (O.φ :)))
    (w := (by with_unfolding_all exact (O.w :)))
    (U₂ := (by with_unfolding_all exact (O.U₂ :)))
    (dict₂ := (by with_unfolding_all exact (O.dict₂ :)))
    (xi := (by with_unfolding_all exact (O.xi :)))
    (thAd := (by with_unfolding_all exact (O.thAd :)))
    (Plc := (by with_unfolding_all exact (O.Plc :)))

theorem omPins_tr {O : OMDat T R i Tp tup} {κ v₀ ι x₀} (h : O.Pins κ v₀ ι x₀) :
    @OMDat.Pins b.D G _ _ Pl0 T0 (famM b A) (core b T) ((@alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) iK)) ((@real B C a b G ‹Group G› ‹Fintype G› Pl0 T0 (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (inferInstance) iK A R)) ((i)) Tp tup (omDat b O) ((@wt B C a b (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Fin.val (@Late.D B C a).R.m i) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) κ)) ((v₀))
      ((ι)) ((x₀)) := by
  apply (config := { synthAssignedInstances := false }) OMDat.Pins.mk
  case lift =>
    apply (config := { synthAssignedInstances := false }) ThPinsR.mk
    case field => exact (by with_unfolding_all exact (h.lift.field :))
    case std => exact (by with_unfolding_all exact (h.lift.std :))
    case v0 => exact (by with_unfolding_all exact (h.lift.v0 :))
    case lev => exact (by with_unfolding_all exact (h.lift.lev :))
    case c0 =>
      obtain ⟨x, y, z, h1, h2⟩ := h.lift.c0
      refine ⟨(by with_unfolding_all exact (x :)), (by with_unfolding_all exact (y :)), (by with_unfolding_all exact (z :)), ?_, (by with_unfolding_all exact (h2 :))⟩
      exact (by with_unfolding_all exact ((famTie_imp b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1) :))
  case tuple =>
    intro t
    apply (config := { synthAssignedInstances := false }) ThPinsT.mk
    case reps => exact (by with_unfolding_all exact ((h.tuple t).reps :))
    case B => exact (by with_unfolding_all exact ((h.tuple t).B :))
    case xi => exact (by with_unfolding_all exact ((h.tuple t).xi :))
    case phi => exact (by with_unfolding_all exact ((h.tuple t).phi :))
    case half => exact (by with_unfolding_all exact ((h.tuple t).half :))
  case act => exact (by with_unfolding_all exact (h.act :))
  case bad => exact (by with_unfolding_all exact (h.bad :))
  case reps => exact (by with_unfolding_all exact (h.reps :))
  case ep => exact (by with_unfolding_all exact (h.ep :))
  case io => exact (by with_unfolding_all exact (h.io :))
  case w => exact (by with_unfolding_all exact (h.w :))
  case cov => exact (by with_unfolding_all exact (h.cov :))
  case cxi => exact (by with_unfolding_all exact (h.cxi :))
  case model₂ => exact (by with_unfolding_all exact (h.model₂ :))

end Theta

variable {T : CoreJ a.D} [iK : Algebra T.Q.c.F a.D.what₂.LL] {R : RealDat a.D A T.Q.c.F}

def fwTie {κ v₀} (x : FWTie T R κ v₀) :
    @FWTie b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) (by with_unfolding_all exact (alg b iK :)) (by with_unfolding_all exact (real b R :)) (fun i => by with_unfolding_all exact (wt b (κ (by with_unfolding_all exact (i :))) :)) (by with_unfolding_all exact (v₀ :)) :=
  @FWTie.mk b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) ((by with_unfolding_all exact ((alg b iK) :))) ((by with_unfolding_all exact ((real b R) :))) (fun i => (by with_unfolding_all exact ((wt b (κ ((i)))) : _))) ((by with_unfolding_all exact (v₀ :)))
    (alg_eq := (by with_unfolding_all exact (x.alg_eq :)))
    (e := (by with_unfolding_all exact (x.e :)))
    (ks := (by with_unfolding_all exact (x.ks :)))
    (kap := (by with_unfolding_all exact (x.kap :)))
    (pt := (by with_unfolding_all exact (x.pt :)))
    (nrm_eq := (by with_unfolding_all exact (x.nrm_eq :)))
    (laws := lawsJ_tr b x.laws)
    (chiR := (by with_unfolding_all exact (x.chiR :)))
    (hv₀ := (by with_unfolding_all exact (x.hv₀ :)))
    (x0 := (by with_unfolding_all exact (x.x0 :)))
    (ev0 := (by with_unfolding_all exact (x.ev0 :)))
    (ev := (by with_unfolding_all exact (x.ev :)))

def geoHalf {ph : Fin a.D.R.m → ℂ} (x : GeoHalf T R ph) :
    @GeoHalf b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) ((@alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) iK)) ((@real B C a b G ‹Group G› ‹Fintype G› Pl0 T0 (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (inferInstance) iK A R)) ((ph)) :=
  @GeoHalf.mk b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) ((by with_unfolding_all exact ((alg b iK) :))) ((by with_unfolding_all exact ((real b R) :))) ((by with_unfolding_all exact (ph :)))
    (κ := fun i => (by with_unfolding_all exact ((wt b (x.κ ((i)))) : _)))
    (v₀ := (by with_unfolding_all exact (x.v₀ :)))
    (fw := (by with_unfolding_all exact ((fwTie b x.fw) :)))
    (bar := (by with_unfolding_all exact (x.bar :)))
    (O := fun i => (by with_unfolding_all exact ((omDat b (x.O ((i)))) : _)))
    (pins := fun i => (by with_unfolding_all exact ((And.intro (x.pins ((i))).1 (omPins_tr b (x.pins ((i))).2)) : _)))
    (rhoGeo := (by with_unfolding_all exact (x.rhoGeo :)))
    (equivAll := (by with_unfolding_all exact (x.equivAll :)))
    (cTie := (by with_unfolding_all exact (x.cTie :)))
    (phase := (by with_unfolding_all exact (x.phase :)))

set_option maxHeartbeats 16000000 in
theorem inGeo_tr {ph : Fin a.D.R.m → ℂ} {x : GeoHalf T R ph} (h : InGeo x) :
    @InGeo b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) ((@alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) iK)) ((@real B C a b G ‹Group G› ‹Fintype G› Pl0 T0 (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (inferInstance) iK A R)) ((ph)) (geoHalf b x) := by
  apply (config := { synthAssignedInstances := false }) InGeo.mk
  case jEvExists => exact (by with_unfolding_all exact (h.jEvExists :))
  case jEvBar => exact (by with_unfolding_all exact (h.jEvBar :))
  case evInj => exact (by with_unfolding_all exact (h.evInj :))
  case jUnif => exact (by with_unfolding_all exact (h.jUnif :))
  case geoAct =>
    intro i
    exact (by with_unfolding_all exact (h.geoAct i :))
  case latFull => exact (by with_unfolding_all exact (h.latFull :))
  case dimMatch =>
    intro i
    exact (by with_unfolding_all exact (h.dimMatch i :))

end GlobalTheory.Mem.R3.Tr

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStagesClauses
noncomputable section

namespace GlobalTheory.Mem.Top.V4.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem ev_imp {p q : Ctx → Prop} (hp : Ev p) (h : ∀ K, p K → q K) : Ev q := by
  obtain ⟨ε0, h0, H⟩ := hp
  refine ⟨ε0, h0, fun eps C8 a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, H⟩ := H eps C8 a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, H⟩ := H C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, H⟩ := H cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, H⟩ := H ch hch
  exact ⟨x0, fun K d1 d2 d3 d4 d5 => h K (H K d1 d2 d3 d4 d5)⟩

theorem mem_iff {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {Wt : Set X.B.places.Pl} {xi : X.C.Tup → HChar X.B.host.E}
    (h : MuIsW X f T Wt xi) (w : X.B.places.Pl) : w ∈ Wt ↔ X.W.muAt w ≠ X.C.mu0 := by
  refine ⟨fun hw he => ?_, fun hw => by_contra fun hn => hw (h.off w hn)⟩
  have h1 := h.tw w
  rw [← h.on w hw, he, h.mu0] at h1
  exact (TwFin.tw_fin X.B f T).2.1 w h1.symm

variable (hH : DC.HostExQ) (hLP : LevelPrime) (hSP : SmallPrimeOne) (h2b : StandardLattice.SiegelMassRatioCM)






end GlobalTheory.Mem.Top.V4.Model

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Limits (pullback)
open GlobalTheory.VB Formalism.BasicNotions
open GlobalTheory.LieVB (omega omegaBase)
open GlobalTheory.Vert (SmallPic smallPicEquiv)
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol IsProjSurface degCh2)
open scoped CategoryTheory.Obj

namespace GlobalTheory.ShFam.Pad

structure ProjCode (R : Type) [CommRing R] : Type where

  n : ℕ

  I : (PSpace R n).IdealSheafData

namespace ProjCode

variable {R : Type} [CommRing R] (C : ProjCode R)

def X : Scheme.{0} := C.I.subscheme

def str : C.X ⟶ Sp R := C.I.subschemeι ≫ PSpace.str R C.n

instance algebra : Algebra R Γ(C.X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ C.str.appTop).hom.toAlgebra

end ProjCode

abbrev toSpZ (Y : Scheme.{0}) : Y ⟶ Sp ℤ := specZIsTerminal.from Y

theorem isProjOver_toSpZ {R : Type} [CommRing R] [Module.Finite ℤ R] {Y : Scheme.{0}}
    {f : Y ⟶ Sp R} (h : IsProjOver f) : IsProjOver (toSpZ Y) := by
  obtain ⟨N, i, hi, -⟩ := h
  have hb : IsFinite (spMap (Int.castRingHom R)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := R)).2 inferInstance
  have P := GlobalTheory.ProjSpace.isPullback_baseChange N (Int.castRingHom R)
  have hf : IsFinite (GlobalTheory.ProjSpace.baseChange N (Int.castRingHom R)) :=
    MorphismProperty.of_isPullback P.flip hb
  have := isProjOver_comp_of_finite ℤ (PSpace ℤ N) Y
    (i ≫ GlobalTheory.ProjSpace.baseChange N (Int.castRingHom R)) (PSpace.str ℤ N) inferInstance
    ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  exact specZIsTerminal.hom_ext _ (toSpZ Y) ▸ this

theorem isArithVar_toSpZ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) : IsArithVar (toSpZ Y) D :=
  have := h.finite
  ⟨inferInstance, inferInstance, h.isIntegral, isProjOver_toSpZ h.isProjOver,
    specZIsTerminal.hom_ext (p ≫ spMap (Int.castRingHom k))
      (toSpZ Y ≫ spMap (Int.castRingHom ℤ)) ▸ h.flat, h.dim_eq⟩

structure PPCode (S : Scheme.{0}) : Type where

  C : ProjCode ℤ

  π : C.X ⟶ S

  [grp : GrpObj (Over.mk π)]

  isAb : IsAbelianScheme (Over.mk π)

  g : ℕ

  pos : 1 ≤ g

  smoothDim : SmoothOfRelativeDimension g π

  c : SmallPic (Over.mk π ⊗ Over.mk π).left

  isPol : IsPrincipalPol (Over.mk π) (smallPicEquiv _ c)

namespace PPCode

variable {S S' : Scheme.{0}}

def P (Q : PPCode S) : PPAS S :=
  letI := Q.grp
  { A := Over.mk Q.π, isAb := Q.isAb, g := Q.g, smoothDim := Q.smoothDim,
    c := smallPicEquiv _ Q.c, isPol := Q.isPol }

end PPCode

structure Surf : Type where

  C : ProjCode ℤ

  arith : IsArithVar C.str 1

  A : PPCode C.X

namespace Surf

variable (s : Surf)


end Surf

structure SurfFp : Type where

  p : ℕ

  [prime : Fact p.Prime]

  C : ProjCode (ZMod p)

  surf : IsProjSurface (ZMod p) C.X

  A : PPCode C.X

namespace SurfFp

attribute [instance] prime

variable (s : SurfFp)


end SurfFp

structure SurfSt : Type 1 where

  Surf : Type

  surfCh2 : Surf → ℝ

  surfDegOm : Surf → ℝ

  SurfFp : Type

  surfFpCh2 : SurfFp → ℝ

namespace SurfSt

variable {D : D7}

def of (X : DivX D) : SurfSt := ⟨X.Surf, X.surfCh2, X.surfDegOm, X.SurfFp, X.surfFpCh2⟩

end SurfSt

variable {D : D7} {X : DivX D}

end GlobalTheory.ShFam.Pad
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RecExGOfRecAtG
noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem exists_du_nat (eps : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) : ∃ x0 : ℝ, ∀ (s : Scale) (C : FC) (cD ch : ℝ) (P : PreCh) (q1 : ℕ)
    (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c →
    ∃ du : P.Word → ℕ, (∀ u, 0 < du u) ∧ ∀ u, (du u : ℝ) = duP P u := by
  obtain ⟨x0, h⟩ := Inh.g_big eps h0 h1
  refine ⟨x0, fun s C cD ch P q1 a b c hs hx hok => ?_⟩
  choose du hpos hdu using fun u => DuInt.duStarOf_nat P.R P.H (P.hcW u) hok.arith.2.1
    fun i => h s P.R _ hs hx hok.rank (hok.val.2.2.2.2.1 i).1
  exact ⟨du, hpos, hdu⟩

namespace Inh

end Inh

end GlobalTheory.Mem.Top

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsWtOfParUnique
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Col Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2
open scoped TensorProduct

namespace GlobalTheory.Mem.R3.StdModel

section Gen

variable {X : Fields} {n : ℕ} (σ : X.K →+* ℂ)

variable [NeZero n]

variable {σ} {a : ℕ} {H Γ W : Type} [AddCommGroup W] [Module ℂ W]
  {mat : H → GL (Fin a) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)} {rat : Γ → GL (Fin a) X.E → Prop} {ρ : Γ → W → W}
  {ι : Type} {lam : X.Tau → DomWeight n} {rho : GL (Fin n) X.E →* Module.End X.K (VV X.K lam)}

end Gen

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gram_V (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hI : I.Ok) (i : Fin X.toD7.R.m) : (Vc X.toD7 i).gram = 1 := by
  obtain ⟨hs, -, -, -, -, hV⟩ := hI.spaces
  have h1 := hV ((i : ℕ) + 1)
  have hn : X.B.sp.Vneg ((i : ℕ) + 1) = false := X.B.V_pos _ (by omega) i.2
  rw [hn] at h1
  change (X.B.sp.V ((i : ℕ) + 1)).gram = 1
  rw [h1]
  refine Matrix.ext fun a b => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ a b).trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL))
  (tr : TrI X.B px)



end Rec

end GlobalTheory.Mem.R3.StdModel

end
end
