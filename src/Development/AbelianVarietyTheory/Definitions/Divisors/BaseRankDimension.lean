module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertJunkColIn3

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB

namespace GlobalTheory.Fc.Ind

attribute [local instance] Formalism.BasicNotions.Host.cmStar

protected abbrev zsc {D : D7} {O : Obj D} (P : RowSideFamily O.ex) (Del h0 : ℕ) (c : ℝ) :
    DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3 :=
  GlobalTheory.Fc.zsc P Del h0 c


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure Part (D : D7) (O : Obj D) (c : ℝ) : Type 1 where
  R : Formalism.L2.RecT O.ex
  S : Formalism.L2.SG.SpectralTiesReal.STiesR R
  P : RowSideFamily O.ex
  pin : RowSideDetermined R.T P
  DH : {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)}
  Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)
  Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)
  ok1 : P.A3.fam3.Ok3 1
  B : RealTB R P Dcf Spf (GlobalTheory.Fc.zsc P DH.1.1 DH.1.2 c) S
  Rr : RealRec B.Q
  psi : PsiPPTie D P.P0 P.ψ0 P.Ps P.ψs P.I.eG
  pins : RealPins B.Q
  muDef : ∀ C CH : ℝ, (B.Q.Rl.toCx3 B.Q.F).MuDef B.Q.F.cr (B.Q.Rl.num B.Q.F C CH) B.Q.Rl.mu
  recPins : RealRecPins pins Rr

def PFire : BdP Part := fun _ _ _ b =>
  b.B.Q.Rl.toRealDat.ExAt ∧ JEvBar b.B.T b.B.Q.Rl.toRealDat b.B.κ ∧ GeoAct b.B.T b.B.Q.Rl.toRealDat b.B.κ b.B.v₀ ∧
    EvInj b.B.T b.B.Q.Rl.toRealDat b.B.v₀

def PRB : BdP Part := fun _ _ _ b => RowsB b.B

def PNmj : BdP Part := fun _ O _ b => NX.NMjT b.B.Q b.B.Q.cG b.B.Q.Sx b.B.Q.nexp O.ex.nch

def L3 (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).L3 (b.B.Q.Rl.num b.B.Q.F C CH)

def ON (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).ON (b.B.Q.Rl.num b.B.Q.F C CH)

def L6 (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr true).L6 (b.B.Q.Rl.num b.B.Q.F C CH)

def FUN (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).FUN (b.B.Q.Rl.num b.B.Q.F C CH)

variable {Bd : BdT}

def Ev {𝒜 : FamClass} (σ : RawSel Bd 𝒜) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (q : BdP Bd) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, q _ _ _ (σ Fm hc x hx i)

def EvW (q : BdP Bd) (𝒜 : FamClass) (σ : RawSel Bd 𝒜) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∀ hc : W3 𝒜 Fm, Ev σ Fm (w3_a hc) q

def EvWC (prem : ∀ {eps : ℝ}, FamP eps → Prop) (q : ℝ → ℝ → BdP Bd) (𝒜 : FamClass) (σ : RawSel Bd 𝒜) : Prop :=
  Closed (W3 𝒜) fun Fm CH => ∀ hc : W3 𝒜 Fm, prem Fm → ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ev σ Fm (w3_a hc) (q C CH)

theorem ev_of_atAll {𝒜 : FamClass} {σ : RawSel Bd 𝒜} {q : BdP Bd} (h : AtAll q 𝒜 σ) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) :
    Ev σ Fm hc q := ⟨0, fun x hx _ i => h Fm hc x hx i⟩

end GlobalTheory.Fc.Ind


end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.Params
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrimIn

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}

structure TiesB {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop where
  ok : A3.fam3.Ok3 1
  char : R.WeakCharacterisation F
  ex : R.toRealDat.ExAt
  host : Formalism.IndefR.Links.HostHyp D
  params : ∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)
  ccK : D.host.ccK = ⊤
  guard : QGuard R.toRealDat
  types : GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat
  ser : SerClause D
  junk : GlobalTheory.Hk3.InertJunk A3
  trSem : (∃ tr, R.TrISem F tr ∧ GlobalTheory.Hk3.TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep
  std : IsStdChar D R.ψ (-1)
  phs : ∀ i, R.phs i = 1
  nV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV

end GlobalTheory.PrimIn

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
noncomputable section

namespace GlobalTheory.ThK.Check

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}




theorem resEta_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {a b m : ℕ} (h : ResEtaPow K χ a) (h' : ResEtaPow K χ' b)
    (hm : m = a + b) : ResEtaPow K (χ / χ') m := fun x => by
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x, hm]
  split_ifs
  · simp
  · rcases neg_one_pow_eq_or ℂ b with e | e <;> simp [pow_add, e, div_neg]

theorem isHecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]⟩

theorem isPair_of_isTriple {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {Y : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (h : IsTriple B G Y om om') :
    IsPair B G.M Y.β (Y.β / Y.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) ∧
      IsPair B G.M' Y.α (Y.α / Y.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
      resEta_div h.chars.resβ h.chars.resα rfl, h.weil⟩,
    h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
      resEta_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩



end GlobalTheory.ThK.Check

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

def evAt {R : Type} [CommRing R] {X : Scheme.{0}} (ξ : Sp R ⟶ X) {U : X.Opens} (h : ⊤ ≤ ξ ⁻¹ᵁ U) : Γ(X, U) →+* R :=
  (Scheme.ΓSpecIso (.of R)).hom.hom.comp (ξ.appLE U ⊤ h).hom

section Path

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R]

def sqr : G.left ⟶ G.left := (𝟙 G * 𝟙 G : G ⟶ G).left

def triv (b : Sp R ⟶ S) : Sp (PowerSeries R) ⟶ G.left := spMap (PowerSeries.C (R := R)) ≫ b ≫ unitSec G

structure IsPath (c : R) (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left) : Prop where

  base : ξ ≫ G.hom = spMap (PowerSeries.C (R := R)) ≫ b

  zero : spMap (PowerSeries.constantCoeff (R := R)) ≫ ξ = b ≫ unitSec G

  scale : spMap (PowerSeries.rescale c) ≫ ξ = ξ ≫ sqr G

def HasTan {n : ℕ} (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left) {V : S.Opens} (τ : Fin n → Γ(Lie G, V))
    (w : Fin n → R) : Prop :=
  ∀ (U : G.left.Opens) (hU : ⊤ ≤ ξ ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U)
    (hb : ⊤ ≤ b ⁻¹ᵁ V') (f : Γ(G.left, U)),
    PowerSeries.coeff 1 (evAt ξ hU f) = ∑ i, w i * evAt b hb (dualApp (τ i) hV (dUnit G he f))

structure StalkData (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s))
    (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s)
    (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)) : Prop where

  str : Spec.map (CommRingCat.ofHom π) ≫ S.fromSpecStalk s = G.left.fromSpecStalk _ ≫ G.hom

  unit : Spec.map (CommRingCat.ofHom ε) ≫ G.left.fromSpecStalk _ = S.fromSpecStalk s ≫ unitSec G

  sq : Spec.map (CommRingCat.ofHom m) ≫ G.left.fromSpecStalk _ = G.left.fromSpecStalk _ ≫ sqr G

end Path

def IsRatPath {F : Type} [Field F] {Y : Scheme.{0}} (ξ : Sp (PowerSeries F) ⟶ Y) : Prop :=
  ∃ β : Sp (RatFunc F) ⟶ Y, spMap (algebraMap (RatFunc F) (LaurentSeries F)) ≫ β =
    spMap (algebraMap (PowerSeries F) (LaurentSeries F)) ≫ ξ

def RatRigid {S : Scheme.{0}} (G : Over S) [GrpObj G] {F : Type} [Field F] (b : Sp F ⟶ S) : Prop :=
  ∀ ξ : Sp (PowerSeries F) ⟶ G.left, IsPath G 2 b ξ → IsRatPath ξ → ξ = triv G b

def LocFrame {k K : Type} [Field k] [Field K] [Algebra k K] {C : Scheme.{0}} (x : Sp K ⟶ C) {W : C.Modules} {r : ℕ}
    {V₀ : C.Opens} (s : Fin r → Γ(W, V₀)) (v : Place k K) (g : Matrix (Fin r) (Fin r) K) : Prop :=
  ∃ (b : Sp v.O ⟶ C) (V : C.Opens) (t : Fin r → Γ(W, V)) (V' : C.Opens) (h₀ : V' ≤ V₀) (h₁ : V' ≤ V)
    (hx : ⊤ ≤ x ⁻¹ᵁ V') (M : Matrix (Fin r) (Fin r) Γ(C, V')),
    spMap v.O.subtype ≫ b = x ∧ ⊤ ≤ b ⁻¹ᵁ V ∧ IsFrame t ∧
      (∀ j, resM W h₀ (s j) = ∑ i, M i j • resM W h₁ (t i)) ∧ g = M.map (evAt x hx)

def IsGenOver (k : Type) {K : Type} [Field k] [Field K] [Algebra k K] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
    (x : Sp K ⟶ C) : Prop :=
  NeronCurve.IsCurve k C ∧ NeronCurve.IsGen x ∧ x ≫ strHom k C = spMap (algebraMap k K)

theorem triv_over {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (b : Sp R ⟶ S) :
    triv G b ≫ G.hom = spMap (PowerSeries.C (R := R)) ≫ b := by
  rw [triv, Category.assoc, Category.assoc, sec_hom, Category.comp_id]

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.Imports
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FunObj

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

def RealMatch.Tied (ρ : RealMatch W) : Prop :=
  ∀ (i j : Fin D.R.m) (A : Fr (G.V (.grid (i + 1) (j + 1)))) (A₁ : Fr (G.V (.grid i j))) (AV : Fr (G.V (.grid i (j + 1))))
    (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ A → IsGridFr W _ A₁ → IsGridFr W _ AV → IsGridFr W _ AV₁ →
    ∀ (t : T) ωA ωB Pi rf rl p p', IsMatch W.ψ W.θ A A₁ (frSum AV AV₁) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j)
      ωA ωB Pi rf rl p p' →
    ∀ (B : Frames G) n Φ τ τ', (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) →
      HasFlip B t ρ i j n Φ τ τ' → ∃ c : ℂ, ∀ a b, ρ.Matched (t := t) (i := i) (j := j) a b →
        p (datumA W (tensT W a τ)) = c • p' (datumB W (tensT W b τ'))

end GlobalTheory.FunObj

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.OfDat
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrimIn

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {Tw : Top.TwDat X.B}
  {Wt : Set X.B.places.Pl}

theorem TiesG.of_dat (z : Dat X I hX Tw Wt) (hU : z.R.toRealDat.LUnif) (hI : IoExt z.R.toRealDat)
    (hM : ∀ i, OneMapRowR z.core z.R.toRealDat z.geo.κ z.geo.v₀ z.geo.O (fun _ => 1) i)
    (hC : GlobalTheory.TwistField.CoverField z.core z.R.toRealDat) : TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O := by
  have e : (fun i => cj (twAt X.toD7.what₂.embLL (famR X I hX (usedOf I Tw Wt) z.Xg z.tr).A.v0) (z.R.phs i)) = fun _ => (1 : ℂ) := by
    funext i
    rw [z.pins.phs i]
    exact map_one _
  refine ⟨⟨z.geo.fw, z.geo.bar⟩, z.geo.pins, ?_, hU, hI, ?_, hC⟩
  · rw [e]; exact z.geo.phase
  · rw [e]; exact hM

end GlobalTheory.PrimIn

end
end
