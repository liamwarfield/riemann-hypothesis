module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackAbVarModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}


set_option maxHeartbeats 2000000 in
structure Ext (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') : Prop where
  H : HEq z'.core.Q.H z.core.Q.H
  l : HEq z'.core.Q.l z.core.Q.l
  c : HEq z'.core.Q.c z.core.Q.c
  Dw : HEq z'.core.Q.Dw z.core.Q.Dw
  Xo : HEq z'.core.Q.Xo z.core.Q.Xo
  U : HEq z'.core.U z.core.U
  V : HEq z'.core.V z.core.V
  dict : HEq z'.core.dict z.core.dict
  mu : HEq z'.core.mu z.core.mu
  Kf : HEq z'.core.Kf z.core.Kf
  cE : HEq z'.core.cE z.core.cE
  chiW : HEq z'.core.chiW z.core.chiW
  x₀ : HEq z'.core.x₀ z.core.x₀
  iota : HEq z'.core.iota z.core.iota
  ψ : HEq z'.R.ψ z.R.ψ
  θ : HEq z'.R.θ z.R.θ
  βW : HEq z'.R.βW z.R.βW
  βY : HEq z'.R.βY z.R.βY
  nW : HEq z'.R.nW z.R.nW
  βV : HEq z'.R.βV z.R.βV
  ΛV : HEq z'.R.ΛV z.R.ΛV
  ΛW : HEq z'.R.ΛW z.R.ΛW
  Pg : HEq z'.R.Pg z.R.Pg
  eG : HEq z'.R.eG z.R.eG
  Sb : HEq z'.R.Sb z.R.Sb
  BV : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.R.cV i').W (z.R.cV i).W ∧ HEq (z'.R.cV i').ρ (z.R.cV i).ρ ∧ HEq (z'.R.vacP i') (z.R.vacP i) ∧
    HEq (z'.R.ioP i') (z.R.ioP i) ∧ HEq (z'.R.ωP i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.ωP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq (z'.R.BV i') (z.R.BV i)
  MW : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).H (z.R.MW i (w.st Z).toD7.what₂.embLL).H ∧ HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).nacg (z.R.MW i (w.st Z).toD7.what₂.embLL).nacg ∧
    HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).ips (z.R.MW i (w.st Z).toD7.what₂.embLL).ips ∧ HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).σ (z.R.MW i (w.st Z).toD7.what₂.embLL).σ ∧
    HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).lam (z.R.MW i (w.st Z).toD7.what₂.embLL).lam ∧ HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).ε (z.R.MW i (w.st Z).toD7.what₂.embLL).ε ∧
    HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).fr (z.R.MW i (w.st Z).toD7.what₂.embLL).fr ∧ HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).enum (z.R.MW i (w.st Z).toD7.what₂.embLL).enum ∧
    HEq (z'.R.HW i' (w'.st Z').toD7.what₂.embLL) (z.R.HW i (w.st Z).toD7.what₂.embLL) ∧
    HEq (z'.geo.v₀ i' (w'.st Z').toD7.what₂.embLL) (z.geo.v₀ i (w.st Z).toD7.what₂.embLL) ∧
    ∀ φ φ', HEq φ' φ → HEq ((z'.R.FW i').j (w'.st Z').toD7.what₂.embLL (z'.geo.fw.e i' φ' : (z'.R.FW i').WK).1)
      ((z.R.FW i).j (w.st Z).toD7.what₂.embLL (z.geo.fw.e i φ : (z.R.FW i).WK).1)
  forms : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
    ∀ (k : Fin (z.R.nW i)) (k' : Fin (z'.R.nW i')), (k : ℕ) = k' →
      (w'.st Z').toD7.what₂.embLL ((z'.geo.fw.e i' φ' : (z'.R.FW i').WK).1 k') =
        (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k)
  W1 : ∀ v v', Below (w.D Z) (w'.D Z') v v' → (v ∈ z.W1 (fun _ _ => 0) ↔ v' ∈ z'.W1 fun _ _ => 0)
  cV : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.R.cV i').nW (z.R.cV i).nW ∧ HEq (z'.R.cV i').iW (z.R.cV i).iW
  pb : HEq z'.core.pb z.core.pb
  ΛY : HEq z'.R.ΛY z.R.ΛY
  κ : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.geo.κ i').aP (z.geo.κ i).aP ∧ HEq (z'.geo.κ i').aM (z.geo.κ i).aM ∧ (z'.geo.κ i').n = (z.geo.κ i).n
  ref : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.R.vP i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.vP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.HV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.HV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.thF i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.thF i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.thG i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.thG i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.νV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.νV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.fdV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.fdV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.νW i') (z.R.νW i) ∧ HEq (z'.R.fdW i') (z.R.fdW i)
  jL : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ (ok : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).Ok)
      (ok' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).Ok)
      (φ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).EqFun)
      (φ' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).EqFun),
      (∀ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (φ'.1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (φ.1 d).1)) →
      HEq (z'.R.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).res ok' φ' :))))
        (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok φ :))))


def Fine (z : Dat (w.st Z) w.I hX T Wt) : Prop := z.R.toRealDat.ExAt ∧ GlobalTheory.RealGeo.InGeo z.geo ∧ CoreP z ∧ z.Std

def DatExS : Prop := StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok), GrpTrue Z.N f → GrpAt (w.st Z) w.I →
  VolTieG (w.D Z) → ∃ z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}, Fine z

def DatExt : Prop := StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∃ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' ∧ Ext z z'

end GlobalTheory.Mem.R3.Rw

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ApolarMonomial
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.Serre

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

section Alg

variable {S : Type} [CommRing S] {ρ V : Type}

def apolar (P : MvPolynomial V S) (f : MvPowerSeries V S) : S :=
  ∑ m ∈ P.support, P.coeff m * ((m.prod fun _ n => (n.factorial : S)) * MvPowerSeries.coeff m f)

theorem apolar_monomial (m : V →₀ ℕ) (c : S) (f : MvPowerSeries V S) :
    apolar (MvPolynomial.monomial m c) f = c * ((m.prod fun _ n => (n.factorial : S)) * MvPowerSeries.coeff m f) := by
  classical
  rw [apolar, Finset.sum_subset (MvPolynomial.support_monomial_subset) fun x _ hx => by
    rw [MvPolynomial.notMem_support_iff.1 hx, zero_mul], Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

end Alg

section Exp

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {O : Type} [CommRing O] (a : OAct O G)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ X) {ρ V : Type} [Fintype ρ] [DecidableEq ρ] [Fintype V] [DecidableEq V]
  (ch : ρ → O →+* S)

variable (bar : O → O) (L : LB G.left) (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => eSec G) fun _ => 1))


variable (G) in
abbrev Pw (n : ℕ) : Over X := Over.mk x0 ⊗ powObj G n


variable (G) in
abbrev pr {n : ℕ} (b : Fin n) : (Pw G x0 n).left ⟶ G.left := (snd _ _ ≫ powPr G b).left

end Exp

section Gt

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] {oa : D.toPre.OAct O} (Y : Ray oa)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ Sp R) {ρ V : Type} [Fintype ρ] [DecidableEq ρ] [Fintype V] [DecidableEq V]
  (ch : ρ → O →+* S)

end Gt

end GlobalTheory.RayEv
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.Cht

def RootsSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : TateIso Dw k Q act e)
    (z : ℕ → kˣ), 1 ≤ Dw.p + Dw.q → (∀ n, 0 < n → IsPrimitiveRoot (z n) n) →
    (∀ n m, 0 < n → 0 < m → z (n * m) ^ m = z n) → z l.A = I.ζ l.A →
    ∃ I' : TateIso Dw k Q act e, (∀ n, 0 < n → I'.ζ n = z n) ∧ (∀ a, I'.ev l.A a = I.ev l.A a) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), I'.ev l.M a = I.ev l.M a

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} {ct : At S κ p}

variable {Z : ct.Mdl} {y : DVP ct} {e : Ext y}

end GlobalTheory.LocM.Cht
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PairVEqZeroOfMemLieSpan
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField
open scoped TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.ShFam Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

section Generic

variable {p : ℕ} [Fact p.Prime] {C : SCF p} {Λ : Type} [CommRing Λ] [StarRing Λ]
  (P : Point p (fldVal C) ↥(intO ↥C.S) Λ)

def tateIncl : P.T →+ P.V := (TensorProduct.mk ℤ_[p] ↥C.S P.T 1).toAddMonoidHom

def htMap : P.T →+ P.OmC := P.inclOm.toAddMonoidHom.comp P.al₀.toAddMonoidHom

def lieSpan : Submodule ↥C.S P.V := Submodule.span ↥C.S (P.latLie : Set P.V)

theorem span_tateIncl : Submodule.span ↥C.S (Set.range (tateIncl P)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | tmul c t =>
    rw [← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨t, rfl⟩)

theorem alC_tateIncl (t : P.T) : P.alC (tateIncl P t) = htMap P t := P.alC_tmul 1 t

end Generic

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p)

def htPt {Z : ct.Mdl} (y : ct.Pt Z) :
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing; Point p (fldVal y.C) ↥(intO ↥y.C.S) (𝓞 D.host.E) :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  htPoint (ct.dat y)

def psiEmb (D : D7) (τ : PsiT D) : D.host.E →+* ℂ := DV.tauEmb D (D.eTau.symm τ)


open Classical in
def eigProj {Z : ct.Mdl} (y : ct.Pt Z) (σ : D.host.E →+* ℂ) :
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing; (ct.htPt y).V →ₗ[↥y.C.S] (ct.htPt y).V :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  proj (isSplitting_embInt y.P) (ct.htPt y).actV σ

end At

def htpTrue (ct : At S κ p) : HTpSt ct :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  { Tp := fun y => (ct.htPt y).T
    tpAdd := fun _ => inferInstance
    OmV := fun y => (ct.htPt y).OmC
    omAdd := fun _ => inferInstance
    omMod := fun y => (inferInstance : Module ↥y.C.S (ct.htPt y).OmC)
    om := fun y => (ct.htPt y).latOm.toAddSubgroup
    ht := fun y => htMap (ct.htPt y)
    om_smul := fun y a ha _ hv => (ct.htPt y).latOm.smul_mem (⟨a, ha⟩ : ↥(intO ↥y.C.S)) hv
    TC := fun y => (ct.htPt y).V
    tcAdd := fun _ => inferInstance
    tcMod := fun y => (inferInstance : Module ↥y.C.S (ct.htPt y).V)
    iT := fun y => tateIncl (ct.htPt y)
    iT_span := fun y => span_tateIncl (ct.htPt y)
    htC := fun y => (ct.htPt y).alC
    htC_iT := fun y => alC_tateIncl (ct.htPt y)
    psiC := fun y => (ct.htPt y).pairV
    lieGt1 := fun y => lieSpan (ct.htPt y)
    eT := fun y τ => ct.eigProj y (At.psiEmb D τ) }

namespace HTp

variable (ct : At S κ p) {Z : ct.Mdl} (y : ct.Pt Z)

end HTp

end GlobalTheory.LocM
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotIsBettiZero
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier
open GlobalTheory.TrueCx GlobalTheory.FlatLine

namespace GlobalTheory.ShFam.Pad

section Expo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)


open Classical in
theorem expo_detSym (τ : GlobalTheory.AllWt.Psi H) (a : ℕ → Bool) (R : Option ℝ) (z : Letter Dw) :
    expo Dw (detSym Dw a R τ.1) z = if z.1 = τ.1 then 1 else if z.1 = conjEmb τ.1 then -1 else 0 := by
  obtain ⟨ρ, i⟩ := z
  have hne : conjEmb τ.1 ≠ τ.1 := fun e => GlobalTheory.AllWt.conj_not_mem τ (e.symm ▸ τ.2)
  have hp : Dw.mult τ.1 = Dw.p := if_pos τ.2
  have hq : Dw.mult (conjEmb τ.1) = Dw.q := if_neg (GlobalTheory.AllWt.conj_not_mem τ)
  have hl : ∀ (ρ' : E →+* ℂ) (k : ℕ), letterOf Dw (.inl (ρ', k)) = some ⟨ρ, i⟩ ↔ ρ' = ρ ∧ k = i := fun ρ' k => by
    constructor
    · intro h
      simp only [letterOf] at h
      split_ifs at h
      obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 (Option.some.inj h)
      exact ⟨rfl, congrArg Fin.val (eq_of_heq h2)⟩
    · rintro ⟨rfl, rfl⟩
      exact dif_pos i.2
  have h1 : expo Dw (detSym Dw a R τ.1) ⟨ρ, i⟩ = ∑ k ∈ Finset.range (Dw.p + Dw.q), expo Dw (rootSym Dw a R τ.1 k) ⟨ρ, i⟩ :=
    (Finsupp.sum_finsetSum_index (h := fun (a : Sym E) (n : ℤ) => if letterOf Dw a.2.2 = some ⟨ρ, i⟩ then n else 0)
      (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp)).symm
  have h2 : ∀ k, expo Dw (rootSym Dw a R τ.1 k) ⟨ρ, i⟩ = if k < Dw.p then (if τ.1 = ρ ∧ k = i then 1 else 0)
      else if conjEmb τ.1 = ρ ∧ Dw.p + Dw.q - 1 - k = i then -1 else 0 := fun k => by
    unfold expo rootSym
    split_ifs <;> rw [Finsupp.sum_single_index (by simp)] <;> simp only [hl] <;> simp [*]
  have hi := i.2
  simp only [h1, h2]
  split_ifs with e1 e2
  · subst e1
    rw [Finset.sum_eq_single (i : ℕ) (fun k _ hk => by simp [hk, hne]) fun h => absurd (Finset.mem_range.2 (by omega)) h,
      if_pos (by omega), if_pos ⟨rfl, rfl⟩]
  · subst e2
    rw [Finset.sum_eq_single (Dw.p + Dw.q - 1 - i) (fun k hk hk' => by
        have := Finset.mem_range.1 hk
        split_ifs with b1 b2 b3
        · exact absurd b2.1.symm hne
        · rfl
        · omega
        · rfl) fun h => absurd (Finset.mem_range.2 (by omega)) h,
      if_neg (by omega), if_pos ⟨rfl, by omega⟩]
  · exact Finset.sum_eq_zero fun k _ => by simp [Ne.symm e1, Ne.symm e2]

theorem expo_detSym_eq (τ : GlobalTheory.AllWt.Psi H) (a : ℕ → Bool) (R : Option ℝ) :
    expo Dw (detSym Dw a R τ.1) = fun z => -GlobalTheory.AllWt.exOf Dw (flatWt Dw τ) 0 (some z) := by
  funext ⟨ρ, i⟩
  rw [expo_detSym]
  show _ = -(GlobalTheory.AllWt.wtOf Dw (flatWt Dw τ) 0).1 (ρ, i)
  by_cases h : ρ (H.rt : E) = H.rt0
  · have h1 : ρ ≠ conjEmb τ.1 := fun e => GlobalTheory.AllWt.conj_not_mem τ (e ▸ h)
    rw [GlobalTheory.AllWt.wtOf_big (flatWt Dw τ) 0 ⟨ρ, h⟩ i ((if_pos h : Dw.mult ρ = Dw.p) ▸ i.2)]
    by_cases e : ρ = τ.1 <;> simp [flatWt, parWt, Subtype.ext_iff, e, h1]
  · have h1 : ρ ≠ τ.1 := fun e => h (e ▸ τ.2)
    have := GlobalTheory.AllWt.wtOf_small (flatWt Dw τ) 0 ⟨_, GlobalTheory.AllWt.conj_mem h⟩ i ((if_neg h : Dw.mult ρ = Dw.q) ▸ i.2)
    simp only [GlobalTheory.AllWt.conjEmb_conjEmb] at this
    rw [this]
    have h2 : conjEmb ρ = τ.1 ↔ ρ = conjEmb τ.1 :=
      ⟨fun e => by rw [← e, GlobalTheory.AllWt.conjEmb_conjEmb], fun e => by rw [e, GlobalTheory.AllWt.conjEmb_conjEmb]⟩
    have h3 : (⟨_, GlobalTheory.AllWt.conj_mem h⟩ : GlobalTheory.AllWt.Psi H) = τ ↔ ρ = conjEmb τ.1 := Subtype.ext_iff.trans h2
    simp only [flatWt, parWt, if_neg h1]
    by_cases e : ρ = conjEmb τ.1
    · rw [if_pos e, if_pos (h3.2 e)]; rfl
    · rw [if_neg e, if_neg (mt h3.1 e)]; rfl

end Expo

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (Φ : s.Flag) (L : CmList A)

abbrev cmAt (k : s.Comp) : D.what₂.Tau ≃ ((s.U κ.σ₀).X k).Ψ := cmEquiv _ s.isUnf L.ψ k

def bettiCo (k : s.Comp) (τ : D.what₂.Tau) (x : Frame ((s.U κ.σ₀).X k).Ψ N) : ℂ :=
  (hodgeC ((s.U κ.σ₀).X k) (cmAt s L k) τ : ℂ) ^ S.Dw.q * horizGen (cmAt s L k τ) x

abbrev detEx (S : Sig A N j) (τ : D.what₂.Tau) : Letter S.Dw → ℤ :=
  expo S.Dw (detSym S.Dw (fun _ => false) none (DV.tauEmb D τ))

theorem detEx_eq (S : Sig A N j) (L : CmList A) (τ : D.what₂.Tau) :
    detEx S τ = fun z => -GlobalTheory.AllWt.exOf S.Dw (flatWt S.Dw (L.ψ τ)) 0 (some z) := by
  rw [← expo_detSym_eq S.Dw (L.ψ τ) (fun _ => false) none, L.ψ_val]

def IsBetti (k : s.Comp) (τ : D.what₂.Tau) (σ : (Φ.C k).Y.Fn) (b : ℂˣ) : Prop :=
  ∀ (x : ((s.U κ.σ₀).X k).dom) (a : ℂ),
    CoordAtC (Φ.C k) ((s.U κ.σ₀).un k x) (detEx S τ) σ a ↔ a = b * bettiCo s L k τ x.1


open Classical in
def flBetti (k : s.Comp) (τ : D.what₂.Tau) : ℂˣ :=
  if h : ∃ b, IsBetti s Φ L k τ (flatSec s Φ k τ) b then h.choose else 1

variable {s Φ L} {k : s.Comp} {τ : D.what₂.Tau} {σ : (Φ.C k).Y.Fn} {b b' : ℂˣ}

end GlobalTheory.ShFam.Pad
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesOfLifts
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.StateChecks

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Wt : Set B.places.Pl}

section Types

variable {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 T₀ : Type}
  {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] {A : FamIn a.D.what₂.LL G Pl0 T₀ a.D.R.m}
  {R : RealDat a.D A Ks} (F : Face a.D A) (y : Hd R) (y' : HdB b R) (E : Hs)

end Types

section Std

variable {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok}

def cpR (z : Dat a.st I hX T Wt) :
    @RealDat3 b.st.toD7 _ _ _ _ _ _ (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _ ((by exact @alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@Dat.alg (@Late.st B C a) px I hX T Wt z))) :=
  (by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :))


set_option maxHeartbeats 2000000 in
theorem std_cpR (z : Dat a.st I hX T Wt) (h : z.Std) :
    @BrgStd b.st px I hX (usedOf I T Wt) z.Xg z.tr (coreJ b z.core).Q.c.F _ _ ((by exact @alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@Dat.alg (@Late.st B C a) px I hX T Wt z)))
      (by
        with_unfolding_all
          exact (@RealDat3.toRealDat b.st.toD7 _ _ _ _ _ _
            (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _
            (alg (a := a) b z.alg) (cpR b z) :)) := by
  with_unfolding_all exact (h :)


set_option maxHeartbeats 2000000 in
theorem std_of_copy (z₀ : Dat a.st I hX T Wt) (z : Dat b.st I hX T Wt) (h1 : z.Xg = z₀.Xg) (h2 : z.tr = z₀.tr)
    (h3 : HEq z.core (coreJ b z₀.core)) (h4 : HEq z.R (real3 b (iK := z₀.alg) z₀.R)) (h : z₀.Std) : z.Std := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4
  subst h1 h2
  obtain rfl : core = coreJ b z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg b z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((y))).symm : _)))
  subst e
  obtain rfl : R = cpR b z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR b z₀)) :))))
  exact std_cpR b z₀ h

end Std

section StdState

theorem St.std {P : Pre2 K w} (x : St P) : x.m.z.Std :=
  std_of_copy (B := B) (C := w.C) (a := P.Z₀) x.o.Z P.z x.m.z x.m.Xg x.m.tr ((by with_unfolding_all exact (x.copy.core :))) ((by with_unfolding_all exact (x.copy.R :))) P.std

end StdState

end GlobalTheory.Mem.R3.Rw.StateChecks

end
end
