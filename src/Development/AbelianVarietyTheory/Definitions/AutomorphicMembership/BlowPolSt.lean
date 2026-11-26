module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HomAppHomOfRestrictImage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InclMulInvMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChainHost
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChain
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTopRowSym
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvSmulMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.GtBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.TorRef

section Fun

variable {O : Type} [CommRing O]

def resInt (O : Type) [CommRing O] [Module.Finite ℤ O] (φ : InvFun ℤ) : InvFun O where
  toFun n B := φ.eval (Fin n → O) B
  inv n m r hr B := φ.eval_comp (r := r.restrictScalars ℤ) hr B
  zero B := by
    rw [φ.eval_eq (n := 0) (r := 0) fun a => ⟨0, Subsingleton.elim _ _⟩]
    exact φ.zero _

def IsTame (φ : InvFun O) : Prop :=
  (∀ (n k : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) ∧
    ∀ n B, 0 ≤ φ.toFun n B

end Fun

section Cones

variable {R : Type} [CommRing R] [IsDomain R]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def Refines (H : Host E) (q : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) : Prop :=
  IsPolFan H.bar q φ ∧ NoSelfInt H.bar q φ ∧ IsTwInv H φ ∧ IsPosFn H φ ∧ IsTame φ ∧
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ γ →
        (resInt (𝓞 E) φs).LinearOn γ ∧ ∀ N ∈ 𝒩, IsFine N γ

end Cones

end GlobalTheory.TorRef
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Enl0 (B B' : Base) : Prop :=
  B'.toPre = B.toPre ∧ B'.embLL '' (B'.Ks : Set B'.LL) = B.embLL '' (B.Ks : Set B.LL) ∧
    B.embLL '' (B.LL0 : Set B.LL) ⊆ B'.embLL '' (B'.LL0 : Set B'.LL) ∧ Set.range B.embLL ⊆ Set.range B'.embLL

theorem isBaseEnlargementFixedCoefField_of_coeffEnlargement {B B' : Base} (h : Enl B B') : Enl0 B B' := ⟨h.1, h.2.1, h.2.2.1.ge, h.2.2.2⟩

def DatExt0 : Prop := StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∃ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' ∧ Ext z z'

theorem datExt_of_datExt0 (h : DatExt0) : DatExt := by
  unfold DatExt0 at h
  unfold DatExt
  exact StepW.trans h (StepW.of_all fun _ _ _ _ _ _ _ H B f T w e => H B f T w (isBaseEnlargementFixedCoefField_of_coeffEnlargement e))

end GlobalTheory.Mem.R3.Rw

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
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
structure ExtN (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') : Prop where
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
      HEq (z'.R.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) (by exact (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).res ok' φ'))
        (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) (by exact (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok φ))


set_option maxHeartbeats 2000000 in
theorem ExtN.ext {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'} (e : ExtN z z')
    (h : ∀ v v', Below (w.D Z) (w'.D Z') v v' → (v ∈ z.W1 (fun _ _ => 0) ↔ v' ∈ z'.W1 fun _ _ => 0)) : Ext z z' :=
  { e with W1 := h }


set_option maxHeartbeats 2000000 in
theorem Ext.extN {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'} (e : Ext z z') : ExtN z z' :=
  { e with }

end GlobalTheory.Mem.R3.Rw

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentFlagVec
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.LieMet GlobalTheory.Points GlobalTheory.GradedPieces
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.Frm

attribute [local instance] Over.cartesianMonoidalCategory

section Linear

variable {C M : Type} [NormedField C] [IsUltrametricDist C] [AddCommGroup M] [Module C M] {m : ℕ}






end Linear

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X} {x' : Sp T ⟶ X}

end Tangent

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀} (y : Z.Pt)

variable {y}




end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} (ct : At S κ p)

variable {ct}


end GlobalTheory.LocM.Frm
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStdFStdLvC
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.StdModel

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

section Ker

variable {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX}

theorem stdKer_iff (t : KerEntTied ex) : I.StdKer l Z t ↔ I.StdKerTie l Z t :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩,
    fun ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩⟩

end Ker

section Tw

variable (l0 : I.Law0 l) {inQ : (I.rec7 l Z).what₂.Tup → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
  {T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ} {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {J : Formalism.L2.Herm.TwChJointS T H}
  {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}

end Tw




section Frames

open GlobalTheory.Mem.FormSym


end Frames

end GlobalTheory.Mem.Col2.StdModel

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HodgeGramEqRiemann
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.ShFam.Pad
open scoped ComplexOrder

namespace GlobalTheory.ShFam

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

variable {σ : c.F →+* ℂ} {r : ℕ}

section Riemann

variable {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (W : UnfWit U)
  {a : ℝ} (ha : ∀ k (τ : (U.X k).Ψ), (τ.1 (-(U.X k).ξ0)).im = a) {k : U.Comp} {x : (U.X k).dom} (hx : IsOrth (U.X k) x.1)
include hσ hU ha hx

theorem im_hermForm_orth (v w : (W.F.Di (W.ik k)).La) :
    (hermForm (((2 * a : ℝ) : ℂ) • 1) (W.Pm k x v) (W.Pm k x w)).im = (W.F.Di (W.ik k)).EF v w := by
  classical
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1
    (Formalism.L2.PjFree.relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  rw [← hp0] at hf
  have hper (v) : W.Pm k x v = perVec (U.X k) (W.e.trans f) x.1 (W.φ k v : Fin r → E) := funext fun j => by
    rw [W.Pm_eq, perVec, Equiv.trans_apply]
    have h := hf (W.e j)
    generalize f (W.e j) = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega), Formalism.L2.PjFree.perFr, dif_pos a, dif_pos hn]
    · rw [if_pos (by omega), Formalism.L2.PjFree.perFr, dite_eq_right a,
        dif_pos (show conjEmb (Formalism.L2.PjFree.relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dif_pos hn]
      rfl
  have hd : (((2 * a : ℝ) : ℂ) • 1 : Matrix _ _ ℂ) = diagonal (diagXi (U.X k) (W.e.trans f)) := by
    rw [smul_one_eq_diagonal]
    exact congrArg _ (funext fun j => by rw [diagXi, ha])
  rw [hd, hper, hper, im_diag_ortho _ _ _ hx, ← W.iso]
  simp

theorem hermForm_eq_of_orth {i : Fin W.F.n} {P : (W.F.Di i).La →+ (Fin W.g → ℂ)}
    (hP : IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P) {Hm : Matrix (Fin W.g) (Fin W.g) ℂ}
    (hH : ∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) {y : FrPt Xo c (CAt σ)}
    {z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin W.g → ℂ)} (hy : AnLie W.F i P y z) (e : y.x = (U.un k x).x)
    {τ : E →+* ℂ} {T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ}
    (hT : ∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (y.u τ b)) :
    (of fun b b' => hermForm Hm (z τ b') (z τ b)) = ((2 * a : ℝ) : ℂ) • (Tᴴ * T) := by
  classical
  have p := W.period k x
  obtain ⟨hPx, hv⟩ := W.lie k x
  obtain ⟨h, gam, hex, hh, hiso, -⟩ := familyUnif_exp_unique E H Dw l Xo _ _ _ W.F i (W.ik k) P _ hP p
    (by rw [← hPx, ← hy.1, e])
  set A := LinearMap.toMatrix' h.toLinearMap with hA
  have hAv : ∀ z, A *ᵥ z = h z := fun z => by rw [hA, LinearMap.toMatrix'_mulVec]; rfl
  have hcol (b) : A *ᵥ z τ b = ∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ) := by
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ W.F _ _ p _ ((U.un k x).u τ) _ (hv τ) _
      (y.u τ b)).1 (hPx ▸ hT b)
    have d2 := (ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ W.F _ P hP _ _ h.toLinearMap p hex _ _).1 (hy.2 τ b)
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ W.F _ _ p
    rw [hAv]
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have key := UnitDet.eq_of_im_hermForm_eq _ hP.2.2.2.1
    (Aᵀ * ((((2 * a : ℝ) : ℂ) • 1) * A.map (starRingEnd ℂ))) Hm (by
      rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
      rw [← UnitDet.hermForm_mulVec, hAv, hAv, ← hh, ← hh, im_hermForm_orth hσ hU W ha hx, hiso, hH])
  ext b b'
  rw [of_apply, ← key, ← UnitDet.hermForm_mulVec, hcol, hcol]
  have hi : ∀ j j' : Fin (Dw.mult τ), W.e.symm ⟨τ, j⟩ = W.e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
  simp [hermForm, smul_mulVec, sum_dotProduct, dotProduct_sum, star_sum, Pi.single_apply, hi, mul_apply, mul_comm]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm]

end Riemann

theorem isCombAt_co {y y' : FrPt Xo c (CAt σ)} (e : y'.x = y.x) {g : EigFrame Z σ ((cxPt Z y).1 ≫ genι Z)}
    (hg : ∀ τ i, g.v τ i = (cxFrame Z y').v τ i) (τ : E →+* ℂ) (b : Fin (Dw.mult τ)) :
    IsCombAt y.x (y.u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => (cxFrame Z y).co g τ b' b) (y'.u τ b) := by
  obtain ⟨x, xo, u, ut, ue, ub, s, sg⟩ := y'
  dsimp only at e
  subst e
  let L := lieEquiv (S := CAt σ) Z y (x := (cxPt Z y).1 ≫ genι Z) (Category.assoc _ _ _).symm
  refine (isComb_iff (t := Xo.univ.t) (S := CAt σ) (fun i => tanOf (y.tan τ i)) _ (tanOf (ut τ b))).2 (L.injective ?_)
  exact (tan_ext (w := g.vec τ b) (hg τ b).symm).trans (((cxFrame Z y).vec_eq g τ b).trans
    ((map_sum L _ _).trans (Finset.sum_congr rfl fun _ _ => map_smul L _ _)).symm)

theorem x_eq_of_cxPt {y y' : FrPt Xo c (CAt σ)} (h : (cxPt Z y).1 = (cxPt Z y').1) : y.x = y'.x := by
  have := Z.jQ_open
  rw [← ptF_fst (S := CAt σ) y, ← ptF_fst (S := CAt σ) y']
  exact congrArg (· ≫ _) ((cancel_mono Z.jQ).1 h)

variable (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r)

def IsHodgeFrame (y : CxPts (genStr Z) σ) (g : EigFrame Z σ (y.1 ≫ genι Z)) : Prop :=
  ∃ (ψ : ℂ →+* ℂ) (σ' : c.F →+* ℂ) (k : (U σ').Comp) (x : ((U σ').X k).dom),
    (ψ = RingHom.id ℂ ∨ ψ = starRingEnd ℂ) ∧ σ' = ψ.comp σ ∧ Formalism.L2.PjFree.GoodEmb c σ' ∧ IsOrth ((U σ').X k) x.1 ∧
      (cxPt Z ((U σ').un k x)).1 = spMap ψ ≫ y.1 ∧ g.IsMap ψ (cxFrame Z ((U σ').un k x))


open Classical in
def EigMet.hodge (b : ℝ) (hb : 0 < b) (G₀ : EigMet Z σ) : EigMet Z σ where
  gram y g τ := if h : ∃ f, IsHodgeFrame U y f then (b : ℂ) • ((h.choose.co g τ)ᴴ * h.choose.co g τ) else G₀.gram y g τ
  pos y g τ := by
    split_ifs with h
    · exact (PosDef.conjTranspose_mul_self _ (mulVec_injective_of_isUnit
        ((isUnit_iff_isUnit_det _).2 (h.choose.isUnit_det_co g τ)))).smul (Complex.zero_lt_real.2 hb)
    · exact G₀.pos y g τ
  change y f g τ := by
    split_ifs with h
    · rw [← h.choose.co_mul f g]
      simp only [conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    · exact G₀.change y f g τ

variable {U} {y : CxPts (genStr Z) σ} {f g : EigFrame Z σ (y.1 ≫ genι Z)}

theorem spMap_dualMap_id (R : Type) [CommRing R] : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
  rw [← Spec.map_id]
  congr 1
  ext r <;> simp [dualMap]

theorem isHodgeFrame_cxFrame (hσ : Formalism.L2.PjFree.GoodEmb c σ) {k : (U σ).Comp} {x : ((U σ).X k).dom}
    (hx : IsOrth ((U σ).X k) x.1) : IsHodgeFrame U (cxPt Z ((U σ).un k x)) (cxFrame Z ((U σ).un k x)) :=
  ⟨_, σ, k, x, .inl rfl, rfl, hσ, hx, by rw [show spMap (RingHom.id ℂ) = 𝟙 _ from Spec.map_id _, Category.id_comp],
    fun _ _ => by rw [spMap_dualMap_id, Category.id_comp]⟩

theorem liesIn_iff_of_comp {σ' : c.F →+* ℂ} {y' : CxPts (genStr Z) σ'} {ψ : ℂ →+* ℂ} (e : y'.1 = spMap ψ ≫ y.1)
    (C : Closeds (gen Z)) : LiesIn y' C ↔ LiesIn y C := by
  have : y'.1 (IsLocalRing.closedPoint ℂ) = y.1 (IsLocalRing.closedPoint ℂ) := by
    rw [e]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ (Subsingleton.elim (α := PrimeSpectrum ℂ) _ _))
  rw [LiesIn, LiesIn, this]

theorem IsHodgeFrame.not_liesIn (h : IsHodgeFrame U y g) : ¬ LiesIn y (genBd Z) := fun hy => by
  obtain ⟨ψ, σ', k, x, -, -, -, -, e, -⟩ := h
  exact not_liesIn_cxPt _ ((liesIn_iff_of_comp e _).2 hy)

theorem IsHodgeFrame.conj (h : IsHodgeFrame U y g) {σ₁ : c.F →+* ℂ} {y₁ : CxPts (genStr Z) σ₁}
    {g₁ : EigFrame Z σ₁ (y₁.1 ≫ genι Z)} (hσ : σ = (starRingEnd ℂ).comp σ₁) (e : y.1 = spMap (starRingEnd ℂ) ≫ y₁.1)
    (hg : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v g₁ embτ basisIdx) (starRingEnd ℂ) g) : IsHodgeFrame U y₁ g₁ := by
  obtain ⟨ψ, σ', k, x, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨ψ.comp (starRingEnd ℂ), σ', k, x, ?_, by rw [h2, hσ]; rfl, h3, h4, ?_, fun τ i => ?_⟩
  · rcases h1 with rfl | rfl
    exacts [.inr rfl, .inl (RingHom.ext Complex.conj_conj)]
  · rw [h5, e, ← Category.assoc, ← Spec.map_comp]; rfl
  · rw [h6, hg, GlobalTheory.GradedPieces.dual_comp]

variable (hU : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ))
include hU

theorem exists_isHodgeFrame (hy : ¬ LiesIn y (genBd Z)) : ∃ g, IsHodgeFrame U y g := by
  have good : ∀ {σ : c.F →+* ℂ} {y : CxPts (genStr Z) σ}, Formalism.L2.PjFree.GoodEmb c σ → ¬ LiesIn y (genBd Z) →
      ∃ g, IsHodgeFrame U y g := fun {σ y} hσ hy => by
    have hr : Set.range y.1 ⊆ Set.range Z.jQ := by
      rintro _ ⟨p, rfl⟩
      obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
      exact not_not.1 hy
    have := Z.jQ_open
    let xF := IsOpenImmersion.lift Z.jQ y.1 hr
    have hxF : xF ≫ Z.jQ = y.1 := IsOpenImmersion.lift_fac _ _ _
    have hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F (CAt σ)) := by
      have h2 := y.2
      rw [← hxF, Category.assoc, Z.jQ_over] at h2
      exact h2
    have ho : (xF ≫ pullback.fst _ _) ≫ Xo.s = sOf c (CAt σ) := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hs]
      exact OpenReg.spMap_comp _ _
    have : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
    obtain ⟨z, hz⟩ : ∃ z : FrPt Xo c (CAt σ), z.x = xF ≫ pullback.fst _ _ := GlobalTheory.FlagTan.exists_frPt _ ho
    obtain ⟨k, f, t, hb⟩ := (hU σ hσ).2.2.1 z
    obtain ⟨x, hx, b, hb', e⟩ := ortho_holds r _ f.1 f.2
    obtain ⟨t', ht⟩ := ((hU σ hσ).2.2.2.1 k k ⟨x, KU.orth_dom _ hx⟩ f).2 ⟨1, one_mem _, b, hb', by rw [KU.lact_one, ← e]⟩
    obtain rfl : cxPt Z ((U σ).un k ⟨x, KU.orth_dom _ hx⟩) = y := by
      rw [cxPt_congr (ht.1.symm.trans hb.1.symm)]
      exact Subtype.ext (Eq.trans (congrArg (· ≫ Z.jQ)
        (pullback.hom_ext ((ptF_fst z).trans hz) ((ptF_snd z).trans hs.symm))) hxF)
    exact ⟨_, isHodgeFrame_cxFrame hσ hx⟩
  by_cases hσ : GoodEmb c σ
  · exact good hσ hy
  have h1 : GoodEmb c ((starRingEnd ℂ).comp σ) := by simpa only [goodOf, if_neg hσ] using goodEmb_goodOf c σ
  have hc : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext Complex.conj_conj))
  let y' : CxPts (genStr Z) ((starRingEnd ℂ).comp σ) :=
    ⟨spMap (starRingEnd ℂ) ≫ y.1, by rw [Category.assoc, y.2, ← Spec.map_comp]; rfl⟩
  obtain ⟨g', hg'⟩ := good (y := y') h1 fun h => hy ((liesIn_iff_of_comp rfl _).1 h)
  obtain ⟨g, hg⟩ := g'.exists_isMap (starRingEnd ℂ) (φ' := σ) (x' := y.1 ≫ genι Z)
    (RingHom.ext fun _ => (Complex.conj_conj _).symm) (by simp only [y', ← Category.assoc, hc, Category.id_comp])
  refine ⟨g, hg'.conj rfl rfl fun τ i => ?_⟩
  rw [hg, GlobalTheory.GradedPieces.dual_comp, show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ from
    RingHom.ext Complex.conj_conj, spMap_dualMap_id, Category.id_comp]

variable {a : ℝ} (ha0 : 0 < a) (ha : ∀ σ k (τ : ((U σ).X k).Ψ), (τ.1 (-((U σ).X k).ξ0)).im = a)
include ha0 ha

theorem IsHodgeFrame.unitary (hf : IsHodgeFrame U y f) (hg : IsHodgeFrame U y g) (τ : E →+* ℂ) :
    (f.co g τ)ᴴ * f.co g τ = 1 := by
  classical
  obtain ⟨ψ, σ', k, x, h1, h2, h3, h4, h5, h6⟩ := hf
  obtain ⟨ψ₁, σ₁, k₁, x₁, g1, g2, g3, g4, g5, g6⟩ := hg
  obtain rfl : ψ = ψ₁ := by
    rw [h2] at h3
    rw [g2] at g3
    rcases h1 with rfl | rfl <;> rcases g1 with rfl | rfl
    exacts [rfl, (not_good_conj c (σ := σ) h3 g3).elim, (not_good_conj c (σ := σ) g3 h3).elim, rfl]
  obtain rfl : σ' = σ₁ := h2.trans g2.symm
  have hx : (cxPt Z ((U σ').un k x)).1 ≫ genι Z = spMap ψ ≫ y.1 ≫ genι Z := by rw [h5, Category.assoc]
  obtain ⟨g', hg'⟩ := g.exists_isMap ψ h2 hx
  obtain ⟨W⟩ := nonempty_unfWit_of_isUnf E H Dw l Xo c σ' r _ (hU _ h3)
  have e := x_eq_of_cxPt (g5.trans h5.symm)
  have key := hermForm_eq_of_orth h3 (hU _ h3) W (ha σ') h4 (W.period k₁ x₁)
    (im_hermForm_orth h3 (hU _ h3) W (ha σ') g4) (W.lie k₁ x₁) e
    (isCombAt_co e (fun τ i => (hg' τ i).trans (g6 τ i).symm) τ)
  have h7 : (((2 * a : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  rw [h6.co τ hg' hx] at key
  have k2 : ((f.co g τ).map ψ)ᴴ * (f.co g τ).map ψ = 1 := smul_right_injective _ h7 (key.symm.trans (by
    ext b b'
    simp [hermForm, smul_mulVec, Pi.single_apply, one_apply, eq_comm]
    simp [Matrix.one_apply, eq_comm]))
  rcases h1 with rfl | rfl
  · exact k2
  · have := congrArg (fun M => M.map (starRingEnd ℂ)) k2
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    convert this using 2 <;> ext <;> simp

variable {b : ℝ} {hb : 0 < b} {G₀ : EigMet Z σ}

theorem IsHodgeFrame.gram_eq (hf : IsHodgeFrame U y f) (g : EigFrame Z σ (y.1 ≫ genι Z)) (τ : E →+* ℂ) :
    (EigMet.hodge U b hb G₀).gram y g τ = (b : ℂ) • ((f.co g τ)ᴴ * f.co g τ) := by
  have h : ∃ f, IsHodgeFrame U y f := ⟨f, hf⟩
  refine (dif_pos h).trans (congrArg _ ?_)
  rw [← h.choose.co_mul f g, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (f.co g τ),
    h.choose_spec.unitary hU ha0 ha hf, Matrix.one_mul]

end Free

end GlobalTheory.ShFam
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NormDetAtConstOfPlacewise
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal

namespace GlobalTheory.ShFam.Pad

def inclQb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
    (c : Coeff l) : c.F →+* Qb :=
  c.F.val.toRingHom.codRestrict (algebraicClosure ℚ ℂ) fun a =>
    haveI := c.fin
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a).algHom c.F.val)


open Classical in
def carry {F : Type} [Field F] (f g : F →+* Qb) : Qb →+* Qb :=
  haveI : Nonempty (Qb →+* Qb) := ⟨RingHom.id Qb⟩
  if f = g then RingHom.id Qb else Classical.epsilon fun σ => σ.comp f = g

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

def ioAt (p : ℕ) [Fact p.Prime] (y : Pt s) : Qb →+* ℂ_[p] := (iotaP p).comp (carry y.fK (inclQb κ.c))

def normDetIo (p : ℕ) [Fact p.Prime] (b : Bool) (τ : D.what₂.Tau) (y : Pt s) (io : Qb →+* ℂ_[p]) (a : Qb) : ℝ :=
  ‖io a‖ * Real.exp (∑ i : Fin N, y.lnRoot io p b (DV.tauEmb D τ) i)


open Classical in
def normDetAt (p : ℕ) (b : Bool) (τ : D.what₂.Tau) (y : Pt s) (a : Qb) : ℝ :=
  if h : p.Prime then (haveI := Fact.mk h; normDetIo s p b τ y (ioAt s p y) a) else 1

def padAt {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} (L : LocSt D N j ng)
    (G : GlobSt fun p => (L.loc p).Mdl) (M : AdmSt D N j jC) (F : FlatSt s)
    (I : ArIn D.what₂.Tau N (D.R.f * N) s.Comp) : PadPkg D N j s.Comp jC ng :=
  { padOf s L G M F I with
    normDetT := fun p τ (y : Pt s) => normDetAt s p true τ y (F.sv τ y)
    normDetH := fun p τ (y : Pt s) => normDetAt s p false τ y (F.sv τ y) }

section Unfold

variable {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} (L : LocSt D N j ng)
  (G : GlobSt fun p => (L.loc p).Mdl) (M : AdmSt D N j jC) (F : FlatSt s) (I : ArIn D.what₂.Tau N (D.R.f * N) s.Comp)

end Unfold

end GlobalTheory.ShFam.Pad
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InjectiveOfFlatLocal
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Polynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM.Bdy

section Algebra

theorem exists_etale_local (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (k₀ k : Type) [Field k₀] [Field k]
    [Algebra k₀ k] [FiniteDimensional k₀ k] [Algebra.IsSeparable k₀ k] (φ : k₀ →+* ResidueField V) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (_ : IsLocalHom (algebraMap V W))
      (j : k →+* ResidueField W), Module.Finite V W ∧ Algebra.Etale V W ∧
      j.comp (algebraMap k₀ k) = (ResidueField.map (algebraMap V W)).comp φ := by
  let pb := Field.powerBasisOfFiniteOfSeparable k₀ k
  have hm := minpoly.monic pb.isIntegral_gen
  have hs : ((minpoly k₀ pb.gen).map φ).Separable := Polynomial.Separable.map (Algebra.IsSeparable.isSeparable k₀ pb.gen)
  obtain ⟨g, hgm, hg, hdvd⟩ := Polynomial.exists_monic_irreducible_factor ((minpoly k₀ pb.gen).map φ) (fun h => by
    have := Polynomial.degree_eq_zero_of_isUnit h
    rw [Polynomial.degree_map] at this
    exact (minpoly.degree_pos pb.isIntegral_gen).ne' this)
  obtain ⟨f, rfl, -, hf⟩ := Polynomial.lifts_and_degree_eq_and_monic (f := residue V)
    (Polynomial.mem_lifts_of_surjective residue_surjective g) hgm
  have hfin : Module.Finite V (AdjoinRoot f) := .of_basis (AdjoinRoot.powerBasis' hf).basis
  have hfree : Module.Free V (AdjoinRoot f) := .of_basis (AdjoinRoot.powerBasis' hf).basis
  haveI : Fact (Irreducible (f.map (residue V))) := ⟨hg⟩
  have hmax : ((maximalIdeal V).map (algebraMap V (AdjoinRoot f))).IsMaximal := by
    rw [AdjoinRoot.algebraMap_eq]
    exact Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField (Field.toIsField (AdjoinRoot (f.map (residue V))))
      (AdjoinRoot.quotEquivQuotMap f (maximalIdeal V)).toRingEquiv.toMulEquiv)
  have hl : IsLocalRing (AdjoinRoot f) := by
    refine IsLocalRing.of_unique_max_ideal ⟨_, hmax, fun M hM => ?_⟩
    have hc : (M.comap (algebraMap V (AdjoinRoot f))).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := V) M
    exact (hmax.eq_of_le hM.ne_top (Ideal.map_le_iff_le_comap.2 (IsLocalRing.eq_maximalIdeal hc).ge)).symm
  have hme : (maximalIdeal V).map (algebraMap V (AdjoinRoot f)) = maximalIdeal (AdjoinRoot f) :=
    IsLocalRing.eq_maximalIdeal hmax
  have hlh : IsLocalHom (algebraMap V (AdjoinRoot f)) := ((IsLocalRing.local_hom_tfae _).out 1 3).2 hme.le
  have hres : (algebraMap (ResidueField V) (ResidueField (AdjoinRoot f))).comp (residue V) =
      (residue _).comp (algebraMap V (AdjoinRoot f)) := RingHom.ext fun a => ResidueField.map_residue _ a
  have hroot : aeval (residue _ (AdjoinRoot.root f)) (f.map (residue V)) = 0 := by
    rw [aeval_def, eval₂_map, hres, ← hom_eval₂, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root, map_zero]
  have hsep : Algebra.IsSeparable (ResidueField V) (ResidueField (AdjoinRoot f)) := by
    have hα : IsSeparable (ResidueField V) (residue _ (AdjoinRoot.root f)) :=
      (hs.of_dvd hdvd).of_dvd (minpoly.dvd _ _ hroot)
    have := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2 hα
    refine ⟨fun y => IntermediateField.isSeparable_of_mem_isSeparable (ResidueField V) _
      (L := IntermediateField.adjoin (ResidueField V) {residue _ (AdjoinRoot.root f)}) ?_⟩
    obtain ⟨y, rfl⟩ := residue_surjective y
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
    have e : residue _ (AdjoinRoot.mk f q) = aeval (residue _ (AdjoinRoot.root f)) (q.map (residue V)) := by
      rw [aeval_def, eval₂_map, hres, ← hom_eval₂, ← aeval_def, AdjoinRoot.aeval_eq]
    rw [e]
    exact IntermediateField.algebra_adjoin_le_adjoin _ _ (Polynomial.aeval_mem_adjoin_singleton _ _)
  have hun : Algebra.FormallyUnramified V (AdjoinRoot f) := Algebra.FormallyUnramified.of_map_maximalIdeal hme
  have hfp : Algebra.FinitePresentation V (AdjoinRoot f) := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  letI : Algebra k₀ (ResidueField (AdjoinRoot f)) := ((ResidueField.map (algebraMap V (AdjoinRoot f))).comp φ).toAlgebra
  have hr : aeval (residue _ (AdjoinRoot.root f)) (minpoly k₀ pb.gen) = 0 := by
    obtain ⟨c, hc⟩ := hdvd
    have : aeval (residue _ (AdjoinRoot.root f)) ((minpoly k₀ pb.gen).map φ) = 0 := by rw [hc, map_mul, hroot, zero_mul]
    rw [aeval_def, eval₂_map] at this
    exact this
  exact ⟨AdjoinRoot f, _, hl, _, hlh, (pb.lift _ hr).toRingHom, hfin, Algebra.Etale.of_formallyUnramified_of_flat,
    (pb.lift _ hr).comp_algebraMap⟩

theorem injective_of_flat_local {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (f : A →+* B)
    (hf : f.Flat) [hl : IsLocalHom f] : Function.Injective f := by
  algebraize [f]
  have : IsLocalHom (algebraMap A B) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := B)
  exact FaithfulSMul.algebraMap_injective A B

end Algebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

abbrev Cpl (X : Scheme.{0}) (x : X) : Type := AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)

structure BDat {X : Scheme.{0}} (t₀ : SAB H X) (x : X) : Type 1 where
  R : Type
  [ring : CommRing R]
  [dom : IsDomain R]
  [loc : IsLocalRing R]
  [ch0 : CharZero R]
  [noeth : IsNoetherianRing R]
  [normal : IsIntegrallyClosed R]
  [complete : IsAdicComplete (maximalIdeal R) R]
  [alg : Algebra (Cpl X x) R]
  fin : Module.Finite (Cpl X x) R
  etale : Algebra.Etale (Cpl X x) R
  locHom : IsLocalHom (algebraMap (Cpl X x) R)
  t : SAB H (Sp R)
  m : SABMap t t₀ (spMap (algebraMap (Cpl X x) R) ≫ fromSpecCompletedStalk X x)
  U : PELUnif (maximalIdeal R) t
  unitOn : ∀ y, PsiUnitOn U.D.toPre y (abLocus t.G)
  tors : U.TorsionIso

attribute [instance] BDat.ring BDat.dom BDat.loc BDat.ch0 BDat.noeth BDat.normal BDat.complete BDat.alg

def BDat.Exact {X : Scheme.{0}} {t₀ : SAB H X} {x : X} (A : BDat t₀ x) : Prop := Function.Bijective (algebraMap (Cpl X x) A.R)

theorem split_pull {S : Scheme.{0}} {t₀ : SAB H S} {k : Type} [Field k] (q : Sp k ⟶ S) {S' : SplitExt (Sp k)}
    (hS : S'.IsGt ((Over.pullback q).obj t₀.G)) {R : Type} [CommRing R] [IsLocalRing R] (j : k →+* ResidueField R)
    {ι : Sp R ⟶ S} (hq : spMap j ≫ q = spMap (residue R) ≫ ι) {t : SAB H (Sp R)} (m : SABMap t t₀ ι) :
    ∃ S₁ : SplitExt (Sp (ResidueField R)), S₁.IsGt ((Over.pullback (spMap (residue R))).obj t.G) := by
  obtain ⟨S₁, -, -, -, -, hS₁⟩ := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.gtBaseChange _ _ (spMap j) S' _ hS
  have gp₁ := ((isGrpPullback_pullback _ (spMap j)).comp (isGrpPullback_pullback t₀.G _)).congr hq rfl
  have gp₂ := (isGrpPullback_pullback t.G (spMap (residue R))).comp m.cart
  obtain ⟨e, he, -⟩ := grpPullback_iso gp₁ gp₂
  exact ⟨S₁, isGt_of_iso e hS₁⟩

theorem residue_comp {X : Scheme.{0}} (x : X) [IsNoetherianRing (X.presheaf.stalk x)] {R : Type} [CommRing R] [IsLocalRing R]
    [Algebra (Cpl X x) R] [IsLocalHom (algebraMap (Cpl X x) R)] :
    spMap ((ResidueField.map (algebraMap (Cpl X x) R)).comp
      (ResidueField.map (algebraMap (X.presheaf.stalk x) (Cpl X x)))) ≫ X.fromSpecResidueField x =
      spMap (residue R) ≫ spMap (algebraMap (Cpl X x) R) ≫ fromSpecCompletedStalk X x := by
  have h : ((ResidueField.map (algebraMap (Cpl X x) R)).comp
      (ResidueField.map (algebraMap (X.presheaf.stalk x) (Cpl X x)))).comp (residue (X.presheaf.stalk x)) =
      (residue R).comp ((algebraMap (Cpl X x) R).comp (algebraMap (X.presheaf.stalk x) (Cpl X x))) := rfl
  have h' := (spMap_comp _ _).symm.trans ((congrArg spMap h).trans ((spMap_comp _ _).trans
    (congrArg (spMap (residue R) ≫ ·) (spMap_comp _ _))))
  have h'' := congrArg (· ≫ X.fromSpecStalk x) h'
  exact (Category.assoc _ _ _).symm.trans (h''.trans (by simp only [Category.assoc]; rfl))

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p}

theorem isNoetherianRing_stalk (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (x : Z.X) :
    IsNoetherianRing (Z.X.presheaf.stalk x) := by
  haveI := Z.i.c.fin
  haveI : NumberField Z.i.c.F := {}
  haveI := (isDiscreteValuationRing_and_finite_residueField_of_numberField (Z.i.c.V W) hp
    (SharedLaws.mem_nonunits_V Z.i.c hp hW)).1
  haveI := SharedLaws.isProper_toroidalModel_structureMap Z
  haveI : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  infer_instance

theorem charZero_stalk (Z : Mdl Y i₀) (x : Z.X) : CharZero (Z.X.presheaf.stalk x) := by
  have := Z.flat
  have hf : (Z.s.stalkMap x).hom.Flat := Flat.stalkMap Z.s x
  have h0 : CharZero ((Sp (Z.i.c.V W)).presheaf.stalk (Z.s x)) := by
    have : CharZero Γ(Sp (Z.i.c.V W), ⊤) := charZero_of_injective_ringHom
      (f := (Scheme.ΓSpecIso (.of (Z.i.c.V W))).inv.hom) (ConcreteCategory.bijective_of_isIso _).1
    exact charZero_of_injective_ringHom (f := ((Sp (Z.i.c.V W)).presheaf.germ ⊤ (Z.s x) trivial).hom)
      (germ_injective_of_isIntegral (Sp (Z.i.c.V W)) (U := ⊤) (Z.s x) trivial)
  exact charZero_of_injective_ringHom (injective_of_flat_local _ hf)

theorem generic_image {X : Scheme.{0}} (x : X) {R : Type} [CommRing R] [IsDomain R] (φ : X.presheaf.stalk x →+* R)
    (hφ : Function.Injective φ) (ξ : Sp R) (hξ : ξ.asIdeal = ⊥) (y : X) (hy : y ⤳ (spMap φ ≫ X.fromSpecStalk x) ξ) :
    y = (spMap φ ≫ X.fromSpecStalk x) ξ := by
  rw [Scheme.Hom.comp_apply] at hy ⊢
  have h₁ : X.fromSpecStalk x (spMap φ ξ) ⤳ x := by
    have : X.fromSpecStalk x (spMap φ ξ) ∈ Set.range (X.fromSpecStalk x) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  obtain ⟨q, rfl⟩ : y ∈ Set.range (X.fromSpecStalk x) := by rw [Scheme.range_fromSpecStalk]; exact hy.trans h₁
  have h₂ := (X.fromSpecStalk x).isEmbedding.isInducing.specializes_iff.1 hy
  congr 1
  have h₃ := (PrimeSpectrum.le_iff_specializes _ _).2 h₂
  refine PrimeSpectrum.ext (le_antisymm h₃ fun a ha => ?_)
  have : φ a = 0 := by
    have h : φ a ∈ ξ.asIdeal := ha
    rwa [hξ] at h
  rw [hφ (this.trans (map_zero φ).symm)]
  exact q.asIdeal.zero_mem

theorem exists_bdat (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (hU : (Y Z.i).N3) (x : Z.X)
    [IsDomain (Cpl Z.X x)] [IsIntegrallyClosed (Cpl Z.X x)] (R : Type) [CommRing R] [IsLocalRing R] [Algebra (Cpl Z.X x) R]
    [hl : IsLocalHom (algebraMap (Cpl Z.X x) R)] [hf : Module.Finite (Cpl Z.X x) R] [he : Algebra.Etale (Cpl Z.X x) R]
    (hs : ∀ (t : SAB H (Sp R)), SABMap t Z.t (spMap (algebraMap (Cpl Z.X x) R) ≫ fromSpecCompletedStalk Z.X x) →
      SABMap t (Y Z.i).t ((spMap (algebraMap (Cpl Z.X x) R) ≫ fromSpecCompletedStalk Z.X x) ≫ Z.π) →
      ∃ S₁ : SplitExt (Sp (ResidueField R)), S₁.IsGt ((Over.pullback (spMap (residue R))).obj t.G)) :
    ∃ A : BDat Z.t x, Function.Bijective (algebraMap (Cpl Z.X x) R) → A.Exact := by
  have := isNoetherianRing_stalk hp hW Z x
  have := charZero_stalk Z x
  have hN : IsNoetherianRing (Cpl Z.X x) := by
    refine AdicNoeth.isNoetherianRing_of_isAdicComplete _ (maximalIdeal _) ?_ inferInstance
      (inferInstanceAs (IsNoetherianRing (ResidueField _)))
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact (maximalIdeal _).fg_of_isNoetherianRing.map _
  have : IsLocalization.AtPrime R (maximalIdeal R) :=
    IsLocalization.self fun a ha => by_contra fun h => ha h
  obtain ⟨hd, hn⟩ := isDomain_and_isIntegrallyClosed_atPrime_of_etale (Cpl Z.X x) (maximalIdeal R) R
  have hNR : IsNoetherianRing R := IsNoetherianRing.of_finite (Cpl Z.X x) R
  have hc := CompleteFiniteExtension.isAdicComplete_of_finite_local (Cpl Z.X x) R
  have f₁ := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Z.X.presheaf.stalk x) (B := Cpl Z.X x)
  have f₂ := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Cpl Z.X x) (B := R)
  have hinj : Function.Injective ((algebraMap (Cpl Z.X x) R).comp (algebraMap (Z.X.presheaf.stalk x) (Cpl Z.X x))) :=
    (FaithfulSMul.algebraMap_injective _ _).comp (FaithfulSMul.algebraMap_injective _ _)
  have : CharZero R := charZero_of_injective_ringHom hinj
  obtain ⟨t, ⟨m⟩⟩ := exists_sab (spMap (algebraMap (Cpl Z.X x) R) ≫ fromSpecCompletedStalk Z.X x) Z.t
  obtain ⟨m', -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Z.tMap m
  have e : spMap (algebraMap (Cpl Z.X x) R) ≫ fromSpecCompletedStalk Z.X x =
      spMap ((algebraMap (Cpl Z.X x) R).comp (algebraMap (Z.X.presheaf.stalk x) (Cpl Z.X x))) ≫ Z.X.fromSpecStalk x := by
    rw [spMap_comp, Category.assoc]; rfl
  let ξ : Sp R := (⊥ : PrimeSpectrum R)
  have hab := SharedLaws.abP_of_isGenP hp hW Z _ (generic_image x _ hinj ξ rfl)
  rw [← e] at hab
  obtain ⟨U, hu, ht⟩ := hU R hNR hn hc _ t m' ⟨ξ, by
    rw [Set.mem_preimage, Scheme.Hom.comp_apply]; exact hab⟩ (hs t m m')
  have hloc : ((spMap (algebraMap (Cpl Z.X x) R) ≫ fromSpecCompletedStalk Z.X x) ≫ Z.π) ⁻¹' abLocus (Y Z.i).t.G =
      abLocus t.G := Set.ext fun q => abLocus_pullback abLocusOne (Y Z.i).t.semi m'.cart.1 q
  rw [hloc] at hu
  exact ⟨{ R := R, fin := hf, etale := he, locHom := hl, t := t, m := m, U := U, unitOn := hu, tors := ht }, id⟩

theorem nonempty_bdat (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (hS : (Y Z.i).SplitFibres) (hU : (Y Z.i).N3)
    (x : Z.X) [IsDomain (Cpl Z.X x)] [IsIntegrallyClosed (Cpl Z.X x)] : Nonempty (BDat Z.t x) := by
  have := isNoetherianRing_stalk hp hW Z x
  have hN : IsNoetherianRing (Cpl Z.X x) := by
    refine AdicNoeth.isNoetherianRing_of_isAdicComplete _ (maximalIdeal _) ?_ inferInstance
      (inferInstanceAs (IsNoetherianRing (ResidueField _)))
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact (maximalIdeal _).fg_of_isNoetherianRing.map _
  obtain ⟨k, _, ak, hfin, hsep, S', hS'⟩ := hS (Z.π x)
  obtain ⟨R, _, _, _, _, j, _, _, hj⟩ := exists_etale_local (Cpl Z.X x) ((Y Z.i).X.residueField (Z.π x)) k
    ((ResidueField.map (algebraMap (Z.X.presheaf.stalk x) (Cpl Z.X x))).comp (Z.π.residueFieldMap x).hom)
  obtain ⟨A, -⟩ := exists_bdat hp hW Z hU x R fun t _ m' => split_pull _ hS' j (by
    have h₁ := residue_comp (R := R) x
    have h₂ : spMap j ≫ spMap (algebraMap ((Y Z.i).X.residueField (Z.π x)) k) =
        spMap ((ResidueField.map (algebraMap (Cpl Z.X x) R)).comp
          (ResidueField.map (algebraMap (Z.X.presheaf.stalk x) (Cpl Z.X x)))) ≫ spMap (Z.π.residueFieldMap x).hom :=
      (spMap_comp _ _).symm.trans ((congrArg spMap hj).trans (spMap_comp (Z.π.residueFieldMap x).hom
        ((ResidueField.map (algebraMap (Cpl Z.X x) R)).comp
          (ResidueField.map (algebraMap (Z.X.presheaf.stalk x) (Cpl Z.X x))))))
    rw [← Category.assoc, ← Category.assoc, ← h₁]
    refine (congrArg (· ≫ _) h₂).trans ?_
    rw [Category.assoc]
    exact (congrArg (_ ≫ ·) (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField Z.π x)).trans
      (Category.assoc _ _ _).symm) m'
  exact ⟨A⟩


open Classical in
def pick {X : Scheme.{0}} {t₀ : SAB H X} {x : X} (h : Nonempty (BDat t₀ x)) : BDat t₀ x :=
  if h' : ∃ A : BDat t₀ x, A.Exact then h'.choose else h.some

end GlobalTheory.LocM.Bdy
end
end
