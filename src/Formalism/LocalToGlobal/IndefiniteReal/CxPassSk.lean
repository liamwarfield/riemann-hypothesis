module

public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.LevelAmbTransfer
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.CxPassSk
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

structure In (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) where
  A : FamIn K G Pl0 T m
  P0 : Subgroup G
  ψ0 : P0 →* Kˣ
  P1 : Subgroup G
  ψ1 : P1 →* Kˣ
  Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)
  Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)
  Zsc : DefSub A.fam.amb → IndefScale A.fam.base
  X : CxData A.fam.amb
  gE : Representation ℂ G X.EE

namespace In

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (I : In K G Pl0 T m)

abbrev cr : Crd I.A.fam.amb (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc) := crdOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc

abbrev cg : Crd I.A.fam.amb (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc) := crdOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc

def lvP : Bool → Subgroup G := fun b => cond b I.P1 I.P0

def lvψ : ∀ b, I.lvP b →* Kˣ
  | false => I.ψ0
  | true => I.ψ1

abbrev Sb (b : Bool) := I.X.data I.cr b

abbrev Sg := (prin I.X).data I.cg false

abbrev iCg := I.X.iC I.cg false I.A.fam.base.μ0

def Jm (b : Bool) : Matrix (Fin I.Sg.D) (Fin (I.Sb b).D) K :=
  kMat I.A.fam.base.v0.embedding (relMat I.iCg (I.X.iC I.cr b I.A.fam.base.μ0))

def ρf (g : G) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  kMat I.A.fam.base.v0.embedding (relMat I.iCg ((I.gE g).comp I.iCg))

def Jt (b : Bool) (t : I.A.fam.base.Tup) :
    Matrix (Fin ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ t))
      (Fin ((lv (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ t)) K :=
  kMat I.A.fam.base.v0.embedding (relMat (I.X.iC I.cg false t) (I.X.iC I.cr b t))


open Classical in
def epM (P : Subgroup G) (ψ : P →* Kˣ) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  haveI : Fintype P := Fintype.ofFinite P
  ((Nat.card P : K)⁻¹) • ∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) • I.ρf (h : G)

structure Hyp (s : ℕ) : Prop where
  ok : I.A.fam.Ok s
  sep : I.A.fam.TypesSep
  stable : I.X.zs.Stable
  inBlock : I.X.zs.InBlock
  h4pos : I.X.H4pos
  pos0 : (I.A.side I.P0 I.ψ0 I.X.zs).Pos
  pos1 : (I.A.side I.P1 I.ψ1 I.X.zs).Pos
  h2 : ∀ b, I.X.H2 I.cr b
  ratMu : ∀ b, I.X.RATmu I.cr b
  h2g : PrincipalInjectiveCommonRange I.A I.X (P1 := I.P1) (ψ1 := I.ψ1) (Dc := I.Dc) (Sp := I.Sp) (Zsc := I.Zsc)
  ratMug : I.X.RATmu I.cg false
  gunit : GUnit I.A I.X I.gE
  gequiv : GEquiv I.A I.X I.gE
  np0 : I.X.nP false = (Nat.card I.P0 : ℝ)
  np1 : I.X.nP true = (Nat.card I.P1 : ℝ)

def PRho : Prop :=
  ∀ s, I.Hyp s → I.ρf 1 = 1 ∧ (∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) ∧
    ∀ g (x : Fin I.Sg.D → K), I.iCg (cpt I.A.fam.base.v0.embedding (I.ρf g *ᵥ x)) =
      I.gE g (I.iCg (cpt I.A.fam.base.v0.embedding x))

def PJ : Prop :=
  ∀ s, I.Hyp s → ∀ b, (∀ x : Fin (I.Sb b).D → K, I.iCg (cpt I.A.fam.base.v0.embedding (I.Jm b *ᵥ x)) =
      I.X.iC I.cr b I.A.fam.base.μ0 (cpt I.A.fam.base.v0.embedding x)) ∧ Function.Injective (I.Jm b).mulVec

def PJt : Prop :=
  ∀ s, I.Hyp s → ∀ b t,
    (∀ x, I.X.iC I.cg false t (cpt I.A.fam.base.v0.embedding (I.Jt b t *ᵥ x)) =
      I.X.iC I.cr b t (cpt I.A.fam.base.v0.embedding x)) ∧
    (∀ x, I.cg.toR I.X.zs false t (I.Jt b t *ᵥ x) = I.cr.toR I.X.zs b t x) ∧
    ∀ x, I.Jm b *ᵥ (I.X.rowMat I.cr b t *ᵥ x) = I.X.rowMat I.cg false t *ᵥ (I.Jt b t *ᵥ x)

def PMet : Prop :=
  ∀ s, I.Hyp s → ∀ b v (x y : Fin (I.Sb b).D → K),
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (I.Sb b).D)) (I.Sb b).XE v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) (Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt (Nat.card (I.lvP b))) I.Sg.XE) v
        (I.Jm b *ᵥ x) (I.Jm b *ᵥ y)

def PFrames : Prop := ∀ s, I.Hyp s → ∀ v, IsUnit (I.Sg.XE v).det

def PUni : Prop :=
  ∀ s, I.Hyp s → ∀ v (g : G) (x y : Fin I.Sg.D → K),
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE v (I.ρf g *ᵥ x) (I.ρf g *ᵥ y) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE v x y

end In

end Formalism.IndefR.CxPass
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.PHeisThP
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.PHeisTh

abbrev Ix {D : D7} (V W : HSp D) : Type := Fin V.rank × Fin W.rank × Fin (nE D)

def Co {D : D7} (V W : HSp D) (x : WA V W) (a : Ix V W) : AF D.host.F := Phi V W x a.1 a.2.1 a.2.2

def CoordFinP : Prop :=
  ∀ (D : D7) (V W : HSp D) (x : WA V W), x.map (finPart D) = 0 → ∀ a, (Co V W x a).2 = 0



def PsiOpenP : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∃ G : AddSubgroup (Af F), IsOpen (G : Set (Af F)) ∧ (∀ y ∈ G, ∀ z ∈ Ohat F, z * y ∈ G) ∧
      ∀ y ∈ G, ψ (pairA F 0 y) = 1

def PsiSmoothP : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (k : ℕ) (s : (Fin k → ℝ) →+ Ainf D.host.F), Continuous s →
      ContDiff ℝ ∞ fun t => ψ (pairA D.host.F (s t) 0)

end Formalism.IndefR.PHeisTh

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.IsThPKernelSigBase
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.IndefR.Conj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


variable (D) in
def labLL (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)

def labE (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) : D.host.E →+* ℂ := σ.comp (labLL D τ)

theorem labE_base (τ : D.what₂.Tau) : labE D.what₂.embLL τ = tauE D τ := by
  ext x
  have h := RingHom.congr_fun D.embE_φ₀ ((D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E) x)
  simpa [labE, labLL, tauE, Host.emb] using h

structure ArchLab (D : D7) where
  perm : D.what₂.Tau ≃ D.what₂.Tau
  side : Bool

def ArchLab.emb (A : ArchLab D) (τ : D.what₂.Tau) : D.host.E →+* ℂ :=
  if A.side then tauE D (A.perm τ) else (starRingEnd ℂ).comp (tauE D (A.perm τ))

def IsLabOf (σ : D.what₂.LL →+* ℂ) (A : ArchLab D) : Prop := ∀ τ, labE σ τ = A.emb τ



variable (D) in
def LabExists : Prop := ∀ σ : D.what₂.LL →+* ℂ, ∃ A : ArchLab D, IsLabOf σ A




end Formalism.IndefR.Conj

end
end
