module

public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.CoefCol
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section GLmat

variable (E : Type) [Field E] (n : ℕ)

def toGLm : (Sp E n ≃ₗ[E] Sp E n) ≃* GL (Fin n) E :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv E (Sp E n)).symm.trans
    Matrix.GeneralLinearGroup.toLin.symm

def ufGL [StarRing E] : UF E n →* GL (Fin n) E := (toGLm E n).toMonoidHom.comp (UF E n).subtype

end GLmat

structure CoefPk (X : Fields) (n : ℕ) (D : Type) where

  lam : X.Tau → DomWeight n

  rho : UF X.E n →* Module.End X.K (VV X.K lam)

  pair : VV X.K lam →ₗ⋆[X.K] VV X.K lam →ₗ[X.K] X.K

  Nab : D → Submodule (𝓞 X.K) (VV X.K lam)

  Del : D → Submodule (𝓞 X.K) (VV X.K lam)

namespace CoefPk

variable {X : Fields} {n : ℕ} {D : Type} (C : CoefPk X n D)

abbrev V : Type := VV X.K C.lam

def bV : Basis (VVIdx C.lam) X.K C.V := bVV X.K C.lam

def pull {D' : Type} (e : D' → D) : CoefPk X n D' where
  lam := C.lam
  rho := C.rho
  pair := C.pair
  Nab d' := C.Nab (e d')
  Del d' := C.Del (e d')

end CoefPk

section Pk

variable (X : Fields) {n : ℕ}

def roundPk (lam : X.Tau → DomWeight n) {D : Type} (L : D → Submodule (𝓞 X.E) (Sp X.E n)) : CoefPk X n D where
  lam := lam
  rho := (rhoVr X.emb lam).comp (ufGL X.E n)
  pair := pairVr X.emb lam 1
  Nab d := nabAtr X.emb lam (L d)
  Del d := delAtr X.emb lam (L d)

def squarePk (lam : X.Tau → DomWeight n) {D : Type} (L : D → Submodule (𝓞 X.E) (Sp X.E n)) : CoefPk X n D where
  lam := lam
  rho := (rhoV X.emb lam).comp (ufGL X.E n)
  pair := pairV X.emb lam 1
  Nab d := nabAt X.emb lam (L d)
  Del d := delAt X.emb lam (L d)

end Pk

section DecoKer

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.LshKer (d : Deco E n ST SG) (P : ST) : Submodule (𝓞 E) (Sp E n) :=
  Submodule.span (𝓞 E) {x | x ∈ d.Lsh ∧ d.f P x = 0}

end DecoKer

section Vals

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

def colVal (u : Pr.Word) (j : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 X.E))) :
    CoefPk X (R.N j) (DecoSet (E := X.E) (n := R.N j) (ST := ST) (SG := SG)) :=
  roundPk X (W.lamTrue u j) fun d => d.1.Lsh

def rowVal (SG : Finset (HeightOneSpectrum (𝓞 X.E))) :
    CoefPk X (R.N R.m - 1) (DecoSet (E := X.E) (n := R.N R.m - 1) (ST := ∅) (SG := SG)) :=
  squarePk X W.sgTrue fun d => d.1.N

def mtVal (j : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) :
    CoefPk X R.nV (DecoSet (E := X.E) (n := R.nV) (ST := ∅) (SG := SG)) :=
  roundPk X (W.lamV j) fun d => d.1.N

def BvLat (u : Pr.Word) (j : ℕ) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (P : ST) (d : DecoSet (E := X.E) (n := R.N j) (ST := ST) (SG := SG)) : Submodule (𝓞 X.K) (VV X.K (W.lamTrue u j)) :=
  delAtr X.emb (W.lamTrue u j) (d.1.LshKer P)

end Vals

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.TiedRec
noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions NumberField

structure ColRows (R : Ranks) where

  LL : Type
  [instLL : Field LL]
  embLL : LL →+* ℂ
  places : Rows.Places LL

  Tau : Type
  [instTau : Fintype Tau]
  card_Tau : Fintype.card Tau = R.f

  Word : Type

attribute [instance] ColRows.instLL ColRows.instTau

structure ColRec where

  R : Ranks

  host : Host R

  sp : @Spaces R host.F host.E _ _ _ _ host.cmStar _

  what₂ : ColRows R

  eTau : what₂.Tau ≃ (R.Psi)
  [wordFin : Fintype what₂.Word]

  u₀ : what₂.Word

  hcW : what₂.Word → what₂.Tau → HCParam R

  mem : ∀ u : what₂.Word, Member R what₂.Tau (hcW u)
  [nfLL : NumberField what₂.LL]
  [starLL : StarRing what₂.LL]

  embE : host.E →+* what₂.LL

  cOf : what₂.Word → host.E

  clsLat : letI := host.cmStar; ∀ u i, (mem u).C.cls i → Submodule (𝓞 host.E) (sp.X i).V

  fm : ∀ u, MemberForms what₂.LL what₂.embLL what₂.places what₂.Tau (hcW u) (mem u).C (mem u).A (mem u).P

attribute [instance] ColRec.wordFin ColRec.nfLL ColRec.starLL

end Formalism.L2.Col

namespace Formalism.BasicNotions

end Formalism.BasicNotions

end
end
