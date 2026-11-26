module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts

variable {D : D7}


variable (D) in
def Sizes : Prop :=
  1800 < D.R.r ∧ ∀ (τ : D.what₂.Tau) (j : ℕ) (hj : j + 1 < D.R.m),
    2 * (bigN D : ℚ) ^ 3 < (D.hc τ).b ⟨j + 1, hj⟩ - (D.hc τ).b ⟨j, by omega⟩

section Arrow

variable (θ : InfFam D)

def IsCuspOfType (N : Node D) (φ : GA D N.V → ℂ) : Prop :=
  IsAutFunSm θ N.V φ ∧ IsCuspFun N.V φ ∧ ∀ τ, IsTypeAt θ N.V τ (N.S τ) φ

variable {A B : Node D} {P : Type} (m : A.MeasDat)

def LiftsMult (K : P → GA D B.V → GA D A.V → ℂ) (It : P → SmT A.M → SmT B.M) : Prop :=
  ∀ F ∈ A.Cusp θ, ∃ F' ∈ B.Cusp θ, ∀ (p : P) (v : SmT A.M) (h : GA D B.V),
    IntegrableOn (fun g => K p h g * F v g) m.fd m.ν ∧ ∫ g in m.fd, K p h g * F v g ∂m.ν = F' (It p v) h

def LiftsSmooth (K : GA D B.V → GA D A.V → ℂ) : Prop :=
  ∀ φ, IsCuspOfType θ A φ → (∀ h, IntegrableOn (fun g => K h g * φ g) m.fd m.ν) ∧
    IsCuspOfType θ B fun h => ∫ g in m.fd, K h g * φ g ∂m.ν

end Arrow

section Grid

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

structure RowBase : Prop where

  lev : R.toLevCh.Is A.μ0

  inf : IsInfFam R.θ

  measY : R.models_νY

  measY' : R.models_νY'

  measX : R.models_νX

variable {R}

variable (G : GridPre R)

structure CuspAlong : Prop where

  X : ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f →
    LiftsMult R.θ (A := G.V i j) (B := G.V (i + 1) j) (G.meas t i j)
      (fun p h g => thetaKO (G.X i j).ω h g (fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f p)) fun p v => (G.X i j).It p v

  th : ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ f, IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) f →
    LiftsMult R.θ (A := G.V i (j + 1)) (B := G.V i j) (G.meas t i (j + 1))
      (fun p h g => thetaKO (G.th t i j).ω h g (fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) f p)) fun p v => (G.th t i j).It p v

  up : ∀ i, i < D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) f →
    LiftsMult R.θ (A := G.P i) (B := G.P (i + 1)) (G.mP i)
      (fun p h g => starRingEnd ℂ (thetaKO (G.dn i).ω h g (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) f p))) fun p v => G.ItU i p v

  dn : ∀ i, i < D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) f →
    LiftsMult R.θ (A := G.P (i + 1)) (B := G.P i) (G.mP (i + 1))
      (fun p h g => thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) f p)) fun p v => (G.dn i).It p v

  col : ∀ t j, j < D.R.m → ∀ f, IsFinVec R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) f →
    LiftsMult R.θ (A := G.Xp j) (B := G.Xp (j + 1)) (G.measX j)
      (fun p h g => thetaKO (G.col t j).ω g h (fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) f p)) fun p v => (G.col t j).It p v

structure CuspAlongSmooth : Prop where

  X : ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (neg (G.V (i + 1) j).V) (G.V i j).V Φ →
    LiftsSmooth R.θ (A := G.V i j) (B := G.V (i + 1) j) (G.meas t i j) fun h g => thetaKO (G.X i j).ω h g Φ

  th : ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ →
    LiftsSmooth R.θ (A := G.V i (j + 1)) (B := G.V i j) (G.meas t i (j + 1)) fun h g => thetaKO (G.th t i j).ω h g Φ

  up : ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (neg (G.P (i + 1)).V) (G.P i).V Φ →
    LiftsSmooth R.θ (A := G.P i) (B := G.P (i + 1)) (G.mP i) fun h g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ)

  dn : ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (neg (G.P (i + 1)).V) (G.P i).V Φ →
    LiftsSmooth R.θ (A := G.P (i + 1)) (B := G.P i) (G.mP (i + 1)) fun h g => thetaKO (G.dn i).ω g h Φ

  col : ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ →
    LiftsSmooth R.θ (A := G.Xp j) (B := G.Xp (j + 1)) (G.measX j) fun h g => thetaKO (G.col t j).ω g h Φ

end Grid

def LiftsCuspidalAt (D : D7) : Prop :=
  Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GridPre R),
    RowBase R → G.Is → CuspAlong G

def LiftsCuspidal : Prop := ∀ D : D7, LiftsCuspidalAt D

def LiftsCuspidalSmoothAt (D : D7) : Prop :=
  Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GridPre R),
    RowBase R → G.Is → CuspAlongSmooth G

theorem LiftsMult.exists_linear {θ : InfFam D} {A B : Node D} {P : Type} {m : A.MeasDat} {K : P → GA D B.V → GA D A.V → ℂ}
    {It : P → SmT A.M → SmT B.M} (H : LiftsMult θ m K It) :
    ∃ io : A.Cusp θ →ₗ[ℂ] B.Cusp θ, ∀ (F : A.Cusp θ) p v h,
      IntegrableOn (fun g => K p h g * F.1 v g) m.fd m.ν ∧ ∫ g in m.fd, K p h g * F.1 v g ∂m.ν = (io F).1 (It p v) h := by
  classical
  let b := Module.Free.chooseBasis ℂ (A.Cusp θ)
  choose F' hF'mem hF' using fun i => H (b i).1 (b i).2
  let io := b.constr ℂ (fun i => (⟨F' i, hF'mem i⟩ : B.Cusp θ))
  refine ⟨io, fun F => ?_⟩
  have hF : F ∈ Submodule.span ℂ (Set.range b) := by rw [b.span_eq]; trivial
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    intro p v h
    simp only [io, b.constr_basis]
    exact hF' i p v h
  | zero =>
    intro p v h
    simp
  | add x y _ _ hx hy =>
    intro p v h
    obtain ⟨hx1, hx2⟩ := hx p v h
    obtain ⟨hy1, hy2⟩ := hy p v h
    have e : (fun g => K p h g * (x + y).1 v g) = fun g => K p h g * x.1 v g + K p h g * y.1 v g := by
      funext g
      simp [mul_add]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact hx1.add hy1
    · rw [e, integral_add hx1 hy1, hx2, hy2, map_add (f := _)]
      simp
  | smul c x _ hx =>
    intro p v h
    obtain ⟨hx1, hx2⟩ := hx p v h
    have e : (fun g => K p h g * (c • x).1 v g) = fun g => c * (K p h g * x.1 v g) := by
      funext g
      simp [mul_left_comm]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact hx1.const_mul c
    · have h3 : (io (c • x)).1 (It p v) h = c * (io x).1 (It p v) h := by
        simp only [map_smul, Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      rw [h3, e, integral_const_mul, hx2]

section

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem cuspAlong_iff_hasLifts (G : GridPre R) : CuspAlong G ↔ G.HasLifts := by
  constructor
  · intro hc
    refine { X := ?_, th := ?_, col := ?_, dn := ?_, up := ?_ }
    · intro t i j hi hj f hf
      obtain ⟨io, hio⟩ := (hc.X t i j hi hj f hf).exists_linear
      exact ⟨io, Lift.IsIo.mk (fun F φ v g => (hio F φ v g).1) (fun F φ v g => (hio F φ v g).2)⟩
    · intro t i j hi hj f hf
      obtain ⟨io, hio⟩ := (hc.th t i j hi hj f hf).exists_linear
      exact ⟨io, Lift.IsIo.mk (fun F φ v g => (hio F φ v g).1) (fun F φ v g => (hio F φ v g).2)⟩
    · intro t j hj f hf
      obtain ⟨io, hio⟩ := (hc.col t j hj f hf).exists_linear
      exact ⟨io, Lift.IsIo.mk (fun F φ v g => (hio F φ v g).1) (fun F φ v g => (hio F φ v g).2)⟩
    · intro i hi f hf
      obtain ⟨io, hio⟩ := (hc.dn i hi f hf).exists_linear
      exact ⟨io, Lift.IsIo.mk (fun F φ v g => (hio F φ v g).1) (fun F φ v g => (hio F φ v g).2)⟩
    · intro i hi f hf
      obtain ⟨io, hio⟩ := (hc.up i hi f hf).exists_linear
      exact ⟨io, Lift.IsIoUp.mk (fun F φ v g => (hio F φ v g).1) (fun F φ v g => (hio F φ v g).2)⟩
  · intro hl
    refine { X := ?_, th := ?_, up := ?_, dn := ?_, col := ?_ }
    · intro t i j hi hj f hf F hF
      obtain ⟨io, hio⟩ := hl.X t i j hi hj f hf
      exact ⟨(io ⟨F, hF⟩).1, (io ⟨F, hF⟩).2, fun p v h =>
        ⟨Lift.IsIo.integ hio ⟨F, hF⟩ p v h, Lift.IsIo.eq hio ⟨F, hF⟩ p v h⟩⟩
    · intro t i j hi hj f hf F hF
      obtain ⟨io, hio⟩ := hl.th t i j hi hj f hf
      exact ⟨(io ⟨F, hF⟩).1, (io ⟨F, hF⟩).2, fun p v h =>
        ⟨Lift.IsIo.integ hio ⟨F, hF⟩ p v h, Lift.IsIo.eq hio ⟨F, hF⟩ p v h⟩⟩
    · intro i hi f hf F hF
      obtain ⟨io, hio⟩ := hl.up i hi f hf
      exact ⟨(io ⟨F, hF⟩).1, (io ⟨F, hF⟩).2, fun p v h =>
        ⟨Lift.IsIoUp.integ hio ⟨F, hF⟩ p v h, Lift.IsIoUp.eq hio ⟨F, hF⟩ p v h⟩⟩
    · intro i hi f hf F hF
      obtain ⟨io, hio⟩ := hl.dn i hi f hf
      exact ⟨(io ⟨F, hF⟩).1, (io ⟨F, hF⟩).2, fun p v h =>
        ⟨Lift.IsIo.integ hio ⟨F, hF⟩ p v h, Lift.IsIo.eq hio ⟨F, hF⟩ p v h⟩⟩
    · intro t j hj f hf F hF
      obtain ⟨io, hio⟩ := hl.col t j hj f hf
      exact ⟨(io ⟨F, hF⟩).1, (io ⟨F, hF⟩).2, fun p v h =>
        ⟨Lift.IsIo.integ hio ⟨F, hF⟩ p v h, Lift.IsIo.eq hio ⟨F, hF⟩ p v h⟩⟩

end

end GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

open GlobalTheory.Grid

variable {D : D7}

def InId (I : Ideal (𝓞 D.host.E)) (z : Lev.EAf D) : Prop :=
  ∃ h : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, (⟨z, h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ idS D.host.F I

def IsUnitDet (e : AE D) {k : ℕ} (N : Matrix (Fin k) (Fin k) (Lev.EAf D)) (x : (AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧ toEAf D (x : AE D) = 1 - toEAf D e + toEAf D e * N.det ∧
    toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E


open Classical in
def unitChar (ν : (AE D)ˣ →* Circle) (e : AE D) {k : ℕ} (N : Matrix (Fin k) (Fin k) (Lev.EAf D)) : ℂ :=
  if h : ∃ x, IsUnitDet e N x then (((ν h.choose)⁻¹ : Circle) : ℂ) else 0

def rightBlock {κ : Type} [Zero κ] {k d : ℕ} (a : ℕ) (Y : Matrix (Fin k) (Fin d) κ) : Matrix (Fin k) (Fin k) κ :=
  fun i j => if h : a + j.1 < d then Y i ⟨a + j.1, h⟩ else 0


open Classical in
def stdFst (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (A WW : HSp D) (βA : GL (Fin A.rank) (Lev.EAf D))
    (βW : GL (Fin WW.rank) (Lev.EAf D)) (x : WO A WW) : ℂ :=
  if IsHalf e x ∧ IsIntM (frMapO A WW βA βW x) ∧ ∀ i j, A.rank ≤ i.1 → InId I (frMapO A WW βA βW x i j) then
    unitChar ν e (topL A.rank (frMapO A WW βA βW x))
  else 0

def dualCoord (A' WW : HSp D) (βA' : GL (Fin A'.rank) (Lev.EAf D)) (βW : GL (Fin WW.rank) (Lev.EAf D)) (y : WO A' WW) :
    Matrix (Fin A'.rank) (Fin WW.rank) (Lev.EAf D) :=
  eToEAf D D.host.xi0 • frMapAdj A' WW βA' βW y


open Classical in
def stdSnd (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (A' WW : HSp D)
    (βA' : GL (Fin A'.rank) (Lev.EAf D)) (βW : GL (Fin WW.rank) (Lev.EAf D)) (y : WO A' WW) : ℂ :=
  if IsHalf (cA D e) y ∧ IsIntM (dualCoord A' WW βA' βW y) ∧ ∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW y i j) then
    unitChar ν e (rightBlock a (dualCoord A' WW βA' βW y))
  else 0

structure Rig (V : HSp D) where

  Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

  β : GL (Fin V.rank) (Lev.EAf D)

  s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ

  B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ

def Rig.Is {V : HSp D} (r : Rig V) : Prop :=
  IsSelfDualC V r.Λ ∧ Formalism.L2.DIV.IsFrame r.β r.Λ ∧
    ∀ τ, IsCartanInv (gramAt D V τ) (r.s τ) ∧ ∃ p, IsONBasis (gramAt D V τ) (r.s τ) (r.B τ) p

def Rig.IsStd {V : HSp D} (r : Rig V) : Prop :=
  V.gram = 1 ∧ (∀ y, y ∈ r.Λ ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i) ∧ ∀ τ, r.s τ = 1 ∧ r.B τ = 1


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure Tri (T : Type) (A A' WW : HSp D) where

  rA : Rig A

  rA' : Rig A'

  rW : Rig WW

  ω : T → WRep A WW

  ω' : T → WRep A' WW

  vac : WO A WW → ℂ

  vac' : WO A' WW → ℂ

  e : T → AE D

  c : T → Pl D.host.E → ℕ

  f : T → WO A WW → ℂ

  f' : T → WO A' WW → ℂ

  m : Measure (GA D A)

  fd : Set (GA D A)

  m' : Measure (GA D A')

  fd' : Set (GA D A')

namespace Tri

variable {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)

def ideal (S : T → Finset (Pl D.host.E)) (t : T) : Ideal (𝓞 D.host.E) := ∏ w ∈ S t, w.asIdeal ^ X.c t w

structure Is (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (Pl D.host.E)) : Prop where

  rank : A.rank + A'.rank = WW.rank

  rigA : X.rA.Is

  rigA' : X.rA'.Is

  rigW : X.rW.Is

  weil : ∀ t, IsWeil ψ true A WW (β t) (β t / α t) (X.ω t)

  weil' : ∀ t, IsWeil ψ false A' WW (α t) (α t / β t) (X.ω' t)

  isVac : IsVacO ψ θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.Λ X.rW.Λ X.vac

  isVac' : IsVacO ψ θ A' WW X.rA'.s X.rW.s X.rA'.Λ X.rW.Λ X.vac'

  idem : ∀ t, IsIdemSum (X.e t) (S t)

  expo : ∀ t, ∀ w ∈ S t, GlobalTheory.CMVal.ExpAt (νH t) w (X.c t w)

  fst : ∀ t, IsThetaAt ψ (symplO (neg A) WW) (heisO ψ (neg A) WW) (X.e t) (latO (neg A) WW X.rA.Λ X.rW.Λ fun _ => True) 1 X.vac
    (stdFst (α t / β t) (X.e t) (X.ideal S t) A WW X.rA.β X.rW.β) (X.f t)

  snd : ∀ t, IsThetaAt ψ (symplO A' WW) (heisO ψ A' WW) (cA D (X.e t)) (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) 1 X.vac'
    (stdSnd (α t / β t) (X.e t) (X.ideal S t) A.rank A' WW X.rA'.β X.rW.β) (X.f' t)

  meas : X.m.IsHaarMeasure ∧ IsFundamentalDomain (GQ A) X.fd X.m

  meas' : X.m'.IsHaarMeasure ∧ IsFundamentalDomain (GQ A') X.fd' X.m'

def ker (t : T) (P : PolF D WW.rank A.rank) (h : GA D WW) (g : GA D A) : ℂ :=
  thetaKO (X.ω t) g h (pureTensorO ψ θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P)

def ker' (t : T) (P : PolF D WW.rank A'.rank) (h : GA D WW) (g : GA D A') : ℂ :=
  thetaKO (X.ω' t) g h (pureTensorO ψ θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) P)

def I (t : T) (P : PolF D WW.rank A.rank) (h : GA D WW) : ℂ := ∫ g in X.fd, X.ker ψ θ t P h g ∂X.m

def I' (t : T) (P : PolF D WW.rank A'.rank) (h : GA D WW) : ℂ := ∫ g in X.fd', X.ker' ψ θ t P h g ∂X.m'

def IsConst (c : T → ℂ) : Prop :=
  (∃ t, c t ≠ 0) ∧ ∃ (P : PolF D WW.rank A.rank) (P' : PolF D WW.rank A'.rank), ∀ t,
    (∀ h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m ∧ IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') ∧
    (∃ h, X.I' ψ θ t P' h ≠ 0) ∧ ∀ h, X.I ψ θ t P h = c t * X.I' ψ θ t P' h

def RationalSums {L : Type} [Field L] (σ : L →+* ℂ) : Prop :=
  ∃ Ω Ω' : ℂ, Ω ≠ 0 ∧ Ω' ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW,
    (∀ k, IntegrableOn (X.ker ψ θ t (MvPolynomial.monomial k 1) h) X.fd X.m ∧
      ∃ z : L, X.I ψ θ t (MvPolynomial.monomial k 1) h = Ω * σ z) ∧
    ∀ k, IntegrableOn (X.ker' ψ θ t (MvPolynomial.monomial k 1) h) X.fd' X.m' ∧
      ∃ z : L, X.I' ψ θ t (MvPolynomial.monomial k 1) h = Ω' * σ z

end Tri

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {Fam : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D Fam Ks} (G : GridPre R)

def alpha (R : RealDat D Fam Ks) (i j : Fin D.R.m) (t : T) : (AE D)ˣ →* Circle :=
  R.toLevCh.mu t (j.1 + 1) * R.eta ^ (rkV D i j % 2)

def beta (i j : Fin D.R.m) (_ : T) : (AE D)ˣ →* Circle := G.chi (D.R.m - i) * R.eta ^ (rkV D i j % 2)

def nuH (i j : Fin D.R.m) (t : T) : Formalism.L2.Host.HChar D.host.E := R.C.mu0 j * R.xiH t / G.chiH (D.R.m - i)


open Classical in
def places (t : T) : Finset (Pl D.host.E) := G.toPlaceDat.W R.Pg ∪ R.Q t

def IsSum (N₁ N₂ : Node D) (WW : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)) : Prop :=
  N₁.V.rank + N₂.V.rank = WW.rank ∧
    ∃ (ι₁ : N₁.V.V →ₗ[D.host.E] WW.V) (ι₂ : N₂.V.V →ₗ[D.host.E] WW.V),
      Formalism.BasicNotions.HSpace.IsIsomEmb N₁.V WW ι₁ ∧ Formalism.BasicNotions.HSpace.IsIsomEmb N₂.V WW ι₂ ∧ (∀ x y, WW.hD (ι₁ x) (ι₂ y) = 0) ∧
      ∀ z : WW.V, WW.frame.equivFun z ∈ Λ ↔ ∃ x y, N₁.InLat x ∧ N₂.InLat y ∧ z = ι₁ x + ι₂ y

def BottomInField (i j : Fin D.R.m) : Prop :=
  ∃ (A A' WW : HSp D) (X : Tri T A A' WW),
    A.rank + 2 * ((D.R.m - (j + 1)) / 2) = rkV D (i + 1) (j + 1) ∧ A'.rank + 2 * ((D.R.m - j) / 2) = rkV D i j ∧
    X.rA.IsStd ∧ X.rA'.IsStd ∧ X.rW.IsStd ∧ X.Is R.ψ R.θ (alpha R i j) (beta G i j) (nuH G i j) (places G) ∧
    X.RationalSums R.ψ R.θ D.what₂.embLL

def LRatiosInField (i j : Fin D.R.m) : Prop :=
  ∀ (t : T) (L L₀ : ℂ → ℂ), GlobalTheory.CMVal.IsHeckeL (nuH G i j t) L → GlobalTheory.CMVal.IsHeckeL (nuH G i j Fam.μ0) L₀ →
    ∀ s : ℕ, 1 ≤ s → s ≤ bigN D + 1 → ∃ ρ : D.what₂.LL, L s = D.what₂.embLL ρ * L₀ s

structure FieldCond : Prop where

  base : Formalism.L2.Host.ValLL D R.C

  aux : G.ValuesInField

  twist : ∀ t, (R.xiH t).ValuesIn 0 D.what₂.embLL

  ratios : ∀ i j, LRatiosInField G i j

  bottom : ∀ i j, BottomInField G i j

end GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints

open GlobalTheory.Grid GlobalTheory.Doubling

variable {D : D7}

def adj (S T : HSp D) (y : WO S T) : WO T S :=
  HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D)) ((y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose)
    (T.gram.map (incA D))

def blkL (M V V₁ : HSp D) (z : WO M (hsum V V₁)) : WO M V := fun a b => z (Fin.castAdd V₁.rank a) b

def blkR (M V V₁ : HSp D) (z : WO M (hsum V V₁)) : WO M V₁ := fun a b => z (Fin.natAdd V.rank a) b

def ten (M V V₁ : HSp D) : (WO M V → ℂ) →ₗ[ℂ] (WO V₁ M → ℂ) →ₗ[ℂ] (WO M (hsum V V₁) → ℂ) :=
  LinearMap.mk₂ ℂ (fun φ φ' z => φ (blkL M V V₁ z) * φ' (adj M V₁ (blkR M V V₁ z)))
    (fun _ _ _ => funext fun _ => add_mul _ _ _) (fun _ _ _ => funext fun _ => mul_assoc _ _ _)
    (fun _ _ _ => funext fun _ => mul_add _ _ _) (fun _ _ _ => funext fun _ => mul_left_comm _ _ _)

section Route

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (V M V₁ : Node D)

abbrev Pair : Type := (WO M.V V.V → ℂ) × (WO V₁.V M.V → ℂ)

def IsFinPair (f : Pair V M V₁) : Prop := IsFinVec ψ θ ε M V f.1 ∧ IsFinVec ψ θ (!ε) V₁ M f.2

variable {V M V₁}

def route (a : ArrS M V) (b : ArrS V₁ M) (mV : V.MeasDat) (mM : M.MeasDat) {n : ℕ} (Φ : Fin n → Pair V M V₁)
    (F : GA D V.V → ℂ) : GA D V₁.V → ℂ :=
  ∑ k, b.int mM (Φ k).2 (a.int mV (Φ k).1 F)

end Route

section Quot

variable (θ : InfFam D)

def IsDer (X : HSp D) {Z : Type} (ρ : GA D X → Module.End ℂ (Z → ℂ)) (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ)
    (Φ Φ' : Z → ℂ) : Prop :=
  ∀ z, HasDerivAt (fun t : ℝ => ρ (oneP θ X τ Y t) Φ z) (Φ' z) 0

def IsStable (X : HSp D) {Z : Type} (ρ : GA D X → Module.End ℂ (Z → ℂ)) (S : Submodule ℂ (Z → ℂ)) : Prop :=
  (∀ g ∈ GfC X, ∀ Φ ∈ S, ρ g Φ ∈ S) ∧ ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ S, ∃ Φ' ∈ S, IsDer θ X ρ τ Y Φ Φ'

def IsIrred (X : HSp D) (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi)
    (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi) : Prop :=
  Nontrivial Pi ∧ ∀ N : Submodule ℂ Pi, (∀ g ∈ GfC X, ∀ x ∈ N, rf g x ∈ N) → (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ N, rl τ Y x ∈ N) →
    N = ⊥ ∨ N = ⊤

structure IsCoinvMap {M X : HSp D} (ω : WRep M X) (S : Submodule ℂ (WO M X → ℂ)) (Pi : ModuleCat.{0} ℂ)
    (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO M X → ℂ) →ₗ[ℂ] Pi) : Prop where

  stabM : IsStable θ M (fun g => ω (g, 1)) S

  stabX : IsStable θ X (fun h => ω (1, h)) S

  onto : S.map p = ⊤

  invf : ∀ g ∈ GfC M, ∀ Φ ∈ S, p (ω (g, 1) Φ) = p Φ

  invl : ∀ τ, ∀ Y ∈ lieAt M τ, ∀ Φ ∈ S, ∀ Φ' ∈ S, IsDer θ M (fun g => ω (g, 1)) τ Y Φ Φ' → p Φ' = 0

  eqf : ∀ h ∈ GfC X, ∀ Φ ∈ S, p (ω (1, h) Φ) = rf h (p Φ)

  eql : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ S, ∀ Φ' ∈ S, IsDer θ X (fun h => ω (1, h)) τ Y Φ Φ' → p Φ' = rl τ Y (p Φ)

end Quot

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridDat R)


variable (R) in
def al (t : T) (i j : ℕ) : (AE D)ˣ →* Circle := R.toLevCh.mu t (j + 1) * R.eta ^ (rkV D i j % 2)

def be (i j : ℕ) : (AE D)ˣ →* Circle := G.chi (D.R.m - i) * R.eta ^ (rkV D i j % 2)

def routeA (t : T) (i j : ℕ) {n : ℕ} (Φ : Fin n → Pair (G.V i (j + 1)) (G.V (i + 1) (j + 1)) (G.V (i + 1) j))
    (F : GA D (G.V i (j + 1)).V → ℂ) : GA D (G.V (i + 1) j).V → ℂ :=
  route (G.X i (j + 1)) (G.th t (i + 1) j) (G.meas t i (j + 1)) (G.meas t (i + 1) (j + 1)) Φ F

end GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints

end
end
