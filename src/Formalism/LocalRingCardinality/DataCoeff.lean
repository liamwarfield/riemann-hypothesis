module

public import Formalism.LocalRingCardinality.Params
public import Formalism.GradedWeylDivisibility.StatementB
public import Formalism.SatakeDualWeyl.StatementB
public import Formalism.ThetaLiftIndependence.Statement

@[expose] public section

section -- merged from Formalism.LocalRingCardinality.DataCoeff
namespace Formalism.BasicNotions

open MvPolynomial

noncomputable section

structure DomWeight (N : ℕ) where
  w : Fin N → ℤ
  anti : Antitone w

namespace DomWeight

variable {N : ℕ}

def detShift (lam : DomWeight N) : ℤ := if h : 0 < N then lam.w ⟨N - 1, by omega⟩ else 0

def natW (lam : DomWeight N) : Fin N → ℕ := fun i => (lam.w i - lam.detShift).toNat

def dual (lam : DomWeight N) : DomWeight N where
  w := fun i => -lam.w (Fin.rev i)
  anti := by
    intro i j hij
    have h1 : Fin.rev j ≤ Fin.rev i := Fin.rev_le_rev.mpr hij
    have h2 := lam.anti h1
    simp only
    omega

def spread (lam : DomWeight N) : ℤ :=
  if h : 0 < N then lam.w ⟨0, h⟩ - lam.w ⟨N - 1, by omega⟩ + N else 0

end DomWeight

def rhoVec (N : ℕ) (i : Fin N) : ℚ := ((N : ℚ) - 1) / 2 - (i : ℚ)

def hcToWeightQ {N : ℕ} (hc : Fin N → ℚ) : Fin N → ℚ := fun i => hc i - rhoVec N i

def IsIntegralHC {N : ℕ} (hc : Fin N → ℚ) : Prop := ∀ i, ∃ z : ℤ, hcToWeightQ hc i = z

section Modules

variable (R : Type) [CommRing R] (N : ℕ)

def nablaSq (lam : DomWeight N) : Submodule R (MvPolynomial (Fin N × Fin N) R) :=
  Formalism.GradedWeylDivisibility.dualWeyl R N N lam.natW

def delSq (lam : DomWeight N) : Submodule R (MvPolynomial (Fin N × Fin N) R) :=
  Formalism.GradedWeylDivisibility.weyl R N N le_rfl lam.natW

def extremal (lam : DomWeight N) : MvPolynomial (Fin N × Fin N) R :=
  Formalism.GradedWeylDivisibility.hw R le_rfl lam.natW

def detPow (g : GL (Fin N) R) (c : ℤ) : R :=
  ((Matrix.GeneralLinearGroup.det g ^ c : Rˣ) : R)

def sqAct (lam : DomWeight N) (g : GL (Fin N) R) (f : MvPolynomial (Fin N × Fin N) R) :
    MvPolynomial (Fin N × Fin N) R :=
  detPow R N g lam.detShift • Formalism.GradedWeylDivisibility.rowAct R (n := N) (g : Matrix (Fin N) (Fin N) R).transpose f

def roundAct (lam : DomWeight N) (g : GL (Fin N) R) (f : MvPolynomial (Fin N × Fin N) R) :
    MvPolynomial (Fin N × Fin N) R :=
  detPow R N g (-lam.detShift) • Formalism.UG.dwAct R N N g f

def inside₂ (g : GL (Fin N) R) : GL (Fin N) R where
  val := ((g⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R).transpose
  inv := (g : Matrix (Fin N) (Fin N) R).transpose
  val_inv := by rw [← Matrix.transpose_mul]; simp
  inv_val := by rw [← Matrix.transpose_mul]; simp

def diagGL (t : Fin N → Rˣ) : GL (Fin N) R where
  val := Matrix.diagonal fun a => (t a : R)
  inv := Matrix.diagonal fun a => ((t a)⁻¹ : Rˣ)
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

end Modules

noncomputable def normFock {N : ℕ} (lam : DomWeight N) (f g : MvPolynomial (Fin N × Fin N) ℂ) : ℂ :=
  Formalism.REAL.fockF f g / Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)

noncomputable def normFockQ {N : ℕ} (lam : DomWeight N) (f g : MvPolynomial (Fin N × Fin N) ℚ) : ℚ :=
  Formalism.GradedWeylDivisibility.fockQ f g / Formalism.GradedWeylDivisibility.fockQ (extremal ℚ N lam) (extremal ℚ N lam)

def FactNatW : Prop := ∀ (N : ℕ) (lam : DomWeight N),
  Antitone lam.natW ∧ (∀ i, ((lam.natW i : ℕ) : ℤ) + lam.detShift = lam.w i) ∧
  (∀ h : 0 < N, lam.natW ⟨N - 1, by omega⟩ = 0)

def bridge_round_square : Prop := ∀ (R : Type) [CommRing R] (N : ℕ) (lam : DomWeight N)
  (g : GL (Fin N) R) (f : MvPolynomial (Fin N × Fin N) R),
  roundAct R N lam g f = sqAct R N lam (inside₂ R N g) f

def FactSqActMul : Prop := ∀ (R : Type) [CommRing R] (N : ℕ) (lam : DomWeight N)
  (g h : GL (Fin N) R) (f : MvPolynomial (Fin N × Fin N) R),
  sqAct R N lam (g * h) f = sqAct R N lam g (sqAct R N lam h f) ∧
  roundAct R N lam (g * h) f = roundAct R N lam g (roundAct R N lam h f)

def FactSqStable : Prop := ∀ (R : Type) [CommRing R] (N : ℕ) (lam : DomWeight N)
  (g : GL (Fin N) R),
  (∀ f ∈ nablaSq R N lam, sqAct R N lam g f ∈ nablaSq R N lam) ∧
  (∀ f ∈ delSq R N lam, sqAct R N lam g f ∈ delSq R N lam)

def FactSqHighestWeight : Prop := ∀ (R : Type) [CommRing R] (N : ℕ) (lam : DomWeight N),
  (∀ t : Fin N → Rˣ,
    sqAct R N lam (diagGL R N t) (extremal R N lam) =
      ((∏ a, (t a) ^ (lam.w a) : Rˣ) : R) • extremal R N lam) ∧
  (∀ g : GL (Fin N) R, (g : Matrix (Fin N) (Fin N) R).BlockTriangular id →
    (∀ a, (g : Matrix (Fin N) (Fin N) R) a a = 1) →
    sqAct R N lam g (extremal R N lam) = extremal R N lam)

def bridge_normFock_extremal : Prop := ∀ (N : ℕ) (lam : DomWeight N),
  normFock lam (extremal ℂ N lam) (extremal ℂ N lam) = 1

def FactNormFockUnitary : Prop := ∀ (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ),
  (g : Matrix (Fin N) (Fin N) ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ →
  ∀ f h : MvPolynomial (Fin N × Fin N) ℂ,
    normFock lam (roundAct ℂ N lam g f) (roundAct ℂ N lam g h) = normFock lam f h

def FactDelDualNabla : Prop := ∀ (N : ℕ) (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℚ),
  f ∈ nablaSq ℚ N lam →
  ((∀ g ∈ nablaSq ℤ N lam, ∃ z : ℤ, normFockQ lam f (map (Int.castRingHom ℚ) g) = z) ↔
    ∃ f₀ ∈ delSq ℤ N lam, map (Int.castRingHom ℚ) f₀ = f)

def NablaMemDeltaLocallyAtLargePrime : Prop := ∀ (N : ℕ) (lam : DomWeight N) (p : ℕ), p.Prime → lam.spread < p →
  ∀ f ∈ nablaSq ℤ N lam, ∃ c : ℤ, ¬ (p : ℤ) ∣ c ∧ c • f ∈ delSq ℤ N lam

def bridge_hc_rho : Prop := ∀ (N : ℕ) (hc : Fin N → ℚ), StrictAnti hc → IsIntegralHC hc →
  ∃ lam : DomWeight N, ∀ i, (lam.w i : ℚ) = hcToWeightQ hc i

end

end Formalism.BasicNotions
end

section -- merged from Formalism.LocalRingCardinality.DataKernels
namespace Formalism.BasicNotions

open scoped BigOperators

def mulFun {Y : Type*} (g : Y → ℂ) : (Y → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun φ := fun y => g y * φ y
  map_add' φ ψ := by funext y; simp [mul_add]
  map_smul' c φ := by funext y; simp; ring

structure ColumnChain (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) where

  cls : ℕ → Type
  [clsFin : ∀ i, Fintype (cls i)]

  stab : ∀ i, cls i → Type
  [stabGrp : ∀ i c, Group (stab i c)]
  [stabFin : ∀ i c, Finite (stab i c)]

  DGam : ℕ
  DGam_pos : 0 < DGam
  dvd_DGam : ∀ i, i ≤ R.m → ∀ c, Nat.card (stab i c) ∣ DGam

  Y : ℕ → Type

  de : ∀ i, Y i → ι → ℂ
  de_ne : ∀ i y τ, de i y τ ≠ 0

  rhoDet : ∀ i, cls i → ℂ

  rhoDet' : ∀ i, cls (i + 1) → ℂ

  rho_norm : ∀ i, i < R.m → ∀ c, ‖rhoDet i c‖ = 1
  rho'_norm : ∀ i, i < R.m → ∀ c, ‖rhoDet' i c‖ = 1

  unf : ∀ i, cls i → cls (i + 1) → ((Y i → ℂ) →ₗ[ℂ] (Y (i + 1) → ℂ))

  sSharp : ℕ → ι → ℤ
  sSharp_eq : ∀ (i : ℕ) (h : i < R.m) (τ : ι),
    (sSharp i τ : ℚ) = sExp' R ((hc τ).e ⟨i, h⟩) (i + 1)

  sDiv : ℕ → ι → ℤ
  sDiv_eq : ∀ (i : ℕ) (h : i < R.m) (τ : ι),
    (sDiv i τ : ℚ) = sExp R ((hc τ).e ⟨i, h⟩) (i + 1)

namespace ColumnChain

variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc)

attribute [instance] ColumnChain.clsFin ColumnChain.stabGrp ColumnChain.stabFin

noncomputable def wt (i : ℕ) (c : C.cls i) : ℂ := ((Nat.card (C.stab i c) : ℕ) : ℂ)⁻¹

noncomputable def sharp (i : ℕ) : (C.Y i → ℂ) →ₗ[ℂ] (C.Y i → ℂ) :=
  mulFun (fun y => ∏ τ, (C.de i y τ) ^ (C.sSharp i τ))

noncomputable def divDe (i : ℕ) : (C.Y (i + 1) → ℂ) →ₗ[ℂ] (C.Y (i + 1) → ℂ) :=
  mulFun (fun y' => (∏ τ, (C.de (i + 1) y' τ) ^ (C.sDiv i τ))⁻¹)

noncomputable def Kmap (i : ℕ) (L : C.cls i) (L' : C.cls (i + 1)) :
    (C.Y i → ℂ) →ₗ[ℂ] (C.Y (i + 1) → ℂ) :=
  (C.rhoDet i L * C.rhoDet' i L') • ((C.divDe i).comp ((C.unf i L L').comp (C.sharp i)))

noncomputable def K (i : ℕ) (φ : C.cls i → C.Y i → ℂ) : C.cls (i + 1) → C.Y (i + 1) → ℂ :=
  Formalism.ThetaLiftIndependence.kerOpM (C.wt i) (C.Kmap i) φ

noncomputable def col (φ : C.cls 0 → C.Y 0 → ℂ) : C.cls R.m → C.Y R.m → ℂ :=
  Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap R.m φ

noncomputable def KD : (j : ℕ) → (C.cls (j - 1) → C.Y (j - 1) → ℂ) → C.cls j → C.Y j → ℂ
  | 0, φ => φ
  | j + 1, φ => C.K j φ

end ColumnChain

structure TupleData {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R}
    (C : ColumnChain R ι hc) where
  rhoDet : ∀ i, C.cls i → ℂ
  rhoDet' : ∀ i, C.cls (i + 1) → ℂ
  rho_norm : ∀ i, i < R.m → ∀ c, ‖rhoDet i c‖ = 1
  rho'_norm : ∀ i, i < R.m → ∀ c, ‖rhoDet' i c‖ = 1
  unf : ∀ i, C.cls i → C.cls (i + 1) → ((C.Y i → ℂ) →ₗ[ℂ] (C.Y (i + 1) → ℂ))

namespace ColumnChain

variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R}

def twist (C : ColumnChain R ι hc) (T : TupleData C) : ColumnChain R ι hc :=
  { C with rhoDet := T.rhoDet, rhoDet' := T.rhoDet', rho_norm := T.rho_norm,
           rho'_norm := T.rho'_norm, unf := T.unf }

def ownData (C : ColumnChain R ι hc) : TupleData C :=
  ⟨C.rhoDet, C.rhoDet', C.rho_norm, C.rho'_norm, C.unf⟩

end ColumnChain

structure ColumnsAtT (R : Ranks) {ι : Type} [Fintype ι] {hc : ι → HCParam R}
    (C : ColumnChain R ι hc) where

  T : ℕ
  T_prime : T.Prime

  vT : Type
  [vTFin : Fintype vT]
  card_vT : Fintype.card vT = R.f

  Fv : vT → Type
  [FvField : ∀ v, Field (Fv v)]
  [FvFin : ∀ v, Fintype (Fv v)]
  [FvDec : ∀ v, DecidableEq (Fv v)]

  card_Fv : ∀ v, Fintype.card (Fv v) = T

  psiT : ∀ v, AddChar (Fv v) ℂ
  psiT_ne : ∀ v, psiT v ≠ 1

  rhoT : ∀ v, (Fv v)ˣ →* ((C.cls 0 → C.Y 0 → ℂ) →ₗ[ℂ] (C.cls 0 → C.Y 0 → ℂ))

  Mu0 : Submodule ℂ (C.cls 0 → C.Y 0 → ℂ)
  Mu0_fd : FiniteDimensional ℂ Mu0
  Mu0_stable : ∀ v c, Mu0.map (rhoT v c) ≤ Mu0

  duStar : ℕ
  duStar_pos : 0 < duStar

  Dstar : ℝ
  Dstar_pos : 0 < Dstar

  GamP : ℝ
  one_lt_gammaP : 1 < GamP

namespace ColumnsAtT

variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc}
  (A : ColumnsAtT R C)

attribute [instance] ColumnsAtT.vTFin ColumnsAtT.FvField ColumnsAtT.FvFin ColumnsAtT.FvDec

noncomputable def Nm (v : A.vT) : (C.cls 0 → C.Y 0 → ℂ) →ₗ[ℂ] (C.cls 0 → C.Y 0 → ℂ) :=
  ∑ c : (A.Fv v)ˣ, A.rhoT v c

noncomputable def Mram : Submodule ℂ (C.cls 0 → C.Y 0 → ℂ) :=
  A.Mu0 ⊓ ⨅ v, LinearMap.ker (A.Nm v)

noncomputable def du : ℕ := Module.finrank ℂ A.Mram

noncomputable def Xu : ℝ := (A.Dstar / A.duStar) ^ ((1 : ℝ) / (R.f * R.k))

noncomputable def Tstar : ℝ := A.Xu * A.GamP ^ (-(2 : ℝ) / (R.f * R.k))

end ColumnsAtT

structure PeriodMap (R : Ranks) {ι : Type} [Fintype ι] {hc : ι → HCParam R}
    (C : ColumnChain R ι hc) where

  Mt : Type
  [MtAcg : AddCommGroup Mt]
  [MtMod : Module ℂ Mt]

  Wz : Type
  [WzAcg : AddCommGroup Wz]
  [WzMod : Module ℂ Wz]

  evz : (C.cls R.m → C.Y R.m → ℂ) →ₗ[ℂ] Wz

  Wrow : Type
  [WrowAcg : AddCommGroup Wrow]
  [WrowMod : Module ℂ Wrow]

  lowerMap : Wz →ₗ[ℂ] Wrow

  period : Wrow →ₗ[ℂ] Mt →ₗ[ℂ] ℂ

namespace PeriodMap

variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc}
  (P : PeriodMap R C)

attribute [instance] PeriodMap.MtAcg PeriodMap.MtMod PeriodMap.WzAcg PeriodMap.WzMod
  PeriodMap.WrowAcg PeriodMap.WrowMod

noncomputable def Ptil (ψ : C.cls R.m → C.Y R.m → ℂ) (F : P.Mt) : ℂ :=
  P.period (P.lowerMap (P.evz ψ)) F

noncomputable def PtilCol (φ : C.cls 0 → C.Y 0 → ℂ) (F : P.Mt) : ℂ := P.Ptil (C.col φ) F

end PeriodMap

def FactWtPos : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (C : ColumnChain R ι hc) i c,
    0 < Nat.card (C.stab i c)

def ColumnChain.StabZero {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) : Prop :=
  ∀ c, Subsingleton (C.stab 0 c)

def FactWtZero : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (C : ColumnChain R ι hc), C.StabZero → ∀ c,
    C.wt 0 c = 1

def FactWtInt : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (C : ColumnChain R ι hc) i, i ≤ R.m →
    ∀ c, ∃ z : ℤ, (C.DGam : ℂ) * C.wt i c = z

def bridge_KD_succ : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (C : ColumnChain R ι hc)
    (j : ℕ) (φ : C.cls j → C.Y j → ℂ), C.KD (j + 1) φ = C.K j φ

def bridge_thl_index : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (C : ColumnChain R ι hc)
    (φ : C.cls 0 → C.Y 0 → ℂ) (i : ℕ),
    Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap (i + 1) φ = C.K i (Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap i φ)

def FactSDivSharp : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (C : ColumnChain R ι hc)
    (i : ℕ), i < R.m → ∀ τ, ((C.sDiv i τ - C.sSharp i τ : ℤ) : ℚ) = ((R.t : ℚ) + 1) / 2

def FactEInt : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (_C : ColumnChain R ι hc)
    (j : Fin R.m) (τ : ι), ((hc τ).e j).den = 1

def FactDuLe : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (C : ColumnChain R ι hc)
    (A : ColumnsAtT R C), A.du ≤ (haveI := A.Mu0_fd; Module.finrank ℂ A.Mu0)

def FactGaussRam : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (C : ColumnChain R ι hc)
    (A : ColumnsAtT R C) (v : A.vT) (x : C.cls 0 → C.Y 0 → ℂ), A.Nm v x = 0 →
    Formalism.ThetaLiftIndependence.gaussOp (A.psiT v) (A.rhoT v) (Formalism.ThetaLiftIndependence.gaussOpDual (A.psiT v) (A.rhoT v) x) =
      (Fintype.card (A.Fv v) : ℂ) • x

def bridge_autL_not_column : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V),
    (LinearEquiv.neg K : V ≃ₗ[K] V) ∈ Formalism.ThetaLiftIndependence.autL h L

end Formalism.BasicNotions
end
