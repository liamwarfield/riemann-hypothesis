module

public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied

@[expose] public section

section -- merged from Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Rows

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef

section Ties

variable (D : D7) {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 T : Type} {m : ℕ}
  (A : FamIn D.what₂.LL Gp Pl0 T m)

def rOp (P : Subgroup Gp) (ψ : P →* D.what₂.LLˣ) (t : T) (a : MonoidAlgebra D.what₂.LL Gp) :
    Matrix (Fin (rDim D A P ψ t)) (Fin (rDim D A P ψ t)) D.what₂.LL :=
  (A.fam.R t).S.lvlOp (A.fam.R t).r (A.fam.lvl P ψ).P (A.fam.lvl P ψ).ψ a

def CenTie {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (X : RowSide D EE) (P : Subgroup Gp) (ψ : P →* D.what₂.LLˣ) (eG : Gp ≃* G0g D.nd) (tup : T → D.what₂.Tup)
    (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)) : Prop :=
  ∀ (t : T) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (a : MonoidAlgebra D.what₂.LL Gp),
    (∀ g : Gp, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff (eG g)) →
    ∀ x, X.cen (tup t) z (jA t x) = jA t ((rOp D A P ψ t a).mulVec x)

end Ties

section Place

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def hAt {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (x y : Fin n → K) : ℂ :=
  ∑ i, ∑ j, star (v.embedding (x i)) * v.embedding (H i j) * v.embedding (y j)

def PosAt {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) : Prop :=
  (∀ x y, hAt H v y x = star (hAt H v x y)) ∧ ∀ x, x ≠ 0 → 0 < (hAt H v x x).re

end Place

section Amb

variable (D : D7) {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 T : Type} {m : ℕ}
  (A : FamIn D.what₂.LL Gp Pl0 T m)

structure AmbIds {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (X : RowSide D EE) (Fm : AmbForm D X) (P : Subgroup Gp) (ψ : P →* D.what₂.LLˣ) (tup : T → D.what₂.Tup) where

  eA : ∀ t, DV.Used D (tup t) → (Fin (rDim D A P ψ t) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fm.MtH (tup t)).V

structure AmbTie {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (X : RowSide D EE) (Fm : AmbForm D X) (P : Subgroup Gp) (ψ : P →* D.what₂.LLˣ) (tup : T → D.what₂.Tup)
    (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t))
    (J : AmbIds D A X Fm P ψ tup) : Prop where

  j_eq : ∀ t (h : DV.Used D (tup t)) x, Fm.jAmb (tup t) (J.eA t h x) = jA t x

  lat : ∀ t (h : DV.Used D (tup t)),
    (Fm.MtH (tup t)).L = (rNab D A P ψ t).map (((J.eA t h).toLinearMap).restrictScalars (𝓞 D.what₂.LL))

  metric : ∀ t (h : DV.Used D (tup t)) (v : InfinitePlace D.what₂.LL), PosAt (rH D A P ψ t) v → ∀ x y,
    Formalism.HermitianLatticesTheory.majAt (Fm.MtH (tup t)).b (Fm.MtH (tup t)).X v (J.eA t h x) (J.eA t h y) = hAt (rH D A P ψ t) v x y

end Amb

section MjH

variable (D : D7) {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 T : Type} {m : ℕ}
  (A : FamIn D.what₂.LL Gp Pl0 T m) {P0 : Subgroup Gp} {ψ0 : P0 →* D.what₂.LLˣ} {Zs : DefSub A.fam.amb}

structure MjHIds (Y : DivX D) (S0 : IndefData (A.side P0 ψ0 Zs)) where

  eW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Y.MjH ((i : ℕ) + 1)).V

structure MjHTie (Y : DivX D) (S0 : IndefData (A.side P0 ψ0 Zs))
    (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (J : MjHIds D A Y S0) : Prop where

  j_eq : ∀ (i : Fin m) x, Y.jM ((i : ℕ) + 1) (J.eW i x) = jW i x

  hlat : ∀ i : Fin m, HLatTie (Y.MjH ((i : ℕ) + 1)) (S0.M i) (S0.XW i) (J.eW i)

end MjH

section Joint

variable (D : D7) {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 T : Type}
  (A : FamIn D.what₂.LL Gp Pl0 T D.R.m)

structure BaseDivisionAmbientCompatibility (Y : DivX D) (p0 : BaseLevelRowSide D) (a0 : AmbForm D p0.s)
    (P0 : Subgroup Gp) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup Gp) (ψs : Ps →* D.what₂.LLˣ)
    (Zs : DefSub A.fam.amb) (S0 : IndefData (A.side P0 ψ0 Zs)) (S1 : IndefData (A.side Ps ψs Zs))
    {Dc : DefCols (A.side Ps ψs Zs)} {Sp : SPer Dc} (C : ColData Dc Sp S1)
    (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL))
    (I : DivisionCompatibilityData D A P0 ψ0 Ps ψs Zs S0 S1 p0 Dc)
    (JA : AmbIds D A p0.s a0 P0 ψ0 I.tup) (JM : MjHIds D A Y S0) : Prop where

  div : DivisionCompatible D A P0 ψ0 Ps ψs Zs S0 S1 p0 C NuC I

  amb0 : AmbTie D A p0.s a0 P0 ψ0 I.tup I.jA0 JA

  mjH : MjHTie D A Y S0 I.jW JM

  cen0 : CenTie D A p0.s P0 ψ0 I.eG I.tup I.jA0

end Joint

section Consistency

variable {D : D7} {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 T : Type} {A : FamIn D.what₂.LL Gp Pl0 T D.R.m}
  {Y : DivX D} {p0 : BaseLevelRowSide D} {a0 : AmbForm D p0.s} {P0 : Subgroup Gp} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup Gp}
  {ψs : Ps →* D.what₂.LLˣ} {Zs : DefSub A.fam.amb} {S0 : IndefData (A.side P0 ψ0 Zs)} {S1 : IndefData (A.side Ps ψs Zs)}
  {Dc : DefCols (A.side Ps ψs Zs)} {Sp : SPer Dc} {C : ColData Dc Sp S1}
  {NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)} {I : DivisionCompatibilityData D A P0 ψ0 Ps ψs Zs S0 S1 p0 Dc}
  {JA : AmbIds D A p0.s a0 P0 ψ0 I.tup} {JM : MjHIds D A Y S0}

end Consistency

section Bundle

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
  {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}

structure FiniteGroupFamilyCharacterData (ex : Extra D L hT Gi Gl Kc Y cX) : Type 1 where

  Gp : Type
  [grp : Group Gp]
  [fin : Fintype Gp]

  Pl0 : Type
  T : Type

  A : FamIn D.what₂.LL Gp Pl0 T D.R.m

  P0 : Subgroup Gp
  ψ0 : P0 →* D.what₂.LLˣ
  Ps : Subgroup Gp
  ψs : Ps →* D.what₂.LLˣ

  Zs : DefSub A.fam.amb

  S0 : IndefData (A.side P0 ψ0 Zs)
  S1 : IndefData (A.side Ps ψs Zs)

  Dc : DefCols (A.side Ps ψs Zs)
  Sp : SPer Dc
  C : ColData Dc Sp S1
  NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)

  I : DivisionCompatibilityData D A P0 ψ0 Ps ψs Zs S0 S1 ex.p0 Dc

  JA : AmbIds D A ex.p0.s ex.amb0 P0 ψ0 I.tup

  JM : MjHIds D A Y S0

  tied : BaseDivisionAmbientCompatibility D A Y ex.p0 ex.amb0 P0 ψ0 Ps ψs Zs S0 S1 C NuC I JA JM

attribute [instance] FiniteGroupFamilyCharacterData.grp FiniteGroupFamilyCharacterData.fin

end Bundle

end Formalism.L2.Rows
end
end

section -- merged from Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Rows

open Formalism.BasicNotions Formalism.L2.Host

def muFld (n : ℕ) : Fld := IntermediateField.adjoin ℚ {x : Qb | x ^ n = 1}

def valsOf {E : Type} [Field E] [NumberField E] (ι : Qb →+* ℂ) (s : ℝ) (χ : HChar E) : Set Qb :=
  {x | ∃ v, χ.UnrAt v ∧ ι x = χ.valTw s v}

def valsFld (D : D7) (T : HostTied D) (C : CharFrame D) : Fld :=
  IntermediateField.adjoin ℚ
    ((⋃ j, valsOf T.fr.ι 0 (C.mu0 j)) ∪ valsOf T.fr.ι (1 / 2) C.eta ∪
      valsOf T.fr.ι 0 C.del ∪ valsOf T.fr.ι 0 C.del')

def AbelOver (E' L : Fld) : Prop :=
  E' ≤ L ∧ (∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ E', σ x = x) → ∀ y ∈ L, σ y ∈ L) ∧
    ∀ σ τ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ E', σ x = x) → (∀ x ∈ E', τ x = x) → ∀ y ∈ L, σ (τ y) = τ (σ y)

local instance nfOfFin (L : Fld) [FiniteDimensional ℚ L] : NumberField L := {}

def UnramOverK (d : ℕ) (L : Fld) [FiniteDimensional ℚ L] : Prop :=
  (NumberField.discr L).natAbs = d ^ (Module.finrank ℚ L / 2)

def IsHilbertCF (d : ℕ) (H : Fld) [FiniteDimensional ℚ H] : Prop :=
  AbelOver (Formalism.L2.Host.KQ d) H ∧ UnramOverK d H ∧
    ∀ (H' : Fld) [FiniteDimensional ℚ H'], AbelOver (Formalism.L2.Host.KQ d) H' → UnramOverK d H' → H' ≤ H

structure KsPieces (D : D7) (T : HostTied D) where
  HK : Fld
  rcf : Fld
  M : Fld
  MDel : Fld
  KPs : Fld
  [HK_fin : FiniteDimensional ℚ HK]
  [rcf_fin : FiniteDimensional ℚ rcf]
  [M_fin : FiniteDimensional ℚ M]
  [MDel_fin : FiniteDimensional ℚ MDel]
  [KPs_fin : FiniteDimensional ℚ KPs]

  HK_hilb : IsHilbertCF D.host.d HK

  E_le_rcf : T.fr.j.fieldRange ≤ rcf

  rcf_abel : AbelOver T.fr.j.fieldRange rcf

  rcf_cond : (NumberField.discr rcf).natAbs ∣
    (NumberField.discr D.host.E).natAbs ^ (Module.finrank ℚ rcf / Module.finrank ℚ D.host.E) *
      (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') ^ Module.finrank ℚ rcf

  HK_le_M : HK ≤ M

  M_deg : Module.finrank ℚ M ≤ Module.finrank ℚ HK * Nat.card (GL (Fin 2) (ZMod 12))

  M_ram : ∀ p : ℕ, p.Prime → p ∣ (NumberField.discr M).natAbs → p ∣ 6 * D.host.d

  MDel_gen : ∃ (y : Qb) (h : y ^ 12 ∈ M), y ≠ 0 ∧
    (∃ I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers M)) M,
      FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers M)) (⟨y ^ 12, h⟩ : M) = I ^ 12) ∧
    MDel = M ⊔ IntermediateField.adjoin ℚ {y}

  MDel_ram : ∀ p : ℕ, p.Prime → p ∣ (NumberField.discr MDel).natAbs → p ∣ 6 * D.host.d

  KPs_gen : ∃ S : Fin D.R.m → Finset Qb,
    (∀ j, (S j).card ≤ Nat.log 2 (NumberField.classNumber D.host.E)) ∧
    (∀ j, ∀ y ∈ S j, ∃ n : ℕ, 0 < n ∧ n ∣ NumberField.classNumber D.host.E ∧ y ^ n ∈ T.fr.j.fieldRange) ∧
    KPs = T.fr.j.fieldRange ⊔ muFld (NumberField.classNumber D.host.E) ⊔
      IntermediateField.adjoin ℚ (⋃ j, (S j : Set Qb))

  KPs_ram : ∀ p : ℕ, p.Prime → p ∣ (NumberField.discr KPs).natAbs →
    p ∣ NumberField.classNumber D.host.E * (NumberField.discr D.host.E).natAbs

  M_le_MDel : M ≤ MDel

  E_le_KPs : T.fr.j.fieldRange ≤ KPs

def rootOrders (D : D7) : List ℕ :=
  [Nat.card (G0g D.nd), D.host.g 0 * (D.host.g 0 - 1), D.host.g 1 * (D.host.g 1 - 1), 3 ^ 4, 5 ^ 4]

def KsQ (D : D7) (T : HostTied D) (C : CharFrame D) (P : KsPieces D T) : Fld :=
  T.fr.j.fieldRange ⊔ (⨆ n ∈ rootOrders D, muFld n) ⊔ valsFld D T C ⊔ P.rcf ⊔ P.M ⊔ P.MDel ⊔ P.KPs

def OsQ (K : Fld) : Set Qb := {x | x ∈ K ∧ IsIntegral ℤ x}

end Formalism.L2.Rows
end
end
