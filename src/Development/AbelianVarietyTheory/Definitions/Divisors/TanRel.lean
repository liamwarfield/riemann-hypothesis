module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.LocusEqTopOfDualPow
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsIsoGrCechMapPolyToGamma

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.Ex
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def TanRel (U : UnifPre I D A G) (y : epsR R ⟶ G) (gm : GtPt D.toPre (epsR R)) : Prop :=
  ∀ e : ℕ, ∃ ye : Sp (DualNumber (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left,
    ye ≫ (fstG I e G).left = spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ y.left ∧
    ye ≫ (U.gt e).pG.left = spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ gm.b.left ∧
    ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ye)
      (LB.pullGen D.toPre.P.L _ _ (gm.s χ) (spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1))))))

def GtTan {D₀ : DegPre R} (gm : GtPt D₀ (epsR R)) : Prop :=
  ∃ o : GtPt D₀ (baseOver (Sp R)), o.IsZero ∧ GtPt.IsPull (redE R) gm o

abbrev toF (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] : R →+* F :=
  (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))

def VecAt (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : epsR R ⟶ G)
    (yA : Sp (DualNumber F) ⟶ (TFK (R := R) F ⊗ A.A).left) : Prop :=
  yA ≫ (fst (TFK (R := R) F) A.A).left = spMap (algebraMap F (DualNumber F)) ∧
  yA ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = spMap (dualMap (toF R F)) ≫ y.left

def ArchF (κ : Rule) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (D : DegPre R), D.PsiEven → D.TauBimult →
    ∀ (F : Type) [Field F] [CharZero F] [Algebra (FractionRing R) F] (e : F ≃+* ℂ) (N : NumD F) (ν : NumOf D F N) (g r m k : ℕ),
    1 ≤ g → Odd m → m ^ 2 ∣ k →
    ∀ (β : N.Form k) (ζ : Fˣ) (q : (Fin (2 * g) → ZMod (m ^ 2)) → N.QT (m ^ 2)), QLevel N g (m ^ 2) ζ q →
    ∀ (s : (Fin (2 * g) → ZMod (m ^ 2)) → Fam D F (m ^ 2)), (∀ a, ∃ f, ν.FamV (s a) f ∧ IsEvFam N m (q a) f) →
    ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r)
      (gm : Fin g → GtPt D (TE R F)), Adapted ν vB bX σ gm → ∀ k₀ : F, BKey κ ν vB k₀ →
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      (∀ a j, (Summable fun α => ‖e ((jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2)) * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
        Summable fun α => ‖e ((jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2)) * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map (e : F →+* ℂ).toMonoidHom ζ)))
        (ϑ : _ → ℂ),
        (∀ a j, ϑ a = ∑' α, e ((jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2)) * u ^ (β.be α α / (2 * m ^ 2)).toNat) ∧
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) ϑ
          (fun a j => ∑' α, e ((jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2)) * u ^ (β.be α α / (2 * m ^ 2)).toNat) ∧
        (κ ℂ x₀ : ℂ) = e k₀

def AllV (P : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (IsLocalRing.maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G],
    Unif (IsLocalRing.maximalIdeal V) D A G → Prop) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V))
    (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ U : Unif (IsLocalRing.maximalIdeal V) D A G, P U

def AllVC (P : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (IsLocalRing.maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
    (_ : Unif (IsLocalRing.maximalIdeal V) D A G) {C : Type} [NontriviallyNormedField C] [Algebra (FractionRing V) C]
    {N : NumD C}, NumOf D.toPre C N → Prop) : Prop :=
  AllV fun {V} _ _ _ {D} {_} {_} _ _ U =>
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C →
      ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → P U ν

end GlobalTheory.MBLow

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.IndefR Formalism.IndefR.principalLevelFrame
open scoped TensorProduct

namespace GlobalTheory.StdFrame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostS (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

def tensCastR {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) :
    FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E ≃+* E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2 := by
  subst h
  exact (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E).toRingEquiv

variable {D : D7}

def StdPsi {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : RowPsi V n) : Prop :=
  (∃ (β : Matrix (Fin V.rank) (Fin n) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))
      (β' : Matrix (Fin n) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)),
      β * β' = 1 ∧ β' * β = 1 ∧
      ∀ κ, finMat D.sp.cm.sig V.gram (P.ψ κ) =
        β * ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (tensCastR hF).symm) * β') ∧
  ∀ κ, κ ∈ ReciprocityTheory.Aut.Umax D.host.E n ↔ P.ψ κ ∈ KsphC V ∅

end GlobalTheory.StdFrame

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.Ex Matrix
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Cl

section Classical

variable {g : ℕ}

def cv (M : Fin g → ℤ) : Fin g → ℂ := fun i => (M i : ℂ)

def perV (τ : Matrix (Fin g) (Fin g) ℂ) (M N : Fin g → ℤ) : Fin g → ℂ := cv M + τ *ᵥ cv N

def Half (a : Fin g → ℂ) : Prop := ∀ i, a i = 0 ∨ a i = 1 / 2

def autV (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (M N : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (a ⬝ᵥ cv M - b ⬝ᵥ cv N) - Real.pi * Complex.I * (cv N ⬝ᵥ τ *ᵥ cv N) -
    2 * Real.pi * Complex.I * (cv N ⬝ᵥ z))

def trFac (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (m : ℕ) (M N : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (cv N ⬝ᵥ cv M) + Real.pi * Complex.I * (cv N ⬝ᵥ cv M) / (m : ℂ) ^ 2 +
    2 * Real.pi * Complex.I * (a ⬝ᵥ cv M - b ⬝ᵥ cv N) + 2 * Real.pi * Complex.I * (cv N ⬝ᵥ z) +
    Real.pi * Complex.I * (cv N ⬝ᵥ τ *ᵥ cv N) / (m : ℂ) ^ 2)

def trF (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (m : ℕ) (M N : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  trFac τ a b m M N z * thetaChar τ a b ((m : ℂ) • z + (m : ℂ)⁻¹ • perV τ M N)

def NF (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ)
    (W : Fin g → Fin g → ℂ) : Prop :=
  τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ Half a ∧ Half b ∧ c ≠ 0 ∧ (∀ z, z ∈ u.Λ ↔ ∃ M N, z = perV τ M N) ∧
    u.IsRig x.rig ∧ u.IsFn x.th (fun z => c * thetaChar τ a b z) ∧ ∀ j, u.IsDiff (W j) (x.v (j.cast hg.symm))

def FnT {P : PolAV (Sp ℂ)} (u : HolUnif P.A P.L g) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ))))
    (f : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (i : P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i →
    valR (ptSecT P.A (T := baseOver (Sp ℂ)) (u.ex z)).left ((LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ))).U fun _ => i)
      (t.f fun _ => i) = f z * u.fr i z ^ k

end Classical

structure AB (B : NumB ℂ) (g : ℕ) where

  τ : Matrix (Fin g) (Fin g) ℂ

  a : Fin g → ℂ

  b : Fin g → ℂ

  c : ℂ
  symm : τ.IsSymm
  pos : (τ.map Complex.im).PosDef
  ha : Half a
  hb : Half b
  hc : c ≠ 0

  ex : (Fin g → ℂ) → B.A
  ex_add : ∀ z w, ex (z + w) = ex z * ex w
  onto : Function.Surjective ex
  ker : ∀ z, ex z = 1 ↔ ∃ M N, z = perV τ M N

  fr : (Fin g → ℂ) → ℂˣ
  fr_zero : fr 0 = 1
  fr_per : ∀ M N z, (fr z : ℂ) = autV τ a b M N z * fr (z + perV τ M N)
  th : ∀ z, B.th (ex z) = c * thetaChar τ a b z * fr z

def AB.Cub {B : NumB ℂ} {g : ℕ} (d : AB B g) : Prop := ∀ x y z,
  B.θ (d.ex x) (d.ex y) (d.ex z) * d.fr (x + y) * d.fr (x + z) * d.fr (y + z) = d.fr (x + y + z) * d.fr x * d.fr y * d.fr z

def AB.Sym {B : NumB ℂ} {g : ℕ} (d : AB B g) : Prop := ∀ x, B.σ (d.ex x) * d.fr x = d.fr (-x)

def co {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (χ : X) : Fin r → ℂ := fun l => (bX.repr χ l : ℂ)

structure CD (N : NumD ℂ) (g r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) extends AB N.toNumB g where
  cub : toAB.Cub
  sym : toAB.Sym

  t12 : Matrix (Fin g) (Fin r) ℂ

  t22 : Matrix (Fin r) (Fin r) ℂ

  b2 : Fin r → ℂ
  toricPeriodBlock_isSymm : t22.IsSymm
  hb2 : Half b2
  c_eq : ∀ χ, N.c χ = ex (t12 *ᵥ co bX χ)
  ψ_eq : ∀ χ, (N.ψ χ : ℂ) * fr (t12 *ᵥ co bX χ) =
    Complex.exp (Real.pi * Complex.I * (co bX χ ⬝ᵥ t22 *ᵥ co bX χ) + 2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2))

namespace CD

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

def full (S : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (Matrix.fromBlocks d.τ d.t12 d.t12ᵀ (d.t22 + S)).submatrix σ σ

def aF : Fin g → ℂ := fun j => Sum.elim d.a 0 (σ j)

def bF : Fin g → ℂ := fun j => Sum.elim d.b d.b2 (σ j)

end CD

def zP {g' r g : ℕ} {A : Type} (σ : Fin g ≃ Fin g' ⊕ Fin r) (Z : Fin g → A) : Fin g' → A := fun i => Z (σ.symm (Sum.inl i))

def tP {g' r g : ℕ} {A : Type} (σ : Fin g ≃ Fin g' ⊕ Fin r) (Z : Fin g → A) : Fin r → A := fun l => Z (σ.symm (Sum.inr l))

namespace CD

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

def IsPt (Z : Fin g → ℂ) (h : N.Gt) : Prop :=
  h.b = d.ex (zP σ Z) ∧ ∀ χ, (h.s χ : ℂ) * d.fr (d.t12 *ᵥ co bX χ + zP σ Z) =
    Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ tP σ Z)) * d.fr (d.t12 *ᵥ co bX χ) * d.fr (zP σ Z)

def Rep (k : ℕ) (M Nn : Fin g → ℤ) (p : N.QT k) : Prop :=
  p.1.1.toAdd = ∑ l, tP σ Nn l • bX l ∧ d.IsPt σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn) p.1.2

def fj (S : Matrix (Fin r) (Fin r) ℂ) (χ : N.X) (Z : Fin g → ℂ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (co bX χ ⬝ᵥ (d.t22 + S) *ᵥ co bX χ) +
    2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ (tP σ Z + d.b2))) * thetaChar d.τ d.a d.b (zP σ Z + d.t12 *ᵥ co bX χ)

def term (S : Matrix (Fin r) (Fin r) ℂ) (m : ℕ) (M Nn : Fin g → ℤ) (χ : N.X) (Z : Fin g → ℂ) : ℂ :=
  trFac (d.full σ S) (d.aF σ) (d.bF σ) m M Nn Z * d.fj σ S χ ((m : ℂ) • Z + (m : ℂ)⁻¹ • perV (d.full σ S) M Nn)

end CD

def bmat {N : NumD ℂ} {r k : ℕ} (bX : Module.Basis (Fin r) ℤ N.X) (β : N.Form k) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun l l' => (β.be (bX l) (bX l') : ℂ)

section Geo

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

def ptB (ν : NumOf D ℂ N) (d : AB N.toNumB g) (z : Fin g → ℂ) : Sp ℂ ⟶ (DegPre.BF D ℂ).left :=
  (lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z))).left

def IsD (ν : NumOf D ℂ N) (d : AB N.toNumB g) (W : Fin g → ℂ) (b : TE R ℂ ⟶ D.P.A) : Prop :=
  ∀ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)), ⊤ ≤ ptB ν d 0 ⁻¹ᵁ U →
    valR (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left U f =
      TrivSqZeroExt.inl (valF (ptB ν d 0) U f) + TrivSqZeroExt.inr (fderiv ℂ (fun z => valF (ptB ν d z) U f) 0 W)

structure Geo (ν : NumOf D ℂ N) (d : AB N.toNumB g) where

  frG : D.P.L.ι → (Fin g → ℂ) → ℂ
  hol : ∀ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)), IsOpen {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun z => valF (ptB ν d z) U f) {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U}
  fr_hol : ∀ i, DifferentiableOn ℂ (frG i) {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ D.P.L.U i}
  fr_compat : ∀ i j z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ (D.P.L.U i ⊓ D.P.L.U j) →
    frG i z = valF (ν.eA (d.ex z)).left (D.P.L.U i ⊓ D.P.L.U j) (D.P.L.g i j).val * frG j z
  fr_eq : ∀ z, (d.fr z : ℂ) * ν.rg = frG (ν.J (ν.eA (d.ex z)).left) z
  dif : ∀ b : TE R ℂ ⟶ D.P.A, redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left → ∃ W, IsD ν d W b

def KeyOK (κ : Rule) (ν : NumOf D ℂ N) (d : AB N.toNumB D.P.g) : Prop :=
  ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (b : Fin D.P.g → (TE R ℂ ⟶ D.P.A)) (MB : Matrix (Fin D.P.g) (Fin D.P.g) ℂ) (k₀ : ℂ),
    IsLieBasis vB → (∀ i, (b i).left =
      spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ (vB i).left) →
    (∀ i, IsD ν d ((2 * Real.pi * Complex.I : ℂ)⁻¹ • MB i) (b i)) → BKey κ ν vB k₀ → MB.det ≠ 0 ∧ k₀ * d.c ^ 8 = MB.det ^ 4

end Geo

def AllC (P : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ},
    NumOf D ℂ N → Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (D : DegPre R), D.PsiEven → D.TauBimult →
    ∀ [Algebra (FractionRing R) ℂ] (N : NumD ℂ) (ν : NumOf D ℂ N), P ν

def AllCD (P : ∀ {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X}, CD N g' r bX → (Fin g ≃ Fin g' ⊕ Fin r) → Prop) :
    Prop :=
  ∀ (N : NumD ℂ) (g' r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r), P d σ

end GlobalTheory.MBLow.Cl

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Points GlobalTheory.Twist GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isStandardSmooth_mvPolynomial (R σ : Type) [CommRing R] [Finite σ] :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card σ) R (MvPolynomial σ R) := by
  letI : IsEmpty Empty := ⟨Empty.elim⟩
  let P₀ : Algebra.Presentation R (MvPolynomial σ R) σ Empty :=
    { __ := Algebra.Generators.mvPolynomial R σ
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation R (MvPolynomial σ R) σ Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation R (MvPolynomial σ R) σ Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  exact P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])

theorem smoothOfRelativeDimension_pspace (R : Type) [CommRing R] (M : ℕ) :
    SmoothOfRelativeDimension M (PSpace.str R M) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} M)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension M))
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} M) (chartCover R M)
    fun (i : Fin (M + 1)) => ?_
  change SmoothOfRelativeDimension M (chartι R M i ≫ _)
  rw [chartι_str]
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension M)).2 ?_
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  have h := isStandardSmooth_mvPolynomial R {j : Fin (M + 1) // j ≠ i}
  rw [show Nat.card {j : Fin (M + 1) // j ≠ i} = M by simp] at h
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap M).2 h

variable (k : Type) [Field k] (M : ℕ)

theorem geometricallyConnected_pspace : GeometricallyConnected (PSpace.str k M) :=
  ⟨geometrically_iff_of_commRing.2 fun K _ _ _ _ _ h =>
    have e := (isPullback_baseChange M (algebraMap k K)).isoIsPullback _ _ h
    e.hom.homeomorph.surjective.connectedSpace e.hom.continuous⟩

abbrev projSys : LinSys k where
  Y := PSpace k M
  str := PSpace.str k M
  D := M
  L := O1 k M
  isLB := O1_isLB k M
  N := M + 1
  b := coord k M

namespace projSys

theorem algebraΓ_eq : (projSys k M).algebraΓ = algebraSections k M ⊤ :=
  Algebra.algebra_ext _ _ fun r => (LB.resG_self (X := PSpace k M) le_top _).symm

theorem isVariety (hM : 1 ≤ M) : (projSys k M).IsVariety :=
  ⟨smoothOfRelativeDimension_pspace k M, ⟨M, 𝟙 _, inferInstance, Category.id_comp _⟩,
    geometricallyConnected_pspace k M, hM⟩

theorem basePointFree : (projSys k M).BasePointFree := iSup_nonzeroLocus_coord k M

theorem form_eq {d : ℕ} {g : MvPolynomial (Fin (M + 1)) k} (hg : g.IsHomogeneous d) :
    (projSys k M).form hg = ProjSpace.formSec d g hg := by
  rw [ProjCoh.formSec_eq]
  exact congrArg (fun a : Algebra k Γ(PSpace k M, ⊤) =>
    letI := a; Twist.formSec (coord k M) (mem_polyGrading_natCast.2 hg)) (algebraΓ_eq k M)

theorem del_eq_one : (projSys k M).del = 1 := by
  have h := interNum_const_of_polynomial k (structureModule (PSpace k M)) (O1_isLB k M) (d := M)
    (Polynomial.preHilbertPoly ℚ M 0) (Polynomial.natDegree_preHilbertPoly ℚ M 0).le
    (ProjCoh.chi_sheafO_eq_eval k M)
  rw [Polynomial.coeff_preHilbertPoly_self, mul_inv_cancel₀ (Nat.cast_ne_zero.2 M.factorial_ne_zero)] at h
  rw [LinSys.del, algebraΓ_eq]
  exact_mod_cast h

theorem eq_of_sameImage {y y' : PSpace k M} (h : (projSys k M).SameImage y y') : y = y' := by
  refine ProjectiveSpectrum.ext (HomogeneousIdeal.ext' fun d g hg => ?_)
  replace hg : g.IsHomogeneous d := hg
  have := h d g hg
  rw [form_eq, nonzeroLocus_formSec] at this
  exact not_iff_not.1 this

theorem noContract (bd : Set (PSpace k M)) : (projSys k M).NoContract bd := fun C _ _ hC _ h => by
  have : Subsingleton C := ⟨fun a b => Subtype.ext (eq_of_sameImage k M (h _ a.2 _ b.2))⟩
  have := topologicalKrullDim_zero_of_discreteTopology C
  rw [hC] at this
  exact absurd this (by decide)

abbrev gen : PSpace k M := AmpleModel.genericPt k M

theorem gen_mem (i : Fin (M + 1)) : gen k M ∈ chart k M i := fun h => X_ne_zero (R := k) i h

theorem indep : (projSys k M).Indep := fun u hu => by
  have hg : (∑ j, C (u j) * X j : MvPolynomial (Fin (M + 1)) k).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X k j).C_mul _
  have h0 : (∑ j, C (u j) * X j : MvPolynomial (Fin (M + 1)) k) = 0 := by
    by_contra hne
    have h1 : ptOf (resPt (gen k M)) ∈ nonzeroLocus ((projSys k M).form hg) := by
      rw [ptOf_resPt, form_eq, nonzeroLocus_formSec]
      exact hne
    refine ((projSys k M).powVal_ne_zero_iff _ _).2 h1 ?_
    have h2 := (projSys k M).val_comb (resPt (gen k M)) u
    rw [hu, LinSys.val_zero] at h2
    rw [LinSys.powVal_form, h2, eval₂_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [eval₂_mul, eval₂_C, eval₂_X]
  funext j
  have := congrArg (eval (Pi.single j 1 : Fin (M + 1) → k)) h0
  simpa [Pi.single_apply] using this

theorem valR_resPt {Y : Scheme.{0}} (y : Y) (U : Y.Opens) (hy : y ∈ U) (f : Γ(Y, U)) :
    valR (resPt y) U f = Y.evaluation U y hy f := by
  have ht : ⊤ ≤ Y.fromSpecStalk y ⁻¹ᵁ U := (le_preimage_iff (C := Y.presheaf.stalk y) _ U).2 (by
    rw [show Y.fromSpecStalk y (IsLocalRing.closedPoint (Y.presheaf.stalk y)) = y from
      Scheme.fromSpecStalk_closedPoint]; exact hy)
  have e : valMap (C := Y.presheaf.stalk y) (Y.fromSpecStalk y) U ht = Y.presheaf.germ U y hy := by
    change (Y.fromSpecStalk y).appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom = _
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hy]
    simp only [Category.assoc]
    have e : (Spec (Y.presheaf.stalk y)).presheaf.map (homOfLE (le_top : Y.fromSpecStalk y ⁻¹ᵁ U ≤ ⊤)).op ≫
        (Spec (Y.presheaf.stalk y)).presheaf.map (homOfLE ht).op = 𝟙 _ := by
      rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
    rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
  exact (valR_spMap_comp (Y.residue y).hom (Y.fromSpecStalk y) U ht f).trans (congrArg (Y.residue y).hom
    ((valR_eq (C := Y.presheaf.stalk y) _ _ ht f).trans (congrArg (fun q => q.hom f) e)))

theorem birational : (projSys k M).Birational := by
  refine ⟨gen k M, ?_, eq_top_iff.2 fun r _ => ?_⟩
  · exact Set.eq_univ_of_forall fun x => (ProjectiveSpectrum.le_iff_mem_closure _ _ x).1
      (show ⊥ ≤ x.asHomogeneousIdeal from bot_le)
  have hx : ptOf (resPt (gen k M)) ∈ chart k M 0 := by rw [ptOf_resPt]; exact gen_mem k M 0
  have hx' := (le_iff_ptOf_mem _ _).2 hx
  obtain ⟨c, hc, h, -⟩ := (projSys k M).exists_frame_change (resPt (gen k M)) (0 : Fin (M + 1)) hx
  have key : ∀ f : Γ(PSpace k M, chart k M 0),
      valR (resPt (gen k M)) _ f ∈ (projSys k M).ratioField (resPt (gen k M)) := fun f => by
    obtain ⟨p, rfl⟩ := aeval_ratio_surjective k M 0 f
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine Subfield.subset_closure (Or.inl ⟨a, ?_⟩)
      rw [algHom_C, ← resG_algebraMap le_top, ← algebraΓ_eq]
      exact ((valR_res _ le_top hx' _).trans ((projSys k M).valR_algebraMap _ a)).symm
    | add p q hp hq => rw [map_add (f := _), valR_add _ _ hx']; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, valR_mul _ _ hx', aeval_X]
      refine mul_mem hp (Subfield.subset_closure (Or.inr ⟨j, (0 : Fin (M + 1)), ?_⟩))
      have h0 : 1 = c * (projSys k M).coords (resPt (gen k M)) (0 : Fin (M + 1)) :=
        (valR_one _ _ hx').symm.trans ((congrArg _ (ratioOn_self (hi := le_rfl)).symm).trans (h (coord k M 0)))
      rw [← mul_div_mul_left _ _ hc, ← h0, div_one]
      exact h (coord k M j)
  obtain ⟨t, rfl⟩ := (PSpace k M).residue_surjective _ r
  let := (PSpace k M).presheaf.algebra_section_stalk (U := chart k M 0) ⟨gen k M, gen_mem k M 0⟩
  have := (isAffineOpen_chart k M 0).isLocalization_stalk ⟨gen k M, gen_mem k M 0⟩
  obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj
    ((isAffineOpen_chart k M 0).primeIdealOf ⟨gen k M, gen_mem k M 0⟩).asIdeal.primeCompl t
  have hs := (IsLocalization.map_units ((PSpace k M).presheaf.stalk (gen k M)) s).map
    ((PSpace k M).residue (gen k M)).hom
  have e' := congrArg ((PSpace k M).residue (gen k M)).hom e
  rw [map_mul, ← eq_div_iff hs.ne_zero] at e'
  have ha := key a
  have hb := key s
  rw [valR_resPt _ _ (gen_mem k M 0)] at ha hb
  exact e' ▸ div_mem ha hb

end projSys
end GlobalTheory.Adelic
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.Ex
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

def KeyAtMap {R R' : Type} [CommRing R] [CommRing R'] (x' : KeyIn R') (x : KeyIn R) (f : R →+* R')
    (φ : x'.P.A.left ⟶ x.P.A.left) : Prop :=
  ∃ (he : eSec x'.P.A ≫ φ = spMap f ≫ eSec x.P.A)
    (w : LB.Iso x'.P.L (x.P.L.pull φ)) (hg : x'.P.g = x.P.g) (F : DualNumber R →+* DualNumber R'),
    IsGrpPullback x'.P.A x.P.A (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x'.P.A) (fun _ => 1)) x'.rig
      (rigPullOf φ (spMap f) he x.P.L x.rig) ∧
    (∀ (j : (x.P.L.pull φ).ι) (i : x'.P.L.ι)
      (h : (x.P.L.pull φ).U j ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (x.th.f (j PUnit.unit)) =
        (show Γ(x'.P.A.left, (x.P.L.pull φ).U j ⊓ x'.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x'.th.f i)) ∧
    (∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) ∧ F DualNumber.eps = DualNumber.eps ∧
    ∀ i, (x'.v i).left ≫ φ = spMap F ≫ (x.v (i.cast hg)).left

end GlobalTheory.MBLow

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
noncomputable section

open scoped Classical

namespace GlobalTheory.LKCount

section Vol

variable {G : Type} [Group G]

def vol (C H : Subgroup G) : ℚ := ((C.relIndex H : ℕ) : ℚ) / ((H.relIndex C : ℕ) : ℚ)

def orbC (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
    ((vol C (GlobalTheory.BCT.twCent θ δ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℚ) : ℂ)⁻¹ *
      f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q))

def orbK (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  orbC θ K (GlobalTheory.BCT.twCent θ δ ⊓ K) δ f

def massC (Γ' T C : Subgroup G) : ℚ :=
  ∑ᶠ q : DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T),
    ((Nat.card ((Γ'.subgroupOf T) ⊓ (C.subgroupOf T).map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup T) : ℕ) : ℚ)⁻¹

end Vol

section Count

variable {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂]

def stab (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (x : G₁ × G₂) : Subgroup Γ :=
  (K₁.map (MulAut.conj x.1).toMonoidHom).comap ι₁ ⊓ (K₂.map (MulAut.conj x.2).toMonoidHom).comap ι₂

def pointSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
    ((Nat.card (stab ι₁ ι₂ K₁ K₂ (Quotient.out q)) : ℕ) : ℂ)⁻¹ *
      (f₁ ((Quotient.out q).1⁻¹ * γ * (Quotient.out q).1) * φ ((Quotient.out q).2⁻¹ * δ * θ (Quotient.out q).2))

def pointSide (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ((massC (ι₁.prod ι₂).range (GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ))
      (GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ) ⊓ K₁.prod K₂) : ℚ) : ℂ) *
    (orbK (MonoidHom.id G₁) K₁ γ f₁ * orbK θ K₂ δ φ)

def term (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (δ : G₂) (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) (x : G₁ × G₂) (γ : Γ) : ℂ :=
  f₁ (x.1⁻¹ * ι₁ γ * x.1) * φ (x.2⁻¹ * (ι₂ γ * δ) * θ x.2)

def centSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) (γ : Γ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (((Subgroup.centralizer {γ}).map (ι₁.prod ι₂) : Subgroup (G₁ × G₂)) : Set (G₁ × G₂))
      ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
    ((Nat.card (stab ι₁ ι₂ K₁ K₂ (Quotient.out q) ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ *
      term ι₁ ι₂ θ δ f₁ φ (Quotient.out q) γ

end Count

section Examples

end Examples

end GlobalTheory.LKCount
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix
open scoped TensorProduct Classical

namespace GlobalTheory.LKRes

section Generic

variable {G : Type} [Group G]

end Generic

variable (p : ℕ) [Fact p.Prime]

abbrev Q0 : IntermediateField ℚ_[p] (PadicAlgCl p) := ⊥

abbrev Qr (r : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) := Kn p (Q0 p) r

def frobQ (r : ℕ) : Qr p r →ₐ[ℚ_[p]] Qr p r :=
  { GlobalTheory.LKLoc.frobR p (Q0 p) r with
    commutes' := fun c => Subtype.ext (((frobK p (Q0 p)).restrictScalars ℚ_[p]).commutes c) }

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def KQ (r : ℕ) : Type := K ⊗[ℚ_[p]] Qr p r

instance (r : ℕ) : CommRing (KQ p K r) := inferInstanceAs (CommRing (K ⊗[ℚ_[p]] Qr p r))

instance (r : ℕ) : Algebra ℚ_[p] (KQ p K r) := inferInstanceAs (Algebra ℚ_[p] (K ⊗[ℚ_[p]] Qr p r))

instance (r : ℕ) : TopologicalSpace (KQ p K r) := moduleTopology ℚ_[p] (KQ p K r)

def inclK (r : ℕ) : K →ₐ[ℚ_[p]] KQ p K r := Algebra.TensorProduct.includeLeft

def inclQ (r : ℕ) : Qr p r →ₐ[ℚ_[p]] KQ p K r := Algebra.TensorProduct.includeRight

def sigKQ (r : ℕ) : KQ p K r →ₐ[ℚ_[p]] KQ p K r :=
  Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r)

def intKQ (r : ℕ) : Subring (KQ p K r) :=
  Subring.closure (Set.range (fun a : GlobalTheory.LKLoc.intK p K => inclK p K r a) ∪
    Set.range (fun b : GlobalTheory.LKLoc.intR p (Q0 p) r => inclQ p K r b))

def sigRes (n r : ℕ) : GL (Fin n) (KQ p K r) →* GL (Fin n) (KQ p K r) :=
  GeneralLinearGroup.map (sigKQ p K r).toRingHom

def Kres (n r : ℕ) : Subgroup (GL (Fin n) (KQ p K r)) :=
  (GeneralLinearGroup.map (intKQ p K r).subtype).range

def nrmRes (n r : ℕ) (δ : GL (Fin n) (KQ p K r)) : GL (Fin n) (KQ p K r) :=
  (List.map (fun i => (⇑(sigRes p K n r))^[i] δ) (List.range r)).prod

abbrev GHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) : Type :=
  GL (Fin 1) (Qr p r) × ((i : Fin m) → GL (Fin n) (KQ p (Kw i) r))

def sigHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) : GHT p m n r Kw →* GHT p m n r Kw :=
  (GlobalTheory.LKLoc.sig p (Q0 p) 1 r).prodMap (Pi.monoidHom fun i => (sigRes p (Kw i) n r).comp (Pi.evalMonoidHom _ i))

def KHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) : Subgroup (GHT p m n r Kw) :=
  (GlobalTheory.LKLoc.Kint p (Q0 p) 1 r).prod (Subgroup.pi Set.univ fun i => Kres p (Kw i) n r)

theorem sigKQ_apply_inclK (r : ℕ) (a : K) : sigKQ p K r (inclK p K r a) = inclK p K r a := by
  show Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) =
    a ⊗ₜ[ℚ_[p]] (1 : Qr p r)
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

theorem sigKQ_apply_inclQ (r : ℕ) (b : Qr p r) : sigKQ p K r (inclQ p K r b) = inclQ p K r (frobQ p r b) := by
  show Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) ((1 : K) ⊗ₜ[ℚ_[p]] b) =
    (1 : K) ⊗ₜ[ℚ_[p]] (frobQ p r b)
  rw [Algebra.TensorProduct.map_tmul, map_one]

theorem frobQ_degree_one : frobQ p 1 = AlgHom.id ℚ_[p] (Qr p 1) := by
  have hK : FiniteDimensional ℚ_[p] (Q0 p) := by
    infer_instance
  have hle : Q0 p ≤ Qr p 1 := bot_le
  have hdeg : degLK p (Q0 p) (Kn p (Q0 p) 1) = 1 := degLK_Kn hK one_pos
  rw [degLK_eq_finrank (h := hle)] at hdeg
  have hbot := IntermediateField.finrank_eq_one_iff.1 hdeg
  refine AlgHom.ext fun x => Subtype.ext ?_
  have hx : (x : PadicAlgCl p) ∈ Q0 p := by
    have h1 : (x : PadicAlgCl p) ∈ IntermediateField.extendScalars hle := by
      exact x.2
    rw [hbot] at h1
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 h1
    rw [← hy]
    exact y.2
  exact (frobK p (Q0 p)).commutes ⟨_, hx⟩

theorem sigRes_degree_one (n : ℕ) : sigRes p K n 1 = MonoidHom.id _ := by
  have h1 : sigKQ p K 1 = AlgHom.id ℚ_[p] (KQ p K 1) := by
    unfold sigKQ
    rw [frobQ_degree_one]
    exact Algebra.TensorProduct.map_id
  refine MonoidHom.ext fun g => Matrix.GeneralLinearGroup.ext fun i j => ?_
  show sigKQ p K 1 ((g : Matrix (Fin n) (Fin n) (KQ p K 1)) i j) = (g : Matrix (Fin n) (Fin n) (KQ p K 1)) i j
  rw [h1]
  rfl

private lemma gl_fin_one_mul_comm {R : Type} [CommRing R] (a b : GL (Fin 1) R) : a * b = b * a := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem normal_of_gl_one {R : Type} [CommRing R] (H : Subgroup (GL (Fin 1) R)) : H.Normal :=
  ⟨fun n hn g => by
    rw [gl_fin_one_mul_comm g n, mul_inv_cancel_right]
    exact hn⟩

end GlobalTheory.LKRes
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsPow8F
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

def IsPow8 {S : Scheme.{0}} (P P₈ : PolAV S) (d : ℕ) (pr : Fin 8 → (P₈.A ⟶ P.A)) (inc : P.A ⟶ P₈.A) : Prop :=
  (∀ u, IsMonHom (pr u)) ∧ IsMonHom inc ∧ (∀ (T : Over S) (y : Fin 8 → (T ⟶ P.A)), ∃! x : T ⟶ P₈.A, ∀ u, x ≫ pr u = y u) ∧
    (∀ u, inc ≫ pr u = if u = 0 then 𝟙 P.A else 1) ∧ LBIso (P₈.L.pull inc.left) (lbPow P.L d)

end GlobalTheory.MBLow

end
end
