module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OverIx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTauLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsDomain R]

structure Factor (D D' : DegPre R) where

  O : Type
  [ring : Ring O]
  [star : StarRing O]
  [mod : Module O D'.X]

  o : D'.OAct O

  e : O

  f : O

  inc : D.P.A ⟶ D'.P.A

  pr : D'.P.A ⟶ D.P.A

  xi : D.X →+ D'.X

  xp : D'.X →+ D.X

  w : letI := D.P.isAb.comm; letI := D'.P.isAb.comm
    LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ D'.P.A D'.P.L).pull
      (lift (fst D.P.A D.P.A ≫ inc) (snd D.P.A D.P.A ≫ inc ≫ o.onB.act f) : G2 D.P.A ⟶ G2 D'.P.A).left)
  idem : e * e = e
  inc_hom : IsMonHom inc
  pr_hom : IsMonHom pr
  inc_pr : inc ≫ pr = 𝟙 _
  pr_inc : pr ≫ inc = o.onB.act e
  xp_xi : ∀ y, xp (xi y) = y
  xi_xp : ∀ z, xi (xp z) = e • z
  c_xi : ∀ y, D'.c (xi y) = D.c y ≫ inc
  inj : Function.Injective fun y => Star.star e • f • xi y
  onto : ∀ z, ∃ y, Star.star e • z = Star.star e • f • xi y
  w_gen : w.IsGen
  tau : ∀ a b z J J', Good D'.P.L z J → Good D.P.L z J' →
    val (D.tau a b) (𝟙 _) z J' =
      GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J J' *
        val (D'.tau (xi a) (f • xi b)) (𝟙 _) z J

attribute [instance] Factor.ring Factor.star Factor.mod

def SamePol (D D' : DegPre R) : Prop :=
  ∃ (Q : GlobalTheory.PolDeg.Data R) (e : D.X ≃+ Q.X) (e' : D'.X ≃+ Q.X),
    GlobalTheory.PolDeg.Refines Q (RingHom.id R) D e ∧ GlobalTheory.PolDeg.Refines Q (RingHom.id R) D' e'

abbrev Kb (R : Type) [CommRing R] [IsDomain R] : Type := AlgebraicClosure (FractionRing R)

abbrev Labels (D : DegPre R) (A : PolAV (Sp (FractionRing R))) : Type :=
  ∀ k : ℕ, QkPt D (Kb R) k → (TFK (R := R) (Kb R) ⟶ A.A)

def Induces {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegPre R} {A : PolAV (Sp (FractionRing R))}
    (lab : Labels D A) (φ : R →+* W) {D' : DegData W I} {A' : PolAV (Sp (FractionRing W))} {G' : Over (Sp W)} [GrpObj G']
    [IsCommMonObj G'] (U' : Unif I D' A' G') (hD : IsPullDeg φ D D'.toPre) (a : A'.A.left ⟶ A.A.left) (k : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W) F] [Algebra (FractionRing R) F]
    (em : Kb R →ₐ[FractionRing R] F),
    (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (φ r))) →
    ∀ (p : QkPt D (Kb R) k) (p₁ : QkPt D F k) (p' : QkPt D'.toPre F k) (x' : TFK (R := W) F ⟶ A'.A),
      QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD F p₁.g p'.g →
      x'.left ≫ a = spMap em.toRingHom ≫ (lab k p).left → QkToAkU U'.toUnifPre F k p' x'

def IsFib {W : Type} [CommRing W] [IsDomain W] (φ : R →+* W) (A : PolAV (Sp (FractionRing R)))
    (A' : PolAV (Sp (FractionRing W))) (a : A'.A.left ⟶ A.A.left) : Prop :=
  ∃ ga : FractionRing R →+* FractionRing W, (∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r)) ∧
    IsGrpPullback A'.A A.A (spMap ga) a ∧ LBIso A'.L (A.L.pull a)

def OneTrait [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (lab : Labels D A) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (G' : Over (Sp W)) (_ : GrpObj G')
    (_ : IsCommMonObj G') (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W)))
    (U' : Unif (maximalIdeal W) D' A' G') (hD : IsPullDeg φ D D'.toPre) (a : A'.A.left ⟶ A.A.left)
    (_ : Algebra (FractionRing R) (Kb W)) (em : Kb R →ₐ[FractionRing R] Kb W),
    GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsSemiAbelian G' ∧ IsFib φ A A' a ∧
    (∀ r, algebraMap (FractionRing R) (Kb W) (algebraMap R _ r) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D (Kb R) k) (p₁ : QkPt D (Kb W) k) (p' : QkPt D'.toPre (Kb W) k)
      (x' : TFK (R := W) (Kb W) ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD (Kb W) p₁.g p'.g →
      x'.left ≫ a = spMap em.toRingHom ≫ (lab k p).left → QkToAkU U'.toUnifPre (Kb W) k p' x'

end

structure Emb {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) (G : Over S) [GrpObj G] where

  N : ℕ

  H : G.left.Opens
  H_all : ∀ g : G.left, π (G.hom g) = closedPoint R → g ∈ H

  f : H.toScheme ⟶ PSpace R N
  f_over : f ≫ PSpace.str R N = H.ι ≫ G.hom ≫ π

  Y : Over (Sp (ResidueField R))
  [grp : GrpObj Y]
  smooth : Smooth Y.hom

  j : Y.left ⟶ PSpace R N
  j_over : j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R)
  imm : IsImmersion j
  fib : ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ S) (κ : ResidueField R →+* Ω), x ≫ π = spMap (κ.comp (residue R)) →
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω')
      (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y)
      (l : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ H.toScheme), IsMonHom e.hom ∧
      l ≫ H.ι = pullback.fst G.hom (spMap io ≫ x) ∧ l ≫ f = e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) ≫ j

attribute [instance] Emb.grp

def Emb.Theta {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G] (E : Emb π G)
    (L : LB G.left) : Prop :=
  ∃ (θ : L.Sec) (O : E.Y.left.Opens), (O : Set E.Y.left).Nonempty ∧ ∀ (g : E.H.toScheme) (y : E.Y.left), y ∈ O →
    π (G.hom (E.H.ι g)) = closedPoint R → E.f g = E.j y → ∃ i : L.ι, E.H.ι g ∈ G.left.basicOpen (θ.f i)

namespace Wit
open InhTate Inh

end Wit

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

def SharpRef (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X) : Prop :=
  ∃ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))),
    (∀ a, IsMonHom (pr a)) ∧
    (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) ∧
    w.IsGen ∧ (∀ mu a, (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = spMap ρ ≫ (Q.c (mu a)).left) ∧
    ∀ κ : (TK V₁).left ⟶ (TK V).left, κ ≫ jK V = jK V₁ ≫ spMap ρ → ∀ mu z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.psi (e mu)) (𝟙 _) z J' =
        gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
            pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
          ∏ a, ∏ b, val (Q.tau (mu a) (mu b)) κ z J ^ W a b

def IsThetaTerms (D : DegPre V₁) (N₁ : ℕ) {X C : Type} [AddCommGroup X] (e : X ≃+ D.X) (T : X → C → V₁) : Prop :=
  ∃ (th : Fam D (FractionRing V₁) 1) (g : C → GtPtF D (FractionRing V₁)) (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A))
    (w : ∀ c, Frm D (FractionRing V₁) 1 (g c).b),
    (∀ c, (g c).b = toUnit _ ≫ b c) ∧ (∀ c, ∃ o, GtPtF.IsNsmul N₁ (g c) o ∧ o.IsZero) ∧
    (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ N₁ = 1 →
      ∃ c, p = toUnit _ ≫ b c) ∧
    (∀ c, (w c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
      val (w c) (𝟙 _) z J ^ (N₁ ^ 2) * val κ (g c).b.left z J = 1) ∧
    (∀ mu c, IsCoef 1 (g c) (w c) (e mu) (th.s (e mu)) (algebraMap V₁ (FractionRing V₁) (T mu c))) ∧
    ∃ c, T 0 c = 1

section Real

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  (X₁ : Setup F W i) (z₁ : X₁.M.Z) {N₁ : ℕ} (Φ : VSys (id : ℤ → ℤ) g W N₁ (X₁.M.Z.presheaf.stalk z₁))

def HasTraits : Prop :=
  ∀ (T : Trait F) (ev : X₁.M.Z.presheaf.stalk z₁ →+* T.V), IsLocalHom ev →
    jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = T.y ≫ i →
    ∃ (y : Φ.Y) (f : T.V →+* Φ.V y) (e : Φ.X y ≃+ T.D.toPre.X), Φ.m y = 1 ∧ IsPrincipalIdealRing (Φ.V y) ∧
      Function.Injective f ∧ IsLocalHom f ∧ f.comp ev = Φ.ev y ∧
      ∀ k, Φ.t y k = f T.ϖ ∧ ∀ a b, Φ.δ y k a b = T.β (e a) (e b)

def IsChartMember [IsLocalRing V] (Q : Data V) (ξ : Sp V ⟶ Z) {m : ℕ} (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X)
    (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m) : Prop :=
  Function.Injective ρ ∧ ρ.Finite ∧ spMap (Φ.ev y) ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = spMap ρ ≫ ξ ∧
    (∀ k, Φ.t y k = ρ (t (h k)) ∧ ∀ a b, Φ.δ y k a b = δ (h k) (e a) (e b)) ∧
    ∃ (D : DegPre (Φ.V y)) (e₈ : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e₈ ∧
      IsThetaTerms D N₁ e₈ fun mu c => Φ.u y (fun a => e.symm (mu a)) c * mono W (Φ.t y) (Φ.δ y) fun a => e.symm (mu a)

end Real

def Elements {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {N₁ : ℕ} {A : Type} [CommRing A]
    [IsLocalRing A] (Φ : VSys bar q W N₁ A) (y : Φ.Y) (φ : InvFun O) (d : ℕ)
    (ga : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y)) {K : Type} [Field K] (ev : Φ.V y →+* K) (k₀ : Subfield K) : Prop :=
  ∃ (O' : Subring (Φ.V y)) (g₀ : Φ.V y) (b : Fin (Φ.m y) → ℕ), (∀ h ∈ O', ev h ∈ k₀ ∧ (h ∈ maximalIdeal (Φ.V y) → ev h = 0)) ∧
    (∀ k, (b k : ℝ) = d * φ.evalZ (Φ.δ y k)) ∧ Associated g₀ (∏ k, Φ.t y k ^ b k) ∧
    ∀ (D l : ℕ) (a : Fin l × Fin s → Φ.X y), Dominant bar φ (D * d) N₁ W ga a → ∀ (c : Fin l → Φ.Q) (e : ℕ), ∃ h ∈ O',
      h * g₀ ^ D - Φ.coefT y a c * Φ.monoT y a ∈
        Ideal.span {Φ.monoT y a} * Ideal.span (Set.range (Φ.t y)) ⊔ maximalIdeal (Φ.V y) ^ e

def Values {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {N₁ : ℕ} {A : Type} [CommRing A]
    [IsLocalRing A] (Φ : VSys bar q W N₁ A) (y : Φ.Y) {K : Type} [Field K] (ev : Φ.V y →+* K) (k₀ : Subfield K) : Prop :=
  (∀ k, ev (Φ.t y k) = 0) ∧
  (∀ mu c c', IsUnit (Φ.u y mu c') → ∃ r ∈ k₀, ev (Φ.u y mu c) = r * ev (Φ.u y mu c')) ∧
  ∀ lam : LinearMap.BilinForm ℤ (Φ.X y) →ₗ[ℤ] ℤ, (∀ k, lam (Φ.δ y k) = 0) →
    ∃ (l l' M : ℕ) (a : Fin l × Fin s → Φ.X y) (a' : Fin l' × Fin s → Φ.X y) (c : Fin l → Φ.Q) (c' : Fin l' → Φ.Q), 1 ≤ M ∧
      IsUnit (Φ.coefT y a c) ∧ IsUnit (Φ.coefT y a' c') ∧ (∀ β ∈ balForms bar (Φ.X y), lin W a β - lin W a' β = M * lam β) ∧
      ∃ r ∈ k₀, ev (Φ.coefT y a c) = r * ev (Φ.coefT y a' c')

end GlobalTheory.Poinc.Sep
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

@[reducible] def GlobalTheory.ZH.ThetaSys.rechart {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (c : Ω) (hc : c ≠ 0)
    (R' : Subalgebra o Ω) (fg : R'.FG) (frac : ∀ x : Ω, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c * S.th x ∈ R')
    (hev : ∀ x i, c * S.ev x i ∈ R') : ThetaSys o Ω :=
  { S with
    th := fun x => c * S.th x
    ev := fun x i => c * S.ev x i
    R := R'
    fg := fg
    frac := frac
    th_mem := hth
    ev_mem := hev
    supp := by simpa [hc] using S.supp
    th_ne := S.th_ne.imp fun _ h => mul_ne_zero hc h }

namespace GlobalTheory.Poinc

variable {g n : ℕ}


open MonObj in
def IsDiagEnd (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T : Scheme.{0}} (P : PolAV T) (u : T ⟶ F.X)
    (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) : Prop :=
  ∃ c : SiegPre g n (zetaAway n) (u ≫ F.s), SiegPB c F.univ u ∧ ∃ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) ∧
    (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y a) ∧
    LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) ∧
    ∀ E a, ε E ≫ pr a = ((List.finRange 8).map fun b => pr b ^ E a b).prod

def Same {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} (ρ : S.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (ρ' : S'.Real)
    (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)) (lab : S.Gam → S'.Gam) (φ : Ω →+* Ω') : Prop :=
  ∃ (P₀ : PolAV (Sp Ω')) (a : P₀.A.left ⟶ ρ.P.A.left) (a' : P₀.A.left ⟶ ρ'.P.A.left)
    (ε₀ : Matrix (Fin 8) (Fin 8) ℤ → (P₀.A ⟶ P₀.A)),
    IsGrpPullback P₀.A ρ.P.A (spMap (φ.comp S.R.val.toRingHom)) a ∧ IsGrpPullback P₀.A ρ'.P.A (spMap S'.R.val.toRingHom) a' ∧
    LBIso P₀.L (ρ.P.L.pull a) ∧ LBIso P₀.L (ρ'.P.L.pull a') ∧
    (∀ E, (ε₀ E).left ≫ a = a ≫ (ε E).left ∧ (ε₀ E).left ≫ a' = a' ≫ (ε' E).left) ∧
    ∀ x, ∃ w : Sp Ω' ⟶ P₀.A.left, w ≫ a = spMap (φ.comp S.R.val.toRingHom) ≫ (ρ.pt x).left ∧
      w ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt (lab x)).left

variable {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

abbrev ModN (m : ℕ) (X : Type) [AddCommGroup X] : Type := X ⧸ (nsmulAddMonoidHom m : X →+ X).range

def IsLab (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) {p : ℕ} [Fact p.Prime] {z : X.M.Z}
    (c : CTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)) : Prop :=
  ∃ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b)
    (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R')
    (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)),
    Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧
    R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧
    ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) ∧
      ∃ (u : ρ'.UTest p y₀) (l : u.Lab) (j : u.D.toPre.X ≃+ (Fin 8 → c.T.D.toPre.X)),
        (∀ χ, l.q χ = c.sc * (qW W c.T.β (j χ) : ℤ)) ∧
        (∀ a χ, l.yy a = QuotientAddGroup.mk χ → yy a = QuotientAddGroup.mk (j χ)) ∧
        ∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
          (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x →
          QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ (ε' E).left →
          CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b)

structure Deep (X₁ : Setup F W i) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) where

  X : Setup F W i

  ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)
  diag : IsDiagEnd F W X.ρ.P X.u ε
  [alg : Algebra X₁.Ω₁ X.Ω₁]
  fd : FiniteDimensional X₁.Ω₁ X.Ω₁
  gal : IsGalois X₁.Ω₁ X.Ω₁
  proj : IsProjOver X.M.s

  q : X.M.Z ⟶ X₁.M.Z
  fin : IsFinite q
  gen : X.M.pt ≫ q = spMap (algebraMap X₁.Ω₁ X.Ω₁) ≫ X₁.M.pt
  comp : q ≫ X₁.π = X.π

  m : ℕ
  sq : X.S.N = m ^ 2
  dvd : X₁.S.r * X₁.S.N ∣ m

  lab : X₁.S.Gam →+ X.S.Gam
  same : Same X₁.ρ ε₁ X.ρ ε lab (algebraMap X₁.Ω₁ X.Ω₁)
  lab_range : ∀ x : X.S.Gam, ∃ a, lab a = (X.S.r * X.S.N / (X₁.S.r * X₁.S.N)) • x

attribute [instance] Deep.alg

namespace Deep

variable {X₁ : Setup F W i} {ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (D : Deep X₁ ε₁)

@[reducible] def lift {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) :
    CTrait D.X p (y (cPt p)) where
  y := y
  cen := rfl
  T := c.T
  ι := c.ι
  int := c.int
  comm := by rw [← D.comp, ← Category.assoc y, h, c.comm]

def Compat {X : Type} [AddCommGroup X] (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) X)
    (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) X) : Prop :=
  ∀ a μ, yy₁ a = QuotientAddGroup.mk μ →
    yy (D.lab a) = QuotientAddGroup.mk ((D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) • μ)

end Deep

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

section Ord

variable {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) {F : SFam g n ζ}

def OrdGe (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  x ∈ M.O ((jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V))) ∧
    ∃ w : T.V, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

def OrdEq (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  ∃ w : T.Vˣ, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

def ThroughU {X : Scheme.{0}} (U₀ : M.Z.Opens) (u₀ : U₀.toScheme ⟶ X) (c : X ⟶ F.X) (T : Trait F) (ξ : Sp T.V ⟶ M.Z) : Prop :=
  ∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ ξ₀ ≫ u₀ ≫ c = T.y

variable {M}

variable (M)

end Ord

def TraitExtSt : Prop :=
  ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
    GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ F.X,
      ∃ (T : Trait F) (f : V →+* T.V) (fK : FractionRing V →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧
        f.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap T.V _ (f a)) ∧ T.y = spMap fK ≫ y

def TraitUniqSt : Prop :=
  ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T T' : Trait F) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W] (f : T.V →+* W) (f' : T'.V →+* W) (fK : FractionRing T.V →+* FractionRing W)
    (fK' : FractionRing T'.V →+* FractionRing W), GlobalTheory.Mum.Base W → IsDiscreteValuationRing W →
    Function.Injective f → Function.Injective f' → IsLocalHom f → IsLocalHom f' →
    (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) → (∀ a, fK' (algebraMap T'.V _ a) = algebraMap W _ (f' a)) →
    spMap fK ≫ T.y = spMap fK' ≫ T'.y → ∀ (w : W) (m m' : ℕ), Irreducible w → Associated (f T.ϖ) (w ^ m) →
      Associated (f' T'.ϖ) (w ^ m') →
      ∃ e : T.D.toPre.X ≃+ T'.D.toPre.X, ∀ a b, (m : ℤ) * T.β a b = m' * T'.β (e a) (e b)

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4

namespace GlobalTheory.Mean4O

section Met

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

abbrev PolOf (x : ToroidalCompactificationData s) (Φ : s.Flag) : Type := PolDat s Φ (metsOf x Φ) (refMet x Φ)

def metTrue (x : ToroidalCompactificationData s) (Φ : s.Flag) (P : PolOf x Φ) : MetIn Φ where
  hm := metsOf x Φ
  h0 := refMet x Φ
  r := rFlag x Φ
  ab := P.ab
  dir := P.dir
  reg := P.reg

end Met

namespace Setup

variable {D : D7} (O : Setup D)

structure CoreWith (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ) : Prop where
  met : O.met = metTrue x O.Φ P
  Mb : O.Mb = mbarOf P
  bd : IsBdOf x O.L O.B
  fl : O.fl = flBetti O.s O.Φ O.L

def Core : Prop := ∃ (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P

namespace CoreWith

variable {O} {x : ToroidalCompactificationData O.s} {P : PolOf x O.Φ} (h : O.CoreWith x P)
include h

end CoreWith

namespace Core

variable {O} (h : O.Core) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ)
include h

end Core

end Setup

end GlobalTheory.Mean4O
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget
noncomputable section

namespace GlobalTheory.UPel.HT.Gen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {G : GDatum} {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] [Algebra ℚ R₁] [Algebra ℚ R₂]
  {S S' : Scheme.{0}}

def IsGGPull {gb₁ : GBase G R₁} {gb₂ : GBase G R₂} {N : ℕ} {s' : S' ⟶ Sp R₂} {s : S ⟶ Sp R₁}
    (o' : GObj gb₂ N s') (o : GObj gb₁ N s) (f : S' ⟶ S) : Prop :=
  ∃ (φA : o'.A.left ⟶ o.A.left) (φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left),
    IsGrpPullback o'.A o.A f φA ∧ IsSquare φA φ₂ ∧
    (∀ c : G.O, (o'.act.act c).left ≫ φA = φA ≫ (o.act.act c).left) ∧ Nonempty (LBIso o'.P (o.P.pull φ₂)) ∧
    ∀ y : G.La, (o'.eta y).left ≫ φA = f ≫ (o.eta y).left

def GBase.IsMap (β : R₁ →+* R₂) (gb₁ : GBase G R₁) (gb₂ : GBase G R₂) : Prop :=
  gb₂.ρ = β gb₁.ρ ∧ ∀ i, gb₂.t i = β.comp (gb₁.t i)

def GBase.map (β : R₁ →+* R₂) (gb : GBase G R₁) : GBase G R₂ where
  ρ := β gb.ρ
  ρ_root := by simpa using congrArg β gb.ρ_root
  t i := β.comp (gb.t i)
  t_ω i := by rw [RingHom.comp_apply, gb.t_ω]
  comax i j hij := by
    have h := congrArg (Ideal.map β) (gb.comax i j hij)
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    simpa [Function.comp_def] using h

theorem GBase.IsMap.id (gb : GBase G R₁) : GBase.IsMap (RingHom.id R₁) gb gb :=
  ⟨rfl, fun _ => rfl⟩

def IsGGPullOver (β : R₁ →+* R₂) {gb₁ : GBase G R₁} {gb₂ : GBase G R₂} {N : ℕ} {s' : S' ⟶ Sp R₂} {s : S ⟶ Sp R₁}
    (o' : GObj gb₂ N s') (o : GObj gb₁ N s) (f : S' ⟶ S) : Prop :=
  f ≫ s = s' ≫ spMap β ∧ GBase.IsMap β gb₁ gb₂ ∧ IsGGPull o' o f

section Over

variable {β : R₁ →+* R₂} {gb₁ : GBase G R₁} {gb₂ : GBase G R₂} {N : ℕ} {s' : S' ⟶ Sp R₂} {s : S ⟶ Sp R₁}
  {o' : GObj gb₂ N s'} {o : GObj gb₁ N s} {f : S' ⟶ S}

end Over

variable {R : Type} [CommRing R] [Algebra ℚ R]

theorem isGGPull_iff {gb : GBase G R} {N : ℕ} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : GObj gb N s'}
    {o : GObj gb N s} {f : S' ⟶ S} : IsGGPull o' o f ↔ Nonempty (GObjMap o' o f) :=
  ⟨fun ⟨φ, φ₂, h₁, h₂, h₃, ⟨h₄⟩, h₅⟩ => ⟨⟨φ, φ₂, h₁, h₂, h₃, h₄, h₅⟩⟩,
    fun ⟨m⟩ => ⟨m.φ, m.φ₂, m.cart, m.sq, m.act, ⟨m.pol⟩, m.eta⟩⟩

theorem isGGPullOver_id_iff {gb : GBase G R} {N : ℕ} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : GObj gb N s'}
    {o : GObj gb N s} {f : S' ⟶ S} :
    IsGGPullOver (RingHom.id R) o' o f ↔ f ≫ s = s' ∧ Nonempty (GObjMap o' o f) := by
  have e : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id (CommRingCat.of R)
  rw [IsGGPullOver, e, Category.comp_id, isGGPull_iff]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, GBase.IsMap.id gb, h.2⟩⟩

theorem IsGGPull.refl {gb : GBase G R} {N : ℕ} {s : S ⟶ Sp R} (o : GObj gb N s) : IsGGPull o o (𝟙 S) :=
  isGGPull_iff.2 (Unique.gObjMap_id o)

section Comp

variable {R₃ : Type} [CommRing R₃] [Algebra ℚ R₃] {gb₁ : GBase G R₁} {gb₂ : GBase G R₂} {gb₃ : GBase G R₃} {N : ℕ}
  {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R₁} {s₂ : S₂ ⟶ Sp R₂} {s₃ : S₃ ⟶ Sp R₃} {o₁ : GObj gb₁ N s₁}
  {o₂ : GObj gb₂ N s₂} {o₃ : GObj gb₃ N s₃} {f : S₃ ⟶ S₂} {f' : S₂ ⟶ S₁}

end Comp

theorem GObj.eta_zero {gb : GBase G R} {M : ℕ} {s : S ⟶ Sp R} (o : GObj gb M s) : o.eta 0 = 1 := by
  have h := o.eta_add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := o.eta 0) (by rw [_root_.mul_one]; exact h.symm)

theorem GObj.eta_neg {gb : GBase G R} {M : ℕ} {s : S ⟶ Sp R} (o : GObj gb M s) (x : G.La) :
    o.eta (-x) = (o.eta x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← o.eta_add, add_neg_cancel, GObj.eta_zero]

theorem GObj.eta_nsmul {gb : GBase G R} {M : ℕ} {s : S ⟶ Sp R} (o : GObj gb M s) (n : ℕ) (x : G.La) :
    o.eta (n • x) = o.eta x ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, GObj.eta_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

def gHeckeSub {gb : GBase G R} {M : ℕ} {s : S ⟶ Sp R} (o : GObj gb M s) (g : G.La →ₗ[G.O] G.La) (N : ℕ) :
    Subgroup (𝟙_ (Over S) ⟶ o.A) where
  carrier := {h | ∃ x, h = o.eta (N • g x)}
  one_mem' := ⟨0, by rw [map_zero, smul_zero, GObj.eta_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by rw [map_add (f := _), smul_add, o.eta_add]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, smul_neg, GObj.eta_neg]⟩

def IsGHecke {gb : GBase G R} (g : G.La →ₗ[G.O] G.La) (c k N : ℕ) {s : S ⟶ Sp R} (o : GObj gb (N * k) s)
    (o' : GObj gb N s) (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ c' : G.O, o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') ∧ (∀ x, o'.eta x = o.eta (g x) ≫ ψ) ∧
    GlobalTheory.ZM.IsGaloisCover (gHeckeSub o g N) (fun h => (Hecke.transl h.1).left) ψ.left ∧
    Nonempty (LBIso (Hecke.lbPow o.P (k ^ 2 / c)) (o'.P.pull (Hecke.sq2 ψ))) ∧ c ∣ k ^ 2

def IsGHeckeMap {gb : GBase G R} (g : G.La →ₗ[G.O] G.La) (c k N : ℕ) (X : GenModel gb N) (X' : GenModel gb (N * k))
    (π : X'.X ⟶ X.X) : Prop :=
  π ≫ X.s = X'.s ∧ ∃ (o' : GObj gb N X'.s) (ψ : X'.univ.A ⟶ o'.A), IsGHecke g c k N X'.univ o' ψ ∧
    Nonempty (GObjMap o' X.univ π)

section API

variable {gb : GBase G R} {g : G.La →ₗ[G.O] G.La} {c k N : ℕ} {s : S ⟶ Sp R} {o : GObj gb (N * k) s}
  {o' : GObj gb N s} {ψ : o.A ⟶ o'.A}

theorem IsGHecke.isMonHom (h : IsGHecke g c k N o o' ψ) : IsMonHom ψ := h.1

theorem IsGHecke.act (h : IsGHecke g c k N o o' ψ) (c' : G.O) : o.act.act c' ≫ ψ = ψ ≫ o'.act.act c' := h.2.1 c'

theorem IsGHecke.eta (h : IsGHecke g c k N o o' ψ) (x : G.La) : o'.eta x = o.eta (g x) ≫ ψ := h.2.2.1 x

theorem IsGHecke.cover (h : IsGHecke g c k N o o' ψ) :
    GlobalTheory.ZM.IsGaloisCover (gHeckeSub o g N) (fun h => (Hecke.transl h.1).left) ψ.left := h.2.2.2.1

theorem IsGHecke.pol (h : IsGHecke g c k N o o' ψ) :
    Nonempty (LBIso (Hecke.lbPow o.P (k ^ 2 / c)) (o'.P.pull (Hecke.sq2 ψ))) := h.2.2.2.2.1

variable {X : GenModel gb N} {X' : GenModel gb (N * k)} {π : X'.X ⟶ X.X}

end API

def GObj.forgetMul {gb : GBase G R} {N k : ℕ} (hN : 0 < N) (hk : 0 < k) {s : S ⟶ Sp R} (o : GObj gb (N * k) s) :
    GObj gb N s where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  rosati := o.rosati
  lie := o.lie
  lieRank := o.lieRank
  eta x := o.eta (k • x)
  eta_add x y := by rw [smul_add, o.eta_add]
  eta_lin c x := by rw [smul_comm, o.eta_lin]
  eta_ker x := by rw [smul_comm, smul_smul, o.eta_ker]
  geom K _ _ x β hx := by
    obtain ⟨I, hI⟩ := o.geom K x β hx
    refine ⟨I, fun y => ?_⟩
    rw [o.eta_nsmul, MonObj.comp_pow, hI, I.tower N k hN hk]

theorem gHeckeSub_smul_id_eq_one {gb : GBase G R} {N k : ℕ} {s : S ⟶ Sp R} (o : GObj gb (N * k) s) :
    ∀ h ∈ gHeckeSub o (k • LinearMap.id) N, h = 1 := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
  exact o.eta_ker x

end GlobalTheory.UPel.HT.Gen
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegJoin

open GlobalTheory.Poinc GlobalTheory.PolDeg

variable {g n : ℕ}

def BlowAt (F : SFam g n (zetaAway n)) {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (φ : InvFun ℤ) (d : ℕ)
    {S : Scheme.{0}} (π : S ⟶ Z) (j : F.X ⟶ S) (BD : EffCartierData S) : Prop :=
  ∃ J : Z.IdealSheafData, 1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range i) ∧ ValOn F i φ J d ∧ IsNormBl π J ∧
    IsProjOver (π ≫ z) ∧ Dense (Set.range j) ∧ j ≫ π = i ∧ π ⁻¹' Set.range i = Set.range j ∧
    BD.idealSheaf = J.comap π ∧ ValOn F j φ BD.idealSheaf d

end GlobalTheory.SiegJoin
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOfPoint
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

structure TautBase (o : Type) [CommRing o] (W : Type) [CommRing W] [IsLocalRing W] where

  b : o →+* W

  B : Over (Sp W)
  [grp : GrpObj B]
  [comm : IsCommMonObj B]
  isAb : IsAbelianScheme B

  g : ℕ
  smoothDim : SmoothOfRelativeDimension g B.hom

  M : RigLB B

  cub : CubicalStr B M
  ample : RelAmple B M.L
  ktriv : KTriv B M.L

  r : ℕ

  c₀ : (Fin r → ℤ) → (𝟙_ (Over (Sp W)) ⟶ B)
  c₀_add : ∀ a a', c₀ (a + a') = c₀ a * c₀ a'

  τ₀ : ∀ a a' : Fin r → ℤ, LB.Gen (LB.LinComb M.L (lamPts (c₀ a) (c₀ a')) negε)
  τ₀_gen : ∀ a a', (τ₀ a a').IsGen
  τ₀_symm : ∀ a a' z J, Good M.L z J → val (τ₀ a a') (𝟙 _) z J = val (τ₀ a' a) (𝟙 _) z J
  τ₀_add : ∀ a a' a'' z J, Good M.L z J →
    val (τ₀ (a + a') a'') (𝟙 _) z J * cubV cub z J (c₀ a) (c₀ a') (c₀ a'') =
      val (τ₀ a a'') (𝟙 _) z J * val (τ₀ a' a'') (𝟙 _) z J

attribute [instance] TautBase.grp TautBase.comm


open InhTate Inh in
def TautBase.torus {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (b : o →+* W) (r : ℕ)
    (u : Γ((𝟙_ (Over (Sp W))).left, ⊤)ˣ) (β : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hβ : ∀ a a', β a a' = β a' a) :
    TautBase o W where
  b := b
  B := (zeroPolAV (Sp W)).A
  comm := (zeroPolAV (Sp W)).isAb.comm
  isAb := (zeroPolAV (Sp W)).isAb
  g := (zeroPolAV (Sp W)).g
  smoothDim := (zeroPolAV (Sp W)).smoothDim
  M := ⟨(zeroPolAV (Sp W)).L, cg _ _ 1, (zeroPolAV (Sp W)).isLB, cg_isGen _ _ 1⟩
  cub :=
    { t := cg _ _ 1
      isGen := cg_isGen _ _ 1
      face := fun _ => corr_of_isConst ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)) (isConst_oneGen _)
      cubeSymmetric_swap_first := corr_of_isConst (cg_isConst _ _ 1) ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
      cubeSymmetric_swap_last := corr_of_isConst (cg_isConst _ _ 1) ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
      cocycle := corr_of_isConst
        ((isConst_mulGen ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
          ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))).of_eq (_root_.mul_one _))
        ((isConst_mulGen ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
          ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))).of_eq (_root_.mul_one _)) }
  ample := (zeroPolAV (Sp W)).ample
  ktriv := (zeroPolAV (Sp W)).ktriv
  r := r
  c₀ := fun _ => toUnit _ ≫ η[(zeroPolAV (Sp W)).A]
  c₀_add := fun _ _ => toUnit_unique _ _
  τ₀ a a' := cg _ _ (u ^ β a a')
  τ₀_gen a a' := cg_isGen _ _ _
  τ₀_symm a a' z J hJ := (gm_res _ z _ (hJ.mem _ _) _).trans
    ((congrArg (fun l : ℤ => gm (𝟙 _) z ⊤ (u ^ l)) (hβ a a')).trans (gm_res _ z _ (hJ.mem _ _) _).symm)
  τ₀_add a a' a'' z J hJ := by
    refine (congrArg₂ (· * ·) (gm_res _ z _ (hJ.mem _ _) _) ((gm_res _ z _ (hJ.mem _ _) _).trans (map_one _))).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (gm_res _ z _ (hJ.mem _ _) _) (gm_res _ z _ (hJ.mem _ _) _)).symm)
    rw [_root_.mul_one, ← map_mul, ← zpow_add, map_add (f := _), LinearMap.add_apply]

def TautBase.ofPolAV {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (b : o →+* W) (P : PolAV (Sp W))
    [IsCommMonObj P.A] (rig : LB.Gen (P.L.pull (eSec P.A))) (hr : rig.IsGen)
    (cub : CubicalStr P.A ⟨P.L, rig, P.isLB, hr⟩) {r : ℕ}
    (c : (Fin r → ℤ) → (𝟙_ (Over (Sp W)) ⟶ P.A)) (hc : ∀ a a', c (a + a') = c a * c a') : TautBase o W :=
  have h := GlobalTheory.TauLocal.exists_tau_local ⟨P.L, rig, P.isLB, hr⟩ cub c hc
  { b := b
    B := P.A
    isAb := P.isAb
    g := P.g
    smoothDim := P.smoothDim
    M := ⟨P.L, rig, P.isLB, hr⟩
    cub := cub
    ample := P.ample
    ktriv := P.ktriv
    r := r
    c₀ := c
    c₀_add := hc
    τ₀ := h.choose
    τ₀_gen := h.choose_spec.1
    τ₀_symm := h.choose_spec.2.1
    τ₀_add := h.choose_spec.2.2 }

theorem TautBase.exists_of_point {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] [IsNoetherianRing W]
    (b : o →+* W) (P : PolAV (Sp W)) (p : 𝟙_ (Over (Sp W)) ⟶ P.A) :
    ∃ (T : TautBase o W) (a : Fin T.r → ℤ), T.B = P.A ∧ T.g = P.g ∧ T.r = 1 ∧ HEq (T.c₀ a) p := by
  obtain ⟨D, α, rfl, h⟩ := GlobalTheory.TwistCompare.exists_degPre P p
  have := D.P.isAb.comm
  refine ⟨TautBase.ofPolAV b D.P D.rig D.rig_gen D.cub (r := 1) (fun a => D.c (a 0 • α))
    (fun a a' => by rw [Pi.add_apply, add_smul, D.c_add]; rfl), fun _ => 1, rfl, rfl, rfl, heq_of_eq ?_⟩
  exact (congrArg D.c (one_smul ℤ α)).trans h

theorem TautBase.exists_ell {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] [IsNoetherianRing W]
    (b : o →+* W) (E : _root_.WeierstrassCurve W) [E.IsElliptic]
    (p : 𝟙_ (Over (Sp W)) ⟶ (GlobalTheory.WeierstrassCurve.ellPolAV E).A) :
    ∃ (T : TautBase o W) (a : Fin T.r → ℤ),
      T.B = (GlobalTheory.WeierstrassCurve.ellPolAV E).A ∧ T.g = 1 ∧ T.r = 1 ∧ HEq (T.c₀ a) p :=
  TautBase.exists_of_point b _ p

theorem TautBase.c₀_zero {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) : T.c₀ 0 = 1 := by
  have h := T.c₀_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

end GlobalTheory.PolDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}

def UValOn (Xo : Moduli D l) (c : Coeff l) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) (φ : InvFun (𝓞 E)) (J : S.IdealSheafData)
    (d : ℕ) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ (χ : Sp W ⟶ S) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ j = jK W ≫ χ →
    ∀ (t : SAB H (Sp W)) (tK : SAB H (Sp (FractionRing W))), Nonempty (SABMap tK t (jK W)) →
      Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∀ P : PELUnif (maximalIdeal W) t,
      ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] →
        ∃ n : ℕ, (n : ℝ) = d * φ.evalZ be ∧ idlAlong J χ = Ideal.span {ϖ ^ n}

def GenOf (Xo : Moduli D l) (c : Coeff l) {R : Type} [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c)
    (t : SAB H (Sp R)) : Prop :=
  ∃ tK : SAB H (Sp (FractionRing R)), Nonempty (SABMap tK t (jK R)) ∧ Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _))

variable {Xo : Moduli D l} {c : Coeff l}

theorem exists_over_iff {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (y : Sp (FractionRing R) ⟶ Xo.XF c) :
    (∃ σ : Sp R ⟶ Sp c.F, jK R ≫ σ = y ≫ pullback.snd _ _) ↔ ∀ n : ℕ, n ≠ 0 → IsUnit (n : R) := by
  constructor
  · rintro ⟨σ, -⟩ n hn
    have := (IsUnit.mk0 (n : c.F) (Nat.cast_ne_zero.2 hn)).map (Spec.preimage σ).hom
    rwa [map_natCast] at this
  · intro hu
    haveI := c.fin
    let g : c.F →+* FractionRing R := (Spec.preimage (y ≫ pullback.snd _ _)).hom
    have hint : ∀ a : c.F, ∃ r : R, algebraMap R (FractionRing R) r = g a := fun a => by
      obtain ⟨m, hm, ha⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2
        (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple
      have hint : IsIntegral R (g (m • a)) := by
        obtain ⟨p, hp, h0⟩ := ha
        refine ⟨p.map (Int.castRingHom R), hp.map _, ?_⟩
        rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap R (FractionRing R)).comp (Int.castRingHom R))
          (g.comp (algebraMap ℤ c.F)), ← Polynomial.hom_eval₂, h0, map_zero]
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
      have hum : IsUnit (m : R) := by
        have := hu m.natAbs (by simpa using hm)
        rcases Int.natAbs_eq m with e | e <;> rw [e] <;> simpa using this
      obtain ⟨u, hu'⟩ := hum
      refine ⟨(↑u⁻¹ : R) * r, ?_⟩
      have e : g (m • a) = algebraMap R (FractionRing R) u * g a := by simp [hu']
      rw [map_mul, hr, e, ← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
    choose f hf using hint
    have hi := IsFractionRing.injective R (FractionRing R)
    let b : c.F →+* R :=
      { toFun := f
        map_one' := hi (by simp [hf])
        map_mul' := fun _ _ => hi (by simp [hf])
        map_zero' := hi (by simp [hf])
        map_add' := fun _ _ => hi (by simp [hf]) }
    refine ⟨spMap b, ?_⟩
    rw [← Spec.map_preimage (y ≫ pullback.snd _ _), ← Spec.map_comp]
    congr 1
    ext a
    exact hf a

end GlobalTheory.UPoinc
end
end
