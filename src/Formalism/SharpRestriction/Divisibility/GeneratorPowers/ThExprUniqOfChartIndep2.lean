module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def ChartIndepSt2 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (C C' : ChartAt Xo c y) (k n : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
    (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S) (f' : Fin n → MvPowerSeries (Fin 1 × Fin C'.d) S),
    (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) →
    (∀ b, IsGerm y C'.d C'.x C'.B.A.act C'.e C'.wP k (F b) (f' b)) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      chartVal C k f P = chartVal C' k f' P

theorem thExprUniq_of_chartIndep2 (hC : ChartIndepSt2) : ThExprUniqSt := by
  intro E _ _ _ H Dw l Xo c _ nab₁ nab₂ h₁ h₂ S _ _ _ y k n F a P hP
  obtain ⟨C₁, hex₁, hpin₁⟩ := h₁.2 S y
  obtain ⟨C₂, hex₂, hpin₂⟩ := h₂.2 S y
  choose f₁ hf₁ using fun b => hex₁ k (F b)
  choose f₂ hf₂ using fun b => hex₂ k (F b)
  have e₁ : ∀ m, ∏ b, nab₁ y k (F b) (colOf m b) =
      ∏ b, C₁.B.nabVal S C₁.h H.w0 k (f₁ b) C₁.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin₁ k (F b) (f₁ b) (hf₁ b) (colOf m b)
  have e₂ : ∀ m, ∏ b, nab₂ y k (F b) (colOf m b) =
      ∏ b, C₂.B.nabVal S C₂.h H.w0 k (f₂ b) C₂.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin₂ k (F b) (f₂ b) (hf₂ b) (colOf m b)
  have h := hC E H Dw l Xo c h₁.1 S y C₁ C₂ k n F f₁ f₂ hf₁ hf₂ a P hP
  simp only [chartVal] at h
  simp only [e₁, e₂]
  exact h

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)

attribute [local instance] Over.cartesianMonoidalCategory

section Rel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

def FrTrunc (e : ∀ m, FrTyG t x0 d x m) : Prop :=
  ∀ m, LB.Gen.Corr t.PP.L _ _ _ _
    (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x (m + 1) (0 : Fin 2), jptG t x0 d x (m + 1) (1 : Fin 2)]) (cε 2) (e (m + 1))
      (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left)
    (e m)

def FrAxes (e : ∀ m, FrTyG t x0 d x m) : Prop :=
  ∀ m, LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m)
        (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d =>
          (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S)
            p.1 p.2)).left)
      (LB.oneGen t.PP.L) ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m)
        (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d =>
          (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun _ => 0] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S)
            p.1 p.2)).left)
      (LB.oneGen t.PP.L)

def Rig0G (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t) :
    Prop :=
  LB.Gen.Corr t.PP.L _ _ _ _
    (LB.pullGen t.PP.L _ _ (eLG t x0 d x act e wP 0) (homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left)
    (rigT t.G t.PP.L t.PP.rig (overAt x0 S) 1)

end Rel

section Ids

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O]

structure AxesOK (ph1 ph2 : PS R 3 d) (sy : PS R 2 d) (ad : O → PS R 2 d) : Prop where
  cocycleLeft_zero_fst : ev (n := 2) ![0, pt R d 0, pt R d 1] ph1 = 1
  cocycleLeft_zero_snd : ev (n := 2) ![pt R d 0, 0, pt R d 1] ph1 = 1
  cocycleLeft_zero_thd : ev (n := 2) ![pt R d 0, pt R d 1, 0] ph1 = 1
  cocycleRight_zero_fst : ev (n := 2) ![0, pt R d 0, pt R d 1] ph2 = 1
  cocycleRight_zero_snd : ev (n := 2) ![pt R d 0, 0, pt R d 1] ph2 = 1
  cocycleRight_zero_thd : ev (n := 2) ![pt R d 0, pt R d 1, 0] ph2 = 1
  symmetry_zero_fst : ev (n := 1) ![0, pt R d 0] sy = 1
  symmetry_zero_snd : ev (n := 1) ![pt R d 0, 0] sy = 1
  ad_c : ∀ a, MvPowerSeries.constantCoeff (ad a) = 1

structure FBRest [StarRing O] (G : FGLaw R d) (A : Germ.OAct O G) (ph1 ph2 : PS R 3 d) (sy : PS R 2 d)
    (ad : O → PS R 2 d) : Prop where
  adjoint_zero_fst : ∀ a, ev (n := 1) ![0, pt R d 0] (ad a) = 1
  adjoint_zero_snd : ∀ a, ev (n := 1) ![pt R d 0, 0] (ad a) = 1

  cocycleLeft_assoc :
    ev (n := 4) ![pt R d 0, pt R d 1, pt R d 3] ph1 *
        ev (n := 4) ![G.add (pt R d 0) (pt R d 1), pt R d 2, pt R d 3] ph1 =
      ev (n := 4) ![pt R d 1, pt R d 2, pt R d 3] ph1 *
        ev (n := 4) ![pt R d 0, G.add (pt R d 1) (pt R d 2), pt R d 3] ph1

  cocycleLeft_comm : ev (n := 3) ![pt R d 1, pt R d 0, pt R d 2] ph1 = ph1

  cocycleRight_assoc :
    ev (n := 4) ![pt R d 0, pt R d 1, pt R d 2] ph2 *
        ev (n := 4) ![pt R d 0, G.add (pt R d 1) (pt R d 2), pt R d 3] ph2 =
      ev (n := 4) ![pt R d 0, pt R d 2, pt R d 3] ph2 *
        ev (n := 4) ![pt R d 0, pt R d 1, G.add (pt R d 2) (pt R d 3)] ph2

  cocycleRight_comm : ev (n := 3) ![pt R d 0, pt R d 2, pt R d 1] ph2 = ph2

  interchange :
    ev (n := 4) ![pt R d 0, pt R d 1, pt R d 2] ph1 * ev (n := 4) ![pt R d 0, pt R d 1, pt R d 3] ph1 *
        ev (n := 4) ![G.add (pt R d 0) (pt R d 1), pt R d 2, pt R d 3] ph2 =
      ev (n := 4) ![pt R d 0, pt R d 2, pt R d 3] ph2 * ev (n := 4) ![pt R d 1, pt R d 2, pt R d 3] ph2 *
        ev (n := 4) ![pt R d 0, pt R d 1, G.add (pt R d 2) (pt R d 3)] ph1

  sy_inv : sy * ev (n := 2) ![pt R d 1, pt R d 0] sy = 1

  sy_law :
    ph2 * ev (n := 3) ![pt R d 0, pt R d 1] sy * ev (n := 3) ![pt R d 0, pt R d 2] sy =
      ev (n := 3) ![pt R d 0, G.add (pt R d 1) (pt R d 2)] sy * ev (n := 3) ![pt R d 1, pt R d 2, pt R d 0] ph1

  adjoint_compat_left : ∀ a : O,
    ev (n := 3) ![comp1 (A.act a) (pt R d 0), comp1 (A.act a) (pt R d 1), pt R d 2] ph1 *
        ev (n := 3) ![G.add (pt R d 0) (pt R d 1), pt R d 2] (ad a) =
      ev (n := 3) ![pt R d 0, pt R d 2] (ad a) * ev (n := 3) ![pt R d 1, pt R d 2] (ad a) *
        ev (n := 3) ![pt R d 0, pt R d 1, comp1 (A.act (star a)) (pt R d 2)] ph1

  adjoint_compat_right : ∀ a : O,
    ev (n := 3) ![comp1 (A.act a) (pt R d 0), pt R d 1, pt R d 2] ph2 *
        ev (n := 3) ![pt R d 0, G.add (pt R d 1) (pt R d 2)] (ad a) =
      ev (n := 3) ![pt R d 0, pt R d 1] (ad a) * ev (n := 3) ![pt R d 0, pt R d 2] (ad a) *
        ev (n := 3) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1),
          comp1 (A.act (star a)) (pt R d 2)] ph2
  ad_one : ad 1 = 1

  ad_mul : ∀ a b : O, ad (a * b) =
    ev (n := 2) ![comp1 (A.act b) (pt R d 0), pt R d 1] (ad a) *
      ev (n := 2) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1)] (ad b)

  ad_add : ∀ a b : O,
    ev (n := 2) ![comp1 (A.act a) (pt R d 0), comp1 (A.act b) (pt R d 0), pt R d 1] ph1 * ad (a + b) =
      ad a * ad b *
        ev (n := 2) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1), comp1 (A.act (star b)) (pt R d 1)] ph2

  ad_sy : ∀ a : O,
    ad a * ev (n := 2) ![pt R d 1, pt R d 0] (ad (star a)) *
        ev (n := 2) ![comp1 (A.act a) (pt R d 0), pt R d 1] sy =
      ev (n := 2) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1)] sy

def mkFB [StarRing O] (G : FGLaw R d) (A : Germ.OAct O G) (ph1 ph2 : PS R 3 d) (sy : PS R 2 d)
    (ad : O → PS R 2 d) (ha : AxesOK ph1 ph2 sy ad) (hr : FBRest G A ph1 ph2 sy ad) : Germ.FB R d O :=
  { G := G, A := A, ph1 := ph1, ph2 := ph2, sy := sy, ad := ad,
    cocycleLeft_zero_fst := ha.cocycleLeft_zero_fst, cocycleLeft_zero_snd := ha.cocycleLeft_zero_snd, cocycleLeft_zero_thd := ha.cocycleLeft_zero_thd,
    cocycleRight_zero_fst := ha.cocycleRight_zero_fst, cocycleRight_zero_snd := ha.cocycleRight_zero_snd, cocycleRight_zero_thd := ha.cocycleRight_zero_thd,
    symmetry_zero_fst := ha.symmetry_zero_fst, symmetry_zero_snd := ha.symmetry_zero_snd, adjoint_zero_fst := hr.adjoint_zero_fst, adjoint_zero_snd := hr.adjoint_zero_snd,
    cocycleLeft_assoc := hr.cocycleLeft_assoc, cocycleLeft_comm := hr.cocycleLeft_comm, cocycleRight_assoc := hr.cocycleRight_assoc, cocycleRight_comm := hr.cocycleRight_comm,
    interchange := hr.interchange, sy_inv := hr.sy_inv, sy_law := hr.sy_law, adjoint_compat_left := hr.adjoint_compat_left,
    adjoint_compat_right := hr.adjoint_compat_right, ad_one := hr.ad_one, ad_mul := hr.ad_mul, ad_add := hr.ad_add, ad_sy := hr.ad_sy }

end Ids

def FrameSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0)
    (S : Type) [CommRing S] [IsLocalRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (G : FGLaw S d) (A : Germ.OAct (𝓞 E) G)
    (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G), IsChartG t x0 d G.F A.act tg uvec x →
    ∃ (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d) (ad : 𝓞 E → PS S 2 d),
      IsFrameG t x0 d x G.F A.act ph1 ph2 sy ad e ∧ IsPrimG t wP ∧ FrTrunc t x0 d x e ∧ FrAxes t x0 d x e ∧
        (∀ a, MvPowerSeries.constantCoeff (ad a) = 1) ∧ Rig0G t x0 d x A.act e wP

def FBIdSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0),
    (∀ n, Function.Bijective (ReciprocityTheory.ChartRestriction.G.Out.powObj t.G n).hom.appTop.hom) → ∀ [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (G : FGLaw S d) (A : Germ.OAct (𝓞 E) G)
    (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (e : ∀ m, FrTyG t x0 d x m) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d)
    (ad : 𝓞 E → PS S 2 d), IsChartG t x0 d G.F A.act tg uvec x →
    IsFrameG t x0 d x G.F A.act ph1 ph2 sy ad e → FrAxes t x0 d x e → (∀ a, MvPowerSeries.constantCoeff (ad a) = 1) →
      AxesOK ph1 ph2 sy ad ∧ FBRest G A ph1 ph2 sy ad

def GermSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0)
    (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d) (ad : 𝓞 E → PS S 2 d)
    (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t), IsChartG t x0 d F act tg uvec x →
    IsFrameG t x0 d x F act ph1 ph2 sy ad e → IsPrimG t wP → FrTrunc t x0 d x e →
    ∀ (k : ℕ) (Fs : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))), ∃ f, IsGermG t x0 d x act e wP k Fs f

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S]

def compL {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (g : MvPowerSeries (Fin 1 × Fin d) S) :
    MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  MvPowerSeries.subst (fun p : Fin 1 × Fin d => φ p.2) g

def atPt {n : ℕ} (b : Fin n) (g : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) :
    MvPowerSeries (Fin n × Fin (dL Dw)) S :=
  MvPowerSeries.subst (fun q : Fin 1 × Fin (dL Dw) => (MvPowerSeries.X (b, q.2) : MvPowerSeries (Fin n × Fin (dL Dw)) S)) g

structure IsExpOf {d : ℕ} (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (uvec : Lt1 Dw → Fin d → S)
    (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) : Prop where
  const : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0
  lin : ∀ ℓ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1) (φ j) = uvec ℓ j
  hom : ∀ j, MvPowerSeries.subst (fun p : Fin 2 × Fin d => atPt p.1 (φ p.2)) (F j) =
    MvPowerSeries.subst (fun q : Fin 1 × Fin (dL Dw) =>
      (MvPowerSeries.X ((0 : Fin 2), q.2) + MvPowerSeries.X ((1 : Fin 2), q.2) :
        MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) (φ j)

variable [Algebra c.F S] [Algebra ℚ S] [StarRing (𝓞 E)]

def jφ {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m :=
  jetSubstPS (fun p : Fin 1 × Fin d => φ p.2)

def xExp (y : FrPt Xo c S) (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    jO y (dL Dw) m 1 ⟶ Xo.univ.t.G :=
  homAt y.x (jφ φ m) ≫ C.x m

def FrTruncC (y : FrPt Xo c S) (C : ChartAt Xo c y) : Prop :=
  ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ (C.e (m + 1))
      (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m)).left)
    (C.e m)

def IsExpGaugeOf (y : FrPt Xo c S) (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (e : ∀ m, ExpFr y (xExp y C φ) m) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ,
    (u : Jet S (Fin 1 × Fin (dL Dw)) m) = psJet m (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0)))) ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e m)
      (scaleGen _ _ (unitΓ u) (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act C.e C.wP m)
        (homAt y.x (jφ φ m)).left))

end Defs

def ExpChartOfSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y),
    ∃ φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S, IsExpOf C.B.G.F C.uvec φ ∧ IsExpChart y (xExp y C φ)

def ExpGaugeOfSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y), FrTruncC y C →
    ∀ (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ → IsExpChart y (xExp y C φ) →
      ∃ e : ∀ m, ExpFr y (xExp y C φ) m, IsExpGauge y (xExp y C φ) e ∧ IsExpGaugeOf y C φ e

def TieSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
    (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ →
    ∀ e : ∀ m, ExpFr y (xExp y C φ) m, IsExpGaugeOf y C φ e →
    ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
      (f : MvPowerSeries (Fin 1 × Fin C.d) S), IsGerm y C.d C.x C.B.A.act C.e C.wP k F f →
      ∃ g : MvPowerSeries (Fin 1 × Fin (dL Dw)) S, IsExpGerm y (xExp y C φ) e k F g ∧
        ∀ α : Lt1 Dw →₀ ℕ, C.B.nabVal S C.h H.w0 k f C.uvec (MvPolynomial.monomial α 1) = expVal g α

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

open AlgebraicGeometry CategoryTheory MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Alg

variable {R : Type} [CommRing R] {ι : Type} {m : ℕ}

theorem jetMap_mk {ι' : Type} (φ : ι → MvPolynomial ι' R) (hφ : ∀ i, φ i ∈ orig R ι') (p : MvPolynomial ι R) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (aeval φ p) := rfl

theorem jetTrunc_mk (p : MvPolynomial ι R) :
    (jetTrunc : Jet R ι (m + 1) →ₐ[R] Jet R ι m) (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ p := rfl

theorem jet_hom_ext {B : Type} [CommRing B] [Algebra R B] {f g : Jet R ι m →ₐ[R] B}
    (h : ∀ i, f (Ideal.Quotient.mk _ (X i)) = g (Ideal.Quotient.mk _ (X i))) : f = g :=
  Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun i => h i)

private theorem deg_sum_lemma {κ : Type} (e : κ →₀ ℕ) : e.degree = ∑ i ∈ e.support, e i := by
  first
  | rfl
  | simp [Finsupp.degree]
  | exact Finsupp.degree_apply e

theorem monomial_mem_orig_pow (e : ι →₀ ℕ) (c : R) : monomial e c ∈ orig R ι ^ e.degree := by
  classical
  rw [MvPolynomial.monomial_eq, Finsupp.prod]
  refine Ideal.mul_mem_left _ _ ?_
  rw [deg_sum_lemma e, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (X_mem_orig i) _

theorem mem_orig_pow_of {n : ℕ} {p : MvPolynomial ι R} (h : ∀ e ∈ p.support, n ≤ e.degree) :
    p ∈ orig R ι ^ n := by
  rw [p.as_sum]
  exact Ideal.sum_mem _ fun e he => Ideal.pow_le_pow_right (h e he) (monomial_mem_orig_pow e _)

private theorem mem_degLE_lemma [Fintype ι] [DecidableEq ι] (k : ℕ) (e : ι →₀ ℕ) :
    e ∈ degLE k ↔ e.degree ≤ k := by
  unfold degLE
  rw [Finset.mem_filter, deg_sum_lemma]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨Finset.mem_image.2 ⟨fun i => ⟨e i, ?_⟩, Finset.mem_univ _, ?_⟩, h⟩
    · have hle : e i ≤ ∑ j ∈ e.support, e j := by
        by_cases hi : i ∈ e.support
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        · have h0 : e i = 0 := by simpa [Finsupp.mem_support_iff] using hi
          rw [h0]
          exact Nat.zero_le _
      omega
    · ext i
      simp

private theorem coeff_psTrunc_lemma_2 [Fintype ι] [DecidableEq ι] (k : ℕ) (g : MvPowerSeries ι R)
    (e : ι →₀ ℕ) :
    AddMonoidAlgebra.coeff (psTrunc k g) e = if e.degree ≤ k then MvPowerSeries.coeff e g else 0 := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : e.degree ≤ k
  · rw [if_pos ((mem_degLE_lemma k e).2 h), if_pos h]
  · rw [if_neg (mt (mem_degLE_lemma k e).1 h), if_neg h]

theorem psTrunc_succ_sub [Fintype ι] [DecidableEq ι] (g : MvPowerSeries ι R) :
    psTrunc (m + 1) g - psTrunc m g ∈ orig R ι ^ (m + 1) := by
  apply mem_orig_pow_of
  intro e he
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, coeff_psTrunc_lemma_2, coeff_psTrunc_lemma_2] at he
  by_contra hlt
  have h1 : e.degree ≤ m := by omega
  rw [if_pos h1, if_pos (by omega : e.degree ≤ m + 1), sub_self] at he
  exact he rfl

theorem exists_ps_of_jets [Fintype ι] [DecidableEq ι] (a : ∀ m, Jet R ι m)
    (ha : ∀ m, (jetTrunc : Jet R ι (m + 1) →ₐ[R] Jet R ι m) (a (m + 1)) = a m) :
    ∃ f : MvPowerSeries ι R, ∀ m, psJet m f = a m := by
  choose p hp using fun k => Ideal.Quotient.mk_surjective (a k)
  have hc : ∀ k l, k ≤ l → p l - p k ∈ orig R ι ^ (k + 1) := by
    intro k l hkl
    induction l, hkl using Nat.le_induction with
    | base => simp
    | succ l hkl ih =>
      have h1 : p (l + 1) - p l ∈ orig R ι ^ (l + 1) := by
        rw [← Ideal.Quotient.eq]
        have h := ha l
        rw [← hp (l + 1), ← hp l, jetTrunc_mk] at h
        exact h
      have h2 : orig R ι ^ (l + 1) ≤ orig R ι ^ (k + 1) := Ideal.pow_le_pow_right (by omega)
      have h3 := Ideal.add_mem _ (h2 h1) ih
      rwa [sub_add_sub_cancel] at h3
  obtain ⟨f, hf⟩ : ∃ f : MvPowerSeries ι R, ∀ e, MvPowerSeries.coeff e f = AddMonoidAlgebra.coeff (p e.degree) e :=
    ⟨fun e => AddMonoidAlgebra.coeff (p e.degree) e, fun e => rfl⟩
  refine ⟨f, fun k => ?_⟩
  rw [← hp k]
  unfold psJet
  rw [Ideal.Quotient.eq]
  apply mem_orig_pow_of
  intro e he
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, coeff_psTrunc_lemma_2] at he
  by_contra hlt
  have h1 : e.degree ≤ k := by omega
  rw [if_pos h1] at he
  apply he
  have h3 := coeff_eq_zero_of_mem (hc e.degree k h1) (by omega : e.degree < e.degree + 1)
  rw [MvPolynomial.coeff_sub, sub_eq_zero] at h3
  rw [hf, sub_eq_zero]
  exact h3.symm

end Alg

section Subst

variable {R : Type} [CommRing R] {d : ℕ}

abbrev sL (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) R) :
    Jet R (Fin 2 × Fin d) m →ₐ[R] Jet R (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => X ((0 : Fin 1), j), fun j => psIn d m ![0] (g j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) R) p.1 p.2

theorem power_series_in_fin_one (m : ℕ) (g : MvPowerSeries (Fin 1 × Fin d) R) : psIn d m ![0] g = psTrunc m g := by
  unfold psIn
  have h : (fun p : Fin 1 × Fin d => ((![0] : Fin 1 → Fin 1) p.1, p.2)) = id := by
    funext p
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [h]
  simp

theorem sL_copy0 (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) R) :
    (sL m g).comp (jetCopy d m (0 : Fin 2)) = AlgHom.id R _ := by
  apply jet_hom_ext
  rintro ⟨i1, j⟩
  obtain rfl : i1 = 0 := Subsingleton.elim _ _
  simp [sL, jetSubstP, jetCopy, jetMap_mk]

theorem sL_copy1 (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) R) :
    (sL m g).comp (jetCopy d m (1 : Fin 2)) = jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (g p.2) := by
  apply jet_hom_ext
  rintro ⟨i1, j⟩
  obtain rfl : i1 = 0 := Subsingleton.elim _ _
  simp [sL, jetSubstP, jetCopy, jetMap_mk, power_series_in_fin_one]

private theorem const_psTrunc_lemma_3 {κ : Type} [Fintype κ] [DecidableEq κ] (k : ℕ) (g : MvPowerSeries κ R) :
    MvPolynomial.constantCoeff (psTrunc k g) = MvPowerSeries.coeff 0 g := by
  rw [show MvPolynomial.constantCoeff (psTrunc k g) = AddMonoidAlgebra.coeff (psTrunc k g) 0 from rfl,
    coeff_psTrunc_lemma_2, if_pos (by simp)]

theorem sL_trunc (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) R) :
    (jetTrunc : Jet R (Fin 1 × Fin d) (m + 1) →ₐ[R] _).comp (sL (m + 1) g) =
      (sL m g).comp (jetTrunc : Jet R (Fin 2 × Fin d) (m + 1) →ₐ[R] _) := by
  apply jet_hom_ext
  rintro ⟨k, j⟩
  simp only [AlgHom.comp_apply, jetTrunc_mk, sL, jetSubstP, jetMap_mk, MvPolynomial.aeval_X]
  rw [Ideal.Quotient.eq]
  fin_cases k
  · simp
  · simp only [power_series_in_fin_one, Matrix.cons_val_one, Matrix.head_cons]
    change psTrunc (m + 1) (g j) - C (MvPolynomial.constantCoeff (psTrunc (m + 1) (g j))) -
      (psTrunc m (g j) - C (MvPolynomial.constantCoeff (psTrunc m (g j)))) ∈ _
    rw [const_psTrunc_lemma_3, const_psTrunc_lemma_3, sub_sub_sub_cancel_right]
    exact psTrunc_succ_sub (g j)

theorem copy_trunc (m : ℕ) (i : Fin 2) :
    (jetTrunc : Jet R (Fin 2 × Fin d) (m + 1) →ₐ[R] _).comp (jetCopy d (m + 1) i) =
      (jetCopy d m i).comp (jetTrunc : Jet R (Fin 1 × Fin d) (m + 1) →ₐ[R] _) := by
  apply jet_hom_ext
  intro p
  simp [jetCopy, jetMap_mk, jetTrunc_mk]

end Subst

section Over

variable {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X)

theorem homAt_comp {A B C : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] [CommRing C] [Algebra S C]
    (f : A →ₐ[S] B) (g : B →ₐ[S] C) : homAt x0 g ≫ homAt x0 f = homAt x0 (g.comp f) := by
  apply Over.OverMorphism.ext
  simp [homAt, spMap, ← Spec.map_comp]
  rfl

theorem homAt_id {A : Type} [CommRing A] [Algebra S A] : homAt x0 (AlgHom.id S A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp [homAt, spMap]

end Over

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PrimUniqPf
section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PrimUniqSt
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def PrimUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (wP wP' : PrimTy H Xo), IsPrim wP → IsPrim wP' → wP = wP'

def PrimUniqOfGlobalSt : Prop :=
  GlobalFnsSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l), IsAbelianScheme Xo.univ.t.G →
    ∀ wP wP' : PrimTy H Xo, IsPrim wP → IsPrim wP' → wP = wP'

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField TopologicalSpace Opposite MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem isAbelianScheme_of_proper {S : Scheme.{0}} (G : Over S) [GrpObj G] (hs : IsSemiAbelian G)
    (hp : IsProper G.hom) : IsAbelianScheme G := ⟨hs.comm, hs.smooth, hp, hs.geomConnected⟩

theorem isAbelianScheme_univ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) : IsAbelianScheme Xo.univ.t.G := isAbelianScheme_of_proper _ Xo.univ.t.semi Xo.univ.proper

theorem wchart_cover {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) : (⊤ : Y.Opens) ≤ ⨆ j, LB.wchart L φ j := by
  intro y _
  have hk : ∀ k, ∃ i, (φ k).base y ∈ L.U i := fun k => by
    have hy : (φ k).base y ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using hy
  choose j hj using hk
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩
  show y ∈ ⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X)
  exact Set.mem_iInter.2 fun k => hj k

theorem gen_ratio {Y : Scheme.{0}} (M : LB Y) (hcov : (⊤ : Y.Opens) ≤ ⨆ j, M.U j)
    (t t' : LB.Gen M) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ u : Γ(Y, ⊤)ˣ, ∀ j, t.s j = res (le_top : M.U j ≤ ⊤) u * t'.s j := by
  classical
  let r : ∀ j, Γ(Y, M.U j)ˣ := fun j => t.s j / t'.s j
  have hcompat : ∀ i j, res (inf_le_left : M.U i ⊓ M.U j ≤ M.U i) (r i) =
      res (inf_le_right : M.U i ⊓ M.U j ≤ M.U j) (r j) := by
    intro i j
    simp only [r, map_div, ht i j, ht' i j, mul_div_mul_left_eq_div]
  have hcompat' : ∀ i j, res (inf_le_left : M.U i ⊓ M.U j ≤ M.U i) (r i)⁻¹ =
      res (inf_le_right : M.U i ⊓ M.U j ≤ M.U j) (r j)⁻¹ := by
    intro i j
    rw [map_inv, map_inv, hcompat i j]
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' M.U ⊤ (fun j => homOfLE le_top) hcov
    (fun j => ((r j : Γ(Y, M.U j)ˣ) : Γ(Y, M.U j))) (fun i j => congrArg Units.val (hcompat i j))
  obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' M.U ⊤ (fun j => homOfLE le_top) hcov
    (fun j => (((r j)⁻¹ : Γ(Y, M.U j)ˣ) : Γ(Y, M.U j))) (fun i j => congrArg Units.val (hcompat' i j))
  have hab : a * b = 1 := by
    refine Y.sheaf.eq_of_locally_eq' M.U ⊤ (fun j => homOfLE le_top) hcov _ _ fun j => ?_
    change (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom (a * b) =
      (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom 1
    erw [map_mul, map_one]
    have e1 := ha j
    have e2 := hb j
    change (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom a = ((r j : Γ(Y, M.U j)ˣ) : Γ(Y, M.U j)) at e1
    change (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom b =
      (((r j)⁻¹ : Γ(Y, M.U j)ˣ) : Γ(Y, M.U j)) at e2
    rw [e1, e2, Units.mul_inv]
  refine ⟨⟨a, b, hab, by erw [mul_comm]; exact hab⟩, fun j => ?_⟩
  have hres : res (le_top : M.U j ≤ ⊤) ⟨a, b, hab, by erw [mul_comm]; exact hab⟩ = r j :=
    Units.ext (ha j)
  rw [hres]
  simp only [r, div_mul_cancel]

private theorem res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V)
    (x : Γ(X, U)ˣ) : res h2 (res h1 x) = res (h2.trans h1) x := by
  apply Units.ext
  change ((X.presheaf.map (homOfLE h1).op ≫ X.presheaf.map (homOfLE h2).op).hom (x : Γ(X, U))) = _
  rw [← Functor.map_comp]
  rfl

theorem pull_res_val {X Y : Scheme.{0}} (h : Y ⟶ X) {V : X.Opens} {W : Y.Opens} (hWV : W ≤ h ⁻¹ᵁ V)
    (u : Γ(X, ⊤)ˣ) :
    ((res hWV (pullU h V (res (le_top : V ≤ ⊤) u)) : Γ(Y, W)ˣ) : Γ(Y, W)) =
      (Y.presheaf.map (homOfLE (le_top : W ≤ h ⁻¹ᵁ ⊤)).op).hom ((h.app ⊤).hom (u : Γ(X, ⊤))) := by
  rw [ReciprocityTheory.ChartRestriction.G.DVR.pullU_res, res_res_lemma]
  rfl

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)ˣ) :
    res h2 (res h1 x) = res (h2.trans h1) x := by
  exact res_res_lemma h1 h2 x

theorem pull_restrict_unit_value {X Y : Scheme.{0}} (h : Y ⟶ X) {V : X.Opens} {W W' : Y.Opens} (hWV : W ≤ h ⁻¹ᵁ V)
    (hW' : W' ≤ W) (u : Γ(X, ⊤)ˣ) :
    ((res hW' (res hWV (pullU h V (res (le_top : V ≤ ⊤) u))) : Γ(Y, W')ˣ) : Γ(Y, W')) =
      (Y.presheaf.map (homOfLE (le_top : W' ≤ h ⁻¹ᵁ ⊤)).op).hom ((h.app ⊤).hom (u : Γ(X, ⊤))) := by
  rw [res_res, pull_res_val]

theorem unit_sec {S : Scheme.{0}} : ∃ ι : S ⟶ (𝟙_ (Over S)).left, ι ≫ (𝟙_ (Over S)).hom = 𝟙 S := ⟨(CartesianMonoidalCategory.toUnit (Over.mk (𝟙 S))).left, by
  simpa using Over.w (CartesianMonoidalCategory.toUnit (Over.mk (𝟙 S)))⟩

theorem pull_unit_eq_one {X Y S0 : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : S0 ⟶ Y) (ψ : S0 ⟶ X)
    (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => 1))
    (t t' : LB.Gen (LB.LinComb L φ ε)) (u : Γ(Y, ⊤)ˣ)
    (hu : ∀ j, t.s j = res (le_top : (LB.LinComb L φ ε).U j ≤ ⊤) u * t'.s j)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t h) rig)
    (hc' : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t' h) rig) :
    (h.app ⊤).hom (u : Γ(Y, ⊤)) = 1 := by
  classical
  have hpt : ∀ (m : S0 ⟶ X) (z : S0), ∃ i, m.base z ∈ L.U i := fun m z => by
    have hz : m.base z ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using hz
  let c : S0 → (S0 ⟶ X) → L.ι := fun z m =>
    if m = ψ then (hpt ψ z).choose else (hpt m z).choose
  have hc_mem : ∀ z m, m.base z ∈ L.U (c z m) := by
    intro z m
    simp only [c]
    split_ifs with hm
    · subst hm; exact (hpt _ z).choose_spec
    · exact (hpt m z).choose_spec
  let j : S0 → K → L.ι := fun z k => c z (h ≫ φ k)
  let j' : S0 → PUnit → L.ι := fun z _ => c z ψ
  let W : S0 → S0.Opens := fun z =>
    LB.wchart L (fun k => h ≫ φ k) (j z) ⊓ LB.wchart L (fun _ : PUnit => ψ) (j' z)
  have hzW : ∀ z, z ∈ W z := fun z =>
    ⟨Set.mem_iInter.2 fun k => hc_mem z _, Set.mem_iInter.2 fun _ => hc_mem z ψ⟩
  have hone : ∀ z, (S0.presheaf.map (homOfLE (le_top : W z ≤ h ⁻¹ᵁ ⊤)).op).hom
      ((h.app ⊤).hom (u : Γ(Y, ⊤))) = 1 := by
    intro z
    have hcoh : LB.Coh L (fun k => h ≫ φ k) (j z) := fun k1 k2 e => congrArg (c z) e
    have hcoh' : LB.Coh L (fun _ : PUnit => ψ) (j' z) := fun _ _ _ => rfl
    have hcomp : ∀ k k', (fun k => h ≫ φ k) k = (fun _ : PUnit => ψ) k' → j z k = j' z k' :=
      fun k k' e => congrArg (c z) e
    have e := (hc (j z) (j' z) hcoh hcoh' hcomp).trans (hc' (j z) (j' z) hcoh hcoh' hcomp).symm
    simp only [LB.pullGen] at e
    rw [hu (j z)] at e
    simp only [map_mul] at e
    erw [map_mul] at e
    have e2 := mul_eq_right.mp e
    have e3 := congrArg Units.val e2
    have hWV : LB.wchart L (fun k => h ≫ φ k) (j z) ≤ h ⁻¹ᵁ LB.wchart L φ (j z) :=
      fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
    exact (pull_restrict_unit_value h (W' := W z) hWV inf_le_left u).symm.trans (e3.trans Units.val_one)
  refine S0.sheaf.eq_of_locally_eq' W (h ⁻¹ᵁ ⊤) (fun z => homOfLE le_top) ?_ _ _ ?_
  · intro z _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨z, hzW z⟩
  · intro z
    change (S0.presheaf.map (homOfLE (le_top : W z ≤ h ⁻¹ᵁ ⊤)).op).hom
      ((h.app ⊤).hom (u : Γ(Y, ⊤))) = (S0.presheaf.map (homOfLE (le_top : W z ≤ h ⁻¹ᵁ ⊤)).op).hom 1
    rw [hone z, map_one]

theorem primUniqOfGlobal_holds : PrimUniqOfGlobalSt := by
  intro hglob E _ _ _ H Dw l Xo hab wP wP' hP hP'
  obtain ⟨u, hu⟩ := gen_ratio _ (wchart_cover Xo.univ.t.PP.L Xo.univ.t.PP.isLB _) wP wP' hP.1 hP'.1
  have h1 := pull_unit_eq_one Xo.univ.t.PP.L Xo.univ.t.PP.isLB _ _ (eSec Xo.univ.t.G) (eSec Xo.univ.t.G)
    Xo.univ.t.PP.rig wP wP' u hu hP.2 hP'.2
  have hu1 : u = 1 := by
    obtain ⟨ι, hι⟩ := unit_sec (S := Xo.X)
    obtain ⟨c, hc⟩ := (hglob _ _ hab).2 (u : Γ(Xo.univ.t.G.left, ⊤))
    have e1 : eSec Xo.univ.t.G ≫ Xo.univ.t.G.hom = (𝟙_ (Over Xo.X)).hom := Over.w _
    have hc1 : c = 1 := by
      calc c = (ι ≫ (𝟙_ (Over Xo.X)).hom).appTop.hom c := by rw [hι]; simp
        _ = ι.appTop.hom ((eSec Xo.univ.t.G).appTop.hom (Xo.univ.t.G.hom.appTop.hom c)) := by
            rw [← e1, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]; rfl
        _ = 1 := by
            rw [hc]
            change ι.appTop.hom (((eSec Xo.univ.t.G).app ⊤).hom (u : Γ(Xo.univ.t.G.left, ⊤))) = 1
            rw [h1]
            exact map_one _
    apply Units.ext
    rw [← hc, hc1, map_one, Units.val_one]
  subst hu1
  cases wP
  cases wP'
  congr
  funext j
  simpa using hu j

theorem primUniq_of_global (hglob : GlobalFnsSt) : PrimUniqSt := fun E _ _ _ H Dw l Xo wP wP' hP hP' =>
  primUniqOfGlobal_holds hglob E H Dw l Xo (isAbelianScheme_univ Xo) wP wP' hP hP'

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartCut
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (FGLaw)

def ChartDataGSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0)
    (S : Type) [CommRing S] [IsLocalRing S] (x0 : Sp S ⟶ X0) {κ : Type} [Fintype κ]
    (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)),
    (∀ ℓ, IsTanAtG t x0 (tg ℓ)) →
    (∀ w, IsTanAtG t x0 w →
      ∃! a : κ → S, IsCombAtG t x0 (m := Fintype.card κ)
        (fun i => tg ((Fintype.equivFin κ).symm i)) (fun i => a ((Fintype.equivFin κ).symm i)) w) →
    ∃ (d : ℕ) (G : FGLaw S d) (A : Germ.OAct (𝓞 E) G) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G),
      d = Fintype.card κ ∧ (∀ ℓ (j : Fin d), uvec ℓ j = if (j : ℕ) = (Fintype.equivFin κ ℓ : ℕ) then 1 else 0) ∧
      IsChartG t x0 d G.F A.act tg uvec x

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniq
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def GaugeUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S)
    (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G), IsExpChart y x →
    ∀ e e' : ∀ m, ExpFr y x m, IsExpGauge y x e → IsExpGauge y x e' →
    ∃ q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S, MvPowerSeries.constantCoeff q = 0 ∧
      (∀ m, MvPowerSeries.coeff m q ≠ 0 → m.degree = 2) ∧
      (∀ ℓ ℓ' : Lt1 Dw, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1 +
          Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ') 1) q ≠ 0 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) ∧
      ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
        (f f' : MvPowerSeries (Fin 1 × Fin (dL Dw)) S),
        IsExpGerm y x e k F f → IsExpGerm y x e' k F f' →
          f' = f * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndRelPf
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

namespace CIndRelPf

theorem dim_eq_card {S : Type} [CommRing S] [Nontrivial S] {ι : Type} [Fintype ι] {d : ℕ}
    (u : ι → Fin d → S) (h : ∀ v : Fin d → S, ∃! a : ι → S, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j) :
    d = Fintype.card ι := by
  let f : (ι → S) →ₗ[S] (Fin d → S) :=
    { toFun := fun a j => ∑ ℓ, a ℓ * u ℓ j
      map_add' := by
        intro a b
        funext j
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        funext j
        simp [Finset.mul_sum, mul_assoc] }
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      obtain ⟨c, -, hc⟩ := h (f a)
      have ha : a = c := hc a (fun j => rfl)
      have hb : b = c := hc b (fun j => congrFun hab.symm j)
      rw [ha, hb]
    · intro v
      obtain ⟨a, ha, -⟩ := h v
      exact ⟨a, funext ha⟩
  have hr := (LinearEquiv.ofBijective f hf).finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fin_fun] at hr
  exact hr.symm

end CIndRelPf

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
