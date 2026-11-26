module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviBlockCentreFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviCentreFiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaChainLastStepIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
namespace GlobalTheory.ThK

structure KP : Prop where

  base : GlobalTheory.FunPr.Hypotheses₂

  howeDualityUnitary : GlobalTheory.Published.HoweDualityUnitary

  howeDualityReal : GlobalTheory.Published.HoweDualityReal

  automorphicFormsUnitary : GlobalTheory.Published.AutomorphicFormsUnitary

  eisensteinIsotropicLine : GlobalTheory.Published.EisensteinIsotropicLine

  genericityGL : GlobalTheory.Published.GenericityGL

  complementaryThetaInert : GlobalTheory.Published.ComplementaryThetaInert

  siegelSetUnitary : GlobalTheory.Published.SiegelSetUnitary

  minguezThetaGL : GlobalTheory.Published.MinguezThetaGL

  jacquetShalika : GlobalTheory.Published.JacquetShalika

  discreteSpectrumGL : GlobalTheory.Published.DiscreteSpectrumGL

  heckeTateFunctionalEquation : GlobalTheory.Published.HeckeTateFunctionalEquation

  automorphicFormsFiniteUnitary : GlobalTheory.Published.AutomorphicFormsFiniteUnitary

  geometricLemmaFiltration : GlobalTheory.Published.GeometricLemmaFiltration

  cuspidalSpectrumGL : GlobalTheory.Published.CuspidalSpectrumGL

  siegelWeilAnisotropicCM : GlobalTheory.Published.SiegelWeilAnisotropicCM

  siegelWeilAnisotropicHermitian : GlobalTheory.Published.SiegelWeilAnisotropicHermitian

  siegelEisensteinDoubled : GlobalTheory.Published.SiegelEisensteinDoubled

  leviCentreFiniteUnitary : GlobalTheory.Published.LeviCentreFiniteUnitary

  leviBlockCentreFinite : GlobalTheory.Published.LeviBlockCentreFinite

  leviCentreInducedUnitary : GlobalTheory.Published.LeviCentreInducedUnitary

  eisensteinResidueLine : GlobalTheory.Published.EisensteinResidueLine

  rallisTowerUnitary : GlobalTheory.Published.RallisTowerUnitary

end GlobalTheory.ThK
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)

structure ArchSec (Z : Comp Xo c) (la : AllWt.Weight Dw) : Type where

  sig : Rul Xo c

  inv : Rul Xo c
  sig_mem : sig ∈ secZ Xo c (exOf Dw la 0)
  inv_mem : inv ∈ secZ Xo c (-exOf Dw la 0)
  idem_sig : idem Z * sig = sig
  idem_inv : idem Z * inv = inv
  mul_inv : sig * inv = idem Z

  cInf : (c.F →+* ℂ) → ℝ
  cInf_pos : ∀ σ, 0 < cInf σ
  norm_inf : ∀ σ, homN (U (goodOf c σ)) x (wtOf Dw la 0) sig '' framesOn (U (goodOf c σ)) Z = {cInf σ}


variable {U x} in
def ArchSec.ofConst {Z : Comp Xo c} {la : AllWt.Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U x Z la δ) :
    ArchSec U x Z la :=
  ⟨s.sig, s.inv, s.sig_mem, s.inv_mem, s.idem_sig, s.idem_inv, s.mul_inv, s.cInf, s.cInf_pos, s.norm_inf⟩

def Onto : Prop :=
  ∀ σ, GoodEmb c σ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → (∀ τ i, i < Dw.mult τ → 1 ≤ a (τ, i)) →
    4 * (finrank ℚ E * r) + 4 ≤ n →
    holSub0 (U σ).X (laU (U σ) a n) ≤ Submodule.span ℂ (rdU (U σ) '' (cusp Xo c U a n : Set (Rul Xo c)))

structure Laws : Prop where
  pos : 1 ≤ Dw.p + Dw.q
  lev : l.A = 1
  good : ∀ p : ℕ, p.Prime → l.GoodAt p
  unf : ∀ σ, GoodEmb c σ → IsUnf (U σ)
  geo : FnAlgClosed (Xo := Xo) (c := c)
  xi : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x
  chi : ∀ σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (laU (U σ) a n k) γ = 1
  det : ∀ σ, GoodEmb c σ → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1
  onto : Onto U
  line : ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0

def IsFlatQuot (Z : Comp Xo c) (τ : Psi H) (f g : Rul Xo c) : Prop :=
  ∀ σ, GoodEmb c σ → ∃ a : ℂ, a ≠ 0 ∧ ∀ k (hτ : relab c σ τ.1 ∈ ((U σ).X k).Ψ) y,
    (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
      rdU (U σ) g k y = a * horizGen ⟨_, hτ⟩ y * rdU (U σ) f k y

def Always (Q : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}, (∀ σ : c.F →+* ℂ, Unf Xo c σ r) → ℝ → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → Q U x

def ArchEx : Prop := ∀ (Z : Comp Xo c) (τ : Psi H), Nonempty (ArchSec U x Z (flatWt Dw τ))


def FrameDeg (logOm : ℝ) : Prop :=
  ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ),
    (∀ la, ∀ w ∈ valOn Z la, w s.sig = (ρ la : EReal)) →
      (Function.support ρ).Finite ∧ lineDeg s.cInf ρ = ((Dw.p : ℝ) - Dw.q) / 2 * logOm

def FlatDegreeSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ →
    ∀ (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ),
      Laws U x → FlatDegree U x (CM.logOm E χ).re

end GlobalTheory.FlatCore

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CM GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames ReciprocityTheory.ChartRestriction.G.Pdiv Formalism.L2.Pj
open scoped CategoryTheory.Obj NNReal

section Index

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


variable (K) in
def detSpan (m : ℕ) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) (⋀[K]^m V) :=
  Submodule.span (𝓞 K) {w | ∃ y : Fin m → V, (∀ i, y i ∈ L) ∧ w = exteriorPower.ιMulti K m y}


variable (K) in
def idx (m : ℕ) (L N : Submodule (𝓞 K) V) : Ideal (𝓞 K) := (detSpan K m N).colon (detSpan K m L)

end Index

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q)

def phiP (a : Fin p) : (X.A true).t.G ⟶ X.B.t.G := X.φ (Sum.inl a)

def phiQ (a : Fin q) : (X.A false).t.G ⟶ X.B.t.G := X.φ (Sum.inr a)

def IsGram (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin q) (Fin q) (𝓞 E)) : Prop :=
  (∀ a b, WeilEq X.B.t.PP.L (phiP X a) (phiP X b) (X.A true).t.PP.L ((X.A true).t.act.act (gP a b)) (𝟙 _)
    (spMap (σ₁.comp (algebraMap (𝓞 K) K)))) ∧
  ∀ a b, WeilEq X.B.t.PP.L (phiQ X a) (phiQ X b) (X.A false).t.PP.L ((X.A false).t.act.act (gQ a b)) (𝟙 _)
    (spMap (σ₁.comp (algebraMap (𝓞 K) K)))

variable {X} (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol)
  (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))) (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)))

def IsDiffs : Prop := (∀ a, FP.IsDiffOf FB (phiP X a) (MP a)) ∧ ∀ a, FQ.IsDiffOf FB (phiQ X a) (MQ a)

def subP (τ : 𝓞 E →+* 𝓞 K) : Submodule (𝓞 K) (Fin FB.P₀.g → K) :=
  ⨆ a, (FP.eigLat (X.A true).t.act τ).map ((MP a).restrictScalars (𝓞 K))

def subQ (τ : 𝓞 E →+* 𝓞 K) : Submodule (𝓞 K) (Fin FB.P₀.g → K) :=
  ⨆ a, (FQ.eigLat (X.A false).t.act τ).map ((MQ a).restrictScalars (𝓞 K))

end GlobalTheory.FlatCM

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.GenOf
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

def TyEll : GlobalTheory.CongL.UnitaryAutomorphicTypeClass := fun E _ _ _ l a w₀ U =>
  ∃ (m : ℕ) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (θ : J →* Multiplicative (ZMod (l ^ m)))
    (χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ),
    IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧ IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧
    (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) ∧ Function.Surjective θ ∧ χ ≠ 1 ∧
    (∀ (σ : SmIrr (GL (Fin a) (w₀.adicCompletion E))) (v : σ.V), v ≠ 0 →
      (∀ g : J, σ.ρ g v = ((χ (θ g) : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ) ∧
    ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU a w₀, ∀ h : cLoc w₀ x ∈ J, RU E a x φ = ((χ (θ ⟨cLoc w₀ x, h⟩) : ℂˣ) : ℂ) • φ

def GenOf (D : ∀ a : ℕ, MvPolynomial (Fin a) ℤ) : ℕ → ℕ → Multiset ℂˣ → Prop := fun a _ B =>
  ∀ α : Fin a → ℂˣ, Finset.univ.val.map α = B → MvPolynomial.aeval (fun i => (α i : ℂ)) (D a) ≠ 0

end GlobalTheory.CongW
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.InclEquiv
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSCore GlobalTheory.Vanishing

namespace GlobalTheory.HSShort

variable {F : Type} [Field F] [NumberField F]

abbrev Tot (G : Geo F) : Type := ∀ j, G.Sec j

def shiftAt (G : Geo F) (u : Fin G.N → F) : ∀ j, Tot G →ₗ[F] G.Sec j
  | 0 => 0
  | j + 1 => G.mulW j u ∘ₗ LinearMap.proj j

def shift (G : Geo F) : (Fin G.N → F) →ₗ[F] Module.End F (Tot G) where
  toFun u := LinearMap.pi (shiftAt G u)
  map_add' u v := LinearMap.ext fun x => funext fun j => by cases j <;> simp [shiftAt]
  map_smul' c u := LinearMap.ext fun x => funext fun j => by cases j <;> simp [shiftAt]

def incl (X : Data F) (j : ℕ) : X.V j →ₗ[F] Tot X.toGeo := LinearMap.single F _ j ∘ₗ (X.V j).subtype

theorem incl_injective (X : Data F) (j : ℕ) : Function.Injective (incl X j) := fun a b h =>
  Subtype.ext (by simpa [incl] using congrFun h j)

def inclEquiv (X : Data F) (j : ℕ) : X.V j ≃ₗ[F] LinearMap.range (incl X j) := LinearEquiv.ofInjective _ (incl_injective X j)

def sysOf (X : Data F) (Λ₀ : ℝ) : Sys F (Tot X.toGeo) where
  N := X.N
  n := X.n
  D := X.D
  T := X.T
  w := X.w
  fr := X.A
  mul := shift X.toGeo
  V j := LinearMap.range (incl X j)
  M j := (X.M j).map ((inclEquiv X j).toLinearMap.restrictScalars (𝓞 F))
  nm j := comap (X.nm j) (inclEquiv X j).symm.toLinearMap (inclEquiv X j).symm.injective
  beta := X.beta
  abelian₂ := X.abelian₂
  Lam0 := Λ₀
  LamD := X.LamD
  LamT := X.LamT

def totExt (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E] :
    Tot G →ₛₗ[algebraMap F E] Tot (G.baseChange E) where
  toFun x j := G.toExt E j (x j)
  map_add' x y := funext fun j => map_add _ _ _
  map_smul' c x := funext fun j => map_smulₛₗ (G.toExt E j) c (x j)

section Split

variable {X : Data F} {s : Fin X.D → Fin X.N → F} {hs : X.IsGood s} {δ : ℕ}

def totRes (Co : Coord X.toGeo hs δ) : Tot X.toGeo →ₗ[F] (Fin δ → F) :=
  (Co.ev 0).toLinearMap ∘ₗ hs.res 0 ∘ₗ LinearMap.proj 0


variable (X s) in
def totFil (a : ℕ) : Submodule F (Tot X.toGeo) := (filV X s a).map (incl X X.T)

def totSym (Co : Coord X.toGeo hs δ) (a : ℕ) : totFil X s a →ₗ[F] (MonoDeg (Fin X.D) a × Fin δ → F) :=
  symV Co a ∘ₗ (Submodule.equivMapOfInjective _ (incl_injective X X.T) (filV X s a)).symm.toLinearMap

end Split

end GlobalTheory.HSShort
end
end
