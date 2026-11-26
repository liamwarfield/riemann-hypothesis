module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArchimedeanUniqueness.MetricDef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DescSt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt

def DlogTan {K₁ : Type} [Field K₁] {D₀ : ReciprocityTheory.ChartRestriction.G.Out.DegPre K₁} (v : ReciprocityTheory.ChartRestriction.G.Out.GtPt D₀ (epsR K₁))
    (χ : D₀.X) (y : K₁) : Prop :=
  ∀ j, ⊤ ≤ LB.wchart D₀.P.L (ReciprocityTheory.ChartRestriction.G.Out.DegPre.gtφT D₀ (epsR K₁) v.b χ) j →
    TrivSqZeroExt.snd (valR (A := DualNumber K₁) (𝟙 _) _ ((v.s χ).s j).val) =
      TrivSqZeroExt.fst (valR (A := DualNumber K₁) (𝟙 _) _ ((v.s χ).s j).val) * y

noncomputable def xiVal {E : Type} [Field E] [NumberField E] {K₁ : Type} [Field K₁] {X : Type} [AddCommGroup X]
    [Module (𝓞 E) X] (τK : E →+* K₁) (ξ : Module.Dual ℤ X) (χ : X) : K₁ :=
  ∑ i, τK ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (NumberField.integralBasis E) i) *
    ((ξ ((NumberField.RingOfIntegers.basis E i) • χ) : ℤ) : K₁)

noncomputable def pairE {E : Type} [Field E] [NumberField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (ξ : Module.Dual ℤ X) (x : X) : E :=
  ∑ i, (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (NumberField.integralBasis E) i *
    ((ξ ((NumberField.RingOfIntegers.basis E i) • x) : ℤ) : E)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

section Fam

variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
  (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (y : FrPt Xo c (CAt σ))

def AnLie (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)) : Prop :=
  y.x = Fu.u i Pm ∧ ∀ τ k, IsDerivAt0 (fun w => (Fu.ex i Pm w).left) (z τ k) (y.u τ k)

def AnGen (θ : (Fin g → ℂ) → ℂ) (κ : ℂ) : Prop :=
  ∃ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u i Pm) (fun w => (Fu.ex i Pm w).left) θ fr ∧
    ∀ j z (pt : Sp ℂ ⟶ Gx y.x), pt ≫ gxFst y.x = (Fu.ex i Pm z).left → pt ≫ gxSnd y.x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) = κ * θ z * fr j z

def IsThetaL2NormSquared (v : ℝ) : Prop :=
  ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
            (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
            Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
            (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (Fu.Di i).EF a b) ∧
            (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
            (∀ j z, ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
            (∀ j j' z, ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
              fr j z = valAt' (Fu.ex i Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
                (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
            (∀ j, ⊤ ≤ (Fu.ex i Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j 0 = valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
                (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
            (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
                Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) ∧
            (∀ j z (pt : Sp ℂ ⟶ Gx y.x),
              pt ≫ gxFst y.x = (Fu.ex i Pm z).left →
              pt ≫ gxSnd y.x = 𝟙 (Sp ℂ) →
              ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) = θ z * fr j z) ∧
            MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume ∧
            (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
              (MeasureTheory.volume Fd).toReal = v

def IsRiem (Hm : Matrix (Fin g) (Fin g) ℂ) : Prop :=
  Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
    ∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (Fu.Di i).EF a b

end Fam

structure UnfWit (U : Unf Xo c σ r) where
  g : ℕ
  e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)
  F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)
  ik : U.Comp → Fin F.n
  φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ
  iso : ∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) =
    Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))
  Pm : ∀ k, (U.X k).dom → ((F.Di (ik k)).La →+ (Fin g → ℂ))
  Pm_eq : ∀ k x a j, Pm k x a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2
  period : ∀ k x, IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) (Pm k x)
  lie : ∀ k x, AnLie F (ik k) (Pm k x) (U.un k x) (fun τ i => Pi.single (e.symm ⟨τ, i⟩) 1)
  norm : ∀ k (x : (U.X k).dom), (∀ τ' i', ‖dmin (U.X k).Gm x.1 τ' i'‖ = 1) → IsThetaL2NormSquared F (ik k) (Pm k x) (U.un k x) 1

section Hol

variable [Algebra (FractionRing ℂ) ℂ] {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {a : ArcIn Dw l β ℂ (σ.comp β)} {χ : Sp (PowerSeries ℂ) ⟶ Y.X} {W : Wit Y a χ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty} (Ha : HolArc Y σ a χ W Fu)

def AnVec (ν : Out.GtPt a.D₀ (epsR ℂ)) (z₀ : Fin g → ℂ) : Prop :=
  IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left)) z₀ ν.b.left ∧
    ∀ x j, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) j →
      valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val =
        TrivSqZeroExt.inl (chiVal (Ha.ex₀ 0) x j) +
          TrivSqZeroExt.inr (fderiv ℂ (fun z => chiVal (Ha.ex₀ z) x j) 0 z₀)

structure ThetaDat (th : a.D₀.P.L.Sec) where
  bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (Fu.Di Ha.i).La
  S : Finset (Fin g)
  h : Matrix (Fin g) (Fin g) ℂ
  τ : ℂ → Matrix (Fin g) (Fin g) ℂ
  c₁ : Fin g → ℂ
  c₂ : Fin g → ℂ
  κ : ℂ
  sympl : ∀ u v, (Fu.Di Ha.i).EF (bas u) (bas v) = -omegaStd u v
  ker : ∀ u, Ha.y (bas u) = 0 ↔ ∀ k ∈ S, u (.inr k) = 0
  orth : ∀ u, (∀ v', Ha.y v' = 0 → (Fu.Di Ha.i).EF (bas u) v' = 0) ↔
    (∀ k, u (.inr k) = 0) ∧ ∀ k ∉ S, u (.inl k) = 0
  per : ∀ w k, h.mulVec (Ha.Pw w (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧
    h.mulVec (Ha.Pw w (bas (Pi.single (.inr k) 1))) = (τ w).mulVec (Pi.single k 1)
  pos : ∀ w, Ha.T < w.im → (τ w).IsSymm ∧ ((τ w).map Complex.im).PosDef
  half₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2
  half₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2
  frame : ∀ w, Ha.T < w.im → ∃ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u Ha.i (Ha.Pw w))
    (fun z => (Fu.ex Ha.i (Ha.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr
  κ_ne : κ ≠ 0
  c₁_S : ∀ k ∈ S, c₁ k = 0
  onB : ∀ w : ℂ, Ha.T < w.im → IsFnInRigFrame a.D₀ (fun z => (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left)) th
    (fun z => κ * thetaCharOff S (τ w) c₁ c₂ (h.mulVec z))

def AnFr {th : a.D₀.P.L.Sec} (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)) (w : ℂ)
    (y : FrPt Xo c (CAt σ)) : Prop :=
  AnLie Fu Ha.i (Ha.Pw w) y z ∧
    AnGen Fu Ha.i (Ha.Pw w) y (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) Θ.κ

def NormOne : Prop :=
  ∀ w : ℂ, Ha.T < w.im → ∀ Hm, IsRiem Fu Ha.i (Ha.Pw w) Hm →
    ∀ v, (hermForm Hm (Ha.N v) (Ha.N v)).re * w.im = a.be (Ha.y v) (Ha.y v)

end Hol

section Freq

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (ξ : Module.Dual ℤ X)

def LevelPar (N : ℕ) (s : E) : Prop :=
  cc s = s ∧ ∀ x y : X, ∃ m : ℤ, Algebra.trace ℚ E (2 * s * pairE ξ x * cc (pairE ξ y)) = (N : ℚ) * m

def IsBePar (be : LinearMap.BilinForm ℤ X) (s : E) : Prop :=
  cc s = s ∧ ∀ x y : X, Algebra.trace ℚ E (2 * s * pairE ξ x * cc (pairE ξ y)) = (be x y : ℚ)

def BetaAt (N : ℕ) (be : LinearMap.BilinForm ℤ X) (ν₀ : E) (jj : ℤ) : Prop :=
  cc ν₀ = ν₀ ∧ ∀ s, IsBePar ξ be s → Algebra.trace ℚ E (ν₀ * s) = jj ∧
    ∀ ν : E, cc ν = ν → (∀ τ : E →+* ℂ, 0 ≤ (τ ν).re) →
      (∀ s', LevelPar ξ N s' → ∃ m : ℤ, Algebra.trace ℚ E (ν * s') = m) → Algebra.trace ℚ E (ν * s) = jj → ν = ν₀

end Freq

def TransvIn (X : Data E r) (N : ℕ) (la : Wt X.Ψ r) : Prop :=
  ∀ ξ, X.IsIso ξ → ∀ s : E, cc s = s →
    (∀ v ∈ X.Λ, ∃ u ∈ X.Λ, (transvMat X.Gm ξ (s * X.κ0)).mulVec v - v = (N : E) • u) →
    ∃ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = transvMat X.Gm ξ (s * X.κ0) ∧ X.χ la γ = 1

variable {K₁ : Type} [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)]

def ajAt (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (F : Rul Xo c) (x : ArcLt Dw → ℂ) : ℂ :=
  ∑ μ ∈ (arcNum (evR Xo c F d.yF)).support,
    ι (((arcNum (evR Xo c F d.yF)).coeff μ).coeff d.jj) * ∏ v ∈ μ.support, x v ^ μ v

def InvBl (x : ArcLt Dw → ℂ) : Prop :=
  ∀ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => x ⟨τ, (i, k)⟩).det ≠ 0

end GlobalTheory.ArcQ
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FreeQuotientRank Formalism.L2.Pj Formalism.L2.Pj.QAt

structure FinSite (K₁ : Type) [Field K₁] [NumberField K₁] (w : HeightOneSpectrum (𝓞 K₁)) where
  K : Type
  [nf : NormedField K]
  [um : IsUltrametricDist K]
  [cs : CompleteSpace K]
  ι : K₁ →+* K
  r : ℝ
  r_pos : 0 < r
  r_lt : r < 1
  norm_ι : ∀ x : K₁, x ≠ 0 → ‖ι x‖ = r ^ ordAt w x
  K₀ : Subfield K
  res : ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K)
  S : Set K
  S_disc : ∀ t ∈ S, 0 < ‖t‖ ∧ ‖t‖ < 1
  S_dense : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ S, |‖t‖ - ρ| < ε
  S_units : ∀ t ∈ S, ∀ τ ∈ K₀, ‖τ‖ = 1 → t * τ ∈ S

attribute [instance] FinSite.nf FinSite.um FinSite.cs

def lcoeffPoly {ι K₁ : Type} [Field K₁] (P : MvPolynomial ι (LaurentSeries K₁)) (m : ℤ) : MvPolynomial ι K₁ :=
  ∑ μ ∈ P.support, MvPolynomial.monomial μ ((P.coeff μ).coeff m)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

def frameSub {K : Type} [Field K] (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K) (Y : ArcLt Dw → K) : ArcLt Dw → K :=
  fun x => (∑ l, Y ⟨x.1, x.2.1, l⟩ * Bm x.1 l x.2.2) * (lam x.1 x.2.2)⁻¹

def FinLocalAt {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁]
    [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁)) (n : ℕ)
    (vth : ℤ) (vη : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℤ) (m : ℕ) (Fs : Set (Rul Xo c)) : Prop :=
  ∃ (Z : FinSite K₁ w) (γ : Z.K) (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Z.K)
    (A Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Z.K),
    (γ ≠ 0 ∧ ‖γ‖ = Z.r ^ vth) ∧
    (∀ τ k, lam τ k ≠ 0 ∧ ‖lam τ k‖ = Z.r ^ vη τ k) ∧
    ((∀ τ, A τ * Bm τ = 1) ∧ ∀ τ k l, ‖A τ k l‖ ≤ Z.r ^ (-(m : ℤ))) ∧
    ∀ F ∈ Fs, ∀ t ∈ Z.S, ∀ Y : ArcLt Dw → Z.K, (∀ x, Y x ∈ Z.K₀ ∧ ‖Y x‖ ≤ 1) →
      ‖∏ τ : E →+* ℂ, (Matrix.of fun i l : Fin (Dw.mult τ) => Y ⟨τ, i, l⟩).det‖ = 1 →
      Filter.Tendsto (fun k : ℤ => ‖MvPolynomial.eval (frameSub Bm lam Y)
          (MvPolynomial.map Z.ι (lcoeffPoly (arcNum (evR Xo c F d.yF)) k)) * t ^ k‖)
        Filter.cofinite (nhds 0) ∧
      ‖(γ ^ n)⁻¹ * ∑' k : ℤ, MvPolynomial.eval (frameSub Bm lam Y)
          (MvPolynomial.map Z.ι (lcoeffPoly (arcNum (evR Xo c F d.yF)) k)) * t ^ k‖ ≤ 1

def arcDetR (Dw : Datum H) (V : Type) [CommRing V] : MvPolynomial (ArcLt Dw) (PowerSeries V) :=
  ∏ τ : E →+* ℂ, Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
    (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (PowerSeries V)))

abbrev ArcSR (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) : Type :=
  Localization.Away (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)

def arcXR (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) (x : ArcLt Dw) : ArcSR Dw V ϖ :=
  algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ) (MvPolynomial.X x)

def FrameBound {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁]
    [Algebra c.F (ArcS Dw K₁)] {w : HeightOneSpectrum (𝓞 K₁)} (Z : FinSite K₁ w) (γ : Z.K)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Z.K)
    (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Z.K) (n : ℕ)
    (d : ArcDatum Xo c K₁) (Fs : Set (Rul Xo c)) : Prop :=
  ∀ F ∈ Fs, ∀ t ∈ Z.S, ∀ Y : ArcLt Dw → Z.K, (∀ x, Y x ∈ Z.K₀ ∧ ‖Y x‖ ≤ 1) →
    ‖∏ τ : E →+* ℂ, (Matrix.of fun i l : Fin (Dw.mult τ) => Y ⟨τ, i, l⟩).det‖ = 1 →
    Filter.Tendsto (fun k : ℤ => ‖MvPolynomial.eval (frameSub Bm lam Y)
        (MvPolynomial.map Z.ι (lcoeffPoly (arcNum (evR Xo c F d.yF)) k)) * t ^ k‖)
      Filter.cofinite (nhds 0) ∧
    ‖(γ ^ n)⁻¹ * ∑' k : ℤ, MvPolynomial.eval (frameSub Bm lam Y)
        (MvPolynomial.map Z.ι (lcoeffPoly (arcNum (evR Xo c F d.yF)) k)) * t ^ k‖ ≤ 1

structure DvrFrame {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁]
    [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁))
    (Z : FinSite K₁ w) where
  Tv : CDVR
  io : K₁ →+* Tv.Fr
  ιT : Tv.Fr →+* Z.K
  ιT_io : ιT.comp io = Z.ι
  norm_le : ∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1
  ϖ : Tv.V
  ϖ_irr : Irreducible ϖ
  norm_ϖ : ‖ιT (algebraMap Tv.V Tv.Fr ϖ)‖ < 1
  [algR : Algebra c.F (ArcSR Dw Tv.V ϖ)]
  [algW : Algebra c.F (ArcS Dw Tv.Fr)]
  algW_eq : ∀ r : c.F, algebraMap c.F (ArcS Dw Tv.Fr) r =
    arcι Dw Tv.Fr (PowerSeries.C (R := Tv.Fr) (io (algebraMap c.F K₁ r)))
  yR : FrPt Xo c (ArcSR Dw Tv.V ϖ)

attribute [instance] DvrFrame.algR DvrFrame.algW

variable {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)]
  {d : ArcDatum Xo c K₁} {w : HeightOneSpectrum (𝓞 K₁)} {Z : FinSite K₁ w}

def BcRigidAt (Dv : DvrFrame d w Z) (γ : Dv.Tv.Fr) (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Dv.Tv.Fr)
    (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr) : Prop :=
  ∃ (φ : ArcS Dw K₁ →ₐ[c.F] ArcS Dw Dv.Tv.Fr)
    (ψ : ArcSR Dw Dv.Tv.V Dv.ϖ →ₐ[c.F] ArcS Dw Dv.Tv.Fr)
    (z₁ z₂ : FrPt Xo c (ArcS Dw Dv.Tv.Fr)) (tγ : Ix Dw → (ArcS Dw Dv.Tv.Fr)ˣ),
    (∀ f : LaurentSeries K₁, ∃ g : LaurentSeries Dv.Tv.Fr, (∀ m, g.coeff m = Dv.io (f.coeff m)) ∧
      φ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) _ (MvPolynomial.C f)) = algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries Dv.Tv.Fr)) _ (MvPolynomial.C g)) ∧
    (∀ x : ArcLt Dw, φ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) _ (MvPolynomial.X x)) =
      ∑ l : Fin (Dw.mult x.1), arcX Dw Dv.Tv.Fr x.1 x.2.1 l *
        algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries Dv.Tv.Fr)) _ (MvPolynomial.C (HahnSeries.C (Γ := ℤ) (Bm x.1 l x.2.2 * (lam x.1 x.2.2)⁻¹)))) ∧
    (∀ p : PowerSeries Dv.Tv.V, ψ (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Dv.Tv.V)) _ (MvPolynomial.C p)) =
      algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries Dv.Tv.Fr)) _ (MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr
        (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr) p)))) ∧
    (∀ x : ArcLt Dw, ψ (arcXR Dw Dv.Tv.V Dv.ϖ x) = arcX Dw Dv.Tv.Fr x.1 x.2.1 x.2.2) ∧
    (tγ none : ArcS Dw Dv.Tv.Fr) = algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries Dv.Tv.Fr)) _ (MvPolynomial.C (HahnSeries.C (Γ := ℤ) γ)) ∧
    (∀ a, tγ (some a) = 1) ∧
    FrMap φ d.yF z₁ ∧ FrMap ψ Dv.yR z₂ ∧ FrBor tγ z₂ z₁

def RecordAt (Dv : DvrFrame d w Z) (Fs : Set (Rul Xo c)) : Prop :=
  ∀ F ∈ Fs, ∀ t ∈ Z.S, ∀ Y : ArcLt Dw → Z.K, (∀ x, Y x ∈ Z.K₀ ∧ ‖Y x‖ ≤ 1) →
    ‖∏ τ : E →+* ℂ, (Matrix.of fun i l : Fin (Dw.mult τ) => Y ⟨τ, i, l⟩).det‖ = 1 →
    ∀ ev : ArcSR Dw Dv.Tv.V Dv.ϖ →+* Z.K,
      (∀ p : PowerSeries Dv.Tv.V, ev (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Dv.Tv.V)) _ (MvPolynomial.C p)) =
        ∑' k : ℕ, Dv.ιT (algebraMap Dv.Tv.V Dv.Tv.Fr (PowerSeries.coeff k p)) * t ^ k) →
      (∀ x, ev (arcXR Dw Dv.Tv.V Dv.ϖ x) = Y x) →
      ‖ev (evR Xo c F Dv.yR)‖ ≤ 1

def FinLocalCutAt (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁)) (vth : ℤ)
    (vη : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℤ) (m : ℕ) (Fs : Set (Rul Xo c)) : Prop :=
  ∃ (Z : FinSite K₁ w) (Dv : DvrFrame d w Z) (γ : Dv.Tv.Fr)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Dv.Tv.Fr)
    (A Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr),
    (γ ≠ 0 ∧ ‖Dv.ιT γ‖ = Z.r ^ vth) ∧
    (∀ τ k, lam τ k ≠ 0 ∧ ‖Dv.ιT (lam τ k)‖ = Z.r ^ vη τ k) ∧
    ((∀ τ, A τ * Bm τ = 1) ∧ ∀ τ k l, ‖Dv.ιT (A τ k l)‖ ≤ Z.r ^ (-(m : ℤ))) ∧
    BcRigidAt Dv γ lam Bm ∧ RecordAt Dv Fs

def SiteAlg (Z : FinSite K₁ w) (Tv : CDVR) (ιT : Tv.Fr →+* Z.K) : Prop :=
  ∀ s : Finset Z.K, (∀ x ∈ s, (x ∈ Z.K₀ ∨ x ∈ Z.S) ∧ ‖x‖ ≤ 1) →
    ∃ (T' : CDVR) (j : Tv.V →+* T'.V) (i' : T'.Fr →+* Z.K), T'.FinRes ∧ IsLocalHom j ∧
      (∀ v, i' (algebraMap T'.V T'.Fr (j v)) = ιT (algebraMap Tv.V Tv.Fr v)) ∧
      (∀ x : T'.Fr, ‖i' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T'.V T'.Fr)) ∧
      ∀ x ∈ s, ∃ v : T'.V, i' (algebraMap T'.V T'.Fr v) = x

def intAt (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (la : HeightOneSpectrum (𝓞 c.F)) :
    Set (Rul Xo c) :=
  {F | F ∈ sec Xo c a n ∧ ∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la, 0 ≤ v F}

structure IntModel (d : ArcDatum Xo c K₁) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) where
  b : c.V Wl →+* Tv.V
  b_eq : ∀ x, algebraMap Tv.V Tv.Fr (b x) = io (algebraMap c.F K₁ (x : c.F))
  ρ : (E →+* ℂ) → (𝓞 E →+* Tv.V)
  ρ_eq : ∀ τ x, algebraMap Tv.V Tv.Fr (ρ τ x) = io (algebraMap c.F K₁ (embK c τ x))
  aw : ArcIn Dw l (c.V Wl).subtype Tv.V b
  aK : ArcIn Dw l (RingHom.id c.F) Tv.Fr (io.comp (algebraMap c.F K₁))
  pw : Out.IsPullDeg (algebraMap Tv.V Tv.Fr) aw.D₀ aK.D₀
  pK : Out.IsPullDeg io d.a.D₀ aK.D₀
  bcw : InBC (algebraMap Tv.V Tv.Fr) aw (aK.restrict (c.V Wl).subtype) pw
  bcK : InBC io d.a aK pK
  thw : aw.D₀.P.L.Sec
  thw_nz : ThNZ thw
  ew : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt aw.D₀ (epsR Tv.V)
  γ : Tv.Fr
  g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Tv.Fr
  th_tie : ∃ th₁ th₂ : aK.D₀.P.L.Sec, ThBC pw thw th₁ ∧ ThBC pK d.th th₂ ∧ ThMul γ th₁ th₂
  e_tie : ∃ e₁ e₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt aK.D₀ (epsR Tv.Fr),
    (∀ τ k, LetBC pw (ew τ k) (e₁ τ k)) ∧ (∀ τ k, LetBC pK (d.e τ k) (e₂ τ k)) ∧ (∀ τ k, GtTanR (e₁ τ k)) ∧
    ∀ τ k, GtComb (g τ k) (e₁ τ) (e₂ τ k)

def arcιR (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) : PowerSeries V →+* ArcSR Dw V ϖ :=
  (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ)).comp MvPolynomial.C

def letMR (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) (τ : E →+* ℂ) :
    Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (ArcSR Dw V ϖ) := Matrix.of fun i k => arcXR Dw V ϖ ⟨τ, i, k⟩

end GlobalTheory.ArcQ
end
end
