module

public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
public import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
noncomputable section

namespace Formalism.MainNotions.EmbeddingTypeJumps

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits
open scoped Pointwise

section Lemma1

variable (D : D7)

def InPhi (φ : D.host.E →+* ℂ) : Prop := φ ∈ D.host.cmType

abbrev decG (v : HeightOneSpectrum (𝓞 D.host.E)) : Subgroup (D.host.E ≃ₐ[ℚ] D.host.E) :=
  MulAction.stabilizer (D.host.E ≃ₐ[ℚ] D.host.E) v.asIdeal

abbrev ineG (v : HeightOneSpectrum (𝓞 D.host.E)) : Subgroup (D.host.E ≃ₐ[ℚ] D.host.E) :=
  Ideal.inertia (D.host.E ≃ₐ[ℚ] D.host.E) v.asIdeal

def Conclusion1 : Prop :=
  ∀ l ∈ ({D.host.q, D.host.d} : Finset ℕ), l % 4 = 3 ∧
    ∀ v ∈ placesOver D.host.E l,
      v.asIdeal.ramificationIdx ℤ = 2 ∧
      D.host.conj • v.asIdeal ≠ v.asIdeal ∧
      (l = D.host.q → ∀ σ ∈ decG D v, ∀ φ : D.host.E →+* ℂ,
        (InPhi D (φ.comp (σ : D.host.E →+* D.host.E)) ↔ InPhi D φ)) ∧
      (l = D.host.d → ∀ σ ∈ ineG D v, σ ≠ 1 → ∀ φ : D.host.E →+* ℂ,
        (InPhi D (φ.comp (σ : D.host.E →+* D.host.E)) ↔ ¬ InPhi D φ))

end Lemma1

def epsL (l : ℕ) : ℝ := ((l : ℝ) ^ 2)⁻¹

def polyVal (P : MvPolynomial (Fin 3) ℕ) (f r t : ℕ) : ℕ := MvPolynomial.eval ![f, r, t] P

def bndB (D : D7) (large₂ : SizeData₂ D) (C : ℝ) (P : MvPolynomial (Fin 3) ℕ) (l : ℕ) : ℝ :=
  C * D.R.f * (D.R.r * (large₂.sc.b / l + large₂.Sc + D.R.t + large₂.etaSz + Real.log large₂.sc.b) + D.R.m * large₂.sc.b) +
    (polyVal P D.R.f D.R.r D.R.t : ℝ) * Real.log large₂.sc.b

def TwLoc (D : D7) (i : D.nd.Loc) : Prop := D.what₂.muAt (D.nd.w i) ≠ D.what₂.mu0

def vZeta (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)) : ℚ :=
  lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1})

section Glob

open Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.BasicNotions.Loc Formalism.MainNotions.N

variable {D : D7}
  (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

def AtQD (i : D.nd.Loc) : Prop :=
  ((D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) ∧ TwLoc D i) ∧ HG D.nd D.naut i

def Conclusion2 (large₂ : SizeData₂ D) (C : ℝ) (P : MvPolynomial (Fin 3) ℕ) : Prop :=
  ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → TwLoc D i →
    large₂.sc.x ^ (2 * large₂.Ct + 5) < (D.nd.l i : ℝ) →
    ∀ π ∈ D.nd.Zgood i, Br.sFin D.loc D.nbr i (ρ i) π →
      (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
      (D.nd.vcc i π : ℝ) ≤ bndB D large₂ C P (D.nd.l i) +
        ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) +
        (padicValNat (D.nd.l i) (hE D.host) : ℝ) +
        (Br.sPi D.loc D.nbr i (ρ i) π : ℝ) + epsL (D.nd.l i)

def admA (CA : ℝ) : Prop := Formalism.MainNotions.ElementDenominator.Conclusion1 D CA

def GlobalIndexAwayFromTypes : Prop :=
  ∀ (i : D.nd.Loc) (π : D.nd.X i) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i)
    (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.admitted i (r i) (ρ i) π dc lenRow e' cB → Formalism.MainNotions.TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i (ρ i) π dc lenRow e' cB

def admG1 : Prop := ∀ i : D.nd.Loc, AtQD i → Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG1 i (r i)

def admG2 : Prop :=
  ∀ i : D.nd.Loc, AtQD i → ∀ π ∈ D.nd.Zgood i, Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG2 i (r i) (ρ i) π

def admG3 : Prop :=
  ∀ i : D.nd.Loc, AtQD i → ∀ π ∈ D.nd.Zgood i, Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG3 i (r i) (ρ i) π

def admG4 : Prop := ∀ i : D.nd.Loc, AtQD i → Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG4 i (r i)

def admG5 : Prop := ∀ i : D.nd.Loc, AtQD i → Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG5 i (r i)

def admG6 : Prop := ∀ i : D.nd.Loc, AtQD i → Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG6 i (r i)

def iwahoriAdmissibleSet : Prop :=
  ∀ i : D.nd.Loc, AtQD i → ∀ π ∈ D.nd.Zgood i,
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous i (r i) ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.admSS i (r i) ∧
      Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition i (r i) (ρ i) π ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i

def admTB (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.Conclusion4 D HW F

def admBK : Prop := Formalism.MainNotions.LocalSituation.Conclusion5 D

def KillingTwistedPlaces : Prop :=
  ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → TwLoc D i →
    ((∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) ∨
      D.R.t * D.R.r < Module.finrank D.host.E (CyclotomicField (D.nd.l i) D.host.E)) →
    ∀ π ∈ D.nd.Zgood i, (Br.sPi D.loc D.nbr i (ρ i) π : ℝ) ≤ epsL (D.nd.l i) ∧
      (D.R.t : ℝ) * ((∑ v ∈ D.nd.Q i, vZeta D i v : ℚ) : ℝ) ≤ epsL (D.nd.l i)

def WachHypothesisLocal (S : Formalism.MainNotions.LocalSituation.Sit) (E : S.Comparison₂) : Prop :=
  ∀ (Y : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ), Formalism.WeaklyAdmissibleFiltrations.IsCrys S.PD Y.ρ →
    (∀ a ∈ Formalism.MainNotions.LocalSituation.Jset S Y, -(M0 : ℤ) ≤ a ∧ a ≤ h0) → Formalism.MainNotions.LocalSituation.HypW S E Y M0 h0

def admW (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ i : D.nd.Loc, AtQD i →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (h : Good (D.nbr i w hw).Kw 1 C.LL),
      WachHypothesisLocal (Formalism.MainNotions.LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL h)
        ((F (D.nd.l i)).E (D.nbr i w hw).Kw 1 C.LL h).tie

def LiteratureHypotheses : Prop :=
  ∀ i : D.nd.Loc, AtQD i →
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.TameGeneratorConditions i ∧
    (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw),
      Formalism.MainNotions.TruncatedSeriesCountingIdentities.TateDualityH2Torsion (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL) ∧
      BlochKatoDim (Br.PD D.loc D.nbr i w hw) ↥C.LL.1) ∧
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.admH2 i ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.UnramifiedClassFieldBound i

def EmbTypeUc {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) : Prop :=
  (∀ x : D.host.E, ∃ y : D.what₂.LL,
    Br.toLLK (D.nbr i w hw) (D.nd.embK i y) = τ₀ (Br.cEw D.nbr i w hw x)) ∧
  ∃ φ ∈ D.host.cmType,
    ∀ (x : D.host.E) (y : D.what₂.LL),
      Br.toLLK (D.nbr i w hw) (D.nd.embK i y) = τ₀ (Br.cEw D.nbr i w hw x) →
        D.what₂.embLL y = starRingEnd ℂ (φ x)

def EmbTypeUe (ep : Bool) {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) : Prop :=
  if ep then Br.EmbTypeU D.nbr i w hw τ₀ else EmbTypeUc τ₀

def UpAt (ep : Bool) {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) : Prop :=
  ∃ τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw,
    EmbTypeUe ep τ₀ ∧ ∀ x, τ x = C.inc (τ₀ x)

def DownAt (ep : Bool) {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) : Prop :=
  ∃ τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw,
    EmbTypeUe (!ep) τ₀ ∧ ∀ x, τ x = C.inc (τ₀ x)

def HodgeJumpWindowsAtDistinguishedPrimes (ep : Bool) (large₂ : SizeData₂ D) : Prop :=
  ∀ i : D.nd.Loc, AtQD i →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1),
      ∃ (s : ℤ) (Jc Jl : Finset ℤ),
        large₂.etaSz + D.R.t + 1 < (s : ℝ) ∧ (s : ℝ) ≤ large₂.sc.b + large₂.etaSz + D.R.t + 1 ∧
        Jc.card = D.R.k - 1 ∧ Jl.card = D.R.m ∧
        (∀ a ∈ Jl,
          ((-large₂.etaSz + ((D.R.t : ℝ) - 1) / 2 ≤ (a : ℝ) ∧ a ≤ -2) ∨
            ((D.R.t : ℤ) + 1 ≤ a ∧ (a : ℝ) ≤ large₂.etaSz + ((D.R.t : ℝ) - 1) / 2)) ∧
          ¬ (0 ≤ a ∧ a < D.R.t) ∧ a ≠ -1 ∧ a ≠ D.R.t) ∧
        ((∀ a ∈ Jc, s ≤ a ∧ (a : ℝ) ≤ s + large₂.Sc) ∨ (∀ a ∈ Jc, -((s : ℝ) + large₂.Sc) ≤ a ∧ a ≤ -s)) ∧
        (UpAt ep C τ → ∀ a ∈ Jc, s ≤ a ∧ (a : ℝ) ≤ s + large₂.Sc) ∧
        (DownAt ep C τ → ∀ a ∈ Jc, -((s : ℝ) + large₂.Sc) ≤ a ∧ a ≤ -s) ∧
        ∀ (x : D.nd.X i) (a : ℤ),
          IsJumpV (Br.PD D.loc D.nbr i w hw)
              (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (r i) x))) τ a ↔
            a ∈ Jc ∨ a ∈ Jl ∨ (0 ≤ a ∧ a < D.R.t)

def FontaineSubOfSumsAtDistinguishedPrimes : Prop :=
  ∀ i : D.nd.Loc, AtQD i →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw),
      (∀ (V1 : Type) [AddCommGroup V1] [Module ↥C.LL.1 V1] [Module ℚ_[D.nd.l i] V1]
          [IsScalarTower ℚ_[D.nd.l i] ↥C.LL.1 V1] [FiniteDimensional ↥C.LL.1 V1]
          (ρ1 : Representation ↥C.LL.1 (Br.G D.nbr i w hw) V1),
          IsSubOfSums ρ1 (fun x : D.nd.X i => ⇑(Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (r i) x))) →
          IsCrys (Br.PD D.loc D.nbr i w hw) ρ1 ∧
          ∀ τ a, IsJumpV (Br.PD D.loc D.nbr i w hw) ρ1 τ a →
            ∃ x : D.nd.X i, IsJumpV (Br.PD D.loc D.nbr i w hw)
              (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (r i) x))) τ (-a - 1)) ∧
      (∀ π ∈ D.nd.Zgood i,
          IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i (ρ i) π))) ∧
          ∀ τ (a : ℤ),
            ((IsJumpV (Br.PD D.loc D.nbr i w hw)
                (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (r i) π))) τ (-a - 1) ∧
                ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ))) →
              multV (Br.PD D.loc D.nbr i w hw)
                (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i (ρ i) π))) τ a = 1) ∧
            (¬ (IsJumpV (Br.PD D.loc D.nbr i w hw)
                (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (r i) π))) τ (-a - 1) ∧
                ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ))) →
              multV (Br.PD D.loc D.nbr i w hw)
                (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i (ρ i) π))) τ a = 0))

def ParametersPolynomiallyBounded (large₂ : SizeData₂ D) : Prop := large₂.Sc + large₂.etaSz + D.R.t + 2 ≤ large₂.sc.b

def Conclusion0 (D : D7) : Prop :=
  ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      (∃ y : Om (D.nd.l i), y ^ 2 = -(D.nd.l i : Om (D.nd.l i)) ∧
        (D.nbr i w hw).Kw.1 = K0 (D.nbr i w hw).Kw ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y}) ∧
      (D.nbr i w hw).Kw.1 ≤ Ks (D.nbr i w hw).Kw 1 ∧
      finrank ↥(K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1 = 2 ∧
      finrank ℚ_[D.nd.l i] ↥(Ks (D.nbr i w hw).Kw 1) =
        (D.nd.l i - 1) / 2 * finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1

end Glob

end Formalism.MainNotions.EmbeddingTypeJumps

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

def sig2 (l H : ℕ) : ℝ := 2 * (H : ℝ) / ((l : ℝ) - 1) ^ 2 + 1

def Mpar (l h : ℕ) : ℕ := h / (l - 1) + 1

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def DL (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) : Prop :=
  (letE i : LetA O n) • x = x ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x

def InPN (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (k : ℕ) (x : W.DD T) : Prop :=
  ∃ y ∈ W.N T, (∀ δ ∈ W.DelF, W.γD T δ y = y) ∧ x = W.π₀ ^ k • y

def PolesFin (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T) : Prop :=
  ∃ k : ℕ, W.InvN T (∏ j ∈ Finset.range k, Formalism.MainNotions.LiftingTheory.pk W j) x

def Dlat (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) : Set (T.V ⊗[Qp] B) :=
  {z | ∃ (x : W.DD T) (hx : x ∈ W.N T), DL W T i x ∧ z = W.cmp T ⟨x, hx⟩}

def DlatImg (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (i : ZMod n) : Set (T₂.V ⊗[Qp] B) :=
  {z | ∃ (x : W.DD T₁) (_ : x ∈ W.N T₁) (hx' : W.map F x ∈ W.N T₂), DL W T₁ i x ∧ z = W.cmp T₂ ⟨W.map F x, hx'⟩}

def RankFC [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n,
      ((i.val + d) % 2 = 0 →
        finrank LL ↥(FilCris PD T₂.ρ (-(η : ℤ)) ⊓ DcrisL PD T₂.ρ (W.emb i)) ≤ m) ∧
      ((i.val + d) % 2 = 1 →
        (finrank LL ↥(DcrisL PD T₂.ρ (W.emb i)) : ℤ) -
          finrank LL ↥(FilCris PD T₂.ρ (b i : ℤ) ⊓ DcrisL PD T₂.ρ (W.emb i)) ≤ m)

def QTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ)
    (Mi hi : ZMod n → ℕ),
    Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m → Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi →
    (∀ i : ZMod n,
      Formalism.MainNotions.LiftingTheory.Kills W F i (W.π₀ ^ (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi / (PD.p - 1) + 1)) ∧
      Formalism.MainNotions.LiftingTheory.Kills W F i (Formalism.MainNotions.LiftingTheory.lp W (Formalism.MainNotions.LiftingTheory.eWA PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi))) ∧
      Formalism.MainNotions.LiftingTheory.Kills W F i
        (Formalism.MainNotions.LiftingTheory.qp W ^ ⌈Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η)⌉₊)) ∧
    ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L),
      IsSESLat (G := G) (Qp := Qp) (LL := LL) (O := O) ι π → IsCrys PD Y.ρ →
      ∀ i : ZMod n,
        Formalism.MainNotions.LiftingTheory.Kills W π i (W.π₀ ^ (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi / (PD.p - 1) + 1)) ∧
        Formalism.MainNotions.LiftingTheory.Kills W π i (Formalism.MainNotions.LiftingTheory.lp W (Formalism.MainNotions.LiftingTheory.eWA PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi))) ∧
        Formalism.MainNotions.LiftingTheory.Kills W π i
          (Formalism.MainNotions.LiftingTheory.qp W ^ ⌈Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η)⌉₊)

def dOp (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T) : W.DD T :=
  Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) • (W.γ T x - x)

def InQN (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (k : ℤ) (x : W.DD T) : Prop :=
  DL W T i x ∧
    (if 0 ≤ k then Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x ∈ W.N T else
      ∃ y ∈ W.N T, x = Formalism.MainNotions.LiftingTheory.qp W ^ (-k).toNat • y)

def cR (W : LocWach PD LL O v n) (j : ℤ) : LL :=
  (algebraMap O LL (((W.χΓ W.gam) ^ (-j) : Oˣ) : O) - 1) / (-(PD.p : LL))

def eY (l y : ℕ) : ℕ := ⌈(y : ℝ) * l / ((l : ℝ) - 1)⌉₊

def InI (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (w : W.DD T) : Prop :=
  DL W T i w ∧ PolesFin W T w ∧ InPN W T 1 (W.γ T w - w)

def IsSer (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (w : W.DD T)
    (c : ℕ → W.DD T) : Prop :=
  c 0 = 0 ∧ (∀ y, DL W T i (c y) ∧ c y ∈ W.N T) ∧
    ∀ K : ℕ, ∃ j : ℕ, InPN W T K (((PD.p : ℕ) : O) ^ j •
      (((PD.p : ℕ) : O) ^ eY PD.p K • (W.γ T w - w) -
        ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (eY PD.p K - eY PD.p y) •
          (W.γ T (W.π₀ ^ y • c y) - W.π₀ ^ y • c y)))

def TTool1 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (w : W.DD T),
    InI W T i w →
    (∃ c, IsSer W T i w c) ∧ ∀ c c', IsSer W T i w c → IsSer W T i w c' → ∀ K : ℕ, ∃ j : ℕ,
      InPN W T K (((PD.p : ℕ) : O) ^ j • ∑ y ∈ Finset.range K,
        ((PD.p : ℕ) : O) ^ (eY PD.p K - eY PD.p y) • (W.π₀ ^ y • (c y - c' y)))

def fMX (W : LocWach PD LL O v n) (M X : ℕ) : LetA O n := W.π₀ ^ M * Formalism.MainNotions.LiftingTheory.qp W ^ X

def IsRem (W : LocWach PD LL O v n) (j M X y : ℕ) (r : LetA O n) : Prop :=
  (∃ a : ℕ → O, r = ∑ k ∈ Finset.range (M + X), algebraMap O (LetA O n) (a k) * W.π₀ ^ k) ∧
    ∃ g : LetA O n, ((W.φA ^ j) W.π₀) ^ y - r = fMX W M X * g

def pullJ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (j : ℕ) :
    Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n) (((W.φD T) ^ j) '' {x | x ∈ W.N T ∧ DL W T i x})

def IsTrunc (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (j M X σ : ℕ)
    (w z : W.DD T) : Prop :=
  ∃ (c : ℕ → W.DD T) (r s : ℕ → LetA O n), IsSer W T i w c ∧
    (∀ y, IsRem W j M X y (r y) ∧
      ((PD.p : ℕ) : LetA O n) ^ eY PD.p y * s y = ((PD.p : ℕ) : LetA O n) ^ σ * r y) ∧
    z = ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) w -
      ∑ y ∈ Finset.range (max M X + 1), s y • ((W.φD T) ^ j) (c y)

def TCase (l j M X σ : ℕ) : Prop :=
  (j = 1 ∧ 1 ≤ M ∧ σ = ⌈((M : ℝ) + X) / ((l : ℝ) - 1) + 1⌉₊) ∨
    (j = 2 ∧ M = 1 ∧ σ = ⌈(X : ℝ) / ((l : ℝ) - 1) ^ 2 + 1⌉₊)

def TTool2 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 11 ≤ PD.p → ∀ (j M X σ : ℕ), TCase PD.p j M X σ →
  (∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n),
    (∀ w, InI W T i w → ∃ z, IsTrunc W T i j M X σ w z) ∧
    (∀ w z, InI W T i w → IsTrunc W T i j M X σ w z →
      z - ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) w ∈ pullJ W T i j ∧
      ∃ p ∈ pullJ W T i j, W.γ T z - z = fMX W M X • p) ∧
    (∀ w z z', InI W T i w → IsTrunc W T i j M X σ w z → IsTrunc W T i j M X σ w z' →
      ∃ p ∈ pullJ W T i j, z - z' = fMX W M X • p) ∧
    (∀ (a a' : O) w w' z z' z'', InI W T i w → InI W T i w' → IsTrunc W T i j M X σ w z →
      IsTrunc W T i j M X σ w' z' → IsTrunc W T i j M X σ (a • w + a' • w') z'' →
      ∃ p ∈ pullJ W T i j, z'' - (a • z + a' • z') = fMX W M X • p) ∧
    (∀ w z, InI W T i w → InPN W T 1 w → IsTrunc W T i j M X σ w z →
      ∃ p ∈ pullJ W T i j, z = fMX W M X • p) ∧
    (∀ p ∈ pullJ W T i j, ∃ p' ∈ pullJ W T i j,
      ((PD.p : ℕ) : O) ^ (2 * σ) • p - fMX W M X • p' ∈ Submodule.span (LetA O n)
        {z | ∃ w, w ∈ W.N T ∧ InI W T i w ∧ IsTrunc W T i j M X σ w z})) ∧
  ∀ (T T' : LocLat G Qp LL O) (F : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    ∀ (i : ZMod n) w z z', InI W T i w → IsTrunc W T i j M X σ w z →
      IsTrunc W T' i j M X σ (W.map F w) z' →
      ∃ p ∈ pullJ W T' i j, W.map F z - z' = fMX W M X • p

def THor [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 11 ≤ PD.p → ∀ (j M X σ : ℕ), TCase PD.p j M X σ →
  ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (w z : W.DD T) (hw : w ∈ W.N T),
    InI W T i w → IsTrunc W T i j M X σ w z →
    ∀ (ζ : LL) (R k : ℕ) (a : LetA O n) (hk : (Formalism.MainNotions.LiftingTheory.qp W ^ k * a) • z ∈ W.N T),
      ((IsPrimitiveRoot ζ PD.p ∧ R = k + X) ∨ (ζ = 1 ∧ R = (PD.p - 1) * M)) →
      (∀ r : ℤ, r < 0 → W.levN T (i + (j : ZMod n)) ζ ⟨_, hk⟩ r = 0) ∧
      ∀ r : ℕ, r < R → W.levN T (i + (j : ZMod n)) ζ ⟨_, hk⟩ (r : ℤ) =
        PowerSeries.coeff r (W.lev (i + (j : ZMod n)) ζ (Formalism.MainNotions.LiftingTheory.qp W ^ k * a)) •
          ((PD.p : LL) ^ σ • ιV PD (LL := LL) (V := T.V)
            ((φVB PD (LL := LL) (V := T.V))^[j] (W.cmp T ⟨w, hw⟩)))

def FTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m →
    ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ →
      (∀ i τ, Formalism.MainNotions.LiftingTheory.Over W τ i →
        JumpsInV PD T.ρ τ (Set.Ici (-((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S : ℕ) : ℤ)))) →
      (∀ (c : ZMod n) τ, (c.val + d) % 2 = 0 → Formalism.MainNotions.LiftingTheory.Over W τ (c + 1) →
        JumpsInV PD T.ρ τ (Set.Ici (-(η : ℤ)))) →
      let M := Mpar PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S)
      (∀ (i : ZMod n) (x : W.DD T), x ∈ W.N T → DL W T (i - 1) x →
        ∃ y ∈ W.N T, W.φD T (W.π₀ ^ M • x) = (W.π₀ ^ M * Formalism.MainNotions.LiftingTheory.qp W) • y) ∧
      (∀ w, InPN W T M w → ∃! z, InPN W T M z ∧ W.φD T z - z = w) ∧
      (∀ (i : ZMod n) (x : W.wachCocyclesDelta T), DL W T i (x : W.DD T × W.DD T).1 →
        InPN W T M (x : W.DD T × W.DD T).2 →
          (InPN W T M (x : W.DD T × W.DD T).1 → W.clK T x = 0) ∧
          (PolesFin W T (x : W.DD T × W.DD T).1 → W.clK T x ∈ latticeFiniteCohomology PD T.L)) ∧
      (∀ (c : ZMod n) (x : W.DD T), (c.val + d) % 2 = 0 → x ∈ W.φpull T →
        (letE (c + 1) : LetA O n) • x = x → Formalism.MainNotions.LiftingTheory.qp W ^ η • x ∈ W.N T) ∧
      (∀ (c : ZMod n) (w z : W.DD T), (c.val + d) % 2 = 0 → InI W T c w →
        IsTrunc W T c 1 M η ⌈((M : ℝ) + η) / ((PD.p : ℝ) - 1) + 1⌉₊ w z →
        (∃ x : W.wachCocyclesDelta T, (x : W.DD T × W.DD T).1 = z ∧ InPN W T M (x : W.DD T × W.DD T).2) ∧
        (InPN W T 1 w → ∀ x : W.wachCocyclesDelta T, (x : W.DD T × W.DD T).1 = z →
          InPN W T M (x : W.DD T × W.DD T).2 → W.clK T x = 0))

end Core

section Lit

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    (LL O : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

end Lit

def TToolAlg : Prop :=
  (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ) [Fact l.Prime]
    (ϖ : O) (e : ℕ), Irreducible ϖ → 1 ≤ e → Associated (l : O) (ϖ ^ e) →
    ∀ (u₁ u₂ u ε : PowerSeries O), IsUnit u₁ → IsUnit u₂ → IsUnit u → IsUnit ε →
    ∀ (y X M η t : ℕ),
      ((t : ℝ) ≤ e * max 0 ((l : ℝ) * y - X) →
        (u₁ * PowerSeries.X * (PowerSeries.X + PowerSeries.C (l : O)) ^ (l - 1)) ^ y ∈
          Ideal.span {PowerSeries.C (ϖ ^ t),
            PowerSeries.X * (PowerSeries.X + PowerSeries.C (l : O)) ^ X}) ∧
      ((t : ℝ) ≤ e * max 0 ((l : ℝ) * y - η - M) →
        (u₁ * PowerSeries.X * (PowerSeries.X + PowerSeries.C (l : O)) ^ (l - 1)) ^ y ∈
          Ideal.span {PowerSeries.C (ϖ ^ t),
            PowerSeries.X ^ M * (PowerSeries.X + PowerSeries.C (l : O)) ^ η}) ∧
      ((t : ℝ) ≤ e * max 0 (((l : ℝ) - 1) * y - (X : ℝ) / l) →
        (u₂ * PowerSeries.X * (PowerSeries.X + PowerSeries.C (l : O)) ^ (l - 1) *
            (u * (PowerSeries.X + PowerSeries.C (l : O)) ^ l + PowerSeries.C (l : O) * ε) ^ (l - 1))
            ^ y ∈
          Ideal.span {PowerSeries.C (ϖ ^ t),
            PowerSeries.X * (PowerSeries.X + PowerSeries.C (l : O)) ^ X})) ∧
  ∀ (l y X M η : ℕ), 11 ≤ l →
    (y : ℝ) * l / ((l : ℝ) - 1) - max 0 ((l : ℝ) * y - X) ≤ ((X : ℝ) + 1) / ((l : ℝ) - 1) + 1 ∧
    (y : ℝ) * l / ((l : ℝ) - 1) - max 0 ((l : ℝ) * y - η - M) ≤
      ((M : ℝ) + η) / ((l : ℝ) - 1) + 1 ∧
    (y : ℝ) * l / ((l : ℝ) - 1) - max 0 (((l : ℝ) - 1) * y - (X : ℝ) / l) ≤
      (X : ℝ) / ((l : ℝ) - 1) ^ 2 + 1

def PowerSeriesDVRFactorisation : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ) [Fact l.Prime]
    (ϖ : O) (e : ℕ), Irreducible ϖ → 1 ≤ e → Associated (l : O) (ϖ ^ e) →
    ∀ (ε u : PowerSeries O), IsUnit ε → IsUnit u →
    ∀ (b y t : ℕ), 1 ≤ b → (b : ℝ) / (l : ℝ) ≤ (y : ℝ) →
      (PowerSeries.C (l : O) * ε + u * PowerSeries.X ^ l) ^ y ∈
        Ideal.span {PowerSeries.C (ϖ ^ t), (PowerSeries.X : PowerSeries O) ^ b} →
      (t : ℝ) / (e : ℝ) ≤ (y : ℝ) - (b : ℝ) / (l : ℝ) + 2 + Real.logb (l : ℝ) (y : ℝ)

def adm6 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionW D HW F

def adm8 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionH D HW F

def adm9 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F

def adm12 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], RankFC ((HW l).W K 1 LL hg)

def adm13 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], QTool ((HW l).W K 1 LL hg)

def adm15 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  TToolAlg ∧ ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))],
    TTool1 ((HW l).W K 1 LL hg) ∧ TTool2 ((HW l).W K 1 LL hg)

def adm16 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], FTool ((HW l).W K 1 LL hg)

def FrobeniusExpansionCongruence (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], THor ((HW l).W K 1 LL hg)

end Formalism.MainNotions.CrystallineLiftingInputs
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.HerrClassFieldOfNorms
noncomputable section

namespace Formalism.MainNotions.HerrComplexNaturality

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def FN (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.adm9 D HW F

def HerrNaturality (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm17 D HW F

def AdmNat (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F

def HerrNaturalityTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmNat D HW F → HerrNaturality D HW F

theorem herr_naturality_theorem_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : HerrNaturalityTheorem D HW F := by
  intro h l _ K s LL g
  refine ⟨(h l K s LL g).2.2, ?_⟩
  intro hg T T' f pr pr' hp
  have h1 := (h l K s LL g).1 hg T
  exact (h1.2.2 T' f pr pr' hp).symm

def HerrExtensionClass (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm16 D HW F

def HerrExtensionUpToUnit (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Formalism.MainNotions.ElementDenominator.coreHerrExt ((HW l).W K s LL h) ∧ Formalism.MainNotions.ElementDenominator.coreHerrExtΔ ((HW l).W K s LL h)

theorem herr_class_maps_of_naturality (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h1 : HerrNaturality D HW F) (h2 : HerrExtensionUpToUnit D HW F) : Formalism.MainNotions.ElementDenominator.HerrClassMapsLocal D HW F :=
  fun l _ K s LL h => ⟨(h1 l K s LL h).1, (h1 l K s LL h).2, (h2 l K s LL h).1, (h2 l K s LL h).2⟩

end Formalism.MainNotions.HerrComplexNaturality
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.ResidualIrreducibleOfTheoremThreePrime
noncomputable section

namespace Formalism.MainNotions.AdmissibleThreePrime

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem parts_of (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (hx : HasParamX D.nd D.naut i x Sig) :
    (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) ∧ rankIso D.nd D.naut Sig = D.R.r := by
  obtain ⟨P, -, hBC⟩ := hx
  refine ⟨fun p hp => ?_, ?_⟩
  · have hm : (⟨p.a, D.naut.tw p.π D.naut.etaTinv, p.d⟩ : Formalism.BasicNotions.Part D.naut.CG) ∈
        twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv :=
      List.mem_map.2 ⟨p, List.mem_append_left _ hp, rfl⟩
    exact ⟨(hBC.1 _ hm).1, (hBC.1 _ hm).2.1⟩
  · have h := hBC.2.2.1
    have e : rankIso D.nd D.naut (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) =
        rankIso D.nd D.naut Sig + D.R.t := by
      simp [rankIso, twistIso, muPart, List.map_map, Function.comp_def]
    rw [e] at h
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega

theorem cusp_of (D : D7) (hT : SumRepresentations.tieLab D) (i : D.nd.Loc) (x : D.nd.X i)
    (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) (hx : HasParamX D.nd D.naut i x Sig)
    (hg : goodSig D.nd D.naut Sig) : IsCuspIso D.nd D.naut Sig := by
  obtain ⟨hpos, hrank⟩ := parts_of D i x Sig hx
  let k : Fin 2 := 0
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨h1, h2, -, -, h5, -⟩ := (hg k).1
  have : Nonempty (D.nd.PlG k) := by
    rw [← Fintype.card_pos_iff, D.nd.card_PlG k]
    show 0 < 2 * D.R.n
    have := D.R.ord_pos
    show 0 < 2 * D.R.ord
    omega
  have hr : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    show 1 ≤ D.R.k + D.R.m - 1
    omega
  have hf : ∀ v, D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)) =
      ∏ j : Fin Sig.length,
        D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v)) ^ (Sig.get j).d := by
    intro v
    rw [SumRepresentations.inertiaCharpoly_eq_of_iso D.nd D.naut hT k v Sig,
      SumRepresentations.list_prod_fin Sig (fun p => D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v)) ^ p.d)]
  have hrk : ∑ j : Fin Sig.length, (Sig.get j).a * (Sig.get j).d = D.R.r := by
    rw [← hrank, rankIso, SumRepresentations.list_sum_fin Sig (fun p => p.a * p.d)]
  have hd : ∀ j : Fin Sig.length, 1 ≤ (Sig.get j).a ∧ 1 ≤ (Sig.get j).d :=
    fun j => hpos _ (List.get_mem Sig j)
  have hdeg : ∀ v (j : Fin Sig.length),
      (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree =
        (Sig.get j).a := by
    intro v
    have hne : ∀ j ∈ (Finset.univ : Finset (Fin Sig.length)),
        D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v)) ^ (Sig.get j).d ≠ 0 := by
      rw [← Finset.prod_ne_zero_iff, ← hf v]
      exact (h1 v).1.ne_zero
    have hsum : ∑ j : Fin Sig.length,
        (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree *
          (Sig.get j).d =
        ∑ j : Fin Sig.length, (Sig.get j).a * (Sig.get j).d := by
      have h1' : (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r :=
        (h1 v).2.1
      rw [hrk, ← h1', hf v, natDegree_prod _ _ hne]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [natDegree_pow, mul_comm]
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin Sig.length)),
        (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree *
          (Sig.get j).d ≤ (Sig.get j).a * (Sig.get j).d := by
      intro j _
      refine Nat.mul_le_mul_right _ ?_
      have := hT.2 k v (D.naut.locG (Sig.get j).π (D.naut.plGw k v))
      rwa [D.naut.locG_dim] at this
    intro j
    have := (Finset.sum_eq_sum_iff_of_le hle).1 hsum j (Finset.mem_univ j)
    exact Nat.eq_of_mul_eq_mul_right (hd j).2 this
  obtain ⟨hc, hall⟩ := Formalism.IrreducibleCountingLemmas.Z.good_cuspidal_multiplicity_one (ZMod (D.host.g k)) (D.nd.PlG k) D.R.r
    (fun v => D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))
    (Fin Sig.length) (fun j => (Sig.get j).a) (fun j => (Sig.get j).d)
    (fun v j => D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))) hr
    (fun v => (h1 v).2.1) h2 hf hdeg (fun j => (hd j).1) (fun j => (hd j).2)
    (by
      rintro ⟨a, ha1, ha2, ha⟩
      obtain ⟨v, hv⟩ := h5 a ha1 ha2
      exact hv (ha v))
  rw [Fintype.card_fin] at hc
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hc
  obtain ⟨hd1, ha1⟩ := hall ⟨0, by simp⟩
  obtain ⟨a, π, d⟩ := p
  simp only [List.get_eq_getElem, List.getElem_cons_zero] at hd1 ha1
  subst hd1 ha1
  exact ⟨π, rfl⟩

theorem eq_of_root_prod {K A : Type} [Field K] (s : Multiset A) (F : A → K) (a : K)
    (h : ((s.map fun x => X - C (F x)).prod).IsRoot a) : ∃ x ∈ s, F x = a := by
  rw [IsRoot, eval_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map] at h
  obtain ⟨y, hy, e⟩ := Multiset.mem_map.1 h
  refine ⟨y, hy, ?_⟩
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C] at e
  exact (sub_eq_zero.1 e).symm

theorem isOfFinOrder_root {g : ℕ} [Fact g.Prime] {N : ℕ} {f : (ZMod g)[X]} (hf : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.GoodPoly N f)
    {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ∈ Formalism.CyclotomicNorms.rootsBar f) : IsOfFinOrder x := by
  obtain ⟨r, σ, -, hmap, hσ⟩ := Formalism.CyclotomicNorms.CycleTypeFiniteOrder.exists_index hf
  rw [← hmap] at hx
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hx
  exact Formalism.CyclotomicNorms.CycleTypeFiniteOrder.isOfFinOrder_of_index hσ j (Formalism.CyclotomicNorms.CycleTypeFiniteOrder.ne_zero_of_mem hf (hmap ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val j)))

theorem isOfFinOrder_alg {g : ℕ} [Fact g.Prime] (u : (ZMod g)ˣ) :
    IsOfFinOrder (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (u : ZMod g)) := by
  have hu : IsOfFinOrder u := isOfFinOrder_of_finite u
  exact (MonoidHom.isOfFinOrder ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom.comp (Units.coeHom (ZMod g))) hu)

theorem primeToPart_inv {K : Type} [Field K] (ℓ : ℕ) (c : K) (hc : c ≠ 0) :
    Formalism.CyclotomicNorms.primeToPart ℓ c⁻¹ = (Formalism.CyclotomicNorms.primeToPart ℓ c)⁻¹ := by
  have ho : orderOf c⁻¹ = orderOf c := by
    let u : Kˣ := Units.mk0 c hc
    have h1 : (u : K) = c := rfl
    rw [← h1, ← Units.val_inv_eq_inv_val, orderOf_units, orderOf_units, orderOf_inv]
  unfold Formalism.CyclotomicNorms.primeToPart
  rw [ho, inv_pow]

theorem not_root_of {g ℓ : ℕ} [Fact g.Prime] [hℓ : Fact ℓ.Prime] (hℓg : ℓ ≠ g) {N : ℕ} {PP J : Type}
    (f : PP → (ZMod g)[X]) (χ : PP → J → (ZMod g)ˣ) (hG1 : Formalism.CyclotomicNorms.IsGood N g f χ)
    (hG2 : Formalism.CyclotomicNorms.IsGood N g f (fun v j => (χ v j)⁻¹)) (v : PP) (j : J)
    (ι : Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar ℓ)
    (hinj : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime ℓ → (orderOf y).Coprime ℓ →
      ι x = ι y → x = y)
    (e₁ e₂ : ℤ) (he₁ : e₁ = 1 ∨ e₁ = -1) (he₂ : e₂ = 1 ∨ e₂ = -1) :
    ¬ (((Formalism.CyclotomicNorms.rootsBar (f v)).map fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart ℓ x) ^ e₁)).prod).IsRoot
      (ι (Formalism.CyclotomicNorms.primeToPart ℓ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (χ v j : ZMod g))) ^ e₂) := by
  intro hroot
  obtain ⟨y, hy, hyeq⟩ := eq_of_root_prod _ (fun x => ι (Formalism.CyclotomicNorms.primeToPart ℓ x) ^ e₁) _ hroot
  obtain ⟨h1, h2, -, h3, -, -⟩ := hG1
  have h3' := hG2.2.2.2.1
  have gp : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.GoodPoly N (f v) := ⟨(h1 v).1, (h1 v).2.1, (h1 v).2.2, h2 v⟩
  have hy0 := Formalism.CyclotomicNorms.CycleTypeFiniteOrder.ne_zero_of_mem gp hy
  have hyfin := isOfFinOrder_root gp hy
  set c := algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (χ v j : ZMod g) with hcdef
  have hc0 : c ≠ 0 := (_root_.map_ne_zero _).2 (χ v j).ne_zero
  have hcfin : IsOfFinOrder c := isOfFinOrder_alg (χ v j)
  have hcinv : c⁻¹ = algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (((χ v j)⁻¹ : (ZMod g)ˣ) : ZMod g) := by
    rw [hcdef, Units.val_inv_eq_inv_val, map_inv₀]
  have hcifin : IsOfFinOrder c⁻¹ := hcinv ▸ isOfFinOrder_alg (χ v j)⁻¹
  have ppne : ∀ z : Formalism.CyclotomicNorms.Fbar g, z ≠ 0 → Formalism.CyclotomicNorms.primeToPart ℓ z ≠ 0 := fun z hz => by
    unfold Formalism.CyclotomicNorms.primeToPart; exact pow_ne_zero _ hz
  have cop : ∀ z : Formalism.CyclotomicNorms.Fbar g, IsOfFinOrder z → (orderOf (Formalism.CyclotomicNorms.primeToPart ℓ z)).Coprime ℓ :=
    fun z hz => Formalism.CyclotomicNorms.CycleTypeFiniteOrder.primeToPart_coprime hℓ.out z hz
  have hιinv : ∀ z : Formalism.CyclotomicNorms.Fbar g, z ≠ 0 → ι z⁻¹ = (ι z)⁻¹ := fun z hz =>
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel₀ hz, map_one])

  have case1 : ι (Formalism.CyclotomicNorms.primeToPart ℓ y) = ι (Formalism.CyclotomicNorms.primeToPart ℓ c) → False := fun e =>
    h3 ℓ hℓ.out hℓg v j y hy
      (hinj _ _ (ppne y hy0) (ppne c hc0) (cop y hyfin) (cop c hcfin) e)
  have case2 : ι (Formalism.CyclotomicNorms.primeToPart ℓ y) = (ι (Formalism.CyclotomicNorms.primeToPart ℓ c))⁻¹ → False := fun e => by
    rw [← hιinv _ (ppne c hc0), ← primeToPart_inv _ _ hc0] at e
    have := hinj _ _ (ppne y hy0) (ppne _ (inv_ne_zero hc0)) (cop y hyfin) (cop _ hcifin) e
    rw [hcinv] at this
    exact h3' ℓ hℓ.out hℓg v j y hy this
  rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl
  · simp only [zpow_one] at hyeq; exact case1 hyeq
  · simp only [zpow_one, zpow_neg] at hyeq; exact case2 hyeq
  · simp only [zpow_one, zpow_neg] at hyeq
    exact case2 (by rw [← hyeq, inv_inv])
  · simp only [zpow_neg, zpow_one, inv_inj] at hyeq; exact case1 hyeq

end Formalism.MainNotions.AdmissibleThreePrime
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoryWindows
noncomputable section

open Classical

namespace Formalism.MainNotions.LocalTheoryWindows

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

inductive LT where
  | thin : LT
  | up (b : ℕ) : LT
  | down (b : ℕ) : LT
  deriving DecidableEq

def LT.thick : LT → Bool
  | .thin => false
  | _ => true

def LT.isUp : LT → Bool
  | .up _ => true
  | _ => false

def LT.isDown : LT → Bool
  | .down _ => true
  | _ => false

def LT.size : LT → ℕ
  | .thin => 0
  | .up b => b
  | .down b => b

def LT.win (G S η : ℕ) : LT → Set ℤ
  | .thin => Set.Icc (-(G : ℤ)) G
  | .up b => Set.Icc (b : ℤ) (b + S) ∪ Set.Icc (-(η : ℤ)) η
  | .down b => Set.Icc (-(b : ℤ) - S) (-(b : ℤ)) ∪ Set.Icc (-(η : ℤ)) η

def LT.ok (η : ℕ) : LT → Prop
  | .thin => True
  | .up b => η < b
  | .down b => η < b

def CutsOK (n j : ℕ) (ty : ZMod n → LT) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) : Prop :=
  cuts.Nonempty ∧ 1 ≤ j ∧
    (∀ c ∈ cuts, 1 ≤ arcLen c ∧ arcLen c ≤ n ∧ c - ((arcLen c : ℕ) : ZMod n) ∈ cuts ∧
      ∀ d : ℕ, 1 ≤ d → d < arcLen c → c - (d : ZMod n) ∉ cuts) ∧
    (∀ c ∈ cuts, j ≤ arcLen c) ∧
    (∀ c ∈ cuts, ∀ k : ℕ, 1 ≤ k → k ≤ j → ty (c + (k : ZMod n)) = LT.thin)

def thickLv {n : ℕ} (ty : ZMod n → LT) (arcLen : ZMod n → ℕ) (c : ZMod n) : Finset ℕ :=
  (Finset.range (arcLen c)).filter fun s => (ty (c - (s : ZMod n))).thick

def ro {n : ℕ} (ty : ZMod n → LT) (arcLen : ZMod n → ℕ) (c : ZMod n) : ℕ :=
  (thickLv ty arcLen c).card

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

end Core

section Lit

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {Bc BdR : Type} [CommRing Bc] [CommRing BdR] [Algebra Qp Bc] [Algebra K₀ Bc]
    [IsScalarTower Qp K₀ Bc] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

def H1fGeneratorBound (PD : PeriodData G Qp K₀ K Bc BdR) (LL O : Type) [Field LL] [Algebra Qp LL]
    [TopologicalSpace LL] [CommRing O] [Algebra O LL] : Prop :=
  Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBound PD LL O

end Lit

section Theory

def H1fGeneratorBoundAll (Th : LocTheory) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBoundAll Th

end Theory

end Formalism.MainNotions.LocalTheoryWindows
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.VKEqOfFrac
noncomputable section

namespace Formalism.MainNotions.TwOe

open Formalism.MainNotions.BlochKatoReduction.Gen

variable {R R' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']

private theorem exists_ne_zero_addVal_algebraMap_eq_mul (hinj : Function.Injective (algebraMap R R')) [Module.Finite R R'] :
    ∃ e : ℕ, e ≠ 0 ∧ ∀ y : R, IsDiscreteValuationRing.addVal R' (algebraMap R R' y) =
      (e : ℕ∞) * IsDiscreteValuationRing.addVal R y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible R'
  have h0 : algebraMap R R' ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ'
  have hnu : ¬ IsUnit (algebraMap R R' ϖ) := by
    intro hu
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R)
      (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (IsLocalRing.maximalIdeal R')
    have heq := IsLocalRing.eq_maximalIdeal hmax
    have hmem : ϖ ∈ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') := by
      rw [heq]; exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
    exact ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp hmem)) hu
  have he : e ≠ 0 := by
    rintro rfl
    apply hnu
    rw [hw, pow_zero, mul_one]
    exact w.isUnit
  refine ⟨e, he, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, AddValuation.map_zero, AddValuation.map_zero, ENat.mul_top (by exact_mod_cast he)]
  · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
    rw [IsDiscreteValuationRing.addVal_def y u hϖ n hu]
    have hy' : algebraMap R R' y =
        ↑(Units.map (algebraMap R R' : R →* R') u * w ^ n) * ϖ' ^ (e * n) := by
      rw [hu, map_mul, map_pow, hw]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_ofClass]
      ring
    rw [IsDiscreteValuationRing.addVal_def _ _ hϖ' _ hy']
    push_cast
    ring

theorem nval_map (hinj : Function.Injective (algebraMap R R')) [Module.Finite R R'] (l : ℕ) (x : R) :
    nval R' l (algebraMap R R' x) = nval R l x := by
  obtain ⟨e, he, hE⟩ := exists_ne_zero_addVal_algebraMap_eq_mul hinj
  simp only [nval]
  rw [hE x, ← map_natCast (algebraMap R R') l, hE]
  simp only [ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_mul]
  exact mul_div_mul_left _ _ (by exact_mod_cast he)

end Formalism.MainNotions.TwOe

end
end
