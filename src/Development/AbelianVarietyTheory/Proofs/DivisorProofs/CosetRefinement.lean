module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PaddedLastEntry
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfData
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MeanPeriodLogarithms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
noncomputable section

namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds
open scoped ComplexOrder

section Ops

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def OpLe (S S' : GSD K) (v : InfinitePlace K) (T : S.V →ₗ[K] S'.V) (t : ℝ) : Prop :=
  ∀ x : S.V, (S'.pairAt v (T x) (T x)).re ≤ t * (S.pairAt v x x).re

def PosAt (S : GSD K) (v : InfinitePlace K) : Prop := (S.gramV.map v.embedding).PosSemidef

end Ops

section Coef

variable {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι]

def sqAt (σ : K →+* ℂ) {n : ℕ} (lam : ι → DomWeight n) (x : Formalism.L2.DIV.VV K lam) : ℝ :=
  (∑ i, ∑ j, starRingEnd ℂ (σ ((bVV K lam).repr x i)) *
    σ (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) (bVV K lam i) (bVV K lam j)) * σ ((bVV K lam).repr x j)).re

def CoefOpLe (σ : K →+* ℂ) {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (T : Formalism.L2.DIV.VV K lam →ₗ[K] Formalism.L2.DIV.VV K lam') (t : ℝ) : Prop :=
  ∀ x, sqAt σ lam' (T x) ≤ t * sqAt σ lam x


open Classical in
def degAt {a b : ℕ} (e : DVar ι a b →₀ ℕ) (τ : ι) : ℕ := ∑ k ∈ e.support.filter (fun k => k.1 = τ), e k

end Coef

section Data

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}

def LocSmall (q : ℕ) (M : Submodule (𝓞 E) (Sp E a)) (M' : Submodule (𝓞 E) (Sp E b)) (Φ : HomE E a b → K) (β : ℝ) : Prop :=
  (∀ x, Φ x ≠ 0 → ∀ y ∈ M, x y ∈ M') ∧ (∀ x z : HomE E a b, (∀ y ∈ M, z y ∈ M') → Φ (x + (q : E) • z) = Φ x) ∧
    ∀ (σ : K →+* ℂ) (x : HomE E a b), ‖σ (Φ x)‖ ≤ β

def SmallDatum (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ)
    (Ξ : HomE E a b → K) (β : ℝ) : Prop :=
  (∀ x, Ξ x ≠ 0 → x ∈ homAt S N N') ∧ (∀ x, ∀ y ∈ mulLat c (homAt S N N'), Ξ (x + y) = Ξ x) ∧
    ∀ (σ : K →+* ℂ) (x : HomE E a b), ‖σ (Ξ x)‖ ≤ β

end Data

def Pres (D : D7) (T : TaylorLogMetric.Tor D) {a b : ℕ} (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (G F : TaylorLogMetric.VC D a b → ℂ) (n : ℝ) : Prop :=
  ∃ (k : ℕ) (r : Fin k → ℂ) (y : Fin k → TaylorLogMetric.VC D a b), (∀ i, r i ∈ TaylorLogMetric.Qbar) ∧ (∀ i, StandardLatticesGL3.LaQ D T L L' (y i)) ∧
    (∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, ∑ i, ‖StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (r i)‖ ≤ n) ∧ F = StandardLatticesGL3.comb D T r y G

def toHost {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (F : VCx X.Tau a b → ℂ) : TaylorLogMetric.VC D a b → ℂ :=
  fun w => F fun τ => w (s.iT τ)

def supConst (D : D7) (a b : ℕ) : ℝ :=
  3 * (2 * ((TaylorLogMetric.fF D * a * b : ℕ) : ℝ) * D.host.rdE + 1) ^ (TaylorLogMetric.fF D * a * b)

def errUnit (N : NumDatum) (T : ℕ) : ℝ :=
  N.R.f * (N.R.m : ℝ) ^ 2 * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * T)

def FamilyTie : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → B.kc.YFinite → StandardLatticesGL3.natTie D cc δ (B.eNat χ)

def FamilyVectors : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → B.kc.YFinite → B.VecP χ

def FamilyNorms : Prop :=
  ∃ C : ℝ, ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → B.kc.YFinite → B.ThP C χ

def PeriodLattices : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ), X.Ok → s.Ok → TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    TaylorLogMetric.IsChi D χ → IsDgen D cD → B.kc.YFinite → ∀ (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))), Even a → Even b →
    (∀ P ∈ S, conjPrime₂ P ∉ S) → (ambOf s B χ cD).AAUnit S → (ambOf s B χ cD).LaHyp a b S

def CosetRefinement : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (Md : ℕ), X.Ok →
    (∀ P ∈ S, (2 : 𝓞 X.E) ∉ P.asIdeal) → Odd Md → A.LaHyp a b S → A.IndAdd a b S Md

end GlobalTheory.ColNorms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbBaseChange

theorem isAbelianScheme_and_relDim_of_isGrpPullback : ∀ {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (φ : A'.left ⟶ A.left) (g : ℕ), IsGrpPullback A' A (spMap f) φ → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom := by
  intro R R' _ _ f A _ A' _ φ g h hA hg
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  exact ⟨GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h,
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h.1 hg⟩

end GlobalTheory.AbBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
noncomputable section

namespace GlobalTheory.ColumnNormCompare

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

@[reducible] def numDatumOfParameters (D : D7) (large₂ : SizeData₂ D) : NumDatum where
  R := D.R
  sc := large₂.sc
  H := D.host.toHostAx
  g := D.host.g
  g_prime := D.host.g_prime
  TT := D.host.TT
  Del := ⌊D.s.Del⌋₊
  h0 := ⌈LevelStarExponents.h0 large₂⌉₊
  hc := fun z => D.hc (tauPl D z)

def plRec (D : D7) : RPl D.R ≃ D.what₂.Tau := GlobalTheory.InertCompare.plEquiv D

def codeRec {D : D7} (large₂ : SizeData₂ D) (u : D.what₂.Word) : Code (numDatumOfParameters D large₂) := D.s.letter u

section Rec

variable {D : D7} (large₂ : SizeData₂ D) {EX : ErrX D} (Ch : Chars (recFields D) (recPrimes EX) D.R.m)
  (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (eta : Formalism.L2.Host.HChar D.host.E)
  (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))

end Rec

end GlobalTheory.ColumnNormCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBar
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem le_two_mul_ediv {x m T h : ℤ} (hm : 0 < m) (hT : 4 * m ≤ 5 * T) (hh : 0 ≤ h)
    (hx : 3 * h ≤ 4 * (x - m)) : h ≤ 2 * T * (x / m) := by
  have h1 : m * (x / m) + x % m = x := Int.mul_ediv_add_emod x m
  have h2 : x % m < m := Int.emod_lt_of_pos x hm
  have h3 : 0 ≤ x / m := Int.ediv_nonneg (by omega) hm.le
  have h4 : 4 * m * (x / m) ≤ 5 * T * (x / m) := mul_le_mul_of_nonneg_right hT h3
  have h5 : 0 ≤ T * (x / m) := mul_nonneg (by omega) h3
  nlinarith

theorem divided_gaps : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ (a b : Fin N), (b : ℕ) = a + 1 → (((b : ℕ) ≠ W.p → (W.T : ℤ) + W.Dd + 2 + 2 * N ≤ W.u1 τ a - W.u1 τ b) ∧ ((b : ℕ) = W.p → W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) ∧ W.h0 ≤ 4 * W.T * (W.u1 τ a - W.u1 τ b - 3 * N)) ∧ ((b : ℕ) ≠ W.p → W.kc ≤ (a : ℕ) → W.h0 ≤ 4 * W.T * (W.u1 τ a - W.u1 τ b))) := by
  intro ι _ N W H hD τ a b hab
  have hq := (hD τ).2 a b hab
  obtain ⟨g1, g2, g3⟩ := H.h4 τ a b hab
  obtain ⟨k1, k2⟩ := H.h2
  have c0 := H.weightConst_nonneg
  have h1 : 4 * (W.Dd : ℤ) + 4 ≤ W.T := by exact_mod_cast H.h1
  have hm : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1 := by positivity
  have hT : 4 * ((W.T : ℤ) + W.Dd + 1) ≤ 5 * (W.T : ℤ) := by omega
  have hh : 0 ≤ W.h0 := by omega
  refine ⟨fun hb => ?_, fun hb => ?_, fun hb ha => ?_⟩
  · rw [hq, if_neg hb]
    refine Int.le_ediv_of_mul_le hm ?_
    have := g1 hb
    have h0 : (0 : ℤ) ≤ (W.T : ℤ) + W.Dd + 2 + 2 * N := by positivity
    nlinarith
  · have := g3 hb
    have key : W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) := by
      rw [hq, if_pos hb]
      exact le_two_mul_ediv hm hT hh (by omega)
    exact ⟨key, by nlinarith⟩
  · have := g2 ha
    have key : W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) := by
      rw [hq, if_neg hb]
      exact le_two_mul_ediv hm hT hh (by omega)
    nlinarith

end GlobalTheory.MeanTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBarStatement
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedWeight_gaps_block_and_bar : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ (a b : Fin N), (b : ℕ) = a + 1 → (((b : ℕ) ≠ W.p → (W.T : ℤ) + W.Dd + 2 + 2 * N ≤ W.u1 τ a - W.u1 τ b) ∧ ((b : ℕ) = W.p → W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) ∧ W.h0 ≤ 4 * W.T * (W.u1 τ a - W.u1 τ b - 3 * N)) ∧ ((b : ℕ) ≠ W.p → W.kc ≤ (a : ℕ) → W.h0 ≤ 4 * W.T * (W.u1 τ a - W.u1 τ b))) := by
  first | exact @GlobalTheory.MeanTop.divided_gaps | exact GlobalTheory.MeanTop.divided_gaps | (intros; apply GlobalTheory.MeanTop.divided_gaps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullback
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem exists_grpObj_isGrpPullback_of_isPullback : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left), IsPullback φ s' A.hom (spMap σ) → ∃ _ : GrpObj (Over.mk s' : Over (Sp R')), IsGrpPullback (Over.mk s' : Over (Sp R')) A (spMap σ) φ ∧ (IsAbelianScheme A → IsAbelianScheme (Over.mk s' : Over (Sp R'))) ∧ ∀ g, SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g s' := by
  intro R R' _ _ σ A _ X' s' φ h
  letI : GrpObj ((Over.pullback (spMap σ)).obj A) := Functor.grpObjObj
  let e : Over.mk s' ≅ (Over.pullback (spMap σ)).obj A := Over.isoMk h.isoPullback h.isoPullback_hom_snd
  letI I : GrpObj (Over.mk s') := GrpObj.ofIso e.symm
  have : IsMonHom e.symm.hom := CategoryTheory.isMonHom_ofIso e.symm
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  have hP : IsGrpPullback (Over.mk s' : Over (Sp R')) A (spMap σ) φ :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A (spMap σ))).congr (Category.id_comp _)
      (by simp [e])
  exact ⟨I, hP, fun hA => GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hP,
    fun g hg => (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h hg⟩

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullbackStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left), IsPullback φ s' A.hom (spMap σ) → ∃ _ : GrpObj (Over.mk s' : Over (Sp R')), IsGrpPullback (Over.mk s' : Over (Sp R')) A (spMap σ) φ ∧ (IsAbelianScheme A → IsAbelianScheme (Over.mk s' : Over (Sp R'))) ∧ ∀ g, SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g s' := by
  first | exact @GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback | exact GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback | (intros; apply GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightEntriesSignsSizes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightEntriesSignsSizes
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop.Wts

variable {ι : Type} {N : ℕ} (W : Wts ι N)

theorem div_gap_step (h : W.Hyp) (hd : W.IsDiv) (τ : ι) (a b : Fin N) (hab : (b : ℕ) = a + 1) :
    0 ≤ W.u1 τ a - W.u1 τ b ∧
      ((W.T : ℤ) + W.Dd + 1) * (W.u1 τ a - W.u1 τ b) ≤ W.u τ a - W.u τ b + 2 := by
  have hM : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1 := by positivity
  have hc := h.weightConst_nonneg
  obtain ⟨h41, -, h43⟩ := h.h4 τ a b hab
  have h2 := h.h2.1
  rw [(hd τ).2 a b hab]
  have hN : (0 : ℤ) ≤ N := by positivity
  split_ifs with hb
  · have := h43 hb
    refine ⟨Int.ediv_nonneg (by linarith) hM.le, ?_⟩
    refine (Int.mul_ediv_self_le hM.ne').trans ?_
    linarith
  · have h5 := h41 hb
    have h6 : (0 : ℤ) ≤ ((W.T : ℤ) + W.Dd + 2) * ((W.T : ℤ) + W.Dd + 2 + 2 * N) := by positivity
    exact ⟨Int.ediv_nonneg (by linarith) hM.le, Int.mul_ediv_self_le hM.ne'⟩

theorem div_gap_sum (h : W.Hyp) (hd : W.IsDiv) (τ : ι) (n : ℕ) : ∀ a b : Fin N, (b : ℕ) = a + n →
    0 ≤ W.u1 τ a - W.u1 τ b ∧
      ((W.T : ℤ) + W.Dd + 1) * (W.u1 τ a - W.u1 τ b) ≤ W.u τ a - W.u τ b + 2 * n := by
  induction n with
  | zero =>
    intro a b hab
    have : b = a := Fin.ext (by simpa using hab)
    subst this
    simp
  | succ n ih =>
    intro a b hab
    have hlt : (a : ℕ) + n < N := by have := b.2; omega
    obtain ⟨h1, h2⟩ := ih a ⟨a + n, hlt⟩ rfl
    obtain ⟨h3, h4⟩ := W.div_gap_step h hd τ ⟨a + n, hlt⟩ b (by simp; omega)
    refine ⟨by linarith, ?_⟩
    push_cast
    nlinarith

end GlobalTheory.MeanTop.Wts

namespace GlobalTheory.MeanTop

theorem divided_entries : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ i,
    ((W.T : ℤ) + W.Dd + 1) * |W.u1 τ i| ≤ |W.u τ i| + W.c0 + 4 * N ∧
      (W.kc ≤ (i : ℕ) + 1 → W.u1 τ i ≤ 0) ∧ ((i : ℕ) < W.kc → 0 ≤ W.u1 τ i) := by
  intro ι _ N W h hd τ i
  have hk := h.kc_pos
  have hk2 := h.kc_lt
  have hp := h.p_lt
  have hc := h.weightConst_nonneg
  have hi := i.2
  have hN : (0 : ℤ) ≤ N := by positivity
  let a : Fin N := ⟨W.kc - 1, by omega⟩
  have ha : (a : ℕ) + 1 = W.kc := by simp only [a]; omega
  have hu : W.u τ a = 0 := h.anchor τ a ha
  have hu1 : W.u1 τ a = 0 := (hd τ).1 a ha
  have up : (i : ℕ) < W.kc → 0 ≤ W.u1 τ i ∧
      ((W.T : ℤ) + W.Dd + 1) * W.u1 τ i ≤ W.u τ i + 2 * N := by
    intro hi'
    obtain ⟨h1, h2⟩ := W.div_gap_sum h hd τ (a - i) i a (by omega)
    have h3 : (((a : ℕ) - i : ℕ) : ℤ) ≤ N := by omega
    rw [hu1, sub_zero] at h1 h2
    rw [hu] at h2
    exact ⟨h1, by linarith⟩
  have down : W.kc ≤ (i : ℕ) + 1 → W.u1 τ i ≤ 0 ∧
      ((W.T : ℤ) + W.Dd + 1) * (-W.u1 τ i) ≤ -W.u τ i + 2 * N := by
    intro hi'
    obtain ⟨h1, h2⟩ := W.div_gap_sum h hd τ (i - a) a i (by omega)
    have h3 : (((i : ℕ) - a : ℕ) : ℤ) ≤ N := by omega
    rw [hu1, zero_sub] at h1 h2
    rw [hu] at h2
    exact ⟨by linarith, by linarith⟩
  refine ⟨?_, fun hi' => (down hi').1, fun hi' => (up hi').1⟩
  by_cases hi' : (i : ℕ) < W.kc
  · obtain ⟨h1, h2⟩ := up hi'
    rw [abs_of_nonneg h1]
    have := le_abs_self (W.u τ i)
    linarith
  · obtain ⟨h1, h2⟩ := down (by omega)
    rw [abs_of_nonpos h1]
    have := neg_le_abs (W.u τ i)
    linarith

end GlobalTheory.MeanTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightEntriesSignsSizesStatement
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedWeight_entries_signs_sizes : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ i, ((W.T : ℤ) + W.Dd + 1) * |W.u1 τ i| ≤ |W.u τ i| + W.c0 + 4 * N ∧ (W.kc ≤ (i : ℕ) + 1 → W.u1 τ i ≤ 0) ∧ ((i : ℕ) < W.kc → 0 ≤ W.u1 τ i) := by
  first | exact @GlobalTheory.MeanTop.divided_entries | exact GlobalTheory.MeanTop.divided_entries | (intros; apply GlobalTheory.MeanTop.divided_entries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPadicValNatMulLogLeLog
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem sum_padicValNat_mul_log_le_log (n : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, (padicValNat p n : ℝ) * Real.log p ≤ Real.log n := by
  classical
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  have h1 : ∑ p ∈ S, (padicValNat p n : ℝ) * Real.log p
      = ∑ p ∈ S, (n.factorization p : ℝ) * Real.log p :=
    Finset.sum_congr rfl fun p hp => by rw [Nat.factorization_def n (hS p hp), Nat.padicValNat_def]
  rw [h1]
  have h2 : ∑ p ∈ S ∪ n.factorization.support, (n.factorization p : ℝ) * Real.log p
      = ∑ p ∈ n.factorization.support, (n.factorization p : ℝ) * Real.log p := by
    symm
    refine Finset.sum_subset Finset.subset_union_right fun p _ hp => ?_
    rw [Finsupp.notMem_support_iff.1 hp]; simp
  rw [← h2]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

theorem sum_vDiff_mul_log_le :
    ∀ (D : D7) (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (∀ p, 0 ≤ vDiff D p) ∧ ∑ p ∈ S, vDiff D p * Real.log p ≤ Real.log D.host.rdE := by
  intro D S hS
  refine ⟨fun p => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
  have hn : (0 : ℝ) < (Module.finrank ℚ D.host.E : ℝ) := by exact_mod_cast Module.finrank_pos
  have hd : (0 : ℝ) < |(discr D.host.E : ℝ)| := by
    rw [abs_pos]; exact_mod_cast discr_ne_zero D.host.E
  have hc : ((WeightThresholdDefs.dE D : ℕ) : ℝ) = |(discr D.host.E : ℝ)| := by
    rw [WeightThresholdDefs.dE, Nat.cast_natAbs, Int.cast_abs]
  have hr : Real.log D.host.rdE = Real.log (WeightThresholdDefs.dE D : ℕ) / (Module.finrank ℚ D.host.E : ℝ) := by
    rw [hc]
    unfold Host.rdE
    rw [Real.log_rpow hd]; ring
  rw [hr]
  refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right (sum_padicValNat_mul_log_le_log (WeightThresholdDefs.dE D) S hS) hn.le)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [vDiff]; ring

end GlobalTheory.MeanTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionWeierstrassPMemValuationSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionWeierstrassPMemValuationSubring
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.TorsMemVal

theorem mem_of_isIntegral (V : ValuationSubring ℂ) {x : ℂ} (hx : IsIntegral ℤ x) : x ∈ V := by
  have h : IsIntegral V x := hx.tower_top
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact y.2

theorem mem_of_val (V : ValuationSubring ℂ) {n u Ω x : ℂ} (k : ℕ) (hn : V.valuation n = 1)
    (hu : V.valuation u = V.valuation Ω) (h : n ^ k * x / Ω ^ k ∈ V) : x / u ^ k ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rw [map_div₀, map_mul, map_pow, map_pow, hn, one_pow, one_mul, ← hu] at h
  rwa [map_div₀, map_pow]

theorem main : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → ∀ z w, z ∉ L.lattice → w ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → (N : ℂ) * w ∈ L.lattice → L.derivWeierstrassP z / u ^ 3 ∈ V ∧ (L.weierstrassP z - L.weierstrassP w) / u ^ 2 ∈ V := by
  intro L β u V N hβ hβi hu hN z w hz hw hNz hNw
  obtain ⟨Ω, hΩ⟩ := IsAlgClosed.exists_pow_nat_eq (latticeCurve L).Δ (n := 12) (by norm_num)
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · simp at hN
    · exact h
  have huΩ : V.valuation u = V.valuation Ω := by
    rw [← hΩ, map_pow] at hu
    exact (pow_left_inj₀ zero_le' zero_le' (by norm_num)).1 hu
  have h := GlobalTheory.WpFam.LatTorsVal.main L β Ω N hβ hβi (hΩ.trans (latticeCurve_Δ L)) hN0
  exact ⟨mem_of_val V 3 hN huΩ (mem_of_isIntegral V (h.1 z hNz).2),
    mem_of_val V 2 hN huΩ (mem_of_isIntegral V (h.2 z w hz hw hNz hNw))⟩

end GlobalTheory.CMModel.TorsMemVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionWeierstrassPMemValuationSubringStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → ∀ z w, z ∉ L.lattice → w ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → (N : ℂ) * w ∈ L.lattice → L.derivWeierstrassP z / u ^ 3 ∈ V ∧ (L.weierstrassP z - L.weierstrassP w) / u ^ 2 ∈ V := by
  first | exact @GlobalTheory.CMModel.TorsMemVal.main | exact GlobalTheory.CMModel.TorsMemVal.main | (intros; apply GlobalTheory.CMModel.TorsMemVal.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresNeZero
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

noncomputable section

namespace GlobalTheory.CMModel.SqNe

theorem natMul_mem {p : ℕ} {F : IntermediateField ℚ ℂ} {L : PeriodPair} {t : ℂ} (h : Datum p F L t) :
    (p : ℂ) * t ∈ L.lattice := by
  have h1 := neg_mem (h.mul _ h.ker)
  rw [← mul_assoc, ← sq, sqrtNegNat_sq, neg_mul, neg_neg] at h1
  exact h1

theorem mul_notMem {p : ℕ} {F : IntermediateField ℚ ℂ} {L : PeriodPair} {t : ℂ} (h : Datum p F L t)
    {n : ℕ} (hn : Nat.Coprime n p) : (n : ℂ) * t ∉ L.lattice := fun hm => by
  have h1 := natMul_mem h
  obtain ⟨a, b, e⟩ := Nat.isCoprime_iff_coprime.2 hn
  have e' : (a : ℂ) * n + b * p = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) e
  have := add_mem (zsmul_mem hm a) (zsmul_mem h1 b)
  rw [zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← mul_assoc, ← add_mul, e', one_mul] at this
  exact h.notMem this

theorem coprime_sq {p : ℕ} (hp : p.Prime) (k : Sq p) : Nat.Coprime (k.1 : ℕ) p :=
  ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => k.2.1 ((ZMod.natCast_eq_zero_iff _ _).2 h)).symm

theorem sqPt_and_sqProd_ne_zero : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t →
      (∀ k : Sq p, sqPt p t k ∉ L.lattice ∧ (p : ℂ) * sqPt p t k ∈ L.lattice) ∧ sqProd p L t ≠ 0 := by
  intro p F L t hp h4 h3 h
  have h2 : p ≠ 2 := by omega
  refine ⟨fun k => ⟨mul_notMem h (coprime_sq hp k), ?_⟩, ?_⟩
  · have := zsmul_mem (natMul_mem h) (k.1 : ℕ)
    rw [zsmul_eq_mul] at this
    convert this using 1
    rw [sqPt]; push_cast; ring
  · refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    rw [Ne, GlobalTheory.derivWeierstrassP_eq_zero_iff L (show sqPt p t k ∉ L.lattice from mul_notMem h (coprime_sq hp k))]
    have := mul_notMem h (Nat.Coprime.mul_left ((Nat.coprime_primes Nat.prime_two hp).2 h2.symm)
      (coprime_sq hp k))
    intro hm
    apply this
    convert hm using 1
    rw [sqPt]; push_cast; ring

end GlobalTheory.CMModel.SqNe
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresNeZeroStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → (∀ k : Sq p, sqPt p t k ∉ L.lattice ∧ (p : ℂ) * sqPt p t k ∈ L.lattice) ∧ sqProd p L t ≠ 0 := by
  first | exact @GlobalTheory.CMModel.SqNe.sqPt_and_sqProd_ne_zero | exact GlobalTheory.CMModel.SqNe.sqPt_and_sqProd_ne_zero | (intros; apply GlobalTheory.CMModel.SqNe.sqPt_and_sqProd_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedBundleOfDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedBundleOfDescent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke

theorem left_comp_of_comp {S : Scheme.{0}} {X Y Z : Over S} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) :
    f.left ≫ g.left = h.left := by
  rw [← Over.comp_left, e]

theorem exists_birigidified_of_descent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsMonHom ψ → ∀ (m : ℕ) (P₀ : LB (G2 A').left), P₀.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P₀.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∃ P' : LB (G2 A').left, P'.IsLB ∧ (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) ∧ (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  intro p _ D R _ b M S s o A' _ _ ψ hψ m P₀ hP₀ H
  let φ : Fin 4 → ((G2 A').left ⟶ (G2 A').left) := ![𝟙 _, (lift (fst A' A') (1 : G2 A' ⟶ A')).left,
    (lift (1 : G2 A' ⟶ A') (snd A' A')).left, (lift (1 : G2 A' ⟶ A') (1 : G2 A' ⟶ A')).left]
  let ε : Fin 4 → ℤ := ![1, -1, -1, 1]
  have hε : ε 0 = 1 ∧ ε 1 = -1 ∧ ε 2 = -1 ∧ ε 3 = 1 := ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨LB.LinComb P₀ φ ε, DVR.linComb_isLB P₀ hP₀ φ ε, ?_, ?_, ?_⟩
  · refine GlobalTheory.PrimNorm.hasGen_nested hP₀ φ ε (fun _ : PUnit => _) (fun _ => 1) ?_
    have e0 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 0 = (lift (1 : A' ⟶ A') (𝟙 A')).left := Category.comp_id _
    have e1 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 1 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e2 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 2 = (lift (1 : A' ⟶ A') (𝟙 A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e3 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 3 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    rw [Fintype.prod_unique, zpow_one, Fin.prod_univ_four, e0, e1, e2, e3]
    rw [hε.1, hε.2.1, hε.2.2.1, hε.2.2.2, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one,
      mul_right_comm _ _ (GlobalTheory.PrimNorm.cls P₀ _)⁻¹, mul_inv_cancel, _root_.one_mul, inv_mul_cancel]
  · refine GlobalTheory.PrimNorm.hasGen_nested hP₀ φ ε (fun _ : PUnit => _) (fun _ => 1) ?_
    have e0 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 0 = (lift (𝟙 A') (1 : A' ⟶ A')).left := Category.comp_id _
    have e1 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 1 = (lift (𝟙 A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e2 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 2 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e3 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 3 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    rw [Fintype.prod_unique, zpow_one, Fin.prod_univ_four, e0, e1, e2, e3]
    rw [hε.1, hε.2.1, hε.2.2.1, hε.2.2.2, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one,
      mul_inv_cancel, _root_.one_mul, inv_mul_cancel]
  · haveI := hψ
    let ρ : Fin 4 → ((G2 o.A).left ⟶ (G2 o.A).left) := ![𝟙 _, (lift (fst o.A o.A) (1 : G2 o.A ⟶ o.A)).left,
      (lift (1 : G2 o.A ⟶ o.A) (snd o.A o.A)).left, (lift (1 : G2 o.A ⟶ o.A) (1 : G2 o.A ⟶ o.A)).left]
    have hsq : ∀ k, sq2 ψ ≫ φ k = ρ k ≫ sq2 ψ := by
      intro k
      fin_cases k
      · exact (Category.comp_id _).trans (Category.id_comp _).symm
      all_goals
        refine (left_comp_of_comp rfl).trans ((left_comp_of_comp ?_).symm)
        apply CartesianMonoidalCategory.hom_ext <;> simp
    have hP := o.isLB
    have cls1 : ∀ (r : (G2 o.A).left ⟶ (G2 o.A).left),
        GlobalTheory.MulPull.HasGen o.P (fun _ : PUnit => r) (fun _ => 1) → GlobalTheory.PrimNorm.cls o.P r = 1 := by
      intro r h
      have := (GlobalTheory.PrimNorm.hasGen_iff hP _ _).1 h
      rwa [Fintype.prod_unique, zpow_one] at this
    have h1 : GlobalTheory.PrimNorm.cls o.P (ρ 1) = 1 := by
      refine cls1 _ ?_
      have h := GlobalTheory.MulPull.HasGen.pull (φ := fun _ : PUnit => (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left)
        (ε := fun _ => 1) o.rig₂ (fst o.A o.A).left
      have e : (fst o.A o.A).left ≫ (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left = ρ 1 :=
        left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
      simpa only [e] using h
    have h2 : GlobalTheory.PrimNorm.cls o.P (ρ 2) = 1 := by
      refine cls1 _ ?_
      have h := GlobalTheory.MulPull.HasGen.pull (φ := fun _ : PUnit => (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left)
        (ε := fun _ => 1) o.rig₁ (snd o.A o.A).left
      have e : (snd o.A o.A).left ≫ (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left = ρ 2 :=
        left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
      simpa only [e] using h
    have h3 : GlobalTheory.PrimNorm.cls o.P (ρ 3) = 1 := by
      refine cls1 _ ?_
      have h := GlobalTheory.MulPull.HasGen.pull (φ := fun _ : PUnit => (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left)
        (ε := fun _ => 1) o.rig₂ (fst o.A o.A ≫ (1 : o.A ⟶ o.A)).left
      have e : (fst o.A o.A ≫ (1 : o.A ⟶ o.A)).left ≫ (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left = ρ 3 :=
        left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
      simpa only [e] using h
    have L1 : (lbPow o.P m).IsLB := DVR.linComb_isLB o.P hP _ _
    have L2 : (LB.LinComb (lbPow o.P m) ρ ε).IsLB := DVR.linComb_isLB _ L1 _ _
    have L3 : (LB.LinComb P₀ (fun k => ρ k ≫ sq2 ψ) ε).IsLB := DVR.linComb_isLB _ hP₀ _ _
    have L4 : ((LB.LinComb P₀ φ ε).pull (sq2 ψ)).IsLB := DVR.linComb_isLB _ (DVR.linComb_isLB _ hP₀ _ _) _ _
    have I1 : LBIso (lbPow o.P m) (LB.LinComb (lbPow o.P m) ρ ε) := by
      refine LBIso.symm (GlobalTheory.PrimNorm.lbIso_nested hP (fun _ : Fin m => 𝟙 _) (fun _ => 1) ρ ε
        (fun _ : Fin m => 𝟙 _) (fun _ => 1) ?_)
      simp only [Category.comp_id, zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Fin.prod_univ_four, h1, h2, h3, one_pow, one_zpow, _root_.mul_one, hε.1]
      rfl
    obtain ⟨w, hw⟩ := H
    have I2 : LBIso (LB.LinComb (lbPow o.P m) ρ ε) (LB.LinComb P₀ (fun k => ρ k ≫ sq2 ψ) ε) :=
      iso_linComb ((isGen_iff w).1 hw) ρ ε
    have I3 : LBIso (LB.LinComb P₀ (fun k => ρ k ≫ sq2 ψ) ε) ((LB.LinComb P₀ φ ε).pull (sq2 ψ)) := by
      refine LBIso.symm (GlobalTheory.PrimNorm.lbIso_nested hP₀ φ ε (fun _ : PUnit => sq2 ψ) (fun _ => 1)
        (fun k => ρ k ≫ sq2 ψ) ε ?_)
      rw [Fintype.prod_unique, zpow_one]
      exact Finset.prod_congr rfl fun k _ => by rw [hsq k]
    exact LBIso.trans L1 L2 L4 I1 (LBIso.trans L2 L3 L4 I2 I3)
end GlobalTheory.UPel.HT.Hecke
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedBundleOfDescentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_birigidified_bundle_of_descent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsMonHom ψ → ∀ (m : ℕ) (P₀ : LB (G2 A').left), P₀.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P₀.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∃ P' : LB (G2 A').left, P'.IsLB ∧ (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) ∧ (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_birigidified_of_descent) | (exact GlobalTheory.UPel.HT.Hecke.exists_birigidified_of_descent) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_birigidified_of_descent  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentsAdeleUnitCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentsAdeleUnitCombination
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSA.PickUnit

variable {F : Type} [Field F] [NumberField F]

def compInf (w : InfinitePlace F) : AF F →+* w.Completion :=
  (Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp (RingHom.fst _ _)

def compFin (v : HeightOneSpectrum (𝓞 F)) : AF F →+* v.adicCompletion F :=
  (RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v).comp
    (RingHom.snd _ _)

theorem ext_comp {a b : AF F} (h1 : ∀ w, compInf w a = compInf w b) (h2 : ∀ v, compFin v a = compFin v b) :
    a = b :=
  Prod.ext (funext h1) (Subtype.ext (funext h2))

theorem isUnit_of_comp {a : AF F} (h1 : ∀ w, compInf w a ≠ 0) (h2 : ∀ v, compFin v a ≠ 0)
    (h3 : ∀ᶠ v in Filter.cofinite, Valued.v (compFin v a) = 1) : IsUnit a :=
  Prod.isUnit_iff.2 ⟨Pi.isUnit_iff.2 fun w => isUnit_iff_ne_zero.2 (h1 w), FiniteAdeleRing.isUnit_iff.2 ⟨h2, h3⟩⟩

variable {ι : Type} [DecidableEq ι]

def ind (a : InfinitePlace F → ι) (b : HeightOneSpectrum (𝓞 F) → ι) (i : ι) : AF F :=
  ((fun w => if a w = i then 1 else 0),
    ⟨fun v => if b v = i then 1 else 0, Filter.Eventually.of_forall fun v => by
      by_cases h : b v = i
      · simp only [h, if_true]; exact one_mem _
      · simp only [h, if_false]; exact zero_mem _⟩)

theorem compInf_ind (a : InfinitePlace F → ι) (b : HeightOneSpectrum (𝓞 F) → ι) (i : ι) (w : InfinitePlace F) :
    compInf w (ind a b i) = if a w = i then 1 else 0 := rfl

theorem compFin_ind (a : InfinitePlace F → ι) (b : HeightOneSpectrum (𝓞 F) → ι) (i : ι)
    (v : HeightOneSpectrum (𝓞 F)) : compFin v (ind a b i) = if b v = i then 1 else 0 := rfl

end GlobalTheory.QSA.PickUnit


open GlobalTheory.QSA.PickUnit in
theorem GlobalTheory.QSA.exists_idem_pick_unit : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    (n u : ι → AF F), IsUnit (∑ i, u i * n i) → ∃ η : ι → AF F, (∀ i, η i * η i = η i) ∧
      (∀ i j, i ≠ j → η i * η j = 0) ∧ ∑ i, η i = 1 ∧ IsUnit (∑ i, η i * n i) := by
  intro F _ _ ι _ n u hs
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · rw [Finset.univ_eq_empty, Finset.sum_empty] at hs
    refine ⟨fun _ => 0, fun i => isEmptyElim i, fun i => isEmptyElim i, ?_, ?_⟩
    · rw [Finset.univ_eq_empty, Finset.sum_empty]; exact isUnit_zero_iff.1 hs
    · rw [Finset.univ_eq_empty, Finset.sum_empty]; exact hs
  have hinf : ∀ w, ∃ i, compInf w (n i) ≠ 0 := by
    intro w
    by_contra h
    push_neg at h
    apply (hs.map (compInf w)).ne_zero
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_mul, h i, mul_zero]
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∃ i, ∀ j, Valued.v (compFin v (n j)) ≤ Valued.v (compFin v (n i)) := by
    intro v
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => Valued.v (compFin v (n j)))
      ⟨i₀, Finset.mem_univ _⟩
    exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩
  choose a ha using hinf
  choose b hb using hfin
  refine ⟨ind a b, ?_, ?_, ?_, ?_⟩
  · intro i
    apply ext_comp
    · intro w; rw [map_mul, compInf_ind]; split_ifs <;> simp
    · intro v; rw [map_mul, compFin_ind]; split_ifs <;> simp
  · intro i j hij
    apply ext_comp
    · intro w; rw [map_mul, map_zero, compInf_ind, compInf_ind]
      by_cases h1 : a w = i
      · rw [if_pos h1, if_neg (fun h2 => hij (h1.symm.trans h2)), mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro v; rw [map_mul, map_zero, compFin_ind, compFin_ind]
      by_cases h1 : b v = i
      · rw [if_pos h1, if_neg (fun h2 => hij (h1.symm.trans h2)), mul_zero]
      · rw [if_neg h1, zero_mul]
  · apply ext_comp
    · intro w; rw [map_sum, map_one]; simp only [compInf_ind]; rw [Finset.sum_ite_eq]; simp
    · intro v; rw [map_sum, map_one]; simp only [compFin_ind]; rw [Finset.sum_ite_eq]; simp
  · have hcInf : ∀ w, compInf w (∑ i, ind a b i * n i) = compInf w (n (a w)) := by
      intro w
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single (a w)]
      · rw [map_mul, compInf_ind, if_pos rfl, one_mul]
      · intro j _ hj; rw [map_mul, compInf_ind, if_neg (Ne.symm hj), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hcFin : ∀ v, compFin v (∑ i, ind a b i * n i) = compFin v (n (b v)) := by
      intro v
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single (b v)]
      · rw [map_mul, compFin_ind, if_pos rfl, one_mul]
      · intro j _ hj; rw [map_mul, compFin_ind, if_neg (Ne.symm hj), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    apply isUnit_of_comp
    · intro w; rw [hcInf]; exact ha w
    · intro v h0
      rw [hcFin] at h0
      apply (hs.map (compFin v)).ne_zero
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      have h := hb v j
      rw [h0, map_zero] at h
      rw [map_mul, (Valuation.zero_iff _).1 (le_antisymm h zero_le'), mul_zero]
    · have hsu := (FiniteAdeleRing.isUnit_iff.1 (hs.map (RingHom.snd (InfiniteAdeleRing F) (Af F)))).2
      have hint : ∀ᶠ v in Filter.cofinite, ∀ j,
          Valued.v (compFin v (u j)) ≤ 1 ∧ Valued.v (compFin v (n j)) ≤ 1 := by
        refine Filter.eventually_all.2 fun j => ?_
        filter_upwards [(u j).2.2, (n j).2.2] with v h1 h2
        exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).1 h1,
          (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).1 h2⟩
      filter_upwards [hsu, hint] with v hv1 hv2
      rw [hcFin]
      refine le_antisymm (hv2 _).2 ?_
      have hv1' : Valued.v (compFin v (∑ i, u i * n i)) = 1 := hv1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hv1', map_sum]
      refine Valuation.map_sum_le _ fun j _ => ?_
      rw [map_mul, map_mul]
      exact (mul_le_of_le_one_left zero_le' (hv2 j).1).trans (hb v j)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentsAdeleUnitCombinationStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_idempotents_adele_unit_combination : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (n u : ι → AF F), IsUnit (∑ i, u i * n i) → ∃ η : ι → AF F, (∀ i, η i * η i = η i) ∧ (∀ i j, i ≠ j → η i * η j = 0) ∧ ∑ i, η i = 1 ∧ IsUnit (∑ i, η i * n i) := by
  first | exact @GlobalTheory.QSA.exists_idem_pick_unit | exact GlobalTheory.QSA.exists_idem_pick_unit | (intros; apply GlobalTheory.QSA.exists_idem_pick_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuousStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicForm_GL_continuous : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → Continuous φ.1 := by
  first | exact @GlobalTheory.CuspRep.IsAutForm.continuous | exact GlobalTheory.CuspRep.IsAutForm.continuous | (intros; apply GlobalTheory.CuspRep.IsAutForm.continuous <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntermediateFieldOfForallComplexAutFixedStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntermediateFieldOfForallComplexAutFixed
namespace GlobalTheory.CMModel

theorem mem_of_forall_ringEquiv_fixed :
    ∀ (F : IntermediateField ℚ ℂ) (x : ℂ),
      (∀ σ : ℂ ≃+* ℂ, (∀ y ∈ F, σ y = y) → σ x = x) → x ∈ F := fun F x hx ↦ by
  obtain ⟨y, rfl⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := F) x
    fun σ ↦ hx σ.toRingEquiv fun y hy ↦ σ.commutes ⟨y, hy⟩
  exact y.2

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed : ∀ (F : IntermediateField ℚ ℂ) (x : ℂ), (∀ σ : ℂ ≃+* ℂ, (∀ y ∈ F, σ y = y) → σ x = x) → x ∈ F := by
  first | exact @GlobalTheory.CMModel.mem_of_forall_ringEquiv_fixed | exact GlobalTheory.CMModel.mem_of_forall_ringEquiv_fixed | (intros; apply GlobalTheory.CMModel.mem_of_forall_ringEquiv_fixed <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJOfNonrealMultiplier
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJOfNonrealMultiplier
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.LatticeJInt

theorem main : ∀ (L : PeriodPair) (β : ℂ), MulStable L β → β.im ≠ 0 →
    _root_.IsIntegral ℤ (latticeCurve L).j := by
  intro L β hβ him
  obtain ⟨c, τ, hτ⟩ := ReciprocityTheory.ChartRestriction.L1.latTau L
  have hj := GlobalTheory.JInt.main L c τ β hτ hβ him
  rw [← ReciprocityTheory.ChartRestriction.L1.jInv_eq_jT hτ] at hj
  rw [latticeCurve_j_eq]
  exact hj

end GlobalTheory.CMModel.LatticeJInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJOfNonrealMultiplierStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_j_of_nonreal_multiplier : ∀ (L : PeriodPair) (β : ℂ), MulStable L β → β.im ≠ 0 → _root_.IsIntegral ℤ (latticeCurve L).j := by
  first | exact @GlobalTheory.CMModel.LatticeJInt.main | exact GlobalTheory.CMModel.LatticeJInt.main | (intros; apply GlobalTheory.CMModel.LatticeJInt.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationNatCastEqOneOfCoprimeStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationNatCastEqOneOfCoprime
namespace GlobalTheory.CMModel

theorem valuation_natCast_eq_one_of_coprime (V : ValuationSubring ℂ) (a b : ℕ)
    (h : Nat.Coprime a b) :
    V.valuation (a : ℂ) = 1 ∨ V.valuation (b : ℂ) = 1 := by
  have hint : ∀ z : ℤ, V.valuation (z : ℂ) ≤ 1 := fun z =>
    (V.valuation_le_one_iff _).2 (intCast_mem V z)
  have hnat : ∀ n : ℕ, V.valuation (n : ℂ) ≤ 1 := fun n =>
    (V.valuation_le_one_iff _).2 (natCast_mem V n)
  by_contra hcon
  rw [not_or] at hcon
  have ha : V.valuation (a : ℂ) < 1 := lt_of_le_of_ne (hnat a) hcon.1
  have hb : V.valuation (b : ℂ) < 1 := lt_of_le_of_ne (hnat b) hcon.2
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 h
  have hC : (x : ℂ) * (a : ℂ) + (y : ℂ) * (b : ℂ) = 1 := by exact_mod_cast hxy
  have h1 : V.valuation ((x : ℂ) * (a : ℂ)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint x)) ha
  have h2 : V.valuation ((y : ℂ) * (b : ℂ)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint y)) hb
  have h3 := V.valuation.map_add_lt h1 h2
  rw [hC, map_one] at h3
  exact lt_irrefl _ h3

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime : ∀ (V : ValuationSubring ℂ) (a b : ℕ), Nat.Coprime a b → V.valuation (a : ℂ) = 1 ∨ V.valuation (b : ℂ) = 1 := by
  first | exact @GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime | exact GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime | (intros; apply GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime <;> assumption)
end
