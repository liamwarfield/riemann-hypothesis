module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GradientAtPoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StImageDimLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ImageDimLe.Statement : Prop :=
  ∀ (n m : ℕ) (P : Ideal (MvPolynomial (Fin n) ℂ)) (Q : Fin m → MvPolynomial (Fin n) ℂ), P.IsPrime →
    ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ RingHom.ker ((Ideal.Quotient.mkₐ ℂ P).comp (aeval Q))) ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFibreDiscriminantHolomorphic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FibreDiscriminantHolomorphic.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ))
    (N : ℕ) (l : (σ → ℂ) →L[ℂ] ℂ),
    IsOpen D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    (∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x)) →
    IsGenericCountCover Y A D N →
    AnalyticOnNhd ℂ (fibreDiscr Y A l N) D

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalBoundedQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalBoundedQuotient.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (N : Set (σ → ℂ))
    (F G : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → IsOpen N → w ∈ N →
    DifferentiableOn ℂ F N → DifferentiableOn ℂ G N →
    ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → G z = 0) →
    Bornology.IsBounded ((fun z => F z / G z) '' ((zeroSetIn I ∩ N) \ {z | G z = 0})) →
    ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ ∃ H : (σ → ℂ) → ℂ, DifferentiableOn ℂ H V ∧
      ∀ z ∈ zeroSetIn I ∩ V, F z = G z * H z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalUniversalDenominator
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def LocalUniversalDenominator.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (w : σ → ℂ)
    (U : Set (σ → ℂ)) (f : (σ → ℂ) → ℂ),
    I.IsPrime → h ∉ I → w ∈ zeroSetIn I → U ∈ 𝓝 w →
    HolomorphicOnSubset f ((zeroSetIn I ∩ U) \ {z | eval z h = 0}) →
    Bornology.IsBounded (f '' ((zeroSetIn I ∩ U) \ {z | eval z h = 0})) →
    ∃ g : MvPolynomial σ ℂ, g ∉ I ∧ ∃ N : Set (σ → ℂ), IsOpen N ∧ w ∈ N ∧ N ⊆ U ∧
      ∃ F : (σ → ℂ) → ℂ, DifferentiableOn ℂ F N ∧
        ∀ z ∈ (zeroSetIn I ∩ N) \ {z | eval z h = 0}, eval z g * f z = F z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StWeaklyHolomorphicIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def WeaklyHolomorphicIntegral.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (N : Set (σ → ℂ))
    (G f : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → IsOpen N → w ∈ N →
    DifferentiableOn ℂ G N → ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → G z = 0) →
    HolomorphicOnSubset f ((zeroSetIn I ∩ N) \ {z | G z = 0}) →
    Bornology.IsBounded (f '' ((zeroSetIn I ∩ N) \ {z | G z = 0})) →
    ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ V ⊆ N ∧ ∃ (d : ℕ) (a : Fin d → (σ → ℂ) → ℂ),
      (∀ j, DifferentiableOn ℂ (a j) V) ∧
      ∀ z ∈ (zeroSetIn I ∩ V) \ {z | G z = 0}, f z ^ d + ∑ j, a j z * f z ^ (j : ℕ) = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalTrace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def LocalTrace.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (U : Set (σ → ℂ))
    (g : (σ → ℂ) → ℂ),
    I.IsPrime → w ∈ zeroSetIn I → U ∈ 𝓝 w → HolomorphicOnSubset g (zeroSetIn I ∩ U) →
    ∃ (k : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (B : Set (σ → ℂ)) (D : Set (Fin k → ℂ)) (m : ℕ)
      (T : (Fin k → ℂ) → ℂ),
      IsOpen B ∧ w ∈ B ∧ B ⊆ U ∧ IsOpen D ∧ A w ∈ D ∧
      (∀ z ∈ zeroSetIn I ∩ B, A z = A w → z = w) ∧ DifferentiableOn ℂ T D ∧
      ∀ y ∈ D, ∃ x : Fin m → σ → ℂ, (∀ j, x j ∈ zeroSetIn I ∩ B ∧ A (x j) = y) ∧
        (∀ z ∈ zeroSetIn I ∩ B, A z = y → z ∈ Set.range x) ∧ T y = ∑ j, g (x j)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDominantFibreBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def DominantFibreBound.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ),
    P.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = (d : ℕ) →
    Function.Injective ((Ideal.Quotient.mkₐ ℂ P).comp (aeval p)) →
    ∃ (e : ℕ) (Δ : MvPolynomial (Fin d) ℂ), Δ ≠ 0 ∧ ∀ w : Fin d → ℂ, eval w Δ ≠ 0 →
      {x | x ∈ zeroSet P ∧ ∀ i, eval x (p i) = w i}.encard ≤ e

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedFibreOpenPoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

def IsolatedFibreOpenPoly.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ),
    P.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = (d : ℕ) → x ∈ zeroSet P →
    (∃ W ∈ 𝓝 x, ∀ x' ∈ zeroSet P ∩ W, (∀ i, eval x' (p i) = eval x (p i)) → x' = x) →
    ∀ W' ∈ 𝓝 x, (fun x' : Fin n → ℂ => fun i => eval x' (p i)) '' (zeroSet P ∩ W') ∈
      𝓝 (fun i => eval x (p i))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StMaximalCountUnbranched
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def MaximalCountUnbranched.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ))
    (N : ℕ),
    IsOpen D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    (∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x)) →
    IsGenericCountCover Y A D N →
    ∀ x ∈ Y, {x' | x' ∈ Y ∧ A x' = A x}.encard = N →
      ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y ∈ O, A (h y) = y) ∧ Y ∩ V = h '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeScaling
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Pointwise

theorem eval_smul_of_isHomogeneous {n i : ℕ} {φ : MvPolynomial (Fin n) ℂ} (hφ : φ.IsHomogeneous i)
    (t : ℂ) (x : Fin n → ℂ) : eval (t • x) φ = t ^ i * eval x φ := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ j ∈ d.support, d j = i := by
    have h := hφ (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring


end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOpenProjectionDominantComponents
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def OpenProjectionDominantComponents.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∀ w ∈ X ∩ B,
    ∃ (n : ℕ) (Y : Fin n → Set (σ → ℂ)),
      (∀ i, IsAnalyticNear (Y i) w ∧ GermIrreducibleAt (Y i) w ∧
        ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y i → h (A z) = 0) →
          ∀ᶠ y in 𝓝 (A w), h y = 0) ∧
      (∀ i j, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j) ∧
      ∃ W ∈ 𝓝 w, X ∩ B ∩ W = (⋃ i, Y i) ∩ W

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedPointsCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

def isolatedFibrePts {n m : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (Q : Fin m → MvPolynomial (Fin n) ℂ)
    (z : Fin m → ℂ) : Set (Fin n → ℂ) :=
  {x | x ∈ zeroSet J ∧ (∀ i, eval x (Q i) = z i) ∧
    ∃ V ∈ 𝓝 x, ∀ x' ∈ zeroSet J ∩ V, (∀ i, eval x' (Q i) = z i) → x' = x}

def IsolatedPointsCount.Statement : Prop :=
  ∀ (n m : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (Q : Fin m → MvPolynomial (Fin n) ℂ),
    ∃ N : ℕ, ∀ z : Fin m → ℂ, (isolatedFibrePts J Q z).encard ≤ N

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionCluster
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Topology

noncomputable section

def FiniteProjectionCluster.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (w : Fin n → ℂ)
    (U : Set (Fin n → ℂ)),
    IsFiniteProjection J A → w ∈ zeroSet J → U ∈ 𝓝 w →
      ∃ (r : ℝ) (N M : Set (Fin n → ℂ)), 0 < r ∧ IsOpen N ∧ IsOpen M ∧ w ∈ N ∧ N ⊆ U ∧
        Disjoint N M ∧
        zeroSet J ∩ {x | A.mulVec x ∈ Metric.ball (A.mulVec w) r} ⊆ N ∪ M ∧
        Bornology.IsBounded (zeroSet J ∩ {x | A.mulVec x ∈ Metric.ball (A.mulVec w) r})

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermMinimalPolynomialDivides
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def GermMinimalPolynomialDivides.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
      ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        (∀ᶠ z in 𝓝 w, z ∈ X → g z ^ n + ∑ j, b j (A z) * g z ^ (j : ℕ) = 0) ∧
        ∀ E : Polynomial ((Fin d → ℂ) → ℂ), (∀ k, AnalyticAt ℂ (E.coeff k) (A w)) →
          (∀ᶠ z in 𝓝 w, z ∈ X → E.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (g z) = 0) →
          ∀ᶠ y in 𝓝 (A w),
            (Polynomial.X ^ n + ∑ j, Polynomial.C (b j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ) ∣
              E.map (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

namespace InjectiveHolomorphicOpen

theorem finrank_eq (k : ℕ) :
    Module.finrank ℝ (Fin k → ℂ) = Module.finrank ℝ (Fin (2 * k) → ℝ) := by
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]

theorem proof (hID : InvarianceOfDomain.Statement) : InjectiveHolomorphicOpen.Statement := by
  intro k U f hU hf hinj
  let e : (Fin k → ℂ) ≃L[ℝ] (Fin (2 * k) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (finrank_eq k)
  have hU' : IsOpen (e '' U) := e.toHomeomorph.isOpenMap U hU
  have hcont : ContinuousOn (fun y => e (f (e.symm y))) (e '' U) := by
    refine e.continuous.comp_continuousOn (hf.continuousOn.comp e.symm.continuous.continuousOn ?_)
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx
  have hinj' : Set.InjOn (fun y => e (f (e.symm y))) (e '' U) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ h
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h
    rw [hinj hx hx' (e.injective h)]
  have himage : (fun y => e (f (e.symm y))) '' (e '' U) = e '' (f '' U) := by
    rw [Set.image_image, Set.image_image]
    simp
  have hopen := hID (2 * k) (e '' U) (fun y => e (f (e.symm y))) hU' hcont hinj'
  rw [himage] at hopen
  have hpre : e ⁻¹' (e '' (f '' U)) = f '' U := Set.preimage_image_eq _ e.injective
  rw [← hpre]
  exact hopen.preimage e.continuous

end InjectiveHolomorphicOpen

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperOpenProjectionCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem subset_closure_nonvanishing_of_open {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ}
    (hDc : IsPreconnected D) (hmaps : Set.MapsTo A Y D)
    (hopen : ∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x))
    (hδ : AnalyticOnNhd ℂ δ D) (hne : ∃ y ∈ D, δ y ≠ 0) :
    Y ⊆ closure {x | x ∈ Y ∧ δ (A x) ≠ 0} := by
  obtain ⟨y₁, hy₁D, hy₁⟩ := hne
  intro x hx
  rw [mem_closure_iff_nhds]
  intro V hV
  by_contra hempty
  have hzero : δ =ᶠ[𝓝 (A x)] 0 := by
    filter_upwards [hopen x hx V hV] with y hy
    obtain ⟨x', ⟨hx'Y, hx'V⟩, rfl⟩ := hy
    by_contra h0
    exact hempty ⟨x', hx'V, hx'Y, h0⟩
  exact hy₁ (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc (hmaps hx) hzero hy₁D)

theorem ProperOpenProjectionCover.proof (hbranch : ProperOpenProjectionBranchLocus.Statement)
    (hcount : UnbranchedProperCountConstant.Statement) : ProperOpenProjectionCover.Statement := by
  intro σ _ X B k f d A D hB hf hXB hD hDc hDne hmaps hprop hopen
  obtain ⟨δ, hδ, hne, hsec⟩ := hbranch σ X B k f d A D hB hf hXB hD hDc hDne hmaps hprop hopen
  obtain ⟨N, hN⟩ := hcount σ (X ∩ B) d A D δ hD hDc hmaps hprop hδ (fun x hx hx0 => by
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hXV⟩ := hsec x hx hx0
    exact ⟨O, V, g, hO, hV, hxV, hg.continuousOn, hAg, hXV⟩)
  exact ⟨δ, N, hδ, hne, hN, hsec, subset_closure_nonvanishing_of_open hDc hmaps hopen hδ hne⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicIsolatedFibreOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric

theorem HolomorphicIsolatedFibreOpen.proof (hPS : ProperHolomorphicSurjective.Statement) :
    HolomorphicIsolatedFibreOpen.Statement := by
  intro k U g u hU hu hg ⟨W, hW, hiso⟩ V hV
  obtain ⟨r, hr, hrsub⟩ : ∃ r > 0, closedBall u r ⊆ U ∩ W ∩ V :=
    nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem (Filter.inter_mem (hU.mem_nhds hu) hW) hV)
  have hgc : ContinuousOn g (closedBall u r) := hg.continuousOn.mono fun x hx => (hrsub hx).1.1

  have hSc : IsCompact (g '' sphere u r) :=
    (isCompact_sphere u r).image_of_continuousOn (hgc.mono sphere_subset_closedBall)
  have hnot : g u ∉ g '' sphere u r := by
    rintro ⟨s, hs, hgs⟩
    have hsK := hrsub (sphere_subset_closedBall hs)
    have := hiso s hsK.1.2 hsK.1.1 hgs
    subst this
    rw [mem_sphere, dist_self] at hs
    exact hr.ne' hs.symm
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hSc.isClosed.isOpen_compl (g u) hnot

  have key : ∀ v ∈ closedBall u r, g v ∈ ball (g u) ε → v ∈ ball u r := by
    intro v hv hgv
    rcases (mem_closedBall.1 hv).lt_or_eq with h | h
    · exact h
    · exact (hεsub hgv ⟨v, mem_sphere.2 h, rfl⟩).elim
  have hΩ : IsOpen (ball u r ∩ g ⁻¹' ball (g u) ε) :=
    (hgc.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_ball
  have hproper : ∀ L ⊆ ball (g u) ε, IsCompact L →
      IsCompact ((ball u r ∩ g ⁻¹' ball (g u) ε) ∩ g ⁻¹' L) := by
    intro L hLD hL
    have heq : (ball u r ∩ g ⁻¹' ball (g u) ε) ∩ g ⁻¹' L = closedBall u r ∩ g ⁻¹' L := by
      ext v
      constructor
      · rintro ⟨⟨hv, _⟩, hvL⟩
        exact ⟨ball_subset_closedBall hv, hvL⟩
      · rintro ⟨hv, hvL⟩
        exact ⟨⟨key v hv (hLD hvL), hLD hvL⟩, hvL⟩
    rw [heq]
    exact (isCompact_closedBall u r).of_isClosed_subset
      (hgc.preimage_isClosed_of_isClosed isClosed_closedBall hL.isClosed) Set.inter_subset_left
  have hsurj := hPS k _ _ g hΩ ⟨u, by exact Set.mem_preimage.mpr (mem_ball_self hr), by exact Set.mem_preimage.mpr (mem_ball_self hε)⟩ isOpen_ball
    (convex_ball _ _).isPreconnected (hg.mono fun x hx => (hrsub (ball_subset_closedBall hx.1)).1.1)
    (fun x hx => hx.2) hproper
  refine Filter.mem_of_superset (ball_mem_nhds _ hε) ?_
  rw [← hsurj]
  exact Set.image_mono fun x hx => (hrsub (ball_subset_closedBall hx.1)).2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGeneralProjection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Matrix MvPolynomial

noncomputable section

def genericMatrix (d n : ℕ) : Matrix (Fin d) (Fin n) (MvPolynomial (Fin d × Fin n) ℂ) :=
  Matrix.of fun i k => X (i, k)

def detPoly {d n : ℕ} (M : Matrix (Fin n) (Fin d) ℂ) : MvPolynomial (Fin d × Fin n) ℂ :=
  Matrix.det (Matrix.of fun i j => ∑ k, genericMatrix d n i k * C (M k j))

theorem eval_detPoly {d n : ℕ} (M : Matrix (Fin n) (Fin d) ℂ) (x : Fin d × Fin n → ℂ) :
    eval x (detPoly M) = (Matrix.of (fun i k => x (i, k)) * M).det := by
  unfold detPoly
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j
  simp [genericMatrix, Matrix.mul_apply]

theorem GeneralProjection.proof : GeneralProjection.Statement := by
  intro n d m L hL
  classical
  set M : Fin m → Matrix (Fin n) (Fin d) ℂ := fun b => LinearMap.toMatrix' (L b) with hM
  have hne : ∀ b, detPoly (M b) ≠ 0 := by
    intro b h
    obtain ⟨g, hg⟩ := (L b).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (hL b))
    have h1 : LinearMap.toMatrix' g * M b = 1 := by
      rw [hM]; dsimp only
      rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
    have := congrArg (eval (fun p : Fin d × Fin n => LinearMap.toMatrix' g p.1 p.2)) h
    rw [eval_detPoly, map_zero] at this
    have h2 : Matrix.of (fun i k => LinearMap.toMatrix' g i k) = LinearMap.toMatrix' g := by
      ext i k; rfl
    rw [h2, h1, det_one] at this
    exact one_ne_zero this
  have hprod : (∏ b, detPoly (M b)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun b _ => hne b
  obtain ⟨x, hx⟩ : ∃ x : Fin d × Fin n → ℂ, eval x (∏ b, detPoly (M b)) ≠ 0 := by
    by_contra hcon
    refine hprod (MvPolynomial.funext fun x => ?_)
    rw [map_zero]
    by_contra hx
    exact hcon ⟨x, hx⟩
  refine ⟨Matrix.of fun i k => x (i, k), fun b v w hvw => ?_⟩
  rw [map_prod] at hx
  have hb : (Matrix.of (fun i k => x (i, k)) * M b).det ≠ 0 := by
    rw [← eval_detPoly]
    exact (Finset.prod_ne_zero_iff.mp hx) b (Finset.mem_univ b)
  have key : ∀ u, (Matrix.of fun i k => x (i, k)) *ᵥ L b u = (Matrix.of (fun i k => x (i, k)) * M b) *ᵥ u := by
    intro u
    rw [← Matrix.mulVec_mulVec, hM]
    dsimp only
    rw [LinearMap.toMatrix'_mulVec]
  simp only [key] at hvw
  have h0 : (Matrix.of (fun i k => x (i, k)) * M b) *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hb h0)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUnbranchedProperCountLocallyConstant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Set

theorem UnbranchedProperCountLocallyConstant.proof : UnbranchedProperCountLocallyConstant.Statement := by
  intro σ _ Y d A D δ hD _ hprop hchart y hyD hδy
  choose! O V g hO hV hxV hg hsec hYV using hchart

  have key : ∀ x ∈ Y, δ (A x) ≠ 0 → ∀ z ∈ Y, z ∈ V x → A z ∈ O x ∧ g x (A z) = z := by
    intro x hx hδ z hz hzV
    obtain ⟨w, hw, rfl⟩ : z ∈ g x '' O x := hYV x hx hδ ▸ ⟨hz, hzV⟩
    rw [hsec x hx hδ w hw]; exact ⟨hw, rfl⟩
  set F := {x | x ∈ Y ∧ A x = y} with hFdef
  have hFδ : ∀ x ∈ F, δ (A x) ≠ 0 := fun x hx => hx.2 ▸ hδy
  have hyO : ∀ x ∈ F, y ∈ O x := fun x hx => hx.2 ▸ (key x hx.1 (hFδ x hx) x hx.1 (hxV x hx.1 (hFδ x hx))).1
  have hgy : ∀ x ∈ F, g x y = x := fun x hx => hx.2 ▸ (key x hx.1 (hFδ x hx) x hx.1 (hxV x hx.1 (hFδ x hx))).2

  have hFc : IsCompact F := by
    simpa [hFdef] using hprop {y} (singleton_subset_iff.2 hyD) isCompact_singleton
  have hFfin : F.Finite := by
    obtain ⟨t, htF, hcov⟩ := hFc.elim_nhds_subcover V
      (fun x hx => (hV x hx.1 (hFδ x hx)).mem_nhds (hxV x hx.1 (hFδ x hx)))
    refine t.finite_toSet.subset fun z hz => ?_
    obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (hcov hz)
    have hx := htF x hxt
    have := (key x hx.1 (hFδ x hx) z hz.1 hzx).2
    rw [hz.2, hgy x hx] at this
    exact this ▸ hxt
  refine ⟨hFfin, ?_⟩

  have hev1 : ∀ᶠ y' in 𝓝 y, ∀ x ∈ F, y' ∈ O x :=
    (eventually_all_finite hFfin).2 fun x hx => (hO x hx.1 (hFδ x hx)).mem_nhds (hyO x hx)

  have hev2 : ∀ᶠ y' in 𝓝 y, ∀ p ∈ F ×ˢ F, p.1 ≠ p.2 → g p.1 y' ≠ g p.2 y' := by
    refine (eventually_all_finite (hFfin.prod hFfin)).2 fun p hp => ?_
    by_cases hne : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hne h
    have c1 := ((hg p.1 hp.1.1 (hFδ _ hp.1)).continuousAt ((hO _ hp.1.1 (hFδ _ hp.1)).mem_nhds (hyO _ hp.1)))
    have c2 := ((hg p.2 hp.2.1 (hFδ _ hp.2)).continuousAt ((hO _ hp.2.1 (hFδ _ hp.2)).mem_nhds (hyO _ hp.2)))
    have hne' : g p.1 y ≠ g p.2 y := by rwa [hgy _ hp.1, hgy _ hp.2]
    exact ((c1.tendsto.prodMk_nhds c2.tendsto).eventually
      (isClosed_diagonal.isOpen_compl.mem_nhds hne')).mono fun _ h _ => h

  have hev3 : ∀ᶠ y' in 𝓝 y, ∀ z ∈ Y, A z = y' → ∃ x ∈ F, z ∈ V x := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hD y hyD
    set K := Metric.closedBall y (ε / 2)
    have hKD : K ⊆ D := (Metric.closedBall_subset_ball (by linarith)).trans hball
    set W := ⋃ x ∈ F, V x
    have hW : IsOpen W := isOpen_biUnion fun x hx => hV x hx.1 (hFδ x hx)
    have hC : IsCompact ({z | z ∈ Y ∧ A z ∈ K} \ W) :=
      (hprop K hKD (isCompact_closedBall y _)).diff hW
    have hyn : y ∉ A '' ({z | z ∈ Y ∧ A z ∈ K} \ W) := by
      rintro ⟨z, ⟨⟨hzY, -⟩, hzW⟩, hzy⟩
      exact hzW (mem_iUnion₂.2 ⟨z, ⟨hzY, hzy⟩, hxV z hzY (hzy ▸ hδy)⟩)
    filter_upwards [Metric.closedBall_mem_nhds y (half_pos hε),
      (hC.image A.continuous).isClosed.isOpen_compl.mem_nhds hyn] with y' hy'K hy'C z hzY hzy
    by_contra hno
    exact hy'C ⟨z, ⟨⟨hzY, hzy ▸ hy'K⟩, fun h => hno (by simpa [W] using h)⟩, hzy⟩
  filter_upwards [hev1, hev2, hev3] with y' h1 h2 h3
  have himg : {x | x ∈ Y ∧ A x = y'} = (fun x => g x y') '' F := by
    ext z
    constructor
    · rintro ⟨hzY, hzy⟩
      obtain ⟨x, hx, hzx⟩ := h3 z hzY hzy
      exact ⟨x, hx, by simpa [hzy] using (key x hx.1 (hFδ x hx) z hzY hzx).2⟩
    · rintro ⟨x, hx, rfl⟩
      have hm : g x y' ∈ Y ∩ V x := hYV x hx.1 (hFδ x hx) ▸ mem_image_of_mem _ (h1 x hx)
      exact ⟨hm.1, hsec x hx.1 (hFδ x hx) y' (h1 x hx)⟩
  rw [himg]
  refine InjOn.encard_image fun a ha b hb hab => ?_
  by_contra hne
  exact h2 (a, b) ⟨ha, hb⟩ hne hab

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.IsClosedComplexSubmanifoldIn
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Pointwise

variable {n d : ℕ}

def linPoly (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (i : Fin d) : MvPolynomial (Fin n) ℂ :=
  ∑ j, C (A (Pi.single j 1) i) * X j

def projAlgHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ J :=
  aeval fun i => Ideal.Quotient.mk J (linPoly A i)

def IsFiniteProjection (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) : Prop :=
  Function.Injective (projAlgHom J A) ∧ (projAlgHom J A).toRingHom.Finite

def unitaryRows (d n : ℕ) : Set (Matrix (Fin d) (Fin n) ℂ) :=
  {M | M * M.conjTranspose = 1}

def GenericProjectionFinite.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    (∃ S : Set (MvPolynomial (Fin d × Fin n) ℂ),
        (∃ M : Matrix (Fin d) (Fin n) ℂ, ∃ f ∈ S, eval (fun p => M p.1 p.2) f ≠ 0) ∧
        ∀ M : Matrix (Fin d) (Fin n) ℂ,
          (∃ f ∈ S, eval (fun p => M p.1 p.2) f ≠ 0) → IsFiniteProjection J M.mulVecLin) ∧
      (∃ M : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J M.mulVecLin) ∧
      (∀ D ⊆ unitaryRows d n, unitaryRows d n ⊆ closure D →
        ∃ M ∈ D, IsFiniteProjection J M.mulVecLin) ∧
      (∀ (m : ℕ) (F : Fin m → Matrix (Fin n) (Fin n) ℂ),
        (∀ k, F k ∈ Matrix.unitaryGroup (Fin n) ℂ) →
        ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (k : Fin m) (s : Fin d ↪ Fin n),
          IsFiniteProjection J (((U * F k).conjTranspose.submatrix s id).mulVecLin))

def lineMap : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  aeval ![X 0, 0]

def lineIdeal : Ideal (MvPolynomial (Fin 2) ℂ) := RingHom.ker lineMap

theorem lineMap_surjective : Function.Surjective lineMap := by
  intro p
  refine ⟨rename (fun _ : Fin 1 => (0 : Fin 2)) p, ?_⟩
  have h : ((![X 0, 0] : Fin 2 → MvPolynomial (Fin 1) ℂ) ∘ fun _ : Fin 1 => (0 : Fin 2)) = X := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    rfl
  simp only [lineMap, aeval_rename, h, aeval_X_left_apply]

def lineEquiv : (MvPolynomial (Fin 2) ℂ ⧸ lineIdeal) ≃ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  Ideal.quotientKerAlgEquivOfSurjective lineMap_surjective

theorem lineIdeal_dim : ringKrullDim (MvPolynomial (Fin 2) ℂ ⧸ lineIdeal) = (1 : ℕ) := by
  rw [ringKrullDim_eq_of_ringEquiv lineEquiv.toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

def lineProj : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) := LinearMap.pi fun _ => LinearMap.proj 0

theorem lineEquiv_projAlgHom (p : MvPolynomial (Fin 1) ℂ) :
    lineEquiv (projAlgHom lineIdeal lineProj p) = p := by
  have h : (lineEquiv.toAlgHom.comp (projAlgHom lineIdeal lineProj)) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [Fin.fin_one_eq_zero i]
    simp [projAlgHom, lineEquiv, linPoly, lineProj, lineMap, Fin.sum_univ_two]
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk lineMap_surjective (X 0)).trans
      (by simp [lineMap])
  exact congrArg (fun f => f p) h

theorem lineProj_finite : IsFiniteProjection lineIdeal lineProj := by
  have hinj : Function.Injective (projAlgHom lineIdeal lineProj) :=
    Function.LeftInverse.injective lineEquiv_projAlgHom
  have hsurj : Function.Surjective (projAlgHom lineIdeal lineProj) := by
    intro q
    refine ⟨lineEquiv q, lineEquiv.injective ?_⟩
    rw [lineEquiv_projAlgHom]
  exact ⟨hinj, RingHom.Finite.of_surjective _ hsurj⟩

def originIdeal (n : ℕ) : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval (0 : Fin n → ℂ))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.NormalModelGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem NormalModel.exists_clear_denominators {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : NormalModel J) (a b : Fin M.m → MvPolynomial (Fin n) ℂ)
    (hab : ∀ i, rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i) ∈ M.ideal)
    (x : Fin n → ℂ) (hb : ∀ i, eval x (b i) ≠ 0) (q : MvPolynomial (Fin n ⊕ Fin M.m) ℂ) :
    ∃ (N : ℕ) (r : MvPolynomial (Fin n) ℂ),
      rename Sum.inl ((∏ i, b i) ^ N) * q - rename Sum.inl r ∈ M.ideal ∧
        eval x r = eval x (∏ i, b i) ^ N *
          eval (Sum.elim x fun i => eval x (a i) / eval x (b i)) q := by
  set B : MvPolynomial (Fin n) ℂ := ∏ i, b i with hB
  set w : Fin n ⊕ Fin M.m → ℂ := Sum.elim x fun i => eval x (a i) / eval x (b i) with hw
  induction q using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0, C c, ?_, ?_⟩
    · simp
    · simp
  | add p q hp hq =>
    obtain ⟨N₁, r₁, h₁, e₁⟩ := hp
    obtain ⟨N₂, r₂, h₂, e₂⟩ := hq
    refine ⟨N₁ + N₂, B ^ N₂ * r₁ + B ^ N₁ * r₂, ?_, ?_⟩
    · have hid : rename Sum.inl (B ^ (N₁ + N₂)) * (p + q) - rename Sum.inl (B ^ N₂ * r₁ + B ^ N₁ * r₂) =
          rename Sum.inl (B ^ N₂) * (rename Sum.inl (B ^ N₁) * p - rename Sum.inl r₁) +
            rename Sum.inl (B ^ N₁) * (rename Sum.inl (B ^ N₂) * q - rename Sum.inl r₂) := by
        simp only [map_mul, map_add (f := _), map_pow]
        ring
      rw [hid]
      exact M.ideal.add_mem (M.ideal.mul_mem_left _ h₁) (M.ideal.mul_mem_left _ h₂)
    · rw [eval_add, eval_add, eval_mul, eval_mul, e₁, e₂, eval_pow, eval_pow]
      ring
  | mul_X p s hp =>
    obtain ⟨N, r, h, e⟩ := hp
    rcases s with j | i
    · refine ⟨N, r * X j, ?_, ?_⟩
      · have hid : rename Sum.inl (B ^ N) * (p * X (Sum.inl j)) - rename Sum.inl (r * X j) =
            X (Sum.inl j) * (rename Sum.inl (B ^ N) * p - rename Sum.inl r) := by
          simp only [map_mul, rename_X]
          ring
        rw [hid]
        exact M.ideal.mul_mem_left _ h
      · rw [eval_mul, eval_mul, e, eval_X, eval_X]
        simp only [hw, Sum.elim_inl]
        ring
    · set Cᵢ : MvPolynomial (Fin n) ℂ := ∏ j ∈ Finset.univ.erase i, b j with hC
      have hBC : B = b i * Cᵢ := (Finset.mul_prod_erase Finset.univ b (Finset.mem_univ i)).symm
      refine ⟨N + 1, r * a i * Cᵢ, ?_, ?_⟩
      · have hid : rename Sum.inl (B ^ (N + 1)) * (p * X (Sum.inr i)) - rename Sum.inl (r * a i * Cᵢ) =
            rename Sum.inl Cᵢ * (rename Sum.inl (b i) * X (Sum.inr i)) *
                (rename Sum.inl (B ^ N) * p - rename Sum.inl r) +
              rename Sum.inl Cᵢ * rename Sum.inl r *
                (rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i)) := by
          rw [pow_succ, hBC]
          simp only [map_mul, map_pow]
          ring
        rw [hid]
        exact M.ideal.add_mem (M.ideal.mul_mem_left _ h) (M.ideal.mul_mem_left _ (hab i))
      · rw [eval_mul, eval_mul, eval_mul, eval_X, pow_succ, hBC]
        have e' : eval x r = eval x (b i * Cᵢ) ^ N * eval w p := by rw [← hBC]; exact e
        rw [e']
        simp only [hw, Sum.elim_inr, eval_mul]
        field_simp [hb i]

theorem NormalModel.graph_mem_zeroSetIn {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : NormalModel J) (a b : Fin M.m → MvPolynomial (Fin n) ℂ)
    (hab : ∀ i, rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i) ∈ M.ideal)
    (x : Fin n → ℂ) (hx : x ∈ zeroSetIn J) (hb : ∀ i, eval x (b i) ≠ 0) :
    (Sum.elim x fun i => eval x (a i) / eval x (b i)) ∈ zeroSetIn M.ideal := by
  intro q hq
  obtain ⟨N, r, h, e⟩ := M.exists_clear_denominators a b hab x hb q
  have hr : rename Sum.inl r ∈ M.ideal := by
    have := M.ideal.sub_mem (M.ideal.mul_mem_left (rename Sum.inl ((∏ i, b i) ^ N)) hq) h
    simpa using this
  have hrJ : r ∈ J := by
    rw [← M.comap_eq]
    exact hr
  have hBx : eval x (∏ i, b i) ^ N ≠ 0 := by
    rw [map_prod]
    exact pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun i _ => hb i)
  have h0 : eval x (∏ i, b i) ^ N * eval (Sum.elim x fun i => eval x (a i) / eval x (b i)) q = 0 := by
    rw [← e]
    exact hx r hrJ
  exact (mul_eq_zero.1 h0).resolve_left hBx

theorem NormalModel.eq_graph_of_mem_zeroSetIn {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : NormalModel J) (a b : Fin M.m → MvPolynomial (Fin n) ℂ)
    (hab : ∀ i, rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i) ∈ M.ideal)
    (w : Fin n ⊕ Fin M.m → ℂ) (hw : w ∈ zeroSetIn M.ideal) (hb : ∀ i, eval (firstCoords w) (b i) ≠ 0) :
    w = Sum.elim (firstCoords w) fun i => eval (firstCoords w) (a i) / eval (firstCoords w) (b i) := by
  funext s
  rcases s with j | i
  · rfl
  · have h := hw _ (hab i)
    simp only [map_sub, map_mul, eval_rename, eval_X] at h
    simp only [Sum.elim_inr]
    rw [eq_div_iff (hb i)]
    have hc : (w ∘ Sum.inl) = firstCoords w := rfl
    rw [hc] at h
    linear_combination h

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolyKaehlerFree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open KaehlerDifferential TensorProduct

theorem PolyKaehlerFree.proof : PolyKaehlerFree.Statement := by
  intro R k _ _ _ n
  set B := MvPolynomial (Fin n) k

  have hinj : Function.Injective (mapBaseChange R k B) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R k B x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  have hex := exact_mapBaseChange_map R k B

  obtain ⟨l, hl⟩ := Module.projective_lifting_property ((map R k B B).restrictScalars B)
    LinearMap.id (map_surjective R k B)
  let e := ((hex.splitSurjectiveEquiv hinj) ⟨l, hl⟩).1
  have : Module.Free B Ω[B⁄k] := Module.Free.of_basis (mvPolynomialBasis k (Fin n))
  exact Module.Free.of_equiv e.symm
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFlatDimFormula
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem FlatDimFormula.proof : FlatDimFormula.Statement := by
  intro A B _ _ _ _ _ hA hB hloc hflat
  set I : Ideal B := (maximalIdeal A).map (algebraMap A B) with hI

  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩

  have hIle : I ≤ maximalIdeal B := IsLocalRing.map_maximalIdeal_le (algebraMap A B)
  have : Nontrivial (B ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hIle)
  have : IsLocalRing (B ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal B).map (Ideal.Quotient.mk I) = maximalIdeal (B ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have key := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal A) (maximalIdeal B)
  rw [← hI, hmap] at key
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B),
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A),
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B ⧸ I), key, WithBot.coe_add]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
