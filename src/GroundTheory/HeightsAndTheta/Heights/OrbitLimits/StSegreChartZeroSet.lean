module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartZeroSet
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal PBlk)
open ComplexSets

def SegreChartZeroSet.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsMultiHomogIdeal P → zeroSet (segreChartIdeal P σ i) = segreChartSet P σ i

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsGenericCount
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet PBlk)

def PtsGenericCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      ∃ d : ℕ, (∀ y, (ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y).encard ≤ d) ∧
        volume {y : Fin e → ℂ | ¬ ((ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y).encard = d ∧
          ∀ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, ∃ γ, IsSheet P Ψ y w γ)} = 0

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisor
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsSectionOn ptsIntegral pot segre divSupp IsHorizontal
  multAt PBlk oneLine fsLine Xc)
open GroundTheory.Heights₂.Heights (varInt localMult IsDegZeroSmooth segreChartSet segreChartComponents chartLift planeBump)

def ChartDivisorCompare.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (n m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) (g : ((Σ k, ι k) → ℂ) → ℝ) (δ : ℝ)
    (G : (Fin m → ℂ) → ℝ) (Φ : Fin n → (Fin m → ℂ) → ℝ),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSectionOn P A s →
    IsDegZeroSmooth g → 0 < δ → (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0) →
    (∀ x ∈ segreChartSet P σ i,
      G =ᶠ[𝓝 x] g ∘ chartLift σ i ∧ ∀ j, Φ j =ᶠ[𝓝 x] pot L j ∘ chartLift σ i) →
      ∑ J ∈ segreChartComponents P σ i,
          ∑ᶠ (W : Ideal (MvPolynomial (Fin m) ℂ))
            (_ : W ∈ (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes),
            (localMult (J ⊔ Ideal.span {chartSection σ i s}) W : ℝ) * varInt W n G Φ =
        ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
          (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) g

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsIntegrable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem abs_finsum_mem_le_finsum_mem_abs {α : Type*} (S : Set α) (f : α → ℝ) :
    |∑ᶠ w ∈ S, f w| ≤ ∑ᶠ w ∈ S, |f w| := by
  rw [finsum_mem_def, finsum_mem_def]
  have hind : S.indicator (fun w => |f w|) = fun w => |S.indicator f w| := by
    funext w
    by_cases hw : w ∈ S <;> simp [hw]
  rw [hind]
  have hsupp : Function.support (fun w => |S.indicator f w|) = Function.support (S.indicator f) := by
    ext w
    simp
  by_cases hfin : (Function.support (S.indicator f)).Finite
  · have hfin' : (Function.support (fun w => |S.indicator f w|)).Finite := hsupp ▸ hfin
    rw [finsum_eq_sum _ hfin, finsum_eq_sum _ hfin']
    have hs : hfin'.toFinset = hfin.toFinset := by
      ext w
      simp only [Set.Finite.mem_toFinset, hsupp]
    rw [hs]
    exact Finset.abs_sum_le_sum_abs _ _
  · have hinf' : ¬ (Function.support (fun w => |S.indicator f w|)).Finite := hsupp ▸ hfin
    rw [finsum_of_infinite_support hfin, finsum_of_infinite_support hinf', abs_zero]

theorem PtsIntegrable.of_found (hAbs : Inter.PtsAbsIntegrable.Statement)
    (hMeas : PtsSumMeasurable.Statement) : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  refine (hAbs K ι P e Ψ L A s hP hΨ hL hA hs).mono' (hMeas K ι P e Ψ L A s hP hΨ hL hA hs) ?_
  exact Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]
    exact abs_finsum_mem_le_finsum_mem_abs _ _

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartProjFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj PBlk)
open ComplexSets

def SegreChartProjFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ w, Ψ w 0 = w i) →
      ∀ J ∈ segreChartComponents P σ i, IsFiniteProjection J (chartProjMatrix σ Ψ)

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartAbsIntegrable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar PBlk oneLine isSmoothHerm_oneLine)
open ComplexSets

def SegreChartAbsIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth g →
      ∀ J ∈ segreChartComponents P σ i, ∀ A : Matrix (Fin e) (Fin m) ℂ, IsFiniteProjection J A →
        Integrable (chartAbsDens J A (chartWeight σ i g) (chartPot σ i L))

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisorComponents
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn divSupp IsHorizontal PBlk fsLine Xc)
open GroundTheory.Heights₂.Heights (segreChartComponents)

def ChartDivisorComponents.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → IsSectionOn P A s →
      (∀ J ∈ segreChartComponents P σ i, ∀ W' : Ideal (MvPolynomial (Fin m) ℂ),
        W' ∈ (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes ↔
          J ≤ W' ∧ ∃ W, (W ∈ divSupp P s ∧ IsHorizontal W) ∧ W' ∈ segreChartComponents W σ i) ∧
      ∀ W₁ W₂, W₁ ∈ divSupp P s ∧ IsHorizontal W₁ → W₂ ∈ divSupp P s ∧ IsHorizontal W₂ →
        ∀ W' ∈ segreChartComponents W₁ σ i, W' ∈ segreChartComponents W₂ σ i → W₁ = W₂

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsSegreChartFibreSum
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj sheetDensity pot PBlk oneLine
  isSmoothHerm_oneLine)
open ComplexSets

def PtsSegreChartFibreSum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth g →
    IsGoodProj P Ψ → (∀ w, Ψ w 0 = w i) →
      ∀ᵐ y, ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, sheetDensity P Ψ (pot L) g y w =
        ∑ J ∈ segreChartComponents P σ i,
          chartDens J (chartProjMatrix σ Ψ) (chartWeight σ i g) (chartPot σ i L) y

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartConeComponent
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiProjPrime PBlk)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartComponents)

variable {K : Type*} [DecidableEq K] {ι : K → Type*}

def chartSubst {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
  bind₁ (fun p : Σ k, ι k => (X (σ.symm (Function.update i p.1 p.2)) : MvPolynomial (Fin m) ℂ))

theorem chartSubst_X {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (p : Σ k, ι k) :
    chartSubst σ i (X p) = X (σ.symm (Function.update i p.1 p.2)) := by
  simp [chartSubst]

theorem chartSection_eq_chartSubst [Fintype K] [∀ k, Fintype (ι k)] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) (s : MRing ι) :
    chartSection σ i s = chartSubst σ i (map (Int.castRingHom ℂ) s) := rfl

def ChartConeComponent.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) (m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsMultiProjPrime W → ∀ W' ∈ segreChartComponents W σ i,
      ∃ W'' ∈ (W.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
        W''.map (chartSubst σ i : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin m) ℂ) ≤ W'

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartIntegral
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj IsSheet ptsIntegral
  ptsIntegralAt sheetDensity fibre maDensity mixedDisc cxHessian pot segre mcPts goodProjExists)

theorem maDensity_eq_zero_of_eventuallyEq_zero {D : ℕ} (φ : Fin (D + 1) → (Fin (D + 1) → ℂ) → ℝ)
    (y : Fin (D + 1) → ℂ) (h : φ 0 =ᶠ[𝓝 y] 0) : maDensity φ y = 0 := by
  have hH : fderiv ℝ (fderiv ℝ (φ 0)) y = 0 := by
    rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq]
    simp
  have hC : cxHessian (φ 0) y = 0 := by
    ext a b
    simp [cxHessian, hH]
  have hU : (fun k => cxHessian (φ k) y) =
      Function.update (fun k => cxHessian (φ k) y) 0 ((0 : ℂ) • (0 : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)) := by
    funext k
    by_cases hk : k = 0
    · subst hk
      simp [hC]
    · simp [Function.update_of_ne hk]
  have hM : mixedDisc (fun k => cxHessian (φ k) y) = 0 := by
    have hdef : mixedDisc (fun k => cxHessian (φ k) y) = ReciprocityTheory.AnForm.mdisc (fun k => cxHessian (φ k) y) :=
      rfl
    rw [hdef, hU, ReciprocityTheory.AnForm.A.mdisc_update_smul, zero_mul]
  simp [maDensity, hM]

theorem SegreChartIntegral.proof (hGood : SegreCoordGoodProj.Statement)
    (hIndep : PtsIntegralProjIndep.Statement) (hChart : PtsIntegralSegreChartProj.Statement) :
    SegreChartIntegral.Statement := by
  classical
  intro K _ _ ι _ P e m σ i L g δ G Φ hP hL hg hδ hsupp hgerm
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ), IsGoodProj P Ψ :=
    goodProjExists K ι P (e + 1) hP
  have hpts : ptsIntegral P (pot L) g = ptsIntegralAt P hex.choose (pot L) g := by
    unfold ptsIntegral
    rw [dite_eq_left hex]
  rw [hpts]
  by_cases hne : ∃ z ∈ mcPts P, segre z i ≠ 0
  · obtain ⟨Ψ, hΨ, hΨ0⟩ := hGood K ι P (e + 1) i hP hne
    rw [hIndep K ι P (e + 1) _ Ψ L g hP hex.choose_spec hΨ hL hg]
    exact hChart K ι P e m σ i L g Ψ G Φ hP hL hg hΨ hΨ0 hgerm
  · push Not at hne

    have hset : segreChartSet P σ i = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨z, hz, hzi, -⟩
      rw [hne z hz] at hzi
      exact zero_ne_one hzi
    have hcomp : segreChartComponents P σ i = ∅ := by
      ext J
      simp only [mem_segreChartComponents, Finset.notMem_empty, iff_false]
      intro hJ
      have htop : segreChartIdeal P σ i = ⊤ := by
        rw [segreChartIdeal, hset]
        exact MvPolynomial.vanishingIdeal_empty
      rw [htop] at hJ
      exact hJ.1.1.ne_top (top_le_iff.1 hJ.1.2)
    rw [hcomp, Finset.sum_empty]

    have hin : ∀ z ∈ mcPts P, ‖segre z i‖ < δ * ‖segre z‖ := by
      intro z hz
      rw [hne z hz, norm_zero]
      choose j hj using hz.1
      have hj' : segre z j ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hj k
      exact mul_pos hδ (norm_pos_iff.2 fun h0 => hj' (congrFun h0 j))
    have hterm : ∀ y w, sheetDensity P hex.choose (pot L) g y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · have hs : IsSheet P hex.choose y w hγ.choose := hγ.choose_spec
        rcases hsupp with hg0 | hp0
        · rw [hg0 _ (hin _ hs.2.self_of_nhds.2.1), zero_mul]
        · rw [maDensity_eq_zero_of_eventuallyEq_zero _ _ ?_, mul_zero]
          filter_upwards [hs.2] with y' hy'
          exact hp0 _ (hin _ hy'.2.1)
      · rfl
    unfold ptsIntegralAt
    simp [hterm]

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFibreDegreeSum
section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsDegreeFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def FibreDegreeSum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e : ℕ) (a : Fin e → K → ℤ) (p : ℕ),
    IsArithVar P (e + 1) → p.Prime →
      NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) a =
        ∑ᶠ V ∈ divSupp P (C (p : ℤ)), (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℤ) * geoNum e V a

end GroundTheory.Heights₂.Heights.Targets
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

section Generic

open NumbersDVR

theorem FibreDegreeSum.intNum_eq_cycEval (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (e : ℕ) (a : Fin e → K → ℤ) (p : ℕ)
    [Fact p.Prime] (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1)) :
    intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) a =
      NumbersDVR.cycEval (fun W ↦ intNum (ZMod p) (W.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) a)
        (NumbersDVR.divCycle P (C (p : ℤ))) := by
  classical
  have hp : p.Prime := Fact.out
  have hPprime : P.IsPrime := hP.2.1.1
  have hhor : ∀ r : ℤ, (C r : MRing ι ℤ) ∈ P → r = 0 := by
    intro r hr
    have hr' : r ∈ P.comap (C : ℤ →+* MRing ι ℤ) := hr
    rw [show P.comap (C : ℤ →+* MRing ι ℤ) = ⊥ from hP.2.2.1] at hr'
    exact (Ideal.mem_bot).mp hr'
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set 𝔭 : Ideal ℤ := Ideal.span {(p : ℤ)} with h𝔭def
  have h𝔭max : 𝔭.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have h𝔭 : 𝔭.IsPrime := h𝔭max.isPrime
  have h𝔭0 : 𝔭 ≠ ⊥ := by
    rw [h𝔭def, Ne, Ideal.span_singleton_eq_bot]
    exact hpZ.ne_zero
  let O := Localization.AtPrime 𝔭
  have : IsDiscreteValuationRing O :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ h𝔭0 O
  let ϖ : O := (p : O)
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 O]
    change Ideal.map (algebraMap ℤ O) (Ideal.span {(p : ℤ)}) = _
    rw [Ideal.map_span, Set.image_singleton]
    simp [ϖ]
  have hϖ : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hmax
  let M : Submonoid (MRing ι ℤ) := 𝔭.primeCompl.map (C (σ := Σ k, ι k))
  let φ := algebraMap (MRing ι ℤ) (MRing ι O)
  let P' : Ideal (MRing ι O) := P.map φ

  have hPdisj : Disjoint (M : Set (MRing ι ℤ)) P := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrP
    have h0 := hhor r hrP
    rw [h0] at hr
    exact hr 𝔭.zero_mem
  have hP'prime : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M (MRing ι O) P hPprime hPdisj
  have hP'comap : P'.comap φ = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (MRing ι O) hPprime hPdisj
  have hmp : IsMultiProjPrime P' :=
    { isPrime := hP'prime
      multiHomog := WeightedDegree.isMultiHomogIdeal_map (M₀ := 𝔭.primeCompl)
        ((Bridge.isMultiHomogIdeal_iff P).mpr hP.2.1.2.1)
      relevant := fun k ↦ by
        obtain ⟨i, hi⟩ := hP.2.1.2.2 k
        refine ⟨i, fun h ↦ hi ?_⟩
        have h' : φ (X ⟨k, i⟩) ∈ P' := by
          rw [show φ (X ⟨k, i⟩) = X ⟨k, i⟩ from map_X _ _]
          exact h
        have h'' : (X ⟨k, i⟩ : MRing ι ℤ) ∈ P'.comap φ := h'
        rw [hP'comap] at h''
        exact h'' }
  have hnt : P'.comap (C : O →+* MRing ι O) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Ideal.mem_comap] at hx
    rw [Ideal.mem_bot]
    obtain ⟨⟨m, s⟩, hms⟩ := IsLocalization.surj 𝔭.primeCompl x
    simp only at hms
    have hmem : φ (C m) ∈ P' := by
      rw [show φ (C m) = C (algebraMap ℤ O m) from map_C _ _, ← hms, map_mul]
      exact P'.mul_mem_right _ hx
    have hmem' : (C m : MRing ι ℤ) ∈ P'.comap φ := hmem
    rw [hP'comap] at hmem'
    have hm0 : m = 0 := hhor m hmem'
    rw [hm0, map_zero] at hms
    exact ((IsLocalization.map_units O s).mul_left_eq_zero).mp hms
  have hdimle : ringKrullDim (MRing ι O ⧸ P') ≤ ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    (WeightedDegree.ringKrullDim_quotient_map_le (M₀ := 𝔭.primeCompl) P).trans_eq hP.2.2.2

  have key := ConservationOfNumberLE.proof.{0} IntNumAssoc.full SpecialCycleEval.full
    SpecialPieceRank.full GenericPieceRank.full SpecialIdealMultiHomog.full O ϖ hϖ K ι P' e hmp hnt
    hdimle a

  have hinjO : Function.Injective (Int.castRingHom O) := by
    rw [RingHom.ext_int (Int.castRingHom O) (algebraMap ℤ O)]
    exact IsLocalization.injective O 𝔭.primeCompl_le_nonZeroDivisors
  have : CharZero (FractionRing O) := WeightedDegree.charZero_fractionRing O hinjO
  have hgen : gNum P' a = intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) a := by
    have hcomp : genFib P' = (P.map (MvPolynomial.map (Int.castRingHom ℚ))).map
        (MvPolynomial.map (algebraMap ℚ (FractionRing O))) := by
      unfold genFib
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      refine RingHom.ext fun x ↦ ?_
      change MvPolynomial.map _ (MvPolynomial.map _ x) = MvPolynomial.map _ (MvPolynomial.map _ x)
      rw [MvPolynomial.map_map, MvPolynomial.map_map]
      exact congrArg (fun g ↦ MvPolynomial.map g x) (RingHom.ext_int _ _)
    unfold gNum
    rw [hcomp]
    exact (FieldNumbers.IntNumBaseChange.intersectionNumber_baseChange.1 ℚ (FractionRing O) K ι _).2 e a

  have : CharP (IsLocalRing.ResidueField O) p :=
    (CharP.charP_iff_prime_eq_zero hp).mpr (by
      rw [show ((p : ℕ) : IsLocalRing.ResidueField O) = IsLocalRing.residue O ϖ by simp [ϖ],
        IsLocalRing.residue_eq_zero_iff, hmax]
      exact Ideal.subset_span rfl)
  let : Algebra (ZMod p) (IsLocalRing.ResidueField O) :=
    (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField O)).toAlgebra
  have hspec : ∀ W : Ideal (MRing ι ℤ), vNum (W.map φ) a =
      intNum (ZMod p) (W.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) a := by
    intro W
    have hcomp : specialIdeal (W.map φ) = (W.map (MvPolynomial.map (Int.castRingHom (ZMod p)))).map
        (MvPolynomial.map (algebraMap (ZMod p) (IsLocalRing.ResidueField O))) := by
      unfold specialIdeal
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      refine RingHom.ext fun x ↦ ?_
      change MvPolynomial.map _ (MvPolynomial.map _ x) = MvPolynomial.map _ (MvPolynomial.map _ x)
      rw [MvPolynomial.map_map, MvPolynomial.map_map]
      exact congrArg (fun g ↦ MvPolynomial.map g x) (RingHom.ext_int _ _)
    unfold vNum
    rw [hcomp]
    exact (FieldNumbers.IntNumBaseChange.intersectionNumber_baseChange.1 (ZMod p) (IsLocalRing.ResidueField O) K ι _).2 e a

  have hWdisj : ∀ W ∈ (P ⊔ Ideal.span {(C (p : ℤ) : MRing ι ℤ)}).minimalPrimes,
      Disjoint (M : Set (MRing ι ℤ)) W := by
    intro W hW
    have : W.IsPrime := hW.1.1
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrW
    have hle : 𝔭 ≤ W.comap (C : ℤ →+* MRing ι ℤ) := by
      rw [h𝔭def, Ideal.span_le, Set.singleton_subset_iff]
      exact hW.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have heq := h𝔭max.eq_of_le (Ideal.comap_isPrime (C : ℤ →+* MRing ι ℤ) W).ne_top hle
    have hr' : r ∈ W.comap (C : ℤ →+* MRing ι ℤ) := hrW
    rw [← heq] at hr'
    exact hr hr'
  have hmain := WeightedDegree.cycEval_divCycle_map (R' := O) 𝔭.primeCompl P (C (p : ℤ)) hWdisj
    (fun W' : Ideal (MRing ι O) ↦ vNum W' a)
  have hCp : (C ϖ : MRing ι O) = φ (C (p : ℤ)) := by
    rw [show φ (C (p : ℤ)) = C (algebraMap ℤ O (p : ℤ)) from map_C _ _]
    simp [ϖ]
  calc intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) a = gNum P' a := hgen.symm
    _ = NumbersDVR.cycEval (fun W ↦ vNum W a) (NumbersDVR.divCycle P' (C ϖ)) := key.symm
    _ = NumbersDVR.cycEval (fun W ↦ vNum W a) (NumbersDVR.divCycle P' (φ (C (p : ℤ)))) := by rw [hCp]
    _ = NumbersDVR.cycEval (fun W ↦ vNum (W.map φ) a) (NumbersDVR.divCycle P (C (p : ℤ))) := hmain.symm
    _ = _ := by
      congr 1
      funext W
      exact hspec W

end Generic

open ReciprocityTheory.ChartRestriction.G

theorem FibreDegreeSum.proof : FibreDegreeSum.Statement := by
  intro K _ _ ι _ P e a p hP hp
  classical
  have : Fact p.Prime := ⟨hp⟩
  rw [FibreDegreeSum.intNum_eq_cycEval K ι P e a p hP, NumbersDVR.cycEval, finsum_mem_def]
  refine finsum_congr fun W ↦ ?_
  by_cases hW : W ∈ Geo.divSupp P (C (p : ℤ))
  · rw [Set.indicator_of_mem hW]
    have hW' : W ∈ (P ⊔ Ideal.span {C (p : ℤ)}).minimalPrimes ∧ NumbersDVR.IsRelevant W := hW
    have hWp : W.IsPrime := hW.1.1.1
    have hpW : (C (p : ℤ) : Geo.MRing ι) ∈ W :=
      hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hC : Geo.IsMultiHomog (C (p : ℤ) : Geo.MRing ι) 0 := by
      intro m hm k
      have h0 := MvPolynomial.mem_support_iff.mp hm
      rw [coeff_C] at h0
      split_ifs at h0 with h
      · subst h
        simp
      · exact absurd rfl h0
    have hMP : Geo.IsMultiProjPrime W :=
      ⟨hWp, ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes hP.2.1.2.1 hC hW.1, hW.2⟩
    have hdimW : ringKrullDim (Geo.MRing ι ⧸ W) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      refine FibreCompDimZ.full (Σ k, ι k) P hP.2.1.1 hP.2.2.1 (e + Fintype.card K) p hp ?_ W hW.1
      rw [show e + Fintype.card K + 1 = e + 1 + Fintype.card K by omega]
      exact hP.2.2.2
    have hm : Geo.multAt (P ⊔ Ideal.span {C (p : ℤ)}) W =
        (NumbersDVR.multAt (P ⊔ Ideal.span {C (p : ℤ)}) W).toNat :=
      Bridge.multAt_eq_toNat _ _
    rw [NumbersDVR.divCycle, dite_eq_left hW', hm, Bridge.intNum_map_eq_geoNum p e W hMP hpW hdimW a]
  · have hW' : ¬(W ∈ (P ⊔ Ideal.span {C (p : ℤ)}).minimalPrimes ∧ NumbersDVR.IsRelevant W) := hW
    rw [Set.indicator_of_notMem hW, NumbersDVR.divCycle, dite_eq_right hW', zero_mul]

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsPosDensIntegrable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj pot PBlk oneLine isSmoothHerm_oneLine)

def PtsPosDensIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth g →
      Integrable (ptsPosDens P Ψ (pot L) g)

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsSheetOnlyNull
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet PBlk)

def PtsSheetOnlyNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsGoodProj P Ψ' →
      volume {y : Fin e → ℂ | ∃ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, IsSimpleSheetPt P Ψ w ∧
        ¬ IsSimpleSheetPt P Ψ' ((Ψ' w 0)⁻¹ • w)} = 0

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsPosDensMeasurable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj pot PBlk oneLine)

def PtsPosDensMeasurable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
      AEMeasurable (ptsPosDens P Ψ (pot L) g)

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartSectionLength
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn divSupp IsHorizontal multAt PBlk fsLine Xc)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartComponents localMult)

def ChartSectionLength.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → IsSectionOn P A s →
      ∀ W, W ∈ divSupp P s → IsHorizontal W → ∀ W' ∈ segreChartComponents W σ i,
        localMult (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}) W' =
          multAt (P ⊔ Ideal.span {s}) W

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartSheetCompare
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm oneLine isSmoothHerm_oneLine)
open ComplexSets Matrix

def SegreChartSheetCompare.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι), (∀ j, IsSmoothHerm (L j)) →
      ∃ C : ℝ, ∀ J ∈ segreChartComponents P σ i, ∀ (A : Matrix (Fin e) (Fin m) ℂ) (x : Fin m → ℂ)
        (s : (Fin e → ℂ) → Fin m → ℂ), x ∈ zeroSet J → IsSheetAt J A x s →
          |ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i L k ∘ s) (A *ᵥ x)| ≤
            C * |ReciprocityTheory.AnForm.maDens
              (fun _ => (fun w => Real.log ((HermNorm.std m).dualNorm w)) ∘ s) (A *ᵥ x)|

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveCountLower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo

def CurveCountLower.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) 1 → Birational y → IsSmoothHerm A →
    IsConjInvariantH A →
    ∃ C : ℝ, ∀ τ : ℕ, 1 ≤ τ →
      (τ : ℝ) * II K ι (mCoordIdeal y) 1 (fun _ => A) - C ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) τ

namespace CurveCountLower

end CurveCountLower

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisorLength
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn divSupp IsHorizontal multAt PBlk fsLine Xc)
open GroundTheory.Heights₂.Heights (segreChartComponents localMult)


open Classical in
def ChartDivisorLength.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → IsSectionOn P A s →
      ∀ W, W ∈ divSupp P s → IsHorizontal W → ∀ W' ∈ segreChartComponents W σ i,
        ∑ J ∈ (segreChartComponents P σ i).filter (fun J => J ≤ W'),
            localMult (J ⊔ Ideal.span {chartSection σ i s}) W' =
          multAt (P ⊔ Ideal.span {s}) W

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFCoord
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem PFCoord.of_found (hGD : GenDegStatement)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hGF : GenFibreExistsStatement) (hFD : FibreDimStatement) (hCF : CoordFibreDeg.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement := by
  intro I hI K _ ι _ K' _ ι' _ κ v Ω _ _ y d L L' hv hP' hP hL hLL'
  obtain ⟨G⟩ := hGF K ι K' ι' κ v (mCoordIdeal y) d hv hP'
  obtain ⟨J, hJ, -⟩ := hR4 G.Φ (FibreBlock κ) (fibreIdx ι' κ)
  have hV : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) 0 := hFD K ι K' ι' κ v (mCoordIdeal y) d 0 G hv hP' hP
  choose i hi using hV.1.2.2
  have h0 := hJ.1 (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) Fin.elim0 i hV hi
  rw [hGD I hI K ι K' ι' κ v (mCoordIdeal y) d G J L L' hv hP' hP hJ hL hLL', h0,
    hCF K ι K' ι' κ v Ω y d G i hv hP' hP hi, Int.cast_natCast]

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsPosPartLocal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj mcPts segre pot PBlk oneLine
  isSmoothHerm_oneLine)

def PtsPosPartLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (z : (Σ k, ι k) → ℂ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsGoodProj P Ψ' → (∀ j, IsSmoothHerm (L j)) →
    Measurable g → (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z' p) = g z') →
    z ∈ mcPts P → IsSimpleSheetPt P Ψ ((Ψ (segre z) 0)⁻¹ • segre z) →
    IsSimpleSheetPt P Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z) →
      ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ z ∈ W ∧
        (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ W ↔ z' ∈ W)) ∧
        ∀ E : Set ((Σ k, ι k) → ℂ), MeasurableSet E →
          (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ E ↔ z' ∈ E)) →
          E ⊆ W →
            ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) (E.indicator g) y) =
              ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ' (pot L) (E.indicator g) y)

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiBig
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem MoriwakiBig.of_found (hG6 : HilbertSamuel.ArithmeticVolumeBig.Statement) (hC : MoriwakiBigCurve.Statement) :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement := by
  intro K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact hC K ι Ω y A P0 II hII har hb hP0 hs hc hnef hgen
  · exact hG6 K ι Ω y D A P0 II hD hII har hb hP0 hs hnef hc

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PoincareLelongAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem PoincareLelongAlt.of_found (hSt : StokesStatement) (hReg : PoincareLelongRegularised.Statement)
    (hLim : PoincareLelongLimit.Statement) : ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticPoincareLelongFormula := by
  intro K _ ι _ P n L A B s hP hL hA hB hBa hs
  obtain ⟨a, ha, hsa, -⟩ := id hs
  have hS : ∀ ε ∈ Set.Ioi (0 : ℝ),
      ptsIntegral P (Fin.cons (regLog A s ε) (pot L)) (fun z => Real.log (B.h z)) =
        ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (regLog A s ε) := by
    intro ε hε
    have h := hSt K ι P n L (regLine A s ε ha hsa) B hP hL (isSmoothHerm_regLine hA hε ha hsa) hB
      (regLine_a A s ε ha hsa) hBa
    rw [log_regLine] at h
    exact h.symm
  exact tendsto_nhds_unique (hReg K ι P n L A B s hP hL hA hB hBa hs)
    ((hLim K ι P n L A B s hP hL hA hB hBa hs).congr' (eventually_nhdsWithin_of_forall hS))

end GroundTheory.Heights₂.Heights.Targets
end
