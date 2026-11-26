module

public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicJacobianNeZero
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

variable {n d : ℕ}

def IsSheetAt (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ)
    (s : (Fin d → ℂ) → Fin n → ℂ) : Prop :=
  ∃ U : Set (Fin d → ℂ), IsOpen U ∧ A *ᵥ x ∈ U ∧ DifferentiableOn ℂ s U ∧ s (A *ᵥ x) = x ∧
    (∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
    ∃ V ∈ 𝓝 x, ∀ x' ∈ zeroSet J ∩ V, A *ᵥ x' ∈ U → x' = s (A *ᵥ x')


open scoped Classical in
open Classical in
def sheetSum (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  ∑ᶠ (x : Fin n → ℂ) (_ : x ∈ fibre J A y),
    if h : ∃ s, IsSheetAt J A x s then F x h.choose else 0

def chartDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  sheetSum J A (fun x s => f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) y

def chartAbsDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  sheetSum J A (fun x s => |f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y|) y

def chartInt (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) : ℝ :=
  ∫ y, chartDens J A f φ y


open scoped Classical in
open Classical in
def varInt (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) : ℝ :=
  if h : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J A then chartInt J h.choose f φ else 0

def SmoothNear (S : Set (Fin n → ℂ)) (φ : (Fin n → ℂ) → ℝ) : Prop :=
  ∃ U : Set (Fin n → ℂ), IsOpen U ∧ S ⊆ U ∧ ContDiffOn ℝ ∞ φ U

def linEval (u x : Fin n → ℂ) : ℂ := ∑ j, u j * x j

def euclPot (x : Fin n → ℂ) : ℝ := ∑ j, ‖x j‖ ^ 2

def energyInt (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (B : Set (Fin n → ℂ)) (χ : (Fin n → ℂ) → ℝ) : ℝ :=
  chartInt J A (B.indicator fun _ => 1) (vecCons (fun x => χ x ^ 2 / 2) fun _ => euclPot) -
    chartInt J A (B.indicator χ) (vecCons χ fun _ => euclPot)

structure VarBranch (J : Ideal (MvPolynomial (Fin n) ℂ)) (k : ℕ) (p : Fin n → ℂ) where

  radius : ℝ
  radius_pos : 0 < radius

  toFun : (Fin k → ℂ) → Fin n → ℂ
  differentiableOn : DifferentiableOn ℂ toFun (Metric.ball 0 radius)
  injOn : Set.InjOn toFun (Metric.ball 0 radius)
  map_zero : toFun 0 = p
  mapsTo : Set.MapsTo toFun (Metric.ball 0 radius) (zeroSet J)

def VarBranch.image {J : Ideal (MvPolynomial (Fin n) ℂ)} {k : ℕ} {p : Fin n → ℂ}
    (b : VarBranch J k p) : Set (Fin n → ℂ) :=
  b.toFun '' Metric.ball 0 b.radius

def VarBranch.slice {J : Ideal (MvPolynomial (Fin n) ℂ)} {k : ℕ} {p : Fin n → ℂ}
    (b : VarBranch J (k + 1) p) : Set (Fin n → ℂ) :=
  b.toFun '' (Metric.ball 0 b.radius ∩ {t | t 0 = 0})

def VanishesToOrder {k : ℕ} (F : (Fin (k + 1) → ℂ) → ℂ) (r : ℝ) (m : ℕ) : Prop :=
  ∃ H : (Fin (k + 1) → ℂ) → ℂ, DifferentiableOn ℂ H (Metric.ball 0 r) ∧
    (∀ t ∈ Metric.ball 0 r, H t ≠ 0) ∧ ∀ t ∈ Metric.ball 0 r, F t = t 0 ^ m * H t

def IntegralIndep.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    IsFiniteProjection J A' → Measurable f →
    (∀ k, SmoothNear (zeroSet J) (φ k)) → Integrable (chartAbsDens J A f φ) →
      Integrable (chartAbsDens J A' f φ) ∧ chartInt J A f φ = chartInt J A' f φ

def PointIntegral.Statement : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ) (φ : Fin 0 → (Fin n → ℂ) → ℝ),
    varInt (RingHom.ker (MvPolynomial.eval p)) 0 f φ = f p

def CutOff.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      ∃ χ : ℕ → (Fin n → ℂ) → ℝ,
        (∀ k, ContDiff ℝ ∞ (χ k)) ∧ (∀ k x, χ k x ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ k, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ {x | eval (A *ᵥ x) P = 0} ⊆ U ∧
          ∀ x ∈ U ∩ zeroSet J, χ k x = 0) ∧
        (∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → Tendsto (fun k => χ k x) atTop (𝓝 1)) ∧
        (∀ R : ℝ, Tendsto (fun k => energyInt J A (Metric.closedBall 0 R) (χ k)) atTop (𝓝 0)) ∧
        (∀ (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ), (∀ i, SmoothNear (zeroSet J) (φ i)) →
          Tendsto (fun k => ∫ y, chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
            (vecCons (χ k) φ) y) atTop (𝓝 0))

def StokesOnVariety.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) →
    SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → (HasCompactSupport f ∨ HasCompactSupport g) →
      varInt J (d + 1) f (vecCons g φ) = varInt J (d + 1) g (vecCons f φ)

def LogIntegrable.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (u : Fin n → ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    linForm u ∉ J → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      Integrable (chartAbsDens J A
        ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval u x‖) φ)

def LocalOrder.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → VarBranch J (d + 1) p) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes → p ∈ zeroSet W →
    (∃ N ∈ 𝓝 p, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∃ N ∈ 𝓝 p, ∀ b, zeroSet W ∩ N ⊆ (γ b).slice) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
      localMult (J ⊔ Ideal.span {linForm u}) W = ∑ b, ord b

section Inhabitants

theorem linForm_single {n : ℕ} (i : Fin n) : linForm (Pi.single i (1 : ℂ)) = X i := by
  classical
  simp [linForm, Pi.single_apply]

theorem space_dim (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin n) ℂ))) = (n : ℕ) := by
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem smoothNear_of_contDiff {n : ℕ} {S : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ}
    (h : ContDiff ℝ ∞ φ) : SmoothNear S φ :=
  ⟨Set.univ, isOpen_univ, Set.subset_univ _, h.contDiffOn⟩

theorem contDiff_euclPot (n : ℕ) : ContDiff ℝ ∞ (euclPot : (Fin n → ℂ) → ℝ) := by
  unfold euclPot
  exact ContDiff.sum fun j _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) j)

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff ENNReal

noncomputable section

variable {n d e : ℕ}

def zeroLocus {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : Set (Fin n → ℂ) :=
  {x | ∀ q ∈ J, eval x q = 0}

structure IsAffVariety (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) : Prop where
  isPrime : J.IsPrime
  dim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d



section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjHomInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

theorem ringKrullDim_mvPolynomial_complex (d : ℕ) :
    ringKrullDim (MvPolynomial (Fin d) ℂ) = d := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem FiniteProjHomInjective.proof : FiniteProjHomInjective.Statement := by
  intro n d J A _ hdim hfin
  set f : MvPolynomial (Fin d) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J := (projHom J A).toRingHom with hf
  have hinj : Function.Injective f := by
    by_contra hni
    rw [injective_iff_map_eq_zero] at hni
    push Not at hni
    obtain ⟨p, hp0, hp⟩ := hni
    let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := f.toAlgebra
    have hint : f.IsIntegral := hfin.to_isIntegral

    let g : PrimeSpectrum (MvPolynomial (Fin n) ℂ ⧸ J) →
        PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin d) ℂ) (Ideal.span {p}) := fun q =>
      ⟨PrimeSpectrum.comap f q, by
        rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le,
          Set.singleton_subset_iff]
        show f p ∈ q.asIdeal
        rw [hp0]; exact q.asIdeal.zero_mem⟩
    have hg : StrictMono g := by
      intro q₁ q₂ hq
      have hlt : q₁.asIdeal < q₂.asIdeal := hq
      obtain ⟨hle, x, hx2, hx1⟩ := SetLike.lt_iff_le_and_exists.mp hlt
      show q₁.asIdeal.comap (algebraMap _ _) < q₂.asIdeal.comap (algebraMap _ _)
      exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hx2, hx1⟩ (hint x)
    have h1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤
        ringKrullDim (MvPolynomial (Fin d) ℂ ⧸ Ideal.span {p}) := by
      rw [ringKrullDim_quotient (Ideal.span {p})]
      exact Order.krullDim_le_of_strictMono g hg
    have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (mem_nonZeroDivisors_of_ne_zero hp)
    rw [ringKrullDim_mvPolynomial_complex] at h2
    rw [hdim] at h1
    have h3 : ((d : ℕ) : WithBot ℕ∞) + 1 ≤ (d : WithBot ℕ∞) := le_trans (by gcongr) h2
    have h4 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by exact_mod_cast h3
    have h5 : d + 1 ≤ d := by exact_mod_cast h4
    omega
  exact fun a b h => hinj h

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem homogeneousComponent_mul_of_isHomogeneous_right {σ : Type*} (a g : MvPolynomial σ ℂ)
    {e : ℕ} (hg : g.IsHomogeneous e) (k : ℕ) :
    homogeneousComponent k (a * g) = if e ≤ k then homogeneousComponent (k - e) a * g else 0 := by
  have hd : ∀ (p : MvPolynomial σ ℂ) (i : ℕ),
      (DirectSum.decompose (homogeneousSubmodule σ ℂ) p i : MvPolynomial σ ℂ) =
        homogeneousComponent i p := fun p i => decomposition.decompose'_apply p i
  have h := DirectSum.coe_decompose_mul_of_right_mem (homogeneousSubmodule σ ℂ) k (a := a)
    ((mem_homogeneousSubmodule e g).2 hg)
  simpa only [hd] using h

theorem isHomogeneous_linPoly {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (j : Fin d) :
    (linPoly A j).IsHomogeneous 1 := by
  have : linPoly A j ∈ homogeneousSubmodule (Fin n) ℂ 1 := by
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X ℂ i))
  exact (mem_homogeneousSubmodule 1 _).1 this

theorem ConeAvoidsFinite.proof : ConeAvoidsFinite.Statement := by
  intro n d N J A hcone
  letI alg : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  letI : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := alg.toModule
  show Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)
  classical
  let gen : Finset (MvPolynomial (Fin n) ℂ ⧸ J) := Finset.univ.image fun f : Fin n → Fin N =>
    Ideal.Quotient.mk J (monomial (Finsupp.equivFunOnFinite.symm fun i => (f i : ℕ)) 1)
  let M := Submodule.span (MvPolynomial (Fin d) ℂ) (gen : Set (MvPolynomial (Fin n) ℂ ⧸ J))
  set_option synthInstance.maxHeartbeats 100000 in
  have hsmul : ∀ (s : MvPolynomial (Fin d) ℂ) (p : MvPolynomial (Fin n) ℂ),
      Ideal.Quotient.mk J p ∈ M → Ideal.Quotient.mk J (pullback A s * p) ∈ M := by
    intro s p hp
    have : Ideal.Quotient.mk J (pullback A s * p) = s • Ideal.Quotient.mk J p := by
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul]; rfl
    rw [this]; exact M.smul_mem s hp
  have hsum : ∀ {ι : Type} (s : Finset ι) (q : ι → MvPolynomial (Fin n) ℂ),
      (∀ i ∈ s, Ideal.Quotient.mk J (q i) ∈ M) → Ideal.Quotient.mk J (∑ i ∈ s, q i) ∈ M :=
    fun s q h => by rw [map_sum]; exact M.sum_mem h
  have hmain : ∀ k (q : MvPolynomial (Fin n) ℂ), q.IsHomogeneous k → Ideal.Quotient.mk J q ∈ M := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>

    have key : ∀ (b x : MvPolynomial (Fin n) ℂ),
        x ∈ leadForm '' (J : Set (MvPolynomial (Fin n) ℂ)) ∪ Set.range (linPoly A) →
        Ideal.Quotient.mk J (homogeneousComponent k (b * x)) ∈ M := by
      rintro b x (⟨f, hf, rfl⟩ | ⟨j, rfl⟩)
      · rw [homogeneousComponent_mul_of_isHomogeneous_right b (leadForm f) (e := f.totalDegree)
          (homogeneousComponent_isHomogeneous f.totalDegree f)]
        split_ifs with hek
        · have hs := sum_homogeneousComponent f
          rw [Finset.sum_range_succ] at hs
          have hf' : leadForm f = f - ∑ i ∈ Finset.range f.totalDegree, homogeneousComponent i f := by
            rw [leadForm]; linear_combination hs
          rw [hf', mul_sub, map_sub, Finset.mul_sum,
            Ideal.Quotient.eq_zero_iff_mem.2 (J.mul_mem_left _ hf), zero_sub]
          refine M.neg_mem (hsum _ _ fun i hi => ih _ ?_ _
            ((homogeneousComponent_isHomogeneous _ _).mul (homogeneousComponent_isHomogeneous _ _)))
          have := Finset.mem_range.1 hi; omega
        · simp
      · rw [homogeneousComponent_mul_of_isHomogeneous_right b _ (isHomogeneous_linPoly A j)]
        split_ifs with hk
        · have hl : linPoly A j = pullback A (X j) := by simp [pullback]
          rw [mul_comm, hl]
          exact hsmul _ _ (ih _ (by omega) _ (homogeneousComponent_isHomogeneous _ _))
        · simp

    intro q hq
    rw [q.as_sum]
    refine hsum _ _ fun s hs => ?_
    have hdeg : s.degree = k := by
      have := hq (mem_support_iff.mp hs)
      rw [Finsupp.degree_eq_weight_one]; exact this
    have hCs : monomial s (AddMonoidAlgebra.coeff q s) = pullback A (C (AddMonoidAlgebra.coeff q s)) * monomial s 1 := by
      simp [pullback, C_mul_monomial]
    rw [hCs]
    refine hsmul _ _ ?_
    by_cases hlow : ∀ i, s i < N
    · refine Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2
        ⟨fun i => ⟨s i, hlow i⟩, Finset.mem_univ _, ?_⟩))
      congr 2; ext i; simp
    simp only [not_forall, not_lt] at hlow
    obtain ⟨i, hi⟩ := hlow

    have hmem : monomial s (1 : ℂ) ∈ leadIdeal J ⊔ linIdeal A := by
      apply hcone
      have hsplit : monomial s (1 : ℂ) = X i ^ N * monomial (s - Finsupp.single i N) 1 := by
        rw [← monomial_single_add, add_tsub_cancel_of_le (Finsupp.single_le_iff.2 hi)]
      rw [hsplit]
      exact Ideal.mul_mem_right _ _
        (Ideal.pow_mem_pow (show X i ∈ originIdeal n from Ideal.subset_span ⟨i, rfl⟩) N)
    rw [leadIdeal, linIdeal, ← Ideal.span_union] at hmem
    obtain ⟨r, a, g, hag⟩ := Submodule.mem_span_set'.1 hmem
    have hm : monomial s (1 : ℂ) = homogeneousComponent k (∑ t, a t • (g t : MvPolynomial (Fin n) ℂ)) := by
      rw [hag, homogeneousComponent_eq_self (isHomogeneous_monomial _ hdeg)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hm, map_sum]
    exact hsum _ _ fun t _ => by rw [smul_eq_mul]; exact key _ _ (g t).2
  have htop : M = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← sum_homogeneousComponent p]
    exact hsum _ _ fun i _ => hmain i _ (homogeneousComponent_isHomogeneous i p)
  exact ⟨⟨gen, htop⟩⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedOffDiscriminant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def PrimitiveFormSheetedOffDiscriminant.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∃ M ∈ 𝓝 w, ∀ y ∈ X ∩ M, δ (A y) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
        (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ y ∈ V ∧ AnalyticOnNhd ℂ g O ∧
          (∀ t ∈ O, A (g t) = t) ∧ X ∩ V = g '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicInverse
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

namespace InjectiveHolomorphicInverse

theorem analyticAt_of_differentiableOn {k : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin k → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : Fin k → ℂ} (hx : x ∈ U) : AnalyticAt ℂ f x := by
  refine AnalyticAt.pi fun i => ?_
  refine analyticOnNhd_of_continuousOn_of_separately hU
    ((continuous_apply i).comp_continuousOn hf.continuousOn) (fun z hz j => ?_) x hx
  have hfz : DifferentiableAt ℂ (fun w => f w i) z :=
    differentiableAt_pi.mp (hf.differentiableAt (hU.mem_nhds hz)) i
  have hu : DifferentiableAt ℂ (Function.update z j) (z j) :=
    (hasFDerivAt_update z (z j)).differentiableAt
  have hfz' : DifferentiableAt ℂ (fun w => f w i) (Function.update z j (z j)) := by
    rwa [Function.update_eq_self]
  exact hfz'.comp (z j) hu

theorem exists_equiv (hJ : InjectiveHolomorphicJacobianNeZero.Statement) {k : ℕ} {U : Set (Fin k → ℂ)}
    {f : (Fin k → ℂ) → Fin k → ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U)
    {x : Fin k → ℂ} (hx : x ∈ U) :
    ∃ e : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ), HasStrictFDerivAt f (e : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) x := by
  have hdet := hJ k U f hU hf hinj x hx
  refine ⟨(LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv, ?_⟩
  have he : ((LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv :
      (Fin k → ℂ) →L[ℂ] Fin k → ℂ) = fderiv ℂ f x := by
    ext1 v
    rfl
  rw [he]
  exact (analyticAt_of_differentiableOn hU hf hx).hasStrictFDerivAt

theorem proof (hJ : InjectiveHolomorphicJacobianNeZero.Statement) : InjectiveHolomorphicInverse.Statement := by
  intro k U f hU hf hinj
  have hleft : ∀ z ∈ U, Function.invFunOn f U (f z) = z := fun z hz =>
    hinj (Function.invFunOn_mem ⟨z, hz, rfl⟩) hz (Function.invFunOn_eq ⟨z, hz, rfl⟩)
  refine ⟨?_, Function.invFunOn f U, ?_, hleft⟩
  · rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := exists_equiv hJ hU hf hinj hx
    rw [← he.map_nhds_eq_of_equiv]
    exact Filter.image_mem_map (hU.mem_nhds hx)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := exists_equiv hJ hU hf hinj hx
    refine (he.to_local_left_inverse ?_).differentiableAt.differentiableWithinAt
    filter_upwards [hU.mem_nhds hx] with z hz
    exact hleft z hz

end InjectiveHolomorphicInverse

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLeadIdealDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

variable {n : ℕ}

theorem leadForm_ne_zero {f : MvPolynomial (Fin n) ℂ} (hf : f ≠ 0) : leadForm f ≠ 0 := by
  obtain ⟨d, hd, hdeg⟩ := Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf)
    (fun m => m.sum fun _ e => e)
  intro h0
  have hc := congrArg (AddMonoidAlgebra.coeff · d) h0
  rw [leadForm, coeff_homogeneousComponent] at hc
  rw [if_pos (by rw [totalDegree, hdeg]; rfl)] at hc
  apply (mem_support_iff.mp hd)
  simpa [AddMonoidAlgebra.coeff] using hc

theorem vars_leadForm_subset (f : MvPolynomial (Fin n) ℂ) : (leadForm f).vars ⊆ f.vars := by
  intro i hi
  rw [mem_vars_iff_mem_support] at hi ⊢
  obtain ⟨d, hd, hid⟩ := hi
  refine ⟨d, ?_, hid⟩
  rw [mem_support_iff, leadForm, coeff_homogeneousComponent] at hd
  rw [mem_support_iff]
  split_ifs at hd
  · exact hd
  · exact absurd rfl hd

theorem aeval_mk_X (I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Set (Fin n))
    (q : MvPolynomial u ℂ) :
    aeval (fun i : u => Ideal.Quotient.mk I (X (i : Fin n))) q =
      Ideal.Quotient.mk I (rename Subtype.val q) := by
  induction q using MvPolynomial.induction_on with
  | C a => rw [aeval_C, rename_C]; rfl
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem algebraicIndependent_mk_X_iff (I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Set (Fin n)) :
    AlgebraicIndependent ℂ (fun i : u => Ideal.Quotient.mk I (X (i : Fin n))) ↔
      ∀ q : MvPolynomial u ℂ, rename Subtype.val q ∈ I → q = 0 := by
  rw [algebraicIndependent_iff]
  simp only [aeval_mk_X, Ideal.Quotient.eq_zero_iff_mem]

theorem rename_mem_of_leadIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Set (Fin n))
    (h : ∀ q : MvPolynomial u ℂ, rename Subtype.val q ∈ leadIdeal J → q = 0)
    (q : MvPolynomial u ℂ) (hq : rename Subtype.val q ∈ J) : q = 0 := by
  by_contra hq0
  have hf : rename Subtype.val q ≠ 0 := by
    rwa [Ne, ← map_zero (rename (Subtype.val : u → Fin n)),
      (rename_injective _ Subtype.val_injective).eq_iff]
  have hvars : ((leadForm (rename Subtype.val q)).vars : Set (Fin n)) ⊆
      Set.range (Subtype.val : u → Fin n) := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := mem_vars_rename _ _ (vars_leadForm_subset _ hi)
    exact ⟨j, rfl⟩
  obtain ⟨r, hr⟩ := exists_rename_eq_of_vars_subset_range _ _ Subtype.val_injective hvars
  have hr0 : r = 0 := h r (hr ▸ Ideal.subset_span ⟨_, hq, rfl⟩)
  exact leadForm_ne_zero hf (by rw [← hr, hr0, map_zero])

theorem quotient_dim_le_of_minimalPrimes {R : Type*} [CommRing R] (I : Ideal R)
    {N : WithBot ℕ∞} (h : ∀ Z ∈ I.minimalPrimes, ringKrullDim (R ⧸ Z) ≤ N) :
    ringKrullDim (R ⧸ I) ≤ N := by
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_coheight, iSup_le_iff]
  intro a
  obtain ⟨Z, hZ, hZa⟩ :=
    Ideal.exists_minimalPrimes_le ((PrimeSpectrum.mem_zeroLocus _ _).mp a.2)
  have : Z.IsPrime := hZ.1.1
  let z : PrimeSpectrum.zeroLocus (R := R) (I : Set R) :=
    ⟨⟨Z, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hZ.1.2⟩
  have hza : z ≤ a := hZa
  let e : Set.Ici z ↪o PrimeSpectrum.zeroLocus (R := R) (Z : Set R) :=
    OrderEmbedding.ofMapLEIff
      (fun x => ⟨x.1.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr (show Z ≤ x.1.1.asIdeal from x.2)⟩)
      fun _ _ => Iff.rfl
  calc ((Order.coheight a : ℕ∞) : WithBot ℕ∞) ≤ ((Order.coheight z : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (Order.coheight_anti hza)
    _ = Order.krullDim (Set.Ici z) := Order.coheight_eq_krullDim_Ici z
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) (Z : Set R)) :=
        Order.krullDim_le_of_orderEmbedding e
    _ = ringKrullDim (R ⧸ Z) := (ringKrullDim_quotient Z).symm
    _ ≤ N := h Z hZ

theorem exists_vars_isTranscendenceBasis (P : Ideal (MvPolynomial (Fin n) ℂ)) [P.IsPrime] :
    ∃ u : Set (Fin n), AlgebraicIndependent ℂ (fun i : u => Ideal.Quotient.mk P (X (i : Fin n))) ∧
      Cardinal.mk u = Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P) := by
  set x : Fin n → MvPolynomial (Fin n) ℂ ⧸ P := fun i => Ideal.Quotient.mk P (X i) with hx
  have hrange : Set.range x = Ideal.Quotient.mkₐ ℂ P '' Set.range X := by
    rw [← Set.range_comp]; rfl
  have hadj : Algebra.adjoin ℂ (Set.range x) = ⊤ := by
    rw [hrange, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top,
      AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective ℂ P
  have _ : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range x)) (MvPolynomial (Fin n) ℂ ⧸ P) :=
    ⟨fun a => isAlgebraic_algebraMap (R := Algebra.adjoin ℂ (Set.range x))
      (⟨a, hadj ▸ Algebra.mem_top⟩ : Algebra.adjoin ℂ (Set.range x))⟩
  have _ := (faithfulSMul_iff_algebraMap_injective ℂ (MvPolynomial (Fin n) ℂ ⧸ P)).mpr
    (algebraMap ℂ _).injective
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := ℂ) (Set.range x)
  obtain ⟨u, hu, hinj⟩ := Set.exists_image_eq_injOn_of_subset_range hts
  let g : u → t := fun i => ⟨x i, hu ▸ Set.mem_image_of_mem x i.2⟩
  have hg : Function.Injective g := fun i j hij =>
    Subtype.ext (hinj i.2 j.2 (congrArg Subtype.val hij))
  refine ⟨u, ht.1.comp g hg, ?_⟩
  rw [← ht.cardinalMk_eq_trdeg, ← hu, Cardinal.mk_image_eq_of_injOn _ _ hinj]

theorem LeadIdealDim.proof : LeadIdealDim.Statement := by
  intro n J
  apply quotient_dim_le_of_minimalPrimes
  intro P hP
  have _ : P.IsPrime := hP.1.1
  obtain ⟨u, hu, hcard⟩ := exists_vars_isTranscendenceBasis P
  have hJ : ∀ q : MvPolynomial u ℂ, rename Subtype.val q ∈ J → q = 0 :=
    rename_mem_of_leadIdeal J u fun q hq => (algebraicIndependent_mk_X_iff P u).mp hu q (hP.1.2 hq)

  let M : Submonoid (MvPolynomial (Fin n) ℂ) :=
    (nonZeroDivisors (MvPolynomial u ℂ)).map (rename (R := ℂ) (Subtype.val : u → Fin n))
  have hdis : Disjoint (J : Set (MvPolynomial (Fin n) ℂ)) M := by
    rw [Set.disjoint_left]
    rintro _ hJf ⟨q, hq, rfl⟩
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hq) (hJ q hJf)
  obtain ⟨Q, hQ, hJQ, hQM⟩ := Ideal.exists_le_prime_disjoint J M hdis
  have hQu : AlgebraicIndependent ℂ (fun i : u => Ideal.Quotient.mk Q (X (i : Fin n))) := by
    rw [algebraicIndependent_mk_X_iff]
    intro q hq
    by_contra hq0
    exact Set.disjoint_left.mp hQM hq ⟨q, mem_nonZeroDivisors_of_ne_zero hq0, rfl⟩
  obtain ⟨a, haP, htP⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg ℂ (A := MvPolynomial (Fin n) ℂ ⧸ P)
  obtain ⟨b, hbQ, htQ⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg ℂ (A := MvPolynomial (Fin n) ℂ ⧸ Q)
  have hab : a ≤ b := by
    have h := hQu.cardinalMk_le_trdeg
    rw [hcard, htP, htQ] at h
    exact_mod_cast h
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = a := haP
    _ ≤ b := by exact_mod_cast hab
    _ = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) := hbQ.symm
    _ ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor hJQ) (Ideal.Quotient.factor_surjective hJQ)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PManifoldZerosComplementConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Set

theorem ManifoldZerosComplementConnected.isPreconnected_of_local {α : Type*} [TopologicalSpace α]
    {X S : Set α} (hX : IsPreconnected X) (hSX : S ⊆ X) (hdense : ∀ x ∈ X, x ∈ closure S)
    (hloc : ∀ x ∈ X, ∃ W, IsOpen W ∧ x ∈ W ∧ IsPreconnected (W ∩ S)) : IsPreconnected S := by
  intro u v hu hv hSuv ⟨a, haS, hau⟩ ⟨b, hbS, hbv⟩
  by_contra hne
  have hne' : ∀ y ∈ S, y ∈ u → y ∈ v → False := fun y hy hyu hyv => hne ⟨y, hy, hyu, hyv⟩
  let P : Set α := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ W ∩ S ⊆ u}
  let Q : Set α := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ W ∩ S ⊆ v}
  have hP : IsOpen P := isOpen_iff_forall_mem_open.mpr fun x ⟨W, hW, hxW, hWS⟩ =>
    ⟨W, fun y hy => ⟨W, hW, hy, hWS⟩, hW, hxW⟩
  have hQ : IsOpen Q := isOpen_iff_forall_mem_open.mpr fun x ⟨W, hW, hxW, hWS⟩ =>
    ⟨W, fun y hy => ⟨W, hW, hy, hWS⟩, hW, hxW⟩
  have hcov : X ⊆ P ∪ Q := by
    intro x hx
    obtain ⟨W, hW, hxW, hWc⟩ := hloc x hx
    by_cases h1 : (W ∩ S ∩ u).Nonempty
    · by_cases h2 : (W ∩ S ∩ v).Nonempty
      · obtain ⟨y, hyWS, hyu, hyv⟩ := hWc u v hu hv (fun y hy => hSuv hy.2) h1 h2
        exact (hne' y hyWS.2 hyu hyv).elim
      · refine Or.inl ⟨W, hW, hxW, fun y hy => ?_⟩
        rcases hSuv hy.2 with h | h
        · exact h
        · exact absurd ⟨y, hy, h⟩ h2
    · refine Or.inr ⟨W, hW, hxW, fun y hy => ?_⟩
      rcases hSuv hy.2 with h | h
      · exact absurd ⟨y, hy, h⟩ h1
      · exact h
  obtain ⟨x, hxX, ⟨W₁, hW₁, hxW₁, hW₁u⟩, ⟨W₂, hW₂, hxW₂, hW₂v⟩⟩ :=
    hX P Q hP hQ hcov ⟨a, hSX haS, u, hu, hau, inter_subset_left⟩
      ⟨b, hSX hbS, v, hv, hbv, inter_subset_left⟩
  obtain ⟨y, ⟨hy₁, hy₂⟩, hyS⟩ := mem_closure_iff.mp (hdense x hxX) _ (hW₁.inter hW₂) ⟨hxW₁, hxW₂⟩
  exact hne' y hyS (hW₁u ⟨hy₁, hyS⟩) (hW₂v ⟨hy₂, hyS⟩)

theorem ManifoldZerosComplementConnected.isPreconnected_ball_diff_countable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : 1 < Module.rank ℝ E) (c : E) {r : ℝ} (hr : 0 < r)
    {s : Set E} (hs : s.Countable) : IsPreconnected (Metric.ball c r \ s) := by
  let e : OpenPartialHomeomorph E E := OpenPartialHomeomorph.univBall c r
  have hsrc : e.source = univ := OpenPartialHomeomorph.univBall_source c r
  have htgt : e.target = Metric.ball c r := OpenPartialHomeomorph.univBall_target c hr
  have hc : (e ⁻¹' s).Countable := hs.preimage_of_injOn (e.injOn.mono (by rw [hsrc]; exact subset_univ _))
  have hcont : ContinuousOn e univ := hsrc ▸ e.continuousOn
  have heq : e '' (e ⁻¹' s)ᶜ = Metric.ball c r \ s := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨htgt ▸ e.map_source (hsrc ▸ mem_univ v), hv⟩
    · rintro ⟨hw, hws⟩
      rw [← htgt] at hw
      exact ⟨e.symm w, by simpa [mem_compl_iff, mem_preimage, e.right_inv hw] using hws, e.right_inv hw⟩
  rw [← heq]
  exact (hc.isConnected_compl_of_one_lt_rank hE).isPreconnected.image e (hcont.mono (subset_univ _))

theorem ManifoldZerosComplementConnected.isPreconnected_inter_ne_zero_of_complex {V : Set ℂ}
    (hVo : IsOpen V) (hV : IsPreconnected V) {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ V) {z₀ : ℂ}
    (hz₀ : z₀ ∈ V) (hφz₀ : φ z₀ ≠ 0) : IsPreconnected (V ∩ {z | φ z ≠ 0}) := by
  have hev : ∀ z ∈ V, ∀ᶠ w in 𝓝[≠] z, φ w ≠ 0 := by
    intro z hz
    rcases (hφ z hz).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hV hz h hz₀) hφz₀
    · exact h
  refine ManifoldZerosComplementConnected.isPreconnected_of_local hV inter_subset_left ?_ ?_
  · intro z hz
    have h1 : ∀ᶠ w in 𝓝[≠] z, w ∈ V ∩ {z | φ z ≠ 0} :=
      ((hev z hz).and (nhdsWithin_le_nhds (hVo.mem_nhds hz))).mono fun w hw => ⟨hw.2, hw.1⟩
    exact mem_closure_iff_frequently.mpr (h1.frequently.filter_mono nhdsWithin_le_nhds)
  · intro z hz
    obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hVo z hz
    obtain ⟨r', hr', hr'φ⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp (hev z hz))
    have hρ : 0 < min r r' := lt_min hr hr'
    refine ⟨Metric.ball z (min r r'), Metric.isOpen_ball, Metric.mem_ball_self hρ, ?_⟩
    have heq : Metric.ball z (min r r') ∩ (V ∩ {w | φ w ≠ 0}) =
        Metric.ball z (min r r') \ ({z} \ {w | φ w ≠ 0}) := by
      ext w
      simp only [mem_inter_iff, Set.mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hb, -, hne⟩
        exact ⟨hb, fun h => h.2 hne⟩
      · rintro ⟨hb, hw⟩
        refine ⟨hb, hrV (Metric.ball_subset_ball (min_le_left _ _) hb), ?_⟩
        by_cases hwz : w = z
        · intro h0
          exact hw ⟨hwz, fun h => h h0⟩
        · exact hr'φ w (Metric.ball_subset_ball (min_le_right _ _) hb) hwz
    rw [heq]
    exact ManifoldZerosComplementConnected.isPreconnected_ball_diff_countable
      (by rw [Complex.rank_real_complex]; exact_mod_cast (by norm_num : (1 : ℕ) < 2)) z hρ ((countable_singleton z).mono sdiff_subset)

theorem ManifoldZerosComplementConnected.isPreconnected_convex_inter_ne_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} (hUo : IsOpen U) (hUc : Convex ℝ U)
    {f : E → ℂ} (hf : AnalyticOnNhd ℂ f U) : IsPreconnected (U ∩ {z | f z ≠ 0}) := by
  refine isPreconnected_of_forall_pair ?_
  rintro p ⟨hpU, hp⟩ q ⟨hqU, hq⟩
  let ℓ : ℂ → E := fun t => p + t • (q - p)
  have hℓc : Continuous ℓ := by fun_prop
  have hℓa : ∀ t, AnalyticAt ℂ ℓ t := fun t =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hVo : IsOpen (ℓ ⁻¹' U) := hUo.preimage hℓc
  have hVc : Convex ℝ (ℓ ⁻¹' U) := by
    intro a ha b hb s t hs ht hst
    have hmem := hUc ha hb hs ht hst
    show ℓ (s • a + t • b) ∈ U
    convert hmem using 1
    obtain rfl : t = 1 - s := by linarith
    simp only [ℓ, ← Complex.coe_smul]
    push_cast
    module
  have h0 : (0 : ℂ) ∈ ℓ ⁻¹' U := by simpa [ℓ] using hpU
  have h1 : (1 : ℂ) ∈ ℓ ⁻¹' U := by simpa [ℓ] using hqU
  refine ⟨ℓ '' (ℓ ⁻¹' U ∩ {t | f (ℓ t) ≠ 0}), ?_, ⟨0, ⟨h0, by simpa [ℓ] using hp⟩, by simp [ℓ]⟩,
    ⟨1, ⟨h1, by simpa [ℓ] using hq⟩, by simp [ℓ]⟩, ?_⟩
  · rintro _ ⟨t, ⟨htV, ht⟩, rfl⟩
    exact ⟨htV, ht⟩
  · exact (ManifoldZerosComplementConnected.isPreconnected_inter_ne_zero_of_complex hVo
      hVc.isPreconnected (φ := fun t => f (ℓ t)) (fun t ht => (hf (ℓ t) ht).comp (hℓa t)) h0
      (by simpa [ℓ] using hp)).image ℓ hℓc.continuousOn

theorem ManifoldZerosComplementConnected.proof : ManifoldZerosComplementConnected.Statement := by
  intro σ _ R h hR hreg hh ⟨x₀, hx₀R, hx₀⟩

  have chart : ∀ x ∈ R, ∃ (d : ℕ) (B : Set (Fin d → ℂ)) (W : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen B ∧ Convex ℝ B ∧ IsOpen W ∧ x ∈ W ∧ AnalyticOnNhd ℂ g B ∧ R ∩ W = g '' B := by
    intro x hx
    obtain ⟨-, d, A, O, V, g, hO, hV, hxV, hg, hAg, hRV⟩ := hreg x hx
    have hxO : A x ∈ O := by
      obtain ⟨y, hy, hgy⟩ : x ∈ g '' O := hRV ▸ ⟨hx, hxV⟩
      rw [← hgy, hAg y hy]
      exact hy
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO (A x) hxO
    refine ⟨d, Metric.ball (A x) ε, V ∩ A ⁻¹' Metric.ball (A x) ε, g, Metric.isOpen_ball,
      convex_ball _ _, hV.inter (Metric.isOpen_ball.preimage A.continuous),
      ⟨hxV, Set.mem_preimage.mpr (Metric.mem_ball_self hε)⟩, hg.mono hεO, ?_⟩
    ext z
    constructor
    · rintro ⟨hzR, hzV, hzB⟩
      obtain ⟨y, hy, rfl⟩ : z ∈ g '' O := hRV ▸ ⟨hzR, hzV⟩
      have hAy : A (g y) ∈ Metric.ball (A x) ε := hzB
      rw [hAg y hy] at hAy
      exact ⟨y, hAy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      have hgy : g y ∈ R ∩ V := by rw [hRV]; exact ⟨y, hεO hy, rfl⟩
      refine ⟨hgy.1, hgy.2, ?_⟩
      show A (g y) ∈ Metric.ball (A x) ε
      rw [hAg y (hεO hy)]
      exact hy
  have chartR : ∀ {d : ℕ} {B : Set (Fin d → ℂ)} {W : Set (σ → ℂ)} {g : (Fin d → ℂ) → σ → ℂ},
      R ∩ W = g '' B → ∀ y ∈ B, g y ∈ R := by
    intro d B W g hRW y hy
    have : g y ∈ R ∩ W := by rw [hRW]; exact ⟨y, hy, rfl⟩
    exact this.1

  let T : Set (σ → ℂ) := {x | ∀ᶠ z in 𝓝 x, z ∈ R → h z = 0}
  have hTo : IsOpen T := isOpen_setOfPred_eventually_nhds
  let T₂ : Set (σ → ℂ) := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ ∀ z ∈ W ∩ R, z ∉ T}
  have hT₂o : IsOpen T₂ := isOpen_iff_forall_mem_open.mpr fun x ⟨W, hW, hxW, hWT⟩ =>
    ⟨W, fun y hy => ⟨W, hW, hy, hWT⟩, hW, hxW⟩
  have hcov : R ⊆ T ∪ T₂ := by
    intro x hx
    obtain ⟨d, B, W, g, hBo, hBc, hWo, hxW, hg, hRW⟩ := chart x hx
    have hhg : AnalyticOnNhd ℂ (fun y => h (g y)) B := fun y hy =>
      (hh (g y) (chartR hRW y hy)).comp (hg y hy)
    by_cases hzero : ∃ y ∈ B, ∀ᶠ y' in 𝓝 y, h (g y') = 0
    · obtain ⟨y, hy, hev⟩ := hzero
      have hEq := hhg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hBc.isPreconnected hy hev
      left
      show ∀ᶠ z in 𝓝 x, z ∈ R → h z = 0
      filter_upwards [hWo.mem_nhds hxW] with z hzW hzR
      obtain ⟨y', hy', rfl⟩ : z ∈ g '' B := hRW ▸ ⟨hzR, hzW⟩
      exact hEq hy'
    · right
      refine ⟨W, hWo, hxW, ?_⟩
      rintro z ⟨hzW, hzR⟩ hzT
      obtain ⟨y, hy, rfl⟩ : z ∈ g '' B := hRW ▸ ⟨hzR, hzW⟩
      have hzT' : ∀ᶠ w in 𝓝 (g y), w ∈ R → h w = 0 := hzT
      refine hzero ⟨y, hy, ?_⟩
      filter_upwards [(hg y hy).continuousAt.tendsto.eventually hzT', hBo.mem_nhds hy] with y' h1 h2
      exact h1 (chartR hRW y' h2)

  have hTR : ∀ x ∈ R, ¬ ∀ᶠ z in 𝓝 x, z ∈ R → h z = 0 := by
    intro x hx hxT
    have hx₀T₂ : x₀ ∈ T₂ := by
      rcases hcov hx₀R with h1 | h1
      · exact absurd ((show ∀ᶠ z in 𝓝 x₀, z ∈ R → h z = 0 from h1).self_of_nhds hx₀R) hx₀
      · exact h1
    obtain ⟨y, hyR, hyT, W, -, hyW, hWT⟩ := hR T T₂ hTo hT₂o hcov ⟨x, hx, hxT⟩ ⟨x₀, hx₀R, hx₀T₂⟩
    exact hWT y ⟨hyW, hyR⟩ hyT
  refine ManifoldZerosComplementConnected.isPreconnected_of_local hR sdiff_subset ?_ ?_
  · intro x hx
    rw [mem_closure_iff_frequently]
    exact (Filter.not_eventually.mp (hTR x hx)).mono fun z hz => Classical.not_imp.mp hz
  · intro x hx
    obtain ⟨d, B, W, g, hBo, hBc, hWo, hxW, hg, hRW⟩ := chart x hx
    have hhg : AnalyticOnNhd ℂ (fun y => h (g y)) B := fun y hy =>
      (hh (g y) (chartR hRW y hy)).comp (hg y hy)
    refine ⟨W, hWo, hxW, ?_⟩
    have heq : W ∩ (R \ {z | h z = 0}) = g '' (B ∩ {y | h (g y) ≠ 0}) := by
      ext z
      constructor
      · rintro ⟨hzW, hzR, hz⟩
        obtain ⟨y, hy, rfl⟩ : z ∈ g '' B := hRW ▸ ⟨hzR, hzW⟩
        exact ⟨y, ⟨hy, hz⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
        have hgy : g y ∈ R ∩ W := by rw [hRW]; exact ⟨y, hy, rfl⟩
        exact ⟨hgy.2, hgy.1, hy'⟩
    rw [heq]
    exact (ManifoldZerosComplementConnected.isPreconnected_convex_inter_ne_zero hBo hBc hhg).image g
      (hg.continuousOn.mono inter_subset_left)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionsContainOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

theorem FiniteProjectionsContainOpen.proof (h₁ : ConeAvoidsFinite.Statement)
    (h₂ : FiniteProjHomInjective.Statement) (h₃ : ConeAvoidsOpen.Statement)
    (h₄ : ConeAvoidsExists.Statement) : FiniteProjectionsContainOpen.Statement := by
  intro n d J hJ hd
  obtain ⟨A₀, N, hA₀⟩ := h₄ n d J hJ hd
  refine ⟨{A | ConeAvoids J A N}, h₃ n d N J, ⟨A₀, hA₀⟩, fun A hA => ?_⟩
  have hfin : (projHom J A).toRingHom.Finite := h₁ n d N J A hA
  exact ⟨h₂ n d J A hJ hd hfin, hfin⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
end
