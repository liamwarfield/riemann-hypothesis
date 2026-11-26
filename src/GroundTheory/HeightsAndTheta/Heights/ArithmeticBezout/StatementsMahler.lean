module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartGramMA
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntSphere
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

def nrmGroups (h : HermNorm n) (k : ℕ) (u : Fin k × Fin n → ℂ) : Fin k × Fin n → ℂ :=
  fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij

def consGroup {k : ℕ} (v : Fin n → ℂ) (w : Fin k × Fin n → ℂ) : Fin (k + 1) × Fin n → ℂ :=
  fun ij => Fin.cases (motive := fun _ => ℂ) (v ij.2) (fun i => w (i, ij.2)) ij.1

def IsAdmissible (Z : ProjCycle ℂ n) (u : Fin n → ℂ) : Prop :=
  ∀ W ∈ Z.support, linForm u ∉ W

def mahlerDefect (h : HermNorm n) (e : ℕ) (Z : ProjCycle ℂ n)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ) : ℝ :=
  mahler h e (specFirst f u) - cycleIntegral h Z e (fsLog h u)

structure IsChowCycleData (Z : ProjCycle ℂ n) (e δ : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :
    Prop where

  prime : ∀ W ∈ Z.support, IsProjPrime W

  chow : IsChowFormCycle Z (e + 1) f

  homog : IsMultiHomog δ f

def MahlerSectionDim (e : ℕ) : Prop :=
  ∀ (n δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (u : Fin n → ℂ), IsChowCycleData Z e δ f → IsAdmissible Z u →
      mahler h e (specFirst f u) =
        mahler h (e + 1) f + δ * (harmonic (n - 1) : ℝ) / 2 + cycleIntegral h Z e (fsLog h u)

def DefectConstDim (e : ℕ) : Prop :=
  ∀ (n δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (u u' : Fin n → ℂ), IsChowCycleData Z e δ f → IsAdmissible Z u → IsAdmissible Z u' →
      mahlerDefect h e Z f u = mahlerDefect h e Z f u'

def MahlerSectionOfConst.Statement : Prop :=
  ∀ e : ℕ, DefectConstDim e → MahlerSectionDim e

def DefectAverage.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsChowCycleData Z e δ f →
      IntegrableOn (fun v => mahlerDefect h e Z f (nrmv h v)) (ballH h) ∧
        ⨍ v in ballH h, mahlerDefect h e Z f (nrmv h v) = mahler h (e + 1) f + δ * (harmonic (n - 1) : ℝ) / 2

def AdmissibleAE.Statement : Prop :=
  ∀ (n : ℕ) (Z : ProjCycle ℂ n), (∀ W ∈ Z.support, IsRelevant W) → ∀ᵐ u : Fin n → ℂ, IsAdmissible Z u

def AdmissibleAENrm.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n), (∀ W ∈ Z.support, IsRelevant W) →
    ∀ᵐ v ∂(volume.restrict (ballH h)), IsAdmissible Z (nrmv h v)

def BallVolume.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n), 0 < volume (ballH h) ∧ volume (ballH h) < ⊤

def MahlerAverageSplit.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), f ≠ 0 → IsMultiHomog δ f →
    IntegrableOn (fun v => mahler h e (specFirst f (nrmv h v))) (ballH h) ∧
      mahler h (e + 1) f = ⨍ v in ballH h, mahler h e (specFirst f (nrmv h v))

def MahlerIntegrand.Statement : Prop :=
  ∀ (n k δ : ℕ) (h : HermNorm n) (f : MvPolynomial (Fin k × Fin n) ℂ), f ≠ 0 → IsMultiHomog δ f →
    IntegrableOn (fun u => Real.log ‖eval (nrmGroups h k u) f‖) (ballProd h k)

def SphereMeanFubini.Statement : Prop :=
  ∀ (n k : ℕ) (h : HermNorm n) (G : (Fin (k + 1) × Fin n → ℂ) → ℝ),
    IntegrableOn (fun u => G (nrmGroups h (k + 1) u)) (ballProd h (k + 1)) →
      IntegrableOn (fun v => sphereMean h k (fun w => G (consGroup (nrmv h v) w))) (ballH h) ∧
        sphereMean h (k + 1) G = ⨍ v in ballH h, sphereMean h k (fun w => G (consGroup (nrmv h v) w))

def EvalSpecFirst.Statement : Prop :=
  ∀ (n k : ℕ) (f : MvPolynomial (Fin (k + 1) × Fin n) ℂ) (v : Fin n → ℂ) (w : Fin k × Fin n → ℂ),
    eval w (specFirst f v) = eval (consGroup v w) f

def CycleAverage.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsChowCycleData Z e δ f →
      IntegrableOn (fun v => cycleIntegral h Z e (fsLog h (nrmv h v))) (ballH h) ∧
        ⨍ v in ballH h, cycleIntegral h Z e (fsLog h (nrmv h v)) = -(δ * (harmonic (n - 1) : ℝ)) / 2

def ConeAverage.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) g → IsMultiHomog δ g →
      IntegrableOn (fun v => coneIntegral h W e (fsLog h (nrmv h v))) (ballH h) ∧
        ⨍ v in ballH h, coneIntegral h W e (fsLog h (nrmv h v)) = -(δ * (harmonic (n - 1) : ℝ)) / 2

def ConeFubini.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (μ : Measure (EuclideanSpace ℂ (Fin n))) [IsFiniteMeasure μ]
    (F : (Fin n → ℂ) → EuclideanSpace ℂ (Fin n) → ℝ) (c M : ℝ),
    Measurable (Function.uncurry F) →
    (∀ᵐ y ∂μ, IntegrableOn (fun v => F v y) (ballH h) ∧ ∫ v in ballH h, |F v y| ≤ M ∧
      ⨍ v in ballH h, F v y = c) →
      IntegrableOn (fun v => ∫ y, F v y ∂μ) (ballH h) ∧
        ⨍ v in ballH h, ∫ y, F v y ∂μ = c * (μ Set.univ).toReal

def FsLogAverage.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)), y ≠ 0 →
    IntegrableOn (fun v => fsLog h (nrmv h v) (h.pointOf y)) (ballH h) ∧
      ∫ v in ballH h, |fsLog h (nrmv h v) (h.pointOf y)| =
        (harmonic (n - 1) : ℝ) / 2 * (volume (ballH h)).toReal ∧
      ⨍ v in ballH h, fsLog h (nrmv h v) (h.pointOf y) = -(harmonic (n - 1) : ℝ) / 2

def FsLogPointOf.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (v : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)),
    fsLog h (nrmv h v) (h.pointOf y) =
      fsLog (HermNorm.std n) (nrmv (HermNorm.std n) (h.mat *ᵥ v)) (fun i => y i)

def BallAverageLinear.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (φ : (Fin n → ℂ) → ℝ),
    (IntegrableOn (fun v => φ (h.mat *ᵥ v)) (ballH h) ↔ IntegrableOn φ (ballH (HermNorm.std n))) ∧
      ⨍ v in ballH h, φ (h.mat *ᵥ v) = ⨍ w in ballH (HermNorm.std n), φ w

def SphereMeanLinearBall.Statement : Prop :=
  ∀ (n : ℕ) (y : Fin n → ℂ), y ≠ 0 →
    IntegrableOn (fun w => fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y) (ballH (HermNorm.std n)) ∧
      (∀ w, fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y ≤ 0) ∧
      ⨍ w in ballH (HermNorm.std n), fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y =
        -(harmonic (n - 1) : ℝ) / 2

def FsLogMeasurable.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n),
    Measurable (fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => fsLog h (nrmv h p.1) (h.pointOf p.2))

def ChowDegreePos.Statement : Prop :=
  ∀ (n k δ : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin k × Fin n) ℂ),
    0 < k → IsProjPrime W → IsChowForm W k g → IsMultiHomog δ g → 1 ≤ δ

def SpecFirstHomog.Statement : Prop :=
  ∀ (n k δ : ℕ) (f : MvPolynomial (Fin (k + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsMultiHomog δ f → IsMultiHomog δ (specFirst f u)

def ChowFormAssoc.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (g g' : MvPolynomial (Fin k × Fin n) F), IsChowForm I k g → IsChowForm I k g' →
      ∃ c : F, c ≠ 0 ∧ g' = C c * g

def ChowFormCycleAdd.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Z₁ Z₂ : ProjCycle F n) (f₁ f₂ : MvPolynomial (Fin k × Fin n) F),
    IsChowFormCycle Z₁ k f₁ → IsChowFormCycle Z₂ k f₂ → IsChowFormCycle (Z₁ + Z₂) k (f₁ * f₂)

def ChowFormCycleSmul.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k m : ℕ) (Z : ProjCycle F n) (f : MvPolynomial (Fin k × Fin n) F),
    IsChowFormCycle Z k f → IsChowFormCycle (m • Z) k (f ^ m)

namespace MahlerInhabit

end MahlerInhabit

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

noncomputable section

def zeroExt (m k : ℕ) : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin (m + k)) where
  toFun x := WithLp.toLp 2 (Fin.append (fun i => x i) 0)
  map_add' x y := by
    ext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
  map_smul' c x := by
    ext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp

theorem norm_zeroExt (m k : ℕ) (x : EuclideanSpace ℂ (Fin m)) : ‖zeroExt m k x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, zeroExt, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.sum_univ_add]
  simp

theorem isometry_zeroExt (m k : ℕ) : Isometry (zeroExt m k) :=
  AddMonoidHomClass.isometry_of_norm (zeroExt m k) (norm_zeroExt m k)

theorem coordBall_mass {n m : ℕ} (hmn : m ≤ n) :
    0 < Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0} ∧
      Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0} < ⊤ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hset : {y : EuclideanSpace ℂ (Fin (m + k)) | ‖y‖ < 1 ∧ ∀ j : Fin (m + k), m ≤ (j : ℕ) → y j = 0} =
      zeroExt m k '' Metric.ball 0 1 := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_image, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨hy, hz⟩
      refine ⟨WithLp.toLp 2 fun i => y (Fin.castAdd k i), ?_, ?_⟩
      · rw [← norm_zeroExt m k]
        convert hy using 2
        ext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp [zeroExt]
        · simp [zeroExt, hz (Fin.natAdd m i) (by simp)]
      · ext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp [zeroExt]
        · simp [zeroExt, hz (Fin.natAdd m i) (by simp)]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨by rwa [norm_zeroExt], fun j hj => ?_⟩
      revert hj
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · intro hi
        simp at hi
        omega
      · intro _
        simp [zeroExt]
  rw [hset, (isometry_zeroExt m k).hausdorffMeasure_image (Or.inl (by positivity))]
  have hd : ((2 * m : ℕ) : ℝ) = (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  rw [hd]
  exact ⟨Metric.measure_ball_pos _ _ one_pos, measure_ball_lt_top⟩

def linProjₗ {m n : ℕ} (π : Fin m → Fin n → ℂ) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) where
  toFun := linProj π
  map_add' x y := by
    ext i
    simp [linProj, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i
    simp [linProj, Finset.mul_sum, mul_left_comm]

theorem ae_fibreCount_eq_zero {n m : ℕ} (hnm : n < m) (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (π : Fin m → Fin n → ℂ) :
    ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w = 0 := by
  set R := (LinearMap.range (linProjₗ π)).restrictScalars ℝ
  have hR : R ≠ ⊤ := by
    intro hT
    rw [Submodule.restrictScalars_eq_top_iff] at hT
    have h1 := LinearMap.finrank_range_le (linProjₗ π)
    rw [hT, finrank_top, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at h1
    omega
  have h0 : volume (R : Set (EuclideanSpace ℂ (Fin m))) = 0 := Measure.addHaar_submodule _ R hR
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with w hw
  rw [fibreCount, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro y ⟨-, rfl⟩
  exact hw ⟨y, rfl⟩

theorem ConeIntegralMass.proof (hF : ConeFibreDegree.Statement) (hM : ConeMassOfFibre.Statement) :
    ConeIntegralMass.Statement := by
  intro n e δ h W f hW hf hδ
  have hfib := hF n e δ h W f hW hf hδ
  have hmass := hM n (e + 1) δ h W hW hfib
  unfold coneIntegral
  simp only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  rw [hmass]
  by_cases hn : e + 1 ≤ n
  · obtain ⟨hpos, hfin⟩ := coordBall_mass hn
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_div_assoc,
      div_self (ENNReal.toReal_pos hpos.ne' hfin.ne).ne', mul_one]
  · have hδ0 : δ = 0 := by
      have : (volume : Measure (Fin (e + 1) → Fin n → ℂ)).IsAddHaarMeasure :=
        Measure.pi.isAddHaarMeasure _
      have : (ae (volume : Measure (Fin (e + 1) → Fin n → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
      have : (ae (volume : Measure (EuclideanSpace ℂ (Fin (e + 1))))).NeBot :=
        ae_neBot.2 (NeZero.ne _)
      obtain ⟨π, hπ⟩ := hfib.exists
      obtain ⟨w, hw1, hw2⟩ := (hπ.and (ae_fibreCount_eq_zero (by omega) h W π)).exists
      rw [hw1] at hw2
      exact_mod_cast hw2
    simp [hδ0]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

section Lemmas

variable {R : Type*} [CommRing R]

theorem IsWeightedHomogeneous.bind₁ {σ τ : Type*} {w : σ → ℕ} {w' : τ → ℕ} {f : MvPolynomial σ R}
    {m : ℕ} (hf : IsWeightedHomogeneous w f m) (φ : σ → MvPolynomial τ R)
    (hφ : ∀ x, IsWeightedHomogeneous w' (φ x) (w x)) :
    IsWeightedHomogeneous w' (bind₁ φ f) m := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro d hd
  rw [bind₁_monomial]
  have hw : Finsupp.weight w d = m := hf (mem_support_iff.mp hd)
  have h1 : IsWeightedHomogeneous w' (∏ x ∈ d.support, φ x ^ d x) (∑ x ∈ d.support, d x * w x) :=
    IsWeightedHomogeneous.prod _ _ _ fun x _ => by
      simpa [mul_comm] using (hφ x).pow (d x)
  have h2 := h1.C_mul (AddMonoidAlgebra.coeff f d)
  convert h2 using 1
  rw [← hw, Finsupp.weight_apply, Finsupp.sum]
  simp [smul_eq_mul]

variable {k n : ℕ}

theorem IsMultiHomog.specFirst {δ : ℕ} {f : MvPolynomial (Fin (k + 1) × Fin n) R}
    (hf : IsMultiHomog δ f) (u : Fin n → R) : IsMultiHomog δ (specFirst f u) := by
  rw [isMultiHomog_iff] at hf ⊢
  intro i
  refine IsWeightedHomogeneous.bind₁ (hf i.succ) _ fun x => ?_
  obtain ⟨a, j⟩ := x
  induction a using Fin.cases with
  | zero =>
    have : inGroup (n := n) i.succ ((0 : Fin (k + 1)), j) = 0 := by
      simp [inGroup, (Fin.succ_ne_zero i).symm]
    rw [this]
    exact isWeightedHomogeneous_C _ _
  | succ a =>
    have : inGroup (n := n) i.succ (a.succ, j) = inGroup (n := n) i (a, j) := by
      simp [inGroup, Fin.succ_inj]
    rw [this]
    exact isWeightedHomogeneous_X R _ (a, j)

theorem IsWeightedHomogeneous.map' {σ S : Type*} [CommSemiring S] {w : σ → ℕ} {f : MvPolynomial σ R}
    {m : ℕ} (hf : IsWeightedHomogeneous w f m) (φ : R →+* S) :
    IsWeightedHomogeneous w (MvPolynomial.map φ f) m := by
  intro d hd
  rw [coeff_map] at hd
  exact hf fun h => hd (by rw [h, map_zero])

end Lemmas

section Components

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type*} [CommRing R] {n : ℕ}

theorem isHomogIdeal_iff (I : Ideal (MvPolynomial (Fin n) R)) :
    IsHomogIdeal I ↔ I.IsHomogeneous (homogeneousSubmodule (Fin n) R) := by
  constructor
  · intro h i r hr
    have := h r hr i
    rwa [← decomposition.decompose'_apply] at this
  · intro h f hf d
    exact homogeneousComponent_mem_of_mem h hf d

theorem isHomogIdeal_sup_span_linForm {I : Ideal (MvPolynomial (Fin n) R)} (hI : IsHomogIdeal I)
    (u : Fin n → R) : IsHomogIdeal (I ⊔ Ideal.span {linForm u}) := by
  rw [isHomogIdeal_iff] at hI ⊢
  refine hI.sup (Ideal.homogeneous_span _ _ fun x hx => ?_)
  rw [Set.mem_singleton_iff] at hx
  subst hx
  refine ⟨1, ?_⟩
  rw [mem_homogeneousSubmodule]
  exact IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _

variable [IsNoetherianRing R]

theorem isProjPrime_of_mem_support_fundCycle {J : Ideal (MvPolynomial (Fin n) R)} (hJ : IsHomogIdeal J)
    {W : Ideal (MvPolynomial (Fin n) R)} (hW : W ∈ (fundCycle J).support) : IsProjPrime W := by
  classical
  have hval : (fundCycle J) W ≠ 0 := Finsupp.mem_support_iff.mp hW
  have hrel : W ∈ relComps J := by
    by_contra h
    apply hval
    unfold fundCycle
    rw [Finsupp.onFinset_apply, if_neg h]
  obtain ⟨hmin, hW'⟩ := hrel
  have hprime : W.IsPrime := hmin.1.1
  have hJh := (isHomogIdeal_iff J).mp hJ
  refine ⟨hprime, (isHomogIdeal_iff W).mpr ?_, hW'⟩
  set core := (W.homogeneousCore (homogeneousSubmodule (Fin n) R)).toIdeal
  have hcore_prime : core.IsPrime := hprime.homogeneousCore
  have hJcore : J ≤ core := by
    rw [← hJh.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hmin.1.2
  have hle : core ≤ W := Ideal.toIdeal_homogeneousCore_le _ _
  have heq : core = W := le_antisymm hle (hmin.2 ⟨hcore_prime, hJcore⟩ hle)
  rw [Ideal.IsHomogeneous.iff_eq]
  exact heq

end Components

section Height

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem chowHt_zero_groups (H : ArchData K n) (δ : ℕ) (g : MvPolynomial (Fin 0 × Fin n) K) :
    chowHt H 0 δ g = chowHt H 0 0 g := by
  simp [chowHt]

theorem chowHt_zero_groups_eq_zero (H : ArchData K n) (δ : ℕ) {g : MvPolynomial (Fin 0 × Fin n) K}
    (hg : g ≠ 0) : chowHt H 0 δ g = 0 := by
  rw [chowHt_zero_groups, eq_C_of_isEmpty g]
  rw [eq_C_of_isEmpty g] at hg
  exact chowHeightConst K n 0 H _ fun h => hg (by rw [h, map_zero])

theorem chowHt_pow (hMul : ChowHeightMul.Statement) (H : ArchData K n) {k : ℕ} (d : ℕ)
    {g : MvPolynomial (Fin k × Fin n) K} (hg : g ≠ 0) (m : ℕ) :
    chowHt H k (m * d) (g ^ m) = m * chowHt H k d g := by
  induction m with
  | zero =>
    rw [zero_mul, pow_zero, Nat.cast_zero, zero_mul, ← C_1]
    exact chowHeightConst K n k H 1 one_ne_zero
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul, hMul K n H k _ _ _ _ (pow_ne_zero _ hg) hg, ih]
    push_cast
    ring

theorem chowHt_C_mul_prod (hMul : ChowHeightMul.Statement) (H : ArchData K n) {k : ℕ} {ι : Type*}
    (s : Finset ι) (m d : ι → ℕ) (g : ι → MvPolynomial (Fin k × Fin n) K) (hg : ∀ i ∈ s, g i ≠ 0)
    {c : K} (hc : c ≠ 0) :
    chowHt H k (∑ i ∈ s, m i * d i) (C c * ∏ i ∈ s, g i ^ m i) =
      ∑ i ∈ s, (m i : ℝ) * chowHt H k (d i) (g i) := by
  classical
  have hP : ∀ t ⊆ s, ∏ i ∈ t, g i ^ m i ≠ 0 := fun t ht =>
    Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hg i (ht hi))
  have hprod : ∀ t ⊆ s, chowHt H k (∑ i ∈ t, m i * d i) (∏ i ∈ t, g i ^ m i) =
      ∑ i ∈ t, (m i : ℝ) * chowHt H k (d i) (g i) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.sum_empty, Finset.prod_empty, Finset.sum_empty, ← C_1]
      exact chowHeightConst K n k H 1 one_ne_zero
    | insert a t ha ih =>
      intro hts
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
        hMul K n H k _ _ _ _ (pow_ne_zero _ (hg a (hts (Finset.mem_insert_self a t))))
          (hP t (fun x hx => hts (Finset.mem_insert_of_mem hx))),
        chowHt_pow hMul H _ (hg a (hts (Finset.mem_insert_self a t))),
        ih (fun x hx => hts (Finset.mem_insert_of_mem hx))]
  have := hMul K n H k 0 (∑ i ∈ s, m i * d i) (C c) _ (C_ne_zero.mpr hc) (hP s le_rfl)
  rw [zero_add] at this
  rw [this, chowHeightConst K n k H c hc, zero_add, hprod s le_rfl]



end Height


end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set MvPolynomial

noncomputable section

namespace LogInt

variable {n k : ℕ}

def ballSet (h : HermNorm n) (k : ℕ) : Set (Fin k × Fin n → ℂ) :=
  {u | ∀ i, h.norm (fun j => u (i, j)) < 1}

theorem measurableSet_ballSet (h : HermNorm n) : MeasurableSet (ballSet h k) := by
  have e : ballSet h k = ⋂ i, {u : Fin k × Fin n → ℂ | h.norm (fun j => u (i, j)) < 1} := by
    ext u; simp [ballSet]
  rw [e]
  exact MeasurableSet.iInter fun i => measurableSet_lt (measurable_groupNorm h i) measurable_const

theorem ballSet_subset_polydisc (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) :
    ballSet h k ⊆ polydisc _ C := by
  intro u hu
  simp only [polydisc, mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  intro ij
  exact (hC (fun j => u (ij.1, j)) ij.2).trans (mul_le_of_le_one_right hC0 (hu ij.1).le)

theorem normT_univ (h : HermNorm n) (u : Fin k × Fin n → ℂ) :
    normT h Finset.univ u = fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij := by
  funext ij
  simp [normT]

theorem integrableOn_log_mahler (h : HermNorm n) (f : MvPolynomial (Fin k × Fin n) ℂ) (hf : f ≠ 0) :
    IntegrableOn (fun u : Fin k × Fin n → ℂ =>
        Real.log ‖eval (fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij) f‖)
        (ballSet h k) ∧
      ∀ᵐ u ∂(volume.restrict (ballSet h k)),
        eval (fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij) f ≠ 0 := by
  obtain ⟨C, hC0, hC⟩ := h.li_exists_coord_le
  obtain ⟨h1, h2⟩ := logNormT h C hC0 hC Finset.univ f hf
  simp only [normT_univ] at h1 h2
  exact ⟨h1.mono_set (ballSet_subset_polydisc h C hC0 hC),
    ae_restrict_of_ae_restrict_of_subset (ballSet_subset_polydisc h C hC0 hC) h2⟩

end LogInt

theorem mahlerMul : MahlerMul.Statement := by
  intro n k h f g hf hg
  obtain ⟨i1, z1⟩ := LogInt.integrableOn_log_mahler h f hf
  obtain ⟨i2, z2⟩ := LogInt.integrableOn_log_mahler h g hg
  unfold mahler sphereMean
  change ⨍ u in LogInt.ballSet h k, _ = (⨍ u in LogInt.ballSet h k, _) + ⨍ u in LogInt.ballSet h k, _
  rw [setAverage_eq, setAverage_eq, setAverage_eq, ← smul_add, ← integral_add i1 i2]
  congr 1
  refine setIntegral_congr_ae (LogInt.measurableSet_ballSet h) ?_
  have := (ae_restrict_iff' (LogInt.measurableSet_ballSet h)).mp (z1.and z2)
  filter_upwards [this] with u hu hB
  obtain ⟨h1, h2⟩ := hu hB
  rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2)]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMapArea
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

theorem ConeMapArea.proof (h : ConeMapAreaOne.Statement) : ConeMapArea.Statement := by
  intro n e ι _ U D v F hUD hinj hF
  let g : ι → (Fin e → ℂ) × ℂ → EuclideanSpace ℂ (Fin n) := fun i q => q.2 • WithLp.toLp 2 (v i q.1)
  let S : ι → Set ((Fin e → ℂ) × ℂ) := fun i => {q | q.1 ∈ D i ∧ q.2 ≠ 0}
  have himg : (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
      {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0} = ⋃ i, g i '' S i := by
    ext y
    simp only [Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨i, x, t⟩, hq, rfl⟩
      exact ⟨i, (x, t), hq, rfl⟩
    · rintro ⟨i, ⟨x, t⟩, hq, rfl⟩
      exact ⟨(i, x, t), hq, rfl⟩
  have hinj_i : ∀ i, Set.InjOn (g i) (S i) := by
    intro i p hp p' hp' hpp
    exact (Prod.ext_iff.1 (@hinj (i, p) hp (i, p') hp' hpp)).2
  have hdisj : Pairwise (Function.onFun Disjoint fun i => g i '' S i) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro y ⟨p, hp, rfl⟩ ⟨p', hp', hpp⟩
    exact hij (congrArg Prod.fst (@hinj (j, p') hp' (i, p) hp hpp)).symm
  have hmeas : ∀ i, MeasurableSet (g i '' S i) := by
    intro i
    obtain ⟨-, hD, hDU, hv⟩ := hUD i
    refine MeasurableSet.image_of_continuousOn_injOn ?_ ?_ (hinj_i i)
    · exact (measurable_fst hD).inter (measurable_snd (measurableSet_singleton (0 : ℂ)).compl)
    · have hc : ContinuousOn (fun q : (Fin e → ℂ) × ℂ => WithLp.toLp 2 (v i q.1)) (S i) :=
        (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp_continuousOn
          ((hv.continuousOn.mono hDU).comp continuousOn_fst fun q hq => hq.1)
      exact continuousOn_snd.smul hc
  rw [himg, lintegral_iUnion hmeas hdisj, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun i => ?_
  obtain ⟨hU, hD, hDU, hv⟩ := hUD i
  exact h n e (U i) (D i) (v i) F hU hD hDU hv (hinj_i i) hF

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PThroughTwoPointsTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ThroughTwoPointsTrdeg.proof (hT : TrdegAdjoinLe.Statement) : ThroughTwoPointsTrdeg.Statement := by
  intro K Ω _ _ n k _ _ _ hinj x c hcx y j hyj hprop hy
  let u : Fin k × Fin n → Ω := fun im => algebraMap (MvPolynomial (Fin k × Fin n) K) Ω (X im)
  let z : Fin n → Ω := fun m => y m * (y j)⁻¹
  let x' : Fin n → Ω := fun m => algebraMap K Ω (x m)
  let c' : Fin n → Ω := fun m => algebraMap K Ω (c m)
  let s : Fin k → Ω := fun i => ∑ l, u (i, l) * x' l
  have hC : ∀ a : K, algebraMap (MvPolynomial (Fin k × Fin n) K) Ω (C a) = algebraMap K Ω a := fun a => by
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin k × Fin n) K) Ω, MvPolynomial.algebraMap_eq]

  have heq : ∀ i, ∑ m, u (i, m) * z m = s i * ∑ m, c' m * z m := by
    intro i
    have h := hy i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [genSubst, map_sub, map_mul, map_sum, hC] at h
    have h' : ∑ m, u (i, m) * y m = s i * ∑ m, c' m * y m := by
      rw [← sub_eq_zero, Finset.mul_sum, ← Finset.sum_sub_distrib, ← h]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [u, s, x', c']
      ring
    simp only [z, ← mul_assoc, ← Finset.sum_mul]
    rw [h']

  obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hcx
  have hx'p : x' p ≠ 0 := by simpa [x'] using hp
  obtain ⟨q, hD⟩ : ∃ q, x' p * z q - x' q * z p ≠ 0 := by
    by_contra h
    push Not at h
    apply hprop (y j * (z p * (x' p)⁻¹))
    funext m
    have hm := h m
    simp only [z, x'] at hm hx'p ⊢
    have hm2 : (algebraMap K Ω (x p) * y m - algebraMap K Ω (x m) * y p) * (y j)⁻¹ = 0 := by
      rw [← hm]; ring
    have hm3 := (mul_eq_zero.1 hm2).resolve_right (inv_ne_zero hyj)
    have e : y j * (y p * (y j)⁻¹ * (algebraMap K Ω (x p))⁻¹) * algebraMap K Ω (x m) =
        y p * algebraMap K Ω (x m) * (algebraMap K Ω (x p))⁻¹ := by
      rw [show y j * (y p * (y j)⁻¹ * (algebraMap K Ω (x p))⁻¹) * algebraMap K Ω (x m) =
        (y j * (y j)⁻¹) * (y p * algebraMap K Ω (x m)) * (algebraMap K Ω (x p))⁻¹ by ring,
        mul_inv_cancel₀ hyj, one_mul]
    rw [e, eq_mul_inv_iff_mul_eq₀ hx'p]
    linear_combination hm3
  set D := x' p * z q - x' q * z p with hDdef
  have hqp : q ≠ p := by
    rintro rfl
    exact hD (by simp [D])
  let E := (Finset.univ.erase p).erase q
  have hqE : q ∈ Finset.univ.erase p := Finset.mem_erase.2 ⟨hqp, Finset.mem_univ q⟩
  have hsplit : ∀ g : Fin n → Ω, ∑ m, g m = g p + g q + ∑ m ∈ E, g m := fun g => by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ hqE, add_assoc]

  let t : Fin k ⊕ (Fin k × E) → Ω := fun a => Sum.elim s (fun b => u (b.1, b.2.1)) a
  let B := Algebra.adjoin K (Set.range z ∪ Set.range t)
  have hzB : ∀ m, z m ∈ B := fun m => Algebra.subset_adjoin (Or.inl ⟨m, rfl⟩)
  have hsB : ∀ i, s i ∈ B := fun i => Algebra.subset_adjoin (Or.inr ⟨Sum.inl i, rfl⟩)
  have huB : ∀ i, ∀ m ∈ E, u (i, m) ∈ B := fun i m hm =>
    Algebra.subset_adjoin (Or.inr ⟨Sum.inr (i, ⟨m, hm⟩), rfl⟩)
  have hKB : ∀ a : K, algebraMap K Ω a ∈ B := fun a => B.algebraMap_mem a
  have hczB : ∑ m, c' m * z m ∈ B := B.sum_mem fun m _ => B.mul_mem (hKB _) (hzB m)
  have hDB : D ∈ B := B.sub_mem (B.mul_mem (hKB _) (hzB q)) (B.mul_mem (hKB _) (hzB p))
  have halg : ∀ v, D * v ∈ B → IsAlgebraic B v := fun v hv =>
    IsAlgebraic.of_mul (y := D) (mem_nonZeroDivisors_of_ne_zero hD)
      (isAlgebraic_algebraMap (⟨D, hDB⟩ : B)) (isAlgebraic_algebraMap (⟨D * v, hv⟩ : B))
  have hw : ∀ im, IsAlgebraic B (u im) := by
    rintro ⟨i, m⟩
    have hSx : ∑ m ∈ E, u (i, m) * x' m ∈ B :=
      B.sum_mem fun m hm => B.mul_mem (huB i m hm) (hKB _)
    have hSz : ∑ m ∈ E, u (i, m) * z m ∈ B :=
      B.sum_mem fun m hm => B.mul_mem (huB i m hm) (hzB m)
    have e1 := hsplit (fun m => u (i, m) * x' m)
    have e2 := hsplit (fun m => u (i, m) * z m)
    rw [heq i] at e2
    change s i = _ at e1
    by_cases hmp : m = p
    · subst hmp
      refine halg _ ?_
      have : D * u (i, m) = z q * (s i - ∑ m ∈ E, u (i, m) * x' m) -
          x' q * (s i * ∑ m, c' m * z m - ∑ m ∈ E, u (i, m) * z m) := by
        rw [hDdef]; linear_combination -z q * e1 + x' q * e2
      rw [this]
      exact B.sub_mem (B.mul_mem (hzB q) (B.sub_mem (hsB i) hSx))
        (B.mul_mem (hKB _) (B.sub_mem (B.mul_mem (hsB i) hczB) hSz))
    by_cases hmq : m = q
    · subst hmq
      refine halg _ ?_
      have : D * u (i, m) = x' p * (s i * ∑ m, c' m * z m - ∑ m ∈ E, u (i, m) * z m) -
          z p * (s i - ∑ m ∈ E, u (i, m) * x' m) := by
        rw [hDdef]; linear_combination -x' p * e2 + z p * e1
      rw [this]
      exact B.sub_mem (B.mul_mem (hKB _) (B.sub_mem (B.mul_mem (hsB i) hczB) hSz))
        (B.mul_mem (hzB p) (B.sub_mem (hsB i) hSx))
    exact isAlgebraic_algebraMap
      (⟨u (i, m), huB i m (Finset.mem_erase.2 ⟨hmq, Finset.mem_erase.2 ⟨hmp, Finset.mem_univ m⟩⟩)⟩ : B)
  have hle := hT K Ω (Set.range z) (Fin k ⊕ (Fin k × E)) t (Fin k × Fin n) u hw

  have hadj : Algebra.adjoin K (Set.range u) = (IsScalarTower.toAlgHom K (MvPolynomial (Fin k × Fin n) K) Ω).range := by
    rw [← Algebra.map_top, ← MvPolynomial.adjoin_range_X, AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  have hinj' : Function.Injective (IsScalarTower.toAlgHom K (MvPolynomial (Fin k × Fin n) K) Ω) := hinj
  have htr : Algebra.trdeg K (Algebra.adjoin K (Set.range u)) = ((k * n : ℕ) : Cardinal) := by
    rw [hadj, ← (AlgEquiv.ofInjective _ hinj').trdeg_eq, MvPolynomial.trdeg_of_isDomain]
    simp
  have hcard : Fintype.card (Fin k ⊕ (Fin k × E)) = k + k * (n - 2) := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
      Finset.card_erase_of_mem hqE, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ,
      Fintype.card_fin]
    rfl
  rw [htr, hcard] at hle
  have hn : 2 ≤ n := by
    have := Fin.val_ne_of_ne hqp
    omega
  rcases lt_or_ge (Algebra.trdeg K (Algebra.adjoin K (Set.range z))) Cardinal.aleph0 with hfin | hinf
  · obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.1 hfin
    rw [hd] at hle ⊢
    norm_cast at hle ⊢
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [Nat.add_sub_cancel_left] at hle
    nlinarith
  · exact (Cardinal.natCast_lt_aleph0 (n := k)).le.trans hinf

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartNormSep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormOfDividedFormSep.Statement : Prop :=
  ∀ (O B : Type) [CommRing O] [IsDomain O] [Infinite O] [CommRing B] [IsDomain B] [Algebra O B]
    [Module.Free O B] [Module.Finite O B] (n : ℕ) (η : Fin n → B) (t : Fin n → O)
    (P : MvPolynomial (Fin n) O),
    (letI := FractionRing.liftAlgebra O (FractionRing B)
     Algebra.IsSeparable (FractionRing O) (FractionRing B)) →
    Algebra.adjoin O (Set.range η) = ⊤ → ∑ m, t m • η m = 1 → Prime P →
      (∑ m, X m * C (η m)) ∣ map (algebraMap O B) P →
        ∀ u : Fin n → O,
          eval u P = eval t P * LinearMap.det (LinearMap.mulLeft O (∑ m, u m • η m))

def ChartFracSeparable.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime] (K L : Type) [Field K] [Field L]
    [Algebra (Localization.AtPrime p) K] [IsFractionRing (Localization.AtPrime p) K]
    [Algebra (ChartLoc I t e p) L] [IsFractionRing (ChartLoc I t e p) L] [Algebra K L]
    [Algebra (Localization.AtPrime p) L] [IsScalarTower (Localization.AtPrime p) K L]
    [IsScalarTower (Localization.AtPrime p) (ChartLoc I t e p) L],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm t ∉ I → Algebra.IsSeparable K L

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjChowNonzero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjChowNonzero.Statement : Prop :=
  ∀ (n e : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → ComplexSets.IsFiniteProjection W A →
      eval (fun j => projPar A (.inr j))
        (Vertical.specRest (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))) f (projPar A)) ≠ 0

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjSecDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjSecDomain.Statement : Prop :=
  ∀ (n e : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    W.IsPrime → ComplexSets.IsFiniteProjection W A →
      IsDomain (Vertical.SecAlg
          (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
          (projPar A)) ∧
        Module.Finite (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
          (Vertical.SecAlg
            (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
            (projPar A))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeFibreAverage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

def matGauss {m n : ℕ} (π : Fin m → Fin n → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-∑ i, ∑ j, ‖π i j‖ ^ 2))

def ConeFibreAverage.Statement : Prop :=
  ∀ n m : ℕ, ∃ K : ℝ≥0∞, 0 < K ∧ K < ⊤ ∧
    ∀ (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J →
      (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
        ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
            ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
          K * Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J}

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionComponents
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def SectionComponents.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (J : Ideal (MvPolynomial (Fin n) F)) (f : MvPolynomial (Fin n) F),
    (∀ P ∈ J.minimalPrimes, ∀ Q ∈ J.minimalPrimes,
      ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ringKrullDim (MvPolynomial (Fin n) F ⧸ Q)) →
    (∀ P ∈ J.minimalPrimes, f ∉ P) →
    ∀ P ∈ J.minimalPrimes, ∀ W : Ideal (MvPolynomial (Fin n) F),
      W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ↔ W ∈ (J ⊔ Ideal.span {f}).minimalPrimes ∧ P ≤ W

end GroundTheory.Heights₂.Heights
end
