module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GenericComplexPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Cardinal

noncomputable section

theorem exists_ringHom_complex_of_charZero (F : Type) [Field F] [CharZero F] (hF : #F ≤ 𝔠) :
    Nonempty (F →+* ℂ) := by
  let M := MvPolynomial ℂ F
  let E := FractionRing M
  let L := AlgebraicClosure E
  have : CharZero M := charZero_of_injective_algebraMap (R := F) (MvPolynomial.C_injective _ _)
  have : CharZero E := charZero_of_injective_algebraMap (R := M) (IsFractionRing.injective M E)
  have : CharZero L := charZero_of_injective_algebraMap (R := E) (algebraMap E L).injective
  have hM : #M ≤ 𝔠 := by
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    rw [mk_complex]
    exact max_le (max_le hF le_rfl) aleph0_le_continuum
  have hE : #E = #M := Cardinal.mk_fractionRing M
  have hL : #L ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max E L).trans (max_le (hE ▸ hM) aleph0_le_continuum)
  have hinj : Function.Injective (fun c : ℂ => algebraMap E L (algebraMap M E (X c))) :=
    (algebraMap E L).injective.comp ((IsFractionRing.injective M E).comp MvPolynomial.X_injective)
  have hLc : #L = #ℂ :=
    le_antisymm (hL.trans_eq mk_complex.symm) (Cardinal.mk_le_of_injective hinj)
  obtain ⟨σ⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (by rw [hLc, mk_complex]; exact aleph0_lt_continuum) (Cardinal.eq.1 hLc)
  exact ⟨σ.toRingHom.comp ((algebraMap E L).comp ((algebraMap M E).comp C))⟩

theorem exists_mcPts_not_mem_mcPts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (hJ : ¬ J ≤ P) :
    ∃ z, z ∈ mcPts P ∧ z ∉ mcPts J := by
  obtain ⟨_, ⟨hprime, -, hrel⟩, hhor, -⟩ := hP
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.mp hJ
  have := hprime
  let Q := MRing ι ⧸ P
  let F := FractionRing Q
  have hQ : Function.Injective (algebraMap ℤ Q) := by
    have e : algebraMap ℤ Q = (Ideal.Quotient.mk P).comp C := RingHom.ext_int _ _
    rw [e, injective_iff_map_eq_zero]
    intro n hn
    have hn0 : (C n : MRing ι) ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hn
    have hn' : n ∈ P.comap (C : ℤ →+* MRing ι) := hn0
    rw [IsHorizontal] at hhor
    rw [hhor] at hn'
    exact (Ideal.mem_bot).mp hn'
  have : CharZero Q := charZero_of_injective_algebraMap hQ
  have : CharZero F := charZero_of_injective_algebraMap (R := Q) (IsFractionRing.injective Q F)
  have hcard : #F ≤ 𝔠 := by
    rw [Cardinal.mk_fractionRing]
    refine (Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := P))).trans ?_
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    exact max_le (max_le (mk_int.le.trans aleph0_le_continuum)
      (Cardinal.mk_le_aleph0.trans aleph0_le_continuum)) aleph0_le_continuum
  obtain ⟨ψ⟩ := exists_ringHom_complex_of_charZero F hcard
  let φ : MRing ι →+* ℂ := (ψ.comp (algebraMap Q F)).comp (Ideal.Quotient.mk P)
  have hker : ∀ f, φ f = 0 ↔ f ∈ P := by
    intro f
    have hi : Function.Injective (ψ.comp (algebraMap Q F)) :=
      ψ.injective.comp (IsFractionRing.injective Q F)
    rw [show φ f = (ψ.comp (algebraMap Q F)) (Ideal.Quotient.mk P f) from rfl,
      map_eq_zero_iff _ hi, Ideal.Quotient.eq_zero_iff_mem]
  let z : (Σ k, ι k) → ℂ := fun p => φ (X p)
  have hev : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = φ f := by
    intro f
    have h : (eval z).comp (map (Int.castRingHom ℂ)) = φ := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · exact RingHom.congr_fun
          (RingHom.ext_int (((eval z).comp (map (Int.castRingHom ℂ))).comp C) (φ.comp C)) r
      · simp [z]
    exact RingHom.congr_fun h f
  refine ⟨z, ⟨fun k => ?_, fun f hf => ?_⟩, fun hz => ?_⟩
  · obtain ⟨i, hi⟩ := hrel k
    exact ⟨i, fun h => hi ((hker _).mp h)⟩
  · rw [hev]
    exact (hker f).mpr hf
  · exact hgP ((hker g).mp (by rw [← hev]; exact hz.2 g hgJ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ComplexConjugate ENNReal ContDiff

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X]

structure HolLineBundle (A : FinHolAtlas D X) where

  g : Fin A.n → Fin A.n → X → ℂ
  holo : ∀ j k, A.HoloOn ((A.chart j).source ∩ (A.chart k).source) (g j k)
  ne_zero : ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, g j k x ≠ 0
  cocycle : ∀ j k l, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source ∩ (A.chart l).source,
    g j l x = g j k x * g k l x

namespace HolLineBundle

variable {A : FinHolAtlas D X} (L : HolLineBundle A)

def sections (n : ℕ) : Submodule ℂ (Fin A.n → X → ℂ) where
  carrier := {f | (∀ j, A.HoloOn (A.chart j).source (f j)) ∧
    (∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, f j x = L.g j k x ^ n * f k x) ∧
    ∀ j, ∀ x ∉ (A.chart j).source, f j x = 0}
  add_mem' := by
    rintro f f' ⟨hf, hc, hz⟩ ⟨hf', hc', hz'⟩
    refine ⟨fun j k => (hf j k).add (hf' j k), fun j k x hx => ?_, fun j x hx => ?_⟩
    · simp only [Pi.add_apply, hc j k x hx, hc' j k x hx]; ring
    · simp [hz j x hx, hz' j x hx]
  zero_mem' := by
    refine ⟨fun j k => ?_, fun j k x _ => by simp, fun j x _ => rfl⟩
    exact analyticOnNhd_const
  smul_mem' := by
    rintro c f ⟨hf, hc, hz⟩
    refine ⟨fun j k => analyticOnNhd_const.mul (hf j k), fun j k x hx => ?_, fun j x hx => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hc j k x hx]; ring
    · simp [hz j x hx]

end HolLineBundle

structure Weight {A : FinHolAtlas D X} (L : HolLineBundle A) where

  φ : Fin A.n → X → ℝ
  smooth : ∀ j, A.SmoothOn (A.chart j).source (φ j)
  compat : ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source,
    φ j x = φ k x + Real.log (‖L.g j k x‖ ^ 2)

namespace Weight

variable {A : FinHolAtlas D X} {L : HolLineBundle A}

def IsSemipositive (W : Weight L) : Prop :=
  ∀ j, ∀ y ∈ (A.chart j).target, ∀ w : Fin D → ℂ, 0 ≤ levi (W.φ j ∘ (A.chart j).symm) y w

def lerp (W₀ W₁ : Weight L) (t : ℝ) : Weight L where
  φ j x := W₀.φ j x + t * (W₁.φ j x - W₀.φ j x)
  smooth j k := (W₀.smooth j k).add (contDiffOn_const.mul ((W₁.smooth j k).sub (W₀.smooth j k)))
  compat j k x hx := by rw [W₀.compat j k x hx, W₁.compat j k x hx]; ring

def diff (W₁ W₀ : Weight L) (x : X) : ℝ :=
  W₁.φ (chartIdx A x) x - W₀.φ (chartIdx A x) x

theorem diff_eq (W₁ W₀ : Weight L) (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    diff W₁ W₀ x = W₁.φ j x - W₀.φ j x := by
  have hi : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  rw [diff, W₁.compat (chartIdx A x) j x ⟨hi, hx⟩, W₀.compat (chartIdx A x) j x ⟨hi, hx⟩]
  ring

end Weight

structure SmoothVolume [MeasurableSpace X] (A : FinHolAtlas D X) where

  μ : Measure X
  isProb : IsProbabilityMeasure μ

  dens : Fin A.n → (Fin D → ℂ) → ℝ
  smooth : ∀ j, ContDiffOn ℝ ∞ (dens j) (A.chart j).target
  pos : ∀ j, ∀ y ∈ (A.chart j).target, 0 < dens j y
  chart_lintegral : ∀ j (g : X → ℝ≥0∞), Measurable g →
    ∫⁻ x in (A.chart j).source, g x ∂μ =
      ∫⁻ y in (A.chart j).target, g ((A.chart j).symm y) * ENNReal.ofReal (dens j y)

variable {A : FinHolAtlas D X} {L : HolLineBundle A}

def ptNormSq (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) : ℝ :=
  ‖s (chartIdx A x) x‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x)

variable [MeasurableSpace X]

def sectionL2NormSq (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (s : Fin A.n → X → ℂ) : ℝ :=
  ∫ x, ptNormSq W n s x ∂dV.μ

def bergman (W : Weight L) (dV : SmoothVolume A) (V : Submodule ℂ (Fin A.n → X → ℂ)) (n : ℕ)
    (x : X) : ℝ :=
  ⨆ s : V, ptNormSq W n (s : Fin A.n → X → ℂ) x / sectionL2NormSq W dV n s

def chernTopDens (W : Weight L) (j : Fin A.n) (y : Fin D → ℂ) : ℝ :=
  (D.factorial : ℝ) * ((((1 / Real.pi : ℝ) : ℂ) • hessC (W.φ j ∘ (A.chart j).symm) y).det).re

def bergmanDens (W : Weight L) (dV : SmoothVolume A) (x : X) : ℝ :=
  chernTopDens W (chartIdx A x) (A.chart (chartIdx A x) x) /
    ((D.factorial : ℝ) * dV.dens (chartIdx A x) (A.chart (chartIdx A x) x))

def gram (W : Weight L) (dV : SmoothVolume A) (n : ℕ) {ι : Type*} (e : ι → Fin A.n → X → ℂ) :
    Matrix ι ι ℂ :=
  Matrix.of fun a b => ∫ x, e a (chartIdx A x) x * conj (e b (chartIdx A x) x) *
    ((Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x) : ℝ) : ℂ) ∂dV.μ

def chiGram (W : Weight L) (dV : SmoothVolume A) (n : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → Fin A.n → X → ℂ) : ℝ :=
  -(1 / 2) * Real.log (gram W dV n e).det.re

end

noncomputable def gaussDiscMass (lam R : ℝ) : ℝ :=
  if lam = 0 then Real.pi * R ^ 2 else Real.pi * (1 - Real.exp (-lam * R ^ 2)) / lam

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDegreePositive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def DegreePositive.Statement : Prop :=
  ∀ (F : Type) [Field F] (ι₀ : Type) [Fintype ι₀] (q : Ideal (MRing (fun _ : Unit => ι₀) F)) (D : ℕ),
    IsMultiProjPrime q →
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    0 < intNum F q (fun _ : Fin D => fun _ => (1 : ℤ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexFormsOnPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ComplexFormsOnPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    P.IsPrime → IsRelevant P →
    ∀ F : MvPolynomial (Σ k, ι k) ℂ, (∀ z ∈ mcPts P, eval z F = 0) →
      F ∈ P.map (MvPolynomial.map (Int.castRingHom ℂ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDegLTGrowth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open GroundTheory.Heights₂.Heights.NumbersDVR

def DegLTGrowth.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (n : ℕ) (g : (K → ℤ) → ℤ), DegLT g n →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |(g (fun k => (a k : ℤ)) : ℝ)| ≤ C * ((∑ k, (a k : ℝ)) + 1) ^ ((n : ℝ) - 1)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEventualPolynomial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def EventualPolynomial.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (n : ℕ) (f : (K → ℤ) → ℤ), DegLT f (n + 1) →
    ∃ (p : MvPolynomial K ℚ) (a₀ : ℕ), p.totalDegree ≤ n ∧
      ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
        (f (fun k => (a k : ℤ)) : ℚ) = MvPolynomial.eval (fun k => (a k : ℚ)) p

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPrimeZariskiDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def PrimeZariskiDense.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (j : MRing ι),
    P.IsPrime → j ∉ P →
    ∀ g : MvPolynomial (Σ k, ι k) ℂ,
      (∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) j) ≠ 0 → eval z g = 0) →
      ∀ z ∈ mcPts P, eval z g = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFiltrationHilbSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u v

def FiltrationHilbSum.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (M : Type v) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    [IsScalarTower F (MRing ι F) M]
    (piece : (K → ℤ) → Submodule F M), IsMultigrading ι M piece →
    ∀ (n : ℕ) (N : Fin (n + 1) → Submodule (MRing ι F) M) (x : Fin n → M) (c : Fin n → K → ℤ)
      (q : Fin n → Ideal (MRing ι F)),
      N 0 = ⊥ → N (Fin.last n) = ⊤ →
      (∀ j : Fin n, x j ∈ piece (c j) ∧
        N j.succ = N j.castSucc ⊔ Submodule.span (MRing ι F) {x j} ∧
        ∀ s : MRing ι F, s • x j ∈ N j.castSucc ↔ s ∈ q j) →
      ∀ m : K → ℤ, (Module.finrank F (piece m) : ℤ) = ∑ j, hilbFn (q j) (m - c j)

section Examples

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

end Examples

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviCompHol
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

theorem LeviCompHol.proof : LeviCompHol.Statement := by
  intro E F _ _ g φ x w hg hφ
  have hgev : ∀ᶠ y in 𝓝 x, AnalyticAt ℂ g y := hg.eventually_analyticAt
  have hfdg : ∀ᶠ y in 𝓝 x, fderiv ℝ g y = (fderiv ℂ g y).restrictScalars ℝ := by
    filter_upwards [hgev] with y hy
    exact hy.differentiableAt.fderiv_restrictScalars ℝ
  have hgC : ContDiffAt ℂ 2 g x := hg.contDiffAt
  have hgR : ContDiffAt ℝ 2 g x := hgC.restrict_scalars ℝ
  have hgd : DifferentiableAt ℝ g x := hgR.differentiableAt (by norm_num)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hgR.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hGw : ∀ v, fderiv ℝ g x v = fderiv ℂ g x v := fun v => by rw [hfdg.self_of_nhds]; rfl
  have hGI : ∀ v, fderiv ℝ g x (Complex.I • v) = Complex.I • fderiv ℝ g x v := fun v => by
    rw [hGw, hGw]; exact (fderiv ℂ g x).map_smul _ _

  have hG2I : ∀ u v, fderiv ℝ (fderiv ℝ g) x u (Complex.I • v) =
      Complex.I • fderiv ℝ (fderiv ℝ g) x u v := by
    intro u v
    have hA : HasFDerivAt (fun y => fderiv ℝ g y (Complex.I • v))
        ((ContinuousLinearMap.apply ℝ (F → ℂ) (Complex.I • v)).comp (fderiv ℝ (fderiv ℝ g) x)) x :=
      (ContinuousLinearMap.apply ℝ (F → ℂ) (Complex.I • v)).hasFDerivAt.comp x hd2.hasFDerivAt
    have hB : HasFDerivAt (fun y => Complex.I • fderiv ℝ g y v)
        (Complex.I • (ContinuousLinearMap.apply ℝ (F → ℂ) v).comp (fderiv ℝ (fderiv ℝ g) x)) x :=
      ((ContinuousLinearMap.apply ℝ (F → ℂ) v).hasFDerivAt.comp x hd2.hasFDerivAt).const_smul Complex.I
    have hAB : (fun y => Complex.I • fderiv ℝ g y v) =ᶠ[𝓝 x] fun y => fderiv ℝ g y (Complex.I • v) := by
      filter_upwards [hfdg] with y hy
      rw [hy]; exact ((fderiv ℂ g y).map_smul _ _).symm
    have h := congrArg (fun L => L u) ((hB.congr_of_eventuallyEq hAB.symm).unique hA)
    simpa using h.symm
  have hsymm : IsSymmSndFDerivAt ℝ g x := hgR.isSymmSndFDerivAt (by simp)
  have hG2II : fderiv ℝ (fderiv ℝ g) x (Complex.I • w) (Complex.I • w) =
      -fderiv ℝ (fderiv ℝ g) x w w := by
    rw [hG2I, hsymm (Complex.I • w) w, hG2I, smul_smul, Complex.I_mul_I, neg_one_smul]
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 φ (g y) :=
    hgd.continuousAt.tendsto.eventually (hφ.eventually (by simp))
  have hfd : fderiv ℝ (fun y => φ (g y)) =ᶠ[𝓝 x]
      fun y => (fderiv ℝ φ (g y)).comp (fderiv ℝ g y) := by
    filter_upwards [hev, hgev] with y hy hy'
    exact fderiv_comp y (hy.differentiableAt (by norm_num)) (hy'.differentiableAt.restrictScalars ℝ)
  have hdφ : DifferentiableAt ℝ (fderiv ℝ φ) (g x) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun y => fderiv ℝ φ (g y))
      ((fderiv ℝ (fderiv ℝ φ) (g x)).comp (fderiv ℝ g x)) x :=
    hdφ.hasFDerivAt.comp x hgd.hasFDerivAt
  have hD := hc.clm_comp hd2.hasFDerivAt
  unfold leviForm
  rw [hfd.fderiv_eq, hD.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, hGI, hG2II, map_neg, hGw]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviLogFlat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

variable {J : Type} [Fintype J]

theorem fderiv_fderiv_add_apply {f g : (J → ℂ) → ℝ} {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) (v : J → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y => f y + g y)) z v v =
      fderiv ℝ (fderiv ℝ f) z v v + fderiv ℝ (fderiv ℝ g) z v v := by
  have hf' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hg' : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) z) z :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hev : fderiv ℝ (fun y => f y + g y) =ᶠ[𝓝 z] fun y => fderiv ℝ f y + fderiv ℝ g y := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hy1 hy2
    exact ((hy1.differentiableAt (by norm_num)).hasFDerivAt.add
      (hy2.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have h2 : HasFDerivAt (fun y => fderiv ℝ f y + fderiv ℝ g y)
      (fderiv ℝ (fderiv ℝ f) z + fderiv ℝ (fderiv ℝ g) z) z := hf'.add hg'
  rw [hev.fderiv_eq, h2.fderiv]
  rfl

theorem fderiv_fderiv_log_apply {F : (J → ℂ) → ℝ} {z : J → ℂ} (hF : ContDiffAt ℝ 2 F z) (hpos : 0 < F z)
    (v : J → ℂ) :
    fderiv ℝ (fderiv ℝ (fun x => Real.log (F x))) z v v =
      fderiv ℝ (fderiv ℝ F) z v v / F z - (fderiv ℝ F z v) ^ 2 / F z ^ 2 := by
  have hpos' : ∀ᶠ y in 𝓝 z, 0 < F y := continuousAt_const.eventually_lt hF.continuousAt hpos
  have hev : fderiv ℝ (fun x => Real.log (F x)) =ᶠ[𝓝 z] fun y => (F y)⁻¹ • fderiv ℝ F y := by
    filter_upwards [hF.eventually (by simp), hpos'] with y hy hy'
    exact ((hy.differentiableAt (by norm_num)).hasFDerivAt.log hy'.ne').fderiv
  have hH : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) z) z :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hinv : HasFDerivAt (fun y => (F y)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(F z ^ 2)⁻¹)).comp (fderiv ℝ F z)) z :=
    (hasFDerivAt_inv hpos.ne').comp z (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hP := hinv.fun_smul hH
  rw [hev.fderiv_eq, hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  field_simp
  ring

theorem leviForm_log {F : (J → ℂ) → ℝ} {z : J → ℂ} (hF : ContDiffAt ℝ 2 F z) (hpos : 0 < F z) (w : J → ℂ) :
    leviForm (fun x => Real.log (F x)) z w =
      leviForm F z w / F z - ((fderiv ℝ F z w) ^ 2 + (fderiv ℝ F z (Complex.I • w)) ^ 2) / (4 * F z ^ 2) := by
  unfold leviForm
  rw [fderiv_fderiv_log_apply hF hpos, fderiv_fderiv_log_apply hF hpos]
  have : F z ≠ 0 := hpos.ne'
  field_simp
  ring

theorem LeviLogFlat.proof : LeviLogFlat.Statement := by
  intro J _ P u z w hP hu hpos hu0 hdw hdiw hlevi
  have hF : ContDiffAt ℝ 2 (fun x => P x + u x) z := hP.add hu
  have hFpos : 0 < P z + u z := by rw [hu0, add_zero]; exact hpos
  have hd : ∀ v, fderiv ℝ (fun x => P x + u x) z v = fderiv ℝ P z v + fderiv ℝ u z v := by
    intro v
    have h2 : HasFDerivAt (fun x => P x + u x) (fderiv ℝ P z + fderiv ℝ u z) z :=
      (hP.differentiableAt (by norm_num)).hasFDerivAt.add (hu.differentiableAt (by norm_num)).hasFDerivAt
    rw [h2.fderiv]
    rfl
  have hL : leviForm (fun x => P x + u x) z w = leviForm P z w + leviForm u z w := by
    unfold leviForm
    rw [fderiv_fderiv_add_apply hP hu, fderiv_fderiv_add_apply hP hu]
    ring
  rw [leviForm_log hF hFpos, leviForm_log hP hpos, hL, hlevi, hd, hd, hdw, hdiw, hu0]
  simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRankOfSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

namespace RankOfSections

theorem position_nsmul {d : ℕ} {A : Type*} [AddCommGroup A] (f : (Fin d → A) → ℤ)
    (hf : ∀ (bs : Fin d → A) (j : Fin d) (x y : A),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y))
    (bs : Fin d → A) (j : Fin d) (m : ℕ) (y : A) :
    f (Function.update bs j (m • y)) = (m : ℤ) * f (Function.update bs j y) := by
  induction m with
  | zero =>
    have h0 := hf bs j 0 0
    simp only [add_zero] at h0
    simp only [zero_smul, Nat.cast_zero, zero_mul]
    linarith
  | succ m ih =>
    rw [succ_nsmul, hf, ih]
    push_cast
    ring

theorem const_nsmul {d : ℕ} {A : Type*} [AddCommGroup A] (f : (Fin d → A) → ℤ)
    (hf : ∀ (bs : Fin d → A) (j : Fin d) (x y : A),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y))
    (n : ℕ) (x : A) :
    f (fun _ => n • x) = (n : ℤ) ^ d * f (fun _ => x) := by
  classical
  have key : ∀ s : Finset (Fin d),
      f (fun i => if i ∈ s then n • x else x) = (n : ℤ) ^ s.card * f (fun _ => x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      have e : (fun i => if i ∈ insert j s then n • x else x) =
          Function.update (fun i => if i ∈ s then n • x else x) j (n • x) := by
        funext i
        by_cases hi : i = j
        · subst hi
          simp
        · simp [hi]
      have e2 : Function.update (fun i => if i ∈ s then n • x else x) j x =
          (fun i => if i ∈ s then n • x else x) := by
        funext i
        by_cases hi : i = j
        · subst hi
          simp [hj]
        · simp [Function.update_of_ne hi]
      rw [e, position_nsmul f hf, e2, ih, Finset.card_insert_of_notMem hj, pow_succ]
      ring
  simpa using key Finset.univ

theorem bound_of_eventually (f : ℕ → ℝ) (r : ℝ) (a₀ : ℕ) (C : ℝ)
    (h : ∀ n, a₀ ≤ n → |f n| ≤ C * ((n : ℝ) + 1) ^ r) :
    ∃ C' : ℝ, ∀ n : ℕ, |f n| ≤ C' * ((n : ℝ) + 1) ^ r := by
  refine ⟨max C (∑ k ∈ Finset.range a₀, |f k| / ((k : ℝ) + 1) ^ r), fun n => ?_⟩
  have hp : 0 < ((n : ℝ) + 1) ^ r := by positivity
  rcases le_or_gt a₀ n with hn | hn
  · exact (h n hn).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)
  · have h1 : |f n| / ((n : ℝ) + 1) ^ r ≤ ∑ k ∈ Finset.range a₀, |f k| / ((k : ℝ) + 1) ^ r :=
      Finset.single_le_sum (f := fun k => |f k| / ((k : ℝ) + 1) ^ r)
        (fun k _ => by positivity) (Finset.mem_range.2 hn)
    calc |f n| = |f n| / ((n : ℝ) + 1) ^ r * ((n : ℝ) + 1) ^ r := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (h1.trans (le_max_right _ _)) hp.le

theorem proof (hP : HilbertPrime.Statement.{0}) (hM : MixedNumberPolynomial.Statement.{0}) :
    RankOfSections.Statement := by
  intro ι₀ _ q D hq hdim
  have hdim' : ringKrullDim (MRing (fun _ : Unit => ι₀) ℚ ⧸ q) =
      ((D + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
    simpa using hdim
  obtain ⟨a₀, C, hC⟩ := hP D ℚ Unit (fun _ => ι₀) q hq hdim'
  have hadd := (hM ℚ Unit (fun _ => ι₀) q D hq hdim').2
  have hhom : ∀ n : ℕ, intNum ℚ q (fun _ : Fin D => fun _ : Unit => (n : ℤ)) =
      (n : ℤ) ^ D * intNum ℚ q (fun _ : Fin D => fun _ : Unit => (1 : ℤ)) := by
    intro n
    have := const_nsmul (fun bs => intNum ℚ q bs) hadd n (fun _ : Unit => (1 : ℤ))
    have e : (n • fun _ : Unit => (1 : ℤ)) = fun _ : Unit => (n : ℤ) := by
      funext u
      simp
    rw [e] at this
    exact this
  apply bound_of_eventually _ _ a₀ C
  intro n hn
  have h := hC (fun _ => n) (fun _ => hn)
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  rw [hhom n] at h
  convert h using 3
  push_cast
  ring

end RankOfSections

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviHolPerturb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ContDiff

noncomputable section

namespace LeviHolPerturb

variable {J : Type} [Fintype J]

theorem hasDerivAt_of_contDiffAt_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    (hf : ContDiffAt ℝ 2 f 0) :
    (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt f (deriv f t) t) ∧ HasDerivAt (deriv f) (deriv (deriv f) 0) 0 := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.eventually (by simp)] with t ht
    exact (ht.differentiableAt (by norm_num)).hasDerivAt
  · have h1 : ContDiffAt ℝ 1 (fun t => fderiv ℝ f t 1) 0 :=
      (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
    exact (h1.differentiableAt one_ne_zero).hasDerivAt

theorem deriv_deriv_mul {f g : ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 2 g 0) :
    deriv (deriv fun t => f t * g t) 0 =
      deriv (deriv f) 0 * g 0 + 2 * (deriv f 0 * deriv g 0) + f 0 * deriv (deriv g) 0 := by
  obtain ⟨hf1, hf2⟩ := hasDerivAt_of_contDiffAt_two hf
  obtain ⟨hg1, hg2⟩ := hasDerivAt_of_contDiffAt_two hg
  have hev : deriv (fun t => f t * g t) =ᶠ[𝓝 0] fun t => deriv f t * g t + f t * deriv g t := by
    filter_upwards [hf1, hg1] with t h1 h2
    exact (h1.mul h2).deriv
  rw [hev.deriv_eq]
  refine ((hf2.mul hg1.self_of_nhds).add (hf1.self_of_nhds.mul hg2)).deriv.trans ?_
  ring

theorem deriv_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (J → ℂ) → F} {z : J → ℂ}
    (hf : DifferentiableAt ℝ f z) (e : J → ℂ) :
    deriv (fun s : ℝ => f (z + s • e)) 0 = fderiv ℝ f z e := by
  have hline : HasDerivAt (fun s : ℝ => z + s • e) e 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z).congr_deriv (one_smul ℝ e)
  have hz0 : z + (0 : ℝ) • e = z := by rw [zero_smul, add_zero]
  exact (hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline hz0.symm).deriv

theorem deriv_deriv_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (J → ℂ) → F}
    {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z) (e : J → ℂ) :
    deriv (deriv fun s : ℝ => f (z + s • e)) 0 = fderiv ℝ (fderiv ℝ f) z e e := by
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => z + s • e) e s := fun s =>
    (((hasDerivAt_id s).smul_const e).const_add z).congr_deriv (one_smul ℝ e)
  have hz0 : z + (0 : ℝ) • e = z := by rw [zero_smul, add_zero]
  have hcont : Tendsto (fun s : ℝ => z + s • e) (𝓝 0) (𝓝 z) := by
    have h := (hline 0).continuousAt.tendsto
    rwa [hz0] at h
  have hfe : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hev : deriv (fun s : ℝ => f (z + s • e)) =ᶠ[𝓝 0] fun s => fderiv ℝ f (z + s • e) e := by
    filter_upwards [hcont.eventually hfe] with s hs
    have h := (hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s (hline s)
    exact h.deriv
  have hH : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hA : HasFDerivAt (fun y => fderiv ℝ f y e) ((fderiv ℝ (fderiv ℝ f) z).flip e) z := by
    have h := hH.clm_apply (hasFDerivAt_const e z)
    simpa using h
  have hd : HasDerivAt (fun s : ℝ => fderiv ℝ f (z + s • e) e) (fderiv ℝ (fderiv ℝ f) z e e) 0 :=
    hA.comp_hasDerivAt_of_eq (0 : ℝ) (hline 0) hz0.symm
  rw [hev.deriv_eq]
  exact hd.deriv

theorem contDiffAt_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (J → ℂ) → F}
    {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z) (e : J → ℂ) :
    ContDiffAt ℝ 2 (fun s : ℝ => f (z + s • e)) 0 := by
  have hl : ContDiffAt ℝ 2 (fun s : ℝ => z + s • e) 0 :=
    (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffAt
  exact ContDiffAt.comp (g := f) (0 : ℝ) (by simpa using hf) hl

theorem sndDeriv_I_I {φ : (J → ℂ) → ℂ} {z : J → ℂ} (hφ : AnalyticAt ℂ φ z) (a : J → ℂ) :
    fderiv ℝ (fderiv ℝ φ) z (Complex.I • a) (Complex.I • a) = - fderiv ℝ (fderiv ℝ φ) z a a := by
  have hR : AnalyticAt ℝ φ z := hφ.restrictScalars
  have hT : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) z) z :=
    (((hR.contDiffAt (n := 2)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hlin : ∀ a b : J → ℂ, fderiv ℝ (fderiv ℝ φ) z a (Complex.I • b) =
      Complex.I • fderiv ℝ (fderiv ℝ φ) z a b := by
    intro a b
    have h1 := hT.clm_apply (hasFDerivAt_const (Complex.I • b) z)
    have h2 := (hT.clm_apply (hasFDerivAt_const b z)).const_smul Complex.I
    have hev : (fun y => fderiv ℝ φ y (Complex.I • b)) =ᶠ[𝓝 z]
        (fun y => Complex.I • fderiv ℝ φ y b) := by
      filter_upwards [hφ.eventually_analyticAt] with y hy
      rw [hy.differentiableAt.fderiv_restrictScalars ℝ]
      simp
    have h3 := (h1.congr_of_eventuallyEq hev.symm).unique h2
    have := congrArg (fun L => L a) h3
    simpa using this
  have hsymm : IsSymmSndFDerivAt ℝ φ z := (hR.contDiffAt (n := ω)).isSymmSndFDerivAt le_top
  calc fderiv ℝ (fderiv ℝ φ) z (Complex.I • a) (Complex.I • a)
      = Complex.I • fderiv ℝ (fderiv ℝ φ) z (Complex.I • a) a := hlin _ _
    _ = Complex.I • fderiv ℝ (fderiv ℝ φ) z a (Complex.I • a) := by rw [hsymm]
    _ = Complex.I • Complex.I • fderiv ℝ (fderiv ℝ φ) z a a := by rw [hlin]
    _ = - fderiv ℝ (fderiv ℝ φ) z a a := by rw [smul_smul, Complex.I_mul_I]; simp

theorem line_key {X : ℝ → ℝ} {A Φ : ℝ → ℂ} (hX : ContDiffAt ℝ 2 X 0) (hA : ContDiffAt ℝ 2 A 0)
    (hΦ : ContDiffAt ℝ 2 Φ 0) (h0 : Φ 0 = 0) (h1 : deriv Φ 0 = 0) :
    deriv (fun t => X t * (‖A t + Φ t‖ ^ 2 - ‖A t‖ ^ 2)) 0 = 0 ∧
      deriv (deriv fun t => X t * (‖A t + Φ t‖ ^ 2 - ‖A t‖ ^ 2)) 0 =
        2 * X 0 * inner ℝ (A 0) (deriv (deriv Φ) 0) := by
  have hg : (fun t => X t * (‖A t + Φ t‖ ^ 2 - ‖A t‖ ^ 2)) =
      fun t => X t * (2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) := by
    funext t
    rw [norm_add_sq_real, real_inner_self_eq_norm_sq]
    ring
  rw [hg]
  obtain ⟨hX1, hX2⟩ := hasDerivAt_of_contDiffAt_two hX
  obtain ⟨hA1, hA2⟩ := hasDerivAt_of_contDiffAt_two hA
  obtain ⟨hΦ1, hΦ2⟩ := hasDerivAt_of_contDiffAt_two hΦ
  have hN2 : ContDiffAt ℝ 2 (fun t => 2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) 0 :=
    (contDiffAt_const.mul (hA.inner ℝ hΦ)).add (hΦ.inner ℝ hΦ)
  have hN0 : (2 * inner ℝ (A 0) (Φ 0) + inner ℝ (Φ 0) (Φ 0) : ℝ) = 0 := by simp [h0]
  have hNd : HasDerivAt (fun t => 2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) 0 0 := by
    have h := ((hA1.self_of_nhds.inner ℝ hΦ1.self_of_nhds).const_mul 2).add
      (hΦ1.self_of_nhds.inner ℝ hΦ1.self_of_nhds)
    exact h.congr_deriv (by simp [h0, h1])
  have hev : deriv (fun t => 2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) =ᶠ[𝓝 0]
      fun t => 2 * (inner ℝ (A t) (deriv Φ t) + inner ℝ (deriv A t) (Φ t)) +
        (inner ℝ (Φ t) (deriv Φ t) + inner ℝ (deriv Φ t) (Φ t)) := by
    filter_upwards [hA1, hΦ1] with t ha hp
    exact (((ha.inner ℝ hp).const_mul 2).add (hp.inner ℝ hp)).deriv
  have hNdd : deriv (deriv fun t => 2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) 0 =
      2 * inner ℝ (A 0) (deriv (deriv Φ) 0) := by
    rw [hev.deriv_eq]
    have h := ((((hA1.self_of_nhds.inner ℝ hΦ2).add (hA2.inner ℝ hΦ1.self_of_nhds)).const_mul 2).add
      ((hΦ1.self_of_nhds.inner ℝ hΦ2).add (hΦ2.inner ℝ hΦ1.self_of_nhds)))
    refine h.deriv.trans ?_
    simp [h0, h1]
  have key := deriv_deriv_mul hX hN2
  beta_reduce at key
  refine ⟨?_, ?_⟩
  · refine (hX1.self_of_nhds.mul hNd).deriv.trans ?_
    simp [h0]
  · rw [key, hNdd, hN0, hNd.deriv]
    ring

theorem along {ξ : (J → ℂ) → ℝ} {a φ : (J → ℂ) → ℂ} {z : J → ℂ} (hξ : ContDiffAt ℝ 2 ξ z)
    (ha : AnalyticAt ℂ a z) (hφ : AnalyticAt ℂ φ z) (hφ0 : φ z = 0)
    (hu : ContDiffAt ℝ 2 (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z) (v : J → ℂ)
    (hv : fderiv ℂ φ z v = 0) :
    fderiv ℝ (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z v = 0 ∧
      fderiv ℝ (fderiv ℝ fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z v v =
        2 * ξ z * inner ℝ (a z) (fderiv ℝ (fderiv ℝ φ) z v v) := by
  have haR : ContDiffAt ℝ 2 a z := ha.restrictScalars.contDiffAt
  have hφR : ContDiffAt ℝ 2 φ z := hφ.restrictScalars.contDiffAt
  have hz0 : z + (0 : ℝ) • v = z := by rw [zero_smul, add_zero]
  have h0 : (fun t : ℝ => φ (z + t • v)) 0 = 0 := by simp [hφ0]
  have h1 : deriv (fun t : ℝ => φ (z + t • v)) 0 = 0 := by
    rw [deriv_line (hφR.differentiableAt (by norm_num)) v,
      hφ.differentiableAt.fderiv_restrictScalars ℝ]
    simpa using hv
  obtain ⟨k1, k2⟩ := line_key (X := fun t => ξ (z + t • v)) (A := fun t => a (z + t • v))
    (Φ := fun t => φ (z + t • v)) (contDiffAt_line hξ v) (contDiffAt_line haR v)
    (contDiffAt_line hφR v) h0 h1
  refine ⟨?_, ?_⟩
  · rw [← deriv_line (hu.differentiableAt (by norm_num)) v]
    exact k1
  · rw [← deriv_deriv_line hu v, ← deriv_deriv_line hφR v]
    rw [show ξ z = ξ (z + (0 : ℝ) • v) by rw [hz0], show a z = a (z + (0 : ℝ) • v) by rw [hz0]]
    exact k2

theorem proof : LeviHolPerturb.Statement := by
  intro J _ ξ a φ z w hξ ha hφ hφ0 hdφ
  have haR : ContDiffAt ℝ 2 a z := ha.restrictScalars.contDiffAt
  have hφR : ContDiffAt ℝ 2 φ z := hφ.restrictScalars.contDiffAt
  have hu : ContDiffAt ℝ 2 (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z :=
    hξ.mul (((haR.add hφR).norm_sq ℝ).sub (haR.norm_sq ℝ))
  have hw := along hξ ha hφ hφ0 hu w hdφ
  have hIw := along hξ ha hφ hφ0 hu (Complex.I • w) (by rw [map_smul, hdφ, smul_zero])
  refine ⟨hu, by simp [hφ0], hw.1, hIw.1, ?_⟩
  unfold leviForm
  rw [hw.2, hIw.2, sndDeriv_I_I hφ w, inner_neg_right]
  ring

end LeviHolPerturb

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
