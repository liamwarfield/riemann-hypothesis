module

public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannThetaLevelOneNeZero
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MulVecOfRealVecAddMemSpanPeriodLattice
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemPeriodLatticeOfThetaTranslateEqUnitMul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMvPolynomialOfPolyBoundOffHypersurface
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsConnectedUnramifiedCoverOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsNhdsSubsetRange
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IntegralAndRationalOfPolynomialGrowth
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsIntegralAndRationalTheta
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsHomogeneousOfMemSpanPow
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsProjectiveModelPolarisedTorusTheta
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FderivEqZeroOfAffine
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.LocallyOfFiniteTypeTensor
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FderivEqMulOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMemThetaLevelCharApplyNeZero
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RelAmpleThetaBundleProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TranslateTrivialEqOneOfFiniteTypePoints
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TranslationFixingBundleArtinPointEqOne
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemPeriodLatticeOfExpThetaLinForm
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsComplementaryThetaOfLinearMap
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.PolarisedTorusAlgebraicOfParts
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsHomogeneousEvalOfMulMemSpan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

private theorem isWeightedHomogeneous_coeff_mul_rw1 {X ρ : Type} (b : ρ → X → ℂ) {k l : ℕ} {f g : X → ℂ}
    (hf : ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous k ∧
      ∀ z, f z = MvPolynomial.eval (fun c => b c z) G)
    (hg : ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous l ∧
      ∀ z, g z = MvPolynomial.eval (fun c => b c z) G) :
    ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous (k + l) ∧
      ∀ z, f z * g z = MvPolynomial.eval (fun c => b c z) G := by
  obtain ⟨G, hG, hfG⟩ := hf
  obtain ⟨H, hH, hgH⟩ := hg
  exact ⟨G * H, hG.mul hH, fun z => by rw [hfG, hgH, map_mul]⟩

private theorem exists_homogeneous_one_eval_of_mem_span {X ρ : Type} (b : ρ → X → ℂ) {f : X → ℂ}
    (hf : f ∈ Submodule.span ℂ (Set.range b)) :
    ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous 1 ∧
      ∀ z, f z = MvPolynomial.eval (fun c => b c z) G := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X (R := ℂ) i, fun z => by simp⟩
  | zero => exact ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, fun z => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨G, hG, hxG⟩ := hx
    obtain ⟨H, hH, hyH⟩ := hy
    exact ⟨G + H, hG.add hH, fun z => by simp [hxG, hyH]⟩
  | smul c x _ hx =>
    obtain ⟨G, hG, hxG⟩ := hx
    have hCG := (MvPolynomial.isHomogeneous_C (σ := ρ) c).mul hG
    rw [zero_add] at hCG
    exact ⟨MvPolynomial.C c * G, hCG, fun z => by simp [hxG]⟩

private theorem exists_homogeneous_eval_of_even_degree_monomial {X σ ρ : Type} (a : σ → X → ℂ) (b : ρ → X → ℂ)
    (hab : ∀ i j, a i * a j ∈ Submodule.span ℂ (Set.range b)) :
    ∀ (k : ℕ) (m : σ →₀ ℕ), m.degree = 2 * k →
      ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous k ∧
        ∀ z, (m.prod fun c e => a c z ^ e) = MvPolynomial.eval (fun c => b c z) G := by
  intro k
  induction k with
  | zero =>
    intro m hm
    rw [mul_zero, Finsupp.degree_eq_zero_iff] at hm
    subst hm
    exact ⟨1, MvPolynomial.isHomogeneous_one _ _, fun z => by simp⟩
  | succ k ih =>
    intro m hm
    classical
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : m = 0 := by ext x; exact h x
      rw [h0, map_zero] at hm
      omega
    have hle₁ : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m₁, rfl⟩ : ∃ m₁, m = m₁ + Finsupp.single i 1 :=
      ⟨_, (tsub_add_cancel_of_le hle₁).symm⟩
    rw [map_add (f := _), Finsupp.degree_single] at hm
    obtain ⟨j, hj⟩ : ∃ j, m₁ j ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : m₁ = 0 := by ext x; exact h x
      rw [h0, map_zero] at hm
      omega
    have hle₂ : Finsupp.single j 1 ≤ m₁ := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m₂, rfl⟩ : ∃ m₂, m₁ = m₂ + Finsupp.single j 1 :=
      ⟨_, (tsub_add_cancel_of_le hle₂).symm⟩
    rw [map_add (f := _), Finsupp.degree_single] at hm
    have hdeg : m₂.degree = 2 * k := by omega
    obtain ⟨G, hG, hGz⟩ := isWeightedHomogeneous_coeff_mul_rw1 b (ih m₂ hdeg) (exists_homogeneous_one_eval_of_mem_span b (hab j i))
    refine ⟨G, hG, fun z => ?_⟩
    rw [← hGz z, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    simp only [Finsupp.prod_single_index, pow_zero, pow_one, Pi.mul_apply]
    ring

theorem exists_isHomogeneous_eval_of_mul_mem_span {X σ ρ : Type} (a : σ → X → ℂ) (b : ρ → X → ℂ)
    (hab : ∀ i j, a i * a j ∈ Submodule.span ℂ (Set.range b)) (d : ℕ) (F : MvPolynomial σ ℂ)
    (hF : F.IsHomogeneous (2 * d)) :
    ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous d ∧
      ∀ z, MvPolynomial.eval (fun c => a c z) F = MvPolynomial.eval (fun c => b c z) G := by
  classical
  have hP : ∀ s : Finset (σ →₀ ℕ), s ⊆ F.support → ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous d ∧
      ∀ z, (∑ m ∈ s, F.coeff m * m.prod fun c e => a c z ^ e) =
        MvPolynomial.eval (fun c => b c z) G := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, fun z => by simp⟩
    | insert m s hms ih =>
      intro hsub
      obtain ⟨G, hG, hGz⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      have hm : m.degree = 2 * d := by
        rw [Finsupp.degree_eq_weight_one]
        exact hF (MvPolynomial.mem_support_iff.mp (hsub (Finset.mem_insert_self m s)))
      obtain ⟨H, hH, hHz⟩ := exists_homogeneous_eval_of_even_degree_monomial a b hab d m hm
      have hCH := (MvPolynomial.isHomogeneous_C (σ := ρ) (F.coeff m)).mul hH
      rw [zero_add] at hCH
      refine ⟨MvPolynomial.C (F.coeff m) * H + G, hCH.add hG, fun z => ?_⟩
      rw [Finset.sum_insert hms, hGz z, hHz z]
      simp
  obtain ⟨G, hG, hGz⟩ := hP F.support subset_rfl
  exact ⟨G, hG, fun z => by rw [MvPolynomial.eval_eq, ← hGz z]; rfl⟩

theorem theta_projectiveNormality_even :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∃ N : ℕ, 3 ≤ N ∧ ∀ (d : ℕ) (f : (Fin g → ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → ∃ F : MvPolynomial (Fin g → Fin N) ℂ, F.IsHomogeneous d ∧ ∀ z, f z = MvPolynomial.eval (fun c => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∃ N : ℕ, 3 ≤ N ∧ Even N ∧ (∀ (d : ℕ) (f : (Fin g → ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → ∃ F : MvPolynomial (Fin g → Fin N) ℂ, F.IsHomogeneous d ∧ ∀ z, f z = MvPolynomial.eval (fun c => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F)) := by
  intro hA hB hC g τ hτ
  obtain ⟨N, hN3, hNC⟩ := hC g τ hτ
  refine ⟨2 * N, by omega, even_two_mul N, fun d f hf => ?_⟩
  obtain ⟨F, hF, hFz⟩ := hNC (2 * d) f
    ⟨hf.1, fun n n' z => by rw [show N * (2 * d) = 2 * N * d by ring]; exact hf.2 n n' z⟩
  have hA' := (hA g τ hτ N (by omega)).1
  have hab : ∀ i j : Fin g → Fin N,
      (fun z : Fin g → ℂ => theta (fun k => ((i k : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) *
        (fun z : Fin g → ℂ => theta (fun k => ((j k : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∈
      Submodule.span ℂ (Set.range (fun (c : Fin g → Fin (2 * N)) (z : Fin g → ℂ) =>
        theta (fun k => ((c k : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)) 0
          (((2 * N : ℕ) : ℂ) • z) (((2 * N : ℕ) : ℂ) • τ))) := by
    intro i j
    refine hB g τ hτ (2 * N) (by omega) _ ⟨(hA' i).1.mul (hA' j).1, fun n n' z => ?_⟩
    have h1 := (hA' i).2 n n' z
    have h2 := (hA' j).2 n n' z
    beta_reduce at h1 h2 ⊢
    rw [Pi.mul_apply, Pi.mul_apply, h1, h2,
      show ∀ x : ℂ, eC (-((2 * N : ℕ) : ℂ) * x) = eC (-(N : ℂ) * x) * eC (-(N : ℂ) * x) from
        fun x => by unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  obtain ⟨G, hG, hGz⟩ := exists_isHomogeneous_eval_of_mul_mem_span
    (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
      theta (fun k => ((c k : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))
    (fun (c : Fin g → Fin (2 * N)) (z : Fin g → ℂ) =>
      theta (fun k => ((c k : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)) 0
        (((2 * N : ℕ) : ℂ) • z) (((2 * N : ℕ) : ℂ) • τ))
    hab d F hF
  exact ⟨G, hG, fun z => (hFz z).trans (hGz z)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ThetaConeIdealIsPrimeAndRingKrullDimLe
namespace GlobalTheory

namespace ThetaCone

open MvPolynomial Filter Topology Module ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf

attribute [local instance] MvPolynomial.gradedAlgebra

section General

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eval_mul_of_isHomogeneous (q : ι → ℂ) (t : ℂ) {G : MvPolynomial ι ℂ} {m : ℕ}
    (hG : G.IsHomogeneous m) : eval (fun i => t * q i) G = t ^ m * eval q G := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hw := hG (mem_support_iff.mp hs)
  simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] at hw
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hw]
  ring

theorem differentiable_eval {φ : ι → E → ℂ} (hφ : ∀ c, Differentiable ℂ (φ c))
    (F : MvPolynomial ι ℂ) : Differentiable ℂ fun z => eval (fun c => φ c z) F := by
  apply MvPolynomial.induction_on F
  · intro a
    simp only [eval_C]
    exact differentiable_const a
  · intro p q hp hq
    simp only [map_add (f := _)]
    exact hp.add hq
  · intro p c hp
    simp only [map_mul, eval_X]
    exact hp.mul (hφ c)

theorem eq_zero_or_eq_zero_of_mul [FiniteDimensional ℂ E] {f g : E → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (h : ∀ z, f z * g z = 0) :
    (∀ z, f z = 0) ∨ ∀ z, g z = 0 := by
  by_cases hf0 : ∀ z, f z = 0
  · exact Or.inl hf0
  right
  simp only [not_forall] at hf0
  obtain ⟨a, ha⟩ := hf0

  have hev : g =ᶠ[𝓝 a] 0 := by
    filter_upwards [hf.continuous.continuousAt.eventually_ne ha] with z hz
    exact (mul_eq_zero.mp (h z)).resolve_left hz
  have hga : AnalyticOnNhd ℂ g Set.univ := GlobalTheory.SCV.analyticOnNhd_of_differentiable hg Set.univ
  have hzero := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ a) hev
  exact fun z => hzero (Set.mem_univ z)

theorem isPrime [FiniteDimensional ℂ E] {φ : ι → E → ℂ} (hφ : ∀ c, Differentiable ℂ (φ c))
    {I : Ideal (MvPolynomial ι ℂ)}
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), eval (fun c => t * φ c z) F = 0) : I.IsPrime := by
  refine Ideal.isPrime_iff.mpr ⟨fun htop => ?_, fun {F G} hFG => ?_⟩
  · have h1 := (hI 1).mp ((Ideal.eq_top_iff_one I).mp htop) 1 0
    simp at h1

  have hmul := (hI _).mp hFG
  have hψ : ∀ c, Differentiable ℂ (fun p : ℂ × E => p.1 * φ c p.2) := fun c =>
    differentiable_fst.mul ((hφ c).comp differentiable_snd)
  rcases eq_zero_or_eq_zero_of_mul (differentiable_eval hψ F) (differentiable_eval hψ G)
      (fun p => by simpa only [map_mul] using hmul p.1 p.2) with h | h
  · exact Or.inl ((hI F).mpr fun t z => h (t, z))
  · exact Or.inr ((hI G).mpr fun t z => h (t, z))

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem isHomogeneous {φ : ι → E → ℂ} {I : Ideal (MvPolynomial ι ℂ)}
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), eval (fun c => t * φ c z) F = 0) :
    I.IsHomogeneous (homogeneousSubmodule ι ℂ) := by
  intro i F hF
  have hdec : ((DirectSum.decompose (homogeneousSubmodule ι ℂ) F) i : MvPolynomial ι ℂ) =
      homogeneousComponent i F := decomposition.decompose'_apply F i
  rw [hdec]
  refine (hI _).mpr fun t z => ?_
  rw [eval_mul_of_isHomogeneous (fun c => φ c z) t (homogeneousComponent_isHomogeneous i F)]
  suffices hz : eval (fun c => φ c z) (homogeneousComponent i F) = 0 by rw [hz, mul_zero]

  have hn : F.totalDegree + 1 ≤ F.totalDegree + i + 1 := by omega
  have hsum : ∑ m ∈ Finset.range (F.totalDegree + i + 1), homogeneousComponent m F = F := by
    rw [← Finset.sum_subset (Finset.range_mono hn) (fun m _ hm => by
      apply homogeneousComponent_eq_zero
      simp only [Finset.mem_range, not_lt] at hm
      omega)]
    exact sum_homogeneousComponent F
  have hP : ∀ s : ℂ, (∑ m ∈ Finset.range (F.totalDegree + i + 1),
      Polynomial.C (eval (fun c => φ c z) (homogeneousComponent m F)) * Polynomial.X ^ m).eval s
        = (0 : Polynomial ℂ).eval s := by
    intro s
    have h0 := (hI F).mp hF s z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hsum, map_sum] at h0
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    rw [← h0]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [eval_mul_of_isHomogeneous (fun c => φ c z) s (homogeneousComponent_isHomogeneous m F)]
    ring
  have hc := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) (Polynomial.funext hP)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero,
    Finset.sum_ite_eq, Finset.mem_range] at hc
  simpa [show i < F.totalDegree + i + 1 by omega] using hc

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem finrank_quotPiece_le [Finite ι] {φ : ι → E → ℂ} {I : Ideal (MvPolynomial ι ℂ)}
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), eval (fun c => t * φ c z) F = 0) {d B : ℕ}
    (hB : ∀ (r : ℕ) (F : Fin r → MvPolynomial ι ℂ), (∀ k, (F k).IsHomogeneous d) →
      LinearIndependent ℂ (fun k z => eval (fun c => φ c z) (F k)) → r ≤ B) :
    finrank ℂ (quotPiece I d) ≤ B := by
  classical
  by_cases hfin : FiniteDimensional ℂ (quotPiece I d)
  swap
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [Module.finrank_of_not_finite hfin]
    exact Nat.zero_le _
  let b := Module.finBasis ℂ (quotPiece I d)

  have hlift : ∀ x ∈ quotPiece I d, ∃ p ∈ homogeneousSubmodule ι ℂ d,
      (Ideal.Quotient.mkₐ ℂ I).toLinearMap p = x := by
    intro x hx
    rw [quotPiece_natCast] at hx
    exact Submodule.mem_map.mp hx
  have hmem : ∀ k, ∃ p ∈ homogeneousSubmodule ι ℂ d,
      (Ideal.Quotient.mkₐ ℂ I).toLinearMap p = (b k : MvPolynomial ι ℂ ⧸ I) :=
    fun k => hlift _ (b k).2
  choose F hFd hFb using hmem
  refine hB _ F (fun k => (mem_homogeneousSubmodule d (F k)).mp (hFd k)) ?_
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have hhom : (∑ k, a k • F k).IsHomogeneous d := (mem_homogeneousSubmodule d _).mp
    (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hFd k))
  have hG : ∑ k, a k • F k ∈ I := by
    refine (hI _).mpr fun t z => ?_
    rw [eval_mul_of_isHomogeneous (fun c => φ c z) t hhom]
    have hz := congrFun ha z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hz
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [smul_eval]
    rw [hz, mul_zero]
  have h0 : ∑ k, a k • b k = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [← hFb, ← map_smul, ← map_sum]
    simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hG
  exact (Fintype.linearIndependent_iff.mp b.linearIndependent) a h0

theorem isPrime_and_ringKrullDim_le [Finite ι] [FiniteDimensional ℂ E] {φ : ι → E → ℂ}
    (hφ : ∀ c, Differentiable ℂ (φ c)) (hne : ∃ c, φ c ≠ 0) {I : Ideal (MvPolynomial ι ℂ)}
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), eval (fun c => t * φ c z) F = 0) {g N : ℕ}
    (hB : ∀ d, 1 ≤ d → ∀ (r : ℕ) (F : Fin r → MvPolynomial ι ℂ), (∀ k, (F k).IsHomogeneous d) →
      LinearIndependent ℂ (fun k z => eval (fun c => φ c z) (F k)) → r ≤ (N * d) ^ g) :
    I.IsPrime ∧ ringKrullDim (MvPolynomial ι ℂ ⧸ I) ≤ (g + 1 : ℕ) := by
  classical
  have hprime := isPrime hφ hI
  have hhom := isHomogeneous hI
  obtain ⟨c, hc⟩ := hne
  have hX : ∃ i, X i ∉ I :=
    ⟨c, fun hmem => hc (funext fun z => by simpa using (hI _).mp hmem 1 z)⟩
  refine ⟨hprime, ?_⟩
  have := hprime
  rw [ProjCut.ringKrullDim_eq_natDegree_idealHilbertPoly hhom hX]

  have hle : (idealHilbertPoly I).degree ≤
      (Polynomial.C ((N : ℚ) ^ g) * Polynomial.X ^ g).degree := by
    apply degree_le_of_eventually_eval_nat (eventually_idealHilbertPoly_nonneg hhom)
    filter_upwards [eventually_finrank_quotPiece hhom, Filter.eventually_ge_atTop 1]
      with n hn hn1
    rw [← hn]
    have hb := finrank_quotPiece_le hI (hB n hn1)
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← mul_pow]
    exact_mod_cast hb
  have hdeg : (idealHilbertPoly I).natDegree ≤ g :=
    Polynomial.natDegree_le_of_degree_le (hle.trans (Polynomial.degree_C_mul_X_pow_le _ _))
  exact_mod_cast (show (idealHilbertPoly I).natDegree + 1 ≤ g + 1 by omega)

end General

end ThetaCone

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

theorem thetaConeIdeal_isPrime_and_ringKrullDim_le :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g n : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (b : Fin g → ℂ), 1 ≤ n → (∀ j, b j ≠ 0) → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, (Differentiable ℂ (f k) ∧ (∀ (i : Fin g) z, (f k) (z + Pi.single i 1) = (f k) z) ∧ ∀ (j : Fin g) z, (f k) (z + τ.mulVec (Pi.single j 1)) = b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * (f k) z)) → LinearIndependent ℂ f → N ≤ n ^ g) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 2 ≤ N → ∀ (I : Ideal (MvPolynomial (Fin g → Fin N) ℂ)), (∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : Fin g → ℂ), MvPolynomial.eval (fun c => t * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F = 0) → I.IsPrime ∧ ringKrullDim (MvPolynomial (Fin g → Fin N) ℂ ⧸ I) ≤ (g + 1 : ℕ)) := by
  intro hA hBd g τ hτ N hN I hI
  let ψ : (Fin g → Fin N) → (Fin g → ℂ) → ℂ := fun c z =>
    theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)
  have hAc := hA g τ hτ N (by omega)
  have hdiff : ∀ c, Differentiable ℂ (ψ c) := fun c => (hAc.1 c).1
  have hquasi : ∀ c (n n' : Fin g → ℤ) z, ψ c (z + τ *ᵥ ofIntVec n + ofIntVec n') =
      eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * ψ c z :=
    fun c => (hAc.1 c).2
  have : Nonempty (Fin g → Fin N) := ⟨fun _ => ⟨0, by omega⟩⟩
  have hne : ∃ c, ψ c ≠ 0 := ⟨Classical.arbitrary _, hAc.2.ne_zero _⟩
  refine ThetaCone.isPrime_and_ringKrullDim_le (φ := ψ) (g := g) (N := N) hdiff hne hI ?_
  intro d hd r F hF hind

  have hscale : ∀ (k : Fin r) (w z : Fin g → ℂ) (l : ℂ), (∀ c, ψ c w = l * ψ c z) →
      MvPolynomial.eval (fun c => ψ c w) (F k) = l ^ d * MvPolynomial.eval (fun c => ψ c z) (F k) := by
    intro k w z l h
    rw [← ThetaCone.eval_mul_of_isHomogeneous (fun c => ψ c z) l (hF k)]
    have hfun : (fun c => ψ c w) = fun c => l * ψ c z := funext h
    rw [hfun]
  have hzero : ofIntVec (0 : Fin g → ℤ) = 0 := by
    funext i
    simp [ofIntVec]
  have hsingle : ∀ j : Fin g, ofIntVec (Pi.single j (1 : ℤ)) = (Pi.single j 1 : Fin g → ℂ) := by
    intro j
    funext i
    by_cases h : i = j
    · subst h
      simp [ofIntVec]
    · simp [ofIntVec, h]
  refine hBd g (N * d) τ (fun j => eC (-(τ j j) / 2)) (Nat.mul_pos (by omega) hd)
    (fun j => Complex.exp_ne_zero _) r (fun k z => MvPolynomial.eval (fun c => ψ c z) (F k))
    (fun k => ⟨ThetaCone.differentiable_eval hdiff (F k), fun i z => ?_, fun j z => ?_⟩) hind
  · have h := hscale k (z + Pi.single i 1) z 1 (fun c => by
      simpa [hzero, hsingle, eC] using hquasi c 0 (Pi.single i 1) z)
    simpa using h
  · have h := hscale k (z + τ.mulVec (Pi.single j 1)) z (eC (-(N : ℂ) * (τ j j / 2 + z j)))
      (fun c => by simpa [hzero, hsingle] using hquasi c (Pi.single j 1) 0 z)
    rw [h]
    congr 1
    simp only [eC, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.FiniteOfIsIntegralOfBirationalOfPresentation
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

theorem finite_of_isIntegral_of_birational_of_finite_over_normal
    (R A B : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [CharZero R] [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra R A] [FaithfulSMul R A] [Module.Finite R A]
    [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (hb : ∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) :
    Module.Finite A B := by
  letI : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let L := FractionRing B
  haveI : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply A B L]; rfl
  have hAB : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A B L]; exact hBL.comp hAB

  haveI : IsFractionRing A L := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · intro y
      exact IsUnit.mk0 _ ((map_ne_zero_iff _ hAL).mpr (nonZeroDivisors.ne_zero y.2))
    · intro z
      obtain ⟨⟨x, y⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors B) z
      obtain ⟨a₁, c₁, hc₁, h₁⟩ := hb x
      obtain ⟨a₂, c₂, hc₂, h₂⟩ := hb (y : B)
      have hy : (y : B) ≠ 0 := nonZeroDivisors.ne_zero y.2
      have ha₂ : a₂ ≠ 0 := by
        intro h0
        rw [h0, map_zero] at h₂
        exact mul_ne_zero ((map_ne_zero_iff _ hAB).mpr hc₂) hy h₂
      refine ⟨⟨a₁ * c₂, ⟨c₁ * a₂, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hc₁ ha₂)⟩⟩, ?_⟩
      simp only [IsScalarTower.algebraMap_apply A B L, map_mul, ← h₁, ← h₂]
      simp only [map_mul] at hz ⊢
      rw [← hz]; ring
    · intro x y hxy
      exact ⟨1, by rw [hAL hxy]⟩
  haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr (by
    rw [IsScalarTower.algebraMap_eq R A L]
    exact hAL.comp (FaithfulSMul.algebraMap_injective R A))
  let K := FractionRing R
  letI : Algebra K L := FractionRing.liftAlgebra R L
  haveI : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  haveI : Module.Finite K L := Module.Finite.of_isLocalization R A (nonZeroDivisors R)
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  haveI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.trans A
  let f : B →ₐ[R] integralClosure R L :=
    (IsScalarTower.toAlgHom R B L).codRestrict (integralClosure R L)
      (fun b => (Algebra.IsIntegral.isIntegral (R := R) b).map (IsScalarTower.toAlgHom R B L))
  have hf : Function.Injective f.toLinearMap := fun x y h =>
    hBL (congrArg Subtype.val h)
  haveI : IsNoetherian R (integralClosure R L) := isNoetherian_of_isNoetherianRing_of_finite _ _
  haveI : IsNoetherian R B := isNoetherian_of_injective f.toLinearMap hf
  haveI : Module.Finite R B := Module.IsNoetherian.finite R B
  exact Module.Finite.of_restrictScalars_finite R A B

theorem finite_of_isIntegral_of_birational_complex
    (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (hb : ∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) :
    Module.Finite A B := by
  obtain ⟨d, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ A
  letI : Algebra (MvPolynomial (Fin d) ℂ) A := g.toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hg
  haveI : Module.Finite (MvPolynomial (Fin d) ℂ) A := hfin
  exact finite_of_isIntegral_of_birational_of_finite_over_normal (MvPolynomial (Fin d) ℂ) A B hb

theorem finite_of_isIntegral_of_birational_of_presentation :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a) → (∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra ℂ A] [Algebra.FiniteType ℂ A] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B], (∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) → Module.Finite A B) := by
  intro _ A B _ _ _ _ _ _ _ _ _ hb
  exact finite_of_isIntegral_of_birational_complex A B hb

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

theorem polarisedTorus_algebraic :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∃ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L g) (th : P.L.Sec), P.g = g ∧ (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧ u.IsFn th (thetaChar τ a b) ∧ ∀ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ l ∈ u.Λ, F l ∈ u.Λ) → ∃ f : P.A ⟶ P.A, IsMonHom f ∧ ∀ z, u.ex (F z) = u.ex z ≫ f) := by
  have f0 := @GlobalTheory.siegelSubDomain_and_domainOpen
  have f1 := @GlobalTheory.thetaMTest_and_thetaSummable
  have f2 := @GlobalTheory.thetaHolo_of_domainOpen_of_mTest f0.2 f1.1
  have f3 := @GlobalTheory.classicalTheta_level_and_linearIndependent f0.1 f2 f1.1
  have f4 := @GlobalTheory.fourierCoeff_unitCube_translate_of_entire_periodic
  have f5 := @GlobalTheory.entire_periodic_eq_zero_of_fourierCoeff_eq_zero f4
  have f6 := @GlobalTheory.ClassicalTheta.card_le_pow_of_linearIndependent f4 f5
  have f7 := @GlobalTheory.ThetaSpan.mem_span_theta_of_level f6 f3
  have f8 := @GlobalTheory.riemannTheta_level_one_ne_zero f3
  have f9 := @GlobalTheory.exists_level_apply_ne_zero_of_two_le f8
  have f10 := @GlobalTheory.periodLattice_isLattice_of_mem_siegelH
  have f11 := @GlobalTheory.mem_periodLattice_of_theta_translate_eq_unit_mul f8 f10
  have f12 := @GlobalTheory.ThetaSeparation.level_three_separates_points f8 f11
  have f13 := @GlobalTheory.ThetaTangent.level_three_separates_tangent_vectors f8 f11 f10
  have f14 := @GlobalTheory.thetaConeIdeal_isPrime_and_ringKrullDim_le f3 f6
  have f15 := @GlobalTheory.noetherNormalization_primitive
  have f16 := @GlobalTheory.isConnected_and_dense_compl_hypersurface
  have f17 := @GlobalTheory.exists_mvPolynomial_of_poly_bound_off_hypersurface
  have f18 := @GlobalTheory.isConnected_unramified_cover_of_irreducible f16 f17
  have f19 := @GlobalTheory.exists_isConnected_principalOpen f15 f18
  have f20 := @GlobalTheory.principalOpen_dense_complexPoints f15 f16
  have f21 := @GlobalTheory.isConnected_basicOpen_complexPoints_of_dense f19 f20
  have f22 := @GlobalTheory.thetaCone_eq_zeroLocus f3 f7 f9 f13 f10 f14 f15 f21 f20
  have f23 := @GlobalTheory.FiniteCoverGrowth.integral_and_rational_of_polynomial_growth f16 f17
  have f24 := @GlobalTheory.ThetaRational.isIntegral_and_rational_theta f3 f7 f9 f12 f13 f10 f14 f22 f15 f23
  have f25 := @GlobalTheory.finite_of_isIntegral_of_birational_of_presentation f15
  have f26 := @GlobalTheory.theta_ring_generated_in_degree_one f3 f7 f24 f25
  have f27 := @GlobalTheory.theta_projectiveNormality_even f3 f7 f26
  have f28 := @GlobalTheory.existsUnique_point_of_ringHom
  have f29 := @GlobalTheory.T.exists_projectiveModel_polarisedTorus_theta f28 f3 f7 f9 f12 f14 f22
  have f30 := @GlobalTheory.valAt'_rules
  have f31 := @GlobalTheory.eq_of_valAt'_eq f30 f28
  have f32 := @GlobalTheory.theta_quotient_regular f31
  have f33 := @GlobalTheory.holFamily_lift f30
  have f34 := @GlobalTheory.existsUnique_hom_of_locally_regular f28 f31
  have f35 := @GlobalTheory.isReduced_tensorObj_complex
  have f36 := @GlobalTheory.ThetaAddition.addition_level_two_mul f3 f7
  have f37 := @GlobalTheory.thetaModel_groupLaw f33 f31 f34 f35 f36 f3 f7 f9 f10
  have f38 := @GlobalTheory.SmoothDim.ringKrullDim_affineOpen
  have f39 := @GlobalTheory.exists_holomorphic_section_of_etale
  have f40 := @GlobalTheory.HolChart.exists_holomorphic_chart f30 f28 f39
  have f41 := @GlobalTheory.ProjModelDim.isAbelianScheme_and_dim f38 f40 f3 f7 f13
  have f42 := @GlobalTheory.exists_thetaBundle_holUnif f31 f0.1 f2 f8 f10
  have f43 := @GlobalTheory.ThetaBundleSym.rigidified_sym_section f31 f0.1 f2
  have f44 := @GlobalTheory.T.relAmple_thetaBundle_projectiveModel f31 f3
  have f45 := @GlobalTheory.exists_coord_adapted f40
  have f46 := @GlobalTheory.kTriv_of_global
  have f47 := @GlobalTheory.T.translate_trivial_eq_one_of_finiteType_points
  have f48 := @GlobalTheory.translDiff_triv_of_artin_local
  have f49 := @GlobalTheory.TangentOrigin.tangent_bijection_of_values f30
  have f50 := @GlobalTheory.T.translation_fixing_bundle_artin_point_eq_one f33 f49
  have f51 := @GlobalTheory.thetaBundle_kTriv f10 f13 f3 f7 f45 f46 f47 f48 f50
  have f52 := @GlobalTheory.appellHumbert_normal_form_of_linear_exponent
  have f53 := @GlobalTheory.ThetaPositivity.re_form_pos_of_theta_ne_zero
  have f54 := @GlobalTheory.T.exists_thetaSeries_apply_ne_zero_of_large_form
  have f55 := @GlobalTheory.exists_complementary_theta_of_linear_map f10 f8 f52 f53 f54
  have f56 := @GlobalTheory.exists_isMonHom_of_map_periodLattice f31 f34 f35 f55 f3
  exact @GlobalTheory.polarisedTorus_algebraic_of_parts f27 f29 f32 f37 f41 f42 f43 f44 f51 f56

theorem torusAlgebraic_of_sections_of_veryAmple :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X
        : Over (Sp ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin
        N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧
        (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left,
        U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex
        w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ
        : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D
        c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i
        : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D
        c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ)
        • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin
        N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso
        (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g →
        ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠
        0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → Even N → ∀ [GrpObj X], (∀ z w, ex (z
        +
        w) = ex z * ex w) → ∀ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∀ (L
        : LB X.left) (u : HolUnif X L g), L.IsLB → (u.ex = ex ∧ (∀ z, z ∈ u.Λ ↔ z ∈ periodLattice τ)
        ∧ (∀ (n n' : Fin g → ℤ) i z, ⊤ ≤ (ex
        z).left ⁻¹ᵁ L.U i → u.fr i z = autFactor a b τ n n' z * u.fr i (z + τ *ᵥ ofIntVec n +
        ofIntVec n')) ∧ (∀ i, ∃ h F : (Fin g → ℂ) → ℂ, (Differentiable ℂ h ∧ ∀ (n n'
        : Fin g → ℤ) z, h (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
        ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * h z) ∧ Differentiable ℂ F ∧ (∀ (n n'
        : Fin g → ℤ) z, F (z + τ *ᵥ ofIntVec n + ofIntVec n') = autFactor a b τ n n' z * eC (-(N
        : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * F z) ∧ ∀ z, (⊤ ≤ (ex
        z).left ⁻¹ᵁ L.U i ↔ h z ≠ 0 ∧ F z ≠
        0) ∧ u.fr i z = h z / F z)) → IsAbelianScheme X → SmoothOfRelativeDimension g X.hom → (∀ n : ℕ, (∀ s, ∃! θ, θ ∈ thetaLevelChar a b n τ ∧ u.IsFnPow n s θ) ∧ ∀ θ ∈ thetaLevelChar a b n τ, ∃! s, u.IsFnPow n s θ)) → (∀ (g
        : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp
        ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin
        N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧
        (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left,
        U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex
        w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ
        : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D
        c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i
        : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D
        c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ)
        • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin
        N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso
        (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g →
        ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠
        0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → Even N → ∀ [GrpObj X], (∀ z w, ex (z
        +
        w) = ex z * ex w) → ∀ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∀ (L
        : LB X.left) (u : HolUnif X L g), L.IsLB → (u.ex = ex ∧ (∀ z, z ∈ u.Λ ↔ z ∈ periodLattice τ)
        ∧ (∀ (n n' : Fin g → ℤ) i z, ⊤ ≤ (ex
        z).left ⁻¹ᵁ L.U i → u.fr i z = autFactor a b τ n n' z * u.fr i (z + τ *ᵥ ofIntVec n +
        ofIntVec n')) ∧ (∀ i, ∃ h F : (Fin g → ℂ) → ℂ, (Differentiable ℂ h ∧ ∀ (n n'
        : Fin g → ℤ) z, h (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
        ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * h z) ∧ Differentiable ℂ F ∧ (∀ (n n'
        : Fin g → ℤ) z, F (z + τ *ᵥ ofIntVec n + ofIntVec n') = autFactor a b τ n n' z * eC (-(N
        : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * F z) ∧ ∀ z, (⊤ ≤ (ex
        z).left ⁻¹ᵁ L.U i ↔ h z ≠ 0 ∧ F z ≠
        0) ∧ u.fr i z = h z / F z)) → IsAbelianScheme X → SmoothOfRelativeDimension g X.hom → (∀ n : ℕ, (∀ s, ∃! θ, θ ∈ thetaLevelChar a b n τ ∧ u.IsFnPow n s θ) ∧ ∀ θ ∈ thetaLevelChar a b n τ, ∃! s, u.IsFnPow n s θ) → ∀ M : ℕ, 3 ≤ M → Out.VeryAmpleAt X L M) → TorusAlgebraic := by
  intro hsec hva g τ a₀ b₀ hs hp ha₀ hb₀
  have f0 := @GlobalTheory.siegelSubDomain_and_domainOpen
  have f1 := @GlobalTheory.thetaMTest_and_thetaSummable
  have f2 := @GlobalTheory.thetaHolo_of_domainOpen_of_mTest f0.2 f1.1
  have f3 := @GlobalTheory.classicalTheta_level_and_linearIndependent f0.1 f2 f1.1
  have f4 := @GlobalTheory.fourierCoeff_unitCube_translate_of_entire_periodic
  have f5 := @GlobalTheory.entire_periodic_eq_zero_of_fourierCoeff_eq_zero f4
  have f6 := @GlobalTheory.ClassicalTheta.card_le_pow_of_linearIndependent f4 f5
  have f7 := @GlobalTheory.ThetaSpan.mem_span_theta_of_level f6 f3
  have f8 := @GlobalTheory.riemannTheta_level_one_ne_zero f3
  have f9 := @GlobalTheory.exists_level_apply_ne_zero_of_two_le f8
  have f10 := @GlobalTheory.periodLattice_isLattice_of_mem_siegelH
  have f11 := @GlobalTheory.mem_periodLattice_of_theta_translate_eq_unit_mul f8 f10
  have f12 := @GlobalTheory.ThetaSeparation.level_three_separates_points f8 f11
  have f13 := @GlobalTheory.ThetaTangent.level_three_separates_tangent_vectors f8 f11 f10
  have f14 := @GlobalTheory.thetaConeIdeal_isPrime_and_ringKrullDim_le f3 f6
  have f15 := @GlobalTheory.noetherNormalization_primitive
  have f16 := @GlobalTheory.isConnected_and_dense_compl_hypersurface
  have f17 := @GlobalTheory.exists_mvPolynomial_of_poly_bound_off_hypersurface
  have f18 := @GlobalTheory.isConnected_unramified_cover_of_irreducible f16 f17
  have f19 := @GlobalTheory.exists_isConnected_principalOpen f15 f18
  have f20 := @GlobalTheory.principalOpen_dense_complexPoints f15 f16
  have f21 := @GlobalTheory.isConnected_basicOpen_complexPoints_of_dense f19 f20
  have f22 := @GlobalTheory.thetaCone_eq_zeroLocus f3 f7 f9 f13 f10 f14 f15 f21 f20
  have f23 := @GlobalTheory.FiniteCoverGrowth.integral_and_rational_of_polynomial_growth f16 f17
  have f24 := @GlobalTheory.ThetaRational.isIntegral_and_rational_theta f3 f7 f9 f12 f13 f10 f14 f22 f15 f23
  have f25 := @GlobalTheory.finite_of_isIntegral_of_birational_of_presentation f15
  have f26 := @GlobalTheory.theta_ring_generated_in_degree_one f3 f7 f24 f25
  have f27 := @GlobalTheory.theta_projectiveNormality_even f3 f7 f26
  have f28 := @GlobalTheory.existsUnique_point_of_ringHom
  have f29 := @GlobalTheory.T.exists_projectiveModel_polarisedTorus_theta f28 f3 f7 f9 f12 f14 f22
  have f30 := @GlobalTheory.valAt'_rules
  have f31 := @GlobalTheory.eq_of_valAt'_eq f30 f28
  have f32 := @GlobalTheory.theta_quotient_regular f31
  have f33 := @GlobalTheory.holFamily_lift f30
  have f34 := @GlobalTheory.existsUnique_hom_of_locally_regular f28 f31
  have f35 := @GlobalTheory.isReduced_tensorObj_complex
  have f36 := @GlobalTheory.ThetaAddition.addition_level_two_mul f3 f7
  have f37 := @GlobalTheory.thetaModel_groupLaw f33 f31 f34 f35 f36 f3 f7 f9 f10
  have f38 := @GlobalTheory.SmoothDim.ringKrullDim_affineOpen
  have f39 := @GlobalTheory.exists_holomorphic_section_of_etale
  have f40 := @GlobalTheory.HolChart.exists_holomorphic_chart f30 f28 f39
  have f41 := @GlobalTheory.ProjModelDim.isAbelianScheme_and_dim f38 f40 f3 f7 f13
  have f42 := @GlobalTheory.exists_thetaBundle_holUnif f31 f0.1 f2 f8 f10
  have f43 := @GlobalTheory.ThetaBundleSym.rigidified_sym_section f31 f0.1 f2
  have f44 := @GlobalTheory.T.relAmple_thetaBundle_projectiveModel f31 f3
  have f45 := @GlobalTheory.exists_coord_adapted f40
  have f46 := @GlobalTheory.kTriv_of_global
  have f47 := @GlobalTheory.T.translate_trivial_eq_one_of_finiteType_points
  have f48 := @GlobalTheory.translDiff_triv_of_artin_local
  have f49 := @GlobalTheory.TangentOrigin.tangent_bijection_of_values f30
  have f50 := @GlobalTheory.T.translation_fixing_bundle_artin_point_eq_one f33 f49
  have f51 := @GlobalTheory.thetaBundle_kTriv f10 f13 f3 f7 f45 f46 f47 f48 f50
  have f52 := @GlobalTheory.appellHumbert_normal_form_of_linear_exponent
  have f53 := @GlobalTheory.ThetaPositivity.re_form_pos_of_theta_ne_zero
  have f54 := @GlobalTheory.T.exists_thetaSeries_apply_ne_zero_of_large_form
  have f55 := @GlobalTheory.exists_complementary_theta_of_linear_map f10 f8 f52 f53 f54
  have f56 := @GlobalTheory.exists_isMonHom_of_map_periodLattice f31 f34 f35 f55 f3
  have hτ : τ ∈ SiegelH (Fin g) := ⟨hs, hp⟩
  obtain ⟨a, ha, rfl⟩ := exists_ofRealVec_of_half a₀ ha₀
  obtain ⟨b, hb, rfl⟩ := exists_ofRealVec_of_half b₀ hb₀
  have ea : (fun i => (ofRealVec a i).re) = a := funext fun i => Complex.ofReal_re _
  have eb : (fun i => (ofRealVec b i).re) = b := funext fun i => Complex.ofReal_re _
  rw [ea, eb]
  obtain ⟨N, hN, hE, hgen⟩ := f27 g τ hτ
  obtain ⟨X, ex, D, hX⟩ := f29 g τ hτ N hN
  have hq := f32 g τ hτ N hN hgen X ex D hX
  obtain ⟨inst, hc, hadd⟩ := f37 g τ hτ N hN X ex D hX hq
  obtain ⟨hab, hsm⟩ := f41 g τ hτ N hN X ex D hX hq hc
  obtain ⟨L, u, hL, hu⟩ := f42 g τ hτ N hN X ex D hX hq hE hadd a b ha hb
  obtain ⟨hr, hsy, th, hth⟩ := f43 g τ hτ N hN X ex D hX hq hE hadd a b ha hb L u hL hu
  have ham := f44 g τ hτ N hN X ex D hX hq hE hadd a b ha hb L u hL hu
  have hk := f51 g τ hτ N hN X ex D hX hq hE hadd a b ha hb L u hL hu hab hsm
  have hend := f56 g τ hτ N hN X ex D hX hq hadd
  have hs' := hsec g τ hτ N hN X ex D hX hq hE hadd a b ha hb L u hL hu hab hsm
  have hv' := hva g τ hτ N hN X ex D hX hq hE hadd a b ha hb L u hL hu hab hsm hs'
  obtain ⟨hex, hΛ, -⟩ := hu
  subst hex
  have htan : (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v := by
    refine f49 X L g u (f45 X L g u hsm fun w hw => ?_)
    obtain ⟨-, -, -, -, -, hD, hcov⟩ := hX
    have hN1 : 1 ≤ N := by omega
    have hmem : (u.ex 0).left (default : PrimeSpectrum ℂ) ∈ ⨆ c, D c := by rw [hcov]; trivial
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
    have hc' := (top_le_preimage_iff_mem _ _).2 hc
    obtain ⟨-, -, hDc, r, hr, -⟩ := hD c
    exact f13 g τ hτ N hN 0 w _ fun f hf => fderiv_eq_mul_of_ratio _
      (fun c => ((f3 g τ hτ N hN1).1 c).1) c 0 w ((hDc 0).1 hc')
      (fun c' z => valAt' (u.ex z).left (D c) (r c')) hr (fun c' => hw _ _ hc') f (f7 g τ hτ N hN1 f hf)
  refine ⟨{ A := X, isAb := hab, g := g, smoothDim := hsm, L := L, isLB := hL, rigid := hr, sym := hsy,
            ample := ham, ktriv := hk }, u, th, rfl, fun z => (hΛ z).trans (TorusAlg.mem_periodLattice_iff z),
    htan, ?_, hs', hv', fun F hF => ?_⟩
  · rw [thetaChar_ofRealVec_eq_theta]
    exact hth
  · exact hend F fun l hl => (hΛ _).1 (hF l ((hΛ _).2 hl))

end GlobalTheory
