module

public import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoboundaryCriterion
public import ReciprocityTheory.SemistableReduction.LemmaH
public import Lemmata.GeneralBFactBisAlt.Imports

@[expose] public section

section -- merged from ReciprocityTheory.SemistableReduction.SemiDegSt
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def wittMat {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun i j =>
    if (i : ℕ) + j + 1 = r ∧ ((i : ℕ) < m ∨ (j : ℕ) < m) then 1
    else if i = j ∧ m ≤ (i : ℕ) ∧ (i : ℕ) + m < r then g i else 0

def WittBasisStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r), S.G.det ≠ 0 →
    ∃ (P : Matrix (Fin r) (Fin r) K) (m : ℕ) (g : Fin r → K), P.det ≠ 0 ∧ 2 * m ≤ r ∧
      (P.map S.c)ᵀ * S.G * P = wittMat r m g ∧
      ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
        ∑ i, S.c (t i) * g i * t i = 0 → t = 0

def spanIdx {K : Type} [Field K] [NumberField K] {r k : ℕ} (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : ℕ :=
  (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup

def hGram {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i j => S.h (b i) (b j)

def LatDegBasisStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r k : ℕ) (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (B : Submodule (𝓞 K) (Fin r → K)) (b b' : Fin k → Fin r → K),
    (∀ σ, (H σ).PosDef) → B.FG → IsKBasisIn B b → IsKBasisIn B b' →
    latDeg H B b = latDeg H B b'

def IntegralIndexStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r k : ℕ) (S : HermForm K r)
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K),
    B.FG → IsKBasisIn B b → IsIntegralOn S B → (hGram S b).det ≠ 0 →
    ((spanIdx B b : ℕ) : ℝ) ^ 2 ≤ |((Algebra.norm ℚ (hGram S b).det : ℚ) : ℝ)|

def SelfDualIndexStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (b : Fin r → Fin r → K),
    IsLattice L → IsSelfDual S L → IsKBasisIn L b →
    |((Algebra.norm ℚ (hGram S b).det : ℚ) : ℝ)| ≤ ((spanIdx L b : ℕ) : ℝ) ^ 2

def cutSub (K : Type) [Field K] [NumberField K] (r e : ℕ) : Submodule (𝓞 K) (Fin r → K) := UpperTheory.Reformulated.B.FirstCoordinatesSubmodule.cutSub K r e

def projGe (K : Type) [Field K] [NumberField K] (r e : ℕ) : (Fin r → K) →ₗ[𝓞 K] (Fin r → K) where
  toFun x i := if e ≤ (i : ℕ) then x i else 0
  map_add' x y := by
    funext i
    by_cases h : e ≤ (i : ℕ) <;> simp [h]
  map_smul' a x := by
    funext i
    by_cases h : e ≤ (i : ℕ) <;> simp [h]

def diagMet {K : Type} [Field K] [NumberField K] {r : ℕ} (δ : (K →+* ℂ) → Fin r → ℝ) :
    (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ :=
  fun σ => Matrix.diagonal fun i => ((δ σ i : ℝ) : ℂ)

def GradedExtStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r e k k₀ k₁ : ℕ) (δ : (K →+* ℂ) → Fin r → ℝ)
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (b₀ : Fin k₀ → Fin r → K)
    (b₁ : Fin k₁ → Fin r → K),
    (∀ σ i, 0 < δ σ i) → B.FG → IsKBasisIn B b → IsKBasisIn (B ⊓ cutSub K r e) b₀ →
    IsKBasisIn (B.map (projGe K r e)) b₁ →
    latDeg (diagMet δ) B b ≤
      latDeg (diagMet δ) (B ⊓ cutSub K r e) b₀ + latDeg (diagMet δ) (B.map (projGe K r e)) b₁

def AbsDetStatement : Prop :=
  ∀ (n : ℕ) (A C : Matrix (Fin n) (Fin n) ℂ), A.PosDef → C.IsHermitian →
    (∀ v : Fin n → ℂ, ‖star v ⬝ᵥ (C *ᵥ v)‖ ≤ (star v ⬝ᵥ (A *ᵥ v)).re) → ‖C.det‖ ≤ A.det.re

end ReciprocityTheory.MultiplicativeHeights
end
end

section -- merged from ReciprocityTheory.SemistableReduction.LagrangeIdealLiftsFact
namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory NumberField

theorem gauss_abs_log_support_finite {K : Type*} [Field K] [NumberField K] {σ : Type*}
    (f : MvPolynomial σ K) (hf : f ≠ 0) :
    (Function.support fun w : FinitePlace K => Real.log (gaussAbs w f)).Finite := by
  have hfin : (⋃ s ∈ f.support, Function.mulSupport fun w : FinitePlace K => w (f.coeff s)).Finite :=
    Set.Finite.biUnion f.support.finite_toSet fun s hs =>
      FinitePlace.hasFiniteMulSupport (MvPolynomial.mem_support_iff.1 hs)
  refine hfin.subset fun w hw => ?_
  by_contra hnot
  apply hw
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hnot
  have h1 : gaussAbs w f = 1 := by
    apply le_antisymm
    · refine gauss_abs_le_of_coeff_le w f zero_le_one fun s => ?_
      by_cases hs : s ∈ f.support
      · exact (hnot s hs).le
      · rw [MvPolynomial.notMem_support_iff.1 hs, map_zero]
        exact zero_le_one
    · obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w f hf
      rw [h, hnot s hs]
  simp [h1]

theorem isMultiHomogeneous_map_ring {K : Type*} [Field K] {B n : ℕ} (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) K) (hf : IsMultiHomogeneous a f) (φ : K →+* ℂ) :
    IsMultiHomogeneous a (MvPolynomial.map φ f) := by
  unfold IsMultiHomogeneous at hf ⊢
  first
  | exact fun d hd => hf d (by rwa [MvPolynomial.support_map_of_injective _ φ.injective] at hd)
  | exact fun b => (hf b).map φ
  | simpa [MvPolynomial.support_map_of_injective _ φ.injective] using hf
  | (intro d hd
     simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map, ne_eq, map_eq_zero] at hd
     exact hf d (by simpa using hd))

theorem sphere_mean_mul_multihomogeneous (hInt : SphereLogIntegrableStatement) (B n : ℕ) (a a' : Fin B → ℕ)
    (F G : MvPolynomial (Fin B × Fin n) ℂ) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hF : IsMultiHomogeneous a F) (hG : IsMultiHomogeneous a' G) :
    blockSphereMean B n (F * G) = blockSphereMean B n F + blockSphereMean B n G := by
  unfold blockSphereMean
  rw [← integral_add (hInt B n a F hF0 hF) (hInt B n a' G hG0 hG)]
  refine integral_congr_ae ?_
  filter_upwards [ae_blockSphere_eval_ne_zero B n a F hF0 hF, ae_blockSphere_eval_ne_zero B n a' G hG0 hG]
    with z hz1 hz2
  rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hz1) (norm_ne_zero_iff.2 hz2)]

theorem gauss_height_mul_multihomogeneous (hInt : SphereLogIntegrableStatement) {K : Type*} [Field K] [NumberField K]
    (B n : ℕ) (a a' : Fin B → ℕ) (f g : MvPolynomial (Fin B × Fin n) K) (hf : f ≠ 0) (hg : g ≠ 0)
    (haf : IsMultiHomogeneous a f) (hbg : IsMultiHomogeneous a' g) :
    h0 (f * g) = h0 f + h0 g := by
  unfold h0
  have hfin : ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w (f * g)) =
      ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w f) + ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w g) := by
    rw [← finsum_add_distrib (gauss_abs_log_support_finite f hf) (gauss_abs_log_support_finite g hg)]
    refine finsum_congr fun w => ?_
    rw [gauss_abs_mul w f g hf hg, Real.log_mul (gauss_abs_pos_of_ne_zero w f hf).ne'
      (gauss_abs_pos_of_ne_zero w g hg).ne']
  have hinf : ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ (f * g)) =
      ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ f) +
        ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ g) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun φ _ => ?_
    have hinj := MvPolynomial.map_injective φ φ.injective (σ := Fin B × Fin n)
    rw [map_mul]
    exact sphere_mean_mul_multihomogeneous hInt B n a a' _ _
      (fun h => hf (hinj (by rw [h, map_zero])))
      (fun h => hg (hinj (by rw [h, map_zero])))
      (isMultiHomogeneous_map_ring a f haf φ) (isMultiHomogeneous_map_ring a' g hbg φ)
  rw [hfin, hinf]
  ring

theorem gauss_height_const_eq_zero {K : Type*} [Field K] [NumberField K] (B n : ℕ) (hn : 0 < n) (c : K)
    (hc : c ≠ 0) : h0 (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) = 0 := by
  unfold h0

  have hG : ∀ w : FinitePlace K, gaussAbs w (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) = w c := by
    intro w
    apply le_antisymm
    · refine gauss_abs_le_of_coeff_le w _ (apply_nonneg w c) fun s => ?_
      rw [MvPolynomial.coeff_C]
      split_ifs
      · exact le_rfl
      · rw [map_zero]; exact apply_nonneg w c
    · have := coeff_le_gauss_abs w (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) 0
      rwa [MvPolynomial.coeff_C, if_pos rfl] at this
  simp_rw [hG]

  have hP : IsProbabilityMeasure (blockSphereProb B n) := by
    have : NeZero n := ⟨hn.ne'⟩
    have hne : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
      rw [Ne, Measure.measure_univ_eq_zero]
      exact Measure.toSphere_ne_zero _
    have : IsProbabilityMeasure (sphereProb n) := by
      unfold sphereProb
      exact ProbabilityTheory.cond_isProbabilityMeasure hne
    unfold blockSphereProb
    infer_instance
  have hM : ∀ φ : K →+* ℂ, blockSphereMean B n
      (MvPolynomial.map φ (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K)) = Real.log ‖φ c‖ := by
    intro φ
    unfold blockSphereMean
    simp [MvPolynomial.map_C, MvPolynomial.eval_C]
  simp_rw [hM]

  have hmul : (Function.mulSupport fun w : FinitePlace K => w c).Finite :=
    FinitePlace.hasFiniteMulSupport hc
  have h1 : ∑ᶠ w : FinitePlace K, Real.log (w c) = Real.log (∏ᶠ w : FinitePlace K, w c) := by
    rw [finsum_eq_sum_of_support_subset (s := hmul.toFinset),
      finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp),
      Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hc).ne')]
    intro w hw
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    simp [h1]
  have h2 : ∑ φ : K →+* ℂ, Real.log ‖φ c‖ = Real.log |Algebra.norm ℚ c| := by
    rw [← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 hc))]
    congr 1
    have := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ c)
    rw [norm_prod] at this
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => ‖φ c‖) (fun φ => ‖φ c‖)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← this]
    rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2, FinitePlace.prod_eq_inv_abs_norm hc]
  push_cast
  rw [Real.log_inv, neg_add_cancel, zero_div]

theorem gauss_height_add_of_sphere (hInt : SphereLogIntegrableStatement) : HeightAdditiveStatement := by
  intro K _ _ B n a a' f g hn hf hg haf hbg
  refine ⟨gauss_height_mul_multihomogeneous hInt B n a a' f g hf hg haf hbg, fun c hc => ?_⟩
  have hC : IsMultiHomogeneous (fun _ : Fin B => 0) (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) := by
    intro s hs b
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hs
    split_ifs at hs with h
    · subst h; simp
    · exact absurd rfl hs
  have hC0 : (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) ≠ 0 := by
    rwa [Ne, MvPolynomial.C_eq_zero]
  rw [gauss_height_mul_multihomogeneous hInt B n _ a _ f hC0 hf hC haf, gauss_height_const_eq_zero B n hn c hc, zero_add]

end ReciprocityTheory.MultiplicativeHeights
end

section -- merged from ReciprocityTheory.SemistableReduction.CauchyInequalityOnTorus
namespace ReciprocityTheory.MultiplicativeHeights

theorem cauchy_inequality_on_torus : CauchyTorusStatement := by
  intro K _ _ _ K₀ hK₀ n c hc hτ χ
  by_contra hχ
  push_neg at hχ
  have hev : ∀ᶠ ψ in Filter.cofinite, ‖c ψ‖ < 1 / 2 := hc.eventually (gt_mem_nhds (by norm_num))
  have hFfin : {ψ | ¬ ‖c ψ‖ < 1 / 2}.Finite := Filter.eventually_cofinite.1 hev
  set F := hFfin.toFinset with hFdef
  have hχF : χ ∈ F := by
    rw [Set.Finite.mem_toFinset]
    show ¬ ‖c χ‖ < 1 / 2
    linarith
  obtain ⟨χm, hχmF, hmax⟩ := F.exists_max_image (fun ψ => ‖c ψ‖) ⟨χ, hχF⟩
  have hgt : 1 < ‖c χm‖ := lt_of_lt_of_le hχ (hmax χ hχF)
  have hglob : ∀ ψ, ‖c ψ‖ ≤ ‖c χm‖ := by
    intro ψ
    by_cases hψ : ψ ∈ F
    · exact hmax ψ hψ
    · have h2 : ‖c ψ‖ < 1 / 2 := by
        rw [Set.Finite.mem_toFinset] at hψ
        simpa using hψ
      linarith
  set lam := c χm with hlam
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h, norm_zero] at hgt
    linarith
  set a : (Fin n → ℤ) → K := fun ψ => c ψ / lam with hadef
  have ha : ∀ ψ, ‖a ψ‖ ≤ 1 := by
    intro ψ
    simp only [hadef, norm_div]
    exact (div_le_one (norm_pos_iff.2 hlam0)).2 (hglob ψ)
  have ha0 : ‖a χm‖ = 1 := by
    simp only [hadef, norm_div]
    exact div_self (norm_ne_zero_iff.2 hlam0)
  obtain ⟨τ, hτu, hτ1⟩ := exists_torus_point_one_le_norm_sum K₀ hK₀ F a ha χm hχmF ha0
  have hprodnorm : ∀ ψ : Fin n → ℤ, ‖∏ i, τ i ^ ψ i‖ = 1 := by
    intro ψ
    rw [norm_prod]
    exact Finset.prod_eq_one fun i _ => by rw [norm_zpow, (hτu i).2, one_zpow]
  have hSF : ∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i = lam * ∑ ψ ∈ F, a ψ * ∏ i, τ i ^ ψ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    simp only [hadef]
    field_simp
  have hSFn : ‖lam‖ ≤ ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖ := by
    rw [hSF, norm_mul]
    calc ‖lam‖ = ‖lam‖ * 1 := (mul_one _).symm
      _ ≤ ‖lam‖ * ‖∑ ψ ∈ F, a ψ * ∏ i, τ i ^ ψ i‖ := mul_le_mul_of_nonneg_left hτ1 (norm_nonneg _)
  have hsum : Summable (fun ψ => c ψ * ∏ i, τ i ^ ψ i) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_mul, hprodnorm] using hc
  have hsplit := hsum.sum_add_tsum_compl (s := F)
  have htail : ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖ ≤ 1 / 2 := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by norm_num) fun ψ => ?_
    rw [norm_mul, hprodnorm, mul_one]
    have hψ : (ψ : Fin n → ℤ) ∉ F := fun h => ψ.2 (Finset.mem_coe.2 h)
    rw [Set.Finite.mem_toFinset] at hψ
    simp only [Set.mem_setOf_eq, not_not] at hψ
    exact le_of_lt hψ
  have hne : ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖ ≠
      ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖ := by
    intro h
    linarith
  have htot := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [hsplit] at htot
  have h1 := hτ τ hτu
  unfold torusSum at h1
  rw [htot] at h1
  have h3 := le_max_left ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖
    ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖
  linarith

end ReciprocityTheory.MultiplicativeHeights
end

section -- merged from ReciprocityTheory.SemistableReduction.ExistsIntSmulMemSpan
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

namespace DegAdd

open NumberField

theorem exists_int_smul_mem_span {K : Type} [Field K] [NumberField K] {r n : ℕ}
    (v : Fin n → Fin r → K) {x : Fin r → K} (hx : x ∈ Submodule.span K (Set.range v)) :
    ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 K) (Set.range v) := by
  first | exact Bl.general_b_fact_bis_other.goal1 .. | (apply Bl.general_b_fact_bis_other.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_bis_other.goal1 <;> assumption)

theorem relIndex_ne_zero_of_fg {K : Type} [Field K] [NumberField K] {r n : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : L.FG) (v : Fin n → Fin r → K)
    (hv : ∀ x ∈ L, x ∈ Submodule.span K (Set.range v)) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
  set N := (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.addSubgroupOf L.toAddSubgroup
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hL
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 K) L
  let f : L →+ (L.toAddSubgroup ⧸ N) :=
    { toFun := fun x => QuotientAddGroup.mk (⟨x.1, x.2⟩ : L.toAddSubgroup)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have : Module.Finite ℤ (L.toAddSubgroup ⧸ N) := by
    refine Module.Finite.of_surjective f.toIntLinearMap ?_
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨⟨y, hy⟩, rfl⟩
  have : Finite (L.toAddSubgroup ⧸ N) := by
    apply Module.finite_of_fg_torsion
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨d, hd, hdy⟩ := exists_int_smul_mem_span v (hv y hy)
    refine ⟨⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩, ?_⟩
    change (d • (QuotientAddGroup.mk (⟨y, hy⟩ : L.toAddSubgroup) : L.toAddSubgroup ⧸ N)) = 0
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hdy
  exact AddSubgroup.index_ne_zero_of_finite

theorem range_fin_append {α : Type} {k m : ℕ} (b : Fin k → α) (c : Fin m → α) :
    Set.range (Fin.append b c) = Set.range b ∪ Set.range c := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i => exact Or.inl ⟨i, (Fin.append_left b c i).symm⟩
    | right j => exact Or.inr ⟨j, (Fin.append_right b c j).symm⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd m i, Fin.append_left b c i⟩
    · exact ⟨Fin.natAdd k j, Fin.append_right b c j⟩

theorem fin_append_comp_equiv {α : Type} {k m : ℕ} (b : Fin k → α) (c : Fin m → α) :
    Fin.append b c ∘ finSumFinEquiv = Sum.elim b c := by
  funext i
  cases i <;> simp

theorem indep_parts {K : Type} [Field K] {r k m : ℕ}
    {b : Fin k → Fin r → K} {c : Fin m → Fin r → K} (h : LinearIndependent K (Fin.append b c)) :
    LinearIndependent K b ∧ LinearIndependent K c ∧
      Disjoint (Submodule.span K (Set.range b)) (Submodule.span K (Set.range c)) := by
  have h2 := h.comp finSumFinEquiv finSumFinEquiv.injective
  rw [fin_append_comp_equiv] at h2
  have h3 := linearIndependent_sum.mp h2
  simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr] using h3

theorem index_split {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hb : ∀ i, b i ∈ L) (hc : ∀ j, c j ∈ L)
    (hdis : Disjoint (Submodule.span K (Set.range b)) (Submodule.span K (Set.range c))) :
    (Submodule.span (𝓞 K) (Set.range (Fin.append b c))).toAddSubgroup.relIndex L.toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex (satSub L b).toAddSubgroup *
      (satSub L b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex
        L.toAddSubgroup := by
  set Sb := Submodule.span (𝓞 K) (Set.range b)
  set Sc := Submodule.span (𝓞 K) (Set.range c)
  set S := satSub L b
  have hA : Submodule.span (𝓞 K) (Set.range (Fin.append b c)) = Sb ⊔ Sc := by
    rw [range_fin_append, Submodule.span_union]
  have hSbS : Sb ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨hb i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hScL : Sc ≤ L := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hc j
  have hSL : S ≤ L := inf_le_left
  have hmeet : ∀ x, x ∈ Sb ⊔ Sc → x ∈ S → x ∈ Sb := by
    intro x hx1 hx2
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx1
    have hyK : y ∈ Submodule.span K (Set.range b) :=
      Submodule.span_le_restrictScalars (𝓞 K) K _ hy
    have hzK : z ∈ Submodule.span K (Set.range c) :=
      Submodule.span_le_restrictScalars (𝓞 K) K _ hz
    have hxK : y + z ∈ Submodule.span K (Set.range b) := hx2.2
    have hz' : z ∈ Submodule.span K (Set.range b) := by
      have h := Submodule.sub_mem _ hxK hyK
      simpa using h
    have hz0 : z = 0 := Submodule.disjoint_def.mp hdis z hz' hzK
    simpa [hz0] using hy
  have hinf : (Sb ⊔ Sc).toAddSubgroup ⊓ S.toAddSubgroup = Sb.toAddSubgroup := by
    ext x
    constructor
    · intro h
      exact hmeet x (AddSubgroup.mem_inf.mp h).1 (AddSubgroup.mem_inf.mp h).2
    · intro h
      exact AddSubgroup.mem_inf.mpr ⟨(le_sup_left : Sb ≤ Sb ⊔ Sc) h, hSbS h⟩
  have key : (Sb ⊔ Sc).toAddSubgroup.relIndex (S ⊔ Sc).toAddSubgroup =
      Sb.toAddSubgroup.relIndex S.toAddSubgroup := by
    have hsup : (S ⊔ Sc).toAddSubgroup = S.toAddSubgroup ⊔ (Sb ⊔ Sc).toAddSubgroup := by
      rw [← Submodule.sup_toAddSubgroup, ← sup_assoc, sup_eq_left.mpr hSbS]
    rw [hsup, AddSubgroup.relIndex_sup_right, ← hinf, AddSubgroup.inf_relIndex_right]
  have le1 : (Sb ⊔ Sc).toAddSubgroup ≤ (S ⊔ Sc).toAddSubgroup :=
    fun x hx => (sup_le_sup_right hSbS Sc) hx
  have le2 : (S ⊔ Sc).toAddSubgroup ≤ L.toAddSubgroup := fun x hx => (sup_le hSL hScL) hx
  rw [hA, ← AddSubgroup.relIndex_mul_relIndex _ _ _ le1 le2, key]

end DegAdd

end ReciprocityTheory.MultiplicativeHeights
end
end

section -- merged from ReciprocityTheory.SemistableReduction.Unipotent
section -- merged from ReciprocityTheory.SemistableReduction.UnipotentB
namespace ReciprocityTheory.MultiplicativeHeights

open Matrix

theorem unip_normSq_pow_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) (n : ℕ) (u : Fin r → ℂ) :
    normSq ((A ^ n) *ᵥ u) ≤ c ^ n * normSq u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, pow_succ']
    calc normSq (A *ᵥ (A ^ n *ᵥ u)) ≤ c * normSq (A ^ n *ᵥ u) := hA _
      _ ≤ c * (c ^ n * normSq u) := mul_le_mul_of_nonneg_left ih hc
      _ = c * c ^ n * normSq u := by ring

theorem unip_normSq_col {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (j : Fin r) :
    normSq (M *ᵥ Pi.single j 1) = ∑ i, ‖M i j‖ ^ 2 := by
  unfold normSq
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_single_one]
  rfl

theorem unip_normSq_single {r : ℕ} (j : Fin r) : normSq (Pi.single j (1 : ℂ)) = 1 := by
  unfold normSq
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem unip_diag_sq_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) (n : ℕ) (i : Fin r) :
    ‖(A ^ n) i i‖ ^ 2 ≤ c ^ n := by
  have h1 := unip_normSq_pow_le A c hc hA n (Pi.single i 1)
  rw [unip_normSq_col, unip_normSq_single, mul_one] at h1
  refine le_trans ?_ h1
  exact Finset.single_le_sum (f := fun k => ‖(A ^ n) k i‖ ^ 2) (fun k _ => by positivity)
    (Finset.mem_univ i)

theorem unip_hs_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) :
    ∑ a, ∑ b, ‖A a b‖ ^ 2 ≤ r * c := by
  rw [Finset.sum_comm]
  calc ∑ b, ∑ a, ‖A a b‖ ^ 2 = ∑ b : Fin r, normSq (A *ᵥ Pi.single b 1) :=
        Finset.sum_congr rfl fun b _ => (unip_normSq_col A b).symm
    _ ≤ ∑ _b : Fin r, c := by
        refine Finset.sum_le_sum fun b _ => ?_
        have h := hA (Pi.single b 1)
        rwa [unip_normSq_single, mul_one] at h
    _ = r * c := by simp

theorem unip_hs_sub_one {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) :
    ∑ a, ∑ b, ‖(A - 1) a b‖ ^ 2 = ∑ a, ∑ b, ‖A a b‖ ^ 2 - 2 * A.trace.re + r := by
  have key : ∀ a b, ‖(A - 1) a b‖ ^ 2 =
      ‖A a b‖ ^ 2 - (if a = b then 2 * (A a b).re - 1 else 0) := by
    intro a b
    by_cases h : a = b
    · subst h
      simp only [Matrix.sub_apply, Matrix.one_apply_eq, if_true, Complex.sq_norm,
        Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      ring
    · simp [Matrix.sub_apply, Matrix.one_apply_ne h, h]
  simp_rw [key, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Matrix.trace, Complex.re_sum]
  simp [Finset.sum_sub_distrib, Finset.mul_sum]
  ring

theorem unip_exp_bound (r : ℕ) (hr : 1 ≤ r) : (r : ℝ) * (Real.exp (2 / (3 * r)) - 1) < 1 := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hx0 : 0 < 2 / (3 * (r : ℝ)) := by positivity
  set x : ℝ := 2 / (3 * (r : ℝ)) with hx
  have hxr : (r : ℝ) * x = 2 / 3 := by rw [hx]; field_simp
  have hx1 : x ≤ 2 / 3 := by nlinarith
  have hb := Real.exp_bound (x := x) (by rw [abs_of_pos hx0]; linarith) (n := 4) (by norm_num)
  rw [abs_of_pos hx0] at hb
  have hup := (abs_le.mp hb).2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hup
  norm_num at hup
  have hmain : Real.exp x - 1 < 3 / 2 * x := by
    nlinarith [pow_pos hx0 2, pow_pos hx0 3, pow_pos hx0 4, mul_le_mul_of_nonneg_left hx1 (le_of_lt (pow_pos hx0 3))]
  have hr0 : (0 : ℝ) < r := by linarith
  calc (r : ℝ) * (Real.exp x - 1) < r * (3 / 2 * x) := mul_lt_mul_of_pos_left hmain hr0
    _ = 1 := by rw [show (r : ℝ) * (3 / 2 * x) = 3 / 2 * (r * x) by ring, hxr]; norm_num

end ReciprocityTheory.MultiplicativeHeights
end

section -- merged from ReciprocityTheory.SemistableReduction.UnipotentA
namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial Matrix

theorem unip_trace_aeval_zero {K : Type*} [Field K] {r : ℕ} (N : Matrix (Fin r) (Fin r) K)
    (hN : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) (P : K[X]) (hP : P.natDegree ≤ r) :
    (aeval N P).trace = P.coeff 0 * r := by
  rw [Polynomial.aeval_eq_sum_range, Matrix.trace_sum, Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp [Matrix.trace_one]
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Matrix.trace_smul, hN (i + 1) (by omega) (by omega), smul_zero]

theorem unip_idem_eq_zero {K : Type*} [Field K] [CharZero K] {r : ℕ} (E : Matrix (Fin r) (Fin r) K)
    (hE : E * E = E) (ht : E.trace = 0) : E = 0 := by
  set f := Matrix.toLin' E with hfdef
  have hf : LinearMap.IsProj (LinearMap.range f) f := by
    constructor
    · intro x
      exact LinearMap.mem_range_self f x
    · intro x hx
      obtain ⟨y, rfl⟩ := hx
      simp only [hfdef, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hE]
  have htr : LinearMap.trace K _ f = E.trace := by
    rw [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin r)),
      LinearMap.toMatrix_eq_toMatrix', hfdef, LinearMap.toMatrix'_toLin']
  have h0 : ((Module.finrank K (LinearMap.range f) : ℕ) : K) = 0 := by
    rw [← hf.trace, htr, ht]
  have h1 : Module.finrank K (LinearMap.range f) = 0 := by exact_mod_cast h0
  have h2 : LinearMap.range f = ⊥ := Submodule.finrank_eq_zero.mp h1
  have h3 : f = 0 := LinearMap.range_eq_bot.mp h2
  exact Matrix.toLin'.injective (h3.trans (map_zero _).symm)

theorem unip_pow_card_eq_zero {K : Type*} [Field K] [CharZero K] {r : ℕ} (N : Matrix (Fin r) (Fin r) K)
    (hN : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) : N ^ r = 0 := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact Subsingleton.elim _ _
  have hint : IsIntegral K N := IsIntegral.of_finite K N
  set m := minpoly K N with hm
  have hmon : m.Monic := minpoly.monic hint
  have hm0 : aeval N m = 0 := minpoly.aeval K N
  have hmdeg : m.natDegree ≤ r := by
    have h2 := Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly N)
      (Matrix.charpoly_monic N).ne_zero
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h2
  have hrK : (r : K) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hmc : m.coeff 0 = 0 := by
    have h := unip_trace_aeval_zero N hN m hmdeg
    rw [hm0, Matrix.trace_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hrK
  have hXm : X ∣ m := Polynomial.X_dvd_iff.mpr hmc
  obtain ⟨q, hq, hXq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd m hmon.ne_zero 0
  simp only [map_zero, sub_zero] at hq hXq
  set k := m.rootMultiplicity 0 with hkdef
  have hk : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero, one_mul] at hq
    exact hXq (hq ▸ hXm)
  have hcop : IsCoprime (X ^ k) q :=
    ((Polynomial.irreducible_X.coprime_iff_not_dvd).mpr hXq).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨P, hP⟩ : ∃ P : K[X], P = u * X ^ k := ⟨_, rfl⟩
  have hPP : aeval N P * aeval N P = aeval N P := by
    have hsub : P - 1 = -(v * q) := by rw [hP, ← huv]; ring
    have hfac : P * P - P = -(u * v) * m := by
      calc P * P - P = P * (P - 1) := by ring
        _ = -(u * v) * (X ^ k * q) := by rw [hsub, hP]; ring
        _ = -(u * v) * m := by rw [← hq]
    have h := congrArg (aeval N) hfac
    rw [map_sub, map_mul, map_mul, hm0, mul_zero] at h
    exact sub_eq_zero.mp h
  obtain ⟨P', hP'⟩ : ∃ P' : K[X], P' = P %ₘ m := ⟨_, rfl⟩
  have hdiv : P' + m * (P /ₘ m) = P := by
    rw [hP']
    first
      | exact Polynomial.modByMonic_add_div P hmon
      | exact Polynomial.modByMonic_add_div P m
  have hPeq : aeval N P' = aeval N P := by
    have h := congrArg (aeval N) hdiv
    rw [map_add (f := _), map_mul, hm0, zero_mul, add_zero] at h
    exact h
  have hP'deg : P'.natDegree ≤ r := by
    rw [hP']
    refine le_trans ?_ hmdeg
    first
      | exact Polynomial.natDegree_modByMonic_le P hmon
      | exact Polynomial.natDegree_modByMonic_le P m
  have hP'0 : P'.coeff 0 = 0 := by
    have h := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 0) hdiv
    simp only [Polynomial.coeff_add, Polynomial.mul_coeff_zero, hmc, zero_mul, add_zero] at h
    rw [h, hP, Polynomial.mul_coeff_zero, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  have htr : (aeval N P).trace = 0 := by
    rw [← hPeq, unip_trace_aeval_zero N hN P' hP'deg, hP'0, zero_mul]
  have hE : aeval N P = 0 := unip_idem_eq_zero _ hPP htr
  have hmP : m ∣ P := minpoly.dvd K N hE
  have hqu : q ∣ u := by
    rw [hq, hP, mul_comm u] at hmP
    exact (mul_dvd_mul_iff_left (pow_ne_zero k Polynomial.X_ne_zero)).mp hmP
  have hq1 : IsUnit q := by
    apply isUnit_of_dvd_one
    rw [← huv]
    exact (dvd_mul_of_dvd_left hqu _).add (dvd_mul_left q v)
  have hNk : N ^ k = 0 := by
    have h := hm0
    rw [hq, map_mul, map_pow, Polynomial.aeval_X] at h
    exact ((hq1.map (aeval N)).mul_left_eq_zero).mp h
  have hkm : k ≤ m.natDegree := by
    have h := Polynomial.natDegree_le_of_dvd ⟨q, hq⟩ hmon.ne_zero
    rwa [Polynomial.natDegree_X_pow] at h
  exact pow_eq_zero_of_le (le_trans hkm hmdeg) hNk

end ReciprocityTheory.MultiplicativeHeights
end

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField Polynomial

theorem unip_conj_pow {r : ℕ} (Q M : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.det ≠ 0) (n : ℕ) :
    (Q * M * Q⁻¹) ^ n = Q * M ^ n * Q⁻¹ := by
  have hinv : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ)
  have hinv' : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ)
  induction n with
  | zero => simp [hinv']
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    calc Q * M ^ n * Q⁻¹ * (Q * M * Q⁻¹) = Q * M ^ n * (Q⁻¹ * Q) * M * Q⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = Q * (M ^ n * M) * Q⁻¹ := by rw [hinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem unip_trace_conj {r : ℕ} (Q M : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.det ≠ 0) :
    (Q * M * Q⁻¹).trace = M.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ), Matrix.one_mul]

theorem unip_trace_map {K : Type*} [Field K] {r : ℕ} (σ : K →+* ℂ) (M : Matrix (Fin r) (Fin r) K) :
    (M.map σ).trace = σ M.trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem unip_map_pow {K : Type*} [Field K] {r : ℕ} (σ : K →+* ℂ) (M : Matrix (Fin r) (Fin r) K)
    (n : ℕ) : (M.map σ) ^ n = (M ^ n).map σ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ, Matrix.map_mul]

theorem unip_trace_aeval_one {K : Type*} [Field K] {r : ℕ} (γ : Matrix (Fin r) (Fin r) K)
    (hγ : ∀ k, k ≤ r → (γ ^ k).trace = r) (P : K[X]) (hP : P.natDegree ≤ r) :
    (aeval γ P).trace = r * P.eval 1 := by
  have hlt : P.natDegree < r + 1 := Nat.lt_succ_of_le hP
  rw [Polynomial.aeval_eq_sum_range' hlt, Matrix.trace_sum, Polynomial.eval_eq_sum_range' hlt,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Matrix.trace_smul, hγ k hk', smul_eq_mul, one_pow, mul_one, mul_comm]

theorem unipotent_holds : UnipotentStatement := by
  intro K _ _ r g γ Q hT hg hQ hA
  set A : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ := fun σ => Q σ * γ.map σ * (Q σ)⁻¹ with hAdef
  have hc : 0 ≤ Real.exp (2 / (3 * (r : ℝ))) := (Real.exp_pos _).le
  have htrA : ∀ σ n, ((A σ) ^ n).trace = σ ((γ ^ n).trace) := by
    intro σ n
    simp only [hAdef]
    rw [unip_conj_pow _ _ (hQ σ), unip_trace_conj _ _ (hQ σ), unip_map_pow, unip_trace_map]
  have htrB : ∀ σ n, n ≤ r → ‖((A σ) ^ n).trace‖ ≤ r * Real.exp (1 / 3) := by
    intro σ n hn
    have hd : ∀ i, ‖((A σ) ^ n) i i‖ ≤ Real.exp (1 / 3) := by
      intro i
      have h1 := unip_diag_sq_le (A σ) _ hc (hA σ) n i
      have h2 : Real.exp (2 / (3 * (r : ℝ))) ^ n ≤ Real.exp (1 / 3) ^ 2 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        rcases Nat.eq_zero_or_pos r with hr | hr
        · subst hr
          have : n = 0 := by omega
          subst this; norm_num
        · have hr' : (0 : ℝ) < r := by exact_mod_cast hr
          have hn' : (n : ℝ) ≤ r := by exact_mod_cast hn
          calc (n : ℝ) * (2 / (3 * r)) = (2 / 3) * ((n : ℝ) / r) := by field_simp
            _ ≤ (2 / 3) * 1 := by gcongr; exact (div_le_one hr').mpr hn'
            _ = ((2 : ℕ) : ℝ) * (1 / 3) := by norm_num
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).mp (h1.trans h2)
    calc ‖((A σ) ^ n).trace‖ = ‖∑ i, ((A σ) ^ n) i i‖ := rfl
      _ ≤ ∑ i, ‖((A σ) ^ n) i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin r, Real.exp (1 / 3) := Finset.sum_le_sum (fun i _ => hd i)
      _ = r * Real.exp (1 / 3) := by simp
  have hT1 : ∀ n, 1 ≤ n → n ≤ r → (γ ^ n).trace = r := by
    intro n h1 h2
    obtain ⟨z, hz⟩ := hT n h1 h2
    by_cases hz0 : z = 0
    · rw [hz0] at hz
      simp only [map_zero, mul_zero] at hz
      exact sub_eq_zero.mp (by simpa using hz)
    · exfalso
      obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hz0
      have e1 : σ ((γ ^ n).trace - r) = (g : ℂ) * σ z := by rw [hz, map_mul, map_natCast]
      rw [map_sub, map_natCast, ← htrA σ n] at e1
      have hn1 : ‖((A σ) ^ n).trace - r‖ ≤ r * Real.exp (1 / 3) + r := by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_natCast]
        linarith [htrB σ n h2]
      rw [e1, norm_mul, Complex.norm_natCast] at hn1
      have : (g : ℝ) ≤ g * ‖σ z‖ := le_mul_of_one_le_right (Nat.cast_nonneg _) hσ
      nlinarith
  have hTall : ∀ k, k ≤ r → (γ ^ k).trace = r := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp [Matrix.trace_one]
    · exact hT1 k h hk
  have hN : ∀ k, 1 ≤ k → k ≤ r → ((γ - 1) ^ k).trace = 0 := by
    intro k h1 h2
    have := unip_trace_aeval_one γ hTall ((X - C 1) ^ k)
      (by rw [natDegree_pow, natDegree_X_sub_C, mul_one]; exact h2)
    simp only [map_pow, map_sub, aeval_X, map_one, eval_pow, eval_sub, eval_X, eval_one,
      sub_self] at this
    rw [this, zero_pow (by omega : k ≠ 0), mul_zero]
  refine ⟨unip_pow_card_eq_zero (γ - 1) hN, fun σ => ?_⟩
  have hinv' : Q σ * (Q σ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hQ σ))
  have heq : Q σ * (γ.map σ - 1) * (Q σ)⁻¹ = A σ - 1 := by
    simp only [hAdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hinv']
  rw [heq, unip_hs_sub_one]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  have htr1 : (A σ).trace = r := by
    have h7 := htrA σ 1
    rw [pow_one] at h7
    rw [h7, hT1 1 le_rfl hr, map_natCast]
  rw [htr1, Complex.natCast_re]
  have h5 := unip_hs_le (A σ) _ (hA σ)
  have h6 := unip_exp_bound r hr
  nlinarith

end ReciprocityTheory.MultiplicativeHeights
end

section -- merged from ReciprocityTheory.SemistableReduction.LatTest
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

end ReciprocityTheory.MultiplicativeHeights
end
end
