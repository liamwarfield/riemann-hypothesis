module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockProjectionFlagUnipotentRadical

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSmoothBumpWithTrigonometricExpansionStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSmoothBumpWithTrigonometricExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealAlgSep
namespace GlobalTheory.RealAlgebraCharacters

open Filter Topology

section
variable {X : Type} {B : Type} [AddCommGroup B] (χ : B → X → ℂ)

theorem span_mul (hadd : ∀ (a b : B) (x : X), χ (a + b) x = χ a x * χ b x)
    {f g : X → ℂ} (hf : f ∈ Submodule.span ℂ (Set.range χ))
    (hg : g ∈ Submodule.span ℂ (Set.range χ)) : f * g ∈ Submodule.span ℂ (Set.range χ) := by
  induction hf using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, rfl⟩ := hu
    induction hg using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨b, rfl⟩ := hv
      exact Submodule.subset_span ⟨a + b, funext fun x => hadd a b x⟩
    | zero => simp
    | add v w _ _ hv hw =>
      rw [mul_add]
      exact Submodule.add_mem _ hv hw
    | smul c v _ hv =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c hv
  | zero => simp
  | add u w _ _ hu hw =>
    rw [add_mul]
    exact Submodule.add_mem _ hu hw
  | smul c u _ hu =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hu


omit [AddCommGroup B] in
theorem span_bdd (hn : ∀ (a : B) (x : X), ‖χ a x‖ = 1)
    {f : X → ℂ} (hf : f ∈ Submodule.span ℂ (Set.range χ)) : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M := by
  induction hf using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, rfl⟩ := hu
    exact ⟨1, fun x => (hn a x).le⟩
  | zero => exact ⟨0, fun x => by simp⟩
  | add u w _ _ hu hw =>
    obtain ⟨M1, h1⟩ := hu
    obtain ⟨M2, h2⟩ := hw
    refine ⟨M1 + M2, fun x => ?_⟩
    show ‖u x + w x‖ ≤ M1 + M2
    exact (norm_add_le _ _).trans (add_le_add (h1 x) (h2 x))
  | smul c u _ hu =>
    obtain ⟨M, h⟩ := hu
    refine ⟨‖c‖ * M, fun x => ?_⟩
    show ‖c • u x‖ ≤ ‖c‖ * M
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (h x) (norm_nonneg _)

theorem chi_neg (hadd : ∀ (a b : B) (x : X), χ (a + b) x = χ a x * χ b x)
    (h0 : ∀ x, χ 0 x = 1) (hn : ∀ (a : B) (x : X), ‖χ a x‖ = 1) (b : B) (x : X) :
    χ (-b) x = (starRingEnd ℂ) (χ b x) := by
  have h1 : χ (-b) x * χ b x = 1 := by rw [← hadd, neg_add_cancel, h0]
  have h2 : χ (-b) x = (χ b x)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [h2, Complex.inv_def, Complex.normSq_eq_norm_sq, hn b x]
  simp

def realAlg [TopologicalSpace X] (hadd : ∀ (a b : B) (x : X), χ (a + b) x = χ a x * χ b x)
    (h0 : ∀ x, χ 0 x = 1) : Subalgebra ℝ C(X, ℝ) where
  carrier := {f | (fun x => ((f x : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range χ)}
  mul_mem' := by
    intro f g hf hg
    have := span_mul χ hadd hf hg
    show (fun x => (((f * g) x : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range χ)
    convert this using 1 <;> ext x <;> simp
  add_mem' := by
    intro f g hf hg
    have := (Submodule.span ℂ (Set.range χ)).add_mem hf hg
    show (fun x => (((f + g) x : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range χ)
    convert this using 1 <;> ext x <;> simp
  algebraMap_mem' := by
    intro r
    have h : χ 0 ∈ Submodule.span ℂ (Set.range χ) := Submodule.subset_span ⟨0, rfl⟩
    have := Submodule.smul_mem _ (r : ℂ) h
    show (fun x => (((algebraMap ℝ C(X, ℝ) r) x : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range χ)
    convert this using 1
    funext x
    simp [h0]

theorem realAlg_sep [TopologicalSpace X] (hc : ∀ b, Continuous (χ b))
    (hadd : ∀ (a b : B) (x : X), χ (a + b) x = χ a x * χ b x)
    (h0 : ∀ x, χ 0 x = 1) (hn : ∀ (a : B) (x : X), ‖χ a x‖ = 1)
    (hs : ∀ x y : X, x ≠ y → ∃ b, χ b x ≠ χ b y) : (realAlg χ hadd h0).SeparatesPoints := by
  intro x y hxy
  obtain ⟨b, hb⟩ := hs x y hxy
  have hneg : ∀ u, χ (-b) u = (starRingEnd ℂ) (χ b u) := fun u => chi_neg χ hadd h0 hn b u
  let fre : C(X, ℝ) := ⟨fun u => (χ b u).re, Complex.continuous_re.comp (hc b)⟩
  let fim : C(X, ℝ) := ⟨fun u => (χ b u).im, Complex.continuous_im.comp (hc b)⟩
  have hre : fre ∈ realAlg χ hadd h0 := by
    show (fun u => (((χ b u).re : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range χ)
    have he : (fun u => (((χ b u).re : ℝ) : ℂ)) = (1 / 2 : ℂ) • (χ b + χ (-b)) := by
      funext u
      simp only [Pi.smul_apply, Pi.add_apply, hneg, smul_eq_mul]
      rw [Complex.re_eq_add_conj]
      ring
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span ⟨b, rfl⟩)
      (Submodule.subset_span ⟨-b, rfl⟩))
  have him : fim ∈ realAlg χ hadd h0 := by
    show (fun u => (((χ b u).im : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range χ)
    have he : (fun u => (((χ b u).im : ℝ) : ℂ)) = (1 / (2 * Complex.I)) • (χ b - χ (-b)) := by
      funext u
      simp only [Pi.smul_apply, Pi.sub_apply, hneg, smul_eq_mul]
      rw [Complex.im_eq_sub_conj]
      ring
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨b, rfl⟩)
      (Submodule.subset_span ⟨-b, rfl⟩))
  by_cases hr : (χ b x).re = (χ b y).re
  · refine ⟨fim, ⟨fim, him, rfl⟩, fun heq => hb (Complex.ext hr heq)⟩
  · exact ⟨fre, ⟨fre, hre, rfl⟩, hr⟩

theorem step [TopologicalSpace X] (hc : ∀ b, Continuous (χ b))
    (hadd : ∀ (a b : B) (x : X), χ (a + b) x = χ a x * χ b x)
    (h0 : ∀ x, χ 0 x = 1) (hn : ∀ (a : B) (x : X), ‖χ a x‖ = 1)
    (hs : ∀ x y : X, x ≠ y → ∃ b, χ b x ≠ χ b y) (β : X → ℝ) (hβ : Continuous β)
    (hβ1 : ∀ u, 0 ≤ β u ∧ β u ≤ 1) {K : Set X} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ (s : Finset B) (c : B → ℂ), (∀ x, ‖∑ b ∈ s, c b * χ b x‖ ≤ 2) ∧
      ∀ x ∈ K, ‖∑ b ∈ s, c b * χ b x - (β x : ℂ)‖ ≤ 2 * ε := by
  obtain ⟨g, hgA, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (realAlg_sep χ hc hadd h0 hn hs) ⟨β, hβ⟩ hK hε
  obtain ⟨M, hM⟩ := span_bdd χ hn hgA
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-M) M (fun t => max 0 (min t 1))
    (by fun_prop) ε hε
  have hmem : Polynomial.aeval g p ∈ realAlg χ hadd h0 := by
    have : Algebra.adjoin ℝ {g} ≤ realAlg χ hadd h0 :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 hgA)
    exact this (Polynomial.aeval_mem_adjoin_singleton ℝ g)
  have hmem' : (fun x => (((Polynomial.aeval g p) x : ℝ) : ℂ)) ∈
      Submodule.span ℂ (Set.range χ) := hmem
  obtain ⟨c, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem'
  have hval : ∀ x, ∑ b ∈ c.support, c b * χ b x = ((p.eval (g x) : ℝ) : ℂ) := by
    intro x
    have := congrFun hcf x
    rw [Polynomial.aeval_continuousMap_apply] at this
    rw [← this, Finsupp.sum, Finset.sum_apply]
    simp
  have hnear : ∀ x, |p.eval (g x) - max 0 (min (g x) 1)| < ε := by
    intro x
    have := hM x
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    exact hp _ (abs_le.1 this)
  refine ⟨c.support, c, fun x => ?_, fun x hx => ?_⟩
  · rw [hval, Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_lt.1 (hnear x)
    have h2 : 0 ≤ max 0 (min (g x) 1) := le_max_left _ _
    have h3 : max 0 (min (g x) 1) ≤ 1 := max_le zero_le_one (min_le_right _ _)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]
  · rw [hval, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_lt.1 (hnear x)
    have h2 : |g x - β x| < ε := hg x hx
    have h3 := abs_lt.1 h2
    have h4 := hβ1 x
    have h5 : max 0 (min (g x) 1) ≤ β x + ε :=
      max_le (by linarith [h4.1]) ((min_le_left _ _).trans (by linarith [h3.2]))
    have h6 : β x - ε ≤ max 0 (min (g x) 1) :=
      le_max_of_le_right (le_min (by linarith [h3.1]) (by linarith [h4.2]))
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]

end

theorem main {X : Type} [PseudoMetricSpace X] [ProperSpace X] (x₀ : X) {B : Type}
    [AddCommGroup B] (χ : B → X → ℂ) (hc : ∀ b, Continuous (χ b))
    (hadd : ∀ (a b : B) (x : X), χ (a + b) x = χ a x * χ b x)
    (h0 : ∀ x, χ 0 x = 1) (hn : ∀ (a : B) (x : X), ‖χ a x‖ = 1)
    (hs : ∀ x y : X, x ≠ y → ∃ b, χ b x ≠ χ b y) (β : X → ℝ) (hβ : Continuous β)
    (hβ1 : ∀ u, 0 ≤ β u ∧ β u ≤ 1) :
    ∃ (s : ℕ → Finset B) (c : ℕ → B → ℂ),
      (∀ (n : ℕ) (x : X), ‖∑ b ∈ s n, c n b * χ b x‖ ≤ 2) ∧
      ∀ x : X, Tendsto (fun n : ℕ => ∑ b ∈ s n, c n b * χ b x) atTop (𝓝 (β x : ℂ)) := by
  have key : ∀ n : ℕ, ∃ (s : Finset B) (c : B → ℂ), (∀ x, ‖∑ b ∈ s, c b * χ b x‖ ≤ 2) ∧
      ∀ x ∈ Metric.closedBall x₀ (n : ℝ),
        ‖∑ b ∈ s, c b * χ b x - (β x : ℂ)‖ ≤ 2 * (1 / ((n : ℝ) + 1)) := by
    intro n
    refine step χ hc hadd h0 hn hs β hβ hβ1 (isCompact_closedBall x₀ n)
      Nat.one_div_pos_of_nat ?_
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  choose s c h1 h2 using key
  refine ⟨s, c, h1, fun x => ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (dist x x₀)]
    with n hn'
  exact h2 n x hn'

end GlobalTheory.RealAlgebraCharacters
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchTrigBump

theorem exists_bounded_trig {X : Type} [PseudoMetricSpace X] [ProperSpace X] (x₀ : X) {B : Type} [AddCommGroup B]
    (χ : B → X → ℂ) (hc : ∀ b, Continuous (χ b)) (hadd : ∀ a b x, χ (a + b) x = χ a x * χ b x)
    (hzero : ∀ x, χ 0 x = 1) (hnorm : ∀ a x, ‖χ a x‖ = 1) (hsep : ∀ x y, x ≠ y → ∃ b, χ b x ≠ χ b y)
    (β : X → ℝ) (hβ : Continuous β) (h01 : ∀ u, 0 ≤ β u ∧ β u ≤ 1) :
    ∃ (s : ℕ → Finset B) (c : ℕ → B → ℂ), (∀ n x, ‖∑ b ∈ s n, c n b * χ b x‖ ≤ 2) ∧
      ∀ x, Filter.Tendsto (fun n => ∑ b ∈ s n, c n b * χ b x) Filter.atTop (nhds (β x : ℂ)) := by
  first
  | exact @_root_.GlobalTheory.RealAlgebraCharacters.main
  | exact _root_.GlobalTheory.RealAlgebraCharacters.main
  | (apply _root_.GlobalTheory.RealAlgebraCharacters.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RealAlgebraCharacters.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RealAlgebraCharacters.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RealAlgebraCharacters.main ..)

variable {F : Type} [Field F] [NumberField F]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm


open scoped Classical in
theorem exists_trace_mul_ne_zero (u : mixedEmbedding.mixedSpace F) (hu : u ≠ 0) :
    ∃ w, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (u * w) ≠ 0 := by
  let w : mixedEmbedding.mixedSpace F := (fun v => (u.1 v)⁻¹, fun v => (u.2 v)⁻¹)
  have h1 : u * w * u = u := by
    refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
    · change u.1 v * (u.1 v)⁻¹ * u.1 v = u.1 v
      exact mul_inv_mul_cancel _
    · change u.2 v * (u.2 v)⁻¹ * u.2 v = u.2 v
      exact mul_inv_mul_cancel _
  have h2 : IsIdempotentElem (u * w) := by
    change u * w * (u * w) = u * w
    rw [← mul_assoc, h1]
  refine ⟨w, fun h => hu ?_⟩
  rw [Algebra.trace_apply] at h
  have h3 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff
    (h2.map (Algebra.lmul ℝ (mixedEmbedding.mixedSpace F)))).1 h
  have h4 := LinearMap.congr_fun h3 u
  simp only [LinearMap.zero_apply] at h4
  rw [← h1]
  exact h4


open scoped Classical in
theorem exists_char_ne {κ : Type} [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) (hxy : x ≠ y) :
    ∃ w : κ → mixedEmbedding.mixedSpace F,
      Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ w) : ℝ)) ≠
      Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ w) : ℝ)) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
  obtain ⟨w, hw⟩ := exists_trace_mul_ne_zero (x i - y i) (sub_ne_zero.2 hi)
  set t := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ((x i - y i) * w) with ht
  refine ⟨Pi.single i ((2 * t)⁻¹ • w), fun h => ?_⟩
  rw [dotProduct_single, dotProduct_single] at h
  have h1 : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y i * ((2 * t)⁻¹ • w)) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x i * ((2 * t)⁻¹ • w)) - 1 / 2 := by
    have : (2 * t)⁻¹ * t = 1 / 2 := by field_simp
    rw [← this, mul_smul_comm, mul_smul_comm, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub]
    congr 1
    rw [ht, sub_mul, map_sub]
    ring
  rw [h1] at h
  generalize Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x i * ((2 * t)⁻¹ • w)) = a at h
  have h2 : -(2 * Real.pi * Complex.I) * ((a - 1 / 2 : ℝ) : ℂ) =
      -(2 * Real.pi * Complex.I) * (a : ℂ) + Real.pi * Complex.I := by
    push_cast; ring
  rw [h2, Complex.exp_add, Complex.exp_pi_mul_I] at h
  have h3 := Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (a : ℂ))
  apply h3
  linear_combination h / 2

theorem arch_bump_trig : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (U : Set (κ → Ainf F)) (y : κ → AF F), IsOpen U → (fun i => (y i).1) ∈ U →
    ∃ β : (κ → Ainf F) → ℝ, Continuous β ∧ (∀ u, 0 ≤ β u ∧ β u ≤ 1) ∧ β (fun i => (y i).1) = 1 ∧
      (∀ u, β u ≠ 0 → u ∈ U) ∧
      ∃ (s : ℕ → Finset (κ → AF F)) (c : ℕ → (κ → AF F) → ℂ) (C : ℝ),
        (∀ n, ∀ b ∈ s n, ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
        (∀ n (x : κ → AF F), ‖∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)‖ ≤ C) ∧
        ∀ x : κ → AF F, Filter.Tendsto (fun n => ∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)) Filter.atTop
          (nhds ((β (fun i => (x i).1) : ℝ) : ℂ)) := by
  intro F _ _ κ _ ψ hψ U y hU hy
  classical
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let P : (κ → Ainf F) → κ → mixedEmbedding.mixedSpace F := fun u i => e (u i)
  let Q : (κ → mixedEmbedding.mixedSpace F) → κ → Ainf F := fun u i => e.symm (u i)
  have hP : Continuous P := continuous_pi fun i => continuous_toMixed.comp (continuous_apply i)
  have hQ : Continuous Q := continuous_pi fun i => continuous_ofMixed.comp (continuous_apply i)
  have hQP : ∀ u, Q (P u) = u := fun u => funext fun i => e.symm_apply_apply _
  have hU' : IsClosed (Q ⁻¹' U)ᶜ := (hU.preimage hQ).isClosed_compl
  obtain ⟨f, hf0, hf1, hf⟩ := exists_continuous_zero_one_of_isClosed hU'
    (isClosed_singleton (x := P fun i => (y i).1))
    (Set.disjoint_singleton_right.2 fun h => h (by rw [Set.mem_preimage, hQP]; exact hy))
  let χ : (κ → mixedEmbedding.mixedSpace F) → (κ → mixedEmbedding.mixedSpace F) → ℂ := fun w u =>
    Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (u ⬝ᵥ w) : ℝ))
  have hT : Continuous (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) :=
    LinearMap.continuous_of_finiteDimensional _
  obtain ⟨s, c, hb, hl⟩ := exists_bounded_trig 0 χ
    (fun w => Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (hT.comp (continuous_id.dotProduct continuous_const)))))
    (fun a b x => by simp only [χ, dotProduct_add, map_add (f := _), Complex.ofReal_add, mul_add, Complex.exp_add])
    (fun x => by simp [χ])
    (fun a x => by simp [χ, Complex.norm_exp])
    exists_char_ne f f.continuous (fun u => hf u)
  let ι : (κ → mixedEmbedding.mixedSpace F) → κ → AF F := fun w i => ((e.symm (w i), 0) : Ainf F × Af F)
  let ρ : (κ → AF F) → κ → mixedEmbedding.mixedSpace F := fun b i => e (b i).1
  have hρ : ∀ w, ρ (ι w) = w := fun w => funext fun i => e.apply_symm_apply _
  have hι : Function.Injective ι := Function.LeftInverse.injective hρ
  have hchar : ∀ (x : κ → AF F) w, ψ (x ⬝ᵥ ι w) = χ w (P fun i => (x i).1) := by
    intro x w
    have h2 : (x ⬝ᵥ ι w).2 = 0 := by
      have := map_sum (RingHom.snd (Ainf F) (Af F)) (fun i => x i * ι w i) Finset.univ
      refine this.trans (Finset.sum_eq_zero fun i _ => ?_)
      exact mul_zero (x i).2
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x ⬝ᵥ ι w) = (P fun i => (x i).1) ⬝ᵥ w := by
      have := map_sum (e.toRingHom.comp (RingHom.fst (Ainf F) (Af F))) (fun i => x i * ι w i) Finset.univ
      refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
      change e ((x i).1 * e.symm (w i)) = _
      rw [map_mul, e.apply_symm_apply]
    rw [hψ.2.2, h1]
    intro u hu
    have hu1 : u.1 = 0 := e.injective (hu.trans (map_zero e).symm)
    refine Prod.ext ?_ ?_
    · change u.1 * (x ⬝ᵥ ι w).1 = 0
      rw [hu1, zero_mul]
    · change u.2 * (x ⬝ᵥ ι w).2 = 0
      rw [h2, mul_zero]
  have hsum : ∀ n (x : κ → AF F), ∑ b ∈ (s n).map ⟨ι, hι⟩, c n (ρ b) * ψ (x ⬝ᵥ b) =
      ∑ w ∈ s n, c n w * χ w (P fun i => (x i).1) := by
    intro n x
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Function.Embedding.coeFn_mk, hρ, hchar]
  refine ⟨fun u => f (P u), f.continuous.comp hP, fun u => hf _, hf1 rfl, fun u hu => ?_,
    fun n => (s n).map ⟨ι, hι⟩, fun n b => c n (ρ b), 2, ?_, fun n x => ?_, fun x => ?_⟩
  · by_contra h
    exact hu (hf0 (fun h' => h (by rwa [Set.mem_preimage, hQP] at h')))
  · intro n b hb v
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hb
    funext i
    refine Prod.ext ?_ ?_
    · exact zero_mul (e.symm (w i))
    · exact mul_zero (GlobalTheory.LatVac.liftV v 1).2
  · rw [hsum]; exact hb _ _
  · simp only [hsum]; exact hl _

end GlobalTheory.ArchTrigBump
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_smooth_bump_with_trigonometric_expansion : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (U : Set (κ → Ainf F)) (y : κ → AF F), IsOpen U → (fun i => (y i).1) ∈ U →
    ∃ β : (κ → Ainf F) → ℝ, Continuous β ∧ (∀ u, 0 ≤ β u ∧ β u ≤ 1) ∧ β (fun i => (y i).1) = 1 ∧
      (∀ u, β u ≠ 0 → u ∈ U) ∧
      ∃ (s : ℕ → Finset (κ → AF F)) (c : ℕ → (κ → AF F) → ℂ) (C : ℝ),
        (∀ n, ∀ b ∈ s n, ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
        (∀ n (x : κ → AF F), ‖∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)‖ ≤ C) ∧
        ∀ x : κ → AF F, Filter.Tendsto (fun n => ∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)) Filter.atTop
          (nhds ((β (fun i => (x i).1) : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.ArchTrigBump.arch_bump_trig | exact GlobalTheory.ArchTrigBump.arch_bump_trig | (intros; apply GlobalTheory.ArchTrigBump.arch_bump_trig <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalizingWeightEqualOffPlaceMasses
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.OffVLocalWeights

theorem sq_lintegral_lt_top : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ < ⊤ := by
  intro F _ _ κ _ Φ hΦ μ hμ
  letI : MeasurableSpace (κ → AF F) := borel _
  have h := (GlobalTheory.WeilM.schA_memLp_two F κ μ hμ Φ hΦ).integrable_norm_pow two_ne_zero
  have h2 := h.2
  simp only [HasFiniteIntegral, enorm_pow, enorm_norm] at h2
  exact h2

theorem continuous_and_compact_finite_support : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    Continuous Φ ∧ ∃ K : Set (κ → Af F), IsCompact K ∧ ∀ x : κ → AF F, Φ x ≠ 0 → (fun i => (x i).2) ∈ K := by
  intro F _ _ κ _ Φ hΦ
  let j : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  have hd := GlobalTheory.SchwartzDecay.decay_of_mem_schA F _ _ (GlobalTheory.RestrSchA.mem_schA_comp_extend F j j.injective Φ hΦ)
  have e : ∀ x : κ → AF F, Φ x = Φ (Function.extend j (x ∘ j) 0) := fun x => by
    congr 1
    funext i
    obtain ⟨k, rfl⟩ := j.surjective i
    rw [j.injective.extend_apply]
    rfl
  have hr : Continuous (fun x : κ → AF F => x ∘ j) := continuous_pi fun i => continuous_apply _
  obtain ⟨hc, ⟨K, hK, hK0⟩, -⟩ := hd
  refine ⟨?_, (fun u : Fin (Fintype.card κ) → Af F => u ∘ j.symm) '' K,
    hK.image (continuous_pi fun i => continuous_apply _), fun x hx => ?_⟩
  · have : Φ = (fun y => Φ (Function.extend j y 0)) ∘ (fun x : κ → AF F => x ∘ j) := funext e
    rw [this]
    exact hc.comp hr
  · refine ⟨GlobalTheory.SWQ.fin (x ∘ j), ?_, ?_⟩
    · by_contra h
      exact hx ((e x).trans (hK0 _ h))
    · funext i
      simp only [GlobalTheory.SWQ.fin, Function.comp_apply, Equiv.apply_symm_apply]
      rfl

theorem exists_box_nhds : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (O : Set (κ → AF F)) (y : κ → AF F),
    IsOpen O → y ∈ O → ∃ (U : Set (κ → Ainf F)) (V : Set (κ → Af F)), IsOpen U ∧ IsOpen V ∧
      (fun i => (y i).1) ∈ U ∧ (fun i => (y i).2) ∈ V ∧
      ∀ x : κ → AF F, (fun i => (x i).1) ∈ U → (fun i => (x i).2) ∈ V → x ∈ O := by
  intro F _ _ κ _ O y hO hy
  have hp : Continuous (fun q : (κ → Ainf F) × (κ → Af F) => (fun i => ((q.1 i, q.2 i) : AF F))) :=
    continuous_pi fun i => ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)
  obtain ⟨U, V, hU, hV, hyU, hyV, hUV⟩ :=
    isOpen_prod_iff.1 (hO.preimage hp) (fun i => (y i).1) (fun i => (y i).2) (by exact hy)
  exact ⟨U, V, hU, hV, hyU, hyV, fun x hx1 hx2 => hUV (Set.mk_mem_prod hx1 hx2)⟩

theorem exists_finite_indicator_poly : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ K : Set (κ → Af F), IsCompact K → ∀ (y : κ → AF F) (V : Set (κ → Af F)), IsOpen V → (fun i => (y i).2) ∈ V →
    ∃ (A : Set (κ → Af F)) (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ),
      IsOpen A ∧ (fun i => (y i).2) ∈ A ∧ (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
      (∀ x z : κ → AF F, GlobalTheory.LatVac.liftV v 1 • z = z →
        ((fun i => ((x + z) i).2) ∈ A ↔ (fun i => (x i).2) ∈ A)) ∧
      (∀ x : κ → AF F, (fun i => (x i).2) ∈ A →
        (fun i => ((x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x)) i).2) ∈ V) ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ K →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = A.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2) := by
  first | exact @GlobalTheory.T.exists_trigPolynomial_indicator_awayFromPlace | exact GlobalTheory.T.exists_trigPolynomial_indicator_awayFromPlace

theorem exists_arch_bump_poly : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (U : Set (κ → Ainf F)) (y : κ → AF F), IsOpen U → (fun i => (y i).1) ∈ U →
    ∃ β : (κ → Ainf F) → ℝ, Continuous β ∧ (∀ u, 0 ≤ β u ∧ β u ≤ 1) ∧ β (fun i => (y i).1) = 1 ∧
      (∀ u, β u ≠ 0 → u ∈ U) ∧
      ∃ (s : ℕ → Finset (κ → AF F)) (c : ℕ → (κ → AF F) → ℂ) (C : ℝ),
        (∀ n, ∀ b ∈ s n, ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
        (∀ n (x : κ → AF F), ‖∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)‖ ≤ C) ∧
        ∀ x : κ → AF F, Filter.Tendsto (fun n => ∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)) Filter.atTop
          (nhds ((β (fun i => (x i).1) : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.T.archimedean_smooth_bump_with_trigonometric_expansion | exact GlobalTheory.T.archimedean_smooth_bump_with_trigonometric_expansion

theorem exists_trig_prod : ∀ {X B : Type} [AddCommMonoid B] [DecidableEq B] (χ : B → X → ℂ),
    (∀ b b' x, χ (b + b') x = χ b x * χ b' x) → ∀ (s₁ s₂ : Finset B) (c₁ c₂ : B → ℂ),
    ∃ (s : Finset B) (c : B → ℂ), (∀ b ∈ s, ∃ b₁ ∈ s₁, ∃ b₂ ∈ s₂, b = b₁ + b₂) ∧
      ∀ x, ∑ b ∈ s, c b * χ b x = (∑ b ∈ s₁, c₁ b * χ b x) * (∑ b ∈ s₂, c₂ b * χ b x) := by
  intro X B _ _ χ hχ s₁ s₂ c₁ c₂
  refine ⟨Finset.image (fun p : B × B => p.1 + p.2) (s₁ ×ˢ s₂),
    fun b => ∑ p ∈ (s₁ ×ˢ s₂).filter (fun p => p.1 + p.2 = b), c₁ p.1 * c₂ p.2, ?_, ?_⟩
  · intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
    exact ⟨p.1, h1, p.2, h2, rfl⟩
  · intro x
    have hb : ∀ b, (∑ p ∈ (s₁ ×ˢ s₂).filter (fun p => p.1 + p.2 = b), c₁ p.1 * c₂ p.2) * χ b x =
        ∑ p ∈ (s₁ ×ˢ s₂).filter (fun p => p.1 + p.2 = b), c₁ p.1 * c₂ p.2 * χ (p.1 + p.2) x := by
      intro b
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.1 hp).2]
    simp_rw [hb]
    rw [Finset.sum_fiberwise_of_maps_to (g := fun p : B × B => p.1 + p.2)
      (fun p hp => Finset.mem_image_of_mem _ hp), Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hχ]
    ring

theorem lintegral_weight_eq_of_approx : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (f g h : X → ENNReal) (m : ℕ → X → ℂ) (C : ℝ),
    Measurable f → Measurable g → (∀ n, Measurable (m n)) → ∫⁻ x, f x ∂μ < ⊤ → ∫⁻ x, g x ∂μ < ⊤ →
    (∀ n, ∫⁻ x, ‖m n x‖ₑ ^ 2 * f x ∂μ = ∫⁻ x, ‖m n x‖ₑ ^ 2 * g x ∂μ) →
    (∀ n x, (f x ≠ 0 ∨ g x ≠ 0) → ‖m n x‖ ≤ C) →
    (∀ x, (f x ≠ 0 ∨ g x ≠ 0) → Filter.Tendsto (fun n => ‖m n x‖ₑ ^ 2) Filter.atTop (nhds (h x))) →
    ∫⁻ x, h x * f x ∂μ = ∫⁻ x, h x * g x ∂μ := by
  intro X _ μ f g h m C hf hg hm hfi hgi heq hb hlim
  have key : ∀ u : X → ENNReal, Measurable u → ∫⁻ x, u x ∂μ < ⊤ → (∀ x, u x ≠ 0 → (f x ≠ 0 ∨ g x ≠ 0)) →
      Filter.Tendsto (fun n => ∫⁻ x, ‖m n x‖ₑ ^ 2 * u x ∂μ) Filter.atTop (nhds (∫⁻ x, h x * u x ∂μ)) := by
    intro u hu hui hsupp
    refine tendsto_lintegral_of_dominated_convergence (fun x => ENNReal.ofReal C ^ 2 * u x)
      (fun n => ((hm n).enorm.pow_const 2).mul hu) (fun n => Filter.Eventually.of_forall fun x => ?_) ?_ ?_
    · by_cases hx : u x = 0
      · simp [hx]
      · have h1 : ‖m n x‖ₑ ≤ ENNReal.ofReal C := by
          rw [← ofReal_norm_eq_enorm]
          exact ENNReal.ofReal_le_ofReal (hb n x (hsupp x hx))
        show ‖m n x‖ₑ ^ 2 * u x ≤ ENNReal.ofReal C ^ 2 * u x
        gcongr
    · rw [lintegral_const_mul _ hu]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hui.ne
    · filter_upwards [ae_lt_top hu hui.ne] with x hx
      by_cases h0 : u x = 0
      · simp [h0]
      · exact ENNReal.Tendsto.mul_const (hlim x (hsupp x h0)) (Or.inr hx.ne)
  exact tendsto_nhds_unique ((key f hf hfi fun x hx => Or.inl hx).congr fun n => heq n)
    (key g hg hgi fun x hx => Or.inr hx)

theorem liftV_mul_fst {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : AF F) :
    (GlobalTheory.LatVac.liftV v 1 * a).1 = 0 := by
  change (0 : Ainf F) * a.1 = 0
  exact zero_mul _

theorem exists_localizing_weight : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ,
    (∀ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) →
      ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x‖ₑ ^ 2 ∂μ) →
    ∀ (y : κ → AF F) (O : Set (κ → AF F)), IsOpen O → y ∈ O →
    ∃ h : (κ → AF F) → ENNReal, @Measurable _ _ (borel _) _ h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, GlobalTheory.LatVac.liftV v 1 • z = z → h (x + z) = h x) ∧
      (∀ x, h x ≠ 0 → x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x) ∈ O) ∧
      (∃ O' : Set (κ → AF F), IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ v ψ hψ hnt μ hμ Φ hΦ Ψ hΨ hyp y O hO hyO
  classical
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨hΦc, KΦ, hKΦ, hΦK⟩ := continuous_and_compact_finite_support Φ hΦ
  obtain ⟨hΨc, KΨ, hKΨ, hΨK⟩ := continuous_and_compact_finite_support Ψ hΨ
  obtain ⟨U, V, hU, hV, hyU, hyV, hbox⟩ := exists_box_nhds O y hO hyO
  obtain ⟨A, sf, cf, hA, hyA, hsf, hAinv, hAV, hfK⟩ :=
    exists_finite_indicator_poly v ψ hψ hnt (KΦ ∪ KΨ) (hKΦ.union hKΨ) y V hV hyV
  obtain ⟨β, hβc, hβ01, hβy, hβU, sa, ca, C, hsa, hCb, hlim⟩ := exists_arch_bump_poly ψ hψ U y hU hyU
  have hmul : ∀ (b b' : κ → AF F) (x : κ → AF F), ψ (x ⬝ᵥ (b + b')) = ψ (x ⬝ᵥ b) * ψ (x ⬝ᵥ b') :=
    fun b b' x => by rw [dotProduct_add, AddChar.map_add_eq_mul]
  choose s c hs hsc using fun n => exists_trig_prod (fun b x => ψ (x ⬝ᵥ b)) hmul sf (sa n) cf (ca n)
  have hfinc : Continuous (fun x : κ → AF F => fun i => (x i).2) :=
    continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  have hinfc : Continuous (fun x : κ → AF F => fun i => (x i).1) :=
    continuous_pi fun i => continuous_fst.comp (continuous_apply i)
  have hgc : Continuous (fun x : κ → AF F => ‖((β (fun i => (x i).1) : ℝ) : ℂ)‖ₑ ^ 2) :=
    (ENNReal.continuous_pow 2).comp (continuous_enorm.comp (Complex.continuous_ofReal.comp (hβc.comp hinfc)))
  have hz1 : ∀ z : κ → AF F, GlobalTheory.LatVac.liftV v 1 • z = z → ∀ i, (z i).1 = 0 := by
    intro z hz i
    have := congrArg Prod.fst (congrFun hz i)
    rw [← this]
    exact liftV_mul_fst v (z i)
  have hβle : ∀ u, ‖((β u : ℝ) : ℂ)‖ₑ ^ 2 ≤ 1 := by
    intro u
    refine pow_le_one₀ zero_le' ?_
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hβ01 u).1]
    exact ENNReal.ofReal_le_one.2 (hβ01 u).2
  refine ⟨fun x => if (fun i => (x i).2) ∈ A then ‖((β (fun i => (x i).1) : ℝ) : ℂ)‖ₑ ^ 2 else 0,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Measurable.ite (p := fun x : κ → AF F => (fun i => (x i).2) ∈ A)
      (hA.preimage hfinc).measurableSet hgc.measurable measurable_const
  · intro x
    dsimp only
    split_ifs
    · exact hβle _
    · exact zero_le'
  · intro x z hz
    dsimp only
    have h1 : (fun i => ((x + z) i).1) = fun i => (x i).1 := by
      funext i
      change (x i).1 + (z i).1 = (x i).1
      rw [hz1 z hz i, add_zero]
    simp only [hAinv x z hz, h1]
  · intro x hx
    dsimp only at hx
    by_cases hxA : (fun i => (x i).2) ∈ A
    · rw [if_pos hxA] at hx
      have hβ0 : β (fun i => (x i).1) ≠ 0 := by
        intro h0
        rw [h0] at hx
        simp at hx
      apply hbox
      · have h1 : (fun i => ((x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x)) i).1) =
            fun i => (x i).1 := by
          funext i
          change (x i).1 + ((GlobalTheory.LatVac.liftV v 1 * y i).1 - (GlobalTheory.LatVac.liftV v 1 * x i).1) = (x i).1
          rw [liftV_mul_fst, liftV_mul_fst, sub_zero, add_zero]
        rw [h1]
        exact hβU _ hβ0
      · exact hAV x hxA
    · rw [if_neg hxA] at hx
      exact absurd rfl hx
  · refine ⟨{x | (fun i => (x i).2) ∈ A} ∩ {x | 1 / 2 < ‖((β (fun i => (x i).1) : ℝ) : ℂ)‖ₑ ^ 2},
      (hA.preimage hfinc).inter (isOpen_lt continuous_const hgc), ⟨hyA, ?_⟩, ?_⟩
    · show 1 / 2 < ‖((β (fun i => (y i).1) : ℝ) : ℂ)‖ₑ ^ 2
      rw [hβy]
      simpa using ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top
    · rintro x ⟨hxA, hx⟩ -
      show 1 / 2 ≤ (if (fun i => (x i).2) ∈ A then ‖((β (fun i => (x i).1) : ℝ) : ℂ)‖ₑ ^ 2 else 0)
      rw [if_pos (show (fun i => (x i).2) ∈ A from hxA)]
      exact le_of_lt hx
  · have hK : ∀ x : κ → AF F, (‖Ψ x‖ₑ ^ 2 ≠ 0 ∨ ‖Φ x‖ₑ ^ 2 ≠ 0) → (fun i => (x i).2) ∈ KΦ ∪ KΨ := by
      intro x hx
      rcases hx with hx | hx
      · refine Or.inr (hΨK x fun h0 => hx ?_)
        rw [h0]; simp
      · refine Or.inl (hΦK x fun h0 => hx ?_)
        rw [h0]; simp
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hCb 0 0)
    refine lintegral_weight_eq_of_approx μ (fun x => ‖Ψ x‖ₑ ^ 2) (fun x => ‖Φ x‖ₑ ^ 2) _ (fun n x => ∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)) C
      (hΨc.measurable.enorm.pow_const 2) (hΦc.measurable.enorm.pow_const 2) ?_ (sq_lintegral_lt_top Ψ hΨ μ hμ) (sq_lintegral_lt_top Φ hΦ μ hμ)
      ?_ ?_ ?_
    · intro n
      refine Continuous.measurable (continuous_finsetSum _ fun b _ => continuous_const.mul (hψ.1.comp ?_))
      exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const
    · intro n
      have hoff : ∀ b ∈ s n, GlobalTheory.LatVac.liftV v 1 • b = 0 := by
        intro b hb
        obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hs n b hb
        rw [smul_add, hsf b₁ hb₁, hsa n b₂ hb₂ v, add_zero]
      have := hyp (s n) (c n) hoff
      simpa only [enorm_mul, mul_pow] using this
    · intro n x hx
      rw [hsc n x, hfK x (hK x hx)]
      by_cases hxA : (fun i => (x i).2) ∈ A
      · rw [Set.indicator_of_mem hxA, one_mul]
        exact hCb n x
      · rw [Set.indicator_of_notMem hxA, zero_mul, norm_zero]
        exact hC0
    · intro x hx
      simp only [hsc _ x, hfK x (hK x hx)]
      by_cases hxA : (fun i => (x i).2) ∈ A
      · simp only [Set.indicator_of_mem hxA, one_mul, if_pos hxA]
        exact ((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp (hlim x))
      · simp only [Set.indicator_of_notMem hxA, zero_mul, if_neg hxA, enorm_zero]
        simpa using tendsto_const_nhds

end GlobalTheory.OffVLocalWeights
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalizingWeightEqualOffPlaceMassesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localizingWeight_equal_offPlaceMasses : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ,
    (∀ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) →
      ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x‖ₑ ^ 2 ∂μ) →
    ∀ (y : κ → AF F) (O : Set (κ → AF F)), IsOpen O → y ∈ O →
    ∃ h : (κ → AF F) → ENNReal, @Measurable _ _ (borel _) _ h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, GlobalTheory.LatVac.liftV v 1 • z = z → h (x + z) = h x) ∧
      (∀ x, h x ≠ 0 → x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x) ∈ O) ∧
      (∃ O' : Set (κ → AF F), IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.OffVLocalWeights.exists_localizing_weight | exact GlobalTheory.OffVLocalWeights.exists_localizing_weight | (intros; apply GlobalTheory.OffVLocalWeights.exists_localizing_weight <;> assumption)
end
