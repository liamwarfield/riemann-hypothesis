module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticLatticeForms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealEmbeddingCharacters

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SpanColsMul
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

def Am (u : Fin 2 → Fin r → E) (τ : X.Ψ) : Matrix (Fin r) (Fin 2) ℂ :=
  Matrix.of fun a i => emb τ.1 (u i) a

noncomputable def Cm (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    Matrix (Fin 2) (Fin r) ℂ :=
  Matrix.of fun i j => -(I * X.c τ) * ∑ k, b τ i k * ∑ l, τ.1 (X.Gm j l) * conj (emb τ.1 (u k) l)

theorem zmat_eq (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    X.zmat u b τ = 1 + X.Am u τ * X.Cm u b τ := by
  ext a j
  simp only [Data.zmat, Data.Am, Data.Cm, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
    Matrix.of_apply, Fin.sum_univ_two]
  ring

theorem Cm_add (u : Fin 2 → Fin r → E) (b b' : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    X.Cm u (b + b') τ = X.Cm u b τ + X.Cm u b' τ := by
  ext i j
  simp only [Data.Cm, Matrix.add_apply, Matrix.of_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

private lemma Cm_mulVec_apply (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ)
    (v : Fin r → ℂ) (i : Fin 2) :
    (X.Cm u b τ *ᵥ v) i = -(I * X.c τ) * ∑ k, b τ i k * hermC τ.1 X.Gm v (emb τ.1 (u k)) := by
  simp only [Matrix.mulVec, dotProduct, Data.Cm, Matrix.of_apply, hermC, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem Cm_mul_Am (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) : X.Cm u b τ * X.Am u τ = 0 := by
  ext i i'
  have e : (X.Cm u b τ * X.Am u τ) i i' = (X.Cm u b τ *ᵥ emb τ.1 (u i')) i := rfl
  rw [e, Cm_mulVec_apply X u b τ, Matrix.zero_apply]
  simp only [hermC_emb, hu, map_zero, mul_zero, Finset.sum_const_zero]

theorem zmat_mul (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b b' : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    X.zmat u b τ * X.zmat u b' τ = X.zmat u (b + b') τ := by
  have h := X.Cm_mul_Am u hu b τ
  rw [X.zmat_eq u b τ, X.zmat_eq u b' τ, X.zmat_eq u (b + b') τ, X.Cm_add]
  calc (1 + X.Am u τ * X.Cm u b τ) * (1 + X.Am u τ * X.Cm u b' τ)
      = 1 + X.Am u τ * X.Cm u b τ + X.Am u τ * X.Cm u b' τ +
          X.Am u τ * (X.Cm u b τ * X.Am u τ) * X.Cm u b' τ := by
        simp only [add_mul, mul_add, one_mul, mul_one, Matrix.mul_assoc]
        abel
    _ = 1 + X.Am u τ * (X.Cm u b τ + X.Cm u b' τ) := by
        rw [h, Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.mul_add, add_assoc]

theorem zmat_det (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) : (X.zmat u b τ).det = 1 := by
  rw [X.zmat_eq, Matrix.det_one_add_mul_comm, X.Cm_mul_Am u hu, add_zero, Matrix.det_one]

theorem Am_mulVec (u : Fin 2 → Fin r → E) (τ : X.Ψ) (y : Fin 2 → ℂ) :
    X.Am u τ *ᵥ y = ∑ i, y i • emb τ.1 (u i) := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Data.Am, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem Cm_mulVec (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) (v : Fin r → ℂ) (i : Fin 2) :
    (X.Cm u b τ *ᵥ v) i = -(I * X.c τ) * ∑ k, b τ i k * hermC τ.1 X.Gm v (emb τ.1 (u k)) := by
  exact Cm_mulVec_apply X u b τ v i

theorem zmat_unitary (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (τ : X.Ψ) (v w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.zmat u b τ *ᵥ v) (X.zmat u b τ *ᵥ w) = hermC τ.1 X.Gm v w := by
  have hee : ∀ i k, hermC τ.1 X.Gm (emb τ.1 (u i)) (emb τ.1 (u k)) = 0 := fun i k => by
    rw [hermC_emb, hu, map_zero]
  have hb' : ∀ i k, conj (b τ i k) = b τ k i := fun i k => (hb τ i k).symm
  have hcw : ∀ k, conj (hermC τ.1 X.Gm w (emb τ.1 (u k))) = hermC τ.1 X.Gm (emb τ.1 (u k)) w :=
    fun k => hermC_conj τ.1 X.Gm_herm _ _
  rw [X.zmat_eq, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, X.Am_mulVec, X.Am_mulVec]
  simp only [Fin.sum_univ_two, hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right, hee,
    X.Cm_mulVec, map_mul, map_add, map_neg, hb', hcw, Complex.conj_I, Complex.conj_ofReal, mul_zero, add_zero]
  ring

theorem mat_Zb (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.Zb u b x) τ = X.zmat u b τ * mat x τ := rfl

theorem Zb_Zb (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b b' : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) :
    X.Zb u b (X.Zb u b' x) = X.Zb u (b + b') x := by
  funext τ
  show X.zmat u b τ * mat (X.Zb u b' x) τ = X.zmat u (b + b') τ * mat x τ
  rw [X.mat_Zb, ← Matrix.mul_assoc, X.zmat_mul u hu]

private lemma col_mul_eq_mulVec_col (M N : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (M * N) a = M *ᵥ col N a := by
  funext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem gram_Zb (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (X.Zb u b x) τ) = gram τ.1 X.Gm (mat x τ) := by
  rw [X.mat_Zb]
  ext a a'
  simp only [gram, Matrix.of_apply, col_mul_eq_mulVec_col]
  exact X.zmat_unitary u hu b hb τ _ _

theorem dmin_Zb (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (X.Zb u b x) τ i = dmin X.Gm x τ i := by
  unfold dmin
  rw [X.gram_Zb u hu b hb x τ]

theorem Zb_dom (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.Zb u b x ∈ X.dom := by
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx ⊢
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · rw [X.mat_Zb, Matrix.det_mul, X.zmat_det u hu, one_mul]
    exact (hx τ).1
  · rw [X.dmin_Zb u hu b hb]
    exact (hx τ).2 i

theorem nfac_Zb (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (la : Wt X.Ψ r) (x : Frame X.Ψ r) :
    X.nfac la (X.Zb u b x) = X.nfac la x := by
  simp only [Data.nfac, X.dmin_Zb u hu b hb]

theorem flowV_uvec (u : Fin 2 → Fin r → E) (a : X.Ψ → Fin 2 → ℂ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    X.flowV (X.uvec u a) s x = X.Zb u (fun τ i k => s τ * a τ i * conj (a τ k)) x := by
  funext τ
  show X.flowMatV (X.uvec u a τ) τ (s τ) * mat x τ =
    X.zmat u (fun τ i k => s τ * a τ i * conj (a τ k)) τ * mat x τ
  congr 1
  ext p q
  have hk : ∀ k, ∑ l, τ.1 (X.Gm q l) * (conj (a τ k) * conj (emb τ.1 (u k) l)) =
      conj (a τ k) * ∑ l, τ.1 (X.Gm q l) * conj (emb τ.1 (u k) l) := fun k => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [Data.flowMatV, Data.zmat, Matrix.of_apply, Data.uvec, Fin.sum_univ_two, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib, hk]
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HolomorphicPeriodicityExtension
namespace ReciprocityTheory.ChartRestriction.G.FD

open Complex Filter Topology

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem d4l4_c_pos {r : ℕ} (X : Data E r) (τ : X.Ψ) : 0 < X.c τ := by
  have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero τ.1).mpr X.ξ0_ne
  show 0 < 2 * ‖τ.1 X.ξ0‖
  exact mul_pos two_pos (norm_pos_iff.mpr h)

open Classical in
theorem d4l4_diff_flow {r : ℕ} (X : Data E r) (e : X.Ψ → Fin r → ℂ) (x : Frame X.Ψ r)
    (s : X.Ψ → ℂ) (τ0 : X.Ψ) :
    Differentiable ℂ (fun z : ℂ => X.flowV e (Function.update s τ0 z) x) := by
  rw [differentiable_pi]
  intro τ
  rw [differentiable_pi]
  intro a
  rw [differentiable_pi]
  intro b
  have hu : Differentiable ℂ (fun z : ℂ => Function.update s τ0 z τ) := by
    by_cases h : τ = τ0
    · subst h
      simpa using differentiable_id
    · simpa [Function.update_of_ne h] using differentiable_const (s τ)
  intro z
  simp only [Data.flowV, Matrix.mul_apply, Data.flowMatV, Matrix.of_apply, mat]
  refine DifferentiableAt.fun_sum fun k _ => ?_
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_sub
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_mul
  exact hu z

theorem holomorphic_periodicity_extension : HolomorphicPeriodicityExtension (E := E) := by
  classical
  intro r X e he G hG m x hx hreal s hs
  have hdom : ∀ s' : X.Ψ → ℂ, X.flowV e s' x ∈ X.dom ↔ ∀ τ, 0 < 1 + (s' τ).im / X.ttV e x τ :=
    fun s' => (flowDomainCriterion_holds (E := E) r X e he x hx s').1
  set H : (X.Ψ → ℂ) → ℂ := fun s' =>
    G (X.flowV e s' x) - cexp (4 * Real.pi * I * ∑ τ, m τ * s' τ) * G x with hH

  suffices key : ∀ A : Finset X.Ψ, ∀ s' : X.Ψ → ℂ, (∀ τ ∉ A, (s' τ).im = 0) →
      X.flowV e s' x ∈ X.dom → H s' = 0 by
    exact sub_eq_zero.mp (key Finset.univ s (fun τ h => absurd (Finset.mem_univ τ) h) hs)
  intro A
  induction A using Finset.induction_on with
  | empty =>
    intro s' hs' _
    have hre : ∀ τ, (((s' τ).re : ℝ) : ℂ) = s' τ := fun τ =>
      Complex.ext (by simp) (by simp [hs' τ (by simp)])
    have h0 := hreal (fun τ => (s' τ).re)
    simp only [hre] at h0
    simp only [hH, h0, sub_self]
  | insert τ0 A hτ0 ih =>
    intro s' hs' hdom'
    have hcond := (hdom s').mp hdom'
    set V : Set ℂ := {z | 0 < 1 + z.im / X.ttV e x τ0} with hVdef
    have hVo : IsOpen V := isOpen_lt continuous_const (by fun_prop)
    have hVc : Convex ℝ V := by
      intro z hz w hw a b ha hb hab
      simp only [hVdef, Set.mem_setOf_eq] at hz hw ⊢
      have him : (a • z + b • w).im = a * z.im + b * w.im := by simp
      have h1 : 1 + (a * z.im + b * w.im) / X.ttV e x τ0 =
          a * (1 + z.im / X.ttV e x τ0) + b * (1 + w.im / X.ttV e x τ0) := by
        linear_combination (-1 : ℝ) * hab
      rw [him, h1]
      rcases ha.lt_or_eq with ha' | ha'
      · exact add_pos_of_pos_of_nonneg (mul_pos ha' hz) (mul_nonneg hb hw.le)
      · have hb1 : b = 1 := by linarith
        rw [← ha', hb1]
        simpa using hw
    have hreal0 : ∀ y : ℝ, (y : ℂ) ∈ V := by intro y; simp [hVdef]
    have hmaps : ∀ z ∈ V, X.flowV e (Function.update s' τ0 z) x ∈ X.dom := by
      intro z hz
      rw [hdom]
      intro τ
      by_cases h : τ = τ0
      · subst h
        simpa [hVdef] using hz
      · simpa [Function.update_of_ne h] using hcond τ
    have hu : ∀ τ, Differentiable ℂ (fun z : ℂ => Function.update s' τ0 z τ) := by
      intro τ
      by_cases h : τ = τ0
      · subst h
        simpa using differentiable_id
      · simpa [Function.update_of_ne h] using differentiable_const (s' τ)
    have hdiff : DifferentiableOn ℂ (fun z => H (Function.update s' τ0 z)) V := by
      have h1 : DifferentiableOn ℂ (fun z => G (X.flowV e (Function.update s' τ0 z) x)) V :=
        hG.comp (d4l4_diff_flow X e x s' τ0).differentiableOn (fun z hz => hmaps z hz)
      have hsum : Differentiable ℂ (fun z : ℂ => ∑ τ, m τ * Function.update s' τ0 z τ) := by
        intro z
        exact DifferentiableAt.fun_sum fun τ _ => ((hu τ) z).const_mul (m τ)
      have h2 : Differentiable ℂ (fun z : ℂ =>
          cexp (4 * Real.pi * I * ∑ τ, m τ * Function.update s' τ0 z τ) * G x) :=
        ((hsum.const_mul (4 * Real.pi * I)).cexp).mul_const (G x)
      exact h1.sub h2.differentiableOn
    have han : AnalyticOnNhd ℂ (fun z => H (Function.update s' τ0 z)) V :=
      hdiff.analyticOnNhd hVo

    have hzero_real : ∀ y : ℝ, H (Function.update s' τ0 (y : ℂ)) = 0 := by
      intro y
      apply ih
      · intro τ hτ
        by_cases h : τ = τ0
        · subst h
          simp
        · rw [Function.update_of_ne h]
          exact hs' τ (by simp [h, hτ])
      · exact hmaps _ (hreal0 y)
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), H (Function.update s' τ0 z) = 0 := by
      have ht : Filter.Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
        have h3 := Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
          (s := {(0 : ℝ)}ᶜ) (t := {(0 : ℂ)}ᶜ) (x := 0) (fun y hy => by simpa using hy)
        rwa [Complex.ofReal_zero] at h3
      exact ht.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall hzero_real))
    have h0V : (0 : ℂ) ∈ V := by simp [hVdef]
    have hEq := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hVc.isPreconnected h0V hfreq
    have h4 := hEq (hcond τ0)
    simpa using h4

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegralBasisReduction
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace IntegralBasisReduction

open Matrix NumberField Complex Module QuadraticLatticeForms
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

private lemma sum4_lemma {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := by
  calc ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ a, ∑ i, ∑ b, ∑ j, f a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, ∑ j, f a b i j := Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ j, ∑ b, f a b i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm

private lemma hermC_mulVec_lemma_2 {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (Y : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    hermC τ G (Y *ᵥ u) (Y *ᵥ v) = ∑ i, ∑ j, u i * gram τ G Y i j * conj (v j) := by
  calc hermC τ G (Y *ᵥ u) (Y *ᵥ v)
      = ∑ a, ∑ b, ∑ i, ∑ j, Y a i * u i * τ (G a b) * (conj (Y b j) * conj (v j)) := by
        simp only [hermC, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
    _ = ∑ i, ∑ j, ∑ a, ∑ b, Y a i * u i * τ (G a b) * (conj (Y b j) * conj (v j)) := sum4_lemma _
    _ = ∑ i, ∑ j, u i * gram τ G Y i j * conj (v j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [gram, hermC, col, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring

theorem hermC_normal {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} (hY : Y.det ≠ 0) (s : Fin r → ℂ)
    (hg : gram τ X.Gm Y = diagonal s) (p q : Fin r → ℂ) :
    hermC τ X.Gm p q = ∑ a, s a * (Y⁻¹ *ᵥ p) a * conj ((Y⁻¹ *ᵥ q) a) := by
  have hu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hY
  have key := hermC_mulVec_lemma_2 τ X.Gm Y (Y⁻¹ *ᵥ p) (Y⁻¹ *ᵥ q)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec, Matrix.one_mulVec, hg] at key
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]; ring
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

def IsNormal (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ : X.Ψ, (y τ).det ≠ 0 ∧ gram τ.1 X.Gm (y τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

theorem ip_Sg {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (p q : Fin r → E) :
    ip X (Ly X y (X.embV p)) (Sg X (Ly X y (X.embV q))) = ∑ τ, X.c τ * (τ.1 (herm X.Gm p q)).re := by
  simp only [ip, Sg, Ly, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun τ _ => ?_
  obtain ⟨hdet, hg⟩ := hy τ
  have hτ : τ.1 (herm X.Gm p q) = hermC τ.1 X.Gm (X.embV p τ) (X.embV q τ) := by
    first
      | simp [herm, hermC, Data.embV, Data.emb, cc, map_sum, map_mul,
          IsCMField.complexEmbedding_complexConj]
      | simp [herm, hermC, Data.embV, Data.emb, cc, map_sum, map_mul,
          NumberField.IsCMField.complexEmbedding_complexConj]
  rw [hτ, hermC_normal X hdet _ hg]
  congr 2
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [map_mul, Complex.conj_ofReal]
  ring

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def zbas {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ) :
    Basis ι ℝ (X.Ψ → Fin r → ℂ) :=
  (Basis.mk (RealPlaceEmbeddings.linIndR X g) (RealPlaceEmbeddings.span_embV X g).ge).map
    (LinearEquiv.ofBijective (Ly X y) ⟨Ly_injective X y fun τ => (hy τ).1,
      Ly_surjective X y fun τ => (hy τ).1⟩)

theorem zbas_apply {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ)
    (i : ι) : zbas X hy g i = Ly X y (X.embV (g i : Fin r → E)) := by
  simp only [zbas, Basis.map_apply, Basis.mk_apply]
  exact LinearEquiv.ofBijective_apply _ _

private lemma ip_sum_lemma_3 (u : X.Ψ → Fin r → ℂ) (a : ι → ℝ) (w : ι → X.Ψ → Fin r → ℂ) :
    ip X u (∑ k, a k • w k) = ∑ k, a k * ip X u (w k) := by
  have h1 : ∀ τ b, u τ b * conj ((∑ k, a k • w k) τ b) =
      ∑ k, ((a k : ℂ) * (u τ b * conj (w k τ b))) := by
    intro τ b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_apply, Finset.sum_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    ring
  simp only [ip, h1, Complex.re_sum, Complex.re_ofReal_mul, Finset.mul_sum]
  calc ∑ τ, ∑ b, ∑ k, X.c τ * (a k * (u τ b * conj (w k τ b)).re)
      = ∑ τ, ∑ k, ∑ b, X.c τ * (a k * (u τ b * conj (w k τ b)).re) :=
        Finset.sum_congr rfl fun τ _ => Finset.sum_comm
    _ = ∑ k, ∑ τ, ∑ b, X.c τ * (a k * (u τ b * conj (w k τ b)).re) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun τ _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring

theorem Bm_eq {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ) :
    Bm X g = Am X y g * LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X) := by
  ext i j
  rw [Matrix.mul_apply]
  have hS := (zbas X hy g).sum_repr (Sg X (zbas X hy g j))
  simp only [LinearMap.toMatrix_apply]
  rw [show Bm X g i j = ip X (zbas X hy g i) (Sg X (zbas X hy g j)) by
    simp only [Bm, Matrix.of_apply, zbas_apply]
    exact (ip_Sg X hy _ _).symm]
  conv_lhs => rw [← hS]
  rw [ip_sum_lemma_3]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Am, Matrix.of_apply, zbas_apply]
  ring

theorem det_Am_le {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ) :
    (Am X y g).det ≤ |(Bm X g).det| := by
  have hSS : Sg X * Sg X = 1 := by
    refine LinearMap.ext fun u => funext fun τ => funext fun a => ?_
    show ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * (((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * u τ a) = u τ a
    rw [← mul_assoc, ← Complex.ofReal_mul]
    unfold sgn
    split_ifs <;> simp
  have hM : LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X) *
      LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X) = 1 := by
    rw [← LinearMap.toMatrix_mul, hSS, LinearMap.toMatrix_one]
  have h2 : |(LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det| *
      |(LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det| = 1 := by
    rw [← abs_mul, ← Matrix.det_mul, hM, Matrix.det_one, abs_one]
  have hd : |(LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det| = 1 := by
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · exact h
    · linarith [abs_nonneg (LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det]
  rw [Bm_eq X hy g, Matrix.det_mul, abs_mul, hd, mul_one]
  exact le_abs_self _

theorem reduce {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) {m : ℝ} (hm : 0 < m)
    (hmin : ∀ v ∈ X.Λ, v ≠ 0 → m ≤ Qy X y v) :
    ∃ f : Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ,
      (∀ i, Qy X y (f i) ≤ 2 ^ (finrank ℤ X.Λ * (finrank ℤ X.Λ - 1)) *
        |(Bm X (RealPlaceEmbeddings.zb X)).det| / m ^ (finrank ℤ X.Λ - 1)) ∧
      ∀ (v : X.Λ) (i : Fin (finrank ℤ X.Λ)),
        ((f.repr v i : ℤ) : ℝ) ^ 2 ≤ 9 ^ (finrank ℤ X.Λ) * Qy X y v / m := by
  set g := RealPlaceEmbeddings.zb X with hgdef
  have hcoe : ∀ x : Fin (finrank ℤ X.Λ) → ℤ,
      ((∑ i, x i • g i : X.Λ) : Fin r → E) = ∑ i, x i • (g i : Fin r → E) := by
    intro x; simp
  have hint : ∀ x : Fin (finrank ℤ X.Λ) → ℤ, x ≠ 0 →
      m ≤ (fun i => (x i : ℝ)) ⬝ᵥ (Am X y g *ᵥ fun i => (x i : ℝ)) := by
    intro x hx
    rw [quad_int]
    refine hmin _ ?_ ?_
    · rw [← hcoe]; exact (∑ i, x i • g i : X.Λ).2
    · intro h0
      rw [← hcoe] at h0
      have h1 : (∑ i, x i • g i : X.Λ) = 0 := Subtype.ext h0
      exact hx (funext (Fintype.linearIndependent_iff.mp g.linearIndependent x h1))
  obtain ⟨eb, h1, h2⟩ := ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.redGram_holds (finrank ℤ X.Λ) (Am X y g) m
    |(Bm X g).det| (Am_posDef X y (fun τ => (hy τ).1) g) hm hint (det_Am_le X hy g)
  refine ⟨eb.map g.equivFun.symm, fun i => ?_, fun v i => ?_⟩
  · have h3 := h1 i
    rw [quad_int, ← hcoe] at h3
    simpa [Basis.equivFun_symm_apply] using h3
  · have h3 := h2 (g.equivFun v) i
    rw [quad_int, ← hcoe] at h3
    simpa [Basis.map_repr, Basis.equivFun_symm_apply, g.sum_repr] using h3

end IntegralBasisReduction

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientMatrices
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

section Fam

variable {ι : Type} [Fintype ι]

def kap (b : ι → Fin 2 → Fin 2 → ℂ) : ι → Fin 2 → Fin 2 → ℝ :=
  fun τ i k => if (i : ℕ) ≤ k then (b τ i k).re else (b τ k i).im

def th (y : ι → Fin 2 → Fin 2 → ℝ) : ι → Fin 2 → Fin 2 → ℂ :=
  fun τ i k => if i = k then (y τ i k : ℂ) else if (i : ℕ) < k then (y τ i k : ℂ) + I * y τ k i
    else (y τ k i : ℂ) - I * y τ i k

def kapL : (ι → Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] (ι → Fin 2 → Fin 2 → ℝ) where
  toFun := kap
  map_add' b c := by
    funext τ i k; simp only [kap, Pi.add_apply]; split_ifs <;> simp
  map_smul' s b := by
    funext τ i k; simp only [kap, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp

def thL : (ι → Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (ι → Fin 2 → Fin 2 → ℂ) where
  toFun := th
  map_add' y z := by
    funext τ i k; simp only [th, Pi.add_apply]; split_ifs <;> push_cast <;> ring
  map_smul' s y := by
    funext τ i k; simp only [th, Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Complex.real_smul]
    split_ifs <;> push_cast <;> ring

lemma th_herm (y : ι → Fin 2 → Fin 2 → ℝ) : IsHermFam (th y) := by
  intro τ i k
  fin_cases i <;> fin_cases k <;> simp [th] <;> ring

lemma kap_th (y : ι → Fin 2 → Fin 2 → ℝ) : kap (th y) = y := by
  funext τ i k
  fin_cases i <;> fin_cases k <;> simp [kap, th]

lemma th_kap {b : ι → Fin 2 → Fin 2 → ℂ} (hb : IsHermFam b) : th (kap b) = b := by
  funext τ i k
  have h00 := hb τ 0 0
  have h11 := hb τ 1 1
  have h01 := hb τ 0 1
  rw [Complex.ext_iff] at h00 h11 h01
  simp at h00 h11 h01
  fin_cases i <;> fin_cases k <;> apply Complex.ext <;> simp [th, kap] <;> linarith

lemma th_zero : th (0 : ι → Fin 2 → Fin 2 → ℝ) = 0 := by
  funext τ i k
  simp [th]

lemma conj_herm {χ : ι → Fin 2 → Fin 2 → ℂ} (h : IsHermFam χ) :
    IsHermFam (fun τ i k => conj (χ τ i k)) := by
  intro τ i k
  show conj (χ τ k i) = conj (conj (χ τ i k))
  rw [h τ i k]

def pr (χ b : ι → Fin 2 → Fin 2 → ℂ) : ℝ := (∑ τ, ∑ i, ∑ k, χ τ i k * b τ i k).re

lemma pr_add_right (χ b c : ι → Fin 2 → Fin 2 → ℂ) : pr χ (b + c) = pr χ b + pr χ c := by
  simp only [pr, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]

lemma pr_add_left (χ ψ b : ι → Fin 2 → Fin 2 → ℂ) : pr (χ + ψ) b = pr χ b + pr ψ b := by
  simp only [pr, Pi.add_apply, add_mul, Finset.sum_add_distrib, Complex.add_re]

lemma pr_smul_right (χ b : ι → Fin 2 → Fin 2 → ℂ) (s : ℝ) : pr χ ((s : ℂ) • b) = s * pr χ b := by
  simp only [pr, Pi.smul_apply, smul_eq_mul, mul_left_comm _ (s : ℂ), ← Finset.mul_sum, Complex.re_ofReal_mul]

lemma pr_smul_left (χ b : ι → Fin 2 → Fin 2 → ℂ) (s : ℝ) : pr ((s : ℂ) • χ) b = s * pr χ b := by
  simp only [pr, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, Complex.re_ofReal_mul]

def prL (χ : ι → Fin 2 → Fin 2 → ℂ) : (ι → Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] ℝ where
  toFun := pr χ
  map_add' := pr_add_right χ
  map_smul' s b := by rw [← Complex.coe_smul, pr_smul_right]; rfl

def prR (b : ι → Fin 2 → Fin 2 → ℂ) : (ι → Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] ℝ where
  toFun χ := pr χ b
  map_add' χ ψ := pr_add_left χ ψ b
  map_smul' s χ := by simp only [RingHom.id_apply, smul_eq_mul]; rw [← Complex.coe_smul, pr_smul_left]

lemma pr_sum {N : ℕ} (χ : ι → Fin 2 → Fin 2 → ℂ) (c : Fin N → ℝ) (ω : Fin N → ι → Fin 2 → Fin 2 → ℂ) :
    pr χ (∑ j, (c j : ℂ) • ω j) = ∑ j, c j * pr χ (ω j) := by
  show prL χ (∑ j, (c j : ℂ) • ω j) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => pr_smul_right χ (ω j) (c j)

lemma eq_zero_of_pr_conj {χ : ι → Fin 2 → Fin 2 → ℂ}
    (h : pr χ (fun τ i k => conj (χ τ i k)) = 0) : χ = 0 := by
  simp only [pr, Complex.mul_conj] at h
  simp only [← Complex.ofReal_sum, Complex.ofReal_re] at h
  funext τ i k
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _)] at h
  have h2 := h τ (Finset.mem_univ _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun k _ =>
    Complex.normSq_nonneg _)] at h2
  have h3 := h2 i (Finset.mem_univ _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg _)] at h3
  exact Complex.normSq_eq_zero.mp (h3 k (Finset.mem_univ _))

lemma finrank_rfam : Module.finrank ℝ (ι → Fin 2 → Fin 2 → ℝ) = 4 * Fintype.card ι := by
  rw [Module.finrank_pi_fintype]
  simp [Module.finrank_pi_fintype, mul_comm]

end Fam

section Basis

variable {ι : Type} [Fintype ι] {N : ℕ} (ω : Fin N → ι → Fin 2 → Fin 2 → ℂ)

lemma kap_li (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω) :
    LinearIndependent ℝ (fun j => kap (ω j)) := by
  rw [linearIndependent_iff'] at hli ⊢
  intro s g hg i hi
  refine hli s g ?_ i hi
  have h := congrArg thL hg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  exact congrArg _ (th_kap (hω j)).symm

def basR (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω) (hN : N = 4 * Fintype.card ι) :
    Module.Basis (Fin N) ℝ (ι → Fin 2 → Fin 2 → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank' _ (kap_li ω hω hli) (by rw [Fintype.card_fin, finrank_rfam, hN])

lemma herm_eq_sum (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω)
    (hN : N = 4 * Fintype.card ι) {b : ι → Fin 2 → Fin 2 → ℂ} (hb : IsHermFam b) :
    ∃ s : Fin N → ℝ, b = ∑ j, (s j : ℂ) • ω j := by
  obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin N) ℝ (ι → Fin 2 → Fin 2 → ℝ), ⇑B = fun j => kap (ω j) :=
    ⟨basR ω hω hli hN, by unfold basR; exact coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _⟩
  refine ⟨B.repr (kap b), ?_⟩
  have hsum := B.sum_repr (kap b)
  simp only [hB] at hsum
  calc b = thL (kap b) := (th_kap hb).symm
    _ = thL (∑ j, B.repr (kap b) j • kap (ω j)) := by rw [hsum]
    _ = ∑ j, (B.repr (kap b) j : ℂ) • ω j := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, Complex.coe_smul]
        exact congrArg _ (th_kap (hω j))

def phiL : (ι → Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  LinearMap.pi fun j => (2 : ℝ) • ((prR (ω j)).comp thL)

lemma phiL_apply (z : ι → Fin 2 → Fin 2 → ℝ) (j : Fin N) : phiL ω z j = 2 * pr (th z) (ω j) := rfl

lemma phiL_inj (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω)
    (hN : N = 4 * Fintype.card ι) : Function.Injective (phiL ω) := by
  refine (injective_iff_map_eq_zero (phiL ω)).mpr fun z hz => ?_
  have hp : ∀ j, pr (th z) (ω j) = 0 := fun j => by
    have h := congrFun hz j
    rw [phiL_apply] at h
    simpa using h
  obtain ⟨s, hs⟩ := herm_eq_sum ω hω hli hN (conj_herm (th_herm z))
  have h0 : pr (th z) (fun τ i k => conj (th z τ i k)) = 0 := by
    rw [hs, pr_sum]
    simp [hp]
  have hz0 := eq_zero_of_pr_conj h0
  rw [← kap_th z, hz0]
  funext τ i k
  simp [kap]

lemma phiL_surj (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω)
    (hN : N = 4 * Fintype.card ι) : Function.Surjective (phiL ω) := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [finrank_rfam, Module.finrank_fin_fun, hN])).mp (phiL_inj ω hω hli hN)

def chiOf (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω)
    (hN : N = 4 * Fintype.card ι) (m : Fin N → ℝ) : ι → Fin 2 → Fin 2 → ℂ :=
  th ((LinearEquiv.ofBijective (phiL ω) ⟨phiL_inj ω hω hli hN, phiL_surj ω hω hli hN⟩).symm m)

variable (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω) (hN : N = 4 * Fintype.card ι)

lemma chiOf_herm (m : Fin N → ℝ) : IsHermFam (chiOf ω hω hli hN m) := th_herm _

lemma chiOf_pair (m : Fin N → ℝ) (j : Fin N) : 2 * pr (chiOf ω hω hli hN m) (ω j) = m j := by
  unfold chiOf
  exact congrFun (LinearEquiv.apply_symm_apply
    (LinearEquiv.ofBijective (phiL ω) ⟨phiL_inj ω hω hli hN, phiL_surj ω hω hli hN⟩) m) j

lemma chiOf_eq {χ : ι → Fin 2 → Fin 2 → ℂ} (hχ : IsHermFam χ) {m : Fin N → ℝ}
    (hm : ∀ j, 2 * pr χ (ω j) = m j) : χ = chiOf ω hω hli hN m := by
  unfold chiOf
  have he : phiL ω (kap χ) = m := funext fun j => by rw [phiL_apply, th_kap hχ, hm j]
  rw [← th_kap hχ]
  congr 1
  rw [← he]
  exact ((LinearEquiv.ofBijective (phiL ω) ⟨phiL_inj ω hω hli hN, phiL_surj ω hω hli hN⟩).symm_apply_apply
    (kap χ)).symm

lemma chiOf_inj : Function.Injective (chiOf ω hω hli hN) := by
  intro m m' h
  funext j
  rw [← chiOf_pair ω hω hli hN m j, ← chiOf_pair ω hω hli hN m' j, h]

end Basis

section ZbFacts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E)

lemma mat_Zb (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.Zb u b x) τ = X.zmat u b τ * mat x τ := rfl

lemma zmat_zero (τ : X.Ψ) : X.zmat u 0 τ = 1 := by
  ext a j
  simp [Data.zmat, Matrix.one_apply]

lemma Zb_zero (x : Frame X.Ψ r) : X.Zb u 0 x = x := by
  funext τ
  show X.zmat u 0 τ * mat x τ = x τ
  rw [zmat_zero, one_mul]
  rfl

def fac (la : Wt X.Ψ r) (x : Frame X.Ψ r) : ℝ :=
  ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)

lemma pnorm_eq (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la P x = ‖P x‖ * fac X la x := rfl

lemma fac_nonneg (la : Wt X.Ψ r) (x : Frame X.Ψ r) : 0 ≤ fac X la x := Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _

end ZbFacts

end

end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ExponentialGrowthExclusion
namespace ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion

open NumberField Complex MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma exists_fd (X : Data E r) (la : Wt X.Ψ r) :
    ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧ IsAddFundamentalDomain (X.periods la) D volume ∧
      0 < volume D ∧ volume D < ⊤ := by
  let L : Submodule ℤ (X.Ψ → ℝ) := (X.periods la).toIntSubmodule
  haveI : DiscreteTopology L := inferInstanceAs (DiscreteTopology (X.periods la))
  haveI : IsZLattice ℝ L := ⟨by simpa [L] using RealEmbeddingCharacters.periods_span (X := X) (la := la)⟩
  haveI := ZLattice.module_free ℝ L
  haveI := ZLattice.module_finite ℝ L
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  have hspan : Submodule.span ℤ (Set.range b) = L := by
    show Submodule.span ℤ (Set.range ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) = L
    rw [Module.Basis.ofZLatticeBasis_span]
  refine ⟨ZSpan.fundamentalDomain b, ZSpan.fundamentalDomain_measurableSet b, ?_, ?_, ?_⟩
  · have h := ZSpan.isAddFundamentalDomain b volume
    rw [hspan] at h
    exact h
  · exact pos_iff_ne_zero.2 (ZSpan.measure_fundamentalDomain_ne_zero b)
  · exact (ZSpan.fundamentalDomain_isBounded b).measure_lt_top

lemma integral_swap_of_bdd {m n : Type} [Fintype m] [Fintype n] {D : Set (m → ℝ)} {K : Set (n → ℝ)}
    (hD : volume D < ⊤) (hK : volume K < ⊤) {f : (m → ℝ) → (n → ℝ) → ℂ}
    (hf : Continuous (Function.uncurry f)) {M : ℝ} (hM : ∀ s t, ‖f s t‖ ≤ M) :
    ∫ s in D, ∫ t in K, f s t = ∫ t in K, ∫ s in D, f s t := by
  haveI : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.2 hD.ne
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.ne
  apply MeasureTheory.integral_integral_swap
  exact Integrable.mono' (integrable_const M) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => hM p.1 p.2)

end

end ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
end
