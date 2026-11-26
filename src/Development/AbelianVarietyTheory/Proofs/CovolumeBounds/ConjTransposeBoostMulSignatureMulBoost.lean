module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ConjTransposeBoostMulSignatureMulBoost
open Matrix WithLp
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace GlobalTheory
namespace MatrixBall

section general

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
lemma norm_toEuclideanLin_le (M : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ‖toEuclideanLin M x‖ ≤ ‖M‖ * ‖x‖ :=
  M.l2_opNorm_mulVec x

lemma dotProduct_mulVec_eq_inner (M : Matrix n n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ M *ᵥ v = ⟪(toLp 2 v : EuclideanSpace ℂ n), toEuclideanLin M (toLp 2 v)⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

lemma inner_conjTranspose_mul (M N : Matrix m n ℂ) (x y : EuclideanSpace ℂ n) :
    ⟪x, toEuclideanLin (Mᴴ * N) y⟫_ℂ = ⟪toEuclideanLin M x, toEuclideanLin N y⟫_ℂ := by
  rw [toLpLin_mul (q := 2), LinearMap.comp_apply, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_right]

lemma inner_one_sub (M : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ⟪x, toEuclideanLin (1 - Mᴴ * M) x⟫_ℂ = ((‖x‖ ^ 2 - ‖toEuclideanLin M x‖ ^ 2 : ℝ) : ℂ) := by
  rw [map_sub, LinearMap.sub_apply, inner_sub_right, inner_conjTranspose_mul, toLpLin_one,
    LinearMap.id_apply, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp

omit [DecidableEq n] in
lemma isHermitian_one_sub [DecidableEq n] (M : Matrix m n ℂ) : (1 - Mᴴ * M).IsHermitian :=
  isHermitian_one.sub (isHermitian_conjTranspose_mul_self M)

lemma posDef_one_sub_conjTranspose_mul {Z : Matrix m n ℂ} (hZ : ‖Z‖ < 1) :
    (1 - Zᴴ * Z).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (isHermitian_one_sub Z) fun v hv => ?_
  rw [dotProduct_mulVec_eq_inner, inner_one_sub]
  have hx : 0 < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ := by
    rw [norm_pos_iff]; intro h; exact hv (by simpa using h)
  have h1 := norm_toEuclideanLin_le Z (toLp 2 v)
  have h2 : ‖toEuclideanLin Z (toLp 2 v)‖ < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ := by nlinarith
  have h3 := norm_nonneg (toEuclideanLin Z (toLp 2 v))
  exact_mod_cast (by nlinarith : (0 : ℝ) < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 -
    ‖toEuclideanLin Z (toLp 2 v)‖ ^ 2)

theorem norm_lt_one_of_posDef {Z : Matrix m n ℂ} (hP : (1 - Zᴴ * Z).PosDef) : ‖Z‖ < 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have : Z = 0 := by ext i j; exact hn.elim j
    simp [this]
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ n) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 zero_le_one)
    (f := fun x => ‖toEuclideanLin Z x‖)
    ((toEuclideanLin Z).continuous_of_finiteDimensional.norm.continuousOn)
  have hx1 : ‖x‖ = 1 := by simpa using hx
  have hx0 : ofLp x ≠ 0 := by
    intro h
    have : x = 0 := by simpa using h
    simp [this] at hx1
  have h1 := hP.dotProduct_mulVec_pos hx0
  rw [dotProduct_mulVec_eq_inner, inner_one_sub, toLp_ofLp, hx1] at h1
  have h2 : (0 : ℝ) < 1 ^ 2 - ‖toEuclideanLin Z x‖ ^ 2 := by exact_mod_cast h1
  have h3 := norm_nonneg (toEuclideanLin Z x)
  have h4 : ‖toEuclideanLin Z x‖ < 1 := by nlinarith
  refine lt_of_le_of_lt ?_ h4
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm h3 fun y hy => ?_
  exact hmax (by simpa using hy)

theorem posDef_iff_norm_lt_one (Z : Matrix m n ℂ) : (1 - Zᴴ * Z).PosDef ↔ ‖Z‖ < 1 :=
  ⟨norm_lt_one_of_posDef, posDef_one_sub_conjTranspose_mul⟩

end general

section hermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

end hermitian

section boost

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

def invSqrt {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) : Matrix n n ℂ :=
  (CFC.sqrt M)⁻¹

def boost (Z : Matrix p q ℂ) : Matrix (p ⊕ q) (p ⊕ q) ℂ :=
  fromBlocks (invSqrt (1 - Z * Zᴴ)) (Z * invSqrt (1 - Zᴴ * Z))
    (Zᴴ * invSqrt (1 - Z * Zᴴ)) (invSqrt (1 - Zᴴ * Z))

section invSqrt

variable {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}

end invSqrt

variable {Z : Matrix p q ℂ}

end boost

end MatrixBall

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LineDerivListEqIteratedFDeriv
open Filter Topology
open scoped ContDiff

namespace GlobalTheory

section Def

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

noncomputable def lineDerivList : List E → (E → V) → E → V
  | [], F => F
  | v :: l, F => fun z => lineDeriv 𝕜 (lineDerivList l F) z v

variable {𝕜}

theorem lineDerivList_cons (v : E) (l : List E) (F : E → V) :
    lineDerivList 𝕜 (v :: l) F = fun z => lineDeriv 𝕜 (lineDerivList 𝕜 l F) z v := rfl

theorem lineDerivList_append (l₁ l₂ : List E) (F : E → V) :
    lineDerivList 𝕜 (l₁ ++ l₂) F = lineDerivList 𝕜 l₁ (lineDerivList 𝕜 l₂ F) := by
  induction l₁ with
  | nil => rfl
  | cons v l ih => simp only [List.cons_append, lineDerivList_cons, ih]

theorem lineDerivList_const_smul (l : List E) (c : 𝕜) (F : E → V) :
    lineDerivList 𝕜 l (fun z => c • F z) = fun z => c • lineDerivList 𝕜 l F z := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    simp only [lineDerivList_cons, ih, lineDeriv]
    exact deriv_fun_const_smul_field c _

@[simp] theorem lineDerivList_zero (l : List E) :
    lineDerivList 𝕜 l (fun _ => (0 : V)) = fun _ => 0 := by
  simpa using lineDerivList_const_smul l (0 : 𝕜) (fun _ => (0 : V))

theorem lineDerivList_comp_linearMap {E' : Type*} [AddCommGroup E'] [Module 𝕜 E']
    (L : E' →ₗ[𝕜] E) (l : List E') (F : E → V) :
    lineDerivList 𝕜 l (fun z => F (L z)) = fun z => lineDerivList 𝕜 (l.map L) F (L z) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    simp only [lineDerivList_cons, ih, lineDeriv, List.map_cons, map_add (f := _), map_smul]

theorem lineDerivList_comp_add_const (c : E) (l : List E) (F : E → V) :
    lineDerivList 𝕜 l (fun z => F (z + c)) = fun z => lineDerivList 𝕜 l F (z + c) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    simp only [lineDerivList_cons, ih, lineDeriv, add_right_comm]

theorem lineDerivList_map_smul {κ : Type*} (c : κ → 𝕜) (e : κ → E) (l : List κ) (F : E → V) :
    lineDerivList 𝕜 (l.map fun k => c k • e k) F
      = fun z => (l.map c).prod • lineDerivList 𝕜 (l.map e) F z := by
  induction l with
  | nil => simp
  | cons v l ih =>
    funext z
    simp only [List.map_cons, lineDerivList_cons, ih, lineDeriv_smul, List.prod_cons, mul_smul]
    congr 1
    simp only [lineDeriv]
    exact deriv_fun_const_smul_field _ _

theorem lineDerivList_replicate (n : ℕ) (v : E) (F : E → V) (z : E) (t : 𝕜) :
    lineDerivList 𝕜 (List.replicate n v) F (z + t • v)
      = iteratedDeriv n (fun s : 𝕜 => F (z + s • v)) t := by
  induction n generalizing t with
  | zero => simp [lineDerivList]
  | succ n ih =>
    rw [List.replicate_succ, lineDerivList_cons, iteratedDeriv_succ]
    simp only [lineDeriv, add_assoc, ← add_smul, ih]
    rw [deriv_comp_const_add (f := iteratedDeriv n (fun s : 𝕜 => F (z + s • v))), add_zero]

end Def

section Analytic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

theorem lineDerivList_congr {F G : E → V} {a : E} (h : F =ᶠ[𝓝 a] G) (l : List E) :
    lineDerivList 𝕜 l F =ᶠ[𝓝 a] lineDerivList 𝕜 l G := by
  induction l with
  | nil => exact h
  | cons v l ih =>
    filter_upwards [ih.eventuallyEq_nhds] with z hz
    exact hz.lineDeriv_eq

variable [CompleteSpace V]

theorem analyticAt_lineDeriv {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (v : E) :
    AnalyticAt 𝕜 (fun z => lineDeriv 𝕜 F z v) a := by
  have h1 : AnalyticAt 𝕜 (fun z => fderiv 𝕜 F z v) a :=
    ((ContinuousLinearMap.apply 𝕜 V v).analyticAt _).comp h.fderiv
  refine h1.congr ?_
  filter_upwards [h.eventually_analyticAt] with z hz
  exact hz.differentiableAt.lineDeriv_eq_fderiv.symm

theorem analyticAt_lineDerivList {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (l : List E) :
    AnalyticAt 𝕜 (lineDerivList 𝕜 l F) a := by
  induction l with
  | nil => exact h
  | cons v l ih => exact analyticAt_lineDeriv ih v

theorem lineDerivList_ofFn {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) {n : ℕ} (m : Fin n → E) :
    lineDerivList 𝕜 (List.ofFn m) F a = iteratedFDeriv 𝕜 n F a m := by
  induction n generalizing a with
  | zero => simp [lineDerivList]
  | succ n ih =>
    have hev : lineDerivList 𝕜 (List.ofFn fun i => m i.succ) F
        =ᶠ[𝓝 a] fun z => iteratedFDeriv 𝕜 n F z (Fin.tail m) := by
      filter_upwards [h.eventually_analyticAt] with z hz
      exact ih hz _
    have hd : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n F) a :=
      (h.contDiffAt (n := ω)).differentiableAt_iteratedFDeriv (by simp)
    rw [List.ofFn_succ, lineDerivList_cons, iteratedFDeriv_succ_apply_left]
    dsimp only
    rw [(analyticAt_lineDerivList h _).differentiableAt.lineDeriv_eq_fderiv, hev.fderiv_eq,
      fderiv_continuousMultilinear_apply_const_apply hd]

theorem lineDerivList_eq_iteratedFDeriv {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (l : List E) :
    lineDerivList 𝕜 l F a = iteratedFDeriv 𝕜 l.length F a l.get := by
  rw [← lineDerivList_ofFn h, List.ofFn_get]

theorem lineDerivList_swap {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (v w : E) :
    lineDerivList 𝕜 [v, w] F a = lineDerivList 𝕜 [w, v] F a := by
  have h1 := lineDerivList_ofFn h ![v, w]
  have h2 := lineDerivList_ofFn h ![w, v]
  have h3 := (h.contDiffAt (n := ω)).iteratedFDeriv_comp_perm ![v, w] (Equiv.swap 0 1)
  have h4 : ![v, w] ∘ (Equiv.swap (0 : Fin 2) 1) = ![w, v] := by
    funext i; fin_cases i <;> simp
  rw [h4] at h3
  simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ] at h1 h2
  rw [h1, h2, h3]

theorem lineDerivList_perm {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) {l₁ l₂ : List E}
    (hl : l₁.Perm l₂) : lineDerivList 𝕜 l₁ F a = lineDerivList 𝕜 l₂ F a := by
  induction hl generalizing a with
  | nil => rfl
  | cons v _ ih =>
    refine Filter.EventuallyEq.lineDeriv_eq ?_
    filter_upwards [h.eventually_analyticAt] with z hz
    exact ih hz
  | swap v w l => exact lineDerivList_swap (analyticAt_lineDerivList h l) w v
  | trans _ _ ih₁ ih₂ => exact (ih₁ h).trans (ih₂ h)

theorem lineDerivList_add {F G : E → V} {a : E} (hF : AnalyticAt 𝕜 F a) (hG : AnalyticAt 𝕜 G a)
    (l : List E) :
    lineDerivList 𝕜 l (fun z => F z + G z) a
      = lineDerivList 𝕜 l F a + lineDerivList 𝕜 l G a := by
  have hFG : AnalyticAt 𝕜 (fun z => F z + G z) a := hF.add hG
  rw [lineDerivList_eq_iteratedFDeriv hFG, lineDerivList_eq_iteratedFDeriv hF,
    lineDerivList_eq_iteratedFDeriv hG,
    fun_iteratedFDeriv_add_apply (hF.contDiffAt) (hG.contDiffAt)]
  rfl

theorem lineDerivList_sum {κ : Type*} (s : Finset κ) {F : κ → E → V} {a : E}
    (hF : ∀ k ∈ s, AnalyticAt 𝕜 (F k) a) (l : List E) :
    lineDerivList 𝕜 l (fun z => ∑ k ∈ s, F k z) a = ∑ k ∈ s, lineDerivList 𝕜 l (F k) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hs : ∀ k ∈ s, AnalyticAt 𝕜 (F k) a := fun k hk => hF k (Finset.mem_insert_of_mem hk)
    simp only [Finset.sum_insert hj]
    rw [lineDerivList_add (hF j (Finset.mem_insert_self _ _)) (Finset.analyticAt_fun_sum _ hs),
      ih hs]

end Analytic

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfEvalGridEqZeroOfTotalDegreeLe
namespace GlobalTheory

open MvPolynomial

section Vanishing

variable {σ R : Type*} [Finite σ] [CommRing R] [IsDomain R] [CharZero R]

theorem eq_zero_of_eval_box_eq_zero (d : σ → ℕ) (P : MvPolynomial σ R)
    (hdeg : ∀ i, P.degreeOf i ≤ d i)
    (hP : ∀ x : σ → ℕ, (∀ i, x i ≤ d i) → eval (fun i => (x i : R)) P = 0) : P = 0 := by
  classical
  refine eq_zero_of_eval_zero_at_prod_finset P
    (fun i => (Finset.range (d i + 1)).image (Nat.cast : ℕ → R)) (fun i => ?_) (fun x hx => ?_)
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    exact Nat.lt_succ_of_le (hdeg i)
  · choose n hn hnx using fun i => Finset.mem_image.1 (hx i)
    have : x = fun i => (n i : R) := funext fun i => (hnx i).symm
    rw [this]
    exact hP n fun i => Nat.lt_succ_iff.1 (Finset.mem_range.1 (hn i))

theorem eq_zero_of_eval_grid_eq_zero (d : ℕ) (P : MvPolynomial σ R)
    (hdeg : ∀ i, P.degreeOf i ≤ d)
    (hP : ∀ x : σ → ℕ, (∀ i, x i ≤ d) → eval (fun i => (x i : R)) P = 0) : P = 0 :=
  eq_zero_of_eval_box_eq_zero (fun _ => d) P hdeg hP

end Vanishing

section Span

variable {σ A K V : Type*} [Finite σ] [Field K] [CharZero K] [CommSemiring A] [Algebra A K]
  [AddCommGroup V] [Module K V]

theorem mem_of_grid_mem (d : ℕ) (Φ : (σ → A) → V)
    (hΦ : ∀ l : Module.Dual K V, ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧
      ∀ x, l (Φ x) = eval (fun i => algebraMap A K (x i)) P)
    (U : Submodule K V)
    (hU : ∀ x : σ → ℕ, (∀ i, x i ≤ d) → Φ (fun i => (x i : A)) ∈ U) (y : σ → A) :
    Φ y ∈ U := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U]
  intro l hl
  obtain ⟨P, hdeg, hP⟩ := hΦ l
  have h0 : P = 0 := by
    refine eq_zero_of_eval_grid_eq_zero d P hdeg fun x hx => ?_
    have := (Submodule.mem_dualAnnihilator l).1 hl _ (hU x hx)
    rw [hP] at this
    simpa using this
  rw [hP, h0, map_zero]

theorem span_grid_eq_span_range (d : ℕ) (Φ : (σ → A) → V)
    (hΦ : ∀ l : Module.Dual K V, ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧
      ∀ x, l (Φ x) = eval (fun i => algebraMap A K (x i)) P) :
    Submodule.span K ((fun x : σ → ℕ => Φ fun i => (x i : A)) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range Φ) := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨x, -, rfl⟩
    exact ⟨_, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    refine mem_of_grid_mem d Φ hΦ _ (fun x hx => ?_) y
    apply Submodule.subset_span
    exact ⟨x, hx, rfl⟩

omit [Finite σ] [CharZero K] in
theorem exists_poly_dual_sum_monomial_smul (d : ℕ) (s : Finset (σ →₀ ℕ)) (v : (σ →₀ ℕ) → V)
    (hs : ∀ a ∈ s, ∀ i, a i ≤ d) (l : Module.Dual K V) :
    ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧ ∀ x : σ → A,
      l (∑ a ∈ s, (a.prod fun i n => algebraMap A K (x i) ^ n) • v a) =
        eval (fun i => algebraMap A K (x i)) P := by
  classical
  refine ⟨∑ a ∈ s, monomial a (l (v a)), fun i => ?_, fun x => ?_⟩
  · rw [degreeOf_le_iff]
    intro m hm
    obtain ⟨a, ha, hma⟩ := Finset.mem_biUnion.1 (support_sum hm)
    have := Finset.mem_singleton.1 (support_monomial_subset hma)
    rw [this]
    exact hs a ha i
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_smul, eval_monomial, smul_eq_mul, mul_comm]

theorem span_grid_eq_span_range_of_eq_sum (d : ℕ) (Φ : (σ → A) → V)
    (s : Finset (σ →₀ ℕ)) (v : (σ →₀ ℕ) → V) (hs : ∀ a ∈ s, ∀ i, a i ≤ d)
    (hΦ : ∀ x, Φ x = ∑ a ∈ s, (a.prod fun i n => algebraMap A K (x i) ^ n) • v a) :
    Submodule.span K ((fun x : σ → ℕ => Φ fun i => (x i : A)) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range Φ) := by
  refine span_grid_eq_span_range d Φ fun l => ?_
  simp only [hΦ]
  exact exists_poly_dual_sum_monomial_smul d s v hs l

theorem span_grid_eval_eq_span_range {B : Type*} [CommRing B] [Algebra K B] (d : ℕ)
    (F : MvPolynomial σ B) (hF : ∀ i, F.degreeOf i ≤ d) :
    Submodule.span K ((fun x : σ → ℕ => eval (fun i => (x i : B)) F) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range fun x : σ → A =>
        eval (fun i => algebraMap K B (algebraMap A K (x i))) F) := by
  have h := span_grid_eq_span_range_of_eq_sum (K := K) d
    (fun x : σ → A => eval (fun i => algebraMap K B (algebraMap A K (x i))) F)
    F.support (fun a => F.coeff a) (fun a ha i => (degreeOf_le_iff.1 (hF i)) a ha)
    (fun x => by
      rw [eval_eq]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Algebra.smul_def, Finsupp.prod, map_prod, mul_comm]
      simp only [map_pow])
  simpa only [map_natCast] using h

end Span

section Combination

variable {ι κ V : Type*} [Fintype ι] [AddCommGroup V] {W : ι → Type*}
  [∀ j, AddCommGroup (W j)]

theorem exists_nsmul_add_apply_ne_zero [∀ j, IsAddTorsionFree (W j)] (l : ∀ j, V →+ W j)
    (v w : V) :
    ∃ c : ℕ, c ≤ Fintype.card ι ∧ ∀ j, l j v ≠ 0 ∨ l j w ≠ 0 → l j (c • w + v) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  choose f hf hf0 using h
  have hinj : Function.Injective fun a : Fin (Fintype.card ι + 1) =>
      f a (Nat.lt_succ_iff.1 a.2) := by
    intro a b hab
    have h1 := hf0 a (Nat.lt_succ_iff.1 a.2)
    have h2 := hf0 b (Nat.lt_succ_iff.1 b.2)
    have h3 := hf a (Nat.lt_succ_iff.1 a.2)
    simp only at hab
    rw [← hab] at h2
    generalize f a _ = j at h1 h2 h3
    rw [map_add (f := _), map_nsmul] at h1 h2
    have hw : l j w ≠ 0 := by
      intro hw
      rw [hw, nsmul_zero, zero_add] at h1
      exact h3.elim (· h1) (· hw)
    have h4 : (a : ℕ) • l j w = (b : ℕ) • l j w := add_right_cancel (h1.trans h2.symm)
    have h5 : ((a : ℤ) - (b : ℤ)) • l j w = 0 := by
      rw [sub_smul, natCast_zsmul, natCast_zsmul, h4, sub_self]
    have h6 := (IsAddTorsionFree.zsmul_eq_zero_iff_left hw).1 h5
    exact Fin.ext (by omega)
  have := Fintype.card_le_of_injective _ hinj
  simp at this

theorem exists_sum_nsmul_apply_ne_zero_finset [∀ j, IsAddTorsionFree (W j)]
    (l : ∀ j, V →+ W j) (s : κ → V) (t : Finset κ) :
    ∃ c : κ → ℕ, (∀ k, c k ≤ Fintype.card ι) ∧
      ∀ j, (∃ k ∈ t, l j (s k) ≠ 0) → l j (∑ k ∈ t, c k • s k) ≠ 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, fun _ => Nat.zero_le _, fun j ⟨k, hk, _⟩ => absurd hk (by simp)⟩
  | insert a t ha ih =>
    obtain ⟨c, hc, hl⟩ := ih
    obtain ⟨n, hn, hln⟩ := exists_nsmul_add_apply_ne_zero l (∑ k ∈ t, c k • s k) (s a)
    refine ⟨Function.update c a n, fun k => ?_, fun j ⟨k, hk, hjk⟩ => ?_⟩
    · by_cases hk : k = a
      · subst hk; simpa using hn
      · simpa [hk] using hc k
    · rw [Finset.sum_insert ha, Function.update_self,
        Finset.sum_congr rfl (g := fun k => c k • s k) fun k hk => by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hk ha)]]
      apply hln
      rcases Finset.mem_insert.1 hk with rfl | hk
      · exact Or.inr hjk
      · exact Or.inl (hl j ⟨k, hk, hjk⟩)

theorem exists_sum_nsmul_apply_ne_zero [∀ j, IsAddTorsionFree (W j)] [Fintype κ]
    (l : ∀ j, V →+ W j) (s : κ → V) (h : ∀ j, ∃ k, l j (s k) ≠ 0) :
    ∃ c : κ → ℕ, (∀ k, c k ≤ Fintype.card ι) ∧ ∀ j, l j (∑ k, c k • s k) ≠ 0 := by
  obtain ⟨c, hc, hl⟩ := exists_sum_nsmul_apply_ne_zero_finset l s Finset.univ
  exact ⟨c, hc, fun j => hl j ((h j).imp fun k hk => ⟨Finset.mem_univ k, hk⟩)⟩

variable {K : Type*} [Field K] [CharZero K] [Module K V] [∀ j, Module K (W j)]

theorem exists_sum_natCast_smul_apply_ne_zero [Fintype κ]
    (l : ∀ j, V →ₗ[K] W j) (s : κ → V) (h : ∀ j, ∃ k, l j (s k) ≠ 0) :
    ∃ c : κ → ℕ, (∀ k, c k ≤ Fintype.card ι) ∧ ∀ j, l j (∑ k, (c k : K) • s k) ≠ 0 := by
  have : ∀ j, IsAddTorsionFree (W j) := fun j => by
    letI : HasUniqueDiv (W j) := HasUniqueDiv.of_isTorsionFree K (W j)
    infer_instance
  simp only [Nat.cast_smul_eq_nsmul]
  exact exists_sum_nsmul_apply_ne_zero (fun j => (l j).toAddMonoidHom) s h

end Combination

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsNeZeroMemFractionalIdealNormSqLe
namespace GlobalTheory

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped nonZeroDivisors NNReal ENNReal Classical

section General

variable (K : Type*) [Field K] [NumberField K]

theorem exists_ne_zero_mem_fractionalIdeal_place_le (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (g : InfinitePlace K → ℝ≥0) (h : minkowskiBound K I ≤ volume (convexBodyLT K g)) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧ ∀ w : InfinitePlace K, w a ≤ g w := by
  classical
  set S : Set (mixedSpace K) :=
    (Set.univ.pi (fun w : { w : InfinitePlace K // IsReal w } => Metric.closedBall 0 (g w))) ×ˢ
    (Set.univ.pi (fun w : { w : InfinitePlace K // IsComplex w } => Metric.closedBall 0 (g w)))
    with hS
  have hsub : convexBodyLT K g ⊆ S :=
    Set.prod_mono (Set.pi_mono fun _ _ => Metric.ball_subset_closedBall)
      (Set.pi_mono fun _ _ => Metric.ball_subset_closedBall)
  have hneg : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    simp only [hS, Set.mem_prod, Prod.fst_neg, Set.mem_pi, Set.mem_univ, Pi.neg_apply,
      mem_closedBall_zero_iff, norm_neg, forall_true_left, Prod.snd_neg] at hx ⊢
    exact hx
  have hconv : Convex ℝ S :=
    Convex.prod (convex_pi (fun _ _ => convex_closedBall _ _))
      (convex_pi (fun _ _ => convex_closedBall _ _))
  have hcomp : IsCompact S :=
    IsCompact.prod (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
      (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
  have h_fund := ZSpan.isAddFundamentalDomain' (fractionalIdealLatticeBasis K I) volume
  have : Countable (Submodule.span ℤ
      (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range (fractionalIdealLatticeBasis K I)))
    infer_instance
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      h_fund hneg hconv hcomp (h.trans (measure_mono hsub))
  rw [Submodule.mem_toAddSubgroup, mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨a, ha, by simpa using h_nz, fun w => ?_⟩
  simp only [hS, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left,
    mem_closedBall_zero_iff] at h_mem
  rw [← normAtPlace_apply]
  rcases isReal_or_isComplex w with hw | hw
  · rw [normAtPlace_apply_of_isReal hw]
    exact h_mem.1 ⟨w, hw⟩
  · rw [normAtPlace_apply_of_isComplex hw]
    exact h_mem.2 ⟨w, hw⟩

end General

section TotallyComplex

variable {E : Type*} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {f : ℕ}

theorem exists_ne_zero_mem_fractionalIdeal_norm_sq_le (hf : finrank ℚ E = 2 * f)
    (J : FractionalIdeal (𝓞 E)⁰ E) (hJ : J ≠ 0) :
    ∃ a ∈ J, a ≠ 0 ∧ ∀ τ : E →+* ℂ, ‖τ a‖ ^ 2 ≤
      2 / Real.pi * ((FractionalIdeal.absNorm J : ℝ) * √|(discr E : ℝ)|) ^ ((f : ℝ)⁻¹) := by
  classical
  have hc : nrComplexPlaces E = f := by
    have := IsTotallyComplex.finrank E
    omega
  have hr : nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  have hf0 : f ≠ 0 := by
    have : 0 < finrank ℚ E := finrank_pos
    omega
  set X : ℝ := (FractionalIdeal.absNorm J : ℝ) * √|(discr E : ℝ)| with hX
  have hN : (0 : ℝ) ≤ (FractionalIdeal.absNorm J : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg J
  have hX0 : 0 ≤ X := mul_nonneg hN (Real.sqrt_nonneg _)
  set B : ℝ := 2 / Real.pi * X ^ ((f : ℝ)⁻¹) with hB
  have hB0 : 0 ≤ B := by positivity
  let R : ℝ≥0 := ⟨√B, Real.sqrt_nonneg _⟩
  have hR : (R : ℝ) ^ 2 = B := Real.sq_sqrt hB0
  obtain ⟨a, ha, ha0, hle⟩ := exists_ne_zero_mem_fractionalIdeal_place_le E
    (Units.mk0 J hJ) (fun _ => R) (by
      rw [convexBodyLT_volume, minkowskiBound,
        volume_fundamentalDomain_fractionalIdealLatticeBasis,
        volume_fundamentalDomain_latticeBasis, mixedEmbedding.finrank,
        Finset.prod_pow_eq_pow_sum, sum_mult_eq, hf, convexBodyLTFactor, hc, hr]
      refine (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp (le_of_eq ?_)
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.coe_toReal,
        ENNReal.toReal_ofNat, Units.val_mk0, ENNReal.toReal_ofReal hN, pow_zero, one_mul,
        NNReal.coe_pow, NNReal.coe_real_pi, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
      rw [pow_mul (R : ℝ), hR, hB, mul_pow, Real.rpow_inv_natCast_pow hX0 hf0, hX, pow_mul,
        div_pow, show ((2 : ℝ) ^ 2) ^ f = 2 ^ f * 2 ^ f by rw [← mul_pow]; norm_num, inv_pow]
      have := Real.pi_pos
      field_simp)
  refine ⟨a, ha, ha0, fun τ => ?_⟩
  rw [← hR]
  have := hle (InfinitePlace.mk τ)
  rw [InfinitePlace.apply] at this
  exact pow_le_pow_left₀ (norm_nonneg _) this 2

end TotallyComplex

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SetIntegralPowEqZeroOfPosFreqEuclidean
section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummablePiProd
namespace GlobalTheory.SummablePiProd

universe u_1 u_2

theorem summable_pi_prod {ι : Type u_1} [inst : Fintype ι] {J : ι → Type u_2}
    {u : (i : ι) → J i → ℝ} (h0 : ∀ (i : ι) (j : J i), (0 : ℝ) ≤ u i j)
    (hs : ∀ (i : ι), Summable (u i)) :
    Summable fun (t : (i : ι) → J i) ↦ ∏ i : ι, u i (t i) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' j, u i j)
    (fun t => Finset.prod_nonneg fun i _ => h0 i (t i)) ?_
  intro s
  calc ∑ t ∈ s, ∏ i, u i (t i)
      ≤ ∑ t ∈ Fintype.piFinset (fun i => s.image (fun t => t i)), ∏ i, u i (t i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun t _ _ => Finset.prod_nonneg fun i _ => h0 i (t i))
        intro t ht
        exact Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ ht
    _ = ∏ i, ∑ j ∈ s.image (fun t => t i), u i j := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' j, u i j := by
        refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun j _ => h0 i j) ?_
        intro i _
        exact (hs i).sum_le_tsum _ (fun j _ => h0 i j)

end GlobalTheory.SummablePiProd
end

open MeasureTheory Filter Topology
open scoped Real FourierTransform Pointwise

namespace GlobalTheory

section Products

variable {ι : Type*} [Fintype ι] {J : ι → Type*}

theorem summable_prod_tuples {u : ∀ i, J i → ℝ} (h0 : ∀ i j, 0 ≤ u i j) (hu : ∀ i, Summable (u i)) :
    Summable fun t : ∀ i, J i => ∏ i, u i (t i) := by
  apply _root_.GlobalTheory.SummablePiProd.summable_pi_prod <;> assumption

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, NormedSpace 𝕜 (V i)] {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

theorem summable_norm_multilinear_tuples (M : ContinuousMultilinearMap 𝕜 V W)
    {x : ∀ i, J i → V i} (hx : ∀ i, Summable fun j => ‖x i j‖) :
    Summable fun t : ∀ i, J i => ‖M fun i => x i (t i)‖ :=
  .of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => M.le_opNorm _)
    ((summable_prod_tuples (fun i j => norm_nonneg (x i j)) hx).mul_left ‖M‖)

theorem hasSum_multilinear_tuples [CompleteSpace W] (M : ContinuousMultilinearMap 𝕜 V W)
    {x : ∀ i, J i → V i} {A : ∀ i, V i} (hx : ∀ i, Summable fun j => ‖x i j‖)
    (hA : ∀ i, HasSum (x i) (A i)) :
    HasSum (fun t : ∀ i, J i => M fun i => x i (t i)) (M A) := by
  classical
  have hs := (summable_norm_multilinear_tuples M hx).of_norm.hasSum
  have hpi : Tendsto (fun s : ∀ i, Finset (J i) => Fintype.piFinset s) atTop atTop := by
    refine tendsto_atTop_atTop_of_monotone (fun s s' hss => Fintype.piFinset_subset _ _ hss)
      fun T => ⟨fun i => T.image fun t => t i, fun t ht => ?_⟩
    exact Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ ht
  have h1 : Tendsto (fun s : ∀ i, Finset (J i) => M fun i => ∑ j ∈ s i, x i j) atTop (𝓝 (M A)) := by
    refine (M.cont.tendsto A).comp (tendsto_pi_nhds.2 fun i => ?_)
    refine Tendsto.comp (hA i) (g := fun s => ∑ j ∈ s, x i j) (f := fun s : ∀ i, Finset (J i) => s i) ?_
    refine tendsto_atTop_atTop_of_monotone (fun s s' hss => hss i) fun T => ?_
    exact ⟨Function.update (fun _ => ∅) i T, by simp⟩
  have h2 : Tendsto (fun s : ∀ i, Finset (J i) => M fun i => ∑ j ∈ s i, x i j) atTop
      (𝓝 (∑' t : ∀ i, J i, M fun i => x i (t i))) := by
    have hs' : Tendsto (fun s : Finset (∀ i, J i) => ∑ t ∈ s, M fun i => x i (t i)) atTop
        (𝓝 (∑' t : ∀ i, J i, M fun i => x i (t i))) := hs
    exact (hs'.comp hpi).congr fun s => (M.map_sum_finset x s).symm
  rwa [tendsto_nhds_unique h1 h2]

end Products

section Banach

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {R : Type*} [NormedCommRing R] [NormedAlgebra 𝕜 R]
  [CompleteSpace R] {J : Type*}

end Banach

section Characters

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G] {μ : Measure G}
  [μ.IsAddLeftInvariant] {L : AddSubgroup G} [Countable L] {D : Set G}

end Characters

section Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {D : Set E}

end Lattice

section Orthant

end Orthant

end GlobalTheory
end
