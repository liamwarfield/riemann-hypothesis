module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAt
public import Formalism.FilteredPoleLength.LocalDescentLevels.ExistsSumOfMemSpanImage
public import Formalism.FilteredPoleLength.LocalDescentLevels.DetMulEqSumPrincipal
public import Formalism.FilteredPoleLength.LocalDescentLevels.GAdjugateNormBound

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

structure TorusAt (X : Data E r) (x : Frame X.Ψ r) where
  T : PT E
  φ : (Fin r → E) →+ Vsp T.dim
  sg : ℝ
  sg_pm : sg = 1 ∨ sg = -1

  dim_pos : ∀ τ : X.Ψ, T.dim τ.1 = X.p0
  dim_neg : ∀ τ : X.Ψ, T.dim (ComplexEmbedding.conjugate τ.1) = r - X.p0

  e : X.Ψ → Fin r → (Fin r → ℂ)
  e_orth : ∀ τ a b, hermC τ.1 X.Gm (e τ a) (e τ b) = if a = b then ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0
  e_flag : ∀ τ (i : ℕ) (hi : i ≤ r),
    Submodule.span ℂ (Set.range fun a : Fin i => e τ (Fin.castLE hi a)) =
      Submodule.span ℂ (Set.range fun a : Fin i => col (mat x τ) (Fin.castLE hi a))

  coord_pos : ∀ (τ : X.Ψ) (a : Fin (T.dim τ.1)) (v : Fin r → E),
    (φ v) ⟨τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) *
      hermC τ.1 X.Gm (Data.emb τ.1 v) (e τ (Fin.castLE (by rw [dim_pos τ]; exact X.p0_le) a))
  coord_neg : ∀ (τ : X.Ψ) (a : Fin (T.dim (ComplexEmbedding.conjugate τ.1))) (v : Fin r → E),
    (φ v) ⟨ComplexEmbedding.conjugate τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) *
      (starRingEnd ℂ) (-hermC τ.1 X.Gm (Data.emb τ.1 v)
        (e τ ⟨X.p0 + a.1, by have h1 : a.1 < r - X.p0 := lt_of_lt_of_eq a.2 (dim_neg τ); have := X.p0_le; omega⟩))
  lat : ∀ y, y ∈ T.L ↔ ∃ v ∈ X.Λ, φ v = y
  act_eq : ∀ (α : 𝓞 E) (v : Fin r → E), φ ((α : E) • v) = act α (φ v)
  im_eq : ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, (Hf (φ u) (φ v)).im =
    sg * ((Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) : ℚ) : ℝ)

  w0 : 𝓞 E
  eps_eq : ∀ v ∈ X.Λ, (T.eps (φ v) : ℝ) = Real.cos (Real.pi * (Hf (φ v) (φ ((w0 : E) • v))).im)

  s : (Fin 1 → Vsp T.dim) → ℂ
  s_mem : s ∈ T.Sec 1 1
  s_ne : s ≠ 0

def TorusAtExistsStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ φ : X.Λ →+ ℤ, ∃ u ∈ X.Λ, ∀ v : X.Λ,
      (φ v : ℚ) = Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (v : Fin r → E))) →
    ∀ w0 : 𝓞 E, (∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ,
      Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) -
        Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) →
    ∀ x ∈ X.dom, ∃ A : TorusAt X x, A.w0 = w0

def TorusAtIsStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r)
    (A : TorusAt X x), IsTorusAt X x A.T

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchy
namespace ReciprocityTheory.ChartRestriction.G.I2

open Classical in
theorem gCauchy : GCauchyStatement := by
  intro ι _ F hF S hS α
  set N := Fintype.card ι
  let e : ι ≃ Fin N := Fintype.equivFin ι

  let T : (Fin N → ℂ) →L[ℂ] EuclideanSpace ℂ ι :=
    (EuclideanSpace.equiv ι ℂ).symm.toContinuousLinearMap.comp
      (LinearMap.funLeft ℂ ℂ e).toContinuousLinearMap
  have hT : ∀ z : Fin N → ℂ, ‖T z‖ ^ 2 = ∑ j, ‖z j‖ ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq]
    simp only [T, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
      LinearMap.coe_toContinuousLinearMap', Function.comp_apply, LinearMap.funLeft_apply]
    simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply]
    exact Fintype.sum_equiv e _ _ (fun i => by simp)
  have hTs : ∀ i : ι, T (Pi.single (e i) 1) = EuclideanSpace.single i 1 := by
    intro i
    ext j
    simp only [T, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
      LinearMap.coe_toContinuousLinearMap', Function.comp_apply, LinearMap.funLeft_apply,
      EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply, PiLp.single_apply]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Pi.single_apply, e.injective.ne h]
  set G : (Fin N → ℂ) → ℂ := F ∘ T
  have hG : Differentiable ℂ G := hF.comp T.differentiable
  have hGS : ∀ z, ‖G z‖ ^ 2 * Real.exp (-Real.pi * ∑ i, ‖z i‖ ^ 2) ≤ S := by
    intro z
    have := hS (T z)
    rwa [hT z] at this
  set k := Multiset.card (Finsupp.toMultiset α)
  set l : Fin k → Fin N := fun j =>
    e ((Finsupp.toMultiset α).toList.get (j.cast (Multiset.length_toList _).symm))
  have hc := cauchy_gauss_le G hG S hGS l
  have hF' : ContDiff ℂ k F := contDiff_of_differentiable_fd hF k
  have hcomp : iteratedFDeriv ℂ k G 0 (fun j => Pi.single (l j) 1) =
      iteratedFDeriv ℂ k F 0 (fun j => EuclideanSpace.single
        ((Finsupp.toMultiset α).toList.get (j.cast (Multiset.length_toList _).symm)) 1) := by
    rw [show G = F ∘ T from rfl, T.iteratedFDeriv_comp_right hF' 0 le_rfl]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
    congr 1
    funext j
    exact hTs _
  have hk : k = α.degree := by
    simp only [k, Finsupp.card_toMultiset]
    first
      | rfl
      | simp [Finsupp.sum, Finsupp.degree]
  have hdeg : (k : ℝ) = (α.degree : ℝ) := by rw [hk]
  unfold polyDeriv
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl, one_mul]
  rw [← hdeg, ← hcomp]
  exact hc

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfRsmulRight
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

lemma Hf_eq_inner {ι : Type} [Fintype ι] (v w : EuclideanSpace ℂ ι) : Hf v w = inner ℂ w v := by
  unfold Hf
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply, mul_comm]

lemma Hf_add_left {ι : Type} [Fintype ι] (v v' w : EuclideanSpace ℂ ι) :
    Hf (v + v') w = Hf v w + Hf v' w := by
  simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]

lemma Hf_zero_left {ι : Type} [Fintype ι] (v : EuclideanSpace ℂ ι) : Hf 0 v = 0 := by
  simp [Hf]

open Classical in
def prj {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : Vsp dim →ₗ[ℂ] Vsp dim where
  toFun v := WithLp.toLp 2 fun i => if i.1 = σ then v i else 0
  map_add' v w := by ext i; simp only [PiLp.add_apply]; split_ifs <;> simp
  map_smul' c v := by ext i; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

open Classical in
lemma prj_apply {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) (i : Idx dim) :
    prj σ v i = if i.1 = σ then v i else 0 := rfl

lemma prj_inPart {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) : InPart σ (prj σ v) := by
  intro j hj
  rw [prj_apply, if_neg hj]

lemma Hf_prj_right {dim : (E →+* ℂ) → ℕ} {σ : E →+* ℂ} {v : Vsp dim} (hv : InPart σ v) (x : Vsp dim) :
    Hf v (prj σ x) = Hf v x := by
  unfold Hf
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prj_apply]
  split_ifs with h
  · rfl
  · rw [hv i h, zero_mul, zero_mul]

lemma norm_prj_le {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) : ‖prj σ v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  rw [prj_apply]
  split_ifs
  · exact le_rfl
  · rw [norm_zero, zero_pow two_ne_zero]
    positivity

lemma ne_conj [IsCMField E] (σ : E →+* ℂ) : ComplexEmbedding.conjugate σ ≠ σ := by
  intro h
  have hc := NumberField.IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk σ)
  rw [NumberField.InfinitePlace.isComplex_mk_iff] at hc
  exact hc (ComplexEmbedding.isReal_iff.mpr h)

open Classical in
def Mc {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) : Vsp dim →ₗ[ℂ] Vsp dim where
  toFun v := WithLp.toLp 2 fun i => if i.1 = σ then c * v i else
    if i.1 = ComplexEmbedding.conjugate σ then (starRingEnd ℂ) c * v i else 0
  map_add' v w := by ext i; simp only [PiLp.add_apply]; split_ifs <;> ring
  map_smul' a v := by ext i; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

open Classical in
lemma Mc_apply {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) (v : Vsp dim) (i : Idx dim) :
    Mc σ c v i = if i.1 = σ then c * v i else
      if i.1 = ComplexEmbedding.conjugate σ then (starRingEnd ℂ) c * v i else 0 := rfl

lemma real_inner_Mc {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) (v w : Vsp dim) :
    inner ℝ (Mc σ c v) w = inner ℝ v (Mc σ ((starRingEnd ℂ) c) w) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Mc_apply, Mc_apply]
  split_ifs <;> simp only [Complex.inner, map_mul, Complex.conj_conj, mul_zero, zero_mul,
    map_zero] <;> ring_nf

lemma prj_Mc {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) (v : Vsp dim) :
    prj σ (Mc σ c v) = c • prj σ v := by
  ext i
  rw [prj_apply, PiLp.smul_apply, prj_apply, Mc_apply, smul_eq_mul]
  split_ifs <;> simp

lemma prj_eq_Mc [IsCMField E] {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) :
    prj σ v = (1 / 2 : ℂ) • (Mc σ 1 v - Complex.I • Mc σ Complex.I v) := by
  ext i
  simp only [prj_apply, PiLp.smul_apply, PiLp.sub_apply, Mc_apply, smul_eq_mul, map_one,
    Complex.conj_I]
  split_ifs
  · ring_nf
    rw [Complex.I_sq]
    ring
  · ring_nf
    rw [Complex.I_sq]
    ring
  · ring

lemma isU_add {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)} {x y u v : Vsp dim}
    (hu : IsU I x u) (hv : IsU I y v) : IsU I (x + y) (u + v) :=
    ⟨add_mem hu.1 hv.1, fun a ha => by
      rw [inner_add_left, hu.2 a ha, hv.2 a ha, Hf_add_left, Complex.add_im]⟩

lemma isU_neg {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim}
    (hu : IsU I x u) : IsU I (-x) (-u) :=
    ⟨neg_mem hu.1, fun a ha => by
      have hn : Hf (-x) a = -Hf x a := by simp [Hf, Finset.sum_neg_distrib]
      rw [inner_neg_left, hu.2 a ha, hn, Complex.neg_im]⟩

lemma isU_zero {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) : IsU I 0 0 :=
    ⟨zero_mem _, fun a _ => by rw [inner_zero_left, Hf_zero_left, Complex.zero_im]⟩

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitA
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

section basic

variable {ι : Type} [Fintype ι]

private theorem Hf_eq_inner_swap_complex (v w : EuclideanSpace ℂ ι) : Hf v w = inner ℂ w v := by
  simp [Hf, PiLp.inner_apply, RCLike.inner_apply]

private theorem real_inner_eq_re_inner' (x y : EuclideanSpace ℂ ι) : ⟪x, y⟫_ℝ = (inner ℂ x y).re := by
  first
  | exact real_inner_eq_re_inner ℂ x y
  | simp [PiLp.inner_apply, Complex.inner, Complex.re_sum, RCLike.inner_apply, mul_comm]

theorem Hf_conj (v w : EuclideanSpace ℂ ι) : Hf w v = (starRingEnd ℂ) (Hf v w) := by
  rw [Hf_eq_inner_swap_complex, Hf_eq_inner_swap_complex]
  exact (inner_conj_symm _ _).symm

theorem real_inner_eq_Hf (x y : EuclideanSpace ℂ ι) : ⟪x, y⟫_ℝ = (Hf y x).re := by
  rw [Hf_eq_inner_swap_complex, real_inner_eq_re_inner']

theorem Hf_im_eq (v w : EuclideanSpace ℂ ι) : (Hf v w).im = ⟪Complex.I • w, v⟫_ℝ := by
  rw [real_inner_eq_re_inner', inner_smul_left, Hf_eq_inner_swap_complex]
  simp

theorem Hf_im_eq' (v w : EuclideanSpace ℂ ι) : (Hf v w).im = ⟪-(Complex.I • v), w⟫_ℝ := by
  rw [Hf_conj w v, Complex.conj_im, Hf_im_eq w v, inner_neg_left]

theorem Hf_im_antisymm (v w : EuclideanSpace ℂ ι) : (Hf v w).im = -(Hf w v).im := by
  rw [Hf_conj w v, Complex.conj_im]

theorem Hf_im_add_left (v v' w : EuclideanSpace ℂ ι) :
    (Hf (v + v') w).im = (Hf v w).im + (Hf v' w).im := by
  simp only [Hf_eq_inner_swap_complex, inner_add_right, Complex.add_im]

theorem Hf_im_add_right (v w w' : EuclideanSpace ℂ ι) :
    (Hf v (w + w')).im = (Hf v w).im + (Hf v w').im := by
  simp only [Hf_eq_inner_swap_complex, inner_add_left, Complex.add_im]

theorem Hf_im_smul_left (r : ℝ) (v w : EuclideanSpace ℂ ι) :
    (Hf (r • v) w).im = r * (Hf v w).im := by
  simp [Hf, Complex.im_sum, Finset.mul_sum, mul_assoc]

theorem Hf_im_smul_right (r : ℝ) (v w : EuclideanSpace ℂ ι) :
    (Hf v (r • w)).im = r * (Hf v w).im := by
  simp [Hf, Complex.im_sum, Finset.mul_sum, mul_left_comm]

theorem Hf_im_zero_left (w : EuclideanSpace ℂ ι) : (Hf 0 w).im = 0 := by
  simp [Hf]

theorem Hf_im_zero_right (v : EuclideanSpace ℂ ι) : (Hf v 0).im = 0 := by
  simp [Hf]

theorem abs_Hf_im_le (v w : EuclideanSpace ℂ ι) : |(Hf v w).im| ≤ ‖v‖ * ‖w‖ := by
  rw [Hf_eq_inner_swap_complex, mul_comm]
  exact (Complex.abs_im_le_norm _).trans (norm_inner_le_norm w v)

theorem Hf_im_span_left (S : Set (EuclideanSpace ℂ ι)) (w : EuclideanSpace ℂ ι)
    (h : ∀ v ∈ S, (Hf v w).im = 0) : ∀ v ∈ Submodule.span ℝ S, (Hf v w).im = 0 := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact Hf_im_zero_left w
  | add x y _ _ hx hy => rw [Hf_im_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [Hf_im_smul_left, hx, mul_zero]

theorem Hf_im_span_right (S : Set (EuclideanSpace ℂ ι)) (v : EuclideanSpace ℂ ι)
    (h : ∀ w ∈ S, (Hf v w).im = 0) : ∀ w ∈ Submodule.span ℝ S, (Hf v w).im = 0 := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact Hf_im_zero_right v
  | add x y _ _ hx hy => rw [Hf_im_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [Hf_im_smul_right, hx, mul_zero]

theorem Hf_im_span_iso (S : Set (EuclideanSpace ℂ ι)) (h : ∀ v ∈ S, ∀ w ∈ S, (Hf v w).im = 0) :
    ∀ v ∈ Submodule.span ℝ S, ∀ w ∈ Submodule.span ℝ S, (Hf v w).im = 0 := by
  intro v hv w hw
  exact Hf_im_span_right S v (fun w' hw' => Hf_im_span_left S w' (fun v' hv' => h v' hv' w' hw') v hv) w hw

end basic

variable {E : Type} [Field E] [NumberField E]

section vecU

variable {dim : (E →+* ℂ) → ℕ}

theorem exists_isU (I : Submodule ℤ (Vsp dim)) (x : Vsp dim) : ∃ u, IsU I x u := by
  let K := IR I
  let f : K →ₗ[ℝ] ℝ :=
    { toFun := fun a => (Hf x (a : Vsp dim)).im
      map_add' := fun a b => by simp only [Submodule.coe_add, Hf_im_add_right]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul, Hf_im_smul_right, smul_eq_mul, RingHom.id_apply] }
  let u : K := (InnerProductSpace.toDual ℝ K).symm (LinearMap.toContinuousLinearMap f)
  refine ⟨(u : Vsp dim), u.2, fun a ha => ?_⟩
  have h1 := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := K) (x := ⟨a, ha⟩)
    (y := LinearMap.toContinuousLinearMap f)
  exact h1

theorem IsU.unique {I : Submodule ℤ (Vsp dim)} {x u u' : Vsp dim} (h : IsU I x u)
    (h' : IsU I x u') : u = u' := by
  have hd : u - u' ∈ IR I := Submodule.sub_mem _ h.1 h'.1
  have h0 : inner ℝ (u - u') (u - u') = (0 : ℝ) := by
    rw [inner_sub_left, h.2 _ hd, h'.2 _ hd, sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

theorem IsU.norm_sq {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim} (h : IsU I x u) :
    ‖u‖ ^ 2 = (Hf x u).im := by
  rw [← real_inner_self_eq_norm_sq, h.2 u h.1]

theorem IsU.eq_zero_iff {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim} (h : IsU I x u) :
    u = 0 ↔ ∀ a ∈ I, (Hf x a).im = 0 := by
  constructor
  · rintro rfl a ha
    rw [← h.2 a (Submodule.subset_span ha), inner_zero_left]
  · intro hI
    have hs := Hf_im_span_right (I : Set (Vsp dim)) x (fun w hw => hI w hw) u h.1
    have h0 : inner ℝ u u = (0 : ℝ) := by rw [h.2 u h.1, hs]
    exact inner_self_eq_zero.1 h0

theorem mem_IR {I : Submodule ℤ (Vsp dim)} {x : Vsp dim} (h : x ∈ I) : x ∈ IR I := Submodule.subset_span h

end vecU

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ExtProof
namespace ReciprocityTheory.ChartRestriction.G.I2.Ext

private theorem pow_sub_pow_le_mul_sub_mul_pow {x y M : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hxM : x ≤ M) (hM : 1 ≤ M) :
    ∀ n : ℕ, x ^ n - y ^ n ≤ n * (x - y) * M ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hx : 0 ≤ x := hy.trans hyx
    have hxy : 0 ≤ x - y := sub_nonneg.2 hyx
    have hMn : 0 ≤ M ^ n := pow_nonneg (by linarith) n
    have hyn : y ^ n ≤ M ^ n := by
      first
      | exact pow_le_pow_left hy (hyx.trans hxM) n
      | exact pow_le_pow_left₀ hy (hyx.trans hxM) n
      | (gcongr <;> linarith)
    have hMn1 : M ^ n ≤ M ^ (n + 1) := by
      rw [pow_succ]; nlinarith [mul_nonneg hMn (sub_nonneg.2 hM)]
    have h1 : x * (x ^ n - y ^ n) ≤ x * (n * (x - y) * M ^ n) := mul_le_mul_of_nonneg_left ih hx
    have h2 : x * (n * (x - y) * M ^ n) ≤ M * (n * (x - y) * M ^ n) :=
      mul_le_mul_of_nonneg_right hxM (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hxy) hMn)
    have h3 : (x - y) * y ^ n ≤ (x - y) * M ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (hyn.trans hMn1) hxy
    have e : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by ring
    have e2 : M * (n * (x - y) * M ^ n) = n * (x - y) * M ^ (n + 1) := by ring
    rw [e]
    push_cast
    linarith

private theorem detProductRest : DetProductRest := by
  intro i c ε hε hε1
  have h2 : (0 : ℝ) ≤ 2 ^ c := by positivity
  have hM : (1 : ℝ) ≤ 2 ^ c + 1 := by linarith
  have key := pow_sub_pow_le_mul_sub_mul_pow h2 (by linarith : (2 : ℝ) ^ c ≤ 2 ^ c + ε)
    (by linarith : (2 : ℝ) ^ c + ε ≤ 2 ^ c + 1) hM i
  have e : (2 : ℝ) ^ c + ε - 2 ^ c = ε := by ring
  rw [e] at key
  rw [pow_mul]
  exact key

theorem all : All :=
  ⟨Formalism.LatticeBaseChangeAlt.packingCount, Formalism.LatticeBaseChangeAlt.gaussian_tail_bound, Formalism.LatticeBaseChangeAlt.ballVolume, Formalism.LatticeBaseChangeAlt.gHadamard,
    Formalism.LatticeBaseChangeAlt.nearestPlane, Formalism.LatticeBaseChangeAlt.cauchyBinetMax, Formalism.LatticeBaseChangeAlt.detPerturbation,
    Formalism.LatticeBaseChangeAlt.detPerturbNumeric, detProductRest⟩

end ReciprocityTheory.ChartRestriction.G.I2.Ext
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelA
namespace ReciprocityTheory.ChartRestriction.G.I2

section

open Complex

noncomputable section

theorem cab_dirCauchy {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (F : V → ℂ) (hF : Differentiable ℂ F) (c : ℕ) (x : Fin c → V) (hx : ∀ k, ‖x k‖ ≤ 1)
    (ρ M : ℝ) (hρ : 0 < ρ) (hM : ∀ v, ‖v‖ ≤ c * ρ → ‖F v‖ ≤ M) :
    ‖iteratedFDeriv ℂ c F 0 x‖ ≤ M / ρ ^ c := by
  let T : (Fin c → ℂ) →L[ℂ] V := ∑ k, (ContinuousLinearMap.proj k).smulRight (x k)
  have hT : ∀ z, T z = ∑ k, z k • x k := by
    intro z; simp [T]
  have hG : Differentiable ℂ (F ∘ T) := hF.comp T.differentiable
  have h1 := iter_step_bound (F ∘ T) hG ρ M hρ c id 0 (by
    intro y hy
    simp only [Pi.zero_apply, sub_zero] at hy
    apply hM
    rw [hT]
    calc ‖∑ k, y k • x k‖ ≤ ∑ k, ‖y k • x k‖ := norm_sum_le _ _
      _ ≤ ∑ k, ‖y k‖ := by
          apply Finset.sum_le_sum; intro k _
          rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (hx k)
      _ ≤ c * ρ := hy)
  have hcd : ContDiff ℂ c F := contDiff_of_differentiable_fd hF c
  rw [T.iteratedFDeriv_comp_right hcd 0 le_rfl] at h1
  have hx' : (fun j : Fin c => T (Pi.single j 1)) = x := by
    funext j; rw [hT]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero, hx'] using h1

theorem cab_iter_pow {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ℓ : V →L[ℂ] ℂ) (c : ℕ) (x : Fin c → V) :
    iteratedFDeriv ℂ c (fun v => (ℓ v) ^ c) 0 x = (c.factorial : ℂ) * ∏ k, ℓ (x k) := by
  let f := (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin c) ℂ).compContinuousLinearMap (fun _ => ℓ)
  have hf : (fun v => (ℓ v) ^ c) = fun v => f (fun _ => v) := by
    funext v; simp [f, ContinuousMultilinearMap.mkPiAlgebra_apply, Finset.prod_const]
  rw [hf, ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal]
  simp only [f, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  have : ∀ σ : Equiv.Perm (Fin c), ∏ i, ℓ (x (σ i)) = ∏ k, ℓ (x k) := fun σ =>
    Equiv.prod_comp σ (fun k => ℓ (x k))
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

theorem cab_perm_of_ofFn {ι : Type} [Fintype ι] {n : ℕ} (f g : Fin n → ι)
    (h : List.Perm (List.ofFn f) (List.ofFn g)) : ∃ σ : Equiv.Perm (Fin n), g = f ∘ σ := by
  classical
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have h1 : f ∘ Tuple.sort f = g ∘ Tuple.sort g := by
    apply List.ofFn_injective
    exact (((Tuple.sort f).ofFn_comp_perm f).trans
      (h.trans ((Tuple.sort g).ofFn_comp_perm g).symm)).eq_of_pairwise'
        (Tuple.monotone_sort f).sortedLE_ofFn.pairwise (Tuple.monotone_sort g).sortedLE_ofFn.pairwise
  refine ⟨(Tuple.sort g).symm.trans (Tuple.sort f), ?_⟩
  funext i
  have := congrFun h1 ((Tuple.sort g).symm i)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
  simp [this]

theorem cab_iter_cast {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (F : W → ℂ) (z : W)
    {n n' : ℕ} (h : n = n') (v : Fin n → W) :
    iteratedFDeriv ℂ n F z v = iteratedFDeriv ℂ n' F z (v ∘ Fin.cast h.symm) := by
  subst h; rfl

theorem cab_jet_eq {ι : Type} [Fintype ι] [DecidableEq ι] {c : ℕ} {β P : EuclideanSpace ℂ ι → ℂ}
    (hβ : ContDiff ℂ (⊤ : WithTop ℕ∞) β) (hP : ContDiff ℂ (⊤ : WithTop ℕ∞) P)
    (h : ∀ α : ι →₀ ℕ, α.degree ≤ c →
      polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) β 0 =
        polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) P 0) :
    iteratedFDeriv ℂ c β 0 = iteratedFDeriv ℂ c P 0 := by
  have hbasis : ∀ l : Fin c → ι, iteratedFDeriv ℂ c β 0 (fun k => EuclideanSpace.single (l k) 1) =
      iteratedFDeriv ℂ c P 0 (fun k => EuclideanSpace.single (l k) 1) := by
    intro l
    set m : Multiset ι := (List.ofFn l : Multiset ι) with hm
    set α := Multiset.toFinsupp m with hα
    have hαm : Finsupp.toMultiset α = m := Multiset.toFinsupp_toMultiset m
    have hn : Multiset.card (Finsupp.toMultiset α) = c := by
      rw [hαm, hm, Multiset.coe_card, List.length_ofFn]
    have hdeg : α.degree ≤ c := by
      have : Multiset.card (Finsupp.toMultiset α) = α.degree := by
        simp only [Finsupp.card_toMultiset]
        rfl
      omega
    have h1 := h α hdeg
    unfold polyDeriv at h1
    simp only [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_true, one_mul] at h1
    rw [cab_iter_cast β 0 hn, cab_iter_cast P 0 hn] at h1
    set g : Fin c → ι := fun k => (Finsupp.toMultiset α).toList.get
      ((Fin.cast hn.symm k).cast (Multiset.length_toList _).symm) with hg
    have hperm : List.Perm (List.ofFn l) (List.ofFn g) := by
      have e1 : List.ofFn g = (Finsupp.toMultiset α).toList := by
        apply List.ext_get (by simp [hn])
        intro k h1 h2; simp [hg]
      rw [e1, ← Multiset.coe_eq_coe, Multiset.coe_toList, hαm]
    obtain ⟨σ, hσ⟩ := cab_perm_of_ofFn l g hperm
    have hv : ((fun k => EuclideanSpace.single
        ((Finsupp.toMultiset α).toList.get (k.cast (Multiset.length_toList _).symm)) (1 : ℂ)) ∘
          Fin.cast hn.symm) = (fun k => EuclideanSpace.single (l k) (1 : ℂ)) ∘ σ := by
      funext k
      have := congrFun hσ k
      simp only [Function.comp_apply] at this ⊢
      rw [← this]
    rw [hv, (hβ.contDiffAt).iteratedFDeriv_comp_perm, (hP.contDiffAt).iteratedFDeriv_comp_perm] at h1
    simpa using h1
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ => (EuclideanSpace.basisFun ι ℂ).toBasis)
  intro l
  simpa [EuclideanSpace.basisFun_apply] using hbasis l

end

end

section

noncomputable section

theorem cab_contDiff_top {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {F : W → ℂ} (hF : Differentiable ℂ F) : ContDiff ℂ (⊤ : WithTop ℕ∞) F := by
  let e : W ≃L[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    (Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv
  have h1 : Differentiable ℂ (F ∘ e.symm) := hF.comp e.symm.differentiable
  have h3 : ContDiff ℂ (⊤ : WithTop ℕ∞) (F ∘ e.symm) := contDiff_of_differentiable h1
  have : F = (F ∘ e.symm) ∘ e := by ext x; simp
  rw [this]
  exact h3.comp e.contDiff

theorem cab_restrict {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (Sb : Submodule ℂ V)
    {c : ℕ} {f g : V → ℂ} (hf : ContDiff ℂ c f) (hg : ContDiff ℂ c g) (hfg : ∀ v ∈ Sb, f v = g v)
    (x : Fin c → V) (hx : ∀ k, x k ∈ Sb) :
    iteratedFDeriv ℂ c f 0 x = iteratedFDeriv ℂ c g 0 x := by
  let ι : Sb →L[ℂ] V := Sb.subtypeL
  have hfi : f ∘ ι = g ∘ ι := by funext v; exact hfg v v.2
  have e1 := ι.iteratedFDeriv_comp_right hf (0 : Sb) le_rfl
  have e2 := ι.iteratedFDeriv_comp_right hg (0 : Sb) le_rfl
  rw [hfi, e2] at e1
  have := congrArg (fun M => M (fun k => (⟨x k, hx k⟩ : Sb))) e1
  simpa [ι, ContinuousMultilinearMap.compContinuousLinearMap_apply] using this.symm

theorem iteratedFDeriv_single_column {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {c : ℕ} {g : V → ℂ}
    (hg : ContDiff ℂ c g) (x : Fin c → V) :
    iteratedFDeriv ℂ c (fun w : Fin 1 → V => g (w 0)) 0 (fun k _ => x k) = iteratedFDeriv ℂ c g 0 x := by
  let pr : (Fin 1 → V) →L[ℂ] V := ContinuousLinearMap.proj 0
  have := pr.iteratedFDeriv_comp_right hg (0 : Fin 1 → V) le_rfl
  have h2 := congrArg (fun M => M (fun k _ => x k)) this
  simp only [pr, ContinuousMultilinearMap.compContinuousLinearMap_apply] at h2
  exact h2

end

end

section

noncomputable section

theorem cab_expo_le {q t u c : ℝ} (hq : 0 < q) (hqt : q * t ^ 2 ≤ c) :
    q * Real.pi * t ^ 2 / 2 - q * Real.pi * u ^ 2 + 2 * q * Real.pi * t * u ≤
      5 * Real.pi * c / 2 - Real.pi / 2 * q * u ^ 2 := by
  have h1 : 0 ≤ q * (u - 2 * t) ^ 2 := by positivity
  have hp := Real.pi_pos
  nlinarith [mul_nonneg hp.le h1]

theorem cab_tail_deriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {κ : Type} (R : V → ℂ) (hR : Differentiable ℂ R) (c : ℕ) (x : Fin c → V) (hx : ∀ k, ‖x k‖ ≤ 1)
    (q : ℝ) (hq : 0 < q) (B : ℝ) (hB : 0 ≤ B) (u : κ → ℝ)
    (hsum : Summable (fun a => Real.exp (-(Real.pi / 2 * q * u a ^ 2))))
    (hbd : ∀ v, ‖R v‖ ≤ B * ∑' a, Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2 - q * Real.pi * u a ^ 2 +
      2 * q * Real.pi * ‖v‖ * u a)) :
    ‖iteratedFDeriv ℂ c R 0 x‖ ≤ B * (q * (c + 1)) ^ ((c : ℝ) / 2) *
      Real.exp (5 * Real.pi * c / 2) * ∑' a, Real.exp (-(Real.pi / 2 * q * u a ^ 2)) := by
  have hc1 : (0 : ℝ) < c + 1 := by positivity
  have hqc : 0 < q * (c + 1) := mul_pos hq hc1
  set ρ := 1 / Real.sqrt (q * (c + 1)) with hρ
  have hρ0 : 0 < ρ := by positivity
  set S0 := ∑' a, Real.exp (-(Real.pi / 2 * q * u a ^ 2)) with hS0
  have hS0 : 0 ≤ S0 := tsum_nonneg fun a => (Real.exp_pos _).le
  have hM : ∀ v, ‖v‖ ≤ c * ρ → ‖R v‖ ≤ B * Real.exp (5 * Real.pi * c / 2) * S0 := by
    intro v hv
    have hqt : q * ‖v‖ ^ 2 ≤ c := by
      have h1 : ‖v‖ ^ 2 ≤ (c * ρ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
      have h2 : (c * ρ) ^ 2 = c ^ 2 / (q * (c + 1)) := by
        rw [hρ, mul_pow, div_pow, Real.sq_sqrt hqc.le]; ring
      rw [h2] at h1
      have h3 : q * ‖v‖ ^ 2 ≤ c ^ 2 / (c + 1) := by
        calc q * ‖v‖ ^ 2 ≤ q * (c ^ 2 / (q * (c + 1))) := mul_le_mul_of_nonneg_left h1 hq.le
          _ = c ^ 2 / (c + 1) := by field_simp
      refine h3.trans ?_
      rw [div_le_iff₀ hc1]; nlinarith
    have hterm : ∀ a, Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2 - q * Real.pi * u a ^ 2 +
        2 * q * Real.pi * ‖v‖ * u a) ≤
        Real.exp (5 * Real.pi * c / 2) * Real.exp (-(Real.pi / 2 * q * u a ^ 2)) := by
      intro a
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := cab_expo_le (u := u a) hq hqt
      linarith
    have hs2 : Summable (fun a => Real.exp (5 * Real.pi * c / 2) * Real.exp (-(Real.pi / 2 * q * u a ^ 2))) :=
      hsum.mul_left _
    have hs1 : Summable (fun a => Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2 - q * Real.pi * u a ^ 2 +
        2 * q * Real.pi * ‖v‖ * u a)) :=
      Summable.of_nonneg_of_le (fun a => (Real.exp_pos _).le) hterm hs2
    refine (hbd v).trans (le_of_le_of_eq (mul_le_mul_of_nonneg_left ?_ hB) (mul_assoc _ _ _).symm)
    calc _ ≤ ∑' a, Real.exp (5 * Real.pi * c / 2) * Real.exp (-(Real.pi / 2 * q * u a ^ 2)) :=
          hs1.tsum_le_tsum hterm hs2
      _ = _ := by rw [tsum_mul_left]
  have h := cab_dirCauchy R hR c x hx ρ _ hρ0 hM
  refine h.trans (le_of_eq ?_)
  have hr : 1 / ρ ^ c = (q * (c + 1)) ^ ((c : ℝ) / 2) := by
    rw [hρ, one_div_pow, one_div_one_div, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hqc.le]
    ring_nf
  rw [div_eq_mul_one_div, hr]; ring

end

end

end ReciprocityTheory.ChartRestriction.G.I2
end
