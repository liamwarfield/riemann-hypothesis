module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentOnHyperbolicComplement
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable section

section herm

variable {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

private lemma hermC_sub_left_section (u u' v : Fin r → ℂ) :
    hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma hermC_add_right_section (u v v' : Fin r → ℂ) :
    hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by
  simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

private lemma hermC_smul_right_section (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ G u (c • v) = conj c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma hC_sub_right (u v v' : Fin r → ℂ) :
    hermC τ G u (v - v') = hermC τ G u v - hermC τ G u v' := by
  simp only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

lemma hC_zero_left (v : Fin r → ℂ) : hermC τ G 0 v = 0 := by
  simp [hermC]

def hL (y : Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun v := hermC τ G v y
  map_add' u v := hC_add_left τ G u v y
  map_smul' c v := by
    simp only [smul_eq_mul, RingHom.id_apply]
    exact hC_smul_left τ G c v y

def rz (φ : (Fin r → ℂ) →ₗ[ℂ] ℂ) : Fin r → ℂ :=
  fun b => conj (((G.map τ)⁻¹).mulVec (fun a => φ (fun j => if a = j then 1 else 0)) b)

lemma rz_spec (hG : (G.map τ).det ≠ 0) (φ : (Fin r → ℂ) →ₗ[ℂ] ℂ) (v : Fin r → ℂ) :
    hermC τ G v (rz τ G φ) = φ v := by
  have hM : G.map τ * (G.map τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG)
  have key : ∀ a, ∑ b, τ (G a b) * (((G.map τ)⁻¹).mulVec
      (fun a => φ (fun j => if a = j then 1 else 0))) b = φ (fun j => if a = j then 1 else 0) := by
    intro a
    have h2 := congrFun (Matrix.mulVec_mulVec (fun a => φ (fun j => if a = j then 1 else 0))
      (G.map τ) (G.map τ)⁻¹) a
    rw [hM, Matrix.one_mulVec] at h2
    simpa [Matrix.mulVec, dotProduct] using h2
  have hv : v = ∑ a, v a • (fun j => if a = j then (1 : ℂ) else 0) := by
    funext j
    simp [Finset.sum_apply]
  calc hermC τ G v (rz τ G φ)
      = ∑ a, v a * ∑ b, τ (G a b) * (((G.map τ)⁻¹).mulVec
          (fun a => φ (fun j => if a = j then 1 else 0))) b := by
        simp only [hermC, rz, Complex.conj_conj, Finset.mul_sum, mul_assoc]
    _ = ∑ a, v a * φ (fun j => if a = j then 1 else 0) := by simp only [key]
    _ = φ v := by
        conv_rhs => rw [hv]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, smul_eq_mul]

lemma map_det_ne (hG : G.det ≠ 0) : (G.map τ).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero τ).mpr hG

end herm

namespace Data

variable {r : ℕ} (X : Data E r)

lemma positive_part_add (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.ppos x τ (u + v) = X.ppos x τ u + X.ppos x τ v := by
  simp only [ppos, hC_add_left, add_mul, Finset.sum_add_distrib, add_smul]

private lemma hermC_Gm_eq_conj_swap (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm u w = conj (hermC τ.1 X.Gm w u) := by
  have hG : ∀ a b, τ.1 (X.Gm a b) = conj (τ.1 (X.Gm b a)) := fun a b => by
    rw [← X.Gm_herm b a, cc]
    first
      | exact NumberField.IsCMField.complexEmbedding_complexConj E _ _
      | exact (NumberField.IsCMField.complexEmbedding_complexConj E _ _).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hG a b]
  ring

private lemma hermC_finset_sum_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*}
    (s : Finset ι) (f : ι → Fin r → ℂ) (w : Fin r → ℂ) :
    hermC τ G (∑ i ∈ s, f i) w = ∑ i ∈ s, hermC τ G (f i) w := by
  induction s using Finset.cons_induction with
  | empty => simp [hC_zero_left]
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, hC_add_left, ih]

private lemma hermC_finset_sum_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*}
    (s : Finset ι) (f : ι → Fin r → ℂ) (u : Fin r → ℂ) :
    hermC τ G u (∑ i ∈ s, f i) = ∑ i ∈ s, hermC τ G u (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [hermC]
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, hermC_add_right_section, ih]

private lemma sum_mul_mul_eq_of_mul_eq_one {n : ℕ} (k : Fin n → ℂ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : A * B = 1) (a : Fin n) : ∑ b, (∑ a', k a' * A a' b) * B b a = k a := by
  calc ∑ b, (∑ a', k a' * A a' b) * B b a = Matrix.vecMul (Matrix.vecMul k A) B a := rfl
    _ = Matrix.vecMul k (A * B) a := by rw [Matrix.vecMul_vecMul]
    _ = k a := by rw [h, Matrix.vecMul_one]

lemma ppos_idem {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.ppos x τ (X.ppos x τ v) = X.ppos x τ v := by
  have hdet : (X.gramPos x τ).det ≠ 0 := by
    have h := (hx τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
    intro h0
    have h1 : dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = 0 := h0
    rw [h1] at h
    simp at h
  have hinv : X.gramPos x τ * (X.gramPos x τ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hP : ∀ b, hermC τ.1 X.Gm (X.ppos x τ v) (col (mat x τ) (Fin.castLE X.p0_le b)) =
      ∑ a', (∑ b', hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b')) * (X.gramPos x τ)⁻¹ b' a') *
        X.gramPos x τ a' b := by
    intro b
    simp only [ppos, hermC_finset_sum_left, hC_smul_left]
    rfl
  show ∑ a : Fin X.p0, (∑ b : Fin X.p0, hermC τ.1 X.Gm (X.ppos x τ v) (col (mat x τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos x τ)⁻¹ b a) • col (mat x τ) (Fin.castLE X.p0_le a) = X.ppos x τ v
  simp only [hP]
  simp only [sum_mul_mul_eq_of_mul_eq_one (fun a' => ∑ b', hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b')) * (X.gramPos x τ)⁻¹ b' a')
    _ _ hinv]
  rfl

def Jp (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) : Fin r → ℂ := (2 : ℂ) • X.ppos x τ v - v

lemma Jp_add (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.Jp x τ (u + v) = X.Jp x τ u + X.Jp x τ v := by
  funext i
  simp only [Jp, positive_part_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma ppos_smul' (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.ppos x τ (c • v) = c • X.ppos x τ v := by
  simp only [ppos, hC_smul_left, Finset.smul_sum, smul_smul, mul_assoc, Finset.mul_sum]

private lemma ppos_sub' (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.ppos x τ (u - v) = X.ppos x τ u - X.ppos x τ v := by
  have h := X.positive_part_add x τ u ((-1 : ℂ) • v)
  rw [ppos_smul'] at h
  simpa [sub_eq_add_neg, neg_one_smul] using h

lemma Jp_smul (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.Jp x τ (c • v) = c • X.Jp x τ v := by
  funext i
  simp only [Jp, ppos_smul', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma Jp_Jp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.Jp x τ (X.Jp x τ v) = v := by
  simp only [Jp]
  rw [ppos_sub', ppos_smul', X.ppos_idem hx]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma hermC_ppos_left_eq_ppos_right_frame (x : Frame X.Ψ r) (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) w = hermC τ.1 X.Gm u (X.ppos x τ w) := by
  have hH : (X.gramPos x τ).IsHermitian := by
    ext a b
    simp only [Matrix.conjTranspose_apply, gramPos, gram, Matrix.submatrix_apply, Matrix.of_apply]
    exact (X.hermC_Gm_eq_conj_swap τ (col (mat x τ) (Fin.castLE X.p0_le a)) (col (mat x τ) (Fin.castLE X.p0_le b))).symm
  have hGi : ∀ a b, conj ((X.gramPos x τ)⁻¹ b a) = (X.gramPos x τ)⁻¹ a b :=
    fun a b => hH.inv.apply a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ppos, hermC_finset_sum_left, hermC_finset_sum_right, hC_smul_left, hermC_smul_right_section, map_sum,
    map_mul]
  simp only [← X.hermC_Gm_eq_conj_swap, hGi, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma Jp_adj {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.Jp x τ u) w = hermC τ.1 X.Gm u (X.Jp x τ w) := by
  simp only [Jp, hermC_sub_left_section, hC_sub_right, hC_smul_left, hermC_smul_right_section, X.hermC_ppos_left_eq_ppos_right_frame,
    map_ofNat]

section perTau

variable (x : Frame X.Ψ r) (τ : X.Ψ) (e : Fin r → ℂ) (δ : (Fin r → ℂ) →ₗ[ℂ] ℂ)

def d2q : ℂ := X.Hf x τ e e

def d2b : (Fin r → ℂ) →ₗ[ℂ] ℂ := (X.d2q x τ e)⁻¹ • hL τ.1 X.Gm e

def d2a : (Fin r → ℂ) →ₗ[ℂ] ℂ := (X.d2q x τ e)⁻¹ • hL τ.1 X.Gm (X.Jp x τ e)

def d2pi : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
  LinearMap.id - (X.d2a x τ e).smulRight e - (X.d2b x τ e).smulRight (X.Jp x τ e)

def d2z : Fin r → ℂ := rz τ.1 X.Gm ((X.d2q x τ e) • (δ ∘ₗ X.d2pi x τ e))

def d2nL : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
  LinearMap.id + (δ ∘ₗ X.d2pi x τ e - (δ (X.d2z x τ e δ) / 2) • X.d2b x τ e).smulRight e -
    (X.d2b x τ e).smulRight (X.d2z x τ e δ)

def d2n : Matrix (Fin r) (Fin r) ℂ := LinearMap.toMatrix' (X.d2nL x τ e δ)

lemma hyperbolic_coeff_b_apply (v : Fin r → ℂ) :
    X.d2b x τ e v = (X.d2q x τ e)⁻¹ * hermC τ.1 X.Gm v e := rfl

lemma hyperbolic_coeff_a_apply (v : Fin r → ℂ) :
    X.d2a x τ e v = (X.d2q x τ e)⁻¹ * hermC τ.1 X.Gm v (X.Jp x τ e) := rfl

lemma hyperbolic_projection_apply (v : Fin r → ℂ) :
    X.d2pi x τ e v = v - X.d2a x τ e v • e - X.d2b x τ e v • X.Jp x τ e := rfl

lemma unipotent_mulVec_formula (v : Fin r → ℂ) :
    Matrix.mulVec (X.d2n x τ e δ) v = v + (δ (X.d2pi x τ e v) -
      δ (X.d2z x τ e δ) / 2 * X.d2b x τ e v) • e - X.d2b x τ e v • X.d2z x τ e δ := by
  simp only [d2n, LinearMap.toMatrix'_mulVec]
  rfl

variable {x τ e}

lemma hsym (u w : Fin r → ℂ) : hermC τ.1 X.Gm u w = conj (hermC τ.1 X.Gm w u) := by
  have hG : ∀ a b, τ.1 (X.Gm a b) = conj (τ.1 (X.Gm b a)) := fun a b => by
    rw [← X.Gm_herm b a, cc]
    first
      | exact NumberField.IsCMField.complexEmbedding_complexConj E _ _
      | exact (NumberField.IsCMField.complexEmbedding_complexConj E _ _).symm
      | exact NumberField.IsCMField.complexEmbedding_complexConj E _
      | exact (NumberField.IsCMField.complexEmbedding_complexConj E _).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hG a b]
  ring

lemma hermitian_pairing_Je_e : hermC τ.1 X.Gm (X.Jp x τ e) e = X.d2q x τ e := rfl

lemma hermitian_pairing_e_Je (hx : x ∈ X.dom) : hermC τ.1 X.Gm e (X.Jp x τ e) = X.d2q x τ e := (X.Jp_adj hx τ e e).symm.trans X.hermitian_pairing_Je_e

lemma hermitian_pairing_Je_Je_zero (hx : x ∈ X.dom) (he : hermC τ.1 X.Gm e e = 0) :
    hermC τ.1 X.Gm (X.Jp x τ e) (X.Jp x τ e) = 0 := by
  rw [X.Jp_adj hx τ e (X.Jp x τ e), X.Jp_Jp hx τ e, he]

variable (hx : x ∈ X.dom) (he : hermC τ.1 X.Gm e e = 0) (hq : X.d2q x τ e ≠ 0)
include hx he hq

lemma hyperbolic_projection_e : X.d2pi x τ e e = 0 := by
  rw [hyperbolic_projection_apply, hyperbolic_coeff_a_apply, hyperbolic_coeff_b_apply, X.hermitian_pairing_e_Je hx, he, inv_mul_cancel₀ hq]
  simp

lemma hyperbolic_projection_Je : X.d2pi x τ e (X.Jp x τ e) = 0 := by
  rw [hyperbolic_projection_apply, hyperbolic_coeff_a_apply, hyperbolic_coeff_b_apply, X.hermitian_pairing_Je_Je_zero hx he, X.hermitian_pairing_Je_e, inv_mul_cancel₀ hq]
  simp

lemma hyperbolic_projection_of_perp {u : Fin r → ℂ} (hu1 : hermC τ.1 X.Gm u e = 0)
    (hu2 : hermC τ.1 X.Gm u (X.Jp x τ e) = 0) : X.d2pi x τ e u = u := by
  rw [hyperbolic_projection_apply, hyperbolic_coeff_a_apply, hyperbolic_coeff_b_apply, hu1, hu2]
  simp

lemma hyperbolic_projection_perp_e (v : Fin r → ℂ) : hermC τ.1 X.Gm (X.d2pi x τ e v) e = 0 := by
  rw [hyperbolic_projection_apply, hermC_sub_left_section, hermC_sub_left_section, hC_smul_left, hC_smul_left, he, X.hermitian_pairing_Je_e,
    hyperbolic_coeff_b_apply, mul_zero, sub_zero, inv_mul_eq_div, div_mul_cancel₀ _ hq, sub_self]

lemma hyperbolic_projection_perp_Je (v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.d2pi x τ e v) (X.Jp x τ e) = 0 := by
  rw [hyperbolic_projection_apply, hermC_sub_left_section, hermC_sub_left_section, hC_smul_left, hC_smul_left, X.hermitian_pairing_e_Je hx,
    X.hermitian_pairing_Je_Je_zero hx he, hyperbolic_coeff_a_apply, mul_zero, sub_zero, inv_mul_eq_div, div_mul_cancel₀ _ hq, sub_self]

lemma unipotent_shift_spec (v : Fin r → ℂ) :
    hermC τ.1 X.Gm v (X.d2z x τ e δ) = X.d2q x τ e * δ (X.d2pi x τ e v) := by
  simp only [d2z]
  rw [rz_spec _ _ (map_det_ne _ _ X.Gm_det)]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]

lemma unipotent_shift_orthogonal_e : hermC τ.1 X.Gm (X.d2z x τ e δ) e = 0 := by
  rw [X.hsym, X.unipotent_shift_spec δ hx he hq, X.hyperbolic_projection_e hx he hq]
  simp

lemma unipotent_shift_orthogonal_Je : hermC τ.1 X.Gm (X.d2z x τ e δ) (X.Jp x τ e) = 0 := by
  rw [X.hsym, X.unipotent_shift_spec δ hx he hq, X.hyperbolic_projection_Je hx he hq]
  simp

lemma d2pi_d2z_eq_d2z : X.d2pi x τ e (X.d2z x τ e δ) = X.d2z x τ e δ := X.hyperbolic_projection_of_perp hx he hq (X.unipotent_shift_orthogonal_e δ hx he hq) (X.unipotent_shift_orthogonal_Je δ hx he hq)

lemma unipotent_shift_self_pairing : hermC τ.1 X.Gm (X.d2z x τ e δ) (X.d2z x τ e δ) =
    X.d2q x τ e * δ (X.d2z x τ e δ) := by
  rw [X.unipotent_shift_spec δ hx he hq, X.d2pi_d2z_eq_d2z δ hx he hq]

lemma unipotent_fixes_e : Matrix.mulVec (X.d2n x τ e δ) e = e := by
  rw [unipotent_mulVec_formula, X.hyperbolic_projection_e hx he hq, hyperbolic_coeff_b_apply, he]
  simp

lemma unipotent_on_orthogonal_e {u : Fin r → ℂ} (hu1 : hermC τ.1 X.Gm u e = 0) :
    Matrix.mulVec (X.d2n x τ e δ) u = u + δ (X.d2pi x τ e u) • e := by
  rw [unipotent_mulVec_formula, hyperbolic_coeff_b_apply, hu1]
  simp

lemma unipotent_on_hyperbolic_complement {u : Fin r → ℂ} (hu1 : hermC τ.1 X.Gm u e = 0)
    (hu2 : hermC τ.1 X.Gm u (X.Jp x τ e) = 0) :
    Matrix.mulVec (X.d2n x τ e δ) u = u + δ u • e := by
  rw [X.unipotent_on_orthogonal_e δ hx he hq hu1, X.hyperbolic_projection_of_perp hx he hq hu1 hu2]

lemma unipotent_transform_unitary (hqr : conj (X.d2q x τ e) = X.d2q x τ e) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (X.d2n x τ e δ) u) (Matrix.mulVec (X.d2n x τ e δ) w) =
      hermC τ.1 X.Gm u w := by
  have hb : ∀ v, hermC τ.1 X.Gm v e = X.d2q x τ e * X.d2b x τ e v := by
    intro v
    rw [hyperbolic_coeff_b_apply, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
  have hz : ∀ v, hermC τ.1 X.Gm v (X.d2z x τ e δ) = X.d2q x τ e * δ (X.d2pi x τ e v) :=
    X.unipotent_shift_spec δ hx he hq
  have hze : hermC τ.1 X.Gm (X.d2z x τ e δ) e = 0 := X.unipotent_shift_orthogonal_e δ hx he hq
  have hez : hermC τ.1 X.Gm e (X.d2z x τ e δ) = 0 := by
    rw [X.hsym, hze, map_zero]
  have hew : ∀ v, hermC τ.1 X.Gm e v = X.d2q x τ e * conj (X.d2b x τ e v) := by
    intro v
    rw [X.hsym, hb, map_mul, hqr]
  have hzw : ∀ v, hermC τ.1 X.Gm (X.d2z x τ e δ) v =
      X.d2q x τ e * conj (δ (X.d2pi x τ e v)) := by
    intro v
    rw [X.hsym, hz, map_mul, hqr]
  have hzz := X.unipotent_shift_self_pairing δ hx he hq
  have hδ : conj (δ (X.d2z x τ e δ)) = δ (X.d2z x τ e δ) := by
    have h1 := X.hsym (τ := τ) (X.d2z x τ e δ) (X.d2z x τ e δ)
    rw [hzz, map_mul, hqr] at h1
    exact (mul_left_cancel₀ hq h1).symm
  rw [unipotent_mulVec_formula, unipotent_mulVec_formula]
  simp only [hC_add_left, hermC_sub_left_section, hC_smul_left, hermC_add_right_section, hC_sub_right,
    hermC_smul_right_section]
  simp only [he, hze, hez, hzz]
  simp only [hb, hz, hew, hzw]
  simp only [map_sub, map_mul, map_div₀, hδ, map_ofNat]
  ring

end perTau

end Data

end

end ReciprocityTheory.ChartRestriction.G.FD
end

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma normSq_sub_le_two (a b : ℂ) :
    Complex.normSq (a - b) ≤ 2 * Complex.normSq a + 2 * Complex.normSq b := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith [sq_nonneg (a.re + b.re), sq_nonneg (a.im + b.im)]

namespace Data

variable {r : ℕ} (X : Data E r)

lemma Jp_sub (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.Jp x τ (u - v) = X.Jp x τ u - X.Jp x τ v := by
  unfold Jp
  rw [X.ppos_sub, smul_sub]
  abel

section perTau

variable {x : Frame X.Ψ r} {τ : X.Ψ}

lemma maj_smul (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ)) (c : ℂ) (v : Fin r → ℂ) :
    X.maj x τ (c • v) = Complex.normSq c * X.maj x τ v := by
  have hJ : X.Jp x τ (c • v) = c • X.Jp x τ v := by
    unfold Jp; rw [X.ppos_smul, smul_comm (2 : ℂ) c, ← smul_sub]
  have hH : ∀ u w, hermC τ.1 X.Gm (c • u) (c • w) = (Complex.normSq c : ℂ) * hermC τ.1 X.Gm u w := by
    intro u w
    unfold hermC
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  have h1 := hself (c • v)
  rw [show X.Hf x τ (c • v) (c • v) = hermC τ.1 X.Gm (X.Jp x τ (c • v)) (c • v) from rfl, hJ, hH,
    show hermC τ.1 X.Gm (X.Jp x τ v) v = X.Hf x τ v v from rfl, hself v] at h1
  exact_mod_cast h1.symm

lemma maj_zero' (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ)) : X.maj x τ 0 = 0 := by
  have h1 := X.maj_smul hself (0 : ℂ) 0
  simpa using h1

lemma maj_nonneg' (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ))
    (hpos : ∀ v, v ≠ 0 → 0 < X.maj x τ v) (v : Fin r → ℂ) : 0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · rw [hv, X.maj_zero' hself]
  · exact (hpos v hv).le

variable {e : Fin r → ℂ} (δ : (Fin r → ℂ) →ₗ[ℂ] ℂ) (hx : x ∈ X.dom) (he : hermC τ.1 X.Gm e e = 0)
  (hq : X.d2q x τ e ≠ 0) (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ))
include hx he hq hself

lemma maj_Ce_bz (C b : ℂ) :
    X.maj x τ (C • e - b • X.d2z x τ e δ) =
      Complex.normSq C * X.maj x τ e + Complex.normSq b * X.maj x τ (X.d2z x τ e δ) := by
  have hfz : hermC τ.1 X.Gm (X.Jp x τ e) (X.d2z x τ e δ) = 0 := by
    rw [hsym, unipotent_shift_orthogonal_Je X δ hx he hq, map_zero]
  have hze : hermC τ.1 X.Gm (X.Jp x τ (X.d2z x τ e δ)) e = 0 := by
    rw [Jp_adj X hx, unipotent_shift_orthogonal_Je X δ hx he hq]
  have h3 : X.Hf x τ (C • e - b • X.d2z x τ e δ) (C • e - b • X.d2z x τ e δ) =
      C * conj C * X.Hf x τ e e + b * conj b * X.Hf x τ (X.d2z x τ e δ) (X.d2z x τ e δ) := by
    show hermC τ.1 X.Gm (X.Jp x τ (C • e - b • X.d2z x τ e δ)) (C • e - b • X.d2z x τ e δ) =
      C * conj C * hermC τ.1 X.Gm (X.Jp x τ e) e +
        b * conj b * hermC τ.1 X.Gm (X.Jp x τ (X.d2z x τ e δ)) (X.d2z x τ e δ)
    rw [Jp_sub, Jp_smul, Jp_smul]
    simp only [hC_sub_left, hC_smul_left, hC_sub_right, hC_smul_right, hfz, hze]
    ring
  rw [hself, hself, hself, Complex.mul_conj, Complex.mul_conj] at h3
  exact_mod_cast h3

lemma maj_decomp (w : Fin r → ℂ) (hw1 : hermC τ.1 X.Gm w e = 0)
    (hw2 : hermC τ.1 X.Gm w (X.Jp x τ e) = 0) (a b : ℂ) :
    X.maj x τ (w + a • e + b • X.Jp x τ e) =
      Complex.normSq a * X.maj x τ e + Complex.normSq b * X.maj x τ e + X.maj x τ w := by
  have k1 : hermC τ.1 X.Gm (X.Jp x τ w) e = 0 := by rw [Jp_adj X hx, hw2]
  have k2 : hermC τ.1 X.Gm (X.Jp x τ w) (X.Jp x τ e) = 0 := by
    rw [Jp_adj X hx, Jp_Jp X hx, hw1]
  have k3 : hermC τ.1 X.Gm (X.Jp x τ e) w = 0 := by rw [hsym, hw2, map_zero]
  have k4 : hermC τ.1 X.Gm e w = 0 := by rw [hsym, hw1, map_zero]
  have k5 := hermitian_pairing_Je_Je_zero X hx he
  have k6 : hermC τ.1 X.Gm (X.Jp x τ e) e = X.Hf x τ e e := rfl
  have k7 : hermC τ.1 X.Gm e (X.Jp x τ e) = X.Hf x τ e e := hermitian_pairing_e_Je X hx
  have h3 : X.Hf x τ (w + a • e + b • X.Jp x τ e) (w + a • e + b • X.Jp x τ e) =
      a * conj a * X.Hf x τ e e + b * conj b * X.Hf x τ e e + X.Hf x τ w w := by
    show hermC τ.1 X.Gm (X.Jp x τ (w + a • e + b • X.Jp x τ e)) (w + a • e + b • X.Jp x τ e) =
      a * conj a * X.Hf x τ e e + b * conj b * X.Hf x τ e e + hermC τ.1 X.Gm (X.Jp x τ w) w
    rw [Jp_add, Jp_add, Jp_smul, Jp_smul, Jp_Jp X hx]
    simp only [hC_add_left, hC_smul_left, hC_add_right, hC_smul_right, k1, k2, k3, k4, k5, k6, k7,
      he]
    ring
  rw [hself, hself, hself, Complex.mul_conj, Complex.mul_conj] at h3
  exact_mod_cast h3

lemma unipotent_sub_one_majorant_bound (hpos : ∀ v, v ≠ 0 → 0 < X.maj x τ v) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hδ : ∀ u, hermC τ.1 X.Gm u e = 0 → hermC τ.1 X.Gm u (X.Jp x τ e) = 0 →
      X.maj x τ (δ u • e) ≤ κ ^ 2 * X.maj x τ u) (v : Fin r → ℂ) :
    X.maj x τ (Matrix.mulVec (X.d2n x τ e δ - 1) v) ≤ (3 * κ) ^ 2 * X.maj x τ v := by
  have hnn := maj_nonneg' X hself hpos
  have hqQ : X.d2q x τ e = (X.maj x τ e : ℂ) := hself e
  have hQ : 0 < X.maj x τ e := by
    rcases (hnn e).lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [hqQ, ← h]; simp) hq
  set Q := X.maj x τ e with hQdef
  set z := X.d2z x τ e δ with hzdef

  have hA : Matrix.mulVec (X.d2n x τ e δ - 1) v =
      (δ (X.d2pi x τ e v) - δ z / 2 * X.d2b x τ e v) • e - X.d2b x τ e v • z := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, unipotent_mulVec_formula]
    abel
  rw [hA, maj_Ce_bz X δ hx he hq hself]

  have hv : v = X.d2pi x τ e v + X.d2a x τ e v • e + X.d2b x τ e v • X.Jp x τ e := by
    rw [hyperbolic_projection_apply]; abel
  have hw1 := hyperbolic_projection_perp_e X hx he hq v
  have hw2 := hyperbolic_projection_perp_Je X hx he hq v
  conv_rhs => rw [hv, maj_decomp X hx he hq hself _ hw1 hw2]

  have hz1 : hermC τ.1 X.Gm (X.Jp x τ z) e = 0 := by rw [Jp_adj X hx, unipotent_shift_orthogonal_Je X δ hx he hq]
  have hz2 : hermC τ.1 X.Gm (X.Jp x τ z) (X.Jp x τ e) = 0 := by
    rw [Jp_adj X hx, Jp_Jp X hx, unipotent_shift_orthogonal_e X δ hx he hq]
  have hmJz : X.maj x τ (X.Jp x τ z) = X.maj x τ z := by
    have h1 := hself (X.Jp x τ z)
    have h2 := hself z
    have h3 : X.Hf x τ (X.Jp x τ z) (X.Jp x τ z) = X.Hf x τ z z := by
      show hermC τ.1 X.Gm (X.Jp x τ (X.Jp x τ z)) (X.Jp x τ z) = X.Hf x τ z z
      rw [Jp_Jp X hx, Hf_eq X x hx]
      rfl
    rw [h1, h2] at h3
    exact_mod_cast h3
  have hZc : (X.maj x τ z : ℂ) = (Q : ℂ) * δ (X.Jp x τ z) := by
    rw [← hself z, ← hqQ]
    show hermC τ.1 X.Gm (X.Jp x τ z) z = _
    rw [unipotent_shift_spec X δ hx he hq, hyperbolic_projection_of_perp X hx he hq hz1 hz2]
  have hdJ : δ (X.Jp x τ z) = ((X.maj x τ z / Q : ℝ) : ℂ) := by
    have hQc : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
    push_cast
    rw [hZc]
    field_simp
  have hZ0 := hnn z
  have hZ : X.maj x τ z ≤ κ ^ 2 * Q := by
    have h := hδ _ hz1 hz2
    rw [maj_smul X hself, hdJ, Complex.normSq_ofReal, hmJz] at h

    have h' : X.maj x τ z * X.maj x τ z ≤ κ ^ 2 * Q * X.maj x τ z := by
      have e1 : X.maj x τ z / Q * (X.maj x τ z / Q) * Q = X.maj x τ z * X.maj x τ z / Q := by
        field_simp
      rw [e1, div_le_iff₀ hQ] at h
      nlinarith
    rcases hZ0.lt_or_eq with h0 | h0
    · exact le_of_mul_le_mul_right h' h0
    · rw [← h0]; positivity
  have hDz : Complex.normSq (δ z) ≤ κ ^ 4 := by
    have h := hδ z (unipotent_shift_orthogonal_e X δ hx he hq) (unipotent_shift_orthogonal_Je X δ hx he hq)
    rw [maj_smul X hself] at h
    have h2 : Complex.normSq (δ z) * Q ≤ κ ^ 4 * Q := by nlinarith
    exact le_of_mul_le_mul_right h2 hQ
  have hw := hyperbolic_projection_perp_e X hx he hq v
  have hD := hδ (X.d2pi x τ e v) hw1 hw2
  rw [maj_smul X hself] at hD
  have hC : Complex.normSq (δ (X.d2pi x τ e v) - δ z / 2 * X.d2b x τ e v) ≤
      2 * Complex.normSq (δ (X.d2pi x τ e v)) +
        Complex.normSq (δ z) * Complex.normSq (X.d2b x τ e v) / 2 := by
    have h1 := normSq_sub_le_two (δ (X.d2pi x τ e v)) (δ z / 2 * X.d2b x τ e v)
    have h2 : Complex.normSq (δ z / 2 * X.d2b x τ e v) =
        Complex.normSq (δ z) * Complex.normSq (X.d2b x τ e v) / 4 := by
      rw [Complex.normSq_mul, Complex.normSq_div]
      norm_num
      ring
    linarith
  have hWn := hnn (X.d2pi x τ e v)
  have hAn := Complex.normSq_nonneg (X.d2a x τ e v)
  have hBn := Complex.normSq_nonneg (X.d2b x τ e v)
  have hDn := Complex.normSq_nonneg (δ (X.d2pi x τ e v))
  have hDzn := Complex.normSq_nonneg (δ z)
  have hk4 : κ ^ 4 ≤ κ ^ 2 := pow_le_pow_of_le_one hκ0 hκ1 (by norm_num)
  have t1 := mul_le_mul_of_nonneg_right hC hQ.le
  have t2 := mul_le_mul_of_nonneg_left hZ hBn
  have t3 := mul_le_mul_of_nonneg_right hDz (mul_nonneg hBn hQ.le)
  have t4 := mul_le_mul_of_nonneg_right hk4 (mul_nonneg hBn hQ.le)
  have t5 := mul_nonneg (sq_nonneg κ) (mul_nonneg hAn hQ.le)
  have t6 := mul_nonneg (sq_nonneg κ) hWn
  have t7 := mul_nonneg (sq_nonneg κ) (mul_nonneg hBn hQ.le)
  nlinarith

end perTau

end Data

end ReciprocityTheory.ChartRestriction.G.FD
