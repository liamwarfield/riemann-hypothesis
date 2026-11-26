module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.GramFlowTransform
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PositiveMinorUnits
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.GramDeterminantReal
namespace ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open Complex Matrix
open scoped ComplexConjugate
noncomputable section

variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

def hL (v : Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun u := hermC τ G u v
  map_add' u u' := by simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a u := by
    simp only [hermC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem hC_add_left (u u' v : Fin r → ℂ) :
    hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := (hL τ G v).map_add u u'

theorem hC_sub_left (u u' v : Fin r → ℂ) :
    hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := (hL τ G v).map_sub u u'

theorem hermC_smul_left (a : ℂ) (u v : Fin r → ℂ) : hermC τ G (a • u) v = a * hermC τ G u v := (hL τ G v).map_smul a u

theorem hC_sum_left {n : ℕ} (f : Fin n → Fin r → ℂ) (w : Fin n → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ b, w b • f b) v = ∑ b, w b * hermC τ G (f b) v := by
  change (hL τ G v) (∑ b, w b • f b) = ∑ b, w b * (hL τ G v) (f b)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, smul_eq_mul]

def gramF {n : ℕ} (f : Fin n → Fin r → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => hermC τ G (f a) (f b)

section Proj
variable {n : ℕ} (f : Fin n → Fin r → ℂ) (e : Fin r → ℂ)

def cv : Fin n → ℂ := fun a => hermC τ G e (f a)

def yv : Fin n → ℂ := Matrix.vecMul (cv τ G f e) (gramF τ G f)⁻¹

def pv : Fin r → ℂ := ∑ b, yv τ G f e b • f b

def mt : ℂ := ∑ a, ∑ b, cv τ G f e a * (gramF τ G f)⁻¹ a b * conj (cv τ G f e b)

theorem pv_orth (hA : IsUnit (gramF τ G f).det) (d : Fin n) :
    hermC τ G (pv τ G f e) (f d) = cv τ G f e d := by
  have h1 : Matrix.vecMul (yv τ G f e) (gramF τ G f) = cv τ G f e := by
    unfold yv
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]
  unfold pv
  rw [hC_sum_left, ← h1]
  simp only [Matrix.vecMul, dotProduct, gramF, Matrix.of_apply]

end Proj

section StepDef
variable {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ)

def dv : Fin r → ℂ := pv τ G f e - pv τ G (fun a : Fin n => f a.castSucc) e

theorem dv_orth (hA : IsUnit (gramF τ G f).det)
    (hA' : IsUnit (gramF τ G (fun a : Fin n => f a.castSucc)).det) (d : Fin n) :
    hermC τ G (dv τ G f e) (f d.castSucc) = 0 := by
  unfold dv
  rw [hC_sub_left, pv_orth τ G f e hA d.castSucc, pv_orth τ G _ e hA' d]
  exact sub_self _

theorem comb_orth_zero {n : ℕ} (f : Fin n → Fin r → ℂ) (hA : IsUnit (gramF τ G f).det)
    (w : Fin n → ℂ) (h : ∀ d, hermC τ G (∑ b, w b • f b) (f d) = 0) : ∑ b, w b • f b = 0 := by
  have hv : Matrix.vecMul w (gramF τ G f) = 0 := by
    funext d
    have hd := h d
    rw [hC_sum_left] at hd
    simpa [Matrix.vecMul, dotProduct, gramF] using hd
  have hw : w = 0 := by
    have h2 := congrArg (fun x => Matrix.vecMul x (gramF τ G f)⁻¹) hv
    simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hA] using h2
  simp [hw]

theorem dv_eq {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ) :
    dv τ G f e = ∑ b, (yv τ G f e b -
      Fin.snoc (α := fun _ => ℂ) (yv τ G (fun a : Fin n => f a.castSucc) e) 0 b) • f b := by
  unfold dv pv
  simp only [sub_smul, Finset.sum_sub_distrib]
  congr 1
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem dv_zero {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ) (hA : IsUnit (gramF τ G f).det)
    (hA' : IsUnit (gramF τ G (fun a : Fin n => f a.castSucc)).det)
    (hy : yv τ G f e (Fin.last n) = 0) : dv τ G f e = 0 := by
  have h : dv τ G f e = ∑ a : Fin n,
      (yv τ G f e a.castSucc - yv τ G (fun a : Fin n => f a.castSucc) e a) • f a.castSucc := by
    rw [dv_eq, Fin.sum_univ_castSucc]
    simp [Fin.snoc_castSucc, Fin.snoc_last, hy]
  rw [h]
  refine comb_orth_zero τ G (fun a : Fin n => f a.castSucc) hA'
    (fun a => yv τ G f e a.castSucc - yv τ G (fun a : Fin n => f a.castSucc) e a) ?_
  intro d
  have hd := dv_orth τ G f e hA hA' d
  rw [h] at hd
  exact hd

end StepDef

variable {τ G} (hG : ∀ a b, τ (G b a) = conj (τ (G a b)))
include hG

theorem hC_conj (u v : Fin r → ℂ) : hermC τ G v u = conj (hermC τ G u v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hG x y]
  ring

theorem hC_self_real (u : Fin r → ℂ) : (hermC τ G u u).im = 0 := Complex.conj_eq_iff_im.mp (hC_conj hG u u).symm

theorem hC_add_right (u v v' : Fin r → ℂ) :
    hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by
  simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem hermC_smul_right (a : ℂ) (u v : Fin r → ℂ) :
    hermC τ G u (a • v) = conj a * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem hC_sum_right {n : ℕ} (f : Fin n → Fin r → ℂ) (w : Fin n → ℂ) (v : Fin r → ℂ) :
    hermC τ G v (∑ b, w b • f b) = ∑ b, conj (w b) * hermC τ G v (f b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hC_conj hG (∑ b, w b • f b) v, hC_sum_left, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, hC_conj hG (f b) v]

theorem gramF_comb {n : ℕ} (f : Fin n → Fin r → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    gramF τ G (fun a => ∑ b, M b a • f b) = Mᵀ * gramF τ G f * M.map conj := by
  ext a c
  simp only [gramF, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hC_sum_left]
  simp_rw [hC_sum_right hG]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem det_gramF_comb {n : ℕ} (f : Fin n → Fin r → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    (gramF τ G (fun a => ∑ b, M b a • f b)).det = M.det * (gramF τ G f).det * conj M.det := by
  rw [gramF_comb hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  congr 1
  exact ((starRingEnd ℂ).map_det M).symm

theorem det_gramF_real {n : ℕ} (f : Fin n → Fin r → ℂ) : (gramF τ G f).det.im = 0 := by
  have h : (gramF τ G f)ᴴ = gramF τ G f := by
    ext a b
    rw [Matrix.conjTranspose_apply]
    simp only [gramF, Matrix.of_apply]
    rw [hC_conj hG (f b) (f a), starRingEnd_apply]
  have h2 := Matrix.det_conjTranspose (gramF τ G f)
  rw [h] at h2
  apply Complex.conj_eq_iff_im.mp
  rw [starRingEnd_apply]
  exact h2.symm

theorem hC_pv_self {n : ℕ} (f : Fin n → Fin r → ℂ) (e : Fin r → ℂ)
    (hA : IsUnit (gramF τ G f).det) :
    hermC τ G (pv τ G f e) (pv τ G f e) = ∑ b, conj (yv τ G f e b) * cv τ G f e b := by
  rw [show hermC τ G (pv τ G f e) (pv τ G f e) =
      hermC τ G (pv τ G f e) (∑ b, yv τ G f e b • f b) from rfl, hC_sum_right hG]
  simp only [pv_orth τ G f e hA]

theorem mt_eq {n : ℕ} (f : Fin n → Fin r → ℂ) (e : Fin r → ℂ) (hA : IsUnit (gramF τ G f).det) :
    mt τ G f e = hermC τ G (pv τ G f e) (pv τ G f e) := by
  rw [hC_pv_self hG f e hA]
  have hH : (gramF τ G f)ᴴ = gramF τ G f := by
    ext a b
    rw [Matrix.conjTranspose_apply]
    simp only [gramF, Matrix.of_apply]
    rw [hC_conj hG (f b) (f a), starRingEnd_apply]
  have hI : ∀ a b, conj ((gramF τ G f)⁻¹ a b) = (gramF τ G f)⁻¹ b a := by
    intro a b
    have h3 := congrFun (congrFun (Matrix.conjTranspose_nonsing_inv (gramF τ G f)) b) a
    rw [hH, Matrix.conjTranspose_apply] at h3
    rw [starRingEnd_apply]
    exact h3
  unfold mt yv
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, hI, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

section Step
variable {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ)

theorem pv_pyth (hA : IsUnit (gramF τ G f).det)
    (hA' : IsUnit (gramF τ G (fun a : Fin n => f a.castSucc)).det) :
    hermC τ G (pv τ G f e) (pv τ G f e) =
      hermC τ G (pv τ G (fun a : Fin n => f a.castSucc) e)
        (pv τ G (fun a : Fin n => f a.castSucc) e) + hermC τ G (dv τ G f e) (dv τ G f e) := by
  have hp : pv τ G f e = pv τ G (fun a : Fin n => f a.castSucc) e + dv τ G f e := by
    unfold dv
    abel
  have h0 : hermC τ G (dv τ G f e) (pv τ G (fun a : Fin n => f a.castSucc) e) = 0 := by
    rw [show hermC τ G (dv τ G f e) (pv τ G (fun a : Fin n => f a.castSucc) e) =
        hermC τ G (dv τ G f e) (∑ b, yv τ G (fun a : Fin n => f a.castSucc) e b • f b.castSucc)
        from rfl, hC_sum_right hG]
    exact Finset.sum_eq_zero fun b _ => by simp only [dv_orth τ G f e hA hA' b, mul_zero]
  have h1 : hermC τ G (pv τ G (fun a : Fin n => f a.castSucc) e) (dv τ G f e) = 0 := by
    rw [hC_conj hG (dv τ G f e) _, h0, map_zero]
  rw [hp, hC_add_left, hC_add_right hG, hC_add_right hG, h0, h1]
  ring

theorem det_step (hA : IsUnit (gramF τ G f).det)
    (hA' : IsUnit (gramF τ G (fun a : Fin n => f a.castSucc)).det) :
    (gramF τ G (fun a : Fin n => f a.castSucc)).det * hermC τ G (dv τ G f e) (dv τ G f e) =
      yv τ G f e (Fin.last n) * conj (yv τ G f e (Fin.last n)) * (gramF τ G f).det := by
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, M = Matrix.of fun b a =>
      if a = Fin.last n then
        (yv τ G f e b - Fin.snoc (α := fun _ => ℂ) (yv τ G (fun a : Fin n => f a.castSucc) e) 0 b)
      else if b = a then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : Fin (n + 1) → Fin r → ℂ, g = fun a => ∑ b, M b a • f b := ⟨_, rfl⟩
  have hgl : g (Fin.last n) = dv τ G f e := by
    rw [hgdef, dv_eq]
    simp [hMdef]
  have hgc : ∀ a : Fin n, g a.castSucc = f a.castSucc := by
    intro a
    rw [hgdef]
    simp [hMdef, Fin.castSucc_ne_last]
  have hM : M.det = yv τ G f e (Fin.last n) := by
    rw [Matrix.det_of_upperTriangular, Fin.prod_univ_castSucc]
    · simp [hMdef, Fin.castSucc_ne_last]
    · intro i j hij
      have hij' : j < i := hij
      have hj : j ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hij' (Fin.le_last i))
      simp [hMdef, hj, ne_of_gt hij']
  have hgram : (gramF τ G g).det =
      (gramF τ G (fun a : Fin n => f a.castSucc)).det * hermC τ G (dv τ G f e) (dv τ G f e) := by
    rw [Matrix.det_succ_column _ (Fin.last n), Fin.sum_univ_castSucc]
    have hsub : (gramF τ G g).submatrix (Fin.last n).succAbove (Fin.last n).succAbove =
        gramF τ G (fun a : Fin n => f a.castSucc) := by
      ext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_last, gramF, Matrix.of_apply, hgc]
    have hz0 : ∀ i : Fin n, gramF τ G g i.castSucc (Fin.last n) = 0 := by
      intro i
      simp only [gramF, Matrix.of_apply, hgc, hgl]
      rw [hC_conj hG (dv τ G f e) (f i.castSucc), dv_orth τ G f e hA hA' i, map_zero]
    have hll : gramF τ G g (Fin.last n) (Fin.last n) = hermC τ G (dv τ G f e) (dv τ G f e) := by
      simp only [gramF, Matrix.of_apply, hgl]
    have hsgn : ((-1 : ℂ) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    simp only [hz0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
    rw [hsub, hll, hsgn]
    ring
  have hd := det_gramF_comb hG f M
  rw [← hgdef, hgram, hM] at hd
  rw [hd]
  ring

end Step

end

end ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
end

namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section

variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

def famN (x : Matrix (Fin r) (Fin r) ℂ) (i : ℕ) (hi : i ≤ r) : Fin i → Fin r → ℂ :=
  fun a => col x (Fin.castLE hi a)

def pN (x : Matrix (Fin r) (Fin r) ℂ) (e : Fin r → ℂ) (i : ℕ) : Fin r → ℂ :=
  if h : i ≤ r then pv τ G (famN x i h) e else 0

def mN (x : Matrix (Fin r) (Fin r) ℂ) (e : Fin r → ℂ) (i : ℕ) : ℝ :=
  (hermC τ G (pN τ G x e i) (pN τ G x e i)).re

theorem famN_succ (x : Matrix (Fin r) (Fin r) ℂ) (i : ℕ) (h : i + 1 ≤ r) :
    (fun a : Fin i => famN x (i + 1) h a.castSucc) = famN x i (Nat.le_of_succ_le h) := rfl

theorem mN_zero (x : Matrix (Fin r) (Fin r) ℂ) (e : Fin r → ℂ) : mN τ G x e 0 = 0 := by
  simp [mN, pN, pv, hermC]

section Frame
variable {τ G} (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (p0 : ℕ) (hp0 : p0 ≤ r)
  (x : Matrix (Fin r) (Fin r) ℂ) (hx : x.det ≠ 0)
  (hsg : ∀ i (h : i ≤ r), 0 < psgn p0 i * (gramF τ G (famN x i h)).det.re)
  (e : Fin r → ℂ) (he : hermC τ G e e = 0)
include hsg

theorem unit_of (i : ℕ) (h : i ≤ r) : IsUnit (gramF τ G (famN x i h)).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h1 := hsg i h
  rw [h0] at h1
  simp at h1

include hG

theorem mN_succ (i : ℕ) (h : i + 1 ≤ r) : mN τ G x e (i + 1) = mN τ G x e i +
    (hermC τ G (dv τ G (famN x (i + 1) h) e) (dv τ G (famN x (i + 1) h) e)).re := by
  have hp := pv_pyth hG (famN x (i + 1) h) e (unit_of p0 x hsg (i + 1) h)
    (unit_of p0 x hsg i (Nat.le_of_succ_le h))
  rw [famN_succ] at hp
  simp only [mN, pN, dif_pos h, dif_pos (Nat.le_of_succ_le h)]
  rw [hp, Complex.add_re]

theorem mN_step (i : ℕ) (h : i + 1 ≤ r) : 0 ≤ sgn p0 i * (mN τ G x e (i + 1) - mN τ G x e i) := by
  have hA1 := unit_of p0 x hsg (i + 1) h
  have hA0 := unit_of p0 x hsg i (Nat.le_of_succ_le h)
  have hs := det_step hG (famN x (i + 1) h) e hA1 hA0
  rw [famN_succ] at hs
  rw [mN_succ hG p0 x hsg e i h, add_sub_cancel_left]
  set y := yv τ G (famN x (i + 1) h) e (Fin.last i)
  set hd := hermC τ G (dv τ G (famN x (i + 1) h) e) (dv τ G (famN x (i + 1) h) e)
  have hre := congrArg Complex.re hs
  rw [Complex.mul_conj, Complex.mul_re, Complex.mul_re, det_gramF_real hG, hC_self_real hG,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul, sub_zero] at hre
  have hps : psgn p0 (i + 1) = psgn p0 i * sgn p0 i := Finset.prod_range_succ _ _
  have key : (psgn p0 i * (gramF τ G (famN x i (Nat.le_of_succ_le h))).det.re) * (sgn p0 i * hd.re) =
      Complex.normSq y * (psgn p0 (i + 1) * (gramF τ G (famN x (i + 1) h)).det.re) := by
    rw [hps]; linear_combination (psgn p0 i * sgn p0 i) * hre
  have h1 := hsg i (Nat.le_of_succ_le h)
  have h2 := hsg (i + 1) h
  refine le_of_mul_le_mul_left ?_ h1
  rw [mul_zero, key]
  exact mul_nonneg (Complex.normSq_nonneg _) h2.le

include hp0 in
theorem mN_up (j : ℕ) (hj : j ≤ p0) (i : ℕ) (hi : i ≤ j) : mN τ G x e i ≤ mN τ G x e j := by
  have step : ∀ k, k < p0 → mN τ G x e k ≤ mN τ G x e (k + 1) := by
    intro k hk
    have h1 := mN_step (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e) (i := k) (h := by omega)
    have hs : sgn p0 k = 1 := by simp [sgn, hk]
    rw [hs] at h1
    linarith
  revert hj
  induction j, hi using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ j hij ih => intro hj; exact (ih (by omega)).trans (step j (by omega))

theorem mN_down (i : ℕ) (hi : p0 ≤ i) (j : ℕ) (hij : i ≤ j) (hj : j ≤ r) :
    mN τ G x e j ≤ mN τ G x e i := by
  have step : ∀ k, p0 ≤ k → k + 1 ≤ r → mN τ G x e (k + 1) ≤ mN τ G x e k := by
    intro k hk hkr
    have h1 := mN_step (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e) (i := k) (h := hkr)
    have hs : sgn p0 k = -1 := by simp [sgn, not_lt.mpr hk]
    rw [hs] at h1
    linarith
  revert hj
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ j hij ih => intro hj; exact (step j (by omega) hj).trans (ih (by omega))

include hx in
theorem pN_top : pN τ G x e r = e := by
  have hA := unit_of p0 x hsg r le_rfl
  rw [pN, dif_pos le_rfl]
  have he' : e = ∑ d, (x⁻¹ *ᵥ e) d • famN x r le_rfl d := by
    have h1 : x *ᵥ (x⁻¹ *ᵥ e) = e := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hx),
        Matrix.one_mulVec]
    conv_lhs => rw [← h1]
    funext k
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, famN, col]
    exact Finset.sum_congr rfl fun d _ => by rw [mul_comm]; rfl
  have h2 : e - pv τ G (famN x r le_rfl) e = ∑ d, ((x⁻¹ *ᵥ e) d - yv τ G (famN x r le_rfl) e d) •
      famN x r le_rfl d := by
    conv_lhs => arg 1; rw [he']
    rw [pv, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => (sub_smul _ _ _).symm
  have h3 := comb_orth_zero τ G (famN x r le_rfl) hA _ fun d => by
    rw [← h2, hC_sub_left, pv_orth τ G _ e hA d]; exact sub_self _
  rw [← h2] at h3
  exact (sub_eq_zero.mp h3).symm

include hx he in
theorem mN_top : mN τ G x e r = 0 := by
  unfold mN
  rw [pN_top (hG := hG) (p0 := p0) (x := x) (hx := hx) (hsg := hsg) (e := e), he]
  simp

include hp0 hx he in
theorem mN_bounds (i : ℕ) (hi : i ≤ r) : 0 ≤ mN τ G x e i ∧ mN τ G x e i ≤ mN τ G x e p0 := by
  rcases le_total i p0 with hi0 | hi0
  · constructor
    · have h1 := mN_up (hG := hG) (p0 := p0) (hp0 := hp0) (x := x) (hsg := hsg) (e := e)
        (j := i) (hj := hi0) (i := 0) (hi := Nat.zero_le _)
      rw [mN_zero] at h1
      exact h1
    · exact mN_up (hG := hG) (p0 := p0) (hp0 := hp0) (x := x) (hsg := hsg) (e := e)
        (j := p0) (hj := le_rfl) (i := i) (hi := hi0)
  · constructor
    · have h1 := mN_down (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e)
        (i := i) (hi := hi0) (j := r) (hij := hi) (hj := le_rfl)
      rw [mN_top (hG := hG) (p0 := p0) (x := x) (hx := hx) (hsg := hsg) (e := e) (he := he)] at h1
      exact h1
    · exact mN_down (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e)
        (i := p0) (hi := le_rfl) (j := i) (hij := hi0) (hj := hi)

include hp0 hx he in
theorem mN_pos (hne : e ≠ 0) : 0 < mN τ G x e p0 := by
  by_contra hle
  rw [not_lt] at hle
  have hz : ∀ i, i ≤ r → mN τ G x e i = 0 := fun i hi => by
    have := mN_bounds hG p0 hp0 x hx hsg e he i hi; linarith
  have hstep : ∀ i (h : i + 1 ≤ r), pN τ G x e (i + 1) = pN τ G x e i := by
    intro i h
    have hA1 := unit_of p0 x hsg (i + 1) h
    have hA0 := unit_of p0 x hsg i (Nat.le_of_succ_le h)
    have hd0 : (hermC τ G (dv τ G (famN x (i + 1) h) e) (dv τ G (famN x (i + 1) h) e)).re = 0 := by
      have := mN_succ hG p0 x hsg e i h
      rw [hz i (by omega), hz (i + 1) h] at this; linarith
    have hs := det_step hG (famN x (i + 1) h) e hA1 hA0
    have hre := congrArg Complex.re hs
    rw [Complex.mul_conj, Complex.mul_re, Complex.mul_re, det_gramF_real hG, hC_self_real hG,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul, sub_zero, hd0,
      mul_zero] at hre
    have hd1 : (gramF τ G (famN x (i + 1) h)).det.re ≠ 0 := fun h0 => by
      have := hsg (i + 1) h; rw [h0, mul_zero] at this; exact lt_irrefl _ this
    have hy : yv τ G (famN x (i + 1) h) e (Fin.last i) = 0 :=
      Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hre.symm).resolve_right hd1)
    have hdv := dv_zero τ G (famN x (i + 1) h) e hA1 hA0 hy
    rw [dv, famN_succ, sub_eq_zero] at hdv
    simp only [pN, dif_pos h, dif_pos (Nat.le_of_succ_le h)]
    exact hdv
  have hall : ∀ i, i ≤ r → pN τ G x e i = 0 := by
    intro i hi
    induction i with
    | zero => rw [pN, dif_pos (Nat.zero_le r), pv]; exact Finset.sum_empty
    | succ i ih => rw [hstep i hi, ih (by omega)]
  exact hne ((pN_top hG p0 x hx hsg e).symm.trans (hall r le_rfl))

end Frame

end

end ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
end

namespace ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section

variable {E : Type} [Field E] {r : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E}

def flw (α : ℂ) (e : Fin r → ℂ) (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ}
    (f : Fin n → Fin r → ℂ) : Fin n → Fin r → ℂ :=
  fun a => f a + (α * hermC τ G (f a) e) • e

theorem cv_flw (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ) :
    cv τ G (flw α e τ G f) e = cv τ G f e := by
  funext a
  show hermC τ G e (f a + (α * hermC τ G (f a) e) • e) = hermC τ G e (f a)
  rw [GramDeterminantReal.hC_add_right, GramDeterminantReal.hermC_smul_right, he, mul_zero, add_zero]
  all_goals exact hG

theorem gramF_flw (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ) :
    gramF τ G (flw α e τ G f) = gramF τ G f +
      replicateCol Unit (fun a => (α + conj α) * conj (cv τ G f e a)) *
        replicateRow Unit (cv τ G f e) := by
  ext a b
  have hc := GramDeterminantReal.hC_conj hG
  simp only [Matrix.add_apply, Matrix.mul_apply, replicateCol, replicateRow, Matrix.of_apply,
    Finset.univ_unique, Finset.sum_singleton, GramDeterminantReal.gramF, flw]
  rw [GramDeterminantReal.hC_add_left, GramDeterminantReal.hC_add_right, GramDeterminantReal.hC_add_right,
    GramDeterminantReal.hermC_smul_left, GramDeterminantReal.hermC_smul_left, GramDeterminantReal.hermC_smul_right,
    GramDeterminantReal.hermC_smul_right, he, hc e (f a)]
  all_goals try exact hG
  simp only [GramDeterminantReal.cv, map_mul]
  rw [← hc (f b) e]
  ring

theorem mt_y {n : ℕ} (f : Fin n → Fin r → ℂ) (e : Fin r → ℂ) :
    GramDeterminantReal.mt τ G f e = ∑ b, yv τ G f e b * conj (cv τ G f e b) := by
  simp only [GramDeterminantReal.mt, GramDeterminantReal.yv, Matrix.vecMul, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm

theorem det_flw (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ)
    (hA : IsUnit (gramF τ G f).det) : (gramF τ G (flw α e τ G f)).det =
      (gramF τ G f).det * (1 + (α + conj α) * GramDeterminantReal.mt τ G f e) := by
  rw [gramF_flw hG e he α f, Matrix.det_add_replicateCol_mul_replicateRow hA]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateCol, replicateRow,
    Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, GramDeterminantReal.mt, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mt_flw (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ)
    (hA : IsUnit (gramF τ G f).det) (h1 : 1 + (α + conj α) * GramDeterminantReal.mt τ G f e ≠ 0) :
    GramDeterminantReal.mt τ G (flw α e τ G f) e =
      GramDeterminantReal.mt τ G f e / (1 + (α + conj α) * GramDeterminantReal.mt τ G f e) := by
  set s := α + conj α with hs
  set m := GramDeterminantReal.mt τ G f e with hm
  have hA' : IsUnit (gramF τ G (flw α e τ G f)).det := by
    rw [det_flw hG e he α f hA]
    exact hA.mul (isUnit_iff_ne_zero.mpr h1)
  have hyA : Matrix.vecMul (yv τ G f e) (gramF τ G f) = cv τ G f e := by
    simp only [GramDeterminantReal.yv, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]
  have hyB : Matrix.vecMul (yv τ G f e)
      (replicateCol Unit (fun a => s * conj (cv τ G f e a)) * replicateRow Unit (cv τ G f e)) =
      (s * m) • cv τ G f e := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, replicateCol, replicateRow,
      Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul]
    rw [hm, mt_y, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have key : Matrix.vecMul (yv τ G f e) (gramF τ G (flw α e τ G f)) =
      (1 + s * m) • cv τ G f e := by
    rw [gramF_flw hG e he α f, Matrix.vecMul_add, hyA, hyB, add_smul, one_smul]
  have hy : yv τ G (flw α e τ G f) e = (1 + s * m)⁻¹ • yv τ G f e := by
    have h2 : yv τ G f e = (1 + s * m) • yv τ G (flw α e τ G f) e := by
      conv_rhs => rw [GramDeterminantReal.yv, cv_flw hG e he α f, ← Matrix.smul_vecMul, ← key,
        Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hA', Matrix.vecMul_one]
    rw [h2, smul_smul, inv_mul_cancel₀ h1, one_smul]
  rw [mt_y (flw α e τ G f) e, hy, cv_flw hG e he α f, div_eq_inv_mul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  congr 1
  exact (mt_y f e).symm

end

end ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
end

namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open scoped ComplexConjugate
noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} (X : Data E r)

theorem hG_of (τ : X.Ψ) : ∀ a b, τ.1 (X.Gm b a) = conj (τ.1 (X.Gm a b)) := by
  intro a b
  rw [← X.Gm_herm a b]
  first
    | simp [NumberField.IsCMField.complexEmbedding_complexConj]
    | rw [NumberField.IsCMField.complexEmbedding_complexConj]
    | simp [NumberField.IsCMField.complexConj_apply]
    | simp [NumberField.IsCMField.conj_complexEmbedding]
    | (simp only [cc]
       exact NumberField.IsCMField.complexEmbedding_complexConj ..)

theorem c_pos (τ : X.Ψ) : 0 < X.c τ := by
  unfold Data.c
  have h : (τ.1 X.ξ0) ≠ 0 := (map_ne_zero τ.1).mpr X.ξ0_ne
  have := norm_pos_iff.mpr h
  linarith

theorem hsg_of {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    ∀ i (h : i ≤ r), 0 < psgn X.p0 i * (gramF τ.1 X.Gm (famN (mat x τ) i h)).det.re := by
  intro i h
  unfold Data.dom GG at hx
  simp only [Set.mem_setOf_eq] at hx
  have h1 := (hx τ).2 ⟨i, Nat.lt_succ_of_le h⟩
  first
    | exact h1
    | (unfold dmin lminor gram gramF famN at h1
       exact h1)

theorem dmin_eq (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i = (gramF τ.1 X.Gm (famN (mat x τ) i (Nat.le_of_lt_succ i.isLt))).det := rfl

theorem famN_flow (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) (i : ℕ)
    (h : i ≤ r) : famN (mat (X.flowV e s x) τ) i h =
      flw (-I * X.c τ * s τ) (e τ) τ.1 X.Gm (famN (mat x τ) i h) := by
  unfold Data.flowV flw famN mat
  funext a c
  show ∑ b, X.flowMatV (e τ) τ (s τ) c b * x τ b (Fin.castLE h a) =
    x τ c (Fin.castLE h a) + (-I * (X.c τ : ℂ) * s τ *
      hermC τ.1 X.Gm (fun d => x τ d (Fin.castLE h a)) (e τ)) * e τ c
  unfold Data.flowMatV hermC
  simp only [Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem alpha_re (c : ℝ) (s : ℂ) : (-I * (c : ℂ) * s) + conj (-I * (c : ℂ) * s) =
    ((2 * c * s.im : ℝ) : ℂ) := by
  apply Complex.ext <;> simp <;> ring

theorem det_flowMat (e : Fin r → ℂ) (τ : X.Ψ) (s : ℂ) (he : hermC τ.1 X.Gm e e = 0) :
    (X.flowMatV e τ s).det = 1 := by
  unfold Data.flowMatV hermC at *
  have key : (of fun a b => (if a = b then (1 : ℂ) else 0) - I * (X.c τ : ℂ) * s * e a *
      ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) =
      1 + replicateCol Unit (fun a => -(I * (X.c τ : ℂ) * s * e a)) *
        replicateRow Unit (fun b => ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) := by
    ext a b
    simp [Matrix.one_apply, Matrix.mul_apply, sub_eq_add_neg]
  have hd : (fun b => ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) ⬝ᵥ
      (fun a => -(I * (X.c τ : ℂ) * s * e a)) = 0 := by
    calc (fun b => ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) ⬝ᵥ
          (fun a => -(I * (X.c τ : ℂ) * s * e a))
        = -(I * (X.c τ : ℂ) * s) * ∑ a, ∑ b, e a * τ.1 (X.Gm a b) * (starRingEnd ℂ) (e b) := by
          simp only [dotProduct]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = 0 := by rw [he, mul_zero]
  rw [key, det_one_add_replicateCol_mul_replicateRow, hd, add_zero]

section Prof
variable {x : Frame X.Ψ r} (hx : x ∈ X.dom) (e : X.Ψ → Fin r → ℂ) (τ : X.Ψ)
include hx

theorem mt_famN (i : ℕ) (h : i ≤ r) : GramDeterminantReal.mt τ.1 X.Gm (famN (mat x τ) i h) (e τ) =
    (mN τ.1 X.Gm (mat x τ) (e τ) i : ℂ) := by
  rw [mt_eq (hG_of X τ) _ _ (unit_of X.p0 (mat x τ) (hsg_of X hx τ) i h), mN, pN, dite_eq_left h]
  exact Complex.ext rfl (by simp [hC_self_real (hG_of X τ)])

theorem dmin_flow (he : hermC τ.1 X.Gm (e τ) (e τ) = 0) (s : X.Ψ → ℂ) (i : ℕ) (h : i ≤ r) :
    (gramF τ.1 X.Gm (famN (mat (X.flowV e s x) τ) i h)).det =
      (gramF τ.1 X.Gm (famN (mat x τ) i h)).det *
        ((1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) i : ℝ) : ℂ) := by
  rw [famN_flow, det_flw (hG_of X τ) (e τ) he _ _ (unit_of X.p0 (mat x τ) (hsg_of X hx τ) i h),
    mt_famN X hx e τ i h, alpha_re]
  push_cast; ring

theorem maj_eq (he : hermC τ.1 X.Gm (e τ) (e τ) = 0) :
    X.maj x τ (e τ) = 2 * mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := by
  have : X.posPart x τ (e τ) = (GramDeterminantReal.mt τ.1 X.Gm (famN (mat x τ) X.p0 X.p0_le) (e τ)).re := rfl
  rw [Data.maj, this, mt_famN X hx e τ X.p0 X.p0_le, he, Complex.ofReal_re, Complex.zero_re, sub_zero]

theorem maj_flow (he : hermC τ.1 X.Gm (e τ) (e τ) = 0) (s : X.Ψ → ℂ)
    (h1 : 1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0 ≠ 0) :
    X.maj (X.flowV e s x) τ (e τ) = 2 * (mN τ.1 X.Gm (mat x τ) (e τ) X.p0 /
      (1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0)) := by
  have hα := alpha_re (X.c τ) (s τ)
  have hp : X.posPart (X.flowV e s x) τ (e τ) =
      (GramDeterminantReal.mt τ.1 X.Gm (famN (mat (X.flowV e s x) τ) X.p0 X.p0_le) (e τ)).re := rfl
  rw [Data.maj, hp, famN_flow, mt_flw (hG_of X τ) (e τ) he _ _
    (unit_of X.p0 (mat x τ) (hsg_of X hx τ) X.p0 X.p0_le), hα, mt_famN X hx e τ X.p0 X.p0_le, he,
    Complex.zero_re, sub_zero]
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_div,
      Complex.ofReal_re]
  · rw [hα, mt_famN X hx e τ X.p0 X.p0_le, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_add]
    exact_mod_cast h1

end Prof

end

end ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
