module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MmatMulVec
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bNormHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bExpHolds

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

namespace FrameDegreeData

noncomputable section

variable {r : ℕ} (X : Data E r)

lemma upper_of_bor {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) : (mat b τ).BlockTriangular id := by
  intro i j hij
  exact (hb τ).2 i j hij

lemma bdiag_ne {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (j : Fin r) : b τ j j ≠ 0 := by
  have h1 := (hb τ).1
  rw [Matrix.det_of_upperTriangular (upper_of_bor X hb τ)] at h1
  exact (Finset.prod_ne_zero_iff.1 h1) j (Finset.mem_univ _)

private theorem sum_eq_sum_castLE_of_eq_zero {n m : ℕ} (h : m ≤ n) (f : Fin n → ℂ)
    (hf : ∀ j : Fin n, m ≤ j.val → f j = 0) :
    ∑ j, f j = ∑ j : Fin m, f (Fin.castLE h j) := by
  refine Eq.trans ?_ (Finset.sum_map (Finset.univ : Finset (Fin m)) ⟨Fin.castLE h, Fin.castLE_injective h⟩ f)
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
  by_contra hlt
  push_neg at hlt
  exact hj (Finset.mem_map.2 ⟨⟨j.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

private theorem gram_eq_lemma {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a c
  simp only [gram, Matrix.of_apply, hermC, col, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma dmin_rmul (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (rmul x b) τ i =
      (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) *
        dmin X.Gm x τ i *
        conj (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) := by
  have hB := upper_of_bor X hb τ
  have hmat : mat (rmul x b) τ = mat x τ * mat b τ := rfl
  unfold dmin lminor
  rw [hmat, gram_eq_lemma, gram_eq_lemma τ.1 X.Gm (mat x τ), Matrix.transpose_mul, Matrix.map_mul]
  have hre : (mat b τ)ᵀ * (mat x τ)ᵀ * X.Gm.map τ.1 *
      ((mat x τ).map (starRingEnd ℂ) * (mat b τ).map (starRingEnd ℂ)) =
      (mat b τ)ᵀ * ((mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ)) *
        (mat b τ).map (starRingEnd ℂ) := by
    simp only [Matrix.mul_assoc]
  rw [hre]
  set A := (mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ) with hA
  set B := mat b τ with hBdef
  set e : Fin i → Fin r := Fin.castLE (Nat.le_of_lt_succ i.isLt) with he
  have hlt : ∀ (a : Fin i) (j : Fin r), (i : ℕ) ≤ j.val → e a < j := by
    intro a j hj
    rw [Fin.lt_iff_val_lt_val, he, Fin.coe_castLE]
    have := a.isLt
    omega
  have hsub : (Bᵀ * A * B.map (starRingEnd ℂ)).submatrix e e =
      (B.submatrix e e)ᵀ * A.submatrix e e * (B.submatrix e e).map (starRingEnd ℂ) := by
    ext a c
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [sum_eq_sum_castLE_of_eq_zero (Nat.le_of_lt_succ i.isLt) _ (fun k hk => by
      have h0 : B k (e c) = 0 := hB (hlt c k hk)
      rw [h0, map_zero, mul_zero])]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact sum_eq_sum_castLE_of_eq_zero (Nat.le_of_lt_succ i.isLt) _ (fun j hj => by
      have h0 : B j (e a) = 0 := hB (hlt a j hj)
      rw [h0, zero_mul])
  have hBe : (B.submatrix e e).BlockTriangular id := by
    intro j k hjk
    apply hB
    show e k < e j
    rw [Fin.lt_iff_val_lt_val, he, Fin.coe_castLE, Fin.coe_castLE]
    exact hjk
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show ((B.submatrix e e).map (starRingEnd ℂ)).det = starRingEnd ℂ (B.submatrix e e).det from
      (RingHom.map_det _ _).symm,
    Matrix.det_of_upperTriangular hBe]
  rfl

lemma ratio_rmul (x : Frame X.Ψ r) (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (k : Fin r) :
    ‖dmin X.Gm (rmul x b) τ k.succ / dmin X.Gm (rmul x b) τ k.castSucc‖ =
      ‖b τ k k‖ ^ 2 * ‖dmin X.Gm x τ k.succ / dmin X.Gm x τ k.castSucc‖ := by
  have hsucc : (∏ j : Fin (k.succ : ℕ), mat b τ (Fin.castLE (Nat.le_of_lt_succ k.succ.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.succ.isLt) j)) =
      (∏ j : Fin (k.castSucc : ℕ), mat b τ (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j)
        (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j)) * b τ k k := by
    change (∏ j : Fin ((k : ℕ) + 1), mat b τ (Fin.castLE (Nat.le_of_lt_succ k.succ.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.succ.isLt) j)) = _
    rw [Fin.prod_univ_castSucc]
    rfl
  have hPk : (∏ j : Fin (k.castSucc : ℕ), mat b τ (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => bdiag_ne X hb τ _
  rw [dmin_rmul X x hb τ k.succ, dmin_rmul X x hb τ k.castSucc, hsucc]
  set Pk := (∏ j : Fin (k.castSucc : ℕ), mat b τ (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j))
  have hPn : ‖Pk‖ ≠ 0 := norm_ne_zero_iff.2 hPk
  simp only [norm_div, norm_mul, map_mul, Complex.norm_conj]
  by_cases hd : ‖dmin X.Gm x τ k.castSucc‖ = 0
  · simp [hd]
  · field_simp

lemma factor_eq (t q : ℝ) (ht : 0 < t) (hq : 0 ≤ q) (l : ℤ) :
    t ^ l * (t ^ 2 * q) ^ (-(l : ℝ) / 2) = q ^ (-(l : ℝ) / 2) := by
  rw [Real.mul_rpow (by positivity) hq]
  have h1 : (t ^ 2) ^ (-(l : ℝ) / 2) = (t ^ l)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le,
      show ((2 : ℕ) : ℝ) * (-(l : ℝ) / 2) = -(l : ℝ) by push_cast; ring,
      Real.rpow_neg ht.le, Real.rpow_intCast]
  rw [h1, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ ht.ne'), one_mul]

lemma pnorm_rmul (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hP : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) : X.pnorm la P (rmul x b) = X.pnorm la P x := by
  have hfac : ∀ (τ : X.Ψ) (i : Fin r), ‖b τ i i‖ ^ la τ i *
      (‖b τ i i‖ ^ 2 * ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖) ^ (-(la τ i : ℝ) / 2) =
      ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) :=
    fun τ i => factor_eq _ _ (norm_pos_iff.2 (bdiag_ne X hb τ i)) (norm_nonneg _) _
  unfold Data.pnorm
  rw [hP x hx b hb, norm_mul]
  simp only [ratio_rmul X x hx hb]
  unfold bchar
  simp only [norm_prod, norm_zpow]
  rw [← Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => hfac τ i]
  simp only [Finset.prod_mul_distrib]
  ring

private theorem hermC_sub_left_of_natDim {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (u v w : Fin r → ℂ) : hermC τ G (u - v) w = hermC τ G u w - hermC τ G v w := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem hermC_eq_zero_of_mem_span' {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (w : Fin r → ℂ)
    (S : Set (Fin r → ℂ)) (h : ∀ s ∈ S, hermC τ G w s = 0) {v : Fin r → ℂ}
    (hv : v ∈ Submodule.span ℂ S) : hermC τ G w v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp [hermC]
  | add x y _ _ hx hy =>
    have e : hermC τ G w (x + y) = hermC τ G w x + hermC τ G w y := by
      simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
    rw [e, hx, hy, add_zero]
  | smul c x _ hx =>
    have e : hermC τ G w (c • x) = (starRingEnd ℂ) c * hermC τ G w x := by
      simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [e, hx, mul_zero]

lemma ppos_sameFlag {x x' : Frame X.Ψ r} (hx : x ∈ X.dom) (hx' : x' ∈ X.dom) (h : X.SameFlag x x')
    (τ : X.Ψ) (u : Fin r → ℂ) : X.ppos x τ u = X.ppos x' τ u := by
  have hspan := h τ
  have hmem : ∀ y : Frame X.Ψ r, X.ppos y τ u ∈
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat y τ) (Fin.castLE X.p0_le a)) := by
    intro y
    rw [X.ppos_eq]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have horth : ∀ y ∈ X.dom, ∀ c ∈
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat y τ) (Fin.castLE X.p0_le a)),
      hermC τ.1 X.Gm (X.ppos y τ u - u) c = 0 := by
    intro y hy c hc
    refine hermC_eq_zero_of_mem_span' τ.1 X.Gm _ _ (fun s hs => ?_) hc
    obtain ⟨d, rfl⟩ := hs
    rw [hermC_sub_left_of_natDim]
    exact sub_eq_zero.2 (X.hermC_ppos_colP hy τ u d)
  set v := X.ppos x τ u - X.ppos x' τ u with hv
  have hvmem : v ∈
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le a)) := by
    refine Submodule.sub_mem _ (hmem x) ?_
    rw [hspan]
    exact hmem x'
  have hvperp : ∀ c ∈
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le a)),
      hermC τ.1 X.Gm v c = 0 := by
    intro c hc
    have e : v = (X.ppos x τ u - u) - (X.ppos x' τ u - u) := by
      rw [hv]
      abel
    rw [e, hermC_sub_left_of_natDim, horth x hx c hc, horth x' hx' c (hspan ▸ hc), sub_zero]
  by_contra hne
  have hne' : v ≠ 0 := sub_ne_zero.2 hne
  have hlt := X.neg_of_perp hx τ hne' (fun b => hvperp _ (Submodule.subset_span ⟨b, rfl⟩))
  rw [hvperp v hvmem] at hlt
  simp at hlt

lemma Hf_sameFlag {x x' : Frame X.Ψ r} (hx : x ∈ X.dom) (hx' : x' ∈ X.dom) (h : X.SameFlag x x') :
    X.Hf x = X.Hf x' := by
  funext τ u w
  simp only [Data.Hf, ppos_sameFlag X hx hx' h τ u]

end

end FrameDegreeData

theorem orthonormalFlagTranslate_holds : OrthonormalFlagTranslate (E := E) := by
  intro r X
  refine ⟨fun x hx => ⟨FrameDegreeData.bOf X x, FrameDegreeData.bOf_mem X hx, FrameDegreeData.ortho_bOf X hx⟩,
    fun la P hP x hx b hb => FrameDegreeData.pnorm_rmul X la P hP x hx b hb, fun x hx x' hx' h => ?_⟩
  have hpp := FrameDegreeData.ppos_sameFlag X hx hx' h
  have hJ : X.Jz x = X.Jz x' := by
    funext u τ
    simp only [Data.Jz, hpp]
  refine ⟨fun ξ => ⟨hJ, ?_, ?_⟩, ?_⟩
  · simp only [Data.Uz, hJ]
  · unfold Data.aproj
    rw [FrameDegreeData.Hf_sameFlag X hx hx' h]
  · funext τ v
    have e : ∀ y : Frame X.Ψ r, X.posPart y τ v = (hermC τ.1 X.Gm (X.ppos y τ v) v).re := by
      intro y
      rw [X.hermC_ppos_self]
      rfl
    simp only [Data.maj, e, hpp]

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms
namespace ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Classical

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem quad2 (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian) (a : Fin 2 → ℂ) :
    M.det.re * Complex.normSq (a 1) ≤ (M 0 0).re * (∑ i, ∑ k, M i k * a i * conj (a k)).re := by
  have h00 : (M 0 0).im = 0 := by
    have := hM.apply 0 0
    rw [Complex.star_def] at this
    exact Complex.conj_eq_iff_im.mp this
  have h11 : (M 1 1).im = 0 := by
    have := hM.apply 1 1
    rw [Complex.star_def] at this
    exact Complex.conj_eq_iff_im.mp this
  have h10 : M 1 0 = conj (M 0 1) := by
    have := hM.apply 1 0
    rw [Complex.star_def] at this
    exact this.symm
  simp only [Matrix.det_fin_two, Fin.sum_univ_two, h10, Complex.sub_re, Complex.add_re,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply, h00, h11]
  nlinarith [sq_nonneg ((M 0 0).re * (a 0).re + (M 0 1).re * (a 1).re + (M 0 1).im * (a 1).im),
    sq_nonneg ((M 0 0).re * (a 0).im + (M 0 1).re * (a 1).im - (M 0 1).im * (a 1).re)]

theorem coef_zero {r : ℕ} {ξ x : Fin r → E} (hξ0 : ξ ≠ 0) (hne : ∀ e : E, x ≠ e • ξ)
    (τ : E →+* ℂ) (p q : ℂ) (h : p • Data.emb τ ξ + q • Data.emb τ x = 0) : q = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, ξ a ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hξ0 (funext h0)
  obtain ⟨b, hb⟩ : ∃ b, x b ≠ (x a / ξ a) * ξ b := by
    by_contra h0
    push_neg at h0
    exact hne (x a / ξ a) (funext fun b => by rw [Pi.smul_apply, smul_eq_mul, h0 b])
  have hm : ξ a * x b - ξ b * x a ≠ 0 := by
    intro h0
    apply hb
    rw [div_mul_eq_mul_div, eq_div_iff ha]
    linear_combination h0
  have h1 := congrFun h a
  have h2 := congrFun h b
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Data.emb] at h1 h2
  have hτ : τ (ξ a * x b - ξ b * x a) ≠ 0 := (map_ne_zero τ).2 hm
  rw [map_sub, map_mul, map_mul] at hτ
  have h3 : q * (τ (ξ a) * τ (x b) - τ (ξ b) * τ (x a)) = 0 := by
    linear_combination τ (ξ a) * h2 - τ (ξ b) * h1
  exact (mul_eq_zero.1 h3).resolve_right hτ

variable {r : ℕ} (X : Data E r)

def toCP (τ : X.Ψ) : TraceIntegralBasis.CP E := ⟨InfinitePlace.mk τ.1, IsTotallyComplex.isComplex _⟩

theorem toCP_bij : Function.Bijective (toCP X) := by
  constructor
  · rintro ⟨τ, hτ⟩ ⟨τ', hτ'⟩ h
    have h' : InfinitePlace.mk τ = InfinitePlace.mk τ' := congrArg Subtype.val h
    rcases InfinitePlace.mk_eq_iff.1 h' with e | e
    · exact Subtype.ext e
    · exfalso
      rw [← e] at hτ'
      exact (X.cmType τ).1 hτ hτ'
  · rintro ⟨w, hw⟩
    by_cases hφ : w.embedding ∈ X.Ψ
    · exact ⟨⟨_, hφ⟩, Subtype.ext (InfinitePlace.mk_embedding w)⟩
    · have hc : ComplexEmbedding.conjugate w.embedding ∈ X.Ψ := by
        by_contra hc
        exact hφ ((X.cmType _).2 hc)
      exact ⟨⟨_, hc⟩, Subtype.ext ((InfinitePlace.mk_conjugate_eq _).trans (InfinitePlace.mk_embedding w))⟩

theorem card_Psi : Fintype.card X.Ψ = fdeg E := by
  rw [Fintype.card_of_bijective (toCP_bij X)]
  unfold fdeg
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank E
  have h0 : NumberField.InfinitePlace.nrRealPlaces E = 0 := by
    first
    | exact NumberField.IsTotallyComplex.nrRealPlaces_eq_zero
    | exact NumberField.nrRealPlaces_eq_zero_iff.2 inferInstance
    | simp
  rw [h0, zero_add] at h
  rw [← h]
  unfold NumberField.InfinitePlace.nrComplexPlaces
  have h3 : Fintype.card (TraceIntegralBasis.CP E) = Fintype.card {w : InfinitePlace E // w.IsComplex} :=
    Fintype.card_congr (Equiv.refl _)
  omega

theorem card_Psi_pos : 0 < Fintype.card X.Ψ := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := by
    first
    | exact inferInstance
    | exact ⟨(Classical.arbitrary (InfinitePlace E)).embedding⟩
  rw [Fintype.card_pos_iff]
  by_cases h : φ ∈ X.Ψ
  · exact ⟨⟨φ, h⟩⟩
  · exact ⟨⟨ComplexEmbedding.conjugate φ, by
      by_contra hc
      exact h ((X.cmType φ).2 hc)⟩⟩

theorem one_le_prod_norm (γ : E) (hint : IsIntegral ℤ γ) (hγ : γ ≠ 0) :
    1 ≤ ∏ τ : X.Ψ, ‖τ.1 γ‖ ^ 2 := by
  have hall : ∀ w : InfinitePlace E, w.IsComplex := fun w => IsTotallyComplex.isComplex w
  have h1 : ∏ τ : X.Ψ, ‖τ.1 γ‖ ^ 2 = ∏ w : TraceIntegralBasis.CP E, w.1 γ ^ 2 :=
    Fintype.prod_bijective (toCP X) (toCP_bij X) _ _ fun τ => by
      show _ = (InfinitePlace.mk τ.1 γ) ^ 2
      rw [InfinitePlace.apply]
  have h2 : ∏ w : TraceIntegralBasis.CP E, w.1 γ ^ 2 = ∏ w : InfinitePlace E, w γ ^ w.mult := by
    refine Fintype.prod_equiv (Equiv.subtypeUnivEquiv hall) _ _ fun w => ?_
    show w.1 γ ^ 2 = w.1 γ ^ InfinitePlace.mult w.1
    rw [InfinitePlace.mult_isComplex w]
  rw [h1, h2, InfinitePlace.prod_eq_abs_norm]
  have hI : IsIntegral ℤ (Algebra.norm ℚ γ) := by
    first
    | exact Algebra.isIntegral_norm ℚ hint
    | exact Algebra.isIntegral_norm hint
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hI
  have hN : Algebra.norm ℚ γ ≠ 0 := Algebra.norm_ne_zero_iff.2 hγ
  rw [← hn] at hN ⊢
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hN (map_zero _)
  have h3 := Int.one_le_abs hn0
  simp only [algebraMap_int_eq, eq_intCast]
  push_cast
  exact_mod_cast h3

end

end ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientBounds
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem dmin_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i ≠ 0 := by
  intro h
  have h1 := (hx τ).2 i
  rw [h] at h1
  simp at h1

theorem nfac_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) : 0 < X.nfac la x := by
  unfold Data.nfac
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => ?_
  apply Real.rpow_pos_of_pos
  rw [norm_pos_iff]
  exact div_ne_zero (dmin_ne X hx τ _) (dmin_ne X hx τ _)

theorem norm_cexp_I (z : ℂ) (hz : z.im = 0) : ‖cexp (-(4 * (Real.pi : ℂ) * I) * z)‖ = 1 := by
  rw [Complex.norm_exp, Real.exp_eq_one_iff]
  simp [Complex.mul_re, Complex.mul_im, hz]

private lemma sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg {r : ℕ} (g : Fin r → Fin r → ℂ) (hg : ∀ a b, conj (g a b) = g b a)
    (z v w : Fin r → ℂ) (α : ℂ) (hα : conj α = -α)
    (hz : ∑ a, ∑ b, z a * g a b * conj (z b) = 0) :
    ∑ a, ∑ b, (v a - α * (∑ p, ∑ q, v p * g p q * conj (z q)) * z a) * g a b *
        conj (w b - α * (∑ p, ∑ q, w p * g p q * conj (z q)) * z b) =
      ∑ a, ∑ b, v a * g a b * conj (w b) := by
  set A := ∑ p, ∑ q, v p * g p q * conj (z q) with hA
  set B := ∑ p, ∑ q, w p * g p q * conj (z q) with hB
  have hB' : conj B = ∑ a, ∑ b, z a * g a b * conj (w b) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hB, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [map_sum, map_mul, Complex.conj_conj, hg]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have expand : ∀ a b, (v a - α * A * z a) * g a b * conj (w b - α * B * z b) =
      v a * g a b * conj (w b) + α * (conj B * (v a * g a b * conj (z b))) -
        α * A * (z a * g a b * conj (w b)) - α * α * A * conj B * (z a * g a b * conj (z b)) := by
    intro a b
    simp only [map_sub, map_mul, hα]
    ring
  simp_rw [expand, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← hA, ← hB', hz]
  ring

theorem flow_real {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (s : X.Ψ → ℝ) (la : Wt X.Ψ r) :
    X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom ∧
      X.nfac la (X.flow ξ (fun τ => (s τ : ℂ)) x) = X.nfac la x := by
  have hflow : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ) =
      gram τ.1 X.Gm (mat x τ) ∧ (X.flowMat ξ τ (s τ)).det = 1 := by
    intro τ
    have hg : ∀ p q, conj (τ.1 (X.Gm p q)) = τ.1 (X.Gm q p) := fun p q => by
      rw [← X.Gm_herm p q, cc, IsCMField.complexEmbedding_complexConj]
    have hz : ∑ a, ∑ b, τ.1 (ξ a) * τ.1 (X.Gm a b) * conj (τ.1 (ξ b)) = 0 := by
      have h0 := congrArg τ.1 hξ.2.1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [herm, map_sum, map_mul, map_zero, cc, IsCMField.complexEmbedding_complexConj] at h0
      exact h0
    have hα : conj (I * (X.c τ : ℂ) * (s τ : ℂ)) = -(I * (X.c τ : ℂ) * (s τ : ℂ)) := by
      rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
      ring
    constructor
    · ext a b
      show hermC τ.1 X.Gm (col (X.flowMat ξ τ (s τ) * mat x τ) a) (col (X.flowMat ξ τ (s τ) * mat x τ) b) =
        hermC τ.1 X.Gm (col (mat x τ) a) (col (mat x τ) b)
      have hcol : ∀ c : Fin r, col (X.flowMat ξ τ (s τ) * mat x τ) c = fun p => col (mat x τ) c p -
          (I * (X.c τ : ℂ) * (s τ : ℂ)) * (∑ p', ∑ q, col (mat x τ) c p' * τ.1 (X.Gm p' q) * conj (τ.1 (ξ q))) * τ.1 (ξ p) := by
        intro c
        funext p
        simp only [col, Data.flowMat, Matrix.mul_apply, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
          ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, reduceIte]
        congr 1
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
      unfold hermC
      rw [hcol a, hcol b]
      exact sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg (fun p q => τ.1 (X.Gm p q)) hg (fun q => τ.1 (ξ q)) (col (mat x τ) a)
        (col (mat x τ) b) (I * (X.c τ : ℂ) * (s τ : ℂ)) hα hz
    · have hT : X.flowMat ξ τ (s τ) = 1 + Matrix.replicateCol (Fin 1) (fun a => -((I * (X.c τ : ℂ) * (s τ : ℂ)) * τ.1 (ξ a))) *
          Matrix.replicateRow (Fin 1) (fun b => ∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))) := by
        ext a b
        simp [Data.flowMat, Matrix.mul_apply, Matrix.one_apply] <;> ring
      have h5 : ∑ b, (∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))) * -((I * (X.c τ : ℂ) * (s τ : ℂ)) * τ.1 (ξ b)) = 0 := by
        have h6 : ∑ b, (∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))) * -((I * (X.c τ : ℂ) * (s τ : ℂ)) * τ.1 (ξ b)) =
            -(I * (X.c τ : ℂ) * (s τ : ℂ)) * ∑ b, ∑ k, τ.1 (ξ b) * τ.1 (X.Gm b k) * conj (τ.1 (ξ k)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [h6, hz, mul_zero]
      rw [hT]
      refine (Matrix.det_one_add_replicateCol_mul_replicateRow _ _).trans ?_
      simp only [dotProduct]
      rw [h5, add_zero]
  have hdmin : ∀ τ i, dmin X.Gm (X.flow ξ (fun τ => (s τ : ℂ)) x) τ i = dmin X.Gm x τ i := by
    intro τ i
    unfold dmin
    rw [(hflow τ).1]
  refine ⟨?_, ?_⟩
  · show ∀ τ : X.Ψ, (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.flow ξ (fun τ => (s τ : ℂ)) x) τ i).re
    intro τ
    refine ⟨?_, fun i => ?_⟩
    · show (X.flowMat ξ τ (s τ) * mat x τ).det ≠ 0
      rw [Matrix.det_mul, (hflow τ).2, one_mul]
      exact (hx τ).1
    · rw [hdmin]
      exact (hx τ).2 i
  · unfold Data.nfac
    simp only [hdmin]

theorem fj_bound (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (C : ℝ)
    (hP : ∀ y ∈ X.dom, X.pnorm la P y ≤ C) {ξ : Fin r → E} (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : X.pnorm la (X.fj la ξ ν P) x ≤ C := by
  have hpos := nfac_pos X hx la
  change ‖X.fj la ξ ν P x‖ * X.nfac la x ≤ C
  have hC : 0 ≤ C := le_trans (by unfold Data.pnorm; positivity) (hP x hx)
  unfold Data.fj
  split_ifs with h1 h2
  · obtain ⟨-, -, hD0, hDt⟩ := h2.choose_spec
    rw [← le_div_iff₀ hpos, norm_mul]
    have hpt : ∀ s : X.Ψ → ℝ, ‖P (X.flow ξ (fun τ => (s τ : ℂ)) x) *
        cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)‖ ≤ C / X.nfac la x := by
      intro s
      obtain ⟨hd, hn⟩ := flow_real X hξ hx s la
      rw [norm_mul, norm_cexp_I _ (by rw [Complex.im_sum]; simp), mul_one, le_div_iff₀ hpos, ← hn]
      exact hP _ hd
    haveI : IsFiniteMeasure (volume.restrict h2.choose) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hDt⟩
    have hI := norm_integral_le_of_norm_le_const (μ := volume.restrict h2.choose) (ae_of_all _ hpt)
    rw [measureReal_def, Measure.restrict_apply_univ] at hI
    have hv : 0 < (volume h2.choose).toReal := ENNReal.toReal_pos hD0.ne' hDt.ne
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]
    refine (mul_le_mul_of_nonneg_left hI (inv_nonneg.2 hv.le)).trans (le_of_eq ?_)
    rw [mul_comm (C / X.nfac la x) _, ← mul_assoc, inv_mul_cancel₀ hv.ne', one_mul]
  · simp [hC]
  · simp [hC]

theorem herm_of_LZ {g : ℕ} {b : X.Ψ → Fin 2 → Fin 2 → ℂ} (hb : b ∈ X.LZ g) : IsHermFam b := by
  obtain ⟨β, hβ, -, he⟩ := hb
  intro τ i k
  rw [he]
  simp only [Data.embH]
  rw [← hβ i k, cc, IsCMField.complexEmbedding_complexConj]

theorem herm_sum {n : ℕ} (ω : Fin n → X.Ψ → Fin 2 → Fin 2 → ℂ) (hω : ∀ j, IsHermFam (ω j))
    (t : Fin n → ℝ) : IsHermFam (∑ j, (t j : ℂ) • ω j) := by
  intro τ i k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun j _ => by rw [hω j τ i k]

theorem fz_bound (u : Fin 2 → Fin r → E) (g : ℕ) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ)
    (G : Frame X.Ψ r → ℂ) (la : Wt X.Ψ r) {y : Frame X.Ψ r} (hy : y ∈ X.dom) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ b, IsHermFam b → ‖G (X.Zb u b y)‖ * X.nfac la y ≤ M) :
    X.pnorm la (X.fz u g χ G) y ≤ M := by
  have hpos := nfac_pos X hy la
  change ‖X.fz u g χ G y‖ * X.nfac la y ≤ M
  unfold Data.fz
  split_ifs with h1 h2
  · rw [← le_div_iff₀ hpos]
    have hpt : ∀ t : Fin (4 * Fintype.card X.Ψ) → ℝ, ‖G (X.Zb u (∑ j, (t j : ℂ) • h2.choose j) y) *
        cexp (-(4 * Real.pi * I) * X.pairR χ (∑ j, (t j : ℂ) • h2.choose j))‖ ≤ M / X.nfac la y := by
      intro t
      have hherm : IsHermFam (∑ j, (t j : ℂ) • h2.choose j) :=
        herm_sum X _ (fun j => herm_of_LZ X (h2.choose_spec.1 j)) t
      rw [norm_mul, norm_cexp_I _ (Complex.ofReal_im _), mul_one, le_div_iff₀ hpos]
      exact hb _ hherm
    have hvol : volume (Set.pi Set.univ fun _ : Fin (4 * Fintype.card X.Ψ) => Set.Icc (0 : ℝ) 1) = 1 := by
      rw [volume_pi_pi]
      simp [Real.volume_Icc]
    haveI : IsFiniteMeasure (volume.restrict
        (Set.pi Set.univ fun _ : Fin (4 * Fintype.card X.Ψ) => Set.Icc (0 : ℝ) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
    refine (norm_integral_le_of_norm_le_const (ae_of_all _ hpt)).trans ?_
    rw [measureReal_def, Measure.restrict_apply_univ, hvol]
    simp
  · simp [hM]
  · simp [hM]

end ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SublatticeCoefficients
namespace ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients

open NumberField Complex MeasureTheory ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
  ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing

lemma ioc_orth (m : ℤ) :
    ∫ t in Set.Ioc (0 : ℝ) 1, cexp (2 * Real.pi * I * (m : ℂ) * (t : ℂ)) = if m = 0 then 1 else 0 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hm
  · subst hm; simp
  · have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    have hc : (2 * Real.pi * I * (m : ℂ)) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [this, Complex.I_ne_zero, hm']
    rw [integral_exp_mul_complex hc]
    have h1 : cexp (2 * Real.pi * I * (m : ℂ) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show 2 * (Real.pi : ℂ) * I * (m : ℂ) * ((1 : ℝ) : ℂ) = m * (2 * Real.pi * I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [h1]
    simp

lemma cube_orth {n : ℕ} (m : Fin n → ℤ) :
    ∫ t in Set.univ.pi (fun _ : Fin n => Set.Ioc (0 : ℝ) 1),
      cexp (2 * Real.pi * I * ∑ j, (m j : ℂ) * (t j : ℂ)) = if m = 0 then 1 else 0 := by
  have hprod : ∀ t : Fin n → ℝ, cexp (2 * Real.pi * I * ∑ j, (m j : ℂ) * (t j : ℂ)) =
      ∏ j, cexp (2 * Real.pi * I * (m j : ℂ) * (t j : ℂ)) := by
    intro t
    rw [Finset.mul_sum, Complex.exp_sum]
    exact Finset.prod_congr rfl fun j _ => by ring_nf
  simp_rw [hprod]
  rw [show (volume : Measure (Fin n → ℝ)) = Measure.pi fun _ => volume from rfl,
    Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun (j : Fin n) (t : ℝ) => cexp (2 * Real.pi * I * (m j : ℂ) * (t : ℂ)))]
  simp_rw [ioc_orth]
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg hm]
    obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
      by_contra h; push Not at h; exact hm (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma freq_of_basis {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {n : ℕ}
    (β : Module.Basis (Fin n) ℝ (X.Ψ → ℝ)) (hβ : Submodule.span ℤ (Set.range β) = perL X la)
    (ν : X.Ψ → ℝ) (k : Fin n → ℤ) (hk : ∀ i, 2 * ∑ τ, ν τ * β i τ = k i) :
    ∀ p ∈ X.periods la, ∃ z : ℤ, 2 * ∑ τ, ν τ * p τ = z := by
  intro p hp
  have hp' : p ∈ Submodule.span ℤ (Set.range β) := by rw [hβ]; exact hp
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℤ |>.mp hp'
  refine ⟨∑ j, c j * k j, ?_⟩
  rw [← hc]
  push_cast
  simp only [Finset.sum_apply, Pi.smul_apply]
  simp only [zsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hk j, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

theorem subCoeff {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hP : X.IsSec la P) (ξ : Fin r → E) (hξ : X.IsIso ξ) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) (hωp : ∀ j, ω j ∈ X.periods la)
    (hωi : LinearIndependent ℝ ω) (k : Fin (Fintype.card X.Ψ) → ℤ) (ν : X.Ψ → ℝ)
    (hk : ∀ j, (k j : ℝ) = 2 * ∑ τ, ν τ * ω j τ) :
    fourCoeff (fun t => P (X.flow ξ (fun τ => ∑ j, t j * (ω j τ : ℂ)) x)) 0 k = X.fj la ξ ν P x := by
  classical
  obtain ⟨hξΛ, hξh, hξ0⟩ := hξ
  obtain ⟨β, hβ⟩ := exists_basis X la
  have hβp : ∀ j, β j ∈ X.periods la := fun j => by
    have : β j ∈ Submodule.span ℤ (Set.range β) := Submodule.subset_span ⟨j, rfl⟩
    rw [hβ] at this; exact this
  set a : (Fin (Fintype.card X.Ψ) → ℤ) → ℂ := fun k' => X.fj la ξ (νk β k') P x with ha

  obtain ⟨hΩo, hΩc⟩ := Om_open_convex (ξ := ξ) (⇑β) hx
  have h0 : (0 : Fin (Fintype.card X.Ψ) → ℝ) ∈ Om X ξ x β := zero_mem_Om (⇑β) hξh hx
  have h0t : (0 : Fin (Fintype.card X.Ψ) → ℂ) ∈ tube (Fintype.card X.Ψ) (Om X ξ x β) := by
    show (fun j => ((0 : Fin (Fintype.card X.Ψ) → ℂ) j).im) ∈ Om X ξ x β
    convert h0 using 1
  obtain ⟨hsumβ, -⟩ := tube_expansion _ _ hΩo hΩc h0 (hline_diff X la P ξ x β hP hξh hx)
    (hline_periodic X la P ξ x β hP hξΛ hξh hx hβp) 0 h0t
  have hak : ∀ k', a k' = fourCoeff (hline X P ξ x β) 0 k' := fun k' =>
    fj_eq_fourCoeff X la P hP ⟨hξΛ, hξh, hξ0⟩ hx β hβ (νk β k') k' (νk_spec β k')
  have hsa : Summable (fun k' => ‖a k'‖) := hsumβ.congr fun k' => by
    rw [hak k']; simp

  choose mZ hmZ using fun (k' : Fin (Fintype.card X.Ψ) → ℤ) j =>
    freq_of_basis X la β hβ (νk β k') k' (νk_spec β k') (ω j) (hωp j)

  set sR : (Fin (Fintype.card X.Ψ) → ℝ) → X.Ψ → ℝ := fun t τ => ∑ j, t j * ω j τ with hsR
  have hexp : ∀ t : Fin (Fintype.card X.Ψ) → ℝ, HasSum
      ((fun ν' : X.Ψ → ℝ => X.fj la ξ ν' P x *
        cexp (4 * Real.pi * I * ∑ τ, (ν' τ : ℂ) * ((sR t τ : ℝ) : ℂ))) ∘ νk β)
      (P (X.flow ξ (fun τ => ((sR t τ : ℝ) : ℂ)) x)) := by
    intro t
    have hdom := flow_real_mem_dom X hξh (sR t) x hx
    have hH := m3bExp_holds r X la P hP ξ ⟨hξΛ, hξh, hξ0⟩ x hx _ hdom
    refine (Function.Injective.hasSum_iff (νk_injective β) ?_).mpr hH
    intro ν' hν'
    have hnf : ¬ ∀ p ∈ X.periods la, ∃ z : ℤ, 2 * ∑ τ, ν' τ * p τ = z := by
      intro hfreq
      apply hν'
      choose k0 hk0 using fun j => hfreq (β j) (hβp j)
      exact ⟨k0, (eq_νk β ν' k0 hk0).symm⟩
    rw [Data.fj, if_neg hnf, zero_mul]

  set F : (Fin (Fintype.card X.Ψ) → ℤ) → (Fin (Fintype.card X.Ψ) → ℝ) → ℂ := fun k' t =>
    a k' * cexp (2 * Real.pi * I * ∑ j, ((mZ k' j - k j : ℤ) : ℂ) * (t j : ℂ)) with hF
  have hexpF : ∀ k' t, ((fun ν' : X.Ψ → ℝ => X.fj la ξ ν' P x *
      cexp (4 * Real.pi * I * ∑ τ, (ν' τ : ℂ) * ((sR t τ : ℝ) : ℂ))) ∘ νk β) k' *
      cexp (-2 * Real.pi * I * ∑ j, (k j : ℂ) * ((t j : ℂ) + ((0 : Fin (Fintype.card X.Ψ) → ℝ) j : ℂ) * I)) =
      F k' t := by
    intro k' t
    simp only [Function.comp_apply, hF, ha, Pi.zero_apply, Complex.ofReal_zero, zero_mul, add_zero]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    have hpair : ∀ j, ∑ τ, ((νk β k' τ : ℝ) : ℂ) * (ω j τ : ℂ) = (mZ k' j : ℂ) / 2 := by
      intro j
      have h2 : ((2 * ∑ τ, νk β k' τ * ω j τ : ℝ) : ℂ) = (mZ k' j : ℂ) := by rw [hmZ k' j]; simp
      push_cast at h2
      linear_combination h2 / 2
    have hsum : ∑ τ, ((νk β k' τ : ℝ) : ℂ) * ((sR t τ : ℝ) : ℂ) =
        (∑ j, (mZ k' j : ℂ) * (t j : ℂ)) / 2 := by
      simp only [hsR]
      push_cast
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      calc ∑ τ, ((νk β k' τ : ℝ) : ℂ) * ((t j : ℂ) * (ω j τ : ℂ))
          = (t j : ℂ) * ∑ τ, ((νk β k' τ : ℝ) : ℂ) * (ω j τ : ℂ) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => by ring
        _ = (mZ k' j : ℂ) * (t j : ℂ) / 2 := by rw [hpair j]; ring
    rw [hsum]
    push_cast
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hint : ∀ t ∈ Set.univ.pi (fun _ : Fin (Fintype.card X.Ψ) => Set.Ioc (0 : ℝ) 1),
      (fun t => P (X.flow ξ (fun τ => ∑ j, t j * (ω j τ : ℂ)) x))
        (fun j => (t j : ℂ) + ((0 : Fin (Fintype.card X.Ψ) → ℝ) j : ℂ) * I) *
      cexp (-2 * Real.pi * I *
        ∑ j, (k j : ℂ) * ((t j : ℂ) + ((0 : Fin (Fintype.card X.Ψ) → ℝ) j : ℂ) * I)) =
      ∑' k', F k' t := by
    intro t _
    have harg : X.flow ξ (fun τ => ∑ j, ((t j : ℂ) + ((0 : Fin (Fintype.card X.Ψ) → ℝ) j : ℂ) * I) *
        (ω j τ : ℂ)) x = X.flow ξ (fun τ => ((sR t τ : ℝ) : ℂ)) x := by
      congr 1
      funext τ
      simp [hsR]
    dsimp only
    rw [harg, ← (hexp t).tsum_eq, ← tsum_mul_right]
    exact tsum_congr fun k' => hexpF k' t
  unfold fourCoeff
  rw [setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) hint]
  have hnormF : ∀ k' t, ‖F k' t‖ = ‖a k'‖ := by
    intro k' t
    simp only [hF, norm_mul]
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      norm_exp_real_I (2 * Real.pi) (fun j => mZ k' j - k j) t, mul_one]
  have hvol : volume (Set.univ.pi fun _ : Fin (Fintype.card X.Ψ) => Set.Ioc (0 : ℝ) 1) = 1 := by
    rw [Real.volume_pi_Ioc]; simp
  have hFint : ∀ k', IntegrableOn (F k') (Set.univ.pi fun _ => Set.Ioc (0 : ℝ) 1) := by
    intro k'
    refine Measure.integrableOn_of_bounded (M := ‖a k'‖) (by rw [hvol]; exact ENNReal.one_ne_top)
      ?_ (Filter.Eventually.of_forall fun t => (hnormF k' t).le)
    refine Continuous.aestronglyMeasurable ?_
    simp only [hF]
    fun_prop
  have hFsum : Summable fun k' => ∫ t in Set.univ.pi (fun _ => Set.Ioc (0 : ℝ) 1), ‖F k' t‖ := by
    refine hsa.congr fun k' => ?_
    simp_rw [hnormF]
    rw [setIntegral_const, measureReal_def, hvol]; simp
  rw [← integral_tsum_of_summable_integral_norm hFint hFsum]
  have hcoef : ∀ k', ∫ t in Set.univ.pi (fun _ => Set.Ioc (0 : ℝ) 1), F k' t =
      a k' * (if (fun j => mZ k' j - k j) = 0 then 1 else 0) := by
    intro k'
    simp only [hF]
    rw [integral_const_mul]
    rw [cube_orth (fun j => mZ k' j - k j)]
  simp_rw [hcoef]
  have hcard : Fintype.card (Fin (Fintype.card X.Ψ)) = Module.finrank ℝ (X.Ψ → ℝ) := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hΨ : Nonempty X.Ψ := by
    obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : τ0 ∈ X.Ψ
    · exact ⟨⟨τ0, h⟩⟩
    · exact ⟨⟨_, by_contra fun hc => h ((X.cmType τ0).mpr hc)⟩⟩
  have : Nonempty (Fin (Fintype.card X.Ψ)) := Fin.pos_iff_nonempty.mp Fintype.card_pos
  set ωB := basisOfLinearIndependentOfCardEqFinrank hωi hcard with hωBdef
  have hωB : ∀ j, ωB j = ω j := fun j => by simp [hωBdef]
  have hsame : ∀ k', (fun j => mZ k' j - k j) = 0 → νk β k' = ν := by
    intro k' h
    have hm : ∀ j, mZ k' j = k j := fun j => by
      have := congrFun h j; simp only [Pi.zero_apply] at this; omega
    have e1 : νk β k' = νk ωB k := eq_νk ωB (νk β k') k (fun j => by
      rw [hωB, hmZ k' j, hm j])
    have e2 : ν = νk ωB k := eq_νk ωB ν k (fun j => by rw [hωB]; exact (hk j).symm)
    rw [e1, ← e2]
  by_cases hfreq : ∀ p ∈ X.periods la, ∃ z : ℤ, 2 * ∑ τ, ν τ * p τ = z
  · choose k0 hk0 using fun j => hfreq (β j) (hβp j)
    have hν0 : ν = νk β k0 := eq_νk β ν k0 hk0
    have huniq : ∀ k', (fun j => mZ k' j - k j) = 0 → k' = k0 := fun k' h =>
      νk_injective β (by rw [hsame k' h, hν0])
    have hk0z : (fun j => mZ k0 j - k j) = 0 := by
      funext j
      have h1 : (mZ k0 j : ℝ) = k j := by rw [← hmZ k0 j, ← hν0, hk j]
      have h2 : mZ k0 j = k j := by exact_mod_cast h1
      simp only [Pi.zero_apply]
      omega
    rw [tsum_eq_single k0 (fun k' hk' => by rw [if_neg (fun h => hk' (huniq k' h)), mul_zero]),
      if_pos hk0z, mul_one, ha]
    show X.fj la ξ (νk β k0) P x = _
    rw [← hν0]
  · have hz : X.fj la ξ ν P x = 0 := by rw [Data.fj, if_neg hfreq]
    rw [hz]
    have hterm : ∀ k', a k' * (if (fun j => mZ k' j - k j) = 0 then (1 : ℂ) else 0) = 0 := by
      intro k'
      rw [if_neg, mul_zero]
      intro h
      apply hfreq
      rw [← hsame k' h]
      exact freq_of_basis X la β hβ (νk β k') k' (νk_spec β k')
    simp only [hterm, tsum_zero]

end ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients
end
