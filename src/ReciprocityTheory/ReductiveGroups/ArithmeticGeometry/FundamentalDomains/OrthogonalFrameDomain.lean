module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LogDOfPosBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicIndexSums

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

private lemma sum_castLE_lemma {r k : ℕ} (hk : k ≤ r) (f : Fin r → ℂ)
    (hf : ∀ j : Fin r, k ≤ (j : ℕ) → f j = 0) : ∑ j, f j = ∑ j : Fin k, f (Fin.castLE hk j) := by
  have hr : r = k + (r - k) := (Nat.add_sub_cancel' hk).symm
  rw [← Equiv.sum_comp (finCongr hr.symm), Fin.sum_univ_add]
  have h2 : ∑ a : Fin (r - k), f (finCongr hr.symm (Fin.natAdd k a)) = 0 :=
    Finset.sum_eq_zero fun a _ => hf _ (by simp)
  rw [h2, add_zero]
  exact Finset.sum_congr rfl fun j _ => congrArg f (Fin.ext (by simp))

lemma rmul_mem_dom {z b : Frame X.Ψ r} (hz : z ∈ X.dom) (hb : b ∈ Bor X.Ψ r) : rmul z b ∈ X.dom := by
  intro τ
  obtain ⟨hz1, hz2⟩ := hz τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hmat : mat (rmul z b) τ = mat z τ * mat b τ := rfl
  have hgram : ∀ M : Matrix (Fin r) (Fin r) ℂ,
      gram τ.1 X.Gm M = Mᵀ * X.Gm.map τ.1 * M.map (starRingEnd ℂ) := by
    intro M
    ext a c
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hprod : gram τ.1 X.Gm (mat z τ * mat b τ) =
      (mat b τ)ᵀ * gram τ.1 X.Gm (mat z τ) * (mat b τ).map (starRingEnd ℂ) := by
    rw [hgram, hgram, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have htri : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ), (∀ a c : Fin n, c < a → M a c = 0) →
      M.det = ∏ a, M a a :=
    fun n M h => Matrix.det_of_upperTriangular (fun a c hca => h a c hca)
  have hdiag : ∀ a, mat b τ a a ≠ 0 := by
    have h0 := hb1
    rw [htri r (mat b τ) hb2] at h0
    exact fun a => Finset.prod_ne_zero_iff.mp h0 a (Finset.mem_univ a)
  refine ⟨by rw [hmat, Matrix.det_mul]; exact mul_ne_zero hz1 hb1, fun i => ?_⟩
  have hk : (i : ℕ) ≤ r := Nat.le_of_lt_succ i.isLt
  have hsub : ((mat b τ)ᵀ * gram τ.1 X.Gm (mat z τ) * (mat b τ).map (starRingEnd ℂ)).submatrix
        (Fin.castLE hk) (Fin.castLE hk) =
      ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk))ᵀ *
        (gram τ.1 X.Gm (mat z τ)).submatrix (Fin.castLE hk) (Fin.castLE hk) *
        ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).map (starRingEnd ℂ) := by
    ext a c
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    refine (sum_castLE_lemma hk _ ?_).trans (Finset.sum_congr rfl fun l _ => ?_)
    · intro l hl
      have hc := c.isLt
      have h0 : mat b τ l (Fin.castLE hk c) = 0 :=
        hb2 l (Fin.castLE hk c) (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE]; omega)
      exact mul_eq_zero_of_right _ ((map_eq_zero _).mpr h0)
    · refine congrArg (fun s => s * _) (sum_castLE_lemma hk _ ?_)
      intro j hj
      have ha := a.isLt
      have h0 : mat b τ j (Fin.castLE hk a) = 0 :=
        hb2 j (Fin.castLE hk a) (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE]; omega)
      exact mul_eq_zero_of_left h0 _
  set d := ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det with hd
  have hdne : d ≠ 0 := by
    rw [hd, htri (i : ℕ) ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk))
      (fun a c h => hb2 _ _ (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE, Fin.coe_castLE]; exact h))]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hdiag (Fin.castLE hk a)
  have hdetmap : (((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).map (starRingEnd ℂ)).det =
      starRingEnd ℂ d := by
    rw [hd, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hclaim : dmin X.Gm (rmul z b) τ i = ((Complex.normSq d : ℝ) : ℂ) * dmin X.Gm z τ i := by
    unfold dmin lminor
    rw [hmat, hprod, hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetmap, ← hd,
      mul_right_comm, Complex.mul_conj]
  rw [hclaim, Complex.re_ofReal_mul]
  have hpos : 0 < Complex.normSq d := Complex.normSq_pos.mpr hdne
  calc (0 : ℝ) < Complex.normSq d * (psgn X.p0 i * (dmin X.Gm z τ i).re) := mul_pos hpos (hz2 i)
    _ = _ := by ring

lemma opN_smul_le {m n : ℕ} (t : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) :
    Data.opN (t • A) ≤ ‖t‖ * Data.opN A := by
  unfold Data.opN
  have key : ∀ v : Fin n → ℂ,
      Real.sqrt (∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2) =
        ‖t‖ * (Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)) := by
    intro v
    have h1 : ∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2 = ‖t‖ ^ 2 * ∑ i, ‖Matrix.mulVec A v i‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hmv : Matrix.mulVec (t • A) v i = t * Matrix.mulVec A v i := by
        simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
      rw [hmv, norm_mul, mul_pow]
    rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg t), mul_div_assoc]
  open scoped Pointwise in
  have hS : {s | ∃ v : Fin n → ℂ, v ≠ 0 ∧
        s = Real.sqrt (∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} =
      ‖t‖ • {s | ∃ v : Fin n → ℂ, v ≠ 0 ∧
        s = Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} := by
    ext s
    simp only [Set.mem_smul_set, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨_, ⟨v, hv, rfl⟩, ?_⟩
      rw [smul_eq_mul, key v]
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, by rw [smul_eq_mul, key v]⟩
  refine le_of_eq ?_
  rw [hS, Real.sSup_smul_of_nonneg (norm_nonneg t), smul_eq_mul]

private lemma opN_nonneg' {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : 0 ≤ Data.opN A := by
  unfold Data.opN
  apply Real.sSup_nonneg
  rintro s ⟨v, _, rfl⟩
  positivity

lemma zN_nonneg (Z : X.Coord) : 0 ≤ X.zN Z := by
  unfold Data.zN
  exact Real.iSup_nonneg fun τ => opN_nonneg' _

lemma zN_smul_le (t : ℂ) (Z : X.Coord) : X.zN (t • Z) ≤ ‖t‖ * X.zN Z := by
  unfold Data.zN
  refine Real.iSup_le (fun τ => ?_) (mul_nonneg (norm_nonneg t) (zN_nonneg X Z))
  have h1 : Data.opN (Matrix.of ((t • Z) τ)) ≤ ‖t‖ * Data.opN (Matrix.of (Z τ)) :=
    opN_smul_le t (Matrix.of (Z τ))
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg t))
  exact le_ciSup (f := fun τ : X.Ψ => Data.opN (Matrix.of (Z τ))) (Set.finite_range _).bddAbove τ

lemma xZ_diff (x : Frame X.Ψ r) : Differentiable ℂ fun Z : X.Coord => X.xZ x Z := by
  rw [differentiable_pi]
  intro τ
  rw [differentiable_pi]
  intro a
  rw [differentiable_pi]
  intro b
  have hL : ∀ j, Differentiable ℂ fun Z : X.Coord => X.lowBlock Z τ j b := by
    intro j
    simp only [Data.lowBlock, Matrix.of_apply]
    split_ifs <;> fun_prop
  show Differentiable ℂ fun Z : X.Coord => ∑ j, mat x τ a j * X.lowBlock Z τ j b
  first
    | exact Differentiable.fun_sum (fun j _ => (hL j).const_mul _)
    | exact Differentiable.sum (fun j _ => (hL j).const_mul _)

lemma xZ_zero (x : Frame X.Ψ r) : X.xZ x 0 = x := by
  funext τ
  have h1 : X.lowBlock 0 τ = 1 := by
    ext a b
    simp [Data.lowBlock, Matrix.one_apply]
  show mat x τ * X.lowBlock 0 τ = x τ
  rw [h1, Matrix.mul_one]
  rfl

lemma exp_small : Real.exp (1 / 25) < 3 / 2 := by
  by_contra hcon
  push_neg at hcon
  have h25 : Real.exp 1 = Real.exp (1 / 25) ^ 25 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpow : (3 / 2 : ℝ) ^ 25 ≤ Real.exp (1 / 25) ^ 25 := pow_le_pow_left₀ (by norm_num) hcon 25
  have he := Real.exp_one_lt_d9
  norm_num at hpow
  linarith

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCombinations
namespace ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Herm

variable {n : ℕ} (G : Matrix (Fin r) (Fin r) E)

def hermLin (y : Fin r → E) : (Fin r → E) →ₗ[E] E where
  toFun x := herm G x y
  map_add' x x' := by simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [herm, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

lemma herm_sum_smul (c : Fin n → E) (β : Fin n → Fin r → E) (y : Fin r → E) :
    herm G (∑ k, c k • β k) y = ∑ k, c k * herm G (β k) y := by
  have h := map_sum (hermLin G y) (fun k => c k • β k) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

lemma herm_add_smul (x ξ y : Fin r → E) (e : E) : herm G (x + e • ξ) y = herm G x y + e * herm G ξ y := by
  have h := map_add (hermLin G y) x (e • ξ)
  rw [map_smul, smul_eq_mul] at h
  exact h

variable {G} (hG : ∀ a b, cc (G a b) = G b a) {ξ : Fin r → E} {β : Fin n → Fin r → E}
  (hβ : ∀ k, herm G (β k) ξ = 0) (hξξ : herm G ξ ξ = 0)

include hβ in
lemma herm_B_ξ (c : Fin n → E) : herm G (∑ k, c k • β k) ξ = 0 := by
  rw [herm_sum_smul]
  simp [hβ]

include hβ hξξ in
lemma herm_lam_ξ (c : Fin n → E) (e : E) : herm G (∑ k, c k • β k + e • ξ) ξ = 0 := by
  rw [herm_add_smul, herm_B_ξ hβ, hξξ]
  ring

include hG hβ hξξ in
lemma herm_lam_lam (c c' : Fin n → E) (e e' : E) :
    herm G (∑ k, c k • β k + e • ξ) (∑ k, c' k • β k + e' • ξ) =
      herm G (∑ k, c k • β k) (∑ k, c' k • β k) := by
  have hadd : ∀ x y y' : Fin r → E, herm G x (y + y') = herm G x y + herm G x y' := by
    intro x y y'
    simp only [herm, Pi.add_apply, cc, map_add (f := _), mul_add, Finset.sum_add_distrib]
  have hsm : ∀ (x y : Fin r → E) (a : E), herm G x (a • y) = cc a * herm G x y := by
    intro x y a
    simp only [herm, Pi.smul_apply, smul_eq_mul, cc, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hswap : ∀ x y : Fin r → E, herm G y x = cc (herm G x y) := by
    intro x y
    have hmap : ∀ s : Finset (Fin r), ∀ f : Fin r → E, cc (∑ i ∈ s, f i) = ∑ i ∈ s, cc (f i) :=
      fun s f => by simp only [cc, map_sum]
    have hmul : ∀ a b : E, cc (a * b) = cc a * cc b := fun a b => by simp only [cc, map_mul]
    simp only [herm, hmap, hmul, cc_cc, hG]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hξβ : ∀ k, herm G ξ (β k) = 0 := fun k => by
    rw [hswap, hβ k]
    simp only [cc, map_zero]
  have hξB : herm G ξ (∑ k, c' k • β k) = 0 := by
    have hs : ∀ (s : Finset (Fin n)), herm G ξ (∑ k ∈ s, c' k • β k) = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty, herm, Pi.zero_apply, cc, map_zero, mul_zero, Finset.sum_const_zero]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, hadd, hsm, hξβ, ih]
        ring
    exact hs _
  rw [herm_add_smul, hadd, hadd, hsm, hsm, herm_B_ξ hβ, hξξ, hξB]
  ring

lemma ne_smul_ξ (hli : LinearIndependent E (Fin.cons ξ β : Fin (n + 1) → Fin r → E))
    {c : Fin n → E} (hc : c ≠ 0) (e e' : E) : ∑ k, c k • β k + e • ξ ≠ e' • ξ := by
  intro h
  rw [Fintype.linearIndependent_iff] at hli
  have h0 := hli (Fin.cons (e - e') c) (by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, sub_smul]
    rw [← sub_eq_zero] at h
    rw [← h]
    abel)
  exact hc (funext fun k => by simpa using h0 k.succ)

lemma cons_li (hli : LinearIndependent E (Fin.cons ξ β : Fin (n + 1) → Fin r → E))
    {la : Fin n → Fin n → E} (hla : LinearIndependent E la) (e : Fin n → E) :
    LinearIndependent E (Fin.cons ξ (fun j => ∑ k, la j k • β k + e j • ξ) :
      Fin (n + 1) → Fin r → E) := by
  rw [Fintype.linearIndependent_iff] at hli hla ⊢
  intro g hg
  rw [Fin.sum_univ_succ] at hg
  simp only [Fin.cons_zero, Fin.cons_succ] at hg
  have key := hli (Fin.cons (g 0 + ∑ j, g j.succ * e j) (fun k => ∑ j, g j.succ * la j k)) (by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hg]
    simp only [smul_add, Finset.smul_sum, smul_smul, add_smul, Finset.sum_smul,
      Finset.sum_add_distrib]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun x y => (g y.succ * la y x) • β x)]
    abel)
  have hs : ∀ j : Fin n, g j.succ = 0 := by
    refine hla (fun j => g j.succ) ?_
    funext k
    have := key k.succ
    simp only [Fin.cons_succ] at this
    simpa [Finset.sum_apply, smul_eq_mul] using this
  have h0 : g 0 = 0 := by
    have := key 0
    simpa [hs] using this
  intro i
  refine Fin.cases h0 (fun j => hs j) i

end Herm

lemma hC_comb2_ortho (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n p : ℕ} (f : Fin n → Fin r → ℂ)
    (hf : ∀ k l, hermC τ G (f k) (f l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
    (b c : Fin n → ℂ) :
    hermC τ G (∑ k, b k • f k) (∑ l, c l • f l) = ReciprocityTheory.MultiplicativeHeights.jForm p c b := by
  have h1 : ∀ (w : Fin n → ℂ) (v : Fin r → ℂ),
      hermC τ G (∑ k, w k • f k) v = ∑ k, w k * hermC τ G (f k) v := by
    intro w v
    simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have h2 : ∀ (w : Fin n → ℂ) (u : Fin r → ℂ),
      hermC τ G u (∑ l, w l • f l) = ∑ l, conj (w l) * hermC τ G u (f l) := by
    intro w u
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
      Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h1]
  simp_rw [h2, hf, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold ReciprocityTheory.MultiplicativeHeights.jForm ReciprocityTheory.MultiplicativeHeights.sgn
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

lemma comb_swap {m n : ℕ} (w : Fin n → ℂ) (y : Fin n → Fin m → ℂ) (f : Fin m → Fin r → ℂ) :
    ∑ j, w j • ∑ k, y j k • f k = ∑ k, (∑ j, w j * y j k) • f k := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

lemma qcomb {m n : ℕ} (Q : Matrix (Fin m) (Fin m) ℂ) (w : Fin n → ℂ) (a : Fin n → Fin m → ℂ)
    (k : Fin m) : (Q *ᵥ ∑ j, w j • a j) k = ∑ j, w j * (Q *ᵥ a j) k := by
  have h := map_sum (Matrix.mulVecLin Q) (fun j => w j • a j) Finset.univ
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_smul] at h
  rw [h]
  simp [Finset.sum_apply]

lemma la_bound {T μ x : ℝ} (hT : 1 ≤ T) (hμ : 2 * μ ^ 2 ≤ T ^ 2) {p0 : ℕ} (hp0 : 1 ≤ p0)
    (hx : x ≤ T ^ 2 ∨ x ≤ T ^ (4 * (p0 - 1)) * (2 * μ ^ 2)) : x ≤ (T ^ (2 * p0 - 1)) ^ 2 := by
  have he : (T ^ (2 * p0 - 1)) ^ 2 = T ^ (4 * (p0 - 1)) * T ^ 2 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [he]
  have h1 : 1 ≤ T ^ (4 * (p0 - 1)) := one_le_pow₀ hT
  rcases hx with hx | hx
  · calc x ≤ T ^ 2 := hx
      _ = 1 * T ^ 2 := by ring
      _ ≤ T ^ (4 * (p0 - 1)) * T ^ 2 := by gcongr
  · calc x ≤ T ^ (4 * (p0 - 1)) * (2 * μ ^ 2) := hx
      _ ≤ T ^ (4 * (p0 - 1)) * T ^ 2 := by gcongr

end

end ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations
end
