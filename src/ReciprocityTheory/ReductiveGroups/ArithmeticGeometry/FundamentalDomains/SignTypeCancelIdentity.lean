module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DiscreteLatticeMinimum

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SignTypeCancelIdentity
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PosDefOfBound
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder

noncomputable section

lemma dot_self {n : ℕ} (y : Fin n → ℂ) : star y ⬝ᵥ y = ((nsq y : ℝ) : ℂ) := by
  simp only [nsq, dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Complex.conj_mul' (y i)

lemma quad_AtA {n q : ℕ} (A : Matrix (Fin q) (Fin n) ℂ) (y : Fin n → ℂ) :
    star y ⬝ᵥ ((Aᵀ * A.map (starRingEnd ℂ)) *ᵥ y) = ((nsq (A.map (starRingEnd ℂ) *ᵥ y) : ℝ) : ℂ) := by
  have h : A *ᵥ star y = star (A.map (starRingEnd ℂ) *ᵥ y) := by
    funext i
    simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h, dot_self]

lemma posDef_of_bound {n q k : ℕ} (A : Matrix (Fin q) (Fin n) ℂ) (B : Matrix (Fin k) (Fin n) ℂ) {s : ℝ}
    (hs : s < 1) (hA : ∀ y, nsq (A.map (starRingEnd ℂ) *ᵥ y) ≤ s ^ 2 * nsq y) (hs0 : 0 ≤ s) :
    (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).PosDef := by
  have hH : (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).IsHermitian := by
    have h1 : ∀ {m : ℕ} (C : Matrix (Fin m) (Fin n) ℂ), (Cᵀ * C.map (starRingEnd ℂ)).IsHermitian := by
      intro m C
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.mul_apply, star_sum, mul_comm]
    exact ((Matrix.isHermitian_one.sub (h1 A)).add (h1 B))
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_sub,
    dot_self, quad_AtA, quad_AtA]
  have hpos : 0 < nsq x := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    change x i ≠ 0 at hi
    have : 0 < ‖x i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i))
  have hB := nsq_nonneg (B.map (starRingEnd ℂ) *ᵥ x)
  have hA' := hA x
  have hs2 : s ^ 2 < 1 := by nlinarith
  have key : 0 < nsq x - nsq (A.map (starRingEnd ℂ) *ᵥ x) + nsq (B.map (starRingEnd ℂ) *ᵥ x) := by
    nlinarith
  have : ((nsq x - nsq (A.map (starRingEnd ℂ) *ᵥ x) + nsq (B.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) =
      ((nsq x : ℝ) : ℂ) - ((nsq (A.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) +
        ((nsq (B.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) := by push_cast; ring
  rw [← this]
  exact_mod_cast key

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma bound_castLE {n : ℕ} (h : n ≤ X.p0) (Z : X.Coord) (τ : X.Ψ) (y : Fin n → ℂ) :
    nsq ((Matrix.of fun (m : Fin (r - X.p0)) (b : Fin n) => Z τ m (Fin.castLE h b)).map (starRingEnd ℂ) *ᵥ y) ≤
      X.zN Z ^ 2 * nsq y := by
  classical
  set z : Fin X.p0 → ℂ := fun c => if h' : (c : ℕ) < n then y ⟨c, h'⟩ else 0 with hz
  have hinj : Function.Injective (Fin.castLE h) := Fin.castLE_injective h
  have hzc : ∀ b : Fin n, z (Fin.castLE h b) = y b := by
    intro b
    simp [hz, b.isLt]
  have hz0 : ∀ c ∉ Set.range (Fin.castLE h), z c = 0 := by
    intro c hc
    simp only [hz]
    rw [dite_eq_right]
    intro hcn
    exact hc ⟨⟨c, hcn⟩, Fin.ext rfl⟩
  have hvec : ((Matrix.of fun (m : Fin (r - X.p0)) (b : Fin n) => Z τ m (Fin.castLE h b)).map (starRingEnd ℂ) *ᵥ y) =
      (Matrix.of (Z τ)).map (starRingEnd ℂ) *ᵥ z := by
    funext m
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply]
    refine Fintype.sum_of_injective (M := ℂ) (Fin.castLE h) hinj _ _ ?_ ?_
    · intro c hc
      simp [hz0 c hc]
    · intro b
      simp [hzc b]
  have hnz : nsq z = nsq y := by
    unfold nsq
    exact (Fintype.sum_of_injective (M := ℝ) (Fin.castLE h) hinj _ _ (fun c hc => by simp [hz0 c hc])
      (fun b => by simp [hzc b])).symm
  have hconj : ∀ {q : ℕ} (w : Fin q → ℂ), nsq (fun m => conj (w m)) = nsq w := by
    intro q w
    unfold nsq
    simp
  have hmap : ∀ w : Fin X.p0 → ℂ, nsq ((Matrix.of (Z τ)).map (starRingEnd ℂ) *ᵥ w) =
      nsq (Matrix.of (Z τ) *ᵥ fun c => conj (w c)) := by
    intro w
    rw [← hconj (Matrix.of (Z τ) *ᵥ fun c => conj (w c))]
    congr 1
    funext m
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum]
  have hop0 : 0 ≤ Data.opN (Matrix.of (Z τ)) := by
    unfold Data.opN
    apply Real.sSup_nonneg
    rintro t ⟨v, -, rfl⟩
    positivity
  have hop : Data.opN (Matrix.of (Z τ)) ≤ X.zN Z := by
    unfold Data.zN
    exact le_ciSup (f := fun τ => Data.opN (Matrix.of (Z τ))) (Set.finite_range _).bddAbove τ
  rw [hvec, hmap, ← hnz, ← hconj z]
  calc nsq (Matrix.of (Z τ) *ᵥ fun c => conj (z c))
      ≤ Data.opN (Matrix.of (Z τ)) ^ 2 * nsq (fun c => conj (z c)) := nsq_mulVec_le_opN _ _
    _ ≤ X.zN Z ^ 2 * nsq (fun c => conj (z c)) := by
      gcongr
      exact nsq_nonneg _

lemma det_lowBlock (Z : X.Coord) (τ : X.Ψ) : (X.lowBlock Z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro a _
    simp only [Data.lowBlock, Matrix.of_apply, if_true]
    rw [dite_eq_right (by omega)]
    simp
  · intro a b hab
    have hab' : a < b := hab
    simp only [Data.lowBlock, Matrix.of_apply]
    rw [if_neg (ne_of_lt hab'), dite_eq_right]
    · simp
    · intro hh
      have : (a : ℕ) < b := hab'
      omega

lemma psgn_add (p0 k : ℕ) : psgn p0 (p0 + k) = (-1) ^ k := by
  induction k with
  | zero => simp [psgn_eq_one le_rfl]
  | succ k ih =>
    rw [← add_assoc, psgn_succ, ih, sgn, if_neg (by omega), pow_succ]

lemma signType_cancel_identity (k : ℕ) (D : ℂ) (hD : 0 < D.re) : 0 < (-1 : ℝ) ^ k * (((-1 : ℂ) ^ k) * D).re := by
  have h1 : ((-1 : ℂ) ^ k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, Complex.re_ofReal_mul, ← mul_assoc, ← mul_pow]
  norm_num
  exact hD

lemma pos_re_of_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) : 0 < M.det.re := by
  exact (Complex.pos_iff.mp hM.det_pos).1

lemma minor_le {x : Frame X.Ψ r} (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1) (τ : X.Ψ)
    (i : Fin (r + 1)) (hip : (i : ℕ) ≤ X.p0) : 0 < psgn X.p0 i * (dmin X.Gm (X.xZ x Z) τ i).re := by
  classical
  rw [psgn_eq_one hip, one_mul]
  set A : Matrix (Fin (r - X.p0)) (Fin (i : ℕ)) ℂ :=
    Matrix.of fun m b => Z τ m (Fin.castLE hip b) with hA
  set B : Matrix (Fin 0) (Fin (i : ℕ)) ℂ := 0 with hB
  have hs0 : 0 ≤ X.zN Z := by
    unfold Data.zN
    apply Real.iSup_nonneg
    intro τ'
    unfold Data.opN
    apply Real.sSup_nonneg
    rintro t ⟨v, -, rfl⟩
    positivity
  have hpd := posDef_of_bound A B hZ (bound_castLE X hip Z τ) hs0
  have heq : dmin X.Gm (X.xZ x Z) τ i = (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).det := by
    unfold dmin lminor
    rw [gram_xZ X ho Z τ]
    congr 1
    ext a b
    have hca : (Fin.castLE (Nat.le_of_lt_succ i.isLt) a : Fin r) = Fin.castLE X.p0_le (Fin.castLE hip a) :=
      Fin.ext rfl
    have hcb : (Fin.castLE (Nat.le_of_lt_succ i.isLt) b : Fin r) = Fin.castLE X.p0_le (Fin.castLE hip b) :=
      Fin.ext rfl
    rw [Matrix.submatrix_apply, hca, hcb, Gp_pp]
    simp [hA, hB, Matrix.one_apply, Matrix.mul_apply, Fin.castLE_inj]
  rw [heq]
  exact pos_re_of_posDef hpd

lemma minor_gt {x : Frame X.Ψ r} (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1) (τ : X.Ψ)
    (k : ℕ) (hk : k ≤ r - X.p0) (i : Fin (r + 1)) (hik : (i : ℕ) = X.p0 + k) :
    0 < psgn X.p0 i * (dmin X.Gm (X.xZ x Z) τ i).re := by
  classical
  obtain ⟨i, hi⟩ := i
  simp only at hik
  subst hik
  rw [show ((⟨X.p0 + k, hi⟩ : Fin (r + 1)) : ℕ) = X.p0 + k from rfl, psgn_add]
  set A : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ :=
    Matrix.of fun m b => Z τ m (Fin.castLE (le_refl X.p0) b) with hA
  set B : Matrix (Fin k) (Fin X.p0) ℂ := Matrix.of fun m c => Z τ (Fin.castLE hk m) c with hB
  have hs0 : 0 ≤ X.zN Z := by
    unfold Data.zN
    apply Real.iSup_nonneg
    intro τ'
    unfold Data.opN
    apply Real.sSup_nonneg
    rintro t ⟨v, -, rfl⟩
    positivity
  have hpd := posDef_of_bound A B hZ (bound_castLE X (le_refl X.p0) Z τ) hs0
  haveI : Invertible (1 : Matrix (Fin k) (Fin k) ℂ) := invertibleOne
  haveI : Invertible (-1 : Matrix (Fin k) (Fin k) ℂ) := invertibleNeg 1
  have heq : dmin X.Gm (X.xZ x Z) τ ⟨X.p0 + k, hi⟩ =
      (-1 : ℂ) ^ k * (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).det := by
    unfold dmin lminor
    rw [gram_xZ X ho Z τ, ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
    have hc1 : ∀ a : Fin X.p0, (Fin.castLE (Nat.le_of_lt_succ hi) (finSumFinEquiv (Sum.inl a)) : Fin r) =
        Fin.castLE X.p0_le a := fun a => Fin.ext (by simp)
    have hc2 : ∀ m : Fin k, (Fin.castLE (Nat.le_of_lt_succ hi) (finSumFinEquiv (Sum.inr m)) : Fin r) =
        nI X (Fin.castLE hk m) := fun m => Fin.ext (by simp [nI])
    have hblk : ((Gp X Z τ).submatrix (Fin.castLE (Nat.le_of_lt_succ hi)) (Fin.castLE (Nat.le_of_lt_succ hi))).submatrix
        finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks (1 - Aᵀ * A.map (starRingEnd ℂ)) (-Bᵀ) (-(B.map (starRingEnd ℂ))) (-1) := by
      ext (a | m) (b | m')
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, Gp_pp, Matrix.fromBlocks_apply₁₁]
        simp [hA, Matrix.one_apply, Matrix.mul_apply]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, hc2, Gp_pn, Matrix.fromBlocks_apply₁₂]
        simp [hB]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, hc2, Gp_np, Matrix.fromBlocks_apply₂₁]
        simp [hB]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc2, Gp_nn, Matrix.fromBlocks_apply₂₂]
        simp [Matrix.one_apply, Fin.castLE_inj]
    rw [hblk, Matrix.det_fromBlocks₂₂, invOf_neg, invOf_one, Matrix.det_neg, Matrix.det_one, Fintype.card_fin,
      mul_one]
    congr 2
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg, sub_neg_eq_add]
  rw [heq]
  exact signType_cancel_identity k _ (pos_re_of_posDef hpd)

theorem xZ_mem_dom {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1) :
    X.xZ x Z ∈ X.dom := by
  rw [Data.mem_dom_iff] at hx ⊢
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · show (mat x τ * X.lowBlock Z τ).det ≠ 0
    rw [Matrix.det_mul, det_lowBlock, mul_one]
    exact (hx τ).1
  · by_cases hip : (i : ℕ) ≤ X.p0
    · exact minor_le X ho hZ τ i hip
    · have hi := i.isLt
      have := X.p0_le
      exact minor_gt X ho hZ τ ((i : ℕ) - X.p0) (by omega) i (by omega)

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FinrankRieszBounds
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace FinrankRieszBounds

open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem maj_csmul {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.maj z τ (c • v) = ‖c‖ ^ 2 * X.maj z τ v := by
  have hl : ∀ w, hermC τ.1 X.Gm (c • v) w = c * hermC τ.1 X.Gm v w := by
    intro w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hr : hermC τ.1 X.Gm v (c • v) = conj c * hermC τ.1 X.Gm v v := by
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hcc : c * conj c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hH : hermC τ.1 X.Gm (c • v) (c • v) = ((‖c‖ ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v := by
    rw [hl, hr, ← mul_assoc, hcc]
  have hP : X.posPart z τ (c • v) = ‖c‖ ^ 2 * X.posPart z τ v := by
    simp only [Data.posPart, hl, map_mul]
    rw [← Complex.re_ofReal_mul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hcc]
    ring
  simp only [Data.maj, hP, hH, Complex.re_ofReal_mul]
  ring

variable (z : Frame X.Ψ r) (ξ : Fin r → E) [hz : Fact (z ∈ X.dom)]

theorem riesz (δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ) :
    ∃ d : VT (X := X) z ξ, ∀ u ∈ X.Uz z ξ, ∀ τ : X.Ψ, δ τ (u τ) = X.Hf z τ (u τ) (d.val τ) := by
  classical
  let ℓ : VT (X := X) z ξ →ₗ[ℝ] ℝ :=
    { toFun := fun u => ∑ τ, (δ τ (u.val τ)).re
      map_add' := fun u v => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [VT.val_add, Pi.add_apply, map_add (f := _), Complex.add_re]
      map_smul' := fun c u => by
        rw [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [VT.val_smul, Pi.smul_apply, ← Complex.coe_smul, map_smul, smul_eq_mul,
          Complex.re_ofReal_mul] }
  let d := (InnerProductSpace.toDual ℝ (VT (X := X) z ξ)).symm (LinearMap.toContinuousLinearMap ℓ)
  refine ⟨d, fun u hu τ0 => ?_⟩
  have hd : ∀ v : VT (X := X) z ξ, inner ℝ d v = ℓ v := fun v => by
    rw [InnerProductSpace.toDual_symm_apply]
    rfl

  have key : ∀ w ∈ X.Uz z ξ, (δ τ0 (w τ0)).re = (X.Hf z τ0 (w τ0) (d.val τ0)).re := by
    intro w hw
    let s : X.Ψ → ℂ := fun τ => if τ = τ0 then 1 else 0
    have hw' := MajorantOperators.smul_fam_mem s hw
    have h := hd (VT.mk _ hw')
    rw [inner_eq] at h
    simp only [ℓ, LinearMap.coe_mk, AddHom.coe_mk, VT.val_mk, MajorantOperators.gI] at h
    rw [Finset.sum_eq_single τ0 (fun τ _ hτ => by simp [s, hτ, MajorantOperators.Hf_zero_right])
      (fun h => absurd (Finset.mem_univ τ0) h),
      Finset.sum_eq_single τ0 (fun τ _ hτ => by simp [s, hτ]) (fun h => absurd (Finset.mem_univ τ0) h)]
      at h
    simp only [s, if_true, one_smul] at h
    rw [← h, ← UnipotentCoefficientShift.Hf_conj hz.out, Complex.conj_re]
  have h1 := key u hu
  have h2 := key _ (MajorantOperators.smul_fam_mem (fun _ => Complex.I) hu)
  simp only [map_smul, smul_eq_mul, UnipotentCoefficientShift.Hf_smul_left, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_sub] at h2
  apply Complex.ext
  · exact h1
  · linarith


omit hz in
theorem finrank_le {ξ : Fin r → E} (hz : z ∈ X.dom) (hξ : X.IsIso ξ) :
    finrank ℝ (VT (X := X) z ξ) ≤ 2 * fdeg E * (r - 2) := by
  classical
  let Lm : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin 2 → ℂ) :=
    { toFun := fun u τ => ![hermC τ.1 X.Gm (u τ) (Data.emb τ.1 ξ),
        hermC τ.1 X.Gm (X.jp z τ (u τ)) (Data.emb τ.1 ξ)]
      map_add' := fun u v => by
        funext τ i
        fin_cases i <;> simp [hermC_add_left, Data.jp_add]
      map_smul' := fun c u => by
        funext τ i
        fin_cases i <;> simp [← Complex.coe_smul, hermC_smul_left, Data.jp_smul] }
  have hker : LinearMap.ker Lm = Usub (X := X) z ξ := by
    ext u
    rw [LinearMap.mem_ker]
    show Lm u = 0 ↔ u ∈ X.Uz z ξ
    rw [MajorantOperators.mem_Uz_iff, funext_iff]
    refine forall_congr' fun τ => ?_
    rw [funext_iff, Fin.forall_fin_two]
    simp [Lm]
  have hsurj : LinearMap.range Lm = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    have hm : ∀ τ : X.Ψ, hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ) ≠ 0 := by
      intro τ
      rw [← Data.Hf_eq_jp, X.Hf_self hz]
      exact_mod_cast (X.maj_pos hz τ (emb_ne_zero τ.1 hξ.2.2)).ne'
    have hee : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := fun τ => by
      rw [hermC_emb, hξ.2.1, map_zero]
    refine ⟨fun τ => (t τ 0 / hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ)) •
        X.jp z τ (Data.emb τ.1 ξ) +
      (t τ 1 / hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ, ?_⟩
    funext τ i
    fin_cases i
    · simp [Lm, hermC_add_left, hermC_smul_left, hee, div_mul_cancel₀ _ (hm τ)]
    · simp [Lm, hermC_add_left, hermC_smul_left, Data.jp_add, Data.jp_smul, X.jp_jp hz, hee,
        div_mul_cancel₀ _ (hm τ)]
  have hrn := LinearMap.finrank_range_add_finrank_ker Lm
  rw [hsurj, finrank_top, hker] at hrn
  have hdom : finrank ℝ (X.Ψ → Fin r → ℂ) = Fintype.card X.Ψ * (r * 2) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  have hcod : finrank ℝ (X.Ψ → Fin 2 → ℂ) = Fintype.card X.Ψ * (2 * 2) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  rw [hdom, hcod] at hrn
  have hV : finrank ℝ (VT (X := X) z ξ) = finrank ℝ (Usub (X := X) z ξ) := rfl

  have hΨ : 2 * Fintype.card X.Ψ ≤ finrank ℚ E := by
    have hdisj : Disjoint X.Ψ (X.Ψ.image ComplexEmbedding.conjugate) := by
      rw [Finset.disjoint_left]
      intro σ hσ hσ'
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hσ'
      exact (X.cmType τ).mp hτ hσ
    have hinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) :=
      fun a b h => by
        have := congrArg ComplexEmbedding.conjugate h
        simpa using this
    have h1 := Finset.card_le_univ (X.Ψ ∪ X.Ψ.image ComplexEmbedding.conjugate)
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj,
      NumberField.Embeddings.card] at h1
    rw [Fintype.card_coe]
    omega
  have hf : Fintype.card X.Ψ ≤ fdeg E := by
    unfold fdeg
    omega
  rw [hV]
  have hk : finrank ℝ (Usub (X := X) z ξ) = 2 * Fintype.card X.Ψ * (r - 2) := by
    rw [Nat.eq_sub_of_add_eq' hrn, Nat.mul_sub]
    ring_nf
  rw [hk]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hf)

end FinrankRieszBounds

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermCOrthonormalCoordinates
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

def mjip {n : ℕ} (p q : Fin n → ℂ) : ℂ := ∑ i, p i * conj (q i)

lemma mjip_self {n : ℕ} (p : Fin n → ℂ) : mjip p p = ((nsq p : ℝ) : ℂ) := by
  simp only [mjip, nsq, Complex.ofReal_sum, Complex.ofReal_pow, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

lemma mjip_norm_le {n : ℕ} (p q : Fin n → ℂ) :
    ‖mjip p q‖ ≤ Real.sqrt (nsq p) * Real.sqrt (nsq q) := by
  unfold mjip nsq
  calc ‖∑ i, p i * conj (q i)‖ ≤ ∑ i, ‖p i * conj (q i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖p i‖ * ‖q i‖ := by simp [norm_mul]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

lemma mjip_single {n : ℕ} (p : Fin n → ℂ) (d : Fin n) : mjip p (Pi.single d 1) = p d := by
  unfold mjip
  rw [Finset.sum_eq_single d (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  simp

lemma mjip_zero_right {n : ℕ} (p : Fin n → ℂ) : mjip p 0 = 0 := by
  simp [mjip]

lemma mjnsq_sub_smul {n : ℕ} (p q : Fin n → ℂ) (t : ℝ) :
    nsq (p - (t : ℂ) • q) = nsq p - 2 * t * (mjip p q).re + t ^ 2 * nsq q := by
  unfold nsq mjip
  rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def mjpa (w : Fin r → ℂ) : Fin X.p0 → ℂ := fun a => w (Fin.castLE X.p0_le a)

def mjpb (w : Fin r → ℂ) : Fin (r - X.p0) → ℂ := fun m => w (nI X m)

lemma nsq_zero' {n : ℕ} : nsq (0 : Fin n → ℂ) = 0 := by
  simp [nsq]

private lemma hermC_fin_sum_smul_left {n : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} (p : Fin n → ℂ)
    (f : Fin n → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ i, p i • f i) v = ∑ i, p i * hermC τ G (f i) v := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring

private lemma hermC_fin_sum_smul_right_mul_conj {n : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} (u : Fin r → ℂ)
    (q : Fin n → ℂ) (f : Fin n → Fin r → ℂ) :
    hermC τ G u (∑ j, q j • f j) = ∑ j, hermC τ G u (f j) * conj (q j) := by
  unfold hermC
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring

lemma hermC_bilin (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (p q : Fin n → ℂ)
    (f : Fin n → Fin r → ℂ) :
    hermC τ G (∑ i, p i • f i) (∑ j, q j • f j) =
      ∑ i, ∑ j, p i * hermC τ G (f i) (f j) * conj (q j) := by
  rw [hermC_fin_sum_smul_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hermC_fin_sum_smul_right_mul_conj, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma sum_fin_eq_sum_castLE_add_sum_shift {M : Type} [AddCommMonoid M] {p0 n : ℕ} (h : p0 ≤ n) (f : Fin n → M) :
    ∑ i, f i = ∑ a : Fin p0, f (Fin.castLE h a) +
      ∑ m : Fin (n - p0), f ⟨p0 + m, by have := m.isLt; omega⟩ := by
  let e : Fin p0 ⊕ Fin (n - p0) ≃ Fin n := finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))
  rw [← e.sum_comp f, Fintype.sum_sum_type]
  congr 1
  all_goals exact Finset.sum_congr rfl fun i _ => congrArg f (Fin.ext (by simp [e]))

lemma hermC_orthonormal_coordinates {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (p q : Fin r → ℂ) :
    hermC τ.1 X.Gm (mat x τ *ᵥ p) (mat x τ *ᵥ q) =
      mjip (mjpa X p) (mjpa X q) - mjip (mjpb X p) (mjpb X q) := by
  have hM : ∀ u : Fin r → ℂ, mat x τ *ᵥ u = ∑ c, u c • col (mat x τ) c := by
    intro u
    ext k
    simp [Matrix.mulVec, dotProduct, col, Finset.sum_apply, mul_comm]
  have hij : ∀ i j, hermC τ.1 X.Gm (col (mat x τ) i) (col (mat x τ) j) =
      if i = j then ((sgn X.p0 (i : ℕ) : ℝ) : ℂ) else 0 := by
    intro i j
    have := congrFun (congrFun (ho τ) i) j
    simpa [gram, Matrix.diagonal_apply] using this
  rw [hM p, hM q, hermC_bilin]
  simp only [hij, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sum_fin_eq_sum_castLE_add_sum_shift X.p0_le]
  simp only [mjip, mjpa, mjpb, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [sgn, mjpa, a.isLt]
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp [sgn, mjpb, nI]

lemma mj_colP (x : Frame X.Ψ r) (Z : X.Coord) (τ : X.Ψ) (c : Fin X.p0) :
    X.colP (X.xZ x Z) τ c = mat x τ *ᵥ col (X.lowBlock Z τ) (Fin.castLE X.p0_le c) := by
  funext k
  rfl

def mjg (Z : X.Coord) (τ : X.Ψ) (δ : Fin X.p0 → ℂ) : Fin r → ℂ :=
  ∑ c, δ c • col (X.lowBlock Z τ) (Fin.castLE X.p0_le c)

lemma mjg_pa (Z : X.Coord) (τ : X.Ψ) (δ : Fin X.p0 → ℂ) : mjpa X (mjg X Z τ δ) = δ := by
  funext a
  have ha : ¬ (X.p0 ≤ (a : ℕ)) := not_le.2 a.isLt
  simp [mjpa, mjg, Finset.sum_apply, col, Data.lowBlock, ha, Fin.castLE_inj]

lemma mjg_pb (Z : X.Coord) (τ : X.Ψ) (δ : Fin X.p0 → ℂ) :
    mjpb X (mjg X Z τ δ) = Matrix.of (Z τ) *ᵥ δ := by
  funext m
  simp only [mjpb, mjg, nI, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col, Data.lowBlock, Matrix.of_apply,
    Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hne : ¬ ((⟨X.p0 + (m : ℕ), by have := m.isLt; have := X.p0_le; omega⟩ : Fin r) =
      Fin.castLE X.p0_le c) := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hlt : X.p0 ≤ X.p0 + (m : ℕ) ∧ ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0 := ⟨by omega, by simp⟩
  rw [if_neg hne, dite_eq_left hlt, zero_add, mul_comm]
  congr 2 <;> ext <;> simp

lemma mj_sum_colP (x : Frame X.Ψ r) (Z : X.Coord) (τ : X.Ψ) (δ : Fin X.p0 → ℂ) :
    ∑ c, δ c • X.colP (X.xZ x Z) τ c = mat x τ *ᵥ mjg X Z τ δ := by
  simp only [mj_colP, mjg, Matrix.mulVec_sum, Matrix.mulVec_smul]

lemma mj_coord {x : Frame X.Ψ r} (ho : X.IsOrtho x) (Z : X.Coord) (hy : X.xZ x Z ∈ X.dom)
    (τ : X.Ψ) (w : Fin r → ℂ) : ∃ γ : Fin X.p0 → ℂ,
      X.maj (X.xZ x Z) τ (mat x τ *ᵥ w) =
        2 * (nsq γ - nsq (Matrix.of (Z τ) *ᵥ γ)) - (nsq (mjpa X w) - nsq (mjpb X w)) ∧
      ∀ δ, mjip (mjpa X w) δ - mjip (mjpb X w) (Matrix.of (Z τ) *ᵥ δ) =
        mjip γ δ - mjip (Matrix.of (Z τ) *ᵥ γ) (Matrix.of (Z τ) *ᵥ δ) := by
  have hG := X.gramPos_posDef hy τ
  have hdet : IsUnit (X.gramPos (X.xZ x Z) τ).det := by open scoped ComplexOrder in exact hG.det_pos.ne'.isUnit
  have hGi : (X.gramPos (X.xZ x Z) τ)⁻¹.IsHermitian := (X.gramPos_isHermitian (X.xZ x Z) τ).inv
  have hconj : ∀ a b, conj ((X.gramPos (X.xZ x Z) τ)⁻¹ b a) = (X.gramPos (X.xZ x Z) τ)⁻¹ a b :=
    fun a b => hGi.apply a b
  obtain ⟨β, hβ⟩ : ∃ β : Fin X.p0 → ℂ, ∀ b, β b =
      hermC τ.1 X.Gm (mat x τ *ᵥ w) (col (mat (X.xZ x Z) τ) (Fin.castLE X.p0_le b)) :=
    ⟨_, fun _ => rfl⟩
  have hβ' : ∀ b, β b = hermC τ.1 X.Gm (mat x τ *ᵥ w) (X.colP (X.xZ x Z) τ b) := hβ
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin X.p0 → ℂ, ∀ a, γ a = ∑ b, β b * (X.gramPos (X.xZ x Z) τ)⁻¹ b a :=
    ⟨_, fun _ => rfl⟩
  have K : ∀ c, hermC τ.1 X.Gm (∑ a, γ a • X.colP (X.xZ x Z) τ a) (X.colP (X.xZ x Z) τ c) = β c := by
    intro c
    rw [hermC_fin_sum_smul_left]
    calc ∑ a, γ a * hermC τ.1 X.Gm (X.colP (X.xZ x Z) τ a) (X.colP (X.xZ x Z) τ c)
        = ∑ b, β b * ((X.gramPos (X.xZ x Z) τ)⁻¹ * X.gramPos (X.xZ x Z) τ) b c := by
          simp only [← X.gramPos_apply, hγ, Finset.sum_mul, Matrix.mul_apply, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
      _ = β c := by
          rw [Matrix.nonsing_inv_mul _ hdet, Finset.sum_eq_single c]
          · simp
          · intro b _ hb
            simp [Matrix.one_apply_ne hb]
          · simp
  have P : X.posPart (X.xZ x Z) τ (mat x τ *ᵥ w) = nsq γ - nsq (Matrix.of (Z τ) *ᵥ γ) := by
    have e3 := hermC_orthonormal_coordinates X ho τ (mjg X Z τ γ) (mjg X Z τ γ)
    simp only [mjg_pa, mjg_pb, mjip_self] at e3
    rw [← mj_sum_colP X x Z τ γ, hermC_fin_sum_smul_right_mul_conj] at e3
    simp only [K] at e3
    have hre : (∑ c, β c * conj (γ c)).re = nsq γ - nsq (Matrix.of (Z τ) *ᵥ γ) := by
      rw [e3]
      simp
    rw [← hre, Data.posPart]
    congr 1
    simp only [← hβ]
    refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hγ a, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, hconj]
    ring
  refine ⟨γ, ?_, ?_⟩
  · rw [Data.maj, P, hermC_orthonormal_coordinates X ho τ w w, mjip_self, mjip_self]
    simp
  · intro δ
    have e1 := hermC_orthonormal_coordinates X ho τ w (mjg X Z τ δ)
    have e2 := hermC_orthonormal_coordinates X ho τ (mjg X Z τ γ) (mjg X Z τ δ)
    simp only [mjg_pa, mjg_pb] at e1 e2
    rw [← e1, ← e2, ← mj_sum_colP X x Z τ δ, ← mj_sum_colP X x Z τ γ, hermC_fin_sum_smul_right_mul_conj, hermC_fin_sum_smul_right_mul_conj]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [K c, hβ']

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end
