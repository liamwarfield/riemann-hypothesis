module

public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtFin
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.MemIntLocOfIdem

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.SkewTwo
noncomputable section

namespace GlobalTheory.ThK.Dbl.Vf2

open Matrix GlobalTheory.WeilM PositivityTheory.ThKG.Loc.Cone.Vf

section Skew

variable {A K β : Type} [CommRing A] [Field K] [Fintype β] [DecidableEq β]

omit [DecidableEq β] in
theorem rank_lt {M : Matrix β β K} {y w φ : β → K} (hy : M *ᵥ y = 0) (hw : w ∉ LinearMap.range M.mulVecLin) (hφ : φ ⬝ᵥ y ≠ 0) :
    M.rank < (M + vecMulVec w φ).rank := by
  have e : ∀ x, (M + vecMulVec w φ) *ᵥ x = M *ᵥ x + (φ ⬝ᵥ x) • w := fun x => by
    rw [add_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  have h1 : w ∈ LinearMap.range (M + vecMulVec w φ).mulVecLin := ⟨(φ ⬝ᵥ y)⁻¹ • y, by
    rw [mulVecLin_apply, mulVec_smul, e, hy, zero_add, smul_smul, inv_mul_cancel₀ hφ, one_smul]⟩
  refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne ?_ fun h => hw (h ▸ h1))
  rintro _ ⟨x, rfl⟩
  rw [mulVecLin_apply, eq_sub_of_add_eq (e x).symm]
  exact sub_mem ⟨x, rfl⟩ (Submodule.smul_mem _ _ h1)

variable {c : A →+* A} {r : A →+* K} {G G' M m P Q : Matrix β β A}

omit [DecidableEq β] in
theorem skew_two (hc : ∀ z, c (c z) = z) (hG : ∀ i j, c (G j i) = G i j) (u w : β → A) :
    (vecMulVec u (G *ᵥ c ∘ w) - vecMulVec w (G *ᵥ c ∘ u))ᵀ * G +
      G * (vecMulVec u (G *ᵥ c ∘ w) - vecMulVec w (G *ᵥ c ∘ u)).map c = 0 := by
  have k : ∀ u w : β → A, (vecMulVec u (G *ᵥ c ∘ w))ᵀ * G = G * (vecMulVec w (G *ᵥ c ∘ u)).map c := fun u w => by
    ext i j
    change (∑ k : β, (u k * (G *ᵥ c ∘ w) i) * G k j) =
      ∑ k : β, G i k * c (w k * (G *ᵥ c ∘ u) j)
    simp only [mulVec, dotProduct, Function.comp_apply, Finset.mul_sum, Finset.sum_mul,
      map_sum, map_mul, hc, hG]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [transpose_sub, Matrix.sub_mul, Matrix.map_sub _ (map_sub c), Matrix.mul_sub, k, k]
  abel

theorem step (hc : ∀ z, c (c z) = z) (hr : Function.Surjective r) (hG : ∀ i j, c (G j i) = G i j) (hG' : G * G' = 1)
    (hcase : ((∀ z, r z = 0 → r (c z) = 0) ∧ ∃ κ, r (κ - c κ) ≠ 0) ∨ ∃ η, r η = 1 ∧ r (c η) = 0)
    (lag : Mᵀ * G * m.map c + mᵀ * G * M.map c = 0) (inj : P * M + Q * m = 1) (h0 : (M.map r).det = 0) :
    ∃ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 ∧ (M.map r).rank < ((M + S * m).map r).rank := by
  have mv : ∀ (N : Matrix β β A) x, N.map r *ᵥ r ∘ x = r ∘ (N *ᵥ x) := fun N x => funext fun i => (r.map_mulVec N x i).symm
  have mc : ∀ (N : Matrix β β A) x, N.map c *ᵥ c ∘ x = c ∘ (N *ᵥ x) := fun N x => funext fun i => (c.map_mulVec N x i).symm
  obtain ⟨y₀, hy0, hy⟩ := exists_mulVec_eq_zero_iff.2 h0
  obtain ⟨y, rfl⟩ := hr.comp_left y₀
  obtain ⟨i, hi⟩ : ∃ i, r ((m *ᵥ y) i) ≠ 0 := by
    by_contra h
    push Not at h
    have := congrArg (fun N : Matrix β β A => N.map r *ᵥ r ∘ y) inj
    simp only [Matrix.map_add _ (map_add r), Matrix.map_mul, add_mulVec, ← mulVec_mulVec, hy, mulVec_zero,
      Matrix.map_one _ (map_zero r) (map_one r), one_mulVec] at this
    rw [mv m, show r ∘ (m *ᵥ y) = 0 from funext h, mulVec_zero, add_zero] at this
    exact hy0 this.symm
  let w : β → A := c ∘ (G' *ᵥ Pi.single i 1)
  have hw : G *ᵥ c ∘ w = Pi.single i 1 := by
    rw [show c ∘ w = G' *ᵥ Pi.single i 1 from funext fun _ => hc _, mulVec_mulVec, hG', one_mulVec]
  have fin : ∀ (u : β → A) (z : β → K), (∀ a b, r (u a * (Pi.single i 1 : β → A) b - w a * (G *ᵥ c ∘ u) b) =
      z a * (Pi.single i 1 : β → K) b) → z ∉ LinearMap.range (M.map r).mulVecLin → ∃ S : Matrix β β A,
      Sᵀ * G + G * S.map c = 0 ∧ (M.map r).rank < ((M + S * m).map r).rank := fun u z h1 h2 => by
    refine ⟨_, skew_two hc hG u w, ?_⟩
    rw [Matrix.map_add _ (map_add r), Matrix.map_mul, hw, show (vecMulVec u (Pi.single i 1) - vecMulVec w (G *ᵥ c ∘ u)).map r =
      vecMulVec z (Pi.single i 1) from Matrix.ext h1, vecMulVec_mul]
    refine rank_lt hy h2 ?_
    rwa [← dotProduct_mulVec, mv, single_dotProduct, one_mul]
  have sg : ∀ b, r ((Pi.single i 1 : β → A) b) = (Pi.single i 1 : β → K) b := fun b => by
    simp [Pi.single_apply, apply_ite r]
  rcases hcase with ⟨h1, κ, hκ⟩ | ⟨η, h1, h2⟩
  · refine fin (κ • w) (r (κ - c κ) • r ∘ w) (fun a b => ?_) fun h => ?_
    · rw [show c ∘ (κ • w) = c κ • c ∘ w from funext fun _ => map_mul c _ _, mulVec_smul, hw]
      simp only [Pi.smul_apply, smul_eq_mul, map_sub, map_mul, sg, Function.comp_apply]
      ring
    · obtain ⟨x₀, hx⟩ := (Submodule.smul_mem_iff _ hκ).1 h
      obtain ⟨x, rfl⟩ := hr.comp_left x₀
      rw [mulVecLin_apply, mv] at hx
      have l := congrArg (fun N => y ⬝ᵥ N *ᵥ c ∘ x) lag
      simp only [add_mulVec, dotProduct_add, ← mulVec_mulVec, mc, zero_mulVec, dotProduct_zero] at l
      rw [dotProduct_mulVec y, dotProduct_mulVec y mᵀ, vecMul_transpose, vecMul_transpose] at l
      have e : (m *ᵥ y) i = (m *ᵥ y) ⬝ᵥ G *ᵥ c ∘ (w - M *ᵥ x) - (M *ᵥ y) ⬝ᵥ G *ᵥ c ∘ (m *ᵥ x) := by
        rw [show c ∘ (w - M *ᵥ x) = c ∘ w - c ∘ (M *ᵥ x) from funext fun _ => map_sub c _ _, mulVec_sub, dotProduct_sub, hw,
          dotProduct_single, mul_one]
        linear_combination l
      refine hi ?_
      rw [mv] at hy
      rw [e, map_sub, r.map_dotProduct, r.map_dotProduct, hy, zero_dotProduct, ← mv G, show r ∘ c ∘ (w - M *ᵥ x) = 0 from
        funext fun a => h1 _ (by rw [Pi.sub_apply, map_sub]; exact sub_eq_zero.2 (congrFun hx a).symm), mulVec_zero,
        dotProduct_zero, sub_zero]
  · obtain ⟨z₀, hz⟩ : ∃ z, z ∉ LinearMap.range (M.map r).mulVecLin := by
      by_contra h
      push Not at h
      exact ((isUnit_iff_isUnit_det _).1 (mulVec_surjective_iff_isUnit.1 h)).ne_zero h0
    obtain ⟨z, rfl⟩ := hr.comp_left z₀
    refine fin (η • z) _ (fun a b => ?_) hz
    rw [show c ∘ (η • z) = c η • c ∘ z from funext fun _ => map_mul c _ _, mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul, map_sub, map_mul, sg, Function.comp_apply, h1, h2]
    ring

theorem exists_skew (hc : ∀ z, c (c z) = z) (hr : Function.Surjective r) (hG : ∀ i j, c (G j i) = G i j) (hG' : G * G' = 1)
    (hcase : ((∀ z, r z = 0 → r (c z) = 0) ∧ ∃ κ, r (κ - c κ) ≠ 0) ∨ ∃ η, r η = 1 ∧ r (c η) = 0)
    (hu : ∀ z, r z ≠ 0 → r (c z) ≠ 0 → IsUnit z)
    (lag : Mᵀ * G * m.map c + mᵀ * G * M.map c = 0) (inj : P * M + Q * m = 1) :
    ∃ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 ∧ IsUnit (M + S * m).det := by
  have l2 : ∀ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 →
      (M + S * m)ᵀ * G * m.map c + mᵀ * G * (M + S * m).map c = 0 := fun S hS => by
    rw [transpose_add, transpose_mul, Matrix.map_add _ (map_add c), Matrix.map_mul]
    linear_combination (norm := noncomm_ring) lag + mᵀ * hS * m.map c
  have i2 : ∀ S : Matrix β β A, P * (M + S * m) + (Q - P * S) * m = 1 := fun S => by
    linear_combination (norm := noncomm_ring) inj
  have ind : ∀ k : ℕ, ∃ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 ∧
      (((M + S * m).map r).det ≠ 0 ∨ k ≤ ((M + S * m).map r).rank) := fun k => by
    induction k with
    | zero => exact ⟨0, by simp, .inr (Nat.zero_le _)⟩
    | succ k ih =>
      obtain ⟨S, h1, h2⟩ := ih
      by_cases h0 : ((M + S * m).map r).det = 0
      · obtain ⟨S', h3, h4⟩ := step hc hr hG hG' hcase (l2 S h1) (i2 S) h0
        refine ⟨S + S', ?_, .inr ?_⟩
        · rw [transpose_add, Matrix.map_add _ (map_add c)]
          linear_combination (norm := noncomm_ring) h1 + h3
        · rw [Matrix.add_mul, ← add_assoc]
          exact (h2.resolve_left (not_not.2 h0)).trans_lt h4
      · exact ⟨S, h1, .inl h0⟩
  obtain ⟨S, h1, h2⟩ := ind (Fintype.card β + 1)
  have h3 := h2.resolve_right (not_le.2 (Nat.lt_succ_of_le (rank_le_card_width _)))
  refine ⟨S, h1, hu _ (by rwa [r.map_det]) fun h4 => ?_⟩
  rw [c.map_det, r.map_det] at h4
  obtain ⟨y, hy0, hy⟩ := exists_mulVec_eq_zero_iff.2 h4
  have l := congrArg (fun N : Matrix β β A => N.map r *ᵥ y) (l2 S h1)
  have j := congrArg (fun N : Matrix β β A => (N.map c).map r *ᵥ y) (i2 S)
  generalize M + S * m = t at *
  change (t.map c).map r *ᵥ y = 0 at hy
  simp only [Matrix.map_add _ (map_add r), Matrix.map_add _ (map_add c), Matrix.map_mul, add_mulVec, ← mulVec_mulVec, hy,
    mulVec_zero, add_zero, zero_add, Matrix.map_zero _ (map_zero r), zero_mulVec, Matrix.map_one _ (map_zero r) (map_one r),
    Matrix.map_one _ (map_zero c) (map_one c), one_mulVec] at l j
  have g0 : (G.map r).det ≠ 0 := fun h => by
    have := congrArg (fun N : Matrix β β A => (N.map r).det) hG'
    simp only [Matrix.map_mul, det_mul, h, zero_mul, Matrix.map_one _ (map_zero r) (map_one r), det_one] at this
    exact zero_ne_one this
  rw [eq_zero_of_mulVec_eq_zero g0 (eq_zero_of_mulVec_eq_zero (by rwa [transpose_map, det_transpose]) l), mulVec_zero] at j
  exact hy0 j.symm

end Skew

variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] {c : A →ₐ[R] A} [Fintype β] [DecidableEq β] {J : Matrix β β A}

theorem lag_of {b b' x y : Matrix β β A} (b1 : Adj c J b b') (hb : b + b' = -1) (g : UG c (dbl J))
    (hg : g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = fromRows x y) :
    (y + b * (y - x))ᵀ * J * (y - x).map c + (y - x)ᵀ * J * (y + b * (y - x)).map c = 0 := by
  have h1 : g.1.1ᵀ * dbl J * g.1.1.map c = dbl J := g.2
  have h2 : (fromRows x y)ᵀ * dbl J * (fromRows x y).map c = 0 := by
    rw [← hg, transpose_mul, mapc_mul]
    calc _ = (diagCols β : Matrix (β ⊕ β) β A)ᵀ * (g.1.1ᵀ * dbl J * g.1.1.map c) * (diagCols β : Matrix (β ⊕ β) β A).map c := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by
        rw [h1]; simp [diagCols, dbl, fromRows_map, mapc_one, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  have e : b'.map c = -1 - b.map c := by
    rw [← mapc_one (c := c), ← mapc_neg, ← mapc_sub, ← hb]; congr 1; abel
  have b2 : bᵀ * J = -J - J * b.map c := by rw [b1, e]; noncomm_ring
  rw [transpose_fromRows, dbl, fromCols_mul_fromBlocks, fromRows_map, fromCols_mul_fromRows] at h2
  rw [transpose_add, transpose_mul, mapc_add, mapc_mul, mapc_sub, transpose_sub]
  linear_combination (norm := noncomm_ring) (yᵀ - xᵀ) * b2 * (y.map c - x.map c) - h2

theorem exists_decomp {b b' x y t' : Matrix β β A} (b1 : Adj c J b b') (hb : b + b' = -1) (g : UG c (dbl J))
    (hg : g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = fromRows x y) (ht : (y + b * (y - x)) * t' = 1) {ε : A} (he : ε * ε = ε)
    (hc : c ε = ε) (hm : ε • (y - x) = y - x) :
    ∃ (s n p : UG c (dbl J)) (t : GL β A), s * s = 1 ∧ g = s * n * s * p ∧ s.1.1 = CC b * SS ε * Ci b ∧
      n.1.1 = CC b * fromBlocks 1 (-((y - x) * t')) 0 1 * Ci b ∧ (n⁻¹).1.1 = CC b * fromBlocks 1 ((y - x) * t') 0 1 * Ci b ∧
      n.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * (1 : GL β A).1 ∧
      p.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * t.1 ∧
      t.1 = y + b * (y - x) ∧ (t⁻¹).1 = t' := by
  have lag := lag_of b1 hb g hg
  set m : Matrix β β A := y - x with hmd
  set t₀ := y + b * m with ht₀
  set T := -(m * t') with hT
  have ht' : t' * t₀ = 1 := mul_eq_one_comm.1 ht
  have sk : Tᵀ * J + J * T.map c = 0 := by
    have a1 : t'ᵀ * t₀ᵀ = 1 := by rw [← transpose_mul, ht, transpose_one]
    have a2 : t₀.map c * t'.map c = 1 := by rw [← mapc_mul, ht, mapc_one]
    rw [hT, transpose_neg, transpose_mul, mapc_neg, mapc_mul]
    linear_combination (norm := noncomm_ring) -(t'ᵀ * lag * t'.map c) + a1 * J * m.map c * t'.map c + t'ᵀ * mᵀ * J * a2
  have e0 : ε * (1 - ε) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have e0' : (1 - ε) * ε = 0 := by rw [mul_comm, e0]
  have e1 : (1 - ε) * (1 - ε) = 1 - ε := by rw [sub_mul, one_mul, e0, sub_zero]
  have hS : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A) * SS ε = 1 := by
    rw [SS, fromBlocks_multiply, ← fromBlocks_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, e0, e0', e1, he, ← add_smul]
    simp
  have hSu : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A)ᵀ * fromBlocks 0 J J 0 * (SS ε : Matrix (β ⊕ β) (β ⊕ β) A).map c =
      fromBlocks 0 J J 0 := by
    rw [SS, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    simp only [mapc_smul, mapc_one, map_sub, map_one, hc, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, smul_zero, zero_add, add_zero, smul_smul, e0, e0', e1, he, ← add_smul]
    simp
  have hU : (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks 1 (m * t') 0 1 = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one, hT]; simp
  have hUu : (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A)ᵀ * fromBlocks 0 J J 0 *
      (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A).map c = fromBlocks 0 J J 0 := by
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply, mapc_one, mapc_zero]
    simp only [transpose_one, transpose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
    rw [add_comm (J * _), sk]
  have hTt : T * t₀ = -m := by rw [hT, Matrix.neg_mul, Matrix.mul_assoc, ht', Matrix.mul_one]
  let s := mkU b1 hb _ _ hS hSu
  let n := mkU b1 hb _ _ hU hUu
  have hs : s.1.1 = CC b * SS ε * Ci b := rfl
  have hn : n.1.1 = CC b * fromBlocks 1 T 0 1 * Ci b := rfl
  have hεT : ε • T = T := by rw [hT, smul_neg, ← Matrix.smul_mul, hm]
  have hεT' : (1 - ε) • T = 0 := by rw [sub_smul, one_smul, hεT, sub_self]
  have hL : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks 1 T 0 1 * SS ε = fromBlocks 1 0 T 1 := by
    rw [SS, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, smul_zero, add_zero, hεT, hεT',
      zero_add, Matrix.add_mul, smul_add, smul_smul, e0, e0', e1, he, zero_smul, ← add_smul]
    simp
  have hD : Ci b * (diagCols β : Matrix (β ⊕ β) β A) = (fromRows 1 0 : Matrix (β ⊕ β) β A) := by
    rw [Ci, diagCols, fromBlocks_mul_fromRows]; simp
  have hD' : CC b * (fromRows 1 0 : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) := by
    rw [CC, diagCols, fromBlocks_mul_fromRows]; simp
  refine ⟨s, n, (s * n * s)⁻¹ * g, ⟨t₀, t', ht, ht'⟩, Subtype.ext (Units.ext s.1.mul_inv), by group, hs, hn, rfl, ?_, ?_, rfl, rfl⟩
  · rw [hn, Matrix.mul_assoc _ (Ci b), hD, Matrix.mul_assoc (CC b), fromBlocks_mul_fromRows]
    simpa using hD'
  · have e : (s * n * s).1.1 = CC b * fromBlocks 1 0 T 1 * Ci b := by
      change s.1.1 * n.1.1 * s.1.1 = _
      rw [hs, hn, ← hL]
      calc CC b * SS ε * Ci b * (CC b * fromBlocks 1 T 0 1 * Ci b) * (CC b * SS ε * Ci b)
          = CC b * (SS ε * (Ci b * CC b) * fromBlocks 1 T 0 1 * (Ci b * CC b) * SS ε) * Ci b := by noncomm_ring
        _ = _ := by rw [Ci_CC, Matrix.mul_one, Matrix.mul_one]
    have e2 : g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (s * n * s).1.1 * ((diagCols β : Matrix (β ⊕ β) β A) * t₀) := by
      rw [e, hg, ← Matrix.mul_assoc _ (diagCols β : Matrix (β ⊕ β) β A), Matrix.mul_assoc _ (Ci b), hD, Matrix.mul_assoc (CC b),
        fromBlocks_mul_fromRows, CC, fromBlocks_mul_fromRows, fromRows_mul]
      congr 1
      · linear_combination (norm := noncomm_ring) -((1 + b) * hTt) - ht₀ + hmd
      · linear_combination (norm := noncomm_ring) -(b * hTt) - ht₀
    change ((s * n * s)⁻¹).1.1 * g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * t₀
    rw [Matrix.mul_assoc _ g.1.1, e2, ← Matrix.mul_assoc, show ((s * n * s)⁻¹).1.1 * (s * n * s).1.1 = 1 from (s * n * s).1.inv_mul,
      Matrix.one_mul]

end GlobalTheory.ThK.Dbl.Vf2

end
end

noncomputable section

namespace GlobalTheory.ThK.Dbl.Vf2

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas GlobalTheory.Doubling PositivityTheory.ThKG.Loc.Cone.Vf
open Formalism.UG (bc)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v : Pl F}


variable (σ v) in
def cInt : intLoc F E v →+* intLoc F E v :=
  ((sigR (Fv F v) σ).comp (intLoc F E v).subtype).codRestrict _ fun z => sigR_mem_intLoc σ z.2

theorem exists_res {B : Base F E} (hB : B.IsGood σ) (v : Pl F) : ∃ (K : Type) (_ : Field K) (r : intLoc F E v →+* K),
    Function.Surjective r ∧ (((∀ z, r z = 0 → r (cInt σ v z) = 0) ∧ ∃ κ, r (κ - cInt σ v κ) ≠ 0) ∨
      ∃ η, r η = 1 ∧ r (cInt σ v η) = 0) ∧ ∀ z, r z ≠ 0 → r (cInt σ v z) ≠ 0 → IsUnit z := by
  have hσ := hB.cm
  rcases GlobalTheory.KFinLoc.split_or_inert F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · let ρ : intLoc F E v →+* v.adicCompletionIntegers F := ((splitProj τ : Fv F v ⊗[F] E →+* Fv F v).comp
      (intLoc F E v).subtype).codRestrict (v.adicCompletionIntegers F).toSubring fun z => splitProj_mem τ z.2
    have mk : ∀ a b : v.adicCompletionIntegers F, (splitAlgEquiv hσ τ).symm (a.1, b.1) ∈ intLoc F E v := fun a b =>
      (mem_intLoc_iff_split hσ τ).2 ⟨by rw [splitProj_symm]; exact a.2, by rw [splitProj_comp_symm]; exact b.2⟩
    refine ⟨_, inferInstance, (IsLocalRing.residue _).comp ρ,
      IsLocalRing.residue_surjective.comp fun a => ⟨⟨_, mk a 0⟩, Subtype.ext (splitProj_symm hσ τ _)⟩,
      .inr ⟨⟨_, splitIdem_mem hσ τ⟩, ?_, ?_⟩, fun z h1 h2 => ?_⟩
    · exact (congrArg (IsLocalRing.residue _) (Subtype.ext (splitProj_splitIdem hσ τ) : ρ ⟨_, splitIdem_mem hσ τ⟩ = 1)).trans (map_one _)
    · exact (congrArg (IsLocalRing.residue _) (Subtype.ext ((splitProj_comp τ σ _).symm.trans (splitProj_comp_splitIdem hσ τ)) :
        ρ (cInt σ v ⟨_, splitIdem_mem hσ τ⟩) = 0)).trans (map_zero _)
    · obtain ⟨a, ha⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1).exists_right_inv
      obtain ⟨b, hb⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h2).exists_right_inv
      refine IsUnit.of_mul_eq_one ⟨_, mk a b⟩ (Subtype.ext (split_ext hσ τ ?_ ?_))
      · rw [Subring.coe_mul, map_mul, splitProj_symm, Subring.coe_one, map_one]; exact congrArg Subtype.val ha
      · rw [Subring.coe_mul, map_mul, splitProj_comp_symm, Subring.coe_one, map_one, splitProj_comp]; exact congrArg Subtype.val hb
  · have hu : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
    obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hu
    obtain ⟨ϖ, -, hv, -, -, ⟨x, hx, hx1⟩, -⟩ := exists_isUnramInv hσ hw hc
    let ρ : intLoc F E v →+* w.adicCompletionIntegers E :=
      ((toCompl hu).comp (intLoc F E v).subtype).codRestrict (w.adicCompletionIntegers E).toSubring fun z => toCompl_mem hu z.2
    have sj : Function.Surjective ρ := fun a => by
      obtain ⟨z, hz⟩ := (toCompl_bijective hw hu).2 a.1
      exact ⟨⟨z, (mem_intLoc_iff hw hu _).2 (hz ▸ a.2)⟩, Subtype.ext hz⟩
    have un : ∀ z, ((IsLocalRing.residue _).comp ρ) z ≠ 0 ↔ Valued.v (toCompl hu z.1) = 1 := fun z =>
      (IsLocalRing.residue_ne_zero_iff_isUnit _).trans HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
    refine ⟨_, inferInstance, (IsLocalRing.residue _).comp ρ, IsLocalRing.residue_surjective.comp sj,
      .inl ⟨fun z hz => by_contra fun h => (un z).2 ?_ hz, ?_⟩, fun z h1 _ => ?_⟩
    · rw [← hv, hc]
      exact (un (cInt σ v z)).1 h
    · obtain ⟨κ, hκ⟩ := sj ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx⟩
      refine ⟨κ, (un _).2 ?_⟩
      change Valued.v (toCompl hu (κ.1 - sigR _ σ κ.1)) = 1
      rw [map_sub, ← hc, show toCompl hu κ.1 = x from congrArg Subtype.val hκ, Valuation.map_sub_swap, hx1]
    · obtain ⟨a, ha⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1).exists_right_inv
      obtain ⟨z', rfl⟩ := sj a
      refine IsUnit.of_mul_eq_one z' (Subtype.ext ((toCompl_bijective hw hu).1 ?_))
      rw [Subring.coe_mul, map_mul, Subring.coe_one, map_one]; exact congrArg Subtype.val ha

theorem fr_iff {X : Spc F E n} {a : GL (Fin n) (Fv F v ⊗[F] E)}
    (ha : ∀ y : Fin n → Fv F v ⊗[F] E, (∀ i, y i ∈ intLoc F E v) ↔ a.1 *ᵥ y ∈ latLoc F X.L v) (M) :
    M ∈ Pres v X ↔ ∃ N : Matrix (Fin n) (Fin n) (intLoc F E v), (intLoc F E v).subtype.mapMatrix N = fr v a M := by
  have mv : ∀ (M : Matrix (Fin n) (Fin n) (AE F E)) y, compFin F E v ∘ (M *ᵥ y) = M.map (compFin F E v) *ᵥ (compFin F E v ∘ y) :=
    fun M y => funext fun i => RingHom.map_mulVec _ M y i
  have co : ∀ z ∈ latLoc F X.L v, ∀ i, ((a⁻¹).1 *ᵥ z) i ∈ intLoc F E v := fun z hz =>
    (ha _).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])
  refine ⟨fun hM => ?_, ?_⟩
  · have : ∀ i j, fr v a M i j ∈ intLoc F E v := fun i j => by
      let z := a.1 *ᵥ fun k => (1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) k j
      have hz : z ∈ latLoc F X.L v := (ha _).1 fun k => by
        rw [Matrix.one_apply]; split_ifs
        exacts [one_mem _, zero_mem _]
      have ey : compFin F E v ∘ (fun i => sgE E v (z i)) = z := funext fun i => comp_sgE _
      have h1 := ((mem_latW_loc X _).1 (hM _ ((mem_latW_loc X (fun i => sgE E v (z i))).2
        ⟨fun u hu => funext fun i => at_sgE _ u hu, ey.symm ▸ hz⟩))).2
      have h2 := co _ h1 i
      rw [mv, ey, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h2
      change (fr v a M * 1 : Matrix _ _ _) i j ∈ _ at h2
      rwa [Matrix.mul_one] at h2
    exact ⟨fun i j => ⟨_, this i j⟩, rfl⟩
  · rintro ⟨N, hN⟩ y hy
    obtain ⟨h1, h2⟩ := (mem_latW_loc X y).1 hy
    refine (mem_latW_loc X _).2 ⟨at_mulVec_right _ h1, ?_⟩
    have := (ha (fr v a M *ᵥ ((a⁻¹).1 *ᵥ (compFin F E v ∘ y)))).1 fun i => by
      rw [← hN]
      change ∑ j, (N i j).1 * ((a⁻¹).1 *ᵥ (compFin F E v ∘ y)) j ∈ _
      exact sum_mem fun j _ => mul_mem (N i j).2 (co _ h2 j)
    rwa [fr_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv,
      Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← mv] at this

omit [NumberField E] in
theorem comp_cA (z : AE F E) : compFin F E v (cA σ z) = sigR (Fv F v) σ (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem gram_fr (a : GL (Fin n) (Fv F v ⊗[F] E)) (J M m : Matrix (Fin n) (Fin n) (AE F E)) :
    a.1ᵀ * (Mᵀ * J * m.map (cA σ)).map (compFin F E v) * a.1.map (sigR _ σ) =
      (fr v a M)ᵀ * (a.1ᵀ * J.map (compFin F E v) * a.1.map (sigR _ σ)) * (fr v a m).map (sigR _ σ) := by
  have e1 : (a⁻¹).1ᵀ * a.1ᵀ = 1 := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have e2 : a.1.map (sigR _ σ) * (a⁻¹).1.map (sigR _ σ) = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have e3 : (m.map (cA σ)).map (compFin F E v) = (m.map (compFin F E v)).map (sigR _ σ) := Matrix.ext fun _ _ => comp_cA _
  rw [fr_apply, fr_apply, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    e3, Matrix.transpose_map]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (a⁻¹).1ᵀ, e1, Matrix.one_mul, ← Matrix.mul_assoc (a.1.map _), e2, Matrix.one_mul]

theorem exists_beta {B : Base F E} (hB : B.IsGood σ) {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s)
    (g : UG (cA σ) (dbl (incM F X.J))) {x y a₁ a₂ : Matrix (Fin n) (Fin n) (AE F E)}
    (hg : g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E)) = Matrix.fromRows x y) (hx : x ∈ Pres v X) (hy : y ∈ Pres v X)
    (h1 : a₁ ∈ Pres v X) (h2 : a₂ ∈ Pres v X) (h : a₁ * x + a₂ * y = 1) (ax : At (evFin F v) (x - 1)) (ay : At (evFin F v) (y - 1)) :
    ∃ b b' t', Adj (cA σ) (incM F X.J) b b' ∧ b + b' = -1 ∧ b ∈ Pres v X ∧ t' ∈ Pres v X ∧ (y + b * (y - x)) * t' = 1 := by
  have hσ := cm_conj_conj hB.cm
  have cc := cA_cA (F := F) hσ
  have hL := hX.lat
  obtain ⟨K, _, ρ, r1, r2, r3⟩ := exists_res hB v
  obtain ⟨P, p1, p2⟩ := Frames.exists_rational_frame X.L v
  obtain ⟨G', hG', g1, g2⟩ := Hgt.gram_loc (v := v) (herm_det hX).ne_zero hL.fg (I := IsIntegral ℤ) (fun z hz b => hz.mul b.2) hX.dual
    isIntegral_one (fun z hz => ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, ⟨z, hz⟩, by simp; rfl⟩) P p1 p2
  simp only [inv_one, one_mul] at g1 g2
  have ha := fr_iff (Frames.frame_of_rational P p1 p2)
  set G₀ := P.1ᵀ * X.J * P.1.map σ with hG₀
  let ι := inclR (F := F) (E := E) (Fv F v)
  set a : GL (Fin n) (Fv F v ⊗[F] E) := bc ι P
  let j := (intLoc F E v).subtype.mapMatrix (m := Fin n)
  have inj : Function.Injective j := fun A B e => Matrix.ext fun i k => Subtype.ext (congrFun₂ e i k)
  let G : Matrix (Fin n) (Fin n) (intLoc F E v) := fun i k => ⟨_, (g1 i k).mem⟩
  let H : Matrix (Fin n) (Fin n) (intLoc F E v) := fun i k => ⟨_, (g2 i k).mem⟩
  have eG : a.1ᵀ * (incM F X.J).map (compFin F E v) * a.1.map (sigR _ σ) = j G := by
    change _ = G₀.map ι
    rw [hG₀, Matrix.map_mul, Matrix.map_mul, show (incM F X.J).map (compFin F E v) = X.J.map ι from
      Matrix.ext fun i k => congrArg (· ⊗ₜ[F] X.J i k) (map_one (evFin F v))]
    rfl
  have jj : ∀ N N' : Matrix (Fin n) (Fin n) (intLoc F E v), j (Nᵀ * G * N'.map (cInt σ v)) = (j N)ᵀ * j G * (j N').map (sigR _ σ) :=
    fun N N' => by rw [map_mul, map_mul]; rfl
  obtain ⟨θ₀, hθ⟩ := GlobalTheory.exists_int_add_conj_eq_one_of_base_good B hB
  let θ : AE F E := inclR (F := F) (AF F) (θ₀ : E)
  have iθ : compFin F E v (-θ) ∈ intLoc F E v := by
    rw [map_neg]; exact neg_mem (tmul_mem_intLoc (show evFin F v 1 ∈ _ by rw [map_one]; exact one_mem _) θ₀)
  have b0 : Adj (cA σ) (incM F X.J) ((-θ) • 1) ((-cA σ θ) • 1) := Adj.one.smul (by rw [map_neg, cc])
  have hb0 : (-θ) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + (-cA σ θ) • 1 = -1 := by
    rw [← add_smul, ← neg_add, show θ + cA σ θ = inclR (F := F) (AF F) (θ₀ + σ θ₀ : E) from (map_add _ _ _).symm, hθ, map_one,
      neg_smul, one_smul]
  have pb0 := smul_mem_Pres hL iθ (one_mem (Pres v X))
  have lag := lag_of b0 hb0 g hg
  set b₀ := (-θ) • (1 : Matrix (Fin n) (Fin n) (AE F E))
  have pm := sub_mem hy hx
  obtain ⟨Nm, hNm⟩ := (ha _).1 pm
  obtain ⟨NM, hNM⟩ := (ha _).1 (add_mem hy (mul_mem pb0 pm))
  obtain ⟨NP, hNP⟩ := (ha _).1 (add_mem h1 h2)
  obtain ⟨NQ, hNQ⟩ := (ha _).1 (sub_mem (neg_mem h1) (mul_mem (add_mem h1 h2) pb0))
  obtain ⟨S, s1, s2⟩ := exists_skew (c := cInt σ v) (r := ρ) (G := G) (G' := H) (M := NM) (m := Nm) (P := NP) (Q := NQ)
    (fun z => Subtype.ext (by
      change sigR _ σ (sigR _ σ z.1) = z.1
      induction z.1 using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (hσ x)
      | add x y hx hy => simp only [map_add (f := _), hx, hy])) r1
    (fun i k => Subtype.ext (congrArg ι (by
      change σ (G₀ k i) = G₀ i k
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hG₀, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, hX.herm, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)))
    (inj (by
      rw [map_mul, map_one]
      change G₀.map ι * G'.map ι = 1
      rw [← Matrix.map_mul, mul_eq_one_comm.1 hG', Matrix.map_one _ (map_zero _) (map_one _)])) r2 r3
    (inj (by
      rw [map_add (f := _), jj, jj, hNm, hNM, ← eG, ← gram_fr, ← gram_fr, ← Matrix.add_mul, ← Matrix.mul_add,
        ← Matrix.map_add _ (map_add _), lag, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, map_zero]))
    (inj (by
      rw [map_add (f := _), map_mul, map_mul, hNm, hNM, hNP, hNQ, ← map_mul, ← map_mul, ← map_add (f := _), map_one, ← map_one (fr v a), ← h]
      congr 1
      noncomm_ring))
  let SA : Matrix (Fin n) (Fin n) (AE F E) := (a.1 * j S * (a⁻¹).1).map (sgE E v)
  have aS : At (evFin F v) SA := fun u hu => Matrix.ext fun i k => at_sgE _ u hu
  have fS : fr v a SA = j S := by
    rw [fr_apply, show SA.map (compFin F E v) = a.1 * j S * (a⁻¹).1 from Matrix.ext fun _ _ => comp_sgE _]
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Units.inv_mul_cancel_left]
  have sk : SAᵀ * incM F X.J + incM F X.J * SA.map (cA σ) = 0 := by
    have k1 := gram_fr (σ := σ) a (incM F X.J) SA 1
    have k2 := gram_fr (σ := σ) a (incM F X.J) 1 SA
    have k3 := congrArg j s1
    have k4 := jj S 1
    have k5 := jj 1 S
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, map_one, mapc_one, fS, eG,
      Matrix.map_one _ (map_zero (sigR (Fv F v) σ)) (map_one _), Matrix.map_one _ (map_zero (cInt σ v)) (map_one _)] at k1 k2 k4 k5
    rw [map_add (f := _), k4, k5, ← k1, ← k2, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.map_add _ (map_add _), map_zero] at k3
    have u1 : IsUnit a.1ᵀ := (Matrix.isUnit_transpose _).2 a.isUnit
    have u2 : IsUnit (a.1.map (sigR (Fv F v) σ)) := a.isUnit.map (sigR (Fv F v) σ).mapMatrix
    rw [u2.mul_left_eq_zero, u1.mul_right_eq_zero] at k3
    refine Matrix.ext fun i k => eq_zero_of_at (v := v) (fun u hu => congrFun₂ (at_add (at_mul_left (M := SAᵀ)
      (fun u hu => congrArg Matrix.transpose (aS u hu)) _) (at_mul_right _ (N := SA.map (cA σ)) fun u hu => Matrix.ext fun i k => by
        change u • cA σ (SA i k) = 0
        rw [← map_smul, show u • SA i k = 0 from congrFun₂ (aS u hu) i k, map_zero]) u hu) i k) (congrFun₂ k3 i k)
  have am : At (evFin F v) (y - x) := by simpa using at_sub ay ax
  obtain ⟨t', pt, ht⟩ := exists_inv ha (f := y + (b₀ + SA) * (y - x)) (N := NM + S * Nm)
    (by rw [add_sub_right_comm]; exact at_add ay (at_mul_right _ am))
    (by rw [map_add (f := _), map_mul, hNm, hNM, ← fS, ← map_mul, ← map_add (f := _), add_mul, add_assoc]) s2
  exact ⟨b₀ + SA, _ + -SA, t', b0.add (by rw [Adj, mapc_neg, Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left sk),
    by rw [add_add_add_comm, add_neg_cancel, add_zero, hb0], add_mem pb0 ((ha _).2 ⟨S, fS.symm⟩), pt, ht⟩

end GlobalTheory.ThK.Dbl.Vf2

end
