module

public import Mathlib

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.DvrOfHeightOne
namespace PositivityTheory.HtPt.Gc

theorem dvr_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime] (h1 : q.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  have hdim : ringKrullDim (Localization.AtPrime q) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, h1]; rfl
  have hnf : ¬ IsField (Localization.AtPrime q) := fun hf => by
    rw [ringKrullDim_eq_zero_of_isField hf] at hdim
    exact zero_ne_one hdim
  have hic : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hk : Ring.KrullDimLE 1 (Localization.AtPrime q) := by
    rw [Ring.krullDimLE_iff, hdim]; rfl
  have hD : IsDedekindDomain (Localization.AtPrime q) := by
    have : Ring.DimensionLEOne (Localization.AtPrime q) :=
      ⟨fun {P} hP hP' => (Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hk) P hP hP'⟩
    exact {}
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q) hnf).out 1 3).2 hD

end PositivityTheory.HtPt.Gc
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.EqOfProdEq
open scoped Matrix TensorProduct
open Matrix

namespace PositivityTheory.HtPt.Rh

theorem epi : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B], (∀ b : B, b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) → Function.Surjective (algebraMap A B) := by
  intro A B _ _ _ _ h
  exact Algebra.isEpi_iff_surjective_algebraMap_of_finite.mp
    ((Algebra.isEpi_iff_forall_one_tmul_eq A B).mpr fun b => (h b).symm)

theorem eq_of_prod_eq {T : Type} [Fintype T] (f g : T → NNReal) (hle : ∀ t, f t ≤ g t)
    (h : ∏ t, f t = ∏ t, g t) (h0 : ∏ t, f t ≠ 0) (t : T) : f t = g t := by
  by_contra hne
  have hpos : ∀ i ∈ Finset.univ, 0 < f i := fun i _ =>
    pos_iff_ne_zero.mpr ((Finset.prod_ne_zero_iff.mp h0) i (Finset.mem_univ i))
  have hlt := Finset.prod_lt_prod₀ hpos (fun i _ => hle i)
    ⟨t, Finset.mem_univ t, lt_of_le_of_ne (hle t) hne⟩
  exact hlt.ne h

theorem grcount : ∀ (T S : Type) [Fintype T] [Fintype S] (a b : ℕ), 0 < a → 0 < b → ∀ (x D d : T → S → NNReal) (r : S → NNReal) (cA cN cO : NNReal), cN ≠ 0 → (∀ t s, x t s ≤ D t s) → ∏ t, ∏ s, D t s = cA → (∏ t, ∏ s, x t s) ^ (a * b) = cN ^ 2 → cA ^ (a * b) = cN ^ 2 → (∀ s, ∏ t, d t s ≤ r s) → ∏ s, r s = cO → ∏ t, ∏ s, d t s = (∏ t, ∏ s, x t s) ^ b → cO ^ a = cN ^ 2 → (∀ t s, D t s = x t s) ∧ ∀ s, ∏ t, d t s = r s := by
  intro T S _ _ a b ha hb x D d r cA cN cO hcN hxD hD hx hA hd hr hdx hOa
  have hab : a * b ≠ 0 := (Nat.mul_pos ha hb).ne'
  have hX : ∏ t, ∏ s, x t s = ∏ t, ∏ s, D t s := by
    rw [hD]
    exact (pow_left_inj₀ (by positivity) (by positivity) hab).mp (hx.trans hA.symm)
  have hX0 : ∏ t, ∏ s, x t s ≠ 0 := by
    intro h0
    rw [h0, zero_pow hab] at hx
    exact pow_ne_zero 2 hcN hx.symm
  have hrow : ∀ t, ∏ s, x t s = ∏ s, D t s :=
    PositivityTheory.HtPt.Rh.eq_of_prod_eq (fun t => ∏ s, x t s) (fun t => ∏ s, D t s)
      (fun t => Finset.prod_le_prod' fun s _ => hxD t s) hX hX0
  have hrow0 : ∀ t, ∏ s, x t s ≠ 0 := fun t =>
    (Finset.prod_ne_zero_iff.mp hX0) t (Finset.mem_univ t)
  have hxD' : ∀ t s, D t s = x t s := fun t s =>
    (PositivityTheory.HtPt.Rh.eq_of_prod_eq (x t) (D t) (hxD t) (hrow t) (hrow0 t) s).symm
  have hO : cO = ∏ t, ∏ s, d t s := by
    rw [hdx]
    apply (pow_left_inj₀ (by positivity) (by positivity) ha.ne').mp
    rw [hOa, ← pow_mul, mul_comm b a, hx]
  have hcol : ∏ s, ∏ t, d t s = ∏ s, r s := by
    rw [hr, hO, Finset.prod_comm]
  have hcol0 : ∏ s, ∏ t, d t s ≠ 0 := by
    rw [Finset.prod_comm, hdx]
    exact pow_ne_zero _ hX0
  exact ⟨hxD', PositivityTheory.HtPt.Rh.eq_of_prod_eq (fun s => ∏ t, d t s) r hd hcol hcol0⟩

end PositivityTheory.HtPt.Rh
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.SiuaNum
namespace PositivityTheory.HtPt.Siua

open Filter Topology

theorem expand {M : Type} [AddCommGroup M] {n : ℕ} (f : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => M) ℤ) (μ e : M)
    (x y : Fin n → ℤ) :
    f (fun i => x i • μ + y i • e) =
      ∑ s : Finset (Fin n), (∏ i, if i ∈ s then x i else y i) * f (fun i => if i ∈ s then μ else e) := by
  have hsum := f.map_add_univ (fun i => x i • μ) (fun i => y i • e)
  rw [show (fun i => x i • μ + y i • e) = (fun i => x i • μ) + (fun i => y i • e) from rfl, hsum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hpw : s.piecewise (fun i => x i • μ) (fun i => y i • e) =
      fun i => (if i ∈ s then x i else y i) • (if i ∈ s then μ else e) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  simp only [hpw, f.map_smul_univ, RingHom.id_apply, smul_eq_mul]

noncomputable def form {M : Type} [AddCommGroup M] {n : ℕ} (f : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => M) ℤ)
    (μ e : M) (x y : Fin n → ℚ) : ℚ :=
  ∑ s : Finset (Fin n), (∏ i, if i ∈ s then x i else y i) * (f (fun i => if i ∈ s then μ else e) : ℚ)

theorem form_cast {M : Type} [AddCommGroup M] {n : ℕ} (f : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => M) ℤ) (μ e : M)
    (x y : Fin n → ℤ) :
    (f (fun i => x i • μ + y i • e) : ℚ) = form f μ e (fun i => x i) (fun i => y i) := by
  rw [PositivityTheory.HtPt.Siua.expand]
  simp only [PositivityTheory.HtPt.Siua.form]
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1

theorem form_smul {M : Type} [AddCommGroup M] {n : ℕ} (f : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => M) ℤ) (μ e : M)
    (x y : Fin n → ℚ) (a : ℚ) :
    form f μ e (fun i => a * x i) (fun i => a * y i) = a ^ n * form f μ e x y := by
  simp only [PositivityTheory.HtPt.Siua.form, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hprod : ∏ i, (if i ∈ s then a * x i else a * y i) = a ^ n * ∏ i, (if i ∈ s then x i else y i) := by
    calc ∏ i, (if i ∈ s then a * x i else a * y i)
        = ∏ i, a * (if i ∈ s then x i else y i) :=
          Finset.prod_congr rfl fun i _ => (mul_ite _ _ _ _).symm
      _ = (∏ _i : Fin n, a) * ∏ i, (if i ∈ s then x i else y i) := Finset.prod_mul_distrib
      _ = a ^ n * ∏ i, (if i ∈ s then x i else y i) := by simp
  rw [hprod, mul_assoc]

theorem form_cont {M : Type} [AddCommGroup M] {n : ℕ} (f : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => M) ℤ) (μ e : M)
    (x : Fin n → ℚ) (y : Fin n → ℚ) : Continuous fun t : ℚ => form f μ e x (fun i => y i * t) := by
  simp only [PositivityTheory.HtPt.Siua.form]
  refine continuous_finsetSum _ fun s _ => ?_
  refine Continuous.mul (continuous_finsetProd _ fun i _ => ?_) continuous_const
  by_cases hi : i ∈ s
  · simp only [hi, ↓reduceIte]
    exact continuous_const
  · simp only [hi, ↓reduceIte]
    exact continuous_const.mul continuous_id

theorem siu_num : ∀ (M : Type) [AddCommGroup M] (d : ℕ) (f : MultilinearMap (RingHom.id ℤ) (fun _ : Fin (d + 1) => M) ℤ) (μ e : M), 0 < f (fun _ => μ) → ∃ t : ℚ, 0 < t ∧ ∀ (a : ℕ) (m : ℤ), 1 ≤ a → (m : ℚ) = a * t → ((d + 1 : ℕ) : ℤ) * f (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) ((2 * m) • e)) < f (fun _ => a • μ + m • e) := by
  intro M _ d f μ e hf
  obtain ⟨x2, hx2⟩ : ∃ x2 : Fin (d + 1) → ℚ, x2 = Fin.snoc (α := fun _ => ℚ) (fun _ : Fin d => (1 : ℚ)) 0 :=
    ⟨_, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ y2 : Fin (d + 1) → ℚ, y2 = Fin.snoc (α := fun _ => ℚ) (fun _ : Fin d => (1 : ℚ)) 2 :=
    ⟨_, rfl⟩
  have hc1 : Continuous fun t : ℚ =>
      PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) :=
    PositivityTheory.HtPt.Siua.form_cont f μ e _ (fun _ => 1)
  have hc2 : Continuous fun t : ℚ => PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t) :=
    PositivityTheory.HtPt.Siua.form_cont f μ e x2 y2
  have hc : Continuous fun t : ℚ =>
      PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) -
        ((d : ℚ) + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t) :=
    hc1.sub (continuous_const.mul hc2)
  have h10 : PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * 0) = (f (fun _ => μ) : ℚ) := by
    have h := PositivityTheory.HtPt.Siua.form_cast f μ e (fun _ => 1) (fun _ => 0)
    simp only [one_smul, zero_smul, add_zero, Int.cast_one, Int.cast_zero] at h
    simp only [mul_zero]
    exact h.symm
  have h20 : PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * 0) = 0 := by
    simp only [PositivityTheory.HtPt.Siua.form, mul_zero]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [Finset.prod_eq_zero (f := fun i => if i ∈ s then x2 i else 0) (Finset.mem_univ (Fin.last d))
      (by simp [hx2]), zero_mul]
  have hG0 : (0 : ℚ) < PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * 0) -
      ((d : ℚ) + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * 0) := by
    rw [h10, h20]
    simpa using hf
  have hev := (hc.tendsto 0).eventually (lt_mem_nhds hG0)
  obtain ⟨t, hGt, ht⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℚ) ∈ 𝓝[>] 0)).exists
  have hGt' : (0 : ℚ) < PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) -
      ((d : ℚ) + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t) := hGt
  refine ⟨t, ht, ?_⟩
  intro a m ha hm
  have hR : (f (fun _ => a • μ + m • e) : ℚ) =
      (a : ℚ) ^ (d + 1) * PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) := by
    have h := PositivityTheory.HtPt.Siua.form_cast f μ e (fun _ => (a : ℤ)) (fun _ => m)
    rw [← PositivityTheory.HtPt.Siua.form_smul]
    simp only [natCast_zsmul] at h
    rw [h]
    congr 1
    · funext i
      simp
    · funext i
      simp [hm]
  have hfun : (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) ((2 * m) • e)) =
      fun i => (Fin.snoc (α := fun _ => ℤ) (fun _ : Fin d => (a : ℤ)) 0 i) • μ +
        (Fin.snoc (α := fun _ => ℤ) (fun _ : Fin d => m) (2 * m) i) • e := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [natCast_zsmul]
  have hL : (f (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) ((2 * m) • e)) : ℚ) =
      (a : ℚ) ^ (d + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t) := by
    have h := PositivityTheory.HtPt.Siua.form_cast f μ e
      (Fin.snoc (α := fun _ => ℤ) (fun _ : Fin d => (a : ℤ)) 0)
      (Fin.snoc (α := fun _ => ℤ) (fun _ : Fin d => m) (2 * m))
    rw [← PositivityTheory.HtPt.Siua.form_smul, hfun, h]
    congr 1
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [hx2]
      · simp [hx2]
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hy2]
        simp only [Fin.snoc_last, Int.cast_mul, Int.cast_ofNat, hm]
        ring
      · simp [hy2, hm]
  have hpos : (0 : ℚ) < (a : ℚ) ^ (d + 1) := pow_pos (by exact_mod_cast (show 0 < a by omega)) _
  have hlt : ((d : ℚ) + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t) <
      PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) := by
    linarith
  rw [← Int.cast_lt (R := ℚ), Int.cast_mul, hL, hR]
  calc (((d + 1 : ℕ) : ℤ) : ℚ) * ((a : ℚ) ^ (d + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t))
      = (a : ℚ) ^ (d + 1) * (((d : ℚ) + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t)) := by
        push_cast
        ring
    _ < (a : ℚ) ^ (d + 1) * PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) :=
        mul_lt_mul_of_pos_left hlt hpos

end PositivityTheory.HtPt.Siua
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.CgSplit
namespace PositivityTheory.HtPt.Cg

open Matrix

theorem left_inv_of_residue {A : Type} [CommRing A] [IsLocalRing A] {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (M : Matrix m n A)
    (h : ∀ u, (M.map (IsLocalRing.residue A)).mulVec u = 0 → u = 0) : ∃ N : Matrix n m A, N * M = 1 := by
  have hi : LinearMap.ker (Matrix.toLin' (M.map (IsLocalRing.residue A))) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    exact h u (by simpa using hu)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hi
  have h1 : LinearMap.toMatrix' g * M.map (IsLocalRing.residue A) = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  choose l hl using fun i j => IsLocalRing.residue_surjective (LinearMap.toMatrix' g i j)
  have h2 : (Matrix.of l * M).map (IsLocalRing.residue A) = 1 := by
    rw [Matrix.map_mul, ← h1]
    congr 1
    ext i j
    exact hl i j
  have h3 : IsUnit (Matrix.of l * M).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, h2, det_one]
    exact one_ne_zero
  exact ⟨(Matrix.of l * M)⁻¹ * Matrix.of l, by rw [Matrix.mul_assoc, nonsing_inv_mul _ h3]⟩

theorem split_local : ∀ (A : Type) [CommRing A] [IsLocalRing A] (d : ℕ) (h a S : Matrix (Fin d) (Fin d) A), a * h - h.transpose * S * h - h.transpose * a.transpose = 0 → (∀ u : Fin d → IsLocalRing.ResidueField A, (h.map (IsLocalRing.residue A)).mulVec u = 0 → (a.transpose.map (IsLocalRing.residue A)).mulVec u = 0 → u = 0) → ∃ r₁ r₂ s₁ s₂ : Matrix (Fin d) (Fin d) A, r₁ * h + r₂ * a.transpose = 1 ∧ (a - h.transpose * S) * s₁ - h.transpose * s₂ = 1 ∧ h * r₁ + s₁ * (a - h.transpose * S) = 1 ∧ h * r₂ - s₁ * h.transpose = 0 ∧ a.transpose * r₁ + s₂ * (a - h.transpose * S) = 0 ∧ a.transpose * r₂ - s₂ * h.transpose = 1 := by
  intro A _ _ d h a S hiso hinj
  obtain ⟨N, hN⟩ := left_inv_of_residue (fromRows h a.transpose) (fun u hu => by
    rw [fromRows_map, fromRows_mulVec] at hu
    exact hinj u (funext fun i => congrFun hu (Sum.inl i)) (funext fun i => congrFun hu (Sum.inr i)))
  obtain ⟨x, y, rfl⟩ : ∃ x y, N = fromCols x y := ⟨_, _, (fromCols_toCols N).symm⟩
  rw [fromCols_mul_fromRows] at hN
  have hT : h.transpose * x.transpose + a * y.transpose = 1 := by
    have := congrArg Matrix.transpose hN
    simpa [transpose_add, transpose_mul] using this
  set b := a - h.transpose * S with hb
  set s₁ := y.transpose
  set s₂ := -(x.transpose + S * y.transpose) with hs₂
  have e2 : b * s₁ - h.transpose * s₂ = 1 := by
    rw [← hT, hb, hs₂]; noncomm_ring
  have e0 : b * h - h.transpose * a.transpose = 0 := by
    rw [← hiso, hb]; noncomm_ring
  set w := x * s₁ + y * s₂ with hw
  have e1 : (x - w * b) * h + (y + w * h.transpose) * a.transpose = 1 := by
    have : (x - w * b) * h + (y + w * h.transpose) * a.transpose =
      (x * h + y * a.transpose) - w * (b * h - h.transpose * a.transpose) := by noncomm_ring
    rw [this, hN, e0]; simp
  have e3 : (x - w * b) * s₁ + (y + w * h.transpose) * s₂ = 0 := by
    have : (x - w * b) * s₁ + (y + w * h.transpose) * s₂ =
      (x * s₁ + y * s₂) - w * (b * s₁ - h.transpose * s₂) := by noncomm_ring
    rw [this, e2, ← hw]; simp
  have hNM : fromBlocks (x - w * b) (y + w * h.transpose) b (-h.transpose) *
      fromBlocks h s₁ a.transpose s₂ = 1 := by
    rw [fromBlocks_multiply, e1, e3, ← fromBlocks_one]
    congr 1
    · rw [← e0]; noncomm_ring
    · rw [← e2]; noncomm_ring
  have hMN := mul_eq_one_comm.1 hNM
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hMN
  obtain ⟨f1, f2, f3, f4⟩ := hMN
  refine ⟨_, _, s₁, s₂, e1, e2, f1, ?_, f3, ?_⟩
  · rw [← f2]; noncomm_ring
  · rw [← f4]; noncomm_ring

end PositivityTheory.HtPt.Cg
end
