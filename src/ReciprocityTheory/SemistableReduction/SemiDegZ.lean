module

public import ReciprocityTheory.SemistableReduction.SemiDegR

@[expose] public section

section -- merged from ReciprocityTheory.SemistableReduction.SemiDegW
section -- merged from ReciprocityTheory.SemistableReduction.SemiDegQ
section -- merged from ReciprocityTheory.SemistableReduction.SemiDegN
section -- merged from ReciprocityTheory.SemistableReduction.SemiDegM
section -- merged from ReciprocityTheory.SemistableReduction.SemiDegI
section -- merged from ReciprocityTheory.SemistableReduction.SemiDegH
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem isIntegralElt_add {K : Type} [Field K] [NumberField K] {x y : K} (hx : IsIntegralElt x)
    (hy : IsIntegralElt y) : IsIntegralElt (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; rfl⟩

theorem isIntegralElt_c {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) {x : K}
    (hx : IsIntegralElt x) : IsIntegralElt (S.c x) := by
  obtain ⟨z, rfl⟩ := hx
  exact ⟨RingOfIntegers.mapRingHom S.c z, rfl⟩

theorem norm_c {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (z : K) :
    Algebra.norm ℚ (S.c z) = Algebra.norm ℚ z := by
  have hs : Function.Surjective S.c := fun x => ⟨S.c x, S.c_invol x⟩
  let e : K ≃+* K := RingEquiv.ofBijective S.c ⟨S.c.injective, hs⟩
  let e' : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := e) (fun q => by simp [e])
  exact Algebra.norm_eq_of_algEquiv e' z

def projLt (K : Type) [Field K] [NumberField K] (r e : ℕ) : (Fin r → K) →ₗ[𝓞 K] (Fin r → K) where
  toFun x i := if (i : ℕ) < e then x i else 0
  map_add' x y := by
    funext i
    by_cases h : (i : ℕ) < e <;> simp [h]
  map_smul' a x := by
    funext i
    by_cases h : (i : ℕ) < e <;> simp [h]

theorem spanIdx_pair {K : Type} [Field K] [NumberField K] {r : ℕ} (j p : Fin r)
    (hjp : (j : ℕ) < p) (Gj Gp : Submodule (𝓞 K) (Fin r → K)) (hj : ∀ x ∈ Gj, IsAt j x)
    (hp : ∀ x ∈ Gp, IsAt p x) (x0 y : Fin r → K) (hx0 : x0 ∈ Gj) (hy : y ∈ Gp) :
    spanIdx (Gj ⊔ Gp) ![x0, y] = spanIdx Gj ![x0] * spanIdx Gp ![y] := by
  unfold spanIdx
  have hspan : Submodule.span (𝓞 K) (Set.range ![x0, y]) =
      Submodule.span (𝓞 K) {x0} ⊔ Submodule.span (𝓞 K) {y} := by
    rw [Matrix.range_cons_cons_empty, Submodule.span_insert]
  have h1 : Set.range ![x0] = {x0} := Matrix.range_cons_empty _ _
  have h2 : Set.range ![y] = {y} := Matrix.range_cons_empty _ _
  rw [hspan, h1, h2, Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup]
  set X0 := (Submodule.span (𝓞 K) {x0}).toAddSubgroup
  set Y := (Submodule.span (𝓞 K) {y}).toAddSubgroup
  have hX0 : X0 ≤ Gj.toAddSubgroup := by
    show Submodule.span (𝓞 K) {x0} ≤ Gj
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hx0
  have hY : Y ≤ Gp.toAddSubgroup := by
    show Submodule.span (𝓞 K) {y} ≤ Gp
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hy
  have key := AddSubgroup.relIndex_mul_relIndex _ _ _ (sup_le_sup_left hY X0)
    (sup_le_sup_right hX0 Gp.toAddSubgroup)
  rw [← key, mul_comm (X0.relIndex _)]
  congr 1
  · refine relIndex_sup_proj (projGe K r p).toAddMonoidHom X0 Y Gp.toAddSubgroup hY ?_ ?_
    · intro a ha
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 ha
      show projGe K r p (t • x0) = 0
      rw [map_smul]
      have : projGe K r p x0 = 0 := by
        funext i
        show (if (p : ℕ) ≤ i then x0 i else 0) = 0
        split_ifs with h
        · exact hj x0 hx0 i (fun hi => by rw [hi] at h; omega)
        · rfl
      rw [this, smul_zero]
    · intro x hx
      show projGe K r p x = x
      funext i
      show (if (p : ℕ) ≤ i then x i else 0) = x i
      split_ifs with h
      · rfl
      · exact (hp x hx i (fun hi => by rw [hi] at h; omega)).symm
  · rw [sup_comm X0, sup_comm Gj.toAddSubgroup]
    refine relIndex_sup_proj (projLt K r p).toAddMonoidHom Gp.toAddSubgroup X0 Gj.toAddSubgroup
      hX0 ?_ ?_
    · intro x hx
      show projLt K r p x = 0
      funext i
      show (if (i : ℕ) < p then x i else 0) = 0
      split_ifs with h
      · exact hp x hx i (fun hi => by rw [hi] at h; omega)
      · rfl
    · intro x hx
      show projLt K r p x = x
      funext i
      show (if (i : ℕ) < p then x i else 0) = x i
      split_ifs with h
      · rfl
      · exact (hj x hx i (fun hi => by rw [hi] at h; omega)).symm

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def hypG {K : Type} [Field K] {r : ℕ} (j p : Fin r) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun a b => (if a = j ∧ b = p then 1 else 0) + (if a = p ∧ b = j then 1 else 0)

def hypForm {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (j p : Fin r) :
    HermForm K r where
  c := S.c
  c_invol := S.c_invol
  c_emb := S.c_emb
  G := hypG j p
  G_herm a b := by
    simp only [hypG, Matrix.of_apply, map_add (f := _), apply_ite S.c, map_one, map_zero]
    rw [add_comm]
    congr 1 <;> simp only [and_comm]

theorem hypForm_h {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (j p : Fin r)
    (x y : Fin r → K) : (hypForm S j p).h x y = S.c (x j) * y p + S.c (x p) * y j := by
  rw [HermForm.h]
  have e : ∀ a, ∑ b, (hypForm S j p).c (x a) * (hypForm S j p).G a b * y b =
      (if a = j then S.c (x a) * y p else 0) + (if a = p then S.c (x a) * y j else 0) := by
    intro a
    simp only [hypForm, hypG, Matrix.of_apply, mul_add, add_mul, Finset.sum_add_distrib]
    congr 1
    · by_cases ha : a = j <;> simp [ha]
    · by_cases ha : a = p <;> simp [ha]
  rw [Finset.sum_congr rfl fun a _ => e a]
  simp [Finset.sum_add_distrib]

theorem abs_norm_neg {K : Type} [Field K] [NumberField K] (z : K) :
    |((Algebra.norm ℚ (-z) : ℚ) : ℝ)| = |((Algebra.norm ℚ z : ℚ) : ℝ)| := by
  rw [neg_eq_neg_one_mul, map_mul, Rat.cast_mul, abs_mul]
  have h1 : (-1 : K) = algebraMap ℚ K (-1) := by simp
  rw [h1, Algebra.norm_algebraMap]
  simp

theorem top_le_zero (hN : IntegralIndexStatement) {K : Type} [Field K] [NumberField K] {r : ℕ}
    (S : HermForm K r) (j p : Fin r) (hjp : (j : ℕ) < p) (Gj Gp : Submodule (𝓞 K) (Fin r → K))
    (hGj : Gj.FG) (hGp : Gp.FG) (hj : ∀ x ∈ Gj, IsAt j x) (hp : ∀ x ∈ Gp, IsAt p x)
    (hpair : ∀ x ∈ Gj, ∀ y ∈ Gp, IsIntegralElt (S.c (x j) * y p))
    (x0 y : Fin r → K) (hx0 : x0 ∈ Gj) (hx0j : x0 j ≠ 0) (hy : y ∈ Gp) (hyp : y p ≠ 0)
    (δ : (K →+* ℂ) → Fin r → ℝ) (d : ℝ) (hd : 0 < d) (hδj : ∀ σ, δ σ j = d)
    (hδp : ∀ σ, δ σ p = d⁻¹) (h0 : latDeg (diagMet δ) Gj ![x0] = 0) :
    latDeg (diagMet δ) Gp ![y] ≤ 0 := by
  have hjp' : j ≠ p := fun h => by rw [h] at hjp; omega
  have hx0p : x0 p = 0 := hj x0 hx0 p (Ne.symm hjp')
  have hyj : y j = 0 := hp y hy j hjp'

  set n : ℝ := (Fintype.card (K →+* ℂ) : ℝ)
  have e0 := h0
  rw [latDeg_single δ Gj j x0 (hj x0 hx0)] at e0
  simp only [hδj] at e0
  rw [sum_log_single (x0 j) hx0j d hd] at e0
  rw [latDeg_single δ Gp p y (hp y hy)]
  simp only [hδp]
  rw [sum_log_single (y p) hyp d⁻¹ (inv_pos.2 hd), Real.log_inv]

  set A : ℝ := (spanIdx Gj ![x0] : ℝ)
  set B : ℝ := (spanIdx Gp ![y] : ℝ)
  set X : ℝ := |((Algebra.norm ℚ (x0 j) : ℚ) : ℝ)|
  set Y : ℝ := |((Algebra.norm ℚ (y p) : ℚ) : ℝ)|
  have hA : 1 ≤ A := by
    have := spanIdx_ne_zero Gj ![x0] hGj (kBasisIn_single j Gj hj x0 hx0 hx0j)
    exact Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 this)
  have hB : 1 ≤ B := by
    have := spanIdx_ne_zero Gp ![y] hGp (kBasisIn_single p Gp hp y hy hyp)
    exact Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 this)
  have hX : 0 < X := by
    apply abs_pos.2
    exact_mod_cast (Algebra.norm_ne_zero_iff).2 hx0j
  have hY : 0 < Y := by
    apply abs_pos.2
    exact_mod_cast (Algebra.norm_ne_zero_iff).2 hyp
  have key : A * B ≤ X * Y := by
    set T := Gj ⊔ Gp
    have hT : T.FG := hGj.sup hGp
    have hbT : IsKBasisIn T ![x0, y] := by
      refine ⟨fun i => ?_, ?_, ?_⟩
      · fin_cases i
        · exact Submodule.mem_sup_left hx0
        · exact Submodule.mem_sup_right hy
      · rw [LinearIndependent.pair_iff]
        intro s t hst
        have h1 := congr_fun hst j
        have h2 := congr_fun hst p
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hx0p, hyj,
          mul_zero, add_zero, zero_add] at h1 h2
        exact ⟨(mul_eq_zero.1 h1).resolve_right hx0j, (mul_eq_zero.1 h2).resolve_right hyp⟩
      · intro z hz
        obtain ⟨z1, hz1, z2, hz2, rfl⟩ := Submodule.mem_sup.1 hz
        rw [Matrix.range_cons_cons_empty]
        have e1 : z1 = (z1 j / x0 j) • x0 := by
          funext a
          simp only [Pi.smul_apply, smul_eq_mul]
          by_cases ha : a = j
          · subst ha; field_simp
          · rw [hj z1 hz1 a ha, hj x0 hx0 a ha, mul_zero]
        have e2 : z2 = (z2 p / y p) • y := by
          funext a
          simp only [Pi.smul_apply, smul_eq_mul]
          by_cases ha : a = p
          · subst ha; field_simp
          · rw [hp z2 hz2 a ha, hp y hy a ha, mul_zero]
        rw [e1, e2]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hint : IsIntegralOn (hypForm S j p) T := by
      intro z hz w hw
      obtain ⟨z1, hz1, z2, hz2, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨w1, hw1, w2, hw2, rfl⟩ := Submodule.mem_sup.1 hw
      rw [hypForm_h]
      simp only [Pi.add_apply, hj z1 hz1 p (Ne.symm hjp'), hj w1 hw1 p (Ne.symm hjp'),
        hp z2 hz2 j hjp', hp w2 hw2 j hjp', add_zero, zero_add]
      refine isIntegralElt_add (hpair z1 hz1 w2 hw2) ?_
      have := isIntegralElt_c S (hpair w1 hw1 z2 hz2)
      rwa [map_mul, S.c_invol, mul_comm] at this
    have hgram : hGram (hypForm S j p) ![x0, y] =
        !![0, S.c (x0 j) * y p; S.c (y p) * x0 j, 0] := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [hGram, hypForm_h, hx0p, hyj]
    have hdet : (hGram (hypForm S j p) ![x0, y]).det = -((S.c (x0 j) * y p) * (S.c (y p) * x0 j)) := by
      rw [hgram, Matrix.det_fin_two_of]
      ring
    have hcx : S.c (x0 j) ≠ 0 := fun h => hx0j (S.c.injective (by rw [h, map_zero]))
    have hcy : S.c (y p) ≠ 0 := fun h => hyp (S.c.injective (by rw [h, map_zero]))
    have hdet0 : (hGram (hypForm S j p) ![x0, y]).det ≠ 0 := by
      rw [hdet, neg_ne_zero]
      exact mul_ne_zero (mul_ne_zero hcx hyp) (mul_ne_zero hcy hx0j)
    have hb := hN K r 2 (hypForm S j p) T ![x0, y] hT hbT hint hdet0
    rw [hdet, abs_norm_neg, map_mul, map_mul, map_mul, norm_c, norm_c] at hb
    push_cast at hb
    rw [spanIdx_pair j p hjp Gj Gp hj hp x0 y hx0 hy] at hb
    push_cast at hb
    have hb' : (A * B) ^ 2 ≤ (X * Y) ^ 2 :=
      le_of_le_of_eq hb (by simp only [X, Y]; rw [abs_mul, abs_mul, abs_mul]; ring)
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hb'
  have hlog : Real.log A + Real.log B ≤ Real.log X + Real.log Y := by
    rw [← Real.log_mul (by positivity) (by positivity), ← Real.log_mul hX.ne' hY.ne']
    exact Real.log_le_log (by positivity) key
  linarith

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def colMat {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) K :=
  Matrix.of fun a i => b i a

theorem hGram_eq {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) : hGram S b = ((colMat b).map S.c)ᵀ * S.G * colMat b := by
  ext i j
  simp only [hGram, HermForm.h, colMat, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem colMat_mulVec {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) (t : Fin k → K) :
    colMat b *ᵥ t = ∑ j, t j • b j := by
  funext a
  simp [colMat, mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem form_colMat {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) (t : Fin k → K) :
    (fun i => S.c (t i)) ⬝ᵥ (hGram S b *ᵥ t) = S.h (colMat b *ᵥ t) (colMat b *ᵥ t) := by
  rw [hGram_eq, hermForm_h_eq]
  simp only [formM]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  congr 1
  funext a
  rw [RingHom.map_mulVec]
  rfl

theorem hermForm_swap {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : S.c (S.h x y) = S.h y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [HermForm.h, map_sum, map_mul, S.c_invol]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [S.G_herm]
  ring

theorem quad_eq {r k : ℕ} (E : Matrix (Fin r) (Fin k) ℂ) (X : Matrix (Fin r) (Fin r) ℂ)
    (v : Fin k → ℂ) : star v ⬝ᵥ ((Eᴴ * X * E) *ᵥ v) = star (E *ᵥ v) ⬝ᵥ (X *ᵥ (E *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]

theorem quad_diag {r : ℕ} (d w : Fin r → ℂ) :
    star w ⬝ᵥ (diagonal d *ᵥ w) = ∑ a, d a * ((‖w a‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.ofReal_pow, ← Complex.conj_mul', Complex.star_def]
  ring

def midG {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) : Matrix (Fin r) (Fin r) K :=
  Matrix.diagonal fun a => if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then g a else 0

def midForm {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K) (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a) :
    HermForm K r where
  c := S.c
  c_invol := S.c_invol
  c_emb := S.c_emb
  G := midG r m g
  G_herm a b := by
    by_cases hab : a = b
    · subst hab
      simp only [midG, Matrix.diagonal_apply_eq]
      split_ifs with h
      · exact hfix a h.1 h.2
      · exact map_zero _
    · simp [midG, Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab)]

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem mid_le_zero (hN : IntegralIndexStatement) (hA : AbsDetStatement) {K : Type} [Field K]
    [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ) (g : Fin r → K)
    (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a)
    (Gm : Submodule (𝓞 K) (Fin r → K)) (hGm : Gm.FG)
    (hsupp : ∀ x ∈ Gm, ∀ a : Fin r, ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) → x a = 0)
    (hint : IsIntegralOn (midForm S m g hfix) Gm)
    (haniso : ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
      ∑ i, S.c (t i) * g i * t i = 0 → t = 0)
    (δ : (K →+* ℂ) → Fin r → ℝ) (hδ : ∀ σ a, 0 < δ σ a)
    (hδmid : ∀ σ (a : Fin r), m ≤ (a : ℕ) → (a : ℕ) + m < r → δ σ a = ‖σ (g a)‖)
    (C : Submodule (𝓞 K) (Fin r → K)) (hC : C ≤ Gm) (k : ℕ) (c : Fin k → Fin r → K)
    (hc : IsKBasisIn C c) : latDeg (diagMet δ) C c ≤ 0 := by
  set Sm := midForm S m g hfix with hSm
  have hCfg : C.FG := Submodule.FG.of_le hGm hC
  have hCint : IsIntegralOn Sm C := fun x hx y hy => hint x (hC hx) y (hC hy)

  have hSmh : ∀ z : Fin r → K, (∀ a : Fin r, ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) → z a = 0) →
      Sm.h z z = ∑ a, S.c (z a) * g a * z a := by
    intro z hz
    simp only [HermForm.h, hSm, midForm, midG, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · rfl
    · rw [hz a (by omega)]
      simp
  have hdet : (hGram Sm c).det ≠ 0 := by
    intro h0
    obtain ⟨t, ht0, ht⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    set z := colMat c *ᵥ t with hz
    have hzsupp : ∀ a : Fin r, ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) → z a = 0 := by
      intro a ha
      rw [hz, colMat_mulVec, Finset.sum_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Pi.smul_apply, hsupp _ (hC (hc.1 j)) a ha, smul_zero]
    have h1 : Sm.h z z = 0 := by
      rw [hz, ← form_colMat, ht]
      simp
    rw [hSmh z hzsupp] at h1
    have h2 := haniso z hzsupp h1
    rw [hz, colMat_mulVec] at h2
    exact ht0 (funext (Fintype.linearIndependent_iff.1 hc.2.1 t h2))
  have hidx := hN K r k Sm C c hCfg hc hCint hdet
  have hDpd : ∀ σ, (diagMet δ σ).PosDef := fun σ =>
    Matrix.posDef_diagonal_iff.2 fun a => by exact_mod_cast hδ σ a

  have hσ : ∀ σ : K →+* ℂ, ‖σ (hGram Sm c).det‖ ≤ (gramC (diagMet δ σ) σ c).det.re := by
    intro σ
    set E := embMat σ c with hE
    have hEc : ((colMat c).map S.c)ᵀ.map σ = Eᴴ := by
      ext a b
      simp [hE, embMat, colMat, Matrix.conjTranspose_apply, S.c_emb]
    have hC' : (hGram Sm c).map σ = Eᴴ * (midG r m g).map σ * E := by
      rw [hGram_eq, Matrix.map_mul, Matrix.map_mul]
      simp only [hSm, midForm]
      rw [hEc]
      rfl
    have hGσ : (midG r m g).map σ =
        diagonal fun a : Fin r => σ (if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then g a else 0) := by
      simp only [midG]
      rw [Matrix.diagonal_map (map_zero σ)]
    have hherm : ((hGram Sm c).map σ).IsHermitian := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply, hGram, Matrix.of_apply]
      rw [← hermForm_swap Sm (c j) (c i), Sm.c_emb]
      rfl
    have hineq : ∀ v : Fin k → ℂ, ‖star v ⬝ᵥ (((hGram Sm c).map σ) *ᵥ v)‖ ≤
        (star v ⬝ᵥ ((gramC (diagMet δ σ) σ c) *ᵥ v)).re := by
      intro v
      rw [hC', gramC_eq, quad_eq, quad_eq, hGσ]
      simp only [diagMet]
      rw [quad_diag, quad_diag]
      calc ‖∑ a : Fin r, σ (if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then g a else 0) *
              ((‖(E *ᵥ v) a‖ ^ 2 : ℝ) : ℂ)‖
          ≤ ∑ a : Fin r, ‖σ (if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then g a else 0) *
              ((‖(E *ᵥ v) a‖ ^ 2 : ℝ) : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ a : Fin r, δ σ a * ‖(E *ᵥ v) a‖ ^ 2 := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            gcongr
            split_ifs with h
            · rw [hδmid σ a h.1 h.2]
            · simp only [map_zero, norm_zero]
              exact (hδ σ a).le
        _ = (∑ a : Fin r, ((δ σ a : ℝ) : ℂ) * ((‖(E *ᵥ v) a‖ ^ 2 : ℝ) : ℂ)).re := by
            rw [Complex.re_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Complex.ofReal_mul, Complex.ofReal_re]
    have h5 := hA k (gramC (diagMet δ σ) σ c) ((hGram Sm c).map σ)
      (gramC_posDef S _ (hDpd σ) σ c hc.2.1) hherm hineq
    rwa [show ((hGram Sm c).map σ).det = σ (hGram Sm c).det from (RingHom.map_det σ _).symm] at h5
  have hN0 : 0 < |((Algebra.norm ℚ (hGram Sm c).det : ℚ) : ℝ)| := by
    apply abs_pos.2
    exact_mod_cast (Algebra.norm_ne_zero_iff).2 hdet
  have hsum : Real.log |((Algebra.norm ℚ (hGram Sm c).det : ℚ) : ℝ)| ≤
      ∑ σ : K →+* ℂ, Real.log (gramC (diagMet δ σ) σ c).det.re := by
    rw [← sum_log_norm_emb]
    refine Finset.sum_le_sum fun σ _ => Real.log_le_log ?_ (hσ σ)
    apply norm_pos_iff.2
    intro h0
    exact hdet (σ.injective (by rw [h0, map_zero]))
  have hone : 1 ≤ (spanIdx C c : ℝ) :=
    Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 (spanIdx_ne_zero C c hCfg hc))
  have hidx' : 2 * Real.log (spanIdx C c : ℝ) ≤ Real.log |((Algebra.norm ℚ (hGram Sm c).det : ℚ) : ℝ)| := by
    have := Real.log_le_log (by positivity) hidx
    rwa [Real.log_pow] at this
  unfold latDeg
  unfold spanIdx at hidx'
  linarith

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem gr_at {K : Type} [Field K] [NumberField K] {r : ℕ} (Lp : Submodule (𝓞 K) (Fin r → K))
    (j : Fin r) : ∀ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j), IsAt j x := by
  rintro _ ⟨y, ⟨_, hy⟩, rfl⟩ a ha
  show (if (j : ℕ) ≤ a then y a else 0) = 0
  split_ifs with h
  · exact hy a (by have : (a : ℕ) ≠ j := fun e => ha (Fin.ext e); omega)
  · rfl

theorem exists_at {K : Type} [Field K] [NumberField K] {r : ℕ} (Lp : Submodule (𝓞 K) (Fin r → K))
    (hsp : ∀ v : Fin r → K, ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Lp) (j : Fin r) :
    ∃ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j), x j ≠ 0 := by
  obtain ⟨a, ha, hav⟩ := hsp (Pi.single j 1)
  have hcut : a • (Pi.single j 1 : Fin r → K) ∈ cutSub K r (j + 1) := by
    intro i hi
    have : i ≠ j := fun e => by rw [e] at hi; omega
    simp [this]
  refine ⟨projGe K r j (a • Pi.single j 1), ⟨_, ⟨hav, hcut⟩, rfl⟩, ?_⟩
  show (if (j : ℕ) ≤ j then (a • (Pi.single j 1 : Fin r → K)) j else 0) ≠ 0
  rw [if_pos le_rfl]
  simpa using ha

theorem pair_int {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K) (h2m : 2 * m ≤ r) (Lp : Submodule (𝓞 K) (Fin r → K))
    (hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y))
    (j : Fin r) (hj : (j : ℕ) < m) :
    ∀ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j),
      ∀ y ∈ (Lp ⊓ cutSub K r (Fin.rev j + 1)).map (projGe K r (Fin.rev j)),
        IsIntegralElt (S.c (x j) * y (Fin.rev j)) := by
  rintro _ ⟨x, ⟨hxL, hxc⟩, rfl⟩ _ ⟨y, ⟨hyL, hyc⟩, rfl⟩
  have hrev := Fin.val_rev j
  have hj' := j.isLt
  have e1 : projGe K r j x j = x j := by
    show (if (j : ℕ) ≤ j then x j else 0) = x j
    rw [if_pos le_rfl]
  have e2 : projGe K r (Fin.rev j) y (Fin.rev j) = y (Fin.rev j) := by
    show (if ((Fin.rev j : Fin r) : ℕ) ≤ (Fin.rev j : Fin r) then y (Fin.rev j) else 0) = _
    rw [if_pos le_rfl]
  rw [e1, e2]
  have h := hint x hxL y hyL
  rw [formM_witt, Finset.sum_eq_single j] at h
  · rwa [wVal_outer r m g j (Or.inl hj), wPart_outer r m j (Or.inl hj), one_mul] at h
  · intro a _ ha
    by_cases hlt : (a : ℕ) < j
    · have hao : (a : ℕ) < m ∨ r ≤ (a : ℕ) + m := Or.inl (by omega)
      rw [wPart_outer r m a hao]
      have : y (Fin.rev a) = 0 := hyc _ (by rw [Fin.val_rev, Fin.val_rev]; omega)
      rw [this, mul_zero, mul_zero]
    · have : x a = 0 := hxc a (by have : (a : ℕ) ≠ j := fun e => ha (Fin.ext e); omega)
      rw [this, map_zero, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem mid_supp {K : Type} [Field K] [NumberField K] {r : ℕ} (m : ℕ)
    (Lp : Submodule (𝓞 K) (Fin r → K)) :
    ∀ x ∈ (Lp ⊓ cutSub K r (r - m)).map (projGe K r m), ∀ a : Fin r,
      ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) → x a = 0 := by
  rintro _ ⟨y, ⟨_, hy⟩, rfl⟩ a ha
  show (if m ≤ (a : ℕ) then y a else 0) = 0
  split_ifs with h
  · exact hy a (by omega)
  · rfl

theorem mid_int {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K) (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a)
    (Lp : Submodule (𝓞 K) (Fin r → K))
    (hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y)) :
    IsIntegralOn (midForm S m g hfix) ((Lp ⊓ cutSub K r (r - m)).map (projGe K r m)) := by
  rintro _ ⟨x, ⟨hxL, hxc⟩, rfl⟩ _ ⟨y, ⟨hyL, hyc⟩, rfl⟩
  have h := hint x hxL y hyL
  convert h using 1
  rw [formM_witt]
  simp only [HermForm.h, midForm, midG, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha := a.isLt
  show (if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then
      S.c (if m ≤ (a : ℕ) then x a else 0) * g a * (if m ≤ (a : ℕ) then y a else 0)
      else 0) = _
  by_cases hmid : m ≤ (a : ℕ) ∧ (a : ℕ) + m < r
  · have ho : ¬ ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) := by omega
    simp only [if_pos hmid, if_pos hmid.1]
    rw [wVal_mid r m g a ho, wPart_mid r m a ho]
    ring
  · rw [if_neg hmid]
    by_cases hlt : (a : ℕ) < m
    · have ho : (a : ℕ) < m ∨ r ≤ (a : ℕ) + m := Or.inl hlt
      rw [wPart_outer r m a ho]
      have : y (Fin.rev a) = 0 := hyc _ (by rw [Fin.val_rev]; omega)
      rw [this, mul_zero, mul_zero]
    · have : x a = 0 := hxc a (by omega)
      rw [this, map_zero, zero_mul]

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem cutSub_zero (K : Type) [Field K] [NumberField K] (r : ℕ) : cutSub K r 0 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  funext i
  exact hx i (Nat.zero_le _)

theorem cutSub_self (K : Type) [Field K] [NumberField K] (r : ℕ) : cutSub K r r = ⊤ := by
  rw [eq_top_iff]
  intro x _ i hi
  exact absurd i.isLt (by omega)

theorem flag_base {K : Type} [Field K] [NumberField K] {r : ℕ}
    (D : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (Lp : Submodule (𝓞 K) (Fin r → K)) :
    ∀ B ≤ Lp ⊓ cutSub K r 0, ∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b →
      latDeg D B b ≤ 0 := by
  intro B hB k b hb
  have hB0 : B = ⊥ := eq_bot_iff.2 (hB.trans (inf_le_right.trans (by rw [cutSub_zero])))
  subst hB0
  have hk := kBasisIn_bot_eq b hb
  subst hk
  exact (latDeg_zero_fam D ⊥ b hb).le

theorem flag_step (hE : GradedExtStatement) {K : Type} [Field K] [NumberField K] {r : ℕ}
    (δ : (K →+* ℂ) → Fin r → ℝ) (hδ : ∀ σ i, 0 < δ σ i) (Lp : Submodule (𝓞 K) (Fin r → K))
    (hLp : Lp.FG) (e' e : ℕ)
    (hP : ∀ B ≤ Lp ⊓ cutSub K r e', ∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b →
      latDeg (diagMet δ) B b ≤ 0)
    (hG : ∀ C ≤ (Lp ⊓ cutSub K r e).map (projGe K r e'), ∀ (k : ℕ) (c : Fin k → Fin r → K),
      IsKBasisIn C c → latDeg (diagMet δ) C c ≤ 0) :
    ∀ B ≤ Lp ⊓ cutSub K r e, ∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b →
      latDeg (diagMet δ) B b ≤ 0 := by
  intro B hB k b hb
  have hBfg : B.FG := Submodule.FG.of_le hLp (hB.trans inf_le_left)
  obtain ⟨k0, b0, hb0⟩ := exists_kBasisIn (B ⊓ cutSub K r e')
  obtain ⟨k1, b1, hb1⟩ := exists_kBasisIn (B.map (projGe K r e'))
  have h := hE K r e' k k0 k1 δ B b b0 b1 hδ hBfg hb hb0 hb1
  have h0 := hP (B ⊓ cutSub K r e') (inf_le_inf_right _ (hB.trans inf_le_left)) k0 b0 hb0
  have h1 := hG (B.map (projGe K r e')) (Submodule.map_mono hB) k1 b1 hb1
  linarith

theorem adapted_semistable (hB : LatDegBasisStatement) (hN : IntegralIndexStatement)
    (hA : AbsDetStatement) (hE : GradedExtStatement) {K : Type} [Field K] [NumberField K]
    {r : ℕ} (S : HermForm K r) (m : ℕ) (g : Fin r → K) (h2m : 2 * m ≤ r)
    (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a)
    (hg0 : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0)
    (haniso : ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
      ∑ i, S.c (t i) * g i * t i = 0 → t = 0)
    (Lp : Submodule (𝓞 K) (Fin r → K)) (hLp : Lp.FG)
    (hsp : ∀ v : Fin r → K, ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Lp)
    (hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y)) :
    ∃ dd : Fin r → ℝ, (∀ i, 0 < dd i) ∧ ∀ B ≤ Lp, ∀ (k : ℕ) (b : Fin k → Fin r → K),
      IsKBasisIn B b → latDeg (diagMet (adMet r m g dd)) B b ≤ 0 := by
  classical
  choose x0 hx0 hx0j using exists_at Lp hsp
  have hn : (0 : ℝ) < (Fintype.card (K →+* ℂ) : ℝ) := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card (K →+* ℂ) : ℝ) with hn_def
  let Gr : Fin r → Submodule (𝓞 K) (Fin r → K) := fun j =>
    (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j)
  have hGrfg : ∀ j, (Gr j).FG := fun j => (Submodule.FG.of_le hLp inf_le_left).map _
  let dd : Fin r → ℝ := fun j => Real.exp ((2 / n) * (Real.log (spanIdx (Gr j) ![x0 j] : ℝ) -
    Real.log |((Algebra.norm ℚ (x0 j j) : ℚ) : ℝ)|))
  have hdd : ∀ j, 0 < dd j := fun j => Real.exp_pos _
  refine ⟨dd, hdd, ?_⟩
  set δ := adMet r m g dd with hδdef
  have hδ : ∀ σ a, 0 < δ σ a := adMet_pos r m g dd hdd hg0
  have hbot0 : ∀ j : Fin r, (j : ℕ) < m → latDeg (diagMet δ) (Gr j) ![x0 j] = 0 := by
    intro j hj
    rw [latDeg_single δ _ j (x0 j) (gr_at Lp j _ (hx0 j))]
    have hδj : ∀ σ, δ σ j = dd j := fun σ => by simp [hδdef, adMet, hj]
    simp only [hδj]
    rw [sum_log_single (x0 j j) (hx0j j) (dd j) (hdd j), Real.log_exp]
    field_simp
    ring

  have hGb : ∀ j : Fin r, (j : ℕ) < m → ∀ C ≤ Gr j, ∀ (k : ℕ) (c : Fin k → Fin r → K),
      IsKBasisIn C c → latDeg (diagMet δ) C c ≤ 0 := fun j hj C hC k c hc =>
    rankOne_le_zero hB δ hδ j (Gr j) (hGrfg j) (gr_at Lp j) (x0 j) (hx0 j) (hx0j j)
      (hbot0 j hj).le C hC k c hc
  have hGt : ∀ p : Fin r, r ≤ (p : ℕ) + m → ∀ C ≤ Gr p, ∀ (k : ℕ) (c : Fin k → Fin r → K),
      IsKBasisIn C c → latDeg (diagMet δ) C c ≤ 0 := by
    intro p hp C hC k c hc
    have hpr := p.isLt
    have hjv : ((Fin.rev p : Fin r) : ℕ) = r - (p + 1) := Fin.val_rev p
    have hj : ((Fin.rev p : Fin r) : ℕ) < m := by omega
    have hpj : Fin.rev (Fin.rev p) = p := Fin.rev_rev p
    have hjp : ((Fin.rev p : Fin r) : ℕ) < p := by omega
    have hpair := pair_int S m g h2m Lp hint (Fin.rev p) hj
    rw [hpj] at hpair
    have hδj : ∀ σ, δ σ (Fin.rev p) = dd (Fin.rev p) := fun σ => by
      show adMet r m g dd σ (Fin.rev p) = _
      unfold adMet
      rw [if_pos hj]
    have hδp : ∀ σ, δ σ p = (dd (Fin.rev p))⁻¹ := fun σ => by
      have h1 : ¬ (p : ℕ) < m := by omega
      simp [hδdef, adMet, h1, hp]
    have htop := top_le_zero hN S (Fin.rev p) p hjp (Gr (Fin.rev p)) (Gr p) (hGrfg _) (hGrfg p)
      (gr_at Lp _) (gr_at Lp p) hpair (x0 (Fin.rev p)) (x0 p) (hx0 _) (hx0j _) (hx0 p) (hx0j p)
      δ (dd (Fin.rev p)) (hdd _) hδj hδp (hbot0 _ hj)
    exact rankOne_le_zero hB δ hδ p (Gr p) (hGrfg p) (gr_at Lp p) (x0 p) (hx0 p) (hx0j p) htop
      C hC k c hc
  have hGm : ∀ C ≤ (Lp ⊓ cutSub K r (r - m)).map (projGe K r m), ∀ (k : ℕ)
      (c : Fin k → Fin r → K), IsKBasisIn C c → latDeg (diagMet δ) C c ≤ 0 := by
    intro C hC k c hc
    have hδmid : ∀ σ (a : Fin r), m ≤ (a : ℕ) → (a : ℕ) + m < r → δ σ a = ‖σ (g a)‖ := by
      intro σ a h1 h2
      have h1' : ¬ (a : ℕ) < m := by omega
      have h2' : ¬ r ≤ (a : ℕ) + m := by omega
      simp [hδdef, adMet, h1', h2']
    exact mid_le_zero hN hA S m g hfix _ ((Submodule.FG.of_le hLp inf_le_left).map _)
      (mid_supp m Lp) (mid_int S m g hfix Lp hint) haniso δ hδ hδmid C hC k c hc

  have P1 : ∀ e, e ≤ m → ∀ B ≤ Lp ⊓ cutSub K r e, ∀ (k : ℕ) (b : Fin k → Fin r → K),
      IsKBasisIn B b → latDeg (diagMet δ) B b ≤ 0 := by
    intro e
    induction e with
    | zero => intro _; exact flag_base _ Lp
    | succ e ih =>
      intro he
      exact flag_step hE δ hδ Lp hLp e (e + 1) (ih (by omega))
        (hGb ⟨e, by omega⟩ (by show e < m; omega))
  have P2 := flag_step hE δ hδ Lp hLp m (r - m) (P1 m le_rfl) hGm
  have P3 : ∀ t, t ≤ m → ∀ B ≤ Lp ⊓ cutSub K r (r - m + t), ∀ (k : ℕ)
      (b : Fin k → Fin r → K), IsKBasisIn B b → latDeg (diagMet δ) B b ≤ 0 := by
    intro t
    induction t with
    | zero => intro _; simpa using P2
    | succ t ih =>
      intro ht
      exact flag_step hE δ hδ Lp hLp (r - m + t) (r - m + t + 1) (ih (by omega))
        (hGt ⟨r - m + t, by omega⟩ (by show r ≤ r - m + t + m; omega))
  intro B hB k b hb
  have hrm : r - m + m = r := by omega
  have := P3 m le_rfl
  rw [hrm, cutSub_self, inf_top_eq] at this
  exact this B hB k b hb

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem half_not_integral {K : Type} [Field K] [NumberField K] : ¬ IsIntegralElt ((2 : K)⁻¹) := by
  rintro ⟨z, hz⟩
  have hint : IsIntegral ℤ ((2 : K)⁻¹) := by
    rw [← hz]
    exact NumberField.RingOfIntegers.isIntegral_coe z
  have e : ((2 : K)⁻¹) = algebraMap ℚ K ((2 : ℚ)⁻¹) := by simp
  rw [e, isIntegral_algebraMap_iff ] at hint
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hm' : (m : ℚ) = 2⁻¹ := by simpa using hm
  have h2 : ((m * 2 : ℤ) : ℚ) = 1 := by
    push_cast
    rw [hm']
    norm_num
  have h3 : m * 2 = 1 := by exact_mod_cast h2
  omega

theorem no_line {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : L.FG) (x : Fin r → K) (hx : x ≠ 0) (hline : ∀ t : K, t • x ∈ L) : False := by
  classical
  obtain ⟨S, hS⟩ := hL
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨⟨b, hb⟩, hbint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (S.biUnion fun v => Finset.univ.image v)
  have hb0 : (b : K) ≠ 0 := by
    intro h0
    have : b = 0 := by exact_mod_cast h0
    exact nonZeroDivisors.ne_zero hb this
  have hgen : ∀ v ∈ S, ∀ j, IsIntegralElt ((b : K) * v j) := by
    intro v hv j
    obtain ⟨z, hz⟩ := hbint (v j) (Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩)
    refine ⟨z, ?_⟩
    show algebraMap (𝓞 K) K z = _
    rw [hz, Algebra.smul_def]
  have hall : ∀ w ∈ L, ∀ j, IsIntegralElt ((b : K) * w j) := by
    intro w hw
    rw [← hS] at hw
    induction hw using Submodule.span_induction with
    | mem v hv => exact hgen v hv
    | zero => intro j; exact ⟨0, by simp⟩
    | add v w _ _ hv hw =>
      intro j
      obtain ⟨z1, hz1⟩ := hv j
      obtain ⟨z2, hz2⟩ := hw j
      refine ⟨z1 + z2, ?_⟩
      push_cast
      rw [Pi.add_apply, mul_add]
      exact congrArg₂ (· + ·) hz1 hz2
    | smul a v _ hv =>
      intro j
      obtain ⟨z, hz⟩ := hv j
      refine ⟨a * z, ?_⟩
      push_cast
      rw [Pi.smul_apply, Algebra.smul_def]
      calc (a : K) * (z : K) = (a : K) * ((b : K) * v j) := congrArg (fun q => (a : K) * q) hz
        _ = (b : K) * (algebraMap (𝓞 K) K a * v j) := by
          show (a : K) * ((b : K) * v j) = (b : K) * ((a : K) * v j)
          ring
  have h1 := hall _ (hline ((2 * (b : K) * x i)⁻¹)) i
  apply half_not_integral (K := K)
  convert h1 using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

theorem hermForm_smul_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (t : K) (x y : Fin r → K) : S.h (t • x) y = S.c t * S.h x y := by
  rw [HermForm.h, HermForm.h, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem detG_ne_zero {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : IsLattice L) (hSD : IsSelfDual S L) :
    S.G.det ≠ 0 := by
  intro hdet
  have hdetT : S.Gᵀ.det = 0 := by rw [Matrix.det_transpose]; exact hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  have hw0 : (fun a => S.c (v a)) ≠ 0 := by
    intro h
    apply hv0
    funext a
    have h1 := congrArg S.c (congrFun h a)
    simpa [S.c_invol] using h1
  have hzero : ∀ y, S.h (fun a => S.c (v a)) y = 0 := by
    intro y
    simp only [HermForm.h, S.c_invol]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro b _
    have hb := congrFun hv b
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at hb
    rw [← Finset.sum_mul]
    have h2 : ∑ a, v a * S.G a b = 0 := by
      rw [← hb]
      exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    rw [h2, zero_mul]
  apply no_line L hL.1 _ hw0
  intro t
  apply hSD.2
  intro y _
  rw [hermForm_smul_left, hzero, mul_zero]
  exact ⟨0, by simp⟩

end ReciprocityTheory.MultiplicativeHeights.SemiPt
