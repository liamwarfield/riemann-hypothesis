module

public import Formalism.LocalToGlobal.Columns.QthExistsBound

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.QthCloseScl
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Close

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq0 : (q : E) ≠ 0)

theorem qth_vq_le : P.valuation E (q : E) ≤ 1 := by
  exact (qth_intAt_iff P _).1 ⟨(q : 𝓞 E), 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h),
    by simp⟩

theorem qth_mulVec {m : ℕ} (W : Sp E m ≃ₗ[E] Sp E m) (x : Sp E m) :
    W x = x + (((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1).mulVec x := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, toGLm_mulVec]
  abel

include hq0 in
theorem qth_close_scl {m : ℕ} (e : ℕ → ℤ) (he : ∀ l, e l = 0 ∨ e l = 1) (W : Sp E m ≃ₗ[E] Sp E m)
    (hW : ∀ i j, P.valuation E ((((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i j) ≤ P.valuation E (q : E))
    {x : Sp E m} (hx : x ∈ LocE.sclLat P q m e) : W x ∈ LocE.sclLat P q m e := by
  rw [ciMem_sclLat] at hx ⊢
  intro l
  rw [qth_intAt_iff, qth_mulVec W x]
  set M := ((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hM
  have hyj : ∀ j : Fin m, P.valuation E (((q : E) ^ e j.1)⁻¹ * x j) ≤ 1 :=
    fun j => (qth_intAt_iff P _).1 (hx j)
  have hqe : ∀ j : Fin m, P.valuation E ((q : E) ^ (e j.1)) ≤ 1 := by
    intro j
    rcases he j with h | h <;> rw [h]
    · simp
    · rw [zpow_one]
      exact qth_vq_le P q
  have hv0 : P.valuation E (q : E) ≠ 0 := by simpa using hq0
  have hcM : ∀ j, P.valuation E (((q : E) ^ e l.1)⁻¹ * (M - 1) l j) ≤ 1 := by
    intro j
    rcases he l with h | h <;> rw [h]
    · simp only [zpow_zero, inv_one, one_mul]
      exact (hW l j).trans (qth_vq_le P q)
    · rw [zpow_one, map_mul, map_inv₀]
      calc (P.valuation E (q : E))⁻¹ * P.valuation E ((M - 1) l j)
          ≤ (P.valuation E (q : E))⁻¹ * P.valuation E (q : E) := by gcongr; exact hW l j
        _ = 1 := inv_mul_cancel₀ hv0
  have hsplit : ((q : E) ^ e l.1)⁻¹ * (x + (M - 1).mulVec x) l = ((q : E) ^ e l.1)⁻¹ * x l +
      ∑ j, (((q : E) ^ e l.1)⁻¹ * (M - 1) l j) * (q : E) ^ (e j.1) * (((q : E) ^ e j.1)⁻¹ * x j) := by
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have hz : (q : E) ^ (e j.1) ≠ 0 := zpow_ne_zero _ hq0
    have h1 : (q : E) ^ (e j.1) * (((q : E) ^ (e j.1))⁻¹ * x j) = x j := by
      rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul]
    rw [mul_assoc _ ((q : E) ^ (e j.1)), h1]
    ring
  rw [hsplit]
  refine Valuation.map_add_le _ (hyj l) (Valuation.map_sum_le _ fun j _ => ?_)
  rw [map_mul, map_mul]
  exact mul_le_one' (mul_le_one' (hcM j) (hqe j)) (hyj j)

include hq0 in
theorem qth_close_std {m : ℕ} (W : Sp E m ≃ₗ[E] Sp E m)
    (hW : ∀ i j, P.valuation E ((((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i j) ≤ P.valuation E (q : E))
    {x : Sp E m} (hx : x ∈ stdAt E m P) : W x ∈ stdAt E m P := by
  rw [ciMem_stdAt] at hx ⊢
  intro i
  rw [qth_mulVec W x]
  have hxi : ∀ j, P.valuation E (x j) ≤ 1 := fun j => (qth_intAt_iff P _).1 (hx j)
  rw [qth_intAt_iff]
  show P.valuation E (x i + ∑ j, (((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i j * x j) ≤ 1
  refine Valuation.map_add_le _ (hxi i) (Valuation.map_sum_le _ fun j _ => ?_)
  rw [map_mul]
  exact mul_le_one' ((hW i j).trans (qth_vq_le P q)) (hxi j)

end Close

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Ext

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n c : ℕ}

theorem qth_ext_close (g : Sp E n ≃ₗ[E] Sp E n) (N : ℕ) (hg : lqPrinc P N g) (i l : Fin (n + c)) :
    P.valuation E ((((toGLm E (n + c) (twZrExt (c := c) g) : GL (Fin (n + c)) E) : Matrix (Fin (n + c)) (Fin (n + c)) E) - 1) i l) ≤
      WithZero.exp (-(N : ℤ)) := by
  have hcoe : ∀ W : Sp E (n + c) ≃ₗ[E] Sp E (n + c),
      ((toGLm E (n + c) W : GL (Fin (n + c)) E) : Matrix (Fin (n + c)) (Fin (n + c)) E) =
        LinearMap.toMatrix' (W : Sp E (n + c) →ₗ[E] Sp E (n + c)) := by
    intro W
    simp only [toGLm, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv,
      MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk,
      Units.coe_map, MonoidHom.coe_coe]
    rfl
  set u : Fin (n + c) → E := Pi.single l 1 with hu0
  have hpi : ∀ y : Fin n → E, (Loc.inX E n c y) i = if h : (i : ℕ) < n then y ⟨i, h⟩ else 0 := by
    intro y
    simp only [Loc.inX, LinearMap.pi_apply]
    split_ifs <;> rfl
  have hval : ((twZrExt (c := c) g) u) i =
      Loc.inX E n c (g (LinearMap.funLeft E E (Fin.castAdd c) u)) i +
        (u i - Loc.inX E n c (LinearMap.funLeft E E (Fin.castAdd c) u) i) := by
    rw [twZrExt_apply]
    rfl
  rw [hcoe, Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, ← hu0, hval, hpi, hpi]
  by_cases hi : (i : ℕ) < n
  · rw [dite_eq_left hi, dite_eq_left hi]
    have hu : (LinearMap.funLeft E E (Fin.castAdd c)) u ⟨i, hi⟩ = u i := rfl
    rw [hu, sub_self, add_zero]
    by_cases hl : (l : ℕ) < n
    · have hu' : LinearMap.funLeft E E (Fin.castAdd c) u = Pi.single (⟨l, hl⟩ : Fin n) 1 := by
        ext j
        simp [hu0, LinearMap.funLeft_apply, Pi.single_apply, Fin.ext_iff]
      rw [hu']
      have h1 : (1 : Matrix (Fin (n + c)) (Fin (n + c)) E) i l =
          (1 : Matrix (Fin n) (Fin n) E) ⟨i, hi⟩ ⟨l, hl⟩ := by
        simp [Matrix.one_apply, Fin.ext_iff]
      rw [h1]
      have h2 := hg ⟨i, hi⟩ ⟨l, hl⟩
      rw [Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe] at h2
      exact h2
    · have hu' : LinearMap.funLeft E E (Fin.castAdd c) u = 0 := by
        ext j
        simp only [hu0, LinearMap.funLeft_apply, Pi.single_apply, Pi.zero_apply, Function.comp_apply]
        rw [if_neg]
        intro h
        apply hl
        rw [← h]
        exact j.isLt
      have h1 : (1 : Matrix (Fin (n + c)) (Fin (n + c)) E) i l = 0 := by
        rw [Matrix.one_apply_ne]
        intro h
        apply hl
        rw [← h]
        exact hi
      rw [hu', map_zero, Pi.zero_apply, h1, sub_zero, map_zero]
      exact zero_le'
  · rw [dite_eq_right hi, dite_eq_right hi, zero_add, sub_zero]
    have h3 : u i - (1 : Matrix (Fin (n + c)) (Fin (n + c)) E) i l = 0 := by
      simp [hu0, Pi.single_apply, Matrix.one_apply]
    rw [h3, map_zero]
    exact zero_le'

theorem qth_princ_inv {N : ℕ} (g : ↥(GLint E n P)) (hg : lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n)) :
    lqPrinc P N ((g⁻¹ : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) := by
  unfold lqPrinc at hg ⊢
  intro i j
  set A := LinearMap.toMatrix' ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) with hA
  set B := LinearMap.toMatrix'
    ((((g⁻¹ : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) with hB
  have hBA : B * A = 1 := by
    rw [hA, hB, ← LinearMap.toMatrix'_comp]
    have hc : ((((g⁻¹ : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n).comp
        ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      have hx : ((((g⁻¹ * g : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n)) x = x := by
        rw [inv_mul_cancel]
        rfl
      exact hx
    rw [hc, LinearMap.toMatrix'_id]
  have hBle : ∀ a k, P.valuation E (B a k) ≤ 1 := by
    intro a k
    rw [hB, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
    have hs : (Pi.single k (1 : E) : Sp E n) ∈ stdAt E n P := by
      show _ ∈ localization₂ P.asIdeal (stdLat E n)
      rw [mem_localization_standardLattice]
      intro t
      rw [qth_intAt_iff]
      by_cases h : t = k
      · subst h
        simp
      · simp [Pi.single_apply, h]
    have hmem : ((g⁻¹ : GLint E n P) : Sp E n ≃ₗ[E] Sp E n) ∈ stabL E n (stdAt E n P) :=
      (g⁻¹ : GLint E n P).2
    have h2 := ((ChainCounts.mem_stabL_iff.1 hmem) _).2 hs
    have h3 := (mem_localization_standardLattice P _).1 h2 a
    rw [qth_intAt_iff] at h3
    exact h3
  have hBm : B - 1 = -(B * (A - 1)) := by
    rw [Matrix.mul_sub, hBA, Matrix.mul_one, neg_sub]
  rw [hBm, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
  refine Valuation.map_sum_le _ (fun k _ => ?_)
  rw [map_mul]
  calc _ ≤ 1 * P.valuation E ((A - 1) k j) := mul_le_mul' (hBle i k) le_rfl
    _ ≤ _ := by rw [one_mul]; exact hg k j

end Ext

end Formalism.L2.Col
