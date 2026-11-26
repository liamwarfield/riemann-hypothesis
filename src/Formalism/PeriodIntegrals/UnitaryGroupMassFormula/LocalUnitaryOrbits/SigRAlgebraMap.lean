module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfNorm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUniformizerHermitianIdeal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.FFInert2Holds

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SigRAlgebraMap
noncomputable section

namespace PI.OmLocU.UnN

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU.Orb
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def IsU (z : Fv F v ⊗[F] E) : Prop := ∃ w ∈ OEv (E := E) v, z * w = 1

theorem sigR_algebraMap (a : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) a) = algebraMap (Fv F v) (Fv F v ⊗[F] E) a := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]

theorem sigR_mem {z : Fv F v ⊗[F] E} (hz : z ∈ OEv (E := E) v) : sigR (Fv F v) σ z ∈ OEv (E := E) v := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, -, rfl⟩ := hx
    rw [sigR_inclR]
    have hb : IsIntegral ℤ (σ (b : E)) := by
      simpa using (b.isIntegral_coe).map (σ.toRingHom.toIntAlgHom)
    exact gen_mem v ⟨σ (b : E), hb⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    have h1 : r • x = algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) * x := by
      rw [← Algebra.smul_def]; rfl
    have h2 : algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) * sigR (Fv F v) σ x =
        r • sigR (Fv F v) σ x := by
      rw [← Algebra.smul_def]; rfl
    rw [h1, map_mul, sigR_algebraMap, h2]
    exact Submodule.smul_mem _ r hx

theorem hR_add_left' (x y z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (x + y) z = hR (Fv F v) σ J x z + hR (Fv F v) σ J y z := by
  simp only [hR, hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hR_add_right' (x y z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (y + z) = hR (Fv F v) σ J x y + hR (Fv F v) σ J x z := by
  simp only [hR, hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hR_sub_left' (x y z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (x - y) z = hR (Fv F v) σ J x z - hR (Fv F v) σ J y z := by
  simp only [hR, hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hR_sum_left' {ι : Type} (s : Finset ι) (f : ι → Fin n → Fv F v ⊗[F] E) (z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (∑ k ∈ s, f k) z = ∑ k ∈ s, hR (Fv F v) σ J (f k) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact hR_zero_left _
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, hR_add_left', ih]

theorem splitG (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hsd : IsSDLoc σ J v Λ) {ι : Type} [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E)
    (hX : ∀ i, X i ∈ latLoc (E := E) v Λ) (hU : UniG σ J v X) (x : Fin n → Fv F v ⊗[F] E)
    (hx : x ∈ latLoc (E := E) v Λ) :
    ∃ c : ι → Fv F v ⊗[F] E, (∀ i, c i ∈ OEv (E := E) v) ∧ x - ∑ i, c i • X i ∈ PerpG σ J v Λ X := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let X' : TupV (E := E) v n (Fintype.card ι) := fun k => X (e.symm k)
  have hX' : X' ∈ LamT v Λ (Fintype.card ι) := fun k => hX _
  obtain ⟨w, hw0, hw⟩ := hU
  have hdet : (gramR (Fv F v) σ J X').det = (gramG σ J v X).det := by
    have : gramR (Fv F v) σ J X' = (gramG σ J v X).submatrix e.symm e.symm := by
      ext i j; rfl
    rw [this, det_submatrix_equiv_self]
  obtain ⟨c', hc'0, hc'⟩ := split σ J v Λ (oSub v) (fun c hc y hy => oSmul v Λ hL c hc y hy) hsd X' hX' w hw0
    (by rw [hdet]; exact hw) x hx
  refine ⟨fun i => c' (e i), fun i => hc'0 _, ?_⟩
  have hs : ∑ i, c' (e i) • X i = ∑ k, c' k • X' k := by
    rw [← e.symm.sum_comp]
    simp [X']
  rw [hs]
  refine ⟨hc'.1, fun i => ?_⟩
  have := hc'.2 (e i)
  simpa [X'] using this

end PI.OmLocU.UnN
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfRed
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open PI.VolStabSW PI.OmLocU.CntFF
open scoped TensorProduct

theorem prod_fin_rev (f : ℕ → ℝ) (n : ℕ) : ∀ a : ℕ, a ≤ n →
    ∏ j : Fin a, f (n - (j : ℕ)) = ∏ i ∈ Finset.Icc (n - a + 1) n, f i := by
  intro a
  induction a with
  | zero =>
    intro _
    rw [Finset.Icc_eq_empty (by omega)]
    simp
  | succ a ih =>
    intro ha
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega), show n - (a + 1) + 1 = n - a by omega,
      ← Finset.insert_Icc_add_one_left_eq_Icc (show n - a ≤ n by omega), Finset.prod_insert (by simp), mul_comm]

theorem prod_pow_rev (q : ℝ) (n : ℕ) : ∀ a : ℕ, a ≤ n →
    ∏ j : Fin a, q ^ (2 * (n - (j : ℕ)) - 1) = q ^ (2 * n * a - a ^ 2) := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega), ← pow_add]
    congr 1
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ha
    have e1 : 2 * (a + 1 + m) * a - a ^ 2 = a ^ 2 + 2 * a + 2 * m * a := by
      apply Nat.sub_eq_of_eq_add; ring
    have e2 : 2 * (a + 1 + m) * (a + 1) - (a + 1) ^ 2 = (a + 1) ^ 2 + 2 * m * (a + 1) := by
      apply Nat.sub_eq_of_eq_add; ring
    rw [e1, e2, show 2 * (a + 1 + m - a) - 1 = 2 * m + 1 by omega]
    ring

theorem inert_prod (q : ℝ) (hq : 0 < q) (n a : ℕ) (ha : a ≤ n) :
    ∏ j : Fin a, (q ^ (2 * (n - (j : ℕ)) - 1) - (-1) ^ (n - (j : ℕ)) * q ^ (n - (j : ℕ) - 1)) =
      q ^ (2 * n * a - a ^ 2) * ∏ i ∈ Finset.Icc (n - a + 1) n, (1 - (-1 : ℝ) ^ i * q ^ (-(i : ℤ))) := by
  set f : ℕ → ℝ := fun i => 1 - (-1 : ℝ) ^ i * q ^ (-(i : ℤ)) with hf
  have ht : ∀ j : Fin a, q ^ (2 * (n - (j : ℕ)) - 1) - (-1) ^ (n - (j : ℕ)) * q ^ (n - (j : ℕ) - 1) =
      q ^ (2 * (n - (j : ℕ)) - 1) * f (n - (j : ℕ)) := by
    intro j
    have hj : (j : ℕ) < n := lt_of_lt_of_le j.2 ha
    simp only [hf]
    have e : q ^ (2 * (n - (j : ℕ)) - 1) * q ^ (-((n - (j : ℕ) : ℕ) : ℤ)) = q ^ (n - (j : ℕ) - 1) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq.ne']
      congr 1
      push_cast [Nat.cast_sub (show 1 ≤ 2 * (n - (j : ℕ)) by omega), Nat.cast_sub hj.le,
        Nat.cast_sub (show 1 ≤ n - (j : ℕ) by omega)]
      ring
    rw [mul_sub, mul_one, ← e]
    ring
  rw [Finset.prod_congr rfl (fun j _ => ht j), Finset.prod_mul_distrib, prod_pow_rev q n a ha,
    prod_fin_rev f n a ha]

theorem split_prod (q : ℝ) (hq : 0 < q) (n a : ℕ) (ha : a ≤ n) :
    (∏ i : Fin a, (q ^ n - q ^ (i : ℕ))) * q ^ (a * (n - a)) =
      q ^ (2 * n * a - a ^ 2) * ∏ i ∈ Finset.Icc (n - a + 1) n, (1 - (1 : ℝ) ^ i * q ^ (-(i : ℤ))) := by
  set f : ℕ → ℝ := fun i => 1 - (1 : ℝ) ^ i * q ^ (-(i : ℤ)) with hf
  have ht : ∀ j : Fin a, q ^ n - q ^ (j : ℕ) = q ^ n * f (n - (j : ℕ)) := by
    intro j
    have hj : (j : ℕ) < n := lt_of_lt_of_le j.2 ha
    simp only [hf, one_pow, one_mul]
    have e : q ^ n * q ^ (-((n - (j : ℕ) : ℕ) : ℤ)) = q ^ (j : ℕ) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq.ne']
      congr 1
      push_cast [Nat.cast_sub hj.le]
      ring
    rw [mul_sub, mul_one, e]
  rw [Finset.prod_congr rfl (fun j _ => ht j), Finset.prod_mul_distrib, prod_fin_rev f n a ha,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have e : n * a + a * (n - a) = 2 * n * a - a ^ 2 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ha
    rw [show a + m - a = m by omega]
    symm; apply Nat.sub_eq_of_eq_add; ring
  rw [← e, pow_add]
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def RedU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = Ideal.absNorm v.asIdeal ∧
      ((etaV (E := E) v = -1 ∧ ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K)
          (J' : Matrix (Fin n) (Fin n) K) (T' : Matrix (Fin a) (Fin a) K),
          (∀ x, σ' (σ' x) = x) ∧ Module.finrank k K = 2 ∧ σ' ≠ AlgEquiv.refl ∧
          (∀ i j, σ' (J' j i) = J' i j) ∧ IsUnit J'.det ∧ (∀ i j, σ' (T' j i) = T' i j) ∧ IsUnit T'.det ∧
          Nat.card (clsU σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) =
            Nat.card {X : Fin a → Fin n → K // ffGram (σ' : K →+* K) J' X = T'}) ∨
       (etaV (E := E) v = 1 ∧ ∃ (J' : Matrix (Fin n) (Fin n) (k × k)) (T' : Matrix (Fin a) (Fin a) (k × k)),
          (∀ i j, (J' j i).swap = J' i j) ∧ IsUnit J'.det ∧ (∀ i j, (T' j i).swap = T' i j) ∧ IsUnit T'.det ∧
          Nat.card (clsU σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) =
            Nat.card {X : Fin a → Fin n → k × k //
              ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J' X = T'}))

theorem clsU_of (a : ℕ) (Y : TupV (E := E) v n a) (hR : RedU σ J ψ v Λ a Y) : ClsU σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have ha : a ≤ n := hG.2.2.2.2.1
  have hq := qv_pos v
  obtain ⟨k, _, _, hk, h⟩ := hR hG ϖ hϖ
  rcases h with ⟨hη, K, _, _, σ', J', T', hσ, h2, hne, hJ, hJu, hT, hTu, hc⟩ |
    ⟨hη, J', T', hJ, hJu, hT, hTu, hc⟩
  · rw [hc, fFInert2_holds k K σ' hσ h2 hne n a ha J' hJ hJu T' hT hTu, hk]
    unfold prodEta
    rw [hη]
    push_cast
    exact inert_prod (qv v) hq n a ha
  · rw [hc, fFSplit_holds k n a ha J' hJ hJu T' hT hTu, hk]
    unfold prodEta
    rw [hη]
    push_cast
    exact split_prod (qv v) hq n a ha

end PI.OmLocU
end
end
