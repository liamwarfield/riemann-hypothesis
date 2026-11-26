module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.DedekindLFunctions
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WithZeroLeOneEqExp

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxGen
noncomputable section

open IsDedekindDomain

namespace Formalism.L2.SG.Pf.ProdEApprox

section DedekindLFunctions

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {n : ℕ}

end DedekindLFunctions

section Ent

variable {A : Type*} [CommRing A] {n : ℕ}

def EntIn (J : AddSubgroup A) (X : Matrix (Fin n) (Fin n) A) : Prop := ∀ i j, X i j ∈ J

theorem entIn_mul {J1 J2 J3 : AddSubgroup A} (h : ∀ x ∈ J1, ∀ y ∈ J2, x * y ∈ J3)
    {X Y : Matrix (Fin n) (Fin n) A} (hX : EntIn J1 X) (hY : EntIn J2 Y) : EntIn J3 (X * Y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => h _ (hX i k) _ (hY k j)

theorem entIn_add {J : AddSubgroup A} {X Y : Matrix (Fin n) (Fin n) A} (hX : EntIn J X) (hY : EntIn J Y) :
    EntIn J (X + Y) :=
  fun i j => J.add_mem (hX i j) (hY i j)

theorem entIn_neg {J : AddSubgroup A} {X : Matrix (Fin n) (Fin n) A} (hX : EntIn J X) : EntIn J (-X) :=
  fun i j => J.neg_mem (hX i j)

theorem pow_apply_eq_zero (f : Fin n → ℕ) {X : Matrix (Fin n) (Fin n) A} (hX : ∀ i j, f i ≤ f j → X i j = 0)
    (m : ℕ) : ∀ i j, f i < f j + m → (X ^ m) i j = 0 := by
  induction m with
  | zero =>
    intro i j h
    rw [pow_zero, Matrix.one_apply_ne]
    rintro rfl
    omega
  | succ m ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : f i < f k + m
    · rw [ih i k hk, zero_mul]
    · rw [hX k j (by omega), mul_zero]

theorem pow_eq_zero_of (f : Fin n → ℕ) (hf : ∀ i, f i < n) {X : Matrix (Fin n) (Fin n) A}
    (hX : ∀ i j, f i ≤ f j → X i j = 0) : X ^ n = 0 := by
  ext i j
  have := hf i
  exact pow_apply_eq_zero f hX n i j (by omega)

theorem entIn_negpow {J : AddSubgroup A} (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J) {X : Matrix (Fin n) (Fin n) A}
    (hX : EntIn J X) (m : ℕ) : EntIn J ((-X) ^ (m + 1)) := by
  induction m with
  | zero => rw [zero_add, pow_one]; exact entIn_neg hX
  | succ m ih => rw [pow_succ]; exact entIn_mul hJ ih (entIn_neg hX)

theorem inv_sub_one (f : Fin n → ℕ) (hf : ∀ i, f i < n) {J : AddSubgroup A} (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J)
    (x : GL (Fin n) A) (hlow : ∀ i j, f i ≤ f j → ((x : Matrix (Fin n) (Fin n) A) - 1) i j = 0)
    (hx : EntIn J ((x : Matrix (Fin n) (Fin n) A) - 1)) :
    EntIn J (((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1) ∧
      ∀ i j, f i ≤ f j → (((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1) i j = 0 := by
  set X := (x : Matrix (Fin n) (Fin n) A) - 1 with hXdef
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  have hnX : ∀ i j, f i ≤ f j → (-X) i j = 0 := fun i j h => by rw [Matrix.neg_apply, hlow i j h, neg_zero]
  have hpow : (-X) ^ n = 0 := pow_eq_zero_of f hf hnX

  have hxS : (x : Matrix (Fin n) (Fin n) A) * ∑ i ∈ Finset.range n, (-X) ^ i = 1 := by
    have e : (x : Matrix (Fin n) (Fin n) A) = 1 - (-X) := by rw [sub_neg_eq_add, hXdef, add_sub_cancel]
    rw [e, mul_neg_geom_sum, hpow, sub_zero]
  have hinv : ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = ∑ i ∈ Finset.range n, (-X) ^ i := by
    calc ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)
        = ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) *
          ((x : Matrix (Fin n) (Fin n) A) * ∑ i ∈ Finset.range n, (-X) ^ i) := by rw [hxS, mul_one]
      _ = ∑ i ∈ Finset.range n, (-X) ^ i := by
          rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hY : ((x⁻¹ : GL (Fin (k + 1)) A) : Matrix (Fin (k + 1)) (Fin (k + 1)) A) - 1 =
      ∑ i ∈ Finset.range k, (-X) ^ (i + 1) := by
    rw [hinv, Finset.sum_range_succ', pow_zero, add_sub_cancel_right]
  rw [hY]
  refine ⟨fun i j => ?_, fun i j h => ?_⟩
  · rw [Matrix.sum_apply]
    exact sum_mem fun m _ => entIn_negpow hJ hx m i j
  · rw [Matrix.sum_apply]
    exact Finset.sum_eq_zero fun m _ => pow_apply_eq_zero f hnX (m + 1) i j (by omega)

end Ent

end Formalism.L2.SG.Pf.ProdEApprox
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IotaFIntMem
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain ValuativeRel

namespace Formalism.L2.SG.Pf.PCountEx

section Clear

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)

theorem iotaF_int_mem (p : HeightOneSpectrum (𝓞 F)) (t : 𝓞 F) :
    (A p).ιF (algebraMap (𝓞 F) F t) ∈ (haveI := (A p).lf; 𝒪[(A p).Fp]) := by
  haveI := (A p).lf
  have h := ((A p).val (algebraMap (𝓞 F) F t) 1).2 (by simpa using p.valuation_le_one t)
  rw [map_one] at h
  rw [Valuation.mem_integer_iff]
  exact (Valuation.vle_one_iff (ValuativeRel.valuation (A p).Fp)).1 h

theorem clear_F (p : HeightOneSpectrum (𝓞 F)) (l : (A p).Fp) :
    ∃ t : 𝓞 F, t ≠ 0 ∧ (A p).ιF (algebraMap (𝓞 F) F t) * l ∈ (haveI := (A p).lf; 𝒪[(A p).Fp]) := by
  haveI := (A p).lf
  by_cases hl : l = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [hl, mul_zero]
    exact Subring.zero_mem _
  obtain ⟨π, hπp, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot p.ne_bot
  have hπv : p.valuation F (algebraMap (𝓞 F) F π) < 1 := by
    first
    | exact (p.valuation_lt_one_iff_mem π).2 hπp
    | exact (p.valuation_lt_one_iff_mem (K := F) π).2 hπp
  have hπF0 : algebraMap (𝓞 F) F π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hπ0
  obtain ⟨c, hc⟩ : ∃ c, c = (A p).ιF (algebraMap (𝓞 F) F π) := ⟨_, rfl⟩
  have hcint : c ∈ (ValuativeRel.valuation (A p).Fp).integer := by
    rw [hc]
    exact iotaF_int_mem A p π
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (map_ne_zero (A p).ιF).2 hπF0
  have hnot : -(c⁻¹) ∉ (ValuativeRel.valuation (A p).Fp).integer := by
    intro hmem
    rw [Valuation.mem_integer_iff] at hmem
    have h1 := (Valuation.vle_one_iff (ValuativeRel.valuation (A p).Fp)).2 hmem
    have h2 : -(c⁻¹) = (A p).ιF (-(algebraMap (𝓞 F) F π)⁻¹) := by rw [hc, map_neg, map_inv₀]
    rw [h2, ← map_one (A p).ιF, (A p).val, map_one] at h1
    have h3 : p.valuation F (algebraMap (𝓞 F) F π) * p.valuation F (-(algebraMap (𝓞 F) F π)⁻¹) = 1 := by
      rw [← map_mul, mul_neg, mul_inv_cancel₀ hπF0, Valuation.map_neg, map_one]
    have h4 : p.valuation F (algebraMap (𝓞 F) F π) * p.valuation F (-(algebraMap (𝓞 F) F π)⁻¹) ≤
        p.valuation F (algebraMap (𝓞 F) F π) * 1 := by
      first
      | gcongr
      | exact mul_le_mul_right' h1 _
      | exact mul_le_mul_of_nonneg_left h1 (zero_le _)
    rw [h3, mul_one] at h4
    exact absurd h4 (not_le.2 hπv)
  have hW : IsOpen ((fun z => (z * l - 1) * c⁻¹) ⁻¹'
      ((ValuativeRel.valuation (A p).Fp).integer : Set (A p).Fp)) :=
    Valuation.isOpen_integer.preimage (((continuous_mul_const l).sub continuous_const).mul continuous_const)
  have hne : ((fun z => (z * l - 1) * c⁻¹) ⁻¹'
      ((ValuativeRel.valuation (A p).Fp).integer : Set (A p).Fp)).Nonempty := by
    refine ⟨l⁻¹, ?_⟩
    show (l⁻¹ * l - 1) * c⁻¹ ∈ (ValuativeRel.valuation (A p).Fp).integer
    rw [inv_mul_cancel₀ hl, sub_self, zero_mul]
    exact Subring.zero_mem _
  obtain ⟨y, hy⟩ := (A p).dense.exists_mem_open hW hne
  have hy' : ((A p).ιF y * l - 1) * c⁻¹ ∈ (ValuativeRel.valuation (A p).Fp).integer := hy
  have hy1 : (A p).ιF y * l ∈ (ValuativeRel.valuation (A p).Fp).integer := by
    have e : (A p).ιF y * l = ((A p).ιF y * l - 1) * c⁻¹ * c + 1 := by
      rw [mul_assoc, inv_mul_cancel₀ hc0, mul_one, sub_add_cancel]
    rw [e]
    exact Subring.add_mem _ (Subring.mul_mem _ hy' hcint) (Subring.one_mem _)
  have hy0 : (A p).ιF y ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_sub, neg_mul, one_mul] at hy'
    exact hnot hy'
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) y
  have hb' : algebraMap (𝓞 F) F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hy0' : (A p).ιF (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) ≠ 0 := hy0
  refine ⟨a, ?_, ?_⟩
  · rintro rfl
    apply hy0'
    simp
  · have e : algebraMap (𝓞 F) F a =
        algebraMap (𝓞 F) F b * (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) := by
      field_simp
    rw [e, map_mul, mul_assoc]
    exact Subring.mul_mem _ (iotaF_int_mem A p b) hy1

private theorem ιF_mem_O_of_mem_integers (p : HeightOneSpectrum (𝓞 F)) (w : (A p).Fp)
    (hw : w ∈ (haveI := (A p).lf; 𝒪[(A p).Fp])) : algebraMap (A p).Fp (A p).Ep w ∈ (A p).O := by
  haveI := (A p).lf
  rw [(A p).O_def]
  have e : algebraMap (A p).Fp (A p).Ep w = algebraMap (𝒪[(A p).Fp]) (A p).Ep ⟨_, hw⟩ := rfl
  rw [e]
  exact isIntegral_algebraMap

private theorem algebraMap_ιF_mem_O (p : HeightOneSpectrum (𝓞 F)) (t : 𝓞 F) :
    algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t)) ∈ (A p).O := by
  haveI := (A p).lf
  rw [(A p).O_def]
  have hm := iotaF_int_mem A p t
  have e : algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t)) =
      algebraMap (𝒪[(A p).Fp]) (A p).Ep ⟨_, hm⟩ := rfl
  rw [e]
  exact isIntegral_algebraMap

theorem clear_one (p : HeightOneSpectrum (𝓞 F)) (z : (A p).Ep) :
    ∃ t : 𝓞 F, t ≠ 0 ∧ algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t)) * z ∈ (A p).O := by
  haveI := (A p).lf
  have hz : z ∈ Submodule.span (A p).Fp (Set.range (A p).ιE) := by
    rw [(A p).span]
    trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    have hz : IsAlgebraic ℤ e :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic e)
    have inj : ∀ x : ℤ, algebraMap ℤ E x = 0 → x = 0 := fun x hx => by simpa using hx
    have hint : ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * e) := by
      first
      | (obtain ⟨⟨w, hw⟩, y, hy0, hyw⟩ := exists_integral_multiple hz inj
         refine ⟨y, hy0, ?_⟩
         rw [mul_comm]
         have hw' : IsIntegral ℤ w := hw
         simpa [hyw] using hw')
      | (obtain ⟨y, hy0, hy⟩ := hz.exists_integral_multiple
         exact ⟨y, hy0, by simpa [zsmul_eq_mul] using hy⟩)
    obtain ⟨y, hy0, hy⟩ := hint
    refine ⟨(y : 𝓞 F), by exact_mod_cast hy0, ?_⟩
    rw [← (A p).compat, ← map_mul]
    have e1 : algebraMap F E (algebraMap (𝓞 F) F (y : 𝓞 F)) * e = (y : E) * e := by simp
    rw [e1, (A p).O_def]
    have h2 : IsIntegral ℤ ((A p).ιE ((y : E) * e)) := hy.map (A p).ιE.toIntAlgHom
    exact h2.tower_top
  | zero =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [mul_zero]
    exact Subring.zero_mem _
  | add x y _ _ hx hy =>
    obtain ⟨t1, h10, h1⟩ := hx
    obtain ⟨t2, h20, h2⟩ := hy
    refine ⟨t1 * t2, mul_ne_zero h10 h20, ?_⟩
    have e : algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F (t1 * t2))) * (x + y) =
        algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t2)) *
          (algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t1)) * x) +
        algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t1)) *
          (algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t2)) * y) := by
      simp only [map_mul]
      ring
    rw [e]
    exact Subring.add_mem _ (Subring.mul_mem _ (algebraMap_ιF_mem_O A p t2) h1)
      (Subring.mul_mem _ (algebraMap_ιF_mem_O A p t1) h2)
  | smul c x _ hx =>
    obtain ⟨t1, h10, h1⟩ := hx
    obtain ⟨t2, h20, h2⟩ := clear_F A p c
    refine ⟨t2 * t1, mul_ne_zero h20 h10, ?_⟩
    rw [Algebra.smul_def]
    have e : algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F (t2 * t1))) *
        (algebraMap (A p).Fp (A p).Ep c * x) =
        algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t2) * c) *
          (algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t1)) * x) := by
      simp only [map_mul]
      ring
    rw [e]
    exact Subring.mul_mem _ (ιF_mem_O_of_mem_integers A p _ h2) h1

end Clear

section Mat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p) {n : ℕ}

theorem approx_lo (S : Finset (HeightOneSpectrum (𝓞 F))) (c : 𝓞 F) (hc : c ≠ 0)
    (g : ∀ p, Matrix (Fin n) (Fin n) (A p).Ep) (hg1 : ∀ p ∈ S, ∀ a, g p a a = 1)
    (hg0 : ∀ p ∈ S, ∀ a b, a < b → g p a b = 0) :
    ∃ L : Matrix (Fin n) (Fin n) E, (∀ a, L a a = 1) ∧ (∀ a b, a < b → L a b = 0) ∧
      (∀ p ∈ S, ∀ a b, ∃ o ∈ (A p).O,
        (A p).ιE (L a b) - g p a b = algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F c)) * o) ∧
      ∀ p ∉ S, ∀ a b, (A p).ιE (L a b) ∈ (A p).O := by
  have h := fun ab : Fin n × Fin n => approxE A S c hc (fun p => g p ab.1 ab.2)
  choose x hxS hxO using h
  refine ⟨fun a b => if b < a then x (a, b) else if a = b then 1 else 0, fun a => by simp, fun a b hab => ?_,
    fun p hp a b => ?_, fun p hp a b => ?_⟩
  · simp [not_lt.2 hab.le, hab.ne]
  · by_cases hba : b < a
    · simp only [hba, if_true]; exact hxS (a, b) p hp
    · refine ⟨0, zero_mem _, ?_⟩
      rcases eq_or_ne a b with rfl | hab
      · simp [hg1 p hp a]
      · have hlt : a < b := lt_of_le_of_ne (not_lt.1 hba) hab
        simp [hba, hab, hg0 p hp a b hlt]
  · by_cases hba : b < a
    · simp only [hba, if_true]; exact hxO (a, b) p hp
    · simp only [hba, if_false]
      split_ifs
      · rw [map_one]; exact one_mem _
      · rw [map_zero]; exact zero_mem _

theorem approx_up (S : Finset (HeightOneSpectrum (𝓞 F))) (c : 𝓞 F) (hc : c ≠ 0)
    (g : ∀ p, Matrix (Fin n) (Fin n) (A p).Ep) (hg1 : ∀ p ∈ S, ∀ a, g p a a = 1)
    (hg0 : ∀ p ∈ S, ∀ a b, b < a → g p a b = 0) :
    ∃ U : Matrix (Fin n) (Fin n) E, (∀ a, U a a = 1) ∧ (∀ a b, b < a → U a b = 0) ∧
      (∀ p ∈ S, ∀ a b, ∃ o ∈ (A p).O,
        (A p).ιE (U a b) - g p a b = algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F c)) * o) ∧
      ∀ p ∉ S, ∀ a b, (A p).ιE (U a b) ∈ (A p).O := by
  obtain ⟨L, hL1, hL0, hLS, hLn⟩ := approx_lo A S c hc (fun p => (g p).transpose)
    (fun p hp a => by simpa using hg1 p hp a)
    (fun p hp a b hab => by simpa [Matrix.transpose_apply] using hg0 p hp b a hab)
  refine ⟨L.transpose, fun a => by simpa using hL1 a, fun a b hab => by simpa using hL0 b a hab,
    fun p hp a b => ?_, fun p hp a b => by simpa using hLn p hp b a⟩
  simpa [Matrix.transpose_apply] using hLS p hp b a

end Mat

end Formalism.L2.SG.Pf.PCountEx
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxAd
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.ExistsLatticeAutomorphismApprox
noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace PI.StrongApproxE

open Formalism.MainNotions.S.Loc

theorem existsLatticeAutomorphismApprox : LocLin := by
  intro F E _ _ _ _ _ sig p L a e
  rw [Algebra.smul_def, map_mul, L.compat, Algebra.smul_def]

theorem local_span_holds : LocSpan := by
  intro F E _ _ _ _ _ sig p L n b hb x
  have hsub : Set.range L.ιE ⊆ Submodule.span L.Fp (Set.range (fun i => L.ιE (b i))) := by
    rintro _ ⟨e, rfl⟩
    obtain ⟨c, rfl⟩ := hb e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [existsLatticeAutomorphismApprox F E sig p L]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have htop : Submodule.span L.Fp (Set.range (fun i => L.ιE (b i))) = ⊤ := by
    rw [eq_top_iff, ← L.span]
    exact Submodule.span_le.mpr hsub
  have hx : x ∈ Submodule.span L.Fp (Set.range (fun i => L.ιE (b i))) := htop ▸ Submodule.mem_top
  obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun L.Fp).mp hx
  exact ⟨α, hα.symm⟩

theorem intSpan' : IntSpan := by
  intro F E _ _ _ _ _
  classical
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let B := Module.finBasis F E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image (fun i => B i))
  refine ⟨Module.finrank F E, fun i => y • B i,
    fun i => hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)), fun e => ?_⟩
  refine ⟨fun i => B.repr e i / (y : F), ?_⟩
  conv_lhs => rw [← B.sum_repr e]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hyF : (y : F) ≠ 0 := Int.cast_ne_zero.mpr hy0
  rw [smul_comm, ← smul_assoc, zsmul_eq_mul, mul_div_cancel₀ _ hyF]

end PI.StrongApproxE
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.LocalIntegralOfSubstitution
noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace PI.StrongApproxE

open Formalism.MainNotions.S.Loc

theorem local_dense_embedding : LocDense := by
  intro F E _ _ _ _ _ sig p L V hV α
  have := L.lf
  have ho : IsOpen {x : L.Fp | x - α ∈ V} := hV.preimage (continuous_sub_right α)
  obtain ⟨a, ha⟩ := L.dense.exists_mem_open ho ⟨α, by simp⟩
  exact ⟨a, ha⟩

theorem local_neighbourhood_small : LocSmall := by
  intro F E _ _ _ _ _ sig p L V hV
  have := L.lf
  have hV0 : (V : Set L.Fp) ∈ nhds (0 : L.Fp) := hV.mem_nhds V.zero_mem
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).mp hV0
  obtain ⟨r, hr⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero L.Fp)
  obtain ⟨r', hr'0, hr'1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation L.Fp)
  set x₀ : L.Fp := r * r' with hx₀
  have hx₀v : valuation L.Fp x₀ < γ := by
    rw [hx₀, map_mul, hr]
    calc (γ : ValueGroupWithZero L.Fp) * valuation L.Fp r'
        < (γ : ValueGroupWithZero L.Fp) * 1 := by
          exact mul_lt_mul_of_pos_left hr'1 (by simp [pos_iff_ne_zero])
      _ = γ := mul_one _
  have hx₀0 : valuation L.Fp x₀ ≠ 0 := by
    rw [hx₀, map_mul, hr]
    exact mul_ne_zero (Units.ne_zero γ) (by simpa using hr'0)
  have hs : {y : L.Fp | valuation L.Fp (y - x₀) < valuation L.Fp x₀} ∈ nhds x₀ :=
    IsValuativeTopology.mem_nhds_iff'.mpr ⟨Units.mk0 _ hx₀0, fun y hy => by simpa using hy⟩
  obtain ⟨_, hy, ⟨c, rfl⟩⟩ := mem_closure_iff_nhds.mp (L.dense x₀) _ hs
  have hyv : valuation L.Fp (L.ιF c) = valuation L.Fp x₀ := Valuation.map_eq_of_sub_lt _ hy
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hyv
    exact hx₀0 hyv.symm
  refine ⟨c, hc0, fun z hz => ?_⟩
  have h1 : L.ιF z ≤ᵥ L.ιF c := (L.val z c).mpr hz
  have h2 : valuation L.Fp (L.ιF z) ≤ valuation L.Fp (L.ιF c) :=
    (Valuation.Compatible.vle_iff_le (v := valuation L.Fp) _ _).mp h1
  exact hγ (show valuation L.Fp (L.ιF z) < γ from lt_of_le_of_lt (h2.trans_eq hyv) hx₀v)

theorem local_integral_of_substitution : LocInt := by
  intro F E _ _ _ _ _ sig p L z e hz he
  have := L.lf
  have h1 : L.ιF z ≤ᵥ L.ιF 1 := (L.val z 1).mpr (by simpa using hz)
  have hzO : L.ιF z ∈ 𝒪[L.Fp] := by
    rw [Valuation.mem_integer_iff]
    have := (Valuation.Compatible.vle_iff_le (v := valuation L.Fp) _ _).mp h1
    simpa using this
  have hE : IsIntegral 𝒪[L.Fp] (L.ιE e) := (map_isIntegral_int L.ιE he).tower_top
  have hA : IsIntegral 𝒪[L.Fp] (algebraMap L.Fp L.Ep (L.ιF z)) := by
    have := isIntegral_algebraMap (R := 𝒪[L.Fp]) (A := L.Ep) (x := ⟨L.ιF z, hzO⟩)
    exact this
  rw [Algebra.smul_def]
  exact L.O.mul_mem ((L.O_def _).mpr hA) ((L.O_def _).mpr hE)

end PI.StrongApproxE
end
end

noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.Pf.ProdEApprox

section Ball

variable {K : Type*} [Field K] [ValuativeRel K]

def InBall (c x : K) : Prop := ValuativeRel.valuation K x ≤ ValuativeRel.valuation K c

def ballS (c : K) : AddSubgroup K where
  carrier := {x | InBall c x}
  zero_mem' := by simp [InBall]
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, InBall] at hx hy ⊢
    exact Valuation.map_add_le _ hx hy
  neg_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq, InBall] at hx ⊢
    simpa [Valuation.map_neg] using hx

theorem mem_ballS {c x : K} : x ∈ ballS c ↔ valuation K x ≤ valuation K c := by
  show InBall c x ↔ _
  rfl

theorem ballS_isOpen [TopologicalSpace K] [IsValuativeTopology K] {c : K} (hc : c ≠ 0) :
    IsOpen (ballS c : Set K) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hv : valuation K c ≠ 0 := by simpa using hc
  refine IsValuativeTopology.mem_nhds_iff'.mpr ⟨Units.mk0 _ hv, fun y hy => ?_⟩
  have hy' : valuation K (y - x) < valuation K c := by simpa using hy
  rw [SetLike.mem_coe, mem_ballS]
  have e : y = (y - x) + x := by ring
  rw [e]
  exact Valuation.map_add_le _ hy'.le hx

theorem ballS_mul {c x : K} (hc : c ≠ 0) (hx : x ∈ ballS c) : ∃ β ∈ 𝒪[K], x = c * β := by
  refine ⟨x / c, ?_, by field_simp⟩
  rw [Valuation.mem_integer_iff, map_div₀]
  exact div_le_one_of_le₀ (mem_ballS.1 hx) zero_le'

end Ball

section Ad

open Formalism.MainNotions.S.Loc PI.StrongApproxE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p)

theorem sa_lat (T : Finset (HeightOneSpectrum (𝓞 F))) (x : ∀ p, (L p).Ep) (c : ∀ p, (L p).Fp)
    (hc : ∀ p ∈ T, c p ≠ 0) :
    ∃ t : E, (∀ p ∈ T, ∃ y ∈ (L p).O, (L p).ιE t - x p = algebraMap (L p).Fp (L p).Ep (c p) * y) ∧
      ∀ p, p ∉ T → (L p).ιE t ∈ (L p).O := by
  classical
  obtain ⟨n, b, hbint, hbspan⟩ := intSpan' F E
  choose α hα using fun p => local_span_holds F E sig p (L p) n b hbspan (x p)
  set c' : ∀ p, (L p).Fp := fun p => if p ∈ T then c p else 1 with hc'
  have hc'0 : ∀ p, c' p ≠ 0 := by
    intro p
    by_cases hp : p ∈ T
    · simp only [hc', if_pos hp]; exact hc p hp
    · simp only [hc', if_neg hp]; exact one_ne_zero
  have hVo : ∀ p, IsOpen (ballS (c' p) : Set (L p).Fp) := by
    intro p
    have := (L p).lf
    exact ballS_isOpen (hc'0 p)
  choose a ha using fun p (i : Fin n) => local_dense_embedding F E sig p (L p) (ballS (c' p)) (hVo p) (α p i)
  choose d hd0 hd using fun p => local_neighbourhood_small F E sig p (L p) (ballS (c' p)) (hVo p)
  choose t ht1 ht2 using fun i : Fin n => strong_approximation_finite_places F T (fun p => a p i) d (fun p _ => hd0 p)
  refine ⟨∑ i, t i • b i, fun p hp => ?_, fun p hp => ?_⟩
  · have hιE : (L p).ιE (∑ i, t i • b i) = ∑ i, (L p).ιF (t i) • (L p).ιE (b i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => existsLatticeAutomorphismApprox F E sig p (L p) (t i) (b i)
    have h1 : (L p).ιE (∑ i, t i • b i) - x p = ∑ i, ((L p).ιF (t i) - α p i) • (L p).ιE (b i) := by
      rw [hιE]
      conv_lhs => rw [hα p]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
    have hmem : ∀ i, (L p).ιF (t i) - α p i ∈ ballS (c' p) := by
      intro i
      have h2 : (L p).ιF (t i) - α p i = (L p).ιF (t i - a p i) + ((L p).ιF (a p i) - α p i) := by
        rw [map_sub]; ring
      rw [h2]
      exact (ballS (c' p)).add_mem (hd p _ (ht1 i p hp)) (ha p i)
    have hcp : c' p = c p := by simp only [hc', if_pos hp]
    choose β hβO hβ using fun i => ballS_mul (hc'0 p) (hmem i)
    have hbO : ∀ i, (L p).ιE (b i) ∈ (L p).O := by
      intro i
      have := local_integral_of_substitution F E sig p (L p) 1 (b i) (by simp) (hbint i)
      simpa using this
    have hβE : ∀ i, algebraMap (L p).Fp (L p).Ep (β i) * (L p).ιE (b i) ∈ (L p).O := by
      intro i
      have := (L p).lf
      have hA : IsIntegral 𝒪[(L p).Fp] (algebraMap (L p).Fp (L p).Ep (β i)) :=
        isIntegral_algebraMap (R := 𝒪[(L p).Fp]) (A := (L p).Ep) (x := ⟨β i, hβO i⟩)
      exact (L p).O.mul_mem (((L p).O_def _).mpr hA) (hbO i)
    refine ⟨∑ i, algebraMap (L p).Fp (L p).Ep (β i) * (L p).ιE (b i), (L p).O.sum_mem fun i _ => hβE i, ?_⟩
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hβ i, ← hcp, Algebra.smul_def, map_mul, mul_assoc]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine (L p).O.sum_mem fun i _ => ?_
    rw [existsLatticeAutomorphismApprox F E sig p (L p) (t i) (b i)]
    exact local_integral_of_substitution F E sig p (L p) (t i) (b i) (ht2 i p hp) (hbint i)

end Ad

end Formalism.L2.SG.Pf.ProdEApprox
end
end
