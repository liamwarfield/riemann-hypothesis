module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeAdjoinKthRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeAdjoinKthRoot
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize Polynomial
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize

set_option autoImplicit false in
private theorem natCast_mul_pow_pred_mem_differentIdeal_of_pow_eq {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] (k : ℕ) (β : 𝓞 L) (r : 𝓞 K)
    (hβ : β ^ k = algebraMap (𝓞 K) (𝓞 L) r)
    (hgen : Algebra.adjoin K {algebraMap (𝓞 L) L β} = ⊤) :
    (k : 𝓞 L) * β ^ (k - 1) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  have hint : IsIntegral (𝓞 K) β := Algebra.IsIntegral.isIntegral β
  obtain ⟨h, hh⟩ := minpoly.isIntegrallyClosed_dvd hint (p := X ^ k - C r) (by simp [hβ])
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 K) K L β hgen
  have hder : aeval β (derivative (X ^ k - C r : (𝓞 K)[X])) = (k : 𝓞 L) * β ^ (k - 1) := by
    simp [derivative_X_pow]
  rw [← hder, hh, derivative_mul, map_add (f := _), map_mul, map_mul, minpoly.aeval, zero_mul, add_zero]
  exact Ideal.mul_mem_right _ _ hmem

set_option autoImplicit false in
theorem _root_.GlobalTheory.FieldSize.natCast_mem_differentIdeal_of_root {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (k : ℕ) (hk : 0 < k) (y : K) (hy : y ≠ 0) (I : Submodule (𝓞 K) K)
    (hI : I ^ k = Submodule.span (𝓞 K) {y}) (z : L) (hz : z ^ k = algebraMap K L y)
    (hL : Algebra.adjoin K {z} = ⊤) : (k : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  classical
  have hy' : algebraMap K L y ≠ 0 := (_root_.map_ne_zero _).mpr hy
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hk.ne'] at hz
    exact hy' hz.symm
  have hzk : z ^ k ≠ 0 := pow_ne_zero k hz0
  have htop : K⟮z⟯ = ⊤ := by
    rw [← IntermediateField.toSubalgebra_inj, IntermediateField.top_toSubalgebra, eq_top_iff, ← hL]
    exact IntermediateField.algebra_adjoin_le_adjoin K {z}
  have hpow : ∀ b ∈ I, ∃ r : 𝓞 K, b ^ k = algebraMap (𝓞 K) K r * y := by
    intro b hb
    have hbk : b ^ k ∈ Submodule.span (𝓞 K) {y} := by
      rw [← hI]
      exact Submodule.pow_mem_pow I hb k
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hbk
    exact ⟨r, by rw [← hr, Algebra.smul_def]⟩
  have hquot : ∀ b ∈ I, ∃ β : 𝓞 L, algebraMap (𝓞 L) L β * z = algebraMap K L b := by
    intro b hb
    obtain ⟨r, hr⟩ := hpow b hb
    have hint : IsIntegral ℤ (algebraMap K L b / z) := by
      refine IsIntegral.of_pow hk ?_
      have hq : (algebraMap K L b / z) ^ k = algebraMap K L (algebraMap (𝓞 K) K r) := by
        rw [div_pow, ← map_pow, hr, map_mul, hz, mul_div_cancel_right₀ _ hy']
      rw [hq]
      exact (RingOfIntegers.isIntegral_coe r).algebraMap
    exact ⟨⟨_, hint⟩, div_mul_cancel₀ _ hz0⟩
  set S : Set (𝓞 L) :=
    {β | ∃ b ∈ I, b ≠ 0 ∧ algebraMap (𝓞 L) L β * z = algebraMap K L b} with hS
  have hmemS : ∀ β ∈ S, (k : 𝓞 L) * β ^ (k - 1) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
    rintro β ⟨b, hb, hb0, hβb⟩
    obtain ⟨r, hr⟩ := hpow b hb
    have hβ0 : algebraMap (𝓞 L) L β ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hβb
      exact hb0 ((map_eq_zero _).mp hβb.symm)
    refine natCast_mul_pow_pred_mem_differentIdeal_of_pow_eq k β r ?_ ?_
    · apply FaithfulSMul.algebraMap_injective (𝓞 L) L
      rw [map_pow, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
        IsScalarTower.algebraMap_apply (𝓞 K) K L]
      refine mul_right_cancel₀ hzk ?_
      rw [← mul_pow, hβb, ← map_pow, hr, map_mul, hz]
    · have hK : K⟮algebraMap (𝓞 L) L β⟯ = ⊤ := by
        rw [eq_top_iff, ← htop, IntermediateField.adjoin_simple_le_iff]
        have hzeq : z = algebraMap K L b / algebraMap (𝓞 L) L β := by
          rw [← hβb, mul_div_cancel_left₀ _ hβ0]
        rw [hzeq]
        exact div_mem (IntermediateField.algebraMap_mem _ b)
          (IntermediateField.mem_adjoin_simple_self K _)
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic _), hK, IntermediateField.top_toSubalgebra]
  have key : ∀ n : ℕ, ∀ w ∈ I ^ n, ∃ t ∈ Ideal.span S ^ n,
      algebraMap (𝓞 L) L t * z ^ n = algebraMap K L w := by
    intro n
    induction n with
    | zero =>
      intro w hw
      rw [pow_zero, Submodule.mem_one] at hw
      obtain ⟨r, rfl⟩ := hw
      refine ⟨algebraMap (𝓞 K) (𝓞 L) r, by simp, ?_⟩
      rw [pow_zero, mul_one, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
        ← IsScalarTower.algebraMap_apply (𝓞 K) K L]
    | succ n ih =>
      intro w hw
      rw [pow_succ] at hw
      refine Submodule.mul_induction_on (C := fun w => ∃ t ∈ Ideal.span S ^ (n + 1),
        algebraMap (𝓞 L) L t * z ^ (n + 1) = algebraMap K L w) hw ?_ ?_
      · intro a ha b hb
        obtain ⟨t, ht, hta⟩ := ih a ha
        by_cases hb0 : b = 0
        · exact ⟨0, zero_mem _, by simp [hb0]⟩
        obtain ⟨β, hβ⟩ := hquot b hb
        refine ⟨t * β, ?_, ?_⟩
        · rw [pow_succ]
          exact Ideal.mul_mem_mul ht (Ideal.subset_span ⟨b, hb, hb0, hβ⟩)
        · rw [map_mul, map_mul, pow_succ, ← hta, ← hβ]
          ring
      · rintro x x' ⟨t, ht, htx⟩ ⟨t', ht', htx'⟩
        exact ⟨t + t', add_mem ht ht', by rw [map_add (f := _), add_mul, htx, htx', map_add (f := _)]⟩
  have hspan : Ideal.span S = ⊤ := by
    have hyk : y ∈ I ^ k := by
      rw [hI]
      exact Submodule.mem_span_singleton_self y
    obtain ⟨t, ht, htz⟩ := key k y hyk
    have ht1 : t = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 L) L
      rw [map_one]
      refine mul_right_cancel₀ hzk ?_
      rw [htz, hz, one_mul]
    rw [Ideal.eq_top_iff_one]
    exact Ideal.pow_le_self hk.ne' (by rw [← ht1]; exact ht)
  have h1 : (1 : 𝓞 L) ∈ Ideal.span ((fun x => x ^ (k - 1)) '' S) := by
    rw [Ideal.span_pow_eq_top S hspan]
    exact Submodule.mem_top
  have hfin := Submodule.span_induction
    (p := fun x _ => (k : 𝓞 L) * x ∈ differentIdeal (𝓞 K) (𝓞 L))
    (by rintro _ ⟨β, hβ, rfl⟩; exact hmemS β hβ) (by simp)
    (fun x x' _ _ hx hx' => by rw [mul_add]; exact add_mem hx hx')
    (fun a x _ hx => by rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ a hx) h1
  simpa using hfin

set_option autoImplicit false in
theorem _root_.GlobalTheory.FieldSize.sz_sup_adjoin_root : ∀ (F : IntermediateField ℚ ℂ) (a b : ℝ) (k : ℕ) (y : F) (I : Submodule (𝓞 F) F) (z : ℂ), _root_.GlobalTheory.FieldSize.Sz F a b → 0 < k → y ≠ 0 → I ^ k = Submodule.span (𝓞 F) {y} → z ^ k = (y : ℂ) → _root_.GlobalTheory.FieldSize.Sz (F ⊔ ℚ⟮z⟯) (a + Real.log k) (b + Real.log k) := by
  intro F a b k y I z hF hk hy hI hz
  unfold _root_.GlobalTheory.FieldSize.Sz at hF ⊢
  obtain ⟨hfd, hdeg, hdisc⟩ := hF
  have hyint : IsIntegral ℚ (y : ℂ) := (Algebra.IsIntegral.isIntegral y).map F.val
  have hzint : IsIntegral ℚ z := IsIntegral.of_pow hk (by rw [hz]; exact hyint)
  haveI : FiniteDimensional ℚ ℚ⟮z⟯ := IntermediateField.adjoin.finiteDimensional hzint
  haveI hEfd : FiniteDimensional ℚ ↥(F ⊔ ℚ⟮z⟯) := IntermediateField.finiteDimensional_sup F ℚ⟮z⟯
  set E := F ⊔ ℚ⟮z⟯ with hE
  haveI : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := hfd }
  haveI : NumberField E := { to_charZero := inferInstance, to_finiteDimensional := hEfd }
  have hle : F ≤ E := le_sup_left
  letI : Algebra F E := (IntermediateField.inclusion hle).toAlgebra
  letI : Module.Free F E := Module.Free.of_divisionRing F E
  let z' : E := ⟨z, (le_sup_right : ℚ⟮z⟯ ≤ E) (IntermediateField.mem_adjoin_simple_self ℚ z)⟩
  have hz' : z' ^ k = algebraMap F E y :=
    Subtype.ext (by rw [IntermediateField.coe_pow]; exact hz)
  have hzF : IsIntegral F z := IsIntegral.of_pow hk (by rw [hz]; exact isIntegral_algebraMap)
  let φ : E →ₐ[F] ℂ := { E.val with commutes' := fun _ => rfl }
  have hL : Algebra.adjoin F {z'} = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have hw : (w : ℂ) ∈ Algebra.adjoin F {z} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hzF.isAlgebraic]
      have hwr : (w : ℂ) ∈ (IntermediateField.adjoin F {z}).restrictScalars ℚ := by
        have h := IntermediateField.restrictScalars_adjoin_eq_sup ℚ F {z}
        rw [SetLike.ext_iff] at h
        exact (h _).mpr w.2
      exact hwr
    have hmap : Algebra.adjoin F {z} = (Algebra.adjoin F {z'}).map φ := by
      rw [AlgHom.map_adjoin, Set.image_singleton]
      rfl
    rw [hmap] at hw
    obtain ⟨w', hw', hww⟩ := hw
    have hw'w : w' = w := Subtype.val_injective hww
    exact hw'w ▸ hw'
  have hdiff := _root_.GlobalTheory.FieldSize.natCast_mem_differentIdeal_of_root k hk y hy I hI z' hz' hL
  have hroot := _root_.GlobalTheory.log_rootDiscr_le_of_natCast_mem_differentIdeal F E k hk hdiff
  have hFE : IntermediateField.adjoin F {z'} = ⊤ := by
    rw [← IntermediateField.toSubalgebra_inj, IntermediateField.top_toSubalgebra, eq_top_iff, ← hL]
    exact IntermediateField.algebra_adjoin_le_adjoin F {z'}
  have hz'int : IsIntegral F z' := IsIntegral.of_pow hk (by rw [hz']; exact isIntegral_algebraMap)
  have hdegFE : Module.finrank F E ≤ k := by
    have h1 := IntermediateField.adjoin.finrank hz'int
    rw [hFE, IntermediateField.finrank_top'] at h1
    rw [h1]
    have hp : (X ^ k - C y : F[X]) ≠ 0 := X_pow_sub_C_ne_zero hk y
    calc (minpoly F z').natDegree ≤ (X ^ k - C y : F[X]).natDegree :=
          natDegree_le_of_dvd (minpoly.dvd F z' (by simp [hz'])) hp
      _ = k := natDegree_X_pow_sub_C _
  haveI : FiniteDimensional F E := FiniteDimensional.right ℚ F E
  have hdF : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hdFE : 0 < Module.finrank F E := Module.finrank_pos
  have htower : Module.finrank ℚ E = Module.finrank ℚ F * Module.finrank F E :=
    (Module.finrank_mul_finrank ℚ F E).symm
  refine ⟨hEfd, ?_, ?_⟩
  · rw [htower, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    exact add_le_add hdeg (Real.log_le_log (by positivity) (by exact_mod_cast hdegFE))
  · exact hroot.trans (add_le_add hdisc le_rfl)

end GlobalTheory.FieldSize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeAdjoinKthRootStatement
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_size_adjoin_kth_root : ∀ (F : IntermediateField ℚ ℂ) (a b : ℝ) (k : ℕ) (y : F) (I : Submodule (𝓞 F) F) (z : ℂ), Sz F a b → 0 < k → y ≠ 0 → I ^ k = Submodule.span (𝓞 F) {y} → z ^ k = (y : ℂ) → Sz (F ⊔ ℚ⟮z⟯) (a + Real.log k) (b + Real.log k) := by
  first | exact @GlobalTheory.FieldSize.sz_sup_adjoin_root | exact GlobalTheory.FieldSize.sz_sup_adjoin_root | (intros; apply GlobalTheory.FieldSize.sz_sup_adjoin_root <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HighestWeightGeneratedWeightsBelow
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HighestWeightGeneratedWeightsBelow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.RealPar.HwGen

theorem weight_of_mem_span {V ι κ : Type*} [AddCommGroup V] [Module ℂ V] (H : ι → Module.End ℂ V)
    (m : κ → V) (χ : κ → ι → ℂ) (hm : ∀ k a, H a (m k) = χ k a • m k) (ν : ι → ℂ) (w : V)
    (hw : w ∈ Submodule.span ℂ (Set.range m)) (h0 : w ≠ 0) (hν : ∀ a, H a w = ν a • w) :
    ∃ k, χ k = ν := by
  by_contra hne
  push Not at hne
  let M : Submonoid (Module.End ℂ V) :=
    Submonoid.closure {P | ∃ a c, c ≠ ν a ∧ P = H a - c • (1 : Module.End ℂ V)}
  have hM : ∀ P ∈ M, ∀ (s : V) (η : ι → ℂ), (∀ a, H a s = η a • s) →
      ∃ c : ℂ, P s = c • s ∧ (η = ν → c ≠ 0) := by
    intro P hP s η hs
    induction hP using Submonoid.closure_induction with
    | mem P hP =>
      obtain ⟨a, c, hc, rfl⟩ := hP
      refine ⟨η a - c, by simp [hs, sub_smul], ?_⟩
      rintro rfl
      exact sub_ne_zero.2 hc.symm
    | one => exact ⟨1, by simp, fun _ => one_ne_zero⟩
    | mul P Q _ _ hP hQ =>
      obtain ⟨c, hc, hc'⟩ := hP
      obtain ⟨d, hd, hd'⟩ := hQ
      exact ⟨d * c, by simp [hc, hd, mul_smul], fun h => mul_ne_zero (hd' h) (hc' h)⟩
  have key : ∀ x ∈ Submodule.span ℂ (Set.range m), ∀ Q ∈ M, ∃ P ∈ M, P (Q x) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      intro Q hQ
      obtain ⟨c, hc, -⟩ := hM Q hQ (m k) (χ k) (hm k)
      obtain ⟨a, ha⟩ := Function.ne_iff.1 (hne k)
      refine ⟨H a - χ k a • 1, Submonoid.subset_closure ⟨a, _, ha, rfl⟩, ?_⟩
      rw [hc, map_smul]
      simp [hm]
    | zero => exact fun Q _ => ⟨1, one_mem _, by simp⟩
    | add x y _ _ hx hy =>
      intro Q hQ
      obtain ⟨P, hP, h1⟩ := hx Q hQ
      obtain ⟨R, hR, h2⟩ := hy (P * Q) (mul_mem hP hQ)
      refine ⟨R * P, mul_mem hR hP, ?_⟩
      simp only [Module.End.mul_apply] at h2 ⊢
      simp [h1, h2]
    | smul c x _ hx =>
      intro Q hQ
      obtain ⟨P, hP, h1⟩ := hx Q hQ
      exact ⟨P, hP, by simp [h1]⟩
  obtain ⟨P, hP, h1⟩ := key w hw 1 (one_mem _)
  obtain ⟨c, hc, hc'⟩ := hM P hP w ν hν
  rw [Module.End.one_apply, hc] at h1
  exact h0 ((smul_eq_zero.1 h1).resolve_left (hc' rfl))

variable {p q : ℕ}

theorem isKC_Eab {a b : Ix p q} (h : posC a b) : IsKC (Eab b a) := by
  intro x y hxy
  by_contra hne
  have : b = x ∧ a = y := by
    by_contra hh
    exact hne (by simp [Eab, hh])
  obtain ⟨rfl, rfl⟩ := this
  cases a <;> cases b <;> simp_all [posC, sameBlock]

theorem isKC_mul {X Y : Mat p q} (hX : IsKC X) (hY : IsKC Y) : IsKC (X * Y) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h : sameBlock a c
  · rw [hY c b (by cases a <;> cases b <;> cases c <;> simp_all [sameBlock]), mul_zero]
  · rw [hX a c h, zero_mul]

theorem isKC_sub {X Y : Mat p q} (hX : IsKC X) (hY : IsKC Y) : IsKC (X - Y) := by
  intro a b hab
  simp [hX a b hab, hY a b hab]

theorem sameBlock_cases {a b : Ix p q} (h : sameBlock a b) : a = b ∨ posC a b ∨ posC b a := by
  rcases a with a | a <;> rcases b with b | b
  · rcases lt_trichotomy a b with x | x | x
    · exact .inr (.inl x)
    · exact .inl (by rw [x])
    · exact .inr (.inr x)
  · exact h.elim
  · exact h.elim
  · rcases lt_trichotomy a b with x | x | x
    · exact .inr (.inl x)
    · exact .inl (by rw [x])
    · exact .inr (.inr x)

theorem bracket_diag (x a b : Ix p q) :
    Eab x x * Eab b a - Eab b a * Eab x x =
      (((if x = b then 1 else 0) - (if x = a then 1 else 0) : ℂ)) • Eab b a := by
  have h1 : Eab x x * Eab b a = ((if x = b then 1 else 0) : ℂ) • Eab b a := by
    by_cases h : x = b
    · subst h; simp [Eab]
    · simp [Eab, h]
  have h2 : Eab b a * Eab x x = ((if x = a then 1 else 0) : ℂ) • Eab b a := by
    by_cases h : x = a
    · subst h; simp [Eab]
    · simp [Eab, h, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm h)]
  rw [h1, h2, sub_smul]

abbrev PosRoot (p q : ℕ) := {r : Ix p q × Ix p q // posC r.1 r.2}

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

noncomputable def mono (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (v : V) : List (PosRoot p q) → V
  | [] => v
  | r :: l => act (Eab r.1.2 r.1.1) (mono act v l)

noncomputable def cnt : List (PosRoot p q) → Ix p q → Ix p q → ℕ
  | [], _, _ => 0
  | r :: l, a, b => cnt l a b + if a = r.1.1 ∧ b = r.1.2 then 1 else 0

theorem posC_of_cnt (l : List (PosRoot p q)) (a b : Ix p q) (h : cnt l a b ≠ 0) : posC a b := by
  induction l with
  | nil => exact (h rfl).elim
  | cons r l ih =>
    by_cases hh : a = r.1.1 ∧ b = r.1.2
    · rw [hh.1, hh.2]; exact r.2
    · exact ih (by simpa [cnt, hh] using h)

noncomputable def drop (l : List (PosRoot p q)) (x : Ix p q) : ℝ :=
  ∑ a, ∑ b, (cnt l a b : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0))

theorem drop_cons (r : PosRoot p q) (l : List (PosRoot p q)) (x : Ix p q) :
    drop (r :: l) x = drop l x + ((if x = r.1.1 then 1 else 0) - (if x = r.1.2 then 1 else 0)) := by
  simp only [drop, cnt, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single r.1.1, Finset.sum_eq_single r.1.2]
  · simp
  · intro b _ hb; simp [hb]
  · simp
  · intro a _ ha; simp [ha]
  · simp

theorem act_comm {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) (X Y : Mat p q) (u : V) :
    act X (act Y u) = act Y (act X u) + act (X * Y - Y * X) u := by
  rw [h X Y]; simp

theorem mono_weight {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {μ : Ix p q → ℚ} {v : V}
    (hv : ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) (l : List (PosRoot p q)) (x : Ix p q) :
    act (Eab x x) (mono act v l) = ((((μ x : ℚ) : ℝ) - drop l x : ℝ) : ℂ) • mono act v l := by
  induction l with
  | nil => simp [mono, drop, cnt, hv]
  | cons r l ih =>
    rw [mono, act_comm h, ih, bracket_diag, map_smul, map_smul, LinearMap.smul_apply, ← add_smul, drop_cons]
    congr 1
    push_cast
    split_ifs <;> simp <;> ring

theorem mono_stable {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {μ : Ix p q → ℚ} {v : V}
    (hv : ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) (hr : ∀ a b, posC a b → act (Eab a b) v = 0) :
    KStable act (Submodule.span ℂ (Set.range (mono act v))) := by
  set W := Submodule.span ℂ (Set.range (mono act v)) with hW
  have hm : ∀ l, mono act v l ∈ W := fun l => Submodule.subset_span ⟨l, rfl⟩
  have ext : ∀ T : Module.End ℂ V, (∀ l, T (mono act v l) ∈ W) → ∀ w ∈ W, T w ∈ W := by
    intro T hT w hw
    have : W ≤ W.comap T := Submodule.span_le.2 (by rintro _ ⟨l, rfl⟩; exact hT l)
    exact this hw
  have low : ∀ r : PosRoot p q, ∀ w ∈ W, act (Eab r.1.2 r.1.1) w ∈ W :=
    fun r => ext _ fun l => hm (r :: l)
  have key : ∀ l, ∀ Z, IsKC Z → act Z (mono act v l) ∈ W := by
    intro l
    induction l with
    | nil =>
      intro Z hZ
      have hZ' : Z = ∑ a, ∑ b, Z a b • Eab a b := by
        conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
        simp [Eab]
      rw [hZ']
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      refine W.sum_mem fun a _ => W.sum_mem fun b _ => ?_
      by_cases hab : sameBlock a b
      · refine W.smul_mem _ ?_
        rcases sameBlock_cases hab with x | x | x
        · subst x
          rw [mono, hv]; exact W.smul_mem _ (hm [])
        · rw [mono, hr a b x]; exact W.zero_mem
        · exact hm [⟨(b, a), x⟩]
      · rw [hZ a b hab, zero_smul]; exact W.zero_mem
    | cons r l ih =>
      intro Z hZ
      rw [mono, act_comm h]
      have hF := isKC_Eab r.2
      exact W.add_mem (low r _ (ih Z hZ)) (ih _ (isKC_sub (isKC_mul hZ hF) (isKC_mul hF hZ)))
  exact fun Z hZ => ext _ fun l => key l Z hZ

theorem hw_generated : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (μ : Ix p q → ℚ) (v : V), Formalism.BasicNotions.TH.IsHW act μ v → ∃ W : Submodule ℂ V, v ∈ W ∧ KStable act W ∧ (∀ W' : Submodule ℂ V, v ∈ W' → KStable act W' → W ≤ W') ∧ ∀ (ν : Ix p q → ℝ) (w : V), w ∈ W → w ≠ 0 → (∀ a, act (Eab a a) w = ((ν a : ℝ) : ℂ) • w) → ∃ c : Ix p q → Ix p q → ℕ, (∀ a b, c a b ≠ 0 → posC a b) ∧ ∀ x, ((μ x : ℚ) : ℝ) - ν x = ∑ a, ∑ b, (c a b : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0)) := by
  intro p q V _ _ act h μ v hv
  obtain ⟨-, hw, hr⟩ := hv
  have hv : ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
    intro a
    have := (Submodule.mem_iInf _).1 hw a
    simpa [sub_eq_zero] using this
  have hr : ∀ a b, posC a b → act (Eab a b) v = 0 := by
    intro a b hab
    have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hr a) b) hab
    simpa using this
  refine ⟨Submodule.span ℂ (Set.range (mono act v)), Submodule.subset_span ⟨[], rfl⟩, mono_stable h hv hr, ?_, ?_⟩
  · intro W' hvW hW
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, rfl⟩
    induction l with
    | nil => exact hvW
    | cons r l ih => exact hW _ (isKC_Eab r.2) _ ih
  · intro ν w hw h0 hν
    obtain ⟨l, hl⟩ := weight_of_mem_span (fun a => act (Eab a a)) (mono act v) _
      (fun l x => mono_weight h hv l x) (fun a => ((ν a : ℝ) : ℂ)) w hw h0 hν
    refine ⟨cnt l, posC_of_cnt l, fun x => ?_⟩
    have := Complex.ofReal_injective (congrFun hl x)
    change _ = drop l x
    linarith

end GlobalTheory.RealPar.HwGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HighestWeightGeneratedWeightsBelowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highestWeight_generated_weights_below : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (μ : Ix p q → ℚ) (v : V), Formalism.BasicNotions.TH.IsHW act μ v → ∃ W : Submodule ℂ V, v ∈ W ∧ KStable act W ∧ (∀ W' : Submodule ℂ V, v ∈ W' → KStable act W' → W ≤ W') ∧ ∀ (ν : Ix p q → ℝ) (w : V), w ∈ W → w ≠ 0 → (∀ a, act (Eab a a) w = ((ν a : ℝ) : ℂ) • w) → ∃ c : Ix p q → Ix p q → ℕ, (∀ a b, c a b ≠ 0 → posC a b) ∧ ∀ x, ((μ x : ℚ) : ℝ) - ν x = ∑ a, ∑ b, (c a b : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0)) := by
  first | exact @GlobalTheory.RealPar.HwGen.hw_generated | exact GlobalTheory.RealPar.HwGen.hw_generated | (intros; apply GlobalTheory.RealPar.HwGen.hw_generated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.MemHermitianStandardLatticeIffPairingIntegral
section -- merged from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ShiftMapsUpDown
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev AEf (D : D7) : Type := Af D.host.F ⊗[D.host.F] D.host.E

def locPart (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : AE D →+* Fv D.host.F v ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)).toRingHom.comp (finPart D)

def gramFin (V : HSp D) : Matrix (Fin V.rank) (Fin V.rank) (AEf D) :=
  V.gram.map (inclR (F := D.host.F) (Af D.host.F))

def latFin (V : HSp D) : AddSubgroup (Fin V.rank → AEf D) := latHat D.host.F D.host.E (L0c D V)

def latFinAA (V : HSp D) : AddSubgroup (Fin V.rank → AEf D) :=
  latHat D.host.F D.host.E {y | ∃ a ∈ D.host.AA, ∃ x ∈ L0c D V, y = a • x}

def offS (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : AddSubgroup (WA V W) where
  carrier := {x | (∀ i j, infPart D (x i j) = 0) ∧ ∀ v ∈ S, ∀ i j, locPart D v (x i j) = 0}
  zero_mem' := ⟨fun i j => by simp, fun v _ i j => by simp⟩
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨fun i j => ?_, fun v hv i j => ?_⟩
    · rw [Matrix.add_apply, RingHom.map_add (f := _), hx i j, hy i j, add_zero]
    · rw [Matrix.add_apply, RingHom.map_add (f := _), hx' v hv i j, hy' v hv i j, add_zero]
  neg_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨fun i j => ?_, fun v hv i j => ?_⟩
    · rw [Matrix.neg_apply, RingHom.map_neg, hx i j, neg_zero]
    · rw [Matrix.neg_apply, RingHom.map_neg, hx' v hv i j, neg_zero]

def mapUp (V W : HSp D) (x : WA V W) : Matrix (Fin W.rank) (Fin V.rank) (AEf D) :=
  HMul.hMul (x.map (finPart D)).transpose (gramFin V)

def mapDown (V W : HSp D) (x : WA V W) : Matrix (Fin V.rank) (Fin W.rank) (AEf D) :=
  HMul.hMul (x.map (finPart D)) (gramFin W)

theorem mapUp_add (V W : HSp D) (x y : WA V W) : mapUp V W (x + y) = mapUp V W x + mapUp V W y := by
  ext i j
  simp [mapUp, Matrix.mul_apply, add_mul, Finset.sum_add_distrib]

theorem mapDown_add (V W : HSp D) (x y : WA V W) : mapDown V W (x + y) = mapDown V W x + mapDown V W y := by
  ext i j
  simp [mapDown, Matrix.mul_apply, add_mul, Finset.sum_add_distrib]

theorem mapUp_neg (V W : HSp D) (x : WA V W) : mapUp V W (-x) = -mapUp V W x := by
  ext i j
  simp [mapUp, Matrix.mul_apply]

theorem mapDown_neg (V W : HSp D) (x : WA V W) : mapDown V W (-x) = -mapDown V W x := by
  ext i j
  simp [mapDown, Matrix.mul_apply]

theorem mapUp_zero (V W : HSp D) : mapUp V W 0 = 0 := by
  ext i j
  simp [mapUp, Matrix.mul_apply]

theorem mapDown_zero (V W : HSp D) : mapDown V W 0 = 0 := by
  ext i j
  simp [mapDown, Matrix.mul_apply]

def homInt (V W : HSp D) : AddSubgroup (WA V W) where
  carrier := {x | if V.rank ≤ W.rank then ∀ y ∈ latFin V, (mapUp V W x).mulVec y ∈ latFinAA W
    else ∀ y ∈ latFin W, (mapDown V W x).mulVec y ∈ latFinAA V}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, mapUp_zero, mapDown_zero, Matrix.zero_mulVec]
    split_ifs
    · exact fun _ _ => zero_mem _
    · exact fun _ _ => zero_mem _
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, mapUp_add, mapDown_add, Matrix.add_mulVec] at hx hy ⊢
    split_ifs at hx hy ⊢
    · exact fun z hz => add_mem (hx z hz) (hy z hz)
    · exact fun z hz => add_mem (hx z hz) (hy z hz)
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq, mapUp_neg, mapDown_neg, Matrix.neg_mulVec] at hx ⊢
    split_ifs at hx ⊢
    · exact fun z hz => neg_mem (hx z hz)
    · exact fun z hz => neg_mem (hx z hz)

def homLat (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : AddSubgroup (WA V W) :=
  offS V W S ⊓ homInt V W

def UnramOutside (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → (∀ v ∈ S, locPart D v (x : AE D) = 1) → χ x = 1

def vacSignOf (ψ : AddChar (AF D.host.F) ℂ) (θ : D.host.E) (V W : HSp D) (l : WA V W) : ℂ :=
  ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) *
    Algebra.trace (AF D.host.F) (AE D) (incA D (θ * D.host.xi0) * hHom V W l l))

def theta0 (D : D7) : D.host.E := (1 + D.host.sqrtMinusD) / 2

def vacSign (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (l : WA V W) : ℂ := vacSignOf ψ (theta0 D) V W l

variable {X : ThetaX D} {T : ThetaTied D X}

def IsVacuum (Wl : WeilTied D X T) (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (Φ : X.Sch V W) : Prop :=
  ∀ l ∈ homLat V W S, Heisenberg₂ Wl.ψ V W l (Wl.evS V W Φ) = vacSign Wl.ψ V W l • Wl.evS V W Φ

def HomLatSelfDual (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    ∀ x ∈ offS V W S, x ∈ homLat V W S ↔ ∀ l ∈ homLat V W S, ψ (sympl V W x l) = 1

def HyperspecialFixesVacuum (Wl : WeilTied D X T) : Prop :=
  ∀ (V W : HSp D) (χ χ' : X.Chr), V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), UnramOutside D S (T.eChr χ) → UnramOutside D S (T.eChr χ') →
      ∀ g ∈ KsphC V S, ∀ h ∈ KsphC W S, ∀ Φ : X.Sch V W, IsVacuum Wl V W S Φ → Wl.om V W χ χ' (g, h) Φ = Φ

end GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.WeilUnramifiedCompare

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hT_coord (V : HSpace E) (x y : Fin V.rank → E) :
    V.hT (∑ i, x i • V.frame i) (∑ k, y k • V.frame k) = ∑ i, ∑ k, star (x i) * V.gram i k * y k := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum V.hT, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, HSpace.gram, starRingEnd_apply]
  ring

theorem mem_hermitianStandardLattice_iff_pairing_integral (V : HSpace E) (x : V.V) : x ∈ V.L0 ↔ ∀ y ∈ V.L0, ∃ o : 𝓞 E, (o : E) = V.hT y x := by
  have h : Formalism.E.hdual V.hT V.L0 = V.L0 := V.baseLattice_isUnimodular
  conv_lhs => rw [← h]
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one, LinearMap.restrictScalars_apply]

end Lattice

open GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown (offS homInt homLat latFin latFinAA mapUp mapDown locPart gramFin AEf vacSign vacSignOf theta0
  HyperspecialFixesVacuum HomLatSelfDual mapUp_add mapUp_neg mapUp_zero)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Adeles

variable (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

variable {F} in
theorem intAf_mul {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a * b ∈ intAf F := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

end Adeles

variable {X : ThetaX D} {T : ThetaTied D X}

end GlobalTheory.WeilUnramifiedCompare

end
end
