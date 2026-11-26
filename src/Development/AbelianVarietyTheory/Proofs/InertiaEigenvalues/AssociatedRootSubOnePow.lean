module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexMatrixGaussSumNormIntegralGalois
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralSumIndicatorTranslate
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoprimeVal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConstOfLvlInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CDvdOfDvdXPowMul
noncomputable section

open PowerSeries GlobalTheory.NB.LT

namespace GlobalTheory.NB.LT.EEBasic

section General
variable {B : Type} [CommRing B] (b : B)

theorem pow_dvd_iff_eval (k : ℕ) (x : AdicCompletion (Ideal.span {b}) B) :
    (algebraMap B (AdicCompletion (Ideal.span {b}) B) b) ^ k ∣ x ↔
      AdicCompletion.eval (Ideal.span {b}) B k x = 0 := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval
    (Submodule.fg_span_singleton b), Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
    Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton,
    map_pow]

theorem eval_algebraMap (k : ℕ) (c : B) :
    AdicCompletion.eval (Ideal.span {b}) B k (algebraMap B (AdicCompletion (Ideal.span {b}) B) c)
      = Submodule.Quotient.mk c := by
  rw [AdicCompletion.algebraMap_apply]
  rfl

theorem pow_dvd_of_pow_dvd (k : ℕ) (c : B)
    (h : (algebraMap B (AdicCompletion (Ideal.span {b}) B) b) ^ k ∣
      algebraMap B (AdicCompletion (Ideal.span {b}) B) c) : b ^ k ∣ c := by
  rw [pow_dvd_iff_eval, eval_algebraMap, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
    Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  exact h

theorem exists_pow_dvd_sub (k : ℕ) (x : AdicCompletion (Ideal.span {b}) B) :
    ∃ c : B, (algebraMap B (AdicCompletion (Ideal.span {b}) B) b) ^ k ∣
      x - algebraMap B (AdicCompletion (Ideal.span {b}) B) c := by
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _
    (AdicCompletion.eval (Ideal.span {b}) B k x)
  exact ⟨c, by rw [pow_dvd_iff_eval, map_sub, eval_algebraMap, hc, sub_self]⟩

theorem complete : IsAdicComplete
    (Ideal.span {algebraMap B (AdicCompletion (Ideal.span {b}) B) b})
    (AdicCompletion (Ideal.span {b}) B) := by
  have h : Ideal.span {algebraMap B (AdicCompletion (Ideal.span {b}) B) b} =
      (Ideal.span {b}).map (algebraMap B (AdicCompletion (Ideal.span {b}) B)) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [h, IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete (Submodule.fg_span_singleton b)

end General

variable {O : Type} [CommRing O]

theorem C_dvd_iff (c : O) (a : O⟦X⟧) : C c ∣ a ↔ ∀ n, c ∣ coeff n a := by
  constructor
  · rintro ⟨q, rfl⟩ n
    rw [coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    choose q hq using h
    exact ⟨PowerSeries.mk q, PowerSeries.ext fun n => by rw [coeff_C_mul, coeff_mk, hq]⟩

theorem C_dvd_of_dvd_X_pow_mul (c : O) (m : ℕ) (a : O⟦X⟧) (h : C c ∣ X ^ m * a) : C c ∣ a := by
  rw [C_dvd_iff] at h ⊢
  intro n
  have := h (n + m)
  rwa [coeff_X_pow_mul] at this

theorem C_dvd_of_dvd_away (c : O) (a : O⟦X⟧)
    (h : algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (C c) ∣
      algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) a) : C c ∣ a := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨m, q, hq⟩ := IsLocalization.Away.surj (X : O⟦X⟧) z
  have h1 : algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (X ^ m * a) =
      algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (C c * q) := by
    rw [map_mul, map_mul, map_pow, hz, ← hq]; ring
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (X : O⟦X⟧) h1
  refine C_dvd_of_dvd_X_pow_mul c (n + m) a ⟨X ^ n * q, ?_⟩
  rw [pow_add, mul_assoc, hn]; ring

theorem algebraMap_EE (l : ℕ) (a : O⟦X⟧) : algebraMap O⟦X⟧ (EE O l) a =
    algebraMap (Localization.Away (X : O⟦X⟧)) (EE O l)
      (algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) a) := by
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply]; rfl

theorem saturated (l : ℕ) (a : O⟦X⟧) (k : ℕ)
    (h : (l : EE O l) ^ k ∣ algebraMap O⟦X⟧ (EE O l) a) : (l : O⟦X⟧) ^ k ∣ a := by
  rw [algebraMap_EE, ← map_natCast (algebraMap (Localization.Away (X : O⟦X⟧)) (EE O l)) l] at h
  have h2 := pow_dvd_of_pow_dvd _ k _ h
  have e : (l : O⟦X⟧) ^ k = C ((l : O) ^ k) := by rw [map_pow, map_natCast]
  rw [e]
  apply C_dvd_of_dvd_away
  rwa [← e, map_pow, map_natCast]

end GlobalTheory.NB.LT.EEBasic

namespace GlobalTheory.NB.LT

open EEBasic

theorem EE_basic : ∀ {l : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O], l.Prime → ¬ IsUnit (l : O) → Function.Injective (algebraMap O⟦X⟧ (EE O l)) ∧ IsUnit (algebraMap O⟦X⟧ (EE O l) X) ∧ IsAdicComplete (Ideal.span {(l : EE O l)}) (EE O l) ∧ (∀ (x : EE O l) (k : ℕ), ∃ (a : O⟦X⟧) (m : ℕ), (l : EE O l) ^ k ∣ x * algebraMap O⟦X⟧ (EE O l) (X ^ m) - algebraMap O⟦X⟧ (EE O l) a) ∧ (∀ (a : O⟦X⟧) (k : ℕ), (l : EE O l) ^ k ∣ algebraMap O⟦X⟧ (EE O l) a → (l : O⟦X⟧) ^ k ∣ a) := by
  intro l O _ _ _ _ _ _ hl
  refine ⟨?_, ?_, ?_, ?_, saturated l⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    refine PowerSeries.ext fun n => ?_
    rw [map_zero]
    refine IsHausdorff.haus (I := IsLocalRing.maximalIdeal O) inferInstance _ fun k => ?_
    have h1 := saturated l a k (by rw [ha]; exact dvd_zero _)
    have e : (l : O⟦X⟧) ^ k = C ((l : O) ^ k) := by rw [map_pow, map_natCast]
    rw [e, C_dvd_iff] at h1
    obtain ⟨q, hq⟩ := h1 n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hq]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ((IsLocalRing.mem_maximalIdeal _).2 hl) k)
  · rw [algebraMap_EE]
    exact (IsLocalization.Away.algebraMap_isUnit (X : O⟦X⟧)).map _
  · have := complete (l : Localization.Away (X : O⟦X⟧))
    rwa [map_natCast] at this
  · intro x k
    obtain ⟨c, hc⟩ := exists_pow_dvd_sub (l : Localization.Away (X : O⟦X⟧)) k x
    rw [map_natCast] at hc
    obtain ⟨m, q, hq⟩ := IsLocalization.Away.surj (X : O⟦X⟧) c
    refine ⟨q, m, ?_⟩
    rw [algebraMap_EE l q, ← hq, map_mul, algebraMap_EE, map_pow (algebraMap O⟦X⟧ _), ← sub_mul]
    exact hc.mul_right _

end GlobalTheory.NB.LT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootMulPowApprox
open PowerSeries

namespace GlobalTheory.PadicUnitGen

theorem dvd_iff_toZMod {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) :
    (l : ℤ_[l]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

theorem one_add_pow_eq {R : Type*} [CommRing R] (t : R) (j : ℕ) :
    ∃ z, (1 + t) ^ j = 1 + j * t + t ^ 2 * z := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨z, hz⟩ := ih
    exact ⟨j + z + t * z, by rw [pow_succ, hz]; push_cast; ring⟩

theorem exists_pow_approx {l : ℕ} [hl : Fact l.Prime] (u : ℤ_[l]) (h2 : l ≠ 2)
    (hu : Associated (u - 1) (l : ℤ_[l])) (x : ℤ_[l]) (hx : (l : ℤ_[l]) ∣ x - 1) (k : ℕ) :
    ∃ m : ℕ, (l : ℤ_[l]) ^ (k + 1) ∣ x - u ^ m := by
  obtain ⟨w, hw⟩ := hu.symm
  have hu' : u = 1 + l * (w : ℤ_[l]) := by rw [hw]; ring
  have h3 : 3 ≤ l := by
    have := hl.out.two_le
    omega
  have hl0 : PadicInt.toZMod (l : ℤ_[l]) = 0 := by simp
  have hw0 : PadicInt.toZMod (w : ℤ_[l]) ≠ 0 :=
    (w.isUnit.map (PadicInt.toZMod (p := l))).ne_zero
  have hu1 : PadicInt.toZMod u = 1 := by rw [hu']; simp
  induction k with
  | zero => exact ⟨0, by simpa using hx⟩
  | succ k ih =>
    obtain ⟨m, c, hc⟩ := ih
    obtain ⟨y, hy⟩ := ZMod.exists_one_add_mul_pow_prime_pow_eq (R := ℤ_[l]) (u := l) (v := l)
      hl.out dvd_rfl (by rw [← pow_two, ← pow_succ]; exact pow_dvd_pow _ h3) (w : ℤ_[l]) k
    rw [← hu'] at hy
    set j : ℕ := (PadicInt.toZMod c / PadicInt.toZMod (w : ℤ_[l])).val with hj
    obtain ⟨z, hz⟩ := one_add_pow_eq ((l : ℤ_[l]) ^ k * l * (w + l * y)) j
    refine ⟨m + l ^ k * j, ?_⟩
    have hd : (l : ℤ_[l]) ∣ c - u ^ m * (j * (w + l * y)
        + (l : ℤ_[l]) ^ k * l * (w + l * y) ^ 2 * z) := by
      rw [dvd_iff_toZMod]
      simp only [map_sub, map_mul, map_add (f := _), map_pow, hl0, hu1, map_natCast, hj,
        ZMod.natCast_zmod_val, ZMod.natCast_self]
      field_simp
      ring
    obtain ⟨d, hd⟩ := hd
    refine ⟨d, ?_⟩
    rw [pow_add, pow_mul, hy, hz]
    linear_combination hc + (l : ℤ_[l]) ^ (k + 1) * hd

theorem exists_lift {l : ℕ} [hl : Fact l.Prime] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ]
    (hΔ : Nat.card Δ = l - 1) (x : (ZMod l)ˣ) :
    ∃ δ ∈ Δ, PadicInt.toZMod (δ : ℤ_[l]) = x := by
  let f : Δ →* (ZMod l)ˣ :=
    (Units.map (PadicInt.toZMod (p := l) : ℤ_[l] →* ZMod l)).comp Δ.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro δ hδ
    have h1 : PadicInt.toZMod ((δ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := congrArg Units.val hδ
    have h2 : ((δ : ℤ_[l]ˣ) : ℤ_[l]) ^ (l - 1) = 1 := by
      have : δ ^ (l - 1) = 1 := by rw [← hΔ]; exact pow_card_eq_one'
      have := congrArg (fun t : Δ => ((t : ℤ_[l]ˣ) : ℤ_[l])) this
      simpa using this
    have h3 := geom_sum_mul ((δ : ℤ_[l]ˣ) : ℤ_[l]) (l - 1)
    rw [h2, sub_self] at h3
    rcases mul_eq_zero.1 h3 with h | h
    · exfalso
      have := congrArg (PadicInt.toZMod (p := l)) h
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_pow, h1, one_pow, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one, map_zero] at this
      rw [Nat.cast_pred hl.out.pos] at this
      simp at this
    · apply Subtype.ext
      apply Units.ext
      exact sub_eq_zero.1 h
  have hbij : Function.Bijective f := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hΔ, Nat.card_eq_fintype_card, ZMod.card_units]
  obtain ⟨δ, hδ⟩ := hbij.2 x
  exact ⟨δ, δ.2, congrArg Units.val hδ⟩

theorem exists_root_mul_pow_approx :
    ∀ {l : ℕ} [Fact l.Prime] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ] (u : ℤ_[l]), l ≠ 2 →
      Nat.card Δ = l - 1 → Associated (u - 1) (l : ℤ_[l]) → ∀ k a : ℕ, ¬ l ∣ a →
      ∃ δ ∈ Δ, ∃ m : ℕ, (l : ℤ_[l]) ^ k ∣ (a : ℤ_[l]) - (δ : ℤ_[l]) * u ^ m := by
  intro l hl Δ _ u h2 hΔ hu k a ha
  have ha0 : (a : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  obtain ⟨δ, hδ, hδa⟩ := exists_lift Δ hΔ (Units.mk0 _ ha0)
  have hx : (l : ℤ_[l]) ∣ (a : ℤ_[l]) * (δ⁻¹ : ℤ_[l]ˣ) - 1 := by
    have : (l : ℤ_[l]) ∣ (a : ℤ_[l]) - δ := by
      rw [dvd_iff_toZMod, map_sub, hδa]; simp
    have h := this.mul_right ((δ⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
    rwa [sub_mul, Units.mul_inv] at h
  obtain ⟨m, hm⟩ := exists_pow_approx u h2 hu _ hx k
  refine ⟨δ, hδ, m, (pow_dvd_pow _ (Nat.le_succ k)).trans ?_⟩
  have h := hm.mul_left (δ : ℤ_[l])
  rwa [mul_sub, mul_comm (a : ℤ_[l]), Units.mul_inv_cancel_left] at h

end GlobalTheory.PadicUnitGen
end

noncomputable section

open PowerSeries GlobalTheory.NB

namespace GlobalTheory.CycFr

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [CharZero O] [Algebra ℤ_[l] O]

section Descent

variable {Δ : Subgroup ℤ_[l]ˣ} {j : O⟦X⟧ →ₐ[O] O⟦X⟧} (hinj : Function.Injective j)
  (hr : ∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ Δ, act O (δ : ℤ_[l]) a = a)
include hinj hr

end Descent

omit [Algebra ℤ_[l] O] [IsDomain O] [CharZero O] [Fact l.Prime] in
theorem _root_.GlobalTheory.CycFr.constantCoeff_lvl (k : ℕ) :
    constantCoeff (_root_.GlobalTheory.CycFr.lvl l O k) = (l : O) := by
  unfold _root_.GlobalTheory.CycFr.lvl
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum]

omit [IsDomain O] [CharZero O] in
theorem _root_.GlobalTheory.CycFr.act_l_X :
    _root_.GlobalTheory.CycFr.act O (l : ℤ_[l]) X = X * _root_.GlobalTheory.CycFr.lvl l O 0 := by
  rw [_root_.GlobalTheory.CycFr.act_nat_X]
  have h := _root_.GlobalTheory.CycFr.mul_lvl (l := l) (O := O) 0
  simp only [pow_zero, pow_one, zero_add, add_sub_cancel_left] at h
  exact h.symm

omit [Algebra ℤ_[l] O] [CharZero O] in
theorem _root_.GlobalTheory.CycFr.sub_one_mem_max [IsLocalRing O] (hl : ¬ IsUnit (l : O)) (ζ : O)
    (hζ : ζ ^ l = 1) : ζ - 1 ∈ IsLocalRing.maximalIdeal O := by
  have hp : l.Prime := Fact.out
  have h0 : (l : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact hl
  haveI : CharP (IsLocalRing.ResidueField O) l := (CharP.charP_iff_prime_eq_zero hp).2 h0
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one]
  have h1 : (IsLocalRing.residue O ζ - 1) ^ l = 0 := by
    rw [sub_pow_char, ← map_pow, hζ, map_one, one_pow, sub_self]
  exact (pow_eq_zero_iff hp.ne_zero).mp h1

omit [Algebra ℤ_[l] O] [CharZero O] [Fact l.Prime] in
theorem _root_.GlobalTheory.CycFr.prime_X_sub_C [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : O) (hx : x ∈ IsLocalRing.maximalIdeal O) :
    Prime (X - C x : O⟦X⟧) ∧ ∀ d : O, (X - C x : O⟦X⟧) ∣ C d → d = 0 := by
  obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.NB.LT.exists_algEquiv_X_add_C (IsLocalRing.maximalIdeal O) x hx
  have hσC : ∀ d : O, σ (C d) = C d := fun d => by
    simpa using _root_.GlobalTheory.CycFr.algHom_C σ.toAlgHom d
  have hXσ : σ (X - C x) = X := by rw [map_sub, hσ, hσC]; ring
  refine ⟨?_, fun d hd => ?_⟩
  · have : Prime (σ (X - C x)) := by rw [hXσ]; exact X_prime
    exact (MulEquiv.prime_iff σ.toMulEquiv).mp this
  · have h := map_dvd σ hd
    rw [hXσ, hσC, X_dvd_iff, constantCoeff_C] at h
    exact h

section Fields

variable {Δ : Subgroup ℤ_[l]ˣ} {j : O⟦X⟧ →ₐ[O] O⟦X⟧} (hinj : Function.Injective j)
  (hr : ∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ Δ, act O (δ : ℤ_[l]) a = a) {s : ℕ}
  (hξ : Associated (j X) (X ^ s)) {E : O⟦X⟧} (hE : Associated (j E) (lvl l O 0))
include hinj hr hξ hE

end Fields

private lemma exists_descent_of_cyclotomic_action {Δ : Subgroup ℤ_[l]ˣ} {j : O⟦X⟧ →ₐ[O] O⟦X⟧}
    (hr : ∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ Δ, _root_.GlobalTheory.CycFr.act O (δ : ℤ_[l]) a = a)
    (hX : X ∣ j X) (c : ℤ_[l]) :
    ∃ ψ : O⟦X⟧ →ₐ[O] O⟦X⟧, ∀ a, j (ψ a) = _root_.GlobalTheory.CycFr.act O c (j a) := by
  have hinv : ∀ δ ∈ Δ, _root_.GlobalTheory.CycFr.act O (δ : ℤ_[l])
      (_root_.GlobalTheory.CycFr.act O c (j X)) = _root_.GlobalTheory.CycFr.act O c (j X) := by
    intro δ hδ
    rw [_root_.GlobalTheory.CycFr.act_comm, (hr (j X)).1 ⟨X, rfl⟩ δ hδ]
  obtain ⟨y, hy⟩ := (hr _).2 hinv
  have hy0 : constantCoeff y = 0 := by
    rw [← _root_.GlobalTheory.CycFr.constantCoeff_algHom j hX y, hy,
      _root_.GlobalTheory.CycFr.constantCoeff_act,
      _root_.GlobalTheory.CycFr.constantCoeff_algHom j hX, constantCoeff_X]
  have hs : HasSubst y := HasSubst.of_constantCoeff_zero hy0
  refine ⟨substAlgHom hs, fun a => ?_⟩
  have hX' : X ∣ _root_.GlobalTheory.CycFr.act O c (j X) := by
    obtain ⟨v, hv⟩ := hX
    rw [hv, map_mul]
    exact dvd_mul_of_dvd_left (_root_.GlobalTheory.CycFr.X_dvd_act_X c) _
  have key : j.comp (substAlgHom hs) = (_root_.GlobalTheory.CycFr.act O c).comp j := by
    apply _root_.GlobalTheory.CycFr.algHom_ext_X
    · simp only [AlgHom.comp_apply, coe_substAlgHom, subst_X hs, hy]
      exact hX'
    · simp only [AlgHom.comp_apply, coe_substAlgHom, subst_X hs, hy]
  exact congrArg (fun f => f a) key

private lemma dvd_of_invariant_map_dvd {Δ : Subgroup ℤ_[l]ˣ} {j : O⟦X⟧ →ₐ[O] O⟦X⟧}
    (hinj : Function.Injective j)
    (hr : ∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ Δ, _root_.GlobalTheory.CycFr.act O (δ : ℤ_[l]) a = a)
    {a b : O⟦X⟧} (hb : b ≠ 0) (h : j b ∣ j a) : b ∣ a := by
  obtain ⟨c, hc⟩ := h
  have hjb : j b ≠ 0 := fun h0 => hb (hinj (by rw [h0, map_zero]))
  have hinvc : ∀ δ ∈ Δ, _root_.GlobalTheory.CycFr.act O (δ : ℤ_[l]) c = c := by
    intro δ hδ
    have ha := (hr (j a)).1 ⟨a, rfl⟩ δ hδ
    have hb' := (hr (j b)).1 ⟨b, rfl⟩ δ hδ
    rw [hc, map_mul, hb'] at ha
    exact mul_left_cancel₀ hjb ha
  obtain ⟨c', rfl⟩ := (hr c).2 hinvc
  exact ⟨c', hinj (by rw [hc, map_mul])⟩

private lemma associated_of_associated_invariant_map {Δ : Subgroup ℤ_[l]ˣ} {j : O⟦X⟧ →ₐ[O] O⟦X⟧}
    (hinj : Function.Injective j)
    (hr : ∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ Δ, _root_.GlobalTheory.CycFr.act O (δ : ℤ_[l]) a = a)
    {a b : O⟦X⟧} (h : Associated (j a) (j b)) : Associated a b := by
  by_cases hb : b = 0
  · subst hb
    rw [map_zero, associated_zero_iff_eq_zero] at h
    rw [hinj (h.trans (map_zero j).symm)]
  · have ha : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact hb (hinj ((associated_zero_iff_eq_zero _).1 h.symm ▸ (map_zero j).symm))
    exact associated_of_dvd_dvd (dvd_of_invariant_map_dvd hinj hr ha h.dvd)
      (dvd_of_invariant_map_dvd hinj hr hb h.symm.dvd)

private lemma associated_pow_sub_one_prime_of_lt_prime {l : ℕ} [Fact l.Prime] (u : ℤ_[l])
    (hu : Associated (u - 1) (l : ℤ_[l])) {d : ℕ} (hd0 : 0 < d) (hdl : d < l) :
    Associated (u ^ d - 1) (l : ℤ_[l]) := by
  have hg : u ^ d - 1 = (u - 1) * ∑ i ∈ Finset.range d, u ^ i := (mul_geom_sum u d).symm
  have hS : IsUnit (∑ i ∈ Finset.range d, u ^ i) := by
    have hdiv : (l : ℤ_[l]) ∣ ∑ i ∈ Finset.range d, u ^ i - d := by
      have : ∑ i ∈ Finset.range d, u ^ i - d = ∑ i ∈ Finset.range d, (u ^ i - 1) := by
        rw [Finset.sum_sub_distrib]; simp
      rw [this]
      exact Finset.dvd_sum fun i _ => hu.symm.dvd.trans (by simpa using sub_dvd_pow_sub_pow u 1 i)
    obtain ⟨m, hm⟩ := hdiv
    by_contra hnu
    have hmem : ∑ i ∈ Finset.range d, u ^ i ∈ IsLocalRing.maximalIdeal ℤ_[l] :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hmem
    have h1 : ∑ i ∈ Finset.range d, u ^ i = d + l * m := by linear_combination hm
    rw [h1, map_add (f := _), map_mul, map_natCast, map_natCast, ZMod.natCast_self, zero_mul, add_zero,
      ZMod.natCast_eq_zero_iff] at hmem
    exact Nat.not_dvd_of_pos_of_lt hd0 hdl hmem
  rw [hg]
  exact (associated_mul_unit_left _ _ hS).trans hu

theorem _root_.GlobalTheory.CycFr.exists_frame [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ] (u : ℤ_[l]ˣ) (ξ : O⟦X⟧) (hl2 : l ≠ 2) (hl : ¬ IsUnit (l : O))
    (hζ : ∃ ζ : O, IsPrimitiveRoot ζ l) (hξ : Associated ξ (X ^ Nat.card Δ))
    (hinv : ∀ δ ∈ Δ, _root_.GlobalTheory.CycFr.act O (δ : ℤ_[l]) ξ = ξ)
    (hu : Associated ((u : ℤ_[l]) - 1) (l : ℤ_[l])) :
    ∃ (R : _root_.GlobalTheory.NB.Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧), j X = ξ ∧ Function.Injective j ∧
      (∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ Δ, _root_.GlobalTheory.CycFr.act O (δ : ℤ_[l]) a = a) ∧
      (∀ a, j (R.φ a) = _root_.GlobalTheory.CycFr.act O (l : ℤ_[l]) (j a)) ∧
      (∀ a, j (R.γ a) = _root_.GlobalTheory.CycFr.act O (u : ℤ_[l]) (j a)) ∧
      (R.χ : O) = algebraMap ℤ_[l] O u ∧ R.s = Nat.card Δ ∧
      Associated (j R.E) (_root_.GlobalTheory.CycFr.lvl l O 0) ∧
      ∀ τ, ∃ ζ : O, IsPrimitiveRoot ζ l ∧ X - C (ζ - 1) ∣ ξ - C (R.ϖ τ) := by

  classical
  have hp : l.Prime := Fact.out
  have hd : 0 < Nat.card Δ := Nat.card_pos
  obtain ⟨e, ϖ, hed, hϖ, hϖsub, hprod, hroot⟩ :=
    _root_.GlobalTheory.CycRoots.exists_roots Δ ξ hl2 hl hζ hξ hinv
  have hξX : X ∣ ξ := (dvd_pow_self X hd.ne').trans hξ.symm.dvd
  have hξ0 : constantCoeff ξ = 0 := X_dvd_iff.mp hξX
  have hs : HasSubst ξ := HasSubst.of_constantCoeff_zero hξ0
  set j : O⟦X⟧ →ₐ[O] O⟦X⟧ := substAlgHom hs with hjdef
  have hjX : j X = ξ := by rw [hjdef, coe_substAlgHom, subst_X hs]
  have hjC : ∀ c : O, j (C c) = C c := fun c => by
    simpa using _root_.GlobalTheory.CycFr.algHom_C j c
  obtain ⟨hinj, hr⟩ := _root_.GlobalTheory.CycFr.injective_and_range_eq_invariants Δ j (hjX ▸ hξ)
    (by rw [hjX]; exact hinv)
  have hXj : X ∣ j X := hjX ▸ hξX
  obtain ⟨φ, hφ⟩ := exists_descent_of_cyclotomic_action hr hXj (l : ℤ_[l])
  obtain ⟨γ, hγ⟩ := exists_descent_of_cyclotomic_action hr hXj (u : ℤ_[l])
  have hϖmem : ∀ τ, ϖ τ ∈ IsLocalRing.maximalIdeal O := by
    intro τ
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu'
    exact hl ((hϖ τ).isUnit_iff.mp (hu'.pow _))
  choose lev hlev using fun τ =>
    _root_.GlobalTheory.NB.LT.exists_algEquiv_X_add_C (IsLocalRing.maximalIdeal O) (ϖ τ) (hϖmem τ)
  set E : O⟦X⟧ := ∏ τ, (X - C (ϖ τ)) with hEdef
  have hjE : j E = ∏ τ, (ξ - C (ϖ τ)) := by
    rw [hEdef, map_prod]
    exact Finset.prod_congr rfl fun τ _ => by rw [map_sub, hjX, hjC]
  have hjEassoc : Associated (j E) (_root_.GlobalTheory.CycFr.lvl l O 0) := hjE ▸ hprod
  have hcomm : ∀ a, φ (γ a) = γ (φ a) := fun a => hinj (by
    rw [hφ, hγ, hγ, hφ, _root_.GlobalTheory.CycFr.act_comm])
  have hφX : ∃ v : O⟦X⟧ˣ, φ X = (v : O⟦X⟧) * X * E ^ Nat.card Δ := by
    have hA : Associated (j (φ X)) (j (X * E ^ Nat.card Δ)) := by
      obtain ⟨w, hw⟩ := hξ.symm
      rw [hφ, hjX, ← hw, map_mul, map_pow, _root_.GlobalTheory.CycFr.act_l_X, map_mul, map_pow, hjX, ← hw]
      have hu1 : IsUnit (_root_.GlobalTheory.CycFr.act O (l : ℤ_[l]) (w : O⟦X⟧)) := w.isUnit.map _
      refine (associated_mul_unit_left _ _ hu1).trans ?_
      rw [mul_pow]
      exact (associated_mul_unit_right _ _ w.isUnit).mul_mul hjEassoc.symm.pow_pow
    obtain ⟨c, hc⟩ := associated_of_associated_invariant_map hinj hr hA
    refine ⟨c⁻¹, ?_⟩
    have h1 : φ X = X * E ^ Nat.card Δ * ((c⁻¹ : O⟦X⟧ˣ) : O⟦X⟧) := by
      rw [← hc, mul_assoc, Units.mul_inv, mul_one]
    rw [h1]; ring
  have hγX : ∃ κ : O⟦X⟧ˣ, γ X = X * (1 + (κ : O⟦X⟧) * E) ∧
      constantCoeff (1 + (κ : O⟦X⟧) * E) = algebraMap ℤ_[l] O u ^ Nat.card Δ := by
    obtain ⟨w, hw⟩ := hξ.symm
    have hlvl0 : (1 + X : O⟦X⟧) ^ l - 1 = X * _root_.GlobalTheory.CycFr.lvl l O 0 := by
      rw [← _root_.GlobalTheory.CycFr.act_l_X, _root_.GlobalTheory.CycFr.act_nat_X]
    have hXlvl : ¬ X ∣ _root_.GlobalTheory.CycFr.lvl l O 0 := by
      rw [X_dvd_iff, _root_.GlobalTheory.CycFr.constantCoeff_lvl]
      exact Nat.cast_ne_zero.mpr hp.ne_zero
    have hdiff : X ^ Nat.card Δ * _root_.GlobalTheory.CycFr.lvl l O 0 ∣
        _root_.GlobalTheory.CycFr.act O (u : ℤ_[l]) ξ - ξ := by
      have h1 := _root_.GlobalTheory.CycFr.dvd_act_sub (O := O) 1 (u : ℤ_[l]) 1
        (by rw [pow_one]; exact hu.symm.dvd) ξ
      rw [_root_.GlobalTheory.CycFr.act_one, pow_one, hlvl0] at h1
      obtain ⟨z, hz⟩ := h1
      have h2 : X ^ Nat.card Δ ∣ _root_.GlobalTheory.CycFr.act O (u : ℤ_[l]) ξ - ξ := by
        refine dvd_sub ?_ hξ.symm.dvd
        rw [← hw, map_mul, map_pow]
        exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (_root_.GlobalTheory.CycFr.X_dvd_act_X _) _) _
      rw [hz] at h2
      obtain ⟨d', hd'⟩ : ∃ d', Nat.card Δ = d' + 1 := ⟨Nat.card Δ - 1, by omega⟩
      rw [hd', pow_succ', mul_assoc] at h2
      have h3 := (mul_dvd_mul_iff_left (X_ne_zero (R := O))).mp h2
      obtain ⟨y, hy⟩ := (X_prime (R := O)).pow_dvd_of_dvd_mul_left d' hXlvl h3
      have h5 : X ^ Nat.card Δ * _root_.GlobalTheory.CycFr.lvl l O 0 ∣
          X * _root_.GlobalTheory.CycFr.lvl l O 0 * z :=
        ⟨y, by rw [hd', hy]; ring⟩
      exact h5.trans (dvd_of_eq hz.symm)
    have hE0 : E ≠ 0 := by
      intro h0
      have h := hjEassoc.symm
      rw [h0, map_zero, associated_zero_iff_eq_zero] at h
      have h' := congrArg constantCoeff h
      rw [_root_.GlobalTheory.CycFr.constantCoeff_lvl, map_zero] at h'
      exact (Nat.cast_ne_zero.mpr hp.ne_zero) h'
    have hXE : X * E ∣ γ X - X := by
      apply dvd_of_invariant_map_dvd hinj hr (mul_ne_zero X_ne_zero hE0)
      have hA : Associated (j (X * E)) (X ^ Nat.card Δ * _root_.GlobalTheory.CycFr.lvl l O 0) := by
        rw [map_mul, hjX]
        exact hξ.mul_mul hjEassoc
      refine hA.dvd.trans ?_
      rw [map_sub, hγ, hjX]
      exact hdiff
    obtain ⟨κ', hκ'⟩ := hXE
    have hγX' : γ X = X * (1 + κ' * E) := by linear_combination hκ'
    obtain ⟨V, hV, hV0⟩ := _root_.GlobalTheory.CycFr.exists_act_X (O := O) (u : ℤ_[l])
    have hcc : constantCoeff (1 + κ' * E) = algebraMap ℤ_[l] O u ^ Nat.card Δ := by
      have h1 := congrArg j hγX'
      rw [hγ, hjX, map_mul, hjX, ← hw, map_mul, map_pow, hV, mul_pow, mul_assoc, mul_assoc] at h1
      have h2 := mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) h1
      have h3 := congrArg constantCoeff h2
      rw [map_mul, map_mul, map_pow, hV0, _root_.GlobalTheory.CycFr.constantCoeff_act,
        _root_.GlobalTheory.CycFr.constantCoeff_algHom j hXj] at h3
      have hw0 : IsUnit (constantCoeff (w : O⟦X⟧)) := w.isUnit.map _
      exact (mul_right_cancel₀ hw0.ne_zero (by rw [h3, mul_comm])).symm
    have hκunit : IsUnit (constantCoeff κ') := by
      have hEl : Associated (constantCoeff E) (l : O) := by
        have := hjEassoc.map constantCoeff
        rwa [_root_.GlobalTheory.CycFr.constantCoeff_algHom j hXj,
          _root_.GlobalTheory.CycFr.constantCoeff_lvl] at this
      have hul : Associated (algebraMap ℤ_[l] O u ^ Nat.card Δ - 1) (l : O) := by
        have he1 : 0 < e := by
          rcases Nat.eq_zero_or_pos e with h | h
          · rw [h, zero_mul] at hed
            have := hp.two_le
            omega
          · exact h
        have hdl : Nat.card Δ < l := by
          have := Nat.le_mul_of_pos_left (Nat.card Δ) he1
          have := hp.two_le
          omega
        have := (associated_pow_sub_one_prime_of_lt_prime (u : ℤ_[l]) hu hd hdl).map (algebraMap ℤ_[l] O)
        simpa using this
      have h1 : constantCoeff κ' * constantCoeff E = algebraMap ℤ_[l] O u ^ Nat.card Δ - 1 := by
        rw [← hcc, map_add (f := _), map_one, map_mul]; ring
      obtain ⟨a, ha⟩ := hEl
      obtain ⟨b, hb⟩ := hul
      have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      have hne : algebraMap ℤ_[l] O u ^ Nat.card Δ - 1 ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hb
        exact hl0 hb.symm
      have h2 : constantCoeff κ' * ↑b = ↑a := by
        apply mul_left_cancel₀ hne
        linear_combination constantCoeff κ' * hb + (a : O) * h1 - constantCoeff κ' * ha
      have h3 : constantCoeff κ' = ↑(a * b⁻¹) := by
        rw [Units.val_mul, ← h2, mul_assoc, Units.mul_inv, mul_one]
      rw [h3]
      exact Units.isUnit _
    refine ⟨(isUnit_iff_constantCoeff.mpr hκunit).unit, ?_, ?_⟩
    · simpa using hγX'
    · simpa using hcc
  obtain ⟨v, hv⟩ := hφX
  obtain ⟨κ, hκ, hκ0⟩ := hγX
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, zero_mul] at hed
      have := hp.two_le
      omega
    · exact h
  have hroot' : ∃ x : O, Associated (x ^ (l - 1)) (l : O) := by
    obtain ⟨ζ, w, hζτ, hw, -⟩ := hroot ⟨0, he⟩
    have hmem := _root_.GlobalTheory.CycFr.sub_one_mem_max hl ζ hζτ.pow_eq_one
    obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.NB.LT.exists_algEquiv_X_add_C (IsLocalRing.maximalIdeal O) _ hmem
    have hσC : ∀ c : O, σ (C c) = C c := fun c => by
      simpa using _root_.GlobalTheory.CycFr.algHom_C σ.toAlgHom c
    have hX' : σ (X - C (ζ - 1)) = X := by rw [map_sub, hσ, hσC]; ring
    have h1 : constantCoeff (σ ξ) = ϖ ⟨0, he⟩ := by
      have h0 := congrArg (fun b => constantCoeff (σ b)) hw
      rw [map_mul σ, hX', map_mul, constantCoeff_X, zero_mul, map_sub, map_sub, hσC,
        constantCoeff_C] at h0
      exact sub_eq_zero.mp h0
    obtain ⟨w', hw'⟩ := hξ.symm
    rw [← hw', map_mul, map_pow, hσ, map_mul, map_pow, map_add (f := _), constantCoeff_X, constantCoeff_C,
      zero_add] at h1
    have hunit : IsUnit (constantCoeff (σ (w' : O⟦X⟧))) :=
      (PowerSeries.isUnit_iff_constantCoeff).mp (w'.isUnit.map σ)
    refine ⟨ζ - 1, ?_⟩
    have h2 : Associated ((ζ - 1) ^ Nat.card Δ) (ϖ ⟨0, he⟩) := by
      have : ϖ ⟨0, he⟩ = (ζ - 1) ^ Nat.card Δ * constantCoeff (σ (w' : O⟦X⟧)) := by
        exact h1.symm
      rw [this]
      exact associated_mul_unit_right _ _ hunit
    rw [← hed, mul_comm, pow_mul]
    exact (h2.pow_pow).trans (hϖ ⟨0, he⟩)
  have hχ : Associated (algebraMap ℤ_[l] O u - 1) (l : O) := by
    have := hu.map (algebraMap ℤ_[l] O)
    simpa using this
  have hunits := _root_.GlobalTheory.NB.LT.EE_basic (O := O) hp hl
  obtain ⟨hEEinj, hEEX, hEEc, hEEd, hEEs⟩ := hunits
  have hEunit : IsUnit (algebraMap O⟦X⟧ (_root_.GlobalTheory.NB.LT.EE O l) E) := by
    rw [hEdef, map_prod]
    refine IsUnit.prod_univ_iff.mpr fun τ => ?_
    obtain ⟨x, hx⟩ := hEEX
    set y := ((x⁻¹ : (_root_.GlobalTheory.NB.LT.EE O l)ˣ) :
      _root_.GlobalTheory.NB.LT.EE O l)
    set t := algebraMap O⟦X⟧ (_root_.GlobalTheory.NB.LT.EE O l) (C (ϖ τ)) * y
    have hsplit : algebraMap O⟦X⟧ (_root_.GlobalTheory.NB.LT.EE O l) (X - C (ϖ τ)) =
        algebraMap O⟦X⟧ (_root_.GlobalTheory.NB.LT.EE O l) X * (t * (-1) + 1) := by
      rw [map_sub, ← hx]
      simp only [t, y]
      linear_combination (algebraMap O⟦X⟧ (_root_.GlobalTheory.NB.LT.EE O l) (C (ϖ τ))) *
        Units.mul_inv x
    rw [hsplit]
    refine (hx ▸ x.isUnit).mul (Ideal.mem_jacobson_bot.mp ?_ (-1))
    have he : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · exact absurd (Fin.elim0 (h ▸ τ)) id
      · exact h
    apply (Ideal.isRadical_jacobson (⊥ : Ideal (_root_.GlobalTheory.NB.LT.EE O l))) ⟨e, ?_⟩
    apply IsAdicComplete.le_jacobson_bot (Ideal.span {(l : _root_.GlobalTheory.NB.LT.EE O l)})
    obtain ⟨c, hc⟩ := hϖ τ
    have hϖl : ϖ τ ^ e = (l : O) * ((c⁻¹ : Oˣ) : O) := by rw [← hc, mul_assoc, Units.mul_inv, mul_one]
    have hmem : algebraMap O⟦X⟧ (_root_.GlobalTheory.NB.LT.EE O l) (C (ϖ τ ^ e)) ∈
        Ideal.span {(l : _root_.GlobalTheory.NB.LT.EE O l)} := by
      rw [hϖl, map_mul, map_mul, map_natCast, map_natCast]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    rw [mul_pow, ← map_pow, ← map_pow]
    exact Ideal.mul_mem_right _ _ hmem
  have hφunit : IsUnit (algebraMap O⟦X⟧ (_root_.GlobalTheory.NB.LT.EE O l) (φ X)) := by
    rw [hv, map_mul, map_mul, map_pow]
    exact ((v.isUnit.map _).mul hEEX).mul (hEunit.pow _)
  have hγunit : IsUnit (algebraMap O⟦X⟧ (_root_.GlobalTheory.NB.LT.EE O l) (γ X)) := by
    have h1 : IsUnit (1 + (κ : O⟦X⟧) * E) := by
      rw [PowerSeries.isUnit_iff_constantCoeff, hκ0]
      exact ((u.isUnit.map (algebraMap ℤ_[l] O)).pow _)
    rw [hκ, map_mul]
    exact hEEX.mul (h1.map _)
  obtain ⟨φE, hφE⟩ := _root_.GlobalTheory.NB.LT.exists_EE_extension φ hφunit
  obtain ⟨γE, hγE⟩ := _root_.GlobalTheory.NB.LT.exists_EE_extension γ hγunit

  have hφk : ∀ k b, j ((φ ^ k) b) = _root_.GlobalTheory.CycFr.act O ((l : ℤ_[l]) ^ k) (j b) := by
    intro k
    induction k with
    | zero => intro b; simp [_root_.GlobalTheory.CycFr.act_one]
    | succ k ih =>
      intro b
      rw [pow_succ', AlgHom.mul_apply, hφ, ih, ← _root_.GlobalTheory.CycFr.act_mul, pow_succ']
  have hγk : ∀ k b, j ((γ ^ k) b) = _root_.GlobalTheory.CycFr.act O ((u : ℤ_[l]) ^ k) (j b) := by
    intro k
    induction k with
    | zero => intro b; simp [_root_.GlobalTheory.CycFr.act_one]
    | succ k ih =>
      intro b
      rw [pow_succ', AlgHom.mul_apply, hγ, ih, ← _root_.GlobalTheory.CycFr.act_mul, pow_succ']
  have hEk : ∀ k, Associated (j ((φ ^ k) E)) (_root_.GlobalTheory.CycFr.lvl l O k) := by
    intro k
    rw [hφk, ← _root_.GlobalTheory.CycFr.act_l_pow_lvl]
    exact hjEassoc.map (_root_.GlobalTheory.CycFr.act O ((l : ℤ_[l]) ^ k))
  have hEk0 : ∀ k, (φ ^ k) E ≠ 0 := by
    intro k h0
    have h := (hEk k).symm
    rw [h0, map_zero, associated_zero_iff_eq_zero] at h
    have h' := congrArg constantCoeff h
    rw [_root_.GlobalTheory.CycFr.constantCoeff_lvl, map_zero] at h'
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) h'
  have hred : ∀ k a, (φ ^ k) E ∣ a ^ 2 → (φ ^ k) E ∣ a := by
    intro k a h
    apply dvd_of_invariant_map_dvd hinj hr (hEk0 k)
    refine (hEk k).dvd.trans ?_
    apply _root_.GlobalTheory.CycFr.Red.lvl_dvd_of_dvd_sq hl
    rw [← map_pow]
    exact (hEk k).symm.dvd.trans (map_dvd j h)
  have htriv : ∀ k a, (φ ^ k) E ∣ (γ ^ l ^ k) a - a := by
    intro k a
    apply dvd_of_invariant_map_dvd hinj hr (hEk0 k)
    refine (hEk k).dvd.trans ?_
    rw [map_sub, hγk]
    have hlu : (l : ℤ_[l]) ^ (k + 1) ∣ (u : ℤ_[l]) ^ l ^ k - 1 ^ l ^ k :=
      dvd_sub_pow_of_dvd_sub hu.symm.dvd k
    rw [one_pow] at hlu
    have h1 := _root_.GlobalTheory.CycFr.dvd_act_sub (O := O) (k + 1) _ _ hlu (j a)
    rw [_root_.GlobalTheory.CycFr.act_one] at h1
    refine (Dvd.intro_left _ (_root_.GlobalTheory.CycFr.mul_lvl k)).trans h1

  have hjC' : ∀ c : O, j (C c) = C c := hjC
  have hγC : ∀ c : O, γ (C c) = C c := fun c => by
    simpa using _root_.GlobalTheory.CycFr.algHom_C γ c
  have hchilev : ∀ τ, ∃ W, γ (X - C (ϖ τ)) = (X - C (ϖ τ)) * W ∧
      constantCoeff (lev τ W) = ((Units.map (algebraMap ℤ_[l] O).toMonoidHom u : Oˣ) : O) := by
    intro τ
    obtain ⟨ζ, w, hζτ, hw, hndvd⟩ := hroot τ
    have hmem := _root_.GlobalTheory.CycFr.sub_one_mem_max hl ζ hζτ.pow_eq_one
    obtain ⟨σ', hσ'⟩ :=
      _root_.GlobalTheory.NB.LT.exists_algEquiv_X_add_C (IsLocalRing.maximalIdeal O) _ hmem
    have hσ'C : ∀ c : O, σ' (C c) = C c := fun c => by
      simpa using _root_.GlobalTheory.CycFr.algHom_C σ'.toAlgHom c
    have hσC : ∀ c : O, lev τ (C c) = C c := fun c => by
      simpa using _root_.GlobalTheory.CycFr.algHom_C (lev τ).toAlgHom c
    have hσinv : (lev τ).symm X = X - C (ϖ τ) := by
      apply (lev τ).injective
      rw [AlgEquiv.apply_symm_apply, map_sub, hlev, hσC]; ring
    have hA : ∀ b, constantCoeff (σ' (j b)) = constantCoeff (lev τ b) := by
      intro b
      set g : O⟦X⟧ →ₐ[O] O⟦X⟧ := σ'.toAlgHom.comp (j.comp (lev τ).symm.toAlgHom) with hg
      have hgX : X ∣ g X := by
        simp only [hg, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe]
        show X ∣ σ' (j ((lev τ).symm X))
        rw [hσinv, map_sub, hjX, hjC, hw, map_mul, map_sub, hσ', hσ'C, add_sub_cancel_right]
        exact dvd_mul_right _ _
      have := _root_.GlobalTheory.CycFr.constantCoeff_algHom g hgX (lev τ b)
      simpa [hg] using this
    have hB2 : ∀ (c c' : ℤ_[l]) b, (l : ℤ_[l]) ∣ c - c' →
        constantCoeff (σ' (_root_.GlobalTheory.CycFr.act O c b)) =
        constantCoeff (σ' (_root_.GlobalTheory.CycFr.act O c' b)) := by
      intro c c' b hcc
      have h1 := _root_.GlobalTheory.CycFr.dvd_act_sub (O := O) 1 c c'
        (by rw [pow_one]; exact hcc) b
      rw [pow_one] at h1
      obtain ⟨q, hq⟩ := h1
      have h2 := congrArg (fun y => constantCoeff (σ' y)) hq
      simp only [map_sub, map_mul, map_pow, map_add (f := _), map_one, hσ', hσ'C, constantCoeff_X,
        constantCoeff_C, zero_add, add_sub_cancel_left, hζτ.pow_eq_one, sub_self, zero_mul] at h2
      rw [add_sub_cancel, hζτ.pow_eq_one, sub_self, zero_mul] at h2
      exact sub_eq_zero.mp h2
    have hB : ∀ b, constantCoeff (σ' (_root_.GlobalTheory.CycFr.act O (u : ℤ_[l]) b)) =
        constantCoeff (σ' b) := by
      intro b
      rw [hB2 (u : ℤ_[l]) 1 b hu.symm.dvd, _root_.GlobalTheory.CycFr.act_one]
    have hval : constantCoeff (lev τ (γ X)) = ϖ τ := by
      rw [← hA, hγ, hjX, hB, ← hjX, hA, hlev, map_add (f := _), constantCoeff_X, constantCoeff_C, zero_add]
    have hdvd := _root_.GlobalTheory.CycFr.dvd_sub_C_of_shift (ϖ τ) (lev τ) (hlev τ) (γ X)
    rw [hval] at hdvd
    obtain ⟨W, hW⟩ := hdvd
    refine ⟨W, by rw [map_sub, hγC, hW], ?_⟩
    set P : O⟦X⟧ := X - C (ζ - 1) with hP
    have hPσ : σ' P = X := by rw [hP, map_sub, hσ', hσ'C]; ring
    have hP0 : P ≠ 0 := fun h0 => by
      have := congrArg σ' h0
      rw [hPσ, map_zero] at this
      exact X_ne_zero this
    have hevP : constantCoeff (σ' (_root_.GlobalTheory.CycFr.act O (u : ℤ_[l]) P)) = 0 := by
      rw [hB, hPσ, constantCoeff_X]
    obtain ⟨Q, hQ⟩ : P ∣ _root_.GlobalTheory.CycFr.act O (u : ℤ_[l]) P := by
      have := _root_.GlobalTheory.CycFr.dvd_sub_C_of_shift (ζ - 1) σ' hσ'
        (_root_.GlobalTheory.CycFr.act O (u : ℤ_[l]) P)
      rwa [hevP, map_zero, sub_zero] at this
    have hQval : constantCoeff (σ' Q) = algebraMap ℤ_[l] O u := by
      have hd1 := congrArg (fun y => constantCoeff (σ' (d⁄dX y))) hQ
      have hdP : d⁄dX P = 1 := by rw [hP, map_sub, derivative_X, derivative_C, sub_zero]
      rw [Derivation.leibniz, hdP, smul_eq_mul, smul_eq_mul, mul_one, map_add (f := _), map_mul, hPσ, map_add (f := _), map_mul, constantCoeff_X,
        zero_mul, zero_add] at hd1
      rw [← hd1, hP]
      simp only [map_sub, _root_.GlobalTheory.CycFr.act_X, _root_.GlobalTheory.CycFr.act_C,
        derivative_C, Derivation.map_one_eq_zero, sub_zero, map_zero,
        _root_.GlobalTheory.CycFr.derivative_bin, map_mul, hσ'C, constantCoeff_C]
      rw [← _root_.GlobalTheory.CycFr.act_one_add_X,
        hB2 ((u : ℤ_[l]) - 1) ((0 : ℕ) : ℤ_[l]) _ (by rw [Nat.cast_zero, sub_zero]; exact hu.symm.dvd),
        _root_.GlobalTheory.CycFr.act_one_add_X, _root_.GlobalTheory.CycFr.bin_nat, pow_zero,
        map_one, map_one, mul_one]
    have hrel : Q * _root_.GlobalTheory.CycFr.act O (u : ℤ_[l]) w = w * j W := by
      apply mul_left_cancel₀ hP0
      have h1 := congrArg j hW
      rw [map_sub, hγ, hjX, hjC, map_mul, map_sub, hjX, hjC] at h1
      have h2 : _root_.GlobalTheory.CycFr.act O (u : ℤ_[l]) ξ - C (ϖ τ) =
          _root_.GlobalTheory.CycFr.act O (u : ℤ_[l]) (ξ - C (ϖ τ)) := by
        rw [map_sub, _root_.GlobalTheory.CycFr.act_C]
      rw [h2, hw, map_mul, hQ] at h1
      linear_combination h1
    have hev := congrArg (fun y => constantCoeff (σ' y)) hrel
    simp only [map_mul, hB, hA] at hev
    have hw0 : constantCoeff (σ' w) ≠ 0 := by
      intro h0
      apply hndvd
      have := _root_.GlobalTheory.CycFr.dvd_sub_C_of_shift (ζ - 1) σ' hσ' w
      rwa [h0, map_zero, sub_zero] at this
    rw [hQval] at hev
    show constantCoeff (lev τ W) = algebraMap ℤ_[l] O u
    exact mul_right_cancel₀ hw0 (by linear_combination -hev)

  have hγφk : ∀ k b, γ ((φ ^ k) b) = (φ ^ k) (γ b) := fun k b => hinj (by
    rw [hγ, hφk, hφk, hγ, _root_.GlobalTheory.CycFr.act_comm])
  have hEγ : E ∣ γ E := by
    choose Wc hWc _ using hchilev
    rw [hEdef, map_prod]
    refine ⟨∏ τ, Wc τ, ?_⟩
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => hWc τ
  have hinvk : ∀ k (e1 : e = 1) a, (φ ^ k) E ∣ γ a - a → ∃ c, (φ ^ k) E ∣ a - C c := by
    intro k he1 a h
    have hcard : Nat.card Δ = l - 1 := by rw [he1, one_mul] at hed; exact hed
    have hstab : ∀ x, (φ ^ k) E ∣ x → (φ ^ k) E ∣ γ x := by
      rintro x ⟨y, rfl⟩
      rw [map_mul, hγφk]
      exact dvd_mul_of_dvd_left (map_dvd (φ ^ k) hEγ) _
    have hm : ∀ m, (φ ^ k) E ∣ (γ ^ m) a - a := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have : (γ ^ (m + 1)) a - a = γ ((γ ^ m) a - a) + (γ a - a) := by
          rw [pow_succ', AlgHom.mul_apply, map_sub]; ring
        rw [this]
        exact dvd_add (hstab _ ih) h
    have hall : ∀ a' : ℕ, ¬ l ∣ a' → _root_.GlobalTheory.CycFr.lvl l O k ∣
        _root_.GlobalTheory.CycFr.act O (a' : ℤ_[l]) (j a) - j a := by
      intro a' ha'
      obtain ⟨δ, hδ, m, hδm⟩ := _root_.GlobalTheory.PadicUnitGen.exists_root_mul_pow_approx Δ (u : ℤ_[l]) hl2 hcard hu
        (k + 1) a' ha'
      have h1 := _root_.GlobalTheory.CycFr.dvd_act_sub (O := O) (k + 1) _ _ hδm (j a)
      have h2 : _root_.GlobalTheory.CycFr.act O ((δ : ℤ_[l]) * (u : ℤ_[l]) ^ m) (j a) =
          j ((γ ^ m) a) := by
        rw [_root_.GlobalTheory.CycFr.act_mul, ← hγk]
        exact (hr _).1 ⟨_, rfl⟩ δ hδ
      rw [h2] at h1
      have h3 : _root_.GlobalTheory.CycFr.act O (a' : ℤ_[l]) (j a) - j a =
          (_root_.GlobalTheory.CycFr.act O (a' : ℤ_[l]) (j a) - j ((γ ^ m) a)) +
            j ((γ ^ m) a - a) := by rw [map_sub]; ring
      rw [h3]
      refine dvd_add ((Dvd.intro_left _ (_root_.GlobalTheory.CycFr.mul_lvl k)).trans h1) ?_
      exact (hEk k).symm.dvd.trans (map_dvd j (hm m))
    obtain ⟨c, hc⟩ := _root_.GlobalTheory.CycFr.exists_const_of_lvl_invariant hl k (j a) hall
    refine ⟨c, dvd_of_invariant_map_dvd hinj hr (hEk0 k) ?_⟩
    rw [map_sub, hjC]
    exact (hEk k).dvd.trans hc
  refine ⟨{
      prime := hp
      odd := hl2
      l_nonunit := hl
      root := hroot'
      e := e
      s := Nat.card Δ
      es := hed
      ϖ := ϖ
      ϖ_val := hϖ
      ϖ_sub := hϖsub
      E := E
      E_def := rfl
      φ := φ
      γ := γ
      comm := hcomm
      u := v
      φ_X := hv
      κ := κ
      γ_X := hκ
      χ := Units.map (algebraMap ℤ_[l] O).toMonoidHom u
      χ_gen := by simpa using hχ
      χ_zero := by simpa using hκ0
      lev := lev
      lev_X := hlev
      χ_lev := hchilev
      lvl_red := hred
      lvl_triv := htriv
      lvl_inv := fun he1 k a h => hinvk k he1 a h
      EE := _root_.GlobalTheory.NB.LT.EE O l
      EE_inj := hEEinj
      EE_X := hEEX
      EE_complete := hEEc
      EE_dense := hEEd
      EE_sat := hEEs
      φE := φE
      φE_ext := hφE
      γE := γE
      γE_ext := hγE }, j, hjX, hinj, hr, hφ, hγ, rfl, rfl, hjEassoc, fun τ => ?_⟩
  obtain ⟨ζ, w, hζτ, hw, -⟩ := hroot τ
  exact ⟨ζ, hζτ, ⟨w, hw⟩⟩

end GlobalTheory.CycFr
