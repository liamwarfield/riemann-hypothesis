module

public import Formalism.LocalToGlobal.HilbertRowConditions.KaTiedIffKapDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedLatticeDiagonalBasePointMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdDiscrTorsionField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscFieldEqTorsionField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmallFieldClassFieldPieces
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMemDifferentIdeal
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.RayDiscr

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem exists_ideal {L' : Type} [Field L'] [NumberField L'] [Algebra K L'] [Algebra L' L] [IsScalarTower K L' L]
    [IsGalois K L'] {𝔪 : Ideal (𝓞 K)} (h : IsRayField K L 𝔪) (σ : L ≃ₐ[K] L) :
    ∃ I : Ideal (𝓞 K), I ≠ 0 ∧ IsCoprime I 𝔪 ∧ (∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = χ σ) ∧
      ∀ χ : (L' ≃ₐ[K] L') →* ℂˣ, heckeIdeal L' χ I = χ (AlgEquiv.restrictNormalHom L' σ) := by
  obtain ⟨hab, hun, hgen, -⟩ := h
  have hσ : σ ∈ Subgroup.closure _ := hgen ▸ Subgroup.mem_top σ
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨𝔭, hp, hx⟩ := hx
    refine ⟨𝔭.asIdeal, 𝔭.ne_bot, ?_, fun χ => ?_, fun χ => ?_⟩
    · rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      have := 𝔭.isMaximal.eq_of_le hne le_sup_left
      exact hp (Ideal.dvd_iff_le.2 (this ▸ le_sup_right))
    · rw [GlobalTheory.NT.Model.heckeIdeal_prime, heckeVal_of_unramIn L χ (hun 𝔭 hp) hx]
    · rw [GlobalTheory.NT.Model.heckeIdeal_prime, heckeVal_of_unramIn L' χ (GlobalTheory.RayMaximal.unramIn_of_tower (hun 𝔭 hp))
        (GlobalTheory.RayMaximal.isFrob_restrictNormal hx)]
      rfl
  | one =>
    exact ⟨1, one_ne_zero, isCoprime_one_left, fun χ => by rw [GlobalTheory.NT.Model.heckeIdeal_top, map_one, Units.val_one],
      fun χ => by rw [GlobalTheory.NT.Model.heckeIdeal_top, map_one, map_one, Units.val_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨I, hI, hc, h1, h2⟩ := hx
    obtain ⟨J, hJ, hc', h3, h4⟩ := hy
    refine ⟨I * J, mul_ne_zero hI hJ, hc.mul_left hc', fun χ => ?_, fun χ => ?_⟩
    · rw [GlobalTheory.NT.Model.heckeIdeal_mul L χ hI hJ, h1, h3, map_mul, Units.val_mul]
    · rw [GlobalTheory.NT.Model.heckeIdeal_mul L' χ hI hJ, h2, h4, map_mul, map_mul, Units.val_mul]
  | inv x _ hx =>
    obtain ⟨I, hI, hc, h1, h2⟩ := hx
    have e : x⁻¹ = x ^ (Nat.card (L ≃ₐ[K] L) - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel Nat.card_pos, pow_card_eq_one']
    refine ⟨I ^ (Nat.card (L ≃ₐ[K] L) - 1), pow_ne_zero _ hI, hc.pow_left, fun χ => ?_, fun χ => ?_⟩
    · rw [RayExp.heckeIdeal_pow L χ hI, h1, e, map_pow, Units.val_pow_eq_pow_val]
    · rw [RayExp.heckeIdeal_pow L' χ hI, h2, e, map_pow, map_pow, Units.val_pow_eq_pow_val]

theorem pow_absNorm_sub_one (𝔭 : HeightOneSpectrum (𝓞 K)) {x : 𝓞 K} (hx : x ∉ 𝔭.asIdeal) :
    x ^ (Ideal.absNorm 𝔭.asIdeal - 1) - 1 ∈ 𝔭.asIdeal := by
  have := 𝔭.isMaximal
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  let _ := Fintype.ofFinite (𝓞 K ⧸ 𝔭.asIdeal)
  let _ := Ideal.Quotient.field 𝔭.asIdeal
  rw [← Ideal.Quotient.eq, map_pow, map_one, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one _ (mt Ideal.Quotient.eq_zero_iff_mem.1 hx)

theorem inertia_pow (hR : RayField) (𝔭 : HeightOneSpectrum (𝓞 K)) {𝔪 : Ideal (𝓞 K)} (hm : 𝔪 ≠ ⊥)
    (hp : ¬ 𝔭.asIdeal ∣ 𝔪) (h : IsRayField K L (𝔭.asIdeal * 𝔪)) {σ : L ≃ₐ[K] L} (hσ : InInertia L 𝔭 σ) :
    σ ^ (Ideal.absNorm 𝔭.asIdeal - 1) = 1 := by
  obtain ⟨L', _, _, _, _, h'⟩ := hR K 𝔪 hm
  have := h.1
  obtain ⟨f⟩ := nonempty_algHom_of_isRay_of_dvd (L := L) (L' := L') (mul_ne_zero 𝔭.ne_bot hm) (dvd_mul_left 𝔪 _) h.2 h'
  let _ := f.toRingHom.toAlgebra
  have : IsScalarTower K L' L := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  obtain ⟨I, hI, hc, h1, h2⟩ := exists_ideal (L' := L') h σ
  have hres : AlgEquiv.restrictNormalHom L' σ = 1 := by
    obtain ⟨P, hP, hPo, hx⟩ := hσ
    refine h'.1 𝔭 hp _ ⟨P.under (𝓞 L'), inferInstance, inferInstance, fun x => ?_⟩
    have h1 : algebraMap (𝓞 L') (𝓞 L) (AlgEquiv.restrictNormalHom L' σ • x) = σ • algebraMap (𝓞 L') (𝓞 L) x :=
      RingOfIntegers.ext (σ.restrictNormal_commutes L' x)
    rw [Ideal.mem_under, map_sub, h1]
    exact hx _
  obtain ⟨α, β, ⟨-, hb, -, hb', hab, hpos⟩, e⟩ := (h'.2.2 I hI hc.of_mul_right_right).1 fun χ => by
    rw [h2, hres, map_one, Units.val_one]
  obtain ⟨x, rfl⟩ : β ∣ α := by
    rw [← Ideal.mem_span_singleton, ← Ideal.dvd_span_singleton, ← e]
    exact dvd_mul_left _ _
  have hb0 : Ideal.span {β} ≠ 0 := by simpa using hb
  obtain rfl : I = Ideal.span {x} := by
    rw [← Ideal.span_singleton_mul_span_singleton, mul_comm] at e
    exact mul_left_cancel₀ hb0 e
  have hx0 : x ≠ 0 := by simpa using hI
  have hx1 : x - 1 ∈ 𝔪 := by
    rw [← Ideal.dvd_span_singleton] at hab ⊢
    rw [show β * x - β = β * (x - 1) by ring, ← Ideal.span_singleton_mul_span_singleton] at hab
    exact hb'.symm.dvd_of_dvd_mul_left hab
  have hxp : x ∉ 𝔭.asIdeal := fun hx => 𝔭.prime.not_isUnit
    (hc.of_mul_right_left.isUnit_of_dvd' (Ideal.dvd_span_singleton.2 hx) dvd_rfl)
  have hcp : IsCoprime 𝔭.asIdeal 𝔪 := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have := 𝔭.isMaximal.eq_of_le hne le_sup_left
    exact hp (Ideal.dvd_iff_le.2 (this ▸ le_sup_right))
  set n := Ideal.absNorm 𝔭.asIdeal - 1
  have h3 := (h.2.2.2 (Ideal.span {x} ^ n) (pow_ne_zero _ hI) hc.pow_left).2 ⟨x ^ n, 1, ⟨pow_ne_zero _ hx0,
    one_ne_zero, by rw [← Ideal.span_singleton_pow]; exact hc.pow_left,
    by rw [Ideal.span_singleton_one, ← Ideal.one_eq_top]; exact isCoprime_one_left, ?_, fun φ => ?_⟩,
    by rw [Ideal.span_singleton_one, Ideal.mul_top, Ideal.span_singleton_pow]⟩
  · refine GlobalTheory.RayMaximal.eq_of_forall_char fun χ => Units.ext ?_
    rw [map_pow, Units.val_pow_eq_pow_val, ← h1, ← RayExp.heckeIdeal_pow L χ hI, h3, map_one, Units.val_one]
  · rw [← Ideal.dvd_span_singleton]
    refine hcp.mul_dvd (Ideal.dvd_span_singleton.2 (pow_absNorm_sub_one 𝔭 hxp)) (Ideal.dvd_span_singleton.2 ?_)
    obtain ⟨c, hc⟩ := sub_one_dvd_pow_sub_one x n
    rw [hc]
    exact 𝔪.mul_mem_right _ hx1
  · have h4 := hpos φ
    have h5 : φ ((β * x : 𝓞 K) : K) * φ β = φ x * (φ β * φ β) := by
      rw [show ((β * x : 𝓞 K) : K) = (β : K) * (x : K) from rfl, map_mul]; ring
    rw [h5] at h4
    have h6 : 0 < φ x := by nlinarith [mul_self_nonneg (φ β)]
    simpa using pow_pos h6 n

theorem exists_intTrace_not_mem [IsGalois K L] (P Q : Ideal (𝓞 L)) [P.IsPrime] (hPQ : P ⊔ Q = ⊤)
    (he : ((Nat.card (P.inertia (L ≃ₐ[K] L)) : ℕ) : 𝓞 L) ∉ P) :
    ∃ x ∈ Q, algebraMap (𝓞 K) (𝓞 L) (Algebra.intTrace (𝓞 K) (𝓞 L) x) ∉ P := by
  classical
  by_contra! H
  obtain ⟨a, ha, x, hx, hax⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hPQ)
  let f : (L ≃ₐ[K] L) → (𝓞 L →* 𝓞 L ⧸ P) := fun σ =>
    ((Ideal.Quotient.mk P).comp (MulSemiringAction.toRingHom (L ≃ₐ[K] L) (𝓞 L) σ)).toMonoidHom
  have hf : ∀ σ y, f σ y = Ideal.Quotient.mk P (σ • y) := fun _ _ => rfl
  have hx1 : f 1 x = 1 := by
    rw [hf, one_smul, ← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq, ← hax]
    simpa using ha
  have h0 : ∑ σ, Finsupp.single (f σ) (f σ x) = 0 := by
    refine linearIndependent_iff.1 (linearIndependent_monoidHom (𝓞 L) (𝓞 L ⧸ P)) _ (funext fun y => ?_)
    have h1 := Ideal.Quotient.eq_zero_iff_mem.2 (H _ (Q.mul_mem_right y hx))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GlobalTheory.DifferentBound.algebraMap_intTrace_eq_sum, map_sum] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finsupp.linearCombination_single, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      ← map_mul, hf]
    simpa only [smul_mul'] using h1
  have h2 := DFunLike.congr_fun h0 (f 1)
  have h3 : ∀ σ, Finsupp.single (f σ) (f σ x) (f 1) = if σ ∈ P.inertia (L ≃ₐ[K] L) then 1 else 0 := by
    intro σ
    have : σ ∈ P.inertia (L ≃ₐ[K] L) ↔ f σ = f 1 := by
      rw [MonoidHom.ext_iff]
      refine forall_congr' fun y => ?_
      rw [hf, hf, one_smul, Ideal.Quotient.eq]
      rfl
    rw [Finsupp.single_apply, this]
    split_ifs with h
    · rw [h, hx1]
    · rfl
  rw [Finsupp.finsetSum_apply] at h2
  simp only [h3, Finset.sum_boole, Finsupp.zero_apply] at h2
  apply he
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h2

theorem not_sq_dvd {M : ℕ} (hM : Squarefree M) (hc : Nat.Coprime M (discr K).natAbs) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    ¬ 𝔭.asIdeal ^ 2 ∣ Ideal.span {(M : 𝓞 K)} := by
  intro h
  have := 𝔭.isMaximal
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 K ⧸ 𝔭.asIdeal)
  have hpp : p.Prime := CharP.char_is_prime (𝓞 K ⧸ 𝔭.asIdeal) p
  have key : ∀ n : ℕ, (n : 𝓞 K) ∈ 𝔭.asIdeal ↔ p ∣ n := fun n => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero_iff _ p]
  obtain ⟨m, rfl⟩ := (key M).1 (Ideal.dvd_span_singleton.1 ((dvd_pow_self _ two_ne_zero).trans h))
  have hm : ¬ 𝔭.asIdeal ∣ Ideal.span {(m : 𝓞 K)} := fun hd =>
    hpp.prime.not_isUnit (hM p (mul_dvd_mul_left p ((key m).1 (Ideal.dvd_span_singleton.1 hd))))
  rw [Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton] at h
  have h1 := 𝔭.prime.pow_dvd_of_dvd_mul_right 2 hm h
  have hZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hpp
  have : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hZ.ne_zero).2 hZ).isMaximal (by simpa using hpp.ne_zero)
  have h2 := pow_sub_one_dvd_differentIdeal ℤ (p := Ideal.span {(p : ℤ)}) 𝔭.asIdeal 2 (by simpa using hpp.ne_zero)
    (by simpa [Ideal.map_span] using h1)
  have h3 := Ideal.le_of_dvd h2 (Ideal.absNorm_mem _)
  rw [absNorm_differentIdeal K, pow_one, key] at h3
  exact hpp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc (dvd_mul_right p m) h3)

theorem card_not_mem {G : Type} [Group G] [Finite G] (P : Ideal (𝓞 L)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) {n : ℕ} (hn0 : n ≠ 0)
    (hn : (n : 𝓞 L) ∈ P) (h : ∀ g : G, g ^ (n - 1) = 1) : ((Nat.card G : ℕ) : 𝓞 L) ∉ P := by
  have : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hP0
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 L ⧸ P)
  have hpp : p.Prime := CharP.char_is_prime (𝓞 L ⧸ P) p
  have key : ∀ n : ℕ, (n : 𝓞 L) ∈ P ↔ p ∣ n := fun n => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero_iff _ p]
  rw [key] at hn ⊢
  intro hd
  have := Fact.mk hpp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : p ∣ n - 1 := hg ▸ orderOf_dvd_of_pow_eq_one (h g)
  have h2 := Nat.dvd_sub hn h1
  rw [show n - (n - 1) = 1 by omega] at h2
  exact hpp.one_lt.ne' (Nat.dvd_one.1 h2)

theorem natCast_mem_differentIdeal (hR : RayField) {M : ℕ} (hM : Squarefree M) (hc : Nat.Coprime M (discr K).natAbs)
    (h : IsRayField K L (natIdeal K M)) : (M : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  classical
  have := h.1
  have hD0 : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := differentIdeal_ne_bot
  have hI : Ideal.span {(M : 𝓞 L)} ≠ ⊥ := by simpa using hM.ne_zero
  rw [← Ideal.dvd_span_singleton, UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hD0]
  intro P hP
  have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
  have hP0 : P ≠ ⊥ := hP.ne_zero
  have hPm := hPp.isMaximal hP0
  have hp : P.under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP0
  let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨P.under (𝓞 K), inferInstance, hp⟩
  by_cases hnP : 𝔭.asIdeal ∣ natIdeal K M
  · obtain ⟨Q, hPQ, e⟩ := Ideal.eq_prime_pow_mul_coprime hI P
    obtain ⟨𝔪, hm⟩ := hnP
    have hm0 : 𝔪 ≠ ⊥ := by
      rintro rfl
      exact hM.ne_zero (by simpa using hm)
    have hpm : ¬ 𝔭.asIdeal ∣ 𝔪 := fun hd => not_sq_dvd hM hc 𝔭 (by
      rw [show Ideal.span {(M : 𝓞 K)} = _ from hm, sq]
      exact mul_dvd_mul_left _ hd)
    have he := card_not_mem (G := P.inertia (L ≃ₐ[K] L)) P hP0 (n := Ideal.absNorm 𝔭.asIdeal)
      (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hp)
      (by simpa using Ideal.mem_comap.1 (Ideal.absNorm_mem (P.under (𝓞 K))))
      fun g => Subtype.ext (inertia_pow hR 𝔭 hm0 hpm (hm ▸ h) ⟨P, hPp, ⟨rfl⟩, g.2⟩)
    obtain ⟨x, hx, htr⟩ := exists_intTrace_not_mem P Q hPQ he
    have h1 := not_dvd_differentIdeal_of_intTrace_not_mem (𝓞 K) (p := natIdeal K M) _ Q
      (by rw [Ideal.map_span, Set.image_singleton, map_natCast]; exact e.symm) x hx
      fun hmem => htr (Ideal.le_of_dvd ⟨𝔪, hm⟩ hmem)
    exact (emultiplicity_lt_iff_not_dvd.2 h1).le.trans (le_emultiplicity_of_pow_dvd ⟨Q, e⟩)
  · have h2 := GlobalTheory.DifferentBound.not_dvd_of_inertia K L P hP0 fun σ hσ => h.2.1 𝔭 hnP σ ⟨P, hPp, ⟨rfl⟩, hσ⟩
    rw [emultiplicity_eq_zero.2 h2]
    exact zero_le

theorem natAbs_discr_dvd : RayField → ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (M : ℕ), Squarefree M → Nat.Coprime M (discr K).natAbs → IsRayField K L (natIdeal K M) →
      (discr L).natAbs ∣ (discr K).natAbs ^ Module.finrank K L * M ^ Module.finrank ℚ L := by
  intro hR K L _ _ _ _ _ M hM hc h
  have h1 := map_dvd Ideal.absNorm (Ideal.dvd_span_singleton.2 (natCast_mem_differentIdeal hR hM hc h))
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h1
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L), mul_comm]
  exact mul_dvd_mul_left _ h1

end GlobalTheory.Mem.RayDiscr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeDvdOfMemDifferent
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.Mem.FieldsEx
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KPsiRam

theorem prime_dvd_of_mem_different (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (N : ℕ) (hmem : (N : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L)) {p : ℕ} (hp : p.Prime) (h : p ∣ (discr L).natAbs) :
    p ∣ N ∨ p ∣ (discr K).natAbs := by
  have h1 := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have h2 : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) ∣ Ideal.absNorm (Ideal.span {(N : 𝓞 L)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  rw [Ideal.absNorm_span_natCast] at h2
  rw [h1] at h
  exact ((Nat.Prime.dvd_mul hp).1 h).imp (fun h => hp.dvd_of_dvd_pow (h.trans h2)) hp.dvd_of_dvd_pow

theorem sup_adjoin_root (F : IntermediateField ℚ ℂ) [NumberField F] {k : ℕ} (hk : 0 < k) {y : F}
    (hy : y ∈ powIdealElts F k) {z : ℂ} (hz : z ^ k = (y : ℂ)) :
    ∃ _ : NumberField ↥(F ⊔ ℚ⟮z⟯), ∀ p : ℕ, p.Prime → p ∣ (discr ↥(F ⊔ ℚ⟮z⟯)).natAbs →
      p ∣ k ∨ p ∣ (discr F).natAbs := by
  obtain ⟨hy, I, hI⟩ := hy
  have hI' : (I : Submodule (𝓞 F) F) ^ k = Submodule.span (𝓞 F) {y} := by
    rw [← FractionalIdeal.coe_pow, ← hI, FractionalIdeal.coe_spanSingleton]
  set L : IntermediateField ℚ ℂ := F ⊔ ℚ⟮z⟯ with hLdef
  have hzL : z ∈ L := (le_sup_right : ℚ⟮z⟯ ≤ L) (IntermediateField.mem_adjoin_simple_self ℚ z)
  have hzF : IsIntegral F z := IsIntegral.of_pow hk (by rw [hz]; exact isIntegral_algebraMap (x := y))
  have hzQ : IsIntegral ℚ z := isIntegral_trans z hzF
  haveI : FiniteDimensional ℚ ℚ⟮z⟯ := IntermediateField.adjoin.finiteDimensional hzQ
  have hLfin : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_sup F ℚ⟮z⟯
  letI : NumberField L := NumberField.mk
  letI : Algebra F L := (IntermediateField.inclusion (le_sup_left : F ≤ L)).toRingHom.toAlgebra
  haveI : IsScalarTower F L ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hz' : (⟨z, hzL⟩ : L) ^ k = algebraMap F L y := Subtype.ext hz
  have hzi : IsIntegral F (⟨z, hzL⟩ : L) := Algebra.IsIntegral.isIntegral _
  have htop : F⟮(⟨z, hzL⟩ : L)⟯ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨w, hw⟩ -
    let M : IntermediateField ℚ ℂ :=
      ((F⟮(⟨z, hzL⟩ : L)⟯).map (IsScalarTower.toAlgHom F L ℂ)).restrictScalars ℚ
    have hM : L ≤ M := by
      refine sup_le (fun v hv => ?_) (IntermediateField.adjoin_simple_le_iff.mpr ?_)
      · exact ((F⟮(⟨z, hzL⟩ : L)⟯).map (IsScalarTower.toAlgHom F L ℂ)).algebraMap_mem ⟨v, hv⟩
      · exact ⟨_, IntermediateField.mem_adjoin_simple_self F _, rfl⟩
    obtain ⟨w', hw', hww⟩ := hM hw
    have : w' = ⟨w, hw⟩ := Subtype.ext hww
    rwa [this] at hw'
  have htop' : Algebra.adjoin F {(⟨z, hzL⟩ : L)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hzi.isAlgebraic, htop,
      IntermediateField.top_toSubalgebra]
  have hD := GlobalTheory.FieldSize.natCast_mem_differentIdeal_of_root k hk y hy _ hI' _ hz' htop'
  exact ⟨inferInstance, fun p hp h => prime_dvd_of_mem_different F L k hD hp h⟩

theorem sup_adjoin_roots {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) {h : ℕ} (hh : 0 < h) (S : Set ℂ)
    (hS : S.Finite) (hS' : ∀ z ∈ S, ∃ y ∈ powIdealElts E h, z ^ h = φ y) :
    ∃ _ : NumberField ↥(imField φ ⊔ IntermediateField.adjoin ℚ S), ∀ p : ℕ, p.Prime →
      p ∣ (discr ↥(imField φ ⊔ IntermediateField.adjoin ℚ S)).natAbs → p ∣ h ∨ p ∣ (discr E).natAbs := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    rw [IntermediateField.adjoin_empty, sup_bot_eq]
    let e₀ : E ≃ₐ[ℚ] imField φ := AlgEquiv.ofInjectiveField φ.toRatAlgHom
    have : FiniteDimensional ℚ (imField φ) := e₀.toLinearEquiv.finiteDimensional
    have hN : NumberField (imField φ) := NumberField.of_module_finite ℚ _
    exact ⟨hN, fun p _ hp => Or.inr (by rwa [discr_eq_discr_of_algEquiv _ e₀])⟩
  | @insert z S _ _ ih =>
    obtain ⟨_, ih⟩ := ih fun w hw => hS' w (Set.mem_insert_of_mem _ hw)
    obtain ⟨y, hy, hz⟩ := hS' z (Set.mem_insert _ _)
    have hE : ∀ x, φ x ∈ imField φ ⊔ IntermediateField.adjoin ℚ S := (imField_le_iff φ).1 le_sup_left
    obtain ⟨hN, H⟩ := sup_adjoin_root _ hh (map_mem_pow (φ.codRestrict _ hE) hy) hz
    rw [Set.insert_eq, Set.union_comm, IntermediateField.adjoin_union, ← sup_assoc]
    exact ⟨hN, fun p hp hd => (H p hp hd).elim Or.inl (ih p hp)⟩

theorem typeNorm_mem {R : Ranks} (H : Host R) (p q : ℕ) {h : ℕ} {γ : H.E} (hγ : γ ∈ powIdealElts H.E h) :
    typeNorm H p q γ ∈ powIdealElts H.E h := by
  have hσ : ∀ (σ : H.E ≃ₐ[ℚ] H.E) {x}, x ∈ powIdealElts H.E h → σ x ∈ powIdealElts H.E h :=
    fun σ _ hx => map_mem_pow (σ : H.E →+* H.E) hx
  exact prod_mem_pow _ _ fun g _ => mul_mem_pow (npow_mem_pow (hσ _ hγ) _) (npow_mem_pow (hσ _ (hσ _ hγ)) _)

theorem prime_dvd_discr_iSup_kPsi : ∀ (P : Pre) (δ : FieldDat P),
    ∃ _ : NumberField ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j), ∀ p : ℕ, p.Prime →
      p ∣ (discr ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j)).natAbs → p ∣ classNumber P.host.E * (discr P.host.E).natAbs := by
  intro P δ
  let S : Set ℂ := {rootOne (classNumber P.host.E)} ∪ ⋃ j ∈ Set.Icc 1 P.R.m, ⋃ i,
    {z | z ^ δ.basis.h i = P.host.φ₀ (typeNorm P.host (P.R.sigW j).1 (P.R.sigW j).2 (δ.basis.γ i : P.host.E))}
  have hS : S.Finite := by
    refine (Set.finite_singleton _).union ((Set.finite_Icc _ _).biUnion fun j _ => Set.finite_iUnion fun i => ?_)
    refine Set.Finite.subset (Polynomial.nthRoots (δ.basis.h i) (P.host.φ₀
      (typeNorm P.host (P.R.sigW j).1 (P.R.sigW j).2 (δ.basis.γ i : P.host.E)))).toFinset.finite_toSet fun z hz => ?_
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots (δ.basis.h_pos i)]
    exact hz
  have hS' : ∀ z ∈ S, ∃ y ∈ powIdealElts P.host.E (classNumber P.host.E), z ^ classNumber P.host.E = P.host.φ₀ y := by
    rintro z (rfl | hz)
    · exact ⟨1, one_mem_pow, by
        rw [map_one]; exact (Complex.isPrimitiveRoot_exp _ (classNumber_ne_zero _)).pow_eq_one⟩
    · simp only [Set.mem_iUnion] at hz
      obtain ⟨j, -, i, hz⟩ := hz
      have hγ : (δ.basis.γ i : P.host.E) ∈ powIdealElts P.host.E (δ.basis.h i) :=
        ⟨(δ.basis.γ i).ne_zero, δ.basis.c i, by
          rw [← coe_toPrincipalIdeal, ← δ.basis.pow_eq i, Units.val_pow_eq_pow_val]; rfl⟩
      obtain ⟨k, hk⟩ : δ.basis.h i ∣ classNumber P.host.E := orderOf_dvd_card
      refine ⟨_, hk ▸ pow_mem_powIdealElts (typeNorm_mem P.host (P.R.sigW j).1 (P.R.sigW j).2 hγ) k, ?_⟩
      rw [hk, pow_mul, map_pow]
      exact congrArg (· ^ k) hz
  obtain ⟨_, H⟩ := sup_adjoin_roots P.host.φ₀ (classNumber_pos P.host.E) S hS hS'
  have hle : (⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) ≤ imField P.host.φ₀ ⊔ IntermediateField.adjoin ℚ S := by
    refine iSup₂_le fun j hj => sup_le (sup_le le_sup_left (le_sup_of_le_right ?_)) (le_sup_of_le_right ?_)
    · exact IntermediateField.adjoin.mono _ _ _ Set.subset_union_left
    · refine IntermediateField.adjoin.mono _ _ _ ?_
      rintro z ⟨i, hz⟩
      exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hj, Set.mem_iUnion.2 ⟨i, hz⟩⟩)
  have : FiniteDimensional ℚ ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion hle).injective
  have hN : NumberField ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) := NumberField.mk
  letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  refine ⟨hN, fun p hp hd => (Nat.Prime.dvd_mul hp).2 (H p hp (hd.trans ?_))⟩
  exact Int.natAbs_dvd_natAbs.2 (discr_dvd_discr _ _)

end GlobalTheory.Mem.KPsiRam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmallFieldClassFieldPieces
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host Formalism.L2.Rows GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open GlobalTheory.HilbertInClosure
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.SmallFieldPieces

section Copy

variable (ι : Qb →+* ℂ)

theorem qb_eq_of_map {L : Fld} {M : IntermediateField ℚ ℂ} (h : L.map ι.toRatAlgHom = M) : qb ι M = L := by
  rw [← h, qb, IntermediateField.comap_map]

theorem map_qb (M : IntermediateField ℚ ℂ) [Algebra.IsAlgebraic ℚ M] : (qb ι M).map ι.toRatAlgHom = M := by
  refine IntermediateField.map_comap_eq_self fun z hz => ?_
  exact exists_eq_of_isAlgebraic ι
    (IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (⟨z, hz⟩ : M)))

theorem qb_mono {M N : IntermediateField ℚ ℂ} (h : M ≤ N) : qb ι M ≤ qb ι N := fun _ hx => h hx

theorem finrank_qb (M : IntermediateField ℚ ℂ) [Algebra.IsAlgebraic ℚ M] :
    Module.finrank ℚ (qb ι M) = Module.finrank ℚ M :=
  (AlgEquiv.ofRingEquiv (R := ℚ) (f := qbEquiv ι M) fun q => by simp).toLinearEquiv.finrank_eq

theorem discr_qb (M : IntermediateField ℚ ℂ) [NumberField M] [NumberField (qb ι M)] : discr (qb ι M) = discr M :=
  discr_eq_discr_of_ringEquiv _ (qbEquiv ι M)

theorem qb_imField {E : Type} [Field E] [NumberField E] (j : E →ₐ[ℚ] Qb) (φ : E →+* ℂ) (h : ∀ x, ι (j x) = φ x) :
    qb ι (imField φ) = j.fieldRange := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, ι.injective ((h y).trans hy)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, (h y).symm⟩

theorem qb_cycField {n : ℕ} (hn : n ≠ 0) : qb ι (cycField n) = muFld n := by
  refine qb_eq_of_map ι ?_
  rw [muFld, IntermediateField.adjoin_map]
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (cycField_le_iff.2 ?_)
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_cycField hn (by rw [← map_pow, show x ^ n = 1 from hx, map_one])
  · have h1 : rootOne n ^ n = 1 := (Complex.isPrimitiveRoot_exp n hn).pow_eq_one
    obtain ⟨x, hx⟩ := exists_eq_of_isAlgebraic ι (z := rootOne n)
      (IsAlgebraic.of_pow (Nat.pos_of_ne_zero hn) (h1 ▸ isAlgebraic_one))
    exact IntermediateField.subset_adjoin ℚ _ ⟨x, ι.injective (by rw [map_pow, hx, h1, map_one]), hx⟩

theorem qb_KC (d : ℕ) : qb ι (KC d) = KQ d := by
  refine qb_eq_of_map ι ?_
  rw [KQ, sqQ, IntermediateField.adjoin_map]
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_simple_le_iff.2 ?_)
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : ι x ^ 2 = sqrtNegNat d ^ 2 := by
      rw [← map_pow, show x ^ 2 = _ from hx, sqrtNegNat_sq]
      simp
    have h2 := IntermediateField.mem_adjoin_simple_self ℚ (sqrtNegNat d)
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact (show ι x ∈ KC d from h ▸ h2)
    · exact (show ι x ∈ KC d from h ▸ neg_mem h2)
  · obtain ⟨x, hx⟩ := exists_eq_of_isAlgebraic ι (z := sqrtNegNat d)
      (IsAlgebraic.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isAlgebraic_nat d).neg))
    refine IntermediateField.subset_adjoin ℚ _ ⟨x, ι.injective ?_, hx⟩
    rw [map_pow, hx, sqrtNegNat_sq]
    simp

end Copy

theorem abelOver_of_isAbelianGalois {E : Type} [Field E] [NumberField E] (j : E →ₐ[ℚ] Qb) (L : Fld)
    (h : j.fieldRange ≤ L) (hab : letI := algThrough j L h; IsAbelianGalois E L) : AbelOver j.fieldRange L := by
  have hm : ∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → σ ∈ GalOf j.fieldRange := fun σ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2
  refine ⟨h, fun σ hσ => map_mem_of_normal j L h ?_ σ (hm σ hσ),
    fun σ τ hσ hτ => (isAbelianGalois_iff j L h).1 hab σ (hm σ hσ) τ (hm τ hτ)⟩
  let := algThrough j L h
  infer_instance

theorem isHilbertCF_qb (hA : GlobalArtinReciprocity) (hW : WeberRayFieldSt) (ι : Qb →+* ℂ) {d : ℕ}
    {F : IntermediateField ℚ ℂ} {A : WeierstrassCurve F} (hd : d.Prime) (h4 : d % 4 = 3) (h3 : 3 < d)
    (hF : IsGoodCMCurve d F A) :
    ∃ (_ : NumberField (hilbertField d F)) (_ : FiniteDimensional ℚ (qb ι (hilbertField d F))),
      IsHilbertCF d (qb ι (hilbertField d F)) := by
  obtain ⟨hN, hdisc, h2, hR⟩ := isRayFieldIn_hilbertField hW d F A hd h4 h3 hF
  have hx : (IntermediateField.AdjoinSimple.gen ℚ (sqrtNegNat d)) ^ 2 =
      -(d : ℚ⟮sqrtNegNat d⟯) := Subtype.ext (by simpa using sqrtNegNat_sq d)
  have hTC := isTotallyComplex_of_sq_eq_neg hd.pos hx
  let j : ℚ⟮sqrtNegNat d⟯ →ₐ[ℚ] Qb :=
    ((qb ι ℚ⟮sqrtNegNat d⟯).val.toRingHom.comp (qbEquiv ι ℚ⟮sqrtNegNat d⟯).symm.toRingHom).toRatAlgHom
  have hj : ∀ x, ι (j x) = x := fun x =>
    congrArg Subtype.val ((qbEquiv ι ℚ⟮sqrtNegNat d⟯).apply_symm_apply x)
  have hr : j.fieldRange = KQ d := by
    rw [← qb_KC ι d, ← qb_imField ι j (ℚ⟮sqrtNegNat d⟯.val : ℚ⟮sqrtNegNat d⟯ →+* ℂ) hj]
    exact congrArg _ (le_antisymm (fun _ ⟨x, hx⟩ => hx ▸ x.2) fun z hz => ⟨⟨z, hz⟩, rfl⟩)
  have he : (ℚ⟮sqrtNegNat d⟯.val : ℚ⟮sqrtNegNat d⟯ →+* ℂ) = ι.comp j.toRingHom := RingHom.ext fun x => (hj x).symm
  obtain ⟨hN', h, hab, hd', hmax⟩ := hilbert_qb hA _ j ι _ (he ▸ hR)
  rw [hdisc, h2, Int.natAbs_neg, Int.natAbs_natCast] at hd' hmax
  refine ⟨hR.numberField, inferInstance, hr ▸ abelOver_of_isAbelianGalois j _ h hab, hd', fun L _ hL hU => ?_⟩
  have : NumberField L := {}
  rw [← hr] at hL
  refine hmax L hL.1 ((isAbelianGalois_iff j L hL.1).2 fun σ hσ τ hτ => hL.2.2 σ τ ?_ ?_) hU
  exacts [(IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ]

theorem squarefree_modulus (P : Pre) : Squarefree (modulus P) := by
  have g0 := P.host.g_prime 0
  have g1 := P.host.g_prime 1
  have p0 := P.host.pde_prime
  have p1 := P.host.pde'_prime
  simp only [modulus, Nat.squarefree_mul_iff, Nat.coprime_mul_iff_left, Nat.coprime_primes, g0, g1, p0, p1,
    g0.squarefree, g1.squarefree, p0.squarefree, p1.squarefree, and_true]
  exact ⟨⟨⟨(P.host.pde_ne_g 0).2.symm, (P.host.pde_ne_g 1).2.symm⟩, P.host.pde_ne⟩,
    ⟨(P.host.pde_ne_g 0).1.symm, (P.host.pde_ne_g 1).1.symm⟩, P.host.g_ne⟩

theorem coprime_discr {R : Ranks} (H : Host R) {p : ℕ} (hp : p % (H.QS * H.q * H.d) = 1) :
    Nat.Coprime p (discr H.E).natAbs := by
  have hc : Nat.Coprime p (H.QS * H.q * H.d) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hp, Nat.gcd_one_left]
  refine Nat.Coprime.symm (Nat.coprime_of_dvd fun k hk h1 h2 => ?_)
  exact hk.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc h2 (H.der.discr_primes.1 k hk (Int.natCast_dvd.2 h1)))

theorem ray_qb (hA : GlobalArtinReciprocity) {P : Pre} (δ : FieldDat P) (T : Frame P.host) :
    ∃ _ : NumberField (qb T.ι δ.ray), AbelOver T.j.fieldRange (qb T.ι δ.ray) ∧
      (discr (qb T.ι δ.ray)).natAbs ∣
        (discr P.host.E).natAbs ^ (Module.finrank ℚ (qb T.ι δ.ray) / Module.finrank ℚ P.host.E) *
          modulus P ^ Module.finrank ℚ (qb T.ι δ.ray) := by
  have he : P.host.φ₀ = T.ι.comp T.j.toRingHom := RingHom.ext fun x => (T.phi0 x).symm
  obtain ⟨hN, h, hR⟩ := isRayField_qb T.j T.ι (he ▸ δ.isRay)
  refine ⟨hN, abelOver_of_isAbelianGalois _ _ h hR.1, ?_⟩
  let := algThrough T.j _ h
  rw [finrank_div]
  refine RayDiscr.natAbs_discr_dvd hA.rayClassFieldSt _ _ _ (squarefree_modulus P) ?_ hR
  exact (((coprime_discr _ (P.g_cond 0)).mul_left (coprime_discr _ (P.g_cond 1))).mul_left
    (coprime_discr _ P.pde_cond.1)).mul_left (coprime_discr _ P.pde_cond.2)

theorem kPsi_qb {P : Pre} (δ : FieldDat P) (T : Frame P.host) :
    ∃ S : Fin P.R.m → Finset Qb, (∀ j, (S j).card ≤ Nat.log 2 (classNumber P.host.E)) ∧
      (∀ j, ∀ y ∈ S j, ∃ n : ℕ, 0 < n ∧ n ∣ classNumber P.host.E ∧ y ^ n ∈ T.j.fieldRange) ∧
      qb T.ι (⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) =
        T.j.fieldRange ⊔ muFld (classNumber P.host.E) ⊔ IntermediateField.adjoin ℚ (⋃ j, (S j : Set Qb)) := by
  choose S hc hy hK using fun j : ℕ =>
    exists_kPsiField_generators P.R P.host δ.basis (P.R.sigW j).1 (P.R.sigW j).2
  have hE := qb_imField T.ι T.j P.host.φ₀ T.phi0
  have hal : ∀ j, ∀ y ∈ S j, IsAlgebraic ℚ y := fun j y h => by
    obtain ⟨n, hn, -, x, hx⟩ := hy j y h
    exact IsAlgebraic.of_pow hn (hx ▸ (Algebra.IsAlgebraic.isAlgebraic x).algHom P.host.φ₀.toRatAlgHom)
  refine ⟨fun j => (S (j + 1)).preimage T.ι T.ι.injective.injOn, fun j => le_trans ?_ (hc (j + 1)), fun j y h => ?_, ?_⟩
  · exact Finset.card_le_card_of_injOn T.ι (fun y h => Finset.mem_preimage.1 h) T.ι.injective.injOn
  · obtain ⟨n, hn, hd, h⟩ := hy _ _ (Finset.mem_preimage.1 h)
    exact ⟨n, hn, hd, hE ▸ mem_qb.2 (by rwa [map_pow])⟩
  · have hm := P.R.two_le_m
    have : Algebra.IsAlgebraic ℚ (imField P.host.φ₀) :=
      (AlgEquiv.ofInjectiveField P.host.φ₀.toRatAlgHom).isAlgebraic
    have h0 := classNumber_ne_zero P.host.E
    have : Algebra.IsAlgebraic ℚ (cycField (classNumber P.host.E)) :=
      IntermediateField.isAlgebraic_adjoin_simple (IsIntegral.of_pow (Nat.pos_of_ne_zero h0) (by
        rw [(Complex.isPrimitiveRoot_exp _ h0).pow_eq_one]; exact isIntegral_one))
    refine qb_eq_of_map _ ?_
    rw [← hE, ← qb_cycField T.ι h0, IntermediateField.map_sup, IntermediateField.map_sup, map_qb, map_qb,
      IntermediateField.adjoin_map, Set.image_iUnion]
    have hi : ∀ j, T.ι.toRatAlgHom '' ((S j).preimage T.ι T.ι.injective.injOn : Set Qb) = S j := fun j => by
      rw [Finset.coe_preimage]
      exact Set.image_preimage_eq_of_subset fun z hz => exists_eq_of_isAlgebraic _ (hal j z hz)
    simp only [hi, FieldDat.KPsi, hK]
    refine le_antisymm (sup_le ?_ (IntermediateField.adjoin_le_iff.2 (Set.iUnion_subset fun j => ?_)))
      (iSup₂_le fun j hj => sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _)
    · exact le_iSup₂_of_le 1 ⟨le_rfl, by omega⟩ le_sup_left
    · exact IntermediateField.adjoin_le_iff.1 (le_iSup₂_of_le (j + 1) ⟨by omega, j.2⟩ le_sup_right)
    · refine Set.subset_iUnion_of_subset ⟨j - 1, by have := hj.1; have := hj.2; omega⟩ ?_
      rw [Nat.sub_add_cancel hj.1]

theorem exists_twelfth_root (M : Fld) [NumberField M] {y : Qb} (hy : y ∈ M) :
    ∃ h : y ^ 12 ∈ M, (∃ I : FractionalIdeal (𝓞 M)⁰ M,
      FractionalIdeal.spanSingleton (𝓞 M)⁰ (⟨y ^ 12, h⟩ : M) = I ^ 12) ∧ M = M ⊔ IntermediateField.adjoin ℚ {y} :=
  ⟨pow_mem hy 12, ⟨FractionalIdeal.spanSingleton _ ⟨y, hy⟩, by rw [FractionalIdeal.spanSingleton_pow]; rfl⟩,
    (sup_eq_left.2 (IntermediateField.adjoin_simple_le_iff.2 hy)).symm⟩

theorem exists_pieces : GlobalArtinReciprocity → WeberRayFieldSt → ∀ (X : Stages) (f : Fr X.B.toPre)
    (δ : FieldDat X.B.toPre) (T : HostTied X.toD7), ∃ P : KsPieces X.toD7 T,
      P.HK = qb T.fr.ι (hilbertField X.B.host.d δ.jField) ∧ P.rcf = qb T.fr.ι δ.ray ∧ P.M = qb T.fr.ι δ.M ∧
        P.MDel = qb T.fr.ι δ.M' ∧ P.KPs = qb T.fr.ι (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j) := by
  intro hA hW X _ δ T
  have h16 : X.B.host.d % 16 = 7 := X.B.host.hyp.2.2.2.1
  obtain ⟨hH, hH', hilb⟩ := isHilbertCF_qb hA hW T.fr.ι X.B.host.hyp.2.1 (by omega) (by omega) δ.good
  obtain ⟨hR, hab, hcond⟩ := ray_qb hA δ T.fr
  obtain ⟨hF, hEll, -, -, -, -, hred⟩ := δ.good
  obtain ⟨hMf, hdeg⟩ := TorsionDegree.finrank_torsionField_le X.B.host.d δ.jField δ.curve
  have hM : NumberField δ.M := @NumberField.of_module_finite ℚ _ _ _ _ _ hMf
  have hMq := numberField_qb T.fr.ι δ.M
  have hMM : δ.M' = δ.M := DiscRoot.discField_eq_torsionField _ _ _
  obtain ⟨hK, hKram⟩ := KPsiRam.prime_dvd_discr_iSup_kPsi _ δ
  have hKq := numberField_qb T.fr.ι (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j :)
  have hHq := numberField_qb T.fr.ι (hilbertField X.B.host.d δ.jField)
  have hram : ∀ p : ℕ, p.Prime → p ∣ (discr (qb T.fr.ι δ.M)).natAbs → p ∣ 6 * X.B.host.d := fun p hp h => by
    rw [discr_qb] at h
    have : NumberField (torsionField X.B.host.d δ.curve) := hM
    refine (TorsionRam.dvd_discr_torsionField _ _ δ.curve hred p hp h).elim id fun h => ?_
    rw [← discr_qb T.fr.ι, show (discr (qb T.fr.ι (hilbertField X.B.host.d δ.jField))).natAbs = _ from hilb.2.1] at h
    exact (hp.dvd_of_dvd_pow h).mul_left 6
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (δ.curve.Δ : ℂ) (show 0 < 12 by norm_num)
  have hzM : z ∈ δ.M := hMM ▸ ((discField_le_iff _ δ.curve).1 le_rfl).2.2.2 z hz
  have hz0 : z ≠ 0 := fun h => δ.curve.isUnit_Δ.ne_zero (Subtype.ext (by rw [← hz, h]; norm_num))
  let y := (qbEquiv T.fr.ι δ.M).symm ⟨z, hzM⟩
  have hy0 : (y : Qb) ≠ 0 := fun h => hz0 (congrArg Subtype.val
    ((map_eq_zero (qbEquiv T.fr.ι δ.M).symm).1 (Subtype.ext h)))
  obtain ⟨hy, hI, hgen⟩ := exists_twelfth_root _ y.2
  obtain ⟨S, hS1, hS2, hS3⟩ := kPsi_qb δ T.fr
  exact ⟨{
    HK := qb T.fr.ι (hilbertField X.B.host.d δ.jField)
    rcf := qb T.fr.ι δ.ray
    M := qb T.fr.ι δ.M
    MDel := qb T.fr.ι δ.M
    KPs := qb T.fr.ι (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j)
    HK_hilb := hilb
    E_le_rcf := hab.1
    rcf_abel := hab
    rcf_cond := hcond
    HK_le_M := qb_mono _ (hilbertField_le_torsionField _ _)
    M_deg := by rw [finrank_qb, finrank_qb]; exact hdeg
    M_ram := hram
    MDel_gen := ⟨y, hy, hy0, hI, hgen⟩
    MDel_ram := hram
    KPs_gen := ⟨S, hS1, hS2, hS3⟩
    KPs_ram := fun p hp h => hKram p hp (by rwa [discr_qb] at h)
    M_le_MDel := le_rfl
    E_le_KPs := hS3 ▸ le_sup_left.trans le_sup_left }, rfl, rfl, rfl, by rw [hMM], rfl⟩

end GlobalTheory.SmallFieldPieces

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmallFieldClassFieldPiecesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host Formalism.L2.Rows GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smallField_classFieldPieces : GlobalArtinReciprocity → WeberRayFieldSt → ∀ (X : Stages) (f : Fr X.B.toPre) (δ : FieldDat X.B.toPre) (T : HostTied X.toD7), ∃ P : KsPieces X.toD7 T, P.HK = qb T.fr.ι (hilbertField X.B.host.d δ.jField) ∧ P.rcf = qb T.fr.ι δ.ray ∧ P.M = qb T.fr.ι δ.M ∧ P.MDel = qb T.fr.ι δ.M' ∧ P.KPs = qb T.fr.ι (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j) := by
  first | exact @GlobalTheory.SmallFieldPieces.exists_pieces | exact GlobalTheory.SmallFieldPieces.exists_pieces | (intros; apply GlobalTheory.SmallFieldPieces.exists_pieces <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host Formalism.L2.Rows GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain

namespace GlobalTheory.Mem.CyclotomicFieldContainment

theorem natCard_codeWordStages_finiteGroup_eq (X : Stages) : Nat.card (G0g X.toD7.nd) = X.B.restRowsFiniteGroupCard := by
  have : ∀ k, NeZero (X.toD7.host.g k) := fun k => ⟨(X.toD7.host.g_prime k).ne_zero⟩
  rw [Nat.card_pi, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  change ∏ _y : X.toD7.nd.PlG k, Nat.card (GL (Fin X.toD7.R.r) (ZMod (X.toD7.host.g k))) = _
  rw [Finset.prod_const, Finset.card_univ, X.toD7.nd.card_PlG k]
  rfl

theorem rootsField_le_iff (X : Stages) {N : IntermediateField ℚ ℂ} :
    rootsField X.B.toPre ≤ N ↔ ∀ n ∈ rootOrders X.toD7, cycField n ≤ N := by
  simp only [rootsField, rootOrders, natCard_codeWordStages_finiteGroup_eq, sup_le_iff, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, and_assoc]
  rfl

theorem rootOrders_ne_zero (X : Stages) : ∀ n ∈ rootOrders X.toD7, n ≠ 0 := by
  have hg : ∀ k, X.toD7.host.g k * (X.toD7.host.g k - 1) ≠ 0 := fun k => by
    have hp := X.toD7.host.g_prime k
    exact mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  simp only [rootOrders, natCard_codeWordStages_finiteGroup_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨X.B.restRowsFiniteGroupCard_pos.ne', hg 0, hg 1, by norm_num, by norm_num⟩

variable (ι : Qb →+* ℂ)

theorem le_map_of_qb_le {A : IntermediateField ℚ ℂ} {Y : Fld} (hA : ∀ z ∈ A, ∃ x, ι x = z) (h : qb ι A ≤ Y) :
    A ≤ Y.map ι.toRatAlgHom := fun z hz => by
  obtain ⟨x, rfl⟩ := hA z hz
  exact ⟨x, h (mem_qb.2 hz), rfl⟩

theorem muFld_le_qb {n : ℕ} (hn : n ≠ 0) {N : IntermediateField ℚ ℂ} (h : cycField n ≤ N) : muFld n ≤ qb ι N := by
  rw [muFld, IntermediateField.adjoin_le_iff]
  intro x hx
  refine mem_qb.2 (h (mem_cycField hn ?_))
  rw [← map_pow, show x ^ n = 1 from hx, map_one]

theorem cycField_le_map {n : ℕ} (hn : n ≠ 0) {Y : Fld} (hY : muFld n ≤ Y) (hz : ∃ x, ι x = rootOne n) :
    cycField n ≤ Y.map ι.toRatAlgHom := by
  obtain ⟨x, hx⟩ := hz
  refine cycField_le_iff.2 ⟨x, hY (IntermediateField.subset_adjoin ℚ _ ?_), hx⟩
  apply ι.injective
  rw [map_pow, hx, map_one]
  exact (Complex.isPrimitiveRoot_exp n hn).pow_eq_one

variable {E : Type} [Field E] [NumberField E]

theorem valsOf_subset_qb {χ : HChar E} {s : ℝ} {N : IntermediateField ℚ ℂ} (h : valueField χ s ≤ N) :
    valsOf ι s χ ⊆ qb ι N := fun _ ⟨v, hv, e⟩ =>
  mem_qb.2 (h (IntermediateField.subset_adjoin ℚ _ ⟨v, hv, e⟩))

theorem valueField_le_map {χ : HChar E} {s : ℝ} {Y : Fld} (hY : valsOf ι s χ ⊆ Y)
    (hz : ∀ z ∈ valueField χ s, ∃ x, ι x = z) : valueField χ s ≤ Y.map ι.toRatAlgHom := by
  rw [valueField, IntermediateField.adjoin_le_iff]
  rintro z ⟨v, hv, rfl⟩
  obtain ⟨x, hx⟩ := hz _ (IntermediateField.subset_adjoin ℚ _ ⟨v, hv, rfl⟩)
  exact ⟨x, hY ⟨v, hv, hx⟩, hx⟩

theorem ksQ_eq (X : Stages) (f : Fr X.B.toPre) (δ : FieldDat X.B.toPre) (hx : X.B.KsExact δ f) (T : HostTied X.toD7)
    (P : KsPieces X.toD7 T) (hR : P.rcf = qb T.fr.ι δ.ray) (hM : P.M = qb T.fr.ι δ.M) (hD : P.MDel = qb T.fr.ι δ.M')
    (hK : P.KPs = qb T.fr.ι (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j)) :
    KsQ X.toD7 T (Fr.at X f) P = qb T.fr.ι (listField δ f) := by
  have hran : ∀ z ∈ listField δ f, ∃ x, T.fr.ι x = z := by
    intro z hz
    have hz' : z ∈ X.B.KsC := by rw [show X.B.KsC = listField δ f from hx]; exact hz
    obtain ⟨x, -, rfl⟩ := hz'
    exact ⟨T.jLL x, T.embLL x⟩
  have hle : ∀ {A : IntermediateField ℚ ℂ}, A ≤ listField δ f → ∀ z ∈ A, ∃ x, T.fr.ι x = z :=
    fun h z hz => hran z (h hz)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (listField_le_iff δ f).1 le_rfl
  have hKP : (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j) ≤ listField δ f :=
    iSup₂_le fun j hj => h6 j hj.1 hj.2
  have hroots := (rootsField_le_iff X).1 h4
  have hne := rootOrders_ne_zero X
  simp only [charField, sup_le_iff, iSup_le_iff] at h5
  obtain ⟨⟨⟨⟨hmu, heta⟩, hdel⟩, hdel'⟩, hom⟩ := h5
  apply le_antisymm
  · have hM' : P.M ≤ qb T.fr.ι (listField δ f) := by
      rw [hM]
      exact fun x hx => mem_qb.2 (h2 (δ.M_le_M' hx))
    simp only [KsQ, sup_le_iff, iSup_le_iff]
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, hM'⟩, ?_⟩, ?_⟩
    · rintro _ ⟨a, rfl⟩
      exact mem_qb.2 (h1 ⟨a, (T.fr.phi0 a).symm⟩)
    · exact fun n hn => muFld_le_qb _ (hne n hn) (hroots n hn)
    · rw [valsFld, IntermediateField.adjoin_le_iff]
      rintro x (((hx | hx) | hx) | hx)
      · obtain ⟨j, hx⟩ := Set.mem_iUnion.1 hx
        exact valsOf_subset_qb _ (hmu j) hx
      · exact valsOf_subset_qb _ heta hx
      · exact valsOf_subset_qb _ hdel hx
      · exact valsOf_subset_qb _ hdel' hx
    · rw [hR]; exact fun x hx => mem_qb.2 (h3 hx)
    · rw [hD]; exact fun x hx => mem_qb.2 (h2 hx)
    · rw [hK]; exact fun x hx => mem_qb.2 (hKP hx)
  · obtain ⟨Y, hYe⟩ : ∃ Y, Y = KsQ X.toD7 T (Fr.at X f) P := ⟨_, rfl⟩
    have hY : KsQ X.toD7 T (Fr.at X f) P ≤ Y := hYe.ge
    rw [← hYe]
    simp only [KsQ, sup_le_iff, iSup_le_iff] at hY
    obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, -⟩, a6⟩, a7⟩ := hY
    have ha3 : ∀ {A : Set Qb}, A ⊆ valsFld X.toD7 T (Fr.at X f) → A ⊆ Y := fun h _ hx => a3 (h hx)
    have hv : (⋃ j, valsOf T.fr.ι 0 ((Fr.at X f).mu0 j)) ∪ valsOf T.fr.ι (1 / 2) (Fr.at X f).eta ∪
        valsOf T.fr.ι 0 (Fr.at X f).del ∪ valsOf T.fr.ι 0 (Fr.at X f).del' ⊆ Y :=
      ha3 (IntermediateField.subset_adjoin ℚ _)
    have hr : rootsField X.B.toPre ≤ Y.map T.fr.ι.toRatAlgHom := (rootsField_le_iff X).2 fun n hn =>
      cycField_le_map _ (hne n hn) (a2 n hn) (hran _ (hroots n hn (IntermediateField.mem_adjoin_simple_self ℚ _)))
    have hmap : listField δ f ≤ Y.map T.fr.ι.toRatAlgHom := by
      refine (listField_le_iff δ f).2 ⟨?_, ?_, ?_, hr, ?_, fun j hj hj' => ?_⟩
      · rintro _ ⟨a, rfl⟩
        exact ⟨T.fr.j a, a1 ⟨a, rfl⟩, T.fr.phi0 a⟩
      · exact le_map_of_qb_le _ (hle h2) (hD ▸ a6)
      · exact le_map_of_qb_le _ (hle h3) (hR ▸ a4)
      · simp only [charField, sup_le_iff, iSup_le_iff]
        refine ⟨⟨⟨⟨fun j => ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
        · exact valueField_le_map _ (fun x hx => hv (Or.inl (Or.inl (Or.inl (Set.mem_iUnion.2 ⟨j, hx⟩))))) (hle (hmu j))
        · exact valueField_le_map _ (fun x hx => hv (Or.inl (Or.inl (Or.inr hx)))) (hle heta)
        · exact valueField_le_map _ (fun x hx => hv (Or.inl (Or.inr hx))) (hle hdel)
        · exact valueField_le_map _ (fun x hx => hv (Or.inr hx)) (hle hdel')
        · rw [IntermediateField.adjoin_le_iff]
          rintro _ ⟨k, a, rfl⟩
          exact hr (om_mem_rootsField f k a)
      · refine le_map_of_qb_le _ (hle (h6 j hj hj')) fun x hx => a7 ?_
        rw [hK]
        exact mem_qb.2 ((le_iSup₂_of_le j ⟨hj, hj'⟩ le_rfl : δ.KPsi j ≤ ⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j) hx)
    intro x hx
    obtain ⟨y, hy, e⟩ := hmap hx
    have hyx : y = x := T.fr.ι.injective e
    exact hyx ▸ hy

theorem oTied_of_ksExact : GlobalArtinReciprocity → WeberRayFieldSt → ∀ (X : Stages) (f : Fr X.B.toPre)
    (δ : FieldDat X.B.toPre), X.B.KsExact δ f → ∀ T : HostTied X.toD7, ∃ O : OTied X.toD7 T (Fr.at X f),
      O.pieces.rcf = qb T.fr.ι δ.ray ∧ O.pieces.MDel = qb T.fr.ι δ.M' := by
  intro hA hW X f δ hx T
  obtain ⟨P, -, hR, hM, hD, hK⟩ := GlobalTheory.T.exists_smallField_classFieldPieces hA hW X f δ T
  have hq := ksQ_eq X f δ hx T P hR hM hD hK
  refine ⟨⟨P, X.B.OtoLL_injective, fun x => ?_⟩, hR, hD⟩
  rw [hq]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨mem_qb.2 ?_, (X.toD7.O_int y).map T.jLL.toIntAlgHom⟩
    rw [T.embLL, ← show X.B.KsC = listField δ f from hx]
    exact ⟨_, (algebraMap (𝓞 X.B.Ks) X.B.Ks y).2, rfl⟩
  · rintro ⟨hxq, hi⟩
    have hz : T.fr.ι x ∈ X.B.KsC := by
      rw [show X.B.KsC = listField δ f from hx]
      exact hxq
    obtain ⟨w, hw, e⟩ := hz
    have hwx : T.jLL w = x := T.fr.ι.injective ((T.embLL w).trans e)
    subst hwx
    have hwi : IsIntegral ℤ w := (isIntegral_algHom_iff T.jLL.toIntAlgHom T.jLL.injective).1 hi
    obtain ⟨y, hy⟩ := X.B.O_full w hw hwi
    exact ⟨y, congrArg T.jLL hy⟩

end GlobalTheory.Mem.CyclotomicFieldContainment

end
