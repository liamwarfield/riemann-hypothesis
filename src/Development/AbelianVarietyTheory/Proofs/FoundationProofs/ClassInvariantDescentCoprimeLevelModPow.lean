module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueGenericFibreDualNumberPointOfModel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTranslatesLevelAndScalarMod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomToKernelSqCentralExtensionSlTwoZMod
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2CentralExtensionCommutatorSq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2CentralExtensionCommutatorSq
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.SLTwoCentral

noncomputable def red (p a : ℕ) :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ (a + 1))) →*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
  Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero a)) (ZMod p))

end GlobalTheory.SLTwoCentral

namespace GlobalTheory

private theorem pow_card_div_orderOf_eq_one_of_mem_ker_commutator {E G : Type} [Group E] [Group G]
    [Finite G] (π : E →* G) (hπ : Function.Surjective π)
    (hK : π.ker ≤ Subgroup.center E) (g : G) (x : E) (hx : x ∈ π.ker) (hc : x ∈ commutator E) :
    x ^ (Nat.card G / orderOf g) = 1 := by
  set A := (Subgroup.zpowers g).comap π with hAdef
  obtain ⟨e, he⟩ := hπ g
  have key : ∀ a ∈ A, ∃ i : ℤ, ∃ k ∈ π.ker, a = e ^ i * k := by
    intro a ha
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp ha)
    refine ⟨i, (e ^ i)⁻¹ * a, ?_, by group⟩
    simp [MonoidHom.mem_ker, map_zpow, he, hi]
  have hA : ∀ a b : A, a * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨i, k, hk, rfl⟩ := key a ha
    obtain ⟨j, m, hm, rfl⟩ := key b hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hkc := Subgroup.mem_center_iff.mp (hK hk)
    have hmc := Subgroup.mem_center_iff.mp (hK hm)
    calc e ^ i * k * (e ^ j * m) = e ^ i * e ^ j * (k * m) := by
          rw [mul_assoc, mul_assoc, ← mul_assoc k, ← hkc (e ^ j), mul_assoc]
      _ = e ^ j * e ^ i * (m * k) := by
          rw [← _root_.zpow_add, ← _root_.zpow_add, add_comm, (hmc k).symm]
      _ = e ^ j * m * (e ^ i * k) := by
          rw [mul_assoc, mul_assoc, ← mul_assoc m, ← hmc (e ^ i), mul_assoc]
  have hidx : A.index = Nat.card G / orderOf g := by
    rw [hAdef, Subgroup.index_comap_of_surjective _ hπ, ← Nat.card_zpowers,
      ← (Subgroup.zpowers g).card_mul_index, Nat.mul_div_cancel_left _ Nat.card_pos]
  haveI : A.FiniteIndex := ⟨by
    rw [hAdef, Subgroup.index_comap_of_surjective _ hπ]; exact Subgroup.index_ne_zero_of_finite⟩
  rw [← hidx]
  letI : CommGroup A := { (inferInstance : Group A) with mul_comm := hA }
  have h1 := Abelianization.commutator_subset_ker ((MonoidHom.id A).transfer (H := A)) hc
  rw [MonoidHom.mem_ker, MonoidHom.transfer_eq_pow (MonoidHom.id A) x] at h1
  · simpa using congrArg Subtype.val h1
  · intro k g₀ _
    have : x ^ k ∈ Subgroup.center E := Subgroup.pow_mem _ (hK hx) k
    rw [mul_assoc, (Subgroup.mem_center_iff.mp this g₀).symm, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem exists_card_ker_red_eq_prime_pow (p b : ℕ) [Fact p.Prime] :
    ∃ k, Nat.card (_root_.GlobalTheory.SLTwoCentral.red p b).ker = p ^ k := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdiv : ∀ z : ZMod (p ^ (b + 1)),
      ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero b)) (ZMod p) z = 0 →
        ∃ w : ZMod (p ^ (b + 1)), z = p * w := by
    intro z hz
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at hz
    obtain ⟨w, hw⟩ := (ZMod.natCast_eq_zero_iff _ p).mp hz
    exact ⟨w, by rw [← ZMod.natCast_zmod_val z, hw]; push_cast; ring⟩
  have binom : ∀ (A : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (b + 1)))) (r : ℕ),
      (A + 1) ^ (r + 2) = 1 + A * ((r + 2 : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (b + 1)))) +
        A ^ 2 * ∑ m ∈ Finset.range (r + 1), A ^ m * ((r + 2).choose (m + 2) : Matrix _ _ _) := by
    intro A r
    rw [(Commute.one_right A).add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, Finset.mul_sum]
    have : ∀ m, A ^ (m + 1 + 1) * ((r + 2).choose (m + 1 + 1) : Matrix _ _ _) =
        A ^ 2 * (A ^ m * ((r + 2).choose (m + 2) : Matrix _ _ _)) := by
      intro m; rw [← mul_assoc, ← pow_add]; ring_nf
    simp only [this]
    rw [pow_one, Nat.choose_one_right]
    abel
  obtain ⟨r, hr⟩ : ∃ r, p = r + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have step : ∀ (j : ℕ) (Y : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (b + 1)))), ∃ Y',
      ((p : ZMod (p ^ (b + 1))) ^ (j + 1) • Y + 1) ^ p = (p : ZMod (p ^ (b + 1))) ^ (j + 2) • Y' + 1 := by
    intro j Y
    have e1 : ((p : ZMod (p ^ (b + 1))) ^ (j + 1) • Y + 1) ^ p =
        ((p : ZMod (p ^ (b + 1))) ^ (j + 1) • Y + 1) ^ (r + 2) := by rw [← hr]
    rw [e1, binom]
    set S := ∑ m ∈ Finset.range (r + 1), ((p : ZMod (p ^ (b + 1))) ^ (j + 1) • Y) ^ m *
      ((r + 2).choose (m + 2) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (b + 1))))
    refine ⟨Y + (p : ZMod (p ^ (b + 1))) ^ j • (Y ^ 2 * S), ?_⟩
    rw [← hr, ← Nat.cast_comm, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul (ZMod (p ^ (b + 1))), smul_pow,
      smul_mul_assoc, smul_smul, smul_add, smul_smul]
    have c1 : (p : ZMod (p ^ (b + 1))) * (p : ZMod (p ^ (b + 1))) ^ (j + 1) =
        (p : ZMod (p ^ (b + 1))) ^ (j + 2) := by ring
    have c2 : ((p : ZMod (p ^ (b + 1))) ^ (j + 1)) ^ 2 =
        (p : ZMod (p ^ (b + 1))) ^ (j + 2) * (p : ZMod (p ^ (b + 1))) ^ j := by ring
    rw [c1, c2]
    abel
  have hpow : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ (b + 1))),
      _root_.GlobalTheory.SLTwoCentral.red p b g = 1 → ∀ j, ∃ Y,
        (g : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (b + 1)))) ^ (p ^ j) =
          (p : ZMod (p ^ (b + 1))) ^ (j + 1) • Y + 1 := by
    intro g hg j
    induction j with
    | zero =>
      have hent : ∀ i k, ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero b)) (ZMod p)
          (((g : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (b + 1)))) - 1) i k) = 0 := by
        intro i k
        have h1 := congrFun (congrFun (congrArg Subtype.val hg) i) k
        have h2 := congrFun (congrFun (Matrix.map_one
          (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero b)) (ZMod p)) (map_zero _) (map_one _)) i) k
        rw [Matrix.sub_apply, map_sub, sub_eq_zero]
        exact h1.trans (by rw [Matrix.SpecialLinearGroup.coe_one]; exact h2.symm)
      refine ⟨Matrix.of fun i k => Classical.choose (hdiv _ (hent i k)), ?_⟩
      rw [pow_zero, pow_one, zero_add, pow_one, ← sub_eq_iff_eq_add]
      ext i k
      rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      exact Classical.choose_spec (hdiv _ (hent i k))
    | succ j ih =>
      obtain ⟨Y, hY⟩ := ih
      rw [show p ^ (j + 1) = p ^ j * p from pow_succ p j, pow_mul, hY]
      exact step j Y
  have hP : IsPGroup p (_root_.GlobalTheory.SLTwoCentral.red p b).ker := by
    rintro ⟨g, hg⟩
    refine ⟨b, Subtype.ext (Subtype.ext ?_)⟩
    obtain ⟨Y, hY⟩ := hpow g hg b
    have h0 : (p : ZMod (p ^ (b + 1))) ^ (b + 1) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    change (g : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (b + 1)))) ^ (p ^ b) = 1
    rw [hY, h0, zero_smul, zero_add]
  exact IsPGroup.iff_card.mp hP

private theorem card_sl2_zmod_mul_pred (p : ℕ) [Fact p.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) * (p - 1) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  set D := Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod p)
  have hdet : ∀ g : GL (Fin 2) (ZMod p), D g = 1 ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
    intro g
    rw [← Units.val_eq_one]
    rfl
  have e : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) ≃ D.ker :=
    { toFun := fun A => ⟨Matrix.SpecialLinearGroup.toGL A, (hdet _).mpr A.2⟩
      invFun := fun g => ⟨(g.1 : Matrix (Fin 2) (Fin 2) (ZMod p)), (hdet g.1).mp g.2⟩
      left_inv := fun A => rfl
      right_inv := fun g => Subtype.ext (Units.ext rfl) }
  have hrange : Nat.card D.range = p - 1 := by
    rw [MonoidHom.range_eq_top.mpr Matrix.GeneralLinearGroup.det_surjective, Subgroup.card_top,
      Nat.card_eq_fintype_card, ZMod.card_units]
  rw [Nat.card_congr e, ← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index, Matrix.card_GL_field,
    Fin.prod_univ_two, ZMod.card]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]

private theorem exists_orderOf_eq_succ_sl2_zmod (p : ℕ) [Fact p.Prime] :
    ∃ h : Matrix.SpecialLinearGroup (Fin 2) (ZMod p), orderOf h = p + 1 := by
  have hp := (Fact.out : p.Prime)
  classical
  set K := GaloisField p 2
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Nat.card K = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have hsq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have := hp.one_le
    zify [this, Nat.one_le_pow 2 p hp.pos]
    ring
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hunits : Nat.card Kˣ = p ^ 2 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcard]
  set ζ : K := (γ : K) ^ (p - 1)
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have hζ : orderOf ζ = p + 1 := by
    rw [orderOf_pow_of_dvd hp1, orderOf_units, hγ, hunits, hsq, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp1)]
    rw [orderOf_units, hγ, hunits, hsq]; exact dvd_mul_right _ _
  have hnorm : Algebra.norm (ZMod p) ζ = 1 := by
    apply (algebraMap (ZMod p) K).injective
    rw [FiniteField.algebraMap_norm_eq_pow, hcard, Nat.card_zmod, hsq,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp1), map_one, ← hζ, pow_orderOf_eq_one]
  let b := Module.finBasisOfFinrankEq (ZMod p) K (GaloisField.finrank p (n := 2) (by norm_num))
  have hdet : (Algebra.leftMulMatrix b ζ).det = 1 := by rw [← Algebra.norm_eq_matrix_det, hnorm]
  let h : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) := ⟨Algebra.leftMulMatrix b ζ, hdet⟩
  refine ⟨h, ?_⟩
  rw [← hζ]
  refine orderOf_eq_orderOf_iff.mpr fun n => ?_
  have hval : h ^ n = 1 ↔ (h : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ n = 1 := by
    constructor <;> intro H
    · rw [← Matrix.SpecialLinearGroup.coe_pow, H]; rfl
    · exact Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow, H]; rfl)
  rw [hval]
  change (Algebra.leftMulMatrix b ζ) ^ n = 1 ↔ _
  rw [← map_pow, ← map_one (Algebra.leftMulMatrix b), (Algebra.leftMulMatrix_injective b).eq_iff]

private theorem exists_orderOf_eq_pred_sl2_zmod (p : ℕ) [Fact p.Prime] :
    ∃ h : Matrix.SpecialLinearGroup (Fin 2) (ZMod p), orderOf h = p - 1 := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hunits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hdet : (Matrix.diagonal ![(γ : ZMod p), ((γ⁻¹ : (ZMod p)ˣ) : ZMod p)]).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    exact γ.mul_inv
  let h : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) := ⟨_, hdet⟩
  refine ⟨h, ?_⟩
  rw [← hunits, ← hγ]
  refine orderOf_eq_orderOf_iff.mpr fun n => ?_
  have hval : h ^ n = 1 ↔ (h : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ n = 1 := by
    constructor <;> intro H
    · rw [← Matrix.SpecialLinearGroup.coe_pow, H]; rfl
    · exact Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow, H]; rfl)
  rw [hval]
  change (Matrix.diagonal _) ^ n = 1 ↔ _
  rw [Matrix.diagonal_pow, ← Matrix.diagonal_one, Matrix.diagonal_eq_diagonal_iff, ← Units.val_eq_one,
    Units.val_pow_eq_pow_val]
  constructor
  · intro H; exact H 0
  · intro H i
    have hγn : γ ^ n = 1 := Units.val_eq_one.mp (by rw [Units.val_pow_eq_pow_val]; exact H)
    fin_cases i
    · exact H
    · change ((γ⁻¹ : (ZMod p)ˣ) : ZMod p) ^ n = 1
      rw [← Units.val_pow_eq_pow_val, inv_pow, hγn, inv_one, Units.val_one]

theorem _root_.GlobalTheory.sl2_zmod_central_ext_commutator_sq_eq_one :
    ∀ (l n p a : ℕ), l.Prime → p.Prime → 5 ≤ p → p ≠ l → ∀ (E : Type) [Group E]
      (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ a))), Function.Surjective π →
      π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ (l ^ n) = 1) →
      ∀ x ∈ π.ker, x ∈ commutator E → x ^ 2 = 1 := by
  intro l n p a hl hp hp5 hpl E _ π hπ hK hexp x hx hc
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow := fun g => pow_card_div_orderOf_eq_one_of_mem_ker_commutator π hπ hK g x hx hc
  have hd : orderOf x ∣ l ^ n := orderOf_dvd_of_pow_eq_one (hexp x hx)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).mp hd
  have hcop : ∀ m, Nat.Coprime (orderOf x) (p ^ m) := fun m => by
    rw [hj]; exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hl hp).mpr hpl.symm)
  rcases a with _ | b
  · have h1 := hpow 1
    haveI : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ 0))) :=
      ⟨fun A B => Subtype.ext (funext fun i => funext fun j => Subsingleton.elim _ _)⟩
    rw [orderOf_one, Nat.div_one, Nat.card_of_subsingleton (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ 0))), pow_one] at h1
    rw [h1, one_pow]
  set G := Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ (b + 1)))
  have hred : Function.Surjective (_root_.GlobalTheory.SLTwoCentral.red p b) :=
    _root_.GlobalTheory.specialLinearGroup_map_surjective (ZMod.castHom_surjective _)
  obtain ⟨k, hk⟩ := exists_card_ker_red_eq_prime_pow p b
  have hcardG : Nat.card G = p ^ k * (p * (p + 1) * (p - 1)) := by
    have hSL := card_sl2_zmod_mul_pred p
    have hSL' : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p + 1) * (p - 1) := by
      have h1 : 0 < p - 1 := by omega
      apply Nat.eq_of_mul_eq_mul_right h1
      rw [hSL]
      have := hp.one_le
      zify [this, Nat.one_le_pow 2 p hp.pos, Nat.pow_le_pow_left this 2, Nat.le_self_pow two_ne_zero p]
      ring
    rw [← hk, ← hSL', ← (_root_.GlobalTheory.SLTwoCentral.red p b).ker.card_mul_index, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr hred, Subgroup.card_top]
  have hdiv : ∀ c : ℕ, (∃ h : Matrix.SpecialLinearGroup (Fin 2) (ZMod p), orderOf h = c) →
      orderOf x * c ∣ Nat.card G := by
    rintro c ⟨h, rfl⟩
    obtain ⟨g, rfl⟩ := hred h
    have hxg : orderOf x ∣ Nat.card G / orderOf g := orderOf_dvd_of_pow_eq_one (hpow g)
    have hg : orderOf g ∣ Nat.card G := orderOf_dvd_natCard g
    exact (Nat.mul_dvd_mul_left _ (orderOf_map_dvd _ g)).trans (by rw [mul_comm]; exact Nat.mul_dvd_of_dvd_div hg hxg)
  have hplus := hdiv _ (exists_orderOf_eq_succ_sl2_zmod p)
  have hminus := hdiv _ (exists_orderOf_eq_pred_sl2_zmod p)
  rw [hcardG] at hplus hminus
  have hA : orderOf x ∣ p - 1 := by
    have : orderOf x ∣ p ^ (k + 1) * (p - 1) := by
      apply Nat.dvd_of_mul_dvd_mul_right (show 0 < p + 1 by omega)
      calc orderOf x * (p + 1) ∣ p ^ k * (p * (p + 1) * (p - 1)) := hplus
        _ = p ^ (k + 1) * (p - 1) * (p + 1) := by ring
    exact (hcop (k + 1)).dvd_of_dvd_mul_left this
  have hB : orderOf x ∣ p + 1 := by
    have : orderOf x ∣ p ^ (k + 1) * (p + 1) := by
      apply Nat.dvd_of_mul_dvd_mul_right (show 0 < p - 1 by omega)
      calc orderOf x * (p - 1) ∣ p ^ k * (p * (p + 1) * (p - 1)) := hminus
        _ = p ^ (k + 1) * (p + 1) * (p - 1) := by ring
    exact (hcop (k + 1)).dvd_of_dvd_mul_left this
  have h2 : orderOf x ∣ 2 := by
    have := Nat.dvd_sub hB hA
    rwa [show p + 1 - (p - 1) = 2 by omega] at this
  exact orderOf_dvd_iff_pow_eq_one.mp h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2CentralExtensionCommutatorSqStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_eq_one_of_mem_ker_commutator_central_ext_sl : ∀ (l n p a : ℕ), l.Prime → p.Prime → 5 ≤ p → p ≠ l → ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ a))), Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ (l ^ n) = 1) → ∀ x ∈ π.ker, x ∈ commutator E → x ^ 2 = 1 := by
  first | exact @GlobalTheory.sl2_zmod_central_ext_commutator_sq_eq_one | exact GlobalTheory.sl2_zmod_central_ext_commutator_sq_eq_one | (intros; apply GlobalTheory.sl2_zmod_central_ext_commutator_sq_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomToKernelSqCentralExtensionSlTwoZMod
open scoped MatrixGroups TensorProduct commutatorElement
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.CentralExt

theorem exists_ker_mul_commutator {E G : Type*} [Group E] [Group G] (π : E →* G)
    (hs : Function.Surjective π) (hG : commutator G = ⊤) (e : E) :
    ∃ a ∈ π.ker, ∃ c ∈ commutator E, e = a * c := by
  have h1 : (commutator E).map π = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hs,
      ← commutator_def, hG]
  have h2 : π e ∈ (commutator E).map π := h1 ▸ Subgroup.mem_top _
  obtain ⟨c, hc, hce⟩ := h2
  refine ⟨e * c⁻¹, ?_, c, hc, by simp⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hce, mul_inv_cancel]

theorem exists_hom_sq {E G : Type*} [Group E] [Group G] (π : E →* G)
    (hs : Function.Surjective π) (hG : commutator G = ⊤) (hc : π.ker ≤ Subgroup.center E)
    (h2 : ∀ x ∈ π.ker, x ∈ commutator E → x ^ 2 = 1) :
    ∃ ψ : E →* E, (∀ e, ψ e ∈ π.ker) ∧ ∀ x ∈ π.ker, ψ x = x ^ 2 := by
  choose a ha c hcm hac using exists_ker_mul_commutator π hs hG
  have key : ∀ e, ∀ b ∈ π.ker, ∀ d ∈ commutator E, e = b * d → a e ^ 2 = b ^ 2 := by
    intro e b hb d hd he
    have h3 : b⁻¹ * a e = d * (c e)⁻¹ := by
      have h4 : a e = b * d * (c e)⁻¹ := by
        rw [← he, eq_mul_inv_iff_mul_eq]; exact (hac e).symm
      rw [h4]; group
    have h5 := h2 (b⁻¹ * a e) (mul_mem (inv_mem hb) (ha e))
      (h3 ▸ mul_mem hd (inv_mem (hcm e)))
    have hcomm : Commute b⁻¹ (a e) :=
      ((Subgroup.mem_center_iff.1 (hc (ha e))) b⁻¹)
    rw [hcomm.mul_pow, inv_pow, inv_mul_eq_one] at h5
    exact h5.symm
  refine ⟨MonoidHom.mk' (fun e => a e ^ 2) ?_, fun e => (by exact pow_mem (ha e) 2), fun x hx => ?_⟩
  · intro e f
    have hcomm : Commute (a e) (a f) := ((Subgroup.mem_center_iff.1 (hc (ha f))) (a e))
    rw [← hcomm.mul_pow]
    refine key (e * f) _ (mul_mem (ha e) (ha f)) (c e * c f) (mul_mem (hcm e) (hcm f)) ?_
    have h6 : c e * a f = a f * c e := ((Subgroup.mem_center_iff.1 (hc (ha f))) (c e))
    calc e * f = a e * c e * (a f * c f) := by rw [← hac e, ← hac f]
      _ = a e * (c e * a f) * c f := by group
      _ = a e * a f * (c e * c f) := by rw [h6]; group
  · exact key x x hx 1 (one_mem _) (mul_one x).symm

theorem commutator_sl2_zmod (m : ℕ) (hm : Nat.Coprime m 6) :
    commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod m)) = ⊤ := by
  have h2 : Nat.Coprime 2 m := (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) hm).symm
  have h3 : Nat.Coprime 3 m := (Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) hm).symm
  obtain ⟨u, hu⟩ : ∃ u : ZMod m, 2 * u = 1 :=
    ⟨((ZMod.unitOfCoprime 2 h2)⁻¹ : (ZMod m)ˣ), by
      simpa using (ZMod.unitOfCoprime 2 h2).mul_inv⟩
  obtain ⟨v, hv⟩ : ∃ v : ZMod m, 3 * v = 1 :=
    ⟨((ZMod.unitOfCoprime 3 h3)⁻¹ : (ZMod m)ˣ), by
      simpa using (ZMod.unitOfCoprime 3 h3).mul_inv⟩
  set ρ : SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod m) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m)) with hρ
  have hs : Function.Surjective ρ := GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) m
  let d : Matrix.SpecialLinearGroup (Fin 2) (ZMod m) :=
    ⟨!![2, 0; 0, u], by rw [Matrix.det_fin_two_of]; linear_combination hu⟩
  let t : Matrix.SpecialLinearGroup (Fin 2) (ZMod m) :=
    ⟨!![1, v; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩
  have hT : ρ ModularGroup.T ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod m)) := by
    have : ρ ModularGroup.T = ⁅d, t⁆ := by
      have h : ρ ModularGroup.T * t * d = d * t := by
        have hT' : (ρ ModularGroup.T).1 = !![1, 1; 0, 1] := by
          ext i j
          change ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j : ZMod m) = _
          fin_cases i <;> fin_cases j <;> simp
        apply Subtype.ext
        change (ρ ModularGroup.T).1 * !![1, v; 0, 1] * !![2, 0; 0, u] =
          !![2, 0; 0, u] * !![1, v; 0, 1]
        rw [hT', Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
        have e : (1 * 1 + 1 * 0) * 0 + (1 * v + 1 * 1) * u = 2 * v + 0 * 1 := by
          linear_combination (-u) * hv + (2 * v) * hu
        rw [e]
        simp
      rw [commutatorElement_def, ← h]; group
    rw [this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hS : ρ ModularGroup.S ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod m)) := by
    have h : ModularGroup.S = ModularGroup.T⁻¹ *
        (ModularGroup.S⁻¹ * ModularGroup.T⁻¹ * ModularGroup.S⁻¹⁻¹) * ModularGroup.T⁻¹ := by
      decide
    rw [h]
    simp only [map_mul, map_inv]
    refine mul_mem (mul_mem (inv_mem hT) ?_) (inv_mem hT)
    exact Subgroup.Normal.conj_mem _ (inv_mem hT) _
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective ρ hs, ← _root_.SpecialLinearGroup.SL2Z_generators,
    MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with rfl | rfl
  · exact hS
  · exact hT

theorem slTwo_zmod_mul_crt_exists_and_eq_one : ∀ a b : ℕ, Nat.Coprime a b → (∀ (g₁ : Matrix.SpecialLinearGroup (Fin 2) (ZMod a)) (g₂ : Matrix.SpecialLinearGroup (Fin 2) (ZMod b)), ∃ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (a * b)), Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_right a b) (ZMod a)) g = g₁ ∧ Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_left b a) (ZMod b)) g = g₂) ∧ (∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (a * b)), Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_right a b) (ZMod a)) g = 1 → Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_left b a) (ZMod b)) g = 1 → g = 1) := by
  intro a b h
  have h1 : ∀ x, ((ZMod.chineseRemainder h) x).1 = ZMod.castHom (dvd_mul_right a b) (ZMod a) x := by
    intro x
    exact RingHom.congr_fun (Subsingleton.elim ((RingHom.fst _ _).comp (ZMod.chineseRemainder h).toRingHom) (ZMod.castHom (dvd_mul_right a b) (ZMod a))) x
  have h2 : ∀ x, ((ZMod.chineseRemainder h) x).2 = ZMod.castHom (dvd_mul_left b a) (ZMod b) x := by
    intro x
    exact RingHom.congr_fun (Subsingleton.elim ((RingHom.snd _ _).comp (ZMod.chineseRemainder h).toRingHom) (ZMod.castHom (dvd_mul_left b a) (ZMod b))) x
  constructor
  · intro g₁ g₂
    let M : Matrix.SpecialLinearGroup (Fin 2) (ZMod a × ZMod b) :=
      ⟨Matrix.of fun i j => (g₁ i j, g₂ i j), by
        have e1 := g₁.det_coe
        have e2 := g₂.det_coe
        rw [Matrix.det_fin_two] at e1 e2 ⊢
        exact Prod.ext e1 e2⟩
    refine ⟨Matrix.SpecialLinearGroup.map (ZMod.chineseRemainder h).symm.toRingHom M, ?_, ?_⟩
    · ext i j
      change ZMod.castHom (dvd_mul_right a b) (ZMod a) ((ZMod.chineseRemainder h).symm (g₁ i j, g₂ i j)) = _
      rw [← h1, RingEquiv.apply_symm_apply]
    · ext i j
      change ZMod.castHom (dvd_mul_left b a) (ZMod b) ((ZMod.chineseRemainder h).symm (g₁ i j, g₂ i j)) = _
      rw [← h2, RingEquiv.apply_symm_apply]
  · intro g e1 e2
    ext i j
    apply (ZMod.chineseRemainder h).injective
    have f1 : ZMod.castHom (dvd_mul_right a b) (ZMod a) (g i j) = (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod a)) i j := by
      rw [← e1]; rfl
    have f2 : ZMod.castHom (dvd_mul_left b a) (ZMod b) (g i j) = (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod b)) i j := by
      rw [← e2]; rfl
    refine Prod.ext ?_ ?_
    · rw [h1, h1, f1]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · rw [h2, h2, f2]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem glue : ∀ (k : ℕ) (G G₁ G₂ : Type) [Group G] [Group G₁] [Group G₂] (ρ₁ : G →* G₁) (ρ₂ : G →* G₂), (∀ g₁ g₂, ∃ g, ρ₁ g = g₁ ∧ ρ₂ g = g₂) → (∀ g, ρ₁ g = 1 → ρ₂ g = 1 → g = 1) → commutator G₁ = ⊤ → (∀ (E : Type) [Group E] (π : E →* G₁), Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ k = 1) → ∀ x ∈ π.ker, x ∈ commutator E → x ^ 2 = 1) → (∀ (E : Type) [Group E] (π : E →* G₂), Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ k = 1) → ∀ x ∈ π.ker, x ∈ commutator E → x ^ 2 = 1) → (∀ (E : Type) [Group E] (π : E →* G), Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ k = 1) → ∀ x ∈ π.ker, x ∈ commutator E → x ^ 2 = 1) := by
  intro k G G₁ G₂ _ _ _ ρ₁ ρ₂ hsur hinj hperf Q₁ Q₂ E _ π hs hc hk x hx hxc
  let E₁ : Subgroup E := (ρ₂.comp π).ker
  let E₂ : Subgroup E := (ρ₁.comp π).ker
  let π₁ : E₁ →* G₁ := (ρ₁.comp π).comp E₁.subtype
  let π₂ : E₂ →* G₂ := (ρ₂.comp π).comp E₂.subtype
  have s₁ : Function.Surjective π₁ := by
    intro g
    obtain ⟨g', h1, h2⟩ := hsur g 1
    obtain ⟨e, rfl⟩ := hs g'
    exact ⟨⟨e, h2⟩, h1⟩
  have s₂ : Function.Surjective π₂ := by
    intro g
    obtain ⟨g', h1, h2⟩ := hsur 1 g
    obtain ⟨e, rfl⟩ := hs g'
    exact ⟨⟨e, h1⟩, h2⟩
  have k₁ : ∀ y ∈ π₁.ker, (y : E) ∈ π.ker := fun y hy => hinj _ hy y.2
  have k₂ : ∀ y ∈ π₂.ker, (y : E) ∈ π.ker := fun y hy => hinj _ y.2 hy
  have q₁ := Q₁ E₁ π₁ s₁ (fun y hy => Subgroup.mem_center_iff.2 fun z =>
      Subtype.ext (Subgroup.mem_center_iff.1 (hc (k₁ y hy)) z))
    (fun y hy => Subtype.ext (hk y (k₁ y hy)))
  have q₂ := Q₂ E₂ π₂ s₂ (fun y hy => Subgroup.mem_center_iff.2 fun z =>
      Subtype.ext (Subgroup.mem_center_iff.1 (hc (k₂ y hy)) z))
    (fun y hy => Subtype.ext (hk y (k₂ y hy)))
  have cen : ∀ (y : E₁) (z : E₂), ⁅(y : E), (z : E)⁆ ∈ Subgroup.center E := by
    intro y z
    apply hc
    have hy : ρ₂ (π y) = 1 := y.2
    have hz : ρ₁ (π z) = 1 := z.2
    apply hinj
    · simp [map_commutatorElement, hz]
    · simp [map_commutatorElement, hy]
  have comm : ∀ (y : E₁) (z : E₂), (y : E) * z = z * y := by
    intro y z
    let φ : E₁ →* Subgroup.center E := MonoidHom.mk' (fun y => ⟨_, cen y z⟩) (by
      intro y y'
      apply Subtype.ext
      have h := Subgroup.mem_center_iff.1 (cen y' z) y
      have h' := Subgroup.mem_center_iff.1 (cen y' z) ⁅(y : E), (z : E)⁆
      change ⁅(y : E) * y', (z : E)⁆ = ⁅(y : E), (z : E)⁆ * ⁅(y' : E), (z : E)⁆
      rw [h']
      calc ⁅(y : E) * y', (z : E)⁆ = (y * ⁅(y' : E), (z : E)⁆) * (z * (y : E)⁻¹ * (z : E)⁻¹) := by
            simp only [commutatorElement_def]; group
        _ = _ := by rw [h]; simp only [commutatorElement_def]; group)
    obtain ⟨a, ha, c, hc', rfl⟩ := exists_ker_mul_commutator π₁ s₁ hperf y
    have h1 : φ c = 1 := by
      have h0 : (commutator E₁).map φ = ⊥ := by
        rw [commutator_def, Subgroup.map_commutator,
          Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro e _
        exact Subgroup.mem_centralizer_iff.2 fun g _ =>
          Subtype.ext (Subgroup.mem_center_iff.1 e.2 g)
      exact (Subgroup.map_eq_bot_iff _).1 h0 hc'
    have h2 : (c : E) * z = z * c := commutatorElement_eq_one_iff_mul_comm.1 (congrArg Subtype.val h1)
    have h3 : (z : E) * a = a * z := Subgroup.mem_center_iff.1 (hc (k₁ a ha)) z
    change (a : E) * c * z = z * (a * c)
    rw [mul_assoc, h2, ← mul_assoc, ← h3, mul_assoc]
  let μ : E₁ × E₂ →* E := MonoidHom.noncommCoprod E₁.subtype E₂.subtype comm
  have sμ : Function.Surjective μ := by
    intro e
    obtain ⟨y, hy⟩ := s₁ (ρ₁ (π e))
    have hy' : ρ₁ (π y) = ρ₁ (π e) := hy
    refine ⟨(y, ⟨(y : E)⁻¹ * e, ?_⟩), ?_⟩
    · change ρ₁ (π _) = 1
      simp [hy']
    · change (y : E) * ((y : E)⁻¹ * e) = e
      group
  have h1 : (commutator (E₁ × E₂)).map μ = commutator E := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective μ sμ,
      ← commutator_def]
  rw [← h1] at hxc
  obtain ⟨⟨y, z⟩, hyz, rfl⟩ := hxc
  have hy : y ∈ commutator E₁ := by
    have : (commutator (E₁ × E₂)).map (MonoidHom.fst E₁ E₂) ≤ commutator E₁ := by
      rw [commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact this ⟨_, hyz, rfl⟩
  have hz : z ∈ commutator E₂ := by
    have : (commutator (E₁ × E₂)).map (MonoidHom.snd E₁ E₂) ≤ commutator E₂ := by
      rw [commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact this ⟨_, hyz, rfl⟩
  have hx' : π y * π z = 1 := by rw [← map_mul]; exact hx
  have hy0 : ρ₂ (π y) = 1 := y.2
  have hz0 : ρ₁ (π z) = 1 := z.2
  have hy1 : y ∈ π₁.ker := by
    have := congrArg ρ₁ hx'
    rw [map_mul, hz0, mul_one, map_one] at this
    exact this
  have hz1 : z ∈ π₂.ker := by
    have := congrArg ρ₂ hx'
    rw [map_mul, hy0, one_mul, map_one] at this
    exact this
  rw [← map_pow, Prod.pow_mk, q₁ y hy1 hy, q₂ z hz1 hz]
  exact map_one μ

theorem sq_eq_one (l n : ℕ) (hl : l.Prime) (m : ℕ) : 0 < m → Nat.Coprime m (6 * l) →
    ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod m)),
      Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ (l ^ n) = 1) →
      ∀ x ∈ π.ker, x ∈ commutator E → x ^ 2 = 1 := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p a hp ha =>
    intro _ hm
    have hp' : Nat.Coprime p (6 * l) := Nat.Coprime.coprime_dvd_left (dvd_pow_self p ha.ne') hm
    have hnd : ¬ p ∣ 6 * l := (Nat.Prime.coprime_iff_not_dvd hp).1 hp'
    refine GlobalTheory.T.sq_eq_one_of_mem_ker_commutator_central_ext_sl l n p a hl hp ?_ ?_
    · refine hp.five_le_of_ne_two_of_ne_three ?_ ?_ <;> rintro rfl <;> apply hnd <;> omega
    · rintro rfl
      exact hnd (dvd_mul_left _ _)
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ _ E _ π _ hc _ x _ hxc
    have hcen : ∀ e : E, e ∈ Subgroup.center E := fun e => hc (by
      rw [MonoidHom.mem_ker]; ext i j; exact Subsingleton.elim _ _)
    have : commutator E = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro e _
      exact Subgroup.mem_centralizer_iff.2 fun g _ => Subgroup.mem_center_iff.1 (hcen e) g
    rw [this, Subgroup.mem_bot] at hxc
    rw [hxc, one_pow]
  | coprime a b ha hb hab iha ihb =>
    intro _ hm
    have hma : Nat.Coprime a (6 * l) := Nat.Coprime.coprime_dvd_left (dvd_mul_right a b) hm
    have hmb : Nat.Coprime b (6 * l) := Nat.Coprime.coprime_dvd_left (dvd_mul_left b a) hm
    exact glue (l ^ n) _ _ _ _ _ (slTwo_zmod_mul_crt_exists_and_eq_one a b hab).1 (slTwo_zmod_mul_crt_exists_and_eq_one a b hab).2
      (commutator_sl2_zmod a (Nat.Coprime.coprime_dvd_right (dvd_mul_right 6 l) hma))
      (iha (by omega) hma) (ihb (by omega) hmb)

theorem exists_hom_to_kernel_eq_sq_on_kernel_of_central_ext_sl2 : ∀ (l n m : ℕ), l.Prime → 0 < m → Nat.Coprime m (6 * l) → ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod m)), Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ (l ^ n) = 1) → ∃ ψ : E →* E, (∀ e, ψ e ∈ π.ker) ∧ ∀ x ∈ π.ker, ψ x = x ^ 2 := by
  intro l n m hl hm hc E _ π hs hcen hk
  exact exists_hom_sq π hs
    (commutator_sl2_zmod m (Nat.Coprime.coprime_dvd_right (dvd_mul_right 6 l) hc)) hcen
    (sq_eq_one l n hl m hm hc E π hs hcen hk)

end GlobalTheory.CentralExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomToKernelSqCentralExtensionSlTwoZModStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_to_kernel_sq_centralExtension_slTwoZMod : ∀ (l n m : ℕ), l.Prime → 0 < m → Nat.Coprime m (6 * l) → ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod m)), Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ (l ^ n) = 1) → ∃ ψ : E →* E, (∀ e, ψ e ∈ π.ker) ∧ ∀ x ∈ π.ker, ψ x = x ^ 2 := by
  first | exact @GlobalTheory.CentralExt.exists_hom_to_kernel_eq_sq_on_kernel_of_central_ext_sl2 | exact GlobalTheory.CentralExt.exists_hom_to_kernel_eq_sq_on_kernel_of_central_ext_sl2 | (intros; apply GlobalTheory.CentralExt.exists_hom_to_kernel_eq_sq_on_kernel_of_central_ext_sl2 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassInvariantDescentCoprimeLevelModPow
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.CoprimeDescent

theorem exists_cocycle {Q A : Type} [Group Q] [CommGroup A] (φ : Q →* MulAut A) (m : ℕ) (f : A)
    (hf : ∀ q, ∃ g, φ q f = f * g ^ m) (htor : ∀ a : A, a ^ m = 1 → ∀ q, φ q a = a)
    (hQ : ∀ (E : Type) [Group E] (π : E →* Q), Function.Surjective π → π.ker ≤ Subgroup.center E →
      (∀ x ∈ π.ker, x ^ m = 1) → ∃ ψ : E →* E, (∀ e, ψ e ∈ π.ker) ∧ ∀ x ∈ π.ker, ψ x = x ^ 2) :
    ∃ c : Q → A, (∀ q q', c (q * q') = c q * φ q (c q')) ∧ ∀ q, φ q (f ^ 2) = f ^ 2 * c q ^ m := by
  let E : Subgroup (A ⋊[φ] Q) :=
    { carrier := {x | φ x.right f = f * x.left ^ m}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        simp only [SemidirectProduct.mul_right, SemidirectProduct.mul_left, map_mul, MulAut.mul_apply, hy, hx,
          map_pow, mul_pow, mul_assoc]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        simp only [SemidirectProduct.inv_right, SemidirectProduct.inv_left]
        have h := congrArg (φ x.right⁻¹) hx
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply, map_mul, map_pow] at h
        rw [map_inv (φ x.right⁻¹), inv_pow, eq_mul_inv_iff_mul_eq]
        exact h.symm }
  have hE : ∀ x, x ∈ E ↔ φ x.right f = f * x.left ^ m := fun x => Iff.rfl
  let π : E →* Q := SemidirectProduct.rightHom.comp E.subtype
  have hπ : ∀ x : E, π x = x.1.right := fun x => rfl
  have hker : ∀ x : E, x ∈ π.ker → x.1.right = 1 ∧ x.1.left ^ m = 1 := by
    intro x hx
    have h1 : x.1.right = 1 := hx
    have h2 := (hE x.1).1 x.2
    rw [h1, map_one, MulAut.one_apply] at h2
    exact ⟨h1, by simpa using h2.symm⟩
  have hpow : ∀ x : E, x ∈ π.ker → ∀ k : ℕ, (x ^ k).1.left = x.1.left ^ k := by
    intro x hx k
    have : x.1 = SemidirectProduct.inl x.1.left := by
      ext
      · simp
      · simp [(hker x hx).1]
    rw [SubgroupClass.coe_pow, this, ← map_pow, SemidirectProduct.left_inl, SemidirectProduct.left_inl]
  choose g hg using hf
  let s : Q → E := fun q => ⟨⟨g q, q⟩, hg q⟩
  obtain ⟨ψ, hψ1, hψ2⟩ := hQ E π (fun q => ⟨s q, rfl⟩)
    (by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨h1, h2⟩ := hker x hx
      apply Subtype.ext
      ext
      · simp [h1, htor _ h2, mul_comm]
      · simp [h1])
    (by
      intro x hx
      apply Subtype.ext
      ext
      · rw [hpow x hx, (hker x hx).2]; rfl
      · exact (hker _ (π.ker.pow_mem hx m)).1)
  let χ : E → A := fun x => (ψ x).1.left
  have hχ : ∀ x y, χ (x * y) = χ x * χ y := by
    intro x y
    simp [χ, (hker _ (hψ1 x)).1]
  have hχm : ∀ x, χ x ^ m = 1 := fun x => (hker _ (hψ1 x)).2
  let C : E → A := fun x => x.1.left ^ 2 * (χ x)⁻¹
  have hC : ∀ x y, C (x * y) = C x * φ x.1.right (C y) := by
    intro x y
    simp only [C, hχ, Subgroup.coe_mul, SemidirectProduct.mul_left, map_mul, map_pow, map_inv, htor _ (hχm y),
      mul_pow, _root_.mul_inv_rev]
    rw [mul_comm (χ y)⁻¹, mul_mul_mul_comm]
  have hC1 : ∀ x ∈ π.ker, C x = 1 := by
    intro x hx
    simp only [C, χ, hψ2 x hx, hpow x hx, mul_inv_cancel]
  have hCs : ∀ x : E, C x = C (s x.1.right) := by
    intro x
    have hk : x * (s x.1.right)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      exact mul_inv_cancel _
    have := hC (x * (s x.1.right)⁻¹) (s x.1.right)
    rw [hC1 _ hk, (hker _ hk).1, inv_mul_cancel_right] at this
    simpa using this
  refine ⟨fun q => C (s q), fun q q' => ?_, fun q => ?_⟩
  · have := hC (s q) (s q')
    rw [hCs] at this
    exact this
  · have h : (s q).1.left = g q := rfl
    simp only [C, mul_pow, inv_pow, hχm, h, map_pow, hg q, inv_one, mul_one]
    rw [← pow_mul, ← pow_mul, mul_comm m 2]

theorem exists_invariant {Q F : Type} [Group Q] [Finite Q] [Field F] [CharZero F] (τ : Q → F →+* F)
    (hτ : ∀ q q' a, τ (q * q') a = τ q' (τ q a)) (m : ℕ) (f : Fˣ)
    (hf : ∀ q, ∃ g : Fˣ, τ q f = f * (g : F) ^ m) (htor : ∀ a : F, a ^ m = 1 → ∀ q, τ q a = a)
    (hsq : ∀ q, (∀ a, τ q a = a) → q * q = 1)
    (hQ : ∀ (E : Type) [Group E] (π : E →* Q), Function.Surjective π → π.ker ≤ Subgroup.center E →
      (∀ x ∈ π.ker, x ^ m = 1) → ∃ ψ : E →* E, (∀ e, ψ e ∈ π.ker) ∧ ∀ x ∈ π.ker, ψ x = x ^ 2) :
    ∃ h : Fˣ, ∀ q, τ q ((f : F) ^ 4 * (h : F) ^ m) = (f : F) ^ 4 * (h : F) ^ m := by
  have h1 : ∀ a, τ 1 a = a := by
    intro a
    have e := hτ 1 1 a
    rw [mul_one] at e
    exact (τ 1).injective e.symm
  let φ0 : Q → MulAut Fˣ := fun q =>
    { toFun := Units.map (τ q⁻¹ : F →* F)
      invFun := Units.map (τ q : F →* F)
      left_inv := fun a => Units.ext (by simp [← hτ, h1])
      right_inv := fun a => Units.ext (by simp [← hτ, h1])
      map_mul' := map_mul _ }
  have hφ0 : ∀ q a, (φ0 q a : F) = τ q⁻¹ a := fun q a => rfl
  let φ : Q →* MulAut Fˣ := MonoidHom.mk' φ0 (by
    intro q q'
    ext a
    simp only [MulAut.mul_apply, hφ0, _root_.mul_inv_rev, hτ])
  have hφ : ∀ q a, (φ q a : F) = τ q⁻¹ a := fun q a => rfl
  obtain ⟨c, hc1, hc2⟩ := exists_cocycle φ m f
    (fun q => by
      obtain ⟨g, hg⟩ := hf q⁻¹
      exact ⟨g, Units.ext (by rw [hφ, hg]; simp)⟩)
    (fun a ha q => Units.ext (by
      rw [hφ]
      exact htor _ (by rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]) _)) hQ
  have hc0 : c 1 = 1 := by
    have := hc1 1 1
    simpa using this
  obtain ⟨h, hh⟩ := GlobalTheory.exists_unit_of_cocycle_rightAction_charZero F Q τ hτ (fun q => c q⁻¹ ^ 2)
    (fun q q' => by
      rw [_root_.mul_inv_rev, hc1]
      simp only [Units.val_pow_eq_pow_val, Units.val_mul, hφ, inv_inv, map_pow]
      ring)
    (fun q hq => by
      have e := hc1 q⁻¹ q⁻¹
      rw [← _root_.mul_inv_rev, hsq q hq, inv_one, hc0] at e
      have e2 : φ q⁻¹ (c q⁻¹) = c q⁻¹ := Units.ext (by rw [hφ, inv_inv, hq])
      rw [e2] at e
      rw [sq, ← e])
  refine ⟨h⁻¹, fun q => ?_⟩
  have e := congrArg Units.val (hc2 q⁻¹)
  rw [hφ, inv_inv] at e
  simp only [Units.val_pow_eq_pow_val, Units.val_mul] at e
  have e4 : (f : F) ^ 4 = ((f : F) ^ 2) ^ 2 := by ring
  have hc := (c q⁻¹).ne_zero
  have hh0 := h.ne_zero
  rw [map_mul, map_pow (τ q) _ m, Units.val_inv_eq_inv_val, map_inv₀, hh q, e4, map_pow, e]
  simp only [Units.val_pow_eq_pow_val, mul_inv, mul_pow, inv_pow]
  have : ((c q⁻¹ : F) ^ 2) ^ m = ((c q⁻¹ : F) ^ m) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [this]
  field_simp

theorem mem_gamma_iff {M : ℕ} {γ : SL(2, ℤ)} :
    γ ∈ CongruenceSubgroup.Gamma M ↔ ∀ i j, (M : ℤ) ∣ γ i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp only [← ZMod.intCast_zmod_eq_zero_iff_dvd, Fin.forall_fin_two]
  simp [sub_eq_zero, and_assoc]

theorem gamma_mono {M N : ℕ} (h : M ∣ N) : CongruenceSubgroup.Gamma N ≤ CongruenceSubgroup.Gamma M := by
  intro γ hγ
  rw [mem_gamma_iff] at hγ ⊢
  exact fun i j => (Int.natCast_dvd_natCast.2 h).trans (hγ i j)

theorem gamma_inf {M N : ℕ} (h : Nat.Coprime M N) {γ : SL(2, ℤ)} (h1 : γ ∈ CongruenceSubgroup.Gamma M)
    (h2 : γ ∈ CongruenceSubgroup.Gamma N) : γ ∈ CongruenceSubgroup.Gamma (M * N) := by
  rw [mem_gamma_iff] at h1 h2 ⊢
  intro i j
  push_cast
  exact (Nat.isCoprime_iff_coprime.2 h).mul_dvd (h1 i j) (h2 i j)

theorem exists_lift {M N : ℕ} (h : Nat.Coprime M N) (q : SL(2, ZMod N)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma M, SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ = q := by
  let e := ZMod.chineseRemainder h
  let B : Matrix (Fin 2) (Fin 2) (ZMod M × ZMod N) :=
    Matrix.of fun i j => ((1 : Matrix (Fin 2) (Fin 2) (ZMod M)) i j, q i j)
  have hB : B.det = 1 := by
    have := q.det_coe
    rw [Matrix.det_fin_two] at this ⊢
    ext
    · simp [B]
    · simpa [B] using this
  obtain ⟨γ, hγ⟩ := GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective (M * N)
    (SpecialLinearGroup.map (e.symm : ZMod M × ZMod N →+* ZMod (M * N)) ⟨B, hB⟩)
  have key : ∀ i j, ((γ i j : ℤ) : ZMod M × ZMod N) = B i j := by
    intro i j
    have h1 : ((γ i j : ℤ) : ZMod (M * N)) = e.symm (B i j) := congrArg (fun x : SL(2, ZMod (M * N)) => x i j) hγ
    have h2 := congrArg e h1
    rwa [map_intCast, RingEquiv.apply_symm_apply] at h2
  refine ⟨γ, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma_mem]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [B] using congrArg Prod.fst (key 0 0)
    · simpa [B] using congrArg Prod.fst (key 0 1)
    · simpa [B] using congrArg Prod.fst (key 1 0)
    · simpa [B] using congrArg Prod.fst (key 1 1)
  · ext i j
    simpa [B] using congrArg Prod.snd (key i j)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def levSub (X : Tower Ω ε) (M : ℕ) : Subfield X.K where
  carrier := {f | Lev X M f}
  mul_mem' := fun ha hb γ hγ => by rw [map_mul, ha γ hγ, hb γ hγ]
  one_mem' := fun γ _ => map_one _
  add_mem' := fun ha hb γ hγ => by rw [map_add (f := _), ha γ hγ, hb γ hγ]
  zero_mem' := fun γ _ => map_zero _
  neg_mem' := fun ha γ hγ => by rw [map_neg, ha γ hγ]
  inv_mem' := fun a ha γ hγ => by rw [map_inv₀, ha γ hγ]

theorem lev_sl (X : Tower Ω ε) {M : ℕ} {f : X.K} (hf : Lev X M f) (γ : SL(2, ℤ)) :
    Lev X M (X.sl (ofSL γ) f) := by
  intro δ hδ
  have h := hf _ ((CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ γ)
  rw [← X.sl_mul, ← map_mul]
  conv_rhs => rw [← h]
  rw [← X.sl_mul, ← map_mul, inv_mul_cancel_right]

noncomputable def levAct (X : Tower Ω ε) (M : ℕ) (γ : SL(2, ℤ)) : levSub X M →+* levSub X M :=
  RingHom.codRestrict ((X.sl (ofSL γ) : X.K →+* X.K).comp (levSub X M).subtype) (levSub X M)
    fun a => lev_sl X a.2 γ

theorem coe_levAct (X : Tower Ω ε) (M : ℕ) (γ : SL(2, ℤ)) (a : levSub X M) :
    (levAct X M γ a : X.K) = X.sl (ofSL γ) a := rfl

theorem sl_root [IsAlgClosed Ω] (X : Tower Ω ε) {m : ℕ} (hm : 0 < m) {a : X.K} (ha : a ^ m = 1) (g : GQ) :
    X.sl g a = a := by
  have hi : IsIntegral Ω a := IsIntegral.of_pow hm (ha ▸ isIntegral_one)
  obtain ⟨b, rfl⟩ := minpoly.mem_range_of_degree_eq_one Ω a
    (IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hi))
  exact AlgEquiv.commutes _ b

theorem descent : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l n Ma Mb : ℕ), l.Prime → 0 < Ma → 0 < Mb → 6 * l ∣ Ma → Nat.Coprime Ma Mb → ∀ f : X.Kˣ, Lev X (Ma * Mb) f → (∀ γ ∈ CongruenceSubgroup.Gamma Ma, ∃ g : X.Kˣ, Lev X (Ma * Mb) g ∧ X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) → ∃ h : X.Kˣ, Lev X Ma ((f : X.K) ^ 4 * (h : X.K) ^ (l ^ n)) := by
  intro Ω _ _ _ ε X l n Ma Mb hl hMa hMb h6 hco f hf hinv
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : CharZero X.K := charZero_of_injective_algebraMap (algebraMap Ω X.K).injective
  haveI : NeZero Mb := ⟨hMb.ne'⟩
  let ρ : SL(2, ℤ) →* SL(2, ZMod Mb) := SpecialLinearGroup.map (Int.castRingHom (ZMod Mb))
  choose s hs1 hs2 using exists_lift hco
  have hs2' : ∀ q, ρ (s q) = q := hs2
  have hact : ∀ γ ∈ CongruenceSubgroup.Gamma Ma, ∀ a : X.K, Lev X (Ma * Mb) a →
      X.sl (ofSL (s (ρ γ))) a = X.sl (ofSL γ) a := by
    intro γ hγ a ha
    have hm : s (ρ γ) * γ⁻¹ ∈ CongruenceSubgroup.Gamma (Ma * Mb) := by
      refine gamma_inf hco (Subgroup.mul_mem _ (hs1 _) (Subgroup.inv_mem _ hγ)) ?_
      show ρ (s (ρ γ) * γ⁻¹) = 1
      rw [map_mul, map_inv, hs2', mul_inv_cancel]
    conv_rhs => rw [← ha _ hm]
    rw [← X.sl_mul, ← map_mul, inv_mul_cancel_right]
  let u : ∀ g : X.Kˣ, Lev X (Ma * Mb) g → (levSub X (Ma * Mb))ˣ := fun g hg =>
    Units.mk0 ⟨g, hg⟩ (fun h => g.ne_zero (congrArg Subtype.val h))
  obtain ⟨h, hh⟩ := exists_invariant (Q := SL(2, ZMod Mb)) (fun q => levAct X (Ma * Mb) (s q))
    (fun q q' a => Subtype.ext (by
      rw [coe_levAct, coe_levAct, coe_levAct, ← X.sl_mul, ← map_mul,
        ← hact _ (Subgroup.mul_mem _ (hs1 q) (hs1 q')) _ a.2, map_mul, hs2', hs2']))
    (l ^ n) (u f hf)
    (fun q => by
      obtain ⟨g, hg1, hg2⟩ := hinv _ (hs1 q)
      exact ⟨u g hg1, Subtype.ext hg2⟩)
    (fun a ha q => Subtype.ext (sl_root X (pow_pos hl.pos n) (congrArg Subtype.val ha) _))
    (fun q hq => by
      obtain ⟨h1, h2⟩ := GlobalTheory.T.jTranslates_level_and_scalar_mod ε X Mb hMb
      obtain ⟨e1, e2, e3⟩ := h2 (s q) (fun g hg =>
        congrArg Subtype.val (hq ⟨_, fun γ hγ => h1 g hg γ (gamma_mono (dvd_mul_left Mb Ma) hγ)⟩))
      have key : ∀ i j, (en (s q) i j : ZMod Mb) = q i j := fun i j =>
        congrArg (fun x : SL(2, ZMod Mb) => x i j) (hs2 q)
      simp only [key] at e1 e2 e3
      have hd := q.det_coe
      rw [Matrix.det_fin_two, e1, e2] at hd
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, e1, e2] <;>
        first | (simpa [e3] using hd))
    (GlobalTheory.T.exists_hom_to_kernel_sq_centralExtension_slTwoZMod l n Mb hl hMb (Nat.Coprime.coprime_dvd_right h6 hco.symm))
  refine ⟨Units.map (levSub X (Ma * Mb)).subtype.toMonoidHom h, fun γ hγ => ?_⟩
  have e := congrArg Subtype.val (hh (ρ γ))
  have hw : ∀ w : levSub X (Ma * Mb), Lev X (Ma * Mb) (w : X.K) := fun w => w.2
  rw [coe_levAct, hact γ hγ _ (hw _)] at e
  exact e

end GlobalTheory.KZ.ES.CoprimeDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassInvariantDescentCoprimeLevelModPowStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classInvariant_descent_coprimeLevel_modPow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l n Ma Mb : ℕ), l.Prime → 0 < Ma → 0 < Mb → 6 * l ∣ Ma → Nat.Coprime Ma Mb → ∀ f : X.Kˣ, Lev X (Ma * Mb) f → (∀ γ ∈ CongruenceSubgroup.Gamma Ma, ∃ g : X.Kˣ, Lev X (Ma * Mb) g ∧ X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) → ∃ h : X.Kˣ, Lev X Ma ((f : X.K) ^ 4 * (h : X.K) ^ (l ^ n)) := by
  first | exact @GlobalTheory.KZ.ES.CoprimeDescent.descent | exact GlobalTheory.KZ.ES.CoprimeDescent.descent | (intros; apply GlobalTheory.KZ.ES.CoprimeDescent.descent <;> assumption)
end
