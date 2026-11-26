module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.DecompTypeI
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RdBound

@[expose] public section

section -- merged from Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RdDiff
open NumberField IntermediateField Polynomial ArithmeticFunction

noncomputable section

namespace Formalism.HC.Der.Rd

private theorem log_abs_eval_one_cyclotomic_eq_vonMangoldt {m : ℕ} (hm : 1 < m) :
    Real.log |((eval 1 (cyclotomic m ℚ) : ℚ) : ℝ)| = vonMangoldt m := by
  by_cases h : IsPrimePow m
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).1 h
    rcases k with _ | j
    · omega
    haveI := Fact.mk hp
    rw [eval_one_cyclotomic_prime_pow, vonMangoldt_apply_pow (Nat.succ_ne_zero j),
      vonMangoldt_apply_prime hp]
    simp
  · rw [eval_one_cyclotomic_not_prime_pow, vonMangoldt_eq_zero_iff.2 h]
    · simp
    · intro p hp k hk
      apply h
      rw [← hk]
      refine hp.isPrimePow.pow ?_
      rintro rfl
      rw [pow_zero] at hk
      omega

private theorem log_abs_norm_sub_one_mul_totient_eq {m : ℕ} (hm : 1 < m) {L : Type*} [Field L] [NumberField L] {η : L}
    (hη : IsPrimitiveRoot η m) :
    Real.log |((Algebra.norm ℚ (η - 1) : ℚ) : ℝ)| * (m.totient : ℝ) = (Module.finrank ℚ L : ℝ) * vonMangoldt m := by
  have hm0 : 0 < m := by omega
  have hint_r : IsIntegral ℚ η := .of_finite ℚ η
  have hx : IsIntegral ℚ (η - 1) := .of_finite ℚ _
  have hmin : minpoly ℚ (η - 1) = (cyclotomic m ℚ).comp (X + C 1) := by
    have h0 : minpoly ℚ (η - algebraMap ℚ L 1) = (minpoly ℚ η).comp (X + C 1) := by
      exact minpoly.sub_algebraMap η (1 : ℚ)
    rw [map_one] at h0
    rw [h0, ← cyclotomic_eq_minpoly_rat hη hm0]
  have hdeg : Module.finrank ℚ ℚ⟮η - 1⟯ = m.totient := by
    rw [IntermediateField.adjoin.finrank hx, hmin, natDegree_comp, natDegree_cyclotomic, natDegree_X_add_C,
      mul_one]
  have hnormval : Algebra.norm ℚ (η - 1) =
      ((-1) ^ m.totient * eval 1 (cyclotomic m ℚ)) ^ Module.finrank ℚ⟮η - 1⟯ L := by
    rw [Algebra.norm_eq_norm_adjoin ℚ (η - 1)]
    congr 1
    have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hx)
    rw [IntermediateField.adjoin.powerBasis_dim] at h
    rw [show IntermediateField.AdjoinSimple.gen ℚ (η - 1) = (IntermediateField.adjoin.powerBasis hx).gen from rfl,
      h, IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, hmin, coeff_zero_eq_eval_zero,
      eval_comp, natDegree_comp, natDegree_cyclotomic, natDegree_X_add_C, mul_one]
    simp
  have habs : |((Algebra.norm ℚ (η - 1) : ℚ) : ℝ)| =
      |((eval 1 (cyclotomic m ℚ) : ℚ) : ℝ)| ^ Module.finrank ℚ⟮η - 1⟯ L := by
    rw [hnormval]; push_cast; rw [abs_pow, abs_mul, abs_pow]; simp
  haveI : Module.Free ℚ ℚ⟮η - 1⟯ := Module.Free.of_divisionRing _ _
  rw [habs, Real.log_pow, log_abs_eval_one_cyclotomic_eq_vonMangoldt hm, ← Module.finrank_mul_finrank ℚ ℚ⟮η - 1⟯ L, hdeg]
  push_cast; ring

private theorem absNorm_map_algebraMap_eq_pow_finrank {L E : Type*} [Field L] [NumberField L] [Field E] [NumberField E]
    [Algebra E L] (I : Ideal (𝓞 E)) :
    Ideal.absNorm (I.map (algebraMap (𝓞 E) (𝓞 L))) = Ideal.absNorm I ^ Module.finrank E L := by
  have hr : Module.finrank (𝓞 E) (𝓞 L) = Module.finrank E L := by
    exact (IsFractionRing.finrank_eq (𝓞 E) E (𝓞 L) L).symm
  rw [Ideal.absNorm_algebraMap (𝓞 E) (𝓞 L) I, hr]

variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L] {ζ : L}
  (hζ : IsPrimitiveRoot ζ N) (E : Type*) [Field E] [NumberField E] [Algebra E L]
include hζ


set_option maxHeartbeats 800000 in
theorem adjoin_top : Algebra.adjoin E {ζ} = ⊤ := by
  have h1 : Algebra.adjoin ℚ ({ζ} : Set L) = ⊤ := IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  refine eq_top_iff.2 fun x hxt => ?_
  clear hxt
  have hx : x ∈ Algebra.adjoin ℚ ({ζ} : Set L) := by rw [h1]; exact Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
    rw [eq_ratCast (algebraMap ℚ L) r, ← map_ratCast (algebraMap E L) r]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem gal_inj : Function.Injective fun σ : L ≃ₐ[E] L => σ ζ := by
  intro σ τ h
  have := AlgHom.ext_of_adjoin_eq_top (adjoin_top hζ E)
    (φ₁ := (σ : L →ₐ[E] L)) (φ₂ := (τ : L →ₐ[E] L)) (by simpa using h)
  exact AlgEquiv.coe_algHom_injective this

theorem minpoly_map : (minpoly E ζ).map (algebraMap E L) = Lagrange.nodal Finset.univ fun σ : L ≃ₐ[E] L => σ ζ := by
  haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
  haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {N} ℚ L
  haveI : IsGalois E L := IsGalois.tower_top_of_isGalois ℚ E L
  have hint_r : IsIntegral E ζ := .of_finite E ζ
  have htop : E⟮ζ⟯ = ⊤ := by
    rw [eq_top_iff]; intro x _
    have hx : x ∈ Algebra.adjoin E ({ζ} : Set L) := by
      rw [adjoin_top hζ E]; exact Algebra.mem_top
    first
    | exact IntermediateField.algebra_adjoin_le_adjoin E ({ζ} : Set L) hx
    | exact IntermediateField.algebra_adjoin_le_adjoin (F := E) (S := ({ζ} : Set L)) hx
  have hcard : Fintype.card (L ≃ₐ[E] L) = Module.finrank E L := by
    rw [← IsGalois.card_aut_eq_finrank E L, Nat.card_eq_fintype_card]
  have hinj := gal_inj hζ E
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic
  · exact (minpoly.monic hint_r).map _
  · unfold Lagrange.nodal
    refine Finset.prod_dvd_of_coprime ((Polynomial.pairwise_coprime_X_sub_C hinj).set_pairwise _)
      fun σ _ => ?_
    rw [Polynomial.dvd_iff_isRoot, IsRoot.def, eval_map, ← aeval_def]
    have := Polynomial.aeval_algHom_apply (σ : L →ₐ[E] L) ζ (minpoly E ζ)
    rw [minpoly.aeval, _root_.map_zero] at this
    exact this
  · refine le_of_eq ?_
    rw [natDegree_map, ← IntermediateField.adjoin.finrank hint_r, htop, IntermediateField.finrank_top',
      Lagrange.natDegree_nodal, Finset.card_univ, hcard]

open Classical in
theorem absNorm_diff : ((Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 L)) : ℕ) : ℝ) =
    ∏ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| := by
  haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
  have hζL : algebraMap (𝓞 L) L hζ.toInteger = ζ := hζ.coe_toInteger
  have hadjZ : Algebra.adjoin ℤ ({hζ.toInteger} : Set (𝓞 L)) = ⊤ :=
    IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hζ
  generalize hζ.toInteger = z at hζL hadjZ
  have hadj : Algebra.adjoin (𝓞 E) ({z} : Set (𝓞 L)) = ⊤ := by
    refine eq_top_iff.2 fun x hxt => ?_
    clear hxt
    have hx : x ∈ Algebra.adjoin ℤ ({z} : Set (𝓞 L)) := by rw [hadjZ]; exact Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin hx
    | algebraMap r =>
      rw [IsScalarTower.algebraMap_apply ℤ (𝓞 E) (𝓞 L)]; exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have hK : Algebra.adjoin E {algebraMap (𝓞 L) L z} = ⊤ := by
    rw [hζL]; exact adjoin_top hζ E
  have hD := conductor_mul_differentIdeal (𝓞 E) E L z hK
  have hc : conductor (𝓞 E) z = ⊤ := by
    first
    | exact conductor_eq_top_of_adjoin_eq_top hadj
    | exact conductor_eq_top_of_adjoin_eq_top _ hadj
    | exact conductor_eq_top_of_adjoin_eq_top (𝓞 E) hadj
  rw [hc, Ideal.top_mul] at hD
  have hint_r : IsIntegral (𝓞 E) ζ := (hζ.isIntegral (NeZero.pos N)).tower_top
  have hminE : minpoly E ζ = (minpoly (𝓞 E) z).map (algebraMap (𝓞 E) E) := by
    rw [← minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 L) L) z, hζL]
    first
    | exact minpoly.isIntegrallyClosed_eq_field_fractions' E hint_r
    | exact minpoly.isIntegrallyClosed_eq_field_fractions' (K := E) hint_r
  have hmapL : (minpoly (𝓞 E) z).map (algebraMap (𝓞 E) L) =
      Lagrange.nodal Finset.univ (fun σ : L ≃ₐ[E] L => σ ζ) := by
    rw [← minpoly_map hζ E, hminE, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hy : algebraMap (𝓞 L) L (aeval z (derivative (minpoly (𝓞 E) z))) =
      ∏ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, (ζ - σ ζ) := by
    rw [← aeval_algebraMap_apply, hζL, aeval_def, eval₂_eq_eval_map, ← derivative_map, hmapL]
    have h1 := Lagrange.eval_nodal_derivative_eval_node_eq (s := (Finset.univ : Finset (L ≃ₐ[E] L)))
      (v := fun σ : L ≃ₐ[E] L => σ ζ) (Finset.mem_univ 1)
    rw [Lagrange.eval_nodal] at h1
    exact h1
  have hnormR : ((Algebra.norm ℤ (aeval z (derivative (minpoly (𝓞 E) z))) : ℤ) : ℝ) =
      ((Algebra.norm ℚ (∏ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, (ζ - σ ζ)) : ℚ) : ℝ) := by
    rw [← hy, ← Algebra.coe_norm_int]; norm_cast
  rw [hD, Ideal.absNorm_span_singleton]
  simp only [Nat.cast_natAbs, Int.cast_abs]
  rw [hnormR, map_prod, Rat.cast_prod,
    Finset.abs_prod]

open Classical in
theorem log_discr_tower : Real.log |(discr L : ℝ)| =
    ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| +
      Module.finrank E L * Real.log |(discr E : ℝ)| := by
  haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
  have hD := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 E) (𝓞 L)
  have h1 : ((Ideal.absNorm (differentIdeal ℤ (𝓞 L)) : ℕ) : ℝ) = |(discr L : ℝ)| := by
    rw [NumberField.absNorm_differentIdeal L (𝓞 L)]
    simp only [Nat.cast_natAbs, Int.cast_abs]
  have hE : ((Ideal.absNorm (differentIdeal ℤ (𝓞 E)) : ℕ) : ℝ) = |(discr E : ℝ)| := by
    rw [NumberField.absNorm_differentIdeal E (𝓞 E)]
    simp only [Nat.cast_natAbs, Int.cast_abs]
  have hne : ∀ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1,
      |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| ≠ 0 := by
    intro σ hσ
    have hσ1 : σ ≠ 1 := Finset.ne_of_mem_erase hσ
    have hne : ζ - σ ζ ≠ 0 := by
      intro h
      apply hσ1
      apply gal_inj hζ E
      exact (sub_eq_zero.1 h).symm
    rw [abs_ne_zero, Rat.cast_ne_zero]
    exact Algebra.norm_ne_zero_iff.2 hne
  have hdE : |(discr E : ℝ)| ≠ 0 := abs_ne_zero.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))
  rw [← h1, hD, map_mul, absNorm_map_algebraMap_eq_pow_finrank, Nat.cast_mul, Nat.cast_pow, absNorm_diff hζ E,
    hE, Real.log_mul (Finset.prod_ne_zero_iff.2 hne) (pow_ne_zero _ hdE), Real.log_prod hne, Real.log_pow]

open Classical in
theorem log_discr_sub : Module.finrank E L * Real.log |(discr E : ℝ)| =
    ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter (fun σ => ¬ ∀ x : E, σ (algebraMap E L x) = algebraMap E L x),
      Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| := by
  have sum_log_aut_eq_sum_filter_lemma_4 {N : ℕ} [NeZero N] {L : Type _} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ N) (E : Type _) [Field E] [NumberField E] [Algebra E L] :
      ∑ τ : L ≃ₐ[E] L, Real.log |((Algebra.norm ℚ (ζ - τ ζ) : ℚ) : ℝ)| =
        ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter
          (fun σ => ∀ x : E, σ (algebraMap E L x) = algebraMap E L x),
          Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| := by
    refine Finset.sum_bij (fun τ _ => τ.restrictScalars ℚ) ?_ ?_ ?_ ?_
    · intro τ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro x; exact τ.commutes x
    · intro a _ b _ h; exact AlgEquiv.restrictScalars_injective ℚ h
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hσ, Finset.mem_univ _, by ext x; rfl⟩
    · intro τ _; rfl
  have h1 := log_discr_tower hζ E
  have h2 := log_discr_tower hζ ℚ
  rw [NumberField.discr_rat] at h2
  simp only [Int.cast_one, abs_one, Real.log_one, mul_zero, add_zero] at h2
  have e1 : ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| =
      ∑ σ : L ≃ₐ[E] L, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| :=
    Finset.sum_erase _ (by simp [Algebra.norm_zero])
  have e2 : ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).erase 1, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| =
      ∑ σ : L ≃ₐ[ℚ] L, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| :=
    Finset.sum_erase _ (by simp [Algebra.norm_zero])
  have hsplit : ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter
        (fun σ => ∀ x : E, σ (algebraMap E L x) = algebraMap E L x),
        Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| +
      ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter
        (fun σ => ¬ ∀ x : E, σ (algebraMap E L x) = algebraMap E L x),
        Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| =
      ∑ σ : L ≃ₐ[ℚ] L, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hsub := sum_log_aut_eq_sum_filter_lemma_4 hζ E
  linarith

omit E in
theorem log_norm_weight (u : ZMod N) (hu : u ≠ 1) :
    Real.log |((Algebra.norm ℚ (ζ - ζ ^ u.val) : ℚ) : ℝ)| =
      (N.totient : ℝ) * (vonMangoldt (addOrderOf (u - 1)) / ((addOrderOf (u - 1)).totient : ℝ)) := by
  have hN : N ≠ 0 := NeZero.ne N
  have hw : (1 - u).val ≠ 0 := by
    rw [Ne, ZMod.val_eq_zero, sub_eq_zero]; exact Ne.symm hu
  have hmod : ζ ^ (u.val + (1 - u).val) = ζ := by
    have h1 : (u.val + (1 - u).val) % orderOf ζ = 1 % orderOf ζ := by
      rw [← hζ.eq_orderOf, ← ZMod.val_add, show u + (1 - u) = 1 by ring, ZMod.val_one_eq_one_mod]
    rw [← pow_mod_orderOf, h1, pow_mod_orderOf, pow_one]
  have hfac : ζ - ζ ^ u.val = ζ ^ u.val * (ζ ^ (1 - u).val - 1) := by
    calc ζ - ζ ^ u.val = ζ ^ (u.val + (1 - u).val) - ζ ^ u.val := by rw [hmod]
      _ = ζ ^ u.val * (ζ ^ (1 - u).val - 1) := by ring
  have hnz : |((Algebra.norm ℚ ζ : ℚ) : ℝ)| = 1 := by
    have h : (Algebra.norm ℚ ζ) ^ N = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    have h' : |((Algebra.norm ℚ ζ : ℚ) : ℝ)| ^ N = 1 := by
      rw [← abs_pow, ← Rat.cast_pow, h, Rat.cast_one, abs_one]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) hN).1 h'
  have hd : orderOf (ζ ^ (1 - u).val) = addOrderOf (u - 1) := by
    rw [orderOf_pow' ζ hw, ← hζ.eq_orderOf,
      show u - 1 = -(((1 - u).val : ℕ) : ZMod N) by rw [ZMod.natCast_zmod_val]; ring,
      addOrderOf_neg, ZMod.addOrderOf_coe _ hN]
  have hη : IsPrimitiveRoot (ζ ^ (1 - u).val) (addOrderOf (u - 1)) := by
    rw [← hd]; exact IsPrimitiveRoot.orderOf _
  have hd1 : 1 < addOrderOf (u - 1) := by
    have h0 : 0 < addOrderOf (u - 1) := addOrderOf_pos _
    have h1 : addOrderOf (u - 1) ≠ 1 := by
      intro h
      have := addOrderOf_nsmul_eq_zero (u - 1)
      rw [h, one_nsmul, sub_eq_zero] at this
      exact hu this
    omega
  have key := log_abs_norm_sub_one_mul_totient_eq hd1 hη
  rw [IsCyclotomicExtension.finrank L (cyclotomic.irreducible_rat (NeZero.pos N))] at key
  rw [hfac, map_mul, map_pow, Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow, hnz, one_pow, one_mul]
  have ht : (0 : ℝ) < (addOrderOf (u - 1)).totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  rw [mul_div_assoc', eq_div_iff ht.ne']
  exact key


local instance (p : Prop) : Decidable p := Classical.propDecidable p

open Classical in
theorem log_rd (U : Subgroup (ZMod N)ˣ)
    (hU : ∀ (σ : L ≃ₐ[ℚ] L) (u : (ZMod N)ˣ), σ ζ = ζ ^ (u : ZMod N).val →
      ((∀ x : E, σ (algebraMap E L x) = algebraMap E L x) ↔ u ∈ U)) :
    Real.log |(discr E : ℝ)| / Module.finrank ℚ E =
      ∑ u ∈ (Finset.univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U),
        vonMangoldt (addOrderOf ((u : ZMod N) - 1)) / ((addOrderOf ((u : ZMod N) - 1)).totient : ℝ) := by
  classical
  haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
  haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {N} ℚ L
  have hφ : Module.finrank ℚ L = N.totient :=
    IsCyclotomicExtension.finrank L (cyclotomic.irreducible_rat (NeZero.pos N))
  have hcard : Fintype.card (L ≃ₐ[ℚ] L) = Fintype.card (ZMod N)ˣ := by
    rw [ZMod.card_units_eq_totient, ← hφ, ← IsGalois.card_aut_eq_finrank ℚ L, Nat.card_eq_fintype_card]
  have hinj : Function.Injective (hζ.autToPow ℚ) := by
    intro a b h
    apply gal_inj hζ ℚ
    show a ζ = b ζ
    rw [← hζ.autToPow_spec ℚ a, ← hζ.autToPow_spec ℚ b, h]
  have hbij : Function.Bijective (hζ.autToPow ℚ) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩
  have hsum : ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter
        (fun σ => ¬ ∀ x : E, σ (algebraMap E L x) = algebraMap E L x),
        Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| =
      (N.totient : ℝ) * ∑ u ∈ (Finset.univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U),
        vonMangoldt (addOrderOf ((u : ZMod N) - 1)) / ((addOrderOf ((u : ZMod N) - 1)).totient : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_equiv (Equiv.ofBijective _ hbij) ?_ ?_
    · intro σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.ofBijective_apply]
      rw [hU σ _ (hζ.autToPow_spec ℚ σ).symm]
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      have hu : hζ.autToPow ℚ σ ∉ U := by rwa [← hU σ _ (hζ.autToPow_spec ℚ σ).symm]
      have hu1 : ((hζ.autToPow ℚ σ : (ZMod N)ˣ) : ZMod N) ≠ 1 := by
        intro h; apply hu; rw [Units.val_eq_one.1 h]; exact U.one_mem
      simp only [Equiv.ofBijective_apply]
      rw [← hζ.autToPow_spec ℚ σ, log_norm_weight hζ _ hu1]
  have key := log_discr_sub hζ E
  rw [hsum] at key
  have hEQ : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have hLE : (0 : ℝ) < Module.finrank E L := by exact_mod_cast Module.finrank_pos
  have htow : (Module.finrank ℚ E : ℝ) * Module.finrank E L = N.totient := by
    rw [← Nat.cast_mul, Module.finrank_mul_finrank ℚ E L, hφ]
  rw [div_eq_iff hEQ.ne']
  apply mul_left_cancel₀ hLE.ne'
  rw [key, ← htow]; ring

end Formalism.HC.Der.Rd

end
end

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits

namespace Rd

theorem cycRat (m : ℕ) : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨fun h h0 => absurd (Set.mem_singleton_iff.1 h) h0, fun x => ?_⟩
    have htop : Algebra.adjoin ℚ ((Polynomial.cyclotomic 0 ℚ).rootSet
        (Polynomial.cyclotomic 0 ℚ).SplittingField) = ⊤ :=
      Polynomial.SplittingField.adjoin_rootSet _
    rw [Polynomial.cyclotomic_zero, Polynomial.rootSet_one, Algebra.adjoin_empty] at htop
    have hx : x ∈ (⊥ : Subalgebra ℚ (CyclotomicField 0 ℚ)) := by
      rw [show (⊥ : Subalgebra ℚ (CyclotomicField 0 ℚ)) = ⊤ from htop]
      exact Algebra.mem_top
    exact (bot_le : (⊥ : Subalgebra ℚ (CyclotomicField 0 ℚ)) ≤ _) hx
  · haveI : NeZero m := ⟨hm.ne'⟩
    haveI : NeZero (m : ℚ) := ⟨by exact_mod_cast hm.ne'⟩
    exact CyclotomicField.isCyclotomicExtension m ℚ

theorem dvd_discr_of_inertia {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {l : ℕ} (hl : l.Prime)
    (h : ∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})],
      ∃ σ : E ≃ₐ[ℚ] E, σ ≠ 1 ∧ ∀ x : 𝓞 E, σ • x - x ∈ P) : (l : ℤ) ∣ discr E := by
  by_contra hn
  have : Fact l.Prime := ⟨hl⟩
  have hl' := Nat.prime_iff_prime_int.mp hl
  have hpr : (span {(l : ℤ)}).IsPrime := (span_singleton_prime hl'.ne_zero).mpr hl'
  obtain ⟨⟨P, h1, h2⟩⟩ : Nonempty ((span {(l : ℤ)}).primesOver (𝓞 E)) := inferInstance
  have hpb : span {(l : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hl'.ne_zero
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hpb P
  have hun := (not_dvd_discr_iff_forall_liesOver E (𝓞 E) hl').mp hn P (h1.isMaximal hP0) h2
  have hcard := card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[ℚ] E) (span {(l : ℤ)}) P
  rw [ramificationIdxIn_eq_ramificationIdx (span {(l : ℤ)}) P (E ≃ₐ[ℚ] E),
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, Subgroup.card_eq_one] at hcard
  obtain ⟨σ, hσ1, hσ⟩ := h P
  have h3 : σ ∈ P.inertia (E ≃ₐ[ℚ] E) := AddSubgroup.mem_inertia.mpr hσ
  rw [hcard, Subgroup.mem_bot] at h3
  exact hσ1 h3

theorem hcl_eq_one {e : ℕ} {v : (ZMod (2 ^ (e + 2)))ˣ} (h : hcl e v = 1) : v = 1 ∨ v = -1 := by
  unfold hcl at h
  rw [QuotientGroup.eq_one_iff] at h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← hk, ← two_mul, zpow_mul]
    simp
  · right
    rw [← hk, zpow_add, zpow_mul]
    simp

variable {φ : Frame} (H : HostRaw φ)

instance neZeroN : NeZero H.condN :=
  ⟨by have := H.QS_pos; have := H.hyp.1.pos; have := H.hyp.2.1.pos; positivity⟩

theorem log_rd_eq : Real.log H.rd = SS H.art.ker := by
  have := cycRat H.condN
  let : Algebra H.E (CyclotomicField H.condN ℚ) := H.cycEmb.toRingHom.toAlgebra
  have h1 := log_rd H.cycZeta_prim H.E H.art.ker (fun σ u hσ => by
    have h2 := H.art_spec u σ hσ
    rw [MonoidHom.mem_ker, ← H.gal.symm.map_eq_one_iff]
    constructor
    · intro h3
      exact AlgEquiv.ext fun x => H.cycEmb.injective ((h2 x).trans (h3 x))
    · intro h3 x
      rw [h3] at h2
      exact (h2 x).symm)
  have h0 : (0 : ℝ) < |(discr H.E : ℝ)| := by simpa using discr_ne_zero H.E
  rw [HostRaw.rd, Real.log_rpow h0, one_div_mul_eq_div, h1, SS, ← abel]

theorem rd_pos : 0 < H.rd := by
  unfold Formalism.HC.HostRaw.rd
  apply Real.rpow_pos_of_pos
  apply abs_pos.2
  exact_mod_cast NumberField.discr_ne_zero H.E

theorem two_dvd : 2 ^ (φ.e + 2) ∣ H.condN := (H.tower_dvd.mul_right _).mul_right _

theorem hH_art (u : (ZMod H.condN)ˣ) : φ.hH (H.art u).2 = hcl φ.e (ZMod.unitsMap (two_dvd H) u) := by
  apply H.art_h
  show (ZMod.castHom (two_dvd H) (ZMod (2 ^ (φ.e + 2)))) (u : ZMod H.condN) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem q_mul_d_ne_zero : H.q * H.d ≠ 0 := by
  intro h0
  have h1 := H.QS_coprime
  rw [h0, Nat.coprime_zero_right] at h1
  have h2 := H.tower_dvd
  rw [h1, Nat.dvd_one] at h2
  have h3 : 2 ^ 1 ≤ 2 ^ (φ.e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [h2] at h3
  norm_num at h3

theorem div_d : H.condN / H.d = H.QS * H.q := by
  show H.QS * H.q * H.d / H.d = H.QS * H.q
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (right_ne_zero_of_mul (q_mul_d_ne_zero H)))

theorem div_q : H.condN / H.q = H.QS * H.d := by
  show H.QS * H.q * H.d / H.q = H.QS * H.d
  rw [show H.QS * H.q * H.d = H.QS * H.d * H.q by ring]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (left_ne_zero_of_mul (q_mul_d_ne_zero H)))

theorem q_ne_d : H.q ≠ H.d := by
  intro h
  have h1 := H.hyp.2.2.1
  have h2 := H.hyp.2.2.2.1
  rw [h] at h1
  omega

theorem exists_d (C : HostCore H) : ∃ u ∈ KK H.condN (H.QS * H.q), u ∉ H.art.ker := by
  by_contra h
  push Not at h
  have hc : Nat.Coprime (H.QS * H.q) H.d := Nat.Coprime.mul_left H.QS_coprime.coprime_mul_left_right
    ((Nat.coprime_primes H.hyp.1 H.hyp.2.1).mpr (q_ne_d H))
  have h1 := KK_gcd (φ.chD.comp H.art).ker (dvd_mul_right (H.QS * H.q) H.d) (dvd_mul_left H.d (H.QS * H.q))
    (fun u hu => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.mp (h u hu), map_one])
    (fun u hu => by
      apply Units.ext
      refine (C.art_ch u).trans ?_
      rw [jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast Int.natCast_modEq_iff.mpr (mem_KK.mp hu)), jacobiSym.one_left]
      rfl) (-1) (by rw [hc, mem_KK]; exact Nat.modEq_one)
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, H.art_neg_one] at h1
  exact absurd h1 (show ¬ (-1 : ℤˣ) = 1 by decide)

theorem exists_two : ∃ u ∈ KK H.condN (ordCompl[2] H.condN), u ∉ H.art.ker := by
  by_contra h
  push Not at h
  have hc : Nat.Coprime (ordCompl[2] H.condN) (2 ^ (φ.e + 2)) :=
    ((Nat.coprime_ordCompl Nat.prime_two (NeZero.ne _)).pow_left _).symm
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (two_dvd H)
    (ZMod.unitOfCoprime 3 (Nat.Coprime.pow_right _ (by norm_num)))
  have h1 := KK_gcd (φ.hH.comp ((MonoidHom.snd _ _).comp H.art)).ker (Nat.ordCompl_dvd _ 2) (two_dvd H)
    (fun u hu => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.mem_ker.mp (h u hu), map_one, map_one])
    (fun u hu => by
      refine (hH_art H u).trans ?_
      rw [MonoidHom.mem_ker.mp ((mem_ker_iff (two_dvd H) u).mpr (mem_KK.mp hu))]
      rfl) u (by rw [hc, mem_KK]; exact Nat.modEq_one)
  have h2 := (hH_art H u).symm.trans h1
  rw [hu] at h2
  have h3 : 2 ^ 4 ≤ 2 ^ (φ.e + 2) := Nat.pow_le_pow_right (by norm_num) (by have := H.two_le_e; omega)
  rcases hcl_eq_one h2 with h4 | h4
  · have h5 := congrArg Units.val h4
    rw [ZMod.coe_unitOfCoprime, Units.val_one] at h5
    have h6 : ((2 : ℕ) : ZMod (2 ^ (φ.e + 2))) = 0 := by
      push_cast at h5 ⊢
      linear_combination h5
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).mp h6)
    omega
  · have h5 := congrArg Units.val h4
    rw [ZMod.coe_unitOfCoprime, Units.val_neg, Units.val_one] at h5
    have h6 : ((4 : ℕ) : ZMod (2 ^ (φ.e + 2))) = 0 := by
      push_cast at h5 ⊢
      linear_combination h5
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).mp h6)
    omega

theorem rho_d : rho H.art.ker (H.condN / H.d) ≤ 1 / 2 := by
  rw [div_d]
  refine rho_le_half _ (dvd_mul_right _ _) fun u hu v hv h1 h2 => ?_
  rw [MonoidHom.mem_ker] at h1 h2 ⊢
  rw [map_mul, (H.art_d u (mem_KK.mp hu)).resolve_left h1, (H.art_d v (mem_KK.mp hv)).resolve_left h2]
  exact Prod.ext (show ((1, -1) : G0) * (1, -1) = 1 by decide) (mul_one _)

theorem rho_q : rho H.art.ker (H.condN / H.q) ≤ 1 / 2 := by
  rw [div_q]
  have : Fact H.q.Prime := ⟨H.hyp.1⟩
  have hf : H.QS * H.d ∣ H.condN := ⟨H.q, mul_right_comm _ _ _⟩
  have hq : H.q ∣ H.condN := (dvd_mul_left _ _).mul_right _
  have hc : Nat.Coprime (H.QS * H.d) H.q := Nat.Coprime.mul_left H.QS_coprime.coprime_mul_right_right
    ((Nat.coprime_primes H.hyp.2.1 H.hyp.1).mpr (q_ne_d H).symm)
  have hcyc : IsCyclic (ZMod.unitsMap hf).ker := by
    refine isCyclic_of_injective ((ZMod.unitsMap hq).comp (ZMod.unitsMap hf).ker.subtype) ?_
    rw [injective_iff_map_eq_one]
    rintro ⟨u, hu⟩ h1
    have h2 := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨(mem_ker_iff hf u).mp hu, (mem_ker_iff hq u).mp h1⟩
    rw [mul_right_comm, ← mem_ker_iff dvd_rfl, ZMod.unitsMap_self, MonoidHom.mem_ker, MonoidHom.id_apply] at h2
    exact Subtype.ext h2
  obtain ⟨⟨g, hg⟩, hgen⟩ := hcyc.exists_generator
  have hg2 := H.art_q g ((mem_ker_iff hf g).mp hg)
  have key : ∀ u ∈ KK H.condN (H.QS * H.d), H.art u ≠ 1 → H.art u = H.art g := by
    intro u hu h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨u, (mem_ker_iff hf u).mpr (mem_KK.mp hu)⟩)
    have h2 : g ^ k = u := congrArg Subtype.val hk
    rw [← h2, map_zpow] at h1 ⊢
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · rw [zpow_mul, zpow_ofNat, hg2, one_zpow] at h1
      exact absurd rfl h1
    · rw [zpow_add, zpow_mul, zpow_ofNat, hg2, one_zpow, one_mul, zpow_one]
  refine rho_le_half _ hf fun u hu v hv h1 h2 => ?_
  rw [MonoidHom.mem_ker] at h1 h2 ⊢
  rw [map_mul, key u hu h1, key v hv h2, ← sq, hg2]

end Rd

open Rd

variable {φ : Frame} (H : HostRaw φ)

theorem discr_primes (C : HostCore H) :
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr H.E → p ∣ H.condN) ∧ (2 : ℤ) ∣ discr H.E ∧ (H.d : ℤ) ∣ discr H.E := by
  have := H.galois
  refine ⟨fun p hp h => ?_, ?_, ?_⟩
  · have := cycRat H.condN
    let : Algebra H.E (CyclotomicField H.condN ℚ) := H.cycEmb.toRingHom.toAlgebra
    have h1 := h.trans (discr_dvd_discr H.E (CyclotomicField H.condN ℚ))
    rw [Int.natCast_dvd, IsCyclotomicExtension.Rat.natAbs_discr H.condN] at h1
    exact hp.dvd_of_dvd_pow (h1.trans (Nat.div_dvd_of_dvd (Nat.prod_primeFactors_pow_totient_ediv_dvd H.condN)))
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine dvd_discr_of_inertia Nat.prime_two fun P _ _ => ?_
    obtain ⟨u, hu, h1⟩ := exists_two H
    refine ⟨H.gal.symm (H.art u), fun h2 => h1 (H.gal.symm.map_eq_one_iff.mp h2), ?_⟩
    exact (C.inertia 2 P _).mpr ⟨u, mem_KK.mp hu, H.gal.apply_symm_apply _⟩
  · refine dvd_discr_of_inertia H.hyp.2.1 fun P _ _ => ⟨H.gal.symm φ.iod, fun h2 => ?_,
      (C.inertia_d P _).mpr (Or.inr (H.gal.apply_symm_apply _))⟩
    exact absurd (congrArg (fun g : φ.GG => g.1) (H.gal.symm.map_eq_one_iff.mp h2))
      (show ¬ ((1, -1) : G0) = 1 by decide)

theorem rd_ge (C : HostCore H) : (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) * Real.sqrt H.d ≤ H.rd := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  have h1 := le_SS H.art.ker (two_dvd H) H.hyp.2.1 (dvd_mul_left _ _) (by have := H.hyp.2.2.2.1; omega)
    (fun u hu => hcl_eq_one (by rw [← hH_art, MonoidHom.mem_ker.mp hu]; exact map_one _))
    (by rw [div_d]; exact half_le_rho _ (dvd_mul_right _ _) (exists_d H C))
  rw [← Real.log_le_log_iff (by positivity) (rd_pos H), log_rd_eq, Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by norm_num), Real.log_sqrt hd.le, Real.rpow_neg (by norm_num), Real.rpow_natCast, ← one_div]
  exact h1

theorem rd_le : H.rd ≤ (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d) := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  have hq : (0 : ℝ) < H.q := by exact_mod_cast H.hyp.1.pos
  have hS : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
  have h1 := SS_le H.art.ker ((dvd_pow_self 2 (by omega)).trans (two_dvd H)) H.hyp.1 H.hyp.2.1
    ((dvd_mul_left _ _).mul_right _) (dvd_mul_left _ _) (by have := H.hyp.2.2.1; omega)
    (by have := H.hyp.2.2.2.1; omega) (q_ne_d H) (rho_q H) (rho_d H)
  have hN : Real.log (H.condN : ℝ) = Real.log H.QS + Real.log H.q + Real.log H.d := by
    rw [Nat.cast_mul, Nat.cast_mul, Real.log_mul (by positivity) hd.ne', Real.log_mul hS.ne' hq.ne']
  rw [hN] at h1
  rw [← Real.log_le_log_iff (rd_pos H) (by positivity), log_rd_eq, Real.log_mul (by positivity) (by positivity),
    Real.log_div hS.ne' (by norm_num), Real.log_sqrt (by positivity), Real.log_mul hq.ne' hd.ne']
  linarith

theorem rd_sq_ge (C : HostCore H) : (4 * φ.ord : ℝ) ≤ H.rd ^ 2 := by
  have h1 := log_index_le H.art.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr C.art_surj, Subgroup.card_top, φ.natCard_GG] at h1
  have h0 : (0 : ℝ) < φ.ord := by exact_mod_cast φ.ord_pos
  rw [← Real.log_le_log_iff (by positivity) (pow_pos (rd_pos H) 2), Real.log_pow, log_rd_eq]
  exact_mod_cast h1

end Formalism.HC.Der

end
