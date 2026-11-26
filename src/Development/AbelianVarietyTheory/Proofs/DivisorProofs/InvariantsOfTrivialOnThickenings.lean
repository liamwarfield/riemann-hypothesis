module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletionGaloisInvariantsAgreeModMaxIdealPow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitApproximationAdicCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitApproximationAdicCompletion
namespace GlobalTheory

theorem finite_alg_hom_ker_coker_killed_of_onto_mod_ideal
    (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (M N : Type) [CommRing M]
    [Algebra A M] [Module.Finite A M] [CommRing N] [Algebra A N] [Module.Finite A N]
    (φ : M →ₐ[A] N) :
    (∀ y : N, ∃ t : M, y - φ t ∈ J.map (algebraMap A N)) →
    (∀ (n : ℕ) (t : M), φ t ∈ (J ^ n).map (algebraMap A N) → t ∈ (J ^ n).map (algebraMap A M)) →
    ∃ f : A, f - 1 ∈ J ∧ (∀ y : N, algebraMap A N f * y ∈ Set.range φ) ∧
      ∀ t : M, φ t = 0 → algebraMap A M f * t = 0 := by
  intro h1 h2

  set R : Submodule A N := LinearMap.range φ.toLinearMap with hR
  have hQ : (⊤ : Submodule A (N ⧸ R)) ≤ J • ⊤ := by
    rintro q -
    obtain ⟨y, rfl⟩ := R.mkQ_surjective q
    obtain ⟨t, ht⟩ := h1 y
    have hz : y - φ t ∈ J • (⊤ : Submodule A N) := by
      rw [Ideal.smul_top_eq_map]; exact ht
    have hm : R.mkQ (y - φ t) ∈ J • (⊤ : Submodule A (N ⧸ R)) := by
      have := Submodule.mem_map_of_mem (f := R.mkQ) hz
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
      exact this
    have he : R.mkQ (y - φ t) = R.mkQ y := by
      rw [map_sub, sub_eq_self, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨t, rfl⟩
    rwa [he] at hm
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J
    (⊤ : Submodule A (N ⧸ R)) (Module.Finite.fg_top) hQ
  have hrR : ∀ y : N, r • y ∈ R := by
    intro y
    have := hr (R.mkQ y) trivial
    rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

  set K : Submodule A M := LinearMap.ker φ.toLinearMap with hK
  have hKfg : K.FG := IsNoetherian.noetherian K
  have hKle : K ≤ J • K := by
    intro t ht
    have hφ : φ t = 0 := ht
    have hmem : t ∈ (⨅ i : ℕ, J ^ i • ⊤ : Submodule A M) := by
      rw [Submodule.mem_iInf]
      intro i
      rw [Ideal.smul_top_eq_map]
      exact h2 i t (by rw [hφ]; exact Ideal.zero_mem _)
    obtain ⟨⟨s, hs⟩, hst⟩ := (J.mem_iInf_smul_pow_eq_bot_iff t).1 hmem
    simp only at hst
    rw [← hst]
    exact Submodule.smul_mem_smul hs ht
  obtain ⟨u, hu1, hu⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J K hKfg hKle
  refine ⟨r * u, ?_, ?_, ?_⟩
  · have : r * u - 1 = r * (u - 1) + (r - 1) := by ring
    rw [this]
    exact J.add_mem (J.mul_mem_left r hu1) hr1
  · intro y
    rw [← Algebra.smul_def, mul_comm, mul_smul]
    obtain ⟨t, ht⟩ := hrR y
    exact ⟨u • t, by
      change φ (u • t) = u • (r • y)
      rw [map_smul]
      congr 1⟩
  · intro t ht
    rw [← Algebra.smul_def, mul_smul, hu t ht, smul_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitApproximationAdicCompletionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_approximation_adic_completion : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (M N : Type) [CommRing M] [Algebra A M] [Module.Finite A M] [CommRing N] [Algebra A N] [Module.Finite A N] (φ : M →ₐ[A] N), (∀ y : N, ∃ t : M, y - φ t ∈ J.map (algebraMap A N)) → (∀ (n : ℕ) (t : M), φ t ∈ (J ^ n).map (algebraMap A N) → t ∈ (J ^ n).map (algebraMap A M)) → ∃ f : A, f - 1 ∈ J ∧ (∀ y : N, algebraMap A N f * y ∈ Set.range φ) ∧ ∀ t : M, φ t = 0 → algebraMap A M f * t = 0 := by
  first | exact @GlobalTheory.finite_alg_hom_ker_coker_killed_of_onto_mod_ideal | exact GlobalTheory.finite_alg_hom_ker_coker_killed_of_onto_mod_ideal | (intros; apply GlobalTheory.finite_alg_hom_ker_coker_killed_of_onto_mod_ideal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeInvariantsFiniteGroupAndFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeInvariantsFiniteGroupAndFinite
namespace GlobalTheory

theorem finiteType_invariants_and_finite (R : Type) [CommRing R] [IsNoetherianRing R]
    (C' : Type) [CommRing C'] [Algebra R C'] [Algebra.FiniteType R C']
    (G : Type) [Group G] [Finite G] (act : G →* (C' ≃ₐ[R] C')) (C : Subalgebra R C')
    (hC : ∀ x, x ∈ C ↔ ∀ σ, act σ x = x) :
    Algebra.FiniteType R C ∧ Module.Finite C C' := by
  letI : MulSemiringAction G C' := MulSemiringAction.compHom C' act
  haveI : Algebra.IsInvariant C C' G := ⟨fun b hb => ⟨⟨b, (hC b).2 fun σ => hb σ⟩, rfl⟩⟩
  haveI : Algebra.IsIntegral C C' := Algebra.IsInvariant.isIntegral C C' G
  haveI : Algebra.FiniteType C C' := Algebra.FiniteType.of_restrictScalars_finiteType R C C'
  haveI hfin : Module.Finite C C' := Algebra.IsIntegral.finite
  refine ⟨⟨fg_of_fg_of_fg (A := R) (B := C) (C := C') Algebra.FiniteType.out
    hfin.fg_top Subtype.val_injective⟩, hfin⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeInvariantsFiniteGroupAndFiniteStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteType_invariants_finite_group_and_finite : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra.FiniteType R C'] (G : Type) [Group G] [Finite G] (act : G →* (C' ≃ₐ[R] C')) (C : Subalgebra R C'), (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C ∧ Module.Finite C C' := by
  first | exact @GlobalTheory.finiteType_invariants_and_finite | exact GlobalTheory.finiteType_invariants_and_finite | (intros; apply GlobalTheory.finiteType_invariants_and_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorQuotientOntoAndInjectiveModIdealPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorQuotientOntoAndInjectiveModIdealPow
namespace GlobalTheory

open TensorProduct


set_option maxHeartbeats 1000000 in
theorem quot_tensor_level : ∀ (R : Type) [CommRing R] (I : Ideal R) (R' : Type) [CommRing R'] [Algebra R R'] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (O : Type) [CommRing O] [Algebra R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (I ^ (e + 1)).map (algebraMap R C')), (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (I ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ (C : Subalgebra R C') (gm : ∀ e : ℕ, (O ⧸ (I ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (I ^ (e + 1)).map (algebraMap R C))), (∀ e (x : O) (c : C), gm e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ c → Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R C')) (c : C') = i e x) → (∀ y : C', ∃ t : TensorProduct R C R', y - Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t ∈ (I.map (algebraMap R C)).map (algebraMap C C')) ∧ ∀ (n : ℕ) (t : TensorProduct R C R'), Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t ∈ ((I.map (algebraMap R C)) ^ n).map (algebraMap C C') → t ∈ ((I.map (algebraMap R C)) ^ n).map (algebraMap C (TensorProduct R C R')) := by
  intro R _ I R' _ _ C' _ _ _ _ O _ _ i hi C gm hcomp

  have hJ : ∀ k : ℕ, ((I.map (algebraMap R C)) ^ k).map (algebraMap C C') =
      (I ^ k).map (algebraMap R C') := by
    intro k
    rw [← Ideal.map_pow, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  set φ := Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C')
    (fun _ _ => Commute.all _ _) with hφ
  have hφt : ∀ (c : C) (r : R'), φ (c ⊗ₜ r) = (c : C') * algebraMap R' C' r := by
    intro c r
    simp [φ, Algebra.TensorProduct.lift_tmul]
  refine ⟨?_, ?_⟩
  · intro y
    have key : ∀ s : O ⊗[R] R', ∃ t : C ⊗[R] R',
        Algebra.TensorProduct.lift (i 0) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C'))
          (fun _ _ => Commute.all _ _) s = Ideal.Quotient.mk _ (φ t) := by
      intro s
      induction s using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | tmul x r =>
        obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (gm 0 (Ideal.Quotient.mk _ x))
        refine ⟨c ⊗ₜ r, ?_⟩
        rw [Algebra.TensorProduct.lift_tmul, hφt, ← hcomp 0 x c hc.symm]
        simp [map_mul]
      | add a b ha hb =>
        obtain ⟨ta, hta⟩ := ha
        obtain ⟨tb, htb⟩ := hb
        exact ⟨ta + tb, by rw [map_add (f := _), hta, htb, map_add (f := _), map_add (f := _)]⟩
    obtain ⟨s, hs⟩ := (hi 0).1 (Ideal.Quotient.mk _ y)
    obtain ⟨t, ht⟩ := key s
    refine ⟨t, ?_⟩
    have h1 := (Ideal.Quotient.eq).1 (hs.symm.trans ht)
    have h2 := hJ 1
    rw [pow_one] at h2
    rw [h2]
    simpa using h1
  · intro n t ht
    cases n with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
      exact Submodule.mem_top
    | succ e =>
    rw [← Ideal.map_pow] at ht ⊢
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at ht
    set K := (I ^ (e + 1)).map (algebraMap R C) with hK
    set πC : C ⊗[R] R' →ₐ[R] (C ⧸ K) ⊗[R] R' :=
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R K) (AlgHom.id R R') with hπC
    have hker : RingHom.ker πC = K.map (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R') := by
      rw [Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective R K)]
      congr 1
      ext a
      simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    have hinc : K.map (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R') =
        K.map (algebraMap C (C ⊗[R] R')) := by
      have : ((Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R') : C →+* C ⊗[R] R') =
          algebraMap C (C ⊗[R] R') := by
        ext c
        simp [Algebra.TensorProduct.algebraMap_apply]
      rw [← this]
      rfl
    have hvan : ∀ a ∈ K, ((Ideal.Quotient.mkₐ R ((I ^ (e + 1)).map (algebraMap R C'))).comp C.val) a = 0 := by
      intro a ha
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      have : (a : C') ∈ K.map (algebraMap C C') := Ideal.mem_map_of_mem _ ha
      rwa [hK, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at this
    set Λ : (C ⧸ K) ⊗[R] R' →ₐ[R] C' ⧸ (I ^ (e + 1)).map (algebraMap R C') :=
      Algebra.TensorProduct.lift (Ideal.Quotient.liftₐ K _ hvan)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _) with hΛ
    have hL : ∀ c : C, Ideal.Quotient.liftₐ K _ hvan (Ideal.Quotient.mk K c) =
        Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R C')) (c : C') := fun c => rfl
    set G : O ⊗[R] R' →ₐ[R] (C ⧸ K) ⊗[R] R' :=
      Algebra.TensorProduct.map ((gm e).toAlgHom.comp (Ideal.Quotient.mkₐ R _)) (AlgHom.id R R') with hG
    have hGs : Function.Surjective G :=
      Algebra.TensorProduct.map_surjective _ _
        ((gm e).surjective.comp (Ideal.Quotient.mkₐ_surjective R _)) Function.surjective_id
    have hΛG : ∀ s, Λ (G s) = Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _) s := by
      intro s
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul x r =>
        obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (gm e (Ideal.Quotient.mk _ x))
        have hc' := hcomp e x c hc.symm
        simp only [G, Λ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
        show Ideal.Quotient.liftₐ K _ hvan (gm e (Ideal.Quotient.mk _ x)) * _ = _
        rw [← hc, ← hc']
        congr 1
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]
    have hΛπ' : Λ.comp πC = (Ideal.Quotient.mkₐ R _).comp (φ.restrictScalars R) := by
      refine Algebra.TensorProduct.ext' fun c r => ?_
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, πC, Λ, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.lift_tmul, hφt]
      rw [map_mul]
      congr 1
    have hΛπ : ∀ u, Λ (πC u) = Ideal.Quotient.mk _ (φ u) := fun u => by
      have := congrArg (fun f => f u) hΛπ'
      simpa using this
    obtain ⟨s, hs⟩ := hGs (πC t)
    have hs0 : s ∈ RingHom.ker (Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _)) := by
      rw [RingHom.mem_ker, ← hΛG, hs, hΛπ, Ideal.Quotient.eq_zero_iff_mem]
      exact ht
    rw [(hi e).2] at hs0
    have hGz : G s = 0 := by
      have hle : (I ^ (e + 1)).map (algebraMap R (O ⊗[R] R')) ≤ RingHom.ker G.toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
          IsScalarTower.algebraMap_apply R (C ⧸ K) ((C ⧸ K) ⊗[R] R'), ← Ideal.Quotient.mk_algebraMap,
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha), map_zero]
      exact hle hs0
    rw [← hinc, ← hker, RingHom.mem_ker, ← hs, hGz]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorQuotientOntoAndInjectiveModIdealPowStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_quotient_onto_and_injective_mod_ideal_pow : ∀ (R : Type) [CommRing R] (I : Ideal R) (R' : Type) [CommRing R'] [Algebra R R'] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (O : Type) [CommRing O] [Algebra R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (I ^ (e + 1)).map (algebraMap R C')), (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (I ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ (C : Subalgebra R C') (gm : ∀ e : ℕ, (O ⧸ (I ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (I ^ (e + 1)).map (algebraMap R C))), (∀ e (x : O) (c : C), gm e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ c → Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R C')) (c : C') = i e x) → (∀ y : C', ∃ t : TensorProduct R C R', y - Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t ∈ (I.map (algebraMap R C)).map (algebraMap C C')) ∧ ∀ (n : ℕ) (t : TensorProduct R C R'), Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t ∈ ((I.map (algebraMap R C)) ^ n).map (algebraMap C C') → t ∈ ((I.map (algebraMap R C)) ^ n).map (algebraMap C (TensorProduct R C R')) := by
  first | exact @GlobalTheory.quot_tensor_level | exact GlobalTheory.quot_tensor_level | (intros; apply GlobalTheory.quot_tensor_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantsOfTrivialOnThickenings
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.InvAlg

theorem invariants_of_trivial_on_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] [Algebra.FiniteType R' C'] (act : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')), (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) → ∀ (O : Type) [CommRing O] [Algebra R O] [Module.Flat R O] [Algebra.FiniteType R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C')), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ C : Subalgebra R C', (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C ∧ Module.Finite C C' ∧ ∃ f : C, f - 1 ∈ (maximalIdeal R).map (algebraMap R C) ∧ (∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _)) ∧ (∀ t : TensorProduct R C R', Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) ∧ ∀ e, Nonempty ((O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C))) := by
  intro R _ _ _ hR R' _ _ _ _ hinj hGal C' _ _ _ _ _ act hact O _ _ _ _ i hi1 hi2 hi3 C hC
  haveI : IsNoetherianRing R := hR.1
  haveI : Finite (Gal (algebraMap R R')) := hGal.1
  haveI : Algebra.FiniteType R C' := Algebra.FiniteType.trans (S := R') inferInstance inferInstance
  obtain ⟨hft, hfin⟩ := GlobalTheory.T.finiteType_invariants_finite_group_and_finite R C' (Gal (algebraMap R R')) act C hC
  have hg := GlobalTheory.T.completion_galoisInvariants_agree_mod_maxIdeal_pow R hR R' hinj hGal C' act hact O i hi1 hi2 hi3 C hC hft hfin
  choose gm hgc using hg
  obtain ⟨hs, hinj'⟩ := GlobalTheory.T.tensor_quotient_onto_and_injective_mod_ideal_pow R (maximalIdeal R) R' C' O i hi3 C gm hgc
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing R C
  obtain ⟨f, hf1, hf2, hf3⟩ := GlobalTheory.T.exists_unit_approximation_adic_completion C ((maximalIdeal R).map (algebraMap R C)) (TensorProduct R C R') C' _ hs hinj'
  have hL : ∀ t, Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t = Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  refine ⟨hft, hfin, f, hf1, fun x => ⟨1, ?_⟩, fun t ht => ⟨1, ?_⟩, fun e => ⟨gm e⟩⟩
  · obtain ⟨t, ht⟩ := hf2 x
    exact ⟨t, by rw [← hL]; simpa using ht⟩
  · have := hf3 t (by rw [hL]; exact ht)
    rw [pow_one]
    rwa [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at this

end GlobalTheory.InvAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantsOfTrivialOnThickeningsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariants_of_trivial_on_thickenings_alt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] [Algebra.FiniteType R' C'] (act : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')), (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) → ∀ (O : Type) [CommRing O] [Algebra R O] [Module.Flat R O] [Algebra.FiniteType R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C')), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ C : Subalgebra R C', (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C ∧ Module.Finite C C' ∧ ∃ f : C, f - 1 ∈ (maximalIdeal R).map (algebraMap R C) ∧ (∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _)) ∧ (∀ t : TensorProduct R C R', Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) ∧ ∀ e, Nonempty ((O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C))) := by
  first | exact @GlobalTheory.InvAlg.invariants_of_trivial_on_thickenings | exact GlobalTheory.InvAlg.invariants_of_trivial_on_thickenings | (intros; apply GlobalTheory.InvAlg.invariants_of_trivial_on_thickenings <;> assumption)
end
