module

public import GroundTheory.TateCohomology.InducedNorm

@[expose] public section

section -- merged from GroundTheory.TateCohomology.DimensionShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

section ConnectingIso

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem isIso_δ_of_tateAcyclic {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (h : TateAcyclic S.X₂) (n : ℤ) : IsIso (TateCohomology.δ hS n) := by
  have : Mono (TateCohomology.δ hS n) :=
    (TateCohomology.exact₃ hS n).mono_g ((h n).eq_of_src _ _)
  have : Epi (TateCohomology.δ hS n) :=
    (TateCohomology.exact₁ hS n).epi_f ((h (n + 1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end ConnectingIso

variable {k G : Type u} [CommRing k] [Group G]

section Coind

noncomputable abbrev toCoind (A : Rep.{u} k G) :
    A ⟶ coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) :=
  (resCoindAdjunction k (⊥ : Subgroup G).subtype).unit.app A

theorem toCoind_hom_apply (A : Rep.{u} k G) (a : A) (x : G) :
    ((toCoind A).hom a).1 x = A.ρ x a := rfl

theorem toCoind_injective (A : Rep.{u} k G) : Function.Injective (toCoind A).hom := by
  intro a b hab
  have h : ((toCoind A).hom a).1 1 = ((toCoind A).hom b).1 1 := by rw [hab]
  rwa [toCoind_hom_apply, toCoind_hom_apply, map_one, one_apply_eq_self,
    one_apply_eq_self] at h

instance (A : Rep.{u} k G) : Mono (toCoind A) :=
  (Rep.mono_iff_injective _).2 (toCoind_injective A)

noncomputable def coindSES : Rep.{u} k G ⥤ ShortComplex (Rep.{u} k G) where
  obj A := ShortComplex.mk (toCoind A) (cokernel.π (toCoind A)) (cokernel.condition _)
  map {A B} f :=
    { τ₁ := f
      τ₂ := (resFunctor (⊥ : Subgroup G).subtype ⋙ coindFunctor k (⊥ : Subgroup G).subtype).map f
      τ₃ := cokernel.map (toCoind A) (toCoind B) f _
        ((resCoindAdjunction k (⊥ : Subgroup G).subtype).unit.naturality f).symm
      comm₁₂ := (resCoindAdjunction k (⊥ : Subgroup G).subtype).unit.naturality f
      comm₂₃ := by simp }
  map_id A := by
    refine ShortComplex.hom_ext _ _ rfl ?_ ?_
    · exact (resFunctor (⊥ : Subgroup G).subtype ⋙ coindFunctor k (⊥ : Subgroup G).subtype).map_id A
    · have h : coindMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype (𝟙 A)) = 𝟙 _ :=
        (resFunctor (⊥ : Subgroup G).subtype ⋙ coindFunctor k (⊥ : Subgroup G).subtype).map_id A
      exact coequalizer.hom_ext (by simp [h])
  map_comp f g := by
    refine ShortComplex.hom_ext _ _ rfl ?_ ?_
    · exact (resFunctor (⊥ : Subgroup G).subtype ⋙ coindFunctor k (⊥ : Subgroup G).subtype).map_comp f g
    · have h : coindMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype (f ≫ g)) =
          coindMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype f) ≫
            coindMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype g) :=
        (resFunctor (⊥ : Subgroup G).subtype ⋙ coindFunctor k (⊥ : Subgroup G).subtype).map_comp f g
      exact coequalizer.hom_ext (by simp [h])

@[simp] theorem coindSES_obj_X₁ (A : Rep.{u} k G) : (coindSES.obj A).X₁ = A := rfl

@[simp] theorem coindSES_obj_X₂ (A : Rep.{u} k G) :
    (coindSES.obj A).X₂ = coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) := rfl

theorem coindSES_shortExact (A : Rep.{u} k G) : (coindSES.obj A).ShortExact := by
  change (ShortComplex.cokernelSequence (toCoind A)).ShortExact
  refine ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _) ?_ inferInstance
  change Mono (toCoind A)
  infer_instance

noncomputable abbrev coindShift (A : Rep.{u} k G) : Rep.{u} k G := (coindSES.obj A).X₃

variable [Fintype G]

theorem tateAcyclic_coindSES_X₂ (A : Rep.{u} k G) : TateAcyclic (coindSES.obj A).X₂ :=
  tateAcyclic_coind_bot _

noncomputable def coindShiftIso (A : Rep.{u} k G) (n : ℤ) :
    tateCohomology (coindShift A) n ≅ tateCohomology A (n + 1) :=
  @asIso _ _ _ _ (TateCohomology.δ (coindSES_shortExact A) n)
    (isIso_δ_of_tateAcyclic (coindSES_shortExact A) (tateAcyclic_coindSES_X₂ A) n)

theorem isIso_δ_coindSES (A : Rep.{u} k G) (n : ℤ) :
    IsIso (TateCohomology.δ (coindSES_shortExact A) n) :=
  isIso_δ_of_tateAcyclic _ (tateAcyclic_coindSES_X₂ A) n

end Coind

section Ind

noncomputable abbrev fromInd (A : Rep.{u} k G) :
    ind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) ⟶ A :=
  (indResAdjunction k (⊥ : Subgroup G).subtype).counit.app A

theorem fromInd_surjective (A : Rep.{u} k G) : Function.Surjective (fromInd A).hom := by
  intro a
  refine ⟨Representation.IndV.mk _ _ 1 a, ?_⟩
  change ((indResHomEquiv _ _ _).symm (𝟙 _)).hom _ = a
  simp

instance (A : Rep.{u} k G) : Epi (fromInd A) :=
  (Rep.epi_iff_surjective _).2 (fromInd_surjective A)

noncomputable def indSES : Rep.{u} k G ⥤ ShortComplex (Rep.{u} k G) where
  obj A := ShortComplex.mk (kernel.ι (fromInd A)) (fromInd A) (kernel.condition _)
  map {A B} f :=
    { τ₁ := kernel.map (fromInd A) (fromInd B)
        ((resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map f) f
        ((indResAdjunction k (⊥ : Subgroup G).subtype).counit.naturality f).symm
      τ₂ := (resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map f
      τ₃ := f
      comm₁₂ := by simp
      comm₂₃ := (indResAdjunction k (⊥ : Subgroup G).subtype).counit.naturality f }
  map_id A := by
    refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
    · have h : indMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype (𝟙 A)) = 𝟙 _ :=
        (resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map_id A
      exact equalizer.hom_ext (by simp [h])
    · exact (resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map_id A
  map_comp f g := by
    refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
    · have h : indMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype (f ≫ g)) =
          indMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype f) ≫
            indMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype g) :=
        (resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map_comp f g
      exact equalizer.hom_ext (by simp [h])
    · exact (resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map_comp f g

@[simp] theorem indSES_obj_X₂ (A : Rep.{u} k G) :
    (indSES.obj A).X₂ = ind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) := rfl

@[simp] theorem indSES_obj_X₃ (A : Rep.{u} k G) : (indSES.obj A).X₃ = A := rfl

theorem indSES_shortExact (A : Rep.{u} k G) : (indSES.obj A).ShortExact := by
  change (ShortComplex.kernelSequence (fromInd A)).ShortExact
  refine ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _) inferInstance ?_
  change Epi (fromInd A)
  infer_instance

noncomputable abbrev indShift (A : Rep.{u} k G) : Rep.{u} k G := (indSES.obj A).X₁

variable [Fintype G]

theorem tateAcyclic_indSES_X₂ (A : Rep.{u} k G) : TateAcyclic (indSES.obj A).X₂ :=
  tateAcyclic_ind_bot _

noncomputable def indShiftIso (A : Rep.{u} k G) (n : ℤ) :
    tateCohomology A n ≅ tateCohomology (indShift A) (n + 1) :=
  @asIso _ _ _ _ (TateCohomology.δ (indSES_shortExact A) n)
    (isIso_δ_of_tateAcyclic (indSES_shortExact A) (tateAcyclic_indSES_X₂ A) n)

end Ind

end GroundTheory.GroupCoh
end

section -- merged from GroundTheory.TateCohomology.Herbrand
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

universe u

open CategoryTheory Rep.FiniteCyclicGroup

section CommGroup

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G] (A : Rep.{u} R G) {σ : G}
  (hσ : ∀ x, x ∈ Subgroup.zpowers σ)


include hσ in
theorem invariants_eq_ker_normHomCompSub_g :
    A.ρ.invariants = LinearMap.ker (normHomCompSub A σ).g.hom := by
  ext x
  simpa [Rep.sub_hom, Rep.applyAsHom, sub_eq_zero] using
    Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ σ hσ x

include hσ in
theorem normRangeInvariants_map :
    (normRangeInvariants A).map
        (LinearEquiv.ofEq _ _ (invariants_eq_ker_normHomCompSub_g A hσ) :
          A.ρ.invariants →ₗ[R] LinearMap.ker (normHomCompSub A σ).g.hom) =
      LinearMap.range (normHomCompSub A σ).moduleCatToCycles := by
  ext ⟨y, hy⟩
  rw [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨⟨z, hz⟩, ⟨m, hm⟩, he⟩
    refine ⟨m, Subtype.ext ?_⟩
    have he' := congrArg Subtype.val he
    change (z : A) = y at he'
    change A.ρ.norm m = y
    rw [← he']
    exact hm
  · rintro ⟨m, hm⟩
    have hm' := congrArg Subtype.val hm
    change A.ρ.norm m = y at hm'
    refine ⟨⟨A.ρ.norm m, fun g => Representation.self_norm_apply A.ρ g m⟩, ⟨m, rfl⟩, Subtype.ext ?_⟩
    exact hm'

noncomputable def tateCohomologyZeroIsoHomology :
    tateCohomology A 0 ≅ (normHomCompSub A σ).homology :=
  (tateCohomologyZeroIso (R := R) (G := G)).app A ≪≫
    (Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (invariants_eq_ker_normHomCompSub_g A hσ))
      (normRangeInvariants_map A hσ)).toModuleIso ≪≫
    (normHomCompSub A σ).moduleCatHomologyIso.symm

theorem ker_norm_eq_ker_subCompNormHom_g :
    LinearMap.ker A.ρ.norm = LinearMap.ker (subCompNormHom A σ).g.hom :=
  rfl

include hσ in
theorem augmentationKerNorm_map :
    (augmentationKerNorm A).map
        (LinearEquiv.ofEq _ _ (ker_norm_eq_ker_subCompNormHom_g A (σ := σ)) :
          LinearMap.ker A.ρ.norm →ₗ[R] LinearMap.ker (subCompNormHom A σ).g.hom) =
      LinearMap.range (subCompNormHom A σ).moduleCatToCycles := by
  have hc := Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ σ hσ
  ext ⟨y, hy⟩
  rw [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨⟨z, hz⟩, hzm, he⟩
    have he' := congrArg Subtype.val he
    change (z : A) = y at he'
    rw [mem_augmentationKerNorm_iff, hc] at hzm
    obtain ⟨m, hm⟩ := hzm
    refine ⟨m, Subtype.ext ?_⟩
    change A.ρ σ m - m = y
    rw [← he']
    exact hm
  · rintro ⟨m, hm⟩
    have hm' := congrArg Subtype.val hm
    change A.ρ σ m - m = y at hm'
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    rw [mem_augmentationKerNorm_iff, hc]
    exact ⟨m, hm'⟩

noncomputable def tateCohomologyNegOneIsoHomology :
    tateCohomology A (-1) ≅ (subCompNormHom A σ).homology :=
  (tateCohomologyNegOneIso (R := R) (G := G)).app A ≪≫
    (Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (ker_norm_eq_ker_subCompNormHom_g A))
      (augmentationKerNorm_map A hσ)).toModuleIso ≪≫
    (subCompNormHom A σ).moduleCatHomologyIso.symm

theorem odd_of_even_negSucc {i : ℕ} (h : Even (Int.negSucc i)) : Odd i := by
  rw [Int.negSucc_eq, even_neg, ← Nat.cast_succ, Int.even_coe_nat, Nat.even_add_one] at h
  exact Nat.not_even_iff_odd.1 h

theorem even_of_odd_negSucc {i : ℕ} (h : Odd (Int.negSucc i)) : Even i := by
  rw [Int.negSucc_eq, odd_neg, ← Nat.cast_succ, Int.odd_coe_nat, Nat.odd_add_one] at h
  exact Nat.not_odd_iff_even.1 h

variable [DecidableEq G]

noncomputable def tateCohomologyIsoEven :
    ∀ n : ℤ, Even n → (tateCohomology A n ≅ (normHomCompSub A σ).homology)
  | .ofNat 0, _ => tateCohomologyZeroIsoHomology A hσ
  | .ofNat (i + 1), hn =>
      (TateCohomology.isoGroupCohomology (i + 1)).app A ≪≫
        groupCohomologyIsoEven A σ hσ (i + 1) ((Int.even_coe_nat (i + 1)).1 hn)
  | .negSucc i, hn =>
      haveI : NeZero i := ⟨fun h => by
        have := odd_of_even_negSucc hn
        rw [h] at this
        exact Nat.not_odd_zero this⟩
      (TateCohomology.isoGroupHomology (Int.negSucc i) i (Int.negSucc_eq i)).app A ≪≫
        groupHomologyIsoOdd A σ hσ i (odd_of_even_negSucc hn)

noncomputable def tateCohomologyIsoOdd :
    ∀ n : ℤ, Odd n → (tateCohomology A n ≅ (subCompNormHom A σ).homology)
  | .ofNat 0, hn => absurd hn (by decide)
  | .ofNat (i + 1), hn =>
      (TateCohomology.isoGroupCohomology (i + 1)).app A ≪≫
        groupCohomologyIsoOdd A σ hσ (i + 1) ((Int.odd_coe_nat (i + 1)).1 hn)
  | .negSucc 0, _ => tateCohomologyNegOneIsoHomology A hσ
  | .negSucc (i + 1), hn =>
      (TateCohomology.isoGroupHomology (Int.negSucc (i + 1)) (i + 1)
          (Int.negSucc_eq (i + 1))).app A ≪≫
        groupHomologyIsoEven A σ hσ (i + 1) (even_of_odd_negSucc hn)

noncomputable def tateCohomologyPeriodicIsoOfComm (n : ℤ) :
    tateCohomology A (n + 2) ≅ tateCohomology A n :=
  if h : Even n then
    tateCohomologyIsoEven A hσ (n + 2) (h.add even_two) ≪≫ (tateCohomologyIsoEven A hσ n h).symm
  else
    tateCohomologyIsoOdd A hσ (n + 2) ((Int.not_even_iff_odd.1 h).add_even even_two) ≪≫
      (tateCohomologyIsoOdd A hσ n (Int.not_even_iff_odd.1 h)).symm

end CommGroup

noncomputable def tateCohomologyPeriodicIso {R G : Type u} [CommRing R] [Group G] [Fintype G]
    (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) (n : ℤ) :
    tateCohomology A (n + 2) ≅ tateCohomology A n := by
  classical
  letI : CommGroup G :=
    { (inferInstance : Group G) with
      mul_comm := fun a b => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hσ a)
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hσ b)
        exact zpow_mul_comm σ i j }
  exact tateCohomologyPeriodicIsoOfComm A hσ n

end GroundTheory.GroupCoh
end

section -- merged from GroundTheory.TateCohomology.UniquelyDivisible
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

section UniquelyDivisible

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem tateAcyclic_of_bijective_nsmul (M : Rep.{u} k G)
    (h : Function.Bijective fun m : M => Fintype.card G • m) : TateAcyclic M := by
  let f : M.V →ₗ[k] M.V := Fintype.card G • LinearMap.id
  have hf : ∀ m : M, f m = Fintype.card G • m := fun m => rfl
  have hb : Function.Bijective f := by
    have : (f : M → M) = fun m : M => Fintype.card G • m := funext hf
    rw [this]; exact h
  let e := LinearEquiv.ofBijective f hb
  have he : ∀ m : M, Fintype.card G • e.symm m = m := fun m => by
    rw [← hf]; exact e.apply_symm_apply m
  have hc : ∀ (g : G) (x : M), M.ρ g (e.symm x) = e.symm (M.ρ g x) := by
    intro g x
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    change f (M.ρ g (e.symm x)) = M.ρ g x
    rw [hf, ← map_nsmul, he]
  refine tateAcyclic_of_sum_eq M e.symm.toLinearMap fun m => ?_
  have hg : ∀ g : G, M.ρ g (e.symm.toLinearMap (M.ρ g⁻¹ m)) = e.symm m := fun g => by
    rw [LinearEquiv.coe_coe, hc, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  rw [Finset.sum_congr rfl fun g _ => hg g, Finset.sum_const, Finset.card_univ, he]

theorem isZero_groupCohomology_of_bijective_nsmul (M : Rep.{u} k G)
    (h : Function.Bijective fun m : M => Fintype.card G • m) (n : ℕ) [NeZero n] :
    IsZero (groupCohomology M n) :=
  (tateAcyclic_of_bijective_nsmul M h n).of_iso
    ((TateCohomology.isoGroupCohomology (R := k) (G := G) n).app M).symm

end UniquelyDivisible

section Rat

variable {G : Type} [Group G] [Fintype G]

theorem bijective_nsmul_of_module_rat {V : Type*} [AddCommGroup V] [Module ℚ V] {n : ℕ}
    (hn : n ≠ 0) : Function.Bijective fun v : V => n • v := by
  have : (fun v : V => n • v) = LinearEquiv.smulOfUnit (M := V)
      (IsUnit.unit (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn) : IsUnit (n : ℚ))) := by
    funext v
    change _ = IsUnit.unit (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn) : IsUnit (n : ℚ)) • v
    rw [Units.smul_def, IsUnit.unit_spec, Nat.cast_smul_eq_nsmul]
  rw [this]
  exact LinearEquiv.bijective _

theorem isZero_groupCohomology_trivial_rat (n : ℕ) [NeZero n] :
    IsZero (groupCohomology (Rep.trivial ℤ G ℚ) n) :=
  isZero_groupCohomology_of_bijective_nsmul _
    (bijective_nsmul_of_module_rat (V := ℚ) Fintype.card_ne_zero) n

end Rat

end GroundTheory.GroupCoh
end
