module

public import GroundTheory.ProfiniteCohomology.RealPlaces.OrderTwoTate
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalInvariants
public import GroundTheory.ProfiniteCohomology.LocalTateDuality.InjectiveCohomologyMapKummerSeqOpenFTwo

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.RealPlaces.LocalDuality
section -- merged from GroundTheory.ProfiniteCohomology.RealPlaces.LocalDualityCup
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Involution OrderTwo

attribute [local instance 2000] Rep.hV2

section Transfer

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F))
  {n : ℕ} [NeZero n] (hMn : ∀ m : M, n • m = 0) (e : galRootsOfUnity.{0} F Ω n ≃+ ZMod n)

def cartierDualRoots : cartierDual F Ω M →+ (M →+ galRootsOfUnity.{0} F Ω n) :=
  (uliftIntLinearEquivAddHom M (galRootsOfUnity.{0} F Ω n)).toAddMonoidHom.comp
    (cartierDualIsoHomRootsOfUnityOfNsmul F Ω M n hMn).inv.hom.toLinearMap.toAddMonoidHom

omit [NeZero n] in
theorem rootsOfUnityToUnits_cartierDualRoots (φ : cartierDual F Ω M) (m : M) :
    (rootsOfUnityToUnits F Ω n).hom (cartierDualRoots M hMn φ m) =
      (φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) m := by
  have h := cartierDualIsoHomRootsOfUnityOfNsmul_hom_apply M n hMn
    ((cartierDualIsoHomRootsOfUnityOfNsmul F Ω M n hMn).inv.hom φ) m
  have hi := congrArg (fun f => (f.hom φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) m)
    (cartierDualIsoHomRootsOfUnityOfNsmul F Ω M n hMn).inv_hom_id
  exact h.symm.trans hi

def cartierDualToQZ : cartierDual F Ω M →+ (M →+ QZ) :=
  (AddMonoidHom.compHom ((zmodToQZ n).comp e.toAddMonoidHom)).comp (cartierDualRoots M hMn)

omit [NeZero n] in
theorem cartierDualToQZ_apply (φ : cartierDual F Ω M) (m : M) :
    cartierDualToQZ M hMn e φ m = zmodToQZ n (e (cartierDualRoots M hMn φ m)) :=
  rfl

theorem cartierDualToQZ_apply_eq_zero_iff (φ : cartierDual F Ω M) (m : M) :
    cartierDualToQZ M hMn e φ m = 0 ↔ (φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) m = 0 := by
  rw [cartierDualToQZ_apply, ← rootsOfUnityToUnits_cartierDualRoots M hMn,
    ← map_zero (zmodToQZ n), (zmodToQZ_injective (n := n)).eq_iff, ← map_zero e,
    e.injective.eq_iff, ← map_zero (rootsOfUnityToUnits F Ω n).hom,
    (rootsOfUnityToUnits_injective n).eq_iff]

theorem cartierDualToQZ_injective : Function.Injective (cartierDualToQZ M hMn e) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro φ hφ
  apply LinearMap.ext
  intro m
  exact (cartierDualToQZ_apply_eq_zero_iff M hMn e φ m).1 (DFunLike.congr_fun hφ m)

theorem cartierDualToQZ_surjective : Function.Surjective (cartierDualToQZ M hMn e) := by
  intro f
  have hf : ∀ m, n • f m = 0 := fun m => by rw [← map_nsmul, hMn, map_zero]
  let ψ : M →ₗ[ULift.{0} ℤ] galRootsOfUnity.{0} F Ω n :=
    (uliftIntLinearEquivAddHom M (galRootsOfUnity.{0} F Ω n)).symm
      (e.symm.toAddMonoidHom.comp (zmodOfQZ f hf))
  refine ⟨(cartierDualIsoHomRootsOfUnityOfNsmul F Ω M n hMn).hom.hom
    (show (Rep.ihom M).obj (galRootsOfUnity.{0} F Ω n) from ψ), ?_⟩
  ext m
  rw [cartierDualToQZ_apply]
  have hi := congrArg (fun g => (g.hom (show (Rep.ihom M).obj (galRootsOfUnity.{0} F Ω n) from ψ) :
      M →ₗ[ULift.{0} ℤ] galRootsOfUnity.{0} F Ω n) m)
    (cartierDualIsoHomRootsOfUnityOfNsmul F Ω M n hMn).hom_inv_id
  have h : cartierDualRoots M hMn ((cartierDualIsoHomRootsOfUnityOfNsmul F Ω M n hMn).hom.hom
      (show (Rep.ihom M).obj (galRootsOfUnity.{0} F Ω n) from ψ)) m = ψ m := hi
  rw [h]
  change zmodToQZ n (e (e.symm (zmodOfQZ f hf m))) = f m
  rw [e.apply_symm_apply, zmodToQZ_zmodOfQZ]

def cartierDualEquivQZ : cartierDual F Ω M ≃+ (M →+ QZ) :=
  AddEquiv.ofBijective (cartierDualToQZ M hMn e)
    ⟨cartierDualToQZ_injective M hMn e, cartierDualToQZ_surjective M hMn e⟩

end Transfer

section Equivariance

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F))
  {n : ℕ} [NeZero n] (hMn : ∀ m : M, n • m = 0) (e : galRootsOfUnity.{0} F Ω n ≃+ ZMod n)


omit [NeZero n] in
theorem cartierDualToQZ_act {c : Gal(Ω/F)} (hinv : c⁻¹ = c)
    (hconj : ∀ ζ : galUnits.{0} F Ω, n • ζ = 0 → (galUnits.{0} F Ω).ρ c ζ = -ζ)
    (φ : cartierDual F Ω M) :
    cartierDualToQZ M hMn e ((cartierDual F Ω M).ρ c φ) =
      dualInv (act M c) (cartierDualToQZ M hMn e φ) := by
  ext m
  rw [dualInv_apply, cartierDualToQZ_apply, cartierDualToQZ_apply, ← map_neg, ← map_neg]
  congr 2
  apply rootsOfUnityToUnits_injective n
  rw [map_neg, rootsOfUnityToUnits_cartierDualRoots, rootsOfUnityToUnits_cartierDualRoots,
    cartierDual_ρ_apply, hinv]
  apply hconj
  rw [← map_nsmul, hMn, map_zero]

end Equivariance

namespace QZ

theorem eq_mk_half_of_two_nsmul {q : QZ} (hq : 2 • q = 0) (hq0 : q ≠ 0) : q = QZ.mk (1 / 2) := by
  obtain ⟨m, hm⟩ := QZ.exists_eq_nsmul_mk_one_div (by norm_num) hq
  rw [hm] at hq0 ⊢
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · exfalso
    apply hq0
    rw [mul_nsmul]
    have := QZ.nsmul_mk_one_div 2
    rw [this, nsmul_zero]
  · rw [add_nsmul, one_nsmul, mul_nsmul]
    have := QZ.nsmul_mk_one_div 2
    rw [this, nsmul_zero, zero_add]
    norm_num

end QZ

section Invariant

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (h2 : Module.finrank F Ω ≤ 2)
  (hN : ∀ a b : Fˣ, (a : F) ∉ Set.range (Algebra.norm F : Ω → F) →
    (b : F) ∉ Set.range (Algebra.norm F : Ω → F) →
      ((a * b : Fˣ) : F) ∈ Set.range (Algebra.norm F : Ω → F))
  {c : Gal(Ω/F)} (hG : ∀ g : Gal(Ω/F), g = 1 ∨ g = c) (hc : c ≠ 1)
  (hneg : (-1 : F) ∉ Set.range (Algebra.norm F : Ω → F))


include hneg in
theorem realInv_cocycleTwo (t : galUnits.{0} F Ω) (ht : (galUnits.{0} F Ω).ρ c t = t)
    (h2t : 2 • t = 0) (q : QZ) (hq : 2 • q = 0) (hqt : q = 0 ↔ t = 0) :
    realInv F Ω h2 hN (cohomologyπ _ 2 (cocycleTwo (galUnits.{0} F Ω) hG hc t ht)) = q := by
  by_cases ht0 : t = 0
  · have hz : cohomologyπ _ 2 (cocycleTwo (galUnits.{0} F Ω) hG hc t ht) = 0 := by
      rw [cohomologyπ_cocycleTwo_eq_zero_iff]
      exact ⟨0, by rw [ht0, map_zero, add_zero]⟩
    rw [hz, map_zero, hqt.2 ht0]
  · have hq0 : q ≠ 0 := fun h => ht0 (hqt.1 h)
    rw [QZ.eq_mk_half_of_two_nsmul hq hq0]
    have hne : cohomologyπ _ 2 (cocycleTwo (galUnits.{0} F Ω) hG hc t ht) ≠ 0 := by
      rw [Ne, cohomologyπ_cocycleTwo_eq_zero_iff]
      rintro ⟨m, hm⟩
      have hu : ((Additive.toMul t : Ωˣ) : Ω) = -1 := by
        have hsq : ((Additive.toMul t : Ωˣ) : Ω) * ((Additive.toMul t : Ωˣ) : Ω) = 1 := by
          rw [← Units.val_mul, ← toMul_add, ← two_nsmul, h2t, toMul_zero, Units.val_one]
        rcases mul_self_eq_one_iff.1 hsq with h | h
        · exfalso
          apply ht0
          apply Additive.toMul.injective
          exact Units.ext h
        · exact h
      have hnorm := coe_toMul_norm_galUnitsZ F Ω m
      rw [norm_apply (galUnitsZ F Ω) hG hc] at hnorm
      change ((Additive.toMul (m + (galUnits.{0} F Ω).ρ c m) : Ωˣ) : Ω) = _ at hnorm
      rw [← hm, hu, ← map_one (algebraMap F Ω), ← map_neg] at hnorm
      exact hneg ⟨_, ((algebraMap F Ω).injective hnorm).symm⟩
    rw [realInv_apply]
    exact quadraticInvFun_of_ne_zero F Ω
      ((AddEquiv.map_ne_zero_iff (cohomologyULiftIntAddEquiv (galUnits.{0} F Ω) 2)).2 hne)

end Invariant

section Congr

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] {c : G} (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)

theorem cohomologyπ_cocycleTwo_congr (A : Rep.{0} k G) [IsDiscreteRep A]
    {a b : A} (ha : A.ρ c a = a) (hb : A.ρ c b = b) (hab : a = b) :
    cohomologyπ A 2 (cocycleTwo A hG hc a ha) = cohomologyπ A 2 (cocycleTwo A hG hc b hb) := by
  subst hab
  rfl

end Congr

section Cup

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M]
  {c : Gal(Ω/F)} (hG : ∀ g : Gal(Ω/F), g = 1 ∨ g = c) (hc : c ≠ 1)


omit [FiniteDimensional F Ω] in
theorem cochainOf_cupCartier {p q : ℕ} (h : p + q = 2) (x : cocycles M p)
    (y : cocycles (cartierDual F Ω M) q) (s : Fin 2 → Gal(Ω/F)) :
    cochainOf _ (cocycleι _ 2 (HomologicalComplex.cyclesMap (cochainsMap (cartierPairing F Ω M)) 2
        (cupCocycles h x y))) s =
      ((((cartierDual F Ω M).ρ (Fin.partialProd s ⟨p, by omega⟩)
          (cochainOf _ (cocycleι _ q y) fun j : Fin q => s ⟨p + j, by omega⟩)) :
        M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) (cochainOf M (cocycleι M p x) fun i : Fin p => s ⟨i, by omega⟩)) := by
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, cartierPairing_tmul]

theorem cupPairing_cocycleOne (α : M) (hα : α + M.ρ c α = 0) (β : cartierDual F Ω M)
    (hβ : β + (cartierDual F Ω M).ρ c β = 0) :
    ∃ ht, cupPairing (cartierPairing F Ω M) (show 1 + 1 = 2 from rfl)
        (cohomologyπ M 1 (cocycleOne M hG hc α hα))
        (cohomologyπ _ 1 (cocycleOne (cartierDual F Ω M) hG hc β hβ)) =
      cohomologyπ _ 2 (cocycleTwo (galUnits.{0} F Ω) hG hc
        ((((cartierDual F Ω M).ρ c β) : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) α) ht) := by
  set z := HomologicalComplex.cyclesMap (cochainsMap (cartierPairing F Ω M)) 2
    (cupCocycles (show 1 + 1 = 2 from rfl) (cocycleOne M hG hc α hα)
      (cocycleOne (cartierDual F Ω M) hG hc β hβ)) with hz
  have hval : ∀ g h : Gal(Ω/F), cochainOf _ (cocycleι _ 2 z) ![g, h] =
      ((((cartierDual F Ω M).ρ g) (cochainOne (cartierDual F Ω M) β ![h])) :
        M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) (cochainOne M α ![g]) := by
    intro g h
    rw [hz, cochainOf_cupCartier, cochainOf_cocycleOne, cochainOf_cocycleOne]
    have e1 : (fun j : Fin 1 => (![g, h] : Fin 2 → Gal(Ω/F)) ⟨1 + j, by omega⟩) = ![h] := by
      funext j; fin_cases j; rfl
    have e2 : (fun i : Fin 1 => (![g, h] : Fin 2 → Gal(Ω/F)) ⟨i, by omega⟩) = ![g] := by
      funext i; fin_cases i; rfl
    have e3 : Fin.partialProd (![g, h] : Fin 2 → Gal(Ω/F)) ⟨1, by omega⟩ = g := by
      simp [Fin.partialProd]
    rw [e1, e2, e3]
  obtain ⟨ht, hzt⟩ := exists_eq_cocycleTwo_of_normalized (galUnits.{0} F Ω) hG hc z
    (fun g => by rw [hval, cochainOne_one, map_zero])
    (fun g => by rw [hval, cochainOne_one, map_zero, LinearMap.zero_apply])
  have hcc : cochainOf _ (cocycleι _ 2 z) ![c, c] =
      ((((cartierDual F Ω M).ρ c β) : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) α) := by
    rw [hval, cochainOne_c _ hc, cochainOne_c _ hc]
  refine ⟨hcc ▸ ht, ?_⟩
  rw [cupPairing_cohomologyπ, ← hz]
  exact (congrArg (cohomologyπ _ 2).hom hzt).trans (cohomologyπ_cocycleTwo_congr hG hc _ _ _ hcc)

end Cup

section Cup2

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M]
  {c : Gal(Ω/F)} (hG : ∀ g : Gal(Ω/F), g = 1 ∨ g = c) (hc : c ≠ 1)

theorem cupPairing_cocycleTwo_H0 (a : M) (ha : M.ρ c a = a)
    (φ : (cartierDual F Ω M).ρ.invariants) :
    ∃ ht, cupPairing (cartierPairing F Ω M) (show 2 + 0 = 2 from rfl)
        (cohomologyπ M 2 (cocycleTwo M hG hc a ha)) ((H0Iso (cartierDual F Ω M)).inv.hom φ) =
      cohomologyπ _ 2 (cocycleTwo (galUnits.{0} F Ω) hG hc
        (((φ : cartierDual F Ω M) : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) a) ht) := by
  obtain ⟨z0, hz0, hz0c⟩ := exists_cocycle_H0Iso_inv (cartierDual F Ω M) φ
  rw [← hz0]
  set z := HomologicalComplex.cyclesMap (cochainsMap (cartierPairing F Ω M)) 2
    (cupCocycles (show 2 + 0 = 2 from rfl) (cocycleTwo M hG hc a ha) z0) with hz
  have hval : ∀ g h : Gal(Ω/F), cochainOf _ (cocycleι _ 2 z) ![g, h] =
      (((φ : cartierDual F Ω M) : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) (cochainTwo M c a ![g, h])) := by
    intro g h
    rw [hz, cochainOf_cupCartier, cochainOf_cocycleTwo, hz0c, φ.2]
  obtain ⟨ht, hzt⟩ := exists_eq_cocycleTwo_of_normalized (galUnits.{0} F Ω) hG hc z
    (fun g => by rw [hval, cochainTwo_one_left M hc, map_zero])
    (fun g => by rw [hval, cochainTwo_one_right M hc, map_zero])
  have hcc : cochainOf _ (cocycleι _ 2 z) ![c, c] =
      (((φ : cartierDual F Ω M) : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) a) := by
    rw [hval, cochainTwo_cc]
  refine ⟨hcc ▸ ht, ?_⟩
  rw [cupPairing_cohomologyπ, ← hz]
  exact (congrArg (cohomologyπ _ 2).hom hzt).trans (cohomologyπ_cocycleTwo_congr hG hc _ _ _ hcc)

theorem cupPairing_H0_cocycleTwo (a : M.ρ.invariants) (φ : cartierDual F Ω M)
    (hφ : (cartierDual F Ω M).ρ c φ = φ) :
    ∃ ht, cupPairing (cartierPairing F Ω M) (show 0 + 2 = 2 from rfl)
        ((H0Iso M).inv.hom a) (cohomologyπ _ 2 (cocycleTwo (cartierDual F Ω M) hG hc φ hφ)) =
      cohomologyπ _ 2 (cocycleTwo (galUnits.{0} F Ω) hG hc
        ((φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) (a : M)) ht) := by
  obtain ⟨z0, hz0, hz0c⟩ := exists_cocycle_H0Iso_inv M a
  rw [← hz0]
  set z := HomologicalComplex.cyclesMap (cochainsMap (cartierPairing F Ω M)) 2
    (cupCocycles (show 0 + 2 = 2 from rfl) z0 (cocycleTwo (cartierDual F Ω M) hG hc φ hφ)) with hz
  have hval : ∀ g h : Gal(Ω/F), cochainOf _ (cocycleι _ 2 z) ![g, h] =
      ((cochainTwo (cartierDual F Ω M) c φ ![g, h] : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) (a : M)) := by
    intro g h
    rw [hz, cochainOf_cupCartier, cochainOf_cocycleTwo, hz0c]
    have e1 : (fun j : Fin 2 => (![g, h] : Fin 2 → Gal(Ω/F)) ⟨0 + j, by omega⟩) = ![g, h] := by
      funext j; fin_cases j <;> rfl
    have e3 : Fin.partialProd (![g, h] : Fin 2 → Gal(Ω/F)) ⟨0, by omega⟩ = 1 := by
      simp [Fin.partialProd]
    rw [e1, e3, map_one, Module.End.one_apply]
  obtain ⟨ht, hzt⟩ := exists_eq_cocycleTwo_of_normalized (galUnits.{0} F Ω) hG hc z
    (fun g => by rw [hval, cochainTwo_one_left _ hc, LinearMap.zero_apply])
    (fun g => by rw [hval, cochainTwo_one_right _ hc, LinearMap.zero_apply])
  have hcc : cochainOf _ (cocycleι _ 2 z) ![c, c] =
      ((φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) (a : M)) := by
    rw [hval, cochainTwo_cc]
  refine ⟨hcc ▸ ht, ?_⟩
  rw [cupPairing_cohomologyπ, ← hz]
  exact (congrArg (cohomologyπ _ 2).hom hzt).trans (cohomologyπ_cocycleTwo_congr hG hc _ _ _ hcc)

end Cup2

end GroundTheory.ProfCoh
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Involution OrderTwo

attribute [local instance 2000] Rep.hV2

section Neg

variable {M : Type*} [AddCommGroup M]

theorem Involution.dualInv_neg (σ : M →+ M) (f : M →+ QZ) : dualInv (-σ) f = -dualInv σ f := by
  ext x
  simp

end Neg

section Generic

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (h2 : Module.finrank F Ω ≤ 2)
  (hN : ∀ a b : Fˣ, (a : F) ∉ Set.range (Algebra.norm F : Ω → F) →
    (b : F) ∉ Set.range (Algebra.norm F : Ω → F) →
      ((a * b : Fˣ) : F) ∈ Set.range (Algebra.norm F : Ω → F))
  {c : Gal(Ω/F)} (hG : ∀ g : Gal(Ω/F), g = 1 ∨ g = c) (hc : c ≠ 1)
  (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M]


include hG hc in
theorem realDualityPairing_two_zero_eq_zero (x : cohomology M 2)
    (y : cohomology (cartierDual F Ω M) 0) (hy : y ∈ normClasses (cartierDual F Ω M)) :
    realDualityPairing F Ω h2 hN M (show 2 + 0 = 2 from rfl) x y = 0 := by
  obtain ⟨b, hb, rfl⟩ := (mem_normClasses_iff _ y).1 hy
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective M 2 x
  obtain ⟨a, ha, e⟩ := exists_cohomologyπ_eq_cocycleTwo M hG hc z
  rw [e, realDualityPairing_apply]
  obtain ⟨ht, hcup⟩ := cupPairing_cocycleTwo_H0 M hG hc a ha ⟨_, hb⟩
  rw [hcup]
  convert map_zero (realInv F Ω h2 hN)
  rw [cohomologyπ_cocycleTwo_eq_zero_iff]
  refine ⟨(b : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) a, ?_⟩
  change ((((cartierDual F Ω M).ρ.norm b) : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) a) = _
  rw [norm_apply _ hG hc, LinearMap.add_apply, cartierDual_ρ_apply, inv_eq_self hG hc, ha]


include hG hc in
theorem realDualityPairing_zero_two_eq_zero (x : cohomology M 0) (hx : x ∈ normClasses M)
    (y : cohomology (cartierDual F Ω M) 2) :
    realDualityPairing F Ω h2 hN M (show 0 + 2 = 2 from rfl) x y = 0 := by
  obtain ⟨b, hb, rfl⟩ := (mem_normClasses_iff _ x).1 hx
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 2 y
  obtain ⟨φ, hφ, e⟩ := exists_cohomologyπ_eq_cocycleTwo _ hG hc z
  rw [e, realDualityPairing_apply]
  obtain ⟨ht, hcup⟩ := cupPairing_H0_cocycleTwo M hG hc ⟨_, hb⟩ φ hφ
  rw [hcup]
  convert map_zero (realInv F Ω h2 hN)
  rw [cohomologyπ_cocycleTwo_eq_zero_iff]
  refine ⟨(φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) b, ?_⟩
  have hφb : (φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) (M.ρ c b) =
      (galUnits.{0} F Ω).ρ c ((φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) b) := by
    conv_lhs => rw [← hφ]
    rw [cartierDual_ρ_apply, inv_eq_self hG hc, ← Module.End.mul_apply, ← map_mul,
      mul_self_eq_one hG hc, map_one, Module.End.one_apply]
  change (φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) (M.ρ.norm b) = _
  rw [norm_apply _ hG hc, map_add (f := _), hφb]

end Generic

section Lifted

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (h2 : Module.finrank F Ω ≤ 2)
  (hN : ∀ a b : Fˣ, (a : F) ∉ Set.range (Algebra.norm F : Ω → F) →
    (b : F) ∉ Set.range (Algebra.norm F : Ω → F) →
      ((a * b : Fˣ) : F) ∈ Set.range (Algebra.norm F : Ω → F))
  {c : Gal(Ω/F)} (hG : ∀ g : Gal(Ω/F), g = 1 ∨ g = c) (hc : c ≠ 1)
  (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M]

def realDualityPairingTwoZero :
    cohomology M 2 →+ cohomologyTateZero (cartierDual F Ω M) →+ QZ where
  toFun x := QuotientAddGroup.lift (normClasses (cartierDual F Ω M)).toAddSubgroup
    (realDualityPairing F Ω h2 hN M (show 2 + 0 = 2 from rfl) x)
    (fun y hy => realDualityPairing_two_zero_eq_zero h2 hN hG hc M x y hy)
  map_zero' := by
    refine DFunLike.ext _ _ fun y => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact DFunLike.congr_fun (map_zero (realDualityPairing F Ω h2 hN M (show 2 + 0 = 2 from rfl))) y
  map_add' x x' := by
    refine DFunLike.ext _ _ fun y => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact DFunLike.congr_fun (map_add (realDualityPairing F Ω h2 hN M (show 2 + 0 = 2 from rfl)) x x') y

theorem realDualityPairingTwoZero_mk (x : cohomology M 2) (y : cohomology (cartierDual F Ω M) 0) :
    realDualityPairingTwoZero h2 hN hG hc M x (Submodule.Quotient.mk y) =
      realDualityPairing F Ω h2 hN M (show 2 + 0 = 2 from rfl) x y :=
  rfl

def realDualityPairingZeroTwo :
    cohomologyTateZero M →+ cohomology (cartierDual F Ω M) 2 →+ QZ :=
  QuotientAddGroup.lift (normClasses M).toAddSubgroup
    (realDualityPairing F Ω h2 hN M (show 0 + 2 = 2 from rfl))
    (fun x hx => by
      ext y
      exact realDualityPairing_zero_two_eq_zero h2 hN hG hc M x hx y)

theorem realDualityPairingZeroTwo_mk (x : cohomology M 0) (y : cohomology (cartierDual F Ω M) 2) :
    realDualityPairingZeroTwo h2 hN hG hc M (Submodule.Quotient.mk x) y =
      realDualityPairing F Ω h2 hN M (show 0 + 2 = 2 from rfl) x y :=
  rfl

end Lifted

section Duality

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (h2 : Module.finrank F Ω ≤ 2)
  (hN : ∀ a b : Fˣ, (a : F) ∉ Set.range (Algebra.norm F : Ω → F) →
    (b : F) ∉ Set.range (Algebra.norm F : Ω → F) →
      ((a * b : Fˣ) : F) ∈ Set.range (Algebra.norm F : Ω → F))
  {c : Gal(Ω/F)} (hG : ∀ g : Gal(Ω/F), g = 1 ∨ g = c) (hc : c ≠ 1)
  (hneg : (-1 : F) ∉ Set.range (Algebra.norm F : Ω → F))
  (hconj : ∀ ζ : galUnits.{0} F Ω, (∃ k : ℕ, 0 < k ∧ k • ζ = 0) → (galUnits.{0} F Ω).ρ c ζ = -ζ)
  (hroots : ∀ k : ℕ, 0 < k → Nonempty (galRootsOfUnity.{0} F Ω k ≃+ ZMod k))
  (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M]


omit [IsDiscreteRep M] [Finite M] in
include hneg in
theorem realInv_cocycleTwo_eq_cartierDualToQZ {n : ℕ} [NeZero n] (hMn : ∀ m : M, n • m = 0)
    (e : galRootsOfUnity.{0} F Ω n ≃+ ZMod n) (φ : cartierDual F Ω M) (m : M)
    (hq : 2 • cartierDualToQZ M hMn e φ m = 0) (t : galUnits.{0} F Ω)
    (htφ : t = (φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) m ∨
      t = -(φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) m)
    (ht : (galUnits.{0} F Ω).ρ c t = t) :
    realInv F Ω h2 hN (cohomologyπ _ 2 (cocycleTwo (galUnits.{0} F Ω) hG hc t ht)) =
      cartierDualToQZ M hMn e φ m := by
  have h2φ : 2 • (φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) m = 0 := by
    rw [← map_nsmul, ← cartierDualToQZ_apply_eq_zero_iff M hMn e, map_nsmul]
    exact hq
  have ht0 : t = 0 ↔ (φ : M →ₗ[ULift.{0} ℤ] galUnits.{0} F Ω) m = 0 := by
    rcases htφ with rfl | rfl
    · rfl
    · exact neg_eq_zero
  refine realInv_cocycleTwo h2 hN hG hc hneg t ht ?_ _ hq ?_
  · rcases htφ with rfl | rfl
    · exact h2φ
    · rw [two_nsmul] at h2φ ⊢
      rw [← neg_add, h2φ, neg_zero]
  · rw [ht0]
    exact cartierDualToQZ_apply_eq_zero_iff M hMn e φ m


include hneg hconj hroots in
theorem realDualityPairingTwoZero_eq_tatePair :
    ∃ (e : tateQuot (act M c) ≃+ cohomology M 2)
      (e' : tateQuot (dualInv (act M c)) ≃+ cohomologyTateZero (cartierDual F Ω M)),
      ∀ x y, realDualityPairingTwoZero h2 hN hG hc M (e x) (e' y) = tatePair (act M c) x y := by
  have : NeZero (Nat.card M) := ⟨Nat.card_pos.ne'⟩
  have hMn : ∀ m : M, Nat.card M • m = 0 := fun m => card_nsmul_eq_zero'
  obtain ⟨e⟩ := hroots (Nat.card M) Nat.card_pos
  set T := cartierDualEquivQZ M hMn e with hT
  have hact : ∀ φ, T ((cartierDual F Ω M).ρ c φ) = dualInv (act M c) (T φ) := fun φ =>
    cartierDualToQZ_act M hMn e (OrderTwo.inv_eq_self hG hc) (fun ζ hζ => hconj ζ ⟨_, Nat.card_pos, hζ⟩) φ
  have he0 : ∀ f, T.symm (dualInv (act M c) f) = act (cartierDual F Ω M) c (T.symm f) := fun f => by
    apply T.injective
    rw [T.apply_symm_apply]
    change _ = T ((cartierDual F Ω M).ρ c (T.symm f))
    rw [hact, T.apply_symm_apply]
  refine ⟨h2EquivOfOrderTwo M hG hc, (tateQuotCongr T.symm he0).trans (cohomZeroEquivContinuous (cartierDual F Ω M) hG hc),
    fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [AddEquiv.trans_apply, tateQuotCongr_mk, h2Equiv_mk, h0Equiv_mk, realDualityPairingTwoZero_mk,
    realDualityPairing_apply, tatePair_mk]
  obtain ⟨ht, hcup⟩ := cupPairing_cocycleTwo_H0 M hG hc (a : M) ((mem_fixedSub_act M).1 a.2)
    ⟨_, mem_invariants_of_fixed (cartierDual F Ω M) hG
      ((mem_fixedSub_act _).1 (fixedSubCongr T.symm he0 f).2)⟩
  rw [hcup]
  have hTf : cartierDualToQZ M hMn e (T.symm f) = f := T.apply_symm_apply f
  have hq : 2 • cartierDualToQZ M hMn e (T.symm f) a = 0 := by
    rw [hTf]
    exact two_nsmul_fixedPair (act M c) a f
  refine (realInv_cocycleTwo_eq_cartierDualToQZ h2 hN hG hc hneg M hMn e (T.symm f) a hq _
    (Or.inl rfl) ht).trans ?_
  rw [hTf]


include hneg hconj hroots in
theorem realDualityPairingZeroTwo_eq_tatePair :
    ∃ (e : tateQuot (act M c) ≃+ cohomologyTateZero M)
      (e' : tateQuot (dualInv (act M c)) ≃+ cohomology (cartierDual F Ω M) 2),
      ∀ x y, realDualityPairingZeroTwo h2 hN hG hc M (e x) (e' y) = tatePair (act M c) x y := by
  have : NeZero (Nat.card M) := ⟨Nat.card_pos.ne'⟩
  have hMn : ∀ m : M, Nat.card M • m = 0 := fun m => card_nsmul_eq_zero'
  obtain ⟨e⟩ := hroots (Nat.card M) Nat.card_pos
  set T := cartierDualEquivQZ M hMn e with hT
  have hact : ∀ φ, T ((cartierDual F Ω M).ρ c φ) = dualInv (act M c) (T φ) := fun φ =>
    cartierDualToQZ_act M hMn e (OrderTwo.inv_eq_self hG hc) (fun ζ hζ => hconj ζ ⟨_, Nat.card_pos, hζ⟩) φ
  have he0 : ∀ f, T.symm (dualInv (act M c) f) = act (cartierDual F Ω M) c (T.symm f) := fun f => by
    apply T.injective
    rw [T.apply_symm_apply]
    change _ = T ((cartierDual F Ω M).ρ c (T.symm f))
    rw [hact, T.apply_symm_apply]
  refine ⟨cohomZeroEquivContinuous M hG hc, (tateQuotCongr T.symm he0).trans (h2EquivOfOrderTwo (cartierDual F Ω M) hG hc),
    fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [AddEquiv.trans_apply, tateQuotCongr_mk, h2Equiv_mk, h0Equiv_mk, realDualityPairingZeroTwo_mk,
    realDualityPairing_apply, tatePair_mk]
  obtain ⟨ht, hcup⟩ := cupPairing_H0_cocycleTwo M hG hc
    ⟨_, mem_invariants_of_fixed M hG ((mem_fixedSub_act M).1 a.2)⟩
    ((fixedSubCongr T.symm he0 f : fixedSub _) : cartierDual F Ω M)
    ((mem_fixedSub_act _).1 (fixedSubCongr T.symm he0 f).2)
  rw [hcup]
  have hTf : cartierDualToQZ M hMn e ((fixedSubCongr T.symm he0 f : fixedSub _) : cartierDual F Ω M) =
      f := T.apply_symm_apply f
  have hq : 2 • cartierDualToQZ M hMn e
      ((fixedSubCongr T.symm he0 f : fixedSub _) : cartierDual F Ω M) a = 0 := by
    rw [hTf]
    exact two_nsmul_fixedPair (act M c) a f
  refine (realInv_cocycleTwo_eq_cartierDualToQZ h2 hN hG hc hneg M hMn e _ a hq _
    (Or.inl rfl) ht).trans ?_
  rw [hTf]


include hG hc hneg hconj hroots in
theorem realDualityPairing_one_eq_tatePair :
    ∃ (e : tateQuot (-act M c) ≃+ cohomology M 1)
      (e' : tateQuot (dualInv (-act M c)) ≃+ cohomology (cartierDual F Ω M) 1),
      ∀ x y, realDualityPairing F Ω h2 hN M (show 1 + 1 = 2 from rfl) (e x) (e' y) =
        tatePair (-act M c) x y := by
  have : NeZero (Nat.card M) := ⟨Nat.card_pos.ne'⟩
  have hMn : ∀ m : M, Nat.card M • m = 0 := fun m => card_nsmul_eq_zero'
  obtain ⟨e⟩ := hroots (Nat.card M) Nat.card_pos
  set T := cartierDualEquivQZ M hMn e with hT
  have hact : ∀ φ, T ((cartierDual F Ω M).ρ c φ) = dualInv (act M c) (T φ) := fun φ =>
    cartierDualToQZ_act M hMn e (OrderTwo.inv_eq_self hG hc) (fun ζ hζ => hconj ζ ⟨_, Nat.card_pos, hζ⟩) φ
  have he1 : ∀ f, T.symm (dualInv (-act M c) f) = (-act (cartierDual F Ω M) c) (T.symm f) :=
    fun f => by
      apply T.injective
      rw [T.apply_symm_apply, AddMonoidHom.neg_apply, map_neg, dualInv_neg]
      change _ = -T ((cartierDual F Ω M).ρ c (T.symm f))
      rw [hact, T.apply_symm_apply]
  refine ⟨h1EquivOfOrderTwo M hG hc, (tateQuotCongr T.symm he1).trans (h1EquivOfOrderTwo (cartierDual F Ω M) hG hc),
    fun x y => ?_⟩
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [AddEquiv.trans_apply, tateQuotCongr_mk, h1Equiv_mk, h1Equiv_mk, realDualityPairing_apply,
    tatePair_mk]
  set β : cartierDual F Ω M := ((fixedSubCongr T.symm he1 f : fixedSub _) : cartierDual F Ω M)
    with hβdef
  obtain ⟨ht, hcup⟩ := cupPairing_cocycleOne M hG hc (α : M) ((mem_fixedSub_neg_act M).1 α.2)
    β ((mem_fixedSub_neg_act _).1 (fixedSubCongr T.symm he1 f).2)
  rw [hcup]
  have hTf : cartierDualToQZ M hMn e β = f := T.apply_symm_apply f
  have hq : 2 • cartierDualToQZ M hMn e β α = 0 := by
    rw [hTf]
    exact two_nsmul_fixedPair (-act M c) α f
  have hβ : (cartierDual F Ω M).ρ c β = -β :=
    eq_neg_of_add_eq_zero_right ((mem_fixedSub_neg_act _).1 (fixedSubCongr T.symm he1 f).2)
  refine (realInv_cocycleTwo_eq_cartierDualToQZ h2 hN hG hc hneg M hMn e β α hq _
    (Or.inr (by rw [hβ]; rfl)) ht).trans ?_
  rw [hTf]


include hG hc hneg hconj hroots in
theorem realDualityPairing_one_bijective :
    Function.Bijective (realDualityPairing F Ω h2 hN M (show 1 + 1 = 2 from rfl)) := by
  obtain ⟨e, e', h⟩ := realDualityPairing_one_eq_tatePair h2 hN hG hc hneg hconj hroots M
  exact bijective_of_pairing_eq _ _ e e' h tatePair_bijective


include hG hc hneg hconj hroots in
theorem realDualityPairing_one_flip_bijective :
    Function.Bijective (realDualityPairing F Ω h2 hN M (show 1 + 1 = 2 from rfl)).flip := by
  obtain ⟨e, e', h⟩ := realDualityPairing_one_eq_tatePair h2 hN hG hc hneg hconj hroots M
  exact bijective_flip_of_pairing_eq _ _ e e' h tatePair_flip_bijective


include hneg hconj hroots in
theorem realDualityPairingTwoZero_bijective :
    Function.Bijective (realDualityPairingTwoZero h2 hN hG hc M) := by
  obtain ⟨e, e', h⟩ := realDualityPairingTwoZero_eq_tatePair h2 hN hG hc hneg hconj hroots M
  exact bijective_of_pairing_eq _ _ e e' h tatePair_bijective


include hneg hconj hroots in
theorem realDualityPairingTwoZero_flip_bijective :
    Function.Bijective (realDualityPairingTwoZero h2 hN hG hc M).flip := by
  obtain ⟨e, e', h⟩ := realDualityPairingTwoZero_eq_tatePair h2 hN hG hc hneg hconj hroots M
  exact bijective_flip_of_pairing_eq _ _ e e' h tatePair_flip_bijective


include hneg hconj hroots in
theorem realDualityPairingZeroTwo_bijective :
    Function.Bijective (realDualityPairingZeroTwo h2 hN hG hc M) := by
  obtain ⟨e, e', h⟩ := realDualityPairingZeroTwo_eq_tatePair h2 hN hG hc hneg hconj hroots M
  exact bijective_of_pairing_eq _ _ e e' h tatePair_bijective


include hneg hconj hroots in
theorem realDualityPairingZeroTwo_flip_bijective :
    Function.Bijective (realDualityPairingZeroTwo h2 hN hG hc M).flip := by
  obtain ⟨e, e', h⟩ := realDualityPairingZeroTwo_eq_tatePair h2 hN hG hc hneg hconj hroots M
  exact bijective_flip_of_pairing_eq _ _ e e' h tatePair_flip_bijective

end Duality

section Values

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (h2 : Module.finrank F Ω ≤ 2)
  (hN : ∀ a b : Fˣ, (a : F) ∉ Set.range (Algebra.norm F : Ω → F) →
    (b : F) ∉ Set.range (Algebra.norm F : Ω → F) →
      ((a * b : Fˣ) : F) ∈ Set.range (Algebra.norm F : Ω → F))
  {c : Gal(Ω/F)} (hG : ∀ g : Gal(Ω/F), g = 1 ∨ g = c) (hc : c ≠ 1)
  (hneg : (-1 : F) ∉ Set.range (Algebra.norm F : Ω → F))
  (hconj : ∀ ζ : galUnits.{0} F Ω, (∃ k : ℕ, 0 < k ∧ k • ζ = 0) → (galUnits.{0} F Ω).ρ c ζ = -ζ)
  (hroots : ∀ k : ℕ, 0 < k → Nonempty (galRootsOfUnity.{0} F Ω k ≃+ ZMod k))
  (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M]

end Values

section Bundle

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (h2 : Module.finrank F Ω ≤ 2)
  (hN : ∀ a b : Fˣ, (a : F) ∉ Set.range (Algebra.norm F : Ω → F) →
    (b : F) ∉ Set.range (Algebra.norm F : Ω → F) →
      ((a * b : Fˣ) : F) ∈ Set.range (Algebra.norm F : Ω → F))
  {c : Gal(Ω/F)} (hG : ∀ g : Gal(Ω/F), g = 1 ∨ g = c) (hc : c ≠ 1)
  (hneg : (-1 : F) ∉ Set.range (Algebra.norm F : Ω → F))
  (hconj : ∀ ζ : galUnits.{0} F Ω, (∃ k : ℕ, 0 < k ∧ k • ζ = 0) → (galUnits.{0} F Ω).ρ c ζ = -ζ)
  (hroots : ∀ k : ℕ, 0 < k → Nonempty (galRootsOfUnity.{0} F Ω k ≃+ ZMod k))
  (M : Rep.{0} (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M]


include hneg hconj hroots in
theorem real_local_duality_of_orderTwo :
    (Function.Bijective (realDualityPairingZeroTwo h2 hN hG hc M) ∧
      Function.Bijective (realDualityPairingZeroTwo h2 hN hG hc M).flip) ∧
    (Function.Bijective (realDualityPairing F Ω h2 hN M (show 1 + 1 = 2 from rfl)) ∧
      Function.Bijective (realDualityPairing F Ω h2 hN M (show 1 + 1 = 2 from rfl)).flip) ∧
    (Function.Bijective (realDualityPairingTwoZero h2 hN hG hc M) ∧
      Function.Bijective (realDualityPairingTwoZero h2 hN hG hc M).flip) :=
  ⟨⟨realDualityPairingZeroTwo_bijective h2 hN hG hc hneg hconj hroots M,
      realDualityPairingZeroTwo_flip_bijective h2 hN hG hc hneg hconj hroots M⟩,
    ⟨realDualityPairing_one_bijective h2 hN hG hc hneg hconj hroots M,
      realDualityPairing_one_flip_bijective h2 hN hG hc hneg hconj hroots M⟩,
    ⟨realDualityPairingTwoZero_bijective h2 hN hG hc hneg hconj hroots M,
      realDualityPairingTwoZero_flip_bijective h2 hN hG hc hneg hconj hroots M⟩⟩

end Bundle

end GroundTheory.ProfCoh
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField GroundTheory.Global Involution OrderTwo

open scoped NumberField.LiesOver

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (v : InfinitePlace K.1) (hv : v.IsReal)


include hv in
theorem exists_isComplex_infCompletion_algEquiv : ∃ (F : FiniteSubfield) (_ : Fact (K ≤ F))
    (w : v.placesOver F.1), (w : InfinitePlace F.1).IsComplex ∧
      Nonempty ((w : InfinitePlace F.1).Completion ≃ₐ[v.Completion] AlgebraicClosure v.Completion) := by
  obtain ⟨F, hF, w, ⟨e⟩⟩ := exists_infCompletion_algEquiv v
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  refine ⟨F, hF, w, ?_, ⟨e⟩⟩
  by_contra hw
  have h1 : Module.finrank v.Completion (AlgebraicClosure v.Completion) = 1 := by
    rw [← e.toLinearEquiv.finrank_eq]
    exact (GroundTheory.Global.InfinitePlace.finrank_completion_eq_one_iff (w : InfinitePlace F.1)).2
      fun h => hw h.2
  have hbt := Subalgebra.bot_eq_top_of_finrank_eq_one h1
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure v.Completion)
    (n := 2) (by norm_num)
  have hmem : i ∈ (⊥ : Subalgebra v.Completion (AlgebraicClosure v.Completion)) := by
    rw [hbt]
    exact Algebra.mem_top
  obtain ⟨x, hx⟩ := Algebra.mem_bot.1 hmem
  have hx2 : x ^ 2 = -1 := by
    apply (algebraMap v.Completion (AlgebraicClosure v.Completion)).injective
    rw [map_pow, hx, hi, map_neg, map_one]
  have h := congrArg (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv) hx2
  rw [map_pow, map_neg, map_one] at h
  nlinarith [sq_nonneg (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv x)]


include hv in
theorem finrank_infAlgClosure_of_isReal :
    Module.finrank v.Completion (AlgebraicClosure v.Completion) = 2 := by
  obtain ⟨F, _, w, hw, ⟨e⟩⟩ := exists_isComplex_infCompletion_algEquiv v hv
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  rw [← e.toLinearEquiv.finrank_eq]
  exact (GroundTheory.Global.InfinitePlace.finrank_completion_eq_two_iff (w : InfinitePlace F.1)).2 ⟨hv, hw⟩


include hv in
theorem extensionEmbeddingOfIsReal_norm_pos (y : AlgebraicClosure v.Completion) (hy : y ≠ 0) :
    0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (Algebra.norm v.Completion y) := by
  obtain ⟨F, _, w, hw, ⟨e⟩⟩ := exists_isComplex_infCompletion_algEquiv v hv
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  have hy' : e.symm y ≠ 0 := (map_ne_zero e.symm).2 hy
  have hn : Algebra.norm v.Completion y ≠ 0 := Algebra.norm_ne_zero_iff.2 hy
  have hmem : Units.mk0 _ hn ∈ GroundTheory.Global.InfinitePlace.normSubgroup v (w : InfinitePlace F.1) :=
    ⟨Units.mk0 _ hy', Units.ext (by
      rw [Units.coe_map, Units.val_mk0, Units.val_mk0]
      exact Algebra.norm_eq_of_algEquiv e.symm y)⟩
  exact (GroundTheory.Global.InfinitePlace.mem_normSubgroup_iff hv hw _).1 hmem


include hv in
theorem neg_one_not_mem_range_norm_infAlgClosure :
    (-1 : v.Completion) ∉ Set.range (Algebra.norm v.Completion :
      AlgebraicClosure v.Completion → v.Completion) := by
  rintro ⟨y, hy⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [Algebra.norm_zero] at hy
    exact zero_ne_one (neg_eq_zero.1 hy.symm).symm
  have h := extensionEmbeddingOfIsReal_norm_pos v hv y hy0
  rw [hy, map_neg, map_one] at h
  linarith

include hv in
theorem card_realGal_eq_two :
    Fintype.card Gal(AlgebraicClosure v.Completion / v.Completion) = 2 := by
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, finrank_infAlgClosure_of_isReal v hv]

include hv in
theorem exists_ne_one_gal_infAlgClosure :
    ∃ c : Gal(AlgebraicClosure v.Completion / v.Completion), c ≠ 1 := by
  have h := card_realGal_eq_two v hv
  obtain ⟨c, d, hcd⟩ := Fintype.exists_pair_of_one_lt_card (by omega :
    1 < Fintype.card Gal(AlgebraicClosure v.Completion / v.Completion))
  by_cases hc : c = 1
  · exact ⟨d, fun hd => hcd (hc.trans hd.symm)⟩
  · exact ⟨c, hc⟩

def realConj : Gal(AlgebraicClosure v.Completion / v.Completion) :=
  (exists_ne_one_gal_infAlgClosure v hv).choose

theorem realConj_ne_one : realConj v hv ≠ 1 :=
  (exists_ne_one_gal_infAlgClosure v hv).choose_spec

theorem eq_one_or_eq_realConj (g : Gal(AlgebraicClosure v.Completion / v.Completion)) :
    g = 1 ∨ g = realConj v hv := by
  by_cases hg : g = 1
  · exact Or.inl hg
  · exact Or.inr (eq_of_ne_one_of_card_eq_two (card_realGal_eq_two v hv) hg
      (realConj_ne_one v hv))

theorem realConj_apply_of_pow_eq_one (u : (AlgebraicClosure v.Completion)ˣ) {k : ℕ} (hk : 0 < k)
    (huk : u ^ k = 1) : realConj v hv (u : AlgebraicClosure v.Completion) = ((u⁻¹ : (AlgebraicClosure v.Completion)ˣ) : AlgebraicClosure v.Completion) := by
  classical
  have hu0 : (u : AlgebraicClosure v.Completion) ≠ 0 := Units.ne_zero _
  have hprod : algebraMap v.Completion (AlgebraicClosure v.Completion)
      (Algebra.norm v.Completion (u : AlgebraicClosure v.Completion)) =
        (u : AlgebraicClosure v.Completion) * realConj v hv u := by
    rw [Algebra.norm_eq_prod_automorphisms]
    have huniv : (Finset.univ : Finset Gal(AlgebraicClosure v.Completion / v.Completion)) =
        {1, realConj v hv} := by
      ext g
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      exact eq_one_or_eq_realConj v hv g
    rw [huniv, Finset.prod_pair (realConj_ne_one v hv).symm, AlgEquiv.one_apply]
  have hr : Algebra.norm v.Completion (u : AlgebraicClosure v.Completion) = 1 := by
    have hpos := extensionEmbeddingOfIsReal_norm_pos v hv u hu0
    have hpow : (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
        (Algebra.norm v.Completion (u : AlgebraicClosure v.Completion))) ^ k = 1 := by
      rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, huk, Units.val_one, map_one, map_one]
    have h1 := (pow_eq_one_iff_of_nonneg hpos.le hk.ne').1 hpow
    apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).injective
    rw [h1, map_one]
  rw [hr, map_one] at hprod
  rw [Units.val_inv_eq_inv_val]
  exact eq_inv_of_mul_eq_one_right hprod.symm

theorem realConj_galUnits_of_torsion (ζ : galUnits.{0} v.Completion (AlgebraicClosure v.Completion))
    (hζ : ∃ k : ℕ, 0 < k ∧ k • ζ = 0) :
    (galUnits.{0} v.Completion (AlgebraicClosure v.Completion)).ρ (realConj v hv) ζ = -ζ := by
  obtain ⟨k, hk, hkζ⟩ := hζ
  obtain ⟨u, rfl⟩ : ∃ u : (AlgebraicClosure v.Completion)ˣ,
      (Additive.ofMul u : Additive (AlgebraicClosure v.Completion)ˣ) = ζ :=
    ⟨Additive.toMul (ζ : Additive (AlgebraicClosure v.Completion)ˣ), rfl⟩
  have huk : u ^ k = 1 := by
    change k • (Additive.ofMul u : Additive (AlgebraicClosure v.Completion)ˣ) = 0 at hkζ
    rwa [← ofMul_pow, ofMul_eq_zero] at hkζ
  show Additive.ofMul (galUnitsHom v.Completion (AlgebraicClosure v.Completion) (realConj v hv) u) =
    Additive.ofMul u⁻¹
  congr 1
  apply Units.ext
  rw [coe_galUnitsHom_apply]
  exact realConj_apply_of_pow_eq_one v hv u hk huk

theorem nonempty_addEquiv_galRootsOfUnity_infAlgClosure (k : ℕ) (hk : 0 < k) :
    Nonempty (galRootsOfUnity.{0} v.Completion (AlgebraicClosure v.Completion) k ≃+ ZMod k) :=
  nonempty_addEquiv_galRootsOfUnity (Nat.cast_ne_zero.2 hk.ne')

theorem realInv_eq_placeInv
    (x : cohomology (galUnits.{0} v.Completion (AlgebraicClosure v.Completion)) 2) :
    realInv v.Completion (AlgebraicClosure v.Completion) (infAlgClosure_finrank_le_two v)
        (infAlgClosure_mul_mem_range_norm v) x =
      placeInv (.inl v)
        (cohomologyULiftIntAddEquiv (galUnits.{0} v.Completion (AlgebraicClosure v.Completion)) 2 x) :=
  rfl

end GroundTheory.ProfCoh
