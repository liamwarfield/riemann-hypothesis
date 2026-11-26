module

public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohFin

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTate
section -- merged from CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTateB
open CategoryTheory MonoidalCategory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

attribute [local instance 2000] Rep.hV2

section Core

variable {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M M' P : Type} [AddCommGroup M] [Module (ZMod n) M] [AddCommGroup M'] [Module (ZMod n) M']
  [AddCommGroup P] [Module (ZMod n) P]
  [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace M'] [DiscreteTopology M']
  [TopologicalSpace P] [DiscreteTopology P]
  (rho : Representation (ZMod n) G M) (rho' : Representation (ZMod n) G M')
  (rhoP : Representation (ZMod n) G P) (b : M →ₗ[ZMod n] M' →ₗ[ZMod n] P)
  (hbc : Continuous fun p : M × M' => b p.1 p.2)
  (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
  (A D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] [IsDiscreteRep D]
  [IsDiscreteRep (dualRep D A)]
  (eA : M ≃+ A.V) (hA : ∀ g m, eA (rho g m) = A.ρ g (eA m))
  (eD : P ≃+ D.V) (hD : ∀ g m, eD (rhoP g m) = D.ρ g (eD m))
  (eB : M' ≃+ (dualRep D A).V) (hB : ∀ g y, eB (rho' g y) = (dualRep D A).ρ g (eB y))
  (hev : ∀ x y, (eB y : A →ₗ[ULift.{0} ℤ] D) (eA x) = eD (b x y))
  (t : cohomology D 2 ≃+ ZMod n)

omit [DiscreteTopology M] in
include hA in
theorem exists_cocycle_zero [IsTopologicalAddGroup M] [ContinuousConstSMul (ZMod n) M]
    (m : H0 rho) :
    ∃ x : cocycles A 0, ∀ s, cochainOf (A := A) (cocycleι (A := A) (p := 0) x) s = eA m.1 := by
  obtain ⟨z, -, hz⟩ := exists_cocycle_H0Iso_inv A ⟨eA m.1, fun g => by
    rw [← hA, (mem_riemannRochSpace_iff_regularAt_everywhere rho m.1).1 m.2 g]⟩
  exact ⟨z, fun s => by rw [hz]⟩

include hA hD hB hev in
theorem cup_product_H0_H2_bijective (h0 : Sgc0) (h2 : Sgc2)
    (hd : Function.Bijective (dualityMap D (rfl : 0 + 2 = 2) t.toAddMonoidHom A)) :
    Function.Bijective (cupProductH0H2 rho rho' rhoP b hbc hbe) := by
  obtain ⟨e0, he0⟩ := h0 G (ZMod n) M rho A eA hA
  obtain ⟨e2, hex, he2⟩ := h2 G (ZMod n) M' rho' (dualRep D A) eB hB
  obtain ⟨eP, -, heP⟩ := h2 G (ZMod n) P rhoP D eD hD
  refine bij_transport _ _ e0 e2 (eP.trans t) (fun m y => ?_) hd
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨x, hx⟩ := exists_cocycle_zero rho A eA hA m
  obtain ⟨w, hw⟩ := hex z
  rw [he0 m x hx, he2 z w hw, dualityMap_apply, cupPairing_cohomologyπ, AddEquiv.trans_apply]
  refine congrArg t (heP (cupCocycleH0Z2 rho rho' rhoP b hbc hbe m z) _ fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hw, ← hB]
  refine (evalPairing_tmul D A _ _).trans ?_
  rw [hev, cupCocycleH0Z2_apply]
  congr 2
  simp [Fin.partialProd]

include hA hD hB hev in
theorem cup_product_H2_H0_bijective (h0 : Sgc0) (h2 : Sgc2)
    (hd : Function.Bijective (dualityMap D (rfl : 2 + 0 = 2) t.toAddMonoidHom A)) :
    Function.Bijective (cupProductH2H0 rho rho' rhoP b hbc hbe) := by
  obtain ⟨e0, he0⟩ := h0 G (ZMod n) M' rho' (dualRep D A) eB hB
  obtain ⟨e2, hex, he2⟩ := h2 G (ZMod n) M rho A eA hA
  obtain ⟨eP, -, heP⟩ := h2 G (ZMod n) P rhoP D eD hD
  refine bij_transport _ _ e2 e0 (eP.trans t) (fun y m => ?_) hd
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨x, hx⟩ := exists_cocycle_zero rho' (dualRep D A) eB hB m
  obtain ⟨w, hw⟩ := hex z
  rw [he0 m x hx, he2 z w hw, dualityMap_apply, cupPairing_cohomologyπ, AddEquiv.trans_apply]
  refine congrArg t (heP (cupCocycleZ2H0 rho rho' rhoP b hbc hbe z m) _ fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hw, ← hB]
  refine (evalPairing_tmul D A _ _).trans ?_
  rw [hev, cupCocycleZ2H0_apply, (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2]

include hA hD hB hev in
theorem cup_product_H1_H1_bijective (h1 : Sgc1) (h2 : Sgc2) (hc : ContAction rho')
    (hd : Function.Bijective (dualityMap D (rfl : 1 + 1 = 2) t.toAddMonoidHom A)) :
    Function.Bijective (cupProductH1H1 rho rho' rhoP b hbc hbe hc) := by
  obtain ⟨e1, hex1, he1⟩ := h1 G (ZMod n) M rho A eA hA
  obtain ⟨e1', hex1', he1'⟩ := h1 G (ZMod n) M' rho' (dualRep D A) eB hB
  obtain ⟨eP, -, heP⟩ := h2 G (ZMod n) P rhoP D eD hD
  refine bij_transport _ _ e1 e1' (eP.trans t) (fun y y' => ?_) hd
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ y'
  obtain ⟨x, hx⟩ := hex1 z
  obtain ⟨w, hw⟩ := hex1' z'
  rw [he1 z x hx, he1' z' w hw, dualityMap_apply, cupPairing_cohomologyπ, AddEquiv.trans_apply]
  refine congrArg t (heP (cupCocycleZ1Z1 rho rho' rhoP b hbc hbe hc z z') _ fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hw, ← hB]
  refine (evalPairing_tmul D A _ _).trans ?_
  rw [hev, cupCocycleZ1Z1_apply]
  congr 2
  simp [Fin.partialProd]

end Core

end CompanionTheory.LocalTateOrthogonality.Gcoh
end

open CategoryTheory MonoidalCategory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel Formalism.GaloisCohomology

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

attribute [local instance 2000] Rep.hV2

theorem tate_core (hRep : SgcRep) (h0 : Sgc0) (h1 : Sgc1) (h2 : Sgc2) {n : ℕ} [NeZero n]
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep D]
    (H : DualityHypotheses n D)
    (hfin : ∀ (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] [Finite A], (∀ a : A, n • a = 0) →
      Finite (cohomology A 1))
    (χ : G →* (ZMod n)ˣ) (eD : ZMod n ≃+ D.V)
    (hD : ∀ (g : G) (m : ZMod n), eD ((χ g : ZMod n) * m) = D.ρ g (eD m))
    (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation (ZMod n) G M) (hrho : ContAction rho) :
    Nonempty (H2 (charRep χ) ≃ₗ[ZMod n] ZMod n) ∧
    Function.Bijective (cupH0H2TwistedDual χ rho (MonoidHom.id _)) ∧
    Function.Bijective (cupH1H1TwistedDual χ rho (MonoidHom.id _) (hrho.comp' continuous_id)) ∧
    Function.Bijective (cupH1H1TwistedDual χ rho (MonoidHom.id _) (hrho.comp' continuous_id)).flip ∧
    Function.Bijective (cup20 χ rho (MonoidHom.id _)) := by
  obtain ⟨A, _, eA, hA⟩ := hRep G (ZMod n) M rho hrho
  have ht : Function.Bijective H.tTop :=
    (H.t ⊤).bijective.comp (bijective_cohomologyRes_top D 2)
  let t : cohomology D 2 ≃+ ZMod n := AddEquiv.ofBijective H.tTop ht
  have : Finite A := Finite.of_equiv _ eA.toEquiv
  have : Finite D := Finite.of_equiv _ eD.toEquiv
  have hAn : ∀ a : A, n • a = 0 := fun a => by
    obtain ⟨m, rfl⟩ := eA.surjective a
    rw [← map_nsmul, nsmul_zmod, map_zero]
  have hDn : ∀ a : D, n • a = 0 := nsmul_eq_zero_of_nonempty_addEquiv ⟨eD.symm⟩
  let ι := MonoidHom.id G
  have hid : Function.Bijective (evalPair (R := ZMod n) (M := M)).flip :=
    Function.bijective_id
  have hev : Function.Bijective (evalPair (R := ZMod n) (M := M)).flip.flip :=
    bij_flip _ (AddEquiv.refl _) hid
  obtain ⟨eB, hB, hAB⟩ := exists_dualEquiv (rho.comp ι) ((twDual χ rho).comp ι)
    ((charRep χ).comp ι) evalPair (fun g x y => evalPair_equiv χ rho (ι g) x y) A D eA hA eD hD hid
  obtain ⟨eC, hC, hBC⟩ := exists_dualEquiv ((twDual χ rho).comp ι) (rho.comp ι)
    ((charRep χ).comp ι) evalPair.flip (fun g y x => evalPair_equiv χ rho (ι g) x y)
    (dualRep D A) D eB hB eD hD hev
  have : Finite (dualRep D A) := finite_dualRep
  have : IsDiscreteRep (dualRep D (dualRep D A)) := isDiscreteRep_dualRep D (dualRep D A)
  have h11 : Function.Bijective (cupH1H1TwistedDual χ rho ι (hrho.comp' continuous_id)) :=
    cup_product_H1_H1_bijective _ _ _ _ _ _ (dualRep D A) D eB hB eD hD eC hC hBC t h1 h2 _
      (H.bijective_dualityMap_of_group (dualRep D A) (nsmul_dualRep_eq_zero hDn) _)
  obtain ⟨eP, -⟩ := h2 G (ZMod n) (ZMod n) (charRep χ) D eD hD
  obtain ⟨eP', -⟩ := h2 G (ZMod n) (ZMod n) ((charRep χ).comp ι) D eD hD
  obtain ⟨e1, -⟩ := h1 G (ZMod n) M (rho.comp ι) A eA hA
  have := hfin A hAn
  have : Finite (H1 (rho.comp ι)) := Finite.of_equiv _ e1.symm.toEquiv
  refine ⟨⟨LinearEquiv.ofBijective ((eP.trans t).toAddMonoidHom.toZModLinearMap n)
    (eP.trans t).bijective⟩, ?_, h11, bij_flip _ (eP'.trans t) h11, ?_⟩
  · exact cup_product_H0_H2_bijective _ _ _ _ _ _ A D eA hA eD hD eB hB hAB t h0 h2
      (H.bijective_dualityMap_of_group A hAn _)
  · exact cup_product_H2_H0_bijective _ _ _ _ _ _ A D eA hA eD hD eB hB hAB t h0 h2
      (H.bijective_dualityMap_of_group A hAn _)

theorem tate_of (hRep : SgcRep) (h0 : Sgc0) (h1 : Sgc1) (h2 : Sgc2) (hF : SgcField) (hMu : SgcMu) :
    Formalism.GaloisCohomology.LocalTateDualityK := by
  intro l _ K hK r M _ _ _ _ _ rho hr hrho
  obtain ⟨hsep, _, _, hloc, -⟩ := hF l K hK
  have hl : (l ^ r : ℕ) ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ r) := ⟨hl⟩
  have : CharZero K := algebraRat.charZero K
  have hn : ((l ^ r : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hl
  obtain ⟨eD, hD⟩ := hMu l K r
  exact tate_core hRep h0 h1 h2 (galRootsOfUnity.{0} K (PadicAlgCl l) (l ^ r))
    (localDualityHypotheses hn)
    (fun A _ _ hA => finite_cohomology_galois_top K (PadicAlgCl l) hn A hA 1)
    (cycK l K r) eD hD M rho hrho

end CompanionTheory.LocalTateOrthogonality.Gcoh
end

section -- merged from CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohMu
open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

theorem cycKSpec : Formalism.GaloisCohomology.CycKSpec := by
  intro l _ K r σ ζ hζ
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut _ (PadicAlgCl l) σ) ζ hζ

theorem gcMu : SgcMu := by
  intro l hl K r
  have : IsSepClosure ↥K (PadicAlgCl l) :=
    ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable ℚ_[l] K _⟩
  have hn : ((l ^ r : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hl.out.ne_zero)
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  obtain ⟨e⟩ := nonempty_addEquiv_galRootsOfUnity (K := K) (Ksep := PadicAlgCl l) hn
  refine ⟨e.symm, fun g m => ?_⟩
  have key : ∀ x : Additive (rootsOfUnity (l ^ r) (PadicAlgCl l)),
      (galRootsOfUnity.{0} ↥K (PadicAlgCl l) (l ^ r)).ρ g x =
        (Formalism.GaloisCohomology.cycK l K r g : ZMod (l ^ r)).val • x := by
    intro x
    rw [galRootsOfUnity_ρ_apply]
    apply Additive.toMul.injective
    rw [toMul_ofMul, toMul_nsmul]
    apply Subtype.ext
    apply Units.ext
    rw [coe_galRootsOfUnityHom_apply, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]
    refine cycKSpec l K r g _ ?_
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 x.toMul.2, Units.val_one]
  refine Eq.trans ?_ (key _).symm
  refine Eq.trans ?_ (map_nsmul e.symm _ m)
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]

end CompanionTheory.LocalTateOrthogonality.Gcoh
end

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

theorem top_tate : Formalism.GaloisCohomology.LocalTateDualityK := tate_of gcRep gc0 gc1 gc2 gcField gcMu

theorem top_locfin : Formalism.GaloisCohomology.LocalFinitenessK := locfin_of gcField

end CompanionTheory.LocalTateOrthogonality.Gcoh
