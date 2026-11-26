module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RingKrullDimMvPowerSeriesFinField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegrallyClosedPowerSeries
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CohenStructureFiniteOverNormalCompleteSubring

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsFiniteInjectiveMvPowerSeriesCompatibleSect
open IsLocalRing UpperTheory.V.Alg

private theorem finite_quotient_of_pow_le {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    [IsNoetherianRing S] {I J : Ideal S} (h : ∀ s : S, ∃ a : A, s - algebraMap A S a ∈ I) {N : ℕ}
    (hN : I ^ N ≤ J) : Module.Finite A (S ⧸ J) := _root_.GlobalTheory.CohenStructure.finite_quotient_of_pow_le (A := A) (S := S) (I := I) (J := J) (N := N) h hN

private theorem injective_of_ringKrullDim_eq {A S : Type} [CommRing A] [IsDomain A] [CommRing S]
    [Algebra A S] [Module.Finite A S] {n : ℕ} (hA : ringKrullDim A = n) (hS : ringKrullDim S = n) :
    Function.Injective (algebraMap A S) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  letI : Algebra (A ⧸ Ideal.span {r}) S :=
    (Ideal.Quotient.lift (Ideal.span {r}) (algebraMap A S) (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
      rw [map_mul, hr, zero_mul])).toAlgebra
  haveI : IsScalarTower A (A ⧸ Ideal.span {r}) S := .of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite (A ⧸ Ideal.span {r}) S := Module.Finite.of_restrictScalars_finite A _ _
  have h1 : ringKrullDim S ≤ ringKrullDim (A ⧸ Ideal.span {r}) :=
    Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap (A ⧸ Ideal.span {r}) S))
      fun _ _ hpq => Ideal.IsIntegral.comap_lt_comap (R := A ⧸ Ideal.span {r}) hpq
  have h2 := ringKrullDim_succ_le_of_surjective
    (Ideal.Quotient.mk (Ideal.span {r})) Ideal.Quotient.mk_surjective
    (mem_nonZeroDivisors_of_ne_zero hr0)
    (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self r))
  have h3 : ringKrullDim S + 1 ≤ ringKrullDim A := (add_le_add_left h1 1).trans h2
  rw [hA, hS] at h3
  norm_cast at h3
  omega

open MvPowerSeries GlobalTheory in
theorem UpperTheory.exists_finite_injective_mvPowerSeries_compatible_section :
    ∀ (O S : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing S] [IsDomain S] [Algebra O S] [IsCO O S] (x : S →ₐ[O] O), ∃ (d : ℕ) (F : MvPowerSeries (Fin d) O →ₐ[O] S), Function.Injective F ∧ F.toRingHom.Finite ∧ ringKrullDim S = (d + 1 : ℕ) ∧ ∀ g, x (F g) = MvPowerSeries.constantCoeff g := by
  intro O S _ _ _ _ _ _ _ hS x
  have hc : IsAdicComplete (maximalIdeal S) S := IsCO.complete (O := O)
  have hl : IsLocalHom (algebraMap O S) := IsCO.isLocalHom
  have hn : IsNoetherianRing S := hS.toIsNoetherian
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm := hp.maximalIdeal_eq
  have hloc : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ maximalIdeal S :=
    fun a ha h => ha (IsLocalHom.map_nonunit a h)
  have hpm : p ∈ maximalIdeal O := hm ▸ Ideal.mem_span_singleton_self p
  have hp0 : algebraMap O S p ≠ 0 := fun h => hp.ne_zero (by simpa using congrArg x h)
  have hx : ∀ s ∈ maximalIdeal S, x s ∈ maximalIdeal O := fun s hs => by
    rw [← res_eq_zero_iff O O, res_map, res_eq_zero_iff]
    exact hs
  obtain ⟨n, y, hy, hd, N, hN⟩ := GlobalTheory.exists_systemOfParameters_insert S _ hp0 (hloc p hpm)
  let z : Fin n → S := fun i => y i - algebraMap O S (x (y i))
  have hz : ∀ i, z i ∈ maximalIdeal S := fun i => sub_mem (hy i) (hloc _ (hx _ (hy i)))
  let A := MvPowerSeries (Fin n) O
  let φ : A →ₐ[O] S := mvEvalAdic O (maximalIdeal S) z hz
  have hφX : ∀ i, φ (X i) = z i := fun i => mvEvalAdic_X _ z hz i
  letI : Algebra A S := φ.toRingHom.toAlgebra
  have : IsDomain A := NoZeroDivisors.to_isDomain _
  have hA : IsAdicComplete (maximalIdeal A) A := (co_mvps O O (Fin n)).complete
  have hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S := by
    refine Ideal.map_le_iff_le_comap.2 fun g hg => ?_
    have h4 := algHom_sub_constantCoeff_mem φ (K := maximalIdeal S)
      (fun j => hφX j ▸ hz j) g
    have h5 := FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    have h7 := add_mem h4 (hloc _ h5)
    rwa [sub_add_cancel] at h7
  have hC : ∀ a : O, algebraMap A S (C a) = algebraMap O S a := fun a => mvEvalAdic_C _ z hz a
  have hCm : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ (maximalIdeal A).map (algebraMap A S) :=
    fun a ha => hC a ▸ Ideal.mem_map_of_mem (algebraMap A S)
      (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simpa using ha))
  have hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S) := by
    refine hN.trans (Ideal.span_le.2 ?_)
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact hCm p hpm
    · have h1 : z i ∈ (maximalIdeal A).map (algebraMap A S) := by
        rw [← hφX i]
        exact Ideal.mem_map_of_mem (algebraMap A S)
          (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))
      have h2 := add_mem h1 (hCm _ (hx _ (hy i)))
      simpa [z] using h2
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A S)) S :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  have : Module.Finite A (S ⧸ (maximalIdeal A).map (algebraMap A S)) := by
    refine finite_quotient_of_pow_le (fun s => ?_) hge
    obtain ⟨a, h⟩ := IsCO.res_surj (O := O) s
    exact ⟨C a, by rwa [hC]⟩
  have hfin : Module.Finite A S := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)
  have hd' : ringKrullDim S = (n + 1 : ℕ) := by rw [hd]; norm_cast
  refine ⟨n, φ, injective_of_ringKrullDim_eq (A := A) (n := n + 1) ?_ hd', hfin, hd', fun g => ?_⟩
  · rw [FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one,
      Nat.card_eq_fintype_card, Fintype.card_fin, add_comm]
    norm_cast
  · have h := algHom_sub_constantCoeff_mem (x.comp φ) (K := ⊥) (fun j => by
      simp [hφX, z]) g
    simpa [sub_eq_zero] using h
end

open IsLocalRing UpperTheory.V.Alg

private theorem normal_mv (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (n : ℕ) : IsIntegrallyClosed (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact IsIntegrallyClosed.of_equiv (MvPowerSeries.isEmptyEquiv (Fin 0) R).toRingEquiv.symm
  | succ n ih =>
    have : IsDomain (MvPowerSeries (Fin n) R) := NoZeroDivisors.to_isDomain _
    have := GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries (MvPowerSeries (Fin n) R)
    exact IsIntegrallyClosed.of_equiv (MvPowerSeries.finSuccEquiv R n).toRingEquiv.symm

private theorem ht_const (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (n : ℕ) :
    (n : ℕ∞) ≤ (RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) O →+* O)).height := by
  let x : MvPowerSeries (Fin n) O →ₐ[O] O :=
    { (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) O →+* O) with
      commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] }
  let φ : MvPowerSeries (Fin n) O →ₐ[O] MvPowerSeries (Fin n) (FractionRing O) :=
    { (MvPowerSeries.map (algebraMap O (FractionRing O))) with
      commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] }
  have hφ : ∀ a, φ a = MvPowerSeries.map (algebraMap O (FractionRing O)) a := fun _ => rfl
  refine UpperTheory.ringKrullDim_mvPowerSeries_fin_field O (FractionRing O) (MvPowerSeries (Fin n) O) x n φ MvPowerSeries.X 1
    one_ne_zero (fun a => ?_) (fun i => ?_)
  · rw [hφ, MvPowerSeries.constantCoeff_map]; rfl
  · rw [hφ]; simp

theorem UpperTheory.ringKrullDim_eq_height_ker_section_add_one :
    ∀ (O S : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing S] [IsDomain S] [Algebra O S] [IsCO O S] (x : S →ₐ[O] O), ringKrullDim S = ((RingHom.ker x).height : WithBot ℕ∞) + 1 := by
  intro O S _ _ _ _ _ _ _ hS x
  have hn : IsNoetherianRing S := hS.toIsNoetherian
  have hl : IsLocalHom (algebraMap O S) := IsCO.isLocalHom
  obtain ⟨d, F, hinj, hfin, hd, hF⟩ := UpperTheory.exists_finite_injective_mvPowerSeries_compatible_section O S x
  haveI : (RingHom.ker x).IsPrime := RingHom.ker_isPrime _
  refine le_antisymm ?_ ?_
  · let A := MvPowerSeries (Fin d) O
    letI : Algebra A S := F.toRingHom.toAlgebra
    haveI : Module.Finite A S := hfin
    haveI : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).2 hinj
    haveI : IsIntegrallyClosed A := normal_mv O d
    let p : Ideal A := RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) O →+* O)
    haveI : p.IsPrime := RingHom.ker_isPrime _
    haveI : (RingHom.ker x).LiesOver p := ⟨by
      ext a
      rw [Ideal.under_def, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, ← hF]
      rfl⟩
    have h1 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p (RingHom.ker x)
    have h2 : (d : ℕ∞) ≤ (RingHom.ker x).height := by
      rw [h1]; exact (ht_const O d).trans le_self_add
    rw [hd]
    have h3 : ((d + 1 : ℕ) : ℕ∞) ≤ (RingHom.ker x).height + 1 := by
      push_cast; gcongr
    exact_mod_cast h3
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hlt : RingHom.ker x < maximalIdeal S := by
      refine lt_of_le_of_ne (le_maximalIdeal Ideal.IsPrime.ne_top') fun h => ?_
      have h1 : algebraMap O S π ∈ maximalIdeal S := fun h => hπ.not_isUnit (IsLocalHom.map_nonunit π h)
      rw [← h, RingHom.mem_ker, AlgHom.commutes] at h1
      exact hπ.ne_zero h1
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast Ideal.height_add_one_le_of_lt_of_isPrime hlt
