module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfRel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpRoots
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpoCo
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SplittingAlgebraNontrivialFreeGenerated
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem spCo_desc {R L : Type} [CommRing R] [CommRing L] [Algebra R L] {q n : ℕ}
    (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) (a : Fin q → Fin n → L)
    (ha : ∀ j, ∏ i, (Polynomial.X - Polynomial.C (a j i)) = (P j).map (algebraMap R L))
    (F : MvPowerSeries (Fin q × Fin n) R →ₐ[R] L)
    (hX : ∀ p, F (MvPowerSeries.X p) = a p.1 p.2 - algebraMap R L (ut p.1 p.2)) :
    ∃ F' : Sp P ut →ₐ[R] L, ∀ z, F' (Sp.mk P ut z) = F z := by
  classical
  have hC : ∀ r : R, F (MvPowerSeries.C r) = algebraMap R L r := by
    intro r
    have : (MvPowerSeries.C r : MvPowerSeries (Fin q × Fin n) R) = algebraMap R _ r := by
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [this, F.commutes]
  have hle : spIdeal P ut ≤ RingHom.ker F := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨j, k, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have h1 : ∀ i, F (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i)) = a j i := by
      intro i
      rw [map_add (f := _), hC, hX]
      exact add_sub_cancel _ _
    have h2 : (F : MvPowerSeries (Fin q × Fin n) R →+* L).comp MvPowerSeries.C = algebraMap R L :=
      RingHom.ext hC
    rw [← RingHom.coe_coe F, ← Polynomial.coeff_map]
    rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, h2, ← ha j]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe, h1, sub_self,
      Polynomial.coeff_zero]
  exact ⟨Ideal.Quotient.liftₐ _ F fun z hz => hle hz, fun z => rfl⟩

private theorem splitting_algebra_nontrivial_free_generated (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (q n : ℕ) (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R)
    (h : ∀ j, (P j).Monic ∧ (P j).natDegree = n ∧
      (P j).map (residue R) = ∏ i, (Polynomial.X - Polynomial.C (residue R (ut j i)))) :
    Nontrivial (Sp P ut) ∧ Module.Free R (Sp P ut) ∧
      Algebra.adjoin R (Set.range fun p : Fin q × Fin n => Sp.u P ut p.1 p.2) = ⊤ := by
  classical
  obtain ⟨bas, -⟩ := mSplitAlg_basis (Fin q) n R P (fun j => (h j).1) (fun j => (h j).2.1)
  haveI : Module.Free R (MSplitAlg P n) := Module.Free.of_basis bas
  haveI : Module.Finite R (MSplitAlg P n) := Module.Finite.of_basis bas
  have hχ : ∀ j, ∏ i, (Polynomial.X - Polynomial.C (residue R (ut j i))) =
      (P j).map (algebraMap R (ResidueField R)) := by
    intro j
    rw [ResidueField.algebraMap_eq, (h j).2.2]
  obtain ⟨χ, hχr⟩ : ∃ χ : (MSplitAlg P n) →ₐ[R] ResidueField R,
      ∀ j i, χ (MSplitAlg.root P n j i) = residue R (ut j i) :=
    ⟨MSplitAlg.lift P n _ hχ, MSplitAlg.lift_root P n _ hχ⟩
  have hχalg : ∀ r : R, χ (algebraMap R (MSplitAlg P n) r) = residue R r := by
    intro r
    rw [χ.commutes, ResidueField.algebraMap_eq]
  have hχs : Function.Surjective χ := by
    intro y
    obtain ⟨r, rfl⟩ := residue_surjective y
    exact ⟨_, hχalg r⟩
  obtain ⟨n0, hn0⟩ : ∃ n0 : Ideal (MSplitAlg P n), n0 = RingHom.ker χ := ⟨_, rfl⟩
  haveI : n0.IsMaximal := hn0 ▸ RingHom.ker_isMaximal_of_surjective χ hχs
  obtain ⟨hBs, hBfin, hBloc, hBcpl, hBfree, -, hBuniv⟩ := local_factor R (MSplitAlg P n) n0
  haveI := hBfin
  haveI := hBloc
  haveI : Module.Free R (Localization.AtPrime n0) := hBfree inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime n0) := isNoetherian_of_tower R (inferInstance : IsNoetherian R (Localization.AtPrime n0))
  have hmem0 : ∀ y, y ∈ n0 ↔ χ y = 0 := fun y => by rw [hn0, RingHom.mem_ker]
  have hinB : ∀ y ∈ n0, algebraMap (MSplitAlg P n) (Localization.AtPrime n0) y ∈ maximalIdeal (Localization.AtPrime n0) := fun y hy =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime n0) n0 y).2 hy
  have hroot : ∀ j i, MSplitAlg.root P n j i - algebraMap R (MSplitAlg P n) (ut j i) ∈ n0 := by
    intro j i
    rw [hmem0, map_sub, hχalg, hχr, sub_self]
  haveI hRR : IsCO R R := @IsCO.mk R R _ _ _ _ _ _ inferInstance ⟨fun a ha => ha⟩
    (fun x => ⟨x, by rw [Algebra.algebraMap_self, RingHom.id_apply, sub_self]; exact zero_mem _⟩)
  haveI hRB : IsCO R (Localization.AtPrime n0) := @IsCO.mk R (Localization.AtPrime n0) _ _ _ _ _ _ hBcpl hBloc (fun x => by
    obtain ⟨y, rfl⟩ := hBs x
    obtain ⟨r, hr⟩ := residue_surjective (χ y)
    refine ⟨r, ?_⟩
    rw [IsScalarTower.algebraMap_apply R (MSplitAlg P n) (Localization.AtPrime n0), ← (algebraMap (MSplitAlg P n) (Localization.AtPrime n0)).map_sub y (algebraMap R (MSplitAlg P n) r)]
    apply hinB
    rw [hmem0, map_sub, hχalg, hr, sub_self])
  have hmemB : ∀ p : Fin q × Fin n, algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n p.1 p.2) -
      algebraMap R (Localization.AtPrime n0) (ut p.1 p.2) ∈ maximalIdeal (Localization.AtPrime n0) := by
    intro p
    rw [IsScalarTower.algebraMap_apply R (MSplitAlg P n) (Localization.AtPrime n0), ← (algebraMap (MSplitAlg P n) (Localization.AtPrime n0)).map_sub (MSplitAlg.root P n p.1 p.2) (algebraMap R (MSplitAlg P n) (ut p.1 p.2))]
    exact hinB _ (hroot p.1 p.2)
  obtain ⟨F, ⟨hFC, hFX⟩, -⟩ := co_ev R R (Localization.AtPrime n0) (Fin q × Fin n) (Algebra.ofId R (Localization.AtPrime n0))
    (fun p => algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n p.1 p.2) - algebraMap R (Localization.AtPrime n0) (ut p.1 p.2)) hmemB
  have hFX' : ∀ p : Fin q × Fin n, F (MvPowerSeries.X p) =
      algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n p.1 p.2) - algebraMap R (Localization.AtPrime n0) (ut p.1 p.2) := hFX
  have hFC' : ∀ x : R, F (MvPowerSeries.C x) = algebraMap R (Localization.AtPrime n0) x := fun x => hFC x
  have hrootB : ∀ j, ∏ i, (Polynomial.X - Polynomial.C (algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n j i))) =
      (P j).map (algebraMap R (Localization.AtPrime n0)) := by
    intro j
    have := congrArg (Polynomial.map (algebraMap (MSplitAlg P n) (Localization.AtPrime n0))) (MSplitAlg.prod_root P n j)
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
    rw [← this, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  obtain ⟨Φ, hΦ⟩ := spCo_desc P ut (fun j i => algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n j i)) hrootB F hFX
  haveI : Nontrivial (Sp P ut) := Φ.toRingHom.domain_nontrivial
  haveI : IsLocalRing (Sp P ut) := IsLocalRing.of_surjective' (Sp.mk P ut).toRingHom
    (fun z => Ideal.Quotient.mk_surjective z)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (MSplitAlg P n) →ₐ[R] Sp P ut, ∀ j i, Ψ (MSplitAlg.root P n j i) = Sp.u P ut j i :=
    ⟨MSplitAlg.lift P n _ (fun j => (spRoots R q n P ut j).1), MSplitAlg.lift_root P n _ _⟩
  obtain ⟨F0, hF0X, hF0C⟩ : ∃ F0 : MvPowerSeries (Fin q × Fin n) R →ₐ[R] ResidueField R,
      (∀ p, F0 (MvPowerSeries.X p) = 0) ∧ ∀ r, F0 (MvPowerSeries.C r) = residue R r :=
    ⟨{ toRingHom := (residue R).comp MvPowerSeries.constantCoeff
       commutes' := fun r => by
         show residue R (MvPowerSeries.constantCoeff (algebraMap R (MvPowerSeries (Fin q × Fin n) R) r)) = _
         rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
           MvPowerSeries.constantCoeff_C, ResidueField.algebraMap_eq] },
     fun p => by
       show residue R (MvPowerSeries.constantCoeff (MvPowerSeries.X p)) = 0
       rw [MvPowerSeries.constantCoeff_X, map_zero],
     fun r => by
       show residue R (MvPowerSeries.constantCoeff (MvPowerSeries.C r)) = _
       rw [MvPowerSeries.constantCoeff_C]⟩
  have hF0X' : ∀ p : Fin q × Fin n, F0 (MvPowerSeries.X p) =
      residue R (ut p.1 p.2) - algebraMap R (ResidueField R) (ut p.1 p.2) := by
    intro p
    rw [hF0X, ResidueField.algebraMap_eq, sub_self]
  obtain ⟨χ', hχ'⟩ := spCo_desc P ut (fun j i => residue R (ut j i)) hχ F0 hF0X'
  have hχ'alg : ∀ r : R, χ' (algebraMap R (Sp P ut) r) = residue R r := by
    intro r
    rw [χ'.commutes, ResidueField.algebraMap_eq]
  have hχ's : Function.Surjective χ' := by
    intro y
    obtain ⟨r, rfl⟩ := residue_surjective y
    exact ⟨_, hχ'alg r⟩
  have hkerχ' : RingHom.ker χ' = maximalIdeal (Sp P ut) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective χ' hχ's)
  have hχΨ : χ'.comp Ψ = χ := by
    apply MSplitAlg.hom_ext
    intro j i
    rw [AlgHom.comp_apply, hΨ, hχr]
    show χ' (Sp.mk P ut _) = _
    rw [hχ', map_add (f := _), hF0C, hF0X, add_zero]
  have hcomap : Ideal.comap Ψ.toRingHom (maximalIdeal (Sp P ut)) = n0 := by
    refine Ideal.ext fun y => ?_
    rw [Ideal.mem_comap, ← hkerχ', hmem0, RingHom.mem_ker]
    show χ' (Ψ y) = 0 ↔ χ y = 0
    rw [← AlgHom.comp_apply, hχΨ]
  obtain ⟨g0, hg0⟩ := hBuniv (Sp P ut) Ψ.toRingHom hcomap
  have hg0' : ∀ y, g0 (algebraMap (MSplitAlg P n) (Localization.AtPrime n0) y) = Ψ y := fun y => RingHom.congr_fun hg0 y
  obtain ⟨g, hg⟩ : ∃ g : (Localization.AtPrime n0) →ₐ[R] Sp P ut, ∀ y, g (algebraMap (MSplitAlg P n) (Localization.AtPrime n0) y) = Ψ y :=
    ⟨{ g0 with
        commutes' := fun r => by
          show g0 (algebraMap R (Localization.AtPrime n0) r) = _
          rw [IsScalarTower.algebraMap_apply R (MSplitAlg P n) (Localization.AtPrime n0), hg0', Ψ.commutes] }, hg0'⟩
  have hΦu : ∀ j i, Φ (Sp.u P ut j i) = algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n j i) := by
    intro j i
    show Φ (Sp.mk P ut _) = _
    rw [hΦ, map_add (f := _), hFC', hFX']
    exact add_sub_cancel _ _
  have hΦg : Φ.comp g = AlgHom.id R (Localization.AtPrime n0) := by
    have h1 : (Φ.comp g).comp (IsScalarTower.toAlgHom R (MSplitAlg P n) (Localization.AtPrime n0)) = IsScalarTower.toAlgHom R (MSplitAlg P n) (Localization.AtPrime n0) := by
      apply MSplitAlg.hom_ext
      intro j i
      rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hg, hΨ, hΦu]
    refine AlgHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := hBs x
    exact AlgHom.congr_fun h1 y
  haveI : IsCO R (MvPowerSeries (Fin q × Fin n) R) := co_mvps R R (Fin q × Fin n)
  haveI : IsCO R (Sp P ut) := co_quot R (MvPowerSeries (Fin q × Fin n) R) (Sp P ut) (Sp.mk P ut)
    (fun z => Ideal.Quotient.mk_surjective z)
  have hmemSp : ∀ p : Fin q × Fin n, Sp.mk P ut (MvPowerSeries.X p) ∈ maximalIdeal (Sp P ut) := by
    intro p
    rw [← hkerχ', RingHom.mem_ker, hχ', hF0X]
  obtain ⟨F1, -, huniq⟩ := co_ev R R (Sp P ut) (Fin q × Fin n) (Algebra.ofId R (Sp P ut))
    (fun p => Sp.mk P ut (MvPowerSeries.X p)) hmemSp
  have hCalg : ∀ (f : MvPowerSeries (Fin q × Fin n) R →ₐ[R] Sp P ut) (x : R),
      f (MvPowerSeries.C x) = Algebra.ofId R (Sp P ut) x := by
    intro f x
    have : (MvPowerSeries.C x : MvPowerSeries (Fin q × Fin n) R) = algebraMap R _ x := by
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [this, f.commutes, Algebra.ofId_apply]
  have hX1 : ∀ p : Fin q × Fin n, ((g.comp Φ).comp (Sp.mk P ut)) (MvPowerSeries.X p) =
      Sp.mk P ut (MvPowerSeries.X p) := by
    intro p
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hΦ, hFX', map_sub, AlgHom.commutes, hg, hΨ]
    exact (spRoots R q n P ut p.1).2 p.2
  have hgΦ : g.comp Φ = AlgHom.id R (Sp P ut) := by
    apply Ideal.Quotient.algHom_ext
    exact (huniq _ ⟨hCalg _, hX1⟩).trans (huniq _ ⟨hCalg _, fun p => rfl⟩).symm
  let e : Sp P ut ≃ₐ[R] (Localization.AtPrime n0) := AlgEquiv.ofAlgHom Φ g hΦg hgΦ
  refine ⟨inferInstance, Module.Free.of_equiv e.symm.toLinearEquiv, ?_⟩
  rw [eq_top_iff]
  rintro z -
  obtain ⟨y, hy⟩ := hBs (Φ z)
  have hz : Ψ y = z := by
    rw [← hg y, hy]
    exact AlgHom.congr_fun hgΦ z
  rw [← hz]
  clear hz hy
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction p using MvPolynomial.induction_on with
  | C r =>
    show Ψ (algebraMap R (MSplitAlg P n) r) ∈ _
    rw [Ψ.commutes]
    exact Subalgebra.algebraMap_mem _ r
  | add p1 p2 h1 h2 =>
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem h1 h2
  | mul_X p s hp =>
    rw [map_mul, map_mul]
    refine mul_mem hp (Algebra.subset_adjoin ⟨s, ?_⟩)
    exact (hΨ s.1 s.2).symm

theorem UpperTheory.V.Pa.Core.spCo :
    ∀ (O R : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] (q n : ℕ) (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R), (∀ j, (P j).Monic ∧ (P j).natDegree = n ∧ (P j).map (residue R) = ∏ i, (Polynomial.X - Polynomial.C (residue R (ut j i)))) → IsCO O (Sp P ut) ∧ Module.Free R (Sp P ut) ∧ Module.Finite R (Sp P ut) ∧ Algebra.adjoin R (Set.range fun p : Fin q × Fin n => Sp.u P ut p.1 p.2) = ⊤ := by
  intro O R _ _ _ _ _ q n P ut h
  haveI : IsNoetherianRing R := IsCO.toIsNoetherian (O := O)
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  obtain ⟨hnt, hfree, hadj⟩ := splitting_algebra_nontrivial_free_generated R q n P ut h
  obtain ⟨hfin, -⟩ := BC.sp_fin R q n P ut
  haveI := hnt
  haveI := co_mvps O R (Fin q × Fin n)
  refine ⟨?_, hfree, hfin, hadj⟩
  exact co_quot O (MvPowerSeries (Fin q × Fin n) R) (Sp P ut) ((Sp.mk P ut).restrictScalars O)
    (fun z => Ideal.Quotient.mk_surjective z)
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.spoCo :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T), Adapted T (r := r) → (IsCO O (Spo A) ∧ Module.Free B (Spo A) ∧ Module.Finite B (Spo A) ∧ Algebra.adjoin B (Set.range fun p : Fin T.q × Fin n => (Sp.u _ _ p.1 p.2 : Spo A)) = ⊤) ∧ ∀ N, IsCO O (SpAt u (fun j => (T.h N).p₀ (T.ph N j)) A.ut) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A hA
  refine ⟨spCo O B T.q n _ _ fun j => chiRes l G0.frame n O r B u (T.sg j) (A.ut j) (A.ut_res j), fun N => ?_⟩
  exact (spCo O B T.q n _ _ fun j => chiRes l G0.frame n O r B u ((T.h N).p₀ (T.ph N j)) (A.ut j) fun i => by
    have h1 := hA.1 ((T.h N).p₀ (T.ph N j) * (T.sg j)⁻¹) (T.ph_H N j) i
    have h2 := ((r.chib i).map_mul _ _).symm.trans h1
    have h3 := (congrArg (r.chib i ((T.h N).p₀ (T.ph N j)) * ·) ((r.chib i).map_inv (T.sg j))).symm.trans h2
    exact (A.ut_res j i).trans (congrArg Units.val (mul_inv_eq_one.1 h3).symm)).1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PhSees
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem sees_mono {n : ℕ} {R G : Type} [CommRing R] [Group G] (D : GDet n R G) (V V' : Subgroup G)
    [V.Normal] [V'.Normal] (h : V' ≤ V) (I : Ideal R) (hV : Sees D V I) : Sees D V' I := by
  intro i x y hxy
  apply hV i x y
  have h' : V' ≤ V.comap (MonoidHom.id G) := fun g hg => h hg
  have key : ∀ z : MonoidAlgebra R G, MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' V) z =
      MonoidAlgebra.mapDomainRingHom R (QuotientGroup.map V' V (MonoidHom.id G) h')
        (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' V') z) := by
    intro z
    simp only [MonoidAlgebra.mapDomainRingHom_apply]
    apply MonoidAlgebra.coeff_injective
    simp only [MonoidAlgebra.coeff_mapDomain]
    rw [← Finsupp.mapDomain_comp]
    rfl
  rw [key, key, hxy]

theorem UpperTheory.V.Pa.Core.phSees :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (j : ℕ), ∃ V : OpenNormalSubgroup Λ.Ph, V.toSubgroup ≤ Ph0 Λ ∧ Sees W.t.D (V.toSubgroup.subgroupOf (Ph0 Λ)) (maximalIdeal W.R ^ j) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W j
  letI := W.ring
  letI := W.alg
  haveI := W.co
  obtain ⟨V, hV⟩ := dSees n W.R (Ph0 Λ) W.t.D (maximalIdeal W.R) W.t.cont j
  have hUo : IsOpen (Subtype.val '' (V : Set (Ph0 Λ))) :=
    (Λ.Ph0_open).isOpenMap_subtype_val _ V.toOpenSubgroup.isOpen
  have h1U : (1 : Λ.Ph) ∈ Subtype.val '' (V : Set (Ph0 Λ)) := ⟨1, V.one_mem, rfl⟩
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo h1U
  have hHle : H.toSubgroup ≤ Ph0 Λ := by
    intro g hg
    obtain ⟨x, -, rfl⟩ := hH hg
    exact x.2
  refine ⟨H, hHle, ?_⟩
  refine sees_mono W.t.D _ _ ?_ _ hV
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨y, hy, hxy⟩ := hH hx
  have hyx : y = x := Subtype.ext hxy
  rw [← hyx]
  exact hy
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.OoMaps
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem comap_inj {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G)
    (hφ : Function.Surjective φ) {D D' : GDet n A G} (h : D.comap φ = D'.comap φ) : D = D' := by
  refine GDet.ext fun B _ _ x => ?_
  obtain ⟨y, hy⟩ := Finsupp.mapDomain_surjective hφ x.coeff
  have hx : MonoidAlgebra.mapDomainRingHom B φ (MonoidAlgebra.ofCoeff y) = x := by
    apply MonoidAlgebra.coeff_injective
    simp [MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.mapDomain, hy]
  rw [← hx]
  exact congrArg (fun E : GDet n A H => E.D B (MonoidAlgebra.ofCoeff y)) h

private theorem comap_comp' {n : ℕ} {A G H K : Type} [CommRing A] [Group G] [Group H] [Group K] (φ : H →* G)
    (ψ : K →* H) (D : GDet n A G) : (D.comap φ).comap ψ = D.comap (φ.comp ψ) := by
  refine GDet.ext fun B _ _ x => ?_
  simp [GDet.comap, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_comp]

private theorem map_comap' {n : ℕ} {A A' G H : Type} [CommRing A] [CommRing A'] [Group G] [Group H] (φ : H →* G)
    (f : A →+* A') (D : GDet n A G) : (D.map f).comap φ = (D.comap φ).map f := by
  rfl

theorem UpperTheory.V.Pa.Core.ooMaps :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) [IsCO O (W.R ⧸ ii W)] (o : OoPair W) (πb : (W.R ⧸ ii W) →ₐ[O] Spo A), (∀ a, πb (Ideal.Quotient.mk (ii W) a) = m.π a) → o.p.Maps πb.toRingHom ((u.D.comap Λ.h.p₀).map (algebraMap B (Spo A))) fun v i => pushCh (algebraMap B (Spo A)) (u.ψ v i) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m _ o πb hπ
  have hc : πb.toRingHom.comp (Ideal.Quotient.mk (ii W)) = m.π.toRingHom := RingHom.ext hπ
  refine ⟨?_, fun v i => ?_⟩
  · refine comap_inj (πo0 Λ) Λ.πo0_surj ?_
    rw [map_comap', map_comap', o.D_eq, (UpperTheory.V.CA.d_gmap W.t.D).2.1, hc, comap_comp']
    exact m.π_maps.1
  · have h2 := m.π_maps.2.1 v i
    refine Eq.trans ?_ h2
    rw [o.ψ_eq, ← hc]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.RrExt
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.TupMap
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem mem_map {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {y : R} (hy : y ∈ maximalIdeal R) :
    f y ∈ maximalIdeal R' := by
  rw [← res_eq_zero_iff O R'] at *
  rw [res_map]
  exact (res_eq_zero_iff O R y).mpr hy

private theorem adic_map {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => f (a g) := by
  intro N
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap f.toRingHom := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    apply Ideal.pow_right_mono
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact mem_map f hx
  have key := (ha N).comp (Ideal.quotientMap (maximalIdeal R' ^ N) f.toRingHom hle)
  convert key using 1
  funext g
  simp [Ideal.quotientMap_mk]

theorem UpperTheory.V.Pa.Core.tupMap :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (R R' : Type) [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (t : Tup Λ A R) (f : R →ₐ[O] R'), ∃ t' : Tup Λ A R', t.Maps f.toRingHom t'.D t'.ψ t'.s t'.U t'.y := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A R R' _ _ _ _ _ _ t f
  refine ⟨⟨t.D.map f.toRingHom, ?_, ?_, fun v i => pushCh f.toRingHom (t.ψ v i), ?_, f t.s, mem_map f t.s_mem,
    fun j i => f (t.U j i), ?_, fun j i => f (t.y j i), fun j i => mem_map f (t.y_mem j i)⟩,
    rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro i
    have h := adic_map f (t.cont i)
    convert h using 2 with g
    have := ((UpperTheory.V.CA.d_gmap t.D).2.2.1 f.toRingHom (MonoidAlgebra.single g 1)).2 i
    simpa using this
  · rw [(UpperTheory.V.CA.d_gmap t.D).2.1]
    have : (res O R' : R' →+* ResidueField O).comp f.toRingHom = (res O R : R →+* ResidueField O) := by
      ext x
      exact res_map f x
    rw [this]
    exact t.red
  · intro v i
    have hp := t.psi v i
    refine ⟨?_, ?_, ?_⟩
    · exact adic_map f hp.cont
    · intro g
      simpa [res_map] using hp.red g
    · intro g
      simpa using congrArg f (hp.mu g)
  · intro j i
    have h := mem_map f (t.U_mem j i)
    simpa using h
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.rrExt :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : W.R →ₐ[O] R'), (∀ i g, f (W.t.D.lam i (MonoidAlgebra.single g 1)) = f' (W.t.D.lam i (MonoidAlgebra.single g 1))) → (∀ v i g, f (W.t.ψ v i g) = f' (W.t.ψ v i g)) → f W.t.s = f' W.t.s → (∀ j i, f (W.t.U j i) = f' (W.t.U j i)) → (∀ j i, f (W.t.y j i) = f' (W.t.y j i)) → f = f' := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W R' _ _ _ f f' hD hψ hs hU hy
  obtain ⟨t', ht'⟩ := UpperTheory.V.Pa.Core.tupMap l L G0 T Λ n O r B u J D A W.R R' W.t f
  obtain ⟨-, -, hlam, -⟩ := UpperTheory.V.CA.d_gmap W.t.D
  have hl : ∀ (φ : W.R →+* R') i (g : Ph0 Λ), (W.t.D.map φ).lam i (MonoidAlgebra.single g 1) =
      φ (W.t.D.lam i (MonoidAlgebra.single g 1)) := fun φ i g => by
    have := (hlam φ (MonoidAlgebra.single g 1)).2 i
    rwa [MonoidAlgebra.mapRingHom_single, map_one] at this
  refine (W.univ R' t').unique ht' ?_
  obtain ⟨h1, h2, h3, h4, h5⟩ := ht'
  refine ⟨?_, fun v i => ?_, ?_, fun j i => ?_, fun j i => ?_⟩
  · rw [← h1]
    refine UpperTheory.V.CA.d_gext _ _ fun g i _ _ => ?_
    rw [hl, hl]
    exact (hD i g).symm
  · rw [← h2]
    ext g
    exact (hψ v i g).symm
  · exact hs.symm.trans h3
  · exact (hU j i).symm.trans (h4 j i)
  · exact (hy j i).symm.trans (h5 j i)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.T3Of
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.t3Of :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) (a : W.R), (∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, a - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0)) → IsApproximateAnnihilatorAtLevels m a := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m a h j
  filter_upwards [h j, Λ.U_le (Filter.eventually_ge_atTop j)] with N hN hjN
  obtain ⟨a', ha', hor⟩ := hN
  obtain ⟨hf, hρf, -⟩ := foCong l L G0 T Λ n O r B u J D A W m j N hjN
  refine ⟨(fEl (T.Nq N) W.t.U * a') ^ (A.ex + 1), ?_, ?_⟩
  · have h1 : fo W * a - fEl (T.Nq N) W.t.U * a' ∈ maximalIdeal W.R ^ j := by
      have e : fo W * a - fEl (T.Nq N) W.t.U * a' =
          (fo W - fEl (T.Nq N) W.t.U) * a + fEl (T.Nq N) W.t.U * (a - a') := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ ha')
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (fo W * a) (fEl (T.Nq N) W.t.U * a') (A.ex + 1)
    rw [hc]
    exact Ideal.mul_mem_right _ _ h1
  · intro x
    rw [MN.smul_def, map_pow, map_mul, hρf]
    rcases hor with h0 | h0
    · rw [h0, mul_zero, zero_pow (Nat.succ_ne_zero _), zero_smul]
    · rw [pow_succ', mul_smul]
      exact (congrArg (fun y : (A.A N).M => (fEl (T.Nq N) (A.A N).U * (m.ρ N) a') • y) (h0 x)).trans
        (smul_zero _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.CharpolyElementEqAevalGroupElement
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem ch_ker {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E) :
    Polynomial.aeval x (D.chi x) ∈ D.ker := by
  apply UpperTheory.V.CA.d_ch_ker D
  have h1 := (UpperTheory.V.CA.d_chS D A).1 ((1 : A) ⊗ₜ[A] x)
  have hchi : D.chiS A ((1 : A) ⊗ₜ[A] x) = D.chi x := by
    unfold Det.chiS Det.chi
    simp [Algebra.TensorProduct.map_tmul]
  rw [hchi] at h1
  have he : Polynomial.aeval x (D.chi x) =
      Algebra.TensorProduct.lid A E (Polynomial.aeval ((1 : A) ⊗ₜ[A] x) (D.chi x)) := by
    rw [← Polynomial.aeval_algHom_apply]
    simp
  rw [he]
  have key : ∀ w ∈ Submodule.span A ((fun z : E => (1 : A) ⊗ₜ[A] z) '' (D.CH : Set E)),
      Algebra.TensorProduct.lid A E w ∈ D.CH := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, hc, rfl⟩ := hz
      simpa using hc
    | zero => simpa using TwoSidedIdeal.zero_mem _
    | add a b _ _ ha hb =>
      rw [map_add (f := _)]
      exact TwoSidedIdeal.add_mem _ ha hb
    | smul a z _ hz =>
      rw [map_smul, Algebra.smul_def]
      exact TwoSidedIdeal.mul_mem_left _ _ _ hz
  exact key _ h1

private theorem tr_ker {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (hn : 1 ≤ n)
    {y : MonoidAlgebra A G} (hy : y ∈ D.toDet.ker) (h : MonoidAlgebra A G) : D.tr (h * y) = 0 := by
  have hk := (UpperTheory.V.CA.d_ker D.toDet y).2.2 hy h 1 le_rfl hn
  have htr : D.toDet.tr (h * y) = D.toDet.lam 1 (h * y) := by
    unfold Det.tr Det.lam
    rfl
  rw [← (UpperTheory.V.CA.d_toDet D (h * y)).2.2.1, htr, hk]

private theorem charpoly_element_eq_aeval_group_element {n : ℕ} {A G : Type} [CommRing A] [Group G] (g : G) (U : Fin n → A) :
    q1El g U = Polynomial.aeval (MonoidAlgebra.single g (1 : A)) (∏ i, (Polynomial.X - Polynomial.C (U i))) := by
  unfold q1El
  rw [← Fin.prod_ofFn, map_list_prod, List.map_ofFn]
  congr 1
  congr 1
  funext i
  simp [MonoidAlgebra.coe_algebraMap]

private noncomputable def push {R S H G : Type} [CommRing R] [CommRing S] [Group H] [Group G] (f : R →+* S)
    (φ : H →* G) : MonoidAlgebra R H →+* MonoidAlgebra S G :=
  (MonoidAlgebra.mapDomainRingHom S φ).comp (MonoidAlgebra.mapRingHom H f)

private theorem push_single {R S H G : Type} [CommRing R] [CommRing S] [Group H] [Group G] (f : R →+* S)
    (φ : H →* G) (g : H) (a : R) : push f φ (MonoidAlgebra.single g a) = MonoidAlgebra.single (φ g) (f a) := by
  simp [push, MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.mapRingHom]

private theorem gDet_lam_map_comap_eq_lam_mapDomainRingHom {n : ℕ} {B S H G : Type} [CommRing B] [CommRing S] [Group H] [Group G]
    (D : GDet n B G) (a : B →+* S) (φ : H →* G) (i : ℕ) (z : MonoidAlgebra S H) :
    ((D.comap φ).map a).lam i z = (D.map a).lam i (MonoidAlgebra.mapDomainRingHom S φ z) := by
  have key : MonoidAlgebra.mapDomainRingHom (Polynomial S) φ
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom H Polynomial.C z) =
      MonoidAlgebra.single 1 Polynomial.X -
        MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom S φ z) := by
    rw [map_sub]
    congr 1
    · simp [MonoidAlgebra.mapDomainRingHom]
    · induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add p q hp hq => simp only [map_add (f := _), hp, hq]
      | single h s =>
        simp [MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.mapRingHom, MonoidAlgebra.mapDomain_single]
  unfold GDet.lam GDet.map GDet.comap GDet.chi
  dsimp only
  rw [MonoidHom.comp_apply]
  erw [key]

private theorem lam_push {n : ℕ} {R B S H G : Type} [CommRing R] [CommRing B] [CommRing S] [Group H] [Group G]
    {E : GDet n R H} {D : GDet n B G} {f : R →+* S} {a : B →+* S} {φ : H →* G}
    (h : E.map f = (D.comap φ).map a) (i : ℕ) (y : MonoidAlgebra R H) :
    f (E.lam i y) = (D.map a).lam i (push f φ y) := by
  rw [← ((UpperTheory.V.CA.d_gmap E).2.2.1 f y).2 i, h, gDet_lam_map_comap_eq_lam_mapDomainRingHom]
  rfl

theorem UpperTheory.V.Pa.Core.piKer :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), 1 ≤ n → Adapted T (r := r) → ii W ≤ RingHom.ker m.π := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hn hAd
  obtain ⟨hD, hψ, hs, hU, hy⟩ := m.π_maps
  have hL : ∀ i y, m.π.toRingHom (W.t.D.lam i y) =
      (u.D.map (algebraMap B (Spo A))).lam i (push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) y) :=
    fun i y => lam_push hD i y
  have hT : ∀ y, m.π (W.t.D.tr y) =
      (u.D.map (algebraMap B (Spo A))).tr (push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) y) :=
    fun y => hL 1 y
  have hz : ∀ h y, y ∈ (u.D.map (algebraMap B (Spo A))).toDet.ker →
      (u.D.map (algebraMap B (Spo A))).tr (h * y) = 0 :=
    fun h y hy => tr_ker _ hn hy h
  have hz0 : (u.D.map (algebraMap B (Spo A))).tr 0 = 0 := by
    simpa using hz 1 0 (TwoSidedIdeal.zero_mem _)
  have hmapTr : ∀ x, (u.D.map (algebraMap B (Spo A))).tr
      (MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A)) x) = algebraMap B (Spo A) (u.D.tr x) :=
    fun x => ((UpperTheory.V.CA.d_gmap u.D).2.2.1 (algebraMap B (Spo A)) x).2 1
  have hc : (push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ))).comp
      (algebraMap W.R (MonoidAlgebra W.R (Ph0 Λ))) =
      (algebraMap (Spo A) (MonoidAlgebra (Spo A) G0.frame.G₀)).comp m.π.toRingHom := by
    ext c
    simp [push_single, MonoidAlgebra.coe_algebraMap]
  rw [ii, Ideal.span_le]
  intro x hx
  rw [SetLike.mem_coe, RingHom.mem_ker]
  induction hx
  next h k hk =>
    rw [hT, map_mul, map_sub, map_one, push_single, push_single]
    simp [hk, ← MonoidAlgebra.one_def, hz0]
  next i g g' hg =>
    have hL' : ∀ i y, m.π (W.t.D.lam i y) =
        (u.D.map (algebraMap B (Spo A))).lam i (push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) y) := hL
    have hlam : ∀ z, (u.D.map (algebraMap B (Spo A))).lam i
        (MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A)) z) = algebraMap B (Spo A) (u.D.lam i z) :=
      fun z => ((UpperTheory.V.CA.d_gmap u.D).2.2.1 (algebraMap B (Spo A)) z).2 i
    have heps : ∀ (x : Λ.G.G₀) (k : ℤ), m.π (((Λ.G.frame.eps O W.R x ^ k : W.Rˣ)) : W.R) =
        (((G0.frame.eps O (Spo A) (Λ.h.p₀ x) ^ k : (Spo A)ˣ)) : Spo A) := by
      intro x k
      rw [Λ.h.eps_p₀]
      have hu : Units.map (m.π : W.R →* Spo A) (Λ.G.frame.eps O W.R x) = Λ.G.frame.eps O (Spo A) x := by
        ext
        simp [GFrame.eps, pushCh]
      rw [← hu]
      exact congrArg Units.val (map_zpow (Units.map (m.π : W.R →* Spo A)) (Λ.G.frame.eps O W.R x) k)
    have hepsB : ∀ (y : G0.G₀) (k : ℤ), algebraMap B (Spo A) (((G0.frame.eps O B y ^ k : Bˣ)) : B) =
        (((G0.frame.eps O (Spo A) y ^ k : (Spo A)ˣ)) : Spo A) := by
      intro y k
      have hu : Units.map (algebraMap B (Spo A) : B →* Spo A) (G0.frame.eps O B y) = G0.frame.eps O (Spo A) y := by
        ext
        simp [GFrame.eps, pushCh, ← IsScalarTower.algebraMap_apply]
      rw [← hu]
      exact congrArg Units.val (map_zpow (Units.map (algebraMap B (Spo A) : B →* Spo A)) (G0.frame.eps O B y) k)
    have hconj : πo0 Λ g' = Λ.G.frame.conj (πo0 Λ g) := by
      clear hL hT hz hz0 hmapTr hs hD hAd hy hU hc hψ hL' hlam heps hepsB
      apply Subtype.ext
      show Λ.πo (g' : Λ.Ph) = Λ.G.c * Λ.πo (g : Λ.Ph) * Λ.G.c⁻¹
      rw [hg, map_mul, map_mul, map_inv, Λ.ct_o]
    have h1 : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ))
        (MonoidAlgebra.single g'⁻¹ (((Λ.G.frame.eps O W.R (πo0 Λ g) ^ (1 - (n : ℤ)) : W.Rˣ)) : W.R)) =
        MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A))
          (G0.frame.star O B n (MonoidAlgebra.single (Λ.h.p₀ (πo0 Λ g)) 1)) := by
      unfold GFrame.star GFrame.starOp
      rw [MonoidAlgebra.lift_single, one_smul]
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]
      rw [MonoidAlgebra.mapRingHom_single, push_single]
      congr 1
      · rw [map_inv, MonoidHom.comp_apply, hconj, Λ.h.p₀_conj]
      · rw [hepsB]
        exact heps _ _
    have h2 : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) (MonoidAlgebra.single g 1) =
        MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A))
          (MonoidAlgebra.single (Λ.h.p₀ (πo0 Λ g)) 1) := by
      rw [push_single, MonoidAlgebra.mapRingHom_single, map_one, map_one, MonoidHom.comp_apply]
    rw [map_sub, hL', hL', h1, h2, hlam, hlam, u.P, sub_self]
  next v g ga h hga =>
    have hpt : ∀ i, m.π.toRingHom ((W.t.ψ v i (g i) : W.R)) =
        algebraMap B (Spo A) ((u.ψ v i (g i) : B)) := by
      intro i
      have := congrArg (fun χ : L.Gv v →* (Spo A)ˣ => ((χ (g i) : (Spo A)ˣ) : Spo A)) (hψ v i)
      simpa [pushCh] using this
    have hp : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ))
        (MonoidAlgebra.single h 1 * (List.ofFn fun i => MonoidAlgebra.single (ga i) 1 -
          MonoidAlgebra.single 1 ((W.t.ψ v i (g i) : W.R))).prod) =
        MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A))
          (MonoidAlgebra.single (Λ.h.p₀ (πo0 Λ h)) 1 * G0.frame.oEl v (u.ψ v) g) := by
      clear hL hT hz hz0 hmapTr hs hD hAd hy hU hc
      unfold GFrame.oEl
      rw [map_mul, map_mul, push_single, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      congr 1
      · rw [MonoidAlgebra.mapRingHom_single, MonoidHom.comp_apply, map_one, map_one]
      · congr 2
        funext i
        have hpt' : m.π ((W.t.ψ v i (g i) : W.R)) = algebraMap B (Spo A) ((u.ψ v i (g i) : B)) := hpt i
        rw [Function.comp_apply, Function.comp_apply, map_sub, map_sub, push_single, push_single, MonoidAlgebra.mapRingHom_single,
          MonoidAlgebra.mapRingHom_single, MonoidHom.comp_apply, hga, Λ.h.p₀_φ, map_one, map_one]
        exact congrArg (fun c => MonoidAlgebra.single _ 1 - MonoidAlgebra.single 1 c) hpt'
    rw [hT, hp, hmapTr, u.Ord, map_zero]
  next w g ga h hg hga =>
    have hp : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ))
        (MonoidAlgebra.single h 1 * (MonoidAlgebra.single ga 1 - 1)) =
        MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A))
          (MonoidAlgebra.single (Λ.h.p₀ (πo0 Λ h)) 1 * (MonoidAlgebra.single (G0.φu w g) 1 - 1)) := by
      simp only [map_mul, map_sub, map_one, push_single, MonoidAlgebra.mapRingHom_single,
        MonoidHom.comp_apply, hga, Λ.h.p₀_φu]
    have hmem : G0.φu w g ∈ r.Ip w := by
      rw [hAd.2 w]
      exact Subgroup.mem_map_of_mem _ hg
    rw [hT, hp, hmapTr, u.I w _ hmem, map_zero]
  next j ph h hph =>
    have hchi : (u.D.map (algebraMap B (Spo A))).chi (MonoidAlgebra.single (T.sg j) 1) =
        Polynomial.map (algebraMap B (Spo A)) (u.D.chi (MonoidAlgebra.single (T.sg j) 1)) := by
      have := ((UpperTheory.V.CA.d_gmap u.D).2.2.1 (algebraMap B (Spo A))
        (MonoidAlgebra.single (T.sg j) 1)).1
      simpa [MonoidAlgebra.mapRingHom] using this
    have hq : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) (q1El ph (W.t.U j)) =
        Polynomial.aeval (MonoidAlgebra.single (T.sg j) (1 : Spo A))
          ((u.D.map (algebraMap B (Spo A))).chi (MonoidAlgebra.single (T.sg j) 1)) := by
      clear hL hT hz hz0 hmapTr hψ hs hD hAd hy
      rw [charpoly_element_eq_aeval_group_element, Polynomial.aeval_def, Polynomial.hom_eval₂, hc, ← Polynomial.eval₂_map,
        ← Polynomial.aeval_def, push_single, MonoidHom.comp_apply, hph, Λ.p_ph, map_one, hchi,
        Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rw [← (spRoots B T.q n _ _ j).1]
      congr 2
      funext i
      exact congrArg (fun c => Polynomial.X - Polynomial.C c) (hU j i)
    rw [hT, map_mul, push_single, hq]
    apply hz
    have := ch_ker (u.D.map (algebraMap B (Spo A))).toDet (MonoidAlgebra.single (T.sg j) 1)
    rwa [(UpperTheory.V.CA.d_toDet _ _).1] at this
  next j i ph ta h hph hta =>
    have h0 : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ))
        (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 (W.t.y j i)) = 0 := by
      rw [map_sub, map_sub, map_one, push_single, push_single, MonoidHom.comp_apply, hta, Λ.p_ta,
        map_one, hy, MonoidAlgebra.single_zero, sub_zero, ← MonoidAlgebra.one_def, sub_self]
    rw [hT]
    unfold q2El
    rw [map_mul, map_mul, h0, mul_zero, mul_zero, hz0]
end
