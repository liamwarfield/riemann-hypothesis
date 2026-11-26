module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsRest
open IsLocalRing Matrix

namespace GlobalTheory.DualNumberLocal

theorem main : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], ∃ _ : IsLocalRing (DualNumber O), IsNoetherianRing (DualNumber O) ∧ IsAdicComplete (maximalIdeal (DualNumber O)) (DualNumber O) ∧ IsLocalHom (algebraMap O (DualNumber O)) ∧ Function.Surjective (fun x : O => residue (DualNumber O) (algebraMap O (DualNumber O) x)) ∧ ∀ z : DualNumber O, z ∈ maximalIdeal (DualNumber O) ↔ z.fst ∈ maximalIdeal O := by
  intro O _ _ _ _
  haveI hloc : IsLocalRing (DualNumber O) :=
    IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
      simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
      exact isUnit_or_isUnit_one_sub_self _
  haveI : Module.Finite O (DualNumber O) := inferInstanceAs (Module.Finite O (O × O))
  have hmem : ∀ z : DualNumber O, z ∈ maximalIdeal (DualNumber O) ↔ z.fst ∈ maximalIdeal O := by
    intro z
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  refine ⟨hloc, IsNoetherianRing.of_finite O (DualNumber O),
    GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite O (DualNumber O), ?_, ?_, hmem⟩
  · refine ⟨fun a h => ?_⟩
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.isUnit_iff_isUnit_fst,
      TrivSqZeroExt.fst_inl] at h
    exact h
  · intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    refine ⟨z.fst, ?_⟩
    show residue (DualNumber O) (algebraMap O (DualNumber O) z.fst) = residue (DualNumber O) z
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hmem,
      TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl, sub_self]
    exact Ideal.zero_mem _

end GlobalTheory.DualNumberLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartDerivationBoundaryParamMemSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartDerivationBoundaryParamMemSpan
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartDerBd

theorem X_dvd_of_X_mul {σ K : Type} [Field K] {s t : σ} (hst : t ≠ s) {g : MvPowerSeries σ K}
    (h : MvPowerSeries.X s ∣ MvPowerSeries.X t * g) : MvPowerSeries.X s ∣ g := by
  classical
  rw [MvPowerSeries.X_dvd_iff] at h ⊢
  intro n hn
  have h1 := h (n + Finsupp.single t 1) (by simp [Finsupp.single_apply, hst, hn])
  rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul] at h1
  simpa using h1

theorem X_dvd_of_prod_mul {σ K : Type} [Field K] {Idx : Type} (f : Idx → σ) {s : σ}
    (S : Finset Idx) (hS : ∀ j ∈ S, f j ≠ s) {g : MvPowerSeries σ K}
    (h : MvPowerSeries.X s ∣ (∏ j ∈ S, MvPowerSeries.X (f j)) * g) : MvPowerSeries.X s ∣ g := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using h
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, _root_.mul_assoc] at h
    exact ih (fun j hj => hS j (Finset.mem_insert_of_mem hj))
      (X_dvd_of_X_mul (hS a (Finset.mem_insert_self a S)) h)

theorem deriv_bdParam_mem_span : ∀ (A : Type) [CommRing A] (k : Type) [Field k] (m d : ℕ) (ψ : A →+* ChartRing k m d) (δ : Derivation ℤ A A) (D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (I : Ideal A), (∀ a ∈ I, δ a ∈ I) → (∀ a, D' (ψ a) = ψ (δ a)) → I.map ψ = Ideal.span {∏ i, bdParam k m d i} → ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  classical
  intro A _ k _ m d ψ δ D' I hI hD hJ i

  have hpres : ∀ x ∈ I.map ψ, D' x ∈ I.map ψ := by
    intro x hx
    rw [Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      rw [hD]
      exact Ideal.mem_map_of_mem ψ (hI a ha)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy
    | smul r x hxm hx =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ r hx)
        (Ideal.mul_mem_right _ _ (Ideal.span_le.2 (fun y hy => Ideal.subset_span hy) hxm))
  set t := bdParam k m d with ht
  have hP : t i * ∏ j ∈ Finset.univ.erase i, t j = ∏ j, t j := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have hmem : D' (∏ j, t j) ∈ Ideal.span {∏ j, t j} := by
    rw [← hJ]; apply hpres; rw [hJ]; exact Ideal.subset_span rfl
  rw [Ideal.mem_span_singleton] at hmem ⊢
  rw [← hP, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hmem
  have h1 : t i ∣ t i * D' (∏ j ∈ Finset.univ.erase i, t j) + (∏ j ∈ Finset.univ.erase i, t j) * D' (t i) :=
    (dvd_mul_right (t i) _).trans hmem
  have h2 : t i ∣ (∏ j ∈ Finset.univ.erase i, t j) * D' (t i) :=
    (dvd_add_right (dvd_mul_right _ _)).1 h1
  exact X_dvd_of_prod_mul (fun j : Fin m => (Sum.inl j : Fin m ⊕ Fin d)) (Finset.univ.erase i)
    (fun j hj h => (Finset.ne_of_mem_erase hj) (Sum.inl_injective h)) h2

end GlobalTheory.ChartDerBd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartDerivationBoundaryParamMemSpanStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricChart_derivation_boundaryParam_mem_span : ∀ (A : Type) [CommRing A] (k : Type) [Field k] (m d : ℕ) (ψ : A →+* ChartRing k m d) (δ : Derivation ℤ A A) (D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (I : Ideal A), (∀ a ∈ I, δ a ∈ I) → (∀ a, D' (ψ a) = ψ (δ a)) → I.map ψ = Ideal.span {∏ i, bdParam k m d i} → ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  first | exact @GlobalTheory.ChartDerBd.deriv_bdParam_mem_span | exact GlobalTheory.ChartDerBd.deriv_bdParam_mem_span | (intros; apply GlobalTheory.ChartDerBd.deriv_bdParam_mem_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendStalkOfIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendStalkOfIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.StalkDer

theorem derivation_extend_stalk_of_iso : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsIso f] (U : X.affineOpens) (d : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (x : X') (hx : x ∈ f ⁻¹ᵁ U.1), ∃ δ : Derivation ℤ (X'.presheaf.stalk x) (X'.presheaf.stalk x), ∀ r, δ ((X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom ((f.app U.1).hom r)) = (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom ((f.app U.1).hom (d r)) := by
  intro X X' f _ U d x hx
  have hU' : IsAffineOpen (f ⁻¹ᵁ U.1) := U.2.preimage f
  let φ : Γ(X, U.1) ≃+* Γ(X', f ⁻¹ᵁ U.1) := (asIso (f.app U.1)).commRingCatIsoToRingEquiv
  letI : Algebra Γ(X', f ⁻¹ᵁ U.1) (X'.presheaf.stalk x) :=
    X'.presheaf.algebra_section_stalk (⟨x, hx⟩ : f ⁻¹ᵁ U.1)
  haveI := hU'.isLocalization_stalk ⟨x, hx⟩
  have halg : ∀ a, algebraMap Γ(X', f ⁻¹ᵁ U.1) (X'.presheaf.stalk x) a =
      (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom a := fun a => rfl
  let g : Γ(X', f ⁻¹ᵁ U.1) →+ X'.presheaf.stalk x :=
    (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom.toAddMonoidHom.comp
      (φ.toRingHom.toAddMonoidHom.comp (d.toLinearMap.toAddMonoidHom.comp φ.symm.toRingHom.toAddMonoidHom))
  have hg : ∀ a, g a = (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom (φ (d (φ.symm a))) := fun a => rfl
  obtain ⟨D', hD'⟩ := derivation_extend_localization_atPrime ℤ Γ(X', f ⁻¹ᵁ U.1) (X'.presheaf.stalk x)
    (hU'.primeIdealOf ⟨x, hx⟩).asIdeal
    (intDerivationOfLeibniz g (fun a b => by
      simp only [hg, map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _), Algebra.smul_def, halg,
        RingEquiv.apply_symm_apply]))
  refine ⟨D', fun r => ?_⟩
  have h1 := hD' (φ r)
  rw [halg] at h1
  refine h1.trans ?_
  show g (φ r) = _
  rw [hg, RingEquiv.symm_apply_apply]
  rfl

end GlobalTheory.StalkDer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendStalkOfIsoStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_stalk_extend_of_app : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsIso f] (U : X.affineOpens) (d : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (x : X') (hx : x ∈ f ⁻¹ᵁ U.1), ∃ δ : Derivation ℤ (X'.presheaf.stalk x) (X'.presheaf.stalk x), ∀ r, δ ((X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom ((f.app U.1).hom r)) = (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom ((f.app U.1).hom (d r)) := by
  first | exact @GlobalTheory.StalkDer.derivation_extend_stalk_of_iso | exact GlobalTheory.StalkDer.derivation_extend_stalk_of_iso | (intros; apply GlobalTheory.StalkDer.derivation_extend_stalk_of_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkIdealVanishingIdealPreimageIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkIdealVanishingIdealPreimageIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.StalkVan

theorem comap_inv_eq_map {A B : CommRingCat.{0}} (e : A ≅ B) (I : Ideal A) :
    I.comap e.inv.hom = I.map e.hom.hom := by
  have := Ideal.map_comap_of_equiv (I := I) e.commRingCatIsoToRingEquiv
  exact this.symm

theorem ideal_comap_eq_map {X X' : Scheme.{0}} (f : X' ⟶ X) [IsIso f] (I : X.IdealSheafData)
    (V : X'.affineOpens) :
    (I.comap f).ideal V = (I.ideal ⟨f ''ᵁ V.1, V.2.image_of_isOpenImmersion f⟩).map
      (f.appLE (f ''ᵁ V.1) V.1 (f.preimage_image_eq V.1).ge).hom := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, comap_inv_eq_map, Scheme.Hom.appIso_hom']

theorem map_germ_app_congr {X X' : Scheme.{0}} (f : X' ⟶ X) (I : X.IdealSheafData) (x : X') :
    ∀ (W U : X.affineOpens), W = U → ∀ (hW : x ∈ f ⁻¹ᵁ W.1) (hU : x ∈ f ⁻¹ᵁ U.1),
      (I.ideal W).map ((X'.presheaf.germ (f ⁻¹ᵁ W.1) x hW).hom.comp (f.app W.1).hom) =
      (I.ideal U).map ((X'.presheaf.germ (f ⁻¹ᵁ U.1) x hU).hom.comp (f.app U.1).hom) := by
  rintro W U rfl hW hU
  rfl

theorem stalkId_vanishingIdeal_preimage : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsIso f]
    (Z : TopologicalSpace.Closeds X) (Z' : TopologicalSpace.Closeds X'),
    (Z' : Set X') = f ⁻¹' (Z : Set X) → ∀ (U : X.affineOpens) (x : X') (hx : x ∈ f ⁻¹ᵁ U.1),
    ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal Z') x =
      ((Scheme.IdealSheafData.vanishingIdeal Z).ideal U).map
        ((X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom.comp (f.app U.1).hom) := by
  intro X X' f _ Z Z' hZ U x hx
  have hc : (Scheme.IdealSheafData.vanishingIdeal Z).comap f =
      Scheme.IdealSheafData.vanishingIdeal Z' :=
    GlobalTheory.vanishingIdeal_comap_of_isOpenImmersion X' X f Z Z' fun y => by
      rw [← SetLike.mem_coe, hZ]; rfl
  let V : X'.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  have hxV : x ∈ V.1 := hx
  rw [ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ x V hxV, ← hc, ideal_comap_eq_map, Ideal.map_map]
  have hWU : (⟨f ''ᵁ V.1, V.2.image_of_isOpenImmersion f⟩ : X.affineOpens) = U := by
    apply Subtype.ext
    show f ''ᵁ (f ⁻¹ᵁ U.1) = U.1
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    refine inf_eq_right.2 fun y _ => ?_
    exact ⟨(inv f) y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  have hxW : x ∈ f ⁻¹ᵁ (f ''ᵁ V.1) := (f.preimage_image_eq V.1).ge hxV
  rw [← map_germ_app_congr f _ x _ U hWU hxW hx]
  congr 1
  rw [Scheme.Hom.appLE, CommRingCat.hom_comp, ← RingHom.comp_assoc, ← CommRingCat.hom_comp,
    TopCat.Presheaf.germ_res]

end GlobalTheory.StalkVan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkIdealVanishingIdealPreimageIsoStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalkIdeal_vanishingIdeal_preimage_iso : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsIso f] (Z : TopologicalSpace.Closeds X) (Z' : TopologicalSpace.Closeds X'), (Z' : Set X') = f ⁻¹' (Z : Set X) → ∀ (U : X.affineOpens) (x : X') (hx : x ∈ f ⁻¹ᵁ U.1), ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal Z') x = ((Scheme.IdealSheafData.vanishingIdeal Z).ideal U).map ((X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom.comp (f.app U.1).hom) := by
  first | exact @GlobalTheory.StalkVan.stalkId_vanishingIdeal_preimage | exact GlobalTheory.StalkVan.stalkId_vanishingIdeal_preimage | (intros; apply GlobalTheory.StalkVan.stalkId_vanishingIdeal_preimage <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtensionCompletedEtaleChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtensionCompletedEtaleChart
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartDerivation

open Polynomial

theorem lift_with_value {A R V : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V]
    (φ : A →+* R) (α : A →+* V) (hα : IsLocalHom α) (θ : R) (ζ : V) (q : Polynomial A)
    (hq : q.Monic) (hqθ : (q.map φ).eval θ = 0) (hqζ : (q.map α).eval ζ = 0)
    (happ : ∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n)
    (hinj : ∀ (n : ℕ) (P : Polynomial A), P.natDegree < q.natDegree →
      (P.map φ).eval θ ∈ maximalIdeal R ^ n → ∀ i, P.coeff i ∈ maximalIdeal A ^ n) :
    ∃ ψ : R →+* V, ψ.comp φ = α ∧ ψ θ = ζ := by
  classical
  have hq1 : q ≠ 1 := by
    rintro rfl
    simp at hqθ
  have key : ∀ (n : ℕ) (P P' : Polynomial A),
      (P.map φ).eval θ - (P'.map φ).eval θ ∈ maximalIdeal R ^ n →
      (P.map α).eval ζ - (P'.map α).eval ζ ∈ maximalIdeal V ^ n := by
    intro n P P' h
    have hD := Polynomial.modByMonic_add_div (P - P') q
    have e1 : (P.map φ).eval θ - (P'.map φ).eval θ = (((P - P') %ₘ q).map φ).eval θ := by
      rw [← Polynomial.eval_sub, ← Polynomial.map_sub]
      conv_lhs => rw [← hD]
      simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.eval_add,
        Polynomial.eval_mul, hqθ, zero_mul, add_zero]
    have e2 : (P.map α).eval ζ - (P'.map α).eval ζ = (((P - P') %ₘ q).map α).eval ζ := by
      rw [← Polynomial.eval_sub, ← Polynomial.map_sub]
      conv_lhs => rw [← hD]
      simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.eval_add,
        Polynomial.eval_mul, hqζ, zero_mul, add_zero]
    rw [e2]
    rw [e1] at h
    exact GlobalTheory.eval_map_mem_maximalIdeal_pow_of_coeff_mem α n _
      (hinj n _ (Polynomial.natDegree_modByMonic_lt _ hq hq1) h) ζ
  have hmem : ∀ (n : ℕ) (x : V),
      x ∈ (maximalIdeal V ^ n) • (⊤ : Submodule V V) ↔ x ∈ maximalIdeal V ^ n :=
    fun n x => GlobalTheory.mem_ideal_smul_top_iff_mem _ x
  have ex : ∀ r : R, ∃ L : V, ∀ (n : ℕ) (P : Polynomial A),
      r - (P.map φ).eval θ ∈ maximalIdeal R ^ n → L - (P.map α).eval ζ ∈ maximalIdeal V ^ n := by
    intro r
    choose Pn hPn using fun n => happ n r
    have hc : ∀ {m n : ℕ}, m ≤ n → ((Pn m).map α).eval ζ ≡ ((Pn n).map α).eval ζ
        [SMOD (maximalIdeal V ^ m • (⊤ : Submodule V V))] := by
      intro m n hmn
      rw [SModEq.sub_mem, hmem]
      apply key
      have h1 : r - ((Pn n).map φ).eval θ ∈ maximalIdeal R ^ m :=
        Ideal.pow_le_pow_right hmn (hPn n)
      have := Ideal.sub_mem _ h1 (hPn m)
      convert this using 1
      ring
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (f := fun k => ((Pn k).map α).eval ζ) inferInstance hc
    refine ⟨L, fun n P hP => ?_⟩
    have h1 := (hmem n _).1 ((SModEq.sub_mem).1 (hL n))
    have h2 : ((Pn n).map α).eval ζ - (P.map α).eval ζ ∈ maximalIdeal V ^ n := by
      apply key
      have := Ideal.sub_mem _ hP (hPn n)
      convert this using 1
      ring
    have := Ideal.sub_mem _ h2 h1
    convert this using 1
    ring
  have haus : ∀ x : V, (∀ n, x ∈ maximalIdeal V ^ n) → x = 0 := by
    intro x hx
    exact IsHausdorff.haus inferInstance x fun n =>
      SModEq.sub_mem.2 (by rw [sub_zero, hmem]; exact hx n)
  choose ψ0 hψ0 using ex
  have char : ∀ (x : R) (b : V), (∀ n, ∃ P : Polynomial A,
      x - (P.map φ).eval θ ∈ maximalIdeal R ^ n ∧ b - (P.map α).eval ζ ∈ maximalIdeal V ^ n) →
      ψ0 x = b := by
    intro x b h
    rw [← sub_eq_zero]
    apply haus
    intro n
    obtain ⟨P, h1, h2⟩ := h n
    have := Ideal.sub_mem _ (hψ0 x n P h1) h2
    convert this using 1
    ring
  let ψ : R →+* V :=
    { toFun := ψ0
      map_one' := char 1 1 fun n => ⟨1, by simp, by simp⟩
      map_zero' := char 0 0 fun n => ⟨0, by simp, by simp⟩
      map_add' := fun x y => char _ _ fun n => by
        obtain ⟨Px, hx⟩ := happ n x
        obtain ⟨Py, hy⟩ := happ n y
        refine ⟨Px + Py, ?_, ?_⟩
        · have := Ideal.add_mem _ hx hy
          convert this using 1
          simp only [Polynomial.map_add (f := _), Polynomial.eval_add]
          ring
        · have := Ideal.add_mem _ (hψ0 x n Px hx) (hψ0 y n Py hy)
          convert this using 1
          simp only [Polynomial.map_add (f := _), Polynomial.eval_add]
          ring
      map_mul' := fun x y => char _ _ fun n => by
        obtain ⟨Px, hx⟩ := happ n x
        obtain ⟨Py, hy⟩ := happ n y
        refine ⟨Px * Py, ?_, ?_⟩
        · have := Ideal.add_mem _ (Ideal.mul_mem_right y _ hx)
            (Ideal.mul_mem_left _ ((Px.map φ).eval θ) hy)
          convert this using 1
          simp only [Polynomial.map_mul, Polynomial.eval_mul]
          ring
        · have := Ideal.add_mem _ (Ideal.mul_mem_right (ψ0 y) _ (hψ0 x n Px hx))
            (Ideal.mul_mem_left _ ((Px.map α).eval ζ) (hψ0 y n Py hy))
          convert this using 1
          simp only [Polynomial.map_mul, Polynomial.eval_mul]
          ring }
  refine ⟨ψ, ?_, ?_⟩
  · ext a
    show ψ0 (φ a) = α a
    exact char _ _ fun n => ⟨Polynomial.C a, by simp, by simp⟩
  · show ψ0 θ = ζ
    exact char _ _ fun n => ⟨Polynomial.X, by simp, by simp⟩

theorem ringHom_ext_of_approx {A R V : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] [CommRing V] [IsLocalRing V] [IsHausdorff (maximalIdeal V) V]
    (φ : A →+* R) (hm : (maximalIdeal A).map φ = maximalIdeal R) (θ : R)
    (happ : ∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n)
    (g₁ g₂ : R →+* V) (hloc : ∀ a ∈ maximalIdeal A, g₁ (φ a) ∈ maximalIdeal V)
    (h : g₁.comp φ = g₂.comp φ) (hθ : g₁ θ = g₂ θ) : g₁ = g₂ := by
  have hpow : ∀ (g : R →+* V), g.comp φ = g₁.comp φ →
      ∀ n, ∀ x ∈ maximalIdeal R ^ n, g x ∈ maximalIdeal V ^ n := by
    intro g hg n x hx
    rw [← hm, ← Ideal.map_pow] at hx
    have hle : Ideal.map g ((maximalIdeal A ^ n).map φ) ≤ maximalIdeal V ^ n := by
      rw [Ideal.map_map, hg, Ideal.map_pow]
      apply Ideal.pow_right_mono
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact hloc a ha
    exact hle (Ideal.mem_map_of_mem g hx)
  have hev : ∀ (g : R →+* V) (P : Polynomial A), g ((P.map φ).eval θ) = P.eval₂ (g.comp φ) (g θ) := by
    intro g P
    rw [Polynomial.eval_map, Polynomial.hom_eval₂]
  ext r
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal V) V) _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, GlobalTheory.mem_ideal_smul_top_iff_mem]
  obtain ⟨P, hP⟩ := happ n r
  have h1 := hpow g₁ rfl n _ hP
  have h2 := hpow g₂ h.symm n _ hP
  have h3 : g₁ ((P.map φ).eval θ) = g₂ ((P.map φ).eval θ) := by
    rw [hev, hev, h, hθ]
  have := Ideal.sub_mem _ h1 h2
  rw [map_sub, map_sub, h3] at this
  convert this using 1
  ring

end GlobalTheory.ChartDerivation

namespace GlobalTheory.ChartDerivation

open Polynomial

theorem main : ∀ (A : Type) [CommRing A] [IsLocalRing A] (k : Type) [Field k] [CharZero k] (m d : ℕ) (ψ : A →+* ChartRing k m d), IsEtaleCompletion ψ → ∀ δ : Derivation ℤ A A, ∃ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), ∀ a, D' (ψ a) = ψ (δ a) := by
  intro A _ _ k _ _ m d ψ hψ δ
  obtain ⟨hflat, hmax, hfin⟩ := hψ
  have hloc : ∀ a ∈ maximalIdeal A, ψ a ∈ maximalIdeal (ChartRing k m d) := fun a ha =>
    hmax ▸ Ideal.mem_map_of_mem ψ ha
  haveI : IsLocalHom ψ := ⟨fun a ha => by
    by_contra hna
    exact (mem_maximalIdeal _).1 (hloc a ((mem_maximalIdeal a).2 hna)) ha⟩
  haveI : CharZero (ChartRing k m d) :=
    (RingHom.charZero_iff (algebraMap k (ChartRing k m d)).injective).1 inferInstance
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI hRA : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
  have hur := GlobalTheory.GenFan.formallyUnramified_residue_comp_of_isEtaleCompletion k m d ψ ⟨hflat, hmax, hfin⟩
  obtain ⟨θ, q, hqm, hqθ, hqu, happ1, hind⟩ :=
    GlobalTheory.exists_hensel_generator_of_residue_finite_unramified ψ hfin hur
  have happ := GlobalTheory.exists_poly_sub_mem_maximalIdeal_pow ψ hmax θ happ1
  have hinj := GlobalTheory.coeff_mem_pow_of_flat_of_indep_mod_max ψ hflat hmax θ q hqm hqθ happ hind
  obtain ⟨hVloc, -, hVcomp, -, -, -⟩ := GlobalTheory.DualNumberLocal.main (ChartRing k m d)
  let α : A →+* DualNumber (ChartRing k m d) :=
    { toFun := fun a => TrivSqZeroExt.inl (ψ a) + TrivSqZeroExt.inr (ψ (δ a))
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp <;> ring
      map_mul' := fun a b => by
        ext
        · simp
        · simp [TrivSqZeroExt.snd_mul, Derivation.leibniz]
          ring_nf }
  have hαfst : ∀ a, (α a).fst = ψ a := fun a => by simp [α]
  have hαsnd : ∀ a, (α a).snd = ψ (δ a) := fun a => by simp [α]
  have hαloc : IsLocalHom α := ⟨fun a ha => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hαfst] at ha
    exact IsUnit.of_map ψ a ha⟩
  let fstR : DualNumber (ChartRing k m d) →+* ChartRing k m d :=
    (TrivSqZeroExt.fstHom (ChartRing k m d) (ChartRing k m d) (ChartRing k m d)).toRingHom
  have hfstR : ∀ x, fstR x = x.fst := fun x => rfl
  have hfα : fstR.comp α = ψ := by ext a; simp [hfstR, hαfst]
  have hfev : ∀ (P : Polynomial A) (x : DualNumber (ChartRing k m d)),
      ((P.map α).eval x).fst = (P.map ψ).eval x.fst := by
    intro P x
    rw [← hfstR, Polynomial.eval_map, Polynomial.hom_eval₂, hfα, hfstR, Polynomial.eval_map]
  set w := (q.map α).eval (TrivSqZeroExt.inl θ) with hw
  set t := (q.derivative.map ψ).eval θ with ht
  have hw0 : w.fst = 0 := by rw [hw, hfev, TrivSqZeroExt.fst_inl, hqθ]
  set u : ChartRing k m d := -((hqu.unit⁻¹ : (ChartRing k m d)ˣ) : ChartRing k m d) * w.snd with hu
  set ζ : DualNumber (ChartRing k m d) := TrivSqZeroExt.inl θ + TrivSqZeroExt.inr u with hζ
  have hsq : (TrivSqZeroExt.inr u : DualNumber (ChartRing k m d)) ^ 2 = 0 := by
    rw [pow_two, TrivSqZeroExt.inr_mul_inr]
  have hqζ : (q.map α).eval ζ = 0 := by
    rw [hζ, Polynomial.eval_add_of_sq_eq_zero _ _ _ hsq, ← hw]
    have hD : ((q.map α).derivative.eval (TrivSqZeroExt.inl θ)).fst = t := by
      rw [Polynomial.derivative_map, hfev, TrivSqZeroExt.fst_inl]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [hw0]
    · have h1 : t * ((hqu.unit⁻¹ : (ChartRing k m d)ˣ) : ChartRing k m d) = 1 := hqu.mul_val_inv
      show (w + _).snd = (0 : DualNumber (ChartRing k m d)).snd
      rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inr, hD,
        TrivSqZeroExt.snd_zero, MulOpposite.op_zero, zero_smul, add_zero, smul_eq_mul, hu]
      rw [← _root_.mul_assoc, mul_neg, h1, neg_mul, _root_.one_mul, add_neg_cancel]
  obtain ⟨Ψ, hΨ, hΨθ⟩ := lift_with_value ψ α hαloc θ ζ q hqm hqθ hqζ happ hinj
  have hid : RingHom.id (ChartRing k m d) = fstR.comp Ψ := by
    refine ringHom_ext_of_approx ψ hmax θ happ _ _ (fun a ha => hloc a ha) ?_ ?_
    · rw [RingHom.comp_assoc, hΨ, hfα]; rfl
    · simp [hfstR, hΨθ, hζ]
  have hfst : ∀ r, (Ψ r).fst = r := fun r => (RingHom.congr_fun hid r).symm
  let L : ChartRing k m d →ₗ[ℤ] ChartRing k m d :=
    (AddMonoidHom.mk' (fun r => (Ψ r).snd) (fun x y => by simp)).toIntLinearMap
  have hL : ∀ r, L r = (Ψ r).snd := fun r => rfl
  refine ⟨{ toLinearMap := L
            map_one_eq_zero' := by
              show (Ψ 1).snd = 0
              rw [map_one]; rfl
            leibniz' := fun x y => by
              show (Ψ (x * y)).snd = x • (Ψ y).snd + y • (Ψ x).snd
              rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, smul_eq_mul, smul_eq_mul,
                MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
              ring }, fun a => ?_⟩
  show (Ψ (ψ a)).snd = ψ (δ a)
  rw [← RingHom.comp_apply, hΨ, hαsnd]

end GlobalTheory.ChartDerivation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtensionCompletedEtaleChartStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_extension_completedEtaleChart : ∀ (A : Type) [CommRing A] [IsLocalRing A] (k : Type) [Field k] [CharZero k] (m d : ℕ) (ψ : A →+* ChartRing k m d), IsEtaleCompletion ψ → ∀ δ : Derivation ℤ A A, ∃ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), ∀ a, D' (ψ a) = ψ (δ a) := by
  first | exact @GlobalTheory.ChartDerivation.main | exact GlobalTheory.ChartDerivation.main | (intros; apply GlobalTheory.ChartDerivation.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivationExtendsCompletedToricChartRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartDer

theorem logDer_extend_chartRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), ∀ (U : Y.X.affineOpens) (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (genBdIdeal Y) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m d i} → ∃ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ r, D' (((Scheme.stalkClosedPointTo ξ).hom.comp (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)) r) = ((Scheme.stalkClosedPointTo ξ).hom.comp (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)) (D.1 r)) ∧ ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  intro E _ _ _ H Dw l Xo c Y U D k _ m d ξ hx hE hI
  have hiso : IsIso (genι Y) := isIso_fst Y
  set x := ξ (closedPoint _) with hxdef
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_derivation_stalk_extend_of_app _ _ (genι Y) U D.1 x hx
  set g := ((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) x hx).hom.comp ((genι Y).app U.1).hom with hg
  have hZ : ((genBd Y : TopologicalSpace.Closeds (gen Y)) : Set (gen Y)) = (genι Y) ⁻¹' ((interior Y).compl : Set Y.X) := by
    ext z
    simp only [TopologicalSpace.Opens.coe_compl, Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe]
    rw [mem_genBd]
    unfold GlobalTheory.LogKS.interior Model.j
    have hc : ∀ w, (Y.jQ ≫ pullback.fst Y.s (spMap (RingHom.id c.F))) w = genι Y (Y.jQ w) := fun w => rfl
    simp only [Scheme.Hom.coe_opensRange, Set.mem_range, hc]
    constructor
    · rintro h ⟨w, hw⟩
      exact h ⟨w, (genι Y).isOpenEmbedding.injective hw⟩
    · rintro h ⟨w, hw⟩
      exact h ⟨w, by rw [← hw]; rfl⟩
  have hJ := GlobalTheory.T.stalkIdeal_vanishingIdeal_preimage_iso _ _ (genι Y) _ (genBd Y) hZ U x hx
  have hstab : ∀ a ∈ ((Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal U).map g,
      δ a ∈ ((Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal U).map g := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      have := hδ r
      simp only [hg, RingHom.comp_apply] at this ⊢
      rw [this]
      exact Ideal.mem_map_of_mem _ (D.2.2 r hr)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Ideal.add_mem _ hy hz
    | smul c y hy' hy =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_right _ _ hy')
  have hC : CharZero (ChartRing k m d) :=
    (Spec.preimage (ξ ≫ genStr Y)).hom.charZero_iff (RingHom.injective _) |>.1 inferInstance
  have hk : CharZero k := (RingHom.charZero_iff (MvPowerSeries.C_injective (σ := Fin m ⊕ Fin d) (R := k))).2 hC
  obtain ⟨D', hD'⟩ := GlobalTheory.T.exists_derivation_extension_completedEtaleChart _ k m d (Scheme.stalkClosedPointTo ξ).hom hE δ
  refine ⟨D', fun r => ?_, GlobalTheory.T.toricChart_derivation_boundaryParam_mem_span _ k m d _ δ D' _ hstab hD' (by rw [← hJ]; exact hI)⟩
  simp only [RingHom.comp_apply]
  rw [hD']
  exact congrArg _ (hδ r)

end GlobalTheory.ChartDer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivationExtendsCompletedToricChartRingStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logDerivation_extends_completed_toricChart_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), ∀ (U : Y.X.affineOpens) (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (genBdIdeal Y) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m d i} → ∃ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ r, D' (((Scheme.stalkClosedPointTo ξ).hom.comp (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)) r) = ((Scheme.stalkClosedPointTo ξ).hom.comp (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)) (D.1 r)) ∧ ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  first | exact @GlobalTheory.ChartDer.logDer_extend_chartRing | exact GlobalTheory.ChartDer.logDer_extend_chartRing | (intros; apply GlobalTheory.ChartDer.logDer_extend_chartRing <;> assumption)
end
