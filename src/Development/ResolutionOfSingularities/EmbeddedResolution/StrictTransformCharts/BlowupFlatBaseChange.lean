module

public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution

private theorem map_mem_nonZeroDivisors_of_flat {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat) {s : R} (hs : s ∈ nonZeroDivisors R) :
    φ s ∈ nonZeroDivisors S := by
  let _ : Algebra R S := φ.toAlgebra
  have : Module.Flat R S := hφ
  have hmul : ∀ x : S, φ s * x = s • x := by
    intro x
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hs1 : ∀ x : R, s * x = 0 → x = 0 := (mem_nonZeroDivisors_iff.mp hs).1
  have hL : Function.Injective (LinearMap.mulLeft R s) := by
    intro a b hab
    have h1 : s * a = s * b := by
      simpa only [LinearMap.mulLeft_apply] using hab
    have h2 : s * (a - b) = 0 := by rw [mul_sub, h1, sub_self]
    exact sub_eq_zero.mp (hs1 _ h2)
  have hinj : Function.Injective ((LinearMap.mulLeft R s).rTensor S) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := S) _ hL
  have key : ∀ t : S, φ s * t = 0 → t = 0 := by
    intro t ht
    have hsmul : s • t = 0 := by rw [← hmul t]; exact ht
    have e1 : TensorProduct.tmul R s t = (0 : TensorProduct R R S) := by
      have h3 : TensorProduct.tmul R s t = TensorProduct.tmul R (1 : R) (s • t) := by
        rw [← TensorProduct.smul_tmul, smul_eq_mul, mul_one]
      rw [h3, hsmul, TensorProduct.tmul_zero]
    have e0 : ((LinearMap.mulLeft R s).rTensor S) (TensorProduct.tmul R (1 : R) t)
        = ((LinearMap.mulLeft R s).rTensor S) 0 := by
      rw [LinearMap.rTensor_tmul, map_zero, LinearMap.mulLeft_apply, mul_one]
      exact e1
    have h1 : TensorProduct.tmul R (1 : R) t = (0 : TensorProduct R R S) := hinj e0
    have h2 : (TensorProduct.lid R S) (TensorProduct.tmul R (1 : R) t)
        = (TensorProduct.lid R S) 0 := by rw [h1]
    rwa [TensorProduct.lid_tmul, one_smul, map_zero] at h2
  exact mem_nonZeroDivisors_iff.mpr
    ⟨key, fun t ht => key t (by rw [mul_comm]; exact ht)⟩

private theorem exists_affineOpen_mem_le {Y : Scheme.{u}} (y : Y) (W : Y.Opens) (hy : y ∈ W) :
    ∃ V : Y.affineOpens, y ∈ (V : Y.Opens) ∧ (V : Y.Opens) ≤ W := by
  obtain ⟨V, hVmem, hyV, hVle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hy
  exact ⟨⟨V, hVmem⟩, hyV, hVle⟩

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_of_flat {X Y : Scheme.{u}} {D : X.IdealSheafData}
    (hD : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor D) (f : Y ⟶ X) [AlgebraicGeometry.Flat f] :
    FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor (D.comap f) := by
  unfold FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor at hD ⊢
  intro y
  obtain ⟨U, s, hxU, hs, hUs⟩ := hD (f.base y)
  obtain ⟨V, hyV, hVle⟩ :=
    EmbeddedResolution.exists_affineOpen_mem_le y (f ⁻¹ᵁ (U : X.Opens))
      (show y ∈ f ⁻¹ᵁ (U : X.Opens) from hxU)
  have hU2 : IsAffineOpen (U : X.Opens) := U.2
  have hV2 : IsAffineOpen (V : Y.Opens) := V.2
  have hflat : (Scheme.Hom.appLE f (U : X.Opens) (V : Y.Opens) hVle).hom.Flat := by
    apply AlgebraicGeometry.Scheme.Hom.flat_appLE <;> assumption
  refine ⟨V, (Scheme.Hom.appLE f (U : X.Opens) (V : Y.Opens) hVle).hom s, hyV, ?_, ?_⟩
  · exact _root_.FunctorialResolution.EmbeddedResolution.map_mem_nonZeroDivisors_of_flat _ hflat hs
  · rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE D f U V hVle, hUs, Ideal.map_span,
      Set.image_singleton]

theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.pullback_snd_of_flat {X Y B : Scheme.{u}} {π : B ⟶ X}
    {J : X.IdealSheafData} (h : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π J) (g : Y ⟶ X) [AlgebraicGeometry.Flat g] :
    FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf (pullback.snd π g) (J.comap g) := by
  have e1 : (J.comap g).comap (pullback.snd π g)
      = (J.comap π).comap (pullback.fst π g) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      pullback.condition]
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact h.1.comap_of_flat (pullback.fst π g)
  · intro W m hm
    have hm' : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor (J.comap (m ≫ g)) := by
      rw [Scheme.IdealSheafData.comap_comp]
      exact hm
    obtain ⟨b, hb, hbuniq⟩ := h.2 W (m ≫ g) hm'
    refine ⟨pullback.lift b m hb, ?_, ?_⟩
    · exact pullback.lift_snd b m hb
    · intro a ha
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst]
        refine hbuniq _ ?_
        show (a ≫ pullback.fst π g) ≫ π = m ≫ g
        rw [Category.assoc, pullback.condition, ← Category.assoc, ha]
      · rw [pullback.lift_snd, ha]

theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.of_isPullback_of_flat {X Y B P : Scheme.{u}} {π : B ⟶ X}
    {J : X.IdealSheafData} (h : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π J) (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    {p : P ⟶ B} {q : P ⟶ Y} (hsq : IsPullback p q π g) :
    FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf q (J.comap g) := by
  have h3 : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf (pullback.snd π g) (J.comap g) := h.pullback_snd_of_flat g
  have h4 := h3.iso_hom_comp hsq.isoPullback
  rwa [hsq.isoPullback_hom_snd] at h4

theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.exists_isPullback_of_flat {X Y B B' : Scheme.{u}} {π : B ⟶ X}
    {J : X.IdealSheafData} (h : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π J) (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    {π' : B' ⟶ Y} (h' : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π' (J.comap g)) :
    ∃ q : B' ⟶ B, q ≫ π = π' ≫ g ∧ IsPullback q π' π g := by
  obtain ⟨e, he⟩ := h'.exists_iso (h.pullback_snd_of_flat g)
  have hc : (e.hom ≫ pullback.fst π g) ≫ π = π' ≫ g := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  exact ⟨e.hom ≫ pullback.fst π g, hc, IsPullback.of_iso_pullback ⟨hc⟩ e rfl he⟩

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.AffineSpaceCoordinateBlowup
open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

universe u

def uliftFinset (m : ℕ) (S : Finset (Fin m)) : Finset (ULift.{u} (Fin m)) :=
  S.map ⟨fun j => (ULift.up j : ULift.{u} (Fin m)), fun _ _ h => congrArg ULift.down h⟩

@[simp] theorem mem_uliftFinset {m : ℕ} (S : Finset (Fin m)) (x : ULift.{u} (Fin m)) :
    x ∈ uliftFinset.{u} m S ↔ x.down ∈ S := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp h
    exact ha
  · intro h
    exact Finset.mem_map.mpr ⟨x.down, h, rfl⟩

theorem up_mem_uliftFinset {m : ℕ} {S : Finset (Fin m)} {j : Fin m} (hj : j ∈ S) :
    (ULift.up j : ULift.{u} (Fin m)) ∈ uliftFinset.{u} m S :=
  (mem_uliftFinset S _).mpr hj

theorem down_mem_of_mem_uliftFinset {m : ℕ} {S : Finset (Fin m)} {x : ULift.{u} (Fin m)}
    (hx : x ∈ uliftFinset.{u} m S) : x.down ∈ S :=
  (mem_uliftFinset S x).mp hx

abbrev finCoordIdeal (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    Ideal (MvPolynomial (ULift.{u} (Fin m)) k) :=
  coordIdeal k (uliftFinset.{u} m S)

def affineSpaceSpecIso (k : Type u) [Field k] (m : ℕ) :
    affineSpaceFin k m ≅ Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k)) :=
  AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)

private theorem appTop_comp_apply_eq_appTop_appTop {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Γ(Z, ⊤)) : (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := rfl

private theorem appTop_specMap_ΓSpecIso_inv_apply {R S : CommRingCat.{u}} (f : R ⟶ S) (x : R) :
    (Spec.map f).appTop.hom ((Scheme.ΓSpecIso R).inv.hom x)
      = (Scheme.ΓSpecIso S).inv.hom (f.hom x) := by
  have h : (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop = f ≫ (Scheme.ΓSpecIso S).inv := by
    rw [← cancel_mono (Scheme.ΓSpecIso S).hom]
    simp [Scheme.ΓSpecIso_naturality]
  have h2 : ((Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop).hom x
      = (f ≫ (Scheme.ΓSpecIso S).inv).hom x := by rw [h]
  exact h2

private theorem affineSpaceSpecIso_inv_appTop_coord (k : Type u) [Field k] (m : ℕ)
    (j : ULift.{u} (Fin m)) :
    (affineSpaceSpecIso k m).inv.appTop.hom (AffineSpace.coord (Spec (CommRingCat.of k)) j)
      = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv.hom
          (MvPolynomial.X j) := by
  apply AlgebraicGeometry.AffineSpace.SpecIso_inv_appTop_coord

private theorem affineSpaceSpecIso_hom_appTop_X (k : Type u) [Field k] (m : ℕ)
    (j : ULift.{u} (Fin m)) :
    (affineSpaceSpecIso k m).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv.hom
          (MvPolynomial.X j))
      = AffineSpace.coord (Spec (CommRingCat.of k)) j := by
  rw [← affineSpaceSpecIso_inv_appTop_coord k m j, ← appTop_comp_apply_eq_appTop_appTop, Iso.hom_inv_id]
  simp

private theorem affineSpaceSpecIso_inv_comp_affineSpaceFinToSpec (k : Type u) [Field k] (m : ℕ) :
    (affineSpaceSpecIso k m).inv ≫ affineSpaceFinToSpec k m
      = Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k)) := by
  simp [affineSpaceSpecIso, affineSpaceFinToSpec]

abbrev affineSpaceCoordBlowup (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) : Scheme.{u} :=
  Blowup.affineBlowup (finCoordIdeal k m S)

def affineSpaceCoordBlowupMap (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    affineSpaceCoordBlowup k m S ⟶ affineSpaceFin k m :=
  Blowup.AffineBlowup.toSpec (finCoordIdeal k m S) ≫ (affineSpaceSpecIso k m).inv

private theorem comap_specIdealSheaf_finCoordIdeal (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    (Blowup.specIdealSheaf (finCoordIdeal k m S)).comap (affineSpaceSpecIso k m).hom
      = coordSubspaceIdeal k m S := by
  have : IsAffine (affineSpaceFin k m) := inferInstance
  have hset : ((affineSpaceSpecIso k m).hom.appTop.hom) ''
      (((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv.hom) ''
        ((MvPolynomial.X : ULift.{u} (Fin m) → MvPolynomial (ULift.{u} (Fin m)) k) ''
          (↑(uliftFinset.{u} m S) : Set (ULift.{u} (Fin m)))))
      = (fun i => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
          (↑S : Set (Fin m)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, ⟨j, hj, rfl⟩, rfl⟩, rfl⟩
      exact ⟨j.down, Finset.mem_coe.mpr (down_mem_of_mem_uliftFinset (Finset.mem_coe.mp hj)),
        (affineSpaceSpecIso_hom_appTop_X k m j).symm⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv.hom
          (MvPolynomial.X (ULift.up i)),
        ⟨MvPolynomial.X (ULift.up i),
          ⟨ULift.up i, Finset.mem_coe.mpr (up_mem_uliftFinset (Finset.mem_coe.mp hi)), rfl⟩, rfl⟩,
        ?_⟩
      exact affineSpaceSpecIso_hom_appTop_X k m (ULift.up i)
  have hI : (finCoordIdeal k m S : Ideal (MvPolynomial (ULift.{u} (Fin m)) k))
      = Ideal.span ((MvPolynomial.X : ULift.{u} (Fin m) → MvPolynomial (ULift.{u} (Fin m)) k) ''
          (↑(uliftFinset.{u} m S) : Set (ULift.{u} (Fin m)))) :=
    coordIdeal_eq_span k (uliftFinset.{u} m S)
  rw [Blowup.specIdealSheaf_eq_ofIdealTop, Scheme.IdealSheafData.comap_ofIdealTop, coordSubspaceIdeal_eq_ofIdealTop_span_coord, hI,
    Ideal.map_span, Ideal.map_span, hset]

theorem isBlowupAlongIdealSheaf_affineSpaceCoordBlowupMap (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    Blowup.IsBlowupAlongIdealSheaf (affineSpaceCoordBlowupMap k m S) (coordSubspaceIdeal k m S) := by
  rw [← comap_specIdealSheaf_finCoordIdeal k m S]
  exact (Blowup.isBlowupAlongIdealSheaf_affineBlowup_toSpec (finCoordIdeal k m S)).comp_iso_hom
    (affineSpaceSpecIso k m).symm

abbrev finCoordIdealGen (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    ↥(finCoordIdeal k m S) :=
  coordIdealGen k (uliftFinset.{u} m S) (ULift.up s) (up_mem_uliftFinset hs)

abbrev coordBlowupChartRing (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :=
  HomogeneousLocalization.Away (Blowup.reesGrading (finCoordIdeal k m S))
    (Blowup.reesGenerator (finCoordIdeal k m S) (finCoordIdealGen k m S s hs))

def coordBlowupChartRingEquiv (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    coordBlowupChartRing k m S s hs ≃+* MvPolynomial (ULift.{u} (Fin m)) k :=
  @awayCoordGenEquivMvPolynomial k _ (ULift.{u} (Fin m)) (Classical.decEq _) (uliftFinset.{u} m S) (ULift.up s)
    (up_mem_uliftFinset hs)

def coordBlowupChartRingCatIso (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    CommRingCat.of (coordBlowupChartRing k m S s hs) ≅
      CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k) :=
  (coordBlowupChartRingEquiv k m S s hs).toCommRingCatIso

def specCoordBlowupChartRingIso (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    Spec (CommRingCat.of (coordBlowupChartRing k m S s hs)) ≅
      Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k)) where
  hom := Spec.map (coordBlowupChartRingCatIso k m S s hs).inv
  inv := Spec.map (coordBlowupChartRingCatIso k m S s hs).hom
  hom_inv_id := by rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
  inv_hom_id := by rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]

def specCoordBlowupChartRingIsoAffineSpace (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    Spec (CommRingCat.of (coordBlowupChartRing k m S s hs)) ≅ affineSpaceFin k m :=
  specCoordBlowupChartRingIso k m S s hs ≪≫ (affineSpaceSpecIso k m).symm

def affineSpaceCoordBlowupChart (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m)
    (hs : s ∈ S) :
    Spec (CommRingCat.of (coordBlowupChartRing k m S s hs)) ⟶ affineSpaceCoordBlowup k m S :=
  Blowup.affineBlowupChart (finCoordIdeal k m S) (finCoordIdealGen k m S s hs)

instance instIsOpenImmersionModelBlowupChart (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    (s : Fin m) (hs : s ∈ S) : IsOpenImmersion (affineSpaceCoordBlowupChart k m S s hs) :=
  Blowup.instIsOpenImmersionAffineBlowupChart (finCoordIdeal k m S) (finCoordIdealGen k m S s hs)

private def coordBlowupSubstUliftFin (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) :
    MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] MvPolynomial (ULift.{u} (Fin m)) k :=
  @coordBlowupSubst k _ (ULift.{u} (Fin m)) (Classical.decEq _) (uliftFinset.{u} m S) (ULift.up s)

private theorem specMap_coordBlowupSubstUliftFin_comp_affineSpaceSpecIso_inv (k : Type u) [Field k] (m : ℕ)
    (S : Finset (Fin m)) (s : Fin m) :
    Spec.map (CommRingCat.ofHom (coordBlowupSubstUliftFin k m S s).toRingHom)
        ≫ (affineSpaceSpecIso k m).inv
      = (affineSpaceSpecIso k m).inv ≫ coordBlowupSubstMap k m S s := by
  refine AffineSpace.hom_ext ?_ ?_
  · show (Spec.map (CommRingCat.ofHom (coordBlowupSubstUliftFin k m S s).toRingHom)
          ≫ (affineSpaceSpecIso k m).inv) ≫ affineSpaceFinToSpec k m
      = ((affineSpaceSpecIso k m).inv ≫ coordBlowupSubstMap k m S s) ≫ affineSpaceFinToSpec k m
    rw [Category.assoc, Category.assoc, coordBlowupSubstMap_comp_affineSpaceFinToSpec, affineSpaceSpecIso_inv_comp_affineSpaceFinToSpec,
      ← Spec.map_comp]
    congr 1
    ext r
    simp [coordBlowupSubstUliftFin]
  · intro i
    show (Spec.map (CommRingCat.ofHom (coordBlowupSubstUliftFin k m S s).toRingHom)
          ≫ (affineSpaceSpecIso k m).inv).appTop.hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) i)
      = ((affineSpaceSpecIso k m).inv ≫ coordBlowupSubstMap k m S s).appTop.hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) i)
    rw [appTop_comp_apply_eq_appTop_appTop, appTop_comp_apply_eq_appTop_appTop, affineSpaceSpecIso_inv_appTop_coord,
      appTop_specMap_ΓSpecIso_inv_apply, coordBlowupSubstMap_appTop_coord]
    by_cases hc : i.down ∈ S ∧ i.down ≠ s
    · rw [if_pos hc, map_mul, affineSpaceSpecIso_inv_appTop_coord, affineSpaceSpecIso_inv_appTop_coord]
      simp [coordBlowupSubstUliftFin, ULift.ext_iff, hc.1, hc.2]
    · rw [if_neg hc, affineSpaceSpecIso_inv_appTop_coord]
      simp [coordBlowupSubstUliftFin, ULift.ext_iff, hc]

theorem affineSpaceCoordBlowupChart_comp_affineSpaceCoordBlowupMap (k : Type u) [Field k] (m : ℕ)
    (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    affineSpaceCoordBlowupChart k m S s hs ≫ affineSpaceCoordBlowupMap k m S =
      (specCoordBlowupChartRingIsoAffineSpace k m S s hs).hom ≫ coordBlowupSubstMap k m S s := by
  have hcomp : (coordBlowupChartRingEquiv k m S s hs).symm.toRingHom.comp
      (coordBlowupSubstUliftFin k m S s).toRingHom
      = Blowup.chartRingHom (finCoordIdeal k m S) (finCoordIdealGen k m S s hs) :=
    @awayCoordGenEquivMvPolynomial_symm_comp_coordBlowupSubst k _ (ULift.{u} (Fin m)) (Classical.decEq _)
      (uliftFinset.{u} m S) (ULift.up s) (up_mem_uliftFinset hs)
  have hring : CommRingCat.ofHom (Blowup.chartRingHom (finCoordIdeal k m S) (finCoordIdealGen k m S s hs))
      = CommRingCat.ofHom (coordBlowupSubstUliftFin k m S s).toRingHom ≫
        CommRingCat.ofHom (coordBlowupChartRingEquiv k m S s hs).symm.toRingHom := by
    rw [← hcomp]
    rfl
  show Blowup.affineBlowupChart (finCoordIdeal k m S) (finCoordIdealGen k m S s hs) ≫
      (Blowup.AffineBlowup.toSpec (finCoordIdeal k m S) ≫ (affineSpaceSpecIso k m).inv)
    = (specCoordBlowupChartRingIsoAffineSpace k m S s hs).hom ≫ coordBlowupSubstMap k m S s
  rw [← Category.assoc, Blowup.affineBlowupChart_comp_toSpec, Blowup.algebraMap_chart_eq_chartRingHom, hring,
    Spec.map_comp, Category.assoc, specMap_coordBlowupSubstUliftFin_comp_affineSpaceSpecIso_inv k m S s, ← Category.assoc]
  rfl

theorem iSup_opensRange_affineSpaceCoordBlowupChart (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    (⨆ i : ↥S, Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S i.1 i.2))
      = (⊤ : (affineSpaceCoordBlowup k m S).Opens) := by
  refine le_antisymm le_top ?_
  rw [← iSup_opensRange_affineBlowupChart_coordIdealGen k (uliftFinset.{u} m S)]
  refine iSup_le fun j => ?_
  refine le_iSup_of_le ⟨j.1.down, down_mem_of_mem_uliftFinset j.2⟩ ?_
  exact le_rfl

end FunctorialResolution.EmbeddedResolution

end
end
