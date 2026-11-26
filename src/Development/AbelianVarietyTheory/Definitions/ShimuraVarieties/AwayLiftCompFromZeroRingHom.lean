module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.AwayLiftCompFromZeroRingHom
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal

universe u

noncomputable section

namespace GlobalTheory

section Quot

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)

def quotGrading (I : Ideal A) : ℕ → Submodule R (A ⧸ I) :=
  fun d => (𝒜 d).map (Ideal.Quotient.mkₐ R I).toLinearMap

theorem mk_mem_quotGrading (I : Ideal A) {d : ℕ} {a : A} (ha : a ∈ 𝒜 d) :
    Ideal.Quotient.mk I a ∈ quotGrading 𝒜 I d := ⟨a, ha, rfl⟩

variable [GradedAlgebra 𝒜]

theorem isInternal_quotGrading {I : Ideal A} (hI : I.IsHomogeneous 𝒜) :
    DirectSum.IsInternal (quotGrading 𝒜 I) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    rintro y ⟨a, ha, rfl⟩ hy
    have hmap : (⨆ (j) (_ : j ≠ i), quotGrading 𝒜 I j) =
        (⨆ (j) (_ : j ≠ i), 𝒜 j).map (Ideal.Quotient.mkₐ R I).toLinearMap := by
      simp only [quotGrading, Submodule.map_iSup]
    rw [hmap] at hy
    obtain ⟨b, hb, hab⟩ := hy
    have hb0 : GradedRing.proj 𝒜 i b = 0 := by
      refine Submodule.iSup_induction _ (motive := fun x => GradedRing.proj 𝒜 i x = 0) hb ?_
        (map_zero _) (fun x y hx hy => by simp only [map_add (f := _), hx, hy, add_zero])
      intro j x hx
      refine Submodule.iSup_induction _ (motive := fun x => GradedRing.proj 𝒜 i x = 0) hx ?_
        (map_zero _) (fun x y hx hy => by simp only [map_add (f := _), hx, hy, add_zero])
      intro hji z hz
      rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 hz hji]
    have hab' : a - b ∈ I := Ideal.Quotient.eq.mp hab.symm
    have h2 : GradedRing.proj 𝒜 i (a - b) ∈ I := hI i hab'
    rw [map_sub, hb0, sub_zero, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_same 𝒜 ha] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h2
  · have htop := (DirectSum.Decomposition.isInternal 𝒜).submodule_iSup_eq_top
    change (⨆ d, (𝒜 d).map (Ideal.Quotient.mkₐ R I).toLinearMap) = ⊤
    rw [← Submodule.map_iSup, htop, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Ideal.Quotient.mkₐ_surjective R I)

instance gradedMonoid_quotGrading (I : Ideal A) : SetLike.GradedMonoid (quotGrading 𝒜 I) where
  one_mem := ⟨1, SetLike.GradedOne.one_mem, map_one (Ideal.Quotient.mkₐ R I)⟩
  mul_mem := by
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, SetLike.GradedMul.mul_mem ha hb, map_mul (Ideal.Quotient.mkₐ R I) a b⟩

@[reducible] def quotGradedAlgebra {I : Ideal A} (hI : I.IsHomogeneous 𝒜) :
    GradedAlgebra (quotGrading 𝒜 I) where
  toGradedMonoid := inferInstance
  toDecomposition := (isInternal_quotGrading 𝒜 hI).chooseDecomposition

end Quot

namespace ProjPoint

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {B C : Type u} [CommRing B] [CommRing C]

def awayLift (φ : A →+* B) (f : A) (hf : IsUnit (φ f)) : Away 𝒜 f →+* B :=
  (IsLocalization.Away.lift (S := Localization.Away f) f hf).comp
    (algebraMap (Away 𝒜 f) (Localization.Away f))

theorem awayLift_mk_mul (φ : A →+* B) {f : A} (hf : IsUnit (φ f)) {d : ℕ} (hd : f ∈ 𝒜 d) (n : ℕ)
    (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayLift 𝒜 φ f hf (Away.mk 𝒜 hd n a ha) * φ f ^ n = φ a := by
  have h1 : φ f ^ n = IsLocalization.Away.lift (S := Localization.Away f) f hf
      (algebraMap A _ (f ^ n)) := by
    rw [IsLocalization.Away.lift_eq, map_pow]
  rw [h1, awayLift, RingHom.comp_apply, ← map_mul, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk, Localization.mk_eq_mk']
  rw [IsLocalization.mk'_spec (Localization.Away f) a ⟨f ^ n, _⟩, IsLocalization.Away.lift_eq]

theorem eq_awayLift (φ : A →+* B) {f : A} (hf : IsUnit (φ f)) {d : ℕ} (hd : f ∈ 𝒜 d)
    (g : Away 𝒜 f →+* B)
    (hg : ∀ n a ha, g (Away.mk 𝒜 hd n a ha) * φ f ^ n = φ a) : g = awayLift 𝒜 φ f hf := by
  ext x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hd x
  apply (hf.pow n).mul_right_cancel
  rw [hg, awayLift_mk_mul]

theorem awayLift_comp_fromZeroRingHom (φ : A →+* B) (f : A) (hf : IsUnit (φ f)) :
    (awayLift 𝒜 φ f hf).comp (fromZeroRingHom 𝒜 _) = φ.comp (algebraMap (𝒜 0) A) := by
  ext a
  change IsLocalization.Away.lift (S := Localization.Away f) f hf
    (algebraMap (Away 𝒜 f) _ (algebraMap (𝒜 0) _ a)) = _
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝒜 0) A,
    IsLocalization.Away.lift_eq]
  rfl

theorem map_irrelevant_comp {φ : A →+* B} (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) (ψ : B →+* C) :
    (irrelevant 𝒜).toIdeal.map (ψ.comp φ) = ⊤ := by
  rw [← Ideal.map_map, hφ, Ideal.map_top]

def ofHom (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) : Spec (.of B) ⟶ Proj 𝒜 :=
  Proj.fromOfGlobalSections 𝒜 ((Scheme.ΓSpecIso (.of B)).inv.hom.comp φ)
    (map_irrelevant_comp 𝒜 hφ _)

theorem ofHom_preimage_basicOpen (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤)
    {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) :
    ofHom 𝒜 φ hφ ⁻¹ᵁ Proj.basicOpen 𝒜 r = PrimeSpectrum.basicOpen (φ r) := by
  rw [ofHom, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hn hr]
  exact basicOpen_eq_of_affine (R := .of B) (φ r)

@[reassoc]
theorem ofHom_toSpecZero (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) :
    ofHom 𝒜 φ hφ ≫ Proj.toSpecZero 𝒜 =
      Spec.map (CommRingCat.ofHom (φ.comp (algebraMap (𝒜 0) A))) := by
  rw [ofHom, Proj.fromOfGlobalSections_toSpecZero, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  congr 1
  ext a
  simp


set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
theorem SpecMap_ofHom_eq_awayι (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤)
    (ψ : B →+* C) {f : A} {n : ℕ} (hn : 0 < n) (hf : f ∈ 𝒜 n) (hu : IsUnit (ψ (φ f))) :
    Spec.map (CommRingCat.ofHom ψ) ≫ ofHom 𝒜 φ hφ =
      Spec.map (CommRingCat.ofHom (awayLift 𝒜 (ψ.comp φ) f hu)) ≫ Proj.awayι 𝒜 f hf hn := by
  set φ' := (Scheme.ΓSpecIso (.of B)).inv.hom.comp φ with hφ'
  have hφ'' := map_irrelevant_comp 𝒜 hφ (Scheme.ΓSpecIso (.of B)).inv.hom
  have hrange : Set.range (Spec.map (CommRingCat.ofHom ψ)) ⊆
      Set.range ((Spec (.of B)).basicOpen (φ' f)).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change _ ∈ (Spec (.of B)).basicOpen ((Scheme.ΓSpecIso (.of B)).inv (φ f))
    rw [basicOpen_eq_of_affine]
    exact fun h => x.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  let l := IsOpenImmersion.lift _ _ hrange
  have hl : l ≫ _ = _ := IsOpenImmersion.lift_fac _ _ hrange
  have h1 : ((Spec (.of B)).basicOpen (φ' f)).ι ≫ ofHom 𝒜 φ hφ =
      Proj.toBasicOpenOfGlobalSections 𝒜 φ' rfl hn hf ≫ (Proj.basicOpen 𝒜 f).ι := by
    rw [← Proj.fromOfGlobalSections_resLE 𝒜 φ' hφ'' hn hf, Scheme.Hom.resLE_comp_ι]
    rfl
  rw [← hl, Category.assoc, h1, Proj.awayι, Proj.toBasicOpenOfGlobalSections]
  simp only [← Category.assoc]
  congr 2
  let ψ' : Γ(Spec (.of B), ⊤) →+* C := ψ.comp (Scheme.ΓSpecIso (.of B)).hom.hom
  have hψ' : ∀ a, ψ' (φ' a) = ψ (φ a) := by
    intro a
    simp [ψ', φ']
  have hu' : IsUnit (ψ' (φ' f)) := hψ' f ▸ hu
  have h2 : ((l ≫ ((Spec (.of B)).isoOfEq
      ((Spec (.of B)).toSpecΓ_preimage_basicOpen (φ' f))).inv) ≫
      (Spec (.of B)).toSpecΓ ∣_ (PrimeSpectrum.basicOpen (φ' f))) ≫
      (basicOpenIsoSpecAway (φ' f)).hom = Spec.map (CommRingCat.ofHom
        (IsLocalization.Away.lift (S := Localization.Away (φ' f)) (φ' f) hu')) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(Spec (.of B), ⊤) (Localization.Away (φ' f)))))]
    simp only [Category.assoc, basicOpenIsoSpecAway, IsOpenImmersion.isoOfRangeEq_hom_fac,
      morphismRestrict_ι, Scheme.isoOfEq_inv_ι_assoc]
    rw [reassoc_of% hl, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    simp [ψ', IsLocalization.Away.lift_eq]
  rw [h2, ← Spec.map_comp]
  congr 2
  rw [← CommRingCat.ofHom_comp, awayLift, ← RingHom.comp_assoc]
  congr 2
  apply IsLocalization.ringHom_ext (M := .powers f)
  ext a
  simp [IsLocalization.Away.lift_eq, hψ']

theorem ofHom_eq_awayι (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤)
    {f : A} {n : ℕ} (hn : 0 < n) (hf : f ∈ 𝒜 n) (hu : IsUnit (φ f)) :
    ofHom 𝒜 φ hφ = Spec.map (CommRingCat.ofHom (awayLift 𝒜 φ f hu)) ≫ Proj.awayι 𝒜 f hf hn := by
  simpa using SpecMap_ofHom_eq_awayι 𝒜 φ hφ (RingHom.id B) hn hf hu

theorem hom_ext (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) {Y : Scheme.{u}}
    {g₁ g₂ : Spec (.of B) ⟶ Y}
    (h : ∀ (C : Type u) [CommRing C] (ψ : B →+* C) (f : A) (n : ℕ), 0 < n → f ∈ 𝒜 n →
      IsUnit (ψ (φ f)) →
      Spec.map (CommRingCat.ofHom ψ) ≫ g₁ = Spec.map (CommRingCat.ofHom ψ) ≫ g₂) : g₁ = g₂ := by
  let s : {f : A // ∃ n, 0 < n ∧ f ∈ 𝒜 n} → (CommRingCat.of B) := fun f => φ f.1
  have hs : Ideal.span (Set.range s) = ⊤ := by
    rw [_root_.eq_top_iff, ← hφ, Ideal.map_le_iff_le_comap, toIdeal_irrelevant_le]
    intro i hi x hx
    exact Ideal.subset_span ⟨⟨x, i, hi, hx⟩, rfl⟩
  refine (Scheme.affineOpenCoverOfSpanRangeEqTop s hs).openCover.hom_ext _ _ fun i => ?_
  obtain ⟨n, hn, hf⟩ := i.2
  exact h (Localization.Away (φ i.1)) (algebraMap B _) i.1 n hn hf
    (IsLocalization.Away.algebraMap_isUnit _)

theorem SpecMap_ofHom (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) (ψ : B →+* C) :
    Spec.map (CommRingCat.ofHom ψ) ≫ ofHom 𝒜 φ hφ =
      ofHom 𝒜 (ψ.comp φ) (map_irrelevant_comp 𝒜 hφ ψ) := by
  refine hom_ext 𝒜 _ (map_irrelevant_comp 𝒜 hφ ψ) fun D _ χ f n hn hf hu => ?_
  rw [SpecMap_ofHom_eq_awayι 𝒜 _ _ χ hn hf hu, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    SpecMap_ofHom_eq_awayι 𝒜 φ hφ (χ.comp ψ) hn hf hu]

theorem ofHom_eq_of_scale {φ φ' : A →+* B} (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤)
    (hφ' : (irrelevant 𝒜).toIdeal.map φ' = ⊤) (c : B)
    (hc : ∀ n, ∀ a ∈ 𝒜 n, φ' a = c ^ n * φ a) : ofHom 𝒜 φ' hφ' = ofHom 𝒜 φ hφ := by
  refine hom_ext 𝒜 _ hφ' fun D _ χ f n hn hf hu => ?_
  have hu2 := hu
  rw [hc n f hf, map_mul, IsUnit.mul_iff] at hu2
  rw [SpecMap_ofHom_eq_awayι 𝒜 _ _ χ hn hf hu, SpecMap_ofHom_eq_awayι 𝒜 _ _ χ hn hf hu2.2]
  congr 3
  symm
  refine eq_awayLift 𝒜 _ _ hf _ fun m a ha => ?_
  have := awayLift_mk_mul 𝒜 (χ.comp φ) hu2.2 hf m a ha
  simp only [RingHom.comp_apply] at this ⊢
  generalize awayLift 𝒜 (χ.comp φ) f hu2.2 (Away.mk 𝒜 hf m a ha) = t at this ⊢
  rw [hc _ a ha, hc n f hf, map_mul, map_mul, ← this, mul_pow, smul_eq_mul, map_pow, map_pow]
  ring

section Map

variable {A' τ τ' : Type u} {A₀ : Type u} [CommRing A₀] [CommRing A'] [SetLike τ A₀]
  [AddSubgroupClass τ A₀] [SetLike τ' A'] [AddSubgroupClass τ' A']
  {𝒜₀ : ℕ → τ} {ℬ : ℕ → τ'} [GradedRing 𝒜₀] [GradedRing ℬ]

theorem map_irrelevant_comp_graded (g : 𝒜₀ →+*ᵍ ℬ) (hg : irrelevant ℬ ≤ (irrelevant 𝒜₀).map g)
    {φ : A' →+* B} (hφ : (irrelevant ℬ).toIdeal.map φ = ⊤) :
    (irrelevant 𝒜₀).toIdeal.map (φ.comp g.toRingHom) = ⊤ := by
  rw [← Ideal.map_map, _root_.eq_top_iff, ← hφ]
  exact Ideal.map_mono hg

theorem ofHom_map (g : 𝒜₀ →+*ᵍ ℬ) (hg : irrelevant ℬ ≤ (irrelevant 𝒜₀).map g)
    (φ : A' →+* B) (hφ : (irrelevant ℬ).toIdeal.map φ = ⊤) :
    ofHom ℬ φ hφ ≫ Proj.map g hg =
      ofHom 𝒜₀ (φ.comp g.toRingHom) (map_irrelevant_comp_graded g hg hφ) := by
  refine hom_ext 𝒜₀ _ (map_irrelevant_comp_graded g hg hφ) fun D _ χ f n hn hf hu => ?_
  rw [SpecMap_ofHom_eq_awayι 𝒜₀ _ _ χ hn hf hu,
    SpecMap_ofHom_eq_awayι_assoc ℬ φ hφ χ hn (g.2 hf) hu]
  erw [Proj.awayι_comp_map g hg hn f hf]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 3
  refine eq_awayLift 𝒜₀ _ _ hf _ fun m a ha => ?_
  rw [RingHom.comp_apply]
  erw [Away.map_mk]
  exact awayLift_mk_mul ℬ (χ.comp φ) hu (g.2 hf) m _ _

end Map

end ProjPoint

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PiTensorLiftCompSingle
open TensorProduct PiTensorProduct

namespace GlobalTheory

noncomputable section

universe u v w

variable {A : Type u} [CommRing A] {σ : Type w} [Fintype σ] [DecidableEq σ] {X : σ → Type v}
  [∀ s, CommRing (X s)] [∀ s, Algebra A (X s)] {S : Type*} [CommRing S] [Algebra A S]

def piTensorLift (f : ∀ s, X s →ₐ[A] S) : (⨂[A] s, X s) →ₐ[A] S :=
  liftAlgHom ((MultilinearMap.mkPiAlgebra A σ S).compLinearMap fun s => (f s).toLinearMap)
    (by simp) (fun x y => by simp [Finset.prod_mul_distrib])


omit [DecidableEq σ] in
@[simp] theorem piTensorLift_tprod (f : ∀ s, X s →ₐ[A] S) (x : ∀ s, X s) :
    piTensorLift f (tprod A x) = ∏ s, f s (x s) := by
  refine (PiTensorProduct.lift.tprod x).trans ?_
  simp

@[simp] theorem piTensorLift_comp_single (f : ∀ s, X s →ₐ[A] S) (s : σ) :
    (piTensorLift f).comp (singleAlgHom s) = f s := by
  ext x
  rw [AlgHom.comp_apply, singleAlgHom_apply, piTensorLift_tprod,
    Finset.prod_eq_single s (fun t _ ht => by simp [Pi.mulSingle_eq_of_ne ht]) (by simp)]
  simp

theorem piTensorLift_single (f : ∀ s, X s →ₐ[A] S) (s : σ) (x : X s) :
    piTensorLift f (singleAlgHom s x) = f s x := congr($(piTensorLift_comp_single f s) x)


end

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsAdaptedOfIsLocalRing
open Module TensorProduct

namespace GlobalTheory

noncomputable section

section Dual

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

def basisOfDual (v : ι → M) (c : ι → Dual R M) (h₁ : ∀ i j, c i (v j) = if i = j then 1 else 0)
    (h₂ : ∀ x, ∑ i, c i x • v i = x) : Basis ι R M :=
  Basis.ofEquivFun <| LinearEquiv.ofLinear (LinearMap.pi c) (Fintype.linearCombination R v)
    (by
      refine LinearMap.ext fun a => funext fun i => ?_
      simp [Fintype.linearCombination_apply, h₁])
    (by
      refine LinearMap.ext fun x => ?_
      simp [Fintype.linearCombination_apply, h₂])

end Dual

section Action

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

def basisMulGL (b : Basis ι R M) (g : GL ι R) : Basis ι R M :=
  b.map (Matrix.toLinOfInv b b g.mul_inv g.inv_mul)

theorem basisMulGL_apply (b : Basis ι R M) (g : GL ι R) (j : ι) :
    basisMulGL b g j = ∑ i, (g : Matrix ι ι R) i j • b i := by
  simp [basisMulGL, Matrix.toLinOfInv, Matrix.toLin_self]

end Action

section Triangular

variable (ι R : Type*) [CommRing R] [Fintype ι] [LinearOrder ι]

variable {ι R}

variable {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}

theorem mem_basis_flag_iff (b : Basis (Fin n) R M) (k : Fin (n + 1)) (x : M) :
    x ∈ b.flag k ↔ ∀ i : Fin n, k ≤ i.castSucc → b.repr x i = 0 := by
  refine ⟨fun hx i hi => b.flag_le_ker_coord hi hx, fun h => ?_⟩
  rw [← b.sum_repr x]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : i.castSucc < k
  · exact Submodule.smul_mem _ _ (b.self_mem_flag hi)
  · simp [h i (not_lt.mp hi)]

end Triangular

section Flag

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

abbrev SubQuot (P Q : Submodule R M) : Type _ := Q ⧸ P.submoduleOf Q

def subQuotEquivOfSplitting {L : Type*} [AddCommGroup L] [Module R L] {P Q : Submodule R M}
    (π : M →ₗ[R] L) (σ : L →ₗ[R] M) (h₁ : ∀ l, π (σ l) = l) (h₂ : ∀ x ∈ P, π x = 0)
    (h₃ : ∀ l, σ l ∈ Q) (h₄ : ∀ x ∈ Q, x - σ (π x) ∈ P) : SubQuot P Q ≃ₗ[R] L :=
  (Submodule.quotEquivOfEq _ (LinearMap.ker (π ∘ₗ Q.subtype)) (by
    ext x
    refine ⟨fun hx => h₂ _ hx, fun hx => ?_⟩
    have hx' : π x = 0 := hx
    have := h₄ x x.2
    rwa [hx', map_zero, sub_zero] at this)).trans
    ((π ∘ₗ Q.subtype).quotKerEquivOfSurjective fun l => ⟨⟨σ l, h₃ l⟩, h₁ l⟩)


variable (R M) in
@[ext] structure FullFlag (n : ℕ) where

  sub : Fin (n + 1) → Submodule R M
  sub_zero : sub 0 = ⊥
  sub_last : sub (Fin.last n) = ⊤
  castSucc_le_succ : ∀ i : Fin n, sub i.castSucc ≤ sub i.succ
  invertible_step : ∀ i : Fin n, Module.Invertible R (SubQuot (sub i.castSucc) (sub i.succ))

namespace FullFlag

variable {n : ℕ}

abbrev Step (F : FullFlag (R := R) (M := M) n) (i : Fin n) : Type _ := SubQuot (F.sub i.castSucc) (F.sub i.succ)

instance (F : FullFlag (R := R) (M := M) n) (i : Fin n) : Module.Invertible R (F.Step i) := F.invertible_step i

theorem monotone (F : FullFlag (R := R) (M := M) n) : Monotone F.sub :=
  Fin.monotone_iff_le_succ.2 F.castSucc_le_succ

def basisStepEquiv (b : Basis (Fin n) R M) (i : Fin n) :
    SubQuot (b.flag i.castSucc) (b.flag i.succ) ≃ₗ[R] R :=
  subQuotEquivOfSplitting (b.coord i) (LinearMap.toSpanSingleton R M (b i)) (by simp)
    (fun _ hx => b.flag_le_ker_coord le_rfl hx)
    (fun l => Submodule.smul_mem _ _ (b.self_mem_flag Fin.castSucc_lt_succ))
    (fun x hx => by
      rw [mem_basis_flag_iff] at hx ⊢
      intro j hj
      rcases (Fin.castSucc_le_castSucc_iff.mp hj).eq_or_lt with rfl | h
      · simp
      · simp [hx j (Fin.succ_le_castSucc_iff.mpr h), Finsupp.single_apply, h.ne])

def ofBasis (b : Basis (Fin n) R M) : FullFlag (R := R) (M := M) n where
  sub := b.flag
  sub_zero := b.flag_zero
  sub_last := b.flag_last
  castSucc_le_succ _ := b.flag_mono Fin.castSucc_lt_succ.le
  invertible_step i := Module.Invertible.congr (basisStepEquiv b i).symm

def IsAdapted (F : FullFlag (R := R) (M := M) n) (b : Basis (Fin n) R M) : Prop := b.flag = F.sub

theorem isAdapted_iff {F : FullFlag (R := R) (M := M) n} {b : Basis (Fin n) R M} :
    F.IsAdapted b ↔ ofBasis b = F := ⟨fun h => FullFlag.ext h, fun h => h ▸ rfl⟩

theorem exists_retraction (F : FullFlag (R := R) (M := M) n) (k : Fin (n + 1)) :
    ∃ r : M →ₗ[R] M, (∀ x, r x ∈ F.sub k) ∧ ∀ x ∈ F.sub k, r x = x := by
  induction k using Fin.reverseInduction with
  | last => exact ⟨LinearMap.id, fun x => by simp [F.sub_last], fun _ _ => rfl⟩
  | cast i ih =>
    obtain ⟨r, hr₁, hr₂⟩ := ih
    obtain ⟨s, hs⟩ := Module.projective_lifting_property
      ((F.sub i.castSucc).submoduleOf (F.sub i.succ)).mkQ (LinearMap.id (R := R) (M := F.Step i))
      (Submodule.mkQ_surjective _)
    let r' : M →ₗ[R] F.sub i.succ := r.codRestrict _ hr₁
    refine ⟨r - (F.sub i.succ).subtype ∘ₗ s ∘ₗ Submodule.mkQ _ ∘ₗ r', fun x => ?_, fun x hx => ?_⟩
    · have : r' x - s (Submodule.mkQ _ (r' x)) ∈ (F.sub i.castSucc).submoduleOf (F.sub i.succ) := by
        rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
        exact sub_eq_zero.mpr (congr($hs _)).symm
      exact this
    · have hx' := F.castSucc_le_succ i hx
      have : Submodule.mkQ ((F.sub i.castSucc).submoduleOf (F.sub i.succ)) (r' x) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        change r x ∈ F.sub i.castSucc
        rwa [hr₂ x hx']
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, this, map_zero, hr₂ x hx']
      exact _root_.sub_zero x

theorem exists_splitting (F : FullFlag (R := R) (M := M) n) (i : Fin n) :
    ∃ (π : M →ₗ[R] F.Step i) (σ : F.Step i →ₗ[R] M), (∀ l, π (σ l) = l) ∧
      (∀ x ∈ F.sub i.castSucc, π x = 0) ∧ (∀ l, σ l ∈ F.sub i.succ) ∧
      (∀ x ∈ F.sub i.succ, x - σ (π x) ∈ F.sub i.castSucc) := by
  obtain ⟨r, hr₁, hr₂⟩ := F.exists_retraction i.succ
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    ((F.sub i.castSucc).submoduleOf (F.sub i.succ)).mkQ (LinearMap.id (R := R) (M := F.Step i))
    (Submodule.mkQ_surjective _)
  let r' : M →ₗ[R] F.sub i.succ := r.codRestrict _ hr₁
  have hr' : ∀ y : F.sub i.succ, r' y = y := fun y => Subtype.ext (hr₂ y y.2)
  refine ⟨Submodule.mkQ _ ∘ₗ r', (F.sub i.succ).subtype ∘ₗ s, fun l => ?_, fun x hx => ?_,
    fun l => (s l).2, fun x hx => ?_⟩
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply, hr']
    exact congr($hs l)
  · rw [LinearMap.comp_apply, hr' ⟨x, F.castSucc_le_succ i hx⟩, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hx
  · have : (⟨x, hx⟩ : F.sub i.succ) - s (Submodule.mkQ _ ⟨x, hx⟩) ∈
        (F.sub i.castSucc).submoduleOf (F.sub i.succ) := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
      exact sub_eq_zero.mpr (congr($hs _)).symm
    simp only [LinearMap.comp_apply, hr' ⟨x, hx⟩]
    exact this

theorem exists_isAdapted_of_free (F : FullFlag (R := R) (M := M) n) (h : ∀ i, Module.Free R (F.Step i)) :
    ∃ b : Basis (Fin n) R M, F.IsAdapted b := by
  choose π σ h₁ h₂ h₃ h₄ using F.exists_splitting
  have e : ∀ i, F.Step i ≃ₗ[R] R := fun i => (Module.Invertible.free_iff_linearEquiv.mp (h i)).some
  let v : Fin n → M := fun i => σ i ((e i).symm 1)
  have hv : ∀ (i) (l : F.Step i), σ i l = e i l • v i := fun i l => by
    simp only [v, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  have hspan : ∀ k, Submodule.span R (v '' {i | i.castSucc < k}) = F.sub k := by
    intro k
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact F.monotone (Fin.castSucc_lt_iff_succ_le.mp hi) (h₃ i _)
    · induction k using Fin.induction with
      | zero => rw [F.sub_zero]; exact bot_le
      | succ i ih =>
        intro x hx
        rw [← sub_add_cancel x (σ i (π i x))]
        refine add_mem (Submodule.span_mono (Set.image_mono ?_) (ih (h₄ i x hx))) ?_
        · exact fun j hj => lt_trans hj Fin.castSucc_lt_succ
        · rw [hv]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Fin.castSucc_lt_succ, rfl⟩)
  have hli : LinearIndependent R v := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    by_contra hne
    push Not at hne
    classical
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i => a i ≠ 0) id
      (by obtain ⟨i, hi⟩ := hne; exact ⟨i, by simpa using hi⟩)
    have h0 : e i (π i (∑ j, a j • v j)) = a i := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, Finset.sum_eq_single i _ (by simp)]
      · simp [v, h₁]
      · intro j _ hj
        by_cases haj : a j = 0
        · simp [haj]
        have hji : j < i := lt_of_le_of_ne (hmax j (by simpa using haj)) hj
        rw [map_smul, h₂ i (v j) (F.monotone (Fin.succ_le_castSucc_iff.mpr hji) (h₃ j _))]
        simp
    rw [ha] at h0
    simp only [map_zero] at h0
    exact (Finset.mem_filter.mp hi).2 h0.symm
  refine ⟨Basis.mk hli ?_, funext fun k => ?_⟩
  · have := hspan (Fin.last n)
    rw [F.sub_last] at this
    exact this.ge.trans (Submodule.span_mono (Set.image_subset_range _ _))
  · rw [Basis.flag, Basis.coe_mk]
    exact hspan k

theorem exists_isAdapted_of_isLocalRing [IsLocalRing R] (F : FullFlag (R := R) (M := M) n) :
    ∃ b : Basis (Fin n) R M, F.IsAdapted b :=
  F.exists_isAdapted_of_free fun _ => Module.free_of_flat_of_isLocalRing

end FullFlag

end Flag

end

end GlobalTheory
end
