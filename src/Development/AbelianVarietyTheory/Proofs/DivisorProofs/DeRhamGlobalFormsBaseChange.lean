module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToStructureH1Surjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivGlobalOneFormsBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LTensorLiftBaseChangeGlobalOneFormsAffinePreimag
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LTensorLiftBaseChangeGlobalOneFormsAffinePreimag
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem lTensor_liftSemi_bijective_of_isBaseChange {R R' B B' W W' Ω Ω' : Type} [CommRing R]
    [CommRing R'] [Algebra R R'] [CommRing B] [Algebra R B] [CommRing B'] [Algebra R' B']
    [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R' W']
    [AddCommGroup Ω] [Module R Ω] [Module B Ω] [IsScalarTower R B Ω]
    [AddCommGroup Ω'] [Module R' Ω'] [Module B' Ω'] [IsScalarTower R' B' Ω']
    (α : B →+* B') (f : B →ₛₗ[algebraMap R R'] B') (hf : ∀ b, f b = α b)
    (h1 : Function.Surjective (liftSemi f))
    (m : Ω →ₛₗ[algebraMap R R'] Ω') (hm : ∀ (b : B) (ω : Ω), m (b • ω) = α b • m ω)
    (h2 : Function.Bijective (liftSemi m))
    (e : W →ₗ[R] Ω) (he : IsBaseChange B e) (e' : W' →ₗ[R'] Ω') (he' : IsBaseChange B' e')
    (p : W →ₛₗ[algebraMap R R'] W') (hp : ∀ w, e' (p w) = m (e w)) :
    Function.Bijective (LinearMap.lTensor B' (liftSemi p)) := by
  letI : Module R (B' ⊗[R'] (R' ⊗[R] W)) := Module.compHom _ (algebraMap R R')
  have hsm : ∀ (c : R) (z : B' ⊗[R'] (R' ⊗[R] W)), c • z = algebraMap R R' c • z := fun _ _ ↦ rfl
  have hR : ∀ (c : R) (x : R' ⊗[R] B), c • x = algebraMap R R' c • x := fun c x ↦
    (algebraMap_smul R' c x).symm
  have hW : ∀ (c : R) (w : W), (1 : R') ⊗ₜ[R] (c • w) = algebraMap R R' c • ((1 : R') ⊗ₜ[R] w) := by
    intro c w
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one,
      Algebra.algebraMap_eq_smul_one]

  let bil : R' ⊗[R] B →ₗ[R] W →ₗ[R] B' ⊗[R'] (R' ⊗[R] W) :=
    LinearMap.mk₂ R (fun x w ↦ liftSemi f x ⊗ₜ[R'] ((1 : R') ⊗ₜ[R] w))
      (fun x y w ↦ by rw [map_add (f := _), TensorProduct.add_tmul])
      (fun c x w ↦ by rw [hR, map_smul, hsm, TensorProduct.smul_tmul'])
      (fun x w w' ↦ by rw [TensorProduct.tmul_add, TensorProduct.tmul_add])
      (fun c x w ↦ by rw [hW, TensorProduct.tmul_smul, hsm])
  let Ψ : R' ⊗[R] (B ⊗[R] W) →ₗ[R] B' ⊗[R'] (R' ⊗[R] W) :=
    TensorProduct.lift bil ∘ₗ (TensorProduct.assoc R R' B W).symm.toLinearMap
  have hΨ : Function.Surjective Ψ := by
    suffices hall : ∀ z, z ∈ LinearMap.range Ψ from
      LinearMap.range_eq_top.1 (eq_top_iff.2 fun z _ ↦ hall z)
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul b t =>
      induction t using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
      | add x y hx hy => rw [TensorProduct.tmul_add]; exact add_mem hx hy
      | tmul r w =>
        obtain ⟨x, hx⟩ := h1 (r • b)
        refine ⟨TensorProduct.assoc R R' B W (x ⊗ₜ w), ?_⟩
        have e1 : r ⊗ₜ[R] w = r • ((1 : R') ⊗ₜ[R] w) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        simp only [Ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
          TensorProduct.lift.tmul, bil, LinearMap.mk₂_apply, hx, e1, ← TensorProduct.smul_tmul]
  let Θ : R' ⊗[R] (B ⊗[R] W) ≃ₗ[R] R' ⊗[R] Ω := (he.equiv.restrictScalars R).lTensor R'
  have hΘ : Function.Bijective (fun z ↦ liftSemi m (Θ z)) := h2.comp Θ.bijective
  have key : ∀ z, he'.equiv (LinearMap.lTensor B' (liftSemi p) (Ψ z)) = liftSemi m (Θ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
    | tmul r t =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
      | tmul b w =>
        simp only [Ψ, Θ, bil, LinearMap.comp_apply, LinearEquiv.coe_coe,
          TensorProduct.assoc_symm_tmul, TensorProduct.lift.tmul, LinearMap.mk₂_apply,
          liftSemi_tmul, LinearMap.lTensor_tmul, LinearEquiv.lTensor_tmul,
          LinearEquiv.restrictScalars_apply, IsBaseChange.equiv_tmul, one_smul, hf, hp, hm,
          map_smul, smul_assoc]
  refine ⟨fun x y hxy ↦ ?_, fun q ↦ ?_⟩
  · obtain ⟨x0, rfl⟩ := hΨ x
    obtain ⟨y0, rfl⟩ := hΨ y
    have := hΘ.1 (show liftSemi m (Θ x0) = liftSemi m (Θ y0) by rw [← key, ← key, hxy])
    rw [this]
  · obtain ⟨z, hz⟩ := hΘ.2 (he'.equiv q)
    refine ⟨Ψ z, he'.equiv.injective ?_⟩
    rw [key]; exact hz

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem lTensor_liftSemi_pullForm_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → ∀ U : X.affineOpens, IsAffineOpen (φ ⁻¹ᵁ U.1) → Function.Bijective (LinearMap.lTensor (Sec s' (φ ⁻¹ᵁ U.1)) (liftSemi (pullForm h.w))) := by
  intro R R' _ _ _ X X' s s' φ h hF hH hF' hH' U hU
  let U' : X'.affineOpens := ⟨φ ⁻¹ᵁ U.1, hU⟩
  let pr : Pair φ := ⟨(U', U), le_rfl⟩
  have hsemi : SemiHom (algebraMap R R') (GlobalTheory.CechDR.secPull s s' pr) := GlobalTheory.CechDR.semiHom_secPull h.w pr
  let f : Sec s U.1 →ₛₗ[algebraMap R R'] Sec s' (φ ⁻¹ᵁ U.1) :=
    { toFun := GlobalTheory.CechDR.secPull s s' pr, map_add' := map_add _, map_smul' := hsemi }
  have h1 : Function.Bijective (liftSemi f) :=
    GlobalTheory.CechDR.bijective_liftSemi_secPull R R' X X' s s' φ h pr rfl f (fun _ ↦ rfl)
  have h2 : Function.Bijective (liftSemi hsemi.m1) :=
    GlobalTheory.kaehler_liftSemi_bijective R R' _ _ (GlobalTheory.CechDR.secPull s s' pr) hsemi f (fun _ ↦ rfl) h1
  let e : GlobForm s →ₗ[R] Ω[Sec s U.1⁄R] :=
    { toFun := fun w ↦ w.1 (Opposite.op U), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have he : IsBaseChange (Sec s U.1) e :=
    isBaseChange_glob1 R (AffOp X) (OAff s) hF hH (Opposite.op U) e (fun _ ↦ rfl)
  let e' : GlobForm s' →ₗ[R'] Ω[Sec s' (φ ⁻¹ᵁ U.1)⁄R'] :=
    { toFun := fun w ↦ w.1 (Opposite.op U'), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have he' : IsBaseChange (Sec s' (φ ⁻¹ᵁ U.1)) e' :=
    isBaseChange_glob1 R' (AffOp X') (OAff s') hF' hH' (Opposite.op U') e' (fun _ ↦ rfl)
  exact lTensor_liftSemi_bijective_of_isBaseChange (GlobalTheory.CechDR.secPull s s' pr) f (fun _ ↦ rfl) h1.2 hsemi.m1
    (fun b ω ↦ hsemi.oneFormMap_smul_semilinear b ω) h2 e he e' he' (pullForm h.w)
    (fun w ↦ ((isPullForm_iff.1 (isPullForm_pullForm h.w w)) pr).symm)

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LTensorLiftBaseChangeGlobalOneFormsAffinePreimagStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lTensor_liftBaseChange_globalOneForms_affinePreimage_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → ∀ U : X.affineOpens, IsAffineOpen (φ ⁻¹ᵁ U.1) → Function.Bijective (LinearMap.lTensor (Sec s' (φ ⁻¹ᵁ U.1)) (liftSemi (pullForm h.w))) := by
  first | exact @GlobalTheory.AbCoh.lTensor_liftSemi_pullForm_bijective | exact GlobalTheory.AbCoh.lTensor_liftSemi_pullForm_bijective | (intros; apply GlobalTheory.AbCoh.lTensor_liftSemi_pullForm_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineMapNeTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineMapNeTop
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

namespace GlobalTheory.PointSec

theorem exists_affine_map_ne_top : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X), Surjective s' → ∀ m : Ideal R', m.IsMaximal → ∃ U : X.affineOpens, Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U.1))) m ≠ ⊤ := by
  intro R' _ X X' s' φ hs m hm
  obtain ⟨x', hx'⟩ := hs.surj (⟨m, hm.isPrime⟩ : PrimeSpectrum R')
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show φ.base x' ∈ (⊤ : X.Opens) from trivial)
  refine ⟨⟨U, hU⟩, ?_⟩
  have hx : x' ∈ φ ⁻¹ᵁ U := hxU
  intro htop
  let g : Sec s' (φ ⁻¹ᵁ U) →+* X'.presheaf.stalk x' := (X'.presheaf.germ (φ ⁻¹ᵁ U) x' hx).hom
  have key : ∀ a ∈ m, ¬ IsUnit (g (algebraMap R' (Sec s' (φ ⁻¹ᵁ U)) a)) := by
    intro a ha hu
    have h1 : x' ∈ X'.basicOpen (algebraMap R' (Sec s' (φ ⁻¹ᵁ U)) a : Γ(X', φ ⁻¹ᵁ U)) :=
      (Scheme.mem_basicOpen _ _ _ hx).2 hu
    change x' ∈ X'.basicOpen ((X'.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ U ≤ s' ⁻¹ᵁ ⊤)).op)
      (s'.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a))) at h1
    have h2 : x' ∈ X'.basicOpen (s'.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a)) :=
      Scheme.basicOpen_restrict X' (homOfLE (le_top : φ ⁻¹ᵁ U ≤ s' ⁻¹ᵁ ⊤)) _ h1
    have h3 : x' ∈ s' ⁻¹ᵁ (Sp R').basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a) := by
      rw [Scheme.preimage_basicOpen]; exact h2
    have h4 : s'.base x' ∈ (Sp R').basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a) := h3
    rw [basicOpen_eq_of_affine] at h4
    have h2 : s'.base x' ∈ PrimeSpectrum.basicOpen a := h4
    rw [hx'] at h2
    exact h2 ha
  have hle : Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U))) m ≤
      (IsLocalRing.maximalIdeal (X'.presheaf.stalk x')).comap g := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact key a ha
  have h1 : (1 : Sec s' (φ ⁻¹ᵁ U)) ∈ (IsLocalRing.maximalIdeal (X'.presheaf.stalk x')).comap g :=
    hle (by rw [show Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U))) m = ⊤ from htop]; trivial)
  rw [Ideal.mem_comap, map_one] at h1
  exact (IsLocalRing.mem_maximalIdeal _).1 h1 isUnit_one
end GlobalTheory.PointSec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineMapNeTopStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_map_maximal_proper : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X), Surjective s' → ∀ m : Ideal R', m.IsMaximal → ∃ U : X.affineOpens, Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U.1))) m ≠ ⊤ := by
  first | exact @GlobalTheory.PointSec.exists_affine_map_ne_top | exact GlobalTheory.PointSec.exists_affine_map_ne_top | (intros; apply GlobalTheory.PointSec.exists_affine_map_ne_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionsAffineOpenOfFlatScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionsAffineOpenOfFlatScheme
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

namespace GlobalTheory.CechDR

theorem flat_sec (R' : Type) [CommRing R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (hs : Flat s')
    (U : X'.affineOpens) : Module.Flat R' (Sec s' U.1) := by
  have h1 : (s'.appLE ⊤ U.1 le_top).hom.Flat :=
    HasRingHomProperty.appLE (P := @Flat) s' hs ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h0 : (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have h2 : (secMap s' U.1).hom.Flat := by
    exact RingHom.Flat.comp h0 h1
  exact h2

end GlobalTheory.CechDR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionsAffineOpenOfFlatSchemeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_sections_affineOpen_of_flat_scheme : ∀ (R' : Type) [CommRing R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R'), Flat s' → ∀ U : X'.affineOpens, Module.Flat R' (Sec s' U.1) := by
  first | exact @GlobalTheory.CechDR.flat_sec | exact GlobalTheory.CechDR.flat_sec | (intros; apply GlobalTheory.CechDR.flat_sec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfLTensorFlatFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfLTensorFlatFamily
open TensorProduct

namespace GlobalTheory

theorem subsingleton_of_lTensor_flat_family (R : Type) [CommRing R] (J : Type) (B : J → Type)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] (hflat : ∀ i, Module.Flat R (B i))
    (hmax : ∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤)
    (M : Type) [AddCommGroup M] [Module R M] (h : ∀ i, Subsingleton (B i ⊗[R] M)) :
    Subsingleton M := by
  by_contra hM
  rw [not_subsingleton_iff_nontrivial] at hM
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  set g : R →ₗ[R] M := LinearMap.toSpanSingleton R M x with hg
  set I : Ideal R := LinearMap.ker g with hIdef
  have hI : I ≠ ⊤ := by
    intro hT
    have h1 : (1 : R) ∈ I := hT ▸ Submodule.mem_top
    rw [hIdef, LinearMap.mem_ker, hg, LinearMap.toSpanSingleton_apply, one_smul] at h1
    exact hx h1
  obtain ⟨m, hm, hIm⟩ := I.exists_le_maximal hI
  obtain ⟨i, hi⟩ := hmax m hm
  let e : (R ⧸ I) →ₗ[R] M := (LinearMap.ker g).liftQ g le_rfl
  have he : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have hinj : Function.Injective (e.lTensor (B i)) :=
    Module.Flat.lTensor_preserves_injective_linearMap e he
  haveI := h i
  haveI : Subsingleton (B i ⊗[R] (R ⧸ I)) := hinj.subsingleton
  haveI : Subsingleton ((R ⧸ I) ⊗[R] B i) := (TensorProduct.comm R (R ⧸ I) (B i)).toEquiv.injective.subsingleton
  haveI : Subsingleton (B i ⧸ (I • (⊤ : Submodule R (B i)))) :=
    (TensorProduct.quotTensorEquivQuotSMul (B i) I).symm.toEquiv.injective.subsingleton
  have htop : I • (⊤ : Submodule R (B i)) = ⊤ :=
    Submodule.unique_quotient_iff_eq_top.mp ⟨uniqueOfSubsingleton 0⟩
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at htop
  exact hi (top_le_iff.mp (htop ▸ Ideal.map_mono hIm))

theorem bijective_of_lTensor_flat_family : ∀ (R : Type) [CommRing R] (N N' : Type) [AddCommGroup N]
    [Module R N] [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') (J : Type) (B : J → Type)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)], (∀ i, Module.Flat R (B i)) →
    (∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤) →
    (∀ i, Function.Bijective (LinearMap.lTensor (B i) f)) → Function.Bijective f := by
  intro R _ N N' _ _ _ _ f J B _ _ hflat hmax hbij
  constructor
  · set K := LinearMap.ker f
    have hK : ∀ i, Subsingleton (B i ⊗[R] K) := by
      intro i
      have hinjK : Function.Injective (K.subtype.lTensor (B i)) :=
        Module.Flat.lTensor_preserves_injective_linearMap K.subtype K.injective_subtype
      have hz : (f.lTensor (B i)).comp (K.subtype.lTensor (B i)) = 0 := by
        rw [← LinearMap.lTensor_comp]
        have : f ∘ₗ K.subtype = 0 := by
          ext x
          exact LinearMap.mem_ker.mp x.2
        rw [this, LinearMap.lTensor_zero]
      refine ⟨fun a b => hinjK ((hbij i).1 ?_)⟩
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hz]
      rfl
    have := subsingleton_of_lTensor_flat_family R J B hflat hmax K hK
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.eq_bot_of_subsingleton
  · set q := (LinearMap.range f).mkQ
    have hQ : ∀ i, Subsingleton (B i ⊗[R] (N' ⧸ LinearMap.range f)) := by
      intro i
      have hsurj : Function.Surjective (q.lTensor (B i)) :=
        LinearMap.lTensor_surjective (B i) (Submodule.mkQ_surjective _)
      have hz : (q.lTensor (B i)).comp (f.lTensor (B i)) = 0 := by
        rw [← LinearMap.lTensor_comp]
        have : q ∘ₗ f = 0 := by
          ext x
          simp [q]
        rw [this, LinearMap.lTensor_zero]
      refine subsingleton_of_forall_eq 0 fun y => ?_
      obtain ⟨z, rfl⟩ := hsurj y
      obtain ⟨w, rfl⟩ := (hbij i).2 z
      rw [← LinearMap.comp_apply, hz]
      rfl
    have := subsingleton_of_lTensor_flat_family R J B hflat hmax _ hQ
    have htop : LinearMap.range f = ⊤ :=
      Submodule.unique_quotient_iff_eq_top.mp ⟨uniqueOfSubsingleton 0⟩
    exact LinearMap.range_eq_top.mp htop

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfLTensorFlatFamilyStatement
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_of_lTensor_bijective_of_flat_family : ∀ (R : Type) [CommRing R] (N N' : Type) [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') (J : Type) (B : J → Type) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)], (∀ i, Module.Flat R (B i)) → (∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤) → (∀ i, Function.Bijective (LinearMap.lTensor (B i) f)) → Function.Bijective f := by
  first | exact @GlobalTheory.bijective_of_lTensor_flat_family | exact GlobalTheory.bijective_of_lTensor_flat_family | (intros; apply GlobalTheory.bijective_of_lTensor_flat_family <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivGlobalOneFormsBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

namespace GlobalTheory.AbCoh

theorem isAffineOpen_preimage_of_isPullback (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']
    (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X)
    (h : IsPullback φ s' s (spMap (algebraMap R R'))) (U : X.affineOpens) : IsAffineOpen (φ ⁻¹ᵁ U.1) := by
  haveI : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  exact U.2.preimage φ

theorem exists_equiv_globForm_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → Flat s' → Surjective s' → ∃ e : R' ⊗[R] GlobForm s ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  intro R R' _ _ _ X X' s s' φ h hF hC hF' hC' hfl hsu
  have hb : Function.Bijective (liftSemi (pullForm h.w)) :=
    GlobalTheory.T.bijective_of_lTensor_bijective_of_flat_family R' _ _ (liftSemi (pullForm h.w)) X.affineOpens (fun U ↦ Sec s' (φ ⁻¹ᵁ U.1))
      (fun U ↦ GlobalTheory.T.flat_sections_affineOpen_of_flat_scheme R' X' s' hfl ⟨_, isAffineOpen_preimage_of_isPullback R R' X X' s s' φ h U⟩)
      (GlobalTheory.T.exists_affineOpen_map_maximal_proper R' X X' s' φ hsu)
      (fun U ↦ GlobalTheory.T.lTensor_liftBaseChange_globalOneForms_affinePreimage_bijective R R' X X' s s' φ h hF hC hF' hC' U
        (isAffineOpen_preimage_of_isPullback R R' X X' s s' φ h U))
  refine ⟨LinearEquiv.ofBijective _ hb, fun c ↦ ?_⟩
  rw [LinearEquiv.ofBijective_apply, liftSemi_tmul, one_smul]

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivGlobalOneFormsBaseChangeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_globalOneForms_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → Flat s' → Surjective s' → ∃ e : R' ⊗[R] GlobForm s ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  first | exact @GlobalTheory.AbCoh.exists_equiv_globForm_baseChange | exact GlobalTheory.AbCoh.exists_equiv_globForm_baseChange | (intros; apply GlobalTheory.AbCoh.exists_equiv_globForm_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsAbelianSchemeOfIsPullbackSpMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsAbelianSchemeOfIsPullbackSpMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory

theorem exists_grpObj_isAbelianScheme_of_isPullback_spMap : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left), IsPullback φ s' A.hom (spMap σ) → ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') ∧ SmoothOfRelativeDimension g s' := by
  intro R _ A _ g hA hg R' _ σ X' s' φ h
  have hsm : SmoothOfRelativeDimension g s' := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h hg
  let B := (Over.pullback (spMap σ)).obj A
  letI : GrpObj B := Functor.grpObjObj
  let e : B ≅ Over.mk s' := Over.isoMk h.isoPullback.symm (by simp [B])
  letI : GrpObj (Over.mk s') := GrpObj.ofIso e
  refine ⟨this, ?_, hsm⟩
  have hc := hA.comm
  have hcB : IsCommMonObj B := Functor.isCommMonObj_obj
  exact {
    comm := by
      constructor
      show (β_ _ _).hom ≫ ((e.inv ⊗ₘ e.inv) ≫ μ[B] ≫ e.hom) = (e.inv ⊗ₘ e.inv) ≫ μ[B] ≫ e.hom
      rw [← Category.assoc, ← BraidedCategory.braiding_naturality, Category.assoc,
        ← Category.assoc (β_ B B).hom, IsCommMonObj.mul_comm]
    smooth := MorphismProperty.of_isPullback (P := @Smooth) h hA.smooth
    proper := MorphismProperty.of_isPullback (P := @IsProper) h hA.proper
    geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h hA.geomConnected }

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsAbelianSchemeOfIsPullbackSpMapStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grpObj_isAbelianScheme_of_isPullback_spMap' : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left), IsPullback φ s' A.hom (spMap σ) → ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') ∧ SmoothOfRelativeDimension g s' := by
  first | exact @GlobalTheory.exists_grpObj_isAbelianScheme_of_isPullback_spMap | exact GlobalTheory.exists_grpObj_isAbelianScheme_of_isPullback_spMap | (intros; apply GlobalTheory.exists_grpObj_isAbelianScheme_of_isPullback_spMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearShortExactCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearShortExactCompatible
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem baseChange_middle_equiv_of_exact : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (W' M' H' : Type) [AddCommGroup W'] [Module R' W'] [AddCommGroup M'] [Module R' M'] [AddCommGroup H'] [Module R' H'] (i : W →ₗ[R] M) (p : M →ₗ[R] H) (i' : W' →ₗ[R'] M') (p' : M' →ₗ[R'] H') (a : W →ₛₗ[algebraMap R R'] W') (b : M →ₛₗ[algebraMap R R'] M') (c : H →ₛₗ[algebraMap R R'] H'), Function.Surjective p → Function.Exact i p → Function.Injective i' → Function.Exact i' p' → (∀ x, b (i x) = i' (a x)) → (∀ x, p' (b x) = c (p x)) → (∃ e : R' ⊗[R] W ≃ₗ[R'] W', ∀ x, e (1 ⊗ₜ x) = a x) → (∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ x, e (1 ⊗ₜ x) = c x) → ∃ e : R' ⊗[R] M ≃ₗ[R'] M', ∀ x, e (1 ⊗ₜ x) = b x := by
  intro R R' _ _ _ W M H _ _ _ _ _ _ W' M' H' _ _ _ _ _ _ i p i' p' a b c hp hip hi' hip' hb hc hW hH
  obtain ⟨eW, heW⟩ := hW
  obtain ⟨eH, heH⟩ := hH
  letI : Module R M' := Module.compHom M' (algebraMap R R')
  haveI : IsScalarTower R R' M' := ⟨fun r s x => by
    show (r • s) • x = algebraMap R R' r • s • x
    rw [Algebra.smul_def, mul_smul]⟩
  let b' : M →ₗ[R] M' :=
    { toFun := b, map_add' := b.map_add, map_smul' := fun r m => b.map_smulₛₗ r m }
  let f : R' ⊗[R] M →ₗ[R'] M' := b'.liftBaseChange R'
  have hf1 : ∀ x, f (1 ⊗ₜ x) = b x := by
    intro x; simp [f, b']
  have hfp : ∀ s, p' (f s) = eH (LinearMap.baseChange R' p s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      have h1 : (r ⊗ₜ[R] m : R' ⊗[R] M) = r • (1 ⊗ₜ m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [h1]; simp only [map_smul, hf1, LinearMap.baseChange_tmul, heH, hc]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hfi : ∀ u, f (LinearMap.baseChange R' i u) = i' (eW u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r w =>
      have h1 : (r ⊗ₜ[R] w : R' ⊗[R] W) = r • (1 ⊗ₜ w) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [h1]; simp only [map_smul, hf1, LinearMap.baseChange_tmul, heW, hb]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hex : Function.Exact (LinearMap.baseChange R' i) (LinearMap.baseChange R' p) := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    first | exact lTensor_exact R' hip hp | exact LinearMap.lTensor_exact R' hip hp
  have hsurj : Function.Surjective (LinearMap.baseChange R' p) := by
    rw [LinearMap.baseChange_eq_ltensor]; exact LinearMap.lTensor_surjective R' hp
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    have h0 : LinearMap.baseChange R' p s = 0 := by
      have := hfp s
      rw [hs, map_zero] at this
      exact (LinearEquiv.map_eq_zero_iff eH).1 this.symm
    obtain ⟨u, rfl⟩ := (hex s).1 h0
    have h2 : i' (eW u) = 0 := by rw [← hfi u, hs]
    have h3 : eW u = 0 := hi' (by rw [h2, map_zero])
    rw [(LinearEquiv.map_eq_zero_iff eW).1 h3, map_zero]
  have hsur : Function.Surjective f := by
    intro m'
    obtain ⟨s, hs⟩ := hsurj (eH.symm (p' m'))
    have h0 : p' (m' - f s) = 0 := by
      rw [map_sub, hfp, hs, LinearEquiv.apply_symm_apply, sub_self]
    obtain ⟨w', hw'⟩ := (hip' _).1 h0
    refine ⟨s + LinearMap.baseChange R' i (eW.symm w'), ?_⟩
    rw [map_add (f := _), hfi, LinearEquiv.apply_symm_apply, hw', add_sub_cancel]
  have hbij : Function.Bijective f := ⟨hinj, hsur⟩
  exact ⟨LinearEquiv.ofBijective f hbij, fun x => hf1 x⟩

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearShortExactCompatibleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinear_short_exact_compatible : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (W' M' H' : Type) [AddCommGroup W'] [Module R' W'] [AddCommGroup M'] [Module R' M'] [AddCommGroup H'] [Module R' H'] (i : W →ₗ[R] M) (p : M →ₗ[R] H) (i' : W' →ₗ[R'] M') (p' : M' →ₗ[R'] H') (a : W →ₛₗ[algebraMap R R'] W') (b : M →ₛₗ[algebraMap R R'] M') (c : H →ₛₗ[algebraMap R R'] H'), Function.Surjective p → Function.Exact i p → Function.Injective i' → Function.Exact i' p' → (∀ x, b (i x) = i' (a x)) → (∀ x, p' (b x) = c (p x)) → (∃ e : R' ⊗[R] W ≃ₗ[R'] W', ∀ x, e (1 ⊗ₜ x) = a x) → (∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ x, e (1 ⊗ₜ x) = c x) → ∃ e : R' ⊗[R] M ≃ₗ[R'] M', ∀ x, e (1 ⊗ₜ x) = b x := by
  first | exact @GlobalTheory.AbCoh.baseChange_middle_equiv_of_exact | exact GlobalTheory.AbCoh.baseChange_middle_equiv_of_exact | (intros; apply GlobalTheory.AbCoh.baseChange_middle_equiv_of_exact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamGlobalFormsBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem exact_clAll_toHO1 {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hc : Closed1 (OAff s) = ⊤) :
    Function.Exact (clAll (OAff s) hc) (toHO1 s) := by
  rw [LinearMap.exact_iff]
  change Fil1 (OAff s) = _
  rw [Fil1_eq_range, clAll, LinearMap.range_comp_of_range_eq_top]
  exact LinearEquiv.range _

theorem surjective_of_section {X Y : Scheme.{0}} (f : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ f = 𝟙 Y) : Surjective f := by
  have : Surjective (e ≫ f) := by rw [he]; infer_instance
  exact Surjective.of_comp e f

theorem baseChange_HH1_globForm : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))), (∃ e : R' ⊗[R] HH1 A.hom ≃ₗ[R'] HH1 s', ∀ c, e (1 ⊗ₜ c) = pullHH1 h.w c) ∧ ∃ e : R' ⊗[R] GlobForm A.hom ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  intro R _ A _ g hab hsm R' _ _ X' s' φ h
  obtain ⟨inst', hab', hsm'⟩ := GlobalTheory.T.exists_grpObj_isAbelianScheme_of_isPullback_spMap' R A g hab hsm R' (algebraMap R R') X' s' φ h
  obtain ⟨hfr, h0, -, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hab hsm
  obtain ⟨hfr', h0', -, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R' (Over.mk s') g hab' hsm'
  have hc := GlobalTheory.T.abelianScheme_globalOneForms_closed R A g hab hsm
  have hc' := GlobalTheory.T.abelianScheme_globalOneForms_closed R' (Over.mk s') g hab' hsm'
  have hflat : Flat s' := by
    haveI := hsm'
    haveI : Smooth s' := SmoothOfRelativeDimension.smooth g s'
    infer_instance
  have hsurj : Surjective s' := by
    refine surjective_of_section s' (η[Over.mk s']).left ?_
    have := Over.w (η[Over.mk s'])
    simpa using this
  have hW := GlobalTheory.T.exists_equiv_globalOneForms_baseChange R R' A.left X' A.hom s' φ h hfr h0 hfr' h0' hflat hsurj
  refine ⟨?_, hW⟩
  have hH := (GlobalTheory.T.abelian_structure_cohomology_statement R A g hab hsm).2.2.1 R' X' s' φ h
  refine GlobalTheory.T.semilinear_short_exact_compatible R R' (GlobForm A.hom) (HH1 A.hom) (HO1 A.hom) (GlobForm s') (HH1 s') (HO1 s')
    (clAll (OAff A.hom) hc) (toHO1 A.hom) (clAll (OAff s') hc') (toHO1 s')
    (pullForm h.w) (pullHH1 h.w) (pullHO1 h.w)
    (GlobalTheory.T.de_rham_to_structure_h1_surjective R A g hab hsm) (exact_clAll_toHO1 A.hom hc) ?_ (exact_clAll_toHO1 s' hc') ?_ ?_ hW hH
  · exact (ofForm_injective_of_H0Const R' _ (OAff s') h0').comp (LinearEquiv.injective _)
  · intro x
    exact GlobalTheory.T.pull_closed_form_class R R' A.left X' A.hom s' (algebraMap R R') φ h.w hc hc' x
  · intro x
    exact toHO1_pullHH1 h.w x

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamGlobalFormsBaseChangeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_global_forms_base_change : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))), (∃ e : R' ⊗[R] HH1 A.hom ≃ₗ[R'] HH1 s', ∀ c, e (1 ⊗ₜ c) = pullHH1 h.w c) ∧ ∃ e : R' ⊗[R] GlobForm A.hom ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  first | exact @GlobalTheory.AbCoh.baseChange_HH1_globForm | exact GlobalTheory.AbCoh.baseChange_HH1_globForm | (intros; apply GlobalTheory.AbCoh.baseChange_HH1_globForm <;> assumption)
end
