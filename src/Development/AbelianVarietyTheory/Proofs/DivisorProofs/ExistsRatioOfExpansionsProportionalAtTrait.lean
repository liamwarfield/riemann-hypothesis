module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisDualPointsOfTangentModuleBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionTransferOfRelationGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionTransferOfRelationGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Trait.gs_scal_base {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) {Z : Scheme.{0}}
    (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left) (h : p ≫ T.β = p' ≫ C.α) (z : Z) (c : R) :
    gs p z ⊤ (scal T.G.hom (T.φ c)) = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c)) := by
  have hc : ∀ {A B : Type} [CommRing A] [CommRing B] {Y : Scheme.{0}} (q : Y ⟶ Sp B) (φ : A →+* B) (x : A),
      scal q (φ x) = scal (q ≫ spMap φ) x := by
    intro A B _ _ Y q φ x
    have e := congrArg (fun g => g.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    rw [e]
  rw [hc, hc]
  have hg : ∀ {A : Type} [CommRing A] {Y : Scheme.{0}} (f : Z ⟶ Y) (q : Y ⟶ Sp A) (x : A),
      gs f z ⊤ (scal q x) = gs (f ≫ q) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x) :=
    fun f q x => gs_pull f q z ⊤ trivial _
  rw [hg, hg]
  have e : p ≫ T.G.hom ≫ spMap T.φ = p' ≫ C.A.A.hom ≫ spMap (algebraMap R (FractionRing R)) := by
    have h1 : T.β ≫ C.G.hom = T.G.hom ≫ T.ξ := T.cart.1.w
    have h2 : C.α ≫ C.G.hom = C.A.A.hom ≫ C.gp := C.α_cart.1.w
    have h3 : C.gp ≫ C.π = spMap (algebraMap R (FractionRing R)) := C.gp_π
    rw [← T.ξ_π, ← h3, ← Category.assoc T.G.hom, ← h1, ← Category.assoc C.A.A.hom, ← h2]
    simp only [← Category.assoc, h]
  rw [e]

theorem Trait.exp_transfer : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k) (s₁ s₂ : SecK C.P.L.L C.α k) (r t : R) (u : W), (∀ (Z : Scheme.{0}) (p' : Z ⟶ C.A.A.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * sval s₁ p' z J = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * sval s₂ p' z J) → T.Exp 1 u s₂ F → T.Exp (T.φ t) (T.φ r * u) s₁ F := by
  intro R _ _ _ D C W _ _ _ T k F s₁ s₂ r t u hrel hExp
  have h1 := GlobalTheory.Mum.Trait.exp_mul_left R D C W T k s₂ F 1 u (T.φ r) hExp
  rw [_root_.mul_one] at h1
  obtain ⟨σ, hσ, hs⟩ := h1
  refine ⟨σ, hσ, ?_⟩
  intro Z p p' hp z J hJ
  rw [hs Z p p' hp z J hJ, T.gs_scal_base p p' hp z r, T.gs_scal_base p p' hp z t]
  exact (hrel Z p' z J hJ).symm

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionTransferOfRelationGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_transfer_of_relation_genericFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k) (s₁ s₂ : SecK C.P.L.L C.α k) (r t : R) (u : W), (∀ (Z : Scheme.{0}) (p' : Z ⟶ C.A.A.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * sval s₁ p' z J = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * sval s₂ p' z J) → T.Exp 1 u s₂ F → T.Exp (T.φ t) (T.φ r * u) s₁ F := by
  first | exact @GlobalTheory.Mum.Trait.exp_transfer | exact GlobalTheory.Mum.Trait.exp_transfer | (intros; apply GlobalTheory.Mum.Trait.exp_transfer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionsSameFamilyProportional
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionsSameFamilyProportional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.DVR

theorem Trait.exp_pair : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (F : IntFam (maximalIdeal R) D.toPre k) (s₁ s₂ : SecK C.P.L.L C.α k) (a₁ b₁ a₂ b₂ : W), T.Exp a₁ b₁ s₁ F → T.Exp a₂ b₂ s₂ F → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom (b₂ * a₁)) * sval s₁ p' z J = gs p z ⊤ (scal T.G.hom (b₁ * a₂)) * sval s₂ p' z J := by
  intro R _ _ _ hB D C W _ _ _ T k hk F s₁ s₂ a₁ b₁ a₂ b₂ h₁ h₂ Z p p' hpp' z J hJ
  obtain ⟨σ₁, ⟨τ₁, f₁, hc₁, hp₁, he₁⟩, hg₁⟩ := h₁
  obtain ⟨σ₂, ⟨τ₂, f₂, hc₂, hp₂, he₂⟩, hg₂⟩ := h₂
  have hf : f₁ = f₂ := funext fun x =>
    (SecPull.existsUnique_secPull _ _ _ _ _ _ _ D.toPre.P.isLB T.D'.toPre.P.isLB T.hD.w T.hD.w_gen (Fin 4)
      (T.D'.toPre.famφB x) (D.toPre.famφB (T.hD.xe x)) (DegPre.famε k) _ (ExpGTrans.famφB_pull T.hD x)
      (F.f (T.hD.xe x))).unique (hp₁ x) (hp₂ x)
  subst hf
  have hW := T.cdvr
  have := hW.1
  have := hW.2.2
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hGs : IsSemiAbelian T.G := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso T.cart (isGrpPullback_pullback C.G T.ξ)
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback T.ξ C.G C.semi)
  have hGc := hGs.geomConnected
  have H := (comb_eq_zero_iff_expansion_comb_eq_zero W _ bW T.D' T.A T.G T.U.toUnifPre k 2 ![1, -1] ![τ₁, τ₂]
    ![f₁, f₁] (fun i => by fin_cases i; exacts [he₁, he₂])).2 hGc (fun α j => by simp [Fin.sum_univ_two, Out.scal])
  have hτ : τ₁ = τ₂ := SecOps.sec_ext fun j => by
    have := H j
    simpa [Fin.sum_univ_two, Out.scal, add_neg_eq_zero] using this
  subst hτ
  choose J' hJ' using fun ψ : Z ⟶ T.G.left => exists_chart T.U.LG.isLB (ψ z)
  have c₁ := hc₁ Z p z J J' hJ hJ'
  have c₂ := hc₂ Z p z J J' hJ hJ'
  have g₁ := hg₁ Z p p' hpp' z J hJ
  have g₂ := hg₂ Z p p' hpp' z J hJ
  have m : ∀ a b : W, gs p z ⊤ (scal T.G.hom (a * b)) = gs p z ⊤ (scal T.G.hom a) * gs p z ⊤ (scal T.G.hom b) :=
    fun a b => by
      rw [show scal T.G.hom (a * b) = scal T.G.hom a * scal T.G.hom b by simp only [scal, map_mul]]
      exact gs_mul p z ⊤ (show p z ∈ (⊤ : T.G.left.Opens) from trivial) _ _
  have key : gs p z ⊤ (scal T.G.hom b₂) * sval σ₁ p z J = gs p z ⊤ (scal T.G.hom b₁) * sval σ₂ p z J := by
    rw [c₁, c₂]; ring
  rw [g₁, g₂] at key
  rw [m, m]
  linear_combination key

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionsSameFamilyProportionalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitExpansions_same_family_proportional : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (F : IntFam (maximalIdeal R) D.toPre k) (s₁ s₂ : SecK C.P.L.L C.α k) (a₁ b₁ a₂ b₂ : W), T.Exp a₁ b₁ s₁ F → T.Exp a₂ b₂ s₂ F → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom (b₂ * a₁)) * sval s₁ p' z J = gs p z ⊤ (scal T.G.hom (b₁ * a₂)) * sval s₂ p' z J := by
  first | exact @GlobalTheory.Mum.Trait.exp_pair | exact GlobalTheory.Mum.Trait.exp_pair | (intros; apply GlobalTheory.Mum.Trait.exp_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecKRatioTraitDescendsToFractionField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfBaseChangeRatioSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfBaseChangeRatioSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.ConstDescent

open TensorProduct

theorem mem_range_of_tmul_one_eq {K L B : Type} [Field K] [Field L] [CommRing B] [Algebra K L]
    [Algebra K B] (b₁ b₂ : B) (l : L) (hb : b₂ ≠ 0) (h : b₁ ⊗ₜ[K] (1 : L) = b₂ ⊗ₜ[K] l) :
    l ∈ Set.range (algebraMap K L) := by
  by_contra hl
  have hx : l ∉ (K ∙ (1 : L)) := by
    intro hm
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
    exact hl ⟨c, by rw [Algebra.algebraMap_eq_smul_one, hc]⟩
  obtain ⟨f, hf, hp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have h1 : f 1 = 0 := by
    have : f 1 ∈ (K ∙ (1 : L)).map f :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self 1)
    rw [hp] at this
    simpa using this
  have h2 := congrArg ((TensorProduct.rid K B).toLinearMap ∘ₗ LinearMap.lTensor B f) h
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.lTensor_tmul, TensorProduct.rid_tmul, h1, zero_smul] at h2
  exact hb ((smul_eq_zero.1 h2.symm).resolve_left hf)

end GlobalTheory.ConstDescent

namespace GlobalTheory.ConstDescent

theorem exists_affine_res_ne_zero {X : Scheme.{0}} {U : X.Opens} (f : Γ(X, U)) (hf : f ≠ 0) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ U), X.presheaf.map (homOfLE hVU).op f ≠ 0 := by
  have : ∃ (x : X) (hx : x ∈ U), X.presheaf.germ U x hx f ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf (TopCat.Presheaf.section_ext X.sheaf U f 0 (fun x hx => by rw [map_zero]; exact hc x hx))
  obtain ⟨x, hx, hne⟩ := this
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := U) hx
  refine ⟨V, hV, hVU, fun h0 => hne ?_⟩
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) x hxV, h0, map_zero]

end GlobalTheory.ConstDescent

namespace GlobalTheory.ConstDescent

theorem fromSpec_appLE_hom {X : Scheme.{0}} {U V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
    (e : ⊤ ≤ hV.fromSpec ⁻¹ᵁ U) (f : Γ(X, U)) :
    (Scheme.ΓSpecIso Γ(X, V)).hom.hom ((hV.fromSpec.appLE U ⊤ e).hom f) =
      (X.presheaf.map (homOfLE hVU).op).hom f := by
  have : hV.fromSpec.appLE U ⊤ e ≫ (Scheme.ΓSpecIso Γ(X, V)).hom =
      X.presheaf.map (homOfLE hVU).op := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_of_le hV U hVU, Category.assoc, Category.assoc,
      Category.assoc, ← Functor.map_comp_assoc]
    have h' : ((homOfLE le_top).op ≫ (homOfLE e).op :
        Opposite.op (⊤ : (Spec Γ(X, V)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := Subsingleton.elim _ _
    rw [h', CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  rw [← this]
  rfl

theorem appLE_top_top {X Y : Scheme.{0}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem appLE_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (hfg : f = g) (U : Y.Opens) (V : X.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V e₁ = g.appLE U V e₂ := by
  subst hfg; rfl

end GlobalTheory.ConstDescent

namespace GlobalTheory.ConstDescent

open TensorProduct

theorem mem_range_of_pullback_eq {K L : Type} [Field K] [Field L] (ψ : K →+* L) {X : Scheme.{0}}
    (h : X ⟶ Sp K) (U : X.Opens) (f₁ f₂ : Γ(X, U)) (l : L) (hf : f₂ ≠ 0)
    (heq : ((pullback.fst h (spMap ψ)).app U).hom f₁ =
      ((pullback.fst h (spMap ψ)).app U).hom f₂ * resTop _ (scal (pullback.snd h (spMap ψ)) l)) :
    l ∈ Set.range ψ := by
  obtain ⟨V, hV, hVU, hne⟩ := exists_affine_res_ne_zero f₂ hf
  let B : CommRingCat := Γ(X, V)
  let e : Spec B ⟶ X := hV.fromSpec
  let α : CommRingCat.of K ⟶ B := Spec.preimage (e ≫ h)
  letI : Algebra K B := α.hom.toAlgebra
  letI : Algebra K L := ψ.toAlgebra
  let Z : CommRingCat := CommRingCat.of (B ⊗[K] L)
  let a : Spec Z ⟶ Spec B := Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
  let b : Spec Z ⟶ Sp L :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : L →ₐ[K] B ⊗[K] L).toRingHom)
  have hcomm : (a ≫ e) ≫ h = b ≫ spMap ψ := by
    rw [Category.assoc, ← Spec.map_preimage (e ≫ h)]
    simp only [a, b, spMap, ← Spec.map_comp]
    congr 1
    ext x
    show (algebraMap K B x) ⊗ₜ[K] (1 : L) = (1 : B) ⊗ₜ[K] (algebraMap K L x)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let k : Spec Z ⟶ pullback h (spMap ψ) := pullback.lift (a ≫ e) b hcomm
  have hk1 : k ≫ pullback.fst h (spMap ψ) = a ≫ e := pullback.lift_fst _ _ _
  have hk2 : k ≫ pullback.snd h (spMap ψ) = b := pullback.lift_snd _ _ _
  have heU : ⊤ ≤ e ⁻¹ᵁ U := by
    intro z _
    show e z ∈ U
    apply hVU
    have hr : e z ∈ Set.range hV.fromSpec := ⟨z, rfl⟩
    rw [hV.range_fromSpec] at hr
    exact hr
  have hk : ⊤ ≤ k ⁻¹ᵁ ((pullback.fst h (spMap ψ)) ⁻¹ᵁ U) := by
    intro z _
    show (pullback.fst h (spMap ψ)) (k z) ∈ U
    rw [← Scheme.Hom.comp_apply, hk1, Scheme.Hom.comp_apply]
    exact heU (show a z ∈ (⊤ : (Spec B).Opens) from trivial)

  have heU' : ⊤ ≤ (a ≫ e) ⁻¹ᵁ U := by
    intro z _
    exact heU (show a z ∈ (⊤ : (Spec B).Opens) from trivial)
  have key1m : (pullback.fst h (spMap ψ)).app U ≫ k.appLE _ ⊤ hk =
      e.appLE U ⊤ heU ≫ (Scheme.ΓSpecIso B).hom ≫
        CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ (Scheme.ΓSpecIso Z).inv := by
    refine (Scheme.Hom.comp_appLE k _ U ⊤ hk).symm.trans ?_
    refine (appLE_congr hk1 U ⊤ _ heU').trans ?_
    refine (Scheme.Hom.appLE_comp_appLE a e U ⊤ ⊤ heU (fun _ _ => trivial)).symm.trans ?_
    congr 1
    refine (appLE_top_top a _).trans ?_
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact Scheme.ΓSpecIso_naturality _
  have key2m : (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ (pullback.snd h (spMap ψ)).appTop ≫
      k.appTop = CommRingCat.ofHom (Algebra.TensorProduct.includeRight : L →ₐ[K] B ⊗[K] L).toRingHom ≫
        (Scheme.ΓSpecIso Z).inv := by
    rw [← Scheme.Hom.comp_appTop, hk2, ← Scheme.ΓSpecIso_inv_naturality]
  have key1 : ∀ s : Γ(X, U), (k.appLE _ ⊤ hk).hom (((pullback.fst h (spMap ψ)).app U).hom s) =
      (Scheme.ΓSpecIso Z).inv.hom
        (((Scheme.ΓSpecIso B).hom.hom ((e.appLE U ⊤ heU).hom s)) ⊗ₜ[K] (1 : L)) := fun s =>
    congrArg (fun φ => φ.hom s) key1m
  have key2 : (k.appLE _ ⊤ hk).hom (resTop _ (scal (pullback.snd h (spMap ψ)) l)) =
      (Scheme.ΓSpecIso Z).inv.hom ((1 : B) ⊗ₜ[K] l) := by
    have e1 : ∀ c, (k.appLE _ ⊤ hk).hom (resTop ((pullback.fst h (spMap ψ)) ⁻¹ᵁ U) c) =
        k.appTop.hom c := by
      intro c
      show ((pullback h (spMap ψ)).presheaf.map _ ≫ k.appLE _ ⊤ hk).hom c = _
      rw [Scheme.Hom.map_appLE, appLE_top_top]
    rw [e1]
    exact congrArg (fun φ => φ.hom l) key2m
  have h3 := congrArg (k.appLE _ ⊤ hk).hom heq
  rw [map_mul, key1, key1, key2, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
    _root_.one_mul] at h3
  have inj : Function.Injective (Scheme.ΓSpecIso Z).inv.hom := fun x y hxy => by
    simpa using congrArg (Scheme.ΓSpecIso Z).hom.hom hxy
  have h4 := inj h3
  have hb : (Scheme.ΓSpecIso B).hom.hom ((e.appLE U ⊤ heU).hom f₂) ≠ 0 := by
    rw [fromSpec_appLE_hom hV hVU heU f₂]
    exact hne
  obtain ⟨c, hc⟩ := mem_range_of_tmul_one_eq _ _ l hb h4
  exact ⟨c, hc⟩

end GlobalTheory.ConstDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfBaseChangeRatioSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_of_base_change_ratio_sections : ∀ {K L : Type} [Field K] [Field L] (ψ : K →+* L) {X : Scheme.{0}} (h : X ⟶ Sp K) (U : X.Opens) (f₁ f₂ : Γ(X, U)) (l : L), f₂ ≠ 0 → ((pullback.fst h (spMap ψ)).app U).hom f₁ = ((pullback.fst h (spMap ψ)).app U).hom f₂ * resTop _ (scal (pullback.snd h (spMap ψ)) l) → l ∈ Set.range ψ := by
  first | exact @GlobalTheory.ConstDescent.mem_range_of_pullback_eq | exact GlobalTheory.ConstDescent.mem_range_of_pullback_eq | (intros; apply GlobalTheory.ConstDescent.mem_range_of_pullback_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointFactorOfInjectiveBaseMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointFactorOfInjectiveBaseMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_fractionRing_map_comp_eq {R W B : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] [CommRing B]
    (φ : R →+* W) (hφ : Function.Injective φ) (c : R →+* B) (a : B →+* FractionRing R) (b : B →+* FractionRing W)
    (ha : Function.Injective a) (hac : a.comp c = algebraMap R (FractionRing R))
    (hbc : b.comp c = (algebraMap W (FractionRing W)).comp φ) :
    ∃ ψ : FractionRing R →+* FractionRing W,
      ψ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ ∧ ψ.comp a = b := by
  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp φ) :=
    (IsFractionRing.injective W (FractionRing W)).comp hφ
  refine ⟨IsFractionRing.lift hinj, ?_, ?_⟩
  · ext r
    simp only [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  · ext x
    obtain ⟨r, r', hr', h⟩ := IsFractionRing.div_surjective (A := R) (a x)
    have h0 : algebraMap R (FractionRing R) r' ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr'
    have hac' : ∀ y, a (c y) = algebraMap R (FractionRing R) y := fun y => RingHom.congr_fun hac y
    have hbc' : ∀ y, b (c y) = ((algebraMap W (FractionRing W)).comp φ) y := fun y => RingHom.congr_fun hbc y
    have h1 : x * c r' = c r := by
      apply ha
      rw [map_mul, hac', hac', ← h, div_mul_cancel₀ _ h0]
    have h2 : ((algebraMap W (FractionRing W)).comp φ) r' ≠ 0 := by
      intro h3
      exact nonZeroDivisors.ne_zero hr' (hinj (h3.trans (map_zero _).symm))
    rw [RingHom.comp_apply, ← h, map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap,
      div_eq_iff h2, ← hbc', ← hbc', ← map_mul, h1]

theorem Modif.exists_generic_factor : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ ξ : Sp W ⟶ M.S, ξ ≫ M.π = spMap φ → ∃ ψ : FractionRing R →+* FractionRing W, ψ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ ∧ spMap ψ ≫ M.gp = jK W ≫ ξ := by
  intro R _ _ M W _ _ φ hφ ξ hξ
  haveI := M.integral
  haveI := M.dominant
  let s : M.S := (jK W ≫ ξ) (IsLocalRing.closedPoint (FractionRing W))
  obtain ⟨B, f, hf, hs, -⟩ := M.S.exists_affine_mem_range_and_range_subset (x := s) (U := ⊤) trivial
  have hb : Set.range (jK W ≫ ξ) ⊆ Set.range f := by
    rintro _ ⟨y, rfl⟩
    have : y = IsLocalRing.closedPoint (FractionRing W) := Subsingleton.elim (α := PrimeSpectrum (FractionRing W)) _ _
    rw [this]; exact hs
  have ha : Set.range M.gp ⊆ Set.range f := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := M.gp.denseRange.exists_mem_open f.isOpenEmbedding.isOpen_range ⟨s, hs⟩
    have : y = z := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    rw [this]; exact hz
  obtain ⟨a, ha'⟩ := Spec.map_surjective (IsOpenImmersion.lift f M.gp ha)
  obtain ⟨b, hb'⟩ := Spec.map_surjective (IsOpenImmersion.lift f (jK W ≫ ξ) hb)
  obtain ⟨c, hc'⟩ := Spec.map_surjective (f ≫ M.π)
  have e1 : Spec.map a ≫ f = M.gp := by rw [ha', IsOpenImmersion.lift_fac]
  have e2 : Spec.map b ≫ f = jK W ≫ ξ := by rw [hb', IsOpenImmersion.lift_fac]
  have hac : c ≫ a = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hc', ← Category.assoc, e1, M.gp_π]
  have hbc : c ≫ b = CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap W (FractionRing W)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hc', ← Category.assoc, e2, Category.assoc, hξ, Spec.map_comp]
  have hred : IsReduced (Spec B) := isReduced_of_isOpenImmersion f
  have hred' : _root_.IsReduced B := (affine_isReduced_iff B).1 hred
  have hdom : IsDominant (Spec.map a) := by
    haveI : IsDominant (Spec.map a ≫ f) := e1 ▸ M.dominant
    exact IsDominant.of_comp_of_isOpenImmersion _ f
  have hainj : Function.Injective a.hom := by
    have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical a.hom).1 hdom.1
    rw [nilradical_eq_zero] at this
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 this)
  obtain ⟨ψ, h1, h2⟩ := exists_fractionRing_map_comp_eq φ hφ c.hom a.hom b.hom hainj
    (congrArg CommRingCat.Hom.hom hac) (congrArg CommRingCat.Hom.hom hbc)
  refine ⟨ψ, h1, ?_⟩
  have h3 : a ≫ CommRingCat.ofHom ψ = b := by
    ext1; exact h2
  rw [← e1, ← e2, ← h3, Spec.map_comp, Category.assoc]

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointFactorOfInjectiveBaseMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericPoint_factor_of_injective_base_map : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ ξ : Sp W ⟶ M.S, ξ ≫ M.π = spMap φ → ∃ ψ : FractionRing R →+* FractionRing W, ψ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ ∧ spMap ψ ≫ M.gp = jK W ≫ ξ := by
  first | exact @GlobalTheory.Mum.Modif.exists_generic_factor | exact GlobalTheory.Mum.Modif.exists_generic_factor | (intros; apply GlobalTheory.Mum.Modif.exists_generic_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecKRatioTraitDescendsToFractionField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatioDesc

open ReciprocityTheory.ChartRestriction.G.DVR.TG

theorem pull_fst_app_injective {K L : Type} [Field K] [Field L] (ψ : K →+* L) {X : Scheme.{0}} (h : X ⟶ Sp K)
    (U : X.Opens) : Function.Injective ((pullback.fst h (spMap ψ)).app U).hom := by
  have : Flat (spMap ψ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := ψ.toAlgebra
    exact (RingHom.flat_algebraMap_iff).2 inferInstance
  have : Surjective (spMap ψ) := by
    constructor
    intro x
    exact ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩
  exact app_injective_of_flat_surj _ U

variable {A : Type} [CommRing A] {X Y Z : Scheme.{0}}

theorem scal_mul' (p : Y ⟶ Sp A) (a b : A) : scal p (a * b) = scal p a * scal p b := by
  unfold scal; rw [map_mul, map_mul]

theorem scal_one' (p : Y ⟶ Sp A) : scal p 1 = 1 := by
  unfold scal; rw [map_one, map_one]

theorem scal_comp' (f : Z ⟶ Y) (p : Y ⟶ Sp A) (r : A) : scal (f ≫ p) r = f.appTop.hom (scal p r) := by
  unfold scal; rw [Scheme.Hom.comp_appTop]; rfl

theorem scal_spMap {B : Type} [CommRing B] (g : Y ⟶ Sp B) (ψ : A →+* B) (r : A) :
    scal (g ≫ Spec.map (CommRingCat.ofHom ψ)) r = scal g (ψ r) := by
  rw [scal_comp']
  unfold scal
  congr 1
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)
  exact (congrArg (fun f => f.hom r) this).symm

theorem gs_top' (f : Z ⟶ Y) (z : Z) (a : Γ(Y, ⊤)) : gs f z ⊤ a = gs (𝟙 Z) z ⊤ (f.appTop.hom a) := by
  have := gs_pull (𝟙 Z) f z ⊤ trivial a
  rw [Category.id_comp] at this
  exact this.symm

theorem gs_zero'' (f : Z ⟶ Y) (z : Z) (U : Y.Opens) : gs f z U 0 = 0 := by
  unfold gs; split_ifs <;> simp

abbrev sg (g : Z ⟶ Sp A) (z : Z) (a : A) : Z.presheaf.stalk z := gs (𝟙 Z) z ⊤ (scal g a)

theorem sg_mul (g : Z ⟶ Sp A) (z : Z) (a b : A) : sg g z (a * b) = sg g z a * sg g z b := by
  unfold sg; rw [scal_mul', gs_mul _ z ⊤ trivial]

theorem sg_one (g : Z ⟶ Sp A) (z : Z) : sg g z 1 = 1 := by
  unfold sg; rw [scal_one', gs_eq _ z ⊤ trivial, map_one, map_one]

theorem sg_isUnit {F : Type} [Field F] (g : Z ⟶ Sp F) (z : Z) {a : F} (ha : a ≠ 0) : IsUnit (sg g z a) :=
  have h1 : sg g z a * sg g z a⁻¹ = 1 := by rw [← sg_mul, mul_inv_cancel₀ ha, sg_one]
  ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

end GlobalTheory.Mum.RatioDesc

namespace GlobalTheory.Mum

open GlobalTheory.Mum.RatioDesc

theorem secK_ratio_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s₁ s₂ : SecK C.P.L.L C.α k) (c d : W), c ≠ 0 → d ≠ 0 → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom c) * sval s₁ p' z J = gs p z ⊤ (scal T.G.hom d) * sval s₂ p' z J) → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (Z : Scheme.{0}) (p' : Z ⟶ C.A.A.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * sval s₁ p' z J = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * sval s₂ p' z J := by
  intro R _ _ _ _ D C W _ _ _ T k s₁ s₂ c d hc hd H
  obtain ⟨ψ, hψR, hψ⟩ := GlobalTheory.T.exists_genericPoint_factor_of_injective_base_map R C.toModif W T.φ T.inj T.ξ T.ξ_π
  let Y : Scheme.{0} := pullback C.A.A.hom (spMap ψ)
  let q : Y ⟶ C.A.A.left := pullback.fst C.A.A.hom (spMap ψ)
  let g : Y ⟶ Sp (FractionRing W) := pullback.snd C.A.A.hom (spMap ψ)
  have hw : (q ≫ C.α) ≫ C.G.hom = (g ≫ jK W) ≫ T.ξ := by
    simp only [Category.assoc]
    rw [C.α_cart.1.w, ← Category.assoc q, pullback.condition, Category.assoc]
    exact congrArg (g ≫ ·) hψ
  let p := T.cart.1.lift (q ≫ C.α) (g ≫ jK W) hw
  have hp : p ≫ T.β = q ≫ C.α := T.cart.1.lift_fst _ _ _
  have hpG : p ≫ T.G.hom = g ≫ jK W := T.cart.1.lift_snd _ _ _
  have hsc : ∀ (y : Y) (w : W),
      gs p y ⊤ (scal T.G.hom w) = sg g y (algebraMap W (FractionRing W) w) := by
    intro y w
    rw [gs_top', ← scal_comp', hpG, scal_spMap]

  set c' := algebraMap W (FractionRing W) c with hc'
  set d' := algebraMap W (FractionRing W) d with hd'
  have hc0 : c' ≠ 0 := fun h => hc (IsFractionRing.injective W (FractionRing W) (h.trans (map_zero _).symm))
  have hd0 : d' ≠ 0 := fun h => hd (IsFractionRing.injective W (FractionRing W) (h.trans (map_zero _).symm))
  let Uc : (Fin 1 → C.P.L.L.ι) → C.A.A.left.Opens := fun j => LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) j
  have G0 : ∀ (j : Fin 1 → C.P.L.L.ι) (y : Y), q y ∈ Uc j →
      sg g y c' * gs q y (Uc j) (s₁.f j) = sg g y d' * gs q y (Uc j) (s₂.f j) := by
    intro j y hy
    obtain ⟨J, hJ, hJj⟩ := exists_good C.P.L.L C.P.L.isLB y (fun _ : Unit => q ≫ C.α) (fun _ => j 0)
      (fun _ _ _ => rfl) (fun _ => by simpa using Set.mem_iInter.1 hy 0)
    have e := H Y p q hp y J hJ
    have hj : ∀ i : Fin 1, J (q ≫ C.α) = j i := fun i => by rw [Subsingleton.elim i 0]; exact hJj ()
    rw [hsc, hsc, sval_of s₁ q y J j hj, sval_of s₂ q y J j hj] at e
    exact e

  have key : ∃ m₀ : FractionRing R, m₀ ≠ 0 ∧ ∀ (j : Fin 1 → C.P.L.L.ι) (y : Y), q y ∈ Uc j →
      gs q y (Uc j) (s₁.f j) = sg g y (ψ m₀) * gs q y (Uc j) (s₂.f j) := by
    by_cases h0 : ∀ j, s₂.f j = 0
    · refine ⟨1, one_ne_zero, fun j y hy => ?_⟩
      have e := G0 j y hy
      have hz : gs q y (Uc j) (s₂.f j) = 0 := by rw [h0 j]; exact gs_zero'' _ _ _
      rw [hz, mul_zero] at e
      rw [hz, mul_zero]
      exact (sg_isUnit g y hc0).mul_left_cancel (e.trans (mul_zero _).symm)
    · push Not at h0
      obtain ⟨j₀, hj₀⟩ := h0
      have e : ((q.app (Uc j₀)).hom (s₁.f j₀)) = (q.app (Uc j₀)).hom (s₂.f j₀) * resTop _ (scal g (d' / c')) := by
        apply fn_ext
        intro y hy
        have hy' : q ((𝟙 Y) y) ∈ Uc j₀ := by simpa using hy
        have e1 := gs_pull (𝟙 Y) q y (Uc j₀) hy' (s₁.f j₀)
        have e2 := gs_pull (𝟙 Y) q y (Uc j₀) hy' (s₂.f j₀)
        rw [Category.id_comp] at e1 e2
        rw [gs_mul _ y _ hy, gs_res _ y le_top hy]
        erw [e1, e2]
        apply (sg_isUnit g y hc0).mul_left_cancel
        have hcd : c' * (d' / c') = d' := by field_simp
        rw [G0 j₀ y hy]
        change _ = sg g y c' * (_ * sg g y (d' / c'))
        rw [mul_comm _ (sg g y (d' / c')), ← _root_.mul_assoc, ← sg_mul, hcd]
      obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.mem_range_of_base_change_ratio_sections ψ C.A.A.hom (Uc j₀) (s₁.f j₀) (s₂.f j₀) (d' / c') hj₀ e
      refine ⟨m₀, fun h => ?_, fun j y hy => ?_⟩
      · rw [h, map_zero] at hm₀
        exact div_ne_zero hd0 hc0 hm₀.symm
      · apply (sg_isUnit g y hc0).mul_left_cancel
        have hcd : c' * (d' / c') = d' := by field_simp
        rw [G0 j y hy, hm₀, ← _root_.mul_assoc, ← sg_mul, hcd]

  obtain ⟨m₀, hm0, hm⟩ := key
  obtain ⟨r, t, ht, hrt⟩ := IsFractionRing.div_surjective (A := R) m₀
  have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
  have ht' : algebraMap R (FractionRing R) t ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hm0
    rw [← hrt, map_zero, zero_div]
  refine ⟨r, t, hr0, ht0, ?_⟩
  have hK : algebraMap R (FractionRing R) t * m₀ = algebraMap R (FractionRing R) r := by
    rw [← hrt]; field_simp
  let F₁ : ∀ j, Γ(C.A.A.left, Uc j) := fun j => s₁.f j
  let F₂ : ∀ j, Γ(C.A.A.left, Uc j) := fun j => s₂.f j
  have sec : ∀ j : Fin 1 → C.P.L.L.ι, resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * F₁ j =
      resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * F₂ j := by
    intro j
    apply pull_fst_app_injective ψ C.A.A.hom (Uc j)
    apply fn_ext
    intro y hy
    have hy' : q ((𝟙 Y) y) ∈ Uc j := by simpa using hy
    have e1 := gs_pull (𝟙 Y) q y (Uc j) hy' (resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * F₁ j)
    have e2 := gs_pull (𝟙 Y) q y (Uc j) hy' (resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * F₂ j)
    rw [Category.id_comp] at e1 e2
    erw [e1, e2]
    rw [gs_mul q y _ hy, gs_mul q y _ hy, gs_res q y le_top hy, gs_res q y le_top hy, gs_top' q, gs_top' q,
      ← scal_comp', ← scal_comp', pullback.condition, scal_spMap, scal_spMap]
    change sg g y _ * _ = sg g y _ * _
    rw [hm j y hy, ← _root_.mul_assoc, ← sg_mul, ← map_mul, hK]
  intro Z p' z J hJ
  have hm' : p' z ∈ Uc (fun _ => J (p' ≫ C.α)) := hJ.mem (fun _ : Fin 1 => C.α) p'
  have e := congrArg (gs p' z (Uc (fun _ => J (p' ≫ C.α)))) (sec (fun _ => J (p' ≫ C.α)))
  rw [gs_mul p' z _ hm', gs_mul p' z _ hm', gs_res p' z le_top hm', gs_res p' z le_top hm'] at e
  exact e

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecKRatioTraitDescendsToFractionFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secK_ratio_trait_descends_to_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s₁ s₂ : SecK C.P.L.L C.α k) (c d : W), c ≠ 0 → d ≠ 0 → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom c) * sval s₁ p' z J = gs p z ⊤ (scal T.G.hom d) * sval s₂ p' z J) → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (Z : Scheme.{0}) (p' : Z ⟶ C.A.A.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * sval s₁ p' z J = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * sval s₂ p' z J := by
  first | exact @GlobalTheory.Mum.secK_ratio_descends | exact GlobalTheory.Mum.secK_ratio_descends | (intros; apply GlobalTheory.Mum.secK_ratio_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioOfExpansionsProportionalAtTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_ratio_of_exp_one_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ (G : IntFam (maximalIdeal R) D.toPre k) (S Ψ : SecK C.P.L.L C.α k), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u Ψ G) → ∀ (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsLocalRing W₀] (T₀ : Trait C W₀) (a₀ b₀ : W₀), a₀ ≠ 0 → b₀ ≠ 0 → T₀.Exp a₀ b₀ S G → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp (T.φ t) (T.φ r * u) S G := by
  intro R _ _ _ hB D C k hk G S Ψ hΨ W₀ _ _ _ T₀ a₀ b₀ ha hb hS
  obtain ⟨u₀, hu₀⟩ := hΨ W₀ T₀
  have hp := GlobalTheory.T.traitExpansions_same_family_proportional R hB D C W₀ T₀ k hk G S Ψ a₀ b₀ 1 (u₀ : W₀) hS hu₀
  obtain ⟨r, t, hr, ht, hrt⟩ := GlobalTheory.T.secK_ratio_trait_descends_to_fractionField R hB D C W₀ T₀ k S Ψ ((u₀ : W₀) * a₀) (b₀ * 1)
    (mul_ne_zero u₀.ne_zero ha) (by rw [_root_.mul_one]; exact hb) hp
  refine ⟨r, t, hr, ht, fun W _ _ _ T => ?_⟩
  obtain ⟨u, hu⟩ := hΨ W T
  exact ⟨u, GlobalTheory.T.expansion_transfer_of_relation_genericFibre R D C W T k G S Ψ r t (u : W) hrt hu⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioOfExpansionsProportionalAtTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ratio_of_expansions_proportional_at_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ (G : IntFam (maximalIdeal R) D.toPre k) (S Ψ : SecK C.P.L.L C.α k), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u Ψ G) → ∀ (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsLocalRing W₀] (T₀ : Trait C W₀) (a₀ b₀ : W₀), a₀ ≠ 0 → b₀ ≠ 0 → T₀.Exp a₀ b₀ S G → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp (T.φ t) (T.φ r * u) S G := by
  first | exact @GlobalTheory.Mum.exists_ratio_of_exp_one_trait | exact GlobalTheory.Mum.exists_ratio_of_exp_one_trait | (intros; apply GlobalTheory.Mum.exists_ratio_of_exp_one_trait <;> assumption)
end
