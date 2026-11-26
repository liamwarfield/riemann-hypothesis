module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RangeRestrictCompSubtypeOfOrthogonalOfNe
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineOpenBiInfOfLe
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSecOnRTensorEquiv
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
noncomputable section
namespace GlobalTheory.AbLaw.ExtProd

theorem exists_tensor_addEquiv {R A B C P Q N N' : Type*} [CommRing R] [CommRing A] [CommRing B]
    [CommRing C] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A C] [Algebra B C]
    [IsScalarTower R A C] [IsScalarTower R B C] [Algebra.IsPushout R B A C]
    [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P]
    [AddCommGroup Q] [Module R Q] [Module B Q] [IsScalarTower R B Q]
    [AddCommGroup N] [Module A N] [Module C N] [IsScalarTower A C N]
    [AddCommGroup N'] [Module B N'] [Module C N'] [IsScalarTower B C N']
    {j : P →ₗ[A] N} {j' : Q →ₗ[B] N'} (hj : IsBaseChange C j) (hj' : IsBaseChange C j') :
    ∃ E : P ⊗[R] Q ≃+ N ⊗[C] N', (∀ x y, E (x ⊗ₜ y) = j x ⊗ₜ j' y) ∧
      ∀ (r : R) z, E (r • z) = algebraMap R C r • E z := by
  let E₁ : P ⊗[R] Q ≃ₗ[R] Q ⊗[R] P := TensorProduct.comm R P Q
  let E₂ : Q ⊗[R] P ≃ₗ[B] Q ⊗[B] (B ⊗[R] P) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R B B Q P).symm
  let E₃ : Q ⊗[B] (B ⊗[R] P) ≃ₗ[B] (C ⊗[A] P) ⊗[B] Q :=
    TensorProduct.comm B _ _ ≪≫ₗ
      (Algebra.IsPushout.cancelBaseChange R B A C P).symm.rTensor Q
  let E₄ : (C ⊗[A] P) ⊗[B] Q ≃ₗ[C] (C ⊗[A] P) ⊗[C] (C ⊗[B] Q) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B C C (C ⊗[A] P) Q).symm
  let E₅ : (C ⊗[A] P) ⊗[C] (C ⊗[B] Q) ≃ₗ[C] N ⊗[C] N' := TensorProduct.congr hj.equiv hj'.equiv
  let E : P ⊗[R] Q ≃+ N ⊗[C] N' :=
    (((E₁.toAddEquiv.trans E₂.toAddEquiv).trans E₃.toAddEquiv).trans E₄.toAddEquiv).trans
      E₅.toAddEquiv
  have hE (x : P) (y : Q) : E (x ⊗ₜ y) = j x ⊗ₜ j' y := by
    change E₅ (E₄ (E₃ (E₂ (E₁ (x ⊗ₜ y))))) = _
    simp [E₁, E₂, E₃, E₄, E₅]
  refine ⟨E, hE, fun r z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  | tmul x y =>
    rw [TensorProduct.smul_tmul', hE, hE, TensorProduct.smul_tmul', ← algebraMap_smul A r x,
      j.map_smul (algebraMap R A r) x, IsScalarTower.algebraMap_apply R A C, algebraMap_smul C]

section Mul

open GlobalTheory.LB GlobalTheory.AbLaw.SecOn

variable {X : Scheme.{0}} {M H : LB X} {V W : X.Opens}

def mul (s : SecOn M V) (t : SecOn H V) : SecOn (tw M H 1) V :=
  twMk 1 (fun p k => rs X (inf_le_inf_left V inf_le_left) (coord s p) *
      rs X (inf_le_inf_left V inf_le_right) (coord t k))
    fun p q k l O hp hq hM hH => by
      rw [map_mul, map_mul, rs_rs, rs_rs, rs_rs, rs_rs,
        compat s p q _ (hq.trans (inf_le_inf_left V inf_le_left)) hM,
        compat t k l _ (hq.trans (inf_le_inf_left V inf_le_right)) hH, zpow_one, ← val_res hH,
        ← val_res hM]
      simp only [Units.val_mul]
      ring

@[simp] theorem twCoord_mul (s : SecOn M V) (t : SecOn H V) (p : M.ι) (k : H.ι) :
    twCoord (mul s t) p k = rs X (inf_le_inf_left V inf_le_left) (coord s p) *
      rs X (inf_le_inf_left V inf_le_right) (coord t k) := rfl

theorem restrict_mul (h : W ≤ V) (s : SecOn M V) (t : SecOn H V) :
    restrict _ h (mul s t) = mul (restrict M h s) (restrict H h t) :=
  tw_ext fun p k => by
    simp only [twCoord_mul, twCoord_restrict, coord_restrict, map_mul, rs_rs]


variable (M H V) in
def secMulHom : SecOn M V ⊗[Γ(X, V)] SecOn H V →ₗ[Γ(X, V)] SecOn (tw M H 1) V :=
  TensorProduct.lift <| LinearMap.mk₂ Γ(X, V) mul
    (fun s s' t => tw_ext fun p k => by
      simp only [twCoord_mul, twCoord_add, coord_add, map_add (f := _), add_mul])
    (fun a s t => tw_ext fun p k => by
      simp only [twCoord_mul, twCoord_smul, coord_smul, map_mul, rs_rs, _root_.mul_assoc])
    (fun s t t' => tw_ext fun p k => by
      simp only [twCoord_mul, twCoord_add, coord_add, map_add (f := _), mul_add])
    (fun a s t => tw_ext fun p k => by
      simp only [twCoord_mul, twCoord_smul, coord_smul, map_mul, rs_rs]
      exact mul_left_comm _ _ _)

@[simp] theorem secMulHom_tmul (s : SecOn M V) (t : SecOn H V) :
    secMulHom M H V (s ⊗ₜ t) = mul s t := rfl

theorem exists_mul_eq (hM : M.IsLB) (hH : H.IsLB) (p : M.ι) (k : H.ι) (hp : V ≤ M.U p)
    (hk : V ≤ H.U k) (x : SecOn (tw M H 1) V) : ∃ s t, mul s t = x := by
  have hT := isLB_tw hM hH 1
  have hpk : V ≤ (tw M H 1).U (p, k) := le_inf hp hk
  have key (s : SecOn M V) (t : SecOn H V) :
      chart hT (p, k) hpk (mul s t) = chart hM p hp s * chart hH k hk t := by
    change rs X (le_inf le_rfl (le_inf hp hk)) (twCoord (mul s t) p k) = _
    rw [twCoord_mul, map_mul, rs_rs, rs_rs, chart_apply, chart_apply]
  refine ⟨(chart hM p hp).symm (chart hT (p, k) hpk x), (chart hH k hk).symm 1,
    (chart hT (p, k) hpk).injective ?_⟩
  rw [key, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, _root_.mul_one]

theorem secMulHom_bijective (hM : M.IsLB) (hH : H.IsLB) (hV : IsAffineOpen V) :
    Function.Bijective (secMulHom M H V) := by
  have hT := isLB_tw hM hH 1
  haveI := invertible hM hV
  haveI := invertible hH hV
  haveI := invertible hT hV
  refine Module.Invertible.bijective_of_surjective fun x => ?_
  let S : Set Γ(X, V) := {a | ∃ p k, X.basicOpen a ≤ M.U p ∧ X.basicOpen a ≤ H.U k}
  have hS : Ideal.span S = ⊤ := by
    rw [← hV.self_le_iSup_basicOpen_iff]
    intro y hy
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ y))
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (Set.mem_univ y))
    obtain ⟨a, ha, hya⟩ := hV.exists_basicOpen_le (V := M.U p ⊓ H.U k) ⟨y, hp, hk⟩ hy
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨⟨a, p, k, ha.trans inf_le_left, ha.trans inf_le_right⟩, hya⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (LinearMap.range (secMulHom M H V)) S hS x ?_
  rintro ⟨a, p, k, hp, hk⟩
  have h := X.basicOpen_le a
  obtain ⟨s, t, e⟩ := exists_mul_eq hM hH p k hp hk (restrict _ h x)
  obtain ⟨n, s', hs⟩ := exists_pow_smul_eq_restrict hM hV.isCompact hV.isQuasiSeparated a h rfl s
  obtain ⟨m, t', ht⟩ := exists_pow_smul_eq_restrict hH hV.isCompact hV.isQuasiSeparated a h rfl t
  obtain ⟨l, hl⟩ := exists_pow_smul_eq_zero hT hV.isCompact a h rfl
    (a ^ (n + m) • x - mul s' t') (by
      rw [map_sub, restrict_mul, ← hs, ← ht, map_smulₛₗ, ← e, ← secMulHom_tmul, ← secMulHom_tmul,
        TensorProduct.smul_tmul_smul, map_smul, map_pow, pow_add, sub_self])
  refine ⟨l + (n + m), a ^ l • (s' ⊗ₜ t'), ?_⟩
  rw [smul_sub, sub_eq_zero, ← mul_smul, ← pow_add] at hl
  rw [map_smul, secMulHom_tmul, ← hl]

end Mul

section Pullback

variable {R : Type} [CommRing R] {Y Y' Z : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)}
  {f' : Y' ⟶ Spec (CommRingCat.of R)} {p₁ : Z ⟶ Y} {p₂ : Z ⟶ Y'}

theorem isAffineOpen_inf (H : IsPullback p₁ p₂ f f') {U : Y.Opens} {W : Y'.Opens}
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) : IsAffineOpen (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ W) := by
  have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of R))
  have : IsAffine _ := hU
  have : IsAffine _ := hW
  exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W) (UX := U) le_top le_top
    rfl).isoPullback.hom

theorem isPushout_prod (H : IsPullback p₁ p₂ f f') {U : Y.Opens} {W : Y'.Opens} {O : Z.Opens}
    (e₁ : O ≤ p₁ ⁻¹ᵁ U) (e₂ : O ≤ p₂ ⁻¹ᵁ W) (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (e : O = p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ W) :
    IsPushout (CommRingCat.ofHom (cst f' W)) (CommRingCat.ofHom (cst f U))
      (p₂.appLE W O e₂) (p₁.appLE U O e₁) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := W) (UX := U) (UY := O) le_top
    le_top e).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) hW hU)
  refine po.flip.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp [cst_eq_appLE]
  · simp [cst_eq_appLE]
  · simp
  · simp

end Pullback

end GlobalTheory.AbLaw.ExtProd

namespace GlobalTheory.AbLaw


open ExtProd in
theorem exists_secOnR_tensor_equiv : ∀ (R : Type) [CommRing R] (Y Y' Z : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (f' : Y' ⟶ Spec (CommRingCat.of R)) (p₁ : Z ⟶ Y) (p₂ : Z ⟶ Y') (M : LB Y) (M' : LB Y'), IsPullback p₁ p₂ f f' → M.IsLB → M'.IsLB → ∀ (U : Y.Opens) (W : Y'.Opens) (O : Z.Opens) (e₁ : O ≤ p₁ ⁻¹ᵁ U) (e₂ : O ≤ p₂ ⁻¹ᵁ W), IsAffineOpen U → IsAffineOpen W → O = p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ W → ∃ E : SecOnR f M U ⊗[R] SecOnR f' M' W ≃ₗ[R] SecOnR (p₁ ≫ f) (tw (M.pull p₁) (M'.pull p₂) 1) O, ∀ (a : SecOn M U) (b : SecOn M' W) (p : (M.pull p₁).ι) (l : (M'.pull p₂).ι), SecOn.twCoord ((SecOnR.of _ _ O).symm (E (SecOnR.of f M U a ⊗ₜ SecOnR.of f' M' W b))) p l = rs Z (inf_le_inf_left O inf_le_left) (GlobalTheory.LB.coord (SecOn.pullLE M p₁ U O e₁ a) p) * rs Z (inf_le_inf_left O inf_le_right) (GlobalTheory.LB.coord (SecOn.pullLE M' p₂ W O e₂ b) l) := by
  intro R _ Y Y' Z f f' p₁ p₂ M M' H hM hM' U W O e₁ e₂ hU hW e
  have hO : IsAffineOpen O := e ▸ isAffineOpen_inf H hU hW
  letI := cstAlgebra f U
  letI := cstAlgebra f' W
  letI := cstAlgebra (p₁ ≫ f) O
  letI : Algebra Γ(Y, U) Γ(Z, O) := (p₁.appLE U O e₁).hom.toAlgebra
  letI : Algebra Γ(Y', W) Γ(Z, O) := (p₂.appLE W O e₂).hom.toAlgebra
  haveI : IsScalarTower R Γ(Y, U) Γ(Z, O) :=
    .of_algebraMap_eq fun r => (appLE_cst (g := RingHom.id R) (by simp) e₁ r).symm
  haveI : IsScalarTower R Γ(Y', W) Γ(Z, O) :=
    .of_algebraMap_eq fun r => (appLE_cst (g := RingHom.id R) (by simp [H.w]) e₂ r).symm
  haveI : Algebra.IsPushout R Γ(Y', W) Γ(Y, U) Γ(Z, O) :=
    CommRingCat.isPushout_iff_isPushout.mp (isPushout_prod H e₁ e₂ hU hW e)
  letI : Module Γ(Y, U) (SecOn (M.pull p₁) O) := Module.compHom _ (p₁.appLE U O e₁).hom
  haveI : IsScalarTower Γ(Y, U) Γ(Z, O) (SecOn (M.pull p₁) O) :=
    .of_algebraMap_smul fun _ _ => rfl
  letI : Module Γ(Y', W) (SecOn (M'.pull p₂) O) := Module.compHom _ (p₂.appLE W O e₂).hom
  haveI : IsScalarTower Γ(Y', W) Γ(Z, O) (SecOn (M'.pull p₂) O) :=
    .of_algebraMap_smul fun _ _ => rfl
  let j₁ : SecOnR f M U →ₗ[Γ(Y, U)] SecOn (M.pull p₁) O :=
    { toFun := SecOn.pullLE M p₁ U O e₁
      map_add' := (SecOn.pullLE M p₁ U O e₁).map_add
      map_smul' := (SecOn.pullLE M p₁ U O e₁).map_smulₛₗ }
  let j₂ : SecOnR f' M' W →ₗ[Γ(Y', W)] SecOn (M'.pull p₂) O :=
    { toFun := SecOn.pullLE M' p₂ W O e₂
      map_add' := (SecOn.pullLE M' p₂ W O e₂).map_add
      map_smul' := (SecOn.pullLE M' p₂ W O e₂).map_smulₛₗ }
  have h₁ : IsBaseChange Γ(Z, O) j₁ :=
    SecOn.isBaseChange_pullLE hM p₁ hU hO e₁ (fun _ => rfl) j₁ fun _ => rfl
  have h₂ : IsBaseChange Γ(Z, O) j₂ :=
    SecOn.isBaseChange_pullLE hM' p₂ hW hO e₂ (fun _ => rfl) j₂ fun _ => rfl
  obtain ⟨E, hE, hE'⟩ := exists_tensor_addEquiv (R := R) h₁ h₂
  let F := LinearEquiv.ofBijective _
    (secMulHom_bijective (LB.isLB_pull hM p₁) (LB.isLB_pull hM' p₂) hO) ≪≫ₗ
      SecOnR.of (p₁ ≫ f) (tw (M.pull p₁) (M'.pull p₂) 1) O
  refine ⟨{ E.trans F.toAddEquiv with
    map_smul' := fun r z => (congrArg F (hE' r z)).trans (F.map_smul _ _) }, fun a b p l => ?_⟩
  exact congrArg (fun z => SecOn.twCoord (secMulHom _ _ _ z) p l) (hE a b)

end GlobalTheory.AbLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankCechLBHomologyExtProd
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem isAffineOpen_preimage_inf_of_isSeparated {Y Z : Scheme.{0}} [Y.IsSeparated] (p : Z ⟶ Y)
    {U : Y.Opens} (hU : IsAffineOpen U) {V : Z.Opens} (hV : IsAffineOpen V) :
    IsAffineOpen (p ⁻¹ᵁ U ⊓ V) := by
  have : IsAffine V := hV
  have : IsAffineHom ((V.ι ≫ p) ≫ terminal.from Y) := inferInstance
  have : IsAffineHom (V.ι ≫ p) := IsAffineHom.of_comp _ (terminal.from Y)
  have h := (hU.preimage (V.ι ≫ p)).image_of_isOpenImmersion V.ι
  rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_comm] at h

theorem rs_coord_pullLE_restrict {Y Z : Scheme.{0}} {M : LB Y} (p : Z ⟶ Y) {V V' : Y.Opens}
    {O O' B B' : Z.Opens} (h : V' ≤ V) (hO : O' ≤ O) (e : O ≤ p ⁻¹ᵁ V) (e' : O' ≤ p ⁻¹ᵁ V')
    (a : SecOn M V) (j : (M.pull p).ι) (h₁ : B' ≤ O' ⊓ (M.pull p).U j)
    (h₂ : B ≤ O ⊓ (M.pull p).U j) (h₃ : B' ≤ B) :
    rs Z h₁ (GlobalTheory.LB.coord (SecOn.pullLE M p V' O' e' (SecOn.restrict M h a)) j) =
      rs Z h₃ (rs Z h₂ (GlobalTheory.LB.coord (SecOn.pullLE M p V O e a) j)) := by
  rw [SecOn.pullLE_restrict, ← SecOn.restrict_pullLE p e hO, SecOn.coord_restrict, rs_rs, rs_rs]

theorem finrank_cechLB_homology_extProd : ∀ (K : Type) [Field K] (Y Y' Z : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of K)) (f' : Y' ⟶ Spec (CommRingCat.of K)) (p₁ : Z ⟶ Y) (p₂ : Z ⟶ Y') (M : LB Y) (M' : LB Y'), IsPullback p₁ p₂ f f' → M.IsLB → M'.IsLB → IsSeparated f → IsSeparated f' → ∀ (κ₁ : Type) [LinearOrder κ₁] [Fintype κ₁] (U : κ₁ → Y.Opens) (κ₂ : Type) [LinearOrder κ₂] [Fintype κ₂] (W : κ₂ → Y'.Opens) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Z.Opens), (∀ i, IsAffineOpen (U i)) → ⨆ i, U i = ⊤ → (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = ⊤ → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ n, Module.Finite K ((cechLB f M U).homology n)) → (∀ n, Module.Finite K ((cechLB f' M' W).homology n)) → ∀ n, Module.finrank K ((cechLB (p₁ ≫ f) (tw (M.pull p₁) (M'.pull p₂) 1) D).homology n) = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, Module.finrank K ((cechLB f M U).homology x.1) * Module.finrank K ((cechLB f' M' W).homology x.2) := by
  intro K _ Y Y' Z f f' p₁ p₂ M M' H hM hM' hf hf' κ₁ _ _ U κ₂ _ _ W κ _ _ D hU cU hW cW hD cD hA hB n
  have hY : Y.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have hY' : Y'.IsSeparated := ⟨by rw [← terminal.comp_from f']; infer_instance⟩
  have hp₁ : IsSeparated p₁ := MorphismProperty.of_isPullback H.flip hf'
  obtain ⟨e⟩ := cechLB_homology_equiv_trunc₂ K Z (p₁ ≫ f) (tw (M.pull p₁) (M'.pull p₂) 1) κ D
    κ₁ (fun i => p₁ ⁻¹ᵁ U i) κ₂ (fun j => p₂ ⁻¹ᵁ W j)
    (isLB_tw (LB.isLB_pull hM p₁) (LB.isLB_pull hM' p₂) 1) inferInstance hD cD
    (by rw [← Scheme.Hom.preimage_iSup, cU]; rfl) (by rw [← Scheme.Hom.preimage_iSup, cW]; rfl)
    (fun i V hV => isAffineOpen_preimage_inf_of_isSeparated p₁ (hU i) hV)
    (fun j V hV => isAffineOpen_preimage_inf_of_isSeparated p₂ (hW j) hV)
    (fun i j => ExtProd.isAffineOpen_inf H (hU i) (hW j)) n
  rw [e.finrank_eq]
  let E : κ₁ ⊕ₗ κ₂ → Z.Opens := fun u =>
    Sum.elim (fun i => p₁ ⁻¹ᵁ U i) (fun j => p₂ ⁻¹ᵁ W j) (ofLex u)
  have hO (s : Finset κ₁) (t : Finset κ₂) : ⨅ i ∈ Cube.sumVertex s t, E i =
      p₁ ⁻¹ᵁ (⨅ i ∈ s, U i) ⊓ p₂ ⁻¹ᵁ (⨅ j ∈ t, W j) := by
    rw [biInf_sumVertex, preimage_biInf, preimage_biInf]
    rfl
  have hs (s : Finset κ₁) (h : s.Nonempty) : IsAffineOpen (⨅ i ∈ s, U i) :=
    IsAffineOpen.biInf (s : Set κ₁) s.finite_toSet h fun i _ => hU i
  have ht (t : Finset κ₂) (h : t.Nonempty) : IsAffineOpen (⨅ j ∈ t, W j) :=
    IsAffineOpen.biInf (t : Set κ₂) t.finite_toSet h fun j _ => hW j
  choose m hm using fun (s : Finset κ₁) (t : Finset κ₂) (h : s.Nonempty) (h' : t.Nonempty) =>
    exists_secOnR_tensor_equiv K Y Y' Z f f' p₁ p₂ M M' H hM hM' _ _ _
      ((hO s t).le.trans inf_le_left) ((hO s t).le.trans inf_le_right) (hs s h) (ht t h') (hO s t)
  refine (cech_kuenneth_of_bijective (secCube f M U) (secCube f' M' W)
    (secCube (p₁ ≫ f) (tw (M.pull p₁) (M'.pull p₂) 1) E)
    (fun s t h h' => (m s t h h').toLinearMap) (fun s t h h' => (m s t h h').bijective)
    (fun {s s' t t'} h₁ h₂ h h' a b => SecOn.tw_ext fun p l => ?_) hA hB n).2
  have hE := iInf_le_iInf_of_subset E (Cube.sumVertex_mono h h')
  refine (hm s' t' (h₁.mono h) (h₂.mono h') (SecOn.restrict M (iInf_le_iInf_of_subset U h) a)
    (SecOn.restrict M' (iInf_le_iInf_of_subset W h') b) p l).trans
    (Eq.trans ?_ (congrArg (rs Z (inf_le_inf_right _ hE)) (hm s t h₁ h₂ a b p l)).symm)
  rw [map_mul]
  exact congrArg₂ (· * ·) (rs_coord_pullLE_restrict p₁ _ hE _ _ a p _ _ _)
    (rs_coord_pullLE_restrict p₂ _ hE _ _ b l _ _ _)

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankCechLBHomologyExtProdStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
theorem _root_.GlobalTheory.T.finrank_cechLB_homology_extProd_alt : ∀ (K : Type) [Field K] (Y Y' Z : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of K)) (f' : Y' ⟶ Spec (CommRingCat.of K)) (p₁ : Z ⟶ Y) (p₂ : Z ⟶ Y') (M : LB Y) (M' : LB Y'), IsPullback p₁ p₂ f f' → M.IsLB → M'.IsLB → IsSeparated f → IsSeparated f' → ∀ (κ₁ : Type) [LinearOrder κ₁] [Fintype κ₁] (U : κ₁ → Y.Opens) (κ₂ : Type) [LinearOrder κ₂] [Fintype κ₂] (W : κ₂ → Y'.Opens) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Z.Opens), (∀ i, IsAffineOpen (U i)) → ⨆ i, U i = ⊤ → (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = ⊤ → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ n, Module.Finite K ((cechLB f M U).homology n)) → (∀ n, Module.Finite K ((cechLB f' M' W).homology n)) → ∀ n, Module.finrank K ((cechLB (p₁ ≫ f) (tw (M.pull p₁) (M'.pull p₂) 1) D).homology n) = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, Module.finrank K ((cechLB f M U).homology x.1) * Module.finrank K ((cechLB f' M' W).homology x.2) := by
  first | exact @GlobalTheory.AbLaw.finrank_cechLB_homology_extProd | exact GlobalTheory.AbLaw.finrank_cechLB_homology_extProd | (intros; apply GlobalTheory.AbLaw.finrank_cechLB_homology_extProd <;> assumption)
end
