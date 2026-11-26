module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphLieConditionOfDirections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroLiftRealisingKs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandIsotropic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandIsotropic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open IsLocalRing GlobalTheory.AbDual

namespace GlobalTheory.HTLiftIso

theorem liftFil_isotropic : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → ∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ liftFil (divided₂ hsq) m.cart, ∀ y ∈ liftFil (divided₂ hsq) m.cart, φ x y = 0 := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR s s₀ o₀ o m _ _ φ hφ x hx y hy
  let κ := GlobalTheory.Cris.divided₂ hsq
  have hκ : GlobalTheory.Cris.IsNilDP κ := GlobalTheory.Cris.isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C o.A o.ab
  have CS := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl o.ab hg o.ab hg m.cart m.cart
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have CD := cupSquare_of_free ADR.1 hAB (smooth_prod hg hg)
  obtain ⟨φd, hφd⟩ := exists_isCorrForm CD o.isLB o.rig₁ o.rig₂
  obtain ⟨φ₀, hφ₀, e₀⟩ := GlobalTheory.Published.AbelianDualCrystal.exists_crystal_pairing κ m.cart m.cart m.sq.1 m.sq.2
    o.isLB o₀.isLB (LBIso.symm m.pol) hφd
  obtain rfl := hφ.unique CS o₀.isLB hφ₀
  rw [e₀]
  obtain ⟨ψ, hψ, eψ⟩ := hφd.isPolForm
  have iso := (ADR.2.2.2.2 C _ _ hAB (smooth_prod hg hg) o.P o.isLB ψ hψ).1
  have hx' : crysToDR κ m.cart x ∈ Fil o.A := hx
  have hy' : crysToDR κ m.cart y ∈ Fil o.A := hy
  have h := iso _ (push_mem_Fil (inl o.A o.A) hx') _ (push_mem_Fil (inr o.A o.A) hy')
  rw [eψ, push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_push _ _ _ (lift_fst _ _),
    push_push _ _ _ (lift_snd _ _)] at h
  simpa [push_id, push_one] using h

end GlobalTheory.HTLiftIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandIsotropicStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lift_hodge_summand_isotropic : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → ∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ liftFil (divided₂ hsq) m.cart, ∀ y ∈ liftFil (divided₂ hsq) m.cart, φ x y = 0 := by
  first | (exact @GlobalTheory.HTLiftIso.liftFil_isotropic) | (exact GlobalTheory.HTLiftIso.liftFil_isotropic) | (intros; apply GlobalTheory.HTLiftIso.liftFil_isotropic  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphIsotropicOfDirections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphIsotropicOfDirections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTGlueIso

open GlobalTheory.AbDual

variable {k : Type} [Field k]

theorem fil_isotropic_of_isCorrForm (A : Over (Sp k)) [GrpObj A] (hA : IsAbelianScheme A) (P : LB (A ⊗ A).left)
    (hP : P.IsLB) (φ : HdR A →ₗ[k] HdR A →ₗ[k] k) (hφ : IsCorrForm (dp0 k) (𝟙 _) A A P φ) :
    ∀ x ∈ Fil A, ∀ y ∈ Fil A, φ x y = 0 := by
  have H := GlobalTheory.abelianDeRham
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k A hA
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have gAB := smooth_prod hg hg
  obtain ⟨ψ, hψ, e⟩ := hφ.isPolForm
  obtain ⟨iso, -⟩ := H.2.2.2.2 k _ _ hAB gAB P hP ψ hψ
  intro x hx y hy
  have a₁ : push (dp0 k) (𝟙 _) (fst A A) (push (dp0 k) (𝟙 _) (inl A A) x) = x := by
    rw [push_push _ _ _ (lift_fst _ _), push_id]; rfl
  have a₂ : push (dp0 k) (𝟙 _) (snd A A) (push (dp0 k) (𝟙 _) (inl A A) x) = 0 := by
    rw [push_push _ _ _ (lift_snd _ _), push_one]; rfl
  have b₁ : push (dp0 k) (𝟙 _) (fst A A) (push (dp0 k) (𝟙 _) (inr A A) y) = 0 := by
    rw [push_push _ _ _ (lift_fst _ _), push_one]; rfl
  have b₂ : push (dp0 k) (𝟙 _) (snd A A) (push (dp0 k) (𝟙 _) (inr A A) y) = y := by
    rw [push_push _ _ _ (lift_snd _ _), push_id]; rfl
  have key : φ x y = ψ (push (dp0 k) (𝟙 _) (inl A A) x) (push (dp0 k) (𝟙 _) (inr A A) y) := by
    rw [e, a₁, a₂, b₁, b₂]; simp
  rw [key]
  exact iso _ (push_mem_Fil _ hx) _ (push_mem_Fil _ hy)

variable {d : ℕ}

def proj (j : Fin d) : TrivSqZeroExt k (Fin d → k) →+* TrivSqZeroExt k k :=
  (TrivSqZeroExt.map (LinearMap.proj (R := k) (φ := fun _ : Fin d => k) j)).toRingHom

@[simp] theorem fst_proj (j : Fin d) (a : TrivSqZeroExt k (Fin d → k)) : (proj j a).fst = a.fst := by
  simp [proj]

@[simp] theorem snd_proj (j : Fin d) (a : TrivSqZeroExt k (Fin d → k)) : (proj j a).snd = a.snd j := by
  simp [proj]

theorem projMor (A₀ : Over (Sp k)) [GrpObj A₀] (j : Fin d) :
    GrpMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀
      (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀ (proj j) (𝟙 _)
      (Over.Hom.left (𝟙 A₀)) :=
  GrpMor.of_hom (isDPMorphism_sqDP _ _ _ fun a ha => by
      rw [RingHom.mem_ker] at ha ⊢
      change (proj j a).fst = 0
      rw [fst_proj]; exact ha)
    (by
      rw [← GlobalTheory.Cris.spMap_comp]
      congr 1
      ext a <;> simp) (𝟙 A₀)

theorem eq_of_liftSemi_surj' {K C C' : Type} [Field K] [CommRing C] [CommRing C'] [Algebra K C] {M M' M'' : Type*}
    [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module C M'] [AddCommGroup M''] [Module C' M'']
    (P : M →ₛₗ[algebraMap K C] M') (hP : Function.Surjective (liftSemi P)) (σ : C →+* C')
    (Q : M' →ₛₗ[σ] M'') (P' : M → M'') (hQ : ∀ c, Q (P c) = P' c) (x : M' →ₗ[C] C) (x' : M'' →ₗ[C'] C')
    (h : ∀ c, x' (P' c) = σ (x (P c))) (c : M') : x' (Q c) = σ (x c) := by
  obtain ⟨u, rfl⟩ := hP c
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hu, hv]
  | tmul r c =>
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, map_smul, map_smul, hQ, h, smul_eq_mul, smul_eq_mul, map_mul]

theorem projMor_corr (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀) (j : Fin d)
    (x : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (x' : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀)
    (h : ∀ c, x' ((GlobalTheory.FODef.constMorV k k A₀).pull c) = proj j (x ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c))) :
    (projMor A₀ j).Corr x x' :=
  eq_of_liftSemi_surj' _ (GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) A₀ hA (GlobalTheory.FODef.sqZero k (Fin d → k))
    (GlobalTheory.FODef.constMorV k (Fin d → k) A₀)).2 (proj j) (projMor A₀ j).pull _
    (fun c => GrpMor.pull_pull (GlobalTheory.FODef.constMorV k (Fin d → k) A₀) (projMor A₀ j) (GlobalTheory.FODef.constMorV k k A₀)
      (fun r => by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]) (by simp) c) x x' h

theorem exists_red_form (A₀ : Over (Sp k)) [GrpObj A₀] (P : LB (A₀ ⊗ A₀).left) (hP : P.IsLB)
    (φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀ →ₗ[TrivSqZeroExt k (Fin d → k)]
      Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀ →ₗ[TrivSqZeroExt k (Fin d → k)]
        TrivSqZeroExt k (Fin d → k))
    (hφ : IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
      A₀ A₀ P φ) :
    ∃ φ₀ : HdR A₀ →ₗ[k] HdR A₀ →ₗ[k] k, IsCorrForm (dp0 k) (𝟙 _) A₀ A₀ P φ₀ ∧
      ∀ x x' y y', (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀).Corr x x' →
        (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀).Corr y y' →
        φ₀ x' y' = (φ x y).fst :=
  hφ.pull hP (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀)
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀)
    (h := 𝟙 _) ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm) hP (GlobalTheory.lbIso_pull_id hP)

theorem exists_proj_form (A₀ : Over (Sp k)) [GrpObj A₀] (P : LB (A₀ ⊗ A₀).left) (hP : P.IsLB) (j : Fin d)
    (φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀ →ₗ[TrivSqZeroExt k (Fin d → k)]
      Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀ →ₗ[TrivSqZeroExt k (Fin d → k)]
        TrivSqZeroExt k (Fin d → k))
    (hφ : IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
      A₀ A₀ P φ) :
    ∃ φ' : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀ →ₗ[TrivSqZeroExt k k]
        Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀ →ₗ[TrivSqZeroExt k k]
          TrivSqZeroExt k k,
      IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀ A₀ P φ' ∧
      ∀ x x' y y', (projMor A₀ j).Corr x x' → (projMor A₀ j).Corr y y' → φ' x' y' = proj j (φ x y) :=
  hφ.pull hP (projMor A₀ j) (projMor A₀ j) (h := 𝟙 _) ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm) hP (GlobalTheory.lbIso_pull_id hP)

theorem exists_mem_of_fil (A₀ : Over (Sp k)) [GrpObj A₀] (g : HdR A₀ →ₗ[k] HdR A₀)
    (E : Submodule (TrivSqZeroExt k k)
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
    (hE : ∀ x ∈ Fil A₀, ∃ e ∈ E, ∀ c, e ((GlobalTheory.FODef.constMorV k k A₀).pull c) =
      TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (g x c))
    {x z : HdR A₀} (hx : x ∈ Fil A₀) (hz : z ∈ Fil A₀) :
    ∃ e ∈ E, ∀ c, e ((GlobalTheory.FODef.constMorV k k A₀).pull c) =
      TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr ((g x + z) c) := by
  obtain ⟨e₁, h₁, he₁⟩ := hE x hx
  obtain ⟨e₂, h₂, he₂⟩ := hE z hz
  refine ⟨e₁ + (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • e₂, add_mem h₁ (E.smul_mem _ h₂), fun c => ?_⟩
  rw [LinearMap.add_apply, LinearMap.smul_apply, he₁, he₂, smul_eq_mul]
  ext <;> simp

theorem glueFil_isotropic : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ (E' : Fin d → Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A)), (∀ j, ∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A), IsCompl (E' j) M) → (∀ j, ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E' j, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl o₀.A).Corr e y) → (∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c)) → (∀ j (c : D.O), ∀ e ∈ E' j, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (c)) (e)) ∈ E' j) → (∀ j, ∀ φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A →ₗ[TrivSqZeroExt k k] Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A →ₗ[TrivSqZeroExt k k] TrivSqZeroExt k k, GlobalTheory.AbDual.IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A o₀.A o₀.P φ → ∀ x ∈ E' j, ∀ y ∈ E' j, φ x y = 0) → ∀ φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[TrivSqZeroExt k (Fin d → k)] Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[TrivSqZeroExt k (Fin d → k)] TrivSqZeroExt k (Fin d → k), GlobalTheory.AbDual.IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A o₀.A o₀.P φ → ∀ x ∈ GlobalTheory.HTGlue.glueFil o₀.A f, ∀ y ∈ GlobalTheory.HTGlue.glueFil o₀.A f, φ x y = 0 := by
  intro p _ D R _ b N k _ _ tk s o₀ _ d f E' _ _ h3 _ h5 φ hφ x hx y hy
  obtain ⟨x₀, hx₀, zx, hzx, hxc⟩ := hx
  obtain ⟨y₀, hy₀, zy, hzy, hyc⟩ := hy
  have t₀ := exists_red_form (k := k) (d := d) o₀.A o₀.P o₀.isLB φ hφ
  obtain ⟨φ₀, hφ₀, e₀⟩ := t₀
  have hfst : (φ x y).fst = 0 := by
    have cx := GlobalTheory.HTGlue.corr_of_fst o₀.A o₀.ab x x₀ fun c => by rw [hxc c]; simp
    have cy := GlobalTheory.HTGlue.corr_of_fst o₀.A o₀.ab y y₀ fun c => by rw [hyc c]; simp
    rw [← e₀ x x₀ y y₀ cx cy]
    exact fil_isotropic_of_isCorrForm o₀.A o₀.ab o₀.P o₀.isLB φ₀ hφ₀ x₀ hx₀ y₀ hy₀
  have hsnd : ∀ j, (φ x y).snd j = 0 := by
    intro j
    have t₁ := exists_proj_form (k := k) (d := d) o₀.A o₀.P o₀.isLB j φ hφ
    obtain ⟨φ', hφ', e'⟩ := t₁
    have t₂ := exists_mem_of_fil o₀.A (f j) (E' j) (h3 j) hx₀ (hzx j)
    obtain ⟨x', hx', hx'c⟩ := t₂
    have t₃ := exists_mem_of_fil o₀.A (f j) (E' j) (h3 j) hy₀ (hzy j)
    obtain ⟨y', hy', hy'c⟩ := t₃
    have cx := projMor_corr o₀.A o₀.ab j x x' fun c => by
      rw [hx'c c, hxc c]; ext <;> simp
    have cy := projMor_corr o₀.A o₀.ab j y y' fun c => by
      rw [hy'c c, hyc c]; ext <;> simp
    have e := e' x x' y y' cx cy
    have h0 : φ' x' y' = 0 := h5 j φ' hφ' x' hx' y' hy'
    have e2 : proj j (φ x y) = 0 := e.symm.trans h0
    have e3 : (proj j (φ x y)).snd = (0 : TrivSqZeroExt k k).snd := congrArg TrivSqZeroExt.snd e2
    rw [snd_proj] at e3
    exact e3
  exact TrivSqZeroExt.ext hfst (funext hsnd)

end GlobalTheory.HTGlueIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphIsotropicOfDirectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalGluedHodgeGraph_isotropic_of_directions : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ (E' : Fin d → Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A)), (∀ j, ∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A), IsCompl (E' j) M) → (∀ j, ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E' j, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl o₀.A).Corr e y) → (∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c)) → (∀ j (c : D.O), ∀ e ∈ E' j, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (c)) (e)) ∈ E' j) → (∀ j, ∀ φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A →ₗ[TrivSqZeroExt k k] Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A →ₗ[TrivSqZeroExt k k] TrivSqZeroExt k k, GlobalTheory.AbDual.IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A o₀.A o₀.P φ → ∀ x ∈ E' j, ∀ y ∈ E' j, φ x y = 0) → ∀ φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[TrivSqZeroExt k (Fin d → k)] Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[TrivSqZeroExt k (Fin d → k)] TrivSqZeroExt k (Fin d → k), GlobalTheory.AbDual.IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A o₀.A o₀.P φ → ∀ x ∈ GlobalTheory.HTGlue.glueFil o₀.A f, ∀ y ∈ GlobalTheory.HTGlue.glueFil o₀.A f, φ x y = 0 := by
  first | (exact @GlobalTheory.HTGlueIso.glueFil_isotropic) | (exact GlobalTheory.HTGlueIso.glueFil_isotropic) | (intros; apply GlobalTheory.HTGlueIso.glueFil_isotropic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsComplCrystalGluedHodgeGraphFiltration
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsComplCrystalGluedHodgeGraphFiltration
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

theorem exists_isCompl_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R)
    (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)),
    ∃ M : Submodule (TrivSqZeroExt k (Fin d → k))
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A),
      IsCompl (GlobalTheory.HTGlue.glueFil o₀.A f) M := by
  intro p _ D R _ b N k _ _ tk s o₀ _ d f
  obtain ⟨M₀, hM₀⟩ := Submodule.exists_isCompl (Fil o₀.A)
  exact ⟨_, isCompl_glueFil o₀.A o₀.ab f M₀ hM₀⟩

end GlobalTheory.HTGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsComplCrystalGluedHodgeGraphFiltrationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isCompl_crystalGluedHodgeGraphFiltration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∃ M : Submodule (TrivSqZeroExt k (Fin d → k)) (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A), IsCompl (GlobalTheory.HTGlue.glueFil o₀.A f) M := by
  first | (exact @GlobalTheory.HTGlue.exists_isCompl_glueFil) | (exact GlobalTheory.HTGlue.exists_isCompl_glueFil) | (intros; apply GlobalTheory.HTGlue.exists_isCompl_glueFil  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandCrystallineLie
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandCrystallineLie
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

namespace GlobalTheory.HTLiftLie

theorem lie_liftFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → ∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ liftFil (divided₂ hsq) m.cart → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ liftFil (divided₂ hsq) m.cart) ∧ d - ∑ i, w i ∈ liftFil (divided₂ hsq) m.cart := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR s s₀ o₀ o m hs _ d hd
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C o.A o.ab
  have bij : Function.Bijective (crysToDR (divided₂ hsq) m.cart) :=
    GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective GlobalTheory.abelianDeRham.2.2.2.1 o.ab hg (isDPNilpotent_squareZero hsq) hπ rfl
      m.cart
  have key : ∀ (c : D.O) (x : Crys (divided₂ hsq) (spMap π) o₀.A),
      crysToDR (divided₂ hsq) m.cart (haveI := o₀.act.hom c; push (divided₂ hsq) (spMap π) (o₀.act.act c) x) =
        GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act c (crysToDR (divided₂ hsq) m.cart x) := by
    intro c x
    haveI := o₀.act.hom c
    haveI := o.act.hom c
    rw [GlobalTheory.HTSummand.crysAct_apply]
    exact crysToDR_push (divided₂ hsq) m.cart m.cart (o₀.act.act c) (o.act.act c) (m.act c).symm x
  have hy : GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act (algebraMap (𝓞 D.F) D.O D.ω) (crysToDR (divided₂ hsq) m.cart d) -
      tR b.ρ • crysToDR (divided₂ hsq) m.cart d ∈ Fil o.A := by
    have h' := hd
    rw [liftFil, Submodule.mem_comap, map_sub, map_smul, key] at h'
    exact h'
  obtain ⟨w', hw', hsum⟩ := GlobalTheory.HTSummand.lie_mod_fil p D R b N C tR s hs o _ hy
  choose w hw using fun i => bij.2 (w' i)
  refine ⟨w, fun i c => ?_, ?_⟩
  · rw [liftFil, Submodule.mem_comap, map_sub, map_smul, key, hw i]
    exact hw' i c
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [liftFil, Submodule.mem_comap, map_sub, map_sum]
      simp only [hw]
      exact hsum

end GlobalTheory.HTLiftLie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandCrystallineLieStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lift_hodge_summand_crystalline_lie : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → ∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ liftFil (divided₂ hsq) m.cart → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ liftFil (divided₂ hsq) m.cart) ∧ d - ∑ i, w i ∈ liftFil (divided₂ hsq) m.cart := by
  first | (exact @GlobalTheory.HTLiftLie.lie_liftFil) | (exact GlobalTheory.HTLiftLie.lie_liftFil) | (intros; apply GlobalTheory.HTLiftLie.lie_liftFil  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFiltration
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFiltration
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

variable {k : Type} [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]

theorem red_constPull (A₀ : Over (Sp k)) [GrpObj A₀] (c : primDR A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).pull
      ((GlobalTheory.FODef.constMorV k V A₀).pull c) = c :=
  (GrpMor.pull_pull _ _ (homMor (dp0 k) (𝟙 _) (𝟙 A₀))
    (fun r ↦ by simp [TrivSqZeroExt.algebraMap_eq_inl]) (by simp) c).trans
    (Subtype.ext (IsMor.pullCohomologyOne_id _ _))

theorem corr_crysRedMor_iff (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) (y : HdR A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).Corr e y ↔
      ∀ c, y c = TrivSqZeroExt.fst (e ((GlobalTheory.FODef.constMorV k V A₀).pull c)) := by
  constructor
  · intro H c
    have := H ((GlobalTheory.FODef.constMorV k V A₀).pull c)
    rw [red_constPull] at this
    exact this
  · intro H c'
    have hm := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V) (GlobalTheory.FODef.constMorV k V A₀)
    obtain ⟨z, rfl⟩ := hm.2 c'
    induction z with
    | add x x' hx hx' => simp only [map_add (f := _), hx, hx']
    | tmul r c =>
      rw [liftSemi_tmul]
      have h1 := (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).pull.map_smulₛₗ r
        ((GlobalTheory.FODef.constMorV k V A₀).pull c)
      refine (congrArg y h1).trans ?_
      rw [red_constPull, map_smul, H c]
      have h2 := e.map_smul r ((GlobalTheory.FODef.constMorV k V A₀).pull c)
      rw [h2]
      exact (TrivSqZeroExt.fst_mul r _).symm

theorem mem_fil_iff_exists_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ GlobalTheory.HTGlue.glueFil o₀.A f, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl o₀.A).Corr e y := by
  intro p _ D R _ b N k _ _ tk s o₀ _ d f y
  constructor
  · intro hy
    obtain ⟨e, he, hc⟩ := exists_mem_glueFil o₀.A o₀.ab f hy
    refine ⟨e, he, (corr_crysRedMor_iff (Fin d → k) o₀.A o₀.ab e y).2 fun c ↦ ?_⟩
    rw [hc c]
    simp
  · rintro ⟨e, ⟨x, hx, z, -, he⟩, hc⟩
    have hxy : y = x := LinearMap.ext fun c ↦ by
      rw [(corr_crysRedMor_iff (Fin d → k) o₀.A o₀.ab e y).1 hc c, he c]
      simp
    exact hxy ▸ hx

end GlobalTheory.HTGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFiltrationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_hodgeFiltration_iff_reduction_gluedFiltration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ GlobalTheory.HTGlue.glueFil o₀.A f, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl o₀.A).Corr e y := by
  first | (exact @GlobalTheory.HTGlue.mem_fil_iff_exists_glueFil) | (exact GlobalTheory.HTGlue.mem_fil_iff_exists_glueFil) | (intros; apply GlobalTheory.HTGlue.mem_fil_iff_exists_glueFil  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandAdmissibleStable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandAdmissibleStable
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTDeform


open GlobalTheory.Published.GrothendieckMessing in
theorem liftFil_isCompl_red_stable : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl (liftFil (divided₂ hsq) m.cart) M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ liftFil (divided₂ hsq) m.cart, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ liftFil (divided₂ hsq) m.cart, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ liftFil (divided₂ hsq) m.cart) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR s s₀ o₀ o m _ _
  have HC := canonical_of_abelianDeRham GlobalTheory.T.abelianScheme_firstDeRham_structure (isDPNilpotent_squareZero hsq) hπ rfl
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C o.A o.ab
  obtain ⟨bij, ⟨M, hM⟩, hAdm⟩ := HC g o₀.A o.A m.φ m.cart o.ab hg
  have bijD := HC.crysToDR_bijective m.cart o.ab hg
  let e := LinearEquiv.ofBijective (crysToDR (divided₂ hsq) m.cart) bijD
  refine ⟨⟨M.comap (crysToDR (divided₂ hsq) m.cart), (Submodule.orderIsoMapComap e).symm.isCompl hM⟩,
    fun y ↦ ?_, fun c d hd ↦ ?_⟩
  · rw [hAdm y]
    constructor
    · rintro ⟨x, hx, ex⟩
      obtain ⟨d, rfl⟩ := bijD.2 x
      exact ⟨d, hx, (corr_crysToDR_iff rfl m.cart bij.2 d y).1 ex⟩
    · rintro ⟨d, hd, ed⟩
      exact ⟨_, hd, (corr_crysToDR_iff rfl m.cart bij.2 d y).2 ed⟩
  · haveI := o₀.act.hom c
    haveI := o.act.hom c
    exact push_mem_liftFil (divided₂ hsq) m.cart m.cart (o₀.act.act c) (o.act.act c) (m.act c).symm hd

end GlobalTheory.HTDeform
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandAdmissibleStableStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lift_hodge_summand_admissible_stable : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl (liftFil (divided₂ hsq) m.cart) M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ liftFil (divided₂ hsq) m.cart, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ liftFil (divided₂ hsq) m.cart, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ liftFil (divided₂ hsq) m.cart) := by
  first | (exact @GlobalTheory.HTDeform.liftFil_isCompl_red_stable) | (exact GlobalTheory.HTDeform.liftFil_isCompl_red_stable) | (intros; apply GlobalTheory.HTDeform.liftFil_isCompl_red_stable  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphOrderStableOfDirections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphOrderStableOfDirections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlueOStab

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]

theorem coord_ext (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    {e e' : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀}
    (h : ∀ c, e ((GlobalTheory.FODef.constMorV k V A₀).pull c) = e' ((GlobalTheory.FODef.constMorV k V A₀).pull c)) :
    e = e' := by
  refine LinearMap.ext fun c' => ?_
  obtain ⟨u, rfl⟩ := (GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V)
    (GlobalTheory.FODef.constMorV k V A₀)).2 c'
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | tmul r c => rw [liftSemi_tmul, map_smul, map_smul, h]

theorem push_coord (A₀ : Over (Sp k)) [GrpObj A₀] (f : A₀ ⟶ A₀) [IsMonHom f]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀)
    (c : primDR A₀) :
    push (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) f e
        ((GlobalTheory.FODef.constMorV k V A₀).pull c) =
      e ((GlobalTheory.FODef.constMorV k V A₀).pull (primPull (dp0 k) (𝟙 _) f c)) := by
  rw [push_apply]
  congr 1
  have m : GrpMor (dp0 k) (𝟙 _) A₀ (divided₂ (GlobalTheory.FODef.sqZero k V))
      (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀
      (algebraMap k (TrivSqZeroExt k V)) (𝟙 _) f.left :=
    ⟨(GlobalTheory.FODef.constMorV k V A₀).dp, (GlobalTheory.FODef.constMorV k V A₀).base,
      (homMor (dp0 k) (𝟙 _) f).w, (homMor (dp0 k) (𝟙 _) f).mul⟩
  exact (GrpMor.pull_pull (GlobalTheory.FODef.constMorV k V A₀) (homMor _ _ f) m (fun _ => rfl) (by simp) c).trans
    (GrpMor.pull_pull (homMor (dp0 k) (𝟙 _) f) (GlobalTheory.FODef.constMorV k V A₀) m (fun _ => rfl) rfl c).symm

theorem red_pull (A₀ : Over (Sp k)) [GrpObj A₀] (c : prim (dp0 k) (𝟙 _) A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).pull
      ((GlobalTheory.FODef.constMorV k V A₀).pull c) = c := by
  rw [GrpMor.pull_pull _ _ (homMor (dp0 k) (𝟙 _) (𝟙 A₀)) (fun r => rfl) (by simp)]
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)

theorem eq_of_surj {K C : Type} [Field K] [CommRing C] [Algebra K C] {M M' : Type*} [AddCommGroup M]
    [Module K M] [AddCommGroup M'] [Module C M'] (P : M →ₛₗ[algebraMap K C] M')
    (hP : Function.Surjective (liftSemi P)) (π : C →+* K)
    (Q : M' →ₛₗ[π] M) (e : M' →ₗ[C] C) (y : M →ₗ[K] K) (hQ : ∀ c, Q (P c) = c)
    (he : ∀ c, π (e (P c)) = y c) (c' : M') : y (Q c') = π (e c') := by
  obtain ⟨u, rfl⟩ := hP c'
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hu, hv]
  | tmul r c =>
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, hQ, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul, he]

theorem corr_of_fst (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀)
    (y : HdR A₀) (hc : ∀ c, (TrivSqZeroExt.fstHom k k V).toRingHom
      (e ((GlobalTheory.FODef.constMorV k V A₀).pull c)) = y c) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).Corr e y :=
  eq_of_surj _ (GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V)
    (GlobalTheory.FODef.constMorV k V A₀)).2 _ _ e y (red_pull A₀) hc

theorem eps_smul_eq {k : Type} [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀) (y : HdR A₀)
    (w e₃ : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀)
    (hw : ∀ c, w ((GlobalTheory.FODef.constMorV k k A₀).pull c) = (Algebra.linearMap k (TrivSqZeroExt k k) ∘ₗ y) c)
    (hy : ∀ c, e₃ ((GlobalTheory.FODef.constMorV k k A₀).pull c) = TrivSqZeroExt.inr (y c)) :
    (TrivSqZeroExt.inr 1 : TrivSqZeroExt k k) • w = e₃ := by
  refine coord_ext A₀ hA fun c => ?_
  have e1 : ((TrivSqZeroExt.inr 1 : TrivSqZeroExt k k) • w) ((GlobalTheory.FODef.constMorV k k A₀).pull c) =
      (TrivSqZeroExt.inr 1 : TrivSqZeroExt k k) * (w ((GlobalTheory.FODef.constMorV k k A₀).pull c)) := rfl
  rw [e1, hw c, hy c]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_smul_eq_of_isCompl {C X : Type*} [CommRing C] [AddCommGroup X] [Module C X] {E M : Submodule C X}
    (hEM : IsCompl E M) (ε : C) {w e₃ : X} (h1 : ε • w = e₃) (he₃ : e₃ ∈ E) : ∃ a ∈ E, ε • a = e₃ := by
  have hw : w ∈ E ⊔ M := by rw [hEM.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, m, hm, rfl⟩ := Submodule.mem_sup.1 hw
  have h4 : ε • m = e₃ - ε • a := by rw [← h1, smul_add]; abel
  have hmE : ε • m ∈ E := h4 ▸ E.sub_mem he₃ (E.smul_mem ε ha)
  have h2 : ε • m = 0 := (Submodule.disjoint_def.1 hEM.disjoint) _ hmE (M.smul_mem ε hm)
  exact ⟨a, ha, by rw [← h1, smul_add, h2, add_zero]⟩

theorem fil_of_eps (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (E M : Submodule (TrivSqZeroExt k k)
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
    (hEM : IsCompl E M)
    (hred : ∀ y : HdR A₀, y ∈ Fil A₀ ↔
      ∃ e ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl A₀).Corr e y)
    {e₃ : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀}
    (he₃ : e₃ ∈ E) (y : HdR A₀)
    (hy : ∀ c, e₃ ((GlobalTheory.FODef.constMorV k k A₀).pull c) = TrivSqZeroExt.inr (y c)) : y ∈ Fil A₀ := by
  obtain ⟨w, hw⟩ := GlobalTheory.HTGlue.exists_coords k A₀ hA (Algebra.linearMap k (TrivSqZeroExt k k) ∘ₗ y)
  obtain ⟨a, ha, h1⟩ := exists_smul_eq_of_isCompl hEM _ (eps_smul_eq A₀ hA y w e₃ hw hy) he₃
  refine (hred y).2 ⟨a, ha, corr_of_fst A₀ hA a y fun c => ?_⟩
  have h3 := congrArg (fun u => (u ((GlobalTheory.FODef.constMorV k k A₀).pull c)).snd) h1
  have e1 : ((TrivSqZeroExt.inr 1 : TrivSqZeroExt k k) • a) ((GlobalTheory.FODef.constMorV k k A₀).pull c) =
      (TrivSqZeroExt.inr 1 : TrivSqZeroExt k k) * (a ((GlobalTheory.FODef.constMorV k k A₀).pull c)) := rfl
  simp only [e1, hy c] at h3
  simpa using h3

theorem glueFil_stable : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ (E' : Fin d → Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A)), (∀ j, ∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A), IsCompl (E' j) M) → (∀ j, ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E' j, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl o₀.A).Corr e y) → (∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c)) → (∀ j (c : D.O), ∀ e ∈ E' j, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (c)) (e)) ∈ E' j) → ∀ (c : D.O), ∀ e ∈ GlobalTheory.HTGlue.glueFil o₀.A f, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (c)) (e)) ∈ GlobalTheory.HTGlue.glueFil o₀.A f := by
  intro p _ D R _ b N k _ _ tk s o₀ _ d f E' hcompl hred hlift hstab c e he
  obtain ⟨x, hx, z, hz, hze⟩ := he
  haveI := o₀.act.hom c
  have key : ∀ j, ∀ x ∈ Fil o₀.A, push (dp0 k) (𝟙 _) (o₀.act.act c) (f j x) -
      f j (push (dp0 k) (𝟙 _) (o₀.act.act c) x) ∈ Fil o₀.A := by
    intro j x hx
    obtain ⟨M, hM⟩ := hcompl j
    obtain ⟨e1, he1, hc1⟩ := hlift j x hx
    obtain ⟨e2, he2, hc2⟩ := hlift j _ (push_mem_Fil (o₀.act.act c) hx)
    refine fil_of_eps o₀.A o₀.ab (E' j) M hM (hred j) (sub_mem (hstab j c e1 he1) he2) _ fun c' => ?_
    rw [LinearMap.sub_apply, push_coord, hc1, hc2]
    ext <;> simp [push_apply]
  refine ⟨_, push_mem_Fil (o₀.act.act c) hx, fun j => push (dp0 k) (𝟙 _) (o₀.act.act c) (f j x) -
      f j (push (dp0 k) (𝟙 _) (o₀.act.act c) x) + push (dp0 k) (𝟙 _) (o₀.act.act c) (z j),
    fun j => add_mem (key j x hx) (push_mem_Fil _ (hz j)), fun c' => ?_⟩
  rw [push_coord, hze]
  ext
  · simp [push_apply]
  · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, Pi.add_apply,
      LinearMap.add_apply, LinearMap.sub_apply, push_apply]
    ring

end GlobalTheory.HTGlueOStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphOrderStableOfDirectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalGluedHodgeGraph_order_stable_of_directions : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ (E' : Fin d → Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A)), (∀ j, ∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A), IsCompl (E' j) M) → (∀ j, ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E' j, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl o₀.A).Corr e y) → (∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c)) → (∀ j (c : D.O), ∀ e ∈ E' j, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (c)) (e)) ∈ E' j) → ∀ (c : D.O), ∀ e ∈ GlobalTheory.HTGlue.glueFil o₀.A f, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (c)) (e)) ∈ GlobalTheory.HTGlue.glueFil o₀.A f := by
  first | (exact @GlobalTheory.HTGlueOStab.glueFil_stable) | (exact GlobalTheory.HTGlueOStab.glueFil_stable) | (intros; apply GlobalTheory.HTGlueOStab.glueFil_stable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsGluedFirstOrderDeformation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem GlobalTheory.HTGlue.isFilLift_coords {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] {A' : Over (Sp (DualNumber k))}
    [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i)
    {x y : HdR A} (hx : IsFilLift h x y) :
    ∃ e ∈ liftFil (divided₂ (GlobalTheory.FODef.sqZero k k)) h,
      ∀ c, e ((GlobalTheory.FODef.constMorV k k A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (y c) := hx

theorem GlobalTheory.HTGlue.exists_obj_of_summand (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (hNp : N.Coprime p) (C C₀ : Type) [CommRing C] [IsLocalRing C]
    [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀) (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0)
    (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)) (E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A))
    (hEc : ∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M)
    (hEf : ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y)
    (hEs : ∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E)
    (hEi : ∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C,
      GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ E, ∀ y ∈ E, φ x y = 0)
    (hEl : ∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω);
      push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ E →
      ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c);
        push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧
        d - ∑ i, w i ∈ E)
    (s : Sp C ⟶ Sp R) (hs : s = spMap tR) :
    ∃ (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), liftFil (divided₂ hsq) m.cart = E := by
  subst hs
  obtain ⟨A, _, i, h, act, hA, hE, hact⟩ := GlobalTheory.T.harrisTaylor_exists_lift_orderAction_hodge_summand p D R b N C C₀ π hπ hsq tR o₀ E hEc hEf hEs
  haveI : IsCommMonObj A := hA.comm
  subst hE
  obtain ⟨P, φ₂, hP, r1, r2, hsym, hamp, hker, hros, hsq2, hpol⟩ :=
    GlobalTheory.T.harrisTaylor_exists_polarisation_bundle_lift p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEi
  obtain ⟨eta, e1, e2, e3, e4, e5⟩ :=
    GlobalTheory.T.harrisTaylor_primeToP_level_lift_squareZero p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hNp P φ₂ hP hsq2 hpol
  exact ⟨{ A := A
           ab := hA
           act := act
           P := P
           isLB := hP
           rig₁ := r1
           rig₂ := r2
           symm := hsym
           ample := hamp
           kerP := hker
           rosati := hros
           lie := fun R' _ β x hx v hv => GlobalTheory.T.harrisTaylor_lift_lie_of_hodge_summand_lie p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEl R' β x hx v hv
           lieRank := fun k _ _ x β hx j => GlobalTheory.T.harrisTaylor_lieMultiplicity_squareZeroLift p D R b N C C₀ π hπ hsq tR o₀ A i h act hact k x β hx j
           eta := eta
           eta_add := e1
           eta_lin := e2
           eta_ker := e3
           geom := e4 },
    { φ := i
      φ₂ := φ₂
      cart := h
      sq := hsq2
      act := hact
      pol := hpol
      eta := e5 }, rfl⟩

theorem GlobalTheory.HTGlue.isFilLiftV_of_eq {k : Type} [Field k] {d : ℕ} {A₀ : Over (Sp k)} [GrpObj A₀] (hA : IsAbelianScheme A₀)
    {A : Over (Sp (TrivSqZeroExt k (Fin d → k)))} [GrpObj A] {i : A₀.left ⟶ A.left}
    (h : IsGrpPullback A₀ A (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) i)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀))
    (hh : liftFil (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) h = GlobalTheory.HTGlue.glueFil A₀ f) {x : HdR A₀}
    (hx : x ∈ Fil A₀) : GlobalTheory.FODef.IsFilLiftV h x (LinearMap.pi fun j => f j x) := by
  obtain ⟨e, he, hc⟩ := GlobalTheory.HTGlue.exists_mem_glueFil A₀ hA f hx
  exact ⟨e, hh ▸ he, hc⟩


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.HTGlue.exists_glue : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f j x)) → ∃ (o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t)) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)), ∀ x ∈ Fil o₀.A, GlobalTheory.FODef.IsFilLiftV m.cart x (LinearMap.pi fun j => f j x) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ d f hdef
  rcases Nat.eq_zero_or_pos d with rfl | hd
  ·

    obtain ⟨tk, ht⟩ : ∃ tk : R →+* k, t = spMap tk := ⟨(Spec.preimage t).hom, by simp [spMap]⟩
    obtain ⟨φ, hφ⟩ := GlobalTheory.UPel.HT.CorrForm.exists_isCorrForm_obj p D R b N hN hNp k t o₀
    exact GlobalTheory.UPel.HT.exists_sqZero_lift_realising_ks p D R b N hN hNp k t o₀ tk ht φ hφ 0 f (fun j => j.elim0)
  haveI : IsArtinianRing (TrivSqZeroExt k (Fin d → k)) := GlobalTheory.HTGlue.isArtinianRing_tsze k d
  haveI : Module.Finite k (DualNumber k) :=
    Module.Finite.of_surjective ((Algebra.linearMap k (DualNumber k)).coprod (TrivSqZeroExt.inrHom k k))
      (fun x => ⟨(x.fst, x.snd), by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]⟩)
  haveI : IsArtinianRing (DualNumber k) := IsArtinianRing.of_finite k _
  obtain ⟨tk, ht⟩ : ∃ tk : R →+* k, t = spMap tk := ⟨(Spec.preimage t).hom, by simp [spMap]⟩
  set tR : R →+* TrivSqZeroExt k (Fin d → k) := (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp tk with htR
  have hs : t = spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
    all_goals (congr 1 <;> ext x <;> simp [tR])
  subst hs
  choose o' m' hm' using hdef
  have hsε : spMap (algebraMap k (DualNumber k)) ≫
      (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR) =
      spMap ((algebraMap k (TrivSqZeroExt k k)).comp tk) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
  have hs₀ : spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap ((algebraMap k (TrivSqZeroExt k k)).comp tk) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
    all_goals (congr 1 <;> ext x <;> simp)
  have hsurε : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, by simp⟩
  have n1 := fun j => GlobalTheory.T.harrisTaylor_lift_hodge_summand_admissible_stable p D R b N (DualNumber k) k (TrivSqZeroExt.fstHom k k k).toRingHom hsurε (GlobalTheory.FODef.sqZero k k) ((algebraMap k (TrivSqZeroExt k k)).comp tk) (spMap (algebraMap k (DualNumber k)) ≫ (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR)) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR) o₀ (o' j) (m' j) hsε hs₀
  have n2 := fun j => GlobalTheory.T.harrisTaylor_lift_hodge_summand_isotropic p D R b N (DualNumber k) k (TrivSqZeroExt.fstHom k k k).toRingHom hsurε (GlobalTheory.FODef.sqZero k k) ((algebraMap k (TrivSqZeroExt k k)).comp tk) (spMap (algebraMap k (DualNumber k)) ≫ (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR)) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR) o₀ (o' j) (m' j) hsε hs₀
  have n3 := fun j => GlobalTheory.T.harrisTaylor_lift_hodge_summand_crystalline_lie p D R b N (DualNumber k) k (TrivSqZeroExt.fstHom k k k).toRingHom hsurε (GlobalTheory.FODef.sqZero k k) ((algebraMap k (TrivSqZeroExt k k)).comp tk) (spMap (algebraMap k (DualNumber k)) ≫ (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR)) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR) o₀ (o' j) (m' j) hsε hs₀
  have hmem : ∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ liftFil (divided₂ (GlobalTheory.FODef.sqZero k k)) (m' j).cart,
      ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c) :=
    fun j x hx => GlobalTheory.HTGlue.isFilLift_coords (m' j).cart (hm' j x hx)
  have hab := o₀.ab
  have htk : spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR = spMap tk := ht
  have g1 := GlobalTheory.T.exists_isCompl_crystalGluedHodgeGraphFiltration p D R b N k tk _ o₀ htk d f
  have g2 := GlobalTheory.T.mem_hodgeFiltration_iff_reduction_gluedFiltration p D R b N k tk _ o₀ htk d f
  have g3 := GlobalTheory.T.crystalGluedHodgeGraph_order_stable_of_directions p D R b N k tk _ o₀ htk d f _ (fun j => (n1 j).1) (fun j => (n1 j).2.1) hmem (fun j => (n1 j).2.2)
  have g4 := GlobalTheory.T.crystalGluedHodgeGraph_isotropic_of_directions p D R b N k tk _ o₀ htk d f _ (fun j => (n1 j).1) (fun j => (n1 j).2.1) hmem (fun j => (n1 j).2.2) n2
  have g5 := GlobalTheory.T.crystalGluedHodgeGraph_lie_condition_of_directions p D R b N k tk _ o₀ htk d hd f _ (fun j => (n1 j).1) (fun j => (n1 j).2.1) hmem (fun j => (n1 j).2.2) n3
  have hsurC : Function.Surjective (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, by simp⟩
  have hst : spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫
      (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR) = spMap tR := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
  obtain ⟨o, m, hm⟩ := GlobalTheory.HTGlue.exists_obj_of_summand p D R b N hNp _ k _ hsurC (GlobalTheory.FODef.sqZero k (Fin d → k))
    tR o₀ (GlobalTheory.HTGlue.glueFil o₀.A f) g1 g2 g3 g4 g5 _ hst
  exact ⟨o, m, fun x hx => GlobalTheory.HTGlue.isFilLiftV_of_eq hab m.cart f hm hx⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsGluedFirstOrderDeformationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
theorem _root_.GlobalTheory.T.harrisTaylor_exists_glued_firstOrder_deformation : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f j x)) → ∃ (o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t)) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)), ∀ x ∈ Fil o₀.A, GlobalTheory.FODef.IsFilLiftV m.cart x (LinearMap.pi fun j => f j x) := by
  first | exact @GlobalTheory.HTGlue.exists_glue | exact GlobalTheory.HTGlue.exists_glue | exact @GlobalTheory.HTGlue.isFilLiftV_of_eq | exact GlobalTheory.HTGlue.isFilLiftV_of_eq | exact @GlobalTheory.HTGlue.exists_obj_of_summand | exact GlobalTheory.HTGlue.exists_obj_of_summand
end
