module

public import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.PerfectRing
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CrystallineDeRham
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.AbelianDeRhamPage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AbelianDeRhamStructure.AbelianDeRhamPages.AbelianDeRhamStructureOfPage
namespace AbelianDeRhamStructureFromPages.Adrs

theorem abelianDeRhamStructure_of_page (P : FubiniStudyChowHeightFormula₂.Hdr.AbelianDeRhamPage) : GlobalTheory.Published.AbelianDeRhamStructure :=
  let hL := GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations
  let hH := FubiniStudyChowHeightFormula₂.Hdr.abelianHodgeDeRham_of_page P
  ⟨GlobalTheory.Proof.abelianDeRhamFree_of_hodge hL hH,
    GlobalTheory.T.abelian_hodge_de_rham_of_crystalline_lift hL hH,
    GlobalTheory.AbelianBaseChange.abelianDeRham_baseChange_of_smoothLift hL hH⟩

end AbelianDeRhamStructureFromPages.Adrs
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.PoincareDeRhamDualityOfCube
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RestrictTrivEqZero
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoefRestrictSmallCoverInjective
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoefRestrictSmallCoverInjective
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivSmall

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem isTriv_loc (s : X ⟶ Sp R) (T : (IsTriv s).FullSubcategory) (b : T.obj.B) :
    IsTriv s (ThickLoc.loc T.obj b) := by
  change Ideal.map _ T.obj.J = ⊥
  rw [show T.obj.J = ⊥ from T.property, Ideal.map_bot]

theorem hasLoc (s : X ⟶ Sp R) : Desc.HasLoc ((IsTriv s).ι ⋙ O (dp0 R) s) := by
  intro T b
  let b' : T.obj.B := b
  refine ⟨⟨ThickLoc.loc T.obj b', isTriv_loc s T b'⟩, ObjectProperty.homMk (ThickLoc.toLoc T.obj b'),
    IsLocalization.Away.algebraMap_isUnit (S := Localization.Away b') b',
    fun y ↦ IsLocalization.Away.surj (S := Localization.Away b') b' y, fun x hx ↦ ?_,
    fun S u hu ↦ ⟨ObjectProperty.homMk (ThickLoc.lift u.hom hu), ?_, fun v hv ↦ ?_⟩⟩
  · obtain ⟨⟨_, n, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers b') (Localization.Away b') x).1 hx
    exact ⟨n, hm⟩
  · exact ObjectProperty.hom_ext _ (Thick.Hom.ext' (AlgHom.ext (ThickLoc.liftφ_algebraMap u.hom hu)))
  · have hv' : ∀ x : T.obj.B, v.hom.φ (algebraMap T.obj.B (Localization.Away b') x) = u.hom.φ x :=
      fun x ↦ by rw [← hv]; rfl
    have : (v.hom.φ : Localization.Away b' →+* S.obj.B) =
        (ThickLoc.liftφ u.hom hu : Localization.Away b' →+* S.obj.B) := by
      refine IsLocalization.ringHom_ext (Submonoid.powers b') (RingHom.ext fun x ↦ ?_)
      exact (hv' x).trans (ThickLoc.liftφ_algebraMap u.hom hu x).symm
    exact ObjectProperty.hom_ext _ (Thick.Hom.ext' (AlgHom.ext fun x ↦ RingHom.congr_fun this x))

theorem pull_restrict_small_injective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (K : Type) (U : K → X.Opens), ⨆ i, U i = ⊤ → Function.Injective (CoefMap.restrict ((IsTriv s).ι ⋙ O (dp0 R) s) (ObjectProperty.ι (fun T : (IsTriv s).FullSubcategory => IsSmall (dp0 R) s U T.obj))).pull2 := by
  intro R _ X s K U hU
  exact (Desc.pull2_bijective _ (hasLoc s) _ (fun _ _ φ h ↦ h.imp fun _ ↦ φ.hom.le_preimage)
    fun T ↦ by
      obtain ⟨n, b, hb, h⟩ := exists_finite_small_cover R ⊥ (dp0 R) X s K U hU T.obj
      exact ⟨n, b, hb, fun i S u hu ↦ h i S.obj u.hom hu⟩).1

end GlobalTheory.CompanionTheory.TrivSmall
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoefRestrictSmallCoverInjectiveStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coef_restrict_small_cover_injective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (K : Type) (U : K → X.Opens), ⨆ i, U i = ⊤ → Function.Injective (CoefMap.restrict ((IsTriv s).ι ⋙ O (dp0 R) s) (ObjectProperty.ι (fun T : (IsTriv s).FullSubcategory => IsSmall (dp0 R) s U T.obj))).pull2 := by
  first | exact @GlobalTheory.CompanionTheory.TrivSmall.pull_restrict_small_injective | exact GlobalTheory.CompanionTheory.TrivSmall.pull_restrict_small_injective | (intros; apply GlobalTheory.CompanionTheory.TrivSmall.pull_restrict_small_injective <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.PdChern

theorem restrict_triv_eq_zero : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ z : SecondDeRham s, IsChern (dp0 R) s L z → (CoefMap.restrict (O (dp0 R) s) (IsTriv s).ι).pull2 z = 0 := by
  intro R _ X s L hL z hz
  obtain ⟨i, hi, u, ℓ, -, hℓ, hz⟩ := hz
  obtain ⟨c, rfl⟩ := H2.mk_surjective _ z
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hz
  obtain ⟨f, hf⟩ := hz
  apply GlobalTheory.T.coef_restrict_small_cover_injective R X s L.ι L.U hL.cover
  rw [map_zero, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero]
  let P : ObjectProperty (IsTriv s).FullSubcategory :=
    fun T : (IsTriv s).FullSubcategory => IsSmall (dp0 R) s L.U T.obj
  let F : P.FullSubcategory ⥤ (IsSmall (dp0 R) s L.U).FullSubcategory :=
    ObjectProperty.lift _ (P.ι ⋙ (IsTriv s).ι) (fun T => T.property)
  refine ⟨fun T T' φ => f (F.obj T) (F.obj T') (F.map φ), ?_⟩
  funext T T' T'' φ ψ
  have h := congrFun (congrFun (congrFun (congrFun (congrFun hf (F.obj T)) (F.obj T'))
    (F.obj T'')) (F.map φ)) (F.map ψ)
  have h0 : (ℓ.1 (F.obj T) (F.obj T') (F.obj T'') (F.map φ) (F.map ψ) : T''.obj.obj.B) = 0 := by
    have hm : (ℓ.1 (F.obj T) (F.obj T') (F.obj T'') (F.map φ) (F.map ψ) : T''.obj.obj.B) ∈
      T''.obj.obj.J := (hℓ (F.obj T) (F.obj T') (F.obj T'') (F.map φ) (F.map ψ)).1
    have e : T''.obj.obj.J = ⊥ := T''.obj.property
    rw [e] at hm
    exact Ideal.mem_bot.1 hm
  exact h.trans (sub_eq_self.2 h0)

end GlobalTheory.CompanionTheory.PdChern
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.H1OnPointsEqZeroOfIsIso
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}

theorem hom_ext' {s : X ⟶ Sp R} {P Q : Pt s} {φ ψ : P.Hom Q} (h : ∀ b, φ.ρ b = ψ.ρ b) : φ = ψ := by
  obtain ⟨ρ, e⟩ := φ
  obtain ⟨ρ', e'⟩ := ψ
  obtain rfl : ρ = ρ' := AlgHom.ext h
  rfl

instance ptCat (s : X ⟶ Sp R) : Category.{0} (Pt s) where
  Hom := Pt.Hom
  id := Pt.Hom.id
  comp := Pt.Hom.comp
  id_comp _ := hom_ext' fun _ ↦ rfl
  comp_id _ := hom_ext' fun _ ↦ rfl
  assoc _ _ _ := hom_ext' fun _ ↦ rfl

@[reducible] def FP (s : X ⟶ Sp R) : Pt s ⥤ CommAlgCat.{0} R where
  obj P := CommAlgCat.of R P.B
  map φ := CommAlgCat.ofHom φ.ρ

def toPC (s : X ⟶ Sp R) : CoefMap (RingHom.id R) (O (dp0 R) s) (FP s) where
  G := { obj := fun P ↦ P.triv
         map := fun φ ↦ Pt.Hom.triv φ
         map_id := fun _ ↦ Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl)
         map_comp := fun _ _ ↦ Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl) }
  α P := RingHom.id P.B
  naturality _ _ := rfl
  smul _ _ _ := rfl

abbrev H1OnPoints (s : X ⟶ Sp R) : Type 1 := GlobalTheory.CatCoh.H1 (FP s)

def toP (s : X ⟶ Sp R) : FirstDeRham s →ₗ[R] H1OnPoints s := (toPC s).pull1

variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {φ : X' ⟶ X}

@[reducible] def pushPt (h : φ ≫ s = s' ≫ spMap σ) (P : Pt s') : Pt s where
  B := P.B
  alg := ((algebraMap R' P.B).comp σ).toAlgebra
  x := P.x ≫ φ
  w := by rw [Category.assoc, h, ← Category.assoc, P.w, ← GlobalTheory.Cris.spMap_comp]

def pushHom (h : φ ≫ s = s' ≫ spMap σ) {P Q : Pt s'} (f : P ⟶ Q) : pushPt h P ⟶ pushPt h Q where
  ρ := { (f.ρ : P.B →+* Q.B) with commutes' := fun r ↦ f.ρ.commutes (σ r) }
  pt := by
    change spMap (f.ρ : P.B →+* Q.B) ≫ P.x ≫ φ = Q.x ≫ φ
    rw [← Category.assoc, f.pt]

def pushC (h : φ ≫ s = s' ≫ spMap σ) : CoefMap σ (FP s) (FP s') where
  G := { obj := pushPt h
         map := pushHom h
         map_id := fun _ ↦ hom_ext' fun _ ↦ rfl
         map_comp := fun _ _ ↦ hom_ext' fun _ ↦ rfl }
  α P := RingHom.id P.B
  naturality _ _ := rfl
  smul T r b := (Algebra.smul_def (A := T.B) (σ r) b).symm

def pullP (h : φ ≫ s = s' ≫ spMap σ) : H1OnPoints s →ₛₗ[σ] H1OnPoints s' := (pushC h).pull1

theorem pullP_toP (m : IsMor (dp0 R) s (dp0 R') s' σ φ) (c : FirstDeRham s) :
    pullP m.w (toP s c) = toP s' (m.pull1 c) := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rfl

theorem pullP_pullP {τ : R' →+* R''} {ψ : X'' ⟶ X'} {ρ : R →+* R''} {χ : X'' ⟶ X}
    (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ) (h'' : χ ≫ s = s'' ≫ spMap ρ)
    (e : ∀ r, τ (σ r) = ρ r) (e' : ψ ≫ φ = χ) (c : H1OnPoints s) : pullP h' (pullP h c) = pullP h'' c :=
  ((pushC h).pullCohomologyOne_comp (pushC h') c).symm.trans (((pushC h).comp (pushC h')).pullCohomologyOne_eq_of_natTrans (pushC h'')
    { app := fun T ↦
        { ρ := { RingHom.id T.B with commutes' := fun r ↦ congrArg (algebraMap R'' T.B) (e r) }
          pt := by
            change spMap (RingHom.id T.B) ≫ (T.x ≫ ψ) ≫ φ = T.x ≫ χ
            rw [GlobalTheory.Cris.spMap_id, ← e']; simp }
      naturality := fun _ _ _ ↦ hom_ext' fun _ ↦ rfl } (fun _ _ ↦ rfl) c)

theorem toP_eq_zero_iff (c : FirstDeRham s) : toP s c = 0 ↔ c ∈ F1 s := by
  constructor
  · intro hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hc
    refine h1_mk_mem_f1_of_isRep_zero R X s Unit (fun _ ↦ ⊤) (by simp) f
      ⟨fun _ P ↦ g P, fun _ P Q φ _ ↦ ?_, fun _ _ _ _ _ ↦ sub_self _⟩
    exact (congrFun (congrFun (congrFun hg P) Q) φ).symm
  · intro hc
    rw [hodgeFiltration_eq_range] at hc
    obtain ⟨f, rfl⟩ := hc
    refine H1.mk_eq_zero.2 ⟨0, ?_⟩
    funext T T' φ
    rw [map_zero]
    exact (f.2 (Pt.Hom.triv φ) rfl rfl).symm

def SurjAll : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → Function.Surjective (toP (A.hom ≫ 𝟙 _))

end CrystallinePoints.Pd
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.Pull2ChernClassEqZero
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

section Alg

theorem key₁ {B B' : Type} [CommRing B] [CommRing B'] {n : ℕ} (ρ : B →+* B') (fφ : B) (fc fψ : B')
    (aφ gm : Fin n → B) (ac aψ bψ gm' : Fin n → B') (h1 : ρ fφ - fc + fψ = ∑ k, ρ (aφ k) * bψ k)
    (h2 : ∀ k, ac k = ρ (aφ k) + aψ k) (h3 : ∀ k, gm' k = ρ (gm k) + bψ k) :
    fc + ∑ k, ac k * gm' k = ρ (fφ + ∑ k, aφ k * gm k) + (fψ + ∑ k, aψ k * gm' k) := by
  have e : ∀ k, ac k * gm' k = ρ (aφ k) * ρ (gm k) + ρ (aφ k) * bψ k + aψ k * gm' k := by
    intro k
    linear_combination gm' k * h2 k + ρ (aφ k) * h3 k
  have hs := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => e k)
  simp only [Finset.sum_add_distrib] at hs
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum]
  simp only [map_mul]
  linear_combination hs - h1

theorem exists_factor' {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) (x : M →ₗ[R] R)
    (h : ∀ m, f m = 0 → x m = 0) : ∃ x' : N →ₗ[R] R, ∀ m, x' (f m) = x m := by
  have hk : LinearMap.ker f ≤ LinearMap.ker x := fun m hm => h m hm
  refine ⟨(LinearMap.ker f).liftQ x hk ∘ₗ (f.quotKerEquivOfSurjective hf).symm.toLinearMap, fun m => ?_⟩
  have hm : (f.quotKerEquivOfSurjective hf).symm (f m) = Submodule.Quotient.mk m := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp [hm]

end Alg

section Cochain

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

def v1 (f : C1 (FP s)) {S S' : Pt s} (φ : S ⟶ S') : S'.B := f S S' φ

theorem cocycle_value_comp (f : Z1 (FP s)) {S S' S'' : Pt s} (φ : S ⟶ S') (ψ : S' ⟶ S'') (χ : S ⟶ S'')
    (e : ∀ b, χ.ρ b = ψ.ρ (φ.ρ b)) : v1 f.1 χ = ψ.ρ (v1 f.1 φ) + v1 f.1 ψ := by
  have hχ : χ = φ ≫ ψ := by
    obtain ⟨ρχ, hχpt⟩ := χ
    have hρ : ρχ = (φ ≫ ψ).ρ := AlgHom.ext e
    subst hρ
    rfl
  subst hχ
  exact f.2 φ ψ

theorem cocycle_value_sum {n : ℕ} (t : Fin n → R) (z : Fin n → Z1 (FP s)) {S S' : Pt s} (φ : S ⟶ S') :
    v1 (∑ k, t k • z k).1 φ = ∑ k, algebraMap R S'.B (t k) * v1 (z k).1 φ := by
  unfold v1
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Algebra.smul_def _ _

theorem pull2_chern_class_eq_zero {L : LB X} (hL : L.IsLB) {z : SecondDeRham s} (hz : IsChern (dp0 R) s L z) :
    (toPC s).pull2 z = 0 := by
  have hT : ∀ P : Pt s, IsTriv s ((toPC s).G.obj P) := fun P => rfl
  let n : CoefMap (RingHom.id R) ((IsTriv s).ι ⋙ O (dp0 R) s) (FP s) :=
    { G := ObjectProperty.lift (IsTriv s) (toPC s).G hT
      α := fun P => RingHom.id P.B
      naturality := fun φ b => (toPC s).naturality φ b
      smul := fun P r b => (toPC s).smul P r b }
  have he : toPC s = (CoefMap.restrict (O (dp0 R) s) (IsTriv s).ι).comp n := rfl
  rw [he, CoefMap.pullCohomologyTwo_comp, GlobalTheory.CompanionTheory.PdChern.restrict_triv_eq_zero R X s L hL z hz, map_zero]

variable {W Y : Scheme.{0}} {sW : W ⟶ Sp R} {sY : Y ⟶ Sp R} {p : W ⟶ Y}
  (hp : p ≫ sY = sW ≫ spMap (RingHom.id R)) {n : ℕ} (α : Fin n → Z1 (FP sW)) (β : Fin n → Z1 (FP sY))
  (f : C1 (FP sW))

def Bounds : Prop := ∀ (S S' S'' : Pt sW) (φ : S ⟶ S') (ψ : S' ⟶ S'') (χ : S ⟶ S''),
  (∀ b, χ.ρ b = ψ.ρ (φ.ρ b)) →
    ψ.ρ (v1 f φ) - v1 f χ + v1 f ψ = ∑ k, ψ.ρ (v1 (α k).1 φ) * v1 (β k).1 (pushHom hp ψ)

theorem exists_bounds
    (h : ∑ k, cup (FP sW) (H1.mk _ (α k)) (pullP hp (H1.mk _ (β k))) = 0) : ∃ f, Bounds hp α β f := by
  have hpull : ∀ k, pullP hp (H1.mk _ (β k)) = H1.mk (FP sW) ((pushC hp).pullbackOneCocycle (β k)) :=
    fun k => CoefMap.pullCohomologyOne_class _ _
  simp only [hpull, cup_mk] at h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum] at h
  obtain ⟨f, hf⟩ := H2.mk_eq_zero.mp h
  refine ⟨f, fun S S' S'' φ ψ χ e => ?_⟩
  have hχ : χ = φ ≫ ψ := by
    obtain ⟨ρχ, hχpt⟩ := χ
    have hρ : ρχ = (φ ≫ ψ).ρ := AlgHom.ext e
    subst hρ
    rfl
  subst hχ
  have hz := congrFun (congrFun (congrFun (congrFun (congrFun hf S) S') S'') φ) ψ
  simp only [d1_apply, Submodule.coe_sum, Finset.sum_apply, cupZ_apply, CoefMap.pullCocycleOne_apply] at hz
  exact hz

variable {T : Pt sY} {X' : Scheme.{0}} {s' : X' ⟶ Sp T.B} {w : X' ⟶ W}
  (hw : w ≫ sW = s' ≫ spMap (algebraMap R T.B)) (hw₂ : w ≫ p = s' ≫ T.x)

def eHom (S : Pt s') : T ⟶ pushPt hp (pushPt hw S) where
  ρ := { algebraMap T.B S.B with commutes' := fun _ ↦ rfl }
  pt := by
    change spMap (algebraMap T.B S.B) ≫ T.x = (S.x ≫ w) ≫ p
    rw [← S.w, Category.assoc, Category.assoc, hw₂]

variable {α β f}

def hZ (H : Bounds hp α β f) : Z1 (FP s') :=
  ⟨fun S S' φ ↦ (show S'.B from v1 f (pushHom hw φ)) +
      ∑ k, (show S'.B from v1 (α k).1 (pushHom hw φ)) * (show S'.B from v1 (β k).1 (eHom hp hw hw₂ S')),
    fun S S' S'' φ ψ ↦ key₁ (ψ.ρ : S'.B →+* S''.B) _ _ _ _ _ _ _ _ _
      (H _ _ _ (pushHom hw φ) (pushHom hw ψ) (pushHom hw (φ ≫ ψ)) fun _ ↦ rfl)
      (fun k ↦ cocycle_value_comp (α k) (pushHom hw φ) (pushHom hw ψ) (pushHom hw (φ ≫ ψ)) fun _ ↦ rfl)
      (fun k ↦ cocycle_value_comp (β k) (eHom hp hw hw₂ S') (pushHom hp (pushHom hw ψ)) (eHom hp hw hw₂ S'')
        fun b ↦ (ψ.ρ.commutes b).symm)⟩

theorem hZ_rel (H : Bounds hp α β f) {T' : Pt sY} (τ : T ⟶ T') {X'' : Scheme.{0}} {s'' : X'' ⟶ Sp T'.B}
    {w' : X'' ⟶ W} (hw' : w' ≫ sW = s'' ≫ spMap (algebraMap R T'.B)) (hw₂' : w' ≫ p = s'' ≫ T'.x)
    {j : X'' ⟶ X'} (hj : j ≫ s' = s'' ≫ spMap (τ.ρ : T.B →+* T'.B)) (e : j ≫ w = w') :
    H1.mk _ (hZ hp hw' hw₂' H) - pullP hj (H1.mk _ (hZ hp hw hw₂ H)) +
      ∑ k, v1 (β k).1 τ • pullP hj (pullP hw (H1.mk _ (α k))) = 0 := by
  have e1 : ∀ z, pullP hj (H1.mk (FP s') z) = H1.mk (FP s'') ((pushC hj).pullbackOneCocycle z) :=
    fun z => CoefMap.pullCohomologyOne_class _ _
  have e2 : ∀ z, pullP hw (H1.mk (FP sW) z) = H1.mk (FP s') ((pushC hw).pullbackOneCocycle z) :=
    fun z => CoefMap.pullCohomologyOne_class _ _
  simp only [e1, e2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← LinearMap.map_smul, ← map_sum, ← map_sub, ← map_add (f := _)]
  rw [H1.mk_eq_zero]
  let u : ∀ S : Pt s'', pushPt hw (pushPt hj S) ⟶ pushPt hw' S := fun S =>
    { ρ := { RingHom.id S.B with commutes' := fun r => congrArg (algebraMap T'.B S.B) (τ.ρ.commutes r) }
      pt := by
        show Spec.map (CommRingCat.ofHom (RingHom.id S.B)) ≫ (S.x ≫ j) ≫ w = S.x ≫ w'
        rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.assoc, e] }
  refine ⟨fun S => v1 f (u S) + ∑ k, v1 (α k).1 (u S) * v1 (β k).1 (eHom hp hw' hw₂' S), ?_⟩
  funext S S' φ
  rw [amitsur_d0_apply]
  have hR : (↑(hZ hp hw' hw₂' H - (pushC hj).pullbackOneCocycle (hZ hp hw hw₂ H) +
      ∑ x : Fin n, v1 (β x).1 τ • (pushC hj).pullbackOneCocycle ((pushC hw).pullbackOneCocycle (α x))) : C1 (FP s'')) S S' φ
      = (v1 f (pushHom hw' φ) + ∑ k, v1 (α k).1 (pushHom hw' φ) * v1 (β k).1 (eHom hp hw' hw₂' S'))
        - (v1 f (pushHom hw (pushHom hj φ)) + ∑ k, v1 (α k).1 (pushHom hw (pushHom hj φ)) *
            v1 (β k).1 (eHom hp hw hw₂ (pushPt hj S')))
        + ∑ k, algebraMap T'.B S'.B (v1 (β k).1 τ) * v1 (α k).1 (pushHom hw (pushHom hj φ)) := by
    simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def]
    rfl
  rw [hR]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum]
  simp only [map_mul]
  have B1 : mp (FP s'') φ (v1 f (u S)) - v1 f (u S ≫ pushHom hw' φ) + v1 f (pushHom hw' φ)
      = ∑ k, mp (FP s'') φ (v1 (α k).1 (u S)) * v1 (β k).1 (pushHom hp (pushHom hw' φ)) :=
    H _ _ _ (u S) (pushHom hw' φ) (u S ≫ pushHom hw' φ) (fun _ => rfl)
  have B2 : v1 f (pushHom hw (pushHom hj φ)) - v1 f (u S ≫ pushHom hw' φ) + v1 f (u S')
      = ∑ k, v1 (α k).1 (pushHom hw (pushHom hj φ)) * v1 (β k).1 (pushHom hp (u S')) :=
    H _ _ _ (pushHom hw (pushHom hj φ)) (u S') (u S ≫ pushHom hw' φ) (fun _ => rfl)
  have Ek : ∀ k, v1 (α k).1 (u S') * v1 (β k).1 (eHom hp hw' hw₂' S')
      - mp (FP s'') φ (v1 (α k).1 (u S)) * mp (FP s'') φ (v1 (β k).1 (eHom hp hw' hw₂' S))
      - v1 (α k).1 (pushHom hw' φ) * v1 (β k).1 (eHom hp hw' hw₂' S')
      + v1 (α k).1 (pushHom hw (pushHom hj φ)) * v1 (β k).1 (eHom hp hw hw₂ (pushPt hj S'))
      - algebraMap T'.B S'.B (v1 (β k).1 τ) * v1 (α k).1 (pushHom hw (pushHom hj φ))
      - mp (FP s'') φ (v1 (α k).1 (u S)) * v1 (β k).1 (pushHom hp (pushHom hw' φ))
      + v1 (α k).1 (pushHom hw (pushHom hj φ)) * v1 (β k).1 (pushHom hp (u S')) = 0 := by
    intro k
    have A1 : v1 (α k).1 (u S ≫ pushHom hw' φ)
        = mp (FP s'') φ (v1 (α k).1 (u S)) + v1 (α k).1 (pushHom hw' φ) :=
      cocycle_value_comp (α k) (u S) (pushHom hw' φ) (u S ≫ pushHom hw' φ) (fun _ => rfl)
    have A2 : v1 (α k).1 (u S ≫ pushHom hw' φ)
        = v1 (α k).1 (pushHom hw (pushHom hj φ)) + v1 (α k).1 (u S') :=
      cocycle_value_comp (α k) (pushHom hw (pushHom hj φ)) (u S') (u S ≫ pushHom hw' φ) (fun _ => rfl)
    have C1 : v1 (β k).1 (eHom hp hw hw₂ (pushPt hj S') ≫ pushHom hp (u S'))
        = algebraMap T'.B S'.B (v1 (β k).1 τ) + v1 (β k).1 (eHom hp hw' hw₂' S') :=
      cocycle_value_comp (β k) τ (eHom hp hw' hw₂' S') (eHom hp hw hw₂ (pushPt hj S') ≫ pushHom hp (u S')) (fun _ => rfl)
    have C2 : v1 (β k).1 (eHom hp hw hw₂ (pushPt hj S') ≫ pushHom hp (u S'))
        = v1 (β k).1 (eHom hp hw hw₂ (pushPt hj S')) + v1 (β k).1 (pushHom hp (u S')) :=
      cocycle_value_comp (β k) (eHom hp hw hw₂ (pushPt hj S')) (pushHom hp (u S'))
        (eHom hp hw hw₂ (pushPt hj S') ≫ pushHom hp (u S')) (fun _ => rfl)
    have D : v1 (β k).1 (eHom hp hw' hw₂' S')
        = mp (FP s'') φ (v1 (β k).1 (eHom hp hw' hw₂' S)) + v1 (β k).1 (pushHom hp (pushHom hw' φ)) :=
      cocycle_value_comp (β k) (eHom hp hw' hw₂' S) (pushHom hp (pushHom hw' φ)) (eHom hp hw' hw₂' S')
        (fun b => (φ.ρ.commutes b).symm)
    linear_combination (v1 (β k).1 (eHom hp hw' hw₂' S') : S'.B) * (A1 - A2)
      + (mp (FP s'') φ (v1 (α k).1 (u S)) : S'.B) * D
      + (v1 (α k).1 (pushHom hw (pushHom hj φ)) : S'.B) * (C1 - C2)
  have hs := Finset.sum_eq_zero (fun k (_ : k ∈ Finset.univ) => Ek k)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
  linear_combination B2 - B1 + hs

end Cochain

section Fun

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ}

theorem exists_fun (hF : AbelianDeRham.Free) (hB : AbelianDeRham.BaseChange) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {x : HdR A} (hx : x ∈ Fil A) {C : Type} [CommRing C] [Algebra R C]
    {A' : Over (Sp C)} [GrpObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap (algebraMap R C)) φ)
    (hS : Function.Surjective (toP (A'.hom ≫ 𝟙 _)))
    (hφ : φ ≫ A.hom ≫ 𝟙 _ = (A'.hom ≫ 𝟙 _) ≫ spMap (algebraMap R C)) :
    (∃ X : H1OnPoints (A'.hom ≫ 𝟙 _) →ₗ[C] C, ∀ c : primDR A, X (pullP hφ (toP _ c.1)) = algebraMap R C (x c)) ∧
      ∀ u : H1OnPoints (A'.hom ≫ 𝟙 _), u ∈ Submodule.span C (Set.range fun c : primDR A ↦ pullP hφ (toP _ c.1)) := by
  obtain ⟨hbc, hF1⟩ := hB R A g hA hg C A' φ h
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h
  have hg' : SmoothOfRelativeDimension g A'.hom := by
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
    exact MorphismProperty.of_isPullback h.1 hg
  have hall : prim (dp0 C) (𝟙 (Sp C)) A' = ⊤ := (hF C A' g hA' hg').1
  set m := AbelianDeRham.bcMor h with hm
  have hpt : ∀ c : primDR A, pullP hφ (toP _ c.1) = toP _ (m.pull c).1 := fun c => pullP_toP m.isMor c.1
  set x' := hbc.bcMap x with hxe
  have hx' : ∀ c, x' (m.pull c) = algebraMap R C (x c) := hbc.corr_iff.mpr rfl
  let e : FirstDeRham (A'.hom ≫ 𝟙 _) →ₗ[C] primDR A' :=
    LinearMap.codRestrict (primDR A') LinearMap.id (fun d => by
      show d ∈ prim (dp0 C) (𝟙 (Sp C)) A'
      rw [hall]
      exact Submodule.mem_top)
  have hle : Submodule.span C (m.pull '' (PrimitiveSubmodule A)) ≤ LinearMap.ker x' := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hx', (Submodule.mem_dualAnnihilator x).mp hx c hc, map_zero]
  obtain ⟨X, hX⟩ := exists_factor' (toP (A'.hom ≫ 𝟙 _)) hS (x'.comp e) (by
    intro d hd
    rw [toP_eq_zero_iff] at hd
    have hmem : e d ∈ PrimitiveSubmodule A' := hd
    rw [hF1] at hmem
    exact hle hmem)
  refine ⟨⟨X, fun c => ?_⟩, fun u => ?_⟩
  · rw [hpt, hX]
    have he : e (m.pull c).1 = m.pull c := Subtype.ext rfl
    simp only [LinearMap.comp_apply, he, hx']
  · obtain ⟨d, rfl⟩ := hS u
    obtain ⟨t, ht⟩ := hbc.2 (e d)
    have hd : d = (liftSemi m.pull t).1 := by rw [ht]; rfl
    rw [hd]
    clear ht hd
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r c =>
      have hl : liftSemi m.pull (r ⊗ₜ c) = r • m.pull c := by
        first
        | rfl
        | simp [liftSemi]
      rw [hl, Submodule.coe_smul, map_smul, ← hpt]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
    | add a b ha hb =>
      rw [map_add (f := _), Submodule.coe_add, map_add (f := _)]
      exact Submodule.add_mem _ ha hb

end Fun

open scoped CategoryTheory.Obj in
theorem exists_grpPullback {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) :
    ∃ (G' : Over S') (_ : GrpObj G') (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ := by
  letI : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
  letI iP : GrpObj (Over.mk (Limits.pullback.snd G.hom f)) := Over.grpObjMkPullbackSnd
  refine ⟨Over.mk (Limits.pullback.snd G.hom f), iP, Limits.pullback.fst G.hom f,
    ⟨IsPullback.of_hasPullback _ _, ?_⟩⟩
  intro T x y x₀ y₀ hx hy
  rw [Hom.mul_def, Hom.mul_def, Over.grpObjMkPullbackSnd_mul]
  simp only [Over.comp_left, Category.assoc]
  have hm : ((Over.pullback f).map (μ : Over.mk G.hom ⊗ Over.mk G.hom ⟶ Over.mk G.hom)).left ≫
      Limits.pullback.fst G.hom f = Limits.pullback.fst _ f ≫ (μ : Over.mk G.hom ⊗ Over.mk G.hom ⟶ Over.mk G.hom).left := by
    simp only [Over.pullback_map_left]
    exact Limits.pullback.lift_fst _ _ _
  rw [hm]
  have key : (lift x y).left ≫ (Functor.LaxMonoidal.μ (Over.pullback f) (Over.mk G.hom) (Over.mk G.hom)).left ≫
      Limits.pullback.fst _ f = (lift x₀ y₀).left := by
    apply Limits.pullback.hom_ext
    · simp
      exact hx.symm
    · simp
      exact hy.symm
  rw [← key]
  simp only [Category.assoc]

set_option maxHeartbeats 1000000 in
theorem orth_of_surj (hF : AbelianDeRham.Free) (hB : AbelianDeRham.BaseChange) {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hS : ∀ (C : Type) [CommRing C] [Algebra R C] (A' : Over (Sp C)) [GrpObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A (spMap (algebraMap R C)) φ → Function.Surjective (toP (A'.hom ≫ 𝟙 _))) {P : LB (A ⊗ B).left} (hP : P.IsLB) {φ : HdR A →ₗ[R] HdR B →ₗ[R] R} (hφ : IsCorrForm (dp0 R) (𝟙 _) A B P φ) : ∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0 := by
  intro x hx y hy
  obtain ⟨n, a, b, hCh, hform⟩ := hφ
  rw [hform]
  have hp : (snd A B).left ≫ B.hom ≫ 𝟙 (Sp R) = ((A ⊗ B).hom ≫ 𝟙 (Sp R)) ≫ spMap (RingHom.id R) := by
    rw [← Category.assoc, Over.w]
    simp [spMap]
  have hq : (fst A B).left ≫ A.hom ≫ 𝟙 (Sp R) = ((A ⊗ B).hom ≫ 𝟙 (Sp R)) ≫ spMap (RingHom.id R) := by
    rw [← Category.assoc, Over.w]
    simp [spMap]
  have h0 := pull2_chern_class_eq_zero hP hCh
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h0
  simp only [CoefMap.pullCohomologyTwo_cup] at h0
  have eA : ∀ k, (toPC _).pull1 (pullOver (dp0 R) (𝟙 (Sp R)) (fst A B) (a k).1) = pullP hq (toP _ (a k).1) :=
    fun k => (pullP_toP (IsMor.of_dividedPowersZeroIdeal (dp0 R) hq) _).symm
  have eB : ∀ k, (toPC _).pull1 (pullOver (dp0 R) (𝟙 (Sp R)) (snd A B) (b k).1) = pullP hp (toP _ (b k).1) :=
    fun k => (pullP_toP (IsMor.of_dividedPowersZeroIdeal (dp0 R) hp) _).symm
  simp only [eA, eB] at h0
  obtain ⟨α, hα⟩ : ∃ α : Fin n → Z1 (FP ((A ⊗ B).hom ≫ 𝟙 (Sp R))),
      ∀ k, H1.mk _ (α k) = pullP hq (toP _ (a k).1) :=
    ⟨fun k => (H1.mk_surjective _ (pullP hq (toP _ (a k).1))).choose,
      fun k => (H1.mk_surjective _ (pullP hq (toP _ (a k).1))).choose_spec⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin n → Z1 (FP (B.hom ≫ 𝟙 (Sp R))), ∀ k, H1.mk _ (β k) = toP _ (b k).1 :=
    ⟨fun k => (H1.mk_surjective _ (toP _ (b k).1)).choose,
      fun k => (H1.mk_surjective _ (toP _ (b k).1)).choose_spec⟩
  simp only [← hα, ← hβ] at h0
  obtain ⟨f, H⟩ := exists_bounds hp α β h0
  have hex : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), ∃ (A' : Over (Sp T.B)) (_ : GrpObj A') (φ : A'.left ⟶ A.left),
      IsGrpPullback A' A (spMap (algebraMap R T.B)) φ := fun T => exists_grpPullback A _
  choose A' iA φT hT using hex
  have hcond : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), φT T ≫ A.hom = ((A' T).hom ≫ T.x) ≫ B.hom := by
    intro T
    rw [(hT T).1.w, Category.assoc]
    congr 1
    simpa using T.w.symm
  let w : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), (A' T).left ⟶ (A ⊗ B).left :=
    fun T => Limits.pullback.lift (φT T) ((A' T).hom ≫ T.x) (hcond T)
  have hwf : ∀ T, w T ≫ (fst A B).left = φT T := fun T => Limits.pullback.lift_fst _ _ _
  have hws : ∀ T, w T ≫ (snd A B).left = (A' T).hom ≫ T.x := fun T => Limits.pullback.lift_snd _ _ _
  have hw : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), w T ≫ (A ⊗ B).hom ≫ 𝟙 (Sp R) =
      ((A' T).hom ≫ 𝟙 (Sp T.B)) ≫ spMap (algebraMap R T.B) := by
    intro T
    rw [← Over.w (fst A B), ← Category.assoc, ← Category.assoc, hwf, (hT T).1.w]
    simp
  have hw₂ : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), w T ≫ (snd A B).left = ((A' T).hom ≫ 𝟙 (Sp T.B)) ≫ T.x := by
    intro T
    rw [hws]
    simp
  have hφ' : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), φT T ≫ A.hom ≫ 𝟙 (Sp R) =
      ((A' T).hom ≫ 𝟙 (Sp T.B)) ≫ spMap (algebraMap R T.B) := by
    intro T
    simpa using (hT T).1.w
  have hE := fun T => exists_fun hF hB hA hg hx (hT T) (hS T.B (A' T) (φT T) (hT T)) (hφ' T)
  choose X hXc using fun T => (hE T).1
  let g : C0 (FP (B.hom ≫ 𝟙 (Sp R))) := fun T => X T (H1.mk _ (hZ hp (hw T) (hw₂ T) H))
  have key : ∀ (T T' : Pt (B.hom ≫ 𝟙 (Sp R))) (τ : T ⟶ T'),
      g T' - τ.ρ (g T) + ∑ k, v1 (β k).1 τ * algebraMap R T'.B (x (a k)) = 0 := by
    intro T T' τ
    have hsp : spMap (algebraMap R T'.B) = spMap (τ.ρ : T.B →+* T'.B) ≫ spMap (algebraMap R T.B) := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext r
      exact (τ.ρ.commutes r).symm
    have hjc : φT T' ≫ A.hom = ((A' T').hom ≫ spMap (τ.ρ : T.B →+* T'.B)) ≫ spMap (algebraMap R T.B) := by
      rw [(hT T').1.w, Category.assoc, hsp]
    let j : (A' T').left ⟶ (A' T).left := (hT T).1.lift (φT T') ((A' T').hom ≫ spMap (τ.ρ : T.B →+* T'.B)) hjc
    have hjf : j ≫ φT T = φT T' := (hT T).1.lift_fst _ _ _
    have hjs : j ≫ (A' T).hom = (A' T').hom ≫ spMap (τ.ρ : T.B →+* T'.B) := (hT T).1.lift_snd _ _ _
    have hj : j ≫ (A' T).hom ≫ 𝟙 (Sp T.B) = ((A' T').hom ≫ 𝟙 (Sp T'.B)) ≫ spMap (τ.ρ : T.B →+* T'.B) := by
      rw [Category.comp_id (A' T).hom, Category.comp_id (A' T').hom, hjs]
    have he : j ≫ w T = w T' := by
      apply Limits.pullback.hom_ext
      · change (j ≫ w T) ≫ (fst A B).left = w T' ≫ (fst A B).left
        rw [Category.assoc, hwf, hwf, hjf]
      · change (j ≫ w T) ≫ (snd A B).left = w T' ≫ (snd A B).left
        rw [Category.assoc, hws, hws, ← Category.assoc, hjs, Category.assoc, τ.pt]
    have hrel := hZ_rel hp (hw T) (hw₂ T) H τ (hw T') (hw₂ T') hj he
    have hi : ∀ u, X T' (pullP hj u) = τ.ρ (X T u) := by
      intro u
      refine Submodule.span_induction (p := fun u _ => X T' (pullP hj u) = τ.ρ (X T u)) ?_ ?_ ?_ ?_ ((hE T).2 u)
      · rintro _ ⟨c, rfl⟩
        rw [pullP_pullP (hφ' T) hj (hφ' T') (fun r => τ.ρ.commutes r) hjf, hXc, hXc]
        exact (τ.ρ.commutes _).symm
      · simp
      · intro u v _ _ hu hv
        simp only [map_add (f := _), hu, hv]
      · intro c u _ hu
        simp only [map_smulₛₗ, smul_eq_mul, map_mul, hu]
        rfl
    have hii : ∀ k, X T' (pullP hj (pullP (hw T) (H1.mk _ (α k)))) = algebraMap R T'.B (x (a k)) := by
      intro k
      rw [hα k, pullP_pullP hq (hw T) (hφ' T) (fun r => rfl) (hwf T),
        pullP_pullP (hφ' T) hj (hφ' T') (fun r => τ.ρ.commutes r) hjf, hXc]
    have h1 := congrArg (X T') hrel
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sub, map_sum, map_smul, smul_eq_mul, hii, map_zero] at h1
    simp only [hi] at h1
    exact h1
  have hcob : ∃ g : C0 (FP (B.hom ≫ 𝟙 (Sp R))), d0 _ g = ↑(∑ k, x (a k) • β k) := by
    refine ⟨-g, ?_⟩
    funext T T' τ
    rw [amitsur_d0_apply]
    show -g T' - τ.ρ (-g T) = v1 (∑ k, x (a k) • β k).1 τ
    rw [cocycle_value_sum, map_neg]
    have hs : ∑ k, algebraMap R T'.B (x (a k)) * v1 (β k).1 τ = ∑ k, v1 (β k).1 τ * algebraMap R T'.B (x (a k)) :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hs]
    linear_combination -key T T' τ
  have hmk : H1.mk _ (∑ k, x (a k) • β k) = 0 := H1.mk_eq_zero.mpr hcob
  have hc : toP (B.hom ≫ 𝟙 (Sp R)) (∑ k, x (a k) • (b k).1) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_smul, hβ] using hmk
  have hF1 := (toP_eq_zero_iff _).mp hc
  have hcF : (∑ k, x (a k) • b k) ∈ PrimitiveSubmodule B := by
    show (primDR B).subtype (∑ k, x (a k) • b k) ∈ F1 _
    simpa using hF1
  have hy0 := (Submodule.mem_dualAnnihilator _).mp hy _ hcF
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum, map_smul] using hy0

end CrystallinePoints.Pd
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.MkEqZeroOfCover
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.Points

namespace CrystallinePoints.Pd

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' Y : Scheme.{0}}

def pre {B : Type} [CommRing B] (y : Sp B ⟶ Sp R) : R →+* B := (Spec.preimage y).hom

theorem spMap_pre {B : Type} [CommRing B] (y : Sp B ⟶ Sp R) : spMap (pre y) = y := Spec.map_preimage y

@[reducible] def ptOf (s : X ⟶ Sp R) {B : Type} [CommRing B] (x : Sp B ⟶ X) : Pt s where
  B := B
  alg := (pre (x ≫ s)).toAlgebra
  x := x
  w := (spMap_pre _).symm

variable {s : X ⟶ Sp R}

section
variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']

end


end CrystallinePoints.Pd
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

theorem duality_of_surjAll (hF : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge) (hB : AbelianDeRham.BaseChange)
    (hS : SurjAll) : AbelianDeRham.Duality := by
  intro R _ A _ g hA hg L hL ψ hψ
  haveI := hA.comm
  have iso : ∀ x ∈ Fil A, ∀ y ∈ Fil A, ψ x y = 0 :=
    orth_of_surj hF hB hA hg (fun C _ _ A' _ φ h ↦ hS C A' g (GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h)
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg))
      (LB.isLB_linComb hL _ _) (isCorrForm_lam hψ)
  exact ⟨iso, perfect_ring hF hH hB hA hg hL hψ iso⟩

end CrystallinePoints.Pd
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.DualAbelianScheme.AbelianDeRhamDuality.SurjAllOfHodge
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.DualRT

open CrystallinePoints.Pd GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

variable {R : Type} [CommRing R] {X : Scheme.{0}}

@[reducible] def ptOf {s : X ⟶ Sp R} (T : TT s) : Pt s := ⟨T.obj.B, pt T, pt_w T⟩

theorem pt_comp {s : X ⟶ Sp R} {T T' : TT s} (a : T ⟶ T') :
    spMap (a.hom.φ : T.obj.B →+* T'.obj.B) ≫ pt T = pt T' := by
  have key : (a.hom.φ : T.obj.B →+* T'.obj.B).comp ((πe T).symm : T.obj.B₀ →+* T.obj.B)
      = ((πe T').symm : T'.obj.B₀ →+* T'.obj.B).comp a.hom.φ₀ := by
    ext x
    obtain ⟨b, rfl⟩ := (πe T).surjective x
    apply (πe T').injective
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply,
      RingEquiv.apply_symm_apply, AlgHom.coe_toRingHom]
    simp only [πe, RingEquiv.ofBijective_apply]
    exact (a.hom.comm b).symm
  unfold pt
  rw [← a.hom.pt]
  simp only [spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [key]

def ofPC (s : X ⟶ Sp R) : CoefMap (RingHom.id R) (FP s) ((IsTriv s).ι ⋙ O (dp0 R) s) where
  G := { obj := ptOf
         map := fun a ↦ ⟨a.hom.φ, pt_comp a⟩
         map_id := fun _ ↦ CrystallinePoints.Pd.hom_ext' fun _ ↦ rfl
         map_comp := fun _ _ ↦ CrystallinePoints.Pd.hom_ext' fun _ ↦ rfl }
  α T := RingHom.id T.obj.B
  naturality _ _ := rfl
  smul _ _ _ := rfl

def toPO (s : X ⟶ Sp R) : CoefMap (RingHom.id R) ((IsTriv s).ι ⋙ O (dp0 R) s) (FP s) :=
  ptCoef (F := FP s) (fun P ↦ P.x) (fun P ↦ P.w) fun _ _ a ↦ a.pt

theorem toPO_toH1O (s : X ⟶ Sp R) (c : FirstDeRham s) : (toPO s).pull1 (toH1O s c) = toP s c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rfl

private theorem spMap_id_comp_spMap_symm_comp {A : Type} [CommRing A] [Algebra R A] {Y : Scheme} (e : A ≃+* A)
    (he : ∀ z, e z = z) (y : Sp A ⟶ Y) :
    spMap ((AlgHom.id R A : A →ₐ[R] A) : A →+* A) ≫ spMap (e.symm : A →+* A) ≫ y = y := by
  have h1 : (e.symm : A →+* A) = RingHom.id A := by
    ext z
    apply e.injective
    show e (e.symm z) = e z
    rw [RingEquiv.apply_symm_apply, he]
  have h2 : ((AlgHom.id R A : A →ₐ[R] A) : A →+* A) = RingHom.id A := rfl
  rw [h1, h2]
  simp [spMap]

theorem toPO_ofPC (s : X ⟶ Sp R) (c : H1OnPoints s) : (toPO s).pull1 ((ofPC s).pull1 c) = c := by
  rw [← CoefMap.pullCohomologyOne_comp]
  let θ : ((ofPC s).comp (toPO s)).G ⟶ (CoefMap.id (FP s)).G :=
    { app := fun P => ⟨AlgHom.id R P.B, spMap_id_comp_spMap_symm_comp _ (fun _ => rfl) P.x⟩
      naturality := fun _ _ _ => CrystallinePoints.Pd.hom_ext' fun _ => rfl }
  exact (CoefMap.pullCohomologyOne_eq_of_natTrans _ (CoefMap.id (FP s)) θ (fun _ _ => rfl) c).trans (CoefMap.pullCohomologyOne_id c)

private theorem cmpO_toH1O_eq_toHO1_cmp1 (s : X ⟶ Sp R) (c : FirstDeRham s) :
    GlobalTheory.CechDR.cmpO s (toH1O s c) = toHO1 s (cmp1 s c) := by
  obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective _ c
  rfl

theorem toPicard_surjective (s : X ⟶ Sp R) (h₁ : Function.Surjective (cmp1 s)) (h₂ : Function.Surjective (toHO1 s)) :
    Function.Surjective (toP s) := by
  intro t
  obtain ⟨c, hc⟩ := (h₂.comp h₁) (GlobalTheory.CechDR.cmpO s ((ofPC s).pull1 t))
  refine ⟨c, ?_⟩
  have e : toH1O s c = (ofPC s).pull1 t :=
    GlobalTheory.CechDR.cmpO_injective R X s (by rw [cmpO_toH1O_eq_toHO1_cmp1]; exact hc)
  rw [← toPO_toH1O, e, toPO_ofPC]

theorem surjAll_of_hodge (hC : CrystallineSmoothLift) (hH : AbelianHodgeDeRham) : SurjAll := by
  intro R _ A _ g hAb hsm
  haveI := hAb
  haveI : IsProper A.hom := IsAbelianScheme.proper
  have hs : A.hom ≫ 𝟙 (Sp R) = A.hom := Category.comp_id _
  refine toPicard_surjective _ ?_ ?_
  · rw [hs]
    exact (hC.bijective_cechDeRhamComparison_degreeOne A.hom IsAbelianScheme.smooth inferInstance inferInstance).2
  · rw [hs]
    exact (hH R A g hAb hsm).2.2.2.2.1.2.2

end PositivityTheory.DualRT
end
end

set_option autoImplicit false

namespace PositivityTheory.DualRT

open GlobalTheory.Published
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CrystallinePoints.Pd

theorem surjAll : CrystallinePoints.Pd.SurjAll := by
  intro R _ A _ g hAb hsm
  haveI := hAb
  haveI : IsProper A.hom := IsAbelianScheme.proper
  have hs : A.hom ≫ 𝟙 (Sp R) = A.hom := Category.comp_id _
  refine toPicard_surjective _ ?_ ?_
  · rw [hs]
    exact (GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations.bijective_cechDeRhamComparison_degreeOne A.hom IsAbelianScheme.smooth inferInstance inferInstance).2
  · rw [hs]
    exact (MainStatements.Hodge.Free.abelianHodgeDeRham R A g hAb hsm).2.2.2.2.1.2.2

theorem duality : AbelianDeRham.Duality :=
  have hS := AbelianDeRhamStructureFromPages.Adrs.abelianDeRhamStructure_of_page MainStatements.Hodge.Free.abelianDeRhamPage
  CrystallinePoints.Pd.duality_of_surjAll (GlobalTheory.abelianDeRhamStructure_toFree hS) hS.2.1 hS.2.2 surjAll

theorem abelianDeRham : AbelianDeRham :=
  have hS := AbelianDeRhamStructureFromPages.Adrs.abelianDeRhamStructure_of_page MainStatements.Hodge.Free.abelianDeRhamPage
  have hF := GlobalTheory.abelianDeRhamStructure_toFree hS
  ⟨hF, hS.2.1, hS.2.2, AbelianDeRham.rigid_of_free_of_crystallineDeRham hF FubiniStudyChowHeightFormula₂.Adr.crystallineDeRham, duality⟩

end PositivityTheory.DualRT
