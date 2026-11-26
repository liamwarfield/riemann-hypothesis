module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentImagesLinearIndependent
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientAffineOpenSpecInvariants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientAffineOpenSpecInvariants
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem quot_affine_spec_invariants : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [Algebra R R'], Base R → FinExt (algebraMap R R') → IsGal (algebraMap R R') → ∀ (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), (∀ σ, act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ)) → act 1 = 𝟙 _ → (∀ σ τ, act (σ * τ) = act σ ≫ act τ) → ∀ (H : G'.left.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H) (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap (algebraMap R R') → IsAffineHom π → (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ V : X.left.Opens, IsAffineOpen V → ∃ (C' : Type) (_ : CommRing C') (_ : Algebra R C') (_ : Algebra R' C') (_ : IsScalarTower R R' C') (actC : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')) (C : Subalgebra R C') (j : Sp C' ⟶ H.toScheme) (l : Sp C ⟶ X.left), IsOpenImmersion j ∧ IsOpenImmersion l ∧ Set.range l = (V : Set X.left) ∧ IsPullback j (spMap (algebraMap C C')) π l ∧ j ≫ H.ι ≫ G'.hom = spMap (algebraMap R' C') ∧ l ≫ X.hom = spMap (algebraMap R C) ∧ (∀ σ, spMap (actC σ : C' →+* C') ≫ j ≫ H.ι = j ≫ H.ι ≫ act σ) ∧ (∀ σ r, actC σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) ∧ ∀ x, x ∈ C ↔ ∀ σ, actC σ x = x := by
  intro R _ _ _ R' _ _ _ _ _ _ _ G' act hact h1 hmul H hH X π hπ hAff hinv _ hsec V hV
  haveI := hAff
  have hU : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  let r : Gal (algebraMap R R') → (H.toScheme ⟶ H.toScheme) := fun σ => (act σ).resLE H H (hH σ).ge
  have hrπ : ∀ σ, r σ ≫ π = π := hinv
  have hr : ∀ σ, π ⁻¹ᵁ V ≤ (r σ) ⁻¹ᵁ (π ⁻¹ᵁ V) := fun σ x hx => by
    show x ∈ (r σ ≫ π) ⁻¹ᵁ V
    rw [hrπ σ]; exact hx
  have hrι : ∀ σ, r σ ≫ H.ι = H.ι ≫ act σ := fun σ => Scheme.Hom.resLE_comp_ι _ _
  let a : Gal (algebraMap R R') → (Γ(H.toScheme, π ⁻¹ᵁ V) ⟶ Γ(H.toScheme, π ⁻¹ᵁ V)) :=
    fun σ => (r σ).appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (hr σ)
  have key0 : ∀ σ, Spec.map (a σ) ≫ hU.fromSpec = hU.fromSpec ≫ r σ := fun σ =>
    IsAffineOpen.SpecMap_appLE_fromSpec (r σ) hU hU (hr σ)
  have key : ∀ σ, Spec.map (a σ) ≫ hU.fromSpec ≫ H.ι = hU.fromSpec ≫ H.ι ≫ act σ := fun σ => by
    rw [← Category.assoc, key0, Category.assoc, hrι]
  have key_assoc : ∀ σ {Z : Scheme.{0}} (g : G'.left ⟶ Z),
      Spec.map (a σ) ≫ hU.fromSpec ≫ H.ι ≫ g = hU.fromSpec ≫ H.ι ≫ act σ ≫ g := fun σ Z g => by
    simpa only [Category.assoc] using congrArg (· ≫ g) (key σ)
  have a_one : a 1 = 𝟙 _ := by
    rw [← Spec.map_inj, ← cancel_mono (hU.fromSpec ≫ H.ι), key, h1, Spec.map_id]
    simp
  have a_mul : ∀ σ τ, a (σ * τ) = a τ ≫ a σ := fun σ τ => by
    rw [← Spec.map_inj, ← cancel_mono (hU.fromSpec ≫ H.ι), key, hmul, Spec.map_comp]
    simp only [Category.assoc, key, key_assoc]
  have a_one' : ∀ x, (a 1).hom x = x := fun x => by rw [a_one]; rfl
  have a_mul' : ∀ σ τ x, (a (σ * τ)).hom x = (a σ).hom ((a τ).hom x) := fun σ τ x => by
    rw [a_mul]; rfl
  obtain ⟨φ', hφ'⟩ : ∃ φ' : CommRingCat.of R' ⟶ Γ(H.toScheme, π ⁻¹ᵁ V),
      Spec.map φ' = hU.fromSpec ≫ H.ι ≫ G'.hom := ⟨Spec.preimage _, Spec.map_preimage _⟩
  have semi : ∀ σ, φ' ≫ a σ = CommRingCat.ofHom (Gal.hom σ) ≫ φ' := fun σ => by
    rw [← Spec.map_inj, Spec.map_comp, Spec.map_comp, hφ', key_assoc, hact]
    simp only [Category.assoc]
  have semi' : ∀ σ y, (a σ).hom (φ'.hom y) = φ'.hom (σ.1 y) := fun σ y =>
    congrArg (fun f => f.hom y) (semi σ)
  letI alg' : Algebra R' Γ(H.toScheme, π ⁻¹ᵁ V) := φ'.hom.toAlgebra
  letI algR : Algebra R Γ(H.toScheme, π ⁻¹ᵁ V) := (φ'.hom.comp (algebraMap R R')).toAlgebra
  haveI tow : IsScalarTower R R' Γ(H.toScheme, π ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have fixR : ∀ σ r, (a σ).hom (algebraMap R Γ(H.toScheme, π ⁻¹ᵁ V) r) = algebraMap R Γ(H.toScheme, π ⁻¹ᵁ V) r :=
    fun σ r => by
      show (a σ).hom (φ'.hom (algebraMap R R' r)) = φ'.hom (algebraMap R R' r)
      rw [semi' σ]
      exact congrArg φ'.hom ((show ∀ r, σ.1 (algebraMap R R' r) = algebraMap R R' r from σ.2) r)
  let ah : Gal (algebraMap R R') → (Γ(H.toScheme, π ⁻¹ᵁ V) →ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) :=
    fun σ => { (a σ).hom with commutes' := fixR σ }
  have inv1 : ∀ σ x, (a σ).hom ((a σ⁻¹).hom x) = x := fun σ x => by
    rw [← a_mul', mul_inv_cancel, a_one']
  have inv2 : ∀ σ x, (a σ⁻¹).hom ((a σ).hom x) = x := fun σ x => by
    rw [← a_mul', inv_mul_cancel, a_one']
  let actE : Gal (algebraMap R R') → (Γ(H.toScheme, π ⁻¹ᵁ V) ≃ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) := fun σ =>
    AlgEquiv.ofAlgHom (ah σ) (ah σ⁻¹) (AlgHom.ext fun x => inv1 σ x) (AlgHom.ext fun x => inv2 σ x)
  let actC : Gal (algebraMap R R') →* (Γ(H.toScheme, π ⁻¹ᵁ V) ≃ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) :=
    { toFun := actE
      map_one' := AlgEquiv.ext fun x => a_one' x
      map_mul' := fun σ τ => AlgEquiv.ext fun x => a_mul' σ τ x }
  have actC_apply : ∀ σ x, actC σ x = (a σ).hom x := fun _ _ => rfl
  let C : Subalgebra R Γ(H.toScheme, π ⁻¹ᵁ V) :=
    ⨅ σ, AlgHom.equalizer (actC σ : Γ(H.toScheme, π ⁻¹ᵁ V) →ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) (AlgHom.id R _)
  have memC : ∀ x, x ∈ C ↔ ∀ σ, actC σ x = x := fun x =>
    Algebra.mem_iInf.trans (forall_congr' fun σ => Iff.rfl)
  have happ : Spec.map (π.app V) ≫ hV.fromSpec = hU.fromSpec ≫ π := by
    rw [Scheme.Hom.app_eq_appLE]; exact IsAffineOpen.SpecMap_appLE_fromSpec π hV hU le_rfl
  have hmem : ∀ g, (π.app V).hom g ∈ C := by
    intro g; rw [memC]; intro σ
    have e : π.app V ≫ a σ = π.app V := by
      rw [← Spec.map_inj, ← cancel_mono hV.fromSpec, Spec.map_comp]
      simp only [Category.assoc]
      rw [happ, ← Category.assoc, key0, Category.assoc, hrπ]
    exact congrArg (fun f => f.hom g) e
  let ψ : Γ(X.left, V) →+* C := (π.app V).hom.codRestrict C hmem
  have hbij : Function.Bijective ψ := by
    refine ⟨fun x y h => (hsec V).1 (congrArg Subtype.val h), fun ⟨y, hy⟩ => ?_⟩
    obtain ⟨x, hx⟩ := (hsec V).2 y (fun σ _ => (memC y).1 hy σ)
    exact ⟨x, Subtype.ext hx⟩
  let eψ := RingEquiv.ofBijective ψ hbij
  let l : Sp C ⟶ X.left := Spec.map eψ.toCommRingCatIso.hom ≫ hV.fromSpec
  have hlr : l.opensRange = V := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, IsAffineOpen.opensRange_fromSpec]
  have sq : hU.fromSpec ≫ π = spMap (algebraMap C Γ(H.toScheme, π ⁻¹ᵁ V)) ≫ l := by
    rw [← happ]
    show _ = _ ≫ Spec.map eψ.toCommRingCatIso.hom ≫ hV.fromSpec
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hj : hU.fromSpec ≫ H.ι ≫ G'.hom = spMap (algebraMap R' Γ(H.toScheme, π ⁻¹ᵁ V)) := by
    rw [← hφ']; rfl
  have hl : l ≫ X.hom = spMap (algebraMap R C) := by
    obtain ⟨m, hm⟩ : ∃ m : CommRingCat.of R ⟶ CommRingCat.of C, Spec.map m = l ≫ X.hom :=
      ⟨Spec.preimage _, Spec.map_preimage _⟩
    rw [← hm]
    have e : m ≫ CommRingCat.ofHom (algebraMap C Γ(H.toScheme, π ⁻¹ᵁ V)) =
        CommRingCat.ofHom (algebraMap R Γ(H.toScheme, π ⁻¹ᵁ V)) := by
      rw [← Spec.map_inj, Spec.map_comp, hm, ← Category.assoc, ← sq, Category.assoc, hπ]
      have h2 := congrArg (· ≫ spMap (algebraMap R R')) hj
      simp only [Category.assoc] at h2
      rw [h2, ← Spec.map_comp]
      rfl
    congr 1
    ext r
    exact congrArg (fun f => f.hom r) e
  refine ⟨Γ(H.toScheme, π ⁻¹ᵁ V), inferInstance, algR, alg', tow, actC, C, hU.fromSpec, l, inferInstance,
    inferInstance, ?_, ?_, hj, hl, ?_, ?_, memC⟩
  · exact congrArg (fun U : X.left.Opens => (U : Set X.left)) hlr
  · refine (IsOpenImmersion.isPullback _ _ _ _ sq ?_).flip
    rw [hlr, IsAffineOpen.opensRange_fromSpec]
  · intro σ
    exact key σ
  · intro σ y
    exact semi' σ y

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientAffineOpenSpecInvariantsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisQuotient_affineOpen_spec_invariants : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [Algebra R R'], Base R → FinExt (algebraMap R R') → IsGal (algebraMap R R') → ∀ (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), (∀ σ, act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ)) → act 1 = 𝟙 _ → (∀ σ τ, act (σ * τ) = act σ ≫ act τ) → ∀ (H : G'.left.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H) (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap (algebraMap R R') → IsAffineHom π → (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ V : X.left.Opens, IsAffineOpen V → ∃ (C' : Type) (_ : CommRing C') (_ : Algebra R C') (_ : Algebra R' C') (_ : IsScalarTower R R' C') (actC : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')) (C : Subalgebra R C') (j : Sp C' ⟶ H.toScheme) (l : Sp C ⟶ X.left), IsOpenImmersion j ∧ IsOpenImmersion l ∧ Set.range l = (V : Set X.left) ∧ IsPullback j (spMap (algebraMap C C')) π l ∧ j ≫ H.ι ≫ G'.hom = spMap (algebraMap R' C') ∧ l ≫ X.hom = spMap (algebraMap R C) ∧ (∀ σ, spMap (actC σ : C' →+* C') ≫ j ≫ H.ι = j ≫ H.ι ≫ act σ) ∧ (∀ σ r, actC σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) ∧ ∀ x, x ∈ C ↔ ∀ σ, actC σ x = x := by
  first | exact @GlobalTheory.Mum.quot_affine_spec_invariants | exact GlobalTheory.Mum.quot_affine_spec_invariants | (intros; apply GlobalTheory.Mum.quot_affine_spec_invariants <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGeneratorFactorPairingGenericMumfordBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGeneratorFactorPairingGenericMumfordBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem lbIso_pull_pull_comp {X Y Z : Scheme.{0}} {M : LB X} (hM : M.IsLB) (F : Y ⟶ X) (g : Z ⟶ Y) :
    LBIso ((M.pull F).pull g) (M.pull (g ≫ F)) :=
  Geo.Tor.LBIso.chartPull (h := g) (Geo.Tor.chartPullPull (M.pull F) g g rfl)
    (Geo.Tor.chartPullSame M (fun _ => g ≫ F) (fun _ => F) (fun _ => 1) g (fun _ => rfl))
    (GlobalTheory.PolBaseChange.lbIso_refl (LB.isLB_pull hM F))

theorem exists_gen_pull_pull_iff {X Y Z : Scheme.{0}} {M : LB X} (hM : M.IsLB) (F : Y ⟶ X) (g : Z ⟶ Y) :
    (∃ t : LB.Gen ((M.pull F).pull g), t.IsGen) ↔ ∃ t : LB.Gen (M.pull (g ≫ F)), t.IsGen := by
  have h₁ := LB.isLB_pull (LB.isLB_pull hM F) g
  have h₂ := LB.isLB_pull hM (g ≫ F)
  exact ⟨GlobalTheory.CM.PairingIso.exists_gen_of_lbIso h₁ h₂ (lbIso_pull_pull_comp hM F g),
    GlobalTheory.CM.PairingIso.exists_gen_of_lbIso h₂ h₁ (Geo.Tor.LBIso.symm (lbIso_pull_pull_comp hM F g))⟩

theorem left_tensor_ext {S : Scheme.{0}} {X Y : Over S} {Z : Scheme.{0}} (u v : Z ⟶ (X ⊗ Y).left)
    (h₁ : u ≫ (fst X Y).left = v ≫ (fst X Y).left) (h₂ : u ≫ (snd X Y).left = v ≫ (snd X Y).left) : u = v := by
  rw [Over.fst_left] at h₁
  rw [Over.snd_left] at h₂
  exact pullback.hom_ext h₁ h₂

theorem pull_gen_lam_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (inc : G ⟶ G'), IsMonHom inc → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → ∃ t : LB.Gen (letI := A'.isAb.comm; (abelian₂ A'.A A'.L).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ (x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom)) (fst ((Over.pullback (jK R)).obj G) T ≫ ((Over.pullback (jK R)).map inc ≫ U'.gen.hom) ≫ oA.act F.f) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 A'.A).left), t.IsGen := by
  intro R _ _ _ D D' F A' G' _ _ U' oA oG hlin G _ _ inc hinc κ₀ hκ T x ht
  letI := A'.isAb.comm
  haveI : IsMonHom U'.gen.hom := U'.gen_hom
  have hL' : U'.LG.L.IsLB := U'.LG.isLB
  have hQ : (abelian₂ G' U'.LG.L).IsLB := DVR.linComb_isLB _ hL' _ _
  have hA : A'.L.IsLB := A'.isLB
  have hQA : (abelian₂ A'.A A'.L).IsLB := DVR.linComb_isLB _ hA _ _
  obtain ⟨β₂, hβ₂, Hβ⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (jK R) G' ((Over.pullback (jK R)).obj G')
    (pullback.fst G'.hom (jK R)) (Geo.Tor.isGrpPullback_pullback G' (jK R))
  have E₁ := Hβ U'.LG.L (U'.LG.L.pull (pullback.fst G'.hom (jK R))) _ (abelian₂ G' U'.LG.L) (𝟙 _) hL'
    (LB.isLB_pull hL' _) hQ (GlobalTheory.PolBaseChange.lbIso_refl (LB.isLB_pull hL' _))
    (Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl hQ))
  obtain ⟨γ₂, hγ₂, Hγ⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (𝟙 _) A'.A ((Over.pullback (jK R)).obj G')
    U'.gen.hom.left (Geo.Tor.isGrpPullback_of_iso U'.gen)
  have E₂ := Hγ A'.L (U'.LG.L.pull (pullback.fst G'.hom (jK R))) _ (abelian₂ A'.A A'.L) (𝟙 _) hA
    (LB.isLB_pull hL' _) hQA (Geo.Tor.LBIso.symm U'.ext)
    (Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl hQA))
  have E₃ := Geo.Tor.LBIso.trans (LB.isLB_pull hQ _) (DVR.linComb_isLB _ (LB.isLB_pull hL' _) _ _)
    (LB.isLB_pull hQA _) (Geo.Tor.LBIso.symm E₁) E₂
  let m := (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x ≫ (Over.pullback (jK R)).map inc)
    (fst ((Over.pullback (jK R)).obj G) T ≫ (Over.pullback (jK R)).map inc ≫ (Over.pullback (jK R)).map (oG.act F.f))).left
  have E₄ := Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullPull _ m m rfl) (Geo.Tor.chartPullPull _ m m rfl) E₃
  obtain ⟨t, ht⟩ := ht
  let φl := (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left
  let ψl := (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left
  let χl := (lift (snd ((Over.pullback (jK R)).obj G) T ≫ (x ≫ ((Over.pullback (jK R)).map inc) ≫ U'.gen.hom)) (fst ((Over.pullback (jK R)).obj G) T ≫ (((Over.pullback (jK R)).map inc) ≫ U'.gen.hom) ≫ oA.act F.f) :
    ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 A'.A).left
  have hinc' : ((Over.pullback (jK R)).map inc).left ≫ pullback.fst G'.hom (jK R) = pullback.fst G.hom (jK R) ≫ inc.left :=
    pullback.lift_fst _ _ _
  have hf' : ((Over.pullback (jK R)).map (oG.act F.f)).left ≫ pullback.fst G'.hom (jK R) = pullback.fst G'.hom (jK R) ≫ (oG.act F.f).left :=
    pullback.lift_fst _ _ _
  have hgen : ((Over.pullback (jK R)).map (oG.act F.f)).left ≫ U'.gen.hom.left = U'.gen.hom.left ≫ (oA.act F.f).left :=
    congrArg Over.Hom.left (hlin.ext F.f)
  have hφ1 : φl ≫ (fst G' G').left = (fst G G).left ≫ inc.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_fst (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f))
  have hφ2 : φl ≫ (snd G' G').left = (snd G G).left ≫ inc.left ≫ (oG.act F.f).left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_snd (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f))
  have hψ1 : ψl ≫ (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)).left = (snd ((Over.pullback (jK R)).obj G) T).left ≫ x.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_fst (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T))
  have hψ2 : ψl ≫ (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)).left = (fst ((Over.pullback (jK R)).obj G) T).left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_snd (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T))
  have hm1 : m ≫ (fst ((Over.pullback (jK R)).obj G') ((Over.pullback (jK R)).obj G')).left = (snd ((Over.pullback (jK R)).obj G) T).left ≫ x.left ≫ ((Over.pullback (jK R)).map inc).left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_fst (snd ((Over.pullback (jK R)).obj G) T ≫ x ≫ ((Over.pullback (jK R)).map inc)) (fst ((Over.pullback (jK R)).obj G) T ≫ ((Over.pullback (jK R)).map inc) ≫ ((Over.pullback (jK R)).map (oG.act F.f))))
  have hm2 : m ≫ (snd ((Over.pullback (jK R)).obj G') ((Over.pullback (jK R)).obj G')).left = (fst ((Over.pullback (jK R)).obj G) T).left ≫ ((Over.pullback (jK R)).map inc).left ≫ ((Over.pullback (jK R)).map (oG.act F.f)).left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_snd (snd ((Over.pullback (jK R)).obj G) T ≫ x ≫ ((Over.pullback (jK R)).map inc)) (fst ((Over.pullback (jK R)).obj G) T ≫ ((Over.pullback (jK R)).map inc) ≫ ((Over.pullback (jK R)).map (oG.act F.f))))
  have hχ1 : χl ≫ (fst A'.A A'.A).left = (snd ((Over.pullback (jK R)).obj G) T).left ≫ x.left ≫ ((Over.pullback (jK R)).map inc).left ≫ U'.gen.hom.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_fst (snd ((Over.pullback (jK R)).obj G) T ≫ (x ≫ ((Over.pullback (jK R)).map inc) ≫ U'.gen.hom)) (fst ((Over.pullback (jK R)).obj G) T ≫ (((Over.pullback (jK R)).map inc) ≫ U'.gen.hom) ≫ oA.act F.f))
  have hχ2 : χl ≫ (snd A'.A A'.A).left = (fst ((Over.pullback (jK R)).obj G) T).left ≫ ((Over.pullback (jK R)).map inc).left ≫ U'.gen.hom.left ≫ (oA.act F.f).left := by
    have := congrArg Over.Hom.left (lift_snd (snd ((Over.pullback (jK R)).obj G) T ≫ (x ≫ ((Over.pullback (jK R)).map inc) ≫ U'.gen.hom)) (fst ((Over.pullback (jK R)).obj G) T ≫ (((Over.pullback (jK R)).map inc) ≫ U'.gen.hom) ≫ oA.act F.f))
    simp only [Over.comp_left, Category.assoc] at this
    exact this
  have eq1 : ψl ≫ κ₀ ≫ φl = m ≫ β₂ ≫ 𝟙 _ := by
    apply left_tensor_ext
    · simp only [Category.assoc, Category.comp_id]
      rw [hφ1, reassoc_of% hκ.1]
      rw [reassoc_of% hψ1]
      rw [hβ₂.1]
      rw [reassoc_of% hm1]
      simp only [Category.assoc, hinc']
    · simp only [Category.assoc, Category.comp_id]
      rw [hφ2, reassoc_of% hκ.2]
      rw [reassoc_of% hψ2]
      rw [hβ₂.2]
      rw [reassoc_of% hm2]
      simp only [Category.assoc, hf']
      rw [reassoc_of% hinc']
  have eq2 : m ≫ γ₂ ≫ 𝟙 _ = χl := by
    apply left_tensor_ext
    · simp only [Category.assoc, Category.comp_id]
      rw [hγ₂.1]
      rw [reassoc_of% hm1, hχ1]
    · simp only [Category.assoc, Category.comp_id]
      rw [hγ₂.2]
      rw [reassoc_of% hm2, hχ2, hgen]
  have hP1 := LB.isLB_pull (LB.isLB_pull (LB.isLB_pull hQ φl) κ₀) ψl
  have hP2 := LB.isLB_pull (LB.isLB_pull hQ (κ₀ ≫ φl)) ψl
  have g₀ := GlobalTheory.CM.PairingIso.exists_gen_of_lbIso hP1 hP2
    (Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullPull _ ψl ψl rfl) (Geo.Tor.chartPullPull _ ψl ψl rfl)
      (lbIso_pull_pull_comp hQ φl κ₀)) ⟨t, ht⟩
  have g₁ := (exists_gen_pull_pull_iff hQ (κ₀ ≫ φl) ψl).1 g₀
  rw [eq1] at g₁
  have g₂ := (exists_gen_pull_pull_iff hQ (β₂ ≫ 𝟙 _) m).2 g₁
  have g₃ := GlobalTheory.CM.PairingIso.exists_gen_of_lbIso (LB.isLB_pull (LB.isLB_pull hQ _) _)
    (LB.isLB_pull (LB.isLB_pull hQA _) _) E₄ g₂
  have g₄ := (exists_gen_pull_pull_iff hQA (γ₂ ≫ 𝟙 _) m).1 g₃
  rw [eq2] at g₄
  exact g₄

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGeneratorFactorPairingGenericMumfordBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pull_generator_factor_pairing_generic_mumfordBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (inc : G ⟶ G'), IsMonHom inc → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → ∃ t : LB.Gen (letI := A'.isAb.comm; (abelian₂ A'.A A'.L).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ (x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom)) (fst ((Over.pullback (jK R)).obj G) T ≫ ((Over.pullback (jK R)).map inc ≫ U'.gen.hom) ≫ oA.act F.f) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 A'.A).left), t.IsGen := by
  first | exact @GlobalTheory.Mum.pull_gen_lam_generic | exact GlobalTheory.Mum.pull_gen_lam_generic | (intros; apply GlobalTheory.Mum.pull_gen_lam_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleLiftOfNilpotentDividedPowersThickening
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleLiftOfNilpotentDividedPowersThickening
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleNilThickening

theorem exists_pow_eq_bot_of_isNilDP {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I}
    (h : IsNilDP κ) : ∃ N : ℕ, I ^ N = ⊥ := by
  obtain ⟨N, hN⟩ := h
  have hlen : ∀ l : List R, ((l.map fun x => ((1 : ℕ), x)).map Prod.fst).sum = l.length := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega
  have hprod : ∀ l : List R, (∀ x ∈ l, x ∈ I) →
      ((l.map fun x => ((1 : ℕ), x)).map fun p => κ.dpow p.1 p.2).prod = l.prod := by
    intro l hl; induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [κ.dpow_one (hl a (by simp)), ih fun x hx => hl x (by simp [hx])]
  have hl : ∀ l : List R, (∀ x ∈ l, x ∈ I) → N ≤ l.length → l.prod = 0 := by
    intro l hl' hle
    rw [← hprod l hl']
    exact hN _ (by simpa using hl') (by rw [hlen]; exact hle)
  have key : ∀ k : ℕ, ∀ y ∈ I ^ k, ∀ l : List R, (∀ x ∈ l, x ∈ I) → N ≤ k + l.length → l.prod * y = 0 := by
    intro k
    induction k with
    | zero => intro y _ l hl' hle; rw [hl l hl' (by omega), zero_mul]
    | succ k ih =>
      intro y hy l hl' hle
      rw [pow_succ] at hy
      refine Submodule.mul_induction_on (C := fun y => l.prod * y = 0) hy ?_ ?_
      · intro a ha b hb
        have := ih a ha (b :: l) (by simpa [hb] using hl') (by simp; omega)
        rw [List.prod_cons] at this
        rw [← this]; ring
      · intro y z hy hz; rw [mul_add, hy, hz, add_zero]
  refine ⟨N, eq_bot_iff.2 fun y hy => ?_⟩
  have := key N y hy [] (fun x hx => by cases hx) (Nat.le_add_right N _)
  simpa using this

end GlobalTheory.AmpleNilThickening

namespace GlobalTheory.AmpleNilThickening

theorem relAmple_of_pow_eq_bot : ∀ (n : ℕ) (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π ^ n = ⊥ →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (β : X₀.left ⟶ X.left), IsPullback β X₀.hom X.hom (spMap π) →
      LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L₀ : LB X₀.left), L.IsLB → L₀.IsLB → LBIso L₀ (L.pull β) →
      Out.RelAmple X₀ L₀ → Out.RelAmple X L := by
  intro n
  induction n with
  | zero =>
    intro R R₀ _ _ π hπ hn X X₀ β hβ hX L L₀ hL hL₀ hw hA
    have h2 : RingHom.ker π ^ 2 = ⊥ := eq_bot_iff.2 ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
    exact GlobalTheory.AmpleThickening.relAmple_of_sq_zero R R₀ π hπ h2 X X₀ β hβ hX L L₀ hL hL₀ hw hA
  | succ n ih =>
    intro R R₀ _ _ π hπ hn X X₀ β hβ hX L L₀ hL hL₀ hw hA
    by_cases h0 : n = 0
    · subst h0
      have h2 : RingHom.ker π ^ 2 = ⊥ := eq_bot_iff.2 ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
      exact GlobalTheory.AmpleThickening.relAmple_of_sq_zero R R₀ π hπ h2 X X₀ β hβ hX L L₀ hL hL₀ hw hA
    set I := RingHom.ker π with hI
    let J : Ideal R := I ^ n
    let q : R →+* R ⧸ J := Ideal.Quotient.mk J
    have hJI : J ≤ RingHom.ker π := Ideal.pow_le_self h0
    let π₁ : R ⧸ J →+* R₀ := Ideal.Quotient.lift J π fun a ha => (RingHom.mem_ker).1 (hJI ha)
    have hfac : π = π₁.comp q := RingHom.ext fun _ => rfl
    have hπ₁ : Function.Surjective π₁ := fun y => by
      obtain ⟨x, hx⟩ := hπ y
      exact ⟨q x, hx⟩
    have hker₁ : RingHom.ker π₁ ^ n = ⊥ := by
      have hle : RingHom.ker π₁ ≤ I.map q := by
        intro z hz
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
        have hx : x ∈ I := RingHom.mem_ker.2 (RingHom.mem_ker.1 hz)
        exact Ideal.mem_map_of_mem q hx
      refine eq_bot_iff.2 ((Ideal.pow_right_mono hle n).trans ?_)
      rw [← Ideal.map_pow]
      exact (Ideal.map_quotient_self J).le
    have hsq : RingHom.ker q ^ 2 = ⊥ := by
      rw [Ideal.mk_ker, ← pow_mul]
      exact eq_bot_iff.2 ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
    have hcomp : spMap π = spMap π₁ ≫ spMap q := by
      rw [hfac]; simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    let f : Sp (R ⧸ J) ⟶ Sp R := spMap q
    let X₁ : Over (Sp (R ⧸ J)) := Over.mk (pullback.snd X.hom f)
    have hw' : β ≫ X.hom = (X₀.hom ≫ spMap π₁) ≫ f := by
      rw [hβ.w, hcomp, Category.assoc]
    let β₀ : X₀.left ⟶ X₁.left := pullback.lift β (X₀.hom ≫ spMap π₁) hw'
    have hβ₀ : β₀ ≫ pullback.fst X.hom f = β := pullback.lift_fst _ _ _
    have hpb : IsPullback β₀ X₀.hom X₁.hom (spMap π₁) := by
      refine IsPullback.of_right (h₁₂ := pullback.fst X.hom f) (h₂₂ := f) (v₁₃ := X.hom) ?_
        (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback X.hom f)
      rw [hβ₀, ← hcomp]
      exact hβ
    have hX₁ : LocallyOfFiniteType X₁.hom :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd X.hom f))
    let L₁ : LB X₁.left := L.pull (pullback.fst X.hom f)
    have hL₁ : L₁.IsLB := LB.isLB_pull hL _
    have hw₁ : LBIso L₀ (L₁.pull β₀) :=
      LBIso.trans hL₀ (LB.isLB_pull hL β) (LB.isLB_pull hL₁ β₀) hw
        (GlobalTheory.GenSpread.lbIso_pull_pull hL β₀ hβ₀.symm)
    have hA₁ : Out.RelAmple X₁ L₁ := ih (R ⧸ J) R₀ π₁ hπ₁ hker₁ X₁ X₀ β₀ hpb hX₁ L₁ L₀ hL₁ hL₀ hw₁ hA
    exact GlobalTheory.AmpleThickening.relAmple_of_sq_zero R (R ⧸ J) q Ideal.Quotient.mk_surjective hsq X X₁
      (pullback.fst X.hom f) (IsPullback.of_hasPullback X.hom f) hX L L₁ hL hL₁
      (lbIso_refl hL₁) hA₁

theorem relAmple_of_isNilDP : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (β : X₀.left ⟶ X.left), IsPullback β X₀.hom X.hom (spMap π) →
      LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L₀ : LB X₀.left), L.IsLB → L₀.IsLB → LBIso L₀ (L.pull β) →
      Out.RelAmple X₀ L₀ → Out.RelAmple X L := by
  intro R R₀ _ _ I κ hκ π hπ hker X X₀ β hβ hX L L₀ hL hL₀ hw hA
  obtain ⟨N, hN⟩ := exists_pow_eq_bot_of_isNilDP hκ
  exact relAmple_of_pow_eq_bot N R R₀ π hπ (hker ▸ hN) X X₀ β hβ hX L L₀ hL hL₀ hw hA

end GlobalTheory.AmpleNilThickening
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleLiftOfNilpotentDividedPowersThickeningStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_lift_of_nilpotentDividedPowers_thickening : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (β : X₀.left ⟶ X.left), IsPullback β X₀.hom X.hom (spMap π) →
      LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L₀ : LB X₀.left), L.IsLB → L₀.IsLB → LBIso L₀ (L.pull β) →
      Out.RelAmple X₀ L₀ → Out.RelAmple X L := by
  first | exact @GlobalTheory.AmpleNilThickening.relAmple_of_isNilDP | exact GlobalTheory.AmpleNilThickening.relAmple_of_isNilDP | (intros; apply GlobalTheory.AmpleNilThickening.relAmple_of_isNilDP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSequenceExtendCoords
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ParamFrame

theorem linearIndependent_toCotangent {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {m : ℕ} (r : Fin m → R) (hrsp : FinalTheorems.Rsp R m r) (hr : ∀ i, r i ∈ IsLocalRing.maximalIdeal R) :
    LinearIndependent (IsLocalRing.ResidueField R) (fun i =>
      ((IsLocalRing.maximalIdeal R).toCotangent ⟨r i, hr i⟩ : IsLocalRing.CotangentSpace R)) := by
  classical
  haveI : IsRegularLocalRing R := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [← hrsp.2, ← hrsp.1]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Set.finite_range r)
    have h2 : (Set.range r).ncard ≤ m := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])
    exact_mod_cast h1.trans h2
  have hfr : Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = m := by
    have := (IsRegularLocalRing.iff_finrank_cotangentSpace R).1 inferInstance
    rw [← hrsp.2] at this
    exact_mod_cast this
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp [hfr])
  have hsp : Submodule.span R (Set.range fun i => (⟨r i, hr i⟩ : IsLocalRing.maximalIdeal R)) = ⊤ := by
    apply Submodule.map_injective_of_injective (IsLocalRing.maximalIdeal R).injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
    exact hrsp.1
  rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff] at hsp
  rw [← Set.range_comp] at hsp
  exact hsp.ge


open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in
open GlobalTheory.AdaptedFrame in
theorem exists_frame_of_rsp : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (y : Y) (U : Y.affineOpens) (hy : y ∈ U.1) (c : ℕ) (a : Fin c → Γ(Y, U.1)), FinalTheorems.Rsp (Y.presheaf.stalk y) c (fun i => Y.presheaf.germ U.1 y hy (a i)) → ∃ (V : Y.Opens) (hV : V ≤ U.1) (_ : y ∈ V) (z : Fin n → Γ(Y, V)) (e : Fin c ↪ Fin n), (∀ j, z (e j) = resG Y hV (a j)) ∧ IsFrame (dOn q z) := by
  classical
  intro k _ _ X _ _ p n _ y O hyO m s hrsp
  let f : Fin m → X.presheaf.stalk y := fun i => X.presheaf.germ O.1 y hyO (s i)
  have hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
    fun i => hrsp.1 ▸ Ideal.subset_span ⟨i, rfl⟩
  have hli := linearIndependent_toCotangent f hrsp hf
  obtain ⟨U, x, b, hUO, hyU, hU, hb⟩ := exists_basis_dFun p n hyO
  let z₀ : Fin m → Γ(X, U) := fun j => resG X hUO (s j)
  have hz₀ (j : Fin m) : (X.presheaf.germ U y hyU).hom (z₀ j) = f j := by
    rw [germ_resG]

  let a : Fin m → Fin n → Γ(X, U) := fun j l => b.repr (dFun (algX p U) (z₀ j)) l
  have ha (j : Fin m) : dFun (algX p U) (z₀ j) = ∑ l, a j l • dFun (algX p U) (x l) := by
    conv_lhs => rw [← b.sum_repr (dFun (algX p U) (z₀ j))]
    simp only [hb, a]

  letI iΓ : Algebra k Γ(X, U) := (algX p U).toAlgebra
  letI iA : Algebra k (X.presheaf.stalk y) :=
    ((X.presheaf.germ U y hyU).hom.comp (algX p U)).toAlgebra
  letI iΓA : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hyU).hom.toAlgebra
  haveI : IsScalarTower k Γ(X, U) (X.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl
  haveI := formallySmooth_residueField (n := n) p hU y hyU rfl
  have hw := linearIndependent_tmul_D (k := k) f hf hli
  let ρ : Γ(X, U) →+* IsLocalRing.ResidueField (X.presheaf.stalk y) :=
    (IsLocalRing.residue (X.presheaf.stalk y)).comp (X.presheaf.germ U y hyU).hom
  let ab : Fin m → Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) := fun j l => ρ (a j l)
  have hab : LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk y)) ab := by
    let wx : Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) ⊗[X.presheaf.stalk y]
        Ω[(X.presheaf.stalk y)⁄k] :=
      fun l => 1 ⊗ₜ KaehlerDifferential.D k (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (x l))
    refine LinearIndependent.of_comp (Fintype.linearCombination _ wx) ?_
    have key : ⇑(Fintype.linearCombination (IsLocalRing.ResidueField (X.presheaf.stalk y)) wx) ∘ ab =
        fun j => (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)) ⊗ₜ[X.presheaf.stalk y]
          KaehlerDifferential.D k (X.presheaf.stalk y) (f j) := by
      funext j
      rw [Function.comp_apply, Fintype.linearCombination_apply, ← hz₀ j]
      have e1 := congrArg (KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y)) (ha j)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at e1
      change KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y)
        (KaehlerDifferential.D k Γ(X, U) (z₀ j)) = _ at e1
      rw [KaehlerDifferential.map_D] at e1
      change KaehlerDifferential.D k (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (z₀ j)) = _ at e1
      rw [e1, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul]
      change _ = 1 ⊗ₜ (a j l • KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y)
        (KaehlerDifferential.D k Γ(X, U) (x l)))
      rw [KaehlerDifferential.map_D, ← algebraMap_smul (X.presheaf.stalk y) (a j l),
        TensorProduct.tmul_smul, ← algebraMap_smul (IsLocalRing.ResidueField (X.presheaf.stalk y))]
      rfl
    rw [key]
    exact hw

  obtain ⟨e, he, hdet⟩ := GlobalTheory.T.exists_standard_basis_extension_det_ne_zero ab hab
  let z : Fin n → Γ(X, U) := Function.extend e z₀ x
  let c : Matrix (Fin n) (Fin n) Γ(X, U) :=
    Matrix.of (Function.extend e a (fun i => Pi.single i (1 : Γ(X, U))))
  have hdz (i : Fin n) : dFun (algX p U) (z i) = ∑ l, c i l • dFun (algX p U) (x l) := by
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      simp only [z, c, Matrix.of_apply, he.extend_apply]
      exact ha j
    · simp only [z, c, Matrix.of_apply, Function.extend_apply' _ _ _ hi]
      simp [Pi.single_apply]
  have hform : dOn p z = c.det • dOn p x := dForm_eq_det_smul z x c hdz
  have hρ : ρ c.det ≠ 0 := by
    have hm : c.map ρ = Matrix.of (Function.extend e ab
        (fun i => Pi.single i (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)))) := by
      ext i l
      by_cases hi : ∃ j, e j = i
      · obtain ⟨j, rfl⟩ := hi
        simp only [c, ab, Matrix.map_apply, Matrix.of_apply, he.extend_apply]
      · simp only [c, Matrix.map_apply, Matrix.of_apply, Function.extend_apply' _ _ _ hi]
        by_cases hil : l = i
        · subst hil
          simp
        · simp [hil]
    rw [RingHom.map_det]
    exact (congrArg Matrix.det hm).trans_ne hdet
  have hunit : IsUnit ((X.presheaf.germ U y hyU).hom c.det) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hρ
  have hyW : y ∈ X.basicOpen c.det := (X.mem_basicOpen c.det y hyU).2 hunit
  have hWU : X.basicOpen c.det ≤ U := X.basicOpen_le _
  refine ⟨X.basicOpen c.det, hWU.trans hUO, hyW, fun i => resG X hWU (z i), ⟨e, he⟩, fun j => ?_, ?_⟩
  · simp only [z, z₀, Function.Embedding.coeFn_mk, he.extend_apply]
    exact resG_resG _ _ _
  · have hx : IsFrame (dOn p x) := ⟨hU, isFreeGen_dForm x b hb⟩
    have h1 := hx.res (hU.basicOpen c.det) hWU
    refine ⟨hU.basicOpen c.det, ?_⟩
    rw [← resForm_dOn hWU, hform, resForm_smul]
    exact h1.gen.smul_iff.2 (RingedSpace.isUnit_res_basicOpen X.toRingedSpace c.det)

end GlobalTheory.ParamFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingAdd
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FactorAdd

open GlobalTheory.CechPic

variable {S S' : Scheme.{0}}

theorem comp_psum {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (u : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ G))
    (x' : Fin n → (T' ⟶ G)) (h : ∀ i, u ≫ x i = x' i) (I : Finset (Fin n)) :
    u.left ≫ (psum G x I).left = (psum G x' I).left :=
  congrArg (fun q => q.left) ((psum_hom (preHom u) x I).trans (congrArg (fun q => psum G q I) (funext h)))

theorem pull_lam {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (h : (abelian₂ G L).IsLB)
    (x y : T ⟶ G) :
    pull (lift x y : T ⟶ G2 G).left (cls (abelian₂ G L) h) =
      pull (x * y).left (cls L hL) - pull x.left (cls L hL) - pull y.left (cls L hL) +
        pull (1 : T ⟶ G).left (cls L hL) := by
  have e := cls_linComb hL (K := ULift.{0} (Finset (Fin 2))) (fun I => (psum G (x2 G) I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) h
  refine (congrArg (pull (lift x y : T ⟶ G2 G).left) e).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (Fintype.sum_equiv Equiv.ulift _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum G ![x, y] I).left (cls L hL)) fun I => ?_).trans ?_
  · rw [map_zsmul, ← pull_comp, comp_psum (lift x y : T ⟶ G2 G) (x2 G) ![x, y] (fun i => by fin_cases i <;> simp [x2])]
    rfl
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₃ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [neg_smul, one_smul]
  abel

theorem cube {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) (x x' y : T ⟶ G) :
    pull (x * x' * y).left (cls L.L L.isLB) - pull (x * x').left (cls L.L L.isLB) - pull (x * y).left (cls L.L L.isLB)
      - pull (x' * y).left (cls L.L L.isLB) + pull x.left (cls L.L L.isLB) + pull x'.left (cls L.L L.isLB)
      + pull y.left (cls L.L L.isLB) - pull (1 : T ⟶ G).left (cls L.L L.isLB) = 0 := by
  have h : (Theta G L.L).IsLB := LB.isLB_linComb L.isLB _ _
  have z : cls (Theta G L.L) h = 0 := (cls_eq_zero_iff h).2 ⟨c.t, c.isGen⟩
  have e := cls_linComb L.isLB (K := ULift.{0} (Finset (Fin 3))) (fun I => (psum G (x3 G) I.down).left)
    (fun I => (-1) ^ (3 - I.down.card)) h
  have e' := (congrArg (pull (lift x (lift x' y) : T ⟶ G3 G).left) (e.symm.trans z)).trans (map_zero _)
  refine Eq.trans (Eq.symm ?_) e'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (Fintype.sum_equiv Equiv.ulift _
    (fun I => ((-1 : ℤ) ^ (3 - I.card)) • pull (psum G ![x, x', y] I).left (cls L.L L.isLB)) fun I => ?_).trans ?_
  · rw [map_zsmul, ← pull_comp, comp_psum (lift x (lift x' y) : T ⟶ G3 G) (x3 G) ![x, x', y]
      (fun i => by fin_cases i <;> simp [x3])]
    rfl
  rw [show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have p₀ : psum G ![x, x', y] ∅ = 1 := rfl
  have p₁ : psum G ![x, x', y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, x', y] {1} = x' := _root_.mul_one x'
  have p₃ : psum G ![x, x', y] {2} = y := _root_.mul_one y
  have p₄ : psum G ![x, x', y] {0, 1} = x * x' := congrArg (x * ·) (_root_.mul_one x')
  have p₅ : psum G ![x, x', y] {0, 2} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have p₆ : psum G ![x, x', y] {1, 2} = x' * y := congrArg (x' * ·) (_root_.mul_one y)
  have p₇ : psum G ![x, x', y] {0, 1, 2} = x * x' * y :=
    (congrArg (fun q => x * (x' * q)) (_root_.mul_one y)).trans (_root_.mul_assoc _ _ _).symm
  have q₀ : (-1 : ℤ) ^ (3 - (∅ : Finset (Fin 3)).card) = -1 := by decide
  have q₁ : ∀ i : Fin 3, (-1 : ℤ) ^ (3 - ({i} : Finset (Fin 3)).card) = 1 := by decide
  have q₄ : (-1 : ℤ) ^ (3 - ({0, 1} : Finset (Fin 3)).card) = -1 := by decide
  have q₅ : (-1 : ℤ) ^ (3 - ({0, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₆ : (-1 : ℤ) ^ (3 - ({1, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₇ : (-1 : ℤ) ^ (3 - ({0, 1, 2} : Finset (Fin 3)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, p₄, p₅, p₆, p₇, q₀, q₁, q₁, q₁, q₄, q₅, q₆, q₇]
  simp only [neg_smul, one_smul]
  abel

theorem lam_add {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) (h : (abelian₂ G L.L).IsLB)
    (x x' y : T ⟶ G) :
    pull (lift (x * x') y : T ⟶ G2 G).left (cls (abelian₂ G L.L) h) - pull (lift x y : T ⟶ G2 G).left (cls (abelian₂ G L.L) h)
      - pull (lift x' y : T ⟶ G2 G).left (cls (abelian₂ G L.L) h) = 0 := by
  rw [pull_lam L.isLB, pull_lam L.isLB, pull_lam L.isLB, ← cube c x x' y]
  abel

theorem lift_square {G : Over S} {H : Over S'} [GrpObj G] [GrpObj H] {f : S' ⟶ S} {φ : H.left ⟶ G.left}
    (hp : IsGrpPullback H G f φ) {κ : (G2 H).left ⟶ (G2 G).left} (hκ : Geo.Tor.IsSquare (G' := H) (G := G) φ κ)
    {T : Over S'} (x y : T ⟶ H) :
    (lift x y : T ⟶ G2 H).left ≫ κ = (lift (pushHom hp T x) (pushHom hp T y) : Over.mk (T.hom ≫ f) ⟶ G2 G).left := by
  have A : ∀ (p q : Over.mk (T.hom ≫ f) ⟶ G), p.left = x.left ≫ φ → q.left = y.left ≫ φ →
      (lift x y : T ⟶ G2 H).left ≫ κ = (lift p q : Over.mk (T.hom ≫ f) ⟶ G2 G).left := by
    intro p q hp' hq'
    apply pullback.hom_ext
    · show (_ ≫ κ) ≫ (fst G G).left = (lift p q ≫ fst G G).left
      rw [lift_fst, hp', Category.assoc, hκ.1, ← Category.assoc, ← Over.comp_left, lift_fst]
    · show (_ ≫ κ) ≫ (snd G G).left = (lift p q ≫ snd G G).left
      rw [lift_snd, hq', Category.assoc, hκ.2, ← Category.assoc, ← Over.comp_left, lift_snd]
  exact A _ _ rfl rfl

theorem exists_gen {G G' : Over S} {H : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj H]
    {L : RigLB G'} (c : CubicalStr G' L) (a b : G ⟶ G') [IsMonHom a] {f : S' ⟶ S} {φ : H.left ⟶ G.left}
    (hp : IsGrpPullback H G f φ) {κ : (G2 H).left ⟶ (G2 G).left} (hκ : Geo.Tor.IsSquare (G' := H) (G := G) φ κ)
    {T : Over S'} (x x' y : T ⟶ H) (ψ : Fin 3 → (T.left ⟶ (G2 H).left))
    (h₀ : ψ 0 = (lift (x * x') y : T ⟶ G2 H).left) (h₁ : ψ 1 = (lift x y : T ⟶ G2 H).left)
    (h₂ : ψ 2 = (lift x' y : T ⟶ G2 H).left) :
    ∃ u : LB.Gen (LB.LinComb (((abelian₂ G' L.L).pull (lift (fst G G ≫ a) (snd G G ≫ b) : G2 G ⟶ G2 G').left).pull κ)
      (K := Fin 3) ψ ![1, -1, -1]), u.IsGen := by
  have hΛ : (abelian₂ G' L.L).IsLB := LB.isLB_linComb L.isLB _ _
  have hP := pull_isLB (pull_isLB hΛ (lift (fst G G ≫ a) (snd G G ≫ b) : G2 G ⟶ G2 G').left) κ
  have key : ∀ p q : T ⟶ H, pull (lift p q : T ⟶ G2 H).left (cls _ hP) =
      pull (lift (pushHom hp T p ≫ a) (pushHom hp T q ≫ b) : Over.mk (T.hom ≫ f) ⟶ G2 G').left (cls _ hΛ) := by
    intro p q
    rw [cls_pull (pull_isLB hΛ _), cls_pull hΛ, ← pull_comp, ← pull_comp, lift_square hp hκ]
    refine congrArg (fun m => pull m (cls _ hΛ)) ?_
    refine congrArg (fun m : Over.mk (T.hom ≫ f) ⟶ G2 G' => m.left)
      (show lift (pushHom hp T p) (pushHom hp T q) ≫ lift (fst G G ≫ a) (snd G G ≫ b) = _ from ?_)
    simp
  refine (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).1 ?_
  rw [cls_linComb hP, Fin.sum_univ_three, h₀, h₁, h₂, key, key, key, map_mul, MonObj.mul_comp]
  have e := lam_add c hΛ (pushHom hp T x ≫ a) (pushHom hp T x' ≫ a) (pushHom hp T y ≫ b)
  refine Eq.trans ?_ e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    one_smul, neg_smul, sub_eq_add_neg]

end GlobalTheory.Mum.FactorAdd

theorem GlobalTheory.Mum.factorPairing_add : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀) (K := Fin 3) ![(lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) * (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1, -1]), u.IsGen := by
  intro R _ _ _ _ D D' F A' G' _ _ _ U' oA oG _ G _ _ _ inc pr hinc _ _ _ κ₀ hκ
  exact GlobalTheory.Mum.FactorAdd.exists_gen U'.cubG inc (inc ≫ oG.act F.f) (isGrpPullback_pullback G (jK R)) hκ
    (fst _ _) (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _) _ rfl rfl
    (by rw [lift_comp_fst_snd]; rfl)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorContractionTwoCochainProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorContractionTwoCochainProduct
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.ContrMor

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]
  {D : Type} [CommRing D] [Algebra R D] {D' : Type} [CommRing D'] [Algebra R D']

omit [GrpObj A] in
theorem specOverOfAlgHom_pointWithZeroSecondCoord (φ : D →ₐ[R] D') (x : Pt A D) :
    spOver φ ≫ pt0 B x = pt0 B (spOver φ ≫ x : Pt A D') := by
  simp [pt0, comp_lift, MonObj.comp_one]

omit [GrpObj A] in
theorem spOver_fst_ptV (v : epsR R ⟶ B) (hv : IsTangent v) (x : Pt A D) :
    spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x = pt0 B x := by
  have k : spOver (TrivSqZeroExt.fstHom R D D) ≫ spOver (EpsWeil.epsMap R D) =
      toUnit _ ≫ GrpTangent.epsZero R := by
    refine Over.OverMorphism.ext ?_
    rw [spOver_comp, PDiv.spOver_left, Over.comp_left, Over.toUnit_left]
    refine Eq.trans (congrArg spMap (RingHom.ext fun a ↦ ?_)) (Cris.spMap_comp
      (TrivSqZeroExt.fstHom R R R).toRingHom (algebraMap R D))
    simp [EpsWeil.epsMap, DualNumber.lift_apply_apply, TrivSqZeroExt.algebraMap_eq_inl']
  ext1
  · simp only [ptV, pt0, comp_lift, lift_fst, ← Category.assoc, spOver_comp]
    rw [show (TrivSqZeroExt.fstHom R D D).comp (TrivSqZeroExt.inlAlgHom R D D) = AlgHom.id R D from
      AlgHom.ext fun _ ↦ rfl, PDiv.spOver_id, Category.id_comp]
  · simp only [ptV, pt0, comp_lift, lift_snd]
    rw [← Category.assoc, k, Category.assoc, (GrpTangent.isTangent_iff v).1 hv, MonObj.comp_one]

omit [GrpObj A] [GrpObj B] in
theorem spOver_epsHom_ptV (v : epsR R ⟶ B) (φ : D →ₐ[R] D') (x : Pt A D) :
    spOver (epsHom φ) ≫ ptV v x = ptV v (spOver φ ≫ x : Pt A D') := by
  ext1
  · simp only [ptV, comp_lift, lift_fst, ← Category.assoc, spOver_comp]
    congr 2
    ext c <;> simp [epsHom]
  · simp only [ptV, comp_lift, lift_snd, ← Category.assoc, spOver_comp]
    congr 2
    ext <;> simp only [AlgHom.comp_apply, EpsWeil.epsMap, epsHom, DualNumber.lift_apply_eps]

def sHom (x : Pt A D) : trivAt (pt0 B x) ⟶ thickAt B x :=
  (epsExt R D).secHom (Pt.w (pt0 B x)) (epsExt R D).i (epsExt R D).π_i

def iHom (v : epsR R ⟶ B) (hv : IsTangent v) (x : Pt A D) : trivAt (ptV v x) ⟶ thickAt B x :=
  Thick.trivHom (T := thickAt B x) (AlgHom.id R (DualNumber D)) (by
    have := congrArg Over.Hom.left (spOver_fst_ptV v hv x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

def aHom (φ : D →ₐ[R] D') (x : Pt A D) :
    trivAt (pt0 B x) ⟶ trivAt (pt0 B (spOver φ ≫ x : Pt A D')) :=
  Thick.trivHom φ (by
    have := congrArg Over.Hom.left (specOverOfAlgHom_pointWithZeroSecondCoord (B := B) φ x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

def bHom (v : epsR R ⟶ B) (φ : D →ₐ[R] D') (x : Pt A D) :
    trivAt (ptV v x) ⟶ trivAt (ptV v (spOver φ ≫ x : Pt A D')) :=
  Thick.trivHom (epsHom φ) (by
    have := congrArg Over.Hom.left (spOver_epsHom_ptV v φ x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

def τHom (φ : D →ₐ[R] D') (x : Pt A D) :
    thickAt B x ⟶ thickAt B (spOver φ ≫ x : Pt A D') :=
  (epsExt R D).thickHom (epsExt R D') (epsHom φ) φ
    (fun c ↦ by simp [epsHom, DualNumber.lift_apply_apply]) _ _ (by
    have := congrArg Over.Hom.left (specOverOfAlgHom_pointWithZeroSecondCoord (B := B) φ x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

end GlobalTheory.PtExt.ContrMor

namespace GlobalTheory.PtExt.ContrMor

theorem exists_contr : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (v : epsR R ⟶ B), IsTangent v →
    (∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt A D),
      let y : Pt A D' := spOver φ ≫ x
      ∃ (s : trivAt (pt0 B x) ⟶ thickAt B x) (i : trivAt (ptV v x) ⟶ thickAt B x)
        (s' : trivAt (pt0 B y) ⟶ thickAt B y) (i' : trivAt (ptV v y) ⟶ thickAt B y)
        (a : trivAt (pt0 B x) ⟶ trivAt (pt0 B y)) (b : trivAt (ptV v x) ⟶ trivAt (ptV v y))
        (τ : thickAt B x ⟶ thickAt B y),
        (∀ r, s.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i.φ r = r) ∧
        (∀ r, s'.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i'.φ r = r) ∧
        (∀ r, a.φ r = φ r) ∧ (∀ r, b.φ r = epsHom φ r) ∧ (∀ r, τ.φ r = epsHom φ r)) ∧
    ∀ z : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), ∃ κ : Fn1 A, IsContr z v κ := by
  intro R _ A B _ _ v hv
  refine ⟨fun D _ _ D' _ _ φ x ↦ ⟨sHom x, iHom v hv x, sHom _, iHom v hv _, aHom φ x, bHom v φ x, τHom φ x,
    fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩, fun z ↦ ?_⟩
  refine ⟨fun D _ _ D' _ _ φ x ↦ TrivSqZeroExt.snd (R := D')
    (z _ _ _ (sHom x) (τHom φ x) - z _ _ _ (aHom φ x) (sHom _) - z _ _ _ (iHom v hv x) (τHom φ x) +
      z _ _ _ (bHom v φ x) (iHom v hv _)), ?_⟩
  intro D _ _ D' _ _ φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ
  obtain rfl : s = sHom x := Thick.hom_ext fun r ↦ (hs r).trans rfl
  obtain rfl : i = iHom v hv x := Thick.hom_ext fun r ↦ (hi r).trans rfl
  obtain rfl : s' = sHom _ := Thick.hom_ext fun r ↦ (hs' r).trans rfl
  obtain rfl : i' = iHom v hv _ := Thick.hom_ext fun r ↦ (hi' r).trans rfl
  obtain rfl : a = aHom φ x := Thick.hom_ext fun r ↦ (ha r).trans rfl
  obtain rfl : b = bHom v φ x := Thick.hom_ext fun r ↦ (hb r).trans rfl
  obtain rfl : τ = τHom φ x := Thick.hom_ext fun r ↦ (hτ r).trans rfl
  rfl

end GlobalTheory.PtExt.ContrMor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorContractionTwoCochainProductStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangentVector_contraction_twoCochain_product :
    ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (v : epsR R ⟶ B), IsTangent v →
    (∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt A D),
      let y : Pt A D' := spOver φ ≫ x
      ∃ (s : trivAt (pt0 B x) ⟶ thickAt B x) (i : trivAt (ptV v x) ⟶ thickAt B x)
        (s' : trivAt (pt0 B y) ⟶ thickAt B y) (i' : trivAt (ptV v y) ⟶ thickAt B y)
        (a : trivAt (pt0 B x) ⟶ trivAt (pt0 B y)) (b : trivAt (ptV v x) ⟶ trivAt (ptV v y))
        (τ : thickAt B x ⟶ thickAt B y),
        (∀ r, s.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i.φ r = r) ∧
        (∀ r, s'.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i'.φ r = r) ∧
        (∀ r, a.φ r = φ r) ∧ (∀ r, b.φ r = epsHom φ r) ∧ (∀ r, τ.φ r = epsHom φ r)) ∧
    ∀ z : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), ∃ κ : Fn1 A, IsContr z v κ :=
  GlobalTheory.PtExt.ContrMor.exists_contr
end
end
