module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrCongrOfResidueFixedByDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBasisSectionsAbelianSchemeOverDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixDescentUnramifiedDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExtendsUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGoodReductionOfUnramifiedAbelianSchemeModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldValuationRingStrictlyHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGoodReductionOfManyRationalTorsionPoints

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.HasGoodReductionOfInfiniteTorsionUnramified
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.HasGoodReductionOfInertiaFixed
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.ExistsSchemeModelDescentUnramified
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.ExistsCompatibleProjectiveEmbeddings
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.ExistsVeryAmpleFamiliesStableMatrix
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.TwistedSectionsExtend
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.TwistIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit.Nos.TwistIsomorphismSections

private theorem appLE_appLE {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (k : Z ⟶ X) (h : g ≫ f = k)
    {U : X.Opens} {V : Y.Opens} {W : Z.Opens} (e : V ≤ f ⁻¹ᵁ U) (e' : W ≤ g ⁻¹ᵁ V) (e'' : W ≤ k ⁻¹ᵁ U)
    (a : Γ(X, U)) :
    (g.appLE V W e').hom ((f.appLE U V e).hom a) = (k.appLE U W e'').hom a := by
  subst h
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]

private theorem isGen_iff_val {X : Scheme.{0}} {A B : LB X} (w : LB.Iso A B) :
    w.IsGen ↔ ∀ (p : B.ι) (q : A.ι) (p' : B.ι) (q' : A.ι),
      resG X (inf_le_left : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ _)
          (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q))).val *
        resG X (inf_le_inf inf_le_right inf_le_right : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ _)
          (A.g q q').val =
      resG X (inf_le_inf inf_le_left inf_le_left : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ _)
          (B.g p p').val *
        resG X (inf_le_right : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ _)
          (@id (Γ(X, B.U p' ⊓ A.U q')ˣ) (w.s (p', q'))).val := by
  have key : ∀ (p : B.ι) (q : A.ι) (p' : B.ι) (q' : A.ι),
      (res (inf_le_left : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ _)
          (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q))) =
        res (inf_le_inf inf_le_left inf_le_left : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ _) (B.g p p') *
          (res (inf_le_inf inf_le_right inf_le_right : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ _)
            (A.g q q'))⁻¹ *
          res (inf_le_right : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ _)
            (@id (Γ(X, B.U p' ⊓ A.U q')ˣ) (w.s (p', q')))) ↔ _ := fun p q p' q' => by
    rw [mul_right_comm, eq_mul_inv_iff_mul_eq, Units.ext_iff, Units.val_mul, Units.val_mul]
  exact ⟨fun h p q p' q' => (key p q p' q').1 (h (p, q) (p', q')),
    fun h p p' => (key p.1 p.2 p'.1 p'.2).2 (h p.1 p.2 p'.1 p'.2)⟩

private theorem appTop_cst {X Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (β : Y ⟶ X)
    (f : X ⟶ Sp R) (f' : Y ⟶ Sp R') (c : R →+* R') (h : β ≫ f = f' ≫ spMap c) (r : R) :
    β.appTop (GlobalTheory.AbLaw.cst f ⊤ r) = GlobalTheory.AbLaw.cst f' ⊤ (c r) := by
  simp only [GlobalTheory.AbLaw.cst, RingHom.comp_apply, GlobalTheory.AbLaw.rs_self]
  have h1 := congrArg (fun φ : Y ⟶ Sp R => φ.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) h
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h1
  rw [h1]
  congr 1
  have h2 := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom c))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2.symm

private theorem sum_f {X : Scheme.{0}} {L : LB X} {J : Type} (S : Finset J) (s : J → L.Sec) (i : L.ι) :
    (∑ k ∈ S, s k).f i = ∑ k ∈ S, (s k).f i := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.LB.add_f, ih]

private theorem secPull_f {X Y : Scheme.{0}} {L : LB X} (s : L.Sec) (f : Y ⟶ X) (j : (L.pull f).ι) :
    (GlobalTheory.Cartier.secPull s f).f j =
      (f.appLE _ _ (GlobalTheory.LB.pull_U_le f j)).hom (s.f (j PUnit.unit)) := rfl

private theorem pull_g_val {X Y : Scheme.{0}} {L : LB X} (f : Y ⟶ X) (i j : (L.pull f).ι) :
    ((L.pull f).g i j).val =
      (f.appLE (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) _
        (inf_le_inf (GlobalTheory.LB.pull_U_le f i) (GlobalTheory.LB.pull_U_le f j))).hom
        (L.g (i PUnit.unit) (j PUnit.unit)).val :=
  (GlobalTheory.LB.resG_self le_rfl _).symm.trans (GlobalTheory.LB.resG_pull_g f i j le_rfl)

private theorem ΓSpec_spMap {K : Type} [CommRing K] (σ : K →+* K) (b : Γ(Sp K, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (((spMap σ).appLE ⊤ ⊤ le_top).hom b) =
      σ ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom b) := by
  have h2 := congrArg (fun φ => φ.hom b) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [← h2]
  congr 1

private theorem transport {Y : Scheme.{0}} (ρ : Y ⟶ Y) {A A' B : LB Y} (τ : A'.ι → A.ι)
    (lA : ∀ i, A'.U i ≤ ρ ⁻¹ᵁ A.U (τ i)) (lB : ∀ n, B.U n ≤ ρ ⁻¹ᵁ B.U n)
    (gA : ∀ i j, (A'.g i j).val = (ρ.appLE (A.U (τ i) ⊓ A.U (τ j)) (A'.U i ⊓ A'.U j)
      (inf_le_inf (lA i) (lA j))).hom (A.g (τ i) (τ j)).val)
    (gB : ∀ i j, (B.g i j).val = (ρ.appLE (B.U i ⊓ B.U j) (B.U i ⊓ B.U j)
      (inf_le_inf (lB i) (lB j))).hom (B.g i j).val)
    (w : LB.Iso A B) (hw : w.IsGen) :
    ∃ w₁ : LB.Iso A' B, w₁.IsGen ∧
      (∀ (a : A.Sec) (a' : A'.Sec) (b b' : B.Sec),
        (∀ i, a'.f i = (ρ.appLE _ _ (lA i)).hom (a.f (τ i))) →
        (∀ n, b'.f n = (ρ.appLE _ _ (lB n)).hom (b.f n)) →
        GlobalTheory.Cartier.SecMaps w a b → GlobalTheory.Cartier.SecMaps w₁ a' b') ∧
      ∀ n i, (@id (Γ(Y, B.U n ⊓ A'.U i)ˣ) (w₁.s (n, i))).val =
        (ρ.appLE (B.U n ⊓ A.U (τ i)) (B.U n ⊓ A'.U i) (inf_le_inf (lB n) (lA i))).hom
          (@id (Γ(Y, B.U n ⊓ A.U (τ i))ˣ) (w.s (n, τ i))).val := by
  have lAB : ∀ n i, B.U n ⊓ A'.U i ≤ ρ ⁻¹ᵁ (B.U n ⊓ A.U (τ i)) := fun n i => inf_le_inf (lB n) (lA i)
  let w₁ : LB.Iso A' B :=
    ⟨fun p => Units.map (ρ.appLE _ _ (lAB p.1 p.2)).hom.toMonoidHom (w.s (p.1, τ p.2))⟩
  have hw₁ : ∀ n i, (@id (Γ(Y, B.U n ⊓ A'.U i)ˣ) (w₁.s (n, i))).val =
        (ρ.appLE (B.U n ⊓ A.U (τ i)) (B.U n ⊓ A'.U i) (lAB n i)).hom
          (@id (Γ(Y, B.U n ⊓ A.U (τ i))ˣ) (w.s (n, τ i))).val := fun _ _ => rfl
  refine ⟨w₁, (isGen_iff_val w₁).2 fun n i n' i' => ?_, fun a a' b b' ha hb H p => ?_, hw₁⟩
  · have l : B.U n ⊓ A'.U i ⊓ (B.U n' ⊓ A'.U i') ≤
        ρ ⁻¹ᵁ (B.U n ⊓ A.U (τ i) ⊓ (B.U n' ⊓ A.U (τ i'))) := inf_le_inf (lAB n i) (lAB n' i')
    have e := congrArg (ρ.appLE _ _ l).hom ((isGen_iff_val w).1 hw n (τ i) n' (τ i'))
    rw [map_mul, map_mul, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG,
      GlobalTheory.LB.appLE_resG] at e
    rw [hw₁, hw₁, gA, gB, GlobalTheory.LB.resG_appLE, GlobalTheory.LB.resG_appLE]
    erw [GlobalTheory.LB.resG_appLE, GlobalTheory.LB.resG_appLE]
    exact e
  · obtain ⟨n, i⟩ := p
    have e := congrArg (ρ.appLE _ _ (lAB n i)).hom (H (n, τ i))
    rw [map_mul, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG] at e
    rw [hw₁, ha, hb, GlobalTheory.LB.resG_appLE, GlobalTheory.LB.resG_appLE]
    exact e

end UpperTheory.Lit.Nos.TwistIsomorphismSections

open UpperTheory.Lit.Nos.TwistIsomorphismSections in
theorem UpperTheory.Lit.Nos.twistIso :
    ∀ {X₁ X₂ Y : Scheme.{0}} {K' : Type} [Field K'] (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (q : Y ⟶ Sp K') (ρ : Y ⟶ Y) (φ : X₁ ⟶ X₁) (σ : K' →+* K'), f₁ ≫ φ = ρ ≫ f₁ → ρ ≫ f₂ = f₂ → ρ ≫ q = q ≫ spMap σ → L₁.IsLB → L₂.IsLB → ∀ (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)), w.IsGen → ∃ w₁ : LB.Iso ((L₁.pull φ).pull f₁) (L₂.pull f₂), w₁.IsGen ∧ (∀ (n : ℕ) (s : Fin n → L₂.Sec) (u : L₁.Sec) (c : Fin n → K'), GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull u f₁) (∑ k, GlobalTheory.AbLaw.cst q ⊤ (c k) • GlobalTheory.Cartier.secPull (s k) f₂) → GlobalTheory.Cartier.SecMaps w₁ (GlobalTheory.Cartier.secPull (GlobalTheory.Cartier.secPull u φ) f₁) (∑ k, GlobalTheory.AbLaw.cst q ⊤ (σ (c k)) • GlobalTheory.Cartier.secPull (s k) f₂)) ∧ (∀ x : Sp K' ⟶ Y, x ≫ ρ = spMap σ ≫ x → ∀ (n : (L₂.pull f₂).ι) (i : ((L₁.pull φ).pull f₁).ι) (h : ⊤ ≤ x ⁻¹ᵁ ((L₂.pull f₂).U n ⊓ ((L₁.pull φ).pull f₁).U i)) (h' : ⊤ ≤ x ⁻¹ᵁ ((L₂.pull f₂).U n ⊓ (L₁.pull f₁).U (fun _ => i PUnit.unit PUnit.unit))), (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h).hom (w₁.s (n, i)).val) = σ ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h').hom (w.s (n, fun _ => i PUnit.unit PUnit.unit)).val))) := by
  intro X₁ X₂ Y K' _ L₁ L₂ f₁ f₂ q ρ φ σ h₁ h₂ hq _ _ w hw
  have lB : ∀ n : (L₂.pull f₂).ι, (L₂.pull f₂).U n ≤ ρ ⁻¹ᵁ (L₂.pull f₂).U n := fun n => by
    rw [GlobalTheory.LB.pull_U, ← Scheme.Hom.comp_preimage, h₂]
  let τ : ((L₁.pull φ).pull f₁).ι → (L₁.pull f₁).ι := fun i _ => i PUnit.unit PUnit.unit
  have lA : ∀ i : ((L₁.pull φ).pull f₁).ι, ((L₁.pull φ).pull f₁).U i ≤
      ρ ⁻¹ᵁ (L₁.pull f₁).U (τ i) := fun i => by
    rw [GlobalTheory.LB.pull_U f₁ (τ i), ← Scheme.Hom.comp_preimage, ← h₁, Scheme.Hom.comp_preimage]
    exact (GlobalTheory.LB.pull_U_le f₁ i).trans (f₁.preimage_mono (GlobalTheory.LB.pull_U_le φ _))
  obtain ⟨w₁, hg, hs, hv⟩ := transport ρ τ lA lB (fun i j => by
      have l : ((L₁.pull φ).pull f₁).U i ⊓ ((L₁.pull φ).pull f₁).U j ≤
          (f₁ ≫ φ) ⁻¹ᵁ (L₁.U (i PUnit.unit PUnit.unit) ⊓ L₁.U (j PUnit.unit PUnit.unit)) :=
        inf_le_inf ((GlobalTheory.LB.pull_U_le f₁ i).trans (f₁.preimage_mono (GlobalTheory.LB.pull_U_le φ _)))
          ((GlobalTheory.LB.pull_U_le f₁ j).trans (f₁.preimage_mono (GlobalTheory.LB.pull_U_le φ _)))
      refine (pull_g_val f₁ i j).trans ((congrArg _ (pull_g_val φ _ _)).trans
        ((appLE_appLE f₁ φ _ rfl _ _ l _).trans ?_))
      exact ((congrArg _ (pull_g_val f₁ (τ i) (τ j))).trans (appLE_appLE ρ f₁ _ h₁.symm _ _ l _)).symm)
    (fun i j => (pull_g_val f₂ i j).trans
      ((congrArg _ (pull_g_val f₂ i j)).trans (appLE_appLE ρ f₂ _ h₂ _ _ _ _)).symm) w hw
  refine ⟨w₁, hg, fun m s u c H => hs _ _ _ _ (fun i => ?_) (fun n => ?_) H, fun x hx n i h h' => ?_⟩
  · have l : ((L₁.pull φ).pull f₁).U i ≤ (f₁ ≫ φ) ⁻¹ᵁ L₁.U (i PUnit.unit PUnit.unit) :=
      (GlobalTheory.LB.pull_U_le f₁ i).trans (f₁.preimage_mono (GlobalTheory.LB.pull_U_le φ _))
    exact (appLE_appLE f₁ φ _ rfl (GlobalTheory.LB.pull_U_le φ _) (GlobalTheory.LB.pull_U_le f₁ i) l _).trans
      (appLE_appLE ρ f₁ _ h₁.symm (GlobalTheory.LB.pull_U_le f₁ (τ i)) (lA i) l _).symm
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [sum_f, sum_f, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [GlobalTheory.LB.smul_f, GlobalTheory.LB.smul_f, map_mul, secPull_f,
        appLE_appLE ρ f₂ _ h₂ _ _ (GlobalTheory.LB.pull_U_le f₂ n),
        GlobalTheory.LB.appLE_resG, ← appTop_cst ρ q q σ hq]
      rfl
  · have e : (x.appLE _ ⊤ h).hom (w₁.s (n, i)).val =
        ((spMap σ).appLE ⊤ ⊤ le_top).hom ((x.appLE _ ⊤ h').hom (w.s (n, τ i)).val) := by
      have l : ⊤ ≤ (x ≫ ρ) ⁻¹ᵁ ((L₂.pull f₂).U n ⊓ (L₁.pull f₁).U (τ i)) :=
        h.trans (x.preimage_mono (inf_le_inf (lB n) (lA i)))
      exact (congrArg _ (hv n i)).trans ((appLE_appLE x ρ _ rfl _ _ l _).trans
        (appLE_appLE (spMap σ) x _ hx.symm _ _ l _).symm)
    exact (congrArg _ e).trans (ΓSpec_spMap σ _)
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.IntegralSec
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Cartier in
private theorem UpperTheory.Lit.Nos.IntegralSec.sec_of_rel {X Y : Scheme.{0}} (f : Y ⟶ X) (P M : LB X) (N : LB Y)
    (hP : P.IsLB) (hM : M.IsLB) (w : LB.Iso (M.pull f) N) (w₁ : LB.Iso (P.pull f) N)
    (v : LB.Iso P M) (hv : v.IsGen) (g₀ : Γ(X, ⊤))
    (H : ∀ (n : N.ι) (i : P.ι) (m : M.ι) (V : Y.Opens) (h₁ : V ≤ N.U n ⊓ (P.pull f).U (fun _ => i))
      (h₂ : V ≤ N.U n ⊓ (M.pull f).U (fun _ => m)) (h₃ : V ≤ f ⁻¹ᵁ (M.U m ⊓ P.U i)),
      resG Y h₁ (@id (Γ(Y, N.U n ⊓ (P.pull f).U (fun _ => i))ˣ) (w₁.s (n, fun _ => i))).val =
        resG Y (le_top : V ≤ f ⁻¹ᵁ ⊤) ((f.app ⊤).hom g₀) *
          resG Y h₃ ((f.app _).hom (@id (Γ(X, M.U m ⊓ P.U i)ˣ) (v.s (m, i))).val) *
          resG Y h₂ (@id (Γ(Y, N.U n ⊓ (M.pull f).U (fun _ => m))ˣ) (w.s (n, fun _ => m))).val)
    (t : P.Sec) (b : N.Sec) (hb : SecMaps w₁ (secPull t f) b) :
    ∃ t' : M.Sec, SecMaps w (secPull t' f) b := by
  obtain ⟨u, hu⟩ := GlobalTheory.exists_secMaps hP hM v hv t
  let t' : M.Sec := ⟨fun m => resG X le_top g₀ * u.f m, fun m m' => by
    have e := u.compat m m'
    change resG X _ _ = _ * resG X _ _ at e ⊢
    rw [map_mul, map_mul, resG_resG, resG_resG, e, mul_left_comm]⟩
  refine ⟨t', ?_⟩
  rintro ⟨n, j⟩
  obtain ⟨m, rfl⟩ : ∃ m : M.ι, j = fun _ => m := ⟨j ⟨⟩, rfl⟩
  refine ext_germ fun y hy => ?_
  obtain ⟨i, hi⟩ := LB.mem_of_cover hP (f y)
  let V : Y.Opens := N.U n ⊓ (M.pull f).U (fun _ => m) ⊓ (P.pull f).U (fun _ => i)
  have hyV : y ∈ V := ⟨hy, (pull_U P f (fun _ => i)).ge hi⟩
  have h₂ : V ≤ N.U n ⊓ (M.pull f).U (fun _ => m) := inf_le_left
  have hn : V ≤ N.U n := inf_le_left.trans inf_le_left
  have hq : V ≤ (P.pull f).U (fun _ => i) := inf_le_right
  have hm : V ≤ f ⁻¹ᵁ M.U m := (h₂.trans inf_le_right).trans (pull_U M f (fun _ => m)).le
  have hi' : V ≤ f ⁻¹ᵁ P.U i := hq.trans (pull_U P f (fun _ => i)).le
  have h₃ : V ≤ f ⁻¹ᵁ (M.U m ⊓ P.U i) := le_inf hm hi'
  rw [← germ_resG h₂ y hyV, ← germ_resG h₂ y hyV]
  congr 1
  have e₁ := hb.on n (fun _ => i) hn hq
  have e₂ := H n i m V (le_inf hn hq) h₂ h₃
  have e₃ := congrArg (fun a => resG Y h₃ ((f.app _).hom a)) (hu (m, i))
  simp only [map_mul, app_resG, resG_resG] at e₃
  have e₄ : resG Y hq ((secPull t f).f (fun _ => i)) = resG Y hi' ((f.app _).hom (t.f i)) :=
    resG_resG _ _ _
  have e₅ : resG Y (h₂.trans inf_le_right) ((secPull t' f).f (fun _ => m)) =
      resG Y (le_top : V ≤ f ⁻¹ᵁ ⊤) ((f.app ⊤).hom g₀) * resG Y hm ((f.app _).hom (u.f m)) := by
    refine (resG_resG _ _ _).trans ?_
    change resG Y hm ((f.app _).hom (resG X le_top g₀ * u.f m)) = _
    rw [map_mul, map_mul, app_resG, resG_resG]
    rfl
  rw [map_mul, resG_resG, resG_resG, e₅, e₃]
  refine e₁.trans ?_
  rw [e₂, e₄]
  ring

private theorem UpperTheory.Lit.Nos.IntegralSec.cst_algebraMap {W K' : Type} [CommRing W] [Field K'] [Algebra W K']
    {X Y : Scheme.{0}} (p : X ⟶ Sp W) (f : Y ⟶ X) (q : Y ⟶ Sp K')
    (h : f ≫ p = q ≫ spMap (algebraMap W K')) (V : Y.Opens) (a : W) :
    GlobalTheory.AbLaw.cst q V (algebraMap W K' a) =
      resG Y (le_top : V ≤ f ⁻¹ᵁ ⊤) ((f.app ⊤).hom (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a))) := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ p.appTop ≫ f.appTop =
      CommRingCat.ofHom (algebraMap W K') ≫ (Scheme.ΓSpecIso (CommRingCat.of K')).inv ≫ q.appTop := by
    rw [← Scheme.Hom.comp_appTop, h, Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  exact congrArg (fun φ => resG Y (le_top : V ≤ ⊤) (φ.hom a)) e.symm

private theorem UpperTheory.Lit.Nos.IntegralSec.ev_cst {K' : Type} [Field K'] {Y : Scheme.{0}} (q : Y ⟶ Sp K')
    (x : Sp K' ⟶ Y) (hx : x ≫ q = 𝟙 _) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (c : K') :
    (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE V ⊤ h).hom (GlobalTheory.AbLaw.cst q V c)) = c := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of K')).inv ≫ q.appTop ≫ Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫
      x.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K')).hom = 𝟙 _ := by
    rw [Scheme.Hom.map_appLE_assoc]
    have : q.appTop ≫ x.appLE ⊤ ⊤ le_top = 𝟙 _ := by
      have h1 : x.appLE ⊤ ⊤ le_top = x.appTop := (Scheme.Hom.app_eq_appLE x).symm
      rw [h1, ← Scheme.Hom.comp_appTop, hx, Scheme.Hom.id_appTop]
    rw [reassoc_of% this, Iso.inv_hom_id]
  exact congrArg (fun φ => φ.hom c) e

private theorem UpperTheory.Lit.Nos.IntegralSec.ev_pull {W K' : Type} [CommRing W] [Field K'] [Algebra W K']
    {X Y : Scheme.{0}} (f : Y ⟶ X) (x : Sp K' ⟶ Y) (e₀ : Sp W ⟶ X)
    (hx : x ≫ f = spMap (algebraMap W K') ≫ e₀) (U : X.Opens) (V : Y.Opens) (hle : V ≤ f ⁻¹ᵁ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (h₀ : ⊤ ≤ e₀ ⁻¹ᵁ U) (s : Γ(X, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE V ⊤ h).hom ((f.appLE U V hle).hom s)) =
      algebraMap W K' ((Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom ((e₀.appLE U ⊤ h₀).hom s)) := by
  have key : ∀ (g g' : Sp K' ⟶ X) (_ : g = g') (k : ⊤ ≤ g ⁻¹ᵁ U) (k' : ⊤ ≤ g' ⁻¹ᵁ U),
      g.appLE U ⊤ k = g'.appLE U ⊤ k' := by
    rintro g _ rfl k k'
    rfl
  have e : f.appLE U V hle ≫ x.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K')).hom =
      e₀.appLE U ⊤ h₀ ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom ≫ CommRingCat.ofHom (algebraMap W K') := by
    have h1 : (spMap (algebraMap W K')).appLE ⊤ ⊤ le_top = (spMap (algebraMap W K')).appTop :=
      (Scheme.Hom.app_eq_appLE _).symm
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc, ← Category.assoc, Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact (key _ _ hx _ _).trans ((Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm.trans
      (congrArg (e₀.appLE U ⊤ h₀ ≫ ·) h1))
  exact congrArg (fun φ => φ.hom s) e

theorem UpperTheory.Lit.Nos.integralSec :
    ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) (P M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), w.IsGen → w₁.IsGen → GlobalTheory.SectionLattice.IntegralAtSection G.hom w w₁ → ∀ (v : LB.Iso P M) (c : K'), v.IsGen → (∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ pullback.fst G.hom (spMap (algebraMap W K')) ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) _ c * ((pullback.fst G.hom (spMap (algebraMap W K'))).appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m)) (w.s (n, fun _ => m)).val) → ∀ (t : P.Sec) (b : N.Sec), GlobalTheory.Cartier.SecMaps w₁ (GlobalTheory.Cartier.secPull t (pullback.fst G.hom (spMap (algebraMap W K')))) b → ∃ t' : M.Sec, GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull t' (pullback.fst G.hom (spMap (algebraMap W K')))) b := by
  intro W K' _ _ _ _ _ _ G P M N hP hM _ w w₁ _ _ hI v c hv hrel t b hb
  obtain ⟨e₀, -, x, hx₁, hx₂, i, m, n, hi, hm, h₁, h₂, a, ha⟩ := hI
  have hle : ∀ (n : N.ι) (i : P.ι) (m : M.ι), N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ pullback.fst G.hom (spMap (algebraMap W K')) ⁻¹ᵁ (M.U m ⊓ P.U i) := fun n i m =>
    le_inf (inf_le_right.trans (GlobalTheory.Cartier.pull_U M _ (fun _ => m)).le)
      ((inf_le_left.trans inf_le_right).trans (GlobalTheory.Cartier.pull_U P _ (fun _ => i)).le)
  have h₃ : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m)) :=
    fun y hy => ⟨h₁ hy, (h₂ hy).2⟩
  have h₀ : ⊤ ≤ e₀ ⁻¹ᵁ (M.U m ⊓ P.U i) := fun y hy => ⟨hm hy, hi hy⟩
  have hres : ∀ (U V : (pullback G.hom (spMap (algebraMap W K'))).Opens) (k : V ≤ U) (hU : ⊤ ≤ x ⁻¹ᵁ U)
      (hV : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(pullback G.hom (spMap (algebraMap W K')), U)),
      (x.appLE V ⊤ hV).hom (GlobalTheory.AbLaw.rs _ k s) = (x.appLE U ⊤ hU).hom s := fun U V k hU hV s =>
    congrArg (fun φ => φ.hom s) (Scheme.Hom.map_appLE x hV (homOfLE k).op)
  have e := congrArg (fun s => (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h₃).hom s))
    (hrel n i m (hle n i m))
  simp only [map_mul] at e
  erw [hres _ _ _ h₁, hres _ _ _ h₂, UpperTheory.Lit.Nos.IntegralSec.ev_cst _ x hx₂,
    UpperTheory.Lit.Nos.IntegralSec.ev_pull _ x e₀ hx₁ _ _ _ _ h₀] at e
  have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom
      ((x.appLE _ ⊤ h₂).hom (w.s (n, fun _ => m)).val)) := ((Units.isUnit _).map _).map _
  have hv₀ : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom
      ((e₀.appLE _ ⊤ h₀).hom (v.s (m, i)).val)) := ((Units.isUnit _).map _).map _
  have e' := mul_right_cancel₀ hu.ne_zero (ha.symm.trans e)
  obtain ⟨r, hr⟩ := hv₀.exists_right_inv
  have hc : c = algebraMap W K' (a * r) := by
    rw [map_mul, e', _root_.mul_assoc, ← map_mul]
    exact ((congrArg (fun z => c * algebraMap W K' z) hr).trans (by rw [map_one, _root_.mul_one])).symm
  refine UpperTheory.Lit.Nos.IntegralSec.sec_of_rel _ P M N hP hM w w₁ v hv
    (G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom (a * r))) ?_ t b hb
  intro n i m V k₁ k₂ k₃
  have k : V ≤ N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) := le_inf k₁ (k₂.trans inf_le_right)
  have e := congrArg (GlobalTheory.AbLaw.rs _ k) (hrel n i m (hle n i m))
  rw [map_mul, map_mul, GlobalTheory.AbLaw.rs_cst, hc,
    UpperTheory.Lit.Nos.IntegralSec.cst_algebraMap G.hom _ _ pullback.condition] at e
  refine ((GlobalTheory.AbLaw.rs_rs _ _ _).symm.trans e).trans ?_
  exact congrArg₂ (· * ·) (congrArg (_ * ·) (GlobalTheory.LB.resG_appLE _ _ k _)) (GlobalTheory.AbLaw.rs_rs _ _ _)
end

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit.Nos.C1
open GlobalTheory GlobalTheory.SectionLattice

theorem twisted_sections_extend : ∀ (K W K' : Type) [Field K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra K K'] (D : Set (K' ≃ₐ[K] K')), (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → (∀ σ ∈ D, ∃ (τ : W →+* W) (φ : G.left ⟶ G.left), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) ∧ φ ≫ G.hom = G.hom ≫ spMap τ ∧ pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm) ≫ e.inv.left) ≫ pullback.fst G.hom (spMap (algebraMap W K'))) → ∀ (H : LB A.left) (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))), H.IsLB → M.IsLB → w.IsGen → ∀ σ ∈ D, ∀ (n : ℕ) (s : Fin n → H.Sec) (u : M.Sec) (c : Fin n → K'), GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull u (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (c k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))) → ∃ u' : M.Sec, GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull u' (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (σ (c k)) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))) := by
  intro K W K' _ _ _ _ _ _ _ _ D hD hD' A _ hA G _ hG e he hφ H M w hH hM hw σ hσ n s u c hu
  obtain ⟨τ, φ, hτ, hφG, hφY⟩ := hφ σ hσ
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom
      (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp)
      (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext y; exact (σ.commutes y).symm) ≫
      e.inv.left := ⟨_, rfl⟩
  rw [← hρ] at hφY
  have hA' : ρ ≫ (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) =
      e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) := by
    subst hρ
    have h := congrArg CommaMorphism.left e.inv_hom_id
    simp only [Over.comp_left, Over.id_left] at h
    simp only [Category.assoc]
    rw [reassoc_of% h]
    simp only [pullback.map, Category.id_comp, pullback.lift_fst, Category.comp_id]
  have hq : ρ ≫ pullback.snd G.hom (spMap (algebraMap W K')) =
      pullback.snd G.hom (spMap (algebraMap W K')) ≫ spMap (σ : K' →+* K') := by
    subst hρ
    have h₁ := Over.w e.inv
    have h₂ := Over.w e.hom
    simp only [Over.pullback_obj_hom] at h₁ h₂
    simp only [Category.assoc, h₁]
    simp only [pullback.map, pullback.lift_snd]
    rw [reassoc_of% h₂]
  obtain ⟨w₁, hw₁, hsec, hval⟩ := UpperTheory.Lit.Nos.twistIso M H (pullback.fst G.hom (spMap (algebraMap W K')))
    (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))
    (pullback.snd G.hom (spMap (algebraMap W K'))) ρ φ (σ : K' →+* K') hφY hA' hq hM hH w hw
  have he₀ : η[G].left ≫ G.hom = 𝟙 _ := by simpa using Over.w η[G]
  let x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K')) :=
    pullback.lift (spMap (algebraMap W K') ≫ η[G].left) (𝟙 _)
      (by rw [Category.assoc, he₀]; simp)
  have hx₁ : x ≫ pullback.fst G.hom (spMap (algebraMap W K')) =
      spMap (algebraMap W K') ≫ η[G].left := pullback.lift_fst _ _ _
  have hx₂ : x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ := pullback.lift_snd _ _ _
  have hxρ : x ≫ ρ = spMap (σ : K' →+* K') ≫ x := by
    subst hρ
    exact GlobalTheory.T.semilinear_symm_fixes_unit_section_genericFibre K W K' A G e he σ x hx₁ hx₂
  have he₀φ := GlobalTheory.T.semilinearModel_fixes_unit_section_abelian W K' G hG (σ : K' →+* K') τ φ ρ hτ hφG hφY η[G].left he₀ x hx₁ hxρ
  have hv := GlobalTheory.T.dvr_fractionField_ringEquiv_eq_unit_mul W K' σ.toRingEquiv (hD σ hσ) (hD' σ hσ)
  have hHp : (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))).IsLB :=
    LB.isLB_pull hH _
  have hIAS := GlobalTheory.T.integral_twisted_comparison_at_fixed_section W K' G σ.toRingEquiv τ hv φ η[G].left he₀ he₀φ ρ x hx₁ hx₂ hxρ M _ hM hHp
    w w₁ (hval x hxρ)
  obtain ⟨v, c', hv', hrel⟩ := GlobalTheory.T.exists_lineBundleIso_const_of_genericIso_dvr W K' G hG (M.pull φ) M _ (LB.isLB_pull hM φ) hM hHp w w₁ hw hw₁
  exact UpperTheory.Lit.Nos.integralSec W K' G (M.pull φ) M _ (LB.isLB_pull hM φ) hM hHp w w₁ hw hw₁ hIAS v c' hv' hrel
    (GlobalTheory.Cartier.secPull u φ) _ (hsec n s u c hu)

end UpperTheory.Lit.Nos.C1
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace UpperTheory.Lit.Nos.C2
open GlobalTheory

theorem appTop_cst' {X Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (β : Y ⟶ X)
    (f : X ⟶ Sp R) (f' : Y ⟶ Sp R') (c : R →+* R') (h : β ≫ f = f' ≫ spMap c) (r : R) :
    β.appTop (GlobalTheory.AbLaw.cst f ⊤ r) = GlobalTheory.AbLaw.cst f' ⊤ (c r) := by
  simp only [GlobalTheory.AbLaw.cst, RingHom.comp_apply, GlobalTheory.AbLaw.rs_self]
  have h1 := congrArg (fun φ : Y ⟶ Sp R => φ.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) h
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h1
  rw [h1]
  congr 1
  have h2 := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom c))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2.symm

theorem secPull_add' {X Y : Scheme.{0}} {L : LB X} (s t : L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (s + t) φ = Cartier.secPull s φ + Cartier.secPull t φ :=
  GlobalTheory.LB.f_injective (funext fun i => by simp only [Cartier.secPull, GlobalTheory.LB.add_f, map_add (f := _)])

theorem secPull_smul' {X Y : Scheme.{0}} {L : LB X} (c : Γ(X, ⊤)) (s : L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (c • s) φ = φ.appTop c • Cartier.secPull s φ :=
  GlobalTheory.LB.f_injective (funext fun i => by
    simp only [Cartier.secPull, GlobalTheory.LB.smul_f, map_mul, Cartier.app_resG, Cartier.resG_resG]
    rfl)

theorem secPull_sum_smul' {X Y : Scheme.{0}} {L : LB X} {J : Type} (S : Finset J) (c : J → Γ(X, ⊤))
    (s : J → L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (∑ i ∈ S, c i • s i) φ = ∑ i ∈ S, φ.appTop (c i) • Cartier.secPull (s i) φ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact GlobalTheory.LB.f_injective (funext fun i => by simp [Cartier.secPull, GlobalTheory.LB.zero_f])
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, secPull_add', secPull_smul', ih]

theorem secMaps_sum_smul' {X : Scheme.{0}} {A B : LB X} (w : LB.Iso A B) {J : Type} (S : Finset J)
    (c : J → Γ(X, ⊤)) (a : J → A.Sec) (b : J → B.Sec) (h : ∀ i, Cartier.SecMaps w (a i) (b i)) :
    Cartier.SecMaps w (∑ i ∈ S, c i • a i) (∑ i ∈ S, c i • b i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro p
    simp [GlobalTheory.LB.zero_f]
  | insert x S hx ih =>
    intro p
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    simp only [GlobalTheory.LB.add_f, GlobalTheory.LB.smul_f, map_add (f := _), map_mul, ih p, h x p, Cartier.resG_resG]
    ring

theorem exists_veryAmple_families_stable_matrix : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ D : Set (K' ≃ₐ[K] K'), (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → (∀ x : W, (∀ σ ∈ D, ∀ y : W, σ (algebraMap W K' x) = algebraMap W K' y → y - x ∈ maximalIdeal W) → ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W) → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → (∀ σ ∈ D, ∃ (τ : W →+* W) (φ : G.left ⟶ G.left), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) ∧ φ ≫ G.hom = G.hom ≫ spMap τ ∧ pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm) ≫ e.inv.left) ≫ pullback.fst G.hom (spMap (algebraMap W K'))) → ∃ (N : ℕ) (H : LB A.left) (s : Fin (N + 1) → H.Sec) (M : LB G.left) (t : Fin (N + 1) → M.Sec) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K'), H.IsLB ∧ M.IsLB ∧ GlobalTheory.AbLaw.VeryAmpleBy A.hom H s ∧ GlobalTheory.AbLaw.VeryAmpleBy G.hom M t ∧ IsUnit g.det ∧ (∀ j, GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull (t j) (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (g j k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) ∧ ∀ σ ∈ D, ∃ h : Matrix (Fin (N + 1)) (Fin (N + 1)) W, g.map σ = h.map (algebraMap W K') * g := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm D hD1 hD2 hres A _ _ hA G _ hG e he hφ
  obtain ⟨H₀, hH₀, m₀, s₀, hs₀⟩ := GlobalTheory.ProjField.isProjBy_of_isAbelianScheme K A hA
  obtain ⟨M₀, w₀, hM₀, hw₀⟩ := GlobalTheory.T.exists_lineBundle_extension_of_genericFiber W K' G hG (H₀.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))) (pull_isLB hH₀ _)
  obtain ⟨n, hn, m₂, t₀, ht₀⟩ := GlobalTheory.T.veryAmple_power_of_extension_genericFibre_abelianModel K W K' A hA G hG e H₀ m₀ s₀ M₀ w₀ hH₀ hs₀ hM₀ hw₀
  obtain ⟨m₁, s₁, hs₁⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw K A.left A.hom H₀ m₀ s₀ hH₀ hs₀ n hn
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_isGen_iso_pullback_lineBundle_zpow M₀ H₀ _ _ w₀ hM₀ hH₀ hw₀ n
  have hH := GlobalTheory.AbLaw.isLB_pw hH₀ n
  have hM := GlobalTheory.AbLaw.isLB_pw hM₀ n
  obtain ⟨N, t, ht, htb⟩ := GlobalTheory.T.exists_veryAmple_basis_sections_abelianScheme_over_dvr W G hG _ m₂ t₀ hM ht₀
  obtain ⟨s, g, hs, hg, hgw, huniq⟩ := GlobalTheory.T.abelian_scheme_iso_line_bundle_sections_transfer K W K' A hA G hG e _ m₁ s₁ _ w N t hH hs₁ hM hw htb
  refine ⟨N, _, s, _, t, w, g, hH, hM, hs, ht, hg, hgw, ?_⟩
  intro σ hσ
  have key : ∀ j, ∃ c : Fin (N + 1) → W, ∀ k, σ (g j k) = ∑ l, algebraMap W K' (c l) * g l k := by
    intro j
    obtain ⟨u', hu'⟩ := UpperTheory.Lit.Nos.C1.twisted_sections_extend K W K' D hD1 hD2 A hA G hG e he hφ _ _ w hH hM hw σ hσ (N + 1) s (t j) (g j) (hgw j)
    obtain ⟨c, hc, -⟩ := htb u'
    refine ⟨c, fun k => ?_⟩
    have h2 : Cartier.SecMaps w (Cartier.secPull u' (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (∑ l, algebraMap W K' (c l) * g l k) • Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))) := by
      have e2 : ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (∑ l, algebraMap W K' (c l) * g l k) • Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) = ∑ l, (pullback.fst G.hom (spMap (algebraMap W K'))).appTop (GlobalTheory.AbLaw.cst G.hom ⊤ (c l)) • ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (g l k) • Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [appTop_cst' (pullback.fst G.hom (spMap (algebraMap W K'))) G.hom (pullback.snd G.hom (spMap (algebraMap W K'))) (algebraMap W K') pullback.condition, Finset.smul_sum, smul_smul, map_sum, map_mul, Finset.sum_smul]
        exact Finset.sum_comm
      rw [e2, hc, secPull_sum_smul']
      exact secMaps_sum_smul' w _ _ _ _ hgw
    have h3 := Cartier.SecMaps.eq (pull_isLB hM _) hu' h2
    exact congrFun (huniq _ _ h3) k
  choose c hc using key
  refine ⟨Matrix.of c, ?_⟩
  ext j k
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, hc]

end UpperTheory.Lit.Nos.C2
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit.Nos.C3
open GlobalTheory

theorem appTop_cst {X Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (β : Y ⟶ X)
    (f : X ⟶ Sp R) (f' : Y ⟶ Sp R') (c : R →+* R') (h : β ≫ f = f' ≫ spMap c) (r : R) :
    β.appTop (GlobalTheory.AbLaw.cst f ⊤ r) = GlobalTheory.AbLaw.cst f' ⊤ (c r) := by
  simp only [GlobalTheory.AbLaw.cst, RingHom.comp_apply, GlobalTheory.AbLaw.rs_self]
  have h1 := congrArg (fun φ : Y ⟶ Sp R => φ.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) h
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h1
  rw [h1]
  congr 1
  have h2 := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom c))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2.symm

theorem secPull_add {X Y : Scheme.{0}} {L : LB X} (s t : L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (s + t) φ = Cartier.secPull s φ + Cartier.secPull t φ :=
  GlobalTheory.LB.f_injective (funext fun i => by simp only [Cartier.secPull, GlobalTheory.LB.add_f, map_add (f := _)])

theorem secPull_smul {X Y : Scheme.{0}} {L : LB X} (c : Γ(X, ⊤)) (s : L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (c • s) φ = φ.appTop c • Cartier.secPull s φ :=
  GlobalTheory.LB.f_injective (funext fun i => by
    simp only [Cartier.secPull, GlobalTheory.LB.smul_f, map_mul, Cartier.app_resG, Cartier.resG_resG]
    rfl)

theorem secPull_sum_smul {X Y : Scheme.{0}} {L : LB X} {J : Type} (S : Finset J) (c : J → Γ(X, ⊤))
    (s : J → L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (∑ i ∈ S, c i • s i) φ = ∑ i ∈ S, φ.appTop (c i) • Cartier.secPull (s i) φ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact GlobalTheory.LB.f_injective (funext fun i => by simp [Cartier.secPull, GlobalTheory.LB.zero_f])
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, secPull_add, secPull_smul, ih]

theorem secMaps_sum_smul {X : Scheme.{0}} {A B : LB X} (w : LB.Iso A B) {J : Type} (S : Finset J)
    (c : J → Γ(X, ⊤)) (a : J → A.Sec) (b : J → B.Sec) (h : ∀ i, Cartier.SecMaps w (a i) (b i)) :
    Cartier.SecMaps w (∑ i ∈ S, c i • a i) (∑ i ∈ S, c i • b i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro p
    simp [GlobalTheory.LB.zero_f]
  | insert x S hx ih =>
    intro p
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    simp only [GlobalTheory.LB.add_f, GlobalTheory.LB.smul_f, map_add (f := _), map_mul, ih p, h x p, Cartier.resG_resG]
    ring

theorem spMap_tower (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] :
    spMap (algebraMap S T) ≫ spMap (algebraMap R S) = spMap (algebraMap R T) := by
  rw [← Spec.map_comp, IsScalarTower.algebraMap_eq R S T]
  rfl

theorem exists_compatible_projective_embeddings : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ D : Set (K' ≃ₐ[K] K'), (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → (∀ x : W, (∀ σ ∈ D, ∀ y : W, σ (algebraMap W K' x) = algebraMap W K' y → y - x ∈ maximalIdeal W) → ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W) → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → (∀ σ ∈ D, ∃ (τ : W →+* W) (φ : G.left ⟶ G.left), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) ∧ φ ≫ G.hom = G.hom ≫ spMap τ ∧ pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm) ≫ e.inv.left) ≫ pullback.fst G.hom (spMap (algebraMap W K'))) → ∃ (P : Over (Sp R)) (_ : QuasiSeparated P.hom) (iA : A.left ⟶ P.left) (hA : iA ≫ P.hom = A.hom ≫ spMap (algebraMap R K)) (_ : IsClosedImmersion (pullback.lift iA A.hom hA)) (iG : G.left ⟶ P.left) (hG : iG ≫ P.hom = G.hom ≫ spMap (algebraMap R W)) (_ : IsClosedImmersion (pullback.lift iG G.hom hG)), e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ iA = pullback.fst G.hom (spMap (algebraMap W K')) ≫ iG := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm D hD1 hD2 hres A _ _ hA G _ hG e he hφ
  obtain ⟨N, H, s, M, t, w, g, hH, hM, hs, ht, hg, hw, hD⟩ := UpperTheory.Lit.Nos.C2.exists_veryAmple_families_stable_matrix R K W K' hm D hD1 hD2 hres A hA G hG e he hφ
  obtain ⟨h, k, hh, hk⟩ := GlobalTheory.T.matrix_descent_unramified_dvr R K W K' hm D hD1 hD2 hres (N + 1) g hg hD
  have hkdet : IsUnit k.det := by
    have e1 : algebraMap K K' k.det = algebraMap W K' h.det * g.det := by
      rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]; exact congrArg Matrix.det hk
    have hu : IsUnit (algebraMap K K' k.det) := by
      rw [e1]; exact ((hh.map (algebraMap W K')).mul hg)
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero] at hu
    exact not_isUnit_zero hu
  have hs' := GlobalTheory.T.isVeryAmpleBySections_of_invertible_linear_change K A.left A.hom H N s k hkdet hH hs
  have ht' := GlobalTheory.T.isVeryAmpleBySections_of_invertible_linear_change W G.left G.hom M N t h hh hM ht
  obtain ⟨hs0, hsci⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff _ _).1 hs'
  obtain ⟨ht0, htci⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff _ _).1 ht'
  have hqA : (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) ≫ A.hom = (pullback.snd G.hom (spMap (algebraMap W K'))) ≫ spMap (algebraMap K K') := by
    have h1 : e.hom.left ≫ pullback.snd A.hom (spMap (algebraMap K K')) = (pullback.snd G.hom (spMap (algebraMap W K'))) := Over.w e.hom
    rw [Category.assoc, pullback.condition, ← Category.assoc, h1]
  have hqG : (pullback.fst G.hom (spMap (algebraMap W K'))) ≫ G.hom = (pullback.snd G.hom (spMap (algebraMap W K'))) ≫ spMap (algebraMap W K') := pullback.condition
  have hbase : (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) ≫ A.hom ≫ spMap (algebraMap R K) = (pullback.fst G.hom (spMap (algebraMap W K'))) ≫ G.hom ≫ spMap (algebraMap R W) := by
    rw [← Category.assoc, hqA, ← Category.assoc, hqG, Category.assoc, Category.assoc,
      spMap_tower R K K', spMap_tower R W K']
  have hsec : ∀ j, Cartier.SecMaps w (Cartier.secPull (∑ l, GlobalTheory.AbLaw.cst G.hom ⊤ (h j l) • t l) (pullback.fst G.hom (spMap (algebraMap W K'))))
      (Cartier.secPull (∑ m, GlobalTheory.AbLaw.cst A.hom ⊤ (k j m) • s m) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))) := by
    intro j
    rw [UpperTheory.Lit.Nos.C3.secPull_sum_smul, UpperTheory.Lit.Nos.C3.secPull_sum_smul]
    have e2 : ∑ m, (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))).appTop (GlobalTheory.AbLaw.cst A.hom ⊤ (k j m)) • Cartier.secPull (s m) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) =
        ∑ l, (pullback.fst G.hom (spMap (algebraMap W K'))).appTop (GlobalTheory.AbLaw.cst G.hom ⊤ (h j l)) •
          ∑ m, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (g l m) • Cartier.secPull (s m) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) := by
      simp only [UpperTheory.Lit.Nos.C3.appTop_cst (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) A.hom (pullback.snd G.hom (spMap (algebraMap W K'))) (algebraMap K K') hqA,
        UpperTheory.Lit.Nos.C3.appTop_cst (pullback.fst G.hom (spMap (algebraMap W K'))) G.hom (pullback.snd G.hom (spMap (algebraMap W K'))) (algebraMap W K') hqG, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      have e3 := congrFun (congrFun hk j) m
      simp only [Matrix.map_apply, Matrix.mul_apply] at e3
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e3, map_sum]
      simp only [map_mul]
    rw [e2]
    exact UpperTheory.Lit.Nos.C3.secMaps_sum_smul w _ _ _ _ hw
  refine ⟨Over.mk (PSpace.str R N), by show QuasiSeparated (PSpace.str R N); unfold PSpace.str; infer_instance,
    GlobalTheory.ProjSpace.toProj A.hom _ hs0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R K),
    by simp only [Over.mk_hom, Category.assoc, GlobalTheory.ProjSpace.baseChange_str, GlobalTheory.ProjSpace.toProj_str_assoc], ?_,
    GlobalTheory.ProjSpace.toProj G.hom _ ht0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R W),
    by simp only [Over.mk_hom, Category.assoc, GlobalTheory.ProjSpace.baseChange_str, GlobalTheory.ProjSpace.toProj_str_assoc], ?_, ?_⟩
  · have hci : IsClosedImmersion (GlobalTheory.ProjSpace.toProj A.hom _ hs0 ≫
        (GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap R K)).isoPullback.hom) := inferInstance
    change IsClosedImmersion (pullback.lift (f := PSpace.str R N) (g := spMap (algebraMap R K))
      (GlobalTheory.ProjSpace.toProj A.hom _ hs0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R K)) A.hom _)
    have key : pullback.lift (f := PSpace.str R N) (g := spMap (algebraMap R K))
        (GlobalTheory.ProjSpace.toProj A.hom _ hs0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R K)) A.hom
        (by simp only [Category.assoc, GlobalTheory.ProjSpace.baseChange_str, GlobalTheory.ProjSpace.toProj_str_assoc]) =
        GlobalTheory.ProjSpace.toProj A.hom _ hs0 ≫ (GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap R K)).isoPullback.hom := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst]
      · rw [pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd, GlobalTheory.ProjSpace.toProj_str]
    rw [key]
    exact hci
  · have hci : IsClosedImmersion (GlobalTheory.ProjSpace.toProj G.hom _ ht0 ≫
        (GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap R W)).isoPullback.hom) := inferInstance
    change IsClosedImmersion (pullback.lift (f := PSpace.str R N) (g := spMap (algebraMap R W))
      (GlobalTheory.ProjSpace.toProj G.hom _ ht0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R W)) G.hom _)
    have key : pullback.lift (f := PSpace.str R N) (g := spMap (algebraMap R W))
        (GlobalTheory.ProjSpace.toProj G.hom _ ht0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R W)) G.hom
        (by simp only [Category.assoc, GlobalTheory.ProjSpace.baseChange_str, GlobalTheory.ProjSpace.toProj_str_assoc]) =
        GlobalTheory.ProjSpace.toProj G.hom _ ht0 ≫ (GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap R W)).isoPullback.hom := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst]
      · rw [pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd, GlobalTheory.ProjSpace.toProj_str]
    rw [key]
    exact hci
  · rw [GlobalTheory.ProjSpace.toProj_baseChange, GlobalTheory.ProjSpace.toProj_baseChange, ← Category.assoc,
      ← GlobalTheory.ProjSpace.toProj_secPull hs0, ← GlobalTheory.ProjSpace.toProj_secPull ht0]
    change GlobalTheory.ProjSpace.toProj ((e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) ≫ A.hom ≫ spMap (algebraMap R K)) _ _ =
      GlobalTheory.ProjSpace.toProj ((pullback.fst G.hom (spMap (algebraMap W K'))) ≫ G.hom ≫ spMap (algebraMap R W)) _ _
    rw [hbase]
    exact GlobalTheory.ProjSpace.toProj_eq_of_secMaps _ _ hsec

end UpperTheory.Lit.Nos.C3
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit.Nos.C4
open GlobalTheory

theorem exists_scheme_model_descent_unramified : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ D : Set (K' ≃ₐ[K] K'), (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → (∀ x : W, (∀ σ ∈ D, ∀ y : W, σ (algebraMap W K' x) = algebraMap W K' y → y - x ∈ maximalIdeal W) → ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W) → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → ∃ (X : Over (Sp R)) (a : A.left ⟶ X.left) (g : G.left ⟶ X.left), IsPullback a A.hom X.hom (spMap (algebraMap R K)) ∧ IsPullback g G.hom X.hom (spMap (algebraMap R W)) ∧ e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ a = pullback.fst G.hom (spMap (algebraMap W K')) ≫ g := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm D hD1 hD2 hres A _ _ hA G _ hG e he
  obtain ⟨P, hPs, iA, hA', hiA, iG, hG', hiG, hc⟩ := UpperTheory.Lit.Nos.C3.exists_compatible_projective_embeddings R K W K' hm D hD1 hD2 hres A hA G hG e he
    (fun σ _ => GlobalTheory.T.galois_descent_integral_structure R K W K' σ (hD1 σ ‹_›) A hA G hG e he)
  have := hA.proper
  have := hG.proper
  have := hG.smooth
  exact GlobalTheory.T.abelian_variety_extends_unramified R K W K' hm P hPs A inferInstance G inferInstance inferInstance e iA hA' hiA iG hG' hiG hc

end UpperTheory.Lit.Nos.C4
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit.Nos.C5
open GlobalTheory

theorem val_lt_one_iff {F : Type} [Field F] (A : ValuationSubring F) {x : F} (hx : x ≠ 0) :
    A.valuation x < 1 ↔ x⁻¹ ∉ A := by
  rw [← A.valuation_le_one_iff, not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hx), inv_inv]

end UpperTheory.Lit.Nos.C5

theorem UpperTheory.Lit.Nos.C5.mapsTo_fixedField_inertia : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω), σ • V = V → ∀ x ∈ IntermediateField.fixedField (inertia K V), σ x ∈ IntermediateField.fixedField (inertia K V) := by
  intro K Ω _ _ _ V σ hσ x hx
  have hσinv : σ⁻¹ • V = V := by
    conv_lhs => rw [← hσ]
    exact inv_smul_smul σ V
  have hmem : ∀ (ρ : Ω ≃ₐ[K] Ω), ρ • V = V → ∀ y, ρ y ∈ V ↔ y ∈ V := by
    intro ρ h y
    rw [← ValuationSubring.smul_mem_pointwise_smul_iff (g := ρ) (S := V) (x := y), h]
    rfl
  have hval : ∀ (ρ : Ω ≃ₐ[K] Ω), ρ • V = V → ∀ w, V.valuation (ρ w) < 1 ↔ V.valuation w < 1 := by
    intro ρ h w
    by_cases hw : w = 0
    · simp [hw]
    · rw [UpperTheory.Lit.Nos.C5.val_lt_one_iff V hw, UpperTheory.Lit.Nos.C5.val_lt_one_iff V ((map_ne_zero ρ).2 hw), ← map_inv₀, hmem ρ h]
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro τ hτ
  have hρ : σ⁻¹ * τ * σ ∈ inertia K V := by
    rw [mem_inertia_iff] at hτ ⊢
    obtain ⟨h1, h2⟩ := hτ
    refine ⟨?_, fun y hy => ?_⟩
    · rw [mul_smul, mul_smul, hσ, h1, hσinv]
    · have hz : σ y ∈ V := (hmem σ hσ y).2 hy
      have e : (σ⁻¹ * τ * σ) y - y = σ⁻¹ (τ (σ y) - σ y) := by
        rw [map_sub]
        simp [AlgEquiv.mul_apply]
      rw [e, hval σ⁻¹ hσinv]
      exact h2 _ hz
  have := hx _ hρ
  have e2 : τ (σ x) = σ ((σ⁻¹ * τ * σ) x) := by simp [AlgEquiv.mul_apply]
  rw [e2, this]

theorem UpperTheory.Lit.Nos.C5.hasGoodReduction_of_inertiaFixed : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → HasGoodReduction (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) (IntermediateField.fixedField (inertia K V)) ((Over.pullback (spMap (algebraMap K (IntermediateField.fixedField (inertia K V))))).obj A) → HasGoodReduction R K A := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA hgood
  set K' := IntermediateField.fixedField (inertia K V) with hK'
  set W := V.comap (algebraMap K' Ω) with hW
  haveI : IsDiscreteValuationRing W := GlobalTheory.T.isDiscreteValuationRing_fixedField_inertia_alt R K Ω V hV
  have memW : ∀ z : K', z ∈ W ↔ algebraMap K' Ω z ∈ V := fun z => ValuationSubring.mem_comap
  have e1 : ∀ a : K, algebraMap K' Ω (algebraMap K K' a) = algebraMap K Ω a :=
    fun a => (IsScalarTower.algebraMap_apply K K' Ω a).symm
  have hRW : ∀ r : R, algebraMap K K' (algebraMap R K r) ∈ W := by
    intro r
    rw [memW, e1]
    have h1 : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨r, rfl⟩
    exact h1
  letI : Algebra R W := (((algebraMap K K').comp (algebraMap R K)).codRestrict W hRW).toAlgebra
  letI : Algebra R K' := ((algebraMap K K').comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R W K' := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  have hmax : ∀ x : W, x ∈ maximalIdeal W ↔ V.valuation (algebraMap K' Ω x) < 1 := by
    intro x
    rw [ValuationSubring.valuation_lt_one_iff]
    by_cases hx : (x : K') = 0
    · simp [hx]
    · have hx' : algebraMap K' Ω x ≠ 0 := (map_ne_zero _).2 hx
      rw [UpperTheory.Lit.Nos.C5.val_lt_one_iff W hx, UpperTheory.Lit.Nos.C5.val_lt_one_iff V hx', memW, map_inv₀]
  have hunr : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨hlt, hdiv⟩ := GlobalTheory.T.uniformizer_of_valuationRing_fixedField_inertia R K Ω V hV π hπ
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    apply le_antisymm
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap R W π ∈ maximalIdeal W
      rw [hmax]
      show V.valuation (algebraMap K' Ω (algebraMap K K' (algebraMap R K π))) < 1
      rw [e1]; exact hlt
    · intro x hx
      rw [hmax] at hx
      obtain ⟨z, hzV, hz⟩ := hdiv (x : K') hx
      rw [Ideal.mem_span_singleton']
      refine ⟨⟨z, (memW z).2 hzV⟩, Subtype.ext ?_⟩
      show z * algebraMap K K' (algebraMap R K π) = (x : K')
      rw [hz, mul_comm]
  have hσinv : ∀ σ : Ω ≃ₐ[K] Ω, σ • V = V → σ⁻¹ • V = V := by
    intro σ h
    conv_lhs => rw [← h]
    exact inv_smul_smul σ V
  have hσmem : ∀ σ : Ω ≃ₐ[K] Ω, σ • V = V → ∀ x, σ x ∈ V ↔ x ∈ V := by
    intro σ h x
    rw [← ValuationSubring.smul_mem_pointwise_smul_iff (g := σ) (S := V) (x := x), h]
    rfl
  let res : ∀ σ : Ω ≃ₐ[K] Ω, σ • V = V → (K' ≃ₐ[K] K') := fun σ h =>
    { toFun := fun x => ⟨σ (x : Ω), UpperTheory.Lit.Nos.C5.mapsTo_fixedField_inertia K Ω V σ h x x.2⟩
      invFun := fun x => ⟨σ.symm (x : Ω), UpperTheory.Lit.Nos.C5.mapsTo_fixedField_inertia K Ω V σ⁻¹ (hσinv σ h) x x.2⟩
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : Ω))
      right_inv := fun x => Subtype.ext (σ.apply_symm_apply (x : Ω))
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : Ω) (y : Ω))
      map_add' := fun x y => Subtype.ext (map_add σ (x : Ω) (y : Ω))
      commutes' := fun a => Subtype.ext (σ.commutes a) }
  let D : Set (K' ≃ₐ[K] K') := {τ | ∃ σ : Ω ≃ₐ[K] Ω, σ • V = V ∧ ∀ x : K', algebraMap K' Ω (τ x) = σ (algebraMap K' Ω x)}
  have hD1 : ∀ σ : K' ≃ₐ[K] K', σ ∈ D → ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y := by
    rintro τ ⟨σ, hσ, hτ⟩ x
    refine ⟨⟨τ x, ?_⟩, rfl⟩
    rw [memW, hτ, hσmem σ hσ, ← memW]
    exact x.2
  have hD2 : ∀ σ : K' ≃ₐ[K] K', σ ∈ D → ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y := by
    rintro τ ⟨σ, hσ, hτ⟩ x
    refine ⟨⟨τ.symm x, ?_⟩, rfl⟩
    have h2 : σ (algebraMap K' Ω (τ.symm x)) = algebraMap K' Ω x := by
      rw [← hτ, τ.apply_symm_apply]
    rw [memW, ← hσmem σ hσ, h2, ← memW]
    exact x.2
  have hres : ∀ x : W, (∀ σ : K' ≃ₐ[K] K', σ ∈ D → ∀ y : W, σ (algebraMap W K' x) = algebraMap W K' y → y - x ∈ maximalIdeal W) →
      ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W := by
    intro x H
    obtain ⟨r, hr⟩ := GlobalTheory.T.exists_dvr_congr_of_residue_fixed_by_decomposition R K Ω V hV (algebraMap K' Ω x) ((memW x).1 x.2) (fun σ hσ => by
      have hτD : res σ hσ ∈ D := ⟨σ, hσ, fun _ => rfl⟩
      have hy : (res σ hσ x : K') ∈ W := by
        rw [memW]; exact (hσmem σ hσ _).2 ((memW x).1 x.2)
      have h3 := (hmax _).1 (H (res σ hσ) hτD ⟨_, hy⟩ rfl)
      exact h3)
    refine ⟨r, (hmax _).2 ?_⟩
    exact hr
  obtain ⟨G, _, hG, e, he⟩ := hgood
  obtain ⟨X, a, g, ha, hg, hc⟩ := UpperTheory.Lit.Nos.C4.exists_scheme_model_descent_unramified R K W K' hunr D hD1 hD2 hres A hA G hG e he
  exact GlobalTheory.T.hasGoodReduction_of_unramified_abelianScheme_model R K W K' hunr A hA G hG e he X a g ha hg hc
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace UpperTheory.Lit.Nos.C6
open GlobalTheory

def basePtEquiv {K L : Type} [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] :
    (ptOver K L ⟶ A) ≃* (𝟙_ (Over (Sp L)) ⟶ (Over.pullback (spMap (algebraMap K L))).obj A) :=
  let e : (Over.map (spMap (algebraMap K L))).obj (𝟙_ (Over (Sp L))) ≅ ptOver K L :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ spMap (algebraMap K L) = 𝟙 _ ≫ spMap (algebraMap K L)
      rfl)
  { toFun := fun x => (Over.mapPullbackAdj (spMap (algebraMap K L))).homEquiv _ A (e.hom ≫ x)
    invFun := fun y => e.inv ≫ ((Over.mapPullbackAdj (spMap (algebraMap K L))).homEquiv _ A).symm y
    left_inv := fun x => by simp
    right_inv := fun y => by simp
    map_mul' := fun x y => by
      rw [MonObj.comp_mul, ReciprocityTheory.ChartRestriction.G.Out.UBC.homEquiv_mul] }

def fixedPtHom {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω))
    (A : Over (Sp K)) [GrpObj A] :
    (ptOver K (IntermediateField.fixedField H) ⟶ A) →* (ptOver K Ω ⟶ A) :=
  MonoidHom.mk' (fun x => ptOverMap (IntermediateField.val _) ≫ x) fun x y => MonObj.comp_mul _ x y

theorem fixedPtHom_injective {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω))
    (A : Over (Sp K)) [GrpObj A] : Function.Injective (fixedPtHom H A) := by
  intro x y e
  have := epi_ptOverMap (IntermediateField.val (IntermediateField.fixedField H))
  exact Over.OverMorphism.ext ((cancel_epi (ptOverMap (IntermediateField.val _)).left).1
    (by simpa using congrArg (fun q => q.left) (show ptOverMap (IntermediateField.val _) ≫ x =
      ptOverMap (IntermediateField.val _) ≫ y from e)))

set_option synthInstance.maxHeartbeats 200000 in
theorem card_torsion_fixedField {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω))
    (A : Over (Sp K)) [GrpObj A] (hA : LocallyOfFiniteType A.hom) (m : ℕ)
    (hfix : ∀ σ ∈ H, ∀ x : ptOver K Ω ⟶ A, x ^ m = 1 → specAut σ ≫ x = x) :
    Nat.card {x : 𝟙_ (Over (Sp (IntermediateField.fixedField H))) ⟶
        (Over.pullback (spMap (algebraMap K (IntermediateField.fixedField H)))).obj A // x ^ m = 1} =
      Nat.card {x : ptOver K Ω ⟶ A // x ^ m = 1} := by
  have e1 := Equiv.subtypeEquiv (basePtEquiv (K := K) (L := IntermediateField.fixedField H) A).symm.toEquiv
    (p := fun x => x ^ m = 1) (q := fun y => y ^ m = 1) (fun x => by
      change x ^ m = 1 ↔ (basePtEquiv A).symm x ^ m = 1
      rw [← map_pow, MulEquiv.map_eq_one_iff])
  rw [Nat.card_congr e1]
  refine Nat.card_eq_of_bijective (fun y => ⟨fixedPtHom H A y.1, by rw [← map_pow, y.2, map_one]⟩) ⟨?_, ?_⟩
  · intro y y' h
    exact Subtype.ext (fixedPtHom_injective H A (congrArg Subtype.val h))
  · rintro ⟨z, hz⟩
    obtain ⟨y, hy⟩ := GlobalTheory.T.exists_fixedField_point_of_fixed_by_subgroup K Ω H A hA z (fun σ hσ => hfix σ hσ z hz)
    have hep := epi_ptOverMap (IntermediateField.val (IntermediateField.fixedField H))
    have hj : (ptOverMap (IntermediateField.val (IntermediateField.fixedField H))).left =
        spMap (algebraMap (IntermediateField.fixedField H) Ω) := rfl
    rw [hj] at hep
    have hover : y ≫ A.hom = spMap (algebraMap K (IntermediateField.fixedField H)) := by
      refine (cancel_epi (spMap (algebraMap (IntermediateField.fixedField H) Ω))).1 ?_
      rw [← Category.assoc, hy, Over.w z]
      change spMap (algebraMap K Ω) = _
      rw [← Spec.map_comp]
      congr 1
    let y' : ptOver K (IntermediateField.fixedField H) ⟶ A := Over.homMk y hover
    have hy' : fixedPtHom H A y' = z := Over.OverMorphism.ext hy
    refine ⟨⟨y', ?_⟩, Subtype.ext hy'⟩
    apply fixedPtHom_injective H A
    rw [map_pow, hy', hz, map_one]

end UpperTheory.Lit.Nos.C6

namespace UpperTheory.Lit.Nos.C6
open GlobalTheory

theorem hasGoodReduction_of_infinite_torsionUnramified : ∀ (R K Ω : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite → HasGoodReduction R K A := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA hinf
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  apply UpperTheory.Lit.Nos.C5.hasGoodReduction_of_inertiaFixed R K Ω V hV A hA
  obtain ⟨hSH, f, -, -⟩ := GlobalTheory.T.inertiaFixedField_valuationRing_strictlyHenselian R K Ω V hV
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_relativeDimension_abelianVariety_field K A hA
  have hA' := isAbelianScheme_pullback_obj (spMap (algebraMap K (IntermediateField.fixedField (inertia K V)))) A hA
  haveI := hA'.comm
  have hloc : LocallyOfFiniteType A.hom := by haveI := hA.smooth; infer_instance
  refine GlobalTheory.T.hasGoodReduction_of_many_rational_torsion_points _ _ hSH _ hA' g ?_ ?_
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg
  · refine hinf.mono ?_
    rintro m ⟨hm, hu⟩
    have hunit : IsUnit (m : R) := by
      by_contra h
      apply hm
      rw [← map_natCast (residue R), residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
      exact h
    have hmK : (m : K) ≠ 0 := by
      rw [← map_natCast (algebraMap R K)]
      exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hunit.ne_zero
    refine ⟨?_, ?_⟩
    · have h' := hunit.map f
      rw [map_natCast] at h'
      rw [← map_natCast (residue _), ne_eq, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, not_not]
      exact h'
    · rw [card_torsion_fixedField (inertia K V) A hloc m (fun σ hσ x hx => hu σ hσ x hx)]
      exact GlobalTheory.T.card_abelianVariety_torsion_sepClosed K Ω A hA g hg m hmK

end UpperTheory.Lit.Nos.C6
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit.Nos.Nos
open GlobalTheory

theorem neronOggShafarevich : NeronOggShafarevichSt := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA
  tfae_have 1 → 2 := GlobalTheory.T.torsionUnramified_of_hasGoodReduction_alt R K Ω V hV A
  tfae_have 2 → 4 := fun hb => (GlobalTheory.T.torsionUnramified_imp_tateModule_and_infinite R K Ω V A hb).1
  tfae_have 2 → 3 := fun hb => (GlobalTheory.T.torsionUnramified_imp_tateModule_and_infinite R K Ω V A hb).2
  tfae_have 4 → 3 := by
    rintro ⟨l, hf, hl, ht⟩
    exact GlobalTheory.T.infinite_torsionUnramified_of_tateModuleUnramified R K Ω V hV A hA l hl ht
  tfae_have 3 → 1 := UpperTheory.Lit.Nos.C6.hasGoodReduction_of_infinite_torsionUnramified R K Ω V hV A hA
  tfae_finish

end UpperTheory.Lit.Nos.Nos
