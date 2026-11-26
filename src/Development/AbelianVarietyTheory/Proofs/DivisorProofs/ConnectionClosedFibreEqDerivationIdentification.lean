module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionClosedFibreOfPulledBackIso

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreDerivationOfTwoDualNumberPullbacks
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreDerivationOfTwoDualNumberPullbacks
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KS.TwoPull

variable {X Y Z : Scheme.{0}}

theorem pull_pull (f : Z ⟶ Y) (g : Y ⟶ X) (h : Z ⟶ X) (e : f ≫ g = h) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e₃ : W ≤ h ⁻¹ᵁ U) (a : Γ(X, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom a) = (h.appLE U W e₃).hom a := by
  subst e
  exact congrArg (fun φ => φ.hom a) (Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂)

theorem res_pull (φ : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG Y h' ((φ.appLE U V h).hom a) = (φ.appLE U W (h'.trans h)).hom a :=
  congrArg (fun q => q.hom a) (φ.appLE_map h (homOfLE h').op)

theorem pull_res (φ : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U') (h' : U' ≤ U) (a : Γ(X, U)) :
    (φ.appLE U' V h).hom (resG X h' a) = (φ.appLE U V (h.trans fun _ hy => h' hy)).hom a :=
  congrArg (fun q => q.hom a) (φ.map_appLE h (homOfLE h').op)

theorem app_res (φ : Y ⟶ X) {U U' : X.Opens} (h' : U' ≤ U) (a : Γ(X, U)) :
    (φ.app U').hom (resG X h' a) = resG Y (fun _ hy => h' hy) ((φ.app U).hom a) := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
  exact (pull_res φ _ _ _).trans (res_pull φ _ _ _).symm

theorem id_pull {U : X.Opens} (h : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (a : Γ(X, U)) :
    ((𝟙 X : X ⟶ X).appLE U U h).hom a = a := by
  have : (𝟙 X : X ⟶ X).appLE U U h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (X.presheaf.map_id _)
  rw [this]
  rfl

theorem spec_pull_inv {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (e : ⊤ ≤ spMap f ⁻¹ᵁ ⊤)
    (r : R) :
    ((spMap f).appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (f r) := by
  have h := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  have h2 : (spMap f).appLE ⊤ ⊤ e = (spMap f).appTop := (Scheme.Hom.app_eq_appLE (spMap f) (U := ⊤)).symm
  rw [h2]
  exact h.symm

theorem pull_const {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (φ : Y ⟶ X) (p : X ⟶ Sp R)
    (p' : Y ⟶ Sp R') (hφ : φ ≫ p = p' ≫ spMap f) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (r : R) :
    (φ.appLE U V h).hom (constFn p U r) = constFn p' V (f r) := by
  unfold constFn
  rw [← spec_pull_inv f le_top r]
  exact (pull_pull φ p _ hφ _ _ le_top _).trans (pull_pull p' (spMap f) _ rfl _ _ _ _).symm

theorem res_const {R : Type} [CommRing R] (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    resG X h (constFn q U a) = constFn q V a :=
  res_pull q _ h _

def twoPullConstantsRingHom {R : Type} [CommRing R] (q : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (q.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem const_eq {R : Type} [CommRing R] (q : X ⟶ Sp R) (U : X.Opens) (a : R) :
    constFn q U a = twoPullConstantsRingHom q U a := rfl

theorem dual_decomp {k : Type} [Field k] (x : DualNumber k) :
    x = algebraMap k (DualNumber k) x.fst + DualNumber.eps * algebraMap k (DualNumber k) x.snd := by
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.KS.TwoPull


open GlobalTheory.KS.TwoPull in
theorem GlobalTheory.KS.TwoPull.exists_locDerK_of_two_pullbacks : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∃ d : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.A.hom m₀ (fun r => (ρ r).snd) ⊤ d ∧ (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (d W f) (π₂ ⁻¹ᵁ W)) := by
  intro k _ R _ P ρ B' _ π₁ π₂ hπ₁ hπ₂ hagr A₀ _ m₀ hm₀ pr hpr hprA
  subst hpr
  have hsp : spMap (constHom ρ) =
      spMap (algebraMap k (DualNumber k)) ≫ spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) := by
    rw [← spMap_comp]; rfl
  have hpb : IsPullback pr B'.hom A₀.hom (spMap (algebraMap k (DualNumber k))) := by
    refine IsPullback.of_right ?_ hprA hm₀.1
    rw [← hsp]; exact hπ₂.1
  have hid : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [← spMap_comp]
    have : ((TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k))) = RingHom.id k := by
      ext x; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; simp [spMap]
  have hcomp : 𝟙 A₀.left ≫ A₀.hom =
      (A₀.hom ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ spMap (algebraMap k (DualNumber k)) := by
    rw [Category.assoc, hid, Category.id_comp, Category.comp_id]
  set j := hpb.lift (𝟙 _) (A₀.hom ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom) hcomp with hjdef
  have hjρ : j ≫ pr = 𝟙 _ := hpb.lift_fst _ _ _
  have hjπ : j ≫ B'.hom = A₀.hom ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := hpb.lift_snd _ _ _
  have hm : j ≫ π₁ = m₀ := by
    rw [hagr _ j A₀.hom hjπ, ← Category.assoc, hjρ, Category.id_comp]
  have hp : π₁ ≫ P.A.hom = B'.hom ≫ spMap ρ := hπ₁.1.w
  have hW : ∀ W : P.A.left.Opens, pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W) = π₁ ⁻¹ᵁ W := fun W =>
    (GlobalTheory.T.preimage_eq_of_agree_on_closedFibre_dualNumbers k _ _ B'.hom π₁ (pr ≫ m₀) hagr W).symm
  have hdec := GlobalTheory.T.existsUnique_add_eps_mul_on_dualNumber_thickening k A₀.left B'.left A₀.hom B'.hom pr hpb
  have uniq : ∀ (O : A₀.left.Opens) (a b a' b' : Γ(A₀.left, O)),
      (pr.app O).hom a + constFn B'.hom _ DualNumber.eps * (pr.app O).hom b =
        (pr.app O).hom a' + constFn B'.hom _ DualNumber.eps * (pr.app O).hom b' → b = b' := fun O a b a' b' h =>
    congrArg Prod.snd ((hdec O ((pr.app O).hom a + constFn B'.hom _ DualNumber.eps * (pr.app O).hom b)).unique
      (y₁ := (a, b)) (y₂ := (a', b')) rfl h)
  have ex : ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ∃ b : Γ(A₀.left, m₀ ⁻¹ᵁ W),
      (π₁.appLE W _ (hW W).le).hom f = (pr.app _).hom ((m₀.app W).hom f) +
        constFn B'.hom _ DualNumber.eps * (pr.app _).hom b := by
    intro W f
    obtain ⟨⟨a, b⟩, hab, -⟩ := hdec (m₀ ⁻¹ᵁ W) ((π₁.appLE W _ (hW W).le).hom f)
    refine ⟨b, ?_⟩
    have hle : m₀ ⁻¹ᵁ W ≤ j ⁻¹ᵁ (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) := by
      rw [← Scheme.Hom.comp_preimage, hjρ]; exact le_rfl
    have h1 := congrArg (j.appLE _ _ hle).hom hab
    rw [map_add (f := _), map_mul, pull_const _ j B'.hom A₀.hom hjπ, pull_pull j π₁ m₀ hm _ _ le_rfl] at h1
    have h2 : (j.appLE _ _ hle).hom ((pr.app (m₀ ⁻¹ᵁ W)).hom a) = a := by
      rw [Scheme.Hom.app_eq_appLE]
      exact (pull_pull j pr (𝟙 _) hjρ (U := m₀ ⁻¹ᵁ W) (W := m₀ ⁻¹ᵁ W) le_rfl hle le_rfl a).trans (id_pull _ a)
    have h3 : constFn A₀.hom (m₀ ⁻¹ᵁ W) ((TrivSqZeroExt.fstHom k k k).toRingHom DualNumber.eps) = 0 := by
      have : (TrivSqZeroExt.fstHom k k k).toRingHom DualNumber.eps = 0 := by simp
      rw [this, const_eq, map_zero]
    have h4 : (m₀.app W).hom f = a := by
      rw [Scheme.Hom.app_eq_appLE]
      refine h1.trans ?_
      rw [h3, zero_mul, add_zero]
      exact h2
    rw [h4]
    exact hab
  choose d hd using ex
  have hee : ∀ O : B'.left.Opens, constFn B'.hom O DualNumber.eps * constFn B'.hom O DualNumber.eps = 0 := fun O => by
    rw [const_eq, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  refine ⟨d, ⟨fun W _ f f' => ?_, fun W _ f f' => ?_, fun W W' h _ f => ?_, fun W _ r => ?_⟩, ?_⟩
  · refine uniq _ ((m₀.app W).hom (f + f')) _ ((m₀.app W).hom (f + f')) _ ?_
    rw [← hd, map_add (f := _), hd, hd]
    simp only [map_add (f := _)]
    ring
  · refine uniq _ ((m₀.app W).hom (f * f')) _ ((m₀.app W).hom (f * f')) _ ?_
    rw [← hd, map_mul, hd, hd]
    simp only [map_add (f := _), map_mul]
    linear_combination (pr.app _).hom (d W f) * (pr.app _).hom (d W f') * hee _
  · have h0 : m₀ ⁻¹ᵁ W' ≤ m₀ ⁻¹ᵁ W := fun _ hy => h hy
    rw [show rsT (d W f) (m₀ ⁻¹ᵁ W') = resG _ h0 (d W f) from dif_pos h0]
    refine uniq _ ((m₀.app W').hom (resG _ h f)) _ ((m₀.app W').hom (resG _ h f)) _ ?_
    have h0' : pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W') ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W) := fun _ hy => h hy
    have h1 := congrArg (resG _ h0') (hd W f)
    rw [res_pull, map_add (f := _), map_mul, res_const] at h1
    rw [← hd, pull_res]
    refine h1.trans ?_
    rw [app_res m₀ h f]
    exact congrArg₂ (· + ·) (app_res pr h0 _).symm (congrArg (_ * ·) (app_res pr h0 _).symm)
  · refine uniq _ ((m₀.app W).hom (constFn P.A.hom W r)) _ (constFn A₀.hom _ (ρ r).fst) _ ?_
    rw [← hd, pull_const ρ π₁ P.A.hom B'.hom hp, Scheme.Hom.app_eq_appLE, pull_const _ pr A₀.hom B'.hom hpb.w,
      pull_const _ pr A₀.hom B'.hom hpb.w]
    simp only [const_eq]
    rw [← map_mul, ← map_add (f := _)]
    exact congrArg _ (dual_decomp _)
  · intro W f
    show pbT π₁ f (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) = pbT (pr ≫ m₀) f (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) +
      constFn B'.hom (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) DualNumber.eps * pbT pr (d W f) (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W))
    unfold pbT
    rw [dif_pos (hW W).le, dif_pos le_rfl, dif_pos (show pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W) ≤ (pr ≫ m₀) ⁻¹ᵁ W from le_rfl), hd W f, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
      pull_pull pr m₀ (pr ≫ m₀) rfl]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreDerivationOfTwoDualNumberPullbacksStatement
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
theorem _root_.GlobalTheory.T.exists_fibre_derivation_of_two_dualNumber_pullbacks : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∃ d : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.A.hom m₀ (fun r => (ρ r).snd) ⊤ d ∧ (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (d W f) (π₂ ⁻¹ᵁ W)) := by
  first | exact @GlobalTheory.KS.TwoPull.exists_locDerK_of_two_pullbacks | exact GlobalTheory.KS.TwoPull.exists_locDerK_of_two_pullbacks | (intros; apply GlobalTheory.KS.TwoPull.exists_locDerK_of_two_pullbacks <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEqUnitMulOneAddEpsPotential
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEqUnitMulOneAddEpsPotential
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ConnUnit
open GlobalTheory.KS

theorem constFn_mul {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) (O : X.Opens) (a b : R) :
    constFn q O (a * b) = constFn q O a * constFn q O b := by
  simp only [constFn, map_mul]

theorem constFn_eps_sq {k : Type} [Field k] {X : Scheme.{0}} (q : X ⟶ Sp (DualNumber k)) (O : X.Opens) :
    constFn q O DualNumber.eps * constFn q O DualNumber.eps = 0 := by
  rw [← constFn_mul, DualNumber.eps_mul_eps]; simp only [constFn, map_zero]

theorem rsT_resG {Y : Scheme.{0}} {U V : Y.Opens} (h : V ≤ U) (x : Γ(Y, U)) {Q : Y.Opens} (hQ : Q ≤ V) :
    rsT (resG Y h x) Q = rsT x Q := by
  rw [← rsT_of_le h, rsT_rsT h hQ]

theorem rsT_app {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (x : Γ(Y, U)) {Q : Z.Opens} (hQ : Q ≤ f ⁻¹ᵁ U) :
    rsT ((f.app U).hom x) Q = pbT f x Q := by
  rw [rsT_of_le hQ, pbT_of_le f hQ]
  rfl

theorem pbT_pbT {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) {O₀ : X.Opens} {O₁ : Y.Opens} {O₂ : Z.Opens}
    (h₁ : O₁ ≤ g ⁻¹ᵁ O₀) (h₂ : O₂ ≤ f ⁻¹ᵁ O₁) (s : Γ(X, O₀)) :
    pbT f (pbT g s O₁) O₂ = pbT (f ≫ g) s O₂ := by
  rw [pbT_of_le g h₁, pbT_of_le f h₂, pbT_of_le (f ≫ g) (h₂.trans (f.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE f g O₀ O₁ O₂ h₁ h₂)

theorem constFn_top_appTop {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) (x : Γ(Sp R, ⊤)) :
    constFn q ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = q.appTop.hom x := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = x := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  unfold constFn
  rw [e]
  exact congrArg (fun φ => φ.hom x) (Scheme.Hom.appLE_eq_app (f := q) (U := ⊤))

theorem preimage_le_of_eps {k : Type} [Field k] {B X : Scheme.{0}} (q : B ⟶ Sp (DualNumber k)) (π₁ π₂ : B ⟶ X)
    (e : ∀ W : X.Opens, Γ(X, W) → Γ(B, π₂ ⁻¹ᵁ W))
    (hid : ∀ (W : X.Opens) (f : Γ(X, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) +
      constFn q (π₂ ⁻¹ᵁ W) DualNumber.eps * e W f) (W : X.Opens) : π₂ ⁻¹ᵁ W ≤ π₁ ⁻¹ᵁ W := by
  by_contra h
  have h1 := hid W 1
  rw [pbT, dite_eq_right h, pbT_one π₂ le_rfl] at h1
  have hu : (1 + constFn q (π₂ ⁻¹ᵁ W) DualNumber.eps * e W 1) *
      (1 - constFn q (π₂ ⁻¹ᵁ W) DualNumber.eps * e W 1) = 1 := by
    linear_combination (-(e W 1) ^ 2) * constFn_eps_sq q (π₂ ⁻¹ᵁ W)
  rw [← h1, zero_mul] at hu
  apply h
  intro y hy
  exfalso
  haveI : Nonempty (π₂ ⁻¹ᵁ W) := ⟨⟨y, hy⟩⟩
  exact zero_ne_one hu

theorem rsT_inv_mul {Y : Scheme.{0}} {U : Y.Opens} (u : Γ(Y, U)ˣ) {Q : Y.Opens} (hQ : Q ≤ U) :
    rsT (↑(u⁻¹) : Γ(Y, U)) Q * rsT (u : Γ(Y, U)) Q = 1 := by
  rw [← rsT_mul, Units.inv_mul, rsT_one hQ]

theorem rsT_res_val {Y : Scheme.{0}} {U V : Y.Opens} (h : V ≤ U) (u : Γ(Y, U)ˣ) {Q : Y.Opens} (hQ : Q ≤ V) :
    rsT ((res h u : Γ(Y, V)ˣ) : Γ(Y, V)) Q = rsT (u : Γ(Y, U)) Q :=
  rsT_resG h (u : Γ(Y, U)) hQ

theorem rsT_pullU_val {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (u : Γ(Y, U)ˣ) {Q : Z.Opens}
    (hQ : Q ≤ f ⁻¹ᵁ U) : rsT ((pullU f U u : Γ(Z, f ⁻¹ᵁ U)ˣ) : Γ(Z, f ⁻¹ᵁ U)) Q = pbT f (u : Γ(Y, U)) Q :=
  rsT_app f U (u : Γ(Y, U)) hQ

theorem rsT_pull_g {Y Z : Scheme.{0}} (L : LB Y) (f : Z ⟶ Y) (a b : L.ι) (Q : Z.Opens)
    (hQ : Q ≤ f ⁻¹ᵁ (L.U a ⊓ L.U b)) (hQ' : Q ≤ (L.pull f).U (fun _ => a) ⊓ (L.pull f).U (fun _ => b)) :
    rsT ((L.pull f).g (fun _ => a) (fun _ => b) : Γ(Z, (L.pull f).U (fun _ => a) ⊓ (L.pull f).U (fun _ => b))) Q =
      pbT f (L.g a b : Γ(Y, L.U a ⊓ L.U b)) Q := by
  simp only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one]
  erw [rsT_res_val _ _ hQ', rsT_pullU_val _ _ _ hQ]

theorem isGen_rel {B X : Scheme.{0}} (L : LB X) (π₁ π₂ : B ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂))
    (hw : w.IsGen) (a b : L.ι) (Q : B.Opens) (hQ1 : Q ≤ π₁ ⁻¹ᵁ (L.U a ⊓ L.U b))
    (hQ2 : Q ≤ π₂ ⁻¹ᵁ (L.U a ⊓ L.U b)) :
    rsT (w.s (fun _ => a, fun _ => a)).val Q * pbT π₁ (L.g a b).val Q =
      pbT π₂ (L.g a b).val Q * rsT (w.s (fun _ => b, fun _ => b)).val Q := by
  have hQa : Q ≤ ((L.pull π₂).div (L.pull π₁)).U (fun _ => a, fun _ => a) :=
    fun y hy => ⟨Set.mem_iInter.2 fun _ => (hQ2 hy).1, Set.mem_iInter.2 fun _ => (hQ1 hy).1⟩
  have hQb : Q ≤ ((L.pull π₂).div (L.pull π₁)).U (fun _ => b, fun _ => b) :=
    fun y hy => ⟨Set.mem_iInter.2 fun _ => (hQ2 hy).2, Set.mem_iInter.2 fun _ => (hQ1 hy).2⟩
  have hQab := le_inf hQa hQb
  have h := congrArg (fun u => rsT (Units.val u) Q) (hw (fun _ => a, fun _ => a) (fun _ => b, fun _ => b))
  rw [rsT_res_val _ _ hQab, Units.val_mul, rsT_mul, rsT_res_val _ _ hQab] at h
  rw [h]
  simp only [LB.div]
  rw [Units.val_mul, rsT_mul]
  erw [rsT_res_val _ _ hQab]
  have hM := rsT_pull_g L π₂ a b Q hQ2 (le_inf (hQa.trans inf_le_left) (hQb.trans inf_le_left))
  have hN := rsT_pull_g L π₁ a b Q hQ1 (le_inf (hQa.trans inf_le_right) (hQb.trans inf_le_right))
  rw [← map_inv]
  erw [rsT_res_val _ _ hQab]
  have hI := rsT_inv_mul ((L.pull π₁).g (fun _ => a) (fun _ => b))
    (le_inf (hQa.trans inf_le_right) (hQb.trans inf_le_right))
  rw [hN] at hI
  rw [hM]
  rw [show ∀ x y z t : Γ(B, Q), x * y * z * t = x * z * (y * t) from fun _ _ _ _ => by ring]
  erw [hI]
  exact _root_.mul_one _

theorem unit_mul_one_add_eps : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (ed : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun r => (ρ r).snd) V jj ed pb → (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → ∃ κ : (DualNumber k)ˣ, ∀ i, rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) = constFn B'.hom (π₂ ⁻¹ᵁ V i) κ.val * (1 + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (pb i) (π₂ ⁻¹ᵁ V i)) := by
  intro k _ R _ P ρ B' _ π₁ π₂ h₁ _ _ A₀ _ m₀ _ pr hpr _ J V jj ed pb hconn hid w hw
  obtain ⟨-, hcov, hVU, hcoc⟩ := hconn
  have hle : ∀ W, π₂ ⁻¹ᵁ W ≤ π₁ ⁻¹ᵁ W :=
    preimage_le_of_eps B'.hom π₁ π₂ (fun W f => pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) hid
  have hpre : ∀ U, π₂ ⁻¹ᵁ U = pr ⁻¹ᵁ (m₀ ⁻¹ᵁ U) := fun U => by rw [← hpr]; rfl
  have hE2 : ∀ O : B'.left.Opens, constFn B'.hom O DualNumber.eps * constFn B'.hom O DualNumber.eps = 0 :=
    fun O => constFn_eps_sq B'.hom O
  have hchart : ∀ i, π₂ ⁻¹ᵁ V i ≤ ((P.L.pull π₂).div (P.L.pull π₁)).U (fun _ => jj i, fun _ => jj i) :=
    fun i y hy => ⟨Set.mem_iInter.2 fun _ => hVU i hy, Set.mem_iInter.2 fun _ => hVU i (hle _ hy)⟩
  have hcovB : (⊤ : B'.left.Opens) ≤ ⨆ i, π₂ ⁻¹ᵁ V i := by
    have := GlobalTheory.KS.le_iSup_inf_preimage π₂ V hcov ⊤
    simpa only [top_inf_eq] using this

  let u : ∀ i, Γ(B'.left, π₂ ⁻¹ᵁ V i) := fun i => rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i)
  let E : ∀ O : B'.left.Opens, Γ(B'.left, O) := fun O => constFn B'.hom O DualNumber.eps
  let Pf : ∀ i, Γ(B'.left, π₂ ⁻¹ᵁ V i) := fun i => pbT pr (pb i) (π₂ ⁻¹ᵁ V i)
  let t : ∀ i, Γ(B'.left, π₂ ⁻¹ᵁ V i) := fun i => u i * (1 - E _ * Pf i)
  let s : ∀ i, Γ(B'.left, π₂ ⁻¹ᵁ V i) := fun i =>
    rsT ((w.s (fun _ => jj i, fun _ => jj i))⁻¹).val (π₂ ⁻¹ᵁ V i) * (1 + E _ * Pf i)

  have hres : ∀ i i', rsT (u i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') =
      rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') ∧
      rsT (Pf i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = pbT pr (pb i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') ∧
      rsT (E (π₂ ⁻¹ᵁ V i)) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = E (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') := by
    intro i i'
    refine ⟨rsT_rsT (hchart i) inf_le_left _, rsT_pbT pr (hpre (V i)).le inf_le_left _,
      rsT_constFn B'.hom inf_le_left _⟩
  have hres' : ∀ i i', rsT (u i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') =
      rsT (w.s (fun _ => jj i', fun _ => jj i')).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') ∧
      rsT (Pf i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') ∧
      rsT (E (π₂ ⁻¹ᵁ V i')) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = E (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') := by
    intro i i'
    refine ⟨rsT_rsT (hchart i') inf_le_right _, rsT_pbT pr (hpre (V i')).le inf_le_right _,
      rsT_constFn B'.hom inf_le_right _⟩

  have key : ∀ i i', rsT (w.s (fun _ => jj i', fun _ => jj i')).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') =
      rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') *
        (1 + E _ * (pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') - pbT pr (pb i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i'))) := by
    intro i i'
    have hVV : V i ⊓ V i' ≤ P.L.U (jj i) ⊓ P.L.U (jj i') := inf_le_inf (hVU i) (hVU i')
    have hQ2 : π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i' ≤ π₂ ⁻¹ᵁ (V i ⊓ V i') := le_rfl
    have hQ1 : π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i' ≤ π₁ ⁻¹ᵁ (V i ⊓ V i') := hQ2.trans (hle _)
    have rel := isGen_rel P.L π₁ π₂ w hw (jj i) (jj i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')
      (hQ1.trans (π₁.preimage_mono hVV)) (hQ2.trans (π₂.preimage_mono hVV))
    have h := hid (V i ⊓ V i') (rsT (P.L.g (jj i) (jj i')).val (V i ⊓ V i'))
    rw [hcoc i i', pbT_mul, pbT_sub, pbT_pbT pr m₀ (m₀.preimage_mono hVV) (hpre _).le, hpr,
      pbT_rsT pr (m₀.preimage_mono inf_le_right) (hpre _).le, pbT_rsT pr (m₀.preimage_mono inf_le_left) (hpre _).le,
      pbT_rsT π₁ hVV (hle _), pbT_rsT π₂ hVV le_rfl] at h
    have hQeq : π₂ ⁻¹ᵁ (V i ⊓ V i') = π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i' := rfl
    rw [hQeq] at h
    have hG : pbT π₂ ((P.L.g (jj i) (jj i'))⁻¹).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') *
        pbT π₂ (P.L.g (jj i) (jj i')).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = 1 := by
      rw [← pbT_mul, Units.inv_mul, pbT_one π₂ (hQ2.trans (π₂.preimage_mono hVV))]
    rw [h] at rel
    linear_combination (-(rsT (w.s (fun _ => jj i', fun _ => jj i')).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') -
      rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') *
        (1 + E _ * (pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') - pbT pr (pb i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i'))))) * hG
      - pbT π₂ ((P.L.g (jj i) (jj i'))⁻¹).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') * rel

  have ht : ∀ i i', rsT (t i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = rsT (t i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') := by
    intro i i'
    obtain ⟨a1, a2, a3⟩ := hres i i'
    obtain ⟨b1, b2, b3⟩ := hres' i i'
    simp only [t, rsT_mul, rsT_sub, rsT_one inf_le_left, rsT_one inf_le_right, a1, a2, a3, b1, b2, b3, key i i']
    linear_combination (rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') *
      (pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') - pbT pr (pb i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')) *
      pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')) * hE2 _
  have hts : ∀ i, t i * s i = 1 := by
    intro i
    have hinv := rsT_inv_mul (w.s (fun _ => jj i, fun _ => jj i)) (hchart i)
    simp only [t, s, u]
    linear_combination (1 - E _ * Pf i * (E _ * Pf i)) * hinv - (Pf i * Pf i) * hE2 _
  have hs : ∀ i i', rsT (s i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = rsT (s i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') := by
    intro i i'
    have e1 := congrArg (fun f => rsT f (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')) (hts i)
    have e2 := congrArg (fun f => rsT f (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')) (hts i')
    simp only [rsT_mul, rsT_one inf_le_left, rsT_one inf_le_right] at e1 e2
    rw [← ht i i'] at e2
    linear_combination rsT (s i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') * e1 - rsT (s i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') * e2
  obtain ⟨T, hT⟩ := GlobalTheory.KS.exists_rsT_eq (fun i => π₂ ⁻¹ᵁ V i) (fun _ => le_top) hcovB t ht
  obtain ⟨S, hS⟩ := GlobalTheory.KS.exists_rsT_eq (fun i => π₂ ⁻¹ᵁ V i) (fun _ => le_top) hcovB s hs
  have hTS : T * S = 1 := by
    refine GlobalTheory.KS.eq_of_rsT_eq (fun i => π₂ ⁻¹ᵁ V i) (fun _ => le_top) hcovB _ _ fun i => ?_
    rw [rsT_mul, hT, hS, hts, rsT_one le_top]

  have hab : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback P.isAb h₁
  have hbij := GlobalTheory.allSixLaws.1.globalFns (Sp (DualNumber k)) B' hab
  obtain ⟨x, hx⟩ := hbij.2 T
  obtain ⟨y, hy⟩ := hbij.2 S
  have hxy : x * y = 1 := hbij.1 (by rw [map_mul, hx, hy, hTS, map_one])
  refine ⟨⟨(Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom x,
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom y,
    by rw [← map_mul, hxy, map_one], by rw [← map_mul, _root_.mul_comm, hxy, map_one]⟩, fun i => ?_⟩
  have hκ : constFn B'.hom ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom x) = T :=
    (constFn_top_appTop B'.hom x).trans hx
  have hc := hT i
  rw [← hκ, rsT_constFn B'.hom le_top] at hc
  simp only [t, u, Pf, E] at hc
  show u i = _
  simp only [u]
  linear_combination (-(1 + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (pb i) (π₂ ⁻¹ᵁ V i))) * hc +
    (rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) * pbT pr (pb i) (π₂ ⁻¹ᵁ V i) ^ 2) * hE2 _

end GlobalTheory.ConnUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEqUnitMulOneAddEpsPotentialStatement
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
theorem _root_.GlobalTheory.T.lineBundleIso_eq_unit_mul_one_add_eps_potential : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (ed : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun r => (ρ r).snd) V jj ed pb → (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → ∃ κ : (DualNumber k)ˣ, ∀ i, rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) = constFn B'.hom (π₂ ⁻¹ᵁ V i) κ.val * (1 + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (pb i) (π₂ ⁻¹ᵁ V i)) := by
  first | exact @GlobalTheory.ConnUnit.unit_mul_one_add_eps | exact GlobalTheory.ConnUnit.unit_mul_one_add_eps | (intros; apply GlobalTheory.ConnUnit.unit_mul_one_add_eps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalDerivationLiftingPrincipalPolarizationEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalDerivationLiftingPrincipalPolarizationEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatConn.Vert
open GlobalTheory.KS

theorem transport {k : Type} [Field k] {R : Type} [CommRing R] (A : Over (Sp R)) (L : LB A.left)
    (A₀ B₀ : Over (Sp k)) (m₀ : A₀.left ⟶ A.left) (e : B₀.left ⟶ A₀.left) (he : e ≫ A₀.hom = B₀.hom)
    (D' : R → k) {J : Type} (V : J → A.left.Opens) (jj : J → L.ι)
    (v : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (q : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i))
    (hc : GlobalTheory.HeatConn.IsConnK A L A₀ m₀ D' V jj v q) :
    GlobalTheory.HeatConn.IsConnK A L B₀ (e ≫ m₀) D' V jj (fun W f => pbT e (v W f) ((e ≫ m₀) ⁻¹ᵁ W))
      (fun i => pbT e (q i) ((e ≫ m₀) ⁻¹ᵁ V i)) := by
  obtain ⟨hd, hcov, hle, htr⟩ := hc
  have le : ∀ W : A.left.Opens, (e ≫ m₀) ⁻¹ᵁ W ≤ e ⁻¹ᵁ (m₀ ⁻¹ᵁ W) := fun W => le_rfl
  have app : ∀ W (f : Γ(A.left, W)), pbT e ((m₀.app W).hom f) ((e ≫ m₀) ⁻¹ᵁ W) = ((e ≫ m₀).app W).hom f := by
    intro W f
    rw [AdjDlog.app_eq_pbT m₀, AdjDlog.app_eq_pbT (e ≫ m₀), AdjDlog.pbT_pbT e m₀ le_rfl (le W)]
  refine ⟨⟨fun W _ f f' => ?_, fun W _ f f' => ?_, fun W W' h _ f => ?_, fun W _ r => ?_⟩, hcov, hle, fun i i' => ?_⟩
  · simp only [hd.add W le_top, pbT_add]
  · rw [hd.mul W le_top, pbT_add, pbT_mul, pbT_mul, app, app]
  · show pbT e (v W' (resG A.left h f)) _ = rsT (pbT e (v W f) _) _
    rw [hd.res W W' h le_top, pbT_rsT e (m₀.preimage_mono h) (le W'), rsT_pbT e (le W) ((e ≫ m₀).preimage_mono h)]
  · show pbT e (v W (constFn A.hom W r)) _ = _
    rw [hd.base W le_top, pbT_constFn A₀.hom e (le W), he]
  · show pbT e (v (V i ⊓ V i') _) _ = _
    rw [htr i i', pbT_mul, pbT_sub, AdjDlog.pbT_pbT e m₀ (m₀.preimage_mono (le_inf (inf_le_left.trans (hle i)) (inf_le_right.trans (hle i')))) (le _),
      pbT_rsT e (m₀.preimage_mono inf_le_left) (le _), pbT_rsT e (m₀.preimage_mono inf_le_right) (le _),
      rsT_pbT e (le _) ((e ≫ m₀).preimage_mono inf_le_left), rsT_pbT e (le _) ((e ≫ m₀).preimage_mono inf_le_right)]

theorem coeff_const (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (x₀ : R →+* k)
    (P₀ : PolAV (Sp k)) (θ : P₀.A.left ⟶ P.A.left) (hθ : IsPullback θ P₀.A.hom P.A.hom (spMap x₀))
    {n : ℕ} (u : Fin n → (epsR k ⟶ P₀.A)) (hu : IsLieBasis u)
    (dd : Fin n → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)) (hdd : ∀ a, IsInvDer (u a) (dd a))
    (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(P₀.A.left, θ ⁻¹ᵁ W))
    (hv : LocDerK P₀.A.hom P.A.hom θ (fun _ => (0 : k)) ⊤ v) :
    ∃ c : Fin n → k, ∀ W f, v W f = ∑ a, constFn P₀.A.hom (θ ⁻¹ᵁ W) (c a) * dd a (θ ⁻¹ᵁ W) ((θ.app W).hom f) := by
  have hs : Smooth P₀.A.hom := P₀.isAb.smooth
  have hU : IsAffineOpen (⊤ : (Sp R).Opens) := isAffineOpen_top _
  obtain ⟨c0, hc0, -⟩ := GlobalTheory.KSUniq.coeff_id hs hu hdd (spMap x₀) P.A.hom θ hθ hU ⊤ (fun _ _ => trivial) v
    (fun W _ => hv.add W le_top) (fun W _ => hv.mul W le_top) (fun W W' h _ => hv.res W W' h le_top) (fun W _ r => by
      have e1 : pbT P.A.hom r W = constFn P.A.hom W ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) := by
        rw [pbT_of_le _ (by simp)]
        simp [constFn]
      rw [e1, hv.base W le_top]
      simp [constFn])
  have hGF := GlobalTheory.allSixLaws.1.globalFns
  choose s hs' using fun a => (hGF _ P₀.A P₀.isAb).2 (rsT (c0 a) ⊤)
  refine ⟨fun a => (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (s a), fun W f => ?_⟩
  rw [hc0 W le_top f]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [← rsT_rsT (O₁ := ⊤) (by simp) le_top, ← hs' a, rsT_of_le le_top]
  simp [constFn]
  rfl

theorem cob_of_conn (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R))
    (P₀ : PolAV (Sp k)) (θ : P₀.A.left ⟶ P.A.left)
    {n : ℕ} (u : Fin n → (epsR k ⟶ P₀.A)) (hu : IsLieBasis u)
    (dd : Fin n → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)) (hdd : ∀ a, IsInvDer (u a) (dd a))
    (φ : Fin n → C1 (fun i => θ ⁻¹ᵁ P.L.U i)) (hφ : IsDlog θ P.L dd φ) (hcoc : ∀ a, IsCoc _ (φ a))
    {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι)
    (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(P₀.A.left, θ ⁻¹ᵁ W)) (q : ∀ i, Γ(P₀.A.left, θ ⁻¹ᵁ V i))
    (hc : GlobalTheory.HeatConn.IsConnK P.A P.L P₀.A θ (fun _ => 0) V jj v q) (c : Fin n → k)
    (hcv : ∀ W f, v W f = ∑ a, constFn P₀.A.hom (θ ⁻¹ᵁ W) (c a) * dd a (θ ⁻¹ᵁ W) ((θ.app W).hom f)) :
    IsCob _ (lc P₀.A.hom c φ) := by
  obtain ⟨-, hcov, hle, htr⟩ := hc
  have hres : ∀ a, ∀ W W' (f : Γ(P₀.A.left, W)), W' ≤ W → dd a W' (rsT f W') = rsT (dd a W f) W' :=
    fun a => ((GlobalTheory.KS.InvField.main k P₀.A (u a) (hu.1 a)).2 (dd a) (hdd a)).2.2.1
  have hcovθ : ⨆ p, θ ⁻¹ᵁ V p = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    have hz : θ z ∈ ⨆ i, V i := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  refine GlobalTheory.T.isCechOneCoboundary_of_refinement (fun i => θ ⁻¹ᵁ P.L.U i) (lc P₀.A.hom c φ) (GlobalTheory.KSUniq.isCoc_lc _ _ _ hcoc)
    (fun p => θ ⁻¹ᵁ V p) jj (fun p => θ.preimage_mono (hle p)) hcovθ q (fun p p' => ?_)
  have hWU : V p ⊓ V p' ≤ P.L.U (jj p) ⊓ P.L.U (jj p') := le_inf (inf_le_left.trans (hle p)) (inf_le_right.trans (hle p'))
  have hOU : θ ⁻¹ᵁ (V p ⊓ V p') ≤ θ ⁻¹ᵁ P.L.U (jj p) ⊓ θ ⁻¹ᵁ P.L.U (jj p') := θ.preimage_mono hWU
  change rsT (lc P₀.A.hom c φ (jj p) (jj p')) (θ ⁻¹ᵁ (V p ⊓ V p')) =
    rsT (q p') (θ ⁻¹ᵁ (V p ⊓ V p')) - rsT (q p) (θ ⁻¹ᵁ (V p ⊓ V p'))
  have E := htr p p'
  rw [hcv] at E
  set g := (P.L.g (jj p) (jj p')).val with hg
  have r1 : rsT (pbT θ g (θ ⁻¹ᵁ P.L.U (jj p) ⊓ θ ⁻¹ᵁ P.L.U (jj p'))) (θ ⁻¹ᵁ (V p ⊓ V p')) = pbT θ g (θ ⁻¹ᵁ (V p ⊓ V p')) :=
    rsT_pbT θ (O₀ := P.L.U (jj p) ⊓ P.L.U (jj p')) (O₁ := θ ⁻¹ᵁ P.L.U (jj p) ⊓ θ ⁻¹ᵁ P.L.U (jj p')) le_rfl hOU _
  have e1 : (θ.app (V p ⊓ V p')).hom (rsT g (V p ⊓ V p')) =
      rsT (pbT θ g (θ ⁻¹ᵁ P.L.U (jj p) ⊓ θ ⁻¹ᵁ P.L.U (jj p'))) (θ ⁻¹ᵁ (V p ⊓ V p')) := by
    rw [AdjDlog.app_eq_pbT, pbT_rsT θ hWU le_rfl, r1]
  have e2 : ∀ a, dd a (θ ⁻¹ᵁ (V p ⊓ V p')) ((θ.app (V p ⊓ V p')).hom (rsT g (V p ⊓ V p'))) =
      pbT θ g (θ ⁻¹ᵁ (V p ⊓ V p')) * rsT (φ a (jj p) (jj p')) (θ ⁻¹ᵁ (V p ⊓ V p')) := fun a => by
    rw [e1, hres a _ _ _ hOU, ← hφ a (jj p) (jj p'), rsT_mul, r1]
  simp only [e2] at E
  have hunit : IsUnit (pbT θ g (θ ⁻¹ᵁ (V p ⊓ V p'))) := AdjDlog.isUnit_pbT θ (θ.preimage_mono hWU) _
  refine (hunit.mul_left_cancel ?_).symm
  rw [← E, lc, rsT_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rsT_mul, rsT_constFn _ hOU]
  ring

theorem vert_polAV (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (x₀ : R →+* k)
    (P₀ : PolAV (Sp k)) (θ : P₀.A.left ⟶ P.A.left) (hθ : IsPullback θ P₀.A.hom P.A.hom (spMap x₀))
    (hiso : LBIso P₀.L (P.L.pull θ)) {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι)
    (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(P₀.A.left, θ ⁻¹ᵁ W)) (q : ∀ i, Γ(P₀.A.left, θ ⁻¹ᵁ V i))
    (hc : GlobalTheory.HeatConn.IsConnK P.A P.L P₀.A θ (fun _ => 0) V jj v q) (W : P.A.left.Opens) (f : Γ(P.A.left, W)) :
    v W f = 0 := by
  haveI : IsCommMonObj P₀.A := P₀.isAb.comm
  obtain ⟨u, hu⟩ := GlobalTheory.CM.TenDim.exists_isLieBasis P₀.A P₀.smoothDim
  choose dd hdd using fun a => (GlobalTheory.KS.InvField.main k P₀.A (u a) (hu.1 a)).1
  obtain ⟨⟨φ, hφ⟩, hind⟩ := GlobalTheory.KS.DlogPol.dlog_independent k P₀ P₀.g u dd hu hdd _ θ P.L P.isLB hiso
  obtain ⟨hcoc, hcob⟩ := hind φ hφ
  obtain ⟨c, hcv⟩ := coeff_const k R P x₀ P₀ θ hθ u hu dd hdd v hc.1
  have c0 := hcob c (cob_of_conn k R P P₀ θ u hu dd hdd φ hφ hcoc V jj v q hc c hcv)
  rw [hcv]
  simp [c0, constFn]

theorem vert_eq_zero : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (x₀ : R →+* k) (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap x₀) m₀ → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (q : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun _ => 0) V jj v q → ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), v W f = 0 := by
  intro k _ R _ P x₀ A₀ _ m₀ hm J V jj v q hc W f
  obtain ⟨P₀, θ, hθ, hiso⟩ := GlobalTheory.UniformisedModel.exists_polBaseChange GlobalTheory.allSixLaws.1.polBaseChange (spMap x₀) P
  obtain ⟨e, -, he⟩ := grpPullback_iso hθ hm
  subst he
  have hw : e.hom.left ≫ A₀.hom = P₀.A.hom := Over.w e.hom
  have hc' := transport P.A P.L A₀ P₀.A m₀ e.hom.left hw (fun _ => 0) V jj v q hc
  have h0 := vert_polAV k R P x₀ P₀ _ hθ.1 hiso V jj _ _ hc' W f
  haveI : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]⟩⟩
  have hle : m₀ ⁻¹ᵁ W ≤ (inv e.hom.left) ⁻¹ᵁ ((e.hom.left ≫ m₀) ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, IsIso.inv_hom_id_assoc]
  have key := congrArg (fun s => pbT (inv e.hom.left) s (m₀ ⁻¹ᵁ W)) h0
  rw [AdjDlog.pbT_pbT (inv e.hom.left) e.hom.left (U := m₀ ⁻¹ᵁ W) (V := (e.hom.left ≫ m₀) ⁻¹ᵁ W) le_rfl hle, IsIso.inv_hom_id, LinDir.pbT_id, pbT_zero] at key
  exact key

end GlobalTheory.HeatConn.Vert
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalDerivationLiftingPrincipalPolarizationEqStatement
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
theorem _root_.GlobalTheory.T.vertical_derivation_lifting_principalPolarization_eq_zero : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (x₀ : R →+* k) (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap x₀) m₀ → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (q : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun _ => 0) V jj v q → ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), v W f = 0 := by
  first | exact @GlobalTheory.HeatConn.Vert.vert_eq_zero | exact GlobalTheory.HeatConn.Vert.vert_eq_zero | (intros; apply GlobalTheory.HeatConn.Vert.vert_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionClosedFibreEqDerivationIdentification
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

theorem connK_eq_ident : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (ed : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun r => (ρ r).snd) V jj ed pb → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) ∧ ∃ κ : (DualNumber k)ˣ, ∀ i, rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) = constFn B'.hom (π₂ ⁻¹ᵁ V i) κ.val * (1 + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (pb i) (π₂ ⁻¹ᵁ V i)) := by
  intro k _ R _ P ρ B' _ π₁ π₂ h₁ h₂ hag A₀ _ m₀ hm₀ pr hpr hprb J V jj ed pb hc w hw
  obtain ⟨dB, hdB, hid⟩ := GlobalTheory.T.exists_fibre_derivation_of_two_dualNumber_pullbacks k R P ρ B' π₁ π₂ h₁ h₂ hag A₀ m₀ hm₀ pr hpr hprb
  obtain ⟨q, hq⟩ := GlobalTheory.T.connection_closedFibre_of_pulledBack_iso k R P ρ B' π₁ π₂ h₁ h₂ hag A₀ m₀ hm₀ pr hpr hprb V jj hc.2.1 hc.2.2.1 dB hdB hid w hw
  have hv : GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun _ => 0) V jj (fun W f => ed W f - dB W f) (fun i => pb i - q i) := by
    refine ⟨⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_, fun W hW r => ?_⟩, hc.2.1, hc.2.2.1, fun i i' => ?_⟩
    · simp only [hc.1.add W hW, hdB.add W hW]; ring
    · simp only [hc.1.mul W hW, hdB.mul W hW]; ring
    · rw [hc.1.res W W' h hW, hdB.res W W' h hW, GlobalTheory.KS.rsT_sub]
    · rw [hc.1.base W hW, hdB.base W hW, sub_self]; simp [constFn]
    · dsimp only
      rw [hc.2.2.2 i i', hq.2.2.2 i i', GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_sub]; ring
  have e : ∀ W f, ed W f = dB W f := fun W f =>
    sub_eq_zero.1 (GlobalTheory.T.vertical_derivation_lifting_principalPolarization_eq_zero k R P ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) A₀ m₀ hm₀ V jj _ _ hv W f)
  have hA : (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) := fun W f => by rw [e]; exact hid W f
  exact ⟨hA, GlobalTheory.T.lineBundleIso_eq_unit_mul_one_add_eps_potential k R P ρ B' π₁ π₂ h₁ h₂ hag A₀ m₀ hm₀ pr hpr hprb V jj ed pb hc hA w hw⟩

end GlobalTheory.HeatConn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionClosedFibreEqDerivationIdentificationStatement
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
theorem _root_.GlobalTheory.T.connection_closedFibre_eq_derivation_identification : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (ed : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun r => (ρ r).snd) V jj ed pb → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) ∧ ∃ κ : (DualNumber k)ˣ, ∀ i, rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) = constFn B'.hom (π₂ ⁻¹ᵁ V i) κ.val * (1 + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (pb i) (π₂ ⁻¹ᵁ V i)) := by
  first | exact @GlobalTheory.HeatConn.connK_eq_ident | exact GlobalTheory.HeatConn.connK_eq_ident | (intros; apply GlobalTheory.HeatConn.connK_eq_ident <;> assumption)
end
