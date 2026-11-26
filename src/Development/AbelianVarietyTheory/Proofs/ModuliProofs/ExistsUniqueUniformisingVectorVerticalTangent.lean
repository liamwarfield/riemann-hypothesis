module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationUniformisedAbelianVarietyUniqueVec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationOfFibreOfKillsBase
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationOfFibreOfKillsBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.VertFib

abbrev epsPt : Sp ℂ ⟶ Sp (DualNumber ℂ) := spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

abbrev epsStr : Sp (DualNumber ℂ) ⟶ Sp ℂ := spMap (algebraMap ℂ (DualNumber ℂ))

def ringVal {A : Type} [CommRing A] {X : Scheme.{0}} (v : Sp A ⟶ X) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((v.appLE W ⊤ h).hom f)

theorem epsPt_epsStr : epsPt ≫ epsStr = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem top_le_of_epsPt {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (W : X.Opens)
    (h : ⊤ ≤ (epsPt ≫ v) ⁻¹ᵁ W) : ⊤ ≤ v ⁻¹ᵁ W := by
  intro q _
  have hq : (q : PrimeSpectrum (DualNumber ℂ)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)]
    intro x hx
    have hx0 : TrivSqZeroExt.fst x = 0 := hx
    apply q.isPrime.mem_of_pow_mem 2
    have : x ^ 2 = 0 := by
      rw [pow_two]; ext <;> simp [hx0]
    rw [this]; exact q.asIdeal.zero_mem
  obtain ⟨s, rfl⟩ := hq
  exact h (Set.mem_univ s)

theorem top_le_epsPt {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (W : X.Opens)
    (h : ⊤ ≤ v ⁻¹ᵁ W) : ⊤ ≤ (epsPt ≫ v) ⁻¹ᵁ W := fun _ _ => h (Set.mem_univ _)

theorem ringVal_appLE {A : Type} [CommRing A] {X Y : Scheme.{0}} (v : Sp A ⟶ Y) (m : Y ⟶ X) (W : X.Opens) (O : Y.Opens)
    (e : O ≤ m ⁻¹ᵁ W) (h : ⊤ ≤ v ⁻¹ᵁ O) (h' : ⊤ ≤ (v ≫ m) ⁻¹ᵁ W) (f : Γ(X, W)) :
    ringVal v O h ((m.appLE W O e).hom f) = ringVal (v ≫ m) W h' f := by
  rw [ringVal, ringVal, ← CommRingCat.comp_apply (m.appLE W O e), Scheme.Hom.appLE_comp_appLE]

theorem ringVal_app {A : Type} [CommRing A] {X Y : Scheme.{0}} (v : Sp A ⟶ Y) (m : Y ⟶ X) (W : X.Opens)
    (h : ⊤ ≤ v ⁻¹ᵁ (m ⁻¹ᵁ W)) (h' : ⊤ ≤ (v ≫ m) ⁻¹ᵁ W) (f : Γ(X, W)) :
    ringVal v (m ⁻¹ᵁ W) h ((m.app W).hom f) = ringVal (v ≫ m) W h' f := by
  rw [Scheme.Hom.app_eq_appLE]
  exact ringVal_appLE v m W _ _ h h' f

theorem ringVal_spMap {A R : Type} [CommRing A] [CommRing R] (φ : R →+* A) (h : ⊤ ≤ spMap φ ⁻¹ᵁ ⊤) (s : Γ(Sp R, ⊤)) :
    ringVal (spMap φ) ⊤ h s = φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s) := by
  have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h2 := congrArg (fun g => g.hom s) h1
  have h3 : (spMap φ).appLE ⊤ ⊤ h = (spMap φ).appTop := (Scheme.Hom.app_eq_appLE (spMap φ) (U := ⊤)).symm
  rw [ringVal, h3]
  exact h2

theorem ringVal_congr {A : Type} [CommRing A] {X : Scheme.{0}} {v v' : Sp A ⟶ X} (e : v = v') (W : X.Opens)
    (h : ⊤ ≤ v ⁻¹ᵁ W) (h' : ⊤ ≤ v' ⁻¹ᵁ W) (f : Γ(X, W)) : ringVal v W h f = ringVal v' W h' f := by
  subst e; rfl

theorem ringVal_constFn {A R : Type} [CommRing A] [CommRing R] {X : Scheme.{0}} (v : Sp A ⟶ X) (p : X ⟶ Sp R)
    (φ : R →+* A) (hv : v ≫ p = spMap φ) (h : ⊤ ≤ v ⁻¹ᵁ ⊤) (r : R) :
    ringVal v ⊤ h (constFn p ⊤ r) = φ r := by
  refine (ringVal_appLE v p ⊤ ⊤ le_top h le_top _).trans ?_
  refine (ringVal_congr hv ⊤ _ le_top _).trans ((ringVal_spMap φ _ _).trans ?_)
  congr 1
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id_apply r

theorem snd_ringVal_const {X : Scheme.{0}} (z : Sp ℂ ⟶ X) (W : X.Opens) (h : ⊤ ≤ (epsStr ≫ z) ⁻¹ᵁ W) (f : Γ(X, W)) :
    TrivSqZeroExt.snd (ringVal (epsStr ≫ z) W h f) = 0 := by
  have hz : ⊤ ≤ z ⁻¹ᵁ W := by
    have := top_le_epsPt _ W h
    rwa [← Category.assoc, epsPt_epsStr, Category.id_comp] at this
  exact congrArg TrivSqZeroExt.snd
    ((ringVal_appLE epsStr z W ⊤ hz le_top h f).symm.trans (ringVal_spMap _ _ _))

theorem comp_eq_const {R : Type} [CommRing R] (x₀ : R →+* ℂ) {X : Scheme.{0}} (p : X ⟶ Sp R)
    (v : Sp (DualNumber ℂ) ⟶ X) (h₁ : epsPt ≫ v ≫ p = spMap x₀)
    (h₂ : ∀ r, TrivSqZeroExt.snd (ringVal v ⊤ le_top (constFn p ⊤ r)) = 0) :
    v ≫ p = epsStr ≫ spMap x₀ := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (v ≫ p)
  have hφ : v ≫ p = spMap ψ.hom := hψ.symm
  rw [hφ, ← Spec.map_comp] at h₁
  have h₃ := Spec.map_injective h₁
  rw [hφ, ← Spec.map_comp]
  congr 1
  refine RingHom.ext fun r => ?_
  have h₄ : TrivSqZeroExt.snd (ψ.hom r : DualNumber ℂ) = 0 :=
    (congrArg TrivSqZeroExt.snd (ringVal_constFn v p ψ.hom hφ le_top r)).symm.trans (h₂ r)
  have h₅ : TrivSqZeroExt.fst (ψ.hom r : DualNumber ℂ) = x₀ r := congrArg (fun g => g.hom r) h₃
  exact TrivSqZeroExt.ext h₅ h₄

end GlobalTheory.KS.VertFib


open GlobalTheory.KS.VertFib in
theorem GlobalTheory.KS.ptDer_of_fibre : ∀ (Y : Over (Sp ℂ)) (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y.left ⟶ X), IsPullback m Y.hom p (spMap x₀) → ∀ y : Sp ℂ ⟶ Y.left, y ≫ Y.hom = 𝟙 _ → (∀ δ, PtDer (y ≫ m) δ → (∀ r, δ ⊤ (constFn p ⊤ r) = 0) → ∃ δ₀, PtDer y δ₀ ∧ (∀ a, δ₀ ⊤ (constFn Y.hom ⊤ a) = 0) ∧ ∀ W f, ⊤ ≤ (y ≫ m) ⁻¹ᵁ W → δ W f = δ₀ (m ⁻¹ᵁ W) ((m.app W).hom f)) ∧ ∀ δ₀, PtDer y δ₀ → (∀ a, δ₀ ⊤ (constFn Y.hom ⊤ a) = 0) → (∀ W f, ⊤ ≤ (y ≫ m) ⁻¹ᵁ W → δ₀ (m ⁻¹ᵁ W) ((m.app W).hom f) = 0) → ∀ O f, ⊤ ≤ y ⁻¹ᵁ O → δ₀ O f = 0 := by
  intro Y R _ x₀ X p m hP y hy
  constructor
  · intro δ hδ h0
    obtain ⟨v, ⟨hv, hvδ⟩, -⟩ := (GlobalTheory.T.germDerivation_iff_dualNumberPoint X (y ≫ m)).1 δ hδ
    have hvp : v ≫ p = epsStr ≫ spMap x₀ := by
      refine comp_eq_const x₀ p v ?_ fun r => (hvδ ⊤ le_top _).trans (h0 r)
      rw [← Category.assoc, hv, Category.assoc, hP.w, ← Category.assoc, hy, Category.id_comp]
    have hw₁ := hP.lift_fst v epsStr hvp
    have hw₂ := hP.lift_snd v epsStr hvp
    generalize hP.lift v epsStr hvp = w at hw₁ hw₂
    have hwy : epsPt ≫ w = y := by
      apply hP.hom_ext
      · rw [Category.assoc, hw₁, hv]
      · rw [Category.assoc, hw₂, epsPt_epsStr, hy]
    obtain ⟨δ₀, hδ₀, hw⟩ := (GlobalTheory.T.germDerivation_iff_dualNumberPoint Y.left y).2 w hwy
    refine ⟨δ₀, hδ₀, fun a => ?_, fun W f hW => ?_⟩
    · refine (hw ⊤ le_top _).symm.trans ?_
      exact congrArg TrivSqZeroExt.snd (ringVal_constFn w Y.hom _ hw₂ le_top a)
    · have h1 : ⊤ ≤ v ⁻¹ᵁ W := top_le_of_epsPt v W (by rw [hv]; exact hW)
      have h2 : ⊤ ≤ (w ≫ m) ⁻¹ᵁ W := by rw [hw₁]; exact h1
      refine (hvδ W h1 f).symm.trans (Eq.trans ?_ (hw (m ⁻¹ᵁ W) h2 _))
      exact congrArg TrivSqZeroExt.snd
        ((ringVal_congr hw₁.symm W h1 h2 f).trans (ringVal_app w m W h2 h2 f).symm)
  · intro δ₀ hδ₀ h0 hm O f hO
    obtain ⟨v, ⟨hv, hvδ⟩, -⟩ := (GlobalTheory.T.germDerivation_iff_dualNumberPoint Y.left y).1 δ₀ hδ₀
    have hvp : v ≫ Y.hom = epsStr := by
      have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
      have := comp_eq_const (RingHom.id ℂ) Y.hom v (by rw [← Category.assoc, hv, hy, hid])
        fun r => (hvδ ⊤ le_top _).trans (h0 r)
      rwa [hid, Category.comp_id] at this
    have hz : PtDer (y ≫ m) (fun _ _ => 0) := ⟨by simp, by simp, by simp⟩
    have hvm : v ≫ m = epsStr ≫ y ≫ m := by
      refine ((GlobalTheory.T.germDerivation_iff_dualNumberPoint X (y ≫ m)).1 _ hz).unique ⟨?_, fun W h g => ?_⟩ ⟨?_, fun W h g => ?_⟩
      · rw [← Category.assoc, hv]
      · have hW : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W := by
          have := top_le_epsPt _ W h
          rwa [← Category.assoc, hv] at this
        refine Eq.trans ?_ ((hvδ (m ⁻¹ᵁ W) h _).trans (hm W g hW))
        exact congrArg TrivSqZeroExt.snd (ringVal_app v m W h h g).symm
      · rw [← Category.assoc, epsPt_epsStr, Category.id_comp]
      · exact snd_ringVal_const (y ≫ m) W h g
    have hvc : v = epsStr ≫ y := by
      apply hP.hom_ext
      · rw [hvm, Category.assoc]
      · rw [hvp, Category.assoc, hy, Category.comp_id]
    have h1 : ⊤ ≤ v ⁻¹ᵁ O := top_le_of_epsPt v O (by rw [hv]; exact hO)
    refine (hvδ O h1 f).symm.trans ?_
    have h2 : ⊤ ≤ (epsStr ≫ y) ⁻¹ᵁ O := by rw [← hvc]; exact h1
    exact (congrArg TrivSqZeroExt.snd (ringVal_congr hvc O h1 h2 f)).trans (snd_ringVal_const y O h2 f)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationOfFibreOfKillsBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germDerivation_of_fibre_of_kills_base : ∀ (Y : Over (Sp ℂ)) (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y.left ⟶ X), IsPullback m Y.hom p (spMap x₀) → ∀ y : Sp ℂ ⟶ Y.left, y ≫ Y.hom = 𝟙 _ → (∀ δ, PtDer (y ≫ m) δ → (∀ r, δ ⊤ (constFn p ⊤ r) = 0) → ∃ δ₀, PtDer y δ₀ ∧ (∀ a, δ₀ ⊤ (constFn Y.hom ⊤ a) = 0) ∧ ∀ W f, ⊤ ≤ (y ≫ m) ⁻¹ᵁ W → δ W f = δ₀ (m ⁻¹ᵁ W) ((m.app W).hom f)) ∧ ∀ δ₀, PtDer y δ₀ → (∀ a, δ₀ ⊤ (constFn Y.hom ⊤ a) = 0) → (∀ W f, ⊤ ≤ (y ≫ m) ⁻¹ᵁ W → δ₀ (m ⁻¹ᵁ W) ((m.app W).hom f) = 0) → ∀ O f, ⊤ ≤ y ⁻¹ᵁ O → δ₀ O f = 0 := by
  first | exact @GlobalTheory.KS.ptDer_of_fibre | exact GlobalTheory.KS.ptDer_of_fibre | (intros; apply GlobalTheory.KS.ptDer_of_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueUniformisingVectorVerticalTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.VertFamily

variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)

private theorem valAt'_add' {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (W : X.Opens) (f f' : Γ(X, W)) :
    valAt' y W (f + f') = valAt' y W f + valAt' y W f' := by
  unfold valAt' valAt
  split_ifs <;> simp

private theorem valAt'_mul_of_top_le_preimage_open {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (W : X.Opens) (f f' : Γ(X, W)) :
    valAt' y W (f * f') = valAt' y W f * valAt' y W f' := by
  unfold valAt' valAt
  split_ifs <;> simp

private theorem valAt'_resG {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W W' : X.Opens} (hle : W' ≤ W)
    (h : ⊤ ≤ y ⁻¹ᵁ W') (f : Γ(X, W)) : valAt' y W' (resG X hle f) = valAt' y W f := by
  have hW : ⊤ ≤ y ⁻¹ᵁ W := fun x hx => hle (h hx)
  unfold valAt' valAt
  rw [dite_eq_left h, dite_eq_left hW]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

private theorem valAt'_constFn_top {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (p : X ⟶ Sp ℂ) (hp : y ≫ p = 𝟙 _) (a : ℂ) :
    valAt' y ⊤ (constFn p ⊤ a) = a := by
  have hq : ∀ (q : Sp ℂ ⟶ Sp ℂ) (e : ⊤ ≤ q ⁻¹ᵁ ⊤), q = 𝟙 _ →
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((q.appLE ⊤ ⊤ e).hom
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) = a := by
    rintro q e rfl
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    show (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (((Sp ℂ).presheaf.map (𝟙 (Opposite.op (⊤ : (Sp ℂ).Opens)))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) = a
    simp
  have e0 : ⊤ ≤ y ⁻¹ᵁ (⊤ : X.Opens) := fun _ _ => trivial
  unfold valAt' valAt constFn
  rw [dite_eq_left e0]
  refine Eq.trans ?_ (hq (y ≫ p) (fun _ _ => trivial) hp)
  congr 1
  rw [← CommRingCat.comp_apply]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE y p ⊤ ⊤ ⊤ _ e0)

theorem ex_over (z : Fin g → ℂ) : (u.ex z).left ≫ A.hom = 𝟙 _ := by
  exact (Over.w (u.ex z)).trans (by simp)

theorem differentiableAt_val (z : Fin g → ℂ) (O : A.left.Opens) (f : Γ(A.left, O)) (h : ⊤ ≤ (u.ex z).left ⁻¹ᵁ O) :
    DifferentiableAt ℂ (fun z' => valAt' (u.ex z').left O f) z := by
  obtain ⟨hO, hD⟩ := u.hol O f
  exact hD.differentiableAt (hO.mem_nhds h)

theorem ptDer_fderiv (z w : Fin g → ℂ) :
    PtDer (u.ex z).left (fun O f => fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w) := by
  constructor
  · intro O h f f'
    have e : (fun z' => valAt' (u.ex z').left O (f + f')) =
        (fun z' => valAt' (u.ex z').left O f) + fun z' => valAt' (u.ex z').left O f' := by
      funext z'
      exact valAt'_add' _ _ _ _
    rw [e, fderiv_add (differentiableAt_val u z O f h) (differentiableAt_val u z O f' h)]
    rfl
  · intro O h f f'
    have e : (fun z' => valAt' (u.ex z').left O (f * f')) =
        (fun z' => valAt' (u.ex z').left O f) * fun z' => valAt' (u.ex z').left O f' := by
      funext z'
      exact valAt'_mul_of_top_le_preimage_open _ _ _ _
    rw [e, fderiv_mul (differentiableAt_val u z O f h) (differentiableAt_val u z O f' h)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  · intro O O' hle h f
    have hev : (fun z' => valAt' (u.ex z').left O' (resG A.left hle f)) =ᶠ[nhds z]
        fun z' => valAt' (u.ex z').left O f := by
      filter_upwards [(u.hol O' (resG A.left hle f)).1.mem_nhds h] with z' hz'
      exact valAt'_resG _ hle hz' f
    rw [hev.fderiv_eq]

theorem fderiv_constFn (z w : Fin g → ℂ) (a : ℂ) :
    fderiv ℂ (fun z' => valAt' (u.ex z').left ⊤ (constFn A.hom ⊤ a)) z w = 0 := by
  have e : (fun z' => valAt' (u.ex z').left ⊤ (constFn A.hom ⊤ a)) = fun _ => a := by
    funext z'
    exact valAt'_constFn_top _ _ (ex_over u z') a
  rw [e]
  simp

theorem fn_eq {X : Scheme.{0}} (m : A.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    fn u m W f = fun z' => valAt' (u.ex z').left (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  funext z'
  unfold fn valAt' valAt
  by_cases h : ⊤ ≤ ((u.ex z').left ≫ m) ⁻¹ᵁ W
  · rw [dite_eq_left h, dite_eq_left (show ⊤ ≤ (u.ex z').left ⁻¹ᵁ (m ⁻¹ᵁ W) from h)]
    congr 1
  · rw [dite_eq_right h, dite_eq_right (show ¬ ⊤ ≤ (u.ex z').left ⁻¹ᵁ (m ⁻¹ᵁ W) from h)]

theorem existsUnique_vector : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ z δ, PtDer ((u.ex z).left ≫ m) δ → (∀ r, δ ⊤ (constFn p ⊤ r) = 0) → ∃! w, ∀ W f, z ∈ dom u m W → δ W f = fderiv ℂ (fn u m W f) z w := by
  intro P₀ u Hm χ hG R _ x₀ X p m _ hpb z δ hδ hc
  obtain ⟨hex, huniq⟩ := GlobalTheory.T.germDerivation_of_fibre_of_kills_base P₀.A R x₀ X p m hpb (u.ex z).left (ex_over u z)
  obtain ⟨δ₀, hδ₀, hc₀, hδδ₀⟩ := hex δ hδ hc
  obtain ⟨w, hw, hwu⟩ := GlobalTheory.T.germDerivation_uniformised_abelianVariety_unique_vector P₀ u Hm χ hG z δ₀ hδ₀ hc₀
  refine ⟨w, fun W f hz => ?_, fun w' hw' => hwu w' fun O f hO => ?_⟩
  · rw [hδδ₀ W f hz, hw (m ⁻¹ᵁ W) ((m.app W).hom f) hz, fn_eq]
  · have hD := ptDer_fderiv u z w'
    have hpt : PtDer (u.ex z).left
        (fun O f => δ₀ O f - fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w') := by
      refine ⟨fun V hV f f' => ?_, fun V hV f f' => ?_, fun V V' hle hV f => ?_⟩
      · have h1 := hδ₀.add V hV f f'
        have h2 := hD.add V hV f f'
        linear_combination h1 - h2
      · have h1 := hδ₀.mul V hV f f'
        have h2 := hD.mul V hV f f'
        linear_combination h1 - h2
      · have h1 := hδ₀.res V V' hle hV f
        have h2 := hD.res V V' hle hV f
        linear_combination h1 - h2
    have key := huniq _ hpt (fun a => by
        have h1 := hc₀ a
        have h2 := fderiv_constFn u z w' a
        linear_combination h1 - h2)
      (fun V f hV => by
        have h1 := hδδ₀ V f hV
        have h2 := hw' V f hV
        rw [fn_eq] at h2
        linear_combination h2 - h1) O f hO
    exact sub_eq_zero.mp key

end GlobalTheory.KS.VertFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueUniformisingVectorVerticalTangentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ z δ, PtDer ((u.ex z).left ≫ m) δ → (∀ r, δ ⊤ (constFn p ⊤ r) = 0) → ∃! w, ∀ W f, z ∈ dom u m W → δ W f = fderiv ℂ (fn u m W f) z w := by
  first | exact @GlobalTheory.KS.VertFamily.existsUnique_vector | exact GlobalTheory.KS.VertFamily.existsUnique_vector | (intros; apply GlobalTheory.KS.VertFamily.existsUnique_vector <;> assumption)
end
