module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherian
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import GroundTheory.GlobalFields.LocalAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
public import Formalism.DegreeFormula.FlagDegFormula

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosure
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

variable {ι : Type} {act : ι → SL(2, ℤ) → ι}

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
private lemma isFam_apply_smul_mul_denom_zpow {w : ℤ} {f : ι → ℍ → ℂ}
    (hf : _root_.GlobalTheory.QFam.IsFam act w f) (i : ι) (γ : SL(2, ℤ)) (τ : ℍ) :
    f i (γ • τ) * UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) ↑τ ^ (-w) = f (act i γ) τ := by
  rw [← SL_slash_apply, hf i γ]


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
theorem _root_.GlobalTheory.QFam.IsFam.const_mul_fun {w : ℤ} {f : ι → ℍ → ℂ} (c : ℂ)
    (hf : _root_.GlobalTheory.QFam.IsFam act w f) :
    _root_.GlobalTheory.QFam.IsFam act w fun i τ => c * f i τ := by
  intro i γ
  funext τ
  simp only [SL_slash_apply]
  rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ]
  ring


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
theorem _root_.GlobalTheory.QFam.IsFam.mul_fun {w w' : ℤ} {f g : ι → ℍ → ℂ}
    (hf : _root_.GlobalTheory.QFam.IsFam act w f) (hg : _root_.GlobalTheory.QFam.IsFam act w' g) :
    _root_.GlobalTheory.QFam.IsFam act (w + w') fun i τ => f i τ * g i τ := by
  intro i γ
  funext τ
  simp only [SL_slash_apply]
  rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ, ← isFam_apply_smul_mul_denom_zpow hg i γ τ, neg_add,
    zpow_add₀ (UpperHalfPlane.denom_ne_zero _ _)]
  ring


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
theorem _root_.GlobalTheory.QFam.IsFam.pow_fun {w : ℤ} {f : ι → ℍ → ℂ} (k : ℕ)
    (hf : _root_.GlobalTheory.QFam.IsFam act w f) :
    _root_.GlobalTheory.QFam.IsFam act (k * w) fun i τ => f i τ ^ k := by
  intro i γ
  funext τ
  simp only [SL_slash_apply]
  rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
    show -((k : ℤ) * w) = -w * k by ring]


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
theorem _root_.GlobalTheory.QFam.IsFam.sum_fun {κ : Type} (t : Finset κ) {w : ℤ}
    {f : κ → ι → ℍ → ℂ} (hf : ∀ k ∈ t, _root_.GlobalTheory.QFam.IsFam act w (f k)) :
    _root_.GlobalTheory.QFam.IsFam act w fun i τ => ∑ k ∈ t, f k i τ := by
  intro i γ
  funext τ
  simp only [SL_slash_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k hk => isFam_apply_smul_mul_denom_zpow (hf k hk) i γ τ


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
theorem _root_.GlobalTheory.QFam.isFam_algebra : ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι),
    (∀ c : ℂ, _root_.GlobalTheory.QFam.IsFam act 0 fun _ _ => c) ∧
    (∀ w f g, _root_.GlobalTheory.QFam.IsFam act w f → _root_.GlobalTheory.QFam.IsFam act w g →
      (_root_.GlobalTheory.QFam.IsFam act w fun i τ => f i τ + g i τ) ∧
        _root_.GlobalTheory.QFam.IsFam act w fun i τ => f i τ - g i τ) ∧
    (∀ w (c : ℂ) f, _root_.GlobalTheory.QFam.IsFam act w f →
      _root_.GlobalTheory.QFam.IsFam act w fun i τ => c * f i τ) ∧
    (∀ w w' f g, _root_.GlobalTheory.QFam.IsFam act w f → _root_.GlobalTheory.QFam.IsFam act w' g →
      _root_.GlobalTheory.QFam.IsFam act (w + w') fun i τ => f i τ * g i τ) ∧
    (∀ w f (k : ℕ), _root_.GlobalTheory.QFam.IsFam act w f →
      _root_.GlobalTheory.QFam.IsFam act (k * w) fun i τ => f i τ ^ k) ∧
    (∀ (κ : Type) (t : Finset κ) w (f : κ → ι → ℍ → ℂ),
      (∀ k ∈ t, _root_.GlobalTheory.QFam.IsFam act w (f k)) →
        _root_.GlobalTheory.QFam.IsFam act w fun i τ => ∑ k ∈ t, f k i τ) ∧
    (∀ (κ : Type) (t : Finset κ) (w : κ → ℤ) (f : κ → ι → ℍ → ℂ),
      (∀ k ∈ t, _root_.GlobalTheory.QFam.IsFam act (w k) (f k)) →
        _root_.GlobalTheory.QFam.IsFam act (∑ k ∈ t, w k) fun i τ => ∏ k ∈ t, f k i τ) ∧
    (∀ (κ : Type) (act' : κ → SL(2, ℤ) → κ) (φ : κ → ι) w f,
      (∀ k γ, φ (act' k γ) = act (φ k) γ) → _root_.GlobalTheory.QFam.IsFam act w f →
        _root_.GlobalTheory.QFam.IsFam act' w fun k => f (φ k)) := by
  intro ι act
  have hconst : ∀ c : ℂ, _root_.GlobalTheory.QFam.IsFam act 0 fun _ _ => c := by
    intro c i γ
    funext τ
    simp [SL_slash_apply]
  refine ⟨hconst, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w f g hf hg
    constructor
    · intro i γ
      funext τ
      simp only [SL_slash_apply]
      rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ, ← isFam_apply_smul_mul_denom_zpow hg i γ τ]
      ring
    · intro i γ
      funext τ
      simp only [SL_slash_apply]
      rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ, ← isFam_apply_smul_mul_denom_zpow hg i γ τ]
      ring
  · intro w c f hf
    exact hf.const_mul_fun c
  · intro w w' f g hf hg
    exact hf.mul_fun hg
  · intro w f k hf
    exact hf.pow_fun k
  · intro κ t w f hf
    exact _root_.GlobalTheory.QFam.IsFam.sum_fun t hf
  · intro κ t w f hf
    classical
    induction t using Finset.induction_on with
    | empty => simpa using hconst 1
    | insert a s ha ih =>
      have hmul := (hf a (Finset.mem_insert_self a s)).mul_fun
        (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
      simpa [Finset.sum_insert ha, Finset.prod_insert ha] using hmul
  · intro κ act' φ w f hφ hf k γ
    show f (φ k) ∣[w] γ = f (φ (act' k γ))
    rw [hf (φ k) γ, hφ k γ]

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosureStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure : ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι), (∀ c : ℂ, IsFam act 0 fun _ _ => c) ∧ (∀ w f g, IsFam act w f → IsFam act w g → (IsFam act w fun i τ => f i τ + g i τ) ∧ IsFam act w fun i τ => f i τ - g i τ) ∧ (∀ w (c : ℂ) f, IsFam act w f → IsFam act w fun i τ => c * f i τ) ∧ (∀ w w' f g, IsFam act w f → IsFam act w' g → IsFam act (w + w') fun i τ => f i τ * g i τ) ∧ (∀ w f (k : ℕ), IsFam act w f → IsFam act (k * w) fun i τ => f i τ ^ k) ∧ (∀ (κ : Type) (t : Finset κ) w (f : κ → ι → ℍ → ℂ), (∀ k ∈ t, IsFam act w (f k)) → IsFam act w fun i τ => ∑ k ∈ t, f k i τ) ∧ (∀ (κ : Type) (t : Finset κ) (w : κ → ℤ) (f : κ → ι → ℍ → ℂ), (∀ k ∈ t, IsFam act (w k) (f k)) → IsFam act (∑ k ∈ t, w k) fun i τ => ∏ k ∈ t, f k i τ) ∧ (∀ (κ : Type) (act' : κ → SL(2, ℤ) → κ) (φ : κ → ι) w f, (∀ k γ, φ (act' k γ) = act (φ k) γ) → IsFam act w f → IsFam act' w fun k => f (φ k)) := by
  first | exact @GlobalTheory.QFam.isFam_algebra | exact GlobalTheory.QFam.isFam_algebra | (intros; apply GlobalTheory.QFam.isFam_algebra <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

def secAlg {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) : A →+* Γ(T, U) :=
  (g.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.appLE_eq_of_eq {X Y : Scheme.{0}} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂)
    (U : Y.Opens) (V : X.Opens)
    (e₁ : V ≤ f₁ ⁻¹ᵁ U) (e₂ : V ≤ f₂ ⁻¹ᵁ U) : f₁.appLE U V e₁ = f₂.appLE U V e₂ := by
  subst h
  rfl

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.kappa_comm {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (_root_.GlobalTheory.HilbAff.str A B) g).IdealSheafData) (U : T.Opens) (a : A) :
    ((I.subschemeι ≫ pullback.fst _ g).appLE ⊤ ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U)
      (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a)) =
    ((I.subschemeι ≫ pullback.snd _ g).app U).hom (_root_.GlobalTheory.HilbAff.secAlg A g U a) := by
  have key : (I.subschemeι ≫ pullback.fst _ g) ≫ _root_.GlobalTheory.HilbAff.str A B =
      (I.subschemeι ≫ pullback.snd _ g) ≫ g := by
    simp [pullback.condition]
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a) =
      (_root_.GlobalTheory.HilbAff.str A B).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
    have := congrArg (fun φ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have hm : (_root_.GlobalTheory.HilbAff.str A B).appTop ≫
      (I.subschemeι ≫ pullback.fst _ g).appLE ⊤ ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U)
        (by simp) = g.appLE ⊤ U (by simp) ≫ (I.subschemeι ≫ pullback.snd _ g).app U := by
    calc _ = ((I.subschemeι ≫ pullback.fst _ g) ≫ _root_.GlobalTheory.HilbAff.str A B).appLE ⊤
          ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) (by simp) :=
          (Scheme.Hom.comp_appLE _ _ _ _ _).symm
      _ = ((I.subschemeι ≫ pullback.snd _ g) ≫ g).appLE ⊤
          ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) (by simp) :=
          _root_.GlobalTheory.HilbAff.appLE_eq_of_eq key _ _ _ _
      _ = _ := by
        rw [Scheme.Hom.app_eq_appLE]
        exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [h1]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) hm

def kappa {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) :
    letI := (secAlg A g U).toAlgebra;
    Γ(T, U) ⊗[A] B →+* Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) :=
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) :=
    (((I.subschemeι ≫ pullback.snd _ g).app U).hom.comp (secAlg A g U)).toAlgebra
  (Algebra.TensorProduct.lift
    { toRingHom := ((I.subschemeι ≫ pullback.snd _ g).app U).hom, commutes' := fun (_ : A) => rfl }
    { toRingHom := (((I.subschemeι ≫ pullback.fst _ g).appLE ⊤ _ (by simp)).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom),
      commutes' := fun a => kappa_comm A B g I U a }
    (fun _ _ => Commute.all _ _)).toRingHom

theorem kappa_tmul {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) (c : Γ(T, U)) (b : B) :
    letI := (secAlg A g U).toAlgebra
    kappa A B g I U (c ⊗ₜ[A] b) = ((I.subschemeι ≫ pullback.snd _ g).app U).hom c *
      ((I.subschemeι ≫ pullback.fst _ g).appLE ⊤ ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U)
        (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) :=
    (((I.subschemeι ≫ pullback.snd _ g).app U).hom.comp (secAlg A g U)).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

def xI (C : Type) [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)) :
    (pullback (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp
    (Algebra.TensorProduct.comm A B C).toRingHom)) ≫ (pullbackSpecIso A B C).inv).ker

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.basic_iff_kappa {r N : ℕ} (e : Module.Basis (Fin N) A B)
    (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (_root_.GlobalTheory.HilbAff.str A B) g).IdealSheafData)
    (hI : _root_.GlobalTheory.HilbAff.Good A B r g I) :
    _root_.GlobalTheory.HilbAff.Basic A B e σ (T := T) ⟨g, ⟨I, hI⟩⟩ ↔ ∀ U : T.affineOpens,
      letI := (_root_.GlobalTheory.HilbAff.secAlg A g U).toAlgebra;
      Function.Bijective fun c : Fin r → Γ(T, U) =>
        _root_.GlobalTheory.HilbAff.kappa A B g I U (∑ k, c k ⊗ₜ[A] e (σ k)) := by
  unfold _root_.GlobalTheory.HilbAff.Basic
  refine forall_congr' fun U => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, _root_.GlobalTheory.HilbAff.kappa_tmul]

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.secAlg_res {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) {U V : T.Opens}
    (h : U ≤ V) : (T.presheaf.map (homOfLE h).op).hom.comp (_root_.GlobalTheory.HilbAff.secAlg A g V) =
      _root_.GlobalTheory.HilbAff.secAlg A g U := by
  ext a
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
    (Scheme.Hom.appLE_map g (U := ⊤) (by simp) (homOfLE h).op)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.secAlg_comp {C : Type} [CommRing C] {T : Scheme.{0}}
    (h : T ⟶ Spec (CommRingCat.of C)) (f : A →+* C) (U : T.Opens) :
    _root_.GlobalTheory.HilbAff.secAlg A (h ≫ Spec.map (CommRingCat.ofHom f)) U =
      (_root_.GlobalTheory.HilbAff.secAlg C h U).comp f := by
  have hm : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (h ≫ Spec.map (CommRingCat.ofHom f)).appLE ⊤ U (by simp) =
      CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ h.appLE ⊤ U (by simp) :=
    calc _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (Spec.map (CommRingCat.ofHom f)).appTop ≫ h.appLE ⊤ U (by simp) :=
          congrArg (_ ≫ ·) (Scheme.Hom.comp_appLE h _ ⊤ U _)
      _ = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (Spec.map (CommRingCat.ofHom f)).appTop) ≫ h.appLE ⊤ U (by simp) :=
          (Category.assoc _ _ _).symm
      _ = (CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv) ≫
          h.appLE ⊤ U (by simp) := by rw [← Scheme.ΓSpecIso_inv_naturality]
      _ = _ := Category.assoc _ _ _
  ext a
  exact congrArg (fun φ => φ.hom a) hm

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.eq_of_secAlg_top {T : Scheme.{0}}
    {g₁ g₂ : T ⟶ Spec (CommRingCat.of A)}
    (h : _root_.GlobalTheory.HilbAff.secAlg A g₁ ⊤ = _root_.GlobalTheory.HilbAff.secAlg A g₂ ⊤) :
    g₁ = g₂ := by
  apply ext_of_isAffine
  have e₁ : g₁.appLE ⊤ ⊤ le_top = g₁.appTop := g₁.appLE_eq_app
  have e₂ : g₂.appLE ⊤ ⊤ le_top = g₂.appTop := g₂.appLE_eq_app
  have h' : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g₁.appLE ⊤ ⊤ le_top =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g₂.appLE ⊤ ⊤ le_top := CommRingCat.hom_ext h
  rw [e₁, e₂] at h'
  exact (cancel_epi _).1 h'

end GlobalTheory.HilbAff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelMulOfPosLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelMulOfPosLevel
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

private lemma hasSum_conv_mul_of_multiplicative {a b : ℕ → ℂ} {e : ℕ → ℂ} {x y : ℂ}
    (he : ∀ m n, e (m + n) = e m * e n)
    (ha : HasSum (fun n => a n * e n) x) (hb : HasSum (fun n => b n * e n) y) :
    HasSum (fun n => conv a b n * e n) (x * y) := by
  have hna : Summable fun n => ‖a n * e n‖ := summable_norm_iff.mpr ha.summable
  have hnb : Summable fun n => ‖b n * e n‖ := summable_norm_iff.mpr hb.summable
  have hS : HasSum (fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (a p.1 * e p.1) * (b p.2 * e p.2)) (x * y) := by
    rw [← ha.tsum_eq, ← hb.tsum_eq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hna hnb]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hna hnb).of_norm.hasSum
  convert hS using 1
  funext n
  rw [conv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, he]
  ring

private lemma mvExp_add_character_germs (N : ℕ) (τ : ℍ) (m n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((m + n : ℕ) : ℂ) * τ / N) =
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * τ / N) *
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / N) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem HasQ.mul_conv {N : ℕ} {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g b) :
    HasQ N (fun τ => f τ * g τ) (conv a b) :=
  fun τ => hasSum_conv_mul_of_multiplicative (mvExp_add_character_germs N τ) (hf τ) (hg τ)

theorem hasQ_mul_conv : ∀ (N : ℕ) (f g : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N g b →
    HasQ N (fun τ => f τ * g τ) (conv a b) := by
  intro N f g a b _ hf hg τ
  exact hasSum_conv_mul_of_multiplicative (mvExp_add_character_germs N τ) (hf τ) (hg τ)

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelMulOfPosLevelStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansionOfLevel_mul_of_pos_level : ∀ (N : ℕ) (f g : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ * g τ) (conv a b) := by
  first | exact @GlobalTheory.QFam.hasQ_mul_conv | exact GlobalTheory.QFam.hasQ_mul_conv | (intros; apply GlobalTheory.QFam.hasQ_mul_conv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceTensorRatFiniteAlgebraModuleTopology
noncomputable section

open NumberField Matrix IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct RestrictedProduct

namespace GlobalTheory.LKTrip

namespace LevelExists

theorem isCompact_intCompl (v : HeightOneSpectrum ℤ) :
    IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  haveI : CompleteSpace (v.adicCompletionIntegers ℚ) :=
    (Valued.isClosed_valuationSubring (v.adicCompletion ℚ)).completeSpace_coe
  haveI : Finite (ℤ ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
    Finite.of_equiv _ (GroundTheory.Global.residueFieldEquiv (K := ℚ) v).toEquiv
  have hc : CompactSpace (Valued.integer (v.adicCompletion ℚ)) :=
    Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
      ⟨inferInstanceAs (CompleteSpace (v.adicCompletionIntegers ℚ)),
        inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers ℚ)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)))⟩
  exact isCompact_iff_compactSpace.mpr hc

def rp {p : ℕ} (x : AfP p) : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ] := x

def intAfP (p : ℕ) : Subring (AfP p) where
  carrier := {x | ∀ v : AwayP p, (rp x).1 v ∈ v.1.adicCompletionIntegers ℚ}
  mul_mem' := by intro a b ha hb v; exact mul_mem (ha v) (hb v)
  one_mem' := by intro v; exact one_mem _
  add_mem' := by intro a b ha hb v; exact add_mem (ha v) (hb v)
  zero_mem' := by intro v; exact zero_mem _
  neg_mem' := by intro a ha v; exact neg_mem (ha v)

theorem isOpen_intAfP (p : ℕ) : IsOpen (intAfP p : Set (AfP p)) := by
  exact RestrictedProduct.isOpen_forall_mem
    (R := fun w : AwayP p => w.1.adicCompletion ℚ)
    (A := fun w => (w.1.adicCompletionIntegers ℚ : Set (w.1.adicCompletion ℚ)))
    (fun w => Valued.isOpen_valuationSubring (w.1.adicCompletion ℚ))

theorem isCompact_intAfP (p : ℕ) : IsCompact (intAfP p : Set (AfP p)) := by
  haveI : ∀ w : AwayP p, CompactSpace (w.1.adicCompletionIntegers ℚ) :=
    fun w => isCompact_iff_compactSpace.mp (isCompact_intCompl w.1)
  let e := RestrictedProduct.homeoTop (R := fun w : AwayP p => w.1.adicCompletion ℚ)
    (A := fun w => (w.1.adicCompletionIntegers ℚ : Set (w.1.adicCompletion ℚ)))
  let f : (Π w : AwayP p, w.1.adicCompletionIntegers ℚ) → AfP p := fun g =>
    RestrictedProduct.inclusion (fun w : AwayP p => w.1.adicCompletion ℚ)
      (fun w => (w.1.adicCompletionIntegers ℚ : Set (w.1.adicCompletion ℚ))) le_top (e g)
  have hf : Continuous f :=
    (RestrictedProduct.continuous_inclusion le_top).comp e.continuous
  have hset : (intAfP p : Set (AfP p)) = Set.range f := by
    ext x
    constructor
    · intro hx
      exact ⟨fun w => ⟨(rp x).1 w, hx w⟩, rfl⟩
    · rintro ⟨g, rfl⟩ w
      exact (g w).2
  rw [hset]
  exact isCompact_range hf

end LevelExists

namespace LevelExists

section Tensor

variable (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
  (F : Type) [Field F] [NumberField F]

def tensorInt (O : Subring R) : Subring (R ⊗[ℚ] F) where
  carrier := {x | ∀ i j, Algebra.leftMulMatrix (Algebra.TensorProduct.basis R (Module.finBasis ℚ F)) x i j ∈ O}
  mul_mem' := by
    intro x y hx hy i j
    simp only [Set.mem_setOf_eq, map_mul, Matrix.mul_apply]
    exact sum_mem fun k _ ↦ mul_mem (hx i k) (hy k j)
  one_mem' := by
    intro i j
    simp only [Set.mem_setOf_eq, map_one, Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  add_mem' := by
    intro x y hx hy i j
    simp only [Set.mem_setOf_eq, map_add (f := _), Matrix.add_apply]
    exact add_mem (hx i j) (hy i j)
  zero_mem' := by intro i j; simp
  neg_mem' := by
    intro x hx i j
    simp only [Set.mem_setOf_eq, map_neg, Matrix.neg_apply]
    exact neg_mem (hx i j)

def mulMatAlg (A : Type) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] :
    R ⊗[ℚ] A →ₐ[R] Matrix (Fin (Module.finrank ℚ A)) (Fin (Module.finrank ℚ A)) R :=
  (LinearMap.toMatrixAlgEquiv (Algebra.TensorProduct.basis R (Module.finBasis ℚ A))).toAlgHom.comp
    (Algebra.lmul R (R ⊗[ℚ] A))

def tensorIntAlg (A : Type) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] (O : Subring R) : Subring (R ⊗[ℚ] A) where
  carrier := {x | ∀ i j, mulMatAlg R A x i j ∈ O}
  mul_mem' := by
    intro x y hx hy i j
    simp only [Set.mem_setOf_eq, map_mul, Matrix.mul_apply]
    exact sum_mem fun k _ ↦ mul_mem (hx i k) (hy k j)
  one_mem' := by
    intro i j
    simp only [Set.mem_setOf_eq, map_one, Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  add_mem' := by
    intro x y hx hy i j
    simp only [Set.mem_setOf_eq, map_add (f := _), Matrix.add_apply]
    exact add_mem (hx i j) (hy i j)
  zero_mem' := by intro i j; simp
  neg_mem' := by
    intro x hx i j
    simp only [Set.mem_setOf_eq, map_neg, Matrix.neg_apply]
    exact neg_mem (hx i j)

theorem isOpen_isCompact_tensorIntAlg (A : Type) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] (O : Subring R)
    (hOo : IsOpen (O : Set R)) (hOc : IsCompact (O : Set R)) :
    @IsOpen _ (moduleTopology R (R ⊗[ℚ] A)) (tensorIntAlg R A O : Set (R ⊗[ℚ] A)) ∧
      @IsCompact _ (moduleTopology R (R ⊗[ℚ] A)) (tensorIntAlg R A O : Set (R ⊗[ℚ] A)) := by
  letI : TopologicalSpace (R ⊗[ℚ] A) := moduleTopology R (R ⊗[ℚ] A)
  haveI : IsModuleTopology R (R ⊗[ℚ] A) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[ℚ] A) := IsModuleTopology.isTopologicalRing R (R ⊗[ℚ] A)
  set bS := Algebra.TensorProduct.basis R (Module.finBasis ℚ A) with hbS
  set L := mulMatAlg R A with hL
  have hLc : Continuous L := IsModuleTopology.continuous_of_linearMap L.toLinearMap
  set box : Set (Matrix (Fin (Module.finrank ℚ A)) (Fin (Module.finrank ℚ A)) R) :=
    Set.univ.pi fun _ ↦ Set.univ.pi fun _ ↦ (O : Set R) with hbox
  have hset : (tensorIntAlg R A O : Set (R ⊗[ℚ] A)) = L ⁻¹' box := by
    ext x
    constructor
    · intro h i _ j _; exact h i j
    · intro h i j; exact h i trivial j trivial
  have hopen : IsOpen (tensorIntAlg R A O : Set (R ⊗[ℚ] A)) := by
    rw [hset]
    exact hLc.isOpen_preimage _ (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_set_pi Set.finite_univ fun _ _ ↦ hOo)
  refine ⟨hopen, ?_⟩
  have hboxc : IsCompact box := isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ hOc
  set w := bS.equivFun 1
  let ψ : Matrix (Fin (Module.finrank ℚ A)) (Fin (Module.finrank ℚ A)) R → R ⊗[ℚ] A :=
    fun M ↦ bS.equivFun.symm (M *ᵥ w)
  have hψ : Continuous ψ :=
    (IsModuleTopology.continuous_of_linearMap bS.equivFun.symm.toLinearMap).comp
      (continuous_id.matrix_mulVec continuous_const)
  have e : ∀ f : Module.End R (R ⊗[ℚ] A), LinearMap.toMatrixAlgEquiv bS f = LinearMap.toMatrix bS bS f :=
    fun f ↦ by ext i j; simp [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  have hrec : ∀ x, ψ (L x) = x := by
    intro x
    show bS.equivFun.symm (LinearMap.toMatrixAlgEquiv bS (Algebra.lmul R (R ⊗[ℚ] A) x) *ᵥ bS.equivFun 1) = x
    rw [e, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr, ← Module.Basis.equivFun_apply,
      LinearEquiv.symm_apply_apply]
    simp
  have hsub : (tensorIntAlg R A O : Set (R ⊗[ℚ] A)) ⊆ ψ '' box := by
    intro x hx
    refine ⟨L x, by rw [hset] at hx; exact hx, hrec x⟩
  have hcl : IsClosed (tensorIntAlg R A O : Set (R ⊗[ℚ] A)) :=
    AddSubgroup.isClosed_of_isOpen (tensorIntAlg R A O).toAddSubgroup hopen
  exact (hboxc.image hψ).of_isClosed_subset hcl hsub

theorem t2Space_tensor_rat_finite_algebra_moduleTopology [T2Space R] (A : Type) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] :
    @T2Space (R ⊗[ℚ] A) (moduleTopology R (R ⊗[ℚ] A)) := by
  letI : TopologicalSpace (R ⊗[ℚ] A) := moduleTopology R (R ⊗[ℚ] A)
  haveI : IsModuleTopology R (R ⊗[ℚ] A) := ⟨rfl⟩
  set bS := Algebra.TensorProduct.basis R (Module.finBasis ℚ A)
  exact T2Space.of_injective_continuous bS.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap bS.equivFun.toLinearMap)

end Tensor

end LevelExists

namespace LevelExists

section Entries

variable {S : Type} [CommRing S] {n : ℕ}

end Entries

variable {p : ℕ} [Fact p.Prime]

def stdLevel (G : HTGroup p) (O : Subring (AfP p)) (P : Subring (AfP p ⊗[ℚ] G.C)) : Subgroup G.GAf where
  carrier := {x | ((((x.1.1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) ∈ P ∧
      (((x.1.1⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) ∈ P) ∧
      (((x.1.2 : (AfP p)ˣ) : AfP p) ∈ O ∧ (((x.1.2⁻¹ : (AfP p)ˣ)) : AfP p) ∈ O))}
  mul_mem' := by
    rintro x y ⟨⟨hx1, hx2⟩, hx3, hx4⟩ ⟨⟨hy1, hy2⟩, hy3, hy4⟩
    exact ⟨⟨mul_mem hx1 hy1, mul_mem hy2 hx2⟩, mul_mem hx3 hy3, mul_mem hy4 hx4⟩
  one_mem' := ⟨⟨P.one_mem, P.one_mem⟩, O.one_mem, O.one_mem⟩
  inv_mem' := by
    rintro x ⟨⟨hx1, hx2⟩, hx3, hx4⟩
    exact ⟨⟨hx2, hx1⟩, hx4, hx3⟩

theorem level_exists : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Nonempty G.Level := by
  intro p _ G
  haveI : T2Space (AfP p) := inferInstanceAs
    (T2Space (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]))
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) _
  haveI : T2Space (AfP p ⊗[ℚ] G.C) := t2Space_tensor_rat_finite_algebra_moduleTopology (AfP p) G.C
  obtain ⟨hPo, hPc⟩ := isOpen_isCompact_tensorIntAlg (AfP p) G.C (intAfP p) (isOpen_intAfP p) (isCompact_intAfP p)
  have hOo := isOpen_intAfP p
  have hOc := isCompact_intAfP p
  set P := tensorIntAlg (AfP p) G.C (intAfP p)
  set O := intAfP p
  have hσ : Continuous (fun y : AfP p ⊗[ℚ] G.C ↦ (starT G.star (AfP p) y).unop) := by
    let σl : (AfP p ⊗[ℚ] G.C) →ₗ[AfP p] (AfP p ⊗[ℚ] G.C) :=
      { toFun := fun y ↦ (starT G.star (AfP p) y).unop
        map_add' := fun x y ↦ by simp only [map_add (f := _), MulOpposite.unop_add]
        map_smul' := by
          intro r x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul a y =>
            simp only [TensorProduct.smul_tmul', smul_eq_mul, starT_tmul, RingHom.id_apply]
          | add x y hx hy => simp only [smul_add, map_add (f := _), MulOpposite.unop_add, hx, hy, RingHom.id_apply] }
    exact IsModuleTopology.continuous_of_linearMap σl
  have hj : Continuous (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AfP p) (AfP p ⊗[ℚ] G.C))
  have hGcl : IsClosed (UPts G.star (AfP p) : Set ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
    apply isClosed_eq
    · exact (Units.continuous_val.comp continuous_fst).mul
        (hσ.comp (Units.continuous_val.comp continuous_fst))
    · exact hj.comp (Units.continuous_val.comp continuous_snd)
  let g : G.GAf → ((AfP p ⊗[ℚ] G.C) × (AfP p ⊗[ℚ] G.C)ᵐᵒᵖ) × (AfP p × (AfP p)ᵐᵒᵖ) :=
    fun x ↦ (Units.embedProduct _ x.1.1, Units.embedProduct _ x.1.2)
  have hg : Topology.IsClosedEmbedding g :=
    (Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct).comp
      hGcl.isClosedEmbedding_subtypeVal
  let C := ((P : Set (AfP p ⊗[ℚ] G.C)) ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' (P : Set (AfP p ⊗[ℚ] G.C)))) ×ˢ
    ((O : Set (AfP p)) ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' (O : Set (AfP p))))
  have hKC : (stdLevel G O P : Set G.GAf) = g ⁻¹' C := rfl
  refine ⟨⟨⟨stdLevel G O P, ?_⟩, ?_⟩⟩
  · show IsOpen (stdLevel G O P : Set G.GAf)
    rw [hKC]
    exact hg.continuous.isOpen_preimage _ ((hPo.prod
      (MulOpposite.opHomeomorph.symm.isOpen_preimage.2 hPo)).prod
      (hOo.prod (MulOpposite.opHomeomorph.symm.isOpen_preimage.2 hOo)))
  · show IsCompact (stdLevel G O P : Set G.GAf)
    rw [hKC]
    exact hg.isCompact_preimage ((hPc.prod
      (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hPc)).prod
      (hOc.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hOc)))

end LevelExists

end GlobalTheory.LKTrip
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanInvolutionConjOfPosDef
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder MatrixOrder

namespace GlobalTheory


open scoped MatrixOrder in
theorem cartanInvolution_conj_of_posDef (ι : Type) [Fintype ι] [DecidableEq ι]
    (s s' : Matrix ι ι ℂ) (hs : sᴴ = s) (hss : s * s = 1) (hs's' : s' * s' = 1)
    (hM : (s * s').PosDef) :
    ∃ a : Matrix ι ι ℂ, aᴴ * s * a = s ∧ a * s = s' * a := by
  set M := s * s' with hMdef
  have hMpsd : M.PosSemidef := hM.posSemidef
  have hM0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hMpsd
  set R := CFC.sqrt M with hRdef
  have hR0 : 0 ≤ R := CFC.sqrt_nonneg M
  have hRpsd : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hR0
  have hRR : R * R = M := CFC.sqrt_mul_sqrt_self M hM0
  have hRh : Rᴴ = R := hRpsd.isHermitian
  have hsM : s * M = s' := by rw [hMdef, ← Matrix.mul_assoc, hss, Matrix.one_mul]
  have hMinv : M⁻¹ = s * M * s := by
    apply Matrix.inv_eq_left_inv
    calc s * M * s * M = (s * M) * (s * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hsM, hs's']
  have hsRs : CFC.sqrt M⁻¹ = s * R * s := by
    refine CFC.sqrt_unique ?_ ?_
    · calc s * R * s * (s * R * s) = s * (R * R) * s := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc s s, hss, Matrix.one_mul]
        _ = M⁻¹ := by rw [hRR, hMinv]
    · have h := hRpsd.conjTranspose_mul_mul_same s
      rw [hs] at h
      exact Matrix.nonneg_iff_posSemidef.mpr h
  have hRinv : R⁻¹ = s * R * s := by
    rw [← hsRs]
    exact hMpsd.inv_sqrt
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  have hRu : IsUnit R.det := by
    rw [← hRR, Matrix.det_mul] at hMu
    exact isUnit_of_mul_isUnit_left hMu
  have hsRinv : s * R⁻¹ = R * s := by
    rw [hRinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hss, Matrix.one_mul]
  refine ⟨R⁻¹, ?_, ?_⟩
  · rw [Matrix.conjTranspose_nonsing_inv, hRh, Matrix.mul_assoc, hsRinv, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hRu, Matrix.one_mul]
  · calc R⁻¹ * s = s * R := by rw [hRinv, Matrix.mul_assoc, hss, Matrix.mul_one]
      _ = s * M * R⁻¹ := by
        rw [← hRR, Matrix.mul_assoc s, Matrix.mul_assoc R, Matrix.mul_nonsing_inv _ hRu,
          Matrix.mul_one]
      _ = s' * R⁻¹ := by rw [hsM]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermutedModularFamilySumEsymmSlashInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermutedModularFamilySumEsymmSlashInvariant
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.IsFam.value_mul_denom {ι : Type} {act : ι → SL(2, ℤ) → ι}
    {w : ℤ} {f : ι → ℍ → ℂ}
    (h : _root_.GlobalTheory.QFam.IsFam act w f) (i : ι) (γ : SL(2, ℤ)) (τ : ℍ) :
    f i (γ • τ) * UpperHalfPlane.denom γ τ ^ (-w) = f (act i γ) τ := by
  have hi := congrFun (h i γ) τ
  rw [ModularForm.SL_slash_apply] at hi
  exact hi


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.IsFam.esymm_slash {ι : Type} [Fintype ι]
    {act : ι → SL(2, ℤ) → ι} {w : ℤ} {f : ι → ℍ → ℂ}
    (hb : _root_.GlobalTheory.QFam.ActBij act) (h : _root_.GlobalTheory.QFam.IsFam act w f)
    (γ : SL(2, ℤ)) (k : ℕ) :
    (fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) ∣[(k * w : ℤ)] γ =
      fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ := by
  let e : ι ≃ ι := Equiv.ofBijective _ (hb γ)
  ext τ
  rw [ModularForm.SL_slash_apply, Finset.sum_mul]
  have key : ∀ t ∈ Finset.powersetCard k (Finset.univ : Finset ι),
      (∏ i ∈ t, f i (γ • τ)) * UpperHalfPlane.denom γ τ ^ (-(k * w : ℤ)) =
        ∏ i ∈ t, f (e i) τ := by
    intro t ht
    rw [Finset.mem_powersetCard] at ht
    calc (∏ i ∈ t, f i (γ • τ)) * UpperHalfPlane.denom γ τ ^ (-(k * w : ℤ))
        = ∏ i ∈ t, (f i (γ • τ) * UpperHalfPlane.denom γ τ ^ (-w)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, ht.2, ← zpow_natCast, ← zpow_mul]
          congr 2
          ring
      _ = ∏ i ∈ t, f (e i) τ := Finset.prod_congr rfl fun i _ => h.value_mul_denom i γ τ
  rw [Finset.sum_congr rfl key]
  refine Finset.sum_nbij' (fun t => t.map e.toEmbedding) (fun t => t.map e.symm.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.card_map] at ht ⊢
    exact ht
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.card_map] at ht ⊢
    exact ht
  · intro t _
    simp [Finset.map_map]
  · intro t _
    simp [Finset.map_map]
  · intro t _
    rw [Finset.prod_map]
    rfl


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.sum_esymm_slash : ∀ (ι : Type) [Fintype ι]
    (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ),
    _root_.GlobalTheory.QFam.ActBij act → _root_.GlobalTheory.QFam.IsFam act w f → ∀ γ : SL(2, ℤ),
      ((fun τ => ∑ i, f i τ) ∣[w] γ = fun τ => ∑ i, f i τ) ∧
      ∀ k : ℕ, ((fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) ∣[(k * w : ℤ)] γ =
        fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) := by
  intro ι _ act w f hb h γ
  refine ⟨?_, fun k => h.esymm_slash hb γ k⟩
  let e : ι ≃ ι := Equiv.ofBijective _ (hb γ)
  ext τ
  rw [ModularForm.SL_slash_apply, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun i _ => h.value_mul_denom i γ τ]
  exact e.sum_comp (fun i => f i τ)

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermutedModularFamilySumEsymmSlashInvariantStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.permutedModularFamily_sum_esymm_slash_invariant : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ), ActBij act → IsFam act w f → ∀ γ : SL(2, ℤ), ((fun τ => ∑ i, f i τ) ∣[w] γ = fun τ => ∑ i, f i τ) ∧ ∀ k : ℕ, ((fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) ∣[(k * w : ℤ)] γ = fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) := by
  first | exact @GlobalTheory.QFam.sum_esymm_slash | exact GlobalTheory.QFam.sum_esymm_slash | (intros; apply GlobalTheory.QFam.sum_esymm_slash <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMemSpanLinearRoots
open MvPolynomial

namespace GlobalTheory

namespace PowLinSpan

variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem sum_C_mul_X_pow (u : σ → ℝ) (d : ℕ) :
    (∑ x, C (u x) * X x : MvPolynomial σ ℝ) ^ d =
      ∑ k ∈ Finset.piAntidiag Finset.univ d,
        ((Nat.multinomial Finset.univ k : ℝ) * ∏ x, u x ^ k x) •
          monomial (Finsupp.equivFunOnFinite.symm k) (1 : ℝ) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_C_mul, monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, map_mul, map_natCast, C_1, one_mul,
    Finsupp.coe_equivFunOnFinite_symm]
  ring

noncomputable def polOf (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) : MvPolynomial σ ℝ :=
  ∑ k ∈ Finset.piAntidiag Finset.univ d,
    monomial (Finsupp.equivFunOnFinite.symm k)
      ((Nat.multinomial Finset.univ k : ℝ) * φ (monomial (Finsupp.equivFunOnFinite.symm k) 1))

theorem eval_polOf (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (u : σ → ℝ) :
    eval u (polOf φ d) = φ ((∑ x, C (u x) * X x) ^ d) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [sum_C_mul_X_pow, map_sum, polOf, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, eval_monomial, smul_eq_mul, Finsupp.prod_fintype _ _ (by simp)]
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  ring

theorem coeff_polOf (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (m : σ →₀ ℕ) (hm : ∑ x, m x = d) :
    AddMonoidAlgebra.coeff (polOf φ d) m = (Nat.multinomial Finset.univ m : ℝ) * φ (monomial m 1) := by
  rw [polOf, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single (⇑m)]
  · simp
  · intro k _ hk
    rw [if_neg]
    intro h
    apply hk
    rw [← h]
    simp
  · intro h
    exfalso
    apply h
    rw [Finset.mem_piAntidiag]
    simp [hm]

theorem degreeOf_polOf_le (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (x : σ) :
    (polOf φ d).degreeOf x ≤ d := by
  refine (degreeOf_le_totalDegree _ _).trans ?_
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun k hk => ?_)
  refine (totalDegree_monomial_le _ _).trans ?_
  rw [Finset.mem_piAntidiag] at hk
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simpa [Finsupp.coe_equivFunOnFinite_symm] using hk.1.le

theorem monomial_kill (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (hP : polOf φ d = 0)
    (m : σ →₀ ℕ) (hm : ∑ x, m x = d) : φ (monomial m 1) = 0 := by
  have h := coeff_polOf φ d m hm
  rw [hP, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h
  have hne : (Nat.multinomial Finset.univ m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  rcases mul_eq_zero.mp h.symm with h1 | h1
  · exact absurd h1 hne
  · exact h1

theorem homog_kill (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (hP : polOf φ d = 0)
    (Q : MvPolynomial σ ℝ) (hQ : Q.IsHomogeneous d) : φ Q = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Q.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hdeg : ∑ x, m x = d := by
    have := hQ (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  have : monomial m (AddMonoidAlgebra.coeff Q m) = AddMonoidAlgebra.coeff Q m • monomial m (1 : ℝ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, monomial_kill φ d hP m hdeg, smul_zero]

end PowLinSpan
end GlobalTheory
end
