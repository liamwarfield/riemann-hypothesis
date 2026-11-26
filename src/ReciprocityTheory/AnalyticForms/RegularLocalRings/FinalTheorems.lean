module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory TensorProduct
universe u
namespace ReciprocityTheory.AnForm.R.FinalTheorems

def EffCartier {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ (U : X.affineOpens) (f : Γ(X, U.1)),
    x ∈ U.1 ∧ f ∈ nonZeroDivisors Γ(X, U.1) ∧ I.ideal U = Ideal.span {f}

def Blowup {X X' : Scheme.{u}} (π : X' ⟶ X) (I : X.IdealSheafData) : Prop :=
  EffCartier (I.comap π) ∧
    ∀ (W : Scheme.{u}) (g : W ⟶ X), EffCartier (I.comap g) → ∃! h : W ⟶ X', h ≫ π = g

def Rsp (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) (x : Fin n → R) : Prop :=
  Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R ∧ (n : WithBot ℕ∞) = ringKrullDim R

def Snc {Y : Scheme.{u}} (D : Y.IdealSheafData) : Prop :=
  ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) ∧
    ∃ (U : Y.affineOpens) (hy : y ∈ U.1) (n : ℕ) (f : Fin n → Γ(Y, U.1)) (J : Finset (Fin n)),
      Rsp (Y.presheaf.stalk y) n (fun i => Y.presheaf.germ U.1 y hy (f i)) ∧
        D.ideal U = Ideal.span {∏ i ∈ J, f i}

def GeomRegFib (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∀ (P : Ideal A) [P.IsPrime] (K : Type u) [Field K] [Algebra P.ResidueField K] [Algebra A K]
    [IsScalarTower A P.ResidueField K], (⊤ : IntermediateField P.ResidueField K).FG →
    IsNoetherianRing (B ⊗[A] K) ∧
      ∀ (Q : Ideal (B ⊗[A] K)) [Q.IsPrime], IsRegularLocalRing (Localization.AtPrime Q)

def QERing (A : Type u) [CommRing A] : Prop :=
  IsNoetherianRing A ∧
  (∀ (P : Ideal A) [P.IsPrime],
    Module.Flat (Localization.AtPrime P)
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)) ∧
    GeomRegFib (Localization.AtPrime P)
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P))) ∧
  (∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B],
    IsOpen {Q : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime Q.asIdeal)})

def QE (X : Scheme.{u}) : Prop := ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ QERing Γ(X, U.1)

def FFinRes (X : Scheme.{u}) : Prop :=
  ∀ (x : X) (p : ℕ) [Fact p.Prime] [CharP (X.residueField x) p], (frobenius (X.residueField x) p).Finite

def Sing (X : Scheme.{u}) : Set X := {x | ¬ IsRegularLocalRing (X.presheaf.stalk x)}

noncomputable def stalkId {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) : Ideal (X.presheaf.stalk x) :=
  ⨆ (U : X.affineOpens) (hx : x ∈ U.1), Ideal.map (X.presheaf.germ U.1 x hx).hom (I.ideal U)

def LSncAt (X : Scheme.{u}) {q : ℕ} (L : Fin q → TopologicalSpace.Closeds X) (x : X) : Prop :=
  IsRegularLocalRing (X.presheaf.stalk x) ∧
    ∃ (n : ℕ) (r : Fin n → X.presheaf.stalk x) (e : {i : Fin q // x ∈ L i} ↪ Fin n),
      Rsp (X.presheaf.stalk x) n r ∧
        ∀ i : {i : Fin q // x ∈ L i},
          stalkId (Scheme.IdealSheafData.vanishingIdeal (L i.1)) x = Ideal.span {r (e i)}

def CompList {X : Scheme.{u}} (B : Set X) {q : ℕ} (V : Fin q → TopologicalSpace.Closeds X) : Prop :=
  (∀ j, IsIrreducible (V j : Set X)) ∧ (⋃ j, (V j : Set X)) = B ∧ ∀ i j, (V i : Set X) ⊆ V j → i = j

def SncAt {Y : Scheme.{u}} (D : Y.IdealSheafData) (y : Y) : Prop :=
  IsRegularLocalRing (Y.presheaf.stalk y) ∧
    ∃ (U : Y.affineOpens) (hy : y ∈ U.1) (n : ℕ) (f : Fin n → Γ(Y, U.1)) (J : Finset (Fin n)),
      Rsp (Y.presheaf.stalk y) n (fun i => Y.presheaf.germ U.1 y hy (f i)) ∧
        D.ideal U = Ideal.span {∏ i ∈ J, f i}

end ReciprocityTheory.AnForm.R.FinalTheorems
end

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.FromSpecResidueFieldAppTopIso
namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory

noncomputable section

variable {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of ℂ))

def constSec (U : S.Opens) : ℂ →+* Γ(S, U) :=
  (s.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

def constRes (x : S) : ℂ →+* S.residueField x :=
  (S.evaluation ⊤ x trivial).hom.comp (constSec s ⊤)


open Classical in
def valHom (x : S) : S.residueField x → ℂ := by
  classical
  exact if h : ∃ φ : S.residueField x →+* ℂ, φ.comp (constRes s x) = RingHom.id ℂ then h.choose else fun _ => 0

def val {U : S.Opens} (f : Γ(S, U)) (x : S) (hx : x ∈ U) : ℂ :=
  valHom s x (S.evaluation U x hx f)

theorem fromSpecResidueField_appTop_iso (x : S) :
    (S.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso _).hom = S.evaluation ⊤ x trivial := by
  simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.fromSpecStalk_appTop, Scheme.evaluation]
  have hid : (Spec (S.presheaf.stalk x)).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (S.presheaf.stalk x)).Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [show (homOfLE (le_top : (⊤ : (Spec (S.presheaf.stalk x)).Opens) ≤ ⊤)).op = 𝟙 _ from rfl,
      CategoryTheory.Functor.map_id]
  simp [hid]

theorem constRes_eq (x : S) (hx : IsClosed ({x} : Set S)) [LocallyOfFiniteType s] :
    constRes s x = (residueFieldIsoBase s x hx).inv.hom := by
  have hφ := Scheme.ΓSpecIso_naturality (Spec.preimage (S.fromSpecResidueField x ≫ s))
  rw [Spec.map_preimage] at hφ
  have hpre : Spec.preimage (S.fromSpecResidueField x ≫ s) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (S.fromSpecResidueField x ≫ s).appTop ≫
        (Scheme.ΓSpecIso (S.residueField x)).hom := by
    rw [hφ, Iso.inv_hom_id_assoc]
  have hA : s.appLE ⊤ ⊤ le_top = s.appTop := (s.app_eq_appLE (U := ⊤)).symm
  have hc : constRes s x = ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ ⊤ le_top ≫
      S.evaluation ⊤ x trivial).hom := rfl
  rw [hc, hA, ← fromSpecResidueField_appTop_iso x]
  show _ = (Spec.preimage (S.fromSpecResidueField x ≫ s)).hom
  rw [hpre, Scheme.Hom.comp_appTop, Category.assoc]

theorem valHom_unique [LocallyOfFiniteType s] (x : S) (hx : IsClosed ({x} : Set S))
    (ψ : S.residueField x →+* ℂ) (h : ψ.comp (constRes s x) = RingHom.id ℂ) :
    ψ = (residueFieldIsoBase s x hx).hom.hom := by
  ext y
  have h1 : (residueFieldIsoBase s x hx).inv.hom ((residueFieldIsoBase s x hx).hom.hom y) = y := by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
      RingHom.id_apply]
  have h2 := congrArg (fun f : ℂ →+* ℂ => f ((residueFieldIsoBase s x hx).hom.hom y)) h
  simp only [RingHom.comp_apply, RingHom.id_apply, constRes_eq s x hx, h1] at h2
  exact h2

theorem valHom_spec [LocallyOfFiniteType s] (x : S) (hx : IsClosed ({x} : Set S)) :
    ((residueFieldIsoBase s x hx).hom.hom).comp (constRes s x) = RingHom.id ℂ := by
  rw [constRes_eq s x hx, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id]

theorem valHom_eq [LocallyOfFiniteType s] (x : S) (hx : IsClosed ({x} : Set S)) :
    valHom s x = (residueFieldIsoBase s x hx).hom.hom := by
  have hex : ∃ φ : S.residueField x →+* ℂ, φ.comp (constRes s x) = RingHom.id ℂ :=
    ⟨_, valHom_spec s x hx⟩
  unfold valHom
  rw [dite_eq_left hex, valHom_unique s x hx _ hex.choose_spec]

theorem evaluation_res {U V : S.Opens} (h : V ≤ U) (f : Γ(S, U)) (x : S) (hx : x ∈ V) :
    S.evaluation V x hx (S.presheaf.map (homOfLE h).op f) = S.evaluation U x (h hx) f := by
  have key : S.presheaf.map (homOfLE h).op ≫ S.evaluation V x hx = S.evaluation U x (h hx) := by
    simp only [Scheme.evaluation, TopCat.Presheaf.germ_res_assoc]
  rw [← key]
  rfl

theorem constSec_res (U : S.Opens) (c : ℂ) :
    constSec s U c = S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (constSec s ⊤ c) := by
  simp only [constSec, RingHom.comp_apply]
  rw [← s.appLE_map (U := ⊤) (V := ⊤) le_top (homOfLE (le_top : U ≤ ⊤)).op]
  rfl

theorem isClosed_image_of_closed {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (g : S ⟶ T)
    (hg : g ≫ t = s) [LocallyOfFiniteType s] [LocallyOfFiniteType t] (x : S)
    (hc : IsClosed ({x} : Set S)) : IsClosed ({g.base x} : Set T) := by
  haveI : JacobsonSpace T := AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace t
  haveI : AlgebraicGeometry.LocallyOfFiniteType (g ≫ t) := by rw [hg]; infer_instance
  haveI : AlgebraicGeometry.LocallyOfFiniteType g := AlgebraicGeometry.locallyOfFiniteType_of_comp g t
  have hx : x ∈ closedPoints S := by simpa [mem_closedPoints_iff] using hc
  have := g.closePoints_subset_preimage_closedPoints hx
  simpa [mem_closedPoints_iff] using this

theorem residueFieldMap_constRes {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (g : S ⟶ T)
    (hg : g ≫ t = s) (x : S) :
    (g.residueFieldMap x).hom.comp (constRes t (g.base x)) = constRes s x := by
  have hA : ∀ (Y : Scheme.{0}) (y : Y ⟶ Spec (CommRingCat.of ℂ)), y.appLE ⊤ ⊤ le_top = y.appTop :=
    fun Y y => (y.app_eq_appLE (U := ⊤)).symm
  have hc : ∀ (Y : Scheme.{0}) (y : Y ⟶ Spec (CommRingCat.of ℂ)) (z : Y), constRes y z =
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ y.appTop ≫ Y.evaluation ⊤ z trivial).hom := by
    intro Y y z
    rw [← hA]; rfl
  rw [hc, hc, ← CommRingCat.hom_comp]
  congr 1
  simp only [Category.assoc]
  rw [Scheme.evaluation_naturality g x (V := ⊤) trivial, ← hg, Scheme.Hom.comp_appTop,
    Category.assoc]
  rfl

theorem val_ringHom [LocallyOfFiniteType s] (U : S.Opens) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) :
    ∃ φ : Γ(S, U) →+* ℂ, ∀ f, φ f = val s f x hx := by
  refine ⟨(residueFieldIsoBase s x hc).hom.hom.comp (S.evaluation U x hx).hom, fun f => ?_⟩
  unfold val
  rw [valHom_eq s x hc]
  rfl

theorem val_const [LocallyOfFiniteType s] (U : S.Opens) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) (c : ℂ) : val s (constSec s U c) x hx = c := by
  unfold val
  rw [constSec_res s U c, evaluation_res le_top _ x hx, valHom_eq s x hc]
  exact DFunLike.congr_fun (valHom_spec s x hc) c

theorem val_restrict {U V : S.Opens} (hVU : V ≤ U) (f : Γ(S, U)) (x : S) (hx : x ∈ V) :
    val s (S.presheaf.map (homOfLE hVU).op f) x hx = val s f x (hVU hx) := by
  unfold val
  rw [evaluation_res hVU f x hx]

theorem val_eq_zero_iff [LocallyOfFiniteType s] {U : S.Opens} (f : Γ(S, U)) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) : val s f x hx = 0 ↔ S.evaluation U x hx f = 0 := by
  unfold val
  rw [valHom_eq s x hc]
  exact map_eq_zero_iff _ (residueFieldIsoBase s x hc).commRingCatIsoToRingEquiv.injective

theorem val_comp {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (g : S ⟶ T) (hg : g ≫ t = s)
    [LocallyOfFiniteType s] [LocallyOfFiniteType t] {U : T.Opens} {V : S.Opens} (hVU : V ≤ g ⁻¹ᵁ U)
    (f : Γ(T, U)) (x : S) (hx : x ∈ V) (hc : IsClosed ({x} : Set S)) :
    IsClosed ({g.base x} : Set T) ∧ val s (g.appLE U V hVU f) x hx = val t f (g.base x) (hVU hx) := by
  have hcl := isClosed_image_of_closed s t g hg x hc
  refine ⟨hcl, ?_⟩
  have hmor : g.appLE U V hVU ≫ S.evaluation V x hx =
      T.evaluation U (g.base x) (hVU hx) ≫ g.residueFieldMap x := by
    rw [Scheme.evaluation_naturality g x (V := U) (hVU hx :), Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp only [Scheme.evaluation, TopCat.Presheaf.germ_res_assoc]
  have hres : (residueFieldIsoBase s x hc).hom.hom.comp (g.residueFieldMap x).hom =
      (residueFieldIsoBase t (g.base x) hcl).hom.hom := by
    apply valHom_unique t (g.base x) hcl
    rw [RingHom.comp_assoc, residueFieldMap_constRes s t g hg x, valHom_spec s x hc]
  unfold val
  rw [valHom_eq s x hc, valHom_eq t (g.base x) hcl, ← hres]
  show _ = ((residueFieldIsoBase s x hc).hom.hom.comp (g.residueFieldMap x).hom)
    ((T.evaluation U (g.base x) (hVU hx)).hom f)
  rw [RingHom.comp_apply, ← RingHom.comp_apply (g.residueFieldMap x).hom, ← CommRingCat.hom_comp,
    ← hmor]
  rfl

end

end ReciprocityTheory.AnForm.R
end

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCA
namespace ReciprocityTheory.AnForm.R.BaseChangeC

open MvPolynomial TensorProduct

section FracTensor

variable (ι : Type) (F : Type) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial ι ℚ) F]
  [IsScalarTower ℚ (MvPolynomial ι ℚ) F] [IsFractionRing (MvPolynomial ι ℚ) F]
  (C : Type) [Field C] [Algebra ℚ C]

theorem fracTensor_exists_den (z : F ⊗[ℚ] C) :
    ∃ s ∈ nonZeroDivisors (MvPolynomial ι ℚ), ∃ w : MvPolynomial ι ℚ ⊗[ℚ] C,
      (algebraMap (MvPolynomial ι ℚ) F s ⊗ₜ[ℚ] (1 : C)) * z =
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F)
          (AlgHom.id ℚ C) w := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, 0, by simp⟩
  | tmul a c =>
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (MvPolynomial ι ℚ)) a
    refine ⟨(s : MvPolynomial ι ℚ), s.2, x ⊗ₜ[ℚ] c, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.map_tmul, mul_comm, hs]
    rfl
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨s₁, hs₁, w₁, e₁⟩ := h₁
    obtain ⟨s₂, hs₂, w₂, e₂⟩ := h₂
    refine ⟨s₁ * s₂, mul_mem hs₁ hs₂,
      (s₂ ⊗ₜ[ℚ] (1 : C)) * w₁ + (s₁ ⊗ₜ[ℚ] (1 : C)) * w₂, ?_⟩
    have hΦ : ∀ t : MvPolynomial ι ℚ,
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F) (AlgHom.id ℚ C)
          (t ⊗ₜ[ℚ] (1 : C)) = algebraMap (MvPolynomial ι ℚ) F t ⊗ₜ[ℚ] (1 : C) := fun t => by
      rw [Algebra.TensorProduct.map_tmul]; rfl
    have hsplit : (algebraMap (MvPolynomial ι ℚ) F s₁ * algebraMap (MvPolynomial ι ℚ) F s₂) ⊗ₜ[ℚ] (1 : C) =
        (algebraMap (MvPolynomial ι ℚ) F s₁ ⊗ₜ[ℚ] (1 : C)) *
          (algebraMap (MvPolynomial ι ℚ) F s₂ ⊗ₜ[ℚ] (1 : C)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp only [map_add (f := _), map_mul, hΦ]
    rw [← e₁, ← e₂, hsplit]
    ring

include ι in
theorem isDomain_tensor_of_isFractionRing : IsDomain (F ⊗[ℚ] C) := by
  have h1 : Function.Injective (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F) :=
    IsFractionRing.injective (MvPolynomial ι ℚ) F
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F) (AlgHom.id ℚ C)) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := C)
      (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F).toLinearMap h1
  let e : MvPolynomial ι ℚ ⊗[ℚ] C ≃+* MvPolynomial ι C :=
    (Algebra.TensorProduct.comm ℚ (MvPolynomial ι ℚ) C).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv (σ := ι) ℚ C).toRingEquiv
  haveI hD : IsDomain (MvPolynomial ι ℚ ⊗[ℚ] C) := Function.Injective.isDomain e e.injective
  haveI : Nontrivial (F ⊗[ℚ] C) := hinj.nontrivial
  have hu : ∀ s ∈ nonZeroDivisors (MvPolynomial ι ℚ),
      IsUnit (algebraMap (MvPolynomial ι ℚ) F s ⊗ₜ[ℚ] (1 : C)) := by
    intro s hs
    have h0 : algebraMap (MvPolynomial ι ℚ) F s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    exact (isUnit_iff_ne_zero.mpr h0).map
      (Algebra.TensorProduct.includeLeftRingHom (R := ℚ) (A := F) (B := C))
  haveI nzd : NoZeroDivisors (F ⊗[ℚ] C) := by
    constructor
    intro a b hab
    obtain ⟨s₁, hs₁, w₁, e₁⟩ := fracTensor_exists_den ι F C a
    obtain ⟨s₂, hs₂, w₂, e₂⟩ := fracTensor_exists_den ι F C b
    have hw : Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F)
        (AlgHom.id ℚ C) (w₁ * w₂) = 0 := by
      rw [map_mul, ← e₁, ← e₂]
      calc _ = (algebraMap (MvPolynomial ι ℚ) F s₁ ⊗ₜ[ℚ] (1 : C)) *
            (algebraMap (MvPolynomial ι ℚ) F s₂ ⊗ₜ[ℚ] (1 : C)) * (a * b) := by ring
        _ = 0 := by rw [hab, mul_zero]
    have hw0 : w₁ * w₂ = 0 := hinj (by rw [hw, map_zero])
    rcases mul_eq_zero.mp hw0 with h | h
    · left
      have h' : (algebraMap (MvPolynomial ι ℚ) F s₁ ⊗ₜ[ℚ] (1 : C)) * a = 0 := by
        rw [e₁, h, map_zero]
      exact ((hu s₁ hs₁).mul_right_eq_zero).mp h'
    · right
      have h' : (algebraMap (MvPolynomial ι ℚ) F s₂ ⊗ₜ[ℚ] (1 : C)) * b = 0 := by
        rw [e₂, h, map_zero]
      exact ((hu s₂ hs₂).mul_right_eq_zero).mp h'
  exact NoZeroDivisors.to_isDomain _

end FracTensor

section Red

attribute [-instance] DivisionRing.toRatAlgebra

theorem isReduced_tensor_domain (F K D : Type) [Field F] [Field K] [Algebra F K]
    [Algebra.FormallyUnramified F K] [Algebra.EssFiniteType F K] [CommRing D] [IsDomain D]
    [Algebra F D] : IsReduced (K ⊗[F] D) := by
  let M := FractionRing D
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id F K)
      (IsScalarTower.toAlgHom F D M)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  have : IsReduced (K ⊗[F] M) := by
    have := Algebra.FormallyUnramified.isReduced_of_field M (M ⊗[F] K)
    exact isReduced_of_injective (Algebra.TensorProduct.comm F K M).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm F K M).injective
  exact isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id F K)
      (IsScalarTower.toAlgHom F D M)).toRingHom hinj

theorem isReduced_tensor_of_essFiniteType (K : Type) [Field K] [Algebra ℚ K]
    [Algebra.EssFiniteType ℚ K] (C : Type) [Field C] [Algebra ℚ C] : IsReduced (K ⊗[ℚ] C) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ K
  set F0 := IntermediateField.adjoin ℚ (Set.range ((↑) : s → K))
  have : Algebra.IsAlgebraic F0 K := hs.isAlgebraic_field
  have : PerfectField F0 :=
    @PerfectField.ofCharZero F0 _ (charZero_of_injective_algebraMap (algebraMap ℚ F0).injective)
  have : Algebra.IsSeparable F0 K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Algebra.FormallyUnramified F0 K := Algebra.FormallyUnramified.of_isSeparable F0 K
  have : Algebra.EssFiniteType F0 K := Algebra.EssFiniteType.of_comp ℚ F0 K
  let e := hs.1.aevalEquivField
  letI : Algebra (MvPolynomial s ℚ) F0 :=
    (e.toRingEquiv.toRingHom.comp (algebraMap (MvPolynomial s ℚ) (FractionRing (MvPolynomial s ℚ)))).toAlgebra
  have := IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := MvPolynomial s ℚ) (A := F0)
    (Subsingleton.elim _ _)
  let e' : FractionRing (MvPolynomial s ℚ) ≃ₐ[MvPolynomial s ℚ] F0 :=
    { e.toRingEquiv with commutes' := fun _ => rfl }
  have : IsFractionRing (MvPolynomial s ℚ) F0 :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors (MvPolynomial s ℚ)) e'
  have : IsDomain (F0 ⊗[ℚ] C) := isDomain_tensor_of_isFractionRing s F0 C
  have : IsReduced (K ⊗[F0] (F0 ⊗[ℚ] C)) := isReduced_tensor_domain F0 K (F0 ⊗[ℚ] C)
  exact isReduced_of_injective
    (Algebra.TensorProduct.cancelBaseChange ℚ F0 K K C).symm.toRingEquiv.toRingHom
    (Algebra.TensorProduct.cancelBaseChange ℚ F0 K K C).symm.injective

end Red

end ReciprocityTheory.AnForm.R.BaseChangeC
end
