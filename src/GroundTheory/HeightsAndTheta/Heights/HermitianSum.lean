module

public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleSheaf

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HermitianSum
namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt

noncomputable section

section Core

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

@[instance_reducible]
def coreComap (h : InnerProductSpace.Core ℂ W) (f : V →ₗ[ℂ] W) (hf : Function.Injective f) :
    InnerProductSpace.Core ℂ V where
  inner x y := h.inner (f x) (f y)
  conj_inner_symm x y := h.conj_inner_symm (f x) (f y)
  re_inner_nonneg x := h.re_inner_nonneg (f x)
  add_left x y z := by simp only [map_add (f := _), h.add_left]
  smul_left x y r := by simp only [map_smul, h.smul_left]
  definite x hx := hf (by rw [map_zero]; exact h.definite _ hx)

theorem coreComap_inner (h : InnerProductSpace.Core ℂ W) (f : V →ₗ[ℂ] W)
    (hf : Function.Injective f) (x y : V) :
    (coreComap h f hf).inner x y = h.inner (f x) (f y) := rfl

end Core

variable {K : Type*} [Field K]

section Split

variable (σ : K →+* ℂ) (E F : Type*) [AddCommGroup E] [Module (𝓞 K) E] [AddCommGroup F]
  [Module (𝓞 K) F]

variable {σ E F}

end Split

variable [NumberField K]

variable {E F : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] [AddCommGroup F] [Module (𝓞 K) F] [Module.Finite (𝓞 K) F]
  [Module.Projective (𝓞 K) F]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FinrankFibreAtOfIsInvertibleSheaf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

def Via {R : Type*} [CommRing R] (_φ : R →+* ℂ) : Type := ℂ

namespace Via

variable {R : Type*} [CommRing R] (φ : R →+* ℂ)

instance : Field (Via φ) := inferInstanceAs (Field ℂ)

instance : Algebra R (Via φ) := φ.toAlgebra

def ofComplex : ℂ ≃+* Via φ := RingEquiv.refl ℂ

end Via

variable {X : Scheme.{u}} (L : X.Modules)


variable (X) in
abbrev locRing (X : Scheme.{u}) (p : X) : CommRingCat.{u} :=
  TopCat.Presheaf.stalk (X := X.toTopCat) X.sheaf.obj p

abbrev modStalk (p : X) : Type u :=
  TopCat.Presheaf.stalk (X := X.toTopCat) (C := Ab.{u}) ((preMod X).obj L).presheaf p

def fibreAt (p : X) (φ : locRing X p →+* ℂ) : Type u :=
  TensorProduct (locRing X p) (Via φ) (modStalk L p)

variable {L}

def germM {U : X.Opens} {p : X} (hp : p ∈ U) (s : ((preMod X).obj L).obj (op U)) :
    modStalk L p :=
  TopCat.Presheaf.germ (X := X.toTopCat) (C := Ab.{u}) ((preMod X).obj L).presheaf U p hp s

def germR {U : X.Opens} {p : X} (hp : p ∈ U) (r : ringOn X U) : locRing X p :=
  TopCat.Presheaf.germ (X := X.toTopCat) X.sheaf.obj U p hp r

lemma germM_smul {U : X.Opens} {p : X} (hp : p ∈ U) (r : ringOn X U)
    (s : ((preMod X).obj L).obj (op U)) : germM hp (r • s) = germR hp r • germM hp s :=
  PresheafOfModules.germ_smul _ _ _ _ _ _

lemma germM_resM {U V : X.Opens} (hVU : V ≤ U) {p : X} (hp : p ∈ V)
    (s : ((preMod X).obj L).obj (op U)) : germM hp (resM _ hVU s) = germM (hVU hp) s :=
  TopCat.Presheaf.germ_res_apply (X := X.toTopCat) (C := Ab.{u}) ((preMod X).obj L).presheaf
    (homOfLE hVU) p hp s

lemma germR_resR {U V : X.Opens} (hVU : V ≤ U) {p : X} (hp : p ∈ V) (r : ringOn X U) :
    germR hp (resR hVU r) = germR (hVU hp) r :=
  TopCat.Presheaf.germ_res_apply (X := X.toTopCat) X.sheaf.obj (homOfLE hVU) p hp r

lemma germM_zero {U : X.Opens} {p : X} (hp : p ∈ U) :
    germM (L := L) hp (0 : ((preMod X).obj L).obj (op U)) = 0 :=
  map_zero _

theorem bijective_smul_germ {U : X.Opens} {p : X} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) :
    Function.Bijective (fun r : locRing X p => r • germM hp e) := by
  have key : ∀ r : locRing X p, r • germM hp e = 0 → r = 0 := by
    intro r hr
    obtain ⟨V, hVU, hpV, r', rfl⟩ :=
      TopCat.Presheaf.exists_le_germ_eq (X := X.toTopCat) X.sheaf.obj r hp
    change germR hpV r' • germM hp e = 0 at hr
    rw [← germM_resM hVU hpV, ← germM_smul] at hr
    obtain ⟨W, hpW, iV, iV', hW⟩ := TopCat.Presheaf.germ_eq (X := X.toTopCat) (C := Ab.{u})
      ((preMod X).obj L).presheaf p hpV hpV _ 0 (hr.trans (germM_zero hpV).symm)
    have h0 : resR iV.le r' • resM _ (iV.le.trans hVU) e = 0 := by
      rw [← resM_smul_res]
      exact hW.trans (map_zero _)
    have hz : resR iV.le r' = 0 :=
      (he W (iV.le.trans hVU)).1 (a₁ := resR iV.le r') (a₂ := 0) (by
        simp only [zero_smul]; exact h0)
    change germR hpV r' = 0
    rw [← germR_resR iV.le hpW, hz]
    exact map_zero _
  constructor
  · intro r₁ r₂ h
    have := key (r₁ - r₂) (by simp only at h; rw [sub_smul, h, sub_self])
    exact sub_eq_zero.mp this
  · intro m
    obtain ⟨V, hVU, hpV, t, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq (X := X.toTopCat)
      (C := Ab.{u}) ((preMod X).obj L).presheaf m hp
    obtain ⟨r, hr⟩ := (he V hVU).2 t
    refine ⟨germR hpV r, ?_⟩
    change germR hpV r • germM hp e = germM hpV t
    rw [← hr, germM_smul, germM_resM]

def stalkEquiv {U : X.Opens} {p : X} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) : locRing X p ≃ₗ[locRing X p] modStalk L p :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ (germM hp e)) (bijective_smul_germ hp he)

section Fibre

variable {p : X} {φ : locRing X p →+* ℂ}

instance : AddCommGroup (fibreAt L p φ) :=
  inferInstanceAs (AddCommGroup (TensorProduct (locRing X p) (Via φ) (modStalk L p)))

instance : Module (Via φ) (fibreAt L p φ) :=
  inferInstanceAs (Module (Via φ) (TensorProduct (locRing X p) (Via φ) (modStalk L p)))

instance : Module ℂ (fibreAt L p φ) :=
  Module.compHom (fibreAt L p φ) (Via.ofComplex φ).toRingHom

lemma complex_smul_def (c : ℂ) (s : fibreAt L p φ) : c • s = Via.ofComplex φ c • s := rfl


variable (L φ) in
def fibreMk (c : Via φ) (m : modStalk L p) : fibreAt L p φ :=
  (c ⊗ₜ[locRing X p] m : TensorProduct (locRing X p) (Via φ) (modStalk L p))


variable (φ) in
def value {U : X.Opens} (hp : p ∈ U) (s : ((preMod X).obj L).obj (op U)) : fibreAt L p φ :=
  fibreMk (L := L) (φ := φ) 1 (germM hp s)


variable (φ) in
def fibreEquiv {U : X.Opens} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) : fibreAt L p φ ≃ₗ[Via φ] Via φ :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Via φ) (Via φ))
    (stalkEquiv hp he).symm).trans
      (TensorProduct.AlgebraTensorModule.rid (locRing X p) (Via φ) (Via φ))



end Fibre

end

end GroundTheory.Heights₂.Heights
end
