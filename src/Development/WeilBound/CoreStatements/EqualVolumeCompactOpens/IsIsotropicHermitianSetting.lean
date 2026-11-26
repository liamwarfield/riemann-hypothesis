module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Definitions.AdelicLattices.IsSelfDualLat
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

section General

variable {R : Type} [CommRing R] {N : ℕ}

def uGrp (σ : R →+* R) (J : Matrix (Fin N) (Fin N) R) : Subgroup (GL (Fin N) R) where
  carrier := {g | (g : Matrix (Fin N) (Fin N) R)ᵀ * J * (g : Matrix (Fin N) (Fin N) R).map σ = J}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, Matrix.transpose_mul, Matrix.map_mul] at *
    calc _ = (b : Matrix (Fin N) (Fin N) R)ᵀ * ((a : Matrix (Fin N) (Fin N) R)ᵀ * J *
          (a : Matrix (Fin N) (Fin N) R).map σ) * (b : Matrix (Fin N) (Fin N) R).map σ := by
            simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    calc _ = ((a⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R)ᵀ * ((a : Matrix (Fin N) (Fin N) R)ᵀ * J *
          (a : Matrix (Fin N) (Fin N) R).map σ) * ((a⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R).map σ := by
            rw [ha]
      _ = ((a : Matrix (Fin N) (Fin N) R) * ((a⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R))ᵀ * J *
          ((a : Matrix (Fin N) (Fin N) R) * ((a⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R)).map σ := by
            simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv]; simp

def suGrp (σ : R →+* R) (J : Matrix (Fin N) (Fin N) R) : Subgroup (GL (Fin N) R) :=
  uGrp σ J ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin N) R →* Rˣ).ker

def congGrp (Λ Λ' : AddSubgroup (Fin N → R)) : Subgroup (GL (Fin N) R) where
  carrier := {g | (∀ x, x ∈ Λ ↔ (g : Matrix (Fin N) (Fin N) R) *ᵥ x ∈ Λ) ∧
    ∀ x ∈ Λ, (g : Matrix (Fin N) (Fin N) R) *ᵥ x - x ∈ Λ'}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← ha, ← hb]
    · have h := Λ'.add_mem (ha' _ ((hb x).1 hx)) (hb' x hx)
      rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      simpa using h
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have e : ∀ x, (a : Matrix (Fin N) (Fin N) R) *ᵥ
        (((a⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) *ᵥ x) = x := fun x => by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · rw [ha (((a⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) *ᵥ x), e]
    · have hy : ((a⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) *ᵥ x ∈ Λ := by rw [ha, e]; exact hx
      have h := Λ'.neg_mem (ha' _ hy)
      rw [e] at h
      simpa using h

end General

section NumberFields

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

abbrev Adf : Type := FiniteAdeleRing (𝓞 F) F ⊗[F] E

def inclAd : E →+* Adf F E := (Algebra.TensorProduct.includeRight : E →ₐ[F] Adf F E).toRingHom

variable {F E}

def sigAd (c : E ≃ₐ[F] E) : Adf F E →+* Adf F E :=
  (Algebra.TensorProduct.map (AlgHom.id F (FiniteAdeleRing (𝓞 F) F)) c.toAlgHom).toRingHom

variable (F)

def hatLat (Λ : AddSubgroup (Fin N → E)) : AddSubgroup (Fin N → Adf F E) :=
  AddSubgroup.closure {y | ∃ a : FiniteAdeleRing (𝓞 F) F,
    (∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F) ∧ ∃ x ∈ Λ, y = fun i => a ⊗ₜ[F] x i}

variable {F}

def levelGrp (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E))
    (𝔞 : Ideal (𝓞 E)) : Subgroup (GL (Fin N) E) :=
  uGrp σ J ⊓ congGrp Λ.toAddSubgroup (𝔞 • Λ).toAddSubgroup

def adLevelGrp (c : E ≃ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E))
    (𝔞 : Ideal (𝓞 E)) : Subgroup (GL (Fin N) (Adf F E)) :=
  suGrp (sigAd c) (J.map (inclAd F E)) ⊓
    congGrp (hatLat F Λ.toAddSubgroup) (hatLat F (𝔞 • Λ).toAddSubgroup)

def AdGenus (c : E ≃ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (Λ Λ' : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  ∃ g ∈ uGrp (sigAd c) (J.map (inclAd F E)), ∀ x,
    x ∈ hatLat F Λ.toAddSubgroup ↔ (g : Matrix (Fin N) (Fin N) (Adf F E)) *ᵥ x ∈ hatLat F Λ'.toAddSubgroup

end NumberFields

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cmp
open scoped TensorProduct

scoped instance topAdf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    TopologicalSpace (Adf F E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (Adf F E)

section defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

def UA (c : E ≃ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) : Subgroup (GL (Fin N) (Adf F E)) :=
  uGrp (sigAd c) (J.map (inclAd F E))

def SUA (c : E ≃ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) : Subgroup (GL (Fin N) (Adf F E)) :=
  suGrp (sigAd c) (J.map (inclAd F E))

def IsCO (c : E ≃ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (K : Subgroup (GL (Fin N) (Adf F E))) : Prop :=
  K ≤ SUA c J ∧ IsCompact (K : Set (GL (Fin N) (Adf F E))) ∧
    ∃ O : Set (GL (Fin N) (Adf F E)), IsOpen O ∧ O ∩ (SUA c J : Set (GL (Fin N) (Adf F E))) = K


variable (F) in
def diagGL : GL (Fin N) E →* GL (Fin N) (Adf F E) := Matrix.GeneralLinearGroup.map (inclAd F E)

def rat (K : Subgroup (GL (Fin N) (Adf F E))) : Subgroup (GL (Fin N) E) := K.comap (diagGL F)

def IsIsotropicHermitianSetting (c : E ≃ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) : Prop :=
  Module.finrank F E = 2 ∧ c ≠ 1 ∧ Jᵀ = J.map c ∧ IsUnit J.det ∧
    ∃ e : Fin N → E, e ≠ 0 ∧ ∑ i, ∑ j, e i * J i j * c (e j) = 0

def IsLat (Λ : Submodule (𝓞 E) (Fin N → E)) : Prop := Λ.FG ∧ Submodule.span E (Λ : Set (Fin N → E)) = ⊤

def Neat (c : E ≃ₐ[F] E) (𝔞 : Ideal (𝓞 E)) : Prop :=
  ∀ z : 𝓞 E, (z : E) * c (z : E) = 1 → z - 1 ∈ 𝔞 → z = 1

end defs

abbrev conjBy {G : Type} [Group G] (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

def EqIdx {G : Type} [Group G] (A B : Subgroup G) : Prop := A.relIndex B = B.relIndex A ∧ A.relIndex B ≠ 0

def TopRing : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsTopologicalRing (Adf F E) ∧ T2Space (Adf F E) ∧ ∀ c : E ≃ₐ[F] E, Continuous (sigAd c)

def CoInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (c : E ≃ₐ[F] E)
    (J : Matrix (Fin N) (Fin N) E) (K K' : Subgroup (GL (Fin N) (Adf F E))),
    IsCO c J K → IsCO c J K' → IsCO c J (K ⊓ K') ∧ K.relIndex K' ≠ 0

def CoConj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (c : E ≃ₐ[F] E)
    (J : Matrix (Fin N) (Fin N) E) (K : Subgroup (GL (Fin N) (Adf F E))),
    IsCO c J K → ∀ g ∈ UA c J, IsCO c J (conjBy g K)

def CoSA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (c : E ≃ₐ[F] E)
    (J : Matrix (Fin N) (Fin N) E) (K : Subgroup (GL (Fin N) (Adf F E))),
    IsIsotropicHermitianSetting c J → IsCO c J K → ∀ s ∈ SUA c J, ∃ γ ∈ suGrp c.toRingHom J, ∃ k ∈ K, s = diagGL F γ * k

def Divisible : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (c : E ≃ₐ[F] E)
    (J : Matrix (Fin N) (Fin N) E), IsIsotropicHermitianSetting c J →
    suGrp c.toRingHom J ≤
      Subgroup.closure {x : GL (Fin N) E | ∀ n : ℕ, 0 < n → ∃ y ∈ suGrp c.toRingHom J, y ^ n = x}

def PowerScalar : Prop :=
  ∀ (R : Type) [CommRing R] (N : ℕ) (σ : R →+* R) (J : Matrix (Fin N) (Fin N) R), IsUnit J.det →
    ∀ g ∈ uGrp σ J, ∃ n : ℕ, 0 < n ∧ ∃ z ∈ uGrp σ J, z ∈ Subgroup.center (GL (Fin N) R) ∧
      ∃ s ∈ suGrp σ J, g ^ n = z * s

def IndexEq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (c : E ≃ₐ[F] E)
    (J : Matrix (Fin N) (Fin N) E) (K : Subgroup (GL (Fin N) (Adf F E))),
    IsIsotropicHermitianSetting c J → IsCO c J K → ∀ g ∈ UA c J, EqIdx (rat K) (rat (conjBy g K))

def HatCompactOpen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ)
    (Λ : Submodule (𝓞 E) (Fin N → E)), IsLat Λ →
    IsCompact (hatLat F Λ.toAddSubgroup : Set (Fin N → Adf F E)) ∧
      IsOpen (hatLat F Λ.toAddSubgroup : Set (Fin N → Adf F E))

def CongCompactOpen : Prop :=
  ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] (N : ℕ)
    (Λ Λ' : AddSubgroup (Fin N → R)), IsCompact (Λ : Set (Fin N → R)) → IsOpen (Λ : Set (Fin N → R)) →
    IsOpen (Λ' : Set (Fin N → R)) → (∃ u : Rˣ, ∀ i, Pi.single i (u : R) ∈ Λ) →
    IsCompact (congGrp Λ Λ' : Set (GL (Fin N) R)) ∧ IsOpen (congGrp Λ Λ' : Set (GL (Fin N) R))

def LevelCO : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (c : E ≃ₐ[F] E)
    (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) (𝔞 : Ideal (𝓞 E)),
    IsLat Λ → 𝔞 ≠ ⊥ → IsCO c J (adLevelGrp c J Λ 𝔞)

def LevelConj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (c : E ≃ₐ[F] E)
    (J : Matrix (Fin N) (Fin N) E) (Λ Λ' : Submodule (𝓞 E) (Fin N → E)) (𝔞 : Ideal (𝓞 E)),
    ∀ g ∈ UA c J, (∀ x, x ∈ hatLat F Λ.toAddSubgroup ↔
      (g : Matrix (Fin N) (Fin N) (Adf F E)) *ᵥ x ∈ hatLat F Λ'.toAddSubgroup) →
    conjBy g (adLevelGrp c J Λ 𝔞) = adLevelGrp c J Λ' 𝔞

def HatRat : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ)
    (Λ : Submodule (𝓞 E) (Fin N → E)), IsLat Λ →
    ∀ x : Fin N → E, (fun i => inclAd F E (x i)) ∈ hatLat F Λ.toAddSubgroup ↔ x ∈ Λ

def LevelRat : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (c : E ≃ₐ[F] E)
    (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) (𝔞 : Ideal (𝓞 E)),
    IsLat Λ → 𝔞 ≠ ⊥ → IsUnit J.det → Neat c 𝔞 → rat (adLevelGrp c J Λ 𝔞) = levelGrp c.toRingHom J Λ 𝔞

def LevelIndexEq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (c : E ≃ₐ[F] E)
    (J : Matrix (Fin N) (Fin N) E) (Λ Λ' : Submodule (𝓞 E) (Fin N → E)) (𝔞 : Ideal (𝓞 E)),
    IsIsotropicHermitianSetting c J → IsLat Λ → IsLat Λ' → 𝔞 ≠ ⊥ → Neat c 𝔞 → AdGenus c J Λ Λ' →
    EqIdx (levelGrp c.toRingHom J Λ 𝔞) (levelGrp c.toRingHom J Λ' 𝔞)

theorem levelIndexEq_of (h1 : IndexEq) (h2 : LevelCO) (h3 : LevelConj) (h4 : LevelRat) : LevelIndexEq := by
  intro F E _ _ _ _ _ N c J Λ Λ' 𝔞 hS hΛ hΛ' h𝔞 hN ⟨g, hg, hgΛ⟩
  have h := h1 F E N c J _ hS (h2 F E N c J Λ 𝔞 hΛ h𝔞) g hg
  rwa [h3 F E N c J Λ Λ' 𝔞 g hg hgΛ, h4 F E N c J Λ 𝔞 hΛ h𝔞 hS.2.2.2.1 hN,
    h4 F E N c J Λ' 𝔞 hΛ' h𝔞 hS.2.2.2.1 hN] at h

end PositivityTheory.EqVol
