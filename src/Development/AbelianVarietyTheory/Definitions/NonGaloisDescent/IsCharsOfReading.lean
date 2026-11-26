module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharsOfReading
noncomputable section

namespace GlobalTheory.Triple.Model

open NumberField IsDedekindDomain Polynomial ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open Neutral.B1 hiding IsPlaceOver
open Formalism.L2.Host (HChar CharFrame embLL0 eExp ValLL0)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ block)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE toFb)
open scoped TensorProduct

variable {D : D7}

section Indep

variable {C : CharFrame D} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
  {i : X.Tw} {b : Bool}

theorem notMem_l {k : Fin 2} (hk : X.l i ≠ D.host.g k) (v : D.nd.PlG k) :
    ((X.l i : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal :=
  GlobalTheory.GalChar.notMem_of_ne (D.host.g_prime k) (X.lPrime i).out hk.symm (D.naut.plGw_over k v)

end Indep

section Tame

variable (C : CharFrame D) (art : Ideles D.host.E →* Gab D.host.E D.nd.Om)

variable {C art}

end Tame

section Record

variable (D) (C : CharFrame D) {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} (ha : IsGlobalArtin art) (hC : ValLL0 D C)
  (hs : ∀ x : ↥D.LL0, star (x : D.what₂.LL) ∈ D.LL0)

def rd (i : D.ntw.Tw) : Reading D.ntw i true := (Reading.nonempty i true).some



structure Chars (art : Ideles D.host.E →* Gab D.host.E D.nd.Om) (i : D.ntw.Tw) where
  delta : GalE D →* (D.ntw.O0 i)ˣ
  chi1 : ℕ → Bool → (GalE D →* (D.ntw.O0 i)ˣ)
  gal : ∀ (j : Fin D.R.m) (b : Bool), ∃ n, IsGal art (rd D i).κ (GlobalTheory.GalChar.sideIso (rd D i).ι b)
    (blockChar C (D.ntw.l i) j) n (chi1 (j.1 + 1) b)
  h1 : IsOpen (delta.ker : Set (GalE D))
  h2 : AntiHom D.ntw.cc delta
  h3 : RamExactly delta ↑(D.ntw.pD i)
  h4 : ∀ v ∈ D.ntw.pD i, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
    Nat.card ((Ine (F := D.host.E) A).map delta) = 15
  h5 : ∀ j b, Continuous (fun g => ((chi1 j b g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i))
  h6 : ∀ j b v, v ∉ placesOver D.host.E (D.ntw.l i) → (∀ k, v ∉ placesOver D.host.E (D.host.g k)) → v ∉ D.ntw.pD i →
    ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, chi1 j b σ = 1
  h7 : ∀ j b, ∀ v ∈ D.ntw.pD i, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := D.host.E) A, chi1 j b σ = if b then delta σ else (delta σ)⁻¹
  h8 : ∀ j b k v, v ∈ placesOver D.host.E (D.host.g k) → v ∉ placesOver D.host.E (D.ntw.l i) →
    ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, chi1 j b σ ^ (D.host.g k - 1) = 1


variable {art' : Ideles D.host.E →* Gab D.host.E D.nd.Om} (K : ∀ i, Chars D C art' i) [IsEmpty D.nd.Loc]


end Record

end GlobalTheory.Triple.Model

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LocalisationCoefficientExtensionIsWildInertiaCyc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial

noncomputable section
namespace GlobalTheory.CoefDuty.Model
open GlobalTheory.CoefDuty

section Record
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

variable {N₀ N₁ N₂ : NData R H what₂} {A₀ : NAut N₀} {A₁ : NAut N₁} {A₂ : NAut N₂} {i₀ : N₀.Loc} {i₁ : N₁.Loc} {i₂ : N₂.Loc}

theorem iotaO_injective (N : NData R H what₂) (A : NAut N) (i : N.Loc) : Function.Injective (iotaO N A i) :=
  (((A.iotaQC i).toRingHom.comp (A.iotaQ i)).injective).comp (IsFractionRing.injective (N.O i) (FractionRing (N.O i)))

theorem φ_injective (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : Function.Injective a.φ := fun x y h =>
  iotaO_injective N₀ A₀ i₀ (by rw [← a.φ_iota, ← a.φ_iota, h])

theorem s0_eq (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : N₀.s0 i₀ = N₁.s0 i₁ := by
  by_cases h : N₀.l i₀ = 2
  · rw [N₀.restNLevelExponent_of_two i₀ h, N₁.restNLevelExponent_of_two i₁ (a.l_eq ▸ h)]
  · rw [N₀.restNLevelExponent_of_odd i₀ h, N₁.restNLevelExponent_of_odd i₁ (a.l_eq ▸ h), a.l_eq]

theorem heckePol_map (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) (x : N₁.X i₁) (w : PlE H) (hw : SplitOut N₁ i₁ w) :
    heckePol N₁ i₁ x w = (heckePol N₀ i₀ (a.e x) w).map a.φ := by
  unfold heckePol
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.map_add (f := _), Polynomial.map_pow, map_X, Polynomial.map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  rw [a.hT w k x hw hk.1 hk.2]
  simp

theorem gen_heq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (s : ℕ) (z : ℤ_[p]ˣ) (z' : ℤ_[q]ˣ) (hz : HEq z z') :
    (∃ u : ℤ_[p]ˣ, (z : ℤ_[p]) = 1 + (p : ℤ_[p]) ^ s * (u : ℤ_[p])) ↔
    ∃ u : ℤ_[q]ˣ, (z' : ℤ_[q]) = 1 + (q : ℤ_[q]) ^ s * (u : ℤ_[q]) := by
  subst h
  cases hz
  rfl

theorem localisationCoefficientExtension_isWildInertiaCyclotomic_iff (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) (g : GE N₁) : IsWildInertiaCyclotomicElement N₁ i₁ g ↔ IsWildInertiaCyclotomicElement N₀ i₀ (a.γ g) := by
  unfold IsWildInertiaCyclotomicElement GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsInertiaCyclotomicGeneratorElement
  rw [gen_heq a.l_eq (N₀.s0 i₀) _ _ (a.cyc g), s0_eq a]
  simp only [a.ine, a.wild, a.l_eq]

end Record

section Plain
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem isBounded_umax : IsBounded (Umax L n) := ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using hκ⟩⟩

theorem exists_isClassReps (J : Subgroup (GAf L n)) (T : Finset (GAf L n))
    (hT : ∀ g : GAf L n, ∃ t ∈ T, ∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ g = (γ : GAf L n) * t * κ) :
    ∃ T', IsClassReps J T' := by
  classical
  let q : GAf L n → DoubleCoset.Quotient (GQ L n : Set (GAf L n)) J := DoubleCoset.mk _ _
  have key : ∀ g t : GAf L n, (∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ g = (γ : GAf L n) * t * κ) ↔ q t = q g := by
    intro g t
    rw [DoubleCoset.eq]
    exact ⟨fun ⟨γ, κ, h, e⟩ => ⟨γ, γ.2, κ, h, e⟩, fun ⟨γ, hγ, κ, h, e⟩ => ⟨⟨γ, hγ⟩, κ, h, e⟩⟩
  have hout : ∀ c, q (Quotient.out c) = c := fun c => Quotient.out_eq c
  refine ⟨T.image fun t => (q t).out, fun g => ⟨(q g).out, ⟨?_, (key _ _).2 (hout _)⟩, ?_⟩⟩
  · obtain ⟨t, ht, h⟩ := hT g
    exact Finset.mem_image.2 ⟨t, ht, by rw [(key _ _).1 h]⟩
  · rintro y ⟨hy, h⟩
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hy
    rw [← (key _ _).1 h, hout]

end Plain
end GlobalTheory.CoefDuty.Model
end
end
