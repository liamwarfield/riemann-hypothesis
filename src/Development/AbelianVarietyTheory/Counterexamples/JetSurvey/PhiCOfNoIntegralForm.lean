module

public import Formalism.SharpRestriction.Divisibility.WeightFamilies
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPosHermOfPositive

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.JetGauges.TraceFormDualSystem
open NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

noncomputable abbrev bar (a : 𝓞 E) : 𝓞 E := IsCMField.ringOfIntegersComplexConj E a

section Forms

variable (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y]

def balancedForms : Submodule ℝ (Y →+ Y →+ ℝ) where
  carrier := {β | (∀ x x', β x x' = β x' x) ∧
    ∀ (a : 𝓞 E) (x x' : Y), β (a • x) x' = β x (bar E a • x')}
  add_mem' := by
    rintro β γ ⟨h1, h2⟩ ⟨k1, k2⟩
    refine ⟨fun x x' => ?_, fun a x x' => ?_⟩
    · simp only [AddMonoidHom.add_apply]; rw [h1, k1]
    · simp only [AddMonoidHom.add_apply]; rw [h2, k2]
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro c β ⟨h1, h2⟩
    refine ⟨fun x x' => ?_, fun a x x' => ?_⟩
    · simp only [AddMonoidHom.smul_apply]; rw [h1]
    · simp only [AddMonoidHom.smul_apply]; rw [h2]

variable {E Y}

noncomputable def quad (β : balancedForms E Y) (x : Y) : ℝ := β.1 x x / 2

def IsPosSemidef (β : balancedForms E Y) : Prop := ∀ x : Y, 0 ≤ β.1 x x

def IsPosDef (β : balancedForms E Y) : Prop :=
  ∀ (n : ℕ) (x : Fin n → Y), LinearIndependent ℤ x →
    ∀ t : Fin n → ℝ, t ≠ 0 → 0 < ∑ i, ∑ j, t i * t j * β.1 (x i) (x j)

variable (E Y)

structure Exponent where

  form : Module.Dual (𝓞 E) Y →+ Module.Dual (𝓞 E) Y →+ 𝓞 E
  smul_left : ∀ (a : 𝓞 E) y y', form (a • y) y' = a * form y y'
  hermitian : ∀ y y', form y' y = bar E (form y y')
  pos : ∀ (τ : E →+* ℂ) (y : Module.Dual (𝓞 E) Y), y ≠ 0 → 0 < (τ ((form y y : 𝓞 E) : E)).re

variable {E Y}

variable (E Y)

structure DualSystem where

  n : ℕ

  e : Fin n → Y

  y : Fin n → Module.Dual (𝓞 E) Y
  expand : ∀ x, ∑ j, y j x • e j = x

theorem nonempty_dualSystem [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y] :
    Nonempty (DualSystem E Y) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) Y
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨⟨n, fun j => f (fun k => if j = k then 1 else 0), fun j => LinearMap.proj j ∘ₗ s,
    fun x => ?_⟩⟩
  have hx : f (s x) = x := LinearMap.congr_fun hs x
  calc _ = f (s x) := (LinearMap.pi_apply_eq_sum_univ f (s x)).symm
    _ = x := hx

variable {E Y}

noncomputable def DualSystem.pairing (D : DualSystem E Y) (l : Exponent E Y)
    (β : balancedForms E Y) : ℝ :=
  (∑ j, ∑ k, β.1 (l.form (D.y j) (D.y k) • D.e j) (D.e k)) / 2

variable [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y]

noncomputable def pairing (l : Exponent E Y) (β : balancedForms E Y) : ℝ :=
  (Classical.choice (nonempty_dualSystem E Y)).pairing l β

noncomputable def pairingValues (β : balancedForms E Y) : Set ℝ := Set.range fun l : Exponent E Y => pairing l β

def IsPhiC (β : balancedForms E Y) (r : ℝ) : Prop := IsLeast (pairingValues β) r

end Forms

end GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FunctionalValuesNonempty
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LeastExponentCompare

open NumberField Formalism.MainNotions.ModuliIntegralCharts
open GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem (bar balancedForms quad IsPosSemidef IsPosDef Exponent pairing pairingValues IsPhiC)
open GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace (IsBalancedSpace evalSum)
open GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement (outer IsPosHerm)

variable {E : Type} [Field E] [NumberField E]

theorem finite_projective_iff (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] :
    (Module.Finite (𝓞 E) Y ∧ Module.Projective (𝓞 E) Y) ↔ (Module.Finite ℤ Y ∧ Module.Free ℤ Y) := by
  constructor
  · rintro ⟨hf, hp⟩
    have hfin : Module.Finite ℤ Y := Module.Finite.trans (𝓞 E) Y
    have hfl : Module.Flat ℤ Y := Module.Flat.trans ℤ (𝓞 E) Y
    exact ⟨hfin, inferInstance⟩
  · rintro ⟨hf, hfr⟩
    exact ⟨Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) Y, GlobalTheory.PointStepCompare.projective_of_free E⟩

variable [IsCMField E] {cj : E → E}

def IsConj (cj : E → E) : Prop := ∀ c : 𝓞 E, cj c = IsCMField.complexConj E (c : E)

variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

theorem isBalancedSpace (h : IsConj cj) : IsBalancedSpace E (SymB cj Y) := by
  intro β
  change ((∀ a b, β a b = β b a) ∧ ∀ (c c' : 𝓞 E), (c' : E) = cj (c : E) → ∀ a b, β (c • a) b = β a (c' • b)) ↔ _
  constructor
  · rintro ⟨hs, hb⟩
    refine ⟨hs, fun a x y => hb a _ ?_ x y⟩
    rw [h a, IsCMField.coe_ringOfIntegersComplexConj]
  · rintro ⟨hs, hb⟩
    refine ⟨hs, fun c c' hc x y => ?_⟩

    have hc' : c' = IsCMField.ringOfIntegersComplexConj E c := by
      apply RingOfIntegers.ext
      rw [hc, h c, IsCMField.coe_ringOfIntegersComplexConj]
    rw [hc']
    exact hb c x y


variable (Y) in
def formsEquiv (h : IsConj cj) : SymB cj Y ≃ₗ[ℝ] balancedForms E Y where
  toFun β := ⟨AddMonoidHom.mk' (fun x => ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) x).toAddMonoidHom)
      (fun x x' => by ext y; simp),
    ((isBalancedSpace h _).1 β.2).1, ((isBalancedSpace h _).1 β.2).2⟩
  invFun β := ⟨LinearMap.mk₂ ℤ (fun x y => β.1 x y) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) (fun _ _ _ => by simp),
    (isBalancedSpace h _).2 ⟨β.2.1, β.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def Admissible (l : SymB cj Y →ₗ[ℝ] ℝ) : Prop :=
  (∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) ∧
    ∀ β : SymB cj Y, (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β

def functionalValues (b : SymB cj Y) : Set ℝ := {x | ∃ l : SymB cj Y →ₗ[ℝ] ℝ, Admissible l ∧ x = l b}

variable [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y]

theorem functionalValues_nonempty (h : IsConj cj) (b : SymB cj Y) : (functionalValues b).Nonempty := by
  obtain ⟨_, _⟩ := (finite_projective_iff (E := E) Y).1 ⟨inferInstance, inferInstance⟩
  obtain ⟨l, hi, hp⟩ := GlobalTheory.PointStepCompare.exists_admissible E (isBalancedSpace (Y := Y) h)
  exact ⟨l b, l, ⟨hi, hp⟩, rfl⟩

section Host

open Formalism.BasicNotions

end Host

end GlobalTheory.LeastExponentCompare

end
end

noncomputable section
open NumberField Formalism.MainNotions.ModuliIntegralCharts
open GlobalTheory.LeastExponentCompare
open scoped Pointwise

namespace GlobalTheory.LeastExponentProbe

variable {E : Type} [Field E] [NumberField E] {cj : E → E}
variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

def vals (b : SymB cj Y) : Set ℝ := {x | ∃ l : SymB cj Y →ₗ[ℝ] ℝ,
    (∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) ∧
    (∀ β : SymB cj Y, (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β) ∧ x = l b}

theorem phiC_def (b : SymB cj Y) : phiC cj b = sInf (vals b) := rfl

private lemma vals_eq_functionalValues [IsCMField E] (b : SymB cj Y) : vals b = functionalValues b := by
  ext x
  constructor
  · rintro ⟨l, h1, h2, hx⟩
    exact ⟨l, ⟨h1, h2⟩, hx⟩
  · rintro ⟨l, ⟨h1, h2⟩, hx⟩
    exact ⟨l, h1, h2, hx⟩

section CM

variable [IsCMField E] [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y]

theorem one_le_phiC (h : IsConj cj) (b : SymB cj Y)
    (hint : ∀ a c, ∃ z : ℤ, (b : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z)
    (hpos : ∀ a, 0 ≤ (b : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) (h0 : b ≠ 0) : 1 ≤ phiC cj b := by
  rw [phiC_def]
  refine le_csInf (by rw [vals_eq_functionalValues]; exact functionalValues_nonempty h b) ?_
  rintro x ⟨l, h1, h2, rfl⟩
  obtain ⟨z, hz⟩ := h1 b hint
  have hp := h2 b hpos h0
  rw [hz] at hp ⊢
  have hz0 : (0 : ℤ) < z := by exact_mod_cast hp
  exact_mod_cast (show (1 : ℤ) ≤ z by omega)

end CM

end GlobalTheory.LeastExponentProbe

end
