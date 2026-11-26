module

public import Formalism.PadicSubsetSums.CentralIdempotents.WindowSums
public import Formalism.FrobeniusContraction.FrobeniusContractionProofs.ContractBij
public import Formalism.FrobeniusContraction.HighestWeightResidueAvoids
public import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LenBound
public import Formalism.EisensteinCokernelLengths.FactorialValuationBounds.LagrangeIdealSgProof
public import Formalism.GaloisIrreducibility.NoSolvableTransitive
public import Formalism.ResultantValuation.ResultantAdjugateProofs.Window
public import Formalism.ResultantValuation.ResultantAdjugateProofs.Laplace
public import Formalism.CyclotomicNorms.StatementI

@[expose] public section

section -- merged from Formalism.EisensteinCokernelLengths.FactorialValuationBounds.FactorialValuationBoundsProofFact
namespace Formalism.ZetaNonvanishing.ARCV

open Polynomial

theorem range_sdiff_range (H : ℕ) : Finset.range (2 * H) \ Finset.range H = Finset.Ico H (2 * H) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico]
  omega

end Formalism.ZetaNonvanishing.ARCV
end

section -- merged from Formalism.EisensteinCokernelLengths.FactorialValuationBounds.ToolsB
section -- merged from Formalism.EisensteinCokernelLengths.CokernelLengthBoundOfLifts
noncomputable section

open Classical

namespace Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts

open Formalism.WachCohomologyFacts Formalism.WachCohomologyFacts.V2

def LenBound2 : Prop :=
  ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (ℓ g g₀ e e' : ℕ)
    (Z Bc I : Submodule O M) (s s₀ : Finset M),
    s.card ≤ g → Submodule.span O (s : Set M) ⊔ Bc = Z → Bc ≤ I →
    s₀.card ≤ g₀ → (s₀ : Set M) ⊆ Z →
    (∀ p ∈ Z, (ℓ ^ e : ℕ) • p ∈ Submodule.span O (s₀ : Set M) ⊔ I) →
    (∀ p ∈ Submodule.span O (s₀ : Set M), (ℓ ^ e' : ℕ) • p ∈ I) →
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      ((g : ℕ∞) * (e : ℕ∞) + (g₀ : ℕ∞) * (e' : ℕ∞)) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})

end Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts
end
end

namespace Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts.FactorialValuationBoundsFacts
open Formalism.WachCohomologyFacts

theorem key {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (Z Z₀ I : Submodule O M)
    (hZ₀Z : Z₀ ≤ Z) :
    Module.length O (↥Z ⧸ I.comap Z.subtype) =
      Module.length O (↥Z₀ ⧸ I.comap Z₀.subtype) + Module.length O (↥Z ⧸ (Z₀ ⊔ I).comap Z.subtype) := by
  set I' := I.comap Z.subtype
  set J' := (Z₀ ⊔ I).comap Z.subtype
  set I₀ := I.comap Z₀.subtype
  have hIJ : I' ≤ J' := Submodule.comap_mono le_sup_right
  let f : ↥Z₀ →ₗ[O] ↥Z ⧸ I' := I'.mkQ ∘ₗ Submodule.inclusion hZ₀Z
  have hker : LinearMap.ker f = I₀ := by
    ext x
    simp only [f, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, I', I₀, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.coe_inclusion]
  let f' := I₀.liftQ f hker.ge
  let g := I'.mapQ J' LinearMap.id hIJ
  have hf' : Function.Injective f' := by
    rw [← LinearMap.ker_eq_bot]; exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  have hg : Function.Surjective g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H z => exact ⟨Submodule.Quotient.mk z, rfl⟩
  have hex : Function.Exact f' g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H z =>
      simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero, J',
        Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_sup]
      constructor
      · rintro ⟨a, ha, b, hb, hab⟩
        refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
        simp only [f', Submodule.liftQ_apply, f, LinearMap.coe_comp, Function.comp_apply,
          Submodule.mkQ_apply]
        rw [Submodule.Quotient.eq]
        simp only [I', Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
          Submodule.coe_inclusion]
        have : (a : M) - z = -b := by rw [← hab]; abel
        rw [this]; exact I.neg_mem hb
      · rintro ⟨w, hw⟩
        induction w using Submodule.Quotient.induction_on with
        | H a =>
          simp only [f', Submodule.liftQ_apply, f, LinearMap.coe_comp, Function.comp_apply,
            Submodule.mkQ_apply] at hw
          rw [Submodule.Quotient.eq] at hw
          simp only [I', Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
            Submodule.coe_inclusion] at hw
          refine ⟨a, a.2, (z : M) - a, ?_, by abel⟩
          have := I.neg_mem hw; simpa using this
  exact Module.length_eq_add_of_exact f' g hf' hg hex

theorem lenBound2 : Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts.LenBound2 := by
  intro O M _ _ _ ℓ g g₀ e e' Z Bc I s s₀ hs hZ hBc hs₀ hs₀Z hke hke'
  have hZ₀Z : Submodule.span O (s₀ : Set M) ≤ Z := Submodule.span_le.mpr hs₀Z
  have h1 := quotientLengthBound_holds O M ℓ g e Z Bc (Submodule.span O (s₀ : Set M) ⊔ I) s hs hZ
    (hBc.trans le_sup_right) hke
  have h2 := quotientLengthBound_holds O M ℓ g₀ e' (Submodule.span O (s₀ : Set M)) ⊥ I s₀ hs₀ (by simp)
    bot_le hke'
  rw [key Z _ I hZ₀Z]
  calc _ ≤ (g₀ : ℕ∞) * (e' : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) +
        (g : ℕ∞) * (e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := add_le_add h2 h1
    _ = _ := by ring

end Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts.FactorialValuationBoundsFacts
end

namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial

theorem colength_bound_two_layers : ColengthTwoStep := Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts.FactorialValuationBoundsFacts.lenBound2

theorem lagrange_resolvent_T : LagrangeT := by
  intro l _ D₁ D₂ ρ hd hρ
  have hass : ∀ a ∈ D₁, ∀ b ∈ D₁ ∪ D₂, a ≠ b →
      Associated (((a : ℤ) : ℤ_[l]) - ((b : ℤ) : ℤ_[l])) ((l : ℤ_[l]) ^ (0 + padicValInt l (a - b))) := by
    intro a _ b _ hab
    have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
    set v := padicValInt l (a - b) with hv
    obtain ⟨c, hc⟩ : (l : ℤ) ^ v ∣ a - b := padicValInt_dvd (a - b)
    have hcn : ¬ (l : ℤ) ∣ c := by
      intro ⟨c', hc'⟩
      have : (l : ℤ) ^ (v + 1) ∣ a - b := ⟨c', by rw [hc, hc']; ring⟩
      have h2 := (padicValInt_dvd_iff (p := l) _ (a - b)).mp this
      rcases h2 with h2 | h2
      · exact hne h2
      · omega
    have hu : IsUnit ((c : ℤ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_intCast_eq_one_iff]
      exact ((Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)).coprime_iff_not_dvd.mpr hcn).symm
    rw [zero_add, ← Int.cast_sub, hc]
    push_cast
    exact (associated_mul_unit_left _ _ hu)
  have h := Formalism.ZetaNonvanishing.LIFTV.lagrangeIdealSg_proof l ℤ_[l] 0 D₁ D₂ (fun a => ((a : ℤ) : ℤ_[l])) hd hass
  set E := D₁.sup fun a => (∑ b ∈ D₂, (0 + padicValInt l (a - b))) +
    ∑ a' ∈ D₁.erase a, (0 + padicValInt l (a - a')) with hE
  have hle : E ≤ ρ := by
    rw [hE]; apply Finset.sup_le; intro a ha
    simpa using hρ a ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [pow_add, mul_comm, C_mul]
  exact Ideal.mul_mem_left _ _ h

theorem filtered_product : FiltProd := by
  intro R V _ _ _ T F c k a
  induction a with
  | zero => intro _ x hx; simpa using hx
  | succ a ih =>
    intro h x hx
    have hy := ih (fun i h1 h2 => h i h1 (by omega)) x hx
    rw [← add_assoc, Finset.prod_Ico_succ_top (by omega), mul_comm, map_mul, Module.End.mul_apply]
    have := h (k + a) (by omega) (by omega) _ hy
    simpa [Module.algebraMap_end_apply] using this

theorem aeval_mapQ {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (T : Module.End R V)
    (W : Submodule R V) (hW : W ≤ W.comap T) (P : R[X]) (y : V) :
    aeval (W.mapQ W T hW : Module.End R (V ⧸ W)) P (W.mkQ y) = W.mkQ (aeval T P y) := by
  have hpow : ∀ (n : ℕ) (z : V),
      ((W.mapQ W T hW : Module.End R (V ⧸ W)) ^ n) (W.mkQ z) = W.mkQ ((T ^ n) z) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      have : (W.mapQ W T hW : Module.End R (V ⧸ W)) (W.mkQ z) = W.mkQ (T z) := rfl
      rw [this, ih]
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n r =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, hpow,
      map_smul]

end Formalism.IrreducibleCountingLemmas.WindowSums
