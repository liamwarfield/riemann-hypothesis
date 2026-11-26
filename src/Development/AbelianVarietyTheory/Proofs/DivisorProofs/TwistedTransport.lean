module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeFiniteProjectiveReflexive
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfLocallyRegular

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransport
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal
open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols (IsTwistedSum IsSymbol conjChar classOf)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt IsConjChar lamF upIdele)

namespace GlobalTheory.ToricTransport

def coordIn (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ) (Ω T : ℂ) : ℂ :=
  (C0 E d (2 * s) κ : ℂ) * T / Ω ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i)

def IsDatum {K E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] {I : Type} [Fintype I] (ι : K →+* ℂ)
    (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) : Prop :=
  UnramFin E ∧ IsCMType φ ∧ (∀ i, (φ i).comp (algebraMap K E) = ι) ∧ 1 ≤ s ∧ (∀ i, 1 ≤ κ i) ∧ IsBaseCond 𝔣 ∧ IsFinSetSplitPlacesCoprimeConductor 𝔣 Q ∧
    IsValChar φ s κ 𝔣 ∅ χ

def TwistedTransport : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ),
    Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∃ Ω₀ : ℂ, Ω₀ ≠ 0 ∧
      (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
        (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E), IsDatum ι φ s κ 𝔣 Q χ →
        ∀ (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) (T : ℂ), IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T → IsAlgebraic ℚ (coordIn E d s κ Ω₀ T)) ∧
      ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (j : Ω →+* ℂ) (art : Ideles K →* Gab K Ω),
        j.comp (algebraMap K Ω) = ι → IsGlobalArtin art →
        ∀ (g : ℂ ≃+* ℂ) (σ : Formalism.ConjugateSelfDual.G K Ω) (t : (Af K)ˣ), (∀ x, j (σ x) = g (j x)) → IsSymbol art t σ →
        ∃ Ω₁ : ℂ, Ω₁ ≠ 0 ∧
          ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
            (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E), IsDatum ι φ s κ 𝔣 Q χ →
            ∀ (κ' : I → ℕ) (χ' : HChar E), IsConjWt φ g κ κ' → IsConjChar φ s κ' g χ χ' →
            ∀ (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) (T T' : ℂ), IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T →
              IsTwistedSum φ s κ' (condQ 𝔣 Q) χ' (conjChar g ψ) T' →
              g (coordIn E d s κ Ω₀ T) =
                coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ *
                  (lamF s χ' (upIdele K E t) * ((conjChar g ψ (classOf K (condQ 𝔣 Q) t) : ℂˣ) : ℂ))⁻¹ * T')

theorem coordIn_div (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] {d s : ℕ} (hd : 0 < d) (hs : 1 ≤ s) (κ : I → ℕ)
    {Ω : ℂ} (hΩ : Ω ≠ 0) (T T₀ : ℂ) : coordIn E d s κ Ω T / coordIn E d s κ Ω T₀ = T / T₀ := by
  have hC : (C0 E d (2 * s) κ : ℂ) ≠ 0 := by exact_mod_cast (cmValueConst_pos E hd (by omega) κ).ne'
  rw [coordIn, coordIn, div_div_div_cancel_right₀ (pow_ne_zero _ hΩ), mul_div_mul_left _ _ hC]

end GlobalTheory.ToricTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDualPairSwapSymmetry
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDualPairSwapSymmetry
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockSwap

variable {p q r s : ℕ}

theorem linePos_swap (l : Ln p q r s) : linePos (l.swap : Ln r s p q) = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> rfl

theorem rename_lowB (l : Ln p q r s) (P : Pol p q r s) :
    rename Prod.swap (lowB l P) = lowB (l.swap : Ln r s p q) (rename Prod.swap P) := by
  unfold lowB
  rw [linePos_swap]
  split_ifs
  · exact (pderiv_rename Prod.swap_injective l P).symm
  · simp

theorem rename_raiB (l : Ln p q r s) (P : Pol p q r s) :
    rename Prod.swap (raiB l P) = raiB (l.swap : Ln r s p q) (rename Prod.swap P) := by
  unfold raiB
  rw [linePos_swap]
  split_ifs
  · simp
  · simp only [LinearMap.neg_apply, map_neg, neg_inj]
    exact (pderiv_rename Prod.swap_injective l P).symm

theorem rename_omE (l l' : Ln p q r s) (P : Pol p q r s) :
    rename Prod.swap (omE l l' P) =
      omE (l.swap : Ln r s p q) l'.swap (rename Prod.swap P) := by
  unfold omE
  simp only [LinearMap.add_apply, map_add (f := _), Module.End.mul_apply, rename_raiB, rename_lowB,
    Prod.swap_inj]
  congr 1
  split_ifs <;> simp

theorem rename_omAct (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P : Pol p q r s) :
    rename Prod.swap (omAct p q r s M P) =
      omAct r s p q (M.submatrix Prod.swap Prod.swap) (rename Prod.swap P) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [omAct_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    rename_omE]
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l => ?_
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l' => ?_
  simp

theorem rename_fockAct1 (Z : Mat p q) (P : Pol p q r s) :
    rename Prod.swap (fockAct1 p q r s Z P) = fockAct2 r s p q Z (rename Prod.swap P) := by
  simp only [fockAct1, fockAct2, LinearMap.comp_apply]
  rw [rename_omAct]
  congr 2
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.kroneckerMapBilinear_apply_apply, mul_comm]

theorem rename_fockAct2 (Z : Mat r s) (P : Pol p q r s) :
    rename Prod.swap (fockAct2 p q r s Z P) = fockAct1 r s p q Z (rename Prod.swap P) := by
  simp only [fockAct1, fockAct2, LinearMap.comp_apply]
  rw [rename_omAct]
  congr 2
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.kroneckerMapBilinear_apply_apply, mul_comm]

theorem rename_minusPart {σ τ : Type} (e : σ ≃ τ) (A : Module.End ℂ (MvPolynomial σ ℂ))
    (B : Module.End ℂ (MvPolynomial τ ℂ)) (h : ∀ P, rename e (A P) = B (rename e P))
    (P : MvPolynomial σ ℂ) : rename e (minusPart A P) = minusPart B (rename e P) := by
  unfold minusPart
  have := (renameEquiv ℂ e).toAddEquiv.map_finsum
    (fun d : ℕ => homogeneousComponent d (A (homogeneousComponent (d + 2) P)))
  refine this.trans (finsum_congr fun d => ?_)
  show rename e _ = _
  rw [rename_homogeneousComponent, h, rename_homogeneousComponent]

theorem minusPart_eq_zero_iff {σ τ : Type} (e : σ ≃ τ) (A : Module.End ℂ (MvPolynomial σ ℂ))
    (B : Module.End ℂ (MvPolynomial τ ℂ)) (h : ∀ P, rename e (A P) = B (rename e P))
    (P : MvPolynomial σ ℂ) : minusPart A P = 0 ↔ minusPart B (rename e P) = 0 := by
  rw [← rename_minusPart e A B h, map_eq_zero_iff _ (rename_injective _ e.injective)]

theorem swap_symmetry : ∀ (p q r s : ℕ), (∀ (Z : Mat p q) (P : Pol p q r s), rename Prod.swap (fockAct1 p q r s Z P) = fockAct2 r s p q Z (rename Prod.swap P)) ∧ (∀ (Z : Mat r s) (P : Pol p q r s), rename Prod.swap (fockAct2 p q r s Z P) = fockAct1 r s p q Z (rename Prod.swap P)) ∧ (∀ P : Pol p q r s, (P ∈ harm1 p q r s ↔ rename Prod.swap P ∈ harm2 r s p q) ∧ (P ∈ harm2 p q r s ↔ rename Prod.swap P ∈ harm1 r s p q)) := by
  intro p q r s
  refine ⟨rename_fockAct1, rename_fockAct2, fun P => ⟨?_, ?_⟩⟩
  · exact forall₂_congr fun Z _ =>
      minusPart_eq_zero_iff (Equiv.prodComm _ _) _ _ (rename_fockAct2 Z) P
  · exact forall₂_congr fun Z _ =>
      minusPart_eq_zero_iff (Equiv.prodComm _ _) _ _ (rename_fockAct1 Z) P

end GlobalTheory.FockSwap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDualPairSwapSymmetryStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_dualPair_swap_symmetry : ∀ (p q r s : ℕ), (∀ (Z : Mat p q) (P : Pol p q r s), rename Prod.swap (fockAct1 p q r s Z P) = fockAct2 r s p q Z (rename Prod.swap P)) ∧ (∀ (Z : Mat r s) (P : Pol p q r s), rename Prod.swap (fockAct2 p q r s Z P) = fockAct1 r s p q Z (rename Prod.swap P)) ∧ (∀ P : Pol p q r s, (P ∈ harm1 p q r s ↔ rename Prod.swap P ∈ harm2 r s p q) ∧ (P ∈ harm2 p q r s ↔ rename Prod.swap P ∈ harm1 r s p q)) := by
  first | exact @GlobalTheory.FockSwap.swap_symmetry | exact GlobalTheory.FockSwap.swap_symmetry | (intros; apply GlobalTheory.FockSwap.swap_symmetry <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMulFinrankCharacterSpaceOfFreePermutedSumman
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMulFinrankCharacterSpaceOfFreePermutedSumman
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem trace_rho_eq_zero_of_free {K Γ V X : Type} [Field K] [Group Γ] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ)
    [MulAction H X] (hfree : ∀ (h : H) (x : X), h • x = x → h = 1)
    (A : X → Submodule K V) (hA : DirectSum.IsInternal A)
    (hmap : ∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) (h : H) (hne : h ≠ 1) :
    LinearMap.trace K V (ρ h) = 0 := by
  classical
  refine LinearMap.trace_eq_zero_of_mapsTo_ne hA (fun x => h • x) (fun x hx => hne (hfree h x hx)) ?_
  intro x v hv
  exact hmap h x v hv

theorem card_mul_finrank_eig_of_free : ∀ (K Γ V X : Type) [Field K] [CharZero K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype X] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ) [MulAction H X], (∀ (h : H) (x : X), h • x = x → h = 1) → ∀ (A : X → Submodule K V), DirectSum.IsInternal A → (∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) → ∀ (Hb : Subgroup Γ), Hb ≤ H → ∀ lam : Hb →* Kˣ, Nat.card Hb * finrank K (eig ρ Hb lam) = finrank K V := by
  intro K Γ V X _ _ _ _ _ _ _ _ _ ρ H _ hfree A hA hmap Hb hle lam
  classical
  haveI : Fintype Hb := Fintype.ofFinite Hb
  set n : K := (Fintype.card Hb : K) with hn
  have hn0 : n ≠ 0 := by simp [hn, Fintype.card_ne_zero]
  let P : Module.End K V := n⁻¹ • ∑ h : Hb, (((lam h)⁻¹ : Kˣ) : K) • ρ h
  have hproj : LinearMap.IsProj (eig ρ Hb lam) P := by
    constructor
    · intro v
      rw [mem_eig]
      intro g
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [P, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
      rw [smul_comm]
      congr 1
      rw [Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => ?_)
      simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul, mul_inv, Units.val_mul]
      congr 1
      simp only [← Units.val_mul]
      congr 1
      group
    · intro v hv
      rw [mem_eig] at hv
      simp only [P, LinearMap.smul_apply, LinearMap.sum_apply, hv, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul K, smul_smul, ← hn, inv_mul_cancel₀ hn0, one_smul]
  have htr : LinearMap.trace K V P = n⁻¹ * (finrank K V : K) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, map_smul, map_sum, smul_eq_mul]
    congr 1
    rw [Finset.sum_eq_single 1]
    · simp [LinearMap.trace_one]
    · intro h _ hne
      have h0 : LinearMap.trace K V (ρ h) = 0 :=
        trace_rho_eq_zero_of_free ρ H hfree A hA hmap ⟨h, hle h.2⟩ (by
          intro e; apply hne; ext; simpa using congrArg Subtype.val e)
      rw [h0, mul_zero]
    · simp
  have h1 := hproj.trace
  rw [htr] at h1
  rw [Nat.card_eq_fintype_card]
  have : ((Fintype.card Hb * finrank K (eig ρ Hb lam) : ℕ) : K) = (finrank K V : K) := by
    push_cast
    rw [← h1, ← hn, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  exact_mod_cast this

end GlobalTheory.BadCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMulFinrankCharacterSpaceOfFreePermutedSummanStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_mul_finrank_characterSpace_of_free_permuted_summands : ∀ (K Γ V X : Type) [Field K] [CharZero K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype X] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ) [MulAction H X], (∀ (h : H) (x : X), h • x = x → h = 1) → ∀ (A : X → Submodule K V), DirectSum.IsInternal A → (∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) → ∀ (Hb : Subgroup Γ), Hb ≤ H → ∀ lam : Hb →* Kˣ, Nat.card Hb * finrank K (eig ρ Hb lam) = finrank K V := by
  first | exact @GlobalTheory.BadCount.card_mul_finrank_eig_of_free | exact GlobalTheory.BadCount.card_mul_finrank_eig_of_free | (intros; apply GlobalTheory.BadCount.card_mul_finrank_eig_of_free <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfFreePermute
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfFreePermute
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem embReg_of_free_permuted_summands : ∀ (K Γ V X : Type) [Field K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype X] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ) [MulAction H X], (∀ (h : H) (x : X), h • x = x → h = 1) → ∀ (A : X → Submodule K V), DirectSum.IsInternal A → (∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) → ∃ n : ℕ, EmbReg ρ H n ∧ n * Nat.card H = finrank K V := by
  intro K Γ V X _ _ _ _ _ _ _ _ ρ H _ hfree A hA hmap
  classical
  haveI : Fintype H := Fintype.ofFinite H
  have hinv : ∀ (g : Γ) (v : V), ρ g⁻¹ (ρ g v) = v := by
    intro g v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  let E := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA
  let comp : ∀ x : X, V →ₗ[K] A x := fun x =>
    (DirectSum.component K X (fun y => A y) x) ∘ₗ E.symm.toLinearMap
  have comp_apply : ∀ x v, comp x v = E.symm v x := fun x v => rfl

  have htr : ∀ (h : H) (x : X) (v : V), (comp (h • x) (ρ h v) : V) = ρ h (comp x v) := by
    intro h x v
    obtain ⟨w, rfl⟩ : ∃ w, v = E w := ⟨E.symm v, (E.apply_symm_apply v).symm⟩
    rw [comp_apply, comp_apply, E.symm_apply_apply]
    induction w using DirectSum.induction_on with
    | zero => simp
    | of y a =>
      have hE : E (DirectSum.of (fun y => A y) y a) = (a : V) := DirectSum.coeLinearMap_of A y a
      rw [hE]
      by_cases hxy : y = x
      · subst hxy
        rw [DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem hA (hmap h y a a.2), DirectSum.of_eq_same]
      · have hne : h • y ≠ h • x := fun he => hxy (smul_left_cancel h he)
        rw [DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem_ne hA hne (hmap h y a a.2),
          DirectSum.of_eq_of_ne (β := fun i => A i) y x a (Ne.symm hxy)]
        simp
    | add w₁ w₂ h₁ h₂ =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), DirectSum.add_apply, Submodule.coe_add, h₁, h₂,
        DirectSum.add_apply, Submodule.coe_add, map_add]
  have hzero : ∀ v : V, (∀ x, comp x v = 0) → v = 0 := by
    intro v hv
    have : E.symm v = 0 := DFinsupp.ext fun x => by rw [← comp_apply, hv]; rfl
    rw [← E.apply_symm_apply v, this, map_zero]

  let d : X → ℕ := fun x => finrank K (A x)
  have hdle : ∀ (h : H) (x : X), d x ≤ d (h • x) := by
    intro h x
    let φ : A x →ₗ[K] A (h • x) :=
      LinearMap.codRestrict (A (h • x)) ((ρ h).comp (A x).subtype) (fun a => hmap h x a a.2)
    refine LinearMap.finrank_le_finrank_of_injective (f := φ) fun a b hab => ?_
    have := congrArg (fun c : A (h • x) => ρ (h : Γ)⁻¹ (c : V)) hab
    have ha : ((φ a : A (h • x)) : V) = ρ h a := rfl
    have hb : ((φ b : A (h • x)) : V) = ρ h b := rfl
    simp only [ha, hb, hinv] at this
    exact Subtype.ext this
  have hdeq : ∀ (h : H) (x : X), d (h • x) = d x := by
    intro h x
    refine le_antisymm ?_ (hdle h x)
    have := hdle h⁻¹ (h • x)
    rwa [inv_smul_smul] at this

  let O := MulAction.orbitRel.Quotient H X
  haveI : Fintype O := Fintype.ofFinite O
  let β : H × O → X := fun p => p.1 • p.2.out
  have hβ : Function.Bijective β := by
    constructor
    · rintro ⟨h, o⟩ ⟨h', o'⟩ he
      simp only [β] at he
      have ho : o = o' := by
        have e1 : (Quotient.mk _ (h • o.out) : O) = o := by
          conv_rhs => rw [← Quotient.out_eq o]
          exact Quotient.sound (MulAction.mem_orbit _ h)
        have e2 : (Quotient.mk _ (h' • o'.out) : O) = o' := by
          conv_rhs => rw [← Quotient.out_eq o']
          exact Quotient.sound (MulAction.mem_orbit _ h')
        rw [← e1, ← e2, he]
      subst ho
      have : (h'⁻¹ * h) • o.out = o.out := by rw [mul_smul, he, inv_smul_smul]
      have := hfree _ _ this
      rw [inv_mul_eq_one] at this
      rw [this]
    · intro x
      let o : O := Quotient.mk _ x
      have hrel : o.out ∈ MulAction.orbit H x := by
        have := Quotient.exact (Quotient.out_eq o)
        exact this
      obtain ⟨g, hg⟩ := hrel
      exact ⟨(g⁻¹, o), by simp only [β, ← hg, inv_smul_smul]⟩

  let n : ℕ := ∑ o : O, d o.out
  have hdimV : finrank K V = ∑ x, d x := by
    rw [Module.finrank_eq_card_basis (hA.collectedBasis fun x => Module.finBasis K (A x)), Fintype.card_sigma]
    simp [d]
  have hcount : n * Nat.card H = finrank K V := by
    rw [hdimV, ← hβ.sum_comp d, Fintype.sum_prod_type_right]
    simp only [β, hdeq, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, n, Finset.sum_mul]
    exact Finset.sum_congr rfl fun o _ => by ring

  let I := Σ o : O, Fin (d o.out)
  have hcard : Fintype.card I = n := by simp [I, Fintype.card_sigma, n]
  let e : Fin n ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  let b : ∀ o : O, Basis (Fin (d o.out)) K (A o.out) := fun o => Module.finBasis K (A o.out)
  let fo : I → V →ₗ[K] K := fun p => (b p.1).coord p.2 ∘ₗ comp p.1.out
  let T : (V →ₗ[K] K) → V →ₗ[K] MonoidAlgebra K H := fun f =>
    ∑ h : H, (f ∘ₗ ρ (h : Γ)⁻¹).smulRight (MonoidAlgebra.single h (1 : K))
  have hT : ∀ f v, T f v = ∑ h : H, f (ρ (h : Γ)⁻¹ v) • MonoidAlgebra.single h (1 : K) := by
    intro f v; simp [T]
  have hTc : ∀ f v (h : H), (T f v).coeff h = f (ρ (h : Γ)⁻¹ v) := by
    intro f v h
    rw [hT, MonoidAlgebra.coeff_sum]
    simp [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  have hTeq : ∀ f (g : H) v, T f (ρ g v) = MonoidAlgebra.single g 1 * T f v := by
    intro f g v
    rw [hT, hT, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun h => ?_
    simp only [Equiv.coe_mulLeft]
    rw [mul_smul_comm, MonoidAlgebra.single_mul_single, one_mul, mul_inv_cancel_left]
    have hc : ρ (h : Γ)⁻¹ (ρ g v) = ρ ((g⁻¹ * h : H) : Γ)⁻¹ v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp [mul_assoc]
    rw [hc]
  let j : V →ₗ[K] (Fin n → MonoidAlgebra K H) := LinearMap.pi fun k => T (fo (e k))
  refine ⟨n, ⟨j, ?_, ?_⟩, hcount⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply hzero
    intro x
    obtain ⟨⟨h, o⟩, rfl⟩ := hβ.2 x
    have h1 : comp o.out (ρ (h : Γ)⁻¹ v) = 0 := by
      rw [← (b o).forall_coord_eq_zero_iff]
      intro i
      have hk : e (e.symm ⟨o, i⟩) = ⟨o, i⟩ := e.apply_symm_apply _
      have h5 : T (fo (e (e.symm ⟨o, i⟩))) v = 0 := congrFun hv (e.symm ⟨o, i⟩)
      rw [hk] at h5
      have h6 := congrArg (fun a => MonoidAlgebra.coeff a h) h5
      simp only [hTc] at h6
      simpa [fo] using h6
    have h2 := htr h⁻¹ (h • o.out) v
    rw [inv_smul_smul] at h2
    simp only [Subgroup.coe_inv] at h2
    rw [h1, Submodule.coe_zero] at h2
    have h3 := congrArg (ρ (h : Γ)) h2
    have h4 := hinv ((h : Γ)⁻¹) (comp (h • o.out) v : V)
    rw [inv_inv] at h4
    rw [map_zero, h4] at h3
    exact Subtype.ext h3.symm
  · intro h v i
    simp only [j, LinearMap.pi_apply]
    exact hTeq _ h v

end GlobalTheory.BadCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfFreePermuteStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedsInRegularRepresentationCopies_of_free_permuted_summands : ∀ (K Γ V X : Type) [Field K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype X] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ) [MulAction H X], (∀ (h : H) (x : X), h • x = x → h = 1) → ∀ (A : X → Submodule K V), DirectSum.IsInternal A → (∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) → ∃ n : ℕ, EmbReg ρ H n ∧ n * Nat.card H = finrank K V := by
  first | exact @GlobalTheory.BadCount.embReg_of_free_permuted_summands | exact GlobalTheory.BadCount.embReg_of_free_permuted_summands | (intros; apply GlobalTheory.BadCount.embReg_of_free_permuted_summands <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActDualPairCommutingLieActions
open Formalism.BasicNotions.TH
open scoped Kronecker

namespace GlobalTheory.FockPair

theorem fockAct1_eq_kron (p q r s : ℕ) (Y : Mat p q) :
    fockAct1 p q r s Y = omAct p q r s (Y ⊗ₖ (1 : Mat r s)) := rfl

theorem fockAct2_eq_kron (p q r s : ℕ) (Z : Mat r s) :
    fockAct2 p q r s Z = omAct p q r s ((1 : Mat p q) ⊗ₖ Z) := rfl

theorem pair_lie_commute : ∀ (p q r s : ℕ), IsLieAct (fockAct1 p q r s) ∧
    IsLieAct (fockAct2 p q r s) ∧ ∀ (Y : Mat p q) (Z : Mat r s),
      fockAct1 p q r s Y * fockAct2 p q r s Z = fockAct2 p q r s Z * fockAct1 p q r s Y := by
  intro p q r s
  refine ⟨fun X Y => ?_, fun X Y => ?_, fun Y Z => ?_⟩
  · rw [map_sub]
    simp only [fockAct1_eq_kron]
    rw [← GlobalTheory.T.fockQuadraticAction_map_lie_bracket, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      map_sub]
  · rw [map_sub]
    simp only [fockAct2_eq_kron]
    rw [← GlobalTheory.T.fockQuadraticAction_map_lie_bracket, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      map_sub]
  · rw [← sub_eq_zero, fockAct1_eq_kron, fockAct2_eq_kron, ← GlobalTheory.T.fockQuadraticAction_map_lie_bracket,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp

end GlobalTheory.FockPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesComplexEmbedd
open Module NumberField

namespace GlobalTheory.BadCount

theorem semilin_eq_sum {K V : Type} [Field K] [AddCommGroup V] [Module ℂ V] {N : ℕ} {σ : K →+* ℂ}
    (f : (Fin N → K) →ₛₗ[σ] V) (x : Fin N → K) : f x = ∑ k, σ (x k) • f (Pi.single k 1) := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ]

theorem top_le_span_single {K V : Type} [Field K] [AddCommGroup V] [Module ℂ V] {N : ℕ} {σ : K →+* ℂ}
    (f : (Fin N → K) →ₛₗ[σ] V) (h : Submodule.span ℂ (Set.range f) = ⊤) :
    ⊤ ≤ Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) := by
  rw [← h, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [semilin_eq_sum f x]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem embReg_of_semilinear {V V' G : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [Group G] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (τ : ℂ ≃+* ℂ) (T : V' →+ V)
    (hs : ∀ (c : ℂ) v, T (c • v) = τ.symm c • T v) (hi : Function.Injective T)
    (he : ∀ g v, T (ρ' g v) = ρ g (T v)) (H : Subgroup G) (n : ℕ) (h : EmbReg ρ H n) : EmbReg ρ' H n := by
  obtain ⟨j, hj, hje⟩ := h
  let m : MonoidAlgebra ℂ H →+* MonoidAlgebra ℂ H := MonoidAlgebra.mapRingHom H (τ : ℂ →+* ℂ)
  have hm : ∀ x a, (m x).coeff a = τ (x.coeff a) := fun x a => MonoidAlgebra.coeff_mapRingHom _ _ _
  have hmi : Function.Injective m := by
    intro x y hxy
    ext a
    apply τ.injective
    rw [← hm, ← hm, hxy]
  refine ⟨{ toFun := fun v i => m (j (T v) i)
            map_add' := fun v w => ?_
            map_smul' := fun c v => ?_ }, fun v w hvw => ?_, fun g v i => ?_⟩
  · funext i
    simp
  · funext i
    ext a
    simp [hs, hm]
  · exact hi (hj (funext fun i => hmi (congrFun hvw i)))
  · show m (j (T (ρ' g v)) i) = _ * m (j (T v) i)
    rw [he, hje, map_mul]
    congr 1
    exact (MonoidAlgebra.mapRingHom_single _ _ _).trans (by rw [map_one])

theorem embReg_of_baseChange : ∀ (K V V' G : Type) [Field K] [NumberField K] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [Group G] [Finite G] (N : ℕ) (ρK : Representation K G (Fin N → K))
    (σ σ' : K →+* ℂ) (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (f : (Fin N → K) →ₛₗ[σ] V)
    (f' : (Fin N → K) →ₛₗ[σ'] V'), (LinearIndependent ℂ fun k => f (Pi.single k 1)) →
    Submodule.span ℂ (Set.range f) = ⊤ → (LinearIndependent ℂ fun k => f' (Pi.single k 1)) →
    Submodule.span ℂ (Set.range f') = ⊤ → (∀ g v, ρ g (f v) = f (ρK g v)) →
    (∀ g v, ρ' g (f' v) = f' (ρK g v)) → ∀ (H : Subgroup G) (n : ℕ),
    GlobalTheory.BadCount.EmbReg ρ H n → GlobalTheory.BadCount.EmbReg ρ' H n := by
  intro K V V' G _ _ _ _ _ _ _ _ N ρK σ σ' ρ ρ' f f' hl _ hl' hsp' he he' H n h
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq K σ σ'
  let b' : Basis (Fin N) ℂ V' := Basis.mk hl' (top_le_span_single f' hsp')
  have hb' : ∀ k, b' k = f' (Pi.single k 1) := fun k => Basis.mk_apply _ _ k
  let T : V' →+ V :=
    { toFun := fun v => ∑ k, τ.symm (b'.repr v k) • f (Pi.single k 1)
      map_zero' := by simp
      map_add' := fun v w => by simp [add_smul, Finset.sum_add_distrib] }
  have hT : ∀ v, T v = ∑ k, τ.symm (b'.repr v k) • f (Pi.single k 1) := fun _ => rfl
  have hs : ∀ (c : ℂ) v, T (c • v) = τ.symm c • T v := fun c v => by
    simp [hT, Finset.smul_sum, mul_smul]
  have hTf : ∀ x, T (f' x) = f x := fun x => by
    have hr : ∀ k, b'.repr (f' x) k = σ' (x k) := fun k => by
      rw [semilin_eq_sum f' x]
      simp only [← hb']
      exact congrFun (b'.repr_sum_self _) k
    rw [hT, semilin_eq_sum f x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hr, ← hτ, RingEquiv.symm_apply_apply]
  refine embReg_of_semilinear ρ ρ' τ T hs ?_ (fun g v => ?_) H n h
  · rw [injective_iff_map_eq_zero]
    intro v hv
    rw [hT] at hv
    have h0 := Fintype.linearIndependent_iff.1 hl _ hv
    apply b'.repr.injective
    ext k
    simpa using h0 k
  · have hv : v ∈ Submodule.span ℂ (Set.range f') := hsp' ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      rw [he', hTf, hTf, he]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
    | smul c x _ hx => rw [map_smul, hs, hs, map_smul, hx]

end GlobalTheory.BadCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirFockAct1SubCasimirFockAct2
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirFockAct1SubCasimirFockAct2
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockCasimir

theorem sum_mul_normal_order {A ι κ : Type} [Ring A] [Algebra ℂ A] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (x d : ι → κ → A)
    (h : ∀ b c e, d b c * x b e = x b e * d b c + if c = e then 1 else 0) :
    ∑ a, ∑ b, (∑ c, (x a c * d b c + if a = b then (1 / 2 : ℂ) • (1 : A) else 0)) *
        (∑ e, (x b e * d a e + if b = a then (1 / 2 : ℂ) • (1 : A) else 0)) =
      (∑ a, ∑ b, ∑ c, ∑ e, x a c * x b e * (d b c * d a e)) +
        ((Fintype.card ι : ℂ) + (Fintype.card κ : ℂ)) • (∑ a, ∑ c, x a c * d a c) +
        ((Fintype.card ι : ℂ) * (Fintype.card κ : ℂ) ^ 2 / 4) • (1 : A) := by
  have h0 : ∀ a b, (∑ c, x a c * d b c) * (∑ e, x b e * d a e) =
      (∑ c, ∑ e, x a c * x b e * (d b c * d a e)) + ∑ c, x a c * d a c := by
    intro a b
    rw [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 : ∀ e, x a c * d b c * (x b e * d a e) =
        x a c * x b e * (d b c * d a e) + if c = e then x a c * d a e else 0 := by
      intro e
      have : x a c * d b c * (x b e * d a e) = x a c * (d b c * x b e) * d a e := by
        simp only [mul_assoc]
      rw [this, h, mul_add, add_mul]
      split_ifs <;> simp [mul_assoc]
    simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h2 : ∀ a b, (∑ c, (x a c * d b c + if a = b then (1 / 2 : ℂ) • (1 : A) else 0)) *
        (∑ e, (x b e * d a e + if b = a then (1 / 2 : ℂ) • (1 : A) else 0)) =
      ((∑ c, ∑ e, x a c * x b e * (d b c * d a e)) + ∑ c, x a c * d a c) +
        if a = b then (Fintype.card κ : ℂ) • (∑ c, x a c * d a c) +
          ((Fintype.card κ : ℂ) ^ 2 / 4) • (1 : A) else 0 := by
    intro a b
    rw [← h0]
    by_cases hab : a = b
    · subst hab
      simp only [if_true, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul ℂ, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    · simp [hab, Ne.symm hab]
  simp only [h2]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, ← Finset.smul_sum]
  module

variable {p q r s : ℕ}

theorem pderiv_pderiv_comm {σ : Type} (l m : σ) (P : MvPolynomial σ ℂ) :
    pderiv l (pderiv m P) = pderiv m (pderiv l P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P n hP =>
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add (f := _), hP, Pi.single_apply]
    split_ifs <;> simp <;> ring

theorem lowB_comm (l m : Ln p q r s) : lowB l * lowB m = lowB m * lowB l := by
  by_cases hlm : l = m
  · rw [hlm]
  refine LinearMap.ext fun P => ?_
  cases hl : linePos l <;> cases hm : linePos m <;>
    simp [lowB, hl, hm, pderiv_X, Pi.single_apply, hlm, Ne.symm hlm, pderiv_pderiv_comm l m,
      mul_left_comm]

theorem lowB_mul_raiB (l m : Ln p q r s) :
    lowB l * raiB m = raiB m * lowB l + if l = m then 1 else 0 := by
  refine LinearMap.ext fun P => ?_
  by_cases hlm : l = m
  · subst hlm
    cases hl : linePos l <;> simp [lowB, raiB, hl, add_comm]
  · cases hl : linePos l <;> cases hm : linePos m <;>
      simp [lowB, raiB, hl, hm, pderiv_X, Pi.single_apply, hlm, Ne.symm hlm, pderiv_pderiv_comm l m,
        mul_left_comm]

theorem casimir_fockAct1_sub_casimir_fockAct2 : ∀ (p q r s : ℕ),
    casimir (fockAct1 p q r s) - casimir (fockAct2 p q r s) =
      ((((p + q : ℕ) : ℂ) * ((r + s : ℕ) : ℂ) * (((r + s : ℕ) : ℂ) - ((p + q : ℕ) : ℂ))) / 4) •
        (1 : Module.End ℂ (Pol p q r s)) := by
  intro p q r s
  have h1 := sum_mul_normal_order (fun (a : Ix p q) (c : Ix r s) => raiB (a, c))
    (fun (a : Ix p q) (c : Ix r s) => lowB (a, c)) (fun b c e => by simp [lowB_mul_raiB])
  have h2 := sum_mul_normal_order (fun (c : Ix r s) (a : Ix p q) => raiB (a, c))
    (fun (c : Ix r s) (a : Ix p q) => lowB (a, c)) (fun b c e => by simp [lowB_mul_raiB])
  have hQ : (∑ c : Ix r s, ∑ e : Ix r s, ∑ a : Ix p q, ∑ b : Ix p q,
        raiB (a, c) * raiB (b, e) * (lowB (a, e) * lowB (b, c))) =
      ∑ a : Ix p q, ∑ b : Ix p q, ∑ c : Ix r s, ∑ e : Ix r s,
        raiB (a, c) * raiB (b, e) * (lowB (b, c) * lowB (a, e)) := by
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type' (α₁ := Ix p q) (α₂ := Ix p q)]
    simp only [← Fintype.sum_prod_type' (α₁ := Ix p q) (α₂ := Ix p q),
      ← Fintype.sum_prod_type' (α₁ := Ix r s) (α₂ := Ix r s)]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [lowB_comm]
  have hE : (∑ c : Ix r s, ∑ a : Ix p q, raiB (a, c) * lowB (a, c)) =
      ∑ a : Ix p q, ∑ c : Ix r s, raiB (a, c) * lowB (a, c) := Finset.sum_comm
  rw [hQ, hE] at h2
  simp only [Formalism.BasicNotions.TH.casimir, fockAct1_Eab, fockAct2_Eab, Formalism.BasicNotions.TH.omE, Prod.mk.injEq, and_true, true_and]
  rw [h1, h2]
  simp only [Fintype.card_sum, Fintype.card_fin]
  module

end GlobalTheory.FockCasimir
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirFockAct1SubCasimirFockAct2Statement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_fockAct1_sub_casimir_fockAct2_eq_smul_one : ∀ (p q r s : ℕ), casimir (fockAct1 p q r s) - casimir (fockAct2 p q r s) = ((((p + q : ℕ) : ℂ) * ((r + s : ℕ) : ℂ) * (((r + s : ℕ) : ℂ) - ((p + q : ℕ) : ℂ))) / 4) • (1 : Module.End ℂ (Pol p q r s)) := by
  first | exact @GlobalTheory.FockCasimir.casimir_fockAct1_sub_casimir_fockAct2 | exact GlobalTheory.FockCasimir.casimir_fockAct1_sub_casimir_fockAct2 | (intros; apply GlobalTheory.FockCasimir.casimir_fockAct1_sub_casimir_fockAct2 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltIsDomainValuationRing
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.TiltValuation

theorem tilt_isDomain_valuationRing : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∃ _ : IsDomain (PreTilt O p), ValuationRing (PreTilt O p) := by
  intro p _ C _ _ _ v O _ _ _ _ hv
  haveI hdom : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  haveI : IsDomain O := hv.hom_inj.isDomain _
  haveI : ValuationRing O := ValuationRing.iff_dvd_total.2 ⟨fun a b => by
    rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
    · exact Or.inr (hv.dvd_of_le h)
    · exact Or.inl (hv.dvd_of_le h)⟩
  exact ⟨hdom, ValuationRing.iff_dvd_total.2 ⟨fun a b => GlobalTheory.FrobInt.dvd_total_tilt a b⟩⟩

end GlobalTheory.TiltValuation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointShapeUniqueAndDegWEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointShapeUniqueAndDegWEq
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.JointShapeUniq

theorem length_pad {x y : List ℤ} {n : ℕ} (h : x.length + y.length ≤ n) :
    (pad x (n - x.length - y.length) y).length = n := by
  simp [pad]; omega

theorem ofFn_getD {L : List ℚ} {n : ℕ} (h : L.length = n) :
    List.ofFn (fun i : Fin n => L.getD i 0) = L := by
  subst h
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [List.getElem?_eq_getElem h2]

theorem filter_pos {x y : List ℤ} (hx : ∀ v ∈ x, 0 < v) (hy : ∀ v ∈ y, v < 0) (k : ℕ) :
    (x ++ List.replicate k 0 ++ y).filter (fun v => decide (0 < v)) = x := by
  rw [List.filter_append, List.filter_append, List.filter_eq_self.2 (by simpa using hx),
    List.filter_eq_nil_iff.2 (by simp),
    List.filter_eq_nil_iff.2 (fun v hv => by have := hy v hv; simp; omega)]
  simp

theorem filter_neg {x y : List ℤ} (hx : ∀ v ∈ x, 0 < v) (hy : ∀ v ∈ y, v < 0) (k : ℕ) :
    (x ++ List.replicate k 0 ++ y).filter (fun v => decide (v < 0)) = y := by
  rw [List.filter_append, List.filter_append,
    List.filter_eq_nil_iff.2 (fun v hv => by have := hx v hv; simp; omega),
    List.filter_eq_nil_iff.2 (by simp), List.filter_eq_self.2 (by simpa using hy)]
  simp

theorem pad_inj {x y x' y' : List ℤ} (hx : ∀ v ∈ x, 0 < v) (hy : ∀ v ∈ y, v < 0)
    (hx' : ∀ v ∈ x', 0 < v) (hy' : ∀ v ∈ y', v < 0) {n : ℕ}
    (h : x.length + y.length ≤ n) (h' : x'.length + y'.length ≤ n)
    (e : ∀ i : Fin n, (pad x (n - x.length - y.length) y).getD i 0 =
      (pad x' (n - x'.length - y'.length) y').getD i 0) : x = x' ∧ y = y' := by
  have e1 : pad x (n - x.length - y.length) y = pad x' (n - x'.length - y'.length) y' := by
    rw [← ofFn_getD (length_pad h), ← ofFn_getD (length_pad h'), funext e]
  have e2 := List.map_injective_iff.2 (Int.cast_injective (α := ℚ)) e1
  exact ⟨by rw [← filter_pos hx hy, e2, filter_pos hx' hy'],
    by rw [← filter_neg hx hy, e2, filter_neg hx' hy']⟩

def absSum (x : List ℤ) : ℚ := (x.map fun v : ℤ => |(v : ℚ)|).sum

theorem sum_abs_pad {x y : List ℤ} {n : ℕ} (h : x.length + y.length ≤ n) :
    ∑ i : Fin n, |(pad x (n - x.length - y.length) y).getD i 0| = absSum x + absSum y := by
  have : ∑ i : Fin n, |(pad x (n - x.length - y.length) y).getD i 0| =
      ((pad x (n - x.length - y.length) y).map fun v => |v|).sum := by
    conv_rhs => rw [← ofFn_getD (length_pad h), List.map_ofFn, List.sum_ofFn]
    rfl
  rw [this]
  simp [pad, absSum, Function.comp_def]

theorem shiftNu_injective {p q : ℕ} (c : ℚ) :
    Function.Injective (shiftNu (p := p) (q := q) c) := by
  intro μ μ₁ h
  funext a
  have := congrFun h a
  rcases a with a | a <;> simpa [shiftNu] using this

theorem jointShape_unique_deg : ∀ (p q r s : ℕ) (μ μ₁ : Ix p q → ℚ) (μ' μ₁' : Ix r s → ℚ),
    JointShape p q r s μ μ' → JointShape p q r s μ₁ μ₁' →
      (μ = μ₁ ↔ μ' = μ₁') ∧ degW (cPair r s) μ = degW (cPair p q) μ' := by
  intro p q r s μ μ₁ μ' μ₁' h h₁
  obtain ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, l1, l2, l3, l4, e1, e2⟩ := h
  obtain ⟨a', b', c', d', ha', hc', hb', hd', -, -, -, -, l1', l2', l3', l4', e1', e2'⟩ := h₁
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · subst h
    have e := e1.symm.trans e1'
    obtain ⟨rfl, rfl⟩ := pad_inj ha hb ha' hb' l1 l1' fun i => congrFun e (.inl i)
    obtain ⟨rfl, rfl⟩ := pad_inj hc hd hc' hd' l2 l2' fun i => congrFun e (.inr i)
    exact shiftNu_injective _ (e2.trans e2'.symm)
  · subst h
    have e := e2.symm.trans e2'
    obtain ⟨rfl, rfl⟩ := pad_inj ha hd ha' hd' l3 l3' fun i => congrFun e (.inl i)
    obtain ⟨rfl, rfl⟩ := pad_inj hc hb hc' hb' l4 l4' fun i => congrFun e (.inr i)
    exact shiftNu_injective _ (e1.trans e1'.symm)
  · simp only [degW, e1, e2, Fintype.sum_sum_type, ofBlocks]
    rw [sum_abs_pad l1, sum_abs_pad l2, sum_abs_pad l3, sum_abs_pad l4]
    ring

end GlobalTheory.JointShapeUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointShapeUniqueAndDegWEqStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointShape_unique_and_degW_eq : ∀ (p q r s : ℕ) (μ μ₁ : Ix p q → ℚ) (μ' μ₁' : Ix r s → ℚ), JointShape p q r s μ μ' → JointShape p q r s μ₁ μ₁' → (μ = μ₁ ↔ μ' = μ₁') ∧ degW (cPair r s) μ = degW (cPair p q) μ' := by
  first | exact @GlobalTheory.JointShapeUniq.jointShape_unique_deg | exact GlobalTheory.JointShapeUniq.jointShape_unique_deg | (intros; apply GlobalTheory.JointShapeUniq.jointShape_unique_deg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeMulLeftIdempotentGroupAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeMulLeftIdempotentGroupAlgebra
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem finrank_range_mulLeft_idem : ∀ (K H : Type) [Field K] [CharZero K] [Group H] [Finite H] (a : MonoidAlgebra K H), a * a = a → ((finrank K (LinearMap.range (LinearMap.mulLeft K a)) : ℕ) : K) = (Nat.card H : K) * a.coeff 1 := by
  intro K H _ _ _ _ a ha
  classical
  haveI : Fintype H := Fintype.ofFinite H
  have hi : IsIdempotentElem (LinearMap.mulLeft K a) := by
    change LinearMap.mulLeft K a * LinearMap.mulLeft K a = LinearMap.mulLeft K a
    refine LinearMap.ext fun x => ?_
    change a * (a * x) = a * x
    rw [← mul_assoc, ha]
  rw [← (LinearMap.IsIdempotentElem.isProj_range _ hi).trace]
  rw [LinearMap.trace_eq_matrix_trace K (MonoidAlgebra.basis H K), Matrix.trace]
  have h : ∀ g : H, Matrix.diag (LinearMap.toMatrix (MonoidAlgebra.basis H K)
      (MonoidAlgebra.basis H K) (LinearMap.mulLeft K a)) g = a.coeff 1 := by
    intro g
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply,
      LinearMap.mulLeft_apply]
    change (a * MonoidAlgebra.single g 1).coeff g = a.coeff 1
    rw [MonoidAlgebra.coeff_mul_single_apply, mul_inv_cancel, mul_one]
  rw [Finset.sum_congr rfl (fun g _ => h g), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]

end GlobalTheory.BadCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeMulLeftIdempotentGroupAlgebraStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_range_mulLeft_idempotent_groupAlgebra : ∀ (K H : Type) [Field K] [CharZero K] [Group H] [Finite H] (a : MonoidAlgebra K H), a * a = a → ((finrank K (LinearMap.range (LinearMap.mulLeft K a)) : ℕ) : K) = (Nat.card H : K) * a.coeff 1 := by
  first | exact @GlobalTheory.BadCount.finrank_range_mulLeft_idem | exact GlobalTheory.BadCount.finrank_range_mulLeft_idem | (intros; apply GlobalTheory.BadCount.finrank_range_mulLeft_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfMixedOverlaps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfMixedOverlaps
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)

noncomputable section
namespace GlobalTheory.KS

theorem isCob_of_mixed : ∀ (X : Scheme.{0}) (J K : Type) (V : J → X.Opens) (U : K → X.Opens), ⨆ k, U k = ⊤ → ∀ (z : C1 V) (z' : C1 U) (b : ∀ i k, Γ(X, V i ⊓ U k)), (∀ i i' k, rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (b i k) (V i ⊓ V i' ⊓ U k) - rsT (b i' k) (V i ⊓ V i' ⊓ U k)) → (∀ i k k', rsT (z' k k') (V i ⊓ U k ⊓ U k') = rsT (b i k') (V i ⊓ U k ⊓ U k') - rsT (b i k) (V i ⊓ U k ⊓ U k')) → IsCob U z' → IsCob V z := by
  intro X J K V U hU z z' b h1 h2 hz'
  obtain ⟨y', hy'⟩ := hz'
  have cov : ∀ O : X.Opens, O ≤ ⨆ k, O ⊓ U k := fun O x hx => by
    have : x ∈ ⨆ k, U k := by rw [hU]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩
  have glue : ∀ i, ∃ t : Γ(X, V i), ∀ k, rsT t (V i ⊓ U k) = rsT (y' k) (V i ⊓ U k) - b i k := by
    intro i
    refine exists_rsT_eq (fun k => V i ⊓ U k) (fun k => inf_le_left) (cov _) _ fun k l => ?_
    have e : (V i ⊓ U k) ⊓ (V i ⊓ U l) ≤ V i ⊓ U k ⊓ U l := fun x hx => ⟨⟨hx.1.1, hx.1.2⟩, hx.2.2⟩
    have e₁ : V i ⊓ U k ⊓ U l ≤ V i ⊓ U k := inf_le_left
    have e₂ : V i ⊓ U k ⊓ U l ≤ V i ⊓ U l := fun x hx => ⟨hx.1.1, hx.2⟩
    have e₃ : V i ⊓ U k ⊓ U l ≤ U k ⊓ U l := fun x hx => ⟨hx.1.2, hx.2⟩
    rw [← rsT_rsT e₁ e, ← rsT_rsT e₂ e]
    congr 1
    have k₀ := congrArg (fun s => rsT s (V i ⊓ U k ⊓ U l)) (hy' k l)
    simp only [rsT_sub] at k₀
    rw [h2, rsT_rsT inf_le_right e₃, rsT_rsT inf_le_left e₃] at k₀
    simp only [rsT_sub]
    rw [rsT_rsT inf_le_right e₁, rsT_rsT inf_le_right e₂]
    linear_combination k₀
  choose y hy using glue
  refine ⟨y, fun i i' => ?_⟩
  refine eq_of_rsT_eq (fun k => V i ⊓ V i' ⊓ U k) (fun k => inf_le_left) (cov _) _ _ fun k => ?_
  have e₁ : V i ⊓ V i' ⊓ U k ≤ V i ⊓ U k := fun x hx => ⟨hx.1.1, hx.2⟩
  have e₂ : V i ⊓ V i' ⊓ U k ≤ V i' ⊓ U k := fun x hx => ⟨hx.1.2, hx.2⟩
  show rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (rsT (y i') (V i ⊓ V i') - rsT (y i) (V i ⊓ V i')) (V i ⊓ V i' ⊓ U k)
  rw [h1, rsT_sub, rsT_rsT inf_le_right inf_le_left, rsT_rsT inf_le_left inf_le_left,
    ← rsT_rsT inf_le_left e₂ (y i'), ← rsT_rsT inf_le_left e₁ (y i), hy, hy]
  simp only [rsT_sub]
  rw [rsT_rsT inf_le_right e₁, rsT_rsT inf_le_right e₂]
  ring

end GlobalTheory.KS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfMixedOverlapsStatement
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCechOneCoboundary_of_mixed_overlaps : ∀ (X : Scheme.{0}) (J K : Type) (V : J → X.Opens) (U : K → X.Opens), ⨆ k, U k = ⊤ → ∀ (z : C1 V) (z' : C1 U) (b : ∀ i k, Γ(X, V i ⊓ U k)), (∀ i i' k, rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (b i k) (V i ⊓ V i' ⊓ U k) - rsT (b i' k) (V i ⊓ V i' ⊓ U k)) → (∀ i k k', rsT (z' k k') (V i ⊓ U k ⊓ U k') = rsT (b i k') (V i ⊓ U k ⊓ U k') - rsT (b i k) (V i ⊓ U k ⊓ U k')) → IsCob U z' → IsCob V z := by
  first | exact @GlobalTheory.KS.isCob_of_mixed | exact GlobalTheory.KS.isCob_of_mixed | (intros; apply GlobalTheory.KS.isCob_of_mixed <;> assumption)
end
end
