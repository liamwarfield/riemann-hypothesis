module

public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.WeylFormNondegenerateGlobal
public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Formalism.SharpRestriction.GrowthBounds.ObjPol

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FormSK
section -- merged from Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FormSK
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

def nabO (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (ν : Fin (m + 1) → ℕ) :
    Submodule O (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :=
  Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap (dualWeyl O (m + 1) (m + 1) ν)

def expN (p m : ℕ) (lam : Fin (m + 1) → ℤ) : ℕ :=
  if ellWt lam = 0 then 0 else N0 (m + 1) * deF p (m + 1) (ellWt lam)

def FormCoreSK : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
    ∃ B : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] Kf,
      (∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf),
        B (rowAct Kf g P) Q = B P (rowAct Kf g.transpose Q)) ∧
      (∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam),
        (∀ P ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam), B P Q = 0) → Q = 0) ∧
      (∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam),
        (∀ P ∈ nabO O Kf m (nuOf lam), B P Q ∈ Set.range (algebraMap O Kf)) → Q ∈ nabO O Kf m (nuOf lam)) ∧
      (∀ Q ∈ nabO O Kf m (nuOf lam), ∀ P ∈ nabO O Kf m (nuOf lam),
        B P (((p : Kf) ^ expN p m lam) • Q) ∈ Set.range (algebraMap O Kf))

end Formalism.L2.G.Model.TS
end
end

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.InvariantFactorPaths.INST

theorem charZero_of_irreducible_natCast {W : Type*} [CommRing W] [IsDomain W] {p : ℕ} (hp : p.Prime)
    (h : Irreducible (p : W)) : CharZero W := by
  rcases CharP.char_is_prime_or_zero W (ringChar W) with hq | hq
  · exfalso
    haveI : CharP W (ringChar W) := ringChar.charP W
    haveI : Fact (ringChar W).Prime := ⟨hq⟩
    by_cases hpq : p = ringChar W
    · exact h.ne_zero (by rw [hpq]; exact CharP.cast_eq_zero W _)
    · apply h.not_isUnit
      have hu : IsUnit (p : ZMod (ringChar W)) := by
        rw [ZMod.isUnit_iff_coprime]
        exact (Nat.coprime_primes hp hq).mpr hpq
      have hu' := hu.map (ZMod.castHom (dvd_refl _) W)
      simpa using hu'
  · haveI : CharP W 0 := by
      rw [← hq]
      exact ringChar.charP W
    exact CharP.charP_to_charZero W

theorem nuOf_antitone {m : ℕ} {lam : Fin (m + 1) → ℤ} (hl : Antitone lam) : Antitone (nuOf lam) := by
  intro a b hab
  exact Int.toNat_le_toNat (sub_le_sub_right (hl hab) _)

theorem lastIdx_succ (m : ℕ) : lastIdx (m + 1) = Fin.last m := by
  ext
  simp [lastIdx]

theorem nuOf_le_ellWt {m : ℕ} {lam : Fin (m + 1) → ℤ} (hl : Antitone lam) (t : Fin (m + 1)) :
    nuOf lam t ≤ ellWt lam := by
  unfold ellWt
  rw [lastIdx_succ]
  exact Int.toNat_le_toNat (sub_le_sub_right (hl (Fin.zero_le t)) _)

theorem formCoreSK_of (h : FormCoreG) : FormCoreSK := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS m lam hl
  have : Fact p.Prime := ⟨hS.prime⟩
  have : IsFractionRing O Kf := hS.frac_O
  have : IsFractionRing W Qq := hS.frac_alt
  have : CharZero W := charZero_of_irreducible_natCast hS.prime hS.p_unif
  have hinj : Function.Injective (ι.comp (algebraMap W Qq)) :=
    ι.injective.comp (IsFractionRing.injective W Qq)
  have : CharZero Kf := charZero_of_injective_ringHom hinj
  have hj : Function.Injective j := by
    intro x y hxy
    apply hinj
    simp only [RingHom.comp_apply, hS.ι_comp, hxy]
  have hp : ¬ IsUnit ((p : ℕ) : O) := by
    intro hu
    have := hS.finite.to_isIntegral.isLocalHom hj
    have hu' : IsUnit (j (p : W)) := by rwa [map_natCast]
    exact hS.p_unif.not_isUnit (isUnit_of_map_unit j _ hu')
  obtain ⟨B, ha, hb, hc, hd, he⟩ := h p O Kf hp (m + 1) (m + 1) le_rfl (nuOf lam) (nuOf_antitone hl)
  refine ⟨B, ha, hb, hc, ?_⟩
  intro Q hQ P hP
  unfold expN
  split_ifs with h0
  · rw [pow_zero, one_smul]
    refine he (fun t => ?_) Q hQ P hP
    have := nuOf_le_ellWt hl t
    omega
  · exact hd (ellWt lam) (Or.inl (nuOf_le_ellWt hl)) Q hQ P hP

end Formalism.L2.G.Model.TS
end
end

namespace Formalism.L2.G.Model.TS.Top

open Formalism.L2.G.Model.TS Formalism.GradedWeylDivisibility

theorem fockRBilin : FockRBilin := Formalism.L2.G.Model.TS.fock_pairing_bilinear
theorem fockRMap : FockRMap := Formalism.L2.G.Model.TS.fock_pairing_map
theorem fockRBlock : FockRBlock := Formalism.L2.G.Model.TS.fock_pairing_block
theorem hWNorm : HWNorm := Formalism.L2.G.Model.TS.highest_weight_norm
theorem fockRRowDivAdj : FockRRowDivAdj := Formalism.L2.G.Model.TS.fock_pairing_divided_adjoint
theorem fockRRowAct : FockRRowAct := Formalism.L2.G.Model.TS.fock_pairing_row_action
theorem fock_pairing_highest_weight : FockPairingHighestWeight := Formalism.L2.G.Model.TS.fock_pairing_highest_weight_proof
theorem weylPair : WeylPair := Formalism.L2.G.Model.TS.weyl_pairing
theorem dualWeylIn : DualWeylIn := Formalism.L2.G.Model.TS.dual_weyl_inclusion
theorem nondegK : NondegK := Formalism.L2.G.Model.TS.nondegenerate_over_field
theorem formCoreSK : FormCoreSK := Formalism.L2.G.Model.TS.formCoreSK_of Formalism.L2.G.Model.TS.weyl_form_nondegenerate_global

end Formalism.L2.G.Model.TS.Top
