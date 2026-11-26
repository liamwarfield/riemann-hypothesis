module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftAtRExistsEq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedTypesLowerBound

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.TypeExponentsConsecutiveGap
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.TypeExponentsDifferByIntegers
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.CapelliParamsDiffInt
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.GapLie

theorem capelli_params_diff_int : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (m : Fin n → ℂ), GlRel E → (∀ w v, qdet E w v = Qr.cpol m w • v) → ∀ i j, ∃ N : ℤ, m i - m j = (N : ℂ) := by
  intro V _ _ _ _ n E m hE hq
  obtain ⟨ν, v, -, hv0, hw, -⟩ := Formalism.FourierDecayAlt.P.exists_singular_maximal_vector V n E hE ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  have hc := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol (m := m) hE (Qr.mem_CapSp.2 fun w => hq w v) hv0 hw
  have hroot : ∀ i, ∃ a : Fin n, m i = ν a - ((a : ℕ) : ℂ) := by
    intro i
    have h1 := hc (-m i)
    unfold Qr.cpol at h1
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by ring)] at h1
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h1.symm
    exact ⟨a, by linear_combination -ha⟩
  have hdom : ∀ a b : Fin n, ∃ N : ℤ, ν a - ν b = (N : ℂ) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · obtain ⟨N, hN⟩ := Formalism.FourierDecayAlt.P.singular_dominant V n E ν v hE hw hv0 a b h
      exact ⟨N, by simpa using hN⟩
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨N, hN⟩ := Formalism.FourierDecayAlt.P.singular_dominant V n E ν v hE hw hv0 b a h
      refine ⟨-N, ?_⟩
      push_cast
      linear_combination -hN
  intro i j
  obtain ⟨a, ha⟩ := hroot i
  obtain ⟨b, hb⟩ := hroot j
  obtain ⟨N, hN⟩ := hdom a b
  refine ⟨N - (a : ℕ) + (b : ℕ), ?_⟩
  push_cast
  linear_combination ha - hb + hN

end GlobalTheory.CompanionTheory.GapLie
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.TypeExponentsDifferByIntegers
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.GapInt

theorem type_param_diff_int : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : B.Mat k r → (Wq →L[ℂ] Wq)) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → ∀ i ∈ Finset.Icc 1 k, ∀ j ∈ Finset.Icc 1 k, ∃ N : ℤ, u i - u j = (N : ℝ) := by
  intro Wq _ _ _ k r z π u hz hT hty i hi j hj
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨Bs, hB⟩ := Formalism.FourierDecayAlt.P.Qx8.frame_exists hz hT
  obtain ⟨hnt, hrep, hcont, -, -, hcap⟩ := hty
  have hR : Qr.IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  obtain ⟨hgl, hq⟩ := Formalism.FourierDecayAlt.P.frame_general_linear Wq (n + 1) r (n + 1) z π Bs hR hB
  have hc : ∀ w v, qdet (Qr.EB π Bs) w v =
      Qr.cpol (fun a : Fin (n + 1) => (u ((a : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2) w • v := by
    intro w v
    rw [← hq w v, hcap Bs hB w v, Formalism.FourierDecayAlt.P.FrameExtension.prod_Icc_fin]
    congr 1
    unfold Qr.cpol
    refine Finset.prod_congr rfl (fun a _ => ?_)
    ring
  obtain ⟨N, hN⟩ := GlobalTheory.CompanionTheory.GapLie.capelli_params_diff_int Wq (n + 1) (Qr.EB π Bs) _ hgl hc
    ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
  refine ⟨N, ?_⟩
  have e1 : i - 1 + 1 = i := by omega
  have e2 : j - 1 + 1 = j := by omega
  simp only [e1, e2] at hN
  have h : ((u i : ℝ) : ℂ) - (u j : ℂ) = (N : ℂ) := by linear_combination hN
  exact_mod_cast h

end GlobalTheory.CompanionTheory.GapInt
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.TypeExponentsDifferByIntegersStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_exponents_differ_by_integers : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : B.Mat k r → (Wq →L[ℂ] Wq)) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → ∀ i ∈ Finset.Icc 1 k, ∀ j ∈ Finset.Icc 1 k, ∃ N : ℤ, u i - u j = (N : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.GapInt.type_param_diff_int | exact GlobalTheory.CompanionTheory.GapInt.type_param_diff_int | (intros; apply GlobalTheory.CompanionTheory.GapInt.type_param_diff_int <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.TypeExponentsConsecutiveGap
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.TypeGaps

theorem gap_eq_nat_add_one :
    ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : B.Mat k r → (Wq →L[ℂ] Wq)) (u : ℕ → ℝ),
      inWb k r z → 0 < Tz k r z → IsType k r z π u →
      (∀ i ∈ Finset.Ico 1 k, u (i + 1) + 1 ≤ u i) →
      ∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1 := by
  intro Wq _ _ _ k r z π u hz hT hty hdec i hi
  rw [Finset.mem_Icc] at hi
  obtain ⟨N, hN⟩ := GlobalTheory.T.type_exponents_differ_by_integers Wq k r z π u hz hT hty i
    (Finset.mem_Icc.2 ⟨hi.1, by omega⟩) (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have h1 := hdec i (Finset.mem_Ico.2 ⟨hi.1, by omega⟩)
  have h2 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have h3 : (1 : ℤ) ≤ N := by exact_mod_cast h2
  refine ⟨(N - 1).toNat, ?_⟩
  have h4 : (((N - 1).toNat : ℕ) : ℤ) = N - 1 := Int.toNat_of_nonneg (by omega)
  have h5 : (((N - 1).toNat : ℕ) : ℝ) = (N : ℝ) - 1 := by exact_mod_cast h4
  rw [hN, h5]
  ring

end GlobalTheory.CompanionTheory.TypeGaps
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.TypeExponentsConsecutiveGapStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_exponents_consecutive_gap : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : B.Mat k r → (Wq →L[ℂ] Wq)) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → (∀ i ∈ Finset.Ico 1 k, u (i + 1) + 1 ≤ u i) → ∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1 := by
  first | exact @GlobalTheory.CompanionTheory.TypeGaps.gap_eq_nat_add_one | exact GlobalTheory.CompanionTheory.TypeGaps.gap_eq_nat_add_one | (intros; apply GlobalTheory.CompanionTheory.TypeGaps.gap_eq_nat_add_one <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapContinuousRep
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.OmgNMulN
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.OmegaBiInv

theorem omg_N_mul_N : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → inWb k r z' → ∀ g ∈ B.GV k r, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, GlobalTheory.WigSh.omg k r z z' (n * g * n') = GlobalTheory.WigSh.omg k r z z' (g) := by
  intro k r z z' hz hz' g hg n hn n' hn'
  rw [Matrix.mul_assoc, GlobalTheory.WigSh.OmLeftN.omg_mul_left k r z z' (g * n') n hz hn]
  exact GlobalTheory.WigSh.omg_mul_N k r z z' g n' hz hz' hg hn'

end GlobalTheory.CompanionTheory.OmegaBiInv
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.OmgLeftRight
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.OmgUW

lemma one_mem_UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z := by
  simp [UWset, UH]

theorem omg_left_right : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → ∀ g ∈ B.GV k r, (∀ h ∈ UWset k r z, GlobalTheory.WigSh.omg k r z z' (h * g) = GlobalTheory.WigSh.omg k r z z' (g)) ∧ ∀ h' ∈ UWset k r z', GlobalTheory.WigSh.omg k r z z' (g * h') = h'⁻¹ *ᵥ GlobalTheory.WigSh.omg k r z z' (g) := by
  intro k r z z' hz hTz hz' hTz' g hg
  refine ⟨fun h hh => ?_, fun h' hh' => ?_⟩
  · have hhU : h ∈ UH (Hpk k r) := by
      simp only [UWset, Set.mem_setOf_eq] at hh
      exact hh.1
    have hii : h⁻¹⁻¹ = h :=
      Matrix.nonsing_inv_nonsing_inv h
        (Matrix.isUnit_det_of_right_inverse (GlobalTheory.WigSh.OmgEquiv.mul_inv hhU))
    have e := GlobalTheory.WigSh.omg_equivariant k r z z' g h⁻¹ 1 hz hTz hz' hTz' hg
      (GlobalTheory.WigSh.OmgEquiv.inv_mem hh) (one_mem_UWset k r z')
    rw [hii, mul_one, inv_one, Matrix.one_mulVec] at e
    exact e
  · have e := GlobalTheory.WigSh.omg_equivariant k r z z' g 1 h' hz hTz hz' hTz' hg
      (one_mem_UWset k r z) hh'
    rw [inv_one, one_mul] at e
    exact e

end GlobalTheory.CompanionTheory.OmgUW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapContinuousRep
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.OmgWigEquiv

theorem wigEquiv_omg (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type)
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ))
    (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ)
    (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq))
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hz' : inWb k r z') (hT' : 0 < Tz k r z')
    (hA : GlobalTheory.WigSh.WigMap k r z' π'' π' d A) (hπ : IsCRepOn (UWset k r z') π'') :
    WigEquiv z z' π' π'' (fun g => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  refine ⟨fun g hg _ n hn n' hn' => ?_, fun g hg _ h hh => ?_, fun g hg _ h hh => ?_⟩
  · exact congrArg A (GlobalTheory.CompanionTheory.OmegaBiInv.omg_N_mul_N k r z z' hz hz' g hg n hn n' hn')
  · exact congrArg A ((GlobalTheory.CompanionTheory.OmgUW.omg_left_right k r z z' hz hT hz' hT' g hg).1 h hh)
  · have hi := Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv hh
    have h1 := (GlobalTheory.CompanionTheory.OmgUW.omg_left_right k r z z' hz hT hz' hT' g hg).2 h hh
    have h2 := hA.2.1 h⁻¹ hi (GlobalTheory.WigSh.omg k r z z' g)
    have h3 : (π'' h⁻¹).comp (π'' h) = ContinuousLinearMap.id ℂ Wq' := by
      rw [← hπ.2 _ hi _ hh, Formalism.FourierDecayAlt.P.LeftDerivativeCurves.uh_inv_mul hh.1, hπ.1]
      rfl
    show A (GlobalTheory.WigSh.omg k r z z' (g * h)) = (π' h⁻¹).comp ((A (GlobalTheory.WigSh.omg k r z z' g)).comp (π'' h))
    rw [h1, ← ContinuousLinearMap.comp_assoc, ← h2, ContinuousLinearMap.comp_assoc, h3,
      ContinuousLinearMap.comp_id]

end GlobalTheory.CompanionTheory.OmgWigEquiv
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapContinuousRepStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wigEquiv_of_wigMap_of_isCRepOn : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A → IsCRepOn (UWset k r z') π'' → WigEquiv z z' π' π'' (fun g => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  first | exact @GlobalTheory.CompanionTheory.OmgWigEquiv.wigEquiv_omg | exact GlobalTheory.CompanionTheory.OmgWigEquiv.wigEquiv_omg | (intros; apply GlobalTheory.CompanionTheory.OmgWigEquiv.wigEquiv_omg <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapPolynomialOperator
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapPolynomialOperator
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.WigOmgPoly

theorem polyOp_wigMap_omg : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A → PolyOp (d * (r + 1)) (fun g : B.Mat k r => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  intro Wq _ _ Wq' _ _ k r z z' π' π'' d A hz hT hz' hT' hA
  exact (GlobalTheory.WigSh.wigMap_omg Wq Wq' k r z z' π' π'' d A hz hT hz' hT' hA).1

end GlobalTheory.CompanionTheory.WigOmgPoly
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapPolynomialOperatorStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wigner_map_polynomial_operator : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A → PolyOp (d * (r + 1)) (fun g : B.Mat k r => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  first | exact @GlobalTheory.CompanionTheory.WigOmgPoly.polyOp_wigMap_omg | exact GlobalTheory.CompanionTheory.WigOmgPoly.polyOp_wigMap_omg | (intros; apply GlobalTheory.CompanionTheory.WigOmgPoly.polyOp_wigMap_omg <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapUpperBound
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapUpperBound
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.WigAtOmega

theorem wigUpper_omg : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type)
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ))
    (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ)
    (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)),
    inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A →
    WigUpper z z' d (fun g : B.Mat k r => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  intro Wq _ _ Wq' _ _ k r z z' π' π'' d A hz hT hz' hT' hA g hg
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.WigSh.OmgNorm.omg_norm k r z z' g hz hT hz' hT' hg
  have h := hA.2.2.2 _ h1 h2
  rw [h3] at h
  exact h

end GlobalTheory.CompanionTheory.WigAtOmega
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapUpperBoundStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wigner_map_upper_bound : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A → WigUpper z z' d (fun g : B.Mat k r => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  first | exact @GlobalTheory.CompanionTheory.WigAtOmega.wigUpper_omg | exact GlobalTheory.CompanionTheory.WigAtOmega.wigUpper_omg | (intros; apply GlobalTheory.CompanionTheory.WigAtOmega.wigUpper_omg <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerPlusMinusDecomposition
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerPlusMinusDecomposition
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.WigLowerOmg

theorem wigLower_omg : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Wqp : Type) [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] (Wqm : Type) [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (b : ℝ) (n₀ : ℕ) (Ap : (Fin (2 * r + k + 1) → ℂ) → (Wqp →L[ℂ] Wq)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Wqm →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → (∀ ω, inWb k r ω → herm (Hpk k r) ω z' = 0 → ∀ v : Wq, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2)) → WigLower z z' b n₀ (fun g : B.Mat k r => Ap (GlobalTheory.WigSh.omg k r z z' (g))) (fun g : B.Mat k r => Am (GlobalTheory.WigSh.omg k r z z' (g))) := by
  intro Wq _ _ _ Wqp _ _ _ Wqm _ _ _ k r z z' b n₀ Ap Am hz hTz hz' hTz' hbound
  unfold WigLower
  intro g hg hGf v
  obtain ⟨hW, hperp, hre⟩ := GlobalTheory.WigSh.OmgNorm.omg_norm k r z z' g hz hTz hz' hTz' hg
  have h := hbound _ hW hperp v
  rw [hre] at h
  have hq : 0 < Gf k r z z' g / Tz k r z' := div_pos hGf hTz'
  have hqn := pow_pos hq n₀
  have key : ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) *
      (‖ContinuousLinearMap.adjoint (Ap (GlobalTheory.WigSh.omg k r z z' g)) v‖ ^ 2 +
        ‖ContinuousLinearMap.adjoint (Am (GlobalTheory.WigSh.omg k r z z' g)) v‖ ^ 2) /
      (Gf k r z z' g / Tz k r z') ^ n₀ := by
    rw [le_div_iff₀ hqn, mul_comm]
    exact h
  refine key.trans (le_of_eq ?_)
  beta_reduce
  rw [← inv_div (Gf k r z z' g) (Tz k r z'), inv_pow]
  ring

end GlobalTheory.CompanionTheory.WigLowerOmg
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerPlusMinusDecompositionStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wigLower_of_adjoint_norm_sq_lower_bound : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Wqp : Type) [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] (Wqm : Type) [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (b : ℝ) (n₀ : ℕ) (Ap : (Fin (2 * r + k + 1) → ℂ) → (Wqp →L[ℂ] Wq)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Wqm →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → (∀ ω, inWb k r ω → herm (Hpk k r) ω z' = 0 → ∀ v : Wq, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2)) → WigLower z z' b n₀ (fun g : B.Mat k r => Ap (GlobalTheory.WigSh.omg k r z z' (g))) (fun g : B.Mat k r => Am (GlobalTheory.WigSh.omg k r z z' (g))) := by
  first | exact @GlobalTheory.CompanionTheory.WigLowerOmg.wigLower_omg | exact GlobalTheory.CompanionTheory.WigLowerOmg.wigLower_omg | (intros; apply GlobalTheory.CompanionTheory.WigLowerOmg.wigLower_omg <;> assumption)
end
end

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.WignerShift

theorem update_eq_uPlus (u : ℕ → ℝ) (l n₀ : ℕ) :
    Function.update u (l + 1) (u (l + 1) + (n₀ : ℝ)) = uPlus u l n₀ := by
  funext i
  unfold uPlus
  rw [Function.update_apply]
  split_ifs with h
  · rw [h]
  · rfl

theorem update_eq_uMinus (u : ℕ → ℝ) (l n₀ : ℕ) :
    Function.update u l (u l - (n₀ : ℝ)) = uMinus u l n₀ := by
  funext i
  unfold uMinus
  rw [Function.update_apply]
  split_ifs with h
  · rw [h]
  · rfl

theorem wigExists : WigExists := by
  intro k r z z' Wq _ _ _ π' u l n₀ b hz hz' hT hT' hπ hdec hl1 hlk hgap hb3 hb
  have hreg := GlobalTheory.T.type_exponents_consecutive_gap Wq k r z' π' u hz' hT' hπ hdec
  have h1 := abs_le.mp (hb l (Finset.mem_Icc.mpr ⟨hl1, hlk.le⟩))
  have h2 := abs_le.mp (hb (l + 1) (Finset.mem_Icc.mpr ⟨by omega, hlk⟩))
  have hn : (n₀ : ℝ) ≤ b := by linarith [h1.2, h2.1]
  obtain ⟨Vp, iP1, iP2, iP3, Vm, familyMassRatio, familyMassSecondLine, iM3, πp, πm, Ap, Am, hπp, hπm, hAp, hAm, hlow⟩ :=
    GlobalTheory.WigSh.exists_shifted_types_lower_bound Wq k r z' π' u l n₀ b hz' hT' hπ hreg hl1 hlk hgap hb hn
      (by linarith)
  rw [update_eq_uPlus] at hπp
  rw [update_eq_uMinus] at hπm
  exact ⟨{
    Wqp := Vp
    Wqm := Vm
    πp := πp
    πm := πm
    Ap := fun g => Ap (GlobalTheory.WigSh.omg k r z z' g)
    Am := fun g => Am (GlobalTheory.WigSh.omg k r z z' g)
    typeP := hπp
    typeM := hπm
    polyP := GlobalTheory.T.wigner_map_polynomial_operator Wq Vp k r z z' π' πp n₀ Ap hz hT hz' hT' hAp
    polyM := GlobalTheory.T.wigner_map_polynomial_operator Wq Vm k r z z' π' πm n₀ Am hz hT hz' hT' hAm
    equivP := GlobalTheory.T.wigEquiv_of_wigMap_of_isCRepOn Wq Vp k r z z' π' πp n₀ Ap hz hT hz' hT' hAp hπp.2.1
    equivM := GlobalTheory.T.wigEquiv_of_wigMap_of_isCRepOn Wq Vm k r z z' π' πm n₀ Am hz hT hz' hT' hAm hπm.2.1
    upperP := GlobalTheory.T.wigner_map_upper_bound Wq Vp k r z z' π' πp n₀ Ap hz hT hz' hT' hAp
    upperM := GlobalTheory.T.wigner_map_upper_bound Wq Vm k r z z' π' πm n₀ Am hz hT hz' hT' hAm
    lower := GlobalTheory.T.wigLower_of_adjoint_norm_sq_lower_bound Wq Vp Vm k r z z' b n₀ Ap Am hz hT hz' hT' hlow }⟩

end GlobalTheory.CompanionTheory.WignerShift
