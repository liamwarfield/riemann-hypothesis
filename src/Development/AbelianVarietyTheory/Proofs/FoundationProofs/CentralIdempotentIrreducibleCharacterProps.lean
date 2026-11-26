module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Scalar
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeDiamondAction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeFunctionIsModularFormCoeffSeq
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleTwistedCoboundary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReparametrizationByTowerParameter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.VolumeOpenPosUpperHalfPlane

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.ZCalc

variable {G : Type} [Group G] [Fintype G]

theorem character_inv (V : FDRep ℂ G) (t : G) : V.character t⁻¹ = (starRingEnd ℂ) (V.character t) := by
  let b := Module.finBasis ℂ V
  have htr : ∀ s, V.character s = (LinearMap.toMatrix b b (V.ρ s)).trace := fun s =>
    LinearMap.trace_eq_matrix_trace ℂ b _
  rw [htr, htr]
  refine Formalism.L2.DIV.trace_inv_of_pow_eq_one _ _ (N := Fintype.card G) Fintype.card_ne_zero ?_ ?_
  · rw [LinearMap.toMatrix_pow, ← map_pow, pow_card_eq_one, map_one, LinearMap.toMatrix_one]
  · rw [← LinearMap.toMatrix_mul, ← map_mul, inv_mul_cancel, map_one, LinearMap.toMatrix_one]

theorem op_zc (V W : FDRep ℂ G) :
    op W.ρ (zc V.character) = PI.CharIdem.act W (PI.CharIdem.charIdem V) := by
  rw [PI.CharIdemW.act_charIdem]
  simp only [op, zc, FDRep.char_one]

theorem conv_zc_of_scalar (χ : G → ℂ) (W : FDRep ℂ G) (c : ℂ) (h : op W.ρ (zc χ) = c • 1) (x : G) :
    conv (zc χ) (zc W.character) x = c * zc W.character x := by
  have h1 : ∑ y, zc χ y * W.character (y * x⁻¹) = c * W.character x⁻¹ := by
    have h2 : LinearMap.trace ℂ W (op W.ρ (zc χ) * W.ρ x⁻¹) = c * W.character x⁻¹ := by
      rw [h, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]; rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h2, op, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, ← map_mul]; rfl
  have h3 : ∀ y, zc χ y * zc W.character (y⁻¹ * x) =
      W.character 1 / (Fintype.card G : ℂ) * (zc χ y * W.character (y * x⁻¹)) := by
    intro y
    have : W.character (y⁻¹ * x)⁻¹ = W.character (y * x⁻¹) := by
      rw [mul_inv_rev, inv_inv, FDRep.char_mul_comm]
    rw [show zc W.character (y⁻¹ * x) = W.character 1 / (Fintype.card G : ℂ) * W.character (y⁻¹ * x)⁻¹ from rfl, this]
    ring
  rw [conv, Finset.sum_congr rfl fun y _ => h3 y, ← Finset.mul_sum, h1,
    show zc W.character x = W.character 1 / (Fintype.card G : ℂ) * W.character x⁻¹ from rfl]
  ring

theorem op_conv_eq {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (a b : G → ℂ) :
    op ρ (conv a b) = op ρ a * op ρ b := by
  simp only [op, conv, Finset.sum_smul, Finset.sum_mul_sum, smul_mul_smul_comm, ← map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine (Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun x => ?_).symm
  simp

theorem rk_eq_trace {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M)
    (e : G → ℂ) (he : conv e e = e) : (rk ρ e : ℂ) = ∑ γ, e γ * LinearMap.trace ℂ M (ρ γ) := by
  have hi : IsIdempotentElem (op ρ e) := by
    rw [IsIdempotentElem, ← op_conv_eq, he]
  have hp := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rk, ← hp, op, map_sum]
  simp only [map_smul, smul_eq_mul]

theorem zc_calc : ∀ (G : Type) [Group G] [Fintype G], ∀ (V : FDRep ℂ G) [CategoryTheory.Simple V], IsProj (zc V.character) ∧ (∀ a : G → ℂ, conv (zc V.character) a = conv a (zc V.character)) ∧ (∀ (W : FDRep ℂ G) [CategoryTheory.Simple W], V.character ≠ W.character → conv (zc V.character) (zc W.character) = 0) ∧ ∀ e : G → ℂ, conv e e = e → conv (zc V.character) e 1 = (Module.finrank ℂ V : ℂ) * (rk V.ρ e : ℂ) / (Fintype.card G : ℂ) := by
  intro G _ _ V hV
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · funext x
    have h := (PI.CharIdemW.scalar G V V hV hV).1 ⟨CategoryTheory.Iso.refl V⟩
    rw [conv_zc_of_scalar _ V 1 (by rw [op_zc, h, one_smul]), one_mul]
  · intro x
    simp only [zc, map_mul, map_div₀, FDRep.char_one, map_natCast]
    rw [character_inv V x⁻¹]
  · intro a
    funext x
    simp only [conv]
    refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight x)) _ _ fun y => ?_
    simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulRight, zc]
    have : V.character ((y⁻¹ * x)⁻¹ * x)⁻¹ = V.character y⁻¹ := by
      rw [← FDRep.char_conj V y⁻¹ x⁻¹]
      congr 1
      group
    rw [this, mul_comm]
  · intro W hW hne
    funext x
    have h := (PI.CharIdemW.scalar G V W hV hW).2 ⟨fun i => hne (FDRep.char_iso i)⟩
    rw [conv_zc_of_scalar _ W 0 (by rw [op_zc, h, zero_smul]), zero_mul]
    rfl
  · intro e he
    rw [rk_eq_trace _ e he, conv, Finset.mul_sum, Finset.sum_div]
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun y => ?_
    simp only [Equiv.inv_apply, zc, mul_one, FDRep.char_one]
    rw [show LinearMap.trace ℂ V (V.ρ y⁻¹) = V.character y⁻¹ from rfl]
    ring

end GlobalTheory.BadShare.ZCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterPropsStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralIdempotent_irreducible_character_props : ∀ (G : Type) [Group G] [Fintype G], ∀ (V : FDRep ℂ G) [CategoryTheory.Simple V], IsProj (zc V.character) ∧ (∀ a : G → ℂ, conv (zc V.character) a = conv a (zc V.character)) ∧ (∀ (W : FDRep ℂ G) [CategoryTheory.Simple W], V.character ≠ W.character → conv (zc V.character) (zc W.character) = 0) ∧ ∀ e : G → ℂ, conv e e = e → conv (zc V.character) e 1 = (Module.finrank ℂ V : ℂ) * (rk V.ρ e : ℂ) / (Fintype.card G : ℂ) := by
  first | exact @GlobalTheory.BadShare.ZCalc.zc_calc | exact GlobalTheory.BadShare.ZCalc.zc_calc | (intros; apply GlobalTheory.BadShare.ZCalc.zc_calc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeUAndDepletion
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeUAndDepletion
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem dep_eq_sub (l : ℕ) (a : ℕ → ℂ) : dep l a = a + (-1 : ℂ) • Vo l (Uo l a) := by
  funext n
  simp only [dep, Vo, Uo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [Nat.mul_div_cancel' h]; ring
  · ring

theorem depletion_mf : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → l.Prime → l ∣ L → (∀ d, χ (d + L) = χ d) → MF k L χ a → MF k L χ (Uo l a) ∧ MF k (L * l) χ (dep l a) := by
  intro k L l χ a hk hl hlL hχ ha
  have haL : MF k (L * l) χ a := ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k L χ).2.2.2.2.1 (L * l) a (dvd_mul_right L l) ha)
  have hU : MF k L χ (Uo l a) := GlobalTheory.T.coeffHeckeUOperator_lowers_level k L l χ a hk hl hlL hχ haL
  refine ⟨hU, ?_⟩
  have hV : MF k (L * l) χ (Vo l (Uo l a)) := (GlobalTheory.T.coeffHeckeVOperator_raises_level k L l χ (Uo l a) hl.pos).1 hU
  have hV' := ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (L * l) χ).2.2.1 (-1 : ℂ) _ hV).1
  rw [dep_eq_sub]
  exact ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (L * l) χ).2.1 _ _ haL hV').1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeUAndDepletionStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → l.Prime → l ∣ L → (∀ d, χ (d + L) = χ d) → MF k L χ a → MF k L χ (Uo l a) ∧ MF k (L * l) χ (dep l a) := by
  first | exact @GlobalTheory.depletion_mf | exact GlobalTheory.depletion_mf | (intros; apply GlobalTheory.depletion_mf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPeriodicWeightsIsModularForm
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPeriodicWeightsIsModularForm
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisPer

theorem per_val {N : ℕ} [NeZero N] (a : ℤ → ℂ) (ha : ∀ x, a (x + N) = a x) (n : ℤ) :
    a n = a (((n : ZMod N).val : ℕ) : ℤ) := by
  have hp : Function.Periodic a (N : ℤ) := ha
  rw [ZMod.val_intCast]
  have := hp.int_mul (n / N) (n % N)
  simp only [Int.cast_id] at this
  rw [← this]
  congr 1
  have := Int.mul_ediv_add_emod n N
  linarith [mul_comm (N : ℤ) (n / N)]

theorem sum_range_zmod {N : ℕ} [NeZero N] (g : ZMod N → ℂ) :
    ∑ y ∈ Finset.range N, g (y : ZMod N) = ∑ z : ZMod N, g z := by
  refine Finset.sum_bij' (fun y _ => (y : ZMod N)) (fun z _ => z.val) (by simp)
    (fun z _ => by simpa using ZMod.val_lt z) (fun y hy => ZMod.val_cast_of_lt (Finset.mem_range.1 hy))
    (fun z _ => ZMod.natCast_zmod_val z) (fun _ _ => rfl)

def invF {N : ℕ} [NeZero N] (a : ℤ → ℂ) (y : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ x : ZMod N, a (x.val : ℤ) * ZMod.stdAddChar (-(x * y))

theorem hat_invF {N : ℕ} [NeZero N] (a : ℤ → ℂ) (ha : ∀ x, a (x + N) = a x) (d : ℤ) :
    hat (invF (N := N) a) d = a d := by
  unfold hat
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have e1 : ∀ y : ℕ, cexp (2 * π * Complex.I * (y * d) / N) = ZMod.stdAddChar ((y : ZMod N) * (d : ZMod N)) := by
    intro y
    have := ZMod.stdAddChar_coe (N := N) ((y : ℤ) * d)
    push_cast at this
    rw [← this]
  simp_rw [e1]
  rw [sum_range_zmod (fun z => invF a z * ZMod.stdAddChar (z * (d : ZMod N)))]
  unfold invF
  simp_rw [mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have e2 : ∀ x y : ZMod N, a (x.val : ℤ) * ZMod.stdAddChar (-(x * y)) * ZMod.stdAddChar (y * (d : ZMod N))
      = a (x.val : ℤ) * ZMod.stdAddChar (y * ((d : ZMod N) - x)) := by
    intro x y
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [e2]
  simp_rw [← Finset.mul_sum]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N)]
  simp_rw [ZMod.card, Nat.cast_ite, Nat.cast_zero, sub_eq_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ (d : ZMod N) (fun x => a (x.val : ℤ) * (N : ℂ))]
  simp only [Finset.mem_univ, if_true]
  rw [← per_val a ha d]
  field_simp

theorem invF_twist {N : ℕ} [NeZero N] (a : ℤ → ℂ) (ha : ∀ x, a (x + N) = a x) (d : ℤ) (c : ℂ)
    (hd : IsCoprime d (N : ℤ)) (hmul : ∀ x, a (x * d) = c * a x) (y : ZMod N) :
    invF (N := N) a y = c * invF (N := N) a (y * (d : ZMod N)) := by
  obtain ⟨u, v, huv⟩ := hd
  have hu : (u : ZMod N) * (d : ZMod N) = 1 := by
    have := congrArg (fun t : ℤ => (t : ZMod N)) huv
    simpa using this
  let U : (ZMod N)ˣ := ⟨(d : ZMod N), (u : ZMod N), by rw [mul_comm]; exact hu, hu⟩
  unfold invF
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have e : ∀ x : ZMod N, c * ((N : ℂ)⁻¹ * (a (x.val : ℤ) * ZMod.stdAddChar (-(x * (y * (d : ZMod N))))))
      = (N : ℂ)⁻¹ * (a ((x * (d : ZMod N)).val : ℤ) * ZMod.stdAddChar (-((x * (d : ZMod N)) * y))) := by
    intro x
    have h1 : a ((x * (d : ZMod N)).val : ℤ) = c * a (x.val : ℤ) := by
      rw [← hmul, per_val a ha ((x.val : ℤ) * d)]
      congr 3
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [h1]
    have h2 : -(x * (y * (d : ZMod N))) = -((x * (d : ZMod N)) * y) := by ring
    rw [h2]; ring
  exact (Fintype.sum_equiv (Units.mulRight U) _ _ e).symm

end GlobalTheory.EisPer

end

open GlobalTheory.EisPer in
theorem GlobalTheory.eis_periodic_weights : ∀ (j L₁ L₂ : ℕ) (a b χ₁ χ₂ : ℤ → ℂ), 1 ≤ j → 0 < L₁ → 0 < L₂ → a 0 = 0 → (∀ x, a (x + L₁) = a x) → (∀ x, b (x + L₂) = b x) → (∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ x, a (x * d) = χ₁ d * a x) ∧ ∀ x, b (x * d) = χ₂ d * b x) → χ₁ (-1) * χ₂ (-1) = (-1) ^ j → ∃ c : ℂ, MF j (L₁ * L₂) (fun d => χ₁ d * χ₂ d) (eis j c a b) := by
  intro j L₁ L₂ a b χ₁ χ₂ hj hL₁ hL₂ ha0 ha hb hχ hpar
  haveI : NeZero L₁ := ⟨hL₁.ne'⟩
  have hhat : hat (invF (N := L₁) a) = a := funext (hat_invF a ha)
  obtain ⟨c, hc, -⟩ := GlobalTheory.T.eisenstein_latticeFunction_isModularFormCoeffSeq j L₁ L₂ b χ₁ χ₂ (invF (N := L₁) a) hj hL₁ hL₂
    (by rw [hhat]; exact ha0) hb
    (fun d hd => ⟨fun y => invF_twist a ha d (χ₁ d)
      (by
        have : IsCoprime d ((L₁ : ℤ) * (L₂ : ℤ)) := by exact_mod_cast hd
        exact this.of_mul_right_left) (hχ d hd).1 y, (hχ d hd).2⟩) hpar
  exact ⟨c, by rw [hhat] at hc; exact hc⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPeriodicWeightsIsModularFormStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_periodic_weights_isModularForm : ∀ (j L₁ L₂ : ℕ) (a b χ₁ χ₂ : ℤ → ℂ), 1 ≤ j → 0 < L₁ → 0 < L₂ → a 0 = 0 → (∀ x, a (x + L₁) = a x) → (∀ x, b (x + L₂) = b x) → (∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ x, a (x * d) = χ₁ d * a x) ∧ ∀ x, b (x * d) = χ₂ d * b x) → χ₁ (-1) * χ₂ (-1) = (-1) ^ j → ∃ c : ℂ, MF j (L₁ * L₂) (fun d => χ₁ d * χ₂ d) (eis j c a b) := by
  first | exact @GlobalTheory.eis_periodic_weights | exact GlobalTheory.eis_periodic_weights | (intros; apply GlobalTheory.eis_periodic_weights <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeTOfPrimeNotDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterSlashSumInvariantOfStable
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterSlashSumInvariantOfStable
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem GlobalTheory.EisM.hsum_inv_of_stable : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (Δ : Set M2) (ι : Type) [Fintype ι] (β : ι → M2) (f : ℍ → ℂ), 1 ≤ k → N ∣ L → N ∣ L' → (∀ δ ∈ Δ, 0 < δ.det ∧ (N : ℤ) ∣ δ 1 0) → (∀ δ ∈ Δ, ∀ γ : SL(2, ℤ), (L' : ℤ) ∣ γ 1 0 → δ * (γ : M2) ∈ Δ) → LRep L Δ β → Inv k L (ch ε) f → Inv k L' (ch ε) (hsum k (ch ε) β f) := by
  intro k L L' N ε Δ ι _ β f hk hNL hNL' hΔ hΔγ hβ hf
  have hcoc := (GlobalTheory.T.slashIntMatrixPosDet_properties k f hk).1
  rw [(GlobalTheory.T.slashIntMatrixPosDet_properties k (hsum k (ch ε) β f) hk).2.2.1 L' (ch ε)]
  intro γ hγ
  have hNγ : (N : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hNL').trans hγ
  have hβmem : ∀ i, β i ∈ Δ := fun i => by
    have := hβ.mapsTo (Set.mem_univ ((1 : Gamma0 L), i))
    simpa using this
  have hγγ : (γ : M2) * ((γ⁻¹ : SL(2,ℤ)) : M2) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hγγ' : ((γ⁻¹ : SL(2,ℤ)) : M2) * (γ : M2) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hγinv : (L' : ℤ) ∣ (γ⁻¹ : SL(2,ℤ)) 1 0 := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simpa using hγ.neg_right
  set β' : ι → M2 := fun i => β i * (γ : M2) with hβ'
  have hβ'rep : LRep L Δ β' := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨g, i⟩ -
      have := hβ.mapsTo (Set.mem_univ (g, i))
      simp only [β', ← mul_assoc]
      exact hΔγ _ this γ hγ
    · rintro ⟨g, i⟩ - ⟨g', j⟩ - h
      have h' := congrArg (· * ((γ⁻¹ : SL(2,ℤ)) : M2)) h
      simp only [β', mul_assoc, hγγ, mul_one] at h'
      exact hβ.injOn (Set.mem_univ _) (Set.mem_univ _) h'
    · intro δ hδ
      have h1 := hΔγ δ hδ γ⁻¹ hγinv
      obtain ⟨⟨g, i⟩, -, hgi⟩ := hβ.surjOn h1
      refine ⟨(g, i), Set.mem_univ _, ?_⟩
      simp only at hgi ⊢
      rw [← mul_assoc, hgi, mul_assoc, hγγ', mul_one]
  have hsumeq := GlobalTheory.T.heckeCharacterSlashSum_indep_reps k L N ε Δ ι ι β β' f hk hNL hΔ hβ hβ'rep hf
  have hdetγ : (0 : ℤ) < (γ : M2).det := by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num
  have hch : ∀ i, ch ε (β' i 0 0) = ch ε (β i 0 0) * ch ε (γ 0 0) := by
    intro i
    have hz : ((γ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNγ
    simp only [ch, β', Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [hz, mul_zero, add_zero, map_mul]
  have hγd : ch ε (γ 0 0) * ch ε (γ 1 1) = 1 := by
    have hd := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hd
    have hz : ((γ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNγ
    have h2 : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have := congrArg (fun x : ℤ => (x : ZMod N)) hd
      push_cast at this
      rw [hz, mul_zero, sub_zero] at this
      exact this
    simp only [ch]
    rw [← map_mul, h2, map_one]
  funext τ
  have hlin : slz k (γ : M2) (hsum k (ch ε) β f) τ = ∑ i, ch ε (β i 0 0) * slz k (γ : M2) (slz k (β i) f) τ := by
    simp only [slz, hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hlin, hsumeq]
  simp only [hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hcoc (β i) γ (hΔ _ (hβmem i)).1 hdetγ, hch i]
  calc ch ε (β i 0 0) * slz k (β i * ↑γ) f τ
      = ch ε (β i 0 0) * (ch ε (γ 0 0) * ch ε (γ 1 1)) * slz k (β i * ↑γ) f τ := by rw [hγd, mul_one]
    _ = _ := by simp only [β']; ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterSlashSumInvariantOfStableStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacterSlashSum_invariant_of_stable : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (Δ : Set M2) (ι : Type) [Fintype ι] (β : ι → M2) (f : ℍ → ℂ), 1 ≤ k → N ∣ L → N ∣ L' → (∀ δ ∈ Δ, 0 < δ.det ∧ (N : ℤ) ∣ δ 1 0) → (∀ δ ∈ Δ, ∀ γ : SL(2, ℤ), (L' : ℤ) ∣ γ 1 0 → δ * (γ : M2) ∈ Δ) → LRep L Δ β → Inv k L (ch ε) f → Inv k L' (ch ε) (hsum k (ch ε) β f) := by
  first | exact @GlobalTheory.EisM.hsum_inv_of_stable | exact GlobalTheory.EisM.hsum_inv_of_stable | (intros; apply GlobalTheory.EisM.hsum_inv_of_stable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeTOfPrimeNotDvd
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem To_MF : ∀ (k L N q : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → N ∣ L → q.Prime → ¬ q ∣ L →
    MF k L (ch ε) a → MF k L (ch ε) (To k (ch ε q) q a) := by
  intro k L N q ε a hk hNL hq hqL ha
  have h1 : ch ε 1 = 1 := by simp [ch]
  obtain ⟨hP, hqs⟩ := GlobalTheory.T.coeffHeckeTOperator_qExpansion_slashSum k q (ch ε) a hk hq.pos h1 ha.1
  refine ⟨hP, ?_⟩
  rw [hqs]
  refine GlobalTheory.T.heckeCharacterSlashSum_invariant_of_stable k L L N ε (DT L q) (Option (Fin q)) (repT q) (qs a) hk hNL hNL ?_ ?_
    (GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepTOperator L q hq hqL) ha.2
  · rintro δ ⟨hdet, hL⟩
    refine ⟨by rw [hdet]; exact_mod_cast hq.pos, ?_⟩
    exact (Int.natCast_dvd_natCast.mpr hNL).trans hL
  · rintro δ ⟨hdet, hL⟩ γ hγ
    refine ⟨?_, ?_⟩
    · rw [Matrix.det_mul, hdet]
      simp
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_mul_of_dvd_left hL _) (dvd_mul_of_dvd_right hγ _)

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeTOfPrimeNotDvdStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd : ∀ (k L N q : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → N ∣ L → q.Prime → ¬ q ∣ L → MF k L (ch ε) a → MF k L (ch ε) (To k (ch ε q) q a) := by
  first | exact @GlobalTheory.EisM.To_MF | exact GlobalTheory.EisM.To_MF | (intros; apply GlobalTheory.EisM.To_MF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinProductSeriesEqDepletedEisensteinProdu
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinProductSeriesEqDepletedEisensteinProdu
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem zm_eq_mul_dep_eis : ∀ (k l j : ℕ) (u w A A' : ℤ → ℂ) (c c' : ℂ), j + 2 ≤ k → Zm k l u w (fun x y => A x * A' y * ((y : ℂ) / x) ^ j) = mul (dep l (eis (k - 1 - j) c (fun x => u x * A x) fun _ => 1)) (dep l (eis (j + 1) c' A' w)) := by
  intro k l j u w A A' c c' hjk
  funext n
  unfold Zm mul
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : l ∣ p.1 ∨ l ∣ p.2
  · have hz : dep l (eis (k - 1 - j) c (fun x => u x * A x) fun _ => 1) p.1 * dep l (eis (j + 1) c' A' w) p.2 = 0 := by
      rcases h with h | h <;> simp [dep, h]
    rw [hz]
    simp [h]
  · push_neg at h
    obtain ⟨h1, h2⟩ := h
    have p1 : p.1 ≠ 0 := fun e => h1 (e ▸ dvd_zero l)
    have p2 : p.2 ≠ 0 := fun e => h2 (e ▸ dvd_zero l)
    simp only [dep, eis, h1, h2, p1, p2, if_false, or_self]
    have hsw : ∑ q ∈ p.2.divisorsAntidiagonal, A' (q.1 : ℤ) * ((q.1 : ℂ)) ^ (j + 1 - 1) * w (q.2 : ℤ)
        = ∑ y ∈ p.2.divisorsAntidiagonal, A' (y.2 : ℤ) * ((y.2 : ℂ)) ^ (j + 1 - 1) * w (y.1 : ℤ) := by
      refine Finset.sum_equiv (Equiv.prodComm ℕ ℕ) (fun q => ?_) (fun q _ => rfl)
      simp only [Nat.mem_divisorsAntidiagonal, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, mul_comm]
    rw [hsw, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _ => ?_
    have hx0 : (x.1 : ℂ) ≠ 0 := by
      have := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have : x.1 ≠ 0 := fun e => p1 (by rw [← this, e, zero_mul])
      exact_mod_cast this
    have hk : k - 2 = (k - 1 - j - 1) + j := by omega
    have hj : j + 1 - 1 = j := by omega
    rw [hk, hj, pow_add, div_pow]
    field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinProductSeriesEqDepletedEisensteinProduStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinProductSeries_eq_depleted_eisenstein_product : ∀ (k l j : ℕ) (u w A A' : ℤ → ℂ) (c c' : ℂ), j + 2 ≤ k → Zm k l u w (fun x y => A x * A' y * ((y : ℂ) / x) ^ j) = mul (dep l (eis (k - 1 - j) c (fun x => u x * A x) fun _ => 1)) (dep l (eis (j + 1) c' A' w)) := by
  first | exact @GlobalTheory.zm_eq_mul_dep_eis | exact GlobalTheory.zm_eq_mul_dep_eis | (intros; apply GlobalTheory.zm_eq_mul_dep_eis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormCoeffSeqExpDecayAtEveryCusp
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormCoeffSeqExpDecayAtEveryCusp
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

open Matrix.SpecialLinearGroup
open scoped Pointwise

theorem norm_petersson_self_eq (k : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    ‖UpperHalfPlane.petersson (k : ℤ) f f z‖ = ‖f z‖ ^ 2 * z.im ^ k := by
  simp only [UpperHalfPlane.petersson, norm_mul, Complex.norm_conj, zpow_natCast, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg z.im_pos.le]
  ring

theorem cusp_decay : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ) (γ : SL(2, ℤ)), 1 ≤ k → 0 < L → N ∣ L →
    CF k L (ch ε) a → ∃ C δ : ℝ, 0 < δ ∧ ∀ τ : ℍ, 1 / 2 ≤ τ.im →
      ‖qs a (γ • τ)‖ ^ 2 * (γ • τ).im ^ k ≤ C * Real.exp (-δ * τ.im) := by
  intro k L N ε a γ hk hL hN hcf
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_cuspForm_gamma1_of_isCuspFormCoeffSeq k L N ε a hk hL hN hcf
  obtain ⟨C₀, hC₀⟩ := hcf.2
  haveI : NeZero L := ⟨hL.ne'⟩
  have : ((ConjAct.toConjAct (γ : GL (Fin 2) ℝ)⁻¹) • (Gamma1 L : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using! Subgroup.IsArithmetic.conj (Gamma1 L : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ γ)⁻¹
  obtain ⟨δ, hδ, hd⟩ := (CuspFormClass.zero_at_infty (CuspForm.translate f γ)).petersson_exp_decay_left (k : ℤ) _
      (CuspForm.translate f γ)
  obtain ⟨D, hD, h⟩ := hd.exists_pos
  rw [Asymptotics.isBigOWith_iff, atImInfty, eventually_comap, eventually_atTop] at h
  obtain ⟨y, hy⟩ := h
  have hC₀0 : 0 ≤ C₀ := le_trans (by positivity) (hC₀ UpperHalfPlane.I)
  refine ⟨max D (C₀ * Real.exp (δ * |y|)), δ, hδ, fun τ hτ => ?_⟩
  have key : ‖qs a (γ • τ)‖ ^ 2 * (γ • τ).im ^ k =
      ‖UpperHalfPlane.petersson (k : ℤ) (CuspForm.translate f γ) (CuspForm.translate f γ) τ‖ := by
    rw [show ((CuspForm.translate f γ : CuspForm _ _) : ℍ → ℂ) = (⇑f) ∣[(k : ℤ)] γ from rfl,
      UpperHalfPlane.petersson_slash_SL, norm_petersson_self_eq, hf]
  rw [key]
  rcases le_total y τ.im with h1 | h1
  · have h2 := hy _ h1 τ rfl
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h2
    exact h2.trans (by gcongr; exact le_max_left _ _)
  · rw [← key]
    have h3 : 1 ≤ Real.exp (δ * |y|) * Real.exp (-δ * τ.im) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith [le_abs_self y]
    calc ‖qs a (γ • τ)‖ ^ 2 * (γ • τ).im ^ k ≤ C₀ := hC₀ _
      _ ≤ C₀ * (Real.exp (δ * |y|) * Real.exp (-δ * τ.im)) := le_mul_of_one_le_right hC₀0 h3
      _ = C₀ * Real.exp (δ * |y|) * Real.exp (-δ * τ.im) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormCoeffSeqExpDecayAtEveryCuspStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_coeffSeq_exp_decay_at_every_cusp : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ) (γ : SL(2, ℤ)), 1 ≤ k → 0 < L → N ∣ L → CF k L (ch ε) a → ∃ C δ : ℝ, 0 < δ ∧ ∀ τ : ℍ, 1 / 2 ≤ τ.im → ‖qs a (γ • τ)‖ ^ 2 * (γ • τ).im ^ k ≤ C * Real.exp (-δ * τ.im) := by
  first | exact @GlobalTheory.EisM.cusp_decay | exact GlobalTheory.EisM.cusp_decay | (intros; apply GlobalTheory.EisM.cusp_decay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricLevelH1Coboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricLevelH1Coboundary
noncomputable section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois Polynomial

namespace GlobalTheory.K5.Reb

def RebT {p : ℕ} [Fact p.Prime] (Ω : Type) [Field Ω] (_ψ : O0 p →+* Ω) : Type := Ω

section Inst

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω]

instance (ψ : O0 p →+* Ω) : Field (RebT Ω ψ) := inferInstanceAs (Field Ω)

instance (ψ : O0 p →+* Ω) : Algebra (O0 p) (RebT Ω ψ) := ψ.toAlgebra

end Inst

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
variable {T : GlobalTheory.K5.Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω}

theorem mem_range (hψ : IsReb T L ψ) (a : O0 p) : ∃ b, ψ b = algebraMap (O0 p) Ω a := by
  have h : algebraMap (O0 p) Ω a ∈ ψ.range := by
    rw [hψ.rng, Subalgebra.mem_toSubring]
    exact Subalgebra.algebraMap_mem _ a
  exact RingHom.mem_range.1 h

def jf (hψ : IsReb T L ψ) (a : O0 p) : O0 p := (mem_range hψ a).choose

theorem jf_spec (hψ : IsReb T L ψ) (a : O0 p) : ψ (jf hψ a) = algebraMap (O0 p) Ω a :=
  (mem_range hψ a).choose_spec

def jj (hψ : IsReb T L ψ) : O0 p →+* O0 p where
  toFun := jf hψ
  map_one' := hψ.inj (by rw [jf_spec, map_one, map_one])
  map_mul' a b := hψ.inj (by rw [jf_spec, map_mul, map_mul, jf_spec, jf_spec])
  map_zero' := hψ.inj (by rw [jf_spec, map_zero, map_zero])
  map_add' a b := hψ.inj (by rw [jf_spec, map_add (f := _), map_add (f := _), jf_spec, jf_spec])

theorem comp_jj (hψ : IsReb T L ψ) : ψ.comp (jj hψ) = algebraMap (O0 p) Ω :=
  RingHom.ext (jf_spec hψ)

theorem isInt_iff (hψ : IsReb T L ψ) (x : Ω) : @IsInt p _ (RebT Ω ψ) _ _ x ↔ IsInt (p := p) x := by
  constructor
  · rintro ⟨f, hf, h⟩
    let A := Algebra.adjoin (O0 p) {T.qq L}
    have hq : IsIntegral (O0 p) (T.qq L) := by
      refine ⟨X ^ (p ^ L) - C (qO p), monic_X_pow_sub_C _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), ?_⟩
      rw [← aeval_def]
      simp [GlobalTheory.K5.Basic.qq_pow]
    haveI : Algebra.IsIntegral (O0 p) A := Algebra.IsIntegral.adjoin (by rintro _ rfl; exact hq)
    let g : O0 p →+* A := ψ.codRestrict A (fun b => by
      have := ψ.mem_range_self b
      rw [hψ.rng] at this
      exact this)
    have hA : IsIntegral A x := by
      refine ⟨f.map g, hf.map g, ?_⟩
      rw [eval₂_map]
      have e : (algebraMap A Ω).comp g = ψ := RingHom.ext fun _ => rfl
      rw [e]
      exact h
    exact isIntegral_trans x hA
  · rintro ⟨f, hf, h⟩
    refine ⟨f.map (jj hψ), hf.map _, ?_⟩
    show eval₂ ψ x (f.map (jj hψ)) = 0
    rw [eval₂_map]
    rw [comp_jj]
    exact h

theorem cong_iff (hψ : IsReb T L ψ) (k : ℕ) (x y : Ω) :
    @Cong p _ (RebT Ω ψ) _ _ k x y ↔ Cong (p := p) k x y := by
  constructor
  · rintro ⟨z, hz, e⟩
    exact ⟨z, (isInt_iff hψ z).1 hz, e⟩
  · rintro ⟨z, hz, e⟩
    exact ⟨z, (isInt_iff hψ z).2 hz, e⟩

theorem isClo (hΩ : IsClo p Ω) (hψ : IsReb T L ψ) : IsClo p (RebT Ω ψ) := by
  refine ⟨hψ.inj, ⟨fun (x : Ω) => ?_⟩, hΩ.clo⟩
  obtain ⟨f, hf, h⟩ := hΩ.alg.isAlgebraic x
  have hinj : Function.Injective (jj hψ) := by
    intro a b hab
    apply hΩ.inj
    rw [← comp_jj hψ, RingHom.comp_apply, RingHom.comp_apply, hab]
  refine ⟨f.map (jj hψ), (Polynomial.map_ne_zero_iff hinj).2 hf, ?_⟩
  show eval₂ ψ x (f.map (jj hψ)) = 0
  rw [eval₂_map, comp_jj, ← aeval_def]
  exact h

theorem zp_eq (hψ : IsReb T L ψ) (z : ℤ_[p]) :
    ψ (algebraMap ℤ_[p] (O0 p) z) = algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) z) := by
  have e : algebraMap ℤ_[p] (O0 p) z = algebraMap (Lau p) (O0 p) (HahnSeries.C z) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] (Lau p) (O0 p)]
    congr 1
    show HahnSeries.ofPowerSeries ℤ ℤ_[p] (algebraMap ℤ_[p] (PowerSeries ℤ_[p]) z) = _
    rw [← HahnSeries.ofPowerSeries_C]
    rfl
  rw [e]
  have hp0 : (p : ℤ) ^ L ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  refine hψ.sub _ _ (fun i => ?_) (fun r hr => ?_)
  · by_cases hi : i = 0
    · subst hi; simp [HahnSeries.C_apply, HahnSeries.coeff_single]
    · have : (p : ℤ) ^ L * i ≠ 0 := mul_ne_zero hp0 hi
      simp [HahnSeries.C_apply, HahnSeries.coeff_single, hi, this]
  · have : r ≠ 0 := by rintro rfl; exact hr (dvd_zero _)
    simp [HahnSeries.C_apply, HahnSeries.coeff_single, this]

theorem isAlgZp_iff (hψ : IsReb T L ψ) (x : Ω) : @IsAlgZp p _ (RebT Ω ψ) _ _ x ↔ IsAlgZp p x := by
  have hc : ψ.comp (algebraMap ℤ_[p] (O0 p)) = (algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p)) :=
    RingHom.ext (zp_eq hψ)
  constructor
  · rintro ⟨P, hP, h⟩
    refine ⟨P, hP, ?_⟩
    have h' : eval₂ ψ x (P.map (algebraMap ℤ_[p] (O0 p))) = 0 := h
    rw [eval₂_map, hc, ← eval₂_map, ← aeval_def] at h'
    exact h'
  · rintro ⟨P, hP, h⟩
    refine ⟨P, hP, ?_⟩
    show eval₂ ψ x (P.map (algebraMap ℤ_[p] (O0 p))) = 0
    rw [eval₂_map, hc, ← eval₂_map, ← aeval_def]
    exact h

def tw (hψ : IsReb T L ψ) : GlobalTheory.K5.Tower p (RebT Ω ψ) where
  ζ := T.ζ
  qq k := T.qq (L + k)
  prim := T.prim
  ζpow := T.ζpow
  q0 := hψ.par.symm
  qpow k := T.qpow (L + k)

def down (hψ : IsReb T L ψ) (g : Gal p (RebT Ω ψ)) : Gal p Ω :=
  AlgEquiv.ofRingEquiv (f := (g.toRingEquiv : Ω ≃+* Ω)) (fun a => by
    obtain ⟨b, hb⟩ := mem_range hψ a
    rw [← hb]
    exact g.commutes b)

theorem down_mul (hψ : IsReb T L ψ) (g h : Gal p (RebT Ω ψ)) : down hψ (g * h) = down hψ g * down hψ h :=
  AlgEquiv.ext fun _ => rfl

theorem fix_range (hψ : IsReb T L ψ) (g : Gal p Ω) (hg : g (T.qq L) = T.qq L) (a : O0 p) : g (ψ a) = ψ a := by
  have h1 : ψ a ∈ (Algebra.adjoin (O0 p) {T.qq L}).toSubring := hψ.rng ▸ ψ.mem_range_self a
  have h2 : Algebra.adjoin (O0 p) {T.qq L} ≤ AlgHom.equalizer (g : Ω →ₐ[O0 p] Ω) (AlgHom.id (O0 p) Ω) :=
    Algebra.adjoin_le (by rintro x rfl; exact hg)
  exact (AlgHom.mem_equalizer _ _ _).1 (h2 h1)

def up (hψ : IsReb T L ψ) (g : Gal p Ω) (hg : g (T.qq L) = T.qq L) : Gal p (RebT Ω ψ) :=
  AlgEquiv.ofRingEquiv (f := (g.toRingEquiv : RebT Ω ψ ≃+* RebT Ω ψ)) (fun a => fix_range hψ g hg a)

theorem isAlgZp_zeta (T : GlobalTheory.K5.Tower p Ω) (L : ℕ) : IsAlgZp p (T.ζ L) := by
  refine ⟨X ^ (p ^ L) - C 1, (monic_X_pow_sub_C _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).ne_zero, ?_⟩
  simp [(T.prim L).pow_eq_one]

theorem mem_H (hψ : IsReb T L ψ) {g : Gal p (RebT Ω ψ)} (hg : g ∈ Ggeo p (RebT Ω ψ)) :
    down hψ g ∈ Ggeo p Ω ⊓ Gn T L := by
  have hgeo : down hψ g ∈ Ggeo p Ω := fun x hx => hg x ((isAlgZp_iff hψ x).2 hx)
  refine Subgroup.mem_inf.2 ⟨hgeo, (GlobalTheory.K5.Basic.mem_gn T L _).2 ⟨hgeo _ (isAlgZp_zeta T L), ?_⟩⟩
  have h : g (ψ (qO p)) = ψ (qO p) := g.commutes (qO p)
  rw [hψ.par] at h
  exact h

theorem exists_up (hψ : IsReb T L ψ) {g : Gal p Ω} (hg : g ∈ Ggeo p Ω ⊓ Gn T L) :
    ∃ g' : Gal p (RebT Ω ψ), g' ∈ Ggeo p (RebT Ω ψ) ∧ down hψ g' = g := by
  have hg1 := (Subgroup.mem_inf.1 hg).1
  have hq := ((GlobalTheory.K5.Basic.mem_gn T L g).1 (Subgroup.mem_inf.1 hg).2).2
  exact ⟨up hψ g hq, fun x hx => hg1 x ((isAlgZp_iff hψ x).1 hx), AlgEquiv.ext fun _ => rfl⟩

theorem h1_geometric_level_coboundary : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → ∀ lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq →
  (∀ a : Gal p Ω → Ω, IntegralLocallyConstCochainModPow n (Ggeo p Ω ⊓ Gn T L) a → (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), Cong (p := p) n (a (g * h)) (a g + g (a h))) →
    ∃ o : Ω, IsInt (p := p) o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => (p : Ω) ^ c * a g - o * ((lq g).val : Ω))) ∧
  (∀ o : Ω, IsInt (p := p) o → (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) → Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => o * ((lq g).val : Ω)) → Cong (p := p) n ((p : Ω) ^ c * o) 0) := by
  intro p _ hp2
  have hkum := GlobalTheory.K5.TopGeo.top p hp2
  obtain ⟨c, hc⟩ := hkum
  refine ⟨c, fun Ω _ _ hΩ T L n _ lq hlq => ?_⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_reparametrizationByTowerParameter p Ω hΩ T L
  have hk : IsKum (tw hψ) n (Ggeo p (RebT Ω ψ)) ((tw hψ).qq n) (fun g => lq (down hψ g)) :=
    fun g hg => hlq (down hψ g) (mem_H hψ hg)
  obtain ⟨h1, h2⟩ := hc (RebT Ω ψ) (isClo hΩ hψ) (tw hψ) n (fun _ => 0) _ hk
  constructor
  · intro a ha hcoc
    have hlc : IntegralLocallyConstCochainModPow n (Ggeo p (RebT Ω ψ)) (fun g => a (down hψ g)) := by
      refine ⟨fun g hg => (isInt_iff hψ _).2 (ha.1 _ (mem_H hψ hg)), fun g hg => ?_⟩
      obtain ⟨S, hS⟩ := ha.2 _ (mem_H hψ hg)
      exact ⟨S, fun h hh hx => (cong_iff hψ n _ _).2 (hS _ (mem_H hψ hh) hx)⟩
    have hco : IsTwistedOneCocycle 0 n (Ggeo p (RebT Ω ψ)) (fun _ => 0) (fun g => a (down hψ g)) := by
      intro g hg h hh
      simp only [pow_zero, one_mul]
      rw [down_mul]
      exact (cong_iff hψ n _ _).2 (hcoc _ (mem_H hψ hg) _ (mem_H hψ hh))
    obtain ⟨o, ho, hof, x, hx, hxc⟩ := h1 _ hlc hco
    refine ⟨o, (isInt_iff hψ o).1 ho, fun g hg => ?_, x, (isInt_iff hψ x).1 hx, fun g hg => ?_⟩
    · obtain ⟨g', hg', rfl⟩ := exists_up hψ hg
      exact hof g' hg'
    · obtain ⟨g', hg', rfl⟩ := exists_up hψ hg
      have e := hxc g' hg'
      rw [pow_zero, one_mul] at e
      exact (cong_iff hψ n _ _).1 e
  · intro o ho hof hcob
    obtain ⟨x, hx, hxc⟩ := hcob
    refine (cong_iff hψ n _ _).1 (h2 o ((isInt_iff hψ o).2 ho) (fun g hg => hof _ (mem_H hψ hg))
      ⟨x, (isInt_iff hψ x).2 hx, fun g hg => ?_⟩)
    rw [pow_zero, one_mul]
    exact (cong_iff hψ n _ _).2 (hxc _ (mem_H hψ hg))

end GlobalTheory.K5.Reb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricLevelH1CoboundaryStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_level_h1_coboundary : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → ∀ lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq →
  (∀ a : Gal p Ω → Ω, IntegralLocallyConstCochainModPow n (Ggeo p Ω ⊓ Gn T L) a → (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), Cong (p := p) n (a (g * h)) (a g + g (a h))) →
    ∃ o : Ω, IsInt (p := p) o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => (p : Ω) ^ c * a g - o * ((lq g).val : Ω))) ∧
  (∀ o : Ω, IsInt (p := p) o → (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) → Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => o * ((lq g).val : Ω)) → Cong (p := p) n ((p : Ω) ^ c * o) 0) := by
  exact @GlobalTheory.K5.Reb.h1_geometric_level_coboundary
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumSelfPosGamma1InterGamma
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevFiniteIndex
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem lev_finiteIndex : ∀ (N l : ℕ), 0 < N → 0 < l → (GlobalTheory.Hk.lev N l).FiniteIndex := by
  intro N l hN hl
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  unfold lev
  infer_instance

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumSelfPosGamma1InterGamma
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem petersson_self_eq (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    petersson k f f z = ((‖f z‖ ^ 2 * z.im ^ k : ℝ) : ℂ) := by
  rw [petersson, mul_comm (starRingEnd ℂ (f z)), Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

end GlobalTheory.Hk

namespace GlobalTheory.Hk

theorem pet_self_pos (N l : ℕ) (k : ℤ) (hN : 0 < N) (hl : 0 < l) (f : CuspForm (lev N l) k)
    (hf : f ≠ 0) :
    0 < (pet (lev N l) k ⇑f ⇑f).re ∧ (pet (lev N l) k ⇑f ⇑f).im = 0 := by
  haveI := lev_finiteIndex N l hN hl
  haveI : Finite (SL(2, ℤ) ⧸ lev N l) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (SL(2, ℤ) ⧸ lev N l) := Fintype.ofFinite _
  set r : ℍ → ℝ := fun z => ‖f z‖ ^ 2 * z.im ^ k with hr_def
  have hr0 : ∀ z, 0 ≤ r z := fun z => mul_nonneg (sq_nonneg _) (zpow_nonneg z.im_pos.le _)
  have hrc : Continuous r := by
    refine (f.holo'.continuous.norm.pow 2).mul ?_
    exact (continuous_im).zpow₀ k fun z => Or.inl z.im_ne_zero
  have hrp : ∀ z, petersson k f f z = (r z : ℂ) := fun z => petersson_self_eq k f z

  set I : SL(2, ℤ) ⧸ lev N l → ℝ := fun q => ∫ z in ModularGroup.fd, r (q.out⁻¹ • z) with hI
  have hpet : pet (lev N l) k ⇑f ⇑f = ((∑ q, I q : ℝ) : ℂ) := by
    rw [pet, finsum_eq_sum_of_fintype, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [hrp, hI]
    exact integral_ofReal
  have hI0 : ∀ q, 0 ≤ I q := fun q => integral_nonneg fun z => hr0 _

  obtain ⟨z₀, hz₀⟩ : ∃ z, f z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (CuspForm.ext h)
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z₀
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (lev N l) g
  have hinv : ∀ z, r (((h⁻¹ : lev N l) : SL(2, ℤ)) • z) = r z := by
    intro z
    have e := SlashInvariantFormClass.norm_petersson_smul (f := f) (f' := f) (τ := z)
      (Γ := (lev N l : Subgroup (GL (Fin 2) ℝ)))
      (g := (((h⁻¹ : lev N l) : SL(2, ℤ)) : GL (Fin 2) ℝ)) ⟨_, (h⁻¹).2, rfl⟩
    rw [hrp, hrp, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hr0 _),
      Real.norm_of_nonneg (hr0 _)] at e
    exact e
  have hpt : (((g : SL(2, ℤ) ⧸ lev N l)).out⁻¹ • (g • z₀)) = ((h⁻¹ : lev N l) : SL(2, ℤ)) • z₀ := by
    rw [hh, smul_smul, mul_inv_rev, inv_mul_cancel_right]
    rfl
  have hIpos : 0 < I (g : SL(2, ℤ) ⧸ lev N l) := by
    have hpos : 0 < r ((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ • (g • z₀)) := by
      rw [hpt, hinv]
      exact mul_pos (pow_pos (norm_pos_iff.2 hz₀) 2) (zpow_pos z₀.im_pos _)
    have hc : Continuous fun z : ℍ => r ((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ • z) :=
      hrc.comp (continuous_const_smul (((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ))
    have hint : IntegrableOn (fun z : ℍ => r ((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ • z)) ModularGroup.fd := by
      obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k (lev N l : Subgroup (GL (Fin 2) ℝ)) f f
      have fin := UpperTheory.V.Af.Rs.fdFin (UpperTheory.V.Af.Rs.stripIm UpperTheory.V.Af.Rs.volMap) UpperTheory.V.Af.Rs.volMap
      refine Measure.integrableOn_of_bounded (M := C) fin.2.ne hc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ?_)
      have := hC ((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ • z)
      rw [hrp, Complex.norm_real] at this
      exact this
    exact UpperTheory.V.Af.Rs.fdPos UpperTheory.V.Af.Rs.volMap _ hc (fun z => hr0 _) hint _ hg hpos
  rw [hpet, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨Finset.sum_pos' (fun q _ => hI0 q) ⟨_, Finset.mem_univ _, hIpos⟩, rfl⟩

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumSelfPosGamma1InterGammaStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.peterssonCosetIntegralSum_self_pos_gamma1InterGamma0 : ∀ (N l : ℕ) (k : ℤ), 0 < N → 0 < l → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, f ≠ 0 → 0 < (GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑f).re ∧ (GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑f).im = 0 := by
  first | exact @GlobalTheory.Hk.pet_self_pos | exact GlobalTheory.Hk.pet_self_pos | (intros; apply GlobalTheory.Hk.pet_self_pos <;> assumption)
end
end
