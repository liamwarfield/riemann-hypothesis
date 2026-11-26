module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommonRepresentativesPeriodLatticeHalves
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntOfHomAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralGramCorrectionSkewHermitianMaximal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramDifferenceEntryMemUniformizerPowIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramDifferenceEntryMemUniformizerPowIntegers
open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem gram_entry_eq_hform {L : Type} [Field L] (σ : L →+* L) {n n' r : ℕ}
    (J : Matrix (Fin n') (Fin n') L) (z : Matrix (Fin n') (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (j k : Fin r) :
    (Formalism.UG.cT σ (z * M) * J * (z * M)) j k =
      Formalism.UG.hform σ J (z *ᵥ fun i => M i j) (z *ᵥ fun i => M i k) := by
  have hz : ∀ a l, (z * M) a l = (z *ᵥ fun i => M i l) a := fun a l => by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  simp only [Formalism.UG.cT, Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hz,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem gramDiff_entry_int : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (n n' r : ℕ) (JT : GL (Fin n') L) (a : GL (Fin n) L)
  (x y : Matrix (Fin n') (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
  ϖ ∈ Formalism.UG.intL L → (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
    ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔ ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) → (∀ i k, M i k ∈ Formalism.UG.intL L) → (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.GramEq σ JT x y →
  ∀ j k, ((Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M)) - (Formalism.UG.cT σ (x * M) * (JT : Matrix (Fin n') (Fin n') L) * (x * M))) j k * ϖ ^ max (e j) (e k) ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ n n' r JT a x y M e hϖ hiff hM haM hG j k
  have hcO : ∀ t : ℕ, ϖ ^ t ∈ Formalism.UG.intL L := fun t => Subring.pow_mem _ hϖ t
  have hx : ∀ l, e l ≤ max (e j) (e k) →
      ∀ i, (x *ᵥ ((ϖ ^ max (e j) (e k)) • fun i => M i l)) i ∈ Formalism.UG.intL L := by
    intro l hl
    refine (hiff ((ϖ ^ max (e j) (e k)) • fun i => M i l) (fun i => ?_)).1
      ⟨(ϖ ^ max (e j) (e k)) • (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ fun i => M i l),
        fun i => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; exact Subring.mul_mem _ (hcO _) (hM i l)
    · have h1 : ((ϖ ^ max (e j) (e k)) • (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ fun i => M i l)) i =
          ((((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i l * ϖ ^ e l) * ϖ ^ (max (e j) (e k) - e l) := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hl]
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm]
      rw [h1]; exact Subring.mul_mem _ (haM i l) (hcO _)
    · rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, a.mul_inv, Matrix.one_mulVec]
  have key := hG (fun i => M i j) (fun i => M i k) (fun i => hM i j) (fun i => hM i k) _ (hcO _)
    (hx j (le_max_left _ _)) (hx k (le_max_right _ _))
  rw [Matrix.sub_apply, gram_entry_eq_hform, gram_entry_eq_hform, mul_comm]
  exact key

end GlobalTheory.Hk3.HoweG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramDifferenceEntryMemUniformizerPowIntegersStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramDifference_entry_mem_uniformizerPow_integers : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (n n' r : ℕ) (JT : GL (Fin n') L) (a : GL (Fin n) L)
  (x y : Matrix (Fin n') (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
  ϖ ∈ Formalism.UG.intL L → (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
    ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔ ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) → (∀ i k, M i k ∈ Formalism.UG.intL L) → (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.GramEq σ JT x y →
  ∀ j k, ((Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M)) - (Formalism.UG.cT σ (x * M) * (JT : Matrix (Fin n') (Fin n') L) * (x * M))) j k * ϖ ^ max (e j) (e k) ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.HoweG.gramDiff_entry_int | exact GlobalTheory.Hk3.HoweG.gramDiff_entry_int | (intros; apply GlobalTheory.Hk3.HoweG.gramDiff_entry_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OneAddMaximalMatrixIntegralInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OneAddMaximalMatrixIntegralInverse
open Matrix

namespace GlobalTheory.Hk3

theorem one_add_maximal_inv_int (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (n : ℕ) (X : Matrix (Fin n) (Fin n) L) (hX : ∀ i j, Valued.v (X i j) < 1) :
    ∃ k : GL (Fin n) L, (k : Matrix (Fin n) (Fin n) L) = 1 + X ∧
      ∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
  classical
  let v : Valuation L (WithZero (Multiplicative ℤ)) := Valued.v
  let O := v.valuationSubring
  let Y : Matrix (Fin n) (Fin n) O := fun i j => ⟨X i j, (hX i j).le⟩
  have hY : ∀ i j, IsLocalRing.residue O (Y i j) = 0 := fun i j => by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (Valuation.mem_maximalIdeal_iff L v).2 (hX i j)
  have h1 : (IsLocalRing.residue O).mapMatrix (1 + Y) = 1 := by
    rw [map_add (f := _), map_one]
    have : (IsLocalRing.residue O).mapMatrix Y = 0 := by
      ext i j; exact hY i j
    rw [this, add_zero]
  have hd : IsUnit (1 + Y).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, h1, det_one]
    exact one_ne_zero
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hd
  refine ⟨Units.map (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* _).toMonoidHom u, ?_, ?_⟩
  · show O.subtype.mapMatrix (u : Matrix (Fin n) (Fin n) O) = _
    rw [hu, map_add (f := _), map_one]
    rfl
  · intro i j
    rw [← map_inv]
    exact ((u⁻¹ : (Matrix (Fin n) (Fin n) O)ˣ).1 i j).2

end GlobalTheory.Hk3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OneAddMaximalMatrixIntegralInverseStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_add_maximal_matrix_integral_inverse : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (X : Matrix (Fin n) (Fin n) L), (∀ i j, Valued.v (X i j) < 1) →
  ∃ k : GL (Fin n) L, (k : Matrix (Fin n) (Fin n) L) = 1 + X ∧ ∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.one_add_maximal_inv_int | exact GlobalTheory.Hk3.one_add_maximal_inv_int | (intros; apply GlobalTheory.Hk3.one_add_maximal_inv_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramHermitianSkewTraceSigmaFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramHermitianSkewTraceSigmaFixed
open Matrix

namespace GlobalTheory

theorem gram_hermitian_and_trace_fixed :
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L), (∀ x, σ (σ x) = x) → σ δ = -δ →
  ∀ (n' r : ℕ) (JT : GL (Fin n') L) (z : Matrix (Fin n') (Fin r) L) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
  (∀ k j, σ (Γ k j) = - Γ j k) →
  (∀ j k, σ ((Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) j k) = (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) k j) ∧
  σ (δ * Matrix.trace (Γ * (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z))) =
    δ * Matrix.trace (Γ * (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z)) := by
  intro L _ _ σ δ hσ hδ n' r JT z Γ hJ hΓ
  have h1 : ∀ j k, σ ((Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) j k) =
      (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) k j := by
    intro j k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum,
      map_mul, hσ, hJ, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  refine ⟨h1, ?_⟩
  generalize Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z = G at h1 ⊢
  have h2 : σ (Matrix.trace (Γ * G)) = - Matrix.trace (Γ * G) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul, hΓ, h1,
      ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [map_mul, hδ, h2]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramHermitianSkewTraceSigmaFixedStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_hermitian_skewTrace_sigmaFixed : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L), (∀ x, σ (σ x) = x) → σ δ = -δ →
  ∀ (n' r : ℕ) (JT : GL (Fin n') L) (z : Matrix (Fin n') (Fin r) L) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
  (∀ k j, σ (Γ k j) = - Γ j k) →
  (∀ j k, σ ((Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) j k) = (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) k j) ∧
  σ (δ * Matrix.trace (Γ * (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z))) =
    δ * Matrix.trace (Γ * (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z)) := by
  first | exact @GlobalTheory.gram_hermitian_and_trace_fixed | exact GlobalTheory.gram_hermitian_and_trace_fixed | (intros; apply GlobalTheory.gram_hermitian_and_trace_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralOfTraceCharPairingSkewHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralOfTraceCharPairingSkewHermitian
open Matrix

namespace GlobalTheory.Hk3.GramSep

theorem int_of_psi_trace_gam : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ),
  Formalism.UG.IsUnramInv ϖ σ q → (Valued.v δ = 1 ∧ σ δ = -δ) →
  (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) →
  ∀ (r : ℕ) (e : Fin r → ℕ) (Δ : Matrix (Fin r) (Fin r) L), (∀ j k, σ (Δ j k) = Δ k j) →
  (∀ Γ ∈ GlobalTheory.Hk3.GramSep.gam σ ϖ e, ψ (δ * Matrix.trace (Γ * Δ)) = 1) →
  ∀ j k, Δ j k * ϖ ^ max (e j) (e k) ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ q δ ψ hU hδ hne r e Δ hΔ hψ j k
  have hσ := hU.1
  have hv := hU.2.1
  have hw : δ * (Δ j k * ϖ ^ max (e j) (e k)) ∈ Formalism.UG.intL L := by
    refine GlobalTheory.Hk3.int_of_psi hU ψ hne _ (fun b hb => ?_)
    set c : L := b * ϖ ^ max (e j) (e k) with hc
    have hcv : Valued.v c ≤ Valued.v ϖ ^ max (e j) (e k) := by
      rw [hc, map_mul, map_pow]
      exact mul_le_of_le_one_left' hb
    have hmem : Matrix.single k j c + Matrix.single j k (-σ c) ∈ gam σ ϖ e := by
      refine ⟨fun a a' => ?_, fun a a' => ?_⟩
      · simp only [Matrix.add_apply, Matrix.single_apply, map_add (f := _), apply_ite σ, map_neg, hσ, map_zero,
          and_comm (a := k = a'), and_comm (a := j = a')]
        split_ifs <;> ring
      · rw [Matrix.add_apply]
        refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
        · rw [Matrix.single_apply]
          split_ifs with h
          · obtain ⟨rfl, rfl⟩ := h
            rw [max_comm]; exact hcv
          · simp
        · rw [Matrix.single_apply]
          split_ifs with h
          · obtain ⟨rfl, rfl⟩ := h
            rw [Valuation.map_neg, hv]; exact hcv
          · simp
    have h := hψ _ hmem
    have e1 : b * (δ * (Δ j k * ϖ ^ max (e j) (e k))) = δ * (c * Δ j k) := by rw [hc]; ring
    rw [e1, map_mul, map_mul σ c, hδ.2, hΔ, ← h]
    congr 1
    rw [Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul]
    simp only [smul_eq_mul]
    ring
  rw [GlobalTheory.Hk3.mem_intL_iff, map_mul, hδ.1, one_mul] at hw
  exact hw

end GlobalTheory.Hk3.GramSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralOfTraceCharPairingSkewHermitianStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_of_traceCharPairing_skewHermitian : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ),
  Formalism.UG.IsUnramInv ϖ σ q → (Valued.v δ = 1 ∧ σ δ = -δ) →
  (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) →
  ∀ (r : ℕ) (e : Fin r → ℕ) (Δ : Matrix (Fin r) (Fin r) L), (∀ j k, σ (Δ j k) = Δ k j) →
  (∀ Γ ∈ GlobalTheory.Hk3.GramSep.gam σ ϖ e, ψ (δ * Matrix.trace (Γ * Δ)) = 1) →
  ∀ j k, Δ j k * ϖ ^ max (e j) (e k) ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.GramSep.int_of_psi_trace_gam | exact GlobalTheory.Hk3.GramSep.int_of_psi_trace_gam | (intros; apply GlobalTheory.Hk3.GramSep.int_of_psi_trace_gam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOneAddSkewHermitianMulLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOneAddSkewHermitianMulLattice
open Matrix

noncomputable section

namespace GlobalTheory.SelfDualUnip

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem cT_add' (σ : L →+* L) {n : ℕ} (X Y : Matrix (Fin n) (Fin n) L) :
    Formalism.UG.cT σ (X + Y) = Formalism.UG.cT σ X + Formalism.UG.cT σ Y := by
  unfold Formalism.UG.cT; ext i j; simp

theorem det_cT (σ : L →+* L) {n : ℕ} (X : Matrix (Fin n) (Fin n) L) :
    (Formalism.UG.cT σ X).det = σ X.det := by
  unfold Formalism.UG.cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl

theorem cT_int (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} {X : Matrix (Fin n) (Fin n) L}
    (hX : ∀ i j, X i j ∈ Formalism.UG.intL L) (i j : Fin n) : Formalism.UG.cT σ X i j ∈ Formalism.UG.intL L := by
  have h := hX j i
  rw [GlobalTheory.Hk3.mem_intL_iff] at h ⊢
  show Valued.v (σ (X j i)) ≤ 1
  rw [hσ]; exact h

theorem lift_int {n : ℕ} {X : Matrix (Fin n) (Fin n) L} (hX : ∀ i j, X i j ∈ Formalism.UG.intL L) :
    ∃ X' : Matrix (Fin n) (Fin n) (Formalism.UG.intL L), X'.map (Formalism.UG.intL L).subtype = X :=
  ⟨fun i j => ⟨X i j, hX i j⟩, by ext i j; rfl⟩

theorem v_det_eq_one {n : ℕ} {M N : Matrix (Fin n) (Fin n) L} (hM : ∀ i j, M i j ∈ Formalism.UG.intL L)
    (hN : ∀ i j, N i j ∈ Formalism.UG.intL L) (hMN : M * N = 1) : Valued.v M.det = 1 := by
  have hd : Valued.v M.det * Valued.v N.det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, hMN, Matrix.det_one, map_one]
  obtain ⟨M', rfl⟩ := lift_int hM
  obtain ⟨N', rfl⟩ := lift_int hN
  have hdM : (M'.map (Formalism.UG.intL L).subtype).det = (Formalism.UG.intL L).subtype M'.det :=
    (RingHom.map_det _ _).symm
  have hdN : (N'.map (Formalism.UG.intL L).subtype).det = (Formalism.UG.intL L).subtype N'.det :=
    (RingHom.map_det _ _).symm
  have hM1 : Valued.v (M'.map (Formalism.UG.intL L).subtype).det ≤ 1 := by
    rw [hdM]; exact (M'.det).2
  have hN1 : Valued.v (N'.map (Formalism.UG.intL L).subtype).det ≤ 1 := by
    rw [hdN]; exact (N'.det).2
  by_contra hne
  have hlt := lt_of_le_of_ne hM1 hne
  have := mul_lt_one_of_lt_of_le hlt hN1
  rw [hd] at this
  exact lt_irrefl _ this

theorem int_of_left_inv {n : ℕ} {G X : Matrix (Fin n) (Fin n) L} (hG : ∀ i j, G i j ∈ Formalism.UG.intL L)
    (hd : Valued.v G.det = 1) (hXG : X * G = 1) : ∀ i j, X i j ∈ Formalism.UG.intL L := by
  obtain ⟨G', rfl⟩ := lift_int hG
  have hdG : (G'.map (Formalism.UG.intL L).subtype).det = (Formalism.UG.intL L).subtype G'.det :=
    (RingHom.map_det _ _).symm
  have hne : (G'.map (Formalism.UG.intL L).subtype).det ≠ 0 := by
    intro h; rw [h, map_zero] at hd; exact zero_ne_one hd
  have hinv : ((G'.map (Formalism.UG.intL L).subtype).det)⁻¹ ∈ Formalism.UG.intL L := by
    rw [GlobalTheory.Hk3.mem_intL_iff, map_inv₀, hd, inv_one]
  have hu : IsUnit G'.det := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.ext
    show (Formalism.UG.intL L).subtype G'.det * ((G'.map (Formalism.UG.intL L).subtype).det)⁻¹ = 1
    rw [← hdG]; exact mul_inv_cancel₀ hne
  have hGY : G'.map (Formalism.UG.intL L).subtype * (G'⁻¹).map (Formalism.UG.intL L).subtype = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv G' hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hX : X = (G'⁻¹).map (Formalism.UG.intL L).subtype := by
    calc X = X * (G'.map (Formalism.UG.intL L).subtype * (G'⁻¹).map (Formalism.UG.intL L).subtype) := by
          rw [hGY, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hXG, Matrix.one_mul]
  intro i j
  rw [hX]; exact (G'⁻¹ i j).2

theorem selfDual_mul_of_skew : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L), (∀ x, Valued.v (σ x) = Valued.v x) →
  ∀ (n : ℕ) (JS a k : GL (Fin n) L) (E : Matrix (Fin n) (Fin n) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  Formalism.UG.cT σ E * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * E) → (∀ i j, E i j ∈ Formalism.UG.intL L) →
  (∀ i j, (E * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) → (k : Matrix (Fin n) (Fin n) L) = 1 + E →
  (∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.HoweG.SelfDual σ JS (k * a) := by
  intro L _ _ σ hσ n JS a k E hJ ha hE hEint hEa hk hki
  obtain ⟨hG0, hX0⟩ := ha

  have hKint : ∀ i j, (k : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro i j
    rw [hk, Matrix.add_apply, Matrix.one_apply]
    refine (Formalism.UG.intL L).add_mem ?_ (hEint i j)
    split_ifs
    · exact (Formalism.UG.intL L).one_mem
    · exact (Formalism.UG.intL L).zero_mem
  have hE' : ∀ X : Matrix (Fin n) (Fin n) L, Formalism.UG.cT σ E * ((JS : Matrix (Fin n) (Fin n) L) * X) =
      -((JS : Matrix (Fin n) (Fin n) L) * (E * X)) := by
    intro X; rw [← Matrix.mul_assoc, hE, Matrix.neg_mul, Matrix.mul_assoc]

  have hGeq : Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
      (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) =
      Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L) +
      Formalism.UG.cT σ (E * (a : Matrix (Fin n) (Fin n) L)) * (JS : Matrix (Fin n) (Fin n) L) *
        (E * (a : Matrix (Fin n) (Fin n) L)) := by
    rw [hk, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_add', Formalism.UG.cT_one]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hE',
      Matrix.mul_neg]
    abel
  have hGint : ∀ i j, (Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
      (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L))) i j ∈
      Formalism.UG.intL L := by
    intro i j
    rw [hGeq, Matrix.add_apply]
    exact (Formalism.UG.intL L).add_mem (hG0 i j)
      (GlobalTheory.Hk3.matMul_int (GlobalTheory.Hk3.matMul_int (cT_int σ hσ hEa) hJ) hEa i j)

  have hK1 : Valued.v (k : Matrix (Fin n) (Fin n) L).det = 1 := v_det_eq_one hKint hki k.mul_inv
  have hX0G0 : Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L) *
      (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) = 1 := by
    have e3 : Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Formalism.UG.cT_mul, a.inv_mul, Formalism.UG.cT_one]
    calc _ = Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * ((JS : Matrix (Fin n) (Fin n) L) *
          (((a : Matrix (Fin n) (Fin n) L) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
          (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)))) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [a.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc (JS : Matrix (Fin n) (Fin n) L), JS.mul_inv,
          Matrix.one_mul, e3]
  have hG01 := v_det_eq_one hG0 hX0 hX0G0
  have hdet : Valued.v (Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
      (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L))).det = 1 := by
    have : (Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
        (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L))).det =
        σ (k : Matrix (Fin n) (Fin n) L).det * (k : Matrix (Fin n) (Fin n) L).det *
        (Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)).det := by
      simp only [Matrix.det_mul, det_cT, map_mul]; ring
    rw [this, map_mul, map_mul, hσ, hK1, hG01]; simp

  have hXG : (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Formalism.UG.cT σ (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
      (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L))) = 1 := by
    have hka : ((k * a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        (k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L) := Units.val_mul k a
    rw [← hka]
    have e3 : Formalism.UG.cT σ (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        Formalism.UG.cT σ ((k * a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Formalism.UG.cT_mul, (k * a).mul_inv, Formalism.UG.cT_one]
    calc _ = (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          ((Formalism.UG.cT σ (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          Formalism.UG.cT σ ((k * a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
          ((JS : Matrix (Fin n) (Fin n) L) * ((k * a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e3, Matrix.one_mul, ← Matrix.mul_assoc ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L), JS.inv_mul, Matrix.one_mul, (k * a).inv_mul]
  refine ⟨?_, int_of_left_inv hGint hdet hXG⟩
  intro i j
  rw [Units.val_mul]
  exact hGint i j

end GlobalTheory.SelfDualUnip
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOneAddSkewHermitianMulLatticeStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_one_add_skewHermitian_mul_lattice : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L), (∀ x, Valued.v (σ x) = Valued.v x) →
  ∀ (n : ℕ) (JS a k : GL (Fin n) L) (E : Matrix (Fin n) (Fin n) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  Formalism.UG.cT σ E * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * E) → (∀ i j, E i j ∈ Formalism.UG.intL L) →
  (∀ i j, (E * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) → (k : Matrix (Fin n) (Fin n) L) = 1 + E →
  (∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.HoweG.SelfDual σ JS (k * a) := by
  first | exact @GlobalTheory.SelfDualUnip.selfDual_mul_of_skew | exact GlobalTheory.SelfDualUnip.selfDual_mul_of_skew | (intros; apply GlobalTheory.SelfDualUnip.selfDual_mul_of_skew <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SkewConjGramSigmaConjTransposeTraceIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SkewConjGramSigmaConjTransposeTraceIdentity
open Matrix

namespace GlobalTheory

theorem skewConj_cT_mul_and_trace :
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L), (∀ x, σ (σ x) = x) →
  ∀ (n r : ℕ) (JS : GL (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) → (∀ k j, σ (Γ k j) = - Γ j k) →
  Formalism.UG.cT σ (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L))) ∧
  ∀ (n' : ℕ) (JT : GL (Fin n') L) (y : Matrix (Fin n') (Fin n) L),
    Matrix.trace ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ y * (JT : Matrix (Fin n') (Fin n') L) * y) =
      Matrix.trace (Γ * (Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M))) := by
  intro L _ _ σ hσ n r JS M Γ hJ hΓ
  have hmul : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) L) (B : Matrix (Fin b) (Fin c) L),
      Formalism.UG.cT σ (A * B) = Formalism.UG.cT σ B * Formalism.UG.cT σ A := by
    intro a b c A B
    simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have hcc : Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
    ext i j
    simp [Formalism.UG.cT, hσ]
  have hJ' : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS := by
    ext i j
    simp [Formalism.UG.cT, hJ]
  have hΓ' : Formalism.UG.cT σ Γ = -Γ := by
    ext i j
    simp [Formalism.UG.cT, hΓ]
  refine ⟨?_, ?_⟩
  · rw [hmul, hmul, hmul, hcc, hJ', hΓ']
    simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
  · intro n' JT y
    rw [hmul, Matrix.mul_assoc (M * Γ * Formalism.UG.cT σ M), Units.mul_inv, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm M]
    simp only [Matrix.mul_assoc]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SkewConjGramSigmaConjTransposeTraceIdentityStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewConjGram_sigmaConjTranspose_trace_identity : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L), (∀ x, σ (σ x) = x) →
  ∀ (n r : ℕ) (JS : GL (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) → (∀ k j, σ (Γ k j) = - Γ j k) →
  Formalism.UG.cT σ (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L))) ∧
  ∀ (n' : ℕ) (JT : GL (Fin n') L) (y : Matrix (Fin n') (Fin n) L),
    Matrix.trace ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ y * (JT : Matrix (Fin n') (Fin n') L) * y) =
      Matrix.trace (Γ * (Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M))) := by
  first | exact @GlobalTheory.skewConj_cT_mul_and_trace | exact GlobalTheory.skewConj_cT_mul_and_trace | (intros; apply GlobalTheory.skewConj_cT_mul_and_trace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinsetRepresentativesMulInvIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinsetRepresentativesMulInvIntegral
open Matrix

namespace GlobalTheory.Hk3.HoweDuality.Reps

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem eventually_pow_mul_le_one (ϖ : L)
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (e : L) : ∀ᶠ K : ℕ in Filter.atTop, Valued.v ϖ ^ K * Valued.v e ≤ 1 := by
  rcases eq_or_ne (Valued.v e) 0 with h0 | h0
  · exact Filter.Eventually.of_forall fun K => by rw [h0, mul_zero]; exact zero_le
  · obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.1 h0
    refine Filter.eventually_atTop.2 ⟨(Multiplicative.toAdd m).toNat, fun K hK => ?_⟩
    rw [← hm, hϖ, ← WithZero.coe_pow, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe,
      ← ofAdd_nsmul, ← Multiplicative.toAdd_le]
    simp only [toAdd_mul, toAdd_ofAdd, toAdd_one, nsmul_eq_mul, mul_neg, mul_one]
    have : Multiplicative.toAdd m ≤ (K : ℤ) := (Int.self_le_toNat _).trans (by exact_mod_cast hK)
    linarith

end GlobalTheory.Hk3.HoweDuality.Reps

open GlobalTheory.Hk3.HoweDuality.Reps in
theorem GlobalTheory.Hk3.HoweDuality.exists_finset_reps_mul_inv :
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧ ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K) →
  ∀ (n n' : ℕ) (a : GL (Fin n) L) (x : Matrix (Fin n') (Fin n) L),
  (∀ i j, (x * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  ∃ Y : Finset (Matrix (Fin n') (Fin n) L), x ∈ Y ∧ (∀ y ∈ Y, ∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
    (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → y = y') ∧
    ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ∃ y ∈ Y, u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - y ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n := by
  intro L _ _ ϖ hϖ hR n n' a x hx
  classical
  set ai : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hai
  have hinv : ai * (a : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [hai, ← Units.val_mul, inv_mul_cancel, Units.val_one]

  obtain ⟨K, hK⟩ := (Filter.eventually_all.2 fun p : Fin n × Fin n =>
    eventually_pow_mul_le_one ϖ hϖ (ai p.1 p.2)).exists
  obtain ⟨R, hRint, hRapp⟩ := hR K
  have hv1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_le_coe, ← Multiplicative.toAdd_le]; simp

  let S : Finset (Matrix (Fin n') (Fin n) L) :=
    Fintype.piFinset fun _ : Fin n' => Fintype.piFinset fun _ : Fin n => R
  have hSint : ∀ s ∈ S, ∀ i j, s i j ∈ Formalism.UG.intL L := by
    intro s hs i j
    exact hRint _ (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hs i) j)

  have hcong : ∀ d : Matrix (Fin n') (Fin n) L, (∀ i j, Valued.v (d i j) ≤ Valued.v ϖ ^ K) →
      d * ai ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n := by
    intro d hd i j
    rw [Matrix.mul_apply]
    refine (Formalism.UG.intL L).sum_mem fun k _ => ?_
    change Valued.v (d i k * ai k j) ≤ 1
    rw [map_mul]
    calc Valued.v (d i k) * Valued.v (ai k j) ≤ Valued.v ϖ ^ K * Valued.v (ai k j) := by gcongr; exact hd i k
      _ ≤ 1 := hK (k, j)
  let T : Finset (Matrix (Fin n') (Fin n) L) := insert x (S.image fun s => s * ai)
  have hTint : ∀ t ∈ T, ∀ i j, (t * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hx
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
      rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
      exact hSint s hs
  let q : Matrix (Fin n') (Fin n) L → Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n :=
    QuotientAddGroup.mk
  let rep : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n → Matrix (Fin n') (Fin n) L :=
    fun c => if q x = c then x else if h : ∃ t ∈ T, q t = c then h.choose else 0
  have hrep : ∀ t ∈ T, rep (q t) ∈ T ∧ q (rep (q t)) = q t := by
    intro t ht
    by_cases hxt : q x = q t
    · have hr : rep (q t) = x := by simp [rep, hxt]
      rw [hr]; exact ⟨Finset.mem_insert_self _ _, hxt⟩
    · have h : ∃ t' ∈ T, q t' = q t := ⟨t, ht, rfl⟩
      simp only [rep, hxt, if_false, h, dif_pos]
      exact h.choose_spec
  refine ⟨T.image fun t => rep (q t), ?_, ?_, ?_, ?_⟩
  · refine Finset.mem_image.2 ⟨x, Finset.mem_insert_self _ _, ?_⟩
    simp [rep]
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact hTint _ (hrep t ht).1
  · intro y hy y' hy' hyy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hy'
    have e : q t = q t' := by
      rw [← (hrep t ht).2, ← (hrep t' ht').2]
      exact QuotientAddGroup.eq_iff_sub_mem.2 hyy
    rw [e]
  · intro u hu
    have hpick : ∀ i j, ∃ r ∈ R, Valued.v (u i j - r) ≤ Valued.v ϖ ^ K := fun i j => hRapp _ (hu i j)
    choose s hsR hsv using hpick
    have hsS : (Matrix.of fun i j => s i j) ∈ S := by
      refine Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 fun j => hsR i j
    have ht : (Matrix.of fun i j => s i j) * ai ∈ T :=
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hsS)
    refine ⟨rep (q ((Matrix.of fun i j => s i j) * ai)), Finset.mem_image_of_mem _ ht, ?_⟩
    have h1 : u * ai - (Matrix.of fun i j => s i j) * ai ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n := by
      rw [← Matrix.sub_mul]
      exact hcong _ fun i j => by simpa using hsv i j
    have h2 := (hrep _ ht).2
    rw [← QuotientAddGroup.eq_iff_sub_mem] at h1 ⊢
    exact h1.trans h2.symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinsetRepresentativesMulInvIntegralStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_representatives_mul_inv_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧ ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K) →
  ∀ (n n' : ℕ) (a : GL (Fin n) L) (x : Matrix (Fin n') (Fin n) L),
  (∀ i j, (x * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  ∃ Y : Finset (Matrix (Fin n') (Fin n) L), x ∈ Y ∧ (∀ y ∈ Y, ∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
    (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → y = y') ∧
    ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ∃ y ∈ Y, u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - y ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n := by
  first | exact @GlobalTheory.Hk3.HoweDuality.exists_finset_reps_mul_inv | exact GlobalTheory.Hk3.HoweDuality.exists_finset_reps_mul_inv | (intros; apply GlobalTheory.Hk3.HoweDuality.exists_finset_reps_mul_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGramClassRepsSelfDualLatticeGroup
open Matrix

namespace GlobalTheory.Hk3.GramSep

open GlobalTheory.Hk3

theorem gram_class_family : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    (Valued.v δ = 1 ∧ σ δ = -δ) → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
      (∀ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweG.HomA σ JS JT x y ↔
        ∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
      (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
        ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔
          ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) ∧
      (∀ w : Fin n → L, (∃ u v : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, v i ∈ Formalism.UG.intL L) ∧
          w = (a : Matrix (Fin n) (Fin n) L) *ᵥ u + v) ↔
        ∃ v : Fin n → L, ∃ w' : Fin n' → L, (∀ i, v i ∈ Formalism.UG.intL L) ∧ (∀ i, w' i ∈ Formalism.UG.intL L) ∧
          w = v + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') →
    ∃ Y : Finset (Matrix (Fin n') (Fin n) L), x ∈ Y ∧ (∀ y ∈ Y, GlobalTheory.Hk3.HoweG.HomA σ JS JT x y) ∧
      (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → y = y') ∧
      ∃ (B : Type) (_ : AddCommGroup B) (_ : Fintype B) (b0 : B → GL (Fin n) L)
        (l : B → Matrix (Fin n') (Fin n) L → Matrix (Fin n') (Fin n) L),
        (∀ b, GlobalTheory.Hk3.HoweG.SelfDual σ JS (b0 b)) ∧
        (∀ b, ∀ y ∈ Y, l b y ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n ∧
          ∃ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
            y + l b y = u * (((b0 b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∧
        (∀ b, ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
          ∃ y ∈ Y, u * (((b0 b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - (y + l b y) ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n) ∧
        (∀ b b', ∀ y ∈ Y, ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l (b + b') y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l (b + b') y))) / 2)) = ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l b y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l b y))) / 2)) * ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l b' y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l b' y))) / 2))) ∧
        (∀ y ∈ Y, GlobalTheory.Hk3.HoweG.GramEq σ JT x y ↔ ∀ b, ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l b y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l b y))) / 2)) = ψ (-((GlobalTheory.Hk3.locH σ δ JS JT x (l b x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (l b x))) / 2))) := by
  intro L _ _ ϖ σ q δ n n' JS JT ψ hU hodd hSint hTint hS hT hδ hpsi_int hpsi_ne x hx a ha
  obtain ⟨hSD, hHom, hN, hNv⟩ := ha
  classical
  have hσσ : ∀ z, σ (σ z) = z := hU.1
  have hσv : ∀ z, Valued.v (σ z) = Valued.v z := hU.2.1
  have hvϖ := hU.2.2.2.1
  have hϖO : ϖ ∈ Formalism.UG.intL L := by
    show Valued.v ϖ ≤ 1
    rw [hvϖ]
    exact WithZero.coe_le_coe.mpr (Multiplicative.ofAdd_le.mpr (by norm_num))
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hodd
  have hδO : δ ∈ Formalism.UG.intL L := by show Valued.v δ ≤ 1; rw [hδ.1]
  have hSJ : ∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := fun i j => glint_entry hSint i j
  have hSJi : ∀ i j, ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L :=
    fun i j => glint_entry (Subgroup.inv_mem _ hSint) i j
  have hTJ : ∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L := fun i j => glint_entry hTint i j
  have hmv : ∀ {p s : ℕ} (A : Matrix (Fin p) (Fin s) L) (v : Fin s → L), (∀ i j, A i j ∈ Formalism.UG.intL L) →
      (∀ i, v i ∈ Formalism.UG.intL L) → ∀ i, (A *ᵥ v) i ∈ Formalism.UG.intL L := by
    intro p s A v hA hv i
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hv j)

  have hxx : HoweG.HomA σ JS JT x x := by
    refine ⟨fun u _ hxu => hxu, fun w hw i => ?_⟩
    rw [Matrix.mulVec_mulVec]
    refine hmv _ w (fun k l => ?_) hw i
    have e1 : x * HoweG.adj σ JS JT x = (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) *
        (JT : Matrix (Fin n') (Fin n') L) := by
      simp only [HoweG.adj, Formalism.UG.cT, Matrix.mul_assoc]
    rw [e1]
    exact matMul_int hx hTJ k l
  have hxa : ∀ i j, (x * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L := (hHom x).mp hxx

  obtain ⟨r, M, e, he1, hMint, hD1, hD2, hD3⟩ := GlobalTheory.T.exists_smithNormalForm_generators_exactOrders L ϖ hvϖ n a
  have hR := GlobalTheory.T.exists_finite_representatives_mod_uniformizerPow L ϖ σ q hU
  obtain ⟨Y, hxY, hYa, hYd, hYc⟩ := GlobalTheory.T.exists_finset_representatives_mul_inv_integral L ϖ hvϖ hR n n' a x hxa
  haveI hfin := GlobalTheory.T.finite_skewHermitian_valuationMax_quot_sum L ϖ σ hvϖ hR r e
  set G := gam σ ϖ e with hG
  set G0 := (gam0 σ ϖ e).addSubgroupOf G with hG0
  let Γf : (G ⧸ G0) → Matrix (Fin r) (Fin r) L := fun b => ((Quotient.out b : G) : Matrix (Fin r) (Fin r) L)
  have hΓ : ∀ b, Γf b ∈ gam σ ϖ e := fun b => (Quotient.out b).2
  let E : (G ⧸ G0) → Matrix (Fin n) (Fin n) L := fun b => M * Γf b * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)
  have hEi : ∀ b, _ := fun b => GlobalTheory.T.integral_gramCorrection_skewHermitian_maximal L ϖ σ hvϖ hσv n r JS a M e (Γf b) hSJ hSD he1 hMint hD1 (hΓ b)
  have hsk : ∀ b, _ := fun b => GlobalTheory.T.skewConjGram_sigmaConjTranspose_trace_identity L σ hσσ n r JS M (Γf b) hS (hΓ b).1
  choose kf hkf hkinv using fun b => GlobalTheory.T.one_add_maximal_matrix_integral_inverse L n (E b) (hEi b).2.2
  have hEint : ∀ b i j, E b i j ∈ Formalism.UG.intL L := fun b i j => le_of_lt ((hEi b).2.2 i j)

  have hEa : ∀ b, ∀ z : Matrix (Fin n') (Fin n) L, (∀ i j, (z * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
      ∀ i j, (z * E b) i j ∈ Formalism.UG.intL L := by
    intro b z hz i j
    have e1 : z * E b = (z * (a : Matrix (Fin n) (Fin n) L)) * (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * E b) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (a : Matrix (Fin n) (Fin n) L), Units.mul_inv, Matrix.one_mul]
    rw [e1]; exact matMul_int hz (hEi b).1 i j
  have hkk : ∀ b, (((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1 =
      -(E b * (((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
    intro b
    have h1 := Units.mul_inv (kf b)
    rw [hkf b, Matrix.add_mul, Matrix.one_mul] at h1
    calc (((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1
        = ((((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) + E b * (((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) - 1 -
            E b * (((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by abel
      _ = _ := by rw [h1]; abel
  let b0 : (G ⧸ G0) → GL (Fin n) L := fun b => kf b * a
  let l : (G ⧸ G0) → Matrix (Fin n') (Fin n) L → Matrix (Fin n') (Fin n) L :=
    fun b y => y * ((((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1)
  have hb0inv : ∀ b, (((b0 b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    intro b; simp only [b0, _root_.mul_inv_rev, Units.val_mul]
  have hlint : ∀ b, ∀ z : Matrix (Fin n') (Fin n) L, (∀ i j, (z * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
      z * ((((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) ∈ HoweDuality.intMat L n' n := by
    intro b z hz i j
    rw [hkk b, Matrix.mul_neg, ← Matrix.mul_assoc]
    exact (Formalism.UG.intL L).neg_mem (matMul_int (hEa b z hz) (hkinv b) i j)

  let Φ : Matrix (Fin n') (Fin n) L → Matrix (Fin r) (Fin r) L :=
    fun y => Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M)
  let w : (G ⧸ G0) → Matrix (Fin n') (Fin n) L → L := fun b y => δ * Matrix.trace (Γf b * Φ y)
  have hPA : ∀ T w0 : L, T - w0 ∈ Formalism.UG.intL L → σ w0 = w0 → ψ (-((T + σ T) / 2)) = ψ (-w0) := by
    intro T w0 hT0 hw0
    obtain ⟨o, hoO, rfl⟩ : ∃ o, o ∈ Formalism.UG.intL L ∧ T = w0 + o := ⟨T - w0, hT0, by ring⟩
    have hp : (o + σ o) / 2 ∈ Formalism.UG.intL L := by
      show Valued.v ((o + σ o) / 2) ≤ 1
      rw [map_div₀, h2, div_one]
      exact (Valuation.map_add _ _ _).trans (max_le hoO (by show Valued.v (σ o) ≤ 1; rw [hσv]; exact hoO))
    have hpσ : σ (-((o + σ o) / 2)) = -((o + σ o) / 2) := by
      rw [map_neg, map_div₀, map_add (f := _), hσσ, map_ofNat]; ring
    have e1 : -(((w0 + o) + σ (w0 + o)) / 2) = -w0 + -((o + σ o) / 2) := by
      have h2ne : (2 : L) ≠ 0 := fun h0 => by rw [h0, map_zero] at h2; exact zero_ne_one h2
      rw [map_add (f := _), hw0]; field_simp; ring
    rw [e1, AddChar.map_add_eq_mul, hpsi_int _ ((Formalism.UG.intL L).neg_mem hp) hpσ, mul_one]
  have hkey : ∀ b y, (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
      ψ (-((locH σ δ JS JT y (l b y) + σ (locH σ δ JS JT y (l b y))) / 2)) = ψ (-(w b y)) := by
    intro b y hya
    apply hPA
    · have h1 := GlobalTheory.T.vacuumPhase_sub_trace_mem_integers L σ δ hσv hδO n n' JS a (kf b) JT (E b) y hSJ hSJi hTJ hSD (hsk b).1 (hEi b).1 (hEi b).2.1
        (hkf b) (hkinv b) hya
      rw [(hsk b).2 n' JT y] at h1
      exact h1
    · exact (GlobalTheory.T.gram_hermitian_skewTrace_sigmaFixed L σ δ hσσ hδ.2 n' r JT (y * M) (Γf b) hT (hΓ b).1).2
  have hw0 : ∀ Γ0 ∈ gam0 σ ϖ e, ∀ y, (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
      δ * Matrix.trace (Γ0 * Φ y) ∈ Formalism.UG.intL L ∧ σ (δ * Matrix.trace (Γ0 * Φ y)) = δ * Matrix.trace (Γ0 * Φ y) :=
    fun Γ0 hΓ0 y hya => ⟨GlobalTheory.T.trace_skewHermitian_gram_integral_alt L ϖ σ δ hσv hδO n n' r JT a y M e Γ0 hTJ hya hD1 hΓ0,
      (GlobalTheory.T.gram_hermitian_skewTrace_sigmaFixed L σ δ hσσ hδ.2 n' r JT (y * M) Γ0 hT hΓ0.1).2⟩
  have hψ1 : ∀ s : L, s ∈ Formalism.UG.intL L → σ s = s → ψ s = 1 ∧ ψ (-s) = 1 := fun s hs hσs =>
    ⟨hpsi_int s hs hσs, hpsi_int _ ((Formalism.UG.intL L).neg_mem hs) (by rw [map_neg, hσs])⟩
  have hsplit : ∀ b b', ∃ Γ0 ∈ gam0 σ ϖ e, Γf (b + b') = Γ0 + Γf b + Γf b' := by
    intro b b'
    have h1 : (QuotientAddGroup.mk (Quotient.out b + Quotient.out b') : G ⧸ G0) = QuotientAddGroup.mk (Quotient.out (b + b')) := by
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
    have h3 := QuotientAddGroup.eq.mp h1
    refine ⟨((-(Quotient.out b + Quotient.out b') + Quotient.out (b + b') : G) : Matrix (Fin r) (Fin r) L),
      (AddSubgroup.mem_addSubgroupOf).mp h3, ?_⟩
    simp only [Γf, AddSubgroup.coe_add, AddSubgroup.coe_neg]; abel

  have hψne : ∀ z : L, ψ z ≠ 0 := fun z h0 => by
    have := AddChar.map_add_eq_mul ψ z (-z)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
    exact one_ne_zero this
  refine ⟨Y, hxY, fun y hy => (hHom y).mpr (hYa y hy), hYd, G ⧸ G0, inferInstance, Fintype.ofFinite _, b0, l,
    fun b => GlobalTheory.T.selfDual_one_add_skewHermitian_mul_lattice L σ hσv n JS a (kf b) (E b) hSJ hSD (hsk b).1 (hEint b) (hEi b).2.1 (hkf b) (hkinv b),
    fun b y hy => ⟨hlint b y (hYa y hy), y * (a : Matrix (Fin n) (Fin n) L), hYa y hy, ?_⟩,
    fun b u hu => ?_, fun b b' y hy => ?_, fun y hy => ?_⟩
  ·
    rw [hb0inv b, Matrix.mul_assoc, ← Matrix.mul_assoc (a : Matrix (Fin n) (Fin n) L), Units.mul_inv, Matrix.one_mul]
    simp only [l, Matrix.mul_sub, Matrix.mul_one]; abel
  ·
    obtain ⟨y, hy, hz⟩ := hYc u hu
    refine ⟨y, hy, ?_⟩
    set z := u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - y with hzdef
    have hza : ∀ i j, (z * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L := by
      intro i j
      have e1 : z * (a : Matrix (Fin n) (Fin n) L) = u - y * (a : Matrix (Fin n) (Fin n) L) := by
        rw [hzdef, Matrix.sub_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [e1]; exact (Formalism.UG.intL L).sub_mem (hu i j) (hYa y hy i j)
    have e2 : u * (((b0 b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - (y + l b y) =
        z + z * ((((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) := by
      rw [hb0inv b, hzdef]
      simp only [l, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]; abel
    rw [e2]
    exact (HoweDuality.intMat L n' n).add_mem hz (hlint b z hza)
  ·
    have hya := hYa y hy
    rw [hkey _ _ hya, hkey _ _ hya, hkey _ _ hya]
    obtain ⟨Γ0, hΓ0, hsum⟩ := hsplit b b'
    have e1 : -(w (b + b') y) = -(δ * Matrix.trace (Γ0 * Φ y)) + (-(w b y) + -(w b' y)) := by
      simp only [w, hsum, Matrix.add_mul, Matrix.trace_add]; ring
    obtain ⟨h0i, h0f⟩ := hw0 Γ0 hΓ0 y hya
    rw [e1, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, (hψ1 _ h0i h0f).2, one_mul]
  ·
    have hya := hYa y hy
    have hΔh : ∀ j k, σ ((Φ y - Φ x) j k) = (Φ y - Φ x) k j := by
      intro j k
      simp only [Matrix.sub_apply, map_sub]
      rw [(GlobalTheory.T.gram_hermitian_skewTrace_sigmaFixed L σ δ hσσ hδ.2 n' r JT (y * M) 0 hT (fun _ _ => by simp)).1 j k,
        (GlobalTheory.T.gram_hermitian_skewTrace_sigmaFixed L σ δ hσσ hδ.2 n' r JT (x * M) 0 hT (fun _ _ => by simp)).1 j k]
    have hwd : ∀ b, w b y - w b x = δ * Matrix.trace (Γf b * (Φ y - Φ x)) := by
      intro b; simp only [w, Matrix.mul_sub, Matrix.trace_sub]; ring
    have hfix : ∀ b, σ (δ * Matrix.trace (Γf b * (Φ y - Φ x))) = δ * Matrix.trace (Γf b * (Φ y - Φ x)) := by
      intro b
      rw [← hwd, map_sub, (GlobalTheory.T.gram_hermitian_skewTrace_sigmaFixed L σ δ hσσ hδ.2 n' r JT (y * M) (Γf b) hT (hΓ b).1).2,
        (GlobalTheory.T.gram_hermitian_skewTrace_sigmaFixed L σ δ hσσ hδ.2 n' r JT (x * M) (Γf b) hT (hΓ b).1).2]
    constructor
    · intro hg b
      rw [hkey _ _ hya, hkey _ _ hxa]
      have hb := GlobalTheory.T.gramDifference_entry_mem_uniformizerPow_integers L ϖ σ n n' r JT a x y M e hϖO hN hMint hD1 hg
      have hint : δ * Matrix.trace (Γf b * (Φ y - Φ x)) ∈ Formalism.UG.intL L := by
        refine Subring.mul_mem _ hδO ?_
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
        refine Subring.sum_mem _ fun k _ => Subring.sum_mem _ fun j _ => ?_
        show Valued.v (Γf b k j * (Φ y - Φ x) j k) ≤ 1
        calc Valued.v (Γf b k j * (Φ y - Φ x) j k) = Valued.v (Γf b k j) * Valued.v ((Φ y - Φ x) j k) := map_mul _ _ _
          _ ≤ Valued.v ϖ ^ max (e k) (e j) * Valued.v ((Φ y - Φ x) j k) := mul_le_mul_of_nonneg_right ((hΓ b).2 k j) zero_le'
          _ = Valued.v ((Φ y - Φ x) j k * ϖ ^ max (e j) (e k)) := by rw [map_mul, map_pow, max_comm, mul_comm]
          _ ≤ 1 := hb j k
      have e1 : -(w b y) = -(w b x) + -(w b y - w b x) := by ring
      rw [e1, AddChar.map_add_eq_mul, hwd, (hψ1 _ hint (hfix b)).2, mul_one]
    · intro hb
      have hb' : ∀ b, ψ (-(w b y)) = ψ (-(w b x)) := fun b => (hkey b y hya).symm.trans ((hb b).trans (hkey b x hxa))
      refine GlobalTheory.T.gramClassEq_of_sigmaHermitianForm_bounds L ϖ σ hσσ hσv hϖO n n' r JT a x y M e hTJ hT hN hxa hya hMint hD1 hD2 hD3
        (GlobalTheory.T.integral_of_traceCharPairing_skewHermitian L ϖ σ q δ ψ hU hδ hpsi_ne r e _ hΔh ?_)
      intro Γ hΓm
      let bb : G ⧸ G0 := QuotientAddGroup.mk (⟨Γ, hΓm⟩ : G)
      have hq : -(⟨Γ, hΓm⟩ : G) + Quotient.out bb ∈ G0 :=
        QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' bb).symm
      have hΓ0 : -Γ + Γf bb ∈ gam0 σ ϖ e := (AddSubgroup.mem_addSubgroupOf).mp hq
      have h1 : ψ (w bb y - w bb x) * ψ (-(w bb y)) = ψ (-(w bb y)) := by
        rw [← AddChar.map_add_eq_mul, show w bb y - w bb x + -(w bb y) = -(w bb x) by ring]
        exact (hb' bb).symm
      have h1' : ψ (w bb y - w bb x) = 1 := mul_right_cancel₀ (hψne _) (by rw [h1, one_mul])
      obtain ⟨hiy, hfy⟩ := hw0 _ hΓ0 y hya
      obtain ⟨hix, hfx⟩ := hw0 _ hΓ0 x hxa
      have hs : δ * Matrix.trace ((-Γ + Γf bb) * Φ y) - δ * Matrix.trace ((-Γ + Γf bb) * Φ x) ∈ Formalism.UG.intL L :=
        (Formalism.UG.intL L).sub_mem hiy hix
      have hsf : σ (δ * Matrix.trace ((-Γ + Γf bb) * Φ y) - δ * Matrix.trace ((-Γ + Γf bb) * Φ x)) =
          δ * Matrix.trace ((-Γ + Γf bb) * Φ y) - δ * Matrix.trace ((-Γ + Γf bb) * Φ x) := by
        rw [map_sub, hfy, hfx]
      have e2 : δ * Matrix.trace (Γ * (Φ y - Φ x)) = (w bb y - w bb x) +
          -(δ * Matrix.trace ((-Γ + Γf bb) * Φ y) - δ * Matrix.trace ((-Γ + Γf bb) * Φ x)) := by
        simp only [w, Matrix.mul_sub, Matrix.add_mul, Matrix.neg_mul, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_neg]
        ring
      rw [e2, AddChar.map_add_eq_mul, h1', (hψ1 _ hs hsf).2, one_mul]

end GlobalTheory.Hk3.GramSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGramClassRepsSelfDualLatticeGroupStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gramClass_reps_selfDualLattice_group : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    (Valued.v δ = 1 ∧ σ δ = -δ) → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
      (∀ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweG.HomA σ JS JT x y ↔
        ∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
      (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
        ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔
          ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) ∧
      (∀ w : Fin n → L, (∃ u v : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, v i ∈ Formalism.UG.intL L) ∧
          w = (a : Matrix (Fin n) (Fin n) L) *ᵥ u + v) ↔
        ∃ v : Fin n → L, ∃ w' : Fin n' → L, (∀ i, v i ∈ Formalism.UG.intL L) ∧ (∀ i, w' i ∈ Formalism.UG.intL L) ∧
          w = v + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') →
    ∃ Y : Finset (Matrix (Fin n') (Fin n) L), x ∈ Y ∧ (∀ y ∈ Y, GlobalTheory.Hk3.HoweG.HomA σ JS JT x y) ∧
      (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → y = y') ∧
      ∃ (B : Type) (_ : AddCommGroup B) (_ : Fintype B) (b0 : B → GL (Fin n) L)
        (l : B → Matrix (Fin n') (Fin n) L → Matrix (Fin n') (Fin n) L),
        (∀ b, GlobalTheory.Hk3.HoweG.SelfDual σ JS (b0 b)) ∧
        (∀ b, ∀ y ∈ Y, l b y ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n ∧
          ∃ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
            y + l b y = u * (((b0 b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∧
        (∀ b, ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
          ∃ y ∈ Y, u * (((b0 b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - (y + l b y) ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n) ∧
        (∀ b b', ∀ y ∈ Y, ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l (b + b') y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l (b + b') y))) / 2)) = ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l b y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l b y))) / 2)) * ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l b' y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l b' y))) / 2))) ∧
        (∀ y ∈ Y, GlobalTheory.Hk3.HoweG.GramEq σ JT x y ↔ ∀ b, ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l b y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l b y))) / 2)) = ψ (-((GlobalTheory.Hk3.locH σ δ JS JT x (l b x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (l b x))) / 2))) := by
  first | exact @GlobalTheory.Hk3.GramSep.gram_class_family | exact GlobalTheory.Hk3.GramSep.gram_class_family | (intros; apply GlobalTheory.Hk3.GramSep.gram_class_family <;> assumption)
end
