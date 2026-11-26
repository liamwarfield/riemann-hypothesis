module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionModuleStructure
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.TorCls.OpenP

theorem mem_range_map_of_entries {R : Type} [CommRing R] (S : Subring R) {n : ℕ} (X : GL (Fin n) R)
    (h1 : ∀ i j, (X : Matrix (Fin n) (Fin n) R) i j ∈ S)
    (h2 : ∀ i j, ((X⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ S) :
    X ∈ (GeneralLinearGroup.map S.subtype).range := by
  let A : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h2 i j⟩
  have hA : A.map S.subtype = (X : Matrix (Fin n) (Fin n) R) := by ext i j; rfl
  have hB : B.map S.subtype = ((X⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by ext i j; rfl
  have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) S => M.map S.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hAB : A * B = 1 := inj (by
    simp only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero S.subtype) (map_one S.subtype)]
    exact X.mul_inv)
  have hBA : B * A = 1 := inj (by
    simp only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero S.subtype) (map_one S.subtype)]
    exact X.inv_mul)
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

variable (p : ℕ) [Fact p.Prime]

theorem exists_pow_mul_mem (L : IntermediateField ℚ_[p] (PadicAlgCl p)) (x : L) :
    ∃ N : ℕ, (((p : L) ^ N * x : L) : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p := by
  have hp : ‖(p : PadicAlgCl p)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (‖(x : PadicAlgCl p)‖ + 1) by positivity) hp
  refine ⟨N, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.2 ?_⟩
  have e : (((p : L) ^ N * x : L) : PadicAlgCl p) = (p : PadicAlgCl p) ^ N * (x : PadicAlgCl p) := by
    simp
  rw [e, norm_mul, norm_pow]
  have h0 : 0 ≤ ‖(x : PadicAlgCl p)‖ := norm_nonneg _
  calc ‖(p : PadicAlgCl p)‖ ^ N * ‖(x : PadicAlgCl p)‖ ≤ 1 / (‖(x : PadicAlgCl p)‖ + 1) * (‖(x : PadicAlgCl p)‖ + 1) :=
        mul_le_mul hN.le (by linarith) h0 (by positivity)
    _ = 1 := by field_simp

end GlobalTheory.TorCls.OpenP

namespace GlobalTheory.TorCls.OpenP
variable (p : ℕ) [Fact p.Prime]

theorem natCast_pow_mem_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r N : ℕ) :
    (p : KQ p K r) ^ N ∈ intKQ p K r :=
  pow_mem (natCast_mem _ p) N

theorem inclK_mem_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (x : K)
    (h : (x : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p) : inclK p K r x ∈ intKQ p K r :=
  Subring.subset_closure (Or.inl ⟨⟨x, h⟩, rfl⟩)

theorem inclQ_mem_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (x : Qr p r)
    (h : (x : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p) : inclQ p K r x ∈ intKQ p K r :=
  Subring.subset_closure (Or.inr ⟨⟨x, h⟩, rfl⟩)

theorem tmul_eq_inclK_mul_inclQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (a : K) (b : Qr p r) :
    (show KQ p K r from a ⊗ₜ[ℚ_[p]] b) = inclK p K r a * inclQ p K r b := by
  change a ⊗ₜ[ℚ_[p]] b = (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) * ((1 : K) ⊗ₜ[ℚ_[p]] b)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem exists_pow_mul_mem_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (x : KQ p K r) :
    ∃ N : ℕ, (p : KQ p K r) ^ N * x ∈ intKQ p K r := by
  refine TensorProduct.induction_on (R := ℚ_[p]) (M := K) (N := Qr p r)
    (motive := fun y : K ⊗[ℚ_[p]] Qr p r => ∃ N : ℕ, (p : KQ p K r) ^ N * (show KQ p K r from y) ∈ intKQ p K r) x
    ⟨0, ?_⟩ ?_ ?_
  · change (p : KQ p K r) ^ 0 * (0 : KQ p K r) ∈ intKQ p K r
    rw [mul_zero]; exact zero_mem _
  · intro a b
    obtain ⟨N₁, h₁⟩ := exists_pow_mul_mem p K a
    obtain ⟨N₂, h₂⟩ := exists_pow_mul_mem p (Qr p r) b
    refine ⟨N₁ + N₂, ?_⟩
    rw [tmul_eq_inclK_mul_inclQ]
    have e : (p : KQ p K r) ^ (N₁ + N₂) * (inclK p K r a * inclQ p K r b) =
        inclK p K r ((p : K) ^ N₁ * a) * inclQ p K r ((p : Qr p r) ^ N₂ * b) := by
      rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, pow_add]; ring
    rw [e]
    exact mul_mem (inclK_mem_intKQ p K r _ h₁) (inclQ_mem_intKQ p K r _ h₂)
  · rintro x y ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨N + M, ?_⟩
    change (p : KQ p K r) ^ (N + M) * ((show KQ p K r from x) + (show KQ p K r from y)) ∈ intKQ p K r
    generalize (show KQ p K r from x) = x' at hN ⊢
    generalize (show KQ p K r from y) = y' at hM ⊢
    have e : (p : KQ p K r) ^ (N + M) * (x' + y') =
        (p : KQ p K r) ^ M * ((p : KQ p K r) ^ N * x') + (p : KQ p K r) ^ N * ((p : KQ p K r) ^ M * y') := by
      ring
    rw [e]
    exact add_mem (mul_mem (natCast_pow_mem_intKQ p K r M) hN) (mul_mem (natCast_pow_mem_intKQ p K r N) hM)

theorem exists_pow_mul_entries_mem (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (KQ p K r)) :
    ∃ N : ℕ, ∀ i j, (p : KQ p K r) ^ N * A i j ∈ intKQ p K r := by
  choose f hf using exists_pow_mul_mem_intKQ p K r
  refine ⟨Finset.univ.sup fun ij : Fin n × Fin n => f (A ij.1 ij.2), fun i j => ?_⟩
  have hle : f (A i j) ≤ Finset.univ.sup fun ij : Fin n × Fin n => f (A ij.1 ij.2) :=
    Finset.le_sup (f := fun ij : Fin n × Fin n => f (A ij.1 ij.2)) (Finset.mem_univ (i, j))
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, add_comm, pow_add, mul_assoc]
  exact mul_mem (natCast_pow_mem_intKQ p K r _) (hf _)

end GlobalTheory.TorCls.OpenP

namespace GlobalTheory.TorCls.OpenP
variable (p : ℕ) [Fact p.Prime]

theorem norm_p_pos : 0 < ‖(p : PadicAlgCl p)‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)

theorem exists_conj_entries_mem (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) {n : ℕ}
    (R : GL (Fin n) (KQ p K r)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ M : Matrix (Fin n) (Fin n) K,
      (∀ i j, ‖(((M - 1) i j : K) : PadicAlgCl p)‖ < ε) →
      ∀ i l, (((R⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) * M.map (inclK p K r) *
        (R : Matrix (Fin n) (Fin n) (KQ p K r))) i l ∈ intKQ p K r := by
  obtain ⟨N₁, h₁⟩ := exists_pow_mul_entries_mem p K r (R : Matrix (Fin n) (Fin n) (KQ p K r))
  obtain ⟨N₂, h₂⟩ := exists_pow_mul_entries_mem p K r ((R⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r))
  refine ⟨‖(p : PadicAlgCl p)‖ ^ (N₁ + N₂), pow_pos (norm_p_pos p) _, fun M hM i l => ?_⟩
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hsplit : M.map (inclK p K r) = 1 + (M - 1).map (inclK p K r) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, map_sub]
    split_ifs <;> simp
  rw [hsplit, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul]
  refine add_mem ?_ ?_
  · rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [Matrix.mul_apply]
  refine sum_mem fun k _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine sum_mem fun j _ => ?_
  set B := (M - 1) j k with hB
  set b : K := ((p : K) ^ (N₁ + N₂))⁻¹ * B with hb
  have hBb : B = (p : K) ^ (N₁ + N₂) * b := by rw [hb, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp0), one_mul]
  have hbint : (b : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p := by
    rw [ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff]
    have h := hM j k
    rw [← hB, hBb] at h
    have e : (((p : K) ^ (N₁ + N₂) * b : K) : PadicAlgCl p) = (p : PadicAlgCl p) ^ (N₁ + N₂) * (b : PadicAlgCl p) := by
      simp
    rw [e, norm_mul, norm_pow] at h
    have hpos := pow_pos (norm_p_pos p) (N₁ + N₂)
    by_contra hc
    push_neg at hc
    nlinarith
  have e2 : ((R⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j * ((M - 1).map (inclK p K r)) j k *
      (R : Matrix (Fin n) (Fin n) (KQ p K r)) k l =
      ((p : KQ p K r) ^ N₂ * ((R⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j) *
        inclK p K r b * ((p : KQ p K r) ^ N₁ * (R : Matrix (Fin n) (Fin n) (KQ p K r)) k l) := by
    rw [Matrix.map_apply, ← hB, hBb, map_mul, map_pow, map_natCast, pow_add]; ring
  rw [e2]
  exact mul_mem (mul_mem (h₂ i j) (inclK_mem_intKQ p K r b hbint)) (h₁ k l)

end GlobalTheory.TorCls.OpenP

namespace GlobalTheory.TorCls.OpenP

theorem scalar_one_entry {R : Type} [CommRing R] (u : Rˣ) (i j : Fin 1) :
    ((GeneralLinearGroup.scalar (Fin 1) u : GL (Fin 1) R) : Matrix (Fin 1) (Fin 1) R) i j = (u : R) := by
  fin_cases i; fin_cases j; simp [GeneralLinearGroup.scalar]

theorem psiP_fst_mem (p : ℕ) [Fact p.Prime] (G : HTGroup p) (z : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)
    (h1 : ‖(z.2 : ℚ_[p])‖ ≤ 1) (h2 : ‖((z.2⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1) :
    (psiP G z).1 ∈ GlobalTheory.LKLoc.Kint p (Q0 p) 1 1 := by
  have hfst : (psiP G z).1 = GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p 1)).toMonoidHom z.2) := rfl
  have hmem : ∀ a : ℚ_[p], ‖a‖ ≤ 1 → algebraMap ℚ_[p] (Qr p 1) a ∈ GlobalTheory.LKLoc.intR p (Q0 p) 1 := by
    intro a ha
    show ((algebraMap ℚ_[p] (Qr p 1) a : Qr p 1) : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p
    rw [ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff, IntermediateField.coe_algebraMap_apply, PadicAlgCl.norm_extends]
    exact ha
  refine mem_range_map_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [hfst, scalar_one_entry]; exact hmem _ h1
  · rw [hfst, ← map_inv, scalar_one_entry, ← map_inv]; exact hmem _ h2

theorem openp : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r₂ : Gr G 1),
    letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C);
    ∃ O : Set ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, r₂⁻¹ * psiP G z * r₂ ∈ KHT p G.m G.n 1 G.Fw := by
  intro p _ G r₂
  letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C)
  haveI : IsModuleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) := ⟨rfl⟩
  choose ε hε hM using fun w : Fin G.m => exists_conj_entries_mem p (G.Fw w) 1 (r₂.2 w)
  let e : ∀ (w : Fin G.m) (i j : Fin G.n), ℚ_[p] ⊗[ℚ] G.C → PadicAlgCl p :=
    fun w i j g => (((G.locW w g - 1) i j : G.Fw w) : PadicAlgCl p)
  have hcont : ∀ w i j, Continuous (e w i j) := by
    intro w i j
    let L : ℚ_[p] ⊗[ℚ] G.C →ₗ[ℚ_[p]] PadicAlgCl p :=
      (G.Fw w).val.toLinearMap ∘ₗ (Matrix.entryLinearMap ℚ_[p] (G.Fw w) i j) ∘ₗ (G.locW w).toLinearMap
    have he : e w i j = fun g => L g - (((1 : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) i j : G.Fw w) : PadicAlgCl p) := by
      funext g; simp [e, L, Matrix.sub_apply]
    rw [he]
    exact (IsModuleTopology.continuous_of_linearMap L).sub continuous_const
  have hent : ∀ (w : Fin G.m) (z' : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ), (∀ i j, ‖e w i j (z'.1 : ℚ_[p] ⊗[ℚ] G.C)‖ < ε w) →
      ∀ i l, (((r₂⁻¹ * psiP G z' * r₂).2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)) i l ∈ intKQ p (G.Fw w) 1 := by
    intro w z' h i l
    have hv : (((r₂⁻¹ * psiP G z' * r₂).2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)) =
        (((r₂.2 w)⁻¹ : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)) *
          (G.locW w (z'.1 : ℚ_[p] ⊗[ℚ] G.C)).map (inclK p (G.Fw w) 1) * ((r₂.2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)) := rfl
    rw [hv]
    exact hM w _ h i l
  refine ⟨{z | ‖(z.2 : ℚ_[p])‖ ≤ 1 ∧ ‖((z.2⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 ∧
      ∀ w i j, ‖e w i j (z.1 : ℚ_[p] ⊗[ℚ] G.C)‖ < ε w ∧ ‖e w i j (((z.1)⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C)‖ < ε w},
    ?_, ?_, ?_⟩
  · have hball : IsOpen {x : ℚ_[p] | ‖x‖ ≤ 1} := by
      have := IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) (one_ne_zero : (1 : ℝ) ≠ 0)
      simpa [Metric.closedBall, dist_zero_right] using this
    simp only [Set.setOf_and, Set.setOf_forall]
    refine (hball.preimage ((Units.continuous_val (M := ℚ_[p])).comp (continuous_snd (X := (ℚ_[p] ⊗[ℚ] G.C)ˣ) (Y := ℚ_[p]ˣ)))).inter
      ((hball.preimage ((Units.continuous_coe_inv (M := ℚ_[p])).comp (continuous_snd (X := (ℚ_[p] ⊗[ℚ] G.C)ˣ) (Y := ℚ_[p]ˣ)))).inter ?_)
    refine isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact (isOpen_lt (continuous_norm.comp ((hcont w i j).comp ((Units.continuous_val (M := ℚ_[p] ⊗[ℚ] G.C)).comp continuous_fst)))
      continuous_const).inter
      (isOpen_lt (continuous_norm.comp ((hcont w i j).comp ((Units.continuous_coe_inv (M := ℚ_[p] ⊗[ℚ] G.C)).comp continuous_fst)))
      continuous_const)
  · refine ⟨by simp, by simp, fun w i j => ⟨?_, ?_⟩⟩ <;> simp [e, hε w]
  · rintro z ⟨h1, h2, h3⟩
    refine Subgroup.mem_prod.2 ⟨?_, ?_⟩
    · have hk := psiP_fst_mem p G z h1 h2
      have := (normal_of_gl_one (GlobalTheory.LKLoc.Kint p (Q0 p) 1 1)).conj_mem _ hk r₂.1⁻¹
      simpa using this
    · refine (Subgroup.mem_pi _).2 fun w _ => ?_
      refine mem_range_map_of_entries _ _ (hent w z fun i j => (h3 w i j).1) ?_
      have hinv : ((r₂⁻¹ * psiP G z * r₂).2 w)⁻¹ = (r₂⁻¹ * psiP G z⁻¹ * r₂).2 w := by
        have hg : (r₂⁻¹ * psiP G z * r₂)⁻¹ = r₂⁻¹ * psiP G z⁻¹ * r₂ := by rw [map_inv]; group
        rw [show ((r₂⁻¹ * psiP G z * r₂).2 w)⁻¹ = ((r₂⁻¹ * psiP G z * r₂)⁻¹).2 w from rfl, hg]
      rw [hinv]
      exact hent w z⁻¹ fun i j => (h3 w i j).2

end GlobalTheory.TorCls.OpenP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyMapBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyMapBaseChange
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.HilbBaseChange

open Module TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem homogeneousComponent_map_algebraMap {σ K L : Type} [Field K] [Field L] [Algebra K L] (n : ℕ) (p : MvPolynomial σ K) :
    homogeneousComponent n (MvPolynomial.map (algebraMap K L) p) =
      MvPolynomial.map (algebraMap K L) (homogeneousComponent n p) := by
  ext d
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem homogeneousComponent_mem_span_map_homogeneous {σ K L : Type} [Field K] [Field L] [Algebra K L]
    (P : Ideal (MvPolynomial σ K)) (hP : ∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P)
    {g : MvPolynomial σ L}
    (hg : g ∈ Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (P : Set (MvPolynomial σ K))))
    (n : ℕ) :
    homogeneousComponent n g ∈ Submodule.span L ((MvPolynomial.map (algebraMap K L)) ''
      ((P.restrictScalars K ⊓ homogeneousSubmodule σ K n : Submodule K (MvPolynomial σ K)) :
        Set (MvPolynomial σ K))) := by
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, hq, rfl⟩ := hy
    rw [homogeneousComponent_map_algebraMap]
    exact Submodule.subset_span ⟨_, ⟨hP q hq n, homogeneousComponent_mem n q⟩, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem mem_span_image_of_mem_ideal_map {σ K L : Type} [Field K] [Field L] [Algebra K L]
    (P : Ideal (MvPolynomial σ K)) {g : MvPolynomial σ L}
    (hg : g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial σ K →+* MvPolynomial σ L)) :
    g ∈ Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (P : Set (MvPolynomial σ K))) := by
  obtain ⟨M, hM⟩ : ∃ M : Submodule L (MvPolynomial σ L),
      M = Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (P : Set (MvPolynomial σ K))) :=
    ⟨_, rfl⟩
  rw [← hM]
  have hX : ∀ (i : σ) (x : MvPolynomial σ L), x ∈ M → X i * x ∈ M := by
    intro i x hx
    rw [hM] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨q, hq, rfl⟩ := hy
      refine Submodule.subset_span ⟨X i * q, P.mul_mem_left _ hq, ?_⟩
      simp
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  have hmul : ∀ (a x : MvPolynomial σ L), x ∈ M → a * x ∈ M := by
    intro a x hx
    induction a using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.C_mul']; exact M.smul_mem c hx
    | add p q hp hq => rw [add_mul]; exact M.add_mem hp hq
    | mul_X p i hp =>
      rw [show p * X i * x = X i * (p * x) by ring]
      exact hX i _ hp
  induction hg using Submodule.span_induction with
  | mem y hy => rw [hM]; exact Submodule.subset_span hy
  | zero => exact M.zero_mem
  | add y z _ _ hy hz => exact M.add_mem hy hz
  | smul a y _ hy => exact hmul a y hy

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem decompose_coe_eq_homogeneousComponent {σ L : Type} [Field L]
    (g : MvPolynomial σ L) (n : ℕ) :
    letI := MvPolynomial.gradedAlgebra (σ := σ) (R := L)
    (((DirectSum.decompose (homogeneousSubmodule σ L)) g) n : MvPolynomial σ L) =
      homogeneousComponent n g := by
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := L)
  conv_lhs => rw [← sum_homogeneousComponent g]
  rw [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  by_cases hn : n ∈ Finset.range (g.totalDegree + 1)
  · rw [Finset.sum_eq_single n]
    · exact DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem n g)
    · intro i _ hi
      exact DirectSum.decompose_of_mem_ne _ (homogeneousComponent_mem i g) hi
    · intro h; exact absurd hn h
  · rw [homogeneousComponent_eq_zero]
    · refine Finset.sum_eq_zero fun i hi => ?_
      exact DirectSum.decompose_of_mem_ne _ (homogeneousComponent_mem i g) (by rintro rfl; exact hn hi)
    · simp at hn; omega

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem linearIndependent_map_algebraMap {σ K L : Type} [Field K] [Field L] [Algebra K L] {ι : Type} {v : ι → MvPolynomial σ K}
    (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => MvPolynomial.map (algebraMap K L) (v i)) := by
  have h := Module.Flat.linearIndependent_one_tmul (S := L) hv
  have h2 := h.map' (algebraTensorAlgEquiv K L).toLinearEquiv.toLinearMap
    (algebraTensorAlgEquiv K L).toLinearEquiv.ker
  have he : (fun i => MvPolynomial.map (algebraMap K L) (v i)) =
      (algebraTensorAlgEquiv K L).toLinearEquiv.toLinearMap ∘ fun i => (1 : L) ⊗ₜ[K] v i := by
    funext i
    simp [algebraTensorAlgEquiv_tmul]
  rw [he]
  exact h2

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem finrank_span_map_algebraMap_eq {σ K L : Type} [Field K] [Field L] [Algebra K L]
    (W : Submodule K (MvPolynomial σ K)) [FiniteDimensional K W] :
    Module.finrank L (Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (W : Set (MvPolynomial σ K)))) =
      Module.finrank K W := by
  let b := Module.finBasis K W
  let v : Fin (Module.finrank K W) → MvPolynomial σ L :=
    fun i => MvPolynomial.map (algebraMap K L) (b i : MvPolynomial σ K)
  have hli : LinearIndependent L v :=
    linearIndependent_map_algebraMap (b.linearIndependent.map' W.subtype (Submodule.ker_subtype W))
  have hspan : Submodule.span L (Set.range v) =
      Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (W : Set (MvPolynomial σ K))) := by
    apply le_antisymm
    · refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨_, (b i).2, rfl⟩
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨w, hw, rfl⟩
      have hw' : (⟨w, hw⟩ : W) ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
      have key : ∀ x : W, x ∈ Submodule.span K (Set.range b) →
          MvPolynomial.map (algebraMap K L) (x : MvPolynomial σ K) ∈
            (Submodule.span L (Set.range v)).restrictScalars K := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simp
        | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
        | smul c y _ hy =>
          have : MvPolynomial.map (algebraMap K L) ((c • y : W) : MvPolynomial σ K) =
              c • MvPolynomial.map (algebraMap K L) (y : MvPolynomial σ K) := by
            simp [MvPolynomial.smul_eq_C_mul, Algebra.smul_def]
          rw [this]
          exact Submodule.smul_mem _ c hy
      exact key _ hw'
  rw [← hspan, finrank_span_eq_card hli, Fintype.card_fin]


open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem _root_.GlobalTheory.HilbBaseChange.idealHilbertPoly_map : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (N : ℕ) (P : Ideal (MvPolynomial (Fin N) K)), (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → (∀ g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L), ∀ n : ℕ, homogeneousComponent n g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) ∧ _root_.GlobalTheory.idealHilbertPoly (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) = _root_.GlobalTheory.idealHilbertPoly P := by
  intro K L _ _ _ N P hP
  have hW : ∀ n : ℕ,
      (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)).restrictScalars L ⊓
          homogeneousSubmodule (Fin N) L n =
        Submodule.span L ((MvPolynomial.map (algebraMap K L)) ''
          ((P.restrictScalars K ⊓ homogeneousSubmodule (Fin N) K n : Submodule K (MvPolynomial (Fin N) K)) :
            Set (MvPolynomial (Fin N) K))) := by
    intro n
    apply le_antisymm
    · rintro g ⟨hg1, hg2⟩
      have := homogeneousComponent_mem_span_map_homogeneous P hP (mem_span_image_of_mem_ideal_map P hg1) n
      rwa [homogeneousComponent_of_mem hg2, if_pos rfl] at this
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨w, ⟨hw1, hw2⟩, rfl⟩
      exact ⟨Ideal.mem_map_of_mem _ hw1,
        (mem_homogeneousSubmodule _ _).2 (((mem_homogeneousSubmodule _ _).1 hw2).map _)⟩
  have hA : ∀ g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L),
      ∀ n : ℕ, homogeneousComponent n g ∈
        P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) := by
    intro g hg n
    have h := homogeneousComponent_mem_span_map_homogeneous P hP (mem_span_image_of_mem_ideal_map P hg) n
    rw [← hW n] at h
    exact h.1
  refine ⟨hA, ?_⟩
  have hhomP : Ideal.IsHomogeneous (homogeneousSubmodule (Fin N) K) P := by
    intro i r hr
    rw [decompose_coe_eq_homogeneousComponent]
    exact hP r hr i
  have hhomQ : Ideal.IsHomogeneous (homogeneousSubmodule (Fin N) L)
      (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) := by
    intro i r hr
    rw [decompose_coe_eq_homogeneousComponent]
    exact hA r hr i
  have hdim : ∀ n : ℕ,
      Module.finrank L (_root_.GlobalTheory.quotPiece
        (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) (n : ℤ)) =
      Module.finrank K (_root_.GlobalTheory.quotPiece P (n : ℤ)) := by
    intro n
    have h1 := _root_.GlobalTheory.finrank_quotPiece_add
      (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) n
    have h2 := _root_.GlobalTheory.finrank_quotPiece_add P n
    rw [hW n, finrank_span_map_algebraMap_eq, _root_.GlobalTheory.ProjCut.finrank_homogeneousSubmodule] at h1
    rw [_root_.GlobalTheory.ProjCut.finrank_homogeneousSubmodule] at h2
    omega
  obtain ⟨n₀, hn₀⟩ := ((_root_.GlobalTheory.eventually_finrank_quotPiece hhomQ).and
    (_root_.GlobalTheory.eventually_finrank_quotPiece hhomP)).exists_forall_of_atTop
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((m + n₀ : ℕ) : ℚ)) ?_ ?_
  · intro a b h
    simpa using h
  · intro m
    obtain ⟨h1, h2⟩ := hn₀ (m + n₀) (by omega)
    simp only [Set.mem_setOf_eq]
    rw [← h1, ← h2, hdim]

end GlobalTheory.HilbBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyMapBaseChangeStatement
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealQuotientHilbertPoly_map_baseChange : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (N : ℕ) (P : Ideal (MvPolynomial (Fin N) K)), (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → (∀ g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L), ∀ n : ℕ, homogeneousComponent n g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) ∧ GlobalTheory.idealHilbertPoly (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) = GlobalTheory.idealHilbertPoly P := by
  first | exact @GlobalTheory.HilbBaseChange.idealHilbertPoly_map | exact GlobalTheory.HilbBaseChange.idealHilbertPoly_map | (intros; apply GlobalTheory.HilbBaseChange.idealHilbertPoly_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormGenericHyperplaneSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormGenericHyperplaneSection
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.ChowSpec

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial

def lastSubst {A : Type} [CommRing A] {N : ℕ} (D : ℕ) (t : Fin N → A) :
    Fin (D + 1) × Fin N → MvPolynomial (Fin D × Fin N) A :=
  fun v => Fin.lastCases (motive := fun _ => MvPolynomial (Fin D × Fin N) A)
    (C (t v.2)) (fun i => X (i, v.2)) v.1

set_option autoImplicit false in
open MvPolynomial Filter in
open scoped ENNReal in
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial in
@[simp] theorem _root_.GlobalTheory.ChowSpec.lastSubst_last {A : Type} [CommRing A] {N : ℕ} (D : ℕ)
    (t : Fin N → A) (j : Fin N) : _root_.GlobalTheory.ChowSpec.lastSubst D t (Fin.last D, j) = C (t j) := by
  simp [_root_.GlobalTheory.ChowSpec.lastSubst]

set_option autoImplicit false in
open MvPolynomial Filter in
open scoped ENNReal in
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial in
@[simp] theorem _root_.GlobalTheory.ChowSpec.lastSubst_castSucc {A : Type} [CommRing A] {N : ℕ} (D : ℕ)
    (t : Fin N → A) (i : Fin D) (j : Fin N) :
    _root_.GlobalTheory.ChowSpec.lastSubst D t (i.castSucc, j) = X (i, j) := by
  simp [_root_.GlobalTheory.ChowSpec.lastSubst]

def lastEquiv (K : Type) [CommRing K] (N D : ℕ) :
    MvPolynomial (Fin (D + 1) × Fin N) K ≃+* MvPolynomial (Fin D × Fin N) (MvPolynomial (Fin N) K) :=
  RingEquiv.ofRingHom
    (aeval (R := K) (lastSubst D (X : Fin N → MvPolynomial (Fin N) K))).toRingHom
    (eval₂Hom (aeval (R := K) (fun j => X (Fin.last D, j))).toRingHom
      (fun v => X (v.1.castSucc, v.2)))
    (by
      refine MvPolynomial.ringHom_ext' (MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_))
        (fun v => ?_) <;> simp)
    (by
      refine MvPolynomial.ringHom_ext (fun r => by simp) ?_
      rintro ⟨i, j⟩
      refine Fin.lastCases ?_ (fun i => ?_) i <;> simp)

set_option autoImplicit false in
open MvPolynomial Filter in
open scoped ENNReal in
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial in
private theorem isWeightedHomogeneous_aeval_of_forall {R S σ τ Γ Δ : Type} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [AddCommMonoid Γ] [AddCommMonoid Δ] {w : σ → Γ}
    {w' : τ → Δ} (g : Γ →+ Δ) {p : MvPolynomial σ R} {m : Γ}
    (hp : IsWeightedHomogeneous w p m) (φ : σ → MvPolynomial τ S)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ v) (g (w v))) :
    IsWeightedHomogeneous w' (aeval φ p) (g m) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [p.as_sum, map_sum, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun s hs => ?_
  rw [mem_weightedHomogeneousSubmodule, aeval_monomial, Finsupp.prod]
  have hw : Finsupp.weight w s = m := hp (mem_support_iff.mp hs)
  have hm : g m = 0 + ∑ v ∈ s.support, s v • g (w v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [zero_add, ← hw, Finsupp.weight_apply, Finsupp.sum, map_sum]
    simp [map_nsmul]
  rw [hm, MvPolynomial.algebraMap_apply]
  exact (isWeightedHomogeneous_C w' _).mul
    (IsWeightedHomogeneous.prod _ _ _ fun v _ => (hφ v).pow _)


set_option autoImplicit false in
open MvPolynomial Filter in
open scoped ENNReal in
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial in
theorem _root_.GlobalTheory.ChowSpec.exists_isChowFormInt_generic_section : ∀ (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K)) (D δ : ℕ) (f : MvPolynomial (Fin (D + 1 + 1) × Fin N) K), (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → _root_.GlobalTheory.ChowHt.IsChowFormInt P (D + 1) δ f → ∃ f' : MvPolynomial (Fin (D + 1) × Fin N) L, _root_.GlobalTheory.ChowHt.IsChowFormInt (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔ Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L)}) D δ f' := by
  intro K L _ _ N _ _ _ _ P D δ f hP hf
  set t : Fin N → L := fun j => algebraMap (MvPolynomial (Fin N) K) L (X j) with ht
  set φ := _root_.GlobalTheory.ChowSpec.lastSubst (D + 1) t with hφ
  set f' : MvPolynomial (Fin (D + 1) × Fin N) L := aeval (R := K) φ f with hf'
  have hfhom : _root_.GlobalTheory.Chow.IsBlockHomogeneous f (fun _ => δ) :=
    _root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block.1 hf.homog
  have hf'hom : _root_.GlobalTheory.Chow.IsBlockHomogeneous f' (fun _ => δ) := by
    unfold _root_.GlobalTheory.Chow.IsBlockHomogeneous at hfhom ⊢
    let g : (Fin (D + 1 + 1) → ℕ) →+ (Fin (D + 1) → ℕ) :=
      { toFun := fun a i => a i.castSucc, map_zero' := rfl, map_add' := fun _ _ => rfl }
    refine isWeightedHomogeneous_aeval_of_forall (S := L) g hfhom φ ?_
    rintro ⟨i, j⟩
    induction i using Fin.lastCases with
    | last =>
      have hg : g (_root_.GlobalTheory.Chow.blockWeight (Fin.last (D + 1), j)) = 0 := by
        funext i
        simp [g, _root_.GlobalTheory.Chow.blockWeight, Fin.castSucc_ne_last]
      rw [hφ, _root_.GlobalTheory.ChowSpec.lastSubst_last, hg]
      exact isWeightedHomogeneous_C _ _
    | cast i =>
      have hg : g (_root_.GlobalTheory.Chow.blockWeight (i.castSucc, j)) = _root_.GlobalTheory.Chow.blockWeight (i, j) := by
        funext i'
        simp [g, _root_.GlobalTheory.Chow.blockWeight, Pi.single_apply]
      rw [hφ, _root_.GlobalTheory.ChowSpec.lastSubst_castSucc, hg]
      exact isWeightedHomogeneous_X _ _ _
  refine ⟨f', _root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block.2 hf'hom, ?_, ?_⟩
  · have hkey : MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)
        (_root_.GlobalTheory.ChowSpec.lastEquiv K N (D + 1) f) = f' := by
      rw [hf']
      change ((MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)).comp
        (_root_.GlobalTheory.ChowSpec.lastEquiv K N (D + 1)).toRingHom) f = (aeval φ).toRingHom f
      congr 1
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
      · simp [_root_.GlobalTheory.ChowSpec.lastEquiv, MvPolynomial.algebraMap_apply,
          IsScalarTower.algebraMap_apply K (MvPolynomial (Fin N) K) L]
      · rcases v with ⟨i, j⟩
        induction i using Fin.lastCases <;> simp [_root_.GlobalTheory.ChowSpec.lastEquiv, hφ, ht]
    set F := _root_.GlobalTheory.ChowSpec.lastEquiv K N (D + 1) f with hF
    have hFirr : Irreducible F :=
      (MulEquiv.irreducible_iff (_root_.GlobalTheory.ChowSpec.lastEquiv K N (D + 1))).2
        hf.irred
    have hF0 : F ≠ 0 := hFirr.ne_zero
    have hFprime : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.1 hFirr
    have hδ : 0 < δ := by
      rcases Nat.eq_zero_or_pos δ with h | h
      · exfalso
        subst h
        have hh := hfhom.isHomogeneous
        simp only [Finset.sum_const_zero] at hh
        have hf0 := hf.ne_zero
        have hC : f = C (AddMonoidAlgebra.coeff f 0) :=
          (totalDegree_eq_zero_iff_eq_C).1 (by simpa using hh.totalDegree hf0)
        have hc : AddMonoidAlgebra.coeff f 0 ≠ 0 := fun h0 => hf0 (by rw [hC, h0, C_0])
        apply hf.irred.not_isUnit
        rw [hC]
        exact hc.isUnit.map C
      · exact h
    have hf'0 : f' ≠ 0 := by
      rw [← hkey]
      exact fun h => hF0 ((map_eq_zero_iff _
        (MvPolynomial.map_injective _ (IsFractionRing.injective (MvPolynomial (Fin N) K) L))).1 h)
    have hnotunit : ¬ IsUnit f' := by
      intro hu
      obtain ⟨r, hr, hfr⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 hu
      have hh := hf'hom.isHomogeneous
      rw [hfr] at hh
      have h0 := hh (show AddMonoidAlgebra.coeff (C r) 0 ≠ 0 by simpa using hr.ne_zero)
      simp at h0
      omega
    have hdisj : Disjoint ((Submonoid.map (C : MvPolynomial (Fin N) K →+*
        MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K))
          (nonZeroDivisors (MvPolynomial (Fin N) K))) :
            Set (MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K)))
        (↑(Ideal.span {F}) : Set (MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K))) := by
      rw [Set.disjoint_left]
      rintro _ ⟨s, hs, rfl⟩ hmem
      obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.1 hmem
      apply hnotunit
      have hs0 : algebraMap (MvPolynomial (Fin N) K) L s ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
      have hmapped := congrArg (MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)) hg
      rw [map_mul, hkey, map_C] at hmapped
      exact isUnit_of_mul_isUnit_right (hmapped ▸ hs0.isUnit.map C)
    have hprime := IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.map (C : MvPolynomial (Fin N) K →+*
        MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K))
          (nonZeroDivisors (MvPolynomial (Fin N) K)))
      (MvPolynomial (Fin (D + 1) × Fin N) L) (Ideal.span {F})
      ((Ideal.span_singleton_prime hF0).2 hFprime) hdisj
    rw [Ideal.map_span, Set.image_singleton] at hprime
    have hF' : algebraMap (MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K))
        (MvPolynomial (Fin (D + 1) × Fin N) L) F = f' := hkey
    rw [hF'] at hprime
    exact ((Ideal.span_singleton_prime hf'0).1 hprime).irreducible
  · intro u
    set ũ : Fin (D + 1 + 1) × Fin N → AlgebraicClosure L := fun v =>
      Fin.lastCases (motive := fun _ => AlgebraicClosure L) (algebraMap L (AlgebraicClosure L) (t v.2))
        (fun i => u (i, v.2)) v.1 with hũ
    have hev : aeval u f' = aeval ũ f := by
      rw [hf']
      change ((aeval u).restrictScalars K) (aeval φ f) = aeval ũ f
      rw [← AlgHom.comp_apply, comp_aeval]
      refine congrArg (fun x => (aeval x) f) (funext fun v => ?_)
      rcases v with ⟨i, j⟩
      induction i using Fin.lastCases <;> simp [hφ, hũ]
    have hPhom : Ideal.IsHomogeneous (homogeneousSubmodule (Fin N) K) P := by
      intro i r hr
      convert hP r hr i using 1
      conv_lhs => rw [← sum_homogeneousComponent r]
      rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum,
        Finset.sum_eq_single i]
      · exact DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem i r)
      · intro b _ hb
        exact DirectSum.decompose_of_mem_ne _ (homogeneousComponent_mem b r) hb
      · intro hi
        have h0 : homogeneousComponent i r = 0 :=
          homogeneousComponent_eq_zero i r (by simp at hi; omega)
        rw [h0, DirectSum.decompose_zero]
        rfl
    have hideal : ∀ y : Fin N → AlgebraicClosure L,
        (∀ g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
          Ideal.span {(∑ j : Fin N, C (t j) * X j : MvPolynomial (Fin N) L)}, aeval y g = 0) ↔
        (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, ũ (Fin.last (D + 1), j) * y j = 0 := by
      intro y
      have hmap : ∀ g : MvPolynomial (Fin N) K,
          aeval y (MvPolynomial.map (algebraMap K L) g) = aeval y g := fun g => aeval_map_algebraMap L y g
      have hlin : aeval y (∑ j : Fin N, C (t j) * X j : MvPolynomial (Fin N) L) =
          ∑ j, ũ (Fin.last (D + 1), j) * y j := by
        simp [hũ]
      constructor
      · intro H
        refine ⟨fun g hg => ?_, ?_⟩
        · rw [← hmap]
          exact H _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg))
        · rw [← hlin]
          exact H _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      · rintro ⟨H1, H2⟩ g hg
        have hle : P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
            Ideal.span {(∑ j : Fin N, C (t j) * X j : MvPolynomial (Fin N) L)} ≤
            RingHom.ker (aeval y : MvPolynomial (Fin N) L →ₐ[L] AlgebraicClosure L) := by
          refine sup_le (Ideal.map_le_iff_le_comap.2 fun g hg => ?_) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
          · simpa [RingHom.mem_ker, hmap] using H1 g hg
          · simpa [RingHom.mem_ker, hlin] using H2
        exact RingHom.mem_ker.1 (hle hg)
    rw [hev, hf.zero_iff_of_isAlgClosed hPhom ũ]
    constructor
    · rintro ⟨y, hy0, hyP, hyu⟩
      rw [Fin.forall_fin_succ'] at hyu
      exact ⟨y, hy0, (hideal y).2 ⟨hyP, hyu.2⟩, fun i => by simpa [hũ] using hyu.1 i⟩
    · rintro ⟨y, hy0, hyI, hyu⟩
      obtain ⟨hyP, hyh⟩ := (hideal y).1 hyI
      exact ⟨y, hy0, hyP, Fin.forall_fin_succ'.2 ⟨fun i => by simpa [hũ] using hyu i, hyh⟩⟩

end GlobalTheory.ChowSpec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormGenericHyperplaneSectionStatement
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chowForm_generic_hyperplane_section : ∀ (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K)) (D δ : ℕ) (f : MvPolynomial (Fin (D + 1 + 1) × Fin N) K), (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → IsChowFormInt P (D + 1) δ f → ∃ f' : MvPolynomial (Fin (D + 1) × Fin N) L, IsChowFormInt (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔ Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L)}) D δ f' := by
  first | exact @GlobalTheory.ChowSpec.exists_isChowFormInt_generic_section | exact GlobalTheory.ChowSpec.exists_isChowFormInt_generic_section | (intros; apply GlobalTheory.ChowSpec.exists_isChowFormInt_generic_section <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerContractionChartForms
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR.StabTheta

variable {K : Type} [Field K]

theorem smul_mem_spanForms (M M' : Set K) (H : Set Ω[K⁄ℤ]) (a : ℕ) (c : K)
    (h : ∀ m ∈ M, c * m ∈ M') {η : abelian₂ K} (hη : η ∈ spanForms M H a) :
    c • η ∈ spanForms M' H a := by
  have key : spanForms M H a ≤
      (spanForms M' H a).comap (DistribSMul.toAddMonoidHom (abelian₂ K) c) := by
    unfold spanForms
    rw [AddSubgroup.closure_le]
    rintro _ ⟨m, hm, v, hv, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    show c • (m • ExteriorAlgebra.ιMulti K a v) ∈ AddSubgroup.closure _
    rw [smul_smul]
    exact AddSubgroup.subset_closure ⟨c * m, h m hm, v, hv, rfl⟩
  exact key hη

theorem iota_mul_mem_spanForms (M : Set K) (H : Set Ω[K⁄ℤ]) (q : ℕ) (w : Ω[K⁄ℤ]) (hw : w ∈ H)
    {η : abelian₂ K} (hη : η ∈ spanForms M H q) :
    ExteriorAlgebra.ι K w * η ∈ spanForms M H (q + 1) := by
  have key : spanForms M H q ≤
      (spanForms M H (q + 1)).comap (AddMonoidHom.mulLeft (ExteriorAlgebra.ι K w)) := by
    unfold spanForms
    rw [AddSubgroup.closure_le]
    rintro _ ⟨m, hm, v, hv, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    show ExteriorAlgebra.ι K w * (m • ExteriorAlgebra.ιMulti K q v) ∈ AddSubgroup.closure _
    rw [mul_smul_comm]
    refine AddSubgroup.subset_closure ⟨m, hm, Fin.cons w v, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hw
      · simpa using hv k
    · rw [ExteriorAlgebra.ιMulti_succ_apply]
      simp [Matrix.vecTail]
  exact key hη

theorem theta_dlog {n : ℕ} (x : Fin n → Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K)
    (hθ : IsEulerContraction x i θ) (j : Fin n) :
    θ (ExteriorAlgebra.ι K (dlog (x j))) = algebraMap K (abelian₂ K) (if j = i then 1 else 0) := by
  rw [hθ.2.2 j]
  split_ifs <;> simp

theorem theta_frame (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n)
    (θ : abelian₂ K →ₗ[K] abelian₂ K) (hx : ∀ j, (x j : K) ∈ A) (hθ : IsEulerContraction x i θ) (j : Fin n) :
    ∃ a ∈ A, θ (ExteriorAlgebra.ι K (frame x J j)) = algebraMap K (abelian₂ K) a := by
  have hif : (if j = i then (1 : K) else 0) ∈ A := by split_ifs <;> simp
  unfold frame
  split_ifs with hj
  · exact ⟨_, hif, theta_dlog x i θ hθ j⟩
  · have hd : dK (x j : K) = (x j : K) • dlog (x j) := by
      unfold dlog
      rw [smul_smul]
      simp
    refine ⟨(x j : K) * (if j = i then 1 else 0), A.mul_mem (hx j) hif, ?_⟩
    rw [hd, map_smul, map_smul, theta_dlog x i θ hθ j, Algebra.smul_def, ← map_mul]

theorem theta_iotaMulti (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n)
    (θ : abelian₂ K →ₗ[K] abelian₂ K) (hx : ∀ j, (x j : K) ∈ A) (hθ : IsEulerContraction x i θ) :
    ∀ (q : ℕ) (v : Fin (q + 1) → Ω[K⁄ℤ]), (∀ k, v k ∈ Set.range (frame x J)) →
      θ (ExteriorAlgebra.ιMulti K (q + 1) v) ∈ spanForms (A : Set K) (Set.range (frame x J)) q := by
  intro q
  induction q with
  | zero =>
    intro v hv
    rw [ExteriorAlgebra.ιMulti_succ_apply, hθ.2.1, ExteriorAlgebra.ιMulti_zero_apply, hθ.1,
      mul_zero, sub_zero, mul_one]
    obtain ⟨j, hj⟩ := hv 0
    obtain ⟨a, ha, he⟩ := theta_frame A x J i θ hx hθ j
    rw [← hj, he, Algebra.algebraMap_eq_smul_one]
    refine AddSubgroup.subset_closure ⟨a, ha, Matrix.vecTail v, fun k => k.elim0, ?_⟩
    rw [ExteriorAlgebra.ιMulti_zero_apply]
  | succ q ih =>
    intro v hv
    rw [ExteriorAlgebra.ιMulti_succ_apply, hθ.2.1]
    obtain ⟨j, hj⟩ := hv 0
    obtain ⟨a, ha, he⟩ := theta_frame A x J i θ hx hθ j
    have htail : ∀ k, Matrix.vecTail v k ∈ Set.range (frame x J) := fun k => hv k.succ
    refine AddSubgroup.sub_mem _ ?_ ?_
    · rw [← hj, he, ← Algebra.smul_def]
      exact AddSubgroup.subset_closure ⟨a, ha, Matrix.vecTail v, htail, rfl⟩
    · exact iota_mul_mem_spanForms _ _ q _ (hv 0) (ih _ htail)

end GlobalTheory.LogDR.StabTheta

open GlobalTheory.LogDR.StabTheta in
theorem GlobalTheory.LogDR.chartForms_stable_euler :
    ∀ (K : Type) [Field K] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K), (∀ j, (x j : K) ∈ A) → IsEulerContraction x i θ → (∀ q, ∀ η ∈ chartForms A x J t (q + 1), θ η ∈ chartForms A x J t q) ∧ ∀ η ∈ chartForms A x J t 0, θ η = 0 := by
  intro K _ A n x J t i θ hx hθ
  constructor
  · intro q η hη
    have key : chartForms A x J t (q + 1) ≤ (chartForms A x J t q).comap θ.toAddMonoidHom := by
      unfold chartForms spanForms
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, v, hv, rfl⟩
      rw [SetLike.mem_coe, AddSubgroup.mem_comap]
      show θ (c • ExteriorAlgebra.ιMulti K (q + 1) v) ∈ spanForms _ _ q
      rw [map_smul]
      refine smul_mem_spanForms (A : Set K) _ _ q c ?_ (theta_iotaMulti A x J i θ hx hθ q v hv)
      intro m hm
      show c * m * (t : K) ∈ A
      rw [mul_right_comm]
      exact A.mul_mem hc hm
    exact key hη
  · intro η hη
    have key : chartForms A x J t 0 ≤ θ.toAddMonoidHom.ker := by
      unfold chartForms spanForms
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, v, hv, rfl⟩
      rw [SetLike.mem_coe, AddMonoidHom.mem_ker]
      show θ (c • ExteriorAlgebra.ιMulti K 0 v) = 0
      rw [map_smul, ExteriorAlgebra.ιMulti_zero_apply, hθ.1, smul_zero]
    exact key hη
end
