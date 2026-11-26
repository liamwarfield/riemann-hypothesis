module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SimplicialConeTiling

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PlaceApply
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsUnitPowerInCongruence
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsUnitPowerInCongruence
set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem exists_pow_mem_congUnits : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∃ e : ℕ, 0 < e ∧ ∀ u : (𝓞 F)ˣ, u ^ e ∈ congUnits 𝔣 := by
  intro F _ _ 𝔣 h𝔣
  haveI : Finite (𝓞 F ⧸ 𝔣) := Ideal.finiteQuotientOfFreeOfNeBot 𝔣 h𝔣
  have hpos : 0 < Nat.card (𝓞 F ⧸ 𝔣)ˣ := Nat.card_pos
  refine ⟨2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ, by omega, fun u => ⟨?_, fun σ => ?_⟩⟩
  · have h1 : (Units.map (Ideal.Quotient.mk 𝔣 : 𝓞 F →* 𝓞 F ⧸ 𝔣) u) ^ (2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ) = 1 := by
      rw [mul_comm, pow_mul, pow_card_eq_one', one_pow]
    have h2 : Ideal.Quotient.mk 𝔣 ((u ^ (2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ) : (𝓞 F)ˣ) : 𝓞 F) = Ideal.Quotient.mk 𝔣 1 := by
      have h3 := congrArg (fun z : (𝓞 F ⧸ 𝔣)ˣ => (z : 𝓞 F ⧸ 𝔣)) h1
      simpa using h3
    exact Ideal.Quotient.eq.mp h2
  · have hne : σ (((u : 𝓞 F)) : F) ≠ 0 := by
      rw [Ne, map_eq_zero]
      simp
    have h : (((u ^ (2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ) : (𝓞 F)ˣ) : 𝓞 F) : F) = (((u : 𝓞 F)) : F) ^ (2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ) := by
      simp
    rw [h, map_pow, pow_mul]
    exact pow_pos (by positivity) _

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsUnitPowerInCongruenceStatement
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_power_in_congruence : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ → ∃ e : ℕ, 0 < e ∧ ∀ u : (𝓞 F)ˣ, u ^ e ∈ congUnits 𝔣 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.exists_pow_mem_congUnits | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.exists_pow_mem_congUnits | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.exists_pow_mem_congUnits <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitLogLatticeBoundedTranslate
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitLogLatticeBoundedTranslate
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.UnitLattice

theorem multiples_relativelyDense (F : Type) [Field F] [NumberField F] (e : ℕ) (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : logSpace F, ∃ u : (𝓞 F)ˣ,
      ∀ w, |y w + (e : ℝ) * logEmbedding F (Additive.ofMul u) w| ≤ C := by
  classical
  let b := (basisUnitLattice F).ofZLatticeBasis ℝ (unitLattice F)
  let R : ℝ := ∑ i, ‖b i‖
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  refine ⟨(e : ℝ) * R, by positivity, fun y => ?_⟩
  let v : logSpace F := fun w => -(y w) / (e : ℝ)
  have hfl : ((ZSpan.floor b v : _) : logSpace F) ∈ unitLattice F := by
    rw [← (basisUnitLattice F).ofZLatticeBasis_span ℝ (unitLattice F)]
    exact (ZSpan.floor b v).2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.mp hfl
  refine ⟨Additive.toMul x, fun w => ?_⟩
  have hfr : ‖v - (ZSpan.floor b v : logSpace F)‖ ≤ R := by
    simpa [ZSpan.fract_apply] using ZSpan.norm_fract_le b v
  have h1 := norm_le_pi_norm (v - (ZSpan.floor b v : logSpace F)) w
  rw [← hx] at h1 hfr
  have h2 : (logEmbedding F).toIntLinearMap x w
      = logEmbedding F (Additive.ofMul (Additive.toMul x)) w := rfl
  rw [Pi.sub_apply, h2, Real.norm_eq_abs] at h1
  have h3 : y w + (e : ℝ) * logEmbedding F (Additive.ofMul (Additive.toMul x)) w
      = -((e : ℝ) * (v w - logEmbedding F (Additive.ofMul (Additive.toMul x)) w)) := by
    simp only [v]; field_simp; ring
  rw [h3, abs_neg, abs_mul, abs_of_pos he0]
  exact mul_le_mul_of_nonneg_left (h1.trans hfr) he0.le

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.UnitLattice
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitLogLatticeBoundedTranslateStatement
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_log_lattice_bounded_translate : ∀ (F : Type) [Field F] [NumberField F] (e : ℕ), 0 < e → ∃ C : ℝ, 0 ≤ C ∧ ∀ y : logSpace F, ∃ u : (𝓞 F)ˣ,
    ∀ w, |y w + (e : ℝ) * logEmbedding F (Additive.ofMul u) w| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.UnitLattice.multiples_relativelyDense | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.UnitLattice.multiples_relativelyDense | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.UnitLattice.multiples_relativelyDense <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PlaceApply
set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance

theorem abs_le_of_sum_eq_zero {F : Type} [Field F] [NumberField F] (f : InfinitePlace F → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hs : ∑ w, f w = 0) (hf : ∀ w, w ≠ w₀ → |f w| ≤ C) (w : InfinitePlace F) :
    |f w| ≤ (Fintype.card (InfinitePlace F) : ℝ) * C := by
  classical
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨w⟩
  by_cases hw : w = w₀
  · subst hw
    have h1 : f w₀ = -∑ v ∈ Finset.univ.erase w₀, f v := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w₀)] at hs
      linarith
    rw [h1, abs_neg]
    calc |∑ v ∈ Finset.univ.erase w₀, f v| ≤ ∑ v ∈ Finset.univ.erase w₀, |f v| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ Finset.univ.erase w₀, C :=
          Finset.sum_le_sum fun v hv => hf v (Finset.ne_of_mem_erase hv)
      _ = ((Finset.univ.erase w₀).card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card (InfinitePlace F) : ℝ) * C := by
          refine mul_le_mul_of_nonneg_right ?_ hC
          exact_mod_cast (Finset.card_erase_le).trans (Finset.card_le_univ _)
  · calc |f w| ≤ C := hf w hw
      _ = 1 * C := (one_mul C).symm
      _ ≤ (Fintype.card (InfinitePlace F) : ℝ) * C := mul_le_mul_of_nonneg_right hcard hC

theorem place_apply {F : Type} [Field F] [NumberField F] (σ : F →+* ℝ) (y : F) :
    (InfinitePlace.mk (Complex.ofRealHom.comp σ)) y = |σ y| := by
  rw [InfinitePlace.apply]
  simp

theorem balance : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∃ M : ℝ, ∀ x : F, TotPos F x → ∃ u : (𝓞 F)ˣ, u ∈ congUnits 𝔣 ∧
      ∀ σ τ : F →+* ℝ, σ (((u : 𝓞 F) : F) * x) ≤ M * τ (((u : 𝓞 F) : F) * x) := by
  intro F _ _ _ 𝔣 h𝔣
  obtain ⟨e, he, hpow⟩ := GlobalTheory.T.exists_unit_power_in_congruence F 𝔣 h𝔣
  obtain ⟨C, hC, hbound⟩ := GlobalTheory.T.unit_log_lattice_bounded_translate F e he
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (Fintype.card (InfinitePlace F) : ℝ) := ⟨_, rfl⟩
  refine ⟨Real.exp (2 * (n * C)), fun x hx => ?_⟩
  have hx0 : x ≠ 0 := by
    intro h0
    have h := hx (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal (w₀ : InfinitePlace F)))
    rw [h0, map_zero] at h
    exact lt_irrefl _ h
  have hwx : ∀ w : InfinitePlace F, 0 < w x := fun w => InfinitePlace.pos_iff.mpr hx0
  have hn0 : n ≠ 0 := by
    rw [hn]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(w₀ : InfinitePlace F)⟩).ne'
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ∑ w : InfinitePlace F, Real.log (w x) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ := hbound (fun w => Real.log (w.1 x) - s / n)
  have hv := hpow u
  refine ⟨u ^ e, hv, fun σ τ => ?_⟩
  obtain ⟨-, hvpos⟩ := hv
  have hpowc : (((u ^ e : (𝓞 F)ˣ) : 𝓞 F) : F) = (algebraMap (𝓞 F) F (u : 𝓞 F)) ^ e := by
    rw [Units.val_pow_eq_pow_val]
    exact map_pow (algebraMap (𝓞 F) F) _ _
  have hξpos : ∀ ρ : F →+* ℝ, 0 < ρ ((((u ^ e : (𝓞 F)ˣ) : 𝓞 F) : F) * x) := by
    intro ρ
    rw [map_mul]
    exact mul_pos (hvpos ρ) (hx ρ)
  generalize hξ : (((u ^ e : (𝓞 F)ˣ) : 𝓞 F) : F) * x = ξ at hξpos ⊢
  have hlog : ∀ w : InfinitePlace F,
      Real.log (w ξ) = e * Real.log (w (algebraMap (𝓞 F) F (u : 𝓞 F))) + Real.log (w x) := by
    intro w
    have hwu : w (algebraMap (𝓞 F) F (u : 𝓞 F)) ≠ 0 :=
      (InfinitePlace.pos_iff.mpr (NumberField.Units.coe_ne_zero u)).ne'
    rw [← hξ, hpowc, map_mul, map_pow, Real.log_mul (pow_ne_zero _ hwu) (hwx w).ne', Real.log_pow]
  set f : InfinitePlace F → ℝ := fun w => Real.log (w ξ) - s / n with hf
  have hsumu : ∑ w : InfinitePlace F, Real.log (w (algebraMap (𝓞 F) F (u : 𝓞 F))) = 0 := by
    have h := NumberField.Units.sum_mult_mul_log u
    simpa only [IsTotallyReal.mult_eq, Nat.cast_one, one_mul] using h
  have hsum : ∑ w, f w = 0 := by
    have h1 : ∀ w, f w = (e : ℝ) * Real.log (w (algebraMap (𝓞 F) F (u : 𝓞 F))) + Real.log (w x) - s / n :=
      fun w => by
        show Real.log (w ξ) - s / n = _
        rw [hlog w]
    rw [Finset.sum_congr rfl (fun w _ => h1 w), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hsumu, ← hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]
    have h2 : n * (s / n) = s := by field_simp
    rw [h2]
    ring
  have hfC : ∀ w, w ≠ w₀ → |f w| ≤ C := by
    intro w hw
    have h := hu ⟨w, hw⟩
    simp only [logEmbedding_component, IsTotallyReal.mult_eq, Nat.cast_one, one_mul] at h
    have h2 : f w = Real.log (w x) - s / n + e * Real.log (w (algebraMap (𝓞 F) F (u : 𝓞 F))) := by
      show Real.log (w ξ) - s / n = _
      rw [hlog w]
      ring
    rw [h2]
    exact h
  have hbd : ∀ w, |f w| ≤ n * C := fun w => by
    rw [hn]
    exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance.abs_le_of_sum_eq_zero f C hC hsum hfC w
  have hρ : ∀ ρ : F →+* ℝ, Real.log (ρ ξ) = f (InfinitePlace.mk (Complex.ofRealHom.comp ρ)) + s / n := by
    intro ρ
    rw [hf]
    simp only []
    rw [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance.place_apply, abs_of_pos (hξpos ρ)]
    ring
  have key : Real.log (σ ξ) ≤ 2 * (n * C) + Real.log (τ ξ) := by
    rw [hρ σ, hρ τ]
    have h1 := abs_le.mp (hbd (InfinitePlace.mk (Complex.ofRealHom.comp σ)))
    have h2 := abs_le.mp (hbd (InfinitePlace.mk (Complex.ofRealHom.comp τ)))
    linarith [h1.2, h2.1]
  calc σ ξ = Real.exp (Real.log (σ ξ)) := (Real.exp_log (hξpos σ)).symm
    _ ≤ Real.exp (2 * (n * C) + Real.log (τ ξ)) := Real.exp_le_exp.mpr key
    _ = Real.exp (2 * (n * C)) * τ ξ := by rw [Real.exp_add, Real.exp_log (hξpos τ)]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PlaceApplyStatement
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_congruence_unit_balancing_embeddings : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∃ M : ℝ, ∀ x : F, TotPos F x → ∃ u : (𝓞 F)ˣ, u ∈ congUnits 𝔣 ∧
      ∀ σ τ : F →+* ℝ, σ (((u : 𝓞 F) : F) * x) ≤ M * τ (((u : 𝓞 F) : F) * x) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance.balance | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance.balance | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance.balance <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsTotallyPositiveBasisPositiveCoords
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CardRealEmbeddingsEqFinrank
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CardRealEmbeddingsEqFinrank
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard

theorem finite_and_card_realEmbeddings (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Finite (F →+* ℝ) ∧ Nat.card (F →+* ℝ) = Module.finrank ℚ F := by
  have e : (F →+* ℝ) ≃ (F →+* ℂ) :=
    { toFun := fun σ => Complex.ofRealHom.comp σ
      invFun := fun φ => (IsTotallyReal.complexEmbedding_isReal φ).embedding
      left_inv := fun σ => by
        ext x
        apply Complex.ofReal_injective
        simp [ComplexEmbedding.IsReal.coe_embedding_apply]
      right_inv := fun φ => by
        ext x
        simp [ComplexEmbedding.IsReal.coe_embedding_apply] }
  have hc : Nat.card (F →+* ℂ) = Module.finrank ℚ F := by
    rw [Nat.card_eq_fintype_card]
    exact Embeddings.card F ℂ
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, hc]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CardRealEmbeddingsEqFinrankStatement
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_real_embeddings_eq_finrank : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Finite (F →+* ℝ) ∧ Nat.card (F →+* ℝ) = Module.finrank ℚ F := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard.finite_and_card_realEmbeddings | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard.finite_and_card_realEmbeddings | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard.finite_and_card_realEmbeddings <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyRealFieldDenseEmbeddings
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyRealFieldDenseEmbeddings
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density

theorem denseRange_real_places (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    DenseRange fun (x : F) (w : InfinitePlace F) =>
      InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x := by
  rw [Metric.denseRange_iff]
  intro z ε hε
  have hq : ∀ w : InfinitePlace F, ∃ q : ℚ, |(q : ℝ) - z w| < ε / 2 := by
    intro w
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show z w < z w + ε / 2 by linarith)
    exact ⟨q, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  choose q hq using hq
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.mp (InfinitePlace.denseRange_algebraMap_pi F)
    (fun w => WithAbs.toAbs w.1 ((q w : ℚ) : F)) (ε / 2) (by linarith)
  refine ⟨x, (dist_pi_lt_iff hε).mpr fun w => ?_⟩
  have hxw := (dist_pi_lt_iff (by linarith : (0 : ℝ) < ε / 2)).mp hx w
  try dsimp only at hxw
  rw [Pi.algebraMap_apply, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub, WithAbs.ofAbs_toAbs,
    WithAbs.algebraMap_right_apply, WithAbs.ofAbs_toAbs, Algebra.algebraMap_self, RingHom.id_apply] at hxw
  have h2 : w.1 ((q w : F) - x) =
      |(q w : ℝ) - InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x| := by
    have h := InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal w) ((q w : F) - x)
    rw [Real.norm_eq_abs, map_sub, map_ratCast] at h
    exact h.symm
  rw [h2] at hxw
  show dist (z w) (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x) < ε
  rw [Real.dist_eq]
  have h3 : |z w - (q w : ℝ)| < ε / 2 := by
    rw [abs_sub_comm]
    exact hq w
  linarith [abs_sub_le (z w) (q w : ℝ) (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x)]

theorem exists_place_eq (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (σ : F →+* ℝ) :
    ∃ w : InfinitePlace F, InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) = σ := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  refine ⟨InfinitePlace.mk (Complex.ofRealHom.comp σ), ?_⟩
  ext x
  have h1 := InfinitePlace.embedding_of_isReal_apply
    (IsTotallyReal.isReal (InfinitePlace.mk (Complex.ofRealHom.comp σ))) x
  rw [InfinitePlace.embedding_mk_eq_of_isReal hφ, RingHom.comp_apply, Complex.ofRealHom_eq_coe] at h1
  exact_mod_cast h1

theorem exists_approx : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : (F →+* ℝ) → ℝ) (ε : ℝ),
    0 < ε → ∃ x : F, ∀ σ : F →+* ℝ, |σ x - y σ| < ε := by
  intro F _ _ _ y ε hε
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.mp (denseRange_real_places F)
    (fun w => y (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))) ε hε
  refine ⟨x, fun σ => ?_⟩
  obtain ⟨w, hw⟩ := exists_place_eq F σ
  have h := (dist_pi_lt_iff hε).mp hx w
  rw [Real.dist_eq, hw, abs_sub_comm] at h
  exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyRealFieldDenseEmbeddingsStatement
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totally_real_field_dense_embeddings : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : (F →+* ℝ) → ℝ) (ε : ℝ), 0 < ε → ∃ x : F, ∀ σ : F →+* ℝ, |σ x - y σ| < ε := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density.exists_approx | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density.exists_approx | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density.exists_approx <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.NearIdentityMatrixPositiveSolution
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.NearIdentityMatrixPositiveSolution
namespace GlobalTheory.CompanionTheory.DiagDom

theorem perturb_bound {κ : Type} [Fintype κ] [DecidableEq κ] (W : κ → κ → ℝ) (ε C : ℝ)
    (hW : ∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) (c : κ → ℝ)
    (hC : ∀ i, |c i| ≤ C) (σ : κ) :
    |∑ i, W σ i * c i - c σ| ≤ (Fintype.card κ : ℝ) * ε * C := by
  have hrw : ∑ i, W σ i * c i - c σ = ∑ i, (W σ i - if σ = i then 1 else 0) * c i := by
    simp [sub_mul, Finset.sum_sub_distrib, ite_mul]
  rw [hrw]
  calc |∑ i, (W σ i - if σ = i then 1 else 0) * c i|
      ≤ ∑ i, |(W σ i - if σ = i then 1 else 0) * c i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : κ, ε * C := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (hW σ i).le (hC i) (abs_nonneg _) ((abs_nonneg _).trans (hW σ i).le)
    _ = (Fintype.card κ : ℝ) * ε * C := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

theorem small_perturbation_injective_pos :
    ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (M : ℝ), ∃ ε : ℝ, 0 < ε ∧ ∀ W : κ → κ → ℝ,
      (∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) →
      (∀ c : κ → ℝ, (∀ σ, ∑ i, W σ i * c i = 0) → c = 0) ∧
      ∀ c : κ → ℝ, (∀ σ, 0 < ∑ i, W σ i * c i) →
        (∀ σ τ, ∑ i, W σ i * c i ≤ M * ∑ i, W τ i * c i) → ∀ i, 0 < c i := by
  intro κ _ _ M
  have hn0 : (0 : ℝ) ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  have hM1 : 0 < |M| + 1 := by positivity
  refine ⟨1 / (2 * ((Fintype.card κ : ℝ) + 1) * (|M| + 1)), by positivity, fun W hW => ?_⟩
  set n : ℝ := (Fintype.card κ : ℝ) with hn
  set ε := 1 / (2 * (n + 1) * (|M| + 1)) with hε
  have hδ : n * ε * (2 * (|M| + 1)) ≤ 1 := by
    have e : n * ε * (2 * (|M| + 1)) = n / (n + 1) := by
      rw [hε]
      field_simp
    rw [e, div_le_one (by linarith)]
    linarith
  have hε0 : 0 < ε := by positivity
  have hδ0 : 0 ≤ n * ε := by positivity
  have hδh : n * ε ≤ 1 / 2 := by nlinarith [abs_nonneg M]
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · exact ⟨fun c _ => funext fun i => (IsEmpty.false i).elim, fun c _ _ i => (IsEmpty.false i).elim⟩
  have bound : ∀ c : κ → ℝ, ∃ j, ∀ σ,
      |∑ i, W σ i * c i - c σ| ≤ n * ε * |c j| ∧ |c σ| ≤ |c j| := by
    intro c
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |c i|) Finset.univ_nonempty
    exact ⟨j, fun σ => ⟨perturb_bound W ε |c j| hW c (fun i => hj i (Finset.mem_univ i)) σ,
      hj σ (Finset.mem_univ σ)⟩⟩
  constructor
  · intro c hc
    obtain ⟨j, hj⟩ := bound c
    have h1 := (hj j).1
    rw [hc j, zero_sub, abs_neg] at h1
    have hC : |c j| = 0 := by nlinarith [abs_nonneg (c j)]
    funext i
    have h2 := (hj i).2
    rw [hC] at h2
    exact abs_nonpos_iff.mp h2
  · intro c hpos hratio i
    obtain ⟨j, hj⟩ := bound c
    have hC0 : 0 ≤ |c j| := abs_nonneg _
    have h1 : |c j| ≤ ∑ k, W j k * c k + n * ε * |c j| := by
      have e := abs_sub_abs_le_abs_sub (c j) (∑ k, W j k * c k)
      rw [abs_sub_comm (c j), abs_of_pos (hpos j)] at e
      linarith [(hj j).1]
    have h2 : ∑ k, W i k * c k - n * ε * |c j| ≤ c i := by
      linarith [(abs_le.mp (hj i).1).2]
    have h3 := hratio j i
    have hyi := hpos i
    have hMy : M * ∑ k, W i k * c k ≤ |M| * ∑ k, W i k * c k :=
      mul_le_mul_of_nonneg_right (le_abs_self M) hyi.le
    have s1 : n * ε * |c j| * (2 * (|M| + 1)) ≤ |c j| := by
      nlinarith [mul_le_mul_of_nonneg_right hδ hC0]
    have s2 : |c j| * (1 - n * ε) ≤ |M| * ∑ k, W i k * c k := by nlinarith
    have s3 : n * ε * |c j| * (|M| + 1) < (∑ k, W i k * c k) * (|M| + 1) := by
      nlinarith [mul_nonneg hC0 (by linarith : (0 : ℝ) ≤ 1 - 2 * (n * ε))]
    have s4 : n * ε * |c j| < ∑ k, W i k * c k := lt_of_mul_lt_mul_right s3 hM1.le
    linarith

end GlobalTheory.CompanionTheory.DiagDom
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.NearIdentityMatrixPositiveSolutionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.near_identity_matrix_positive_solution : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (M : ℝ), ∃ ε : ℝ, 0 < ε ∧ ∀ W : κ → κ → ℝ, (∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) →
    (∀ c : κ → ℝ, (∀ σ, ∑ i, W σ i * c i = 0) → c = 0) ∧
    ∀ c : κ → ℝ, (∀ σ, 0 < ∑ i, W σ i * c i) → (∀ σ τ, ∑ i, W σ i * c i ≤ M * ∑ i, W τ i * c i) → ∀ i, 0 < c i := by
  first | exact @GlobalTheory.CompanionTheory.DiagDom.small_perturbation_injective_pos | exact GlobalTheory.CompanionTheory.DiagDom.small_perturbation_injective_pos | (intros; apply GlobalTheory.CompanionTheory.DiagDom.small_perturbation_injective_pos <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsTotallyPositiveBasisPositiveCoords
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens

theorem map_sum_ratSmul {F κ : Type} [Field F] [Fintype κ] (σ : F →+* ℝ) (q : κ → ℚ) (v : κ → F) :
    σ (∑ i, q i • v i) = ∑ i, σ (v i) * (q i : ℝ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast, mul_comm]

theorem exists_totPos_basis : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : ℝ),
    ∃ (κ : Type) (_ : Fintype κ) (b : Module.Basis κ ℚ F), (∀ i, TotPos F (b i)) ∧
      ∀ x : F, TotPos F x → (∀ σ τ : F →+* ℝ, σ x ≤ M * τ x) → ∀ i, 0 < b.repr x i := by
  intro F _ _ _ M
  classical
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.card_real_embeddings_eq_finrank F
  letI : Fintype (F →+* ℝ) := Fintype.ofFinite _
  obtain ⟨ε, hε, hW⟩ := GlobalTheory.T.near_identity_matrix_positive_solution (κ := F →+* ℝ) M
  have hex : ∀ i : F →+* ℝ, ∃ v : F, ∀ σ : F →+* ℝ,
      |σ v - ((if σ = i then 1 else 0) + ε / 2)| < ε / 2 :=
    fun i => GlobalTheory.T.totally_real_field_dense_embeddings F (fun σ => (if σ = i then 1 else 0) + ε / 2) (ε / 2) (by positivity)
  choose v hv using hex
  have hclose : ∀ σ i : F →+* ℝ, |σ (v i) - if σ = i then 1 else 0| < ε := by
    intro σ i
    have h := abs_lt.mp (hv i σ)
    rw [abs_lt]
    constructor <;> linarith [h.1, h.2]
  have hpos : ∀ σ i : F →+* ℝ, 0 < σ (v i) := by
    intro σ i
    have h := (abs_lt.mp (hv i σ)).1
    split_ifs at h <;> linarith
  obtain ⟨h1, h2⟩ := hW (fun σ i => σ (v i)) hclose
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro q hq i
    have hz : (fun i => (q i : ℝ)) = 0 := h1 _ fun σ => by
      rw [← map_sum_ratSmul σ q v, hq, map_zero]
    have hi : (q i : ℝ) = 0 := congrFun hz i
    exact_mod_cast hi
  have hcardκ : Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  haveI : Nonempty (F →+* ℝ) := by
    apply Fintype.card_pos_iff.mp
    rw [hcardκ]
    exact Module.finrank_pos
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcardκ
  have hb : ∀ i, b i = v i := fun i => by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨F →+* ℝ, inferInstance, b, fun i σ => ?_, fun x hx hM i => ?_⟩
  · rw [hb]; exact hpos σ i
  · have hrep : ∀ σ : F →+* ℝ, σ x = ∑ i, σ (v i) * ((b.repr x i : ℚ) : ℝ) := by
      intro σ
      rw [← map_sum_ratSmul σ (fun i => b.repr x i) v]
      congr 1
      conv_lhs => rw [← b.sum_repr x]
      exact Finset.sum_congr rfl fun j _ => by rw [hb]
    have hc := h2 (fun i => ((b.repr x i : ℚ) : ℝ))
      (fun σ => by rw [← hrep σ]; exact hx σ)
      (fun σ τ => by rw [← hrep σ, ← hrep τ]; exact hM σ τ) i
    exact_mod_cast hc

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsTotallyPositiveBasisPositiveCoordsStatement
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_totally_positive_basis_positive_coords : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : ℝ),
    ∃ (κ : Type) (_ : Fintype κ) (b : Module.Basis κ ℚ F), (∀ i, TotPos F (b i)) ∧
      ∀ x : F, TotPos F x → (∀ σ τ : F →+* ℝ, σ x ≤ M * τ x) → ∀ i, 0 < b.repr x i := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens.exists_totPos_basis | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens.exists_totPos_basis | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens.exists_totPos_basis <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteUnitsBoundedEmbeddingRatio
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteUnitsBoundedEmbeddingRatio
set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem embedding_unit_le_abs {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {R : ℝ} {u : (𝓞 F)ˣ}
    (hu : TotPos F ((u : 𝓞 F) : F)) (hR : ∀ σ τ : F →+* ℝ, σ ((u : 𝓞 F) : F) ≤ R * τ ((u : 𝓞 F) : F))
    (σ : F →+* ℝ) : σ ((u : 𝓞 F) : F) ≤ |R| := by
  classical
  haveI : Finite (F →+* ℝ) := Finite.of_equiv _ (realEmbeddingsEquiv F).symm
  haveI : Fintype (F →+* ℝ) := Fintype.ofFinite _
  have hprod : ∏ τ : F →+* ℝ, τ ((u : 𝓞 F) : F) = 1 := by
    rw [prod_real_embeddings_eq_absNorm (u : 𝓞 F) hu, Ideal.span_singleton_eq_top.2 u.isUnit, Ideal.absNorm_top]
    simp
  obtain ⟨τ, hτ⟩ : ∃ τ : F →+* ℝ, τ ((u : 𝓞 F) : F) ≤ 1 := by
    by_contra hne
    push_neg at hne
    have hlt : ∏ _τ : F →+* ℝ, (1 : ℝ) < ∏ τ : F →+* ℝ, τ ((u : 𝓞 F) : F) :=
      Finset.prod_lt_prod_of_nonempty₀ (fun _ _ => one_pos) (fun τ _ => hne τ) ⟨σ, Finset.mem_univ σ⟩
    rw [hprod] at hlt
    simp at hlt
  calc σ ((u : 𝓞 F) : F) ≤ R * τ ((u : 𝓞 F) : F) := hR σ τ
    _ ≤ |R| * τ ((u : 𝓞 F) : F) := mul_le_mul_of_nonneg_right (le_abs_self R) (hu τ).le
    _ ≤ |R| * 1 := mul_le_mul_of_nonneg_left hτ (abs_nonneg R)
    _ = |R| := mul_one _

theorem finite_totPos_units_bounded_ratio : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (R : ℝ),
    {u : (𝓞 F)ˣ | TotPos F ((u : 𝓞 F) : F) ∧ ∀ σ τ : F →+* ℝ, σ ((u : 𝓞 F) : F) ≤ R * τ ((u : 𝓞 F) : F)}.Finite := by
  intro F _ _ _ R
  have hinj : Function.Injective (fun u : (𝓞 F)ˣ => ((u : 𝓞 F) : F)) := fun a b h =>
    Units.ext (RingOfIntegers.ext h)
  refine ((Embeddings.finite_of_norm_le F ℂ |R|).preimage hinj.injOn).subset ?_
  rintro u ⟨hu, hR⟩
  refine ⟨(u : 𝓞 F).isIntegral_coe, fun φ => ?_⟩
  obtain ⟨σ, rfl⟩ := (realEmbeddingsEquiv F).surjective φ
  have h := embedding_unit_le_abs hu hR σ
  change ‖((σ ((u : 𝓞 F) : F) : ℝ) : ℂ)‖ ≤ |R|
  rw [Complex.norm_real, Real.norm_of_nonneg (hu σ).le]
  exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteUnitsBoundedEmbeddingRatioStatement
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_units_bounded_embedding_ratio : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (R : ℝ),
    {u : (𝓞 F)ˣ | TotPos F ((u : 𝓞 F) : F) ∧ ∀ σ τ : F →+* ℝ, σ ((u : 𝓞 F) : F) ≤ R * τ ((u : 𝓞 F) : F)}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finite_totPos_units_bounded_ratio | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finite_totPos_units_bounded_ratio | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finite_totPos_units_bounded_ratio <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyPositiveBasisRatioBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyPositiveBasisRatioBound
set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem finite_realEmbeddings (F : Type) [Field F] [NumberField F] : Finite (F →+* ℝ) :=
  Finite.of_injective (fun σ : F →+* ℝ => (Complex.ofRealHom.comp σ : F →+* ℂ)) (by
    intro σ τ h
    ext x
    have := congrArg (fun f : F →+* ℂ => f x) h
    simpa using this)

theorem bounded_ratio_on_basis_cone : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ F), (∀ i, TotPos F (b i)) →
    ∃ R : ℝ, 0 < R ∧ ∀ x : F, (∀ i, 0 < b.repr x i) → ∀ σ τ : F →+* ℝ, σ x ≤ R * τ x := by
  intro F _ _ κ _ b hb
  classical
  haveI := finite_realEmbeddings F
  haveI : Fintype (F →+* ℝ) := Fintype.ofFinite _
  have hterm : ∀ (i : κ) (σ τ : F →+* ℝ), 0 < σ (b i) / τ (b i) := fun i σ τ => div_pos (hb i σ) (hb i τ)
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 1 + ∑ i, ∑ σ : F →+* ℝ, ∑ τ : F →+* ℝ, σ (b i) / τ (b i) := ⟨_, rfl⟩
  have hsum : 0 ≤ ∑ i, ∑ σ : F →+* ℝ, ∑ τ : F →+* ℝ, σ (b i) / τ (b i) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun τ _ => (hterm i σ τ).le
  have hR : 0 < R := by rw [hRdef]; linarith
  have hle : ∀ (i : κ) (σ τ : F →+* ℝ), σ (b i) ≤ R * τ (b i) := by
    intro i σ τ
    have h1 : σ (b i) / τ (b i) ≤ ∑ τ' : F →+* ℝ, σ (b i) / τ' (b i) :=
      Finset.single_le_sum (f := fun τ' : F →+* ℝ => σ (b i) / τ' (b i)) (fun τ' _ => (hterm i σ τ').le) (Finset.mem_univ τ)
    have h2 : ∑ τ' : F →+* ℝ, σ (b i) / τ' (b i) ≤ ∑ σ' : F →+* ℝ, ∑ τ' : F →+* ℝ, σ' (b i) / τ' (b i) :=
      Finset.single_le_sum (f := fun σ' : F →+* ℝ => ∑ τ' : F →+* ℝ, σ' (b i) / τ' (b i))
        (fun σ' _ => Finset.sum_nonneg fun τ' _ => (hterm i σ' τ').le) (Finset.mem_univ σ)
    have h3 : ∑ σ' : F →+* ℝ, ∑ τ' : F →+* ℝ, σ' (b i) / τ' (b i) ≤ ∑ j, ∑ σ' : F →+* ℝ, ∑ τ' : F →+* ℝ, σ' (b j) / τ' (b j) :=
      Finset.single_le_sum (f := fun j => ∑ σ' : F →+* ℝ, ∑ τ' : F →+* ℝ, σ' (b j) / τ' (b j))
        (fun j _ => Finset.sum_nonneg fun σ' _ => Finset.sum_nonneg fun τ' _ => (hterm j σ' τ').le) (Finset.mem_univ i)
    have h4 : σ (b i) / τ (b i) ≤ R := by rw [hRdef]; linarith
    exact (div_le_iff₀ (hb i τ)).1 h4
  refine ⟨R, hR, fun x hx σ τ => ?_⟩
  have hrep : ∀ ρ : F →+* ℝ, ρ x = ∑ i, (b.repr x i : ℝ) * ρ (b i) := by
    intro ρ
    conv_lhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
  rw [hrep σ, hrep τ, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hc : (0 : ℝ) < (b.repr x i : ℝ) := by exact_mod_cast hx i
  calc (b.repr x i : ℝ) * σ (b i) ≤ (b.repr x i : ℝ) * (R * τ (b i)) := mul_le_mul_of_nonneg_left (hle i σ τ) hc.le
    _ = R * ((b.repr x i : ℝ) * τ (b i)) := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyPositiveBasisRatioBoundStatement
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totally_positive_basis_ratio_bound : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ F), (∀ i, TotPos F (b i)) →
    ∃ R : ℝ, 0 < R ∧ ∀ x : F, (∀ i, 0 < b.repr x i) → ∀ σ τ : F →+* ℝ, σ x ≤ R * τ x := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.bounded_ratio_on_basis_cone | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.bounded_ratio_on_basis_cone | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.bounded_ratio_on_basis_cone <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ShintaniConeDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ShintaniConeDecomposition
set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem sum_equivFin_symm {F M : Type} [AddCommMonoid M] (s : Finset F) (f : F → M) :
    ∑ i : Fin s.card, f (s.equivFin.symm i : F) = ∑ y ∈ s, f y := by
  rw [← Finset.sum_coe_sort s f]
  exact Equiv.sum_comp s.equivFin.symm (fun y : s => f (y : F))

theorem openCone_equivFin {F : Type} [Field F] [CharZero F] (s : Finset F) :
    openCone (fun i : Fin s.card => (s.equivFin.symm i : F)) = coneOn s := by
  classical
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun y => if h : y ∈ s then t (s.equivFin ⟨y, h⟩) else 1, ?_, ?_⟩
    · intro y hy
      simp only [dif_pos hy]
      exact ht _
    · rw [← sum_equivFin_symm s (fun y => (if h : y ∈ s then t (s.equivFin ⟨y, h⟩) else 1 : ℚ) • y)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hm : (s.equivFin.symm i : F) ∈ s := (s.equivFin.symm i).2
      simp only [dif_pos hm, Subtype.coe_eta, Equiv.apply_symm_apply]
      rw [Rat.smul_def]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun i => t (s.equivFin.symm i : F), fun i => ht _ (s.equivFin.symm i).2, ?_⟩
    rw [← sum_equivFin_symm s (fun y => t y • y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Rat.smul_def]

theorem tile_family {F : Type} [Field F] [NumberField F] (P : Set F) (Q : Set F → Prop) (C : Set F) (h : Tile P Q C) :
    (0 : F) ∉ C →
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), (∀ c, 0 < r c) ∧
      (∀ c, LinearIndependent ℚ (v c)) ∧ (∀ c i, v c i ∈ P) ∧ (∀ c, openCone (v c) ⊆ C) ∧
      ∀ x ∈ C, ∃! c, x ∈ openCone (v c) := by
  induction h with
  | empty =>
    intro _
    exact ⟨Empty, inferInstance, fun c => c.elim, fun c => c.elim, fun c => c.elim, fun c => c.elim,
      fun c => c.elim, fun c => c.elim, fun x hx => hx.elim⟩
  | cone s hli hP hQ =>
    intro h0
    have hcone := openCone_equivFin s
    refine ⟨Unit, inferInstance, fun _ => s.card, fun _ i => (s.equivFin.symm i : F), ?_, ?_, ?_, ?_, ?_⟩
    · intro _
      refine Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ?_)
      rintro rfl
      exact h0 ⟨fun _ => 0, by simp, by simp⟩
    · intro _
      have hinj : Function.Injective (fun i : Fin s.card => (⟨(s.equivFin.symm i : F), (s.equivFin.symm i).2⟩ : (s : Set F))) := by
        intro i j hij
        exact s.equivFin.symm.injective (Subtype.ext (congrArg Subtype.val hij))
      exact LinearIndependent.comp hli _ hinj
    · intro _ i
      exact hP (s.equivFin.symm i).2
    · intro _
      exact hcone.le
    · intro x hx
      exact ⟨(), hcone.ge hx, fun _ _ => rfl⟩
  | @union A B _ _ hAB ihA ihB =>
    intro h0
    obtain ⟨ι₁, f₁, r₁, v₁, hr₁, hl₁, hp₁, hs₁, hu₁⟩ := ihA (fun h => h0 (Or.inl h))
    obtain ⟨ι₂, f₂, r₂, v₂, hr₂, hl₂, hp₂, hs₂, hu₂⟩ := ihB (fun h => h0 (Or.inr h))
    refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim r₁ r₂,
      fun c => match c with
        | Sum.inl a => v₁ a
        | Sum.inr b => v₂ b, ?_, ?_, ?_, ?_, ?_⟩
    · rintro (a | b)
      · exact hr₁ a
      · exact hr₂ b
    · rintro (a | b)
      · exact hl₁ a
      · exact hl₂ b
    · rintro (a | b) i
      · exact hp₁ a i
      · exact hp₂ b i
    · rintro (a | b)
      · exact (hs₁ a).trans Set.subset_union_left
      · exact (hs₂ b).trans Set.subset_union_right
    · rintro x (hx | hx)
      · obtain ⟨a, ha, hu⟩ := hu₁ x hx
        refine ⟨Sum.inl a, ha, ?_⟩
        rintro (a' | b') h'
        · exact congrArg Sum.inl (hu a' h')
        · exact (Set.disjoint_left.mp hAB hx (hs₂ b' h')).elim
      · obtain ⟨b, hb, hu⟩ := hu₂ x hx
        refine ⟨Sum.inr b, hb, ?_⟩
        rintro (a' | b') h'
        · exact (Set.disjoint_left.mp hAB (hs₁ a' h') hx).elim
        · exact congrArg Sum.inr (hu b' h')

theorem tile_family_closed : ∀ {F : Type} [Field F] [NumberField F] (P : Set F) (Q : Set F → Prop) (C : Set F), Tile P Q C → (0 : F) ∉ C →
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), (∀ c, 0 < r c) ∧
      (∀ c, LinearIndependent ℚ (v c)) ∧ (∀ c i, v c i ∈ P) ∧ (∀ c, openCone (v c) ⊆ C) ∧
      ∀ x ∈ C, ∃! c, x ∈ openCone (v c) :=
  fun P Q C h => tile_family P Q C h

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ShintaniConeDecompositionStatement
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_cone_decomposition : ∀ {F : Type} [Field F] [NumberField F] (P : Set F) (Q : Set F → Prop) (C : Set F), Tile P Q C → (0 : F) ∉ C →
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), (∀ c, 0 < r c) ∧
      (∀ c, LinearIndependent ℚ (v c)) ∧ (∀ c i, v c i ∈ P) ∧ (∀ c, openCone (v c) ⊆ C) ∧
      ∀ x ∈ C, ∃! c, x ∈ openCone (v c) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.tile_family_closed | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.tile_family_closed | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.tile_family_closed <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.UniqueReducedOrbitRepresentative
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.UniqueReducedOrbitRepresentative
namespace GlobalTheory.CompanionTheory.SiegelKlingen

theorem exists_unique_minimal_translate :
    ∀ {G M : Type} [Group G] [Monoid M] (φ : G →* M) (f : G →* ℝ), (∀ g, 0 < f g) →
    Function.Injective f → ∀ (D : Set M),
    {g : G | ∃ x ∈ D, φ g * x ∈ D}.Finite → ∀ (x : M), (∃ g, φ g * x ∈ D) →
    ∃! g, φ g * x ∈ {y ∈ D | ∀ g' : G, f g' < 1 → φ g' * y ∉ D} := by
  intro G M _ _ φ f hpos hinj D hfin x ⟨g0, hg0⟩
  have key : ∀ a b : G, φ (a * b⁻¹) * (φ b * x) = φ a * x := by
    intro a b
    rw [← mul_assoc, ← map_mul, inv_mul_cancel_right]
  have hS : {g : G | φ g * x ∈ D}.Finite := by
    refine (hfin.image (fun h => h * g0)).subset ?_
    intro g hg
    exact ⟨g * g0⁻¹, ⟨φ g0 * x, hg0, by rw [key]; exact hg⟩, inv_mul_cancel_right g g0⟩
  obtain ⟨g, hgS, hmin⟩ := Set.exists_min_image _ f hS ⟨g0, hg0⟩
  refine ⟨g, ⟨hgS, fun g' hg' hD => ?_⟩, ?_⟩
  · have hmem : φ (g' * g) * x ∈ D := by rwa [map_mul, mul_assoc]
    have h1 := hmin _ hmem
    rw [map_mul] at h1
    have hp := hpos g
    nlinarith
  · rintro g2 ⟨hg2, hmin2⟩
    have h1 : 1 ≤ f (g * g2⁻¹) := not_lt.1 fun hlt => hmin2 _ hlt (by rw [key]; exact hgS)
    rw [map_mul, map_inv] at h1
    have hp2 := hpos g2
    have h3 := mul_le_mul_of_nonneg_right h1 hp2.le
    rw [one_mul, inv_mul_cancel_right₀ hp2.ne'] at h3
    exact hinj (le_antisymm h3 (hmin g2 hg2))

end GlobalTheory.CompanionTheory.SiegelKlingen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.UniqueReducedOrbitRepresentativeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unique_reduced_orbit_representative : ∀ {G M : Type} [Group G] [Monoid M] (φ : G →* M) (f : G →* ℝ), (∀ g, 0 < f g) → Function.Injective f → ∀ (D : Set M),
    {g : G | ∃ x ∈ D, φ g * x ∈ D}.Finite → ∀ (x : M), (∃ g, φ g * x ∈ D) →
    ∃! g, φ g * x ∈ {y ∈ D | ∀ g' : G, f g' < 1 → φ g' * y ∉ D} := by
  first | exact @GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate | exact GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate | (intros; apply GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsShintaniConeDomain
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem exists_coneDomain : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), IsConeDomain 𝔣 r v := by
  intro F _ _ _ 𝔣 h𝔣
  classical
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_congruence_unit_balancing_embeddings F 𝔣 h𝔣
  obtain ⟨κ, _, b, hbpos, hbcov⟩ := GlobalTheory.T.exists_totally_positive_basis_positive_coords F M
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.totally_positive_basis_ratio_bound F b hbpos

  obtain ⟨σ₁⟩ : Nonempty (F →+* ℝ) := by
    have w : InfinitePlace F := Classical.choice inferInstance
    exact ⟨w.embedding_of_isReal (IsTotallyReal.isReal w)⟩

  let G := ↥(congSubgroup 𝔣)
  let φ : G →* F := ((algebraMap (𝓞 F) F : 𝓞 F →+* F) : 𝓞 F →* F).comp ((Units.coeHom (𝓞 F)).comp (congSubgroup 𝔣).subtype)
  have hφ : ∀ g : G, φ g = (((g : (𝓞 F)ˣ) : 𝓞 F) : F) := fun g => rfl
  have hgpos : ∀ g : G, TotPos F (φ g) := fun g => g.2.2
  let f : G →* ℝ := (σ₁ : F →* ℝ).comp φ
  have hf : ∀ g : G, f g = σ₁ (φ g) := fun g => rfl
  have hfpos : ∀ g, 0 < f g := fun g => hgpos g σ₁
  have hφinj : Function.Injective φ := by
    intro g g' h
    apply Subtype.ext
    apply Units.ext
    exact RingOfIntegers.coe_injective h
  have hfinj : Function.Injective f := fun g g' h => hφinj (σ₁.injective h)
  let D : Set F := {x | ∀ i, 0 < b.repr x i}

  have hDpos : ∀ x ∈ D, TotPos F x := by
    intro x hx σ
    have hk : Nonempty κ := b.index_nonempty
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_pos (by exact_mod_cast hx i) (hbpos i σ)
  have hfin : {g : G | ∃ x ∈ D, φ g * x ∈ D}.Finite := by
    have hfin0 := GlobalTheory.T.finite_units_bounded_embedding_ratio F (R * R)
    refine Set.Finite.of_finite_image (f := fun g : G => (g : (𝓞 F)ˣ)) (hfin0.subset ?_) (Subtype.val_injective.injOn)
    rintro _ ⟨g, ⟨x, hx, hgx⟩, rfl⟩
    refine ⟨hgpos g, fun σ τ => ?_⟩
    have h1 := hR _ hgx σ τ
    have h2 := hR x hx τ σ
    have hxσ := hDpos x hx σ
    have hgτ := hgpos g τ
    rw [map_mul, map_mul] at h1
    have h3 : σ (φ g) * σ x ≤ (R * R * τ (φ g)) * σ x := by
      calc σ (φ g) * σ x ≤ R * (τ (φ g) * τ x) := h1
        _ ≤ R * (τ (φ g) * (R * σ x)) := by gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_right h3 hxσ
  let E : Set F := {y ∈ D | ∀ g' : G, f g' < 1 → φ g' * y ∉ D}
  let T := {g : G | ∃ x ∈ D, φ g * x ∈ D}
  let Λ : Set (F →ₗ[ℚ] ℚ) := (fun p : G × κ => (b.coord p.2).comp (LinearMap.mulLeft ℚ (φ p.1))) '' (T ×ˢ Set.univ)
  have hΛ : Λ.Finite := (hfin.prod Set.finite_univ).image _
  have hsign : ∀ (p q : ℚ), SignType.sign p = SignType.sign q → 0 < p → 0 < q := by
    intro p q h hp
    rw [sign_pos hp] at h
    exact sign_eq_one_iff.mp h.symm
  have htile : Tile ((posCone F : ConvexCone ℚ F) : Set F) (fun _ => True) E := by
    refine GlobalTheory.T.cone_tiling_by_sign_regions (posCone F) b hbpos Λ hΛ E (fun x hx => hx.1) ?_
    intro x y hx hy hs hxE
    refine ⟨hy, fun g' hg' hyD => ?_⟩
    refine hxE.2 g' hg' ?_
    have hgT : g' ∈ T := ⟨y, hy, hyD⟩
    intro i
    have := hs _ ⟨(g', i), ⟨hgT, trivial⟩, rfl⟩
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply, LinearMap.mulLeft_apply] at this
    exact hsign _ _ this.symm (hyD i)
  have h0 : (0 : F) ∉ E := by
    intro h
    have := hDpos 0 h.1 σ₁
    simp at this
  obtain ⟨ι, hι, r, v, hr, hli, hvP, hsub, hun⟩ := GlobalTheory.T.shintani_cone_decomposition _ _ E htile h0
  refine ⟨ι, hι, r, v, hr, hli, hvP, ?_⟩
  intro x hx

  obtain ⟨u, hu, hub⟩ := hM x hx
  have hxD : ∃ g : G, φ g * x ∈ D := by
    refine ⟨⟨u, hu⟩, hbcov _ ?_ hub⟩
    intro σ
    rw [map_mul]
    exact mul_pos (hu.2 σ) (hx σ)
  obtain ⟨g, hg, hguniq⟩ := GlobalTheory.T.unique_reduced_orbit_representative φ f hfpos hfinj D hfin x hxD
  obtain ⟨c, hc, hcuniq⟩ := hun _ hg
  refine ⟨(⟨g.1, g.2⟩, c), hc, ?_⟩
  rintro ⟨⟨u', hu'⟩, c'⟩ hp
  have hp' : φ ⟨u', hu'⟩ * x ∈ openCone (v c') := hp
  have hg' : (⟨u', hu'⟩ : G) = g := hguniq _ (hsub c' hp')
  have hc' : c' = c := by
    apply hcuniq
    rw [← hg']
    exact hp'
  subst hc'
  have := congrArg Subtype.val hg'
  simp only at this
  simp [this]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsShintaniConeDomainStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shintani_cone_domain : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
  ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), IsConeDomain 𝔣 r v := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_coneDomain | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_coneDomain | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_coneDomain <;> assumption)
end
