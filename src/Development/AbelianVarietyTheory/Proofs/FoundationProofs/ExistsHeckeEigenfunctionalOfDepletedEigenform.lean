module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralHeckeTAdjoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralHeckeUAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsRightGamma0CosetDecompositionHeckeU
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsRightGamma0CosetDecompositionHeckeU
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.RightRepU

lemma adj_repL (L l : ℕ) (j : Fin l) :
    (repL L l (some j)).adjugate = !![(1:ℤ), 0; -((L:ℤ) * ((j:ℕ):ℤ)), (l:ℤ)] := by
  simp [repL, Matrix.adjugate_fin_two_of]

lemma dvd_10 {L : ℕ} (γ : Gamma0 L) : (L:ℤ) ∣ ((γ : SL(2,ℤ)) : M2) 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.1 γ.2)

lemma not_dvd_00 {L l : ℕ} (hl : l.Prime) (hlL : l ∣ L) (γ : Gamma0 L) :
    ¬ (l:ℤ) ∣ ((γ : SL(2,ℤ)) : M2) 0 0 := by
  intro h
  have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2,ℤ))
  rw [Matrix.det_fin_two] at hdet
  have hc' : (l:ℤ) ∣ ((γ : SL(2,ℤ)) : M2) 1 0 := dvd_trans (Int.natCast_dvd_natCast.2 hlL) (dvd_10 γ)
  have h1 : (l:ℤ) ∣ 1 := by
    rw [← hdet]; exact dvd_sub (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right hc' _)
  have := Int.eq_one_of_dvd_one (by positivity) h1
  exact hl.one_lt.ne' (by exact_mod_cast this)

end GlobalTheory.EisM.RightRepU

namespace GlobalTheory.EisM.RightRepU

theorem rrep (L l : ℕ) (hl : l.Prime) (hlL : l ∣ L) (hL : 0 < L) :
    RRep L (DU L l) (fun j : Fin l => (repL L l (some j)).adjugate) := by
  haveI := Fact.mk hl
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have hpr : Prime (l:ℤ) := Nat.prime_iff_prime_int.mp hl
  have hlpos : (0:ℤ) < l := by exact_mod_cast hl.pos
  simp only [RRep, adj_repL]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨j, γ⟩ -
    have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2,ℤ))
    refine ⟨?_, ?_, ?_⟩
    · simp only [Matrix.det_mul]
      rw [hdet, Matrix.det_fin_two_of]; ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_neg.2 (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)) (dvd_mul_of_dvd_right (dvd_10 γ) _)
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using not_dvd_00 hl hlL γ
  · rintro ⟨j, γ⟩ - ⟨j', γ'⟩ - h
    simp only at h
    have e := fun r s => congrArg (fun M : M2 => M r s) h
    have h00 := e 0 0
    have h01 := e 0 1
    have h10 := e 1 0
    have h11 := e 1 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
    obtain ⟨c1, hc1⟩ := dvd_10 γ
    obtain ⟨c1', hc1'⟩ := dvd_10 γ'
    have hLz : (0:ℤ) < L := by exact_mod_cast hL
    have hk : (L:ℤ) * ((((j':ℕ):ℤ) - (j:ℕ)) * ((γ : SL(2,ℤ)) : M2) 0 0) = (L:ℤ) * ((l:ℤ) * (c1' - c1)) := by
      rw [hc1, hc1', ← h00] at h10
      linear_combination h10
    have hk2 := mul_left_cancel₀ hLz.ne' hk
    have hdv : (l:ℤ) ∣ (((j':ℕ):ℤ) - (j:ℕ)) * ((γ : SL(2,ℤ)) : M2) 0 0 := ⟨_, hk2⟩
    have hjj := (hpr.dvd_or_dvd hdv).resolve_right (not_dvd_00 hl hlL γ)
    have hj0 : ((j':ℕ):ℤ) - (j:ℕ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd hjj
      have := j.isLt; have := j'.isLt
      rw [abs_lt]; constructor <;> omega
    have hjeq : j = j' := Fin.ext (by omega)
    subst hjeq
    have h10' : ((γ : SL(2,ℤ)) : M2) 1 0 = ((γ' : SL(2,ℤ)) : M2) 1 0 := by
      rw [← h00] at h10
      exact mul_left_cancel₀ hlpos.ne' (by linear_combination h10)
    have h11' : ((γ : SL(2,ℤ)) : M2) 1 1 = ((γ' : SL(2,ℤ)) : M2) 1 1 := by
      rw [← h01] at h11
      exact mul_left_cancel₀ hlpos.ne' (by linear_combination h11)
    refine Prod.ext rfl (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ (fun r s => ?_)))
    fin_cases r <;> fin_cases s
    · exact h00
    · exact h01
    · exact h10'
    · exact h11'
  · rintro δ ⟨hdet, hc, ha⟩
    rw [Matrix.det_fin_two] at hdet
    obtain ⟨c1, hc1⟩ := hc
    obtain ⟨L1, hL1⟩ := hlL
    have hLl : (L:ℤ) = l * L1 := by rw [hL1]; push_cast; ring
    have hd : (l:ℤ) ∣ δ 1 1 := by
      have : (l:ℤ) ∣ δ 0 0 * δ 1 1 :=
        ⟨1 + L1 * c1 * δ 0 1, by linear_combination hdet + δ 0 1 * hc1 + δ 0 1 * c1 * hLl⟩
      exact (hpr.dvd_or_dvd this).resolve_left ha
    obtain ⟨d1, hd1⟩ := hd
    have ha0 : ((δ 0 0 : ℤ) : ZMod l) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨x, hx⟩ : ∃ x : ZMod l, x = -(c1 : ZMod l) * ((δ 0 0 : ℤ) : ZMod l)⁻¹ := ⟨_, rfl⟩
    let j : Fin l := ⟨x.val, ZMod.val_lt x⟩
    have hj : (l:ℤ) ∣ c1 + ((j:ℕ):ℤ) * δ 0 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp only [j, ZMod.natCast_val, ZMod.cast_id', id]
      rw [hx, mul_assoc, inv_mul_cancel₀ ha0]; ring
    obtain ⟨m, hm⟩ := hj
    let M : M2 := !![δ 0 0, δ 0 1; (L:ℤ) * m, d1 + L1 * ((j:ℕ):ℤ) * δ 0 1]
    have hM : M.det = 1 := by
      rw [Matrix.det_fin_two_of]
      apply mul_left_cancel₀ hlpos.ne'
      linear_combination hdet + δ 0 1 * hc1 + δ 0 1 * L * hm - ((j:ℕ):ℤ) * δ 0 0 * δ 0 1 * hLl - δ 0 0 * hd1
    let g : SL(2,ℤ) := ⟨M, hM⟩
    have hmem : g ∈ Gamma0 L := by
      rw [Gamma0_mem]; simp [g, M]
    refine ⟨(j, ⟨g, hmem⟩), trivial, ?_⟩
    ext r s
    fin_cases r <;> fin_cases s
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination -(L:ℤ) * hm - hc1
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination -hd1 - ((j:ℕ):ℤ) * δ 0 1 * hLl

end GlobalTheory.EisM.RightRepU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsRightGamma0CosetDecompositionHeckeUStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRightGamma0CosetDecomposition_heckeU : ∀ L l : ℕ, 0 < L → l.Prime → l ∣ L → RRep L (DU L l) (fun j : Fin l => (repL L l (some j)).adjugate) := by
  first | exact @GlobalTheory.EisM.RightRepU.rrep | exact GlobalTheory.EisM.RightRepU.rrep | (intros; apply GlobalTheory.EisM.RightRepU.rrep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralHeckeUAdjoint
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem adjoint_U : ∀ (k L N l : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → l.Prime → l ∣ L → ¬ l ∣ N → Wt L ρ → CF k L (ch ε) h → MF k L (ch ε) a → pet k ρ (qs h) (qs (Uo l a)) = pet k ρ (fun τ => ∑ j : Fin l, slz k (repL L l (some j)) (qs h) τ) (qs a) := by
  intro k L N l ε ρ h a hk hL hNL hl hlL hlN hW hh ha
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNL hL
  have hcop : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hl).2 hlN
  have hpos : 0 < l := hl.pos
  obtain ⟨-, hUa⟩ := GlobalTheory.T.qExpansion_heckeU_eq_sum_slash k l a hk hpos ha.1
  have hcontH : Continuous (qs h) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hh.1.1).2
  have hcontA : Continuous (qs a) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha.1).2
  have hModA : Mod (qs a) := GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth a ha.1
  have hdet : ∀ j : Fin l, (repU l j).det = l := by
    intro j; simp [repU, Matrix.det_fin_two]
  have hint : ∀ i : Fin l, Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * slz k (repU l i) (qs a) τ * (τ.im : ℂ) ^ k)) := by
    intro i
    have hd : 0 < (repU l i).det := by rw [hdet]; exact_mod_cast hpos
    exact GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L L N ε h ρ _ hk hL hNL hW hh
      (((GlobalTheory.T.slashIntMatrixPosDet_properties k (qs a) hk).2.2.2.1 _ hd hcontA).aestronglyMeasurable)
      ((GlobalTheory.T.hasModerateGrowth_algebra_slash_stable).2.2 (qs a) k _ hd (by simp [repU]) hModA)
  have key := GlobalTheory.T.petersson_doubleCoset_adjoint k L N l ε ρ (DU L l) (Fin l) (Fin l) (repU l)
    (fun j => (repL L l (some j)).adjugate) (qs h) (qs a) hk hN hNL hpos hcop hW
    (by
      intro δ hδ
      obtain ⟨h1, h2, -⟩ := hδ
      exact ⟨h1, (Int.natCast_dvd_natCast.2 hNL).trans h2⟩)
    ((GlobalTheory.T.heckeU_leftRepresentatives_level_change L l hl).1 hlL) (GlobalTheory.T.isRightGamma0CosetDecomposition_heckeU L l hL hl hlL) hh.1.2 ha.2 hcontH hcontA hint
  have e1 : qs (Uo l a) = hsum k (ch ε) (repU l) (qs a) := by
    funext τ
    rw [hUa τ]
    simp [hsum, repU, ch]
  have e2 : (fun τ => ∑ j : Fin l, slz k (repL L l (some j)) (qs h) τ) =
      (fun τ => ∑ j, ch ε⁻¹ ((fun j => (repL L l (some j)).adjugate) j 0 0) *
        slz k ((fun j => (repL L l (some j)).adjugate) j).adjugate (qs h) τ) := by
    funext τ
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [repL, ch, Matrix.adjugate_fin_two_of]
  rw [e1, e2]
  exact key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralHeckeUAdjointStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfPeterssonIntegral_heckeU_adjoint : ∀ (k L N l : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → l.Prime → l ∣ L → ¬ l ∣ N → Wt L ρ → CF k L (ch ε) h → MF k L (ch ε) a → pet k ρ (qs h) (qs (Uo l a)) = pet k ρ (fun τ => ∑ j : Fin l, slz k (repL L l (some j)) (qs h) τ) (qs a) := by
  first | exact @GlobalTheory.adjoint_U | exact GlobalTheory.adjoint_U | (intros; apply GlobalTheory.adjoint_U <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralWeightedLinearForms
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralWeightedLinearForms
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem qs_lin (a b : ℕ → ℂ) (x y : ℂ) (ha : PolyB a) (hb : PolyB b) (τ : ℍ) :
    qs (x • a + y • b) τ = x * qs a τ + y * qs b τ := by
  have sa : Summable fun n : ℕ => a n * cexp (2 * π * Complex.I * n * τ) :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).1 τ).of_norm
  have sb : Summable fun n : ℕ => b n * cexp (2 * π * Complex.I * n * τ) :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb).1 τ).of_norm
  unfold qs
  rw [← tsum_mul_left, ← tsum_mul_left, ← (sa.mul_left x).tsum_add (sb.mul_left y)]
  congr 1; funext n; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem pet_linear : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ), 1 ≤ k → 0 < L' → N ∣ L' → Wt L ρ → (∀ (h a b : ℕ → ℂ) (x y : ℂ), CF k L' (ch ε) h → PolyB a → PolyB b → pet k ρ (qs h) (qs (x • a + y • b)) = x * pet k ρ (qs h) (qs a) + y * pet k ρ (qs h) (qs b)) ∧ ∀ (h h' a : ℕ → ℂ) (x y : ℂ), CF k L' (ch ε) h → CF k L' (ch ε) h' → PolyB a → pet k ρ (fun τ => x * qs h τ + y * qs h' τ) (qs a) = conj x * pet k ρ (qs h) (qs a) + conj y * pet k ρ (qs h') (qs a) := by
  intro k L L' N ε ρ hk hL' hN hW
  have intg : ∀ h a : ℕ → ℂ, CF k L' (ch ε) h → PolyB a →
      Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * qs a τ * (τ.im : ℂ) ^ k)) := by
    intro h a hh ha
    exact GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L L' N ε h ρ (qs a) hk hL' hN hW hh
      (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).2.aestronglyMeasurable (GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth a ha)
  refine ⟨?_, ?_⟩
  · intro h a b x y hh ha hb
    unfold pet
    have e : (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * qs (x • a + y • b) τ * (τ.im : ℂ) ^ k)) =
        fun τ => x * ((ρ τ : ℂ) * (conj (qs h τ) * qs a τ * (τ.im : ℂ) ^ k)) +
          y * ((ρ τ : ℂ) * (conj (qs h τ) * qs b τ * (τ.im : ℂ) ^ k)) := by
      funext τ; rw [qs_lin a b x y ha hb τ]; ring
    rw [e, integral_add ((intg h a hh ha).const_mul x) ((intg h b hh hb).const_mul y),
      integral_const_mul, integral_const_mul]
  · intro h h' a x y hh hh' ha
    unfold pet
    have e : (fun τ : ℍ => (ρ τ : ℂ) * (conj (x * qs h τ + y * qs h' τ) * qs a τ * (τ.im : ℂ) ^ k)) =
        fun τ => conj x * ((ρ τ : ℂ) * (conj (qs h τ) * qs a τ * (τ.im : ℂ) ^ k)) +
          conj y * ((ρ τ : ℂ) * (conj (qs h' τ) * qs a τ * (τ.im : ℂ) ^ k)) := by
      funext τ; simp only [map_add (f := _), map_mul]; ring
    rw [e, integral_add ((intg h a hh ha).const_mul _) ((intg h' a hh' ha).const_mul _),
      integral_const_mul, integral_const_mul]

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralWeightedLinearFormsStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfPeterssonIntegralWeighted_linear_forms : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ), 1 ≤ k → 0 < L' → N ∣ L' → Wt L ρ → (∀ (h a b : ℕ → ℂ) (x y : ℂ), CF k L' (ch ε) h → PolyB a → PolyB b → pet k ρ (qs h) (qs (x • a + y • b)) = x * pet k ρ (qs h) (qs a) + y * pet k ρ (qs h) (qs b)) ∧ ∀ (h h' a : ℕ → ℂ) (x y : ℂ), CF k L' (ch ε) h → CF k L' (ch ε) h' → PolyB a → pet k ρ (fun τ => x * qs h τ + y * qs h' τ) (qs a) = conj x * pet k ρ (qs h) (qs a) + conj y * pet k ρ (qs h') (qs a) := by
  first | exact @GlobalTheory.EisM.pet_linear | exact GlobalTheory.EisM.pet_linear | (intros; apply GlobalTheory.EisM.pet_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerHeckeVEigenform
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftGamma0CosetDecompositionHeckeRepLowerLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftGamma0CosetDecompositionHeckeRepLowerLevel
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma repL_det (L q : ℕ) (i : Option (Fin q)) : (repL L q i).det = q := by
  cases i <;> simp [repL, Matrix.det_fin_two_of]

lemma gamma0_lower_dvd {L : ℕ} (γ : Gamma0 L) : (L : ℤ) ∣ ((γ : SL(2, ℤ)) : M2) 1 0 := by
  have := Gamma0_mem.mp γ.2
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast this)

lemma exists_kernel_param {K : Type*} [Field K] (a b c d l : K) (hl : l ≠ 0)
    (hdet : a * d - b * c = 0) (hbd : b ≠ 0 ∨ d ≠ 0) : ∃ u, a = l * u * b ∧ c = l * u * d := by
  by_cases hd : d = 0
  · have hb : b ≠ 0 := hbd.resolve_right (by simpa using hd)
    refine ⟨a / (l * b), by field_simp, ?_⟩
    subst hd
    have : b * c = 0 := by linear_combination -hdet
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hb
    · simp [h]
  · refine ⟨c / (l * d), ?_, by field_simp⟩
    field_simp
    linear_combination hdet

theorem repL_LRep : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → LRep L (DT L q) (repL L q) := by
  intro L q hq hqL
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hqLZ : ¬ (q : ℤ) ∣ L := by exact_mod_cast hqL
  haveI := Fact.mk hq
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨γ, i⟩ -
    refine ⟨?_, ?_⟩
    · simp [Matrix.det_mul, repL_det]
    · have h := gamma0_lower_dvd γ
      cases i with
      | none => simpa [repL, Matrix.mul_apply, Fin.sum_univ_two] using h
      | some j =>
        simp only [repL, Matrix.mul_apply, Fin.sum_univ_two]
        simp
        exact dvd_add (dvd_mul_of_dvd_left h _) (Dvd.dvd.mul_left (dvd_mul_right _ _) _)
  · rintro ⟨γ, i⟩ - ⟨γ', i'⟩ - h
    dsimp only at h
    have hd := (γ : SL(2, ℤ)).2
    have hd' := (γ' : SL(2, ℤ)).2
    rw [Matrix.det_fin_two] at hd hd'
    have e00 := congrFun (congrFun h 0) 0
    have e01 := congrFun (congrFun h 0) 1
    have e10 := congrFun (congrFun h 1) 0
    have e11 := congrFun (congrFun h 1) 1
    have hq0' : q ≠ 0 := hq.ne_zero
    have hq1 : ¬ (q : ℤ) ∣ 1 := hqZ.not_dvd_one
    rcases i with _ | j <;> rcases i' with _ | j' <;>
      simp [repL, Matrix.mul_apply, Fin.sum_univ_two, hq0'] at e00 e01 e10 e11
    · refine Prod.ext (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)) rfl
      fin_cases i <;> fin_cases j <;> simp <;> assumption
    · exact absurd (Dvd.intro (((γ' : SL(2, ℤ)) : M2) 0 0 * ((γ : SL(2, ℤ)) : M2) 1 1 -
          ((γ : SL(2, ℤ)) : M2) 0 1 * ((γ' : SL(2, ℤ)) : M2) 1 0)
        (by linear_combination hd' + ((γ' : SL(2, ℤ)) : M2) 0 0 * e11 - ((γ' : SL(2, ℤ)) : M2) 1 0 * e01)) hq1
    · exact absurd (Dvd.intro (((γ : SL(2, ℤ)) : M2) 0 0 * ((γ' : SL(2, ℤ)) : M2) 1 1 -
          ((γ' : SL(2, ℤ)) : M2) 0 1 * ((γ : SL(2, ℤ)) : M2) 1 0)
        (by linear_combination hd - ((γ : SL(2, ℤ)) : M2) 0 0 * e11 + ((γ : SL(2, ℤ)) : M2) 1 0 * e01)) hq1
    · have h0 : (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ) * ((γ : SL(2, ℤ)) : M2) 0 1 :=
        Dvd.intro (((γ' : SL(2, ℤ)) : M2) 0 0 - ((γ : SL(2, ℤ)) : M2) 0 0)
          (by linear_combination -e00 + ((L : ℤ) * ((j' : ℕ) : ℤ)) * e01)
      have h1 : (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ) * ((γ : SL(2, ℤ)) : M2) 1 1 :=
        Dvd.intro (((γ' : SL(2, ℤ)) : M2) 1 0 - ((γ : SL(2, ℤ)) : M2) 1 0)
          (by linear_combination -e10 + ((L : ℤ) * ((j' : ℕ) : ℤ)) * e11)
      have hjj : (q : ℤ) ∣ ((j : ℕ) - (j' : ℕ) : ℤ) := by
        by_contra hn
        have hLj : ¬ (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ) := fun hh =>
          (hqZ.dvd_or_dvd hh).elim hqLZ hn
        have a0 := (hqZ.dvd_or_dvd h0).resolve_left hLj
        have a1 := (hqZ.dvd_or_dvd h1).resolve_left hLj
        apply hq1
        rw [← hd]
        exact (Dvd.dvd.mul_left a1 _).sub (Dvd.dvd.mul_right a0 _)
      have hj := j.isLt
      have hj' := j'.isLt
      have hz := Int.eq_zero_of_abs_lt_dvd hjj (abs_sub_lt_iff.mpr ⟨by omega, by omega⟩)
      have hjeq : j = j' := Fin.ext (by omega)
      subst hjeq
      refine Prod.ext (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i k => ?_)) rfl
      have f00 : ((γ : SL(2, ℤ)) : M2) 0 0 = ((γ' : SL(2, ℤ)) : M2) 0 0 :=
        mul_right_cancel₀ hq0 (by linear_combination e00 - ((L : ℤ) * ((j : ℕ) : ℤ)) * e01)
      have f10 : ((γ : SL(2, ℤ)) : M2) 1 0 = ((γ' : SL(2, ℤ)) : M2) 1 0 :=
        mul_right_cancel₀ hq0 (by linear_combination e10 - ((L : ℤ) * ((j : ℕ) : ℤ)) * e11)
      fin_cases i <;> fin_cases k <;> simp <;> assumption
  · rintro δ ⟨hdet, hL⟩
    rw [Matrix.det_fin_two] at hdet
    by_cases hbd : (q : ℤ) ∣ δ 0 1 ∧ (q : ℤ) ∣ δ 1 1
    · obtain ⟨⟨b', hb⟩, ⟨d', hd⟩⟩ := hbd
      have hdet1 : (!![δ 0 0, b'; δ 1 0, d'] : M2).det = 1 := by
        rw [Matrix.det_fin_two_of]
        apply mul_left_cancel₀ hq0
        rw [hb, hd] at hdet
        linear_combination hdet
      let g : SL(2, ℤ) := ⟨_, hdet1⟩
      have hg : g ∈ Gamma0 L := by
        rw [Gamma0_mem]
        have : ((δ 1 0 : ℤ) : ZMod L) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hL
        simpa [g] using this
      refine ⟨(⟨g, hg⟩, none), trivial, ?_⟩
      ext i k
      fin_cases i <;> fin_cases k <;> simp [g, repL, Matrix.mul_apply, Fin.sum_univ_two, hb, hd] <;> ring
    · have hu : ∃ u : ZMod q, ((δ 0 0 : ℤ) : ZMod q) = (L : ZMod q) * u * ((δ 0 1 : ℤ) : ZMod q) ∧
          ((δ 1 0 : ℤ) : ZMod q) = (L : ZMod q) * u * ((δ 1 1 : ℤ) : ZMod q) := by
        apply exists_kernel_param
        · rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqL
        · have := congrArg (fun x : ℤ => (x : ZMod q)) hdet
          simpa using this
        · by_contra hn
          push_neg at hn
          exact hbd ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn.1,
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn.2⟩
      obtain ⟨u, hu0, hu1⟩ := hu
      set j : Fin q := ⟨u.val, ZMod.val_lt u⟩ with hjdef
      have hju : (((j : ℕ) : ℤ) : ZMod q) = u := by simp [hjdef]
      obtain ⟨x, hx⟩ : (q : ℤ) ∣ δ 0 0 - L * (j : ℕ) * δ 0 1 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast at hju ⊢
        rw [hju, hu0]; ring
      obtain ⟨z, hz⟩ : (q : ℤ) ∣ δ 1 0 - L * (j : ℕ) * δ 1 1 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast at hju ⊢
        rw [hju, hu1]; ring
      have hcop : IsCoprime (L : ℤ) (q : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqL).symm
      have hLz : (L : ℤ) ∣ z := by
        apply hcop.dvd_of_dvd_mul_left
        rw [← hz]
        exact dvd_sub hL (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _)
      have hdet1 : (!![x, δ 0 1; z, δ 1 1] : M2).det = 1 := by
        rw [Matrix.det_fin_two_of]
        apply mul_left_cancel₀ hq0
        linear_combination -(δ 1 1) * hx + δ 0 1 * hz + hdet
      let g : SL(2, ℤ) := ⟨_, hdet1⟩
      have hg : g ∈ Gamma0 L := by
        rw [Gamma0_mem]
        have : ((z : ℤ) : ZMod L) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hLz
        simpa [g] using this
      refine ⟨(⟨g, hg⟩, some j), trivial, ?_⟩
      ext i k
      fin_cases i <;> fin_cases k <;> simp [g, repL, Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | linear_combination -hx | linear_combination -hz

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftGamma0CosetDecompositionHeckeRepLowerLevelStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepLowerLevel : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → LRep L (DT L q) (repL L q) := by
  first | exact @GlobalTheory.EisM.repL_LRep | exact GlobalTheory.EisM.repL_LRep | (intros; apply GlobalTheory.EisM.repL_LRep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerHeckeVEigenform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

private theorem slz_const_mul (k : ℕ) (δ : M2) (c : ℂ) (g : ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun σ => c * g σ) τ = c * slz k δ g τ := by
  unfold slz; ring

private theorem slz_sub (k : ℕ) (δ : M2) (g g' : ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun σ => g σ - g' σ) τ = slz k δ g τ - slz k δ g' τ := by
  unfold slz; ring

private theorem slz_sum {ι : Type} (s : Finset ι) (k : ℕ) (δ : M2) (g : ι → ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun σ => ∑ i ∈ s, g i σ) τ = ∑ i ∈ s, slz k δ (g i) τ := by
  unfold slz; rw [Finset.mul_sum]

theorem qs_Vo_slz (k l : ℕ) (hl : 0 < l) (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    qs (Vo l a) τ = ((l : ℂ) ^ (k - 1))⁻¹ * slz k !![(l : ℤ), 0; 0, 1] (qs a) τ := by
  have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have him : 0 < ((l : ℂ) * (τ : ℂ)).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hl) τ.im_pos
  have hV := (GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion l a hl ha).2 τ ⟨(l : ℂ) * τ, him⟩ rfl
  rw [hV]
  unfold slz
  simp only [Matrix.det_fin_two_of, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  push_cast
  simp only [zero_mul, zero_add, mul_one, mul_zero, sub_zero, add_zero, div_one, one_pow, inv_one]
  rw [ofComplex_apply_of_im_pos him]
  field_simp

end GlobalTheory.EisM

namespace GlobalTheory.EisM

private theorem qs_smul (t : ℂ) (a : ℕ → ℂ) : qs (t • a) = fun τ => t * qs a τ := by
  funext τ; unfold qs
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

theorem sum_slz_repL_Vo : ∀ (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ) (t : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → MF k N (ch ε) h → To k (ch ε l) l h = t • h → ∀ τ : ℍ, ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ = ch ε⁻¹ l * (t * qs (Vo l h) τ - (l : ℂ)⁻¹ * qs h τ) := by
  intro k N l ε h t hk hN hl hlN hMF hT τ
  have hl0 : 0 < l := hl.pos
  have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
  set F := qs h with hF
  set D : M2 := !![(l : ℤ), 0; 0, 1] with hD
  set E : M2 := !![(1 : ℤ), 0; 0, (l : ℤ)] with hE
  have hcoc := GlobalTheory.T.slashIntMatrixPosDet_properties k

  have hTq := (GlobalTheory.T.coeffHeckeTOperator_qExpansion_slashSum k l (ch ε) h hk hl0 (by simp [ch]) hMF.1).2
  rw [hT, qs_smul] at hTq
  have hind := GlobalTheory.T.heckeCharacterSlashSum_indep_reps k N N ε (DT N l) (Option (Fin l)) (Option (Fin l)) (repT l) (repL N l) F hk dvd_rfl
    (fun δ hδ => ⟨by rw [hδ.1]; exact_mod_cast hl0, hδ.2⟩) (GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepTOperator N l hl hlN) (GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepLowerLevel N l hl hlN) hMF.2
  have hcop : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hl).2 hlN
  have hu : IsUnit (((l : ℤ) : ZMod N)) := by
    rw [Int.cast_natCast]; exact (ZMod.isUnit_iff_coprime l N).2 hcop
  have hεl : ch ε l ≠ 0 := by
    unfold ch; exact (IsUnit.map ε hu).ne_zero
  have hinv : ch ε⁻¹ l = (ch ε l)⁻¹ := by
    unfold ch; rw [MulChar.inv_apply_eq_inv']
  have key : ∀ σ : ℍ, ∑ j : Fin l, slz k (repL N l (some j)) F σ = (ch ε l)⁻¹ * (t * F σ - slz k E F σ) := by
    intro σ
    have h1 := congrFun hTq σ
    rw [hind] at h1
    unfold hsum at h1
    rw [Fintype.sum_option] at h1
    have h2 : repL N l none = E := rfl
    rw [h2] at h1
    have h3 : ∀ j : Fin l, ch ε (repL N l (some j) 0 0) = ch ε l := by
      intro j; simp [repL]
    have h4 : ch ε (E 0 0) = 1 := by simp [hE, ch]
    simp only [h3, h4, one_mul, ← Finset.mul_sum] at h1
    field_simp
    rw [← hF] at h1
    linear_combination -h1
  have hVfun : qs (Vo l h) = fun σ => ((l : ℂ) ^ (k - 1))⁻¹ * slz k D F σ := by
    funext σ; exact qs_Vo_slz k l hl0 h hMF.1 σ
  have hdetD : 0 < D.det := by simp [hD, Matrix.det_fin_two_of]; exact_mod_cast hl0
  have hdetE : 0 < E.det := by simp [hE, Matrix.det_fin_two_of]; exact_mod_cast hl0
  have hdetA : ∀ (L : ℕ) (j : Fin l), 0 < (repL L l (some j)).det := by
    intro L j; simp [repL, Matrix.det_fin_two_of]; exact_mod_cast hl0
  have hmat : ∀ j : Fin l, D * repL (N * l) l (some j) = repL N l (some j) * D := by
    intro j
    ext i m; fin_cases i <;> fin_cases m <;> simp [hD, repL, Matrix.mul_apply, Fin.sum_univ_two] <;> push_cast <;> ring
  have hED : E * D = !![((l : ℕ) : ℤ), 0; 0, ((l : ℕ) : ℤ)] := by
    ext i m; fin_cases i <;> fin_cases m <;> simp [hD, hE, Matrix.mul_apply, Fin.sum_univ_two]
  have hterm : ∀ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ =
      ((l : ℂ) ^ (k - 1))⁻¹ * slz k D (slz k (repL N l (some j)) F) τ := by
    intro j
    rw [hVfun, slz_const_mul]
    congr 1
    rw [← (hcoc F hk).1 D _ hdetD (hdetA _ j), hmat j, (hcoc F hk).1 _ D (hdetA _ j) hdetD]
  simp only [hterm]
  rw [← Finset.mul_sum, ← slz_sum]
  have hfun : (fun σ => ∑ j : Fin l, slz k (repL N l (some j)) F σ) = fun σ => (ch ε l)⁻¹ * (t * F σ - slz k E F σ) := by
    funext σ; exact key σ
  rw [hfun, slz_const_mul, slz_sub, slz_const_mul]
  have hDE : slz k D (slz k E F) τ = (l : ℂ) ^ k / (l : ℂ) ^ 2 * F τ := by
    rw [← (hcoc F hk).1 E D hdetE hdetD, hED]
    exact (hcoc F hk).2.2.2.2 l τ hl0
  rw [hDE, hinv]
  have hV := qs_Vo_slz k l hl0 h hMF.1 τ
  rw [hV]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerHeckeVEigenformStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_slash_heckeRepLower_heckeV_eigenform : ∀ (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ) (t : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → MF k N (ch ε) h → To k (ch ε l) l h = t • h → ∀ τ : ℍ, ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ = ch ε⁻¹ l * (t * qs (Vo l h) τ - (l : ℂ)⁻¹ * qs h τ) := by
  first | exact @GlobalTheory.EisM.sum_slz_repL_Vo | exact GlobalTheory.EisM.sum_slz_repL_Vo | (intros; apply GlobalTheory.EisM.sum_slz_repL_Vo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerLevelEqPowMulHeckeV
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerLevelEqPowMulHeckeV
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem qExpansionFunction_coeffHeckeVOperator_eq_tsum (l : ℕ) (hl : 0 < l) (a : ℕ → ℂ) (τ : ℍ) :
    qs (Vo l a) τ = ∑' m : ℕ, a m * cexp (2 * π * Complex.I * m * ((l : ℂ) * τ)) := by
  unfold qs Vo
  have hinj : Function.Injective (fun m : ℕ => l * m) := fun x y h => by
    simpa [hl.ne'] using h
  rw [← hinj.tsum_eq]
  · congr 1; ext m
    simp only [dvd_mul_right, if_true, Nat.mul_div_cancel_left m hl]
    congr 2; push_cast; ring
  · intro n hn
    by_cases h : l ∣ n
    · obtain ⟨m, rfl⟩ := h; exact ⟨m, rfl⟩
    · simp [Function.mem_support, h] at hn

theorem adjU_sum (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ) (hk : 1 ≤ k) (hl : 0 < l)
    (hf : MF k N (ch ε) h) (τ : ℍ) :
    ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ = (l : ℂ) ^ k * qs (Vo l h) τ := by
  have hlC : (0 : ℝ) < l := by exact_mod_cast hl
  let τ' : ℍ := ⟨(l : ℂ) * τ, by simpa using mul_pos hlC τ.im_pos⟩
  have hτ' : (τ' : ℂ) = (l : ℂ) * τ := rfl
  have key : ∀ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ = (l : ℂ) ^ (k - 1) * qs h τ' := by
    intro j
    let γ : SL(2, ℤ) := ⟨!![1, 0; (N * (j : ℕ) : ℤ), 1], by simp [Matrix.det_fin_two]⟩
    have hγ := hf.2 γ (by simp [γ]) τ'
    have hpt : ((γ • τ' : ℍ) : ℂ) = ((l : ℂ) * τ) / (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) := by
      rw [coe_specialLinearGroup_apply]; simp [γ, hτ']; ring
    have hden : ((((N * (j : ℕ) : ℤ)) : ℂ) * (τ' : ℂ) + 1) = (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) := by
      rw [hτ']; push_cast; ring
    have hne : (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      rcases this with h1 | h1
      · have h2 : N * l * (j : ℕ) = 0 := by rcases h1 with (h1 | h1) | h1 <;> simp [h1]
        simp [h2] at h0
      · exact (τ.im_pos.ne' h1)
    have hγ' : qs h (γ • τ') = (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) ^ k * qs h τ' := by
      rw [← hden, hγ]; simp [γ, ch]
    have harg : ((l : ℂ) * τ / ((N : ℂ) * l * ((j : ℕ) : ℂ) * τ + 1)) = ((γ • τ' : ℍ) : ℂ) := by
      rw [hpt]; push_cast; ring
    unfold slz repL
    simp [Matrix.det_fin_two]
    rw [harg, ofComplex_apply, hγ']
    push_cast at hne ⊢
    field_simp
  simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [qExpansionFunction_coeffHeckeVOperator_eq_tsum l hl h τ]
  have hp : (l : ℂ) * (l : ℂ) ^ (k - 1) = (l : ℂ) ^ k := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  rw [← mul_assoc, hp]
  rfl
end GlobalTheory.EisM

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerLevelEqPowMulHeckeVStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_slash_heckeRepLowerLevel_eq_pow_mul_heckeV : ∀ (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ), 1 ≤ k → 0 < l → MF k N (ch ε) h → ∀ τ : ℍ, ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ = (l : ℂ) ^ k * qs (Vo l h) τ := by
  first | exact @GlobalTheory.EisM.adjU_sum | exact GlobalTheory.EisM.adjU_sum | (intros; apply GlobalTheory.EisM.adjU_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalOfDepletedEigenform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem eigF_of_prim : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (ρ : ℍ → ℝ) (α β : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → Prim k N χ g → Wt (N * l) ρ → α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (k - 1) → ∃ (B : ℕ) (c : ℕ → ℂ), EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧ ∀ a, MF k (N * l) (ch χ⁻¹) a → lam B c a = pet k ρ (qs (Vo l fun n => conj (g n))) (qs a) - β / (l : ℂ) ^ k * pet k ρ (qs fun n => conj (g n)) (qs a) := by
  intro k N l χ g ρ α β hk hN hl hlN hg hρ hab hαβ
  haveI : NeZero N := ⟨by omega⟩
  set h : ℕ → ℂ := fun n => conj (g n) with hh_def
  have hNl : 0 < N * l := Nat.mul_pos hN hl.pos
  have hdvd : N ∣ N * l := dvd_mul_right N l
  have hP : Prim k N χ⁻¹ h := (GlobalTheory.T.cuspForm_conjugate_coefficients_inv_char k N χ g).2 hg
  have hMFh : MF k N (ch χ⁻¹) h := hP.cf.1
  have lin := GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) (ch χ⁻¹)
  have hCFh : CF k (N * l) (ch χ⁻¹) h := (GlobalTheory.T.modularFormCoeffSeq_linear_structure k N (ch χ⁻¹)).2.2.2.2.2 (N * l) h hdvd hP.cf
  have hCFV : CF k (N * l) (ch χ⁻¹) (Vo l h) := (GlobalTheory.T.coeffHeckeVOperator_raises_level k N l (ch χ⁻¹) h hl.pos).2 hP.cf
  have petlin := GlobalTheory.T.halfPeterssonIntegralWeighted_linear_forms k (N * l) (N * l) N χ⁻¹ ρ hk hNl hdvd hρ

  have hsc : ∀ (h' a : ℕ → ℂ) (x : ℂ), CF k (N * l) (ch χ⁻¹) h' → MF k (N * l) (ch χ⁻¹) a →
      pet k ρ (qs (x • h')) (qs a) = conj x * pet k ρ (qs h') (qs a) := by
    intro h' a x hh' ha
    have e : qs (x • h') = fun τ => x * qs h' τ + 0 * qs h' τ := by
      rw [(lin.2.2.1 x h' hh'.1).2]; funext τ; simp
    rw [e, petlin.2 h' h' a x 0 hh' hh' ha.1]; simp
  have hconj : ∀ x : ZMod N, conj (χ x) = χ⁻¹ x := fun x => MulChar.star_apply' χ x
  have hch : ∀ n : ℕ, ch χ⁻¹ (n : ℤ) = χ⁻¹ (n : ZMod N) := by intro n; simp [ch]
  set φ : (ℕ → ℂ) → ℂ := fun a => pet k ρ (qs (Vo l h)) (qs a) - β / (l : ℂ) ^ k * pet k ρ (qs h) (qs a) with hφ_def
  obtain ⟨B, hB⟩ := GlobalTheory.T.exists_sturmBound_isModularFormCoeffSeq k (N * l) N χ⁻¹ hNl hdvd
  obtain ⟨c, hc⟩ := GlobalTheory.T.linearFunctional_eq_coeffLinearCombinationFinite {a | MF k (N * l) (ch χ⁻¹) a} B φ lin.1
    (by
      intro a ha b hb
      refine ⟨(lin.2.1 a b ha hb).1, ?_⟩
      have e1 := petlin.1 (Vo l h) a b 1 1 hCFV ha.1 hb.1
      have e2 := petlin.1 h a b 1 1 hCFh ha.1 hb.1
      simp only [one_smul, one_mul] at e1 e2
      simp only [hφ_def, e1, e2]; ring)
    (by
      intro x a ha
      refine ⟨(lin.2.2.1 x a ha).1, ?_⟩
      have e1 := petlin.1 (Vo l h) a a x 0 hCFV ha.1 ha.1
      have e2 := petlin.1 h a a x 0 hCFh ha.1 ha.1
      simp only [zero_smul, add_zero, zero_mul] at e1 e2
      simp only [hφ_def, e1, e2]; ring)
    hB
  have hφ : ∀ a, MF k (N * l) (ch χ⁻¹) a → lam B c a = φ a := fun a ha => (hc a ha).symm
  refine ⟨B, c, ⟨?_, ?_⟩, hφ⟩
  ·
    intro a ha q hq hqNl
    have hqN : ¬ q ∣ N := fun d => hqNl (dvd_mul_of_dvd_left d l)
    have hql : q ≠ l := fun e => hqNl (e ▸ dvd_mul_left q N)
    have hcop : q.Coprime l := (Nat.coprime_primes hq hl).2 hql
    have hTa := GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ⁻¹ a hk hdvd hq hqNl ha
    rw [hφ _ hTa, hφ _ ha]
    have eigh : To k (ch χ⁻¹ q) q h = h q • h := by
      rw [hP.eig q hq hqN]; funext n; simp
    have eigV : To k (ch χ⁻¹ q) q (Vo l h) = h q • Vo l h := by
      rw [(GlobalTheory.T.coeffHecke_UV_cauchyProduct_identities ℂ l hl.pos).2.2.2.2.1 k q _ h hcop hq.pos, eigh]
      funext n; simp only [Vo, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp
    have adj0 := GlobalTheory.T.halfPeterssonIntegral_heckeT_adjoint k (N * l) N q χ⁻¹ ρ h a hk hNl hdvd hq hqNl hρ hCFh ha
    have adj1 := GlobalTheory.T.halfPeterssonIntegral_heckeT_adjoint k (N * l) N q χ⁻¹ ρ (Vo l h) a hk hNl hdvd hq hqNl hρ hCFV ha
    rw [eigh, hsc h a _ hCFh ha] at adj0
    rw [eigV, hsc (Vo l h) a _ hCFV ha] at adj1
    have hgq : conj (h q) = g q := by simp [hh_def]
    simp only [hφ_def]
    rw [adj0, adj1]
    simp only [hgq, hch]
    ring
  ·
    intro a ha
    have hper : ∀ d : ℤ, ch χ⁻¹ (d + ((N * l : ℕ) : ℤ)) = ch χ⁻¹ d := by
      intro d; simp only [ch]; congr 1; push_cast; simp
    have hUa := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch χ⁻¹) a hk hl (dvd_mul_left l N) hper ha).1
    rw [hφ _ hUa, hφ _ ha]
    have adjU0 := GlobalTheory.T.halfPeterssonIntegral_heckeU_adjoint k (N * l) N l χ⁻¹ ρ h a hk hNl hdvd hl (dvd_mul_left l N) hlN hρ hCFh ha
    have adjU1 := GlobalTheory.T.halfPeterssonIntegral_heckeU_adjoint k (N * l) N l χ⁻¹ ρ (Vo l h) a hk hNl hdvd hl (dvd_mul_left l N) hlN hρ hCFV ha
    have tr0 := GlobalTheory.T.sum_slash_heckeRepLowerLevel_eq_pow_mul_heckeV k N l χ⁻¹ h hk hl.pos hMFh
    have eigl : To k (ch χ⁻¹ l) l h = h l • h := by
      rw [hP.eig l hl hlN]; funext n; simp
    have tr1 := GlobalTheory.T.sum_slash_heckeRepLower_heckeV_eigenform k N l χ⁻¹ h (h l) hk hN hl hlN hMFh eigl
    have f0 : (fun τ => ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ)
        = fun τ => ((l : ℂ) ^ k) * qs (Vo l h) τ + 0 * qs (Vo l h) τ := by
      funext τ; rw [tr0]; ring
    have f1 : (fun τ => ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ)
        = fun τ => (ch χ⁻¹⁻¹ l * h l) * qs (Vo l h) τ + (-(ch χ⁻¹⁻¹ l * (l : ℂ)⁻¹)) * qs h τ := by
      funext τ; rw [tr1]; ring
    rw [f0, petlin.2 (Vo l h) (Vo l h) a _ 0 hCFV hCFV ha.1] at adjU0
    rw [f1, petlin.2 (Vo l h) h a _ _ hCFV hCFh ha.1] at adjU1
    have e1 : conj (ch χ⁻¹⁻¹ (l : ℤ)) = χ⁻¹ (l : ZMod N) := by
      rw [inv_inv]; simp only [ch, Int.cast_natCast]; exact hconj _
    have hgl : conj (h l) = g l := by simp [hh_def]
    have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
    have key : (l : ℂ) ^ (k - 1) / (l : ℂ) ^ k = (l : ℂ)⁻¹ := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]; field_simp
    simp only [map_mul, map_neg, map_inv₀, map_pow, Complex.conj_natCast, map_zero, e1, hgl, zero_mul, add_zero] at adjU0 adjU1
    simp only [hφ_def, adjU0, adjU1]
    set P0 := pet k ρ (qs h) (qs a)
    set P1 := pet k ρ (qs (Vo l h)) (qs a)
    have hcan : (l : ℂ) ^ k / (l : ℂ) ^ k = 1 := div_self (pow_ne_zero _ hl0)
    linear_combination (-P1) * hab + (P0 / (l : ℂ) ^ k) * hαβ + (χ⁻¹ (l : ZMod N) * P0) * key + (-β * P1) * hcan

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalOfDepletedEigenformStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeEigenfunctional_of_depletedEigenform : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (ρ : ℍ → ℝ) (α β : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → Prim k N χ g → Wt (N * l) ρ → α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (k - 1) → ∃ (B : ℕ) (c : ℕ → ℂ), EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧ ∀ a, MF k (N * l) (ch χ⁻¹) a → lam B c a = pet k ρ (qs (Vo l fun n => conj (g n))) (qs a) - β / (l : ℂ) ^ k * pet k ρ (qs fun n => conj (g n)) (qs a) := by
  first | exact @GlobalTheory.EisM.eigF_of_prim | exact GlobalTheory.EisM.eigF_of_prim | (intros; apply GlobalTheory.EisM.eigF_of_prim <;> assumption)
end
