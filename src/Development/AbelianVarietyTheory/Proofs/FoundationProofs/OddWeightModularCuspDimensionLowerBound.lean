module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOddFrameNotReducesToSmallerOddWeight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducesOfDetEvMEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalOfGammaLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostDualTraceDerivationMemSpanValues
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducesOfDetEvMEqZeroStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumFinrankLevelOneLeFinrankCuspFormOfFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumFinrankLevelOneLeFinrankCuspFormOfFrame
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section
namespace GlobalTheory.OddFrame

theorem levelOne_mul_slash {k w : ℤ} (g : ModularForm 𝒮ℒ (k - w)) (F : ℍ → ℂ) (x : SL(2, ℤ)) :
    ((⇑g) * F) ∣[k] x = (⇑g) * (F ∣[w] x) := by
  have h := ModularForm.mul_slash_SL2 (k - w) w x (⇑g) F
  rw [sub_add_cancel] at h
  rw [h, (isMF_coe_top g).slash_top x]

theorem sum_finrank_le_finrank_cuspForm (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (k : ℤ) (hΓ : Γ.FiniteIndex) (hfin : FiniteDimensional ℂ (CuspForm Γ k))
    (hF : ∀ j, IsCF Γ (w j) (F j)) (hdet : ∀ τ, (evM s w F τ).det ≠ 0) :
    ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j)) ≤ Module.finrank ℂ (CuspForm Γ k) := by
  have hcf : ∀ (j : Fin r) (g : ModularForm 𝒮ℒ (k - w j)), IsCF Γ k ((⇑g) * F j) := fun j g =>
    ((isMF_coe_top g).mono le_top).mul_isCF (hF j) (by ring)
  have happ : ∀ (c : Fin r → CuspForm Γ k) (τ : ℍ), (∑ j, c j) τ = ∑ j, c j τ := by
    intro c τ
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => simp
    | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, CuspForm.add_apply, ih]
  let L : (Π j, ModularForm 𝒮ℒ (k - w j)) →ₗ[ℂ] CuspForm Γ k :=
    { toFun := fun g => ∑ j, (hcf j (g j)).toCF
      map_add' := by
        intro a b; ext τ
        simp only [CuspForm.add_apply, happ, IsCF.coe_toCF, Pi.mul_apply, Pi.add_apply, ModularForm.add_apply,
          add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a; ext τ
        simp only [CuspForm.smul_apply, happ, IsCF.coe_toCF, Pi.mul_apply, Pi.smul_apply, ModularForm.smul_apply,
          RingHom.id_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    have h0 : ∀ τ, ∑ j, g j τ * F j τ = 0 := by
      intro τ
      have := congrArg (fun f : CuspForm Γ k => f τ) hg
      simpa [L, happ] using this
    have hfun : (∑ j, (⇑(g j)) * F j) = 0 := by
      ext τ; simpa [Finset.sum_apply] using h0 τ
    have hvec : ∀ τ, Matrix.mulVec (evM s w F τ) (fun j => g j τ) = 0 := by
      intro τ; ext i
      have h1 := congrArg (fun f => (f ∣[k] s i) τ) hfun
      simp only [SlashAction.zero_slash, Pi.zero_apply] at h1
      rw [SlashAction.sum_slash] at h1
      simp only [levelOne_mul_slash, Finset.sum_apply, Pi.mul_apply] at h1
      simp only [Matrix.mulVec, dotProduct, evM, Matrix.of_apply, Pi.zero_apply]
      rw [← h1]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    funext j; ext τ
    have := Matrix.eq_zero_of_mulVec_eq_zero (hdet τ) (hvec τ)
    exact congrFun this j
  haveI : FiniteDimensional ℂ (Π j, ModularForm 𝒮ℒ (k - w j)) := inferInstance
  calc ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j))
      = Module.finrank ℂ (Π j, ModularForm 𝒮ℒ (k - w j)) := (Module.finrank_pi_fintype ℂ).symm
    _ ≤ Module.finrank ℂ (CuspForm Γ k) := LinearMap.finrank_le_finrank_of_injective hinj

end GlobalTheory.OddFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumFinrankLevelOneLeFinrankCuspFormOfFrameStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_finrank_levelOne_le_finrank_cuspForm_of_frame : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ), Γ.FiniteIndex → FiniteDimensional ℂ (CuspForm Γ k) → (∀ j, IsCF Γ (w j) (F j)) → (∀ τ, (evM s w F τ).det ≠ 0) → ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j)) ≤ Module.finrank ℂ (CuspForm Γ k) := by
  first | exact @GlobalTheory.OddFrame.sum_finrank_le_finrank_cuspForm | exact GlobalTheory.OddFrame.sum_finrank_le_finrank_cuspForm | (intros; apply GlobalTheory.OddFrame.sum_finrank_le_finrank_cuspForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlusMinusCosetRepresentativesTwoMulCard
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlusMinusCosetRepresentativesTwoMulCard
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame

theorem neg_inv_SL (a : SL(2, ℤ)) : (-a)⁻¹ = -a⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [neg_mul_neg, mul_inv_cancel]

def pmSub (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {g | g ∈ Γ ∨ -g ∈ Γ}
  one_mem' := Or.inl Γ.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (Γ.mul_mem ha hb)
    · exact Or.inr (by simpa only [mul_neg] using Γ.mul_mem ha hb)
    · exact Or.inr (by simpa only [neg_mul] using Γ.mul_mem ha hb)
    · exact Or.inl (by simpa only [neg_mul_neg] using Γ.mul_mem ha hb)
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (Γ.inv_mem ha)
    · refine Or.inr ?_
      have := Γ.inv_mem ha
      rwa [neg_inv_SL] at this

theorem mem_pmSub {Γ : Subgroup SL(2, ℤ)} {g : SL(2, ℤ)} : g ∈ pmSub Γ ↔ g ∈ Γ ∨ -g ∈ Γ := by
  rfl

theorem le_pmSub (Γ : Subgroup SL(2, ℤ)) : Γ ≤ pmSub Γ := by
  intro g hg
  exact Or.inl hg

theorem relIndex_pmSub {Γ : Subgroup SL(2, ℤ)} (hm : (-1 : SL(2, ℤ)) ∉ Γ) : Γ.relIndex (pmSub Γ) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨-1, mem_pmSub.2 (Or.inr (by rw [neg_neg]; exact Γ.one_mem)), fun b hb => ?_⟩
  rw [mul_neg_one]
  rcases mem_pmSub.1 hb with h | h
  · refine Or.inr ⟨h, fun h' => hm ?_⟩
    have := Γ.mul_mem (Γ.inv_mem h) h'
    rwa [mul_neg, inv_mul_cancel] at this
  · refine Or.inl ⟨h, fun h' => hm ?_⟩
    have := Γ.mul_mem (Γ.inv_mem h') h
    rwa [mul_neg, inv_mul_cancel] at this

theorem reps_index : ∀ (Γ : Subgroup SL(2, ℤ)), Γ.FiniteIndex → (-1 : SL(2, ℤ)) ∉ Γ →
    ∃ (r : ℕ) (s : Fin r → SL(2, ℤ)), IsReps Γ s ∧ 2 * r = Γ.index := by
  intro Γ hΓ hm
  have : (pmSub Γ).FiniteIndex := Subgroup.finiteIndex_of_le (le_pmSub Γ)
  let e : Fin (Nat.card (SL(2, ℤ) ⧸ pmSub Γ)) ≃ SL(2, ℤ) ⧸ pmSub Γ :=
    (Finite.equivFin (SL(2, ℤ) ⧸ pmSub Γ)).symm
  refine ⟨Nat.card (SL(2, ℤ) ⧸ pmSub Γ), fun i => (Quotient.out (e i))⁻¹, ⟨fun x => ?_, ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := e.surjective (QuotientGroup.mk x⁻¹)
    have hq : (QuotientGroup.mk (Quotient.out (e i)) : SL(2, ℤ) ⧸ pmSub Γ) = QuotientGroup.mk x⁻¹ := by
      rw [hi]; exact QuotientGroup.out_eq' _
    have hp := QuotientGroup.eq.1 hq
    have hx : x = ((Quotient.out (e i))⁻¹ * x⁻¹)⁻¹ * (Quotient.out (e i))⁻¹ := by group
    refine ⟨i, ?_⟩
    rcases mem_pmSub.1 ((pmSub Γ).inv_mem hp) with h | h
    · exact ⟨_, h, Or.inl hx⟩
    · refine ⟨_, h, Or.inr ?_⟩
      rw [neg_mul, neg_neg]
      exact hx
  · intro i j γ hγ hij
    dsimp only at hij
    have hp : ∃ p ∈ pmSub Γ, (Quotient.out (e i))⁻¹ = p * (Quotient.out (e j))⁻¹ := by
      rcases hij with h | h
      · exact ⟨γ, le_pmSub Γ hγ, h⟩
      · refine ⟨-γ, mem_pmSub.2 (Or.inr (by rw [neg_neg]; exact hγ)), ?_⟩
        rw [h, neg_mul]
    obtain ⟨p, hpP, hpe⟩ := hp
    have hmem : (Quotient.out (e j))⁻¹ * Quotient.out (e i) ∈ pmSub Γ := by
      have : (Quotient.out (e j))⁻¹ * Quotient.out (e i) = p⁻¹ := by
        have hi : Quotient.out (e i) = Quotient.out (e j) * p⁻¹ := by
          rw [← inv_inv (Quotient.out (e i)), hpe, mul_inv_rev, inv_inv]
        rw [hi, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact (pmSub Γ).inv_mem hpP
    have hq := QuotientGroup.eq.2 hmem
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at hq
    exact e.injective hq.symm
  · rw [← Subgroup.relIndex_mul_index (le_pmSub Γ), relIndex_pmSub hm]
    rfl

end GlobalTheory.OddFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlusMinusCosetRepresentativesTwoMulCardStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_plusMinusCosetRepresentatives_two_mul_card : ∀ (Γ : Subgroup SL(2, ℤ)), Γ.FiniteIndex → (-1 : SL(2, ℤ)) ∉ Γ → ∃ (r : ℕ) (s : Fin r → SL(2, ℤ)), IsReps Γ s ∧ 2 * r = Γ.index := by
  first | exact @GlobalTheory.OddFrame.reps_index | exact GlobalTheory.OddFrame.reps_index | (intros; apply GlobalTheory.OddFrame.reps_index <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelOneTwelveMulFinrankModularFormLowerBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelOneTwelveMulFinrankModularFormLowerBound
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem levelOne_twelve_mul_finrank_lower_bound :
    ∀ n : ℤ, Even n → n + 5 + 3 * (if n % 4 = 0 then 1 else -1) +
      4 * (if n % 6 = 0 then 1 else if n % 6 = 2 then -1 else 0) ≤
        12 * (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) := by
  intro n hn
  rcases lt_or_ge n 0 with hneg | hpos
  · have h0 : (0 : ℤ) ≤ (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) := Int.natCast_nonneg _
    obtain ⟨m, hm⟩ := hn
    generalize (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) = d at h0 ⊢
    split_ifs <;> omega
  · lift n to ℕ using hpos
    have hke : Even n := by exact_mod_cast hn
    have hrank := ModularForm.dimension_level_one n hke
    have hfin : Module.finrank ℂ (ModularForm 𝒮ℒ (n : ℤ)) =
        if n % 12 = 2 then n / 12 else n / 12 + 1 := by
      exact Module.finrank_eq_of_rank_eq hrank
    obtain ⟨m, hm⟩ := hke
    generalize Module.finrank ℂ (ModularForm 𝒮ℒ (n : ℤ)) = d at hfin ⊢
    split_ifs at hfin ⊢ <;> omega

end GlobalTheory.OddFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelOneTwelveMulFinrankModularFormLowerBoundStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelOne_twelve_mul_finrank_modularForm_lower_bound : ∀ n : ℤ, Even n → n + 5 + 3 * (if n % 4 = 0 then 1 else -1) + 4 * (if n % 6 = 0 then 1 else if n % 6 = 2 then -1 else 0) ≤ 12 * (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) := by
  first | exact @GlobalTheory.OddFrame.levelOne_twelve_mul_finrank_lower_bound | exact GlobalTheory.OddFrame.levelOne_twelve_mul_finrank_lower_bound | (intros; apply GlobalTheory.OddFrame.levelOne_twelve_mul_finrank_lower_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeMulCardOddFrameWeightsDvdThree
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeMulCardOddFrameWeightsDvdThree
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame.ThirdDiv

def uEl : SL(2, ℤ) := ⟨!![0, -1; 1, 1], by norm_num [Matrix.det_fin_two_of]⟩

noncomputable def μ : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩

theorem μ_sq : μ ^ 2 = μ - 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [μ, pow_two] <;> nlinarith [h3]

theorem coe_ρ : (ρ : ℂ) = μ - 1 := by
  apply Complex.ext <;> simp [μ, UpperHalfPlane.ρ] <;> norm_num

theorem μ_ne : μ ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [μ] at this

theorem denom_uEl : denom (uEl : GL (Fin 2) ℝ) ρ = μ := by
  simp only [denom, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
  simp [uEl, coe_ρ]

theorem uEl_smul_ρ : uEl • ρ = ρ := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  simp [uEl, coe_ρ]
  rw [div_eq_iff (by simpa using μ_ne), neg_eq_iff_eq_neg]
  linear_combination μ_sq

theorem re_μ_zpow {w : ℤ} (hw : Odd w) :
    (μ ^ (-w)).re = if (3 : ℤ) ∣ w then -1 else 1 / 2 := by
  have h3 : μ ^ 3 = -1 := by linear_combination (μ + 1) * μ_sq
  have h5 : μ ^ 5 = 1 - μ := by linear_combination μ ^ 2 * h3 - μ_sq
  have h6 : μ ^ (6 : ℤ) = 1 := by
    rw [zpow_ofNat]; linear_combination (μ ^ 3 - 1) * h3
  have key : ∀ q t : ℤ, μ ^ (6 * q + t) = μ ^ t := fun q t => by
    rw [zpow_add₀ μ_ne, zpow_mul, h6, one_zpow, one_mul]
  have hre : μ.re = 1 / 2 := rfl
  obtain ⟨m, hm⟩ := hw
  have hc : -w = 6 * (-w / 6) + 1 ∨ -w = 6 * (-w / 6) + 3 ∨ -w = 6 * (-w / 6) + 5 := by omega
  rcases hc with h | h | h
  · rw [if_neg (by omega), h, key, zpow_one, hre]
  · rw [if_pos (by omega), h, key, zpow_ofNat, h3]; simp
  · rw [if_neg (by omega), h, key, zpow_ofNat, h5, Complex.sub_re, hre]; norm_num

theorem not_fixed {N : ℕ} (hN : 5 ≤ N) {γ x : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) :
    ¬ (x * uEl = γ * x ∨ x * uEl = -(γ * x)) := by
  obtain ⟨h0, h1, -⟩ := (CongruenceSubgroup.Gamma1_mem N γ).1 hγ
  have htr : ((x * uEl * x⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel_left]
    simp [uEl, Matrix.trace_fin_two]
  rintro (h | h)
  · rw [h, mul_inv_cancel_right, Matrix.trace_fin_two] at htr
    have h2 := congrArg (Int.cast : ℤ → ZMod N) htr
    push_cast at h2
    have h3 : ((1 : ℕ) : ZMod N) = 0 := by
      push_cast; linear_combination h2 - h0 - h1
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).1 h3)
    omega
  · rw [h, neg_mul, mul_inv_cancel_right, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg,
      Matrix.trace_fin_two] at htr
    have h2 := congrArg (Int.cast : ℤ → ZMod N) htr
    push_cast at h2
    have h3 : ((3 : ℕ) : ZMod N) = 0 := by
      push_cast; linear_combination - h2 - h0 - h1
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).1 h3)
    omega

theorem three_mul_card_dvd (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (hN : 5 ≤ N) (hΓ : Γ ≤ CongruenceSubgroup.Gamma1 N) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (hdet : (evM s w F ρ).det ≠ 0) :
    3 * (Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card = r := by
  classical
  obtain ⟨π, hπ⟩ := hs.exists_perm uEl
  have hε : ∀ i, ∃ ε : ℂ, ∀ j, evM s w F ρ i j * μ ^ (-w j) = ε * evM s w F ρ (π i) j := by
    intro i
    have h0 : ∀ j, (F j ∣[w j] (s i * uEl)) ρ = evM s w F ρ i j * μ ^ (-w j) := fun j => by
      rw [slash_mul_apply, uEl_smul_ρ, denom_uEl]; rfl
    obtain ⟨γ, hγ, h | h⟩ := hπ i
    · refine ⟨1, fun j => ?_⟩
      rw [← h0, h, (hF j).2.slash_mul hγ, one_mul]; rfl
    · refine ⟨-1, fun j => ?_⟩
      rw [← h0, h, slash_neg_of_odd (hF j).1, (hF j).2.slash_mul hγ, neg_one_mul]; rfl
  choose ε hε using hε
  have hne : ∀ i, π i ≠ i := fun i hi => by
    obtain ⟨γ, hγ, h⟩ := hπ i
    rw [hi] at h
    exact not_fixed hN (hΓ hγ) h
  set A := evM s w F ρ with hA
  let P : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i i' => if i' = π i then ε i else 0
  have hAP : A * Matrix.diagonal (fun j => μ ^ (-w j)) = P * A := by
    ext i j
    rw [Matrix.mul_diagonal, hε, Matrix.mul_apply]
    simp [P]
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  have hD : Matrix.diagonal (fun j => μ ^ (-w j)) = A⁻¹ * (P * A) := by
    rw [← hAP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have htr : ∑ j, μ ^ (-w j) = 0 := by
    rw [← Matrix.trace_diagonal, hD, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
      Matrix.mul_one]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [P, (hne i).symm]
  have hre := congrArg Complex.re htr
  rw [Complex.re_sum, Finset.sum_congr rfl fun j _ => re_μ_zpow (hF j).1, Finset.sum_ite] at hre
  simp only [Finset.sum_const, nsmul_eq_mul, Complex.zero_re] at hre
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin r)))
    (fun j => (3 : ℤ) ∣ w j)
  rw [Finset.card_univ, Fintype.card_fin] at hc
  have hc' := congrArg (Nat.cast : ℕ → ℝ) hc
  push_cast at hc'
  have : (3 : ℝ) * ((Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card : ℝ) = r := by linarith
  exact_mod_cast this

end GlobalTheory.OddFrame.ThirdDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeMulCardOddFrameWeightsDvdThreeStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.three_mul_card_oddFrame_weights_dvd_three : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), 5 ≤ N → Γ ≤ CongruenceSubgroup.Gamma1 N → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (evM s w F ρ).det ≠ 0 → 3 * (Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card = r := by
  first | exact @GlobalTheory.OddFrame.ThirdDiv.three_mul_card_dvd | exact GlobalTheory.OddFrame.ThirdDiv.three_mul_card_dvd | (intros; apply GlobalTheory.OddFrame.ThirdDiv.three_mul_card_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumFinrankLevelOneLeFinrankOfFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumFinrankLevelOneLeFinrankOfFrame
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame

def frameMap (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {r : ℕ} (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ)
    (hF : ∀ j, IsMF Γ (w j) (F j)) :
    (Π j : Fin r, ModularForm 𝒮ℒ (k - w j)) →ₗ[ℂ] ModularForm Γ k where
  toFun g := (IsMF.sum (f := fun j => ⇑(g j) * F j) Finset.univ
    (fun j _ => ((isMF_coe_top (g j)).mono le_top).mul (hF j) (by ring))).toMF
  map_add' g h := by
    ext τ
    simp [add_mul, Finset.sum_add_distrib, Finset.sum_apply]
  map_smul' c g := by
    ext τ
    simp [Finset.mul_sum, mul_assoc, Finset.sum_apply]

theorem frameMap_apply (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {r : ℕ} (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ)
    (k : ℤ) (hF : ∀ j, IsMF Γ (w j) (F j)) (g : Π j : Fin r, ModularForm 𝒮ℒ (k - w j)) :
    ⇑(frameMap Γ w F k hF g) = ∑ j, ⇑(g j) * F j := rfl

theorem mul_slash_levelOne {r : ℕ} (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ)
    (g : Π j : Fin r, ModularForm 𝒮ℒ (k - w j)) (j : Fin r) (x : SL(2, ℤ)) :
    (⇑(g j) * F j) ∣[k] x = ⇑(g j) * (F j ∣[w j] x) := by
  have h := ModularForm.mul_slash_SL2 (k - w j) (w j) x (⇑(g j)) (F j)
  rw [sub_add_cancel] at h
  rw [h, IsMF.slash_top (isMF_coe_top (g j)) x]

theorem frameMap_injective (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {r : ℕ} (s : Fin r → SL(2, ℤ))
    (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ) (hF : ∀ j, IsMF Γ (w j) (F j))
    (hdet : ∀ τ, (evM s w F τ).det ≠ 0) : Function.Injective (frameMap Γ w F k hF) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  have hsum : ∑ j, ⇑(g j) * F j = 0 := by
    rw [← frameMap_apply Γ w F k hF g, hg]
    rfl
  have hrow : ∀ i τ, ∑ j, (g j) τ * (F j ∣[w j] s i) τ = 0 := by
    intro i τ
    have h1 : (∑ j, ⇑(g j) * F j) ∣[k] s i = 0 := by
      rw [hsum]
      exact SlashAction.zero_slash _ _
    rw [SlashAction.sum_slash] at h1
    simp only [mul_slash_levelOne w F k g _ (s i)] at h1
    have h2 := congrFun h1 τ
    simpa [Finset.sum_apply] using h2
  have hv : ∀ τ, (fun j => (g j) τ) = 0 := by
    intro τ
    apply Matrix.eq_zero_of_mulVec_eq_zero (hdet τ)
    funext i
    simp only [Matrix.mulVec, dotProduct, evM, Matrix.of_apply, Pi.zero_apply]
    rw [← hrow i τ]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  funext j
  ext τ
  exact congrFun (hv τ) j

theorem finrank_sum_le_of_frame : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (k : ℤ), Γ.FiniteIndex → FiniteDimensional ℂ (ModularForm Γ k) →
    (∀ j, IsMF Γ (w j) (F j)) → (∀ τ, (evM s w F τ).det ≠ 0) →
    ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j)) ≤ Module.finrank ℂ (ModularForm Γ k) := by
  intro Γ r s w F k hΓ hfin hF hdet
  have hinj := frameMap_injective Γ s w F k hF hdet
  have : Module.Finite ℂ (Π j : Fin r, ModularForm 𝒮ℒ (k - w j)) :=
    Module.Finite.of_injective (frameMap Γ w F k hF) hinj
  have : ∀ j, Module.Finite ℂ (ModularForm 𝒮ℒ (k - w j)) := fun j =>
    Module.Finite.of_surjective (LinearMap.proj (R := ℂ)
      (φ := fun j : Fin r => ModularForm 𝒮ℒ (k - w j)) j)
      (fun y => ⟨Pi.single j y, by simp⟩)
  rw [← Module.finrank_pi_fintype]
  exact LinearMap.finrank_le_finrank_of_injective hinj

end GlobalTheory.OddFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumFinrankLevelOneLeFinrankOfFrameStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_finrank_levelOne_le_finrank_of_frame : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ), Γ.FiniteIndex → FiniteDimensional ℂ (ModularForm Γ k) → (∀ j, IsMF Γ (w j) (F j)) → (∀ τ, (evM s w F τ).det ≠ 0) → ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j)) ≤ Module.finrank ℂ (ModularForm Γ k) := by
  first | exact @GlobalTheory.OddFrame.finrank_sum_le_of_frame | exact GlobalTheory.OddFrame.finrank_sum_le_of_frame | (intros; apply GlobalTheory.OddFrame.finrank_sum_le_of_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEisensteinSlashNeOutsideGamma
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEisensteinSlashNeOutsideGamma
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.EisSep

open EisensteinSeries Complex

def pt (n : ℕ) : ℍ := UpperHalfPlane.mk (((n : ℂ) + 1) * Complex.I) (by simp; positivity)

theorem coe_pt (n : ℕ) : ((pt n : ℍ) : ℂ) = ((n : ℂ) + 1) * Complex.I := rfl

def lim0 (v : Fin 2 → ℤ) : ℂ := if v 0 = 0 then (v 1 : ℂ) ^ (-3 : ℤ) else 0

theorem re_im_summand (v : Fin 2 → ℤ) (n : ℕ) :
    ((v 0 : ℂ) * (pt n : ℂ) + v 1).re = v 1 ∧ ((v 0 : ℂ) * (pt n : ℂ) + v 1).im = v 0 * ((n : ℝ) + 1) := by
  rw [coe_pt]; constructor <;> simp

theorem norm_le (v : Fin 2 → ℤ) (n : ℕ) : ‖eisSummand 3 v (pt n)‖ ≤ ‖v‖ ^ (-(3 : ℝ)) := by
  obtain ⟨hre, him⟩ := re_im_summand v n
  set w : ℂ := (v 0 : ℂ) * (pt n : ℂ) + v 1 with hw
  have hvw : ‖v‖ ≤ ‖w‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    fin_cases i
    · have h1 := Complex.abs_im_le_norm w
      rw [him, abs_mul] at h1
      have h2 : |(v 0 : ℝ)| ≤ |(v 0 : ℝ)| * |(n : ℝ) + 1| := by
        have : (1 : ℝ) ≤ |(n : ℝ) + 1| := by rw [abs_of_pos (by positivity)]; simp
        nlinarith [abs_nonneg (v 0 : ℝ)]
      simp only [Int.norm_eq_abs]
      simpa using h2.trans h1
    · have h1 := Complex.abs_re_le_norm w
      rw [hre] at h1
      simpa [Int.norm_eq_abs] using h1
  have he : eisSummand 3 v (pt n) = w ^ (-3 : ℤ) := rfl
  rw [he, norm_zpow, Real.rpow_neg (norm_nonneg _), zpow_neg]
  rcases (norm_nonneg v).eq_or_lt with h0 | h0
  · have : v = 0 := norm_eq_zero.1 h0.symm
    have hw0 : w = 0 := by simp [hw, this]
    simp [hw0]
  · rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, zpow_ofNat]
    exact inv_anti₀ (pow_pos h0 _) (pow_le_pow_left₀ h0.le hvw _)

theorem tendsto_term (v : Fin 2 → ℤ) : Tendsto (fun n => eisSummand 3 v (pt n)) atTop (𝓝 (lim0 v)) := by
  by_cases h : v 0 = 0
  · have : ∀ n, eisSummand 3 v (pt n) = (v 1 : ℂ) ^ (-3 : ℤ) := fun n => by simp [eisSummand, h]
    simp only [this, lim0, h, if_true]
    exact tendsto_const_nhds
  · simp only [lim0, h, if_false]
    refine squeeze_zero_norm (a := fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨_, him⟩ := re_im_summand v n
    set w : ℂ := (v 0 : ℂ) * (pt n : ℂ) + v 1
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by simp
    have hw : (n : ℝ) + 1 ≤ ‖w‖ := by
      have h1 := Complex.abs_im_le_norm w
      rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)] at h1
      have : (1 : ℝ) ≤ |(v 0 : ℝ)| := by exact_mod_cast Int.one_le_abs h
      nlinarith
    have he : eisSummand 3 v (pt n) = w ^ (-3 : ℤ) := rfl
    rw [he, norm_zpow, zpow_neg, one_div]
    have hw1 : (1 : ℝ) ≤ ‖w‖ := hn.trans hw
    have : ‖w‖ ≤ ‖w‖ ^ (3 : ℤ) := by
      rw [zpow_ofNat]; nlinarith [mul_le_mul hw1 hw1 zero_le_one (by linarith)]
    exact inv_anti₀ (by positivity) (hw.trans this)

theorem tendsto_eis {M : ℕ} (c : Fin 2 → ZMod M) :
    Tendsto (fun n => eisensteinSeries c 3 (pt n)) atTop (𝓝 (∑' v : gammaSet M 1 c, lim0 v)) :=
  tendsto_tsum_of_dominated_convergence (bound := fun v : gammaSet M 1 c => ‖v.1‖ ^ (-(3 : ℝ)))
    ((summable_one_div_norm_rpow (by norm_num)).subtype _) (fun v => tendsto_term v.1)
    (Eventually.of_forall fun n v => norm_le v.1 n)

theorem eq_of_zero {M : ℕ} {c : Fin 2 → ZMod M} {v : Fin 2 → ℤ} (hv : v ∈ gammaSet M 1 c) (h0 : v 0 = 0) :
    v = ![0, 1] ∨ v = ![0, -1] := by
  have h := hv.2
  rw [h0, Int.gcd_zero_left, Int.natAbs_eq_iff] at h
  rcases h with h | h
  · left; ext i; fin_cases i <;> simp [h0, h]
  · right; ext i; fin_cases i <;> simp [h0, h]

theorem cast_zero_one (M : ℕ) : ((↑) : ℤ → ZMod M) ∘ (![0, 1] : Fin 2 → ℤ) = ![0, 1] := by
  ext i; fin_cases i <;> simp

theorem lim_one {M : ℕ} (hM : 3 ≤ M) : ∑' v : gammaSet M 1 (![0, 1] : Fin 2 → ZMod M), lim0 v = 1 := by
  haveI : Fact (2 < M) := ⟨by omega⟩
  have hm : (![0, 1] : Fin 2 → ℤ) ∈ gammaSet M 1 (![0, 1] : Fin 2 → ZMod M) := ⟨cast_zero_one M, by simp⟩
  rw [tsum_eq_single ⟨_, hm⟩]
  · simp [lim0]
  · intro v hv
    by_contra hne
    have h0 : v.1 0 = 0 := by by_contra h; simp [lim0, h] at hne
    rcases eq_of_zero v.2 h0 with h | h
    · exact hv (Subtype.ext h)
    · have h1 := congrFun v.2.1 1
      rw [h] at h1
      exact ZMod.neg_one_ne_one (n := M) (by simpa using h1)

theorem lim_ne {M : ℕ} {c : Fin 2 → ZMod M} (hc : c ≠ ![0, 1]) : ∑' v : gammaSet M 1 c, lim0 v ≠ 1 := by
  have key : ∀ v : gammaSet M 1 c, v.1 ≠ ![0, -1] → lim0 v = 0 := by
    intro v hv
    by_contra hne
    have h0 : v.1 0 = 0 := by by_contra h; simp [lim0, h] at hne
    rcases eq_of_zero v.2 h0 with h | h
    · exact hc (by rw [← v.2.1, h, cast_zero_one])
    · exact hv h
  by_cases hm : (![0, -1] : Fin 2 → ℤ) ∈ gammaSet M 1 c
  · rw [tsum_eq_single ⟨_, hm⟩ fun v hv => key v fun h => hv (Subtype.ext h)]
    simp only [lim0]
    norm_num
  · rw [tsum_congr fun v => key v fun h => hm (h ▸ v.2)]
    simp

theorem eq_of_eis_eq {M : ℕ} (hM : 3 ≤ M) {c : Fin 2 → ZMod M}
    (h : eisensteinSeries c 3 = eisensteinSeries (![0, 1] : Fin 2 → ZMod M) 3) : c = ![0, 1] := by
  by_contra hc
  have h1 := tendsto_eis c
  rw [h] at h1
  exact lim_ne hc ((tendsto_nhds_unique h1 (tendsto_eis _)).trans (lim_one hM))

theorem exists_isMF_slash_ne : ∀ M : ℕ, 3 ≤ M → ∀ x : SL(2, ℤ), x ∉ CongruenceSubgroup.Gamma M →
    ∃ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f ∧ f ∣[k] x ≠ f := by
  intro M hM x hx
  haveI : NeZero M := ⟨by omega⟩
  have hMF : ∀ a : Fin 2 → ZMod M, IsMF (CongruenceSubgroup.Gamma M) 3 (eisensteinSeries a 3) := fun a =>
    isMF_coe (ModularForm.eisensteinSeriesMF le_rfl a)
  rw [CongruenceSubgroup.Gamma_mem] at hx
  by_cases hrow : ((x 1 0 : ℤ) : ZMod M) = 0 ∧ ((x 1 1 : ℤ) : ZMod M) = 1
  · refine ⟨3, _, hMF ![-1, 0], fun h => ?_⟩
    have h2 := congrArg (fun f => f ∣[(3 : ℤ)] ModularGroup.S) h
    simp only [eisensteinSeries_slash_apply] at h2
    have hS0 : ((ModularGroup.S : SL(2, ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) = !![0, -1; 1, 0] := by
      rw [Matrix.SpecialLinearGroup.map_apply_coe, ModularGroup.coe_S]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hS : Matrix.vecMul (![-1, 0] : Fin 2 → ZMod M) ((ModularGroup.S : SL(2, ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) = ![0, 1] := by
      rw [hS0]; ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [hS, hS0] at h2
    have h3 := eq_of_eis_eq hM h2
    have h30 := congrFun h3 0
    have h31 := congrFun h3 1
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h30 h31
    exact hx ⟨h31, h30, hrow⟩
  · refine ⟨3, _, hMF ![0, 1], fun h => ?_⟩
    rw [eisensteinSeries_slash_apply] at h
    have h3 := eq_of_eis_eq hM h
    have h30 := congrFun h3 0
    have h31 := congrFun h3 1
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h30 h31
    exact hrow ⟨h30, h31⟩

end GlobalTheory.EisSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEisensteinSlashNeOutsideGammaStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eisenstein_slash_ne_outside_gamma : ∀ M : ℕ, 3 ≤ M → ∀ x : SL(2, ℤ), x ∉ CongruenceSubgroup.Gamma M → ∃ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f ∧ f ∣[k] x ≠ f := by
  first | exact @GlobalTheory.EisSep.exists_isMF_slash_ne | exact GlobalTheory.EisSep.exists_isMF_slash_ne | (intros; apply GlobalTheory.EisSep.exists_isMF_slash_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualOddFrameCuspForms
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualOddFrameCuspForms
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame.DualFrame

theorem mdiff_det {n : ℕ} {M : ℍ → Matrix (Fin n) (Fin n) ℂ} (hM : ∀ a b, MDiff fun τ => M τ a b) :
    MDiff fun τ => (M τ).det := by
  have : (fun τ => (M τ).det) =
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ∏ a, (fun τ => M τ (σ a) a) := by
    ext τ; simp [Matrix.det_apply', Finset.sum_apply, Finset.prod_apply]
  rw [this]
  exact MDifferentiable.sum fun σ _ => (MDifferentiable.prod fun a _ => hM _ _).const_smul _

variable {r : ℕ} (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ)

def dualEntry (i j : Fin r) : ℍ → ℂ := fun τ => ModularForm.discriminant τ * (evM s w F τ)⁻¹ j i

variable {s w F}

theorem evM_smul {y : SL(2, ℤ)} {π : Equiv.Perm (Fin r)} {c : Fin r → ℂ}
    (hc : ∀ i j, F j ∣[w j] (s i * y) = c i • F j ∣[w j] s (π i)) (τ : ℍ) (i k : Fin r) :
    evM s w F (y • τ) i k = c i * evM s w F τ (π i) k * denom (y : GL (Fin 2) ℝ) τ ^ w k := by
  have hJ : denom (y : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  simp only [evM, Matrix.of_apply]
  calc (F k ∣[w k] s i) (y • τ)
      = (F k ∣[w k] s i) (y • τ) * denom (y : GL (Fin 2) ℝ) τ ^ (-w k) * denom (y : GL (Fin 2) ℝ) τ ^ w k := by
        rw [mul_assoc, ← zpow_add₀ hJ]; simp
    _ = c i * (F k ∣[w k] s (π i)) τ * denom (y : GL (Fin 2) ℝ) τ ^ w k := by
        rw [← slash_mul_apply, hc]; simp [smul_eq_mul]

theorem inv_evM_smul {y : SL(2, ℤ)} {π : Equiv.Perm (Fin r)} {c : Fin r → ℂ} (hcc : ∀ i, c i * c i = 1)
    (hc : ∀ i j, F j ∣[w j] (s i * y) = c i • F j ∣[w j] s (π i)) (τ : ℍ) (hA : (evM s w F τ).det ≠ 0)
    (i j : Fin r) :
    (evM s w F (y • τ))⁻¹ j i = denom (y : GL (Fin 2) ℝ) τ ^ (-w j) * c i * (evM s w F τ)⁻¹ j (π i) := by
  set J := denom (y : GL (Fin 2) ℝ) τ with hJdef
  have hJ : J ≠ 0 := denom_ne_zero _ _
  have key : (Matrix.of fun j i => J ^ (-w j) * c i * (evM s w F τ)⁻¹ j (π i)) * evM s w F (y • τ) = 1 := by
    ext j k
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, evM_smul hc, ← hJdef]
    have h1 : ∀ l, J ^ (-w j) * c l * (evM s w F τ)⁻¹ j (π l) * (c l * evM s w F τ (π l) k * J ^ w k)
        = (J ^ (-w j) * J ^ w k) * ((evM s w F τ)⁻¹ j (π l) * evM s w F τ (π l) k) := by
      intro l
      linear_combination (J ^ (-w j) * (evM s w F τ)⁻¹ j (π l) * evM s w F τ (π l) k * J ^ w k) * hcc l
    rw [Finset.sum_congr rfl fun l _ => h1 l, ← Finset.mul_sum, Equiv.sum_comp π (fun l => (evM s w F τ)⁻¹ j l * evM s w F τ l k), ← Matrix.mul_apply,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA)]
    rcases eq_or_ne j k with rfl | hjk
    · rw [← zpow_add₀ hJ]; simp
    · simp [Matrix.one_apply_ne hjk]
  rw [Matrix.inv_eq_left_inv key]; rfl

theorem discriminant_smul (y : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.discriminant (y • τ) = ModularForm.discriminant τ * denom (y : GL (Fin 2) ℝ) τ ^ (12 : ℤ) := by
  have hJ : denom (y : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have h := congrFun (SlashInvariantForm.slash_action_generators_SL2Z ModularForm.discriminant_S_invariant
    ModularForm.discriminant_T_invariant y) τ
  rw [ModularForm.SL_slash_apply] at h
  rw [← h, mul_assoc, ← zpow_add₀ hJ]; simp

theorem dualEntry_slash {y : SL(2, ℤ)} {π : Equiv.Perm (Fin r)} {c : Fin r → ℂ} (hcc : ∀ i, c i * c i = 1)
    (hc : ∀ i j, F j ∣[w j] (s i * y) = c i • F j ∣[w j] s (π i)) (hA : ∀ τ, (evM s w F τ).det ≠ 0)
    (i j : Fin r) : dualEntry s w F i j ∣[12 - w j] y = c i • dualEntry s w F (π i) j := by
  ext τ
  have hJ : denom (y : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  rw [ModularForm.SL_slash_apply]
  simp only [dualEntry, Pi.smul_apply, smul_eq_mul, discriminant_smul, inv_evM_smul hcc hc τ (hA τ)]
  have hJJ : denom (y : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * denom (y : GL (Fin 2) ℝ) τ ^ (-w j) *
      denom (y : GL (Fin 2) ℝ) τ ^ (-(12 - w j)) = 1 := by
    rw [← zpow_add₀ hJ, ← zpow_add₀ hJ, show (12 : ℤ) + -w j + -(12 - w j) = 0 by ring, zpow_zero]
  linear_combination (c i * ModularForm.discriminant τ * (evM s w F τ)⁻¹ j (π i)) * hJJ

theorem dualEntry_slash_of_eq {Γ : Subgroup SL(2, ℤ)} (hΓ : (-1 : SL(2, ℤ)) ∉ Γ) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (hA : ∀ τ, (evM s w F τ).det ≠ 0)
    {y γ : SL(2, ℤ)} (hγ : γ ∈ Γ) {i i' : Fin r} (hy : s i * y = γ * s i') (j : Fin r) :
    dualEntry s w F i j ∣[12 - w j] y = dualEntry s w F i' j := by
  classical
  obtain ⟨π, hπ⟩ := hs.exists_perm y
  choose g hg hdec using hπ
  let c : Fin r → ℂ := fun l => if s l * y = g l * s (π l) then 1 else -1
  have hcc : ∀ l, c l * c l = 1 := by
    intro l; simp only [c]; split_ifs <;> norm_num
  have hc : ∀ l j, F j ∣[w j] (s l * y) = c l • F j ∣[w j] s (π l) := by
    intro l j
    by_cases hp : s l * y = g l * s (π l)
    · simp only [c, if_pos hp]
      rw [hp, (hF j).2.slash_mul (hg l), one_smul]
    · simp only [c, if_neg hp]
      rw [(hdec l).resolve_left hp, slash_neg_of_odd (hF j).1, (hF j).2.slash_mul (hg l), neg_one_smul]
  have hπi : π i = i' := by
    apply hs.2 (π i) i' ((g i)⁻¹ * γ) (Γ.mul_mem (Γ.inv_mem (hg i)) hγ)
    rcases hdec i with h | h
    · left; rw [mul_assoc, ← hy, h, inv_mul_cancel_left]
    · right; rw [mul_assoc, ← hy, h, mul_neg, neg_neg, inv_mul_cancel_left]
  have hp : s i * y = g i * s (π i) := by
    by_contra hp
    have h := (hdec i).resolve_left hp
    rw [hy, hπi, ← neg_mul] at h
    have h2 : γ = -g i := mul_right_cancel h
    apply hΓ
    have h3 : (-1 : SL(2, ℤ)) = γ * (g i)⁻¹ := by rw [h2, neg_mul, mul_inv_cancel]
    rw [h3]
    exact Γ.mul_mem hγ (Γ.inv_mem (hg i))
  rw [dualEntry_slash hcc hc hA, hπi]
  simp only [c, if_pos hp, one_smul]

theorem mdiff_dualEntry (hF : ∀ j, MDiff (F j)) (hA : ∀ τ, (evM s w F τ).det ≠ 0) (i j : Fin r) :
    MDiff (dualEntry s w F i j) := by
  have e : dualEntry s w F i j = ModularForm.discriminant * ((fun τ => (evM s w F τ).det)⁻¹ *
      fun τ => ((evM s w F τ).updateRow i (Pi.single j 1)).det) := by
    ext τ
    simp [dualEntry, Matrix.inv_def, Matrix.adjugate_apply, Ring.inverse_eq_inv']
  rw [e]
  refine CuspForm.discriminant.holo'.mul (((mdiff_det_evM s w hF).inv hA).mul (mdiff_det fun a b => ?_))
  by_cases h : a = i
  · simp only [Matrix.updateRow_apply, if_pos h]
    exact mdifferentiable_const
  · simp only [Matrix.updateRow_apply, if_neg h]
    exact mdiff_slash (hF b) _ _

theorem exists_dual_cuspForms (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (hΓ : (-1 : SL(2, ℤ)) ∉ Γ) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (hA : ∀ τ, (evM s w F τ).det ≠ 0)
    (hT : Tendsto (fun τ => ModularForm.discriminant τ • (evM s w F τ)⁻¹) atImInfty (𝓝 0)) :
    ∃ G : Fin r → ℍ → ℂ, (∀ j, IsCF Γ (12 - w j) (G j)) ∧
      ∀ τ, (evM s (fun j => 12 - w j) G τ).det ≠ 0 := by
  let G : Fin r → ℍ → ℂ := fun j => dualEntry s w F j j ∣[12 - w j] (s j)⁻¹
  have hodd : ∀ j, Odd (12 - w j) := fun j => by
    obtain ⟨k, hk⟩ := (hF j).1
    exact ⟨5 - k, by omega⟩
  have hpos : ∀ j i, ∀ γ ∈ Γ, G j ∣[12 - w j] (γ * s i) = dualEntry s w F i j := by
    intro j i γ hγ
    simp only [G]
    rw [← SlashAction.slash_mul]
    exact dualEntry_slash_of_eq hΓ hs hF hA hγ (mul_inv_cancel_left _ _) j
  have hzero : ∀ i j, IsZeroAtImInfty (dualEntry s w F i j) := fun i j =>
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hT j) i
  refine ⟨G, fun j => ⟨fun γ hγ => ?_, mdiff_slash (mdiff_dualEntry (fun j => (hF j).2.2.1) hA j j) _ _,
    fun x => ?_⟩, fun τ => ?_⟩
  · obtain ⟨i, g, hg, h | h⟩ := hs.1 1
    · calc G j ∣[12 - w j] γ = G j ∣[12 - w j] (γ * g * s i) := by rw [mul_assoc, ← h, mul_one]
        _ = G j ∣[12 - w j] (g * s i) := by rw [hpos j i _ (Γ.mul_mem hγ hg), hpos j i g hg]
        _ = G j := by rw [← h, SlashAction.slash_one]
    · calc G j ∣[12 - w j] γ = G j ∣[12 - w j] (-(γ * g * s i)) := by
            rw [mul_assoc, ← mul_neg, ← h, mul_one]
        _ = G j ∣[12 - w j] (-(g * s i)) := by
            rw [slash_neg_of_odd (hodd j), slash_neg_of_odd (hodd j), hpos j i _ (Γ.mul_mem hγ hg),
              hpos j i g hg]
        _ = G j := by rw [← h, SlashAction.slash_one]
  · obtain ⟨i, g, hg, rfl | rfl⟩ := hs.1 x
    · rw [hpos j i g hg]; exact hzero i j
    · rw [slash_neg_of_odd (hodd j), hpos j i g hg]; exact (hzero i j).neg
  · have e : evM s (fun j => 12 - w j) G τ = (ModularForm.discriminant τ • (evM s w F τ)⁻¹).transpose := by
      ext i j
      have h := hpos j i 1 Γ.one_mem
      rw [one_mul] at h
      change (G j ∣[12 - w j] s i) τ = _
      rw [h]; rfl
    rw [e, Matrix.det_transpose, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (pow_ne_zero _ (ModularForm.discriminant_ne_zero τ)) (inv_ne_zero (hA τ))

end GlobalTheory.OddFrame.DualFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualOddFrameCuspFormsStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_oddFrame_cuspForms : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), (-1 : SL(2, ℤ)) ∉ Γ → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (∀ τ, (evM s w F τ).det ≠ 0) → Tendsto (fun τ => ModularForm.discriminant τ • (evM s w F τ)⁻¹) atImInfty (𝓝 0) → ∃ G : Fin r → ℍ → ℂ, (∀ j, IsCF Γ (12 - w j) (G j)) ∧ ∀ τ, (evM s (fun j => 12 - w j) G τ).det ≠ 0 := by
  first | exact @GlobalTheory.OddFrame.DualFrame.exists_dual_cuspForms | exact GlobalTheory.OddFrame.DualFrame.exists_dual_cuspForms | (intros; apply GlobalTheory.OddFrame.DualFrame.exists_dual_cuspForms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddWeightModularCuspDimensionLowerBound
open UpperHalfPlane Filter GlobalTheory.OddFrame
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem neg_one_not_mem_Gamma1 {N : ℕ} (hN : 5 ≤ N) : (-1 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma1 N := by
  intro h
  rw [CongruenceSubgroup.Gamma1_mem] at h
  have h1 : ((2 : ℕ) : ZMod N) = 0 := by
    have := h.1
    simp at this
    push_cast
    linear_combination -this
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd (by norm_num) h1
  omega

theorem neg_one_mem_Gamma {M : ℕ} (h0 : 0 < M) (hM : M < 3) : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem]
  interval_cases M <;> simp <;> decide

theorem exists_frame (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (hM : 0 < M) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ)
    (h1 : (-1 : SL(2, ℤ)) ∉ Γ) {r : ℕ} {s : Fin r → SL(2, ℤ)} (hs : IsReps Γ s) :
    ∃ (w : Fin r → ℤ) (F G : Fin r → ℍ → ℂ), (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) ∧
      (∀ τ, (evM s w F τ).det ≠ 0) ∧ (∀ j, IsCF Γ (12 - w j) (G j)) ∧
      ∀ τ, (evM s (fun j => 12 - w j) G τ).det ≠ 0 := by
  have hfi := finiteIndex_of_Gamma_le hM hΓ
  have hM3 : 3 ≤ M := by
    by_contra h
    exact h1 (hΓ (neg_one_mem_Gamma hM (by omega)))
  obtain ⟨τ₀, hτ₀⟩ := GlobalTheory.T.exists_point_slashEvaluations_independent_gamma M hM (GlobalTheory.T.exists_eisenstein_slash_ne_outside_gamma M hM3)
  obtain ⟨w₀, F₀, hF₀, hd₀⟩ := GlobalTheory.T.exists_odd_weight_frame_det_ne_zero M Γ r s τ₀ hM hΓ h1 hs hτ₀
  obtain ⟨w, F, hF, -, hred⟩ := GlobalTheory.T.exists_oddFrame_not_reducesToSmallerOddWeight Γ r s w₀ F₀ hfi hF₀ ⟨τ₀, hd₀⟩
  have hdet : ∀ τ, (evM s w F τ).det ≠ 0 := fun τ h => hred (GlobalTheory.T.reduces_of_det_evM_eq_zero' Γ r s w F τ hs hF h)
  have hlead : (leadM M s w F).det ≠ 0 := fun h => hred (GlobalTheory.T.reducesToSmallerOddWeight_of_leadingCoeffMatrix_det_zero M Γ r s w F hM hΓ hs hF h)
  obtain ⟨U, hU1, hU2⟩ := GlobalTheory.T.exists_tendsto_slashEvaluationMatrix_mul M Γ r s w F hM hΓ hs hF hlead
  obtain ⟨G, hG, hGd⟩ := GlobalTheory.T.exists_dual_oddFrame_cuspForms Γ r s w F h1 hs hF hdet (GlobalTheory.T.tendsto_smul_inv_of_mul_tendsto_invertible_matrix r _ U _ _ hlead hU1 hU2)
  exact ⟨w, F, G, hF, hdet, hG, hGd⟩

theorem levelOne_pair (k j : ℤ) (hk : Odd k) (hj : Odd j) :
    2 * k - 2 + 4 * (if k % 3 = 0 then 1 else if k % 3 = 2 then -1 else 0) * (3 * (if (3 : ℤ) ∣ j then 1 else 0) - 1)
      ≤ 12 * ((Module.finrank ℂ (ModularForm 𝒮ℒ (k - j)) : ℤ) +
        (Module.finrank ℂ (ModularForm 𝒮ℒ (k - (12 - j))) : ℤ)) := by
  have ha := GlobalTheory.T.levelOne_twelve_mul_finrank_modularForm_lower_bound (k - j) (hk.sub_odd hj)
  have hb := GlobalTheory.T.levelOne_twelve_mul_finrank_modularForm_lower_bound (k - (12 - j)) (hk.sub_odd (Even.sub_odd (by decide) hj))
  rw [Int.odd_iff] at hk hj
  generalize (Module.finrank ℂ (ModularForm 𝒮ℒ (k - j)) : ℤ) = a at *
  generalize (Module.finrank ℂ (ModularForm 𝒮ℒ (k - (12 - j))) : ℤ) = b at *
  have e4 : ((if (k - j) % 4 = 0 then 1 else -1) : ℤ) + (if (k - (12 - j)) % 4 = 0 then 1 else -1) = 0 := by
    split_ifs <;> omega
  have e3 : ((if (k - j) % 6 = 0 then 1 else if (k - j) % 6 = 2 then -1 else 0) : ℤ) +
      (if (k - (12 - j)) % 6 = 0 then 1 else if (k - (12 - j)) % 6 = 2 then -1 else 0) =
      (if k % 3 = 0 then 1 else if k % 3 = 2 then -1 else 0) * (3 * (if (3 : ℤ) ∣ j then 1 else 0) - 1) := by
    split_ifs <;> omega
  rw [mul_assoc, ← e3]
  linarith

theorem dim_lower_bound : ∀ (N M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → 0 < M →
    CongruenceSubgroup.Gamma M ≤ Γ → Γ ≤ CongruenceSubgroup.Gamma1 N → Odd k → 3 ≤ k →
    FiniteDimensional ℂ (ModularForm Γ (k : ℤ)) ∧ FiniteDimensional ℂ (CuspForm Γ (k : ℤ)) ∧
      (k - 1) * Γ.index ≤
        12 * (Module.finrank ℂ (ModularForm Γ (k : ℤ)) + Module.finrank ℂ (CuspForm Γ (k : ℤ))) := by
  intro N M Γ k hN hM hΓ hΓ1 hk hk3
  obtain ⟨hfM, hfS⟩ := GlobalTheory.T.finiteDimensional_modularForm_cuspForm_of_gamma_le M Γ k hM hΓ
  refine ⟨hfM, hfS, ?_⟩
  have hfi := finiteIndex_of_Gamma_le hM hΓ
  have h1 : (-1 : SL(2, ℤ)) ∉ Γ := fun h => neg_one_not_mem_Gamma1 hN (hΓ1 h)
  obtain ⟨r, s, hs, hr⟩ := GlobalTheory.T.exists_plusMinusCosetRepresentatives_two_mul_card Γ hfi h1
  obtain ⟨w, F, G, hF, hd, hG, hGd⟩ := exists_frame M Γ hM hΓ h1 hs
  have hcM := GlobalTheory.T.sum_finrank_levelOne_le_finrank_of_frame Γ r s w F k hfi hfM (fun j => (hF j).2) hd
  have hcS := GlobalTheory.T.sum_finrank_levelOne_le_finrank_cuspForm_of_frame Γ r s (fun j => 12 - w j) G k hfi hfS hG hGd
  have h3 := GlobalTheory.T.three_mul_card_oddFrame_weights_dvd_three N Γ r s w F hN hΓ1 hs hF (hd _)
  have hkz : Odd (k : ℤ) := by exact_mod_cast hk
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun j _ => levelOne_pair k (w j) hkz (hF j).1
  have h3' : ∑ j, (3 * (if (3 : ℤ) ∣ w j then (1 : ℤ) else 0) - 1) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have : (3 : ℤ) * ((Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card : ℤ) = r := by exact_mod_cast h3
    omega
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, h3', ← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_zero, add_zero] at hsum
  have hcM' : ∑ j, (Module.finrank ℂ (ModularForm 𝒮ℒ ((k : ℤ) - w j)) : ℤ) ≤
      Module.finrank ℂ (ModularForm Γ (k : ℤ)) := by exact_mod_cast hcM
  have hcS' : ∑ j, (Module.finrank ℂ (ModularForm 𝒮ℒ ((k : ℤ) - (12 - w j))) : ℤ) ≤
      Module.finrank ℂ (CuspForm Γ (k : ℤ)) := by exact_mod_cast hcS
  rw [← hr]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  zify
  simp only [Nat.add_sub_cancel]
  push_cast at hsum hcM' hcS' ⊢
  nlinarith

end GlobalTheory.OddFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddWeightModularCuspDimensionLowerBoundStatement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oddWeight_modular_cusp_dimension_lower_bound : ∀ (N M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → Γ ≤ CongruenceSubgroup.Gamma1 N → Odd k → 3 ≤ k → FiniteDimensional ℂ (ModularForm Γ (k : ℤ)) ∧ FiniteDimensional ℂ (CuspForm Γ (k : ℤ)) ∧ (k - 1) * Γ.index ≤ 12 * (Module.finrank ℂ (ModularForm Γ (k : ℤ)) + Module.finrank ℂ (CuspForm Γ (k : ℤ))) := by
  first | exact @GlobalTheory.OddFrame.dim_lower_bound | exact GlobalTheory.OddFrame.dim_lower_bound | (intros; apply GlobalTheory.OddFrame.dim_lower_bound <;> assumption)
end
