module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractionLieDerivativeDivPowerCompatFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLtBinomialBoundOfMulPowLt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierIntegralImaginary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassImageEqLevelAction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationHomotopyOperatorFiltrationProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationHomotopyOperatorFiltrationProperties
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.HotFil

theorem hot_fil : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (v : Derivation R B B) (e : ℕ → B) (N : ℕ), (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) → (∀ k, e k ∈ fil δ k) → (∀ x y, hot v e N (x + y) = hot v e N x + hot v e N y) ∧ (∀ b, hot v e N (algebraMap B (DR R B) b) = 0) ∧ (∀ (j : ℕ), ∀ x ∈ ⋀[B]^(j + 1) Ω[B⁄R], hot v e N x ∈ ⋀[B]^j Ω[B⁄R]) ∧ (∀ x ∈ rel R δ, hot v e N x ∈ rel R δ) ∧ ∀ n, ∀ x ∈ filDR R δ n, hot v e N x ∈ filDR R δ (n + 1) := by
  intro R B _ _ _ J δ v e N hv he
  obtain ⟨hc0, -, -, -, -, hcdeg⟩ := (GlobalTheory.T.derivationContraction_lieDerivative_deRham_rules).1 R B v
  obtain ⟨-, -, -, -, -, hldeg⟩ := (GlobalTheory.T.derivationContraction_lieDerivative_deRham_rules).2 R B v
  have hrel := (GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules).1
  have hfil := (GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules).2
  obtain ⟨-, -, -, -, hfil0, hanti, hsmul⟩ := (GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base).1 R B J δ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [hot, map_add (f := _), smul_add, Finset.sum_add_distrib]
  · intro b
    simp only [hot, hc0, map_zero, smul_zero, Finset.sum_const_zero]
  · intro j x hx
    have hc := hcdeg j x hx
    have hk : ∀ k, (lie v ^ k) (ctr v x) ∈ ⋀[B]^j Ω[B⁄R] := by
      intro k
      induction k with
      | zero => simpa using hc
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact hldeg j _ ih
    exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (hk k)
  · intro x hx
    have hc := (hrel R B J δ v hv x hx).1
    have hk : ∀ k, (lie v ^ k) (ctr v x) ∈ rel R δ := by
      intro k
      induction k with
      | zero => simpa using hc
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact (hrel R B J δ v hv _ ih).2
    refine Ideal.sum_mem _ fun k _ ↦ ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (hk k)
  · intro n x hx
    have hc := (hfil R B J δ v hv n).1 x hx
    have hk : ∀ k, (lie v ^ k) (ctr v x) ∈ filDR R δ (n - k) := by
      intro k
      induction k with
      | zero => simpa using hc
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        rcases Nat.eq_zero_or_pos (n - k) with h0 | hpos
        · have : n - (k + 1) = 0 := by omega
          rw [this, hfil0]
          exact Submodule.mem_top
        · have h1 : n - k = (n - (k + 1)) + 1 := by omega
          rw [h1] at ih
          exact (hfil R B J δ v hv (n - (k + 1))).2.2 _ ih
    refine Ideal.sum_mem _ fun k _ ↦ ?_
    have hek : (-1) ^ k * e (k + 1) ∈ fil δ (k + 1) := Ideal.mul_mem_left _ _ (he (k + 1))
    exact hanti (n + 1) ((k + 1) + (n - k)) (by omega) (hsmul (k + 1) (n - k) _ hek _ (hk k))

end GlobalTheory.PDForm.HotFil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationHomotopyOperatorFiltrationPropertiesStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationHomotopyOperator_filtration_properties : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (v : Derivation R B B) (e : ℕ → B) (N : ℕ), (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) → (∀ k, e k ∈ fil δ k) → (∀ x y, hot v e N (x + y) = hot v e N x + hot v e N y) ∧ (∀ b, hot v e N (algebraMap B (DR R B) b) = 0) ∧ (∀ (j : ℕ), ∀ x ∈ ⋀[B]^(j + 1) Ω[B⁄R], hot v e N x ∈ ⋀[B]^j Ω[B⁄R]) ∧ (∀ x ∈ rel R δ, hot v e N x ∈ rel R δ) ∧ ∀ n, ∀ x ∈ filDR R δ n, hot v e N x ∈ filDR R δ (n + 1) := by
  first | exact @GlobalTheory.PDForm.HotFil.hot_fil | exact GlobalTheory.PDForm.HotFil.hot_fil | (intros; apply GlobalTheory.PDForm.HotFil.hot_fil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerPolyAlgebraHomotopyIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerHomotopyOperatorValuesGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerHomotopyOperatorValuesGenerators
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section Gen

variable {R B P : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing P] [Algebra R P]
  (v : Derivation R P P) {α : B →+* P} (h : SemiHom (RingHom.id R) α)

theorem ctr_mDR_of_kill (hv : ∀ b, v (α b) = 0) (x : DR R B) : ctr v (h.mDR x) = 0 := by
  induction x using indDR with
  | h b => rw [h.mDR_algebraMap, ctr_algebraMap]
  | hd b => rw [h.mDR_ι, h.m1_D, ctr_ι, Derivation.liftKaehlerDifferential_comp_D, hv, map_zero]
  | hm x y hx hy => rw [map_mul, ctr_mul, hx, hy, zero_mul, mul_zero, add_zero]
  | ha x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

theorem lie_mDR_of_kill (hv : ∀ b, v (α b) = 0) (x : DR R B) : lie v (h.mDR x) = 0 := by
  rw [lie_apply, ctr_mDR_of_kill v h hv, map_zero, zero_add, ← h.mDR_dDR, ctr_mDR_of_kill v h hv]

theorem lie_smul_mDR (hv : ∀ b, v (α b) = 0) (p : P) (x : DR R B) :
    lie v (p • h.mDR x) = v p • h.mDR x := by
  rw [Algebra.smul_def, lie_mul, lie_algebraMap, lie_mDR_of_kill v h hv, mul_zero, add_zero, ← Algebra.smul_def]

theorem lie_pow_smul_mDR (hv : ∀ b, v (α b) = 0) (e : ℕ → P) (he0 : v (e 0) = 0)
    (hs : ∀ n, v (e (n + 1)) = e n) (x : DR R B) (n k : ℕ) :
    (lie v ^ k) (e n • h.mDR x) = (if k ≤ n then e (n - k) else 0) • h.mDR x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    by_cases hk : k ≤ n
    · rw [if_pos hk, lie_smul_mDR v h hv]
      by_cases hk' : k + 1 ≤ n
      · rw [if_pos hk', show n - k = (n - (k + 1)) + 1 by omega, hs]
      · rw [if_neg hk', show n - k = 0 by omega, he0]
    · rw [if_neg hk, if_neg (by omega), zero_smul, map_zero]

end Gen

theorem alt_sum_choose_succ (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * ((n + 1).choose (k + 1) : ℤ) = 1 := by
  have h0 := Int.alternating_sum_range_choose (n := n + 1)
  rw [Finset.sum_range_succ'] at h0
  simp only [pow_succ, Nat.choose_zero_right, pow_zero, Nat.cast_one, mul_one, if_neg (Nat.succ_ne_zero n)] at h0
  have : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * -1 * ((n + 1).choose (k + 1) : ℤ) =
      -∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * ((n + 1).choose (k + 1) : ℤ) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
  linarith

theorem sum_e_mul {B : Type} [CommRing B] (Q : PDPoly B) (N n : ℕ) (hn : n < N) :
    ∑ k ∈ Finset.range N, ((-1) ^ k * Q.e (k + 1)) * (if k ≤ n then Q.e (n - k) else 0) = Q.e (n + 1) := by
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter, show (Finset.range N).filter (· ≤ n) = Finset.range (n + 1) by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega]
  have key : ∀ k ∈ Finset.range (n + 1), (-1 : Q.P) ^ k * Q.e (k + 1) * Q.e (n - k) =
      (((-1 : ℤ) ^ k * ((n + 1).choose (k + 1) : ℤ) : ℤ) : Q.P) * Q.e (n + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [mul_assoc, Q.e_mul, show k + 1 + (n - k) = n + 1 by omega]
    push_cast; ring
  rw [Finset.sum_congr rfl key, ← Finset.sum_mul, ← Int.cast_sum, alt_sum_choose_succ, Int.cast_one, one_mul]

theorem hot_values : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η → (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) → (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (N n : ℕ) (α : DR R B), hot v Q.e N (Q.e n • h.mDR α) = 0 ∧ (n < N → hot v Q.e N (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α)) = Q.e (n + 1) • h.mDR α) := by
  intro R B _ _ _ J δ Q _ _ η v h _ hB hs _ N n α
  have he0 : v (Q.e 0) = 0 := by rw [Q.e_zero]; exact v.map_one_eq_zero
  refine ⟨?_, fun hn ↦ ?_⟩
  · unfold hot
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [map_smul, ctr_mDR_of_kill v h hB, smul_zero, map_zero, smul_zero]
  · have hc : ctr v (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α)) = Q.e n • h.mDR α := by
      rw [map_smul, ctr_ι_mul, Derivation.liftKaehlerDifferential_comp_D, hs 0, Q.e_zero, one_smul,
        ctr_mDR_of_kill v h hB, mul_zero, sub_zero]
    unfold hot
    simp only [hc, lie_pow_smul_mDR v h hB Q.e he0 hs, smul_smul]
    rw [← Finset.sum_smul, sum_e_mul Q N n hn]

end GlobalTheory.PDForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerHomotopyOperatorValuesGeneratorsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerHomotopyOperator_values_generators : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η → (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) → (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (N n : ℕ) (α : DR R B), hot v Q.e N (Q.e n • h.mDR α) = 0 ∧ (n < N → hot v Q.e N (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α)) = Q.e (n + 1) • h.mDR α) := by
  first | exact @GlobalTheory.PDForm.hot_values | exact GlobalTheory.PDForm.hot_values | (intros; apply GlobalTheory.PDForm.hot_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdPolynomialCompatibleFormsGeneratedInduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdPolynomialCompatibleFormsGeneratedInduction
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem rel_mul_mem_right {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {J : Ideal B}
    (δ : DividedPowers J) {x : DR R B} (hx : x ∈ rel R δ) (y : DR R B) : x * y ∈ rel R δ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, a, ha, rfl⟩ := hx
    rw [ι_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n, a, ha, rfl⟩)
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul a x _ ih => rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ _ ih

section Poly

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {J : Ideal B}
  {Q : PDPoly B} [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J))
  (h : SemiHom (RingHom.id R) (algebraMap B Q.P))

def pdGen : Set (DR R Q.P) :=
  {x | ∃ n α, x = Q.e n • h.mDR α} ∪ {x | ∃ n α, x = Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α)} ∪
    (rel R η : Set (DR R Q.P))

theorem pdGen_mem_one (n : ℕ) (α : DR R B) : Q.e n • h.mDR α ∈ pdGen η h :=
  Set.mem_union_left _ (Set.mem_union_left _ ⟨n, α, rfl⟩)

theorem pdGen_mem_two (n : ℕ) (α : DR R B) : Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α) ∈ pdGen η h :=
  Set.mem_union_left _ (Set.mem_union_right _ ⟨n, α, rfl⟩)

theorem pdGen_mem_rel {x : DR R Q.P} (hx : x ∈ rel R η) : x ∈ pdGen η h :=
  Set.mem_union_right _ hx

theorem smul_gen_mem (b : Q.P) : ∀ α : DR R B,
    b • h.mDR α ∈ AddSubgroup.closure (pdGen η h) ∧
      b • (ι1 (D R Q.P (Q.e 1)) * h.mDR α) ∈ AddSubgroup.closure (pdGen η h) := by
  have hb : b ∈ Submodule.span B (Set.range Q.e) := by rw [Q.e.span_eq]; trivial
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    exact fun α ↦ ⟨AddSubgroup.subset_closure (pdGen_mem_one η h n α),
      AddSubgroup.subset_closure (pdGen_mem_two η h n α)⟩
  | zero => intro α; simp only [zero_smul]; exact ⟨zero_mem _, zero_mem _⟩
  | add x y _ _ hx hy =>
    intro α
    rw [add_smul, add_smul]
    exact ⟨add_mem (hx α).1 (hy α).1, add_mem (hx α).2 (hy α).2⟩
  | smul c x _ ih =>
    intro α
    have e1 : (c • x) • h.mDR α = x • h.mDR (c • α) := by
      rw [h.mDR_smul, Algebra.smul_def c x, mul_comm, mul_smul]
    have e2 : (c • x) • (ι1 (D R Q.P (Q.e 1)) * h.mDR α) = x • (ι1 (D R Q.P (Q.e 1)) * h.mDR (c • α)) := by
      rw [h.mDR_smul, mul_smul_comm, Algebra.smul_def c x, mul_comm, mul_smul]
    rw [e1, e2]
    exact ih (c • α)

theorem smul_mem_closure (b : Q.P) {x : DR R Q.P} (hx : x ∈ AddSubgroup.closure (pdGen η h)) :
    b • x ∈ AddSubgroup.closure (pdGen η h) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with (⟨n, α, rfl⟩ | ⟨n, α, rfl⟩) | hx
    · rw [smul_smul]; exact (smul_gen_mem η h _ α).1
    · rw [smul_smul]; exact (smul_gen_mem η h _ α).2
    · refine AddSubgroup.subset_closure (pdGen_mem_rel η h ?_)
      rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ hx
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem D_mem_closure {δ : DividedPowers J} (hs : Q.IsStd δ η) (b : Q.P) :
    ι1 (D R Q.P b) ∈ AddSubgroup.closure (pdGen η h) := by
  have hb : b ∈ Submodule.span B (Set.range Q.e) := by rw [Q.e.span_eq]; trivial
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    cases n with
    | zero => rw [Q.e_zero, Derivation.map_one_eq_zero, map_zero]; exact zero_mem _
    | succ n =>
      have hr : ι1 (D R Q.P (η.dpow (n + 1) (Q.e 1)) - η.dpow n (Q.e 1) • D R Q.P (Q.e 1)) ∈ rel R η :=
        Ideal.subset_span ⟨n, Q.e 1, Q.e_one_mem_ext J, rfl⟩
      rw [hs.var, hs.var] at hr
      have e : ι1 (D R Q.P (Q.e (n + 1))) = ι1 (D R Q.P (Q.e (n + 1)) - Q.e n • D R Q.P (Q.e 1)) +
          Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR 1) := by
        rw [map_one h.mDR, mul_one, map_sub, map_smul, sub_add_cancel]
      rw [e]
      exact add_mem (AddSubgroup.subset_closure (pdGen_mem_rel η h hr))
        (AddSubgroup.subset_closure (pdGen_mem_two η h n 1))
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact add_mem hx hy
  | smul c x _ ih =>
    rw [Algebra.smul_def, Derivation.leibniz, map_add (f := _), map_smul, map_smul]
    refine add_mem (smul_mem_closure η h _ ih) ?_
    have e : ι1 (D R Q.P (algebraMap B Q.P c)) = h.mDR (ι1 (D R B c)) := by rw [h.mDR_ι, h.m1_D]
    rw [e]; exact (smul_gen_mem η h x _).1


omit [IsScalarTower R B Q.P] in
theorem mDR_mul_dtau (α β : DR R B) :
    h.mDR α * (ι1 (D R Q.P (Q.e 1)) * h.mDR β) = ι1 (D R Q.P (Q.e 1)) * h.mDR (sgn α * β) := by
  rw [← mul_assoc, map_mul, h.mDR_sgn, ← mul_assoc, ι_mul (D R Q.P (Q.e 1)) (sgn (h.mDR α)), sgn_sgn]

theorem gen_mul_gen {x y : DR R Q.P} (hx : x ∈ pdGen η h) (hy : y ∈ pdGen η h) :
    x * y ∈ AddSubgroup.closure (pdGen η h) := by
  have base : ∀ α : DR R B, h.mDR α ∈ AddSubgroup.closure (pdGen η h) := fun α ↦ by
    have := (smul_gen_mem η h 1 α).1; rwa [one_smul] at this
  have base2 : ∀ α : DR R B, ι1 (D R Q.P (Q.e 1)) * h.mDR α ∈ AddSubgroup.closure (pdGen η h) := fun α ↦ by
    have := (smul_gen_mem η h 1 α).2; rwa [one_smul] at this
  have relL : ∀ {z : DR R Q.P} (w : DR R Q.P), z ∈ rel R η → w * z ∈ AddSubgroup.closure (pdGen η h) :=
    fun w hz ↦ AddSubgroup.subset_closure (pdGen_mem_rel η h (Ideal.mul_mem_left _ w hz))
  rcases hx with (⟨m, α, rfl⟩ | ⟨m, α, rfl⟩) | hx
  · rcases hy with (⟨n, β, rfl⟩ | ⟨n, β, rfl⟩) | hy
    · rw [smul_mul_assoc, mul_smul_comm, ← map_mul]
      exact smul_mem_closure η h _ (smul_mem_closure η h _ (base _))
    · rw [smul_mul_assoc, mul_smul_comm, mDR_mul_dtau]
      exact smul_mem_closure η h _ (smul_mem_closure η h _ (base2 _))
    · exact relL _ hy
  · rcases hy with (⟨n, β, rfl⟩ | ⟨n, β, rfl⟩) | hy
    · rw [smul_mul_assoc, mul_smul_comm, mul_assoc, ← map_mul]
      exact smul_mem_closure η h _ (smul_mem_closure η h _ (base2 _))
    · rw [smul_mul_assoc, mul_smul_comm, mul_assoc, mDR_mul_dtau, ← mul_assoc, ExteriorAlgebra.ι_sq_zero,
        zero_mul, smul_zero, smul_zero]
      exact zero_mem _
    · exact relL _ hy
  · exact AddSubgroup.subset_closure (pdGen_mem_rel η h (rel_mul_mem_right η hx _))

theorem mul_mem_closure {x y : DR R Q.P} (hx : x ∈ AddSubgroup.closure (pdGen η h))
    (hy : y ∈ AddSubgroup.closure (pdGen η h)) : x * y ∈ AddSubgroup.closure (pdGen η h) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    induction hy using AddSubgroup.closure_induction with
    | mem y hy => exact gen_mul_gen η h hx hy
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

end Poly

theorem pdPoly_forms_induction : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J))
    (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η →
    (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) →
    (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (p : DR R Q.P → Prop),
    (∀ x ∈ rel R η, p x) → (∀ x y, p x → p y → p (x + y)) → (∀ n α, p (Q.e n • h.mDR α)) →
    (∀ n α, p (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α))) → ∀ x, p x := by
  intro R B _ _ _ J δ Q _ _ η _ h hs _ _ _ p hrel hadd h1 h2 x
  have hS : ∀ x, x ∈ AddSubgroup.closure (pdGen η h) := fun x ↦ by
    induction x using indDR with
    | h b =>
      have := (smul_gen_mem η h b 1).1
      rwa [map_one, ← Algebra.algebraMap_eq_smul_one] at this
    | hd b => exact D_mem_closure η h hs b
    | hm x y hx hy => exact mul_mem_closure η h hx hy
    | ha x y hx hy => exact add_mem hx hy
  have key : ∀ x ∈ AddSubgroup.closure (pdGen η h), p x ∧ p (-x) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      rcases hx with (⟨n, α, rfl⟩ | ⟨n, α, rfl⟩) | hx
      · exact ⟨h1 n α, by rw [← smul_neg, ← map_neg]; exact h1 n (-α)⟩
      · exact ⟨h2 n α, by rw [← smul_neg, ← mul_neg, ← map_neg]; exact h2 n (-α)⟩
      · exact ⟨hrel x hx, hrel _ (neg_mem hx)⟩
    | zero => exact ⟨hrel 0 (zero_mem _), by rw [neg_zero]; exact hrel 0 (zero_mem _)⟩
    | add x y _ _ hx hy => exact ⟨hadd _ _ hx.1 hy.1, by rw [neg_add]; exact hadd _ _ hx.2 hy.2⟩
    | neg x _ hx => exact ⟨hx.2, by rw [neg_neg]; exact hx.1⟩
  exact (key x (hS x)).1

end GlobalTheory.PDForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdPolynomialCompatibleFormsGeneratedInductionStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pdPolynomial_compatibleForms_generated_induction : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η → (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) → (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (p : DR R Q.P → Prop), (∀ x ∈ rel R η, p x) → (∀ x y, p x → p y → p (x + y)) → (∀ n α, p (Q.e n • h.mDR α)) → (∀ n α, p (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α))) → ∀ x, p x := by
  first | exact @GlobalTheory.PDForm.pdPoly_forms_induction | exact GlobalTheory.PDForm.pdPoly_forms_induction | (intros; apply GlobalTheory.PDForm.pdPoly_forms_induction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerPolyAlgebraHomotopyIdentity
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem homotopy_identity : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η → (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) → (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (ε : Q.P →+* B) (hε : SemiHom (RingHom.id R) ε), IsDPMorphism η δ ε → (∀ b, ε (algebraMap B Q.P b) = b) → (∀ n, ε (Q.e (n + 1)) = 0) → ∀ (N : ℕ) (x : DR R Q.P), x - h.mDR (hε.mDR x) - dDR R Q.P (hot v Q.e N x) - hot v Q.e N (dDR R Q.P x) ∈ filDR R η N := by
  intro R B _ _ _ J δ Q _ _ η v g hstd hvb hve hvd ε hε hεd hεb hεe N

  have hfilE : ∀ k, Q.e k ∈ fil η k := fun k ↦ by
    have := (GlobalTheory.PDA.fil_properties Q.P (Q.ext J) η).2.2.2.2.1 k (Q.e 1) (Q.e_one_mem_ext J)
    rwa [hstd.var] at this
  obtain ⟨hot_add, hot_alg, -, hot_rel, hot_fil⟩ := GlobalTheory.T.derivationHomotopyOperator_filtration_properties R Q.P (Q.ext J) η v Q.e N hvd hfilE
  obtain ⟨hrel_mul, -, -, -, hfil0, hfil_anti, hfil_smul⟩ := GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base.1 R Q.P (Q.ext J) η
  have hd_fil : ∀ n, ∀ x ∈ filDR R η (n + 1), dDR R Q.P x ∈ filDR R η n := fun n ↦
    (GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules.2 R Q.P (Q.ext J) η v hvd n).2.1
  have hrel_le : rel R η ≤ filDR R η N := le_sup_right
  let H : DR R Q.P →+ DR R Q.P := AddMonoidHom.mk' (hot v Q.e N) hot_add
  have hH : ∀ x, H x = hot v Q.e N x := fun _ ↦ rfl
  have hrelgen : ∀ m, ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1)) ∈ rel R η := fun m ↦ by
    have : ι1 (D R Q.P (η.dpow (m + 1) (Q.e 1)) - η.dpow m (Q.e 1) • D R Q.P (Q.e 1)) ∈ rel R η :=
      Ideal.subset_span ⟨m, Q.e 1, Q.e_one_mem_ext J, rfl⟩
    rwa [hstd.var, hstd.var, map_sub, map_smul] at this
  have hD0 : ι1 (D R Q.P (Q.e 0)) = 0 := by rw [Q.e_zero, Derivation.map_one_eq_zero, map_zero]
  have hε1 : ε (Q.e 1) = 0 := by simpa using hεe 0
  have hcomp : ∀ α : DR R B, hε.mDR (g.mDR α) = α := by
    intro α
    induction α using indDR with
    | h b => rw [g.mDR_algebraMap, hε.mDR_algebraMap, hεb]
    | hd b => rw [g.mDR_ι, hε.mDR_ι, g.m1_D, hε.m1_D, hεb]
    | hm x y hx hy => rw [map_mul, map_mul, hx, hy]
    | ha x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hεD1 : hε.mDR (ι1 (D R Q.P (Q.e 1))) = 0 := by
    rw [hε.mDR_ι, hε.m1_D, hε1, Derivation.map_zero, map_zero]

  have big : ∀ M, ∀ x ∈ filDR R η M, N ≤ M →
      x - dDR R Q.P (hot v Q.e N x) - hot v Q.e N (dDR R Q.P x) ∈ filDR R η N := by
    intro M x hx hM
    refine sub_mem (sub_mem (hfil_anti N M hM hx) ?_) ?_
    · exact hfil_anti N M hM (hd_fil M _ (hot_fil M x hx))
    · cases M with
      | zero => rw [Nat.le_zero.1 hM, hfil0]; trivial
      | succ k => exact hfil_anti N (k + 1) hM (hot_fil k _ (hd_fil k x hx))
  have hsmul_mem : ∀ n (y : DR R Q.P), Q.e n • y ∈ filDR R η n := fun n y ↦ by
    simpa using hfil_smul n 0 (Q.e n) (hfilE n) y (by rw [hfil0]; trivial)
  intro x
  refine GlobalTheory.T.pdPolynomial_compatibleForms_generated_induction R B J δ Q η v g hstd hvb hve hvd
    (fun x ↦ x - g.mDR (hε.mDR x) - dDR R Q.P (hot v Q.e N x) - hot v Q.e N (dDR R Q.P x) ∈ filDR R η N)
    ?_ ?_ ?_ ?_ x
  ·
    intro x hx
    refine sub_mem (sub_mem (sub_mem (hrel_le hx) (hrel_le ?_)) (hrel_le ?_)) (hrel_le ?_)
    · exact mDR_mem_rel g hstd.dp (mDR_mem_rel hε hεd hx)
    · exact dDR_mem_rel R η (hot_rel x hx)
    · exact hot_rel _ (dDR_mem_rel R η hx)
  ·
    intro x y hx hy
    have := add_mem hx hy
    convert this using 1
    simp only [map_add (f := _), hot_add]
    abel
  ·
    intro n α
    have hz := (GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N n α).1
    have hz' := (GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N n (dDR R B α)).1
    have hdx : dDR R Q.P (Q.e n • g.mDR α) = ι1 (D R Q.P (Q.e n)) * g.mDR α + Q.e n • g.mDR (dDR R B α) := by
      rw [dDR_smul, g.mDR_dDR]
    have hmx : g.mDR (hε.mDR (Q.e n • g.mDR α)) = algebraMap B Q.P (ε (Q.e n)) • g.mDR α := by
      rw [hε.mDR_smul, hcomp, g.mDR_smul]
    rw [hmx, hz, hdx, hot_add, hz', map_zero]
    cases n with
    | zero =>
      rw [hD0, zero_mul, Q.e_zero, map_one, map_one, one_smul, ← hH, map_zero]
      simp
    | succ m =>
      rw [hεe m, map_zero, zero_smul]
      rcases lt_or_ge m N with hm | hm
      · have hv := (GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N m α).2 hm
        have hr : (ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α ∈ rel R η :=
          hrel_mul _ (hrelgen m) _
        have key : ι1 (D R Q.P (Q.e (m + 1))) * g.mDR α =
            (ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α +
              Q.e m • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) := by
          rw [sub_mul, smul_mul_assoc]; abel
        rw [key, hot_add, hv]
        have : Q.e (m + 1) • g.mDR α - 0 - 0 -
            (hot v Q.e N ((ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α) +
              Q.e (m + 1) • g.mDR α + 0) =
            -hot v Q.e N ((ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α) := by abel
        rw [this]
        exact hrel_le (neg_mem (hot_rel _ hr))
      · have hb := big (m + 1) _ (hsmul_mem (m + 1) (g.mDR α)) (by omega)
        rw [hz, hdx, hot_add, hz', map_zero] at hb
        simpa using hb
  ·
    intro n α
    have hdy : dDR R Q.P (ι1 (D R Q.P (Q.e 1)) * g.mDR α) = -(ι1 (D R Q.P (Q.e 1)) * g.mDR (dDR R B α)) := by
      rw [dDR_mul, sgn_ι, dDR_D, zero_mul, add_zero, neg_mul, g.mDR_dDR]
    have hmx : g.mDR (hε.mDR (Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α))) = 0 := by
      rw [hε.mDR_smul, map_mul, hεD1, zero_mul, smul_zero, map_zero]
    rw [hmx, sub_zero]
    rcases lt_or_ge n N with hn | hn
    · have hv := (GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N n α).2 hn
      have hv' := (GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N n (dDR R B α)).2 hn

      have hr2 : ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) ∈ rel R η := by
        cases n with
        | zero => rw [hD0, zero_mul]; exact zero_mem _
        | succ k =>
          have : ι1 (D R Q.P (Q.e (k + 1))) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) =
              (ι1 (D R Q.P (Q.e (k + 1))) - Q.e k • ι1 (D R Q.P (Q.e 1))) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) := by
            have hsq : Q.e k • ι1 (D R Q.P (Q.e 1)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) = 0 := by
              rw [smul_mul_assoc, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, smul_zero]
            rw [sub_mul, hsq, sub_zero]
          rw [this]
          exact hrel_mul _ (hrelgen k) _
      have hr1 : (ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α ∈ rel R η :=
        hrel_mul _ (hrelgen n) _
      have hdx : dDR R Q.P (Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α)) =
          ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) -
            Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR (dDR R B α)) := by
        rw [dDR_smul, hdy, smul_neg, sub_eq_add_neg]
      have hdh : dDR R Q.P (Q.e (n + 1) • g.mDR α) =
          (ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α +
            Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) + Q.e (n + 1) • g.mDR (dDR R B α) := by
        rw [dDR_smul, g.mDR_dDR, sub_mul, smul_mul_assoc]; abel
      rw [hv, hdh, hdx, ← hH, map_sub, hH, hH, hv']
      have : Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) -
          ((ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α +
            Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) + Q.e (n + 1) • g.mDR (dDR R B α)) -
          (hot v Q.e N (ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α)) -
            Q.e (n + 1) • g.mDR (dDR R B α)) =
          -((ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α) -
            hot v Q.e N (ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α)) := by abel
      rw [this]
      exact hrel_le (sub_mem (neg_mem hr1) (hot_rel _ hr2))
    · exact big n _ (hsmul_mem n _) hn

end GlobalTheory.PDForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerPolyAlgebraHomotopyIdentityStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerPolyAlgebra_homotopy_identity : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η → (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) → (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (ε : Q.P →+* B) (hε : SemiHom (RingHom.id R) ε), IsDPMorphism η δ ε → (∀ b, ε (algebraMap B Q.P b) = b) → (∀ n, ε (Q.e (n + 1)) = 0) → ∀ (N : ℕ) (x : DR R Q.P), x - h.mDR (hε.mDR x) - dDR R Q.P (hot v Q.e N x) - hot v Q.e N (dDR R Q.P x) ∈ filDR R η N := by
  first | exact @GlobalTheory.PDForm.homotopy_identity | exact GlobalTheory.PDForm.homotopy_identity | (intros; apply GlobalTheory.PDForm.homotopy_identity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientDividedPowerFiltrationCompatibleForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientDividedPowerFiltrationCompatibleForms
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

namespace GlobalTheory.PDForm

theorem quot_fil_rel : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : B →+* G) (h : SemiHom (RingHom.id R) q) (n : ℕ), IsDPMorphism δ δ' q → Function.Surjective q → J' = J.map q → (∀ b, q b = 0 ↔ b ∈ fil δ (n + 1)) → (∀ x, h.mDR x ∈ rel R δ' → x ∈ filDR R δ n) ∧ ∀ x ∈ filDR R δ (n + 1), h.mDR x ∈ rel R δ' := by
  intro R B _ _ _ J δ G _ _ J' δ' q h n hd hq hJ hk
  obtain ⟨-, -, hsurj, hker⟩ := GlobalTheory.T.deRhamAlgebra_quotientRing_surjective_and_kernel R B G q h hq
  obtain ⟨-, -, hmul, -, -, hanti, -⟩ := (GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base).1 R B J δ
  have hv : ∀ m, ∀ a ∈ J, (0 : Derivation R B B) (δ.dpow (m + 1) a) = δ.dpow m a * (0 : Derivation R B B) a := by
    intro m a _; simp
  have hd0 := ((GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules).2 R B J δ 0 hv n).2.1
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  ·
    have hle : rel R δ' ≤ (rel R δ).map h.mDR := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨m, a', ha', rfl⟩
      rw [hJ, Ideal.mem_map_iff_of_surjective _ hq] at ha'
      obtain ⟨a, ha, rfl⟩ := ha'
      have e : ι1 (D R G (δ'.dpow (m + 1) (q a)) - δ'.dpow m (q a) • D R G (q a)) =
          h.mDR (ι1 (D R B (δ.dpow (m + 1) a) - δ.dpow m a • D R B a)) := by
        rw [h.mDR_ι, map_sub h.m1, h.m1_D, h.oneFormMap_smul_semilinear, h.m1_D, hd.2 a ha, hd.2 a ha]
      rw [e]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨m, a, ha, rfl⟩)
    obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 (hle hx)
    have hK : x - y ∈ filDR R δ n := by
      refine hker (filDR R δ n) (hmul n) (fun b hb ↦ ?_) (x - y) (by rw [map_sub, hxy, sub_self])
      have hb1 : algebraMap B (DR R B) b ∈ filDR R δ (n + 1) :=
        Ideal.mem_sup_left (Ideal.subset_span ⟨b, (hk b).1 hb, rfl⟩)
      refine ⟨hanti n (n + 1) (Nat.le_succ n) hb1, ?_⟩
      rw [← dDR_algebraMap]
      exact hd0 _ hb1
    have hyn : y ∈ filDR R δ n := Ideal.mem_sup_right hy
    simpa using add_mem hK hyn
  · have hle : filDR R δ (n + 1) ≤ (rel R δ').comap h.mDR := by
      refine sup_le (Ideal.span_le.2 ?_) (fun z hz ↦ mDR_mem_rel h hd hz)
      rintro _ ⟨b, hb, rfl⟩
      change h.mDR (algebraMap B _ b) ∈ rel R δ'
      rw [h.mDR_algebraMap, (hk b).2 hb, map_zero]
      exact zero_mem _
    exact hle hx

end GlobalTheory.PDForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientDividedPowerFiltrationCompatibleFormsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_dividedPowerFiltration_compatibleForms : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : B →+* G) (h : SemiHom (RingHom.id R) q) (n : ℕ), IsDPMorphism δ δ' q → Function.Surjective q → J' = J.map q → (∀ b, q b = 0 ↔ b ∈ fil δ (n + 1)) → (∀ x, h.mDR x ∈ rel R δ' → x ∈ filDR R δ n) ∧ ∀ x ∈ filDR R δ (n + 1), h.mDR x ∈ rel R δ' := by
  first | exact @GlobalTheory.PDForm.quot_fil_rel | exact GlobalTheory.PDForm.quot_fil_rel | (intros; apply GlobalTheory.PDForm.quot_fil_rel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerLinEMulE
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.CrysConn

namespace GlobalTheory.PDA

variable {B : Type} [CommRing B]

def PDPoly.derVal (Q : PDPoly B) : ℕ → Q.P
  | 0 => 0
  | n + 1 => Q.e n

def PDPoly.derLin (Q : PDPoly B) : Q.P →ₗ[B] Q.P := Q.e.constr B Q.derVal

theorem PDPoly.derLin_e (Q : PDPoly B) (n : ℕ) : Q.derLin (Q.e n) = Q.derVal n := by
  simp [PDPoly.derLin, Module.Basis.constr_basis]

theorem PDPoly.derLin_e_succ (Q : PDPoly B) (n : ℕ) : Q.derLin (Q.e (n + 1)) = Q.e n := Q.derLin_e (n + 1)

theorem PDPoly.derLin_e_zero (Q : PDPoly B) : Q.derLin (Q.e 0) = 0 := Q.derLin_e 0

theorem PDPoly.derLin_e_mul_e (Q : PDPoly B) (m n : ℕ) :
    Q.derLin (Q.e m * Q.e n) = Q.e m * Q.derLin (Q.e n) + Q.e n * Q.derLin (Q.e m) := by
  rcases m with _ | a
  · rw [Q.derLin_e_zero, Q.e_zero]; simp
  rcases n with _ | b
  · rw [Q.derLin_e_zero, Q.e_zero]; simp
  rw [Q.derLin_e_succ, Q.derLin_e_succ, Q.e_mul, Q.e_mul, Q.e_mul, ← nsmul_eq_mul, map_nsmul,
    show a + 1 + (b + 1) = (a + b + 1) + 1 by omega, Q.derLin_e_succ, show a + 1 + b = a + b + 1 by omega,
    show b + 1 + a = a + b + 1 by omega, Nat.choose_succ_succ' (a + b + 1) a,
    Nat.choose_symm_of_eq_add (show a + b + 1 = (b + 1) + a by omega)]
  push_cast
  rw [nsmul_eq_mul]
  push_cast
  ring

theorem PDPoly.derLin_mul (Q : PDPoly B) (x y : Q.P) :
    Q.derLin (x * y) = x * Q.derLin y + y * Q.derLin x := by
  have h2 : ∀ x n, Q.derLin (x * Q.e n) = x * Q.derLin (Q.e n) + Q.e n * Q.derLin x := fun x n ↦ by
    have := Q.e.ext (f₁ := Q.derLin ∘ₗ LinearMap.mulRight B (Q.e n))
      (f₂ := LinearMap.mulRight B (Q.derLin (Q.e n)) + LinearMap.mulLeft B (Q.e n) ∘ₗ Q.derLin)
      (fun m ↦ by simpa using Q.derLin_e_mul_e m n)
    simpa using LinearMap.congr_fun this x
  have := Q.e.ext (f₁ := Q.derLin ∘ₗ LinearMap.mulLeft B x)
    (f₂ := LinearMap.mulLeft B x ∘ₗ Q.derLin + LinearMap.mulRight B (Q.derLin x))
    (fun n ↦ by simpa using h2 x n)
  simpa using LinearMap.congr_fun this y

def PDPoly.der (Q : PDPoly B) : Derivation B Q.P Q.P :=
  Derivation.mk' Q.derLin fun x y ↦ by simpa [smul_eq_mul] using Q.derLin_mul x y

theorem PDPoly.der_apply (Q : PDPoly B) (x : Q.P) : Q.der x = Q.derLin x := rfl

end GlobalTheory.PDA

namespace GlobalTheory.PDA

variable {B : Type} [CommRing B]

theorem PDPoly.der_dpow_succ {J : Ideal B} (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (n : ℕ) {a : Q.P} (ha : a ∈ Q.ext J) :
    Q.der (η.dpow (n + 1) a) = η.dpow n a * Q.der a := by
  set D := Q.der
  let P : Q.P → Prop := fun a ↦ ∀ n, D (η.dpow n a) = dpPred η n a • D a
  have hzero : P 0 := fun n ↦ by
    cases n with
    | zero => simp [η.dpow_zero (Q.ext J).zero_mem]
    | succ n => simp [dpow_eval_zero _ n.succ_ne_zero]
  have hadd : ∀ a ∈ Q.ext J, ∀ b ∈ Q.ext J, P a → P b → P (a + b) := fun a ha b hb iha ihb n ↦ by
    have iha : ∀ n, D (η.dpow n a) = dpPred η n a • D a := iha
    have ihb : ∀ n, D (η.dpow n b) = dpPred η n b • D b := ihb
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [η.dpow_add ha hb, map_sum, D.leibniz, iha, ihb, smul_smul, Finset.sum_add_distrib,
      ← Finset.sum_smul, sum_dpow_mul_dpPred η ha hb, sum_dpow_mul_dpPred' η ha hb, map_add, smul_add]
    exact add_comm _ _
  have hmul : ∀ r, ∀ a ∈ Q.ext J, P a → P (r * a) := fun r a ha hP n ↦ by
    cases n with
    | zero => simp [η.dpow_zero (Ideal.mul_mem_left _ r ha), dpPred]
    | succ m =>
      have hm := hP (m + 1)
      have hs := dpPred_mul_self η ha (m + 1)
      simp only [dpPred, smul_eq_mul] at hm hs ⊢
      rw [η.dpow_mul ha, η.dpow_mul ha, D.leibniz, D.leibniz, D.leibniz_pow, hm]
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
      push_cast at hs ⊢
      linear_combination (-(r ^ m * D r)) * hs
  have hspan : ∀ s : Set Q.P, s ⊆ Q.ext J → (∀ x ∈ s, P x) → ∀ a ∈ Ideal.span s, P a := by
    intro s hs hP a ha
    have hle : Ideal.span s ≤ Q.ext J := Ideal.span_le.2 hs
    induction ha using Submodule.span_induction with
    | mem x hx => exact hP x hx
    | zero => exact hzero
    | add x y hx hy ihx ihy => exact hadd x (hle hx) y (hle hy) ihx ihy
    | smul r x hx ih => exact hmul r x (hle hx) ih
  have hJ : ∀ x ∈ J.map (algebraMap B Q.P), P x := by
    refine hspan _ ?_ ?_
    · rintro _ ⟨j, hj, rfl⟩; exact Q.algebraMap_mem_ext hj
    · rintro _ ⟨j, hj, rfl⟩ n
      rw [h.dp.2 j hj, Derivation.map_algebraMap, Derivation.map_algebraMap, smul_zero]
  have he1 := Q.e_one_mem_ext J
  have hA : ∀ x ∈ Q.aug, P x := by
    refine hspan _ ?_ ?_
    · rintro _ ⟨k, rfl⟩; exact Ideal.mem_sup_right (Q.e_succ_mem_aug k)
    · rintro _ ⟨k, rfl⟩ n
      cases n with
      | zero => simp [η.dpow_zero (Ideal.mem_sup_right (Q.e_succ_mem_aug k)), dpPred]
      | succ m =>
        have c1 : η.dpow (m + 1) (Q.e (k + 1)) =
            (Nat.uniformBell (m + 1) (k + 1) : Q.P) * Q.e ((m * (k + 1) + k) + 1) := by
          rw [← h.var (k + 1), η.dpow_comp (by omega) he1, h.var, show (m + 1) * (k + 1) = m * (k + 1) + k + 1 by ring]
        have c2 : dpPred η (m + 1) (Q.e (k + 1)) * Q.e k =
            (Nat.uniformBell (m + 1) (k + 1) : Q.P) * Q.e (m * (k + 1) + k) := by
          have := dpPred_dpow η he1 (m + 1) (n := k + 1) (by omega)
          rw [h.var, show dpPred η (k + 1) (Q.e 1) = Q.e k from h.var k,
            show (m + 1) * (k + 1) = m * (k + 1) + k + 1 by ring,
            show dpPred η (m * (k + 1) + k + 1) (Q.e 1) = Q.e (m * (k + 1) + k) from h.var _] at this
          exact this
        rw [c1, D.leibniz, D.map_natCast, smul_zero, add_zero, smul_eq_mul, smul_eq_mul, Q.der_apply,
          Q.der_apply, Q.derLin_e_succ, Q.derLin_e_succ, c2]
  have hall : ∀ x ∈ Q.ext J, P x := fun x hx ↦ by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    exact hadd y (Ideal.mem_sup_left hy) z (Ideal.mem_sup_right hz) (hJ y hy) (hA z hz)
  simpa [dpPred, smul_eq_mul] using hall a ha (n + 1)

theorem PDPoly.exists_der (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) :
    Q.IsStd δ η → ∃ D : Derivation R Q.P Q.P, (∀ b, D (algebraMap B Q.P b) = 0) ∧
      (∀ n, D (Q.e (n + 1)) = Q.e n) ∧ ∀ n, ∀ a ∈ Q.ext J, D (η.dpow (n + 1) a) = η.dpow n a * D a := by
  intro h
  refine ⟨Q.der.restrictScalars R, fun b ↦ ?_, fun n ↦ ?_, fun n a ha ↦ ?_⟩
  · rw [Derivation.restrictScalars_apply, Derivation.map_algebraMap]
  · rw [Derivation.restrictScalars_apply, Q.der_apply, Q.derLin_e_succ]
  · simp only [Derivation.restrictScalars_apply]
    exact Q.der_dpow_succ δ η h n ha

end GlobalTheory.PDA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLemmaTruncatedDivPowerPolyOneVariable
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.Poincare

theorem eq_zero_of_algebraMap_mem_rel {R G : Type} [CommRing R] [CommRing G] [Algebra R G] {J' : Ideal G}
    (δ' : DividedPowers J') (g : G) (hg : algebraMap G (DR R G) g ∈ rel R δ') : g = 0 := by
  have hle : rel R δ' ≤ RingHom.ker (ExteriorAlgebra.algebraMapInv (R := G) (M := Ω[G⁄R])).toRingHom := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨m, a, _, rfl⟩
    simp [ExteriorAlgebra.algebraMapInv]
  have := hle hg
  rw [RingHom.mem_ker] at this
  simpa [ExteriorAlgebra.algebraMap_leftInverse _ g] using this

theorem mDR_mDR {R R' R'' B B' B'' : Type} [CommRing R] [CommRing B] [Algebra R B]
    [CommRing R'] [CommRing B'] [Algebra R' B'] [CommRing R''] [CommRing B''] [Algebra R'' B'']
    {σ : R →+* R'} {α : B →+* B'} {τ : R' →+* R''} {β : B' →+* B''} {ρ : R →+* R''} {γ : B →+* B''}
    (h : SemiHom σ α) (h' : SemiHom τ β) (h'' : SemiHom ρ γ) (e : ∀ b, β (α b) = γ b) (x : DR R B) :
    h'.mDR (h.mDR x) = h''.mDR x := by
  induction x using indDR with
  | h b => simp [e]
  | hd b => simp [e]
  | hm x y hx hy => simp only [map_mul, hx, hy]
  | ha x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.PDForm.Poincare


open GlobalTheory.PDForm.Poincare in
theorem GlobalTheory.PDForm.rq_truncPoly : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : Q.P →+* G) (n : ℕ), Q.IsStd δ η → IsLev δ (n + 1) → SemiHom (RingHom.id R) q → IsDPMorphism η δ' q → Function.Surjective q → J' = (Q.ext J).map q → (∀ b, q b = 0 ↔ b ∈ fil η (n + 1)) → ∀ (α : B →+* G) (h : SemiHom (RingHom.id R) α) (hd : IsDPMorphism δ δ' α), (∀ b, α b = q (algebraMap B Q.P b)) → RQ h hd := by
  intro R B _ _ _ J δ Q _ _ η G _ _ J' δ' q n hstd hlev hq hqd hqs hJ' hker α h hd hα

  obtain ⟨ε, hεs, hεd, hεb, hεe⟩ : ∃ ε : Q.P →+* B, SemiHom (RingHom.id R) ε ∧ IsDPMorphism η δ ε ∧
      (∀ b, ε (algebraMap B Q.P b) = b) ∧ ∀ k, ε (Q.e (k + 1)) = 0 := by
    obtain ⟨ε0, hε0⟩ := (GlobalTheory.PDA.PDPoly.exists_lift_and_aug B Q).2
    have hb : ∀ b, ε0 (algebraMap B Q.P b) = b := fun b ↦ ε0.commutes b
    refine ⟨ε0, fun r p ↦ ?_, ?_, hb, fun k ↦ (hε0 _).1 (Q.e_succ_mem_aug k)⟩
    · change ε0 (r • p) = r • ε0 p
      rw [← algebraMap_smul B r p, map_smul, algebraMap_smul]
    · refine GlobalTheory.PDA.PDPoly.isDPMorphism_of_isStd B J δ Q η hstd B J δ ε0 0 J.zero_mem ⟨?_, ?_⟩ ?_
      · intro x hx
        rw [Ideal.mem_map_iff_of_surjective _ (fun b ↦ ⟨b, hb b⟩)] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        simpa [hb] using hy
      · intro k a _
        simp [hb]
      · intro k
        cases k with
        | zero => change ε0 (Q.e 0) = _; rw [Q.e_zero, map_one, δ.dpow_zero J.zero_mem]
        | succ k => change ε0 (Q.e (k + 1)) = _; rw [(hε0 _).1 (Q.e_succ_mem_aug k), δ.dpow_eval_zero (Nat.succ_ne_zero k)]
  have hi : SemiHom (RingHom.id R) (algebraMap B Q.P) := fun r b ↦ map_smul (IsScalarTower.toAlgHom R B Q.P) r b

  have hkε : ∀ p, q p = 0 → ε p = 0 := by
    intro p hp
    have h1 : ε p ∈ fil δ (n + 1) :=
      (GlobalTheory.PDA.fil_properties Q.P (Q.ext J) η).2.2.2.2.2.2 B J δ ε hεd (n + 1) (Ideal.mem_map_of_mem _ ((hker p).1 hp))
    rw [hlev] at h1
    exact (Ideal.mem_bot).1 h1
  obtain ⟨eb, hebq⟩ : ∃ eb : G →+* B, ∀ p, eb (q p) = ε p :=
    ⟨q.liftOfRightInverse (Function.surjInv hqs) (Function.rightInverse_surjInv hqs) ⟨ε, fun p hp ↦ hkε p hp⟩,
      fun p ↦ RingHom.liftOfRightInverse_comp_apply _ _ _ _ p⟩
  have hebα : ∀ b, eb (α b) = b := fun b ↦ by rw [hα, hebq, hεb]
  have heb : SemiHom (RingHom.id R) eb := by
    intro r g
    obtain ⟨p, rfl⟩ := hqs g
    have := hq r p
    simp only [RingHom.id_apply] at this ⊢
    rw [← this, hebq, hebq]
    simpa using hεs r p
  have hdeb : IsDPMorphism δ' δ eb := by
    have hc : eb.comp q = ε := RingHom.ext hebq
    refine ⟨?_, ?_⟩
    · rw [hJ', Ideal.map_map, hc]; exact hεd.1
    · intro k a ha
      rw [hJ', Ideal.mem_map_iff_of_surjective _ hqs] at ha
      obtain ⟨a, ha, rfl⟩ := ha
      rw [hebq, hqd.2 a ha, hebq, hεd.2 a ha]
  have hid : SemiHom (RingHom.id R) (RingHom.id B) := fun _ _ ↦ rfl
  have hdid : IsDPMorphism δ δ (RingHom.id B) := (DPMorphism.id δ).isDPMorphism
  have ret1 : ∀ x, km1 heb hdeb (km1 h hd x) = x := fun x ↦
    (divPowerCompatOneFormMap_comp h hd heb hdeb hid hdid hebα x).trans (divPowerCompatOneFormMap_id hid hdid (fun _ ↦ rfl) x)
  have ret : ∀ j x, km heb hdeb j (km h hd j x) = x := fun j x ↦
    (km_km h hd heb hdeb hid hdid hebα j x).trans (km_id hid hdid (fun _ ↦ rfl) j x)

  obtain ⟨v, hv0, hv1, hv2⟩ := GlobalTheory.PDA.PDPoly.exists_der R B J δ Q η hstd
  have he : ∀ k, Q.e k ∈ fil η k := fun k ↦ by
    rw [← hstd.var k]
    exact (GlobalTheory.PDA.fil_properties Q.P (Q.ext J) η).2.2.2.2.1 k _ (Q.e_one_mem_ext J)
  have hht := GlobalTheory.T.derivationHomotopyOperator_filtration_properties R Q.P (Q.ext J) η v Q.e (n + 1) hv2 he
  have kq := GlobalTheory.T.quotient_dividedPowerFiltration_compatibleForms R Q.P (Q.ext J) η G J' δ' q hq n hqd hqs hJ' hker
  have kdr := GlobalTheory.T.deRhamAlgebra_quotientRing_surjective_and_kernel R Q.P G q hq hqs
  have key : ∀ X : DR R Q.P, hq.mDR (dDR R Q.P X) ∈ rel R δ' →
      hq.mDR X - h.mDR (hεs.mDR X) - dDR R G (hq.mDR (hot v Q.e (n + 1) X)) ∈ rel R δ' := by
    intro X hX
    have hT := hht.2.2.2.2 n _ (kq.1 _ hX)
    have hH := GlobalTheory.T.dividedPowerPolyAlgebra_homotopy_identity R B J δ Q η v hi hstd hv0 hv1 hv2 ε hεs hεd hεb hεe (n + 1) X
    have h3 := add_mem hH hT
    rw [sub_add_cancel] at h3
    have := kq.2 _ h3
    rwa [map_sub, map_sub, mDR_mDR hi hq h (fun b ↦ (hα b).symm), hq.mDR_dDR] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x _ hx
    have hx' : α x = 0 := hx
    rw [← hebα x, hx', map_zero]
  ·
    intro y hy
    obtain ⟨p, rfl⟩ := hqs y
    have hy' : hq.mDR (dDR R Q.P (algebraMap Q.P (DR R Q.P) p)) ∈ rel R δ' := by
      rw [dDR_algebraMap, hq.mDR_ι, hq.m1_D]
      exact (Submodule.Quotient.mk_eq_zero (N1 R δ')).1 (by rw [← divPowerCompatFunctionDifferential_apply]; exact hy)
    have hk := key _ hy'
    rw [(hht.2.1 p), map_zero, map_zero, sub_zero, hq.mDR_algebraMap, hεs.mDR_algebraMap, h.mDR_algebraMap,
      ← map_sub] at hk
    have hp : q p = α (ε p) := sub_eq_zero.1 (eq_zero_of_algebraMap_mem_rel δ' _ hk)
    refine ⟨ε p, ?_, hp.symm⟩
    have h0 : km1 h hd (kd0 R δ (ε p)) = 0 := by rw [divPowerCompatOneFormMap_functionDifferential, ← hp]; exact hy
    rw [← ret1 (kd0 R δ (ε p)), h0, map_zero]
  ·
    intro x y _ hxy
    refine ⟨eb y, ?_⟩
    rw [← divPowerCompatOneFormMap_functionDifferential heb hdeb, ← hxy, ret1]
  ·
    intro y hy
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨ω, rfl⟩ := kdr.1 y
    have hy' : hq.mDR (dDR R Q.P (ι1 ω)) ∈ rel R δ' := by
      rw [hq.mDR_dDR, hq.mDR_ι]
      exact (Submodule.Quotient.mk_eq_zero (N R δ' 2)).1 (by rw [← divPowerCompatOneFormDerivative_mk]; exact hy)
    obtain ⟨c, hc⟩ : ∃ c, algebraMap Q.P (DR R Q.P) c = hot v Q.e (n + 1) (ι1 ω) := by
      have := hht.2.2.1 0 _ (ι_mem ω)
      change _ ∈ LinearMap.range _ ^ 0 at this
      rwa [pow_zero, Submodule.mem_one] at this
    have hk := key _ hy'
    rw [← hc, hq.mDR_algebraMap, dDR_algebraMap, hq.mDR_ι, hεs.mDR_ι, h.mDR_ι, ← map_sub, ← map_sub] at hk
    set x : K1 R δ := Submodule.Quotient.mk (hεs.m1 ω) with hxdef
    have heq : (Submodule.Quotient.mk (hq.m1 ω) : K1 R δ') = km1 h hd x + kd0 R δ' (q c) := by
      rw [divPowerCompatOneFormMap_mk, divPowerCompatFunctionDifferential_apply, ← Submodule.Quotient.mk_add, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
        Submodule.Quotient.mk_eq_zero, ← sub_sub]
      exact hk
    refine ⟨x, q c, ?_, heq⟩
    have h0 : km h hd 2 (kd1 R δ x) = 0 := by
      rw [divPowerCompatFormMap_oneFormDerivative, show km1 h hd x = Submodule.Quotient.mk (hq.m1 ω) - kd0 R δ' (q c) by rw [heq]; abel,
        map_sub, divPowerCompatOneFormDerivative_comp_differential, sub_zero]
      exact hy
    rw [← ret 2 (kd1 R δ x), h0, map_zero]
  ·
    intro x y _ hxy
    refine ⟨km1 heb hdeb y, ?_⟩
    rw [← divPowerCompatFormMap_oneFormDerivative heb hdeb, ← hxy, ret]
  ·
    intro y hy
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨ω, rfl⟩ := kdr.2.1 2 y
    have hy' : hq.mDR (dDR R Q.P (ω : DR R Q.P)) ∈ rel R δ' := by
      rw [hq.mDR_dDR]
      exact (Submodule.Quotient.mk_eq_zero (N R δ' 3)).1 (by rw [← divPowerCompatTwoFormDerivative_mk]; exact hy)
    obtain ⟨c, hc⟩ : ∃ c, ι1 c = hot v Q.e (n + 1) (ω : DR R Q.P) := by
      have := hht.2.2.1 1 _ ω.2
      change _ ∈ LinearMap.range _ ^ 1 at this
      rwa [pow_one] at this
    have hk := key _ hy'
    rw [← hc, hq.mDR_ι] at hk
    set x : K R δ 2 := Submodule.Quotient.mk (hεs.mOm 2 ω) with hxdef
    have heq : (Submodule.Quotient.mk (hq.mOm 2 ω) : K R δ' 2) = km h hd 2 x + kd1 R δ' (Submodule.Quotient.mk (hq.m1 c)) := by
      rw [km_mk, divPowerCompatOneFormDerivative_mk, ← Submodule.Quotient.mk_add, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
        Submodule.Quotient.mk_eq_zero, ← sub_sub]
      exact hk
    refine ⟨x, Submodule.Quotient.mk (hq.m1 c), ?_, heq⟩
    have h0 : km h hd 3 (kd2 R δ x) = 0 := by
      rw [divPowerCompatFormMap_twoFormDerivative, show km h hd 2 x = Submodule.Quotient.mk (hq.mOm 2 ω) - kd1 R δ' (Submodule.Quotient.mk (hq.m1 c)) by
        rw [heq]; abel, map_sub, divPowerCompatTwoFormDerivative_comp_oneForm, sub_zero]
      exact hy
    rw [← ret 3 (kd2 R δ x), h0, map_zero]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLemmaTruncatedDivPowerPolyOneVariableStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareLemma_truncated_divPowerPoly_oneVariable : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : Q.P →+* G) (n : ℕ), Q.IsStd δ η → IsLev δ (n + 1) → SemiHom (RingHom.id R) q → IsDPMorphism η δ' q → Function.Surjective q → J' = (Q.ext J).map q → (∀ b, q b = 0 ↔ b ∈ fil η (n + 1)) → ∀ (α : B →+* G) (h : SemiHom (RingHom.id R) α) (hd : IsDPMorphism δ δ' α), (∀ b, α b = q (algebraMap B Q.P b)) → RQ h hd := by
  first | exact @GlobalTheory.PDForm.rq_truncPoly | exact GlobalTheory.PDForm.rq_truncPoly | (intros; apply GlobalTheory.PDForm.rq_truncPoly <;> assumption)
end
