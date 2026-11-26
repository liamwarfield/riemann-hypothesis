module

public import ReciprocityTheory.DualLattices.SubMemOfCompat
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupGeneration
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RbAflat
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RdFlagFin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.HasColenNotUniqueWithoutGuard
noncomputable section

namespace GlobalTheory.HopfOrderCheck

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem vdet_le_of_span_le (v : Valuation C NNReal) (hv : ∀ r : R, v (algebraMap R C r) ≤ 1)
    {X : Type} [Fintype X] [DecidableEq X] (B B' : Matrix X X C)
    (h : Submodule.span R (Set.range fun j x => B x j) ≤
      Submodule.span R (Set.range fun j x => B' x j)) : v B.det ≤ v B'.det := by
  have hc : ∀ j, ∃ c : X → R, ∑ i, c i • (fun x => B' x i) = fun x => B x j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun R).mp (h (Submodule.subset_span ⟨j, rfl⟩))
  choose c hc using hc
  have hB : B = B' * (Matrix.of fun i j => c j i).map (algebraMap R C) := by
    ext x j
    have := congrFun (hc j) x
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] at this
    rw [← this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  have hd : ((Matrix.of fun i j => c j i).map (algebraMap R C)).det
      = algebraMap R C (Matrix.of fun i j => c j i).det := ((algebraMap R C).map_det _).symm
  rw [hB, Matrix.det_mul, map_mul, hd]
  exact mul_le_of_le_one_right' (hv _)

theorem hasColen_unique (v : Valuation C NNReal) (hv : ∀ r : R, v (algebraMap R C r) ≤ 1)
    {X : Type} [Fintype X] [DecidableEq X] {M : Submodule R (X → C)} {c c' : NNReal}
    (h : HasColen R v M c) (h' : HasColen R v M c') : c = c' := by
  obtain ⟨B, hB, rfl⟩ := h
  obtain ⟨B', hB', rfl⟩ := h'
  exact le_antisymm (vdet_le_of_span_le v hv B B' (by rw [← hB, ← hB']))
    (vdet_le_of_span_le v hv B' B (by rw [← hB, ← hB']))

end GlobalTheory.HopfOrderCheck
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagComparisonTheorem
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisColength
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisColength
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_colength : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) (∏ i, s i) → ∀ j : ℕ, HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : flagSub b j → N))) χ) (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), s i) := by
  first | exact @PositivityTheory.HtPt.Rd.gr_partial | exact PositivityTheory.HtPt.Rd.gr_partial
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisColengthStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_basis_colength : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) (∏ i, s i) → ∀ j : ℕ, HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : flagSub b j → N))) χ) (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), s i) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_colength | exact GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_colength | (intros; apply GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_colength <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisLengths
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisLengths
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_lengths : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal) (r : NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) r → ∏ i, s i ≤ r := by
  first | exact @PositivityTheory.HtPt.Rd.flag_om | exact PositivityTheory.HtPt.Rd.flag_om
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisLengthsStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_basis_lengths : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal) (r : NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) r → ∏ i, s i ≤ r := by
  first | exact @GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_lengths | exact GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_lengths | (intros; apply GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_lengths <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NonFundamentalEigenLeSquareAugmentation
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NonFundamentalEigenLeSquareAugmentation
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR.NonFund

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N)

theorem aug_mul {g h : N → C} (hg : g ∈ augIdeal AA.carrier) (hh : h ∈ AA.carrier) :
    g * h ∈ augIdeal AA.carrier := by
  refine ⟨AA.mul_mem _ _ hg.1 hh, ?_⟩
  have h0 : g 0 = 0 := hg.2
  change g 0 * h 0 = 0
  rw [h0, zero_mul]

theorem sq_mul {g h : N → C} (hg : g ∈ sqIdeal (augIdeal AA.carrier)) (hh : h ∈ AA.carrier) :
    g * h ∈ sqIdeal (augIdeal AA.carrier) := by
  unfold sqIdeal at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact Submodule.subset_span ⟨a, ha, b * h, aug_mul AA hb hh, mul_assoc _ _ _⟩
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

def Lev (k : ℕ) (g : N → C) : Prop :=
  g ∈ AA.carrier ∧ (1 ≤ k → g ∈ augIdeal AA.carrier) ∧
    (2 ≤ k → g ∈ sqIdeal (augIdeal AA.carrier))

theorem lev_one : Lev AA 0 1 :=
  ⟨AA.one_mem, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

theorem lev_mul {k l : ℕ} {g h : N → C} (hg : Lev AA k g) (hh : Lev AA l h) :
    Lev AA (k + l) (g * h) := by
  refine ⟨AA.mul_mem _ _ hg.1 hh.1, fun hk => ?_, fun hk => ?_⟩
  · by_cases h1 : 1 ≤ k
    · exact aug_mul AA (hg.2.1 h1) hh.1
    · rw [mul_comm]; exact aug_mul AA (hh.2.1 (by omega)) hg.1
  · by_cases h2 : 2 ≤ k
    · exact sq_mul AA (hg.2.2 h2) hh.1
    · by_cases h3 : 2 ≤ l
      · rw [mul_comm]; exact sq_mul AA (hh.2.2 h3) hg.1
      · exact Submodule.subset_span ⟨g, hg.2.1 (by omega), h, hh.2.1 (by omega), rfl⟩

theorem lev_pow {g : N → C} (hg : g ∈ augIdeal AA.carrier) (k : ℕ) : Lev AA k (g ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact lev_one AA
  | succ k ih =>
    rw [pow_succ]
    exact lev_mul AA ih ⟨hg.1, fun _ => hg, fun h => absurd h (by omega)⟩

theorem lev_prod {ι : Type} (s : Finset ι) (u : ι → N → C) (hu : ∀ i, u i ∈ augIdeal AA.carrier)
    (d : ι → ℕ) : Lev AA (∑ i ∈ s, d i) (∏ i ∈ s, u i ^ d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact lev_one AA
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact lev_mul AA (lev_pow AA (hu a) _) ih

theorem digits_single {f p : ℕ} (d : Fin f → ℕ) (n : Fin f) (hn : d n ≠ 0)
    (hs : ¬ 2 ≤ ∑ i, d i) : ∑ i : Fin f, d i * p ^ (i : ℕ) = p ^ (n : ℕ) := by
  have h := Finset.add_sum_erase Finset.univ d (Finset.mem_univ n)
  have h1 : d n = 1 := by omega
  have h0 : ∑ i ∈ Finset.univ.erase n, d i = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at h0
  rw [Finset.sum_eq_single n, h1, one_mul]
  · intro b _ hb
    rw [h0 b (Finset.mem_erase.2 ⟨hb, Finset.mem_univ b⟩), zero_mul]
  · intro h; exact absurd (Finset.mem_univ n) h

end GlobalTheory.CompanionTheory.Ar.GR.NonFund

open GlobalTheory.CompanionTheory.Ar.GR.NonFund in
theorem _root_.GlobalTheory.CompanionTheory.Relay.non_fundamental_eigen_le_square_augmentation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ χ : MulChar F R, ¬ IsFund p χ → eig AA.carrier χ ≤ sqIdeal (augIdeal AA.carrier) := by
  intro p hpp C _ _ _ v R _ _ hv hp F _ _ _ _ f hc AA hA χ hχ g hg
  obtain ⟨σ, hσ⟩ := fund_ex_relay p C v R hv hp F f hc
  obtain ⟨-, hgen, hfund, -, -⟩ := FundGen.main p C v R hv hp F f hc σ hσ
  obtain ⟨m, hm1, hm2, rfl⟩ := hgen χ
  have hr := eig_rank_one p C v R hv hp F f hc AA hA
  choose c hc0 hcx using fun n : ℕ => (hr (σ ^ p ^ n)).1
  have hp0 : 0 < p := hpp.out.pos
  have hlt : m < p ^ f := by
    have := pow_pos hp0 f
    omega
  obtain ⟨d, hd⟩ : ∃ d : Fin f → Fin p, ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = m := by
    refine ⟨finFunctionFinEquiv.symm ⟨m, hlt⟩, ?_⟩
    rw [← finFunctionFinEquiv_apply, Equiv.apply_symm_apply]
  have hne : ∃ n, (d n : ℕ) ≠ 0 := by
    by_contra hcon
    have h0 : ∀ n, (d n : ℕ) = 0 := fun n => by
      by_contra h; exact hcon ⟨n, h⟩
    simp only [h0, zero_mul, Finset.sum_const_zero] at hd
    omega
  have hx := (GlobalTheory.T.fundamental_ideal_frobenius_powers p C v R hv hp F f hc AA hA σ hσ c hcx).2 d hne
  rw [hd] at hx
  have hs : 2 ≤ ∑ n, (d n : ℕ) := by
    by_contra hs
    obtain ⟨n, hn⟩ := hne
    have := digits_single (p := p) (fun n => (d n : ℕ)) n hn hs
    rw [hd] at this
    rw [this] at hχ
    exact hχ (hfund n)
  obtain ⟨c0, hc0m, rfl⟩ := ((hr (σ ^ m)).2 g).1 hg
  rw [hx, Ideal.mem_span_singleton'] at hc0m
  obtain ⟨r, rfl⟩ := hc0m
  let u : Fin f → F → C := fun n a => algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a)
  have hu : ∀ n, u n ∈ augIdeal AA.carrier := by
    intro n
    have h1 : u n ∈ eig AA.carrier (σ ^ p ^ (n : ℕ)) :=
      ((hr _).2 _).2 ⟨c n, by rw [hcx]; exact Ideal.mem_span_singleton_self _, rfl⟩
    refine ⟨h1.1, ?_⟩
    change algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) 0) = 0
    rw [MulChar.map_zero, mul_zero, map_zero]
  have hprod := (lev_prod AA Finset.univ u hu fun n => (d n : ℕ)).2.2 hs
  convert Submodule.smul_mem _ r hprod using 1
  funext a
  have ha : (σ ^ m) a = ∏ n : Fin f, ((σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ) := by
    rw [MulChar.pow_apply' _ (by omega), ← hd, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [MulChar.pow_apply' _ (pow_pos hp0 _).ne', ← pow_mul, mul_comm]
  rw [ha, mul_assoc, ← Finset.prod_mul_distrib, map_mul, map_prod, Pi.smul_apply,
    Algebra.smul_def, Finset.prod_apply]
  refine congrArg _ (Finset.prod_congr rfl fun n _ => ?_)
  rw [← mul_pow, map_pow, Pi.pow_apply]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NonFundamentalEigenLeSquareAugmentationStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.non_fundamental_eigen_le_square_augmentation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ χ : MulChar F R, ¬ IsFund p χ → eig AA.carrier χ ≤ sqIdeal (augIdeal AA.carrier) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.non_fundamental_eigen_le_square_augmentation | exact GlobalTheory.CompanionTheory.Relay.non_fundamental_eigen_le_square_augmentation | (intros; apply GlobalTheory.CompanionTheory.Relay.non_fundamental_eigen_le_square_augmentation <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusValuation
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusValuation
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR.RankOneColen

lemma two_mul_sum_digit (p f : ℕ) (j : Fin f) :
    (∑ d : Fin f → Fin p, (d j : ℕ)) * 2 = p ^ f * (p - 1) := by
  let e : (Fin f → Fin p) ≃ (Fin f → Fin p) := Equiv.arrowCongr (Equiv.refl _) Fin.revPerm
  have h1 : ∑ d : Fin f → Fin p, ((e d) j : ℕ) = ∑ d : Fin f → Fin p, (d j : ℕ) :=
    e.sum_comp (fun d => (d j : ℕ))
  have h2 : ∀ d : Fin f → Fin p, ((e d) j : ℕ) = p - ((d j : ℕ) + 1) := by
    intro d
    simp [e, Equiv.arrowCongr_apply, Fin.val_rev]
  simp only [h2] at h1
  rw [mul_two]
  nth_rewrite 2 [← h1]
  rw [← Finset.sum_add_distrib]
  have h3 : ∀ d : Fin f → Fin p, (d j : ℕ) + (p - ((d j : ℕ) + 1)) = p - 1 := by
    intro d; have := (d j).2; omega
  simp only [h3, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]

lemma prod_digit_sq (p f : ℕ) (x : Fin f → NNReal) :
    (∏ d : Fin f → Fin p, ∏ j, x j ^ (d j : ℕ)) ^ 2 = (∏ j, x j) ^ (p ^ f * (p - 1)) := by
  have key : ∀ j : Fin f, (∏ d : Fin f → Fin p, x j ^ (d j : ℕ)) ^ 2 = x j ^ (p ^ f * (p - 1)) := by
    intro j
    rw [Finset.prod_pow_eq_pow_sum, ← pow_mul, two_mul_sum_digit]
  calc (∏ d : Fin f → Fin p, ∏ j, x j ^ (d j : ℕ)) ^ 2
      = (∏ j, ∏ d : Fin f → Fin p, x j ^ (d j : ℕ)) ^ 2 := by rw [Finset.prod_comm]
    _ = ∏ j, (∏ d : Fin f → Fin p, x j ^ (d j : ℕ)) ^ 2 := (Finset.prod_pow _ _ _).symm
    _ = ∏ j, x j ^ (p ^ f * (p - 1)) := Finset.prod_congr rfl (fun j _ => key j)
    _ = (∏ j, x j) ^ (p ^ f * (p - 1)) := Finset.prod_pow _ _ _

def num {p f : ℕ} (d : Fin f → Fin p) : ℕ := ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ)

lemma num_eq {p f : ℕ} (d : Fin f → Fin p) : num d = (finFunctionFinEquiv d : ℕ) := by
  rw [num, finFunctionFinEquiv_apply]

lemma num_lt {p f : ℕ} (d : Fin f → Fin p) : num d < p ^ f := by
  rw [num_eq]; exact Fin.isLt _

lemma num_inj {p f : ℕ} {d e : Fin f → Fin p} (h : num d = num e) : d = e := by
  rw [num_eq, num_eq] at h
  exact finFunctionFinEquiv.injective (Fin.ext h)

lemma num_surj {p f m : ℕ} (h : m < p ^ f) : ∃ d : Fin f → Fin p, num d = m :=
  ⟨finFunctionFinEquiv.symm ⟨m, h⟩, by rw [num_eq, Equiv.apply_symm_apply]⟩

lemma num_ne_zero_iff {p f : ℕ} (hp : 0 < p) (d : Fin f → Fin p) :
    num d ≠ 0 ↔ ∃ n, (d n : ℕ) ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    have hc' : ∀ n, (d n : ℕ) = 0 := fun n => by_contra (fun hn => hc ⟨n, hn⟩)
    apply h
    simp [num, hc']
  · rintro ⟨n, hn⟩ h
    apply hn
    rw [num] at h
    have h' := (Finset.sum_eq_zero_iff.mp h) n (Finset.mem_univ _)
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact h''
    · exact absurd h'' (pow_ne_zero _ hp.ne')

lemma prod_Icc_num {M : Type} [CommMonoid M] {p f : ℕ} (hp : 0 < p) (g : ℕ → M)
    (G : (Fin f → Fin p) → M) (h0 : ∀ d, num d = 0 → G d = 1)
    (h1 : ∀ d, num d ≠ 0 → g (num d) = G d) :
    ∏ m ∈ Finset.Icc 1 (p ^ f - 1), g m = ∏ d, G d := by
  classical
  have hfilt : ∏ d ∈ Finset.univ.filter (fun d : Fin f → Fin p => num d ≠ 0), G d = ∏ d, G d :=
    Finset.prod_filter_of_ne (fun d _ hG h0' => hG (h0 d h0'))
  rw [← hfilt]
  symm
  refine Finset.prod_bij (fun d _ => num d) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    have := num_lt d
    rw [Finset.mem_Icc]
    omega
  · intro a _ b _ h
    exact num_inj h
  · intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨d, hd⟩ := num_surj (p := p) (f := f) (show m < p ^ f by omega)
    refine ⟨d, ?_, hd⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    exact (h1 d hd).symm

lemma mono_eq {C R F : Type} [Field C] [CommRing R] [Algebra R C] [Field F] {p f : ℕ}
    (hp : 0 < p) (σ : MulChar F R) (c : ℕ → R) (d : Fin f → Fin p) (hd : num d ≠ 0) (a : F) :
    ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ) =
      algebraMap R C ((∏ n : Fin f, c n ^ (d n : ℕ)) * (σ ^ num d) a) := by
  have hpow' : ∀ n : ℕ, (σ ^ p ^ n) a = σ a ^ p ^ n :=
    fun n => MulChar.pow_apply' σ (pow_ne_zero _ hp.ne') a
  rw [MulChar.pow_apply' σ hd a]
  simp only [hpow']
  simp only [map_mul, map_pow, map_prod]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum, num]
  congr 2
  exact Finset.sum_congr rfl (fun n _ => Nat.mul_comm _ _)

lemma digits_zero {p f : ℕ} (hp : 0 < p) {d : Fin f → Fin p} (hd : num d = 0) (n : Fin f) :
    (d n : ℕ) = 0 := by
  by_contra h
  exact (num_ne_zero_iff hp d).2 ⟨n, h⟩ hd

end GlobalTheory.CompanionTheory.Ar.GR.RankOneColen


open GlobalTheory.CompanionTheory.Ar.GR.RankOneColen in
theorem _root_.GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_valuation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → AA.carrier = Submodule.span R (Set.range fun (d : Fin f → Fin p) (a : F) => ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ)) ∧ ∀ cN, HasColen R v AA.carrier cN → cN ^ 2 = (∏ n : Fin f, v (algebraMap R C (c n))) ^ (p ^ f * (p - 1)) := by
  intro p _ C _ _ _ v R _ _ hv hpv F _ _ _ _ f hcard AA hst σ hσ c hc
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hT := GlobalTheory.T.fundamental_ideal_frobenius_powers p C v R hv hpv F f hcard AA hst σ hσ c hc
  obtain ⟨c', hc', hc'd⟩ : ∃ c' : ℕ → R, (∀ m, xIdeal AA.carrier (σ ^ m) = Ideal.span {c' m}) ∧
      ∀ d : Fin f → Fin p, num d ≠ 0 → c' (num d) = ∏ n : Fin f, c n ^ (d n : ℕ) := by
    refine ⟨fun m => if h : m ≠ 0 ∧ m < p ^ f then
        ∏ n : Fin f, c n ^ ((Classical.choose (num_surj h.2) : Fin f → Fin p) n : ℕ)
      else Classical.choose (eig_rank_one p C v R hv hpv F f hcard AA hst (σ ^ m)).1, ?_, ?_⟩
    · intro m
      dsimp only
      by_cases h : m ≠ 0 ∧ m < p ^ f
      · rw [dite_eq_left h]
        have hd := Classical.choose_spec (num_surj h.2)
        have hne : ∃ n, ((Classical.choose (num_surj h.2) : Fin f → Fin p) n : ℕ) ≠ 0 :=
          (num_ne_zero_iff hp _).mp (by rw [hd]; exact h.1)
        have e : σ ^ m = σ ^ num (Classical.choose (num_surj h.2)) := by rw [hd]
        rw [e]
        exact hT.2 _ hne
      · rw [dite_eq_right h]
        exact (Classical.choose_spec (eig_rank_one p C v R hv hpv F f hcard AA hst (σ ^ m)).1).2
    · intro d hd
      dsimp only
      have h : num d ≠ 0 ∧ num d < p ^ f := ⟨hd, num_lt d⟩
      rw [dite_eq_left h]
      have := num_inj (Classical.choose_spec (num_surj h.2))
      rw [this]
  obtain ⟨hAug, hCar, hCol⟩ := r_decomp_relay p C v R hv hpv F f hcard AA hst σ hσ c' hc'
  refine ⟨?_, ?_⟩
  · have hset : Set.range (fun (d : Fin f → Fin p) (a : F) =>
          ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ)) =
        insert 1 ((fun m a => algebraMap R C (c' m * (σ ^ m) a)) '' ↑(Finset.Icc 1 (p ^ f - 1))) := by
      ext g
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_image, Finset.coe_Icc, Set.mem_Icc]
      constructor
      · rintro ⟨d, rfl⟩
        by_cases h0 : num d = 0
        · left
          funext a
          simp only [Pi.one_apply]
          exact Finset.prod_eq_one (fun n _ => by rw [digits_zero hp h0 n, pow_zero])
        · right
          refine ⟨num d, ⟨by omega, by have := num_lt d; omega⟩, ?_⟩
          funext a
          rw [mono_eq hp σ c d h0 a, hc'd d h0]
      · rintro (rfl | ⟨m, ⟨hm1, hm2⟩, rfl⟩)
        · refine ⟨fun _ => ⟨0, hp⟩, ?_⟩
          funext a
          simp only [Pi.one_apply]
          exact Finset.prod_eq_one (fun n _ => pow_zero _)
        · obtain ⟨d, rfl⟩ := num_surj (p := p) (f := f) (show m < p ^ f by omega)
          have h0 : num d ≠ 0 := by omega
          refine ⟨d, ?_⟩
          funext a
          rw [mono_eq hp σ c d h0 a, hc'd d h0]
    rw [hset, Submodule.span_insert, ← hAug, ← hCar]
  · intro cN hcN
    have huniq : cN = ∏ m ∈ Finset.Icc 1 (p ^ f - 1), v (algebraMap R C (c' m)) := by
      obtain ⟨B, hB, hBd⟩ := hcN
      obtain ⟨B', hB', hB'd⟩ := hCol
      obtain ⟨P, hPu, hP⟩ := AA.lat
      rw [← hBd, ← hB'd, valuation_det_eq_of_span_eq_alt hv hPu (hP.symm.trans hB),
        valuation_det_eq_of_span_eq_alt hv hPu (hP.symm.trans hB')]
    rw [huniq, prod_Icc_num hp (fun m => v (algebraMap R C (c' m)))
      (fun d => ∏ n : Fin f, v (algebraMap R C (c n)) ^ (d n : ℕ)) ?_ ?_]
    · exact prod_digit_sq p f (fun n => v (algebraMap R C (c n)))
    · intro d hd
      exact Finset.prod_eq_one (fun n _ => by rw [digits_zero hp hd n, pow_zero])
    · intro d hd
      simp only [hc'd d hd, map_prod, map_pow]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusValuationStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_ideal_frobenius_valuation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → AA.carrier = Submodule.span R (Set.range fun (d : Fin f → Fin p) (a : F) => ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ)) ∧ ∀ cN, HasColen R v AA.carrier cN → cN ^ 2 = (∏ n : Fin f, v (algebraMap R C (c n))) ^ (p ^ f * (p - 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_valuation | exact GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_valuation | (intros; apply GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_valuation <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisIdeals
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisIdeals
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem flag_colen : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (cs : Fin n → NNReal) (cN : NNReal), (∀ i : Fin n, HasColen R v (stepOrder AA.carrier (flagSub b i) (b i)) (cs i)) → HasColen R v AA.carrier cN → cN ^ (p ^ f) = (∏ i, cs i) ^ Fintype.card N :=
  @PositivityTheory.HtPt.Rc.flag_colen

end GlobalTheory.CompanionTheory.Ar.GR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisIdealsStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_basis_ideals : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (cs : Fin n → NNReal) (cN : NNReal), (∀ i : Fin n, HasColen R v (stepOrder AA.carrier (flagSub b i) (b i)) (cs i)) → HasColen R v AA.carrier cN → cN ^ (p ^ f) = (∏ i, cs i) ^ Fintype.card N := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.flag_colen | exact GlobalTheory.CompanionTheory.Ar.GR.flag_colen | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.flag_colen <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalLengths
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalLengths
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_lengths : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∃ d : Fin n → Fin f → R, (∀ (i : Fin n) (s : Fin f), idealD p AA.carrier (flagSub b i) (b i) (σ ^ p ^ (s : ℕ)) = Ideal.span {d i s}) ∧ HasLen v R (AFQuot p AA.carrier) (∏ i, ∏ s, v (algebraMap R C (d i s))) := by
  first | exact @PositivityTheory.HtPt.Rb.flag_D | exact PositivityTheory.HtPt.Rb.flag_D
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalLengthsStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_fundamental_lengths : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∃ d : Fin n → Fin f → R, (∀ (i : Fin n) (s : Fin f), idealD p AA.carrier (flagSub b i) (b i) (σ ^ p ^ (s : ℕ)) = Ideal.span {d i s}) ∧ HasLen v R (AFQuot p AA.carrier) (∏ i, ∏ s, v (algebraMap R C (d i s))) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_lengths | exact GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_lengths | (intros; apply GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_lengths <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProductInequalitiesForceEquality
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProductInequalitiesForceEquality
open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem grcount : ∀ (T S : Type) [Fintype T] [Fintype S] (a b : ℕ), 0 < a → 0 < b → ∀ (x D d : T → S → NNReal) (r : S → NNReal) (cA cN cO : NNReal), cN ≠ 0 → (∀ t s, x t s ≤ D t s) → ∏ t, ∏ s, D t s = cA → (∏ t, ∏ s, x t s) ^ (a * b) = cN ^ 2 → cA ^ (a * b) = cN ^ 2 → (∀ s, ∏ t, d t s ≤ r s) → ∏ s, r s = cO → ∏ t, ∏ s, d t s = (∏ t, ∏ s, x t s) ^ b → cO ^ a = cN ^ 2 → (∀ t s, D t s = x t s) ∧ ∀ s, ∏ t, d t s = r s :=
  PositivityTheory.HtPt.Rh.grcount

end GlobalTheory.CompanionTheory.Ar.GR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProductInequalitiesForceEqualityStatement
open scoped Matrix TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_inequalities_force_equality : ∀ (T S : Type) [Fintype T] [Fintype S] (a b : ℕ), 0 < a → 0 < b → ∀ (x D d : T → S → NNReal) (r : S → NNReal) (cA cN cO : NNReal), cN ≠ 0 → (∀ t s, x t s ≤ D t s) → ∏ t, ∏ s, D t s = cA → (∏ t, ∏ s, x t s) ^ (a * b) = cN ^ 2 → cA ^ (a * b) = cN ^ 2 → (∀ s, ∏ t, d t s ≤ r s) → ∏ s, r s = cO → ∏ t, ∏ s, d t s = (∏ t, ∏ s, x t s) ^ b → cO ^ a = cN ^ 2 → (∀ t s, D t s = x t s) ∧ ∀ s, ∏ t, d t s = r s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.grcount | exact GlobalTheory.CompanionTheory.Ar.GR.grcount | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.grcount <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagComparisonTheorem
noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR.FlagClose

section Val

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

lemma v_le_of_span_le (hv : v.Integers R) {a b : R} (h : Ideal.span {a} ≤ Ideal.span {b}) :
    v (algebraMap R C a) ≤ v (algebraMap R C b) := by
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.1 (h (Ideal.mem_span_singleton_self a))
  rw [map_mul, map_mul]
  exact mul_le_of_le_one_right' (hv.map_le_one u)

lemma v_eq_of_span_eq (hv : v.Integers R) {a b : R} (h : Ideal.span {a} = Ideal.span {b}) :
    v (algebraMap R C a) = v (algebraMap R C b) :=
  le_antisymm (v_le_of_span_le hv h.le) (v_le_of_span_le hv h.ge)

lemma span_eq_of_le_of_v_eq (hv : v.Integers R) {c d : R} (hc : c ≠ 0)
    (h : Ideal.span {c} ≤ Ideal.span {d})
    (hvv : v (algebraMap R C c) = v (algebraMap R C d)) :
    Ideal.span {c} = Ideal.span {d} := by
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.1 (h (Ideal.mem_span_singleton_self c))
  have hu0 : u ≠ 0 := by rintro rfl; simp at hc
  have hd0 : d ≠ 0 := by rintro rfl; simp at hc
  have hinj := hv.hom_inj
  have hd1 : algebraMap R C d ≠ 0 := fun e => hd0 (hinj (by simpa using e))
  have hu1 : algebraMap R C u ≠ 0 := fun e => hu0 (hinj (by simpa using e))
  have hvd : v (algebraMap R C d) ≠ 0 := (Valuation.ne_zero_iff v).2 hd1
  have hvu : v (algebraMap R C u) = 1 := by
    rw [map_mul, map_mul] at hvv
    exact mul_left_cancel₀ hvd (by rw [hvv, mul_one])
  exact Ideal.span_singleton_mul_right_unit (hv.isUnit_of_one (IsUnit.mk0 _ hu1) hvu) d

lemma hasLen_le_one' (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {x : NNReal}
    (h : HasLen v R M x) : x ≤ 1 := by
  obtain ⟨m, c, -, rfl⟩ := h
  exact Finset.prod_le_one' fun i _ => hv.map_le_one _

end Val

lemma prod_fin_shift (f : ℕ) (G : ℕ → NNReal) (h : G f = G 0) (h0 : G 0 ≠ 0) :
    ∏ s : Fin f, G ((s : ℕ) + 1) = ∏ s : Fin f, G s := by
  rw [Fin.prod_univ_eq_prod_range (fun i => G (i + 1)), Fin.prod_univ_eq_prod_range G]
  have h1 := Finset.prod_range_succ' G f
  have h2 := Finset.prod_range_succ G f
  rw [h1, h] at h2
  exact mul_right_cancel₀ h0 h2

section Char

variable {R : Type} [CommRing R] {F : Type} [Field F] [Fintype F]

lemma pow_card_char (χ : MulChar F R) : χ ^ Fintype.card F = χ := by
  ext a
  rw [MulChar.pow_apply_coe, ← map_pow, FiniteField.pow_card]

lemma pow_period {p f : ℕ} (hf : Fintype.card F = p ^ f) (σ : MulChar F R) (s : ℕ) :
    σ ^ p ^ (s + f) = σ ^ p ^ s := by
  rw [pow_add, pow_mul, ← hf, pow_card_char]

lemma pow_period_mul {p f : ℕ} (hf : Fintype.card F = p ^ f) (σ : MulChar F R) (s k : ℕ) :
    σ ^ p ^ (s + f * k) = σ ^ p ^ s := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← add_assoc, pow_period hf, ih]

lemma pow_mod {p f : ℕ} (hf : Fintype.card F = p ^ f) (σ : MulChar F R) (s : ℕ) :
    σ ^ p ^ (s % f) = σ ^ p ^ s := by
  conv_rhs => rw [← Nat.mod_add_div s f]
  rw [pow_period_mul hf]

lemma prod_chars {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (σ : MulChar F R)
    (ho : orderOf σ = p ^ f - 1)
    (hfund : ∀ m, IsFund p (σ ^ m) → ∃ n < f, σ ^ m = σ ^ p ^ n)
    (L : MulChar F R → NNReal) (h1 : ∀ χ, ¬ IsFund p χ → L χ = 1) :
    ∏ m ∈ Finset.Icc 1 (p ^ f - 1), L (σ ^ m) = ∏ s : Fin f, L (σ ^ p ^ (s : ℕ)) := by
  have hp2 := hp.two_le
  have hle : ∀ n < f, 1 ≤ p ^ n ∧ p ^ n ≤ p ^ f - 1 := by
    intro n hn
    refine ⟨Nat.one_le_pow _ _ hp.pos, ?_⟩
    have h2 : p ^ (n + 1) ≤ p ^ f := Nat.pow_le_pow_right hp.pos hn
    have h3 : p ^ (n + 1) = p ^ n * p := pow_succ p n
    have h4 : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.pos
    have h5 : p ^ n * 2 ≤ p ^ n * p := Nat.mul_le_mul_left _ hp2
    omega
  have hinj : Function.Injective (fun s : Fin f => p ^ (s : ℕ)) := fun a b e =>
    Fin.ext (Nat.pow_right_injective hp2 e)
  have himg : ∏ s : Fin f, L (σ ^ p ^ (s : ℕ)) =
      ∏ m ∈ (Finset.univ : Finset (Fin f)).image (fun s : Fin f => p ^ (s : ℕ)), L (σ ^ m) := by
    rw [Finset.prod_image (fun a _ b _ e => hinj e)]
  rw [himg]
  symm
  apply Finset.prod_subset
  · intro m hm
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hm
    exact Finset.mem_Icc.2 (hle s s.2)
  · intro m hm hnot
    apply h1
    intro hfm
    obtain ⟨n, hn, e⟩ := hfund m hfm
    apply hnot
    refine Finset.mem_image.2 ⟨⟨n, hn⟩, Finset.mem_univ _, ?_⟩
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.1 hm
    obtain ⟨hn1, hn2⟩ := hle n hn
    have hmod : m ≡ p ^ n [MOD orderOf σ] := pow_eq_pow_iff_modEq.1 e
    rw [ho] at hmod
    refine (Nat.ModEq.eq_of_abs_lt hmod ?_).symm
    rw [abs_lt]
    omega

end Char

end GlobalTheory.CompanionTheory.Ar.GR.FlagClose

namespace GlobalTheory.CompanionTheory.Ar.GR


open FlagClose in
theorem flagStatement_holds : FlagStatement := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ N _ _ _ _ AA hFS hT n b hG σ hσ
  obtain ⟨f, hf0, hf⟩ : ∃ f : ℕ, 0 < f ∧ Fintype.card F = p ^ f := by
    obtain ⟨k, -, e⟩ := FiniteField.card F p
    exact ⟨k, k.pos, e⟩
  have hpp : p.Prime := Fact.out
  obtain ⟨hord, -, hfp, hfund, -⟩ := GlobalTheory.T.teichmuller_character_order_generates p C v R hv hp F f hf σ hσ
  have hFp : ∀ s, IsFund p (σ ^ p ^ s) := hfp
  have hbK : ∀ i : Fin n, b i ∉ flagSub b i := fun i =>
    b.linearIndependent.notMem_span_image (by simp)
  have hstep := fun i : Fin n =>
    GlobalTheory.T.stable_hopf_order_subgroup_translation p C v R hv hp F f hf N AA hFS (flagSub b i) (b i) (hbK i)
  choose S hSc hSF using fun i => (hstep i).1
  have hres : ∀ i : Fin n, stepOrder AA.carrier (flagSub b i) (b i) =
      stepOrderRes AA.carrier (flagSub b i) (b i) := fun i => (hstep i).2
  choose c hc0 hcX using fun (i : Fin n) (s : ℕ) =>
    (GlobalTheory.T.character_ideal_principal_eigen p C v R hv hp F f hf (S i) (hSF i) (σ ^ p ^ s)).1
  have hom := fun i : Fin n =>
    GlobalTheory.T.fundamental_ideal_frobenius_product p C v R hv hp F f hf (S i) (hSF i) σ hσ (c i) (hcX i)
  choose δ hδ using fun (i : Fin n) (s : ℕ) => (hom i s).2.1
  have hδL : ∀ (i : Fin n) (s : ℕ), HasLen v R (OmType (S i).carrier (σ ^ p ^ (s + 1)))
      (v (algebraMap R C (δ i s))) := fun i s => (hom i s).2.2 _ (hδ i s)
  have hstepL : ∀ (i : Fin n) (s : ℕ),
      HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) (σ ^ p ^ (s + 1)))
        (v (algebraMap R C (δ i s))) := by
    intro i s
    rw [← hSc i]
    exact hδL i s
  have hXc : ∀ (i : Fin n) (s : ℕ),
      idealX AA.carrier (flagSub b i) (b i) (σ ^ p ^ s) = Ideal.span {c i s} := by
    intro i s
    show xIdeal (stepOrder AA.carrier (flagSub b i) (b i)) (σ ^ p ^ s) = _
    rw [← hSc i]
    exact hcX i s
  obtain ⟨d, hdD, hdL⟩ := GlobalTheory.T.stable_hopf_order_fundamental_lengths p C v R hv hp F f hf N AA hFS σ hσ n b
  obtain ⟨cA, cN, cO, hcA, hcN, hcO, e1, e2⟩ := hT
  obtain ⟨hLex, hLprod⟩ := GlobalTheory.T.stable_hopf_order_fundamental_ideal p C v R hv hp F f hf N AA hFS σ hσ
  choose L hL0 hL using hLex

  have hnf : ∀ χ : MulChar F R, ¬ IsFund p χ → L χ = 1 := by
    intro χ hχ
    have hsub : ∀ i : Fin n,
        HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) 1 := by
      intro i
      rw [← hSc i]
      have hle := GlobalTheory.T.non_fundamental_eigen_le_square_augmentation p C v R hv hp F f hf (S i) (hSF i) χ hχ
      haveI : Subsingleton (OmType (S i).carrier χ) := by
        refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 ?_)
        intro x _
        exact hle x.2
      exact hasLen_subsingleton v R _
    have h1 := GlobalTheory.T.stable_hopf_order_basis_lengths p C v R hv hp F f hf N AA hFS n b χ (fun _ => 1) (L χ) hsub (hL χ)
    exact le_antisymm (hasLen_le_one' hv (hL χ)) (by simpa using h1)

  have hcN0 : cN ≠ 0 := by
    obtain ⟨B, hB, h⟩ := AA.lat
    have e := GlobalTheory.HopfOrderCheck.hasColen_unique v (fun r => hv.map_le_one r) hcN ⟨B, h, rfl⟩
    rw [e]
    exact (Valuation.ne_zero_iff v).2 hB.ne_zero

  have hvc0 : ∀ (i : Fin n) (s : ℕ), v (algebraMap R C (c i s)) ≠ 0 := fun i s =>
    (Valuation.ne_zero_iff v).2 fun e => hc0 i s (hv.hom_inj (by simpa using e))
  have hcmod : ∀ (i : Fin n) (s : ℕ), Ideal.span {c i (s % f)} = Ideal.span {c i s} := by
    intro i s
    rw [← hXc, ← hXc, pow_mod hf]
  have hvper : ∀ (i : Fin n), v (algebraMap R C (c i f)) = v (algebraMap R C (c i 0)) := by
    intro i
    have h := hcmod i f
    rw [Nat.mod_self] at h
    exact (v_eq_of_span_eq hv h).symm
  have hxD : ∀ (t : Fin n) (s : Fin f),
      v (algebraMap R C (c t s)) ≤ v (algebraMap R C (d t s)) := by
    intro t s
    have h := GlobalTheory.T.stable_hopf_order_subgroup_generation p C v R hv hp F f hf N AA hFS (flagSub b t) (b t) (hbK t) (hG t)
      (σ ^ p ^ (s : ℕ)) (hFp s)
    rw [hXc, hdD] at h
    exact v_le_of_span_le hv h
  have hDA : ∏ t, ∏ s, v (algebraMap R C (d t s)) = cA := hasLen_unique hv hdL hcA

  choose cs hcs using fun i : Fin n => hasColen_of_lat v (S i).lat
  have hcsq : ∀ i : Fin n, cs i ^ 2 =
      (∏ s : Fin f, v (algebraMap R C (c i s))) ^ (p ^ f * (p - 1)) := fun i =>
    (GlobalTheory.T.fundamental_ideal_frobenius_valuation p C v R hv hp F f hf (S i) (hSF i) σ hσ (c i) (hcX i)).2 _ (hcs i)
  have hcfl : cN ^ (p ^ f) = (∏ i, cs i) ^ Fintype.card N :=
    GlobalTheory.T.stable_hopf_order_basis_ideals p C v R hv hp F f hf N AA hFS n b cs cN
      (fun i => by rw [← hSc i]; exact hcs i) hcN
  have hxN : (∏ t, ∏ s : Fin f, v (algebraMap R C (c t s))) ^ (Fintype.card N * (p - 1)) =
      cN ^ 2 := by
    have hq : p ^ f ≠ 0 := pow_ne_zero _ hpp.ne_zero
    refine (pow_left_inj₀ zero_le' zero_le' hq).1 ?_
    calc ((∏ t, ∏ s : Fin f, v (algebraMap R C (c t s))) ^ (Fintype.card N * (p - 1))) ^ p ^ f
        = (∏ t, (∏ s : Fin f, v (algebraMap R C (c t s))) ^ (p ^ f * (p - 1))) ^ Fintype.card N := by
          rw [Finset.prod_pow, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = (∏ t, cs t ^ 2) ^ Fintype.card N := by simp only [hcsq]
      _ = (cN ^ 2) ^ p ^ f := by
          rw [Finset.prod_pow, ← pow_mul, pow_right_comm cN, hcfl, ← pow_mul, mul_comm 2]

  have hdx : ∏ t, ∏ s : Fin f, v (algebraMap R C (δ t s)) =
      (∏ t, ∏ s : Fin f, v (algebraMap R C (c t s))) ^ (p - 1) := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun t _ => ?_
    have hP : ∏ s : Fin f, v (algebraMap R C (c t s)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun s _ => hvc0 t s
    have hsh := prod_fin_shift f (fun s => v (algebraMap R C (c t s))) (hvper t) (hvc0 t 0)
    have hmul : (∏ s : Fin f, v (algebraMap R C (c t s))) ^ p =
        (∏ s : Fin f, v (algebraMap R C (δ t s))) *
          ∏ s : Fin f, v (algebraMap R C (c t s)) := by
      rw [← Finset.prod_pow]
      conv_rhs => rw [← hsh]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [← map_pow, ← map_pow, hδ, map_mul, map_mul]
    have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel hpp.one_le).symm
    have h2 : (∏ s : Fin f, v (algebraMap R C (c t s))) ^ (p - 1) *
        ∏ s : Fin f, v (algebraMap R C (c t s)) =
        (∏ s : Fin f, v (algebraMap R C (c t s))) ^ p := by
      rw [← pow_succ, ← hp1]
    exact (mul_right_cancel₀ hP (h2.trans hmul)).symm
  have hrle : ∀ s : Fin f, ∏ t, v (algebraMap R C (δ t s)) ≤ L (σ ^ p ^ ((s : ℕ) + 1)) :=
    fun s => GlobalTheory.T.stable_hopf_order_basis_lengths p C v R hv hp F f hf N AA hFS n b (σ ^ p ^ ((s : ℕ) + 1))
      (fun i => v (algebraMap R C (δ i s))) _ (fun i => hstepL i s) (hL _)
  have hrO : ∏ s : Fin f, L (σ ^ p ^ ((s : ℕ) + 1)) = cO := by
    have h1 := prod_fin_shift f (fun s => L (σ ^ p ^ s))
      (by simpa using congrArg L (pow_period hf σ 0)) (hL0 _)
    have h2 := prod_chars hpp hf0 σ hord (fun m hm => hfund _ hm) L hnf
    have h3 := hasLen_unique hv (hLprod (fun m => L (σ ^ m)) (fun m _ => hL _)) hcO
    exact h1.trans (h2.symm.trans h3)
  obtain ⟨hDx, hlen⟩ := GlobalTheory.T.product_inequalities_force_equality (Fin n) (Fin f) (Fintype.card N) (p - 1) Fintype.card_pos
    (Nat.sub_pos_of_lt hpp.one_lt)
    (fun t s => v (algebraMap R C (c t s))) (fun t s => v (algebraMap R C (d t s)))
    (fun t s => v (algebraMap R C (δ t s))) (fun s => L (σ ^ p ^ ((s : ℕ) + 1))) cA cN cO hcN0
    hxD hDA hxN e1 hrle hrO hdx e2

  have hCD : ∀ (i : Fin n) (s : Fin f), Ideal.span {c i s} = Ideal.span {d i s} := by
    intro i s
    refine span_eq_of_le_of_v_eq hv (hc0 i s) ?_ (hDx i s).symm
    have h := GlobalTheory.T.stable_hopf_order_subgroup_generation p C v R hv hp F f hf N AA hFS (flagSub b i) (b i) (hbK i) (hG i)
      (σ ^ p ^ (s : ℕ)) (hFp s)
    rwa [hXc, hdD] at h
  have hD : ∀ (i : Fin n) (s : ℕ),
      idealD p AA.carrier (flagSub b i) (b i) (σ ^ p ^ s) = Ideal.span {c i s} := by
    intro i s
    have hs : s % f < f := Nat.mod_lt _ hf0
    have h := hdD i ⟨s % f, hs⟩
    have h' := hCD i ⟨s % f, hs⟩
    simp only at h h'
    rw [pow_mod hf] at h
    rw [h, ← h', hcmod]
  have hsucc : ∀ s : ℕ, σ ^ p ^ (s % f + 1) = σ ^ p ^ (s + 1) := by
    intro s
    rw [pow_succ, pow_succ, pow_mul, pow_mul, pow_mod hf]
  have hall : ∀ s : ℕ, HasLen v R (OmType AA.carrier (σ ^ p ^ (s + 1)))
      (∏ i, v (algebraMap R C (δ i s))) := by
    intro s
    have hs : s % f < f := Nat.mod_lt _ hf0
    have h := hlen ⟨s % f, hs⟩
    simp only at h
    have hδe : ∀ i : Fin n, v (algebraMap R C (δ i s)) = v (algebraMap R C (δ i (s % f))) := by
      intro i
      have h2 := hδL i (s % f)
      rw [hsucc] at h2
      exact hasLen_unique hv (hδL i s) h2
    simp only [hδe]
    rw [h, hsucc]
    exact hL _
  refine ⟨c, δ, fun i s => ⟨hc0 i s, hXc i s, ?_, hD i s, hδ i s, hstepL i s⟩, hall, ?_⟩
  · rw [← hres i, ← hSc i]
    exact hcX i s
  · intro j s
    exact GlobalTheory.T.stable_hopf_order_basis_colength p C v R hv hp F f hf N AA hFS n b (σ ^ p ^ (s + 1))
      (fun i => v (algebraMap R C (δ i s))) (fun i => hstepL i s) (hall s) j

end GlobalTheory.CompanionTheory.Ar.GR
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagComparisonTheoremStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_comparison_theorem : GlobalTheory.CompanionTheory.Ar.GR.FlagStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.flagStatement_holds | exact GlobalTheory.CompanionTheory.Ar.GR.flagStatement_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.flagStatement_holds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractElementary
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractElementary
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → IsTight v p AA.carrier → IsTight v p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) := by
  first | exact @PositivityTheory.HtPt.Re.ret_tight | exact PositivityTheory.HtPt.Re.ret_tight
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractElementaryStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_retract_elementary : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → IsTight v p AA.carrier → IsTight v p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary | exact GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary | (intros; apply GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbelianFactorTightFieldAction
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem flagConcl_directFactor_of_subquotient :
    SubquotientStatement → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, (∀ x : N, p • x = 0) → IsAbFactor p AA.carrier → IsTight v p AA.carrier → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (Nw : Type) [AddCommGroup Nw] [Module F Nw] [Fintype Nw] [DecidableEq Nw] (i : Nw →+ N) (π : N →+ Nw), (∀ y, π (i y) = y) → (∀ h ∈ AA.carrier, (fun x => h (i (π x))) ∈ AA.carrier) → FStable F (AA.carrier.map (LinearMap.funLeft R C (i : Nw → N))) → ∀ (n : ℕ) (b : Module.Basis (Fin n) F Nw) (σ : MulChar F R), IsFund p σ → FlagConcl v p (AA.carrier.map (LinearMap.funLeft R C (i : Nw → N))) b σ := by
  intro hS p _ C _ _ _ v R _ _ hInt hp hcomp N _ _ _ AA hpN hab htight F _ _ _ _ Nw _ _ _ _ i π hπi
    hstab hFS n b σ hσ
  obtain ⟨⟨A', hA'⟩, -, hgen⟩ := GlobalTheory.T.hopf_order_retract_restriction p C v R hInt hp N AA Nw i π hπi hstab
  have ht' := GlobalTheory.T.hopf_order_retract_elementary p C v R hInt hp N hpN AA Nw i π hπi hstab htight
  rw [← hA'] at hFS ht' ⊢
  refine GlobalTheory.T.flag_comparison_theorem p C v R hInt hp F Nw A' hFS ht' n b ?_ σ hσ
  intro k
  rw [hA']
  exact hgen _ (hS p C v R hInt hp hcomp N AA.carrier hab _)

end GlobalTheory.CompanionTheory.Ar.GR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbelianFactorTightFieldActionStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_factor_tight_field_action : SubquotientStatement → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, (∀ x : N, p • x = 0) → IsAbFactor p AA.carrier → IsTight v p AA.carrier → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (Nw : Type) [AddCommGroup Nw] [Module F Nw] [Fintype Nw] [DecidableEq Nw] (i : Nw →+ N) (π : N →+ Nw), (∀ y, π (i y) = y) → (∀ h ∈ AA.carrier, (fun x => h (i (π x))) ∈ AA.carrier) → FStable F (AA.carrier.map (LinearMap.funLeft R C (i : Nw → N))) → ∀ (n : ℕ) (b : Module.Basis (Fin n) F Nw) (σ : MulChar F R), IsFund p σ → FlagConcl v p (AA.carrier.map (LinearMap.funLeft R C (i : Nw → N))) b σ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.flagConcl_directFactor_of_subquotient | exact GlobalTheory.CompanionTheory.Ar.GR.flagConcl_directFactor_of_subquotient | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.flagConcl_directFactor_of_subquotient <;> assumption)
end
