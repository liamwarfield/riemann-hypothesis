module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WBMemLatS
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothingFundamentalDomainIntegral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureUnitaryGroupInvariant

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFieldEmbeddingsDifferFrobenius
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFieldEmbeddingsDifferFrobenius
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem exists_frobenius_pow_of_ringHoms : ∀ {l : ℕ} [Fact l.Prime] {k D : Type} [Field k] [Finite k] [CommRing D] [IsDomain D] [CharP D l]
    (α β : k →+* D), ∃ i : ℕ, ∀ x, β x = α x ^ l ^ i := by
  intro l _ k D _ _ _ _ _ α β
  haveI : CharP k l := α.charP α.injective l
  exact GlobalTheory.ResidueChar.exists_pow_of_finite_field l α β

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFieldEmbeddingsDifferFrobeniusStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_field_embeddings_differ_frobenius : ∀ {l : ℕ} [Fact l.Prime] {k D : Type} [Field k] [Finite k] [CommRing D] [IsDomain D] [CharP D l]
    (α β : k →+* D), ∃ i : ℕ, ∀ x, β x = α x ^ l ^ i := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.exists_frobenius_pow_of_ringHoms | exact GlobalTheory.CompanionTheory.LTPer.Tilt.exists_frobenius_pow_of_ringHoms | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.exists_frobenius_pow_of_ringHoms <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerDividesFrobeniusDifference
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerDividesFrobeniusDifference
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem dvd_pow_qOf_sub_self : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), (Ideal.span {π}).IsMaximal →
    Finite (↥(OL K) ⧸ Ideal.span {π}) → ∀ c : ↥(OL K), π ∣ c ^ qOf π - c := by
  intro l _ K π hmax hfin c
  set_option synthInstance.maxHeartbeats 200000 in
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem,
      map_sub (Ideal.Quotient.mk _), map_pow (Ideal.Quotient.mk _), sub_eq_zero]
  letI := Ideal.Quotient.field (Ideal.span {π})
  letI := Fintype.ofFinite (↥(OL K) ⧸ Ideal.span {π})
  rw [qOf, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card _

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerDividesFrobeniusDifferenceStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_divides_frobenius_difference : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), (Ideal.span {π}).IsMaximal →
    Finite (↥(OL K) ⧸ Ideal.span {π}) → ∀ c : ↥(OL K), π ∣ c ^ qOf π - c := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.dvd_pow_qOf_sub_self | exact GlobalTheory.CompanionTheory.LTPer.Tilt.dvd_pow_qOf_sub_self | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.dvd_pow_qOf_sub_self <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerCompatibleSequenceApproximation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerCompatibleSequenceApproximation
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

variable {l : ℕ} [Fact l.Prime]

private def vv (a : ℕ → Tl l) (f n m : ℕ) : Tl l := a (n + m) ^ l ^ (f * m)

private theorem vv_step (a : ℕ → Tl l) {f : ℕ} {ρ : ℝ} (h : ∀ n, ‖a (n + 1) ^ l ^ f - a n‖ ≤ ρ)
    (n m : ℕ) : ‖vv a f n (m + 1) - vv a f n m‖ ≤ ρ ^ l ^ (f * m) := by
  have e : vv a f n (m + 1) = (a (n + m + 1) ^ l ^ f) ^ l ^ (f * m) := by
    rw [vv, ← pow_mul, ← pow_add, ← add_assoc, mul_add, mul_one, add_comm (f * m) f]
  rw [e, vv, norm_sub_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h _) _

private theorem pow_bound {f : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hf : 0 < f) (m : ℕ) :
    ρ ^ l ^ (f * m) ≤ ρ ^ m := by
  refine pow_le_pow_of_le_one hρ0 hρ1.le ?_
  have h2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have h3 : m ≤ f * m := Nat.le_mul_of_pos_left m hf
  exact h3.trans (Nat.lt_pow_self h2).le

private theorem vv_near (a : ℕ → Tl l) {f : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : ∀ n, ‖a (n + 1) ^ l ^ f - a n‖ ≤ ρ) (n m : ℕ) : ‖vv a f n m - a n‖ ≤ ρ := by
  induction m with
  | zero => simpa [vv] using hρ0
  | succ m ih =>
    have e : vv a f n (m + 1) - a n = (vv a f n (m + 1) - vv a f n m) + (vv a f n m - a n) := by
      abel
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
    refine (vv_step a h n m).trans ?_
    exact pow_le_of_le_one hρ0 hρ1.le (pow_pos (Fact.out : l.Prime).pos _).ne'

theorem exists_tilt_lift_compat {l : ℕ} [Fact l.Prime] (f : ℕ) (ρ : ℝ) (hf : 0 < f)
    (hl : ‖(l : ℂ_[l])‖ ≤ ρ) (hρ1 : ρ < 1) (Z : ℕ → ℂ_[l])
    (hZ : ∀ n, ‖Z n‖ ≤ 1) (hc : ∀ n, ‖Z (n + 1) ^ l ^ f - Z n‖ ≤ ρ) :
    ∃ u : ℕ → Tl l, (∀ n, u (n + 1) ^ l ^ f = u n) ∧ ∀ n, ‖sh (u n) - Z n‖ ≤ ρ := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hl
  choose a ha using fun n => exists_sh_near (l := l) (Z n) (hZ n)
  have ha' : ∀ n, ‖sh (a n) - Z n‖ ≤ ρ := fun n => (ha n).trans hl
  have hd : ∀ n, ‖a (n + 1) ^ l ^ f - a n‖ ≤ ρ := by
    intro n
    refine norm_sub_le_of_near hl ?_
    have h1 := near_pow hl (hZ (n + 1)) (ha' (n + 1)) (l ^ f)
    have e : sh (a (n + 1) ^ l ^ f) - sh (a n) =
        (sh (a (n + 1) ^ l ^ f) - Z (n + 1) ^ l ^ f) +
          ((Z (n + 1) ^ l ^ f - Z n) + -(sh (a n) - Z n)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc n) ?_)
    rw [norm_neg]
    exact ha' n
  have hcau : ∀ n, CauchySeq (vv a f n) := by
    intro n
    refine cauchySeq_of_le_geometric ρ 1 hρ1 fun m => ?_
    rw [dist_comm, dist_eq_norm, one_mul]
    exact (vv_step a hd n m).trans (pow_bound hρ0 hρ1 hf m)
  choose u hu using fun n => cauchySeq_tendsto_of_complete (hcau n)
  refine ⟨u, fun n => ?_, fun n => ?_⟩
  · have h1 : Filter.Tendsto (fun m => vv a f (n + 1) m ^ l ^ f) Filter.atTop
        (nhds (u (n + 1) ^ l ^ f)) := (hu (n + 1)).pow _
    have h2 : Filter.Tendsto (fun m => vv a f n (m + 1)) Filter.atTop (nhds (u n)) :=
      (hu n).comp (Filter.tendsto_add_atTop_nat 1)
    have e : (fun m => vv a f (n + 1) m ^ l ^ f) = fun m => vv a f n (m + 1) := by
      funext m
      rw [vv, vv, ← pow_mul, ← pow_add, mul_add, mul_one, add_comm (f * m) f, add_assoc,
        add_comm 1 m]
    rw [e] at h1
    exact tendsto_nhds_unique h1 h2
  · have h1 : ‖u n - a n‖ ≤ ρ :=
      le_of_tendsto (((hu n).sub_const (a n)).norm)
        (Filter.Eventually.of_forall fun m => vv_near a hρ0 hρ1 hd n m)
    have h2 := near_of_norm_sub_le hl h1
    have e : sh (u n) - Z n = (sh (u n) - sh (a n)) + (sh (a n) - Z n) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 (ha' n))

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerCompatibleSequenceApproximationStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_compatible_sequence_approximation : ∀ {l : ℕ} [Fact l.Prime] (f : ℕ) (ρ : ℝ), 0 < f → ‖(l : ℂ_[l])‖ ≤ ρ → ρ < 1 → ∀ Z : ℕ → ℂ_[l],
    (∀ n, ‖Z n‖ ≤ 1) → (∀ n, ‖Z (n + 1) ^ l ^ f - Z n‖ ≤ ρ) →
    ∃ u : ℕ → Tl l, (∀ n, u (n + 1) ^ l ^ f = u n) ∧ ∀ n, ‖sh (u n) - Z n‖ ≤ ρ := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.exists_tilt_lift_compat | exact GlobalTheory.CompanionTheory.LTPer.Tilt.exists_tilt_lift_compat | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.exists_tilt_lift_compat <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerFixedPointApproximation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerFixedPointApproximation
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem exists_fixed_near : ∀ {l : ℕ} [Fact l.Prime] (f : ℕ) (ρ : ℝ), 0 < f → ‖(l : ℂ_[l])‖ ≤ ρ → ρ < 1 → ∀ c : ℂ_[l],
    ‖c‖ ≤ 1 → ‖c ^ l ^ f - c‖ ≤ ρ → ∃ y : Tl l, y ^ l ^ f = y ∧ ‖sh y - c‖ ≤ ρ := by
  intro l _ f ρ hf hρ hρ1 c hc hcf
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hρ
  obtain ⟨a, ha⟩ := exists_sh_near c hc
  have ha' : ‖sh a - c‖ ≤ ρ := ha.trans hρ
  have hq1 : 1 ≤ l ^ f := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  have hq2 : 2 ≤ l ^ f := Nat.one_lt_pow hf.ne' (Fact.out : l.Prime).one_lt

  have h0 : ‖a ^ l ^ f - a‖ ≤ ρ := by
    refine norm_sub_le_of_near hρ ?_
    have e : sh (a ^ l ^ f) - sh a =
        (sh (a ^ l ^ f) - c ^ l ^ f) + ((c ^ l ^ f - c) + -(sh a - c)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (near_pow hρ hc ha' _) ?_)
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hcf ?_)
    rwa [norm_neg]
  let u : ℕ → Tl l := fun n => a ^ l ^ (f * n)
  have hstep : ∀ n, u (n + 1) = u n ^ l ^ f := by
    intro n
    show a ^ l ^ (f * (n + 1)) = (a ^ l ^ (f * n)) ^ l ^ f
    rw [← pow_mul, ← pow_add, Nat.mul_succ]
  have hdiff : ∀ n, ‖u (n + 1) - u n‖ ≤ ρ ^ (l ^ (f * n)) := by
    intro n
    have e : u (n + 1) - u n = (a ^ l ^ f) ^ l ^ (f * n) - a ^ l ^ (f * n) := by
      show a ^ l ^ (f * (n + 1)) - a ^ l ^ (f * n) = _
      rw [← pow_mul, ← pow_add, Nat.mul_succ, Nat.add_comm]
    rw [e, norm_sub_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h0 _
  have hdiff1 : ∀ n, ‖u (n + 1) - u n‖ ≤ ρ := by
    intro n
    refine (hdiff n).trans ?_
    have : 1 ≤ l ^ (f * n) := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
    simpa using pow_le_pow_of_le_one hρ0 hρ1.le this
  have hgeom : ∀ n, dist (u n) (u (n + 1)) ≤ 1 * ρ ^ n := by
    intro n
    rw [dist_comm, dist_eq_norm, one_mul]
    refine (hdiff n).trans (pow_le_pow_of_le_one hρ0 hρ1.le ?_)
    have h1 : n < l ^ n := Nat.lt_pow_self (Fact.out : l.Prime).one_lt
    have h2 : l ^ n ≤ l ^ (f * n) :=
      Nat.pow_le_pow_right (Fact.out : l.Prime).pos (Nat.le_mul_of_pos_left n hf)
    omega
  have hcau : CauchySeq u := cauchySeq_of_le_geometric ρ 1 hρ1 hgeom
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcau
  have hclose : ∀ n, ‖u n - a‖ ≤ ρ := by
    intro n
    induction n with
    | zero => simpa [u] using hρ0
    | succ n ih =>
      have e : u (n + 1) - a = (u (n + 1) - u n) + (u n - a) := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hdiff1 n) ih)
  have hya : ‖y - a‖ ≤ ρ :=
    le_of_tendsto ((hy.sub_const a).norm) (Filter.Eventually.of_forall hclose)
  refine ⟨y, ?_, ?_⟩
  · have h1 : Filter.Tendsto (fun n => u n ^ l ^ f) Filter.atTop (nhds (y ^ l ^ f)) := hy.pow _
    have h2 : Filter.Tendsto (fun n => u n ^ l ^ f) Filter.atTop (nhds y) := by
      simpa only [hstep] using (Filter.tendsto_add_atTop_iff_nat 1).2 hy
    exact tendsto_nhds_unique h1 h2
  · have e : sh y - c = (sh y - sh a) + (sh a - c) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (near_of_norm_sub_le hρ hya) ha')

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerFixedPointApproximationStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_fixed_point_approximation : ∀ {l : ℕ} [Fact l.Prime] (f : ℕ) (ρ : ℝ), 0 < f → ‖(l : ℂ_[l])‖ ≤ ρ → ρ < 1 → ∀ c : ℂ_[l],
    ‖c‖ ≤ 1 → ‖c ^ l ^ f - c‖ ≤ ρ → ∃ y : Tl l, y ^ l ^ f = y ∧ ‖sh y - c‖ ≤ ρ := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.exists_fixed_near | exact GlobalTheory.CompanionTheory.LTPer.Tilt.exists_fixed_near | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.exists_fixed_near <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerCharacterEqResidueLift
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerCharacterEqResidueLift
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem isUnit_BdRp_of_thB {l : ℕ} [Fact l.Prime] {u : Formalism.Per6.BdRp l} (h : thB l u ≠ 0) :
    IsUnit u := by
  change IsUnit (show BDeRhamPlus (GroundTheory.PAdicHodge.normInteger ℂ_[l]) l from u)
  by_contra hy
  have h2 := (IsLocalRing.mem_maximalIdeal _).2 hy
  rw [GroundTheory.PAdicHodge.IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker] at h2
  exact h h2

theorem eq_of_pow_eq_self_of_thB_eq {l : ℕ} [Fact l.Prime] {q : ℕ} (hq : 2 ≤ q)
    {a b : Formalism.Per6.BdRp l} (ha : a ^ q = a) (hb : b ^ q = b) (hab : thB l a = thB l b) :
    a = b := by
  set S : Formalism.Per6.BdRp l := ∑ i ∈ Finset.range q, a ^ i * b ^ (q - 1 - i) with hS
  have hkey : (a - b) * (S - 1) = 0 := by
    have h1 : (a - b) * S = a ^ q - b ^ q := (Commute.all a b).mul_geom_sum₂ q
    rw [mul_sub, h1, ha, hb, mul_one, sub_self]
  have hθS : thB l S = (q : ℂ_[l]) * thB l a ^ (q - 1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum, Finset.sum_congr rfl (g := fun _ => thB l a ^ (q - 1))]
    · simp
    · intro i hi
      have hi' : i ≤ q - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.1 hi)
      rw [map_mul, map_pow, map_pow, ← hab, ← pow_add, Nat.add_sub_cancel' hi']
  have hζ : thB l a ^ q = thB l a := by rw [← map_pow, ha]
  have hne : thB l (S - 1) ≠ 0 := by
    rw [map_sub, map_one, hθS]
    by_cases h0 : thB l a = 0
    · rw [h0, zero_pow (by omega)]
      simp
    · have h1 : thB l a ^ (q - 1) = 1 := by
        have e : thB l a ^ (q - 1) * thB l a = 1 * thB l a := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega), hζ, one_mul]
        exact mul_right_cancel₀ h0 e
      rw [h1, mul_one, sub_ne_zero]
      exact_mod_cast (by omega : q ≠ 1)
  have hu := isUnit_BdRp_of_thB hne
  exact sub_eq_zero.1 ((hu.mul_left_eq_zero).1 hkey)

theorem tch_eq_rB_of_sh_eq : ∀ {l : ℕ} [Fact l.Prime] (q : ℕ), 2 ≤ q → l ∣ q → ∀ (x : Tl l) (y : Om l),
    x ^ q = x → y ^ q = y → sh x = omC y → tch l x = rB l y := by
  intro l _ q hq _ x y hx hy hxy
  refine eq_of_pow_eq_self_of_thB_eq hq ?_ ?_ ?_
  · rw [← tch_pow, hx]
  · rw [← map_pow, hy]
  · rw [thB_tch, thB_rB, hxy, omC_apply]

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerCharacterEqResidueLiftStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_character_eq_residue_lift : ∀ {l : ℕ} [Fact l.Prime] (q : ℕ), 2 ≤ q → l ∣ q → ∀ (x : Tl l) (y : Om l),
    x ^ q = x → y ^ q = y → sh x = omC y → tch l x = rB l y := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.tch_eq_rB_of_sh_eq | exact GlobalTheory.CompanionTheory.LTPer.Tilt.tch_eq_rB_of_sh_eq | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.tch_eq_rB_of_sh_eq <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGaloisExtensionOfEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGaloisExtensionOfEmbedding
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem exists_gal_extending_embedding : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l),
    ∃ g : GQ l, ∀ x : ↥K.1, g (x : Om l) = μ x := by
  intro l _ K μ
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits (F := ℚ_[l]) (E := Om l) (K := Om l)
    (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) (L := K.1) μ
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun x => ?_⟩
  exact DFunLike.congr_fun hφ x

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGaloisExtensionOfEmbeddingStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_extension_of_embedding : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l),
    ∃ g : GQ l, ∀ x : ↥K.1, g (x : Om l) = μ x := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.exists_gal_extending_embedding | exact GlobalTheory.CompanionTheory.LTPer.Tilt.exists_gal_extending_embedding | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.exists_gal_extending_embedding <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerResidueFieldFinitePower
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerResidueFieldFinitePower
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem resfield_of_irreducible : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π →
    (Ideal.span {π}).IsMaximal ∧ Finite (↥(OL K) ⧸ Ideal.span {π}) ∧ ∃ f : ℕ, 0 < f ∧ qOf π = l ^ f := by
  intro l _ K π hπ
  obtain ⟨⟨⟨hD, hV, -⟩, -⟩, hfin⟩ := GlobalTheory.LocalIntegers.good_integers l K
  have hlp : l.Prime := Fact.out
  have hinj : Function.Injective (algebraMap ℤ_[l] ↥(OL K)) := by
    intro a b hab
    have h1 : algebraMap ℤ_[l] ↥K.1 a = algebraMap ℤ_[l] ↥K.1 b := congrArg Subtype.val hab
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1 b] at h1
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] ↥K.1).injective h1)
  have hi : Algebra.IsIntegral ℤ_[l] ↥(OL K) := integralClosure.algebraIsIntegral
  have hf : FaithfulSMul ℤ_[l] ↥(OL K) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have hl : ¬ IsUnit ((l : ℕ) : ↥(OL K)) := by
    intro hu
    rw [← map_natCast (algebraMap ℤ_[l] ↥(OL K))] at hu
    letI : Algebra.IsIntegral ℤ_[l] ↥(OL K) := hi
    letI : FaithfulSMul ℤ_[l] ↥(OL K) := hf
    letI : IsLocalHom (algebraMap ℤ_[l] ↥(OL K)) :=
      Algebra.IsIntegral.isLocalHom ℤ_[l] ↥(OL K)
    exact PadicInt.irreducible_p.not_isUnit (isUnit_of_map_unit _ _ hu)
  have hdvd : π ∣ ((l : ℕ) : ↥(OL K)) := by
    have hm : ((l : ℕ) : ↥(OL K)) ∈ IsLocalRing.maximalIdeal ↥(OL K) := hl
    rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  have hle : Ideal.span {((l : ℕ) : ↥(OL K)) ^ 1} ≤ Ideal.span {π} := by
    rw [pow_one, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact hdvd
  have hmax : (Ideal.span {π}).IsMaximal := by
    rw [← hπ.maximalIdeal_eq]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have hfinQ : Finite (↥(OL K) ⧸ Ideal.span {π}) := by
    have := hfin 1
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)
  refine ⟨hmax, hfinQ, ?_⟩
  letI : Field (↥(OL K) ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  haveI : Fintype (↥(OL K) ⧸ Ideal.span {π}) := Fintype.ofFinite _
  have hz : ((l : ℕ) : ↥(OL K) ⧸ Ideal.span {π}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {π})), Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
    exact hdvd
  haveI : CharP (↥(OL K) ⧸ Ideal.span {π}) l := (CharP.charP_iff_prime_eq_zero hlp).2 hz
  obtain ⟨n, -, hn⟩ := FiniteField.card (↥(OL K) ⧸ Ideal.span {π}) l
  refine ⟨n, n.pos, ?_⟩
  rw [qOf, Nat.card_eq_fintype_card, hn]

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerResidueFieldFinitePowerStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_residue_field_finite_power : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π →
    (Ideal.span {π}).IsMaximal ∧ Finite (↥(OL K) ⧸ Ideal.span {π}) ∧ ∃ f : ℕ, 0 < f ∧ qOf π = l ^ f := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.resfield_of_irreducible | exact GlobalTheory.CompanionTheory.LTPer.Tilt.resfield_of_irreducible | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.resfield_of_irreducible <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerResidueCongruence
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerResidueCongruence
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

variable {l : ℕ} [Fact l.Prime]

theorem norm_pow_sub_pow_le {a b : ℂ_[l]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = a ^ n * (a - b) + (a ^ n - b ^ n) * b := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hb).trans ih

theorem norm_pow_prime_sub_le {a b : ℂ_[l]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) {s : ℝ}
    (hl : ‖(l : ℂ_[l])‖ ≤ s) (hs : ‖a - b‖ ≤ s) : ‖a ^ l - b ^ l‖ ≤ s * ‖a - b‖ := by
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hl
  have hbp : ∀ n : ℕ, ‖b ^ n‖ ≤ 1 := fun n => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hb
  have hap : ∀ n : ℕ, ‖a ^ n‖ ≤ 1 := fun n => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have e : a ^ l - b ^ l = (∑ i ∈ Finset.range l, a ^ i * b ^ (l - 1 - i)) * (a - b) :=
    (geom_sum₂_mul a b l).symm
  have e2 : (∑ i ∈ Finset.range l, a ^ i * b ^ (l - 1 - i))
      = (∑ i ∈ Finset.range l, (a ^ i * b ^ (l - 1 - i) - b ^ (l - 1))) + (l : ℂ_[l]) * b ^ (l - 1) := by
    simp [Finset.sum_sub_distrib]
  have h1 : ‖∑ i ∈ Finset.range l, (a ^ i * b ^ (l - 1 - i) - b ^ (l - 1))‖ ≤ s := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hs0 fun i hi => ?_
    have hi' : i ≤ l - 1 := by
      have := Finset.mem_range.1 hi
      omega
    have e3 : a ^ i * b ^ (l - 1 - i) - b ^ (l - 1) = (a ^ i - b ^ i) * b ^ (l - 1 - i) := by
      rw [sub_mul, ← pow_add, Nat.add_sub_cancel' hi']
    rw [e3, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hbp _)).trans
      ((norm_pow_sub_pow_le ha hb i).trans hs)
  have h2 : ‖(l : ℂ_[l]) * b ^ (l - 1)‖ ≤ s := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hbp _)).trans hl
  rw [e, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [e2]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

theorem norm_pow_prime_pow_sub_le {a b : ℂ_[l]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) {s : ℝ}
    (hs1 : s ≤ 1) (hl : ‖(l : ℂ_[l])‖ ≤ s) (hs : ‖a - b‖ ≤ s) (n : ℕ) :
    ‖a ^ l ^ n - b ^ l ^ n‖ ≤ s ^ n * ‖a - b‖ := by
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hl
  induction n with
  | zero => simp
  | succ n ih =>
    have ha' : ‖a ^ l ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
    have hb' : ‖b ^ l ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hb
    have hle : ‖a ^ l ^ n - b ^ l ^ n‖ ≤ s :=
      ih.trans ((mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs0 hs1)).trans hs)
    have h := norm_pow_prime_sub_le ha' hb' hl hle
    rw [← pow_mul, ← pow_mul, ← pow_succ] at h
    refine h.trans ?_
    rw [pow_succ, mul_comm (s ^ n) s, mul_assoc]
    exact mul_le_mul_of_nonneg_left ih hs0

theorem isClosed_range_finExt (K : FinExt l) :
    IsClosed (Set.range fun y : ↥K.1 => omC (l := l) (y : Om l)) := by
  haveI := K.2
  let L : ↥K.1 →ₗ[ℚ_[l]] ℂ_[l] :=
    (IsScalarTower.toAlgHom ℚ_[l] (Om l) ℂ_[l]).toLinearMap ∘ₗ K.1.val.toLinearMap
  have h := Submodule.closed_of_finiteDimensional (LinearMap.range L)
  have e : (Set.range fun y : ↥K.1 => omC (l := l) (y : Om l)) = (LinearMap.range L : Set ℂ_[l]) := by
    ext z
    rfl
  rw [e]
  exact h

theorem exists_int_of_norm_le (K : FinExt l) (y : ↥K.1) (hy : ‖(y : Om l)‖ ≤ 1) :
    ∃ c : ↥(OL K), (c : ↥K.1) = y :=
  ⟨(GlobalTheory.CompanionTheory.LTHodge.CharEx.intEquiv K).symm
    ⟨y, (GlobalTheory.CompanionTheory.LTHodge.CharEx.mem_integer_iff K y).2 hy⟩, rfl⟩

theorem sh_root_near_integer : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (f : ℕ), 0 < f → qOf π = l ^ f →
    ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖ → ‖oc K π‖ < 1 → π ≠ 0 → ∀ (x : Tl l) (c : ↥(OL K)), x ^ l ^ f = x →
    ‖sh x - oc K c‖ ≤ ‖oc K π‖ → ∃ c' : ↥(OL K), sh x = oc K (c + π * c') := by
  intro l _ K π f hf _ hl hπ1 hπ0 x c hx hc
  set s := ‖oc K π‖ with hsdef
  have hs0 : 0 ≤ s := norm_nonneg _
  have hζ1 : ‖sh x‖ ≤ 1 := norm_sh_le_one x
  have hc1 : ‖oc K c‖ ≤ 1 := norm_oc_le_one K c
  have hfix1 : sh x ^ l ^ f = sh x := by rw [← sh_pow, hx]
  have hfix : ∀ m : ℕ, sh x ^ (l ^ f) ^ m = sh x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_mul, ih, hfix1]
  have hdist : ‖oc K c - sh x‖ ≤ s := by rw [norm_sub_rev]; exact hc
  have hbound : ∀ m : ℕ, ‖oc K (c ^ (l ^ f) ^ m) - sh x‖ ≤ s ^ m := by
    intro m
    have h := norm_pow_prime_pow_sub_le hc1 hζ1 hπ1.le hl hdist (f * m)
    rw [pow_mul, hfix m, ← map_pow] at h
    refine h.trans ?_
    have h1 : s ^ (f * m) ≤ s ^ m :=
      pow_le_pow_of_le_one hs0 hπ1.le (Nat.le_mul_of_pos_left m hf)
    exact (mul_le_of_le_one_right (pow_nonneg hs0 _) (hdist.trans hπ1.le)).trans h1
  have hlim : Filter.Tendsto (fun m : ℕ => oc K (c ^ (l ^ f) ^ m)) Filter.atTop (nhds (sh x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) hbound
      (tendsto_pow_atTop_nhds_zero_of_lt_one hs0 hπ1)
  have hmem : sh x ∈ Set.range fun y : ↥K.1 => omC (l := l) (y : Om l) :=
    (isClosed_range_finExt K).mem_of_tendsto hlim
      (Filter.Eventually.of_forall fun m => ⟨((c ^ (l ^ f) ^ m : ↥(OL K)) : ↥K.1), rfl⟩)
  obtain ⟨y, hy⟩ := hmem
  have hy : omC (l := l) (y : Om l) = sh x := hy
  have hcK : oc K c = omC (l := l) ((c : ↥K.1) : Om l) := rfl
  have hπK : oc K π = omC (l := l) ((π : ↥K.1) : Om l) := rfl
  have hπ0' : (π : ↥K.1) ≠ 0 := fun h => hπ0 (Subtype.ext h)
  have hπ0'' : ((π : ↥K.1) : Om l) ≠ 0 := fun h => hπ0' (Subtype.ext h)
  have hnum : ‖((y - (c : ↥K.1) : ↥K.1) : Om l)‖ ≤ ‖((π : ↥K.1) : Om l)‖ := by
    have : ‖sh x - oc K c‖ = ‖((y - (c : ↥K.1) : ↥K.1) : Om l)‖ := by
      rw [← hy, hcK, ← map_sub, norm_omC]
      rfl
    rw [← this, ← norm_omC, ← hπK]
    exact hc
  have hq : ‖(((y - (c : ↥K.1)) / (π : ↥K.1) : ↥K.1) : Om l)‖ ≤ 1 := by
    have e : (((y - (c : ↥K.1)) / (π : ↥K.1) : ↥K.1) : Om l)
        = ((y - (c : ↥K.1) : ↥K.1) : Om l) / ((π : ↥K.1) : Om l) := rfl
    rw [e, norm_div]
    exact div_le_one_of_le₀ hnum (norm_nonneg _)
  obtain ⟨c', hc'⟩ := exists_int_of_norm_le K _ hq
  refine ⟨c', ?_⟩
  have hsum : ((c + π * c' : ↥(OL K)) : ↥K.1) = y := by
    have : ((c + π * c' : ↥(OL K)) : ↥K.1) = (c : ↥K.1) + (π : ↥K.1) * (c' : ↥K.1) := rfl
    rw [this, hc']
    field_simp
    ring
  rw [← hy]
  show _ = omC (l := l) (((c + π * c' : ↥(OL K)) : ↥K.1) : Om l)
  rw [hsum]

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerResidueCongruenceStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_residue_congruence : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (f : ℕ), 0 < f → qOf π = l ^ f →
    ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖ → ‖oc K π‖ < 1 → π ≠ 0 → ∀ (x : Tl l) (c : ↥(OL K)), x ^ l ^ f = x →
    ‖sh x - oc K c‖ ≤ ‖oc K π‖ → ∃ c' : ↥(OL K), sh x = oc K (c + π * c') := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.sh_root_near_integer | exact GlobalTheory.CompanionTheory.LTPer.Tilt.sh_root_near_integer | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.sh_root_near_integer <;> assumption)
end
end
end

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem frob_pow_read {l : ℕ} [Fact l.Prime] (N : ℕ) (a y : Tl l) (b : ℕ → Tl l) (D : ℕ) :
    (a - ∑ i ∈ Finset.range D, b i * y ^ i) ^ l ^ N =
      a ^ l ^ N - ∑ i ∈ Finset.range D, b i ^ l ^ N * (y ^ l ^ N) ^ i := by
  rw [sub_pow_char_pow, sum_pow_char_pow]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i]

theorem oc_eq {l : ℕ} [Fact l.Prime] (K : FinExt l) (c : ↥(OL K)) : oc K c = omC (((c : ↥K.1) : Om l)) := rfl

theorem sys_pow_iter {l : ℕ} [Fact l.Prime] {f : ℕ} {u : ℕ → Tl l} (h : ∀ n, u (n + 1) ^ l ^ f = u n)
    (n m : ℕ) : u (n + m) ^ l ^ (f * m) = u n := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : u (n + (m + 1)) ^ l ^ (f * (m + 1)) = (u (n + m + 1) ^ l ^ f) ^ l ^ (f * m) := by
      rw [← pow_mul, ← pow_add, ← add_assoc]
      congr 2
      ring
    rw [e, h, ih]

theorem fix_ringHom {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (f : ℕ) (hf : 0 < f)
    (hl : ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖) (h1 : ‖oc K π‖ < 1)
    (hfer : ∀ c : ↥(OL K), ‖oc K c ^ l ^ f - oc K c‖ ≤ ‖oc K π‖) :
    ∃ r₀ : ↥(OL K) →+* Tl l, (∀ c, r₀ c ^ l ^ f = r₀ c) ∧ ∀ c, ‖sh (r₀ c) - oc K c‖ ≤ ‖oc K π‖ := by
  have hex : ∀ c : ↥(OL K), ∃ y : Tl l, y ^ l ^ f = y ∧ ‖sh y - oc K c‖ ≤ ‖oc K π‖ := fun c =>
    GlobalTheory.T.teichmuller_fixed_point_approximation f _ hf hl h1 (oc K c) (norm_oc_le_one K c) (hfer c)
  choose F hF1 hF2 using hex
  have huniq : ∀ (x : Tl l) (A : ↥(OL K)), x ^ l ^ f = x → ‖sh x - oc K A‖ ≤ ‖oc K π‖ → F A = x := by
    intro x A hx hA
    apply fixed_unique hf (hF1 A) hx
    refine lt_of_le_of_lt (norm_sub_le_of_near hl ?_) h1
    have e : sh (F A) - sh x = (sh (F A) - oc K A) - (sh x - oc K A) := by ring
    rw [e]
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hF2 A) (by rw [norm_neg]; exact hA))
  refine ⟨{ toFun := F, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hF1, hF2⟩
  · exact huniq 1 1 (one_pow _) (by rw [map_one, sh_one, sub_self, norm_zero]; exact norm_nonneg _)
  · intro a b
    refine huniq _ _ (by rw [mul_pow, hF1, hF1]) ?_
    rw [map_mul]
    exact near_mul (norm_oc_le_one K b) (hF2 a) (hF2 b)
  · exact huniq 0 0 (zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))
      (by rw [map_zero, sh_zero, sub_self, norm_zero]; exact norm_nonneg _)
  · intro a b
    refine huniq _ _ (by rw [add_pow_char_pow, hF1, hF1]) ?_
    rw [map_add (f := _)]
    exact near_add hl (hF2 a) (hF2 b)

theorem tch_eq {l : ℕ} [Fact l.Prime] (f : ℕ) (hf : 0 < f) (x : Tl l) (hx : x ^ l ^ f = x) (y : Om l)
    (hy : sh x = omC y) : tch l x = rB l y := by
  have hq2 : 2 ≤ l ^ f := by
    have := Nat.pow_le_pow_right (Fact.out : l.Prime).pos hf
    have h2 := (Fact.out : l.Prime).two_le
    simp only [pow_one] at this
    omega
  have hyf : y ^ l ^ f = y := by
    apply omC.injective
    rw [map_pow, ← hy, ← sh_pow, hx]
  exact GlobalTheory.T.teichmuller_character_eq_residue_lift (l ^ f) hq2 (dvd_pow_self l hf.ne') x y hx hyf hy

theorem exp_twist {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (f : ℕ) (hf : 0 < f) (hqf : qOf π = l ^ f)
    (hl : ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖) (h1 : ‖oc K π‖ < 1) (hπ0 : π ≠ 0)
    (hmax : (Ideal.span {π}).IsMaximal) (hfin : Finite (↥(OL K) ⧸ Ideal.span {π}))
    (r₀ : ↥(OL K) →+* Tl l) (hr1 : ∀ c, r₀ c ^ l ^ f = r₀ c) (hr2 : ∀ c, ‖sh (r₀ c) - oc K c‖ ≤ ‖oc K π‖)
    (hrπ : r₀ π = 0) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) :
    ∃ i : ℕ, ∀ c, ∃ c' : ↥(OL K), sh (r₀ c ^ l ^ i) = omC (μ ((c + π * c' : ↥(OL K)) : ↥K.1)) := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_extension_of_embedding K μ
  haveI := hmax
  haveI := hfin
  letI : Field (↥(OL K) ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  have hker : ∀ a ∈ Ideal.span {π}, r₀ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, hrπ, mul_zero]
  let α : (↥(OL K) ⧸ Ideal.span {π}) →+* Tl l := Ideal.Quotient.lift _ r₀ hker
  obtain ⟨i, hi⟩ := GlobalTheory.T.finite_field_embeddings_differ_frobenius (l := l) (k := ↥(OL K) ⧸ Ideal.span {π}) (D := Tl l) α ((actT g).comp α)
  refine ⟨i, fun c => ?_⟩
  obtain ⟨c', hc'⟩ := GlobalTheory.T.teichmuller_residue_congruence K π f hf hqf hl h1 hπ0 (r₀ c) c (hr1 c) (hr2 c)
  refine ⟨c', ?_⟩
  have h : actT g (r₀ c) = r₀ c ^ l ^ i := hi (Ideal.Quotient.mk _ c)
  rw [← h, sh_actT, hc', oc_eq, galCp_omC, hg]

theorem tch_clause {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (f : ℕ) (hf : 0 < f)
    (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (r₀ : ↥(OL K) →+* Tl l) (hr1 : ∀ c, r₀ c ^ l ^ f = r₀ c) (i : ℕ)
    (hic : ∀ c, ∃ c' : ↥(OL K), sh (r₀ c ^ l ^ i) = omC (μ ((c + π * c' : ↥(OL K)) : ↥K.1))) :
    ∀ c, ∃ c', tch l (((iterateFrobenius (Tl l) l i).comp r₀) c) = oB K μ (c + π * c') := by
  intro c
  obtain ⟨c', hc'⟩ := hic c
  refine ⟨c', ?_⟩
  rw [RingHom.comp_apply, iterateFrobenius_def]
  have hfix : (r₀ c ^ l ^ i) ^ l ^ f = r₀ c ^ l ^ i := by
    rw [← pow_mul, mul_comm, pow_mul, hr1]
  rw [tch_eq f hf _ hfix _ hc']
  simp only [oB, RingHom.comp_apply]
  rfl

theorem gal_clause {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (g : GQ l) (r₀ : R →+* Tl l) (i : ℕ)
    (x : Tl l) (c : ℕ → R) (D : ℕ) (hd : x ^ D ∣ actT g x - ∑ j ∈ Finset.range D, r₀ (c j) * x ^ j) :
    (x ^ l ^ i) ^ D ∣ actT g (x ^ l ^ i) -
      ∑ j ∈ Finset.range D, ((iterateFrobenius (Tl l) l i).comp r₀) (c j) * (x ^ l ^ i) ^ j := by
  have h := pow_dvd_pow_of_dvd hd (l ^ i)
  rw [frob_pow_read] at h
  have e1 : (x ^ l ^ i) ^ D = (x ^ D) ^ l ^ i := by rw [← pow_mul, ← pow_mul, mul_comm]
  have e2 : actT g (x ^ l ^ i) = actT g x ^ l ^ i := map_pow _ _ _
  have e3 : ∀ j, ((iterateFrobenius (Tl l) l i).comp r₀) (c j) = r₀ (c j) ^ l ^ i := fun j => by
    rw [RingHom.comp_apply, iterateFrobenius_def]
  simp only [e1, e2, e3]
  exact h

end GlobalTheory.CompanionTheory.LTPer.Tilt

theorem GlobalTheory.CompanionTheory.LTPer.Tilt.tilt_period : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l,
    ∃ (r : ↥(OL K) →+* Tl l) (v : ℕ → Tl l),
      (∀ n, v (n + 1) ^ qOf π = v n) ∧ v 0 ≠ 0 ∧ ‖thB l (tch l (v 0))‖ < 1 ∧
      (∀ c, ∃ c', tch l (r c) = oB K μ (c + π * c')) ∧
      (∀ (g : GQ l) (hg : g ∈ GK K) (φ : PowerSeries ↥(OL K)), PowerSeries.constantCoeff φ = 0 →
        ((PowerSeries.coeff 1 φ : ↥(OL K)) : ↥K.1) = ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) →
        PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ →
        ∀ n D, v n ^ D ∣ actT g (v n) - ∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * v n ^ i) ∧
      (μ = K.1.val → ∀ n, ‖thB l (tch l (v n)) - ((z n : Om l) : ℂ_[l])‖ ≤ ‖(((π : ↥K.1) : Om l) : ℂ_[l])‖) := by
  intro l _ K χ π z hLT μ
  obtain ⟨hirr, hz0, hz1, hrec, hgal⟩ := hLT
  obtain ⟨hq2, hlq, hπl, hπ1, -⟩ := GlobalTheory.CompanionTheory.LTPer.uniformiser_facts K π hirr
  obtain ⟨hmax, hfin, f, hf, hqf⟩ := GlobalTheory.T.uniformizer_residue_field_finite_power K π hirr
  have hπ1' : ‖oc K π‖ < 1 := by rw [oc_apply]; exact hπ1
  have hl : ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖ := by
    obtain ⟨a, ha⟩ := hπl
    have e : (l : ℂ_[l]) = oc K π * oc K a := by rw [← map_mul, ← ha, map_natCast]
    rw [e, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_oc_le_one K a)
  have hπ0 : π ≠ 0 := hirr.ne_zero
  obtain ⟨hzlt, hzgt⟩ := GlobalTheory.T.lubin_tate_sequence_norm_bounds K χ π z ⟨hirr, hz0, hz1, hrec, hgal⟩ hq2 hπ1'
  have hrec' : ∀ n, z (n + 1) ^ l ^ f + ((π : ↥K.1) : Om l) * z (n + 1) = z n := by
    intro n
    have h := hrec n
    rwa [show Nat.card (↥(OL K) ⧸ Ideal.span {π}) = l ^ f from hqf] at h
  have hZ : ∀ n, ‖omC (z (n + 1)) ^ l ^ f - omC (z n)‖ ≤ ‖oc K π‖ := by
    intro n
    have e : omC (z (n + 1)) ^ l ^ f - omC (z n) = -(oc K π * omC (z (n + 1))) := by
      rw [← hrec' n, map_add (f := _), map_mul, map_pow, oc_eq]
      ring
    rw [e, norm_neg, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hzlt _).le
  obtain ⟨u, hu1, hu2⟩ := GlobalTheory.T.teichmuller_compatible_sequence_approximation f ‖oc K π‖ hf hl hπ1' (fun n => omC (z n)) (fun n => (hzlt n).le) hZ
  have hu0 : ∀ n, u n ≠ 0 := by
    have h2 : ∀ n, 2 ≤ n → u n ≠ 0 := by
      intro n hn h0
      have h := hu2 n
      rw [h0, sh_zero, zero_sub, norm_neg] at h
      exact absurd (hzgt n hn) (not_lt.2 h)
    intro n
    rw [← sys_pow_iter hu1 n 2]
    exact pow_ne_zero _ (h2 _ (by omega))
  have hfer : ∀ c : ↥(OL K), ‖oc K c ^ l ^ f - oc K c‖ ≤ ‖oc K π‖ := by
    intro c
    obtain ⟨a, ha⟩ := GlobalTheory.T.uniformizer_divides_frobenius_difference K π hmax hfin c
    rw [hqf] at ha
    rw [← map_pow, ← map_sub, ha, map_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_oc_le_one K a)
  obtain ⟨r₀, hr1, hr2⟩ := fix_ringHom K π f hf hl hπ1' hfer
  have hrπ : r₀ π = 0 := by
    apply fixed_unique hf (hr1 π) (zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))
    refine lt_of_le_of_lt (norm_sub_le_of_near hl ?_) hπ1'
    rw [sh_zero, sub_zero]
    have e : sh (r₀ π) = (sh (r₀ π) - oc K π) + oc K π := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hr2 π) le_rfl)
  have hexp : ∃ i : ℕ, (μ = K.1.val → i = 0) ∧
      ∀ c, ∃ c' : ↥(OL K), sh (r₀ c ^ l ^ i) = omC (μ ((c + π * c' : ↥(OL K)) : ↥K.1)) := by
    by_cases hμ : μ = K.1.val
    · refine ⟨0, fun _ => rfl, fun c => ?_⟩
      obtain ⟨c', hc'⟩ := GlobalTheory.T.teichmuller_residue_congruence K π f hf hqf hl hπ1' hπ0 (r₀ c) c (hr1 c) (hr2 c)
      refine ⟨c', ?_⟩
      rw [pow_zero, pow_one, hc', hμ]
      rfl
    · obtain ⟨i, hi⟩ := exp_twist K π f hf hqf hl hπ1' hπ0 hmax hfin r₀ hr1 hr2 hrπ μ
      exact ⟨i, fun h => absurd h hμ, hi⟩
  obtain ⟨i, hi0, hic⟩ := hexp
  refine ⟨(iterateFrobenius (Tl l) l i).comp r₀, fun n => u n ^ l ^ i, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    show (u (n + 1) ^ l ^ i) ^ qOf π = u n ^ l ^ i
    rw [hqf, ← pow_mul, mul_comm, pow_mul, hu1]
  · exact pow_ne_zero _ (hu0 0)
  · show ‖thB l (tch l (u 0 ^ l ^ i))‖ < 1
    rw [thB_tch, sh_pow, norm_pow]
    have h := hu2 0
    rw [hz0, map_zero, sub_zero] at h
    exact pow_lt_one₀ (norm_nonneg _) (h.trans_lt hπ1') (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  · exact tch_clause K π f hf μ r₀ hr1 i hic
  · intro g hg φ h0 h1 hcomm n D
    have hs := hgal ⟨g, hg⟩ φ h0 h1 hcomm
    have hd := GlobalTheory.T.lubin_tate_teichmuller_sequence_compatibility K π z f hf hl hπ1' hzlt hzgt u hu1 hu2 r₀ hr1 hr2 hu0 g
      (fun k => PowerSeries.coeff k φ) hs n D
    exact gal_clause g r₀ i (u n) (fun k => PowerSeries.coeff k φ) D hd
  · intro hμ n
    show ‖thB l (tch l (u n ^ l ^ i)) - _‖ ≤ _
    rw [hi0 hμ, pow_zero, pow_one, thB_tch, ← omC_apply, ← oc_apply]
    exact hu2 n
