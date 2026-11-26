module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.MemOfIsIntegralElem
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSeriesIdentityPrincipleComplexPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemThetaPointsOfClosureCosetConditionStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EvalTwistTxEqZeroOfAevalArcTx
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.BddArc

section
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C]

def AbsSumAt (u : C) (f : PowerSeries C) (c : C) : Prop :=
  (Summable fun n => ‖PowerSeries.coeff n f * u ^ n‖) ∧ ∑' n, PowerSeries.coeff n f * u ^ n = c

theorem AbsSumAt.add {u : C} {f g : PowerSeries C} {a b : C} (hf : AbsSumAt u f a) (hg : AbsSumAt u g b) :
    AbsSumAt u (f + g) (a + b) := by
  constructor
  · refine (hf.1.add hg.1).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    rw [map_add (f := _), add_mul]
    exact norm_add_le _ _
  · rw [← hf.2, ← hg.2, ← hf.1.of_norm.tsum_add hg.1.of_norm]
    simp only [map_add (f := _), add_mul]

private theorem absSumAt_algebraMap (u a : C) :
    _root_.GlobalTheory.BddArc.AbsSumAt u (algebraMap C (PowerSeries C) a) a := by
  have h : (fun n => PowerSeries.coeff n (algebraMap C (PowerSeries C) a) * u ^ n) =
      fun n => if n = 0 then a else 0 := by
    funext n
    rcases n with _ | n <;> simp [PowerSeries.coeff_C]
  refine ⟨?_, ?_⟩
  · refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    rw [congrFun h n, if_neg (by simpa using hn), norm_zero]
  · rw [h]
    simp

private theorem absSumAt_add {u : C} {f g : PowerSeries C} {a b : C}
    (hf : _root_.GlobalTheory.BddArc.AbsSumAt u f a) (hg : _root_.GlobalTheory.BddArc.AbsSumAt u g b) :
    _root_.GlobalTheory.BddArc.AbsSumAt u (f + g) (a + b) := by
  have h : ∀ n, PowerSeries.coeff n (f + g) * u ^ n =
      PowerSeries.coeff n f * u ^ n + PowerSeries.coeff n g * u ^ n := fun n => by
    rw [map_add (f := _), add_mul]
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (Summable.add hf.1 hg.1)
    rw [h]
    exact norm_add_le _ _
  · simp_rw [h]
    rw [(hf.1.of_norm).tsum_add hg.1.of_norm, hf.2, hg.2]

private theorem absSumAt_mul {u : C} {f g : PowerSeries C} {a b : C}
    (hf : _root_.GlobalTheory.BddArc.AbsSumAt u f a) (hg : _root_.GlobalTheory.BddArc.AbsSumAt u g b) :
    _root_.GlobalTheory.BddArc.AbsSumAt u (f * g) (a * b) := by
  have h : ∀ n, PowerSeries.coeff n (f * g) * u ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 f * u ^ kl.1) * (PowerSeries.coeff kl.2 g * u ^ kl.2) := fun n => by
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hkl, pow_add]
    ring
  refine ⟨?_, ?_⟩
  · exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hf.1 hg.1).congr fun n => by rw [h]
  · rw [tsum_congr h, ← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf.1 hg.1, hf.2, hg.2]

theorem _root_.GlobalTheory.BddArc.AbsSumAt.aeval {u : C} {ι : Type} {f : ι → PowerSeries C} {a : ι → C}
    (h : ∀ i, _root_.GlobalTheory.BddArc.AbsSumAt u (f i) (a i))
    (F : MvPolynomial ι C) :
    _root_.GlobalTheory.BddArc.AbsSumAt u (MvPolynomial.aeval f F) (MvPolynomial.eval a F) := by
  induction F using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.aeval_C, MvPolynomial.eval_C]
    exact absSumAt_algebraMap u c
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _)]
    exact absSumAt_add hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X]
    exact absSumAt_mul hp (h i)

end

end GlobalTheory.BddArc

private theorem finite_setOf_bilin_self_le_of_posDef {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (B : LinearMap.BilinForm ℤ X) (hsymm : ∀ y z, B y z = B z y) (hpos : ∀ y, y ≠ 0 → 0 < B y y) (L : ℤ) :
    {y | B y y ≤ L}.Finite := by
  classical
  set b := Module.Free.chooseBasis ℤ X with hb
  let M : Matrix (Module.Free.ChooseBasisIndex ℤ X) (Module.Free.ChooseBasisIndex ℤ X) ℚ :=
    Matrix.of fun i j => (B (b i) (b j) : ℚ)
  let Bq := Matrix.toBilin' M
  let φ : X → Module.Free.ChooseBasisIndex ℤ X → ℚ := fun y i => (b.repr y i : ℚ)
  have hφ : ∀ y z, ((B y z : ℤ) : ℚ) = Bq (φ y) (φ z) := by
    intro y z
    rw [Matrix.toBilin'_apply]
    conv_lhs => rw [← b.sum_repr y, ← b.sum_repr z]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, Int.cast_sum,
      Int.cast_mul, Finset.mul_sum, M, φ, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hBsymm : LinearMap.IsSymm Bq := by
    refine LinearMap.isSymm_iff_eq_flip.2 (LinearMap.ext₂ fun x y => ?_)
    rw [LinearMap.flip_apply, Matrix.toBilin'_apply, Matrix.toBilin'_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [M, Matrix.of_apply, hsymm (b i) (b j)]
    ring
  have hqpos : ∀ v, v ≠ 0 → 0 < Bq v v := by
    intro v hv
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) Finset.univ v
    choose n hn using fun i => hd i (Finset.mem_univ i)
    have hd0 : ((d : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d
    set y : X := b.equivFun.symm n
    have hy : φ y = ((d : ℤ) : ℚ) • v := by
      funext i
      have := hn i
      simp only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul] at this
      have hr : b.repr y i = n i := by rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
      simp only [φ, Pi.smul_apply, smul_eq_mul, hr]
      exact this
    have hy0 : y ≠ 0 := by
      intro h
      apply hv
      have h2 : ((d : ℤ) : ℚ) • v = 0 := by rw [← hy, h]; funext i; simp [φ]
      exact (smul_eq_zero.1 h2).resolve_left hd0
    have h1 := hpos y hy0
    have h2 : (0 : ℚ) < Bq (φ y) (φ y) := by rw [← hφ]; exact_mod_cast h1
    rw [hy] at h2
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
    have h3 : 0 < ((d : ℤ) : ℚ) * ((d : ℤ) : ℚ) := mul_self_pos.2 hd0
    nlinarith
  haveI : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  obtain ⟨w, hw⟩ := LinearMap.BilinForm.exists_orthogonal_basis hBsymm
  have hexp : ∀ v, Bq v v = ∑ k, (w.repr v k) ^ 2 * Bq (w k) (w k) := by
    intro v
    conv_lhs => rw [← w.sum_repr v]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k]
    · ring
    · intro l _ hlk
      rw [hw hlk]
      ring
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hdpos : ∀ k, 0 < Bq (w k) (w k) := fun k => hqpos _ (w.ne_zero k)
  set A : ℚ := ∑ k, max 1 ((L : ℚ) / Bq (w k) (w k)) with hAdef
  set T : ℚ := ∑ i, A * ∑ k, |w k i| with hTdef
  have hA : 0 ≤ A := Finset.sum_nonneg fun k _ => le_trans zero_le_one (le_max_left _ _)
  have hcoord : ∀ v, Bq v v ≤ L → ∀ i, |v i| ≤ T := by
    intro v hv i
    have hc : ∀ k, |w.repr v k| ≤ A := by
      intro k
      have h1 : (w.repr v k) ^ 2 * Bq (w k) (w k) ≤ L := by
        rw [hexp] at hv
        refine le_trans ?_ hv
        exact Finset.single_le_sum (f := fun k => (w.repr v k) ^ 2 * Bq (w k) (w k))
          (fun k _ => mul_nonneg (sq_nonneg _) (hdpos k).le) (Finset.mem_univ k)
      have h2 : |w.repr v k| ≤ max 1 ((L : ℚ) / Bq (w k) (w k)) := by
        rcases le_or_gt (|w.repr v k|) 1 with h | h
        · exact h.trans (le_max_left _ _)
        · refine le_trans ?_ (le_max_right _ _)
          rw [le_div_iff₀ (hdpos k)]
          have h3 : |w.repr v k| ≤ (w.repr v k) ^ 2 := by rw [← sq_abs]; nlinarith
          nlinarith [hdpos k]
      refine h2.trans ?_
      exact Finset.single_le_sum (f := fun k => max 1 ((L : ℚ) / Bq (w k) (w k)))
        (fun k _ => le_trans zero_le_one (le_max_left _ _)) (Finset.mem_univ k)
    have hvi : v i = ∑ k, w.repr v k * w k i := by
      conv_lhs => rw [← w.sum_repr v]
      simp [Finset.sum_apply]
    calc |v i| ≤ ∑ k, |w.repr v k * w k i| := by rw [hvi]; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, A * |w k i| := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hc k) (abs_nonneg _)
      _ = A * ∑ k, |w k i| := (Finset.mul_sum _ _ _).symm
      _ ≤ T := Finset.single_le_sum (f := fun i => A * ∑ k, |w k i|)
          (fun i _ => mul_nonneg hA (Finset.sum_nonneg fun k _ => abs_nonneg _)) (Finset.mem_univ i)
  let ψ : X → Module.Free.ChooseBasisIndex ℤ X → ℤ := fun y i => b.repr y i
  have hψ : Function.Injective ψ := by
    intro y z h
    apply b.repr.injective
    ext i
    exact congrFun h i
  refine ((Set.finite_Icc (fun _ => -⌈T⌉) (fun _ => ⌈T⌉)).preimage hψ.injOn).subset ?_
  intro y hy
  have hy' : Bq (φ y) (φ y) ≤ L := by rw [← hφ]; exact_mod_cast hy
  have h := hcoord _ hy'
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h4 := (abs_le.1 ((h i).trans (Int.le_ceil T))).1
    show -⌈T⌉ ≤ b.repr y i
    simp only [φ] at h4
    exact_mod_cast h4
  · have h4 := (abs_le.1 ((h i).trans (Int.le_ceil T))).2
    show b.repr y i ≤ ⌈T⌉
    simp only [φ] at h4
    exact_mod_cast h4

private theorem injective_add_nsmul_of_ne_zero {X : Type} [AddCommGroup X] [Module.Free ℤ X] (a : X) {m : ℕ}
    (hm : m ≠ 0) : Function.Injective (fun χ : X => a + m • χ) := by
  intro x y h
  have h' : m • x = m • y := add_left_cancel h
  apply (Module.Free.chooseBasis ℤ X).repr.injective
  ext i
  have := congrArg (fun z => (Module.Free.chooseBasis ℤ X).repr z i) h'
  simp only [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at this
  exact mul_left_cancel₀ (by exact_mod_cast hm) this

private theorem tsum_subtype_eq_finsum_mem_of_finite {X M : Type} [AddCommMonoid M] [TopologicalSpace M]
    [T2Space M] (S : Set X) (hS : S.Finite) (g : X → M) : ∑' b : S, g b = ∑ᶠ x ∈ S, g x := by
  have h := Finset.tsum_subtype' hS.toFinset g
  rw [hS.coe_toFinset] at h
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, h]

private theorem absSumAt_arcTx_twist_tx {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] (N : _root_.GlobalTheory.Ex.NumD C) {k : ℕ}
    (β : N.Form k) (m : ℕ) (hm : m ^ 2 ∣ k) (hodd : Odd m)
    (p : N.QT (m ^ 2))
    (hbd : ∀ χ, ‖N.txT m p χ‖ ≤ 1) (u : Cˣ) (hu : ‖(u : C)‖ < 1) :
    _root_.GlobalTheory.BddArc.AbsSumAt (u : C)
      (N.arcTx β.be m p)
      ((N.twist β u).tx m (N.twQ β u hm p)) := by
  classical
  set a : N.X := Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1 with ha
  set q : N.X → ℤ := fun χ =>
    β.be (a + m • χ) (a + m • χ) / (2 * (m : ℤ) ^ 2) with hq
  have hm0 : m ≠ 0 := hodd.pos.ne'
  have hden : (0 : ℤ) < 2 * (m : ℤ) ^ 2 := by positivity
  have hq0 : ∀ χ, 0 ≤ q χ := by
    intro χ
    refine Int.ediv_nonneg ?_ hden.le
    by_cases h : a + m • χ = 0
    · rw [h]; simp
    · exact (β.pos _ h).le
  have hfin : ∀ K : ℤ, {χ | q χ ≤ K}.Finite := by
    intro K
    refine ((finite_setOf_bilin_self_le_of_posDef β.be β.symm β.pos
      ((K + 1) * (2 * (m : ℤ) ^ 2))).preimage (injective_add_nsmul_of_ne_zero a hm0).injOn).subset ?_
    intro χ hχ
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hχ ⊢
    have h1 := Int.lt_mul_ediv_self_add
      (x := β.be (a + m • χ) (a + m • χ)) hden
    have h2 : 2 * (m : ℤ) ^ 2 * (β.be (a + m • χ) (a + m • χ) / (2 * (m : ℤ) ^ 2))
        ≤ 2 * (m : ℤ) ^ 2 * K := mul_le_mul_of_nonneg_left hχ hden.le
    linarith
  have hfinS : ∀ n : ℕ, {χ | q χ = n}.Finite := fun n =>
    (hfin n).subset fun χ hχ => le_of_eq hχ
  set Q : N.X → ℕ := fun χ => (q χ).toNat with hQdef
  have hQ : ∀ χ, ((Q χ : ℕ) : ℤ) = q χ := fun χ => Int.toNat_of_nonneg (hq0 χ)
  have hpow : ∀ χ, ((u ^ q χ : Cˣ) : C) = (u : C) ^ Q χ := by
    intro χ
    conv_lhs => rw [← hQ χ]
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  set f : N.X → C := fun χ => (u : C) ^ Q χ * N.txT m p χ with hf
  have htw : (N.twist β u).tx m (N.twQ β u hm p)
      = ∑' χ, f χ := by
    unfold _root_.GlobalTheory.Ex.NumD.tx
    refine tsum_congr fun χ => ?_
    rw [N.twist_txT β u m hm hodd p χ]
    exact congrArg (· * N.txT m p χ) (hpow χ)
  have hcoeff' : ∀ n : ℕ, PowerSeries.coeff n (N.arcTx β.be m p)
      = ∑ᶠ χ ∈ {χ | q χ = n}, N.txT m p χ := by
    intro n
    unfold _root_.GlobalTheory.Ex.NumD.arcTx
    rw [PowerSeries.coeff_mk]
    rfl
  have hcn : ∀ n : ℕ,
      ‖PowerSeries.coeff n (N.arcTx β.be m p)‖ ≤ 1 := by
    intro n
    rw [hcoeff', finsum_mem_eq_finite_toFinset_sum _ (hfinS n)]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun χ _ => hbd χ
  have hnorm : ∀ χ, ‖f χ‖ ≤ ‖(u : C)‖ ^ Q χ := fun χ => by
    rw [hf, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (hbd χ)
  have hQtend : Filter.Tendsto Q Filter.cofinite Filter.atTop := by
    refine Filter.tendsto_atTop.2 fun K => Filter.eventually_cofinite.2 ?_
    refine (hfin K).subset fun χ hχ => ?_
    simp only [Set.mem_setOf_eq, not_le] at hχ ⊢
    have := hQ χ
    omega
  have hsum : Summable f := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun χ => norm_nonneg _) hnorm
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hu).comp hQtend)
  have hcoeff : ∀ n : ℕ, ∑' b : ↑(Q ⁻¹' {n}), f b =
      PowerSeries.coeff n (N.arcTx β.be m p) * (u : C) ^ n := by
    intro n
    have hset : Q ⁻¹' {n} = {χ | q χ = n} := by
      ext χ
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      have := hQ χ
      omega
    have hterm : ∀ b : ↑(Q ⁻¹' {n}), f b = (u : C) ^ n * N.txT m p b := by
      intro b
      have hb : Q b = n := b.2
      rw [hf]
      simp only [hb]
    rw [tsum_congr hterm, tsum_mul_left, hset,
      tsum_subtype_eq_finsum_mem_of_finite _ (hfinS n), hcoeff', mul_comm]
  have hfib := hsum.hasSum.tsum_fiberwise Q
  rw [show (fun n => ∑' b : ↑(Q ⁻¹' {n}), f b) = fun n =>
      PowerSeries.coeff n (N.arcTx β.be m p) * (u : C) ^ n
      from funext hcoeff] at hfib
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (summable_geometric_of_lt_one (norm_nonneg _) hu)
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hcn n)
  · rw [htw]
    exact hfib.tsum_eq

theorem _root_.GlobalTheory.eval_twist_tx_eq_zero_of_aeval_arcTx : ∀ (C : Type) [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] (N : _root_.GlobalTheory.Ex.NumD C) (k : ℕ)
    (β : N.Form k) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m →
    ∀ (ι : Type) (p : ι → N.QT (m ^ 2)),
    (∀ i χ, ‖N.txT m (p i) χ‖ ≤ 1) → ∀ (F : MvPolynomial ι C),
    MvPolynomial.aeval (fun i => N.arcTx β.be m (p i)) F = 0 →
    ∀ u : Cˣ, ‖(u : C)‖ < 1 →
    MvPolynomial.eval (fun i => (N.twist β u).tx m
      (N.twQ β u hm (p i))) F = 0 := by
  intro C _ _ _ N k β m hm hodd ι p hbd F hF u hu
  have h := _root_.GlobalTheory.BddArc.AbsSumAt.aeval (u := (u : C))
    (fun i => absSumAt_arcTx_twist_tx N β m hm hodd (p i) (hbd i) u hu) F
  rw [hF] at h
  rw [← h.2]
  simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsObjectWithThetaPointOfDegenerationSeries
namespace GlobalTheory.Ex.OneLevel
section Arith
open Polynomial

theorem dvd_pow_sub {z : ℂ} {d k : ℕ} (hd : d.Prime) (hz : z ^ d ^ k = z) (y : Algebra.adjoin ℤ {z}) :
    (d : Algebra.adjoin ℤ {z}) ∣ y ^ d ^ k - y := by
  obtain ⟨y, hy⟩ := y
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl : x = z := hx
    exact ⟨0, Subtype.ext (by simp [hz])⟩
  | algebraMap r =>
    haveI := Fact.mk hd
    have h : (d : ℤ) ∣ r ^ d ^ k - r := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ZMod.pow_card_pow, sub_self]
    have := map_dvd (algebraMap ℤ (Algebra.adjoin ℤ {z})) h
    rwa [map_natCast, map_sub, map_pow] at this
  | add x y hx hy ihx ihy =>
    change _ ∣ ((⟨x, hx⟩ + ⟨y, hy⟩ : Algebra.adjoin ℤ {z})) ^ _ - (⟨x, hx⟩ + ⟨y, hy⟩)
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hd (⟨x, hx⟩ : Algebra.adjoin ℤ {z}) ⟨y, hy⟩ k
    rw [hr]
    generalize (⟨x, hx⟩ : Algebra.adjoin ℤ {z}) = a at *
    generalize (⟨y, hy⟩ : Algebra.adjoin ℤ {z}) = b at *
    obtain ⟨s, hs⟩ := ihx
    obtain ⟨t, ht⟩ := ihy
    exact ⟨s + t + a * b * r, by linear_combination hs + ht⟩
  | mul x y hx hy ihx ihy =>
    change _ ∣ ((⟨x, hx⟩ * ⟨y, hy⟩ : Algebra.adjoin ℤ {z})) ^ _ - (⟨x, hx⟩ * ⟨y, hy⟩)
    generalize (⟨x, hx⟩ : Algebra.adjoin ℤ {z}) = a at *
    generalize (⟨y, hy⟩ : Algebra.adjoin ℤ {z}) = b at *
    obtain ⟨s, hs⟩ := ihx
    obtain ⟨t, ht⟩ := ihy
    exact ⟨s * b ^ d ^ k + a * t, by rw [mul_pow]; linear_combination b ^ d ^ k * hs + a * ht⟩

theorem dvd_of_dvd_sq {z : ℂ} {d N : ℕ} (hd : d.Prime) (hN : 0 < N) (hdN : ¬ d ∣ N) (hz : z ^ N = 1)
    (y : Algebra.adjoin ℤ {z}) (h : (d : Algebra.adjoin ℤ {z}) ∣ y ^ 2) : (d : Algebra.adjoin ℤ {z}) ∣ y := by
  have hc : d.Coprime N := (Nat.Prime.coprime_iff_not_dvd hd).2 hdN
  have h1 : z ^ d ^ N.totient = z := by
    have := pow_eq_pow_of_modEq (Nat.ModEq.pow_totient hc) hz
    rwa [pow_one] at this
  have h2 : 2 ≤ d ^ N.totient := hd.two_le.trans (Nat.le_self_pow (Nat.totient_pos.2 hN).ne' d)
  have h3 := dvd_sub (h.trans (pow_dvd_pow y h2)) (dvd_pow_sub hd h1 y)
  rwa [sub_sub_cancel] at h3

theorem eq_zero_of_sq {z : ℂ} {d N : ℕ} (hd : d.Prime) (hN : 0 < N) (hdN : ¬ d ∣ N) (hz : z ^ N = 1)
    (B : Algebra.adjoin ℤ {z}) : ∀ A : Algebra.adjoin ℤ {z}, A ^ 2 = -d * B ^ 2 → B = 0 := by
  have hi : IsIntegral ℤ z := IsIntegral.of_pow hN (hz ▸ isIntegral_one)
  haveI : Module.Finite ℤ (Algebra.adjoin ℤ {z}) := Algebra.finite_adjoin_simple_of_isIntegral hi
  haveI : IsNoetherianRing (Algebra.adjoin ℤ {z}) := Algebra.FiniteType.isNoetherianRing ℤ _
  have hd0 : (d : Algebra.adjoin ℤ {z}) ≠ 0 := Nat.cast_ne_zero.2 hd.ne_zero
  have hu : ¬ IsUnit (d : Algebra.adjoin ℤ {z}) := fun hu => by
    rw [← map_natCast (algebraMap ℤ (Algebra.adjoin ℤ {z}))] at hu
    exact (Nat.prime_iff_prime_int.1 hd).not_unit (IsUnit.of_map _ _ hu)
  induction B using (wellFounded_dvdNotUnit (α := Algebra.adjoin ℤ {z})).induction with
  | _ B ih =>
    intro A hA
    obtain ⟨A', rfl⟩ := dvd_of_dvd_sq hd hN hdN hz A ⟨-B ^ 2, by rw [hA]; ring⟩
    have h1 : B ^ 2 = d * -A' ^ 2 := mul_left_cancel₀ hd0 (by linear_combination hA)
    obtain ⟨B', rfl⟩ := dvd_of_dvd_sq hd hN hdN hz B ⟨_, h1⟩
    by_contra h0
    have hB' : B' ≠ 0 := right_ne_zero_of_mul h0
    exact hB' (ih B' ⟨hB', d, hu, mul_comm _ _⟩ A' (mul_left_cancel₀ hd0 (by linear_combination h1)))

theorem exists_linear (d : ℕ) (c : MvPolynomial (Fin 2) ℤ) : ∃ a b : ℤ[X], ∀ (K : Type) [CommRing K] (ζ ρ : K),
    ρ ^ 2 = -(d : K) → cf ζ ρ c = aeval ζ a + ρ * aeval ζ b := by
  induction c using MvPolynomial.induction_on with
  | C r => exact ⟨C r, 0, fun K _ ζ ρ _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨a, b, h⟩ := hp
    obtain ⟨a', b', h'⟩ := hq
    exact ⟨a + a', b + b', fun K _ ζ ρ e => by rw [map_add (f := _), h K ζ ρ e, h' K ζ ρ e, map_add (f := _), map_add (f := _)]; ring⟩
  | mul_X p i hp =>
    obtain ⟨a, b, h⟩ := hp
    fin_cases i
    · exact ⟨a * X, b * X, fun K _ ζ ρ e => by rw [map_mul, h K ζ ρ e]; simp; ring⟩
    · exact ⟨-d * b, a, fun K _ ζ ρ e => by
        rw [map_mul, h K ζ ρ e]; simp; linear_combination aeval ζ b * e⟩

theorem compat_of_not_dvd {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {N : ℕ} (hN : 0 < N) (hdN : ¬ H.d ∣ N) {K : Type} [Field K] {ζ ρ : K}
    (hζ : IsPrimitiveRoot ζ N) (hρ : ρ ^ 2 = -(H.d : K)) : Compat H N ζ ρ := by
  intro c hc
  obtain ⟨a, b, h⟩ := exists_linear H.d c
  have hz : IsPrimitiveRoot (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta N) N := Complex.isPrimitiveRoot_exp N hN.ne'
  generalize ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta N = z at hc hz
  rw [h ℂ _ _ H.sqrt_neg_disc_sq] at hc
  have hb : aeval z b = 0 := congrArg Subtype.val (eq_zero_of_sq H.d_prime hN hdN hz.pow_eq_one
    ⟨aeval z b, aeval_mem_adjoin_singleton _ _⟩ ⟨aeval z a, aeval_mem_adjoin_singleton _ _⟩ (Subtype.ext (by
      have := H.sqrt_neg_disc_sq
      push_cast
      linear_combination (aeval z a - H.rt0 * aeval z b) * hc + aeval z b ^ 2 * this)))
  have ha : aeval z a = 0 := by rwa [hb, mul_zero, add_zero] at hc
  have key : ∀ p : ℤ[X], aeval z p = 0 → aeval ζ p = 0 := fun p hp => by
    have h1 := minpoly.isIntegrallyClosed_dvd (hz.isIntegral hN) hp
    rw [← cyclotomic_eq_minpoly hz hN] at h1
    refine aeval_eq_zero_of_dvd_aeval_eq_zero h1 ?_
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hN
  rw [h K _ _ hρ, key a ha, key b hb, mul_zero, add_zero]
end Arith

def scaleForm {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (j : ℕ) (hj : 0 < j) : N.Form j where
  be := (j : ℤ) • β.be
  symm y z := congrArg ((j : ℤ) * ·) (β.symm y z)
  pos y hy := mul_pos (Int.natCast_pos.2 hj) (β.pos y hy)
  dvd y z := by
    change _ ∣ (j : ℤ) * β.be y z
    rw [mul_comm 2]
    exact mul_dvd_mul_left _ ((Dvd.intro _ rfl).trans (β.dvd y z))

theorem tx_congr {O : Type} [CommRing O] [TopologicalSpace O] (N : NumD O) (ψ ψ' : N.X → Oˣ) (e b e' b') (h : ψ = ψ')
    (m : ℕ) (p : ({ N with ψ := ψ, even := e, bimult := b } : NumD O).QT (m ^ 2))
    (p' : ({ N with ψ := ψ', even := e', bimult := b' } : NumD O).QT (m ^ 2))
    (h1 : p.1.1 = p'.1.1) (h2 : p.1.2.b = p'.1.2.b) (h3 : p.1.2.s = p'.1.2.s) :
    NumD.tx _ m p = NumD.tx _ m p' := by
  subst h
  rw [show p = p' from Subtype.ext (Prod.ext h1 (NumD.Gt.ext h2 h3))]

theorem tx_scale {O : Type} [CommRing O] [TopologicalSpace O] {N : NumD O} {k : ℕ} (β : N.Form k) (m : ℕ)
    (hm : 0 < m ^ 2) (u r : Oˣ) (hr : r ^ m ^ 2 = u) (q : N.QT (m ^ 2)) (p : (N.twist β u).QT (m ^ 2))
    (h : TwRel β u r q p) :
    (N.twist β u).tx m p =
      (N.twist (scaleForm β _ hm) r).tx m (N.twQ (scaleForm β _ hm) r dvd_rfl q) := by
  refine tx_congr N _ _ _ _ _ _ (funext fun χ => ?_) m _ _ h.1 h.2.1 (funext fun χ => (h.2.2 χ).trans ?_)
  · change _ = _ * r ^ (((m ^ 2 : ℕ) : ℤ) * β.be χ χ / 2)
    rw [Int.mul_ediv_assoc _ ((Dvd.intro _ rfl).trans (β.dvd χ χ)), zpow_mul, zpow_natCast, hr]
  · change _ = q.1.2.s χ * r ^ (((m ^ 2 : ℕ) : ℤ) * β.be q.1.1.toAdd χ / ((m ^ 2 : ℕ) : ℤ))
    rw [Int.mul_ediv_cancel_left _ (Int.natCast_pos.2 hm).ne']

theorem eval_mul_of_isHomogeneous {ι C : Type} [CommRing C] {G : MvPolynomial ι C} {d : ℕ} (hG : G.IsHomogeneous d)
    (s : C) (v : ι → C) : MvPolynomial.eval (fun i => s * v i) G = s ^ d * MvPolynomial.eval v G := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have h := hG (MvPolynomial.mem_support_iff.1 he)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← h, Finsupp.weight_apply]
  simp only [Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one]
  ring
end GlobalTheory.Ex.OneLevel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.OneLevel

theorem exists_full_theta : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → ∀ (S : Ser a K (algebraMap _ K)) (n j : ℕ), n.Prime → Odd n → IsUnit (n : O') → ¬ n ∣ H.d → 2 ≤ j → ∃ o : Full D K, o.ρ = S.A.ρ ∧ o.I.ζ ((n ^ j) ^ 2) = S.A.I.ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (S.v (n ^ j)) := by
  intro h1 h2 h3 h4 h5 h6 h7 E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb K _ _ _ _ _ _ _ S n j hn ho hu hd hj
  haveI : CharZero K := S.A.arc.charZero
  have hm : Odd (n ^ j) := ho.pow
  have hm2 : 0 < (n ^ j) ^ 2 := pow_pos hm.pos 2
  have hdN : ¬ H.d ∣ (n ^ j) ^ 2 := fun h => hd (by
    rw [(Nat.prime_dvd_prime_iff_eq H.d_prime hn).1 (H.d_prime.dvd_of_dvd_pow (H.d_prime.dvd_of_dvd_pow h))])
  obtain ⟨o, e1, e2, e3⟩ := GlobalTheory.T.mem_thetaPoints_of_closure_coset_condition h1 h2 h3 h4 h5 h6 h7 E H D l Xo c W₀ Y K n j S.A.ρ
    (S.A.I.ζ ((n ^ j) ^ 2)) (S.v (n ^ j)) hn ho hj
    (compat_of_not_dvd H hm2 hdN (IsPrimitiveRoot.coe_units_iff.2 (S.A.I.ζ_prim _ hm2)) S.A.ρ_sq)
    (fun G hG => by_contra fun hne => S.base.not_allC_false fun C _ _ _ _ _ gam u c1 c2 c3 c4 => hne (by
      obtain ⟨A', r', i1, ⟨_, o1, o2, -⟩, i3, i4⟩ := S.val C gam u c1 c2 c3 c4
      haveI : CharZero C := A'.arc.charZero
      have hr : r' ((n ^ j) ^ 2) ^ (n ^ j) ^ 2 = u := Units.ext (by
        rw [Units.val_pow_eq_pow_val, i3, ← map_pow, ← Units.val_pow_eq_pow_val, S.roots.pow hm2, S.r_one, c3]; rfl)
      have hr1 : ‖(r' ((n ^ j) ^ 2) : C)‖ < 1 := by
        rw [← hr, Units.val_pow_eq_pow_val, norm_pow] at c4
        exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hm2.ne').1 c4
      choose p hp using fun x => (existsUnique_twRel A'.be u _ hr (A'.q _ x)).exists
      obtain ⟨⟨s, hs⟩, -⟩ := i4 _ hm p hp
      have hbal : A'.arc.Bal (scaleForm A'.be _ hm2) := fun x y z => by
        refine congrArg ((((n ^ j) ^ 2 : ℕ) : ℤ) * ·) ((A'.be_eq _ _).trans (Eq.trans ?_ (A'.be_eq _ _).symm))
        refine (congrArg (a.be · _) (A'.ν.eX.apply_symm_apply _)).trans ((a.be_adj _ _ _).trans ?_)
        exact congrArg (a.be _ ·) (A'.ν.eX.apply_symm_apply _).symm
      have k1 := GlobalTheory.T.theta_series_identity_principle_complex_points h1 h2 h3 h4 h5 h6 h7 E H D O' C A'.arc _ (scaleForm A'.be _ hm2) hbal _ dvd_rfl hm
        (compat_of_not_dvd H hm2 hdN (IsPrimitiveRoot.coe_units_iff.2 (A'.I.ζ_prim _ hm2)) A'.ρ_sq) G hG
      have hC : CExt O' ⊥ C := ⟨fun x => by rw [c1]; exact c2 _, fun x hx => by
        rw [(Submodule.mem_bot _).1 hx, map_zero, map_zero, norm_zero]; exact one_pos⟩
      have k2 := GlobalTheory.eval_twist_tx_eq_zero_of_aeval_arcTx C A'.N _ (scaleForm A'.be _ hm2) _ dvd_rfl hm D.La (A'.q _)
        (fun x => (GlobalTheory.Ex.UnitNorm.norms_of_arc_input E H D l Xo c W₀ Y O' b ϖ a hb C hC A' i1).2.1 _ hm _) _ k1 _ hr1
      obtain ⟨d, hGd⟩ := hG.2.1
      apply gam.injective
      have ec : gam.comp (cf (S.A.I.ζ ((n ^ j) ^ 2) : K) S.A.ρ) = cf (A'.I.ζ ((n ^ j) ^ 2) : C) A'.ρ := by
        refine MvPolynomial.ringHom_ext (fun x => by simp) fun i => ?_
        fin_cases i
        · simpa [Lift.arc] using o2 _ hm2
        · simpa [Lift.arc] using o1
      rw [map_zero, MvPolynomial.eval₂_comp_left, ec, MvPolynomial.eval₂_eq_eval_map]
      have ev : gam ∘ S.v (n ^ j) = fun x => (s : C) * (A'.N.twist (scaleForm A'.be _ hm2) (r' ((n ^ j) ^ 2))).tx (n ^ j)
          (A'.N.twQ (scaleForm A'.be _ hm2) (r' ((n ^ j) ^ 2)) dvd_rfl (A'.q _ x)) := funext fun x =>
        (hs x).trans (congrArg _ (tx_scale A'.be _ hm2 u _ hr _ _ (hp x)))
      rw [ev, eval_mul_of_isHomogeneous (hGd.map _)]
      exact mul_eq_zero_of_right _ k2))
    (fun x => by
      have hX : algebraMap (PowerSeries O') K PowerSeries.X ≠ 0 := by rw [← S.r_one]; exact Units.ne_zero _
      obtain ⟨h, hh⟩ := (S.int n j hn ho hu (by omega) ⊤ fun _ => trivial).2.2
        ((ValuationSubring.valuation_eq_one_iff (⊤ : ValuationSubring K) ⟨_, trivial⟩).1
          (IsUnit.of_mul_eq_one ⟨_⁻¹, trivial⟩ (Subtype.ext (mul_inv_cancel₀ hX)))) x
      exact ⟨h, fun e => by rw [e, map_zero] at hh; exact zero_ne_one hh⟩)
  exact ⟨o, e1, Units.ext e2, e3⟩
end GlobalTheory.Ex.OneLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsObjectWithThetaPointOfDegenerationSeriesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_object_with_thetaPoint_of_degenerationSeries : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → ∀ (S : Ser a K (algebraMap _ K)) (n j : ℕ), n.Prime → Odd n → IsUnit (n : O') → ¬ n ∣ H.d → 2 ≤ j → ∃ o : Full D K, o.ρ = S.A.ρ ∧ o.I.ζ ((n ^ j) ^ 2) = S.A.I.ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (S.v (n ^ j)) := by
  first | exact @GlobalTheory.Ex.OneLevel.exists_full_theta | exact GlobalTheory.Ex.OneLevel.exists_full_theta | (intros; apply GlobalTheory.Ex.OneLevel.exists_full_theta <;> assumption)
end
