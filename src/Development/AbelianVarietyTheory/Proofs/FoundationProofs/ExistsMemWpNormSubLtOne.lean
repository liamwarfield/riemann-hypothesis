module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Formalism.LocalToGlobal.Columns.PolyFn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemWpNormSubLtOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowSubOneNormLtOne
namespace GlobalTheory.PowerNearOneNorm

theorem exists_pow_sub_one_norm_lt_one {p : ℕ} [hp : Fact (Nat.Prime p)] (x : PadicAlgCl p)
    (hx : ‖x‖ = (1 : ℝ)) : ∃ n : ℕ, 0 < n ∧ ‖x ^ n - (1 : PadicAlgCl p)‖ < (1 : ℝ) := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  let V : Submodule ℚ_[p] (PadicAlgCl p) := Subalgebra.toSubmodule (Algebra.adjoin ℚ_[p] {x})
  have : FiniteDimensional ℚ_[p] V := Module.Finite.iff_fg.mpr hint.fg_adjoin_singleton
  have : ProperSpace V := FiniteDimensional.proper ℚ_[p] V
  have hmem : ∀ n : ℕ, x ^ n ∈ V := fun n =>
    Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℚ_[p] x) n
  let s : ℕ → V := fun n => ⟨x ^ n, hmem n⟩
  have hs : ∀ n, s n ∈ Metric.closedBall (0 : V) 1 := by
    intro n
    simp [s, norm_pow, hx]
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : V) 1).tendsto_subseq hs
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq 1 one_pos
  have h1 := hN (N + 1) (Nat.le_succ N)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (hφ (Nat.lt_succ_self N))
  refine ⟨d + 1, d.succ_pos, ?_⟩
  have e : x ^ φ (N + 1) - x ^ φ N = x ^ φ N * (x ^ (d + 1) - 1) := by
    rw [hd]
    ring
  have h1' : ‖x ^ φ (N + 1) - x ^ φ N‖ < 1 := by simpa [s, dist_eq_norm] using h1
  rwa [e, norm_mul, norm_pow, hx, one_pow, one_mul] at h1'

end GlobalTheory.PowerNearOneNorm
end

open Formalism.MainNotions

namespace GlobalTheory.ResidueRoot

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

def ball (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by show ‖(1 : ℂ_[p])‖ ≤ 1; simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by show ‖(0 : ℂ_[p])‖ ≤ 1; simp
  neg_mem' := fun {a} ha => by show ‖-a‖ ≤ 1; rw [norm_neg]; exact ha

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem norm_add_lt_one {a b : ℂ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)

theorem sub_one_lt_of_pow_p {y : ℂ_[p]} (hy : ‖y‖ ≤ 1) (h : ‖y ^ p - 1‖ < 1) : ‖y - 1‖ < 1 := by
  let Y : ball p := ⟨y, hy⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (Y - 1) 1
  have hr' := congrArg (fun t : ball p => (t : ℂ_[p])) hr
  simp only [sub_add_cancel, one_pow, mul_one] at hr'
  push_cast at hr'
  have hz : ‖y - 1‖ ≤ 1 := (Y - 1).2
  have hrr : ‖(r : ℂ_[p])‖ ≤ 1 := r.2
  have e : (y - 1) ^ p = (y ^ p - 1) + -((p : ℂ_[p]) * (y - 1) * r) := by
    have : (Y : ℂ_[p]) = y := rfl
    rw [this] at hr'
    rw [hr']; ring
  have h2 : ‖(y - 1) ^ p‖ < 1 := by
    rw [e]
    refine norm_add_lt_one h ?_
    rw [norm_neg, norm_mul, norm_mul, mul_assoc]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) norm_p_lt_one
      (mul_le_one₀ hz (norm_nonneg _) hrr)
  rw [norm_pow] at h2
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).1 h2

theorem sub_one_lt_of_pow_p_pow (k : ℕ) {y : ℂ_[p]} (hy : ‖y‖ ≤ 1) (h : ‖y ^ p ^ k - 1‖ < 1) :
    ‖y - 1‖ < 1 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply sub_one_lt_of_pow_p
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy
    · rwa [← pow_mul, ← pow_succ]

theorem exists_root {x : ℂ_[p]} {m : ℕ} (hm : 0 < m) (h : ‖x ^ m - 1‖ < 1) :
    ∃ ζ : ℂ_[p], ζ ^ m = 1 ∧ ‖x - ζ‖ < 1 := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[p] m
  have e := congrArg (eval x) (X_pow_sub_one_eq_prod hm hξ)
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at e
  rw [e, norm_prod] at h
  by_contra hc
  push Not at hc
  refine absurd h (not_lt.2 ?_)
  exact Finset.prod_induction _ (fun r : ℝ => 1 ≤ r) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
    le_rfl fun ζ hζ => hc ζ ((mem_nthRootsFinset hm _).1 hζ)

theorem exists_pow_alg (x : PadicAlgCl p) (hx : ‖x‖ = 1) : ∃ n, 0 < n ∧ ‖x ^ n - 1‖ < 1 := by
  first
  | exact @_root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one
  | exact _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one
  | (apply _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one ..)

end GlobalTheory.ResidueRoot

namespace GlobalTheory

open ResidueRoot

theorem exists_mem_Wp_norm_sub_lt_one (p : ℕ) [hp : Fact p.Prime] (x : ℂ_[p]) (hx : ‖x‖ ≤ 1) :
    ∃ w ∈ GL3Theta.Wp p, ‖x - w‖ < 1 := by
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.1
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)) x 1 one_pos
  rw [dist_eq_norm] at hy
  have hy1 : ‖(y : ℂ_[p])‖ ≤ 1 := by
    have : (y : ℂ_[p]) = x + -(x - y) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (by rw [norm_neg]; exact hy.le))
  rcases hy1.lt_or_eq with h | h
  · refine ⟨0, zero_mem _, ?_⟩
    have := norm_add_lt_one hy h
    simpa using this
  · obtain ⟨n, hn, hyn⟩ := exists_pow_alg y (by rwa [PadicComplex.norm_extends] at h)
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.out.ne_one
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero p))
    have h3 : ‖((y : ℂ_[p]) ^ m) ^ p ^ k - 1‖ < 1 := by
      rw [← PadicComplex.norm_extends, PadicComplex.coe_eq, map_sub, map_pow, map_one,
        ← PadicComplex.coe_eq] at hyn
      rwa [← pow_mul, mul_comm]
    have h4 := sub_one_lt_of_pow_p_pow k
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy1) h3
    obtain ⟨ζ, hζ, h5⟩ := exists_root hm0 h4
    refine ⟨ζ, Subring.le_topologicalClosure _ (Subring.subset_closure
      ⟨m, hm0, ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm).symm, hζ⟩), ?_⟩
    have := norm_add_lt_one hy h5
    simpa using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroMapEqZeroOfWeightNe
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem rowDiv_eq_zero_of_unipotent_fixed {n : ℕ} (nu : DomWeight n) (q : MvPolynomial (Fin n × Fin n) ℂ)
    (hq : ∀ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id →
      (∀ a, (g : Matrix (Fin n) (Fin n) ℂ) a a = 1) → sqAct ℂ n nu g q = q)
    (a b : Fin n) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv ℂ a b k q = 0 := by
  have hfix : ∀ t : ℂ, rowAct ℂ (lfockq_mat a b t) q = q := by
    intro t
    have htri : (lfockq_mat a b t).transpose.BlockTriangular id := by
      intro i j hij
      have hij' : j < i := hij
      simp only [Matrix.transpose_apply, lfockq_mat]
      rw [if_neg hij'.ne, if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hab hij'
    have hdiag : ∀ i, (lfockq_mat a b t).transpose i i = 1 := by
      intro i
      simp only [Matrix.transpose_apply, lfockq_mat]
      rw [if_pos trivial, if_neg, add_zero]
      rintro ⟨h1, h2⟩
      exact hab.ne (h2.symm.trans h1)
    have hdet : (lfockq_mat a b t).transpose.det = 1 := by
      rw [Matrix.det_of_upperTriangular htri]
      simp only [hdiag, Finset.prod_const_one]
    let g : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet ▸ one_ne_zero :
      (lfockq_mat a b t).transpose.det ≠ 0)
    have hg : (g : Matrix (Fin n) (Fin n) ℂ) = (lfockq_mat a b t).transpose := rfl
    have hd : Matrix.GeneralLinearGroup.det g = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hg, hdet, Units.val_one]
    have := hq g htri hdiag
    unfold sqAct at this
    rwa [detPow, hd, one_zpow, Units.val_one, one_smul, hg, Matrix.transpose_transpose] at this
  have hP : rowGen ℂ a b q = Polynomial.C q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective
      (C_injective (Fin n × Fin n) ℂ))
    rintro _ ⟨t, rfl⟩
    show Polynomial.eval _ _ = Polynomial.eval _ _
    rw [lfockq_eval_rowGen, hfix, Polynomial.eval_C]
  rw [rowDiv, hP, Polynomial.coeff_C, if_neg (by omega)]

theorem exists_ne_zero_map_eq_zero_of_weight_ne (n : ℕ) (mu nu : DomWeight n) (hne : mu ≠ nu)
    (φ : (sqRep ℂ n mu).IntertwiningMap (sqRep ℂ n nu)) :
    ∃ f : nablaSq ℂ n mu, f ≠ 0 ∧ φ f = 0 := by
  let f : nablaSq ℂ n mu := ⟨extremal ℂ n mu, hwMem ℂ n n le_rfl _ (factNatW n mu).1⟩
  refine ⟨f, fun h => hwNe ℂ n n le_rfl mu.natW (congrArg Subtype.val h), ?_⟩
  have hint : ∀ g x, φ (sqRep ℂ n mu g x) = sqRep ℂ n nu g (φ x) := fun g x =>
    Representation.IntertwiningMap.isIntertwining _ _ φ g x
  obtain ⟨c, hc⟩ : ∃ c : ℂ, (φ f : MvPolynomial (Fin n × Fin n) ℂ) = c • extremal ℂ n nu := by
    apply hwLine ℂ n n le_rfl nu.natW (factNatW n nu).1 _ (φ f).2
    intro a b hab k hk
    refine rowDiv_eq_zero_of_unipotent_fixed nu _ (fun g h1 h2 => ?_) a b hab k hk
    have e : sqRep ℂ n mu g f = f := Subtype.ext ((factSqHighestWeight ℂ n mu).2 g h1 h2)
    rw [← sqRep_coe, ← hint, e]
  obtain ⟨i, hi⟩ : ∃ i, mu.w i ≠ nu.w i := by
    by_contra h
    push Not at h
    apply hne
    obtain ⟨w, hw⟩ := mu
    obtain ⟨w', hw'⟩ := nu
    have : w = w' := funext h
    subst this
    rfl
  let u : ℂˣ := Units.mk0 2 two_ne_zero
  let t : Fin n → ℂˣ := fun a => if a = i then u else 1
  have hprod : ∀ lam : DomWeight n, ((∏ a, (t a) ^ (lam.w a) : ℂˣ) : ℂ) = (2 : ℂ) ^ lam.w i := by
    intro lam
    rw [Finset.prod_eq_single i (fun b _ hb => by simp [t, hb]) (by simp)]
    simp [t, u]
  have e : sqRep ℂ n mu (diagGL ℂ n t) f = (2 : ℂ) ^ mu.w i • f := by
    apply Subtype.ext
    rw [← hprod]
    exact (factSqHighestWeight ℂ n mu).1 t
  have e2 : sqRep ℂ n nu (diagGL ℂ n t) (φ f) = (2 : ℂ) ^ nu.w i • φ f := by
    let h : nablaSq ℂ n nu := ⟨extremal ℂ n nu, hwMem ℂ n n le_rfl _ (factNatW n nu).1⟩
    have hc' : φ f = c • h := Subtype.ext hc
    have e3 : sqRep ℂ n nu (diagGL ℂ n t) h = (2 : ℂ) ^ nu.w i • h := by
      apply Subtype.ext
      rw [← hprod]
      exact (factSqHighestWeight ℂ n nu).1 t
    rw [hc', map_smul, e3, smul_comm]
  have e4 := hint (diagGL ℂ n t) f
  rw [e, e2, map_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at e4
  refine e4.resolve_left fun h => hi ?_
  have h' : ((2 : ℝ) ^ mu.w i) = (2 : ℝ) ^ nu.w i := by
    simpa [norm_zpow] using congrArg norm h
  exact zpow_right_injective₀ (by norm_num) (by norm_num) h'

end GlobalTheory.Branching
end
