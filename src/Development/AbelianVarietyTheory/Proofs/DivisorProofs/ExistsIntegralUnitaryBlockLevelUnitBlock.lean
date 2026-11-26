module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemPolarizationIdealOfMemConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentPowerLimitCongruentOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentPowerLimitCongruentOne
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.PowIdem

theorem exists_period {M : Type*} [Monoid M] [Finite M] (y : M) :
    ∃ i p : ℕ, 0 < p ∧ i + p ≤ Nat.card M ∧ y ^ (i + p) = y ^ i := by
  classical
  haveI := Fintype.ofFinite M
  obtain ⟨a, b, hab, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Nat.card M + 1) => y ^ (i : ℕ)) (by simp [Nat.card_eq_fintype_card])
  have ha := a.isLt
  have hb := b.isLt
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hab) with hlt | hlt
  · refine ⟨a, b - a, by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel' hlt.le]; exact h.symm
  · refine ⟨b, a - b, by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel' hlt.le]; exact h

theorem pow_add_mul_factorial {M : Type*} [Monoid M] [Finite M] (y : M) (n : ℕ)
    (hn : Nat.card M ≤ n) (k j : ℕ) (hk : n ≤ k) : y ^ (k + j * n.factorial) = y ^ k := by
  obtain ⟨i, p, hp, hip, h⟩ := exists_period y
  have step : ∀ t, i ≤ t → y ^ (t + p) = y ^ t := by
    intro t ht
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [show i + s + p = s + (i + p) by ring, pow_add, h, ← pow_add, add_comm s i]
  have iter : ∀ q t, i ≤ t → y ^ (t + q * p) = y ^ t := by
    intro q
    induction q with
    | zero => intro t _; simp
    | succ q ih =>
      intro t ht
      rw [show t + (q + 1) * p = (t + q * p) + p by ring, step _ (by omega), ih t ht]
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hp (by omega : p ≤ n)
  rw [hc, show j * (p * c) = (j * c) * p by ring]
  exact iter _ _ (by omega)

theorem finite_quot (D : D7) (N : ℕ) (hN : 0 < N) :
    Finite (OhE D ⧸ Ideal.span {(N : OhE D)}) := by
  let ι : 𝓞 D.host.E →+* OhE D :=
    ((inc D).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict _
      fun x => GlobalTheory.CongApprox.inc_mem_OhE D x
  haveI : Finite (𝓞 D.host.E ⧸ Ideal.span {(N : 𝓞 D.host.E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')
  refine Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 D.host.E)})
    (Ideal.span {(N : OhE D)}) ι ?_) ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change ι N ∈ Ideal.span {(N : OhE D)}
    rw [map_natCast]
    exact Ideal.mem_span_singleton_self _
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, w, hw, h⟩ := GlobalTheory.CongApprox.exists_int_approx D N hN z z.2
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    change (z : AE D) - inc D (x : D.host.E) = ((N : OhE D) : AE D) * w
    rw [h, add_sub_cancel_left]
    simp

theorem exists_of_mk_eq (D : D7) (N : ℕ) (a b : OhE D)
    (h : Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) a = Ideal.Quotient.mk _ b) :
    ∃ w ∈ OhE D, (a : AE D) = b + (N : AE D) * w := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, c.2, ?_⟩
  have := congrArg Subtype.val hc
  push_cast at this
  linear_combination this

theorem mk_eq_of_exists (D : D7) (N : ℕ) (a b : OhE D) (w : AE D) (hw : w ∈ OhE D)
    (h : (a : AE D) = b + (N : AE D) * w) :
    Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) a = Ideal.Quotient.mk _ b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
  push_cast
  linear_combination h

theorem pow_sub_one_mem (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (y : AE D) (hy : y ∈ OhE D)
    (hy1 : y - 1 ∈ hatId D 𝔪) (k : ℕ) : y ^ k - 1 ∈ hatId D 𝔪 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : y ^ (k + 1) - 1 = y * (y ^ k - 1) + (y - 1) := by ring
    rw [e]
    exact add_mem (GlobalTheory.CongApprox.mul_mem_hatId D 𝔪 y hy _ ih) hy1


set_option maxHeartbeats 1600000 in
theorem exists_idem : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ y ∈ OhE D, y - 1 ∈ hatId D 𝔪 → ∃ g ∈ OhE D, y * g * (y * g) = y * g ∧ y * g - 1 ∈ hatId D 𝔪 := by
  intro D 𝔪 h𝔪 y hy hy1
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.T.cmFiniteAdele_integral_separated_complete D
  let R : ℕ → ℕ := fun N =>
    ∑ n ∈ Finset.range (N + 1), Nat.card (OhE D ⧸ Ideal.span {(n : OhE D)})
  have hR : ∀ N : ℕ, Nat.card (OhE D ⧸ Ideal.span {(N : OhE D)}) ≤ R N := fun N =>
    Finset.single_le_sum (f := fun n : ℕ => Nat.card (OhE D ⧸ Ideal.span {((n : ℕ) : OhE D)}))
      (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ N)
  have hRmono : ∀ N M, N ≤ M → R N ≤ R M := fun N M h =>
    Finset.sum_le_sum_of_subset (by intro a ha; simp only [Finset.mem_range] at ha ⊢; omega)
  let ys : OhE D := ⟨y, hy⟩
  let e : ℕ → ℕ := fun N => 2 * (R N).factorial - 1
  have key : ∀ N : ℕ, 0 < N → ∀ k j, R N ≤ k →
      (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (k + j * (R N).factorial) =
        (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ k := by
    intro N hN k j hk
    haveI := finite_quot D N hN
    exact pow_add_mul_factorial _ _ (hR N) k j hk
  have he : ∀ N : ℕ, R N ≤ e N := by
    intro N
    have := Nat.self_le_factorial (R N)
    have := Nat.factorial_pos (R N)
    simp only [e]
    omega
  have he1 : ∀ N : ℕ, e N + 1 = 2 * (R N).factorial := by
    intro N
    have := Nat.factorial_pos (R N)
    simp only [e]
    omega
  have hediv : ∀ N M : ℕ, R N ≤ R M → ∃ j : ℕ, e M = e N + j * (R N).factorial := by
    intro N M hle
    obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hle
    have hF := Nat.factorial_pos (R N)
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · have := Nat.factorial_pos (R M); rw [hc, h0, mul_zero] at this; omega
      · exact h0
    obtain ⟨c', rfl⟩ := Nat.exists_eq_add_of_le' hc0
    refine ⟨2 * c', ?_⟩
    simp only [e]
    rw [hc]
    have h1 : (R N).factorial * (c' + 1) = (R N).factorial * c' + (R N).factorial := by ring
    have h2 : 2 * c' * (R N).factorial = 2 * ((R N).factorial * c') := by ring
    rw [h1, h2]
    omega
  clear_value e R
  let x : ℕ → AE D := fun N => ((ys ^ e N : OhE D) : AE D)
  have hx : ∀ N : ℕ, x N ∈ OhE D := fun N => (ys ^ e N).2
  have hcong : ∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ OhE D, x (N * m) = x N + (N : AE D) * w := by
    intro N m hN hm
    apply exists_of_mk_eq
    obtain ⟨j, hj⟩ := hediv N (N * m) (hRmono _ _ (Nat.le_mul_of_pos_right N hm))
    rw [map_pow, map_pow, hj, key N hN _ _ (he N)]
  obtain ⟨g, hg, hgN⟩ := hcpl x hx hcong
  let gs : OhE D := ⟨g, hg⟩
  have hmk : ∀ N : ℕ, 0 < N → Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) gs =
      (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ e N := by
    intro N hN
    obtain ⟨w, hw, h⟩ := hgN N hN
    rw [← map_pow]
    exact mk_eq_of_exists D N gs (ys ^ e N) w hw h
  have hyg : ∀ N : ℕ, 0 < N → Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs) =
      (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (2 * (R N).factorial) := by
    intro N hN
    rw [map_mul, hmk N hN, ← he1]
    exact (pow_succ' _ _).symm
  refine ⟨g, hg, ?_, ?_⟩
  · have h0 : y * g * (y * g) - y * g = 0 := by
      apply hsep
      intro N hN
      have hq : Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs * (ys * gs)) =
          Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs) := by
        have hk : R N ≤ 2 * (R N).factorial := (he N).trans ((Nat.le_succ _).trans (he1 N).le)
        calc Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs * (ys * gs))
            = Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs) *
                Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs) := map_mul _ _ _
          _ = (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (2 * (R N).factorial) *
                (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (2 * (R N).factorial) := by
              rw [hyg N hN]
          _ = (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^
                (2 * (R N).factorial + 2 * (R N).factorial) := (pow_add _ _ _).symm
          _ = (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (2 * (R N).factorial) :=
              key N hN _ 2 hk
          _ = Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs) := (hyg N hN).symm
      obtain ⟨w, hw, h⟩ := exists_of_mk_eq D N _ _ hq
      refine ⟨w, hw, ?_⟩
      have h' : y * g * (y * g) = y * g + (N : AE D) * w := h
      rw [h']; ring
    exact sub_eq_zero.1 h0
  · have hN0 : 0 < Ideal.absNorm 𝔪 := by
      rcases Nat.eq_zero_or_pos (Ideal.absNorm 𝔪) with h0 | h0
      · exact absurd (Ideal.absNorm_eq_zero_iff.1 h0) h𝔪
      · exact h0
    obtain ⟨w, hw, h⟩ := exists_of_mk_eq D (Ideal.absNorm 𝔪) (ys * gs) (ys ^ (2 * (R (Ideal.absNorm 𝔪)).factorial))
      (by rw [map_pow]; exact hyg _ hN0)
    have h' : y * g = y ^ (2 * (R (Ideal.absNorm 𝔪)).factorial) + (Ideal.absNorm 𝔪 : AE D) * w := by
      exact h
    have hmem : (Ideal.absNorm 𝔪 : AE D) * w ∈ hatId D 𝔪 := by
      refine AddSubgroup.subset_closure ⟨(Ideal.absNorm 𝔪 : 𝓞 D.host.E), Ideal.absNorm_mem 𝔪, w, hw, ?_⟩
      congr 1
    rw [h', show y ^ (2 * (R (Ideal.absNorm 𝔪)).factorial) + (Ideal.absNorm 𝔪 : AE D) * w - 1 =
      (y ^ (2 * (R (Ideal.absNorm 𝔪)).factorial) - 1) + (Ideal.absNorm 𝔪 : AE D) * w by ring]
    exact add_mem (pow_sub_one_mem D 𝔪 y hy hy1 _) hmem

end GlobalTheory.PowIdem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentPowerLimitCongruentOneStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_powerLimit_congruentOne : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ y ∈ OhE D, y - 1 ∈ hatId D 𝔪 → ∃ g ∈ OhE D, y * g * (y * g) = y * g ∧ y * g - 1 ∈ hatId D 𝔪 := by
  first | exact @GlobalTheory.PowIdem.exists_idem | exact GlobalTheory.PowIdem.exists_idem | (intros; apply GlobalTheory.PowIdem.exists_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryBlockLevelUnitBlock
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.BlockPoint

variable {D : D7}

theorem det_mem_OhE {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE D)) (hM : ∀ i j, M i j ∈ OhE D) : M.det ∈ OhE D := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hM _ _)

theorem one_mem_OhE {n : ℕ} (i j : Fin n) : (1 : Matrix (Fin n) (Fin n) (AE D)) i j ∈ OhE D := by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem adjugate_mem_OhE {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE D)) (hM : ∀ i j, M i j ∈ OhE D) (i j : Fin n) :
    M.adjugate i j ∈ OhE D := by
  classical
  rw [Matrix.adjugate_apply]
  refine det_mem_OhE _ fun k l => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  · exact hM _ _

theorem exists_sep (𝔪 : Ideal (𝓞 D.host.E)) (hco : IsCoprime 𝔪 (D.host.conj • 𝔪)) :
    ∃ T ∈ OhE D, 1 - T ∈ hatId D 𝔪 ∧ sgA D T ∈ hatId D 𝔪 := by
  have hsup : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ := by
    rw [← Ideal.add_eq_sup, Ideal.isCoprime_iff_add.1 hco, Ideal.one_eq_top]
  have h1m : (1 : 𝓞 D.host.E) ∈ 𝔪 ⊔ D.host.conj • 𝔪 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1m
  refine ⟨inc D (t : D.host.E), VacMove.inc_int D t, ?_, ?_⟩
  · have e : 1 - inc D (t : D.host.E) = inc D (s : D.host.E) * 1 := by
      rw [mul_one, ← map_one (inc D), ← map_sub]
      congr 1
      have h3 := congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) hst
      push_cast at h3
      linear_combination -h3
    rw [e]
    exact AddSubgroup.subset_closure ⟨s, hs, 1, one_mem _, rfl⟩
  · have h1 : inc D (t : D.host.E) ∈ hatId D (D.host.conj • 𝔪) :=
      AddSubgroup.subset_closure ⟨t, ht, 1, one_mem _, (mul_one _).symm⟩
    have h2 := DetCong.sgA_mem_hatId h1
    have hcc : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun x => VacMove.conj_conj D x
    rwa [smul_smul, hcc, one_smul] at h2

theorem block_inv_mul {a d : ℕ} (had : a ≤ d) (𝔪 : Ideal (𝓞 D.host.E)) (H H' : Matrix (Fin d) (Fin d) (AE D))
    (hH' : ∀ i j, H' i j ∈ OhE D) (hHH : H' * H = 1)
    (hC : ∀ i j : Fin d, j.1 < a → a ≤ i.1 → H i j ∈ hatId D 𝔪) (i j : Fin a) :
    ((Matrix.of fun i j : Fin a => H' (Fin.castLE had i) (Fin.castLE had j)) *
      (Matrix.of fun i j : Fin a => H (Fin.castLE had i) (Fin.castLE had j)) - 1) i j ∈ hatId D 𝔪 := by
  classical
  have e1 : (1 : Matrix (Fin a) (Fin a) (AE D)) i j = (H' * H) (Fin.castLE had i) (Fin.castLE had j) := by
    rw [hHH, Matrix.one_apply, Matrix.one_apply]
    simp [Fin.castLE_inj]
  have e3 : Finset.univ.filter (fun l : Fin d => l.1 < a) = Finset.univ.map (Fin.castLEEmb had) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro hl; exact ⟨⟨l, hl⟩, rfl⟩
    · rintro ⟨l', rfl⟩; exact l'.2
  rw [Matrix.sub_apply, e1, Matrix.mul_apply, Matrix.mul_apply,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l : Fin d => l.1 < a), e3, Finset.sum_map]
  simp only [Matrix.of_apply, Fin.castLEEmb_apply]
  rw [sub_add_cancel_left]
  refine neg_mem (sum_mem fun l hl => mul_mem_hatId (hH' _ _) (hC l _ j.2 ?_))
  exact not_lt.1 (Finset.mem_filter.1 hl).2

section Glue

variable {R : Type*} [CommRing R] (σ : R →+* R) {n : ℕ}

theorem ct_comb (hσ : ∀ x, σ (σ x) = x) (f g c : R) (M N : Matrix (Fin n) (Fin n) R) :
    ((f • M + g • (N.map σ).transpose + c • (1 : Matrix (Fin n) (Fin n) R)).map σ).transpose =
      σ f • (M.map σ).transpose + σ g • N + σ c • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [hσ]
  · simp [hσ, Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]

theorem glue_mul_ct (hσ : ∀ x, σ (σ x) = x) (M B : Matrix (Fin n) (Fin n) R) (f0 f e : R) (hidem : f0 * f0 = f0)
    (hf : f = f0 * (1 - σ f0)) (he : e = 1 - f - σ f) (hAB : M * B = f0 • (1 : Matrix (Fin n) (Fin n) R)) :
    (f • M + σ f • (B.map σ).transpose + e • (1 : Matrix (Fin n) (Fin n) R)) *
      ((f • M + σ f • (B.map σ).transpose + e • (1 : Matrix (Fin n) (Fin n) R)).map σ).transpose = 1 := by
  have hs0 : σ f0 * σ f0 = σ f0 := by rw [← map_mul, hidem]
  have sf : σ f = σ f0 * (1 - f0) := by rw [hf, map_mul, map_sub, map_one, hσ]
  have se : σ e = e := by rw [he, map_sub, map_sub, map_one, hσ]; ring
  have hBA : (B.map σ).transpose * (M.map σ).transpose = σ f0 • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hAB]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  have hff : f * f = f := by rw [hf]; linear_combination (1 - σ f0) ^ 2 * hidem + f0 * hs0
  have hgg : σ f * σ f = σ f := by rw [← map_mul, hff]
  have hfg : f * σ f = 0 := by rw [sf, hf]; linear_combination (σ f0 * σ f0 - σ f0) * hidem
  have hgf : σ f * f = 0 := by rw [mul_comm, hfg]
  have hfe : f * e = 0 := by rw [he]; linear_combination -hff - hfg
  have hef : e * f = 0 := by rw [mul_comm, hfe]
  have hge : σ f * e = 0 := by rw [he]; linear_combination -hgg - hfg
  have heg : e * σ f = 0 := by rw [mul_comm, hge]
  have hee : e * e = e := by rw [he]; linear_combination hff + hgg + 2 * hfg
  have hff0 : f * f0 = f := by rw [hf]; linear_combination (1 - σ f0) * hidem
  have hgs0 : σ f * σ f0 = σ f := by rw [sf]; linear_combination (1 - f0) * hs0
  rw [ct_comb σ hσ, hσ, se]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_add]
  simp only [hff, hfg, hgf, hfe, hef, hge, heg, hgg, hee, zero_smul, add_zero, zero_add]
  rw [hAB, hBA, smul_smul, smul_smul, hff0, hgs0, ← add_smul, ← add_smul, he]
  rw [show σ f + f + (1 - f - σ f) = 1 by ring, one_smul]

theorem ct_ct (hσ : ∀ x, σ (σ x) = x) (M : Matrix (Fin n) (Fin n) R) :
    (((M.map σ).transpose).map σ).transpose = M := by
  ext i j; simp [hσ]

end Glue

theorem exists_unitary_near {a : ℕ} (𝔪 : Ideal (𝓞 D.host.E)) (h𝔪 : 𝔪 ≠ ⊥) (hco : IsCoprime 𝔪 (D.host.conj • 𝔪))
    (A : Matrix (Fin a) (Fin a) (AE D)) (hA : ∀ i j, A i j ∈ OhE D) (δ' : AE D) (hδ' : δ' ∈ OhE D)
    (hδ : δ' * A.det - 1 ∈ hatId D 𝔪) :
    ∃ k ∈ intG D a, ∀ i j, (A - (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈
      hatId D 𝔪 := by
  obtain ⟨T, hT, hT1, hTs⟩ := exists_sep 𝔪 hco
  have hdet := det_mem_OhE A hA
  have hy : T * (A.det * δ') ∈ OhE D := mul_mem hT (mul_mem hdet hδ')
  have hy1 : T * (A.det * δ') - 1 ∈ hatId D 𝔪 := by
    have e : T * (A.det * δ') - 1 = T * (δ' * A.det - 1) - (1 - T) := by ring
    rw [e]
    exact sub_mem (mul_mem_hatId hT hδ) hT1
  obtain ⟨g, hg, hidem, hf1⟩ := GlobalTheory.T.exists_idempotent_powerLimit_congruentOne D 𝔪 h𝔪 _ hy hy1
  obtain ⟨f0, hf0⟩ : ∃ f0, f0 = T * (A.det * δ') * g := ⟨_, rfl⟩
  rw [← hf0] at hidem hf1
  have hf0O : f0 ∈ OhE D := hf0 ▸ mul_mem hy hg
  have hs0O : sgA D f0 ∈ OhE D := VacMove.sgA_mem D hf0O
  have hs0m : sgA D f0 ∈ hatId D 𝔪 := by
    have e : sgA D f0 = sgA D T * sgA D ((A.det * δ') * g) := by rw [hf0, mul_assoc, map_mul]
    rw [e]
    exact mem_hatId_mul (VacMove.sgA_mem D (mul_mem (mul_mem hdet hδ') hg)) hTs
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin a) (Fin a) (AE D), B = (T * δ' * g) • A.adjugate := ⟨_, rfl⟩
  have hAB : A * B = f0 • (1 : Matrix (Fin a) (Fin a) (AE D)) := by
    rw [hB, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hf0]
    congr 1; ring
  have hBO : ∀ i j, B i j ∈ OhE D := fun i j => by
    rw [hB, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (mul_mem (mul_mem hT hδ') hg) (adjugate_mem_OhE A hA i j)
  obtain ⟨f, hf⟩ : ∃ f, f = f0 * (1 - sgA D f0) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = 1 - f - sgA D f := ⟨_, rfl⟩
  have sf : sgA D f = sgA D f0 * (1 - f0) := by rw [hf, map_mul, map_sub, map_one, VacMove.sgA_sgA]
  have hfO : f ∈ OhE D := hf ▸ mul_mem hf0O (sub_mem (one_mem _) hs0O)
  have hgO : sgA D f ∈ OhE D := VacMove.sgA_mem D hfO
  have heO : e ∈ OhE D := he ▸ sub_mem (sub_mem (one_mem _) hfO) hgO
  have hgm : sgA D f ∈ hatId D 𝔪 := by
    rw [sf]; exact mem_hatId_mul (sub_mem (one_mem _) hf0O) hs0m
  have h1f : 1 - f ∈ hatId D 𝔪 := by
    have e1 : 1 - f = -(f0 - 1) + f0 * sgA D f0 := by rw [hf]; ring
    rw [e1]
    exact add_mem (neg_mem hf1) (mul_mem_hatId hf0O hs0m)
  have hem : e ∈ hatId D 𝔪 := by rw [he]; exact sub_mem h1f hgm
  have hKK := glue_mul_ct (sgA D) (VacMove.sgA_sgA D) A B f0 f e hidem hf he hAB
  obtain ⟨K, hK⟩ : ∃ K : Matrix (Fin a) (Fin a) (AE D),
      K = f • A + sgA D f • (B.map (sgA D)).transpose + e • (1 : Matrix (Fin a) (Fin a) (AE D)) := ⟨_, rfl⟩
  rw [← hK] at hKK
  have hKO : ∀ i j, K i j ∈ OhE D := fun i j => by
    rw [hK]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, Matrix.map_apply]
    exact add_mem (add_mem (mul_mem hfO (hA i j)) (mul_mem hgO (VacMove.sgA_mem D (hBO j i))))
      (mul_mem heO (one_mem_OhE i j))
  let kGL : GL (Fin a) (AE D) := ⟨(K.map (sgA D)).transpose, K, mul_eq_one_comm.1 hKK, hKK⟩
  have hmem : kGL ∈ GA D a := by
    rw [PtsMem.mem_GA]
    show (((K.map (sgA D)).transpose).map (sgA D)).transpose * (K.map (sgA D)).transpose = 1
    rw [ct_ct (sgA D) (VacMove.sgA_sgA D)]
    exact hKK
  refine ⟨⟨kGL, hmem⟩, (mem_intG _).2 fun i j => ⟨?_, hKO i j⟩, fun i j => ?_⟩
  · show sgA D (K j i) ∈ OhE D
    exact VacMove.sgA_mem D (hKO j i)
  · show (A - K) i j ∈ hatId D 𝔪
    have e2 : (A - K) i j = (1 - f) * A i j - sgA D f * sgA D (B j i) -
        e * (1 : Matrix (Fin a) (Fin a) (AE D)) i j := by
      rw [hK]
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply,
        Matrix.map_apply]
      ring
    rw [e2]
    exact sub_mem (sub_mem (mem_hatId_mul (hA i j) h1f) (mem_hatId_mul (VacMove.sgA_mem D (hBO j i)) hgm))
      (mem_hatId_mul (one_mem_OhE i j) hem)

theorem exists_intG_unitBlock : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ {a d : ℕ}, a ≤ d →
    ∀ h ∈ intG D d, (∀ i j : Fin d, j.1 < a → a ≤ i.1 →
      ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪) →
    ∃ k ∈ intG D a, ∀ i j, (((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * (unitBlock D 0 a d).map (inc D) -
      (unitBlock D 0 a d).map (inc D) * (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈
        hatId D 𝔪 := by
  intro D 𝔪 h𝔪 hco a d had h hh hC
  have hint := (mem_intG h).1 hh
  have hHH : ((((h : GL (Fin d) (AE D))⁻¹ : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) *
      ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D))) = 1 := Units.inv_mul _
  have hAA := block_inv_mul had 𝔪 _ _ (fun i j => (hint i j).2) hHH hC
  have hAAO : ∀ i j, ((Matrix.of fun i j : Fin a => (((h : GL (Fin d) (AE D))⁻¹ : GL (Fin d) (AE D)) :
      Matrix (Fin d) (Fin d) (AE D)) (Fin.castLE had i) (Fin.castLE had j)) *
      (Matrix.of fun i j : Fin a => ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D))
        (Fin.castLE had i) (Fin.castLE had j))) i j ∈ OhE D := fun i j => by
    rw [Matrix.mul_apply]
    exact sum_mem fun l _ => mul_mem (hint _ _).2 (hint _ _).1
  have hδ := DetCong.det_sub_one_mem_hatId_of _ hAAO hAA
  rw [Matrix.det_mul] at hδ
  obtain ⟨k, hk, hK⟩ := exists_unitary_near 𝔪 h𝔪 hco _ (fun i j => (hint _ _).1) _
    (det_mem_OhE _ fun i j => (hint _ _).2) hδ
  refine ⟨k, hk, fun i j => ?_⟩
  have hHP : (((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * (unitBlock D 0 a d).map (inc D)) i j =
      ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i (Fin.castLE had j) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE had j)]
    · simp [unitBlock]
    · intro l _ hl
      have : l.1 ≠ j.1 := fun e => hl (Fin.ext (by simpa using e))
      have e0 : (unitBlock D 0 a d).map (inc D) l j = 0 := by simp [unitBlock, this]
      rw [e0, mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  rw [Matrix.sub_apply, hHP, Matrix.mul_apply]
  by_cases hi : i.1 < a
  · rw [Finset.sum_eq_single ⟨i.1, hi⟩]
    · have e1 : (unitBlock D 0 a d).map (inc D) i ⟨i.1, hi⟩ = 1 := by simp [unitBlock]
      rw [e1, one_mul]
      have := hK ⟨i.1, hi⟩ j
      exact this
    · intro l _ hl
      have : i.1 ≠ l.1 := fun e => hl (Fin.ext (by simp [e]))
      have e0 : (unitBlock D 0 a d).map (inc D) i l = 0 := by simp [unitBlock, this]
      rw [e0, zero_mul]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · rw [Finset.sum_eq_zero fun l _ => by
      have : i.1 ≠ l.1 := by have := l.2; omega
      have e0 : (unitBlock D 0 a d).map (inc D) i l = 0 := by simp [unitBlock, this]
      rw [e0, zero_mul], sub_zero]
    exact hC i _ j.2 (not_lt.1 hi)

end GlobalTheory.FunObj.StdDatum.BlockPoint

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryBlockLevelUnitBlockStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralUnitary_blockLevel_unitBlock : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ {a d : ℕ}, a ≤ d →
    ∀ h ∈ intG D d, (∀ i j : Fin d, j.1 < a → a ≤ i.1 →
      ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪) →
    ∃ k ∈ intG D a, ∀ i j, (((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * (unitBlock D 0 a d).map (inc D) -
      (unitBlock D 0 a d).map (inc D) * (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈
        hatId D 𝔪 := by
  first | exact @GlobalTheory.FunObj.StdDatum.BlockPoint.exists_intG_unitBlock | exact GlobalTheory.FunObj.StdDatum.BlockPoint.exists_intG_unitBlock | (intros; apply GlobalTheory.FunObj.StdDatum.BlockPoint.exists_intG_unitBlock <;> assumption)
end
