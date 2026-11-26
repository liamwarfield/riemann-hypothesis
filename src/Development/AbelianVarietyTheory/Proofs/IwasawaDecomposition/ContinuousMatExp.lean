module

public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMatExp
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

noncomputable section

namespace GlobalTheory.UpqExpChart

section General

variable {n : Type} [Fintype n] [DecidableEq n]

theorem continuous_matExp : Continuous (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.exp_continuous

theorem exists_chart : ∃ e : OpenPartialHomeomorph (Matrix n n ℂ) (Matrix n n ℂ),
    (e : Matrix n n ℂ → Matrix n n ℂ) = NormedSpace.exp ∧ (0 : Matrix n n ℂ) ∈ e.source := by
  open scoped Matrix.Norms.Operator in
  have h : HasStrictFDerivAt (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix n n ℂ) : Matrix n n ℂ ≃L[ℂ] Matrix n n ℂ) :
        Matrix n n ℂ →L[ℂ] Matrix n n ℂ) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Matrix n n ℂ)
  open scoped Matrix.Norms.Operator in
  exact ⟨h.toOpenPartialHomeomorph _, rfl, h.mem_toOpenPartialHomeomorph_source⟩

theorem exp_mul_exp_neg (X : Matrix n n ℂ) : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
  rw [← Matrix.exp_add_of_commute X (-X) (Commute.refl X).neg_right, add_neg_cancel,
    NormedSpace.exp_zero]

theorem exp_neg_mul_exp (X : Matrix n n ℂ) : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
  simpa using exp_mul_exp_neg (-X)

theorem exp_conj_invol {J : Matrix n n ℂ} (hJ : J * J = 1) (X : Matrix n n ℂ) :
    NormedSpace.exp (J * X * J) = J * NormedSpace.exp X * J :=
  Matrix.exp_units_conj (⟨J, J, hJ, hJ⟩ : (Matrix n n ℂ)ˣ) X

theorem exp_unitary {J : Matrix n n ℂ} (hJ : J * J = 1) {X : Matrix n n ℂ}
    (hX : Xᴴ * J + J * X = 0) : (NormedSpace.exp X)ᴴ * J * NormedSpace.exp X = J := by
  have h1 : Xᴴ = J * (-X) * J := by
    have : Xᴴ * J = J * (-X) := by rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hX
    rw [← this, Matrix.mul_assoc, hJ, Matrix.mul_one]
  rw [← Matrix.exp_conjTranspose, h1, exp_conj_invol hJ, Matrix.mul_assoc _ J J, hJ,
    Matrix.mul_one, Matrix.mul_assoc, exp_neg_mul_exp, Matrix.mul_one]

theorem exp_twist {J : Matrix n n ℂ} (hJ : J * J = 1) {Z : Matrix n n ℂ}
    (hZ : (NormedSpace.exp Z)ᴴ * J * NormedSpace.exp Z = J) :
    NormedSpace.exp (J * (-Z)ᴴ * J) = NormedSpace.exp Z := by
  rw [exp_conj_invol hJ, Matrix.exp_conjTranspose]
  have h1 : (NormedSpace.exp (-Z))ᴴ * (NormedSpace.exp Z)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, exp_mul_exp_neg, Matrix.conjTranspose_one]
  have h2 : (NormedSpace.exp (-Z))ᴴ * J = J * NormedSpace.exp Z := by
    calc (NormedSpace.exp (-Z))ᴴ * J
        = (NormedSpace.exp (-Z))ᴴ * ((NormedSpace.exp Z)ᴴ * J * NormedSpace.exp Z) := by rw [hZ]
      _ = J * NormedSpace.exp Z := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, hJ, Matrix.one_mul]

end General

theorem jpq_sq (P Q : ℕ) : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem mat_unitary {P Q : ℕ} (g : UpqT P Q) :
    (UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat g = Formalism.UG.Jpq P Q := g.2

theorem continuous_mat {P Q : ℕ} : Continuous (UpqT.mat : UpqT P Q → _) :=
  Units.continuous_val.comp continuous_subtype_val

end GlobalTheory.UpqExpChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddMulDerivativeTrunc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.LogAdd

open Polynomial

theorem one_add_mul_derivative_trunc {R : Type} [CommRing R] (n : ℕ) (u : R[X]) (hu : u ^ n = 0) :
    (1 + u) * derivative (∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R[X]) * u ^ (k + 1)) =
      (n.factorial : R[X]) * derivative u := by
  have h1 : derivative (∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R[X]) * u ^ (k + 1)) =
      (∑ k ∈ Finset.range n, (-u) ^ k) * ((n.factorial : R[X]) * derivative u) := by
    rw [derivative_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hd : (k + 1) ∣ n.factorial :=
      Nat.dvd_factorial (Nat.succ_pos k) (Finset.mem_range.1 hk)
    have hc : ((n.factorial / (k + 1) : ℕ) : R[X]) * ((k : R[X]) + 1) = (n.factorial : R[X]) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → R[X]) (Nat.div_mul_cancel hd)
    have hs : derivative ((-1 : R[X]) ^ k) = 0 := by
      rcases neg_one_pow_eq_or R[X] k with h | h <;> simp [h]
    rw [derivative_mul, derivative_mul, hs, derivative_natCast, derivative_pow_succ, ← hc, neg_pow u]
    simp only [map_add (f := _), map_natCast, map_one]
    ring
  have h2 : (1 + u) * ∑ k ∈ Finset.range n, (-u) ^ k = 1 := by
    have := mul_neg_geom_sum (-u) n
    rw [sub_neg_eq_add, neg_pow u, hu, mul_zero, sub_zero] at this
    exact this
  rw [h1, ← mul_assoc, h2, one_mul]

theorem trunc_add {R : Type} [CommRing R] (hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : R)) (n : ℕ)
    (I : Ideal R) (hI : I ^ n = ⊥) (a b : R) (ha : a ∈ I) (hb : b ∈ I) :
    (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * (a + b + a * b) ^ (k + 1)) =
      (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * a ^ (k + 1)) +
      (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * b ^ (k + 1)) := by
  let F : R[X] → R[X] := fun u => ∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R[X]) * u ^ (k + 1)
  let J : Ideal R[X] := I.map (C : R →+* R[X])
  have hJ : ∀ u ∈ J, u ^ n = 0 := by
    intro u hu
    have := Ideal.pow_mem_pow hu n
    rwa [← Ideal.map_pow, hI, Ideal.map_bot, Ideal.mem_bot] at this
  set s : R[X] := C a * X with hs
  set t : R[X] := C b * X with ht
  have hsJ : s ∈ J := J.mul_mem_right _ (Ideal.mem_map_of_mem _ ha)
  have htJ : t ∈ J := J.mul_mem_right _ (Ideal.mem_map_of_mem _ hb)
  have huJ : s + t + s * t ∈ J := J.add_mem (J.add_mem hsJ htJ) (J.mul_mem_right _ hsJ)
  have e1 : (1 + s) * derivative (F s) = _ := one_add_mul_derivative_trunc n s (hJ _ hsJ)
  have e2 : (1 + t) * derivative (F t) = _ := one_add_mul_derivative_trunc n t (hJ _ htJ)
  have e3 : (1 + (s + t + s * t)) * derivative (F (s + t + s * t)) = _ :=
    one_add_mul_derivative_trunc n _ (hJ _ huJ)
  have hunit : IsUnit (1 + (s + t + s * t)) := IsNilpotent.isUnit_one_add ⟨n, hJ _ huJ⟩
  have hD : derivative (F (s + t + s * t) - F s - F t) = 0 := by
    apply hunit.mul_left_cancel
    rw [derivative_add, derivative_add, derivative_mul (f := s) (g := t)] at e3
    rw [derivative_sub, derivative_sub]
    linear_combination e3 - (1 + t) * e1 - (1 + s) * e2
  have hC : F (s + t + s * t) - F s - F t = C ((F (s + t + s * t) - F s - F t).coeff 0) := by
    ext k
    cases k with
    | zero => simp only [coeff_C_zero]
    | succ k =>
      have h := congrArg (fun (p : R[X]) => p.coeff k) hD
      simp only [coeff_derivative, coeff_zero] at h
      rw [coeff_C_succ]
      have hu : IsUnit ((k : R) + 1) := by exact_mod_cast hR (k + 1) (Nat.succ_ne_zero k)
      exact (hu.mul_left_eq_zero).1 h
  have h0 : (F (s + t + s * t) - F s - F t).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    simp [F, hs, ht, eval_finsetSum]
  rw [h0, map_zero] at hC
  have h1 := congrArg (eval 1) hC
  simp only [F, hs, ht, eval_sub, eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one,
    eval_natCast, eval_add, eval_C, eval_X, mul_one, eval_zero] at h1
  linear_combination h1

theorem tm_sub_one_mem (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : e.untilt = 1) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) ∈ Per.kerP l := by
  apply GlobalTheory.RingIface.alg_mem_kerP
  simp [he]

theorem map_mul_sub_one {M A B : Type} [Monoid M] [CommRing A] [CommRing B] (g : M →* A)
    (f : A →+* B) (e e' : M) :
    f (g (e * e') - 1) = f (g e - 1) + f (g e' - 1) + f (g e - 1) * f (g e' - 1) := by
  simp only [map_sub, map_mul, map_one]
  ring

theorem tm_mul_sub_one (l : ℕ) [Fact l.Prime] (e e' : Per.Fl l) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm (e * e') - 1) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) +
        algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e' - 1) +
        algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) *
          algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e' - 1) :=
  map_mul_sub_one (WittVector.teichmuller l) _ e e'

theorem log_add : ∀ (l : ℕ) [Fact l.Prime], ∀ (e e' : Per.Fl l) (y y' z : Per.BdRp l),
    e.untilt = 1 → e'.untilt = 1 → Per.IsLog l e y → Per.IsLog l e' y' →
      Per.IsLog l (e * e') z → z = y + y' := by
  intro l _ e e' y y' z he he' hy hy' hz
  refine GlobalTheory.RingIface.ev_ext l _ _ fun n => ?_
  let q : Per.AinfP l →+* Per.AinfP l ⧸ Per.kerP l ^ n := Ideal.Quotient.mk _
  have hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : Per.AinfP l ⧸ Per.kerP l ^ n) := fun m hm => by
    have := (GlobalTheory.RingBasics.isUnit_nat l m hm).map q
    rwa [map_natCast] at this
  apply (hR _ n.factorial_ne_zero).mul_left_cancel
  rw [map_add (f := _), mul_add, GlobalTheory.CrisIncl.factorial_mul_ev l e y he hy n,
    GlobalTheory.CrisIncl.factorial_mul_ev l e' y' he' hy' n,
    GlobalTheory.CrisIncl.factorial_mul_ev l _ z (by rw [map_mul, he, he', mul_one]) hz n]
  have hI : ((Per.kerP l).map q) ^ n = ⊥ := by
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self _
  have key := trunc_add hR n _ hI _ _ (Ideal.mem_map_of_mem q (tm_sub_one_mem l e he))
    (Ideal.mem_map_of_mem q (tm_sub_one_mem l e' he'))
  rw [tm_mul_sub_one]
  generalize algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) = a at key ⊢
  generalize algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e' - 1) = b at key ⊢
  change q _ = q _ + q _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast, map_add (f := _)]
  exact key

end GlobalTheory.MemLoc.LogAdd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDensityOriginOfAlmostHomogeneous
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem _root_.GlobalTheory.densHom_scale (l : Measure V) [l.IsAddHaarMeasure] (x : V) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) :
    l (Metric.closedBall x (s * r)) =
      ENNReal.ofReal (s ^ Module.finrank ℝ V) * l (Metric.ball 0 r) := by
  rw [Measure.addHaar_closedBall_mul_of_pos l x hs r, Measure.addHaar_closedBall l 0 hr.le,
    Measure.addHaar_ball_of_pos l 0 hr]

theorem _root_.GlobalTheory.densHom_tendsto_mul {s : ℝ} (hs : 0 < s) :
    Tendsto (fun r : ℝ => s * r) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun r : ℝ => s * r) (𝓝 0) (𝓝 (s * 0)) := tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos hs hr

end

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

private theorem closedBall_smul_div_ball_eq_ofReal_pow_mul (l ν : Measure V) [l.IsAddHaarMeasure] (x : V)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    ν (Metric.closedBall x (s * r)) / l (Metric.ball 0 r) =
      ENNReal.ofReal (s ^ Module.finrank ℝ V) *
        (ν (Metric.closedBall x (s * r)) / l (Metric.closedBall x (s * r))) := by
  rw [_root_.GlobalTheory.densHom_scale l x hs hr, ← mul_div_assoc,
    ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.2 (pow_pos hs _)).ne' ENNReal.ofReal_ne_top]

private theorem ofReal_pow_mul_le_liminf_ball_ratio (l ν : Measure V) [l.IsAddHaarMeasure] {x : V} {s : ℝ}
    (hs : 0 < s) {D : ENNReal}
    (hD : Tendsto (fun r => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) (𝓝[>] 0) (𝓝 D))
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (Metric.closedBall x (s * r)) ≤ ν (Metric.ball 0 r)) :
    ENNReal.ofReal (s ^ Module.finrank ℝ V) * D ≤
      liminf (fun r => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) := by
  have htend : Tendsto (fun r => ENNReal.ofReal (s ^ Module.finrank ℝ V) *
      (ν (Metric.closedBall x (s * r)) / l (Metric.closedBall x (s * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (s ^ Module.finrank ℝ V) * D)) :=
    ENNReal.Tendsto.const_mul (hD.comp (_root_.GlobalTheory.densHom_tendsto_mul hs))
      (Or.inr ENNReal.ofReal_ne_top)
  refine (le_of_eq htend.liminf_eq.symm).trans (Filter.liminf_le_liminf ?_)
  filter_upwards [h, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
  rw [← closedBall_smul_div_ball_eq_ofReal_pow_mul l ν x hs hr0]
  exact ENNReal.div_le_div_right hr _

private theorem limsup_ball_ratio_le_ofReal_pow_mul (l ν : Measure V) [l.IsAddHaarMeasure] {x : V} {s : ℝ}
    (hs : 0 < s) {D : ENNReal}
    (hD : Tendsto (fun r => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) (𝓝[>] 0) (𝓝 D))
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (Metric.ball 0 r) ≤ ν (Metric.closedBall x (s * r))) :
    limsup (fun r => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) ≤
      ENNReal.ofReal (s ^ Module.finrank ℝ V) * D := by
  have htend : Tendsto (fun r => ENNReal.ofReal (s ^ Module.finrank ℝ V) *
      (ν (Metric.closedBall x (s * r)) / l (Metric.closedBall x (s * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (s ^ Module.finrank ℝ V) * D)) :=
    ENNReal.Tendsto.const_mul (hD.comp (_root_.GlobalTheory.densHom_tendsto_mul hs))
      (Or.inr ENNReal.ofReal_ne_top)
  refine (Filter.limsup_le_limsup ?_).trans (le_of_eq htend.limsup_eq)
  filter_upwards [h, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
  rw [← closedBall_smul_div_ball_eq_ofReal_pow_mul l ν x hs hr0]
  exact ENNReal.div_le_div_right hr _
end

theorem _root_.GlobalTheory.exists_density_origin_of_almost_homogeneous : ∀ (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V)
    [l.IsAddHaarMeasure] [IsLocallyFiniteMeasure ν], (∀ r : ℝ, 0 < r → ν (Metric.ball 0 r) ≠ 0) →
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ x : V, ‖x‖ < δ →
      ∀ᶠ r in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * r)) ≤ ν (Metric.ball 0 r) ∧
        ν (Metric.ball 0 r) ≤ ν (Metric.ball x ((1 + ε) * r))) →
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      Tendsto (fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c) := by
  intro V _ _ _ _ _ l ν _ _ hpos halmost
  set ρ := fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r) with hρ
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ D : ENNReal, D < ⊤ ∧
      ENNReal.ofReal ((1 - 2 * ε) ^ Module.finrank ℝ V) * D ≤ liminf ρ (𝓝[>] 0) ∧
      limsup ρ (𝓝[>] 0) ≤ ENNReal.ofReal ((1 + ε) ^ Module.finrank ℝ V) * D := by
    intro ε hε hε2
    obtain ⟨δ, hδ, hx⟩ := halmost ε hε (by linarith)
    obtain ⟨x, hxmem, hxD, hxfin⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (Metric.measure_ball_pos l (0 : V) hδ).ne'
      (ae_restrict_of_ae ((Besicovitch.ae_tendsto_rnDeriv ν l).and (Measure.rnDeriv_lt_top ν l)))
    have hxr := hx x (mem_ball_zero_iff.1 hxmem)
    refine ⟨_, hxfin, ofReal_pow_mul_le_liminf_ball_ratio l ν (by linarith) hxD ?_,
      limsup_ball_ratio_le_ofReal_pow_mul l ν (by linarith) hxD ?_⟩
    · filter_upwards [hxr, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
      exact (measure_mono (Metric.closedBall_subset_ball (by nlinarith))).trans hr.1
    · filter_upwards [hxr] with r hr
      exact hr.2.trans (measure_mono Metric.ball_subset_closedBall)
  have hML : liminf ρ (𝓝[>] 0) ≤ limsup ρ (𝓝[>] 0) := liminf_le_limsup
  have hLtop : limsup ρ (𝓝[>] 0) < ⊤ := by
    obtain ⟨D, hD, -, hup⟩ := key (1 / 4) (by norm_num) (by norm_num)
    exact hup.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD)
  have hLM : limsup ρ (𝓝[>] 0) ≤ liminf ρ (𝓝[>] 0) := by
    have hK : Tendsto (fun ε : ℝ => ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V))
        (𝓝 0) (𝓝 1) := by
      have hc : ContinuousAt (fun ε : ℝ =>
          ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V)) 0 :=
        ContinuousAt.div₀ (by fun_prop) (by fun_prop) (by simp)
      simpa using hc.tendsto
    have hT : Tendsto (fun ε : ℝ => ENNReal.ofReal
        ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V) * liminf ρ (𝓝[>] 0))
        (𝓝[>] 0) (𝓝 (liminf ρ (𝓝[>] 0))) := by
      have h1 := ENNReal.Tendsto.mul_const (b := liminf ρ (𝓝[>] 0)) (ENNReal.tendsto_ofReal hK)
        (Or.inr (hML.trans_lt hLtop).ne)
      simpa using h1.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hT ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
    obtain ⟨D, -, hlow, hup⟩ := key ε hε.1 hε.2
    have hb : 0 < (1 - 2 * ε) ^ Module.finrank ℝ V := pow_pos (by linarith [hε.2]) _
    refine hup.trans ?_
    calc ENNReal.ofReal ((1 + ε) ^ Module.finrank ℝ V) * D
        = ENNReal.ofReal ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V) *
          (ENNReal.ofReal ((1 - 2 * ε) ^ Module.finrank ℝ V) * D) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg (pow_nonneg (by linarith [hε.1]) _) hb.le),
            div_mul_cancel₀ _ hb.ne']
      _ ≤ _ := by gcongr
  have htend : Tendsto ρ (𝓝[>] 0) (𝓝 (limsup ρ (𝓝[>] 0))) :=
    tendsto_of_liminf_eq_limsup (le_antisymm hML hLM) rfl
  refine ⟨limsup ρ (𝓝[>] 0), ?_, hLtop.ne, htend⟩
  intro hL0
  rw [hL0] at htend
  obtain ⟨δ, hδ, hx⟩ := halmost (1 / 2) (by norm_num) (by norm_num)
  have hs_le : ∀ t : NNReal, 0 < t → ν (Metric.ball 0 δ) ≤ t * l (Metric.ball 0 δ) := by
    intro t ht
    have hle := VitaliFamily.measure_le_of_frequently_le (Besicovitch.vitaliFamily ν) (t • l)
      (Measure.AbsolutelyContinuous.refl ν) (Metric.ball (0 : V) δ) ?_
    · rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hle
      exact hle
    intro x hxs
    apply ((Besicovitch.tendsto_filterAt ν x).comp
      (_root_.GlobalTheory.densHom_tendsto_mul (show (0 : ℝ) < 1 / 4 by norm_num))).frequently
    refine Filter.Eventually.frequently ?_
    have hpos' : (0 : ENNReal) < t * ENNReal.ofReal ((1 / 4) ^ Module.finrank ℝ V) :=
      ENNReal.mul_pos (by exact_mod_cast ht.ne') (ENNReal.ofReal_pos.2 (by positivity)).ne'
    filter_upwards [(tendsto_order.1 htend).2 _ hpos', hx x (mem_ball_zero_iff.1 hxs),
      self_mem_nhdsWithin] with r hr hxr (hr0 : 0 < r)
    show ν (Metric.closedBall x (1 / 4 * r)) ≤ (t • l) (Metric.closedBall x (1 / 4 * r))
    have hlt : ν (Metric.ball 0 r) <
        t * ENNReal.ofReal ((1 / 4) ^ Module.finrank ℝ V) * l (Metric.ball 0 r) :=
      (ENNReal.div_lt_iff (Or.inl (Metric.measure_ball_pos l 0 hr0).ne')
        (Or.inl measure_ball_lt_top.ne)).1 hr
    rw [mul_assoc, ← _root_.GlobalTheory.densHom_scale l x (by norm_num) hr0] at hlt
    have hsub : Metric.closedBall x (1 / 4 * r) ⊆ Metric.ball x ((1 - 1 / 2) * r) :=
      Metric.closedBall_subset_ball (by linarith)
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ((measure_mono hsub).trans hxr.1).trans hlt.le
  have hzero : ν (Metric.ball 0 δ) = 0 := by
    have hT : Tendsto (fun t : NNReal => (t : ENNReal) * l (Metric.ball 0 δ)) (𝓝[>] 0) (𝓝 0) := by
      have h1 := ENNReal.Tendsto.mul_const (b := l (Metric.ball 0 δ))
        (ENNReal.tendsto_coe.2 (tendsto_id (x := 𝓝 (0 : NNReal)))) (Or.inr measure_ball_lt_top.ne)
      simpa using h1.mono_left nhdsWithin_le_nhds
    exact le_antisymm (ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun t ht => hs_le t ht))
      bot_le
  exact hpos δ hδ hzero

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSubOnePowTotient
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPowSubOneLe
universe u_1

namespace GlobalTheory.NormPowSubOne

theorem norm_pow_sub_one_le {K : Type u_1} [NormedField K] [IsUltrametricDist K] {ζ : K}
    (hζ : ‖ζ‖ = (1 : ℝ)) (a : ℕ) : ‖ζ ^ a - (1 : K)‖ ≤ ‖ζ - (1 : K)‖ := by
  induction a with
  | zero => simp
  | succ n ih =>
    have h : ζ ^ (n + 1) - 1 = ζ * (ζ ^ n - 1) + (ζ - 1) := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul, hζ, one_mul]
    exact ih

theorem main : ∀ {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K] {ζ : K},
    ‖ζ‖ = (1 : ℝ) → ∀ (a : ℕ), ‖ζ ^ a - (1 : K)‖ ≤ ‖ζ - (1 : K)‖ :=
  fun hζ a => norm_pow_sub_one_le hζ a

end GlobalTheory.NormPowSubOne
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.CycTrace
open Polynomial

theorem norm_root_eq_one {K : Type*} [NormedField K] {n : ℕ} (hn : n ≠ 0) {ζ : K}
    (hζ : ζ ^ n = 1) : ‖ζ‖ = 1 := by
  have := congrArg norm hζ
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this

theorem norm_pow_sub_one_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    {ζ : K} (hz : ‖ζ‖ = 1) (a : ℕ) : ‖ζ ^ a - 1‖ ≤ ‖ζ - 1‖ := by
  first
  | exact @_root_.GlobalTheory.NormPowSubOne.main
  | exact _root_.GlobalTheory.NormPowSubOne.main
  | (apply _root_.GlobalTheory.NormPowSubOne.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormPowSubOne.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormPowSubOne.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormPowSubOne.main ..)

theorem norm_sub_one_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    {n : ℕ} (hn : n ≠ 0) {ζ μ : K} (hζ : IsPrimitiveRoot ζ n) (hμ : μ ^ n = 1) :
    ‖μ - 1‖ ≤ ‖ζ - 1‖ := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨a, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  exact norm_pow_sub_one_le (norm_root_eq_one hn hζ.pow_eq_one) a

theorem norm_sub_one_pow_totient {K : Type*} [NormedField K] [IsUltrametricDist K]
    (l : ℕ) [hl : Fact l.Prime] (k : ℕ) (ζ : K) (hζ : IsPrimitiveRoot ζ (l ^ (k + 1))) :
    ‖ζ - 1‖ ^ (l ^ (k + 1)).totient = ‖(l : K)‖ := by
  have hp := hl.out
  have hn : l ^ (k + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have h1 := Polynomial.eval_one_cyclotomic_prime_pow (R := K) (p := l) k
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h1
  have h2 := congrArg norm h1
  rw [norm_prod] at h2
  have h3 : ∀ μ ∈ primitiveRoots (l ^ (k + 1)) K,
      ‖Polynomial.eval 1 (Polynomial.X - Polynomial.C μ)‖ = ‖ζ - 1‖ := by
    intro μ hμ
    have hμ' := (mem_primitiveRoots (Nat.pos_of_ne_zero hn)).1 hμ
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, norm_sub_rev]
    exact le_antisymm (norm_sub_one_le hn hζ hμ'.pow_eq_one)
      (norm_sub_one_le hn hμ' hζ.pow_eq_one)
  rwa [Finset.prod_congr rfl h3, Finset.prod_const, hζ.card_primitiveRoots] at h2

theorem norm_le_norm_sum {K ι : Type*} [NormedField K] [IsUltrametricDist K] (s : Finset ι)
    (f : ι → K) (h : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → ‖f i‖ = ‖f j‖ → i = j) {i : ι} (hi : i ∈ s) :
    ‖f i‖ ≤ ‖∑ j ∈ s, f j‖ := by
  classical
  obtain ⟨k, hk, hmax⟩ := s.exists_max_image (fun j => ‖f j‖) ⟨i, hi⟩
  refine (hmax i hi).trans ?_
  by_cases h0 : f k = 0
  · simp [h0]
  have hlt : ‖∑ j ∈ s.erase k, f j‖ < ‖f k‖ := by
    rcases (s.erase k).eq_empty_or_nonempty with he | hne
    · simpa [he] using h0
    · obtain ⟨j, hj, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne f
      refine hle.trans_lt (lt_of_le_of_ne (hmax j (Finset.mem_of_mem_erase hj)) ?_)
      intro e
      exact (Finset.ne_of_mem_erase hj) (h k hk j (Finset.mem_of_mem_erase hj) h0 e.symm).symm
  rw [← Finset.add_sum_erase s f hk, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne']
  exact le_max_left _ _

variable {l : ℕ} [hl : Fact l.Prime]

theorem norm_l : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  have h2 : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) l := by simp
  rw [h2, norm_algebraMap', Padic.norm_p]

theorem coeff_bound_unif (π : PadicAlgCl l) (e : ℕ) (hπ : ‖π‖ ^ e = (l : ℝ)⁻¹)
    (Q : ℚ_[l][X]) (hQ : Q.natDegree < e) (k : ℕ) :
    (l : ℝ)⁻¹ * ‖Q.coeff k‖ ≤ ‖aeval π Q‖ := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have he : e ≠ 0 := by omega
  have hr0 : 0 < ‖π‖ := by
    rcases (norm_nonneg π).eq_or_lt with h | h
    · rw [← h, zero_pow he] at hπ
      exact absurd hπ (inv_pos.2 hl0).ne
    · exact h
  have hr1 : ‖π‖ < 1 := by
    by_contra h
    have := one_le_pow₀ (not_lt.1 h) (n := e)
    rw [hπ] at this
    exact absurd (inv_lt_one_of_one_lt₀ hl1) (not_lt.2 this)
  by_cases hk : k < e
  swap
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp
  rw [aeval_eq_sum_range' hQ]
  refine le_trans ?_ (norm_le_norm_sum (Finset.range e) (fun j => Q.coeff j • π ^ j) ?_
    (Finset.mem_range.2 hk))
  · simp only [norm_smul, norm_pow]
    rw [mul_comm, ← hπ]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1.le hk.le) (norm_nonneg _)
  · intro i hi j hj h0 hij
    simp only [norm_smul, norm_pow] at hij
    have hi0 : Q.coeff i ≠ 0 := fun h => h0 (by simp [h])
    have hj0 : Q.coeff j ≠ 0 := by
      intro h
      rw [h, norm_zero, zero_mul] at hij
      exact (mul_pos (norm_pos_iff.2 hi0) (pow_pos hr0 _)).ne' hij
    rw [Padic.norm_eq_zpow_neg_valuation hi0, Padic.norm_eq_zpow_neg_valuation hj0,
      ← inv_zpow', ← inv_zpow', ← hπ, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, ← zpow_add₀ hr0.ne', ← zpow_add₀ hr0.ne'] at hij
    have h3 := zpow_right_injective₀ hr0 hr1.ne hij
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    have h4 : (e : ℤ) ∣ (i : ℤ) - j :=
      ⟨(Q.coeff j).valuation - (Q.coeff i).valuation, by linear_combination h3⟩
    have h5 := Int.eq_zero_of_abs_lt_dvd h4 (by rw [abs_lt]; constructor <;> omega)
    omega

theorem coeff_bound (N : ℕ) (z : PadicAlgCl l) (hz : IsPrimitiveRoot z (l ^ (N + 1)))
    (P : ℚ_[l][X]) (hP : P.natDegree < (l ^ (N + 1)).totient) (k : ℕ) :
    (l : ℝ)⁻¹ * ‖P.coeff k‖ ≤ ‖aeval z P‖ := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hπ := norm_sub_one_pow_totient l N z hz
  rw [norm_l] at hπ
  have hQ := coeff_bound_unif (z - 1) _ hπ (taylor 1 P) (by rwa [natDegree_taylor])
  have e1 : aeval (z - 1) (taylor 1 P) = aeval z P := by
    rw [taylor_apply, aeval_comp]; simp
  rw [e1] at hQ
  have e2 : P = taylor (-1) (taylor 1 P) := by rw [taylor_taylor]; simp
  generalize taylor 1 P = Q at hQ e2
  have : ‖P.coeff k‖ ≤ l * ‖aeval z P‖ := by
    conv_lhs => rw [e2, taylor_coeff, eval_eq_sum_range]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
    intro j _
    rw [hasseDeriv_coeff, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
    have h1 := IsUltrametricDist.norm_natCast_le_one ℚ_[l] ((j + k).choose k)
    have h2 := hQ (j + k)
    rw [inv_mul_le_iff₀ hl0] at h2
    calc _ ≤ 1 * ‖Q.coeff (j + k)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ _ := by rwa [one_mul]
  rwa [inv_mul_le_iff₀ hl0]

theorem exists_poly (n : ℕ) (hn : 0 < n) (w : PadicAlgCl l) (hw : IsPrimitiveRoot w n)
    (a : PadicAlgCl l) (ha : a ∈ IntermediateField.adjoin ℚ_[l] {w}) :
    ∃ p : ℚ_[l][X], p.natDegree < n.totient ∧ aeval w p = a := by
  have hint : IsIntegral ℚ_[l] w := (hw.isIntegral hn).tower_top
  have h1 : a ∈ (IntermediateField.adjoin ℚ_[l] {w}).toSubalgebra := ha
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at h1
  obtain ⟨q, rfl⟩ := h1
  have hm : (cyclotomic n ℚ_[l]).Monic := cyclotomic.monic n _
  have hroot : aeval w (cyclotomic n ℚ_[l]) = 0 := by
    rw [aeval_def, ← eval_map, map_cyclotomic]
    exact hw.isRoot_cyclotomic hn
  refine ⟨q %ₘ cyclotomic n ℚ_[l], ?_, aeval_modByMonic_eq_self_of_root hroot⟩
  rw [← natDegree_cyclotomic n ℚ_[l]]
  refine natDegree_modByMonic_lt q hm ?_
  intro h
  have := natDegree_cyclotomic n ℚ_[l]
  rw [h, natDegree_one] at this
  exact (Nat.totient_pos.2 hn).ne this

end GlobalTheory.CycTrace

open Polynomial GlobalTheory.CycTrace in
theorem GlobalTheory.CycTrace.normalised_trace_bound (l : ℕ) [hl : Fact l.Prime] (n m : ℕ) (z : Om l)
    (hn : 1 ≤ n) (hz : IsPrimitiveRoot z (l ^ (n + m))) (a : Fin (l ^ m) → Om l)
    (ha : ∀ i, a i ∈ IntermediateField.adjoin ℚ_[l] {z ^ (l ^ m)}) :
    ‖(l : Om l)‖ * ‖a ⟨0, pow_pos (Fact.out : l.Prime).pos m⟩‖ ≤ ‖∑ i, a i * z ^ (i : ℕ)‖ := by
  have hp := hl.out
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hp.pos
  have hM : 0 < l ^ m := pow_pos hp.pos m
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hw : IsPrimitiveRoot (z ^ (l ^ m)) (l ^ (n + 1)) :=
    hz.pow (pow_pos hp.pos _) (by rw [pow_add, mul_comm])
  choose p hp1 hp2 using fun i => exists_poly _ (pow_pos hp.pos _) _ hw (a i) (ha i)
  have hN : n + 1 + m = (n + m) + 1 := by ring
  rw [hN] at hz
  set P : ℚ_[l][X] := ∑ i : Fin (l ^ m), expand ℚ_[l] (l ^ m) (p i) * X ^ (i : ℕ) with hPdef
  have htot : (l ^ (n + m + 1)).totient = (l ^ (n + 1)).totient * l ^ m := by
    rw [Nat.totient_prime_pow_succ hp, Nat.totient_prime_pow_succ hp]; ring
  have hdeg : P.natDegree < (l ^ (n + m + 1)).totient := by
    have hpos : 0 < (l ^ (n + m + 1)).totient := Nat.totient_pos.2 (pow_pos hp.pos _)
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le (n := (l ^ (n + m + 1)).totient - 1) _ _ ?_) (by omega)
    intro i _
    refine natDegree_mul_le.trans ?_
    rw [natDegree_expand, natDegree_X_pow]
    have h1 := hp1 i
    have h2 := i.2
    have h3 : ((p i).natDegree + 1) * l ^ m ≤ (l ^ (n + 1)).totient * l ^ m :=
      Nat.mul_le_mul_right _ h1
    rw [add_mul] at h3
    omega
  have hev : aeval z P = ∑ i, a i * z ^ (i : ℕ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hPdef, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, expand_aeval, hp2]; simp
  have hco : ∀ j, P.coeff (j * l ^ m) = (p ⟨0, hM⟩).coeff j := by
    intro j
    rw [hPdef, Polynomial.finsetSum_coeff, Finset.sum_eq_single ⟨0, hM⟩]
    · simp [coeff_expand_mul hM]
    · intro i _ hi
      rw [coeff_mul_X_pow']
      split_ifs with h
      · rw [coeff_expand hM, if_neg]
        intro hd
        have : l ^ m ∣ (i : ℕ) := by
          have := (Nat.dvd_sub_iff_right h (Dvd.intro_left j rfl)).1 hd
          exact this
        exact hi (Fin.ext (Nat.eq_zero_of_dvd_of_lt this i.2))
      · rfl
    · simp
  have hb := fun j => coeff_bound (n + m) z hz P hdeg (j * l ^ m)
  simp only [hco, hev] at hb
  have hw1 : ‖z ^ (l ^ m)‖ = 1 := norm_root_eq_one (pow_pos hp.pos _).ne' hw.pow_eq_one
  rw [norm_l, inv_mul_le_iff₀ hl0, ← hp2, aeval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
  intro j _
  rw [norm_smul, norm_pow, hw1, one_pow, mul_one, ← inv_mul_le_iff₀ hl0]
  exact hb j
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaLebesgueMeasure
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.OmegaLebExists

theorem J_conjTranspose (P Q : ℕ) : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by
  unfold Formalism.UG.Jpq
  rw [fromBlocks_conjTranspose]
  simp

end GlobalTheory.OmegaLebExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffGaloisTilt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem coeff_galois_tilt (l : ℕ) [Fact l.Prime] (g : GQ l) (x : OCb l) (n : ℕ) (y : OC l)
    (h : PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y) :
    ∃ y' : OC l, (y' : PadicComplex l) = Per.σC g (y : PadicComplex l) ∧
      PreTilt.coeff n (Per.σF g x) = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y' :=
  ⟨Per.σO g y, GlobalTheory.RingIface.sigO_coe (l := l) g y,
    GlobalTheory.AdicMaps.coeff_galois l g x n y h⟩

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCyclotomicChar
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
namespace GlobalTheory.MemLoc

theorem _root_.GlobalTheory.MemLoc.exists_cyclotomicChar : ∀ (l : ℕ) [Fact l.Prime], ∃ χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℤ_[l]ˣ,
    ∀ (g : _root_.Formalism.BasicNotions.Loc.GQ l) (m : ℕ) (x : _root_.Formalism.BasicNotions.Loc.Om l), x ^ (l ^ m) = 1 →
      g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val := by
  intro l _
  haveI : ∀ i, HasEnoughRootsOfUnity (_root_.Formalism.BasicNotions.Loc.Om l) (l ^ i) := fun i => by
    unfold _root_.Formalism.BasicNotions.Loc.Om
    infer_instance
  let ρ : _root_.Formalism.BasicNotions.Loc.GQ l →* (_root_.Formalism.BasicNotions.Loc.Om l ≃+* _root_.Formalism.BasicNotions.Loc.Om l) :=
    { toFun := fun g => (g : _root_.Formalism.BasicNotions.Loc.Om l ≃+* _root_.Formalism.BasicNotions.Loc.Om l), map_one' := rfl, map_mul' := fun _ _ => rfl }
  exact ⟨(cyclotomicCharacter (_root_.Formalism.BasicNotions.Loc.Om l) l).comp ρ,
    fun g m x hx => cyclotomicCharacter.spec l (g : _root_.Formalism.BasicNotions.Loc.Om l ≃+* _root_.Formalism.BasicNotions.Loc.Om l) x hx⟩

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqDefiniteCompact
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory

theorem Jpq_zero_left_eq_neg_one (q : ℕ) : Formalism.UG.Jpq 0 q = -1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · exact i.elim0
  · exact i.elim0
  · exact j.elim0
  · simp [Formalism.UG.Jpq, Matrix.one_apply]

theorem isCompact_Upq_zero_left (q : ℕ) :
    IsCompact (Formalism.UG.Upq 0 q : Set (GL (Fin 0 ⊕ Fin q) ℂ)) := by
  have hc := Formalism.UG.P.isCompact_units_of_unitary (n := Fin 0 ⊕ Fin q)
    (T := {M | star M * M = 1})
    (isClosed_eq (continuous_star.mul continuous_id) continuous_const) (fun _ h => h)
  convert hc using 1
  ext g
  simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
  rw [Formalism.UG.P.mem_Upq_iff, Jpq_zero_left_eq_neg_one, Matrix.mul_neg, Matrix.mul_one,
    Matrix.neg_mul, neg_inj]

theorem compactSpace_UpqT_definite :
    ∀ N : ℕ, CompactSpace (UpqT N 0) ∧ CompactSpace (UpqT 0 N) := fun N =>
  ⟨(isCompact_iff_compactSpace.1 (Formalism.UG.P.indefinite_unitary_compact N) :
      CompactSpace (Formalism.UG.Upq N 0 : Set (GL (Fin N ⊕ Fin 0) ℂ))),
    (isCompact_iff_compactSpace.1 (isCompact_Upq_zero_left N) :
      CompactSpace (Formalism.UG.Upq 0 N : Set (GL (Fin 0 ⊕ Fin N) ℂ)))⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfForallXiPowDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.XiHaus
variable {l : ℕ} [Fact l.Prime]

theorem isDomain_Fl : IsDomain (Per.Fl l) :=
  PreTilt.isDomain ℂ_[l] Valued.v (Per.OC l) (PadicComplexInt.integers l) l

theorem coeff_pow_pow (x : Per.Fl l) (k : ℕ) :
    PreTilt.coeff k (x ^ l ^ k) = PreTilt.coeff 0 x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, map_pow, PreTilt.coeff_pow_p, ih]

theorem xi_coeff_zero (e : Per.Fl l) :
    (xi e).coeff 0 = ∑ i ∈ Finset.range l, ((frobeniusEquiv (Per.Fl l) l).symm e) ^ i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← WittVector.constantCoeff_apply, xi, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem root_pow (e : Per.Fl l) : ((frobeniusEquiv (Per.Fl l) l).symm e) ^ l = e := by
  simp

theorem xi_coeff_zero_ne {e : Per.Fl l} (he : IsEps e) : (xi e).coeff 0 ≠ 0 := by
  intro h
  have h1 := geom_sum_mul ((frobeniusEquiv (Per.Fl l) l).symm e) l
  rw [← xi_coeff_zero, h, zero_mul, root_pow, eq_comm, sub_eq_zero] at h1
  exact he.2 (by rw [h1, map_one, map_one])

theorem eq_zero_of_dvd {e : Per.Fl l} (he : IsEps e) (b : Per.Fl l)
    (hb : ∀ n : ℕ, ((xi e).coeff 0) ^ n ∣ b) : b = 0 := by
  set u := (frobeniusEquiv (Per.Fl l) l).symm e with hu
  have hy : (u - 1) ∣ (xi e).coeff 0 := by
    rw [xi_coeff_zero, ← hu]
    have : ∑ i ∈ Finset.range l, u ^ i = ∑ i ∈ Finset.range l, (u ^ i - 1 ^ i) := by
      simp [Finset.sum_sub_distrib]
    rw [this]
    exact Finset.dvd_sum fun i _ => sub_dvd_pow_sub_pow u 1 i
  have h0 : PreTilt.coeff 0 ((u - 1) ^ l) = 0 := by
    rw [sub_pow_char, hu, root_pow, one_pow, map_sub, ← PreTilt.mk_untilt_eq_coeff_zero, he.1,
      map_one, map_one, sub_self]
  refine Perfection.ext fun k => ?_
  obtain ⟨c, hc⟩ := (pow_dvd_pow_of_dvd hy (l * l ^ k)).trans (hb _)
  change PreTilt.coeff k b = PreTilt.coeff k 0
  rw [hc, map_mul, pow_mul, coeff_pow_pow, h0, zero_mul, map_zero]

theorem xi_sat {e : Per.Fl l} (he : IsEps e) (n : ℕ) (a : Per.Ainf l)
    (h : xi e ^ n ∣ (l : Per.Ainf l) * a) : xi e ^ n ∣ a := by
  have := isDomain_Fl (l := l)
  obtain ⟨c, hc⟩ := h
  have h1 := congrArg WittVector.constantCoeff hc
  rw [map_mul, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, map_pow,
    WittVector.constantCoeff_apply, WittVector.constantCoeff_apply] at h1
  have h2 : c.coeff 0 = 0 :=
    (mul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ (xi_coeff_zero_ne he))
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.1
    ((WittVector.mem_span_p_iff_coeff_zero_eq_zero c).2 h2)
  refine ⟨d, mul_left_cancel₀ (WittVector.p_nonzero l (Per.Fl l)) ?_⟩
  rw [hc]; ring

end GlobalTheory.MemLoc.XiHaus

namespace GlobalTheory.MemLoc

open XiHaus in
theorem eq_zero_of_forall_xi_pow_dvd (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : IsEps e)
    (a : Per.Ainf l) (ha : ∀ n : ℕ, xi e ^ n ∣ a) : a = 0 := by
  have key : ∀ (k : ℕ) (a : Per.Ainf l), (∀ n : ℕ, xi e ^ n ∣ a) → (l : Per.Ainf l) ^ k ∣ a := by
    intro k
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a ha
      have h0 : a.coeff 0 = 0 := eq_zero_of_dvd he _ fun n => by
        have := map_dvd WittVector.constantCoeff (ha n)
        rwa [map_pow, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply] at this
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.1
        ((WittVector.mem_span_p_iff_coeff_zero_eq_zero a).2 h0)
      rw [pow_succ']
      exact mul_dvd_mul_left _ (ih d fun n => xi_sat he n d (ha n))
  refine IsHausdorff.haus (I := Ideal.span {(l : Per.Ainf l)}) inferInstance a fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact key k a ha
end GlobalTheory.MemLoc
end
