module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumTaylorCoordinateSpaceEntire
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumTaylorCoordinateSpaceEntire
namespace GlobalTheory.EntireTaylor

theorem summable_of_entire {σ : Type*} [Fintype σ] [DecidableEq σ] {f : (σ → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (c : (σ →₀ ℕ) → ℂ)
    (hc : ∀ α, (∏ j, ((α j).factorial : ℂ)) * c α = pderivIter α f 0) (w : σ → ℂ) :
    Summable fun α : σ →₀ ℕ => c α * ∏ j, w j ^ α j := by
  obtain ⟨R, hRdef⟩ : ∃ R : σ → ℝ, R = fun j => 2 * ‖w j‖ + 1 := ⟨_, rfl⟩
  have hR : ∀ j, 0 < R j := fun j => by rw [hRdef]; positivity
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ Set.univ.pi (fun j => Metric.closedBall (0 : ℂ) (R j)), ‖f z‖ ≤ M :=
    (isCompact_univ_pi fun j => isCompact_closedBall (0 : ℂ) (R j)).exists_bound_of_continuousOn
      hf.continuous.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _)
    (hM 0 (Set.mem_univ_pi.mpr fun j => Metric.mem_closedBall.mpr (by simpa using (hR j).le)))
  have hw : ∀ j, ‖w j‖ / R j ≤ 1 / 2 := fun j => by
    rw [div_le_iff₀ (hR j), hRdef]
    linarith [norm_nonneg (w j)]
  have key : ∀ α : σ →₀ ℕ, ‖c α * ∏ j, w j ^ α j‖ ≤ M * ∏ j, (1 / 2 : ℝ) ^ α j := by
    intro α
    have hP : (∏ j, ((α j).factorial : ℂ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast Nat.factorial_ne_zero _
    have hcα : c α = pderivIter α f 0 / ∏ j, ((α j).factorial : ℂ) := by
      rw [← hc α, mul_div_cancel_left₀ _ hP]
    have hnormP : ‖∏ j, ((α j).factorial : ℂ)‖ = ∏ j, ((α j).factorial : ℝ) := by
      rw [norm_prod]
      simp
    have hPpos : 0 < ∏ j, ((α j).factorial : ℝ) :=
      Finset.prod_pos fun j _ => by exact_mod_cast Nat.factorial_pos _
    have hC : ‖pderivIter α f 0‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, R k ^ α k :=
      GlobalTheory.norm_pderivIter_le_of_differentiable α (fun k => (hR k).le) (fun k _ => hR k) hf
        fun z hz => hM z (Set.mem_univ_pi.mpr fun j => Metric.mem_closedBall.mpr (by
          have h := hz j
          simp only [Pi.zero_apply, sub_zero] at h
          rw [dist_zero_right]
          exact h.le))
    have h1 : ‖c α‖ ≤ M / ∏ j, R j ^ α j := by
      rw [hcα, norm_div, hnormP, div_le_iff₀ hPpos]
      calc ‖pderivIter α f 0‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, R k ^ α k := hC
        _ = (M / ∏ j, R j ^ α j) * ∏ j, ((α j).factorial : ℝ) := by ring
    calc ‖c α * ∏ j, w j ^ α j‖ = ‖c α‖ * ∏ j, ‖w j‖ ^ α j := by
          rw [norm_mul, norm_prod]
          simp [norm_pow]
      _ ≤ (M / ∏ j, R j ^ α j) * ∏ j, ‖w j‖ ^ α j :=
          mul_le_mul_of_nonneg_right h1 (Finset.prod_nonneg fun j _ => by positivity)
      _ = M * ∏ j, (‖w j‖ / R j) ^ α j := by
          simp only [div_pow, Finset.prod_div_distrib]
          ring
      _ ≤ M * ∏ j, (1 / 2 : ℝ) ^ α j :=
          mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod₀ (fun j _ => by have := (hR j).le; positivity)
              fun j _ => pow_le_pow_left₀ (by have := (hR j).le; positivity) (hw j) _) hM0
  exact Summable.of_norm_bounded
    ((GlobalTheory.ProdThetaConj.summable_prod_half_pow (σ := σ)).mul_left M) key

end GlobalTheory.EntireTaylor

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

theorem GlobalTheory.EntireTaylor.hasSum_taylor_mono : ∀ (D : D7) (N N' : ℕ) (F : VC D N N' → ℂ), Differentiable ℂ F → ∀ z : VC D N N', HasSum (fun α : Mono D N N' => Formalism.MainNotions.TaylorLogMetric.taylor D F α * mono D α z) (F z) := by
  intro D N N' F hF z
  have hcd : Differentiable ℂ (fun w => F (GlobalTheory.GaussCauchy.curry D N N' w)) := fun w =>
    (hF _).comp w (LinearMap.toContinuousLinearMap (GlobalTheory.GaussCauchy.curry D N N')).differentiableAt
  have hS := GlobalTheory.EntireTaylor.summable_of_entire hcd (fun α => Formalism.MainNotions.TaylorLogMetric.taylor D F α)
    (fun α => by
      rw [← GlobalTheory.GaussCauchy.factorial_mul_taylor D N N' F hF α, Finsupp.prod_fintype]
      intro i
      simp)
    (fun k => z k.1 k.2.1 k.2.2)
  have hmono : ∀ α : Mono D N N', mono D α z = ∏ k, z k.1 k.2.1 k.2.2 ^ α k := fun α => by
    show (α.prod fun k n => z k.1 k.2.1 k.2.2 ^ n) = _
    rw [Finsupp.prod_fintype]
    intro i
    simp
  have hS' : Summable fun α : Mono D N N' => Formalism.MainNotions.TaylorLogMetric.taylor D F α * mono D α z := by
    simpa only [hmono] using hS
  rw [← GlobalTheory.ProdThetaConj.tsum_taylor_mono D hF z]
  exact hS'.hasSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumTaylorCoordinateSpaceEntireStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_taylor_coordinateSpace_entire : ∀ (D : D7) (N N' : ℕ) (F : VC D N N' → ℂ), Differentiable ℂ F → ∀ z : VC D N N', HasSum (fun α : Mono D N N' => taylor D F α * mono D α z) (F z) := by
  first | exact @GlobalTheory.EntireTaylor.hasSum_taylor_mono | exact GlobalTheory.EntireTaylor.hasSum_taylor_mono | (intros; apply GlobalTheory.EntireTaylor.hasSum_taylor_mono <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SphericalPair
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.NormSum.VacInt

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ}

theorem sd_std (D : D7) (N : ℕ) : SD D (stdL D N) := by
  obtain ⟨Lt, h, h1, -⟩ := exists_lattice_of_adelic_point D N
  exact h1 ▸ (h 1).2

theorem vac_mem_TT (hg : admG1 D) (crv : Crv D cc δ) (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) :
    e0 ∈ TT D (tor0 D cc δ) a d := by
  refine ⟨he.1, 1, one_pos, fun x hx => ?_⟩
  rw [one_smul, (GlobalTheory.ThetaLine.theta_line D hg cc δ crv a d _ (Or.inr ⟨_, _, sd_std D a, sd_std D d, rfl⟩)).2.1 x hx]
  exact funext (he.2 x hx)

theorem om_vac_norm (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) (hT : e0 ∈ TT D (tor0 D cc δ) a d)
    (W : WeilO D cc δ a d e0) {k : GA D a} {k' : GA D d} (hk : k ∈ intG D a) (hk' : k' ∈ intG D d) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om k k' e0 = c • e0 := by
  obtain ⟨x, x', -, -, h⟩ := om_vac_of_mem he hT W (AdLattice.intG_of_mem D a k hk) (AdLattice.intG_of_mem D d k' hk')
  refine ⟨_, ?_, h⟩
  simp [W.chV.unitary, W.chV'.unitary]

theorem om_vac_fix (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) (hT : e0 ∈ TT D (tor0 D cc δ) a d)
    (W : WeilO D cc δ a d e0) (hu : ∀ u, IntU D u → W.chV'.f u = 1) {k : GA D a} (hk : k ∈ intG D a) :
    W.Om k 1 e0 = e0 := by
  obtain ⟨x, hx, h⟩ := om_vac_left he hT W (AdLattice.intG_of_mem D a k hk)
  rw [h, hu x hx]
  simp

def sphericalPair (hg : admG1 D) (crv : Crv D cc δ) (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (had : a ≤ d) (hd : Even d)
    (vac : oddE0 D cc δ t0 a d e0) (W : WeilO D cc δ a d e0) (n : D.what₂.Tau → ℕ)
    (wt : ∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - (d : ℤ)) (hu : ∀ u, IntU D u → W.chV'.f u = 1) :
    Pair D cc δ t0 1 :=
  Pair.ofVacuum crv pt0 had hd vac W n wt (fun _ hk => om_vac_fix vac.1 (vac_mem_TT hg crv vac.1) W hu hk)
    (fun _ hj => om_vac_norm vac.1 (vac_mem_TT hg crv vac.1) W (one_mem _) hj)

theorem vacuum_eigen : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (a d : ℕ), ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d), ∀ W : WeilO D cc δ a d e0,
      e0 ∈ TT D (tor0 D cc δ) a d ∧
      (∀ k ∈ intG D a, ∀ k' ∈ intG D d, ∃ x x' : (AE D)ˣ, IntU D x ∧ IntU D x' ∧
        W.Om k k' e0 = ((W.chV.f x' ^ W.ep * W.chV'.f x ^ W.ep' : ℂˣ) : ℂ) • e0) ∧
      (∀ k ∈ intG D a, ∀ k' ∈ intG D d, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om k k' e0 = c • e0) ∧
      ((∀ u, IntU D u → W.chV'.f u = 1) → ∀ k ∈ intG D a, W.Om k 1 e0 = e0) ∧
      ((∀ u, IntU D u → W.chV'.f u = 1) → a ≤ d → Even d → ∀ t0 : ℂ, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
        oddE0 D cc δ t0 a d e0 → ∀ n : D.what₂.Tau → ℕ, (∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - (d : ℤ)) →
        ∃ P : Pair D cc δ t0 1, P.a = a ∧ P.d = d ∧ HEq P.e0 e0 ∧ HEq P.W W ∧ P.n = n ∧ P.F = P.e0 ∧ P.F ≠ 0 ∧
          P.J = intG D P.d) := by
  intro D hg cc δ crv a d e0 he W
  have hT := vac_mem_TT hg crv he
  exact ⟨hT, fun k hk k' hk' => om_vac_of_mem he hT W (AdLattice.intG_of_mem D a k hk) (AdLattice.intG_of_mem D d k' hk'),
    fun _ hk _ hk' => om_vac_norm he hT W hk hk', fun hu _ hk => om_vac_fix he hT W hu hk,
    fun hu had hd t0 pt0 vac n wt => ⟨sphericalPair hg crv pt0 had hd vac W n wt hu, rfl, rfl, HEq.rfl, HEq.rfl, rfl, rfl,
      W.nz, rfl⟩⟩

end GlobalTheory.NormSum.VacInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicProperties
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

variable {Λ : AddSubgroup ℂ}

private lemma sgStar_add_lattice_eq_mul_exp (hΛ : _root_.GlobalTheory.EvenTheta.IsLat Λ) {a : ℂ} (ha : a ∈ Λ)
    (z : ℂ) :
    _root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ (z + a) = (if a / 2 ∈ Λ then 1 else -1) * _root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ z *
      Complex.exp (↑Real.pi * z * (starRingEnd ℂ) a / ↑(_root_.Formalism.MainNotions.TaylorLogMetric.area Λ) +
        ↑Real.pi * a * (starRingEnd ℂ) a / (2 * ↑(_root_.Formalism.MainNotions.TaylorLogMetric.area Λ))) := by
  have h := hΛ.sg_law ha z
  unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1 at h
  rw [← h, mul_assoc, ← Complex.exp_add]
  ring_nf <;> simp

private lemma mul_exp_eq_one_of_exp_relation {ε s x y w k : ℂ} (hs : s ≠ 0)
    (h : -1 * s * Complex.exp x = ε * (-1 * s * Complex.exp y) * Complex.exp w)
    (hk : y + w = x + k) : ε * Complex.exp k = 1 := by
  have h' : -1 * s * Complex.exp x = ε * (-1 * s * (Complex.exp x * Complex.exp k)) := by
    rw [← Complex.exp_add, ← hk, Complex.exp_add]
    linear_combination h
  have hprod : (s * Complex.exp x) * (ε * Complex.exp k - 1) = 0 := by
    linear_combination h'
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact absurd h0 (mul_ne_zero hs (Complex.exp_ne_zero x))
  · exact sub_eq_zero.1 h0

private lemma mul_mul_exp_eq_of_mul_exp_eq_one {ε k a s q : ℂ} (h : ε * Complex.exp k = 1) (hs : s = k + q) :
    ε * (a * Complex.exp s) = a * Complex.exp q := by
  rw [hs, Complex.exp_add]
  linear_combination (a * Complex.exp q) * h

theorem _root_.GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties : ∀ Λ : AddSubgroup ℂ, _root_.GlobalTheory.EvenTheta.IsLat Λ →
    ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → Differentiable ℂ (_root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀) ∧ _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ 0 = 1 ∧
    (∀ z, _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ (-z) = _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z) ∧
    (∀ z, _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z ^ 2 = _root_.GlobalTheory.EvenTheta.sqTh Λ t₀ z) ∧
    (∀ z, _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z = 0 ↔ z + t₀ ∈ Λ) ∧
    ∀ ω ∈ Λ, ω / 2 + t₀ ∉ Λ → ∀ z, _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ ω (_root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀) z = _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z := by
  intro Λ hΛ t ht h2t
  have hσt : _root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ t ≠ 0 := fun h => ht ((hΛ.sg_eq_zero t).1 h)
  have hhalf : ¬ (2 * t / 2 ∈ Λ) := by rwa [mul_div_cancel_left₀ t two_ne_zero]
  have hU0 : _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) 0 ≠ 0 := by
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1
    rw [zero_add]
    exact mul_ne_zero hσt (Complex.exp_ne_zero _)
  have hopp : ∀ y, _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ (-t) (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) y = -_root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) y := by
    intro y
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1
    rw [show y + t = y + -t + 2 * t by ring, sgStar_add_lattice_eq_mul_exp hΛ h2t, if_neg hhalf]
    simp only [mul_assoc, ← Complex.exp_add, map_neg, map_mul, map_ofNat]
    ring_nf
  have heven : ∀ z, _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) (-z) = _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) z := by
    intro z
    have h := hopp z
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1 at h ⊢
    rw [show -z + t = -(z + -t) by ring, hΛ.sg_neg]
    simp only [map_neg] at h ⊢
    ring_nf at h ⊢
    linear_combination -h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hd := hΛ.differentiable
    unfold _root_.Formalism.MainNotions.GL3Theta.th0 _root_.Formalism.MainNotions.TaylorLogMetric.U1
    fun_prop
  · unfold _root_.Formalism.MainNotions.GL3Theta.th0
    exact div_self hU0
  · intro z
    unfold _root_.Formalism.MainNotions.GL3Theta.th0
    rw [heven]
  · intro z
    have h := hΛ.sqTh_mul ht z
    rw [hopp, hopp] at h
    unfold _root_.Formalism.MainNotions.GL3Theta.th0
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hU0)]
    linear_combination h
  · intro z
    unfold _root_.Formalism.MainNotions.GL3Theta.th0
    rw [div_eq_zero_iff, or_iff_left hU0]
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1
    rw [mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), hΛ.sg_eq_zero]
  · intro ω hω hωt z
    have hsum : ¬ ((ω + 2 * t) / 2 ∈ Λ) := by
      rwa [show (ω + 2 * t) / 2 = ω / 2 + t by ring]
    have h1 := sgStar_add_lattice_eq_mul_exp hΛ (add_mem hω h2t) t
    have h2 := sgStar_add_lattice_eq_mul_exp hΛ hω (t + 2 * t)
    have h3 := sgStar_add_lattice_eq_mul_exp hΛ h2t t
    rw [if_neg hsum] at h1
    rw [if_neg hhalf] at h3
    rw [show t + 2 * t + ω = t + (ω + 2 * t) by ring, h1, h3] at h2
    have hε := mul_exp_eq_one_of_exp_relation
      (k := (↑Real.pi * t * (starRingEnd ℂ) ω - ↑Real.pi * ω * (starRingEnd ℂ) t) /
        ↑(_root_.Formalism.MainNotions.TaylorLogMetric.area Λ)) hσt h2 (by simp only [map_add (f := _), map_mul, map_ofNat]; ring)
    unfold _root_.Formalism.MainNotions.GL3Theta.th0 _root_.Formalism.MainNotions.TaylorLogMetric.U1
    beta_reduce
    rw [show z + ω + t = z + t + ω by ring, sgStar_add_lattice_eq_mul_exp hΛ hω, div_mul_eq_mul_div]
    congr 1
    simp only [mul_assoc, ← Complex.exp_add]
    exact mul_mul_exp_eq_of_mul_exp_eq_one hε (by ring)

end GlobalTheory.EvenTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicPropertiesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.th0_zero_even_sq_zeros_and_periodicity : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → Differentiable ℂ (GL3Theta.th0 Λ t₀) ∧ GL3Theta.th0 Λ t₀ 0 = 1 ∧ (∀ z, GL3Theta.th0 Λ t₀ (-z) = GL3Theta.th0 Λ t₀ z) ∧ (∀ z, GL3Theta.th0 Λ t₀ z ^ 2 = sqTh Λ t₀ z) ∧ (∀ z, GL3Theta.th0 Λ t₀ z = 0 ↔ z + t₀ ∈ Λ) ∧ ∀ ω ∈ Λ, ω / 2 + t₀ ∉ Λ → ∀ z, U1 Λ ω (GL3Theta.th0 Λ t₀) z = GL3Theta.th0 Λ t₀ z := by
  first | exact @GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties | exact GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties | (intros; apply GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesSupNormMulPadicComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesSupNormMulPadicComplex
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem exists_least_argmax_of_tendsto_zero (b : ℕ → ℝ) (h0 : ∀ i, 0 ≤ b i)
    (hb : Filter.Tendsto b Filter.atTop (nhds 0)) :
    ∃ i₀, (∀ i, b i ≤ b i₀) ∧ ∀ i < i₀, b i < b i₀ := by
  have hex : ∃ i, ∀ j, b j ≤ b i := by
    by_cases hpos : ∃ k, 0 < b k
    · obtain ⟨k, hk⟩ := hpos
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hb.eventually (gt_mem_nhds hk))
      obtain ⟨i, hi, hmax⟩ := (Finset.range (max N (k + 1))).exists_max_image b
        ⟨k, Finset.mem_range.2 (lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _))⟩
      refine ⟨i, fun j => ?_⟩
      by_cases hj : j < max N (k + 1)
      · exact hmax j (Finset.mem_range.2 hj)
      · have hjN : N ≤ j := le_trans (le_max_left _ _) (not_lt.1 hj)
        have hkmem : k ∈ Finset.range (max N (k + 1)) :=
          Finset.mem_range.2 (lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _))
        exact (hN j hjN).le.trans (hmax k hkmem)
    · push Not at hpos
      exact ⟨0, fun j => (hpos j).trans (h0 0)⟩
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, fun i hi => ?_⟩
  have hle : b i ≤ b (Nat.find hex) := Nat.find_spec hex i
  refine lt_of_le_of_ne hle fun heq => Nat.find_min hex hi ?_
  intro j
  rw [heq]
  exact Nat.find_spec hex j

theorem BddSer.tendsto_weighted {K : Type*} [NormedField K] {f : PowerSeries K} (hf : BddSer f)
    {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    Filter.Tendsto (fun i => ‖PowerSeries.coeff i f‖ * ρ ^ i) Filter.atTop (nhds 0) := by
  obtain ⟨B, hB⟩ := hf
  have hlim : Filter.Tendsto (fun i : ℕ => B * ρ ^ i) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).const_mul B
  exact squeeze_zero (fun i => by positivity)
    (fun i => mul_le_mul_of_nonneg_right (hB i) (pow_nonneg h0.le i)) hlim

private lemma norm_finset_sum_lt_of_ultrametric {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*}
    (s : Finset ι) (x : ι → K) {D : ℝ} (hD : 0 < D) (hx : ∀ p ∈ s, ‖x p‖ < D) :
    ‖∑ p ∈ s, x p‖ < D := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hD
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · exact hx a (Finset.mem_insert_self a s)
    · exact ih fun p hp => hx p (Finset.mem_insert_of_mem hp)

theorem norm_coeff_mul_weighted_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    (f g : PowerSeries K) (c : ℝ) (hf : BddSer f) (hg : BddSer g)
    (hc : ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ c) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) (i j : ℕ) :
    (‖PowerSeries.coeff i f‖ * ρ ^ i) * (‖PowerSeries.coeff j g‖ * ρ ^ j) ≤ c := by
  set A : ℕ → ℝ := fun k => ‖PowerSeries.coeff k f‖ * ρ ^ k with hAdef
  set B : ℕ → ℝ := fun k => ‖PowerSeries.coeff k g‖ * ρ ^ k with hBdef
  have hA0 : ∀ k, 0 ≤ A k := fun k => by positivity
  have hB0 : ∀ k, 0 ≤ B k := fun k => by positivity
  obtain ⟨i₀, hAi, hAlt⟩ := exists_least_argmax_of_tendsto_zero A hA0 (hf.tendsto_weighted h0 h1)
  obtain ⟨j₀, hBj, hBlt⟩ := exists_least_argmax_of_tendsto_zero B hB0 (hg.tendsto_weighted h0 h1)
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0)
  have hstep : A i * B j ≤ A i₀ * B j₀ := mul_le_mul (hAi i) (hBj j) (hB0 j) (hA0 i₀)
  change A i * B j ≤ c
  refine hstep.trans ?_
  rcases (mul_nonneg (hA0 i₀) (hB0 j₀)).eq_or_lt with hz | hpos
  · rw [← hz]; exact hc0
  have hApos : 0 < A i₀ := lt_of_le_of_ne (hA0 i₀) fun h => by rw [← h, zero_mul] at hpos; exact lt_irrefl 0 hpos
  have hBpos : 0 < B j₀ := lt_of_le_of_ne (hB0 j₀) fun h => by rw [← h, mul_zero] at hpos; exact lt_irrefl 0 hpos
  set n := i₀ + j₀ with hn
  have hρn : 0 < ρ ^ n := pow_pos h0 n
  have hterm : ∀ p : ℕ × ℕ, p.1 + p.2 = n →
      A p.1 * B p.2 = ‖PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g‖ * ρ ^ n := by
    intro p hp
    rw [← hp, norm_mul, pow_add]
    simp only [hAdef, hBdef]
    ring
  set D := PowerSeries.coeff i₀ f * PowerSeries.coeff j₀ g with hDdef
  have hDA : A i₀ * B j₀ = ‖D‖ * ρ ^ n := hterm (i₀, j₀) rfl
  have hDpos : 0 < ‖D‖ := by
    have : 0 < ‖D‖ * ρ ^ n := hDA ▸ hpos
    exact pos_of_mul_pos_left this hρn.le
  have hmem : (i₀, j₀) ∈ Finset.HasAntidiagonal.antidiagonal n := Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
  have hrest : ‖∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀),
      PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g‖ < ‖D‖ := by
    refine norm_finset_sum_lt_of_ultrametric _ _ hDpos fun p hp => ?_
    obtain ⟨hne, hp⟩ := Finset.mem_erase.1 hp
    have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    have hlt : A p.1 * B p.2 < A i₀ * B j₀ := by
      rcases lt_trichotomy p.1 i₀ with h | h | h
      · calc A p.1 * B p.2 ≤ A p.1 * B j₀ := mul_le_mul_of_nonneg_left (hBj _) (hA0 _)
          _ < A i₀ * B j₀ := mul_lt_mul_of_pos_right (hAlt _ h) hBpos
      · exfalso
        apply hne
        ext
        · exact h
        · simp only; omega
      · have h2 : p.2 < j₀ := by omega
        calc A p.1 * B p.2 ≤ A i₀ * B p.2 := mul_le_mul_of_nonneg_right (hAi _) (hB0 _)
          _ < A i₀ * B j₀ := mul_lt_mul_of_pos_left (hBlt _ h2) hApos
    rw [hterm p hsum, hDA] at hlt
    exact lt_of_mul_lt_mul_right hlt hρn.le
  have hcoeff : PowerSeries.coeff n (f * g) =
      D + ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀),
        PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g := by
    rw [PowerSeries.coeff_mul, ← Finset.add_sum_erase _ _ hmem]
  have hDle : ‖D‖ ≤ ‖PowerSeries.coeff n (f * g)‖ := by
    by_contra hcon
    push Not at hcon
    have hD : D = PowerSeries.coeff n (f * g) + -(∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀),
        PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g) := by
      rw [hcoeff]; ring
    have := IsUltrametricDist.norm_add_le_max (PowerSeries.coeff n (f * g))
      (-(∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀),
        PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g))
    rw [← hD, norm_neg] at this
    exact lt_irrefl _ (lt_of_le_of_lt this (max_lt hcon hrest))
  rw [hDA]
  calc ‖D‖ * ρ ^ n ≤ c * ρ ^ n := mul_le_mul_of_nonneg_right (hDle.trans (hc n)) hρn.le
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ h0.le h1.le) hc0
    _ = c := mul_one c

theorem norm_coeff_mul_norm_coeff_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    (f g : PowerSeries K) (c : ℝ) (hf : BddSer f) (hg : BddSer g)
    (hc : ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ c) (i j : ℕ) :
    ‖PowerSeries.coeff i f‖ * ‖PowerSeries.coeff j g‖ ≤ c := by
  have ht : Filter.Tendsto
      (fun ρ : ℝ => (‖PowerSeries.coeff i f‖ * ρ ^ i) * (‖PowerSeries.coeff j g‖ * ρ ^ j))
      (nhdsWithin 1 (Set.Iio 1))
      (nhds ((‖PowerSeries.coeff i f‖ * 1 ^ i) * (‖PowerSeries.coeff j g‖ * 1 ^ j))) :=
    ((Continuous.tendsto (by fun_prop) 1).mono_left nhdsWithin_le_nhds)
  have hev : ∀ᶠ ρ in nhdsWithin (1 : ℝ) (Set.Iio 1),
      (‖PowerSeries.coeff i f‖ * ρ ^ i) * (‖PowerSeries.coeff j g‖ * ρ ^ j) ≤ c := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ
    exact norm_coeff_mul_weighted_le f g c hf hg hc hρ.1 hρ.2 i j
  simpa using le_of_tendsto ht hev

theorem sup_norm_mul_padicComplex : ∀ (p : ℕ) [Fact p.Prime] (f g : PowerSeries ℂ_[p]) (c : ℝ),
    BddSer f → BddSer g → (∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ c) →
      ∀ i j, ‖PowerSeries.coeff i f‖ * ‖PowerSeries.coeff j g‖ ≤ c := by
  intro p _ f g c hf hg hc i j
  exact norm_coeff_mul_norm_coeff_le f g c hf hg hc i j

end GlobalTheory.EvenTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesSupNormMulPadicComplexStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeries_supNorm_mul_padicComplex : ∀ (p : ℕ) [Fact p.Prime] (f g : PowerSeries ℂ_[p]) (c : ℝ), BddSer f → BddSer g → (∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ c) → ∀ i j, ‖PowerSeries.coeff i f‖ * ‖PowerSeries.coeff j g‖ ≤ c := by
  first | exact @GlobalTheory.EvenTheta.sup_norm_mul_padicComplex | exact GlobalTheory.EvenTheta.sup_norm_mul_padicComplex | (intros; apply GlobalTheory.EvenTheta.sup_norm_mul_padicComplex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceOneIntegerConjDiffPrimeTo
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceOneIntegerConjDiffPrimeTo
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TraceOne

theorem exists_of_sq (D : D7) (q n : ℕ) (hn : n % 4 = 3) (hc : Nat.Coprime q n) (b : D.host.E)
    (hb : b ^ 2 = -(n : D.host.E)) :
    ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧
      ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (q : 𝓞 D.host.E) ∈ P → w - sgO D w ∉ P := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n + 1 = 4 * m := ⟨(n + 1) / 4, by omega⟩
  have hm' : (n : D.host.E) + 1 = 4 * (m : D.host.E) := by exact_mod_cast hm
  have hint : IsIntegral ℤ ((1 + b) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), ?_, ?_⟩
    · monicity!
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, map_natCast]
      linear_combination (1 / 4 : D.host.E) * hb - (1 / 4 : D.host.E) * hm'
  have hconj : D.host.conj b = -b := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ (D.host.conj b) = starRingEnd ℂ (D.host.φ₀ b) :=
      D.host.conjE_apply D.host.φ₀ b
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h2 : (D.host.φ₀ b) ^ 2 = (Complex.I * (Real.sqrt n : ℂ)) ^ 2 := by
      rw [← map_pow, hb, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
        Real.sq_sqrt hn0]
      simp
    rw [h1, map_neg]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h <;> rw [h] <;> simp
  have hcw : D.host.conj ((1 + b) / 2) = (1 - b) / 2 := by
    rw [map_div₀, map_add (f := _), map_one, map_ofNat, hconj, sub_eq_add_neg]
  let w : 𝓞 D.host.E := ⟨(1 + b) / 2, hint⟩
  have hw : (w : D.host.E) = (1 + b) / 2 := rfl
  have hs : ((sgO D w : 𝓞 D.host.E) : D.host.E) = (1 - b) / 2 := by rw [sgO_coe, hw, hcw]
  refine ⟨w, ?_, fun P hP hq hmem => ?_⟩
  · apply RingOfIntegers.coe_injective
    rw [map_add (f := _), map_one]
    change (w : D.host.E) + ((sgO D w : 𝓞 D.host.E) : D.host.E) = 1
    rw [hw, hs]; ring
  · have hsq : (w - sgO D w) * -(w - sgO D w) = (n : 𝓞 D.host.E) := by
      apply RingOfIntegers.coe_injective
      rw [map_mul, map_neg, map_sub, map_natCast]
      change ((w : D.host.E) - ((sgO D w : 𝓞 D.host.E) : D.host.E)) *
        -((w : D.host.E) - ((sgO D w : 𝓞 D.host.E) : D.host.E)) = _
      rw [hw, hs]
      linear_combination (-1 : D.host.E) * hb
    have hnP : (n : 𝓞 D.host.E) ∈ P := hsq ▸ P.mul_mem_right _ hmem
    obtain ⟨u, v, huv⟩ : IsCoprime (q : 𝓞 D.host.E) (n : 𝓞 D.host.E) := hc.cast
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2
      (huv ▸ P.add_mem (P.mul_mem_left u hq) (P.mul_mem_left v hnP)))

theorem exists_trace_one : ∀ (D : D7) (q : ℕ), q.Prime → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧
    ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (q : 𝓞 D.host.E) ∈ P → w - sgO D w ∉ P := by
  intro D q hq
  obtain ⟨hq₁, hd, hq8, hd16, -⟩ := D.host.hyp
  by_cases h : q = D.host.d
  · refine exists_of_sq D q D.host.q (by omega) ((Nat.coprime_primes hq hq₁).2 (by omega))
      (D.host.sqq) D.host.sqq_sq
  · exact exists_of_sq D q D.host.d (by omega) ((Nat.coprime_primes hq hd).2 h)
      (D.host.sqd) (D.host.sqd_sq)

end GlobalTheory.TraceOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceOneIntegerConjDiffPrimeToStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_traceOne_integer_conj_diff_prime_to : ∀ (D : D7) (q : ℕ), q.Prime → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧ ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (q : 𝓞 D.host.E) ∈ P → w - sgO D w ∉ P := by
  first | exact @GlobalTheory.TraceOne.exists_trace_one | exact GlobalTheory.TraceOne.exists_trace_one | (intros; apply GlobalTheory.TraceOne.exists_trace_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvNegLogMvMul
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.ExpLogMv

open PowerSeries

theorem coeff_subst_range {K σ : Type*} [CommRing K] {G : MvPowerSeries σ K}
    (hG : MvPowerSeries.constantCoeff G = 0) (f : PowerSeries K) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (f.subst G) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
        coeff n f * MvPowerSeries.coeff α (G ^ n) := by
  rw [coeff_subst (HasSubst.of_constantCoeff_zero hG),
    finsum_eq_sum_of_support_subset (s := Finset.range ((α.sum fun _ k => k) + 1))]
  · rfl
  · intro k hk
    by_contra h
    apply hk
    have hlt : (α.sum fun _ k => k) < k := by simpa using h
    have h0 : MvPowerSeries.coeff α (G ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hG)
      exact_mod_cast hlt
    simp [h0]

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem expMv_eq_subst {G : MvPowerSeries σ ℂ_[p]} (hG : MvPowerSeries.constantCoeff G = 0) :
    expMv G = (exp ℂ_[p]).subst G := by
  ext α
  rw [coeff_subst_range hG]
  show expMv G α = _
  rw [expMv]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [div_eq_inv_mul]

theorem logMv_eq_subst {F : MvPowerSeries σ ℂ_[p]} (hF : MvPowerSeries.constantCoeff F = 1) :
    GL3Theta.logMv F = (log ℂ_[p]).subst (F - 1) := by
  have h1 : MvPowerSeries.constantCoeff (F - 1) = 0 := by simp [hF]
  ext α
  rw [coeff_subst_range h1]
  show GL3Theta.logMv F α = _
  rw [GL3Theta.logMv]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_log]
  split_ifs
  · simp
  · simp
    ring

theorem exp_neg_log_one_var (K : Type*) [Field K] [CharZero K] :
    (exp K).subst (-log K) * (1 + X : PowerSeries K) = 1 := by
  have h0 : constantCoeff (-log K) = 0 := by simp
  have hs := HasSubst.of_constantCoeff_zero' h0
  have e : (1 + X) * PowerSeries.derivative (log K) = 1 := by
    rw [derivative_log]
    ext n
    cases n with
    | zero => simp [add_mul]
    | succ n => simp [add_mul, coeff_succ_X_mul, coeff_one, pow_succ]
  refine derivative.ext ?_ ?_
  · rw [Derivation.leibniz, derivative_subst hs, derivative_exp, map_neg, derivative_one, map_add (f := _),
      derivative_one, derivative_X]
    simp only [smul_eq_mul]
    linear_combination (-(exp K).subst (-log K)) * e
  · have : constantCoeff ((exp K).subst (-log K) : PowerSeries K) = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hs, finsum_eq_single _ 0]
      · simp
      · intro k hk
        simp [hk]
    simp [this]

theorem expMv_neg_logMv_mul : ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (F : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff F = 1 → MvPowerSeries.constantCoeff (GL3Theta.logMv F) = 0 ∧ expMv (-GL3Theta.logMv F) * F = 1 := by
  intro p _ σ F hF
  have h1 : MvPowerSeries.constantCoeff (F - 1) = 0 := by simp [hF]
  have hs := HasSubst.of_constantCoeff_zero h1
  have h0 : MvPowerSeries.constantCoeff (GL3Theta.logMv F) = 0 := by
    rw [logMv_eq_subst hF]
    exact constantCoeff_subst_eq_zero h1 _ constantCoeff_log
  refine ⟨h0, ?_⟩
  have hl : HasSubst (-log ℂ_[p]) := HasSubst.of_constantCoeff_zero' (by simp)
  have e := congrArg (substAlgHom (R := ℂ_[p]) hs) (exp_neg_log_one_var ℂ_[p])
  have en : subst (F - 1) (-log ℂ_[p]) = -GL3Theta.logMv F := by
    rw [logMv_eq_subst hF, ← coe_substAlgHom hs, map_neg]
  rw [map_mul, map_add (f := _), map_one, substAlgHom_X, coe_substAlgHom, subst_comp_subst_apply hl hs,
    en, add_sub_cancel] at e
  rw [expMv_eq_subst (by rw [map_neg, h0, neg_zero])]
  exact e

end GlobalTheory.ExpLogMv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisDataExists
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaMemSum
namespace GlobalTheory.LatticeSumMembership

open Formalism.MainNotions.TaylorLogMetric

theorem La_mem_sum :
    ∀ (D : Formalism.BasicNotions.D7) (T : Formalism.MainNotions.TaylorLogMetric.Tor D) {N N' : ℕ}
      (L : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N → (Formalism.BasicNotions.D7.host D).E))
      (L' : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N' → (Formalism.BasicNotions.D7.host D).E)),
      ∀ y ∈ Formalism.MainNotions.TaylorLogMetric.La D T L L', ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) ((Formalism.BasicNotions.D7.host D).E)) (w : Fin r → ℂ),
        (∀ (j : Fin r), b j ∈ Formalism.MainNotions.TaylorLogMetric.YYl D L L') ∧ (∀ (j : Fin r), w j ∈ Formalism.MainNotions.TaylorLogMetric.Tor.abelian₂ T) ∧
          y = ∑ j : Fin r, w j • Formalism.MainNotions.TaylorLogMetric.embV D T (b j) := by
  intro D T N N' L L' y hy
  unfold Formalism.MainNotions.TaylorLogMetric.La at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    exact ⟨1, fun _ => A, fun _ => w, fun _ => hA, fun _ => hw, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, by simp⟩
  | add x z _ _ ihx ihz =>
    obtain ⟨r₁, b₁, w₁, hb₁, hw₁, rfl⟩ := ihx
    obtain ⟨r₂, b₂, w₂, hb₂, hw₂, rfl⟩ := ihz
    refine ⟨r₁ + r₂, Fin.append b₁ b₂, Fin.append w₁ w₂, ?_, ?_, ?_⟩
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa using hb₁ i
      · simpa using hb₂ i
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa using hw₁ i
      · simpa using hw₂ i
    · rw [Fin.sum_univ_add]
      simp
  | neg x _ ihx =>
    obtain ⟨r, b, w, hb, hw, rfl⟩ := ihx
    refine ⟨r, b, fun j => -w j, hb, fun j => T.abelian₂.neg_mem (hw j), ?_⟩
    simp [neg_smul, Finset.sum_neg_distrib]

end GlobalTheory.LatticeSumMembership
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisDataExists
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.GalExist

theorem exists_sum_of_mem_La (D : D7) (T : Tor D) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (y : VC D N N') (hy : y ∈ La D T L L') :
    ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (w : Fin r → ℂ),
      (∀ j, b j ∈ YYl D L L') ∧ (∀ j, w j ∈ T.abelian₂) ∧ y = ∑ j, w j • embV D T (b j) := by
  first
  | exact @_root_.GlobalTheory.LatticeSumMembership.La_mem_sum
  | exact _root_.GlobalTheory.LatticeSumMembership.La_mem_sum
  | (apply _root_.GlobalTheory.LatticeSumMembership.La_mem_sum <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeSumMembership.La_mem_sum <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeSumMembership.La_mem_sum <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeSumMembership.La_mem_sum ..)

theorem galEx_of_galStar (D : D7) (hS : galStar D) : galEx D := by
  intro cc δ hc M ρ hK hD hM N N' L L' _ _ x n hx hn
  obtain ⟨m, hm, hmx⟩ := hx
  obtain ⟨r, b, w, hb, hw, hsum⟩ := exists_sum_of_mem_La D _ L L' _ hmx
  obtain ⟨h1, -, -, -, -, h6, -⟩ := hS cc δ hc M ρ hK hD.2.1 hD.2.2
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hw' : ∀ j, w j ∈ lamOf D cc δ := hw
  have hmul : ∀ j, ((m * n : ℕ) : ℂ) * (w j / m / n) ∈ lamOf D cc δ := by
    intro j
    have : ((m * n : ℕ) : ℂ) * (w j / m / n) = w j := by push_cast; field_simp
    rw [this]; exact hw' j
  have hex : ∀ j, ∃ t', StarPt M ρ (lamOf D cc δ) (w j / m / n) t' := by
    intro j
    have hq : InRationalLattice (lamOf D cc δ) (w j / m / n) := ⟨m * n, Nat.mul_pos hm hn, hmul j⟩
    refine h1 _ hq ?_
    by_cases h : w j / m / n ∈ lamOf D cc δ
    · exact Or.inl h
    · exact Or.inr (hM _ hq h)
  choose t' ht' using hex
  refine ⟨∑ j, ((n : ℂ) * t' j) • embV D (torConj D (tor0 D cc δ) M ρ) (b j),
    ⟨r, b, fun j => w j / m, fun j => (n : ℂ) * t' j, hb, ?_, ?_, rfl, ?_⟩, m, hm, ?_⟩
  · intro j
    refine ⟨m, hm, ?_⟩
    have : (m : ℂ) * (w j / m) = w j := by field_simp
    rw [this]; exact hw j
  · have hx : x = (m : ℂ)⁻¹ • (m • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hm0, one_smul]
    rw [hx, hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, ← div_eq_inv_mul]
  · intro j
    have : (n : ℂ) * t' j / n = t' j := by field_simp
    show StarPt M ρ (lamOf D cc δ) (w j / m / n) ((n : ℂ) * t' j / n)
    rw [this]; exact ht' j
  · rw [Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    refine AddSubgroup.subset_closure ⟨((m * n : ℕ) : ℂ) * t' j, (h6 _ _ _ (ht' j)).1 (hmul j), b j, hb j, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    push_cast; ring

theorem galEx_all : ∀ D : D7, galEx D := fun D => galEx_of_galStar D (GlobalTheory.T.galStar_complexMultiplication_points D)

end GlobalTheory.GalExist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisDataExistsStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_data_exists : ∀ D : D7, galEx D := by
  first | exact @GlobalTheory.GalExist.galEx_all | exact GlobalTheory.GalExist.galEx_all | (intros; apply GlobalTheory.GalExist.galEx_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorTorsionTranslateEvenTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorTorsionTranslateEvenTheta
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenThetaTorsion

variable {Λ : AddSubgroup ℂ}

def phase (Λ : AddSubgroup ℂ) (x y : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * (y * (starRingEnd ℂ) x - x * (starRingEnd ℂ) y) / (2 * (area Λ : ℂ)))

theorem phase_ne_zero (x y : ℂ) : phase Λ x y ≠ 0 := Complex.exp_ne_zero _

theorem thetaTranslate_comp_eq_phase_mul_add (x y : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ x (U1 Λ y G) z = phase Λ x y * U1 Λ (x + y) G z := by
  simp only [U1, phase]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc]
  congr 2
  simp only [map_add (f := _)]
  ring

theorem rationalLatticePoint_add {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) : InRationalLattice Λ (x + y) := by
  obtain ⟨m, hm, hx⟩ := hx
  obtain ⟨n, hn, hy⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  have := Λ.add_mem (Λ.nsmul_mem hx n) (Λ.nsmul_mem hy m)
  convert this using 1
  simp only [nsmul_eq_mul]
  push_cast
  ring

theorem rationalLatticePoint_of_mem_lattice {x : ℂ} (hx : x ∈ Λ) : InRationalLattice Λ x := ⟨1, one_pos, by simpa using hx⟩

theorem phase_mem (h : IsLat Λ) {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) :
    phase Λ x y ∈ Qbar := by
  obtain ⟨m, hm, hx⟩ := hx
  obtain ⟨n, hn, hy⟩ := hy
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  obtain ⟨k, hk⟩ := GlobalTheory.exists_int_im_latticeForm L ((hL _).1 hy) ((hL _).1 hx)
  have hA := GlobalTheory.latticeArea_pos L
  rw [GlobalTheory.latticeForm, Complex.div_ofReal_im, div_eq_iff hA.ne', ← GlobalTheory.OddTheta.area_eq L Λ hL] at hk
  rw [← GlobalTheory.OddTheta.area_eq L Λ hL] at hA
  have hA' : (area Λ : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have e := Complex.sub_conj ((n : ℂ) * y * (starRingEnd ℂ) ((m : ℂ) * x))
  rw [hk] at e
  simp only [map_mul, map_natCast, Complex.conj_conj] at e
  push_cast at e
  have hp : phase Λ x y ^ (2 * m * n) = 1 := by
    rw [phase, ← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I k]
    congr 1
    push_cast
    field_simp
    linear_combination e
  rw [mem_algebraicClosure_iff]
  refine IsAlgebraic.of_pow (n := 2 * m * n) (by positivity) ?_
  rw [hp]
  exact isAlgebraic_one

theorem algEnt_const_mul {F : ℂ → ℂ} (hF : AlgEnt F) {κ : ℂ} (hκ : κ ∈ Qbar) :
    AlgEnt fun z => κ * F z := by
  refine ⟨hF.1.const_mul κ, fun n => ?_⟩
  have : coef1 (fun z => κ * F z) n = κ * coef1 F n := by
    rw [coef1, coef1, iteratedDeriv_const_mul_field, mul_div_assoc]
  rw [this]
  exact Qbar.mul_mem hκ (hF.2 n)

theorem thetaTranslate_evenTheta_eq_sigmaStar_translate (t x z : ℂ) : U1 Λ x (GL3Theta.th0 Λ t) z =
    (phase Λ x t / U1 Λ t (sgStar Λ) 0) * U1 Λ (x + t) (sgStar Λ) z := by
  rw [div_mul_eq_mul_div, ← thetaTranslate_comp_eq_phase_mul_add]
  simp only [U1, GL3Theta.th0]
  ring

theorem sigmaStarTranslate_add_lattice_sign_phase (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (y z : ℂ) :
    U1 Λ (y + ω) (sgStar Λ) z =
      ((if ω / 2 ∈ Λ then 1 else -1) / phase Λ y ω) * U1 Λ y (sgStar Λ) z := by
  have e := thetaTranslate_comp_eq_phase_mul_add (Λ := Λ) y ω (sgStar Λ) z
  rw [funext (h.sg_law hω)] at e
  rw [div_mul_eq_mul_div, eq_div_iff (phase_ne_zero _ _), mul_comm, ← e]
  simp only [U1]
  ring

theorem algebraicTaylor_torsionTranslate_evenTheta_alt : ∀ Λ : AddSubgroup ℂ, IsLat Λ → (∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (sgStar Λ))) → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (GL3Theta.th0 Λ t₀)) ∧ ∀ ω ∈ Λ, ∃ κ ∈ Qbar, κ ≠ 0 ∧ ∀ z, U1 Λ (x + ω) (GL3Theta.th0 Λ t₀) z = κ * U1 Λ x (GL3Theta.th0 Λ t₀) z := by
  intro Λ h halg t _ h2 x hx
  have ht : InRationalLattice Λ t := ⟨2, two_pos, by simpa using h2⟩
  have hc : U1 Λ t (sgStar Λ) 0 ∈ Qbar := by
    simpa [coef1] using (halg t ht).2 0
  refine ⟨?_, fun ω hω => ?_⟩
  · rw [funext (thetaTranslate_evenTheta_eq_sigmaStar_translate t x)]
    exact algEnt_const_mul (halg _ (rationalLatticePoint_add hx ht)) (Qbar.div_mem (phase_mem h hx ht) hc)
  · have hω' := rationalLatticePoint_of_mem_lattice hω
    have hs : (if ω / 2 ∈ Λ then 1 else -1 : ℂ) ∈ Qbar := by
      split_ifs
      · exact Qbar.one_mem
      · exact Qbar.neg_mem Qbar.one_mem
    have hs0 : (if ω / 2 ∈ Λ then 1 else -1 : ℂ) ≠ 0 := by
      split_ifs <;> norm_num
    refine ⟨phase Λ (x + ω) t / phase Λ x t * ((if ω / 2 ∈ Λ then 1 else -1) / phase Λ (x + t) ω),
      Qbar.mul_mem (Qbar.div_mem (phase_mem h (rationalLatticePoint_add hx hω') ht) (phase_mem h hx ht))
        (Qbar.div_mem hs (phase_mem h (rationalLatticePoint_add hx ht) hω')),
      mul_ne_zero (div_ne_zero (phase_ne_zero _ _) (phase_ne_zero _ _))
        (div_ne_zero hs0 (phase_ne_zero _ _)), fun z => ?_⟩
    rw [thetaTranslate_evenTheta_eq_sigmaStar_translate, thetaTranslate_evenTheta_eq_sigmaStar_translate, add_right_comm, sigmaStarTranslate_add_lattice_sign_phase h hω]
    have := phase_ne_zero (Λ := Λ) x t
    generalize (if ω / 2 ∈ Λ then 1 else -1 : ℂ) / phase Λ (x + t) ω = s
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    generalize (U1 Λ t (sgStar Λ) 0)⁻¹ = c
    field_simp

end GlobalTheory.EvenThetaTorsion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorTorsionTranslateEvenThetaStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicTaylor_torsionTranslate_evenTheta : ∀ Λ : AddSubgroup ℂ, IsLat Λ → (∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (sgStar Λ))) → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (GL3Theta.th0 Λ t₀)) ∧ ∀ ω ∈ Λ, ∃ κ ∈ Qbar, κ ≠ 0 ∧ ∀ z, U1 Λ (x + ω) (GL3Theta.th0 Λ t₀) z = κ * U1 Λ x (GL3Theta.th0 Λ t₀) z := by
  first | exact @GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt | exact GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt | (intros; apply GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt <;> assumption)
end
end
