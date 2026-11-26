module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSpreadsOut
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerQuotientExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAtOfSqBound
noncomputable section

open MeasureTheory Topology
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KerVec

theorem ker_mul_right {G : Type} [Group G] (Γ : Subgroup G) (φ : G → ℂ) (z y w : G) :
    ker Γ (fun g => φ (g * w)) z y = ker Γ φ z (y * w) := by
  simp only [ker, mul_assoc]

theorem tst_mul_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {φ : G → ℂ} (h : Tst φ) (w : G) : Tst (fun g => φ (g * w)) :=
  ⟨h.1.comp (continuous_mul_const w), h.2.comp_homeomorph (Homeomorph.mulRight w)⟩

theorem continuousAt_of_sq_bound {G E : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SeminormedAddCommGroup E] (f : G → E) (y₀ : G) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ w in 𝓝 (1 : G),
      ‖f (y₀ * w) - f y₀‖ₑ ^ 2 ≤ c * ENNReal.ofReal ε ^ 2) : ContinuousAt f y₀ := by
  rw [ContinuousAt, ← map_mul_left_nhds_one y₀, Filter.tendsto_map'_iff, Metric.tendsto_nhds]
  intro ε hε
  have hc0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  have hε' : 0 < ε / (c.toReal + 1) := by positivity
  filter_upwards [h _ hε'] with w hw
  have hb : ‖f (y₀ * w) - f y₀‖ ^ 2 ≤ c.toReal * (ε / (c.toReal + 1)) ^ 2 := by
    have hr : ENNReal.ofReal (‖f (y₀ * w) - f y₀‖ ^ 2) ≤
        ENNReal.ofReal (c.toReal * (ε / (c.toReal + 1)) ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_mul hc0,
        ENNReal.ofReal_pow hε'.le, ENNReal.ofReal_toReal hc, ofReal_norm]
      exact hw
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hr
  have hlt : c.toReal * (ε / (c.toReal + 1)) ^ 2 < ε ^ 2 := by
    have hd : 0 < (c.toReal + 1) ^ 2 := by positivity
    rw [div_pow, ← mul_div_assoc, div_lt_iff₀ hd]
    have : 0 < ε ^ 2 := by positivity
    nlinarith [mul_nonneg hc0 hc0, mul_nonneg hc0 this.le, mul_nonneg (mul_nonneg hc0 hc0) this.le]
  show dist (f ((fun x => y₀ * x) w)) (f y₀) < ε
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (hb.trans_lt hlt)

theorem vecEx : CntBasic → KernelL2RowsColumns → TwoUnif → VecClose → VecEx := by
  intro hC hL hT hV X ι _ Φ hΦ
  let k : X.G → ι → X.Hs ι := fun y j =>
    WithLp.toLp 2 fun l => ((hL X (Φ l j) (hΦ l j)).1 y).toLp _
  have hk : ∀ y j, X.IsVec Φ y j (k y j) := fun y j l =>
    ((hL X (Φ l j) (hΦ l j)).1 y).coeFn_toLp
  refine ⟨k, fun j => continuous_iff_continuousAt.2 fun y₀ => ?_, hk⟩
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  have hS : IsCompact (⋃ l, tsupport (Φ l j)) := isCompact_iUnion fun l => (hΦ l j).2
  obtain ⟨Ω, hΩdef⟩ : ∃ Ω : Set X.G, Ω = (⋃ l, tsupport (Φ l j)) * N⁻¹ := ⟨_, rfl⟩
  have hΩ : IsCompact Ω := hΩdef ▸ hS.mul hNc.inv
  have hsub : ∀ (l : ι) (w : X.G), w ∈ N → Function.support (fun g => Φ l j (g * w)) ⊆ Ω := by
    intro l w hw g hg
    rw [hΩdef]
    have h1 : g * w ∈ ⋃ l, tsupport (Φ l j) :=
      Set.mem_iUnion.2 ⟨l, subset_tsupport _ hg⟩
    have h2 : w⁻¹ ∈ N⁻¹ := Set.inv_mem_inv.2 hw
    simpa using Set.mul_mem_mul h1 h2
  have hc : (Fintype.card ι : ℝ≥0∞) * (X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y₀) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top hΩ.inv.measure_lt_top.ne
      ((hC X).1 _ (hΩ.inv.mul hΩ) y₀))
  refine continuousAt_of_sq_bound (fun y => k y j) y₀ _ hc fun ε hε => ?_
  choose W hW hW' using fun l => hT X (Φ l j) ε (hΦ l j) hε
  filter_upwards [hN1, Filter.eventually_all.2 hW] with w hwN hwW
  have hv : X.IsVec (fun l i g => Φ l i (g * w)) y₀ j (k (y₀ * w) j) := fun l =>
    (hk (y₀ * w) j l).trans (Filter.Eventually.of_forall fun z => (ker_mul_right X.Γ (Φ l j) z y₀ w).symm)
  have key := hV X ι (fun l i g => Φ l i (g * w)) Φ Ω ε y₀ j _ _ hΩ
    (fun l => ⟨tst_mul_right (hΦ l j) w, hΦ l j, hsub l w hwN,
      by simpa using hsub l 1 h1N, fun z => by
        simpa using hW' l 1 (mem_of_mem_nhds (hW l)) w (hwW l) z⟩) hv (hk y₀ j)
  refine key.trans (le_of_eq ?_)
  ring

end GlobalTheory.CompanionTheory.KerVec

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeFourthProperty
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeFourthProperty
open MeasureTheory Polynomial

namespace GlobalTheory.CompanionTheory.TfLoc

open PositivityTheory.Rg.Tf.Loc

theorem commute_aeval_right {K : Type*} [Field K] {n : ℕ} {A M : Matrix (Fin n) (Fin n) K}
    (hc : Commute A M) (p : K[X]) : Commute A (aeval M p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add_right hq
  | monomial m a =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right a A).mul_right (hc.pow_right m)

theorem transport_open_trace : D0a → T0 → A1 → MeasureTransportOpenSet := by
  intro hD _ hA
  unfold D0a at hD
  unfold A1 at hA
  unfold MeasureTransportOpenSet
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ hur σ hgen n _ _ _ _ SE Sk hSE hSk δ γ h μδ μγ hreg hN hmap y z hz
  have hinc : Continuous (fun g : GL (Fin n) k => (incl g : GL (Fin n) E)) :=
    (hD k E hur σ hgen).2.2.2.2.2 n
  have hcf : Continuous (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hci : Continuous (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) :=
    hinc.comp continuous_subtype_val

  have hsep : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := by
    have h0 := hreg
    unfold IsTwRegSemisimple at h0
    rw [hN, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at h0
    exact h0
  obtain ⟨p, hp⟩ := hA E n _ hsep (z : Matrix (Fin n) (Fin n) E) hz

  have hzt : ∀ t : Subgroup.centralizer {γ},
      z * incl (t : GL (Fin n) k) = incl (t : GL (Fin n) k) * z := by
    intro t
    have ht : (t : GL (Fin n) k) * γ = γ * t := Subgroup.mem_centralizer_singleton_iff.mp t.2
    have hc : Commute ((incl (t : GL (Fin n) k) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
        ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
      have := congrArg (fun g => ((incl g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) ht
      simpa [Commute, SemiconjBy, map_mul, Units.val_mul] using this
    have hc2 := commute_aeval_right hc p
    rw [← hp] at hc2
    exact Units.ext hc2.symm.eq
  set S' : Set (GL (Fin n) E) := {w | (z * incl y)⁻¹ * w * (z * incl y) ∈ SE} with hS'
  have hopen : IsOpen S' :=
    hSE.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hmeas : MeasurableSet S' := hopen.measurableSet
  have e1 : μδ {x | (h * z * incl y)⁻¹ * (x : GL (Fin n) E) * (h * z * incl y) ∈ SE} =
      Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ S' := by
    rw [Measure.map_apply hcf.measurable hmeas]
    congr 1
    ext x
    have : (h * z * incl y)⁻¹ * (x : GL (Fin n) E) * (h * z * incl y) =
        (z * incl y)⁻¹ * (h⁻¹ * (x : GL (Fin n) E) * h) * (z * incl y) := by group
    simp only [Set.mem_preimage, hS', Set.mem_ofPred_eq, this]
  have e2 : Measure.map (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) μγ S' =
      μγ {t | y⁻¹ * (t : GL (Fin n) k) * y ∈ Sk} := by
    rw [Measure.map_apply hci.measurable hmeas]
    congr 1
    ext t
    have : (z * incl y)⁻¹ * incl (t : GL (Fin n) k) * (z * incl y) =
        incl (y⁻¹ * (t : GL (Fin n) k) * y) := by
      calc (z * incl y)⁻¹ * incl (t : GL (Fin n) k) * (z * incl y)
          = (incl y)⁻¹ * (z⁻¹ * (incl (t : GL (Fin n) k) * z)) * incl y := by group
        _ = (incl y)⁻¹ * (z⁻¹ * (z * incl (t : GL (Fin n) k))) * incl y := by rw [hzt t]
        _ = (incl y)⁻¹ * incl (t : GL (Fin n) k) * incl y := by group
        _ = incl (y⁻¹ * (t : GL (Fin n) k) * y) := by simp only [map_mul, map_inv]
    simp only [Set.mem_preimage, hS', Set.mem_ofPred_eq, this, hSk]
  rw [e1, hmap, e2]

end GlobalTheory.CompanionTheory.TfLoc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeFourthPropertyStatement
alias GlobalTheory.T.unipotent_hecke_fourth_property := GlobalTheory.CompanionTheory.TfLoc.transport_open_trace
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonApproximationLocalToGlobal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonApproximationLocalToGlobal
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.NewtonStep

variable {S : Type} [CommRing S]

theorem mul_eval_eq (Q : Polynomial S) {e z w : S} (h : e * (z - w) = 0) :
    e * Q.eval z = e * Q.eval w := by
  obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub z w Q
  linear_combination e * hc + c * h

theorem mul_pow_eq (d : ℕ) {e z w : S} (h : e * (z - w) = 0) :
    e * z ^ d = e * w ^ d := by
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow z w d
  linear_combination e * hc + c * h

theorem step_of_forall_maximal (ϖ : S)
    (H : ∀ m : Ideal S, m.IsMaximal → Step (Ideal.Quotient.mk (compI m) ϖ)) : Step ϖ := by
  intro Q n hQ hd h0
  have key := GlobalTheory.T.idempotent_local_induction (S := S)
    (fun e => ∃ z, ϖ ^ (n + 1) ∣ e * Q.eval z ∧ ϖ ^ n ∣ e * z ^ Q.natDegree) ?_ ?_ ?_ ?_
  · obtain ⟨z, h1, h2⟩ := key
    exact ⟨z, by simpa using h1, by simpa using h2⟩
  · exact ⟨0, by simp, by simp⟩
  · rintro e e' _ _ ⟨z, h1, h2⟩
    refine ⟨z, ?_, ?_⟩
    · rw [mul_right_comm]; exact Dvd.dvd.mul_right h1 e'
    · rw [mul_right_comm]; exact Dvd.dvd.mul_right h2 e'
  · rintro e e' he he' hee ⟨z1, a1, b1⟩ ⟨z2, a2, b2⟩
    have he1 : e * e = e := he
    have he2 : e' * e' = e' := he'
    have hz1 : e * (e * z1 + e' * z2 - z1) = 0 := by
      linear_combination z1 * he1 + z2 * hee
    have hz2 : e' * (e * z1 + e' * z2 - z2) = 0 := by
      linear_combination z1 * hee + z2 * he2
    refine ⟨e * z1 + e' * z2, ?_, ?_⟩
    · rw [add_mul, mul_eval_eq Q hz1, mul_eval_eq Q hz2]
      exact dvd_add a1 a2
    · rw [add_mul, mul_pow_eq _ hz1, mul_pow_eq _ hz2]
      exact dvd_add b1 b2
  · intro m hm
    have hle : compI m ≤ m := Ideal.span_le.2 (fun e he => he.2)
    have hne : compI m ≠ ⊤ := fun h => hm.ne_top (top_le_iff.1 (h ▸ hle))
    have : Nontrivial (S ⧸ compI m) := Ideal.Quotient.nontrivial_iff.2 hne
    have hdeg : (Q.map (Ideal.Quotient.mk (compI m))).natDegree = Q.natDegree :=
      hQ.natDegree_map _
    have h0' : (Ideal.Quotient.mk (compI m) ϖ) ^ n ∣
        (Q.map (Ideal.Quotient.mk (compI m))).eval 0 := by
      rw [Polynomial.eval_zero_map, ← map_pow]
      exact map_dvd _ h0
    obtain ⟨z', h1, h2⟩ := H m hm (Q.map (Ideal.Quotient.mk (compI m))) n
      (hQ.map _) (hdeg ▸ hd) h0'
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z'
    obtain ⟨a', ha⟩ := h1
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
    obtain ⟨b', hb⟩ := h2
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
    rw [hdeg] at hb
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, ← map_pow, ← map_mul] at ha
    rw [← map_pow, ← map_pow, ← map_mul] at hb
    obtain ⟨e1, i1, n1, E1⟩ := (GlobalTheory.T.mem_idempotent_complement_iff m hm.isPrime _).1 (Ideal.Quotient.eq.1 ha)
    obtain ⟨e2, i2, n2, E2⟩ := (GlobalTheory.T.mem_idempotent_complement_iff m hm.isPrime _).1 (Ideal.Quotient.eq.1 hb)
    have i1' : e1 * e1 = e1 := i1
    have i2' : e2 * e2 = e2 := i2
    refine ⟨e1 * e2, ?_, ?_, z, ⟨e1 * e2 * a, ?_⟩, ⟨e1 * e2 * b, ?_⟩⟩
    · change e1 * e2 * (e1 * e2) = e1 * e2
      linear_combination (e2 * e2) * i1' + e1 * i2'
    · intro h
      exact (hm.isPrime.mem_or_mem h).elim n1 n2
    · linear_combination e2 * E1
    · linear_combination e1 * E2

end GlobalTheory.CompanionTheory.NewtonStep
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonApproximationLocalToGlobalStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
alias GlobalTheory.T.newton_approximation_local_to_global := GlobalTheory.CompanionTheory.NewtonStep.step_of_forall_maximal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardTwoAffineHyperplanes
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardTwoAffineHyperplanes
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

namespace GlobalTheory.CompanionTheory.GapOpCount

noncomputable def pairMap {k : Type} [Field k] {n : ℕ} (a b : Fin (n + 1) → k) :
    (Fin (n + 1) → k) →ₗ[k] k × k where
  toFun x := (a ⬝ᵥ x, b ⬝ᵥ x)
  map_add' x y := by simp [dotProduct_add]
  map_smul' c x := by simp [dotProduct_smul]

theorem pairMap_range {k : Type} [Field k] {n : ℕ} (a b : Fin (n + 1) → k)
    (ha : a ≠ 0) (hb : ∀ s : k, b ≠ s • a) : LinearMap.range (pairMap a b) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hform : ∀ u v : k, φ (u, v) = u * φ (1, 0) + v * φ (0, 1) := by
    intro u v
    have h : ((u, v) : k × k) = u • ((1, 0) : k × k) + v • ((0, 1) : k × k) := by simp
    rw [h, map_add (f := _), map_smul, map_smul]
    simp
  have hzero : (φ (1, 0) • a + φ (0, 1) • b) = 0 := by
    apply dotProduct_eq_zero
    intro x
    have hx : φ (pairMap a b x) = 0 := hle (LinearMap.mem_range_self _ x)
    have hx' : φ (a ⬝ᵥ x, b ⬝ᵥ x) = 0 := hx
    rw [hform] at hx'
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    linear_combination hx'
  by_cases hμ : φ (0, 1) = 0
  · rw [hμ, zero_smul, add_zero] at hzero
    rcases smul_eq_zero.mp hzero with hl | h0
    · apply hφ
      ext p
      · simp [hl]
      · simp [hμ]
    · exact ha h0
  · apply hb (-(φ (0, 1))⁻¹ * φ (1, 0))
    have h1 : φ (0, 1) • b = -(φ (1, 0) • a) := eq_neg_of_add_eq_zero_right hzero
    calc b = (φ (0, 1))⁻¹ • (φ (0, 1) • b) := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = (-(φ (0, 1))⁻¹ * φ (1, 0)) • a := by
        rw [h1, smul_neg, smul_smul, neg_mul, neg_smul]

theorem card_two_equations (k : Type) [Field k] [Fintype k] (n : ℕ) (a b : Fin (n + 1) → k)
    (ha : a ≠ 0) (hb : ∀ s : k, b ≠ s • a) :
    Fintype.card k ^ 2 * (Finset.univ.filter
      (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by
  have hr := pairMap_range a b ha hb
  obtain ⟨x0, hx0⟩ : ∃ x0, pairMap a b x0 = ((1, 1) : k × k) := by
    have : ((1, 1) : k × k) ∈ LinearMap.range (pairMap a b) := by rw [hr]; trivial
    exact this
  have hx1 : a ⬝ᵥ x0 = 1 := congrArg Prod.fst hx0
  have hx2 : b ⬝ᵥ x0 = 1 := congrArg Prod.snd hx0
  have hker : ∀ y, y ∈ LinearMap.ker (pairMap a b) ↔ a ⬝ᵥ y = 0 ∧ b ⬝ᵥ y = 0 := by
    intro y
    rw [LinearMap.mem_ker]
    exact Prod.ext_iff
  let e : LinearMap.ker (pairMap a b) ≃ {x : Fin (n + 1) → k // a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1} :=
    { toFun := fun y => ⟨y.1 + x0, by
        have h := (hker y.1).1 y.2
        simp [dotProduct_add, h.1, h.2, hx1, hx2]⟩
      invFun := fun x => ⟨x.1 - x0, by
        rw [hker]
        simp [dotProduct_sub, x.2.1, x.2.2, hx1, hx2]⟩
      left_inv := fun y => by simp
      right_inv := fun x => by simp }
  have hcard : (Finset.univ.filter
      (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card
      = Fintype.card k ^ Module.finrank k (LinearMap.ker (pairMap a b)) := by
    rw [← Module.card_eq_pow_finrank (K := k) (V := LinearMap.ker (pairMap a b)),
      Fintype.card_congr e, Fintype.card_subtype]
  have hrank := LinearMap.finrank_range_add_finrank_ker (pairMap a b)
  rw [hr, finrank_top] at hrank
  have h2 : Module.finrank k (k × k) = 2 := by simp
  have hV : Module.finrank k (Fin (n + 1) → k) = n + 1 := by simp
  rw [h2, hV] at hrank
  rw [hcard, ← pow_add, hrank]

end GlobalTheory.CompanionTheory.GapOpCount
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardTwoAffineHyperplanesStatement
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
alias GlobalTheory.T.card_two_affine_hyperplanes := GlobalTheory.CompanionTheory.GapOpCount.card_two_equations
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationOfLocalDichotomy
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationOfLocalDichotomy
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.Idem

theorem val_of_dich : ∀ {S : Type} [CommRing S] (ϖ : S),
    (∀ m : Ideal S, m.IsMaximal → Dich (Ideal.Quotient.mk (compI m) ϖ)) → Val ϖ := by
  intro S _ ϖ hD f g hfg
  obtain ⟨N, hN⟩ := hfg
  let Q : S → Prop := fun e => ∃ d, IsIdempotentElem d ∧ d * e = d ∧ d * f ∈ Ideal.span {g} ∧
    (e - d) * g ∈ Ideal.span {f}
  have hQ1 : Q 1 := by
    apply GlobalTheory.CompanionTheory.Idem.glue_idempotent_property Q
    · exact ⟨0, IsIdempotentElem.zero, by simp, by simp, by simp⟩
    · rintro e e' he he' ⟨d, hd, hde, hdf, hdg⟩
      refine ⟨d * e', hd.mul he', ?_, ?_, ?_⟩
      · calc d * e' * (e * e') = (d * e) * (e' * e') := by ring
          _ = d * e' := by rw [hde, he'.eq]
      · rw [mul_comm d e', mul_assoc]
        exact Ideal.mul_mem_left _ _ hdf
      · have h3 : (e * e' - d * e') * g = e' * ((e - d) * g) := by ring
        rw [h3]
        exact Ideal.mul_mem_left _ _ hdg
    · rintro e e' he he' hee ⟨d, hd, hde, hdf, hdg⟩ ⟨d', hd', hde', hdf', hdg'⟩
      have hdd : d * d' = 0 := by
        calc d * d' = (d * e) * (d' * e') := by rw [hde, hde']
          _ = (d * d') * (e * e') := by ring
          _ = 0 := by rw [hee, mul_zero]
      have h1 : d * e' = 0 := by
        calc d * e' = (d * e) * e' := by rw [hde]
          _ = d * (e * e') := by ring
          _ = 0 := by rw [hee, mul_zero]
      have h2 : d' * e = 0 := by
        calc d' * e = (d' * e') * e := by rw [hde']
          _ = d' * (e * e') := by ring
          _ = 0 := by rw [hee, mul_zero]
      refine ⟨d + d', ?_, ?_, ?_, ?_⟩
      · show (d + d') * (d + d') = d + d'
        calc (d + d') * (d + d') = d * d + d' * d' + 2 * (d * d') := by ring
          _ = d + d' := by rw [hd.eq, hd'.eq, hdd, mul_zero, add_zero]
      · calc (d + d') * (e + e') = d * e + d * e' + (d' * e + d' * e') := by ring
          _ = d + d' := by rw [hde, hde', h1, h2]; ring
      · rw [add_mul]
        exact Ideal.add_mem _ hdf hdf'
      · have h3 : (e + e' - (d + d')) * g = (e - d) * g + (e' - d') * g := by ring
        rw [h3]
        exact Ideal.add_mem _ hdg hdg'
    · intro m hm
      have hprime := hm.isPrime
      have hspan : (Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) ϖ) ^ N ∈
          Ideal.span {Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) f, Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) g} := by
        rw [← map_pow]
        have h4 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m)) hN
        rwa [Ideal.map_span, Set.image_pair] at h4
      rcases hD m hm _ _ ⟨N, hspan⟩ with hgf | hfg'
      · obtain ⟨c, hc⟩ := hgf
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        have hmem : f - g * a ∈ CrystallineSemistableComparison.R.compI m := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, sub_self]
        obtain ⟨e, he, hem, hex⟩ := (GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff m hprime _).1 hmem
        have hef : e * f = e * (g * a) := by
          rw [mul_sub] at hex
          exact sub_eq_zero.1 hex
        refine ⟨e, he, hem, e, he, he.eq, ?_, by simp⟩
        rw [hef]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g))
      · obtain ⟨c, hc⟩ := hfg'
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        have hmem : g - f * a ∈ CrystallineSemistableComparison.R.compI m := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, sub_self]
        obtain ⟨e, he, hem, hex⟩ := (GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff m hprime _).1 hmem
        have heg : e * g = e * (f * a) := by
          rw [mul_sub] at hex
          exact sub_eq_zero.1 hex
        refine ⟨e, he, hem, 0, IsIdempotentElem.zero, by simp, by simp, ?_⟩
        rw [sub_zero, heg]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f))
  obtain ⟨d, hd, -, hdf, hdg⟩ := hQ1
  exact ⟨d, hd, hdf, hdg⟩

end GlobalTheory.CompanionTheory.Idem
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationOfLocalDichotomyStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
alias GlobalTheory.T.valuation_of_local_dichotomy := GlobalTheory.CompanionTheory.Idem.val_of_dich
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsQuot
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem tors_quot : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (π : B), Pf p B →
    ∃ (B₁ : Type) (_ : CommRing B₁) (q : B →+* B₁), Function.Surjective q ∧ Pf p B₁ ∧
      q π ∈ nonZeroDivisors B₁ ∧ (∀ x, q x = 0 ↔ π * x = 0) ∧ (AIC B → AIC B₁) ∧
      (VAL π → VAL (q π)) := by
  intro p _ B _ π h
  have hp : p.Prime := Fact.out
  obtain ⟨⟨F, hF⟩, hred, -, -, -⟩ := pf_facts p B h

  have hpow : ∀ (N : ℕ) (x : B), π ^ N * x = 0 → π * x = 0 := by
    intro N x e
    apply hred _ (N + 1)
    calc (π * x) ^ (N + 1) = π * x ^ N * (π ^ N * x) := by ring
      _ = 0 := by rw [e, mul_zero]

  have hfrob : ∀ x : B, π * x ^ p = 0 → π * x = 0 := by
    intro x e
    apply hred _ p
    have h1 : p = (p - 1) + 1 := by have := hp.one_lt; omega
    rw [mul_pow]
    conv_lhs => rw [h1, pow_succ π]
    rw [← h1, mul_assoc, e, mul_zero]
  let I : Ideal B :=
    { carrier := {x | π * x = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [mul_add, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
        rw [mul_left_comm, hx, mul_zero] }
  have hI : ∀ x, Ideal.Quotient.mk I x = 0 ↔ π * x = 0 := fun x => Ideal.Quotient.eq_zero_iff_mem
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  refine ⟨B ⧸ I, inferInstance, Ideal.Quotient.mk I, hsurj, ⟨?_, ?_, ?_⟩, ?_, hI, ?_, ?_⟩
  · rw [← map_natCast (Ideal.Quotient.mk I), h.char, map_zero]
  · intro a b e
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := hsurj b
    simp only at e
    rw [← map_pow, ← map_pow, ← sub_eq_zero, ← map_sub, hI] at e
    rw [← sub_eq_zero, ← map_sub, hI]
    apply hfrob
    have : (x - y) ^ p = x ^ p - y ^ p := by
      rw [← hF, map_sub, hF, hF]
    rw [this, e]
  · intro a
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := h.bij.2 x
    exact ⟨Ideal.Quotient.mk I y, by simp only [map_pow]⟩
  · rw [mem_nonZeroDivisors_iff_right]
    intro a e
    obtain ⟨x, rfl⟩ := hsurj a
    rw [← map_mul, hI] at e
    rw [hI]
    apply hpow 2
    rw [← e]
    ring
  · intro hA P hP hdeg
    have hl : P ∈ Polynomial.lifts (Ideal.Quotient.mk I) :=
      (Polynomial.map_surjective _ hsurj P).imp (fun Q hQ => by simpa using hQ) |> fun ⟨Q, hQ⟩ =>
        (Polynomial.mem_lifts _).2 ⟨Q, hQ⟩
    obtain ⟨Q, rfl, hQd, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hP
    obtain ⟨x, hx⟩ := hA Q hQm (hQd ▸ hdeg)
    exact ⟨Ideal.Quotient.mk I x, hx.map (Ideal.Quotient.mk I)⟩
  · intro hV f₁ g₁ ⟨N, hN⟩
    obtain ⟨f, rfl⟩ := hsurj f₁
    obtain ⟨g, rfl⟩ := hsurj g₁
    obtain ⟨a₁, b₁, hab⟩ := Ideal.mem_span_pair.1 hN
    obtain ⟨a, rfl⟩ := hsurj a₁
    obtain ⟨b, rfl⟩ := hsurj b₁
    have ht : π * (a * f + b * g - π ^ N) = 0 := by
      rw [← hI, map_sub, map_add (f := _), map_mul, map_mul, map_pow, hab, sub_self]
    have hmem : π ^ (N + 1) ∈ Ideal.span {f, g} := by
      refine Ideal.mem_span_pair.2 ⟨π * a, π * b, ?_⟩
      linear_combination ht
    obtain ⟨e, he, h1, h2⟩ := hV f g ⟨N + 1, hmem⟩
    refine ⟨Ideal.Quotient.mk I e, he.map _, ?_, ?_⟩
    · rw [Ideal.mem_span_singleton] at h1 ⊢
      rw [← map_mul]
      exact map_dvd _ h1
    · rw [Ideal.mem_span_singleton] at h2 ⊢
      have : (1 - Ideal.Quotient.mk I e) * Ideal.Quotient.mk I g
          = Ideal.Quotient.mk I ((1 - e) * g) := by
        rw [map_mul, map_sub, map_one]
      rw [this]
      exact map_dvd _ h2

end GlobalTheory.CompanionTheory.PerfectRing
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvAdjEqAvg
noncomputable section

open MeasureTheory
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.ApproxUnit

theorem avg_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (b : α → ℝ) (u : α → ℂ) (c : ℂ)
    (ε : ℝ) (hb0 : ∀ w, 0 ≤ b w) (hb1 : ∫ w, b w ∂μ = 1) (hum : AEStronglyMeasurable u μ)
    (h : ∀ w, b w ≠ 0 → ‖u w - c‖ ≤ ε) :
    ‖∫ w, u w * (b w : ℂ) ∂μ - c‖ ≤ ε := by
  have hbi : Integrable b μ := by
    by_contra hn
    rw [integral_undef hn] at hb1
    exact zero_ne_one hb1
  have hbc : Integrable (fun w => (b w : ℂ)) μ := hbi.ofReal
  have hpt : ∀ w, ‖(u w - c) * (b w : ℂ)‖ ≤ ε * b w := by
    intro w
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hb0 w)]
    by_cases hw : b w = 0
    · simp [hw]
    · exact mul_le_mul_of_nonneg_right (h w hw) (hb0 w)
  have hd : Integrable (fun w => (u w - c) * (b w : ℂ)) μ :=
    Integrable.mono' (hbi.const_mul ε)
      ((hum.sub aestronglyMeasurable_const).mul hbc.aestronglyMeasurable)
      (Filter.Eventually.of_forall hpt)
  have hc : ∫ w, (b w : ℂ) ∂μ = 1 := by
    rw [integral_complex_ofReal, hb1]
    simp
  have hu : Integrable (fun w => u w * (b w : ℂ)) μ := by
    have := hd.add (hbc.const_mul c)
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.add_apply]
    ring
  have e : ∫ w, u w * (b w : ℂ) ∂μ - c = ∫ w, (u w - c) * (b w : ℂ) ∂μ := by
    have h1 : (fun w => (u w - c) * (b w : ℂ)) = fun w => u w * (b w : ℂ) - c * (b w : ℂ) := by
      ext w
      ring
    rw [h1, integral_sub hu (hbc.const_mul c), integral_const_mul, hc, mul_one]
  rw [e]
  calc ‖∫ w, (u w - c) * (b w : ℂ) ∂μ‖ ≤ ∫ w, ε * b w ∂μ :=
        norm_integral_le_of_norm_le (hbi.const_mul ε) (Filter.Eventually.of_forall hpt)
    _ = ε := by rw [integral_const_mul, hb1, mul_one]

theorem cv_eq_avg (X : Ctx) (φ ψ : X.G → ℂ) (hψ : IsBump X ψ) (g : X.G) :
    cv X.μ φ ψ g = ∫ w, φ (g * w) * ((‖ψ w⁻¹‖ : ℝ) : ℂ) ∂X.μ := by
  unfold cv
  rw [← integral_mul_left_eq_self _ g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [mul_inv_rev, inv_mul_cancel_right]
  rw [← hψ.2.1]

theorem cv_adj_eq_avg (X : Ctx) (f ψ : X.G → ℂ) (hψ : IsBump X ψ) (y : X.G) :
    cv X.μ (adj ψ) f y = ∫ z, f (z⁻¹ * y) * ((‖ψ z⁻¹‖ : ℝ) : ℂ) ∂X.μ := by
  unfold cv
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have h : adj ψ z = ((‖ψ z⁻¹‖ : ℝ) : ℂ) := by
    unfold adj
    rw [hψ.2.1 z⁻¹]
    simp
  simp only [h]
  ring

theorem approxU : CvTest → TwoUnif → ApproxU := by
  intro hcv htu X φ ε hφ hε
  letI : Inv (Set X.G) := Set.inv
  obtain ⟨W₀, hW₀, hW⟩ := htu X φ ε hφ hε
  refine ⟨W₀ ∩ W₀⁻¹, Filter.inter_mem hW₀ (inv_mem_nhds_one _ hW₀), ?_⟩
  intro ψ hb hsub y
  have hsupp : ∀ w, ‖ψ w⁻¹‖ ≠ 0 → w ∈ W₀ ∧ w⁻¹ ∈ W₀ := by
    intro w hw
    have h1 : w⁻¹ ∈ tsupport ψ := subset_tsupport _ (norm_ne_zero_iff.1 hw)
    have h2 := hsub h1
    exact ⟨by simpa using h2.2, h2.1⟩
  have hb0 : ∀ w, 0 ≤ ‖ψ w⁻¹‖ := fun w => norm_nonneg _
  have key : ∀ z ∈ W₀, ‖cv X.μ φ ψ (z * y) - φ y‖ ≤ ε := by
    intro z hz
    rw [cv_eq_avg X φ ψ hb]
    refine avg_le X.μ (fun w => ‖ψ w⁻¹‖) (fun w => φ (z * y * w)) (φ y) ε hb0 hb.2.2
      (Continuous.aestronglyMeasurable (hφ.1.comp (by fun_prop))) ?_
    intro w hw
    exact hW z hz w (hsupp w hw).1 y
  refine ⟨?_, ?_⟩
  · simpa using key 1 (mem_of_mem_nhds hW₀)
  · rw [cv_adj_eq_avg X _ ψ hb]
    have hc : Continuous (cv X.μ φ ψ) := (hcv X φ ψ hφ hb.1).1.1
    refine avg_le X.μ (fun w => ‖ψ w⁻¹‖) (fun z => cv X.μ φ ψ (z⁻¹ * y)) (φ y) ε hb0 hb.2.2
      (Continuous.aestronglyMeasurable (hc.comp (by fun_prop))) ?_
    intro z hz
    exact key z⁻¹ (hsupp z hz).2

end GlobalTheory.CompanionTheory.ApproxUnit

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageOverMaximalCompactResidue
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageOverMaximalCompactResidue
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.Jp.AvgRes

theorem avg_of_surjective {G H : Type*} [Group G] [Group H] (N : Subgroup G) [N.Normal] [Finite (G ⧸ N)] (r : G →* H)
    (hr : Function.Surjective r) (hN : N ≤ r.ker) (f : H → ℂ) :
    (Nat.card (G ⧸ N) : ℂ)⁻¹ * ∑ᶠ u : G ⧸ N, f (r (Quotient.out u)) = (∑ᶠ g, f g) / (Nat.card H : ℂ) := by
  classical
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  set φ : G ⧸ N →* H := QuotientGroup.lift N r hN with hφdef
  have hφ : Function.Surjective φ := by
    intro h
    obtain ⟨g, rfl⟩ := hr h
    exact ⟨(g : G ⧸ N), QuotientGroup.lift_mk N hN g⟩
  haveI : Finite H := Finite.of_surjective φ hφ
  haveI : Fintype H := Fintype.ofFinite _
  have hout : ∀ u : G ⧸ N, r (Quotient.out u) = φ u := by
    intro u
    conv_rhs => rw [← Quotient.out_eq u]
    exact (QuotientGroup.lift_mk N hN _).symm
  simp_rw [hout]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_comp f φ,
    Finset.image_univ_of_surjective hφ]
  set c := (Finset.univ.filter fun u : G ⧸ N => φ u = 1).card with hc
  have hfib : ∀ b : H, (Finset.univ.filter fun u : G ⧸ N => φ u = b).card = c := fun b =>
    MonoidHom.card_fiber_eq_of_mem_range φ (hφ b) (hφ 1)
  have hcard : Fintype.card (G ⧸ N) = Fintype.card H * c := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_image φ Finset.univ,
      Finset.image_univ_of_surjective hφ]
    simp [hfib]
  have hc0 : (c : ℂ) ≠ 0 := by
    rw [hc]
    exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨1, by simp⟩)
  have hH : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp_rw [hfib]
  rw [← Finset.smul_sum, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard,
    nsmul_eq_mul]
  push_cast
  field_simp

variable {O : Type} [CommRing O] [IsLocalRing O]

theorem resK_surjective (n : ℕ) : Function.Surjective (resK (n := n) (O := O)) := by
  intro M
  classical
  have hs := IsLocalRing.residue_surjective (R := O)
  let A : Matrix (Ix n) (Ix n) O :=
    (M : Matrix (Ix n) (Ix n) (IsLocalRing.ResidueField O)).map (Function.surjInv hs)
  have hA : (IsLocalRing.residue O).mapMatrix A = (M : Matrix (Ix n) (Ix n) _) := by
    ext i j
    exact Function.surjInv_eq hs _
  have hdet : IsUnit A.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hA]
    exact (Matrix.isUnits_det_units M).ne_zero
  refine ⟨Matrix.nonsingInvUnit A hdet, ?_⟩
  ext i j
  exact Function.surjInv_eq hs _

theorem level_square_congruence_le_reduction_ker (n : ℕ) {ϖ : O} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal O) :
    Gam2 (n := n) ϖ ≤ (resK (n := n) (O := O)).ker := by
  intro g hg
  have hg' := MonoidHom.mem_ker.mp hg
  rw [MonoidHom.mem_ker]
  have hle : Ideal.span {ϖ ^ 2} ≤ IsLocalRing.maximalIdeal O :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.pow_mem_of_mem _ hϖ 2 two_pos))
  ext i j
  have h1 : Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) ((g : Matrix (Ix n) (Ix n) O) i j) =
      Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) ((1 : Matrix (Ix n) (Ix n) O) i j) := by
    have h0 := congrArg
      (fun x : GL (Ix n) (O ⧸ Ideal.span {ϖ ^ 2}) => (x : Matrix (Ix n) (Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) i j) hg'
    change Ideal.Quotient.mk _ ((g : Matrix (Ix n) (Ix n) O) i j) =
      (1 : Matrix (Ix n) (Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) i j at h0
    rw [h0, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h2 := Ideal.Quotient.eq.mpr (hle (Ideal.Quotient.eq.mp h1))
  change IsLocalRing.residue O ((g : Matrix (Ix n) (Ix n) O) i j) =
    (1 : Matrix (Ix n) (Ix n) (IsLocalRing.ResidueField O)) i j
  rw [show (1 : Matrix (Ix n) (Ix n) (IsLocalRing.ResidueField O)) i j =
      IsLocalRing.residue O ((1 : Matrix (Ix n) (Ix n) O) i j) by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp]
  exact h2

theorem avgK_res : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fintype (IsLocalRing.ResidueField O)]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ f : GL (Ix n) (IsLocalRing.ResidueField O) → ℂ,
      avgK ϖ (fun κ => f (resK κ)) = sumG f / (Nat.card (GL (Ix n) (IsLocalRing.ResidueField O)) : ℂ) := by
  intro O _ _ _ _ n ϖ hϖ f
  have hm : ϖ ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  haveI : (Gam2 (n := n) ϖ).Normal := MonoidHom.normal_ker _
  haveI : Finite (GL (Ix n) O ⧸ Gam2 (n := n) ϖ) := GlobalTheory.CompanionTheory.Jp.Unif.finite_quotient_level_square_congruence n hϖ
  exact avg_of_surjective (Gam2 ϖ) resK (resK_surjective n) (level_square_congruence_le_reduction_ker n hm) f

end GlobalTheory.CompanionTheory.Jp.AvgRes

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageOverMaximalCompactResidueStatement
open Matrix GlobalTheory.CompanionTheory.Jp
alias GlobalTheory.T.average_over_maximal_compact_residue := GlobalTheory.CompanionTheory.Jp.AvgRes.avgK_res
end
end
