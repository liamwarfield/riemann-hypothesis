module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartDim
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomial
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAnalyticLogResolution

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjChartSetEqSetChartSet
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

section Defs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def setChartSet (S : Set ((Σ k, ι k) → ℂ)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, Ψ (segre z) 0 = 1 ∧ x = fun a => segre z (σ a)}

def setChartIdeal (S : Set ((Σ k, ι k) → ℂ)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Ideal (MvPolynomial (Fin m) ℂ) :=
  vanishingIdeal ℂ (setChartSet S σ Ψ)

def setSegChartSet (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, segre z i = 1 ∧ x = fun a => segre z (σ a)}

def setSegChartIdeal (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Ideal (MvPolynomial (Fin m) ℂ) :=
  vanishingIdeal ℂ (setSegChartSet S σ i)

def setSegreCone (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, x = fun a => segre z (σ a)}

theorem isMultiHomogIdeal_toR {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal Q) :
    ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQ

theorem cone_scale {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) : (fun p => c p.1 * z p) ∈ conePts Q := by
  refine ⟨fun k => ?_, ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hQ c z hz.2⟩
  obtain ⟨i, hi⟩ := hz.1 k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem exists_segre_smul {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    [Nonempty K] {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) {c : ℂ} (hc : c ≠ 0) :
    ∃ z' ∈ conePts Q, segre z' = c • segre z := by
  classical
  obtain ⟨k0⟩ := ‹Nonempty K›
  refine ⟨_, cone_scale hQ (c := fun k => if k = k0 then c else 1) (fun k => ?_) hz, ?_⟩
  · split_ifs
    · exact hc
    · exact one_ne_zero
  · exact GoodChartZeroSet.segre_scaleBlock k0 c z

end Defs

section ZeroSet

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def liftPolyC [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (f : MRingOver ℂ ι) : MvPolynomial (Fin m) ℂ :=
  aeval (fun p : Σ k, ι k => (X (σ.symm (Function.update i p.1 p.2)) : MvPolynomial (Fin m) ℂ)) f

theorem eval_liftPolyC [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (x : Fin m → ℂ) (f : MRingOver ℂ ι) :
    eval x (liftPolyC σ i f) = eval (chartLift σ i x) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [liftPolyC]
  | add f g hf hg =>
    simp only [liftPolyC, map_add (f := _)] at hf hg ⊢
    rw [hf, hg]
  | mul_X f q hf =>
    simp only [liftPolyC, map_mul] at hf ⊢
    rw [hf]
    simp [chartLift]

theorem segChart_zeroSet {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) {m : ℕ}
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    zeroSet (setSegChartIdeal (conePts Q) σ i) = setSegChartSet (conePts Q) σ i := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ setSegChartSet (conePts Q) σ i, eval y q = 0) →
        eval x q = 0 :=
      fun q hq => hx q (by rw [setSegChartIdeal, mem_vanishingIdeal_iff]; exact hq)
    have ha : x (σ.symm i) = 1 := by
      have h := hv (X (σ.symm i) - 1) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        simp [hzi])
      rw [map_sub, eval_X, map_one] at h
      exact sub_eq_zero.1 h
    have hb : ∀ i' : (k : K) → ι k,
        x (σ.symm i') = ∏ k, x (σ.symm (Function.update i k (i' k))) := by
      intro i'
      have h := hv (X (σ.symm i') - ∏ k, X (σ.symm (Function.update i k (i' k)))) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        have hs : ∏ k, segre z (Function.update i k (i' k)) = segre z i' := by
          have h1 := congrFun (segre_chartLift σ i z hzi) i'
          simpa [ReciprocityTheory.ChartRestriction.G.Geo.segre, chartLift] using h1
        rw [map_sub, eval_X, map_prod]
        simp only [eval_X, Equiv.apply_symm_apply]
        rw [hs, sub_self])
      rw [map_sub, eval_X, map_prod] at h
      simp only [eval_X] at h
      exact sub_eq_zero.1 h
    have hc : ∀ f ∈ Q, eval (chartLift σ i x) f = 0 := by
      intro f hf
      rw [← eval_liftPolyC]
      refine hv _ ?_
      rintro _ ⟨z, hz, hzi, rfl⟩
      rw [eval_liftPolyC]
      have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
        have h1 : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
        rw [hzi] at h1
        exact one_ne_zero h1
      have hcl : chartLift σ i (fun a => segre z (σ a)) = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p := by
        funext ⟨k, j⟩
        rw [chartLift_segre_apply σ i z hzi, mul_comm]
      rw [hcl]
      exact (cone_scale hQ (c := fun k => (z ⟨k, i k⟩)⁻¹) (fun k => inv_ne_zero (hne k)) hz).2 f hf
    refine ⟨chartLift σ i x, ⟨chartLift_blockNonzero σ i ha, hc⟩, ?_, ?_⟩
    · show ∏ k, chartLift σ i x ⟨k, i k⟩ = 1
      simp [chartLift, ha]
    · funext a
      show x a = ∏ k, chartLift σ i x ⟨k, σ a k⟩
      simp only [chartLift]
      rw [← hb, Equiv.symm_apply_apply]
  · intro x hx q hq
    rw [setSegChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx

theorem chart_zeroSet {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) [Nonempty K]
    {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    zeroSet (setChartIdeal (conePts Q) σ Ψ) = setChartSet (conePts Q) σ Ψ := by
  classical
  apply Set.Subset.antisymm
  swap
  · intro x hx q hq
    rw [setChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx
  intro x hx
  have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ setChartSet (conePts Q) σ Ψ, eval y q = 0) → eval x q = 0 :=
    fun q hq => hx q (by rw [setChartIdeal, mem_vanishingIdeal_iff]; exact hq)
  have hseg : ∀ z : (Σ k, ι k) → ℂ, (fun i' => segre z (σ (σ.symm i'))) = segre z := fun z => by
    funext i'; rw [Equiv.apply_symm_apply]

  have hx1 : Ψ (fun i' => x (σ.symm i')) 0 = 1 := by
    have h := hv (GoodChartZeroSet.linForm σ Ψ - 1) (by
      rintro _ ⟨z, -, hz1, rfl⟩
      rw [map_sub, GoodChartZeroSet.eval_linForm, map_one, hseg, hz1, sub_self])
    rw [map_sub, GoodChartZeroSet.eval_linForm, map_one] at h
    exact sub_eq_zero.1 h
  obtain ⟨a, ha⟩ : ∃ a, x a ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have h0 : (fun i' => x (σ.symm i')) = 0 := funext fun i' => h _
    rw [h0, map_zero] at hx1
    exact zero_ne_one hx1

  have hzero : (x a)⁻¹ • x ∈ zeroSet (setSegChartIdeal (conePts Q) σ (σ a)) := by
    intro f hf
    rw [setSegChartIdeal, mem_vanishingIdeal_iff] at hf
    have hg := hv (X a * ∑ d ∈ Finset.range (f.totalDegree + 1),
        X a ^ (f.totalDegree - d) * homogeneousComponent d f) (by
      rintro _ ⟨z, hz, -, rfl⟩
      by_cases h0 : segre z (σ a) = 0
      · simp [h0]
      · rw [GoodChartZeroSet.eval_homogenize f le_rfl a _ h0]
        obtain ⟨z', hz', hz'e⟩ := exists_segre_smul hQ hz (inv_ne_zero h0)
        refine mul_eq_zero_of_right _ (hf _ ⟨z', hz', ?_, ?_⟩)
        · rw [hz'e, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ h0]
        · funext b
          rw [hz'e]
          rfl)
    rw [GoodChartZeroSet.eval_homogenize f le_rfl a x ha] at hg
    exact (mul_eq_zero.1 hg).resolve_left (pow_ne_zero _ ha)
  rw [segChart_zeroSet hQ σ (σ a)] at hzero
  obtain ⟨z', hz', -, hz'e⟩ := hzero
  obtain ⟨z, hz, hze⟩ := exists_segre_smul hQ hz' ha
  have hxz : x = fun b => segre z (σ b) := by
    funext b
    have hb := congrFun hz'e b
    simp only [Pi.smul_apply, smul_eq_mul] at hb
    rw [hze, Pi.smul_apply, smul_eq_mul, ← hb, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  refine ⟨z, hz, ?_, hxz⟩
  rw [← hseg z, ← hx1, hxz]

end ZeroSet

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenComponentAppendIndependentSpan
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenComponentAppendIndependentSpan
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep

theorem eq_zero_of_sum_mem_span : ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : 𝓞 E →+* Module.End ℂ V) (s₀ : 𝓞 E →+* ℂ) (I₀ : AddSubgroup V) (r k : ℕ) (v : Fin r → V) (q : Fin k → V),
    IsOFamily ρ I₀ v → (∀ (c : 𝓞 E), ∀ x ∈ I₀, ρ c x ∈ I₀) → (∀ c, q c ∈ eigSp ρ s₀) →
    LinearIndependent ℂ (Fin.append (fun a => eigComp ρ s₀ (v a)) q) →
    ∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ Submodule.span ℂ (I₀ : Set V) → l = 0 := by
  intro E _ _ V _ _ ρ s₀ I₀ r k v q hF _ hq hli l hl
  obtain ⟨c, hc⟩ := EigCoef.eigComp_eq_combination E s₀
  obtain ⟨h1, h2, h3⟩ := hc V ρ
  let π : V →ₗ[ℂ] V := ∑ a ∈ c.support, c a • ρ a
  have hπ : ∀ x, π x = eigComp ρ s₀ x := by
    intro x
    rw [h1 x]
    simp [π, LinearMap.sum_apply]
  have hact : ∀ (b : 𝓞 E) x, π (ρ b x) = s₀ b • π x := by
    intro b x
    have e : π (ρ b x) = ρ b (π x) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [π, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1
      have : ρ a * ρ b = ρ b * ρ a := by rw [← map_mul, ← map_mul, mul_comm]
      exact LinearMap.congr_fun this x
    rw [e, EigCoef.mem_eigSp_iff.1 (hπ x ▸ h2 x) b]
  let W : Submodule ℂ V := Submodule.span ℂ (Set.range fun a => eigComp ρ s₀ (v a))
  have hO : ∀ y ∈ oSpan ρ v, π y ∈ W := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, i, rfl⟩ := hy
      rw [hact, hπ]
      exact W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact W.add_mem hx hy
    | neg x _ hx =>
      rw [map_neg]
      exact W.neg_mem hx
  have hI : ∀ x ∈ I₀, π x ∈ W := by
    intro x hx
    obtain ⟨_, _, hN⟩ := hF
    have hm := hO _ (AddSubgroup.nsmul_relIndex_mem (oSpan ρ v) hx)
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ] at hm
    have hN' : (((oSpan ρ v).relIndex I₀ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
    exact (W.smul_mem_iff hN').1 hm
  have hS : Submodule.span ℂ (I₀ : Set V) ≤ W.comap π := Submodule.span_le.2 hI
  have hxe : ∑ c, l c • q c ∈ eigSp ρ s₀ := Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hq c)
  have hW : ∑ c, l c • q c ∈ W := by
    have h := hS hl
    rw [Submodule.mem_comap, hπ, h3 _ hxe] at h
    exact h
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hW
  have hz := Fintype.linearIndependent_iff.1 hli (Fin.append (-m) l) (by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
    rw [hm]
    simp)
  funext j
  have := hz (Fin.natAdd r j)
  simpa using this

end GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenComponentAppendIndependentSpanStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenComponent_append_independent_span : ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : 𝓞 E →+* Module.End ℂ V) (s₀ : 𝓞 E →+* ℂ) (I₀ : AddSubgroup V) (r k : ℕ) (v : Fin r → V) (q : Fin k → V), IsOFamily ρ I₀ v → (∀ (c : 𝓞 E), ∀ x ∈ I₀, ρ c x ∈ I₀) → (∀ c, q c ∈ eigSp ρ s₀) → LinearIndependent ℂ (Fin.append (fun a => eigComp ρ s₀ (v a)) q) → ∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ Submodule.span ℂ (I₀ : Set V) → l = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep.eq_zero_of_sum_mem_span | exact GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep.eq_zero_of_sum_mem_span | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep.eq_zero_of_sum_mem_span <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsCompactifiedModel
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.NonemptyComponentModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

variable {K : Type} {J : K → Type}

theorem orb_symm {z z' : (Σ k, J k) → ℂ} (h : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z z') :
    ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp only
  rw [← _root_.mul_assoc, inv_mul_cancel₀ (hc p.1), _root_.one_mul]

theorem orb_trans {z z' z'' : (Σ k, J k) → ℂ} (h : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z z')
    (h' : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z' z'') : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  simp only [_root_.mul_assoc]

theorem orb_limit {α : Type} {F : Filter α} [F.NeBot] {a b : α → (Σ k, J k) → ℂ} {a₀ b₀ : (Σ k, J k) → ℂ}
    (ha : ∀ p, Tendsto (fun w => a w p) F (𝓝 (a₀ p))) (hb : ∀ p, Tendsto (fun w => b w p) F (𝓝 (b₀ p)))
    (h : ∀ᶠ w in F, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (a w) (b w)) (h₀ : ∀ k, ∃ i, a₀ ⟨k, i⟩ ≠ 0)
    (h₁ : ∀ k, ∃ i, b₀ ⟨k, i⟩ ≠ 0) : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit a₀ b₀ := by
  choose ib hib using h₁
  choose ia hia using h₀
  have key : ∀ p : (Σ k, J k), a₀ p * b₀ ⟨p.1, ib p.1⟩ = a₀ ⟨p.1, ib p.1⟩ * b₀ p := by
    intro p
    have e1 : Tendsto (fun w => a w p * b w ⟨p.1, ib p.1⟩) F (𝓝 (a₀ p * b₀ ⟨p.1, ib p.1⟩)) :=
      (ha p).mul (hb _)
    have e2 : Tendsto (fun w => a w ⟨p.1, ib p.1⟩ * b w p) F (𝓝 (a₀ ⟨p.1, ib p.1⟩ * b₀ p)) :=
      (ha _).mul (hb p)
    refine tendsto_nhds_unique (e1.congr' ?_) e2
    filter_upwards [h] with w hw
    obtain ⟨c, -, hc⟩ := hw
    rw [hc]
    ring
  let c : K → ℂ := fun k => a₀ ⟨k, ib k⟩ / b₀ ⟨k, ib k⟩
  have hrel : ∀ p : (Σ k, J k), a₀ p = c p.1 * b₀ p := by
    intro p
    have hb0 := hib p.1
    simp only [c]
    field_simp
    rw [key p]
  refine ⟨c, fun k => ?_, funext hrel⟩
  intro hck
  apply hia k
  rw [hrel ⟨k, ia k⟩]
  simp [hck]

theorem continuousAt_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e X)
    {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {x : X} (hx : x ∈ U) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Set.mem_preimage, (A.chart j).left_inv hj]
    exact hx
  have h1 : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j x) := (hg j _ hmem).continuousAt
  have h2 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) x :=
    h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

variable [Fintype K] [∀ k, Fintype (J k)]

theorem cxModel_of_res {P : Ideal (MRing J)} {d : ℕ} (R : AnLogRes P ⊤ d) (hne : (mcPts P).Nonempty) :
    Nonempty (CxModel P d) := by
  classical
  letI := R.top
  haveI := R.compact
  haveI := R.t2
  have htop : ∀ z, z ∉ mcPts (⊤ : Ideal (MRing J)) := by
    intro z hz
    have h1 := hz.2 1 Submodule.mem_top
    simp at h1
  have hex : ∀ z ∈ mcPts P, ∃ x, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift x x) z :=
    fun z hz => R.surj z hz (htop z)
  have hmemU : ∀ x, R.lift x x ∈ mcPts P := fun x => R.mem x x (R.mem_U x)
  have hinj : ∀ x x', ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift x x) (R.lift x' x') → x = x' :=
    fun x x' h => R.inj x x' (htop _) h
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨x₀, -⟩ := hex z₀ hz₀
  let proj : ((Σ k, J k) → ℂ) → R.X := fun z =>
    if h : ∃ x, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift x x) z then h.choose else x₀
  have hproj : ∀ z ∈ mcPts P, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift (proj z) (proj z)) z := by
    intro z hz
    have h := hex z hz
    simp only [proj, dif_pos h]
    exact h.choose_spec
  have hproj_eq : ∀ z ∈ mcPts P, ∀ x, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift x x) z → proj z = x := by
    intro z hz x hx
    exact hinj _ _ (orb_trans (hproj z hz) (orb_symm hx))
  have hlift : ∀ x y, y ∈ R.U x → proj (R.lift x y) = y := by
    intro x y hy
    exact hproj_eq _ (R.mem x y hy) y (R.compat y x y ⟨R.mem_U y, hy⟩)
  have hcont : ContinuousOn proj (mcPts P) := by
    intro z hz
    show Tendsto proj (𝓝[mcPts P] z) (𝓝 (proj z))
    refine isCompact_univ.tendsto_nhds_of_unique_mapClusterPt
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) ?_
    intro xs _ hxs
    have hG : (𝓝[mcPts P] z ⊓ comap proj (𝓝 xs)).NeBot := by
      rw [← Filter.map_neBot_iff proj, Filter.push_pull, inf_comm]
      exact hxs
    have hpx : Tendsto proj (𝓝[mcPts P] z ⊓ comap proj (𝓝 xs)) (𝓝 xs) :=
      tendsto_comap.mono_left inf_le_right
    have hid : Tendsto id (𝓝[mcPts P] z ⊓ comap proj (𝓝 xs)) (𝓝 z) :=
      tendsto_id.mono_left (inf_le_left.trans nhdsWithin_le_nhds)
    have hlim : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift xs xs) z := by
      refine orb_limit (F := 𝓝[mcPts P] z ⊓ comap proj (𝓝 xs))
        (a := fun w => R.lift xs (proj w)) (b := fun w => w) ?_ ?_ ?_ (hmemU xs).1 hz.1
      · intro p
        exact (continuousAt_of_holoOn R.A (R.holo xs p) (R.mem_U xs)).tendsto.comp hpx
      · intro p
        exact ((continuous_apply p).tendsto z).comp hid
      · have hU : ∀ᶠ w in 𝓝[mcPts P] z ⊓ comap proj (𝓝 xs), proj w ∈ R.U xs :=
          hpx ((R.isOpen_U xs).mem_nhds (R.mem_U xs))
        have hM : ∀ᶠ w in 𝓝[mcPts P] z ⊓ comap proj (𝓝 xs), w ∈ mcPts P :=
          Filter.mem_inf_of_left self_mem_nhdsWithin
        filter_upwards [hU, hM] with w hw hwm
        exact orb_trans (R.compat xs (proj w) (proj w) ⟨hw, R.mem_U _⟩) (hproj w hwm)
    exact (hproj_eq z hz xs hlim).symm
  have hfib : ∀ z ∈ mcPts P, ∀ z' ∈ mcPts P,
      proj z = proj z' ↔ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z' = torusSmul c z := by
    intro z hz z' hz'
    constructor
    · intro he
      have h1 := hproj z hz
      have h2 := hproj z' hz'
      rw [he] at h1
      obtain ⟨c, hc, hcz⟩ := orb_trans (orb_symm h2) h1
      exact ⟨c, hc, hcz⟩
    · rintro ⟨c, hc, hcz⟩
      have h3 : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z' z := ⟨c, hc, hcz⟩
      exact (hproj_eq z' hz' (proj z) (orb_trans (hproj z hz) (orb_symm h3))).symm
  have hsurj : ∀ x, ∃ z ∈ mcPts P, proj z = x :=
    fun x => ⟨R.lift x x, hmemU x, hlift x x (R.mem_U x)⟩
  have hsec : ∀ x, ∃ U : Set R.X, IsOpen U ∧ x ∈ U ∧ ∃ s : R.X → (Σ k, J k) → ℂ,
      (∀ y ∈ U, s y ∈ mcPts P ∧ proj (s y) = y) ∧ ∀ p, R.A.HoloOn U fun y => s y p := by
    intro x
    exact ⟨R.U x, R.isOpen_U x, R.mem_U x, fun y => R.lift x y,
      fun y hy => ⟨R.mem x y hy, hlift x y hy⟩, fun p => R.holo x p⟩
  exact ⟨CxModel.mk R.X R.A proj hsurj hfib hcont hsec⟩

end LevelTowerAlt

theorem LevelTowerAlt.nonempty_component_model : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W), Nonempty (XModel D) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hy : ∀ k, ∃ i, D.y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := D.arith.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap]
    simp [h0]
  obtain ⟨R⟩ := GlobalTheory.T.exists_analytic_log_resolution K J Ω D.y D.n D.arith D.smoothGeneric
  exact LevelTowerAlt.cxModel_of_res R (GlobalTheory.T.multiprojective_points_nonempty K J Ω D.y hy)
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_compactified_model : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W), Nonempty (XModel D) := by
  first | exact @LevelTowerAlt.nonempty_component_model | exact LevelTowerAlt.nonempty_component_model
end
