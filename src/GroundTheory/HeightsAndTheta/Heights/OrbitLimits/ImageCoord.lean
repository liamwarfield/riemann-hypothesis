module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLatticeCountVolume
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongRegularise
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDehomogPrime
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageCoord
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem ImageCoord.mConeMap_rename {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (hv : ∀ p, (v p).1 = κ p.1)
    {Ω : Type} [Field Ω] (y : (Σ k', ι' k') → Ω) (f : MRing ι) :
    mConeMap y (rename v f) = rename κ (mConeMap (y ∘ v) f) := by
  have h : ((mConeMap y).comp (rename v : MRing ι →ₐ[ℤ] MRing ι')) =
      ((rename κ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K' Ω).restrictScalars ℤ).comp
        (mConeMap (y ∘ v)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, hv p]
  exact congrArg (fun φ => φ f) h

theorem ImageCoord.proof : ImageCoordStatement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ y hB
  obtain ⟨hκ, -, hv, -⟩ := hB
  ext f
  simp only [imageZ, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, ImageCoord.mConeMap_rename κ v hv y f]
  constructor
  · intro h
    exact rename_injective κ hκ (by rw [h, map_zero])
  · intro h
    rw [h, map_zero]

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsSumMeasurableA
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Metric Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

namespace PtsSumMeasurable

theorem measurable_maDensity {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) :
    Measurable (maDensity φ) := by
  set M : ((Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) → Matrix (Fin D) (Fin D) ℂ := fun H i j =>
    ((H (Pi.single i 1) (Pi.single j 1) +
        H (Complex.I • Pi.single i 1) (Complex.I • Pi.single j 1) : ℝ) +
      Complex.I * ((H (Pi.single i 1) (Complex.I • Pi.single j 1) -
        H (Complex.I • Pi.single i 1) (Pi.single j 1) : ℝ))) / 4 with hMdef
  have hM : Continuous M := continuous_pi fun i => continuous_pi fun j => by
    simp only [hMdef]
    set_option synthInstance.maxHeartbeats 200000 in
      fun_prop
  have hdisc : Continuous fun B : Fin D → Matrix (Fin D) (Fin D) ℂ => (mixedDisc B).re := by
    unfold mixedDisc
    exact Complex.continuous_re.comp (continuous_const.mul (continuous_finsetSum _ fun S _ =>
      continuous_const.mul (Continuous.matrix_det (continuous_finsetSum _ fun k _ =>
        continuous_apply k))))
  have heq : maDensity φ = fun z => (D.factorial : ℝ) * (2 / Real.pi) ^ D *
      (mixedDisc fun k => M (fderiv ℝ (fderiv ℝ (φ k)) z)).re := rfl
  rw [heq]
  exact measurable_const.mul ((hdisc.comp (continuous_pi fun k => hM.comp (continuous_apply k))).measurable.comp
    (Measurable.of_eval fun k => measurable_fderiv ℝ _))

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

theorem exists_lift_family {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y).Finite) :
    ∃ (B : ℕ → Set (Fin e → ℂ)) (γ : ℕ → (Fin e → ℂ) → (Σ k, ι k) → ℂ),
      (∀ m, IsOpen (B m)) ∧
      (∀ m, ∀ y ∈ B m, DifferentiableAt ℂ (γ m) y ∧ γ m y ∈ mcPts P ∧
        Ψ (segre (γ m y)) = Fin.cons 1 y) ∧
      ∀ y w γ', IsSheet P Ψ y w γ' → ∃ m, y ∈ B m ∧ segre (γ m y) = w := by
  classical
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Fin e → ℂ)
  have hρ : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  let Bl : D × ℕ → Set (Fin e → ℂ) := fun p => ball (p.1 : Fin e → ℂ) (1 / (p.2 + 1))
  have : Countable D := hDc.to_subtype
  have : ∀ p : D × ℕ, Countable (secSet P Ψ (Bl p)) := fun p =>
    (secSet_finite osgood hfin (p.1 : Fin e → ℂ) (hρ p.2)).countable.to_subtype
  let T := Σ p : D × ℕ, secSet P Ψ (Bl p)
  let Lift : T → ((Fin e → ℂ) → (Σ k, ι k) → ℂ) → Prop := fun t γ =>
    ∀ y ∈ Bl t.1, DifferentiableAt ℂ γ y ∧ γ y ∈ mcPts P ∧
      segre (γ y) = (t.2 : (Fin e → ℂ) → ((k : K) → ι k) → ℂ) y
  let Bo : Option T → Set (Fin e → ℂ) := fun o =>
    o.elim ∅ fun t => if ∃ γ, Lift t γ then Bl t.1 else ∅
  let γo : Option T → (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun o =>
    o.elim (fun _ _ => 0) fun t => if h : ∃ γ, Lift t γ then h.choose else fun _ _ => 0
  obtain ⟨f, hf⟩ := exists_surjective_nat (Option T)
  have hBsome : ∀ t : T, Bo (some t) = if ∃ γ, Lift t γ then Bl t.1 else ∅ := fun t => rfl
  have hγsome : ∀ t : T, (h : ∃ γ, Lift t γ) → γo (some t) = h.choose := fun t h => by
    show (if h : ∃ γ, Lift t γ then h.choose else fun _ _ => 0) = _
    rw [dite_eq_left h]
  have hBo : ∀ o, IsOpen (Bo o) := by
    rintro (_ | t)
    · exact isOpen_empty
    · rw [hBsome]
      split_ifs
      · exact isOpen_ball
      · exact isOpen_empty
  have hlift : ∀ o, ∀ y ∈ Bo o, DifferentiableAt ℂ (γo o) y ∧ γo o y ∈ mcPts P ∧
      Ψ (segre (γo o y)) = Fin.cons 1 y := by
    rintro (_ | t) y hy
    · exact absurd hy (Set.notMem_empty y)
    · rw [hBsome] at hy
      split_ifs at hy with h
      · rw [hγsome t h]
        obtain ⟨h1, h2, h3⟩ := h.choose_spec y hy
        refine ⟨h1, h2, ?_⟩
        obtain ⟨-, -, hfib⟩ := t.2.2
        obtain ⟨z, -, -, hΨ⟩ := hfib y hy
        rw [h3, hΨ]
      · exact absurd hy (Set.notMem_empty y)
  refine ⟨fun m => Bo (f m), fun m => γo (f m), fun m => hBo (f m), fun m => hlift (f m),
    fun y w γ' hγ' => ?_⟩
  · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hγ'.2
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨d, hdy, hdD⟩ := Metric.dense_iff.mp hDd y _ (hρ n)
    let p : D × ℕ := (⟨d, hdD⟩, n)
    have hyB : y ∈ Bl p := by
      show y ∈ ball d (1 / ((n : ℝ) + 1))
      rw [mem_ball, dist_comm]
      exact hdy
    have hBsub : Bl p ⊆ ball y ε := by
      intro y' hy'
      have hy'' : dist y' d < 1 / ((n : ℝ) + 1) := hy'
      rw [mem_ball] at hdy ⊢
      calc dist y' y ≤ dist y' d + dist d y := dist_triangle _ _ _
        _ < 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := add_lt_add hy'' hdy
        _ < ε := by linarith
    have hG := mem_secSet_of_sheet (P := P) (Ψ := Ψ) (B := Bl p) (γ := γ') fun y' hy' =>
      hball y' (hBsub hy')
    let t : T := ⟨p, _, hG⟩
    have hL : ∃ γ, Lift t γ := ⟨γ', fun y' hy' => ⟨(hball y' (hBsub hy')).1,
      (hball y' (hBsub hy')).2.1, by simp only [t]; rw [Set.indicator_of_mem hy']⟩⟩
    obtain ⟨m, hm⟩ := hf (some t)
    refine ⟨m, ?_, ?_⟩
    · show y ∈ Bo (f m)
      rw [hm, hBsome, if_pos hL]
      exact hyB
    · show segre (γo (f m) y) = w
      rw [hm, hγsome t hL, (hL.choose_spec y hyB).2.2]
      simp only [t]
      rw [Set.indicator_of_mem hyB, hγ'.1]

end PtsSumMeasurable

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCriticalFibreInfinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Topology Metric

noncomputable section

theorem CriticalFibreInfinite.proof : CriticalFibreInfinite.Statement := by
  intro k d U f hU hUne hf hninj
  classical
  have hfa : AnalyticOnNhd ℂ f U :=
    GroundTheory.Heights₂.Heights.ImplicitCurve.analyticOnNhd_of_differentiableOn hU hf

  let Q : ℕ → Prop := fun m => ∃ t ∈ U, ∃ v : Fin m → Fin k → ℂ,
    LinearIndependent ℂ (fun j => fderiv ℂ f t (v j))
  have hQ0 : Q 0 := by
    obtain ⟨t, ht⟩ := hUne
    exact ⟨t, ht, Fin.elim0, linearIndependent_empty_type⟩
  have hspec : Q (Nat.findGreatest Q d) := Nat.findGreatest_spec (Nat.zero_le d) hQ0
  have hle : ∀ m, m ≤ d → Q m → m ≤ Nat.findGreatest Q d := fun m hmd hm => Nat.le_findGreatest hmd hm
  have hrd : Nat.findGreatest Q d ≤ d := Nat.findGreatest_le d
  generalize Nat.findGreatest Q d = r at hspec hle hrd
  obtain ⟨s, hs, v, hv⟩ := hspec
  have hmax : ∀ t ∈ U, ∀ u : Fin (r + 1) → Fin k → ℂ,
      ¬ LinearIndependent ℂ (fun j => fderiv ℂ f t (u j)) := by
    intro t ht u hu
    have hcard : r + 1 ≤ d := by simpa using hu.fintype_card_le_finrank
    have := hle (r + 1) hcard ⟨t, ht, u, hu⟩
    omega

  let T : (Fin r → ℂ) →ₗ[ℂ] (Fin d → ℂ) := Fintype.linearCombination ℂ (fun j => fderiv ℂ f s (v j))
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    funext j
    exact Fintype.linearIndependent_iff.1 hv c (by simpa [T, Fintype.linearCombination_apply] using hc) j
  obtain ⟨Λ, hΛ⟩ := T.exists_leftInverse_of_injective hT
  have hΛv : ∀ j, Λ (fderiv ℂ f s (v j)) = Pi.single j 1 := by
    intro j
    have := congrArg (fun g => g (Pi.single j (1 : ℂ))) hΛ
    simpa [T, Fintype.linearCombination_apply_single] using this
  let Λc : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ) := LinearMap.toContinuousLinearMap Λ
  have hΛc : ∀ y, Λc y = Λ y := fun y => rfl

  have hev : ∀ᶠ t in 𝓝 s, t ∈ U ∧ LinearIndependent ℂ (fun j => Λ (fderiv ℂ f t (v j))) := by
    have hUev : ∀ᶠ t in 𝓝 s, t ∈ U := hU.mem_nhds hs
    refine hUev.and ?_
    have hDcont : ContinuousAt (fderiv ℂ f) s := (hfa.fderiv s hs).continuousAt
    have hc : ContinuousAt (fun t => fun j => Λc (fderiv ℂ f t (v j))) s := by
      refine continuousAt_pi.2 fun j => ?_
      exact Λc.continuous.continuousAt.comp
        ((ContinuousLinearMap.apply ℂ (Fin d → ℂ) (v j)).continuous.continuousAt.comp hDcont)
    have h0 : LinearIndependent ℂ (fun j => Λc (fderiv ℂ f s (v j))) := by
      have : (fun j => Λc (fderiv ℂ f s (v j))) = ⇑(Pi.basisFun ℂ (Fin r)) := by
        funext j
        simp [hΛc, hΛv]
      rw [this]
      exact (Pi.basisFun ℂ (Fin r)).linearIndependent
    exact hc.eventually h0.eventually

  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ LinearMap.ker (Λ ∘ₗ (fderiv ℂ f s : (Fin k → ℂ) →ₗ[ℂ] (Fin d → ℂ))), w ≠ 0 := by
    obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.1 (hninj s hs)
    refine ⟨x - y, ?_, sub_ne_zero.2 hne⟩
    simp [map_sub, hxy]
  have hw' : Λ (fderiv ℂ f s w) = 0 := by simpa using hw

  let A' : ℂ × (Fin r → ℂ) →L[ℂ] (Fin k → ℂ) :=
    (ContinuousLinearMap.fst ℂ ℂ (Fin r → ℂ)).smulRight w +
      ∑ j, ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ ℂ (Fin r → ℂ))).smulRight (v j)
  have hA' : ∀ p : ℂ × (Fin r → ℂ), A' p = p.1 • w + ∑ j, p.2 j • v j := by
    intro p
    simp [A']
  have hLA : ∀ p : ℂ × (Fin r → ℂ), Λ (fderiv ℂ f s (A' p)) = p.2 := by
    intro p
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hA', map_add (f := _), map_add (f := _), map_smul, map_smul, hw', smul_zero, zero_add, map_sum, map_sum]
    simp only [map_smul, hΛv]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  let H : ℂ × (Fin r → ℂ) → Fin r → ℂ := fun p => Λc (f (s + A' p))
  have hfs : AnalyticAt ℂ f s := hfa s hs
  have hHd : HasFDerivAt H (Λc.comp ((fderiv ℂ f s).comp A')) 0 := by
    have h1 : HasFDerivAt (fun p => s + A' p) A' (0 : ℂ × (Fin r → ℂ)) := A'.hasFDerivAt.const_add s
    have h2 : HasFDerivAt f (fderiv ℂ f s) (s + A' 0) := by
      simpa using hfs.differentiableAt.hasFDerivAt
    exact Λc.hasFDerivAt.comp _ (HasFDerivAt.comp (f := fun p => s + A' p) (0 : ℂ × (Fin r → ℂ)) h2 h1)
  have hHc : ContDiffAt ℂ 1 H 0 := by
    have hf1 : ContDiffAt ℂ 1 f (s + A' 0) := by simpa using hfs.contDiffAt
    exact Λc.contDiff.contDiffAt.comp _
      (ContDiffAt.comp (f := fun p => s + A' p) (0 : ℂ × (Fin r → ℂ)) hf1 (contDiff_const.add A'.contDiff).contDiffAt)
  have hinv : (fderiv ℂ H 0 ∘L ContinuousLinearMap.inr ℂ ℂ (Fin r → ℂ)).IsInvertible := by
    have : fderiv ℂ H 0 ∘L ContinuousLinearMap.inr ℂ ℂ (Fin r → ℂ) =
        ContinuousLinearMap.id ℂ (Fin r → ℂ) := by
      rw [hHd.fderiv]
      refine ContinuousLinearMap.ext fun c => ?_
      simpa [hΛc] using hLA (0, c)
    rw [this]
    exact ⟨ContinuousLinearEquiv.refl ℂ _, rfl⟩

  have hψc := hHc.contDiffAt_implicitFunction one_ne_zero hinv
  set ψ := hHc.implicitFunction one_ne_zero hinv with hψ
  have hψ0 : ψ 0 = 0 := hHc.implicitFunction_apply_self one_ne_zero hinv
  have hψeq : ∀ᶠ z in 𝓝 (0 : ℂ), H (z, ψ z) = H 0 :=
    hHc.eventually_apply_implicitFunction one_ne_zero hinv
  have hψd : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ ψ z :=
    (hψc.eventually (by simp)).mono fun z hz => hz.differentiableAt one_ne_zero
  let P : ℂ → Fin k → ℂ := fun z => s + A' (z, ψ z)
  have hP0 : P 0 = s := by simp [P, hψ0, hA']
  have hPcont : ContinuousAt P 0 :=
    continuousAt_const.add (A'.continuous.continuousAt.comp (continuousAt_id.prodMk hψc.continuousAt))
  rw [← hP0] at hev
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.eventually_nhds_iff_ball.1 (((hPcont.eventually hev).and hψeq).and hψd)
  have hPd : ∀ z ∈ ball (0 : ℂ) δ, DifferentiableAt ℂ P z := fun z hz =>
    (differentiableAt_const _).add (A'.differentiableAt.comp z (differentiableAt_id.prodMk (hball z hz).2))
  have hPU : ∀ z ∈ ball (0 : ℂ) δ, P z ∈ U := fun z hz => (hball z hz).1.1.1
  have hfd : ∀ z ∈ ball (0 : ℂ) δ, DifferentiableAt ℂ f (P z) := fun z hz =>
    (hf _ (hPU z hz)).differentiableAt (hU.mem_nhds (hPU z hz))
  have hgP : ∀ z ∈ ball (0 : ℂ) δ, Λc (f (P z)) = Λc (f s) := by
    intro z hz
    have := (hball z hz).1.2
    simpa [H, P] using this

  have hzero : Set.EqOn (fderiv ℂ (fun z => f (P z))) 0 (ball (0 : ℂ) δ) := by
    intro z hz
    have hcomp : fderiv ℂ (fun z => f (P z)) z = (fderiv ℂ f (P z)).comp (fderiv ℂ P z) :=
      fderiv_comp z (hfd z hz) (hPd z hz)
    have hloc : (fun z => Λc (f (P z))) =ᶠ[𝓝 z] fun _ => Λc (f s) :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) hgP
    have hg0 : fderiv ℂ (fun z => Λc (f (P z))) z = 0 := by
      rw [hloc.fderiv_eq]
      exact fderiv_const_apply _
    have hgc : fderiv ℂ (fun z => Λc (f (P z))) z = Λc.comp ((fderiv ℂ f (P z)).comp (fderiv ℂ P z)) := by
      rw [← hcomp]
      have h := fderiv_comp z Λc.differentiableAt ((hfd z hz).comp z (hPd z hz))
      rw [ContinuousLinearMap.fderiv] at h
      exact h
    have hx : Λ (fderiv ℂ f (P z) (fderiv ℂ P z 1)) = 0 := by
      have := congrArg (fun L => L 1) (hgc.symm.trans hg0)
      simpa [hΛc] using this
    have := IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.kernel_eq_of_maximal (fderiv ℂ f (P z)) v Λ (hmax _ (hPU z hz)) (hball z hz).1.1.2 hx
    rw [hcomp]
    refine ContinuousLinearMap.ext_ring ?_
    simpa using this
  have hconst : ∀ z ∈ ball (0 : ℂ) δ, f (P z) = f s := by
    intro z hz
    have := isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball (0 : ℂ) δ).isPreconnected
      (fun z hz => ((hfd z hz).comp z (hPd z hz)).differentiableWithinAt) hzero hz (mem_ball_self hδ)
    simpa [hP0] using this

  have hPinj : Function.Injective P := by
    intro z z' hzz
    have hψz : ψ z = ψ z' := by
      have h1 := hLA (z, ψ z)
      have h2 := hLA (z', ψ z')
      have : A' (z, ψ z) = A' (z', ψ z') := add_left_cancel hzz
      rw [this] at h1
      exact h1.symm.trans h2
    have : A' (z, ψ z) = A' (z', ψ z') := add_left_cancel hzz
    rw [hA', hA', hψz] at this
    have h3 : z • w = z' • w := add_right_cancel this
    exact smul_left_injective ℂ hw0 h3
  refine ⟨f s, ?_⟩
  have hinf : (ball (0 : ℂ) δ).Infinite := infinite_of_mem_nhds (0 : ℂ) (ball_mem_nhds 0 hδ)
  refine (hinf.image hPinj.injOn).mono ?_
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨hPU z hz, hconst z hz⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLocalMultComap
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights (localMult)

theorem LocalMultComap.proof : LocalMultComap.Statement := by
  intro R S _ _ σ I W hσ hW
  set P := W.comap σ with hPdef
  have hPW : P = W.comap σ := rfl
  unfold localMult
  rw [dite_eq_left hW, dite_eq_left (Ideal.comap_isPrime σ W)]

  have hM : P.primeCompl.map σ = W.primeCompl := by
    ext y
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := hσ y
      exact ⟨x, hy, rfl⟩
  have : IsLocalization (P.primeCompl.map σ) (Localization.AtPrime W) := by
    rw [hM]; infer_instance
  let φ : Localization.AtPrime P →+* Localization.AtPrime W := Localization.localRingHom P W σ hPW
  have hφ : Function.Surjective φ := IsLocalization.map_surjective_of_surjective _ _ _ hσ
  let _ : Algebra (Localization.AtPrime P) (Localization.AtPrime W) := φ.toAlgebra
  set J : Ideal (Localization.AtPrime P) := (I.comap σ).map (algebraMap R (Localization.AtPrime P))
  set I' : Ideal (Localization.AtPrime W) := I.map (algebraMap S (Localization.AtPrime W))
  have hcomp : φ.comp (algebraMap R (Localization.AtPrime P)) =
      (algebraMap S (Localization.AtPrime W)).comp σ :=
    RingHom.ext fun x => Localization.localRingHom_to_map P W σ hPW x
  have hJ : J.map φ = I' := by
    simp only [J, I', Ideal.map_map, hcomp]
    rw [← Ideal.map_map, Ideal.map_comap_of_surjective σ hσ]
  have hker : RingHom.ker φ ≤ J := by
    intro x hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    have h0 : φ (IsLocalization.mk' _ r s) = 0 := hx
    simp only [φ, Localization.localRingHom, IsLocalization.map_mk'] at h0
    obtain ⟨⟨t, ht⟩, htr⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp h0
    obtain ⟨t', rfl⟩ := hσ t
    have hmem : t' * r ∈ I.comap σ := by
      simp only [Ideal.mem_comap, map_mul]
      rw [htr]; exact I.zero_mem
    have ht' : t' ∈ P.primeCompl := ht
    rw [IsLocalization.mk'_mem_iff]
    have h1 : algebraMap R (Localization.AtPrime P) (t' * r) ∈ J := Ideal.mem_map_of_mem _ hmem
    rw [map_mul] at h1
    have hu : IsUnit (algebraMap R (Localization.AtPrime P) t') :=
      IsLocalization.map_units _ (⟨t', ht'⟩ : P.primeCompl)
    exact (Submodule.smul_mem_iff_of_isUnit J hu).mp h1

  let ψ : Localization.AtPrime P →ₐ[Localization.AtPrime P] Localization.AtPrime W ⧸ I' :=
    (Ideal.Quotient.mkₐ _ I').comp (Algebra.ofId (Localization.AtPrime P) (Localization.AtPrime W))
  have hψ : Function.Surjective ψ :=
    (Ideal.Quotient.mkₐ_surjective (Localization.AtPrime P) I').comp hφ
  have hkerψ : RingHom.ker ψ = J := by
    have : RingHom.ker ψ = I'.comap φ := by
      ext x
      simp only [ψ, RingHom.mem_ker, Ideal.mem_comap, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Algebra.ofId_apply]
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [this, ← hJ, Ideal.comap_map_of_surjective' φ hφ, sup_eq_left.mpr hker]
  have e := (Submodule.quotEquivOfEq J (RingHom.ker ψ) hkerψ.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hψ).toLinearEquiv
  rw [e.length_eq, Module.length_eq_of_surjective hφ]

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFnDegRelDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

universe u

namespace FnDegRelDeg

theorem exists_div_of_mem_adjoin {F R L : Type*} [Field F] [CommRing R] [Field L] [Algebra F L]
    (τ : R →+* L) (hF : ∀ c : F, ∃ x, τ x = algebraMap F L c) {z : L}
    (hz : z ∈ IntermediateField.adjoin F (Set.range τ)) : ∃ x y, z = τ x / τ y := by
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.1 hz
  let S : Subalgebra F L := { τ.rangeS with algebraMap_mem' := fun c => RingHom.mem_rangeS.2 (hF c) }
  have hle : Algebra.adjoin F (Set.range τ) ≤ S :=
    Algebra.adjoin_le (by rintro _ ⟨x, rfl⟩; exact RingHom.mem_rangeS.2 ⟨x, rfl⟩)
  obtain ⟨x, rfl⟩ := RingHom.mem_rangeS.1 (hle hr)
  obtain ⟨y, rfl⟩ := RingHom.mem_rangeS.1 (hle hs)
  exact ⟨x, y, rfl⟩

theorem isFractionRing_codRestrict {R L F' : Type*} [CommRing R] [Field L] [Field F'] [Algebra F' L]
    (E : IntermediateField F' L) (τ : R →+* L) (hτ : Function.Injective τ) (hmem : ∀ x, τ x ∈ E)
    (hq : ∀ z ∈ E, ∃ x y, z = τ x / τ y) :
    letI := (τ.codRestrict E hmem).toAlgebra
    IsFractionRing R E := by
  let _ := (τ.codRestrict E hmem).toAlgebra
  have hinj : Function.Injective (algebraMap R E) := fun a b h => hτ (congrArg Subtype.val h)
  have : FaithfulSMul R E := (faithfulSMul_iff_algebraMap_injective R E).2 hinj
  refine IsFractionRing.of_field R E fun z => ?_
  obtain ⟨x, y, hxy⟩ := hq z z.2
  refine ⟨x, y, Subtype.ext ?_⟩
  rw [IntermediateField.coe_div]
  exact hxy

theorem finrank_eq_relfinrank {F R₁ R₂ L : Type*} [Field F] [CommRing R₁] [CommRing R₂] [Field L]
    [Algebra F L] [Algebra R₁ R₂] (ρ : R₂ →+* L) (hρ : Function.Injective ρ)
    (E H : IntermediateField F L) (hEH : E ≤ H)
    (hτ : Function.Injective (ρ.comp (algebraMap R₁ R₂)))
    (hτE : ∀ x, ρ (algebraMap R₁ R₂ x) ∈ E) (hρH : ∀ x, ρ x ∈ H)
    (hEq : ∀ z ∈ E, ∃ x y, z = ρ (algebraMap R₁ R₂ x) / ρ (algebraMap R₁ R₂ y))
    (hHq : ∀ z ∈ H, ∃ x y, z = ρ x / ρ y) :
    Module.finrank R₁ R₂ = IntermediateField.relfinrank E H := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le hEH]
  set H' := IntermediateField.extendScalars hEH
  have hρH' : ∀ x, ρ x ∈ H' := fun x => (IntermediateField.mem_extendScalars hEH).2 (hρH x)
  let _ : Algebra R₁ E := ((ρ.comp (algebraMap R₁ R₂)).codRestrict E hτE).toAlgebra
  let _ : Algebra R₂ H' := (ρ.codRestrict H' hρH').toAlgebra
  let _ : Algebra R₁ H' := ((algebraMap R₂ H').comp (algebraMap R₁ R₂)).toAlgebra
  have : IsScalarTower R₁ R₂ H' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R₁ E H' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsFractionRing R₁ E := isFractionRing_codRestrict E _ hτ hτE hEq
  have : IsFractionRing R₂ H' := isFractionRing_codRestrict H' ρ hρ hρH' fun z hz =>
    hHq z ((IntermediateField.mem_extendScalars hEH).1 hz)
  exact (IsFractionRing.finrank_eq R₁ E R₂ H').symm

section Dehom

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem dehom_mem_homFracDegZero (V : Ideal (MRing ι F)) [V.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V) (f : MRing ι F) :
    IntNumPoint.dehom V i f ∈ homFracDegZero V := by
  have : (IntNumPoint.dehom V i).range ≤ (homFracDegZero V).toSubalgebra := by
    rw [IntNumPoint.dehom, aeval_range]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨p, rfl⟩
    exact IntermediateField.subset_adjoin F _
      ⟨blockWeight ι p, X p, X ⟨p.1, i p.1⟩, isWeightedHomogeneous_X (R := F) _ _,
        isWeightedHomogeneous_X (R := F) _ _, hi p.1, rfl⟩
  exact this ⟨f, rfl⟩

theorem div_eq_dehom_div (V : Ideal (MRing ι F)) [V.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V) {b : K → ℕ} {f g : MRing ι F}
    (hf : NumbersDVR.IsMultiHomog f b) (hg : NumbersDVR.IsMultiHomog g b) :
    algebraMap (MRing ι F ⧸ V) (FractionRing (MRing ι F ⧸ V)) (Ideal.Quotient.mk V f) /
        algebraMap (MRing ι F ⧸ V) (FractionRing (MRing ι F ⧸ V)) (Ideal.Quotient.mk V g) =
      IntNumPoint.dehom V i f / IntNumPoint.dehom V i g := by
  rw [← IntNumPoint.cls_apply, ← IntNumPoint.cls_apply,
    ← IntNumPoint.dehom_mul_of_isMultiHomog i hi hf, ← IntNumPoint.dehom_mul_of_isMultiHomog i hi hg,
    mul_div_mul_right _ _ (IntNumPoint.chartProd_ne_zero i hi b)]

end Dehom

section Contract

variable {F : Type u} [Field F] {K K' : Type} {ι' : K' → Type} (j : K ↪ K') (P' : Ideal (MRing ι' F))
  [P'.IsPrime] (i' : ∀ k', ι' k')

theorem contractFracMap_algebraMap (f : MRing (fun k => ι' (j k)) F) :
    contractFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (contractPrime j P') f)) =
      algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))
        (Ideal.Quotient.mk P' (rename (blockIncl j ι') f)) := by
  simp [contractFracMap, contractQuot]
  rfl

theorem contractFracMap_comp_dehom :
    (contractFracMap j P').comp (IntNumPoint.dehom (contractPrime j P') (fun k => i' (j k))) =
      (IntNumPoint.dehom P' i').comp (rename (blockIncl j ι')) := by
  refine MvPolynomial.algHom_ext fun r => ?_
  simp only [AlgHom.comp_apply, IntNumPoint.dehom, aeval_X, rename_X, map_div₀, IntNumPoint.xc,
    contractFracMap_algebraMap]
  rfl

end Contract

theorem proof : FnDegRelDeg.Statement.{u} := by
  intro F _ K K' _ _ _ _ ι _ ι' _ κ v hκv P' hP' i' hi
  have := hP'.isPrime
  set j : K ↪ K' := ⟨κ, hκv.1⟩

  have hu : ∀ q : Σ k, ι k, ∃ r : ι' (j q.1), blockIncl j ι' ⟨q.1, r⟩ = v q := by
    intro q
    have h := hκv.2.2.1 q
    revert h
    generalize v q = q'
    obtain ⟨k', r⟩ := q'
    rintro (h : k' = κ q.1)
    subst h
    exact ⟨r, rfl⟩
  let ucoord : (Σ k, ι k) → (Σ k, ι' (j k)) := fun q => ⟨q.1, (hu q).choose⟩
  have hucoord : blockIncl j ι' ∘ ucoord = v := funext fun q => (hu q).choose_spec
  have hw : ∀ r : Σ k, ι' (j k), ∃ q, v q = blockIncl j ι' r := fun r => hκv.2.2.2 _ ⟨r.1, rfl⟩
  let wcoord : (Σ k, ι' (j k)) → (Σ k, ι k) := fun r => (hw r).choose
  have hwcoord : v ∘ wcoord = blockIncl j ι' := funext fun r => (hw r).choose_spec
  have hi0 : ∀ k, (X ⟨k, i' (j k)⟩ : MRing (fun k => ι' (j k)) F) ∉ contractPrime j P' := by
    intro k h
    have h' := Ideal.mem_comap.1 h
    rw [rename_X] at h'
    exact hi (j k) h'

  let ρ := Ideal.Quotient.liftₐ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal P' i') (IntNumPoint.dehom P' i')
    (fun a ha => IntNumPoint.dehom_eq_zero_of_mem_chartIdeal i' hi hP'.multiHomog ha)
  have hρ : ∀ f, ρ (Ideal.Quotient.mk _ f) = IntNumPoint.dehom P' i' f := fun f => rfl
  have hρinj : Function.Injective ρ := by
    refine (injective_iff_map_eq_zero ρ).2 fun a ha => ?_
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hρ] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 (IntNumPoint.mem_chartIdeal_of_dehom_eq_zero i' hi ha)
  let _ := (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i').toAlgebra
  have hτ : ∀ p : MRing ι F, ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' (Ideal.Quotient.mk _ p)) =
      IntNumPoint.dehom P' i' (rename v p) := fun p => rfl
  have key : ∀ p : MRing ι F, IntNumPoint.dehom P' i' (rename v p) =
      contractFracMap j P' (IntNumPoint.dehom (contractPrime j P') (fun k => i' (j k))
        (rename ucoord p)) := by
    intro p
    have e : rename v p = rename (blockIncl j ι') (rename ucoord p) := by
      rw [rename_rename, hucoord]
    rw [e]
    exact (AlgHom.congr_fun (contractFracMap_comp_dehom j P' i') _).symm
  have key2 : ∀ f, contractFracMap j P' (IntNumPoint.dehom (contractPrime j P')
      (fun k => i' (j k)) f) =
      ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' (Ideal.Quotient.mk _ (rename wcoord f))) := by
    intro f
    rw [hτ, rename_rename, hwcoord]
    exact AlgHom.congr_fun (contractFracMap_comp_dehom j P' i') f
  have hρH : ∀ x, ρ x ∈ homFracDegZero P' := by
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact dehom_mem_homFracDegZero P' i' hi f
  have hτE : ∀ x, ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' x) ∈
      (homFracDegZero (contractPrime j P')).map (contractFracMap j P') := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hτ, key]
    exact (IntermediateField.mem_map _).2 ⟨_, dehom_mem_homFracDegZero _ _ hi0 _, rfl⟩
  have hHq : ∀ z ∈ homFracDegZero P', ∃ x y, z = ρ x / ρ y := by
    intro z hz
    refine exists_div_of_mem_adjoin ρ.toRingHom (fun c => ⟨algebraMap F _ c, ρ.commutes c⟩) ?_
    revert z
    show homFracDegZero P' ≤ _
    unfold homFracDegZero
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨b, f, g, hf, hg, hgP, rfl⟩
    rw [div_eq_dehom_div P' i' hi hf hg]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨Ideal.Quotient.mk _ f, rfl⟩)
      (IntermediateField.subset_adjoin _ _ ⟨Ideal.Quotient.mk _ g, rfl⟩)
  have hEq : ∀ z ∈ (homFracDegZero (contractPrime j P')).map (contractFracMap j P'),
      ∃ x y, z = ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' x) /
        ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' y) := by
    intro z hz
    refine exists_div_of_mem_adjoin (ρ.toRingHom.comp (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i'))
      (fun c => ⟨Ideal.Quotient.mk _ (C c), ?_⟩) ?_
    · show ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' (Ideal.Quotient.mk _ (C c))) = _
      rw [hτ, rename_C]
      exact (IntNumPoint.dehom P' i').commutes c
    revert z
    show (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤ _
    unfold homFracDegZero
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨_, ⟨d, f, g, hf, hg, hgP, rfl⟩, rfl⟩
    rw [div_eq_dehom_div _ _ hi0 hf hg, map_div₀, key2, key2]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨Ideal.Quotient.mk _ (rename wcoord f), rfl⟩)
      (IntermediateField.subset_adjoin _ _ ⟨Ideal.Quotient.mk _ (rename wcoord g), rfl⟩)
  have hEH : (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤
      homFracDegZero P' := by
    intro z hz
    obtain ⟨x, y, rfl⟩ := hEq z hz
    exact div_mem (hρH _) (hρH _)
  unfold ReciprocityTheory.ChartRestriction.G.AI.I1.fnDeg relDeg
  exact finrank_eq_relfinrank ρ.toRingHom hρinj _ _ hEH
    (fun a b h => Ideal.quotientMap_injective (hρinj h)) hτE hρH hEq hHq

end FnDegRelDeg

end

end GroundTheory.Heights₂.Heights.Targets
end
