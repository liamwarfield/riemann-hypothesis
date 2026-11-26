module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKleimanScheme

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (df : K → ℕ) (f : MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    IsMultiHomog f df → f ∉ mCoordIdeal y →
    ∃ (n c : ℕ) (B : ℝ) (G : MvPolynomial (Fin (D + 1)) ℤ)
      (Fib : (Fin (D + 1) → ℂ) → Finset ((Σ k, ι k) → ℂ)),
      1 ≤ n ∧ 1 ≤ B ∧ G ≠ 0 ∧
      (∀ ζ : Fin (D + 1) → ℂ, (∀ i, ‖ζ i‖ = 1) → eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 →
        ∀ z ∈ Fib ζ, z ∈ mcPts (mCoordIdeal y) ∧ eval z (map (Int.castRingHom ℂ) f) ≠ 0) ∧
      ∀ τ : ℕ, ∀ u ∈ chartLatNm y A.a τ, u ≠ 0 →
        ∃ F : MvPolynomial (Fin (D + 1)) ℤ, F ≠ 0 ∧ (∀ i, F.degreeOf i ≤ c * (τ + 1)) ∧
          ∀ ζ : Fin (D + 1) → ℂ, (∀ i, ‖ζ i‖ = 1) → eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 →
          ∀ M : ℝ, 0 ≤ M →
            (∀ z ∈ Fib ζ, ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
              (∀ k, (dg k : ℤ) = dh k + τ * A.a k) ∧ aeval y g = u * aeval y h ∧
              eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
              ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
                M * A.h z ^ τ * ‖eval z (map (Int.castRingHom ℂ) h)‖) →
            ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * M ^ n

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountMonoLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter

noncomputable section

theorem chartLat_le_chartLatNm {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) :
    chartLat y a τ ≤ chartLatNm y a τ := by
  intro s hs c hc
  have h := hs c hc
  rw [mem_integralClosure_iff]
  exact isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, h⟩)

theorem smallSectionCount_mono_lattice {Ω : Type*} [CommRing Ω] (P : ℕ → Ω → Prop) {La La' : ℕ → AddSubgroup Ω}
    (τ : ℕ) (hle : La τ ≤ La' τ) (hfin : {s : La' τ | P τ (s : Ω)}.Finite) :
    smallSectionCount P La τ ≤ smallSectionCount P La' τ := by
  unfold smallSectionCount
  have : Finite {s : La' τ // P τ (s : Ω)} := hfin.to_subtype
  have hc : Nat.card {s : La τ // P τ (s : Ω)} ≤ Nat.card {s : La' τ // P τ (s : Ω)} := by
    refine Nat.card_le_card_of_injective
      (fun s => (⟨⟨(s.1 : Ω), hle s.1.2⟩, s.2⟩ : {s : La' τ // P τ (s : Ω)})) ?_
    intro s t hst
    exact Subtype.ext (Subtype.ext (congrArg (fun u : {s : La' τ // P τ (s : Ω)} => ((u.1 : La' τ) : Ω)) hst))
  rcases Nat.eq_zero_or_pos (Nat.card {s : La τ // P τ (s : Ω)}) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hc)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeAnalytic
section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeProj
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

def brQ (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    Fin e → ℂ :=
  fun i => Ψ (segre (R.lift x x)) i.succ / Ψ (segre (R.lift x x)) 0

def brBad (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set R.X :=
  {x | R.lift x x ∈ mcPts J} ∪ {x | Ψ (segre (R.lift x x)) 0 = 0} ∪
    {x | ∃ j, x ∈ (R.A.chart j).source ∧
      ¬ (AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}

def brW (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    ((k : K) → ι k) → ℂ :=
  (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x)

variable (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem brGood : ∀ x ∉ brBad R Ψ, ∀ j, x ∈ (R.A.chart j).source →
    AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
      LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  intro x hx j hj
  by_contra h
  exact hx (Or.inr ⟨j, hj, h⟩)

theorem notMemB_of_notMem_brBad {x : R.X} (hx : x ∉ brBad R Ψ) : R.lift x x ∉ mcPts J :=
  fun h => hx (Or.inl (Or.inl h))

theorem projection_zero_ne_of_notMem_bridgeBadSet {x : R.X} (hx : x ∉ brBad R Ψ) :
    Ψ (segre (R.lift x x)) 0 ≠ 0 :=
  fun h => hx (Or.inl (Or.inr h))

theorem brW_mem_fibre (hK : Nonempty K) (hPh : IsMultiHomogIdeal P) {x : R.X}
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) : brW R Ψ x ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ (brQ R Ψ x) := by
  classical
  obtain ⟨k0⟩ := hK
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (R.lift x x)) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre (R.lift x x)) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * R.lift x x p, mcPts_smul hPh c hc (R.mem x x (R.mem_U x)), ?_, ?_⟩
  · rw [segre_smul, hpc]; rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [brW, h0]
    · simp only [brW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, brQ]
      rw [div_eq_inv_mul]

theorem brW_injOn : Set.InjOn (brW R Ψ) {x | R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0} := by
  intro x hx x' hx' hw
  refine R.inj x x' hx.1 ?_
  refine sameOrbit_of_segre (R.mem x' x' (R.mem_U x')).1
    (Ψ (segre (R.lift x x)) 0 * (Ψ (segre (R.lift x' x')) 0)⁻¹) (by simp [hx.2, hx'.2]) ?_
  have := congrArg (fun v => Ψ (segre (R.lift x x)) 0 • v) hw
  simp only [brW, smul_smul, mul_inv_cancel₀ hx.2, one_smul] at this
  exact this

theorem brFib_finite (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (brQ R Ψ ⁻¹' {y} \ brBad R Ψ).Finite := by
  refine Set.Finite.of_finite_image (f := brW R Ψ) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_)
    ((brW_injOn R Ψ).mono fun x hx => show _ ∧ _ from
      ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩)
  rintro _ ⟨x, hx, rfl⟩
  have := brW_mem_fibre R Ψ hP.1 hP.2.1.2.1 (projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2)
  rwa [show brQ R Ψ x = y from hx.1] at this

theorem exists_of_mem_fibre {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y)
    (hy : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y) :
    ∃ x, R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ brQ R Ψ x = y ∧ brW R Ψ x = w := by
  obtain ⟨z, hz, rfl, hΨz⟩ := hw
  have hzJ : z ∉ mcPts J := fun h => hy ⟨z, hz, h, hΨz⟩
  obtain ⟨x, c, hc, hxc⟩ := R.surj z hz hzJ
  have hseg : segre (R.lift x x) = (∏ k, c k) • segre z := by rw [hxc, segre_smul]
  have hpc : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hΨx : Ψ (segre (R.lift x x)) = (∏ k, c k) • Fin.cons 1 y := by rw [hseg, map_smul, hΨz]
  have h0 : Ψ (segre (R.lift x x)) 0 = ∏ k, c k := by simp [hΨx]
  refine ⟨x, fun h => hzJ ?_, by rw [h0]; exact hpc, ?_, ?_⟩
  · refine mem_mcPts_of_sameOrbit R.homog ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩ h
    funext p
    rw [hxc]
    field_simp [hc p.1]
  · funext i
    simp only [brQ, hΨx, h0, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
    field_simp
  · rw [brW, h0, hseg, smul_smul, inv_mul_cancel₀ hpc, one_smul]

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
  (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem analyticAt_lift_chart (x : R.X) (j : Fin R.A.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :
    AnalyticAt ℂ (fun v => R.lift x ((R.A.chart j).symm v)) u :=
  analyticAt_pi_iff.mpr fun p => R.holo x p j u hu

theorem brQ_eq_local {x z : R.X} (hz : z ∈ R.U x) :
    brQ R Ψ z = fun i => Ψ (segre (R.lift x z)) i.succ / Ψ (segre (R.lift x z)) 0 := by
  obtain ⟨c, hc, hzc⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  have hpc : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  funext i
  simp only [brQ, hzc, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hpc

theorem analyticAt_segre_lift (x : R.X) (j : Fin R.A.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :
    AnalyticAt ℂ (fun v => Ψ (segre (R.lift x ((R.A.chart j).symm v)))) u := by
  classical
  have hl := analyticAt_lift_chart R x j hu
  have hs : AnalyticAt ℂ (fun v => segre (R.lift x ((R.A.chart j).symm v))) u := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    simp only [segre]
    exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _
  exact (LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs

theorem analyticAt_brQ (x : R.X) (j : Fin R.A.n) (hj : x ∈ (R.A.chart j).source)
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) :
    AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) := by
  set u := R.A.chart j x
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  have hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩
  have hH := analyticAt_segre_lift R Ψ x j hu
  have hH0 : AnalyticAt ℂ (fun v => Ψ (segre (R.lift x ((R.A.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Ψ (segre (R.lift x ((R.A.chart j).symm u))) 0 ≠ 0 := by rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun v => fun i : Fin e =>
      Ψ (segre (R.lift x ((R.A.chart j).symm v))) i.succ /
        Ψ (segre (R.lift x ((R.A.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hu,
    hH0.continuousAt.eventually_ne hne] with v hv hv0
  exact (brQ_eq_local R Ψ hv.2).symm

theorem brQ_image_null_of
    (hS : ∀ j, volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' brBad R Ψ) = 0) :
    volume (brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 := by
  set T := brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0}
  have hsub : brQ R Ψ '' T ⊆ ⋃ j, (brQ R Ψ ∘ (R.A.chart j).symm) ''
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' T) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := R.A.cover x
    refine Set.mem_iUnion.mpr ⟨j, R.A.chart j x, ⟨(R.A.chart j).map_source hj, ?_⟩, ?_⟩
    · rw [Set.mem_preimage, (R.A.chart j).left_inv hj]; exact hx
    · simp [(R.A.chart j).left_inv hj]
  refine measure_mono_null hsub (measure_iUnion_null fun j => ?_)
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
    (measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left))
      (hS j))
  intro u hu
  have hx := (R.A.chart j).map_target hu.1
  have hcu : R.A.chart j ((R.A.chart j).symm u) = u := (R.A.chart j).right_inv hu.1
  have := analyticAt_brQ R Ψ _ j hx hu.2.2
  rw [hcu] at this
  exact (this.differentiableAt.restrictScalars ℝ).differentiableWithinAt

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockMetricChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def BlockMetricChange.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (I : AllFam) (d d' : HSMBlockDatum D K ι Ω),
    I.IsFamily → d'.y = d.y → d'.k₀ = d.k₀ →
    (fun n => hsDefect D (blockChi d') (I K ι (mCoordIdeal d'.y) (D + 1) fun _ => d'.A) n -
        hsDefect D (blockChi d) (I K ι (mCoordIdeal d.y) (D + 1) fun _ => d.A) n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMetricToFS
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def MetricToFS.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ),
    I.IsFamily → IsProjFrame d.x e →
    ∃ d₀ : HSMDatum D Ω κ, d₀.x = d.x ∧ IsPullFS d.x e d₀.m ∧
      (fun n => hsDefect D (resChi d₀) (top I d.x d₀.m D) n - hsDefect D (resChi d) (top I d.x d.m D) n)
        =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
