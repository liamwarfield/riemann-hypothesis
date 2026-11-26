module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

def IsMultilinFam (II : AllFam) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (j : Fin n) (A B : HermLine ι),
    IsArithVar P n → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    II K ι P n (Function.update L j (A.tensor B)) =
      II K ι P n (Function.update L j A) + II K ι P n (Function.update L j B)

def HasPFCoord (II : AllFam) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k', ι' k') → Ω) (d : ℕ) (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι'),
    IsBlockMap κ v → IsArithVar (mCoordIdeal y) d → IsArithVar (imageZ v (mCoordIdeal y)) d →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
    II K' ι' (mCoordIdeal y) d L' =
      (IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) : ℝ) *
        II K ι (imageZ v (mCoordIdeal y)) d L

def HasContractMixed (II : AllFam) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d₀ d r : ℕ)
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι'),
    IsBlockMap κ v → IsArithVar P' (d + r) → IsArithVar (imageZ v P') d₀ → d₀ < d →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
    II K' ι' P' (d + r) (Fin.append L' N) = 0

def IsFullIntersectionSystem (II : IntersectionSystem) : Prop :=
  IsIntersectionSystem II ∧ IsMultilinFam II ∧ HasPFCoord II ∧ HasContractMixed II

def ArithIntersectionSystemStatement : Prop :=
  ∃ II : IntersectionSystem, IsFullIntersectionSystem II

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDerived
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.ChartRestriction.G.AI.I2

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem divSupp_one (P : Ideal (MRing ι)) : divSupp P 1 = ∅ := by
  ext W
  simp only [divSupp, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hW
  have hp := hW.1
  have htop : (⊤ : Ideal (MRing ι)) ≤ W := by
    have h2 := hp.2
    rwa [Ideal.span_singleton_one, sup_top_eq] at h2
  exact fun _ => hp.1.ne_top (top_le_iff.1 htop)

theorem logNorm_ofWeight_one (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) (z : (Σ k, ι k) → ℂ) :
    logNorm (HermLine.ofWeight u hu) 1 z = u z := by
  simp [logNorm, HermLine.ofWeight, Real.exp_neg, Real.log_exp]

theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) (fun _ => 0) := by
  intro m hm k
  rw [MvPolynomial.support_one] at hm
  simp only [Finset.mem_singleton] at hm
  subst hm
  simp

theorem metricChange : MetricChangeStatement := by
  intro K _ ι _ I hI P n L A u hu hP hL hA hsm
  have hB : IsSmoothHerm (HermLine.ofWeight u hu) := by
    show ContDiffOn ℝ _ (fun z => Real.exp (-u z)) _
    exact hsm.neg.exp
  have h1 : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hlog : logNorm (HermLine.ofWeight u hu) 1 = u := funext (logNorm_ofWeight_one u hu)
  have hrec : recR I P L (HermLine.ofWeight u hu) 1 = -ptsIntegral P (pot L) u := by
    unfold recR
    rw [divSupp_one]
    simp only [finsum_mem_empty, zero_sub, arInt, hlog]
    rfl
  rw [hI.2.1 P n L A _ hP hL hA hB,
    hI.2.2 P n L _ 1 (fun _ => 0) hP hL hB (fun _ => rfl) isMultiHomog_one h1, hrec]
  ring

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {e : ℕ}

theorem continuousOn_lift (R : AnLogRes P J e) (x : R.X) (p : Σ k, ι k) :
    ContinuousOn (fun z => R.lift x z p) (R.U x) := by
  intro z hz
  obtain ⟨j, hj⟩ := R.A.cover z
  have ha : AnalyticAt ℂ ((fun w => R.lift x w p) ∘ (R.A.chart j).symm) (R.A.chart j z) :=
    R.holo x p j _ ⟨(R.A.chart j).map_source hj, by
      simp only [Set.mem_preimage, (R.A.chart j).left_inv hj]; exact hz⟩
  have hc : ContinuousAt (((fun w => R.lift x w p) ∘ (R.A.chart j).symm) ∘ (R.A.chart j)) z :=
    ha.continuousAt.comp ((R.A.chart j).continuousAt hj)
  refine (hc.congr ?_).continuousWithinAt
  filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with w hw
  simp only [Function.comp_apply, (R.A.chart j).left_inv hw]

private theorem smoothOn_potOf_of_isSmoothHerm (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L)
    (x : R.X) : R.A.SmoothOn ((potOf R L).U x) ((potOf R L).φ x) := by
  intro j
  have hlift : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => R.lift x ((R.A.chart j).symm w))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) := by
    refine contDiffOn_pi.mpr fun p => ?_
    exact ((R.holo x p j).contDiffOn ((R.A.chart j).isOpen_inter_preimage_symm
      (R.isOpen_U x)).uniqueDiffOn).restrict_scalars ℝ
  have hcomp := (hL : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L.h _).comp hlift (fun w hw => (R.mem x _ hw.2).1)
  exact hcomp.log fun w hw => (L.pos _ (R.mem x _ hw.2).1).ne'

private theorem exists_holo_re_eq_potOf_sub_on_overlap (R : AnLogRes P J e) (L : HermLine ι) (x x' y : R.X)
    (hy : y ∈ R.U x ∩ R.U x') : ∃ W : Set R.X, IsOpen W ∧ y ∈ W ∧ ∃ G : R.X → ℂ,
      R.A.HoloOn W G ∧ ∀ z ∈ W ∩ R.U x ∩ R.U x',
        (potOf R L).φ x z - (potOf R L).φ x' z = (G z).re := by
  classical
  obtain ⟨c, hc, hxy⟩ := R.compat x x' y hy
  choose i hi using (R.mem x' y hy.2).1
  have hVo : IsOpen (R.U x ∩ R.U x') := (R.isOpen_U x).inter (R.isOpen_U x')
  have hcx : ∀ p, ContinuousOn (fun z => R.lift x z p) (R.U x ∩ R.U x') := fun p =>
    (continuousOn_lift R x p).mono Set.inter_subset_left
  have hcx' : ∀ p, ContinuousOn (fun z => R.lift x' z p) (R.U x ∩ R.U x') := fun p =>
    (continuousOn_lift R x' p).mono Set.inter_subset_right
  let r : K → R.X → ℂ := fun k z => R.lift x z ⟨k, i k⟩ / R.lift x' z ⟨k, i k⟩ / c k
  let D : K → Set R.X := fun k => (R.U x ∩ R.U x') ∩ (fun z => R.lift x' z ⟨k, i k⟩) ⁻¹' {0}ᶜ
  have hD : ∀ k, IsOpen (D k) := fun k => (hcx' _).isOpen_inter_preimage hVo isOpen_compl_singleton
  have hr : ∀ k, ContinuousOn (r k) (D k) := fun k =>
    (((hcx _).mono Set.inter_subset_left).div ((hcx' _).mono Set.inter_subset_left)
      (fun z hz => hz.2)).div_const _
  let W : Set R.X := (R.U x ∩ R.U x') ∩ ⋂ k, (D k ∩ r k ⁻¹' Complex.slitPlane)
  have hW : IsOpen W :=
    hVo.inter (isOpen_iInter_of_finite fun k =>
      (hr k).isOpen_inter_preimage (hD k) Complex.isOpen_slitPlane)
  have hlk : ∀ k, R.lift x y ⟨k, i k⟩ = c k * R.lift x' y ⟨k, i k⟩ := fun k => congrFun hxy _
  have hyW : y ∈ W := by
    refine ⟨hy, Set.mem_iInter.mpr fun k => ⟨⟨hy, hi k⟩, ?_⟩⟩
    have : r k y = 1 := by
      simp only [r, hlk k]
      field_simp [hi k, hc k]
    simp only [Set.mem_preimage, this]
    exact Complex.one_mem_slitPlane
  refine ⟨W, hW, hyW, fun z => ∑ k, (L.a k : ℂ) * (Complex.log (r k z) + (Real.log ‖c k‖ : ℂ)),
    ?_, ?_⟩
  · intro j w hw
    have hzV : (R.A.chart j).symm w ∈ R.U x ∩ R.U x' := hw.2.1
    have hzk := fun k => Set.mem_iInter.mp hw.2.2 k
    have ha : ∀ p, AnalyticAt ℂ (fun w => R.lift x ((R.A.chart j).symm w) p) w := fun p =>
      R.holo x p j w ⟨hw.1, hzV.1⟩
    have ha' : ∀ p, AnalyticAt ℂ (fun w => R.lift x' ((R.A.chart j).symm w) p) w := fun p =>
      R.holo x' p j w ⟨hw.1, hzV.2⟩
    have hrk : ∀ k, AnalyticAt ℂ (fun w => r k ((R.A.chart j).symm w)) w := fun k =>
      ((ha _).div (ha' _) (hzk k).1.2).div analyticAt_const (hc k)
    show AnalyticAt ℂ (fun w => ∑ k, (L.a k : ℂ) *
      (Complex.log (r k ((R.A.chart j).symm w)) + (Real.log ‖c k‖ : ℂ))) w
    refine Finset.analyticAt_fun_sum (𝕜 := ℂ) Finset.univ fun k _ => ?_
    exact analyticAt_const.mul (((hrk k).clog (hzk k).2).add analyticAt_const)
  · rintro z ⟨⟨hzW, hzx⟩, hzx'⟩
    obtain ⟨c', hc', hz⟩ := R.compat x x' z ⟨hzx, hzx'⟩
    have hzk := fun k => Set.mem_iInter.mp hzW.2 k
    have h2 := L.pos _ (R.mem x' z hzx').1
    have hsm := L.smul c' (R.lift x' z) hc'
    rw [← hz] at hsm
    have hrz : ∀ k, r k z = c' k / c k := by
      intro k
      have hne : R.lift x' z ⟨k, i k⟩ ≠ 0 := (hzk k).1.2
      simp only [r, congrFun hz ⟨k, i k⟩]
      field_simp [hne, hc k]
    have hP : ∀ k ∈ Finset.univ, ‖c' k‖ ^ L.a k ≠ 0 := fun k _ =>
      zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc' k))
    simp only [potOf]
    rw [hsm, Real.log_mul (Finset.prod_ne_zero_iff.mpr hP) h2.ne', add_sub_cancel_right,
      Real.log_prod hP, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hrz k, Real.log_zpow]
    simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_re,
      Complex.log_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, zero_mul, sub_zero,
      norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc' k)) (norm_ne_zero_iff.mpr (hc k))]
    ring

theorem isPotential_potOf (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) :
    IsPotential R.A (potOf R L) :=
  ⟨smoothOn_potOf_of_isSmoothHerm R hL, fun x x' y hy => exists_holo_re_eq_potOf_sub_on_overlap R L x x' y hy⟩

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeH
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.M

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def goodT (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (j : Fin A.n) : Set (Fin e → ℂ) :=
  {u | u ∈ (A.chart j).target ∧ AnalyticAt ℂ (q ∘ (A.chart j).symm) u ∧
    LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0}

theorem isOpen_goodT (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (j : Fin A.n) :
    IsOpen (goodT A q j) := by
  rw [isOpen_iff_mem_nhds]
  rintro u ⟨hut, han, hdet⟩
  have h1 : ∀ᶠ v in 𝓝 u, v ∈ (A.chart j).target := (A.chart j).open_target.mem_nhds hut
  have h2 : ∀ᶠ v in 𝓝 u, AnalyticAt ℂ (q ∘ (A.chart j).symm) v := han.eventually_analyticAt
  have hc : ContinuousAt (fun v => ContinuousLinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) v)) u :=
    ContinuousLinearMap.continuous_det.continuousAt.comp han.fderiv.continuousAt
  have h3 : ∀ᶠ v in 𝓝 u, ContinuousLinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) v) ≠ 0 :=
    hc.eventually_ne hdet
  filter_upwards [h1, h2, h3] with v a b c
  exact ⟨a, b, c⟩

theorem target_diff_goodT_subset (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (S : Set X)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) (j : Fin A.n) :
    (A.chart j).target \ goodT A q j ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' S := by
  rintro u ⟨hut, hug⟩
  refine ⟨hut, ?_⟩
  by_contra hS
  apply hug
  have hx := (A.chart j).map_target hut
  have hr : (A.chart j) ((A.chart j).symm u) = u := (A.chart j).right_inv hut
  obtain ⟨h1, h2⟩ := hq _ hS j hx
  rw [hr] at h1 h2
  exact ⟨hut, h1, h2⟩

theorem integrableOn_chart [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Pt : ChartPartition A) (Φ : Fin e → LocPot X) (g : X → ℝ) (hg : MIntegrable A Φ g)
    (j : Fin A.n) :
    IntegrableOn (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) *
      locDens A Φ j u) (A.chart j).target := by
  have hχc : ContinuousOn (fun u => Pt.χ j ((A.chart j).symm u)) (A.chart j).target := by
    have := ((Pt.smooth j) j).continuousOn
    simpa [Function.comp_def] using this
  have hKc : IsCompact ((A.chart j) '' tsupport (Pt.χ j)) :=
    (isClosed_tsupport _).isCompact.image_of_continuousOn
      ((A.chart j).continuousOn.mono (Pt.tsupport_subset j))
  have hKt : (A.chart j) '' tsupport (Pt.χ j) ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (Pt.tsupport_subset j hx)
  have hI := hg j _ hKt hKc
  have hI2 : IntegrableOn (fun u => Pt.χ j ((A.chart j).symm u) *
      (g ((A.chart j).symm u) * locDens A Φ j u)) ((A.chart j) '' tsupport (Pt.χ j)) := by
    first
      | exact hI.continuousOn_mul (hχc.mono hKt) hKc
      | exact IntegrableOn.continuousOn_mul (hχc.mono hKt) hI hKc
  simp only [mul_assoc]
  refine hI2.of_forall_diff_eq_zero (A.chart j).open_target.measurableSet ?_
  rintro u ⟨hut, huK⟩
  have hn : (A.chart j).symm u ∉ tsupport (Pt.χ j) := fun h =>
    huK ⟨_, h, (A.chart j).right_inv hut⟩
  have h0 : Pt.χ j ((A.chart j).symm u) = 0 := by
    first
      | exact image_eq_zero_of_nmem_tsupport hn
      | exact image_eq_zero_of_notMem_tsupport hn
  rw [h0, zero_mul]

theorem goodT_fibre_eq (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (S : Set X)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∉ (q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) :
    goodT A q j ∩ (q ∘ (A.chart j).symm) ⁻¹' {y} =
      (A.chart j) '' ((A.chart j).source ∩ (q ⁻¹' {y} \ S)) := by
  ext u
  constructor
  · rintro ⟨hu, hy'⟩
    have hx := (A.chart j).map_target hu.1
    have hxS : (A.chart j).symm u ∉ S := fun hS => hy ⟨u, ⟨hu, hS⟩, hy'⟩
    exact ⟨(A.chart j).symm u, ⟨hx, hy', hxS⟩, (A.chart j).right_inv hu.1⟩
  · rintro ⟨x, ⟨hx, hqx, hxS⟩, rfl⟩
    have hl : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hx
    obtain ⟨h1, h2⟩ := hq x hxS j hx
    refine ⟨⟨(A.chart j).map_source hx, h1, h2⟩, ?_⟩
    show q ((A.chart j).symm (A.chart j x)) ∈ ({y} : Set (Fin e → ℂ))
    rw [hl]
    exact hqx

theorem fib_term (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (q : X → Fin e → ℂ) (S : Set X)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (Pt : ChartPartition A) (g : X → ℝ) (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source)
    (hxS : x ∉ S) :
    Pt.χ j ((A.chart j).symm (A.chart j x)) * g ((A.chart j).symm (A.chart j x)) *
        locDens A Φ j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) =
      Pt.χ j x * (g x * pushDens A Φ q x) := by
  have hxc : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  have hl : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hx
  have hut : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hx
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart (chartIdx A x)).source :=
    ⟨hut, by
      show (A.chart j).symm (A.chart j x) ∈ (A.chart (chartIdx A x)).source
      rw [hl]
      exact hxc⟩
  have hD := locDensChart A Φ hΦ j (chartIdx A x) (A.chart j x) hut hmem.2
  rw [hl] at hD
  have hTan : AnalyticAt ℂ (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x) :=
    A.holo j (chartIdx A x) _ hmem
  have hTu : (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x) = A.chart (chartIdx A x) x := by
    simp [hl]
  obtain ⟨hqc, -⟩ := hq x hxS (chartIdx A x) hxc
  obtain ⟨-, hdj⟩ := hq x hxS j hx
  have heq : (q ∘ (A.chart j).symm) =ᶠ[𝓝 (A.chart j x)]
      (q ∘ (A.chart (chartIdx A x)).symm) ∘ (A.chart (chartIdx A x) ∘ (A.chart j).symm) := by
    have hopen : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart (chartIdx A x)).source ∈
        𝓝 (A.chart j x) :=
      ((A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target
        (A.chart (chartIdx A x)).open_source).mem_nhds hmem
    filter_upwards [hopen] with y hy
    simp only [Function.comp_apply]
    rw [(A.chart (chartIdx A x)).left_inv hy.2]
  have hfd : fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) =
      (fderiv ℂ (q ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x)).comp
        (fderiv ℂ (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x)) := by
    rw [heq.fderiv_eq, fderiv_comp _ (by rw [hTu]; exact hqc.differentiableAt)
      hTan.differentiableAt, hTu]
  have hdet : LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (q ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
    rw [hfd]
    exact LinearMap.det_comp _ _
  have hT0 : ‖LinearMap.det (fderiv ℂ (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    rw [hdet, h, mul_zero] at hdj
    exact hdj rfl
  have hQ0 : ‖LinearMap.det (fderiv ℂ (q ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    rw [hdet, h, zero_mul] at hdj
    exact hdj rfl
  rw [hl, jacN, pushDens, hD, hdet, norm_mul, mul_pow]
  field_simp

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterExtLocal
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterExt
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def PtsLocalStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g g' : ((Σ k, ι k) → ℂ) → ℝ),
    (∀ j, ∀ z ∈ mcPts P, φ j z = φ' j z) → (∀ z ∈ mcPts P, g z = g' z) →
    ptsIntegralAt P Ψ φ g = ptsIntegralAt P Ψ φ' g' ∧ ptsIntegral P φ g = ptsIntegral P φ' g'

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial Filter Topology

theorem ptsLocal : PtsLocalStatement := by
  intro K _ ι _ P e Ψ₀ φ φ' g g' hφ hg
  have hS : ∀ (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) y w,
      sheetDensity P Ψ φ g y w = sheetDensity P Ψ φ' g' y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs with hγ
    · set γ := hγ.choose with hγdef
      have hev := hγ.choose_spec.2
      have hmem : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := hev.mono fun y' h => h.2.1
      have hy : γ y ∈ mcPts P := hmem.self_of_nhds
      rw [hg _ hy]
      have hH : ∀ k, cxHessian (fun y' => φ k (γ y')) y = cxHessian (fun y' => φ' k (γ y')) y := by
        intro k
        have hloc : (fun y' => φ k (γ y')) =ᶠ[𝓝 y] (fun y' => φ' k (γ y')) :=
          hmem.mono fun y' h => hφ k _ h
        have h2 := hloc.fderiv (𝕜 := ℝ)
        unfold cxHessian
        rw [h2.fderiv_eq]
      unfold maDensity
      simp only [hH]
    · rfl
  exact ⟨by simp only [ptsIntegralAt, hS], by simp only [ptsIntegral, ptsIntegralAt, hS]⟩

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeD
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

def brQ (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    Fin e → ℂ :=
  fun i => Ψ (segre (R.lift x x)) i.succ / Ψ (segre (R.lift x x)) 0

def brBad (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set R.X :=
  {x | R.lift x x ∈ mcPts J} ∪ {x | Ψ (segre (R.lift x x)) 0 = 0} ∪
    {x | ∃ j, x ∈ (R.A.chart j).source ∧
      ¬ (AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}

def brW (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    ((k : K) → ι k) → ℂ :=
  (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x)

variable (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem brGood : ∀ x ∉ brBad R Ψ, ∀ j, x ∈ (R.A.chart j).source →
    AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
      LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  intro x hx j hj
  by_contra h
  exact hx (Or.inr ⟨j, hj, h⟩)

theorem notMemB_of_notMem_brBad {x : R.X} (hx : x ∉ brBad R Ψ) : R.lift x x ∉ mcPts J := fun h => hx (Or.inl (Or.inl h))

theorem projection_zero_ne_of_notMem_bridgeBadSet {x : R.X} (hx : x ∉ brBad R Ψ) :
    Ψ (segre (R.lift x x)) 0 ≠ 0 := fun h => hx (Or.inl (Or.inr h))

theorem brW_mem_fibre (hK : Nonempty K) (hPh : IsMultiHomogIdeal P) {x : R.X}
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) : brW R Ψ x ∈ fibre P Ψ (brQ R Ψ x) := by
  classical
  have hz0 : R.lift x x ∈ mcPts P := R.mem x x (R.mem_U x)
  let k0 : K := hK.some
  let cc : K → ℂ := fun k => if k = k0 then (Ψ (segre (R.lift x x)) 0)⁻¹ else 1
  have hcc : ∀ k, cc k ≠ 0 := by
    intro k
    simp only [cc]
    split_ifs
    · exact inv_ne_zero h0
    · exact one_ne_zero
  have horb : SameOrbit (fun p : (Σ k, ι k) => cc p.1 * R.lift x x p) (R.lift x x) := ⟨cc, hcc, rfl⟩
  have hprod : ∏ k, cc k = (Ψ (segre (R.lift x x)) 0)⁻¹ := by simp [cc]
  have hseg : segre (fun p : (Σ k, ι k) => cc p.1 * R.lift x x p) = brW R Ψ x := by
    rw [segre_smul, hprod]
    rfl
  refine ⟨fun p => cc p.1 * R.lift x x p, mem_mcPts_of_sameOrbit hPh horb hz0, hseg, ?_⟩
  show Ψ ((Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x)) = Fin.cons 1 (brQ R Ψ x)
  rw [map_smul]
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp [inv_mul_cancel₀ h0]
  · simp [brQ, div_eq_inv_mul]

theorem brW_injOn : Set.InjOn (brW R Ψ) {x | R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0} := by
  intro x hx x' hx' h
  have hz' := (R.mem x' x' (R.mem_U x')).1
  apply R.inj x x' hx.1
  apply sameOrbit_of_segre hz' (Ψ (segre (R.lift x x)) 0 * (Ψ (segre (R.lift x' x')) 0)⁻¹)
    (mul_ne_zero hx.2 (inv_ne_zero hx'.2))
  have h' : (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x) =
      (Ψ (segre (R.lift x' x')) 0)⁻¹ • segre (R.lift x' x') := h
  rw [mul_smul, ← h', smul_smul, mul_inv_cancel₀ hx.2, one_smul]

theorem brFib_finite (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (brQ R Ψ ⁻¹' {y} \ brBad R Ψ).Finite := by
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  refine Set.Finite.of_injOn (f := brW R Ψ) (t := fibre P Ψ y) ?_ ?_ (fibreFinite K ι P e Ψ hP hΨ y)
  · intro x hx
    have h0 := projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2
    have hq : brQ R Ψ x = y := hx.1
    rw [← hq]
    exact brW_mem_fibre R Ψ hP.1 hPh h0
  · intro x hx x' hx' h
    exact brW_injOn R Ψ ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩
      ⟨notMemB_of_notMem_brBad R Ψ hx'.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx'.2⟩ h

theorem exists_of_mem_fibre {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre P Ψ y)
    (hy : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y) :
    ∃ x, R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ brQ R Ψ x = y ∧ brW R Ψ x = w := by
  obtain ⟨z, hz, hzw, hΨw⟩ := hw
  have hzJ : z ∉ mcPts J := by
    intro hzJ
    refine hy ⟨z, hz, hzJ, ?_⟩
    rw [hzw]
    exact hΨw
  obtain ⟨x, hx⟩ := R.surj z hz hzJ
  obtain ⟨cc, hcc, hlift⟩ := hx
  have hμ : ∏ k, cc k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hcc k
  have hseg : segre (R.lift x x) = (∏ k, cc k) • w := by
    rw [hlift, segre_smul, hzw]
  have hΨl : Ψ (segre (R.lift x x)) = (∏ k, cc k) • Fin.cons 1 y := by
    rw [hseg, map_smul, hΨw]
  have h0 : Ψ (segre (R.lift x x)) 0 = ∏ k, cc k := by
    rw [hΨl]
    simp
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hzJ
    refine mem_mcPts_of_sameOrbit R.homog ⟨fun k => (cc k)⁻¹, fun k => inv_ne_zero (hcc k), ?_⟩ h
    funext p
    rw [hlift]
    exact (inv_mul_cancel_left₀ (hcc p.1) (z p)).symm
  · rw [h0]
    exact hμ
  · funext i
    simp only [brQ, hΨl]
    simp [hμ]
  · show (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x) = w
    rw [h0, hseg, smul_smul, inv_mul_cancel₀ hμ, one_smul]

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
