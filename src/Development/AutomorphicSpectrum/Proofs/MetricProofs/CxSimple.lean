module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjection
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.FiniteOfTorsion
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CauchyBinet
public import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxComp

open ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt Filter Topology

def cxSimple {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (w : ((k : K) → ι k) → ℂ) : Prop :=
  ∃ (y : Fin e → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ), IsSetSheet S Ψ y w γ ∧
    ∀ᶠ q in 𝓝 (y, w), q.2 ∈ setFibre S Ψ q.1 → q.2 = segre (γ q.1)

end GlobalTheory.CompanionTheory.Ar.Pub.CxComp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositive
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.IsotropicSubmoduleNonzeroFamily
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace LevelTowerAlt

theorem isotropic_submodule_nonzero_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), IsCMFam σ → IsIsoSub R.form I → I ≠ ⊥ → (∃ r v, IsNzFamily I r v) ∧ ∀ r v, IsNzFamily I r v → R.nz σ I = R.nzOf σ I v ∧ 0 < R.nz σ I ∧ r = Module.finrank (𝓞 E) I := by
  intro E _ _ _ g Λ _ _ Ψ _ R σ I hσ hI hne
  have := R.free
  have := R.fin
  refine ⟨exists_family hne, fun r v hv => ⟨nz_eq R hσ hv, ?_, family_rank hv⟩⟩
  rw [nz_eq R hσ hv]
  exact nzOf_pos R σ hI hv

end LevelTowerAlt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositive
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.isotropic_sublattice_covolume_positive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), IsCMFam σ → IsIsoSub R.form I → I ≠ ⊥ → (∃ r v, IsNzFamily I r v) ∧ ∀ r v, IsNzFamily I r v → R.nz σ I = R.nzOf σ I v ∧ 0 < R.nz σ I ∧ r = Module.finrank (𝓞 E) I := by
  first | exact @LevelTowerAlt.isotropic_submodule_nonzero_family | exact LevelTowerAlt.isotropic_submodule_nonzero_family
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_sublattice_covolume_positive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), IsCMFam σ → IsIsoSub R.form I → I ≠ ⊥ → (∃ r v, IsNzFamily I r v) ∧ ∀ r v, IsNzFamily I r v → R.nz σ I = R.nzOf σ I v ∧ 0 < R.nz σ I ∧ r = Module.finrank (𝓞 E) I := by
  first | exact @GlobalTheory.CompanionTheory.Relay.isotropic_sublattice_covolume_positive | exact GlobalTheory.CompanionTheory.Relay.isotropic_sublattice_covolume_positive | (intros; apply GlobalTheory.CompanionTheory.Relay.isotropic_sublattice_covolume_positive <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Fund

def fundCo {N : ℕ} (f : Fin N → ℝ) (i : Fin N) : ℝ :=
  f i - if h : (i : ℕ) + 1 < N then f ⟨i + 1, h⟩ else 0

theorem fundCo_sub {N : ℕ} (f g : Fin N → ℝ) (i : Fin N) : fundCo (f - g) i = fundCo f i - fundCo g i := by
  unfold fundCo
  split_ifs <;> simp <;> ring

theorem fundCo_smul {N : ℕ} (c : ℝ) (f : Fin N → ℝ) (i : Fin N) : fundCo (c • f) i = c * fundCo f i := by
  unfold fundCo
  split_ifs <;> simp <;> ring

private theorem abel_range (F B : ℕ → ℝ) (M : ℕ) :
    ∑ i ∈ Finset.range M, (F i - F (i + 1)) * ∑ k ∈ Finset.range (i + 1), B k + F M * ∑ k ∈ Finset.range M, B k =
      ∑ k ∈ Finset.range M, F k * B k := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun k => F k * B k), ← ih, Finset.sum_range_succ B M]
    ring

theorem sum_fundCo_mul_sum_Iic {N : ℕ} (f B : Fin N → ℝ) :
    ∑ i, fundCo f i * ∑ k ∈ Finset.Iic i, B k = ∑ k, f k * B k := by
  classical
  let F : ℕ → ℝ := fun j => if h : j < N then f ⟨j, h⟩ else 0
  let B' : ℕ → ℝ := fun j => if h : j < N then B ⟨j, h⟩ else 0
  have hF : ∀ i : Fin N, F i = f i := fun i => by simp [F, i.2]
  have hB : ∀ i : Fin N, B' i = B i := fun i => by simp [B', i.2]
  have hFN : F N = 0 := by simp [F]
  have hco : ∀ i : Fin N, fundCo f i = F i - F (i + 1) := fun i => by
    simp only [fundCo, hF]
    congr 1
  have hI : ∀ i : Fin N, ∑ k ∈ Finset.Iic i, B k = ∑ k ∈ Finset.range ((i : ℕ) + 1), B' k := by
    intro i
    symm
    refine Finset.sum_bij' (fun j hj => (⟨j, by have := Finset.mem_range.1 hj; have := i.2; omega⟩ : Fin N))
      (fun k _ => (k : ℕ)) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Iic, Fin.le_def]
      have := Finset.mem_range.1 hj
      omega
    · intro k hk
      have : (k : ℕ) ≤ i := Fin.le_def.1 (Finset.mem_Iic.1 hk)
      exact Finset.mem_range.2 (by omega)
    · intro j hj; rfl
    · intro k hk; rfl
    · intro j hj
      have h1 : j < N := by have := Finset.mem_range.1 hj; have := i.2; omega
      simp [B', h1]
  have h := abel_range F B' N
  rw [hFN, zero_mul, add_zero] at h
  simp only [hco, hI]
  rw [Fin.sum_univ_eq_sum_range (fun i => (F i - F (i + 1)) * ∑ k ∈ Finset.range (i + 1), B' k) N, h,
    ← Fin.sum_univ_eq_sum_range (fun k => F k * B' k) N]
  exact Finset.sum_congr rfl fun k _ => by rw [hF, hB]

theorem aeval_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {S : Type} [CommRing S]
    {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) (t : K → S) (x : (Σ k, ι k) → S) :
    aeval (fun p => t p.1 * x p) g = (∏ k, t k ^ a k) * aeval x g := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hprod : ∏ p, (t p.1 * x p) ^ m p = (∏ k, t k ^ a k) * ∏ p, x p ^ m p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ m ⟨k, i⟩ = t k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [hprod]
  ring

theorem isMultiHomog_mul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {f g : MRing ι}
    {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hm)
  simp [Finset.sum_add_distrib, hf m₁ h₁ k, hg m₂ h₂ k]

theorem aeval_eq_zero_of_mem {K : Type} {ι : K → Type} {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω)
    {f : MRing ι} (hf : f ∈ mCoordIdeal y) : aeval y f = 0 := by
  have hc : (MvPolynomial.eval (fun _ : K => (1 : Ω))).comp (mConeMap y).toRingHom = (aeval y).toRingHom :=
    MvPolynomial.ringHom_ext (fun n => by simp) (fun p => by simp [mConeMap])
  have h0 : mConeMap y f = 0 := hf
  have := congrArg (fun φ => φ f) hc
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h0, map_zero] at this
  exact this.symm

theorem hasVal_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ} (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (h : HasVal y a s z v) : HasVal y a s (fun p => c p.1 * z p) (v * ∏ k, c k ^ a k) := by
  obtain ⟨dg, dh, g, k', hg, hk, hd, hy, h0, hv⟩ := h
  refine ⟨dg, dh, g, k', hg, hk, hd, hy, ?_, ?_⟩
  · rw [aeval_scale hk]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)) h0
  · rw [aeval_scale hg, aeval_scale hk, hv]
    have e : ∀ k, c k ^ dg k = c k ^ a k * c k ^ dh k := fun k => by
      rw [← zpow_natCast, hd k, zpow_add₀ (hc k), zpow_natCast, mul_comm]
    simp only [e, Finset.prod_mul_distrib]
    ring

theorem isSmoothHerm_comb {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {σ : Type} [Fintype σ]
    {A : σ → HermLine ι} (hA : ∀ a, IsSmoothHerm (A a)) (n : σ → ℤ) : IsSmoothHerm (combLine A n) := by
  refine contDiffOn_prod fun a _ => ?_
  intro z hz
  have h0 : (A a).h z ≠ 0 := ((A a).pos z hz).ne'
  have hf := hA a z hz
  have key : ∀ m : ℤ, ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (A a).h z ^ m)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} z := by
    intro m
    cases m with
    | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
    | negSucc k =>
      simp only [zpow_negSucc]
      exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)
  exact key _

end GlobalTheory.CompanionTheory.Ar.Small.Fund
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularChartDataProperties
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularChartDataProperties
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv

open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.Regular (RegChartData)

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem isClosed_coordDiv (S : Finset (Fin e)) : IsClosed (coordDiv S) := by
  have h : coordDiv S = ⋃ i ∈ S, {z : Fin e → ℂ | z i = 0} := by
    ext z
    simp [coordDiv]
  rw [h]
  exact isClosed_biUnion_finset fun i _ => isClosed_eq (continuous_apply i) continuous_const

theorem volume_coordDiv_eq_zero (S : Finset (Fin e)) : volume (coordDiv S) = 0 := by
  have h : coordDiv S = ⋃ i ∈ (S : Set (Fin e)),
      ((LinearMap.ker (LinearMap.proj i : (Fin e → ℂ) →ₗ[ℝ] ℂ) : Submodule ℝ (Fin e → ℂ)) : Set (Fin e → ℂ)) := by
    ext z
    simp [coordDiv]
  rw [h, measure_biUnion_null_iff S.countable_toSet]
  intro i _
  apply Measure.addHaar_submodule
  intro htop
  have hmem : (Pi.single i (1 : ℂ) : Fin e → ℂ) ∈ LinearMap.ker (LinearMap.proj i : (Fin e → ℂ) →ₗ[ℝ] ℂ) := by
    rw [htop]
    exact Submodule.mem_top
  simp at hmem

theorem exists_mem_source (R : RegChartData A) (x : X) : ∃ j, x ∈ (R.chart j).source := by
  obtain ⟨j, hj⟩ := R.cover x
  exact ⟨j, R.closure_mid j (subset_closure (R.closure_inner j (subset_closure hj)))⟩

theorem isOpen_Yo (R : RegChartData A) : IsOpen R.Yo := by
  have h : R.Yo = ⋃ j, (R.chart j).source ∩ (R.chart j) ⁻¹' (coordDiv (R.S j))ᶜ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := exists_mem_source R x
      exact ⟨j, hj, (R.mem_Yo j x hj).1 hx⟩
    · rintro ⟨j, hj, hc⟩
      exact (R.mem_Yo j x hj).2 hc
  rw [h]
  exact isOpen_iUnion fun j => (R.chart j).isOpen_inter_preimage (isClosed_coordDiv _).isOpen_compl

theorem volume_compl_Yo (R : RegChartData A) (j : Fin A.n) :
    volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yoᶜ) = 0 := by
  have hsub : (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yoᶜ ⊆
      ⋃ k, ((A.chart j) ∘ (R.chart k).symm) ''
        (((R.chart k).target ∩ (R.chart k).symm ⁻¹' (A.chart j).source) ∩ coordDiv (R.S k)) := by
    rintro y ⟨hyT, hyY⟩
    have hxs : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hyT
    obtain ⟨k, hk⟩ := exists_mem_source R ((A.chart j).symm y)
    have hxc : R.chart k ((A.chart j).symm y) ∈ coordDiv (R.S k) := by
      by_contra h
      exact hyY ((R.mem_Yo k _ hk).2 h)
    refine Set.mem_iUnion.mpr ⟨k, R.chart k ((A.chart j).symm y), ⟨⟨(R.chart k).map_source hk, ?_⟩, hxc⟩, ?_⟩
    · show (R.chart k).symm (R.chart k ((A.chart j).symm y)) ∈ (A.chart j).source
      rw [(R.chart k).left_inv hk]
      exact hxs
    · show (A.chart j) ((R.chart k).symm (R.chart k ((A.chart j).symm y))) = y
      rw [(R.chart k).left_inv hk, (A.chart j).right_inv hyT]
  refine measure_mono_null hsub (measure_iUnion_null fun k => ?_)
  apply MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
  · exact (((R.compat k j).2.differentiableOn).restrictScalars ℝ).mono Set.inter_subset_left
  · exact measure_mono_null Set.inter_subset_right (volume_coordDiv_eq_zero _)

theorem continuousOn_r (R : RegChartData A) : ContinuousOn R.r R.Yo := by
  intro x hx
  obtain ⟨k, hk⟩ := exists_mem_source R x
  have hxc : R.chart k x ∉ coordDiv (R.S k) := (R.mem_Yo k x hk).1 hx
  have hUo : IsOpen ((R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ) :=
    (R.chart k).isOpen_inter_preimage (isClosed_coordDiv _).isOpen_compl
  have hxU : x ∈ (R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ := ⟨hk, hxc⟩
  have hg : ContinuousOn (fun y : Fin e → ℂ => Real.exp 1 + R.f k y + ∑ i ∈ R.S k, Real.log (‖y i‖ ^ 2)⁻¹)
      ((R.chart k).target \ coordDiv (R.S k)) := by
    refine ContinuousOn.add (continuousOn_const.add ((R.f_smooth k).continuousOn.mono Set.sdiff_subset)) ?_
    refine continuousOn_finsetSum _ fun i hi => ?_
    have hne : ∀ y ∈ (R.chart k).target \ coordDiv (R.S k), ‖y i‖ ^ 2 ≠ 0 := by
      intro y hy
      have hyi : y i ≠ 0 := fun h0 => hy.2 (show ∃ i' ∈ R.S k, y i' = 0 from ⟨i, hi, h0⟩)
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hyi)
    exact (((continuous_apply i).norm.pow 2).continuousOn.inv₀ hne).log fun y hy => inv_ne_zero (hne y hy)
  have heq : Set.EqOn R.r ((fun y : Fin e → ℂ => Real.exp 1 + R.f k y + ∑ i ∈ R.S k, Real.log (‖y i‖ ^ 2)⁻¹) ∘ R.chart k)
      ((R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ) := by
    intro z hz
    have h1 := R.r_chart k (R.chart k z) ⟨(R.chart k).map_source hz.1, hz.2⟩
    rw [(R.chart k).left_inv hz.1] at h1
    exact h1
  have hcont := hg.comp (s := (R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ)
    ((R.chart k).continuousOn.mono Set.inter_subset_left)
    (fun _ hz => ⟨(R.chart k).map_source hz.1, hz.2⟩)
  exact ((hcont.congr heq).continuousAt (hUo.mem_nhds hxU)).continuousWithinAt

theorem eventually_not_le_of_not_mem_Yo (R : RegChartData A) {x : X} (hx : x ∉ R.Yo) (l : ℝ) :
    ∀ᶠ z in 𝓝 x, ¬ (z ∈ R.Yo ∧ R.r z ≤ l) := by
  obtain ⟨k, hk⟩ := exists_mem_source R x
  have hxc : R.chart k x ∈ coordDiv (R.S k) := by
    by_contra h
    exact hx ((R.mem_Yo k x hk).2 h)
  obtain ⟨i, hi, hi0⟩ : ∃ i ∈ R.S k, R.chart k x i = 0 := hxc
  obtain ⟨B, hB⟩ := R.f_bdd
  have hca : ContinuousAt (fun z => ‖R.chart k z i‖ ^ 2) x :=
    ((continuous_apply i).continuousAt.comp ((R.chart k).continuousAt hk)).norm.pow 2
  have h0 : ‖R.chart k x i‖ ^ 2 < Real.exp (-(l - Real.exp 1 + B)) := by
    rw [hi0, norm_zero]
    simp [Real.exp_pos]
  have h1 : ∀ᶠ z in 𝓝 x, ‖R.chart k z i‖ ^ 2 < Real.exp (-(l - Real.exp 1 + B)) :=
    Filter.Tendsto.eventually hca (gt_mem_nhds h0)
  have h2 : ∀ᶠ z in 𝓝 x, z ∈ (R.chart k).source := (R.chart k).open_source.mem_nhds hk
  filter_upwards [h1, h2] with z hz1 hz2
  rintro ⟨hzY, hzr⟩
  have hzc : R.chart k z ∉ coordDiv (R.S k) := (R.mem_Yo k z hz2).1 hzY
  have hyT : R.chart k z ∈ (R.chart k).target := (R.chart k).map_source hz2
  have hr := R.r_chart k (R.chart k z) ⟨hyT, hzc⟩
  rw [(R.chart k).left_inv hz2] at hr
  have hball : ‖R.chart k z‖ < 1 := by simpa using R.target_subset k hyT
  have hne : ∀ i' ∈ R.S k, R.chart k z i' ≠ 0 := fun i' hi' h0 =>
    hzc (show ∃ i'' ∈ R.S k, R.chart k z i'' = 0 from ⟨i', hi', h0⟩)
  have hterm : ∀ i' ∈ R.S k, 0 ≤ Real.log (‖R.chart k z i'‖ ^ 2)⁻¹ := by
    intro i' hi'
    apply Real.log_nonneg
    have hp : 0 < ‖R.chart k z i'‖ := norm_pos_iff.mpr (hne i' hi')
    have hlt : ‖R.chart k z i'‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm _ i') hball
    exact (one_le_inv₀ (by positivity)).mpr (by nlinarith)
  have hsum : Real.log (‖R.chart k z i‖ ^ 2)⁻¹ ≤ ∑ i' ∈ R.S k, Real.log (‖R.chart k z i'‖ ^ 2)⁻¹ :=
    Finset.single_le_sum hterm hi
  have hp : 0 < ‖R.chart k z i‖ ^ 2 := by
    have := norm_pos_iff.mpr (hne i hi)
    positivity
  have hlog : Real.log (‖R.chart k z i‖ ^ 2) < -(l - Real.exp 1 + B) := (Real.log_lt_iff_lt_exp hp).mpr hz1
  rw [Real.log_inv] at hsum
  have hf := (abs_le.mp (hB k _ hyT)).1
  linarith

theorem isCompact_sublevel [CompactSpace X] (R : RegChartData A) (l : ℝ) :
    IsCompact {x | x ∈ R.Yo ∧ R.r x ≤ l} := by
  refine IsClosed.isCompact (isOpen_compl_iff.mp (isOpen_iff_eventually.mpr fun x hx => ?_))
  by_cases hY : x ∈ R.Yo
  · have hlt : l < R.r x := not_le.mp fun h => hx ⟨hY, h⟩
    have hcont : ContinuousAt R.r x := (continuousOn_r R).continuousAt ((isOpen_Yo R).mem_nhds hY)
    filter_upwards [Filter.Tendsto.eventually hcont (lt_mem_nhds hlt)] with z hz
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_and, not_le]
    exact fun _ => hz
  · exact eventually_not_le_of_not_mem_Yo R hY l

theorem regData_open_part : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A),
    IsOpen R.Yo ∧ (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yoᶜ) = 0) ∧
      ContinuousOn R.r R.Yo ∧ ∀ ℓ : ℝ, IsCompact {x | x ∈ R.Yo ∧ R.r x ≤ ℓ} := by
  intro e X _ _ _ A R
  exact ⟨isOpen_Yo R, volume_compl_Yo R, continuousOn_r R, isCompact_sublevel R⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularChartDataPropertiesStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_chart_data_properties : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A), IsOpen R.Yo ∧ (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yoᶜ) = 0) ∧ ContinuousOn R.r R.Yo ∧ ∀ ℓ : ℝ, IsCompact {x | x ∈ R.Yo ∧ R.r x ≤ ℓ} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.regData_open_part | exact GlobalTheory.CompanionTheory.Ar.Giv.regData_open_part | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.regData_open_part <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicSectionOfPotential
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicSectionOfPotential
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
  GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ContDiff

namespace SecPot

section General

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem holoOn_continuousOn' {A : FinHolAtlas e X} {W : Set X} {f : X → ℂ} (h : A.HoloOn W f) :
    ContinuousOn f W := by
  intro z hz
  obtain ⟨j, hj⟩ := A.cover z
  have h1 : (A.chart j).symm (A.chart j z) = z := (A.chart j).left_inv hj
  have hu : A.chart j z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by rw [Set.mem_preimage, h1]; exact hz⟩
  have hc : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j z) := (h j _ hu).continuousAt
  have hc2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) z :=
    ContinuousAt.comp hc ((A.chart j).continuousAt hj)
  have hev : ((f ∘ (A.chart j).symm) ∘ (A.chart j)) =ᶠ[𝓝 z] f := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp [(A.chart j).left_inv hy]
  exact (hc2.congr hev).continuousWithinAt

end General

section Model

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {d : ℕ}

structure LocSec (M : CxModel P d) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ) : Prop where
  isOpen : IsOpen U
  sec : ∀ y ∈ U, s y ∈ mcPts P ∧ M.proj (s y) = y
  holo : ∀ p, M.atlas.HoloOn U fun y => s y p

theorem locSec_sections (M : CxModel P d) (x : M.Xc) :
    LocSec M (M.sections x).choose (M.sections x).choose_spec.2.2.choose :=
  ⟨(M.sections x).choose_spec.1, (M.sections x).choose_spec.2.2.choose_spec.1,
    (M.sections x).choose_spec.2.2.choose_spec.2⟩

theorem smoothOn_log_sec {M : CxModel P d} {U : Set M.Xc} {s : M.Xc → (Σ k, ι k) → ℂ}
    (hs : LocSec M U s) {B : HermLine ι} (hB : IsSmoothHerm B) :
    M.atlas.SmoothOn U (fun y => Real.log (B.h (s y))) := by
  intro j y hy
  have hσ : ContDiffAt ℝ ∞ (fun y' => s ((M.atlas.chart j).symm y')) y :=
    contDiffAt_pi.2 fun p => ((hs.holo p j y hy).contDiffAt (n := ∞)).restrict_scalars ℝ
  have hm := (hs.sec _ hy.2).1.1
  have hn : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (s ((M.atlas.chart j).symm y)) := by
    refine IsOpen.mem_nhds ?_ hm
    simp only [Set.setOf_forall, Set.setOf_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have h1 : ContDiffAt ℝ ∞ (fun y' => Real.log (B.h (s ((M.atlas.chart j).symm y')))) y :=
    ((hB.contDiffAt hn).comp y hσ).log (B.pos _ hm).ne'
  exact h1.contDiffWithinAt

theorem exists_re_holo_sections {M : CxModel P d} {U U' : Set M.Xc} {s s' : M.Xc → (Σ k, ι k) → ℂ}
    (hs : LocSec M U s) (hs' : LocSec M U' s') (B : HermLine ι) {y₀ : M.Xc} (hy : y₀ ∈ U)
    (hy' : y₀ ∈ U') :
    ∃ W : Set M.Xc, IsOpen W ∧ y₀ ∈ W ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn W G ∧
      ∀ z ∈ W ∩ U ∩ U', Real.log (B.h (s z)) - Real.log (B.h (s' z)) = (G z).re := by
  classical
  have hz := (hs.sec y₀ hy).1
  have hz' := (hs'.sec y₀ hy').1
  choose i hi using hz'.1
  obtain ⟨c₀, hc₀, hcz⟩ := (M.fibre _ hz' _ hz).1 (by rw [(hs.sec y₀ hy).2, (hs'.sec y₀ hy').2])
  have hn0 : ∀ k, s y₀ ⟨k, i k⟩ ≠ 0 := fun k => by
    rw [hcz]
    exact mul_ne_zero (hc₀ k) (hi k)

  let r : K → ℂ := fun k => s y₀ ⟨k, i k⟩ / s' y₀ ⟨k, i k⟩
  have hr : ∀ k, r k ≠ 0 := fun k => div_ne_zero (hn0 k) (hi k)
  let q : K → M.Xc → ℂ := fun k z => s z ⟨k, i k⟩ / s' z ⟨k, i k⟩ / r k
  have hO : IsOpen (U ∩ U') := hs.isOpen.inter hs'.isOpen
  let W : Set M.Xc := {z | z ∈ U ∩ U' ∧ ∀ k, s' z ⟨k, i k⟩ ≠ 0 ∧ q k z ∈ Complex.slitPlane}
  have hW : IsOpen W := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have hn : ∀ k, ContinuousAt (fun z => s z ⟨k, i k⟩) z := fun k =>
      ((holoOn_continuousOn' (hs.holo _)).mono Set.inter_subset_left).continuousAt (hO.mem_nhds hz.1)
    have hd : ∀ k, ContinuousAt (fun z => s' z ⟨k, i k⟩) z := fun k =>
      ((holoOn_continuousOn' (hs'.holo _)).mono Set.inter_subset_right).continuousAt (hO.mem_nhds hz.1)
    filter_upwards [hO.mem_nhds hz.1, eventually_all.mpr fun k => (hd k).eventually_ne (hz.2 k).1,
      eventually_all.mpr fun k => (((hn k).div (hd k) (hz.2 k).1).div_const _).eventually_mem
        (Complex.isOpen_slitPlane.mem_nhds (hz.2 k).2)] with w h1 h2 h3
    exact ⟨h1, fun k => ⟨h2 k, h3 k⟩⟩
  have hyW : y₀ ∈ W := by
    refine ⟨⟨hy, hy'⟩, fun k => ⟨hi k, ?_⟩⟩
    have : q k y₀ = 1 := div_self (hr k)
    rw [this]
    exact Complex.one_mem_slitPlane
  let G : M.Xc → ℂ := fun z => ∑ k, ((B.a k : ℝ) : ℂ) *
    (Complex.log (q k z) + ((Real.log ‖r k‖ : ℝ) : ℂ))
  refine ⟨W, hW, hyW, G, fun j u hu => ?_, fun z hz => ?_⟩
  · have hzW : (M.atlas.chart j).symm u ∈ W := hu.2
    have hterm : ∀ k, AnalyticAt ℂ (fun u' => ((B.a k : ℝ) : ℂ) *
        (Complex.log (q k ((M.atlas.chart j).symm u')) + ((Real.log ‖r k‖ : ℝ) : ℂ))) u := by
      intro k
      have hn : AnalyticAt ℂ (fun u' => s ((M.atlas.chart j).symm u') ⟨k, i k⟩) u :=
        hs.holo _ j u ⟨hu.1, hzW.1.1⟩
      have hd : AnalyticAt ℂ (fun u' => s' ((M.atlas.chart j).symm u') ⟨k, i k⟩) u :=
        hs'.holo _ j u ⟨hu.1, hzW.1.2⟩
      have hq : AnalyticAt ℂ (fun u' => q k ((M.atlas.chart j).symm u')) u :=
        (hn.div hd (hzW.2 k).1).div analyticAt_const (hr k)
      have hl : AnalyticAt ℂ (Complex.log ∘ fun u' => q k ((M.atlas.chart j).symm u')) u :=
        AnalyticAt.comp (f := fun u' => q k ((M.atlas.chart j).symm u'))
          (analyticAt_clog (hzW.2 k).2) hq
      exact analyticAt_const.mul (hl.add analyticAt_const)
    exact Finset.analyticAt_fun_sum _ fun k _ => hterm k
  · have hzW : z ∈ W := hz.1.1
    have hm := (hs.sec z hzW.1.1).1
    have hm' := (hs'.sec z hzW.1.2).1
    obtain ⟨c, hc, hcy⟩ := (M.fibre _ hm' _ hm).1
      (by rw [(hs.sec z hzW.1.1).2, (hs'.sec z hzW.1.2).2])
    have hpos : 0 < B.h (s' z) := B.pos _ hm'.1
    have hprod : (∏ k, ‖c k‖ ^ B.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
    have hterm : ∀ k, Real.log ‖q k z‖ + Real.log ‖r k‖ = Real.log ‖c k‖ := by
      intro k
      have hck : s z ⟨k, i k⟩ = c k * s' z ⟨k, i k⟩ := by rw [hcy]; rfl
      have hqz : q k z = c k / r k := by
        simp only [q]
        rw [hck, mul_div_assoc, div_self (hzW.2 k).1, mul_one]
      rw [hqz, norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc k)) (norm_ne_zero_iff.mpr (hr k))]
      ring
    have hsm : B.h (s z) = (∏ k, ‖c k‖ ^ B.a k) * B.h (s' z) := by
      rw [hcy]
      exact B.smul c _ hc
    rw [hsm, Real.log_mul hprod hpos.ne', add_sub_cancel_right,
      Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))]
    simp only [G, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re,
      Complex.ofReal_re]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hterm k, Real.log_zpow]

def potOfSections (M : CxModel P d) (B : HermLine ι) : LocPot M.Xc where
  U x := (M.sections x).choose
  isOpen_U x := (M.sections x).choose_spec.1
  mem_U x := (M.sections x).choose_spec.2.1
  φ x y := Real.log (B.h ((M.sections x).choose_spec.2.2.choose y))

end Model

end SecPot


open SecPot in
theorem exists_potential_of_smoothHerm :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (B : HermLine ι), IsSmoothHerm B → ∃ Φ : LocPot M.Xc, IsPotential M.atlas Φ ∧ ∀ x, ∀ y₀ ∈ (Φ).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ).φ x y' - (fun z => Real.log (B.h z)) (s y') = (G y').re := by
  intro K _ ι _ P n M B hB
  refine ⟨potOfSections M B, ⟨fun x => smoothOn_log_sec (locSec_sections M x) hB, ?_⟩, ?_⟩
  · intro x x' y hy
    exact exists_re_holo_sections (locSec_sections M x) (locSec_sections M x') B hy.1 hy.2
  · intro x y₀ hy
    have hs := locSec_sections M x
    refine ⟨_, hs.isOpen, hy.1, fun z hz => ⟨hz, Set.mem_univ _⟩, _, hs.sec, hs.holo, fun _ => 0,
      fun j u _ => analyticAt_const, fun y' _ => ?_⟩
    simp [potOfSections]

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicSectionOfPotentialStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_holomorphic_section_of_potential : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (B : HermLine ι), IsSmoothHerm B → ∃ Φ : LocPot M.Xc, IsPotential M.atlas Φ ∧ ∀ x, ∀ y₀ ∈ (Φ).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ).φ x y' - (fun z => Real.log (B.h z)) (s y') = (G y').re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.exists_potential_of_smoothHerm | exact GlobalTheory.CompanionTheory.Ar.Giv.exists_potential_of_smoothHerm | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.exists_potential_of_smoothHerm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBlockDiagMapGenBlock
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section Homog

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_rename_base {σ : Type} (blk : σ → Option K) {d' : NonPluckerBlocks blk → ℕ}
    {g : MRing (baseIdx ι blk)} (hg : IsMultiHomog g d') :
    open Classical in
    IsMultiHomog (rename (fun q : Σ k, baseIdx ι blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) g)
      (fun k => if h : ∀ p, blk p ≠ some k then d' ⟨k, h⟩ else 0) := by
  classical
  have hinj : Function.Injective (fun q : Σ k, baseIdx ι blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) := by
    rintro ⟨⟨k, hk⟩, a⟩ ⟨⟨k', hk'⟩, b⟩ h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
    cases h
    rfl
  intro m hm k
  rw [support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  beta_reduce
  by_cases h : ∀ p, blk p ≠ some k
  · rw [dite_eq_left h, ← hg m' hm' ⟨k, h⟩]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finsupp.mapDomain_apply_of_injective hinj m' ⟨⟨k, h⟩, i⟩
  · rw [dite_eq_right h]
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨⟨⟨k', hk'⟩, b⟩, e⟩
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp e
    exact h hk'

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}

end Homog

section Minors

variable {N : ℕ}

theorem minorIJ_eq_det_of_card {R : Type} [CommRing R] (h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) {r : ℕ}
    (hI : I.card = r) (hJ : J.card = r) :
    minorIJ h I J = (h.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det := by
  subst hJ
  unfold minorIJ
  rw [dite_eq_left hI]

theorem minorIJ_mul_sum {R : Type} [CommRing R] (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (T * h) I J = ∑ I', minorIJ T I I' * minorIJ h I' J := by
  classical
  by_cases e : I.card = J.card
  · have hm : (T * h).submatrix (I.orderEmbOfFin e) (J.orderEmbOfFin rfl) =
        T.submatrix (I.orderEmbOfFin e) id * h.submatrix id (J.orderEmbOfFin rfl) := by
      ext a b
      simp [Matrix.mul_apply]
    have hsum : ∑ I', minorIJ T I I' * minorIJ h I' J =
        ∑ S : {S : Finset (Fin N) // S.card = J.card}, minorIJ T I S.1 * minorIJ h S.1 J := by
      rw [← Finset.sum_filter_of_ne (s := Finset.univ) (p := fun S : Finset (Fin N) => S.card = J.card)]
      · exact Finset.sum_subtype _ (by simp) _
      · intro S _ hS
        by_contra hc
        apply hS
        rw [show minorIJ h S J = 0 by unfold minorIJ; rw [dite_eq_right hc], mul_zero]
    rw [minorIJ_eq_det_of_card _ I J e rfl, hm, ReciprocityTheory.ChartRestriction.DS.cauchyBinet, hsum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [minorIJ_eq_det_of_card T I S.1 e S.2, minorIJ_eq_det_of_card h S.1 J S.2 rfl]
    rfl
  · have h0 : minorIJ (T * h) I J = 0 := by
      unfold minorIJ
      rw [dite_eq_right e]
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun I' _ => ?_
    by_cases e' : I.card = I'.card
    · rw [show minorIJ h I' J = 0 by
        unfold minorIJ
        rw [dite_eq_right fun c => e (e'.trans c)], mul_zero]
    · rw [show minorIJ T I I' = 0 by unfold minorIJ; rw [dite_eq_right e'], zero_mul]

theorem minorIJ_block_zero {R : Type} [CommRing R] {j : ℕ} {i : Fin N} {h : Matrix (Fin N) (Fin N) R}
    (hh : IsBlockDiag j h) {I : Finset (Fin N)} (hnot : ¬ IsStepRows N j i I) :
    minorIJ h I (stepCols N j i) = 0 := by
  have hiN := i.isLt
  by_cases e : I.card = (stepCols N j i).card
  · have hsub : ¬ I ⊆ if (i : ℕ) + 1 ≤ j then wIdx N j else omIdx N j := fun hs => hnot ⟨e, hs⟩
    obtain ⟨a, haI, haB⟩ := Finset.not_subset.mp hsub
    have hr : a ∈ Set.range (I.orderEmbOfFin e) := by
      rw [Finset.range_orderEmbOfFin]
      exact haI
    obtain ⟨r, rfl⟩ := hr
    unfold minorIJ
    rw [dite_eq_left e]
    refine Matrix.det_eq_zero_of_row_eq_zero r fun c => ?_
    have hb := Finset.orderEmbOfFin_mem (stepCols N j i) rfl c
    refine hh _ _ ?_
    generalize (stepCols N j i).orderEmbOfFin rfl c = b at hb
    generalize I.orderEmbOfFin e r = a at haB
    by_cases hc : (i : ℕ) + 1 ≤ j
    · simp only [stepCols, wIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hc] at hb haB
      omega
    · simp only [stepCols, omIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hc] at hb haB
      omega
  · unfold minorIJ
    rw [dite_eq_right e]

end Minors

section Model

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

end Model

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackStatementHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackStatementHolds
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

section PullTop

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isPsh_of_phi_eq {A : FinHolAtlas e X} {P Q : LocPot X} (hQ : IsPotential A Q)
    (hφ : P.φ = Q.φ) (hP : IsPsh A P) : IsPsh A Q := by
  intro x j y hy w
  obtain ⟨W, hW, hzW, G, hG, hGe⟩ :=
    hQ.2 x ((A.chart j).symm y) ((A.chart j).symm y) ⟨hy.2, Q.mem_U _⟩
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy.1, hzW⟩
  have ho : IsOpen ((A.chart j).target ∩
      (A.chart j).symm ⁻¹' (W ∩ Q.U x ∩ Q.U ((A.chart j).symm y))) :=
    (A.chart j).isOpen_inter_preimage_symm ((hW.inter (Q.isOpen_U x)).inter (Q.isOpen_U _))
  have hev : (Q.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun v =>
      (Q.φ ((A.chart j).symm y) ∘ (A.chart j).symm) v + 1 * ((G ∘ (A.chart j).symm) v).re := by
    filter_upwards [ho.mem_nhds ⟨hy.1, ⟨hzW, hy.2⟩, Q.mem_U _⟩] with v hv
    have := hGe _ hv.2
    simp only [Function.comp_apply]
    linarith
  have ho2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U ((A.chart j).symm y)) :=
    (A.chart j).isOpen_inter_preimage_symm (Q.isOpen_U _)
  have h2 : ContDiffAt ℝ 2 (Q.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
    ((hQ.1 _ j).contDiffAt (ho2.mem_nhds ⟨hy.1, Q.mem_U _⟩)).of_le
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hRe : ContDiffAt ℝ 2 (fun v => ((G ∘ (A.chart j).symm) v).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr hev, levi_add_smul 1 h2 hRe, levi_re_analytic hGa, mul_zero, add_zero, ← hφ]
  exact hP _ j y ⟨hy.1, P.mem_U _⟩ w

end PullTop

end GlobalTheory.CompanionTheory.Ar.Giv

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem pullbackStatement : PullbackStatement := by
  intro e e' X X' _ _ _ _ _ _ A A' h hh Θ L Θ' s n n' m W m' W' hΘ hΘp hΘ' hΘ'p hL hs hsnc hs0
    hsnc' th ph phT C₅ C t₀ hSW hF hC2
  obtain ⟨hth, hSm, hPshOn, hbd⟩ := hSW
  have hΘpsh : IsPsh A Θ := TailBoundAlt.isPsh_of_isPosPot A Θ hΘp
  have hΘ'psh : IsPsh A' Θ' := TailBoundAlt.isPsh_of_isPosPot A' Θ' hΘ'p
  have hΘpb : IsPotential A' (Θ.pullback h hh.1) := isPotentialPullback A A' h hh Θ hΘ
  obtain ⟨K, hK0, -, hKpsh⟩ := TailBoundAlt.exists_psh_chern_bound A' Θ' (Θ.pullback h hh.1) hΘ' hΘ'p hΘpb
  have ht₀ : 0 < t₀ := hF.1
  have hU : IsOpen (bdry s)ᶜ := (LeviFormBoundaryTopology.isClosed_bdry hs).isOpen_compl
  set M : ℝ := max 1 K with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMK : K ≤ M := le_max_right _ _
  set C' : ℝ := |C| * M with hC'
  set t₁ : ℝ := min t₀ (Real.exp (-Real.exp 1)) with ht₁
  have ht₁0 : 0 < t₁ := lt_min ht₀ (Real.exp_pos _)
  have ht₁t₀ : t₁ ≤ t₀ := min_le_left _ _
  have ht₁e : t₁ ≤ Real.exp (-Real.exp 1) := min_le_right _ _
  have hCC' : |C| ≤ C' := le_mul_of_one_le_right (abs_nonneg C) hM1
  have F1 := isRegFamily_mono A Θ L s th ph phT C t₀ |C| t₁ hΘ hΘpsh hth hs0 hF le_rfl ht₁0 ht₁t₀ ht₁e
  have F2 := isRegFamily_mono A Θ L s th ph phT C t₀ C' t₁ hΘ hΘpsh hth hs0 hF hCC' ht₁0 ht₁t₀ ht₁e
  refine ⟨C', t₁, ⟨isPotentialPullback A A' h hh th hth, ?_, ?_, fun y hy => hbd (h y) hy⟩, ?_, ?_⟩
  · have := smoothOn_pull hh hU hSm
    rwa [Set.preimage_compl] at this
  · have := isPshOn_pull hh hU hth hSm hPshOn
    rwa [Set.preimage_compl] at this
  · obtain ⟨-, -, F1⟩ := F1
    obtain ⟨h1, h2, F2⟩ := F2
    refine ⟨h1, h2, fun t ht htt => ?_⟩
    obtain ⟨a1, a2, a3, a4, -, a6, a7, a8⟩ := F2 t ht htt
    obtain ⟨b1, -, -, -, b5, -⟩ := F1 t ht htt
    have hsm : A'.Smooth (phT t ∘ h) := by
      have := smoothOn_pull hh isOpen_univ a1
      rwa [Set.preimage_univ] at this
    refine ⟨hsm, fun y => a2 (h y), fun y hy => a3 (h y) hy, fun y => a4 (h y), ?_,
      fun y hy hyr => a6 (h y) hy hyr, fun y hy => a7 (h y) hy,
      fun t' h1 h2 y => a8 t' h1 h2 (h y)⟩

    set ε : ℝ := epsT |C| t with hε
    have hq := loglog_quot_nonneg ht (htt.trans ht₁e)
    have hε0 : 0 ≤ ε := by
      rw [hε, epsT_eq_mul]; exact mul_nonneg (abs_nonneg C) hq
    have hε' : epsT C' t = M * ε := by
      rw [hε, epsT, epsT, hC']; ring
    have hεK : 0 ≤ M * ε - K * ε := by nlinarith
    have hP0 : IsPotential A (th + LocPot.ofFun (phT t) + Θ.rsmul ε) :=
      isPotentialAdd A _ _ (isPotentialAdd A _ _ hth (isPotential_ofFun A _ b1))
        (isPotentialRsmul A ε Θ hΘ)
    have hD : IsPotential A' (Θ'.rsmul K + (Θ.pullback h hh.1).rsmul (-1)) :=
      isPotentialAdd A' _ _ (isPotentialRsmul A' K Θ' hΘ') (isPotentialRsmul A' (-1) _ hΘpb)
    have hS1 := isPotentialPullback A A' h hh _ hP0
    have hS1p := isPsh_pull hh hP0 b5
    have hS2 := isPotentialRsmul A' ε _ hD
    have hS2p := isPshRsmul A' ε _ hε0 hD hKpsh
    have hS3 := isPotentialRsmul A' (M * ε - K * ε) Θ' hΘ'
    have hS3p := isPshRsmul A' (M * ε - K * ε) Θ' hεK hΘ' hΘ'psh
    have hS := isPshAdd A' _ _ (isPotentialAdd A' _ _ hS1 hS2) hS3
      (isPshAdd A' _ _ hS1 hS2 hS1p hS2p) hS3p
    have hT : IsPotential A' (th.pullback h hh.1 + LocPot.ofFun (phT t ∘ h) + Θ'.rsmul (epsT C' t)) :=
      isPotentialAdd A' _ _ (isPotentialAdd A' _ _ (isPotentialPullback A A' h hh th hth)
        (isPotential_ofFun A' _ hsm)) (isPotentialRsmul A' _ Θ' hΘ')
    refine isPsh_of_phi_eq hT ?_ hS
    funext x y
    show th.φ (h x) (h y) + phT t (h y) + ε * Θ.φ (h x) (h y) +
        ε * (K * Θ'.φ x y + -1 * Θ.φ (h x) (h y)) + (M * ε - K * ε) * Θ'.φ x y =
      th.φ (h x) (h y) + phT t (h y) + epsT C' t * Θ'.φ x y
    rw [hε']
    ring
  · have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), A.Smooth (phT t) :=
      Filter.mem_of_superset (Ioc_mem_nhdsGT ht₀) fun t ht => (hF.2.2 t ht.1 ht.2).1
    exact regular_family_C2_pullback_of_open A A' h hh s ph phT hU hSm hev hC2

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackStatementHoldsStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_statement_holds : PullbackStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pullbackStatement | exact GlobalTheory.CompanionTheory.Ar.Giv.pullbackStatement | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pullbackStatement <;> assumption)
end
end
