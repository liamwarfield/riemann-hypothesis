module

public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsConjInvariantMollifier
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.DeterminantLatticeGradedTensor
open AlgebraicGeometry CategoryTheory Matrix
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

namespace N1

section

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem gen_ratio {Λ : Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) :
    s / t ∈ regAt ξ p := by
  have : s ∈ Submodule.span (regAt ξ p) {t} := by rw [← ht.2, hs.2]; exact Submodule.mem_span_singleton_self s
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
  have : s / t = a := by rw [← ha, div_eq_iff ht.1]; rfl
  rw [this]; exact a.2

theorem tens_gen {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} (a : I → ℤ) {p : Cpt ξ} {s : I → Ω}
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  have h0 : ∏ i, s i ^ a i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hs i).1
  refine ⟨h0, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2
    (Set.singleton_subset_iff.2 (Submodule.subset_span ⟨s, hs, rfl⟩)))⟩
  rintro _ ⟨s', hs', rfl⟩
  have hm : ∏ i, (s' i / s i) ^ a i ∈ regAt ξ p := by
    refine prod_mem fun i _ => ?_
    rcases Int.eq_nat_or_neg (a i) with ⟨n, h | h⟩
    · rw [h, zpow_natCast]; exact pow_mem (gen_ratio (hs' i) (hs i)) n
    · rw [h, _root_.zpow_neg, ← _root_.inv_zpow, inv_div, zpow_natCast]; exact pow_mem (gen_ratio (hs i) (hs' i)) n
  refine Submodule.mem_span_singleton.2 ⟨⟨_, hm⟩, ?_⟩
  show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = _
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [← mul_zpow, div_mul_cancel₀ _ (hs i).1]

end

end N1

open N1

theorem determinant_lattice_graded_tensor : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (b₀ : Fin r → V), LinearIndependent Ω b₀ → L.IsFlagVBOn Set.univ b₀ → detLat L b₀ = Lat.tens (fun i => L.gr b₀ i) (fun _ => 1) := by
  intro X Ω _ ξ V _ _ L r b₀ h₀ hL
  funext p
  obtain ⟨U, hU, b, hfl, hb⟩ := hL p trivial
  replace hb := hb p trivial hU
  have hmem : ∀ k : Fin r, ∃ c : Fin r → Ω, (∀ k', k < k' → c k' = 0) ∧ b k = ∑ k', c k' • b₀ k' := by
    intro k
    have h1 : b k ∈ flagStep Ω b₀ (k + 1) := by
      rw [← hfl]; exact Submodule.subset_span ⟨k, Nat.lt_succ_self _, rfl⟩
    obtain ⟨c, hc, e⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).1 h1
    refine ⟨c, fun k' h => (Finsupp.mem_supported' Ω c).1 hc k' (by simp only [Set.mem_ofPred_eq, not_lt]; exact h), ?_⟩
    rw [← e, Finsupp.linearCombination_apply]
    exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)
  choose c hc0 hc using hmem
  let T : Matrix (Fin r) (Fin r) Ω := Matrix.of fun k' k => c k k'
  have hT : T.BlockTriangular id := fun k' k h => hc0 k k' h
  have h1 := determinant_lattice_generator X Ω ξ V L r b₀ b T p h₀ hb hc
  have h2 : ∀ i, (L.gr b₀ i).IsGenAt p (T i i) := fun i => by
    refine FlagGrGen.gr_isGenAt X Ω ξ V L r b₀ b p i _ h₀ hfl hb ?_
    rw [hc i, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    show c i i • b₀ i + _ - c i i • b₀ i ∈ _
    rw [add_sub_cancel_left]
    refine Submodule.sum_mem _ fun k' hk' => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hk') with h | h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k', h, rfl⟩)
    · rw [hc0 i k' h, zero_smul]; exact Submodule.zero_mem _
  have h3 := tens_gen (Λ := fun i => L.gr b₀ i) (fun _ => 1) h2
  rw [h1.2, h3.2, Matrix.det_of_isUpperTriangular hT]
  simp

end LevelTowerAlt
end

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.SymmetricChartsCutoffFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

section

open Set GroundTheory.Heights₂.Heights.Regular
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm.M.PLAux (chartPush chartPush_eq_zero isCompact_symm_image smooth_chartPush contDiffOn_compat)
open scoped ContDiff

theorem cutoff_of_bumps {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] {D : ℕ} {A : FinHolAtlas D X}
    (P : PotentialCharts A) (g : Fin P.N → (Fin D → ℂ) → ℝ) (hgs : ∀ j, ContDiff ℝ ∞ (g j))
    (hg01 : ∀ j y, 0 ≤ g j y ∧ g j y ≤ 1) (hg1 : ∀ j, ∀ x ∈ P.inner j, g j (P.chart j x) = 1)
    (hgc : ∀ j, IsCompact (tsupport (g j))) (hgt : ∀ j, tsupport (g j) ⊆ P.chartMid j) :
    ∃ C : ℝ, P.IsCutoffFamily (fun j x => chartPush (P.chart j) (g j) x - 1) C := by
  have hgt' : ∀ j, tsupport (g j) ⊆ (P.chart j).target := fun j => (hgt j).trans inter_subset_left
  have hcp : ∀ j x, 0 ≤ chartPush (P.chart j) (g j) x ∧ chartPush (P.chart j) (g j) x ≤ 1 := by
    intro j x
    unfold chartPush
    by_cases hx : x ∈ (P.chart j).source
    · rw [indicator_of_mem hx]; exact hg01 j _
    · rw [indicator_of_notMem hx]; exact ⟨le_rfl, zero_le_one⟩
  have hsm : ∀ j, A.Smooth (fun x => chartPush (P.chart j) (g j) x - 1) := by
    intro j a
    exact ContDiffOn.sub (f := chartPush (P.chart j) (g j) ∘ (A.chart a).symm)
      (smooth_chartPush (P.compat j) (hgs j) (hgc j) (hgt' j) a) contDiffOn_const
  have hC : ∀ j k, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ P.chart k '' closure (P.mid k), ∀ w,
      -C * ‖w‖ ^ 2 ≤ levi ((fun x => chartPush (P.chart j) (g j) x - 1) ∘ (P.chart k).symm) y w := by
    intro j k
    have h := contDiffOn_compat (P.compat k) isOpen_univ (hsm j)
    rw [preimage_univ, inter_univ] at h
    refine levi_lower_bound_of_isCompact (P.chart k).open_target (h.of_le (WithTop.coe_le_coe.2 le_top))
      (isClosed_closure.isCompact.image_of_continuousOn
        ((P.chart k).continuousOn.mono (P.closure_mid k))) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (P.chart k).map_source (P.closure_mid k hx)
  choose C hC0 hC using hC
  refine ⟨∑ j, ∑ k, C j k, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j a
    exact (hsm j a).mono (inter_subset_inter_right _ (preimage_mono (subset_univ _)))
  · intro j x _
    constructor <;> linarith [hcp j x]
  · intro j x hx
    have hs : x ∈ (P.chart j).source := P.mid_subset_source j (P.inner_subset_mid j hx)
    have h1 : chartPush (P.chart j) (g j) x = 1 := by
      unfold chartPush
      rw [indicator_of_mem hs]
      exact hg1 j x hx
    simp [h1]
  · intro j
    refine ⟨(P.chart j).symm '' tsupport (g j), (isCompact_symm_image (hgc j) (hgt' j)).isClosed,
      ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact (hgt j hy).2
    · intro x hx
      simp [chartPush_eq_zero (P.chart j) hx.2]
  · intro j k x hx w
    have h := hC j k (P.chart k x) ⟨x, subset_closure hx.2, rfl⟩ w
    have hle : C j k ≤ ∑ j, ∑ k, C j k :=
      (Finset.single_le_sum (fun k _ => hC0 j k) (Finset.mem_univ k)).trans
        (Finset.single_le_sum (f := fun j => ∑ k, C j k)
          (fun j _ => Finset.sum_nonneg fun k _ => hC0 j k) (Finset.mem_univ j))
    have h2 : 0 ≤ ‖w‖ ^ 2 := by positivity
    nlinarith

theorem exists_bumps {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] {D : ℕ} {A : FinHolAtlas D X}
    (P : PotentialCharts A) (j : Fin P.N) : ∃ g : (Fin D → ℂ) → ℝ, ContDiff ℝ ∞ g ∧ (∀ y, 0 ≤ g y ∧ g y ≤ 1) ∧
      (∀ y ∈ P.chart j '' closure (P.inner j), g y = 1) ∧ IsCompact (tsupport g) ∧
      tsupport g ⊆ P.chartMid j := by
  have hcl : closure (P.inner j) ⊆ (P.chart j).source :=
    (P.closure_inner j).trans (P.mid_subset_source j)
  refine exists_smooth_bump_of_isCompact
    (isClosed_closure.isCompact.image_of_continuousOn ((P.chart j).continuousOn.mono hcl))
    ((P.chart j).continuousOn_symm.isOpen_inter_preimage (P.chart j).open_target
      (P.isOpen_mid j)) ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨(P.chart j).map_source (hcl hx), by
    rw [mem_preimage, (P.chart j).left_inv (hcl hx)]; exact P.closure_inner j hx⟩

end

end LevelTowerAlt
end
