module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.TrivSymmApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapSecondProperty
public import GroundTheory.AutomorphicForms.DixmierMalliavinBasic
public import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHaarRightInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHaarRightInvariant
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

namespace GlobalTheory.CompanionTheory.HaarUnimod

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

theorem modularCharacterFun_eq_one (hG : IsUnimod G) (g : G) : modularCharacterFun g = 1 :=
  hG g

theorem isMulRightInvariant_of_isUnimod :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G], IsUnimod G →
      ∀ (μ : Measure G) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro G _ _ _ _ _ _ _ hG μ _
  refine ⟨fun g => ?_⟩
  rw [isMulLeftInvariant_eq_smul (map (· * g) μ) μ,
    ← modularCharacterFun_eq_haarScalarFactor, modularCharacterFun_eq_one hG g, one_smul]

end GlobalTheory.CompanionTheory.HaarUnimod
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHaarRightInvariantStatement
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodular_haar_right_invariant : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G], IsUnimod G → ∀ (μ : Measure G) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod | exact GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod | (intros; apply GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSchwartzBruhatCharacterIntegralOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSchwartzBruhatCharacterIntegralOne
noncomputable section

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob Topology

namespace GlobalTheory.CompanionTheory.FrobNz

private theorem three_halves_norm_sub_one_le_norm_sq_sub_one (u : ℂ) (hu : ‖u - 1‖ < 1/2) :
    3/2 * ‖u - 1‖ ≤ ‖u ^ 2 - 1‖ := by
  have h1 : u ^ 2 - 1 = (u - 1) * (u + 1) := by ring
  have h4 : ‖(2:ℂ)‖ ≤ ‖u + 1‖ + ‖u - 1‖ := by
    calc ‖(2:ℂ)‖ = ‖(u + 1) - (u - 1)‖ := by congr 1; ring
      _ ≤ ‖u + 1‖ + ‖u - 1‖ := norm_sub_le _ _
  have h5 : ‖(2:ℂ)‖ = 2 := by simp
  have h2 : (3:ℝ)/2 ≤ ‖u + 1‖ := by linarith
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (u - 1), mul_le_mul_of_nonneg_left h2 (norm_nonneg (u - 1))]

private theorem eq_one_of_forall_norm_pow_two_pow_sub_one_lt' (w : ℂ) (hw : ∀ n : ℕ, ‖w ^ (2 ^ n) - 1‖ < 1/2) :
    w = 1 := by
  have key : ∀ n : ℕ, (3/2 : ℝ) ^ n * ‖w - 1‖ ≤ ‖w ^ (2 ^ n) - 1‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : w ^ (2 ^ (n + 1)) = (w ^ (2 ^ n)) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e]
      have h3 := three_halves_norm_sub_one_le_norm_sq_sub_one (w ^ (2 ^ n)) (hw n)
      calc (3/2 : ℝ) ^ (n + 1) * ‖w - 1‖ = 3/2 * ((3/2) ^ n * ‖w - 1‖) := by ring
        _ ≤ 3/2 * ‖w ^ (2 ^ n) - 1‖ := by linarith
        _ ≤ ‖(w ^ (2 ^ n)) ^ 2 - 1‖ := h3
  by_contra hne
  have hd : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1/2 / ‖w - 1‖) (by norm_num : (1:ℝ) < 3/2)
  have h1 := key n
  have h2 := hw n
  rw [div_lt_iff₀ hd] at hn
  linarith

theorem exists_compact_open_subgroup_trivial {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (χ : G →* ℂˣ) (hχ : Continuous (fun g => (χ g : ℂ))) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ k ∈ K, χ k = 1 := by
  let V : Set G := {g | ‖(χ g : ℂ) - 1‖ < 1/2}
  have hVo : IsOpen V := isOpen_lt ((hχ.sub continuous_const).norm) continuous_const
  have h1V : (1 : G) ∈ V := by
    show ‖((χ 1 : ℂˣ) : ℂ) - 1‖ < 1/2
    simp
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : G)
  have hW : interior N ∩ V ∈ 𝓝 (1 : G) :=
    Filter.inter_mem (interior_mem_nhds.mpr hN1) (hVo.mem_nhds h1V)
  obtain ⟨s, hs, h1s, hsW⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (X := G)).mem_nhds_iff.mp hW
  have hsclo : IsClopen s := hs
  have hsc : IsCompact s :=
    hNc.of_isClosed_subset hsclo.isClosed
      (hsW.trans (Set.inter_subset_left.trans interior_subset))
  obtain ⟨W, hW1, hWs⟩ := compact_open_separated_mul_right hsc hsclo.isOpen subset_rfl
  let H : Subgroup G :=
    { carrier := {g | ∀ x ∈ s, x * g ∈ s ∧ x * g⁻¹ ∈ s}
      mul_mem' := by
        intro a b ha hb
        change ∀ x ∈ s, x * a ∈ s ∧ x * a⁻¹ ∈ s at ha
        change ∀ x ∈ s, x * b ∈ s ∧ x * b⁻¹ ∈ s at hb
        change ∀ x ∈ s, x * (a * b) ∈ s ∧ x * (a * b)⁻¹ ∈ s
        intro x hx
        refine ⟨?_, ?_⟩
        · rw [← mul_assoc]; exact (hb _ (ha x hx).1).1
        · rw [mul_inv_rev, ← mul_assoc]; exact (ha _ (hb x hx).2).2
      one_mem' := by
        change ∀ x ∈ s, x * 1 ∈ s ∧ x * 1⁻¹ ∈ s
        intro x hx
        simp [hx]
      inv_mem' := by
        intro a ha
        change ∀ x ∈ s, x * a ∈ s ∧ x * a⁻¹ ∈ s at ha
        change ∀ x ∈ s, x * a⁻¹ ∈ s ∧ x * a⁻¹⁻¹ ∈ s
        intro x hx
        rw [inv_inv]
        exact ⟨(ha x hx).2, (ha x hx).1⟩ }
  have hHn : (H : Set G) ∈ 𝓝 (1 : G) := by
    have hWW : W ∩ {g | g⁻¹ ∈ W} ∈ 𝓝 (1 : G) := Filter.inter_mem hW1 (inv_mem_nhds_one G hW1)
    refine Filter.mem_of_superset hWW ?_
    rintro g ⟨hg, hg'⟩
    show ∀ x ∈ s, x * g ∈ s ∧ x * g⁻¹ ∈ s
    intro x hx
    exact ⟨hWs (Set.mul_mem_mul hx hg), hWs (Set.mul_mem_mul hx hg')⟩
  have hHo : IsOpen (H : Set G) := Subgroup.isOpen_of_mem_nhds H hHn
  have hHs : (H : Set G) ⊆ s := by
    intro g hg
    have hg' : ∀ x ∈ s, x * g ∈ s ∧ x * g⁻¹ ∈ s := hg
    simpa using (hg' 1 h1s).1
  have hHc : IsCompact (H : Set G) :=
    hsc.of_isClosed_subset (Subgroup.isClosed_of_isOpen H hHo) hHs
  refine ⟨⟨H, hHo⟩, hHc, ?_⟩
  intro k hk
  have hkH : k ∈ H := hk
  apply Units.ext
  rw [Units.val_one]
  apply eq_one_of_forall_norm_pow_two_pow_sub_one_lt'
  intro n
  have hmem : k ^ (2 ^ n) ∈ H := H.pow_mem hkH _
  have hV : k ^ (2 ^ n) ∈ V := (hsW (hHs hmem)).2
  have hV' : ‖((χ (k ^ (2 ^ n)) : ℂˣ) : ℂ) - 1‖ < 1/2 := hV
  simpa [map_pow, Units.val_pow_eq_pow_val] using hV'

theorem exists_SB_integral_mul_char_eq_one : ∀ (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (χ : G →* ℂˣ),
    Continuous (fun g => (χ g : ℂ)) → ∃ α : SB G, ∫ x, (α : G → ℂ) x * (χ x : ℂ) ∂μ = 1 := by
  intro G _ _ _ _ _ _ _ _ μ _ χ hχ
  obtain ⟨K, hKc, hKχ⟩ := exists_compact_open_subgroup_trivial χ hχ
  have hKo : IsOpen (K : Set G) := K.isOpen
  have hKcl : IsClosed (K : Set G) := K.isClosed
  have hKm : MeasurableSet (K : Set G) := hKo.measurableSet
  have hpos : 0 < μ (K : Set G) := hKo.measure_pos μ ⟨1, one_mem K⟩
  have hfin : μ (K : Set G) < ⊤ := hKc.measure_lt_top
  have hr : (μ (K : Set G)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩
  have hlc : ∀ c : ℂ, IsLocallyConstant ((K : Set G).indicator (fun _ => c)) := by
    intro c s
    by_cases hc : c ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s
    · convert isOpen_univ using 1
      ext x
      by_cases hx : x ∈ (K : Set G) <;> simp [Set.indicator, hx, hc, h0]
    · convert hKo using 1
      ext x
      by_cases hx : x ∈ (K : Set G) <;> simp [Set.indicator, hx, hc, h0]
    · convert hKcl.isOpen_compl using 1
      ext x
      by_cases hx : x ∈ (K : Set G) <;> simp [Set.indicator, hx, hc, h0]
    · convert isOpen_empty using 1
      ext x
      by_cases hx : x ∈ (K : Set G) <;> simp [Set.indicator, hx, hc, h0]
  refine ⟨⟨(K : Set G).indicator (fun _ => (((μ (K : Set G)).toReal : ℂ))⁻¹), ?_⟩, ?_⟩
  · show IsLocallyConstant _ ∧ HasCompactSupport _
    exact ⟨hlc _,
      HasCompactSupport.intro hKc (fun x hx => Set.indicator_of_notMem hx _)⟩
  · have key : ∀ x, (K : Set G).indicator (fun _ => (((μ (K : Set G)).toReal : ℂ))⁻¹) x * (χ x : ℂ) =
        (K : Set G).indicator (fun _ => (((μ (K : Set G)).toReal : ℂ))⁻¹) x := by
      intro x
      by_cases hx : x ∈ (K : Set G)
      · rw [hKχ x hx, Units.val_one, mul_one]
      · rw [Set.indicator_of_notMem hx, zero_mul]
    show ∫ x, (K : Set G).indicator (fun _ => (((μ (K : Set G)).toReal : ℂ))⁻¹) x * (χ x : ℂ) ∂μ = 1
    simp only [key]
    rw [integral_indicator_const _ hKm]
    simp [Measure.real, hpos.ne', hfin.ne, hr]

end GlobalTheory.CompanionTheory.FrobNz
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSchwartzBruhatCharacterIntegralOneStatement
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartzBruhat_character_integral_one : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (χ : G →* ℂˣ), Continuous (fun g => (χ g : ℂ)) → ∃ α : SB G, ∫ x, (α : G → ℂ) x * (χ x : ℂ) ∂μ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.FrobNz.exists_SB_integral_mul_char_eq_one | exact GlobalTheory.CompanionTheory.FrobNz.exists_SB_integral_mul_char_eq_one | (intros; apply GlobalTheory.CompanionTheory.FrobNz.exists_SB_integral_mul_char_eq_one <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.HaarDistr
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.PowNear
namespace PositivityTheory.RgUd.T2

open Complex Real

theorem eq_one_of_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ ≤ 1 / 2) : z = 1 := by

  have hup : ∀ n : ℕ, ‖z‖ ^ n ≤ 3 / 2 := fun n => by
    have h1 : ‖z ^ n‖ ≤ ‖z ^ n - 1‖ + ‖(1 : ℂ)‖ := by
      simpa using norm_le_norm_sub_add (z ^ n) 1
    rw [norm_pow] at h1
    have := h n
    simp at h1
    linarith
  have hlo : ∀ n : ℕ, 1 / 2 ≤ ‖z‖ ^ n := fun n => by
    have h1 : ‖(1 : ℂ)‖ ≤ ‖z ^ n‖ + ‖z ^ n - 1‖ := by
      simpa [norm_sub_rev] using norm_le_insert' (1 : ℂ) (z ^ n)
    rw [norm_pow] at h1
    have := h n
    simp at h1
    linarith
  have hz1 : ‖z‖ = 1 := by
    rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
    · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) hlt
      linarith [hlo n]
    · exact heq
    · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 / 2 : ℝ) hgt
      linarith [hup n]
  have hmem : z ∈ Submonoid.unitSphere ℂ := by
    simpa [Submonoid.unitSphere] using hz1
  let w : Circle := (⟨z, hmem⟩ : Submonoid.unitSphere ℂ)
  have hw : (w : ℂ) = z := rfl
  have hw1 : w = 1 := by
    refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ => ?_
    rw [Circle.mem_centeredArc (by linarith [pi_pos]), Circle.coe_pow, hw]
    refine abs_arg_lt_pi_div_two_iff.2 (Or.inl ?_)
    have h2 := abs_re_le_norm (z ^ n - 1)
    have h3 := h n
    rw [sub_re, one_re] at h2
    have h4 := neg_abs_le ((z ^ n).re - 1)
    linarith
  rw [← hw, hw1, Circle.coe_one]

end PositivityTheory.RgUd.T2
end

noncomputable section

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob GroundTheory.Automorphic
open scoped Pointwise

namespace PositivityTheory.RgUd.T2.HaarDistr

section Group

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

theorem exists_openSubgroup_char_eq_one (χ : G →* ℂˣ) (hχ : Continuous (fun g => (χ g : ℂ))) :
    ∃ K : OpenSubgroup G, ∀ k ∈ K, (χ k : ℂ) = 1 := by
  have hU : IsOpen {g : G | ‖(χ g : ℂ) - 1‖ < 1 / 2} :=
    isOpen_lt (by fun_prop) continuous_const
  have h1 : (1 : G) ∈ {g : G | ‖(χ g : ℂ) - 1‖ < 1 / 2} := by simp
  obtain ⟨K, -, hKU⟩ := exists_openSubgroup_isCompact_subset (hU.mem_nhds h1)
  refine ⟨K, fun k hk => PositivityTheory.RgUd.T2.eq_one_of_pow_near fun n => ?_⟩
  have h2 : k ^ n ∈ K := pow_mem hk n
  have h3 := hKU h2
  simp only [Set.mem_setOf_eq, map_pow, Units.val_pow_eq_pow_val] at h3
  exact h3.le

theorem isLocallyConstant_char (χ : G →* ℂˣ) (hχ : Continuous (fun g => (χ g : ℂ))) :
    IsLocallyConstant (fun g => (χ g : ℂ)) := by
  obtain ⟨K, hK⟩ := exists_openSubgroup_char_eq_one χ hχ
  refine (IsLocallyConstant.iff_exists_open _).2 fun g => ?_
  refine ⟨g • (K : Set G), K.isOpen.smul g, Set.mem_smul_set.2 ⟨1, K.one_mem, mul_one g⟩, ?_⟩
  rintro _ hy
  obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hy
  simp [hK k hk]

def mulLC (ψ : G → ℂ) (hψ : IsLocallyConstant ψ) : SB G →ₗ[ℂ] SB G where
  toFun α := ⟨fun x => ψ x * (α : G → ℂ) x,
    hψ.comp₂ α.2.1 (· * ·), HasCompactSupport.mul_left α.2.2⟩
  map_add' α β := by
    apply Subtype.ext; funext x
    show ψ x * ((α : G → ℂ) x + (β : G → ℂ) x) = ψ x * (α : G → ℂ) x + ψ x * (β : G → ℂ) x
    ring
  map_smul' c α := by
    apply Subtype.ext; funext x
    show ψ x * (c * (α : G → ℂ) x) = c * (ψ x * (α : G → ℂ) x)
    ring

def ind (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) : SB G :=
  ⟨(K : Set G).indicator (fun _ => (1 : ℂ)),
    indicator_mem_locallyConstantCompactSupport (R := ℂ) hK K.isOpen 1⟩

theorem exists_sum_eq (K : OpenSubgroup G) (hKc : IsCompact (K : Set G)) (f : SB G)
    (hK : ∀ g, ∀ k ∈ K, (f : G → ℂ) (g * k) = (f : G → ℂ) g) :
    ∃ s : ℂ, ∀ Φ : SB G →ₗ[ℂ] ℂ, (∀ (g : G) (α : SB G), Φ (transl g α) = Φ α) →
      Φ f = s * Φ (ind K hKc) := by
  classical
  have hf : HasCompactSupport (f : G → ℂ) := f.2.2
  set t := (finite_image_mk_tsupport K hf).toFinset with ht
  have key : f = ∑ x ∈ t, ((f : G → ℂ) x.out) • transl x.out (ind K hKc) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    refine (eq_sum_indicator_coset K hf hK).trans (Finset.sum_congr rfl fun x _ => ?_)
    funext y
    show (x.out • (K : Set G)).indicator (fun _ => (f : G → ℂ) x.out) y =
      (f : G → ℂ) x.out * (K : Set G).indicator (fun _ => (1 : ℂ)) (x.out⁻¹ • y)
    by_cases hy : y ∈ x.out • (K : Set G)
    · have hy' : x.out⁻¹ • y ∈ (K : Set G) := Set.mem_smul_set_iff_inv_smul_mem.1 hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy', mul_one]
    · have hy' : x.out⁻¹ • y ∉ (K : Set G) := fun h => hy (Set.mem_smul_set_iff_inv_smul_mem.2 h)
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy', mul_zero]
  refine ⟨∑ x ∈ t, (f : G → ℂ) x.out, fun Φ hΦ => ?_⟩
  conv_lhs => rw [key]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [_root_.map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, hΦ, smul_eq_mul]

theorem exists_eq_const_mul (Φ Ψ : SB G →ₗ[ℂ] ℂ)
    (hΦ : ∀ (g : G) (α : SB G), Φ (transl g α) = Φ α)
    (hΨ : ∀ (g : G) (α : SB G), Ψ (transl g α) = Ψ α)
    (h0 : ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)), Ψ (ind K hK) ≠ 0) :
    ∃ c : ℂ, ∀ α : SB G, Φ α = c * Ψ α := by
  obtain ⟨K₀, hK₀, -⟩ := exists_openSubgroup_isCompact_subset (G := G) (Filter.univ_mem)
  refine ⟨Φ (ind K₀ hK₀) / Ψ (ind K₀ hK₀), fun α => ?_⟩
  obtain ⟨K₁, -, hK₁⟩ := exists_forall_mul_right (R := ℂ) (show (α : G → ℂ) ∈
    locallyConstantCompactSupport G ℂ ℂ from α.2)
  have hKc : IsCompact ((K₁ ⊓ K₀ : OpenSubgroup G) : Set G) :=
    hK₀.of_isClosed_subset (K₁ ⊓ K₀).isClosed fun x hx => (OpenSubgroup.mem_inf.1 hx).2
  obtain ⟨s, hs⟩ := exists_sum_eq (K₁ ⊓ K₀) hKc α
    (fun g k hk => hK₁ g k (OpenSubgroup.mem_inf.1 hk).1)
  obtain ⟨r, hr⟩ := exists_sum_eq (K₁ ⊓ K₀) hKc (ind K₀ hK₀) (fun g k hk => by
    have hk' : k ∈ K₀ := (OpenSubgroup.mem_inf.1 hk).2
    change (K₀ : Set G).indicator (fun _ => (1 : ℂ)) (g * k) =
      (K₀ : Set G).indicator (fun _ => (1 : ℂ)) g
    by_cases hg : g ∈ (K₀ : Set G)
    · have : g * k ∈ (K₀ : Set G) := K₀.mul_mem hg hk'
      rw [Set.indicator_of_mem hg, Set.indicator_of_mem this]
    · have : g * k ∉ (K₀ : Set G) := fun h => hg (by
        simpa using K₀.mul_mem h (K₀.inv_mem hk'))
      rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem this])
  have a1 := hs Φ hΦ
  have a2 := hs Ψ hΨ
  have b1 := hr Φ hΦ
  have b2 := hr Ψ hΨ
  have hne := h0 _ hK₀
  have hne' := h0 _ hKc
  have hrne : r ≠ 0 := by
    rintro rfl
    exact hne (by simpa using b2)
  rw [a1, a2, b1, b2]
  field_simp

variable [MeasurableSpace G] [BorelSpace G]

def intLC (μ : Measure G) [μ.IsHaarMeasure] : SB G →ₗ[ℂ] ℂ where
  toFun α := ∫ x, (α : G → ℂ) x ∂μ
  map_add' α β := integral_add (α.2.1.continuous.integrable_of_hasCompactSupport α.2.2)
    (β.2.1.continuous.integrable_of_hasCompactSupport β.2.2)
  map_smul' c α := integral_const_mul c _

theorem intLC_apply (μ : Measure G) [μ.IsHaarMeasure] (α : SB G) :
    intLC μ α = ∫ x, (α : G → ℂ) x ∂μ :=
  rfl

theorem intLC_transl (μ : Measure G) [μ.IsHaarMeasure] (g : G) (α : SB G) :
    intLC μ (transl g α) = intLC μ α :=
  integral_mul_left_eq_self (fun x => (α : G → ℂ) x) g⁻¹

theorem intLC_ind_ne_zero (μ : Measure G) [μ.IsHaarMeasure] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) : intLC μ (ind K hK) ≠ 0 := by
  have hm : MeasurableSet (K : Set G) := K.isOpen.measurableSet
  have hpos : 0 < μ (K : Set G) := K.isOpen.measure_pos μ ⟨1, K.one_mem⟩
  have hfin : μ (K : Set G) ≠ ⊤ := hK.measure_lt_top.ne
  show ∫ x, (K : Set G).indicator (fun _ => (1 : ℂ)) x ∂μ ≠ 0
  rw [integral_indicator_const _ hm]
  simp only [measureReal_def, Complex.real_smul, mul_one, ne_eq, Complex.ofReal_eq_zero]
  exact (ENNReal.toReal_pos hpos.ne' hfin).ne'

end Group

theorem eq_const_mul_integral_char :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (χ : G →* ℂˣ),
      Continuous (fun g => (χ g : ℂ)) → ∀ L : SB G →ₗ[ℂ] ℂ,
      (∀ (g : G) (α : SB G), L (transl g α) = (χ g : ℂ) * L α) →
      ∃ c : ℂ, ∀ α : SB G, L α = c * ∫ x, (α : G → ℂ) x * (χ x : ℂ) ∂μ := by
  intro G _ _ _ _ _ _ _ _ _ μ _ χ hχ L hL
  have hc : IsLocallyConstant (fun g => (χ g : ℂ)) := isLocallyConstant_char χ hχ
  have hci : IsLocallyConstant (fun g => ((χ g)⁻¹ : ℂˣ).val) := by
    have hχ' : Continuous (fun g => ((χ⁻¹ g : ℂˣ) : ℂ)) := by
      have : (fun g => ((χ⁻¹ g : ℂˣ) : ℂ)) = fun g => (χ g : ℂ)⁻¹ := by
        funext g; simp
      rw [this]
      exact hχ.inv₀ fun g => (χ g).ne_zero
    exact isLocallyConstant_char χ⁻¹ hχ'
  have hinv : ∀ x, ((χ x)⁻¹ : ℂˣ).val * (χ x : ℂ) = 1 := fun x => by simp
  let T := mulLC _ hci
  let S := mulLC _ hc
  have hTS : ∀ β : SB G, T (S β) = β := fun β => by
    apply Subtype.ext; funext x
    show ((χ x)⁻¹ : ℂˣ).val * ((χ x : ℂ) * (β : G → ℂ) x) = (β : G → ℂ) x
    rw [← mul_assoc, hinv, one_mul]
  have hM : ∀ (g : G) (α : SB G), (L ∘ₗ T) (transl g α) = (L ∘ₗ T) α := by
    intro g α
    have e : T (transl g α) = ((χ g)⁻¹ : ℂˣ).val • transl g (T α) := by
      apply Subtype.ext; funext x
      show ((χ x)⁻¹ : ℂˣ).val * (α : G → ℂ) (g⁻¹ • x) =
        ((χ g)⁻¹ : ℂˣ).val * (((χ (g⁻¹ • x))⁻¹ : ℂˣ).val * (α : G → ℂ) (g⁻¹ • x))
      have e2 : (χ x)⁻¹ = (χ g)⁻¹ * (χ (g⁻¹ • x))⁻¹ := by
        rw [smul_eq_mul, map_mul, map_inv, mul_inv, inv_inv, inv_mul_cancel_left]
      rw [e2, Units.val_mul, mul_assoc]
    simp only [LinearMap.comp_apply]
    rw [e, map_smul, hL, smul_eq_mul, ← mul_assoc, hinv g, one_mul]
  obtain ⟨c, hcM⟩ := exists_eq_const_mul (L ∘ₗ T) (intLC μ) hM (intLC_transl μ)
    (intLC_ind_ne_zero μ)
  refine ⟨c, fun α => ?_⟩
  have h1 := hcM (S α)
  rw [LinearMap.comp_apply, hTS, intLC_apply] at h1
  rw [h1]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

end PositivityTheory.RgUd.T2.HaarDistr
end
end

noncomputable section

open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil

namespace PositivityTheory.PfBern.Frob

theorem pull_symm_pull {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (F : SB X) : pullHomeo e (pullHomeo e.symm F) = F :=
  Subtype.ext (funext fun x => by simp)

theorem pull_pull_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (F : SB Y) : pullHomeo e.symm (pullHomeo e F) = F :=
  Subtype.ext (funext fun y => by simp)

section Main

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {H : Subgroup G} [LocallyCompactSpace H]
  {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] [MulAction G X] [ContinuousSMul G X]
  {p : X → G ⧸ H} (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (σ : Sec H)
  (hpc : Continuous p) (μH : Measure H) [μH.IsHaarMeasure] [LocallyCompactSpace (Fib p)]
  (μG : Measure G) [μG.IsHaarMeasure] (χ : G →* ℂˣ)

theorem fibSmul_fibSmul (a b : H) (z : Fib p) :
    fibSmul hp a (fibSmul hp b z) = fibSmul hp (a * b) z := by
  apply Subtype.ext
  change (a : G) • ((b : G) • z.1) = ((a : G) * (b : G)) • z.1
  exact (mul_smul _ _ _).symm

theorem int_chi_right [μG.IsMulRightInvariant] (α : SB G) (h0 : G) :
    ∫ g, (α : G → ℂ) (g * h0⁻¹) * (χ g : ℂ) ∂μG =
      (χ h0 : ℂ) * ∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG := by
  calc ∫ g, (α : G → ℂ) (g * h0⁻¹) * (χ g : ℂ) ∂μG
      = ∫ g, (α : G → ℂ) (g * h0 * h0⁻¹) * (χ (g * h0) : ℂ) ∂μG :=
        (integral_mul_right_eq_self (fun g => (α : G → ℂ) (g * h0⁻¹) * (χ g : ℂ)) h0).symm
    _ = ∫ g, ((α : G → ℂ) g * (χ g : ℂ)) * (χ h0 : ℂ) ∂μG := by
        congr 1; funext g
        simp only [mul_inv_cancel_right, map_mul, Units.val_mul]
        ring
    _ = _ := by rw [integral_mul_const, mul_comm]

theorem int_chi_left (α : SB G) (g0 : G) :
    ∫ g, ((transl g0 α : SB G) : G → ℂ) g * (χ g : ℂ) ∂μG =
      (χ g0 : ℂ) * ∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG := by
  calc ∫ g, ((transl g0 α : SB G) : G → ℂ) g * (χ g : ℂ) ∂μG
      = ∫ g, (α : G → ℂ) (g0⁻¹ * g) * (χ (g0 * (g0⁻¹ * g)) : ℂ) ∂μG := by
        congr 1; funext g
        simp only [transl_apply, smul_eq_mul, mul_inv_cancel_left]
    _ = ∫ g, (α : G → ℂ) g * (χ (g0 * g) : ℂ) ∂μG :=
        integral_mul_left_eq_self (fun g => (α : G → ℂ) g * (χ (g0 * g) : ℂ)) g0⁻¹
    _ = ∫ g, (χ g0 : ℂ) * ((α : G → ℂ) g * (χ g : ℂ)) ∂μG := by
        congr 1; funext g
        simp only [map_mul, Units.val_mul]
        ring
    _ = _ := integral_const_mul _ _

theorem avg_pull (F : SB (X × H)) :
    avg hp σ hpc μH (pullHomeo (triv hp σ hpc).symm F) =
      intB μH (fun _ => (1 : ℂ)) continuous_const F := by
  show intB μH (fun _ => (1 : ℂ)) continuous_const
    (pullHomeo (triv hp σ hpc) (pullHomeo (triv hp σ hpc).symm F)) = _
  rw [pull_symm_pull]

theorem avg_lift (b0 : SB H) (hb0 : ∫ y, (b0 : H → ℂ) y ∂μH = 1) (f : SB X) :
    avg hp σ hpc μH (pullHomeo (triv hp σ hpc).symm (tens f b0)) = f := by
  rw [avg_pull, intB_tens]
  simp [hb0]

theorem exists_schwartz_integral_one : ∃ b0 : SB H, ∫ y, (b0 : H → ℂ) y ∂μH = 1 := by
  obtain ⟨b0, hb0⟩ := GlobalTheory.T.exists_schwartzBruhat_character_integral_one H μH 1
    (by simp only [MonoidHom.one_apply, Units.val_one]; exact continuous_const)
  exact ⟨b0, by simpa using hb0⟩

theorem span_fap :
    Submodule.span ℂ (Set.range fun q : SB G × SB (Fib p) => fap hp σ hpc μH q.1 q.2) = ⊤ := by
  obtain ⟨b0, hb0⟩ := exists_schwartz_integral_one μH
  rw [eq_top_iff]
  intro f _
  rw [← avg_lift hp σ hpc μH b0 hb0 f]
  exact tens_induction (avg hp σ hpc μH) _ _ (fun a b _ => Submodule.subset_span ⟨(a, b), rfl⟩)

theorem transl_fap (g0 : G) (α : SB G) (φ : SB (Fib p)) :
    transl g0 (fap hp σ hpc μH α φ) = fap hp σ hpc μH (transl g0 α) φ := by
  apply eq_fap
  intro g z
  rw [transl_apply, smul_smul, fap_smul]
  simp only [transl_apply, smul_eq_mul, mul_assoc]

theorem fap_translF (uH : IsUnimod H) (h0 : H) (α : SB G) (φ : SB (Fib p)) :
    fap hp σ hpc μH α (translF hp h0 φ) =
      fap hp σ hpc μH (pullHomeo (Homeomorph.mulRight ((h0 : G)⁻¹)) α) φ := by
  haveI : SecondCountableTopology H := inferInstanceAs (SecondCountableTopology (H : Set G))
  haveI := GlobalTheory.T.unimodular_haar_right_invariant H uH μH
  apply eq_fap
  intro g z
  rw [fap_smul]
  refine Eq.trans ?_ (integral_mul_right_eq_self (μ := μH) _ h0)
  congr 1
  funext h
  simp [translF_apply, pullHomeo_apply, Homeomorph.coe_mulRight, fibSmul_fibSmul, mul_assoc]

theorem eval_fap (hχ : Continuous fun g => (χ g : ℂ)) (ξ : eqv (X := X) χ) (α0 : SB G)
    (hα0 : ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG = 1) (α : SB G) (φ : SB (Fib p)) :
    (ξ : Distr X) (fap hp σ hpc μH α φ) =
      (∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) * (ξ : Distr X) (fap hp σ hpc μH α0 φ) := by
  obtain ⟨c, hc⟩ := PositivityTheory.RgUd.T2.HaarDistr.eq_const_mul_integral_char G μG χ hχ ((ξ : Distr X) ∘ₗ (avg hp σ hpc μH ∘ₗ tensL φ))
    (fun g α => by
      show (ξ : Distr X) (fap hp σ hpc μH (transl g α) φ) =
        (χ g : ℂ) * (ξ : Distr X) (fap hp σ hpc μH α φ)
      rw [← transl_fap]
      exact (mem_eqv.1 ξ.2) g _)
  have h1 : (ξ : Distr X) (fap hp σ hpc μH α φ) = c * ∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG := hc α
  have h2 : (ξ : Distr X) (fap hp σ hpc μH α0 φ) =
      c * ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG := hc α0
  rw [h1, h2, hα0, mul_one, mul_comm]

def FrMap (uG : IsUnimod G) (uH : IsUnimod H) (hχ : Continuous fun g => (χ g : ℂ)) (α0 : SB G)
    (hα0 : ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG = 1) :
    eqv (X := X) χ →ₗ[ℂ] eqvF hp (χ.comp H.subtype) where
  toFun ξ := ⟨(ξ : Distr X) ∘ₗ (avg hp σ hpc μH ∘ₗ tensR α0), fun h0 φ => by
    haveI := GlobalTheory.T.unimodular_haar_right_invariant G uG μG
    show (ξ : Distr X) (fap hp σ hpc μH α0 (translF hp h0 φ)) =
      (χ (h0 : G) : ℂ) * (ξ : Distr X) (fap hp σ hpc μH α0 φ)
    rw [fap_translF hp σ hpc μH uH, eval_fap hp σ hpc μH μG χ hχ ξ α0 hα0]
    congr 1
    have := int_chi_right μG χ α0 (h0 : G)
    rw [hα0, mul_one] at this
    exact this⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem FrMap_apply (uG : IsUnimod G) (uH : IsUnimod H) (hχ : Continuous fun g => (χ g : ℂ))
    (α0 : SB G) (hα0 : ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG = 1) (ξ : eqv (X := X) χ)
    (φ : SB (Fib p)) :
    ((FrMap hp σ hpc μH μG χ uG uH hχ α0 hα0 ξ : eqvF hp _) : Distr (Fib p)) φ =
      (ξ : Distr X) (fap hp σ hpc μH α0 φ) :=
  rfl

theorem FrMap_injective (uG : IsUnimod G) (uH : IsUnimod H)
    (hχ : Continuous fun g => (χ g : ℂ)) (α0 : SB G)
    (hα0 : ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG = 1) :
    Function.Injective (FrMap hp σ hpc μH μG χ uG uH hχ α0 hα0) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ξ hξ
  have h0 : ∀ φ, (ξ : Distr X) (fap hp σ hpc μH α0 φ) = 0 := fun φ => by
    have := LinearMap.congr_fun (congrArg Subtype.val hξ) φ
    rw [FrMap_apply] at this
    exact this
  apply Subtype.ext
  show (ξ : Distr X) = 0
  apply LinearMap.ext_on_range (span_fap hp σ hpc μH)
  rintro ⟨α, φ⟩
  show (ξ : Distr X) (fap hp σ hpc μH α φ) = 0
  rw [eval_fap hp σ hpc μH μG χ hχ ξ α0 hα0, h0, mul_zero]

def intG (hχ : Continuous fun g => (χ g : ℂ)) : SB (G × Fib p) →ₗ[ℂ] SB (Fib p) :=
  intB μG (fun g => (χ g : ℂ)) hχ ∘ₗ pullHomeo (Homeomorph.prodComm (Fib p) G)

theorem intG_tens (hχ : Continuous fun g => (χ g : ℂ)) (α : SB G) (φ : SB (Fib p)) :
    intG μG χ hχ (tens α φ) = (∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) • φ := by
  apply Subtype.ext
  funext z
  show ∫ g, ((α : G → ℂ) g * (φ : Fib p → ℂ) z) * (χ g : ℂ) ∂μG =
    (∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) * (φ : Fib p → ℂ) z
  rw [← integral_mul_const]
  congr 1
  funext g
  ring

theorem FrMap_surjective (uG : IsUnimod G) (uH : IsUnimod H)
    (hχ : Continuous fun g => (χ g : ℂ)) (α0 : SB G)
    (hα0 : ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG = 1) :
    Function.Surjective (FrMap hp σ hpc μH μG χ uG uH hχ α0 hα0) := by
  intro η
  haveI := GlobalTheory.T.unimodular_haar_right_invariant G uG μG
  obtain ⟨b0, hb0⟩ := exists_schwartz_integral_one μH
  let Ψ := triv hp σ hpc
  let Lη : SB (G × Fib p) →ₗ[ℂ] ℂ := (η : Distr (Fib p)) ∘ₗ intG μG χ hχ
  have hL : ∀ α φ, Lη (tens α φ) =
      (∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) * (η : Distr (Fib p)) φ := by
    intro α φ
    show (η : Distr (Fib p)) (intG μG χ hχ (tens α φ)) = _
    rw [intG_tens, LinearMap.map_smul, smul_eq_mul]
  let M : SB (X × H) →ₗ[ℂ] ℂ := Lη ∘ₗ pullHomeo Ψ.symm
  have hM : ∀ (h0 : H) (F : SB (X × H)), M (rtr h0 F) = M F := by
    intro h0 F
    have key2 : (M ∘ₗ rtr h0 ∘ₗ pullHomeo Ψ - Lη) (pullHomeo Ψ.symm F) ∈
        (⊥ : Submodule ℂ ℂ) := by
      refine tens_induction _ ⊥ _ (fun α φ _ => ?_)
      rw [Submodule.mem_bot, LinearMap.sub_apply, sub_eq_zero]
      have e : rtr h0 (pullHomeo Ψ (tens α φ)) =
          pullHomeo Ψ (tens (pullHomeo (Homeomorph.mulRight (h0 : G)) α) (translF hp h0 φ)) := by
        apply Subtype.ext
        funext q
        simp [rtr, Ψ, triv, translF_apply, fibSmul_fibSmul, mul_assoc]
      show Lη (pullHomeo Ψ.symm (rtr h0 (pullHomeo Ψ (tens α φ)))) = Lη (tens α φ)
      rw [e, pull_pull_symm, hL, hL, (η.2 h0 φ)]
      have e2 : ∫ g, ((pullHomeo (Homeomorph.mulRight (h0 : G)) α : SB G) : G → ℂ) g *
          (χ g : ℂ) ∂μG = (χ ((h0 : G)⁻¹) : ℂ) * ∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG := by
        have := int_chi_right μG χ α ((h0 : G)⁻¹)
        simpa using this
      have hu : (χ ((h0 : G)⁻¹) : ℂ) * (χ (h0 : G) : ℂ) = 1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      rw [e2]
      calc (χ ((h0 : G)⁻¹) : ℂ) * (∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) *
            (((χ.comp H.subtype) h0 : ℂˣ) * (η : Distr (Fib p)) φ)
          = ((χ ((h0 : G)⁻¹) : ℂ) * (χ (h0 : G) : ℂ)) *
            ((∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) * (η : Distr (Fib p)) φ) := by
            simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
            ring
        _ = _ := by rw [hu, one_mul]
    rw [Submodule.mem_bot, LinearMap.sub_apply, sub_eq_zero] at key2
    simp only [LinearMap.comp_apply, pull_symm_pull] at key2
    exact key2
  let ξ0 : Distr X := M ∘ₗ tensL b0
  have hfac : ∀ F, M F = ξ0 (intB μH (fun _ => (1 : ℂ)) continuous_const F) :=
    fun F => factor_intB μH uH b0 hb0 M hM F
  have hξ0 : ∀ α φ, ξ0 (fap hp σ hpc μH α φ) =
      (∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) * (η : Distr (Fib p)) φ := by
    intro α φ
    show ξ0 (intB μH (fun _ => (1 : ℂ)) continuous_const (pullHomeo Ψ (tens α φ))) = _
    rw [← hfac]
    show Lη (pullHomeo Ψ.symm (pullHomeo Ψ (tens α φ))) = _
    rw [pull_pull_symm, hL]
  have hmem : ξ0 ∈ eqv (X := X) χ := by
    rw [mem_eqv]
    intro g f
    have : ξ0 ∘ₗ transl g = (χ g : ℂ) • ξ0 := by
      apply LinearMap.ext_on_range (span_fap hp σ hpc μH)
      rintro ⟨α, φ⟩
      show ξ0 (transl g (fap hp σ hpc μH α φ)) = (χ g : ℂ) * ξ0 (fap hp σ hpc μH α φ)
      rw [transl_fap, hξ0, hξ0, int_chi_left]
      ring
    exact LinearMap.congr_fun this f
  refine ⟨⟨ξ0, hmem⟩, ?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro φ
  show ξ0 (fap hp σ hpc μH α0 φ) = (η : Distr (Fib p)) φ
  rw [hξ0, hα0, one_mul]

theorem supportedIn_FrMap (uG : IsUnimod G) (uH : IsUnimod H)
    (hχ : Continuous fun g => (χ g : ℂ)) (α0 : SB G)
    (hα0 : ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG = 1) (ξ : eqv (X := X) χ) (C : Set X)
    (hC : ∀ (g : G), ∀ x ∈ C, g • x ∈ C) :
    SupportedIn (ξ : Distr X) C ↔
      SupportedIn ((FrMap hp σ hpc μH μG χ uG uH hχ α0 hα0 ξ : eqvF hp _) : Distr (Fib p))
        (Subtype.val ⁻¹' C) := by
  constructor
  · intro hξ φ hφ
    rw [FrMap_apply]
    apply hξ
    intro x hx
    by_contra hxC
    rw [Set.mem_compl_iff, not_not] at hxC
    apply hx
    rw [fap_apply]
    have h0 : ∀ h : H, (φ : Fib p → ℂ) (fibSmul hp h⁻¹ (zpart hp σ x)) = 0 := by
      intro h
      by_contra hne
      have hc := hφ hne
      apply hc
      show ((h⁻¹ : H) : G) • ((σ.s (p x))⁻¹ • x) ∈ C
      exact hC _ _ (hC _ _ hxC)
    simp [h0]
  · intro hF f hf
    obtain ⟨b0, hb0⟩ := exists_schwartz_integral_one μH
    rw [← avg_lift hp σ hpc μH b0 hb0 f]
    have key3 : ((ξ : Distr X) ∘ₗ avg hp σ hpc μH)
        (pullHomeo (triv hp σ hpc).symm (tens f b0)) ∈ (⊥ : Submodule ℂ ℂ) := by
      refine tens_induction _ ⊥ _ (fun a b hab => ?_)
      rw [Submodule.mem_bot]
      show (ξ : Distr X) (fap hp σ hpc μH a b) = 0
      rw [eval_fap hp σ hpc μH μG χ hχ ξ α0 hα0]
      by_cases ha : ∃ g, (a : G → ℂ) g ≠ 0
      · obtain ⟨g, hg⟩ := ha
        have hb : (ξ : Distr X) (fap hp σ hpc μH α0 b) = 0 := by
          rw [← FrMap_apply hp σ hpc μH μG χ uG uH hχ α0 hα0]
          apply hF
          intro z hz hzC
          have h1 := hab (g, z) hg hz
          simp only [pullHomeo_apply, triv_symm_apply, tens_apply] at h1
          exact hf (left_ne_zero_of_mul h1) (hC g _ hzC)
        rw [hb, mul_zero]
      · push_neg at ha
        have : ∫ g, (a : G → ℂ) g * (χ g : ℂ) ∂μG = 0 := by simp [ha]
        rw [this, zero_mul]
    rw [Submodule.mem_bot] at key3
    exact key3

end Main

theorem frobeniusReciprocity : FrobeniusReciprocity := by
  intro G _ _ _ _ _ _ _ _ _ H _ hH uG uH X _ _ _ _ _ _ p hpc hp χ hχ μG _ μH _
  haveI : IsClosed (H : Set G) := hH
  haveI : LocallyCompactSpace (Fib p) := by
    have hc : IsClosed {x : X | p x = ((1 : G) : G ⧸ H)} :=
      (isClosed_singleton (x := ((1 : G) : G ⧸ H))).preimage hpc
    exact hc.locallyCompactSpace
  obtain ⟨s, hs, hsec⟩ := GlobalTheory.T.exists_continuous_section_quotient G H hH
  let σ : Sec H := ⟨s, hs, hsec⟩
  obtain ⟨α0, hα0⟩ := GlobalTheory.T.exists_schwartzBruhat_character_integral_one G μG χ hχ
  let Fr := LinearEquiv.ofBijective (FrMap hp σ hpc μH μG χ uG uH hχ α0 hα0)
    ⟨FrMap_injective hp σ hpc μH μG χ uG uH hχ α0 hα0,
      FrMap_surjective hp σ hpc μH μG χ uG uH hχ α0 hα0⟩
  refine ⟨Fr, ?_, ?_⟩
  · intro ξ C _ hC
    exact supportedIn_FrMap hp σ hpc μH μG χ uG uH hχ α0 hα0 ξ C hC
  · intro ξ α φ f hf
    rw [eq_fap hp σ hpc μH α φ f hf]
    exact eval_fap hp σ hpc μH μG χ hχ ξ α0 hα0 α φ

end PositivityTheory.PfBern.Frob
