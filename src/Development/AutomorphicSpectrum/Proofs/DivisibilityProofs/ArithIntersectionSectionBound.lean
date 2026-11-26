module

public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionDivisorSupport
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GfForms

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ChartLatticePowerSection
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ChartLatticePowerSection
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top.EffNm

theorem exists_pow_mul_pow_mem {Ω : Type} [Field Ω] (R : Subalgebra ℤ Ω) {u g h : Ω}
    (hu : u ∈ integralClosure R Ω) (hg : g ∈ R) (hh : h ∈ R) (e : u * h = g) :
    ∃ M : ℕ, ∀ n : ℕ, h ^ M * u ^ n ∈ R := by
  classical
  have hI : IsIntegral R u := hu
  obtain ⟨S, hS⟩ := hI.fg_adjoin_singleton
  have key : ∀ x ∈ Algebra.adjoin R {u}, ∃ m : ℕ, h ^ m * x ∈ R := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨1, by rw [pow_one, mul_comm, e]; exact hg⟩
    | algebraMap r => exact ⟨0, by simpa using r.2⟩
    | add x z _ _ ihx ihz =>
      obtain ⟨m₁, h₁⟩ := ihx
      obtain ⟨m₂, h₂⟩ := ihz
      refine ⟨m₁ + m₂, ?_⟩
      have e' : h ^ (m₁ + m₂) * (x + z) = h ^ m₂ * (h ^ m₁ * x) + h ^ m₁ * (h ^ m₂ * z) := by
        rw [pow_add]; ring
      rw [e']
      exact add_mem (mul_mem (pow_mem hh _) h₁) (mul_mem (pow_mem hh _) h₂)
    | mul x z _ _ ihx ihz =>
      obtain ⟨m₁, h₁⟩ := ihx
      obtain ⟨m₂, h₂⟩ := ihz
      refine ⟨m₁ + m₂, ?_⟩
      have e' : h ^ (m₁ + m₂) * (x * z) = (h ^ m₁ * x) * (h ^ m₂ * z) := by
        rw [pow_add]; ring
      rw [e']
      exact mul_mem h₁ h₂
  have hfin : ∀ T : Finset Ω, (∀ x ∈ T, x ∈ Algebra.adjoin R {u}) →
      ∃ M : ℕ, ∀ x ∈ T, h ^ M * x ∈ R := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨0, by simp⟩
    | insert x T _ ih =>
      intro hT
      obtain ⟨M, hM⟩ := ih fun z hz => hT z (Finset.mem_insert_of_mem hz)
      obtain ⟨m, hm⟩ := key x (hT x (Finset.mem_insert_self x T))
      refine ⟨M + m, fun z hz => ?_⟩
      rcases Finset.mem_insert.1 hz with rfl | hz
      · have e' : h ^ (M + m) * z = h ^ M * (h ^ m * z) := by rw [pow_add]; ring
        rw [e']
        exact mul_mem (pow_mem hh _) hm
      · have e' : h ^ (M + m) * z = h ^ m * (h ^ M * z) := by rw [pow_add]; ring
        rw [e']
        exact mul_mem (pow_mem hh _) (hM z hz)
  have hSsub : ∀ x ∈ S, x ∈ Algebra.adjoin R {u} := by
    intro x hx
    have : x ∈ Subalgebra.toSubmodule (Algebra.adjoin R {u}) := hS ▸ Submodule.subset_span hx
    exact this
  obtain ⟨M, hM⟩ := hfin S hSsub
  refine ⟨M, fun n => ?_⟩
  have hn : u ^ n ∈ Subalgebra.toSubmodule (Algebra.adjoin R {u}) :=
    pow_mem (Algebra.subset_adjoin (Set.mem_singleton u)) n
  rw [← hS] at hn
  have hall : ∀ x ∈ Submodule.span R (S : Set Ω), h ^ M * x ∈ R := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hM x hx
    | zero => simp
    | add x z _ _ ihx ihz => rw [mul_add]; exact add_mem ihx ihz
    | smul r x _ ih =>
      have e' : h ^ M * r • x = (r : Ω) * (h ^ M * x) := by
        rw [Algebra.smul_def]
        show h ^ M * ((r : Ω) * x) = _
        ring
      rw [e']
      exact mul_mem r.2 ih
  exact hall _ hn

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem exists_form_at (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) (hb : Birational y)
    (hs : s ∈ chartLatNm y a 1) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (e : K → ℕ) (F : MRing ι), IsMultiHomog F e ∧ aeval y F ≠ 0 ∧
      ∀ n : ℕ, aeval y F * s ^ n * ∏ k, y ⟨k, c k⟩ ^ (-((e k : ℤ) + n * a k)) ∈ chartRingZ y c := by
  classical
  have hu := hs c hc
  set u : Ω := s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) with hudef
  obtain ⟨d, g, h, hg, hh, hh0, heq⟩ := hb u
  have hG := (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).1
    (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.chartLat_form (y := y) hg) c hc
  have hH := (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).1
    (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.chartLat_form (y := y) hh) c hc
  obtain ⟨M, hM⟩ := exists_pow_mul_pow_mem (chartRingZ y c) hu hG hH (by rw [heq]; ring)
  refine ⟨M • d, h ^ M, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_pow hh M, ?_, fun n => ?_⟩
  · rw [map_pow]; exact pow_ne_zero _ hh0
  · have e' : aeval y (h ^ M) * s ^ n * ∏ k, y ⟨k, c k⟩ ^ (-((((M • d) k : ℕ) : ℤ) + n * a k)) =
        (aeval y h * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ))) ^ M * u ^ n := by
      have e2 : ∏ k, y ⟨k, c k⟩ ^ (-((((M • d) k : ℕ) : ℤ) + n * a k)) =
          (∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ))) ^ M * (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) ^ n := by
        rw [← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ (hc k)]
        congr 1
        simp only [Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      rw [e2, map_pow, hudef, mul_pow, mul_pow]
      ring
    rw [e']
    exact hM n

end GlobalTheory.CompanionTheory.Ar.Top.EffNm

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem exists_mul_pow_mem_chartLat_of_mem_chartLatNm :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (a : K → ℤ) (s : Ω), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d → Birational y → s ∈ chartLatNm y a 1 → ∃ (b : K → ℤ) (c : Ω), c ≠ 0 ∧ ∀ n : ℕ, c * s ^ n ∈ chartLat y (b + (n : ℤ) • a) 1 := by
  intro K _ ι _ Ω _ y _ a s _ hb hs
  classical
  have hex : ∀ c : ∀ k, ι k, ∃ (e : K → ℕ) (F : MRing ι), IsMultiHomog F e ∧ aeval y F ≠ 0 ∧
      ((∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ n : ℕ,
        aeval y F * s ^ n * ∏ k, y ⟨k, c k⟩ ^ (-((e k : ℤ) + n * a k)) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨e, F, h1, h2, h3⟩ := EffNm.exists_form_at y a s hb hs c hc
      exact ⟨e, F, h1, h2, fun _ => h3⟩
    · exact ⟨0, 1, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one, by simp, fun h => absurd h hc⟩
  choose e F hF hF0 hFc using hex
  refine ⟨∑ c, fun k => (e c k : ℤ), ∏ c, aeval y (F c),
    Finset.prod_ne_zero_iff.2 fun c _ => hF0 c, fun n => ?_⟩
  rw [GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.mem_chartLat_one]
  intro c₀ hc₀
  have hP := (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).1
    (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.chartLat_prod (y := y)
      (Finset.univ.erase c₀) (fun c => aeval y (F c)) (fun c k => (e c k : ℤ))
      (fun c _ => GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.chartLat_form (y := y) (hF c)))
    c₀ hc₀
  have hQ := hFc c₀ hc₀ n
  have e' : (∏ c, aeval y (F c)) * s ^ n *
        ∏ k, y ⟨k, c₀ k⟩ ^ (-(((∑ c, fun k => (e c k : ℤ)) + (n : ℤ) • a) k)) =
      (aeval y (F c₀) * s ^ n * ∏ k, y ⟨k, c₀ k⟩ ^ (-((e c₀ k : ℤ) + n * a k))) *
        ((∏ c ∈ Finset.univ.erase c₀, aeval y (F c)) *
          ∏ k, y ⟨k, c₀ k⟩ ^ (-((∑ c ∈ Finset.univ.erase c₀, fun k => (e c k : ℤ)) k))) := by
    have e1 : ∏ c, aeval y (F c) = aeval y (F c₀) * ∏ c ∈ Finset.univ.erase c₀, aeval y (F c) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ c₀)).symm
    have e2 : ∏ k, y ⟨k, c₀ k⟩ ^ (-(((∑ c, fun k => (e c k : ℤ)) + (n : ℤ) • a) k)) =
        (∏ k, y ⟨k, c₀ k⟩ ^ (-((e c₀ k : ℤ) + n * a k))) *
          ∏ k, y ⟨k, c₀ k⟩ ^ (-((∑ c ∈ Finset.univ.erase c₀, fun k => (e c k : ℤ)) k)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_add₀ (hc₀ k)]
      congr 1
      have e3 : (∑ c, fun k => (e c k : ℤ)) =
          (fun k => (e c₀ k : ℤ)) + ∑ c ∈ Finset.univ.erase c₀, fun k => (e c k : ℤ) :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ c₀)).symm
      rw [e3]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, e2]
    ring
  rw [e']
  exact mul_mem hQ hP

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ChartLatticePowerSectionStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_power_section : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (a : K → ℤ) (s : Ω), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d → Birational y → s ∈ chartLatNm y a 1 → ∃ (b : K → ℤ) (c : Ω), c ≠ 0 ∧ ∀ n : ℕ, c * s ^ n ∈ chartLat y (b + (n : ℤ) • a) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.exists_mul_pow_mem_chartLat_of_mem_chartLatNm | exact GlobalTheory.CompanionTheory.Ar.Top.exists_mul_pow_mem_chartLat_of_mem_chartLatNm | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.exists_mul_pow_mem_chartLat_of_mem_chartLatNm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionSectionRecursion
section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.PointsIntegralSectionSnoc
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics

theorem mixedDisc_eq_zero {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (k : Fin D)
    (hk : A k = 0) : mixedDisc A = 0 := by
  unfold mixedDisc
  have h : ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ j ∈ S, A j).det = 0 := by
    rw [← Finset.powerset_univ, ← Finset.insert_erase (Finset.mem_univ k),
      Finset.sum_powerset_insert (Finset.notMem_erase k _), ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun S hS => ?_
    have hkS : k ∉ S := fun h => Finset.notMem_erase k _ (Finset.mem_powerset.mp hS h)
    have hc : (insert k S).card ≤ D := by simpa using Finset.card_le_univ (insert k S)
    rw [Finset.card_insert_of_notMem hkS] at hc
    rw [Finset.sum_insert hkS, hk, zero_add, Finset.card_insert_of_notMem hkS,
      show D - S.card = D - (S.card + 1) + 1 by omega, pow_succ]
    ring
  rw [h, mul_zero]

theorem maDensity_eq_zero {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (k : Fin D) (c : ℝ)
    (hk : φ k = fun _ => c) (z : Fin D → ℂ) : maDensity φ z = 0 := by
  have h : cxHessian (φ k) z = 0 := by
    rw [hk]
    funext i j
    simp [cxHessian]
  unfold maDensity
  rw [mixedDisc_eq_zero _ k h]
  simp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ptsIntegral_eq_zero (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (k : Fin e) (c : ℝ) (hk : φ k = fun _ => c) :
    ptsIntegral P φ g = 0 := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have hs : ∀ y w, sheetDensity P hΨ.choose φ g y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs
      · rw [maDensity_eq_zero _ k c (by rw [hk]), mul_zero]
      · rfl
    simp [hs]
  · rfl

theorem geoNum_last_zero (n : ℕ) (V : Ideal (MRing ι)) (a : Fin (n + 1) → K → ℤ)
    (ha : a (Fin.last n) = 0) : geoNum (n + 1) V a = 0 := by
  rw [geoNum.eq_2]
  simp [ha]

theorem snoc_snoc_swap {α : Type*} {e : ℕ} (L : Fin e → α) (A B : α) :
    (Fin.snoc (Fin.snoc L A : Fin (e + 1) → α) B : Fin (e + 2) → α) =
      (Fin.snoc (Fin.snoc L B : Fin (e + 1) → α) A : Fin (e + 2) → α) ∘
        Equiv.swap (Fin.last (e + 1)) (Fin.last e).castSucc := by
  funext k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp
  · refine Fin.lastCases ?_ (fun k => ?_) k
    · simp
    · have h1 : k.castSucc.castSucc ≠ Fin.last (e + 1) := (Fin.castSucc_lt_last _).ne
      have h2 : k.castSucc.castSucc ≠ (Fin.last e).castSucc := fun h =>
        (Fin.castSucc_lt_last k).ne (Fin.castSucc_injective _ h)
      simp [Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem smooth_snoc {e : ℕ} {L : Fin e → HermLine ι} {A : HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (j : Fin (e + 1)) :
    IsSmoothHerm ((Fin.snoc L A : Fin (e + 1) → HermLine ι) j) := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simpa using hA
  · simpa using hL k

theorem points_integral_section_snoc : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s → ptsIntegral P (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) = ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
  classical
  intro II hII hDS K _ ι _ P e L A s hP hL hA hs
  obtain ⟨hIS, -, -, -⟩ := hII
  obtain ⟨hperm, -, hrec⟩ := hIS K ι
  set O : HermLine ι := HermLine.ofWeight (K := K) (ι := ι) (fun _ => (-1 : ℝ)) (fun _ _ _ => rfl) with hO
  have hOs : IsSmoothHerm O := by
    show ContDiffOn ℝ _ (fun _ => Real.exp (-(-1 : ℝ))) _
    exact contDiffOn_const
  have hsnL := smooth_snoc hL hA
  have hsnO := smooth_snoc hL hOs
  obtain ⟨a, ha, hsa, hsP⟩ := hs
  have h1 := intersection_constant_metric_line II hIS K ι P (e + 1) (Fin.snoc L A) (-1) hP hsnL
  have h2 := hrec P (e + 1) (Fin.snoc L O) A s a hP hsnO hA ha hsa hsP
  have h3 : II K ι P (e + 1 + 1) (Fin.snoc (Fin.snoc L A) O) =
      II K ι P (e + 1 + 1) (Fin.snoc (Fin.snoc L O) A) := by
    rw [snoc_snoc_swap L A O]
    exact hperm P (e + 1 + 1) _ _ hP (smooth_snoc hsnO hA)
  have h4 := h1.symm.trans (h3.trans h2)
  rw [neg_neg, one_mul] at h4
  rw [h4]
  unfold recR
  have hz : arInt P s A (Fin.snoc L O) = 0 :=
    ptsIntegral_eq_zero P _ _ (Fin.last e) 1 (by funext z; simp [hO, HermLine.ofWeight])
  rw [hz, sub_zero]
  refine finsum_congr fun W => ?_
  rw [finsum_eq_if, finsum_eq_if]
  by_cases hW : W ∈ divSupp P s
  · have hW' : W ∈ divSupp P s ↔ True := iff_true_intro hW
    by_cases hh : IsHorizontal W
    · have hWa := (hDS K ι P (e + 1) A s W hP ⟨a, ha, hsa, hsP⟩ hW).1 hh
      have hh' : IsHorizontal W ↔ True := iff_true_intro hh
      simp only [hW', hh', and_self, if_true]
      rw [intersection_constant_metric_line II hIS K ι W e L (-1) hWa hL]
      ring
    · have hh' : IsHorizontal W ↔ False := iff_false_intro hh
      simp only [hW', hh', and_false, if_true, if_false]
      rw [geoNum_last_zero e W _ (by simp [hO, HermLine.ofWeight])]
      simp
  · have hW' : W ∈ divSupp P s ↔ False := iff_false_intro hW
    simp only [hW', false_and, if_false]

end RootFieldNumerics
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionSectionRecursion
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.EffLat

open PositivityTheory.HtPt.Gf (hom_mul hom_add hom_mon hom_of_eq hom_sub aeval_mon mon_not_mem mem_mCoordIdeal mon)
open GroundTheory.Heights₂.Heights.NumbersDVR (length_localizedQuot_ne_top mem_minimalPrimes_sup_span_mul
  length_localizedQuot_sup_span_mul localizedQuot_subsingleton_of_not_le)

theorem len_le_of_rel {A : Type*} [CommRing A] [IsNoetherianRing A] {P W : Ideal A} [hP : P.IsPrime]
    [hWp : W.IsPrime] {g h t r : A} (hg : g ∉ P) (ht : t ∉ W) (hrel : t * g - r * h ∈ P)
    (hW : W ∈ (P ⊔ Ideal.span {h}).minimalPrimes) :
    W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧
      (Module.length (Localization.AtPrime W)
        (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {h})))).toNat ≤
      (Module.length (Localization.AtPrime W)
        (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {g})))).toNat := by
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have htP : t ∉ P := fun h' => ht (hPW h')
  have hrP : r ∉ P := by
    intro hr
    have h1 : t * g ∈ P := by
      have := P.add_mem hrel (P.mul_mem_right h hr)
      rwa [sub_add_cancel] at this
    exact (hP.mem_or_mem h1).elim htP hg
  have hm := mem_minimalPrimes_sup_span_mul (P := P) (x := h) (y := r) hrP hW
  have heq : P ⊔ Ideal.span {h * r} = P ⊔ Ideal.span {t * g} := by
    apply le_antisymm
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : h * r = t * g - (t * g - r * h) := by ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
        (Ideal.mem_sup_left hrel)
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : t * g = (t * g - r * h) + h * r := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hrel)
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rw [heq] at hm
  have htg : t * g ∈ W := hm.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hgW : g ∈ W := (hWp.mem_or_mem htg).resolve_left ht
  have hWg : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes := by
    refine ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hgW)⟩, fun Q hQ hQW => ?_⟩
    refine hm.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2)
      ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩ hQW
    exact Q.mul_mem_left t (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  refine ⟨hWg, ?_⟩
  have e1 := length_localizedQuot_sup_span_mul P W (x := t) g htP
  have e2 := length_localizedQuot_sup_span_mul P W (x := r) h hrP
  have heq' : P ⊔ Ideal.span {r * h} = P ⊔ Ideal.span {t * g} := by rw [mul_comm r h, heq]
  rw [heq'] at e2
  have ht0 : Module.length (Localization.AtPrime W)
      (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {t}))) = 0 := by
    have hnle : ¬ (P ⊔ Ideal.span {t}) ≤ W := fun h' =>
      ht (h' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    have := localizedQuot_subsingleton_of_not_le (P ⊔ Ideal.span {t}) W hnle
    exact Module.length_eq_zero_iff.mpr this
  rw [ht0, add_zero] at e1
  have hfin := length_localizedQuot_ne_top _ W hm
  rw [e1] at hfin e2
  refine ENat.toNat_le_toNat ?_ hfin
  rw [e2]
  exact le_self_add

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem y_ne_of_not_mem {y : (Σ k, ι k) → Ω} {p : Σ k, ι k}
    (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply h
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]

theorem eval_one_coneMap (y : (Σ k, ι k) → Ω) (f : MRing ι) :
    eval (fun _ => (1 : Ω)) (mConeMap y f) = aeval y f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    simp [mConeMap]

theorem not_mem_of_aeval_ne {y : (Σ k, ι k) → Ω} {f : MRing ι} (hf : aeval y f ≠ 0) :
    f ∉ mCoordIdeal y := by
  intro h
  apply hf
  rw [← eval_one_coneMap]
  have h0 : mConeMap y f = 0 := h
  rw [h0, map_zero]

theorem prod_pow_add (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a b : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (a + b) k = (∏ k, y ⟨k, c k⟩ ^ a k) * ∏ k, y ⟨k, c k⟩ ^ b k := by
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem exists_form_of_mem_chart {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {t : Ω} (ht : t ∈ chartRingZ y c) :
    ∃ (N : K → ℕ) (r : MRing ι), IsMultiHomog r N ∧ aeval y r = t * ∏ k, y ⟨k, c k⟩ ^ N k := by
  classical
  unfold chartRingZ at ht
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨Pi.single p.1 1, X p, ?_, ?_⟩
    · intro m hm k
      rw [support_X] at hm
      rw [Finset.mem_singleton.mp hm]
      obtain ⟨k0, i0⟩ := p
      by_cases hk : k = k0
      · subst hk
        simp [Finsupp.single_apply]
      · have : ∀ i, (Finsupp.single (⟨k0, i0⟩ : Σ k, ι k) 1 : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩ = 0 := by
          intro i
          rw [Finsupp.single_apply, if_neg]
          intro h
          exact hk (congrArg Sigma.fst h).symm
        simp [this, Pi.single_eq_of_ne hk]
    · have hprod : ∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 1 : K → ℕ) k = y ⟨p.1, c p.1⟩ := by
        rw [Finset.prod_eq_single p.1 (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
        simp
      rw [hprod, aeval_X, div_mul_cancel₀ _ (hc _)]
  | algebraMap n =>
    refine ⟨0, C n, ?_, by simp⟩
    intro m hm k
    rw [C_apply] at hm
    rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
    simp
  | add a b _ _ h1 h2 =>
    obtain ⟨N1, r1, hr1, e1⟩ := h1
    obtain ⟨N2, r2, hr2, e2⟩ := h2
    refine ⟨N1 + N2, r1 * mon c N2 + r2 * mon c N1, hom_add (hom_mul hr1 (hom_mon c N2))
      (hom_of_eq (hom_mul hr2 (hom_mon c N1)) fun k => by simp [add_comm]), ?_⟩
    rw [map_add (f := _), map_mul, map_mul, aeval_mon, aeval_mon, e1, e2, prod_pow_add]
    ring
  | mul a b _ _ h1 h2 =>
    obtain ⟨N1, r1, hr1, e1⟩ := h1
    obtain ⟨N2, r2, hr2, e2⟩ := h2
    refine ⟨N1 + N2, r1 * r2, hom_mul hr1 hr2, ?_⟩
    rw [map_mul, e1, e2, prod_pow_add]
    ring

theorem chart_rel {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {a : K → ℤ} {s : Ω}
    (hs : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) ∈ chartRingZ y c) {g h : MRing ι}
    {dg dh : K → ℕ} (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh)
    (hd : ∀ k, (dg k : ℤ) = dh k + a k) (e : aeval y g = s * aeval y h) :
    ∃ (u : K → ℕ) (r : MRing ι), mon c u * g - r * h ∈ mCoordIdeal y := by
  obtain ⟨N, r, hr, er⟩ := exists_form_of_mem_chart hc hs
  let v : K → ℕ := fun k => (a k).toNat
  let u : K → ℕ := fun k => N k + (-a k).toNat
  refine ⟨u, r * mon c v, mem_mCoordIdeal (d := u + dg) (hom_sub (hom_mul (hom_mon c u) hg)
    (hom_of_eq (hom_mul (hom_mul hr (hom_mon c v)) hh) ?_)) ?_⟩
  · intro k
    have := hd k
    simp only [Pi.add_apply, u, v]
    omega
  · rw [map_sub, map_mul, map_mul, map_mul, aeval_mon, aeval_mon, e, er, sub_eq_zero]
    have key : ∏ k, y ⟨k, c k⟩ ^ u k = (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) *
        (∏ k, y ⟨k, c k⟩ ^ N k) * ∏ k, y ⟨k, c k⟩ ^ v k := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hy := hc k
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hy, ← zpow_add₀ hy]
      congr 1
      simp only [u, v]
      push_cast
      omega
    rw [key]
    ring

theorem exists_rep {y : (Σ k, ι k) → Ω} (hb : Birational y) {c : ∀ k, ι k}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a : K → ℤ) (s : Ω) :
    ∃ (g h : MRing ι) (dg dh : K → ℕ), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
      (∀ k, (dg k : ℤ) = dh k + a k) ∧ aeval y h ≠ 0 ∧ aeval y g = s * aeval y h := by
  obtain ⟨d, g0, h0, hg, hh, hne, e⟩ := hb (s * ∏ k, y ⟨k, c k⟩ ^ (-a k))
  refine ⟨mon c (fun k => (a k).toNat) * g0, mon c (fun k => (-a k).toNat) * h0, _, _,
    hom_mul (hom_mon c _) hg, hom_mul (hom_mon c _) hh, ?_, ?_, ?_⟩
  · intro k
    simp only [Pi.add_apply]
    push_cast
    omega
  · rw [map_mul, aeval_mon]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)) hne
  · rw [map_mul, map_mul, aeval_mon, aeval_mon, e]
    have key : (∏ k, y ⟨k, c k⟩ ^ (a k).toNat) * ∏ k, y ⟨k, c k⟩ ^ (-a k) =
        ∏ k, y ⟨k, c k⟩ ^ (-a k).toNat := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hy := hc k
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hy]
      congr 1
      omega
    rw [← key]
    ring

theorem deg_tensor (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (A B : HermLine ι)
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 2)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hB : IsSmoothHerm B) :
    ptsIntegral P (fun j z => Real.log (((Fin.snoc L (A.tensor B) : Fin (e + 1) → HermLine ι) j).h z))
        (fun _ => 1) =
      ptsIntegral P (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z))
        (fun _ => 1) +
      ptsIntegral P (fun j z => Real.log (((Fin.snoc L B : Fin (e + 1) → HermLine ι) j).h z))
        (fun _ => 1) := by
  set O : HermLine ι := HermLine.ofWeight (fun _ => (-1 : ℝ)) (fun _ _ _ => rfl) with hO
  have hOs : IsSmoothHerm O := RootFieldNumerics.smooth_constLine _
  have key : ∀ Y : HermLine ι, IsSmoothHerm Y →
      II K ι P (e + 2) (Fin.snoc (Fin.snoc L O : Fin (e + 1) → HermLine ι) Y) =
        ptsIntegral P (fun j z => Real.log (((Fin.snoc L Y : Fin (e + 1) → HermLine ι) j).h z))
          (fun _ => 1) := by
    intro Y hY
    have h1 := RootFieldNumerics.intersection_constant_metric_line II hII.1 K ι P (e + 1) (Fin.snoc L Y) (-1) hP
      (RootFieldNumerics.smooth_snoc hL hY)
    rw [neg_neg, one_mul, ← hO, RootFieldNumerics.snoc_snoc_swap,
      (hII.1 K ι).1 P (e + 2) _ _ hP (RootFieldNumerics.smooth_snoc (RootFieldNumerics.smooth_snoc hL hOs) hY)] at h1
    exact h1
  rw [← key _ (isSmoothHerm_tensor hA hB), ← key _ hA, ← key _ hB]
  exact (hII.1 K ι).2.1 P (e + 1) _ A B hP (RootFieldNumerics.smooth_snoc hL hOs) hA hB

end GlobalTheory.CompanionTheory.Ar.Top.EffLat


open GlobalTheory.CompanionTheory.Ar.Top.EffLat PositivityTheory.HtPt.Gf in
theorem GlobalTheory.CompanionTheory.Ar.Top.eff_lat : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : Ω), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (e + 2) → Birational y → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → s ≠ 0 → s ∈ chartLat y A.a 1 → (∀ W, ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (e + 1) → mCoordIdeal y ≤ W → 0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1)) → 0 ≤ ptsIntegral (mCoordIdeal y) (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) := by
  classical
  intro II hII hD K _ ι _ Ω _ y e L A s hP hbir hL hA hs0 hs hnef
  haveI hPp : (mCoordIdeal y).IsPrime := hP.2.1.1
  choose c0 hc0 using hP.2.1.2.2
  have hy0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0 := fun k => EffLat.y_ne_of_not_mem (hc0 k)
  obtain ⟨g, h, dg, dh, hg, hh, hd, hhne, e1⟩ := EffLat.exists_rep hbir hy0 A.a s
  have hgne : aeval y g ≠ 0 := by
    rw [e1]
    exact mul_ne_zero hs0 hhne
  have hgP := EffLat.not_mem_of_aeval_ne hgne
  have hhP := EffLat.not_mem_of_aeval_ne hhne
  have hHs : IsSmoothHerm (HermLine.sqMetric (ι := ι) dh) := isSmoothHerm_sqMetric dh
  have hGs := isSmoothHerm_tensor hA hHs
  have secH : IsSectionOn (mCoordIdeal y) (HermLine.sqMetric (ι := ι) dh) h :=
    ⟨dh, fun _ => rfl, hh, hhP⟩
  have secG : IsSectionOn (mCoordIdeal y) (A.tensor (HermLine.sqMetric (ι := ι) dh)) g := by
    refine ⟨dg, fun k => ?_, hg, hgP⟩
    have : (A.tensor (HermLine.sqMetric (ι := ι) dh)).a k = A.a k + dh k := rfl
    rw [this, hd k]
    ring
  have cutG := RootFieldNumerics.points_integral_section_snoc II hII hD K ι (mCoordIdeal y) e L _ g hP hL hGs secG
  have cutH := RootFieldNumerics.points_integral_section_snoc II hII hD K ι (mCoordIdeal y) e L _ h hP hL hHs secH
  have hadd := EffLat.deg_tensor II hII (mCoordIdeal y) e L A _ hP hL hA hHs
  have hfin : ∀ f : MRing ι, ({W | W ∈ divSupp (mCoordIdeal y) f ∧ IsHorizontal W}).Finite :=
    fun f => (divSupp_finite _ f).subset fun W hW => hW.1
  have hInn : ∀ W, W ∈ divSupp (mCoordIdeal y) g → IsHorizontal W →
      0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) := fun W hW hh' =>
    hnef W ((hD K ι _ (e + 1) _ g W hP secG hW).1 hh') (le_sup_left.trans hW.1.1.2)
  have hkey : ∀ W, W ∈ divSupp (mCoordIdeal y) h → IsHorizontal W →
      W ∈ divSupp (mCoordIdeal y) g ∧
        multAt (mCoordIdeal y ⊔ Ideal.span {h}) W ≤ multAt (mCoordIdeal y ⊔ Ideal.span {g}) W := by
    intro W hW _
    obtain ⟨hWmin, hWrel⟩ := hW
    have hrel' := hWrel
    choose c hcW using hWrel
    have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hWmin.1.2
    have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => EffLat.y_ne_of_not_mem fun h' => hcW k (hPW h')
    have hsc : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * A.a k)) ∈ chartRingZ y c := hs c hyc
    obtain ⟨u, r, hrel⟩ := EffLat.chart_rel hyc hsc hg hh hd e1
    haveI hWp : W.IsPrime := hWmin.1.1
    obtain ⟨hm, hle⟩ := EffLat.len_le_of_rel hgP (PositivityTheory.HtPt.Gf.mon_not_mem hWp hcW u) hrel hWmin
    refine ⟨⟨hm, hrel'⟩, ?_⟩
    unfold multAt
    rw [dite_eq_left hWp, dite_eq_left hWp]
    exact hle
  have cmp : (∑ᶠ (W) (_ : W ∈ divSupp (mCoordIdeal y) h ∧ IsHorizontal W),
        (multAt (mCoordIdeal y ⊔ Ideal.span {h}) W : ℝ) *
          ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1)) ≤
      ∑ᶠ (W) (_ : W ∈ divSupp (mCoordIdeal y) g ∧ IsHorizontal W),
        (multAt (mCoordIdeal y ⊔ Ideal.span {g}) W : ℝ) *
          ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
    change (∑ᶠ W ∈ {W | W ∈ divSupp (mCoordIdeal y) h ∧ IsHorizontal W}, _) ≤
      ∑ᶠ W ∈ {W | W ∈ divSupp (mCoordIdeal y) g ∧ IsHorizontal W}, _
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin h), finsum_mem_eq_finite_toFinset_sum _ (hfin g)]
    refine (Finset.sum_le_sum fun W hW => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (fun W hW => ?_) fun W hW _ => ?_)
    · rw [Set.Finite.mem_toFinset] at hW
      have h2 := hkey W hW.1 hW.2
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 h2.2) (hInn W h2.1 hW.2)
    · rw [Set.Finite.mem_toFinset] at hW ⊢
      exact ⟨(hkey W hW.1 hW.2).1, hW.2⟩
    · rw [Set.Finite.mem_toFinset] at hW
      exact mul_nonneg (Nat.cast_nonneg _) (hInn W hW.1 hW.2)
  rw [cutG, cutH] at hadd
  linarith
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionSectionRecursionStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_intersection_section_recursion : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : Ω), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (e + 2) → Birational y → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → s ≠ 0 → s ∈ chartLat y A.a 1 → (∀ W, ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (e + 1) → mCoordIdeal y ≤ W → 0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1)) → 0 ≤ ptsIntegral (mCoordIdeal y) (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.eff_lat | exact GlobalTheory.CompanionTheory.Ar.Top.eff_lat | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.eff_lat <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.IntersectionSectionLogIntegral
section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.ExistsSmooth
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics.EffN

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smooth_comb {J : Type} [Fintype J] {ℓ : J → HermLine ι} (hℓ : ∀ j, IsSmoothHerm (ℓ j))
    (n : J → ℤ) : IsSmoothHerm (combLine ℓ n) := by
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ∏ j, (ℓ j).h z ^ n j)
    {z : (k : K) × ι k → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  exact contDiffOn_prod (fun j _ => RootFieldNumerics.Ii.contDiffOn_zpow_h (ℓ j) (hℓ j) (n j))

theorem comb_a {J : Type} [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ) :
    (combLine ℓ n).a = ∑ j, n j • (ℓ j).a := rfl

theorem exists_smooth (b : K → ℤ) : ∃ B : HermLine ι, IsSmoothHerm B ∧ B.a = b := by
  classical
  let ℓ : K → HermLine ι := fun k =>
    { a := Pi.single k 1
      h := fun z => Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2)
      pos := by
        intro z hz
        obtain ⟨i, hi⟩ := hz k
        apply Real.sqrt_pos.mpr
        exact Finset.sum_pos' (fun _ _ => by positivity)
          ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
      smul := by
        intro c z hc
        have hprod : ∏ k', ‖c k'‖ ^ ((Pi.single k (1 : ℤ) : K → ℤ) k') = ‖c k‖ := by
          rw [Fintype.prod_eq_single k]
          · simp
          · intro k' hk'
            simp [Pi.single_apply, hk']
        rw [hprod]
        simp only [norm_mul, mul_pow]
        rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)] }
  refine ⟨combLine ℓ b, smooth_comb (fun k => ?_) b, ?_⟩
  · show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (k : K) × ι k → ℂ => Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2))
      {z : (k : K) × ι k → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
    apply ContDiffOn.sqrt
    · exact (ContDiff.sum (fun i _ => (contDiff_norm_sq ℂ).comp
        (contDiff_apply (𝕜 := ℝ) (F' := fun _ => ℂ) (⟨k, i⟩ : (k : K) × ι k)))).contDiffOn
    · intro z hz
      obtain ⟨i, hi⟩ := hz k
      exact (Finset.sum_pos' (fun _ _ => by positivity)
        ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩).ne'
  · rw [comb_a]
    funext k'
    simp [ℓ, Finset.sum_apply, Pi.single_apply]

theorem smooth_snoc {e : ℕ} {L : Fin e → HermLine ι} {X : HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    (hX : IsSmoothHerm X) (j : Fin (e + 1)) :
    IsSmoothHerm ((Fin.snoc L X : Fin (e + 1) → HermLine ι) j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa using hX
  · simpa using hL i

theorem last_lin (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (P : Ideal (MRing ι)) (e : ℕ)
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 2)) (L : Fin e → HermLine ι) (A B C : HermLine ι) (m : ℤ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (hC : IsSmoothHerm C)
    (hdeg : C.a = B.a + m • A.a) :
    ptsIntegral P (fun j z => Real.log (((Fin.snoc L C : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) =
      ptsIntegral P (fun j z => Real.log (((Fin.snoc L B : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) +
        m * ptsIntegral P (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z))
          (fun _ => 1) := by
  classical
  let ℓ : Fin e ⊕ Bool → HermLine ι := Sum.elim L (fun t => if t then A else B)
  have hℓ : ∀ j, IsSmoothHerm (ℓ j) := by
    rintro (i | _ | _) <;> simp [ℓ, hL, hA, hB]
  let n : Fin (e + 1) → Fin e ⊕ Bool → ℤ :=
    Fin.snoc (fun i => Pi.single (Sum.inl i) 1)
      (Pi.single (Sum.inr false) 1 + m • Pi.single (Sum.inr true) 1)
  obtain ⟨hexp, hperm⟩ := GlobalTheory.T.log_integral_multilinear II hII K ι P (e + 1) (Fin e ⊕ Bool) ℓ n hP hℓ
  have h1 := hperm (fun k => combLine ℓ (n k)) (Fin.snoc L C) 1 (fun k => smooth_comb hℓ _)
    (smooth_snoc hL hC) (by
      intro k
      simp only [Equiv.Perm.coe_one, id]
      rw [comb_a]
      refine Fin.lastCases ?_ (fun i => ?_) k
      · simp [n, ℓ, Fintype.sum_sum_type, Pi.single_apply, hdeg]
        abel
      · simp [n, ℓ, Fintype.sum_sum_type, Pi.single_apply])
  let w0 : Fin (e + 1) → Fin e ⊕ Bool := Fin.snoc (fun i => Sum.inl i) (Sum.inr false)
  let w1 : Fin (e + 1) → Fin e ⊕ Bool := Fin.snoc (fun i => Sum.inl i) (Sum.inr true)
  have hne : w0 ≠ w1 := by
    intro h
    have := congrFun h (Fin.last e)
    simp [w0, w1] at this
  have hzero : ∀ w : Fin (e + 1) → Fin e ⊕ Bool, w ≠ w0 ∧ w ≠ w1 →
      (∏ k, (n k (w k) : ℝ)) * ptsIntegral P (fun k z => Real.log ((ℓ (w k)).h z)) (fun _ => 1) = 0 := by
    rintro w ⟨hw0, hw1⟩
    apply mul_eq_zero_of_left
    by_contra hprod
    have hf : ∀ k, (n k (w k) : ℝ) ≠ 0 := fun k =>
      Finset.prod_ne_zero_iff.mp hprod k (Finset.mem_univ _)
    have hcs : ∀ i : Fin e, w (Fin.castSucc i) = Sum.inl i := by
      intro i
      have := hf (Fin.castSucc i)
      simp [n, Pi.single_apply] at this
      exact this
    have hl := hf (Fin.last e)
    rcases hw : w (Fin.last e) with i | (_ | _)
    · rw [hw] at hl
      simp [n, Pi.single_apply] at hl
    · exact hw0 (funext fun k => by
        refine Fin.lastCases ?_ (fun i => ?_) k
        · simp [w0, hw]
        · simp [w0, hcs i])
    · exact hw1 (funext fun k => by
        refine Fin.lastCases ?_ (fun i => ?_) k
        · simp [w1, hw]
        · simp [w1, hcs i])
  have e0 : ∀ k, ℓ (w0 k) = (Fin.snoc L B : Fin (e + 1) → HermLine ι) k := by
    intro k
    refine Fin.lastCases ?_ (fun i => ?_) k <;> simp [ℓ, w0]
  have e1 : ∀ k, ℓ (w1 k) = (Fin.snoc L A : Fin (e + 1) → HermLine ι) k := by
    intro k
    refine Fin.lastCases ?_ (fun i => ?_) k <;> simp [ℓ, w1]
  have p0 : ∏ k, (n k (w0 k) : ℝ) = 1 := by
    rw [Fin.prod_univ_castSucc]
    simp [n, w0]
  have p1 : ∏ k, (n k (w1 k) : ℝ) = m := by
    rw [Fin.prod_univ_castSucc]
    simp [n, w1]
  rw [h1, hexp, Fintype.sum_eq_add w0 w1 hne hzero, p0, p1]
  simp only [e0, e1, one_mul]

end RootFieldNumerics.EffN
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem RootFieldNumerics.intersection_section_log_integral : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : Ω), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (e + 2) → Birational y → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → s ≠ 0 → s ∈ chartLatNm y A.a 1 → (∀ j W', ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W' 2 → mCoordIdeal y ≤ W' → 0 ≤ geomDeg W' (L j) 1) → 0 ≤ ptsIntegral (mCoordIdeal y) (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) := by
  intro hK hEU hDiv II hII K _ ι _ Ω _ y e L A s hV hB hL hA hs hsA hgeo
  have hW : ∀ W : Ideal (MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (e + 1) → mCoordIdeal y ≤ W →
      0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
    intro W hW hle
    exact GlobalTheory.T.ptsIntegral_log_nonneg hK hEU hDiv II hII K ι W e L hW hL
      (fun j W' hW' hle' => hgeo j W' hW' (le_trans hle hle'))
  obtain ⟨b, c, hc0, hc⟩ := GlobalTheory.T.chart_lattice_power_section K ι Ω y (e + 2) A.a s hV hB hsA
  obtain ⟨B, hBs, hBa⟩ := RootFieldNumerics.EffN.exists_smooth (ι := ι) b
  have key : ∀ n : ℕ, 0 ≤ ptsIntegral (mCoordIdeal y)
      (fun j z => Real.log (((Fin.snoc L B : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1)
      + (n : ℝ) * ptsIntegral (mCoordIdeal y)
      (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) := by
    intro n
    obtain ⟨C, hCs, hCa⟩ := RootFieldNumerics.EffN.exists_smooth (ι := ι) (b + n • A.a)
    have hCa' : C.a = B.a + (n : ℤ) • A.a := by rw [hCa, hBa, natCast_zsmul]
    have hmem : c * s ^ n ∈ chartLat y C.a 1 := by rw [hCa]; exact hc n
    have h0 := GlobalTheory.T.arith_intersection_section_recursion II hII hDiv K ι Ω y e L C (c * s ^ n) hV hB hL hCs
      (mul_ne_zero hc0 (pow_ne_zero _ hs)) hmem hW
    rw [RootFieldNumerics.EffN.last_lin II hII (mCoordIdeal y) e hV L A B C (n : ℤ) hL hA hBs hCs hCa'] at h0
    simpa using h0
  set PB := ptsIntegral (mCoordIdeal y)
    (fun j z => Real.log (((Fin.snoc L B : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1)
  set PA := ptsIntegral (mCoordIdeal y)
    (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1)
  by_contra hneg
  push_neg at hneg
  have hpos : 0 < -PA := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (PB / -PA)
  have h1 := (div_lt_iff₀ hpos).mp hn
  have h2 := key n
  have h3 : (n : ℝ) * -PA = -((n : ℝ) * PA) := by ring
  linarith
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionSectionBound
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem effective_mul_nef_nonneg : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : Ω), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (e + 2) → Birational y → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → s ≠ 0 → s ∈ chartLatNm y A.a 1 → (∀ j W', ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W' 2 → mCoordIdeal y ≤ W' → 0 ≤ geomDeg W' (L j) 1) → 0 ≤ ptsIntegral (mCoordIdeal y) (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) :=
  @RootFieldNumerics.intersection_section_log_integral

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionSectionBoundStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_intersection_section_bound : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : Ω), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (e + 2) → Birational y → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → s ≠ 0 → s ∈ chartLatNm y A.a 1 → (∀ j W', ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W' 2 → mCoordIdeal y ≤ W' → 0 ≤ geomDeg W' (L j) 1) → 0 ≤ ptsIntegral (mCoordIdeal y) (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.effective_mul_nef_nonneg | exact GlobalTheory.CompanionTheory.Ar.Top.effective_mul_nef_nonneg | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.effective_mul_nef_nonneg <;> assumption)
end
