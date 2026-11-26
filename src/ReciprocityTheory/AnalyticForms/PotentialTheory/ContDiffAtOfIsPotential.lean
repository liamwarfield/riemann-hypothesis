module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.MaDensCompEqZeroOfRankLt
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt

@[expose] public section

section -- merged from ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

def SmoothOnAlgStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U V : Set X) (f g : X → ℝ)
    (c : ℝ), A.SmoothOn U f → A.SmoothOn V g → V ⊆ U →
      A.SmoothOn V (fun x => f x + g x) ∧ A.SmoothOn U (fun x => c * f x)

theorem smoothOnAlg : SmoothOnAlgStatement := by
  intro e X _ A U V f g c hf hg hVU
  refine ⟨fun j => ?_, fun j => ?_⟩
  · exact ((hf j).mono (by exact fun y hy => ⟨hy.1, hVU hy.2⟩)).add (hg j)
  · exact contDiffOn_const.mul (hf j)

section SlopeTestRemainingChoices

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem add_U (P Q : LocPot X) (x : X) : (P + Q).U x = P.U x ∩ Q.U x := rfl

theorem add_φ (P Q : LocPot X) (x : X) : (P + Q).φ x = fun y => P.φ x y + Q.φ x y := rfl

theorem contDiffAt_of_isPotential (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P)
    (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :
    ContDiffAt ℝ ∞ (P.φ x ∘ (A.chart j).symm) y :=
  (hP.1 x j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds hy)

theorem holoOn_add (A : FinHolAtlas e X) {W₁ W₂ : Set X} {G₁ G₂ : X → ℂ}
    (h₁ : A.HoloOn W₁ G₁) (h₂ : A.HoloOn W₂ G₂) :
    A.HoloOn (W₁ ∩ W₂) (fun z => G₁ z + G₂ z) := fun j w hw =>
  ((h₁ j w ⟨hw.1, hw.2.1⟩).add (h₂ j w ⟨hw.1, hw.2.2⟩))

theorem holoOn_mul (A : FinHolAtlas e X) {W : Set X} {G : X → ℂ} (h : A.HoloOn W G) (c : ℂ) :
    A.HoloOn W (fun z => c * G z) := fun j w hw => analyticAt_const.mul (h j w hw)

theorem isPotential_mul (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P) (c : ℝ)
    (Q : LocPot X) (hU : Q.U = P.U) (hφ : ∀ x y, Q.φ x y = c * P.φ x y) : IsPotential A Q := by
  have hQφ : ∀ x, Q.φ x = fun y => c * P.φ x y := fun x => funext (hφ x)
  refine ⟨fun x => ?_, fun x x' y hy => ?_⟩
  · rw [hQφ x, hU]
    exact fun j => contDiffOn_const.mul (hP.1 x j)
  · rw [hU] at hy
    obtain ⟨W, hW, hyW, G, hG, hGe⟩ := hP.2 x x' y hy
    refine ⟨W, hW, hyW, fun z => (c : ℂ) * G z, holoOn_mul A hG c, fun z hz => ?_⟩
    rw [hU] at hz
    rw [hφ, hφ, ← mul_sub, hGe z hz, Complex.re_ofReal_mul]

end SlopeTestRemainingChoices

theorem isPotentialAdd : IsPotentialAddStatement := by
  intro e X _ A P Q hP hQ
  refine ⟨fun x => ?_, fun x x' y hy => ?_⟩
  · rw [add_U, add_φ]
    exact fun j => ((hP.1 x j).mono (by exact fun y hy => ⟨hy.1, hy.2.1⟩)).add
      ((hQ.1 x j).mono fun y hy => ⟨hy.1, hy.2.2⟩)
  · rw [add_U, add_U] at hy
    obtain ⟨⟨hPx, hQx⟩, hPx', hQx'⟩ := hy
    obtain ⟨W₁, hW₁, hyW₁, G₁, hG₁, hGe₁⟩ := hP.2 x x' y ⟨hPx, hPx'⟩
    obtain ⟨W₂, hW₂, hyW₂, G₂, hG₂, hGe₂⟩ := hQ.2 x x' y ⟨hQx, hQx'⟩
    refine ⟨W₁ ∩ W₂, hW₁.inter hW₂, ⟨hyW₁, hyW₂⟩, fun z => G₁ z + G₂ z, holoOn_add A hG₁ hG₂,
      fun z hz => ?_⟩
    rw [add_U, add_U] at hz
    obtain ⟨⟨⟨hz₁, hz₂⟩, hzP, hzQ⟩, hzP', hzQ'⟩ := hz
    have e₁ := hGe₁ z ⟨⟨hz₁, hzP⟩, hzP'⟩
    have e₂ := hGe₂ z ⟨⟨hz₂, hzQ⟩, hzQ'⟩
    simp only [add_φ, Complex.add_re]
    linarith

theorem isPotentialZsmul : IsPotentialZsmulStatement := by
  intro e X _ A m P hP
  exact isPotential_mul A P hP (m : ℝ) (P.zsmul m) rfl (fun _ _ => rfl)

theorem isPotentialRsmul : IsPotentialRsmulStatement := by
  intro e X _ A c P hP
  exact isPotential_mul A P hP c (P.rsmul c) rfl (fun _ _ => rfl)

private theorem eventually_chart_symm_chart_comp_eq {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (h : Y → X) (hh : Continuous h)
    (j : Fin B.n) (k : Fin A.n) {w : Fin e' → ℂ} (hw : w ∈ (B.chart j).target)
    (hk : h ((B.chart j).symm w) ∈ (A.chart k).source) :
    ∀ᶠ w' in 𝓝 w, (A.chart k).symm (A.chart k (h ((B.chart j).symm w'))) = h ((B.chart j).symm w') := by
  have hO : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source)) :=
    (B.chart j).isOpen_inter_preimage_symm ((A.chart k).open_source.preimage hh)
  filter_upwards [hO.mem_nhds ⟨hw, hk⟩] with w' hw'
  exact (A.chart k).left_inv hw'.2

theorem isPotentialPullback : IsPotentialPullbackStatement := by
  intro e e' X Y _ _ A B h hh P hP
  refine ⟨fun y j w hw => ?_, fun y y' z hz => ?_⟩
  · obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm w))
    have hin : A.chart k (h ((B.chart j).symm w)) ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U (h y) := by
      refine ⟨(A.chart k).map_source hk, ?_⟩
      show (A.chart k).symm (A.chart k (h ((B.chart j).symm w))) ∈ P.U (h y)
      rw [(A.chart k).left_inv hk]
      exact hw.2
    have hf := contDiffAt_of_isPotential A P hP (h y) k hin
    have hg : ContDiffAt ℝ ∞ (A.chart k ∘ h ∘ (B.chart j).symm) w :=
      (AnalyticAt.contDiffAt (n := ∞) (hh.2 j k w ⟨hw.1, hk⟩)).restrict_scalars ℝ
    refine (ContDiffAt.congr_of_eventuallyEq (hf.comp w hg) ?_).contDiffWithinAt
    filter_upwards [eventually_chart_symm_chart_comp_eq A B h hh.1 j k hw.1 hk] with w' hw'
    show P.φ (h y) (h ((B.chart j).symm w')) =
      P.φ (h y) ((A.chart k).symm (A.chart k (h ((B.chart j).symm w'))))
    rw [hw']
  · have hz' : h z ∈ P.U (h y) ∩ P.U (h y') := hz
    obtain ⟨W, hW, hzW, G, hG, hGe⟩ := hP.2 (h y) (h y') (h z) hz'
    refine ⟨h ⁻¹' W, hW.preimage hh.1, hzW, G ∘ h, fun j w hw => ?_, fun z' hz' => hGe (h z') hz'⟩
    obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm w))
    have hin : A.chart k (h ((B.chart j).symm w)) ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' W := by
      refine ⟨(A.chart k).map_source hk, ?_⟩
      show (A.chart k).symm (A.chart k (h ((B.chart j).symm w))) ∈ W
      rw [(A.chart k).left_inv hk]
      exact hw.2
    have hc : AnalyticAt ℂ ((G ∘ (A.chart k).symm) ∘ (A.chart k ∘ h ∘ (B.chart j).symm)) w :=
      AnalyticAt.comp (hG k _ hin) (hh.2 j k w ⟨hw.1, hk⟩)
    refine hc.congr ?_
    filter_upwards [eventually_chart_symm_chart_comp_eq A B h hh.1 j k hw.1 hk] with w' hw'
    show G ((A.chart k).symm (A.chart k (h ((B.chart j).symm w')))) = G (h ((B.chart j).symm w'))
    rw [hw']

private theorem eventually_contDiffAt_potential_chart_symm {e : ℕ} {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P) (x : X) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :
    ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ (P.φ x ∘ (A.chart j).symm) z := by
  filter_upwards [((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds hy] with z hz
  exact contDiffAt_of_isPotential A P hP x j hz

private theorem differentiableAt_of_contDiffAt_infty {n : ℕ} {F : (Fin n → ℂ) → ℝ} {y : Fin n → ℂ}
    (hF : ContDiffAt ℝ ∞ F y) : DifferentiableAt ℝ F y :=
  hF.differentiableAt (by simp)

private theorem differentiableAt_fderiv_of_contDiffAt_infty {n : ℕ} {F : (Fin n → ℂ) → ℝ} {y : Fin n → ℂ}
    (hF : ContDiffAt ℝ ∞ F y) : DifferentiableAt ℝ (fderiv ℝ F) y :=
  (hF.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt (by simp)

private theorem fderiv_fderiv_add' {n : ℕ} {F G : (Fin n → ℂ) → ℝ} {y : Fin n → ℂ}
    (hF : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ F z) (hG : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ G z) :
    fderiv ℝ (fderiv ℝ (fun z => F z + G z)) y = fderiv ℝ (fderiv ℝ F) y + fderiv ℝ (fderiv ℝ G) y := by
  have hev : fderiv ℝ (fun z => F z + G z) =ᶠ[𝓝 y] fun z => fderiv ℝ F z + fderiv ℝ G z := by
    filter_upwards [hF, hG] with z hFz hGz
    exact fderiv_add (differentiableAt_of_contDiffAt_infty hFz) (differentiableAt_of_contDiffAt_infty hGz)
  rw [hev.fderiv_eq]
  exact fderiv_add (differentiableAt_fderiv_of_contDiffAt_infty hF.self_of_nhds)
    (differentiableAt_fderiv_of_contDiffAt_infty hG.self_of_nhds)

theorem isPshAdd : IsPshAddStatement := by
  intro e X _ A P Q hP hQ hpP hpQ x j y hy w
  have hy' : y ∈ (A.chart j).target ∧ (A.chart j).symm y ∈ P.U x ∩ Q.U x := hy
  have hyP : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x := ⟨hy'.1, hy'.2.1⟩
  have hyQ : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U x := ⟨hy'.1, hy'.2.2⟩
  have hp := hpP x j y hyP w
  have hq := hpQ x j y hyQ w
  have hrw : (P + Q).φ x ∘ (A.chart j).symm =
      fun z => (P.φ x ∘ (A.chart j).symm) z + (Q.φ x ∘ (A.chart j).symm) z := rfl
  rw [hrw]
  unfold ReciprocityTheory.AnForm.levi at hp hq ⊢
  rw [fderiv_fderiv_add' (eventually_contDiffAt_potential_chart_symm A P hP x j hyP)
    (eventually_contDiffAt_potential_chart_symm A Q hQ x j hyQ)]
  simp only [ContinuousLinearMap.add_apply]
  linarith

private theorem fderiv_fderiv_const_mul {n : ℕ} {F : (Fin n → ℂ) → ℝ} {y : Fin n → ℂ}
    (hF : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ F z) (c : ℝ) :
    fderiv ℝ (fderiv ℝ (fun z => c * F z)) y = c • fderiv ℝ (fderiv ℝ F) y := by
  have hev : fderiv ℝ (fun z => c * F z) =ᶠ[𝓝 y] fun z => c • fderiv ℝ F z := by
    filter_upwards [hF] with z hFz
    exact fderiv_const_mul (differentiableAt_of_contDiffAt_infty hFz) c
  rw [hev.fderiv_eq]
  exact fderiv_const_smul (differentiableAt_fderiv_of_contDiffAt_infty hF.self_of_nhds) c

theorem isPshRsmul : IsPshRsmulStatement := by
  intro e X _ A c P hc hP hpP x j y hy w
  have hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x := hy
  have hp := hpP x j y hy' w
  have hrw : (P.rsmul c).φ x ∘ (A.chart j).symm = fun z => c * (P.φ x ∘ (A.chart j).symm) z := rfl
  rw [hrw]
  unfold ReciprocityTheory.AnForm.levi at hp ⊢
  rw [fderiv_fderiv_const_mul (eventually_contDiffAt_potential_chart_symm A P hP x j hy') c]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [show ∀ a b : ℝ, (c * a + c * b) / 4 = c * ((a + b) / 4) from fun a b => by ring]
  exact mul_nonneg hc hp

end

end ReciprocityTheory.AnForm.M
end

section -- merged from ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

theorem pa_holoSmooth {e e' : ℕ} (F : (Fin e → ℂ) → (Fin e' → ℂ)) (U : Set (Fin e → ℂ))
    (hF : AnalyticOnNhd ℂ F U) : ContDiffOn ℝ ∞ F U :=
  fun x hx => ((hF x hx).contDiffAt.restrict_scalars ℝ).contDiffWithinAt

def pa_aff {e : ℕ} (a : ℂ) (ha : a ≠ 0) (b : Fin e → ℂ) : (Fin e → ℂ) ≃ₜ (Fin e → ℂ) where
  toFun y := a • (y - b)
  invFun z := a⁻¹ • z + b
  left_inv y := by simp [smul_smul, inv_mul_cancel₀ ha]
  right_inv z := by simp [smul_smul, mul_inv_cancel₀ ha]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem pa_aff_analytic {e : ℕ} (a : ℂ) (b : Fin e → ℂ) (y : Fin e → ℂ) :
    AnalyticAt ℂ (fun y : Fin e → ℂ => a • (y - b)) y :=
  by fun_prop

theorem pa_compat_restr {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (s : Set X)
    (hs : IsOpen s) : IsCompatChart A (ψ.restrOpen s hs) := by
  intro j
  obtain ⟨h1, h2⟩ := hψ j
  refine ⟨h1.mono ?_, h2.mono ?_⟩
  · rintro x ⟨hx1, hx2⟩
    exact ⟨hx1, hx2.1⟩
  · rintro x ⟨hx1, hx2⟩
    exact ⟨hx1.1, hx2⟩

theorem pa_compat_aff {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (a : ℂ) (ha : a ≠ 0)
    (b : Fin e → ℂ) : IsCompatChart A (ψ.transHomeomorph (pa_aff a ha b)) := by
  intro j
  obtain ⟨h1, h2⟩ := hψ j
  refine ⟨fun z hz => (pa_aff_analytic a b _).comp (h1 z hz), fun z hz => ?_⟩
  have hinv : AnalyticAt ℂ (fun z : Fin e → ℂ => a⁻¹ • z + b) z :=
    by fun_prop
  exact AnalyticAt.comp (f := fun w : Fin e → ℂ => a⁻¹ • w + b) (h2 (a⁻¹ • z + b) hz) hinv

theorem existsPartition : ExistsPartitionStatement := by
  intro e X _ _ _ A
  obtain ⟨χ, h0, h1, h2, h3⟩ := ReciprocityTheory.AnForm.exists_chart_partition A.chart A.cover
    (fun i j => pa_holoSmooth _ _ (A.holo i j))
  exact ⟨⟨χ, fun j k => (h3 j k).mono Set.inter_subset_left, h0, h2, h1⟩⟩

def AtlasOfCompatStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ}
    (ψ : Fin m → OpenPartialHomeomorph X (Fin e → ℂ)), (∀ i, IsCompatChart A (ψ i)) →
    (∀ x, ∃ i, x ∈ (ψ i).source) →
    ∃ B : FinHolAtlas e X, A.Compatible B ∧ (∀ i, ∃ j, B.chart j = ψ i) ∧ ∀ j, ∃ i, B.chart j = ψ i

theorem atlasOfCompat : AtlasOfCompatStatement := by
  intro e X _ A m ψ hψ hcov
  refine ⟨⟨m, ψ, hcov, ?_⟩, ⟨fun j k => (hψ k j).1, fun j k => (hψ j k).2⟩, fun i => ⟨i, rfl⟩,
    fun j => ⟨j, rfl⟩⟩
  intro j k z hz
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨l, hx⟩ := A.cover ((ψ j).symm z)
  have hev : ∀ᶠ w in nhds z, (ψ j).symm w ∈ (A.chart l).source :=
    ((ψ j).continuousAt_symm hz1).preimage_mem_nhds ((A.chart l).open_source.mem_nhds hx)
  have ha1 := (hψ k l).1 (A.chart l ((ψ j).symm z))
    ⟨(A.chart l).map_source hx, by rw [Set.mem_preimage, (A.chart l).left_inv hx]; exact hz2⟩
  have ha2 := (hψ j l).2 z ⟨hz1, hx⟩
  exact (AnalyticAt.comp (f := ⇑(A.chart l) ∘ ⇑(ψ j).symm) ha1 ha2).congr (hev.mono fun w hw => by
    simp only [Function.comp, (A.chart l).left_inv hw])

end

end ReciprocityTheory.AnForm.M
end

section -- merged from ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

theorem analyticSubset_chart_local {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {S : Set X} (hS : A.IsAnalyticSubset S) (hint : interior S = ∅) (j : Fin A.n)
    {z : Fin e → ℂ} (hz : z ∈ (A.chart j) '' (S ∩ (A.chart j).source)) :
    ∃ W : Set (Fin e → ℂ), IsOpen W ∧ z ∈ W ∧ IsPreconnected W ∧
      ∃ f : (Fin e → ℂ) → ℂ, AnalyticOnNhd ℂ f W ∧ (∃ w ∈ W, f w ≠ 0) ∧
        ∀ w ∈ (A.chart j) '' (S ∩ (A.chart j).source) ∩ W, f w = 0 := by
  obtain ⟨x, ⟨-, hxs⟩, rfl⟩ := hz
  obtain ⟨W₀, hW₀, hxW₀, r, f, hf, hSW⟩ := hS x
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W₀) :=
    (A.chart j).isOpen_inter_preimage_symm hW₀
  have hmem : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W₀ := by
    refine ⟨(A.chart j).map_source hxs, ?_⟩
    show (A.chart j).symm ((A.chart j) x) ∈ W₀
    rw [(A.chart j).left_inv hxs]
    exact hxW₀
  obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.mp hopen _ hmem

  have hex : ∃ i, ∃ w ∈ Metric.ball ((A.chart j) x) ε, f i ((A.chart j).symm w) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hsub : (A.chart j).symm '' Metric.ball ((A.chart j) x) ε ⊆ S := by
      rintro _ ⟨w, hw, rfl⟩
      have hw' := hε hw
      have hin : (A.chart j).symm w ∈ S ∩ W₀ := by
        rw [hSW]
        exact ⟨hw'.2, fun i => hcon i w hw⟩
      exact hin.1
    have hop : IsOpen ((A.chart j).symm '' Metric.ball ((A.chart j) x) ε) :=
      (A.chart j).symm.isOpen_image_of_subset_source Metric.isOpen_ball
        (fun w hw => (hε hw).1)
    have hint' : (A.chart j).symm ((A.chart j) x) ∈ interior S :=
      interior_maximal hsub hop ⟨_, Metric.mem_ball_self hε0, rfl⟩
    rw [hint] at hint'
    exact hint'
  obtain ⟨i, w₀, hw₀, hfw₀⟩ := hex
  refine ⟨Metric.ball ((A.chart j) x) ε, Metric.isOpen_ball, Metric.mem_ball_self hε0,
    (convex_ball _ _).isPreconnected, f i ∘ (A.chart j).symm, ?_, ⟨w₀, hw₀, hfw₀⟩, ?_⟩
  · exact (hf i j).mono hε
  · rintro w ⟨⟨y, ⟨hyS, hys⟩, rfl⟩, hw⟩
    have hw' := hε hw
    have hin : (A.chart j).symm ((A.chart j) y) ∈ S ∩ W₀ :=
      ⟨by rw [(A.chart j).left_inv hys]; exact hyS, hw'.2⟩
    rw [hSW] at hin
    exact hin.2 i

theorem analyticNull : AnalyticNullStatement := by
  intro e X _ A S hS hint j
  exact ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set _
    (fun z hz => analyticSubset_chart_local A hS hint j hz)

theorem integralWith_congr_null {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) {S : Set X} (hS : A.IsAnalyticSubset S)
    (hint : interior S = ∅) {g g' : X → ℝ} (hg : ∀ x ∉ S, g x = g' x) :
    integralWith A P Φ g = integralWith A P Φ g' := by
  first
  | unfold integralWith
  | simp only [integralWith]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have hnull : volume ((A.chart j) '' (S ∩ (A.chart j).source)) = 0 :=
    analyticNull A S hS hint j
  have hsub : {y | ¬(P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y =
      P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y)} ∩
      (A.chart j).target ⊆ (A.chart j) '' (S ∩ (A.chart j).source) := by
    intro y hy
    have hne : ¬(P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y =
        P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y) := hy.1
    have hyt : y ∈ (A.chart j).target := hy.2
    refine ⟨(A.chart j).symm y, ⟨?_, (A.chart j).map_target hyt⟩, (A.chart j).right_inv hyt⟩
    by_contra hnS
    apply hne
    rw [hg _ hnS]
  have hae : ∀ᵐ y ∂(volume.restrict (A.chart j).target),
      P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y =
      P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y := by
    rw [MeasureTheory.ae_iff, MeasureTheory.Measure.restrict_apply' hT]
    exact MeasureTheory.measure_mono_null hsub hnull
  exact MeasureTheory.integral_congr_ae hae

theorem mIntCongrNull : MIntCongrNullStatement := by
  unfold MIntCongrNullStatement
  intro e X _ A Φ S hS hint g g' hg
  unfold mInt
  split_ifs with h
  · exact integralWith_congr_null A h.some Φ hS hint hg
  · rfl

end

end ReciprocityTheory.AnForm.M
end

section -- merged from ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
namespace ReciprocityTheory.AnForm.M

open Filter Topology
open scoped ContDiff ComplexOrder

noncomputable section

section SlopeTestRemainingChoices

variable {D : ℕ}

theorem hessC_const_mul' (c : ℝ) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    hessC (fun w => c * φ w) z = (c : ℂ) • hessC φ z := by
  have h1 : fderiv ℝ (fun w => c * φ w) = c • fderiv ℝ φ := by
    show fderiv ℝ (c • φ) = _
    exact fderiv_const_smul_field c
  have h2 : fderiv ℝ (fderiv ℝ (fun w => c * φ w)) = c • fderiv ℝ (fderiv ℝ φ) := by
    rw [h1]; exact fderiv_const_smul_field c
  ext i j
  simp only [hessC, h2, Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Matrix.smul_apply]
  push_cast
  ring

theorem hessC_add' (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hψ : ContDiffAt ℝ 2 ψ z) :
    hessC (fun w => φ w + ψ w) z = hessC φ z + hessC ψ z := by
  have e1 : fderiv ℝ (fun w => φ w + ψ w) =ᶠ[𝓝 z] fun w => fderiv ℝ φ w + fderiv ℝ ψ w := by
    filter_upwards [hφ.eventually (by simp), hψ.eventually (by simp)] with w h1 h2
    exact fderiv_add (h1.differentiableAt (by norm_num)) (h2.differentiableAt (by norm_num))
  have d1 : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have d2 : DifferentiableAt ℝ (fderiv ℝ ψ) z :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have e2 : fderiv ℝ (fderiv ℝ (fun w => φ w + ψ w)) z =
      fderiv ℝ (fderiv ℝ φ) z + fderiv ℝ (fderiv ℝ ψ) z := by
    rw [e1.fderiv_eq]; exact fderiv_add d1 d2
  ext i j
  simp only [hessC, e2, ContinuousLinearMap.add_apply, Matrix.add_apply]
  push_cast
  ring

theorem mdisc_cons_add {e : ℕ} (B C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
    (F : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    mdisc (Fin.cons (B + C) F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) =
      mdisc (Fin.cons B F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) +
        mdisc (Fin.cons C F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) := by
  have := ReciprocityTheory.AnForm.A.mdisc_update_add
    (Fin.cons B F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) 0 B C
  simpa only [Fin.update_cons_zero] using this

theorem mdisc_cons_smul {e : ℕ} (c : ℂ) (B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
    (F : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    mdisc (Fin.cons (c • B) F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) =
      c * mdisc (Fin.cons B F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) := by
  have := ReciprocityTheory.AnForm.A.mdisc_update_smul
    (Fin.cons B F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) 0 c B
  simpa only [Fin.update_cons_zero] using this

theorem hessC_isHermitian' (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z) :
    (hessC φ z).IsHermitian := by
  have hs := hφ.isSymmSndFDerivAt (by simp)
  ext i j
  simp only [Matrix.conjTranspose_apply, hessC]
  rw [hs (Pi.single j 1) (Pi.single i 1), hs (Complex.I • Pi.single j 1) (Complex.I • Pi.single i 1),
    hs (Pi.single j 1) (Complex.I • Pi.single i 1), hs (Complex.I • Pi.single j 1) (Pi.single i 1)]
  apply Complex.ext <;> simp

theorem leviC_add_right (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (a b b' : Fin D → ℂ) :
    leviC H a (b + b') = leviC H a b + leviC H a b' := by
  simp only [leviC, smul_add, map_add (f := _)]
  push_cast
  ring

theorem leviC_smul_right (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (c : ℂ) (a b : Fin D → ℂ) :
    leviC H a (c • b) = starRingEnd ℂ c * leviC H a b := by
  have h1 : c • b = c.re • b + c.im • (Complex.I • b) := by
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  have h2 : Complex.I • (c • b) = c.re • (Complex.I • b) - c.im • b := by
    ext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    linear_combination ((c.im : ℂ) * b k) * Complex.I_sq
  unfold leviC
  rw [h2, h1]
  simp only [map_add (f := _), map_sub, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring

theorem sum_leviC_right (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (a x : Fin D → ℂ) :
    ∑ j, leviC H a (Pi.single j 1) * x j = leviC H a (star x) := by
  let ℓ : (Fin D → ℂ) →+ ℂ :=
    { toFun := leviC H a
      map_zero' := by simp [leviC]
      map_add' := leviC_add_right H a }
  have hx : star x = ∑ j, star (x j) • (Pi.single j 1 : Fin D → ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single (star x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  have := map_sum ℓ (fun j => star (x j) • (Pi.single j 1 : Fin D → ℂ)) Finset.univ
  rw [← hx] at this
  change leviC H a (star x) = ∑ j, leviC H a (star (x j) • Pi.single j 1) at this
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [leviC_smul_right]
  simp [mul_comm]

theorem hessC_posSemidef (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (h : ∀ w, 0 ≤ levi φ z w) : (hessC φ z).PosSemidef := by
  have hs := hφ.isSymmSndFDerivAt (by simp)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hessC_isHermitian' φ z hφ) fun x => ?_
  have hq : star x ⬝ᵥ ((hessC φ z).mulVec x) =
      leviC (fderiv ℝ (fderiv ℝ φ) z) (star x) (star x) := by
    rw [Matrix.dotProduct_mulVec]
    simp only [Matrix.vecMul, dotProduct, hessC_eq_leviC, sum_mul_leviC]
    exact sum_leviC_right _ _ _
  rw [hq, Complex.nonneg_iff]
  constructor
  · have := h (star x)
    simp only [levi] at this
    simpa [leviC] using this
  · simp [leviC, hs (star x) (Complex.I • star x)]

end SlopeTestRemainingChoices

end

end ReciprocityTheory.AnForm.M
end

section -- merged from ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
namespace ReciprocityTheory.AnForm.M.PLAux

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem smooth_continuous {A : FinHolAtlas e X} {f : X → ℝ} (hf : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨j, hj⟩ := A.cover p
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j p) := by
    refine (hf j).continuousOn.continuousAt ?_
    simp only [Set.preimage_univ, Set.inter_univ]
    exact (A.chart j).open_target.mem_nhds ((A.chart j).map_source hj)
  refine (h1.comp ((A.chart j).continuousAt hj)).congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with q hq
  simp [(A.chart j).left_inv hq]

theorem smoothOn_mul {A : FinHolAtlas e X} {U : Set X} {f g : X → ℝ} (hf : A.SmoothOn U f)
    (hg : A.SmoothOn U g) : A.SmoothOn U (fun x => f x * g x) := fun j => (hf j).mul (hg j)

theorem mInt_congr {A : FinHolAtlas e X} {Φ Ψ : Fin e → LocPot X} {g g' : X → ℝ}
    (h : ∀ j, ∀ y ∈ (A.chart j).target,
      g ((A.chart j).symm y) * locDens A Φ j y = g' ((A.chart j).symm y) * locDens A Ψ j y) :
    mInt A Φ g = mInt A Ψ g' := by
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    refine setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    simp only [mul_assoc]
    rw [h j y hy]
  · rfl

theorem mInt_zero_fun (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) {g : X → ℝ}
    (hg : ∀ x, g x = 0) : mInt A Φ g = 0 := by
  unfold mInt
  split_ifs
  · simp [integralWith, hg]
  · rfl

theorem hessC_congr_eventuallyEq {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : f =ᶠ[𝓝 y] g) : hessC f y = hessC g y := by
  have h2 : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y := h.fderiv.fderiv_eq
  ext i j
  simp [hessC, h2]

theorem maDens_congr_germ {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ i, φ i =ᶠ[𝓝 y] ψ i) : maDens φ y = maDens ψ y := by
  unfold maDens
  congr 3
  funext k
  exact hessC_congr_eventuallyEq (h k)

theorem hessC_eq_zero_of_eventuallyEq_zero {D : ℕ} {f : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : f =ᶠ[𝓝 y] fun _ => 0) : hessC f y = 0 := by
  have h1 : fderiv ℝ f =ᶠ[𝓝 y] fderiv ℝ (fun _ : Fin D → ℂ => (0 : ℝ)) := h.fderiv
  have h2 : fderiv ℝ (fderiv ℝ f) y = 0 := by
    rw [h1.fderiv_eq]
    simp
  ext i j
  simp [hessC, h2]

theorem maDens_cons_eq_zero {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℝ}
    {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} {y : Fin (n + 1) → ℂ} (h : f =ᶠ[𝓝 y] fun _ => 0) :
    maDens (Fin.cons f φ) y = 0 := by
  have hc : (fun k => hessC ((Fin.cons f φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) y) =
      Fin.cons (hessC f y) (fun k => hessC (φ k) y) := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k <;> simp
  unfold maDens
  rw [hc, ReciprocityTheory.AnForm.A.mdisc_cons_eq_sum, hessC_eq_zero_of_eventuallyEq_zero h]
  simp

theorem locDens_cons_ofFun_eq_zero {A : FinHolAtlas (e + 1) X} (v : X → ℝ)
    (Φ : Fin e → LocPot X) (j : Fin A.n) {y : Fin (e + 1) → ℂ} (hy : y ∈ (A.chart j).target)
    (hv : (A.chart j).symm y ∉ tsupport v) :
    locDens A (Fin.cons (LocPot.ofFun v) Φ) j y = 0 := by
  unfold locDens
  have hfam : (fun i y' => ((Fin.cons (LocPot.ofFun v) Φ : Fin (e + 1) → LocPot X) i).φ
      ((A.chart j).symm y) ((A.chart j).symm y')) =
      Fin.cons (fun y' => v ((A.chart j).symm y'))
        (fun i y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i <;> rfl
  rw [hfam]
  apply maDens_cons_eq_zero
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (tsupport v)ᶜ) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target
      (isClosed_tsupport v).isOpen_compl
  filter_upwards [hO.mem_nhds ⟨hy, hv⟩] with y' hy'
  exact image_eq_zero_of_notMem_tsupport hy'.2

theorem volume_coord_eq_zero {n : ℕ} (i : Fin n) : volume {y : Fin n → ℂ | y i = 0} = 0 := by
  have : {y : Fin n → ℂ | y i = 0} = Function.eval i ⁻¹' {0} := rfl
  rw [this, volume_pi]
  exact Measure.pi_eval_preimage_null _ (measure_singleton 0)

theorem ae_coord_ne_zero {n : ℕ} : ∀ᵐ y : Fin n → ℂ, ∀ i, y i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  simpa using volume_coord_eq_zero i

theorem contDiffOn_compat {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) :
    ContDiffOn ℝ ∞ (f ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' U) := by
  intro y hy
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨a, ha⟩ := A.cover (ψ.symm y)
  have h1 : ContDiffAt ℝ ∞ (f ∘ (A.chart a).symm) (A.chart a (ψ.symm y)) := by
    have hO' : IsOpen ((A.chart a).target ∩ (A.chart a).symm ⁻¹' U) :=
      (A.chart a).continuousOn_symm.isOpen_inter_preimage (A.chart a).open_target hU
    refine (hf a).contDiffAt (hO'.mem_nhds ⟨(A.chart a).map_source ha, ?_⟩)
    simpa [(A.chart a).left_inv ha] using hy.2
  have h2 : ContDiffAt ℝ ∞ (A.chart a ∘ ψ.symm) y :=
    ((hψ a).2 y ⟨hy.1, ha⟩).contDiffAt.restrict_scalars ℝ
  refine (h1.comp y h2).congr_of_eventuallyEq ?_
  have hN : ψ.target ∩ ψ.symm ⁻¹' (A.chart a).source ∈ 𝓝 y :=
    (ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target (A.chart a).open_source).mem_nhds
      ⟨hy.1, ha⟩
  filter_upwards [hN] with y' hy'
  simp [(A.chart a).left_inv hy'.2]

theorem analyticAt_compat {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) (a : Fin A.n) {p : X} (hpa : p ∈ (A.chart a).source)
    (hpψ : p ∈ ψ.source) : AnalyticAt ℂ (ψ ∘ (A.chart a).symm) (A.chart a p) :=
  (hψ a).1 _ ⟨(A.chart a).map_source hpa, by simpa [(A.chart a).left_inv hpa] using hpψ⟩

def chartPush (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (F : (Fin e → ℂ) → ℝ) : X → ℝ :=
  ψ.source.indicator (F ∘ ψ)

def chartExt (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (v : X → ℝ) : (Fin e → ℂ) → ℝ :=
  ψ.target.indicator (v ∘ ψ.symm)

theorem chartPush_eq_zero (ψ : OpenPartialHomeomorph X (Fin e → ℂ))
    {F : (Fin e → ℂ) → ℝ} {p : X}
    (hp : p ∉ ψ.symm '' tsupport F) : chartPush ψ F p = 0 := by
  unfold chartPush
  by_cases hs : p ∈ ψ.source
  · rw [Set.indicator_of_mem hs]
    by_contra hne
    exact hp ⟨ψ p, subset_tsupport _ hne, ψ.left_inv hs⟩
  · exact Set.indicator_of_notMem hs _

theorem isCompact_symm_image {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} {F : (Fin e → ℂ) → ℝ}
    (hK : IsCompact (tsupport F)) (hKt : tsupport F ⊆ ψ.target) :
    IsCompact (ψ.symm '' tsupport F) :=
  hK.image_of_continuousOn (ψ.continuousOn_symm.mono hKt)

theorem tsupport_chartPush [T2Space X] (ψ : OpenPartialHomeomorph X (Fin e → ℂ))
    {F : (Fin e → ℂ) → ℝ} (hK : IsCompact (tsupport F)) (hKt : tsupport F ⊆ ψ.target) :
    tsupport (chartPush ψ F) ⊆ ψ.symm '' tsupport F := by
  refine closure_minimal (fun p hp => ?_) (isCompact_symm_image hK hKt).isClosed
  by_contra h
  exact hp (chartPush_eq_zero ψ h)

theorem tsupport_chartPush_source [T2Space X] (ψ : OpenPartialHomeomorph X (Fin e → ℂ))
    {F : (Fin e → ℂ) → ℝ} (hK : IsCompact (tsupport F)) (hKt : tsupport F ⊆ ψ.target) :
    tsupport (chartPush ψ F) ⊆ ψ.source := by
  refine (tsupport_chartPush ψ hK hKt).trans ?_
  rintro _ ⟨y, hy, rfl⟩
  exact ψ.map_target (hKt hy)

theorem smooth_chartPush [T2Space X] {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) {F : (Fin e → ℂ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hK : IsCompact (tsupport F)) (hKt : tsupport F ⊆ ψ.target) : A.Smooth (chartPush ψ F) := by
  intro a y hy
  refine ContDiffAt.contDiffWithinAt ?_
  set C := ψ.symm '' tsupport F
  have hC : IsClosed C := (isCompact_symm_image hK hKt).isClosed
  by_cases hs : (A.chart a).symm y ∈ ψ.source
  · have hya : (A.chart a).symm y ∈ (A.chart a).source := (A.chart a).map_target hy.1
    have h2 : ContDiffAt ℝ ∞ (ψ ∘ (A.chart a).symm) y := by
      have := (analyticAt_compat hψ a hya hs).contDiffAt (n := ∞)
      rw [(A.chart a).right_inv hy.1] at this
      exact this.restrict_scalars ℝ
    refine (hF.contDiffAt.comp y h2).congr_of_eventuallyEq ?_
    have hN : (A.chart a).target ∩ (A.chart a).symm ⁻¹' ψ.source ∈ 𝓝 y :=
      ((A.chart a).continuousOn_symm.isOpen_inter_preimage (A.chart a).open_target
        ψ.open_source).mem_nhds ⟨hy.1, hs⟩
    filter_upwards [hN] with y' hy'
    simp only [chartPush, Function.comp_apply]
    rw [Set.indicator_of_mem (show (A.chart a).symm y' ∈ ψ.source from hy'.2)]
    rfl
  · have hnC : (A.chart a).symm y ∉ C := fun h => hs (by
      obtain ⟨z, hz, hzz⟩ := h
      rw [← hzz]; exact ψ.map_target (hKt hz))
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    have hN : (A.chart a).target ∩ (A.chart a).symm ⁻¹' Cᶜ ∈ 𝓝 y :=
      ((A.chart a).continuousOn_symm.isOpen_inter_preimage (A.chart a).open_target
        hC.isOpen_compl).mem_nhds ⟨hy.1, hnC⟩
    filter_upwards [hN] with y' hy'
    exact chartPush_eq_zero ψ hy'.2

theorem contDiff_chartExt [T2Space X] [CompactSpace X] {A : FinHolAtlas e X}
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) {v : X → ℝ}
    (hv : A.Smooth v) (hvs : tsupport v ⊆ ψ.source) :
    ContDiff ℝ ∞ (chartExt ψ v) ∧ IsCompact (ψ '' tsupport v) ∧
      tsupport (chartExt ψ v) ⊆ ψ '' tsupport v := by
  have hK : IsCompact (ψ '' tsupport v) :=
    (isClosed_tsupport v).isCompact.image_of_continuousOn (ψ.continuousOn.mono hvs)
  have hsupp : ∀ y, y ∉ ψ '' tsupport v → chartExt ψ v y = 0 := by
    intro y hy
    unfold chartExt
    by_cases ht : y ∈ ψ.target
    · rw [Set.indicator_of_mem ht]
      by_contra hne
      exact hy ⟨ψ.symm y, subset_tsupport _ hne, ψ.right_inv ht⟩
    · exact Set.indicator_of_notMem ht _
  refine ⟨?_, hK, closure_minimal (fun y hy => by_contra fun h => hy (hsupp y h)) hK.isClosed⟩
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases ht : y ∈ ψ.target
  · have h1 := contDiffOn_compat hψ isOpen_univ hv
    simp only [Set.preimage_univ, Set.inter_univ] at h1
    refine (h1.contDiffAt (ψ.open_target.mem_nhds ht)).congr_of_eventuallyEq ?_
    filter_upwards [ψ.open_target.mem_nhds ht] with y' hy'
    simp [chartExt, Set.indicator_of_mem hy']
  · have hy : y ∉ ψ '' tsupport v := by
      rintro ⟨p, hp, rfl⟩; exact ht (ψ.map_source (hvs hp))
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hy] with y' hy'
    exact hsupp y' hy'

end

end ReciprocityTheory.AnForm.M.PLAux
end

section -- merged from ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInhab
namespace ReciprocityTheory.AnForm.M

open FinHolAtlas

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem holoMap_id (A : FinHolAtlas e X) : HoloMap A A id :=
  ⟨continuous_id, fun j k => A.holo j k⟩

theorem isAnalyticSubset_empty (A : FinHolAtlas e X) : A.IsAnalyticSubset ∅ := by
  intro x
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ x, 1, fun _ _ => (1 : ℂ), ?_, ?_⟩
  · intro i j
    exact analyticOnNhd_const
  · ext y
    simp

theorem det_fderiv_transition_ne_zero (A : FinHolAtlas e X) (j k : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hk : (A.chart j).symm y ∈ (A.chart k).source) :
    LinearMap.det (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  have hU : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
    (A.chart j).isOpen_inter_preimage_symm (A.chart k).open_source
  have hyU : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source := ⟨hy, hk⟩
  have hfd : DifferentiableAt ℂ (A.chart k ∘ (A.chart j).symm) y :=
    (A.holo j k y hyU).differentiableAt
  have hz : (A.chart k ∘ (A.chart j).symm) y ∈
      (A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source := by
    refine ⟨(A.chart k).map_source hk, ?_⟩
    show (A.chart k).symm (A.chart k ((A.chart j).symm y)) ∈ (A.chart j).source
    rw [(A.chart k).left_inv hk]
    exact (A.chart j).map_target hy
  have hgd : DifferentiableAt ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y) :=
    (A.holo k j _ hz).differentiableAt
  have hev : (A.chart j ∘ (A.chart k).symm) ∘ (A.chart k ∘ (A.chart j).symm) =ᶠ[nhds y] id := by
    filter_upwards [hU.mem_nhds hyU] with y' hy'
    show (A.chart j) ((A.chart k).symm ((A.chart k) ((A.chart j).symm y'))) = y'
    rw [(A.chart k).left_inv hy'.2, (A.chart j).right_inv hy'.1]
  have hcomp : (fderiv ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y)).comp
      (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y) = ContinuousLinearMap.id ℂ (Fin e → ℂ) := by
    rw [← fderiv_comp y hgd hfd, hev.fderiv_eq, fderiv_id]
  intro h0
  have hdet : LinearMap.det (((fderiv ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y)) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)).comp
      ((fderiv ℂ (A.chart k ∘ (A.chart j).symm) y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) = 1 := by
    have hc : ((fderiv ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y)) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)).comp ((fderiv ℂ (A.chart k ∘ (A.chart j).symm) y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
        (((fderiv ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y)).comp (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y) : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := rfl
    rw [hc, hcomp, ContinuousLinearMap.coe_id, LinearMap.det_id]
  rw [LinearMap.det_comp, h0, mul_zero] at hdet
  exact zero_ne_one hdet

theorem isDegreeOff_id (A : FinHolAtlas e X) : IsDegreeOff A A id 1 ∅ := by
  refine ⟨isAnalyticSubset_empty A, interior_empty, ?_, ?_, ?_, ?_⟩
  · rw [Set.preimage_id]
    exact isAnalyticSubset_empty A
  · rw [Set.preimage_id]
    exact interior_empty
  · intro x _
    rw [Set.preimage_id]
    exact Set.ncard_singleton x
  · intro j k y hy _ hk
    rw [Function.id_comp]
    exact det_fderiv_transition_ne_zero A j k hy hk

end ReciprocityTheory.AnForm.M
end
