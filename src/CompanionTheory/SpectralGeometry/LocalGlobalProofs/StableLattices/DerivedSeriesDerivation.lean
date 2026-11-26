module

public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesDerivation
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesDerivation
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuDsDer

section general

variable {E E' V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]

def dL (a : E → E) (Φ : E × E' → V) (q : E × E') : V := fderiv ℝ Φ q (a q.1, 0)

def dR (b : E' → E') (Φ : E × E' → V) (q : E × E') : V := fderiv ℝ Φ q (0, b q.2)

theorem contDiff_dL {a : E → E} (ha : ContDiff ℝ ∞ a) {Φ : E × E' → V} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (dL a Φ) := by
  exact (contDiff_infty_iff_fderiv.1 hΦ).2.clm_apply ((ha.comp contDiff_fst).prodMk contDiff_const)

theorem contDiff_dR {b : E' → E'} (hb : ContDiff ℝ ∞ b) {Φ : E × E' → V} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (dR b Φ) := by
  exact (contDiff_infty_iff_fderiv.1 hΦ).2.clm_apply (contDiff_const.prodMk (hb.comp contDiff_snd))

theorem dR_dL {a : E → E} (ha : ContDiff ℝ ∞ a) {b : E' → E'} (hb : ContDiff ℝ ∞ b) {Φ : E × E' → V}
    (hΦ : ContDiff ℝ ∞ Φ) : dR b (dL a Φ) = dL a (dR b Φ) := by
  funext q
  have hΦ1 : ContDiff ℝ ∞ (fderiv ℝ Φ) := (contDiff_infty_iff_fderiv.1 hΦ).2
  have hc : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) q) q :=
    ((hΦ1.differentiable (by simp)) q).hasFDerivAt
  have hua : HasFDerivAt (fun q : E × E' => (a q.1, (0 : E')))
      (((fderiv ℝ a q.1).comp (ContinuousLinearMap.fst ℝ E E')).prod 0) q :=
    (((ha.differentiable (by simp)) q.1).hasFDerivAt.comp q hasFDerivAt_fst).prodMk (hasFDerivAt_const 0 q)
  have hub : HasFDerivAt (fun q : E × E' => ((0 : E), b q.2))
      ((0 : E × E' →L[ℝ] E).prod ((fderiv ℝ b q.2).comp (ContinuousLinearMap.snd ℝ E E'))) q :=
    (hasFDerivAt_const 0 q).prodMk (((hb.differentiable (by simp)) q.2).hasFDerivAt.comp q hasFDerivAt_snd)
  have hsymm := ((contDiff_infty.1 hΦ 2).contDiffAt (x := q)).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  show fderiv ℝ (dL a Φ) q (0, b q.2) = fderiv ℝ (dR b Φ) q (a q.1, 0)
  rw [show dL a Φ = fun y => fderiv ℝ Φ y (a y.1, 0) from rfl,
    show dR b Φ = fun y => fderiv ℝ Φ y (0, b y.2) from rfl,
    (hc.clm_apply hua).fderiv, (hc.clm_apply hub).fderiv]
  simp
  exact hsymm _ _

end general

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def dW (W : List (Mat n)) (Φ : Mat n × Mat n → H) : Mat n × Mat n → H :=
  W.foldr (fun Y => dL fun g => g * Y) Φ

theorem contDiff_mulR (Y : Mat n) : ContDiff ℝ ∞ fun g : Mat n => g * Y := by
  exact contDiff_mul' contDiff_id contDiff_const

theorem contDiff_dW {Φ : Mat n × Mat n → H} (hΦ : ContDiff ℝ ∞ Φ) : ∀ W, ContDiff ℝ ∞ (dW W Φ) := by
  intro W
  induction W with
  | nil => exact hΦ
  | cons Y W ih => exact contDiff_dL (contDiff_mulR Y) ih

theorem dR_dW {b : Mat n → Mat n} (hb : ContDiff ℝ ∞ b) {Φ : Mat n × Mat n → H} (hΦ : ContDiff ℝ ∞ Φ) :
    ∀ W, dR b (dW W Φ) = dW W (dR b Φ) := by
  intro W
  induction W with
  | nil => rfl
  | cons Y W ih =>
    show dR b (dL (fun g => g * Y) (dW W Φ)) = dL (fun g => g * Y) (dW W (dR b Φ))
    rw [dR_dL (contDiff_mulR Y) hb (contDiff_dW hΦ W), ih]

theorem hasDerivAt_dL {Φ : Mat n × Mat n → H} (hΦ : ContDiff ℝ ∞ Φ) (Y g y : Mat n) :
    HasDerivAt (fun t => Φ (g * ex Y t, y)) (dL (fun g => g * Y) Φ (g, y)) 0 := by
  have hγ : HasDerivAt (fun t : ℝ => (g * ex Y t, y)) (g * Y, (0 : Mat n)) 0 :=
    (hasDerivAt_mul_ex g Y).prodMk (hasDerivAt_const 0 y)
  have h0 : (g, y) = (g * ex Y 0, y) := by rw [ex_zero, mul_one]
  exact ((hΦ.differentiable (by simp)) (g, y)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ h0

theorem hasDerivAt_dR {Φ : Mat n × Mat n → H} (hΦ : ContDiff ℝ ∞ Φ) (X g y : Mat n) :
    HasDerivAt (fun t => Φ (g, y * ex X t)) (dR (fun y => y * X) Φ (g, y)) 0 := by
  have hγ : HasDerivAt (fun t : ℝ => (g, y * ex X t)) ((0 : Mat n), y * X) 0 :=
    (hasDerivAt_const 0 g).prodMk (hasDerivAt_mul_ex y X)
  have h0 : (g, y) = (g, y * ex X 0) := by rw [ex_zero, mul_one]
  exact ((hΦ.differentiable (by simp)) (g, y)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ h0

variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

private theorem dW_eq_smul_dsW_of_eq_on_open (h : RepOn G σ) {u : H} (hu : IsSm G σ u) {Φ : Mat n × Mat n → H}
    (hΦ : ContDiff ℝ ∞ Φ) {y : Mat n} {O : Set (Mat n)} (hO : IsOpen O)
    (hΦu : ∀ g ∈ G, g ∈ O → Φ (g, y) = σ g u) :
    ∀ {W : List (Mat n)}, LieW G W → ∀ g ∈ G, g ∈ O → dW W Φ (g, y) = σ g (dsW σ W u) := by
  intro W
  induction W with
  | nil => intro _ g hg hgO; exact hΦu g hg hgO
  | cons Y W ih =>
    intro hW g hg hgO
    have hY : ∀ t, ex Y t ∈ G := hW Y (by simp)
    have hW' : LieW G W := fun X hX => hW X (by simp [hX])
    have hc : ContinuousAt (fun t : ℝ => g * ex Y t) 0 := (hasDerivAt_mul_ex g Y).continuousAt
    have hO' : O ∈ nhds (g * ex Y 0) := by rw [ex_zero, mul_one]; exact hO.mem_nhds hgO
    have hev : (fun t => σ (g * ex Y t) (dsW σ W u)) =ᶠ[nhds 0] fun t => dW W Φ (g * ex Y t, y) := by
      filter_upwards [hc.preimage_mem_nhds hO'] with t ht
      exact (ih hW' _ (h.mul_mem g hg _ (hY t)) ht).symm
    have hd := (hasDerivAt_dL (contDiff_dW hΦ W) Y g y).congr_of_eventuallyEq hev
    rw [dsW_cons, apply_ds h hY hg (CompanionTheory.D.Upq.Sm.IsSm.differentiableAt h (CompanionTheory.D.Upq.Sm.IsSm.dsW h hu hW') hY)]
    exact hd.deriv.symm

private theorem hasDerivAt_dsW_smul_mul_ex (h : RepOn G σ) {x : H} (hx : IsSm G σ x) {F : Mat n → H}
    (hF : ContDiff ℝ ∞ F) {O : Set (Mat n)} (hO : IsOpen O) (hFx : ∀ g ∈ G, g ∈ O → σ g x = F g)
    {W : List (Mat n)} (hW : LieW G W) {p : Mat n} (hp : p ∈ G) (hpO : p ∈ O) {X : Mat n}
    (hX : ∀ t, ex X t ∈ G) :
    HasDerivAt (fun τ : ℝ => dsW σ W (σ (p * ex X τ) x)) (dsW σ W (σ p (ds σ X x))) 0 := by
  have hΦ : ContDiff ℝ ∞ (fun q : Mat n × Mat n => F (q.1 * q.2)) := hF.comp contDiff_mul
  have h1 : (1 : Mat n) ∈ G := h.one_mem
  have hσ1 : ∀ v, σ 1 v = v := fun v => by rw [h.map_one]; rfl
  have hcont : ∀ y : Mat n, Continuous (fun g : Mat n => g * y) := fun y => (contDiff_mulR y).continuous
  have hpτ : ∀ᶠ τ in nhds (0 : ℝ), p * ex X τ ∈ O := by
    have hc : ContinuousAt (fun t : ℝ => p * ex X t) 0 := (hasDerivAt_mul_ex p X).continuousAt
    have hO' : O ∈ nhds (p * ex X 0) := by rw [ex_zero, mul_one]; exact hO.mem_nhds hpO
    exact hc.preimage_mem_nhds hO'
  have hev : (fun τ : ℝ => dW W (fun q : Mat n × Mat n => F (q.1 * q.2)) (1, p * ex X τ)) =ᶠ[nhds 0]
      fun τ : ℝ => dsW σ W (σ (p * ex X τ) x) := by
    filter_upwards [hpτ] with τ hτ
    have hpτG : p * ex X τ ∈ G := h.mul_mem p hp _ (hX τ)
    have key := dW_eq_smul_dsW_of_eq_on_open (y := p * ex X τ) (O := (fun g => g * (p * ex X τ)) ⁻¹' O) h
      (CompanionTheory.D.Upq.Sm.IsSm.apply h hx hpτG) hΦ (hO.preimage (hcont _))
      (fun g hg hgO => by
        show F (g * (p * ex X τ)) = σ g (σ (p * ex X τ) x)
        rw [← hFx _ (h.mul_mem g hg _ hpτG) hgO, h.apply_mul hg hpτG]) hW 1 h1
      (by show 1 * (p * ex X τ) ∈ O; rw [one_mul]; exact hτ)
    rw [key, hσ1]
  have hd := hasDerivAt_dR (contDiff_dW hΦ W) X 1 p
  rw [dR_dW (contDiff_mulR X) hΦ W] at hd
  have hX1 : LieW G [X] := by
    intro Y hY t
    simp only [List.mem_singleton] at hY
    subst hY
    exact hX t
  have hds : IsSm G σ (ds σ X x) := CompanionTheory.D.Upq.Sm.IsSm.dsW h hx hX1
  have hΦ2 : ∀ g ∈ G, g ∈ (fun g => g * p) ⁻¹' O →
      dR (fun y => y * X) (fun q : Mat n × Mat n => F (q.1 * q.2)) (g, p) = σ g (σ p (ds σ X x)) := by
    intro g hg hgO
    rw [← (hasDerivAt_dR hΦ X g p).deriv]
    have hgp : g * p ∈ G := h.mul_mem g hg p hp
    rw [← h.apply_mul hg hp, apply_ds h hX hgp (CompanionTheory.D.Upq.Sm.IsSm.differentiableAt h hx hX)]
    apply Filter.EventuallyEq.deriv_eq
    have hc : ContinuousAt (fun t : ℝ => g * p * ex X t) 0 := (hasDerivAt_mul_ex (g * p) X).continuousAt
    have hO' : O ∈ nhds (g * p * ex X 0) := by rw [ex_zero, mul_one]; exact hO.mem_nhds hgO
    filter_upwards [hc.preimage_mem_nhds hO'] with t ht
    show F (g * (p * ex X t)) = σ (g * p * ex X t) x
    rw [← mul_assoc, hFx _ (h.mul_mem _ hgp _ (hX t)) ht]
  have key2 := dW_eq_smul_dsW_of_eq_on_open h (CompanionTheory.D.Upq.Sm.IsSm.apply h hds hp) (contDiff_dR (contDiff_mulR X) hΦ)
    (hO.preimage (hcont p)) hΦ2 hW 1 h1 (by show 1 * p ∈ O; rw [one_mul]; exact hpO)
  rw [key2, hσ1] at hd
  exact hd.congr_of_eventuallyEq hev.symm

private theorem exists_contDiff_eq_on_nhds_of_contDiffOn {F : Mat n → H} {U : Set (Mat n)} {p : Mat n} (hU : IsOpen U) (hpU : p ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) :
    ∃ F' : Mat n → H, ContDiff ℝ ∞ F' ∧ ∃ O : Set (Mat n), IsOpen O ∧ p ∈ O ∧ O ⊆ U ∧ ∀ g ∈ O, F' g = F g := by
  obtain ⟨r, hr0, hrU⟩ := Metric.isOpen_iff.1 hU p hpU
  let φ : ContDiffBump p := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨fun g => (φ g : ℝ) • F g, ?_, Metric.ball p (r / 4), Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity), fun g hg => hrU (Metric.ball_subset_ball (by linarith) hg),
    fun g hg => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ Metric.ball p r
    · exact (φ.contDiff.contDiffAt).smul (hF.contDiffAt (hU.mem_nhds (hrU hz)))
    · have hzc : z ∈ (Metric.closedBall p (r / 2))ᶜ := by
        intro hz'
        exact hz (Metric.closedBall_subset_ball (by linarith) hz')
      have hev0 : ∀ᶠ g in nhds z, φ g = 0 := by
        filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hzc] with g hg
        apply φ.zero_of_le_dist
        simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] at hg
        exact hg.le
      have hev : (fun g => (φ g : ℝ) • F g) =ᶠ[nhds z] fun _ => (0 : H) := by
        filter_upwards [hev0] with g hg
        simp [hg]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · show (φ g : ℝ) • F g = F g
    rw [φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hg), one_smul]

theorem dsDer : DsDer := by
  intro n Hm H _ _ _ σ hσ W hW p hp X hX x hx
  have h := hσ.rep
  have hLX : ∀ Y : Mat n, CompanionTheory.Bmu.Lie Hm Y → ∀ t, ex Y t ∈ Formalism.QuantumDeterminants.UH Hm :=
    fun Y hY t => ex_mem_of_lie hY t
  obtain ⟨U, F, hU, hpU, hFU, hFx⟩ := hx p hp
  obtain ⟨F', hF', O, hO, hpO, hOU, hF'O⟩ := exists_contDiff_eq_on_nhds_of_contDiffOn hU hpU hFU
  exact hasDerivAt_dsW_smul_mul_ex h hx hF' hO
    (fun g hg hgO => by rw [hF'O g hgO]; exact hFx g (hOU hgO) hg)
    (fun Y hY => hLX Y (hW Y hY)) hp hpO (hLX X hX)

end GlobalTheory.CompanionTheory.BmuDsDer

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesDerivationStatement
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DerivedSeriesDerivation : DsDer := by
  first | exact @GlobalTheory.CompanionTheory.BmuDsDer.dsDer | exact GlobalTheory.CompanionTheory.BmuDsDer.dsDer | (intros; apply GlobalTheory.CompanionTheory.BmuDsDer.dsDer <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugacy
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugacy
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuTorConj

theorem cStd_ne : cStd ≠ 0 := by
  simp [cStd, Complex.I_ne_zero]

theorem exists_scale (r : ℕ) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) :
    ∃ T : ℕ → ℂ, (∀ n, T n ≠ 0) ∧ (∀ n, r ≤ n → T n = 1) ∧
      ∀ a : Fin r, c a * T a.val = cStd * T (a.val + 1) := by
  classical
  obtain ⟨c', hc'd⟩ : ∃ f : ℕ → ℂ, f = fun m => if h : m < r then c ⟨m, h⟩ else 1 := ⟨_, rfl⟩
  have hc' : ∀ m, c' m ≠ 0 := fun m => by
    by_cases h : m < r
    · simp only [hc'd, dif_pos h]; exact hc _
    · simp only [hc'd, dif_neg h]; exact one_ne_zero
  refine ⟨fun n => ∏ m ∈ Finset.Ico n r, (cStd / c' m), ?_, ?_, ?_⟩
  · intro n
    exact Finset.prod_ne_zero_iff.mpr fun m _ => div_ne_zero cStd_ne (hc' m)
  · intro n hn
    simp [Finset.Ico_eq_empty_of_le hn]
  · intro a
    simp only
    rw [Finset.prod_eq_prod_Ico_succ_bot a.isLt]
    have hca : c' a.val = c a := by simp only [hc'd, dif_pos a.isLt]
    rw [hca]
    have hcz := hc a
    field_simp

theorem hpk_row (k r : ℕ) (p q : Fin (2 * r + k + 1)) (hpq : p.val + q.val = 2 * r + k)
    (h : p.val < r ∨ q.val < r) (j : Fin (2 * r + k + 1)) :
    Hpk k r p j = if j = q then 1 else 0 := by
  have hp := p.isLt
  have hq := q.isLt
  unfold Hpk
  by_cases hjq : j = q
  · subst hjq
    rw [if_pos rfl]
    rcases h with h | h
    · rw [if_pos ⟨h, hpq⟩]
    · rw [if_neg (by omega), if_pos ⟨h, hpq⟩]
  · rw [if_neg hjq]
    have hjv : j.val ≠ q.val := fun e => hjq (Fin.ext e)
    rw [if_neg (by omega), if_neg (by omega), if_neg]
    rintro ⟨h1, h2, -⟩
    omega

theorem uw_col (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hh : h ∈ UWset k r z) (p : Fin (2 * r + k + 1)) (hp : p.val < r ∨ r + k < p.val)
    (i : Fin (2 * r + k + 1)) : h i p = if i = p then 1 else 0 := by
  obtain ⟨-, hcols, -⟩ := hh
  have hplt := p.isLt
  rcases hp with hp | hp
  · have e : eI k r ⟨p.val, hp⟩ = p := Fin.ext rfl
    have hx := congrFun (hcols ⟨p.val, hp⟩).1 i
    rw [e] at hx
    simpa [bvec, mulVec_single, Pi.single_apply] using hx
  · have e : esI k r ⟨2 * r + k - p.val, by omega⟩ = p := by
      apply Fin.ext
      show 2 * r + k - (2 * r + k - p.val) = p.val
      omega
    have hx := congrFun (hcols ⟨2 * r + k - p.val, by omega⟩).2 i
    rw [e] at hx
    simpa [bvec, mulVec_single, Pi.single_apply] using hx

theorem uw_row (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hh : h ∈ UWset k r z) (q : Fin (2 * r + k + 1)) (hq : q.val < r ∨ r + k < q.val)
    (j : Fin (2 * r + k + 1)) : h q j = if j = q then 1 else 0 := by
  have hqlt := q.isLt
  obtain ⟨p, hpd⟩ : ∃ p : Fin (2 * r + k + 1), p.val = 2 * r + k - q.val := ⟨⟨2 * r + k - q.val, by omega⟩, rfl⟩
  have hp : p.val < r ∨ r + k < p.val := by omega
  have hpq : p.val + q.val = 2 * r + k := by omega
  have hor : p.val < r ∨ q.val < r := by omega
  have hc : ∀ i, h i p = if i = p then 1 else 0 := uw_col k r z h hh p hp
  have hr : ∀ j', Hpk k r p j' = if j' = q then 1 else 0 := hpk_row k r p q hpq hor
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have hx := congrFun (congrFun hU p) j
  simp only [Matrix.mul_apply, conjTranspose_apply, hc, hr] at hx
  simpa [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul, hr] using hx

theorem torConj : CompanionTheory.Bmu.TorConj := by
  unfold CompanionTheory.Bmu.TorConj
  intro k r z c hz hc
  obtain ⟨T, hT0, hT1, hTc⟩ := exists_scale r c hc
  obtain ⟨d, hd⟩ : ∃ d : Fin (2 * r + k + 1) → ℂ, d = fun i =>
      if i.val < r then T i.val else if i.val ≤ r + k then 1 else (star (T (2 * r + k - i.val)))⁻¹ :=
    ⟨_, rfl⟩
  have hdlow : ∀ i : Fin (2 * r + k + 1), i.val < r → d i = T i.val := fun i hi => by
    rw [hd]; simp only; rw [if_pos hi]
  have hdmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → d i = 1 := fun i h1 h2 => by
    rw [hd]; simp only; rw [if_neg (by omega), if_pos h2]
  have hdhigh : ∀ i : Fin (2 * r + k + 1), r + k < i.val → d i = (star (T (2 * r + k - i.val)))⁻¹ :=
    fun i hi => by
      rw [hd]; simp only; rw [if_neg (by omega), if_neg (by omega)]
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i
    by_cases h1 : i.val < r
    · rw [hdlow i h1]; exact hT0 _
    by_cases h2 : i.val ≤ r + k
    · rw [hdmid i (by omega) h2]; exact one_ne_zero
    · rw [hdhigh i (by omega)]; exact inv_ne_zero (star_ne_zero.mpr (hT0 _))
  have hHnz : ∀ i j : Fin (2 * r + k + 1), Hpk k r i j ≠ 0 →
      (i.val < r ∧ i.val + j.val = 2 * r + k) ∨ (j.val < r ∧ i.val + j.val = 2 * r + k) ∨
        (r ≤ i.val ∧ i.val ≤ r + k ∧ i = j) := by
    intro i j h
    unfold Hpk at h
    split_ifs at h with h1 h2 h3 <;> first | exact absurd rfl h | tauto
  have hkey : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1 := by
    intro i j h
    have hilt := i.isLt
    have hjlt := j.isLt
    rcases hHnz i j h with ⟨hi, hij⟩ | ⟨hj, hij⟩ | ⟨hi1, hi2, rfl⟩
    · rw [hdlow i hi, hdhigh j (by omega), show 2 * r + k - j.val = i.val by omega]
      exact mul_inv_cancel₀ (star_ne_zero.mpr (hT0 _))
    · rw [hdhigh i (by omega), hdlow j hj, show 2 * r + k - i.val = j.val by omega]
      simp [hT0 j.val]
    · rw [hdmid i hi1 hi2]; simp
  have hdiagU : ∀ e : Fin (2 * r + k + 1) → ℂ, (∀ i j, Hpk k r i j ≠ 0 → star (e i) * e j = 1) →
      diagonal e ∈ UH (Hpk k r) := by
    intro e he
    show (diagonal e)ᴴ * Hpk k r * diagonal e = Hpk k r
    ext i j
    rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply]
    by_cases h0 : Hpk k r i j = 0
    · rw [h0]; ring
    · calc star (e i) * Hpk k r i j * e j = (star (e i) * e j) * Hpk k r i j := by ring
        _ = Hpk k r i j := by rw [he i j h0, one_mul]
  have hUmul : ∀ A B, A ∈ UH (Hpk k r) → B ∈ UH (Hpk k r) → A * B ∈ UH (Hpk k r) := by
    intro A B hA hB
    have hA' : Aᴴ * Hpk k r * A = Hpk k r := hA
    have hB' : Bᴴ * Hpk k r * B = Hpk k r := hB
    show (A * B)ᴴ * Hpk k r * (A * B) = Hpk k r
    rw [conjTranspose_mul]
    calc Bᴴ * Aᴴ * Hpk k r * (A * B) = Bᴴ * (Aᴴ * Hpk k r * A) * B := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hA', hB']
  have hτU : diagonal d ∈ UH (Hpk k r) := hdiagU d hkey
  have hτinvU : diagonal (fun i => (d i)⁻¹) ∈ UH (Hpk k r) := by
    refine hdiagU _ fun i j h => ?_
    rw [star_inv₀, ← mul_inv, hkey i j h, inv_one]
  have hτinv : (diagonal d)⁻¹ = diagonal (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal]
    have he : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℂ) := funext fun i => inv_mul_cancel₀ (hd0 i)
    rw [he, diagonal_one]
  have hcomm : ∀ h ∈ UWset k r z, diagonal d * h = h * diagonal d := by
    intro h hh
    ext i j
    rw [diagonal_mul, mul_diagonal]
    by_cases hij : i = j
    · subst hij; ring
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [uw_row k r z h hh i hi j, if_neg (fun e => hij e.symm)]; ring
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [uw_col k r z h hh j hj i, if_neg hij]; ring
    push_neg at hi hj
    rw [hdmid i hi.1 hi.2, hdmid j hj.1 hj.2]; ring
  have hzd : ∀ j, (d j)⁻¹ * z j = z j := by
    intro j
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj, mul_zero]
    · push_neg at hj; rw [hdmid j hj.1 hj.2, inv_one, one_mul]
  refine ⟨diagonal d, hτU, hcomm, fun m hm => ?_⟩
  rw [hτinv]
  obtain ⟨hmU, hm2, hm3⟩ := hm
  have hent : ∀ i j, (diagonal d * m * diagonal (fun i => (d i)⁻¹)) i j = d i * m i j * (d j)⁻¹ := by
    intro i j
    rw [mul_diagonal, diagonal_mul]
  refine ⟨⟨hUmul _ _ (hUmul _ _ hτU hmU) hτinvU, ?_, ?_⟩, ?_⟩
  · intro a i hai
    rw [hent, hm2 a i hai]
    split_ifs with h
    · subst h; rw [mul_one, mul_inv_cancel₀ (hd0 _)]
    · simp
  · intro i j hj1 hj2 hi
    rw [hent, hm3 i j hj1 hj2 hi]
    split_ifs with h
    · subst h; rw [mul_one, mul_inv_cancel₀ (hd0 _)]
    · simp
  · have hsum : ∑ a, c a * PI.BesselMapUniq.ellA k r z (diagonal d * m * diagonal (fun i => (d i)⁻¹)) a =
        cStd * ell k r z m := by
      rw [ell, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [PI.BesselMapUniq.ellA]
      have e1 : d (eI k r a) = T a.val := hdlow _ a.isLt
      split_ifs with ha
      · have e2 : d (eI k r ⟨a.val + 1, ha⟩) = T (a.val + 1) := hdlow _ ha
        rw [hent, e1, e2, ← mul_assoc, ← mul_assoc, hTc a,
          mul_right_comm (cStd * T (a.val + 1)), mul_inv_cancel_right₀ (hT0 _)]
      · have hmv : (diagonal d * m * diagonal (fun i => (d i)⁻¹)).mulVec z (eI k r a) =
            d (eI k r a) * m.mulVec z (eI k r a) := by
          simp only [mulVec, dotProduct, hent, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          calc d (eI k r a) * m (eI k r a) j * (d j)⁻¹ * z j
              = d (eI k r a) * m (eI k r a) j * ((d j)⁻¹ * z j) := by ring
            _ = d (eI k r a) * (m (eI k r a) j * z j) := by rw [hzd j]; ring
        rw [hmv, e1, ← mul_assoc, hTc a, hT1 _ (by omega), mul_one]
    rw [PI.BesselMapUniq.psiGen, psi, hsum]

end GlobalTheory.CompanionTheory.BmuTorConj
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugacyStatement
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TorusConjugacy : TorConj := by
  first | exact @GlobalTheory.CompanionTheory.BmuTorConj.torConj | exact GlobalTheory.CompanionTheory.BmuTorConj.torConj | (intros; apply GlobalTheory.CompanionTheory.BmuTorConj.torConj <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTrace
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTrace
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckDecOfTrace

universe u

variable {O : Type u} {N : O → Type} [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]
  {Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop}

def homSub (hc : IsLinCat N Hom) (a b : O) : Submodule ℂ (N a →ₗ[ℂ] N b) where
  carrier := {f | Hom a b f}
  add_mem' := fun {f g} hf hg => hc.add a b f g hf hg
  zero_mem' := hc.zero a b
  smul_mem' := fun c f hf => hc.smul a b c f hf

def post (hc : IsLinCat N Hom) (a : O) {b c : O} (f : N b →ₗ[ℂ] N c) (hf : Hom b c f) :
    homSub hc a b →ₗ[ℂ] homSub hc a c where
  toFun w := ⟨f ∘ₗ w.1, hc.comp _ _ _ _ _ w.2 hf⟩
  map_add' v w := Subtype.ext (by simp [LinearMap.comp_add])
  map_smul' c w := Subtype.ext (by simp [LinearMap.comp_smul])

theorem exists_iso_of_eq (hc : IsLinCat N Hom) {a b : O} (h : a = b) :
    ∃ (θ : N a →ₗ[ℂ] N b) (θ' : N b →ₗ[ℂ] N a), Hom a b θ ∧ Hom b a θ' ∧ θ ∘ₗ θ' = LinearMap.id ∧
      θ' ∘ₗ θ = LinearMap.id := by
  subst h
  exact ⟨LinearMap.id, LinearMap.id, hc.id a, hc.id a, rfl, rfl⟩

theorem exists_basis (hc : IsLinCat N Hom) {P : Type} [DecidableEq P] {T : P → O} (hT : IsSimpleFam Hom T)
    {κ : Type} [Fintype κ] {par : κ → P} {X : O} {io : ∀ k, N (T (par k)) →ₗ[ℂ] N X}
    {pr : ∀ k, N X →ₗ[ℂ] N (T (par k))} (hd : IsDec Hom X (fun k => T (par k)) io pr) (ν : P) :
    ∃ b : Module.Basis {k // par k = ν} ℂ (homSub hc (T ν) X),
      ∀ k, ∃ θ : N (T ν) →ₗ[ℂ] N (T (par k.1)), (b k).1 = io k.1 ∘ₗ θ := by
  classical
  have hex := fun k : {k // par k = ν} => exists_iso_of_eq hc (congrArg T k.2.symm)
  choose θ θ' hθ hθ' h1 h2 using hex
  let v : {k // par k = ν} → homSub hc (T ν) X := fun k =>
    ⟨io k.1 ∘ₗ θ k, hc.comp _ _ _ _ _ (hθ k) (hd.io_hom k.1)⟩
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := hT.1 ν
    obtain ⟨x, hx⟩ := exists_ne (0 : N (T ν))
    have h3 := congrArg (fun w : homSub hc (T ν) X => θ' i (pr i.1 (w.1 x))) hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [v, Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      map_sum, map_smul, Submodule.coe_zero, LinearMap.zero_apply, map_zero, LinearMap.comp_apply] at h3
    rw [Finset.sum_eq_single i] at h3
    · have e1 : pr i.1 (io i.1 (θ i x)) = θ i x := LinearMap.congr_fun (hd.pr_io i.1) _
      have e2 : θ' i (θ i x) = x := LinearMap.congr_fun (h2 i) _
      rw [e1, e2] at h3
      exact (smul_eq_zero.1 h3).resolve_right hx
    · intro k _ hk
      have e1 : pr i.1 (io k.1 (θ k x)) = 0 :=
        LinearMap.congr_fun (hd.pr_io_ne i.1 k.1 fun h => hk (Subtype.ext h.symm)) _
      rw [e1]; simp
    · simp
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    intro w _
    have hw : w = ∑ k, (⟨io k ∘ₗ (pr k ∘ₗ w.1), hc.comp _ _ _ _ _ (hc.comp _ _ _ _ _ w.2 (hd.pr_hom k))
        (hd.io_hom k)⟩ : homSub hc (T ν) X) := by
      apply Subtype.ext
      ext x
      have := LinearMap.congr_fun hd.sum (w.1 x)
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at this
      simp only [Submodule.coe_sum, LinearMap.sum_apply, LinearMap.comp_apply, this]
    rw [hw]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : par k = ν
    · obtain ⟨c, hc'⟩ := hT.2.1 ν (θ' ⟨k, hk⟩ ∘ₗ (pr k ∘ₗ w.1))
        (hc.comp _ _ _ _ _ (hc.comp _ _ _ _ _ w.2 (hd.pr_hom k)) (hθ' ⟨k, hk⟩))
      have : (⟨io k ∘ₗ (pr k ∘ₗ w.1), hc.comp _ _ _ _ _ (hc.comp _ _ _ _ _ w.2 (hd.pr_hom k))
        (hd.io_hom k)⟩ : homSub hc (T ν) X) = c • v ⟨k, hk⟩ := by
        apply Subtype.ext
        ext x
        have e1 : θ' ⟨k, hk⟩ (pr k (w.1 x)) = c • x := LinearMap.congr_fun hc' x
        have e2 : θ ⟨k, hk⟩ (θ' ⟨k, hk⟩ (pr k (w.1 x))) = pr k (w.1 x) := LinearMap.congr_fun (h1 _) _
        rw [e1] at e2
        show io k (pr k (w.1 x)) = c • io k (θ ⟨k, hk⟩ x)
        rw [← e2, map_smul, map_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · have h0 := hT.2.2 ν (par k) (Ne.symm hk) (pr k ∘ₗ w.1) (hc.comp _ _ _ _ _ w.2 (hd.pr_hom k))
      have : (⟨io k ∘ₗ (pr k ∘ₗ w.1), hc.comp _ _ _ _ _ (hc.comp _ _ _ _ _ w.2 (hd.pr_hom k))
        (hd.io_hom k)⟩ : homSub hc (T ν) X) = 0 := by
        apply Subtype.ext
        simp [h0]
      rw [this]
      exact Submodule.zero_mem _
  exact ⟨Module.Basis.mk hli hsp, fun k => ⟨θ k, by rw [Module.Basis.mk_apply]⟩⟩

theorem exists_trace (hc : IsLinCat N Hom) {P : Type} [DecidableEq P] {T : P → O} (hT : IsSimpleFam Hom T)
    {κ : Type} [Fintype κ] {par : κ → P} {X : O} {io : ∀ k, N (T (par k)) →ₗ[ℂ] N X}
    {pr : ∀ k, N X →ₗ[ℂ] N (T (par k))} (hd : IsDec Hom X (fun k => T (par k)) io pr) (ν : P)
    (Φ : Module.End ℂ (N X)) (a : κ → ℂ) (h : ∀ k, Φ ∘ₗ io k = a k • io k) :
    ∃ F : Module.End ℂ (homSub hc (T ν) X), (∀ w, (F w).1 = Φ ∘ₗ w.1) ∧
      LinearMap.trace ℂ _ F = ∑ k ∈ univ.filter (fun k => par k = ν), a k := by
  classical
  obtain ⟨b, hb⟩ := exists_basis hc hT hd ν
  refine ⟨b.constr ℂ fun k => a k.1 • b k, ?_, ?_⟩
  · have : (homSub hc (T ν) X).subtype ∘ₗ (b.constr ℂ fun k => a k.1 • b k) =
        (LinearMap.llcomp ℂ _ _ _ Φ) ∘ₗ (homSub hc (T ν) X).subtype := by
      refine b.ext fun k => ?_
      obtain ⟨θ, hθ⟩ := hb k
      simp only [LinearMap.comp_apply, Module.Basis.constr_basis, Submodule.subtype_apply,
        Submodule.coe_smul, LinearMap.llcomp_apply', hθ]
      rw [← LinearMap.comp_assoc, h, LinearMap.smul_comp]
    intro w
    exact LinearMap.congr_fun this w
  · rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace,
      Finset.sum_subtype (univ.filter fun k => par k = ν) (p := fun k => par k = ν) (by simp)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [LinearMap.toMatrix_apply]

theorem dec_of_gen (hc : IsLinCat N Hom) {P : Type} {T : P → O} (hT : IsSimpleFam Hom T)
    {κ : Type} [Fintype κ] {par : κ → P} {X Z : O} {io : ∀ k, N (T (par k)) →ₗ[ℂ] N X}
    {pr : ∀ k, N X →ₗ[ℂ] N (T (par k))} (hd : IsDec Hom X (fun k => T (par k)) io pr)
    {j : N Z →ₗ[ℂ] N X} {q : N X →ₗ[ℂ] N Z} (hj : Hom Z X j) (hq : Hom X Z q) (hqj : q ∘ₗ j = LinearMap.id)
    {I : Type} [Fintype I] {e : I → P} (he : Function.Injective e)
    (g : ∀ i, homSub hc (T (e i)) Z) (hg0 : ∀ i, g i ≠ 0) (hg : ∀ i w, ∃ c : ℂ, c • g i = w)
    (h0 : ∀ ν, (∀ i, e i ≠ ν) → ∀ w : homSub hc (T ν) Z, w = 0) :
    ∃ io pr, IsDec Hom Z (fun i => T (e i)) io pr := by
  classical
  let S : (N Z →ₗ[ℂ] N Z) → Prop := fun f =>
    ∃ r : ∀ i, homSub hc Z (T (e i)), ∑ i, (g i).1 ∘ₗ (r i).1 = f
  have S0 : S 0 := ⟨0, by simp⟩
  have Sadd : ∀ f f', S f → S f' → S (f + f') := by
    rintro _ _ ⟨r, rfl⟩ ⟨r', rfl⟩
    exact ⟨r + r', by simp [LinearMap.comp_add, Finset.sum_add_distrib]⟩
  have Sterm : ∀ ν (f : N (T ν) →ₗ[ℂ] N Z) (h : N Z →ₗ[ℂ] N (T ν)), Hom _ _ f → Hom _ _ h → S (f ∘ₗ h) := by
    intro ν f h hf hh
    by_cases hν : ∃ i, e i = ν
    · obtain ⟨i, rfl⟩ := hν
      obtain ⟨c, hc'⟩ := hg i ⟨f, hf⟩
      have hc'' : c • (g i).1 = f := congrArg Subtype.val hc'
      refine ⟨Pi.single i (c • ⟨h, hh⟩), ?_⟩
      rw [Finset.sum_eq_single i]
      · simp [← hc'', LinearMap.comp_smul, LinearMap.smul_comp]
      · intro i' _ hi'
        simp [Pi.single_eq_of_ne hi']
      · simp
    · push Not at hν
      have : f = 0 := congrArg Subtype.val (h0 ν hν ⟨f, hf⟩)
      rw [this, LinearMap.zero_comp]
      exact S0
  have Sid : S LinearMap.id := by
    have : (LinearMap.id : N Z →ₗ[ℂ] N Z) = ∑ k, (q ∘ₗ io k) ∘ₗ (pr k ∘ₗ j) := by
      ext x
      have e1 := LinearMap.congr_fun hd.sum (j x)
      have e2 : q (j x) = x := LinearMap.congr_fun hqj x
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at e1 ⊢
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, e1, e2]
    rw [this]
    exact Finset.sum_induction _ S Sadd S0 fun k _ =>
      Sterm _ _ _ (hc.comp _ _ _ _ _ (hd.io_hom k) hq) (hc.comp _ _ _ _ _ hj (hd.pr_hom k))
  obtain ⟨r, hr⟩ := Sid
  have hne : ∀ i i', i ≠ i' → (r i).1 ∘ₗ (g i').1 = 0 := fun i i' h =>
    hT.2.2 (e i') (e i) (fun h' => h (he h').symm) _ (hc.comp _ _ _ _ _ (g i').2 (r i).2)
  refine ⟨fun i => (g i).1, fun i => (r i).1, fun i => (g i).2, fun i => (r i).2, hr, fun i => ?_, hne⟩
  obtain ⟨c, hc'⟩ := hT.2.1 (e i) _ (hc.comp _ _ _ _ _ (g i).2 (r i).2)
  have h1 : (∑ i', (g i').1 ∘ₗ (r i').1) ∘ₗ (g i).1 = (g i).1 := by rw [hr, LinearMap.id_comp]
  have h2 : (∑ i', (g i').1 ∘ₗ (r i').1) ∘ₗ (g i).1 = c • (g i).1 := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    rw [Finset.sum_eq_single i]
    · have : (r i).1 ((g i).1 x) = c • x := LinearMap.congr_fun hc' x
      rw [this, map_smul]; rfl
    · intro i' _ hi'
      have : (r i').1 ((g i).1 x) = 0 := LinearMap.congr_fun (hne i' i hi') x
      rw [this, map_zero]
    · simp
  have h3 : (c - 1) • (g i).1 = 0 := by rw [sub_smul, one_smul, ← h2, h1, sub_self]
  have h4 : (g i).1 ≠ 0 := fun h => hg0 i (Subtype.ext h)
  have h5 : c = 1 := sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right h4)
  rw [hc', h5, one_smul]

theorem decOfTrace : DecOfTrace := by
  intro O N _ _ Hom hc P _ T hT κ _ par X Z io₁ io₂ pr₁ pr₂ hd₁ hd₂ Φ Φ₁ Φ₂ a b cs α β h₁ h₂ hΦ j q hj hq
    hqj hβ hrel I _ e he hone hzero
  have key : ∀ ν, Module.Finite ℂ (homSub hc (T ν) Z) ∧
      β * (Module.finrank ℂ (homSub hc (T ν) Z) : ℂ) =
        ∑ k ∈ univ.filter (fun k => par k = ν), (a k + b k + α - cs ν) := by
    intro ν
    obtain ⟨bs, -⟩ := exists_basis hc hT hd₁ ν
    haveI : Module.Finite ℂ (homSub hc (T ν) X) := Module.Finite.of_basis bs
    have hid : post hc (T ν) q hq ∘ₗ post hc (T ν) j hj = LinearMap.id := by
      ext w x
      exact LinearMap.congr_fun hqj (w.1 x)
    haveI hfin : Module.Finite ℂ (homSub hc (T ν) Z) :=
      Module.Finite.of_surjective (post hc (T ν) q hq) fun w =>
        ⟨post hc (T ν) j hj w, LinearMap.congr_fun hid w⟩
    refine ⟨hfin, ?_⟩
    obtain ⟨F₁, hF₁, t₁⟩ := exists_trace hc hT hd₁ ν Φ₁ a h₁
    obtain ⟨F₂, hF₂, t₂⟩ := exists_trace hc hT hd₂ ν Φ₂ b h₂
    obtain ⟨F₃, hF₃, t₃⟩ := exists_trace hc hT hd₁ ν ((α - cs ν) • LinearMap.id) (fun _ => α - cs ν)
      (fun k => by ext x; simp)
    have hA : β • (post hc (T ν) j hj ∘ₗ post hc (T ν) q hq) = F₁ + F₂ + F₃ := by
      ext w x
      have e1 : Φ (w.1 x) = cs ν • w.1 x := LinearMap.congr_fun (hΦ ν w.1 w.2) x
      rw [hrel] at e1
      simp only [LinearMap.add_apply, Submodule.coe_add, hF₁, hF₂, hF₃, LinearMap.comp_apply,
        LinearMap.smul_apply, LinearMap.id_apply, LinearMap.sub_apply] at e1 ⊢
      show β • j (q (w.1 x)) = _
      rw [sub_smul, ← e1]
      abel
    have ht := congrArg (LinearMap.trace ℂ _) hA
    rw [map_smul, LinearMap.trace_comp_comm', hid, LinearMap.trace_id, map_add (f := _), map_add (f := _), t₁, t₂, t₃,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, smul_eq_mul] at ht
    rw [ht]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hgen : ∀ i, ∃ g : homSub hc (T (e i)) Z, g ≠ 0 ∧ ∀ w, ∃ c : ℂ, c • g = w := by
    intro i
    have h := (key (e i)).2
    rw [hone i] at h
    have h' : (Module.finrank ℂ (homSub hc (T (e i)) Z) : ℂ) = 1 :=
      mul_left_cancel₀ hβ (by rw [h, mul_one])
    exact finrank_eq_one_iff'.1 (by exact_mod_cast h')
  choose g hg0 hg using hgen
  refine dec_of_gen hc hT hd₁ hj hq hqj he g hg0 hg fun ν hν w => ?_
  obtain ⟨hfin, h⟩ := key ν
  rw [hzero ν hν] at h
  have h' : Module.finrank ℂ (homSub hc (T ν) Z) = 0 := by
    exact_mod_cast (mul_eq_zero.1 h).resolve_left hβ
  exact finrank_zero_iff_forall_zero.1 h' w

end GlobalTheory.CompanionTheory.ZuckDecOfTrace
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTraceStatement
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DecompositionOfTrace : DecOfTrace := by
  first | exact @GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace | exact GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace | (intros; apply GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace <;> assumption)
end
end
