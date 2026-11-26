module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AemeasurableCxPosDensity
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietySecond
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetOnlyNull
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartDensityIntegrable
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosPartLocal

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FibreDensityIndependentProjection
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FibreDensityIndependentProjection
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxPosLocal

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp
open GroundTheory.Heights₂.Heights.PtsPosPartLocal
open ReciprocityTheory.AnForm.R (conePts)

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}

def BlockNonzero (S : Set ((Σ k, ι k) → ℂ)) : Prop :=
  ∀ z ∈ S, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0

def ScaleStable (S : Set ((Σ k, ι k) → ℂ)) : Prop :=
  ∀ (c : K → ℂ), (∀ k, c k ≠ 0) → ∀ z ∈ S, (fun p => c p.1 * z p) ∈ S

variable {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}

theorem setSheet_analyticAt {S : Set ((Σ k, ι k) → ℂ)} {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (hc : IsSetSheet S Ψ y w γ) : AnalyticAt ℂ γ y := by
  obtain ⟨V, hVs, hV, hy⟩ := mem_nhds_iff.mp hc.2
  exact analyticOnNhd_of_diffOn hV (fun y' hy' => (hVs hy').1) y hy

theorem exists_local_set {S : Set ((Σ k, ι k) → ℂ)} {w₀ : ((k : K) → ι k) → ℂ} (h : cxSimple S Ψ w₀) :
    ∃ (y₀ : Fin e → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (U : Set (Fin e → ℂ))
      (N : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))),
      IsOpen U ∧ IsOpen N ∧ (y₀, w₀) ∈ N ∧ segre (γ y₀) = w₀ ∧
      (∀ y ∈ U, DifferentiableAt ℂ γ y ∧ γ y ∈ S ∧ Ψ (segre (γ y)) = Fin.cons 1 y) ∧
      ∀ q ∈ N, q.1 ∈ U ∧ (q.2 ∈ setFibre S Ψ q.1 → q.2 = segre (γ q.1)) := by
  obtain ⟨y₀, γ, hsh, hev⟩ := h
  obtain ⟨U, hUs, hU, hy₀⟩ := mem_nhds_iff.mp hsh.2
  obtain ⟨N₁, hN₁s, hN₁, hq₁⟩ := mem_nhds_iff.mp hev
  exact ⟨y₀, γ, U, N₁ ∩ U ×ˢ Set.univ, hU, hN₁.inter (hU.prod isOpen_univ), ⟨hq₁, hy₀, trivial⟩,
    hsh.1, fun y hy => hUs hy, fun q hq => ⟨hq.2.1, hN₁s hq.1⟩⟩

theorem nrm_mem_setFibre {S : Set ((Σ k, ι k) → ℂ)} (hSs : ScaleStable S) (k0 : K)
    {z' : (Σ k, ι k) → ℂ} (hz' : z' ∈ S) (h0 : Ψ (segre z') 0 ≠ 0) :
    nrm Ψ (segre z') ∈ setFibre S Ψ (crd Ψ (segre z')) := by
  classical
  set c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre z') 0)⁻¹ with hcdef
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [hcdef, h0]
    · simp [hcdef, Function.update_of_ne hk]
  have hprod : ∏ k, c k = (Ψ (segre z') 0)⁻¹ := by
    simp [hcdef, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * z' p, hSs c hc _ hz', ?_, map_nrm h0⟩
  rw [segre_smul, hprod]
  rfl

theorem setSheetDensity_eq {S : Set ((Σ k, ι k) → ℂ)} (hS0 : BlockNonzero S) {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {G : ((Σ k, ι k) → ℂ) → ℝ}
    (hG : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → G (fun p => c p.1 * z p) = G z)
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {U : Set (Fin e → ℂ)}
    {N : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))} (hU : IsOpen U)
    (hγ : ∀ y ∈ U, DifferentiableAt ℂ γ y ∧ γ y ∈ S ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    (hN : IsOpen N) (hNp : ∀ q ∈ N, q.1 ∈ U ∧ (q.2 ∈ setFibre S Ψ q.1 → q.2 = segre (γ q.1)))
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} (hq : (y, w) ∈ N) (hw : w ∈ setFibre S Ψ y) :
    setSheetDensity S Ψ (pot L) G y w = G (γ y) * maDensity (fun j y' => pot L j (γ y')) y := by
  obtain ⟨hyU, hw'⟩ := hNp _ hq
  have hw1 : w = segre (γ y) := hw' hw
  have hsh : IsSetSheet S Ψ y w γ := ⟨hw1.symm, Filter.eventually_of_mem (hU.mem_nhds hyU) hγ⟩
  have hex : ∃ γ', IsSetSheet S Ψ y w γ' := ⟨γ, hsh⟩
  have han : AnalyticOnNhd ℂ γ U := analyticOnNhd_of_diffOn hU fun y hy => (hγ y hy).1
  unfold setSheetDensity
  rw [dite_eq_left hex]
  have hc := hex.choose_spec
  set γc := hex.choose
  have hcont : ContinuousAt (fun y' => (y', segre (γc y'))) y :=
    continuousAt_id.prodMk (continuous_segre.continuousAt.comp hc.2.self_of_nhds.1.continuousAt)
  have hN' : ∀ᶠ y' in 𝓝 y, (y', segre (γc y')) ∈ N :=
    hcont.eventually (hN.mem_nhds (by show (y, segre (γc y)) ∈ N; rw [hc.1]; exact hq))
  have hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γc y') := by
    filter_upwards [hN', hc.2] with y' h1 h2
    exact ((hNp _ h1).2 ⟨γc y', h2.2.1, rfl, h2.2.2⟩).symm
  have hblk : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := hS0 _ (hγ y hyU).2.1
  rw [apply_eq_of_segre_eq hG hblk (hc.1.trans hw1).symm,
    maDensity_eq_of_segre hL (han y hyU) (setSheet_analyticAt hc) hblk hseg]

theorem cxPosDens_eq {S : Set ((Σ k, ι k) → ℂ)} (hS0 : BlockNonzero S) {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {g : ((Σ k, ι k) → ℂ) → ℝ}
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z)
    {E : Set ((Σ k, ι k) → ℂ)}
    (hE : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z p) ∈ E ↔ z ∈ E))
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {U : Set (Fin e → ℂ)}
    {N : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))} (hU : IsOpen U)
    (hγ : ∀ y ∈ U, DifferentiableAt ℂ γ y ∧ γ y ∈ S ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    (hN : IsOpen N) (hNp : ∀ q ∈ N, q.1 ∈ U ∧ (q.2 ∈ setFibre S Ψ q.1 → q.2 = segre (γ q.1)))
    (hEN : ∀ z' ∈ E, Ψ (segre z') 0 ≠ 0 → (crd Ψ (segre z'), nrm Ψ (segre z')) ∈ N)
    (y : Fin e → ℂ) :
    cxPosDens S Ψ (pot L) (E.indicator g) y = (U ∩ γ ⁻¹' E).indicator
      (fun y => max (g (γ y) * maDensity (fun j y' => pot L j (γ y')) y) 0) y := by
  classical
  have hEg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      E.indicator g (fun p => c p.1 * z p) = E.indicator g z := by
    intro c z hc
    by_cases hz : z ∈ E
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hE c z hc).2 hz), hg c z hc]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz ((hE c z hc).1 h))]
  have hmemE : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      ((fun p => c p.1 * z p) ∈ E) = (z ∈ E) := fun c z hc => propext (hE c z hc)

  have hnz : ∀ w ∈ setFibre S Ψ y, setSheetDensity S Ψ (pot L) (E.indicator g) y w ≠ 0 →
      (y, w) ∈ N ∧ γ y ∈ E := by
    intro w hw hne
    obtain ⟨-, -, -, hΨw⟩ := hw
    unfold setSheetDensity at hne
    split_ifs at hne with h
    · have hc := h.choose_spec
      have hcE : h.choose y ∈ E := by
        by_contra hn
        exact hne (by rw [Set.indicator_of_notMem hn, zero_mul])
      have hw0 : Ψ (segre (h.choose y)) 0 ≠ 0 := by
        rw [hc.1, hΨw]; simp
      have hqN := hEN _ hcE hw0
      rw [hc.1, crd_of_eq hΨw, nrm_of_eq hΨw] at hqN
      refine ⟨hqN, ?_⟩
      obtain ⟨hyU, hw1⟩ := hNp _ hqN
      have hseg : segre (h.choose y) = segre (γ y) := hc.1.trans (hw1 ⟨h.choose y, hc.2.self_of_nhds.2.1, hc.1, hΨw⟩)
      have := apply_eq_of_segre_eq hmemE (hS0 _ hc.2.self_of_nhds.2.1) hseg
      rw [this]
      exact hcE
    · exact absurd rfl hne
  unfold cxPosDens
  by_cases hy : y ∈ U ∩ γ ⁻¹' E
  · rw [Set.indicator_of_mem hy]
    have hyU := hy.1
    have hΨ1 : Ψ (segre (γ y)) = Fin.cons 1 y := (hγ y hyU).2.2
    have hfib : segre (γ y) ∈ setFibre S Ψ y := ⟨γ y, (hγ y hyU).2.1, rfl, hΨ1⟩
    have hqN : (y, segre (γ y)) ∈ N := by
      have h := hEN _ hy.2 (by rw [hΨ1]; simp)
      rwa [crd_of_eq hΨ1, nrm_of_eq hΨ1] at h
    rw [finsum_eq_single _ (segre (γ y)) ?_, finsum_eq_if, if_pos hfib,
      setSheetDensity_eq hS0 hL hEg hU hγ hN hNp hqN hfib, Set.indicator_of_mem (show γ y ∈ E from hy.2)]
    intro w hne
    rw [finsum_eq_if]
    split_ifs with hw
    · by_cases h0 : setSheetDensity S Ψ (pot L) (E.indicator g) y w = 0
      · rw [h0, max_self]
      · exact absurd ((hNp _ (hnz w hw h0).1).2 hw) hne
    · rfl
  · rw [Set.indicator_of_notMem hy]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun w hw => ?_
    by_cases h0 : setSheetDensity S Ψ (pot L) (E.indicator g) y w = 0
    · rw [h0, max_self]
    · obtain ⟨hqN, hγE⟩ := hnz w hw h0
      exact absurd ⟨(hNp _ hqN).1, hγE⟩ hy

theorem posPart_local_set {S : Set ((Σ k, ι k) → ℂ)} (hS0 : BlockNonzero S) (hSs : ScaleStable S) (k0 : K)
    {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → HermLine ι}
    {g : ((Σ k, ι k) → ℂ) → ℝ} {z : (Σ k, ι k) → ℂ} (hL : ∀ j, IsSmoothHerm (L j))
    (hg : ∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z' p) = g z')
    (hs : cxSimple S Ψ ((Ψ (segre z) 0)⁻¹ • segre z))
    (hs' : cxSimple S Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z)) :
    ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ z ∈ W ∧
      (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ W ↔ z' ∈ W)) ∧
      ∀ E : Set ((Σ k, ι k) → ℂ), MeasurableSet E →
        (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ E ↔ z' ∈ E)) →
        E ⊆ W →
          ∫⁻ y, ENNReal.ofReal (cxPosDens S Ψ (pot L) (E.indicator g) y) =
            ∫⁻ y, ENNReal.ofReal (cxPosDens S Ψ' (pot L) (E.indicator g) y) := by
  obtain ⟨y₀, γ₀, U, N, hU, hN, hq₀, hseg₀, hγ₀, hNp⟩ := exists_local_set hs
  obtain ⟨y₀', γ₀', U', N', hU', hN', hq₀', hseg₀', hγ₀', hNp'⟩ := exists_local_set hs'

  have hz0 : Ψ (segre z) 0 ≠ 0 := by
    intro h0
    have h := congrFun (hγ₀ y₀ (hNp _ hq₀).1).2.2 0
    rw [hseg₀, h0, inv_zero, zero_smul, map_zero] at h
    simp at h
  have hz0' : Ψ' (segre z) 0 ≠ 0 := by
    intro h0
    have h := congrFun (hγ₀' y₀' (hNp' _ hq₀').1).2.2 0
    rw [hseg₀', h0, inv_zero, zero_smul, map_zero] at h
    simp at h
  have hN0 : (crd Ψ (segre z), nrm Ψ (segre z)) ∈ N := by
    have h1 : Ψ (nrm Ψ (segre z)) = Fin.cons 1 y₀ := by
      rw [← (hγ₀ y₀ (hNp _ hq₀).1).2.2, hseg₀]
      rfl
    have h2 : crd Ψ (segre z) = y₀ := by
      funext i
      simp [crd, h1]
    rw [h2]
    exact hq₀
  have hN0' : (crd Ψ' (segre z), nrm Ψ' (segre z)) ∈ N' := by
    have h1 : Ψ' (nrm Ψ' (segre z)) = Fin.cons 1 y₀' := by
      rw [← (hγ₀' y₀' (hNp' _ hq₀').1).2.2, hseg₀']
      rfl
    have h2 : crd Ψ' (segre z) = y₀' := by
      funext i
      simp [crd, h1]
    rw [h2]
    exact hq₀'

  set WS : Set (((k : K) → ι k) → ℂ) := {w | Ψ w 0 ≠ 0 ∧ Ψ' w 0 ≠ 0 ∧ (crd Ψ w, nrm Ψ w) ∈ N ∧
    (crd Ψ' w, nrm Ψ' w) ∈ N'} with hWSdef
  have hWS : IsOpen WS := by
    refine isOpen_iff_mem_nhds.mpr fun w hw => ?_
    have c0 : ContinuousAt (fun w => Ψ w 0) w := (differentiableAt_coord w 0).continuousAt
    have c0' : ContinuousAt (fun w => Ψ' w 0) w := (differentiableAt_coord w 0).continuousAt
    filter_upwards [c0.eventually_ne hw.1, c0'.eventually_ne hw.2.1,
      ((continuousAt_crd hw.1).prodMk (continuousAt_nrm hw.1)).eventually (hN.mem_nhds hw.2.2.1),
      ((continuousAt_crd hw.2.1).prodMk (continuousAt_nrm hw.2.1)).eventually (hN'.mem_nhds hw.2.2.2)]
      with v h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hWSs : ∀ t : ℂ, t ≠ 0 → ∀ w, t • w ∈ WS ↔ w ∈ WS := by
    intro t ht w
    have e1 : ∀ Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), Φ (t • w) 0 ≠ 0 ↔ Φ w 0 ≠ 0 :=
      fun Φ => by simp [map_smul, ht]
    simp only [hWSdef, Set.mem_setOf_eq, e1, crd_smul ht, nrm_smul ht]
  refine ⟨segre ⁻¹' WS, hWS.preimage continuous_segre, ⟨hz0, hz0', hN0, hN0'⟩,
    fun c z' hc => ?_, fun E _ hE hEW => ?_⟩
  · show segre (fun p => c p.1 * z' p) ∈ WS ↔ segre z' ∈ WS
    rw [segre_smul]
    exact hWSs _ (Finset.prod_ne_zero_iff.mpr fun k _ => hc k) _

  have hl : ∀ y, cxPosDens S Ψ (pot L) (E.indicator g) y = (U ∩ γ₀ ⁻¹' E).indicator
      (fun y => max (g (γ₀ y) * maDensity (fun j y' => pot L j (γ₀ y')) y) 0) y :=
    cxPosDens_eq hS0 hL hg hE hU hγ₀ hN hNp fun z' hz' _ => (hEW hz').2.2.1
  have hl' : ∀ y, cxPosDens S Ψ' (pot L) (E.indicator g) y = (U' ∩ γ₀' ⁻¹' E).indicator
      (fun y => max (g (γ₀' y) * maDensity (fun j y' => pot L j (γ₀' y')) y) 0) y :=
    cxPosDens_eq hS0 hL hg hE hU' hγ₀' hN' hNp' fun z' hz' _ => (hEW hz').2.2.2
  simp_rw [hl, hl']

  have hγ₀an : AnalyticOnNhd ℂ γ₀ U := analyticOnNhd_of_diffOn hU fun y hy => (hγ₀ y hy).1
  have hγ₀'an : AnalyticOnNhd ℂ γ₀' U' := analyticOnNhd_of_diffOn hU' fun y hy => (hγ₀' y hy).1
  set Φ : (Fin e → ℂ) → Fin (e + 1) → ℂ := fun y => Ψ (segre (γ₀' y)) with hΦdef
  have hΦan : AnalyticOnNhd ℂ Φ U' := analyticOnNhd_of_diffOn hU' fun y hy =>
    (differentiable_map (Ψ := Ψ) _).comp y (segre_differentiableAt (hγ₀' y hy).1)
  set O' := U' ∩ γ₀' ⁻¹' (segre ⁻¹' WS) with hO'def
  have hO' : IsOpen O' := ContinuousOn.isOpen_inter_preimage
    (fun y hy => (hγ₀' y hy).1.continuousAt.continuousWithinAt) hU' (hWS.preimage continuous_segre)
  set τ : (Fin e → ℂ) → Fin e → ℂ := fun y => crd Ψ (segre (γ₀' y)) with hτdef
  have hτeq : τ = fun y (i : Fin e) => (Φ y 0)⁻¹ * Φ y i.succ := funext fun y => crd_eq _
  have hτan : AnalyticOnNhd ℂ τ O' := fun y hy => by
    rw [hτeq]
    exact analyticAt_pi_iff.mpr fun i =>
      (AnalyticAt.inv (f := fun y => Φ y 0) (analyticAt_pi_iff.mp (hΦan y hy.1) 0) hy.2.1).mul
        (analyticAt_pi_iff.mp (hΦan y hy.1) i.succ)
  have hτU : ∀ y ∈ O', τ y ∈ U ∧ segre (γ₀ (τ y)) = nrm Ψ (segre (γ₀' y)) := fun y hy => by
    have hq : (τ y, nrm Ψ (segre (γ₀' y))) ∈ N := hy.2.2.2.1
    obtain ⟨h1, h2⟩ := hNp _ hq
    exact ⟨h1, (h2 (nrm_mem_setFibre hSs k0 (hγ₀' y hy.1).2.1 hy.2.1)).symm⟩

  set c : (Fin e → ℂ) → K → ℂ := fun y => Function.update (fun _ => (1 : ℂ)) k0 (Φ y 0)⁻¹ with hcdef
  have hc_ne : ∀ y, Φ y 0 ≠ 0 → ∀ k, c y k ≠ 0 := by
    intro y h k
    by_cases hk : k = k0
    · subst hk; simp [hcdef, h]
    · simp [hcdef, Function.update_of_ne hk]
  have hprod : ∀ y, ∏ k, c y k = (Φ y 0)⁻¹ := fun y => by
    simp [hcdef, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  set γt : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y => bsmul (c y) (γ₀' y) with hγtdef
  have hγtseg : ∀ y, segre (γt y) = nrm Ψ (segre (γ₀' y)) := fun y => by
    show segre (fun p => c y p.1 * γ₀' y p) = _
    rw [segre_smul, hprod]
    rfl

  have hcmp : ∀ y ∈ O', (γ₀ (τ y) ∈ E ↔ γ₀' y ∈ E) ∧ g (γ₀ (τ y)) = g (γ₀' y) ∧
      maDensity (fun j y' => pot L j (γ₀' y')) y =
        maDensity (fun j y' => pot L j (γ₀ y')) (τ y) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ y).det := by
    intro y hy
    obtain ⟨hτy, hsy⟩ := hτU y hy
    have hblk : ∀ k, ∃ i, γ₀ (τ y) ⟨k, i⟩ ≠ 0 := hS0 _ (hγ₀ _ hτy).2.1
    have hseg : segre (γ₀ (τ y)) = segre (γt y) := hsy.trans (hγtseg y).symm
    have hy0 : Φ y 0 ≠ 0 := hy.2.1
    have hmemE : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
        ((fun p => c p.1 * z p) ∈ E) = (z ∈ E) := fun c z hc => propext (hE c z hc)
    have hE1 : (γt y ∈ E) = (γ₀ (τ y) ∈ E) := apply_eq_of_segre_eq hmemE hblk hseg
    have hE2 : (γt y ∈ E) = (γ₀' y ∈ E) := hmemE (c y) (γ₀' y) (hc_ne y hy0)
    have hg1 : g (γt y) = g (γ₀ (τ y)) := apply_eq_of_segre_eq hg hblk hseg
    have hg2 : g (γt y) = g (γ₀' y) := hg (c y) (γ₀' y) (hc_ne y hy0)
    refine ⟨by rw [← hE1, hE2], by rw [← hg1, hg2], ?_⟩
    have hca : ∀ k, AnalyticAt ℂ (fun y' => c y' k) y := fun k => by
      by_cases hk : k = k0
      · subst hk
        simp only [hcdef, Function.update_self]
        exact AnalyticAt.inv (f := fun y => Φ y 0) (analyticAt_pi_iff.mp (hΦan y hy.1) 0) hy0
      · simp only [hcdef, Function.update_of_ne hk]
        exact analyticAt_const
    have hγ'a : AnalyticAt ℂ γ₀' y := hγ₀'an y hy.1
    have hγta : AnalyticAt ℂ γt y :=
      analyticAt_pi_iff.mpr fun p => (hca p.1).mul (analyticAt_pi_iff.mp hγ'a p)
    have hτa : AnalyticAt ℂ τ y := hτan y hy
    have hγτa : AnalyticAt ℂ (fun y' => γ₀ (τ y')) y := (hγ₀an _ hτy).comp hτa
    have h1 : maDensity (fun j y' => pot L j (γt y')) y = maDensity (fun j y' => pot L j (γ₀' y')) y :=
      maDensity_bsmul (c := fun k y' => c y' k) hL hγ'a (hS0 _ (hγ₀' y hy.1).2.1) hca (fun k => hc_ne y hy0 k)
        (Eventually.of_forall fun y' => rfl)
    have h2 : maDensity (fun j y' => pot L j (γt y')) y =
        maDensity (fun j y' => pot L j (γ₀ (τ y'))) y :=
      maDensity_eq_of_segre hL hγτa hγta hblk (by
        filter_upwards [hO'.mem_nhds hy] with y' hy'
        exact (hτU y' hy').2.trans (hγtseg y').symm)
    have h3 : maDensity (fun j y' => pot L j (γ₀ (τ y'))) y =
        maDensity (fun j y' => pot L j (γ₀ y')) (τ y) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ y).det :=
      ReciprocityTheory.AnForm.A.maDens_comp (fun j y' => pot L j (γ₀ y')) τ y hτa fun j =>
        pot_contDiffAt (hL j) (hγ₀an _ hτy) hblk
    rw [← h1, h2, h3]

  have hback : ∀ y ∈ O', y = crd Ψ' (nrm Ψ (segre (γ₀' y))) := by
    intro y hy
    have h1 : crd Ψ' (segre (γ₀' y)) = y := crd_of_eq (hγ₀' y hy.1).2.2
    have h2 := crd_smul (Ψ := Ψ') hy.2.1 (nrm Ψ (segre (γ₀' y)))
    rw [← eq_smul_nrm hy.2.1, h1] at h2
    exact h2
  have hτinj : Set.InjOn τ O' := by
    intro y₁ h₁ y₂ h₂ h
    have e₁ := (hτU y₁ h₁).2
    have e₂ := (hτU y₂ h₂).2
    rw [h] at e₁
    rw [hback y₁ h₁, hback y₂ h₂, ← e₁, ← e₂]

  have hsupp : ∀ y ∈ U ∩ γ₀ ⁻¹' E, y ∈ τ '' O' := by
    intro y hy
    have hz₁ := hγ₀ y hy.1
    have hw₁ : segre (γ₀ y) ∈ WS := hEW hy.2
    have hfib := nrm_mem_setFibre (Ψ := Ψ') hSs k0 hz₁.2.1 hw₁.2.1
    obtain ⟨hy'U, hy'seg⟩ := hNp' _ hw₁.2.2.2
    have hseg' := hy'seg hfib
    refine ⟨crd Ψ' (segre (γ₀ y)), ⟨hy'U, ?_⟩, ?_⟩
    · show segre (γ₀' (crd Ψ' (segre (γ₀ y)))) ∈ WS
      rw [← hseg']
      exact (hWSs _ (inv_ne_zero hw₁.2.1) _).2 hw₁
    · show crd Ψ (segre (γ₀' (crd Ψ' (segre (γ₀ y))))) = y
      rw [← hseg']
      show crd Ψ ((Ψ' (segre (γ₀ y)) 0)⁻¹ • segre (γ₀ y)) = y
      rw [crd_smul (inv_ne_zero hw₁.2.1)]
      exact crd_of_eq hz₁.2.2
  calc _ = ∫⁻ y in τ '' O', ENNReal.ofReal ((U ∩ γ₀ ⁻¹' E).indicator
          (fun y => max (g (γ₀ y) * maDensity (fun j y' => pot L j (γ₀ y')) y) 0) y) := by
        refine (setLIntegral_eq_of_support_subset fun y hy => hsupp y ?_).symm
        by_contra h
        exact hy (by simp [Set.indicator_of_notMem h])
    _ = ∫⁻ y in O', ENNReal.ofReal (Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ y).det) *
          ENNReal.ofReal ((U ∩ γ₀ ⁻¹' E).indicator
            (fun y => max (g (γ₀ y) * maDensity (fun j y' => pot L j (γ₀ y')) y) 0) (τ y)) :=
        ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul τ O' hO' hτan hτinj _
    _ = ∫⁻ y in O', ENNReal.ofReal ((U' ∩ γ₀' ⁻¹' E).indicator
          (fun y => max (g (γ₀' y) * maDensity (fun j y' => pot L j (γ₀' y')) y) 0) y) := by
        refine setLIntegral_congr_fun hO'.measurableSet fun y hy => ?_
        obtain ⟨hE', hg', hma⟩ := hcmp y hy
        by_cases hyE : γ₀' y ∈ E
        · rw [Set.indicator_of_mem (show τ y ∈ U ∩ γ₀ ⁻¹' E from ⟨(hτU y hy).1, hE'.2 hyE⟩),
            Set.indicator_of_mem (show y ∈ U' ∩ γ₀' ⁻¹' E from ⟨hy.1, hyE⟩)]
          rw [hg', hma, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm,
            max_mul_of_nonneg _ _ (Complex.normSq_nonneg _), zero_mul, mul_assoc]
        · rw [Set.indicator_of_notMem (show τ y ∉ U ∩ γ₀ ⁻¹' E from fun hm => hyE (hE'.1 hm.2)),
            Set.indicator_of_notMem (show y ∉ U' ∩ γ₀' ⁻¹' E from fun hm => hyE hm.2)]
          simp
    _ = _ := by
        refine setLIntegral_eq_of_support_subset fun y hy => ?_
        have hyE : y ∈ U' ∩ γ₀' ⁻¹' E := by
          by_contra h
          exact hy (by simp [Set.indicator_of_notMem h])
        exact ⟨hyE.1, hEW hyE.2⟩

theorem cxPosPart_local : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ) (z : (Σ k, ι k) → ℂ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → IsSetGoodProj (conePts Q) Ψ' →
    (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z' p) = g z') →
    z ∈ conePts Q → cxSimple (conePts Q) Ψ ((Ψ (segre z) 0)⁻¹ • segre z) →
    cxSimple (conePts Q) Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z) →
      ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ z ∈ W ∧
        (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ W ↔ z' ∈ W)) ∧
        ∀ E : Set ((Σ k, ι k) → ℂ), MeasurableSet E →
          (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ E ↔ z' ∈ E)) →
          E ⊆ W →
            ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot L) (E.indicator g) y) =
              ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ' (pot L) (E.indicator g) y) := by
  intro K _ ι _ Q e Ψ Ψ' L g z hQ _ _ hL _ hg _ hs hs'
  classical
  obtain ⟨k0⟩ := hQ.1
  exact posPart_local_set (S := conePts Q) (fun _ hz => hz.1)
    (fun c hc z' hz' => GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FibSum.bsmul_mem_conePts hQ.2.1.2.1 hc hz') k0 hL hg hs hs'

end GlobalTheory.CompanionTheory.Ar.Pub.CxPosLocal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FibreDensityIndependentProjectionStatement
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_density_independent_projection : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ) (z : (Σ k, ι k) → ℂ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → IsSetGoodProj (conePts Q) Ψ' →
    (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z' p) = g z') →
    z ∈ conePts Q → cxSimple (conePts Q) Ψ ((Ψ (segre z) 0)⁻¹ • segre z) →
    cxSimple (conePts Q) Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z) →
      ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ z ∈ W ∧
        (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ W ↔ z' ∈ W)) ∧
        ∀ E : Set ((Σ k, ι k) → ℂ), MeasurableSet E →
          (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ E ↔ z' ∈ E)) →
          E ⊆ W →
            ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot L) (E.indicator g) y) =
              ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ' (pot L) (E.indicator g) y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxPosLocal.cxPosPart_local | exact GlobalTheory.CompanionTheory.Ar.Pub.CxPosLocal.cxPosPart_local | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxPosLocal.cxPosPart_local <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeNonsimpleFibresEqZero
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeNonsimpleFibresEqZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxOnly

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GroundTheory.Heights₂.Heights.PtsSheetOnlyNull (ratio inv_smul_eq_cons ratio_smul_cons segre_scaleBlock
  differentiableAt_proj_segre differentiableAt_ratio swapProj swapProj_apply
  not_injective_of_coord_eventually_const)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}

theorem mem_conePts (Q : Ideal (MRingOver ℂ ι)) (hQ : IsMultiHomogIdeal Q) (k0 : K) {c : ℂ}
    (hc : c ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) : scaleBlock k0 c z ∈ conePts Q := by
  refine ⟨fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, mul_ne_zero ?_ hi⟩
    split_ifs <;> simp [hc]
  · exact ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hQ (fun k => if k = k0 then c else 1) z hz.2

theorem smul_mem_fibre {Q : Ideal (MRingOver ℂ ι)} (hQh : IsMultiHomogIdeal Q) [Nonempty K] {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ conePts Q) (Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (h0 : Ψ' (segre z) 0 ≠ 0) :
    (Ψ' (segre z) 0)⁻¹ • segre z ∈ setFibre (conePts Q) Ψ' (ratio (Ψ' (segre z))) := by
  obtain ⟨k0⟩ := ‹Nonempty K›
  refine ⟨scaleBlock k0 (Ψ' (segre z) 0)⁻¹ z, mem_conePts Q hQh k0 (inv_ne_zero h0) hz, segre_scaleBlock _ _ _, ?_⟩
  rw [map_smul]
  exact inv_smul_eq_cons _ h0

theorem isGoodProj_swapProj {Q : Ideal (MRingOver ℂ ι)} {Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hΨ' : IsSetGoodProj (conePts Q) Ψ') (j : Fin (e + 1)) : IsSetGoodProj (conePts Q) (swapProj j Ψ') := by
  intro z hz h
  apply hΨ' z hz
  funext i
  have := congrFun h (Equiv.swap 0 j i)
  simpa [swapProj_apply] using this

theorem exists_injective (hC : GroundTheory.Heights₂.Heights.CriticalFibreInfinite.Statement) {Q : Ideal (MRingOver ℂ ι)} (hP : IsCxVar Q e)
    {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ' : IsSetGoodProj (conePts Q) Ψ')
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {V : Set (Fin e → ℂ)} (hV : IsOpen V) (hVne : V.Nonempty)
    (hγ : ∀ y ∈ V, DifferentiableAt ℂ γ y ∧ γ y ∈ conePts Q ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    (h0 : ∀ y ∈ V, Ψ' (segre (γ y)) 0 ≠ 0) :
    ∃ y ∈ V, Function.Injective (fderiv ℂ (fun y' => ratio (Ψ' (segre (γ y')))) y) := by
  by_contra hall
  push Not at hall
  have : Nonempty K := hP.1
  obtain ⟨t, ht⟩ := hC e e V (fun y' => ratio (Ψ' (segre (γ y')))) hV hVne
    (fun y hy => (differentiableAt_ratio Ψ' (hγ y hy).1 (h0 y hy)).differentiableWithinAt) hall
  refine (GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite K ι Q e Ψ' hP hΨ' t).not_infinite ?_
  have hinj : Set.InjOn (fun y => (Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y))
      {y | y ∈ V ∧ ratio (Ψ' (segre (γ y))) = t} := by
    rintro y1 ⟨hy1, -⟩ y2 ⟨hy2, -⟩ h
    have h' := congrArg Ψ h
    simp only [map_smul, (hγ y1 hy1).2.2, (hγ y2 hy2).2.2] at h'
    have e0 := congrFun h' 0
    simp only [Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one] at e0
    funext i
    have ei := congrFun h' i.succ
    simp only [Pi.smul_apply, Fin.cons_succ, smul_eq_mul] at ei
    rw [e0] at ei
    exact mul_left_cancel₀ (inv_ne_zero (h0 y2 hy2)) ei
  refine (Set.Infinite.image hinj ht).mono ?_
  rintro _ ⟨y, ⟨hy, hty⟩, rfl⟩
  have := smul_mem_fibre hP.2.1.2.1 (hγ y hy).2.1 Ψ' (h0 y hy)
  rwa [hty] at this

theorem exists_proj_ne_zero (hC : GroundTheory.Heights₂.Heights.CriticalFibreInfinite.Statement) {Q : Ideal (MRingOver ℂ ι)}
    (hP : IsCxVar Q e) {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ' : IsSetGoodProj (conePts Q) Ψ')
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {V : Set (Fin e → ℂ)} (hV : IsOpen V)
    (hγ : ∀ y ∈ V, DifferentiableAt ℂ γ y ∧ γ y ∈ conePts Q ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    {y : Fin e → ℂ} (hy : y ∈ V) : ∃ y' ∈ V, Ψ' (segre (γ y')) 0 ≠ 0 := by
  by_contra hall
  push Not at hall
  have hne : Ψ' (segre (γ y)) ≠ 0 := hΨ' _ (hγ y hy).2.1
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hj (hall y hy)
  have hcont : ContinuousOn (fun y' => Ψ' (segre (γ y')) j) V := fun y' hy' =>
    (differentiableAt_pi.1 (differentiableAt_proj_segre Ψ' (hγ y' hy').1) j).continuousAt.continuousWithinAt
  have hV'o : IsOpen (V ∩ (fun y' => Ψ' (segre (γ y')) j) ⁻¹' {0}ᶜ) :=
    hcont.isOpen_inter_preimage hV isOpen_compl_singleton
  have h0' : ∀ y' ∈ V ∩ (fun y' => Ψ' (segre (γ y')) j) ⁻¹' {0}ᶜ, swapProj j Ψ' (segre (γ y')) 0 ≠ 0 := by
    intro y' hy'
    simpa [swapProj_apply] using hy'.2
  obtain ⟨y1, hy1, hinj⟩ := exists_injective hC hP (isGoodProj_swapProj hΨ' j) hV'o ⟨y, hy, hj⟩
    (fun y' hy' => hγ y' hy'.1) h0'
  refine not_injective_of_coord_eventually_const (j.pred hj0) 0
    (differentiableAt_ratio _ (hγ y1 hy1.1).1 (h0' y1 hy1)) ?_ hinj
  filter_upwards [hV'o.mem_nhds hy1] with y' hy'
  simp [ratio, swapProj_apply, hall y' hy'.1]

theorem isSimpleSheetPt_of_injective {Q : Ideal (MRingOver ℂ ι)} (hP : IsCxVar Q e)
    {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    {B : Set (Fin e → ℂ)} (hB : IsOpen B)
    (hγ : ∀ y ∈ B, DifferentiableAt ℂ γ y ∧ γ y ∈ conePts Q ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    {y : Fin e → ℂ} (hyB : y ∈ B)
    (huniq : ∀ᶠ q in 𝓝 (y, segre (γ y)), q.2 ∈ setFibre (conePts Q) Ψ q.1 → q.2 = segre (γ q.1))
    (h0 : Ψ' (segre (γ y)) 0 ≠ 0)
    (hinj : Function.Injective (fderiv ℂ (fun y' => ratio (Ψ' (segre (γ y')))) y)) :
    cxSimple (conePts Q) Ψ' ((Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y)) := by
  have hK : Nonempty K := hP.1
  obtain ⟨k0⟩ := hP.1
  have hQh : IsMultiHomogIdeal Q := hP.2.1.2.1
  set τ : (Fin e → ℂ) → Fin e → ℂ := fun y' => ratio (Ψ' (segre (γ y'))) with hτdef
  have hcont0 : ContinuousOn (fun y' => Ψ' (segre (γ y')) 0) B := fun y' hy' =>
    (differentiableAt_pi.1 (differentiableAt_proj_segre Ψ' (hγ y' hy').1) 0).continuousAt.continuousWithinAt
  set D := B ∩ (fun y' => Ψ' (segre (γ y')) 0) ⁻¹' {0}ᶜ with hDdef
  have hDo : IsOpen D := hcont0.isOpen_inter_preimage hB isOpen_compl_singleton
  have hyD : y ∈ D := ⟨hyB, h0⟩
  have hτd : DifferentiableOn ℂ τ D := fun y' hy' =>
    (differentiableAt_ratio Ψ' (hγ y' hy'.1).1 hy'.2).differentiableWithinAt
  have hτa : AnalyticAt ℂ τ y := GroundTheory.Heights₂.Heights.SheetOnlyNull.analyticOnNhd_of_differentiableOn hDo hτd y hyD
  have hτc : ContDiffAt ℂ 1 τ y := hτa.contDiffAt
  set L := (LinearEquiv.ofInjectiveEndo (fderiv ℂ τ y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))
    hinj).toContinuousLinearEquiv with hLdef
  have hτL : HasFDerivAt τ (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) y :=
    hτa.differentiableAt.hasFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  set φ := hτc.toOpenPartialHomeomorph τ hτL one_ne_zero with hφdef
  have hφτ : ∀ y', φ y' = τ y' := fun y' => rfl
  have hysrc : y ∈ φ.source := hτc.mem_toOpenPartialHomeomorph_source hτL one_ne_zero
  have hytgt : τ y ∈ φ.target := hτc.image_mem_toOpenPartialHomeomorph_target hτL one_ne_zero
  have hsymm_y : φ.symm (τ y) = y := φ.left_inv hysrc
  have hsymmc : ContDiffAt ℂ 1 φ.symm (τ y) :=
    φ.contDiffAt_symm (f₀' := L) hytgt (by rw [hsymm_y]; exact hτL) (by rw [hsymm_y]; exact hτc)
  have hev_D : ∀ᶠ t in 𝓝 (τ y), φ.symm t ∈ D :=
    hsymmc.continuousAt.preimage_mem_nhds (by rw [hsymm_y]; exact hDo.mem_nhds hyD)
  have hev_d : ∀ᶠ t in 𝓝 (τ y), DifferentiableAt ℂ φ.symm t :=
    (hsymmc.eventually (by simp)).mono fun t ht => ht.differentiableAt one_ne_zero
  have hev_t : ∀ᶠ t in 𝓝 (τ y), t ∈ φ.target := φ.open_target.mem_nhds hytgt
  set γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
    fun t => scaleBlock k0 (Ψ' (segre (γ (φ.symm t))) 0)⁻¹ (γ (φ.symm t)) with hγ'def
  have hγ'd : ∀ t, φ.symm t ∈ D → DifferentiableAt ℂ φ.symm t → DifferentiableAt ℂ γ' t := by
    intro t ht hdt
    have hg : DifferentiableAt ℂ (fun t => γ (φ.symm t)) t := (hγ _ ht.1).1.comp t hdt
    have hc : DifferentiableAt ℂ (fun t => (Ψ' (segre (γ (φ.symm t))) 0)⁻¹) t :=
      ((differentiableAt_pi.1 (differentiableAt_proj_segre Ψ' (hγ _ ht.1).1) 0).fun_inv ht.2).comp t hdt
    refine differentiableAt_pi.2 fun p => ?_
    simp only [hγ'def, scaleBlock]
    split_ifs
    · exact hc.fun_mul (differentiableAt_pi.1 hg p)
    · exact (differentiableAt_const _).fun_mul (differentiableAt_pi.1 hg p)
  have hsheet : IsSetSheet (conePts Q) Ψ' (τ y) ((Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y)) γ' := by
    refine ⟨by simp only [hγ'def, hsymm_y, segre_scaleBlock], ?_⟩
    filter_upwards [hev_D, hev_d, hev_t] with t h1 h2 h3
    refine ⟨hγ'd t h1 h2, mem_conePts Q hQh k0 (inv_ne_zero h1.2) (hγ _ h1.1).2.1, ?_⟩
    simp only [hγ'def, segre_scaleBlock, map_smul]
    rw [inv_smul_eq_cons _ h1.2]
    exact congrArg _ (φ.right_inv h3)
  have hΨc : Continuous Ψ := LinearMap.continuous_of_finiteDimensional Ψ
  set w' := (Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y) with hw'def
  have hΨw' : Ψ w' = (Ψ' (segre (γ y)) 0)⁻¹ • (Fin.cons 1 y : Fin (e + 1) → ℂ) := by
    rw [hw'def, map_smul, (hγ y hyB).2.2]
  have hw'0 : Ψ w' 0 ≠ 0 := by
    rw [hΨw']
    simpa using h0
  let m : (Fin e → ℂ) × (((k : K) → ι k) → ℂ) → (Fin e → ℂ) × (((k : K) → ι k) → ℂ) :=
    fun q => (ratio (Ψ q.2), (Ψ q.2 0)⁻¹ • q.2)
  have hm0 : m (τ y, w') = (y, segre (γ y)) := by
    refine Prod.ext ?_ ?_
    · show ratio (Ψ w') = y
      rw [hΨw', ratio_smul_cons (inv_ne_zero h0)]
    · show (Ψ w' 0)⁻¹ • w' = segre (γ y)
      rw [hΨw', hw'def]
      simp [h0]
  have h2 : Continuous fun q : (Fin e → ℂ) × (((k : K) → ι k) → ℂ) => Ψ q.2 := hΨc.comp continuous_snd
  have h20 : ContinuousAt (fun q : (Fin e → ℂ) × (((k : K) → ι k) → ℂ) => Ψ q.2 0) (τ y, w') :=
    ((continuous_apply 0).comp h2).continuousAt
  have hmc : ContinuousAt m (τ y, w') := by
    refine ContinuousAt.prodMk ?_ ?_
    · refine continuousAt_pi.2 fun i => ?_
      exact ContinuousAt.div (f := fun q : (Fin e → ℂ) × (((k : K) → ι k) → ℂ) => Ψ q.2 i.succ)
        ((continuous_apply i.succ).comp h2).continuousAt h20 hw'0
    · exact (h20.inv₀ hw'0).smul continuous_snd.continuousAt
  have hm : Tendsto m (𝓝 (τ y, w')) (𝓝 (y, segre (γ y))) := hm0 ▸ hmc.tendsto
  have hev1 := hm.eventually huniq
  have hev2 : ∀ᶠ q in 𝓝 (τ y, w'), (m q).1 ∈ φ.source :=
    ((continuous_fst.tendsto _).comp hm).eventually (φ.open_source.mem_nhds hysrc)
  have hev3 : ∀ᶠ q in 𝓝 (τ y, w'), Ψ q.2 0 ≠ 0 := h20.eventually_ne hw'0
  refine ⟨τ y, γ', hsheet, ?_⟩
  filter_upwards [hev1, hev2, hev3] with q hq1 hq2 hq3 hqf
  obtain ⟨z, hz, hzs, hΨ'z⟩ := hqf
  have hfib : (m q).2 ∈ setFibre (conePts Q) Ψ (m q).1 := by
    have := smul_mem_fibre hQh hz Ψ (by rw [hzs]; exact hq3)
    rw [hzs] at this
    exact this
  have hE : (Ψ q.2 0)⁻¹ • q.2 = segre (γ (ratio (Ψ q.2))) := hq1 hfib
  have hs' : Ψ' (segre (γ (ratio (Ψ q.2)))) = (Ψ q.2 0)⁻¹ • (Fin.cons 1 q.1 : Fin (e + 1) → ℂ) := by
    rw [← hE, map_smul, hΨ'z]
  have hτs : τ (ratio (Ψ q.2)) = q.1 := by
    show ratio (Ψ' (segre (γ (ratio (Ψ q.2))))) = q.1
    rw [hs', ratio_smul_cons (inv_ne_zero hq3)]
  have hsymm_q : φ.symm q.1 = ratio (Ψ q.2) := by
    rw [← hτs]
    exact φ.left_inv hq2
  show q.2 = segre (scaleBlock k0 (Ψ' (segre (γ (φ.symm q.1))) 0)⁻¹ (γ (φ.symm q.1)))
  rw [hsymm_q, segre_scaleBlock, hs', ← hE]
  simp [hq3]

theorem piece_null (hC : GroundTheory.Heights₂.Heights.CriticalFibreInfinite.Statement) {Q : Ideal (MRingOver ℂ ι)} (hP : IsCxVar Q e)
    {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ' : IsSetGoodProj (conePts Q) Ψ')
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {O : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))} (hOo : IsOpen O)
    (hO : ∀ q ∈ O, (DifferentiableAt ℂ γ q.1 ∧ γ q.1 ∈ conePts Q ∧ Ψ (segre (γ q.1)) = Fin.cons 1 q.1) ∧
      (q.2 ∈ setFibre (conePts Q) Ψ q.1 → q.2 = segre (γ q.1))) :
    volume {y | (y, segre (γ y)) ∈ O ∧
      ¬ cxSimple (conePts Q) Ψ' ((Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y))} = 0 := by
  set τ : (Fin e → ℂ) → Fin e → ℂ := fun y' => ratio (Ψ' (segre (γ y'))) with hτdef
  set B := Prod.fst '' O with hBdef
  have hBo : IsOpen B := isOpenMap_fst O hOo
  have hγB : ∀ y ∈ B, DifferentiableAt ℂ γ y ∧ γ y ∈ conePts Q ∧ Ψ (segre (γ y)) = Fin.cons 1 y := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hO q hq).1
  have hgc : ContinuousOn (fun y => (y, segre (γ y))) B := fun y hy =>
    (continuousAt_id.prodMk (segre_differentiableAt (hγB y hy).1).continuousAt).continuousWithinAt
  set D := B ∩ (fun y => (y, segre (γ y))) ⁻¹' O with hDdef
  have hDo : IsOpen D := hgc.isOpen_inter_preimage hBo hOo
  have hcont0 : ContinuousOn (fun y' => Ψ' (segre (γ y')) 0) B := fun y' hy' =>
    (differentiableAt_pi.1 (differentiableAt_proj_segre Ψ' (hγB y' hy').1) 0).continuousAt.continuousWithinAt
  have hsub : {y | (y, segre (γ y)) ∈ O ∧ ¬ cxSimple (conePts Q) Ψ' ((Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y))} ⊆
      {y | y ∈ D ∧ Ψ' (segre (γ y)) 0 = 0} ∪
        {y | y ∈ D ∧ Ψ' (segre (γ y)) 0 ≠ 0 ∧ ¬ Function.Injective (fderiv ℂ τ y)} := by
    rintro y ⟨hyO, hns⟩
    have hyD : y ∈ D := ⟨⟨_, hyO, rfl⟩, hyO⟩
    by_cases h0 : Ψ' (segre (γ y)) 0 = 0
    · exact Or.inl ⟨hyD, h0⟩
    · refine Or.inr ⟨hyD, h0, fun hinj => hns ?_⟩
      have huniq : ∀ᶠ q in 𝓝 (y, segre (γ y)), q.2 ∈ setFibre (conePts Q) Ψ q.1 → q.2 = segre (γ q.1) :=
        Filter.mem_of_superset (hOo.mem_nhds hyO) fun q hq => (hO q hq).2
      exact isSimpleSheetPt_of_injective hP hBo hγB hyD.1 huniq h0 hinj
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro y ⟨hyD, -⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hDo y hyD
    refine ⟨Metric.ball y r, Metric.isOpen_ball, Metric.mem_ball_self hr, (convex_ball y r).isPreconnected,
      fun y' => Ψ' (segre (γ y')) 0, ?_, ?_, fun y' hy' => hy'.1.2⟩
    · exact (osgood e D _ hDo (fun y' hy' => (differentiableAt_pi.1
        (differentiableAt_proj_segre Ψ' (hγB y' hy'.1).1) 0).differentiableWithinAt)).mono hball
    · exact exists_proj_ne_zero hC hP hΨ' Metric.isOpen_ball (fun y' hy' => hγB y' (hball hy').1)
        (Metric.mem_ball_self hr)
  · apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro y ⟨hyD, hy0, -⟩
    have hD'o : IsOpen (D ∩ (fun y' => Ψ' (segre (γ y')) 0) ⁻¹' {0}ᶜ) :=
      (hcont0.mono Set.inter_subset_left).isOpen_inter_preimage hDo isOpen_compl_singleton
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hD'o y ⟨hyD, hy0⟩
    have hτd : DifferentiableOn ℂ τ (D ∩ (fun y' => Ψ' (segre (γ y')) 0) ⁻¹' {0}ᶜ) := fun y' hy' =>
      (differentiableAt_ratio Ψ' (hγB y' hy'.1.1).1 hy'.2).differentiableWithinAt
    refine ⟨Metric.ball y r, Metric.isOpen_ball, Metric.mem_ball_self hr, (convex_ball y r).isPreconnected,
      fun y' => (ReciprocityTheory.AnForm.A.jacC τ y').det,
      (GroundTheory.Heights₂.Heights.SheetOnlyNull.analyticOnNhd_det_jacC hD'o hτd).mono hball, ?_, ?_⟩
    · obtain ⟨y1, hy1, hinj⟩ := exists_injective hC hP hΨ' Metric.isOpen_ball ⟨y, Metric.mem_ball_self hr⟩
        (fun y' hy' => hγB y' (hball hy').1.1) (fun y' hy' => (hball hy').2)
      refine ⟨y1, hy1, ?_⟩
      show (ReciprocityTheory.AnForm.A.jacC τ y1).det ≠ 0
      rw [ReciprocityTheory.AnForm.A.det_jacC]
      exact (GroundTheory.Heights₂.Heights.SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
    · rintro y' ⟨⟨-, -, hni⟩, -⟩
      show (ReciprocityTheory.AnForm.A.jacC τ y').det = 0
      rw [ReciprocityTheory.AnForm.A.det_jacC]
      by_contra hne
      exact hni ((GroundTheory.Heights₂.Heights.SheetOnlyNull.injective_iff_det_ne_zero _).2 hne)

theorem cxSimple_only_null : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → IsSetGoodProj (conePts Q) Ψ' →
    volume {y : Fin e → ℂ | ∃ w ∈ setFibre (conePts Q) Ψ y, cxSimple (conePts Q) Ψ w ∧
      ¬ cxSimple (conePts Q) Ψ' ((Ψ' w 0)⁻¹ • w)} = 0 := by
  intro K _ ι _ Q e Ψ Ψ' hP hΨ hΨ'
  classical
  have hloc : ∀ p : (Fin e → ℂ) × (((k : K) → ι k) → ℂ), ∃ (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ)
      (O : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))), IsOpen O ∧
      (∀ q ∈ O, (DifferentiableAt ℂ γ q.1 ∧ γ q.1 ∈ conePts Q ∧ Ψ (segre (γ q.1)) = Fin.cons 1 q.1) ∧
        (q.2 ∈ setFibre (conePts Q) Ψ q.1 → q.2 = segre (γ q.1))) ∧
      (p.2 ∈ setFibre (conePts Q) Ψ p.1 → cxSimple (conePts Q) Ψ p.2 → p ∈ O) := by
    intro p
    by_cases hp : p.2 ∈ setFibre (conePts Q) Ψ p.1 ∧ cxSimple (conePts Q) Ψ p.2
    · obtain ⟨hpf, y0, γ, ⟨hseg, hsh⟩, hun⟩ := hp
      have hy0 : y0 = p.1 := by
        obtain ⟨z, -, -, hΨz⟩ := hpf
        have h1 := hsh.self_of_nhds.2.2
        rw [hseg, hΨz] at h1
        funext i
        have hi := congrFun h1 i.succ
        simp only [Fin.cons_succ] at hi
        exact hi.symm
      subst hy0
      have hev : ∀ᶠ q in 𝓝 (p.1, p.2),
          (DifferentiableAt ℂ γ q.1 ∧ γ q.1 ∈ conePts Q ∧ Ψ (segre (γ q.1)) = Fin.cons 1 q.1) ∧
            (q.2 ∈ setFibre (conePts Q) Ψ q.1 → q.2 = segre (γ q.1)) :=
        ((continuous_fst.tendsto (p.1, p.2)).eventually hsh).and hun
      obtain ⟨O, hO, hOo, hpO⟩ := eventually_nhds_iff.1 hev
      exact ⟨γ, O, hOo, hO, fun _ _ => hpO⟩
    · exact ⟨fun _ _ => 0, ∅, isOpen_empty, by simp, fun h1 h2 => absurd ⟨h1, h2⟩ hp⟩
  choose γ O hOo hO hpO using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable O hOo
  refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun p _ =>
    piece_null GroundTheory.Heights₂.Heights.CriticalFibreInfinite.proof hP hΨ' (hOo p) (hO p))
  rintro y ⟨w, hwf, hws, hwn⟩
  have hmem : (y, w) ∈ ⋃ p ∈ T, O p := hTU ▸ Set.mem_iUnion.2 ⟨(y, w), hpO (y, w) hwf hws⟩
  obtain ⟨p, hpT, hyw⟩ := Set.mem_iUnion₂.1 hmem
  have hw : w = segre (γ p y) := ((hO p) (y, w) hyw).2 hwf
  subst hw
  exact Set.mem_biUnion hpT ⟨hyw, hwn⟩

end GlobalTheory.CompanionTheory.Ar.Pub.CxOnly
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeNonsimpleFibresEqZeroStatement
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_nonsimple_fibres_eq_zero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → IsSetGoodProj (conePts Q) Ψ' →
    volume {y : Fin e → ℂ | ∃ w ∈ setFibre (conePts Q) Ψ y, cxSimple (conePts Q) Ψ w ∧
      ¬ cxSimple (conePts Q) Ψ' ((Ψ' w 0)⁻¹ • w)} = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.cxSimple_only_null | exact GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.cxSimple_only_null | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.cxSimple_only_null <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralDensityIndependentProjection
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep

theorem cx_fibre_finite : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → ∀ y, (setFibre (conePts Q) Ψ y).Finite := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite | exact GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite <;> assumption)

theorem cx_posDens_aemeasurable : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    AEMeasurable (cxPosDens (conePts Q) Ψ (pot L) g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable | exact GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable <;> assumption)

theorem cx_simple_null : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ →
    volume {y : Fin e → ℂ | ∃ w ∈ setFibre (conePts Q) Ψ y, (∃ γ, IsSetSheet (conePts Q) Ψ y w γ) ∧
      ¬ cxSimple (conePts Q) Ψ w} = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cxSheetSimpleNull | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cxSheetSimpleNull | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cxSheetSimpleNull <;> assumption)

theorem cxPosDens_split {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    {Q : Ideal (MRingOver ℂ ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (E : ℕ → Set ((Σ k, ι k) → ℂ))
    (y : Fin e → ℂ) (hfin : (setFibre (conePts Q) Ψ y).Finite) (hE : Pairwise (Function.onFun Disjoint E))
    (hcov : ∀ w ∈ setFibre (conePts Q) Ψ y, (∃ γ, IsSetSheet (conePts Q) Ψ y w γ) → ∀ z ∈ conePts Q, segre z = w → ∃ k, z ∈ E k) :
    ENNReal.ofReal (cxPosDens (conePts Q) Ψ φ g y) =
      ∑' k, ENNReal.ofReal (cxPosDens (conePts Q) Ψ φ ((E k).indicator g) y) := by
  classical
  unfold cxPosDens
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hT0 : ∀ (g' : ((Σ k, ι k) → ℂ) → ℝ) w, 0 ≤ max (setSheetDensity (conePts Q) Ψ φ g' y w) 0 :=
    fun _ _ => le_max_right _ _
  have hpt : ∀ w ∈ hfin.toFinset, ENNReal.ofReal (max (setSheetDensity (conePts Q) Ψ φ g y w) 0) =
      ∑' k, ENNReal.ofReal (max (setSheetDensity (conePts Q) Ψ φ ((E k).indicator g) y w) 0) := by
    intro w hw
    have hw' : w ∈ setFibre (conePts Q) Ψ y := hfin.mem_toFinset.mp hw
    by_cases hs : ∃ γ, IsSetSheet (conePts Q) Ψ y w γ
    · have hz : hs.choose y ∈ conePts Q := hs.choose_spec.2.self_of_nhds.2.1
      obtain ⟨k₀, hk₀⟩ := hcov w hw' hs _ hz hs.choose_spec.1
      rw [tsum_eq_single k₀]
      · simp only [setSheetDensity, dif_pos hs, Set.indicator_of_mem hk₀]
      · intro k hk
        have hxk : hs.choose y ∉ E k := fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀
        simp [setSheetDensity, dif_pos hs, Set.indicator_of_notMem hxk]
    · simp [setSheetDensity, dif_neg hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 g w), Finset.sum_congr rfl hpt,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 _ w)).symm

theorem cx_posPart_indep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → IsSetGoodProj (conePts Q) Ψ' →
    (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot L) g y) =
      ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ' (pot L) g y) := by
  intro K _ ι _ Q e Ψ Ψ' L g hP hΨ hΨ' hLs hg hg0
  classical

  set Inv : Set ((Σ k, ι k) → ℂ) → Prop := fun S => ∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
    ((fun p => c p.1 * z' p) ∈ S ↔ z' ∈ S) with hInv

  set Gd : ((Σ k, ι k) → ℂ) → Prop := fun z => z ∈ conePts Q ∧
    cxSimple (conePts Q) Ψ ((Ψ (segre z) 0)⁻¹ • segre z) ∧
    cxSimple (conePts Q) Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z) with hGd
  have key : ∀ z, ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ Inv W ∧ (Gd z → z ∈ W) ∧
      ∀ E, MeasurableSet E → Inv E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot L) (E.indicator g) y) =
          ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ' (pot L) (E.indicator g) y) := by
    intro z
    by_cases hz : Gd z
    · obtain ⟨W, hW, hzW, hWi, hWE⟩ := GlobalTheory.T.fibre_density_independent_projection K ι Q e Ψ Ψ' L g z hP hΨ hΨ' hLs hg hg0 hz.1 hz.2.1 hz.2.2
      exact ⟨W, hW, hWi, fun _ => hzW, hWE⟩
    · refine ⟨∅, isOpen_empty, fun _ _ _ => Iff.rfl, fun h => absurd h hz, fun E _ _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.indicator_empty]
      simp [cxPosDens, setSheetDensity]
  choose W hWo hWi hzW hWE using key
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨f, hf⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  set E : ℕ → Set ((Σ k, ι k) → ℂ) := disjointed (fun k => W (f k)) with hE
  have hEm : ∀ k, MeasurableSet (E k) := MeasurableSet.disjointed fun k => (hWo (f k)).measurableSet
  have hEW : ∀ k, E k ⊆ W (f k) := disjointed_subset _
  have hEd : Pairwise (Function.onFun Disjoint E) := disjoint_disjointed _
  have hEi : ∀ k, Inv (E k) := by
    intro k c z' hc
    simp only [hE, disjointed_eq_inter_compl, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
      hWi _ c z' hc]
  have hgE : ∀ k (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      (E k).indicator g (fun p => c p.1 * z' p) = (E k).indicator g z' := by
    intro k c z' hc
    simp only [Set.indicator_apply, hEi k c z' hc, hg0 c z' hc]
  have hcov : ∀ z, Gd z → ∃ k, z ∈ E k := by
    intro z hq
    have : z ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨z, hzW z hq⟩
    obtain ⟨i, hiT, hzi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨m, rfl⟩ : i ∈ Set.range f := hf ▸ Set.mem_insert_of_mem 0 hiT
    have : z ∈ ⋃ k, E k := by
      rw [hE, iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hzi⟩
    exact Set.mem_iUnion.1 this

  have hae : ∀ B B' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsSetGoodProj (conePts Q) B → IsSetGoodProj (conePts Q) B' →
      (∀ z ∈ conePts Q, cxSimple (conePts Q) B ((B (segre z) 0)⁻¹ • segre z) →
        cxSimple (conePts Q) B' ((B' (segre z) 0)⁻¹ • segre z) → ∃ k, z ∈ E k) →
      ∀ᵐ y, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) g y) =
        ∑' k, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) ((E k).indicator g) y) := by
    intro B B' hB hB' hc
    have hnull := measure_union_null (cx_simple_null K ι Q e B hP hB) (GlobalTheory.T.volume_nonsimple_fibres_eq_zero K ι Q e B B' hP hB hB')
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    refine cxPosDens_split _ _ E y (cx_fibre_finite K ι Q e B hP hB y) hEd fun w hw hs z hz hzw => ?_
    have hw1 : B w 0 = 1 := by
      obtain ⟨_, _, _, h⟩ := hw
      rw [h]
      rfl
    have hs1 : cxSimple (conePts Q) B w := by
      by_contra hn
      exact hy (Or.inl ⟨w, hw, hs, hn⟩)
    have hs2 : cxSimple (conePts Q) B' ((B' w 0)⁻¹ • w) := by
      by_contra hn
      exact hy (Or.inr ⟨w, hw, hs1, hn⟩)
    subst hzw
    refine hc z hz ?_ hs2
    rwa [hw1, inv_one, one_smul]
  have hint : ∀ B : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsSetGoodProj (conePts Q) B →
      (∀ᵐ y, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) g y) =
        ∑' k, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) ((E k).indicator g) y)) →
      ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) g y) =
        ∑' k, ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) ((E k).indicator g) y) := by
    intro B hB h2
    rw [lintegral_congr_ae h2, lintegral_tsum fun k =>
      (cx_posDens_aemeasurable K ι Q e B L _ hP hB hLs (hg.indicator (hEm k)) (hgE k)).ennreal_ofReal]
  rw [hint Ψ hΨ (hae Ψ Ψ' hΨ hΨ' fun z hz h1 h2 => hcov z ⟨hz, h1, h2⟩),
    hint Ψ' hΨ' (hae Ψ' Ψ hΨ' hΨ fun z hz h1 h2 => hcov z ⟨hz, h2, h1⟩)]
  exact tsum_congr fun k => hWE (f k) (E k) (hEm k) (hEi k) (hEW k)

end GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralDensityIndependentProjectionStatement
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_density_independent_projection : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → IsSetGoodProj (conePts Q) Ψ' →
    (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot L) g y) =
      ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ' (pot L) g y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep.cx_posPart_indep | exact GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep.cx_posPart_indep | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep.cx_posPart_indep <;> assumption)
end
