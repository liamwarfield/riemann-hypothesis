module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalizingWeightEqualOffPlaceMasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceVacuumIsLocalVacuumChart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOfProjectionSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOfProjectionSupport
open MeasureTheory Filter Topology

namespace GlobalTheory.FiberPointwise

lemma lintegral_indicator_translate {X : Type} [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd X]
    (μ : Measure X) [μ.IsAddRightInvariant] (P : X →+ X)
    (h : X → ENNReal) (hinv : ∀ x z, P z = z → h (x + z) = h x) (S : Set X) (z : X) (hz : P z = z) :
    ∫⁻ x, Set.indicator {x | P x - z ∈ S} h x ∂μ = ∫⁻ x, Set.indicator {x | P x ∈ S} h x ∂μ := by
  rw [← lintegral_add_right_eq_self (μ := μ) _ z]
  congr 1
  funext x
  show Set.indicator {x | P x - z ∈ S} h (x + z) = Set.indicator {x | P x ∈ S} h x
  have hx : (P (x + z) - z ∈ S) ↔ (P x ∈ S) := by rw [map_add (f := _), hz, add_sub_cancel_right]
  by_cases hxs : P x ∈ S
  · rw [Set.indicator_of_mem (show x + z ∈ {x | P x - z ∈ S} from hx.mpr hxs),
      Set.indicator_of_mem (show x ∈ {x | P x ∈ S} from hxs), hinv x z hz]
  · rw [Set.indicator_of_notMem (show x + z ∉ {x | P x - z ∈ S} from fun h' => hxs (hx.mp h')),
      Set.indicator_of_notMem (show x ∉ {x | P x ∈ S} from hxs)]

theorem vanish_at_point : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (P : X →+ X), Continuous P →
    (∀ x, P (P x) = P x) → ∀ (Φ Ψ : X → ℂ), Continuous Φ → Continuous Ψ → ∀ K : Set X, IsCompact K →
    (∀ x, Φ x ≠ 0 → P x ∈ K) → ∀ y : X, (∀ z, P z = z → Φ (y + z) = 0) →
    (∀ O : Set X, IsOpen O → y ∈ O → ∃ h : X → ENNReal, Measurable h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, P z = z → h (x + z) = h x) ∧ (∀ x, h x ≠ 0 → x + (P y - P x) ∈ O) ∧
      (∃ O' : Set X, IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ) → Ψ y = 0 := by
  intro X _ _ _ _ _ _ μ _ P hPc hPP Φ Ψ hΦ hΨ K hK hΦK y hΦy hyp
  by_contra hne
  set δ : NNReal := ‖Ψ y‖₊ / 2 with hδ
  have hΨpos : 0 < ‖Ψ y‖₊ := nnnorm_pos.mpr hne
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < ‖Ψ y‖₊ := NNReal.half_lt_self hΨpos.ne'
  let V : Set X := {x | δ < ‖Ψ x‖₊}
  have hVo : IsOpen V := isOpen_lt continuous_const hΨ.nnnorm
  have hyV : y ∈ V := hδlt
  have hsum : P y + (y - P y) = y := by abel
  have hpre : (fun p : X × X => p.1 + p.2) ⁻¹' V ∈ 𝓝 (P y, y - P y) := by
    apply continuous_add.continuousAt.preimage_mem_nhds
    simp only [hsum]
    exact hVo.mem_nhds hyV
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hpre
  obtain ⟨s1, hs1, hs1u, hs1c⟩ := local_compact_nhds hu
  obtain ⟨s2, hs2, hs2v, hs2c⟩ := local_compact_nhds hv
  set U1 := interior s1 with hU1
  set O2 := interior s2 with hO2
  have hU1o : IsOpen U1 := isOpen_interior
  have hO2o : IsOpen O2 := isOpen_interior
  have hPyU1 : P y ∈ U1 := mem_interior_iff_mem_nhds.mpr hs1
  have hQyO2 : y - P y ∈ O2 := mem_interior_iff_mem_nhds.mpr hs2
  have hUV : ∀ a ∈ U1, ∀ b ∈ O2, a + b ∈ V := fun a ha b hb =>
    huv (Set.mk_mem_prod (hs1u (interior_subset ha)) (hs2v (interior_subset hb)))
  set PK := P '' K with hPK
  have hPKc : IsCompact PK := hK.image hPc
  have hPKfix : ∀ a ∈ PK, P a = a := by rintro _ ⟨k, -, rfl⟩; exact hPP k
  obtain ⟨t, htPK, hcover⟩ := hPKc.elim_nhds_subcover (fun a => {w | w - (a - P y) ∈ U1}) (by
    intro a _
    apply (hU1o.preimage (continuous_id.sub continuous_const)).mem_nhds
    show a - (a - P y) ∈ U1
    rwa [sub_sub_cancel])
  set N := t.card with hN
  set ε : NNReal := δ / (N + 1) with hεdef
  have hεpos : 0 < ε := div_pos hδpos (by positivity)
  have hε : ε ^ 2 * N < δ ^ 2 := by
    rw [hεdef, ← NNReal.coe_lt_coe]; push_cast
    have hδr : (0:ℝ) < δ := hδpos
    have hNr : (0:ℝ) ≤ N := Nat.cast_nonneg _
    rw [div_pow, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [pow_pos hδr 2, mul_nonneg (pow_pos hδr 2).le (sq_nonneg (N:ℝ)), mul_nonneg (pow_pos hδr 2).le hNr]
  have htube : ∀ᶠ b in 𝓝 (y - P y), ∀ a ∈ PK, ‖Φ (a + b)‖₊ < ε := by
    apply hPKc.eventually_forall_of_forall_eventually
    intro a ha
    have h0 : Φ (a + (y - P y)) = 0 := by
      have := hΦy (a - P y) (by rw [map_sub, hPKfix a ha, hPP])
      rwa [show y + (a - P y) = a + (y - P y) by abel] at this
    have hcont : Continuous fun p : X × X => ‖Φ (p.2 + p.1)‖₊ :=
      (hΦ.comp (continuous_snd.add continuous_fst)).nnnorm
    have hmem : {p : X × X | ‖Φ (p.2 + p.1)‖₊ < ε} ∈ 𝓝 (y - P y, a) :=
      (isOpen_lt hcont continuous_const).mem_nhds (by simp [h0, hεpos])
    exact hmem
  obtain ⟨O3, hO3sub, hO3o, hQyO3⟩ := eventually_nhds_iff.mp htube
  let O : Set X := {w | w - P y ∈ O2 ∩ O3}
  have hOo : IsOpen O := (hO2o.inter hO3o).preimage (continuous_id.sub continuous_const)
  have hyO : y ∈ O := ⟨hQyO2, hQyO3⟩
  obtain ⟨h, hhm, hh1, hinv, hsupp, ⟨O', hO'o, hyO', hO'⟩, heq⟩ := hyp O hOo hyO
  have hsupp' : ∀ x, h x ≠ 0 → x - P x ∈ O2 ∧ x - P x ∈ O3 := by
    intro x hx
    have := hsupp x hx
    simp only [O, Set.mem_setOf_eq] at this
    rwa [show x + (P y - P x) - P y = x - P x by abel] at this
  have hdec : ∀ x : X, P x + (x - P x) = x := fun x => by abel
  set A : Set X := {x | P x ∈ U1} with hA
  set I := ∫⁻ x, A.indicator h x ∂μ with hI
  have hlow : (δ:ENNReal) ^ 2 * I ≤ ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ := by
    rw [hI, ← lintegral_const_mul' _ _ (by simp)]
    apply lintegral_mono
    intro x
    dsimp only
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA]
      by_cases hx0 : h x = 0
      · simp [hx0]
      · have hxV : x ∈ V := by
          have := hUV (P x) hxA (x - P x) (hsupp' x hx0).1
          rwa [hdec] at this
        rw [mul_comm]
        gcongr
        rw [enorm_eq_nnnorm]
        exact ENNReal.coe_le_coe.mpr hxV.le
    · simp [hxA]
  have hup : ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ ≤ (ε:ENNReal) ^ 2 * (N * I) := by
    have hpt : ∀ x, h x * ‖Φ x‖ₑ ^ 2 ≤
        (ε:ENNReal) ^ 2 * ∑ a ∈ t, Set.indicator {x | P x - (a - P y) ∈ U1} h x := by
      intro x
      by_cases hx0 : h x = 0
      · simp [hx0]
      by_cases hΦ0 : Φ x = 0
      · simp [hΦ0]
      have hPx : P x ∈ PK := ⟨P x, hΦK x hΦ0, hPP x⟩
      obtain ⟨a, hat, hxa⟩ : ∃ a ∈ t, P x - (a - P y) ∈ U1 := by
        have := hcover hPx
        simp only [Set.mem_iUnion] at this
        obtain ⟨a, ha, h'⟩ := this
        exact ⟨a, ha, h'⟩
      have hsmall : ‖Φ x‖₊ < ε := by
        have := hO3sub _ (hsupp' x hx0).2 (P x) hPx
        rwa [hdec] at this
      calc h x * ‖Φ x‖ₑ ^ 2 ≤ h x * (ε:ENNReal) ^ 2 := by
            gcongr
            rw [enorm_eq_nnnorm]
            exact ENNReal.coe_le_coe.mpr hsmall.le
        _ = (ε:ENNReal) ^ 2 * Set.indicator {x | P x - (a - P y) ∈ U1} h x := by
            rw [Set.indicator_of_mem (show x ∈ {x | P x - (a - P y) ∈ U1} from hxa), mul_comm]
        _ ≤ (ε:ENNReal) ^ 2 * ∑ a ∈ t, Set.indicator {x | P x - (a - P y) ∈ U1} h x := by
            gcongr
            exact Finset.single_le_sum (f := fun a => Set.indicator {x | P x - (a - P y) ∈ U1} h x)
              (fun _ _ => bot_le) hat
    calc _ ≤ ∫⁻ x, (ε:ENNReal) ^ 2 * ∑ a ∈ t, Set.indicator {x | P x - (a - P y) ∈ U1} h x ∂μ :=
          lintegral_mono hpt
      _ = (ε:ENNReal) ^ 2 * ∑ a ∈ t, ∫⁻ x, Set.indicator {x | P x - (a - P y) ∈ U1} h x ∂μ := by
          rw [lintegral_const_mul' _ _ (by simp), MeasureTheory.lintegral_finsetSum]
          intro a _
          exact hhm.indicator ((hU1o.preimage (hPc.sub continuous_const)).measurableSet)
      _ = (ε:ENNReal) ^ 2 * (N * I) := by
          congr 1
          rw [Finset.sum_congr rfl (fun a ha => lintegral_indicator_translate μ P h hinv U1 (a - P y)
            (by rw [map_sub, hPKfix a (htPK a ha), hPP])), Finset.sum_const, nsmul_eq_mul]
  have hIpos : I ≠ 0 := by
    let W := O' ∩ {x | Ψ x ≠ 0} ∩ A
    have hWo : IsOpen W := (hO'o.inter (isOpen_ne_fun hΨ continuous_const)).inter (hU1o.preimage hPc)
    have hyW : y ∈ W := ⟨⟨hyO', hne⟩, hPyU1⟩
    have hWpos : 0 < μ W := hWo.measure_pos μ ⟨y, hyW⟩
    have hle : (1/2 : ENNReal) * μ W ≤ I := by
      rw [← lintegral_indicator_const hWo.measurableSet]
      apply lintegral_mono
      intro x
      by_cases hxW : x ∈ W
      · rw [Set.indicator_of_mem hxW, Set.indicator_of_mem hxW.2]
        exact hO' x hxW.1.1 hxW.1.2
      · simp [hxW]
    intro h0
    rw [h0] at hle
    exact (mul_ne_zero (by simp) hWpos.ne') (le_zero_iff.mp hle)
  have hIfin : I ≠ ⊤ := by
    have hC : IsCompact ((fun p : X × X => p.1 + p.2) '' (s1 ×ˢ s2)) :=
      (hs1c.prod hs2c).image continuous_add
    obtain ⟨U, hCU, hUo, hUfin⟩ := hC.exists_open_superset_measure_lt_top μ
    have hle : I ≤ μ U := by
      rw [← lintegral_indicator_one hUo.measurableSet]
      apply lintegral_mono
      intro x
      by_cases hxA : x ∈ A
      · rw [Set.indicator_of_mem hxA]
        by_cases hx0 : h x = 0
        · simp [hx0]
        · have hxU : x ∈ U := hCU ⟨(P x, x - P x),
            ⟨interior_subset hxA, interior_subset (hsupp' x hx0).1⟩, hdec x⟩
          rw [Set.indicator_of_mem hxU]
          simpa using hh1 x
      · simp [hxA]
    exact ne_top_of_le_ne_top hUfin.ne hle
  have hchain : (δ:ENNReal) ^ 2 * I ≤ ((ε:ENNReal) ^ 2 * N) * I := by
    calc _ ≤ _ := hlow
      _ = _ := heq
      _ ≤ _ := hup
      _ = _ := by ring
  have h2 := (ENNReal.mul_le_mul_iff_left hIpos hIfin).mp hchain
  have h3 : ((δ ^ 2 : NNReal) : ENNReal) ≤ ((ε ^ 2 * N : NNReal) : ENNReal) := by
    push_cast; exact h2
  exact absurd (ENNReal.coe_le_coe.mp h3) (not_le.mpr hε)

end GlobalTheory.FiberPointwise
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOfProjectionSupportStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishing_of_projection_support : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (P : X →+ X), Continuous P →
    (∀ x, P (P x) = P x) → ∀ (Φ Ψ : X → ℂ), Continuous Φ → Continuous Ψ → ∀ K : Set X, IsCompact K →
    (∀ x, Φ x ≠ 0 → P x ∈ K) → ∀ y : X, (∀ z, P z = z → Φ (y + z) = 0) →
    (∀ O : Set X, IsOpen O → y ∈ O → ∃ h : X → ENNReal, Measurable h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, P z = z → h (x + z) = h x) ∧ (∀ x, h x ≠ 0 → x + (P y - P x) ∈ O) ∧
      (∃ O' : Set X, IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ) → Ψ y = 0 := by
  first | exact @GlobalTheory.FiberPointwise.vanish_at_point | exact GlobalTheory.FiberPointwise.vanish_at_point | (intros; apply GlobalTheory.FiberPointwise.vanish_at_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.FibreLocality

theorem lp : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (P : X →+ X), Continuous P →
    (∀ x, P (P x) = P x) → ∀ (Φ Ψ : X → ℂ), Continuous Φ → Continuous Ψ → ∀ K : Set X, IsCompact K →
    (∀ x, Φ x ≠ 0 → P x ∈ K) → ∀ y : X, (∀ z, P z = z → Φ (y + z) = 0) →
    (∀ O : Set X, IsOpen O → y ∈ O → ∃ h : X → ENNReal, Measurable h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, P z = z → h (x + z) = h x) ∧ (∀ x, h x ≠ 0 → x + (P y - P x) ∈ O) ∧
      (∃ O' : Set X, IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ) → Ψ y = 0 := GlobalTheory.T.vanishing_of_projection_support

theorem lw : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ,
    (∀ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) →
      ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x‖ₑ ^ 2 ∂μ) →
    ∀ (y : κ → AF F) (O : Set (κ → AF F)), IsOpen O → y ∈ O →
    ∃ h : (κ → AF F) → ENNReal, @Measurable _ _ (borel _) _ h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, GlobalTheory.LatVac.liftV v 1 • z = z → h (x + z) = h x) ∧
      (∀ x, h x ≠ 0 → x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x) ∈ O) ∧
      (∃ O' : Set (κ → AF F), IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ := GlobalTheory.T.exists_localizingWeight_equal_offPlaceMasses

theorem lc : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ b : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    (fun x => ψ (x ⬝ᵥ b) * Φ x) ∈ GlobalTheory.WeilM.schA F κ := GlobalTheory.T.addCharDotMul_mem_adelicSchwartzSpace

open scoped Classical in
theorem ls_pure {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ K : Set (κ → AF F), IsCompact K ∧ ∀ x, GlobalTheory.WeilM.pureA F f g x ≠ 0 → GlobalTheory.LatVac.liftV v 1 • x ∈ K := by
  set e := GlobalTheory.LatVac.liftV v (1 : Fv F v) with he_def
  let ι : FiniteAdeleRing (𝓞 F) F → AF F := fun a => (0, a)
  have hι : Continuous ι := continuous_const.prodMk continuous_id
  let Θ : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AF F) := fun z => e • fun i => ι (z i)
  have hΘ : Continuous Θ := by
    refine (continuous_const_smul e).comp (continuous_pi fun i => ?_)
    exact hι.comp (continuous_apply i)
  have he1 : e.1 = 0 := rfl
  refine ⟨Θ '' tsupport g, hg.2.isCompact.image hΘ, fun x hx => ⟨fun i => (x i).2, ?_, ?_⟩⟩
  · refine subset_tsupport _ ?_
    intro h0
    apply hx
    simp only [GlobalTheory.WeilM.pureA]
    rw [h0, mul_zero]
  · funext i
    show e * ι (x i).2 = e * x i
    refine Prod.ext ?_ rfl
    show e.1 * 0 = e.1 * (x i).1
    rw [he1, zero_mul, zero_mul]

theorem ls : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∃ K : Set (κ → AF F), IsCompact K ∧ ∀ x, Φ x ≠ 0 → GlobalTheory.LatVac.liftV v 1 • x ∈ K := by
  intro F _ _ κ _ v Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact ls_pure v f g hg
  | zero => exact ⟨∅, isCompact_empty, fun x hx => (hx rfl).elim⟩
  | add Φ₁ Φ₂ _ _ h1 h2 =>
    obtain ⟨K₁, hK₁, h₁⟩ := h1
    obtain ⟨K₂, hK₂, h₂⟩ := h2
    refine ⟨K₁ ∪ K₂, hK₁.union hK₂, fun x hx => ?_⟩
    by_cases hx1 : Φ₁ x = 0
    · exact Or.inr (h₂ x fun hx2 => hx (by simp [hx1, hx2]))
    · exact Or.inl (h₁ x hx1)
  | smul c Φ _ h =>
    obtain ⟨K, hK, hs⟩ := h
    exact ⟨K, hK, fun x hx => hs x fun h0 => hx (by simp [h0])⟩

theorem liftV_mul_self {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) :
    GlobalTheory.LatVac.liftV v (1 : Fv F v) * GlobalTheory.LatVac.liftV v 1 = GlobalTheory.LatVac.liftV v 1 := by
  have h := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) (GlobalTheory.LatVac.liftV v 1 - 1)
    (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h
  exact h

theorem at_iff {F : Type} [Field F] [NumberField F] {κ : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (z : κ → AF F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z ↔ GlobalTheory.LatVac.liftV v 1 • z = z := by
  constructor
  · intro h
    have h1 := h (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    exact h1.symm
  · intro h u hu
    rw [← h, smul_smul]
    have := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) u hu
    rw [smul_eq_mul] at this
    rw [this, zero_smul]

theorem eq_zero_of_vanish_fibre : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    (∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T Φ ∈ GlobalTheory.WeilM.schA F κ) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ) →
    (∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      T (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : κ → AF F, (∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → Φ (y + z) = 0) → T Φ y = 0 := by
  intro F _ _ κ _ v ψ T hstd hnt hpres hiso hcomm Φ hΦ y hy
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  set e := GlobalTheory.LatVac.liftV v (1 : Fv F v) with he_def
  have he0 : evFin F v (1 - e) = 0 := by rw [map_sub, he_def, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self]
  let P : (κ → AF F) →+ (κ → AF F) := DistribSMul.toAddMonoidHom _ e
  have hPc : Continuous P := continuous_const_smul e
  have hPP : ∀ x, P (P x) = P x := fun x => by
    show e • e • x = e • x
    rw [smul_smul, he_def, liftV_mul_self]
  have hTΦ := hpres Φ hΦ
  obtain ⟨K, hK, hKs⟩ := ls v Φ hΦ
  let μ : Measure (κ → AF F) := Measure.addHaar
  refine lp μ P hPc hPP Φ (T Φ) (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ)
    (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hTΦ) K hK hKs y
    (fun z hz => hy z ((at_iff v z).2 hz)) ?_
  intro O hO hyO
  have htrig : ∀ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, e • b = 0) →
      ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * T Φ x‖ₑ ^ 2 ∂μ =
        ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x‖ₑ ^ 2 ∂μ := by
    intro s c hs
    have hchar : ∀ b ∈ s, ∀ Ψ ∈ schA F κ,
        T (fun x => ψ (x ⬝ᵥ b) * Ψ x) = fun x => ψ (x ⬝ᵥ b) * T Ψ x := by
      intro b hb Ψ hΨ
      have h1 := hcomm (1 - e) he0 0 b Ψ hΨ
      have hb' : (1 - e) • b = b := by rw [sub_smul, one_smul, hs b hb, sub_zero]
      have hs0 : ∀ Ψ' : (κ → AF F) → ℂ,
          schr ψ ((1 - e) • (0 : κ → AF F), (1 - e) • b) Ψ' = fun x => ψ (x ⬝ᵥ b) * Ψ' x := by
        intro Ψ'; funext x; simp [schr, hb']
      rw [hs0, hs0] at h1
      exact h1
    have hsum : ∀ G : (κ → AF F) → ℂ, (fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * G x) =
        ∑ b ∈ s, c b • (fun x => ψ (x ⬝ᵥ b) * G x) := by
      intro G; funext x; simp [Finset.sum_mul, mul_assoc]
    have hmem : (fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x) ∈ schA F κ := by
      rw [hsum]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (lc ψ hstd b Φ hΦ)
    have hT : T (fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x) =
        fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * T Φ x := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hsum, hsum, map_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [map_smul, hchar b hb Φ hΦ]
    have := hiso μ inferInstance _ hmem
    rw [hT] at this
    exact this
  exact lw v ψ hstd hnt μ inferInstance Φ hΦ (T Φ) hTΦ htrig y O hO hyO

end GlobalTheory.FibreLocality
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewiseStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    (∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T Φ ∈ GlobalTheory.WeilM.schA F κ) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ) →
    (∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      T (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : κ → AF F, (∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → Φ (y + z) = 0) → T Φ y = 0 := by
  first | exact @GlobalTheory.FibreLocality.eq_zero_of_vanish_fibre | exact GlobalTheory.FibreLocality.eq_zero_of_vanish_fibre | (intros; apply GlobalTheory.FibreLocality.eq_zero_of_vanish_fibre <;> assumption)
end
