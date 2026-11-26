module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TransW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LintegralMulRightOfMem

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvD
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvDA
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

theorem polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := _root_.PI.AprimeInfA.polish_of_lcsc Y

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem meas_avg (H : Subgroup G) (ν : Measure H) [SFinite ν] {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun g : G => ∫⁻ h, f (g * (h : G)) ∂ν) := by
  have hc : Continuous (fun p : G × H => p.1 * (p.2 : G)) :=
    continuous_fst.mul (continuous_subtype_val.comp continuous_snd)
  exact (hf.comp hc.measurable).lintegral_prod_right'

theorem avg_mul_mem (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞)
    (g : G) (k : H) : ∫⁻ h, f (g * k * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by
  have := lintegral_mul_left_eq_self (μ := ν) (fun h : H => f (g * (h : G))) k
  simpa [mul_assoc] using this

theorem avg_out (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) :
    ∫⁻ h, f ((g : G ⧸ H).out * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hk]
  exact avg_mul_mem H ν f g k

theorem meas_avg_q (H : Subgroup G) (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant]
    {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun q : G ⧸ H => ∫⁻ h, f (q.out * (h : G)) ∂ν) := by
  apply measurable_from_quotient.2
  have : ((fun q : G ⧸ H => ∫⁻ h, f (q.out * (h : G)) ∂ν) ∘ Quotient.mk'') =
      fun g => ∫⁻ h, f (g * (h : G)) ∂ν := by
    funext g
    exact avg_out H ν f g
  rw [this]
  exact meas_avg H ν hf

theorem lint_eq (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] [IsFiniteMeasure ν]
    (μ : Measure G) [SFinite μ] (hr : ∀ k : H, μ.map (· * (k : G)) = μ) (f : G → ℝ≥0∞) (hf : Measurable f) :
    ν univ * ∫⁻ g, f g ∂μ =
      ∫⁻ q, (∫⁻ h, f (q.out * (h : G)) ∂ν) ∂(μ.map (QuotientGroup.mk : G → G ⧸ H)) := by
  rw [lintegral_map (meas_avg_q H ν hf) measurable_quotient_mk'']
  have e1 : ∀ g : G, ∫⁻ h, f ((g : G ⧸ H).out * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := avg_out H ν f
  rw [lintegral_congr e1]
  have hmeas2 : AEMeasurable (Function.uncurry fun (g : G) (h : H) => f (g * (h : G))) (μ.prod ν) := by
    have hc2 : Continuous (fun p : G × H => p.1 * (p.2 : G)) :=
      continuous_fst.mul (continuous_subtype_val.comp continuous_snd)
    exact (hf.comp hc2.measurable).aemeasurable
  rw [lintegral_lintegral_swap hmeas2]
  have : ∀ h : H, ∫⁻ g, f (g * (h : G)) ∂μ = ∫⁻ g, f g ∂μ := fun h => by
    rw [← lintegral_map hf (measurable_mul_const (h : G)), hr h]
  rw [lintegral_congr this, lintegral_const, mul_comm]

variable {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

def iotaQ (H : Subgroup G) (p : G → X) (q : G ⧸ H) : X := p q.out

theorem desc_uniq (H : Subgroup G) (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsMulLeftInvariant]
    (h0 : ν univ ≠ 0) (hfin : ν univ ≠ ∞) (p : G → X) (hp : Continuous p)
    (hpH : ∀ g g' : G, p g = p g' ↔ g⁻¹ * g' ∈ H) (μ₁ μ₂ : Measure G) [SFinite μ₁] [SFinite μ₂]
    (h₁ : ∀ k : H, μ₁.map (· * (k : G)) = μ₁) (h₂ : ∀ k : H, μ₂.map (· * (k : G)) = μ₂)
    (hm : μ₁.map p = μ₂.map p) : μ₁ = μ₂ := by
  classical
  haveI : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.2 hfin⟩
  haveI : IsClosed (H : Set G) := hH
  haveI : PolishSpace G := polish_of_lcsc G
  haveI : PolishSpace (G ⧸ H) := polish_of_lcsc _
  haveI : BorelSpace (G ⧸ H) := CosetSpace.borelSpace
  have hmk : ∀ g : G, iotaQ H p (g : G ⧸ H) = p g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H g
    show p (g : G ⧸ H).out = p g
    rw [hk]
    refine ((hpH g (g * k)).2 ?_).symm
    rw [inv_mul_cancel_left]
    exact k.2
  have hcomp : (iotaQ H p ∘ (QuotientGroup.mk : G → G ⧸ H)) = p := funext hmk
  have hιc : Continuous (iotaQ H p) := by
    rw [(QuotientGroup.isQuotientMap_mk H).continuous_iff, hcomp]
    exact hp
  have hinj : Function.Injective (iotaQ H p) := by
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
    exact (hpH _ _).1 h
  have hemb : MeasurableEmbedding (iotaQ H p) := hιc.measurableEmbedding hinj
  have hπ : Measurable (QuotientGroup.mk : G → G ⧸ H) := measurable_quotient_mk''
  have hq : μ₁.map (QuotientGroup.mk : G → G ⧸ H) = μ₂.map (QuotientGroup.mk : G → G ⧸ H) := by
    calc μ₁.map (QuotientGroup.mk : G → G ⧸ H)
        = ((μ₁.map (QuotientGroup.mk : G → G ⧸ H)).map (iotaQ H p)).comap (iotaQ H p) :=
          (hemb.comap_map _).symm
      _ = (μ₁.map p).comap (iotaQ H p) := by rw [Measure.map_map hemb.measurable hπ, hcomp]
      _ = (μ₂.map p).comap (iotaQ H p) := by rw [hm]
      _ = ((μ₂.map (QuotientGroup.mk : G → G ⧸ H)).map (iotaQ H p)).comap (iotaQ H p) := by
          rw [Measure.map_map hemb.measurable hπ, hcomp]
      _ = μ₂.map (QuotientGroup.mk : G → G ⧸ H) := hemb.comap_map _
  ext S hS
  have hf : Measurable (S.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hS
  have e1 := lint_eq H ν μ₁ h₁ _ hf
  have e2 := lint_eq H ν μ₂ h₂ _ hf
  rw [hq, ← e2, lintegral_indicator_one hS, lintegral_indicator_one hS] at e1
  exact (ENNReal.mul_right_inj h0 hfin).1 e1

end Abstract

end PI.RhsWLim.W.RI
end
end

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W

variable {k r : ℕ}

instance : T2Space (HU.Gp k r) := inferInstanceAs (T2Space {x : Mt k r // x ∈ HU.amb k r})

instance : LocallyCompactSpace (HU.Gp k r) :=
  show LocallyCompactSpace {x : Mt k r // x ∈ HU.amb k r} from
    HU.amb_closed.isClosedEmbedding_subtypeVal.locallyCompactSpace

def stabH (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) : Subgroup (HU.Gp k r) where
  carrier := {g | Matrix.of (HU.inc g) *ᵥ z' = z'}
  mul_mem' {a b} ha hb := by
    show (Matrix.of (HU.inc a) * Matrix.of (HU.inc b) : Mat k r) *ᵥ z' = z'
    rw [← Matrix.mulVec_mulVec]
    rw [show Matrix.of (HU.inc b) *ᵥ z' = z' from hb]
    exact ha
  one_mem' := by
    show (1 : Mat k r) *ᵥ z' = z'
    exact Matrix.one_mulVec z'
  inv_mem' {a} ha := by
    show (Matrix.of (HU.inc a) : Mat k r)⁻¹ *ᵥ z' = z'
    exact inv_fix (HU.uwb_unit (HU.inc_mem a)) ha

theorem continuous_orbV_inc (z' : Fin (2 * r + k + 1) → ℂ) :
    Continuous (fun g : HU.Gp k r => orbV k r z' (HU.inc g)) := (orbV_cont z').comp HU.inc_cont

theorem stabH_closed (z' : Fin (2 * r + k + 1) → ℂ) : IsClosed ((stabH k r z' : Subgroup (HU.Gp k r)) : Set (HU.Gp k r)) :=
  isClosed_eq (continuous_orbV_inc z') continuous_const

def jH (z' : Fin (2 * r + k + 1) → ℂ) (h : stabH k r z') : Mt k r := HU.inc h.1

theorem jH_memb (z' : Fin (2 * r + k + 1) → ℂ) : MeasurableEmbedding (jH (k := k) (r := r) z') :=
  HU.inc_memb.comp (MeasurableEmbedding.subtype_coe (stabH_closed z').measurableSet)

theorem jH_mem (z' : Fin (2 * r + k + 1) → ℂ) (h : stabH k r z') : Matrix.of (jH z' h) ∈ UWset k r z' :=
  ⟨(HU.inc_mem h.1).1, (HU.inc_mem h.1).2, h.2⟩

theorem range_jH (z' : Fin (2 * r + k + 1) → ℂ) :
    range (jH (k := k) (r := r) z') = {x | Matrix.of x ∈ UWset k r z'} := by
  ext x
  constructor
  · rintro ⟨h, rfl⟩
    exact jH_mem z' h
  · intro hx
    exact ⟨⟨⟨x, ⟨hx.1, hx.2.1⟩⟩, hx.2.2⟩, rfl⟩

theorem map_jH {z' : Fin (2 * r + k + 1) → ℂ} {μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z') μW') :
    (μW'.comap (jH z')).map (jH z') = μW' := by
  rw [(jH_memb z').map_comap, range_jH]
  exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hW.2.2.1)

theorem nuH_left {z' : Fin (2 * r + k + 1) → ℂ} {μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z') μW') :
    (μW'.comap (jH z')).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  have hg : Measurable (fun h : stabH k r z' => g * h) := (continuous_const_mul g).measurable
  have e : (jH z' ∘ fun h : stabH k r z' => g * h) = lmulM (Matrix.of (jH z' g)) ∘ jH z' := funext fun h => rfl
  calc (μW'.comap (jH z')).map (fun h => g * h)
      = (((μW'.comap (jH z')).map (fun h => g * h)).map (jH z')).comap (jH z') := ((jH_memb z').comap_map _).symm
    _ = (((μW'.comap (jH z')).map (jH z')).map (lmulM (Matrix.of (jH z' g)))).comap (jH z') := by
        rw [Measure.map_map (jH_memb z').measurable hg, e,
          ← Measure.map_map (HU.lmulM_cont _).measurable (jH_memb z').measurable]
    _ = ((μW'.comap (jH z')).map (jH z')).comap (jH z') := by
        rw [map_jH hW, hW.2.2.2 _ (jH_mem z' g)]
    _ = μW'.comap (jH z') := (jH_memb z').comap_map _

theorem pull_right {z' : Fin (2 * r + k + 1) → ℂ} (ν : Measure (Mt k r))
    (hc : ν {x | Matrix.of x ∉ UWb k r} = 0) (hr : ∀ b ∈ UWset k r z', ν.map (rmulM b) = ν)
    (g : stabH k r z') : (HU.pull ν).map (· * (g : HU.Gp k r)) = HU.pull ν := by
  have hg : Measurable (fun h : HU.Gp k r => h * (g : HU.Gp k r)) := (continuous_mul_const _).measurable
  have e : (HU.inc ∘ fun h : HU.Gp k r => h * (g : HU.Gp k r)) = rmulM (Matrix.of (jH z' g)) ∘ HU.inc :=
    funext fun h => rfl
  calc (HU.pull ν).map (· * (g : HU.Gp k r))
      = (((HU.pull ν).map (· * (g : HU.Gp k r))).map HU.inc).comap HU.inc := (HU.inc_memb.comap_map _).symm
    _ = (((HU.pull ν).map HU.inc).map (rmulM (Matrix.of (jH z' g)))).comap HU.inc := by
        rw [Measure.map_map HU.inc_memb.measurable hg, e,
          ← Measure.map_map (rmulM_cont _).measurable HU.inc_memb.measurable]
    _ = ((HU.pull ν).map HU.inc).comap HU.inc := by
        rw [HU.map_pull ν hc, hr _ (jH_mem z' g)]
    _ = HU.pull ν := HU.inc_memb.comap_map _

theorem orb_fib (z' : Fin (2 * r + k + 1) → ℂ) (g g' : HU.Gp k r) :
    orbV k r z' (HU.inc g) = orbV k r z' (HU.inc g') ↔ g⁻¹ * g' ∈ stabH k r z' := by
  have hu := HU.uwb_unit (HU.inc_mem g)
  show (Matrix.of (HU.inc g) : Mat k r) *ᵥ z' = Matrix.of (HU.inc g') *ᵥ z' ↔
    ((Matrix.of (HU.inc g) : Mat k r)⁻¹ * Matrix.of (HU.inc g')) *ᵥ z' = z'
  constructor
  · intro h
    rw [← Matrix.mulVec_mulVec, ← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem descUniq : DescUniq := by
  intro k r z' μW' hW hfin ν₁ ν₂ hσ₁ hσ₂ hc₁ hc₂ hr₁ hr₂ hm
  have : SigmaFinite μW' := hW.1
  have hl := nuH_left hW
  have hmass : (μW'.comap (jH z')) univ = μW' univ := by
    conv_rhs => rw [← map_jH hW]
    rw [Measure.map_apply (jH_memb z').measurable MeasurableSet.univ, preimage_univ]
  have h0 : (μW'.comap (jH z')) univ ≠ 0 := by
    rw [hmass]
    exact fun h => hW.2.1 (Measure.measure_univ_eq_zero.1 h)
  have hf : (μW'.comap (jH z')) univ ≠ ⊤ := by rw [hmass]; exact hfin
  have : SigmaFinite (HU.pull ν₁) := HU.pull_sigmaFinite ν₁
  have : SigmaFinite (HU.pull ν₂) := HU.pull_sigmaFinite ν₂
  have hpm : ∀ ν : Measure (Mt k r), ν {x | Matrix.of x ∉ UWb k r} = 0 →
      (HU.pull ν).map (fun g => orbV k r z' (HU.inc g)) = ν.map (orbV k r z') := by
    intro ν hc
    have e : (fun g : HU.Gp k r => orbV k r z' (HU.inc g)) = orbV k r z' ∘ HU.inc := rfl
    rw [e, ← Measure.map_map (orbV_cont z').measurable HU.inc_memb.measurable, HU.map_pull ν hc]
  have key := desc_uniq (stabH k r z') (stabH_closed z') (μW'.comap (jH z')) h0 hf
    (fun g => orbV k r z' (HU.inc g)) (continuous_orbV_inc z') (orb_fib z') (HU.pull ν₁) (HU.pull ν₂)
    (pull_right ν₁ hc₁ hr₁) (pull_right ν₂ hc₂ hr₂) (by rw [hpm ν₁ hc₁, hpm ν₂ hc₂, hm])
  rw [← HU.map_pull ν₁ hc₁, ← HU.map_pull ν₂ hc₂, key]

theorem rhsWInv_of_orb (hO : OrbInv) : RhsWInv := rhsWInv_of descUniq rInvNu hO

end PI.RhsWLim.W.RI
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvOA
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

def GhatF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW : Measure (Mt k r))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞) (ζ : ℂ) : ℝ≥0∞ :=
  Gf μW F (embWb k r (secP k r z z' μsec ζ) *ᵥ z')

theorem section_vector_properties (hd : WbData k r z z' μW μW' a a' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    inWb k r (embWb k r (μsec ζ) *ᵥ z') ∧
      herm (Hpk k r) (embWb k r (μsec ζ) *ᵥ z') (embWb k r (μsec ζ) *ᵥ z') = herm (Hpk k r) z' z' ∧
      herm (Hpk k r) (embWb k r (μsec ζ) *ᵥ z') z = ζ := by
  refine ⟨inWb_emb _ hd.z'_mem, herm_both _ _ (MB.emb_mem_UWb (hd.sec.2 ζ hζ).1).1 z' z', ?_⟩
  exact (herm_emb (μsec ζ) z z' hd.z_mem hd.z'_mem).trans (hd.sec.2 ζ hζ).2

theorem meas_Ghat (hd : WbData k r z z' μW μW' a a' μsec) {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞}
    (hF : Measurable F) : Measurable (GhatF k r z z' μW μsec F) := by
  have := hd.haarW.1
  have hc : Continuous (fun m : Fin (k + 1) → Fin (k + 1) → ℂ => embWb k r (Matrix.of m) *ᵥ z') :=
    (cont_emb.comp continuous_id).matrix_mulVec continuous_const
  exact (meas_Gf hF).comp (hc.measurable.comp (meas_secP hd.sec))

theorem orbInv_of (hQ : HypQ) (hU : UnimodK) (hT : FibTrans) : OrbInv := by
  intro k r z z' μW μW' a a' μsec hd s hs F hF
  have := hd.haarW.1
  have := hd.haarW'.1
  obtain ⟨Q, hσQ, hQi, hQc, c, hc0, hcT, hpol⟩ := hQ k r z z' hd.k_pos hd.z_mem hd.z'_mem hd.T_pos hd.T'_pos
  have hfinW : μW Set.univ ≠ ⊤ := by rw [hd.massW]; exact ENNReal.ofReal_ne_top
  have hnull : Q {v | Complex.normSq (herm (Hpk k r) v z) ≤ Tz k r z * Tz k r z'} = 0 := by
    have hS : MeasurableSet {ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'} :=
      measurableSet_le Complex.continuous_normSq.measurable measurable_const
    have h1 := hpol ({ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'}.indicator 1) (measurable_one.indicator hS)
    have e : (fun v => ({ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'}.indicator (1 : ℂ → ℝ≥0∞))
        (herm (Hpk k r) v z)) = ({v | Complex.normSq (herm (Hpk k r) v z) ≤ Tz k r z * Tz k r z'}).indicator 1 :=
      funext fun v => rfl
    have hmS : MeasurableSet {v | Complex.normSq (herm (Hpk k r) v z) ≤ Tz k r z * Tz k r z'} :=
      (cont_herm z).measurable hS
    rw [e, lintegral_indicator_one hmS] at h1
    rw [h1]
    have h2 : (fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        {ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'}.indicator (1 : ℂ → ℝ≥0∞) ζ) =ᵐ[volume] 0 := by
      filter_upwards [circle_ae (Tz k r z * Tz k r z')] with ζ hζ
      show ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        {ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'}.indicator (1 : ℂ → ℝ≥0∞) ζ = 0
      by_cases h : Complex.normSq ζ ≤ Tz k r z * Tz k r z'
      · have hlt : Complex.normSq ζ < Tz k r z * Tz k r z' := lt_of_le_of_ne h hζ
        have h0 : zWeight k (Tz k r z) (Tz k r z') ζ = 0 := by
          unfold zWeight
          rw [if_neg (not_le.2 hlt)]
        rw [h0, ENNReal.ofReal_zero, zero_mul]
      · simp only [Set.indicator, Set.mem_ofPred_eq, h, if_false, mul_zero]
    rw [lintegral_congr_ae h2, Pi.zero_def, lintegral_zero, mul_zero]
  have key : ∀ F' : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞, Measurable F' →
      c * rhsW k r z z' μW μW' μsec (fun x => F' (orbV k r z' x)) =
        ENNReal.ofReal a' * (ENNReal.ofReal a * ∫⁻ v, F' v ∂Q) := by
    intro F' hF'
    have sA : ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * Gf μW F' (embWb k r (μsec ζ) *ᵥ z') =
        ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * GhatF k r z z' μW μsec F' ζ := by
      refine lintegral_congr_ae ?_
      filter_upwards [circle_ae (Tz k r z * Tz k r z')] with ζ hζ
      by_cases h : Tz k r z * Tz k r z' < Complex.normSq ζ
      · unfold GhatF
        rw [secP_eq h]
      · have h0 : zWeight k (Tz k r z) (Tz k r z') ζ = 0 := by
          unfold zWeight
          rw [if_neg (not_le.2 (lt_of_le_of_ne (not_lt.1 h) hζ))]
        rw [h0, ENNReal.ofReal_zero, zero_mul, zero_mul]
    have sB : ∫⁻ v, GhatF k r z z' μW μsec F' (herm (Hpk k r) v z) ∂Q = ∫⁻ v, Gf μW F' v ∂Q := by
      refine lintegral_congr_ae ?_
      have hg1 : ∀ᵐ v ∂Q, inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z' := by
        rw [ae_iff]
        exact hQc
      have hg2 : ∀ᵐ v ∂Q, Tz k r z * Tz k r z' < Complex.normSq (herm (Hpk k r) v z) := by
        rw [ae_iff]
        exact measure_mono_null (fun v (hv : ¬ (Tz k r z * Tz k r z' < _)) => not_lt.1 hv) hnull
      filter_upwards [hg1, hg2] with v hv1 hv2
      obtain ⟨p1, p2, p3⟩ := section_vector_properties hd hv2
      unfold GhatF
      rw [secP_eq hv2]
      exact Gf_fib hU hT hd.haarW hfinW hd.z_mem hd.T_pos hF' p1 hv1.1 (p2.trans hv1.2.symm) p3
    rw [rhs_orb hd F', sA, ← hd.massW, ← avg_Q Q hQi hd.haarW hF', ← sB, hpol _ (meas_Ghat hd hF')]
    ring
  have hmv : Measurable (fun v : Fin (2 * r + k + 1) → ℂ => s *ᵥ v) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have k1 := key (fun v => F (s *ᵥ v)) (hF.comp hmv)
  have k2 := key F hF
  have eQ : ∫⁻ v, F (s *ᵥ v) ∂Q = ∫⁻ v, F v ∂Q := by
    rw [← lintegral_map hF hmv, hQi s hs]
  rw [eQ, ← k2] at k1
  exact (ENNReal.mul_right_inj hc0 hcT).1 k1

theorem rhsWInv_of_hyp (hQ : HypQ) (hU : UnimodK) (hT : FibTrans) : RhsWInv :=
  rhsWInv_of_orb (orbInv_of hQ hU hT)

end PI.RhsWLim.W.RI
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvU
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W

theorem fin_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [IsFiniteMeasure ν] [ν.IsMulLeftInvariant] (h0 : ν ≠ 0)
    (g : G) : ν.map (· * g) = ν := by
  have hg : Measurable (· * g : G → G) := measurable_mul_const g
  have hL : (ν.map (· * g)).IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    rw [Measure.map_map (measurable_const_mul h) hg]
    have e : ((h * ·) ∘ (· * g) : G → G) = (· * g) ∘ (h * ·) := funext fun x => (mul_assoc h x g).symm
    rw [e, ← Measure.map_map hg (measurable_const_mul h), map_mul_left_eq_self]
  have hU : (ν.map (· * g)) univ = ν univ := by
    rw [Measure.map_apply hg MeasurableSet.univ, preimage_univ]
  have hu0 : ν univ ≠ 0 := fun h => h0 (Measure.measure_univ_eq_zero.1 h)
  have hfin : IsFiniteMeasure (ν.map (· * g)) := inferInstance
  rw [measure_eq_div_smul (ν.map (· * g)) ν (s := univ) hu0 (measure_ne_top ν univ), hU,
    ENNReal.div_self hu0 (measure_ne_top ν univ), one_smul]

theorem unimodK : UnimodK := by
  intro k r z μ hW hfin b hb
  have : SigmaFinite μ := hW.1
  have hl := nuH_left hW
  have hmass : (μ.comap (jH z)) univ = μ univ := by
    conv_rhs => rw [← map_jH hW]
    rw [Measure.map_apply (jH_memb z).measurable MeasurableSet.univ, preimage_univ]
  have : IsFiniteMeasure (μ.comap (jH z)) := ⟨by rw [hmass]; exact lt_top_iff_ne_top.2 hfin⟩
  have h0 : μ.comap (jH z) ≠ 0 := by
    intro h
    apply hW.2.1
    rw [← map_jH hW, h, Measure.map_zero]
  have : SecondCountableTopology (stabH k r z) :=
    inferInstanceAs (SecondCountableTopology ((stabH k r z : Set (HU.Gp k r))))
  have : BorelSpace (stabH k r z) := inferInstanceAs (BorelSpace ((stabH k r z : Set (HU.Gp k r))))
  let g : stabH k r z := ⟨⟨fun i j => b i j, ⟨hb.1, hb.2.1⟩⟩, hb.2.2⟩
  have hR := fin_right (μ.comap (jH z)) h0 g
  have e : rmulM b ∘ jH z = jH z ∘ (· * g) := funext fun x => rfl
  calc μ.map (rmulM b) = ((μ.comap (jH z)).map (jH z)).map (rmulM b) := by rw [map_jH hW]
    _ = ((μ.comap (jH z)).map (· * g)).map (jH z) := by
        rw [Measure.map_map (rmulM_cont b).measurable (jH_memb z).measurable, e,
          ← Measure.map_map (jH_memb z).measurable (measurable_mul_const g)]
    _ = μ := by rw [hR, map_jH hW]

end PI.RhsWLim.W.RI
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvF
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros

variable {k r : ℕ}

section Form

variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)

theorem herm_add_left (x y w : Fin n → ℂ) : herm H (x + y) w = herm H x w + herm H y w := by
  unfold herm
  rw [Matrix.mulVec_add, dotProduct_add]

theorem herm_sub_left (x y w : Fin n → ℂ) : herm H (x - y) w = herm H x w - herm H y w := by
  unfold herm
  rw [Matrix.mulVec_sub, dotProduct_sub]

theorem herm_smul_left (c : ℂ) (x w : Fin n → ℂ) : herm H (c • x) w = c * herm H x w := by
  unfold herm
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_add_right (x w y : Fin n → ℂ) : herm H x (w + y) = herm H x w + herm H x y := by
  unfold herm
  rw [star_add, add_dotProduct]

theorem herm_sub_right (x w y : Fin n → ℂ) : herm H x (w - y) = herm H x w - herm H x y := by
  unfold herm
  rw [star_sub, sub_dotProduct]

theorem herm_smul_right (c : ℂ) (x w : Fin n → ℂ) : herm H x (c • w) = star c * herm H x w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem herm_symm (hH : Hᴴ = H) (x w : Fin n → ℂ) : herm H w x = star (herm H x w) := by
  unfold herm
  conv_lhs => rw [Matrix.star_dotProduct]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]

theorem herm_conj (g : Matrix (Fin n) (Fin n) ℂ) (x w : Fin n → ℂ) :
    herm H (g *ᵥ x) (g *ᵥ w) = herm (gᴴ * H * g) x w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem herm_single (i j : Fin n) : herm H (Pi.single j 1) (Pi.single i 1) = H i j := by
  unfold herm
  rw [Matrix.mulVec_single_one]
  simp [dotProduct, Pi.single_apply]

theorem unit_of_form (g : Matrix (Fin n) (Fin n) ℂ) (h : ∀ x w, herm H (g *ᵥ x) (g *ᵥ w) = herm H x w) :
    gᴴ * H * g = H := by
  ext i j
  have e := h (Pi.single j 1) (Pi.single i 1)
  rw [herm_conj, herm_single, herm_single] at e
  exact e

def tmat (κ : ℂ) (d : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + Matrix.of fun i j => κ * d i * (star d ᵥ* H) j

theorem tmat_mulVec (κ : ℂ) (d x : Fin n → ℂ) : tmat H κ d *ᵥ x = x + (κ * herm H x d) • d := by
  ext i
  simp only [tmat, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  unfold herm
  rw [Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

end Form

theorem herm_wb {x w : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (hw : inWb k r w) :
    herm (Hpk k r) x w = herm (Hb k) (wbPart k r x) (wbPart k r w) := by
  conv_lhs => rw [← inWb_eq hx, ← inWb_eq hw]
  unfold herm
  rw [Matrix.mulVec_mulVec, MB.Hpk_Em, ← Matrix.mulVec_mulVec, em_dot]

theorem herm_hb (x w : Fin (k + 1) → ℂ) :
    herm (Hb k) x w = (∑ j : Fin k, star (w (Fin.castSucc j)) * x (Fin.castSucc j)) - star (w (Fin.last k)) * x (Fin.last k) := by
  unfold herm Hb
  simp only [dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_castSucc, Pi.star_apply]
  simp only [Fin.castSucc_ne_last, if_false, one_mul, if_true, neg_one_mul, mul_neg]
  ring

theorem herm_self_hb (x : Fin (k + 1) → ℂ) :
    herm (Hb k) x x = ((∑ j : Fin k, Complex.normSq (x (Fin.castSucc j)) - Complex.normSq (x (Fin.last k)) : ℝ) : ℂ) := by
  rw [herm_hb]
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self]
  rfl

theorem wb_posdef {z d : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (hd : inWb k r d)
    (hdz : herm (Hpk k r) d z = 0) (hdd : herm (Hpk k r) d d = 0) : d = 0 := by
  rw [herm_wb hd hz, herm_hb] at hdz
  rw [herm_wb hd hd, herm_self_hb] at hdd
  have hT' : 0 < Complex.normSq (wbPart k r z (Fin.last k)) -
      ∑ j : Fin k, Complex.normSq (wbPart k r z (Fin.castSucc j)) := by
    unfold Tz at hT
    rw [herm_wb hz hz, herm_self_hb, Complex.ofReal_re] at hT
    linarith
  set X : Fin k → ℂ := fun j => wbPart k r d (Fin.castSucc j)
  set Z : Fin k → ℂ := fun j => wbPart k r z (Fin.castSucc j)
  set xk := wbPart k r d (Fin.last k)
  set zk := wbPart k r z (Fin.last k)
  have hX : ∑ j, Complex.normSq (X j) = Complex.normSq xk := by
    have := Complex.ofReal_injective (hdd.trans Complex.ofReal_zero.symm)
    linarith
  have hdz' : star zk * xk = ∑ j, star (Z j) * X j := by
    rw [sub_eq_zero] at hdz
    exact hdz.symm
  have hxk : xk = 0 := by
    by_contra hne
    have h1 : ‖zk‖ * ‖xk‖ ≤ ∑ j, ‖Z j‖ * ‖X j‖ := by
      calc ‖zk‖ * ‖xk‖ = ‖star zk * xk‖ := by rw [norm_mul, norm_star]
        _ = ‖∑ j, star (Z j) * X j‖ := by rw [hdz']
        _ ≤ ∑ j, ‖star (Z j) * X j‖ := norm_sum_le _ _
        _ = ∑ j, ‖Z j‖ * ‖X j‖ := by simp only [norm_mul, norm_star]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖Z j‖) (fun j => ‖X j‖)
    have h3 : (‖zk‖ * ‖xk‖) ^ 2 ≤ (∑ j, ‖Z j‖ ^ 2) * (∑ j, ‖X j‖ ^ 2) :=
      (pow_le_pow_left₀ (by positivity) h1 2).trans h2
    simp only [← Complex.normSq_eq_norm_sq] at h3
    rw [hX, mul_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq] at h3
    have hpos : 0 < Complex.normSq xk := Complex.normSq_pos.2 hne
    nlinarith
  have hX0 : ∀ j, X j = 0 := by
    intro j
    rw [hxk, map_zero] at hX
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (X j))).1 hX j (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 this
  have hb : wbPart k r d = 0 := by
    ext m
    induction m using Fin.lastCases with
    | last => exact hxk
    | cast j => exact hX0 j
  rw [← inWb_eq hd, hb, Matrix.mulVec_zero]

theorem herm_e_wb {d : Fin (2 * r + k + 1) → ℂ} (hd : inWb k r d) {j : Fin (2 * r + k + 1)}
    (hj : j.val < r ∨ r + k < j.val) : herm (Hpk k r) (bvec j) d = 0 := by
  unfold herm bvec
  rw [Matrix.mulVec_single_one]
  refine Finset.sum_eq_zero fun i _ => ?_
  show star (d i) * Hpk k r i j = 0
  rw [HU.hpk_row]
  split_ifs with h
  · by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hd i hi, star_zero, zero_mul]
    · exfalso
      rw [Fin.ext_iff] at h
      unfold HU.tau at h
      simp only [hi, if_false] at h
      omega
  · exact mul_zero _

theorem uwset_one (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mat k r) ∈ UWset k r z :=
  ⟨HU.uh_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩

theorem fibTrans : FibTrans := by
  intro k r z v v' hz hv hv' hT h1 h2
  by_cases hvv : v = v'
  · exact ⟨1, uwset_one z, by rw [hvv, Matrix.one_mulVec]⟩
  have hsym := herm_symm (Hpk k r) MB.hpk_herm
  set d := v - v' with hddef
  have hd : inWb k r d := fun i hi => by simp only [hddef, Pi.sub_apply, hv i hi, hv' i hi, sub_zero]
  have hdz : herm (Hpk k r) d z = 0 := by rw [herm_sub_left, h2, sub_self]
  have hN : herm (Hpk k r) d d = herm (Hpk k r) v d + star (herm (Hpk k r) v d) := by
    simp only [hddef, herm_sub_left, herm_sub_right, star_sub]
    rw [← hsym v v, ← hsym v v', ← h1]
    ring
  have hne : herm (Hpk k r) v d ≠ 0 := by
    intro h0
    have : herm (Hpk k r) d d = 0 := by rw [hN, h0, star_zero, add_zero]
    exact hvv (sub_eq_zero.1 (wb_posdef hz hT hd hdz this))
  have hne' : star (herm (Hpk k r) v d) ≠ 0 := star_ne_zero.2 hne
  set κ : ℂ := -(herm (Hpk k r) v d)⁻¹ with hκ
  have hTx := tmat_mulVec (Hpk k r) κ d
  have hfix : ∀ x, herm (Hpk k r) x d = 0 → tmat (Hpk k r) κ d *ᵥ x = x := by
    intro x hx
    rw [hTx, hx, mul_zero, zero_smul, add_zero]
  have hbr : κ + star κ + κ * star κ * herm (Hpk k r) d d = 0 := by
    rw [hN, hκ, star_neg, star_inv₀]
    field_simp
    ring
  have hunit : ∀ x w, herm (Hpk k r) (tmat (Hpk k r) κ d *ᵥ x) (tmat (Hpk k r) κ d *ᵥ w) = herm (Hpk k r) x w := by
    intro x w
    rw [hTx, hTx, herm_add_left, herm_add_right, herm_add_right, herm_smul_left, herm_smul_left,
      herm_smul_right, herm_smul_right, hsym w d, star_mul']
    linear_combination (herm (Hpk k r) x d * star (herm (Hpk k r) w d)) * hbr
  have hzd : herm (Hpk k r) z d = 0 := by rw [hsym d z, hdz, star_zero]
  refine ⟨tmat (Hpk k r) κ d, ⟨unit_of_form _ _ hunit, fun a => ⟨hfix _ (herm_e_wb hd ?_), hfix _ (herm_e_wb hd ?_)⟩,
    hfix z hzd⟩, ?_⟩
  · left
    exact a.isLt
  · right
    show r + k < 2 * r + k - a.val
    omega
  · rw [hTx, hκ, neg_mul, inv_mul_cancel₀ hne, neg_one_smul, hddef]
    abel

end PI.RhsWLim.W.RI
end
end

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W

theorem rhsWInv_of_hypQ (hQ : HypQ) : RhsWInv := rhsWInv_of_hyp hQ unimodK fibTrans

end PI.RhsWLim.W.RI
