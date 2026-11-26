module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralTranslateDetOneCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalPairPowerSumVanish
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
open scoped Pointwise

noncomputable section
namespace GlobalTheory.CentreCpt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem val_eq_one_of_pow_eq_one (hN : N ≠ 0) {x : ValueGroupWithZero k} (h : x ^ N = 1) : x = 1 := by
  rcases lt_trichotomy x 1 with h1 | h1 | h1
  · exact absurd h (pow_lt_one₀ zero_le' h1 hN).ne
  · exact h1
  · exact absurd h (one_lt_pow₀ h1 hN).ne'

theorem mem_KO_of_mem_center {w : GL (Fin N) k} (hw : w ∈ Subgroup.center (GL (Fin N) k))
    (hv : valuation k (w : Matrix (Fin N) (Fin N) k).det = 1) : w ∈ KO k (Fin N) := by
  rw [GeneralLinearGroup.center_eq_range_scalar] at hw
  obtain ⟨a, rfl⟩ := hw
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [GlobalTheory.SplitFlip.mem_KO_iff]; exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  have hdet : ((GeneralLinearGroup.scalar (Fin N) a : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det =
      (a : k) ^ N := by
    simp [Matrix.det_diagonal]
  rw [hdet, map_pow] at hv
  have ha : valuation k (a : k) = 1 := val_eq_one_of_pow_eq_one hN.ne' hv
  have hai : valuation k ((a⁻¹ : kˣ) : k) = 1 := by simp [ha]
  have ent : ∀ b : kˣ, valuation k (b : k) = 1 → ∀ i j : Fin N,
      ((GeneralLinearGroup.scalar (Fin N) b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] := by
    intro b hb i j
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact (Valuation.mem_integer_iff _ _).2 hb.le
    · exact zero_mem _
  rw [GlobalTheory.SplitFlip.mem_KO_iff, ← map_inv]
  exact ⟨ent a ha, ent a⁻¹ hai⟩

def vdet (k : Type) [Field k] [ValuativeRel k] (N : ℕ) : GL (Fin N) k →* ValueGroupWithZero k :=
  (valuation k).toMonoidWithZeroHom.toMonoidHom.comp ((Units.coeHom k).comp GeneralLinearGroup.det)

theorem vdet_apply (g : GL (Fin N) k) : vdet k N g = valuation k (g : Matrix (Fin N) (Fin N) k).det := rfl

theorem vdet_eq_one_of_mem_KO {g : GL (Fin N) k} (hg : g ∈ KO k (Fin N)) : vdet k N g = 1 := by
  have hle : ∀ h ∈ KO k (Fin N), vdet k N h ≤ 1 := by
    rintro _ ⟨u, rfl⟩
    rw [vdet_apply]
    change valuation k ((algebraMap 𝒪[k] k).mapMatrix (u : Matrix (Fin N) (Fin N) 𝒪[k])).det ≤ 1
    rw [← RingHom.map_det]
    exact ((Valuation.mem_integer_iff _ _).1 (u.val.det).2)
  have h1 := hle g hg
  have h2 := hle g⁻¹ (inv_mem hg)
  have h3 : vdet k N g * vdet k N g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  refine le_antisymm h1 ?_
  calc (1 : ValueGroupWithZero k) = vdet k N g * vdet k N g⁻¹ := h3.symm
    _ ≤ vdet k N g * 1 := by gcongr
    _ = vdet k N g := mul_one _

theorem exists_compact_center_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (C : Set (GL (Fin N) k)), IsCompact C →
    ∃ D : Set (GL (Fin N) k), IsCompact D ∧ ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ c ∈ C,
      ValuativeRel.valuation k ((z * c : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det = 1 → z * c ∈ D := by
  intro k _ _ _ _ N C hC
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun c : GL (Fin N) k => c • (KO k (Fin N) : Set (GL (Fin N) k)))
    (fun c => GlobalTheory.SplitFlip.isOpen_KO.smul c)
    (fun c _ => Set.mem_iUnion.2 ⟨c, 1, one_mem _, mul_one c⟩)
  let f : GL (Fin N) k → GL (Fin N) k := fun i =>
    if h : ∃ z ∈ Subgroup.center (GL (Fin N) k), vdet k N (z * i) = 1 then h.choose * i else 1
  refine ⟨⋃ i ∈ t, f i • (KO k (Fin N) : Set (GL (Fin N) k)),
    t.isCompact_biUnion fun i _ => GlobalTheory.SplitFlip.isCompact_KO.smul (f i), ?_⟩
  intro z hz c hc hzc
  rw [← vdet_apply] at hzc
  obtain ⟨i, hi, hci⟩ := Set.mem_iUnion₂.1 (ht hc)
  obtain ⟨κ, hκ, rfl⟩ := hci
  change z * (i * κ) ∈ _
  change vdet k N (z * (i * κ)) = 1 at hzc
  have hvκ := vdet_eq_one_of_mem_KO hκ
  have hzi : vdet k N (z * i) = 1 :=
    calc vdet k N (z * i) = vdet k N (z * i) * vdet k N κ := by rw [hvκ, mul_one]
      _ = 1 := by rw [← map_mul, mul_assoc, hzc]
  have hex : ∃ z ∈ Subgroup.center (GL (Fin N) k), vdet k N (z * i) = 1 := ⟨z, hz, hzi⟩
  have hfi : f i = hex.choose * i := dif_pos hex
  obtain ⟨hzc', hv'⟩ := hex.choose_spec
  set zi := hex.choose
  set w := z * zi⁻¹ with hw
  have hwc : w ∈ Subgroup.center (GL (Fin N) k) := mul_mem hz (inv_mem hzc')
  have hwv : vdet k N w = 1 :=
    calc vdet k N w = vdet k N w * vdet k N (zi * i) := by rw [hv', mul_one]
      _ = vdet k N (z * i) := by rw [← map_mul, ← mul_assoc, hw, inv_mul_cancel_right]
      _ = 1 := hzi
  have hwK : w ∈ KO k (Fin N) := mem_KO_of_mem_center hwc (by rw [← vdet_apply]; exact hwv)
  refine Set.mem_iUnion₂.2 ⟨i, hi, ?_⟩
  rw [hfi]
  refine ⟨w * κ, mul_mem hwK hκ, ?_⟩
  have hz' : z = w * zi := by rw [hw, inv_mul_cancel_right]
  have hcomm := Subgroup.mem_center_iff.1 hwc
  change zi * i * (w * κ) = z * (i * κ)
  rw [hz', ← mul_assoc, hcomm (zi * i)]
  simp only [mul_assoc]

end GlobalTheory.CentreCpt
end
end

open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_translate_det_one_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (C : Set (GL (Fin N) k)), IsCompact C → ∃ D : Set (GL (Fin N) k), IsCompact D ∧ ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ c ∈ C, ValuativeRel.valuation k ((z * c : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det = 1 → z * c ∈ D := by
  first | exact @GlobalTheory.CentreCpt.exists_compact_center_mul | exact GlobalTheory.CentreCpt.exists_compact_center_mul | (intros; apply GlobalTheory.CentreCpt.exists_compact_center_mul <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalUnipotentVanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalIdealFrobeniusPowers
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

namespace GlobalTheory.SmGL.CuspSpan

theorem blk_two_apply {α β n : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (c : α ⊕ β ≃ n) (s : α ⊕ β) : GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two c) (c s) = s.isRight := by
  rcases s with p | q
  · rw [← GlobalTheory.SmGL.two_false, GlobalTheory.SmGL.blk_apply]; rfl
  · rw [← GlobalTheory.SmGL.two_true, GlobalTheory.SmGL.blk_apply]; rfl

theorem mem_span_unip (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : GlobalTheory.SmGL.IsCuspidal π) (a b : ℕ)
    (e : Fin N ≃ Fin a ⊕ Fin b) (ha : 0 < a) (hb : 0 < b)
    (u : (Fin a → Fin b → k) → GL (Fin N) k)
    (hu : ∀ X, (u X : Matrix (Fin N) (Fin N) k) =
      Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) (w : V) :
    w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} := by
  have h : a + b = N := by
    have := Fintype.card_congr e
    simpa using this.symm
  have H := ((GlobalTheory.SmGL.CuspMax.isCuspidal_iff_maximal k N V π).1 hπ).2 a b h ha hb
  have H' : Subsingleton (Jacquet π (unipRad k (GlobalTheory.SmGL.two e.symm))) := by
    refine GlobalTheory.SmGL.CuspMax.subsingleton_jacquet_of_perm π (e.trans (stdSum h)) (fun i j hij => ?_) H
    have h1 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two (stdSum h)) ((e.trans (stdSum h)) i) = (e i).isRight :=
      fun i => blk_two_apply (stdSum h) (e i)
    have h2 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two e.symm) i = (e i).isRight := fun i => by
      have := blk_two_apply e.symm (e i)
      rwa [Equiv.symm_apply_apply] at this
    rw [h1, h1] at hij
    rw [h2, h2]
    exact hij
  have htop : twKer π (unipRad k (GlobalTheory.SmGL.two e.symm)) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 H'
  have hw : w ∈ twKer π (unipRad k (GlobalTheory.SmGL.two e.symm)) 1 := htop ▸ Submodule.mem_top
  refine (Submodule.span_le.2 ?_) hw
  rintro _ ⟨n, v, rfl⟩
  refine Submodule.subset_span ⟨fun p q => (n : GL (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q)),
    v, ?_⟩
  have hn : (n : GL (Fin N) k) = u (fun p q => (n : GL (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q))) := by
    have hent := GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries.1 n.2
    have h2 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two e.symm) i = (e i).isRight := fun i => by
      have := blk_two_apply e.symm (e i)
      rwa [Equiv.symm_apply_apply] at this
    ext i j
    rw [hu, Matrix.reindex_apply, Matrix.submatrix_apply]
    simp only [Equiv.symm_symm]
    obtain ⟨s, rfl⟩ := e.symm.surjective i
    obtain ⟨t, rfl⟩ := e.symm.surjective j
    simp only [Equiv.apply_symm_apply]
    rcases s with p | p <;> rcases t with q | q
    · rw [hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₁₁]
      simp [Matrix.one_apply]
    · rw [Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
    · rw [hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₂₁]
      simp [Matrix.one_apply]
    · rw [hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₂₂]
      simp [Matrix.one_apply]
  rw [← hn]
  simp

end GlobalTheory.SmGL.CuspSpan
end

open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_unipotent_vanishing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.SmGL.IsCuspidal π → ∀ (a b : ℕ) (e : Fin N ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ u : (Fin a → Fin b → k) → GL (Fin N) k, (∀ X, (u X : Matrix (Fin N) (Fin N) k) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) → ∀ w : V, w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} := by
  first | exact @GlobalTheory.SmGL.CuspSpan.mem_span_unip | exact GlobalTheory.SmGL.CuspSpan.mem_span_unip | (intros; apply GlobalTheory.SmGL.CuspSpan.mem_span_unip <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnipotentRadicalCoefficientCoinvariantEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnipotentRadicalCoefficientCoinvariantEq
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
open scoped Topology

noncomputable section

namespace GlobalTheory.UnipCoefInt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (a b : ℕ) (s : kˣ) : Set (Fin a → Fin b → k) :=
  Set.univ.pi fun _ => Set.univ.pi fun _ => cball s

theorem mem_box {a b : ℕ} {s : kˣ} {X : Fin a → Fin b → k} :
    X ∈ box a b s ↔ ∀ p q, X p q ∈ cball s := by
  simp [box, Set.mem_univ_pi]

theorem isOpen_box (a b : ℕ) (s : kˣ) : IsOpen (box a b s) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball s

theorem isCompact_box (a b : ℕ) (s : kˣ) : IsCompact (box a b s) :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_cball s

theorem box_mono {a b : ℕ} {s t : kˣ} (h : valuation k (s : k) ≤ valuation k (t : k)) :
    box a b s ⊆ box a b t := by
  intro X hX
  rw [mem_box] at hX ⊢
  intro p q
  exact le_trans (show valuation k (X p q) ≤ valuation k (s : k) from hX p q) h

theorem add_mem_box_iff {a b : ℕ} {s : kˣ} {X Y : Fin a → Fin b → k} (hY : Y ∈ box a b s) :
    X + Y ∈ box a b s ↔ X ∈ box a b s := by
  rw [mem_box] at hY
  simp only [mem_box, Pi.add_apply]
  constructor
  · intro h p q
    simpa using add_mem_cball (h p q) (neg_mem_cball (hY p q))
  · intro h p q
    exact add_mem_cball (h p q) (hY p q)

theorem exists_mem_box {a b : ℕ} (X : Fin a → Fin b → k) : ∃ s : kˣ, X ∈ box a b s := by
  set γ : ValueGroupWithZero k := ∏ pq : Fin a × Fin b, max 1 (valuation k (X pq.1 pq.2)) with hγ
  have h1 : ∀ pq ∈ (Finset.univ : Finset (Fin a × Fin b)), 1 ≤ max 1 (valuation k (X pq.1 pq.2)) :=
    fun _ _ => le_max_left _ _
  have hγ1 : 1 ≤ γ := Finset.one_le_prod' h1
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective γ
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact absurd (hy ▸ hγ1) (by simp)
  refine ⟨Units.mk0 y hy0, mem_box.mpr fun p q => ?_⟩
  show valuation k (X p q) ≤ valuation k y
  rw [hy]
  exact (le_max_right _ _).trans (Finset.single_le_prod' h1 (Finset.mem_univ (p, q)))

theorem directed_box (a b : ℕ) : Directed (· ⊆ ·) (box (k := k) a b) := by
  intro s t
  rcases le_total (valuation k (s : k)) (valuation k (t : k)) with h | h
  · exact ⟨t, box_mono h, subset_rfl⟩
  · exact ⟨s, subset_rfl, box_mono h⟩

theorem exists_subset_box {a b : ℕ} {K : Set (Fin a → Fin b → k)} (hK : IsCompact K) :
    ∃ s : kˣ, K ⊆ box a b s :=
  hK.elim_directed_cover _ (isOpen_box a b) (fun X _ => Set.mem_iUnion.mpr (exists_mem_box X))
    (directed_box a b)

section Meas
variable [MeasurableSpace k] [BorelSpace k]

theorem main : ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.PRep.IsSmooth π → ∀ (a b : ℕ) (μ : Measure (Fin a → Fin b → k)), μ.IsAddHaarMeasure → ∀ u : (Fin a → Fin b → k) → GL (Fin N) k, Continuous u → (∀ X Y, u (X + Y) = u X * u Y) → ∀ (l : Module.Dual ℂ V) (w : V), w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} → ∀ F : (Fin a → Fin b → k) → ℂ, HasCompactSupport F → (∀ X, F X = l (π (u X) w)) → ∫ X, F X ∂μ = 0 := by
  intro N V _ _ π hπ a b μ hμ u hu hadd l w hw F hF hFw
  haveI := secondCountable k
  haveI := t2Space k
  haveI : OpensMeasurableSpace (Fin b → k) := inferInstance
  haveI : OpensMeasurableSpace (Fin a → Fin b → k) := inferInstance
  have hu0 : u 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)

  have hcont : ∀ y : V, Continuous fun X => l (π (u X) y) := by
    intro y
    have hlc : IsLocallyConstant fun X => π (u X) y := by
      refine (IsLocallyConstant.iff_eventually_eq _).mpr fun X₀ => ?_
      have hO : IsOpen ((fun X => u (X - X₀)) ⁻¹' {g | π g y = y}) :=
        (hπ y).preimage (hu.comp (continuous_id.sub continuous_const))
      have hX₀ : X₀ ∈ (fun X => u (X - X₀)) ⁻¹' {g | π g y = y} := by
        simp [hu0]
      filter_upwards [hO.mem_nhds hX₀] with X hX
      have hX' : π (u (X - X₀)) y = y := hX
      have e : X = X₀ + (X - X₀) := by abel
      rw [e, hadd, map_mul, Module.End.mul_apply, hX']
    exact (hlc.comp l).continuous
  have hmeas : ∀ s : kˣ, MeasurableSet (box a b s) := fun s => (isOpen_box a b s).measurableSet
  have hint : ∀ (y : V) (s : kˣ), IntegrableOn (fun X => l (π (u X) y)) (box a b s) μ :=
    fun y s => (hcont y).continuousOn.integrableOn_compact (isCompact_box a b s)

  have hshift : ∀ (y : V) (s : kˣ) (Y : Fin a → Fin b → k), Y ∈ box a b s →
      ∫ X in box a b s, l (π (u (X + Y)) y) ∂μ = ∫ X in box a b s, l (π (u X) y) ∂μ := by
    intro y s Y hY
    rw [← integral_indicator (hmeas s), ← integral_indicator (hmeas s)]
    have : ∀ X, (box a b s).indicator (fun X => l (π (u (X + Y)) y)) X =
        (box a b s).indicator (fun X => l (π (u X) y)) (X + Y) := by
      intro X
      by_cases hX : X ∈ box a b s
      · rw [Set.indicator_of_mem hX, Set.indicator_of_mem ((add_mem_box_iff hY).mpr hX)]
      · rw [Set.indicator_of_notMem hX,
          Set.indicator_of_notMem (fun h => hX ((add_mem_box_iff hY).mp h))]
    simp only [this]
    exact integral_add_right_eq_self (μ := μ) (fun X => (box a b s).indicator (fun X => l (π (u X) y)) X) Y

  have key : ∀ w' ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y},
      ∃ s₀ : kˣ, ∀ s : kˣ, valuation k (s₀ : k) ≤ valuation k (s : k) →
        ∫ X in box a b s, l (π (u X) w') ∂μ = 0 := by
    intro w' hw'
    induction hw' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Y, y, rfl⟩ := hx
      obtain ⟨s₀, hs₀⟩ := exists_mem_box Y
      refine ⟨s₀, fun s hs => ?_⟩
      have hY : Y ∈ box a b s := box_mono hs hs₀
      have e : ∀ X, l (π (u X) (π (u Y) y - y)) = l (π (u (X + Y)) y) - l (π (u X) y) := by
        intro X
        rw [map_sub, map_sub, hadd, map_mul, Module.End.mul_apply]
      simp only [e]
      have hi2 : IntegrableOn (fun X => l (π (u (X + Y)) y)) (box a b s) μ :=
        ((hcont y).comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact (isCompact_box a b s)
      rw [integral_sub hi2 (hint y s), hshift y s Y hY, sub_self]
    | zero => exact ⟨1, fun s _ => by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨s₁, h₁⟩ := hx
      obtain ⟨s₂, h₂⟩ := hz
      rcases le_total (valuation k (s₁ : k)) (valuation k (s₂ : k)) with h | h
      · refine ⟨s₂, fun s hs => ?_⟩
        simp only [map_add (f := _)]
        rw [integral_add (hint x s) (hint z s), h₁ s (h.trans hs), h₂ s hs, add_zero]
      · refine ⟨s₁, fun s hs => ?_⟩
        simp only [map_add (f := _)]
        rw [integral_add (hint x s) (hint z s), h₁ s hs, h₂ s (h.trans hs), add_zero]
    | smul c x _ hx =>
      obtain ⟨s₀, h₀⟩ := hx
      refine ⟨s₀, fun s hs => ?_⟩
      simp only [map_smul, smul_eq_mul]
      rw [integral_const_mul, h₀ s hs, mul_zero]
  obtain ⟨s₀, hs₀⟩ := key w hw
  obtain ⟨s₁, hs₁⟩ := exists_subset_box hF
  obtain ⟨s, hs0, hs1⟩ : ∃ s : kˣ, valuation k (s₀ : k) ≤ valuation k (s : k) ∧
      box a b s₁ ⊆ box a b s := by
    rcases le_total (valuation k (s₀ : k)) (valuation k (s₁ : k)) with h | h
    · exact ⟨s₁, h, subset_rfl⟩
    · exact ⟨s₀, le_rfl, box_mono h⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := box a b s)
    (fun X hX => image_eq_zero_of_notMem_tsupport (fun h => hX (hs1 (hs₁ h))))]
  simp only [hFw]
  exact hs₀ s hs0

end Meas

theorem integral_coef_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.PRep.IsSmooth π → ∀ (a b : ℕ) (μ : Measure (Fin a → Fin b → k)), μ.IsAddHaarMeasure → ∀ u : (Fin a → Fin b → k) → GL (Fin N) k, Continuous u → (∀ X Y, u (X + Y) = u X * u Y) → ∀ (l : Module.Dual ℂ V) (w : V), w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} → ∀ F : (Fin a → Fin b → k) → ℂ, HasCompactSupport F → (∀ X, F X = l (π (u X) w)) → ∫ X, F X ∂μ = 0 := by
  intro k _ _ _ _ _ _
  exact main

end GlobalTheory.UnipCoefInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnipotentRadicalCoefficientCoinvariantEqStatement
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_unipotentRadical_coefficient_coinvariant_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.PRep.IsSmooth π → ∀ (a b : ℕ) (μ : Measure (Fin a → Fin b → k)), μ.IsAddHaarMeasure → ∀ u : (Fin a → Fin b → k) → GL (Fin N) k, Continuous u → (∀ X Y, u (X + Y) = u X * u Y) → ∀ (l : Module.Dual ℂ V) (w : V), w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} → ∀ F : (Fin a → Fin b → k) → ℂ, HasCompactSupport F → (∀ X, F X = l (π (u X) w)) → ∫ X, F X ∂μ = 0 := by
  first | exact @GlobalTheory.UnipCoefInt.integral_coef_eq_zero | exact GlobalTheory.UnipCoefInt.integral_coef_eq_zero | (intros; apply GlobalTheory.UnipCoefInt.integral_coef_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentMapContinuousMulDetOneCompactSuppo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentMapContinuousMulDetOneCompactSuppo
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

namespace GlobalTheory

theorem blockUnipotent_props : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N a b : ℕ) (e : Fin N ≃ Fin a ⊕ Fin b) (u : (Fin a → Fin b → k) → GL (Fin N) k), (∀ X, (u X : Matrix (Fin N) (Fin N) k) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) → Continuous u ∧ (∀ X Y, u (X + Y) = u X * u Y) ∧ (∀ X, (u X : Matrix (Fin N) (Fin N) k).det = 1) ∧ ∀ f : GL (Fin N) k → ℂ, HasCompactSupport f → ∀ g h : GL (Fin N) k, HasCompactSupport (fun X => f (g * (h⁻¹ * u X * h))) := by
  intro k _ _ _ _ N a b e u hu
  have hmul : ∀ X Y, u (X + Y) = u X * u Y := by
    intro X Y
    ext1
    rw [Units.val_mul, hu, hu, hu]
    simp only [Matrix.reindex_apply, Equiv.symm_symm]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    congr 1
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.of_add_of]
    rw [add_comm X Y]
  have h0 : u 0 = 1 := by
    have := hmul 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  have hinv : ∀ X, (u X)⁻¹ = u (-X) := by
    intro X
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← hmul, neg_add_cancel, h0]
  have hentry : ∀ X p q, (u X : Matrix (Fin N) (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q)) = X p q := by
    intro X p q
    rw [hu]; simp [Matrix.reindex_apply]
  have hval : Continuous (fun X => (u X : Matrix (Fin N) (Fin N) k)) := by
    have : (fun X => (u X : Matrix (Fin N) (Fin N) k)) = fun X => Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1) := funext hu
    rw [this]
    refine Continuous.matrix_reindex ?_ _ _
    exact Continuous.matrix_fromBlocks continuous_const continuous_id continuous_const continuous_const
  have hcont : Continuous u := by
    rw [Units.continuous_iff]
    refine ⟨hval, ?_⟩
    simp only [hinv]
    exact hval.comp continuous_neg
  refine ⟨hcont, hmul, ?_, ?_⟩
  · intro X
    rw [hu, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
    simp
  · intro f hf g h
    set C : Set (GL (Fin N) k) := (fun y => h * (g⁻¹ * y) * h⁻¹) '' tsupport f with hC
    have hCc : IsCompact C := hf.isCompact.image (by fun_prop)
    let E : Fin a → Fin b → GL (Fin N) k → k := fun p q y => (y : Matrix (Fin N) (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q))
    have hE : ∀ p q, Continuous (E p q) := by
      intro p q
      exact (continuous_apply_apply _ _).comp (Units.continuous_val (M := Matrix (Fin N) (Fin N) k))
    refine HasCompactSupport.intro (K := Set.pi Set.univ (fun p => Set.pi Set.univ (fun q => E p q '' C))) ?_ ?_
    · exact isCompact_univ_pi (fun p => isCompact_univ_pi (fun q => hCc.image (hE p q)))
    · intro X hX
      by_contra hne
      apply hX
      have hs : g * (h⁻¹ * u X * h) ∈ tsupport f := subset_tsupport _ hne
      have huC : u X ∈ C := ⟨_, hs, by simp [mul_assoc]⟩
      intro p _ q _
      exact ⟨u X, huC, hentry X p q⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentMapContinuousMulDetOneCompactSuppoStatement
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockUnipotentMap_continuous_mul_det_one_compactSupport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N a b : ℕ) (e : Fin N ≃ Fin a ⊕ Fin b) (u : (Fin a → Fin b → k) → GL (Fin N) k), (∀ X, (u X : Matrix (Fin N) (Fin N) k) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) → Continuous u ∧ (∀ X Y, u (X + Y) = u X * u Y) ∧ (∀ X, (u X : Matrix (Fin N) (Fin N) k).det = 1) ∧ ∀ f : GL (Fin N) k → ℂ, HasCompactSupport f → ∀ g h : GL (Fin N) k, HasCompactSupport (fun X => f (g * (h⁻¹ * u X * h))) := by
  first | exact @GlobalTheory.blockUnipotent_props | exact GlobalTheory.blockUnipotent_props | (intros; apply GlobalTheory.blockUnipotent_props <;> assumption)
end
end

open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

namespace GlobalTheory.CuspCutCoef

theorem isCuspFn_cutCoef : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.SmGL.IsCuspidal π →
  ∀ (v : V), ∀ l ∈ smoothPart π.dual,
  ∀ f : GL (Fin N) k → ℂ, (∀ g, f g = if ValuativeRel.valuation k (g : Matrix (Fin N) (Fin N) k).det = 1 then l (π g v) else 0) →
  IsLocallyConstant f ∧ HasCompactSupport f ∧
  ∃ K0 : Subgroup (GL (Fin N) k), IsOpen (K0 : Set (GL (Fin N) k)) ∧ IsCompact (K0 : Set (GL (Fin N) k)) ∧
    (∀ x ∈ K0, ∀ y ∈ K0, ∀ g, f (x * g * y) = f g) ∧
  (∀ (a b : ℕ) (e : Fin N ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → k)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → k) → GL (Fin N) k,
      (∀ X, (u X : Matrix (Fin N) (Fin N) k) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL (Fin N) k, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) := by
  intro k _ _ _ _ _ _ N V _ _ π hπ v l hl f hf
  have hsm : IsSmooth π := hπ.1
  have hU : {g : GL (Fin N) k | π g v = v} ∩ {g | ∀ y, l (π g y) = l y} ∈ nhds (1 : GL (Fin N) k) :=
    Filter.inter_mem ((hsm v).mem_nhds (by simp)) (GlobalTheory.CuspCoef.fix_mem_nhds π l hl)
  obtain ⟨γ, hγ, hsub⟩ := GlobalTheory.CentralExponent.exists_cong_subset hU
  set K0 := GlobalTheory.CentralExponent.cong (Fin N) γ hγ with hK0
  have hK0val : ∀ x ∈ K0, ValuativeRel.valuation k (x : Matrix (Fin N) (Fin N) k).det = 1 := by
    intro x hx
    have h1 : x ∈ GlobalTheory.SplitWeil.KO k (Fin N) :=
      KOne_le_KO (mem_KOne.2 fun i j => (hx i j).trans_le hγ)
    obtain ⟨y, rfl⟩ := h1
    have h2 : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) y : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k).det = algebraMap 𝒪[k] k (y : Matrix (Fin N) (Fin N) 𝒪[k]).det :=
      ((algebraMap 𝒪[k] k).map_det _).symm
    rw [h2]
    exact (Valuation.integer.integers (ValuativeRel.valuation k)).one_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit)
  have hbi : ∀ x ∈ K0, ∀ y ∈ K0, ∀ g, f (x * g * y) = f g := by
    intro x hx y hy g
    rw [hf, hf]
    have hd : ValuativeRel.valuation k ((x * g * y : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det =
        ValuativeRel.valuation k (g : Matrix (Fin N) (Fin N) k).det := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul,
        hK0val x hx, hK0val y hy, one_mul, mul_one]
    rw [hd]
    split_ifs
    · rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, (hsub y hy).1, (hsub x hx).2]
    · rfl
  have hlc : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).2 fun g => ?_
    have hc : Continuous fun y : GL (Fin N) k => g⁻¹ * y := continuous_const.mul continuous_id
    have : ∀ᶠ y in nhds g, g⁻¹ * y ∈ K0 :=
      hc.continuousAt.preimage_mem_nhds (by
        rw [inv_mul_cancel]
        exact (GlobalTheory.CentralExponent.isOpen_cong γ hγ).mem_nhds K0.one_mem)
    filter_upwards [this] with y hy
    have := hbi 1 K0.one_mem (g⁻¹ * y) hy g
    rwa [one_mul, mul_inv_cancel_left] at this
  obtain ⟨C, hC, hCs⟩ := (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k N V π hπ).2 v l hl
  obtain ⟨D, hD, hDs⟩ := GlobalTheory.T.central_translate_det_one_compact k N C hC
  have hcs : HasCompactSupport f := by
    refine HasCompactSupport.intro hD fun g hg => ?_
    rw [hf]
    split_ifs with h
    · by_contra h0
      obtain ⟨z, hz, c, hc, rfl⟩ := hCs g h0
      exact hg (hDs z hz c hc h)
    · rfl
  refine ⟨hlc, hcs, K0, GlobalTheory.CentralExponent.isOpen_cong γ hγ, GlobalTheory.CentralExponent.isCompact_cong γ hγ, hbi, ?_⟩
  intro a b e ha hb μ hμ u hu g h
  obtain ⟨huc, hum, hud, hup⟩ := GlobalTheory.T.blockUnipotentMap_continuous_mul_det_one_compactSupport k N a b e u hu
  by_cases hg : ValuativeRel.valuation k (g : Matrix (Fin N) (Fin N) k).det = 1
  · refine GlobalTheory.T.integral_unipotentRadical_coefficient_coinvariant_eq_zero k N V π hsm a b μ hμ u huc hum (l ∘ₗ π (g * h⁻¹)) (π h v)
      (GlobalTheory.T.cuspidal_unipotent_vanishing k N V π hπ a b e ha hb u hu _) _ (hup f hcs g h) fun X => ?_
    have hd : ValuativeRel.valuation k ((g * (h⁻¹ * u X * h) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det = 1 := by
      simp only [Units.val_mul, Matrix.det_mul, hud X, map_mul, hg, one_mul, mul_one]
      rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, map_one]
    rw [hf, if_pos hd]
    simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply]
  · have : (fun X => f (g * (h⁻¹ * u X * h))) = fun _ => 0 := by
      funext X
      rw [hf, if_neg]
      intro hd
      apply hg
      simp only [Units.val_mul, Matrix.det_mul, hud X, map_mul, mul_one] at hd
      rwa [← map_mul, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, map_one, mul_one] at hd
    rw [this, integral_zero]

end GlobalTheory.CuspCutCoef
