module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerSetEqRangeNormalForm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormCongruenceLiftSmallGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRepsOfFinite
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsBlockOfFrame
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RefLatticeStabilizerMiddleBottomLayers
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerFromCoordinatesProductLaw
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatDetHMapInjectiveIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualFlagOfSaturatedIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalSetRowsMiddleSpace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureCommonStabilizerCoordsBoxImage
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureCommonStabilizerCoordsBoxImage
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefMeas

theorem image_meas {ι X Y Z : Type} [Fintype ι] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [StandardBorelSpace X] [StandardBorelSpace Y] [StandardBorelSpace Z]
    (μ : Measure X) [SigmaFinite μ] (ν : Measure Z) (c : X → Y) (hc : Measurable c) (hi : Function.Injective c)
    (a : Z → ι → X) (ha : MeasurePreserving a ν (Measure.pi fun _ : ι => μ)) (hai : Function.Injective a)
    (S : Set Z) (hS : MeasurableSet S) :
    MeasurableSet ((fun p v => c (a p v)) '' S) ∧
      Measure.pi (fun _ : ι => μ.map c) ((fun p v => c (a p v)) '' S) = ν S := by
  have he : MeasurableEmbedding c := hc.measurableEmbedding hi
  haveI : SigmaFinite (μ.map c) := he.sigmaFinite_map
  have h1 : MeasurePreserving (fun (q : ι → X) (v : ι) => c (q v)) (Measure.pi fun _ : ι => μ)
      (Measure.pi fun _ : ι => μ.map c) :=
    measurePreserving_pi _ _ fun _ => ⟨hc, rfl⟩
  have h2 : MeasurePreserving (fun (p : Z) (v : ι) => c (a p v)) ν (Measure.pi fun _ : ι => μ.map c) := h1.comp ha
  have hinj : Function.Injective (fun (p : Z) (v : ι) => c (a p v)) := fun p q h =>
    hai (funext fun v => hi (congrFun h v))
  have hm : MeasurableSet ((fun p v => c (a p v)) '' S) := hS.image_of_measurable_injOn h2.measurable hinj.injOn
  refine ⟨hm, ?_⟩
  rw [← h2.measure_preimage hm.nullMeasurableSet, Set.preimage_image_eq _ hinj]

theorem box_meas : ∀ (ι : Type) [Fintype ι] (k r j : ℕ) (β : Fin r → ℕ), Monotone β → (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) → MeasurePreserving (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) volume (Measure.pi fun _ : ι => (volume : Measure ((UTin β → ℂ) × PTop k r j))) → ∀ (F₁ : UTin β → Set (ι → ℂ)) (F₂ : {a : Fin r // j ≤ a.val} → Set (ι → Fin (k + 1) → ℂ)) (F₃ : {p : UT r // j ≤ p.1.1.val} → Set (ι → ℂ)) (F₄ : {a : Fin r // j ≤ a.val} → Set (ι → ℝ)), (∀ i, MeasurableSet (F₁ i)) → (∀ i, MeasurableSet (F₂ i)) → (∀ i, MeasurableSet (F₃ i)) → (∀ i, MeasurableSet (F₄ i)) → ∀ Ω : Set (ι → Mt k r), Ω = (fun (p : Crd ι k r j β) (v : ι) => (Matrix.of.symm (CC p v) : Mt k r)) '' (Set.pi Set.univ F₁ ×ˢ Set.pi Set.univ F₂ ×ˢ (Set.pi Set.univ F₃ ×ˢ Set.pi Set.univ F₄)) → MeasurableSet Ω ∧ Measure.pi (fun _ : ι => lebR0 k r j β) Ω = (∏ i, volume (F₁ i)) * ((∏ i, volume (F₂ i)) * ((∏ i, volume (F₃ i)) * ∏ i, volume (F₄ i))) := by
  intro ι _ k r j β hm hβ hat F₁ F₂ F₃ F₄ h₁ h₂ h₃ h₄ Ω hΩ
  obtain ⟨hl, -, hinj, -⟩ := Swap.range_eq_and_injective_parabolic_unipotent_product k r j β hm hβ
  haveI s1 : SigmaFinite (volume : Measure (Swap.STop r j)) := Measure.prod.instSigmaFinite
  haveI s2 : SigmaFinite (volume : Measure (PTop k r j)) := Measure.prod.instSigmaFinite
  haveI s3 : SigmaFinite (volume : Measure ((UTin β → ℂ) × PTop k r j)) := Measure.prod.instSigmaFinite
  haveI b1 : BorelSpace (Swap.STop r j) := Prod.borelSpace
  haveI b2 : BorelSpace (PTop k r j) := Prod.borelSpace
  haveI b3 : BorelSpace ((UTin β → ℂ) × PTop k r j) := Prod.borelSpace
  have hG : Continuous fun q : (UTin β → ℂ) × PTop k r j =>
      (Matrix.of.symm (pTop k r j q.2 * uEmb k r (upperIn β q.1)) : Mt k r) :=
    (Swap.cont_pTop.comp continuous_snd).matrix_mul ((GlobalTheory.Amp.Swap.cont_uEmb k r).comp
      ((Swap.extZ (fun p : UT r => β p.1.1 = β p.1.2) ℂ).continuous_of_finiteDimensional.comp continuous_fst))
  have hS : MeasurableSet ((Set.pi Set.univ F₁ ×ˢ Set.pi Set.univ F₂ ×ˢ (Set.pi Set.univ F₃ ×ˢ Set.pi Set.univ F₄)) : Set (Crd ι k r j β)) :=
    (MeasurableSet.univ_pi h₁).prod ((MeasurableSet.univ_pi h₂).prod ((MeasurableSet.univ_pi h₃).prod (MeasurableSet.univ_pi h₄)))
  haveI d1 : StandardBorelSpace (Swap.STop r j) := StandardBorelSpace.prod
  haveI d2 : StandardBorelSpace (PTop k r j) := StandardBorelSpace.prod
  haveI d3 : StandardBorelSpace ((UTin β → ℂ) × PTop k r j) := StandardBorelSpace.prod
  haveI d4 : StandardBorelSpace (Mt k r) := StandardBorelSpace.pi_countable
  haveI d5 : StandardBorelSpace (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ)) := StandardBorelSpace.prod
  haveI d6 : StandardBorelSpace ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) := StandardBorelSpace.pi_countable
  haveI d7 : StandardBorelSpace (({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))) := StandardBorelSpace.prod
  haveI d8 : StandardBorelSpace (Crd ι k r j β) := StandardBorelSpace.prod
  have key := image_meas (volume : Measure ((UTin β → ℂ) × PTop k r j)) volume _ hG.measurable
    (Matrix.of.symm.injective.comp hinj) atP hat usage₂.1 _ hS
  rw [← hl] at key
  subst hΩ
  refine ⟨key.1, key.2.trans ?_⟩
  haveI t1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))) :=
    Measure.prod.instSigmaFinite
  haveI t3 : SigmaFinite (volume : Measure (ι → Fin (k + 1) → ℂ)) := Measure.pi.sigmaFinite _
  haveI t4 : SigmaFinite (volume : Measure ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ)) := Measure.pi.sigmaFinite _
  haveI t2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ)))) :=
    Measure.prod.instSigmaFinite
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    volume_pi_pi, volume_pi_pi, volume_pi_pi, volume_pi_pi]

end GlobalTheory.DegVol.RefMeas
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureCommonStabilizerCoordsBoxImageStatement
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_commonStabilizerCoords_box_image : ∀ (ι : Type) [Fintype ι] (k r j : ℕ) (β : Fin r → ℕ), Monotone β → (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) → MeasurePreserving (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) volume (Measure.pi fun _ : ι => (volume : Measure ((UTin β → ℂ) × PTop k r j))) → ∀ (F₁ : UTin β → Set (ι → ℂ)) (F₂ : {a : Fin r // j ≤ a.val} → Set (ι → Fin (k + 1) → ℂ)) (F₃ : {p : UT r // j ≤ p.1.1.val} → Set (ι → ℂ)) (F₄ : {a : Fin r // j ≤ a.val} → Set (ι → ℝ)), (∀ i, MeasurableSet (F₁ i)) → (∀ i, MeasurableSet (F₂ i)) → (∀ i, MeasurableSet (F₃ i)) → (∀ i, MeasurableSet (F₄ i)) → ∀ Ω : Set (ι → Mt k r), Ω = (fun (p : Crd ι k r j β) (v : ι) => (Matrix.of.symm (CC p v) : Mt k r)) '' (Set.pi Set.univ F₁ ×ˢ Set.pi Set.univ F₂ ×ˢ (Set.pi Set.univ F₃ ×ˢ Set.pi Set.univ F₄)) → MeasurableSet Ω ∧ Measure.pi (fun _ : ι => lebR0 k r j β) Ω = (∏ i, volume (F₁ i)) * ((∏ i, volume (F₂ i)) * ((∏ i, volume (F₃ i)) * ∏ i, volume (F₄ i))) := by
  first | exact @GlobalTheory.DegVol.RefMeas.box_meas | exact GlobalTheory.DegVol.RefMeas.box_meas | (intros; apply GlobalTheory.DegVol.RefMeas.box_meas <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LayerCovolumeProductPowTwoSidedBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LayerCovolumeProductPowTwoSidedBounds
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCov

theorem prod_pow_bounds : ∀ (v : ℝ) (f k r m a b : ℕ) (x : ℝ≥0∞), 1 ≤ v → m ≤ r → a ≤ r ^ 2 → b ≤ r ^ 2 → ENNReal.ofReal ((8 * v) ^ (-(f : ℝ))) ^ m ≤ x → x ≤ ENNReal.ofReal ((8 * v) ^ (f : ℝ)) ^ m → ENNReal.ofReal (v ^ (k * m * f) / (8 * v) ^ (2 * (r + 1) ^ 2 * f)) ≤ ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m * (ENNReal.ofReal (v ^ f) ^ b * x)) ∧ ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m * (ENNReal.ofReal (v ^ f) ^ b * x)) ≤ ENNReal.ofReal (v ^ (k * m * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f)) := by
  intro v f k r m a b x hv hm ha hb hlo hhi
  have hv0 : 0 < v := by linarith
  have hw1 : 1 ≤ 8 * v := by linarith
  have hw0 : 0 < 8 * v := by linarith
  have hvw : v ≤ 8 * v := by linarith
  have hvf : 0 ≤ v ^ f := by positivity
  have key : ∀ y : ℝ, 0 ≤ y →
      ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m *
        (ENNReal.ofReal (v ^ f) ^ b * ENNReal.ofReal y ^ m)) =
      ENNReal.ofReal (v ^ (k * m * f) * (v ^ (f * (a + m + b)) * y ^ m)) := by
    intro y hy
    rw [← ENNReal.ofReal_pow hvf, ← ENNReal.ofReal_pow hvf, ← ENNReal.ofReal_pow hy,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [Real.rpow_neg hw0.le, Real.rpow_natCast] at hlo
  rw [Real.rpow_natCast] at hhi
  constructor
  · refine le_trans ?_ (mul_le_mul_right (mul_le_mul_right (mul_le_mul_right hlo _) _) _)
    rw [key _ (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : 1 ≤ v ^ (f * (a + m + b)) := one_le_pow₀ hv
    have h2 : ((8 * v) ^ (2 * (r + 1) ^ 2 * f))⁻¹ ≤ ((8 * v) ^ f)⁻¹ ^ m := by
      rw [inv_pow, ← pow_mul]
      apply inv_anti₀ (by positivity)
      apply pow_le_pow_right₀ hw1
      rw [mul_comm f m]
      apply Nat.mul_le_mul_right
      nlinarith
    exact h2.trans (le_mul_of_one_le_left (by positivity) h1)
  · refine le_trans (mul_le_mul_right (mul_le_mul_right (mul_le_mul_right hhi _) _) _) ?_
    rw [key _ (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : v ^ (f * (a + m + b)) ≤ (8 * v) ^ (f * (a + m + b)) :=
      pow_le_pow_left₀ hv0.le hvw _
    calc v ^ (f * (a + m + b)) * ((8 * v) ^ f) ^ m
        ≤ (8 * v) ^ (f * (a + m + b)) * ((8 * v) ^ f) ^ m :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (8 * v) ^ ((a + m + b + m) * f) := by ring
      _ ≤ (8 * v) ^ (2 * (r + 1) ^ 2 * f) := by
          apply pow_le_pow_right₀ hw1
          apply Nat.mul_le_mul_right
          nlinarith

end GlobalTheory.DegVol.RefCov
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LayerCovolumeProductPowTwoSidedBoundsStatement
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.layer_covolume_product_pow_two_sided_bounds : ∀ (v : ℝ) (f k r m a b : ℕ) (x : ℝ≥0∞), 1 ≤ v → m ≤ r → a ≤ r ^ 2 → b ≤ r ^ 2 → ENNReal.ofReal ((8 * v) ^ (-(f : ℝ))) ^ m ≤ x → x ≤ ENNReal.ofReal ((8 * v) ^ (f : ℝ)) ^ m → ENNReal.ofReal (v ^ (k * m * f) / (8 * v) ^ (2 * (r + 1) ^ 2 * f)) ≤ ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m * (ENNReal.ofReal (v ^ f) ^ b * x)) ∧ ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m * (ENNReal.ofReal (v ^ f) ^ b * x)) ≤ ENNReal.ofReal (v ^ (k * m * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f)) := by
  first | exact @GlobalTheory.DegVol.RefCov.prod_pow_bounds | exact GlobalTheory.DegVol.RefCov.prod_pow_bounds | (intros; apply GlobalTheory.DegVol.RefCov.prod_pow_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnimodularTraceOnMiddleSpaceLift
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnimodularTraceOnMiddleSpaceLift
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

noncomputable section

open Formalism.HermitianLatticeCounting.P

namespace GlobalTheory.DegCnt.WnLat

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : NF H r)

def pr : V →ₗ[K] V := LinearMap.id - NFGeom.proj N

theorem pr_add (x : V) : pr N x + NFGeom.proj N x = x := by simp [pr]

theorem Wn_perp_Ist {y : V} (hy : y ∈ N.Wn) : ∀ u ∈ N.Ist, H.B y u = 0 :=
  (mem_perp_iff H _ _).1 ((NFGeom.mem_perp_sup _ _ _).1 hy).2

theorem Wn_perp_II {y : V} (hy : y ∈ N.Wn) {x : V} (hx : x ∈ II N.F N.F') : H.B y x = 0 :=
  (mem_perp_iff H _ _).1 ((NFGeom.mem_perp_sup _ _ _).1 hy).1 x (Submodule.mem_sup_left hx.1)

theorem pr_of_Wn {y : V} (hy : y ∈ N.Wn) : pr N y = y := by
  simp [pr, NFGeom.proj_zero N (Wn_perp_Ist N hy)]

theorem pr_II {x : V} (hx : x ∈ II N.F N.F') : pr N x = 0 := by
  simp [pr, NFGeom.proj_II N hx]

theorem pr_mem_Wn {x : V} (hx : x ∈ uPerp N.F N.F') : pr N x ∈ N.Wn :=
  (NFGeom.mem_perp_sup _ _ _).2
    ⟨Submodule.sub_mem _ hx (NFGeom.II_le_uPerp N (NFGeom.proj_mem N x)), NFGeom.sub_proj_perp N x⟩

theorem Wn_le_uPerp : N.Wn ≤ uPerp N.F N.F' := by
  rw [NFGeom.uPerp_eq N]; exact le_sup_left

theorem orthogonal_perp_z {w : V} (hw : w ∈ N.Wt) : H.B w N.F.z = 0 :=
  (mem_perp_iff H _ _).1 ((NFGeom.mem_perp_sup _ _ _).1 hw).1 _ (lastVector_mem_jointSpan_left N.F N.F')

theorem zz : H.B N.F.z N.F.z = -N.F.T := N.F.zz

theorem nondeg_Wn [FiniteDimensional K V] (x : V) (hx : x ∈ N.Wn) (h : ∀ y ∈ N.Wn, H.B x y = 0) :
    x = 0 := by
  have hx' := hx
  rw [NFGeom.Wn_eq N, Submodule.mem_sup] at hx'
  obtain ⟨w, hw, u, hu, rfl⟩ := hx'
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hu
  have hz := h _ (NFGeom.z_mem_Wn N)
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, orthogonal_perp_z N hw,
    zz] at hz
  have ht : t = 0 := by
    have := N.F.hT
    simp at hz
    exact hz.resolve_right this
  subst ht
  simp only [zero_smul, add_zero] at h ⊢
  by_contra h0
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hwW : w ∈ N.Wn := by rw [NFGeom.Wn_eq N]; exact Submodule.mem_sup_left hw
  have := NFGeom.Wt_pos N σ hw h0
  rw [h w hwW] at this
  simp at this

theorem z_ne : N.F.z ≠ 0 := fun h => N.F.hT (by
  have := zz N
  rw [h] at this
  simpa using this.symm)

theorem hermFramePair_middleSpace_inf_span_z_eq_bot : N.Wt ⊓ Submodule.span K {N.F.z} = ⊥ :=
  eq_bot_iff.2 fun x hx => (Submodule.mem_bot K).2 <| by
    obtain ⟨hw, hz⟩ := hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have h := orthogonal_perp_z N hw
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, zz] at h
    have := N.F.hT
    rcases mul_eq_zero.1 h with h1 | h1
    · simp [h1]
    · exact absurd (neg_eq_zero.1 h1) this

theorem finrank_Wn [FiniteDimensional K V] : Module.finrank K N.Wn + 2 * r = Module.finrank K V := by
  have h1 := NFGeom.finrank_Wt N
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq N.Wt (Submodule.span K {N.F.z})
  rw [hermFramePair_middleSpace_inf_span_z_eq_bot, finrank_bot, finrank_span_singleton (z_ne N), ← NFGeom.Wn_eq N] at h2
  omega

def hW [FiniteDimensional K V] : Formalism.HermitianLatticeCounting.S6.HermSpace K N.Wn where
  B := H.B.domRestrict₁₂ N.Wn N.Wn
  herm x y := H.herm x y
  nondeg x hx := Submodule.coe_eq_zero.1 (nondeg_Wn N x x.2 fun y hy => hx ⟨y, hy⟩)

theorem hW_B [FiniteDimensional K V] (x y : N.Wn) : (hW N).B x y = H.B x y := rfl

end GlobalTheory.DegCnt.WnLat

namespace GlobalTheory.DegCnt.WnLat

open Formalism.HermitianLatticeCounting.P

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : NF H r)

theorem unimod (L : Submodule (𝓞 K) V) (hL : IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F')) :
    GlobalTheory.HermLat.IsUnimod (hW N) (L.comap (N.Wn.subtype.restrictScalars (𝓞 K))) := by
  obtain ⟨⟨⟨N0, hN0, hLeq⟩, hspanL⟩, hdL⟩ := hL
  set M := L.comap (N.Wn.subtype.restrictScalars (𝓞 K)) with hM
  have hIL : ∀ x ∈ II N.F N.F', x ∈ L := fun x hx => by
    rw [hLeq]; exact Submodule.mem_sup_right hx
  have hprL : ∀ x ∈ L, pr N x ∈ L := fun x hx => by
    have : pr N x = x - NFGeom.proj N x := by simp [pr]
    rw [this]; exact L.sub_mem hx (hIL _ (NFGeom.proj_mem N x))
  have hprW : ∀ x ∈ L, pr N x ∈ N.Wn := fun x hx => by
    refine pr_mem_Wn N ?_
    rw [← hspanL]; exact Submodule.subset_span hx
  have hS : L ⊓ rs (𝓞 K) N.Wn = N0.map ((pr N).restrictScalars (𝓞 K)) := by
    apply le_antisymm
    · rintro x ⟨hxL, hxW⟩
      have hxL' := hxL
      rw [hLeq] at hxL'
      obtain ⟨n, hn, i, hi, rfl⟩ := Submodule.mem_sup.1 hxL'
      refine ⟨n, hn, ?_⟩
      show pr N n = n + i
      have h1 : pr N (n + i) = n + i := pr_of_Wn N hxW
      rwa [map_add, pr_II N hi, add_zero] at h1
    · rintro _ ⟨n, hn, rfl⟩
      have hnL : n ∈ L := by rw [hLeq]; exact Submodule.mem_sup_left hn
      exact ⟨hprL n hnL, hprW n hnL⟩
  have hmap : M.map (N.Wn.subtype.restrictScalars (𝓞 K)) = L ⊓ rs (𝓞 K) N.Wn := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨hy, y.2⟩
    · rintro ⟨hxL, hxW⟩; exact ⟨⟨x, hxW⟩, hxL, rfl⟩
  have hfg : M.FG := by
    refine Submodule.fg_of_fg_map_injective (N.Wn.subtype.restrictScalars (𝓞 K)) Subtype.val_injective ?_
    rw [hmap, hS]; exact hN0.map _
  have hspan : Submodule.span K (M : Set N.Wn) = ⊤ := by
    apply Submodule.map_injective_of_injective (f := N.Wn.subtype) Subtype.val_injective
    rw [Submodule.map_span, Submodule.map_subtype_top]
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨y, _, rfl⟩; exact y.2
    · intro w hw
      have h1 : w ∈ Submodule.span K (L : Set V) := by rw [hspanL]; exact Wn_le_uPerp N hw
      have h2 : pr N w ∈ (Submodule.span K (L : Set V)).map (pr N) := Submodule.mem_map_of_mem h1
      rw [Submodule.map_span, pr_of_Wn N hw] at h2
      refine Submodule.span_mono ?_ h2
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨pr N x, hprW x hx⟩, hprL x hx, rfl⟩
  have hdual : dual (hW N) M = M := by
    ext y
    rw [mem_dual_iff, hspan]
    simp only [Submodule.mem_top, true_and]
    constructor
    · intro h
      show (y : V) ∈ L
      rw [← hdL, mem_dual_iff, hspanL]
      refine ⟨Wn_le_uPerp N y.2, fun x hx => ?_⟩
      have h1 := h ⟨pr N x, hprW x hx⟩ (hprL x hx)
      rw [hW_B] at h1
      rw [← pr_add N x, map_add (f := _), Wn_perp_II N y.2 (NFGeom.proj_mem N x), add_zero]
      exact h1
    · intro hy x hx
      rw [hW_B]
      have : (y : V) ∈ dual H L := by rw [hdL]; exact hy
      exact ((mem_dual_iff H L y).1 this).2 x hx
  exact ⟨⟨⟨M, hfg, by simp [rs]⟩, hspan⟩, hdual⟩

end GlobalTheory.DegCnt.WnLat

namespace GlobalTheory.DegCnt

theorem NF.wnUnimod : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r) (L : Submodule (𝓞 K) V), IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F') → ∃ HW : Formalism.HermitianLatticeCounting.S6.HermSpace K N.Wn, (∀ x y : N.Wn, HW.B x y = H.B x y) ∧ Module.finrank K N.Wn + 2 * r = Module.finrank K V ∧ GlobalTheory.HermLat.IsUnimod HW (L.comap (N.Wn.subtype.restrictScalars (𝓞 K))) := by
  intro K V _ _ _ _ _ _ _ _ H _ r N L hL
  exact ⟨WnLat.hW N, WnLat.hW_B N, WnLat.finrank_Wn N, WnLat.unimod N L hL⟩

end GlobalTheory.DegCnt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnimodularTraceOnMiddleSpaceLiftStatement
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unimodular_trace_on_middleSpace_lift : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r) (L : Submodule (𝓞 K) V), IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F') → ∃ HW : Formalism.HermitianLatticeCounting.S6.HermSpace K N.Wn, (∀ x y : N.Wn, HW.B x y = H.B x y) ∧ Module.finrank K N.Wn + 2 * r = Module.finrank K V ∧ GlobalTheory.HermLat.IsUnimod HW (L.comap (N.Wn.subtype.restrictScalars (𝓞 K))) := by
  first | exact @GlobalTheory.DegCnt.NF.wnUnimod | exact GlobalTheory.DegCnt.NF.wnUnimod | (intros; apply GlobalTheory.DegCnt.NF.wnUnimod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueMulMemBoxTriangularLayers
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueMulMemBoxTriangularLayers
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCov

theorem existsUnique_mul_mem_box_of_layers : ∀ (M I A B D : Type) [Monoid M] [Fintype I] [AddCommGroup A] [AddCommGroup B] [AddCommGroup D] (ht : I → ℕ) (C : (I → A) × B × D → M) (Γ : Set M) (Λ₁ F₁ : I → Set A) (Λ₂ F₂ : Set B) (Λ₃ F₃ : Set D), Function.Injective C → C 0 = 1 → (∀ p q, ∃ w, C p * C q = C w ∧ (∀ i, (∀ l, ht l < ht i → p.1 l = 0) → w.1 i = p.1 i + q.1 i) ∧ (p.1 = 0 → w.2.1 = p.2.1 + q.2.1) ∧ (p.1 = 0 → p.2.1 = 0 → w.2.2 = p.2.2 + q.2.2)) → Γ ⊆ Set.range C → (1 : M) ∈ Γ → (∀ a ∈ Γ, ∀ b ∈ Γ, a * b ∈ Γ) → (∀ a ∈ Γ, ∃ b ∈ Γ, b * a = 1) → (∀ p, C p ∈ Γ → ∀ i, p.1 i ∈ Λ₁ i) → (∀ p, C p ∈ Γ → p.1 = 0 → p.2.1 ∈ Λ₂) → (∀ p, C p ∈ Γ → p.1 = 0 → p.2.1 = 0 → p.2.2 ∈ Λ₃) → (∀ i, ∀ a ∈ Λ₁ i, ∃ p, C p ∈ Γ ∧ p.1 = Pi.single i a) → (∀ b ∈ Λ₂, ∃ p, C p ∈ Γ ∧ p.1 = 0 ∧ p.2.1 = b) → (∀ d ∈ Λ₃, C (0, 0, d) ∈ Γ) → (∀ i a, ∃! b, b ∈ Λ₁ i ∧ b + a ∈ F₁ i) → (∀ a, ∃! b, b ∈ Λ₂ ∧ b + a ∈ F₂) → (∀ a, ∃! b, b ∈ Λ₃ ∧ b + a ∈ F₃) → ∀ q, ∃! m, m ∈ Γ ∧ m * C q ∈ C '' (Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃) := by
  intro M I A B D _ _ _ _ _ ht C Γ Λ₁ F₁ Λ₂ F₂ Λ₃ F₃ hC hC0 hmul hΓC h1 hmulΓ hinv h1Λ h2Λ h3Λ
    h1s h2s h3s hF₁ hF₂ hF₃ q
  classical

  have h0Γ : C 0 ∈ Γ := hC0 ▸ h1
  have z1 : ∀ i, (0 : A) ∈ Λ₁ i := fun i => h1Λ 0 h0Γ i
  have z2 : (0 : B) ∈ Λ₂ := h2Λ 0 h0Γ rfl
  have z3 : (0 : D) ∈ Λ₃ := h3Λ 0 h0Γ rfl rfl

  have layer1 : ∀ s : Finset I, ∀ q, ∃ m ∈ Γ, ∃ w, m * C q = C w ∧ ∀ i ∈ s, w.1 i ∈ F₁ i := by
    intro s
    induction s using Finset.induction_on_max_value ht with
    | empty => exact fun q => ⟨1, h1, q, one_mul _, by simp⟩
    | insert a s has hmax ih =>
      intro q
      obtain ⟨m, hm, w, hmw, hw⟩ := ih q
      obtain ⟨b, ⟨hbΛ, hbF⟩, -⟩ := hF₁ a (w.1 a)
      obtain ⟨p, hpΓ, hp1⟩ := h1s a b hbΛ
      obtain ⟨w', hw'eq, hw'1, -, -⟩ := hmul p w
      refine ⟨C p * m, hmulΓ _ hpΓ _ hm, w', by rw [mul_assoc, hmw, hw'eq], ?_⟩
      have key : ∀ i, ht i ≤ ht a → w'.1 i = p.1 i + w.1 i := fun i hi =>
        hw'1 i (fun l hl => by
          rw [hp1]; exact Pi.single_eq_of_ne (ne_of_apply_ne ht (by omega)) _)
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [key i le_rfl, hp1, Pi.single_eq_same]; exact hbF
      · have hia : i ≠ a := fun h => has (h ▸ hi)
        rw [key i (hmax i hi), hp1, Pi.single_eq_of_ne hia, zero_add]; exact hw i hi

  have hex : ∃ m ∈ Γ, ∃ u, m * C q = C u ∧ u ∈ Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃ := by
    obtain ⟨m, hm, w, hmw, hw⟩ := layer1 Finset.univ q
    obtain ⟨b, ⟨hbΛ, hbF⟩, -⟩ := hF₂ w.2.1
    obtain ⟨p, hpΓ, hp1, hp2⟩ := h2s b hbΛ
    obtain ⟨w', hw'eq, hw'1, hw'2, -⟩ := hmul p w
    obtain ⟨d, ⟨hdΛ, hdF⟩, -⟩ := hF₃ w'.2.2
    obtain ⟨w'', hw''eq, hw''1, hw''2, hw''3⟩ := hmul (0, 0, d) w'
    refine ⟨C (0, 0, d) * (C p * m), hmulΓ _ (h3s d hdΛ) _ (hmulΓ _ hpΓ _ hm), w'',
      by rw [mul_assoc, mul_assoc, hmw, hw'eq, hw''eq], ?_⟩
    have e1 : ∀ i, w'.1 i = w.1 i := fun i => by
      rw [hw'1 i (fun l _ => by rw [hp1]; rfl), hp1]; exact zero_add _
    have e1' : ∀ i, w''.1 i = w'.1 i := fun i => by
      rw [hw''1 i (fun l _ => rfl)]; exact zero_add _
    have e2 : w''.2.1 = w'.2.1 := by rw [hw''2 rfl]; exact zero_add _
    refine Set.mk_mem_prod ?_ (Set.mk_mem_prod ?_ ?_)
    · exact Set.mem_univ_pi.2 fun i => by
        rw [e1', e1]; exact hw i (Finset.mem_univ i)
    · rw [e2, hw'2 hp1, hp2]; exact hbF
    · rw [hw''3 rfl rfl]; exact hdF

  have rigid : ∀ g ∈ Γ, ∀ u u', u ∈ Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃ →
      u' ∈ Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃ → g * C u = C u' → g = 1 := by
    intro g hg u u' hu hu' hgu
    obtain ⟨p, rfl⟩ := hΓC hg
    obtain ⟨w, hweq, hw1, hw2, hw3⟩ := hmul p u
    have hwu : w = u' := hC (hweq.symm.trans hgu)
    rw [hwu] at hw1 hw2 hw3
    simp only [Set.mem_prod, Set.mem_univ_pi] at hu hu'

    have key : ∀ n, ∀ i, ht i = n → p.1 i = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro i hi
        have e := hw1 i (fun l hl => ih (ht l) (hi ▸ hl) l rfl)
        exact (hF₁ i (u.1 i)).unique ⟨h1Λ p hg i, e ▸ hu'.1 i⟩ ⟨z1 i, (zero_add (u.1 i)).symm ▸ hu.1 i⟩
    have hp1 : p.1 = 0 := funext fun i => key _ i rfl
    have hp2 : p.2.1 = 0 :=
      (hF₂ u.2.1).unique ⟨h2Λ p hg hp1, hw2 hp1 ▸ hu'.2.1⟩ ⟨z2, (zero_add u.2.1).symm ▸ hu.2.1⟩
    have hp3 : p.2.2 = 0 :=
      (hF₃ u.2.2).unique ⟨h3Λ p hg hp1 hp2, hw3 hp1 hp2 ▸ hu'.2.2⟩
        ⟨z3, (zero_add u.2.2).symm ▸ hu.2.2⟩
    have hp : p = 0 := Prod.ext hp1 (Prod.ext hp2 hp3)
    rw [hp, hC0]

  obtain ⟨m, hmΓ, u, hmu, hu⟩ := hex
  refine ⟨m, ⟨hmΓ, u, hu, hmu.symm⟩, ?_⟩
  rintro m' ⟨hm'Γ, u', hu', hm'u⟩
  obtain ⟨n, hnΓ, hnm⟩ := hinv m hmΓ
  have hg : m' * n = 1 := by
    refine rigid (m' * n) (hmulΓ _ hm'Γ _ hnΓ) u u' hu hu' ?_
    rw [← hmu, hm'u, ← mul_assoc, mul_assoc m', hnm, mul_one]
  calc m' = m' * (n * m) := by rw [hnm, mul_one]
    _ = m' * n * m := (mul_assoc _ _ _).symm
    _ = m := by rw [hg, one_mul]

end GlobalTheory.DegVol.RefCov
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueMulMemBoxTriangularLayersStatement
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_mul_mem_box_triangular_layers : ∀ (M I A B D : Type) [Monoid M] [Fintype I] [AddCommGroup A] [AddCommGroup B] [AddCommGroup D] (ht : I → ℕ) (C : (I → A) × B × D → M) (Γ : Set M) (Λ₁ F₁ : I → Set A) (Λ₂ F₂ : Set B) (Λ₃ F₃ : Set D), Function.Injective C → C 0 = 1 → (∀ p q, ∃ w, C p * C q = C w ∧ (∀ i, (∀ l, ht l < ht i → p.1 l = 0) → w.1 i = p.1 i + q.1 i) ∧ (p.1 = 0 → w.2.1 = p.2.1 + q.2.1) ∧ (p.1 = 0 → p.2.1 = 0 → w.2.2 = p.2.2 + q.2.2)) → Γ ⊆ Set.range C → (1 : M) ∈ Γ → (∀ a ∈ Γ, ∀ b ∈ Γ, a * b ∈ Γ) → (∀ a ∈ Γ, ∃ b ∈ Γ, b * a = 1) → (∀ p, C p ∈ Γ → ∀ i, p.1 i ∈ Λ₁ i) → (∀ p, C p ∈ Γ → p.1 = 0 → p.2.1 ∈ Λ₂) → (∀ p, C p ∈ Γ → p.1 = 0 → p.2.1 = 0 → p.2.2 ∈ Λ₃) → (∀ i, ∀ a ∈ Λ₁ i, ∃ p, C p ∈ Γ ∧ p.1 = Pi.single i a) → (∀ b ∈ Λ₂, ∃ p, C p ∈ Γ ∧ p.1 = 0 ∧ p.2.1 = b) → (∀ d ∈ Λ₃, C (0, 0, d) ∈ Γ) → (∀ i a, ∃! b, b ∈ Λ₁ i ∧ b + a ∈ F₁ i) → (∀ a, ∃! b, b ∈ Λ₂ ∧ b + a ∈ F₂) → (∀ a, ∃! b, b ∈ Λ₃ ∧ b + a ∈ F₃) → ∀ q, ∃! m, m ∈ Γ ∧ m * C q ∈ C '' (Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃) := by
  first | exact @GlobalTheory.DegVol.RefCov.existsUnique_mul_mem_box_of_layers | exact GlobalTheory.DegVol.RefCov.existsUnique_mul_mem_box_of_layers | (intros; apply GlobalTheory.DegVol.RefCov.existsUnique_mul_mem_box_of_layers <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingCommonStabilizerCoordinatesAtPl
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingCommonStabilizerCoordinatesAtPl
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCov.Transp

private theorem measurePreserving_curry_symm_pi (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A]
    (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ A).symm (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ)
      (Measure.pi fun _ : ι × κ => μ) := by
  refine ⟨(MeasurableEquiv.curry ι κ A).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s _ => ?_).symm
  have hpre : (MeasurableEquiv.curry ι κ A).symm ⁻¹' Set.univ.pi s
      = Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
    ext f
    simp [MeasurableEquiv.coe_curry_symm, Prod.forall]
  rw [MeasurableEquiv.map_apply, hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

theorem curry_mp (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ A) (Measure.pi fun _ => μ)
      (Measure.pi fun _ => Measure.pi fun _ => μ) := by
  have h := MeasurePreserving.symm _ (measurePreserving_curry_symm_pi ι κ A μ)
  rwa [MeasurableEquiv.symm_symm] at h

theorem swap_mp (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (fun (f : ι → κ → A) (v : κ) (i : ι) => f i v)
      (Measure.pi fun _ => Measure.pi fun _ => μ) (Measure.pi fun _ => Measure.pi fun _ => μ) := by
  have h1 := measurePreserving_curry_symm_pi ι κ A μ
  have h2 := measurePreserving_piCongrLeft (fun _ : κ × ι => μ) (Equiv.prodComm ι κ)
  have h3 := curry_mp κ ι A μ
  have key : (fun (f : ι → κ → A) (v : κ) (i : ι) => f i v) =
      (MeasurableEquiv.curry κ ι A) ∘ (MeasurableEquiv.piCongrLeft (fun _ : κ × ι => A) (Equiv.prodComm ι κ)) ∘
        (MeasurableEquiv.curry ι κ A).symm := by
    funext f v i
    simp [MeasurableEquiv.coe_curry, MeasurableEquiv.coe_curry_symm, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_eq_cast]
  rw [key]
  exact h3.comp (h2.comp h1)

theorem glue_mp {ι A B A' B' : Type} [Fintype ι] [MeasureSpace A] [MeasureSpace B] [MeasureSpace A'] [MeasureSpace B']
    [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)]
    [SigmaFinite (volume : Measure A')] [SigmaFinite (volume : Measure B')]
    {f : A' → ι → A} {g : B' → ι → B}
    (hf : MeasurePreserving f volume (Measure.pi fun _ : ι => (volume : Measure A)))
    (hg : MeasurePreserving g volume (Measure.pi fun _ : ι => (volume : Measure B))) :
    MeasurePreserving (fun (p : A' × B') (v : ι) => (f p.1 v, g p.2 v)) volume
      (Measure.pi fun _ : ι => (volume : Measure (A × B))) := by
  have h1 := hf.prod hg
  have h2 := MeasurePreserving.symm _
    (measurePreserving_arrowProdEquivProdArrow A B ι (fun _ => (volume : Measure A)) (fun _ => (volume : Measure B)))
  exact h2.comp h1

theorem sigmaFinite_volume_pi_family (I A : Type) [Fintype I] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    SigmaFinite (volume : Measure (I → A)) := by
  show SigmaFinite (Measure.pi fun _ : I => (volume : Measure A))
  infer_instance

theorem sigmaFinite_volume_pi_double_family (I J A : Type) [Fintype I] [Fintype J] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    SigmaFinite (volume : Measure (I → J → A)) := by
  have := sigmaFinite_volume_pi_family J A
  show SigmaFinite (Measure.pi fun _ : I => (volume : Measure (J → A)))
  infer_instance

theorem swap_vol (I ι A : Type) [Fintype I] [Fintype ι] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    MeasurePreserving (fun (f : I → ι → A) (v : ι) (i : I) => f i v) volume
      (Measure.pi fun _ : ι => (volume : Measure (I → A))) := by
  have := sigmaFinite_volume_pi_family I A
  exact swap_mp I ι A volume

end GlobalTheory.DegVol.RefCov.Transp

namespace GlobalTheory.DegVol.RefCov

theorem atP_measurePreserving : ∀ (ι : Type) [Fintype ι] (k r j : ℕ) (β : Fin r → ℕ),
    MeasurePreserving (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) volume
      (Measure.pi fun _ : ι => (volume : Measure ((UTin β → ℂ) × PTop k r j))) := by
  intro ι _ k r j β
  have s0 := Transp.sigmaFinite_volume_pi_family (Fin (k + 1)) ℂ
  have s1 := Transp.sigmaFinite_volume_pi_family (UTin β) ℂ
  have s2 := Transp.sigmaFinite_volume_pi_family {a : Fin r // j ≤ a.val} (Fin (k + 1) → ℂ)
  have s3 := Transp.sigmaFinite_volume_pi_family {p : UT r // j ≤ p.1.1.val} ℂ
  have s4 := Transp.sigmaFinite_volume_pi_family {a : Fin r // j ≤ a.val} ℝ
  have t1 := Transp.sigmaFinite_volume_pi_double_family (UTin β) ι ℂ
  have t2 := Transp.sigmaFinite_volume_pi_double_family {a : Fin r // j ≤ a.val} ι (Fin (k + 1) → ℂ)
  have t3 := Transp.sigmaFinite_volume_pi_double_family {p : UT r // j ≤ p.1.1.val} ι ℂ
  have t4 := Transp.sigmaFinite_volume_pi_double_family {a : Fin r // j ≤ a.val} ι ℝ
  have p1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))) := by
    show SigmaFinite ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ℝ)))
    infer_instance
  have p2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ)))) := by
    show SigmaFinite ((volume : Measure ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ)).prod (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))))
    infer_instance
  have q1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))) := by
    show SigmaFinite ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ι → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ι → ℝ)))
    infer_instance
  have q2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ)))) := by
    show SigmaFinite ((volume : Measure ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ)).prod (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))))
    infer_instance
  have e1 := Transp.swap_vol (UTin β) ι ℂ
  have e2 := Transp.swap_vol {a : Fin r // j ≤ a.val} ι (Fin (k + 1) → ℂ)
  have e3 := Transp.swap_vol {p : UT r // j ≤ p.1.1.val} ι ℂ
  have e4 := Transp.swap_vol {a : Fin r // j ≤ a.val} ι ℝ
  have g := Transp.glue_mp e1 (Transp.glue_mp e2 (Transp.glue_mp e3 e4))
  exact g

end GlobalTheory.DegVol.RefCov
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingCommonStabilizerCoordinatesAtPlStatement
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePreserving_commonStabilizerCoordinatesAtPlace : ∀ (ι : Type) [Fintype ι] (k r j : ℕ) (β : Fin r → ℕ), MeasurePreserving (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) volume (Measure.pi fun _ : ι => (volume : Measure ((UTin β → ℂ) × PTop k r j))) := by
  first | exact @GlobalTheory.DegVol.RefCov.atP_measurePreserving | exact GlobalTheory.DegVol.RefCov.atP_measurePreserving | (intros; apply GlobalTheory.DegVol.RefCov.atP_measurePreserving <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeReferenceLatticeStabiliserBounds
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegVol.RefCov

theorem exu_pi {J A : Type} [AddCommGroup A] {Λ F : J → Set A} (h : ∀ i a, ∃! b, b ∈ Λ i ∧ b + a ∈ F i) (a : J → A) :
    ∃! b, b ∈ Set.pi Set.univ Λ ∧ b + a ∈ Set.pi Set.univ F := by
  choose b hb hu using fun i => h i (a i)
  exact ⟨b, ⟨fun i _ => (hb i).1, fun i _ => (hb i).2⟩, fun c hc => funext fun i => hu i _ ⟨hc.1 i trivial, hc.2 i trivial⟩⟩

theorem exu_prod {A B : Type} [AddCommGroup A] [AddCommGroup B] {Λ F : Set A} {Λ' F' : Set B}
    (h : ∀ a, ∃! b, b ∈ Λ ∧ b + a ∈ F) (h' : ∀ a, ∃! b, b ∈ Λ' ∧ b + a ∈ F') (a : A × B) :
    ∃! b, b ∈ Λ ×ˢ Λ' ∧ b + a ∈ F ×ˢ F' := by
  obtain ⟨b, hb, hu⟩ := h a.1
  obtain ⟨b', hb', hu'⟩ := h' a.2
  exact ⟨(b, b'), ⟨⟨hb.1, hb'.1⟩, hb.2, hb'.2⟩, fun c hc => Prod.ext (hu _ ⟨hc.1.1, hc.2.1⟩) (hu' _ ⟨hc.1.2, hc.2.2⟩)⟩

theorem exu_image {T A : Type} [AddCommGroup A] {P : T → Prop} {f : T → A} {F : Set A}
    (h : ∀ a, ∃! t, P t ∧ f t + a ∈ F) (a : A) : ∃! b, b ∈ f '' {t | P t} ∧ b + a ∈ F := by
  obtain ⟨t, ht, hu⟩ := h a
  refine ⟨f t, ⟨⟨t, ht.1, rfl⟩, ht.2⟩, ?_⟩
  rintro _ ⟨⟨t', ht', rfl⟩, h2⟩
  rw [hu t' ⟨ht', h2⟩]

theorem card_top (r j : ℕ) : Fintype.card {a : Fin r // j ≤ a.val} = r - j := by
  have h1 : Fintype.card {b : Fin r // b.val < j} = min r j := by
    rw [Fintype.card_subtype, Fin.card_filter_val_lt]
  have h2 := Fintype.card_subtype_compl fun b : Fin r => b.val < j
  rw [h1, Fintype.card_fin] at h2
  rw [Fintype.card_congr (Equiv.subtypeEquivRight fun b : Fin r => (not_lt (a := b.val) (b := j)).symm), h2]
  omega

theorem card_UT (r : ℕ) (P : UT r → Prop) [Fintype (Subtype P)] : Fintype.card (Subtype P) ≤ r ^ 2 := by
  refine (Fintype.card_le_of_injective (fun p : Subtype P => p.1.1) fun p q h => Subtype.ext (Subtype.ext h)).trans ?_
  simp [sq]

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} {N : NF H r} {k : ℕ} {ι : Type}
  {σ : ι → (K →+* ℂ)} {ρ : ℝ} {β : Fin r → ℕ} {Φ : ι → V → Fin (2 * r + k + 1) → ℂ} {z z' : ι → Fin (2 * r + k + 1) → ℂ}
  {g : ι → Mat k r}

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem rset_eq (hF : ∀ v, IsFrameOf N k (σ v) ρ β (Φ v) (z v) (z' v) (g v)) (v : ι) :
    Rset k r (g v) = Set.range (crd k r N.j β) ∧ IsClosedSub k r (Rset k r (g v)) ∧ Function.Injective (crd k r N.j β) := by
  obtain ⟨-, h1, h2, h3, ⟨c, hc⟩, -⟩ := hF v
  obtain ⟨a1, a2⟩ := rset_normal0 k r N.j N.j_le _ _ _ β c h1 h2 h3 hc
  obtain ⟨-, b1, b2, -⟩ := Swap.range_eq_and_injective_parabolic_unipotent_product k r N.j β hc.2.2.2.1 hc.2.2.2.2.1
  exact ⟨a1.trans b1, a2, b2⟩

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem exists_CC (hF : ∀ v, IsFrameOf N k (σ v) ρ β (Φ v) (z v) (z' v) (g v)) (m : ι → Mat k r)
    (hm : ∀ v, m v ∈ Rset k r (g v)) : ∃ p : Crd ι k r N.j β, CC p = m := by
  choose q hq using fun v => (rset_eq hF v).1 ▸ hm v
  obtain ⟨p, rfl⟩ := usage₂.2 q
  exact ⟨p, funext hq⟩

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem CC_law (hF : ∀ v, IsFrameOf N k (σ v) ρ β (Φ v) (z v) (z' v) (g v)) (p q : Crd ι k r N.j β) :
    ∃ w, CC p * CC q = CC w ∧
      (∀ i : UTin β, (∀ l : UTin β, l.1.1.2.val - l.1.1.1.val < i.1.1.2.val - i.1.1.1.val → p.1 l = 0) →
        w.1 i = p.1 i + q.1 i) ∧ (p.1 = 0 → w.2.1 = p.2.1 + q.2.1) ∧ (p.1 = 0 → p.2.1 = 0 → w.2.2 = p.2.2 + q.2.2) := by
  obtain ⟨w, hw⟩ := exists_CC hF (CC p * CC q) fun v =>
    (rset_eq hF v).2.1.2.2.2.1 _ ((rset_eq hF v).1 ▸ ⟨_, rfl⟩) _ ((rset_eq hF v).1 ▸ ⟨_, rfl⟩)
  have h := fun v => (GlobalTheory.T.commonStabilizerFromCoordinates_product_law k r N.j β).2 (atP p v) (atP q v) (atP w v) (congrFun hw v).symm
  refine ⟨w, hw.symm, fun i hi => funext fun v => (h v).1 i fun l hl => congrFun (hi l hl) v, fun h1 => ?_,
    fun h1 h2 => ?_⟩
  · funext a v
    exact congrFun ((h v).2.1 (funext fun i => congrFun (congrFun h1 i) v)) a
  · have h3 := fun v => (h v).2.2 (funext fun i => congrFun (congrFun h1 i) v) (funext fun i => congrFun (congrFun h2 i) v)
    refine Prod.ext ?_ ?_
    · funext a v
      exact congrFun (congrArg Prod.fst (h3 v)) a
    · funext a v
      exact congrFun (congrArg Prod.snd (h3 v)) a

theorem covol_ref : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (β : Fin r → ℕ) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (z z' : ι → Fin (2 * r + k + 1) → ℂ) (g : ι → Mat k r), IsPlaces σ → Module.finrank K V = 2 * r + k + 1 → (∀ v, IsFrameOf N k (σ v) (2 * Formalism.HermitianLatticesTheory.vInv K) β (Φ v) (z v) (z' v) (g v)) → (Ideal.absNorm N.𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * Fintype.card ι) → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ L : Submodule (𝓞 K) V, IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F') → N.F.z ∈ L → ∃ Ω : Set (ι → Mt k r), IsFund (realPts Φ (N.Gam (N.Ref L) : Set (V ≃ₗ[K] V))) (RP k r g) Ω ∧ ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ (k * (r - N.j) * Fintype.card ι) / (8 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * (r + 1) ^ 2 * Fintype.card ι)) ≤ Measure.pi (fun _ : ι => lebR0 k r N.j β) Ω ∧ Measure.pi (fun _ : ι => lebR0 k r N.j β) Ω ≤ ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ (k * (r - N.j) * Fintype.card ι) * (8 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * (r + 1) ^ 2 * Fintype.card ι)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N k ι _ σ β Φ z z' g hσ hd hF hN hv L hL hz
  set ρ : ℝ := 2 * Formalism.HermitianLatticesTheory.vInv K with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  obtain ⟨v₀, -⟩ := hσ.2 w₀
  obtain ⟨c₀, hc₀⟩ := (hF v₀).2.2.2.2.1
  obtain ⟨m1, -, m3, -⟩ := RealMat.real_points K V H hK r N k ι σ β Φ z z' g hσ hd hF
  obtain ⟨t1, t2⟩ := TopLayer.top_layer K V H hK r N k ι σ β Φ z z' g hσ hd hF L hL hz
  obtain ⟨d1, d2, d3, d4⟩ := GlobalTheory.T.refLatticeStabilizer_middle_bottom_layers K V H hK r N L hL hz
  obtain ⟨HW, hB, hdW, hU⟩ := GlobalTheory.T.exists_unimodular_trace_on_middleSpace_lift K V H hK r N L hL
  have htop := fun v => GlobalTheory.T.realFrame_automorphism_unitriangular_rows_coords K V H r N k (σ v) ρ β (Φ v) (z v) (z' v) (g v) hρ0 (hF v)
  have hskew := fun v => GlobalTheory.T.besselModelMatrix_skew_coordinates_rational_aut K V H r N k (σ v) ρ β (Φ v) (z v) (z' v) (g v) hρ0 (hF v)
  have hne : ∀ n : ℕ, ∀ v : ι, ((ρ ^ n : ℝ) : ℂ) ≠ 0 := fun n _ => by exact_mod_cast (pow_pos hρ0 n).ne'
  choose F₁ hF₁m hF₁ hF₁v using fun i : UTin β => IdealFund.exists_fund_ipow K hK ι σ hσ N.𝔡
    ((i.1.1.1.val : ℤ) - i.1.1.2.val) (fun _ => ((ρ ^ (i.1.1.2.val - i.1.1.1.val) : ℝ) : ℂ)) N.𝔡_ne (hne _)
  choose F₂ hF₂m hF₂ hF₂v using fun b : {a : Fin r // N.j ≤ a.val} => GlobalTheory.T.exists_fundamental_set_rows_middleSpace K V H hK N.Wn HW k r ι σ Φ hB hσ
    (by omega) (fun v => (hF v).1) (fun v => GlobalTheory.T.realisation_mem_standard_middle_space K V H r N k (σ v) ρ β (Φ v) (z v) (z' v) (g v) hρ0 (hF v))
    L N.𝔡 (-((r : ℤ) - b.1.val)) (ρ ^ (r - b.1.val)) hU N.𝔡_ne (pow_pos hρ0 _)
  choose F₃ hF₃m hF₃ hF₃v using fun p : {p : UT r // N.j ≤ p.1.1.val} => IdealFund.exists_fund_ipow K hK ι σ hσ N.𝔡
    (-((r : ℤ) - p.1.1.1.val) - ((r : ℤ) - p.1.1.2.val))
    (fun _ => ((ρ ^ ((r - p.1.1.1.val) + (r - p.1.1.2.val)) : ℝ) : ℂ)) N.𝔡_ne (hne _)
  choose F₄ hF₄m hF₄ hF₄l hF₄u using fun a : {a : Fin r // N.j ≤ a.val} => SkewFund.exists_fund_skew K hK ι σ hσ N.𝔡
    (r - a.1.val) N.𝔡_ne N.𝔡_star hN hv
  obtain ⟨hΩm, hΩv⟩ := GlobalTheory.T.measure_commonStabilizerCoords_box_image ι k r N.j β hc₀.2.2.2.1 hc₀.2.2.2.2.1 (GlobalTheory.T.measurePreserving_commonStabilizerCoordinatesAtPlace ι k r N.j β) F₁ F₂ F₃ F₄
    hF₁m hF₂m hF₃m hF₄m _ rfl
  refine ⟨_, ⟨hΩm, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨q, rfl⟩ := exists_CC hF x hx
    have hex : ∀ s ∈ N.Gam (N.Ref L), ∃ p : Crd ι k r N.j β, ∀ v x, crd k r N.j β (atP p v) *ᵥ Φ v x = Φ v (s x) := by
      intro s hs
      obtain ⟨m, hm, -⟩ := m1 s
      obtain ⟨p, rfl⟩ := exists_CC hF m (m3 ⟨s, hs.1, hm⟩)
      exact ⟨p, hm⟩
    have hu0 : ∀ (s : V ≃ₗ[K] V) (p : Crd ι k r N.j β), (∀ v x, crd k r N.j β (atP p v) *ᵥ Φ v x = Φ v (s x)) →
        (∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) → p.1 = 0 := by
      intro s p hp he
      funext i v
      have := (htop v s _ (hp v)).1 i 0 (by simp [he])
      simpa [atP] using this
    have h10 : ∀ (p : Crd ι k r N.j β), p.1 = 0 → ∀ v, (atP p v).1 = 0 := fun p h v =>
      funext fun i => congrFun (congrFun h i) v
    have h20 : ∀ (p : Crd ι k r N.j β), p.2.1 = 0 → ∀ v, (atP p v).2.1 = 0 := fun p h v =>
      funext fun i => congrFun (congrFun h i) v
    have hcast : ∀ a : Fin r, -(2 * ((r - a.val : ℕ) : ℤ)) = -((r : ℤ) - a.val) - ((r : ℤ) - a.val) := fun a => by
      have := a.2; omega
    refine GlobalTheory.T.existsUnique_mul_mem_box_triangular_layers (ι → Mat k r) (UTin β) _ _ _ (fun l => l.1.1.2.val - l.1.1.1.val) CC
      (realPts Φ (N.Gam (N.Ref L) : Set (V ≃ₗ[K] V))) _ F₁ _ (Set.pi Set.univ F₂) _
      (Set.pi Set.univ F₃ ×ˢ Set.pi Set.univ F₄) ?_ ?_ (CC_law hF) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (fun i => exu_image (hF₁ i)) (exu_pi fun i => exu_image (hF₂ i))
      (exu_prod (exu_pi fun i => exu_image (hF₃ i)) (exu_pi fun i => exu_image (hF₄ i))) q
    · exact fun p p' h => usage₂.1 (funext fun v => (rset_eq hF v).2.2 (congrFun h v))
    · exact funext fun v => (GlobalTheory.T.commonStabilizerFromCoordinates_product_law k r N.j β).1
    · rintro m ⟨s, hs, hm⟩
      exact exists_CC hF m (m3 ⟨s, hs.1, hm⟩)
    · exact ⟨1, one_mem _, fun v x => Matrix.one_mulVec _⟩
    · rintro a ⟨s, hs, ha⟩ b ⟨t, ht, hb⟩
      refine ⟨s * t, mul_mem hs ht, fun v x => ?_⟩
      have := (Matrix.mulVec_mulVec (Φ v x) (Matrix.of (a v)) (Matrix.of (b v))).symm
      rw [hb, ha] at this
      exact this
    · rintro a ⟨s, hs, ha⟩
      obtain ⟨b, hb, -⟩ := m1 s⁻¹
      refine ⟨b, ⟨s⁻¹, inv_mem hs, hb⟩, funext fun v => RealMat.mat_unique (hF v).1 fun x => ?_⟩
      have := (Matrix.mulVec_mulVec (Φ v x) (Matrix.of (b v)) (Matrix.of (a v))).symm
      rw [ha, hb] at this
      refine this.trans ?_
      simp
    · rintro p ⟨s, hs, hp⟩ i
      obtain ⟨u, h1, h2, -⟩ := t1 s hs _ _ i.1.2
      exact ⟨u _, h2 _, funext fun v => ((htop v s _ (hp v)).1 i u h1).symm⟩
    · rintro p ⟨s, hs, hp⟩ h1 b -
      obtain ⟨y, hy, h⟩ := d1 s hs ((htop v₀ s _ (hp v₀)).2.1 (h10 p h1 v₀)) b.1 b.2
      exact ⟨y, hy, funext fun v => ((htop v s _ (hp v)).2.2 (h10 p h1 v) b y h).symm⟩
    · rintro p ⟨s, hs, hp⟩ h1 h2
      have h := fun v => hskew v s _ (hp v) (h10 p h1 v) (h20 p h2 v)
      have h3 := d3 s hs ((htop v₀ s _ (hp v₀)).2.1 (h10 p h1 v₀)) (h v₀).1
      refine ⟨fun i _ => ⟨_, (h3 i.1.1.1 i.1.1.2 i.2 (i.2.trans (le_of_lt i.1.2))).1, funext fun v => ((h v).2.1 i).symm⟩,
        fun a _ => ⟨_, ⟨?_, (h3 a.1 a.1 a.2 a.2).2⟩, funext fun v => ((h v).2.2 a).symm⟩⟩
      rw [hcast]
      exact (h3 a.1 a.1 a.2 a.2).1
    · rintro i _ ⟨t, ht, rfl⟩
      obtain ⟨s, hs, h⟩ := t2 _ _ i.1.2 i.2 t ht
      obtain ⟨p, hp⟩ := hex s hs
      refine ⟨p, ⟨s, hs, hp⟩, funext fun l => funext fun v => ?_⟩
      have := (htop v s _ (hp v)).1 l (Pi.single i.1.1.1 (if l.1.1.2 = i.1.1.2 then t else 0))
        (by rw [h]; simp [Pi.single_apply])
      refine this.trans ?_
      by_cases hl : l = i
      · subst hl; simp
      · rw [@Pi.single_eq_of_ne _ _ _ (fun a b => Classical.propDecidable (a = b)) _ _ hl]
        by_cases h1 : l.1.1.1 = i.1.1.1
        · have h2 : l.1.1.2 ≠ i.1.1.2 := fun h2 => hl (Subtype.ext (Subtype.ext (Prod.ext h1 h2)))
          simp [h2]
        · simp [Pi.single_eq_of_ne h1]
    · intro b hb
      choose y hy hyb using fun a => hb a trivial
      obtain ⟨s, hs, he, h⟩ := d2 (fun a => if h : N.j ≤ a.val then y ⟨a, h⟩ else 0) fun a => by
        by_cases h : N.j ≤ a.val
        · rw [dif_pos h]; exact hy ⟨a, h⟩
        · rw [dif_neg h]; exact Submodule.zero_mem _
      obtain ⟨p, hp⟩ := hex s hs
      have h1 := hu0 s p hp he
      refine ⟨p, ⟨s, hs, hp⟩, h1, funext fun a => ?_⟩
      rw [← hyb a]
      funext v
      refine (htop v s _ (hp v)).2.2 (h10 p h1 v) a (y a) ?_
      have := h a.1 a.2
      rwa [dif_pos a.2] at this
    · rintro d ⟨hd1, hd2⟩
      choose t ht htd using fun a => hd1 a trivial
      choose t' ht' htd' using fun a => hd2 a trivial
      let S : Fin r → Fin r → K := fun a b =>
        if h : N.j ≤ a.val ∧ N.j ≤ b.val then
          if h1 : a < b then t ⟨⟨(a, b), h1⟩, h.1⟩ else if h2 : b < a then -star (t ⟨⟨(b, a), h2⟩, h.2⟩) else t' ⟨a, h.1⟩
        else 0
      have hS : ∀ a b, S a b ∈ ipow N.𝔡 (-((r : ℤ) - a.val) - ((r : ℤ) - b.val)) ∧ S a b + star (S b a) = 0 := by
        intro a b
        by_cases h : N.j ≤ a.val ∧ N.j ≤ b.val
        · rcases lt_trichotomy a b with h1 | rfl | h1
          · simp only [S, dif_pos h, dif_pos h.symm, dif_pos h1, dif_neg h1.not_gt]
            exact ⟨ht ⟨⟨(a, b), h1⟩, h.1⟩, by simp⟩
          · simp only [S, dif_pos h, dif_neg (lt_irrefl a)]
            rw [← hcast]
            exact ht' ⟨a, h.1⟩
          · simp only [S, dif_pos h, dif_pos h.symm, dif_pos h1, dif_neg h1.not_gt]
            refine ⟨neg_mem (LiftS.ipow_star _ N.𝔡_ne N.𝔡_star _ ?_), by simp⟩
            rw [show -((r : ℤ) - a.val) - ((r : ℤ) - b.val) = -((r : ℤ) - b.val) - ((r : ℤ) - a.val) by ring]
            exact ht ⟨⟨(b, a), h1⟩, h.2⟩
        · simp [S, dif_neg h, dif_neg (mt And.symm h)]
      obtain ⟨s, hs, he, h⟩ := d4 S hS
      obtain ⟨p, hp⟩ := hex s hs
      have h1 := hu0 s p hp he
      have h2 : p.2.1 = 0 := by
        funext b v
        refine ((htop v s _ (hp v)).2.2 (h10 p h1 v) b 0 ?_).trans ?_
        · rw [h b.1 b.2, add_sub_cancel_left, sub_zero]
          refine Submodule.sum_mem _ fun a _ => ?_
          by_cases ha : N.j ≤ a.val
          · exact Submodule.smul_mem _ _ (NFGeom.e_mem_II N a ha)
          · simp [ha]
        · funext l
          simp [RealMat.phi_zero (hF v).1]
      have hSB : ∀ a b : Fin r, N.j ≤ a.val → N.j ≤ b.val → H.B (s (N.ist b)) (N.ist a) = S a b := by
        intro a b ha hb
        rw [h b hb]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_add (f := _), map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
          N.ist_iso b a hb ha, N.ist_e _ a ha]
        simp [ha]
      have h3 := fun v => hskew v s _ (hp v) (h10 p h1 v) (h20 p h2 v)
      have h4 : p = (0, 0, d) := by
        refine Prod.ext h1 (Prod.ext h2 (Prod.ext ?_ ?_))
        · funext i v
          have hi : N.j ≤ i.1.1.2.val := i.2.trans (le_of_lt i.1.2)
          refine ((h3 v).2.1 i).trans ?_
          rw [hSB _ _ i.2 hi]
          simp only [S, dif_pos (And.intro i.2 hi), dif_pos i.1.2]
          exact congrFun (htd i) v
        · funext a v
          refine ((h3 v).2.2 a).trans ?_
          rw [hSB _ _ a.2 a.2]
          simp only [S, dif_pos (And.intro a.2 a.2), dif_neg (lt_irrefl a.1)]
          exact congrFun (htd' a) v
      exact h4 ▸ ⟨s, hs, hp⟩
  · have hsc : ∀ (n : ℕ) (m : ℤ), m = -(n : ℤ) → (Ideal.absNorm N.𝔡 : ℝ) ^ m * (ρ ^ n) ^ (2 * Fintype.card ι) = 1 := by
      rintro n _ rfl
      rw [hN, _root_.zpow_neg, _root_.zpow_natCast, ← pow_mul, ← pow_mul, mul_comm n]
      exact inv_mul_cancel₀ (pow_pos hρ0 _).ne'
    have hsc' : ∀ (n : ℕ) (m : ℤ), m = -(n : ℤ) → Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι * (Ideal.absNorm N.𝔡 : ℝ) ^ m *
        ∏ _v : ι, ‖((ρ ^ n : ℝ) : ℂ)‖ ^ 2 = Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι := by
      intro n m h
      rw [Finset.prod_const, Finset.card_univ, Complex.norm_real, Real.norm_of_nonneg (pow_pos hρ0 n).le, ← pow_mul,
        mul_assoc, hsc n m h, mul_one]
    have e1 : ∀ i, volume (F₁ i) = ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι) := fun i => by
      rw [hF₁v, hsc']
      have : i.1.1.1.val < i.1.1.2.val := i.1.2
      omega
    have e2 : ∀ i, volume (F₂ i) = ENNReal.ofReal ((Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι) ^ (k + 1)) := fun i => by
      rw [hF₂v, mul_assoc, hsc, mul_one]
      have := i.1.2
      omega
    have e3 : ∀ i, volume (F₃ i) = ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι) := fun i => by
      rw [hF₃v, hsc']
      have := i.1.1.1.2
      have := i.1.1.2.2
      omega
    rw [hΩv]
    simp only [e1, e2, e3, Finset.prod_const, Finset.card_univ, card_top]
    refine GlobalTheory.T.layer_covolume_product_pow_two_sided_bounds _ _ k r _ _ _ _ hv (Nat.sub_le _ _) (card_UT r _) (card_UT r _) ?_ ?_
    · rw [← card_top, ← Finset.card_univ (α := {a : Fin r // N.j ≤ a.val}), ← Finset.prod_const]
      exact Finset.prod_le_prod' fun i _ => hF₄l i
    · rw [← card_top, ← Finset.card_univ (α := {a : Fin r // N.j ≤ a.val}), ← Finset.prod_const]
      exact Finset.prod_le_prod' fun i _ => hF₄u i

end GlobalTheory.DegVol.RefCov
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeReferenceLatticeStabiliserBoundsStatement
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_referenceLattice_stabiliser_bounds : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (β : Fin r → ℕ) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (z z' : ι → Fin (2 * r + k + 1) → ℂ) (g : ι → Mat k r), IsPlaces σ → Module.finrank K V = 2 * r + k + 1 → (∀ v, IsFrameOf N k (σ v) (2 * Formalism.HermitianLatticesTheory.vInv K) β (Φ v) (z v) (z' v) (g v)) → (Ideal.absNorm N.𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * Fintype.card ι) → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ L : Submodule (𝓞 K) V, IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F') → N.F.z ∈ L → ∃ Ω : Set (ι → Mt k r), IsFund (realPts Φ (N.Gam (N.Ref L) : Set (V ≃ₗ[K] V))) (RP k r g) Ω ∧ ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ (k * (r - N.j) * Fintype.card ι) / (8 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * (r + 1) ^ 2 * Fintype.card ι)) ≤ Measure.pi (fun _ : ι => lebR0 k r N.j β) Ω ∧ Measure.pi (fun _ : ι => lebR0 k r N.j β) Ω ≤ ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ (k * (r - N.j) * Fintype.card ι) * (8 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * (r + 1) ^ 2 * Fintype.card ι)) := by
  first | exact @GlobalTheory.DegVol.RefCov.covol_ref | exact GlobalTheory.DegVol.RefCov.covol_ref | (intros; apply GlobalTheory.DegVol.RefCov.covol_ref <;> assumption)
end
