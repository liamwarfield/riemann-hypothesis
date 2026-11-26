module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfTop
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfCV
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfLoc
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfSt
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct

def SubmDens : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)) (ν : Measure (Fin m → ℝ)), μ.IsAddHaarMeasure →
    ν.IsAddHaarMeasure → ∀ (f : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ 1 f →
      DensAll μ f id ν {x | Function.Surjective (fderiv ℝ f x)}

def SubmLocal : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)) (ν : Measure (Fin m → ℝ)), μ.IsAddHaarMeasure →
    ν.IsAddHaarMeasure → ∀ (f : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ 1 f →
      ∀ x0, Function.Surjective (fderiv ℝ f x0) → ∃ N, IsOpen N ∧ x0 ∈ N ∧ DensAll μ f id ν N

def CoordInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∃ (n m : ℕ) (eV : (Fin a → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → ℝ))
    (eH : HermR (Ainf F) σ a ≃ₜ (Fin m → ℝ)) (f' : (Fin n → ℝ) → (Fin m → ℝ)),
    (∀ x y, eV (x + y) = eV x + eV y) ∧ (∀ x y, eH (x + y) = eH x + eH y) ∧ ContDiff ℝ 1 f' ∧
    (∀ X, ((eH.symm (f' (eV X)) : HermR (Ainf F) σ a) : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) =
      gramR (Ainf F) σ J X) ∧
    ∀ X, LinearIndependent (Ainf F ⊗[F] E) X → Function.Surjective (fderiv ℝ f' (eV X))

section Transport

variable {V X Y V' X' : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace V'] [MeasurableSpace V']
  [BorelSpace V'] [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X']

theorem densAll_transport (μ : Measure V) (ν : Measure X) (f : V → Y) (ι : X → Y) (U : Set V)
    (eV : V ≃ₜ V') (eX : X ≃ₜ X') (f' : V' → X') (hι : Function.Injective ι)
    (hf : ∀ v, ι (eX.symm (f' (eV v))) = f v)
    (h : DensAll (μ.map eV) f' id (ν.map eX) (eV '' U)) : DensAll μ f ι ν U := by
  intro φ hc hs hU
  have hc' : Continuous (φ ∘ eV.symm) := hc.comp eV.symm.continuous
  have hs' : HasCompactSupport (φ ∘ eV.symm) := hs.comp_homeomorph eV.symm
  have hU' : tsupport (φ ∘ eV.symm) ⊆ eV '' U := by
    intro y hy
    have : eV.symm y ∈ tsupport φ := by
      have e : tsupport (φ ∘ eV.symm) = eV.symm ⁻¹' tsupport φ := by
        simpa using (tsupport_comp_eq_preimage φ eV.symm)
      rw [e] at hy; exact hy
    exact ⟨eV.symm y, hU this, by simp⟩
  obtain ⟨g', hg'c, hg'⟩ := h _ hc' hs' hU'
  refine ⟨g' ∘ eX, hg'c.comp eX.continuous, fun S hS => ?_⟩
  have e1 := hg' (eX '' S) (hS.image eX.continuous)
  rw [show ((μ.map eV)) = μ.map eV.toMeasurableEquiv from rfl,
    show ((ν.map eX)) = ν.map eX.toMeasurableEquiv from rfl,
    setIntegral_map_equiv, setIntegral_map_equiv] at e1
  have p1 : (eV.toMeasurableEquiv : V → V') ⁻¹' (f' ⁻¹' (id '' (eX '' S))) = f ⁻¹' (ι '' S) := by
    ext v
    simp only [Set.mem_preimage, Set.image_id, Set.mem_image, Homeomorph.toMeasurableEquiv_coe]
    constructor
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      rw [← hf v, ← hxe]; simp
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      rw [← hf v] at hxe
      have := hι hxe
      rw [this]; simp
  have p2 : (eX.toMeasurableEquiv : X → X') ⁻¹' (eX '' S) = S := by
    ext x; simp
  rw [p1, p2] at e1
  simpa [Homeomorph.toMeasurableEquiv_coe] using e1

end Transport

section Local

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X]

theorem densAll_mono {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X} {U U' : Set V}
    (h : DensAll μ f ι ν U') (hU : U ⊆ U') : DensAll μ f ι ν U := by
  intro φ hc hs hφ
  exact h φ hc hs (hφ.trans hU)

theorem densAll_of_local [T2Space V] [LocallyCompactSpace V] [OpensMeasurableSpace V]
    [OpensMeasurableSpace X] [T2Space X] {μ : Measure V} [IsFiniteMeasureOnCompacts μ] {ν : Measure X}
    [IsFiniteMeasureOnCompacts ν] {f : V → Y} {ι : X → Y} {U : Set V}
    (h : ∀ x ∈ U, ∃ N, IsOpen N ∧ x ∈ N ∧ DensAll μ f ι ν N) : DensAll μ f ι ν U := by
  intro φ hc hs hU
  choose N hNo hNx hND using h
  let K := tsupport φ
  have hK : IsCompact K := hs
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => N x.1 (hU x.2))
    (fun x => hNo _ _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hNx _ _⟩)
  let n := t.card
  let N' : K → Set V := fun x => N x.1 (hU x.2)
  let s : Fin n → Set V := fun i => N' (t.equivFin.symm i).1
  have hso : ∀ i, IsOpen (s i) := fun i => hNo _ _
  have hcov : K ⊆ ⋃ i, s i := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine Set.mem_iUnion.2 ⟨t.equivFin ⟨j, hj⟩, ?_⟩
    have e : s (t.equivFin ⟨j, hj⟩) = N' j := by simp only [s, Equiv.symm_apply_apply]
    rw [e]; exact hxj
  obtain ⟨ρ, hρs, hρ1, -, hρc⟩ := exists_continuous_sum_one_of_isOpen_isCompact hso hK hcov
  have hsum : ∀ x, φ x = ∑ i, φ x * ρ i x := by
    intro x
    by_cases hx : x ∈ K
    · have := hρ1 hx
      simp only [Finset.sum_apply, Pi.one_apply] at this
      rw [← Finset.mul_sum, this, mul_one]
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
  have hi : ∀ i, ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), φ v * ρ i v ∂μ = ∫ b in S, g b ∂ν := by
    intro i
    exact hND _ _ (fun v => φ v * ρ i v) (hc.mul (ρ i).continuous) (hs.mul_right)
      ((tsupport_mul_subset_right).trans (hρs i))
  choose g hgc hg using hi
  refine ⟨fun b => ∑ i, g i b, continuous_finsetSum _ fun i _ => hgc i, fun S hS => ?_⟩
  have e1 : ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∑ i, ∫ v in f ⁻¹' (ι '' S), φ v * ρ i v ∂μ := by
    rw [← integral_finsetSum]
    · exact integral_congr_ae (Filter.Eventually.of_forall fun x => hsum x)
    · intro i _
      exact ((hc.mul (ρ i).continuous).integrable_of_hasCompactSupport hs.mul_right).integrableOn
  rw [e1, integral_finsetSum]
  · exact Finset.sum_congr rfl fun i _ => hg i S hS
  · intro i _
    exact (hgc i).continuousOn.integrableOn_compact hS

end Local

theorem densInf_of (hSub : SubmDens) (hCo : CoordInf) : DensInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ μinf hμ νinf hν
  obtain ⟨n, m, eV, eH, f', hV, hH, hC, hG, hS⟩ :=
    hCo F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet
  have := hμ.1
  have := hν.1
  have : ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E) := ⟨by
    have e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) =>
        p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2) := by
      funext p; rw [← hV, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have : ContinuousAdd (HermR (Ainf F) σ a) := ⟨by
    have e : (fun p : HermR (Ainf F) σ a × HermR (Ainf F) σ a => p.1 + p.2) =
        fun p => eH.symm (eH p.1 + eH p.2) := by
      funext p; rw [← hH, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have hμ' : (μinf.map eV).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μinf (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective
      (eV.map_cocompact).le
  have hν' : (νinf.map eH).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map νinf (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective
      (eH.map_cocompact).le
  have hD := hSub n m _ _ hμ' hν' f' hC
  refine densAll_transport μinf νinf (gramR (Ainf F) σ J) Subtype.val _ eV eH f'
    Subtype.val_injective (fun X => hG X) (densAll_mono hD ?_)
  rintro y ⟨X, hX, rfl⟩
  exact hS X hX

end PI.VolStabS
end
end

noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology

def LinDens : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)) (ν : Measure (Fin m → ℝ)), μ.IsAddHaarMeasure →
    ν.IsAddHaarMeasure → ∀ A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ), Function.Surjective A →
      DensAll μ A id ν Set.univ

def ChangeVar : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)), μ.IsAddHaarMeasure →
    ∀ (f : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ 1 f → ∀ x0,
      Function.Surjective (fderiv ℝ f x0) →
      ∃ N, IsOpen N ∧ x0 ∈ N ∧ ∃ A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ), Function.Surjective A ∧
        ∀ φ : (Fin n → ℝ) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ N →
          ∃ G : (Fin n → ℝ) → ℝ, Continuous G ∧ HasCompactSupport G ∧
            ∀ S : Set (Fin m → ℝ), IsCompact S →
              ∫ v in f ⁻¹' S, φ v ∂μ = ∫ v in A ⁻¹' S, G v ∂μ

theorem submLocal_of (h1 : LinDens) (h2 : ChangeVar) : SubmLocal := by
  intro n m μ ν hμ hν f hf x0 hx0
  obtain ⟨N, hN, hxN, A, hA, hG⟩ := h2 n m μ hμ f hf x0 hx0
  refine ⟨N, hN, hxN, fun φ hc hs hφ => ?_⟩
  obtain ⟨G, hGc, hGs, hGe⟩ := hG φ hc hs hφ
  obtain ⟨g, hgc, hg⟩ := h1 n m μ ν hμ hν A hA G hGc hGs (Set.subset_univ _)
  refine ⟨g, hgc, fun S hS => ?_⟩
  have := hg S hS
  simp only [Set.image_id] at this ⊢
  rw [hGe S hS, this]

theorem submDens_of_local (h : SubmLocal) : SubmDens := by
  intro n m μ ν hμ hν f hf
  exact densAll_of_local fun x hx => h n m μ ν hμ hν f hf x hx

theorem linDens_holds : LinDens := by
  intro n m μ ν hμ hν A hA φ hc hs _
  obtain ⟨B, hB⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hA)
  have hRI : Function.RightInverse B A := fun y => by
    simpa using congrArg (fun L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => L y) hB
  let T := ContinuousLinearEquiv.equivOfRightInverse A B hRI
  let K := A.ker
  let lam : Measure K := Measure.addHaar
  have hT1 : ∀ x, (T x).1 = A x := fun x => rfl
  have hμT : (μ.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  obtain ⟨c, hsm⟩ : ∃ c : ENNReal, μ.map T = c • (ν.prod lam) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  let H : (Fin m → ℝ) × K → ℝ := fun w => φ (T.symm w)
  have hHc : Continuous H := hc.comp T.symm.continuous
  have hHs : HasCompactSupport H := hs.comp_homeomorph T.symm.toHomeomorph
  let s : Set K := Prod.snd '' tsupport H
  have hsc : IsCompact s := hHs.image continuous_snd
  let ψ : (Fin m → ℝ) → ℝ := fun y => ∫ k in s, H (y, k) ∂lam
  have hψc : Continuous ψ :=
    continuous_parametric_integral_of_continuous (f := fun y k => H (y, k)) hHc hsc
  have hψ : ∀ y, ∫ k, H (y, k) ∂lam = ψ y := by
    intro y
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun k hk => ?_).symm
    apply image_eq_zero_of_notMem_tsupport
    intro h'
    exact hk ⟨(y, k), h', rfl⟩
  refine ⟨fun y => c.toReal * ψ y, continuous_const.mul hψc, fun S hS => ?_⟩
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  simp only [Set.image_id]
  let Q : (Fin m → ℝ) × K → ℝ := (Prod.fst ⁻¹' S).indicator H
  have hQ : ∀ v, (A ⁻¹' S).indicator φ v = Q (T v) := by
    intro v
    simp only [Q, Set.indicator, H, ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hQi : Integrable Q (ν.prod lam) :=
    (hHc.integrable_of_hasCompactSupport hHs).indicator (measurable_fst hSm)
  rw [← integral_indicator (hSm.preimage A.continuous.measurable)]
  simp_rw [hQ]
  have e2 : ∫ v, Q (T v) ∂μ = ∫ w, Q w ∂(μ.map T) := by
    rw [show (μ.map T) = μ.map T.toHomeomorph.toMeasurableEquiv from rfl, integral_map_equiv]
    rfl
  rw [e2, hsm, integral_smul_measure, integral_prod _ hQi, smul_eq_mul,
    ← integral_indicator hSm, ← integral_const_mul]
  congr 1
  funext y
  by_cases hy : y ∈ S
  · simp only [Q, Set.indicator, Set.mem_preimage, hy, if_true, ← hψ y]
  · simp [Q, Set.indicator, hy]

end PI.VolStabS
end
end

noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology

theorem changeVar_holds : ChangeVar := by
  intro n m μ hμ f hf x0 hx0
  let A := fderiv ℝ f x0
  obtain ⟨B, hB⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hx0)
  have hRI : Function.RightInverse B A := fun y => by
    simpa using congrArg (fun L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => L y) hB
  let T := ContinuousLinearEquiv.equivOfRightInverse A B hRI
  have hT1 : ∀ x, (T x).1 = A x := fun x => rfl
  let Θ : (Fin n → ℝ) → (Fin n → ℝ) := fun x => T.symm (f x, (T x).2)
  have hΘc : ContDiff ℝ 1 Θ :=
    T.symm.contDiff.comp (hf.prodMk (contDiff_snd.comp T.contDiff))
  have hfA : ∀ x, A (Θ x) = f x := by
    intro x
    rw [← hT1]; simp [Θ]
  have hd : ∀ x, HasFDerivAt Θ (fderiv ℝ Θ x) x :=
    fun x => ((hΘc.differentiable one_ne_zero) x).hasFDerivAt
  have hid : fderiv ℝ Θ x0 = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    let P := (ContinuousLinearMap.snd ℝ (Fin m → ℝ) A.ker).comp T.toContinuousLinearMap
    have hP : HasFDerivAt (fun x => (T x).2) P x0 := P.hasFDerivAt
    have h1 : HasFDerivAt (fun x => (f x, (T x).2)) ((fderiv ℝ f x0).prod P) x0 :=
      ((hf.differentiable one_ne_zero) x0).hasFDerivAt.prodMk hP
    have h2 := T.symm.toContinuousLinearMap.hasFDerivAt.comp x0 h1
    rw [show fderiv ℝ Θ x0 = T.symm.toContinuousLinearMap.comp ((fderiv ℝ f x0).prod P) from
      h2.fderiv]
    ext1 y
    change T.symm ((fderiv ℝ f x0) y, (T y).2) = y
    have : ((fderiv ℝ f x0) y, (T y).2) = T y := Prod.ext (hT1 y).symm rfl
    rw [this, ContinuousLinearEquiv.symm_apply_apply]
  have hs : HasStrictFDerivAt Θ
      ((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x0 := by
    have := hΘc.contDiffAt.hasStrictFDerivAt_fderiv (x := x0) one_ne_zero
    rw [hid] at this
    exact this
  let PH := hs.toOpenPartialHomeomorph Θ
  have hPH : ∀ x, PH x = Θ x := fun x => rfl
  let D : (Fin n → ℝ) → ℝ := fun x => (fderiv ℝ Θ x).det
  have hDc : Continuous D :=
    ContinuousLinearMap.continuous_det.comp (hΘc.continuous_fderiv one_ne_zero)
  let N := PH.source ∩ {x | D x ≠ 0}
  have hNo : IsOpen N := PH.open_source.inter (isOpen_ne_fun hDc continuous_const)
  have hx0N : x0 ∈ N := ⟨hs.mem_toOpenPartialHomeomorph_source, by
    show (fderiv ℝ Θ x0).det ≠ 0
    rw [hid, ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]
    norm_num⟩
  refine ⟨N, hNo, hx0N, A, hx0, fun φ hc hsφ hφN => ?_⟩
  let C := PH '' tsupport φ
  have hNsrc : N ⊆ PH.source := Set.inter_subset_left
  have hCc : IsCompact C :=
    hsφ.image_of_continuousOn (PH.continuousOn.mono (hφN.trans hNsrc))
  let G : (Fin n → ℝ) → ℝ := PH.target.indicator fun z => φ (PH.symm z) / |D (PH.symm z)|
  have hGC : ∀ z, z ∉ C → G z = 0 := by
    intro z hz
    by_cases ht : z ∈ PH.target
    · simp only [G, Set.indicator_of_mem ht]
      have : φ (PH.symm z) = 0 := by
        by_contra h0
        exact hz ⟨PH.symm z, subset_tsupport _ h0, PH.right_inv ht⟩
      rw [this, zero_div]
    · simp [G, ht]
  have hNimg : IsOpen (PH '' N) := PH.isOpen_image_of_subset_source hNo hNsrc
  have hCN : C ⊆ PH '' N := Set.image_mono hφN
  have hGcont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ PH '' N
    · obtain ⟨x, hxN, rfl⟩ := hz
      have hxs : x ∈ PH.source := hNsrc hxN
      have hev : G =ᶠ[𝓝 (PH x)] fun z => φ (PH.symm z) / |D (PH.symm z)| := by
        filter_upwards [PH.open_target.mem_nhds (PH.map_source hxs)] with z hz
        simp [G, Set.indicator_of_mem hz]
      refine ContinuousAt.congr ?_ hev.symm
      have hsymm : ContinuousAt PH.symm (PH x) := PH.continuousAt_symm (PH.map_source hxs)
      have hD0 : D (PH.symm (PH x)) ≠ 0 := by rw [PH.left_inv hxs]; exact hxN.2
      exact (hc.continuousAt.comp hsymm).div
        ((continuous_abs.continuousAt).comp (hDc.continuousAt.comp hsymm))
        (abs_ne_zero.2 hD0)
    · have hzC : z ∉ C := fun h => hz (hCN h)
      have hev : G =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [hCc.isClosed.isOpen_compl.mem_nhds hzC] with w hw
        exact hGC w hw
      exact (continuousAt_const).congr hev.symm
  have hGs : HasCompactSupport G := HasCompactSupport.intro hCc hGC
  refine ⟨G, hGcont, hGs, fun S hS => ?_⟩
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hNm : MeasurableSet N := hNo.measurableSet
  have hJ := integral_image_eq_integral_abs_det_fderiv_smul μ hNm
    (fun x _ => (hd x).hasFDerivWithinAt) (PH.injOn.mono hNsrc)
    ((A ⁻¹' S).indicator G)

  have hL : ∫ x in Θ '' N, (A ⁻¹' S).indicator G x ∂μ = ∫ v in A ⁻¹' S, G v ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_indicator
      (hSm.preimage A.continuous.measurable)]
    intro z hz
    have : G z = 0 := hGC z fun h => hz (hCN h)
    simp [Set.indicator, this]

  have hR : ∫ x in N, |(fderiv ℝ Θ x).det| • (A ⁻¹' S).indicator G (Θ x) ∂μ =
      ∫ v in f ⁻¹' S, φ v ∂μ := by
    have e1 : ∀ x ∈ N, |(fderiv ℝ Θ x).det| • (A ⁻¹' S).indicator G (Θ x) =
        (f ⁻¹' S).indicator φ x := by
      intro x hxN
      have hxs : x ∈ PH.source := hNsrc hxN
      have ht : Θ x ∈ PH.target := PH.map_source hxs
      have hl : PH.symm (Θ x) = x := PH.left_inv hxs
      have hD : D x ≠ 0 := hxN.2
      by_cases hfS : f x ∈ S
      · have h1 : Θ x ∈ A ⁻¹' S := by simp [hfA, hfS]
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show x ∈ f ⁻¹' S from hfS)]
        simp only [G, Set.indicator_of_mem ht, hl, smul_eq_mul]
        change |D x| * (φ x / |D x|) = φ x
        field_simp
      · have h1 : Θ x ∉ A ⁻¹' S := by simp [hfA, hfS]
        rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (show x ∉ f ⁻¹' S from hfS),
          smul_zero]
    rw [setIntegral_congr_fun hNm e1, setIntegral_eq_integral_of_forall_compl_eq_zero,
      integral_indicator (hSm.preimage (hf.continuous.measurable))]
    intro x hx
    have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hφN h)
    simp [Set.indicator, this]
  rw [← hR, ← hL, hJ]

end PI.VolStabS
end
end

noncomputable section

namespace PI.VolStabS

theorem submLocal_holds : SubmLocal := submLocal_of linDens_holds changeVar_holds

theorem submDens_holds : SubmDens := submDens_of_local submLocal_holds

theorem densInf_of_coord (h : CoordInf) : DensInf := densInf_of submDens_holds h

end PI.VolStabS
end
end

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
open PI.AdicCompletionValuation

def QuadCoord : Prop :=
  ∀ (V H : Type) [AddCommGroup V] [TopologicalSpace V] [AddCommGroup H] [TopologicalSpace H]
    (n m : ℕ) (eV : V ≃ₜ (Fin n → ℝ)) (eH : H ≃ₜ (Fin m → ℝ)) (Q : V → H) (β : V → V → H),
    (∀ x y, eV (x + y) = eV x + eV y) → (∀ x y, eH (x + y) = eH x + eH y) →
    Continuous (fun p : V × V => β p.1 p.2) → (∀ x y z, β (x + y) z = β x z + β y z) →
    (∀ x y, β x y = β y x) → (∀ x, β x x = Q x + Q x) →
    ContDiff ℝ 1 (fun y => eH (Q (eV.symm y))) ∧
      ∀ x y, fderiv ℝ (fun y => eH (Q (eV.symm y))) (eV x) (eV y) = eH (β x y)

theorem quadCoord_holds : QuadCoord := by
  intro V H _ _ _ _ n m eV eH Q β hV hH hβc hβa hβs hQ
  have hVs : ∀ y z, eV.symm (y + z) = eV.symm y + eV.symm z := by
    intro y z; apply eV.injective; rw [hV]; simp
  let b : (Fin n → ℝ) → (Fin n → ℝ) → (Fin m → ℝ) := fun y z => eH (β (eV.symm y) (eV.symm z))
  have hb1 : ∀ y y' z, b y z + b y' z = b (y + y') z := by
    intro y y' z; simp only [b, hVs, hβa, hH]
  have hb2 : ∀ y z z', b y (z + z') = b y z + b y z' := by
    intro y z z'; simp only [b, hVs]
    rw [hβs, hβa, hH, hβs (eV.symm z), hβs (eV.symm z')]
  have hbc : Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) => b p.1 p.2) :=
    eH.continuous.comp (hβc.comp ((eV.symm.continuous.comp continuous_fst).prodMk
      (eV.symm.continuous.comp continuous_snd)))
  let L1 : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) := fun y =>
    AddMonoidHom.toRealLinearMap (AddMonoidHom.mk' (b y) (hb2 y))
      (hbc.comp (continuous_const.prodMk continuous_id))
  have hL1 : ∀ y z, L1 y z = b y z := fun _ _ => rfl
  have hsm1 : ∀ (c : ℝ) y z, b (c • y) z = c • b y z := by
    intro c y z
    have : b (c • y) z = c • b y z := (AddMonoidHom.toRealLinearMap (AddMonoidHom.mk' (fun y => b y z)
      (fun y y' => (hb1 y y' z).symm)) (hbc.comp (continuous_id.prodMk continuous_const))).map_smul c y
    exact this
  let Bl : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) :=
    { toFun := L1
      map_add' := fun y y' => by ext1 z; simp only [add_apply, hL1, hb1]
      map_smul' := fun c y => by
        ext1 z; simp only [smul_apply, hL1, hsm1, RingHom.id_apply] }
  let B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) := LinearMap.toContinuousLinearMap Bl
  have hB : ∀ y z, B y z = b y z := fun _ _ => rfl
  have hf : ∀ y, eH (Q (eV.symm y)) = (1/2 : ℝ) • B y y := by
    intro y
    rw [hB]
    simp only [b, hQ, hH]
    rw [← two_smul ℝ (eH (Q (eV.symm y))), smul_smul]
    norm_num
  have hfe : (fun y => eH (Q (eV.symm y))) = fun y => (1/2 : ℝ) • B y y := funext hf
  have hd : ∀ y, HasFDerivAt (fun y => (1/2 : ℝ) • B y y)
      ((1/2 : ℝ) • (B.precompR (Fin n → ℝ) y (ContinuousLinearMap.id ℝ _) +
        B.precompL (Fin n → ℝ) (ContinuousLinearMap.id ℝ _) y)) y :=
    fun y => by
      have h := (B.hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)).const_smul
        (1/2 : ℝ)
      exact h
  refine ⟨?_, fun x y => ?_⟩
  · rw [hfe]
    exact (B.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)).const_smul
      (1/2 : ℝ)
  · rw [hfe, (hd _).fderiv]
    show (1/2 : ℝ) • (B (eV x) (eV y) + B (eV y) (eV x)) = eH (β x y)
    rw [hB, hB]
    simp only [b, Homeomorph.symm_apply_apply]
    rw [hβs y x, ← two_smul ℝ (eH (β x y)), smul_smul]
    norm_num

section B

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def gramB (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y : Fin n → Fin M → R ⊗[F] E) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  fun i j => hR R σ J (X i) (Y j) + hR R σ J (Y i) (X j)

theorem hR_add_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x y z : Fin M → R ⊗[F] E) : hR R σ J (x + y) z = hR R σ J x z + hR R σ J y z := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hR_add_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x y z : Fin M → R ⊗[F] E) : hR R σ J x (y + z) = hR R σ J x y + hR R σ J x z := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hR_herm (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x y) = hR R σ J y x := by
  have hJR : ∀ i j, sigR R σ (JR R J i j) = JR R J j i := by
    intro i j; simp [JR, inclR, sigR, hJ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, map_sum, map_mul, sigR_invol R σ hσ, hJR]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem gramB_mem (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (X Y : Fin n → Fin M → R ⊗[F] E) : gramB R σ J X Y ∈ HermR R σ n := by
  intro a b
  simp only [gramB, map_add (f := _), hR_herm R σ hσ J hJ]
  ring

end B

section BTop

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

theorem continuous_gramB_apply (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (a b : Fin n) : Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      gramB R σ J p.1 p.2 a b) := by
  show Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
    hR R σ J (p.1 a) (p.2 b) + hR R σ J (p.2 a) (p.1 b))
  have hc := continuous_hR R σ J
  have e1 : Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      ((p.1 a, p.2 b) : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E))) := by fun_prop
  have e2 : Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      ((p.2 a, p.1 b) : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E))) := by fun_prop
  have h1 := Continuous.comp (g := fun q : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E) =>
      hR R σ J q.1 q.2) hc e1
  have h2 := Continuous.comp (g := fun q : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E) =>
      hR R σ J q.1 q.2) hc e2
  exact h1.add h2

theorem continuous_gramB (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      gramB R σ J p.1 p.2) :=
  continuous_pi fun a => continuous_pi fun b => continuous_gramB_apply R σ J a b

end BTop

def TensR : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∃ (n m : ℕ) (eV : (Fin a → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → ℝ))
    (eH : HermR (Ainf F) σ a ≃ₜ (Fin m → ℝ)),
    (∀ x y, eV (x + y) = eV x + eV y) ∧ ∀ x y, eH (x + y) = eH x + eH y

def FreeSurj : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ X : Fin a → Fin M → Ainf F ⊗[F] E, LinearIndependent (Ainf F ⊗[F] E) X →
    ∀ S : HermR (Ainf F) σ a, ∃ Y, gramB (Ainf F) σ J X Y = S

theorem coordInf_of (h1 : QuadCoord) (h2 : TensR) (h3 : FreeSurj) : CoordInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a hA1 hA2 X0 hT0 hdet
  obtain ⟨n, m, eV, eH, hV, hH⟩ := h2 F E σ hCM M J hJ ha hc a hA1 hA2 X0 hT0 hdet
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  let Q : (Fin a → Fin M → Ainf F ⊗[F] E) → HermR (Ainf F) σ a := gramH (Ainf F) σ hσ J hJ.1
  let β : (Fin a → Fin M → Ainf F ⊗[F] E) → (Fin a → Fin M → Ainf F ⊗[F] E) →
      HermR (Ainf F) σ a := fun X Y => ⟨gramB (Ainf F) σ J X Y, gramB_mem (Ainf F) σ hσ J hJ.1 X Y⟩
  have hβc : Continuous (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (Fin a → Fin M → Ainf F ⊗[F] E) => β p.1 p.2) := by
    exact (continuous_gramB (Ainf F) σ J).subtype_mk _
  have hβa : ∀ x y z, β (x + y) z = β x z + β y z := by
    intro x y z; apply Subtype.ext; funext i j
    show gramB (Ainf F) σ J (x + y) z i j = gramB (Ainf F) σ J x z i j + gramB (Ainf F) σ J y z i j
    simp only [gramB, Pi.add_apply, hR_add_left, hR_add_right]
    abel
  have hβs : ∀ x y, β x y = β y x := by
    intro x y; apply Subtype.ext; funext i j
    simp only [β, gramB]; exact add_comm _ _
  have hQ : ∀ x, β x x = Q x + Q x := by
    intro x; apply Subtype.ext; funext i j; rfl
  obtain ⟨hC, hD⟩ := h1 _ _ n m eV eH Q β hV hH hβc hβa hβs hQ
  refine ⟨n, m, eV, eH, fun y => eH (Q (eV.symm y)), hV, hH, hC, fun X => ?_, fun X hX => ?_⟩
  · simp [Q, gramH]
  · intro t
    obtain ⟨Y, hY⟩ := h3 F E σ hCM M J hJ ha hc a hA1 hA2 X0 hT0 hdet X hX (eH.symm t)
    refine ⟨eV Y, ?_⟩
    rw [hD X Y]
    have : β X Y = eH.symm t := Subtype.ext hY
    rw [this, Homeomorph.apply_symm_apply]

theorem densInf_of_tens (h2 : TensR) (h3 : FreeSurj) : DensInf :=
  densInf_of_coord (coordInf_of quadCoord_holds h2 h3)

end PI.VolStabS
