module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledStabilizerWeilOperatorTransportsLatticeEi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalUnitaryActionPreserves
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalUnramifiedVector

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLinearWittModelNonvanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLinearWittModelNonvanishing
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LinearModelL2

section General

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

def ip (μ : Measure X) (f g : X → ℂ) : ℂ := ∫ y, f y * (starRingEnd ℂ) (g y) ∂μ

theorem integrable_mul_conj (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {f g : X → ℂ} (hf : f ∈ SB X)
    (hg : g ∈ SB X) : Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ := by
  have hcf : Continuous f := hf.1.continuous
  have hcg : Continuous g := hg.1.continuous
  have hs : HasCompactSupport (fun y => f y * (starRingEnd ℂ) (g y)) := hf.2.mul_right
  exact (hcf.mul (Complex.continuous_conj.comp hcg)).integrable_of_hasCompactSupport hs

theorem ip_smul_smul (μ : Measure X) (a b : ℂ) (f g : X → ℂ) :
    ip μ (a • f) (b • g) = a * (starRingEnd ℂ) b * ip μ f g := by
  unfold ip
  rw [← integral_const_mul]
  congr 1
  funext y
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem ip_sum_sum (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {V : Type} (F : Finset V) (a : V → ℂ)
    (xs : V → X → ℂ) (hxs : ∀ y, xs y ∈ SB X) :
    ip μ (∑ y ∈ F, a y • xs y) (∑ y ∈ F, a y • xs y) =
      ∑ y ∈ F, ∑ y' ∈ F, a y * (starRingEnd ℂ) (a y') * ip μ (xs y) (xs y') := by
  unfold ip
  have e : (fun z => (∑ y ∈ F, a y • xs y) z * (starRingEnd ℂ) ((∑ y ∈ F, a y • xs y) z)) =
      fun z => ∑ y ∈ F, ∑ y' ∈ F, a y * (starRingEnd ℂ) (a y') * (xs y z * (starRingEnd ℂ) (xs y' z)) := by
    funext z
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    rw [map_mul]
    ring
  rw [e, integral_finsetSum _ (fun y _ => integrable_finsetSum _ fun y' _ =>
    (integrable_mul_conj μ (hxs y) (hxs y')).const_mul _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_finsetSum _ (fun y' _ => (integrable_mul_conj μ (hxs y) (hxs y')).const_mul _)]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [integral_const_mul]

theorem ip_self (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {f : X → ℂ} (hf : f ∈ SB X) :
    ip μ f f = (((∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) ∧ ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ := by
  have hcf : Continuous f := hf.1.continuous
  have hs : HasCompactSupport ((fun z : ℂ => ‖z‖ ^ 2) ∘ f) :=
    hf.2.comp_left (by norm_num : ‖(0 : ℂ)‖ ^ 2 = 0)
  have hint : Integrable (fun y => ‖f y‖ ^ 2) μ := (hcf.norm.pow 2).integrable_of_hasCompactSupport hs
  have hE : ∀ y, ENNReal.ofReal (‖f y‖ ^ 2) = ‖f y‖ₑ ^ 2 := fun y => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hfin := hint.lintegral_lt_top
  simp only [hE] at hfin
  refine ⟨?_, hfin.ne⟩
  unfold ip
  have e : (fun y => f y * (starRingEnd ℂ) (f y)) = fun y => (((‖f y‖ ^ 2 : ℝ)) : ℂ) := by
    funext y
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e, integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => by positivity)
    hint.aestronglyMeasurable]
  simp only [hE]

theorem lintegral_ne_zero (μ : Measure X) [μ.IsOpenPosMeasure] {f : X → ℂ} (hf : f ∈ SB X) (h0 : f ≠ 0) :
    ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ 0 := by
  have hc : Continuous f := hf.1.continuous
  have hcont : Continuous fun Y => ‖f Y‖ₑ ^ 2 := (ENNReal.continuous_pow 2).comp hc.enorm
  intro h
  rw [lintegral_eq_zero_iff hcont.measurable] at h
  have h' := (Continuous.ae_eq_iff_eq μ hcont continuous_zero).1 h
  apply h0
  funext Y
  have := congrFun h' Y
  simpa using this

end General

end GlobalTheory.LinearModelL2

namespace GlobalTheory.LinearModelL2

open GlobalTheory.LinSchur

section Cosets

variable {T : Type} [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]


open Classical in
theorem expand (μ : Measure T) [IsFiniteMeasureOnCompacts μ] {V : Type} [AddGroup V]
    (ι : (T → ℂ) →ₗ[ℂ] (V → ℂ)) (hinj : Set.InjOn ι (SB T)) (L : AddSubgroup V) (xs : V → T → ℂ)
    (hxs : ∀ y, xs y ∈ SB T) (hιxs : ∀ y, ι (xs y) = cind L y) (c : ℂ)
    (hP : ∀ y y', ip μ (xs y) (xs y') = if y - y' ∈ L then c else 0) (x : T → ℂ) (hx : x ∈ SB T) (f : V → ℂ)
    (hf : ι x = f) (F : Finset V) (hF : f = ∑ y ∈ F, f y • cind L y) :
    ip μ x x = (∑ y ∈ F, ∑ y' ∈ F, if y - y' ∈ L then f y * (starRingEnd ℂ) (f y') else 0) * c := by
  have hxe : x = ∑ y ∈ F, f y • xs y := by
    refine hinj hx (Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (hxs y)) ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hf, map_sum]
    simp only [map_smul, hιxs]
    exact hF
  rw [hxe, ip_sum_sum μ F f xs hxs, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [hP]
  split_ifs <;> ring

open Classical in
theorem cind_eq_of_sub_mem {V : Type} [AddGroup V] (L : AddSubgroup V) {y y' : V} (h : y - y' ∈ L) :
    cind L y = cind L y' := by
  funext Y
  unfold cind
  have iff : Y - y ∈ L ↔ Y - y' ∈ L := by
    rw [← sub_add_sub_cancel Y y y']
    exact (L.add_mem_cancel_right h).symm
  exact if_congr iff rfl rfl

theorem cind_translate {V : Type} [AddGroup V] (L : AddSubgroup V) (y : V) :
    (fun Y => cind L 0 (Y + -y)) = cind L y := by
  funext Y
  unfold cind
  rw [sub_zero, ← sub_eq_add_neg]

end Cosets

end GlobalTheory.LinearModelL2

namespace GlobalTheory.LinearModelL2

open GlobalTheory.LinSchur


open Classical in
theorem ip_cind {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V]
    [BorelSpace V] (ν : Measure V) [ν.IsAddRightInvariant] (L : AddSubgroup V) (y y' : V) :
    ip ν (cind L y) (cind L y') = if y - y' ∈ L then ip ν (cind L 0) (cind L 0) else 0 := by
  split_ifs with h
  · rw [cind_eq_of_sub_mem L h, ← cind_translate L y']
    unfold ip
    exact integral_add_right_eq_self (fun Y => cind L 0 Y * (starRingEnd ℂ) (cind L 0 Y)) (-y')
  · unfold ip
    have e : (fun Y => cind L y Y * (starRingEnd ℂ) (cind L y' Y)) = fun _ => 0 := by
      funext Y
      unfold cind
      by_cases h1 : Y - y ∈ L
      · by_cases h2 : Y - y' ∈ L
        · exact absurd (by simpa [sub_sub_sub_cancel_left] using L.sub_mem h2 h1) h
        · simp [h2]
      · simp [h1]
    rw [e, integral_zero]


open Classical in
theorem ip_cosets {T : Type} [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    (μ : Measure T) (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0)
    (ι : (T → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)) (hinj : Set.InjOn ι (SB T))
    (Tr : Matrix (Fin n) (Fin d) k → (T → ℂ) → T → ℂ) (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → (T → ℂ) → T → ℂ)
    (hTr : ∀ C, ∀ φ ∈ SB T, Tr C φ ∈ SB T ∧ ι (Tr C φ) = fun Y => ι φ (Y + C))
    (hMu : ∀ l, ∀ φ ∈ SB T, Mu l φ ∈ SB T ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y)
    (hTrI : ∀ C φ φ', ip μ (Tr C φ) (Tr C φ') = ip μ φ φ')
    (hMuI : ∀ l φ φ', ip μ (Mu l φ) (Mu l φ') = ip μ φ φ')
    (s : k) (x0 : T → ℂ) (hx0 : x0 ∈ SB T) (hιx0 : ι x0 = cind (latt ψ0 n d s) 0)
    (y y' : Matrix (Fin n) (Fin d) k) :
    ip μ (Tr (-y) x0) (Tr (-y') x0) = if y - y' ∈ latt ψ0 n d s then ip μ x0 x0 else 0 := by
  have hx : ∀ z, Tr (-z) x0 ∈ SB T ∧ ι (Tr (-z) x0) = cind (latt ψ0 n d s) z := fun z =>
    ⟨(hTr _ _ hx0).1, by rw [(hTr _ _ hx0).2, hιx0]; exact cind_translate _ z⟩
  split_ifs with h
  · have e : Tr (-y) x0 = Tr (-y') x0 :=
      hinj (hx y).1 (hx y').1 (by rw [(hx y).2, (hx y').2]; exact cind_eq_of_sub_mem _ h)
    rw [e, hTrI]
  · obtain ⟨l, hl1, hl2⟩ := dual h
    have hm : ∀ z, Mu l (Tr (-z) x0) = ψ0 (l z) • Tr (-z) x0 := fun z => by
      refine hinj (hMu l _ (hx z).1).1 (Submodule.smul_mem _ _ (hx z).1) ?_
      rw [(hMu l _ (hx z).1).2, map_smul, (hx z).2]
      funext Y
      simp only [Pi.smul_apply, smul_eq_mul]
      unfold cind
      split_ifs with hY
      · rw [mul_one, mul_one, show l Y = l (Y - z) + l z by rw [← map_add (f := _), sub_add_cancel],
          AddChar.map_add_eq_mul, hl1 _ hY, one_mul]
      · simp
    have e := hMuI l (Tr (-y) x0) (Tr (-y') x0)
    rw [hm y, hm y', ip_smul_smul] at e
    have hconj : ∀ w, (starRingEnd ℂ) (ψ0 w) = ψ0 (-w) := fun w => by
      have h1 : ψ0 w * (starRingEnd ℂ) (ψ0 w) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, GlobalTheory.norm_addChar_nonarch ψ0 hψ w]
        simp
      have h2 : ψ0 w * ψ0 (-w) = 1 := by
        rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
      exact mul_left_cancel₀ (addChar_ne_zero ψ0 w) (h1.trans h2.symm)
    rw [hconj, ← AddChar.map_add_eq_mul, ← map_neg, ← map_add (f := _), ← sub_eq_add_neg] at e
    have e2 : (ψ0 (l (y - y')) - 1) * ip μ (Tr (-y) x0) (Tr (-y') x0) = 0 := by linear_combination e
    rcases mul_eq_zero.mp e2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) hl2
    · exact h3

end GlobalTheory.LinearModelL2

namespace GlobalTheory.LinearModelL2

open GlobalTheory.LinSchur
open scoped GlobalTheory.VacAny GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem linIso_lintegral_eq : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
    (∀ μ : @Measure (Fin a × Fin (a + a') → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ x, ‖φ₁ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∀ ν : @Measure (Matrix (Fin a) (Fin (a + a')) (Fv F v)) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖ι φ₁ Y‖ₑ ^ 2 ∂ν = ∫⁻ Y, ‖ι φ Y‖ₑ ^ 2 ∂ν := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hv t ι hι φ hφ φ₁ hφ₁ hnorm ν hν
  letI : MeasurableSpace (Fin a × Fin (a + a') → Fv F v) := borel _
  haveI : BorelSpace (Fin a × Fin (a + a') → Fv F v) := ⟨rfl⟩
  letI : MeasurableSpace (Matrix (Fin a) (Fin (a + a')) (Fv F v)) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin (a + a')) (Fv F v)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin (a + a')) (Fv F v)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin (a + a') → Fv F v))
  haveI := hν
  let μ : Measure (Fin a × Fin (a + a') → Fv F v) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨hψc, hψ1, wT, wM, hA⟩ := GlobalTheory.UnitWShape.heisW B G X om om' hTr v t 1 id (fun f hf => hf)
    (fun γ _ f _ => by simp [actAB, mat])
  obtain ⟨hT0, hM0, -, -⟩ := hA ι hι
  have hbij := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  have hmaps := hbij.mapsTo
  have hsb : ∀ w, ∀ f ∈ SB (Fin a × Fin (a + a') → Fv F v), schr (GlobalTheory.LatVac.psiAt B.ψ v) w f ∈ SB _ :=
    fun w f hf => GlobalTheory.SchrSB.schr_mem_SB B.ψ hTr.base.std.1 v w f hf
  have hU : ∀ w f f', ip μ (schr (GlobalTheory.LatVac.psiAt B.ψ v) w f) (schr (GlobalTheory.LatVac.psiAt B.ψ v) w f') = ip μ f f' :=
    fun w f f' => GlobalTheory.schr_unitary (GlobalTheory.LatVac.psiAt B.ψ v) hψc μ hμ w f f'
  obtain ⟨hLoc, hBasis⟩ := GlobalTheory.T.characterTrivialMatrixLattice_open_compact_basis a (a + a') (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1
  have hB' : ∀ W ∈ 𝓝 (0 : Matrix (Fin a) (Fin (a + a')) (Fv F v)), ∃ i : {s : Fv F v // s ≠ 0},
      (latt (GlobalTheory.LatVac.psiAt B.ψ v) a (a + a') i.1 : Set _) ⊆ W := fun W hW => by
    obtain ⟨s, hs, h⟩ := hBasis W hW
    exact ⟨⟨s, hs⟩, h⟩
  obtain ⟨⟨s1, hs1⟩, hper1⟩ := GlobalTheory.T.exists_openSubgroup_periodic (fun s : {s : Fv F v // s ≠ 0} => latt (GlobalTheory.LatVac.psiAt B.ψ v) a (a + a') s.1)
    (fun s => (hLoc s.1 s.2).1) hB' (ι φ) (hmaps hφ)
  obtain ⟨⟨s2, hs2⟩, hper2⟩ := GlobalTheory.T.exists_openSubgroup_periodic (fun s : {s : Fv F v // s ≠ 0} => latt (GlobalTheory.LatVac.psiAt B.ψ v) a (a + a') s.1)
    (fun s => (hLoc s.1 s.2).1) hB' (ι φ₁) (hmaps hφ₁)
  obtain ⟨s, hs, hsub⟩ := hBasis ((latt (GlobalTheory.LatVac.psiAt B.ψ v) a (a + a') s1 : Set _) ∩ latt (GlobalTheory.LatVac.psiAt B.ψ v) a (a + a') s2)
    (Filter.inter_mem ((hLoc s1 hs1).1.mem_nhds (zero_mem _)) ((hLoc s2 hs2).1.mem_nhds (zero_mem _)))
  set L := latt (GlobalTheory.LatVac.psiAt B.ψ v) a (a + a') s with hLdef
  obtain ⟨Fa, hFa⟩ := GlobalTheory.T.exists_finset_eq_sum_addCosetIndicator L (hLoc s hs).1 (ι φ) (hmaps hφ) (fun Y C hC => hper1 Y C (hsub hC).1)
  obtain ⟨Fb, hFb⟩ := GlobalTheory.T.exists_finset_eq_sum_addCosetIndicator L (hLoc s hs).1 (ι φ₁) (hmaps hφ₁) (fun Y C hC => hper2 Y C (hsub hC).2)
  have hcm : ∀ y, cind L y ∈ SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) :=
    fun y => cind_mem (hLoc s hs).1 (hLoc s hs).2 y
  obtain ⟨x0, hx0, hιx0⟩ := hbij.surjOn (hcm 0)
  have hPD := ip_cosets μ (GlobalTheory.LatVac.psiAt B.ψ v) hψc ι hbij.injOn
    (fun C => schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C)) (fun l => schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l))
    (fun C f hf => ⟨hsb _ f hf, hT0 C f hf⟩) (fun l f hf => ⟨hsb _ f hf, hM0 l f hf⟩)
    (fun C => hU _) (fun l => hU _) s x0 hx0 hιx0
  have hιxs : ∀ y, ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT (-y)) x0) = cind L y := fun y => by
    rw [hT0 _ x0 hx0, hιx0]
    exact cind_translate L y
  have eA := expand μ ι hbij.injOn L (fun y => schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT (-y)) x0) (fun y => hsb _ x0 hx0) hιxs
    (ip μ x0 x0) hPD φ hφ (ι φ) rfl Fa hFa
  have eB := expand μ ι hbij.injOn L (fun y => schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT (-y)) x0) (fun y => hsb _ x0 hx0) hιxs
    (ip μ x0 x0) hPD φ₁ hφ₁ (ι φ₁) rfl Fb hFb
  have eA' := expand ν LinearMap.id (fun _ _ _ _ h => h) L (cind L) hcm (fun y => rfl)
    (ip ν (cind L 0) (cind L 0)) (ip_cind ν L) (ι φ) (hmaps hφ) (ι φ) rfl Fa hFa
  have eB' := expand ν LinearMap.id (fun _ _ _ _ h => h) L (cind L) hcm (fun y => rfl)
    (ip ν (cind L 0) (cind L 0)) (ip_cind ν L) (ι φ₁) (hmaps hφ₁) (ι φ₁) rfl Fb hFb
  have hipD : ip μ φ₁ φ₁ = ip μ φ φ := by
    rw [(ip_self μ hφ₁).1, (ip_self μ hφ).1, hnorm μ hμ]
  have hne : x0 ≠ 0 := fun h => by
    have e := congrFun hιx0 0
    rw [h, map_zero] at e
    simp [cind] at e
  have hc0 : ip μ x0 x0 ≠ 0 := by
    rw [(ip_self μ hx0).1]
    exact_mod_cast (ENNReal.toReal_pos (lintegral_ne_zero μ hx0 hne) (ip_self μ hx0).2).ne'
  rw [eA, eB] at hipD
  have hK := mul_right_cancel₀ hc0 hipD
  have hQ : ip ν (ι φ₁) (ι φ₁) = ip ν (ι φ) (ι φ) := by rw [eA', eB', hK]
  rw [(ip_self ν (hmaps hφ₁)).1, (ip_self ν (hmaps hφ)).1] at hQ
  have hR := Complex.ofReal_injective hQ
  exact (ENNReal.toReal_eq_toReal_iff' (ip_self ν (hmaps hφ₁)).2 (ip_self ν (hmaps hφ)).2).mp hR

end GlobalTheory.LinearModelL2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLinearWittModelNonvanishingStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_linear_witt_model_nonvanishing : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
    (∀ μ : @Measure (Fin a × Fin (a + a') → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ x, ‖φ₁ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∀ ν : @Measure (Matrix (Fin a) (Fin (a + a')) (Fv F v)) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖ι φ₁ Y‖ₑ ^ 2 ∂ν = ∫⁻ Y, ‖ι φ Y‖ₑ ^ 2 ∂ν := by
  first | exact @GlobalTheory.LinearModelL2.linIso_lintegral_eq | exact GlobalTheory.LinearModelL2.linIso_lintegral_eq | (intros; apply GlobalTheory.LinearModelL2.linIso_lintegral_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqRightTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqRightTranslate
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped NNReal ENNReal

namespace GlobalTheory.SplitFlip

theorem lintegral_mul_invT_sq : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}
    (Φ : Matrix (Fin a) (Fin d) k → ℂ) (h : GL (Fin d) k),
    ∀ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖Φ (Y * (GlobalTheory.SplitFlip.invT h).1)‖ₑ ^ 2 ∂ν =
        ‖GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h) (a : ℂ)‖ₑ * ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν := by
  intro k _ _ _ _ a d Φ h ν hν
  letI mk : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  letI mM : MeasurableSpace (Matrix (Fin a) (Fin d) k) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin d) k) := ⟨rfl⟩
  haveI := hν
  set M : Matrix (Fin d) (Fin d) k := (invT h).1 with hM
  set M' : Matrix (Fin d) (Fin d) k := ((invT h)⁻¹).1
  have hMM' : M * M' = 1 := Units.mul_inv _
  have hM'M : M' * M = 1 := Units.inv_mul _
  let L : Matrix (Fin a) (Fin d) k ≃ᵐ Matrix (Fin a) (Fin d) k :=
    { toFun := fun Y => Y * M
      invFun := fun Y => Y * M'
      left_inv := fun Y => by simp [Matrix.mul_assoc, hMM']
      right_inv := fun Y => by simp [Matrix.mul_assoc, hM'M]
      measurable_toFun := (continuous_id.matrix_mul continuous_const).measurable
      measurable_invFun := (continuous_id.matrix_mul continuous_const).measurable }
  let f0 : Matrix (Fin a) (Fin d) k → (Fin a × Fin d → k) := fun Y p => Y p.1 p.2
  have hEc : Continuous f0 := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
  let g0 : (Fin a × Fin d → k) → Matrix (Fin a) (Fin d) k := fun f => Matrix.of fun i j => f (i, j)
  have hEsc : Continuous g0 :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  let E : Matrix (Fin a) (Fin d) k ≃+ (Fin a × Fin d → k) :=
    { toFun := f0, invFun := g0, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl }
  let EM : Matrix (Fin a) (Fin d) k ≃ᵐ (Fin a × Fin d → k) :=
    { toFun := f0, invFun := g0, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      measurable_toFun := hEc.measurable, measurable_invFun := hEsc.measurable }
  haveI hμ : (ν.map E).IsAddHaarMeasure := E.isAddHaarMeasure_map ν hEc hEsc
  let K : Matrix (Fin a × Fin d) (Fin a × Fin d) k := Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin a) (Fin a) k) Mᵀ
  have hK : ∀ Y, K *ᵥ f0 Y = f0 (Y * M) := by
    intro Y; funext p
    simp [K, f0, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, Matrix.mul_apply, mul_comm]
  have hdetK : K.det = (((gdet h)⁻¹ ^ a : kˣ) : k) := by
    rw [Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul, Matrix.det_transpose, Fintype.card_fin, ← gdet_invT]
    simp [M, gdet]
  have hu : K.det ≠ 0 := by rw [hdetK]; exact Units.ne_zero _
  have hlam : (Measure.addHaar : Measure k).map (fun x => algebraMap k k K.det * x) =
      (distribHaarChar k (gdet h) ^ a) • (Measure.addHaar : Measure k) := by
    have h2 := GlobalTheory.CompanionTheory.SW.DetScale.char_smul_map (Measure.addHaar : Measure k) ((gdet h)⁻¹ ^ a)
    rw [Algebra.algebraMap_self, RingHom.id_apply, hdetK]
    have hcd : distribHaarChar k (gdet h) ^ a * distribHaarChar k ((gdet h)⁻¹ ^ a) = 1 := by
      rw [map_pow, map_inv, ← mul_pow, mul_inv_cancel₀ distribHaarChar_pos.ne', one_pow]
    calc (Measure.addHaar : Measure k).map (fun x => (((gdet h)⁻¹ ^ a : kˣ) : k) * x)
        = (distribHaarChar k (gdet h) ^ a * distribHaarChar k ((gdet h)⁻¹ ^ a)) •
            (Measure.addHaar : Measure k).map (fun x => (((gdet h)⁻¹ ^ a : kˣ) : k) * x) := by rw [hcd, one_smul]
      _ = _ := by rw [mul_smul, h2]
  have h1 := GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul k k (Fin a × Fin d) K hu Measure.addHaar inferInstance _ hlam
    (ν.map E) hμ
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h1
  have key : ν.map L = (distribHaarChar k (gdet h) ^ a) • ν := by
    apply EM.map_measurableEquiv_injective
    rw [Measure.map_map EM.measurable L.measurable, Measure.map_smul]
    have e1 : (EM ∘ L) = (fun x => K *ᵥ x) ∘ EM := by funext Y; exact (hK Y).symm
    rw [e1, ← Measure.map_map (GlobalTheory.CompanionTheory.SW.DetScale.measurable_mulVec K) EM.measurable]
    exact h1
    exact EM.measurable.aemeasurable
  have hl := lintegral_map_equiv (fun Y => ‖Φ Y‖ₑ ^ 2) L (μ := ν)
  rw [key] at hl
  refine hl.symm.trans ?_
  rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  congr 1
  simp only [apow, GlobalTheory.SplitWeil.nabs, Complex.cpow_natCast, enorm_pow]
  rw [ENNReal.coe_pow]; congr 1; rw [← ofReal_norm_eq_enorm]; simp

end GlobalTheory.SplitFlip
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqRightTranslateStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_norm_sq_right_translate : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}
    (Φ : Matrix (Fin a) (Fin d) k → ℂ) (h : GL (Fin d) k),
    ∀ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖Φ (Y * (GlobalTheory.SplitFlip.invT h).1)‖ₑ ^ 2 ∂ν =
        ‖GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h) (a : ℂ)‖ₑ * ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν := by
  first | exact @GlobalTheory.SplitFlip.lintegral_mul_invT_sq | exact GlobalTheory.SplitFlip.lintegral_mul_invT_sq | (intros; apply GlobalTheory.SplitFlip.lintegral_mul_invT_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationOneUnitsNhds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationOneUnitsNhds
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

open ValuativeRel

theorem units_valuation_eq_one_mem_nhds_one {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    {x : kˣ | ValuativeRel.valuation k (x : k) = 1} ∈ 𝓝 (1 : kˣ) := by
  have hset : {x : kˣ | ValuativeRel.valuation k (x : k) = 1} =
      (fun x : kˣ => (x : k)) ⁻¹' (𝒪[k] : Set k) ∩
        (fun x : kˣ => ((x⁻¹ : kˣ) : k)) ⁻¹' (𝒪[k] : Set k) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe,
      Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀]
    rw [inv_le_one₀ (by simp [zero_lt_iff])]
    exact le_antisymm_iff
  have hopen : IsOpen {x : kˣ | ValuativeRel.valuation k (x : k) = 1} := by
    rw [hset]
    exact ((Valuation.isOpen_integer (R := k)).preimage Units.continuous_val).inter
      ((Valuation.isOpen_integer (R := k)).preimage Units.continuous_coe_inv)
  exact hopen.mem_nhds (by simp)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationOneUnitsNhdsStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_one_units_nhds : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    {x : kˣ | ValuativeRel.valuation k (x : k) = 1} ∈ 𝓝 (1 : kˣ) := by
  first | exact @GlobalTheory.units_valuation_eq_one_mem_nhds_one | exact GlobalTheory.units_valuation_eq_one_mem_nhds_one | (intros; apply GlobalTheory.units_valuation_eq_one_mem_nhds_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqSchwartzPosFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqSchwartzPosFinite
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}
    (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ SB (Matrix (Fin a) (Fin d) k) → Φ ≠ 0 →
    ∀ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ 0 ∧ ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ ⊤ := by
  intro k _ _ _ _ a d Φ hΦ h0 ν hν
  letI : MeasurableSpace (Matrix (Fin a) (Fin d) k) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin d) k) := ⟨rfl⟩
  obtain ⟨hlc, hcs⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  have hc : Continuous Φ := hlc.continuous
  have hcont : Continuous fun Y => ‖Φ Y‖ₑ ^ 2 :=
    (ENNReal.continuous_pow 2).comp hc.enorm
  constructor
  · intro h
    rw [lintegral_eq_zero_iff hcont.measurable] at h
    have h' := (Continuous.ae_eq_iff_eq ν hcont continuous_zero).1 h
    apply h0
    funext Y
    have := congrFun h' Y
    simpa using this
  · obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
    have hle : ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≤
        ∫⁻ Y, (tsupport Φ).indicator (fun _ => ENNReal.ofReal C ^ 2) Y ∂ν := by
      refine lintegral_mono fun Y => ?_
      by_cases hY : Y ∈ tsupport Φ
      · rw [Set.indicator_of_mem hY]
        gcongr
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hC Y)
      · simp [image_eq_zero_of_notMem_tsupport hY]
    refine ne_top_of_le_ne_top ?_ hle
    rw [lintegral_indicator_const (isClosed_tsupport Φ).measurableSet]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (IsCompact.measure_lt_top hcs).ne

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqSchwartzPosFiniteStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_norm_sq_schwartz_pos_finite : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}
    (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ SB (Matrix (Fin a) (Fin d) k) → Φ ≠ 0 →
    ∀ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ 0 ∧ ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ ⊤ := by
  first | exact @GlobalTheory.schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top | exact GlobalTheory.schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top | (intros; apply GlobalTheory.schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalDeterminedByUnramified
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.WeilLinW

theorem one_mem_UAt' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (Y : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev := by
  intro u _
  simp [mat]

theorem charW_smooth_unitary : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → ∀ β₀ : (Fv F v)ˣ →* ℂˣ, (∀ h ∈ UAt σ G.W (evFin F v), ∃ h' : GL (Fin (a + a')) (Fv F v), (mat h).map (piW t) = h'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA 1 β₀ 1 h' (ι φ)) →
    GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hv t ι hι β₀ hβ
  have hloc := (GlobalTheory.T.theta_action_exists hP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1 v
  obtain ⟨φ₀, hφ₀, hιφ₀⟩ := hι.bij.surjOn (GlobalTheory.KSplit.indicator_intM_mem_SB (k := Fv F v) (R := Fin a) (D := Fin (a + a')))
  have h0 : ι φ₀ 0 ≠ 0 := by
    rw [hιφ₀]
    have : (0 : Matrix (Fin a) (Fin (a + a')) (Fv F v)) ∈ GlobalTheory.KSplit.intM (Fv F v) (Fin a) (Fin (a + a')) :=
      fun i j => by simp
    simp [Set.indicator_of_mem this]
  have omA_eq : ∀ (h' : GL (Fin (a + a')) (Fv F v)) (Φ : Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ) Y,
      GlobalTheory.SplitFlip.omA 1 β₀ 1 h' Φ Y = ((β₀ (GlobalTheory.SplitFlip.gdet h') : ℂ) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h') (-(a : ℂ) / 2)) * Φ (Y * (GlobalTheory.SplitFlip.invT h').1) := by
    intro h' Φ Y
    simp [GlobalTheory.SplitFlip.omA]
  have gdet_eq : ∀ (h : UA σ G.W.J) (h' : GL (Fin (a + a')) (Fv F v)), (mat h).map (piW t) = h'.1 →
      ((GlobalTheory.SplitFlip.gdet h' : (Fv F v)ˣ) : Fv F v) = ((mat h).map (piW t)).det := by
    intro h h' e
    rw [e]; rfl
  refine ⟨?_, ?_⟩
  · obtain ⟨U, hU, hUφ⟩ := hloc.2.2 φ₀ hφ₀
    have hUW : {h : UA σ G.W.J | ((1 : UA σ G.V.J), h) ∈ U} ∈ 𝓝 (1 : UA σ G.W.J) := by
      have hc : Continuous (fun h : UA σ G.W.J => ((1 : UA σ G.V.J), h)) := continuous_const.prodMk continuous_id
      exact hc.continuousAt.preimage_mem_nhds hU
    obtain ⟨V, hV, hVx⟩ := GlobalTheory.T.unitary_determinant_open_image F E σ B a a' G X om om' hTr v hv t _ hUW
    unfold GlobalTheory.SmGL.IsSmoothChar
    apply Subgroup.isOpen_of_mem_nhds (g := 1)
    filter_upwards [hV, GlobalTheory.T.valuation_one_units_nhds (k := Fv F v)] with x hx hxv
    obtain ⟨h, hh, hhU, hdet⟩ := hVx x hx
    obtain ⟨h', hh', hrel⟩ := hβ h hh
    have hA := hUφ (1, h) hhU (one_mem_UAt' σ G.V _) hh
    have e := congrFun (hrel φ₀ hφ₀ φ₀ hφ₀ hA) 0
    rw [omA_eq] at e
    have hg : GlobalTheory.SplitFlip.gdet h' = x := Units.ext ((gdet_eq h h' hh').trans hdet)
    rw [hg, Matrix.zero_mul, GlobalTheory.SplitFlip.apow_of_valuation_eq_one hxv, mul_one] at e
    have e2 : (β₀ x : ℂ) = 1 := by
      have := mul_right_cancel₀ h0 (e.symm.trans (one_mul _).symm)
      exact this
    show β₀ x = 1
    exact Units.ext e2
  · intro x
    have ha : 0 < a + a' := by have := hTr.geo.lt; omega
    let i0 : Fin (a + a') := ⟨0, ha⟩
    let D : (Fv F v)ˣ → Matrix (Fin (a + a')) (Fin (a + a')) (Fv F v) := fun y =>
      Matrix.diagonal (Function.update (1 : Fin (a + a') → Fv F v) i0 (y : Fv F v))
    have hD : ∀ y z : (Fv F v)ˣ, D y * D z = D (y * z) := by
      intro y z
      simp only [D, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases hi : i = i0
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    have hD1 : D 1 = 1 := by
      simp only [D]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      by_cases hi : i = i0
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    let h' : GL (Fin (a + a')) (Fv F v) :=
      ⟨D x, D x⁻¹, by rw [hD, mul_inv_cancel, hD1], by rw [hD, inv_mul_cancel, hD1]⟩
    have hg : GlobalTheory.SplitFlip.gdet h' = x := by
      apply Units.ext
      change (D x).det = (x : Fv F v)
      simp only [D, Matrix.det_diagonal]
      rw [Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp
    obtain ⟨h, hh, hht⟩ := GlobalTheory.T.local_unitary_group_surjects_general_linear_right hP F E σ B a a' G X om om' hTr v hv t h'
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc.1 1 (one_mem_UAt' σ G.V _) h hh φ₀ hφ₀
    obtain ⟨h'', hh'', hrel⟩ := hβ h hh
    have : h'' = h' := Units.ext (hh''.symm.trans hht)
    subst this
    have e := hrel φ₀ hφ₀ φ₁ hφ₁ hA
    obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_add_haar_matrix_space (k := Fv F v) (a := a) (d := a + a')
    have hu := GlobalTheory.T.triple_local_unitary_action_preserves hP F E σ B a a' G X om om' hTr v h hh φ₀ hφ₀ φ₁ hφ₁ hA
    have hl := GlobalTheory.T.triple_linear_witt_model_nonvanishing hP F E σ B a a' G X om om' hTr v hv t ι hι φ₀ hφ₀ φ₁ hφ₁ hu ν hν
    rw [e] at hl
    simp_rw [omA_eq, hg] at hl
    set c : ℂ := (β₀ x : ℂ) * GlobalTheory.SplitFlip.apow x (-(a : ℂ) / 2) with hcdef
    have hc : ∀ Y : Matrix (Fin a) (Fin (a + a')) (Fv F v), ‖c * ι φ₀ (Y * (GlobalTheory.SplitFlip.invT h').1)‖ₑ ^ 2 =
        ‖c‖ₑ ^ 2 * ‖ι φ₀ (Y * (GlobalTheory.SplitFlip.invT h').1)‖ₑ ^ 2 := by
      intro Y; rw [enorm_mul, mul_pow]
    simp_rw [hc] at hl
    rw [lintegral_const_mul' _ _ (by simp [enorm_eq_nnnorm]), GlobalTheory.T.lintegral_norm_sq_right_translate (ι φ₀) h' ν hν, hg] at hl
    obtain ⟨hn0, hntop⟩ := GlobalTheory.T.lintegral_norm_sq_schwartz_pos_finite (ι φ₀) (hι.bij.mapsTo hφ₀) (fun hz => h0 (by simp [hz])) ν hν
    rw [← mul_assoc] at hl
    have h1 : ‖c‖ₑ ^ 2 * ‖GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ = 1 :=
      (ENNReal.mul_left_inj hn0 hntop).mp (hl.trans (one_mul _).symm)
    clear_value c
    have h2 : ‖c‖ₑ ^ 2 * ‖GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ = ‖(β₀ x : ℂ)‖ₑ ^ 2 := by
      have : c * c * GlobalTheory.SplitFlip.apow x (a : ℂ) = (β₀ x : ℂ) * (β₀ x : ℂ) := by
        rw [hcdef]
        have e3 : GlobalTheory.SplitFlip.apow x (-(a : ℂ) / 2) * GlobalTheory.SplitFlip.apow x (-(a : ℂ) / 2) * GlobalTheory.SplitFlip.apow x (a : ℂ) = 1 := by
          rw [← GlobalTheory.SplitFlip.apow_add, ← GlobalTheory.SplitFlip.apow_add]
          have : -(a : ℂ) / 2 + -(a : ℂ) / 2 + a = 0 := by ring
          rw [this, GlobalTheory.SplitFlip.apow_zero]
        linear_combination ((β₀ x : ℂ) * (β₀ x : ℂ)) * e3
      calc ‖c‖ₑ ^ 2 * ‖GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ = ‖c * c * GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ := by
            rw [enorm_mul, enorm_mul]; ring
        _ = ‖(β₀ x : ℂ) * (β₀ x : ℂ)‖ₑ := by rw [this]
        _ = ‖(β₀ x : ℂ)‖ₑ ^ 2 := by rw [enorm_mul]; ring
    rw [h2] at h1
    have h3 : ‖(β₀ x : ℂ)‖₊ = 1 := by
      rw [enorm_eq_nnnorm, ← ENNReal.coe_pow, ENNReal.coe_eq_one] at h1
      exact (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 h1
    exact congrArg NNReal.toReal h3

end GlobalTheory.WeilLinW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalDeterminedByUnramifiedStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_weil_functional_determined_by_unramified : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → ∀ β₀ : (Fv F v)ˣ →* ℂˣ, (∀ h ∈ UAt σ G.W (evFin F v), ∃ h' : GL (Fin (a + a')) (Fv F v), (mat h).map (piW t) = h'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA 1 β₀ 1 h' (ι φ)) →
    GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ := by
  first | exact @GlobalTheory.WeilLinW.charW_smooth_unitary | exact GlobalTheory.WeilLinW.charW_smooth_unitary | (intros; apply GlobalTheory.WeilLinW.charW_smooth_unitary <;> assumption)
end
