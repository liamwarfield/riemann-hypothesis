module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarMeasureNonunitsNull
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.NonarchimedeanSelfdualMeasurePi
public import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV

theorem fibre_mass_eq {V R : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace R] [MeasurableSpace R]
    (μ : Measure V) (ν : Measure R) (q : V → R) (hq : Measurable q) (B : Set R) (fib : R → Measure V)
    (h : IsFibreFamily μ q id Set.univ ν B fib) {A : Set V} {S : Set R} (hA : MeasurableSet A)
    (hS : MeasurableSet S) : μ (A ∩ q ⁻¹' S) = ∫⁻ s in S, fib s A ∂ν := by
  obtain ⟨h1, h2, -⟩ := h
  have hT : MeasurableSet (A ∩ q ⁻¹' S) := hA.inter (hq hS)
  have e := h2 ((A ∩ q ⁻¹' S).indicator 1) (measurable_one.indicator hT)
  simp only [Measure.restrict_univ, lintegral_indicator_one hT] at e
  rw [e, ← lintegral_indicator hS]
  refine lintegral_congr fun b => ?_
  have hae : ∀ᵐ x ∂(fib b), q x = b := by
    refine measure_mono_null ?_ (h1 b)
    intro x hx hx'
    exact hx hx'.1
  by_cases hb : b ∈ S
  · rw [Set.indicator_of_mem hb]
    refine measure_congr ?_
    filter_upwards [hae] with x hx
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    show q x ∈ S
    rwa [hx]
  · rw [Set.indicator_of_notMem hb]
    refine measure_mono_null (t := {x | ¬ q x = b}) ?_ hae
    intro x hx hxb
    apply hb
    rw [← hxb]
    exact hx.2

theorem tendsto_mean {R : Type} [TopologicalSpace R] [MeasurableSpace R] (ν : Measure R) (G : R → ℝ≥0∞) (c : R)
    (hG : ContinuousAt (fun s => (G s).toReal) c) (hfin : ∀ᶠ s in nhds c, G s ≠ ⊤) (S : ℕ → Set R)
    (hS : ∀ k, MeasurableSet (S k)) (hl : Filter.Tendsto S Filter.atTop (nhds c).smallSets)
    (hpos : ∀ k, ν (S k) ≠ 0) (htop : ∀ k, ν (S k) ≠ ⊤) :
    Filter.Tendsto (fun k => (∫⁻ s in S k, G s ∂ν).toReal / (ν (S k)).toReal) Filter.atTop
      (nhds (G c).toReal) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hN : {s | G s ≠ ⊤ ∧ dist (G s).toReal (G c).toReal < ε / 2} ∈ nhds c :=
    Filter.inter_mem hfin (hG.eventually (Metric.ball_mem_nhds _ (half_pos hε)))
  have hev := hl.eventually (Filter.eventually_smallSets_subset.2 hN)
  filter_upwards [hev] with k hk
  set g := (G c).toReal with hg
  have hg0 : 0 ≤ g := ENNReal.toReal_nonneg
  set n := ν (S k) with hn
  have hnr : 0 < n.toReal := ENNReal.toReal_pos (hpos k) (htop k)
  have hup : ∫⁻ s in S k, G s ∂ν ≤ ENNReal.ofReal (g + ε / 2) * n := by
    rw [hn, ← setLIntegral_const]
    refine setLIntegral_mono' (hS k) fun s hs => ?_
    obtain ⟨h1, h2⟩ := hk hs
    rw [← ENNReal.ofReal_toReal h1]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (abs_lt.1 (Real.dist_eq _ _ ▸ h2)).2
    linarith
  have hlo : ENNReal.ofReal (g - ε / 2) * n ≤ ∫⁻ s in S k, G s ∂ν := by
    rw [hn, ← setLIntegral_const]
    refine setLIntegral_mono' (hS k) fun s hs => ?_
    obtain ⟨h1, h2⟩ := hk hs
    rw [← ENNReal.ofReal_toReal h1]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (abs_lt.1 (Real.dist_eq _ _ ▸ h2)).1
    linarith
  have hfinU : ENNReal.ofReal (g + ε / 2) * n ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (htop k)
  have hup' : (∫⁻ s in S k, G s ∂ν).toReal ≤ (g + ε / 2) * n.toReal := by
    have := ENNReal.toReal_mono hfinU hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hlo' : (g - ε / 2) * n.toReal ≤ (∫⁻ s in S k, G s ∂ν).toReal := by
    have := ENNReal.toReal_mono (ne_top_of_le_ne_top hfinU hup) hlo
    rw [ENNReal.toReal_mul] at this
    refine le_trans ?_ this
    refine mul_le_mul_of_nonneg_right ?_ hnr.le
    rw [ENNReal.toReal_ofReal']
    exact le_max_left _ _
  rw [Real.dist_eq, abs_lt]
  constructor
  · have : g - ε / 2 ≤ (∫⁻ s in S k, G s ∂ν).toReal / n.toReal := (le_div_iff₀ hnr).2 hlo'
    linarith
  · have : (∫⁻ s in S k, G s ∂ν).toReal / n.toReal ≤ g + ε / 2 := (div_le_iff₀ hnr).2 hup'
    linarith

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Topology

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec

open PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport

section Group

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem invariant_mem_nhds {f : V → ℂ} (h1 : IsLocallyConstant f) (h2 : HasCompactSupport f) :
    {u : V | ∀ x, f (x + u) = f x} ∈ 𝓝 (0 : V) := by
  have hg : IsLocallyConstant fun p : V × V => f (p.1 + p.2) - f p.1 :=
    (h1.comp_continuous (f := fun p : V × V => p.1 + p.2) (by fun_prop)).sub
      (h1.comp_continuous (f := fun p : V × V => p.1) (by fun_prop))
  have hn := hg.isOpen_fiber 0
  obtain ⟨u, v, _, hv, hCu, h0, huv⟩ := generalized_tube_lemma h2.isCompact
    (isCompact_singleton (x := (0 : V))) hn (by
      rintro ⟨c, x⟩ ⟨_, hx⟩
      have hx' : x = 0 := hx
      subst hx'
      simp)
  have hv0 : v ∈ 𝓝 (0 : V) := hv.mem_nhds (h0 rfl)
  have hv1 : (fun x : V => -x) ⁻¹' v ∈ 𝓝 (0 : V) := by
    have hc : ContinuousAt (fun x : V => -x) 0 := by fun_prop
    exact hc.preimage_mem_nhds (by simpa using hv0)
  refine Filter.mem_of_superset (Filter.inter_mem hv0 hv1) fun w hw x => ?_
  by_cases hx : x ∈ tsupport f
  · have := huv (Set.mk_mem_prod (hCu hx) hw.1)
    simpa [sub_eq_zero] using this
  · by_cases hx' : x + w ∈ tsupport f
    · have h : f (x + w + -w) - f (x + w) = 0 := huv (Set.mk_mem_prod (hCu hx') hw.2)
      rw [add_neg_cancel_right, sub_eq_zero] at h
      exact h.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem eq_sum_cosets {φ : V → ℂ} (hφ : HasCompactSupport φ) (L : AddSubgroup V) (hL : IsOpen (L : Set V))
    (hinv : ∀ x, ∀ l ∈ L, φ (x + l) = φ x) :
    ∃ s : Finset V, ∀ x, φ x = ∑ a ∈ s, φ a * Set.indicator {y | y - a ∈ L} (fun _ => (1 : ℂ)) x := by
  classical
  obtain ⟨t, ht⟩ := hφ.isCompact.elim_finite_subcover (fun a : V => {y | y - a ∈ L})
    (fun a => hL.preimage (continuous_id.sub continuous_const))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [L.zero_mem]⟩)
  let T : Finset (V ⧸ L) := t.image (QuotientAddGroup.mk : V → V ⧸ L)
  refine ⟨T.image Quotient.out, fun x => ?_⟩
  rw [Finset.sum_image (fun a _ b _ hab => Quotient.out_injective hab)]
  have key : ∀ q : V ⧸ L, x - q.out ∈ L ↔ q = (x : V ⧸ L) := by
    intro q
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
  have hval : φ ((x : V ⧸ L).out) = φ x := by
    have hm : x - ((x : V ⧸ L)).out ∈ L := (key _).2 rfl
    have := hinv ((x : V ⧸ L)).out _ hm
    rw [← this]
    congr 1
    abel
  have hterm : ∀ q : V ⧸ L, φ q.out * Set.indicator {y | y - q.out ∈ L} (fun _ => (1 : ℂ)) x
      = if q = (x : V ⧸ L) then φ x else 0 := by
    intro q
    by_cases hq : q = (x : V ⧸ L)
    · subst hq
      rw [if_pos rfl, Set.indicator_of_mem (show x ∈ {y | y - ((x : V ⧸ L)).out ∈ L} from (key _).2 rfl),
        hval, mul_one]
    · rw [if_neg hq, Set.indicator_of_notMem (show x ∉ {y | y - q.out ∈ L} from fun hx => hq ((key _).1 hx)),
        mul_zero]
  simp only [hterm, Finset.sum_ite_eq']
  split_ifs with hx
  · rfl
  · by_contra hne
    have hmem : x ∈ tsupport φ := subset_tsupport φ hne
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (ht hmem)
    apply hx
    refine Finset.mem_image.2 ⟨a, ha, ?_⟩
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
    exact hxa

end Group

theorem exists_nhds_of_pi {ι X : Type} [Finite ι] [TopologicalSpace X] {x : X} {U : Set (ι → X)}
    (hU : U ∈ 𝓝 (fun _ => x)) : ∃ W ∈ 𝓝 x, ∀ c : ι → X, (∀ i, c i ∈ W) → c ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hsub⟩ := hU
  exact ⟨⋂ i ∈ I, t i, (Filter.biInter_mem hI).2 fun i _ => ht i, fun c hc =>
    hsub fun i hi => Set.mem_iInter₂.1 (hc i) i hi⟩

variable {F : Type} [Field F] [NumberField F]

def intSub (v : HeightOneSpectrum (𝓞 F)) : OpenAddSubgroup (Fv F v) :=
  ⟨(v.adicCompletionIntegers F).toSubring.toAddSubgroup, ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v⟩

theorem mem_intSub (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) :
    x ∈ intSub v ↔ x ∈ v.adicCompletionIntegers F := Iff.rfl

theorem exists_box_subset {W : Set (Af F)} (hW : W ∈ 𝓝 (0 : Af F)) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F))) (P : ∀ v : HeightOneSpectrum (𝓞 F), OpenAddSubgroup (Fv F v)),
      (∀ v, P v ≤ intSub v) ∧ (∀ v, v ∉ T → P v = intSub v) ∧ {y : Af F | ∀ v, y v ∈ P v} ⊆ W := by
  classical
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hc : Continuous (RestrictedProduct.structureMap R A Filter.cofinite) :=
    RestrictedProduct.isEmbedding_structureMap.continuous
  have hp : (RestrictedProduct.structureMap R A Filter.cofinite) ⁻¹' W ∈ 𝓝 (fun v => (0 : A v)) :=
    hc.continuousAt.preimage_mem_nhds hW
  rw [nhds_pi, Filter.mem_pi] at hp
  obtain ⟨I, hI, t, ht, hsub⟩ := hp
  have hQ : ∀ v : HeightOneSpectrum (𝓞 F), ∃ Q : OpenAddSubgroup (Fv F v), Q ≤ intSub v ∧
      ∀ x : A v, (x : Fv F v) ∈ Q → x ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := mem_nhds_subtype _ _ _ |>.1 (ht v)
    have h0 : u ∩ (intSub v : Set (Fv F v)) ∈ 𝓝 (0 : Fv F v) :=
      Filter.inter_mem hu ((intSub v).isOpen.mem_nhds (intSub v).zero_mem)
    obtain ⟨Q, hQ⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h0
    exact ⟨Q, fun x hx => (hQ hx).2, fun x hx => hut (hQ hx).1⟩
  choose Q hQ1 hQ2 using hQ
  refine ⟨hI.toFinset, fun v => if v ∈ I then Q v else intSub v, ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ I
    · simpa [hv] using hQ1 v
    · simp [hv]
  · intro v hv
    have : v ∉ I := by simpa using hv
    simp [this]
  · intro y hy
    have hint : ∀ v, y v ∈ A v := by
      intro v
      by_cases hv : v ∈ I
      · have := hy v
        simp only [hv, if_true] at this
        exact hQ1 v this
      · have := hy v
        simp only [hv, if_false] at this
        exact this
    have : (fun v => (⟨y v, hint v⟩ : A v)) ∈ (RestrictedProduct.structureMap R A Filter.cofinite) ⁻¹' W := by
      refine hsub fun v hv => hQ2 v _ ?_
      have := hy v
      simp only [hv, if_true] at this
      exact this
    exact this

variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem crd_add {R : Type} [CommRing R] [Algebra F R] (x y : R ⊗[F] E) (k : Fin d) :
    crd b R (x + y) k = crd b R x k + crd b R y k := by
  simp [crd]

theorem crd_neg {R : Type} [CommRing R] [Algebra F R] (x : R ⊗[F] E) (k : Fin d) :
    crd b R (-x) k = - crd b R x k := by
  simp [crd]

theorem crd_zero {R : Type} [CommRing R] [Algebra F R] (k : Fin d) :
    crd b R (0 : R ⊗[F] E) k = 0 := by
  simp [crd]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

open Dec

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

section Abstract

variable {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]

theorem integral_indicator_char_of_trivial (μ : Measure G) (H : AddSubgroup G)
    (hH : MeasurableSet (H : Set G)) (χ : G → ℂ) (h1 : ∀ x ∈ H, χ x = 1) :
    ∫ x, (H : Set G).indicator χ x ∂μ = ((μ (H : Set G)).toReal : ℂ) := by
  rw [integral_indicator hH, setIntegral_congr_fun hH (g := fun _ => (1 : ℂ)) (fun x hx => h1 x hx)]
  simp [Measure.real]

theorem integral_indicator_char_of_ne (μ : Measure G) [μ.IsAddLeftInvariant] (H : AddSubgroup G)
    (χ : G → ℂ) (hχ : ∀ x y, χ (x + y) = χ x * χ y) {h : G} (hh : h ∈ H) (hne : χ h ≠ 1) :
    ∫ x, (H : Set G).indicator χ x ∂μ = 0 := by
  have key : ∀ x, (H : Set G).indicator χ (x + h) = (H : Set G).indicator χ x * χ h := by
    intro x
    by_cases hx : x ∈ H
    · have hxh : x + h ∈ H := H.add_mem hx hh
      rw [Set.indicator_of_mem (by exact hxh), Set.indicator_of_mem (by exact hx), hχ]
    · have hxh : x + h ∉ H := fun hc => hx (by simpa using H.sub_mem hc hh)
      rw [Set.indicator_of_notMem (by exact hxh), Set.indicator_of_notMem (by exact hx), zero_mul]
  have h2 := integral_add_right_eq_self (μ := μ) ((H : Set G).indicator χ) h
  simp only [key] at h2
  rw [integral_mul_const] at h2
  have h3 : (∫ x, (H : Set G).indicator χ x ∂μ) * (χ h - 1) = 0 := by
    rw [mul_sub, h2, mul_one, sub_self]
  exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hne)

end Abstract

variable {F : Type} [Field F] [NumberField F]

def psiF (ψ : AddChar (AF F) ℂ) (y : Af F) : ℂ := ψ (pairA F 0 y)

def annV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (U : Set (Fv F v)) : Set (Fv F v) :=
  {t | ∀ s ∈ U, psiV F ψ v (s * t) = 1}

def annF (ψ : AddChar (AF F) ℂ) (B : Set (Af F)) : Set (Af F) :=
  {b | ∀ y ∈ B, psiF ψ (y * b) = 1}

def fouInf (ψ : AddChar (AF F) ℂ) (lam : Measure (Ainf F)) (ρ : Ainf F → ℝ) (t : Ainf F) : ℂ :=
  ∫ x, (ρ x : ℂ) * psiInf F ψ (x * t) ∂lam

theorem psiF_add (ψ : AddChar (AF F) ℂ) (x y : Af F) : psiF ψ (x + y) = psiF ψ x * psiF ψ y := by
  have h : pairA F 0 (x + y) = pairA F 0 x + pairA F 0 y := Prod.ext (add_zero (0 : Ainf F)).symm rfl
  rw [psiF, h, AddChar.map_add_eq_mul]
  rfl

theorem psiF_zero (ψ : AddChar (AF F) ℂ) : psiF ψ 0 = 1 := by
  have h : pairA F 0 (0 : Af F) = 0 := rfl
  rw [psiF, h, AddChar.map_zero_eq_one]

theorem psiF_singleV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) :
    psiF ψ (singleV F v s) = psiV F ψ v s := rfl

theorem psi_pairA (ψ : AddChar (AF F) ℂ) (x : Ainf F) (y : Af F) :
    ψ (pairA F x y) = psiInf F ψ x * psiF ψ y := by
  have h : pairA F x y = pairA F x 0 + pairA F 0 y :=
    Prod.ext (add_zero x).symm (zero_add y).symm
  rw [h, AddChar.map_add_eq_mul]
  rfl

theorem psiV_zero (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : psiV F ψ v 0 = 1 := by
  classical
  have h : singleV F v (0 : Fv F v) = 0 := RestrictedProduct.single_zero _ v
  rw [← psiF_singleV, h, psiF_zero]

theorem psiV_add (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    psiV F ψ v (x + y) = psiV F ψ v x * psiV F ψ v y :=
  GlobalTheory.CompanionTheory.SW.PiV.psiV_add ψ v x y

theorem psiV_neg_of_eq_one (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) {x : Fv F v}
    (hx : psiV F ψ v x = 1) : psiV F ψ v (-x) = 1 := by
  have h := psiV_add ψ v (-x) x
  rw [neg_add_cancel, psiV_zero, hx, mul_one] at h
  exact h.symm

def annS (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (U : Set (Fv F v)) :
    AddSubgroup (Fv F v) where
  carrier := annV ψ v U
  add_mem' := by
    intro a b ha hb s hs
    rw [mul_add, psiV_add, ha s hs, hb s hs, one_mul]
  zero_mem' := by
    intro s _
    rw [mul_zero, psiV_zero]
  neg_mem' := by
    intro a ha s hs
    rw [mul_neg]
    exact psiV_neg_of_eq_one ψ v (ha s hs)

theorem coe_annS (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (U : Set (Fv F v)) :
    (annS ψ v U : Set (Fv F v)) = annV ψ v U := rfl

def boxS (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fv F v)) :
    AddSubgroup (Af F) where
  carrier := Coef.boxA S fun v => (U v : Set (Fv F v))
  add_mem' := by
    intro a b ha hb
    exact ⟨fun v hv => (U v).add_mem (ha.1 v hv) (hb.1 v hv),
      fun v hv => add_mem (ha.2 v hv) (hb.2 v hv)⟩
  zero_mem' := ⟨fun v _ => (U v).zero_mem, fun v _ => zero_mem _⟩
  neg_mem' := by
    intro a ha
    exact ⟨fun v hv => (U v).neg_mem (ha.1 v hv),
      fun v hv => neg_mem (ha.2 v hv)⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.EulerFactorStandardMeasureIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.EulerFactorStandardMeasureIdentity
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct

private theorem abs_finset_prod_sub_one_le {κ : Type} (f : κ → ℝ) (s : Finset κ) :
    |(∏ v ∈ s, f v) - 1| ≤ (∏ v ∈ s, (1 + |f v - 1|)) - 1 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : |f a| ≤ 1 + |f a - 1| := by
      have := abs_sub_abs_le_abs_sub (f a) 1
      rw [abs_one] at this
      linarith
    have hfa : f a * (∏ v ∈ s, f v) - 1 = f a * ((∏ v ∈ s, f v) - 1) + (f a - 1) := by ring
    rw [hfa]
    calc |f a * ((∏ v ∈ s, f v) - 1) + (f a - 1)|
        ≤ |f a| * |(∏ v ∈ s, f v) - 1| + |f a - 1| := by
          rw [← abs_mul]
          exact abs_add_le _ _
      _ ≤ (1 + |f a - 1|) * ((∏ v ∈ s, (1 + |f v - 1|)) - 1) + |f a - 1| := by
          gcongr
      _ = (1 + |f a - 1|) * (∏ v ∈ s, (1 + |f v - 1|)) - 1 := by ring

theorem abs_tprod_sub_one_le {κ : Type} (f : κ → ℝ)
    (hs : Summable (fun v => |f v - 1|)) :
    |(∏' v, f v) - 1| ≤ Real.exp (∑' v, |f v - 1|) - 1 := by
  have hm : Multipliable f := by
    have h := multipliable_one_add_of_summable (f := fun v => f v - 1)
      (by simpa only [Real.norm_eq_abs] using hs)
    simpa only [add_sub_cancel] using h
  have ht : Filter.Tendsto (fun s : Finset κ => ∏ v ∈ s, f v) Filter.atTop
      (nhds (∏' v, f v)) := hm.hasProd
  have hb : ∀ s : Finset κ, |(∏ v ∈ s, f v) - 1| ≤ Real.exp (∑' v, |f v - 1|) - 1 := by
    intro s
    refine (abs_finset_prod_sub_one_le f s).trans ?_
    gcongr ?_ - 1
    calc ∏ v ∈ s, (1 + |f v - 1|) ≤ ∏ v ∈ s, Real.exp (|f v - 1|) := by
          apply Finset.prod_le_prod₀
          · intro i _
            positivity
          · intro i _
            have := Real.add_one_le_exp (|f i - 1|)
            linarith
      _ = Real.exp (∑ v ∈ s, |f v - 1|) := (Real.exp_sum s _).symm
      _ ≤ Real.exp (∑' v, |f v - 1|) :=
          Real.exp_le_exp.mpr (hs.sum_le_tsum s (fun i _ => abs_nonneg _))
  exact le_of_tendsto' ((continuous_abs.tendsto _).comp (ht.sub_const 1)) hb

theorem tendsto_tprod_compl_one {ι : Type} (f : ι → ℝ)
    (hs : Summable (fun v => |f v - 1|)) :
    Filter.Tendsto (fun S : Finset ι => ∏' v : {v // v ∉ S}, f v) Filter.atTop (nhds 1) := by
  have hb : ∀ S : Finset ι, ‖(∏' v : {v // v ∉ S}, f v) - 1‖ ≤
      Real.exp (∑' v : {v // v ∉ S}, |f v - 1|) - 1 := by
    intro S
    rw [Real.norm_eq_abs]
    exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.abs_tprod_sub_one_le (fun v : {v // v ∉ S} => f v) (hs.subtype _)
  have hlim : Filter.Tendsto (fun S : Finset ι => Real.exp (∑' v : {v // v ∉ S}, |f v - 1|) - 1)
      Filter.atTop (nhds 0) := by
    have h := ((Real.continuous_exp.tendsto 0).comp
      (tendsto_tsum_compl_atTop_zero (fun v => |f v - 1|))).sub_const 1
    simpa [Function.comp_def, Real.exp_zero] using h
  have h0 := squeeze_zero_norm hb hlim
  simpa using h0.add_const 1

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.EulerFactorStandardMeasureIdentityStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_tail_infinite_product_one : ∀ {ι : Type} (f : ι → ℝ), Summable (fun v => |f v - 1|) → Filter.Tendsto (fun S : Finset ι => ∏' v : {v // v ∉ S}, f v) Filter.atTop (nhds 1) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MeasurableSetIntF
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

theorem placesCountable (F : Type) [Field F] [NumberField F] : Countable (HeightOneSpectrum (𝓞 F)) := by
  have : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  have : Countable (𝓞 F) := inferInstanceAs (Countable {x : F // x ∈ integralClosure ℤ F})
  have hs : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
    exact ⟨s, hs⟩
  have : Countable (Ideal (𝓞 F)) := hs.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v w h => HeightOneSpectrum.ext h)

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.Imports
namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity :=
  CompanionTheory.FamInh.globalArtin

end GlobalTheory.CompanionTheory.Hypotheses₂
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIntegrableOfIsSchwartzBruhat
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiInt

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.FouCoord GroundTheory.Automorphic.GJMatrix
open scoped NNReal

theorem continuous_integrable_of_isSchwartzBruhat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ, IsSchwartzBruhat Φ → Continuous Φ ∧ Integrable Φ dx := by
  intro F E _ _ _ _ _ σ hCM M dx hdx Φ hΦ
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  obtain ⟨h1, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI := hBor 1 M
  have hf := (isSchwartzBruhat_iff b Φ).1 hΦ
  let e := crd (AF F) b M
  have hcomp : (Φ ∘ e.symm) ∘ e = Φ := by
    funext X
    simp
  have hcont : Continuous Φ := by
    have h : Continuous ((Φ ∘ e.symm) ∘ e) :=
      (continuous_of_mem_schwartzBruhatPi hf).comp e.continuous
    rwa [hcomp] at h
  refine ⟨hcont, ?_⟩
  haveI : LocallyCompactSpace (Fin 1 → Fin M → AF F ⊗[F] E) :=
    e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Fin 1 → Fin M → AF F ⊗[F] E) :=
    e.toHomeomorph.secondCountableTopology
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, dx = c • mu0 e := ⟨_, Measure.isAddLeftInvariant_eq_smul dx (mu0 e)⟩
  have hI : Integrable Φ (mu0 e) := by
    rw [mu0, (measurableEmbedding_symm e).integrable_map_iff]
    exact integrable_of_mem_schwartzBruhatPi hf
  rw [hc]
  exact hI.smul_measure_nnreal

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiInt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MeasurableProjInf
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler

open GlobalTheory.CompanionTheory.SW

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem measurable_projInf [Module.Finite F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    Measurable (HeckeCharacterZeroLocus.SiegelWeilU.projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) := by
  have e := TopK.coordHomeo (E := E) (AF F) b
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have hc : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) :=
    MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) MeasProj.continuous_fstA
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_
  exact (((continuous_apply i).comp (continuous_apply a)).comp hc).measurable

theorem measurable_projV [Module.Finite F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) :
    Measurable (fun X : Fin n → Fin M → AF F ⊗[F] E =>
      HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X)) := by
  have e := TopK.coordHomeo (E := E) (AF F) b
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have h1 : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projFin : (Fin n → Fin M → AF F ⊗[F] E) → _) :=
    MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) MeasProj.continuous_sndA
  have h2 : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projV v : (Fin n → Fin M → Af F ⊗[F] E) → _) :=
    MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.evalV F v) (MeasProj.continuous_evalV v)
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_
  exact (((continuous_apply i).comp (continuous_apply a)).comp (h2.comp h1)).measurable

theorem measurableSet_box [Module.Finite F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, MeasurableSet (A v)) (hS : ∀ v, v ∉ S → A v = HeckeCharacterZeroLocus.SiegelWeilU.latV b v) :
    MeasurableSet {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} := by
  have e := TopK.coordHomeo (E := E) (AF F) b
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  rw [EulerBox.box_eq b S A hS]
  exact (MeasProj.isOpen_intOff b S).measurableSet.inter
    (Finset.measurableSet_biInter S fun v _ => measurable_projV b n M v (hA v))

end SlopeTestRemainingChoices

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoordinateMeasureScalingTensor
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoordinateMeasureScalingTensor
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.HaarScale

theorem unit_mul_map_haar : ∀ (F : Type) [Field F] [NumberField F] (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → ∀ (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → lam.map (fun y => t * y) = (∏ w, ‖e t w‖₊)⁻¹ • lam := by
  intro F _ _ e he lam hlam t ht
  classical
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hc : Continuous e := he.continuous
  let h : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph e
  have hcs : Continuous e.symm := by
    have : (e.symm : (InfinitePlace F → ℝ) → Ainf F) = h.symm := by
      funext y
      have h1 : e (h.symm y) = y := h.apply_symm_apply y
      exact e.symm_apply_eq.2 h1.symm
    rw [this]; exact h.symm.continuous
  have hm : Measurable e := hc.measurable
  have hms : Measurable e.symm := hcs.measurable
  have hmul : Measurable (fun y : Ainf F => t * y) := by
    have : (fun y : Ainf F => t * y) = fun y => e.symm (e t * e y) := by
      funext y; simp
    rw [this]
    exact hcs.measurable.comp (hm.const_mul _)
  obtain ⟨D, hD⟩ : ∃ D : InfinitePlace F → ℝ, D = e t := ⟨_, rfl⟩
  have hDu : IsUnit D := hD ▸ ht.map e
  have hD0 : ∀ w, D w ≠ 0 := fun w => by
    obtain ⟨u, hu⟩ := hDu
    have h1 : D w * (u⁻¹ : (InfinitePlace F → ℝ)ˣ).1 w = 1 := by
      have := congrFun (u.mul_inv) w
      rw [hu] at this
      simpa using this
    exact left_ne_zero_of_mul_eq_one h1
  haveI hμ : (lam.map e).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map lam e.toAddEquiv hc hcs
  let L : (InfinitePlace F → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ) := Matrix.toLin' (Matrix.diagonal D)
  have hL : ∀ x, L x = D * x := fun x => by
    funext w
    simp [L, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  have hdet : LinearMap.det L = ∏ w, D w := by
    simp [L, LinearMap.det_toLin', Matrix.det_diagonal]
  have hdet0 : LinearMap.det L ≠ 0 := by
    rw [hdet]; exact Finset.prod_ne_zero_iff.2 fun w _ => hD0 w
  have hscale := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := lam.map e) hdet0
  have hconst : ENNReal.ofReal |(LinearMap.det L)⁻¹| = (((∏ w, ‖e t w‖₊)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    have : |(LinearMap.det L)⁻¹| = (((∏ w, ‖e t w‖₊)⁻¹ : ℝ≥0) : ℝ) := by
      rw [hdet, abs_inv, Finset.abs_prod]
      push_cast
      simp [hD]
    rw [this, ENNReal.ofReal_coe_nnreal]
  have key : (lam.map (fun y => t * y)).map e = (∏ w, ‖e t w‖₊)⁻¹ • lam.map e := by
    rw [Measure.map_map hm hmul, ENNReal.smul_def, ← hconst, ← hscale,
      Measure.map_map L.continuous_of_finiteDimensional.measurable hm]
    congr 1
    funext y
    simp [hL, hD]
  have back : ∀ ν : Measure (Ainf F), (ν.map e).map e.symm = ν := fun ν => by
    rw [Measure.map_map hms hm]
    have : (e.symm ∘ e : Ainf F → Ainf F) = id := by funext y; simp
    rw [this, Measure.map_id]
  rw [← back (lam.map fun y => t * y), key, Measure.map_smul, back]
  exact hms.aemeasurable

end GlobalTheory.CompanionTheory.HaarScale
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoordinateMeasureScalingTensorStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_haar_scaling_norm : ∀ (F : Type) [Field F] [NumberField F] (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → ∀ (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → lam.map (fun y => t * y) = (∏ w, ‖e t w‖₊)⁻¹ • lam := by
  first | exact @GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar | exact GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar | (intros; apply GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianMeasureScalingTransform
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianMeasureScalingTransform
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Dil

section U
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

def mulPiU (ι : Type) (u : Rˣ) : (ι → R) ≃ᵐ (ι → R) :=
  MeasurableEquiv.piCongrRight fun _ =>
    { toEquiv := Units.mulLeft u
      measurable_toFun := (continuous_const.mul continuous_id).measurable
      measurable_invFun := (continuous_const.mul continuous_id).measurable }

theorem mulPiU_apply (ι : Type) (u : Rˣ) (x : ι → R) (i : ι) :
    mulPiU R ι u x i = (u : R) * x i := rfl

theorem map_mulPiU {ι : Type} [Fintype ι] (lam : Measure R) [SigmaFinite lam] (u : Rˣ) (c : ℝ≥0)
    (h : lam.map (fun y => (u : R) * y) = c • lam) :
    (Measure.pi fun _ : ι => lam).map (mulPiU R ι u) =
      (c ^ Fintype.card ι) • Measure.pi fun _ : ι => lam :=
  pi_map_scale lam (fun y => (u : R) * y) (continuous_const.mul continuous_id).measurable c h

theorem coordK_map_unit (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) [SigmaFinite lam] (u : Rˣ) (c : ℝ≥0)
    (h : lam.map (fun y => (u : R) * y) = c • lam) :
    (GlobalTheory.CompanionTheory.SW.coordK R b lam).map (fun y => algebraMap R (R ⊗[F] E) (u : R) * y) =
      (c ^ d) • GlobalTheory.CompanionTheory.SW.coordK R b lam := by
  obtain ⟨hr, -, -, -, -, -, hh, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hb := hh d b
  have hemb : MeasurableEmbedding (fun (y : R ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis R b).repr y k) :=
    hb.homeomorph.toMeasurableEquiv.measurableEmbedding
  have := map_mulPiU (ι := Fin d) R lam u c h
  rw [Fintype.card_fin] at this
  refine map_comap_scale _ _ _ ?_ (mulPiU R (Fin d) u) _ hb.surjective hb.injective
    (fun s hs => (hemb.measurableSet_image' hs).nullMeasurableSet) ?_ this
  · exact (continuous_const.mul continuous_id).measurable
  · intro y
    funext k
    rw [mulPiU_apply, ← Algebra.smul_def, map_smul]
    rfl

end U

theorem coordW_map_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → ∀ c : ℝ≥0, lam.map (fun y => t * y) = c • lam → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M).map (fun X p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i) = (c ^ (d * M)) • GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M := by
  intro F E _ _ _ _ _ σ hσ M d b lam hlam t ht c h
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Ainf F) d b lam hlam
  haveI := hK
  obtain ⟨u, rfl⟩ := ht
  set f : Ainf F ⊗[F] E → Ainf F ⊗[F] E := fun y => algebraMap (Ainf F) (Ainf F ⊗[F] E) (u : Ainf F) * y with hf
  have hfm : Measurable f := (continuous_const.mul continuous_id).measurable
  have hk := coordK_map_unit (Ainf F) σ hσ b lam u c h
  have hk1 := pi_map_scale (ι := Fin M) (GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) f hfm _ hk
  have hk2 := pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam)
    (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1
  simp only [Fintype.card_fin, pow_one, ← pow_mul] at hk2
  exact hk2

end GlobalTheory.CompanionTheory.SW.Dil
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianMeasureScalingTransformStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinate_measure_scaling_tensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → ∀ c : ℝ≥0, lam.map (fun y => t * y) = c • lam → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M).map (fun X p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i) = (c ^ (d * M)) • GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M := by
  first | exact @GlobalTheory.CompanionTheory.SW.Dil.coordW_map_unit | exact GlobalTheory.CompanionTheory.SW.Dil.coordW_map_unit | (intros; apply GlobalTheory.CompanionTheory.SW.Dil.coordW_map_unit <;> assumption)
end
end
