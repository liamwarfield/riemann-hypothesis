module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramFibreMeasureFreeTupleNeZeroFinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairInvolutionContinuous

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal

open Set

section Gen

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}

theorem fib_lt_top (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U) (b : X)
    {K : Set V} (hK : IsCompact K) (hKU : K ⊆ U) : fib b K < ⊤ := by
  obtain ⟨g, hg1, hgc, hgs, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  have hI := (h.2.2 g g.continuous hgc hgs).1 b (mem_univ b)
  calc fib b K = ∫⁻ v, K.indicator 1 v ∂(fib b) := (lintegral_indicator_one hK.measurableSet).symm
    _ ≤ ∫⁻ v, ENNReal.ofReal (g v) ∂(fib b) := lintegral_mono fun v => by
        by_cases hv : v ∈ K
        · simp [indicator_of_mem hv, hg1 hv]
        · simp [indicator_of_notMem hv]
    _ < ⊤ := hI.lintegral_lt_top

theorem sigmaFinite_fib (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U)
    (b : X) : SigmaFinite (fib b) := by
  have hc : fib b Uᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 inter_subset_right) (h.1 b)
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  have hσ : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance
  obtain ⟨K, hKc, hKU⟩ := hσ
  have hsub : ∀ n, K n ⊆ U := fun n => hKU ▸ subset_iUnion K n
  refine Measure.FiniteSpanningSetsIn.sigmaFinite
    (μ := fib b) (C := univ)
    { set := fun n => K n ∪ Uᶜ, set_mem := fun _ => mem_univ _, finite := fun n => ?_, spanning := ?_ }
  · exact (measure_union_le _ _).trans_lt
      (ENNReal.add_lt_top.2 ⟨fib_lt_top h hU b (hKc n) (hsub n), by simp [hc]⟩)
  · refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ U
    · rw [← hKU] at hx
      obtain ⟨n, hn⟩ := mem_iUnion.1 hx
      exact mem_iUnion.2 ⟨n, Or.inl hn⟩
    · exact mem_iUnion.2 ⟨0, Or.inr hx⟩

end Gen

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem gramR_ratTup_eq (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → E) :
    gramR R σ J (ratTup (F := F) R X) = (gramE σ J X).map (inclR R) := by
  ext i j
  simp [gramR, gramE, hE, hR, hform, ratTup, JR, sigR, inclR, Matrix.map_apply, mul_assoc]

theorem ratTup_free (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (X : Fin 1 → Fin M → E)
    (hX : LinearIndependent E X) : LinearIndependent (R ⊗[F] E) (ratTup (F := F) R X) := by
  have h0 : X 0 ≠ 0 := hX.ne_zero 0
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h0
  have hu : IsUnit (inclR (F := F) R (X 0 i)) := (isUnit_iff_ne_zero.2 hi).map _
  refine Fintype.linearIndependent_iff.2 fun g hg k => ?_
  have hk : k = 0 := Subsingleton.elim _ _
  subst hk
  have h1 := congrFun hg i
  simp only [Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ratTup] at h1
  exact (hu.mul_left_eq_zero).1 h1

end Rat

section Arch

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem arch_lb (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E))
    (ν : Measure (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a)) (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    (x : Fin a → Fin M → Ainf F ⊗[F] E) (S0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a)
    (hx : LinearIndependent (Ainf F ⊗[F] E) x)
    (hxS : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramR (Ainf F) σ J x = (S0 : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)))
    (W : Set (Fin a → Fin M → Ainf F ⊗[F] E)) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ 𝓝 S0, ∀ S ⊆ N, MeasurableSet S →
      c * ν S ≤ μ ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W) := by
  obtain ⟨n, m, eV, eH, f', hV, hH, hf', hG, hsurj⟩ :=
    GlobalTheory.ArchGramFibre.exists_submersion_coords F E σ hCM M a J hJ
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a) := ⟨rfl⟩
  have : ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E) := ⟨by
    have e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) =>
        p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2) := by
      funext p; rw [← hV, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have : ContinuousAdd (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a) := ⟨by
    have e : (fun p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a => p.1 + p.2) =
        fun p => eH.symm (eH p.1 + eH p.2) := by
      funext p; rw [← hH, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have hμ' : (μ.map eV).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μ (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective
      (eV.map_cocompact).le
  have hν' : (ν.map eH).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map ν (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective
      (eH.map_cocompact).le
  have hW' : IsOpen (eV.symm ⁻¹' W) := hW.preimage eV.symm.continuous
  have hx0W : eV x ∈ eV.symm ⁻¹' W := by
    show eV.symm (eV x) ∈ W
    rw [Homeomorph.symm_apply_apply]
    exact hxW
  obtain ⟨c, hc0, hct, N', hN', hlb'⟩ :=
    PI.VolStabS.submLB_holds n m _ _ hμ' hν' f' hf' (eV x) (hsurj x hx) _ hW' hx0W
  have hfx0 : f' (eV x) = eH S0 := by
    have h1 : eH.symm (f' (eV x)) = S0 := Subtype.ext ((hG x).trans hxS)
    rw [← h1, Homeomorph.apply_symm_apply]
  have hN : eH ⁻¹' N' ∈ 𝓝 S0 := eH.continuous.continuousAt.preimage_mem_nhds (hfx0 ▸ hN')
  refine ⟨c, hc0, hct, _, hN, fun S hSN hSm => ?_⟩
  have hS'm : MeasurableSet (eH.symm ⁻¹' S) := eH.symm.continuous.measurable hSm
  have hS'N : eH.symm ⁻¹' S ⊆ N' := fun z hz => by
    have := hSN hz
    rwa [mem_preimage, Homeomorph.apply_symm_apply] at this
  have h := hlb' _ hS'N hS'm
  rw [show (ν.map eH) = ν.map eH.toMeasurableEquiv from rfl,
    show (μ.map eV) = μ.map eV.toMeasurableEquiv from rfl,
    MeasurableEquiv.map_apply, MeasurableEquiv.map_apply] at h
  have e1 : eH.toMeasurableEquiv ⁻¹' (eH.symm ⁻¹' S) = S := by
    ext z
    simp
  have e2 : eV.toMeasurableEquiv ⁻¹' (f' ⁻¹' (eH.symm ⁻¹' S) ∩ eV.symm ⁻¹' W) =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W := by
    ext X
    simp only [mem_preimage, mem_inter_iff, Homeomorph.toMeasurableEquiv_coe,
      Homeomorph.symm_apply_apply, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨_, h1, hG X⟩, h2⟩
    · rintro ⟨⟨s, hs, hsX⟩, h2⟩
      refine ⟨?_, h2⟩
      have : s = eH.symm (f' (eV X)) := Subtype.ext (hsX.trans (hG X).symm)
      rw [← this]
      exact hs
  rw [e1, e2] at h
  exact h

end Arch

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigmaFinite_free (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hR : IsLocR R) (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (hm : IsGramFibFree R σ J n μ ν m)
    (S : HermR R σ n) : SigmaFinite (m S) := by
  have hO := GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hCM R hR n M
  obtain ⟨h1, h2, h3, h4, -⟩ := hR
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 n M
  exact sigmaFinite_fib hm hO S

theorem free_fibre_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFibFree (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → SigmaFinite (minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) ∧ (∀ v, SigmaFinite (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))) ∧ ((framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)).Nonempty → minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0 ∧ ∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0) := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ h₀ d b laminf lam hinf hlam minf hminf m hm
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  refine ⟨sigmaFinite_free σ hCM J (Ainf F) hLi 1 _ _ minf hminf _,
    fun v => sigmaFinite_free σ hCM J (Fv F v) (hLv v) 1 _ _ (m v) (hm v) _, ?_⟩
  rintro ⟨X₀, hX₀, hg⟩
  have hgram : ∀ (R : Type) [CommRing R] [Algebra F R],
      gramR R σ J (ratTup (F := F) R X₀) = (hermOf R σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ :
        Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := fun R _ _ => by
    rw [gramR_ratTup_eq, hg]
    rfl
  constructor
  · obtain ⟨h1, h2, h3, h4, hA, hRed, hU, -⟩ := hLi
    haveI := h1
    haveI := h2
    haveI := h3
    haveI := h4
    haveI := hA
    haveI := hRed
    haveI : FiniteDimensional F E := Module.Finite.of_basis b
    have hUo : IsOpen {r : Ainf F | IsUnit r} := by
      have := hU.isOpen_range
      convert this using 1
      ext r
      simp [IsUnit]
    have hH := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Ainf F) d b laminf hinf.1
    haveI := hH.2.1 1 M
    let ν' : Measure (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ 1) := coordHerm (Ainf F) σ b laminf 1
    haveI : ν'.IsAddHaarMeasure := hH.2.2 1
    exact (GlobalTheory.LocalFibreNonzero.fib_tens σ (PI.VolStabS.sigma_invol σ hCM.2.2.2) J hJ.1 1 (Ainf F)
      hUo (GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.lip_of_artinian_reduced (Ainf F)) _ ν' minf hminf
      (ratTup (F := F) (Ainf F) X₀) _ (ratTup_free (Ainf F) X₀ hX₀)
      (fun W hW hxW => arch_lb F E σ hCM M 1 J hJ _ _ (hH.2.1 1 M) (hH.2.2 1) _ _
        (ratTup_free (Ainf F) X₀ hX₀) (hgram (Ainf F)) W hW hxW)).1
  · intro v
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    haveI := h1
    haveI := h2
    haveI := h3
    haveI := h4
    have hH := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    exact (GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite F E σ hCM M J hJ v 1 _ _ (hH.2.1 1 M) (hH.2.2 1)
      (m v) (hm v) (ratTup (F := F) (Fv F v) X₀) _ (ratTup_free (Fv F v) X₀ hX₀) (hgram (Fv F v))).1

end Main

end GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneProductStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_volume_rank_one_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFibFree (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → SigmaFinite (minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) ∧ (∀ v, SigmaFinite (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))) ∧ ((framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)).Nonempty → minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0 ∧ ∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.free_fibre_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.free_fibre_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.free_fibre_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepMetricSmooth
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

open scoped ContDiff Topology

namespace GlobalTheory.CompanionTheory.MPDict.SmoothRep

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def rt (c : ∀ k, Bk n k) (q : Σ k, Bk n k) : Γ(MP ℤ m n, mchart c) :=
  resG _ (mchart_le c q.1) (pullRatio (prB n q.1) _ (c q.1) le_rfl q.2)

def rtOn (c : ∀ k, Bk n k) (W : (MP ℤ m n).Opens) (h : ∀ k, W ≤ blockChart n k (c k)) (q : Σ k, Bk n k) :
    Γ(MP ℤ m n, W) :=
  pullRatio (prB n q.1) W (c q.1) (h q.1) q.2

theorem closure_ratio (N : ℕ) (i : Fin (N + 1)) : Subring.closure (Set.range (ratio ℤ N i)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨p, rfl⟩ := aeval_ratio_surjective ℤ N i v
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [aeval_C]
    simp
  | add p q hp hq =>
    rw [map_add]
    exact add_mem (hp trivial) (hq trivial)
  | mul_X p j hp =>
    rw [map_mul, aeval_X]
    exact mul_mem (hp trivial) (Subring.subset_closure ⟨j, rfl⟩)

theorem eq_top_of_isPushout {R A B C : CommRingCat.{0}} {a : R ⟶ A} {b : R ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (H : IsPushout a b f g) (S : Subring C) (hf : ∀ x, f x ∈ S) (hg : ∀ x, g x ∈ S) : S = ⊤ := by
  let ι : CommRingCat.of S ⟶ C := CommRingCat.ofHom S.subtype
  let f' : A ⟶ .of S := CommRingCat.ofHom (f.hom.codRestrict S hf)
  let g' : B ⟶ .of S := CommRingCat.ofHom (g.hom.codRestrict S hg)
  have w : a ≫ f' = b ≫ g' := by
    ext x
    exact congr($(H.w) x)
  let d := H.desc f' g' w
  have e : d ≫ ι = 𝟙 C := H.hom_ext (by rw [H.inl_desc_assoc]; rfl) (by rw [H.inr_desc_assoc]; rfl)
  rw [eq_top_iff]
  intro x _
  have h : ι (d x) = x := congr($e x)
  exact h ▸ (d x).2

theorem mchart_succ {m : ℕ} {n : Fin (m + 2) → ℕ} (c : ∀ k, Bk n k) :
    mchart c = pullback.fst (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ chart ℤ (n 0) (c 0) ⊓
      pullback.snd (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ
        mchart (n := Fin.tail n) (fun k => c k.succ) := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ⟨fun hx => ?_, ?_⟩)
  · exact ⟨Set.mem_iInter.1 hx 0, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k.succ⟩
  · rintro ⟨h0, h1⟩
    refine Set.mem_iInter.2 fun k => ?_
    induction k using Fin.cases with
    | zero => exact h0
    | succ k => exact Set.mem_iInter.1 h1 k

theorem add_one_pow_eq_ringHom_image_add_prime_mul_zero : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) (W : (MP ℤ m n).Opens), W = mchart c →
    ∀ h : ∀ k, W ≤ blockChart n k (c k),
      IsAffineOpen W ∧ Subring.closure (Set.range (rtOn c W h)) = ⊤ := by
  intro m
  induction m with
  | zero =>
    intro n c W hW h
    have e : W = (chart ℤ (n 0) (c 0) : (MP ℤ 0 n).Opens) := by
      rw [hW]
      refine TopologicalSpace.Opens.ext (Set.ext fun x => ⟨fun hx => Set.mem_iInter.1 hx 0, fun hx => ?_⟩)
      refine Set.mem_iInter.2 fun k => ?_
      have hk : k = 0 := Fin.eq_zero k
      subst k
      exact hx
    clear hW
    subst W
    refine ⟨isAffineOpen_chart ℤ (n 0) (c 0), ?_⟩
    refine eq_top_iff.2 fun x _ => ?_
    have hx : (x : Γ(PSpace ℤ (n 0), chart ℤ (n 0) (c 0))) ∈
        Subring.closure (Set.range (ratio ℤ (n 0) (c 0))) := by
      rw [closure_ratio]
      trivial
    refine Subring.closure_mono ?_ hx
    rintro _ ⟨j, rfl⟩
    refine ⟨⟨0, j⟩, ?_⟩
    exact (Conormal.id_appLE _ _).trans (resG_self _ _)
  | succ m ih =>
    intro n c W hW h
    let c' : ∀ k, Bk (Fin.tail n) k := fun k => c k.succ
    obtain ⟨ha, hc⟩ := ih (Fin.tail n) c' _ rfl (mchart_le c')
    have H := IsPullback.of_hasPullback (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n))
    obtain ⟨h1, h2⟩ := GlobalTheory.Conormal.isAffineOpen_and_isPushout H (U := ⊤) (isAffineOpen_top _) ha
      (isAffineOpen_chart ℤ (n 0) (c 0)) le_top le_top
    obtain rfl := hW.trans (mchart_succ c)
    refine ⟨h1, eq_top_of_isPushout h2 _ (fun x => ?_) (fun x => ?_)⟩
    · have hle : Subring.closure (Set.range (ratio ℤ (n 0) (c 0))) ≤
          (Subring.closure (Set.range (rtOn c _ h))).comap (Scheme.Hom.appLE
            (pullback.fst (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n))) (chart ℤ (n 0) (c 0)) _ inf_le_left).hom := by
        rw [Subring.closure_le]
        rintro _ ⟨j, rfl⟩
        exact Subring.subset_closure ⟨⟨0, j⟩, rfl⟩
      exact hle (closure_ratio (n 0) (c 0) ▸ Subring.mem_top x)
    · have hle : Subring.closure (Set.range (rtOn (n := Fin.tail n) (fun k => c k.succ) _ (mchart_le _))) ≤
          (Subring.closure (Set.range (rtOn c _ h))).comap (Scheme.Hom.appLE
            (pullback.snd (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n)))
            (mchart (n := Fin.tail n) (fun k => c k.succ)) _ inf_le_right).hom := by
        rw [Subring.closure_le]
        rintro _ ⟨⟨k, j⟩, rfl⟩
        refine Subring.subset_closure ⟨⟨k.succ, j⟩, ?_⟩
        exact (appLE_pullRatio _ _).symm
      exact hle (hc ▸ Subring.mem_top x)

theorem gen (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) :
    IsAffineOpen (mchart c) ∧ Subring.closure (Set.range (rt c)) = ⊤ := by
  obtain ⟨h₁, h₂⟩ := add_one_pow_eq_ringHom_image_add_prime_mul_zero m n c _ rfl (mchart_le c)
  refine ⟨h₁, ?_⟩
  rw [← h₂]
  congr 2
  funext q
  exact resG_pullRatio _

theorem contDiffAt_zpow_of_ne' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (h0 : f x ≠ 0) (a : ℤ) : ContDiffAt ℝ ∞ (fun y => f y ^ a) x := by
  obtain ⟨b, rfl | rfl⟩ := a.eq_nat_or_neg
  · simpa only [zpow_natCast] using hf.pow b
  · simp only [zpow_neg, zpow_natCast]
    exact (hf.pow b).inv (pow_ne_zero b h0)

theorem contDiffOn_of_holo {ι : Type} [Fintype ι] {B : Set (ι → ℂ)} (hB : IsOpen B) {f : (ι → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f B) : ContDiffOn ℝ ∞ f B := by
  let e : (ι → ℂ) ≃L[ℂ] (Fin (Module.finrank ℂ (ι → ℂ)) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have ha : AnalyticOnNhd ℂ f B := by
    intro z hz
    have h := ReciprocityTheory.AnForm.Osgood.osgood _ (e.symm ⁻¹' B) (f ∘ e.symm)
      (hB.preimage e.symm.continuous)
      (hf.comp e.symm.differentiableOn (fun _ h => h)) (e z) (by simpa using hz)
    have h2 := h.comp (e.analyticAt z)
    refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  have hc : ContDiffOn ℂ ∞ f B := (ha.contDiffOn hB.uniqueDiffOn).of_le le_top
  exact hc.restrict_scalars ℝ

theorem mem_mchart {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : IsUnder y z)
    {c : ∀ k, Bk n k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) : y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := by
  refine mem_ptsIn.2 (Set.mem_iInter.2 fun k => ?_)
  exact mem_ptsIn.1 ((H k (c k)).1.2 (hc k))

theorem ev_rt {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : IsUnder y z)
    {c : ∀ k, Bk n k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (q : Σ k, Bk n k) :
    CxPts.ev (mpStr ℤ m n) σ₀ (mchart c) (rt c q) y = z q / z ⟨q.1, c q.1⟩ := by
  rw [rt, CxPts.ev_res _ (mem_mchart H hc)]
  exact (H q.1 (c q.1)).2 q.2 ((H q.1 (c q.1)).1.2 (hc q.1))

theorem differentiableOn_ev {c : ∀ k, Bk n k} {s : ((Σ k, Bk n k) → ℂ) → CxPts (mpStr ℤ m n) σ₀}
    (hs : ∀ z, (∀ k, z ⟨k, c k⟩ ≠ 0) → IsUnder (s z) z) (a : Γ(MP ℤ m n, mchart c)) :
    DifferentiableOn ℂ (CxPts.ev (mpStr ℤ m n) σ₀ (mchart c) a ∘ s) {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
  have hin : ∀ z, (∀ k, z ⟨k, c k⟩ ≠ 0) → s z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) :=
    fun z hz => mem_mchart (hs z hz) hz
  have ha : a ∈ Subring.closure (Set.range (rt c)) := by
    rw [(gen m n c).2]; trivial
  induction ha using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    have hd : DifferentiableOn ℂ (fun z : (Σ k, Bk n k) → ℂ => z q * (z ⟨q.1, c q.1⟩)⁻¹)
        {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := fun z hz =>
      ((differentiableAt_apply (𝕜 := ℂ) q z).mul
        ((differentiableAt_apply (𝕜 := ℂ) _ z).inv (hz q.1))).differentiableWithinAt
    exact hd.congr fun z hz => (ev_rt (hs z hz) hz q).trans (div_eq_mul_inv _ _)
  | zero =>
    exact (differentiableOn_const 0).congr fun z hz => by
      simp only [Function.comp_apply, ev_eq (hin z hz), map_zero]
  | one =>
    exact (differentiableOn_const 1).congr fun z hz => by
      simp only [Function.comp_apply, ev_eq (hin z hz), map_one]
  | add x y _ _ hx hy =>
    exact (hx.add hy).congr fun z hz => by
      simp only [Function.comp_apply, Pi.add_apply, ev_add]
  | neg x _ hx =>
    exact hx.neg.congr fun z hz => by
      simp only [Function.comp_apply, Pi.neg_apply, ev_eq (hin z hz), map_neg]
  | mul x y _ _ hx hy =>
    exact (hx.mul hy).congr fun z hz => by
      simp only [Function.comp_apply, Pi.mul_apply, ev_mul]

theorem isSmoothHerm_of_isHermRep (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n))
    (A : Geo.HermLine (Bk n)) (hA : IsHermRep M A) : Geo.IsSmoothHerm A := by
  obtain ⟨u, -, -, hu⟩ := hA
  intro z₀ hz₀
  refine ContDiffAt.contDiffWithinAt ?_
  choose c hc using hz₀
  let T : Set ((Σ k, Bk n k) → ℂ) := {z | ∀ k, z ⟨k, c k⟩ ≠ 0}
  have hT : IsOpen T := by
    have : T = ⋂ k, {z | z ⟨k, c k⟩ ≠ 0} := by ext z; simp [T]
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
  have hmc : ∀ z ∈ T, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := fun z hz k => ⟨c k, hz k⟩
  haveI : Nonempty (CxPts (mpStr ℤ m n) σ₀) :=
    ⟨(Under.existsUnique_isUnder m n z₀ (hmc z₀ hc)).exists.choose⟩
  let s : ((Σ k, Bk n k) → ℂ) → CxPts (mpStr ℤ m n) σ₀ := fun z => Classical.epsilon fun y => IsUnder y z
  have hs : ∀ z, (∀ k, z ⟨k, c k⟩ ≠ 0) → IsUnder (s z) z := fun z hz =>
    Classical.epsilon_spec (Under.existsUnique_isUnder m n z (hmc z hz)).exists
  obtain ⟨hcont, hhol⟩ := holo_of_affine (gen m n c).1 hT (fun z hz => mem_mchart (hs z hz) hz)
    (differentiableOn_ev hs)
  have hsc : ContinuousAt s z₀ := hcont.continuousAt (hT.mem_nhds hc)
  obtain ⟨i, hi⟩ := exists_mem_ptsIn M.isLB.cover (s z₀)

  have hev : ∀ (W : (MP ℤ m n).Opens) (f : Γ(MP ℤ m n, W)), s z₀ ∈ ptsIn (mpStr ℤ m n) σ₀ W →
      ContDiffAt ℝ ∞ (fun z => CxPts.ev (mpStr ℤ m n) σ₀ W f (s z)) z₀ := by
    intro W f hW
    have hO : T ∩ s ⁻¹' ptsIn (mpStr ℤ m n) σ₀ W ∈ 𝓝 z₀ :=
      Filter.inter_mem (hT.mem_nhds hc) (hsc.preimage_mem_nhds ((isOpen_ptsIn W).mem_nhds hW))
    obtain ⟨B, hBs, hBo, hzB⟩ := mem_nhds_iff.1 hO
    exact (contDiffOn_of_holo hBo ((hhol W f).mono hBs)).contDiffAt (hBo.mem_nhds hzB)

  have hφ : ContDiffAt ℝ ∞ (fun z => (M.φ σ₀).φ i (s z)) z₀ := by
    obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := M.cInf σ₀ i (s z₀) hi
    have hg : ContDiffAt ℝ ∞ (fun z a => CxPts.ev (mpStr ℤ m n) σ₀ W (g a) (s z)) z₀ :=
      contDiffAt_pi.2 fun a => hev W (g a) h₁
    exact ((h₄.contDiffAt (h₂.mem_nhds h₃)).comp z₀ hg).congr_of_eventuallyEq (hsc.eventually h₅)
  have hiU : s z₀ ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) :=
    mem_ptsIn_inf.2 ⟨hi, mem_mchart (hs z₀ hc) hc⟩
  have hU : ContDiffAt ℝ ∞ (fun z => ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c)
      (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) (s z)‖) z₀ :=
    (hev _ _ hiU).norm ℝ (ev_ne_zero hiU (u i c).isUnit)
  have hP : ContDiffAt ℝ ∞ (fun z : (Σ k, Bk n k) → ℂ => ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) z₀ := by
    refine contDiffAt_prod fun k _ => ?_
    have hn : ContDiffAt ℝ ∞ (fun z : (Σ k, Bk n k) → ℂ => ‖z ⟨k, c k⟩‖) z₀ :=
      (contDiff_apply ℝ (fun _ => ℂ) (⟨k, c k⟩ : Σ k, Bk n k)).contDiffAt.norm ℝ (hc k)
    exact contDiffAt_zpow_of_ne' hn (norm_ne_zero_iff.2 (hc k)) (A.a k)
  have hE : ContDiffAt ℝ ∞ (fun z => Real.exp ((M.φ σ₀).φ i (s z) / 2)) z₀ :=
    (hφ.div_const 2).exp
  refine ((hP.mul hU).mul hE).congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ z in 𝓝 z₀, z ∈ T ∧ s z ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i) :=
    (hT.eventually_mem hc).and (hsc.eventually ((isOpen_ptsIn _).eventually_mem hi))
  filter_upwards [hmem] with z hz
  exact hu i c (s z) z (hs z hz.1) (mem_ptsIn_inf.2 ⟨hz.2, mem_mchart (hs z hz.1) hz.1⟩)

end GlobalTheory.CompanionTheory.MPDict.SmoothRep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentUnitaryActionIff
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentUnitaryActionIff
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree

theorem linearIndependent_gl_mulVec {K : Type} [CommRing K] {M n : ℕ} (g : GL (Fin M) K)
    (X : Fin n → Fin M → K) (hX : LinearIndependent K X) :
    LinearIndependent K (fun a => (g : Matrix (Fin M) (Fin M) K).mulVec (X a)) := by
  have hinj : Function.Injective (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) K)) := by
    intro x y hxy
    have h2 := congrArg (((g⁻¹ : GL (Fin M) K) : Matrix (Fin M) (Fin M) K).mulVec) hxy
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
    exact h2
  exact hX.map' (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) K)) (LinearMap.ker_eq_bot.2 hinj)

theorem actW_linearIndependent_iff : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), LinearIndependent (R ⊗[F] E) (actW R σ J h X) ↔ LinearIndependent (R ⊗[F] E) X := by
  intro F E _ _ _ R _ _ σ M n J h X
  set g := HA.mat R σ J h with hg
  have hact : actW R σ J h X = fun a => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec (X a) := rfl
  refine ⟨fun hY => ?_, fun hX => ?_⟩
  · have h2 := linearIndependent_gl_mulVec g⁻¹ _ hY
    have h3 : (fun a => ((g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec
        (actW R σ J h X a)) = X := by
      funext a
      rw [hact]
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rwa [h3] at h2
  · rw [hact]
    exact linearIndependent_gl_mulVec g X hX

end GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentUnitaryActionIffStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_unitary_action_iff : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), LinearIndependent (R ⊗[F] E) (actW R σ J h X) ↔ LinearIndependent (R ⊗[F] E) X := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree.actW_linearIndependent_iff | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree.actW_linearIndependent_iff | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree.actW_linearIndependent_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentExtendByUnitVector
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentExtendByUnitVector
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree

variable {K : Type} [CommRing K] {M n : ℕ}

theorem sum_vec_zero (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) (g : Fin (n + 1) → K) :
    (∑ a, g a • (vec α c X : Fin (n + 1) → Fin (M + 1) → K) a) 0
      = g 0 * α + ∑ j : Fin n, g j.succ * c j := by
  rw [Finset.sum_apply, Fin.sum_univ_succ]
  simp [vec]

theorem sum_vec_succ (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) (g : Fin (n + 1) → K)
    (i : Fin M) :
    (∑ a, g a • (vec α c X : Fin (n + 1) → Fin (M + 1) → K) a) i.succ
      = (∑ j : Fin n, g j.succ • X j) i := by
  rw [Finset.sum_apply, Fin.sum_univ_succ, Finset.sum_apply]
  simp [vec]

theorem linearIndependent_vec_iff (K : Type) [CommRing K] (M n : ℕ) (α : K) (hα : IsUnit α)
    (c : Fin n → K) (X : Fin n → Fin M → K) :
    LinearIndependent K (vec α c X : Fin (n + 1) → Fin (M + 1) → K) ↔ LinearIndependent K X := by
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h w hw j
    obtain ⟨β, hβ⟩ := hα.exists_left_inv
    have key := h (Fin.cons (-(∑ j : Fin n, w j * c j) * β) w) (by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [sum_vec_zero]
        simp only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply]
        rw [mul_assoc, hβ]
        ring
      · rw [sum_vec_succ]
        simp only [Fin.cons_succ, Pi.zero_apply]
        rw [hw]
        rfl) j.succ
    simpa using key
  · intro h w hw
    have hs : ∀ j : Fin n, w j.succ = 0 := by
      refine h (fun j => w j.succ) ?_
      funext i
      have := congrFun hw i.succ
      rwa [sum_vec_succ] at this
    have h0 : w 0 = 0 := by
      have := congrFun hw 0
      rw [sum_vec_zero] at this
      simp only [hs, zero_mul, Finset.sum_const_zero, add_zero, Pi.zero_apply] at this
      exact (hα.mul_left_eq_zero).1 this
    intro a
    refine Fin.cases h0 hs a

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentExtendByUnitVectorStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_extend_by_unit_vector : ∀ (K : Type) [CommRing K] (M n : ℕ) (α : K), IsUnit α → ∀ (c : Fin n → K) (X : Fin n → Fin M → K), LinearIndependent K (vec α c X : Fin (n + 1) → Fin (M + 1) → K) ↔ LinearIndependent K X := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree.linearIndependent_vec_iff | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree.linearIndependent_vec_iff | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree.linearIndependent_vec_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFreeSetProjectsCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFreeSetProjectsCompact
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF.Tails

theorem linearIndependent_tails {K : Type} [CommRing K] {M n : ℕ} {Y : Fin (n + 1) → Fin (M + 1) → K}
    (hY : LinearIndependent K Y) (h0 : ∀ i : Fin M, Y 0 i.succ = 0) :
    LinearIndependent K (fun (j : Fin n) (i : Fin M) => Y j.succ i.succ) := by
  have hfree := Fintype.linearIndependent_iff.1 hY

  have hnzd : ∀ b : K, b * Y 0 0 = 0 → b = 0 := by
    intro b hb
    have hsum : ∑ i, (Pi.single 0 b : Fin (n + 1) → K) i • Y i = 0 := by
      rw [Finset.sum_eq_single_of_mem (0 : Fin (n + 1)) (Finset.mem_univ _)
        (fun i _ hi => by simp [Pi.single_eq_of_ne hi])]
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hb
      · simp [h0 i]
    simpa using hfree _ hsum 0
  refine Fintype.linearIndependent_iff.2 fun w hw j => ?_
  have hw' : ∀ i : Fin M, ∑ j, w j * Y j.succ i.succ = 0 := by
    intro i
    have := congrFun hw i
    simpa [Finset.sum_apply] using this
  set r : K := ∑ j, w j * Y j.succ 0 with hr
  have hsum : ∑ i, (Fin.cons (-r) (fun j => Y 0 0 * w j) : Fin (n + 1) → K) i • Y i = 0 := by
    rw [Fin.sum_univ_succ]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero, Fin.cons_succ, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
        Pi.zero_apply]
      have h1 : ∑ j, Y 0 0 * w j * Y j.succ 0 = r * Y 0 0 := by
        rw [hr, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [h1]
      ring
    · simp only [Fin.cons_zero, Fin.cons_succ, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
        Pi.zero_apply, h0 i, mul_zero, zero_add]
      have : ∑ j, Y 0 0 * w j * Y j.succ i.succ = Y 0 0 * ∑ j, w j * Y j.succ i.succ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, hw' i, mul_zero]
  have hj := hfree _ hsum j.succ
  rw [Fin.cons_succ] at hj
  exact hnzd _ (by rw [mul_comm]; exact hj)

theorem exists_compact_tails (K : Type) [CommRing K] [TopologicalSpace K] [T2Space K] (M n : ℕ)
    (Q : Set (Fin (n + 1) → Fin (M + 1) → K)) (hQ : IsCompact Q)
    (hfree : ∀ Y ∈ Q, LinearIndependent K Y) :
    ∃ C : Set (Fin n → Fin M → K), IsCompact C ∧ (∀ X ∈ C, LinearIndependent K X) ∧
      ∀ (A : K) (c : Fin n → K) (X : Fin n → Fin M → K), vec A c X ∈ Q → X ∈ C := by
  let tl : (Fin (n + 1) → Fin (M + 1) → K) → Fin n → Fin M → K := fun Y j i => Y j.succ i.succ
  have htl : Continuous tl :=
    continuous_pi fun j => continuous_pi fun i => (continuous_apply i.succ).comp (continuous_apply j.succ)
  have hclosed : IsClosed {Y : Fin (n + 1) → Fin (M + 1) → K | ∀ i : Fin M, Y 0 i.succ = 0} := by
    have : {Y : Fin (n + 1) → Fin (M + 1) → K | ∀ i : Fin M, Y 0 i.succ = 0} =
        ⋂ i : Fin M, {Y | Y 0 i.succ = 0} := by
      ext Y
      simp
    rw [this]
    exact isClosed_iInter fun i =>
      isClosed_eq ((continuous_apply i.succ).comp (continuous_apply 0)) continuous_const
  refine ⟨tl '' (Q ∩ {Y | ∀ i : Fin M, Y 0 i.succ = 0}), (hQ.inter_right hclosed).image htl, ?_, ?_⟩
  · rintro _ ⟨Y, ⟨hYQ, h0⟩, rfl⟩
    exact linearIndependent_tails (hfree Y hYQ) h0
  · intro A c X h
    exact ⟨vec A c X, ⟨h, fun i => by simp [vec]⟩, by funext j i; simp [tl, vec]⟩

end GlobalTheory.CompanionTheory.SW.StageF.Tails
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFreeSetProjectsCompactStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_free_set_projects_compact : ∀ (K : Type) [CommRing K] [TopologicalSpace K] [T2Space K] (M n : ℕ) (Q : Set (Fin (n + 1) → Fin (M + 1) → K)), IsCompact Q → (∀ Y ∈ Q, LinearIndependent K Y) → ∃ C : Set (Fin n → Fin M → K), IsCompact C ∧ (∀ X ∈ C, LinearIndependent K X) ∧ ∀ (A : K) (c : Fin n → K) (X : Fin n → Fin M → K), vec A c X ∈ Q → X ∈ C := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.Tails.exists_compact_tails | exact GlobalTheory.CompanionTheory.SW.StageF.Tails.exists_compact_tails | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.Tails.exists_compact_tails <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsRepOrderedWordOccurs
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsRepOrderedWordOccurs
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

noncomputable section

namespace GlobalTheory.CompanionTheory.ZWordL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem decW_eq_decWord (Γ : Segment k) : decW Γ = Cos.decWord Γ := by
  apply List.ext_getElem
  · simp [decW, Cos.decWord]
  · intro n h1 h2
    simp only [decW, Cos.decWord, List.getElem_ofFn, List.getElem_reverse, List.length_ofFn, Fin.rev]
    congr 2
    omega

theorem isCusp_of_mem_decWord (Γ : Segment k) : ∀ w ∈ Cos.decWord Γ, w.IsCusp := by
  intro w hw
  simp only [Cos.decWord, List.mem_reverse, List.mem_ofFn] at hw
  obtain ⟨a, rfl⟩ := hw
  exact Γ.isCusp_term a

theorem sum_get_decWord (Γ : Segment k) : ∑ a, ((Cos.decWord Γ).get a).1 = Γ.deg := by
  have hc : ∀ a, ((Cos.decWord Γ).get a).1 = Γ.d := fun a => by
    have hm := List.get_mem (Cos.decWord Γ) a
    simp only [Cos.decWord, List.mem_reverse, List.mem_ofFn] at hm
    obtain ⟨i, hi⟩ := hm
    show ((List.ofFn Γ.term).reverse.get a).1 = Γ.d
    rw [← hi]
    rfl
  rw [Finset.sum_congr rfl (fun a _ => hc a), Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simp [Cos.decWord, Segment.deg]

theorem nontrivial_of_isIrreducible {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} (h : σ.IsIrreducible) : Nontrivial W := by
  by_contra hW
  rw [not_nontrivial_iff_subsingleton] at hW
  haveI : IsSimpleOrder (Subrepresentation σ) := h
  exact bot_ne_top (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _) :
    (⊥ : Subrepresentation σ) = ⊤)

theorem wd_wtW_of_isL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → ∀ (𝔪 : Multiset (Segment k)) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsL 𝔪 π → ∀ (h : ℕ) (Δ : Fin h → Segment k), IsOrderedForm Δ 𝔪 → Wd π (wtW Δ) := by
  intro k _ _ _ _ hA hS hJ 𝔪 N V _ _ π hπ h Δ hΔ
  have hmem : ∀ i, Δ i ∈ 𝔪 := fun i => hΔ.1 ▸ Multiset.mem_map_of_mem Δ (Finset.mem_univ i)
  choose x hx using fun i => SumProd.exists_isLSeg_of_isL hπ (hmem i)
  have hF : LFactors 𝔪 x := ⟨Δ, hΔ, hx⟩
  have hd0 : ∑ a, (x a).1 = N := (SumProd.sum_fst_of_lFactors hF).trans (SumProd.deg_of_isL hπ)
  have hd : ∑ a, (x (Fin.rev a)).1 = N := (Equiv.sum_comp Fin.revPerm (fun a => (x a).1)).trans hd0
  obtain ⟨hirr, f, hfinj, -⟩ := hS 𝔪 h N x hd hF π hπ
  obtain ⟨h', x', hd', hF', hcos⟩ := hπ
  have hsm : IsSmooth π := IsSubquotient.isSmooth (IsCosocle.isSubquotient hcos) (isSmooth_prodIrr _ _)
  have hfl : HasFiniteLength π := hasFiniteLength_of_isIrreducible hirr
  haveI := nontrivial_of_isIrreducible hirr
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h1 : 1 ≤ jm (x ∘ Fin.rev) hd π :=
    GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA (x ∘ Fin.rev) hd π hsm f
      ⟨v, fun h0 => hv (hfinj (h0.trans (map_zero f).symm))⟩
  have hW : ∀ b, ∑ a, ((Cos.decWord (Δ (Fin.rev b))).get a).1 = ((x ∘ Fin.rev) b).1 := fun b =>
    (sum_get_decWord _).trans (hx (Fin.rev b)).deg_eq
  have h2 := GlobalTheory.T.jacquet_multiplicity_transitive_le hA (x ∘ Fin.rev) hd (fun b => Cos.decWord (Δ (Fin.rev b))) π hsm hfl hW
  have h3 : ∀ b, Cos.jmL (Cos.decWord (Δ (Fin.rev b))) ((x ∘ Fin.rev) b).rep = 1 := fun b =>
    (GlobalTheory.T.segment_rep_jacquet_word_multiplicity hA hJ (Δ (Fin.rev b)) _ (hx (Fin.rev b)) _ (isCusp_of_mem_decWord _)).1 rfl
  rw [Finset.prod_congr rfl (fun b _ => h3 b), Finset.prod_const_one, mul_one] at h2
  have h4 := h1.trans h2
  have hw : (List.ofFn fun b => Cos.decWord (Δ (Fin.rev b))).flatten = wtW Δ := by
    simp only [wtW, decW_eq_decWord]
  rw [hw] at h4
  unfold Cos.jmL at h4
  split_ifs at h4 with hdw
  · exact ⟨hdw, fun h0 => by rw [h0] at h4; simp at h4⟩
  · simp at h4

end GlobalTheory.CompanionTheory.ZWordL
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsRepOrderedWordOccursStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_rep_ordered_word_occurs : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → ∀ (𝔪 : Multiset (Segment k)) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsL 𝔪 π → ∀ (h : ℕ) (Δ : Fin h → Segment k), IsOrderedForm Δ 𝔪 → Wd π (wtW Δ) := by
  first | exact @GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL | exact GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL | (intros; apply GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureOrthogonalSum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureOrthogonalSum
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF

theorem isSFiniteKernel_of_compact_open {α β : Type} [MeasurableSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] [T2Space β] (κ : ProbabilityTheory.Kernel α β)
    {K : ℕ → Set β} (hK : ∀ k, IsCompact (K k)) {U : Set β} (hU : (⋃ k, K k) = U)
    (hc : ∀ a, κ a Uᶜ = 0) (hf : ∀ a k, κ a (K k) < ⊤) : ProbabilityTheory.IsSFiniteKernel κ := by
  let C : ℕ → Set β := disjointed K
  have hCm : ∀ k, MeasurableSet (C k) := fun k =>
    MeasurableSet.disjointed (fun i => (hK i).measurableSet) k
  have hCd : Pairwise (Function.onFun Disjoint C) := disjoint_disjointed _
  have hCu : ⋃ k, C k = U := by
    simp only [C, iUnion_disjointed]
    exact hU
  have hk : ∀ k, ProbabilityTheory.IsSFiniteKernel (ProbabilityTheory.Kernel.restrict κ (hCm k)) := fun k =>
    isSFiniteKernel_of_forall_univ_lt_top _ (fun a => by
      rw [ProbabilityTheory.Kernel.restrict_apply]
      simpa using (measure_mono (disjointed_subset _ k)).trans_lt (hf a k))
  have hsum : κ = ProbabilityTheory.Kernel.sum fun k => ProbabilityTheory.Kernel.restrict κ (hCm k) := by
    ext a s hs
    rw [ProbabilityTheory.Kernel.sum_apply]
    simp only [ProbabilityTheory.Kernel.restrict_apply]
    rw [← Measure.restrict_iUnion hCd hCm, hCu,
      Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 (hc a))]
  rw [hsum]
  infer_instance

theorem gramFibFree_basic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N n : ℕ) (J₂ : Matrix (Fin N) (Fin N) E), IsHermND σ J₂ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m : HermR R σ n → Measure (Fin n → Fin N → R ⊗[F] E), IsGramFibFree R σ J₂ n (coordW R b lam n N) (coordHerm R σ b lam n) m → (∀ S, SFinite (m S)) ∧ (∃ κ : ProbabilityTheory.Kernel (HermR R σ n) (Fin n → Fin N → R ⊗[F] E), ProbabilityTheory.IsSFiniteKernel κ ∧ ∀ S, κ S = m S) ∧ (∀ (C : Set (Fin n → Fin N → R ⊗[F] E)) (D : Set (HermR R σ n)), IsCompact C → C ⊆ {X | LinearIndependent (R ⊗[F] E) X} → IsCompact D → ∃ c : ℝ≥0, ∀ S ∈ D, m S C ≤ c) ∧ ∀ S : HermR R σ n, ∀ᵐ X ∂(m S), gramR R σ J₂ X = (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) ∧ LinearIndependent (R ⊗[F] E) X := by
  intro F E _ _ _ _ _ σ hCM N n J₂ hJ R _ _ _ _ _ hR d b lam hlam m hm
  obtain ⟨iTR, iLC, iSC, iT2, -⟩ := id hR
  haveI := iTR; haveI := iLC; haveI := iSC; haveI := iT2
  obtain ⟨kTR, kLC, kSC, kT2, -, -, -, kB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := kTR; haveI := kLC; haveI := kSC; haveI := kT2
  haveI := kB n N
  obtain ⟨hLC, hSC, hT2, hB, -⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hCM R n
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB
  have hU : IsOpen {X : Fin n → Fin N → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    GlobalTheory.T.linearly_independent_frames_open F E σ hCM R hR n N
  obtain ⟨h1, -, h3⟩ := hm
  have hbf : GlobalTheory.CompanionTheory.SW.FibreFam.BumpFamily {X : Fin n → Fin N → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}
      (Set.univ : Set (HermR R σ n)) m :=
    ⟨fun S hS => absurd (Set.mem_univ S) hS, h3⟩
  have hUc : ∀ S, m S {X : Fin n → Fin N → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}ᶜ = 0 := fun S =>
    measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_right) (h1 S)
  have hmeas : ∀ A : Set (Fin n → Fin N → R ⊗[F] E), MeasurableSet A → Measurable fun S => m S A :=
    fun A hA => hbf.measurable_apply isOpen_univ hU hUc hA
  let κ : ProbabilityTheory.Kernel (HermR R σ n) (Fin n → Fin N → R ⊗[F] E) :=
    ⟨m, Measure.measurable_of_measurable_coe _ hmeas⟩
  obtain ⟨K, W, hK, -, -, hKU, -, -, hKun, -⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_exhaustion hU
  haveI hκ : ProbabilityTheory.IsSFiniteKernel κ :=
    isSFiniteKernel_of_compact_open κ hK hKun hUc
      (fun S k => hbf.lt_top hU (hK k) (hKU k) S)
  refine ⟨fun S => (inferInstance : SFinite (κ S)), ⟨κ, hκ, fun _ => rfl⟩, ?_, fun S => ?_⟩
  · intro C D hC hCU hD
    obtain ⟨φ, hc, hcs, hs, h0, -, hone⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump hC hU hCU
    obtain ⟨hi, hco⟩ := h3 φ hc hcs hs
    obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn (hco.mono (Set.subset_univ D))
    refine ⟨M.toNNReal, fun S hS => ?_⟩
    calc m S C ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂(m S) :=
          GlobalTheory.CompanionTheory.SW.FibreFam.le_lintegral_bump _ hC h0 hone
      _ = ENNReal.ofReal (∫ v, φ v ∂(m S)) :=
          (ofReal_integral_eq_lintegral_ofReal (hi S (Set.mem_univ S))
            (Filter.Eventually.of_forall h0)).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM S hS))
      _ = (M.toNNReal : ℝ≥0∞) := rfl
  · have : ∀ᵐ X ∂(m S), X ∈ gramR R σ J₂ ⁻¹' {((S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E))} ∩
        {X : Fin n → Fin N → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
      mem_ae_iff.2 (h1 S)
    filter_upwards [this] with X hX
    exact ⟨hX.1, hX.2⟩

end GlobalTheory.CompanionTheory.SW.StageF
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureOrthogonalSumStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fibre_measure_orthogonal_sum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N n : ℕ) (J₂ : Matrix (Fin N) (Fin N) E), IsHermND σ J₂ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m : HermR R σ n → Measure (Fin n → Fin N → R ⊗[F] E), IsGramFibFree R σ J₂ n (coordW R b lam n N) (coordHerm R σ b lam n) m → (∀ S, SFinite (m S)) ∧ (∃ κ : ProbabilityTheory.Kernel (HermR R σ n) (Fin n → Fin N → R ⊗[F] E), ProbabilityTheory.IsSFiniteKernel κ ∧ ∀ S, κ S = m S) ∧ (∀ (C : Set (Fin n → Fin N → R ⊗[F] E)) (D : Set (HermR R σ n)), IsCompact C → C ⊆ {X | LinearIndependent (R ⊗[F] E) X} → IsCompact D → ∃ c : ℝ≥0, ∀ S ∈ D, m S C ≤ c) ∧ ∀ S : HermR R σ n, ∀ᵐ X ∂(m S), gramR R σ J₂ X = (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) ∧ LinearIndependent (R ⊗[F] E) X := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.gramFibFree_basic | exact GlobalTheory.CompanionTheory.SW.StageF.gramFibFree_basic | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.gramFibFree_basic <;> assumption)
end
end
