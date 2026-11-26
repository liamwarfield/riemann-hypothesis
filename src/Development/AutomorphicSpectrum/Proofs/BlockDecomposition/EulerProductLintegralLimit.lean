module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductLintegralLimit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductLintegralLimit
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem isHermND_hypOne (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) :
    IsHermND σ (hypOne J) := by
  refine ⟨fun i j => ?_, fun h => ?_⟩
  · induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => change σ 0 = 0; simp
      | succ j =>
        induction j using Fin.cases with
        | zero => change σ 1 = 1; simp
        | succ j => change σ 0 = 0; simp
    | succ i =>
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => change σ 1 = 1; simp
        | succ j =>
          induction j using Fin.cases with
          | zero => change σ 0 = 0; simp
          | succ j => change σ 0 = 0; simp
      | succ i =>
        induction j using Fin.cases with
        | zero => change σ 0 = 0; simp
        | succ j =>
          induction j using Fin.cases with
          | zero => change σ 0 = 0; simp
          | succ j => exact hJ.1 i j
  · obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    have hrow : ∀ i, ∑ j, hypOne J i j * v j = 0 := fun i => congrFun hv0 i
    have h1 : v 1 = 0 := by
      have := hrow 0
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at this
      simpa [hypOne_zero_rest, hypOne_zero_zero, hypOne_zero_one] using this
    have h0 : v 0 = 0 := by
      have := hrow 1
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at this
      simpa [hypOne_one_rest, hypOne_one_zero, hypOne_one_one] using this
    have ht : J.mulVec (fun j : Fin M => v j.succ.succ) = 0 := by
      funext i
      have := hrow i.succ.succ
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at this
      simpa [Matrix.mulVec, dotProduct, hypOne_rest_rest, hypOne_rest_zero, hypOne_rest_one] using this
    have hz : (fun j : Fin M => v j.succ.succ) = 0 := by
      by_contra hne
      exact hJ.2 (Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hne, ht⟩)
    apply hv
    funext i
    induction i using Fin.cases with
    | zero => exact h0
    | succ i =>
      induction i using Fin.cases with
      | zero => exact h1
      | succ i => exact congrFun hz i

end Alg

theorem measurableSet_primV (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSet (primV σ J b v) := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : T2Space (Fv F v) := inferInstance
  obtain ⟨-, -, -, t2, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := t2
  obtain ⟨-, lc, sc, -, -, hact⟩ := GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hσ (M + 2) (hypOne J)
    (isHermND_hypOne σ J hJ) (Fv F v)
  haveI := lc
  haveI := sc
  haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_fv F E σ hσ 1 (M + 2) v
  have hc := (hact 1).1
  have hlat := (GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b 1 (M + 2)).2.2.2.1 v
  have hclopen : IsClopen (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) :=
    ⟨hlat.1.isClosed, hlat.2⟩
  have hcl : IsClosed {g : HA (Fv F v) σ (hypOne J) | latStab σ (hypOne J) b v g} := by
    have hE : {g : HA (Fv F v) σ (hypOne J) | latStab σ (hypOne J) b v g} =
        ⋂ x : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E,
          {g | actW (Fv F v) σ (hypOne J) g x ∈ latV b v ↔ x ∈ latV b v} := by
      ext g
      simp [latStab]
    rw [hE]
    refine isClosed_iInter fun x => ?_
    have hcx : Continuous fun g : HA (Fv F v) σ (hypOne J) => actW (Fv F v) σ (hypOne J) g x :=
      hc.comp (continuous_id.prodMk continuous_const)
    have hp := hclopen.preimage hcx
    by_cases hx : x ∈ (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E))
    · have hs : {g : HA (Fv F v) σ (hypOne J) | actW (Fv F v) σ (hypOne J) g x ∈ latV b v ↔ x ∈ latV b v} =
          (fun g => actW (Fv F v) σ (hypOne J) g x) ⁻¹' latV b v := by
        ext g
        simp [hx]
      rw [hs]
      exact hp.1
    · have hs : {g : HA (Fv F v) σ (hypOne J) | actW (Fv F v) σ (hypOne J) g x ∈ latV b v ↔ x ∈ latV b v} =
          ((fun g => actW (Fv F v) σ (hypOne J) g x) ⁻¹' latV b v)ᶜ := by
        ext g
        simp [hx]
      rw [hs]
      exact hp.compl.1
  have hcont : Continuous fun g : HA (Fv F v) σ (hypOne J) => actW (Fv F v) σ (hypOne J) g (e0 _ M) :=
    hc.comp (continuous_id.prodMk continuous_const)
  have him : IsSigmaCompact (primV σ J b v) := by
    exact (isSigmaCompact_univ.of_isClosed_subset hcl (Set.subset_univ _)).image hcont
  obtain ⟨K, hK, hU⟩ := him
  rw [← hU]
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

theorem measurable_purePr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable Ψinf → (∀ v, Measurable (Ψ v)) → Measurable (purePr σ J b S Ψinf Ψ) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b S Ψinf Ψ hΨinf hΨ
  obtain ⟨hpi, hpf, hpv, -⟩ := GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b 1 (M + 2)
  haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_af F E σ hσ 1 (M + 2)
  haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_ainf F E σ hσ 1 (M + 2)
  haveI : ∀ v, BorelSpace (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) :=
    fun v => GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_fv F E σ hσ 1 (M + 2) v
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have hset : MeasurableSet {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E |
      ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v} := by
    have hE : {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E |
        ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v} =
        ⋂ v, ⋂ _ : v ∉ S, (fun y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E => projV v (projFin y)) ⁻¹'
          primV σ J b v := by
      ext y
      simp
    rw [hE]
    refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => ?_
    exact ((hpv v).comp hpf).measurable (measurableSet_primV F E σ hσ M J hJ d b v)
  unfold purePr
  refine Measurable.indicator ?_ hset
  refine (hΨinf.comp hpi.measurable).mul ?_
  refine Finset.measurable_prod _ fun v _ => ?_
  exact (hΨ v).comp ((hpv v).comp hpf).measurable

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductLintegralLimitStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_product_lintegral_limit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable Ψinf → (∀ v, Measurable (Ψ v)) → Measurable (purePr σ J b S Ψinf Ψ) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas.measurable_purePr | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas.measurable_purePr | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas.measurable_purePr <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSubLeOfNear
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

variable {l : ℕ} [Fact l.Prime]

def sh (x : Tl l) : ℂ_[l] := ((PreTilt.untilt x : GroundTheory.PAdicHodge.normInteger ℂ_[l]) : ℂ_[l])

def omC : Om l →+* ℂ_[l] := algebraMap (Om l) ℂ_[l]

theorem omC_apply (y : Om l) : omC y = (y : ℂ_[l]) := (PadicComplex.coe_eq _ y).symm

theorem norm_omC (y : Om l) : ‖omC y‖ = ‖y‖ := by
  rw [omC_apply, PadicComplex.norm_extends]

def oc (K : FinExt l) : ↥(OL K) →+* ℂ_[l] :=
  (omC (l := l)).comp ((K.1.val : ↥K.1 →+* Om l).comp (algebraMap ↥(OL K) ↥K.1))

theorem oc_apply (K : FinExt l) (c : ↥(OL K)) : oc K c = (((c : ↥K.1) : Om l) : ℂ_[l]) :=
  omC_apply _

theorem norm_oc_le_one (K : FinExt l) (c : ↥(OL K)) : ‖oc K c‖ ≤ 1 := by
  have h := (GlobalTheory.CompanionTheory.LTHodge.CharEx.mem_integer_iff K (c : ↥K.1)).1 (GlobalTheory.CompanionTheory.LTHodge.CharEx.intEquiv K c).2
  rw [oc_apply, PadicComplex.norm_extends]
  exact h

@[simp] theorem sh_zero : sh (0 : Tl l) = 0 := by
  simp [sh, GroundTheory.PAdicHodge.untilt_zero]

@[simp] theorem sh_one : sh (1 : Tl l) = 1 := by
  simp [sh]

theorem sh_mul (x y : Tl l) : sh (x * y) = sh x * sh y := by
  simp [sh, GroundTheory.PAdicHodge.untilt_mul]

theorem sh_pow (x : Tl l) (n : ℕ) : sh (x ^ n) = sh x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, sh_mul, ih]

theorem norm_eq_norm_sh (x : Tl l) : ‖x‖ = ‖sh x‖ := rfl

theorem norm_sh_le_one (x : Tl l) : ‖sh x‖ ≤ 1 := GroundTheory.PAdicHodge.norm_untilt_le_one x

theorem norm_sh_add_sub_le (x y : Tl l) : ‖sh (x + y) - (sh x + sh y)‖ ≤ ‖(l : ℂ_[l])‖ := by
  simpa [sh] using GroundTheory.PAdicHodge.norm_untilt_add_sub_le x y

theorem exists_sh_near (y : ℂ_[l]) (hy : ‖y‖ ≤ 1) : ∃ x : Tl l, ‖sh x - y‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨x, hx⟩ := GroundTheory.PAdicHodge.exists_mk_untilt_eq (K := ℂ_[l]) (p := l)
    ⟨y, GroundTheory.PAdicHodge.mem_normInteger.2 hy⟩
  exact ⟨x, by simpa [sh] using (GroundTheory.PAdicHodge.mk_eq_mk_iff_norm_sub_le (p := l)).1 hx⟩

theorem thB_tch (x : Tl l) : thB l (tch l x) = sh x := by
  show GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField l (wB l (WittVector.teichmuller l x)) = _
  rw [wB, GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus,
    WittVector.fontaineTheta_teichmuller]
  rfl

theorem thB_rB (y : Om l) : thB l (rB l y) = (y : ℂ_[l]) :=
  GroundTheory.PAdicHodge.thetaAlgHom_algClToBdR l y

theorem tch_mul (x y : Tl l) : tch l (x * y) = tch l x * tch l y := by
  simp [tch, map_mul]

theorem tch_pow (x : Tl l) (n : ℕ) : tch l (x ^ n) = tch l x ^ n := by
  induction n with
  | zero => simp [tch]
  | succ n ih => rw [pow_succ, pow_succ, tch_mul, ih]

theorem sh_actT (g : GQ l) (x : Tl l) :
    sh (actT g x) = GroundTheory.PAdicHodge.galCp (Formalism.Per6.toBot g) (sh x) :=
  GroundTheory.PAdicHodge.AInf.coe_untilt_gal (Formalism.Per6.toBot g) x

theorem galCp_omC (g : GQ l) (y : Om l) :
    GroundTheory.PAdicHodge.galCp (Formalism.Per6.toBot g) (omC y) = omC (g y) := by
  rw [omC_apply, omC_apply]
  exact GroundTheory.PAdicHodge.galCp_coe (Formalism.Per6.toBot g) y

theorem norm_galCp (g : GQ l) (x : ℂ_[l]) : ‖GroundTheory.PAdicHodge.galCp (Formalism.Per6.toBot g) x‖ = ‖x‖ :=
  GroundTheory.PAdicHodge.norm_galCp _ x

theorem norm_sub_pow (x y : Tl l) (f : ℕ) : ‖x ^ l ^ f - y ^ l ^ f‖ = ‖x - y‖ ^ l ^ f := by
  rw [← sub_pow_char_pow, norm_pow]

section Near

variable {ρ : ℝ}

theorem near_add (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x y : Tl l} {A B : ℂ_[l]} (hx : ‖sh x - A‖ ≤ ρ)
    (hy : ‖sh y - B‖ ≤ ρ) : ‖sh (x + y) - (A + B)‖ ≤ ρ := by
  have e : sh (x + y) - (A + B) = (sh (x + y) - (sh x + sh y)) + ((sh x - A) + (sh y - B)) := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((norm_sh_add_sub_le x y).trans hρ)
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)))

theorem near_mul {x y : Tl l} {A B : ℂ_[l]} (hB : ‖B‖ ≤ 1) (hx : ‖sh x - A‖ ≤ ρ)
    (hy : ‖sh y - B‖ ≤ ρ) : ‖sh (x * y) - A * B‖ ≤ ρ := by
  have e : sh (x * y) - A * B = sh x * (sh y - B) + (sh x - A) * B := by rw [sh_mul]; ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_sh_le_one x)).trans hy
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hB).trans hx

theorem near_neg (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x : Tl l} {A : ℂ_[l]} (hx : ‖sh x - A‖ ≤ ρ) :
    ‖sh (-x) - (-A)‖ ≤ ρ := by
  have h := norm_sh_add_sub_le x (-x)
  rw [add_neg_cancel, sh_zero, zero_sub, norm_neg] at h
  have e : sh (-x) - (-A) = (sh x + sh (-x)) - (sh x - A) := by ring
  rw [e, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (h.trans hρ) (by rw [norm_neg]; exact hx))

theorem near_sub (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x y : Tl l} {A B : ℂ_[l]} (hx : ‖sh x - A‖ ≤ ρ)
    (hy : ‖sh y - B‖ ≤ ρ) : ‖sh (x - y) - (A - B)‖ ≤ ρ := by
  rw [sub_eq_add_neg x y, sub_eq_add_neg A B]
  exact near_add hρ hx (near_neg hρ hy)

theorem near_pow (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x : Tl l} {A : ℂ_[l]} (hA : ‖A‖ ≤ 1)
    (hx : ‖sh x - A‖ ≤ ρ) (n : ℕ) : ‖sh (x ^ n) - A ^ n‖ ≤ ρ := by
  induction n with
  | zero => simpa using (norm_nonneg _).trans hρ
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact near_mul hA ih hx

theorem near_sum (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {ι : Type*} (s : Finset ι) {x : ι → Tl l}
    {A : ι → ℂ_[l]} (hx : ∀ i ∈ s, ‖sh (x i) - A i‖ ≤ ρ) :
    ‖sh (∑ i ∈ s, x i) - ∑ i ∈ s, A i‖ ≤ ρ := by
  induction s using Finset.induction_on with
  | empty => simpa using (norm_nonneg _).trans hρ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact near_add hρ (hx a (Finset.mem_insert_self _ _))
      (ih fun i hi => hx i (Finset.mem_insert_of_mem hi))

theorem near_of_norm_sub_le (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x y : Tl l} (h : ‖x - y‖ ≤ ρ) :
    ‖sh x - sh y‖ ≤ ρ := by
  have h1 : ‖sh (x - y) - 0‖ ≤ ρ := by rw [sub_zero]; exact h
  have h2 : ‖sh y - sh y‖ ≤ ρ := by simpa using (norm_nonneg _).trans hρ
  simpa using near_add hρ h1 h2

theorem norm_sub_le_of_near (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x y : Tl l} (h : ‖sh x - sh y‖ ≤ ρ) :
    ‖x - y‖ ≤ ρ := by
  have h1 : ‖sh x - sh x‖ ≤ ρ := by simpa using (norm_nonneg _).trans hρ
  have h2 : ‖sh y - sh y‖ ≤ ρ := by simpa using (norm_nonneg _).trans hρ
  have h3 := near_sub hρ h1 h2
  have e : sh (x - y) = (sh (x - y) - (sh x - sh y)) + (sh x - sh y) := by ring
  rw [norm_eq_norm_sh, e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h3 h)

end Near

theorem fixed_unique {f : ℕ} (hf : 0 < f) {x y : Tl l} (hx : x ^ l ^ f = x) (hy : y ^ l ^ f = y)
    (h : ‖x - y‖ < 1) : x = y := by
  have h1 : ‖x - y‖ = ‖x - y‖ ^ l ^ f := by rw [← norm_sub_pow, hx, hy]
  have hq : 1 < l ^ f := Nat.one_lt_pow hf.ne' (Fact.out : l.Prime).one_lt
  by_contra hne
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have := pow_lt_self_of_lt_one₀ hpos h hq
  linarith

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorIndexBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorIndexBound
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

variable {K : Type} [Field K] [NumberField K]

theorem index_toAddSubgroup (a : Ideal (𝓞 K)) :
    (Submodule.toAddSubgroup a).index = Ideal.absNorm a := (Ideal.absNorm_eq_index a).symm

theorem relIndex_mul_ideal (𝔱 a : Ideal (𝓞 K)) (ha : a ≠ ⊥) :
    (Submodule.toAddSubgroup (𝔱 * a)).relIndex (Submodule.toAddSubgroup a) =
      Ideal.absNorm 𝔱 := by
  have hle : Submodule.toAddSubgroup (𝔱 * a) ≤ Submodule.toAddSubgroup a :=
    (Submodule.toAddSubgroup_le _ _).2 Ideal.mul_le_right
  have h := AddSubgroup.relIndex_mul_index hle
  rw [index_toAddSubgroup, index_toAddSubgroup, map_mul] at h
  have hne : Ideal.absNorm a ≠ 0 := fun h0 => ha (Ideal.absNorm_eq_zero_iff.1 h0)
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) h

theorem mem_den_iff (x : K) (a : 𝓞 K) :
    a ∈ den K x ↔ (a : K) * x ∈ (1 : Submodule (𝓞 K) K) := by
  rw [den, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro h
    obtain ⟨o, ho⟩ := h 0
    exact Submodule.mem_one.2 ⟨o, by simpa [Algebra.smul_def] using ho⟩
  · intro h
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h
    intro i
    exact ⟨o, by simpa [Algebra.smul_def] using ho⟩

theorem absNorm_den_le (x : K) (d e : 𝓞 K) (hd : d ≠ 0) (hex : (e : K) = (d : K) * x)
    (B : Ideal (𝓞 K)) (hdB : Ideal.span {d} ≤ B) (heB : e ∈ B)
    (hfin : (Submodule.toAddSubgroup (Ideal.span {d})).relIndex (Submodule.toAddSubgroup B) ≠ 0) :
    Ideal.absNorm (den K x) ≤
      (Submodule.toAddSubgroup (Ideal.span {d})).relIndex (Submodule.toAddSubgroup B) := by
  set H := (Submodule.toAddSubgroup (Ideal.span {d})).addSubgroupOf (Submodule.toAddSubgroup B)
    with hH
  let g : 𝓞 K →+ Submodule.toAddSubgroup B :=
    { toFun := fun r => ⟨r * e, B.mul_mem_left r heB⟩
      map_zero' := by ext; simp
      map_add' := fun r s => by ext; simp [add_mul] }
  let f : 𝓞 K →+ (Submodule.toAddSubgroup B) ⧸ H := (QuotientAddGroup.mk' H).comp g
  have hdK : (d : K) ≠ 0 := by simpa using hd
  have hker : f.ker = Submodule.toAddSubgroup (den K x) := by
    ext r
    rw [AddMonoidHom.mem_ker]
    change (QuotientAddGroup.mk (g r) : _ ⧸ H) = 0 ↔ r ∈ den K x
    rw [QuotientAddGroup.eq_zero_iff, hH, AddSubgroup.mem_addSubgroupOf, mem_den_iff]
    change r * e ∈ Ideal.span {d} ↔ _
    rw [Ideal.mem_span_singleton', Submodule.mem_one]
    constructor
    · rintro ⟨o, ho⟩
      refine ⟨o, ?_⟩
      have := congrArg (fun y : 𝓞 K => (y : K)) ho
      simp only [map_mul, hex] at this
      apply mul_left_cancel₀ hdK
      change (d : K) * (o : K) = _
      linear_combination this
    · rintro ⟨o, ho⟩
      refine ⟨o, ?_⟩
      apply RingOfIntegers.coe_injective
      have ho' : (o : K) = (r : K) * x := ho
      simp only [map_mul, hex, ho']
      ring
  have hidx : (den K x).toAddSubgroup.index = Nat.card f.range := by
    rw [← hker]; exact AddSubgroup.index_ker f
  have hfinite : Finite ((Submodule.toAddSubgroup B) ⧸ H) := Nat.finite_of_card_ne_zero hfin
  calc Ideal.absNorm (den K x) = Nat.card f.range := by rw [Ideal.absNorm_eq_index]; exact hidx
    _ ≤ Nat.card ((Submodule.toAddSubgroup B) ⧸ H) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = _ := rfl

theorem span_le_mul (𝔱 a : Ideal (𝓞 K)) (h𝔱 : 𝔱 ≠ ⊥) (d : 𝓞 K) (hd : d ≠ 0)
    (H : ∀ b : K, (∀ u ∈ 𝔱, (u : K) * b ∈ (1 : Submodule (𝓞 K) K)) →
      ∃ y ∈ a, (y : K) = (d : K) * b) :
    Ideal.span {d} ≤ 𝔱 * a := by
  obtain ⟨s, hs𝔱, hs⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔱
  obtain ⟨𝔰, h𝔰⟩ := Ideal.dvd_span_singleton.2 hs𝔱
  have hsK : (s : K) ≠ 0 := by simpa using hs
  have h𝔰0 : 𝔰 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at h𝔰
    exact hs (Ideal.span_singleton_eq_bot.1 h𝔰)
  have hle : Ideal.span {d} * 𝔰 ≤ (𝔱 * a) * 𝔰 := by
    rw [Ideal.span_singleton_mul_le_iff]
    intro u hu
    have hmem : ∀ v ∈ 𝔱, (v : K) * ((u : K) / s) ∈ (1 : Submodule (𝓞 K) K) := by
      intro v hv
      have hvu : v * u ∈ Ideal.span {s} := by
        rw [h𝔰]; exact Ideal.mul_mem_mul hv hu
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hvu
      refine Submodule.mem_one.2 ⟨r, ?_⟩
      have := congrArg (fun y : 𝓞 K => (y : K)) hr
      simp only [map_mul] at this
      change (r : K) = _
      field_simp
      linear_combination this
    obtain ⟨y, hya, hy⟩ := H _ hmem
    have heq : d * u = s * y := by
      apply RingOfIntegers.coe_injective
      simp only [map_mul, hy]
      field_simp
    rw [heq, mul_right_comm 𝔱 a 𝔰, ← h𝔰, mul_comm s y]
    exact Ideal.mul_mem_mul hya (Ideal.mem_span_singleton_self s) |> fun h => by
      rwa [mul_comm a] at h
  rw [← Ideal.dvd_iff_le] at hle ⊢
  exact (mul_dvd_mul_iff_right h𝔰0).1 hle

theorem absNorm_mul_den_le_idx : ∀ (K : Type) [Field K] [NumberField K] (𝔱 : Ideal (𝓞 K)),
    𝔱 ≠ ⊥ → ∀ c : Submodule (𝓞 K) K, c.FG → (1 : Submodule (𝓞 K) K) ≤ c →
    (∀ b : K, (∀ a ∈ 𝔱, (a : K) * b ∈ (1 : Submodule (𝓞 K) K)) → b ∈ c) →
    ∀ (t : 𝓞 K) (w x : K), t ∈ 𝔱 → w ∈ c → (t : K) * w - x ∈ (1 : Submodule (𝓞 K) K) →
    Ideal.absNorm 𝔱 * Ideal.absNorm (den K x) ≤ idx K c := by
  intro K _ _ 𝔱 h𝔱 c hfg h1 hinv t w x ht hw hx
  obtain ⟨d, hd0, hint⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors (𝓞 K)) hfg
  have hd : d ≠ 0 := nonZeroDivisors.ne_zero hd0
  have hdK : (d : K) ≠ 0 := by simpa using hd
  have hint' : ∀ b ∈ c, ∃ y : 𝓞 K, (y : K) = (d : K) * b := by
    intro b hb
    obtain ⟨y, hy⟩ := hint b hb
    exact ⟨y, by simpa [Algebra.smul_def] using hy⟩
  let g : 𝓞 K →ₗ[𝓞 K] K := LinearMap.toSpanSingleton (𝓞 K) K ((d : K)⁻¹)
  have hg : ∀ y : 𝓞 K, g y = (y : K) * (d : K)⁻¹ := fun y => by
    simp [g, LinearMap.toSpanSingleton_apply, Algebra.smul_def]
  let a : Ideal (𝓞 K) := c.comap g
  have hmema : ∀ y : 𝓞 K, y ∈ a ↔ (y : K) * (d : K)⁻¹ ∈ c := fun y => by
    change g y ∈ c ↔ _
    rw [hg]
  have hga : ∀ b ∈ c, ∃ y ∈ a, (y : K) = (d : K) * b := by
    intro b hb
    obtain ⟨y, hy⟩ := hint' b hb
    refine ⟨y, (hmema y).2 ?_, hy⟩
    rw [hy]
    convert hb using 1
    field_simp
  have hda : d ∈ a := by
    rw [hmema, mul_inv_cancel₀ hdK]
    exact h1 (Submodule.one_le.1 le_rfl)
  have ha0 : a ≠ ⊥ := fun h => hd (by simpa [h] using hda)
  have hdle : Ideal.span {d} ≤ 𝔱 * a :=
    span_le_mul 𝔱 a h𝔱 d hd fun b hb => hga b (hinv b hb)
  have hBa : 𝔱 * a ≤ a := Ideal.mul_le_right

  have hinj : Function.Injective g.toAddMonoidHom := by
    intro y z hyz
    change g y = g z at hyz
    rw [hg, hg] at hyz
    exact RingOfIntegers.coe_injective (mul_right_cancel₀ (inv_ne_zero hdK) hyz)
  have hc : c.toAddSubgroup = (Submodule.toAddSubgroup a).map g.toAddMonoidHom := by
    ext b
    constructor
    · intro hb
      obtain ⟨y, hya, hy⟩ := hga b hb
      refine ⟨y, hya, ?_⟩
      change g y = b
      rw [hg, hy]
      field_simp
    · rintro ⟨y, hya, rfl⟩
      exact hya
  have hone : (1 : Submodule (𝓞 K) K).toAddSubgroup =
      (Submodule.toAddSubgroup (Ideal.span {d})).map g.toAddMonoidHom := by
    ext b
    constructor
    · intro hb
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 hb
      refine ⟨o * d, Ideal.mem_span_singleton'.2 ⟨o, rfl⟩, ?_⟩
      change g (o * d) = b
      rw [hg, ← ho]
      simp only [map_mul]
      change (o : K) * d * _ = o
      field_simp
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨o, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      refine Submodule.mem_one.2 ⟨o, ?_⟩
      change (o : K) = g (o * d)
      rw [hg]
      simp only [map_mul]
      field_simp
  have hidx : idx K c = (Submodule.toAddSubgroup (Ideal.span {d})).relIndex
      (Submodule.toAddSubgroup a) := by
    rw [idx, hc, hone, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
  have hdB : Submodule.toAddSubgroup (Ideal.span {d}) ≤ Submodule.toAddSubgroup (𝔱 * a) :=
    (Submodule.toAddSubgroup_le _ _).2 hdle
  have hBa' : Submodule.toAddSubgroup (𝔱 * a) ≤ Submodule.toAddSubgroup a :=
    (Submodule.toAddSubgroup_le _ _).2 hBa
  have hfin : (Submodule.toAddSubgroup (Ideal.span {d})).relIndex
      (Submodule.toAddSubgroup (𝔱 * a)) ≠ 0 := by
    intro h0
    have h := AddSubgroup.relIndex_mul_index hdB
    rw [h0, zero_mul, index_toAddSubgroup] at h
    exact hd (Ideal.span_singleton_eq_bot.1 (Ideal.absNorm_eq_zero_iff.1 h.symm))

  obtain ⟨yw, hywa, hyw⟩ := hga w hw
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 hx
  have ho' : (o : K) = (t : K) * w - x := ho
  have heK : ((t * yw - d * o : 𝓞 K) : K) = (d : K) * x := by
    simp only [map_sub, map_mul, hyw, ho']
    ring
  have heB : t * yw - d * o ∈ 𝔱 * a :=
    Ideal.sub_mem _ (Ideal.mul_mem_mul ht hywa)
      (hdle (Ideal.mem_span_singleton'.2 ⟨o, mul_comm _ _⟩))
  have hden := absNorm_den_le x d _ hd heK (𝔱 * a) hdle heB hfin
  rw [hidx, ← AddSubgroup.relIndex_mul_relIndex _ _ _ hdB hBa', relIndex_mul_ideal 𝔱 a ha0,
    mul_comm]
  exact Nat.mul_le_mul_right _ hden

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorIndexBoundStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.denominator_index_bound : ∀ (K : Type) [Field K] [NumberField K] (𝔱 : Ideal (𝓞 K)), 𝔱 ≠ ⊥ → ∀ c : Submodule (𝓞 K) K, c.FG → (1 : Submodule (𝓞 K) K) ≤ c → (∀ b : K, (∀ a ∈ 𝔱, (a : K) * b ∈ (1 : Submodule (𝓞 K) K)) → b ∈ c) → ∀ (t : 𝓞 K) (w x : K), t ∈ 𝔱 → w ∈ c → (t : K) * w - x ∈ (1 : Submodule (𝓞 K) K) → Ideal.absNorm 𝔱 * Ideal.absNorm (den K x) ≤ idx K c := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe.absNorm_mul_den_le_idx | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe.absNorm_mul_den_le_idx | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe.absNorm_mul_den_le_idx <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOrderedFormSnoc
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.ExhGood

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ind₂_map_injective_right {r t N : ℕ} (e : Fin r ⊕ Fin t ≃ Fin N) {U W W' : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U)
    {ρ : Representation ℂ (GL (Fin t) k) W} {ρ' : Representation ℂ (GL (Fin t) k) W'} (f : ρ.IntertwiningMap ρ')
    (hf : Function.Injective f) :
    ∃ F : (ind₂ e (extTensor σ ρ)).IntertwiningMap (ind₂ e (extTensor σ ρ')), Function.Injective F := by
  have hι : Function.Injective (GlobalTheory.ParIndExact.extTensorMapRight σ f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  have hι' : Function.Injective
      (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hι
  exact ⟨parIndMap (two e)
      (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom),
    GlobalTheory.ParIndExact.parIndMap_injective _ _ hι'⟩

theorem pair_equiv {N : ℕ} (y : Fin 2 → IrrGL (k := k)) (hd : ∑ i, (y i).1 = N) {a : IrrGL (k := k)} (ha : y 0 = a)
    (h : a.1 + (y 1).1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor a.rep (y 1).rep)).Equiv (prodIrr y hd)) := by
  subst ha h
  exact nonempty_prod₂_equiv_prodIrr_rep y hd

theorem embed_family {N c : ℕ} (y : Fin 2 → IrrGL (k := k)) (v : Fin (c + 1) → IrrGL (k := k)) (t : Fin c → IrrGL (k := k))
    (h0 : y 0 = v 0) (hs : ∀ i, v i.succ = t i) (hd : ∑ i, (y i).1 = N) (hv : ∑ i, (v i).1 = N)
    (ht : ∑ i, (t i).1 = (y 1).1) (g : (y 1).rep.IntertwiningMap (prodIrr t ht)) (hg : Function.Injective g) :
    ∃ F : (prodIrr y hd).IntertwiningMap (prodIrr v hv), Function.Injective F := by
  have e : t = fun i => v i.succ := funext fun i => (hs i).symm
  subst e
  have h : (v 0).1 + (y 1).1 = N := by
    rw [← h0, ← hd, Fin.sum_univ_two]
  have A0 := pair_equiv y hd h0 h
  have B0 := GlobalTheory.ProdReorder.multiProd_head (k := k) (d := fun i => (v i).1) (fun i => (v i).rep)
    (stdBlocks (fun i => (v i).1) hv) h (stdBlocks (fun i : Fin c => (v i.succ).1) ht)
  have F0 := ind₂_map_injective_right (stdSum h) (v 0).rep g hg
  obtain ⟨A⟩ := A0
  obtain ⟨B⟩ := B0
  obtain ⟨F, hF⟩ := F0
  exact ⟨(B.symm.toIntertwiningMap.comp F).comp A.symm.toIntertwiningMap,
    B.symm.toLinearEquiv.injective.comp (hF.comp A.symm.toLinearEquiv.injective)⟩

theorem isOrderedForm_snoc {h : ℕ} {Δ : Fin h → Segment k} {𝔫 : Multiset (Segment k)} (H : IsOrderedForm Δ 𝔫)
    (s : Segment k) (hs : ∀ D ∈ 𝔫, ¬ D.Precedes s) :
    IsOrderedForm (Fin.snoc (α := fun _ => Segment k) Δ s) (𝔫 + {s}) := by
  refine ⟨?_, fun i j hij => ?_⟩
  · rw [← H.1, Fin.univ_val_map, Fin.univ_val_map, List.ofFn_succ']
    simpa using (Multiset.coe_add _ [s]).symm
  · induction j using Fin.lastCases with
    | last =>
      obtain ⟨i, rfl⟩ : ∃ i', Fin.castSucc i' = i :=
        ⟨i.castPred (Fin.ne_last_of_lt hij), by simp⟩
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact hs _ (H.1 ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val i))
    | cast j =>
      obtain ⟨i, rfl⟩ : ∃ i', Fin.castSucc i' = i :=
        ⟨i.castPred (Fin.ne_last_of_lt hij), by simp⟩
      simp only [Fin.snoc_castSucc]
      exact H.2 i j (by simpa using hij)

end GlobalTheory.CompanionTheory.ExhGood

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ISupFiniteProductTailLimit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ISupFiniteProductTailLimit
open Filter Topology

namespace GlobalTheory.CompanionTheory.TailProd

theorem term_mono {ι : Type} [DecidableEq ι] (Mv τ p : ι → ℝ) (S : Finset ι)
    (hτ : Summable (fun v => |τ v - 1|)) (hp : Summable (fun v => |p v - 1|))
    (hM0 : ∀ v, 0 ≤ Mv v) (hτ0 : ∀ v, 0 ≤ τ v) (hp0 : ∀ v, 0 ≤ p v)
    (hle : ∀ v, v ∉ S → τ v * p v ≤ Mv v) :
    Monotone (fun S' : Finset ι => (∏ v ∈ (S ∪ S') \ S, Mv v) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) := by
  intro S₁ S₂ h12
  have hU : S ∪ S₁ ⊆ S ∪ S₂ := Finset.union_subset_union_right h12
  dsimp only
  rw [GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι τ (S ∪ S₁) (S ∪ S₂) hτ hU,
    GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι p (S ∪ S₁) (S ∪ S₂) hp hU]
  have hX : ∏ v ∈ (S ∪ S₂) \ S, Mv v =
      (∏ v ∈ (S ∪ S₁) \ S, Mv v) * ∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), Mv v := by
    have hD : ((S ∪ S₂) \ S) \ ((S ∪ S₁) \ S) = (S ∪ S₂) \ (S ∪ S₁) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [← Finset.prod_sdiff (Finset.sdiff_subset_sdiff hU (Finset.Subset.refl S)), hD, mul_comm]
  have hΔ : (∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), τ v) * (∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), p v) ≤
      ∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), Mv v := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun v _ => mul_nonneg (hτ0 v) (hp0 v))
      (fun v hv => hle v (fun hvS => (Finset.mem_sdiff.1 hv).2 (Finset.mem_union_left _ hvS)))
  have hX1 : 0 ≤ ∏ v ∈ (S ∪ S₁) \ S, Mv v := Finset.prod_nonneg fun v _ => hM0 v
  have hT : 0 ≤ ∏' v : {v // v ∉ S ∪ S₂}, τ v.1 :=
    (GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {v // v ∉ S ∪ S₂} (fun v => τ v.1)
      (hτ.comp_injective Subtype.val_injective)).2.2.2 fun v => hτ0 v.1
  have hP : 0 ≤ ∏' v : {v // v ∉ S ∪ S₂}, p v.1 :=
    (GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {v // v ∉ S ∪ S₂} (fun v => p v.1)
      (hp.comp_injective Subtype.val_injective)).2.2.2 fun v => hp0 v.1
  rw [hX]
  set X := ∏ v ∈ (S ∪ S₁) \ S, Mv v
  set D := (S ∪ S₂) \ (S ∪ S₁)
  set T := ∏' v : {v // v ∉ S ∪ S₂}, τ v.1
  set P := ∏' v : {v // v ∉ S ∪ S₂}, p v.1
  calc X * ((∏ v ∈ D, τ v) * T * ((∏ v ∈ D, p v) * P))
      = X * ((∏ v ∈ D, τ v) * (∏ v ∈ D, p v)) * (T * P) := by ring
    _ ≤ X * (∏ v ∈ D, Mv v) * (T * P) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΔ hX1) (mul_nonneg hT hP)

theorem iSup_partial_mul_tails : ∀ (ι : Type) [DecidableEq ι] (Mv τ p : ι → ℝ) (S : Finset ι),
    Summable (fun v => |Mv v - 1|) → Summable (fun v => |τ v - 1|) → Summable (fun v => |p v - 1|) →
    (∀ v, 0 ≤ Mv v) → (∀ v, 0 ≤ τ v) → (∀ v, 0 ≤ p v) → (∀ v, v ∉ S → τ v * p v ≤ Mv v) →
    ⨆ S' : Finset ι, ENNReal.ofReal ((∏ v ∈ (S ∪ S') \ S, Mv v) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) =
      ENNReal.ofReal (∏' v : {v // v ∉ S}, Mv v.1) := by
  intro ι _ Mv τ p S hMs hτs hps hM0 hτ0 hp0 hle
  have hmono := GlobalTheory.CompanionTheory.TailProd.term_mono Mv τ p S hτs hps hM0 hτ0 hp0 hle
  have hg : Tendsto (fun S' : Finset ι => S ∪ S') atTop atTop :=
    tendsto_atTop_mono (fun S' => (Finset.subset_union_right : S' ⊆ S ∪ S')) tendsto_id
  have hM := (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one Mv hMs).comp hg
  have hT := (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one τ hτs).comp hg
  have hP := (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one p hps).comp hg
  have hlim : Tendsto (fun S' : Finset ι => (∏' v : {v // v ∉ S}, Mv v.1) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * (∏' v : {v // v ∉ S ∪ S'}, p v.1) /
        ∏' v : {v // v ∉ S ∪ S'}, Mv v.1)) atTop (𝓝 (∏' v : {v // v ∉ S}, Mv v.1)) := by
    have := (tendsto_const_nhds (x := ∏' v : {v // v ∉ S}, Mv v.1)).mul
      ((hT.mul hP).div hM one_ne_zero)
    simpa only [Function.comp_def, Pi.div_apply, mul_one, div_one] using this
  have hA : Tendsto (fun S' : Finset ι => (∏ v ∈ (S ∪ S') \ S, Mv v) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) atTop
      (𝓝 (∏' v : {v // v ∉ S}, Mv v.1)) := by
    refine hlim.congr' ?_
    filter_upwards [hM.eventually_ne one_ne_zero] with S' hS'
    dsimp only [Function.comp] at hS' ⊢
    rw [GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι Mv S (S ∪ S') hMs Finset.subset_union_left,
      mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hS']
  exact iSup_eq_of_tendsto (fun a b h => ENNReal.ofReal_le_ofReal (hmono h))
    ((ENNReal.continuous_ofReal.tendsto _).comp hA)

end GlobalTheory.CompanionTheory.TailProd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ISupFiniteProductTailLimitStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iSup_finite_product_tail_limit : ∀ (ι : Type) [DecidableEq ι] (Mv τ p : ι → ℝ) (S : Finset ι), Summable (fun v => |Mv v - 1|) → Summable (fun v => |τ v - 1|) → Summable (fun v => |p v - 1|) → (∀ v, 0 ≤ Mv v) → (∀ v, 0 ≤ τ v) → (∀ v, 0 ≤ p v) → (∀ v, v ∉ S → τ v * p v ≤ Mv v) → ⨆ S' : Finset ι, ENNReal.ofReal ((∏ v ∈ (S ∪ S') \ S, Mv v) * ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) = ENNReal.ofReal (∏' v : {v // v ∉ S}, Mv v.1) := by
  first | exact @GlobalTheory.CompanionTheory.TailProd.iSup_partial_mul_tails | exact GlobalTheory.CompanionTheory.TailProd.iSup_partial_mul_tails | (intros; apply GlobalTheory.CompanionTheory.TailProd.iSup_partial_mul_tails <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroCoefficientTotal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroCoefficientTotal
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

variable {D : D7} {p : ℕ}

theorem mx_zero_subsingleton : Subsingleton (Mx D 0 p) :=
  ⟨fun _ _ => funext fun i => i.elim0⟩

theorem one_mem_schwartzA_zero (θ : InfFam D) : (fun _ => 1 : Mx D 0 p → ℂ) ∈ schwartzA θ 0 p := by
  refine Submodule.subset_span ?_
  let f : SchwartzMap (D.what₂.Tau → Fin 0 → Fin p → ℂ) ℂ :=
    { toFun := fun _ => 1
      smooth' := contDiff_const
      decay' := by
        intro k n
        refine ⟨1, fun x => ?_⟩
        have hx : x = 0 := Subsingleton.elim _ _
        subst hx
        rcases k with _ | k
        · rcases n with _ | n
          · simp
          · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
        · simp }
  refine ⟨f, fun _ => 1, ⟨IsLocallyConstant.const 1, ?_⟩, ?_⟩
  · exact (Set.subsingleton_of_subsingleton).isCompact
  · funext x
    exact (mul_one (1 : ℂ)).symm

theorem pr_zero (b₀ : HermE D 0) (x y : Mx D 0 p) : pr b₀ x y = 0 := by
  ext i j
  simp [pr, HMul.hMul]

theorem isTh_one {μ : Measure (Mx D 0 p)} (h1 : μ Set.univ = 1) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (b₀ : HermE D 0) : IsTh ψ 1 θ b₀ μ (fun _ _ => 1) := by
  have : IsProbabilityMeasure μ := ⟨h1⟩
  refine ⟨fun _ => one_mem_schwartzA_zero θ, continuous_const, ?_, ?_, ?_, ?_⟩
  · intro C _
    exact ⟨_, one_mem_schwartzA_zero θ, fun _ _ _ => le_rfl⟩
  · intro g a _ h y
    simp [npow]
  · intro g b _ h y
    simp [pr_zero, halfTr]
  · intro g _ h x
    simp [pr_zero]

theorem zeroTotal : ZeroTotal := by
  intro D p μ 𝓕 h ψ hψ b₀ θ hθ u hu hB hall
  have hs : Subsingleton (Mx D 0 p) := mx_zero_subsingleton
  obtain ⟨-, -, hF⟩ := h
  have hne : 𝓕.Nonempty := by
    rcases Set.eq_empty_or_nonempty 𝓕 with he | hn
    · simp [he] at hF
    · exact hn
  have huniv : 𝓕 = Set.univ := by
    obtain ⟨y, hy⟩ := hne
    exact Set.eq_univ_of_forall fun z => (Subsingleton.elim z y) ▸ hy
  have h1 : μ Set.univ = 1 := huniv ▸ hF
  have : IsProbabilityMeasure μ := ⟨h1⟩
  have h0 := hall _ (isTh_one h1 ψ θ b₀)
  have hc : (fun y => u y * conj (1 : ℂ)) = fun _ => u 0 := by
    funext y
    simp [Subsingleton.elim y 0]
  have h2 : u 0 = 0 := by
    have h3 : ∫ y, u y * conj (1 : ℂ) ∂μ = 0 := h0
    rw [hc] at h3
    simpa using h3
  funext y
  rw [Subsingleton.elim y 0, h2]
  rfl

end GlobalTheory.CompanionTheory.ThTot

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroCoefficientTotalStatement
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zero_coefficient_total : ZeroTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.zeroTotal | exact GlobalTheory.CompanionTheory.ThTot.zeroTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.zeroTotal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootsEqOfDistinctValuations
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootsEqOfDistinctValuations
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.RootsDistinctVal

theorem roots_eq_of_distinct_ord : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (y : Fin n → ℤ),
    Function.Injective y → ∀ u u' : Fin n → L, (∀ i, ordL (u i) = y i) → (∀ i, ordL (u' i) = y i) →
      ∏ i, (X - C (u i)) = ∏ i, (X - C (u' i)) → u = u' := by
  intro L _ _ n y hy u u' hu hu' hprod
  funext i
  have h0 : (∏ j, (X - C (u' j))).eval (u i) = 0 := by
    rw [← hprod, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h0
  obtain ⟨j, -, hj⟩ := h0
  have hij : u i = u' j := by simpa [sub_eq_zero] using hj
  have : i = j := hy (by rw [← hu i, ← hu' j, hij])
  rw [hij, this]

end GlobalTheory.CompanionTheory.RootsDistinctVal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootsEqOfDistinctValuationsStatement
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roots_eq_of_distinct_valuations : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (y : Fin n → ℤ), Function.Injective y → ∀ u u' : Fin n → L, (∀ i, ordL (u i) = y i) → (∀ i, ordL (u' i) = y i) → ∏ i, (X - C (u i)) = ∏ i, (X - C (u' i)) → u = u' := by
  first | exact @GlobalTheory.CompanionTheory.RootsDistinctVal.roots_eq_of_distinct_ord | exact GlobalTheory.CompanionTheory.RootsDistinctVal.roots_eq_of_distinct_ord | (intros; apply GlobalTheory.CompanionTheory.RootsDistinctVal.roots_eq_of_distinct_ord <;> assumption)
end
end
