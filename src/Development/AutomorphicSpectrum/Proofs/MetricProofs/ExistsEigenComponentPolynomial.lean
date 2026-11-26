module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjAvoidingForm
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAvoidFormFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormMax
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormDehomRoots
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameGenPtRel
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KodairaGenericOfAmpleSectionCount

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomial
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomial
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef

section Emb

variable {E : Type} [Field E] [NumberField E]

theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  have hc : (RingHom.ker s).comap (algebraMap ℤ (𝓞 E)) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
  exact (RingHom.injective_iff_ker_eq_bot s).2 (Ideal.eq_bot_of_comap_eq_bot hc)

def extEmb (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (emb_injective s)

theorem extEmb_apply (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : extEmb s (algebraMap (𝓞 E) E a) = s a :=
  IsFractionRing.lift_algebraMap (emb_injective s) a

theorem extEmb_comp (s : 𝓞 E →+* ℂ) : (extEmb s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext (extEmb_apply s)

theorem comp_injective {s s' : E →+* ℂ}
    (h : s.comp (algebraMap (𝓞 E) E) = s'.comp (algebraMap (𝓞 E) E)) : s = s' :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h

def charVec (a : 𝓞 E) : (E →+* ℂ) → ℂ := fun s => s (algebraMap (𝓞 E) E a)

def toChar (s : E →+* ℂ) : 𝓞 E →* ℂ := (s.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* ℂ)

theorem toChar_injective : Function.Injective (toChar (E := E)) := by
  intro s s' h
  exact comp_injective (RingHom.ext fun a => DFunLike.congr_fun h a)

theorem span_charVec : Submodule.span ℂ (Set.range (charVec (E := E))) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hf0
  have li := (linearIndependent_monoidHom (𝓞 E) ℂ).comp _ (toChar_injective (E := E))
  rw [Fintype.linearIndependent_iff] at li
  have hl := li (fun s => f fun j => if s = j then 1 else 0) (by
    funext a
    have h1 : f (charVec a) = 0 := hf (Submodule.subset_span ⟨a, rfl⟩)
    rw [LinearMap.pi_apply_eq_sum_univ] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp, smul_eq_mul, Pi.zero_apply]
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_eq_mul]
    exact mul_comm (_ : ℂ) _)
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.pi_apply_eq_sum_univ f v, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun s _ => (congrArg (v s • ·) (hl s)).trans (smul_zero _)

def evalHom (E : Type) [Field E] [NumberField E] : ℂ ⊗[ℤ] 𝓞 E →ₐ[ℂ] ((E →+* ℂ) → ℂ) :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ _)
    (Pi.ringHom fun s : E →+* ℂ => s.comp (algebraMap (𝓞 E) E)).toIntAlgHom
    fun x y => Algebra.commutes x _

theorem evalHom_tmul (z : ℂ) (a : 𝓞 E) (s : E →+* ℂ) :
    evalHom E (z ⊗ₜ a) s = z * s (algebraMap (𝓞 E) E a) := by
  have h := Algebra.TensorProduct.lift_tmul (Algebra.ofId ℂ ((E →+* ℂ) → ℂ))
    (Pi.ringHom fun s : E →+* ℂ => s.comp (algebraMap (𝓞 E) E)).toIntAlgHom
    (fun x y => Algebra.commutes x _) z a
  have h2 := congrFun h s
  have h3 : (Pi.ringHom fun s : E →+* ℂ => s.comp (algebraMap (𝓞 E) E)) a s =
      s (algebraMap (𝓞 E) E a) := rfl
  simpa [evalHom, Algebra.ofId_apply, h3] using h2

theorem evalHom_surjective : Function.Surjective (evalHom E) := by
  have h : (⊤ : Submodule ℂ ((E →+* ℂ) → ℂ)) ≤ LinearMap.range (evalHom E).toLinearMap := by
    rw [← span_charVec, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine ⟨1 ⊗ₜ a, ?_⟩
    funext s
    simp [evalHom_tmul, charVec]
  intro y
  obtain ⟨t, ht⟩ := h (Submodule.mem_top (x := y))
  exact ⟨t, ht⟩

theorem evalHom_injective : Function.Injective (evalHom E) := by
  have hdim : Module.finrank ℂ (ℂ ⊗[ℤ] 𝓞 E) = Module.finrank ℂ ((E →+* ℂ) → ℂ) := by
    rw [Module.finrank_baseChange, RingOfIntegers.rank, Module.finrank_fintype_fun_eq_card,
      NumberField.Embeddings.card]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (evalHom E).toLinearMap)).2 evalHom_surjective

def combo (c : 𝓞 E →₀ ℂ) : ℂ ⊗[ℤ] 𝓞 E := ∑ a ∈ c.support, c a ⊗ₜ a

theorem evalHom_combo (c : 𝓞 E →₀ ℂ) (s : E →+* ℂ) :
    evalHom E (combo c) s = ∑ a ∈ c.support, c a * s (algebraMap (𝓞 E) E a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [combo, map_sum, Finset.sum_apply, evalHom_tmul]


open Classical in
theorem exists_coeff (s : E →+* ℂ) : ∃ c : 𝓞 E →₀ ℂ, evalHom E (combo c) = Pi.single s 1 := by
  have h : (Pi.single s 1 : (E →+* ℂ) → ℂ) ∈ Submodule.span ℂ (Set.range (charVec (E := E))) := by
    rw [span_charVec]
    trivial
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h
  refine ⟨c, ?_⟩
  funext s'
  rw [evalHom_combo, ← hc]
  simp [Finsupp.sum, Finset.sum_apply, charVec]

end Emb

section Act

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module ℂ V]

def actHom (ρ : 𝓞 E →+* Module.End ℂ V) : ℂ ⊗[ℤ] 𝓞 E →ₐ[ℂ] Module.End ℂ V :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ρ.toIntAlgHom fun x y => Algebra.commutes x (ρ y)

theorem actHom_tmul (ρ : 𝓞 E →+* Module.End ℂ V) (z : ℂ) (a : 𝓞 E) :
    actHom ρ (z ⊗ₜ a) = z • ρ a := by
  have h := Algebra.TensorProduct.lift_tmul (Algebra.ofId ℂ (Module.End ℂ V)) ρ.toIntAlgHom
    (fun x y => Algebra.commutes x (ρ y)) z a
  simpa [actHom, Algebra.ofId_apply, Algebra.smul_def] using h

theorem actHom_combo (ρ : 𝓞 E →+* Module.End ℂ V) (c : 𝓞 E →₀ ℂ) (x : V) :
    actHom ρ (combo c) x = ∑ a ∈ c.support, c a • ρ a x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [combo, map_sum, actHom_tmul, LinearMap.sum_apply]

theorem mem_eigSp_iff {ρ : 𝓞 E →+* Module.End ℂ V} {s : 𝓞 E →+* ℂ} {x : V} :
    x ∈ eigSp ρ s ↔ ∀ a, ρ a x = s a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem eigComp_eq_combination : ∀ (E : Type) [Field E] [NumberField E] (s₀ : 𝓞 E →+* ℂ), ∃ c : 𝓞 E →₀ ℂ,
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : 𝓞 E →+* Module.End ℂ V),
      (∀ x, eigComp ρ s₀ x = ∑ a ∈ c.support, c a • ρ a x) ∧ (∀ x, eigComp ρ s₀ x ∈ eigSp ρ s₀) ∧
        ∀ x ∈ eigSp ρ s₀, eigComp ρ s₀ x = x := by
  intro E _ _ s₀
  classical
  choose cs hcs using exists_coeff (E := E)
  refine ⟨cs (extEmb s₀), fun V _ _ ρ => ?_⟩
  have hsum : ∑ s, combo (cs s) = 1 := by
    apply evalHom_injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    simp only [hcs]
    funext s'
    simp [Finset.sum_apply, Pi.single_apply]
  have hmul : ∀ (s : E →+* ℂ) (b : 𝓞 E),
      ((1 : ℂ) ⊗ₜ[ℤ] b) * combo (cs s) = s (algebraMap (𝓞 E) E b) • combo (cs s) := by
    intro s b
    apply evalHom_injective
    rw [map_mul, map_smul, hcs]
    funext s'
    by_cases h : s' = s
    · subst h
      simp [evalHom_tmul]
    · simp [evalHom_tmul, Pi.single_apply, h]
  have hsum' : ∀ x, ∑ s, actHom ρ (combo (cs s)) x = x := by
    intro x
    have h := congrArg (actHom ρ) hsum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one] at h
    have h2 := LinearMap.congr_fun h x
    simpa [LinearMap.sum_apply] using h2
  have heig : ∀ (s : E →+* ℂ) x, actHom ρ (combo (cs s)) x ∈ eigSp ρ (s.comp (algebraMap (𝓞 E) E)) := by
    intro s x
    refine mem_eigSp_iff.2 fun b => ?_
    have h := congrArg (actHom ρ) (hmul s b)
    rw [map_mul, map_smul, actHom_tmul, one_smul] at h
    exact LinearMap.congr_fun h x
  have hval : ∀ (s : E →+* ℂ) (σ : 𝓞 E →+* ℂ) x, x ∈ eigSp ρ σ →
      actHom ρ (combo (cs s)) x = (Pi.single s 1 : (E →+* ℂ) → ℂ) (extEmb σ) • x := by
    intro s σ x hx
    rw [actHom_combo, ← hcs s, evalHom_combo, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mem_eigSp_iff.1 hx a, smul_smul, extEmb_apply]
  have hself : ∀ x ∈ eigSp ρ s₀, actHom ρ (combo (cs (extEmb s₀))) x = x := by
    intro x hx
    rw [hval _ s₀ x hx]
    simp
  have hz : ∀ y ∈ ⨆ σ' ∈ {σ' : 𝓞 E →+* ℂ | σ' ≠ s₀}, eigSp ρ σ',
      actHom ρ (combo (cs (extEmb s₀))) y = 0 := by
    have hle : (⨆ σ' ∈ {σ' : 𝓞 E →+* ℂ | σ' ≠ s₀}, eigSp ρ σ') ≤
        LinearMap.ker (actHom ρ (combo (cs (extEmb s₀)))) := by
      refine iSup₂_le fun σ' hσ' y hy => ?_
      rw [LinearMap.mem_ker, hval _ σ' y hy]
      have hne : extEmb σ' ≠ extEmb s₀ := fun h => hσ' (by
        rw [← extEmb_comp σ', h, extEmb_comp])
      simp [Pi.single_apply, hne]
    exact fun y hy => hle hy
  have hex : ∀ x, actHom ρ (combo (cs (extEmb s₀))) x ∈ eigSp ρ s₀ ∧
      x - actHom ρ (combo (cs (extEmb s₀))) x ∈ ⨆ σ' ∈ {σ' : 𝓞 E →+* ℂ | σ' ≠ s₀}, eigSp ρ σ' := by
    intro x
    refine ⟨?_, ?_⟩
    · have h := heig (extEmb s₀) x
      rwa [extEmb_comp] at h
    · have e : x - actHom ρ (combo (cs (extEmb s₀))) x =
          ∑ s ∈ Finset.univ.erase (extEmb s₀), actHom ρ (combo (cs s)) x := by
        have h := hsum' x
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (extEmb s₀))] at h
        exact sub_eq_of_eq_add' h.symm
      rw [e]
      refine Submodule.sum_mem _ fun s hs => ?_
      have hne : s.comp (algebraMap (𝓞 E) E) ≠ s₀ := fun h => (Finset.mem_erase.1 hs).1
        (comp_injective (h.trans (extEmb_comp s₀).symm))
      exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hne (heig s x))
  have hcomp : ∀ x, eigComp ρ s₀ x = actHom ρ (combo (cs (extEmb s₀))) x := by
    intro x
    have h : ∃ p ∈ eigSp ρ s₀, x - p ∈ ⨆ σ' ∈ {σ' : 𝓞 E →+* ℂ | σ' ≠ s₀}, eigSp ρ σ' :=
      ⟨_, (hex x).1, (hex x).2⟩
    unfold eigComp
    rw [dite_eq_left h]
    obtain ⟨h1, h2⟩ := h.choose_spec
    have h3 := hz _ h2
    rw [map_sub, hself _ h1, sub_eq_zero] at h3
    exact h3.symm
  refine ⟨fun x => ?_, fun x => ?_, fun x hx => ?_⟩
  · rw [hcomp, actHom_combo]
  · rw [hcomp]
    exact (hex x).1
  · rw [hcomp, hself x hx]

end Act

end GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomialStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenComponent_polynomial : ∀ (E : Type) [Field E] [NumberField E] (s₀ : 𝓞 E →+* ℂ), ∃ c : 𝓞 E →₀ ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : 𝓞 E →+* Module.End ℂ V), (∀ x, eigComp ρ s₀ x = ∑ a ∈ c.support, c a • ρ a x) ∧ (∀ x, eigComp ρ s₀ x ∈ eigSp ρ s₀) ∧ ∀ x ∈ eigSp ρ s₀, eigComp ρ s₀ x = x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef.eigComp_eq_combination | exact GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef.eigComp_eq_combination | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef.eigComp_eq_combination <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PackingAlt
section -- merged from Development.WeilBound.CoreStatements.RationalSupMetrics.PullRatiosAlgebraic
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackConeNullModPHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackConeNullModPHolds
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem pullConeNullModP : GroundTheory.Heights₂.Heights.HilbertSamuel.PullConeNullModP.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PullConeNullModP.proof

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackConeNullModPHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_cone_null_mod_p_holds : GroundTheory.Heights₂.Heights.HilbertSamuel.PullConeNullModP.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP | exact GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP <;> assumption)
end
end

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel

namespace MultiProjectiveCoordinates

theorem pull_ratios_algebraic : PullRatiosAlgebraic.Statement :=
  PullRatiosAlgebraic.proof PullConeNull.proof PullConeDegree.proof PullGradedAlgebraic.proof

theorem pull_forms_generic : PullFormsGeneric.Statement := PullFormsGeneric.proof pull_ratios_algebraic

theorem fibre_pull_integral : FibreNormPullback.Statement :=
  FibreNormPullback.proof_dehom pull_forms_generic
    (FibreNormDehomCharpoly.proof pull_forms_generic pull_ratios_algebraic PullSectionIntegral.proof
      DehomCharpolyForms.proof)
    (FibreNormDehomIntegral.proof FibreNormBadPrimesFinite.proof
      (FibreNormGoodPrimeIntegral.proof GlobalTheory.T.pullback_cone_null_mod_p_holds PullConeDegreeInt.proof PullSectionIntegralInt.proof
        DehomNormPIntegral.proof)
      (FibreNormPrimeBound.proof pull_forms_generic GlobalTheory.T.norm_form_gauss_bound_holds ChartPrimePowerInverse.proof))
    FibreNormDehomRoots.full

theorem grid_separation : GridSeparation.Statement :=
  GridSeparation.proof NormalLocusRep.proof
    (FibreNormBound.proof (ProjAvoidingForm.proof SegreArith.proof)
      (FibreRepresentatives.proof AvoidFormFinite.proof)
      (FibreNormMax.proof fibre_pull_integral) MetricMaxComparison.proof)
    RootGridLower.proof

end MultiProjectiveCoordinates

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology in
theorem MultiProjectiveCoordinates.packing_statement : PackingStatement :=
  SmallPacking.proof
    (NmSectionsRankBound.proof (NmSectionsFinite.proof (Conductor.proof SecEq.proof)) SecMRankBound.full)
    (SmallSectionsSeparated.proof MultiProjectiveCoordinates.grid_separation)
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem packing : PackingStatement := MultiProjectiveCoordinates.packing_statement

end GlobalTheory.CompanionTheory.Ar.Small
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PlkFlagPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem plk_flagPt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) (k : K), M.IsFrame F → b ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal b) → (∀ τ', IsBlockDiag j (h τ')) → M.blk p = some k → FC.plk M F b (FC.flagPt M F b h) p = minorIJ (h p.1) (stepCols N j p.2) (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F b h p k hF hb hG hh hp
  have hCB := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have hoff : ∀ J, ¬ IsStepRows N j p.2 J → minorIJ (h p.1) J (stepCols N j p.2) = 0 := fun J hJ =>
    (hCB.2.1 (h p.1) J (hh p.1) hJ).resolve_right (CovMap.LocImg.stepCols_ne_empty M.j_le)
  have hI₀ : IsStepRows N j p.2 (stepCols N j p.2) := CovMap.LocImg.FV.isStepRows_stepCols p.2
  have hdelta : ∀ J, IsStepRows N j p.2 J →
      ∑ m : ι k, valAt M.x (F.u' (stepCols N j p.2) ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ J) b =
        if stepCols N j p.2 = J then 1 else 0 := by
    intro J hJ
    have hu' := fun m : ι k => (hG.2.1 ⟨k, m⟩ (stepCols N j p.2)).2
    have hu := fun m : ι k => (hG.2.1 ⟨k, m⟩ J).1
    have e1 := (CovMap.LocImg.reg_sum hb Finset.univ (fun m : ι k => F.u' (stepCols N j p.2) ⟨k, m⟩ * F.u ⟨k, m⟩ J)
      fun m _ => (CovMap.LocImg.reg_mul hb (hu' m) (hu m)).1).2
    rw [hF.2.2.1 p k hp _ J hI₀ hJ] at e1
    rw [Finset.sum_congr rfl fun m _ => ((CovMap.LocImg.reg_mul hb (hu' m) (hu m)).2).symm, ← e1]
    split_ifs
    · exact map_one (CovMap.LocImg.regVal M.x hb)
    · exact map_zero (CovMap.LocImg.regVal M.x hb)
  have e1 : FC.plk M F b (FC.flagPt M F b h) p =
      ∑ J, (∑ m : ι k, valAt M.x (F.u' (stepCols N j p.2) ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ J) b) *
        minorIJ (h p.1) J (stepCols N j p.2) := by
    simp only [FC.plk, hp, Option.elim_some]
    simp_rw [flagPt_step M F b h hp, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [e1, Finset.sum_eq_single (stepCols N j p.2)]
  · rw [hdelta _ hI₀, if_pos rfl, one_mul]
  · intro J _ hne
    by_cases hJ : IsStepRows N j p.2 J
    · rw [hdelta J hJ, if_neg hne.symm, zero_mul]
    · rw [hoff J hJ, mul_zero]
  · simp

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIntPreimageOfOrthogonalKernel
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIntPreimageOfOrthogonalKernel
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.IntegralKernel

theorem exists_clear_denominators {g : ℕ} (w : Fin g → ℚ) :
    ∃ (D : ℤ) (v : Fin g → ℤ), D ≠ 0 ∧ ∀ i, (v i : ℚ) = (D : ℚ) * w i := by
  classical
  have hdvd : ∀ i, ∃ k : ℤ, (∏ j, ((w j).den : ℤ)) = ((w i).den : ℤ) * k := fun i =>
    Finset.dvd_prod_of_mem (fun j => ((w j).den : ℤ)) (Finset.mem_univ i)
  choose k hk using hdvd
  refine ⟨∏ j, ((w j).den : ℤ), fun i => (w i).num * k i, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (w j).den_nz
  · intro i
    rw [hk i]
    push_cast
    have h := Rat.mul_den_eq_num (w i)
    rw [← h]
    ring

theorem cast_mulVec {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) (i : Fin g) :
    (((S *ᵥ v) i : ℤ) : ℚ) = ((S.map (Int.cast : ℤ → ℚ)) *ᵥ (fun j => (v j : ℚ))) i := by
  simp [Matrix.mulVec, dotProduct]

theorem exists_smul_eq_mulVec (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ) (hS : Sᵀ = S)
    (u : Fin g → ℤ) (hu : ∀ v : Fin g → ℤ, S *ᵥ v = 0 → u ⬝ᵥ v = 0) :
    ∃ (N : ℤ) (c : Fin g → ℤ), N ≠ 0 ∧ N • u = S *ᵥ c := by
  classical
  let Sq : Matrix (Fin g) (Fin g) ℚ := S.map (Int.cast : ℤ → ℚ)
  let uq : Fin g → ℚ := fun i => (u i : ℚ)
  have hSq : Sqᵀ = Sq := by
    ext i j
    have := congrFun (congrFun hS i) j
    simp only [Matrix.transpose_apply] at this
    simp [Sq, this]

  have hker : ∀ w : Fin g → ℚ, Sq *ᵥ w = 0 → uq ⬝ᵥ w = 0 := by
    intro w hw
    obtain ⟨D, v, hD, hv⟩ := exists_clear_denominators w
    have hvq : (fun j => (v j : ℚ)) = (D : ℚ) • w := by
      funext j; simp [hv j]
    have hSv : S *ᵥ v = 0 := by
      funext i
      have h1 := cast_mulVec S v i
      rw [hvq, Matrix.mulVec_smul] at h1
      have h2 : (((S *ᵥ v) i : ℤ) : ℚ) = 0 := by
        rw [h1]
        change ((D : ℚ) • (Sq *ᵥ w)) i = 0
        rw [hw]; simp
      exact_mod_cast h2
    have h0 := hu v hSv
    have h1 : ((u ⬝ᵥ v : ℤ) : ℚ) = (D : ℚ) * (uq ⬝ᵥ w) := by
      simp only [dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum, hv, uq]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h0] at h1
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    simpa [hDq] using h1.symm
  let f : (Fin g → ℚ) →ₗ[ℚ] (Fin g → ℚ) := Sq.mulVecLin
  let φ : Module.Dual ℚ (Fin g → ℚ) :=
    { toFun := fun w => uq ⬝ᵥ w
      map_add' := fun a b => dotProduct_add uq a b
      map_smul' := fun r a => by simp [dotProduct_smul] }
  have hφ : φ ∈ LinearMap.range f.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    exact hker w (by simpa [f] using hw)
  obtain ⟨ψ, hψ⟩ := hφ
  let c : Fin g → ℚ := fun i => ψ (Pi.single i 1)
  have hψc : ∀ w, ψ w = c ⬝ᵥ w := by
    intro w
    conv_lhs => rw [pi_eq_sum_univ' w]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, c, dotProduct, mul_comm]
  have hu_eq : uq = Sq *ᵥ c := by
    funext i
    have h1 : φ (Pi.single i 1) = uq i := by
      change uq ⬝ᵥ Pi.single i 1 = uq i
      simp
    have h2 : φ (Pi.single i 1) = ψ (Sq *ᵥ Pi.single i 1) := by
      rw [← hψ]; rfl
    rw [← h1, h2, hψc, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hSq]
    simp
  obtain ⟨D, v, hD, hv⟩ := exists_clear_denominators c
  refine ⟨D, v, hD, ?_⟩
  funext i
  have h1 := cast_mulVec S v i
  have hvq : (fun j => (v j : ℚ)) = (D : ℚ) • c := by
    funext j; simp [hv j]
  rw [hvq, Matrix.mulVec_smul] at h1
  have h2 : (((D • u) i : ℤ) : ℚ) = (((S *ᵥ v) i : ℤ) : ℚ) := by
    rw [h1]
    change _ = ((D : ℚ) • (Sq *ᵥ c)) i
    rw [← hu_eq]
    simp [uq]
  exact_mod_cast h2

end GlobalTheory.CompanionTheory.Ar.IntegralKernel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIntPreimageOfOrthogonalKernelStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_preimage_of_orthogonal_kernel : ∀ (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ), Sᵀ = S → ∀ u : Fin g → ℤ, (∀ v : Fin g → ℤ, S *ᵥ v = 0 → u ⬝ᵥ v = 0) → ∃ (N : ℤ) (c : Fin g → ℤ), N ≠ 0 ∧ N • u = S *ᵥ c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IntegralKernel.exists_smul_eq_mulVec | exact GlobalTheory.CompanionTheory.Ar.IntegralKernel.exists_smul_eq_mulVec | (intros; apply GlobalTheory.CompanionTheory.Ar.IntegralKernel.exists_smul_eq_mulVec <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverTwoFramesComparison
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverTwoFramesComparison
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind

theorem stepCols_nonempty {N j : ℕ} (hj : j ≤ N) (i : Fin N) : (stepCols N j i).Nonempty := by
  by_cases h : (i : ℕ) + 1 ≤ j
  · refine ⟨⟨N - j, by have := i.2; omega⟩, ?_⟩
    simp [stepCols, h]
    omega
  · refine ⟨⟨0, by have := i.2; omega⟩, ?_⟩
    simp [stepCols, h]
    omega

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem coord_ne {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {q : Σ k, ι k}
    (hX : (X q : MRing ι) ∉ mCoordIdeal z) : x q ≠ 0 := by
  intro h
  apply hX
  have h1 : (X q : MRing ι) ∈ mCoordIdeal x := by
    show mConeMap x (X q) = 0
    rw [mConeMap, aeval_X, h, map_zero, zero_mul]
  have h2 := hz.2 _ h1
  have h3 : z q = 0 := by simpa using h2
  show mConeMap z (X q) = 0
  rw [mConeMap, aeval_X, h3, map_zero, zero_mul]

theorem valMat_blockDiag {N j : ℕ} {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x))
    {A : Matrix (Fin N) (Fin N) Ω} (hA : IsBlockDiag j A) : IsBlockDiag j (valMat x z A) := fun a b h => by
  show valAt x (A a b) z = 0
  rw [hA a b h]
  exact map_zero (regVal x hz)

theorem reg_chain {N : ℕ} {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x))
    {A B C : Matrix (Fin N) (Fin N) Ω} (hB : B.det ≠ 0)
    (h₁ : ∀ a b, RegAt x (mCoordIdeal z) ((A⁻¹ * B) a b)) (h₂ : ∀ a b, RegAt x (mCoordIdeal z) ((B⁻¹ * C) a b)) :
    (∀ a b, RegAt x (mCoordIdeal z) ((A⁻¹ * C) a b)) ∧
      valMat x z (A⁻¹ * C) = valMat x z (A⁻¹ * B) * valMat x z (B⁻¹ * C) := by
  have e : A⁻¹ * C = (A⁻¹ * B) * (B⁻¹ * C) := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hB)]
  rw [e]
  exact regMat_mul hz h₁ h₂

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

theorem minor_of_plk (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {b : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : b ∈ mcPts (mCoordIdeal M.x)) (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal b)) {p : Ψ × Fin N} {k : K}
    (hk : M.blk p = some k) {I : Finset (Fin N)} (hI : IsStepRows N j p.2 I) {g : Matrix (Fin N) (Fin N) ℂ}
    (hg : IsBlockDiag j g) :
    ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * plk M F b p.2 ⟨k, m⟩ g = minorIJ g I (stepCols N j p.2) := by
  have hi := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have hz : ∀ I', ¬ IsStepRows N j p.2 I' → minorIJ g I' (stepCols N j p.2) = 0 := fun I' h =>
    (hi.2.1 g I' hg h).resolve_right (stepCols_nonempty M.j_le p.2).ne_empty
  have hv : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ I') b = if I = I' then 1 else 0 := by
    intro I' hI'
    have h1 := hF.2.2.1 p k hk I I' hI hI'
    have h2 := (reg_sum hb Finset.univ (fun m : ι k => F.u' I ⟨k, m⟩ * F.u ⟨k, m⟩ I') fun m _ =>
      ValRing.regAt_mul (hG.2.1 _ _).2 (hG.2.1 _ _).1).2
    rw [h1] at h2
    rw [Finset.sum_congr rfl fun m _ => (reg_mul hb (hG.2.1 _ _).2 (hG.2.1 _ _).1).2.symm, ← h2]
    split_ifs
    · exact map_one (regVal M.x hb)
    · exact map_zero (regVal M.x hb)
  calc ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * plk M F b p.2 ⟨k, m⟩ g
      = ∑ I', (∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ I') b) *
          minorIJ g I' (stepCols N j p.2) := by
        simp only [plk, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
    _ = ∑ I', if I = I' then minorIJ g I' (stepCols N j p.2) else 0 := Finset.sum_congr rfl fun I' _ => by
        by_cases h : IsStepRows N j p.2 I'
        · rw [hv I' h]; split_ifs <;> simp
        · rw [hz I' h]; simp
    _ = minorIJ g I (stepCols N j p.2) := by simp

theorem minor_eq_of_plk (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {b : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : b ∈ mcPts (mCoordIdeal M.x)) (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal b)) {p : Ψ × Fin N} {k : K}
    (hk : M.blk p = some k) {g g₂ : Matrix (Fin N) (Fin N) ℂ} (hg : IsBlockDiag j g) (hg₂ : IsBlockDiag j g₂) {μ : ℂ}
    (h : ∀ m : ι k, plk M F b p.2 ⟨k, m⟩ g = μ * plk M F b p.2 ⟨k, m⟩ g₂) (I : Finset (Fin N)) :
    minorIJ g I (stepCols N j p.2) = μ * minorIJ g₂ I (stepCols N j p.2) := by
  by_cases hI : IsStepRows N j p.2 I
  · rw [← minor_of_plk M hb hF hG hk hI hg, ← minor_of_plk M hb hF hG hk hI hg₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [h m]; ring
  · have hi := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
    have hne := (stepCols_nonempty M.j_le p.2).ne_empty
    rw [(hi.2.1 g I hg hI).resolve_right hne, (hi.2.1 g₂ I hg₂ hI).resolve_right hne, mul_zero]

end SlopeTestRemainingChoices

theorem plk_moved_indep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (b : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F₁' F₂' : FrameData ι' Ψ N M'.Ω M'.blk) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk) (H₁ H₂ : Ψ → Matrix (Fin N) (Fin N) ℂ), b ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F₁' → M'.IsFrame F₂' → M.IsFrame F₁ → M.IsFrame F₂ → M'.GoodAt F₁' (mCoordIdeal b) → M'.GoodAt F₂' (mCoordIdeal b) → M.GoodAt F₁ (mCoordIdeal (b ∘ Cv.v)) → M.GoodAt F₂ (mCoordIdeal (b ∘ Cv.v)) → (∀ τ, IsBlockDiag j (H₁ τ)) → (∀ τ, IsBlockDiag j (H₂ τ)) → (∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k', CovMap.LocImg.plk M' F₁' b p.2 ⟨k', m'⟩ (H₁ p.1) = a * CovMap.LocImg.plk M' F₂' b p.2 ⟨k', m'⟩ (H₂ p.1)) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, CovMap.LocImg.plk M F₁ (b ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F₁' F₁ b p.1 * H₁ p.1) = a * CovMap.LocImg.plk M F₂ (b ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F₂' F₂ b p.1 * H₂ p.1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv b F₁' F₂' F₁ F₂ H₁ H₂ hb hF₁' hF₂' hF₁ hF₂ hG₁' hG₂' hG₁ hG₂
    hH₁ hH₂ hyp p k hk
  obtain ⟨k', hk'⟩ := exists_blk_cover M' hk
  obtain ⟨hbv, hpt⟩ := GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv b hb
  have hi := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have dT₁' := (hF₁'.1 p.1).2
  have dP : ∀ F : FrameData ι Ψ N M.Ω M.blk, M.IsFrame F → ((F.T p.1).map Cv.φ).det ≠ 0 := fun F hF => by
    have e : ((F.T p.1).map Cv.φ).det = Cv.φ (F.T p.1).det := (RingHom.map_det Cv.φ (F.T p.1)).symm
    rw [e]
    exact (map_ne_zero Cv.φ).2 (hF.1 p.1).2
  have r₁₁ := fun a c => Cv.agree b hb F₁' F₁ hF₁' hF₁ hG₁' hG₁ p.1 a c
  have r₁₂ := fun a c => Cv.agree b hb F₁' F₂ hF₁' hF₂ hG₁' hG₂ p.1 a c
  have r₂₁ := fun a c => Cv.agree b hb F₂' F₁ hF₂' hF₁ hG₂' hG₁ p.1 a c
  have r₂₂ := fun a c => Cv.agree b hb F₂' F₂ hF₂' hF₂ hG₂' hG₂ p.1 a c
  have c₁ := reg_chain hb (dP F₁ hF₁) (fun a c => (r₁₁ a c).2) (fun a c => (r₂₁ a c).1)
  have c₂ := reg_chain hb (dP F₁ hF₁) (fun a c => (r₂₁ a c).2) (fun a c => (r₁₁ a c).1)
  have c₃ := reg_chain hb dT₁' (fun a c => (r₁₁ a c).1) (fun a c => (r₁₂ a c).2)
  have c₄ := reg_chain hb dT₁' (fun a c => (r₁₂ a c).1) (fun a c => (r₁₁ a c).2)
  have c₅ := reg_chain hb dT₁' (fun a c => (r₁₁ a c).1) c₁.1
  have c₆ := reg_chain hb (dP F₂ hF₂) c₃.1 (fun a c => (r₂₂ a c).1)

  have eid : ∀ A : Matrix (Fin N) (Fin N) M'.Ω, A.map (RingHom.id M'.Ω) = A := fun A => by ext; rfl
  obtain ⟨c', hc'0, hc'⟩ := GlobalTheory.T.frame_change_under_field_map K' ι' Φ' y' Ψ N j M' (NonPluckerBlocks M'.blk) (baseIdx ι' M'.blk) M'.Ω M'.x
    (RingHom.id _) b F₁' F₂' hb hF₁' hF₂' (fun k => coord_ne hb (hG₁'.1 k)) (fun k => coord_ne hb (hG₂'.1 k)) p k' hk'
    (fun m I => ⟨(hG₁'.2.1 _ _).1, (hG₂'.2.1 _ _).1, (hG₁'.2.1 _ _).2, (hG₂'.2.1 _ _).2⟩)
    (fun a c => by simp only [eid]; exact ⟨c₁.1 a c, c₂.1 a c⟩)
  simp only [eid, RingHom.id_apply] at hc'
  obtain ⟨a, ha0, hA⟩ := hyp p k' hk'
  obtain ⟨S', hS'⟩ : ∃ S', S' = valMat M'.x b ((F₁'.T p.1)⁻¹ * F₂'.T p.1) := ⟨_, rfl⟩
  rw [← hS'] at hc'
  have bdS' : IsBlockDiag j S' := hS' ▸ valMat_blockDiag hb
    (((hF₁'.1 p.1).1.inv (isUnit_iff_ne_zero.2 dT₁')).mul (hF₂'.1 p.1).1)
  obtain ⟨μ, hμd⟩ : ∃ μ, μ = c' * a⁻¹ := ⟨_, rfl⟩
  have hμ : μ ≠ 0 := hμd ▸ mul_ne_zero hc'0 (inv_ne_zero ha0)
  have e₁ : ∀ m : ι' k', plk M' F₁' b p.2 ⟨k', m⟩ (S' * H₂ p.1) = μ * plk M' F₁' b p.2 ⟨k', m⟩ (H₁ p.1) := fun m => by
    rw [hA m, hμd, ← mul_assoc, mul_assoc c', inv_mul_cancel₀ ha0, mul_one]
    exact hc' (H₂ p.1) (hH₂ p.1) m
  have e₂ := minor_eq_of_plk M' hb hF₁' hG₁' hk' (bdS'.mul (hH₂ p.1)) (hH₁ p.1) e₁

  obtain ⟨S, hS⟩ : ∃ S, S = valMat M'.x b (((F₁.T p.1).map Cv.φ)⁻¹ * (F₂.T p.1).map Cv.φ) := ⟨_, rfl⟩
  have eT : Cv.trans F₁' F₁ b p.1 * S' = S * Cv.trans F₂' F₂ b p.1 := by
    rw [hS', hS]
    exact c₅.2.symm.trans c₆.2
  have e₃ : ∀ I, minorIJ (Cv.trans F₁' F₁ b p.1 * H₁ p.1) I (stepCols N j p.2) =
      μ⁻¹ * minorIJ (S * (Cv.trans F₂' F₂ b p.1 * H₂ p.1)) I (stepCols N j p.2) := fun I => by
    rw [← Matrix.mul_assoc S, ← eT, Matrix.mul_assoc, hi.1 _ (S' * H₂ p.1), hi.1 _ (H₁ p.1), Finset.mul_sum]
    refine Finset.sum_congr rfl fun I' _ => ?_
    rw [e₂ I']
    field_simp

  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.frame_change_under_field_map K ι Φ y Ψ N j M (NonPluckerBlocks M'.blk) (baseIdx ι' M'.blk) M'.Ω M'.x Cv.φ b F₁ F₂
    hb hF₁ hF₂ (fun k => coord_ne hbv (hG₁.1 k)) (fun k => coord_ne hbv (hG₂.1 k)) p k hk
    (fun m I => ⟨(hpt _ (hG₁.2.1 _ _).1).1, (hpt _ (hG₂.2.1 _ _).1).1, (hpt _ (hG₁.2.1 _ _).2).1,
      (hpt _ (hG₂.2.1 _ _).2).1⟩)
    (fun a c => ⟨c₃.1 a c, c₄.1 a c⟩)
  rw [← hS] at hc
  have bdT₂ := (GlobalTheory.T.flag_cover_frame_compatibility K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv b F₂' F₂ hb hF₂' hF₂ hG₂' hG₂ p.1).1
  have hval : ∀ F : FrameData ι Ψ N M.Ω M.blk, M.GoodAt F (mCoordIdeal (b ∘ Cv.v)) → ∀ q I,
      valAt M'.x (Cv.φ (F.u q I)) b = valAt M.x (F.u q I) (b ∘ Cv.v) := fun F hG q I => (hpt _ (hG.2.1 q I).1).2
  refine ⟨μ⁻¹ * c, mul_ne_zero (inv_ne_zero hμ) hc0, fun m => ?_⟩
  have h3 := hc (Cv.trans F₂' F₂ b p.1 * H₂ p.1) (bdT₂.mul (hH₂ p.1)) m
  simp only [hval F₁ hG₁, hval F₂ hG₂] at h3
  simp only [plk]
  calc ∑ I, valAt M.x (F₁.u ⟨k, m⟩ I) (b ∘ Cv.v) *
        minorIJ (Cv.trans F₁' F₁ b p.1 * H₁ p.1) I (stepCols N j p.2)
      = μ⁻¹ * ∑ I, valAt M.x (F₁.u ⟨k, m⟩ I) (b ∘ Cv.v) *
        minorIJ (S * (Cv.trans F₂' F₂ b p.1 * H₂ p.1)) I (stepCols N j p.2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun I _ => by rw [e₃ I]; ring
    _ = _ := by rw [h3, mul_assoc]

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverTwoFramesComparisonStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_two_frames_comparison : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (b : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F₁' F₂' : FrameData ι' Ψ N M'.Ω M'.blk) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk) (H₁ H₂ : Ψ → Matrix (Fin N) (Fin N) ℂ), b ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F₁' → M'.IsFrame F₂' → M.IsFrame F₁ → M.IsFrame F₂ → M'.GoodAt F₁' (mCoordIdeal b) → M'.GoodAt F₂' (mCoordIdeal b) → M.GoodAt F₁ (mCoordIdeal (b ∘ Cv.v)) → M.GoodAt F₂ (mCoordIdeal (b ∘ Cv.v)) → (∀ τ, IsBlockDiag j (H₁ τ)) → (∀ τ, IsBlockDiag j (H₂ τ)) → (∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k', CovMap.LocImg.plk M' F₁' b p.2 ⟨k', m'⟩ (H₁ p.1) = a * CovMap.LocImg.plk M' F₂' b p.2 ⟨k', m'⟩ (H₂ p.1)) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, CovMap.LocImg.plk M F₁ (b ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F₁' F₁ b p.1 * H₁ p.1) = a * CovMap.LocImg.plk M F₂ (b ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F₂' F₂ b p.1 * H₂ p.1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind.plk_moved_indep | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind.plk_moved_indep | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind.plk_moved_indep <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsKerProj
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem exists_isKerProj (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ) :
    ∃ Pr : Matrix (Fin g) (Fin g) ℝ, IsKerProj S Pr := by
  classical
  set M : Matrix (Fin g) (Fin g) ℝ := S.map (fun x : ℤ => (x : ℝ)) with hM
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin g)) := LinearMap.ker (Matrix.toEuclideanLin M)
  let P : EuclideanSpace ℝ (Fin g) →ₗ[ℝ] EuclideanSpace ℝ (Fin g) :=
    (K.starProjection : EuclideanSpace ℝ (Fin g) →ₗ[ℝ] EuclideanSpace ℝ (Fin g))
  let Pr : Matrix (Fin g) (Fin g) ℝ := Matrix.toEuclideanLin.symm P
  have hPr : Matrix.toEuclideanLin Pr = P := LinearEquiv.apply_symm_apply _ _
  have hmv : ∀ v : Fin g → ℝ, Pr *ᵥ v = WithLp.ofLp (P (WithLp.toLp 2 v)) := by
    intro v
    rw [← hPr, Matrix.toLpLin_apply]
  have hidem : ∀ x, P (P x) = P x := by
    intro x
    have hx : K.starProjection x ∈ K := Submodule.starProjection_apply_mem K x
    exact (Submodule.starProjection_eq_self_iff).2 hx
  refine ⟨Pr, ?_, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hmv, hmv,
      WithLp.toLp_ofLp, hidem]
  · have hs : Pr.IsHermitian := by
      apply Matrix.isSymmetric_toEuclideanLin_iff.mp
      rw [hPr]
      exact Submodule.starProjection_isSymmetric K
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hs.eq
  · intro v
    rw [hmv]
    constructor
    · intro h
      have hk : WithLp.toLp 2 v ∈ K := by
        have h' : M *ᵥ v = 0 := h
        rw [LinearMap.mem_ker, Matrix.toLpLin_apply]
        simp [h']
      have : P (WithLp.toLp 2 v) = WithLp.toLp 2 v := (Submodule.starProjection_eq_self_iff).2 hk
      rw [this]
    · intro h
      have h1 : P (WithLp.toLp 2 v) = WithLp.toLp 2 v := by
        rw [← WithLp.toLp_ofLp (p := 2) (P (WithLp.toLp 2 v)), h]
      have hk : WithLp.toLp 2 v ∈ K := (Submodule.starProjection_eq_self_iff).1 h1
      rw [LinearMap.mem_ker, Matrix.toLpLin_apply] at hk
      have h' : M *ᵥ v = 0 := by simpa using hk
      exact h'

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
end
