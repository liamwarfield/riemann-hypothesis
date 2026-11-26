module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueScaleIsScaleStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
open Formalism.BasicNotions Formalism.L2.Theta Formalism.IndefR.Datum

namespace GlobalTheory.Member

theorem exists_isInfFam_family : ∀ D : D7, ∃ θ : InfFam D, IsInfFam θ :=
  fun D => GlobalTheory.DualPairCompare.exists_infFam D

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionUnramifiedNormal
open IsLocalRing

namespace GlobalTheory.EtaleCompletionNormal

theorem formallyUnramified_of_map_maximalIdeal {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R (ResidueField S)]
    (H : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    Algebra.FormallyUnramified R S := by
  constructor
  rw [← IsLocalRing.subsingleton_tensorProduct (R := S)]
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨x, rfl⟩ := (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R S
    (ResidueField S) Ideal.Quotient.mk_surjective x).mp (Subsingleton.elim _ _)
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  simp only [KaehlerDifferential.kerCotangentToTensor_toCotangent]
  replace hx : x ∈ Ideal.map (algebraMap R S) (maximalIdeal R) := by simpa [H] using hx
  induction hx using Submodule.span_induction with
  | zero => simp
  | mem x h => obtain ⟨x, hx, rfl⟩ := h; simp
  | add x y hx hy _ _ => simp [*, TensorProduct.tmul_add]
  | smul a x hx _ =>
    have : residue S x = 0 := by rwa [residue_eq_zero_iff, ← H]
    simp [*, TensorProduct.tmul_add, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]

theorem isDomain_and_isIntegrallyClosed : ∀ (D E : Type) [CommRing D] [IsDomain D] [IsLocalRing D] [CommRing E] [IsLocalRing E] (h : D →+* E), IsNoetherianRing D → IsDomain (AdicCompletion (IsLocalRing.maximalIdeal D) D) → IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal D) D) → IsNoetherianRing E → IsAdicComplete (IsLocalRing.maximalIdeal E) E → IsLocalHom h → GlobalTheory.Toroidal.IsEtaleCompletion h → ((IsLocalRing.residue E).comp h).FormallyUnramified → IsDomain E ∧ IsIntegrallyClosed E := by
  intro D E _ _ _ _ _ h hD hAd hAi hE hEc _ het hfu
  obtain ⟨hflat, hmap, hfin⟩ := het
  haveI := hD; haveI := hE; haveI := hEc; haveI := hAd; haveI := hAi
  let A := AdicCompletion (maximalIdeal D) D
  haveI : IsNoetherianRing A := AdicNoeth.isNoetherianRing_adicCompletion D _
  haveI : IsAdicComplete ((maximalIdeal D).map h) E := by rw [hmap]; exact hEc
  obtain ⟨g, hg⟩ := exists_adicCompletion_ringHom_extend (maximalIdeal D) h
  letI : Algebra A E := g.toAlgebra
  have hgA : ∀ a, g (algebraMap D A a) = h a := fun a => RingHom.congr_fun hg a
  have hmA : (maximalIdeal A).map (algebraMap A E) = maximalIdeal E := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map]
    change (maximalIdeal D).map (g.comp _) = _
    rw [hg, hmap]
  haveI : IsLocalHom (algebraMap A E) := ((local_hom_tfae _).out 1 3).mpr hmA.le

  have hres : ((residue E).comp g).Finite :=
    RingHom.Finite.of_comp_finite (f := algebraMap D A) (by rw [RingHom.comp_assoc, hg]; exact hfin)
  haveI : Module.Finite A (E ⧸ (maximalIdeal A).map (algebraMap A E)) := by
    rw [← RingHom.finite_algebraMap]
    show ((Ideal.Quotient.mk _).comp (algebraMap A E)).Finite
    rw [hmA]
    exact hres
  haveI : IsHausdorff ((maximalIdeal A).map (algebraMap A E)) E := by rw [hmA]; infer_instance
  haveI : Module.Finite A E := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)

  haveI : Module.Flat A E := by
    refine LocalFlat.flat_of_relationsLift E (I := maximalIdeal A)
      (hmA.le.trans (maximalIdeal_le_jacobson _)) fun n => ?_
    letI : Algebra D E := h.toAlgebra
    haveI : Module.Flat D E := hflat
    have fg := (maximalIdeal D).fg_of_isNoetherianRing
    have hkerA : ∀ x : A, AdicCompletion.evalₐ (maximalIdeal D) n x = 0 ↔ x ∈ maximalIdeal A ^ n := by
      intro x
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem D,
        ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval fg, LinearMap.mem_ker]
      constructor
      · intro h0
        rw [← AdicCompletion.factor_evalₐ_eq_eval _ x (by simp), h0, map_zero]
      · intro h0
        rw [← AdicCompletion.factor_eval_eq_evalₐ _ x (by simp), h0, map_zero]
    have hmapn : (maximalIdeal A ^ n).map (algebraMap A E) = (maximalIdeal D ^ n).map (algebraMap D E) := by
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.map_map]
      change (maximalIdeal D ^ n).map (g.comp _) = _
      rw [hg]
      rfl
    refine LocalFlat.relationsLift_of_square
      (AdicCompletion.evalₐ (maximalIdeal D) n).toRingHom
      (Ideal.Quotient.mk ((maximalIdeal D ^ n).map (algebraMap D E)))
      (algebraMap _ _) (AdicCompletion.surjective_evalₐ _ n) Ideal.Quotient.mk_surjective ?_ ?_ ?_ ?_
    · ext x
      exact (hkerA x)
    · rw [Ideal.mk_ker, hmapn]
    · ext x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal D) n x)
      have hx : x - algebraMap D A a ∈ maximalIdeal A ^ n := by
        rw [← hkerA, map_sub, ← ha, AlgHom.commutes, sub_eq_zero]
        rfl
      have hx' : algebraMap A E x - h a ∈ (maximalIdeal D ^ n).map (algebraMap D E) := by
        rw [← hmapn, ← hgA]
        rw [show algebraMap A E x - g (algebraMap D A a) = algebraMap A E (x - algebraMap D A a) from
          (map_sub g _ _).symm]
        exact Ideal.mem_map_of_mem _ hx
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← ha]
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient, eq_comm, Ideal.Quotient.eq]
      exact hx'
    · rw [RingHom.flat_algebraMap_iff]
      exact Module.Flat.of_linearEquiv
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor E (maximalIdeal D ^ n)).toLinearEquiv

  haveI : Algebra.FormallyUnramified A (ResidueField E) := by
    rw [← RingHom.formallyUnramified_algebraMap]
    have e : (algebraMap A (ResidueField E)).comp (algebraMap D A) = (residue E).comp h := by
      rw [← hg]; rfl
    exact RingHom.FormallyUnramified.of_comp (f := algebraMap D A) (by rw [e]; exact hfu)
  haveI : Algebra.FormallyUnramified A E := formallyUnramified_of_map_maximalIdeal hmA
  haveI : Algebra.FinitePresentation A E :=
    (Algebra.FinitePresentation.of_finiteType (R := A) (A := E)).1 inferInstance
  haveI : Algebra.Etale A E := Algebra.Etale.of_formallyUnramified_of_flat
  haveI : IsLocalization.AtPrime E (maximalIdeal E) :=
    IsLocalization.self fun a ha => by_contra fun h' => ha h'
  exact isDomain_and_isIntegrallyClosed_atPrime_of_etale A (maximalIdeal E) E

end GlobalTheory.EtaleCompletionNormal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeNotMemOfMemQE
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV

theorem _root_.GlobalTheory.Mem.Col2.T_notMem_QE : ∀ {X : _root_.Formalism.L2.Col.Fields} {Pr : _root_.Formalism.L2.Col.Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : _root_.Formalism.L2.DIV.Tup X.F X.E X.K S) (u : Pr.Word), Pr.Ok → _root_.Formalism.L2.Col.IsSel X sel → Pr.T u ∈ S →
      ∀ w ∈ _root_.Formalism.L2.Col.QE sel (mu : _root_.Formalism.L2.DIV.Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal := by
  classical
  intro X Pr sel S mu u hOk hsel hT w hw hmem
  unfold _root_.Formalism.L2.Col.QE at hw
  split_ifs at hw with hfin
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    rw [Set.Finite.mem_toFinset] at hv
    have hmu := mu.2
    unfold _root_.Formalism.L2.DIV.tupGrp at hmu
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf] at hmu
    have hA : _root_.Formalism.L2.DIV.GoodPl X.E S v := by
      by_contra hA
      exact hv (hmu.2 v hA)
    have hchar : _root_.Formalism.EigenvalueLevelCeiling.plc v ∉ S := by
      unfold _root_.Formalism.L2.DIV.GoodPl at hA
      exact hA.2.2
    have hv' : ((Pr.T u : ℕ) : 𝓞 X.F) ∈ v.asIdeal := by
      rw [← hsel v, Ideal.mem_comap]
      simpa using hmem
    have hp := hOk.T_prime u
    have hzero : ((Pr.T u : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hv'
    have : Nontrivial (𝓞 X.F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
    have hdvd : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ Pr.T u := (ringChar.spec _ _).mp hzero
    have heq : ringChar (𝓞 X.F ⧸ v.asIdeal) = Pr.T u :=
      ((Nat.dvd_prime hp).mp hdvd).resolve_left CharP.ringChar_ne_one
    apply hchar
    unfold _root_.Formalism.EigenvalueLevelCeiling.plc
    rw [heq]
    exact hT
  · simp at hw

end GlobalTheory.Mem.Col2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDensityUpqUniqueAndSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaLebUnique
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.OmegaLebUnique

theorem omegaLeb_unique :
    ∀ (P Q : ℕ) (l l' : Measure (lieU P Q)), IsOmegaLeb l → IsOmegaLeb l' → l = l' :=
  fun _ _ _ _ h h' => GlobalTheory.CompactDualUnique.isOmegaLeb_unique h h'

end GlobalTheory.OmegaLebUnique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDensityUpqUniqueAndSmul
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.OmegaDensityScale

theorem omegaDensity_unique {P Q : ℕ} {μ : Measure (UpqT P Q)} {c c' : ENNReal}
    (h : OmegaDensity μ c) (h' : OmegaDensity μ c') : c' = c := by
  obtain ⟨l, hl, ht⟩ := h
  obtain ⟨l', hl', ht'⟩ := h'
  have e : l = l' := GlobalTheory.OmegaLebUnique.omegaLeb_unique P Q l l' hl hl'
  subst e
  exact tendsto_nhds_unique ht' ht

theorem omegaDensity_smul {P Q : ℕ} {μ : Measure (UpqT P Q)} {c : ENNReal}
    (h : OmegaDensity μ c) (a : NNReal) : OmegaDensity ((a : ENNReal) • μ) (a * c) := by
  obtain ⟨l, hl, ht⟩ := h
  refine ⟨l, hl, ?_⟩
  have h2 := ENNReal.Tendsto.const_mul (a := (a : ENNReal)) ht (Or.inr ENNReal.coe_ne_top)
  refine h2.congr fun r => ?_
  rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]

theorem omegaDensity_unique_and_smul : ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)) (c : ENNReal),
    OmegaDensity μ c → (∀ c', OmegaDensity μ c' → c' = c) ∧
      ∀ a : NNReal, OmegaDensity ((a : ENNReal) • μ) (a * c) :=
  fun _ _ _ _ h => ⟨fun _ h' => omegaDensity_unique h h', fun a => omegaDensity_smul h a⟩

end GlobalTheory.OmegaDensityScale
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDensityUpqUniqueAndSmulStatement
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omegaDensity_upq_unique_and_smul : ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)) (c : ENNReal), OmegaDensity μ c → (∀ c', OmegaDensity μ c' → c' = c) ∧ ∀ a : NNReal, OmegaDensity ((a : ENNReal) • μ) (a * c) := by
  first | exact @GlobalTheory.OmegaDensityScale.omegaDensity_unique_and_smul | exact GlobalTheory.OmegaDensityScale.omegaDensity_unique_and_smul | (intros; apply GlobalTheory.OmegaDensityScale.omegaDensity_unique_and_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiscreteSeriesFormalDegreeProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiscreteSeriesFormalDegreeProduct
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem fdegOf_eq_of_isFdeg {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} (μ : Measure (Formalism.REAL.UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ)
    (h : IsFdeg μ σ d) (w : H) (hw : w ≠ 0) : fdegOf μ σ w = d := by
  obtain ⟨hd, h⟩ := h
  have h2 := (h w w w w).2
  have e1 : (fun g : Formalism.REAL.UJ ε => coefOn σ w w g * star (coefOn σ w w g)) =
      fun g => (((‖coefOn σ w w g‖ ^ 2 : ℝ)) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e1, integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at h2
  have h3 : ∫ g : Formalism.REAL.UJ ε, ‖coefOn σ w w g‖ ^ 2 ∂μ = ‖w‖ ^ 4 / d := by
    apply Complex.ofReal_injective
    rw [h2]
    push_cast
    simp only [RCLike.ofReal, Complex.coe_algebraMap]
    ring
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  unfold fdegOf
  rw [h3]
  field_simp

theorem exists_isDS_isFdeg_trueDsig : DiscreteSeriesExist → FormalDegreeFormula₂ → ∀ (cd : CDHaar) (R : Ranks) (P : HCParam R), (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)), IsDS (epsSH R) (lamSH R P) σ ∧ IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ (trueDsig R P)) ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)) (d : ℝ), IsDS (epsSH R) (lamSH R P) σ → IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ d → d = trueDsig R P := by
  intro hE hF cd R P
  have hpar := (GlobalTheory.T.rowHCParameter_isHCParam_and_formalDegree_pos R P).1
  have key : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)) (d : ℝ), IsDS (epsSH R) (lamSH R P) σ → IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ d → d = trueDsig R P := by
    intro H _ _ σ d hσ hd
    have : Nontrivial H := hσ.2.1
    obtain ⟨w, hw⟩ := exists_ne (0 : H)
    rw [← fdegOf_eq_of_isFdeg _ σ d hd w hw]
    exact hF cd (trueScale cd) (GlobalTheory.T.cdScaleIs_trueScale' cd) _ (epsSH R) (lamSH R P) hpar H σ w hσ hw
  refine ⟨?_, key⟩
  obtain ⟨H, i1, i2, σ, hσ⟩ := hE _ (epsSH R) (lamSH R P) hpar
  obtain ⟨d, hd⟩ := exists_isFdeg_smul_of_isDS _ (epsSH R) (lamSH R P) H σ hσ _ (trueScale_pos cd _ (epsSH R))
  refine ⟨H, i1, i2, σ, hσ, ?_⟩
  rw [← key H σ d hσ hd]
  exact hd

end GlobalTheory.Mem.Vol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiscreteSeriesFormalDegreeProductStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_discreteSeries_formalDegree_product : DiscreteSeriesExist → FormalDegreeFormula₂ → ∀ (cd : CDHaar) (R : Ranks) (P : HCParam R), (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)), IsDS (epsSH R) (lamSH R P) σ ∧ IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ (trueDsig R P)) ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)) (d : ℝ), IsDS (epsSH R) (lamSH R P) σ → IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ d → d = trueDsig R P := by
  first | exact @GlobalTheory.Mem.Vol.exists_isDS_isFdeg_trueDsig | exact GlobalTheory.Mem.Vol.exists_isDS_isFdeg_trueDsig | (intros; apply GlobalTheory.Mem.Vol.exists_isDS_isFdeg_trueDsig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsNormModEqOneOfPrincipalRayClass
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsNormModEqOneOfPrincipalRayClass
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.RayNorm

theorem int_norm_pos (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {x : 𝓞 K} (hx : x ≠ 0) :
    0 < Algebra.norm ℤ x := by
  classical
  have hx' : (x : K) ≠ 0 := by exact_mod_cast hx

  have fibre : ∀ w : InfinitePlace K,
      ∏ φ ∈ (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w), φ (x : K) =
        ((Complex.normSq (w.embedding (x : K)) : ℝ) : ℂ) := by
    intro w
    have hset : (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w) =
        {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      have key := InfinitePlace.mk_eq_iff (φ := φ) (ψ := w.embedding)
      rw [InfinitePlace.mk_embedding] at key
      rw [key]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · right; rw [← h]; exact (star_star φ).symm
      · rintro (h | h)
        · exact Or.inl h
        · right; rw [h]; exact star_star w.embedding
    have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
      intro h
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w))
        (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h.symm))
    rw [hset, Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj]
  have hprod : (algebraMap ℚ ℂ) (Algebra.norm ℚ (x : K)) =
      ((∏ w : InfinitePlace K, Complex.normSq (w.embedding (x : K)) : ℝ) : ℂ) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ (x : K)]
    rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ (x : K)) _
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])]
    rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => φ (x : K))]
    push_cast
    exact Finset.prod_congr rfl (fun w _ => fibre w)
  have hpos : (0 : ℝ) < ∏ w : InfinitePlace K, Complex.normSq (w.embedding (x : K)) :=
    Finset.prod_pos fun w _ => Complex.normSq_pos.mpr ((map_ne_zero _).mpr hx')
  have hreal : ((Algebra.norm ℚ (x : K) : ℚ) : ℝ) =
      ∏ w : InfinitePlace K, Complex.normSq (w.embedding (x : K)) := by
    apply Complex.ofReal_injective
    rw [← hprod]
    simp
  have hq : (0 : ℚ) < Algebra.norm ℚ (x : K) := by
    have := hreal ▸ hpos
    exact_mod_cast this
  rw [← Algebra.coe_norm_int] at hq
  exact_mod_cast hq

theorem norm_cast_eq (K : Type) [Field K] [NumberField K] (p : ℕ) {x y : 𝓞 K}
    (h : x - y ∈ Ideal.span {(p : 𝓞 K)}) :
    ((Algebra.norm ℤ x : ℤ) : ZMod p) = ((Algebra.norm ℤ y : ℤ) : ZMod p) := by
  classical
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp h
  have hx : x = y + (p : 𝓞 K) * z := by rw [mul_comm, hz]; ring
  let b := RingOfIntegers.basis K
  have h0 : (Int.castRingHom (ZMod p)).mapMatrix (Algebra.leftMulMatrix b (p : 𝓞 K)) = 0 := by
    rw [map_natCast, map_natCast]
    ext i j
    simp
  have hmat : (Int.castRingHom (ZMod p)).mapMatrix (Algebra.leftMulMatrix b x) =
      (Int.castRingHom (ZMod p)).mapMatrix (Algebra.leftMulMatrix b y) := by
    rw [hx, map_add (f := _), map_mul, map_add (f := _), map_mul, h0, zero_mul, add_zero]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b]
  have e1 := RingHom.map_det (Int.castRingHom (ZMod p)) (Algebra.leftMulMatrix b x)
  have e2 := RingHom.map_det (Int.castRingHom (ZMod p)) (Algebra.leftMulMatrix b y)
  simp only [eq_intCast] at e1 e2
  rw [e1, e2, hmat]

theorem absNorm_modEq_one : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (𝔮 : Ideal (𝓞 K)) (p : ℕ), 𝔮 ≤ Ideal.span {(p : 𝓞 K)} → ∀ (I : Ideal (𝓞 K)) (α β : 𝓞 K), RayPair 𝔮 α β → I * Ideal.span {β} = Ideal.span {α} → Ideal.absNorm I ≡ 1 [MOD p] := by
  intro K _ _ _ 𝔮 p h𝔮 I α β hR hI
  unfold GlobalTheory.NT.RayPair at hR
  obtain ⟨hα, hβ, -, hβq, hαβ, -⟩ := hR

  have hnorm : (Ideal.absNorm I : ℤ) * Algebra.norm ℤ β = Algebra.norm ℤ α := by
    have e := congrArg Ideal.absNorm hI
    rw [map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at e
    have e' : ((Ideal.absNorm I * (Algebra.norm ℤ β).natAbs : ℕ) : ℤ) =
        ((Algebra.norm ℤ α).natAbs : ℤ) := by rw [e]
    push_cast at e'
    rwa [abs_of_pos (int_norm_pos K hβ), abs_of_pos (int_norm_pos K hα)] at e'

  have htop : Ideal.span {β} ⊔ Ideal.span {(p : 𝓞 K)} = ⊤ := by
    rw [Ideal.isCoprime_iff_sup_eq] at hβq
    exact eq_top_mono (sup_le_sup_left h𝔮 _) hβq
  have h1 : (1 : 𝓞 K) ∈ Ideal.span {β} ⊔ Ideal.span {(p : 𝓞 K)} := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp h1
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  have hu : β * u - 1 ∈ Ideal.span {(p : 𝓞 K)} := by
    have e : β * u - 1 = -c := by rw [← hac]; ring
    rw [e]; exact neg_mem hc
  have hinv := norm_cast_eq K p hu
  rw [map_mul, map_one] at hinv
  push_cast at hinv
  have hmod := norm_cast_eq K p (h𝔮 hαβ)
  have key : ((Ideal.absNorm I : ℕ) : ZMod p) * ((Algebra.norm ℤ β : ℤ) : ZMod p) =
      ((Algebra.norm ℤ β : ℤ) : ZMod p) := by
    have e := congrArg (fun t : ℤ => (t : ZMod p)) hnorm
    push_cast at e
    rw [e, hmod]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [Nat.cast_one]
  linear_combination (1 - ((Ideal.absNorm I : ℕ) : ZMod p)) * hinv +
    ((Algebra.norm ℤ u : ℤ) : ZMod p) * key

end GlobalTheory.Mem.RayNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsNormModEqOneOfPrincipalRayClassStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absNorm_modEq_one_of_principal_rayClass : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (𝔮 : Ideal (𝓞 K)) (p : ℕ), 𝔮 ≤ Ideal.span {(p : 𝓞 K)} → ∀ (I : Ideal (𝓞 K)) (α β : 𝓞 K), RayPair 𝔮 α β → I * Ideal.span {β} = Ideal.span {α} → Ideal.absNorm I ≡ 1 [MOD p] := by
  first | exact @GlobalTheory.Mem.RayNorm.absNorm_modEq_one | exact GlobalTheory.Mem.RayNorm.absNorm_modEq_one | (intros; apply GlobalTheory.Mem.RayNorm.absNorm_modEq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldFinrankPowPrincipal
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldFinrankPowPrincipal
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld.RayExp

variable {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem heckeIdeal_pow (χ : (L ≃ₐ[K] L) →* ℂˣ) {I : Ideal (𝓞 K)} (hI : I ≠ 0) (n : ℕ) :
    heckeIdeal L χ (I ^ n) = heckeIdeal L χ I ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, GlobalTheory.NT.Model.heckeIdeal_top]
  | succ n ih => rw [pow_succ, pow_succ, GlobalTheory.NT.Model.heckeIdeal_mul L χ (pow_ne_zero n hI) hI, ih]

theorem heckeIdeal_pow_finrank [IsGalois K L] (χ : (L ≃ₐ[K] L) →* ℂˣ) {𝔮 : Ideal (𝓞 K)}
    (hun : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 → UnramIn L 𝔭) (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hc : IsCoprime I 𝔮) : heckeIdeal L χ I ^ Module.finrank K L = 1 := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ x hx => rw [isUnit_iff_eq_one.1 hx, GlobalTheory.NT.Model.heckeIdeal_top, one_pow]
  | h₃ a p ha hpp ih =>
    let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨p, Ideal.isPrime_of_prime hpp, hpp.ne_zero⟩
    have hnd : ¬ 𝔭.asIdeal ∣ 𝔮 := fun hd =>
      hpp.not_unit (hc.of_mul_left_left.isUnit_of_dvd' dvd_rfl hd)
    obtain ⟨σ, hσ⟩ := GlobalTheory.NT.exists_isFrob L 𝔭
    rw [GlobalTheory.NT.Model.heckeIdeal_mul L _ hpp.ne_zero ha, mul_pow, ih ha hc.of_mul_left_right, mul_one,
      show p = 𝔭.asIdeal from rfl, GlobalTheory.NT.Model.heckeIdeal_prime, heckeVal_of_unramIn L χ (hun 𝔭 hnd) hσ,
      ← Units.val_pow_eq_pow_val, ← map_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', map_one,
      Units.val_one]

theorem pow_finrank_principal : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔮 : Ideal (𝓞 K)), IsRayField K L 𝔮 → ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 →
      ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I ^ Module.finrank K L * Ideal.span {β} = Ideal.span {α} := by
  intro K L _ _ _ _ _ 𝔮 ⟨hab, hun, _, hart⟩ I hI hc
  have hI0 : I ≠ 0 := hI
  refine (hart _ (pow_ne_zero _ hI0) hc.pow_left).1 fun χ => ?_
  rw [heckeIdeal_pow L χ hI0, heckeIdeal_pow_finrank L χ hun I hI0 hc]

end GlobalTheory.Mem.Fld.RayExp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldFinrankPowPrincipalStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassField_finrank_pow_principal : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (𝔮 : Ideal (𝓞 K)), IsRayField K L 𝔮 → ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 → ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I ^ Module.finrank K L * Ideal.span {β} = Ideal.span {α} := by
  first | exact @GlobalTheory.Mem.Fld.RayExp.pow_finrank_principal | exact GlobalTheory.Mem.Fld.RayExp.pow_finrank_principal | (intros; apply GlobalTheory.Mem.Fld.RayExp.pow_finrank_principal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMulInv
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open GlobalTheory.DualPairCheck
open scoped TensorProduct

namespace GlobalTheory.OrientedAdjoint

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gram_det_ne (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    have hx : x = ∑ i, V.frame.repr x i • V.frame i := (V.frame.sum_repr x).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : ∑ j, V.gram i j * v j = 0 := congr_fun h0 i
    have h2 : V.hT (V.frame i) (V.frame.equivFun.symm v) = ∑ j, V.gram i j * v j := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Module.Basis.equivFun_symm_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]; rfl
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h2, h1, smul_zero]
  exact V.frame.equivFun.symm.injective (this.trans (map_zero _).symm)

theorem gram_mul_inv (V : HSp D) : V.gram.map (incA D) * V.gram⁻¹.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem gram_conj (V : HSp D) : ((V.gram.map (incA D)).map (cA D))ᵀ = V.gram.map (incA D) := by
  ext i j
  exact (cA_incA _).trans (congrArg (incA D) (gram_star V j i))

section Generic
variable {A : Type} [CommRing A] {m n : ℕ}

theorem inv_conj (σ : A →+* A) (P Pi : Matrix (Fin n) (Fin n) A) (h : P * Pi = 1) (hP : (P.map σ)ᵀ = P) :
    (Pi.map σ)ᵀ = Pi := by
  have h' : Pi * P = 1 := mul_eq_one_comm.1 h
  have h2 : P * (Pi.map σ)ᵀ = 1 := by
    rw [← hP, ← Matrix.transpose_mul, ← Matrix.map_mul, h',
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  calc _ = (Pi * P) * (Pi.map σ)ᵀ := by rw [h', Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]

end Generic

end GlobalTheory.OrientedAdjoint

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosureFrobeniusElementsEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosureFrobeniusElementsEqTop
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField Pointwise

namespace GlobalTheory.Mem.FieldsEx

theorem isFrob_conj {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {v : HeightOneSpectrum (𝓞 K)} {σ : L ≃ₐ[K] L} (h : IsFrob L v σ) (τ : L ≃ₐ[K] L) :
    IsFrob L v (τ * σ * τ⁻¹) := by
  obtain ⟨P, hP, hl, h⟩ := (isFrob_iff L v σ).1 h
  exact (isFrob_iff L v _).2 ⟨τ • P, inferInstance, inferInstance, h.conj τ⟩

theorem isFrob_one_of_fix {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {v : HeightOneSpectrum (𝓞 K)} {σ : L ≃ₐ[K] L} (h : IsFrob L v σ) (F : IntermediateField K L)
    [NumberField F] (hF : ∀ x ∈ F, σ x = x) : IsFrob F v 1 := by
  obtain ⟨P, hP, hl, h⟩ := h
  refine ⟨P.under (𝓞 F), inferInstance, inferInstance, fun x => ?_⟩
  rw [Ideal.under_def, Ideal.mem_comap, one_smul, map_sub, map_pow]
  have h1 : σ • algebraMap (𝓞 F) (𝓞 L) x = algebraMap (𝓞 F) (𝓞 L) x :=
    RingOfIntegers.ext (hF _ (x : F).2)
  have := h (algebraMap (𝓞 F) (𝓞 L) x)
  rwa [h1] at this

theorem closure_frob_eq_top : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite →
    (∀ (F : Type) [Field F] [NumberField F] [Algebra K F],
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsFrob F v 1) → ∀ σ : F ≃ₐ[K] F, σ = 1) →
    Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ IsFrob L v σ} = ⊤ := by
  intro K L _ _ _ _ _ _ S _ h
  set H := Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ IsFrob L v σ} with hH
  have hn : H.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨v, hv, hx⟩ := hx
      exact Subgroup.subset_closure ⟨v, hv, isFrob_conj hx g⟩
    | one => simp
    | mul x y _ _ hx hy =>
      have := H.mul_mem hx hy
      convert this using 1
      group
    | inv x _ hx =>
      have := H.inv_mem hx
      convert this using 1
      group
  let F := IntermediateField.fixedField H
  have : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  have : NumberField F := NumberField.of_module_finite K F
  have h1 := h F fun v hv => by
    obtain ⟨σ, hσ⟩ := exists_isFrob L v
    exact isFrob_one_of_fix hσ F fun x hx =>
      (IntermediateField.mem_fixedField_iff _ _).1 hx σ (Subgroup.subset_closure ⟨v, hv, hσ⟩)
  refine eq_top_iff.2 fun τ _ => ?_
  rw [← IntermediateField.fixingSubgroup_fixedField H, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h2 := τ.restrictNormal_commutes F ⟨x, hx⟩
  rw [h1 (τ.restrictNormal F)] at h2
  exact h2.symm

end GlobalTheory.Mem.FieldsEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosureFrobeniusElementsEqTopStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_frobeniusElements_eq_top : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → (∀ (F : Type) [Field F] [NumberField F] [Algebra K F], (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsFrob F v 1) → ∀ σ : F ≃ₐ[K] F, σ = 1) → Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ IsFrob L v σ} = ⊤ := by
  first | exact @GlobalTheory.Mem.FieldsEx.closure_frob_eq_top | exact GlobalTheory.Mem.FieldsEx.closure_frob_eq_top | (intros; apply GlobalTheory.Mem.FieldsEx.closure_frob_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllipticTorsionPointCoordinatesFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllipticTorsionPointCoordinatesFinite
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory

theorem finite_latticeCurve_torsion (L : PeriodPair) {n : ℕ} (hn : n ≠ 0) :
    {P : (latticeCurve L).toAffine.Point | n • P = 0}.Finite := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hz : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine (((Set.finite_Ico (0 : ℤ) n).prod (Set.finite_Ico (0 : ℤ) n)).image
    (fun p : ℤ × ℤ => latticePoint L ((p.1 * L.ω₁ + p.2 * L.ω₂) / n))).subset ?_
  intro P hP
  obtain ⟨z, rfl⟩ := latticePoint_surjective L P
  have h1 : latticePoint L (n • z) = 0 := by
    rw [← latticePointHom_apply, map_nsmul, latticePointHom_apply]; exact hP
  rw [latticePoint_eq_zero_iff] at h1
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 h1
  refine ⟨(a % n, b % n), ⟨⟨Int.emod_nonneg _ hz.ne', Int.emod_lt_of_pos _ hz⟩,
    ⟨Int.emod_nonneg _ hz.ne', Int.emod_lt_of_pos _ hz⟩⟩, ?_⟩
  dsimp only
  rw [latticePoint_eq_iff, PeriodPair.mem_lattice]
  refine ⟨-(a / n), -(b / n), ?_⟩
  have ea : (a : ℂ) = ((a % n : ℤ) : ℂ) + n * ((a / n : ℤ) : ℂ) := by
    exact_mod_cast (Int.emod_add_mul_ediv a n).symm
  have eb : (b : ℂ) = ((b % n : ℤ) : ℂ) + n * ((b / n : ℤ) : ℂ) := by
    exact_mod_cast (Int.emod_add_mul_ediv b n).symm
  rw [nsmul_eq_mul] at hab
  rw [Int.cast_neg, Int.cast_neg]
  generalize ((a % n : ℤ) : ℂ) = a₁, ((a / n : ℤ) : ℂ) = a₂, ((b % n : ℤ) : ℂ) = b₁,
    ((b / n : ℤ) : ℂ) = b₂ at ea eb ⊢
  rw [ea, eb] at hab
  field_simp
  linear_combination -hab

theorem finite_complex_torsion_points (W : WeierstrassCurve ℂ) [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) :
    {P : W.toAffine.Point | n • P = 0}.Finite := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_latticeCurve W
  let e := variableChangePointEquiv C hC
  refine ((finite_latticeCurve_torsion L hn).image e).subset ?_
  intro P hP
  refine ⟨e.symm P, ?_, e.apply_symm_apply P⟩
  have hP' : n • P = 0 := hP
  show n • e.symm P = 0
  rw [← map_nsmul, hP', map_zero]

theorem finite_torsionCoords :
    ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic] (n : ℕ), n ≠ 0 → (torsionCoords W n).Finite := by
  intro W _ n hn
  have h := finite_complex_torsion_points W hn
  let fx : W.toAffine.Point → ℂ := fun P => match P with
    | .zero => 0
    | .some x _ _ => x
  let fy : W.toAffine.Point → ℂ := fun P => match P with
    | .zero => 0
    | .some _ y _ => y
  refine ((h.image fx).union (h.image fy)).subset ?_
  rintro z ⟨x, y, hxy, h0, rfl | rfl⟩
  · exact Or.inl ⟨_, h0, rfl⟩
  · exact Or.inr ⟨_, h0, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllipticTorsionPointCoordinatesFiniteStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ellipticTorsionPointCoordinates_finite : ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic] (n : ℕ), n ≠ 0 → (torsionCoords W n).Finite := by
  first | exact @GlobalTheory.finite_torsionCoords | exact GlobalTheory.finite_torsionCoords | (intros; apply GlobalTheory.finite_torsionCoords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharacterValueViaPowerGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharacterValueViaPowerGenerator
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.ValPow

variable {L : Type} [Field L] [NumberField L]

theorem count_span_int (w : HeightOneSpectrum (𝓞 L)) (a : 𝓞 L) (ha : a ≠ 0) :
    FractionalIdeal.count L w (FractionalIdeal.spanSingleton (𝓞 L)⁰ (algebraMap (𝓞 L) L a)) =
      -WithZero.log (w.valuation L (algebraMap (𝓞 L) L a)) := by
  classical
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe L w (by simpa using ha),
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ ha]
  simp

theorem ordF_eq_count (w : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    ordF w k = FractionalIdeal.count L w (FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L)) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (k : L)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact k.ne_zero (by rw [← hab]; simp)
  have ha' : algebraMap (𝓞 L) L a ≠ 0 := by simpa using ha0
  have hb' : algebraMap (𝓞 L) L b ≠ 0 := by simpa using hb0
  unfold ordF
  rw [← hab, div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.count_mul L w (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha')
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hb')),
    FractionalIdeal.count_inv, count_span_int w a ha0, count_span_int w b hb0, map_mul, map_inv₀,
    WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha') (inv_ne_zero ((Valuation.ne_zero_iff _).2 hb')), WithZero.log_inv]
  ring

theorem locK_eq_one {χ : HChar L} {w : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt w) (k : Lˣ)
    (hk : w.valuation L ((k : L) - 1) < 1) : χ.locK w k = 1 := by
  refine h _ ?_ ?_
  · unfold IsUnitAt
    have h1 : Valued.v ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) = w.valuation L (k : L) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (k : L)
    rw [h1]
    have := (w.valuation L).map_one_add_of_lt hk
    rwa [add_sub_cancel] at this
  · have h1 : ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1 =
        algebraMap L (w.adicCompletion L) ((k : L) - 1) := by
      rw [map_sub, map_one]
      rfl
    have h2 : Valued.v (algebraMap L (w.adicCompletion L) ((k : L) - 1)) =
        w.valuation L ((k : L) - 1) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [h1, h2]
    rcases eq_or_ne (w.valuation L ((k : L) - 1)) 0 with h0 | h0
    · rw [h0]; exact zero_le
    · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hk
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      push_cast
      omega

theorem inf_mul_val_pow : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ w, w ∉ S → χ.UnrAt w) → (∀ w ∈ S, χ.TameAt w) → ∀ (v : HeightOneSpectrum (𝓞 L)), v ∉ S → ∀ (h : ℕ) (k : Lˣ), FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h → (∀ w ∈ S, w.valuation L ((k : L) - 1) < 1) → χ.inf k * χ.val v ^ h = 1 := by
  classical
  intro L _ _ χ S hS hT v hv h k hk h1
  rw [← GlobalTheory.HeckeProduct.hchar_productRule L χ S hS k,
    Finset.prod_eq_one (fun w hw => locK_eq_one (hT w hw) k (h1 w hw)), mul_one]
  congr 1
  rw [finprod_eq_single _ v]
  · rw [finprod_eq_if, if_pos hv, ordF_eq_count, hk, FractionalIdeal.count_pow, FractionalIdeal.count_self, mul_one,
      zpow_natCast]
  · intro w hw
    rw [ordF_eq_count, hk, FractionalIdeal.count_pow, FractionalIdeal.count_maximal_coprime L w (Ne.symm hw), mul_zero,
      zpow_zero, finprod_one]

end GlobalTheory.Mem.ValPow

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharacterValueViaPowerGeneratorStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameHeckeCharacter_value_via_power_generator : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ w, w ∉ S → χ.UnrAt w) → (∀ w ∈ S, χ.TameAt w) → ∀ (v : HeightOneSpectrum (𝓞 L)), v ∉ S → ∀ (h : ℕ) (k : Lˣ), FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h → (∀ w ∈ S, w.valuation L ((k : L) - 1) < 1) → χ.inf k * χ.val v ^ h = 1 := by
  first | exact @GlobalTheory.Mem.ValPow.inf_mul_val_pow | exact GlobalTheory.Mem.ValPow.inf_mul_val_pow | (intros; apply GlobalTheory.Mem.ValPow.inf_mul_val_pow <;> assumption)
end
end
