module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

noncomputable section

open scoped Kronecker

namespace GlobalTheory.ModuLR

section Conj

theorem addEquivAddHaarChar_transport {A B : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A] [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [LocallyCompactSpace B] [MeasurableSpace B] [BorelSpace B]
    (e : A ≃ₜ+ B) (φ : A ≃ₜ+ A) :
    addEquivAddHaarChar ((e.symm.trans φ).trans e) = addEquivAddHaarChar φ := by
  set ν : Measure A := Measure.addHaar
  set μ : Measure B := ν.map e
  haveI : μ.IsAddHaarMeasure := e.isAddHaarMeasure_map ν
  haveI : μ.Regular := Measure.Regular.map e.toHomeomorph
  set ψ : B ≃ₜ+ B := (e.symm.trans φ).trans e
  have he : Measurable e := e.continuous.measurable
  have hφ : Measurable φ := φ.continuous.measurable
  have hψ : Measurable ψ := ψ.continuous.measurable
  have h1 := addEquivAddHaarChar_smul_map ν φ
  have h2 := addEquivAddHaarChar_smul_map μ ψ
  have hm : μ.map ψ = (ν.map φ).map e := by
    rw [Measure.map_map hψ he, Measure.map_map he hφ]
    congr 1
    funext x
    simp [ψ]
  have h3 : addEquivAddHaarChar φ • μ.map ψ = μ := by rw [hm, ← Measure.map_smul _ he.aemeasurable, h1]
  haveI : (μ.map ψ).IsAddHaarMeasure := ψ.isAddHaarMeasure_map μ
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : B)
  have hpos : (μ.map ψ) K ≠ 0 := (Measure.measure_pos_of_mem_nhds (μ := μ.map ψ) hKn).ne'
  have htop : (μ.map ψ) K ≠ ⊤ := (hK.measure_lt_top).ne
  have h4 : (addEquivAddHaarChar ψ : ℝ≥0∞) * (μ.map ψ) K = (addEquivAddHaarChar φ : ℝ≥0∞) * (μ.map ψ) K := by
    have a2 := congrArg (fun m : Measure B => m K) h2
    have a3 := congrArg (fun m : Measure B => m K) h3
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at a2 a3
    rw [a2, a3]
  exact_mod_cast (ENNReal.mul_left_inj hpos htop).1 h4

end Conj

section Det

variable {S : Type} [CommRing S] {m n : ℕ}

def lrLin (g : Matrix (Fin m) (Fin m) S) (a : Matrix (Fin n) (Fin n) S) :
    Matrix (Fin m) (Fin n) S →ₗ[S] Matrix (Fin m) (Fin n) S where
  toFun u := g * u * a
  map_add' u v := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c u := by simp [Matrix.mul_smul, Matrix.smul_mul]

theorem det_lrLin (g : Matrix (Fin m) (Fin m) S) (a : Matrix (Fin n) (Fin n) S) :
    LinearMap.det (lrLin g a) = g.det ^ n * a.det ^ m := by
  let e : Matrix (Fin m) (Fin n) S ≃ₗ[S] (Fin m × Fin n → S) := (LinearEquiv.curry S S (Fin m) (Fin n)).symm
  have key : (e : Matrix (Fin m) (Fin n) S →ₗ[S] (Fin m × Fin n → S)) ∘ₗ lrLin g a ∘ₗ
      (e.symm : (Fin m × Fin n → S) →ₗ[S] Matrix (Fin m) (Fin n) S) = Matrix.toLin' (g ⊗ₖ aᵀ) := by
    refine LinearMap.ext fun x => funext fun p => ?_
    obtain ⟨i, j⟩ := p
    change (g * Matrix.of (Function.curry x) * a) i j = _
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.mul_apply, Finset.sum_mul, Function.curry_apply, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← LinearMap.det_conj (lrLin g a) e, key, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose]
  simp

end Det

end GlobalTheory.ModuLR

namespace GlobalTheory.ModuLR

section Restr

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev tensBasis : Module.Basis (Fin (Module.finrank F E)) (AF F) (AF F ⊗[F] E) :=
  Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)

def matCoord (m n : ℕ) :
    Matrix (Fin m) (Fin n) (AF F ⊗[F] E) ≃ₗ[AF F] (Fin m × Fin n × Fin (Module.finrank F E) → AF F) where
  toFun u p := (tensBasis F E).equivFun (u p.1 p.2.1) p.2.2
  invFun x := Matrix.of fun i j => (tensBasis F E).equivFun.symm fun k => x (i, j, k)
  left_inv u := by
    ext i j
    simp only [Matrix.of_apply]
    exact (tensBasis F E).equivFun.symm_apply_apply (u i j)
  right_inv x := by
    funext p
    obtain ⟨i, j, k⟩ := p
    show (tensBasis F E).equivFun ((tensBasis F E).equivFun.symm fun k => x (i, j, k)) k = x (i, j, k)
    rw [LinearEquiv.apply_symm_apply]
  map_add' u v := by funext p; simp
  map_smul' c u := by funext p; simp

theorem continuous_matCoord (m n : ℕ) : Continuous (matCoord F E m n) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have hb : Continuous (tensBasis F E).equivFun :=
    IsModuleTopology.continuous_of_linearMap (tensBasis F E).equivFun.toLinearMap
  exact continuous_pi fun p => (continuous_apply p.2.2).comp
    (hb.comp ((continuous_apply p.2.1).comp (continuous_apply p.1)))

theorem continuous_matCoord_symm (m n : ℕ) : Continuous (matCoord F E m n).symm := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have hb : Continuous (tensBasis F E).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (tensBasis F E).equivFun.symm.toLinearMap
  exact continuous_pi fun i => continuous_pi fun j =>
    hb.comp (continuous_pi fun k => continuous_apply (i, j, k))

def matCoordCE (m n : ℕ) :
    Matrix (Fin m) (Fin n) (AF F ⊗[F] E) ≃ₜ+ (Fin m × Fin n × Fin (Module.finrank F E) → AF F) :=
  { (matCoord F E m n).toAddEquiv with
    continuous_toFun := continuous_matCoord F E m n
    continuous_invFun := continuous_matCoord_symm F E m n }

end Restr

end GlobalTheory.ModuLR

namespace GlobalTheory.ModuLR

theorem exists_matrix_restrictScalars_lrCE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ) [LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [MeasurableSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] (g : GL (Fin m) (AF F ⊗[F] E)) (a : GL (Fin n) (AF F ⊗[F] E)), ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (Λ : Matrix κ κ (AF F)) (hΛ : IsUnit Λ.det), Λ.det = Algebra.norm (AF F) ((Matrix.GeneralLinearGroup.det g ^ n * Matrix.GeneralLinearGroup.det a ^ m : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) ∧ addEquivAddHaarChar (lrCE g a) = addEquivAddHaarChar (mulVecCE Λ hΛ) := by
  intro F E _ _ _ _ _ m n _ _ _ _ g a
  haveI : IsScalarTower (AF F) (AF F ⊗[F] E) (Matrix (Fin m) (Fin n) (AF F ⊗[F] E)) := inferInstance
  haveI : Module.Free (AF F) (AF F ⊗[F] E) := Module.Free.of_basis (tensBasis F E)
  haveI : Module.Finite (AF F) (AF F ⊗[F] E) := Module.Finite.of_basis (tensBasis F E)
  set Φ := matCoord F E m n
  set f : Matrix (Fin m) (Fin n) (AF F ⊗[F] E) →ₗ[AF F ⊗[F] E] Matrix (Fin m) (Fin n) (AF F ⊗[F] E) :=
    lrLin (g : Matrix (Fin m) (Fin m) (AF F ⊗[F] E)) (a : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))
  set Λ := LinearMap.toMatrix' (Φ.toLinearMap ∘ₗ f.restrictScalars (AF F) ∘ₗ Φ.symm.toLinearMap)
  have hdet : Λ.det = Algebra.norm (AF F) ((Matrix.GeneralLinearGroup.det g ^ n * Matrix.GeneralLinearGroup.det a ^ m :
      (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) := by
    rw [LinearMap.det_toMatrix', LinearMap.det_conj, LinearMap.det_restrictScalars, det_lrLin]
    simp [Matrix.GeneralLinearGroup.val_det_apply]
  have hΛ : IsUnit Λ.det := hdet ▸ (Units.isUnit _).map (Algebra.norm (AF F))
  refine ⟨_, inferInstance, inferInstance, Λ, hΛ, hdet, ?_⟩
  have hc : mulVecCE Λ hΛ = ((matCoordCE F E m n).symm.trans (lrCE g a)).trans (matCoordCE F E m n) := by
    ext x
    rw [mulVecCE_apply, LinearMap.toMatrix'_mulVec]
    rfl
  rw [hc, addEquivAddHaarChar_transport]

end GlobalTheory.ModuLR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTensStatement
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_restrictScalars_matrix_leftRightMul_adeleTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ) [LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [MeasurableSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] (g : GL (Fin m) (AF F ⊗[F] E)) (a : GL (Fin n) (AF F ⊗[F] E)), ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (Λ : Matrix κ κ (AF F)) (hΛ : IsUnit Λ.det), Λ.det = Algebra.norm (AF F) ((Matrix.GeneralLinearGroup.det g ^ n * Matrix.GeneralLinearGroup.det a ^ m : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) ∧ addEquivAddHaarChar (lrCE g a) = addEquivAddHaarChar (mulVecCE Λ hΛ) := by
  first | exact @GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE | exact GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE | (intros; apply GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeOnePrimeReductionSplitPlaceDictionary
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeOnePrimeReductionSplitPlaceDictionary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceRed

section Gen

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

theorem mem_max_iff (a : v.adicCompletionIntegers F) :
    IsLocalRing.residue (v.adicCompletionIntegers F) a = 0 ↔ Valued.v (a : v.adicCompletion F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  exact Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))

theorem exists_red {A : Type} [CommRing A] (I : Ideal A) (ψ : A →+* v.adicCompletionIntegers F)
    (hI : ∀ x, x ∈ I ↔ Valued.v (ψ x : v.adicCompletion F) < 1)
    (hs : ∀ a : v.adicCompletionIntegers F, ∃ x, Valued.v ((a : v.adicCompletion F) - ψ x) < 1) :
    ∃ r : v.adicCompletionIntegers F →+* A ⧸ I, (∀ x, r (ψ x) = Ideal.Quotient.mk I x) ∧
      ∀ a, r a = 0 ↔ Valued.v (a : v.adicCompletion F) < 1 := by
  let q := Ideal.Quotient.lift I ((IsLocalRing.residue _).comp ψ)
    (fun x hx => (mem_max_iff _).2 ((hI x).1 hx))
  have hq : Function.Bijective q := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact Ideal.Quotient.eq_zero_iff_mem.2 ((hI x).2 ((mem_max_iff _).1 hy))
    · intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨x, hx⟩ := hs a
      refine ⟨Ideal.Quotient.mk I x, ?_⟩
      show IsLocalRing.residue _ (ψ x) = _
      rw [eq_comm, ← sub_eq_zero, ← map_sub, mem_max_iff]
      exact hx
  let e := RingEquiv.ofBijective q hq
  refine ⟨(e.symm : _ →+* A ⧸ I).comp (IsLocalRing.residue _), fun x => ?_, fun a => ?_⟩
  · show e.symm _ = _
    rw [RingEquiv.symm_apply_eq]
    rfl
  · show e.symm _ = 0 ↔ _
    rw [map_eq_zero_iff _ e.symm.injective, mem_max_iff]

theorem exists_unitPart : ∃ t : (v.adicCompletion F)ˣ →* v.adicCompletionIntegers F,
    ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → (t u : v.adicCompletion F) = u := by
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1))
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  have hne : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) ≠ 0 := fun u =>
    (Valuation.ne_zero_iff _).2 u.ne_zero
  have hv : ∀ u : (v.adicCompletion F)ˣ,
      Valued.v ((u : v.adicCompletion F) * p ^ (WithZero.log (Valued.v (u : v.adicCompletion F)))) = 1 := by
    intro u
    rw [map_mul, map_zpow₀, hp, ← WithZero.exp_zsmul]
    conv_lhs => lhs; rw [← WithZero.exp_log (hne u)]
    rw [← WithZero.exp_add]
    simp
  refine ⟨⟨⟨fun u => ⟨(u : v.adicCompletion F) * p ^ (WithZero.log (Valued.v (u : v.adicCompletion F))),
    (hv u).le⟩, ?_⟩, ?_⟩, ?_⟩
  · apply Subtype.ext
    simp
  · intro a b
    apply Subtype.ext
    show ((a * b : (v.adicCompletion F)ˣ) : v.adicCompletion F) * p ^ _ = (_ * p ^ _) * (_ * p ^ _)
    rw [Units.val_mul, map_mul, WithZero.log_mul (hne a) (hne b), zpow_add₀ hp0]
    ring
  · intro u hu
    show (u : v.adicCompletion F) * p ^ _ = _
    rw [hu]
    simp

end Gen

variable {D : D7} {v : FinPl D} (φ : SplitProj D v)

def rdQh : D.host.E →+* Fv D.host.F v :=
  φ.toRingHom.comp (Algebra.TensorProduct.includeRight (R := D.host.F) (A := Fv D.host.F v) (B := D.host.E)).toRingHom

theorem rdQh_apply (x : D.host.E) : rdQh φ x = rdQ φ x := rfl

theorem rdQ_int (x : 𝓞 D.host.E) : rdQ φ (x : D.host.E) ∈ v.adicCompletionIntegers D.host.F := by
  obtain ⟨p, hm, hp⟩ : IsIntegral ℤ (x : D.host.E) := x.2
  refine ReciprocityTheory.Aut.adic_le_one_of_poly v p hm ?_
  have := congrArg (rdQh φ) hp
  rw [Polynomial.hom_eval₂, map_zero, RingHom.ext_int ((rdQh φ).comp _) (Int.castRingHom _)] at this
  exact this

theorem rdQ_alg (y : D.host.F) :
    rdQ φ (algebraMap D.host.F D.host.E y) = algebraMap D.host.F (Fv D.host.F v) y := by
  show φ ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Fv D.host.F v) (B := D.host.E))
    (algebraMap D.host.F D.host.E y)) = _
  rw [AlgHom.commutes]
  exact φ.commutes (algebraMap D.host.F (Fv D.host.F v) y)

def rdO : 𝓞 D.host.E →+* v.adicCompletionIntegers D.host.F :=
  ((rdQh φ).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict (v.adicCompletionIntegers D.host.F) (rdQ_int φ)

theorem rdO_coe (x : 𝓞 D.host.E) : (rdO φ x : Fv D.host.F v) = rdQ φ (x : D.host.E) := rfl

theorem rdO_dense (a : v.adicCompletionIntegers D.host.F) :
    ∃ x, Valued.v ((a : Fv D.host.F v) - rdO φ x) < 1 := by
  obtain ⟨y, hy⟩ := ReciprocityTheory.Aut.adic_exists_approx v (a : Fv D.host.F v) a.2
  refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y, ?_⟩
  have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F y) := by
    show algebraMap (𝓞 D.host.E) D.host.E _ = _
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [rdO_coe, h1, rdQ_alg]
  exact hy

theorem rdE_tmul (x : D.host.E) (y : Af D.host.F) :
    rdE φ (x ⊗ₜ[D.host.F] y) = φ (y v ⊗ₜ[D.host.F] x) := rfl

theorem rdE_int (N : EAf D) (hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    rdE φ N ∈ v.adicCompletionIntegers D.host.F := by
  have hle : Formalism.L2.Herm.intAf D.host.F D.host.E ≤
      (v.adicCompletionIntegers D.host.F).toSubring.comap (rdE φ) := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨b, rfl⟩ | ⟨y, rfl⟩)
    · obtain ⟨b0, hb0⟩ := b.2
      show rdE φ ((b : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∈ v.adicCompletionIntegers D.host.F
      rw [← hb0]
      exact rdQ_int φ b0
    · show rdE φ ((1 : D.host.E) ⊗ₜ[D.host.F] (y : Af D.host.F)) ∈ v.adicCompletionIntegers D.host.F
      rw [rdE_tmul]
      have : φ ((y : Af D.host.F) v ⊗ₜ[D.host.F] (1 : D.host.E)) = (y : Af D.host.F) v := φ.commutes _
      rw [this]
      exact y.2 v
  exact hle hN

def rdS : Formalism.L2.Herm.intAf D.host.F D.host.E →+* v.adicCompletionIntegers D.host.F :=
  ((rdE φ).comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).codRestrict (v.adicCompletionIntegers D.host.F)
    (fun N => rdE_int φ N.1 N.2)

theorem rdS_oToS (x : 𝓞 D.host.E) : rdS φ (Formalism.L2.DIV.oToS D.host.F D.host.E x) = rdO φ x := rfl

theorem eq_resS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (PP : Formalism.L2.DIV.Pl E) (g : Formalism.L2.Herm.intAf F E →+* Formalism.L2.DIV.kP PP)
    (hg : ∀ x, g (Formalism.L2.DIV.oToS F E x) = Ideal.Quotient.mk PP.asIdeal x) (N : Formalism.L2.Herm.intAf F E) :
    g N = Formalism.L2.DIV.resS F PP N := by
  have key : ∀ g' : Formalism.L2.Herm.intAf F E →+* Formalism.L2.DIV.kP PP,
      (∀ x, g' (Formalism.L2.DIV.oToS F E x) = Ideal.Quotient.mk PP.asIdeal x) →
      Formalism.L2.DIV.idS F PP.asIdeal ≤ RingHom.ker g' := by
    intro g' hg'
    refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, hg']
    exact Ideal.Quotient.eq_zero_iff_mem.2 hx
  obtain ⟨q, hq⟩ := Formalism.L2.DIV.cmpS_surj (F := F) PP.asIdeal PP.ne_bot (Ideal.Quotient.mk _ N)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hm : Formalism.L2.DIV.oToS F E b - N ∈ Formalism.L2.DIV.idS F PP.asIdeal := Ideal.Quotient.eq.1 hq
  have h1 := key g hg hm
  have h2 := key _ (Formalism.L2.DIV.resS_oToS (F := F) PP) hm
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h1 h2
  rw [← h1, ← h2, hg, Formalism.L2.DIV.resS_oToS]

theorem red_dict : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E), IsProjAt φ PP → (∃ r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP, Function.Surjective r ∧ (∀ a : v.adicCompletionIntegers D.host.F, r a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) ∧ (∀ (a : Fv D.host.F v) (b : Formalism.L2.DIV.kP PP), RedRel φ PP a b ↔ ∃ h : a ∈ v.adicCompletionIntegers D.host.F, r ⟨a, h⟩ = b) ∧ ∀ (N : EAf D) (hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∃ h : rdE φ N ∈ v.adicCompletionIntegers D.host.F, r ⟨rdE φ N, h⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨N, hN⟩) ∧ ∀ ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ, ∃ mu : (Fv D.host.F v)ˣ →* ℂˣ, LiftsChar φ PP mu ξ := by
  intro D v φ PP hP
  obtain ⟨r, hr, hr0⟩ := exists_red PP.asIdeal (rdO φ) hP (rdO_dense φ)
  have hrel : ∀ (a : Fv D.host.F v) (b : Formalism.L2.DIV.kP PP),
      RedRel φ PP a b ↔ ∃ h : a ∈ v.adicCompletionIntegers D.host.F, r ⟨a, h⟩ = b := by
    intro a b
    constructor
    · rintro ⟨x, rfl, hx⟩
      have ha : a ∈ v.adicCompletionIntegers D.host.F := by
        have e : a = (a - rdQ φ (x : D.host.E)) + rdQ φ (x : D.host.E) := by ring
        rw [e]
        exact add_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx.le) (rdQ_int φ x)
      refine ⟨ha, ?_⟩
      rw [← hr, ← sub_eq_zero, ← map_sub, hr0]
      exact hx
    · rintro ⟨h, rfl⟩
      obtain ⟨x, hx⟩ := rdO_dense φ ⟨a, h⟩
      refine ⟨x, ?_, hx⟩
      rw [← hr, eq_comm, ← sub_eq_zero, ← map_sub, hr0]
      exact hx
  refine ⟨⟨r, fun b => ?_, hr0, hrel, fun N hN => ⟨rdE_int φ N hN, ?_⟩⟩, fun ξ => ?_⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨_, hr x⟩
  · exact eq_resS PP (r.comp (rdS φ)) (fun x => hr x) ⟨N, hN⟩
  · obtain ⟨t, ht⟩ := exists_unitPart (F := D.host.F) (v := v)
    refine ⟨ξ.comp (r.toMonoidHom.comp t).toHomUnits, fun u k huk => ?_⟩
    obtain ⟨h, hk⟩ := (hrel _ _).1 huk
    have hu : Valued.v (u : Fv D.host.F v) = 1 := by
      refine le_antisymm h (not_lt.1 fun hlt => ?_)
      have h0 : (k : Formalism.L2.DIV.kP PP) = 0 := hk ▸ (hr0 ⟨_, h⟩).2 hlt
      have : Nontrivial (Formalism.L2.DIV.kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
      exact k.ne_zero h0
    show ξ _ = ξ k
    congr 1
    apply Units.ext
    show r (t u) = k
    rw [← hk]
    congr 1
    exact Subtype.ext (ht u hu)

end GlobalTheory.PlaceRed

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeOnePrimeReductionSplitPlaceDictionaryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_one_prime_reduction_split_place_dictionary : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E), IsProjAt φ PP → (∃ r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP, Function.Surjective r ∧ (∀ a : v.adicCompletionIntegers D.host.F, r a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) ∧ (∀ (a : Fv D.host.F v) (b : Formalism.L2.DIV.kP PP), RedRel φ PP a b ↔ ∃ h : a ∈ v.adicCompletionIntegers D.host.F, r ⟨a, h⟩ = b) ∧ ∀ (N : EAf D) (hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∃ h : rdE φ N ∈ v.adicCompletionIntegers D.host.F, r ⟨rdE φ N, h⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨N, hN⟩) ∧ ∀ ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ, ∃ mu : (Fv D.host.F v)ˣ →* ℂˣ, LiftsChar φ PP mu ξ := by
  first | exact @GlobalTheory.PlaceRed.red_dict | exact GlobalTheory.PlaceRed.red_dict | (intros; apply GlobalTheory.PlaceRed.red_dict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryClosureLocalComponentsOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryClosureLocalComponentsOpen
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceGen

open GlobalTheory.AdelicU

theorem piCoprod_mem {ι G : Type} [Fintype ι] [Monoid G] {N : ι → Type} [∀ i, Monoid (N i)] (φ : ∀ i, N i →* G)
    (h : Pairwise fun i j => ∀ x y, Commute (φ i x) (φ j y)) (M : Submonoid G) (hM : ∀ i x, φ i x ∈ M)
    (x : ∀ i, N i) : MonoidHom.noncommPiCoprod φ h x ∈ M := by
  rw [MonoidHom.noncommPiCoprod_apply]
  exact Submonoid.noncommProd_mem _ _ _ _ fun i _ => hM i (x i)

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))

omit [NumberField E] in
theorem levelOff_anti {S S' : Finset (HeightOneSpectrum (𝓞 F))} (h : S ⊆ S') :
    levelOff σ J L S' ≤ levelOff σ J L S := fun g hg => by
  rw [mem_levelOff] at hg ⊢
  refine ⟨hg.1, fun v hv => hg.2.1 v (h hv), fun v _ => ?_⟩
  by_cases hv : v ∈ S'
  · rw [hg.2.1 v hv]; exact one_mem _
  · exact hg.2.2 v hv

theorem exists_levelOff_le [Submodule.IsFullLattice E L] (U : Subgroup (GAd σ J)) (hU : IsOpen (U : Set (GAd σ J))) :
    ∃ S, levelOff σ J L S ≤ U := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun S : Finset (HeightOneSpectrum (𝓞 F)) => (levelOff σ J L S : Set (GAd σ J)) \ (U : Set (GAd σ J)))
    (fun S S' => ⟨S ∪ S', Set.diff_subset_diff_left (levelOff_anti σ J L Finset.subset_union_left),
      Set.diff_subset_diff_left (levelOff_anti σ J L Finset.subset_union_right)⟩)
    (fun S => Set.diff_nonempty.2 (hcon S))
    (fun S => (isCompact_levelOff σ J L S).diff hU)
    (fun S => ((isCompact_levelOff σ J L S).diff hU).isClosed)
  rw [Set.mem_iInter] at hg
  have h1 : g = 1 := GAd_ext σ J
    (fun w => by rw [mem_finPts_iff_forall.1 (mem_levelOff.1 (hg ∅).1).1 w, map_one])
    fun v => by rw [(mem_levelOff.1 (hg {v}).1).2.1 v (Finset.mem_singleton_self v), map_one]
  exact (hg ∅).2 (h1 ▸ one_mem U)

omit [NumberField E] in
theorem emb_proj_mem_levelOff {S : Finset (HeightOneSpectrum (𝓞 F))} {k : GAd σ J} (hk : k ∈ levelOff σ J L S)
    (v : HeightOneSpectrum (𝓞 F)) : emb σ J v (proj σ J v k) ∈ levelOff σ J L S := by
  by_cases hv : v ∈ S
  · rw [(mem_levelOff.1 hk).2.1 v hv, map_one]; exact one_mem _
  · exact emb_mem_levelOff hv ((mem_levelOff.1 hk).2.2 v hv)

theorem eq_top_of_local [Submodule.IsFullLattice E L] (M : Submonoid (GAd σ J)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h1 : ∀ v x, emb σ J v x ∈ M) (h2 : ∀ w x, embArch σ J w x ∈ M) (h3 : ∀ k ∈ levelOff σ J L S, k ∈ M) :
    M = ⊤ := by
  classical
  refine top_unique fun g _ => ?_
  have hinf : ∀ y, ofInf σ J y ∈ M := fun y => by
    rw [← (infEquivPi σ J).symm_apply_apply y]
    generalize infEquivPi σ J y = x
    have : embArchPi σ J x ∈ M.comap (ofInf σ J) := by
      exact piCoprod_mem (fun w => embArchInf σ J w) _ _ (fun w y => h2 w y) x
    exact this
  have hat : ∀ S' x, embAt σ J S' x ∈ M := fun S' x => by
    exact piCoprod_mem (fun v : S' => emb σ J v) _ _ (fun v y => h1 v y) x
  have hf := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc σ J L g)
  set g' := ofFin σ J (projFin σ J g) with hg'
  set S' := S ∪ hf.toFinset with hS'
  have hfin : g' ∈ finPts σ J := mem_finPts.2 (by simp [hg'])
  have hx := mem_atPts.1 (embAt_mem σ J S' (projAt σ J S' g'))
  have hrest : (partAway σ J S' g' : GAd σ J) ∈ levelOff σ J L S' := by
    refine mem_levelOff.2 ⟨mul_mem (inv_mem hx.1) hfin, mem_awayPts.1 (partAway σ J S' g').2, fun v hv => ?_⟩
    change proj σ J v ((embAt σ J S' (projAt σ J S' g'))⁻¹ * g') ∈ _
    rw [map_mul, map_inv, hx.2 v hv, inv_one, one_mul, hg', proj_ofFin, projFinLoc_projFin]
    by_contra hc
    exact hv (Finset.mem_union_right _ (hf.mem_toFinset.2 hc))
  rw [← ofInf_projInf_mul_ofFin_projFin σ J g, ← hg', ← embAt_mul_partAway σ J S' g']
  exact mul_mem (hinf _) (mul_mem (hat _ _) (h3 _ (levelOff_anti σ J L Finset.subset_union_left hrest)))

end General

theorem gen_by_local : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → (∀ g : GA D V, {p : Place D | ¬ (gAt V p g ∈ U ∧ gAt V p g ∈ GfC V)}.Finite) ∧ Submonoid.closure ({g : GA D V | ∃ p, gAt V p g = g} ∪ {k : GA D V | k ∈ U ∧ k ∈ GfC V ∧ ∀ p, gAt V p k ∈ U ∧ gAt V p k ∈ GfC V}) = ⊤ := by
  intro D V U hU
  haveI hL : Submodule.IsFullLattice D.host.E (stdLattice D.host.E V.rank) := isLattice_stdLattice
  obtain ⟨S, hS⟩ := exists_levelOff_le D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) U hU
  have hG : ∀ k ∈ levelOff D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) S, k ∈ U ∧ k ∈ GfC V :=
    fun k hk => ⟨hS hk, (mem_levelOff.1 hk).1⟩
  refine ⟨fun g => ?_, eq_top_of_local D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) _ S
    (fun v x => Submonoid.subset_closure (Or.inl ⟨.inl v, by simp [gAt]⟩)) (fun w x => ?_) fun k hk => ?_⟩
  · have hf := Filter.eventually_cofinite.1
      (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) g)
    haveI : Finite D.what₂.Tau := Finite.of_injective _ (placeOf_bijective D).1
    refine (((hf.union S.finite_toSet).image Sum.inl).union (Set.finite_range Sum.inr)).subset ?_
    rintro (v | τ) hp
    · refine Or.inl ⟨v, ?_, rfl⟩
      by_contra hc
      rw [Set.mem_union, not_or] at hc
      exact hp (hG _ (emb_mem_levelOff hc.2 (not_not.1 hc.1)))
    · exact Or.inr ⟨τ, rfl⟩
  · obtain ⟨τ, rfl⟩ : ∃ τ, plTau D τ = w := (placeOf_bijective D).2 w
    refine Submonoid.subset_closure (Or.inl ⟨.inr τ, ?_⟩)
    simp only [gAt, projArch_embArch_self]
  · refine Submonoid.subset_closure (Or.inr ⟨(hG k hk).1, (hG k hk).2, ?_⟩)
    rintro (v | τ)
    · exact hG _ (emb_proj_mem_levelOff _ _ _ hk v)
    · have : gAt V (.inr τ) k = 1 := by
        simp only [gAt, mem_finPts_iff_forall.1 (mem_levelOff.1 hk).1 _, map_one]
      rw [this]
      exact ⟨one_mem _, one_mem _⟩

end GlobalTheory.PlaceGen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryClosureLocalComponentsOpenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitary_closure_local_components_open : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → (∀ g : GA D V, {p : Place D | ¬ (gAt V p g ∈ U ∧ gAt V p g ∈ GfC V)}.Finite) ∧ Submonoid.closure ({g : GA D V | ∃ p, gAt V p g = g} ∪ {k : GA D V | k ∈ U ∧ k ∈ GfC V ∧ ∀ p, gAt V p k ∈ U ∧ gAt V p k ∈ GfC V}) = ⊤ := by
  first | exact @GlobalTheory.PlaceGen.gen_by_local | exact GlobalTheory.PlaceGen.gen_by_local | (intros; apply GlobalTheory.PlaceGen.gen_by_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharProdCongr
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharProdCongr
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory.ModuLR

theorem addEquivAddHaarChar_prodCE (G₁ G₂ : Type) [AddCommGroup G₁] [TopologicalSpace G₁]
    [IsTopologicalAddGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁]
    [MeasurableSpace G₁] [BorelSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂]
    [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂] [SecondCountableTopology G₂]
    [MeasurableSpace G₂] [BorelSpace G₂] (e₁ : G₁ ≃ₜ+ G₁) (e₂ : G₂ ≃ₜ+ G₂) :
    addEquivAddHaarChar (prodCE e₁ e₂) = addEquivAddHaarChar e₁ * addEquivAddHaarChar e₂ := by
  set μ₁ : Measure G₁ := Measure.addHaar
  set μ₂ : Measure G₂ := Measure.addHaar
  set μ : Measure (G₁ × G₂) := μ₁.prod μ₂
  have hμ : μ.IsAddHaarMeasure := by infer_instance
  have hreg : μ.Regular := by infer_instance
  set φ := prodCE e₁ e₂
  have h1 := addEquivAddHaarChar_smul_map μ₁ e₁
  have h2 := addEquivAddHaarChar_smul_map μ₂ e₂
  have h := addEquivAddHaarChar_smul_map μ φ
  have hm1 : (μ₁.map e₁).IsAddHaarMeasure := e₁.isAddHaarMeasure_map μ₁
  have hm2 : (μ₂.map e₂).IsAddHaarMeasure := e₂.isAddHaarMeasure_map μ₂
  have hmap : μ.map φ = (μ₁.map e₁).prod (μ₂.map e₂) := by
    have := Measure.map_prod_map μ₁ μ₂ e₁.continuous.measurable e₂.continuous.measurable
    exact this.symm
  have hc : (addEquivAddHaarChar e₁ * addEquivAddHaarChar e₂) • μ.map φ = μ := by
    rw [hmap]
    conv_rhs => rw [show μ = μ₁.prod μ₂ from rfl, ← h1, ← h2]
    rw [mul_smul]
    rw [Measure.prod_smul_left, Measure.prod_smul_right]
  have hν : (μ.map φ).IsAddHaarMeasure := φ.isAddHaarMeasure_map μ
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G₁ × G₂)
  have hpos : (μ.map φ) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hfin : (μ.map φ) K ≠ ∞ := hK.measure_lt_top.ne
  have key := congrArg (fun m : Measure (G₁ × G₂) => m K) (h.trans hc.symm)
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at key
  have := (ENNReal.mul_left_inj hpos hfin).1 key
  exact_mod_cast this

end GlobalTheory.ModuLR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharProdCongrStatement
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addEquivAddHaarChar_prodCongr : ∀ (G₁ G₂ : Type) [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂] (e₁ : G₁ ≃ₜ+ G₁) (e₂ : G₂ ≃ₜ+ G₂), addEquivAddHaarChar (prodCE e₁ e₂) = addEquivAddHaarChar e₁ * addEquivAddHaarChar e₂ := by
  first | exact @GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE | exact GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE | (intros; apply GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimePlacesSplit
open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.SplitPlace

theorem isSplit_of_norm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {p : ℕ} (hp : p.Prime)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal →
      Ideal.absNorm w.asIdeal = p ∧ (p : 𝓞 E) ∉ w.asIdeal ^ 2)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (p : 𝓞 F) ∈ v.asIdeal) : IsSplit (E := E) v := by
  classical
  haveI hfin : Module.Finite (𝓞 F) (𝓞 E) := by
    first
    | infer_instance
    | exact Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 E)
  haveI hint : Algebra.IsIntegral (𝓞 F) (𝓞 E) := by
    first
    | infer_instance
    | exact Algebra.IsIntegral.of_finite (𝓞 F) (𝓞 E)

  have hdeg : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact h2

  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)
  rw [hdeg] at hsum

  have hover : ∀ Q : Ideal (𝓞 E), Q.LiesOver v.asIdeal → (p : 𝓞 E) ∈ Q := by
    intro Q hQo
    have hmem : (p : 𝓞 F) ∈ Q.under (𝓞 F) := by
      rw [← hQo.over]
      exact hv
    have hmem' : algebraMap (𝓞 F) (𝓞 E) (p : 𝓞 F) ∈ Q := hmem
    simpa using hmem'

  have hf : ∀ q : v.asIdeal.primesOver (𝓞 E), q.1.inertiaDeg (𝓞 F) = 1 := by
    rintro ⟨Q, hQp, hQo⟩
    haveI := hQp
    haveI := hQo
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    have hN : Ideal.absNorm Q = p := (h ⟨Q, hQp, hQ0⟩ (hover Q hQo)).1
    have key : Ideal.absNorm v.asIdeal ^ Q.inertiaDeg (𝓞 F) = p := by
      rw [Ideal.absNorm_pow_inertiaDeg v.asIdeal Q]
      exact hN
    exact Nat.Prime.eq_one_of_pow (by rw [key]; exact hp)

  have he : ∀ q : v.asIdeal.primesOver (𝓞 E), q.1.ramificationIdx (𝓞 F) = 1 := by
    rintro ⟨Q, hQp, hQo⟩
    haveI := hQp
    haveI := hQo
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    have hsq : (p : 𝓞 E) ∉ Q ^ 2 := (h ⟨Q, hQp, hQ0⟩ (hover Q hQo)).2
    have hle : Q.ramificationIdx (𝓞 F) ≤ 1 := by
      rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal Q v.ne_bot]
      by_contra hlt
      push_neg at hlt
      have hmap : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ Q ^ 2 :=
        Ideal.le_pow_of_le_ramificationIdx' hlt
      apply hsq
      have hin := hmap (Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hv)
      simpa using hin
    have hpos : 0 < Q.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos (R := 𝓞 F) Q
    show Q.ramificationIdx (𝓞 F) = 1
    omega

  by_contra hns
  obtain ⟨Q0, hQ0p, hQ0o⟩ : ∃ Q0 : Ideal (𝓞 E), Q0.IsPrime ∧ Q0.LiesOver v.asIdeal := by
    first
    | obtain ⟨Q0, hQ0m, hQ0o⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
      exact ⟨Q0, hQ0m.isPrime, hQ0o⟩
    | obtain ⟨Q0, hQ0⟩ := Set.nonempty_of_ncard_ne_zero
        (IsDedekindDomain.primesOver_ncard_ne_zero v.asIdeal (𝓞 E))
      exact ⟨Q0, hQ0.1, hQ0.2⟩
  let q0 : v.asIdeal.primesOver (𝓞 E) := ⟨Q0, hQ0p, hQ0o⟩
  have honly : ∀ q : v.asIdeal.primesOver (𝓞 E), q = q0 := by
    rintro ⟨Q, hQp, hQo⟩
    by_contra hne
    apply hns
    haveI := hQo
    haveI := hQ0o
    refine ⟨⟨Q, hQp, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
      ⟨Q0, hQ0p, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q0⟩, ?_, hQo.over.symm, hQ0o.over.symm⟩
    intro hPQ
    exact hne (Subtype.ext (congrArg HeightOneSpectrum.asIdeal hPQ))
  rw [Finset.sum_eq_single q0 (fun b _ hb => absurd (honly b) hb)
    (fun h0 => absurd (Finset.mem_univ q0) h0), he q0, hf q0] at hsum
  omega

theorem isSplit_of_splitsCompletely : ∀ (D : D7) (p : ℕ), SplitsCompletely D p → ∀ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal → IsSplit (E := D.host.E) v := by
  intro D p hp v hv
  have h2 : Module.finrank D.host.F D.host.E = 2 := by
    first
    | haveI : IsCMField D.host.E := Formalism.HC.HostAx.isCMField_hostE D.host.toHostAx
      exact IsQuadraticExtension.finrank_eq_two _ _
    | have hE := Formalism.HC.HostAx.finrank_cmField D.host.toHostAx
      have hF := Formalism.HC.HostAx.finrank_hostF D.host.toHostAx
      have hm := Module.finrank_mul_finrank ℚ D.host.F D.host.E
      have hpos : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos
      rw [hE, hF] at hm
      rw [hF] at hpos
      exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)
  exact isSplit_of_norm h2 hp.1 hp.2 v hv

end GlobalTheory.SplitPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryComponentAtPlaceLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryComponentAtPlaceLaws
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceComponent

section General

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
  {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R''] [Algebra F R'']

theorem tens_comp (φ : R'' →ₐ[F] R) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (k : R' →ₗ[F] R'')
    (hk : ∀ a b, k (a * b) = k a * k b) (h : ∀ a, k (j (φ a)) = k (j 1) * a) (z : R'' ⊗[F] E) :
    tensNU k hk (tensNU j hj (Algebra.TensorProduct.map φ (AlgHom.id F E) z)) = (k (j 1) ⊗ₜ[F] (1 : E)) * z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add]

theorem mat_ext_ext_map (φ : R'' →ₐ[F] R) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (k : R' →ₗ[F] R'')
    (hk : ∀ a b, k (a * b) = k a * k b) (h : ∀ a, k (j (φ a)) = k (j 1) * a) (g : HA R'' σ J) :
    (HA.mat R'' σ J (extH σ J k hk (extH σ J j hj (mapH σ J φ g)))).1 =
      (k (j 1) ⊗ₜ[F] (1 : E)) • (HA.mat R'' σ J g).1 +
        (1 - k (j 1) ⊗ₜ[F] (1 : E)) • (1 : Matrix (Fin M) (Fin M) (R'' ⊗[F] E)) := by
  refine Matrix.ext fun r s => ?_
  have e1 : tensNU (E := E) k hk (tensNU (E := E) j hj 1) = k (j 1) ⊗ₜ[F] (1 : E) := by
    rw [Algebra.TensorProduct.one_def, tensNU_tmul, tensNU_tmul]
  rw [mat_extH, mat_extH, mat_mapH, map_add (f := _), tens_comp φ j hj k hk h, Matrix.add_apply, Matrix.smul_apply,
    Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases e : r = s
  · subst e
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, mul_one, mul_one, mul_one, map_sub, e1]
    ring
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, mul_zero, mul_zero, mul_zero, map_zero, zero_add, zero_add,
      add_zero]

theorem mix_mul {A l m n : Type} [CommRing A] [Fintype m] {b : A} (hb : b * b = b) (X X' : Matrix l m A)
    (Y Y' : Matrix m n A) :
    (b • X + (1 - b) • X') * (b • Y + (1 - b) • Y') = b • (X * Y) + (1 - b) • (X' * Y') := by
  have h1 : b * (1 - b) = 0 := by linear_combination -hb
  have h2 : (1 - b) * b = 0 := by linear_combination -hb
  have h3 : (1 - b) * (1 - b) = 1 - b := by linear_combination hb
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, hb, h1, h2, h3,
    zero_smul, add_zero, zero_add]

theorem mix_act {A m n : Type} [CommRing A] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {b : A}
    (hb : b * b = b) (X : Matrix m m A) (w : Matrix m n A) (Y : Matrix n n A) :
    (b • X + (1 - b) • (1 : Matrix m m A)) * w * (b • Y + (1 - b) • (1 : Matrix n n A)) =
      b • (X * w * Y) + (1 - b) • w := by
  have e : w = b • w + (1 - b) • w := by rw [← add_smul, add_sub_cancel, one_smul]
  conv_lhs => rw [e]
  rw [mix_mul hb, mix_mul hb, Matrix.one_mul, Matrix.mul_one]

theorem mix_act_smul {A m n : Type} [CommRing A] [Fintype m] [Fintype n] {b : A}
    (hb : b * b = b) (X : Matrix m m A) (w : Matrix m n A) (Y : Matrix n n A) :
    b • (X * w * Y) = b • (X * (b • w) * Y) + (1 - b) • b • w := by
  have h2 : (1 - b) * b = 0 := by linear_combination -hb
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul, hb, h2, zero_smul, add_zero]

end General

variable {D : D7}

theorem mt_gAt (V : HSp D) (p : Place D) (g : GA D V) :
    Formalism.L2.Theta.mt V (gAt V p g) =
      idem D p • Formalism.L2.Theta.mt V g + (1 - idem D p) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  classical
  cases p with
  | inl v =>
    refine mat_ext_ext_map (R'' := AF D.host.F) D.sp.cm.sig V.gram (GlobalTheory.AdelicU.evFin D.host.F v)
      (GlobalTheory.AdelicU.singleFin v) (GlobalTheory.AdelicU.singleFin_mul v)
      (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) (fun _ _ => Prod.ext (mul_zero _).symm rfl) (fun a => ?_) g
    refine Prod.ext (zero_mul _).symm (GlobalTheory.AdelicU.af_ext fun u => ?_)
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ u (GlobalTheory.AdelicU.singleFin v _) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ u (GlobalTheory.AdelicU.singleFin v 1 * a.2)
    rw [map_mul]
    by_cases e : u = v
    · subst e
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e, GlobalTheory.AdelicU.evalV_singleFin_ne e, zero_mul]
  | inr τ =>
    refine mat_ext_ext_map (R'' := AF D.host.F) D.sp.cm.sig V.gram (GlobalTheory.AdelicU.evInf D.host.F (plTau D τ))
      (GlobalTheory.AutFunCompare.sgW (plTau D τ)) (GlobalTheory.AutFunCompare.sgW_mul _)
      (LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)) (fun _ _ => Prod.ext rfl (mul_zero _).symm) (fun a => ?_) g
    refine Prod.ext (funext fun u => ?_) (zero_mul _).symm
    change (Pi.single (M := fun w : InfinitePlace D.host.F => w.Completion) (plTau D τ) (a.1 (plTau D τ))) u =
      (Pi.single (M := fun w : InfinitePlace D.host.F => w.Completion) (plTau D τ) 1) u * a.1 u
    by_cases e : u = plTau D τ
    · subst e
      rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
    · rw [Pi.single_eq_of_ne e, Pi.single_eq_of_ne e, zero_mul]

theorem idem_mul_self (p : Place D) : idem D p * idem D p = idem D p := by
  cases p with
  | inl v =>
    change algebraMap (AF D.host.F) (AE D) _ * algebraMap (AF D.host.F) (AE D) _ = algebraMap (AF D.host.F) (AE D) _
    rw [← map_mul]
    refine congrArg _ (Prod.ext (mul_zero _) ?_)
    exact (GlobalTheory.AdelicU.singleFin_mul v 1 1).symm.trans (by rw [mul_one]; rfl)
  | inr τ =>
    change algebraMap (AF D.host.F) (AE D) _ * algebraMap (AF D.host.F) (AE D) _ = algebraMap (AF D.host.F) (AE D) _
    rw [← map_mul]
    refine congrArg _ (Prod.ext ?_ (mul_zero _))
    exact (GlobalTheory.AutFunCompare.sgW_mul (plTau D τ) 1 1).symm.trans (by rw [mul_one]; rfl)

theorem gAt_gAt_self (V : HSp D) (p : Place D) (g : GA D V) : gAt V p (gAt V p g) = gAt V p g := by
  cases p <;> simp [gAt]

theorem gAt_gAt_ne (V : HSp D) (p : Place D) (g : GA D V) (q : Place D) (h : q ≠ p) : gAt V q (gAt V p g) = 1 := by
  cases p with
  | inl v =>
    cases q with
    | inl u =>
      have e : u ≠ v := fun e => h (congrArg _ e)
      simp only [gAt]
      rw [GlobalTheory.AdelicU.proj_emb_ne _ _ e, map_one]
    | inr ρ => simp [gAt]
  | inr τ =>
    cases q with
    | inl u => simp [gAt]
    | inr ρ =>
      have e : plTau D ρ ≠ plTau D τ := fun e => h (congrArg _ ((GlobalTheory.AdelicU.placeOf_bijective D).1 e))
      simp only [gAt]
      rw [GlobalTheory.AdelicU.projArch_embArch_ne _ _ e, map_one]

theorem actO_gAt (S T : HSp D) (p : Place D) (g : GA D S) (h : GA D T) (w : WO S T) :
    actO S T (gAt S p g) (gAt T p h) w = idem D p • actO S T g h w + (1 - idem D p) • w := by
  unfold actO
  rw [← gAt_inv, mt_gAt, mt_gAt]
  exact mix_act (idem_mul_self p) _ _ _

theorem wAt_actO (S T : HSp D) (p : Place D) (g : GA D S) (h : GA D T) (w : WO S T) :
    wAt p (actO S T g h w) = actO S T (gAt S p g) (gAt T p h) (wAt p w) := by
  rw [actO_gAt]
  exact mix_act_smul (idem_mul_self p) _ _ _

theorem gAt_laws : ∀ (D : D7), (∀ (V : HSp D) (p : Place D) (g : GA D V), Formalism.L2.Theta.mt V (gAt V p g) = idem D p • Formalism.L2.Theta.mt V g + (1 - idem D p) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) ∧ gAt V p (gAt V p g) = gAt V p g ∧ ∀ q, q ≠ p → gAt V q (gAt V p g) = 1) ∧ ∀ (S T : HSp D) (p : Place D) (g : GA D S) (h : GA D T) (w : WO S T), actO S T (gAt S p g) (gAt T p h) w = idem D p • actO S T g h w + (1 - idem D p) • w ∧ wAt p (actO S T g h w) = actO S T (gAt S p g) (gAt T p h) (wAt p w) :=
  fun _ => ⟨fun V p g => ⟨mt_gAt V p g, gAt_gAt_self V p g, gAt_gAt_ne V p g⟩,
    fun S T p g h w => ⟨actO_gAt S T p g h w, wAt_actO S T p g h w⟩⟩

end GlobalTheory.PlaceComponent

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryComponentAtPlaceLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitaryComponentAtPlace_laws : ∀ (D : D7), (∀ (V : HSp D) (p : Place D) (g : GA D V), Formalism.L2.Theta.mt V (gAt V p g) = idem D p • Formalism.L2.Theta.mt V g + (1 - idem D p) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) ∧ gAt V p (gAt V p g) = gAt V p g ∧ ∀ q, q ≠ p → gAt V q (gAt V p g) = 1) ∧ ∀ (S T : HSp D) (p : Place D) (g : GA D S) (h : GA D T) (w : WO S T), actO S T (gAt S p g) (gAt T p h) w = idem D p • actO S T g h w + (1 - idem D p) • w ∧ wAt p (actO S T g h w) = actO S T (gAt S p g) (gAt T p h) (wAt p w) := by
  first | exact @GlobalTheory.PlaceComponent.gAt_laws | exact GlobalTheory.PlaceComponent.gAt_laws | (intros; apply GlobalTheory.PlaceComponent.gAt_laws <;> assumption)
end
end
