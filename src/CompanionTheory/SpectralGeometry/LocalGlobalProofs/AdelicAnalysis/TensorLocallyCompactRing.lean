module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.TopK

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]


omit [IsTopologicalRing R] in
theorem isModTop : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

def coordHomeo {d : ℕ} (b : Module.Basis (Fin d) F E) : (R ⊗[F] E) ≃ₜ (Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { (Algebra.TensorProduct.basis R b).equivFun.toEquiv with
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

theorem isHomeomorph_coord {d : ℕ} (b : Module.Basis (Fin d) F E) :
    IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k :=
  (coordHomeo R b).isHomeomorph

theorem isTopRing [Module.Finite F E] : IsTopologicalRing (R ⊗[F] E) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

omit [IsTopologicalRing R] in
theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap

theorem continuous_trace [Module.Finite F E] : Continuous (Algebra.trace R (R ⊗[F] E)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  exact IsModuleTopology.continuous_of_linearMap _

end

theorem topTens_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R], IsTopologicalRing (R ⊗[F] E) ∧ LocallyCompactSpace (R ⊗[F] E) ∧ SecondCountableTopology (R ⊗[F] E) ∧ T2Space (R ⊗[F] E) ∧ Continuous (sigR R σ) ∧ Continuous (Algebra.trace R (R ⊗[F] E)) ∧ (∀ (d : ℕ) (b : Module.Basis (Fin d) F E), IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k) ∧ (∀ n M : ℕ, BorelSpace (Fin n → Fin M → R ⊗[F] E)) ∧ (∀ n : ℕ, IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E)))) ∧ (∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), Continuous (gramR R σ J : (Fin n → Fin M → R ⊗[F] E) → _)) := by
  intro F E _ _ _ _ _ σ _ R _ _ _ _ _ _ _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have e := coordHomeo R (Module.finBasis F E)
  haveI h1 : IsTopologicalRing (R ⊗[F] E) := isTopRing R
  haveI h2 : LocallyCompactSpace (R ⊗[F] E) := e.isOpenEmbedding.locallyCompactSpace
  haveI h3 : SecondCountableTopology (R ⊗[F] E) := e.secondCountableTopology
  haveI h4 : T2Space (R ⊗[F] E) := e.isEmbedding.t2Space
  haveI h5 : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hs := continuous_sigR R σ
  refine ⟨h1, h2, h3, h4, hs, continuous_trace R, fun d b => isHomeomorph_coord R b,
    fun n M => inferInstance, fun n => ?_, fun n M J => ?_⟩
  · have : (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
        ⋂ a, ⋂ b, {S | sigR R σ (S b a) = S a b} := by
      ext S
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      rfl
    rw [this]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ?_ ?_
    · exact hs.comp (continuous_id.matrix_elem b a)
    · exact continuous_id.matrix_elem a b
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    unfold gramR hR hform
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact ((hs.comp ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul
      ((continuous_apply j).comp (continuous_apply b))

end GlobalTheory.CompanionTheory.SW.TopK
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_locally_compact_ring : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R], IsTopologicalRing (R ⊗[F] E) ∧ LocallyCompactSpace (R ⊗[F] E) ∧ SecondCountableTopology (R ⊗[F] E) ∧ T2Space (R ⊗[F] E) ∧ Continuous (sigR R σ) ∧ Continuous (Algebra.trace R (R ⊗[F] E)) ∧ (∀ (d : ℕ) (b : Module.Basis (Fin d) F E), IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k) ∧ (∀ n M : ℕ, BorelSpace (Fin n → Fin M → R ⊗[F] E)) ∧ (∀ n : ℕ, IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E)))) ∧ (∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), Continuous (gramR R σ J : (Fin n → Fin M → R ⊗[F] E) → _)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.TopK.topTens_props | exact GlobalTheory.CompanionTheory.SW.TopK.topTens_props | (intros; apply GlobalTheory.CompanionTheory.SW.TopK.topTens_props <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HermTop

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

section

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_sigR {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) :
    sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, h]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem sigR_inclR (σ : E →ₐ[F] E) (x : E) : sigR R σ (inclR R x) = inclR R (σ x) := by
  simp [sigR, inclR]

theorem gramR_mem {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) {n M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X ∈ HermR R σ n := by
  intro a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramR, hR, hform, JR, Matrix.map_apply, map_sum, map_mul, sigR_sigR R h, sigR_inclR, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem isModTop : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

theorem isTopRing [Module.Finite F E] : IsTopologicalRing (R ⊗[F] E) :=
  haveI := isModTop (F := F) (E := E) R
  IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

theorem exists_homeo [Module.Finite F E] :
    Nonempty ((R ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → R)) := by
  haveI := isModTop (F := F) (E := E) R
  haveI := isTopRing (F := F) (E := E) R
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  exact ⟨{ e.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }⟩

theorem continuous_sigR [Module.Finite F E] (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI := isModTop (F := F) (E := E) R
  haveI := isTopRing (F := F) (E := E) R
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap

end

theorem herm_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ n : ℕ, LocallyCompactSpace (HermR R σ n) ∧ SecondCountableTopology (HermR R σ n) ∧ T2Space (HermR R σ n) ∧ BorelSpace (HermR R σ n) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ g : (Fin n → Fin M → R ⊗[F] E) → HermR R σ n, Continuous g ∧ ∀ X, gramR R σ J X = (g X : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ n
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  haveI := isTopRing (F := F) (E := E) R
  obtain ⟨e⟩ := exists_homeo (F := F) (E := E) R
  haveI : LocallyCompactSpace (R ⊗[F] E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (R ⊗[F] E) := e.secondCountableTopology
  haveI : T2Space (R ⊗[F] E) := e.isEmbedding.t2Space
  have hs := continuous_sigR R σ
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R ⊗[F] E))
  have hc : IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
    have : (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
        ⋂ a, ⋂ b, {S | sigR R σ (S b a) = S a b} := by
      ext S
      simp only [Set.mem_iInter]
      rfl
    rw [this]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ?_ ?_
    · exact hs.comp (continuous_id.matrix_elem b a)
    · exact continuous_id.matrix_elem a b
  refine ⟨hc.locallyCompactSpace, ?_, inferInstance, ⟨rfl⟩, ?_⟩
  · exact TopologicalSpace.Subtype.secondCountableTopology _
  · intro M J hJ
    refine ⟨fun X => ⟨gramR R σ J X, gramR_mem R (sigma_sigma hσ) hJ.1 X⟩, ?_, fun _ => rfl⟩
    refine Continuous.subtype_mk ?_ _
    refine continuous_matrix fun a b => ?_
    simp only [gramR, hR, hform]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    refine ((hs.comp ?_).mul continuous_const).mul ?_
    · exact (continuous_apply i).comp (continuous_apply a)
    · exact (continuous_apply j).comp (continuous_apply b)

end GlobalTheory.CompanionTheory.SW.HermTop
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_matrices_locally_compact_borel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ n : ℕ, LocallyCompactSpace (HermR R σ n) ∧ SecondCountableTopology (HermR R σ n) ∧ T2Space (HermR R σ n) ∧ BorelSpace (HermR R σ n) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ g : (Fin n → Fin M → R ⊗[F] E) → HermR R σ n, Continuous g ∧ ∀ X, gramR R σ J X = (g X : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.HermTop.herm_top | exact GlobalTheory.CompanionTheory.SW.HermTop.herm_top | (intros; apply GlobalTheory.CompanionTheory.SW.HermTop.herm_top <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LocInf

def posU (ι : Type) : Subgroup (ι → ℝ)ˣ where
  carrier := {u | ∀ i, 0 < (u : ι → ℝ) i}
  mul_mem' := fun {a b} ha hb i => by
    simpa using mul_pos (ha i) (hb i)
  one_mem' := fun i => by simp
  inv_mem' := by
    intro u hu i
    have h1 : ((u⁻¹ : (ι → ℝ)ˣ) : ι → ℝ) i * (u : ι → ℝ) i = 1 := by
      have := congrFun (u.inv_mul) i
      simpa using this
    exact (pos_iff_pos_of_mul_pos (h1 ▸ one_pos)).2 (hu i)

theorem isOpen_pos (ι : Type) [Finite ι] : IsOpen {x : ι → ℝ | ∀ i, 0 < x i} := by
  have h1 : {x : ι → ℝ | ∀ i, 0 < x i} = ⋂ i, {x : ι → ℝ | 0 < x i} := by
    ext x
    simp
  rw [h1]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)

theorem isOpen_posU (ι : Type) [Fintype ι] : IsOpen (posU ι : Set (ι → ℝ)ˣ) :=
  (isOpen_pos ι).preimage Units.continuous_val

theorem isOpenEmbedding_sq (ι : Type) [Fintype ι] :
    IsOpenEmbedding (fun u : posU ι => ((u : (ι → ℝ)ˣ) ^ 2 : (ι → ℝ)ˣ)) := by
  have hv : IsOpenEmbedding (Units.val : (ι → ℝ)ˣ → (ι → ℝ)) := Units.isOpenEmbedding_val
  refine (IsOpenEmbedding.of_comp_iff _ hv).1 ?_
  set j : posU ι → (ι → ℝ) := fun u => ((u : (ι → ℝ)ˣ) : ι → ℝ) with hjdef
  have hj : IsOpenEmbedding j := hv.comp (isOpen_posU ι).isOpenEmbedding_subtypeVal
  set g : posU ι → (ι → ℝ) := Units.val ∘ (fun u : posU ι => ((u : (ι → ℝ)ˣ) ^ 2 : (ι → ℝ)ˣ)) with hgdef
  have hg : Continuous g :=
    Units.continuous_val.comp (continuous_subtype_val.pow 2)
  let r : (ι → ℝ) → (ι → ℝ) := fun x i => Real.sqrt (x i)
  have hr : Continuous r := continuous_pi fun i => (continuous_apply i).sqrt
  have hrg : r ∘ g = j := by
    funext u i
    have hu : 0 < ((u : (ι → ℝ)ˣ) : ι → ℝ) i := u.2 i
    simp [r, g, j, Real.sqrt_sq hu.le]
  have hind : IsInducing g := IsInducing.of_comp hg hr (by rw [hrg]; exact hj.isInducing)
  have hinj : Function.Injective g := Function.Injective.of_comp (f := r) (by rw [hrg]; exact hj.injective)
  have hrange : Set.range g = {x : ι → ℝ | ∀ i, 0 < x i} := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩ i
      have hu : 0 < ((u : (ι → ℝ)ˣ) : ι → ℝ) i := u.2 i
      simpa [g] using pow_pos hu 2
    · intro hx
      have hs : ∀ i, 0 < Real.sqrt (x i) := fun i => Real.sqrt_pos.2 (hx i)
      let w : (ι → ℝ)ˣ :=
        ⟨fun i => Real.sqrt (x i), fun i => (Real.sqrt (x i))⁻¹,
          by funext i; simp [(hs i).ne'], by funext i; simp [(hs i).ne']⟩
      refine ⟨⟨w, fun i => hs i⟩, ?_⟩
      funext i
      simp [g, w, Real.sq_sqrt (hx i).le]
  exact ⟨⟨hind, hinj⟩, by rw [hrange]; exact isOpen_pos ι⟩

variable (F : Type) [Field F] [NumberField F]

def eInf (h : IsTotallyReal F) : Ainf F ≃+* (InfinitePlace F → ℝ) :=
  RingEquiv.piCongrRight fun w => InfinitePlace.Completion.ringEquivRealOfIsReal (h.isReal w)

omit [NumberField F] in
theorem continuous_eInf (h : IsTotallyReal F) : Continuous (eInf F h) := by
  show Continuous (fun (x : ∀ w : InfinitePlace F, w.Completion) (w : InfinitePlace F) =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (h.isReal w) (x w))
  exact continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (h.isReal w)).continuous.comp (continuous_apply w)

omit [NumberField F] in
theorem continuous_eInf_symm (h : IsTotallyReal F) : Continuous (eInf F h).symm := by
  show Continuous (fun (x : InfinitePlace F → ℝ) (w : InfinitePlace F) =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (h.isReal w)).symm (x w))
  exact continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (h.isReal w)).symm.continuous.comp (continuous_apply w)

def hInf (h : IsTotallyReal F) : Ainf F ≃ₜ (InfinitePlace F → ℝ) where
  toEquiv := (eInf F h).toEquiv
  continuous_toFun := continuous_eInf F h
  continuous_invFun := continuous_eInf_symm F h

def uInf (h : IsTotallyReal F) : (Ainf F)ˣ ≃ₜ (InfinitePlace F → ℝ)ˣ where
  toEquiv := (Units.mapEquiv (eInf F h).toMulEquiv).toEquiv
  continuous_toFun := Continuous.units_map _ (continuous_eInf F h)
  continuous_invFun := Continuous.units_map _ (continuous_eInf_symm F h)

end GlobalTheory.CompanionTheory.SW.LocInf


open GlobalTheory.CompanionTheory.SW.LocInf in
theorem GlobalTheory.CompanionTheory.SW.isLocR_Ainf : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → IsLocR (Ainf F) := by
  intro F _ _ h
  have hT2 : T2Space (Ainf F) := inferInstanceAs (T2Space (∀ w : InfinitePlace F, w.Completion))
  have hSC : SecondCountableTopology (Ainf F) := (hInf F h).secondCountableTopology
  have hArt : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing (∀ w : InfinitePlace F, w.Completion))
  have hRed : IsReduced (Ainf F) := inferInstanceAs (IsReduced (∀ w : InfinitePlace F, w.Completion))
  have hval : IsOpenEmbedding (Units.val : (Ainf F)ˣ → Ainf F) := by
    have h1 : IsOpenEmbedding (Units.val : (InfinitePlace F → ℝ)ˣ → (InfinitePlace F → ℝ)) :=
      Units.isOpenEmbedding_val
    have h2 := ((hInf F h).symm.isOpenEmbedding.comp h1).comp (uInf F h).isOpenEmbedding
    convert h2 using 1
    funext u
    exact ((eInf F h).symm_apply_apply _).symm
  refine ⟨inferInstance, inferInstance, hSC, hT2, hArt, hRed, hval,
    (posU (InfinitePlace F)).comap (Units.map (eInf F h).toMonoidHom), ?_, ?_⟩
  · exact (isOpen_posU (InfinitePlace F)).preimage (uInf F h).continuous
  · let S := (posU (InfinitePlace F)).comap (Units.map (eInf F h).toMonoidHom)
    let T : S ≃ₜ posU (InfinitePlace F) :=
      (uInf F h).subtype (fun x => Iff.rfl)
    have h2 := ((uInf F h).symm.isOpenEmbedding.comp (isOpenEmbedding_sq (InfinitePlace F))).comp
      T.isOpenEmbedding
    convert h2 using 1
    funext u
    apply (uInf F h).injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    exact map_pow (Units.map (eInf F h).toMonoidHom) (u : (Ainf F)ˣ) 2
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_adeles_local_ring_totally_real : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → IsLocR (Ainf F) := by
  first | exact @GlobalTheory.CompanionTheory.SW.isLocR_Ainf | exact GlobalTheory.CompanionTheory.SW.isLocR_Ainf | (intros; apply GlobalTheory.CompanionTheory.SW.isLocR_Ainf <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def cv (R : Type) [CommRing R] [Algebra F R] {d M : ℕ} (b : Module.Basis (Fin d) F E)
    (x : Fin M → R ⊗[F] E) : Fin M × Fin d → R :=
  fun p => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2

def gmat (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {d M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) (h : HA R σ J) :
    Matrix (Fin M × Fin d) (Fin M × Fin d) R :=
  fun p q => (Algebra.TensorProduct.basis R b).repr
    ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) p.1 q.1 * inclR R (b q.2)) p.2

def ofF {d M : ℕ} (b : Module.Basis (Fin d) F E) (x : Fin M × Fin d → F) : Fin 1 → Fin M → E :=
  fun _ i => ∑ k, x (i, k) • b k

end Coord

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def gfin (σ : E →ₐ[F] E) {d M : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (h : HA (AF F) σ J) : Matrix (Fin M × Fin d) (Fin M × Fin d) (Af F) :=
  (gmat (AF F) σ J b h⁻¹).map (sndA F)

def ginf (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (σ : E →ₐ[F] E) {d M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) (h : HA (AF F) σ J)
    (w : InfinitePlace F) : Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ :=
  (gmat (AF F) σ J b h⁻¹).map fun t => e (fstA F t) w

def xw (e : Ainf F ≃+* (InfinitePlace F → ℝ)) {d M : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin 1 → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) : Fin M × Fin d → ℝ :=
  fun p => e (cv (Ainf F) b (X 0) p) w

def gaussQ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) {d M : ℕ} (b : Module.Basis (Fin d) F E)
    (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ)
    (X : Fin 1 → Fin M → Ainf F ⊗[F] E) : ℝ :=
  Real.exp (-Real.pi * ∑ w, xw e b X w ⬝ᵥ (Pm w *ᵥ xw e b X w))

def prH {G : Type} [MeasurableSpace G] (μ : Measure G) (𝓕 : Set G) : Measure G :=
  (μ 𝓕)⁻¹ • μ.restrict 𝓕

end Adelic

end GlobalTheory.CompanionTheory.SW.BB
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RealCoord

open InfinitePlace InfinitePlace.Completion

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def rho (w : InfinitePlace F) : F →+* ℝ := embedding_of_isReal (IsTotallyReal.isReal w)

def coord : Ainf F ≃+* (InfinitePlace F → ℝ) :=
  RingEquiv.piCongrRight (R := fun w : InfinitePlace F => w.Completion) (S := fun _ => ℝ)
    (fun w => ringEquivRealOfIsReal (IsTotallyReal.isReal w))

theorem coord_apply (y : Ainf F) (w : InfinitePlace F) :
    coord F y w = ringEquivRealOfIsReal (IsTotallyReal.isReal w) (y w) := rfl

def coordHomeo : Ainf F ≃ₜ (InfinitePlace F → ℝ) :=
  Homeomorph.piCongrRight (Y₁ := fun w : InfinitePlace F => w.Completion) (Y₂ := fun _ => ℝ)
    (fun w => (isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).toHomeomorph)

theorem coordHomeo_coe : ⇑(coordHomeo F) = ⇑(coord F) := rfl

theorem isHomeomorph_coord : IsHomeomorph (coord F) := (coordHomeo F).isHomeomorph

theorem abs_coord (y : Ainf F) (w : InfinitePlace F) : |coord F y w| = ‖y w‖ := by
  have h := (isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).isometry.norm_map_of_map_zero
    (map_zero (ringEquivRealOfIsReal (IsTotallyReal.isReal w))) (y w)
  exact h

theorem rho_coe (w : InfinitePlace F) (x : F) : ((rho F w x : ℝ) : ℂ) = w.embedding x :=
  embedding_of_isReal_apply _ _

theorem coord_algebraMap (x : F) (w : InfinitePlace F) :
    coord F (algebraMap F (Ainf F) x) w = rho F w x := by
  have h : ((coord F (algebraMap F (Ainf F) x) w : ℝ) : ℂ) = ((rho F w x : ℝ) : ℂ) := by
    rw [rho_coe, coord_apply, InfiniteAdeleRing.algebraMap_apply, ringEquivRealOfIsReal_apply,
      extensionEmbeddingOfIsReal_apply]
    exact extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)
  exact Complex.ofReal_injective h

instance : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
  ⟨fun w => not_isReal_iff_isComplex.mpr w.2 (IsTotallyReal.isReal w.1)⟩

def toMixed (y : InfinitePlace F → ℝ) : mixedEmbedding.mixedSpace F :=
  (fun w => y w.1, 0)

theorem toMixed_add (y z : InfinitePlace F → ℝ) : toMixed F (y + z) = toMixed F y + toMixed F z := by
  refine Prod.ext rfl ?_
  simp [toMixed]

theorem toMixed_injective : Function.Injective (toMixed F) := by
  intro y z h
  funext w
  exact congrFun (congrArg Prod.fst h) ⟨w, IsTotallyReal.isReal w⟩

theorem toMixed_coord_algebraMap (x : F) :
    toMixed F (coord F (algebraMap F (Ainf F) x)) = mixedEmbedding F x := by
  refine Prod.ext ?_ (Subsingleton.elim _ _)
  funext w
  rw [mixedEmbedding.mixedEmbedding_apply_isReal]
  exact coord_algebraMap F x w.1

open scoped Classical in
theorem measurePreserving_toMixed : MeasurePreserving (toMixed F) volume volume := by
  let f : {w : InfinitePlace F // w.IsReal} ≃ InfinitePlace F :=
    Equiv.subtypeUnivEquiv IsTotallyReal.isReal
  have h1 := (volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace F => ℝ) f).symm
  have h2 : MeasurePreserving (fun y : InfinitePlace F → ℝ => fun w : {w : InfinitePlace F // w.IsReal} => y w.1)
      volume volume := by
    convert h1 using 1
    funext y w
    rfl
  refine ⟨?_, ?_⟩
  · exact h2.measurable.prodMk measurable_const
  · have hm : Measurable (fun x : {w : InfinitePlace F // w.IsReal} → ℝ =>
        (x, (0 : {w : InfinitePlace F // w.IsComplex} → ℂ))) := by fun_prop
    rw [Measure.volume_eq_prod, volume_pi (α := fun _ : {w : InfinitePlace F // w.IsComplex} => ℂ),
      Measure.pi_of_empty _ (0 : {w : InfinitePlace F // w.IsComplex} → ℂ), Measure.prod_dirac, ← h2.map_eq,
      Measure.map_map hm h2.measurable]
    rfl

theorem coord_measurable : Measurable (coord F) := by
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  exact (isHomeomorph_coord F).continuous.measurable

open scoped Classical in
theorem map_coord_eq (lam : Measure (Ainf F)) (hl : IsStdInf lam) :
    lam.map (coord F) = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) := by
  obtain ⟨hH, D, hD, hD1⟩ := hl
  haveI := hH
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : (lam.map (coord F)).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map lam (coord F).toAddEquiv (isHomeomorph_coord F).continuous
      (coordHomeo F).symm.continuous
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, lam.map (coord F) = c • (volume : Measure (InfinitePlace F → ℝ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  set P := ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F) with hP
  have hmp := measurePreserving_toMixed F
  have hPm : MeasurableSet P := ZSpan.fundamentalDomain_measurableSet _
  set Λ := mixedEmbedding.integerLattice F with hΛdef
  set Γ : AddSubgroup (Ainf F) :=
    ((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom.range with hΓ
  let Ψ : Ainf F → mixedEmbedding.mixedSpace F := fun y => toMixed F (coord F y)
  have hΨadd : ∀ x y, Ψ (x + y) = Ψ x + Ψ y := fun x y => by
    simp only [Ψ, map_add (f := _), toMixed_add]
  have hΨinj : Function.Injective Ψ := (toMixed_injective F).comp (coord F).injective
  have hΨalg : ∀ a : 𝓞 F, Ψ (algebraMap F (Ainf F) (algebraMap (𝓞 F) F a)) =
      mixedEmbedding F (algebraMap (𝓞 F) F a) := fun a => toMixed_coord_algebraMap F _
  have hΛmem : ∀ g : Λ, ∃ a : 𝓞 F, (g : mixedEmbedding.mixedSpace F) =
      mixedEmbedding F (algebraMap (𝓞 F) F a) := by
    rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩
  have hΛmem' : ∀ a : 𝓞 F, mixedEmbedding F (algebraMap (𝓞 F) F a) ∈ Λ :=
    fun a => ⟨a, rfl⟩
  choose a ha using hΛmem
  let m : Λ → Γ := fun g => ⟨algebraMap F (Ainf F) (algebraMap (𝓞 F) F (a g)), ⟨a g, rfl⟩⟩
  have hmΨ : ∀ g : Λ, Ψ (m g : Ainf F) = g := fun g => by
    rw [ha g]; exact hΨalg _
  have hmbij : Function.Bijective m := by
    refine ⟨fun g g' h => ?_, ?_⟩
    · apply Subtype.ext
      rw [← hmΨ g, ← hmΨ g', h]
    · rintro ⟨_, b, rfl⟩
      refine ⟨⟨_, hΛmem' b⟩, Subtype.ext (hΨinj ?_)⟩
      rw [hmΨ]
      exact (hΨalg b).symm
  have hq : Measure.QuasiMeasurePreserving Ψ lam volume := by
    refine hmp.quasiMeasurePreserving.comp ⟨(coord_measurable F).aemeasurable, ?_⟩
    rw [hc]
    intro s hs
    simp [hs]
  have hFD : IsAddFundamentalDomain Γ (Ψ ⁻¹' P) lam :=
    (mixedEmbedding.fundamentalDomain_integerLattice F).preimage_of_equiv hq hmbij (fun g x => by
      change Ψ ((m g : Ainf F) + x) = (g : mixedEmbedding.mixedSpace F) + Ψ x
      rw [hΨadd, hmΨ])
  haveI : Countable Γ := hmbij.surjective.countable
  have h1 : lam (Ψ ⁻¹' P) = 1 := by
    rw [← hD1]
    exact hFD.measure_eq hD
  have hQm : MeasurableSet (toMixed F ⁻¹' P) := hmp.measurable hPm
  have h2 : (c : ℝ≥0∞) * volume (toMixed F ⁻¹' P) = 1 := by
    have := Measure.map_apply (μ := lam) (coord_measurable F) hQm
    rw [hc] at this
    have e : Ψ ⁻¹' P = coord F ⁻¹' (toMixed F ⁻¹' P) := rfl
    rw [← h1, e]
    simpa using this
  have h3 : volume (toMixed F ⁻¹' P) = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) := by
    rw [hmp.measure_preimage hPm.nullMeasurableSet, hP, mixedEmbedding.volume_fundamentalDomain_latticeBasis,
      IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, one_mul,
      ← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  have hd : 0 < Real.sqrt |(discr F : ℝ)| := by
    have : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
    positivity
  rw [h3] at h2
  have h4 : (c : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hd]
    exact ENNReal.eq_inv_of_mul_eq_one_left h2
  rw [hc, ← h4]
  rfl

end GlobalTheory.CompanionTheory.SW.RealCoord

open GlobalTheory.CompanionTheory.SW.RealCoord in
theorem GlobalTheory.CompanionTheory.SW.real_iso : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∃ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) ∧ IsHomeomorph e ∧ (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) ∧ (∀ y w, |e y w| = ‖y w‖) ∧ ∀ lam : Measure (Ainf F), IsStdInf lam → lam.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) := by
  intro F _ _ hF
  haveI := hF
  exact ⟨rho F, coord F, rho_coe F, isHomeomorph_coord F, coord_algebraMap F, abs_coord F, map_coord_eq F⟩
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∃ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) ∧ IsHomeomorph e ∧ (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) ∧ (∀ y w, |e y w| = ‖y w‖) ∧ ∀ lam : Measure (Ainf F), IsStdInf lam → lam.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.real_iso | exact GlobalTheory.CompanionTheory.SW.real_iso | (intros; apply GlobalTheory.CompanionTheory.SW.real_iso <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

def vec {K : Type} [Zero K] {M n : ℕ} (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) :
    Fin (n + 1) → Fin (M + 1) → K :=
  Fin.cons (Fin.cons α (fun _ => 0)) (fun j => Fin.cons (c j) (X j))

def scl {K : Type} [Mul K] {N n : ℕ} (u : K) (y : Fin n → Fin N → K) : Fin n → Fin N → K :=
  fun a i => y a i * u

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def s0 {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (S 0 0)

def cvec {n : ℕ} (t : F) (a : R → Rˣ) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) :
    Fin n → R ⊗[F] E :=
  fun j => ((((a (s0 R S))⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * S 0 j.succ

def schurM (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  fun i j => S i.succ j.succ -
    sigR R σ (cvec R t a S i) * inclR R (algebraMap F E t) * cvec R t a S j


open scoped Classical in
open Classical in
def schur (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ) (S : HermR R σ (n + 1)) : HermR R σ n :=
  if h : schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n then ⟨_, h⟩ else 0

theorem schur_coe (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ) (S : HermR R σ (n + 1))
    (h : schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n) :
    (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = schurM R σ t a S := by
  simp [schur, h]

def Bset (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ) (B₀ : Set R) : Set (HermR R σ (n + 1)) :=
  {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀ ∧
    IsUnit (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}

end Alg

section Meas

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) {n : ℕ}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
  (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
  (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
  (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
  (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0)

def fibS (S : HermR R σ (n + 1)) : Measure (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
  (Bset R σ t a B₀).indicator (fun S : HermR R σ (n + 1) =>
    (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) *
        cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n) •
      ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map (fun p =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1)
          (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
            (cvec R t a S) p.2))) S

def Pint (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (α : R) (c : Fin n → R ⊗[F] E)
    (S' : HermR R σ n) : ℝ≥0∞ :=
  ∫⁻ y₀, ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (α ⊗ₜ[F] (1 : E)) c X)) ∂(m' S')
    ∂(m₁ (hermScal R σ (algebraMap F R t)))

def Preal (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ) (α : R) (c : Fin n → R ⊗[F] E)
    (S' : HermR R σ n) : ℝ :=
  ∫ y₀, ∫ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (α ⊗ₜ[F] (1 : E)) c X)) ∂(m' S')
    ∂(m₁ (hermScal R σ (algebraMap F R t)))

def sTil (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) : HA R σ (blockOne (algebraMap F E t) J) :=
  s (scl ((((a (s0 R (gramR R σ (blockOne (algebraMap F E t) J) y)))⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E)) y)

def chi {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) : ℝ≥0∞ :=
  ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E,
    φ (Fin.cons (y 0) (actW R σ (blockOne (algebraMap F E t) J) (sTil σ J t s a y)
      (fun j => Fin.cons (c j) (X j)))) ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam)

def Uset (B₀ : Set R) (a : R → Rˣ) : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
  gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' Bset R σ t a B₀)

def Unt (R : Type) [CommRing R] [Algebra F R] (n : ℕ) : Set (HermR R σ n) :=
  {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}

def Mid {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S' in Unt σ R n,
    Pint σ J t m₁ m' s φ ((a x : Rˣ) : R) c S' ∂(coordHerm R σ b lam n)
    ∂(Measure.pi fun _ => coordK R b lam) ∂lam

end Meas

section Data

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure StageData (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ)
    {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
    (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
    (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0) : Prop where
  hCM : IsCMExt F E σ
  hJ : IsHermND σ J
  ht : t ≠ 0
  hR : IsLocR R
  hlam : lam.IsAddHaarMeasure
  hm₁ : IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁
  hm' : IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m'
  hs : Measurable s
  hsec : ∀ y, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) →
    actW R σ _ (s y) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = y
  hcpt : ∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C →
    ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C,
      gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C'
  hB₀ : IsOpen B₀
  htB : algebraMap F R t ∈ B₀
  hac : ContinuousOn a B₀
  hoff : ∀ x, x ∉ B₀ → a x = 1
  hsq : ∀ x ∈ B₀, x = ((a x : Rˣ) : R) ^ 2 * algebraMap F R t
  ha1 : a (algebraMap F R t) = 1
  hκc : Continuous κ₁
  hκ1 : κ₁ 1 = 1
  hscale : ∀ u : Rˣ, m₁ (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) =
    κ₁ u • (m₁ (hermScal R σ (algebraMap F R t))).map (scl ((u : R) ⊗ₜ[F] (1 : E)))
  hcmc : Continuous cm
  hmod : ∀ u : Rˣ, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) = cm u • coordK R b lam

end Data

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentities
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentities
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramAlg

section Gen

variable {A : Type} [CommRing A] {M n : ℕ}

def colM (X : Fin n → Fin M → A) : Matrix (Fin M) (Fin n) A := fun i a => X a i

theorem colM_injective : Function.Injective (colM : (Fin n → Fin M → A) → _) := by
  intro X Y h
  funext a i
  exact congrFun (congrFun h i) a

theorem hform_eq_entry (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (X : Fin n → Fin M → A)
    (a b : Fin n) :
    hform s J (X a) (X b) = (cT s (colM X) * J * colM X) a b := by
  simp only [hform, Matrix.mul_apply, cT, colM, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem mul_shape {p q r s t u : Type} [Fintype q] [Fintype r] [Fintype s] [Fintype t]
    (a : Matrix p q A) (b : Matrix q r A) (c : Matrix r s A) (d : Matrix s t A) (e : Matrix t u A) :
    (((a * b : Matrix p r A) * c : Matrix p s A) * (d * e : Matrix s u A) : Matrix p u A) =
      ((a * ((b * c : Matrix q s A) * d : Matrix q t A) : Matrix p t A) * e : Matrix p u A) := by
  simp only [Matrix.mul_assoc]

theorem cT_cT (s : A →+* A) (hs : ∀ x, s (s x) = x) {m p : Type} (B : Matrix m p A) :
    cT s (cT s B) = B := by
  ext i j
  simp [cT, hs]

end Gen

section Conj

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigma_invol [NumberField F] [NumberField E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (x : E) :
    σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hσ.2.2.2 τ, hσ.2.2.2 τ, star_star]

variable (R : Type) [CommRing R] [Algebra F R]

theorem sigR_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, h]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

variable {M n : ℕ}

theorem gramR_eq (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X =
      (cT (sigR R σ) (colM X) * JR R J : Matrix (Fin n) (Fin M) (R ⊗[F] E)) * colM X := by
  ext a b
  exact hform_eq_entry _ _ X a b

theorem colM_rmul (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    colM (rmul R X g) = colM X * g := by
  ext i a
  simp [colM, rmul, Matrix.mul_apply]

theorem colM_actTup (g : GL (Fin M) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) :
    colM (actTup R g X) = (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * colM X := by
  ext i a
  simp [colM, actTup, Matrix.mulVec, dotProduct, Matrix.mul_apply]

end Conj

theorem gram_algebra : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (n : ℕ), (∀ (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g) ∧ (∀ (X : Fin n → Fin M → R ⊗[F] E) (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)), rmul R (rmul R X g) g' = rmul R X (g * g')) ∧ (∀ X : Fin n → Fin M → R ⊗[F] E, rmul R X 1 = X) ∧ (∀ (S : HermR R σ n) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g ∈ HermR R σ n) ∧ ∀ (J' : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) (R ⊗[F] E)), JR R J' = cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) → ∀ X : Fin n → Fin M → R ⊗[F] E, gramR R σ J (actTup R g X) = gramR R σ J' X := by
  intro F E _ _ _ _ _ σ hσ M J _ R _ _ n
  have hs : ∀ x : R ⊗[F] E, sigR R σ (sigR R σ x) = x := sigR_invol R (sigma_invol hσ)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X g
    rw [gramR_eq, gramR_eq, colM_rmul, cT_mul]
    exact mul_shape _ _ _ _ _
  · intro X g g'
    apply colM_injective
    rw [colM_rmul, colM_rmul, colM_rmul, Matrix.mul_assoc]
  · intro X
    apply colM_injective
    rw [colM_rmul, Matrix.mul_one]
  · intro S g
    have hS : cT (sigR R σ) (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = S := by
      ext a b
      exact S.2 a b
    have key : cT (sigR R σ) (cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g)
        = cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g := by
      rw [cT_mul, cT_mul, cT_cT _ hs, hS, Matrix.mul_assoc]
    intro a b
    exact congrFun (congrFun key a) b
  · intro J' g hJ X
    rw [gramR_eq, gramR_eq, colM_actTup, cT_mul, hJ]
    exact mul_shape _ _ _ _ _

end GlobalTheory.CompanionTheory.SW.GramAlg
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentitiesStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_right_action_identities : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (n : ℕ), (∀ (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g) ∧ (∀ (X : Fin n → Fin M → R ⊗[F] E) (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)), rmul R (rmul R X g) g' = rmul R X (g * g')) ∧ (∀ X : Fin n → Fin M → R ⊗[F] E, rmul R X 1 = X) ∧ (∀ (S : HermR R σ n) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g ∈ HermR R σ n) ∧ ∀ (J' : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) (R ⊗[F] E)), JR R J' = cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) → ∀ X : Fin n → Fin M → R ⊗[F] E, gramR R σ J (actTup R g X) = gramR R σ J' X := by
  first | exact @GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra | exact GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra | (intros; apply GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra <;> assumption)
end
end
