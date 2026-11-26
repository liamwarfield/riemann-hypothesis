module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousLvMat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePlaceVacuumAnyDarbouxCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestExtra
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandPairSphericalVectorUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantThetaMeanSquareForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HformZeroRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.UnitaryCharEqOneOfTrivialRationalSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandKazhdanDualOfHyps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRapidDecaySiegelGLOfFinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviSectionIsotropicFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviSectionIsotropicFrame
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem exists_isLv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ f
  exact ⟨GlobalTheory.SphEisModel.lv f, GlobalTheory.SphEisModel.isLv_lv f⟩

end GlobalTheory.SphEis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviSectionIsotropicFrameStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_leviSection_isotropicFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv := by
  first | exact @GlobalTheory.SphEis.exists_isLv | exact GlobalTheory.SphEis.exists_isLv | (intros; apply GlobalTheory.SphEis.exists_isLv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelConjugateDoubled
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelConjugateDoubled
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareModel

theorem exists_isGood_model_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (hJ : X.J = (1 : D.host.E) • (spW G i j).gram) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∃ co vac dom, Model.IsGood (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co vac ((M.ν (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))).map (conjU _ 1 hJ)) dom) B.ψ := by
  intro D T L sc G μ₀ _hL t i j M hM B hB X Y hJ r s r' s' hX hY
  obtain ⟨hH, hfd⟩ := (hM.vtx (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).haar_fund
  obtain ⟨hH', hfd'⟩ := GlobalTheory.T.conjugateUnitaryAdelicIso_map_haar_and_fundamentalDomain _ (1 : D.host.E) one_ne_zero hJ _ _ hH hfd
  obtain ⟨co, hrat⟩ := GlobalTheory.T.exists_rational_darboux_coordinates_tensor_hermitian B hB X Y r s r' s' hX hY
  have hind := GlobalTheory.T.eventually_selfDualLattice_indicator_is_vacuum B hB X Y r s r' s' hX hY co hrat
  have hany := GlobalTheory.T.exists_finitePlace_vacuum_any_darboux_coordinates B hB X Y r s r' s' hX hY co
  let ind : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F v) → ℂ :=
    fun v => Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers D.host.F} 1
  let vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F v) → ℂ :=
    fun v => if Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v (ind v) then ind v
      else (hany v).choose
  refine ⟨co, vac, _, { rat := hrat, vac := fun v => ?_, std := ?_, haar := hH', dom := hfd' }⟩
  · show Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v (vac v)
    by_cases h : Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v (ind v)
    · simp only [vac, if_pos h]; exact h
    · simp only [vac, if_neg h]; exact (hany v).choose_spec
  · filter_upwards [hind] with v hv
    show vac v = ind v
    exact if_pos hv

end GlobalTheory.SquareModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelConjugateDoubledStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodSchrodingerModel_conjugateDoubled : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (hJ : X.J = (1 : D.host.E) • (spW G i j).gram) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∃ co vac dom, Model.IsGood (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co vac ((M.ν (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))).map (conjU _ 1 hJ)) dom) B.ψ := by
  first | exact @GlobalTheory.SquareModel.exists_isGood_model_conj | exact GlobalTheory.SquareModel.exists_isGood_model_conj | (intros; apply GlobalTheory.SquareModel.exists_isGood_model_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainRationalMatricesTower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainRationalMatricesTower
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.TowerFD

theorem exists_fd_any : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ),
    ∃ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν := by
  intro F E _ _ _ _ _ nS nT
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : LocallyCompactSpace (AF F ⊗[F] E) := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  have : LocallyCompactSpace (WOF F E nS nT) :=
    inferInstanceAs (LocallyCompactSpace (Fin nT → Fin nS → AF F ⊗[F] E))
  have : SecondCountableTopology (WOF F E nS nT) :=
    inferInstanceAs (SecondCountableTopology (Fin nT → Fin nS → AF F ⊗[F] E))
  have : T2Space (WOF F E nS nT) := inferInstanceAs (T2Space (Fin nT → Fin nS → AF F ⊗[F] E))
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have hdisc : DiscreteTopology (ratLF F E nS nT) := by
    obtain ⟨U, hU, hx⟩ := GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F)
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)
    have hN : (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => U) ∈
        nhds (0 : WOF F E nS nT) :=
      set_pi_mem_nhds Set.finite_univ fun _ _ => set_pi_mem_nhds Set.finite_univ fun _ _ => hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : ratLF F E nS nT => (x : WOF F E nS nT)) 0 :=
      continuous_subtype_val.continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
    rintro ⟨_, y, rfl⟩ hy
    have hy0 : y = 0 := by
      funext i j
      exact hx _ (hy i (Set.mem_univ i) j (Set.mem_univ j))
    subst hy0
    exact Subtype.ext (map_zero _)
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleCocompact.exists_compact_adele F)
  choose c hc using hx
  have hcov : ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈
      (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) :=
    fun x => ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩
  have hKc : IsCompact (Set.univ.pi (fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) :
      Set (WOF F E nS nT)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  have tZ : IsTopologicalAddGroup (WOF F E nS nT) := inferInstance
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ :=
    (@GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WOF F E nS nT) _ _ tZ _ _ _ _ _ (ratLF F E nS nT) hdisc _
      hKc hcov).1
  exact ⟨μ, 𝓕, hμ, h𝓕⟩

end GlobalTheory.TowerFD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainRationalMatricesTowerStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_fundamentalDomain_rationalMatrices_tower : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ),
    ∃ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν := by
  first | exact @GlobalTheory.TowerFD.exists_fd_any | exact GlobalTheory.TowerFD.exists_fd_any | (intros; apply GlobalTheory.TowerFD.exists_fd_any <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCoordinatesGroupLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCoordinatesGroupLaw
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem crdLaw_cT_mul {A : Type} [CommRing A] (s : A →+* A) {a b c : Type} [Fintype b] (M : Matrix a b A) (N : Matrix b c A) :
    cT s (M * N) = cT s N * cT s M := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem crdLaw_cT_add {A : Type} [CommRing A] (s : A →+* A) {a b : Type} (M N : Matrix a b A) :
    cT s (M + N) = cT s M + cT s N := by
  simp [cT, Matrix.map_add (f := _), Matrix.transpose_add]

theorem crdLaw_cT_one {A : Type} [CommRing A] (s : A →+* A) {a : Type} [DecidableEq a] :
    cT s (1 : Matrix a a A) = 1 := by
  simp [cT]

theorem crdLaw_plus_add {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {j m : ℕ} (J₀ : Matrix (Fin m) (Fin m) E) (b b' : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) :
    plus σ J₀ (b + b') = plus σ J₀ b + plus σ J₀ b' := by
  simp only [plus, crdLaw_cT_add, Matrix.mul_add]

theorem crdLaw_plus_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {j m : ℕ} (J₀ : Matrix (Fin m) (Fin m) E) (a : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) :
    plus σ J₀ (a * b) = plus σ J₀ b * cT (sigR (AF F) σ) a := by
  simp only [plus, crdLaw_cT_mul, Matrix.mul_assoc]

theorem crd_law : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ (u u' : GAd σ J) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) (b' : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c' : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c → (Crd σ J C D Z J₀ u' b' c' → Crd σ J C D Z J₀ (u * u') (b + b') (c + c' - b * plus σ J₀ b')) ∧ (Crd σ J C D Z J₀ u' b c → u = u') ∧ ∀ α, Crd σ J C D Z J₀ (lv α * u * (lv α)⁻¹) (α.1 * b) (α.1 * c * cT (sigR (AF F) σ) α.1) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hL u u' b c b' c' h
  refine ⟨fun h' => ?_, fun h' => ?_, fun α => ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [map_mul, Units.val_mul, Matrix.mul_assoc, h'.onC, h.onC]
    · rw [map_mul, Units.val_mul, Matrix.mul_assoc, h'.onZ, Matrix.mul_add, h.onZ, ← Matrix.mul_assoc, h.onC,
        Matrix.mul_add, add_assoc]
    · have eZ : (matHom _ σ J u).1 * (adMat F Z * plus σ J₀ b') = (adMat F Z + adMat F C * b) * plus σ J₀ b' := by
        rw [← Matrix.mul_assoc, h.onZ]
      have eC : (matHom _ σ J u).1 * (adMat F C * c') = adMat F C * c' := by
        rw [← Matrix.mul_assoc, h.onC]
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, h'.onD, Matrix.mul_add, Matrix.mul_sub, h.onD, eZ, eC,
        crdLaw_plus_add]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_assoc]
      abel
  · exact eq_of_frame_cols F E σ n J j m C D Z J₀ hF u u' (h.onC.trans h'.onC.symm) (h.onZ.trans h'.onZ.symm)
      (h.onD.trans h'.onD.symm)
  · have hinv : (lv α)⁻¹ = lv α⁻¹ := (map_inv lv α).symm
    have iC : (matHom _ σ J (lv α⁻¹)).1 * adMat F C = adMat F C * (α⁻¹).1 := hL.onC α⁻¹
    have iZ : (matHom _ σ J (lv α⁻¹)).1 * adMat F Z = adMat F Z := hL.onZ α⁻¹
    have iD : (matHom _ σ J (lv α⁻¹)).1 * adMat F D = adMat F D * cT (sigR (AF F) σ) α.1 := by
      rw [hL.onD α⁻¹, inv_inv]
    have one : cT (sigR (AF F) σ) (α⁻¹).1 * cT (sigR (AF F) σ) α.1 = 1 := by
      rw [← crdLaw_cT_mul, Units.mul_inv, crdLaw_cT_one]
    have aC : (matHom _ σ J (lv α)).1 * (adMat F C * b) = adMat F C * (α.1 * b) := by
      rw [← Matrix.mul_assoc, hL.onC, Matrix.mul_assoc]
    rw [hinv]
    refine ⟨?_, ?_, ?_⟩
    · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, iC, ← Matrix.mul_assoc,
        Matrix.mul_assoc _ _ (adMat F C), h.onC, hL.onC, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, iZ, Matrix.mul_assoc, h.onZ,
        Matrix.mul_add, hL.onZ, aC]
    · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, iD, Matrix.mul_assoc,
        ← Matrix.mul_assoc _ (adMat F D), h.onD, crdLaw_plus_mul]
      have eZ : (matHom _ σ J (lv α)).1 * (adMat F Z * plus σ J₀ b) = adMat F Z * plus σ J₀ b := by
        rw [← Matrix.mul_assoc, hL.onZ]
      have eC : (matHom _ σ J (lv α)).1 * (adMat F C * c) = adMat F C * (α.1 * c) := by
        rw [← Matrix.mul_assoc, hL.onC, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_sub, hL.onD, eZ, eC]
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, one, Matrix.mul_one]

end GlobalTheory.SphEis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCoordinatesGroupLawStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_coordinates_groupLaw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ (u u' : GAd σ J) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) (b' : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c' : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c → (Crd σ J C D Z J₀ u' b' c' → Crd σ J C D Z J₀ (u * u') (b + b') (c + c' - b * plus σ J₀ b')) ∧ (Crd σ J C D Z J₀ u' b c → u = u') ∧ ∀ α, Crd σ J C D Z J₀ (lv α * u * (lv α)⁻¹) (α.1 * b) (α.1 * c * cT (sigR (AF F) σ) α.1) := by
  first | exact @GlobalTheory.SphEis.crd_law | exact GlobalTheory.SphEis.crd_law | (intros; apply GlobalTheory.SphEis.crd_law <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFrameCoordsOfMemIsotropicUnipoten
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFrameCoordsOfMemIsotropicUnipoten
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem exists_crd_of_mem_unipRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ u ∈ unipRad σ J C, ∃ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c ∧ c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0 := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF u hu
  obtain ⟨hC, b, hZ⟩ := (mem_unipRad_iff_frame F E σ n J j m C D Z J₀ hF u).1 hu
  set s := sigR (AF F) σ with hsdef
  set M := (matHom _ σ J u).1 with hMdef
  have hU : cT s M * adMat F J * M = adMat F J := u.2
  have hs : ∀ a : AF F ⊗[F] E, s (s a) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma hF.cm x)
  have cc : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)), cT s (cT s X) = X :=
    fun X => Matrix.ext fun i k => hs _
  have cadd : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)), cT s (X + Y) = cT s X + cT s Y :=
    fun X Y => Matrix.ext fun i k => map_add s _ _
  have csub : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)), cT s (X - Y) = cT s X - cT s Y :=
    fun X Y => Matrix.ext fun i k => map_sub s _ _
  have cad : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) E), cT s (adMat F X) = adMat F (cT (σ : E →+* E) X) :=
    fun X => GlobalTheory.AutFunCounterexample.cT_map_gen σ X
  have gram : ∀ {a b : ℕ} (X : Matrix (Fin n) (Fin a) E) (Y : Matrix (Fin n) (Fin b) E),
      cT s (adMat F X) * adMat F J * adMat F Y = adMat F (cT (σ : E →+* E) X * J * Y) := fun X Y => by
    rw [cad]; simp only [adMat, Matrix.map_mul]
  have unit : ∀ {a b : ℕ} (X : Matrix (Fin n) (Fin a) (AF F ⊗[F] E)) (Y : Matrix (Fin n) (Fin b) (AF F ⊗[F] E)),
      cT s (M * X) * adMat F J * (M * Y) = cT s X * adMat F J * Y := fun X Y => by
    have e : cT s X * cT s M * adMat F J * (M * Y) = cT s X * (cT s M * adMat F J * M) * Y := by
      simp only [Matrix.mul_assoc]
    rw [Formalism.UG.cT_mul, e, hU]
  have ad0 : ∀ {a b : ℕ}, adMat F (0 : Matrix (Fin a) (Fin b) E) = 0 := fun {a b} => Matrix.map_zero _ (map_zero _)
  have ad1 : ∀ {a : ℕ}, adMat F (1 : Matrix (Fin a) (Fin a) E) = 1 := fun {a} => Matrix.map_one _ (map_zero _) (map_one _)

  have h1 : cT s (adMat F C) * adMat F J * (M * adMat F D) = 1 := by
    conv_lhs => rw [← hC]
    rw [unit, gram, hF.cd, ad1]
  have h2 : cT s (adMat F Z) * adMat F J * (M * adMat F D) = - cT s b := by
    have e := unit (adMat F Z) (adMat F D)
    rw [hZ, gram, hF.zd, ad0, cadd, Formalism.UG.cT_mul, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc (cT s b),
      Matrix.mul_assoc (cT s b), h1, Matrix.mul_one] at e
    exact eq_neg_of_add_eq_zero_left e
  set c := cT s (adMat F D) * adMat F J * (M * adMat F D) with hc
  have hsum : adMat F C * (cT s (adMat F D) * adMat F J) + adMat F Z * (adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J)) +
      adMat F D * (cT s (adMat F C) * adMat F J) = 1 := by
    have e := congrArg (fun X => adMat F X) hF.sum
    simp only [adMat, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at e
    simp only [cad, adMat]
    exact e
  have hD : M * adMat F D = adMat F D - adMat F Z * plus σ J₀ b + adMat F C * c := by
    conv_lhs => rw [← Matrix.one_mul (M * adMat F D), ← hsum]
    simp only [Matrix.add_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (cT s (adMat F D)), ← Matrix.mul_assoc (cT s (adMat F Z)),
      ← Matrix.mul_assoc (cT s (adMat F C)), h1, h2, Matrix.mul_one, plus, Matrix.mul_neg, Matrix.mul_neg, ← hc]
    abel
  refine ⟨b, c, ⟨hC, hZ, hD⟩, ?_⟩

  have h0 := unit (adMat F D) (adMat F D)
  rw [gram, hF.dd, ad0] at h0
  have hP : cT s (plus σ J₀ b) = b * adMat F J₀⁻¹ := by
    rw [plus, Formalism.UG.cT_mul, cc, cad, GlobalTheory.UAut.cT_form_inv hF.herm₀]
  conv_lhs at h0 => rw [hD]
  rw [cadd, csub, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hP, Matrix.add_mul, Matrix.sub_mul, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_assoc (b * adMat F J₀⁻¹), Matrix.mul_assoc (b * adMat F J₀⁻¹), Matrix.mul_assoc (cT s c),
    Matrix.mul_assoc (cT s c), ← hD, h1, h2, ← hc, Matrix.mul_one] at h0
  rw [← h0, plus, Matrix.mul_neg, Matrix.mul_assoc]
  abel

end GlobalTheory.SphEis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFrameCoordsOfMemIsotropicUnipotenStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotentFrameCoords_of_mem_isotropicUnipotentRadical : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ u ∈ unipRad σ J C, ∃ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c ∧ c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0 := by
  first | exact @GlobalTheory.SphEis.exists_crd_of_mem_unipRad | exact GlobalTheory.SphEis.exists_crd_of_mem_unipRad | (intros; apply GlobalTheory.SphEis.exists_crd_of_mem_unipRad <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIntegralFixedVectorsEqOneAlmostAll
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIntegralFixedVectorsEqOneAlmostAll
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.SphLine

theorem finiteDimensional_fixed_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (T : ρ.Equiv τ) (U : Subgroup G)
    [FiniteDimensional ℂ (fixed ρ U)] : FiniteDimensional ℂ (fixed τ U) := by
  have hle : fixed τ U ≤ (fixed ρ U).map (T.toLinearEquiv : V →ₗ[ℂ] W) := by
    intro y hy
    refine ⟨T.toLinearEquiv.symm y, ?_, T.toLinearEquiv.apply_symm_apply y⟩
    show _ ∈ fixed ρ U
    rw [GlobalTheory.GelfandLine.mem_fixed_iff] at hy ⊢
    intro k hk
    apply T.toLinearEquiv.injective
    have h2 := LinearMap.congr_fun (T.isIntertwining' k) (T.toLinearEquiv.symm y)
    simp only [LinearMap.comp_apply] at h2
    rw [LinearEquiv.apply_symm_apply]
    apply h2.trans
    change τ k (T.toLinearEquiv (T.toLinearEquiv.symm y)) = y
    rw [LinearEquiv.apply_symm_apply]
    exact hy k hk
  exact Submodule.finiteDimensional_of_le hle

theorem exists_gelfand_anti : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), ∃ θ : UL n w → UL n w, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧ ∀ g, ∃ a ∈ KL n w, ∃ b ∈ KL n w, θ g = a * g * b := by
  intro E _ _ _ hU n w
  by_cases hs : IsSplitAt w
  · have hUL : UL n w = ⊤ := if_pos hs
    have hm : ∀ g : GLw n w, g ∈ UL n w := fun g => by rw [hUL]; trivial
    refine ⟨fun g => ⟨Formalism.UG.P.heckecomm_tr g.1, hm _⟩, fun x y => Subtype.ext (Formalism.UG.P.heckecomm_tr_mul _ _),
      fun x => Subtype.ext (Formalism.UG.P.heckecomm_tr_tr _), fun g => ?_⟩
    obtain ⟨a, b, e⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.P.cartan_decomposition_holds E w n g.1
    exact ⟨⟨a, hm _⟩, Subgroup.mem_subgroupOf.2 a.2, ⟨b, hm _⟩, Subgroup.mem_subgroupOf.2 b.2, Subtype.ext e⟩
  · obtain ⟨-, -, -, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨-, ⟨ϖ, q, hq, -⟩, -⟩ := hns hs
    have hUL : UL n w = UJ (cj w) 1 := if_neg hs
    refine ⟨fun g => g⁻¹, fun x y => mul_inv_rev x y, fun x => inv_inv x, fun g => ?_⟩
    have hg : (g : GLw n w) ∈ UJ (cj w) ((1 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      rw [Units.val_one, ← hUL]; exact g.2
    have hJ : ∀ i j : Fin n, cj w (((1 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) =
        ((1 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) j i := by
      intro i j
      rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
      by_cases h : i = j
      · subst h; simp
      · rw [if_neg h, if_neg (Ne.symm h), map_zero]
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.UnitarySwap.inv_mem_doubleCoset hq (one_mem _) hJ hg
    have m1 : k₁ ∈ UL n w := by rw [hUL]; have := hk₁.1; rwa [Units.val_one] at this
    have m2 : k₂ ∈ UL n w := by rw [hUL]; have := hk₂.1; rwa [Units.val_one] at this
    exact ⟨⟨k₁, m1⟩, Subgroup.mem_subgroupOf.2 hk₁.2, ⟨k₂, m2⟩, Subgroup.mem_subgroupOf.2 hk₂.2, Subtype.ext e⟩

theorem finrank_fixed_KL_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ σ : ∀ w : Pl E, SmIrr (UL n w), (∀ w, IsCompU π w (σ w)) →
    ∀ᶠ w in cofinite, Module.finrank ℂ (fixed (σ w).ρ (KL n w)) = 1 := by
  intro E _ _ _ hU n hn π hπ σ hσ
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hπ.ne_bot
  let L : Subgroup (finU (E := E) (n := n)) :=
    { carrier := {k | RU E n k φ = φ}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hLo : IsOpen (L : Set (finU (E := E) (n := n))) := (hπ.aut φ hφ).level
  have hunr : ∀ᶠ w in cofinite, IsUnramU π w := by
    filter_upwards [GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary E n L hLo] with w hw
    exact ⟨φ, hφ, hφ0, fun x hx hxK => hw x hx hxK hx.1⟩
  have hadm : ∀ w, IsAdmissible (σ w).ρ := by
    intro w
    obtain ⟨⟨σ₀, hσ₀, hfd⟩, huniq⟩ := GlobalTheory.BCT.LocCompU.exists_unique_locComp E hU n hn π hπ w
    obtain ⟨T⟩ := huniq σ₀ (σ w) hσ₀ (hσ w)
    refine ⟨(σ w).smooth, fun K hKo _ => ?_⟩
    haveI := hfd K hKo
    exact finiteDimensional_fixed_of_equiv T K
  filter_upwards [hunr] with w hw
  have hne := GlobalTheory.T.unramifiedVector_gives_localComponent_sphericalVector E hU n π hπ w (σ w) (hσ w) hw
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨θ, h1, h2, h3⟩ := exists_gelfand_anti E hU n w
  obtain ⟨hKo, hKc⟩ := GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w
  have := GlobalTheory.fixed_eq_span_of_gelfandPair (UL n w) (KL n w) hKo hKc θ h1 h2 h3 (σ w).V (σ w).ρ (σ w).irred (hadm w) x hx hx0
  rw [this, finrank_span_singleton hx0]

end GlobalTheory.BCT.SphLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIntegralFixedVectorsEqOneAlmostAllStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_integral_fixed_vectors_eq_one_almost_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ σ : ∀ w : Pl E, SmIrr (UL n w), (∀ w, IsCompU π w (σ w)) → ∀ᶠ w in cofinite, Module.finrank ℂ (fixed (σ w).ρ (KL n w)) = 1 := by
  first | exact @GlobalTheory.BCT.SphLine.finrank_fixed_KL_eq_one | exact GlobalTheory.BCT.SphLine.finrank_fixed_KL_eq_one | (intros; apply GlobalTheory.BCT.SphLine.finrank_fixed_KL_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentRadicalPointWithCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentRadicalPointWithCoords
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.UnipCrd

section Ring

variable {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (A : Matrix (Fin n) (Fin n) R)

theorem cT_add' {p q : Type} (M N : Matrix p q R) : cT s (M + N) = cT s M + cT s N := by
  ext i k; simp [cT]

theorem cT_sub' {p q : Type} (M N : Matrix p q R) : cT s (M - N) = cT s M - cT s N := by
  ext i k; simp [cT]

def gr {p q : ℕ} (X : Matrix (Fin n) (Fin p) R) (Y : Matrix (Fin n) (Fin q) R) : Matrix (Fin p) (Fin q) R :=
  cT s X * A * Y

variable {p q k : ℕ}

theorem gr_add_left (X X' : Matrix (Fin n) (Fin p) R) (Y : Matrix (Fin n) (Fin q) R) :
    gr s A (X + X') Y = gr s A X Y + gr s A X' Y := by
  simp [gr, cT_add', Matrix.add_mul]

theorem gr_sub_left (X X' : Matrix (Fin n) (Fin p) R) (Y : Matrix (Fin n) (Fin q) R) :
    gr s A (X - X') Y = gr s A X Y - gr s A X' Y := by
  simp [gr, cT_sub', Matrix.sub_mul]

theorem gr_add_right (X : Matrix (Fin n) (Fin p) R) (Y Y' : Matrix (Fin n) (Fin q) R) :
    gr s A X (Y + Y') = gr s A X Y + gr s A X Y' := by
  simp [gr, Matrix.mul_add]

theorem gr_sub_right (X : Matrix (Fin n) (Fin p) R) (Y Y' : Matrix (Fin n) (Fin q) R) :
    gr s A X (Y - Y') = gr s A X Y - gr s A X Y' := by
  simp [gr, Matrix.mul_sub]

theorem gr_mul_left (X : Matrix (Fin n) (Fin k) R) (M : Matrix (Fin k) (Fin p) R) (Y : Matrix (Fin n) (Fin q) R) :
    gr s A (X * M) Y = cT s M * gr s A X Y := by
  simp [gr, Formalism.UG.cT_mul, Matrix.mul_assoc]

theorem gr_mul_right (X : Matrix (Fin n) (Fin p) R) (Y : Matrix (Fin n) (Fin k) R) (M : Matrix (Fin k) (Fin q) R) :
    gr s A X (Y * M) = gr s A X Y * M := by
  simp [gr, Matrix.mul_assoc]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

theorem cT_adMat {p q : Type} (X : Matrix p q E) :
    cT (sigR (AF F) σ) (adMat F X) = adMat F (cT (σ : E →+* E) X) := by
  ext i k; simp [cT, adMat, sigR, inclR]

theorem gr_adMat {n p q : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E) :
    gr (sigR (AF F) σ) (adMat F J) (adMat F X) (adMat F Y) = adMat F (cT (σ : E →+* E) X * J * Y) := by
  simp only [gr, cT_adMat, adMat, Matrix.map_mul]

theorem invol (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_invol (h : IsCMExt F E σ) (x : AF F ⊗[F] E) : sigR (AF F) σ (sigR (AF F) σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, invol σ h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem cT_cT (h : IsCMExt F E σ) {p q : Type} (M : Matrix p q (AF F ⊗[F] E)) :
    cT (sigR (AF F) σ) (cT (sigR (AF F) σ) M) = M := by
  ext i k; simp [cT, sigR_invol σ h]

theorem cT_inv_herm {m : ℕ} (J₀ : Matrix (Fin m) (Fin m) E) (h : IsHermND σ J₀) :
    cT (σ : E →+* E) J₀⁻¹ = J₀⁻¹ := by
  have hJ : cT (σ : E →+* E) J₀ = J₀ := by
    ext i k; simp [cT, h.1]
  have hu : IsUnit J₀.det := isUnit_iff_ne_zero.mpr h.2
  have e : cT (σ : E →+* E) J₀⁻¹ * J₀ = 1 := by
    calc cT (σ : E →+* E) J₀⁻¹ * J₀ = cT (σ : E →+* E) J₀⁻¹ * cT (σ : E →+* E) J₀ := by rw [hJ]
      _ = cT (σ : E →+* E) (J₀ * J₀⁻¹) := (Formalism.UG.cT_mul _ _ _).symm
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hu, Formalism.UG.cT_one]
  exact (Matrix.inv_eq_left_inv e).symm

theorem exists_unipRad_crd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0 → ∃ u ∈ unipRad σ J C, Crd σ J C D Z J₀ u b c := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF b c hc
  set s := sigR (AF F) σ with hs
  set p := plus σ J₀ b with hp
  have hu : IsUnit J₀.det := isUnit_iff_ne_zero.mpr hF.herm₀.2
  have key : cT s p * adMat F J₀ = b := by
    rw [hp, plus, Formalism.UG.cT_mul, cT_cT σ hF.cm, cT_adMat, cT_inv_herm σ J₀ hF.herm₀, Matrix.mul_assoc, adMat,
      adMat, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  have g0 : ∀ {p q : ℕ} (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E), cT (σ : E →+* E) X * J * Y = 0 →
      gr s (adMat F J) (adMat F X) (adMat F Y) = 0 := by
    intro p q X Y h; rw [gr_adMat, h]; simp
  have g1 : ∀ (X Y : Matrix (Fin n) (Fin j) E), cT (σ : E →+* E) X * J * Y = 1 →
      gr s (adMat F J) (adMat F X) (adMat F Y) = 1 := by
    intro X Y h; rw [gr_adMat, h]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have gzz : gr s (adMat F J) (adMat F Z) (adMat F Z) = adMat F J₀ := by rw [gr_adMat, hF.zz]
  have hcc := g0 C C hF.cc
  have hdd := g0 D D hF.dd
  have hcz := g0 C Z hF.cz
  have hdz := g0 D Z hF.dz
  have hzc := g0 Z C hF.zc
  have hzd := g0 Z D hF.zd
  have hcd := g1 C D hF.cd
  have hdc := g1 D C hF.dc
  have Ecd : cT s (adMat F C) * adMat F J * (adMat F D - adMat F Z * p + adMat F C * c) = 1 := by
    show gr s (adMat F J) _ _ = 1
    simp only [gr_add_right, gr_sub_right, gr_mul_right, hcd, hcz, hcc]
    simp
  have Ecz : cT s (adMat F C) * adMat F J * (adMat F Z + adMat F C * b) = 0 := by
    show gr s (adMat F J) _ _ = 0
    simp only [gr_add_right, gr_mul_right, hcz, hcc]
    simp
  have Ezz : cT s (adMat F Z + adMat F C * b) * adMat F J * (adMat F Z + adMat F C * b) = adMat F J₀ := by
    show gr s (adMat F J) _ _ = _
    simp only [gr_add_right, gr_add_left, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz]
    simp
  have Edz : cT s (adMat F D - adMat F Z * p + adMat F C * c) * adMat F J * (adMat F Z + adMat F C * b) = 0 := by
    show gr s (adMat F J) _ _ = 0
    simp only [gr_add_right, gr_add_left, gr_sub_left, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz, hdz, hdc]
    simp [key]
  have Edd : cT s (adMat F D - adMat F Z * p + adMat F C * c) * adMat F J * (adMat F D - adMat F Z * p + adMat F C * c) = 0 := by
    show gr s (adMat F J) _ _ = 0
    simp only [gr_add_right, gr_add_left, gr_sub_left, gr_sub_right, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz,
      hdz, hdc, hcd, hdd, hzd]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, sub_zero, zero_add, add_zero, zero_sub,
      sub_neg_eq_add, key]
    simp only [Matrix.neg_mul, sub_neg_eq_add]
    rw [← hc]
    abel
  obtain ⟨g, h1, h2, h3⟩ := GlobalTheory.T.exists_unitaryAdelicPoint_prescribed_frameImages F E σ n J j m C D Z J₀ hF (adMat F C) (adMat F D - adMat F Z * p + adMat F C * c)
    (adMat F Z + adMat F C * b) hcc Edd Ecd Ecz Edz Ezz
  exact ⟨g, (GlobalTheory.T.mem_isotropicUnipotentRadical_iff_frame F E σ n J j m C D Z J₀ hF g).mpr ⟨h1, b, h2⟩, h1, h2, h3⟩

end GlobalTheory.SphEis.UnipCrd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentRadicalPointWithCoordsStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotentRadical_point_with_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0 → ∃ u ∈ unipRad σ J C, Crd σ J C D Z J₀ u b c := by
  first | exact @GlobalTheory.SphEis.UnipCrd.exists_unipRad_crd | exact GlobalTheory.SphEis.UnipCrd.exists_unipRad_crd | (intros; apply GlobalTheory.SphEis.UnipCrd.exists_unipRad_crd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumHeisenbergEigenDoubledLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumHeisenbergEigenDoubledLattice
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacEigen

section Alg

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]


omit [DecidableEq α] in
theorem hTens_dbl (JA : Matrix α α E) (JB : Matrix β β E) (x₁ x₂ y₁ y₂ : Matrix α β E) :
    hTens c JA (dbl JB) (Matrix.fromCols x₁ x₂) (Matrix.fromCols y₁ y₂) = hTens c JA JB x₁ y₁ - hTens c JA JB x₂ y₂ := by
  simp only [hTens, dbl, Fintype.sum_sum_type, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, add_zero, zero_add, mul_neg, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_add_distrib, sub_eq_add_neg, Finset.sum_const_zero]


omit [DecidableEq α] [DecidableEq β] in
theorem hTens_transpose (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix β α E) :
    hTens c JA JB xᵀ yᵀ = hTens c JB JA x y := by
  unfold hTens
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.transpose_apply]
  ring

end Alg

end GlobalTheory.DblVacEigen

namespace GlobalTheory.DblVacEigen

variable {F : Type} [Field F] [NumberField F]

theorem dot_congr_at {κ : Type} [Fintype κ] (v : Pl (F := F)) {y : κ → AF F} (hy : At (evFin F v) y) {z z' : κ → AF F}
    (h : ∀ i, evFin F v (z i) = evFin F v (z' i)) : z ⬝ᵥ y = z' ⬝ᵥ y := by
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := congrFun (hy (z i - z' i) (by rw [map_sub, h i, sub_self])) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e
  rw [sub_mul] at e
  exact sub_eq_zero.mp e

theorem eigen_pointwise {κ : Type} [Fintype κ] (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ) {φ : (κ → Fv F v) → ℂ}
    (hφ : φ ∈ SB (κ → Fv F v)) (p : (κ → AF F) × (κ → AF F)) (hp1 : At (evFin F v) p.1) (hp2 : At (evFin F v) p.2)
    (c : ℂ) (h : Acts (evFin F v) (schr ψ p) φ (c • φ)) (z : κ → AF F) :
    ψ (z ⬝ᵥ p.2 + ⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)) * φ (fun i => evFin F v ((z + p.1) i)) =
      c * φ (fun i => evFin F v (z i)) := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have hr := hR φ hφ
  let Δ : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (z i))
  have hΔ : At (evFin F v) Δ := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have hevΔ : ∀ i, evFin F v (Δ i) = evFin F v (z i) := fun i => GlobalTheory.LatVac.evFin_liftV v _
  have e := congrFun (h R hr) Δ
  have hR2 : R Δ = R 0 := by simpa using hr.1 0 Δ hΔ
  have hR1 : R (Δ + p.1) = R 0 := by rw [hr.1 Δ p.1 hp1, hR2]
  simp only [schr, tens, Pi.smul_apply, smul_eq_mul] at e
  rw [hR1, hR2, dot_congr_at v hp2 hevΔ] at e
  have hev : (fun i => evFin F v ((Δ + p.1) i)) = fun i => evFin F v ((z + p.1) i) := by
    funext i; simp only [Pi.add_apply, map_add (f := _), hevΔ]
  have hev' : (fun i => evFin F v (Δ i)) = fun i => evFin F v (z i) := funext hevΔ
  rw [hev, hev'] at e
  exact mul_right_cancel₀ hR0 (by linear_combination e)

theorem acts_box {κ κ' : Type} [Fintype κ] [Fintype κ'] (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ)
    {φ₁ : (κ → Fv F v) → ℂ} {φ₂ : (κ' → Fv F v) → ℂ} (X₁ Y₁ : κ → AF F)
    (X₂ Y₂ : κ' → AF F) (h11 : At (evFin F v) X₁) (h21 : At (evFin F v) X₂) (c₁ c₂ : ℂ)
    (h₁ : ∀ z, ψ (z ⬝ᵥ Y₁ + ⅟(2 : AF F) * (X₁ ⬝ᵥ Y₁)) * φ₁ (fun i => evFin F v ((z + X₁) i)) =
      c₁ * φ₁ (fun i => evFin F v (z i)))
    (h₂ : ∀ z, ψ (z ⬝ᵥ Y₂ + ⅟(2 : AF F) * (X₂ ⬝ᵥ Y₂)) * φ₂ (fun i => evFin F v ((z + X₂) i)) =
      c₂ * φ₂ (fun i => evFin F v (z i))) :
    Acts (evFin F v) (schr ψ (Sum.elim X₁ X₂, Sum.elim Y₁ Y₂)) (boxFun φ₁ φ₂)
      ((c₁ * c₂) • boxFun φ₁ φ₂) := by
  intro r hr
  have hX : At (evFin F v) (Sum.elim X₁ X₂ : κ ⊕ κ' → AF F) := by
    intro u hu; funext i
    cases i with
    | inl i => exact congrFun (h11 u hu) i
    | inr i => exact congrFun (h21 u hu) i
  funext x
  have hd1 : x ⬝ᵥ Sum.elim Y₁ Y₂ = (x ∘ Sum.inl) ⬝ᵥ Y₁ + (x ∘ Sum.inr) ⬝ᵥ Y₂ := by
    simp [dotProduct, Fintype.sum_sum_type]
  have hd2 : Sum.elim X₁ X₂ ⬝ᵥ Sum.elim Y₁ Y₂ = X₁ ⬝ᵥ Y₁ + X₂ ⬝ᵥ Y₂ :=
    by simp [dotProduct, Fintype.sum_sum_type]
  simp only [schr, tens, Pi.smul_apply, smul_eq_mul]
  rw [hr.1 x _ hX, hd1, hd2,
    show (x ∘ Sum.inl) ⬝ᵥ Y₁ + (x ∘ Sum.inr) ⬝ᵥ Y₂ + ⅟(2 : AF F) * (X₁ ⬝ᵥ Y₁ + X₂ ⬝ᵥ Y₂) =
      ((x ∘ Sum.inl) ⬝ᵥ Y₁ + ⅟(2 : AF F) * (X₁ ⬝ᵥ Y₁)) + ((x ∘ Sum.inr) ⬝ᵥ Y₂ + ⅟(2 : AF F) * (X₂ ⬝ᵥ Y₂))
      by ring, AddChar.map_add_eq_mul]
  have e1 := h₁ (x ∘ Sum.inl)
  have e2 := h₂ (x ∘ Sum.inr)
  simp only [boxFun, Function.comp_def, Pi.add_apply, Sum.elim_inl, Sum.elim_inr] at e1 e2 ⊢
  rw [show ∀ a e b f s : ℂ, a * e * ((b * f) * s) = (a * b) * (e * f) * s from fun _ _ _ _ _ => by ring, e1, e2]
  ring

end GlobalTheory.DblVacEigen

namespace GlobalTheory.DblVacEigen

theorem doubled_vac_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • G.M.vac v)) →
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) (boxFun (G.M.vac v) (fun x => star (G.M.vac v x)))
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • (boxFun (G.M.vac v) (fun x => star (G.M.vac v x))))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w _ _ d' hd' dd hdd θ _ hvac w₁ hw₁ w₂ hw₂
  have hSB := (hT.geo.hM.vac v).1
  have hψ : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hT.base.std
  have hstar : ∀ t, star (B.ψ t) = B.ψ (-t) := by
    intro t
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ t]
    simp
  have hAt : ∀ γ ∈ latAtV G.V G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  have hco : ∀ γ ∈ latAtV G.V G.W v, At (evFin F v) (G.M.co.e γ).1 ∧ At (evFin F v) (G.M.co.e γ).2 := by
    intro γ hγ
    have e : ∀ u, evFin F v u = 0 → u • G.M.co.e γ = 0 := fun u hu => by
      rw [← map_smul, hAt γ hγ u hu, map_zero]
    exact ⟨fun u hu => congrArg Prod.fst (e u hu), fun u hu => congrArg Prod.snd (e u hu)⟩
  have h1 := eigen_pointwise v B.ψ hSB (G.M.co.e w₁) (hco w₁ hw₁).1 (hco w₁ hw₁).2 _ (hvac w₁ hw₁)
  have h2 := eigen_pointwise v B.ψ hSB (G.M.co.e w₂) (hco w₂ hw₂).1 (hco w₂ hw₂).2 _ (hvac w₂ hw₂)
  have h2' : ∀ z, B.ψ (z ⬝ᵥ (-(G.M.co.e w₂).2) + ⅟(2 : AF F) * ((G.M.co.e w₂).1 ⬝ᵥ (-(G.M.co.e w₂).2))) *
      (fun x => star (G.M.vac v x)) (fun i => evFin F v ((z + (G.M.co.e w₂).1) i)) =
      star (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₂ w₂)) * (fun x => star (G.M.vac v x)) (fun i => evFin F v (z i)) := by
    intro z
    have e := congrArg star (h2 z)
    simp only [star_mul, hstar] at e
    rw [hstar, show z ⬝ᵥ (-(G.M.co.e w₂).2) + ⅟(2 : AF F) * ((G.M.co.e w₂).1 ⬝ᵥ (-(G.M.co.e w₂).2)) =
      -(z ⬝ᵥ (G.M.co.e w₂).2 + ⅟(2 : AF F) * ((G.M.co.e w₂).1 ⬝ᵥ (G.M.co.e w₂).2)) by
        rw [dotProduct_neg, dotProduct_neg]; ring]
    linear_combination e
  have hbox := acts_box v B.ψ (φ₁ := G.M.vac v) (φ₂ := fun x => star (G.M.vac v x)) (G.M.co.e w₁).1 (G.M.co.e w₁).2 (G.M.co.e w₂).1 (-(G.M.co.e w₂).2)
    (hco w₁ hw₁).1 (hco w₂ hw₂).1 _ _ h1 h2'
  have hrho : dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ) = schr B.ψ (Sum.elim (G.M.co.e w₁).1 (G.M.co.e w₂).1,
      Sum.elim (G.M.co.e w₁).2 (-(G.M.co.e w₂).2)) := by
    rw [Darboux.rho, hdd, hd', hd']
  have hS : symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
      (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ) = symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₁ w₁ - symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₂ w₂ := by
    unfold symp
    rw [hTens_dbl, hTens_transpose, hTens_transpose, mul_sub, map_sub]
  have hc : B.ψ (⅟(2 : AF F) * (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₁ w₁ - symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₂ w₂)) = B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₁ w₁) * star (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₂ w₂)) := by
    rw [hstar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [hrho, hS, hc]
  exact hbox

end GlobalTheory.DblVacEigen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumHeisenbergEigenDoubledLatticeStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuum_heisenbergEigen_doubledLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • G.M.vac v)) →
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) (boxFun (G.M.vac v) (fun x => star (G.M.vac v x)))
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • (boxFun (G.M.vac v) (fun x => star (G.M.vac v x))))) := by
  first | exact @GlobalTheory.DblVacEigen.doubled_vac_eigen | exact GlobalTheory.DblVacEigen.doubled_vac_eigen | (intros; apply GlobalTheory.DblVacEigen.doubled_vac_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharEqOneOfTrivialRationalSplitPlace
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.unitaryChar_eq_one_of_trivial_rational_splitPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ ν : Formalism.IndefR.DatumF.GAF σ J →* Circle, Continuous ν → (∀ γ ∈ Formalism.IndefR.DatumF.GQF σ J, ν γ = 1) →
        (∀ e, Formalism.IndefR.DatumF.IsSplitIdemF σ e → ∀ g, Formalism.IndefR.DatumF.SuppAtF σ e J g → ν g = 1) → ∀ g, ν g = 1 := by
  first | exact @PositivityTheory.ThKW.character_trivial_of_rational_split | exact PositivityTheory.ThKW.character_trivial_of_rational_split | (intros; apply PositivityTheory.ThKW.character_trivial_of_rational_split <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandKazhdanDualOfTwoHyps
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.GelfandKazhdanTop

theorem gelfandKazhdanDual_of_jacquetShalika : GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL →
    GlobalTheory.Published.GelfandKazhdanDual :=
  fun hJ hA => gelfandKazhdanDual_of_rapidDecay hJ hA (GlobalTheory.cuspRapidDecaySiegelGL_of_finite hA)

end GlobalTheory.GelfandKazhdanTop
end
