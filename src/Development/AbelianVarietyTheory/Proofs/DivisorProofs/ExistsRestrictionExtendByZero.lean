module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsConjOfMinpolyEqOfSeparable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictionExtendByZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ExtendByZero

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ]

theorem extend_zero_add {j : κ₁ → κ} (hj : Function.Injective j) (y z : κ₁ → V) :
    Function.extend j (y + z) (0 : κ → V) = Function.extend j y 0 + Function.extend j z 0 := by
  ext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

theorem extend_zero_smul {j : κ₁ → κ} (hj : Function.Injective j) (c : ℝ) (y : κ₁ → V) :
    Function.extend j (c • y) (0 : κ → V) = c • Function.extend j y 0 := by
  ext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

def clm {j : κ₁ → κ} (hj : Function.Injective j) : (κ₁ → V) →L[ℝ] (κ → V) where
  toFun y := Function.extend j y 0
  map_add' := extend_zero_add hj
  map_smul' := extend_zero_smul hj
  cont := by
    refine continuous_pi fun i => ?_
    by_cases h : ∃ a, j a = i
    · obtain ⟨a, rfl⟩ := h
      simp only [hj.extend_apply]
      exact continuous_apply a
    · simp only [Function.extend_apply' _ _ _ h]
      exact continuous_const

theorem clm_apply {j : κ₁ → κ} (hj : Function.Injective j) (y : κ₁ → V) : clm hj y = Function.extend j y 0 := rfl

theorem norm_le_norm_clm {j : κ₁ → κ} (hj : Function.Injective j) (y : κ₁ → V) : ‖y‖ ≤ ‖clm hj y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
  have h : clm hj y (j a) = y a := by rw [clm_apply, hj.extend_apply]
  rw [← h]
  exact norm_le_pi_norm (clm hj y) (j a)

end GlobalTheory.ExtendByZero

namespace GlobalTheory.RestrS


open scoped Classical in
theorem exists_restr : ∀ (F : Type) [Field F] [NumberField F] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j →
    ∃ R : SInf F κ →L[ℂ] SInf F κ₁, ∀ f y, R f y = f (Function.extend j y 0) := by
  intro F _ _ κ₁ κ _ _ j hj
  refine ⟨SchwartzMap.compCLM ℂ (GlobalTheory.ExtendByZero.clm (V := mixedEmbedding.mixedSpace F) hj).hasTemperateGrowth
    ⟨1, 1, fun y => ?_⟩, fun f y => rfl⟩
  have := GlobalTheory.ExtendByZero.norm_le_norm_clm (V := mixedEmbedding.mixedSpace F) hj y
  simp only [pow_one, one_mul]
  linarith

end GlobalTheory.RestrS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCA
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviModulus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E)

theorem cA_cA (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x =>
    show Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _ (a ⊗ₜ[F] x)) = a ⊗ₜ[F] x
    simp [hσ]


variable (F E) in
theorem topAE : IsTopologicalRing (AE F E) ∧ LocallyCompactSpace (AE F E) ∧ SecondCountableTopology (AE F E) ∧
    T2Space (AE F E) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  exact ⟨inferInstance, e.isClosedEmbedding.locallyCompactSpace, e.secondCountableTopology, e.isEmbedding.t2Space⟩

theorem continuous_cA : Continuous (cA σ) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI := (topAE F E).1
  exact IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap

theorem topUA {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    IsTopologicalGroup (UA σ J) ∧ LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧
      T2Space (UA σ J) := by
  obtain ⟨h1, h2, h3, h4⟩ := topAE F E
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (AE F E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.t2Space
  have hs : Continuous (cA σ) := continuous_cA σ
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) := Units.continuous_val
    exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hs))
      continuous_const
  exact ⟨inferInstance, hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology,
    inferInstanceAs (T2Space (UG (cA σ) (incM F J)))⟩

end GlobalTheory.LeviModulus

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCoordinatesFrameRationalIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCoordinatesFrameRationalIsometry
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.GeoLevel

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
private lemma mat_lact_castFr_eq_map_mul {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)}
    (hΨ : Ψ = Ψ') (a : GL (Fin r) E) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (τ : E →+* ℂ) (hτ : τ ∈ Ψ')
    (hτ₀ : τ ∈ Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact a (_root_.GlobalTheory.Dict.castFr hΨ x)) ⟨τ, hτ⟩ =
      (a : Matrix (Fin r) (Fin r) E).map τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ₀⟩ := by
  rfl

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
private lemma emb_mulVec_eq_map_mulVec_emb {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (τ : E →+* ℂ) (A : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (A *ᵥ v) = (A.map τ) *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := by
  funext k
  set_option synthInstance.maxHeartbeats 100000 in
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
private lemma col_mul_eq_mulVec_col' {r : ℕ} (A M : Matrix (Fin r) (Fin r) ℂ) (j : Fin r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.col (A * M) j = A *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.col M j := by
  funext k
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mulVec, dotProduct, Matrix.mul_apply]


open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
theorem _root_.GlobalTheory.GeoLevel.perFr_lact_of_isMatch : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (r : ℕ) (X X' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (a : GL (Fin r) E)
    (h : _root_.GlobalTheory.LevelCusp.IsMatch X X' a) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (v : Fin r → E)
    (τ : E →+* ℂ) (i : ℕ),
    _root_.Formalism.L2.PjFree.perFr X' (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact a (_root_.GlobalTheory.Dict.castFr h.psi x))
        ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = _root_.Formalism.L2.PjFree.perFr X x v τ i := by
  intro E _ _ _ r X X' a h x v τ i
  have hΨ := h.psi
  have hp := h.p0
  have hA : IsUnit ((a : Matrix (Fin r) (Fin r) E).map τ).det := by
    have h₀ := (Matrix.isUnits_det_units a).map τ
    rwa [RingHom.map_det] at h₀
  unfold _root_.Formalism.L2.PjFree.perFr
  by_cases hτ : τ ∈ X.Ψ
  · have hτ' : τ ∈ X'.Ψ := hΨ ▸ hτ
    rw [dite_eq_left hτ', dite_eq_left hτ]
    by_cases hi : X.p0 + i < r
    · have hi' : X'.p0 + i < r := hp ▸ hi
      rw [dite_eq_left hi', dite_eq_left hi]
      have hfin : (⟨X'.p0 + i, hi'⟩ : Fin r) = ⟨X.p0 + i, hi⟩ := Fin.ext (by simp [hp])
      rw [hfin, mat_lact_castFr_eq_map_mul hΨ a x τ hτ' hτ, emb_mulVec_eq_map_mulVec_emb, Matrix.mul_inv_rev,
        Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
    · have hi' : ¬ X'.p0 + i < r := hp ▸ hi
      rw [dite_eq_right hi', dite_eq_right hi]
  · have hτ' : τ ∉ X'.Ψ := hΨ ▸ hτ
    rw [dite_eq_right hτ', dite_eq_right hτ]
    by_cases hσ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ ∈ X.Ψ
    · have hσ' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ ∈ X'.Ψ := hΨ ▸ hσ
      rw [dite_eq_left hσ', dite_eq_left hσ]
      by_cases hj : X.p0 - 1 - i < r
      · have hj' : X'.p0 - 1 - i < r := hp ▸ hj
        rw [dite_eq_left hj', dite_eq_left hj]
        have hfin : (⟨X'.p0 - 1 - i, hj'⟩ : Fin r) = ⟨X.p0 - 1 - i, hj⟩ := Fin.ext (by simp [hp])
        rw [hfin, mat_lact_castFr_eq_map_mul hΨ a x _ hσ' hσ, col_mul_eq_mulVec_col', emb_mulVec_eq_map_mulVec_emb]
        exact h.hermC_eq _ _ _
      · have hj' : ¬ X'.p0 - 1 - i < r := hp ▸ hj
        rw [dite_eq_right hj', dite_eq_right hj]
    · have hσ' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ ∉ X'.Ψ := hΨ ▸ hσ
      rw [dite_eq_right hσ', dite_eq_right hσ]

end GlobalTheory.GeoLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCoordinatesFrameRationalIsometryStatement
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_coordinates_frame_rational_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E) (h : IsMatch X X' a) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ), Formalism.L2.PjFree.perFr X' (lact a (castFr h.psi x)) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = Formalism.L2.PjFree.perFr X x v τ i := by
  first | exact @GlobalTheory.GeoLevel.perFr_lact_of_isMatch | exact GlobalTheory.GeoLevel.perFr_lact_of_isMatch | (intros; apply GlobalTheory.GeoLevel.perFr_lact_of_isMatch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroSchwartzBruhatMap
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section

namespace GlobalTheory.SchwartzBruhatRestrict

theorem map_funLeft_extendZero : ∀ (F : Type) [Field F] [NumberField F] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j →
    ∀ v : Pl (F := F), (SB (κ → Fv F v)).map (LinearMap.funLeft ℂ ℂ (fun y : κ₁ → Fv F v => Function.extend j y 0)) = SB (κ₁ → Fv F v) := by
  intro F _ _ κ₁ κ _ _ j hj v
  classical
  set ext : (κ₁ → Fv F v) → (κ → Fv F v) := fun y => Function.extend j y 0 with hext
  have hr : Function.LeftInverse (fun x : κ → Fv F v => x ∘ j) ext :=
    fun y => funext fun i => hj.extend_apply y 0 i
  have hcr : Continuous (fun x : κ → Fv F v => x ∘ j) :=
    continuous_pi fun i => continuous_apply (j i)
  have hce : Continuous ext := by
    refine continuous_pi fun k => ?_
    by_cases hk : ∃ i, j i = k
    · obtain ⟨i, rfl⟩ := hk
      simp only [ext, hj.extend_apply]
      exact continuous_apply i
    · simp only [ext, Function.extend_apply' _ _ _ hk]
      exact continuous_const
  have hemb : Topology.IsClosedEmbedding ext := hr.isClosedEmbedding hcr hce
  apply le_antisymm
  · rintro _ ⟨φ, ⟨hlc, hcs⟩, rfl⟩
    exact ⟨hlc.comp_continuous hce, hcs.comp_isClosedEmbedding hemb⟩
  · rintro φ₁ ⟨hlc, hcs⟩
    let O : Set (Fv F v) := (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    have hOeq : O = ((Valued.v : Valuation (v.adicCompletion F) _).integer : Set (v.adicCompletion F)) := by
      ext x
      simp only [O, SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
        Valuation.mem_integer_iff]
    have hOo : IsOpen O := by rw [hOeq]; exact Valued.isOpen_integer _
    have hOc : IsClosed O := by rw [hOeq]; exact Valued.isClosed_integer _
    have hOk : IsCompact O :=
      isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
    have hO0 : (0 : Fv F v) ∈ O := (v.adicCompletionIntegers F).zero_mem
    let S : Set (κ → Fv F v) := {x | ∀ k, k ∉ Set.range j → x k ∈ O}
    have hSeq : S = ⋂ k ∈ (Set.range j)ᶜ, (fun x : κ → Fv F v => x k) ⁻¹' O := by
      ext x; simp [S]
    have hSo : IsOpen S := by
      rw [hSeq]
      exact Set.Finite.isOpen_biInter (Set.toFinite _) fun k _ => hOo.preimage (continuous_apply k)
    have hSc : IsClosed S := by
      rw [hSeq]
      exact isClosed_biInter fun k _ => hOc.preimage (continuous_apply k)
    set g : (κ → Fv F v) → ℂ := fun x => φ₁ (x ∘ j) with hg
    have hglc : IsLocallyConstant g := hlc.comp_continuous hcr
    refine ⟨S.indicator g, ⟨?_, ?_⟩, ?_⟩
    · refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
      by_cases hx : x ∈ S
      · filter_upwards [hSo.mem_nhds hx, (IsLocallyConstant.iff_eventually_eq _).1 hglc x] with y hy hgy
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, hgy]
      · filter_upwards [hSc.isOpen_compl.mem_nhds hx] with y hy
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
    · let C : κ → Set (Fv F v) := fun k =>
        if h : k ∈ Set.range j then (fun y : κ₁ → Fv F v => y (Classical.choose h)) '' tsupport φ₁ else O
      have hC : IsCompact (Set.univ.pi C) := by
        refine isCompact_univ_pi fun k => ?_
        by_cases h : k ∈ Set.range j
        · simp only [C, dif_pos h]
          exact hcs.isCompact.image (continuous_apply _)
        · simp only [C, dif_neg h]
          exact hOk
      refine HasCompactSupport.intro hC fun x hx => ?_
      by_contra hne
      have hxS : x ∈ S := by
        by_contra hxS; exact hne (Set.indicator_of_notMem hxS _)
      have hgx : g x ≠ 0 := by rwa [Set.indicator_of_mem hxS] at hne
      apply hx
      intro k _
      by_cases h : k ∈ Set.range j
      · simp only [C, dif_pos h]
        refine ⟨x ∘ j, subset_tsupport _ hgx, ?_⟩
        simp only [Function.comp_apply]
        rw [Classical.choose_spec h]
      · simp only [C, dif_neg h]
        exact hxS k h
    · funext y
      rw [LinearMap.funLeft_apply]
      have hyS : ext y ∈ S := by
        intro k hk
        have hk' : ¬ ∃ i, j i = k := hk
        simp only [ext, Function.extend_apply' _ _ _ hk']
        exact hO0
      rw [Set.indicator_of_mem hyS]
      exact congrArg φ₁ (hr y)

end GlobalTheory.SchwartzBruhatRestrict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfOrthogonalTranslates
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisTotal

theorem star_char {R : Type} [CommRing R] (ψ : AddChar R ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : R) :
    star (ψ (-x)) = ψ x := by
  have h1 : ψ (-x) * ψ x = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have h2 : star (ψ (-x)) * ψ (-x) = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; simp
  calc star (ψ (-x)) = star (ψ (-x)) * (ψ (-x) * ψ x) := by rw [h1, mul_one]
    _ = ψ x := by rw [← mul_assoc, h2, one_mul]

theorem eq_zero_abstract {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G)
    [DiscreteTopology Γ] (K : Set G) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
    {R : Type} [CommRing R] [TopologicalSpace R] [ContinuousAdd R] (ψ : AddChar R ℂ) (hψc : Continuous ψ)
    (hψn : ∀ x, ‖ψ x‖ = 1) (H : G → G → R)
    (hl : ∀ x y z, H (x + y) z = H x z + H y z) (hr : ∀ x y z, H x (y + z) = H x y + H x z)
    (halt : ∀ x, H x x = 0) (hcont : Continuous fun q : G × G => H q.1 q.2)
    (hann : ∀ x, (∀ γ ∈ Γ, ψ (H x γ + H x γ) = 1) ↔ x ∈ Γ)
    (f₀ f : G → ℂ) (c₀ : Continuous f₀) (c : Continuous f)
    (q₀ : ∀ γ ∈ Γ, ∀ w, f₀ (γ + w) = ψ (-(H γ w)) * f₀ w) (q : ∀ γ ∈ Γ, ∀ w, f (γ + w) = ψ (-(H γ w)) * f w)
    (hne : f₀ ≠ 0) (μ : Measure G) (𝓕 : Set G) (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ)
    (horth : ∀ w, ∫ x in 𝓕, ψ (H x w) * f₀ (x + w) * star (f x) ∂μ = 0) : f = 0 := by
  have hskew : ∀ x y : G, H y x = -H x y := by
    intro x y
    have h := halt (x + y)
    rw [hl, hr, hr, halt x, halt y] at h
    linear_combination h
  have hz : ∀ x : G, H x 0 = 0 := by
    intro x
    have h := hr x 0 0
    rw [add_zero] at h
    linear_combination -h
  have hcy : ∀ y : G, Continuous fun x : G => H x y := fun y =>
    hcont.comp (continuous_id.prodMk continuous_const)
  have key : ∀ a : G, (fun x => ψ (H x a) * f₀ (x + a) * star (f x)) = 0 := by
    intro a
    refine GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero G Γ K hK hcov
      Γ (fun γ x => ψ (H x γ + H x γ)) ?_ ?_ ?_ ?_ ?_ ?_ μ 𝓕 hμ h𝓕 _ ?_ ?_ ?_
    · intro γ
      exact hψc.comp ((hcy _).add (hcy _))
    · intro γ x y
      rw [← AddChar.map_add_eq_mul, hl]
      congr 1; ring
    · intro γ γ' x
      rw [← AddChar.map_add_eq_mul, AddSubgroup.coe_add, hr]
      congr 1; ring
    · intro x
      rw [AddSubgroup.coe_zero, hz, add_zero, AddChar.map_zero_eq_one]
    · intro γ x
      exact hψn _
    · intro x
      rw [← hann x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩
    · exact ((hψc.comp (hcy a)).mul (c₀.comp (continuous_id.add continuous_const))).mul c.star
    · intro γ hγ x
      rw [add_assoc, q₀ γ hγ, q γ hγ, star_mul', star_char ψ hψn]
      have e : ψ (H (γ + x) a) * ψ (-(H γ (x + a))) * ψ (H γ x) = ψ (H x a) := by
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, hl, hr]
        congr 1; ring
      linear_combination (f₀ (x + a) * star (f x)) * e
    · intro γ
      have h := horth ((γ : G) + a)
      have e : ∀ x : G, ψ (H x γ + H x γ) * (ψ (H x a) * f₀ (x + a) * star (f x))
          = ψ (H γ a) * (ψ (H x (γ + a)) * f₀ (x + (γ + a)) * star (f x)) := by
        intro x
        rw [add_left_comm x, q₀ γ γ.2]
        have e' : ψ (H x γ + H x γ) * ψ (H x a) =
            ψ (H γ a) * ψ (H x (γ + a)) * ψ (-(H γ (x + a))) := by
          rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, hr, hr, hskew x γ]
          congr 1; ring
        linear_combination (f₀ (x + a) * star (f x)) * e'
      simp only [e]
      rw [integral_const_mul, h, mul_zero]
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hne
  funext x
  have h := congrFun (key (y - x)) x
  simp only [add_sub_cancel, Pi.zero_apply, mul_eq_zero, star_eq_zero] at h
  rcases h with (h | h) | h
  · have := hψn (H x (y - x))
    rw [h] at this
    simp at this
  · exact absurd h hy
  · exact h

theorem quasi_of_mem {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g)
    (γ : WO S T) (hγ : γ ∈ ratL T S) (w : WO S T) : g (γ + w) = ψ (-(symplOH S T γ w)) * g w := by
  obtain ⟨γ', rfl⟩ := hγ
  exact hg.quasi γ' w

theorem eq_zero_of_orthogonal_translates (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (S T : HSp D) (f₀ f : WO S T → ℂ) (h₀ : IsThetaFunO ψ S T f₀) (hne : f₀ ≠ 0) (hf : IsThetaFunO ψ S T f)
    (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ)
    (horth : ∀ w, ∫ x in 𝓕, heisO ψ S T w f₀ x * star (f x) ∂μ = 0) : f = 0 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨hl, hr, halt, hdbl, hcont, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  obtain ⟨hψc, hψn, -, -⟩ := hψ.1
  have hann : ∀ x : WO S T, (∀ γ ∈ ratL T S, ψ (symplOH S T x γ + symplOH S T x γ) = 1) ↔ x ∈ ratL T S := by
    intro x
    simp only [hdbl]
    exact GlobalTheory.T.rationalSymplecticPoints_self_annihilator D ψ hψ S T x
  exact eq_zero_abstract (G := WO S T) (ratL T S) K hK hcov ψ hψc hψn (symplOH S T) hl hr halt hcont hann f₀ f
    h₀.cont hf.cont (quasi_of_mem h₀) (quasi_of_mem hf) hne μ 𝓕 hμ h𝓕 horth

end GlobalTheory.HeisTotal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicMatrixMemLatticeOfColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicMatrixMemLatticeOfColumns
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.ColsInLat

open GlobalTheory.AdelicLatMove GlobalTheory.AdLat

variable {D : D7}

def lift (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  (finIncl D).rTensor D.host.E

theorem lift_eq (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    lift D z = finEmb D (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem lift_finPart (z : AE D) (h : infPart D z = 0) : lift D (finPart D z) = z := by
  have key : ∀ z : AE D, z =
      (show Ainf D.host.F →ₗ[D.host.F] AF D.host.F from
        LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)).rTensor D.host.E (infPart D z) +
      lift D (finPart D z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a e =>
      change _ = (pairA D.host.F a.1 0) ⊗ₜ[D.host.F] e + (pairA D.host.F 0 a.2) ⊗ₜ[D.host.F] e
      rw [← TensorProduct.add_tmul]
      congr 1
      exact Prod.ext (add_zero a.1).symm (zero_add a.2).symm
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← hx, ← hy]
  have := key z
  rw [h, map_zero, zero_add] at this
  exact this.symm

def col (V W : HSp D) (b : Fin V.rank) : (Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) →+ WO V W where
  toFun z := Matrix.of fun i j => if j = b then lift D (z i) else 0
  map_zero' := by ext i j; simp
  map_add' y z := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add (f := _)]
    split_ifs <;> simp

theorem col_mem (V W : HSp D) (hV : V.gram = 1) (k : GA D W) (b : Fin V.rank)
    (z : Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hz : z ∈ latGHat W k) :
    col V W b z ∈ latO V W (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E))
      (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hz
    have hz' : z ∈ hat D.host.F (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) := by
      rw [← SetLike.mem_coe, GlobalTheory.MovedLat.hat_hLat]
      rw [gLat, (GlobalTheory.Member.latHat_eq_hat_and_gram D W).1] at hz
      exact hz
    have hs : (Pi.single b 1 : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := by
      intro i _
      by_cases h : i = b
      · subst h; rw [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have := rankOne_mem_latO V W _ _ a ha _ (pure_mem_hatL _ 1 (one_mem _) _ hs) _
      (GlobalTheory.PrincInLevel.swap_mem_hatL _ z hz')
    convert this using 1
    ext i j
    change (if j = b then lift D (((1 : Af D.host.F) ⊗ₜ a) * z i) else 0) = _
    simp only [rankOne, Matrix.of_apply, hV, cF_tmul, eToEAf, Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [← TensorProduct.sum_tmul]
    have e : ∑ l, star ((Pi.single b 1 : Fin V.rank → D.host.E) l) *
        (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) l j = if j = b then 1 else 0 := by
      simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Pi.single_apply]
      split_ifs <;> simp
    rw [e]
    split_ifs
    · rw [lift_eq, map_mul, ← Algebra.TensorProduct.one_def, mul_one]
      rfl
    · simp
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem mem_latO_of_cols : ∀ (D : D7) (V W : HSp D), V.gram = 1 → ∀ (k : GA D W) (x : WO V W), x.map (infPart D) = 0 → (∀ b, (fun a => finPart D (x a b)) ∈ latGHat W k) → x ∈ (latO V W (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True) := by
  intro D V W hV k x h0 hc
  have e : x = ∑ b, col V W b fun a => finPart D (x a b) := by
    ext i j
    rw [Matrix.sum_apply]
    change _ = ∑ b, if j = b then lift D (finPart D (x i b)) else 0
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    exact (lift_finPart _ (congrFun (congrFun h0 i) j)).symm
  rw [e]
  exact sum_mem fun b _ => col_mem V W hV k b _ (hc b)

end GlobalTheory.ColsInLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicMatrixMemLatticeOfColumnsStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adelic_matrix_mem_lattice_of_columns : ∀ (D : D7) (V W : HSp D), V.gram = 1 → ∀ (k : GA D W) (x : WO V W), x.map (infPart D) = 0 → (∀ b, (fun a => finPart D (x a b)) ∈ latGHat W k) → x ∈ (latO V W (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True) := by
  first | exact @GlobalTheory.ColsInLat.mem_latO_of_cols | exact GlobalTheory.ColsInLat.mem_latO_of_cols | (intros; apply GlobalTheory.ColsInLat.mem_latO_of_cols <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopOfTie
noncomputable section

namespace GlobalTheory.ConjSpan

section General

open Formalism.IndefR.Bridge Formalism.L2.DIV

theorem span_eq_top {G Γ W W' K V₀ H : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [Field K] [NumberField K] [StarRing K] [AddCommGroup V₀] [Module K V₀]
    [AddCommGroup H] [Module ℂ H] {ι : Γ →* G} {S : CSD K} {τ σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
    {ρ' : Γ →* Module.End ℂ W'} {J : Subgroup G} {χ χ' : J →* ℂˣ} (P : ClassPres ι S τ ρ J χ)
    (c₀ : V₀ →ₛₗ[τ] W) (c₁ : V₀ →ₛₗ[σ] W') (e : S.V ≃ₗ[K] V₀) (he : ∀ x, P.coef x = c₀ (e x))
    (hspan : Submodule.span ℂ (Set.range c₁) = ⊤)
    (hact : ∀ γ v, ∃ v', c₀ v' = ρ γ (c₀ v) ∧ c₁ v' = ρ' γ (c₁ v))
    (hχ : ∀ k, ∃ a : K, τ a = (χ k : ℂ) ∧ σ a = (χ' k : ℂ))
    (E : H →ₗ[ℂ] (G → W')) (hE : Function.Injective E) (hr : LinearMap.range E = AdForms ι ρ' J χ')
    (j : S.Forms → H) (hj : ∀ x h, ∃ v, P.extL x h = c₀ v ∧ E (j x) h = c₁ v) :
    Submodule.span ℂ (Set.range j) = ⊤ := by
  classical
  have hinj : Function.Injective c₀ := by
    intro v v' h
    obtain ⟨x, rfl⟩ := e.surjective v
    obtain ⟨x', rfl⟩ := e.surjective v'
    rw [← he, ← he] at h
    rw [PresBasic.coef_injective P h]
  have hval : ∀ (x : S.Forms) c, E (j x) (P.y c) = c₁ (e ((x : S.Cl → S.V) c)) := by
    intro x c
    obtain ⟨v, h1, h2⟩ := hj x (P.y c)
    rw [ClassPres.extL_apply, PresBasic.ext_y, he] at h1
    rw [h2, hinj h1]
  have hρ : ∀ c (g : S.Gam c) (x : S.V), c₁ (e (S.ρ c g x)) =
      (χ' (stabK ι (P.stabI c g)) : ℂ) • ρ' (P.stabI c g : Γ) (c₁ (e x)) := by
    intro c g x
    obtain ⟨a, ha, ha'⟩ := hχ (stabK ι (P.stabI c g))
    obtain ⟨v', h1, h2⟩ := hact (P.stabI c g : Γ) (e x)
    have h3 : e (S.ρ c g x) = a • v' := by
      apply hinj
      rw [← he, P.coef_act, map_smulₛₗ, ha, h1, he]
    rw [h3, map_smulₛₗ, ha', h2]
  have hmem : ∀ w, E w ∈ AdForms ι ρ' J χ' := fun w => hr ▸ LinearMap.mem_range_self E w
  have hone : ∀ c (u : W'), ∃ w ∈ Submodule.span ℂ (Set.range j), ∀ c', E w (P.y c') =
      (Pi.single c (∑ g : S.Gam c, (χ' (stabK ι (P.stabI c g)) : ℂ) • ρ' (P.stabI c g : Γ) u) : S.Cl → W') c' := by
    intro c u
    have hu : u ∈ Submodule.span ℂ (Set.range c₁) := hspan ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨v, rfl⟩ := hu
      obtain ⟨x, rfl⟩ := e.surjective v
      refine ⟨j (PresBasic.avgForm S c x), Submodule.subset_span ⟨_, rfl⟩, fun c' => ?_⟩
      rw [hval]
      by_cases h : c' = c
      · subst h
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [PresBasic.avgForm, Pi.single_eq_same, map_sum, hρ]
      · simp [PresBasic.avgForm, Pi.single_eq_of_ne h]
    | zero => exact ⟨0, Submodule.zero_mem _, fun c' => by simp⟩
    | add u u' _ _ h h' =>
      obtain ⟨w, hw, h⟩ := h
      obtain ⟨w', hw', h'⟩ := h'
      refine ⟨w + w', Submodule.add_mem _ hw hw', fun c' => ?_⟩
      simp only [map_add (f := _), Pi.add_apply, h, h', smul_add, Finset.sum_add_distrib, Pi.single_add]
    | smul a u _ h =>
      obtain ⟨w, hw, h⟩ := h
      refine ⟨a • w, Submodule.smul_mem _ _ hw, fun c' => ?_⟩
      simp only [map_smul, Pi.smul_apply, h, smul_comm _ a, ← Finset.smul_sum, Pi.single_smul]
  rw [eq_top_iff]
  intro w _
  choose f hf hf' using fun c => hone c ((Fintype.card (S.Gam c) : ℂ)⁻¹ • E w (P.y c))
  have key : w = ∑ c, f c := by
    apply hE
    funext g
    obtain ⟨c, ⟨γ, k, rfl⟩, -⟩ := P.reps g
    rw [hmem w γ _ k, hmem _ γ _ k]
    congr 2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    simp only [hf']
    rw [Finset.sum_eq_single c (fun c' _ hc => Pi.single_eq_of_ne (Ne.symm hc) _) (by simp), Pi.single_eq_same]
    have hg : ∀ g : S.Gam c, (χ' (stabK ι (P.stabI c g)) : ℂ) • ρ' (P.stabI c g : Γ)
        ((Fintype.card (S.Gam c) : ℂ)⁻¹ • E w (P.y c)) = (Fintype.card (S.Gam c) : ℂ)⁻¹ • E w (P.y c) := by
      intro g
      have h1 := hmem w (P.stabI c g : Γ) (P.y c) (stabK ι (P.stabI c g))
      rw [stabK_spec] at h1
      rw [map_smul, smul_comm, ← h1]
    simp only [hg, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀, one_smul]
    exact_mod_cast Fintype.card_ne_zero
  rw [key]
  exact Submodule.sum_mem _ fun c _ => hf c

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem span_eq_top_of_tie {D : D7} {V : HSp D} {C : Bridge.CoefDat D V} {S : CSD D.what₂.LL} {J : Subgroup (Bridge.Gf V)}
    {χ χ' : J →* ℂˣ} (P : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL C.ρ J χ) {lam : D.what₂.Tau → DomWeight V.rank}
    {c₀ : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    {rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)}
    (hP : Bridge.CoefTie V C P lam c₀ pair nab del) (hM : Bridge.CoefMapTie V C c₀ rho)
    {σ : D.what₂.LL →+* ℂ} (c : CoefA V) (c₁ : VV D.what₂.LL lam →ₛₗ[σ] c.W)
    (hact : ∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE →
      ∀ v, c₁ (rho γE v) = c.ρ (γ : GA D V) (c₁ v))
    (hspan : Submodule.span ℂ (Set.range fun a => c₁ (bVV D.what₂.LL lam a)) = ⊤)
    (hχ : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjVal σ ((χ k : ℂˣ) : ℂ) ((χ' k : ℂˣ) : ℂ))
    (H : HMod (Bridge.Gf V → c.W)) {ip} (hH : H.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ J χ') ip)
    (j : S.Forms → H.H) (hj : ∀ x h, ∃ v, P.extL x h = c₀ v ∧ H.e (j x) h = c₁ v) :
    Submodule.span ℂ (Set.range j) = ⊤ := by
  obtain ⟨e, -, he, -⟩ := hP
  have hspan' : Submodule.span ℂ (Set.range c₁) = ⊤ :=
    eq_top_iff.2 (hspan.ge.trans (Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨_, rfl⟩)))
  refine span_eq_top (ρ' := c.coef.ρ) P c₀ c₁ e he hspan' (fun γ v => ?_) hχ H.e hH.1 hH.2.1 j hj
  obtain ⟨γE, h⟩ : ∃ γE, Bridge.IsRatMat V γ γE := by
    obtain ⟨g, hg⟩ := γ.2
    exact ⟨g, hg.2.symm⟩
  exact ⟨_, hM.1 γ γE h v, hact γ γE h v⟩


set_option maxHeartbeats 1600000 in
theorem span_conjForms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_jV → ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) c c₁ H j, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → Submodule.span ℂ (Set.range j) = ⊤ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hjV gramR c0R c0L hT i σ c c₁ H j hC
  obtain ⟨χ', hχ, hH⟩ := hC.model
  have h1 := hT.coefL i A.μ0
  have h2 := hT.mapL i
  refine span_eq_top_of_tie (V := Vc D i) (R.B.L i A.μ0).pres h1 h2 c c₁ hC.act hC.span hχ H hH j fun x h => ?_
  have h0 := congrFun (hjV i A.μ0 x) h
  exact (hC.base x h).imp fun v hv => ⟨h0.symm.trans hv.1, hv.2⟩

end GlobalTheory.ConjSpan

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFixedFieldEmbeddingInjective
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc.BaseChangeCent

variable {p : ℕ} [Fact p.Prime]

def shL (G : HTGroup p) : G.C →ₗ[ℚ] G.C where
  toFun := sh G
  map_add' x y := by simp only [sh, map_add (f := _), MulOpposite.unop_add]
  map_smul' q x := by
    show (G.star (q • x)).unop = q • (G.star x).unop
    rw [map_rat_smul]; rfl

theorem shL_apply (G : HTGroup p) (c : G.C) : shL G c = sh G c := rfl

def phi (G : HTGroup p) (β Y : G.C) (β' : G.C) : G.C →ₗ[ℚ] G.C × G.C :=
  (LinearMap.mulRight ℚ Y - LinearMap.mulLeft ℚ Y).prod
    (LinearMap.mulLeft ℚ β ∘ₗ LinearMap.mulRight ℚ β' ∘ₗ shL G - LinearMap.id)

theorem phi_apply (G : HTGroup p) (β Y β' c : G.C) :
    phi G β Y β' c = (c * Y - Y * c, β * sh G c * β' - c) := by
  simp [phi, shL_apply, mul_assoc]

theorem lTensor_phi (G : HTGroup p) (K : Type) [Field K] [Algebra ℚ K] (β Y β' : G.C)
    (x : K ⊗[ℚ] G.C) :
    TensorProduct.prodRight ℚ ℚ K G.C G.C ((phi G β Y β').lTensor K x) =
      (x * inC G K Y - inC G K Y * x, inC G K β * (starT G.star K x).unop * inC G K β' - x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp <;> rfl
  | tmul k c =>
    simp only [LinearMap.lTensor_tmul, phi_apply, TensorProduct.prodRight_tmul, inC, starT_tmul,
      AlgHom.coe_toRingHom, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, TensorProduct.tmul_sub, sh]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), hx, hy]
    simp only [map_add (f := _), MulOpposite.unop_add, mul_add, add_mul, Prod.mk_add_mk]
    refine Prod.ext ?_ ?_ <;> dsimp only <;> abel

end GlobalTheory.FinClsLoc.BaseChangeCent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralCoordsScalarTensorInclusion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralCoordsScalarTensorInclusion
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.FinClsLoc
open IsDedekindDomain

theorem ratAdicInt_eventually (q : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ := by
  have h := (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  filter_upwards [h] with v hv
  exact hv

theorem intC_inC_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C), ∀ᶠ w : AwayP p in Filter.cofinite,
    IntC G w (inC G (w.1.adicCompletion ℚ) c) := by
  intro p _ G c
  have hall : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ i : Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (v.adicCompletion ℚ) ((Module.finBasis ℚ G.C).repr c i) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i => ratAdicInt_eventually _
  have ht : Filter.Tendsto (Subtype.val : AwayP p → HeightOneSpectrum ℤ) Filter.cofinite Filter.cofinite :=
    Subtype.val_injective.tendsto_cofinite
  filter_upwards [ht.eventually hall] with w hw
  intro i
  have : coordL G w (inC G (w.1.adicCompletion ℚ) c) i =
      algebraMap ℚ (w.1.adicCompletion ℚ) ((Module.finBasis ℚ G.C).repr c i) := by
    have e : inC G (w.1.adicCompletion ℚ) c = (1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] c := rfl
    rw [coordL, e, Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  rw [this]; exact hw i

end GlobalTheory.FinClsLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralCoordsScalarTensorInclusionStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integralCoords_scalarTensorInclusion : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C), ∀ᶠ w : AwayP p in Filter.cofinite,
    IntC G w (inC G (w.1.adicCompletion ℚ) c) := by
  first | (exact @GlobalTheory.FinClsLoc.intC_inC_eventually) | (exact GlobalTheory.FinClsLoc.intC_inC_eventually) | (intros; apply GlobalTheory.FinClsLoc.intC_inC_eventually  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfNilpotentCommuteSeparableMinpoly
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfNilpotentCommuteSeparableMinpoly
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.ClsReg

theorem eq_zero_of_commute_of_pow_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (y₀ : G.C),
    (minpoly G.F y₀).Separable →
    (minpoly G.F y₀).natDegree = G.n → ∀ x : G.C, Commute x y₀ → ∀ k : ℕ, x ^ k = 0 → x = 0 := by
  intro p _ G y₀ hsep hdeg x hx k hk
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  ·
    have h10 : (1 : G.C) = 0 := by simpa using hk
    rw [← one_mul x, h10, zero_mul]
  have hk0 : k ≠ 0 := hkpos.ne'
  have hc := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC y₀ hsep hdeg
  have hxmem : x ∈ Subalgebra.centralizer G.F ({y₀} : Set G.C) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact hx.eq.symm
  rw [hc, Algebra.adjoin_singleton_eq_range_aeval] at hxmem
  obtain ⟨f, rfl⟩ := hxmem
  have h1 : Polynomial.aeval y₀ (f ^ k) = 0 := by
    rw [map_pow]; exact hk
  have h2 : minpoly G.F y₀ ∣ f ^ k := minpoly.dvd G.F y₀ h1
  have hsq : Squarefree (minpoly G.F y₀) := hsep.squarefree
  have h3 : minpoly G.F y₀ ∣ f := (hsq.dvd_pow_iff_dvd hk0).1 h2
  obtain ⟨g, hg⟩ := h3
  show Polynomial.aeval y₀ f = 0
  rw [hg, map_mul, minpoly.aeval, zero_mul]

end GlobalTheory.LKCx.ClsReg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfNilpotentCommuteSeparableMinpolyStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_nilpotent_commute_separable_minpoly : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (y₀ : G.C), (minpoly G.F y₀).Separable →
    (minpoly G.F y₀).natDegree = G.n → ∀ x : G.C, Commute x y₀ → ∀ k : ℕ, x ^ k = 0 → x = 0 := by
  first | (exact @GlobalTheory.LKCx.ClsReg.eq_zero_of_commute_of_pow_eq_zero) | (exact GlobalTheory.LKCx.ClsReg.eq_zero_of_commute_of_pow_eq_zero) | (intros; apply GlobalTheory.LKCx.ClsReg.eq_zero_of_commute_of_pow_eq_zero <;> assumption)
end
end
