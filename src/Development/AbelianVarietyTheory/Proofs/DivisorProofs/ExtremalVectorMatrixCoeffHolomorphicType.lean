module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmFnAndKilledFnOfHolFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeOfSmoothBorelKilled
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftWeightSizesEventuallyAlongFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostNormClassCount
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthStalkNeTopOfNoGenerisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterThetaInvariantExponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreserving
public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorMatrixCoeffHolomorphicType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorMatrixCoeffHolomorphicType
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.CoefExt

open GlobalTheory.HolDict.HolTo

section General

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {Hm : ι → Mt n} {H : ι → Type}
  [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)] {σ : ∀ τ, Mt n → (H τ →L[ℂ] H τ)} {v : ∀ τ, H τ}

omit [Fintype ι] in
theorem prod_single_apply (k : ℕ) (τs : Fin k → ι) (Xs : Fin k → Mt n) (t : Fin k → ℝ) (ρ : ι) :
    (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod ρ =
      (List.ofFn fun i => NormedSpace.exp (t i • (if ρ = τs i then Xs i else 0))).prod := by
  rw [Pi.list_prod_apply, List.map_ofFn]
  congr 2
  funext i
  by_cases h : ρ = τs i
  · subst h
    simp
  · simp [h]

theorem smFn_coef (hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ))
    (hv : ∀ τ, SmoothVec (lieH (Hm τ)) (σ τ) (v τ)) :
    SmFn Hm fun u => ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ := by
  intro k τs Xs hX u hu
  have hmem : ∀ t : Fin k → ℝ, (List.ofFn fun i =>
      (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod ∈ UG Hm := fun t =>
    prod_mem_UG _ fun v hv => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
      exact single_mem_UG Hm _ (hX i) _
  refine contDiff_prod fun ρ _ => ?_
  simp only [Pi.mul_apply, (hσ ρ).2 _ (hu ρ) _ (hmem _ ρ), ContinuousLinearMap.comp_apply]
  simp only [prod_single_apply]
  have h1 := hv ρ k (fun i => if ρ = τs i then Xs i else 0) fun i => by
    split_ifs with h
    · subst h
      exact hX i
    · show _ = _
      simp
  exact (((innerSL ℂ (v ρ)).comp (σ ρ (u ρ))).restrictScalars ℝ).contDiff.comp h1

theorem hasDerivAt_of_smooth {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {L : Set (Mt n)}
    {π : Mt n → (K →L[ℂ] K)} {x : K} (hx : SmoothVec L π x) {X : Mt n} (hX : X ∈ L) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) x) (dRep π X x) 0 := by
  have h1 := hx 1 (fun _ => X) fun _ => hX
  have h2 : ContDiff ℝ ∞ (fun r : ℝ => (fun _ => r : Fin 1 → ℝ)) := by fun_prop
  have h3 := (h1.comp h2).differentiable (by simp)
  have h4 : Differentiable ℝ fun t : ℝ => π (NormedSpace.exp (t • X)) x := by
    have e : (fun t : ℝ => π (NormedSpace.exp (t • X)) x) = ((fun t : Fin 1 → ℝ =>
        π ((List.ofFn fun i => NormedSpace.exp (t i • X)).prod) x) ∘ fun r _ => r) := by
      funext r
      simp
    rw [e]
    exact h3
  exact (h4 0).hasDerivAt

theorem der_coef (hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ))
    (hv : ∀ τ, SmoothVec (lieH (Hm τ)) (σ τ) (v τ)) (τ : ι) {X : Mt n} (hX : X ∈ lieH (Hm τ)) {u : ι → Mt n}
    (hu : u ∈ UG Hm) :
    der τ X (fun u => ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ) u =
      ⟪v τ, σ τ (u τ) (dRep (σ τ) X (v τ))⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪v ρ, σ ρ (u ρ) (v ρ)⟫_ℂ := by
  unfold der
  have e : (fun t : ℝ => ∏ ρ, ⟪v ρ, σ ρ ((u * (Pi.mulSingle τ (NormedSpace.exp (t • X)) : ι → Mt n)) ρ) (v ρ)⟫_ℂ) =
      fun t : ℝ => ⟪v τ, σ τ (u τ) (σ τ (NormedSpace.exp (t • X)) (v τ))⟫_ℂ *
        ∏ ρ ∈ Finset.univ.erase τ, ⟪v ρ, σ ρ (u ρ) (v ρ)⟫_ℂ := by
    funext t
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Pi.mul_apply,
      (hσ τ).2 _ (hu τ) _ (single_mem_UG Hm τ hX t τ), Pi.mulSingle_eq_same]
    congr 1
    refine Finset.prod_congr rfl fun ρ hρ => ?_
    rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hρ), mul_one]
  rw [e]
  have h1 := (((innerSL ℂ (v τ)).comp (σ τ (u τ))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_of_smooth (hv τ) hX)
  exact (h1.mul_const _).deriv

theorem derC_coef {q : ι → ℕ} {x₀ : ι → Mt n} (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ))
    (hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ))
    (hv : ∀ τ, SmoothVec (lieH (Hm τ)) (σ τ) (v τ)) (τ : ι) (Z : Mt n) {u : ι → Mt n} (hu : u ∈ UG Hm) :
    derC Hm τ Z (fun u => ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ) u =
      ⟪v τ, σ τ (u τ) (dRepC (Hm τ) (σ τ) Z (v τ))⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪v ρ, σ ρ (u ρ) (v ρ)⟫_ℂ := by
  obtain ⟨h1, h2⟩ := conj_facts (herm_of_orth (h τ)) (dets_ne (h τ)).1 Z
  have hA : (1 / 2 : ℂ) • (Z + conjH (Hm τ) Z) ∈ lieH (Hm τ) := by
    show _ = _
    rw [conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h1, h2]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]
    abel_nf
    simp
  have hB : (1 / (2 * Complex.I) : ℂ) • (Z - conjH (Hm τ) Z) ∈ lieH (Hm τ) := by
    show _ = _
    rw [conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
    have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp
    rw [this, neg_smul, ← smul_neg, ← smul_add]
    abel_nf
    simp
  unfold derC dRepC
  rw [der_coef hσ hv τ hA hu, der_coef hσ hv τ hB hu, map_add (f := _), map_smul, inner_add_right, inner_smul_right]
  ring

theorem killedFn_coef {q : ι → ℕ} {x₀ : ι → Mt n} {w : ι → Fin n → ℤ} (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ))
    (hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ))
    (hv : ∀ τ, SmoothVec (lieH (Hm τ)) (σ τ) (v τ))
    (hk : ∀ τ (a c : Fin n), a ≤ c → dRepC (Hm τ) (σ τ) (x₀ τ * Matrix.single a c 1 * (x₀ τ)⁻¹) (v τ) =
      if a = c then (w τ a : ℂ) • v τ else 0) :
    KilledFn Hm x₀ w fun u => ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ := by
  intro τ a c hac u hu
  rw [derC_coef h hσ hv τ _ hu, hk τ a c hac]
  split_ifs
  · rw [map_smul, inner_smul_right, mul_assoc]
    beta_reduce
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  · simp

end General

theorem arr_bijective {n q : ℕ} (hq : q ≤ n) : Function.Bijective (arr (n := n) q) := by
  refine Finite.injective_iff_bijective.1 fun a b hab => ?_
  have h := congrArg Fin.val hab
  have := a.2
  have := b.2
  unfold arr at h
  apply Fin.ext
  split_ifs at h <;> simp only at h <;> omega

theorem diagonal_mem_Kset {n : ℕ} (ε : Fin n → Bool) (s : Fin n → ℝ) :
    diagonal (fun a => Complex.exp ((s a : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    simp only [Pi.star_apply]
    change Complex.exp ((s i : ℂ) * Complex.I) * (starRingEnd ℂ) (Complex.exp ((s i : ℂ) * Complex.I)) = 1
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp
  · unfold Formalism.REAL.Jm
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext a
    ring

theorem torus_ext {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {w : D.what₂.Tau → Fin V.rank → ℤ}
    {v : M.Vec} (hw : WtIs M w) (hv : IsExtVec M v) (s : D.what₂.Tau → Fin V.rank → ℝ) (τ : D.what₂.Tau)
    (hx : (x0Mat M τ).det ≠ 0) :
    M.rep τ (torEl (x0Mat M) s τ) (v τ : M.H τ) =
      (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) • (v τ : M.H τ) := by
  set e := Equiv.ofBijective _ (arr_bijective (nNeg_le (M.ε τ))) with he
  have hfr : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 := torus_x0Mat M τ fun a => Complex.exp ((s τ (e.symm a) : ℂ) * Complex.I)
  have h2 : ∀ c, e.symm (arr (nNeg (M.ε τ)) c) = c := fun c => e.symm_apply_apply c
  simp only [h2] at h1
  have h3 : M.fr τ * torEl (x0Mat M) s τ * (M.fr τ)⁻¹ =
      diagonal fun a => Complex.exp ((s τ (e.symm a) : ℂ) * Complex.I) := by
    unfold torEl
    rw [← h1, Matrix.mul_nonsing_inv_cancel_right _ _ hx.isUnit, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hfr, Matrix.mul_nonsing_inv_cancel_right _ _ hfr]
  unfold DSModel.rep
  rw [h3, (hv τ).2.2 (fun a => s τ (e.symm a)) (diagonal_mem_Kset _ _)]
  congr 1
  rw [← e.sum_comp]
  simp only [← Complex.exp_int_mul, ← Complex.exp_sum, Equiv.symm_apply_apply]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h4 : extWt M τ (e c) = (w τ c : ℝ) := (hw τ c).symm
  rw [h4]
  push_cast
  ring

end GlobalTheory.HolDict.CoefExt

namespace GlobalTheory.HolDict


open CoefExt in
theorem holFn_coef_extVec : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w (fun u => ∏ τ, ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ) ∧ ∀ s τ, M.rep τ (torEl (x0Mat M) s τ) (v τ : M.H τ) = (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) • (v τ : M.H τ) := by
  intro D θ V S M w v hθ hM hw hv
  classical
  have ho : ∀ τ, OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) := fun τ => ((GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.2.2 hM).1
  have hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1.1
  have hk := GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight D θ V S M w v hθ hM hw hv
  refine ⟨GlobalTheory.T.holomorphicType_of_smooth_borelKilled _ _ _ _ _ _ ho _ (smFn_coef hσ fun τ => (hk τ).1)
    (killedFn_coef ho hσ (fun τ => (hk τ).1) fun τ => (hk τ).2), fun s τ => ?_⟩
  exact torus_ext M hw hv s τ (HolTo.dets_ne (ho τ)).2

end GlobalTheory.HolDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorMatrixCoeffHolomorphicTypeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extremalVector_matrixCoeff_holomorphicType : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w (fun u => ∏ τ, ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ) ∧ ∀ s τ, M.rep τ (torEl (x0Mat M) s τ) (v τ : M.H τ) = (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) • (v τ : M.H τ) := by
  first | exact @GlobalTheory.HolDict.holFn_coef_extVec | exact GlobalTheory.HolDict.holFn_coef_extVec | (intros; apply GlobalTheory.HolDict.holFn_coef_extVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberSheafEqSumLengthMulCycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimAddOneLeOfSsubsetStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_add_one_le_of_irreducible_ssubset : ∀ (T : Type) [TopologicalSpace T] (A B : Set T), IsClosed A → IsIrreducible A → IsIrreducible B → A ⊂ B → topologicalKrullDim A + 1 ≤ topologicalKrullDim B := by
  first | exact @GlobalTheory.topologicalKrullDim_add_one_le_of_ssubset | exact GlobalTheory.topologicalKrullDim_add_one_le_of_ssubset | (intros; apply GlobalTheory.topologicalKrullDim_add_one_le_of_ssubset <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberSheafEqSumLengthMulCycle
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SheafCycle

theorem dim_add_one_le {T : Type} [TopologicalSpace T] {A B : Set T} (hA : IsClosed A)
    (hAi : IsIrreducible A) (hBi : IsIrreducible B) (h : A ⊂ B) :
    topologicalKrullDim A + 1 ≤ topologicalKrullDim B :=
  GlobalTheory.T.topologicalKrullDim_add_one_le_of_irreducible_ssubset T A B hA hAi hBi h

theorem length_stalk_ne_top {X : Scheme.{0}} [IsLocallyNoetherian X] (F : X.Modules)
    [QCoh.IsFiniteQC F] (w : X) (h : ∀ y ∈ QCoh.support F, w ∈ closure {y} → y = w) :
    Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) ≠ ⊤ :=
  GlobalTheory.T.length_stalk_ne_infty_of_no_generization X F w h

theorem length_stalk_pushforward_generic {X : Scheme.{0}} (Z : Closeds X)
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme]
    (G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules) [QCoh.IsFiniteQC G] :
    Module.length (X.presheaf.stalk (redι Z (genericPoint _)))
      (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk (redι Z (genericPoint _)) :) =
      (GlobalTheory.VB.genRank G : ℕ∞) :=
  GlobalTheory.T.length_stalk_reducedClosed_genericPoint_eq_rank X Z G

theorem lt_of_add_one_le_natCast {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ n) : a < n := _root_.GlobalTheory.CompanionTheory.Ar.IntersectionNumberLength.lt_of_add_one_le_natCast (a := a) (n := n) h

open QCoh

variable {κ : Type} [Field κ] {X : Scheme.{0}} [Algebra κ Γ(X, ⊤)]

theorem length_stalk_eq_zero_of_notMem {F : X.Modules} {w : X} (h : w ∉ support F) :
    Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) = 0 := by
  haveI := notMem_support_iff.1 h
  exact Module.length_eq_zero

theorem dim_closure_le_suppDim {F : X.Modules} [IsFiniteQC F] {w : X} (h : w ∈ support F) :
    topologicalKrullDim (closure {w} : Set X) ≤ suppDim F := by
  rw [suppDim_eq_iSup_closure F]
  exact le_iSup₂ (f := fun x (_ : x ∈ support F) ↦ topologicalKrullDim (closure {x} : Set X)) w h

theorem eq_of_mem_closure {F : X.Modules} [IsFiniteQC F] {n : ℕ} (hd : suppDim F ≤ n) {w : X}
    (hw : topologicalKrullDim (closure {w} : Set X) = n) :
    ∀ y ∈ support F, w ∈ closure {y} → y = w := by
  intro y hy hwy
  have hsub : closure {w} ⊆ closure {y} :=
    isClosed_closure.closure_subset_iff.2 (Set.singleton_subset_iff.2 hwy)
  by_cases he : closure ({w} : Set X) = closure {y}
  · exact (inseparable_iff_closure_eq.2 he.symm).eq
  · have h1 := dim_add_one_le isClosed_closure isIrreducible_singleton.closure
      isIrreducible_singleton.closure (ssubset_of_subset_of_ne hsub he)
    have h2 := (dim_closure_le_suppDim hy).trans hd
    rw [hw] at h1
    have h3 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ n := by push_cast; exact h1.trans h2
    exact absurd (by exact_mod_cast h3 : n + 1 ≤ n) (by omega)


variable (κ) in
theorem interNumRed_eq_zero (hp : IsProjOver (strHom κ (X := X))) {ι : Type} [Fintype ι]
    {P : ι → LB X} (hP : ∀ i, (P i).IsLB) (C : Closeds X)
    (hC : topologicalKrullDim (C : Set X) < (Fintype.card ι : ℕ)) : interNumRed κ C P = 0 := by
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  have : IsLocallyNoetherian X := (isNoetherian_of_isProjOver hp).toIsLocallyNoetherian
  have hAV : IsAmpleLB (A.pull (redι C)) := hA.pull_of_isClosedImmersion _
  haveI : IsFiniteQC ((Scheme.Modules.pushforward (redι C)).obj (structureModule _)) :=
    ProperFinite.isFiniteQC_pushforward (redι C) hAV _
  refine interNum_eq_zero_of_isProjOver (algebraMap_eq_strHom κ X) _ hp ?_ hP
  refine lt_of_le_of_lt (topologicalKrullDim_mono ?_) hC
  exact (support_pushforward_subset_image_of_isClosedImmersion (redι C) _).trans
    ((Set.image_subset_range _ _).trans (range_redι C).le)

theorem interNum_eq_sum_length_mul_interNumRed : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ (X := X)) → ∀ (ι : Type) [Fintype ι] (P : ι → LB X), (∀ i, (P i).IsLB) → ∀ (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F], GlobalTheory.QCoh.suppDim F ≤ (Fintype.card ι : ℕ) → ∀ S : Finset X, (∀ w ∈ GlobalTheory.QCoh.support F, topologicalKrullDim (closure ({w} : Set X)) = (Fintype.card ι : ℕ) → w ∈ S) → interNum κ F P = ∑ w ∈ S, ((Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :)).toNat : ℤ) * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  intro κ _ X _ hp ι _ P hP F hF
  have hf := algebraMap_eq_strHom κ X
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  set n := Fintype.card ι with hn
  let term : X.Modules → X → ℤ := fun E w ↦
    ((Module.length (X.presheaf.stalk w) (E.presheaf.stalk w :)).toNat : ℤ) *
      interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P

  have hsmall : ∀ (E : X.Modules) (w : X), topologicalKrullDim (closure ({w} : Set X)) < n →
      term E w = 0 := fun E w h ↦ by
    simp only [term, interNumRed_eq_zero κ hp hP ⟨closure {w}, isClosed_closure⟩ h, mul_zero]
  have hout : ∀ (E : X.Modules) (w : X), w ∉ support E → term E w = 0 := fun E w h ↦ by
    simp only [term, length_stalk_eq_zero_of_notMem h, ENat.toNat_zero, Nat.cast_zero, zero_mul]
  let Q : X.Modules → Prop := fun E ↦ suppDim E ≤ n → ∀ S : Finset X,
    (∀ w ∈ support E, topologicalKrullDim (closure ({w} : Set X)) = n → w ∈ S) →
      interNum κ E P = ∑ w ∈ S, term E w
  suffices H : Q F from H
  refine GlobalTheory.QCoh.devissage X Q ?_ ?_ ?_ F hF
  · intro E hE _ S _
    rw [interNum_eq_zero_of_isZero κ hE hP]
    refine (Finset.sum_eq_zero fun w _ ↦ hout E w ?_).symm
    rw [support_eq_empty_iff.2 hE]
    exact Set.notMem_empty w
  · intro C hC h₁ h₃ Q₁ Q₃ hd S hS
    haveI := h₁
    haveI := h₃
    haveI := hC.mono_f
    haveI := hC.epi_g
    have hd₁ : suppDim C.X₁ ≤ n := (suppDim_le_of_mono C.f).trans hd
    have hd₃ : suppDim C.X₃ ≤ n := (suppDim_le_of_epi C.g).trans hd
    rw [interNum_shortExact hC hP (finiteCohTwists_of_isProjOver hf _ hp)
        (finiteCohTwists_of_isProjOver hf _ hp),
      Q₁ hd₁ S (fun w hw ↦ hS w (support_subset_of_mono C.f hw)),
      Q₃ hd₃ S (fun w hw ↦ hS w (support_subset_of_epi C.g hw)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    by_cases hw : topologicalKrullDim (closure ({w} : Set X)) < n
    · rw [hsmall _ _ hw, hsmall _ _ hw, hsmall _ _ hw, add_zero]
    have hfin : ∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ n →
        Module.length (X.presheaf.stalk w) (E.presheaf.stalk w :) ≠ ⊤ := fun E _ hE ↦ by
      by_cases hm : w ∈ support E
      · have he : topologicalKrullDim (closure ({w} : Set X)) = n :=
          le_antisymm ((dim_closure_le_suppDim hm).trans hE) (not_lt.1 hw)
        exact length_stalk_ne_top E w (eq_of_mem_closure hE he)
      · rw [length_stalk_eq_zero_of_notMem hm]; exact ENat.zero_ne_top
    have hex := Module.length_eq_add_of_exact (stalkLinear C.f w) (stalkLinear C.g w)
      (stalkLinear_injective C.f w) (stalkLinear_surjective C.g w)
      ((exact_iff_stalkLinear C).1 hC.exact w)
    simp only [term]
    rw [hex, ENat.toNat_add (hfin C.X₁ hd₁) (hfin C.X₃ hd₃)]
    push_cast
    ring
  · intro Z hZ hsm G hG hd S hS
    haveI := hG
    haveI := isIntegral_red hZ
    have hAV : IsAmpleLB (A.pull (redι Z)) := hA.pull_of_isClosedImmersion _
    haveI hFq : IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj G) :=
      ProperFinite.isFiniteQC_pushforward (redι Z) hAV G
    have hsupp : support ((Scheme.Modules.pushforward (redι Z)).obj G) ⊆ (Z : Set X) :=
      (support_pushforward_subset_image_of_isClosedImmersion (redι Z) G).trans
        ((Set.image_subset_range _ _).trans (range_redι Z).le)
    by_cases hss : support ((Scheme.Modules.pushforward (redι Z)).obj G) = (Z : Set X)
    swap
    · exact hsm _ hFq (ssubset_of_subset_of_ne hsupp hss) hd S hS
    have hdZ : topologicalKrullDim (Z : Set X) ≤ n := by
      rw [← hss]; exact hd

    have hlt : ∀ w ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G),
        closure ({w} : Set X) ≠ Z → topologicalKrullDim (closure ({w} : Set X)) < n := by
      intro w hw hne
      have hwZ : closure ({w} : Set X) ⊆ Z :=
        Z.isClosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 (hsupp hw))
      have h1 := dim_add_one_le isClosed_closure isIrreducible_singleton.closure hZ
        (ssubset_of_subset_of_ne hwZ hne)
      exact lt_of_add_one_le_natCast (h1.trans hdZ)
    rcases lt_or_eq_of_le hdZ with hZlt | hZeq
    · rw [interNum_eq_zero_of_isProjOver hf _ hp (by rw [suppDim, hss]; exact hZlt) hP]
      refine (Finset.sum_eq_zero fun w _ ↦ ?_).symm
      by_cases hw : w ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G)
      · refine hsmall _ _ (lt_of_le_of_lt (topologicalKrullDim_mono ?_) hZlt)
        exact Z.isClosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 (hsupp hw))
      · exact hout _ _ hw
    set η := redι Z (genericPoint (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) with hη
    have hcl : closure ({η} : Set X) = Z := by
      rw [hη, ← Set.image_singleton, (redι Z).isClosedEmbedding.closure_image_eq,
        (genericPoint_spec _).def, Set.image_univ, range_redι]
    have hηs : η ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G) := by
      rw [hss]; exact (range_redι Z).le ⟨_, rfl⟩
    rw [Finset.sum_eq_single_of_mem η (hS η hηs (by rw [hcl]; exact hZeq)) fun w _ hne ↦ ?_]
    swap
    · by_cases hw : w ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G)
      · refine hsmall _ _ (hlt w hw fun e ↦ hne ?_)
        exact (inseparable_iff_closure_eq.2 (e.trans hcl.symm)).eq
      · exact hout _ _ hw
    simp only [term]
    rw [length_stalk_pushforward_generic Z G, ENat.toNat_natCast]
    have hC : (⟨closure {η}, isClosed_closure⟩ : Closeds X) = Z := Closeds.ext hcl
    rw [hC]
    letI : Algebra κ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
      algebraΓOfHom (redι Z ≫ strHom κ X)
    have hfZ : ∀ r : κ, (redι Z).appTop (algebraMap κ Γ(X, ⊤) r) =
        algebraMap κ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r := fun r ↦ by
      rw [hf r]; rfl
    have hstr : strHom κ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = redι Z ≫ strHom κ X :=
      strHom_eq fun _ ↦ rfl
    have hpZ : IsProjOver (strHom κ (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
      rw [hstr]; exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
    have hdimZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤
        (Fintype.card ι : ℕ) := by
      rw [topologicalKrullDim_red]; exact hdZ
    rw [interNum_pushforward_of_isClosedImmersion hfZ G hP,
      GlobalTheory.T.lineBundleIntersectionNumber_eq_genericRank_mul κ _ hpZ ι hdimZ G _ (fun i ↦ pull_isLB (hP i) _), interNumRed_def, interNumSub_def,
      interNumOn_def, interNum_pushforward_of_isClosedImmersion hfZ _ hP]

end GlobalTheory.SheafCycle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberSheafEqSumLengthMulCycleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_sheaf_eq_sum_length_mul_cycle : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ (X := X)) → ∀ (ι : Type) [Fintype ι] (P : ι → LB X), (∀ i, (P i).IsLB) → ∀ (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F], GlobalTheory.QCoh.suppDim F ≤ (Fintype.card ι : ℕ) → ∀ S : Finset X, (∀ w ∈ GlobalTheory.QCoh.support F, topologicalKrullDim (closure ({w} : Set X)) = (Fintype.card ι : ℕ) → w ∈ S) → interNum κ F P = ∑ w ∈ S, ((Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :)).toNat : ℤ) * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  first | exact @GlobalTheory.SheafCycle.interNum_eq_sum_length_mul_interNumRed | exact GlobalTheory.SheafCycle.interNum_eq_sum_length_mul_interNumRed | (intros; apply GlobalTheory.SheafCycle.interNum_eq_sum_length_mul_interNumRed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolynomialsBoundedFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorOfValuationLeCofinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorOfValuationLeCofinite
open NumberField IsDedekindDomain

namespace GlobalTheory.ValBoundDenom

theorem exists_nat_le_exp (a : WithZero (Multiplicative ℤ)) : ∃ n : ℕ, a ≤ WithZero.exp (n : ℤ) := by
  induction a using WithZero.recZeroCoe with
  | zero => exact ⟨0, zero_le'⟩
  | coe m =>
    refine ⟨(Multiplicative.toAdd m).toNat, ?_⟩
    show (m : WithZero (Multiplicative ℤ)) ≤ ((Multiplicative.ofAdd ((Multiplicative.toAdd m).toNat : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    rw [WithZero.coe_le_coe]
    exact Int.self_le_toNat (Multiplicative.toAdd m)

theorem exists_common_denominator_of_valuation_le (E : Type) [Field E] [NumberField E]
    (β : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ))
    (hβ : ∀ᶠ w in Filter.cofinite, β w ≤ 1) : ∃ D : 𝓞 E, D ≠ 0 ∧
      ∀ x : E, (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E x ≤ β w) →
        IsIntegral ℤ ((D : E) * x) := by
  classical
  have hfin : {w | ¬ β w ≤ 1}.Finite := Filter.eventually_cofinite.mp hβ
  set T := hfin.toFinset with hT
  choose k hk using fun w => exists_nat_le_exp (β w)
  set I : Ideal (𝓞 E) := ∏ w ∈ T, w.asIdeal ^ k w with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro w _
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)
  obtain ⟨D, hDI, hD0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  refine ⟨D, hD0, fun x hx => ?_⟩
  have hle : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E ((D : E) * x) ≤ 1 := by
    intro w
    rw [map_mul]
    by_cases hw : w ∈ T
    · have hmem : D ∈ w.asIdeal ^ k w :=
        (Finset.inf_le hw : T.inf (fun w => w.asIdeal ^ k w) ≤ _) (Ideal.prod_le_inf hDI)
      have h1 : w.valuation E (D : E) ≤ WithZero.exp (-(k w : ℤ)) := by
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).mpr hmem
      have h2 : w.valuation E x ≤ WithZero.exp (k w : ℤ) := (hx w).trans (hk w)
      calc w.valuation E (D : E) * w.valuation E x
          ≤ WithZero.exp (-(k w : ℤ)) * WithZero.exp (k w : ℤ) := mul_le_mul' h1 h2
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · have hw1 : β w ≤ 1 := by
        by_contra h
        exact hw (by rw [hT, Set.Finite.mem_toFinset]; exact h)
      exact mul_le_one' (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _) ((hx w).trans hw1)
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one E _ hle
  rw [← hr]
  exact r.isIntegral_coe

end GlobalTheory.ValBoundDenom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorOfValuationLeCofiniteStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_of_valuation_le_cofinite : ∀ (E : Type) [Field E] [NumberField E] (β : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)),
    (∀ᶠ w in Filter.cofinite, β w ≤ 1) → ∃ D : 𝓞 E, D ≠ 0 ∧
      ∀ x : E, (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E x ≤ β w) → IsIntegral ℤ ((D : E) * x) := by
  first | exact @GlobalTheory.ValBoundDenom.exists_common_denominator_of_valuation_le | exact GlobalTheory.ValBoundDenom.exists_common_denominator_of_valuation_le | (intros; apply GlobalTheory.ValBoundDenom.exists_common_denominator_of_valuation_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicCoeffNatDegreeSubEqMulCmConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicCoeffNatDegreeSubEqMulCmConj
open NumberField Polynomial

namespace GlobalTheory

theorem coeff_natDegree_sub_eq_of_roots_norm_one (Q : ℂ[X]) (hQ : Q.Monic)
    (hroots : ∀ z ∈ Q.roots, ‖z‖ = 1) :
    ∀ i ≤ Q.natDegree, Q.coeff (Q.natDegree - i) = Q.coeff 0 * starRingEnd ℂ (Q.coeff i) := by
  intro i hi
  set s := Q.roots with hs
  have hprod : (s.map fun z => X - C z).prod = Q := by
    have h := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := Q) IsAlgClosed.card_roots_eq_natDegree
    rwa [hQ.leadingCoeff, C_1, one_mul] at h
  have hrevX : ∀ z ∈ s, (X - C z : ℂ[X]).reverse = C (-z) * (X - C (starRingEnd ℂ z)) := by
    intro z hz
    have hz1 : z * starRingEnd ℂ z = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hroots z hz]; simp
    rw [sub_eq_add_neg, ← C_neg, reverse_add_C, natDegree_X, ← one_mul (X : ℂ[X]), reverse_mul_X, ← C_1, reverse_C]
    rw [mul_sub, ← C_mul, neg_mul, hz1]
    simp only [C_1, C_neg, one_mul, pow_one]
    ring
  have hrev : Q.reverse = C (Q.coeff 0) * Q.map (starRingEnd ℂ) := by
    have key : ∀ t : Multiset ℂ, (∀ z ∈ t, (X - C z : ℂ[X]).reverse = C (-z) * (X - C (starRingEnd ℂ z))) →
        (t.map fun z => X - C z).prod.reverse
          = (t.map fun z => C (-z) * (X - C (starRingEnd ℂ z))).prod := by
      intro t
      induction t using Multiset.induction_on with
      | empty => intro _; simpa using reverse_C (1 : ℂ)
      | cons a t ih =>
        intro h
        rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons,
          reverse_mul_of_domain, ih (fun z hz => h z (Multiset.mem_cons_of_mem hz)),
          h a (Multiset.mem_cons_self a t)]
    conv_lhs => rw [← hprod]
    rw [key s hrevX, Multiset.prod_map_mul]
    conv_rhs => rw [← hprod]
    congr 1
    · rw [coeff_zero_multiset_prod, Multiset.map_map, map_multiset_prod, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro z _
      simp
    · rw [Polynomial.map_multiset_prod, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro z _
      simp
  have h1 := congrArg (fun p => p.coeff i) hrev
  simp only [coeff_reverse, coeff_C_mul, coeff_map] at h1
  rwa [revAt_le hi] at h1

theorem monic_coeff_natDegree_sub_eq_mul_complexConj :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : Polynomial E),
    P.Monic → P.natDegree = n → (∀ (τ : E →+* ℂ), ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) →
    ∀ i ≤ n, P.coeff (n - i) = P.coeff 0 * IsCMField.complexConj E (P.coeff i) := by
  intro E _ _ _ n P hP hn hroots i hi
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  have hQ : (P.map τ).Monic := hP.map τ
  have hdeg : (P.map τ).natDegree = n := by rw [hP.natDegree_map, hn]
  have h := coeff_natDegree_sub_eq_of_roots_norm_one (P.map τ) hQ (hroots τ) i (hdeg ▸ hi)
  rw [hdeg, coeff_map, coeff_map, coeff_map, ← IsCMField.complexEmbedding_complexConj E τ,
    ← map_mul] at h
  exact τ.injective h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicCoeffNatDegreeSubEqMulCmConjStatement
open NumberField Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monic_coeff_natDegree_sub_eq_mul_cmConj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : Polynomial E),
    P.Monic → P.natDegree = n → (∀ (τ : E →+* ℂ), ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) →
    ∀ i ≤ n, P.coeff (n - i) = P.coeff 0 * IsCMField.complexConj E (P.coeff i) := by
  first | exact @GlobalTheory.monic_coeff_natDegree_sub_eq_mul_complexConj | exact GlobalTheory.monic_coeff_natDegree_sub_eq_mul_complexConj | (intros; apply GlobalTheory.monic_coeff_natDegree_sub_eq_mul_complexConj <;> assumption)
end
end

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.BCT.GeoFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem norm_coeff_le {n : ℕ} {P : E[X]} (hP : P ∈ Ell E n) (τ : E →+* ℂ) (i : ℕ) :
    ‖τ (P.coeff i)‖ ≤ n.choose i := by
  obtain ⟨hm, hd, -, hr⟩ := hP
  have h := Polynomial.coeff_le_of_roots_le (f := τ) (B := 1) i hm (IsAlgClosed.splits _)
    (fun z hz => (hr τ z hz).le)
  rw [one_pow, one_mul, hd, Polynomial.coeff_map] at h
  exact h

theorem valued_algebraMap (w : Pl E) (k : E) :
    Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
  Formalism.UG.P.levelaf_valued_algebraMap w k

theorem valuation_conjE (w : Pl E) (k : E) :
    w.valuation E (GlobalTheory.SplitPts.conjE E k) = (conjSrc (GlobalTheory.SplitPts.conjE E) w).valuation E k := by
  have h := (conjLoc_spec (GlobalTheory.SplitPts.conjE E) w).2.2 (algebraMap E _ k)
  rw [(conjLoc_spec (GlobalTheory.SplitPts.conjE E) w).2.1, valued_algebraMap, valued_algebraMap] at h
  exact h

theorem valuation_coeff_le {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) {γ : Pl E → WithZero (Multiplicative ℤ)} (hγ0 : ∀ w, γ w ≠ 0)
    {P : E[X]} (hP : P ∈ Ell E n) (hPS : ∀ w ∈ S, (∀ i, Valued.v ((atPl w P).coeff i) ≤ γ w) ∧
      (γ w)⁻¹ ≤ Valued.v ((atPl w P).coeff 0)) (w : Pl E) (i : ℕ) :
    w.valuation E (P.coeff i) ≤ if w ∈ S then γ w else γ (conjSrc (GlobalTheory.SplitPts.conjE E) w) ^ 2 := by
  have hv : ∀ u ∈ S, (∀ j, u.valuation E (P.coeff j) ≤ γ u) ∧ (γ u)⁻¹ ≤ u.valuation E (P.coeff 0) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hPS u hu
    refine ⟨fun j => ?_, ?_⟩
    · have := h1 j
      rwa [atPl, Polynomial.coeff_map, valued_algebraMap] at this
    · rwa [atPl, Polynomial.coeff_map, valued_algebraMap] at h2
  split_ifs with hw
  · exact (hv w hw).1 i
  obtain ⟨hm, hd, -, hr⟩ := hP
  have hrec := GlobalTheory.T.monic_coeff_natDegree_sub_eq_mul_cmConj E n P hm hd hr
  obtain ⟨u, ⟨hu, huw⟩, -⟩ := hS w
  rcases GlobLev.eq_or_eq_conjSrc huw with rfl | rfl
  · exact absurd hu hw
  set u := conjSrc (GlobalTheory.SplitPts.conjE E) w
  by_cases hi : i ≤ n
  swap
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Valuation.map_zero]
    exact zero_le'
  have hci : P.coeff i = P.coeff 0 * GlobalTheory.SplitPts.conjE E (P.coeff (n - i)) := by
    have := hrec (n - i) (Nat.sub_le n i)
    rwa [Nat.sub_sub_self hi] at this
  have hc0 : P.coeff 0 * GlobalTheory.SplitPts.conjE E (P.coeff 0) = 1 := by
    have := hrec 0 (Nat.zero_le n)
    rw [Nat.sub_zero, ← hd, ← Polynomial.leadingCoeff, hm.leadingCoeff] at this
    exact this.symm
  have hv0 : w.valuation E (P.coeff 0) * u.valuation E (P.coeff 0) = 1 := by
    rw [← valuation_conjE, ← Valuation.map_mul, hc0, Valuation.map_one]
  have hw0 : w.valuation E (P.coeff 0) ≤ γ u := by
    rw [eq_inv_of_mul_eq_one_left hv0]
    have hu0 : u.valuation E (P.coeff 0) ≠ 0 := right_ne_zero_of_mul_eq_one hv0
    exact (inv_le_comm₀ (zero_lt_iff.2 hu0) (zero_lt_iff.2 (hγ0 u))).2 (hv u hu).2
  rw [hci, Valuation.map_mul, valuation_conjE, sq]
  exact mul_le_mul' hw0 ((hv u hu).1 _)

theorem finite_ell_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S →
    ∀ γ : Pl E → WithZero (Multiplicative ℤ), (∀ w, γ w ≠ 0) → (∀ᶠ w in cofinite, γ w = 1) →
    {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, (∀ i, Valued.v ((atPl w P).coeff i) ≤ γ w) ∧
      (γ w)⁻¹ ≤ Valued.v ((atPl w P).coeff 0)}.Finite := by
  intro E _ _ _ n S hS γ hγ0 hγ1
  set σ := GlobalTheory.SplitPts.conjE E
  set β : Pl E → WithZero (Multiplicative ℤ) := fun w => if w ∈ S then γ w else γ (conjSrc σ w) ^ 2 with hβ
  have hβ1 : ∀ᶠ w in cofinite, β w ≤ 1 := by
    have h2 : ∀ᶠ w in cofinite, γ (conjSrc σ w) = 1 := (conjSrc_injective σ).tendsto_cofinite.eventually hγ1
    filter_upwards [hγ1, h2] with w h1 h2
    simp only [hβ]
    split_ifs
    · exact h1.le
    · rw [h2, one_pow]
  obtain ⟨D, hD0, hD⟩ := GlobalTheory.T.exists_common_denominator_of_valuation_le_cofinite E β hβ1
  have hD0' : (D : E) ≠ 0 := by exact_mod_cast hD0
  set r : ℕ → ℝ := fun i => (∑ τ : E →+* ℂ, ‖τ (D : E)‖) * n.choose i with hr
  set X : Fin (n + 1) → Set E := fun i => {x | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ r i} with hXd
  have hX : ∀ i, (X i).Finite := fun i => Embeddings.finite_of_norm_le E ℂ (r i)
  refine Set.Finite.of_finite_image (f := fun (P : E[X]) (i : Fin (n + 1)) => (D : E) * P.coeff i)
    ((Set.Finite.pi hX).subset ?_) ?_
  · rintro _ ⟨P, ⟨hP, hPS⟩, rfl⟩ i -
    refine ⟨hD _ fun w => valuation_coeff_le hS hγ0 hP hPS w i, fun φ => ?_⟩
    rw [map_mul, norm_mul]
    exact mul_le_mul (Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ (D : E)‖) (fun τ _ => norm_nonneg _)
      (Finset.mem_univ φ)) (norm_coeff_le hP φ i) (norm_nonneg _)
      (Finset.sum_nonneg fun τ _ => norm_nonneg _)
  · intro P hP Q hQ hPQ
    ext k
    by_cases hk : k ≤ n
    · exact mul_left_cancel₀ hD0' (congrFun hPQ ⟨k, Nat.lt_succ_of_le hk⟩)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hP.1.2.1]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hQ.1.2.1]; omega)]

end GlobalTheory.BCT.GeoFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMSplitPlaceMulConjPlaceEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMSplitPlaceMulConjPlaceEqOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SplitChar

theorem locK_mul_locK_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ w u : Pl E, u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → ∀ k : Eˣ, μ.locK u k * μ.locK w (Units.map (MonoidHomClass.toMonoidHom (IsCMField.complexConj E)) k) = 1 := by
  intro E _ _ _ μ e h w u hne hunder k
  have hc : GlobalTheory.Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv u w := by
    have hw : w ∈ aboveF (L := E) (maximalRealSubfield E) (u.under (𝓞 (maximalRealSubfield E))) := by
      simp [aboveF, hunder]
    exact ((GlobalTheory.CuspRep.NormTriv.mem_aboveF_iff u w).1 hw).resolve_left (Ne.symm hne)
  have h1 := GlobalTheory.CuspRep.NormTriv.normFin_loc _ μ hc k
  refine (Eq.trans ?_ h1.symm).trans ?_
  · rfl
  · rw [GlobalTheory.CuspRep.NormTriv.normFin, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MonoidHom.mul_apply, MonoidHom.id_apply, map_mul, GlobalTheory.BCT.MuProps.finId_conjFin, ← GlobalTheory.PolChar.ideleConj_eq]
    rw [map_mul]
    exact GlobalTheory.BCT.MuProps.mu_mul_conj h _

end GlobalTheory.BCT.SplitChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMSplitPlaceMulConjPlaceEqOneStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryHeckeCharCM_splitPlace_mul_conjPlace_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ w u : Pl E, u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → ∀ k : Eˣ, μ.locK u k * μ.locK w (Units.map (MonoidHomClass.toMonoidHom (IsCMField.complexConj E)) k) = 1 := by
  first | exact @GlobalTheory.BCT.SplitChar.locK_mul_locK_conj | exact GlobalTheory.BCT.SplitChar.locK_mul_locK_conj | (intros; apply GlobalTheory.BCT.SplitChar.locK_mul_locK_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexEqOfMulEquivSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexEqOfMulEquivSubgroup
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory

theorem relIndex_eq_of_mulEquiv_subgroup : ∀ (G H : Type) [Group G] [Group H] (T : Subgroup G) (S : Subgroup H) (τ : T ≃* S) (A₁ A₂ : Subgroup G) (B₁ B₂ : Subgroup H), A₁ ≤ T → A₂ ≤ T → (∀ t : T, (t : G) ∈ A₁ ↔ ((τ t : S) : H) ∈ B₁) → (∀ t : T, (t : G) ∈ A₂ ↔ ((τ t : S) : H) ∈ B₂) → A₁.relIndex A₂ = (B₁ ⊓ S).relIndex (B₂ ⊓ S) := by
  intro G H _ _ T S τ A₁ A₂ B₁ B₂ h₁ h₂ e₁ e₂
  have key : ∀ (A : Subgroup G) (B : Subgroup H), (∀ t : T, (t : G) ∈ A ↔ ((τ t : S) : H) ∈ B) →
      (A.subgroupOf T).map τ.toMonoidHom = (B ⊓ S).subgroupOf S := by
    intro A B e
    ext s
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, e]
    simp
  rw [← Subgroup.relIndex_subgroupOf h₂, ← Subgroup.relIndex_subgroupOf (inf_le_right : B₂ ⊓ S ≤ S),
    ← key A₁ B₁ e₁, ← key A₂ B₂ e₂,
    Subgroup.relIndex_map_map_of_injective _ _ τ.injective]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexEqOfMulEquivSubgroupStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_eq_relIndex_inf_of_mulEquiv_subgroup : ∀ (G H : Type) [Group G] [Group H] (T : Subgroup G) (S : Subgroup H) (τ : T ≃* S) (A₁ A₂ : Subgroup G) (B₁ B₂ : Subgroup H), A₁ ≤ T → A₂ ≤ T → (∀ t : T, (t : G) ∈ A₁ ↔ ((τ t : S) : H) ∈ B₁) → (∀ t : T, (t : G) ∈ A₂ ↔ ((τ t : S) : H) ∈ B₂) → A₁.relIndex A₂ = (B₁ ⊓ S).relIndex (B₂ ⊓ S) := by
  first | exact @GlobalTheory.relIndex_eq_of_mulEquiv_subgroup | exact GlobalTheory.relIndex_eq_of_mulEquiv_subgroup | (intros; apply GlobalTheory.relIndex_eq_of_mulEquiv_subgroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixSmoothIsUnitInHolomorphicChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixSmoothIsUnitInHolomorphicChart
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ComplexOrder

namespace GlobalTheory.GoodTop

theorem gram_smooth_isUnit_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → MContDiffAt ∞ (fun v => H A (e.symm v) ()) (e y) ∧ IsUnit (H A (e.symm (e y)) ()).det := by
  intro F _ σ X m E O H hH e he y hyO hye A hA
  refine ⟨fun a b => ?_, ?_⟩
  · obtain ⟨hre, him⟩ := hH.smooth y hyO A hA () a b
    have h1 : ContDiffAt ℝ ∞ (fun v => (H A (e.symm v) () a b).re) (e y) := contDiffAt_holoChart he hye hre
    have h2 : ContDiffAt ℝ ∞ (fun v => (H A (e.symm v) () a b).im) (e y) := contDiffAt_holoChart he hye him
    have h3 : ContDiffAt ℝ ∞ (fun v => ((H A (e.symm v) () a b).re : ℂ) + ((H A (e.symm v) () a b).im : ℂ) * Complex.I)
        (e y) :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp (e y) h1).add
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp (e y) h2).mul contDiffAt_const)
    exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => (Complex.re_add_im _).symm)
  · rw [e.left_inv hye]
    exact isUnit_iff_ne_zero.mpr (hH.posDef y hyO A hA ()).det_pos.ne'

end GlobalTheory.GoodTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixSmoothIsUnitInHolomorphicChartStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → MContDiffAt ∞ (fun v => H A (e.symm v) ()) (e y) ∧ IsUnit (H A (e.symm (e y)) ()).det := by
  first | exact @GlobalTheory.GoodTop.gram_smooth_isUnit_holoChart | exact GlobalTheory.GoodTop.gram_smooth_isUnit_holoChart | (intros; apply GlobalTheory.GoodTop.gram_smooth_isUnit_holoChart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMapEqOfKerEq
noncomputable section

namespace GlobalTheory.UPel.Sm.KSCount

open Module GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

section Gen

variable {k H O : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O]

theorem ksDim_finrank [FiniteDimensional k H] (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H)
    (Fil Z : Submodule k H) : KSDim ρ φ Fil Z (finrank k ((ksSub ρ φ Fil Z).map (cls Fil))) := by
  set M := (ksSub ρ φ Fil Z).map (cls Fil) with hM
  let b := Module.finBasis k M
  have hb : ∀ i, ∃ f ∈ ksSub ρ φ Fil Z, cls Fil f = (b i : Fil →ₗ[k] H ⧸ Fil) := fun i => (b i).2
  choose f hf hfb using hb
  have key : ∀ (g : H →ₗ[k] H) (c : Fin (finrank k M) → k),
      (∀ x ∈ Fil, g x - ∑ i, c i • f i x ∈ Fil) ↔
        cls Fil g = ∑ i, c i • (b i : Fil →ₗ[k] H ⧸ Fil) := fun g c => by
    simp_rw [← hfb]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum, cls_eq_iff, LinearMap.sum_apply, LinearMap.smul_apply]
  refine ⟨f, hf, fun g hg => ?_⟩
  let m : M := ⟨cls Fil g, g, hg, rfl⟩
  have hsum : ∀ c : Fin (finrank k M) → k, (cls Fil g = ∑ i, c i • (b i : Fil →ₗ[k] H ⧸ Fil)) ↔
      m = ∑ i, c i • b i := fun c => by
    rw [Subtype.ext_iff]; simp [m]
  refine ⟨b.equivFun m, (key g _).2 ((hsum _).2 ?_), fun c hc => ?_⟩
  · rw [← b.equivFun_symm_apply, LinearEquiv.symm_apply_apply]
  · have := (hsum c).1 ((key g c).1 hc)
    rw [this, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

theorem finrank_map_add_ker {M N : Type*} [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [AddCommGroup N] [Module k N] (p : Submodule k M) (f : M →ₗ[k] N) :
    finrank k (p.map f) + finrank k (LinearMap.ker (f ∘ₗ p.subtype)) = finrank k p := by
  rw [← LinearMap.finrank_range_add_finrank_ker (f ∘ₗ p.subtype), LinearMap.range_comp,
    Submodule.range_subtype]

end Gen

end GlobalTheory.UPel.Sm.KSCount
end
end
