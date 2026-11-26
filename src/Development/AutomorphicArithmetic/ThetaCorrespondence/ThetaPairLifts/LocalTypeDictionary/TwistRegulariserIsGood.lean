module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawFramesWeilEquivalence
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedWeilRepresentationConvergence
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsSmoothAutomorphic

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsCombinationMemRegularSubspace
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConjLinearFunctionalSphericalVectorIndicator
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LinearFunctionalSphericalVectorNeZero
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.VacLinW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
theorem linearFunctional_sphericalVector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∃ ι, M.IsLinW B.ψ t b c ι ∧ ι (M.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1 := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair v t b c hb hc
  obtain ⟨ι, hι⟩ := _root_.GlobalTheory.T.splitPlace_linearFunctional_exists hP F E σ B n d X W M χX χW om r s r' s' hPair v t b c
  have hcm : IsCMExt F E σ := hPair.base.cm
  obtain ⟨hSB, hne, θ, -, hfix⟩ := hPair.good.vac v
  have hat := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  have htt : (t.comp σ).comp σ = t := GlobalTheory.AdelicU.comp_conj_conj hcm t
  have hfix' : ∀ γ ∈ latAtV X W v, (γ.map (piW (t.comp σ)) = 0 ∨ γ.map (piW t) = 0) →
      Acts (evFin F v) (M.co.rho B.ψ γ) (M.vac v) (M.vac v) := by
    intro γ hγ h
    have h0 : symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ = 0 := by
      rcases h with h | h
      · exact symp_eq_zero_of_comp hcm t (hat γ hγ) h h _ _ _
      · rw [← htt] at h
        exact symp_eq_zero_of_comp hcm (t.comp σ) (hat γ hγ) h h _ _ _
    have := hfix γ hγ
    rwa [h0, mul_zero, AddChar.map_zero_eq_one, one_smul] at this
  set f := ι (M.vac v) with hf
  set S : Set (Matrix (Fin n) (Fin d) (Fv F v)) := {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} with hS
  have htr : ∀ A ∈ S, ∀ Y, f (Y + A) = f Y := by
    intro A hA Y
    obtain ⟨γ, hγ, h0, hco⟩ := GlobalTheory.T.exists_tensorLattice_point_of_integral_splitPlace_coordinate hcm X W v t b c hb hc A hA
    have := hι.trans γ (hat γ hγ) h0 _ hSB _ hSB (hfix' γ hγ (Or.inl h0)) Y
    rw [hco] at this
    exact this.symm
  have hsupp : ∀ Y, f Y ≠ 0 → Y ∈ S := by
    intro Y hY
    obtain ⟨x, hx, hx0, rfl⟩ := GlobalTheory.T.exists_supportedAdele_splitPlace_matrix_coordinate_eq hcm v t b c Y
    have hψ : ∀ u ∈ latAtV X W v, u.map (piW t) = 0 →
        B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u) = 1 := by
      intro u hu hu0
      have hm := hι.mult u (hat u hu) hu0 _ hSB _ hSB (hfix' u hu (Or.inr hu0)) x hx hx0
      exact (mul_eq_right₀ hY).mp hm.symm
    have hmem : x ∈ latAtV X W v := by
      refine (GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X W r s r' s' hPair.base hPair.herm hPair.skew v x hx).2
        fun γ hγ => ?_
      obtain ⟨γ₁, hγ₁, γ₂, hγ₂, rfl, h₁, h₂⟩ := GlobalTheory.T.tensorLatticeAtFinitePlace_eq_sum_splitPlace_parts hcm X W v t γ hγ
      rw [symp_add_right, symp_eq_zero_of_comp hcm t hx hx0 h₁, zero_add]
      exact hψ γ₂ hγ₂ h₂
    exact GlobalTheory.T.splitPlace_tensorLattice_component_integral X W v t b c hb hc x hmem
  have hf0 : f ≠ 0 := by
    intro h
    apply hne
    refine hι.bij.injOn hSB (zero_mem _) ?_
    rw [map_zero]; exact h
  have hfe : f = f 0 • S.indicator 1 := by
    funext Y
    by_cases hY : Y ∈ S
    · rw [Pi.smul_apply, Set.indicator_of_mem hY, Pi.one_apply, smul_eq_mul, mul_one, ← htr Y hY 0, zero_add]
    · rw [Pi.smul_apply, Set.indicator_of_notMem hY, smul_zero]
      by_contra h
      exact hY (hsupp Y h)
  have hz : f 0 ≠ 0 := by
    intro h
    apply hf0
    rw [hfe, h, zero_smul]
  refine ⟨(f 0)⁻¹ • ι, isLin_smul M B.ψ hι (inv_ne_zero hz), ?_⟩
  rw [LinearMap.smul_apply, ← hf]
  exact (congrArg ((f 0)⁻¹ • ·) hfe).trans (by rw [smul_smul, inv_mul_cancel₀ hz, one_smul])
end GlobalTheory.VacLinW
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearFunctional_sphericalVector_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∃ ι, M.IsLinW B.ψ t b c ι ∧ ι (M.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1 := by
  first | exact @_root_.GlobalTheory.VacLinW.linearFunctional_sphericalVector | exact _root_.GlobalTheory.VacLinW.linearFunctional_sphericalVector | (intros; apply _root_.GlobalTheory.VacLinW.linearFunctional_sphericalVector <;> assumption)
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Matrix
noncomputable section
namespace GlobalTheory.SplitBarVac
theorem conjLinearFunctional_sphericalVector_indicator : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∃ b₁ : GL (Fin n) (Fv F v), (PsiUnr B.ψ v → b₁ = b) ∧ ∃ ι, M.IsLinBar B.ψ t b₁ c ι ∧ ι (M.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1 := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair v t b c hb hc
  have hcm : IsCMExt F E σ := hPair.base.cm
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  have htt : (t.comp σ).comp σ = t := AlgHom.ext fun x => by simp [hσσ]
  have hJX : IsHermND σ X.Jᵀ := ⟨fun i j => by simp [Matrix.transpose_apply, hPair.herm.herm],
    by rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hPair.herm⟩
  have hL := GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B n X r s hPair.base hPair.herm v
  have hb2 := hb.dual hcm hJX hL
  obtain ⟨z, c₂, hz1, hc2v, hc2⟩ := GlobalTheory.T.skewHermitianLattice_splitPlace_components_dual F E σ B d W r' s' hPair.base hPair.skew v t c hc
  have hc3 : IsSplitBasis (t.comp σ) W.L (-c₂) := fun u => by
    have := hc2 (-u)
    simp only [Pi.neg_apply, neg_mem_iff, Matrix.mulVec_neg] at this
    simpa [Units.val_neg, Matrix.neg_mulVec, Matrix.mulVec_neg] using this
  refine ⟨Units.map (Matrix.scalar (Fin n) : Fv F v →+* Matrix (Fin n) (Fin n) (Fv F v)).toMonoidHom z * b,
    fun hu => by simp [hz1 hu], ?_⟩
  obtain ⟨ι, hι, hvac⟩ := _root_.GlobalTheory.T.linearFunctional_sphericalVector_ne_zero hP F E σ B n d X W M χX χW om r s r' s' hPair v (t.comp σ) _ _ hb2 hc3
  refine ⟨ι, ?_, hvac⟩
  unfold Model.IsLinW at hι
  rw [htt] at hι
  unfold Model.IsLinBar
  convert hι using 1
  have e1 : ((dualConj 1 (splitGram hJX t * b))⁻¹).1 = b.1ᵀ * X.J.map t := by
    rw [← map_inv, dualConj_val]
    simp [Matrix.transpose_mul, Matrix.transpose_map]
  have e2 : ((-c₂)⁻¹).1 = -((z : Fv F v) • (c.1ᵀ * W.J.map t)) := by
    first
    | (rw [← hc2v]; simp)
    | (rw [← hc2v, Units.neg_inv]; rfl)
    | (rw [← hc2v]; exact congrArg Units.val (neg_inv c₂))
  ext Y i j
  rw [e1, e2]
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Matrix.transpose_mul, Matrix.scalar_apply,
    Matrix.transpose_neg, Matrix.transpose_smul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.diagonal_transpose, Matrix.mul_assoc, neg_neg]
  simp [Matrix.mul_assoc, ← Matrix.smul_eq_diagonal_mul, Matrix.mul_smul, Matrix.smul_mul]
end GlobalTheory.SplitBarVac
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_sphericalVector_indicator_value : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∃ b₁ : GL (Fin n) (Fv F v), (PsiUnr B.ψ v → b₁ = b) ∧ ∃ ι, M.IsLinBar B.ψ t b₁ c ι ∧ ι (M.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1 := by
  first | exact @_root_.GlobalTheory.SplitBarVac.conjLinearFunctional_sphericalVector_indicator | exact _root_.GlobalTheory.SplitBarVac.conjLinearFunctional_sphericalVector_indicator | (intros; apply _root_.GlobalTheory.SplitBarVac.conjLinearFunctional_sphericalVector_indicator <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.RegSo
theorem regular_subspace_vacuum_at : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v),
    ∃ (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ))
      (P : GL (Fin a') (Fv F v)) (Λ : Submodule 𝒪[Fv F v] (Fin (a + a') → Fv F v)) (c : ℂ),
      G.M'.IsLinBar B.ψ t 1 1 ι ∧
      ∀ Y, ι (G.M'.vac v) Y = c * (GlobalTheory.SplitFlip.matLat (Fin a') Λ : Set _).indicator 1 (P.val * Y) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v t
  haveI := hT.geo.hV'.lat
  haveI := hT.geo.hW.lat
  obtain ⟨b', hb'⟩ := exists_isSplitBasis t G.V'.L hT.base.cm
  obtain ⟨c, hc⟩ := exists_isSplitBasis t G.W.L hT.base.cm
  obtain ⟨b₁, -, ι', hι', hvac'⟩ :=
    _root_.GlobalTheory.T.splitPlace_sphericalVector_indicator_value hP F E σ B _ _ _ _ _ _ _ om' _ _ _ _ (GlobalTheory.ThKConst.isPair_small hT) v t b' c hb' hc
  let Q : GL (Fin a') (Fv F v) := Matrix.GeneralLinearGroup.mkOfDetNeZero b₁.valᵀ (by
    rw [Matrix.det_transpose]; exact b₁.isUnit.map Matrix.detMonoidHom |>.ne_zero)
  let Λ : Submodule 𝒪[Fv F v] (Fin (a + a') → Fv F v) :=
    { carrier := {x | ∀ j, (x ᵥ* c.val) j ∈ 𝒪[Fv F v]}
      add_mem' := fun {x y} hx hy j => by rw [Matrix.add_vecMul]; exact add_mem (hx j) (hy j)
      zero_mem' := fun j => by rw [Matrix.zero_vecMul]; exact zero_mem _
      smul_mem' := fun s x hx j => by
        rw [show s • x = (s : Fv F v) • x from rfl, Matrix.smul_vecMul]
        exact mul_mem s.2 (hx j) }
  refine ⟨_, Q, Λ, 1, isLinBar_one G.M' B.ψ t b₁ Q rfl c ι' hι', fun Y => ?_⟩
  simp only [LinearMap.comp_apply, LinearMap.funLeft_apply]
  rw [hvac', one_mul]
  have key : mulHomeo Q c Y ∈ {Y : Matrix (Fin a') (Fin (a + a')) (Fv F v) | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} ↔
      Q.val * Y ∈ (GlobalTheory.SplitFlip.matLat (Fin a') Λ : Set (Matrix (Fin a') (Fin (a + a')) (Fv F v))) := by
    rw [mulHomeo_apply]
    show (∀ i j, (Q.val * Y * c.val) i j ∈ v.adicCompletionIntegers F) ↔ ∀ i j, ((Q.val * Y).row i ᵥ* c.val) j ∈ 𝒪[Fv F v]
    simp only [GlobalTheory.FinPl.SplitPoint.mem_integer_iff]
    rfl
  by_cases h : Q.val * Y ∈ (GlobalTheory.SplitFlip.matLat (Fin a') Λ : Set (Matrix (Fin a') (Fin (a + a')) (Fv F v)))
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (key.2 h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (key.1 h'))]
theorem exists_combination_mem_regular_subspace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁))
      (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
      (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
      (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
      (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (n : ℕ) (Ψ : Fin n → WO W₁ X → ℂ), (∀ i, Ψ i ∈ algF ψ θ false A₁ B) →
    ∃ P : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ P, Xc.Good v → ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F v,
      ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁ ∧ k ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v)) ∧
        GlobalTheory.FunObj.zdeg z ≠ 0 ∧ ∀ i, ∃ Φ₀D, IsDatum Γ.M' ψ cB Φ₀D ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) ∧
          Φ₀D ∈ Γ.M'.So Bs.ψ t := by
  intro hP D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hTD n Ψ hΨ
  classical
  choose ΦD hΦD hD using fun i => hO.algB (Ψ i) (hΨ i)
  choose m f φ hsum hSB hvac using fun i => decAlg Γ.M' Bs.ψ Bs.emb (ΦD i) (hΦD i)
  have hfin : Set.Finite (⋃ i, ⋃ k, {v | ¬ φ i k v = Γ.M'.vac v}) :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun k => Filter.eventually_cofinite.1 (hvac i k)
  refine ⟨hfin.toFinset, fun v hv hg t => ?_⟩
  have h0 : ∀ i k, φ i k v = Γ.M'.vac v := fun i k => by
    by_contra h
    exact hv (hfin.mem_toFinset.2 (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨k, h⟩⟩))
  have hTD' := isTriple_goodPlace hTD v t hg
  obtain ⟨K, hK⟩ := homAt W₁ Γ hO.JW₁ hTD.base.cm hTD.geo.hV'.herm v t
  let K' : GL (Fin W₁.rank) (Fv D.host.F v) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V'.J :=
    { toFun := fun g => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ (K g)
      map_one' := by simp only [map_one]; exact GlobalTheory.LocWeilAct.conjU_one' _ _ _
      map_mul' := fun g g' => by simp only [map_mul]; exact GlobalTheory.LocWeilAct.conjU_mul' _ _ _ _ _ }
  obtain ⟨ν', α', hν', hact⟩ := actAt { Bs with v₁ := v, τ₁ := t } Γ Xc om om' hTD' K' (fun g => (hK g).2.2)
  obtain ⟨ι, Pm, Λ, c, hι, hvι⟩ := _root_.GlobalTheory.RegSo.regular_subspace_vacuum_at hP _ _ D.sp.cm.sig { Bs with v₁ := v, τ₁ := t } _ _ Γ Xc om om' hTD' v t
  obtain ⟨z, hzs, hzd, hz⟩ := combAt { Bs with v₁ := v, τ₁ := t } Γ hTD.geo.hM' hTD.geo.lt om'
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁) K ν' α' hν' ι hι (hact ι hι) (Γ.M'.vac v) Pm Λ c hvι
  refine ⟨z, fun k hk => ?_, hzd, fun i => ⟨(z.sum fun k c => c • om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ k, 1) (ΦD i)),
    datumComb D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hTD (ΦD i) (Ψ i) (hD i) z, ?_⟩⟩
  · obtain ⟨g, rfl⟩ := hzs k hk
    exact ⟨(hK g).1, (hK g).2.1⟩
  · rw [hsum i]
    exact hz (f i) (φ i) (hSB i) (hvac i) (h0 i)
end GlobalTheory.RegSo
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_form_mem_regular_subspace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁))
      (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
      (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
      (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
      (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (n : ℕ) (Ψ : Fin n → WO W₁ X → ℂ), (∀ i, Ψ i ∈ algF ψ θ false A₁ B) →
    ∃ P : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ P, Xc.Good v → ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F v,
      ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁ ∧ k ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v)) ∧
        GlobalTheory.FunObj.zdeg z ≠ 0 ∧ ∀ i, ∃ Φ₀D, IsDatum Γ.M' ψ cB Φ₀D ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) ∧
          Φ₀D ∈ Γ.M'.So Bs.ψ t := by
  first | exact @_root_.GlobalTheory.RegSo.exists_combination_mem_regular_subspace | exact _root_.GlobalTheory.RegSo.exists_combination_mem_regular_subspace | (intros; apply _root_.GlobalTheory.RegSo.exists_combination_mem_regular_subspace <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.RegGood
theorem regulariser_isGood : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (W W₁ X : HSp D) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β → ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωB : WRep W₁ X, IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (n : ℕ) (Ψ : Fin n → WO W₁ X → ℂ) (u : Fin n → GA D W₁), (∀ i, Ψ i ∈ algF ψ θ false A₁ B) → (∀ i, u i ∈ GfC W₁) →
    ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁) ∧ GlobalTheory.FunObj.zdeg z ≠ 0 ∧
      ∀ i, ModInt θ ωB ν₁ 𝓕₁ ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) ∧
        ∃ u' ∈ GfC W₁, (z.sum fun k c => c • ωB (k, 1)) (ωB (u i, 1) (Ψ i)) =
          ωB (u', 1) ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) := by
  intro hP hK D ψ θ hθ W W₁ X A₁ B α β hT ν₁ 𝓕₁ hν₁ ωB hωB n Ψ u hΨ hu
  have hstd : IsStdChar D ψ (-1) := hωB.std
  obtain ⟨ωA, -, hωA, -⟩ := _root_.GlobalTheory.T.weilRepresentation_square_comm hP D ψ hstd W W₁ X α β hT
  obtain ⟨A⟩ := GlobalTheory.ChainFr.Model.nonempty_fr W
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D W
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hωA hωB
  obtain ⟨Pa, hPa⟩ := _root_.GlobalTheory.T.twisted_form_mem_regular_subspace hP D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hTD n Ψ hΨ
  obtain ⟨Pb, hPb⟩ := GlobalTheory.T.weilRep_commute_at_good_places_algebraic_vectors D ψ θ hθ W₁ X A₁ B α β ωB hωB n Ψ u hΨ hu
  classical
  obtain ⟨v, hv, hsp, ⟨t⟩⟩ := GlobalTheory.T.exists_place_splitsCompletely_not_mem_embedding D.host.F D.host.E (Pa ∪ Pb ∪ Xc.T)
  have hvg : Xc.Good v := ⟨fun h => hv (Finset.mem_union_right _ h), hsp⟩
  obtain ⟨z, hzs, hzd, hzi⟩ :=
    hPa v (fun h => hv (Finset.mem_union_left _ (Finset.mem_union_left _ h))) hvg t
  refine ⟨z, fun k hk => (hzs k hk).1, hzd, fun i => ⟨?_,
    hPb v (fun h => hv (Finset.mem_union_left _ (Finset.mem_union_right _ h))) z (fun k hk => (hzs k hk).2) i⟩⟩
  obtain ⟨Φ₀D, hD, hSo⟩ := hzi i
  have hTD' := isTriple_atPlace hTD v t hvg
  obtain ⟨hDec, -⟩ := hK.1 D.host.F D.host.E D.sp.cm.sig _ W.rank W₁.rank Γ Xc om om' hTD'
  obtain ⟨hbd, hconv, -⟩ := hDec.2 Φ₀D hSo
  exact GlobalTheory.T.theta_integral_moderate_growth_of_bounded_kernel D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e { Bs with v₁ := v, τ₁ := t } Γ Xc om om' cA cB hθ { hO with } hν₁
    hTD' _ Φ₀D hD hconv (by
      obtain ⟨C, k, hC⟩ := hbd 0
      exact ⟨C, k, fun g h => by simpa using hC g h⟩)
end GlobalTheory.RegGood
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_regulariser_isGood : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (W W₁ X : HSp D) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β → ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωB : WRep W₁ X, IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (n : ℕ) (Ψ : Fin n → WO W₁ X → ℂ) (u : Fin n → GA D W₁), (∀ i, Ψ i ∈ algF ψ θ false A₁ B) → (∀ i, u i ∈ GfC W₁) →
    ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁) ∧ GlobalTheory.FunObj.zdeg z ≠ 0 ∧
      ∀ i, ModInt θ ωB ν₁ 𝓕₁ ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) ∧
        ∃ u' ∈ GfC W₁, (z.sum fun k c => c • ωB (k, 1)) (ωB (u i, 1) (Ψ i)) =
          ωB (u', 1) ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) := by
  first | exact @_root_.GlobalTheory.RegGood.regulariser_isGood | exact _root_.GlobalTheory.RegGood.regulariser_isGood | (intros; apply _root_.GlobalTheory.RegGood.regulariser_isGood <;> assumption)
end
