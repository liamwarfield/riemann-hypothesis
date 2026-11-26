module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemPolarizationStabilizerOfDualPair
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspAverageKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeFormOfDoubling
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.GlobalFormAtFrameLatNc

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationPairDerivation
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.OscillatorDerivAlongLineQuadratic
section
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
namespace GlobalTheory.OscQuad
theorem oscillator_deriv_along_line_quadratic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ Lines σ W, ∃ (m : ℕ) (u v : Fin m → Matrix (Fin n) (Fin d) (AE F E)) (c : Fin m → ℂ) (c₀ : ℂ),
      (∀ i, At (evI F) (u i) ∧ At (evI F) (v i)) ∧
      ∀ (f : SInf F (Fin n × Fin d)) (g₁ g₂ : Fin m → SInf F (Fin n × Fin d)),
        (∀ i, ActsD (evI F) (M.heisLine ψ (v i)) f (g₁ i)) → (∀ i, ActsD (evI F) (M.heisLine ψ (u i)) (g₁ i) (g₂ i)) →
        ∀ F₁ : ℝ → SInf F (Fin n × Fin d), (∀ t, Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (F₁ t)) →
        ∀ y, HasDerivAt (fun t => F₁ t y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  classical
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW γ hγ
  obtain ⟨T, hT, hadd, h0⟩ := _root_.GlobalTheory.T.archimedean_theta_family_exists_smooth hP M ψ χX χW om hCM hψ hW γ hγ
  obtain ⟨A, hAc, hA⟩ := GlobalTheory.T.archimedeanLine_intertwines_realSchrodinger M ψ χX χW om hψ hW γ hγ T hT
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  let μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Measure.addHaar
  have hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := fun t f =>
    GlobalTheory.T.weil_representation_integral_action M ψ χX χW om hW μ inferInstance (γ (Multiplicative.ofAdd t)) f (T t f) (hT t f)
  obtain ⟨hc1, hc2⟩ := GlobalTheory.T.archimedeanOneParameterFamily_continuous M ψ χX χW om hW γ hγ T hT
  have trace_real {ι : Type} [Fintype ι] (f : ι → ℝ) :
      Algebra.trace ℝ (ι → ℝ) f = ∑ i, f i := by
    rw [Algebra.trace_eq_matrix_trace (Pi.basisFun ℝ ι)]
    simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul, Pi.single_apply]
  have trace_complex {ι : Type} [Fintype ι] (f : ι → ℂ) :
      Algebra.trace ℝ (ι → ℂ) f = ∑ i, 2 * (f i).re := by
    rw [Algebra.trace_eq_matrix_trace (Pi.basis fun _ : ι => Complex.basisOneI)]
    simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul, Fintype.sum_sigma, Pi.single_apply, Fin.sum_univ_two,
      Complex.coe_basisOneI, Complex.coe_basisOneI_repr]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have trace_nondeg (x : mixedEmbedding.mixedSpace F)
      (h : ∀ b, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * b) = 0) : x = 0 := by
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · have h1 := h (Pi.single w 1, 0)
      rw [Algebra.trace_prod_apply, trace_real, trace_complex] at h1
      simpa [Pi.single_apply] using h1
    · have h1 := h (0, Pi.single w (star (x.2 w)))
      rw [Algebra.trace_prod_apply, trace_real, trace_complex] at h1
      have h2 : (x.2 w).re * (x.2 w).re + (x.2 w).im * (x.2 w).im = 0 := by
        simpa [Pi.single_apply, apply_ite Complex.re, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Complex.star_def,
          Complex.mul_conj] using h1
      have hre : (x.2 w).re = 0 := by nlinarith [mul_self_nonneg (x.2 w).re, mul_self_nonneg (x.2 w).im]
      have him : (x.2 w).im = 0 := by nlinarith [mul_self_nonneg (x.2 w).re, mul_self_nonneg (x.2 w).im]
      exact Complex.ext hre him
  have hpair : IsPairing (trP F (Fin n × Fin d)) := by
    exact {
      addL x x' y := by simp only [trP, Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)]
      addR x y y' := by simp only [trP, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]
      smulL c x y := by simp only [trP, Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul]
      smulR c x y := by simp only [trP, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul]
      nondegL x hx := by
        funext i
        apply trace_nondeg
        intro b
        have h := hx (Pi.single i b)
        simpa [trP, Pi.single_apply, mul_ite, Finset.sum_ite_eq'] using h
      nondegR y hy := by
        funext i
        apply trace_nondeg
        intro b
        have h := hy (Pi.single i b)
        simpa [trP, Pi.single_apply, ite_mul, Finset.sum_ite_eq', mul_comm] using h
    }
  obtain ⟨m, a, b, c, c₀, hR⟩ := GlobalTheory.T.realMetaplectic_family_derivative_quadratic hP.realMetaplecticRepresentation
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) μ inferInstance _
    hpair A T hAc hadd h0 hA hiso hc1 (hc2 μ inferInstance)
  choose u hu hDu using fun i => GlobalTheory.T.exists_heisenbergLine_derivative_formula M ψ hψ (a i)
  choose v hv hDv using fun i => GlobalTheory.T.exists_heisenbergLine_derivative_formula M ψ hψ (b i)
  obtain ⟨r₀, hr₀, hinj⟩ := GlobalTheory.T.exists_admissible_finiteFactor_archimedeanSchwartz (F := F) (Fin n × Fin d)
  refine ⟨m, u, v, c, c₀, fun i => ⟨hu i, hv i⟩, ?_⟩
  intro f g₁ g₂ h1 h2 F₁ hF y
  have eF : ∀ t, F₁ t = T t f := fun t => hinj _ _ ((hF t r₀ (hr₀ f)).symm.trans (hT t f r₀ (hr₀ f)))
  simp only [eF]
  exact hR f g₁ g₂ (fun i y => hDv i f (g₁ i) (h1 i) y) (fun i y => hDu i (g₁ i) (g₂ i) (h2 i) y) y
end GlobalTheory.OscQuad
end
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oscillator_lie_action_quadratic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ Lines σ W, ∃ (m : ℕ) (u v : Fin m → Matrix (Fin n) (Fin d) (AE F E)) (c : Fin m → ℂ) (c₀ : ℂ),
      (∀ i, At (evI F) (u i) ∧ At (evI F) (v i)) ∧
      ∀ (f : SInf F (Fin n × Fin d)) (g₁ g₂ : Fin m → SInf F (Fin n × Fin d)),
        (∀ i, ActsD (evI F) (M.heisLine ψ (v i)) f (g₁ i)) → (∀ i, ActsD (evI F) (M.heisLine ψ (u i)) (g₁ i) (g₂ i)) →
        ∀ F₁ : ℝ → SInf F (Fin n × Fin d), (∀ t, Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (F₁ t)) →
        ∀ y, HasDerivAt (fun t => F₁ t y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  first | exact @_root_.GlobalTheory.OscQuad.oscillator_deriv_along_line_quadratic | exact _root_.GlobalTheory.OscQuad.oscillator_deriv_along_line_quadratic | (intros; apply _root_.GlobalTheory.OscQuad.oscillator_deriv_along_line_quadratic <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.DerPol
theorem polarization_pair_derivation (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (F := F) E w) (χX χW : Chr F E) (om : Rep σ X W) (hcm : IsCMExt F E σ) (hψ : IsStd ψ)
    (hW : M.IsWeil ψ χX χW om) :
    ∀ γ ∈ Lines σ W, ∃ δ : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f ∈ M.Pol ψ τ,
      δ f ∈ M.Pol ψ τ ∧ ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  intro γ hγ
  obtain ⟨m, u, v, c, c₀, hat, hQ⟩ := _root_.GlobalTheory.T.oscillator_lie_action_quadratic hP M ψ χX χW om hcm hψ hW γ hγ
  choose Du hDu using fun i => GlobalTheory.T.exists_archSchwartz_derivative_heisenbergLine M ψ hψ (u i) (hat i).1
  choose Dv hDv using fun i => GlobalTheory.T.exists_archSchwartz_derivative_heisenbergLine M ψ hψ (v i) (hat i).2
  have closed : ∀ w, At (evI F) w → ∀ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ f : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ w) f (D f)) → ∀ f ∈ M.Pol ψ τ, D f ∈ M.Pol ψ τ := by
    intro w hw D hD f hf
    rw [Model.Pol, Submodule.mem_sInf] at hf ⊢
    intro N hN
    exact hN.2 w hw f (hf N hN) (D f) (hD f)
  refine ⟨∑ i, c i • (Du i ∘ₗ Dv i) + c₀ • LinearMap.id, fun f hf => ⟨?_, ?_⟩⟩
  · simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.id_apply]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ hf)
    exact closed _ (hat i).1 _ (hDu i) _ (closed _ (hat i).2 _ (hDv i) _ hf)
  · intro r hr x
    choose F₁ hF₁ using fun t : ℝ => _root_.GlobalTheory.T.theta_action_archimedean_locality hP M ψ χX χW om hcm hψ hW (γ (Multiplicative.ofAdd t)) (hγ.2 _) f
    have hd := hQ f (fun i => Dv i f) (fun i => Du i (Dv i f)) (fun i => hDv i f) (fun i => hDu i _) F₁ hF₁
      (fun i => evI F (x i))
    have e : (fun t => om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) f r) x) =
        fun t => F₁ t (fun i => evI F (x i)) * r x := by
      funext t; rw [hF₁ t r hr]; rfl
    rw [e]
    refine (hd.mul_const (r x)).congr_deriv ?_
    show _ = ((∑ i, c i • (Du i ∘ₗ Dv i) + c₀ • LinearMap.id : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) f) (fun i => evI F (x i)) * r x
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply,
      SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul]
    congr 2
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, SchwartzMap.add_apply, ih]; simp
theorem exists_lie_derivative_model : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W,
    ∃ δ : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')), ∀ f ∈ G.M'.Pol B.ψ B.emb,
      δ f ∈ G.M'.Pol B.ψ B.emb ∧ ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  intro hP F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ
  exact _root_.GlobalTheory.DerPol.polarization_pair_derivation hP G.M' B.ψ B.emb X.α (X.α / X.β) om' hT.base.cm hT.base.std hT.weil' γ hγ
end GlobalTheory.DerPol
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_lie_derivative_model : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W,
    ∃ δ : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')), ∀ f ∈ G.M'.Pol B.ψ B.emb,
      δ f ∈ G.M'.Pol B.ψ B.emb ∧ ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  first | exact @_root_.GlobalTheory.DerPol.exists_lie_derivative_model | exact _root_.GlobalTheory.DerPol.exists_lie_derivative_model | (intros; apply _root_.GlobalTheory.DerPol.exists_lie_derivative_model <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspFormApproxWeighted
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
noncomputable section
open scoped ENNReal
theorem GlobalTheory.CuspApproxAll.cusp_form_approx_weighted : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (A : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → Formalism.IndefR.Links.SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧ ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ A ≤ ε := by
  intro D θ hθ hP N φ hφ A ε hε
  obtain ⟨hA, hc, -⟩ := id hφ
  obtain ⟨U, hU, hlev⟩ := hA.level
  obtain ⟨d, C, hC⟩ := hP.cuspDecaySobolev D θ hθ N.V U hU 0 A
  have hφg : GlobalTheory.CuspApproxAll.Good θ N.V φ := ⟨GlobalTheory.Size.rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ hA hc, hc⟩
  have hη : 0 < ε / ((C : ℝ) + 1) := div_pos hε (by positivity)
  obtain ⟨e, he, hgrow⟩ := GlobalTheory.T.exists_KFinite_iteratedCompactAverage_approx D θ hθ N φ hφg.1 (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _) d _ hη
  obtain ⟨n, F, v, hF, hFlev, hsum⟩ := _root_.GlobalTheory.T.twist_cusp_average_k_finite_decomposition D θ hθ hP N φ hφ U hU hlev e he
    (Finset.univ : Finset D.what₂.Tau).toList (fun τ => Finset.mem_toList.2 (Finset.mem_univ τ))
  rw [hsum] at hgrow
  refine ⟨n, F, v, hF, fun g => ?_⟩
  set ψ : GA D N.V → ℂ := φ - ∑ j, F j (v j) with hψ
  have hsg : GlobalTheory.CuspApproxAll.Good θ N.V (∑ j, F j (v j)) :=
    Finset.sum_induction _ (GlobalTheory.CuspApproxAll.Good θ N.V) (fun _ _ => GlobalTheory.CuspApproxAll.good_add)
      (GlobalTheory.CuspApproxAll.good_zero θ N.V) fun j _ => GlobalTheory.CuspApproxAll.good_value hP.cuspRapidDecay hθ N (hF j) (v j)
  have hg : GlobalTheory.CuspApproxAll.Good θ N.V ψ := by
    have := GlobalTheory.CuspApproxAll.good_add hφg (GlobalTheory.CuspApproxAll.good_smul (-1) hsg)
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hψlev : ∀ k ∈ U, k ∈ GfC N.V → ∀ x, ψ (x * k) = ψ x := fun k hk hk' x => by
    simp only [hψ, Pi.sub_apply, Finset.sum_apply, hlev k hk hk' x, hFlev _ k hk hk' x]
  have h1 := hC ψ hg.1.toIsAutFun hψlev hg.1.smooth (GlobalTheory.CuspApproxAll.growthSob_zero_ne_top hg.1) hg.2
  have h2 : decaySize N.V A ψ ≤ ENNReal.ofReal ε := by
    have h4 : (C : ℝ≥0∞) * growthSob θ N.V d 0 ψ ≤ C * ENNReal.ofReal (ε / ((C : ℝ) + 1)) := by gcongr
    refine h1.trans (h4.trans ?_)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [NNReal.coe_nonneg C]
  have h3 : ENNReal.ofReal (‖ψ g‖ * quotHeight N.V g ^ A) ≤ ENNReal.ofReal ε := (le_iSup (fun x => ENNReal.ofReal (‖ψ x‖ * quotHeight N.V x ^ A)) g).trans h2
  rw [ENNReal.ofReal_le_ofReal_iff hε.le] at h3
  simpa [hψ, Finset.sum_apply] using h3
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_cusp_form_approx_weighted : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (A : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → Formalism.IndefR.Links.SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧ ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ A ≤ ε := by
  first | exact @_root_.GlobalTheory.CuspApproxAll.cusp_form_approx_weighted | exact _root_.GlobalTheory.CuspApproxAll.cusp_form_approx_weighted | (intros; apply _root_.GlobalTheory.CuspApproxAll.cusp_form_approx_weighted <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HeckeFormOfDoubling
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GlobalFormOfSiegelWeil
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GlobalFormFrameLattice
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalFormAt_frameLat_of_siegelWeil : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → ∀ D : D7, SiegelWeilFock D → ∀ A : HSp D, GlobalFormAt A (frameLat A) := by
  first | exact @_root_.GlobalTheory.Core.Rk.IP.globalFormAt_frameLat_nc | exact _root_.GlobalTheory.Core.Rk.IP.globalFormAt_frameLat_nc | (intros; apply _root_.GlobalTheory.Core.Rk.IP.globalFormAt_frameLat_nc <;> assumption)
end
end

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
namespace GlobalTheory.Core.Rk.IP
theorem globalForm_of_siegelWeil' : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals →
    ∀ D : D7, GlobalForm D := by
  intro hW hC hWS hSW hDM D A L hL
  have hsw := GlobalTheory.T.siegelWeil_fockDoubledPair_of_weil_and_ichino hW hWS hSW D
  have h0 := _root_.GlobalTheory.T.globalFormAt_frameLat_of_siegelWeil hW hC hDM D hsw A
  exact GlobalTheory.T.global_doubling_zeta_form_selfDual_lattice_transfer D A (frameLat A) L (frameLat_isSelfDualC A) hL h0
end GlobalTheory.Core.Rk.IP
end

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalForm_of_siegel_weil : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → ∀ D : D7, GlobalForm D := by
  first | exact @_root_.GlobalTheory.Core.Rk.IP.globalForm_of_siegelWeil' | exact _root_.GlobalTheory.Core.Rk.IP.globalForm_of_siegelWeil' | (intros; apply _root_.GlobalTheory.Core.Rk.IP.globalForm_of_siegelWeil' <;> assumption)
end
end

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
namespace GlobalTheory.Core.Rk.IP
theorem heckeForm_of_doubling' : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals →
    GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, HeckeForm D := by
  intro p1 p2 p3 p4 p5 p6 D
  have hU := GlobalTheory.T.unramifiedDoublingIntegral_inert_place
  have hG : GlobalForm D := _root_.GlobalTheory.T.globalForm_of_siegel_weil p1 p2 p3 p4 p5 D
  have hPB := paramBoundOn_all_of_split_inert D (GlobalTheory.T.sphericalParameterBound_split_place D) (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU D)
  have hLZ := localZetaOn_all_of_split_inert D (GlobalTheory.T.unramifiedDoublingIntegral_splitPlace_adelic p6 D) (GlobalTheory.T.unramified_doubling_integral_inert_adelic hU D (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU D))
  have hE : EulerRight D := GlobalTheory.T.doubling_eulerProduct_farRight p2 D (GlobalTheory.T.doublingSphericalFactorization_of_weilDualPair p1 D) hLZ hPB
  exact GlobalTheory.T.heckeInnerProductFormula_of_doublingEuler D hG hE
end GlobalTheory.Core.Rk.IP
end

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeForm_of_doubling : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, HeckeForm D := by
  first | exact @_root_.GlobalTheory.Core.Rk.IP.heckeForm_of_doubling' | exact _root_.GlobalTheory.Core.Rk.IP.heckeForm_of_doubling' | (intros; apply _root_.GlobalTheory.Core.Rk.IP.heckeForm_of_doubling' <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsWeilRepArchimedeanSmoothOrbit
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanLineSpannedByWeilVector
section
noncomputable section
open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open scoped Classical
open MeasureTheory
namespace GlobalTheory.ArchLine
open scoped SchwartzMap
theorem archimedean_real_line_invariance : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : Chr F E) (om : Rep σ X W), IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ Lines σ W, ∃ (l : Type) (_ : Fintype l) (_ : DecidableEq l)
      (Φ : SInf F (Fin n × Fin d) ≃L[ℂ] GlobalTheory.RealWeil.Sch l) (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ)
      (T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l),
      Continuous g ∧ g 0 = 1 ∧ (∀ s t, g (s + t) = g s * g t) ∧ (∀ t, g t ∈ Matrix.symplecticGroup l ℝ) ∧
      T 0 = LinearMap.id ∧ (∀ s t, T (s + t) = T s ∘ₗ T t) ∧
      (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
        ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (g t *ᵥ w) ⇑(T t h)) ∧
      (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) ∧
      (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) ∧
      ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)),
        Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(Φ.symm (T t (Φ f))) := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW γ hγ
  have hex : ∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁ := fun h hh f => _root_.GlobalTheory.T.theta_action_archimedean_locality hP M ψ χX χW om hCM hψ hW h hh f
  obtain ⟨hadd, hsmul, hone, hmul⟩ := GlobalTheory.T.archimedean_weilOperators_linear_one_mul M ψ χX χW om hW hex
  obtain ⟨aadd, asmul, amul⟩ := GlobalTheory.T.unitary_archimedean_coordinate_action_linear_mul M
  have hγU : ∀ t : ℝ, γ (Multiplicative.ofAdd t) ∈ UAt σ W (evI F) := fun t => hγ.2 _
  have hγ0 : γ (Multiplicative.ofAdd 0) = 1 := by rw [ofAdd_zero, map_one]
  have hγadd : ∀ s t : ℝ, γ (Multiplicative.ofAdd (s + t)) = γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd t) :=
    fun s t => by rw [ofAdd_add, map_mul]
  obtain ⟨N, hN⟩ : ∃ N, Module.finrank ℝ (Fin n × Fin d → mixedEmbedding.mixedSpace F) = N := ⟨_, rfl⟩
  obtain ⟨C, φ, hφ, hC⟩ := pairingCoords (Fin n × Fin d → mixedEmbedding.mixedSpace F) (trP F (Fin n × Fin d))
    (isPairing_trP _) N hN
  let S : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun t =>
    { toFun := archOp om (γ (Multiplicative.ofAdd t))
      map_add' := hadd _ (hγU t)
      map_smul' := hsmul _ (hγU t) }
  let A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) := fun t =>
    { toFun := archAct M (γ (Multiplicative.ofAdd t))
      map_add' := aadd _
      map_smul' := asmul _ }
  let ψt : ℝ → (Fin N ⊕ Fin N → ℝ) →ₗ[ℝ] (Fin N ⊕ Fin N → ℝ) := fun t =>
    φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap
  have hψt : ∀ t w, ψt t w = φ (archAct M (γ (Multiplicative.ofAdd t)) (φ.symm w)) := fun t w => rfl
  let g : ℝ → Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ := fun t => LinearMap.toMatrix' (ψt t)
  have hg : ∀ t w, g t *ᵥ w = ψt t w := fun t w => LinearMap.toMatrix'_mulVec _ _
  let P1 : SInf F (Fin n × Fin d) →L[ℂ] GlobalTheory.RealWeil.Sch (Fin N) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let P2 : GlobalTheory.RealWeil.Sch (Fin N) →L[ℂ] SInf F (Fin n × Fin d) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  let eΦ : SInf F (Fin n × Fin d) ≃L[ℂ] GlobalTheory.RealWeil.Sch (Fin N) := ContinuousLinearEquiv.equivOfInverse P1 P2
    (fun f => by ext x; simp [P1, P2]) (fun h => by ext x; simp [P1, P2])
  have hΦ : ∀ f x, eΦ f x = f (C.symm x) := fun f x => rfl
  have hΦs : ∀ h x, eΦ.symm h x = h (C x) := fun h x => rfl
  let T : ℝ → GlobalTheory.RealWeil.Sch (Fin N) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin N) := fun t =>
    eΦ.toLinearMap ∘ₗ S t ∘ₗ eΦ.symm.toLinearMap
  have hT : ∀ t h x, T t h x = archOp om (γ (Multiplicative.ofAdd t)) (eΦ.symm h) (C.symm x) := fun t h x => rfl
  refine ⟨Fin N, inferInstance, inferInstance, eΦ, g, T, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [g, LinearMap.toMatrix'_apply]
    exact (continuous_apply i).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      (GlobalTheory.T.continuous_oneParameter_unitary_coordinate_action M γ hγ _))
  · have e : ψt 0 = LinearMap.id := LinearMap.ext fun w => by rw [hψt, hγ0, archAct_one]; simp
    simp only [g, e, LinearMap.toMatrix'_id]
  · intro s t
    have e : ψt (s + t) = ψt s ∘ₗ ψt t := LinearMap.ext fun w => by
      rw [hψt, LinearMap.comp_apply, hψt, hψt, hγadd, amul, LinearEquiv.symm_apply_apply]
    simp only [g, e, LinearMap.toMatrix'_comp]
  · intro t
    have hsym : ∀ w w', GlobalTheory.RealWeil.sympl (ψt t w) (ψt t w') = GlobalTheory.RealWeil.sympl w w' := fun w w' => by
      rw [hψt, hψt, hφ, GlobalTheory.T.unitary_archimedean_coordinate_action_symplectic, ← hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    obtain ⟨Mx, hMx⟩ := symplMatrix (Fin N) (ψt t) hsym
    have e : g t = Mx := Matrix.toLin'.injective (LinearMap.ext fun w => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hg, hMx])
    rw [e]; exact Mx.2
  · refine LinearMap.ext fun h => ?_
    ext x
    rw [hT, hγ0, hone, hΦs]
    simp
  · intro s t
    refine LinearMap.ext fun h => ?_
    ext x
    show archOp om (γ (Multiplicative.ofAdd (s + t))) (eΦ.symm h) (C.symm x) =
      archOp om (γ (Multiplicative.ofAdd s)) (eΦ.symm (T t h)) (C.symm x)
    rw [hγadd, hmul _ (hγU s) _ (hγU t)]
    congr 2
    exact (eΦ.symm_apply_apply (S t (eΦ.symm h))).symm
  · intro t w h h₁ hh₁
    have hf : ⇑(eΦ.symm h₁) = schrF (trP F (Fin n × Fin d)) (φ.symm w) ⇑(eΦ.symm h) := by
      have e1 : ⇑(eΦ.symm h) = ⇑h ∘ ⇑C := funext (hΦs h)
      rw [e1, hC, LinearEquiv.apply_symm_apply]
      funext y; rw [hΦs, hh₁]; rfl
    have key := GlobalTheory.T.archimedean_weilOperator_intertwines_schroedinger M ψ χX χW om hψ hW hex _ (hγU t) (φ.symm w) _ _ hf
    have e2 : ⇑(archOp om (γ (Multiplicative.ofAdd t)) (eΦ.symm h)) = ⇑(T t h) ∘ ⇑C := by
      funext y; rw [Function.comp_apply, hT, ContinuousLinearEquiv.symm_apply_apply]
    funext x
    rw [hT, key, e2, hC, hg, hψt]
    simp
  · intro t h
    have e := GlobalTheory.T.archWeilOperator_unitaryW_lintegral_norm_eq M ψ χX χW om hW hex _ (hγU t) N C (eΦ.symm h)
    refine Eq.trans ?_ (e.trans ?_)
    · rfl
    · simp only [hΦs, ContinuousLinearEquiv.apply_symm_apply]
  · intro h x
    exact GlobalTheory.T.continuous_oneParameter_archimedean_weilOperator M ψ χX χW om hW hex γ hγ (eΦ.symm h) (C.symm x)
  · intro t f
    have e : eΦ.symm (T t (eΦ f)) = archOp om (γ (Multiplicative.ofAdd t)) f := by
      ext y; rw [hΦs, hT]; simp
    rw [e]
    exact acts_archOp om _ f (hex _ (hγU t) f)
end GlobalTheory.ArchLine
end
end

section
open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_line_spanned_by_weil_vector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : Chr F E) (om : Rep σ X W), IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ Lines σ W, ∃ (l : Type) (_ : Fintype l) (_ : DecidableEq l)
      (Φ : SInf F (Fin n × Fin d) ≃L[ℂ] GlobalTheory.RealWeil.Sch l) (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ)
      (T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l),
      Continuous g ∧ g 0 = 1 ∧ (∀ s t, g (s + t) = g s * g t) ∧ (∀ t, g t ∈ Matrix.symplecticGroup l ℝ) ∧
      T 0 = LinearMap.id ∧ (∀ s t, T (s + t) = T s ∘ₗ T t) ∧
      (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
        ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (g t *ᵥ w) ⇑(T t h)) ∧
      (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) ∧
      (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) ∧
      ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)),
        Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(Φ.symm (T t (Φ f))) := by
  first | exact @_root_.GlobalTheory.ArchLine.archimedean_real_line_invariance | exact _root_.GlobalTheory.ArchLine.archimedean_real_line_invariance | (intros; apply _root_.GlobalTheory.ArchLine.archimedean_real_line_invariance <;> assumption)
end
end

section
open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
theorem GlobalTheory.WeilArchSmooth.exists_weilRep_archimedean_smooth_orbit : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ Lines σ W, ∀ f : SInf F (Fin n × Fin d), ∃ (c : ℝ → SInf F (Fin n × Fin d)) (c' : SInf F (Fin n × Fin d)),
      c 0 = f ∧ Filter.Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (nhdsWithin 0 {0}ᶜ) (nhds c') ∧
      ∀ t : ℝ, Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) (⇑f) (⇑(c t)) := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hcm hψ hw γ hγ f
  obtain ⟨l, _, _, Φ, g, T, hgc, hg0, hgm, hgs, hT0, hTm, hTi, hTu, hTc, hTa⟩ :=
    _root_.GlobalTheory.T.archimedean_line_spanned_by_weil_vector hP M ψ χX χW om hcm hψ hw γ hγ
  obtain ⟨Z, hZ, hgZ⟩ := GlobalTheory.T.exists_symplecticLie_eq_exp_oneParam l g hgc hg0 hgm hgs
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.T.metaplectic_lift_scalar_derivative_eq hP l Z hZ T hT0 hTm
    (fun t w h h₁ e => by rw [← hgZ t]; exact hTi t w h h₁ e) hTu hTc
  refine ⟨fun t => Φ.symm (T t (Φ f)), Φ.symm (a • Φ f + GlobalTheory.RealWeil.quad Z (Φ f)), ?_, ?_, fun t => hTa t f⟩
  · simp [hT0]
  · have h := (Φ.symm.continuous.tendsto _).comp (ha (Φ f))
    refine h.congr fun t => ?_
    simp only [Function.comp_apply, ← Complex.coe_smul, map_smul, map_sub, ContinuousLinearEquiv.symm_apply_apply]
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TendstoSlopeOfArchimedeanPairing
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory Filter Topology
open scoped SchwartzMap Classical Matrix
noncomputable section
namespace GlobalTheory.ArchLinePair
theorem tendsto_slope_of_archimedean_pairing (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (P : V → V → ℝ) (hp : IsPairing P)
    (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ))
    (hAc : ∀ v, Continuous fun t => A t v) (hA0 : ∀ v, A 0 v = v) (hAm : ∀ s t v, A (s + t) v = A s (A t v))
    (hAo : ∀ t v v', omega P (A t v) (A t v') = omega P v v')
    (hT0 : ∀ f, T 0 f = f) (hTm : ∀ s t f, T (s + t) f = T s (T t f))
    (hTi : ∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f))
    (hTu : ∀ μ : Measure V, μ.IsAddHaarMeasure → ∀ t f, ∫⁻ x, ‖T t f x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ)
    (hTc : ∀ f y, Continuous fun t => T t f y) (f : 𝓢(V, ℂ)) :
    ∃ g : 𝓢(V, ℂ), Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[≠] 0) (𝓝 g) := by
  set n := Module.finrank ℝ V with hn
  obtain ⟨C, φ, hφ, hC⟩ := exists_pairing_coords V P hp n rfl
  let a : ℝ → (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) := fun t => φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap
  have ha : ∀ t v, a t (φ v) = φ (A t v) := fun t v => by simp [a]
  let g : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := fun t => LinearMap.toMatrix' (a t)
  have hg : ∀ t w, g t *ᵥ w = a t w := fun t w => LinearMap.toMatrix'_mulVec _ _
  have hext : ∀ M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, (∀ v, M *ᵥ φ v = N *ᵥ φ v) → M = N := by
    intro M N h
    refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
    obtain ⟨v, rfl⟩ := φ.surjective w
    simpa using h v
  have hgc : Continuous g := by
    refine continuous_matrix fun i j => ?_
    have h1 : Continuous fun t => φ (A t (φ.symm (Pi.single j 1))) :=
      φ.toLinearMap.continuous_of_finiteDimensional.comp (hAc _)
    have h2 := (continuous_apply i).comp h1
    refine h2.congr fun t => ?_
    simp only [g, a, Function.comp_apply, LinearMap.toMatrix'_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hg0 : g 0 = 1 := hext _ _ fun v => by rw [hg, ha, hA0, Matrix.one_mulVec]
  have hgm : ∀ s t, g (s + t) = g s * g t := fun s t => hext _ _ fun v => by
    rw [← Matrix.mulVec_mulVec, hg, hg, hg, ha, ha, ha, hAm]
  have hgs : ∀ t, g t ∈ Matrix.symplecticGroup (Fin n) ℝ := fun t => by
    obtain ⟨M, hM⟩ := GlobalTheory.exists_symplecticGroup_of_sympl (Fin n) (a t) fun w w' => by
      obtain ⟨v, rfl⟩ := φ.surjective w
      obtain ⟨v', rfl⟩ := φ.surjective w'
      rw [ha, ha, hφ, hφ, hAo]
    rw [hext (g t) M fun v => by rw [hg, hM]]
    exact M.2
  obtain ⟨Z, hZ, hgZ⟩ := GlobalTheory.T.exists_symplecticLie_eq_exp_oneParam (Fin n) g hgc hg0 hgm hgs
  let B : GlobalTheory.RealWeil.Sch (Fin n) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  let Bi : 𝓢(V, ℂ) →L[ℂ] GlobalTheory.RealWeil.Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  have hB : ∀ h, ⇑(B h) = ⇑h ∘ ⇑C := fun h => rfl
  have hBi : ∀ h, ⇑(Bi h) = ⇑h ∘ ⇑C.symm := fun h => rfl
  have hBBi : ∀ h, B (Bi h) = h := fun h => by ext x; simp [hB, hBi]
  have hBiB : ∀ h, Bi (B h) = h := fun h => by ext x; simp [hB, hBi]
  let S : ℝ → GlobalTheory.RealWeil.Sch (Fin n) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin n) := fun t =>
    Bi.toLinearMap ∘ₗ T t ∘ₗ B.toLinearMap
  have hS : ∀ t h, S t h = Bi (T t (B h)) := fun t h => rfl
  have hint : ∀ h : 𝓢(V, ℂ), ∫⁻ x, ‖Bi h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2 ∂(Measure.map C.symm volume) := fun h =>
    (lintegral_map_equiv (fun x => ‖h x‖ₑ ^ 2) C.symm.toHomeomorph.toMeasurableEquiv).symm
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.T.metaplectic_lift_scalar_derivative_eq hP (Fin n) Z hZ S (LinearMap.ext fun h => by rw [hS, hT0, hBiB]; rfl)
    (fun s t => LinearMap.ext fun h => by
      show S (s + t) h = S s (S t h)
      rw [hS, hS, hS, hBBi, hTm])
    (fun t w h h₁ e => by
      obtain ⟨v, rfl⟩ := φ.surjective w
      have h1 : ⇑(B h₁) = schrF P v ⇑(B h) := by rw [hB, hB, hC, e]
      have h2 := hTi t v _ _ h1
      rw [← hgZ t, hg, ha, hS, hS, hBi, h2, ← hBBi (T t (B h)), hB, hC, hBiB]
      funext x; simp)
    (fun t h => by
      rw [hS, hint, hTu _ (C.symm.isAddHaarMeasure_map volume), ← hint, hBiB])
    (fun h x => hTc (B h) (C.symm x))
  refine ⟨_, ((B.continuous.tendsto _).comp (hc (Bi f))).congr fun t => ?_⟩
  simp only [Function.comp_apply, ← Complex.coe_smul, map_smul, map_sub, hS, hBBi]
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
theorem exists_orbit_pair_archimedean_line (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E)
    (om : Rep σ X W) (hψ : IsStd ψ) (hW : M.IsWeil ψ χX χW om) (δ : ℝ → UA σ X.J × UA σ W.J) (hδc : Continuous δ)
    (hδ0 : δ 0 = 1) (hδm : ∀ s t, δ (s + t) = δ s * δ t) (hδ1 : ∀ t, (δ t).1 ∈ UAt σ X (evI F))
    (hδ2 : ∀ t, (δ t).2 ∈ UAt σ W (evI F)) (f : SInf F (Fin n × Fin d)) :
    ∃ (c : ℝ → SInf F (Fin n × Fin d)) (g : SInf F (Fin n × Fin d)), c 0 = f ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 g) ∧ ∀ t, Acts (evI F) (om (δ t)) ⇑f ⇑(c t) := by
  have hs := IsUWeilPair.isUSplitting hW
  have hex : ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (δ t)) ⇑f ⇑f₁ := by
    intro t f
    refine acts_of_comm ψ hψ (om (δ t)) (fun Φ hΦ => hs.pres _ Φ hΦ) (fun u hu p q Φ hΦ => ?_) f
    have he : M.co.e (u • M.co.e.symm (p, q)) = (u • p, u • q) := by
      rw [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, Prod.smul_mk]
    have h2 := hs.impl (δ t) (u • M.co.e.symm (p, q)) Φ hΦ
    simp only [Darboux.rho, he, actAB_fin (hδ1 t) (hδ2 t) u hu] at h2
    exact h2
  choose S hS using hex
  let g₀ := GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d)
  have hg₀ : g₀ ∈ SB _ := GlobalTheory.ArchLocality.intInd_mem _
  have hg₀0 : g₀ 0 = 1 := by
    simp only [g₀, GlobalTheory.ArchLocality.intInd]
    rw [Set.indicator_of_mem (show (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
      fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from
        fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
    rfl
  let r₀ : (Fin n × Fin d → AF F) → ℂ := fun x => g₀ fun i => (x i).2
  have hrr : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    refine congrArg g₀ (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.ArchLocality.snd_eq_zero_of_at hz i, add_zero]
  have hR : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) ⇑f r₀ := fun f =>
    ⟨hrr, Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩⟩
  have hr0 : r₀ 0 ≠ 0 := by
    show g₀ 0 ≠ 0
    rw [hg₀0]; exact one_ne_zero
  have hinj : ∀ f₁ f₂ : SInf F (Fin n × Fin d), tens (evI F) ⇑f₁ r₀ = tens (evI F) ⇑f₂ r₀ → f₁ = f₂ :=
    fun f₁ f₂ h => DFunLike.coe_injective (GlobalTheory.ArchFam.tens_inj r₀ hrr 0 hr0 _ _ h)
  have key : ∀ t (f : SInf F (Fin n × Fin d)), om (δ t) (tens (evI F) ⇑f r₀) = tens (evI F) ⇑(S t f) r₀ :=
    fun t f => hS t f r₀ (hR f)
  have tadd : ∀ f g : SInf F (Fin n × Fin d),
      tens (evI F) ⇑(f + g) r₀ = tens (evI F) ⇑f r₀ + tens (evI F) ⇑g r₀ := by
    intro f g; funext x; simp [tens, add_mul]
  have tsmul : ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)), tens (evI F) ⇑(c • f) r₀ = c • tens (evI F) ⇑f r₀ := by
    intro c f; funext x; simp [tens, mul_assoc]
  let T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun t =>
    { toFun := S t
      map_add' := fun f g => hinj _ _ (by rw [← key, tadd, map_add (f := _), key, key, tadd])
      map_smul' := fun c f => hinj _ _ (by rw [← key, tsmul, map_smul, key, RingHom.id_apply, tsmul]) }
  have hT : ∀ t f, T t f = S t f := fun t f => rfl
  have hT0 : ∀ f, T 0 f = f := fun f => hinj _ _ (by rw [hT, ← key, hδ0, map_one, Module.End.one_apply])
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := inferInstance
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.ArchLinePair.tendsto_slope_of_archimedean_pairing hP (trP F (Fin n × Fin d)) (Coord.isPairing_trP _)
    (fun t => amap M (δ t)) T (fun v => (continuous_amap M v).comp hδc)
    (fun v => by
      obtain ⟨w, rfl⟩ : ∃ w, Coord.coordI M w = v := ⟨_, Coord.coordI_lift M v⟩
      rw [amap_coordI, hδ0, actAB_one])
    (fun s t v => by
      obtain ⟨w, rfl⟩ : ∃ w, Coord.coordI M w = v := ⟨_, Coord.coordI_lift M v⟩
      rw [amap_coordI, amap_coordI, amap_coordI, hδm, actAB_mul])
    (fun t v v' => by
      obtain ⟨w, rfl⟩ : ∃ w, Coord.coordI M w = v := ⟨_, Coord.coordI_lift M v⟩
      obtain ⟨w', rfl⟩ : ∃ w, Coord.coordI M w = v' := ⟨_, Coord.coordI_lift M v'⟩
      rw [amap_coordI, amap_coordI, Coord.omega_coordI, Coord.omega_coordI]
      simp only [Coord.sympM, symp, hTens_actAB])
    hT0
    (fun s t f => hinj _ _ (by rw [hT, hT, hT, ← key, hδm, map_mul, Module.End.mul_apply, key, key]))
    (fun t v f f₁ hf => by
      have hc : (locV (M.co.e (GlobalTheory.ArchFam.wv M v)).1, locV (M.co.e (GlobalTheory.ArchFam.wv M v)).2) = v :=
        Coord.coordI_lift M v
      have e1 : tens (evI F) ⇑f₁ r₀ = M.co.rho ψ (GlobalTheory.ArchFam.wv M v) (tens (evI F) ⇑f r₀) := by
        rw [GlobalTheory.ArchFam.rho_tens ψ hψ M.co _ (GlobalTheory.ArchFam.at_wv M v) _ _ hrr, hc, ← hf]
      have e2 := hs.impl (δ t) (GlobalTheory.ArchFam.wv M v) _ (hR f).2
      have hat : At (evI F) (actAB (cA σ) (δ t) (GlobalTheory.ArchFam.wv M v)) := fun u hu => by
        rw [← actAB_smul, GlobalTheory.ArchFam.at_wv M v u hu, actAB, Matrix.mul_zero, Matrix.zero_mul]
      apply GlobalTheory.ArchFam.tens_inj r₀ hrr 0 hr0
      rw [hT, hT, ← key, e1, e2, key, GlobalTheory.ArchFam.rho_tens ψ hψ M.co _ hat _ _ hrr]
      rfl)
    (fun μ hμ t f => by
      obtain ⟨μA, hμA, c, hc0, hct, hc⟩ := GlobalTheory.ArchimedeanUnitaryL2.exists_haar F _ μ g₀ hg₀ hr0
      have hU := hs.unit μA hμA (δ t) (tens (evI F) f r₀) (hR f).2
      rw [key] at hU
      exact (ENNReal.mul_right_inj hc0 hct).1 (((hc (S t f)).symm.trans hU).trans (hc f)))
    (fun f y => by
      let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) (liftV y)
      have hpure : ∀ (f' : SInf F (Fin n × Fin d)) g', l (pureA F (⇑f') g') = g' 0 * f' y := fun f' g' => by
        show f' (locV (liftV y)) * g' 0 = _
        rw [Coord.loc_lift, mul_comm]
      have hl : l ∈ (adeleClass F).adm (Fin n × Fin d) := fun g' _ =>
        ⟨g' 0 • ((BoundedContinuousFunction.evalCLM ℂ y).comp
          (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f' => hpure f' g'⟩
      refine ((hs.cont l hl _ (hR f).2).comp hδc).congr fun t => ?_
      rw [Function.comp_apply, key]
      exact (hpure (S t f) g₀).trans (by rw [hg₀0, one_mul, hT]))
    f
  exact ⟨fun t => T t f, g, hT0 f, hg, fun t => hS t f⟩
theorem exists_curve_along_archimedean_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r →
    ∃ (c : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      (∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (c t) r) ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - c 0)) (𝓝[≠] 0) (𝓝 g) := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ _ hW γ hγ f r hr
  obtain ⟨c, g, hc0, hg, hc⟩ := _root_.GlobalTheory.ArchLinePair.exists_orbit_pair_archimedean_line hP M ψ χX χW om hψ hW (fun t => (γ (Multiplicative.ofAdd t), 1))
    ((hγ.1.comp continuous_ofAdd).prodMk continuous_const) (by rw [ofAdd_zero, map_one]; rfl)
    (fun s t => by rw [ofAdd_add, map_mul, Prod.mk_mul_mk, one_mul]) (fun t => hγ.2 _)
    (fun t u _ => by simp [mat]) f
  exact ⟨c, g, fun t => hc t r hr, by rw [hc0]; exact hg⟩
end GlobalTheory.ArchLinePair
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
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_line_pairing_twist : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r →
    ∃ (c : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      (∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (c t) r) ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - c 0)) (𝓝[≠] 0) (𝓝 g) := by
  first | exact @_root_.GlobalTheory.ArchLinePair.exists_curve_along_archimedean_line | exact _root_.GlobalTheory.ArchLinePair.exists_curve_along_archimedean_line | (intros; apply _root_.GlobalTheory.ArchLinePair.exists_curve_along_archimedean_line <;> assumption)
end
end
