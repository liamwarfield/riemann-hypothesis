module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantUnitConstantsGoodEmbedding

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertModelExtremalValuesEqHolomorphicCuspForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorEvalMultiplicitySpaceOntoHolomorph
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorEvalMultiplicitySpaceOntoHolomorph
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem HolForm.congr_level {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
    {w : D.what₂.Tau → Fin V.rank → ℤ} {J : Set (GA D V)} {χ χ' φ : GA D V → ℂ} (h : HolForm θ M w J χ φ)
    (e : ∀ k ∈ J, χ k = χ' k) : HolForm θ M w J χ' φ :=
  ⟨h.aut, h.bdd, fun k hk g => by rw [← e k hk]; exact h.lev k hk g, h.hol⟩

theorem mult_eval_eq_adel_holSub0 : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → WtIs M w → ∀ v : M.Vec, IsExtVec M v → ∀ χ : GA D V → ℂ, (∀ k ∈ Kf, χ k = 1) → (∀ P ∈ Formalism.L2.Pj.holSub0 X la, ∃ T ∈ Mult θ M (Kf : Set (GA D V)) χ, T v = adel V dict (muPin V dict mu c) P) ∧ ∀ T ∈ Mult θ M (Kf : Set (GA D V)) χ, ∃ P ∈ Formalism.L2.Pj.holSub0 X la, adel V dict (muPin V dict mu c) P = T v := by
  intro hdec hvol D θ V S M w r hr Comp X la dict mu c Kf hS hG hw v hv χ hχ
  refine ⟨fun P hP => ?_, fun T hT => ?_⟩
  · have hP1 : P ∈ Submodule.span ℂ {P | IsHolCusp X la P} := hP.1
    clear hP
    induction hP1 using Submodule.span_induction with
    | mem P hP =>
      have h1 := GlobalTheory.T.holomorphicAdelicForm_of_boundedSection D θ V S M w r hr Comp X la dict mu c Kf hS hG P (fun k => (hP k).1)
      have h2 := GlobalTheory.T.adelicCuspForm_transvection_constantTerms_zero D θ V S M w r hr Comp X la dict mu c Kf hS hG P hP
      obtain ⟨T, hT, hTv⟩ := GlobalTheory.T.boundedHolomorphicForm_eq_multiplicitySpace_value D θ V S M w v hG.inf hS hw hv (exists_finPair hvol D V)
        (Kf : Set (GA D V)) χ _ hG.levFin (h1.congr_level fun k hk => (hχ k hk).symm) h2
      exact ⟨T, Submodule.subset_span hT, hTv⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add P Q _ _ hP hQ =>
      obtain ⟨T, hT, hTv⟩ := hP
      obtain ⟨T', hT', hTv'⟩ := hQ
      exact ⟨T + T', Submodule.add_mem _ hT hT', by rw [map_add (f := _), _root_.add_apply, hTv, hTv']⟩
    | smul a P _ hP =>
      obtain ⟨T, hT, hTv⟩ := hP
      exact ⟨a • T, Submodule.smul_mem _ a hT, by rw [map_smul, _root_.smul_apply, hTv]⟩
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.holomorphic_cusp_form_of_extremal_vector_multiplicity hdec D θ V S M w v hG.inf hS hw hv (Kf : Set (GA D V)) χ T hT
    obtain ⟨P, hP0, hPb, hPe⟩ := GlobalTheory.T.exists_boundedSection_of_boundedHolomorphicForm D θ V S M w r hr Comp X la dict mu c Kf hS hG (T v)
      (h1.congr_level hχ)
    have hc := GlobalTheory.T.isHolomorphicCuspForm_of_adelic_constantTerms_zero D θ V S M w r hr Comp X la dict mu c Kf hS hG P hPb (hPe ▸ h2)
    exact ⟨P, ⟨holCusp_mem_holSub X la hc, hP0⟩, hPe⟩

end GlobalTheory.HolDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorEvalMultiplicitySpaceOntoHolomorphStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extremalVector_eval_multiplicitySpace_onto_holomorphic : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → WtIs M w → ∀ v : M.Vec, IsExtVec M v → ∀ χ : GA D V → ℂ, (∀ k ∈ Kf, χ k = 1) → (∀ P ∈ Formalism.L2.Pj.holSub0 X la, ∃ T ∈ Mult θ M (Kf : Set (GA D V)) χ, T v = adel V dict (muPin V dict mu c) P) ∧ ∀ T ∈ Mult θ M (Kf : Set (GA D V)) χ, ∃ P ∈ Formalism.L2.Pj.holSub0 X la, adel V dict (muPin V dict mu c) P = T v := by
  first | exact @GlobalTheory.HolDict.mult_eval_eq_adel_holSub0 | exact GlobalTheory.HolDict.mult_eval_eq_adel_holSub0 | (intros; apply GlobalTheory.HolDict.mult_eval_eq_adel_holSub0 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertModelExtremalValuesEqHolomorphicCuspForms
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem range_evAt_eq_adel_image : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, Set.range (evAt R i σ (v₀ i σ)) = adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ))) (T.cE ((i : ℕ) + 1) (res T σ))) '' (Formalism.L2.Pj.holSub0 (T.U ((i : ℕ) + 1) (res T σ)).X (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) : Set _) := by
  intro hc hf D G _ _ Pl0 T0 A T _ R κ v₀ hL hM hT hp i σ hσ hV
  obtain ⟨hs, -, w, hw⟩ := GlobalTheory.T.holomorphicShape_integralWeight_goodEmbedding D G Pl0 T0 A T R κ v₀ hT i σ hσ
  have hg := GlobalTheory.T.coreDictionary_good_at_good_embedding D G Pl0 T0 A T R κ v₀ hL hM hT hp i σ hσ hV w hw
  have hχ := (GlobalTheory.T.realisation_principalLevel_eq_coreLevel_open D G Pl0 T0 A T R κ v₀ hL hM hT hp i σ hσ hV).2.1
  obtain ⟨h1, h2⟩ := GlobalTheory.T.extremalVector_eval_multiplicitySpace_onto_holomorphic hc hf D R.θ _ _ (R.MW i σ) w _ _ _ _ _ _ _ _ _ hs hg hw (v₀ i σ)
    (hT.hv₀ i σ).1 _ hχ
  have hW := hM.HW i σ
  have hr : LinearMap.range (R.HW i σ).e = R.Wall i σ := hW.2.1
  ext f
  constructor
  · rintro ⟨h, rfl⟩
    have hm : (R.HW i σ).e h ∈ R.Wall i σ := hr ▸ LinearMap.mem_range_self _ h
    obtain ⟨P, hP, e⟩ := h2 _ hm
    exact ⟨P, hP, e⟩
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨S, hS, e⟩ := h1 P hP
    have hm : S ∈ LinearMap.range (R.HW i σ).e := by rw [hr]; exact hS
    obtain ⟨h, rfl⟩ := hm
    exact ⟨h, e⟩

end GlobalTheory.HolDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertModelExtremalValuesEqHolomorphicCuspFormsStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertModel_extremalValues_eq_holomorphicCuspForms : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, Set.range (evAt R i σ (v₀ i σ)) = adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ))) (T.cE ((i : ℕ) + 1) (res T σ))) '' (Formalism.L2.Pj.holSub0 (T.U ((i : ℕ) + 1) (res T σ)).X (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) : Set _) := by
  first | exact @GlobalTheory.HolDict.range_evAt_eq_adel_image | exact GlobalTheory.HolDict.range_evAt_eq_adel_image | (intros; apply GlobalTheory.HolDict.range_evAt_eq_adel_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormReadingsIndependentSpanningAllEmbeddings
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsEqModelValuesSemilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsEqModelValuesSemilinear
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspFormValues

theorem evEx_of_range {K C H X : Type} [Field K] [AddCommGroup C] [Module K C] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup X] [Module ℂ X] (σ : K →+* ℂ) (ev : H → X) (φ : C → X) (hinj : Function.Injective ev)
    (hadd : ∀ x y, ev (x + y) = ev x + ev y) (hsmul : ∀ (a : ℂ) x, ev (a • x) = a • ev x)
    (hφa : ∀ f g, φ (f + g) = φ f + φ g) (hφs : ∀ (a : K) f, φ (a • f) = σ a • φ f)
    (hmem : ∀ f, φ f ∈ Set.range ev) : EvEx σ ev φ := by
  choose j hj using hmem
  exact ⟨{ toFun := j
           map_add' := fun f g => hinj (by rw [hadd, hj, hj, hj, hφa])
           map_smul' := fun a f => hinj (by rw [hsmul, hj, hj, hφs]) }, hj⟩

theorem phiC_eq {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC T hV a f = adel W (castDict hV (T.dict j σ)) (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ))
      ((lieFac (T.Q.Dw j) (xiR D) a : ℂ) • rdU (T.U j σ) f) := by
  subst hV
  rw [map_smul]
  rfl

theorem jEvExists : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → JEvExists T R κ v₀ := by
  intro hdec hvol D G _ _ Pl0 T0 A T _ R κ v₀ hlev hmod htie hpb i σ hσ hV
  have hr := GlobalTheory.T.hilbertModel_extremalValues_eq_holomorphicCuspForms hdec hvol D G Pl0 T0 A T R κ v₀ hlev hmod htie hpb i σ hσ hV
  refine evEx_of_range _ _ _ (GlobalTheory.EvalAtUnitVector.evInj T R v₀ hmod.HW htie.hv₀ i σ hσ) (fun x y => ?_) (fun a x => ?_)
    (fun f g => ?_) (fun a f => ?_) (fun f => ?_)
  · unfold evAt
    rw [map_add (f := _)]
    rfl
  · unfold evAt
    rw [map_smul]
    rfl
  · simp only [phiC_eq]
    rw [Submodule.coe_add, map_add (f := _), smul_add, map_add (f := _)]
  · simp only [phiC_eq]
    rw [Submodule.coe_smul, map_smulₛₗ (rdU _), smul_comm, map_smul]
  · rw [hr, phiC_eq]
    exact ⟨_, Submodule.smul_mem _ _
      (Submodule.mem_inf.2 ⟨((mem_cusp _ _ _ _ _ _).1 f.2).2 _ hσ, rdU_mem_offZero _ _⟩), rfl⟩

end GlobalTheory.CuspFormValues
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsEqModelValuesSemilinearStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormAdelicFunctions_eq_modelValues_semilinear : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → JEvExists T R κ v₀ := by
  first | exact @GlobalTheory.CuspFormValues.jEvExists | exact GlobalTheory.CuspFormValues.jEvExists | (intros; apply GlobalTheory.CuspFormValues.jEvExists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationGoodEmbeddingIndependentReadings
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsEqSpanReadings
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsEqSpanReadings
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Onto


set_option maxHeartbeats 1000000 in
theorem holSub0_eq_span_readings : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → KapIs κ → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c σ → Formalism.L2.Pj.holSub0 (T.U ((i : ℕ) + 1) σ).X (laU (T.U ((i : ℕ) + 1) σ) (wtA (κ i)) (κ i).n) = Submodule.span ℂ (Set.range fun f : Cu T κ i => rdU (T.U ((i : ℕ) + 1) σ) (f : T.R ((i : ℕ) + 1))) := by
  intro D T κ h hκ hl hn i σ hσ
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega)
  have hni : (κ i).n = D.R.nV := (hκ i τ).2.2
  apply le_antisymm
  · refine (GlobalTheory.T.holomorphicCuspSections_le_span_algebraicCuspForms D T h _ (inR i) (κ i) (hl i) (hni ▸ hn) σ hσ).trans (Submodule.span_mono ?_)
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    exact Submodule.mem_inf.2 ⟨((Formalism.L2.Pj.mem_cusp _ _ _ _ _ _).1 f.2).2 σ hσ, Formalism.L2.Pj.rdU_mem_offZero _ _⟩

end GlobalTheory.Onto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsEqSpanReadingsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicCuspSections_eq_span_readings : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → KapIs κ → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c σ → Formalism.L2.Pj.holSub0 (T.U ((i : ℕ) + 1) σ).X (laU (T.U ((i : ℕ) + 1) σ) (wtA (κ i)) (κ i).n) = Submodule.span ℂ (Set.range fun f : Cu T κ i => rdU (T.U ((i : ℕ) + 1) σ) (f : T.R ((i : ℕ) + 1))) := by
  first | exact @GlobalTheory.Onto.holSub0_eq_span_readings | exact GlobalTheory.Onto.holSub0_eq_span_readings | (intros; apply GlobalTheory.Onto.holSub0_eq_span_readings <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationGoodEmbeddingIndependentReadings
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnifGood

theorem span_top_of_range {H X S C : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] [AddCommGroup S]
    [Module ℂ S] (ev : H →ₗ[ℂ] X) (hev : Function.Injective ev) (ad : S →ₗ[ℂ] X) (rd : C → S) (j : C → H) (c : ℂ) (hc : c ≠ 0)
    (hj : ∀ f, ev (j f) = c • ad (rd f))
    (hr : Set.range ev = ad '' (Submodule.span ℂ (Set.range rd) : Set S)) :
    Submodule.span ℂ (Set.range j) = ⊤ := by
  refine top_le_iff.1 fun h _ => ?_
  obtain ⟨F, hF, hFh⟩ : ev h ∈ ad '' (Submodule.span ℂ (Set.range rd) : Set S) := hr ▸ ⟨h, rfl⟩
  have key : Submodule.span ℂ (Set.range rd) ≤ ((Submodule.span ℂ (Set.range j)).map ev).comap ad := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    refine ⟨c⁻¹ • j f, Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩), ?_⟩
    rw [map_smul, hj, smul_smul, inv_mul_cancel₀ hc, one_smul]
  obtain ⟨y, hy, hy'⟩ := key hF
  rwa [← hev (hy'.trans hFh)]

theorem phiC_eq {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC T hV a f = ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) •
      adel W (castDict hV (T.dict j σ)) (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ))
        (rdU (T.U j σ) f) := by
  subst hV
  rfl

noncomputable def evLin {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) where
  toFun := evAt R i σ v
  map_add' x y := by
    unfold evAt
    rw [map_add (f := _)]
    rfl
  map_smul' a x := by
    unfold evAt
    rw [map_smul]
    rfl

theorem unif_good : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ i σ, GoodEmb T.Q.c (res T σ) → (∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k)) ∧ Submodule.span ℂ (Set.range (jTop T R κ v₀ i σ)) = ⊤ := by
  intro h1 h2 D G _ _ Pl0 T0 A T _ R κ v₀ hL hM hT hpb hlast hn i σ hσ
  have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := hT.laws.spaceW _ (inR i) _ hσ
  have hj := GlobalTheory.T.cuspFormAdelicFunctions_eq_modelValues_semilinear h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hpb i σ hσ hV
  have hev : ∀ f, evLin R i σ (v₀ i σ) (jTop T R κ v₀ i σ f) = phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) :=
    jTop_good T R κ v₀ hσ hV hj
  refine ⟨fun m b hb => ?_, ?_⟩
  · refine LinearIndependent.of_comp (evLin R i σ (v₀ i σ)) ?_
    have h := GlobalTheory.T.cuspFormAdelicFunctions_independent_goodEmbedding D T κ hT.laws i _ hσ hV m b hb
    exact (funext fun k => hev (b k) : (evLin R i σ (v₀ i σ) ∘ fun k => jTop T R κ v₀ i σ (b k)) = _) ▸ h
  · have hr := GlobalTheory.T.hilbertModel_extremalValues_eq_holomorphicCuspForms h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hpb i σ hσ hV
    rw [GlobalTheory.T.holomorphicCuspSections_eq_span_readings D T κ hT.laws hT.kap hlast hn i _ hσ] at hr
    exact span_top_of_range (evLin R i σ (v₀ i σ)) (GlobalTheory.EvalAtUnitVector.evInj T R v₀ hM.HW hT.hv₀ i σ hσ) _ _ _ _
      (Complex.ofReal_ne_zero.2 (lieFac_pos _ _ _).ne') (fun f => (hev f).trans (phiC_eq T hV _ _)) hr

end GlobalTheory.UnifGood
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationGoodEmbeddingIndependentReadingsStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_goodEmbedding_independent_readings : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ i σ, GoodEmb T.Q.c (res T σ) → (∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k)) ∧ Submodule.span ℂ (Set.range (jTop T R κ v₀ i σ)) = ⊤ := by
  first | exact @GlobalTheory.UnifGood.unif_good | exact GlobalTheory.UnifGood.unif_good | (intros; apply GlobalTheory.UnifGood.unif_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormReadingsIndependentSpanningAllEmbeddings
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnifAll

theorem span_range_le {F U H : Type} [Field F] [AddCommGroup U] [Module F U] [AddCommGroup H] [Module ℂ H] {σ : F →+* ℂ}
    (j : U →ₛₗ[σ] H) {n : ℕ} (b : Module.Basis (Fin n) F U) :
    Submodule.span ℂ (Set.range j) ≤ Submodule.span ℂ (Set.range fun k => j (b k)) := by
  rw [Submodule.span_le]
  rintro _ ⟨u, rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← b.sum_repr u, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem span_top {F U H H' : Type} [Field F] [AddCommGroup U] [Module F U] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup H'] [Module ℂ H'] {σ σ' : F →+* ℂ} (j : U →ₛₗ[σ] H) (j' : U →ₛₗ[σ'] H') {n : ℕ}
    (b : Module.Basis (Fin n) F U) (c : H ≃ₗ⋆[ℂ] H') (hi : LinearIndependent ℂ fun k => j (b k))
    (hs : Submodule.span ℂ (Set.range j') = ⊤) : Submodule.span ℂ (Set.range j) = ⊤ := by
  have h1 : Submodule.span ℂ (Set.range fun k => j' (b k)) = ⊤ := top_le_iff.1 (hs ▸ span_range_le j' b)
  have h2 : Submodule.span ℂ (Set.range fun k => c.symm (j' (b k))) = ⊤ := by
    have h3 := congrArg (Submodule.map (c.symm : H' →ₗ⋆[ℂ] H)) h1
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h3
    exact h3
  haveI : Module.Finite ℂ H := ⟨h2 ▸ Submodule.fg_span (Set.finite_range _)⟩
  have h4 : Module.finrank ℂ H ≤ n := by simpa using finrank_le_of_span_eq_top h2
  have h5 : Fintype.card (Fin n) = Module.finrank ℂ H :=
    le_antisymm hi.fintype_card_le_finrank (by simpa using h4)
  refine top_le_iff.1 ((hi.span_eq_top_of_card_eq_finrank' h5).symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  exact ⟨b k, rfl⟩

theorem indep_of_conj {H X : Type} [AddCommGroup H] [Module ℂ H] {m : ℕ} (ev : H → X → ℂ)
    (hadd : ∀ x y, ev (x + y) = ev x + ev y) (hsmul : ∀ (a : ℂ) x, ev (a • x) = a • ev x) (w : Fin m → H)
    (φ : Fin m → X → ℂ) (hφ : LinearIndependent ℂ φ) (h : ∀ k g, ev (w k) g = starRingEnd ℂ (φ k g)) :
    LinearIndependent ℂ w := by
  let E : H →ₗ[ℂ] (X → ℂ) := { toFun := ev, map_add' := hadd, map_smul' := hsmul }
  rw [Fintype.linearIndependent_iff] at hφ ⊢
  intro a ha k
  have h1 : ∑ k, starRingEnd ℂ (a k) • φ k = 0 := by
    funext g
    have h2 := congrFun (congrArg E ha) g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero, Finset.sum_apply] at h2
    have h3 := congrArg (starRingEnd ℂ) h2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Pi.zero_apply, map_zero] at h3
    rw [Finset.sum_apply, Pi.zero_apply, ← h3]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    show _ = starRingEnd ℂ (a k * ev (w k) g)
    rw [h, map_mul, Complex.conj_conj]
    rfl
  simpa using hφ _ h1 k

theorem unif_all : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → JUnif T R κ v₀ := by
  intro h1 h2 D G _ _ Pl0 T0 A T _ R κ v₀ hL hM hT hp hκ hn i σ
  have good := GlobalTheory.T.uniformisation_goodEmbedding_independent_readings h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hp hκ hn i
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · exact good σ hσ
  obtain ⟨hc, hb⟩ := GlobalTheory.T.hilbertModel_conjugation_antilinear_bijection D G Pl0 T0 A T R κ v₀ hM hT
  have hbar := hb (GlobalTheory.T.cuspFormAdelicFunctions_eq_modelValues_semilinear h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hp)
  have hg := good_resC T hσ
  have hV := hT.laws.spaceW _ (inR i) _ hg
  obtain ⟨v, -, hv⟩ := jTop_bar T R κ v₀ hσ hV (hbar i σ hσ hV)
  have ind : ∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b →
      LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k) := fun m b hb =>
    indep_of_conj (evAt R i σ v) (fun x y => by simp only [evAt, map_add (f := _)]; rfl)
      (fun a x => by simp only [evAt, map_smul]; rfl) _ _
      (GlobalTheory.PhiIndep.phiC_indep D T κ hT.laws i _ hg hV m b hb) fun k g => congrFun (hv (b k)) g
  refine ⟨ind, ?_⟩
  obtain ⟨c⟩ := hc i σ hσ
  obtain ⟨b⟩ := hasB_nTop T hT.laws κ i
  exact span_top _ _ b c (ind _ _ b.linearIndependent) (good ((starRingEnd ℂ).comp σ) hg).2

end GlobalTheory.UnifAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormReadingsIndependentSpanningAllEmbeddingsStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormReadings_independent_spanning_all_embeddings : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → JUnif T R κ v₀ := by
  first | exact @GlobalTheory.UnifAll.unif_all | exact GlobalTheory.UnifAll.unif_all | (intros; apply GlobalTheory.UnifAll.unif_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfPins
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JUnifAndLUnifOfTieIn
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationRowCoreFormsOfGeometricAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationRowCoreFormsOfGeometricAction
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem lUnif_topR_of_geoAct : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GeoAct T R κ v₀ → (topR T R κ v₀).LUnif := by
  intro hC hV D G _ _ Pl0 T0 A T _ R κ v₀ hI hM hT hpb hκ hn hg
  exact lUnif_topN T R κ v₀ (nTop T κ) (hasB_nTop T hT.laws κ) hM.HW
    (GlobalTheory.T.cuspFormReadings_independent_spanning_all_embeddings hC hV D G Pl0 T0 A T R κ v₀ hI hM hT hpb hκ hn) hg

end GlobalTheory.HolDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationRowCoreFormsOfGeometricActionStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationRow_coreForms_of_geometricAction : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GeoAct T R κ v₀ → (topR T R κ v₀).LUnif := by
  first | exact @GlobalTheory.HolDict.lUnif_topR_of_geoAct | exact GlobalTheory.HolDict.lUnif_topR_of_geoAct | (intros; apply GlobalTheory.HolDict.lUnif_topR_of_geoAct <;> assumption)
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem jUnif_and_lUnif_of_tieIn : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → JUnif T R κ v₀ ∧ (GeoAct T R κ v₀ → (topR T R κ v₀).LUnif) := by
  intro h1 h2 D G _ _ Pl0 T0 A T _ R κ v₀ hL hM hT hpb hnV
  have hlp := GlobalTheory.HolDict.lastPos_of_kapIs D κ hT.kap
  exact ⟨GlobalTheory.T.cuspFormReadings_independent_spanning_all_embeddings h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hpb hlp hnV,
    GlobalTheory.T.uniformisationRow_coreForms_of_geometricAction h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hpb hlp hnV⟩

end GlobalTheory.HolDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TieInOfFwTie
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Div

theorem tieIn_of_fwTie : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), FWTie T R κ v₀ → TieIn T R κ v₀ :=
  fun _ _ _ _ _ t => ⟨t.laws, t.alg_eq, t.kap, t.hv₀, t.chiR, t.x0⟩

end GlobalTheory.Div
end

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TiedUnif

theorem lUnif_of_pins : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), ∀ (F : Face D A) (fw : FWTie T R κ v₀), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → BarTie fw → (∀ i, OMPins T R κ v₀ O i) → RhoGeo fw O → EquivAll T R κ O → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → R.LUnif := by
  intro h1 h2 D G _ _ Pl0 T0 A T _ R κ v₀ O F fw hI hG hM hb hO hr ha hn
  have hT : TieIn T R κ v₀ := GlobalTheory.Div.tieIn_of_fwTie T R κ v₀ fw
  have hpb : T.pb = R.C.P.pb := GlobalTheory.PinsFixHalf.pb_eq_of_pins T R κ v₀ O hI fw.laws hO
  have hu : JUnif T R κ v₀ := (GlobalTheory.HolDict.jUnif_and_lUnif_of_tieIn h1 h2 D G Pl0 T0 A T R κ v₀ hI hM hT hpb hn).1
  exact lUnif_of_rhoGeo_equivAll fw hM hG hb hr ha (GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding T R κ v₀ O hI hT hpb hO) hu

end GlobalTheory.TiedUnif
end

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TiedUnif

theorem uniformisation_every_embedding_thirdKind : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (fw : FWTie T R.toRealDat κ v₀), ∀ (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), R.WeakCharacterisation F → BarTie fw → (∀ i, OMPins T R.toRealDat κ v₀ O i) → RhoGeo fw O → EquivAll T R.toRealDat κ O → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → R.toRealDat.LUnif := by
  intro h1 h2 D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ fw O hC hb hO hr ha hn
  exact lUnif_of_pins h1 h2 T R.toRealDat κ v₀ O F.lv2 fw hC.base.lev hC.base.grp hC.base.models hb hO hr ha hn

end GlobalTheory.TiedUnif
