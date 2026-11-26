module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOfValuesSesq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPcRatFMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorLatticePointOfIntegralSplitPlaceCoor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedFinprodPureTensorAdelicSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedFinprodPureTensorAdelicSchwartz
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.RestPure

theorem evFin_eq_zero {F : Type} [Field F] [NumberField F] {κ : Type} (z : κ → AF F) (hz : At (evI F) z) (v : Pl (F := F)) (i : κ) :
    evFin F v (z i) = 0 := by

  have hu : evI F (pairA F 0 1) = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _
  have h1 : evFin F v (pairA F 0 1) = 1 := by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v 1 = 1
    exact map_one _
  have h := congrFun (hz _ hu) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  have h2 := congrArg (evFin F v) h
  rwa [map_mul, h1, one_mul, map_zero] at h2

theorem rest_evI_finprod : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ f : SInf F κ, Rest (evI F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  intro F _ _ κ _ φ hφ hcof f
  refine ⟨fun x z hz => ?_, ?_⟩
  ·
    have hc : ∀ v i, evFin F v ((x + z) i) = evFin F v (x i) := fun v i => by
      rw [Pi.add_apply, map_add (f := _), evFin_eq_zero z hz v i, add_zero]
    simp only [hc]
  ·
    have hg : (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
        SB (κ → FiniteAdeleRing (𝓞 F) F) :=
      ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ hcof,
        GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ hcof⟩
    show _ ∈ Submodule.span ℂ _
    exact Submodule.subset_span ⟨f, _, hg, rfl⟩

end GlobalTheory.RestPure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedFinprodPureTensorAdelicSchwartzStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_finprod_pure_tensor_adelic_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ f : SInf F κ, Rest (evI F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  first | exact @GlobalTheory.RestPure.rest_evI_finprod | exact GlobalTheory.RestPure.rest_evI_finprod | (intros; apply GlobalTheory.RestPure.rest_evI_finprod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFactorNonzero
namespace GlobalTheory.StepFacNe

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.StepFacNe.chrW_continuous {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    (χ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (h : Continuous χ) {v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)}
    (τ : E →ₐ[F] _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    Continuous (fun x : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)ˣ => (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW χ τ x : ℂ)) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW
  have h1 := _root_.GlobalTheory.LFun.continuous_locChar h (_root_.GlobalTheory.AdelicU.splitPrime τ)
  have h2 := Continuous.units_map
    (_root_.GlobalTheory.LFun.complMap (_root_.GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom
    (_root_.GlobalTheory.LFun.SplitChart.continuous_complMap (_root_.GlobalTheory.AdelicU.splitPrime_under τ))
  exact h1.comp h2


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.StepFacNe.chrW_ram {F E : Type} [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (χ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) {v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    (h : ¬ _root_.GlobalTheory.LFun.UnrAt χ (_root_.GlobalTheory.AdelicU.splitPrime τ)) :
    ∃ x : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)ˣ, (x : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∈ v.adicCompletionIntegers F ∧
      ((x⁻¹ : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)ˣ) : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∈ v.adicCompletionIntegers F ∧
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW χ τ x ≠ 1 := by
  have hw := _root_.GlobalTheory.AdelicU.splitPrime_under τ
  unfold _root_.GlobalTheory.LFun.UnrAt at h
  push_neg at h
  obtain ⟨y, hy1, hy2⟩ := h
  unfold _root_.Formalism.L2.Host.IsUnitAt at hy1
  obtain ⟨a, ha⟩ := (_root_.GlobalTheory.LFun.SplitTie.complMap_bijective τ hw).2 (y : _)
  have hv : Valued.v a = 1 := by
    rw [← _root_.GlobalTheory.LFun.SplitTie.valued_complMap τ hw, ha]
    exact hy1
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hv
  refine ⟨Units.mk0 a ha0, ?_, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp [hv]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp [hv]
  · intro h1
    apply hy2
    have hy : Units.map (_root_.GlobalTheory.LFun.complMap hw).toMonoidHom (Units.mk0 a ha0) = y :=
      Units.ext (by simpa using ha)
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW at h1
    rw [MonoidHom.comp_apply, hy] at h1
    exact h1

end GlobalTheory.StepFacNe
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormRestrictedPlane
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagrGram

theorem hTens_eq_trace {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = Matrix.trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  conv_rhs => enter [2, j, 2, l]; rw [Finset.sum_comm]
  conv_rhs => enter [2, j]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hTens_restrict {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (JA : Matrix α α E) (JB : Matrix β β E) (JB₁ : Matrix γ γ E) (ι : Matrix β γ E)
    (h : ιᵀ * JB * ι.map c = JB₁) (z z' : Matrix α γ E) :
    hTens c JA JB (z * ιᵀ) (z' * ιᵀ) = hTens c JA JB₁ z z' := by
  rw [hTens_eq_trace, hTens_eq_trace, ← h, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.map_mul, Matrix.transpose_map]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem incM_map_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {m k : Type} (J : Matrix m k E) :
    (incM F J).map (cA σ) = incM F (J.map σ) := by
  ext i j
  simp [incM, cA, inclR]

theorem symp_restrict_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (JW₁ : Matrix (Fin d₁) (Fin d₁) E)
    (ι : Matrix (Fin d) (Fin d₁) E), ιᵀ * JW * ι.map σ = JW₁ → ∀ z z' : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      symp (cA σ) (-1) (incM F JX) (incM F JW) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F ι)ᵀ)
        (incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F ι)ᵀ) = symp (cA σ) (-1) (incM F JX) (incM F JW₁) z z' := by
  intro F E _ _ _ _ _ σ n d d₁ JX JW JW₁ ι h z z'
  have hA : (incM F ι)ᵀ * incM F JW * (incM F ι).map (cA σ) = incM F JW₁ := by
    rw [incM_map_cA, ← h]
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    simp only [incM, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [h1, Matrix.one_mul, Matrix.one_mul]
  simp only [symp]
  rw [hTens_restrict _ _ _ _ _ hA]

end GlobalTheory.MixedLagrGram
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormEqOrientedHomSymplecticForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormEqOrientedHomSymplecticForm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger

theorem cA_eq_sigR (D : D7) (z : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig z = Formalism.L2.Theta.cA D z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem triple_sum_comm_reverse {ι κ μ M : Type} [Fintype ι] [Fintype κ] [Fintype μ] [AddCommMonoid M] (f : ι → κ → μ → M) :
    ∑ i, ∑ k, ∑ l, f i k l = ∑ l, ∑ k, ∑ i, f i k l := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
  exact Finset.sum_comm

theorem symp_eq_symplO : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ x y : Formalism.IndefR.Datum.WO S T,
      GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y =
        Formalism.IndefR.Datum.symplO S T x y := by
  intro D S T JA JB ξ hA hB x y
  have hB' : ∀ j l, ξ * incM D.host.F JB j l = incA D D.host.xi0 * incA D (S.gram⁻¹ j l) := by
    intro j l
    have h1 := congrFun (congrFun hB j) l
    rw [Matrix.smul_apply, smul_eq_mul] at h1
    rw [h1]
    show inclR (F := D.host.F) (AF D.host.F) (D.host.xi0 * S.gram⁻¹ j l) = _
    exact map_mul _ _ _
  have hA' : ∀ i k, incM D.host.F JA i k = incA D (T.gram k i) := by
    intro i k; subst hA; rfl
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens Formalism.IndefR.Datum.symplO Formalism.IndefR.Datum.hO
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [triple_sum_comm_reverse]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hA', cA_eq_sigR]
  calc ξ * (x i j * incA D (T.gram k i) * incM D.host.F JB j l * Formalism.L2.Theta.cA D (y k l))
      = x i j * incA D (T.gram k i) * (ξ * incM D.host.F JB j l) * Formalism.L2.Theta.cA D (y k l) := by ring
    _ = _ := by rw [hB']; ring

end GlobalTheory.WeilSchrodinger

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormEqOrientedHomSymplecticFormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceSymplecticForm_eq_orientedHomSymplecticForm : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ x y : Formalism.IndefR.Datum.WO S T,
      GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y =
        Formalism.IndefR.Datum.symplO S T x y := by
  first | exact @GlobalTheory.WeilSchrodinger.symp_eq_symplO | exact GlobalTheory.WeilSchrodinger.symp_eq_symplO | (intros; apply GlobalTheory.WeilSchrodinger.symp_eq_symplO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqSumSplitPlaceParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqSumSplitPlaceParts
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LatSplit

open GlobalTheory.AdelicU.Supp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem singleTens_tmul (v : Pl (F := F)) (a : Fv F v) (x : E) :
    singleTens E v (a ⊗ₜ[F] x) = GlobalTheory.LatVac.liftV v a ⊗ₜ[F] x := rfl

theorem tmul_smul_gen_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {a : Fv F v}
    (ha : a ∈ v.adicCompletionIntegers F) (o : 𝓞 E) {c : AF F} (hc : At (evFin F v) c)
    (hcv : evFin F v c ∈ v.adicCompletionIntegers F) {x : Fin n → E} (hx : x ∈ X.L) {y : Fin d → E} (hy : y ∈ W.L) :
    singleTens E v (a ⊗ₜ[F] (o : E)) • (c • incM F (Matrix.vecMulVec x y)) ∈ latAtV X W v := by
  refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a * c, ?_, ?_, o • x, X.L.smul_mem o hx, y, hy, ?_⟩
  · intro u hu
    rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u c, hc u hu, mul_zero]
  · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
    exact mul_mem ha hcv
  · ext i j
    simp only [singleTens_tmul, Matrix.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, smul_eq_mul,
      Pi.smul_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, inclR]
    change _ * ((c ⊗ₜ[F] (1:E)) * ((1:AF F) ⊗ₜ[F] (x i * y j))) =
      ((GlobalTheory.LatVac.liftV v a * c) ⊗ₜ[F] (1:E)) * ((1:AF F) ⊗ₜ[F] ((o:E) * x i * y j))
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_assoc]

theorem singleTens_smul_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {y : Fv F v ⊗[F] E}
    (hy : y ∈ intLoc F E v) {γ : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hγ : γ ∈ latAtV X W v) :
    singleTens E v y • γ ∈ latAtV X W v := by
  refine intLoc_induction (p := fun y => singleTens E v y • γ ∈ latAtV X W v) ?_ ?_ ?_ ?_ hy
  · intro a ha o
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, hcv, x, hx, y', hy', rfl⟩ := hz
      exact tmul_smul_gen_mem X W v ha o hc hcv hx hy'
    | zero => rw [smul_zero]; exact zero_mem _
    | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg z _ h => rw [smul_neg]; exact neg_mem h
  · show singleTens E v 0 • γ ∈ latAtV X W v
    rw [map_zero, zero_smul]; exact zero_mem _
  · intro y z h h'
    show singleTens E v (y + z) • γ ∈ latAtV X W v
    rw [map_add (f := _), add_smul]; exact add_mem h h'
  · intro y h
    show singleTens E v (-y) • γ ∈ latAtV X W v
    rw [map_neg, neg_smul]; exact neg_mem h

theorem piW_splitIdemAd {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) :
    piW t (splitIdemAd hcm t) = 1 ∧ piW (t.comp σ) (splitIdemAd hcm t) = 0 := by
  constructor
  · change splitProj t (compFin F E v (singleTens E v (splitIdem hcm t))) = 1
    rw [compFin_singleTens_self, splitProj_splitIdem]
  · change splitProj (t.comp σ) (compFin F E v (singleTens E v (splitIdem hcm t))) = 0
    rw [compFin_singleTens_self, splitProj_comp_splitIdem]

theorem latAtV_decomp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v), ∀ γ ∈ latAtV X W v,
      ∃ γ₁ ∈ latAtV X W v, ∃ γ₂ ∈ latAtV X W v, γ = γ₁ + γ₂ ∧ γ₁.map (piW (t.comp σ)) = 0 ∧ γ₂.map (piW t) = 0 := by
  intro F E _ _ _ _ _ σ n d hcm X W v t γ hγ
  have h1 : splitIdemAd hcm t • γ ∈ latAtV X W v := singleTens_smul_mem X W v (splitIdem_mem hcm t) hγ
  obtain ⟨e1, e0⟩ := piW_splitIdemAd hcm t
  refine ⟨splitIdemAd hcm t • γ, h1, γ - splitIdemAd hcm t • γ, sub_mem hγ h1, (add_sub_cancel _ _).symm, ?_, ?_⟩
  · ext i j
    simp [smul_eq_mul, e0]
  · ext i j
    simp [smul_eq_mul, e1]

end GlobalTheory.LatSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqSumSplitPlacePartsStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorLatticeAtFinitePlace_eq_sum_splitPlace_parts : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v), ∀ γ ∈ latAtV X W v,
      ∃ γ₁ ∈ latAtV X W v, ∃ γ₂ ∈ latAtV X W v, γ = γ₁ + γ₂ ∧ γ₁.map (piW (t.comp σ)) = 0 ∧ γ₂.map (piW t) = 0 := by
  first | exact @GlobalTheory.LatSplit.latAtV_decomp | exact GlobalTheory.LatSplit.latAtV_decomp | (intros; apply GlobalTheory.LatSplit.latAtV_decomp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSetCharPolyCoeffBounded
noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.LocBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_cj (w : Pl E) : Continuous (cj w) := by
  by_cases h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)
  · exact (GlobalTheory.ConjAtPlace.cj_spec w h).1
  · rw [GlobalTheory.ConjAtPlace.cj_of_not w h]; exact continuous_id

theorem continuous_nrmL (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = fun y => y := funext fun y => by simp [nrmL, hs]
    rw [e]; exact continuous_id
  · have e : nrmL n w = fun y => y * thetaGL n (cj w) y := funext fun y => by simp [nrmL, hs]
    rw [e]
    exact continuous_id.mul (GlobalTheory.ThetaPull.continuous_thetaGL (cj w) (continuous_cj w))

theorem continuous_coeff_charpoly {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem exists_bound_of_isCompact (w : Pl E) {K : Set (w.adicCompletion E)} (hK : IsCompact K) :
    ∃ m : ℕ, ∀ x ∈ K, Valued.v x ≤ WithZero.exp (m : ℤ) := by
  let U : ℕ → Set (w.adicCompletion E) := fun m => {y | Valued.v y ≤ WithZero.exp (m : ℤ)}
  have hcov : K ⊆ ⋃ m : ℕ, U m := by
    intro x _
    rcases eq_or_ne (Valued.v x) 0 with h0 | h0
    · exact Set.mem_iUnion.2 ⟨0, by simp only [U, Set.mem_setOf_eq, h0]; exact zero_le'⟩
    · refine Set.mem_iUnion.2 ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
      show Valued.v x ≤ _
      conv_lhs => rw [← WithZero.exp_log h0]
      rw [WithZero.exp_le_exp]
      omega
  have hdir : Directed (· ⊆ ·) U :=
    Monotone.directed_le fun a b hab y hy => le_trans hy (WithZero.exp_le_exp.2 (by exact_mod_cast hab))
  obtain ⟨m, hm⟩ := hK.elim_directed_cover U (fun m => GlobalTheory.PrincCong.isOpen_ball w (m : ℤ)) hcov hdir
  exact ⟨m, fun x hx => hm hx⟩

theorem bound_charpoly_nrmL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (C : Set (GLw n w)), IsCompact C →
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ ∀ y ∈ C,
      (∀ i, Valued.v ((nrmL n w y).val.charpoly.coeff i) ≤ γ) ∧
        γ⁻¹ ≤ Valued.v ((nrmL n w y).val.charpoly.coeff 0) := by
  intro E _ _ _ n w C hC
  let F : Option (Fin (n + 1)) → GLw n w → w.adicCompletion E := fun o y =>
    match o with
    | none => ((nrmL n w y)⁻¹).val.det
    | some i => (nrmL n w y).val.charpoly.coeff i
  have hF : ∀ o, Continuous (F o) := by
    rintro (_ | i)
    · exact (Units.continuous_val.comp (continuous_nrmL n w).inv).matrix_det
    · exact (continuous_coeff_charpoly n i).comp (Units.continuous_val.comp (continuous_nrmL n w))
  have hK : IsCompact (⋃ o, F o '' C) := isCompact_iUnion fun o => hC.image (hF o)
  obtain ⟨m, hm⟩ := exists_bound_of_isCompact w hK
  have hb : ∀ o, ∀ y ∈ C, Valued.v (F o y) ≤ WithZero.exp (m : ℤ) := fun o y hy =>
    hm _ (Set.mem_iUnion.2 ⟨o, Set.mem_image_of_mem _ hy⟩)
  refine ⟨WithZero.exp (m : ℤ), WithZero.exp_ne_zero, fun y hy => ⟨fun i => ?_, ?_⟩⟩
  · by_cases hi : i ≤ n
    · exact hb (some ⟨i, Nat.lt_succ_of_le hi⟩) y hy
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; omega)]
      simp
  · have h1 : Valued.v (((nrmL n w y)⁻¹).val.det) ≤ WithZero.exp (m : ℤ) := hb none y hy
    have hdet : (nrmL n w y).val.det * ((nrmL n w y)⁻¹).val.det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    have hc0 : (nrmL n w y).val.charpoly.coeff 0 = (-1) ^ n * (nrmL n w y).val.det := by
      rw [Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩,
        one_mul]
    have hv : Valued.v ((nrmL n w y).val.charpoly.coeff 0) * Valued.v (((nrmL n w y)⁻¹).val.det) = 1 := by
      rw [hc0, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, ← map_mul, hdet, map_one]
    have hne : Valued.v (((nrmL n w y)⁻¹).val.det) ≠ 0 := fun h => by
      rw [h, mul_zero] at hv; exact zero_ne_one hv
    rw [eq_inv_of_mul_eq_one_left hv]
    exact inv_anti₀ (zero_lt_iff.2 hne) h1

end GlobalTheory.LocBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairingCoordinatesSchrodingerFolland
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairingCoordinatesSchrodingerFolland
open scoped SchwartzMap Matrix

open scoped RealInnerProductSpace
noncomputable section
namespace GlobalTheory.ArchUniq
open GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def leftForm {P : V → V → ℝ} (hP : IsPairing P) (b : V) : V →ₗ[ℝ] ℝ where
  toFun x := P x b
  map_add' x x' := hP.addL x x' b
  map_smul' c x := hP.smulL c x b

theorem pair_expand {n : ℕ} (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) {P : V → V → ℝ} (hP : IsPairing P) (y b : V) :
    P y b = ∑ i, C y i * P (C.symm (EuclideanSpace.single i 1)) b := by
  have hy : y = ∑ i, C y i • C.symm (EuclideanSpace.single i 1) := by
    conv_lhs => rw [← C.symm_apply_apply y, ← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (C y)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have e : P y b = leftForm hP b y := rfl
  rw [e]
  conv_lhs => rw [hy]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp [leftForm, hP.smulL]

def pairCoordsL {n : ℕ} (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) {P : V → V → ℝ} (hP : IsPairing P) :
    V × V →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) where
  toFun v := Sum.elim (fun i => C v.1 i) (fun i => -P (C.symm (EuclideanSpace.single i 1)) v.2)
  map_add' v v' := by
    funext j
    rcases j with i | i <;> simp [hP.addR]; ring
  map_smul' c v := by
    funext j
    rcases j with i | i <;> simp [hP.smulR]

theorem pairCoordsL_injective {n : ℕ} (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) {P : V → V → ℝ} (hP : IsPairing P) :
    Function.Injective (pairCoordsL C hP) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨a, b⟩ h
  have ha : a = 0 := by
    apply C.injective
    ext i
    simpa [pairCoordsL] using congrFun h (Sum.inl i)
  have hb : b = 0 := by
    apply hP.nondegR
    intro x
    rw [pair_expand C hP]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrFun h (Sum.inr i)
    simp [pairCoordsL] at this
    simp [this]
  simp [ha, hb]

theorem exists_pairing_coords : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v v', GlobalTheory.RealWeil.sympl (φ v) (φ v') = -GlobalTheory.ArchUniq.omega P v v') ∧
      ∀ v (f : EuclideanSpace ℝ (Fin n) → ℂ),
        GlobalTheory.ArchUniq.schrF P v (f ∘ C) = GlobalTheory.RealWeil.rhoFun (φ v) f ∘ C := by
  intro V _ _ _ P hP n hn
  let C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (hn.trans (finrank_euclideanSpace_fin).symm)
  have hdim : Module.finrank ℝ (V × V) = Module.finrank ℝ (Fin n ⊕ Fin n → ℝ) := by
    simp [Module.finrank_prod, hn]
  let φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    LinearMap.linearEquivOfInjective (pairCoordsL C hP) (pairCoordsL_injective C hP) hdim
  have hφ : ∀ v, φ v = pairCoordsL C hP v := fun v => rfl
  have hp : ∀ v : V × V, pPart (φ v) = C v.1 := by
    intro v; ext i; simp [hφ, pPart, pairCoordsL]
  have hq : ∀ (v : V × V) (x : EuclideanSpace ℝ (Fin n)),
      ⟪qPart (φ v), x⟫ = -∑ i, P (C.symm (EuclideanSpace.single i 1)) v.2 * x i := by
    intro v x
    simp [hφ, qPart, pairCoordsL, PiLp.inner_apply, mul_comm]
  have hq' : ∀ (v : V × V) (y : V), ⟪qPart (φ v), C y⟫ = -P y v.2 := by
    intro v y
    rw [hq, pair_expand C hP y v.2]
    simp [mul_comm]
  have hCq : ∀ (v : V × V) (y : V), ⟪C y, qPart (φ v)⟫ = -P y v.2 := by
    intro v y
    rw [real_inner_comm, hq']
  refine ⟨C, φ, ?_, ?_⟩
  · intro v v'
    simp only [sympl, omega, hp, hCq, hq']
    ring
  · intro v f
    funext y
    simp only [schrF, rhoFun, phase, Function.comp_apply, map_add (f := _), hp, hq', hCq]
    congr 1
    congr 1
    push_cast
    ring
end GlobalTheory.ArchUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairingCoordinatesSchrodingerFollandStatement
open scoped SchwartzMap Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pairing_coordinates_schrodinger_folland : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v v', GlobalTheory.RealWeil.sympl (φ v) (φ v') = -GlobalTheory.ArchUniq.omega P v v') ∧
      ∀ v (f : EuclideanSpace ℝ (Fin n) → ℂ),
        GlobalTheory.ArchUniq.schrF P v (f ∘ C) = GlobalTheory.RealWeil.rhoFun (φ v) f ∘ C := by
  first | exact @GlobalTheory.ArchUniq.exists_pairing_coords | exact GlobalTheory.ArchUniq.exists_pairing_coords | (intros; apply GlobalTheory.ArchUniq.exists_pairing_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusPart

def GoodCover {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (u : splitTorus S X ⟶ G) : Prop :=
  ∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen u V

def IsKer {S : Scheme.{0}} {T G B : Over S} [GrpObj G] [GrpObj B] (u : T ⟶ G) (q : G ⟶ B) : Prop :=
  IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ QuasiCompact q.left ∧ IsPullback u (toUnit _) q η[B]

def TorPol {O : Type} [CommRing O] (c : O →+* O) {S : Scheme.{0}} {G : Over S} [GrpObj G] (i : OAct O G) {X : Type}
    [AddCommGroup X] (u : splitTorus S X ⟶ G) {K : Type} [Field K] (x : Sp K ⟶ S) : Prop :=
  ∃ (G' : Over (Sp K)) (_ : GrpObj G') (i' : OAct O G') (φ : G'.left ⟶ G.left) (u' : splitTorus (Sp K) X ⟶ G')
    (P : Out.PolAV (Sp K)) (q : G' ⟶ P.A) (j : OAct O P.A),
    IsActPull i' i x φ ∧ TorusCompat x φ u' u ∧ IsKer u' q ∧ (∀ a, i'.act a ≫ q = q ≫ j.act a) ∧ IsRosati c P j

def QFin {S : Scheme.{0}} (Z : Over S) : Prop :=
  Flat Z.hom ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ LocallyQuasiFinite Z.hom

def RatOver {S : Scheme.{0}} (Z : Over S) {K : Type} [Field K] (x : Sp K ⟶ S) : Prop :=
  ∀ (Ω : Type) [Field Ω] (β : K →+* Ω) (y : Sp Ω ⟶ Z.left), y ≫ Z.hom = spMap β ≫ x →
    ∃ y₁ : Sp K ⟶ Z.left, y₁ ≫ Z.hom = x ∧ spMap β ≫ y₁ = y

def WtGeneric : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G),
    IsIntegral (splitTorus S X ⊗ G).left → ∀ (V : G.left.Opens) (f : Γ(G.left, V)) (χ : X) (Z : Over S)
      (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), IsDominant (lift t g).left →
      ∀ (h₁ : ⊤ ≤ ((t ≫ u) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
        (((t ≫ u) * g).left.appLE _ ⊤ h₁).hom f =
          t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom f → Wt u V f χ

theorem isKer_of_isQuot {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B] {u : T ⟶ G} {q : G ⟶ B}
    (h : IsQuot u q) : IsKer u q :=
  have := h.2.2.2.2.1
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, inferInstance, h.2.2.2.2.2.1⟩

theorem isKer_torusExtension {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (T : TorusExtension G) :
    letI := T.addCommGroup; letI := T.grpB; IsKer T.i T.q :=
  ⟨T.q_hom, T.q_flat, T.q_surjective, T.q_quasiCompact, T.isKernel⟩

theorem IsKer.comp_iso {S : Scheme.{0}} {T G B B' : Over S} [GrpObj G] [GrpObj B] [GrpObj B'] {u : T ⟶ G} {q : G ⟶ B}
    (h : IsKer u q) (e : B ≅ B') (he : IsMonHom (q ≫ e.hom)) : IsKer u (q ≫ e.hom) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  refine ⟨he, by rw [Over.comp_left]; infer_instance, by rw [Over.comp_left]; infer_instance,
    by rw [Over.comp_left]; infer_instance, h₅.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
      (by simp) ?_⟩
  rw [Iso.refl_hom, Category.id_comp, ← IsMonHom.one_hom q, Category.assoc, IsMonHom.one_hom]

theorem IsKer.baseChange {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G]
    [GrpObj B] {G' B' : Over S'} [GrpObj G'] [GrpObj B'] {φ : G'.left ⟶ G.left} {ψ : B'.left ⟶ B.left}
    (hφ : IsGrpPullback G' G f φ) (hψ : IsGrpPullback B' B f ψ) {u : splitTorus S X ⟶ G} {u' : splitTorus S' X ⟶ G'}
    (hT : TorusCompat f φ u' u) {q : G ⟶ B} (h : IsKer u q) :
    ∃ q' : G' ⟶ B', IsKer u' q' ∧ IsPullback φ q'.left q.left ψ := by
  obtain ⟨e, he, heF⟩ := grpPullback_iso hφ (isGrpPullback_pullback G f)
  obtain ⟨d, hd, hdF⟩ := grpPullback_iso (isGrpPullback_pullback B f) hψ
  obtain ⟨_, _, _, _, h₅⟩ := h
  have sq := isPullback_pullback_map_left f q
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S').map e.hom))
  have hi : u' ≫ e.hom = (SplitTorus.bcIso f X).hom ≫ (Over.pullback f).map u := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have a := (isPullback_pullback_map_left f u).w
    have b := SplitTorus.bcIso_hom_fst f X
    exact ((Category.assoc _ _ _).trans ((congrArg (u'.left ≫ ·) heF).trans (torusCompat_iff.1 hT).symm)).trans
      ((congrArg (· ≫ u.left) b.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) a).trans (Category.assoc _ _ _).symm)))
  have hk : IsPullback u' (toUnit _) (e.hom ≫ (Over.pullback f).map q) (η[(Over.pullback f).obj B]) := by
    refine (isPullback_kernel_baseChange f h₅).of_iso (SplitTorus.bcIso f X).symm e.symm (Iso.refl _)
      (Iso.refl _) ?_ (toUnit_unique _ _) (by simp) (by simp)
    rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, hi, Iso.inv_hom_id_assoc]
  have h₁ : Flat ((Over.pullback f).map q).left := MorphismProperty.of_isPullback (P := @Flat) sq inferInstance
  have h₂ : Surjective ((Over.pullback f).map q).left :=
    MorphismProperty.of_isPullback (P := @Surjective) sq inferInstance
  have h₃ : QuasiCompact ((Over.pullback f).map q).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have hK : IsKer u' (e.hom ≫ (Over.pullback f).map q) := ⟨inferInstance, by rw [Over.comp_left]; infer_instance,
    by rw [Over.comp_left]; infer_instance, by rw [Over.comp_left]; infer_instance, hk⟩
  refine ⟨_, hK.comp_iso d inferInstance, ?_⟩
  refine IsPullback.of_bot (v₂₁ := B'.hom) (v₂₂ := B.hom) ?_ ?_ hψ.1
  · rw [Over.w, Over.w]
    exact hφ.1
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hdF, ← heF, Category.assoc]
    exact congrArg (_ ≫ ·) sq.w

theorem IsKer.exists_oAct {S : Scheme.{0}} {T G B : Over S} [GrpObj G] [GrpObj B] {u : T ⟶ G} {q : G ⟶ B}
    (h : IsKer u q) {O : Type} [CommRing O] (i : OAct O G) (hu : ∀ a, u ≫ i.act a ≫ q = toUnit _ ≫ η[B]) :
    ∃ j : OAct O B, ∀ a, i.act a ≫ q = q ≫ j.act a := by
  obtain ⟨_, _, _, _, h₅⟩ := h
  have := i.hom
  have : Epi q := FlatQuotient.epi_of_flat_surjective q
  choose fB hm hfB using fun a => FlatQuotient.exists_desc q u (i.act a ≫ q) h₅ (hu a)
  refine ⟨⟨fB, hm, ?_, fun a b => ?_, fun a b => ?_⟩, fun a => (hfB a).symm⟩
  · rw [← cancel_epi q, hfB, i.one, Category.comp_id, Category.id_comp]
  · rw [← cancel_epi q, hfB, i.mul, Category.assoc, ← hfB, reassoc_of% hfB]
  · rw [← cancel_epi q, hfB, MonObj.comp_mul, hfB, hfB, i.add, MonObj.mul_comp]

theorem exists_isActPull {O : Type} [CommRing O] {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G]
    [IsCommMonObj G] (i : OAct O G) : IsActPull (OAct.pullback f G i) i f (pullback.fst G.hom f) :=
  ⟨isGrpPullback_pullback G f, fun _ => pullback.lift_fst _ _ _⟩

end GlobalTheory.TorusPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicGLMulVecHaarEqModulusDet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicGLMulVecHaarEqModulusDet
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.JacSubst

open GlobalTheory.ModuLR GlobalTheory.GaugeEx

theorem chi_AF_split (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    (addEquivAddHaarChar (mulVecCE M hM) : ℝ) =
      (modu (Ainf F) (fstA F M.det) : ℝ) * ∏ᶠ v, ‖evalV F v (sndA F M.det)‖ := _root_.GlobalTheory.SiegelCov.chi_adele (κ := κ) F M hM

theorem chi_AF_det (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    addEquivAddHaarChar (mulVecCE M hM) = distribHaarChar (AF F) hM.unit := by
  classical
  let a : (AF F)ˣ := hM.unit
  let N : Matrix Unit Unit (AF F) := fun _ _ => (a : AF F)
  have hNd : N.det = M.det := by rw [Matrix.det_unique]; rfl
  have hN : IsUnit N.det := hNd ▸ hM
  have h1 : distribHaarChar (AF F) a = addEquivAddHaarChar (mulVecCE N hN) := by
    rw [GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar,
      ← addEquivAddHaarChar_transport (GlobalTheory.ModuNorm.evalUnitCE (AF F)) (mulVecCE N hN)]
    congr 1
    ext x
    show (a : AF F) * x = (N *ᵥ fun _ => x) ()
    simp [N, Matrix.mulVec, dotProduct]
  apply NNReal.coe_injective
  show (addEquivAddHaarChar (mulVecCE M hM) : ℝ) = (distribHaarChar (AF F) a : ℝ)
  rw [h1, chi_AF_split, chi_AF_split, hNd]

def colCE (R : Type) [AddCommGroup R] [TopologicalSpace R] (d : ℕ) : (Fin d → R) ≃ₜ+ Matrix (Fin d) (Fin 1) R where
  toFun u := Matrix.of fun i _ => u i
  invFun m i := m i 0
  left_inv u := rfl
  right_inv m := by
    ext i j
    rw [Fin.fin_one_eq_zero j]
    rfl
  map_add' u v := rfl
  continuous_toFun := continuous_pi fun i => continuous_pi fun _ => continuous_apply i
  continuous_invFun := continuous_pi fun i => (continuous_apply 0).comp (continuous_apply i)

def coordCE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (b : Module.Basis (Fin n) F E) : AE F E ≃ₜ (Fin n → AF F) :=
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  { (Algebra.TensorProduct.basis (AF F) b).equivFun.toEquiv with
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis (AF F) b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis (AF F) b).equivFun.symm.toLinearMap }

end GlobalTheory.JacSubst


open GlobalTheory.ModuLR GlobalTheory.GaugeEx GlobalTheory.JacSubst in
theorem GlobalTheory.JacSubst.integral_mulVec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (t : GL (Fin d) (AE F E)),
    ∀ μ : @Measure (Fin d → AE F E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f : (Fin d → AE F E) → ℂ, ∫ u, f ((t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ u) ∂μ =
      (((distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ)⁻¹ : ℝ) : ℂ) *
        ∫ u, f u ∂μ := by
  intro F E _ _ _ _ _ d t μ hμ f
  letI mV : MeasurableSpace (Fin d → AE F E) := borel _
  haveI : BorelSpace (Fin d → AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  let e := coordCE F E (Module.finBasis F E)
  haveI : LocallyCompactSpace (AE F E) := e.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin d) (Fin 1) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin d → Fin 1 → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin d) (Fin 1) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin 1 → AE F E))
  letI : MeasurableSpace (Matrix (Fin d) (Fin 1) (AE F E)) := borel _
  haveI : BorelSpace (Matrix (Fin d) (Fin 1) (AE F E)) := ⟨rfl⟩
  haveI : μ.Regular := inferInstance
  have hdt : IsUnit (t : Matrix (Fin d) (Fin d) (AE F E)).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
  let φ := mulVecCE (t : Matrix (Fin d) (Fin d) (AE F E)) hdt
  obtain ⟨κ, _, _, Λ, hΛ, hdet, hχ⟩ := @exists_matrix_restrictScalars_lrCE F E _ _ _ _ _ d (1 : ℕ) _ _ _ _ t (1 : GL (Fin 1) (AE F E))
  have hc : addEquivAddHaarChar φ =
      distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) := by
    have h1 : addEquivAddHaarChar φ = addEquivAddHaarChar (lrCE t (1 : GL (Fin 1) (AE F E))) := by
      rw [← addEquivAddHaarChar_transport (colCE (AE F E) d) φ]
      congr 1
      ext m i j
      rw [Fin.fin_one_eq_zero j]
      show ((t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ (fun k => m k 0)) i =
        ((t : Matrix (Fin d) (Fin d) (AE F E)) * m * ((1 : GL (Fin 1) (AE F E)) : Matrix (Fin 1) (Fin 1) (AE F E))) i 0
      rw [Units.val_one, Matrix.mul_one]
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [h1, hχ, chi_AF_det]
    congr 1
    ext
    simp only [IsUnit.unit_spec, hdet, Units.coe_map, MonoidHom.coe_coe, map_one, one_pow, mul_one, pow_one]
  have hmap : μ.map φ = (addEquivAddHaarChar φ)⁻¹ • μ := by
    have key := addEquivAddHaarChar_smul_map μ φ
    have hne : addEquivAddHaarChar φ ≠ 0 := (addEquivAddHaarChar_pos φ).ne'
    calc μ.map φ = ((addEquivAddHaarChar φ)⁻¹ * addEquivAddHaarChar φ) • μ.map φ := by
          rw [inv_mul_cancel₀ hne, one_smul]
      _ = (addEquivAddHaarChar φ)⁻¹ • μ := by rw [mul_smul, key]
  have hint : ∫ u, f u ∂(μ.map φ) = ∫ u, f ((t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ u) ∂μ :=
    integral_map_equiv φ.toHomeomorph.toMeasurableEquiv f
  rw [← hint, hmap, integral_smul_nnreal_measure, hc, NNReal.smul_def, Complex.real_smul, NNReal.coe_inv]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicGLMulVecHaarEqModulusDetStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_adelicGL_mulVec_haar_eq_modulus_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    ∀ μ : @Measure (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → ℂ, ∫ u, f ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ u) ∂μ =
      (((distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ)⁻¹ : ℝ) : ℂ) *
        ∫ u, f u ∂μ := by
  first | exact @GlobalTheory.JacSubst.integral_mulVec | exact GlobalTheory.JacSubst.integral_mulVec | (intros; apply GlobalTheory.JacSubst.integral_mulVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMemIffUnipotentRadical
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.UnipMem

open GlobalTheory.LeviPlane Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.UnipMem
end
end
