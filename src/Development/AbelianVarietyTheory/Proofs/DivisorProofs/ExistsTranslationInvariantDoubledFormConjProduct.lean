module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantDoubledFormConjProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFormBoxStarNeZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

namespace GlobalTheory.DiagSq

open GlobalTheory.DiagForm
open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

instance mu_openPos : (mu F κ).IsOpenPosMeasure := by unfold mu; infer_instance

theorem pureA_glue (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (p : Vi F κ × Vf F κ) : pureA F f g (glue p) = f (eI F κ p.1) * g p.2 := by
  change f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (glue p i).1) * g (fun i => (glue p i).2) = _
  congr 2
  · funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem continuous_glue {φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hφ : φ ∈ schA F κ) :
    Continuous fun p : Vi F κ × Vf F κ => φ (glue p) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    simp only [pureA_glue]
    exact (f.continuous.comp ((eI F κ).continuous.comp continuous_fst)).mul (hg.1.continuous.comp continuous_snd)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact continuous_const.mul hx

theorem glue_shiftOf (x : κ → AF F) : glue (shiftOf x) = x := by
  have h := glue_add_shiftOf (0 : Vi F κ × Vf F κ) x
  rw [zero_add] at h
  rw [h]
  have h0 : glue (0 : Vi F κ × Vf F κ) = 0 := by
    funext i
    refine Prod.ext ?_ ?_
    · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ 0 i) = 0
      rw [map_zero]
      exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
    · rfl
  rw [h0, zero_add]

theorem lDiag_boxFun_star_ne : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : (κ → AF F) → ℂ),
    φ ∈ schA F κ → φ ≠ 0 → GlobalTheory.DiagForm.lDiag F κ (boxFun φ (star φ)) ≠ 0 := by
  intro F _ _ κ _ φ hφ hne
  have hs : star φ ∈ schA F κ := GlobalTheory.SchAConj.star_mem_schA F κ φ hφ
  have hb := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ φ hφ (star φ) hs
  have hi := integrable_resD hb
  have e : resD F κ (boxFun φ (star φ)) = fun p => ((Complex.normSq (φ (glue p)) : ℝ) : ℂ) := by
    funext p
    show φ (Sum.elim (glue p) (glue p) ∘ Sum.inl) * star φ (Sum.elim (glue p) (glue p) ∘ Sum.inr) = _
    rw [Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.star_apply, Complex.star_def, Complex.mul_conj]
  rw [lDiag, LinearMap.comp_apply, Lext_apply _ hi, e, integral_complex_ofReal, Complex.ofReal_ne_zero]
  rw [e] at hi
  have hr : Integrable (fun p => Complex.normSq (φ (glue p))) (mu F κ) := by
    simpa using hi.re
  have hc : Continuous fun p => Complex.normSq (φ (glue p)) :=
    Complex.continuous_normSq.comp (continuous_glue hφ)
  obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  refine ((integral_pos_iff_support_of_nonneg (fun p => Complex.normSq_nonneg _) hr).2 ?_).ne'
  refine hc.isOpen_support.measure_pos _ ⟨shiftOf x, ?_⟩
  rw [Function.mem_support, glue_shiftOf]
  exact (Complex.normSq_pos.2 hx).ne'

end GlobalTheory.DiagSq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantDoubledFormConjProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblDiagForm

open MeasureTheory GlobalTheory.DiagForm

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

local instance measAfD {F : Type} [Field F] [NumberField F] : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
local instance borelAfD {F : Type} [Field F] [NumberField F] : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩

theorem lDiag_translate {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {φ : (κ ⊕ κ → AF F) → ℂ} (hφ : φ ∈ schA F (κ ⊕ κ)) (φ' : (κ ⊕ κ → AF F) → ℂ) (x : κ → AF F)
    (h : ∀ u, φ' (Sum.elim u u) = φ (Sum.elim (u + x) (u + x))) : lDiag F κ φ' = lDiag F κ φ := by
  have hi := integrable_resD hφ
  have e : resD F κ φ' = fun p => resD F κ φ (p + shiftOf x) := by
    funext p
    show φ' (Sum.elim (glue p) (glue p)) = φ (Sum.elim (glue (p + shiftOf x)) (glue (p + shiftOf x)))
    rw [h, glue_add_shiftOf]
  rw [lDiag, LinearMap.comp_apply, LinearMap.comp_apply, e,
    Lext_apply _ (hi.comp_add_right (shiftOf x)), Lext_apply _ hi]
  exact integral_add_right_eq_self _ _

theorem exists_form : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Ψ ∈ schA F κ, Ψ ≠ 0 →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ φ ∈ schA F (κ ⊕ κ), ∀ (φ' : (κ ⊕ κ → AF F) → ℂ) (x : κ → AF F),
      (∀ u, φ' (Sum.elim u u) = φ (Sum.elim (u + x) (u + x))) → l φ' = l φ) ∧ l (GlobalTheory.InertDbl.dblFun Ψ) ≠ 0 := by
  intro F _ _ κ _ Ψ hΨ hne
  exact ⟨lDiag F κ, lDiag_adm, fun φ hφ φ' x h => lDiag_translate hφ φ' x h,
    GlobalTheory.DiagSq.lDiag_boxFun_star_ne F κ Ψ hΨ hne⟩

end GlobalTheory.DblDiagForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantDoubledFormConjProductStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translationInvariant_doubledForm_conjProduct_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Ψ ∈ schA F κ, Ψ ≠ 0 →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ φ ∈ schA F (κ ⊕ κ), ∀ (φ' : (κ ⊕ κ → AF F) → ℂ) (x : κ → AF F),
      (∀ u, φ' (Sum.elim u u) = φ (Sum.elim (u + x) (u + x))) → l φ' = l φ) ∧ l (GlobalTheory.InertDbl.dblFun Ψ) ≠ 0 := by
  first | exact @GlobalTheory.DblDiagForm.exists_form | exact GlobalTheory.DblDiagForm.exists_form | (intros; apply GlobalTheory.DblDiagForm.exists_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecMemThetaSpace
noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.CosetTheta

variable {D : D7}

theorem conj_ne_bot {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) : D.host.conj • 𝔪 ≠ ⊥ := by
  intro h
  apply h𝔪
  have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h
  simpa [inv_smul_smul] using this

theorem mul_mem_one {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {y : D.host.E}
    (hy : y ∈ (((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) :
    ((Ideal.absNorm (D.host.conj • 𝔪) : ℕ) : D.host.E) * y ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  have hJ : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (conj_ne_bot h𝔪)
  rw [FractionalIdeal.coe_div hJ, Submodule.mem_div_iff_forall_mul_mem] at hy
  have hn : ((Ideal.absNorm (D.host.conj • 𝔪) : ℕ) : D.host.E) ∈
      ((((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) :
        Submodule (𝓞 D.host.E) D.host.E) := by
    rw [FractionalIdeal.coe_coeIdeal, IsLocalization.mem_coeSubmodule]
    exact ⟨_, Ideal.absNorm_mem _, by simp⟩
  have h2 := hy _ hn
  rw [FractionalIdeal.coe_coeIdeal, IsLocalization.mem_coeSubmodule] at h2
  obtain ⟨z, -, hz⟩ := h2
  rw [Submodule.mem_one]
  exact ⟨z, by rw [hz, mul_comm]⟩

theorem nsmul_mem_homL {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {a d : ℕ} {A : Matrix (Fin d) (Fin a) D.host.E}
    (hA : A ∈ homL D (stdL D a) (skewLat D 𝔪 d)) :
    Ideal.absNorm (D.host.conj • 𝔪) • A ∈ homL D (stdL D a) (stdL D d) := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    apply Submodule.subset_span
    intro x hx
    have h := hA x hx
    rw [skewLat, Submodule.mem_pi] at h
    rw [stdL, Submodule.mem_pi]
    intro i _
    rw [Matrix.smul_mulVec, Pi.smul_apply, nsmul_eq_mul]
    exact mul_mem_one h𝔪 (h i trivial)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem nsmul_mem_YYl {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {a d : ℕ} {B : Matrix (Fin d) (Fin a) D.host.E}
    (hB : B ∈ YYl D (stdL D a) (skewLat D 𝔪 d)) :
    Ideal.absNorm (D.host.conj • 𝔪) • B ∈ YYl D (stdL D a) (stdL D d) := by
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨c, hc, A, hA, rfl⟩ := hB
    apply Submodule.subset_span
    exact ⟨c, hc, _, nsmul_mem_homL h𝔪 hA, smul_comm _ _ _⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem absNormConj_smul_mem_stdThetaLattice {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {a d : ℕ}
    {x : VC D a d} (hx : x ∈ La D (tor0 D cc δ) (stdL D a) (skewLat D 𝔪 d)) :
    Ideal.absNorm (D.host.conj • 𝔪) • x ∈ La0 D (tor0 D cc δ) a d := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    apply AddSubgroup.subset_closure
    refine ⟨w, hw, _, nsmul_mem_YYl h𝔪 hA, ?_⟩
    funext τ i j
    simp only [embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
    ring
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem u_mem_TT {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ} {x : VC D N N'} {M : ℕ}
    (hM : 0 < M) (hx : M • x ∈ La0 D (tor0 D cc δ) N N') {F : VC D N N' → ℂ} (hF : F ∈ TT D (tor0 D cc δ) N N') :
    U D (tor0 D cc δ) x F ∈ TT D (tor0 D cc δ) N N' := by
  have hw : wdPh D (tor0 D cc δ) x ≠ 0 := by simp [wdPh, ee, Complex.exp_ne_zero]
  have e : U D (tor0 D cc δ) x F = (wdPh D (tor0 D cc δ) x)⁻¹ • Wd D (tor0 D cc δ) x F := by
    funext z
    simp only [Wd, Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_cancel_left₀ hw]
  rw [e]
  exact NormUniq.tt_smul (GlobalTheory.T.thetaFunction_rationalTranslate_mem hc hM hx hF) _

theorem iop_mem_TT {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ} {La₂ : AddSubgroup (VC D N N')}
    {M : ℕ} (hM : 0 < M) (hLa : ∀ x ∈ La₂, M • x ∈ La0 D (tor0 D cc δ) N N') {F : VC D N N' → ℂ}
    (hF : F ∈ TT D (tor0 D cc δ) N N') :
    Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') La₂ F ∈ TT D (tor0 D cc δ) N N' := by
  classical
  by_cases h : ((La0 D (tor0 D cc δ) N N').addSubgroupOf La₂).index = 0
  · have e : Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') La₂ F = 0 := by
      funext z
      simp [Iop, h]
    rw [e]
    exact NormUniq.tt_zero _
  · have : ((La0 D (tor0 D cc δ) N N').addSubgroupOf La₂).FiniteIndex := ⟨h⟩
    haveI : Fintype (La₂ ⧸ (La0 D (tor0 D cc δ) N N').addSubgroupOf La₂) := Fintype.ofFinite _
    have e : Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') La₂ F =
        ((Real.sqrt (((La0 D (tor0 D cc δ) N N').addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) •
          ∑ q : La₂ ⧸ (La0 D (tor0 D cc δ) N N').addSubgroupOf La₂,
            al D (tor0 D cc δ) ((Quotient.out q : La₂) : VC D N N') •
              U D (tor0 D cc δ) ((Quotient.out q : La₂) : VC D N N') F := by
      funext z
      simp only [Iop, finsum_eq_sum_of_fintype, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [e]
    exact NormUniq.tt_smul (NormUniq.tt_sum _ fun q _ =>
      NormUniq.tt_smul (u_mem_TT hc hM (hLa _ (Quotient.out q : La₂).2) hF) _) _

theorem cosetVec_mem_TT : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ →
    ∀ o : ℕ, cosetVec P 𝔪 o ∈ TT D (tor0 D ⊤ δ) P.a P.d := by
  intro D δ t0 Q P 𝔪 h𝔪 o
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have he : P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d := VacMove.vac_TT h1 P.crv P.vac.1
  have hM : 0 < Ideal.absNorm (D.host.conj • 𝔪) :=
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact conj_ne_bot h𝔪)
  have hI := iop_mem_TT P.crv hM (fun x hx => absNormConj_smul_mem_stdThetaLattice h𝔪 hx) he
  unfold cosetVec
  exact NormUniq.tt_smul (GlobalTheory.T.thetaFunction_rationalTranslate_mem P.crv one_pos
    (by rw [one_smul]; exact pt_unitBlock_mem δ o P.a P.d) hI) _

end GlobalTheory.FunObj.CosetTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawOneSourceOrthogonalSumTargets
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawOneSourceOrthogonalSumTargets
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SeesawSumTarget

variable {D : D7}

theorem isHeckeChar_mul {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) :
    IsHeckeChar D (χ * η) := by
  refine ⟨?_, fun x => ?_⟩
  · have : ((χ * η : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => χ x * η x := by
      funext x; simp
    rw [this]
    exact hχ.1.mul hη.1
  · simp only [MonoidHom.mul_apply, hχ.2 x, hη.2 x, mul_one]

theorem exists_scalar {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT χS' χT' : (AE D)ˣ →* Circle}
    {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS' χT' om') (p : GA D S × GA D T) :
    ∃ c : Circle, ∀ f, IsThetaFunO ψ S T f → om p f = (c : ℂ) • om' p f := by
  obtain ⟨c, hc, h⟩ := GlobalTheory.T.schurLemma_thetaFunctions_orientedPair D ψ H.std S T (om' p⁻¹ * om p)
    (fun f hf => H'.om_pres _ _ (H.om_pres _ _ hf))
    (fun w f hf => by
      obtain ⟨g, h⟩ := p
      have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ w
      rw [inv_inv, inv_inv] at e
      rw [Module.End.mul_apply, Module.End.mul_apply, H.om_heis g h w f hf, Prod.inv_mk,
        H'.om_heis _ _ _ _ (H.om_pres _ _ hf), e])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, H'.om_unit μ 𝓕 hμ h𝓕 _ _ (H.om_pres _ _ hf), H.om_unit μ 𝓕 hμ h𝓕 _ _ hf])
  refine ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, fun f hf => ?_⟩
  have := congrArg (om' p) (h f hf)
  rwa [Module.End.mul_apply, GlobalTheory.WeilUniq.om_om_inv, map_smul] at this

section Std
open GlobalTheory.MixModel

theorem qA_sumDec (A B : HSp D) :
    (GlobalTheory.BiTransfer.sumDec A B).qA = (fromCols (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) 0).submatrix id finSumFinEquiv.symm := by
  rw [OrthDec.qA, GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat]
  simp only [GlobalTheory.BiTransfer.sumDec, Matrix.conjTranspose_submatrix, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    conjTranspose_one, conjTranspose_zero, Matrix.submatrix_mul_equiv, fromCols_mul_fromBlocks]
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  ext i j
  simp only [Matrix.mul_apply, submatrix_apply, id]
  rcases finSumFinEquiv.symm j with k | k
  · simp only [fromCols_apply_inl]
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det A)]
  · simp only [fromCols_apply_inr, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]

theorem qB_sumDec (A B : HSp D) :
    (GlobalTheory.BiTransfer.sumDec A B).qB = (fromCols (0 : Matrix (Fin B.rank) (Fin A.rank) D.host.E) 1).submatrix id finSumFinEquiv.symm := by
  rw [OrthDec.qB, GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat]
  simp only [GlobalTheory.BiTransfer.sumDec, Matrix.conjTranspose_submatrix, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    conjTranspose_one, conjTranspose_zero, Matrix.submatrix_mul_equiv, fromCols_mul_fromBlocks]
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  ext i j
  simp only [Matrix.mul_apply, submatrix_apply, id]
  rcases finSumFinEquiv.symm j with k | k
  · simp only [fromCols_apply_inl, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]
  · simp only [fromCols_apply_inr]
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det B)]

theorem pA_sumDec {S A B : HSp D} (x : WO S (GlobalTheory.Doubling.hsum A B)) :
    (GlobalTheory.BiTransfer.sumDec A B).pA ⬝ x = topR (A := A) (B := B) x := by
  ext i j
  simp only [OrthDec.pA, rat, qA_sumDec, Matrix.mul_apply, Matrix.map_apply, submatrix_apply, id, Fin.sum_univ_add,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inl, fromCols_apply_inr,
    Matrix.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, add_zero, Matrix.one_apply, topR]
  simp [apply_ite (incA D)]

theorem pB_sumDec {S A B : HSp D} (x : WO S (GlobalTheory.Doubling.hsum A B)) :
    (GlobalTheory.BiTransfer.sumDec A B).pB ⬝ x = botR (A := A) (B := B) x := by
  ext i j
  simp only [OrthDec.pB, rat, qB_sumDec, Matrix.mul_apply, Matrix.map_apply, submatrix_apply, id, Fin.sum_univ_add,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inl, fromCols_apply_inr,
    Matrix.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, zero_add, Matrix.one_apply, botR]
  simp [apply_ite (incA D)]

theorem boxT_sumDec (S A B : HSp D) (φ : WO S A → ℂ) (φ' : WO S B → ℂ) :
    (GlobalTheory.BiTransfer.sumDec A B).boxT S φ φ' = box2 φ φ' := by
  funext x
  simp only [OrthDec.boxT, OrthDec.resT_apply, box2]
  rw [pA_sumDec, pB_sumDec]

theorem emb_sumDec (A B : HSp D) (g : GA D A) (g₁ : GA D B) :
    (GlobalTheory.BiTransfer.sumDec A B).emb (g, g₁) = GlobalTheory.SquareComm.blk A B (g, g₁) := by
  apply GlobalTheory.MixModel.mt_injective (GlobalTheory.Doubling.hsum A B)
  rw [(GlobalTheory.BiTransfer.sumDec A B).mt_emb, GlobalTheory.SquareComm.mt_blk]
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective j
  simp only [GlobalTheory.Doubling.blkMat, submatrix_apply, Equiv.symm_apply_apply, Matrix.add_apply, Matrix.mul_apply,
    OrthDec.jA, OrthDec.jB, OrthDec.pA, OrthDec.pB, rat, qA_sumDec, qB_sumDec, Matrix.map_apply, id]
  simp only [GlobalTheory.BiTransfer.sumDec, submatrix_apply, Equiv.symm_apply_apply, id]
  rcases s with s | s <;> rcases t with t | t <;>
    simp [Matrix.one_apply, apply_ite (incA D), ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

end Std

theorem seesaw_sum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B : HSp D) (χ₁ χ₁' χ₂ χ₂' : (AE D)ˣ →* Circle)
    (ω₁ : GA D S × GA D A →* Module.End ℂ (WO S A → ℂ)) (ω₂ : GA D S × GA D B →* Module.End ℂ (WO S B → ℂ)),
    IsWeilDatumO ψ S A χ₁ χ₁' ω₁ → IsWeilDatumO ψ S B χ₂ χ₂' ω₂ →
    ∃ (ω : GA D S × GA D (GlobalTheory.Doubling.hsum A B) →* Module.End ℂ (WO S (GlobalTheory.Doubling.hsum A B) → ℂ))
      (χ χ' : (AE D)ˣ →* Circle) (c : GA D S → GA D A → GA D B → ℂ),
      IsWeilDatumO ψ S (GlobalTheory.Doubling.hsum A B) χ χ' ω ∧ (∀ u g g₁, ‖c u g g₁‖ = 1) ∧
      ∀ φ φ', IsThetaFunO ψ S A φ → IsThetaFunO ψ S B φ' → IsThetaFunO ψ S (GlobalTheory.Doubling.hsum A B) (box2 φ φ') ∧
        ∀ u g g₁, thetaKO ω u (GlobalTheory.SquareComm.blk A B (g, g₁)) (box2 φ φ') =
          c u g g₁ * (thetaKO ω₁ u g φ * thetaKO ω₂ u g₁ φ') := by
  intro D ψ hψ S A B χ₁ χ₁' χ₂ χ₂' ω₁ ω₂ H₁ H₂
  have hη := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨ω₂', H₂'⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S B χ₁ χ₂' hη H₁.hecS H₂.hecT H₁.resS H₂.resT
  obtain ⟨ω, H⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S (GlobalTheory.Doubling.hsum A B) χ₁ (χ₁' * χ₂') hη H₁.hecS
    (isHeckeChar_mul H₁.hecT H₂.hecT) H₁.resS (resEta_mul H₁.resT H₂.resT)
  choose c hc using fun p => exists_scalar H₂' H₂ p
  refine ⟨ω, χ₁, χ₁' * χ₂', fun u _ g₁ => (c (u, g₁) : ℂ), H, fun u _ g₁ => Circle.norm_coe _,
    fun φ φ' hφ hφ' => ⟨?_, fun u g g₁ => ?_⟩⟩
  · rw [← boxT_sumDec]
    exact (GlobalTheory.BiTransfer.sumDec A B).isThetaFunO_boxT hφ hφ'
  · have key := (GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ _ A B (GlobalTheory.BiTransfer.sumDec A B) S).om_box χ₁ χ₁' χ₂' ω ω₁
      ω₂' H H₁ H₂' u g g₁ φ φ' hφ hφ'
    simp only [thetaKO]
    rw [← emb_sumDec, ← boxT_sumDec, key, GlobalTheory.MixModel.OrthDec.boxT_zero, hc (u, g₁) φ' hφ', Pi.smul_apply, smul_eq_mul]
    ring

end GlobalTheory.SeesawSumTarget
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawOneSourceOrthogonalSumTargetsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_oneSource_orthogonalSumTargets : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B : HSp D) (χ₁ χ₁' χ₂ χ₂' : (AE D)ˣ →* Circle)
    (ω₁ : GA D S × GA D A →* Module.End ℂ (WO S A → ℂ)) (ω₂ : GA D S × GA D B →* Module.End ℂ (WO S B → ℂ)),
    IsWeilDatumO ψ S A χ₁ χ₁' ω₁ → IsWeilDatumO ψ S B χ₂ χ₂' ω₂ →
    ∃ (ω : GA D S × GA D (GlobalTheory.Doubling.hsum A B) →* Module.End ℂ (WO S (GlobalTheory.Doubling.hsum A B) → ℂ))
      (χ χ' : (AE D)ˣ →* Circle) (c : GA D S → GA D A → GA D B → ℂ),
      IsWeilDatumO ψ S (GlobalTheory.Doubling.hsum A B) χ χ' ω ∧ (∀ u g g₁, ‖c u g g₁‖ = 1) ∧
      ∀ φ φ', IsThetaFunO ψ S A φ → IsThetaFunO ψ S B φ' → IsThetaFunO ψ S (GlobalTheory.Doubling.hsum A B) (box2 φ φ') ∧
        ∀ u g g₁, thetaKO ω u (GlobalTheory.SquareComm.blk A B (g, g₁)) (box2 φ φ') =
          c u g g₁ * (thetaKO ω₁ u g φ * thetaKO ω₂ u g₁ φ') := by
  first | exact @GlobalTheory.SeesawSumTarget.seesaw_sum | exact GlobalTheory.SeesawSumTarget.seesaw_sum | (intros; apply GlobalTheory.SeesawSumTarget.seesaw_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedGLMassFormula
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MassNorm

open GlobalTheory.ClassParam (krylov)

section Core

variable {R : Type} [CommRing R] {m : ℕ}

theorem aeval_of_commute_cyclic {M N : Matrix (Fin m) (Fin m) R} (v : Fin m → R) (hv : IsUnit (krylov M v).det)
    (h : Commute N M) : ∃ p : R[X], N = aeval M p := by
  let a := (krylov M v)⁻¹ *ᵥ (N *ᵥ v)
  let p : R[X] := ∑ j : Fin m, monomial (j : ℕ) (a j)
  have hp : aeval M p *ᵥ v = N *ᵥ v := by
    have : krylov M v *ᵥ a = N *ᵥ v := by rw [mulVec_mulVec, mul_nonsing_inv _ hv, one_mulVec]
    rw [← this]
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [p, krylov, map_sum, aeval_monomial, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.mulVec.eq_def (Matrix.of _), dotProduct, mul_comm]
  have hc : Commute (aeval M p) M := by
    have := congrArg (aeval M) (mul_comm p X)
    rwa [map_mul, map_mul, aeval_X] at this
  refine ⟨p, ((isUnit_iff_isUnit_det _).2 hv).mul_right_cancel ?_⟩
  rw [GlobalTheory.Orb.mul_krylov_of_commute h, GlobalTheory.Orb.mul_krylov_of_commute hc, hp]

def psi (c : R →+* R) (D : GL (Fin m) R) (x : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m) R :=
  D.val * GlobalTheory.Tw.Phi m R * (c.mapMatrix x)ᵀ * (GlobalTheory.Tw.Phi m R)ᵀ * (D⁻¹).val

theorem PhiT_mul_Phi : (GlobalTheory.Tw.Phi m R)ᵀ * GlobalTheory.Tw.Phi m R = 1 := mul_eq_one_comm.1 (Phi_mul_transpose m R)

theorem psi_mul (c : R →+* R) (D : GL (Fin m) R) (x y : Matrix (Fin m) (Fin m) R) :
    psi c D (x * y) = psi c D y * psi c D x := by
  have h1 : (D⁻¹).val * D.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [psi, map_mul, Matrix.transpose_mul]
  calc _ = D.val * GlobalTheory.Tw.Phi m R * (c.mapMatrix y)ᵀ * ((GlobalTheory.Tw.Phi m R)ᵀ * ((D⁻¹).val * D.val) * GlobalTheory.Tw.Phi m R) *
        (c.mapMatrix x)ᵀ * (GlobalTheory.Tw.Phi m R)ᵀ * (D⁻¹).val := by
        rw [h1, Matrix.mul_one, PhiT_mul_Phi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem psi_add (c : R →+* R) (D : GL (Fin m) R) (x y : Matrix (Fin m) (Fin m) R) :
    psi c D (x + y) = psi c D x + psi c D y := by
  simp only [psi, map_add (f := _), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem psi_smul (c : R →+* R) (D : GL (Fin m) R) (r : R) (x : Matrix (Fin m) (Fin m) R) :
    psi c D (r • x) = c r • psi c D x := by
  have : c.mapMatrix (r • x) = c r • c.mapMatrix x := by ext i j; simp
  simp only [psi, this, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem psi_one (c : R →+* R) (D : GL (Fin m) R) : psi c D 1 = 1 := by
  simp only [psi, map_one, Matrix.transpose_one, Matrix.mul_one]
  rw [Matrix.mul_assoc D.val, Phi_mul_transpose, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem psi_pow (c : R →+* R) (D : GL (Fin m) R) (x : Matrix (Fin m) (Fin m) R) (k : ℕ) :
    psi c D (x ^ k) = psi c D x ^ k := by
  induction k with
  | zero => simp [psi_one]
  | succ k ih => rw [pow_succ, psi_mul, ih, pow_succ']

theorem psi_aeval (c : R →+* R) (D : GL (Fin m) R) (x : Matrix (Fin m) (Fin m) R) (p : R[X]) :
    psi c D (aeval x p) = aeval (psi c D x) (p.map c) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), psi_add, hp, hq, Polynomial.map_add (f := _), map_add (f := _)]
  | monomial k r =>
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul, psi_smul, psi_pow, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem psi_units (c : R →+* R) (D h : GL (Fin m) R) :
    psi c D h.val = (D * thetaGL m c h⁻¹ * D⁻¹).val := by
  rw [Units.val_mul, Units.val_mul, GlobalTheory.LocTwist.thetaGL_val, inv_inv]
  simp only [psi, Matrix.mul_assoc]

theorem twCent_le (c : R →+* R) (hc : ∀ x, c (c x) = x) (D₁ D₂ : GL (Fin m) R)
    (hN : D₁ * thetaGL m c D₁ = D₂ * thetaGL m c D₂) (v : Fin m → R)
    (hv : IsUnit (krylov (D₁ * thetaGL m c D₁).val v).det) :
    twCent (thetaGL m c) D₁ ≤ twCent (thetaGL m c) D₂ := by
  have hθ : ∀ g, thetaGL m c (thetaGL m c g) = g := GlobalTheory.LocTwist.thetaGL_thetaGL m c hc
  have hpsiN : ∀ D : GL (Fin m) R, psi c D (D * thetaGL m c D).val = ((D * thetaGL m c D)⁻¹).val := by
    intro D
    rw [psi_units]
    congr 1
    simp only [_root_.mul_inv_rev, map_mul, map_inv, hθ]
    group
  have hmem : ∀ (D g : GL (Fin m) R), g ∈ twCent (thetaGL m c) D ↔ psi c D g.val = (g⁻¹).val := by
    intro D g
    rw [psi_units]
    constructor
    · intro h
      have h' : g⁻¹ * D = D * thetaGL m c g⁻¹ := (twCent (thetaGL m c) D).inv_mem h
      congr 1
      rw [← h']; group
    · intro h
      have h' : D * thetaGL m c g⁻¹ * D⁻¹ = g⁻¹ := Units.ext h
      have : g⁻¹ ∈ twCent (thetaGL m c) D := by
        change g⁻¹ * D = D * thetaGL m c g⁻¹
        calc g⁻¹ * D = (D * thetaGL m c g⁻¹ * D⁻¹) * D := by rw [h']
          _ = _ := by group
      simpa using (twCent (thetaGL m c) D).inv_mem this
  intro g hg
  have hcomm : g * (D₁ * thetaGL m c D₁) = (D₁ * thetaGL m c D₁) * g := by
    have h1 : g * D₁ = D₁ * thetaGL m c g := hg
    have h2 : thetaGL m c g = D₁⁻¹ * g * D₁ := by rw [mul_assoc, h1]; group
    have h3 := congrArg (thetaGL m c) h2
    rw [hθ, map_mul, map_mul, map_inv, h2] at h3
    calc g * (D₁ * thetaGL m c D₁)
        = (D₁ * thetaGL m c D₁) * ((thetaGL m c D₁)⁻¹ * (D₁⁻¹ * g * D₁) * thetaGL m c D₁) := by group
      _ = _ := by rw [← h3]
  obtain ⟨p, hp⟩ := aeval_of_commute_cyclic v hv (N := g.val) (by
    change g.val * (D₁ * thetaGL m c D₁).val = (D₁ * thetaGL m c D₁).val * g.val
    rw [← Units.val_mul, ← Units.val_mul, hcomm])
  have e1 := psi_aeval c D₁ (D₁ * thetaGL m c D₁).val p
  rw [hpsiN] at e1
  have e2 := psi_aeval c D₂ (D₂ * thetaGL m c D₂).val p
  rw [hpsiN, ← hN] at e2
  rw [hmem] at hg ⊢
  rw [← hg, hp, e1, e2]

end Core

section Global

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem thF_ratF (m : ℕ) (g : GL (Fin m) E) : thF E m (ratF E m g) = ratF E m (thE E m g) :=
  (GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (Af E)) _ _
    (fun x => (conjFin_algebraMap (IsCMField.complexConj E).toRingEquiv x).symm) g).symm

theorem isClosed_twCent_thF (m : ℕ) (δ : GL (Fin m) (Af E)) : IsClosed (twCent (thF E m) δ : Set (GL (Fin m) (Af E))) := by
  have e : (twCent (thF E m) δ : Set (GL (Fin m) (Af E))) = {g | (g * δ).val = (δ * thF E m g).val} := by
    ext g; exact Units.ext_iff
  rw [e]
  haveI : T2Space (Af E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  exact isClosed_eq (Units.continuous_val.comp (continuous_id.mul continuous_const))
    (Units.continuous_val.comp (continuous_const.mul (GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _))))

theorem mass_eq_of_charpoly (m : ℕ) (δ₁ δ₂ : GL (Fin m) E)
    (h : (δ₂ * thE E m δ₂).val.charpoly = (δ₁ * thE E m δ₁).val.charpoly)
    (hs : (δ₁ * thE E m δ₁).val.charpoly.Separable) :
    mass (thF E m) (ratF E m).range (ratF E m δ₂) = mass (thF E m) (ratF E m).range (ratF E m δ₁) := by
  have hθE : ∀ g, thE E m (thE E m g) = g :=
    GlobalTheory.ThetaPull.thetaGL_thetaGL _ (fun x => IsCMField.complexConj_apply_apply E x)
  obtain ⟨x, hx⟩ := GlobalTheory.Orb.IsRegSS.exists_conj (A := E) (M := (δ₁ * thE E m δ₁).val) hs h
  have hx' : (δ₂ * thE E m δ₂) * x = x * (δ₁ * thE E m δ₁) := Units.ext hx
  have hu : (x⁻¹ * δ₂ * thE E m x) * thE E m (x⁻¹ * δ₂ * thE E m x) = δ₁ * thE E m δ₁ := by
    simp only [map_mul, map_inv, hθE]
    calc _ = x⁻¹ * ((δ₂ * thE E m δ₂) * x) := by group
      _ = _ := by rw [hx']; group
  have hc : ∀ y, conjFin (IsCMField.complexConj E).toRingEquiv (conjFin (IsCMField.complexConj E).toRingEquiv y) = y :=
    fun y => GlobalTheory.ThetaPull.cFin_cFin y
  have hN : ratF E m δ₁ * thF E m (ratF E m δ₁) =
      ratF E m (x⁻¹ * δ₂ * thE E m x) * thF E m (ratF E m (x⁻¹ * δ₂ * thE E m x)) := by
    rw [thF_ratF, thF_ratF, ← map_mul, ← map_mul, hu]
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field _ hs
  have hv' : IsUnit (GlobalTheory.ClassParam.krylov (ratF E m δ₁ * thF E m (ratF E m δ₁)).val (algebraMap E (Af E) ∘ v)).det := by
    have h1 := (IsUnit.mk0 _ hv).map (algebraMap E (Af E))
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.ClassParam.krylov_map] at h1
    rw [thF_ratF, ← map_mul]
    exact h1
  have heq : twCent (thF E m) (ratF E m δ₁) = twCent (thF E m) (ratF E m (x⁻¹ * δ₂ * thE E m x)) :=
    le_antisymm (twCent_le _ hc _ _ hN _ hv') (twCent_le _ hc _ _ hN.symm _ (hN ▸ hv'))
  set y := ratF E m x with hy
  have hconj : ratF E m (x⁻¹ * δ₂ * thE E m x) = y⁻¹ * ratF E m δ₂ * thF E m y := by
    rw [hy, thF_ratF, map_mul, map_mul, map_inv]
  have hT : twCent (thF E m) (ratF E m δ₁) = (twCent (thF E m) (ratF E m δ₂)).map (MulAut.conj y⁻¹).toMonoidHom := by
    rw [heq, hconj, GlobalTheory.TwOrbConj.twCent_conj]
  have hf : ∀ t : twCent (thF E m) (ratF E m δ₂), y⁻¹ * (t : GL (Fin m) (Af E)) * y ∈ twCent (thF E m) (ratF E m δ₁) := by
    intro t
    rw [hT]
    exact ⟨t, t.2, by simp [MulAut.conj_apply]⟩
  have hg : ∀ s : twCent (thF E m) (ratF E m δ₁), y * (s : GL (Fin m) (Af E)) * y⁻¹ ∈ twCent (thF E m) (ratF E m δ₂) := by
    intro s
    have hs' : (s : GL (Fin m) (Af E)) ∈ (twCent (thF E m) (ratF E m δ₂)).map (MulAut.conj y⁻¹).toMonoidHom :=
      hT ▸ s.2
    obtain ⟨t, ht, he⟩ := hs'
    have : (s : GL (Fin m) (Af E)) = y⁻¹ * t * y := by rw [← he]; simp [MulAut.conj_apply]
    rw [this]; simpa [mul_assoc] using ht
  let e : twCent (thF E m) (ratF E m δ₂) ≃ₜ* twCent (thF E m) (ratF E m δ₁) :=
    { toFun := fun t => ⟨y⁻¹ * t * y, hf t⟩
      invFun := fun s => ⟨y * s * y⁻¹, hg s⟩
      left_inv := fun t => Subtype.ext (by simp [mul_assoc])
      right_inv := fun s => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := Continuous.subtype_mk
        ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
      continuous_invFun := Continuous.subtype_mk
        ((continuous_const.mul continuous_subtype_val).mul continuous_const) _ }
  have hyΓ : y ∈ (ratF E m).range := ⟨x, rfl⟩
  refine GlobalTheory.T.twistedCentralizerMass_eq_of_topEquiv _ _ (thF E m) (thF E m) _ _ (ratF E m δ₂) (ratF E m δ₁) (isClosed_twCent_thF E m _)
    (isClosed_twCent_thF E m _) e fun t => ?_
  change (t : GL (Fin m) (Af E)) ∈ (ratF E m).range ↔ y⁻¹ * (t : GL (Fin m) (Af E)) * y ∈ (ratF E m).range
  rw [Subgroup.mul_mem_cancel_right _ hyΓ, Subgroup.mul_mem_cancel_left _ ((ratF E m).range.inv_mem hyΓ)]

end Global

end GlobalTheory.MassNorm

theorem GlobalTheory.BCT.mass_eq_kap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (δ : GL (Fin n) E), (δ * thE E n δ).val.charpoly ∈ Ell E n → mass (thF E n) (ratF E n).range (ratF E n δ) = kap (δ * thE E n δ).val.charpoly * 2 ^ nfac (δ * thE E n δ).val.charpoly := by
  intro E _ _ _ _ n δ hP
  have hd : (δ * thE E n δ).val.charpoly.natDegree = n := hP.2.1
  have hs : (δ * thE E n δ).val.charpoly.Separable := hP.2.2.1
  generalize hPdef : (δ * thE E n δ).val.charpoly = P at hd hs ⊢
  have hcast : ∀ (k : ℕ) (_ : k = n), (∃ δ' : GL (Fin k) E, (δ' * thE E k δ').val.charpoly = P) ∧
      ∀ δ' : GL (Fin k) E, (δ' * thE E k δ').val.charpoly = P →
        mass (thF E k) (ratF E k).range (ratF E k δ') = mass (thF E n) (ratF E n).range (ratF E n δ) := by
    intro k hk
    subst hk
    exact ⟨⟨δ, hPdef⟩, fun δ' h' => GlobalTheory.MassNorm.mass_eq_of_charpoly E k δ δ' (h'.trans hPdef.symm) (hPdef ▸ hs)⟩
  obtain ⟨hex, hm⟩ := hcast _ hd
  unfold GlobalTheory.BCT.kap GlobalTheory.BCT.nfac
  rw [dite_eq_left hex, hm _ hex.choose_spec, div_mul_cancel₀ _ (pow_ne_zero _ two_ne_zero)]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivative
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

open scoped TensorProduct Matrix ContDiff

namespace GlobalTheory.LineDerSum


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem skew_of_exp_unitary {n : ℕ} (A Z : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Z))ᴴ * A * NormedSpace.exp (t • Z) = A) : Zᴴ * A + A * Z = 0 := by
  have h1 : ∀ t : ℝ, (NormedSpace.exp (t • Z))ᴴ = NormedSpace.exp (t • Zᴴ) := fun t => by
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial]
  have hd := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) Zᴴ (0 : ℝ)).mul_const A).mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ))
  have he : ((fun t : ℝ => NormedSpace.exp (t • Zᴴ) * A) * fun t : ℝ => NormedSpace.exp (t • Z)) = fun _ => A :=
    funext fun t => by rw [Pi.mul_apply, ← h1, h]
  simpa using hd.unique ((hasDerivAt_const (0 : ℝ) A).congr_of_eventuallyEq (.of_forall (congrFun he)))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isRealLine_component (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (δ : ℝ → GAd σ J)
    (hc : Continuous δ) (h0 : δ 0 = 1) (hm : ∀ s t, δ (s + t) = δ s * δ t) (w : InfinitePlace F) :
    IsRealLine σ J fun t => embArch σ J w (projArch σ J w (δ t)) := by
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  obtain ⟨Z, hZ⟩ := GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter
    (fun t => GlobalTheory.Orb.archMat σ J τ (projArch σ J w (δ t)))
    ((GlobalTheory.Orb.continuous_archMat σ J τ).comp ((continuous_projArch σ J w).comp hc))
    (by simp only [h0, map_one]) (fun s t => by simp only [hm, map_mul])
  refine ⟨w, τ, Z, skew_of_exp_unitary _ _ fun t => ?_, fun t => ⟨_, rfl, hZ t⟩⟩
  rw [← hZ t, GlobalTheory.Orb.archMat_eq_archEquiv J hcm]
  exact (archEquiv J hcm τ _).2

end GlobalTheory.LineDerSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticGroupMatrixOfPreservesPhaseSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticGroupMatrixOfPreservesPhaseSpace
open scoped SchwartzMap Matrix

namespace GlobalTheory

open Matrix

theorem sympl_eq_neg_dotProduct_J {l : Type} [Fintype l] [DecidableEq l] (w w' : l ⊕ l → ℝ) :
    GlobalTheory.RealWeil.sympl w w' = -(w ⬝ᵥ (J l ℝ *ᵥ w')) := by
  simp only [GlobalTheory.RealWeil.sympl, GlobalTheory.RealWeil.pPart, GlobalTheory.RealWeil.qPart, J, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec, Matrix.one_apply, Finset.sum_neg_distrib, mul_comm, Matrix.neg_mulVec, Matrix.one_mulVec]
  ring

theorem exists_symplecticGroup_of_sympl (l : Type) [Fintype l] [DecidableEq l]
    (ψ : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (h : ∀ w w', GlobalTheory.RealWeil.sympl (ψ w) (ψ w') = GlobalTheory.RealWeil.sympl w w') :
    ∃ M : Matrix.symplecticGroup l ℝ, ∀ w, (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w = ψ w := by
  set M := LinearMap.toMatrix' ψ with hM
  have hMv : ∀ w, M *ᵥ w = ψ w := fun w => by rw [hM, LinearMap.toMatrix'_mulVec]
  have key : ∀ w w', w ⬝ᵥ ((Mᵀ * J l ℝ * M) *ᵥ w') = w ⬝ᵥ (J l ℝ *ᵥ w') := by
    intro w w'
    have := h w w'
    rw [sympl_eq_neg_dotProduct_J, sympl_eq_neg_dotProduct_J, ← hMv, ← hMv] at this
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    linarith
  have hmem : M ∈ Matrix.symplecticGroup l ℝ := by
    rw [SymplecticGroup.mem_iff']
    ext i j
    have := key (Pi.single i 1) (Pi.single j 1)
    simpa [single_dotProduct, mulVec_single] using this
  exact ⟨⟨M, hmem⟩, hMv⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticGroupMatrixOfPreservesPhaseSpaceStatement
open scoped SchwartzMap Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticGroup_matrix_of_preserves_phaseSpaceForm : ∀ (l : Type) [Fintype l] [DecidableEq l] (ψ : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ w w', GlobalTheory.RealWeil.sympl (ψ w) (ψ w') = GlobalTheory.RealWeil.sympl w w') →
    ∃ M : Matrix.symplecticGroup l ℝ, ∀ w, (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w = ψ w := by
  first | exact @GlobalTheory.exists_symplecticGroup_of_sympl | exact GlobalTheory.exists_symplecticGroup_of_sympl | (intros; apply GlobalTheory.exists_symplecticGroup_of_sympl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedIsAdmissible
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.SmGL.ParIndAdm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_finset_KO_cover (K : Subgroup (GL n k)) (hK : IsOpen (K : Set (GL n k))) :
    ∃ R : Finset (GL n k), ∀ w ∈ KO k n, ∃ r ∈ R, r⁻¹ * w ∈ K := by
  obtain ⟨R, hR⟩ := (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := n)).elim_finite_subcover
    (fun x : GL n k => (fun y => x⁻¹ * y) ⁻¹' (K : Set (GL n k)))
    (fun x => hK.preimage (by fun_prop))
    (fun w _ => Set.mem_iUnion.2 ⟨w, by simp [one_mem]⟩)
  refine ⟨R, fun w hw => ?_⟩
  obtain ⟨r, hr, h⟩ := Set.mem_iUnion₂.1 (hR hw)
  exact ⟨r, hr, h⟩

theorem eq_zero_of_fixed (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) (K : Subgroup (GL n k))
    (R : Finset (GL n k)) (hR : ∀ w ∈ KO k n, ∃ r ∈ R, r⁻¹ * w ∈ K)
    (f : IndSp e ρ) (hf : f ∈ fixed (parInd e ρ) K) (h0 : ∀ r ∈ R, f.1.1 r = 0) : f = 0 := by
  have hfix : ∀ κ ∈ K, ∀ x, f.1.1 (x * κ) = f.1.1 x := fun κ hκ x => by
    have := congrArg (fun φ : IndSp e ρ => φ.1.1 x) (hf ⟨κ, hκ⟩)
    simpa using this
  apply Subtype.ext; apply Subtype.ext; funext x
  obtain ⟨u, l, w, hw, rfl⟩ := UnitInd.exists_iwasawa e x
  obtain ⟨r, hr, hrw⟩ := hR w hw
  let p : parab k e := ⟨(u : GL n k) * leviEmb k e l,
    mul_mem (unipRad_le_parab k e u.2) (leviEmb_mem_parab k e l)⟩
  have hw' : f.1.1 w = 0 := by
    have := hfix _ hrw r
    rw [mul_inv_cancel_left] at this
    rw [this, h0 r hr]
  show f.1.1 ((p : GL n k) * w) = 0
  rw [parInd_law, hw', map_zero, smul_zero]

theorem isAdmissible_parInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W)
    [FiniteDimensional ℂ W] : IsAdmissible (parInd e ρ) := by
  refine ⟨isSmooth_parInd e ρ, fun K hKo _ => ?_⟩
  obtain ⟨R, hR⟩ := exists_finset_KO_cover K hKo
  let L : fixed (parInd e ρ) K →ₗ[ℂ] (R → W) :=
    { toFun := fun f r => f.1.1.1 r
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective L fun f g hfg => ?_
  rw [← sub_eq_zero]
  have h := eq_zero_of_fixed e ρ K R hR (f - g).1 (f - g).2 fun r hr => by
    have := congrFun hfg ⟨r, hr⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at this
    show f.1.1.1 r - g.1.1.1 r = 0
    rw [this, sub_self]
  exact Subtype.ext h

end GlobalTheory.SmGL.ParIndAdm

namespace GlobalTheory.ThK.MidJac

end GlobalTheory.ThK.MidJac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormMul
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

set_option autoImplicit false

open scoped ContDiff

namespace GlobalTheory.CxForm.FormMul

theorem isForm_mul : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α β : A.Fld),
    A.IsForm α → A.IsForm β → A.IsForm (α * β) := by
  intro M _ n A α β hα hβ
  refine ⟨fun i S => ?_, fun x x' h => ?_⟩
  · have e : (fun v => (bas n).repr (A.loc (α * β) i v) S) = fun v => ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)),
        (bas n).repr (A.loc α i v) p.1 * (bas n).repr (A.loc β i v) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S :=
      funext fun v => by rw [loc_mul, repr_mul]
    rw [e]
    exact ContDiffOn.sum fun p _ => ((hα.smooth i p.1).mul (hβ.smooth i p.2)).mul contDiffOn_const
  · show α x * β x = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (α x' * β x')
    rw [map_mul, ← hα.compat x x' h, ← hβ.compat x x' h]

end GlobalTheory.CxForm.FormMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankSumLeHalfRank
open GlobalTheory.SqTop

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest

namespace GlobalTheory.SqTop

theorem exists_coord_ne_of_norm_ne {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ}
    (P : GlobalTheory.NormSum.Pair D cc δ t0 Q) (h : P.norm ≠ 0) : ∃ g T, P.coord g T ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  simp [GlobalTheory.NormSum.Pair.norm, GlobalTheory.NormSum.Pair.sq, hc]

theorem squareBottomHalfRankSum_le_halfRank (D : D7) (i j : ℕ) : h0 D i j ≤ halfRank D i j := by
  simp only [h0, botBig, botSmall, halfRank]
  omega

end GlobalTheory.SqTop

end
end
