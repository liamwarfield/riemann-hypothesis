module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.LatticeAndConstantUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitution
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitution
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem om_rat_mul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S T), IsWeilDatumO ψ S T χ χ' om → ∀ f, IsThetaFunO ψ S T f → ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ g h w, om (γ * g, γ' * h) f w = om (g, h) f (mt T γ'⁻¹ * w * mt S γ) := by
  intro D ψ S T χ χ' om H f hf γ hγ γ' hγ' g h w
  have h1 := GlobalTheory.WeilRat.om_rat_actO D ψ H.std S T χ χ' om H γ hγ γ' hγ' _ (H.om_pres (g, h) f hf)
    (mt T γ'⁻¹ * w * mt S γ)
  have h2 : actO S T γ γ' (mt T γ'⁻¹ * w * mt S γ) = w := by
    change mt T γ' * (mt T γ'⁻¹ * w * mt S γ) * mt S γ⁻¹ = w
    rw [Matrix.mul_assoc, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, mt_mul_inv,
      Matrix.one_mul]
  rw [h2] at h1
  rw [← h1, ← Prod.mk_mul_mk, map_mul, mul_apply_eq_comp]

end GlobalTheory.Unf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitutionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_rational_translate_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S T), IsWeilDatumO ψ S T χ χ' om → ∀ f, IsThetaFunO ψ S T f → ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ g h w, om (γ * g, γ' * h) f w = om (g, h) f (mt T γ'⁻¹ ⬝ w ⬝ mt S γ) := by
  first | exact @GlobalTheory.Unf.om_rat_mul | exact GlobalTheory.Unf.om_rat_mul | (intros; apply GlobalTheory.Unf.om_rat_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
open IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.AeUnit

theorem idem_mul_finPart (D : D7) (v : Pl D) {a : AE D} (ha : a ∈ idAt D (· = v)) :
    (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D a = finPart D a := by
  refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun w => ?_
  rw [map_mul, Algebra.TensorProduct.map_tmul]
  by_cases hw : w = v
  · subst hw
    rw [GlobalTheory.LatVac.evalV_singleV_same, map_one, ← Algebra.TensorProduct.one_def, one_mul]
  · have h0 : GlobalTheory.FinPl.compAt D w a = 0 := (Submodule.mem_iInf _).1 ha.2 ⟨w, hw⟩
    have h1 : Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E) (finPart D a) = 0 := h0
    rw [h1, mul_zero]

theorem inv_smul_singleV_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (N : ℤ)
    (h : (N : 𝓞 F) ∉ v.asIdeal) : (N : F)⁻¹ • singleV F v 1 ∈ intAf F := by
  intro w
  rw [map_smul]
  by_cases hw : w = v
  · subst hw
    rw [GlobalTheory.LatVac.evalV_singleV_same, ← Algebra.algebraMap_eq_smul_one,
      HeightOneSpectrum.mem_adicCompletionIntegers]
    have h1 : w.valuation F (algebraMap (𝓞 F) F N) = 1 := (w.valuation_eq_one_iff_notMem (K := F)).2 h
    rw [map_intCast] at h1
    have h2 : Valued.v (algebraMap F (Fv F w) (N : F)⁻¹) = w.valuation F (N : F)⁻¹ :=
      w.valuedAdicCompletion_eq_valuation' _
    rw [h2, map_inv₀, h1, inv_one]
  · rw [GlobalTheory.LatVac.evalV_singleV_ne F v w hw, smul_zero]
    exact zero_mem _

theorem tmul_eq_inv_smul_tmul {F M P : Type} [Field F] [AddCommGroup M] [Module F M] [AddCommGroup P] [Module F P]
    (N : ℤ) (hN : (N : F) ≠ 0) (x : M) (c : P) : x ⊗ₜ[F] c = ((N : F)⁻¹ • x) ⊗ₜ[F] (N • c) := by
  rw [TensorProduct.smul_tmul, ← Int.cast_smul_eq_zsmul F N c, smul_smul, inv_mul_cancel₀ hN, one_smul]

theorem eventually_incA_mul_mem_intAt : ∀ (D : D7) (c : D.host.E), ∀ᶠ v : Pl D in cofinite,
    ∀ a ∈ intAt D (· = v), incA D c * a ∈ intAt D (· = v) := by
  intro D c
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨N, hN, hint⟩ := halg.exists_integral_multiple
  have hN' : (N : 𝓞 D.host.F) ≠ 0 := Int.cast_ne_zero.2 hN
  have hNF : (N : D.host.F) ≠ 0 := Int.cast_ne_zero.2 hN
  have hfin := Ideal.finite_factors (I := Ideal.span {(N : 𝓞 D.host.F)})
    (fun h => hN' (Ideal.span_singleton_eq_bot.1 h))
  filter_upwards [hfin.compl_mem_cofinite] with v hv a ha
  have hv' : (N : 𝓞 D.host.F) ∉ v.asIdeal := fun h => hv (Ideal.dvd_span_singleton.2 h)
  refine ⟨Ideal.mul_mem_left _ _ ha.1, ?_⟩
  have hc : finPart D (incA D c) = (1 : Af D.host.F) ⊗ₜ[D.host.F] c := rfl
  rw [map_mul, hc, ← idem_mul_finPart D v ha.1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  refine GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ ha.2
  refine AddSubgroup.subset_closure ⟨_, inv_smul_singleV_mem v N hv', ⟨N • c, hint⟩, ?_⟩
  exact tmul_eq_inv_smul_tmul N hNF _ c

end GlobalTheory.FinPl.AeUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.FlatTheta

variable {D : D7} {σ : ℕ}

def lastQ (B : BesLev D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E :=
  Matrix.of fun k => Fin.snoc (α := fun _ => D.host.E) (B.d.e k) ((B.d.i₀ *ᵥ vecB B.o B.ζ) k)

theorem rat_lastQ (B : BesLev D σ) : rat (lastQ B) = xLast B.d (vecB B.o B.ζ) := by
  funext k j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have := congrFun (ratV_mulVec B.d.i₀ (vecB B.o B.ζ)) k
    simp only [xLast, lastQ, rat, Matrix.map_apply, Matrix.of_apply, Fin.snoc_last]
    exact this
  · simp only [xLast, lastQ, rat, Matrix.map_apply, Matrix.of_apply, Fin.snoc_castSucc]
    rfl

theorem zeta_ne (B : BesLev D σ) : B.ζ ≠ 0 := fun h => B.line.2 (by rw [h]; simp)

theorem lastQ_indep (B : BesLev D σ) : LinearIndependent D.host.E (lastQ B).transpose := by
  have key : ∀ c : Fin (σ + 1) → D.host.E, lastQ B *ᵥ c =
      B.d.e *ᵥ (fun i => c i.castSucc) + c (Fin.last σ) • (B.d.i₀ *ᵥ (B.o.iB *ᵥ B.ζ)) := fun c => by
    funext k
    change ∑ j, lastQ B k j * c j = ∑ i, B.d.e k i * c i.castSucc + c (Fin.last σ) * (B.d.i₀ *ᵥ vecB B.o B.ζ) k
    rw [Fin.sum_univ_castSucc, mul_comm (c _)]
    simp only [lastQ, Matrix.of_apply, Fin.snoc_castSucc, Fin.snoc_last]
  refine Matrix.mulVec_injective_iff.1 ((injective_iff_map_eq_zero (lastQ B).mulVecLin).2 fun c hc => ?_)
  rw [Matrix.mulVecLin_apply, key] at hc
  have h1 := congrArg (B.d.qX *ᵥ ·) hc
  have h2 := congrArg ((B.o.qB * B.d.q0) *ᵥ ·) hc
  have a1 : B.d.qX * B.d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact B.d.pX_j0)
  have a2 : B.d.q0 * B.d.e = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact B.d.p0_jX)
  have a3 : B.d.q0 * B.d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact B.d.p0_j0)
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_zero, qX_e, Matrix.one_mulVec,
    ← Matrix.mul_assoc, a1, Matrix.zero_mul, Matrix.zero_mulVec, smul_zero, add_zero] at h1
  have a4 : B.o.qB * B.d.q0 * B.d.e = 0 := by rw [Matrix.mul_assoc, a2, Matrix.mul_zero]
  have a5 : B.o.qB * B.d.q0 * B.d.i₀ * B.o.iB = 1 := by
    rw [Matrix.mul_assoc B.o.qB, a3, Matrix.mul_one, B.o.qB_iB]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_zero,
    ← Matrix.mul_assoc, a4, a5, Matrix.zero_mulVec, zero_add, Matrix.one_mulVec] at h2
  funext j
  refine Fin.lastCases ?_ (fun i => congrFun h1 i) j
  exact (smul_eq_zero.1 h2).resolve_right (zeta_ne B)

theorem flat_isThetaFun : ∀ D : D7, FlatLaw D → ∀ (ψ : AddChar (AF D.host.F) ℂ), (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) Ψ, IsThetaFunO ψ B.V J.W Ψ → IsThetaFunO ψ B.V₀ J.W₀ (flatBF s Ψ)) ∧ ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) Ψ, IsThetaFunO ψ J.W B.V Ψ → IsThetaFunO ψ J.W₀ B.V₀ (flatFB s Ψ) := by
  intro D hF ψ
  refine ⟨fun ρ B J s Ψ hΨ => ?_, fun σ J B s Ψ hΨ => ?_⟩
  · exact (hF ψ s.weil.std B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU J.d.e (isIsoSub_e J.d).1
      (yZero B.V₀ ρ (vecB B.o B.ζ)) Ψ hΨ).2
  · have h := (hF ψ s.weil.std J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.vU (lastQ B) (lastQ_indep B) 0 Ψ hΨ).2
    rw [rat_lastQ] at h
    exact h

end GlobalTheory.Unf.FlatTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions : ∀ D : D7, FlatLaw D → ∀ (ψ : AddChar (AF D.host.F) ℂ), (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) Ψ, IsThetaFunO ψ B.V J.W Ψ → IsThetaFunO ψ B.V₀ J.W₀ (flatBF s Ψ)) ∧ ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) Ψ, IsThetaFunO ψ J.W B.V Ψ → IsThetaFunO ψ J.W₀ B.V₀ (flatFB s Ψ) := by
  first | exact @GlobalTheory.Unf.FlatTheta.flat_isThetaFun | exact GlobalTheory.Unf.FlatTheta.flat_isThetaFun | (intros; apply GlobalTheory.Unf.FlatTheta.flat_isThetaFun <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl

open IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.FinPl

section General

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]

theorem exists_int_smul_mem_of_mem_span (M : Submodule (𝓞 E) V) {y : V}
    (hy : y ∈ Submodule.span E (M : Set V)) : ∃ c : ℤ, c ≠ 0 ∧ c • y ∈ M := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • y = a • (b • y) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact M.add_mem (zsmul_mem hax b) (zsmul_mem hby a)
  | smul e x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨c, hc, hint⟩ := exists_integral_multiples ℤ ℚ ({e} : Finset E)
    have he : IsIntegral ℤ (c • e) := hint e (by simp)
    refine ⟨c * a, mul_ne_zero hc ha, ?_⟩
    obtain ⟨o, ho⟩ : ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = c • e := ⟨⟨c • e, he⟩, rfl⟩
    have h : (c * a) • (e • x) = o • (a • x) := by
      rw [← algebraMap_smul E o (a • x), ho, mul_smul, smul_comm a e x, smul_assoc]
    rw [h]
    exact M.smul_mem o hax

theorem exists_int_smul_le (L M : Submodule (𝓞 E) V) (hL : L.FG)
    (hM : Submodule.span E (M : Set V) = ⊤) : ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ L, d • x ∈ M := by
  classical
  obtain ⟨G, rfl⟩ := hL
  have hg : ∀ g ∈ G, ∃ c : ℤ, c ≠ 0 ∧ c • g ∈ M := fun g _ =>
    exists_int_smul_mem_of_mem_span M (by rw [hM]; trivial)
  choose! c hc0 hcM using hg
  refine ⟨∏ g ∈ G, c g, Finset.prod_ne_zero_iff.2 hc0, fun x hx => ?_⟩
  let N : Submodule (𝓞 E) V :=
    { carrier := {y | (∏ g ∈ G, c g) • y ∈ M}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, smul_add] at *; exact M.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun r y hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_comm]; exact M.smul_mem r hy }
  have hle : Submodule.span (𝓞 E) (G : Set V) ≤ N := by
    rw [Submodule.span_le]
    intro g hg
    show (∏ g ∈ G, c g) • g ∈ M
    rw [← Finset.mul_prod_erase G c hg, mul_comm, mul_smul]
    exact zsmul_mem (hcM g hg) _
  exact hle hx

end General

variable {D : D7}

theorem finite_places_int (d : ℤ) (hd : d ≠ 0) :
    {v : Pl D | ((d : 𝓞 D.host.F)) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((d : 𝓞 D.host.F))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hd
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem pairA_tmul_int_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (d : ℤ) (hd : d ≠ 0)
    (α : Af F) (e : E) :
    pairA F 0 α ⊗ₜ[F] (1 * e) = pairA F 0 ((d : F)⁻¹ • α) ⊗ₜ[F] (1 * (d • e)) := by
  have hdF : (d : F) ≠ 0 := Int.cast_ne_zero.2 hd
  have h : (d : F) • pairA F 0 ((d : F)⁻¹ • α) = pairA F 0 α := by
    have h1 : (d : F) • pairA F 0 ((d : F)⁻¹ • α) = pairA F 0 ((d : F) • (d : F)⁻¹ • α) :=
      Prod.ext (smul_zero (d : F)) rfl
    rw [h1, smul_smul, mul_inv_cancel₀ hdF, one_smul]
  rw [one_mul, one_mul, ← Int.cast_smul_eq_zsmul F, ← TensorProduct.smul_tmul, h]

theorem latV_le_of_int_smul (S : HSp D) (L M : Lat S) (d : ℤ) (hd : d ≠ 0)
    (hLM : ∀ x ∈ L, d • x ∈ M) (v : Pl D) (hv : ((d : 𝓞 D.host.F)) ∉ v.asIdeal) :
    latV S L (· = v) ≤ latV S M (· = v) := by
  rw [latV, latMul, AddSubgroup.closure_le]
  rintro y ⟨α, hα, hsupp, a, ha, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at ha
  subst ha
  have hval : Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) (d : D.host.F)) = 1 := by
    have h1 := (v.valuation_eq_one_iff_notMem (K := D.host.F)).mpr hv
    have h2 := v.valuedAdicCompletion_eq_valuation' (K := D.host.F) ((d : D.host.F))
    have h4 : (((d : 𝓞 D.host.F)) : D.host.F) = ((d : D.host.F)) :=
      map_intCast (algebraMap (𝓞 D.host.F) D.host.F) _
    exact h2.trans (h4 ▸ h1)
  apply AddSubgroup.subset_closure
  refine ⟨((d : D.host.F))⁻¹ • α, ?_, ?_, 1, rfl, d • x, hLM x hx, ?_⟩
  · intro w
    rw [map_smul]
    by_cases hw : w = v
    · subst hw
      have hαw := hα w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hαw ⊢
      rw [Algebra.smul_def, map_mul, map_inv₀, map_inv₀, hval, inv_one, one_mul]
      exact hαw
    · rw [hsupp w hw, smul_zero]
      exact zero_mem _
  · intro w hw
    rw [map_smul, hsupp w hw, smul_zero]
  · funext i
    exact pairA_tmul_int_gen d hd α (x i)

theorem latV_eq_off_finite : ∀ (D : D7) (S : HSp D) (L M : Lat S), Submodule.IsFullLattice D.host.E L →
    Submodule.IsFullLattice D.host.E M → ∃ T : Finset (Pl D), ∀ v, v ∉ T → latV S L (· = v) = latV S M (· = v) := by
  intro D S L M hL hM
  obtain ⟨d₁, hd₁, h₁⟩ := exists_int_smul_le L M hL.fg hM.span_eq_top
  obtain ⟨d₂, hd₂, h₂⟩ := exists_int_smul_le M L hM.fg hL.span_eq_top
  have hd : d₁ * d₂ ≠ 0 := mul_ne_zero hd₁ hd₂
  refine ⟨(finite_places_int (D := D) (d₁ * d₂) hd).toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Int.cast_mul] at hv
  have hv₁ : ((d₁ : 𝓞 D.host.F)) ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_right _ h)
  have hv₂ : ((d₂ : 𝓞 D.host.F)) ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_left _ h)
  exact le_antisymm (latV_le_of_int_smul S L M d₁ hd₁ h₁ v hv₁) (latV_le_of_int_smul S M L d₂ hd₂ h₂ v hv₂)

end GlobalTheory.FinPl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhereStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattices_agree_almost_everywhere : ∀ (D : D7) (S : HSp D) (L M : Lat S), Submodule.IsFullLattice D.host.E L → Submodule.IsFullLattice D.host.E M → ∃ T : Finset (Pl D), ∀ v, v ∉ T → latV S L (· = v) = latV S M (· = v) := by
  intro D S L M hL hM
  first
  | exact GlobalTheory.FinPl.latV_eq_off_finite D S L M hL hM
  | exact GlobalTheory.FinPl.latV_eq_off_finite D S L M hL hM.toIsLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijective
section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.LinkSimil
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.StCheck

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}


theorem link_simil {σ : ℕ} {B : BesLev D σ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (h : IsLineVec L' ζ')
    (l : Link B L' ζ') : l.τᴴ * (B.L.gram * l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram := by
  have e : star ζ' ⬝ᵥ (l.τᴴ * (B.L.gram * l.τ)) *ᵥ ζ' =
      star ζ' ⬝ᵥ ((D.host.xi0 * star D.host.xi0) • L'.gram) *ᵥ ζ' := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec, l.map, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← l.norm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]
  have hu : Unique (Fin L'.rank) := by rw [h.1]; infer_instance
  have h2 := h.2
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at e h2
  funext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have a : star ζ' default ≠ 0 := left_ne_zero_of_mul h2
  have b : ζ' default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
  have c := mul_left_cancel₀ a e
  have c' := mul_right_cancel₀ b c
  exact c'

end GlobalTheory.Unf.StCheck

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijective
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.LinkGram

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj starAdj_ofAdj)

variable {D : D7}

theorem exists_inv_of_rank_one {m n : ℕ} (hm : m = 1) (hn : n = 1) (τ : Matrix (Fin m) (Fin n) D.host.E) (h : τ ≠ 0) :
    ∃ σ : Matrix (Fin n) (Fin m) D.host.E, σ * τ = 1 ∧ τ * σ = 1 := by
  subst hm; subst hn
  have hd : IsUnit τ.det := by
    rw [Matrix.det_unique, isUnit_iff_ne_zero]
    intro h0; apply h; ext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default, h0]; rfl
  exact ⟨τ⁻¹, Matrix.nonsing_inv_mul _ hd, Matrix.mul_nonsing_inv _ hd⟩

theorem scalar_one : incA D (-D.host.xi0⁻¹) * cA D (incA D D.host.xi0) = 1 := by
  have h := congrArg (cA D) (HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv (D := D))
  rw [map_mul, map_one, cA_cA, mul_comm] at h
  exact h

theorem ofAdj_starAdj (L S : HSp D) (x : WO L S) : ofAdj L S (starAdj L S x) = x := by
  rw [starAdj, ofAdj, adj_smul, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    scalar_one, one_smul]
  simp only [Matrix.mul_assoc, giA_gA_cancel, giA_mul_gA, Matrix.mul_one]

theorem link_gram : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' →
    ∀ l : Link B L' ζ', l.τᴴ * (B.L.gram * l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram ∧
      ∀ S : HSp D, Function.Bijective (l.κ S) ∧
        ∀ w, l.κ S w ∈ ratMx D S.rank B.L.rank → w ∈ ratMx D L'.rank S.rank := by
  intro D ρ B L' ζ' h l
  refine ⟨by rw [Int.cast_one, one_mul]; exact GlobalTheory.Unf.StCheck.link_simil h l, fun S => ?_⟩
  have hτ : l.τ ≠ 0 := by
    intro h0
    have e := l.map
    rw [h0, Matrix.zero_mulVec] at e
    have hz : B.ζ = 0 := neg_eq_zero.mp e.symm
    apply B.line.2
    rw [hz]; simp
  obtain ⟨σ, hστ, hτσ⟩ := exists_inv_of_rank_one B.line.1 h.1 l.τ hτ
  have key : ∀ w, (rat σ : Mx D L'.rank B.L.rank) * starAdj B.L S (l.κ S w) = w := by
    intro w
    rw [Link.κ, starAdj_ofAdj, ← Matrix.mul_assoc, ← rat_mul, hστ, rat_one, Matrix.one_mul]
  refine ⟨⟨fun w w' e => by rw [← key w, ← key w', e], fun x => ⟨(rat σ : Mx D L'.rank B.L.rank) * starAdj B.L S x, ?_⟩⟩,
    fun w hw => ?_⟩
  · rw [Link.κ, ← Matrix.mul_assoc, ← rat_mul, hτσ, rat_one, Matrix.one_mul, ofAdj_starAdj]
  · rw [← key w]
    refine ratMx_mul (rat_mem σ) ?_
    obtain ⟨γ, hγ⟩ := mem_ratMx.1 hw
    rw [← hγ, starAdj, giA, gA, ← rat_conjTranspose, ← rat_mul, ← rat_mul, ← rat_smul]
    exact rat_mem _

end GlobalTheory.Unf.LinkGram
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLineLink_gram_similitude_bijective : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ l : Link B L' ζ', l.τᴴ ⬝ (B.L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram ∧ ∀ S : HSp D, Function.Bijective (l.κ S) ∧ ∀ w, l.κ S w ∈ ratMx D S.rank B.L.rank → w ∈ ratMx D L'.rank S.rank := by
  first | exact @GlobalTheory.Unf.LinkGram.link_gram | exact GlobalTheory.Unf.LinkGram.link_gram | (intros; apply GlobalTheory.Unf.LinkGram.link_gram <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCoreOfExists
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCoreOfExists
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem resEta_core {D : D7} {χ : (AE D)ˣ →* Circle} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (h : ResEta D χ S.rank) : ResEta D χ S₀.rank :=
  resEta_parity h (by rw [← d.rank_add]; omega)

theorem descent_of_weilDatumExists : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion.WeilDatumExists D → Descent D := by
  intro D hW ψ S T χS χT om h
  refine ⟨fun S₀ ρ d => ?_, fun T₀ ρ d => ?_⟩
  · exact hW S₀ T ψ χS χT h.std h.hecS h.hecT (resEta_core d h.resS) h.resT
  · exact hW S T₀ ψ χS χT h.std h.hecS h.hecT h.resS (resEta_core d h.resT)

end GlobalTheory.Unf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCoreOfExistsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatumDescendsToWittCore_of_exists : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion.WeilDatumExists D → Descent D := by
  first | exact @GlobalTheory.Unf.descent_of_weilDatumExists | exact GlobalTheory.Unf.descent_of_weilDatumExists | (intros; apply GlobalTheory.Unf.descent_of_weilDatumExists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPa
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPa
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.ParCont

variable {D : D7} {m n : ℕ}

theorem eventually_close {P : Type} [TopologicalSpace P] (K : Mx D m n → P → ℂ) (hc : Continuous (Function.uncurry K))
    (hp : ∀ γ ∈ ratMx D m n, ∀ x p, K (γ + x) p = K x p) (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in nhds p₀, ∀ x, ‖K x p - K x p₀‖ ≤ ε := by
  obtain ⟨-, -, -, -, -, C, hC, hCc⟩ := lattice_Mx D m n
  have h : ∀ᶠ p in nhds p₀, ∀ x ∈ C, ‖K x p - K x p₀‖ < ε := by
    refine hC.eventually_forall_of_forall_eventually (P := fun p x => ‖K x p - K x p₀‖ < ε) fun y _ => ?_
    have h1 : Continuous fun z : P × Mx D m n => ‖K z.2 z.1 - K z.2 p₀‖ :=
      ((hc.comp (continuous_snd.prodMk continuous_fst)).sub
        (hc.comp (continuous_snd.prodMk continuous_const))).norm
    exact (isOpen_lt h1 continuous_const).mem_nhds (by simpa using hε)
  filter_upwards [h] with p h x
  obtain ⟨γ, hγ, hx⟩ := hCc x
  rw [← hp γ hγ x p, ← hp γ hγ x p₀]
  exact (h _ hx).le

theorem isCovolOne_map {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)} (h : IsCovolOne (ratMx D m n) μ 𝓕)
    (e : Mx D m n ≃+ Mx D m n) (he : Continuous e) (he' : Continuous e.symm)
    (hr : ∀ x, e x ∈ ratMx D m n ↔ x ∈ ratMx D m n) :
    IsCovolOne (ratMx D m n) (μ.map e) (e '' 𝓕) ∧ MeasurableEmbedding e := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := h.1
  let f : Mx D m n ≃ₜ Mx D m n := { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  have hemb : MeasurableEmbedding e := f.measurableEmbedding
  refine ⟨⟨e.isAddHaarMeasure_map μ he he', ?_, ?_⟩, hemb⟩
  · let g : ratMx D m n ≃ ratMx D m n :=
      { toFun := fun γ => ⟨e.symm γ, (hr _).1 (by rw [e.apply_symm_apply]; exact γ.2)⟩
        invFun := fun γ => ⟨e γ, (hr _).2 γ.2⟩
        left_inv := fun γ => Subtype.ext (e.apply_symm_apply _)
        right_inv := fun γ => Subtype.ext (e.symm_apply_apply _) }
    refine h.2.1.image_of_equiv e.toEquiv ?_ g fun γ x => ?_
    · refine ⟨he'.measurable.aemeasurable, ?_⟩
      have : (μ.map e).map e.symm = μ := by
        rw [Measure.map_map he'.measurable he.measurable]
        have : (e.symm ∘ e : Mx D m n → Mx D m n) = id := funext e.symm_apply_apply
        rw [this, Measure.map_id]
      exact this.absolutelyContinuous
    · change e (e.symm γ + x) = γ + e x
      rw [map_add (f := _), e.apply_symm_apply]
  · rw [hemb.map_apply, Set.preimage_image_eq _ e.injective]
    exact h.2.2

theorem parCont : ∀ (D : D7) (m n : ℕ) (v : VolM D m n) (P : Type) [TopologicalSpace P] (K : Mx D m n → P → ℂ), Continuous (Function.uncurry K) → (∀ γ ∈ ratMx D m n, ∀ x p, K (γ + x) p = K x p) → (∀ p, IntegrableOn (fun x => K x p) v.𝓕 v.μ) ∧ (Continuous fun p => ∫ x in v.𝓕, K x p ∂v.μ) ∧ (∀ p₀, ∃ C : ℝ, ∀ᶠ p in nhds p₀, ∀ x, ‖K x p‖ ≤ C) ∧ ∀ (e : Mx D m n ≃+ Mx D m n), Continuous e → Continuous e.symm → (∀ x, e x ∈ ratMx D m n ↔ x ∈ ratMx D m n) → ∀ p, ∫ x in v.𝓕, K (e x) p ∂v.μ = ∫ x in v.𝓕, K x p ∂v.μ := by
  intro D m n v P _ K hc hp
  have hx : ∀ p, Continuous fun x => K x p := fun p => hc.comp (continuous_id.prodMk continuous_const)
  have hi : ∀ p, IntegrableOn (fun x => K x p) v.𝓕 v.μ := fun p =>
    covolOne_integrableOn v.covol _ (hx p) fun γ hγ a => hp γ hγ a p
  refine ⟨hi, ?_, fun p₀ => ?_, fun e he he' hr p => ?_⟩
  · refine continuous_iff_continuousAt.2 fun p₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
    filter_upwards [eventually_close K hc hp p₀ (half_pos hε)] with p h
    rw [dist_eq_norm, ← integral_sub (hi p) (hi p₀)]
    have h1 : v.μ v.𝓕 = 1 := v.covol.2.2
    have h2 := norm_setIntegral_le_of_norm_le_const (μ := v.μ) (s := v.𝓕) (f := fun x => K x p - K x p₀) (C := ε / 2)
      (by rw [h1]; exact ENNReal.one_lt_top) fun x _ => h x
    rw [Measure.real, h1, ENNReal.toReal_one, mul_one] at h2
    linarith
  · obtain ⟨-, -, -, -, -, C, hC, hCc⟩ := lattice_Mx D m n
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn (hx p₀).continuousOn
    refine ⟨B + 1, ?_⟩
    filter_upwards [eventually_close K hc hp p₀ one_pos] with p h x
    obtain ⟨γ, hγ, ha⟩ := hCc x
    have h1 : ‖K x p₀‖ ≤ B := by rw [← hp γ hγ x p₀]; exact hB _ ha
    calc ‖K x p‖ = ‖K x p₀ + (K x p - K x p₀)‖ := by rw [add_sub_cancel]
      _ ≤ ‖K x p₀‖ + ‖K x p - K x p₀‖ := norm_add_le _ _
      _ ≤ B + 1 := add_le_add h1 (h x)
  · obtain ⟨h1, hemb⟩ := isCovolOne_map v.covol e he he' hr
    rw [← covolOne_integral_eq v.covol h1 (fun x => K x p) fun γ hγ a => hp γ hγ a p,
      hemb.setIntegral_map, Set.preimage_image_eq _ e.injective]

end GlobalTheory.Unf.ParCont
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixQuotient_periodicIntegral_continuous_param : ∀ (D : D7) (m n : ℕ) (v : VolM D m n) (P : Type) [TopologicalSpace P] (K : Mx D m n → P → ℂ), Continuous (Function.uncurry K) → (∀ γ ∈ ratMx D m n, ∀ x p, K (γ + x) p = K x p) → (∀ p, IntegrableOn (fun x => K x p) v.𝓕 v.μ) ∧ (Continuous fun p => ∫ x in v.𝓕, K x p ∂v.μ) ∧ (∀ p₀, ∃ C : ℝ, ∀ᶠ p in nhds p₀, ∀ x, ‖K x p‖ ≤ C) ∧ ∀ (e : Mx D m n ≃+ Mx D m n), Continuous e → Continuous e.symm → (∀ x, e x ∈ ratMx D m n ↔ x ∈ ratMx D m n) → ∀ p, ∫ x in v.𝓕, K (e x) p ∂v.μ = ∫ x in v.𝓕, K x p ∂v.μ := by
  first | exact @GlobalTheory.Unf.ParCont.parCont | exact GlobalTheory.Unf.ParCont.parCont | (intros; apply GlobalTheory.Unf.ParCont.parCont <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatEqMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FinPl.AlmostAll

theorem exists_nat_eq_mul {E : Type} [Field E] [NumberField E] {c : 𝓞 E} (hc : c ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ c' : 𝓞 E, (n : 𝓞 E) = c * c' := by
  refine ⟨Ideal.absNorm (Ideal.span {c}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc
  · obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    exact ⟨c', by rw [← hc', mul_comm]⟩

theorem exists_nat_bounds {E : Type} [Field E] [NumberField E]
    {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (hI : I ≠ 0) :
    ∃ N M : ℕ, N ≠ 0 ∧ M ≠ 0 ∧ (∀ a ∈ I, ∃ b : 𝓞 E, (N : E) * a = algebraMap (𝓞 E) E b) ∧ (M : E) ∈ I := by
  obtain ⟨d, hd, hint⟩ := I.isFractional
  obtain ⟨N, hN, d', hdd'⟩ := exists_nat_eq_mul (nonZeroDivisors.ne_zero hd)
  have hsub : (I : Submodule (𝓞 E) E) ≠ ⊥ := FractionalIdeal.coeToSubmodule_ne_bot.2 hI
  obtain ⟨x, hxI, hx0⟩ := (Submodule.ne_bot_iff _).1 hsub
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) x
  simp only at hrs
  have hs0 : algebraMap (𝓞 E) E (s : 𝓞 E) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.ne_zero s.2)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at hrs
    exact hrs.elim hx0 hs0
  have hrI : algebraMap (𝓞 E) E r ∈ (I : Submodule (𝓞 E) E) := by
    rw [← hrs, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hxI
  obtain ⟨M, hM, r', hrr'⟩ := exists_nat_eq_mul hr0
  refine ⟨N, M, hN, hM, fun a ha => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hint a (FractionalIdeal.mem_coe.2 ha)
    refine ⟨d' * b, ?_⟩
    rw [map_mul, hb, Algebra.smul_def, ← mul_assoc, ← map_mul, mul_comm d' d, ← hdd', map_natCast]
  · have : (M : E) = r' • algebraMap (𝓞 E) E r := by
      rw [Algebra.smul_def, ← map_mul, mul_comm r' r, ← hrr', map_natCast]
    rw [← FractionalIdeal.mem_coe, this]
    exact Submodule.smul_mem _ _ hrI

theorem eventually_notMem {F : Type} [Field F] [NumberField F] {N : ℕ} (hN : N ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (N : 𝓞 F) ∉ v.asIdeal := by
  have h0 : (N : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hI : Ideal.span {(N : 𝓞 F)} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset ?_)
  intro v hv
  simp only [Set.mem_setOf_eq, not_not] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem inv_mem_integers {F : Type} [Field F] [NumberField F] {N : ℕ} {v : HeightOneSpectrum (𝓞 F)}
    (hv : (N : 𝓞 F) ∉ v.asIdeal) : algebraMap F (Fv F v) (N : F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : v.valuation F (N : F) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 F) F), HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hv
  have h2 : Valued.v (algebraMap F (Fv F v) (N : F)) = 1 := by
    rw [← h1]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (N : F)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, h2, inv_one]

theorem smul_inv_mem {F : Type} [Field F] [NumberField F] {N : ℕ} {v : HeightOneSpectrum (𝓞 F)}
    (hv : (N : 𝓞 F) ∉ v.asIdeal) {α : Af F} (hα : α ∈ intAf F) (h0 : ∀ w, ¬ w = v → evalV F w α = 0) :
    (N : F)⁻¹ • α ∈ intAf F ∧ ∀ w, ¬ w = v → evalV F w ((N : F)⁻¹ • α) = 0 := by
  have key : ∀ w, evalV F w ((N : F)⁻¹ • α) = algebraMap F (Fv F w) (N : F)⁻¹ * evalV F w α := by
    intro w
    rw [map_smul, Algebra.smul_def]
  have hα' : ∀ w, evalV F w α ∈ w.adicCompletionIntegers F := hα
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · rw [key]
    by_cases hw : w = v
    · subst hw
      exact mul_mem (inv_mem_integers hv) (hα' w)
    · rw [h0 w hw, mul_zero]
      exact zero_mem _
  · rw [key, h0 w hw, mul_zero]

theorem pairA_smul {F : Type} [Field F] [NumberField F] (c : F) (α : Af F) :
    pairA F 0 (c • α) = c • pairA F 0 α := by
  show ((0 : Ainf F), c • α) = c • ((0 : Ainf F), α)
  rw [Prod.smul_mk, smul_zero]

theorem tmul_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {N : ℕ} (hN : N ≠ 0) (α : Af F) (z : E) :
    pairA F 0 α ⊗ₜ[F] z = pairA F 0 ((N : F)⁻¹ • α) ⊗ₜ[F] ((N : E) * z) := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hz : (N : E) * z = (N : F) • z := by
    rw [Algebra.smul_def, map_natCast]
  rw [hz, TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← pairA_smul, smul_smul,
    mul_inv_cancel₀ hN', one_smul]

theorem latA_eq_latV (D : D7) :
    ∀ᶠ v : Pl D in cofinite, ∀ (S : HSp D) (L : Lat S), latA S L (· = v) = latV S L (· = v) := by
  obtain ⟨N, M, hN, hM, hNI, hMI⟩ := exists_nat_bounds (GlobalTheory.ModelLatticeCheck.AA_ne_zero D)
  filter_upwards [eventually_notMem (F := D.host.F) hN, eventually_notMem (F := D.host.F) hM]
    with v hvN hvM
  intro S L
  apply le_antisymm
  · rw [latA, latMul, AddSubgroup.closure_le]
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    obtain ⟨b, hb⟩ := hNI a ha
    obtain ⟨hα', h0'⟩ := smul_inv_mem hvN hα h0
    rw [latV, latMul]
    refine AddSubgroup.subset_closure ⟨(N : D.host.F)⁻¹ • α, hα', h0', 1, rfl, b • x, L.smul_mem b hx, ?_⟩
    funext i
    have e : (N : D.host.E) * (a * x i) = 1 * (b • x) i := by
      rw [one_mul, Pi.smul_apply, Algebra.smul_def, ← hb, mul_assoc]
    rw [tmul_eq hN α (a * x i), e]
  · rw [latV, latMul, AddSubgroup.closure_le]
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨hα', h0'⟩ := smul_inv_mem hvM hα h0
    rw [latA, latMul]
    refine AddSubgroup.subset_closure ⟨(M : D.host.F)⁻¹ • α, hα', h0', (M : D.host.E), hMI, x, hx, ?_⟩
    funext i
    rw [one_mul, tmul_eq hM α (x i)]

end GlobalTheory.FinPl.AlmostAll
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorDisjointSupportSmulAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorDisjointSupportSmulAdd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisDisj

variable {D : D7}

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rw [TensorProduct.smul_tmul']; rfl
  | add a b ha hb => rw [smul_add, map_add (f := _), map_add (f := _), ha, hb, smul_add]

theorem hO_add_left (S T : HSp D) (x x' y : WO S T) : hO S T (x + x') y = hO S T x y + hO S T x' y := by
  simp only [hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hO_add_right (S T : HSp D) (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  simp only [hO, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem hO_smul_smul (S T : HSp D) (c c' : AF D.host.F) (x y : WO S T) :
    hO S T (c • x) (c' • y) = (c * c') • hO S T x y := by
  simp only [hO, Matrix.smul_apply, cA_smul, Finset.smul_sum, mul_smul_comm, smul_mul_assoc, smul_smul]

theorem symplOH_add_left (S T : HSp D) (x x' y : WO S T) :
    symplOH S T (x + x') y = symplOH S T x y + symplOH S T x' y := by
  simp only [symplOH, symplO, hO_add_left, mul_add, map_add (f := _)]

theorem symplOH_add_right (S T : HSp D) (x y y' : WO S T) :
    symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  simp only [symplOH, symplO, hO_add_right, mul_add, map_add (f := _)]

theorem symplOH_smul_smul_eq_zero (S T : HSp D) (c c' : AF D.host.F) (x y : WO S T) (h : c * c' = 0) :
    symplOH S T (c • x) (c' • y) = 0 := by
  rw [symplOH, symplO, hO_smul_smul, h, zero_smul, mul_zero, map_zero, mul_zero]

theorem heisO_smul_add_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' : AF D.host.F) (x y : WO S T) (f : WO S T → ℂ), c * c' = 0 → heisO ψ S T (c • x + c' • y) f = heisO ψ S T (c • x) (heisO ψ S T (c' • y) f) := by
  intro D ψ S T c c' x y f h
  funext w
  simp only [heisO]
  rw [symplOH_add_right, symplOH_add_left, symplOH_smul_smul_eq_zero S T c c' x y h, add_zero,
    AddChar.map_add_eq_mul, add_assoc, mul_assoc]

end GlobalTheory.HeisDisj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorDisjointSupportSmulAddStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperator_disjointSupport_smul_add : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' : AF D.host.F) (x y : WO S T) (f : WO S T → ℂ), c * c' = 0 → heisO ψ S T (c • x + c' • y) f = heisO ψ S T (c • x) (heisO ψ S T (c' • y) f) := by
  first | exact @GlobalTheory.HeisDisj.heisO_smul_add_smul | exact GlobalTheory.HeisDisj.heisO_smul_add_smul | (intros; apply GlobalTheory.HeisDisj.heisO_smul_add_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumPreservesThetaFundamentalDomainPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumPreservesThetaFundamentalDomainPairing
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.WeilPairing

theorem thPair_om_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S T), IsWeilDatumO ψ S T χ χ' om → ∀ (v : VolM D T.rank S.rank) p f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → thPair v.μ v.𝓕 (om p f) (om p f') = thPair v.μ v.𝓕 f f' := by
  intro D ψ S T χ χ' om hW v p f f' hf hf'
  obtain ⟨hμ, h𝓕, -⟩ := v.covol
  have h𝓕' : IsAddFundamentalDomain (ratL T S) v.𝓕 v.μ := h𝓕
  exact GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hW.std S T v.μ v.𝓕 hμ h𝓕' (om p) (fun g hg => hW.om_pres p g hg)
    (fun g hg => hW.om_unit v.μ v.𝓕 hμ h𝓕' p g hg) f f' hf hf'

end GlobalTheory.WeilPairing

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumPreservesThetaFundamentalDomainPairingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_preserves_thetaFundamentalDomainPairing : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S T), IsWeilDatumO ψ S T χ χ' om → ∀ (v : VolM D T.rank S.rank) p f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → thPair v.μ v.𝓕 (om p f) (om p f') = thPair v.μ v.𝓕 f f' := by
  first | exact @GlobalTheory.WeilPairing.thPair_om_eq | exact GlobalTheory.WeilPairing.thPair_om_eq | (intros; apply GlobalTheory.WeilPairing.thPair_om_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiKernelEqWeilRepresentationApply
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiKernelEqWeilRepresentationApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem fjKer_eq_om_apply : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W W₀ V₀ A L : HSp D) (ρ : ℕ) (dW : HypDec W W₀ ρ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om V₀ W₀), IsWeilDatumO ψ V₀ W₀ χ χ' om → ∀ Ξ, IsThetaFunO ψ V₀ W₀ Ξ → ∀ h₀ n h, fjKer ψ dW o ζ om Ξ h₀ n h = ψ (cenT dW L (yZero L ρ ζ) n) * om (o.emb (h₀, 1), h) Ξ ((o.resS W₀).symm (0, ptT dW L (yZero L ρ ζ) n)) := by
  intro D ψ W W₀ V₀ A L ρ dW o ζ χ χ' om hW Ξ hΞ h₀ n h
  have hp : (o.resS W₀).symm (0, ptT dW L (yZero L ρ ζ) n) = ptT dW V₀ (yZero V₀ ρ (vecB o ζ)) n := by
    rw [← ptT_yZero_vecB o dW ζ n, AddEquiv.symm_apply_apply]
  have hfix : actO V₀ W₀ (o.emb (h₀, 1)) 1 (ptT dW V₀ (yZero V₀ ρ (vecB o ζ)) n) =
      ptT dW V₀ (yZero V₀ ρ (vecB o ζ)) n := by
    apply (o.resS W₀).injective
    rw [o.resS_actO, ptT_yZero_vecB]
    simp only [actO_eq, inv_one, mt_one, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul]
  have hm : om (o.emb (h₀, 1), 1) (om (1, h) Ξ) = om (o.emb (h₀, 1), h) Ξ := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [hp, fjKer, opA, jacT, map_smul, hW.om_heis _ _ _ _ (hW.om_pres _ _ hΞ), hfix, hm, cenT_yZero_vecB]
  simp only [Pi.smul_apply, smul_eq_mul, heisO, zero_add, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.Unf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiKernelEqWeilRepresentationApplyStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiKernel_eq_weilRepresentation_apply : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W W₀ V₀ A L : HSp D) (ρ : ℕ) (dW : HypDec W W₀ ρ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om V₀ W₀), IsWeilDatumO ψ V₀ W₀ χ χ' om → ∀ Ξ, IsThetaFunO ψ V₀ W₀ Ξ → ∀ h₀ n h, fjKer ψ dW o ζ om Ξ h₀ n h = ψ (cenT dW L (yZero L ρ ζ) n) * om (o.emb (h₀, 1), h) Ξ ((o.resS W₀).symm (0, ptT dW L (yZero L ρ ζ) n)) := by
  first | exact @GlobalTheory.Unf.fjKer_eq_om_apply | exact GlobalTheory.Unf.fjKer_eq_om_apply | (intros; apply GlobalTheory.Unf.fjKer_eq_om_apply <;> assumption)
end
end
