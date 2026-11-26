module

public import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousOfDense
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckDeformationOfLifting
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedAdjoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionPowAnalyticVectorNormLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped Pointwise

namespace GlobalTheory.ConjOverQuad

theorem under_eq_or_smul_under_eq {L : Type} [Field L] [NumberField L] [IsGalois ℚ L] {p : ℕ} (hp : p.Prime) (b : L)
    (hb : ∀ σ : L ≃ₐ[ℚ] L, σ b = b ∨ σ b = -b) (c : L ≃ₐ[ℚ] L) (hc : c b = -b)
    (v : Ideal (𝓞 L)) [v.IsPrime] (hv : ((p : ℕ) : 𝓞 L) ∈ v)
    (Q : Ideal (𝓞 (IntermediateField.adjoin ℚ {b}))) [Q.IsPrime]
    (hQ : ((p : ℕ) : 𝓞 (IntermediateField.adjoin ℚ {b})) ∈ Q) :
    v.under (𝓞 (IntermediateField.adjoin ℚ {b})) = Q ∨
      (c⁻¹ • v).under (𝓞 (IntermediateField.adjoin ℚ {b})) = Q := by
  obtain ⟨⟨W, hW, hWQ⟩⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 L)))
  have hpW : ((p : ℕ) : 𝓞 L) ∈ W := by
    rw [hWQ.over, Ideal.mem_under] at hQ
    simpa using hQ
  have := GlobalTheory.Mem.Chr.liesOver_span_of_natCast_mem hp _ hv
  have := GlobalTheory.Mem.Chr.liesOver_span_of_natCast_mem hp _ hpW
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) v W (L ≃ₐ[ℚ] L)
  rcases hb σ with h1 | h1
  · left
    rw [hWQ.over, ← hσ, GlobalTheory.Mem.Chr.under_smul_of_fix b σ h1]
  · right
    have h2 : (σ * c) b = b := by
      rw [AlgEquiv.mul_apply, hc, map_neg, h1, neg_neg]
    have h4 : (σ * c) • c⁻¹ • v = W := by rw [mul_smul, smul_inv_smul, hσ]
    rw [hWQ.over, ← h4, GlobalTheory.Mem.Chr.under_smul_of_fix b _ h2]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem div_or_conj_div : ∀ (D : D7) (P : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (w : HeightOneSpectrum (𝓞 D.host.E)), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → P.Div k w ∨ ∃ w' : HeightOneSpectrum (𝓞 D.host.E), P.Div k w' ∧ w'.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) w.asIdeal := by
  intro D P k w hw
  have hG : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hsq := D.host.sqrtMinusD_sq
  have hc := D.host.conj_sqrtMinusD
  have hb : ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E,
      σ D.host.sqrtMinusD = D.host.sqrtMinusD ∨ σ D.host.sqrtMinusD = -D.host.sqrtMinusD := by
    intro σ
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    rw [← map_pow, hsq, map_neg, map_natCast]
  have := w.isPrime
  have hQ := (P.pb k).isPrime
  rcases @under_eq_or_smul_under_eq _ _ _ _ _ (D.host.g_prime k) D.host.sqrtMinusD hb D.host.conj hc w.asIdeal _ hw
    (P.pb k).asIdeal hQ (P.pb_over k) with h | h
  · exact Or.inl (HeightOneSpectrum.ext h)
  · refine Or.inr ⟨Formalism.L2.Col.conjPrime₂ w, HeightOneSpectrum.ext ?_, (Formalism.L2.Col.conjIdeal_asIdeal w).symm⟩
    have e : (Formalism.L2.Col.conjPrime₂ w).asIdeal = D.host.conj⁻¹ • w.asIdeal := by
      ext y
      rw [Formalism.L2.Col.mem_conjP, Ideal.mem_inv_pointwise_smul_iff]
      have : Formalism.L2.Col.cO D.host.E y = D.host.conj • y :=
        RingOfIntegers.ext (bridge_star_holds D.R D.host (y : D.host.E))
      rw [this]
    show ((Formalism.L2.Col.conjPrime₂ w).asIdeal).under (𝓞 D.host.K) = _
    rw [e]
    exact h

end GlobalTheory.ConjOverQuad
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuous
noncomputable section

open NumberField Topology

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_mapInf : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_mapFin : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pFin)

theorem IsAutForm.continuous {φ : Sm E a} (h : IsAutForm φ) : Continuous φ.1 := by
  rw [continuous_iff_continuousAt]
  intro g₀
  have hmul : Continuous fun g : GA E a => g₀⁻¹ * g := continuous_const.mul continuous_id
  have hN : {g : GA E a | Matrix.GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) ∈ {k | finRep E a k φ = φ}} ∈ 𝓝 g₀ := by
    refine (h.level.preimage (continuous_mapFin.comp hmul)).mem_nhds ?_
    simp
  have heq : φ.1 =ᶠ[𝓝 g₀] fun g => chart φ.1 g₀ (toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) := by
    filter_upwards [hN] with g hg
    rw [chart_val]
    have hk : ∀ x, φ.1 (x * finGL E a (Matrix.GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g))) = φ.1 x :=
      fun x => congrArg (fun ψ : Sm E a => ψ.1 x) hg
    conv_lhs => rw [← mul_inv_cancel_left g₀ g, ← infGL_mul_finGL (g₀⁻¹ * g), ← mul_assoc, hk]
  refine ContinuousAt.congr ?_ heq.symm
  have hc : ContinuousAt (chart φ.1 g₀) (toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g₀)).val) :=
    (contDiffAt_chart φ.2 g₀ (val_mem_invSet _)).continuousAt
  exact ContinuousAt.comp (f := fun g : GA E a => toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) hc
    (Units.continuous_val.comp (continuous_mapInf.comp hmul)).continuousAt

end GlobalTheory.CuspRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOn
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOn
open NumberField GlobalTheory.CuspRep Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CuspRep.JointCont

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

theorem map_unip {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : BlockIx a r → R) :
    Matrix.GeneralLinearGroup.map f (unip x) = unip (fun p => f (x p)) := by
  apply Units.ext
  ext i j
  change f ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) = (1 + nilM fun p => f (x p) : Matrix (Fin a) (Fin a) S) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add (f := _)]
  split_ifs <;> simp

theorem continuous_nilM {R : Type} [CommRing R] [TopologicalSpace R] :
    Continuous (fun x : BlockIx a r → R => (nilM x : Matrix (Fin a) (Fin a) R)) := by
  refine continuous_matrix fun i j => ?_
  simp only [nilM, Matrix.of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_unip {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (fun x : BlockIx a r → R => unip x) :=
  Units.continuous_iff.2 ⟨continuous_const.add continuous_nilM, continuous_const.sub continuous_nilM⟩

theorem continuous_pInf : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem chart_mul_finGL_of_fix (φ : Sm E a) (h : GA E a) (k : GL (Fin a) (Af E)) (hk : finRep E a k φ = φ) :
    chart φ.1 (h * finGL E a k) = chart φ.1 h := by
  rw [← chart_rt_fin]
  congr 1
  funext z
  exact congrArg (fun ψ : Sm E a => ψ.1 z) hk

def infPart (g : GA E a) (x : BlockIx a r → Ad E) : GL (Fin a) (Cinf E) :=
  unip (fun p => pInf E (x p)) * Matrix.GeneralLinearGroup.map (pInf E) g

def finPart (g : GA E a) (x : BlockIx a r → Ad E) : GL (Fin a) (Af E) :=
  unip (fun p => pFin E (x p)) * Matrix.GeneralLinearGroup.map (pFin E) g

theorem unip_mul_eq (g : GA E a) (x : BlockIx a r → Ad E) :
    unip x * g = finGL E a (finPart g x) * infGL E a (infPart g x) := by
  refine ga_ext ?_ ?_ <;>
    simp only [finPart, infPart, map_mul, map_unip, pInf_finGL, pInf_infGL, pFin_finGL, pFin_infGL, one_mul, mul_one]

theorem continuous_infPart (g : GA E a) : Continuous (fun x : BlockIx a r → Ad E => toL (infPart g x).val) := by
  have h1 : Continuous (fun x : BlockIx a r → Ad E => fun p => pInf E (x p)) :=
    continuous_pi fun p => continuous_pInf.comp (continuous_apply p)
  have h2 : Continuous (fun x : BlockIx a r → Ad E =>
      ((infPart g x : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))) :=
    Units.continuous_val.comp ((continuous_unip.comp h1).mul continuous_const)
  exact h2

theorem continuous_finPart (g : GA E a) : Continuous (fun x : BlockIx a r → Ad E => finPart g x) := by
  have h1 : Continuous (fun x : BlockIx a r → Ad E => fun p => pFin E (x p)) :=
    continuous_pi fun p => continuous_pFin.comp (continuous_apply p)
  exact (continuous_unip.comp h1).mul continuous_const

theorem eventually_chart_eq (φ : Sm E a) (hφ : IsAutForm φ) (g : GA E a) (x₀ : BlockIx a r → Ad E) :
    ∀ᶠ x in 𝓝 x₀, chart φ.1 (unip x * g) =
      chart φ.1 (finGL E a (finPart g x₀)) ∘ lmul (toL (infPart g x).val) := by
  have hc : Continuous (fun x : BlockIx a r → Ad E => (finPart g x₀)⁻¹ * finPart g x) := continuous_const.mul (continuous_finPart g)
  have h1 : finRep E a ((finPart g x₀)⁻¹ * finPart g x₀) φ = φ := by rw [inv_mul_cancel]; simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hφ.level.mem_nhds h1)] with x hx
  have hx' : finRep E a ((finPart g x₀)⁻¹ * finPart g x) φ = φ := hx
  rw [unip_mul_eq, ← mul_inv_cancel_left (finPart g x₀) (finPart g x), map_mul, mul_assoc, ← infGL_comm,
    ← mul_assoc, chart_mul_finGL_of_fix φ _ _ hx', chart_mul]

theorem chart_unipotent_translate_continuousOn (φ : Sm E a) (hφ : IsAutForm φ) (g : GA E a) (X : Lie E a) :
    ContinuousOn (fun p : (BlockIx a r → Ad E) × Lie E a => chart φ.1 (unip p.1 * g) p.2)
        (Set.univ ×ˢ invSet E a) ∧
      ContinuousOn (fun p : (BlockIx a r → Ad E) × Lie E a => fderiv ℝ (chart φ.1 (unip p.1 * g)) p.2 X)
        (Set.univ ×ˢ invSet E a) := by
  have hP : Continuous (fun p : (BlockIx a r → Ad E) × Lie E a => lmul (toL (infPart g p.1).val) p.2) := by
    have := ((continuous_infPart g).comp continuous_fst).matrix_mul
      (continuous_snd : Continuous fun p : (BlockIx a r → Ad E) × Matrix (Fin a) (Fin a) (Cinf E) => p.2)
    exact this
  have hQ : Continuous (fun p : (BlockIx a r → Ad E) × Lie E a => lmul (toL (infPart g p.1).val) X) := by
    have := ((continuous_infPart g).comp continuous_fst).matrix_mul
      (continuous_const : Continuous fun _ : (BlockIx a r → Ad E) × Lie E a => (Matrix.of X))
    exact this
  have hinv : ∀ p : (BlockIx a r → Ad E) × Lie E a, p.2 ∈ invSet E a →
      lmul (toL (infPart g p.1).val) p.2 ∈ invSet E a := fun p hp => (infPart g p.1).isUnit.mul hp
  constructor
  · rintro ⟨x₀, y₀⟩ ⟨-, hy₀⟩
    set f₀ := chart φ.1 (finGL E a (finPart g x₀))
    have hf₀ : ContDiffOn ℝ ∞ f₀ (invSet E a) := φ.2 _
    have hA : ContinuousAt (fun p : (BlockIx a r → Ad E) × Lie E a => f₀ (lmul (toL (infPart g p.1).val) p.2))
        (x₀, y₀) :=
      ContinuousAt.comp (g := f₀) (hf₀.continuousOn.continuousAt (isOpen_invSet.mem_nhds (hinv (x₀, y₀) hy₀)))
        hP.continuousAt
    refine (hA.congr ?_).continuousWithinAt
    filter_upwards [(continuous_fst.tendsto (x₀, y₀)).eventually (eventually_chart_eq φ hφ g x₀)] with p hp
    rw [hp]; rfl
  · rintro ⟨x₀, y₀⟩ ⟨-, hy₀⟩
    set f₀ := chart φ.1 (finGL E a (finPart g x₀))
    have hf₀ : ContDiffOn ℝ ∞ f₀ (invSet E a) := φ.2 _
    have hD : ContinuousOn (fun z => fderiv ℝ f₀ z) (invSet E a) :=
      hf₀.continuousOn_fderiv_of_isOpen isOpen_invSet (by simp)
    have hA : ContinuousAt (fun p : (BlockIx a r → Ad E) × Lie E a =>
        fderiv ℝ f₀ (lmul (toL (infPart g p.1).val) p.2) (lmul (toL (infPart g p.1).val) X)) (x₀, y₀) :=
      ContinuousAt.clm_apply
        (ContinuousAt.comp (g := fun z => fderiv ℝ f₀ z)
          (hD.continuousAt (isOpen_invSet.mem_nhds (hinv (x₀, y₀) hy₀))) hP.continuousAt)
        hQ.continuousAt
    refine (hA.congr ?_).continuousWithinAt
    have hy : ∀ᶠ p : (BlockIx a r → Ad E) × Lie E a in 𝓝 (x₀, y₀), p.2 ∈ invSet E a :=
      (continuous_snd.tendsto (x₀, y₀)).eventually (isOpen_invSet.mem_nhds hy₀)
    filter_upwards [(continuous_fst.tendsto (x₀, y₀)).eventually (eventually_chart_eq φ hφ g x₀), hy]
      with p hp hp2
    have hd : DifferentiableAt ℝ f₀ (lmul (toL (infPart g p.1).val) p.2) :=
      (hf₀.contDiffAt (isOpen_invSet.mem_nhds (hinv p hp2))).differentiableAt (by simp)
    change _ = fderiv ℝ (chart φ.1 (unip p.1 * g)) p.2 X
    rw [hp, fderiv_comp _ hd (lmul _).differentiableAt, ContinuousLinearMap.fderiv]
    rfl

theorem chart_jointCont : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : GlobalTheory.CuspRep.Sm E a), GlobalTheory.CuspRep.IsAutForm φ → ∀ (g : GlobalTheory.CuspRep.GA E a) (X : GlobalTheory.CuspRep.Lie E a), ContinuousOn (fun p : (GlobalTheory.CuspRep.BlockIx a r → GlobalTheory.CuspRep.Ad E) × GlobalTheory.CuspRep.Lie E a => GlobalTheory.CuspRep.chart φ.1 (GlobalTheory.CuspRep.unip p.1 * g) p.2) (Set.univ ×ˢ GlobalTheory.CuspRep.invSet E a) ∧ ContinuousOn (fun p : (GlobalTheory.CuspRep.BlockIx a r → GlobalTheory.CuspRep.Ad E) × GlobalTheory.CuspRep.Lie E a => fderiv ℝ (GlobalTheory.CuspRep.chart φ.1 (GlobalTheory.CuspRep.unip p.1 * g)) p.2 X) (Set.univ ×ˢ GlobalTheory.CuspRep.invSet E a) :=
  fun _ _ _ _ _ _ φ hφ g X => chart_unipotent_translate_continuousOn φ hφ g X

end GlobalTheory.CuspRep.JointCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOnStatement
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_unipotent_fderiv_continuousOn : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : GlobalTheory.CuspRep.Sm E a), GlobalTheory.CuspRep.IsAutForm φ → ∀ (g : GlobalTheory.CuspRep.GA E a) (X : GlobalTheory.CuspRep.Lie E a), ContinuousOn (fun p : (GlobalTheory.CuspRep.BlockIx a r → GlobalTheory.CuspRep.Ad E) × GlobalTheory.CuspRep.Lie E a => GlobalTheory.CuspRep.chart φ.1 (GlobalTheory.CuspRep.unip p.1 * g) p.2) (Set.univ ×ˢ GlobalTheory.CuspRep.invSet E a) ∧ ContinuousOn (fun p : (GlobalTheory.CuspRep.BlockIx a r → GlobalTheory.CuspRep.Ad E) × GlobalTheory.CuspRep.Lie E a => fderiv ℝ (GlobalTheory.CuspRep.chart φ.1 (GlobalTheory.CuspRep.unip p.1 * g)) p.2 X) (Set.univ ×ˢ GlobalTheory.CuspRep.invSet E a) := by
  first | exact @GlobalTheory.CuspRep.JointCont.chart_jointCont | exact GlobalTheory.CuspRep.JointCont.chart_jointCont | (intros; apply GlobalTheory.CuspRep.JointCont.chart_jointCont <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg


open GlobalTheory.JointHarm GlobalTheory.FockSeq in
theorem harmonic_homog_of_type : ∀ (p q r s : ℕ),
    (∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P →
      P ∈ harm1 p q r s →
      ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧
    (∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P →
      P ∈ harm2 p q r s →
      ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d) :=
  fun _ _ _ _ =>
    ⟨fun _ P h0 ht hh => isSide_one.homog_of_type isFockIsometry_embedding emb_injective
        Function.bijective_id h0 ht ((mem_harm1 P).1 hh),
      fun _ P h0 ht hh => isSide_two.homog_of_type isFockIsometry_embedding emb_injective
        Prod.swap_bijective h0 ht ((mem_harm2 P).1 hh)⟩

end GlobalTheory.FockAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKTypeStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockHarmonic_homogeneous_of_KType : ∀ (p q r s : ℕ), (∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P → P ∈ harm1 p q r s → ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧ (∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P → P ∈ harm2 p q r s → ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d) := by
  first | exact @GlobalTheory.FockAlg.harmonic_homog_of_type | exact GlobalTheory.FockAlg.harmonic_homog_of_type | (intros; apply GlobalTheory.FockAlg.harmonic_homog_of_type <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAdjoints
noncomputable section
namespace GlobalTheory.FockAdj
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.FockDeg MvPolynomial Matrix

variable {p q r s : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_pderiv {σ : Type} [DecidableEq σ] {ι : MvPolynomial σ ℂ →ₗ[ℂ] H} (hι : IsFockIP ι)
    (i : σ) (P Q : MvPolynomial σ ℂ) :
    inner ℂ (ι (pderiv i P)) (ι Q) = inner ℂ (ι P) (ι (X i * Q)) := by
  rw [← inner_conj_symm, ← inner_X_mul hι, inner_conj_symm]

theorem inner_raiB {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (raiB l P)) (ι Q) = (if linePos l then 1 else -1) * inner ℂ (ι P) (ι (lowB l Q)) := by
  cases hl : linePos l
  · simp only [raiB, lowB, hl, Bool.false_eq_true, if_false]
    show inner ℂ (ι (-pderiv l P)) (ι Q) = -1 * inner ℂ (ι P) (ι (X l * Q))
    rw [map_neg, inner_neg_left, inner_pderiv hι, neg_one_mul]
  · simp only [raiB, lowB, hl, if_true]
    show inner ℂ (ι (X l * P)) (ι Q) = 1 * inner ℂ (ι P) (ι (pderiv l Q))
    rw [inner_X_mul hι, one_mul]

theorem inner_lowB {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (lowB l P)) (ι Q) = (if linePos l then 1 else -1) * inner ℂ (ι P) (ι (raiB l Q)) := by
  cases hl : linePos l
  · simp only [raiB, lowB, hl, Bool.false_eq_true, if_false]
    show inner ℂ (ι (X l * P)) (ι Q) = -1 * inner ℂ (ι P) (ι (-pderiv l Q))
    rw [map_neg, inner_neg_right, inner_X_mul hι, neg_one_mul, neg_neg]
  · simp only [raiB, lowB, hl, if_true]
    show inner ℂ (ι (pderiv l P)) (ι Q) = 1 * inner ℂ (ι P) (ι (X l * Q))
    rw [inner_pderiv hι, one_mul]

theorem inner_omE {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l l' : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (omE l l' P)) (ι Q) =
      (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (omE l' l Q)) := by
  have h1 : inner ℂ (ι (raiB l (lowB l' P))) (ι Q) =
      (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (raiB l' (lowB l Q))) := by
    rw [inner_raiB hι, inner_lowB hι, ← mul_assoc]
    congr 1
    cases linePos l <;> cases linePos l' <;> simp
  unfold omE
  simp only [LinearMap.add_apply, Module.End.mul_apply, map_add (f := _), inner_add_left, inner_add_right,
    mul_add, h1]
  congr 1
  by_cases h : l = l'
  · subst h
    simp [inner_smul_left, inner_smul_right, map_ofNat]
  · simp [h, Ne.symm h]

theorem inner_omAct {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι)
    (M N : Matrix (Ln p q r s) (Ln p q r s) ℂ)
    (h : ∀ l l', N l' l = (if linePos l = linePos l' then 1 else -1) * star (M l l'))
    (P Q : Pol p q r s) :
    inner ℂ (ι (omAct p q r s M P)) (ι Q) = inner ℂ (ι P) (ι (omAct p q r s N Q)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [omAct_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  rw [inner_omE hι, h, starRingEnd_apply]
  ring

theorem adjZ_apply (Z : Mat p q) (a b : Ix p q) :
    adjZ Z a b = (if sameBlock b a then 1 else -1) * star (Z b a) := by
  have hJ : Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [adjZ, hJ, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock]

theorem fock_adjoints : ∀ (p q r s : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : Pol p q r s →ₗ[ℂ] H), IsFockIP ι →
    (∀ (l l' : Ln p q r s) (P Q : Pol p q r s), inner ℂ (ι (omE l l' P)) (ι Q) =
      (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (omE l' l Q))) ∧
    (∀ (Z : Mat p q) (P Q : Pol p q r s), inner ℂ (ι (fockAct1 p q r s Z P)) (ι Q) =
      inner ℂ (ι P) (ι (fockAct1 p q r s (adjZ Z) Q))) ∧
    (∀ (Z : Mat r s) (P Q : Pol p q r s), inner ℂ (ι (fockAct2 p q r s Z P)) (ι Q) =
      inner ℂ (ι P) (ι (fockAct2 p q r s (adjZ Z) Q))) := by
  intro p q r s H _ _ ι hι
  refine ⟨inner_omE hι, fun Z P Q => ?_, fun Z P Q => ?_⟩
  · rw [fockAct1_eq, fockAct1_eq]
    refine inner_omAct hι _ _ ?_ P Q
    rintro ⟨a, c⟩ ⟨b, d⟩
    by_cases e : c = d
    · subst e
      simp [kr1, adjZ_apply, linePos_eq_iff_fst]
    · simp [kr1, e, Ne.symm e]
  · rw [fockAct2_eq, fockAct2_eq]
    refine inner_omAct hι _ _ ?_ P Q
    rintro ⟨a, c⟩ ⟨b, d⟩
    by_cases e : a = b
    · subst e
      simp [kr2, adjZ_apply, linePos_eq_iff_snd]
    · simp [kr2, e, Ne.symm e]

end GlobalTheory.FockAdj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFockJointHarmonicsHighestWeightOfShape
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFockJointHarmonicsHighestWeightOfShape
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.JointHarm

theorem finrank_joint_highest_of_shape :
    ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ), JointShape p q r s μ μ' →
      Module.finrank ℂ ↥(hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (jointHarm p q r s)) = 1 :=
  fun _ _ _ _ μ μ' => (joint_harmonics μ μ').1

end GlobalTheory.JointHarm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFockJointHarmonicsHighestWeightOfShapeStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_fockJointHarmonics_highestWeight_of_shape : ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ), JointShape p q r s μ μ' → Module.finrank ℂ ↥(hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓ Submodule.span ℂ (jointHarm p q r s)) = 1 := by
  first | exact @GlobalTheory.JointHarm.finrank_joint_highest_of_shape | exact GlobalTheory.JointHarm.finrank_joint_highest_of_shape | (intros; apply GlobalTheory.JointHarm.finrank_joint_highest_of_shape <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenterActsByScalarOnEigenforms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenterActsByScalarOnEigenforms
open NumberField

namespace GlobalTheory.CuspRep

theorem Zalg_acts_by_scalar : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (c : (E →+* ℂ) → ℂ → ℂ) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a →
    ∃ s : ℂ, ∀ φ : GlobalTheory.CuspRep.Sm E a, (∀ τ u, GlobalTheory.CuspRep.cap τ u φ = c τ u • φ) → z φ = s • φ := by
  intro E _ _ _ a c z hz
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    exact ⟨c τ u, fun φ hφ => hφ τ u⟩
  | algebraMap r => exact ⟨r, fun φ _ => by simp [Algebra.algebraMap_eq_smul_one]⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s + t, fun φ hφ => by rw [LinearMap.add_apply, hs φ hφ, ht φ hφ, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s * t, fun φ hφ => by rw [Module.End.mul_apply, ht φ hφ, map_smul, hs φ hφ, smul_smul, mul_comm]⟩

end GlobalTheory.CuspRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenterActsByScalarOnEigenformsStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_acts_by_scalar_on_eigenforms : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (c : (E →+* ℂ) → ℂ → ℂ) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a → ∃ s : ℂ, ∀ φ : GlobalTheory.CuspRep.Sm E a, (∀ τ u, GlobalTheory.CuspRep.cap τ u φ = c τ u • φ) → z φ = s • φ := by
  first | exact @GlobalTheory.CuspRep.Zalg_acts_by_scalar | exact GlobalTheory.CuspRep.Zalg_acts_by_scalar | (intros; apply GlobalTheory.CuspRep.Zalg_acts_by_scalar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLineMatrixKroneckerRightFactor
noncomputable section
namespace GlobalTheory.FockParts
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial GlobalTheory.FockDeg

variable {p q r s : ℕ}

theorem sum_lineMatrixKroneckerLeftFactor (Z : Mat p q) (F : Ln p q r s → Ln p q r s → ℂ → Pol p q r s)
    (hF : ∀ l l', F l l' 0 = 0) :
    ∑ l, ∑ l', F l l' (kr1 r s Z l l') = ∑ a, ∑ b, ∑ c, F (a, c) (b, c) (Z a b) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm (f := fun b c => F (a, c) (b, c) (Z a b))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single c]
  · simp [kr1]
  · intro d _ hd
    simp [kr1, Ne.symm hd, hF]
  · simp

theorem sum_lineMatrixKroneckerRightFactor (Z : Mat r s) (F : Ln p q r s → Ln p q r s → ℂ → Pol p q r s)
    (hF : ∀ l l', F l l' 0 = 0) :
    ∑ l, ∑ l', F l l' (kr2 p q Z l l') = ∑ c, ∑ d, ∑ a, F (a, c) (a, d) (Z c d) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm (f := fun d a => F (a, c) (a, d) (Z c d))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [kr2]
  · intro b _ hb
    simp [kr2, Ne.symm hb, hF]
  · simp

theorem explicit_parts : ∀ (p q r s : ℕ), (∀ Z : Mat p q, IsPC Z → ∀ P : Pol p q r s, plusPart (fockAct1 p q r s Z) P = ∑ a, ∑ b, ∑ c, (if linePos ((a, c) : Ln p q r s) = true then Z a b • (X (a, c) * X (b, c) * P) else 0) ∧ minusPart (fockAct1 p q r s Z) P = ∑ a, ∑ b, ∑ c, (if linePos ((a, c) : Ln p q r s) = true then 0 else -(Z a b • pderiv (a, c) (pderiv (b, c) P)))) ∧ (∀ Z : Mat r s, IsPC Z → ∀ P : Pol p q r s, plusPart (fockAct2 p q r s Z) P = ∑ c, ∑ d, ∑ a, (if linePos ((a, c) : Ln p q r s) = true then Z c d • (X (a, c) * X (a, d) * P) else 0) ∧ minusPart (fockAct2 p q r s Z) P = ∑ c, ∑ d, ∑ a, (if linePos ((a, c) : Ln p q r s) = true then 0 else -(Z c d • pderiv (a, c) (pderiv (a, d) P)))) := by
  intro p q r s
  refine ⟨fun Z hZ P => ⟨?_, ?_⟩, fun Z hZ P => ⟨?_, ?_⟩⟩
  · rw [fockAct1_eq, plusPart_omAct (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ), upOp_apply,
      sum_lineMatrixKroneckerLeftFactor Z (fun l l' z => (if linePos l then z else 0) • (X l * X l' * P)) (by simp)]
    simp only [ite_smul, zero_smul]
  · rw [fockAct1_eq, minusPart_omAct (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ), downOp_apply,
      sum_lineMatrixKroneckerLeftFactor Z (fun l l' z => (if linePos l then 0 else -z) • pderiv l (pderiv l' P)) (by simp)]
    simp only [ite_smul, zero_smul, neg_smul]
  · rw [fockAct2_eq, plusPart_omAct (lineMatrixKroneckerRightFactor_eq_zero_of_isPC hZ), upOp_apply,
      sum_lineMatrixKroneckerRightFactor Z (fun l l' z => (if linePos l then z else 0) • (X l * X l' * P)) (by simp)]
    simp only [ite_smul, zero_smul]
  · rw [fockAct2_eq, minusPart_omAct (lineMatrixKroneckerRightFactor_eq_zero_of_isPC hZ), downOp_apply,
      sum_lineMatrixKroneckerRightFactor Z (fun l l' z => (if linePos l then 0 else -z) • pderiv l (pderiv l' P)) (by simp)]
    simp only [ite_smul, zero_smul, neg_smul]

end GlobalTheory.FockParts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsMonHomLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsMonHomLift
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HomLift

theorem eq_one_of_grpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'}
    (z : Over.mk (T.hom ≫ f) ⟶ G) (hz : z.left = (1 : T ⟶ G').left ≫ φ) : z = 1 := by
  have e := h.2 T 1 1 z z hz hz
  rw [_root_.mul_one, ← hz] at e
  exact _root_.mul_eq_left.1 (Over.OverMorphism.ext e)

theorem one_left {S : Scheme.{0}} (T G : Over S) [GrpObj G] :
    (1 : T ⟶ G).left = T.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  rfl

theorem one_eq_unit {S : Scheme.{0}} (G : Over S) [GrpObj G] :
    (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by
  rw [Hom.one_def, toUnit_unit, Category.id_comp]

theorem existsUnique_isMonHom_lift :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left),
    IsGrpPullback A₀ A (spMap π) i → IsGrpPullback B₀ B (spMap π) j → IsAbelianScheme A → IsAbelianScheme B →
    ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (φ : A ⟶ B), i ≫ φ.left = f₀.left ≫ j → ∃! f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j := by
  intro R R₀ _ _ π hπ hnil A₀ B₀ _ _ A B _ _ i j hA hB hAab hBab f₀ _ φ hφ
  obtain ⟨z, hz⟩ : ∃ z : Over.mk (A₀.hom ≫ spMap π) ⟶ A, z.left = i := ⟨Over.homMk i hA.1.w, rfl⟩
  have hzl : ∀ g : A ⟶ B, (z ≫ g).left = i ≫ g.left := fun g => by rw [Over.comp_left, hz]
  have hu : (1 : A₀ ⟶ A₀).left ≫ i = (1 : Over.mk (A₀.hom ≫ spMap π) ⟶ A).left := by
    have := eq_one_of_grpPullback hA (T := A₀) (Over.homMk ((1 : A₀ ⟶ A₀).left ≫ i) (by
      change (_ ≫ i) ≫ A.hom = A₀.hom ≫ spMap π
      rw [Category.assoc, hA.1.w, ← Category.assoc, Over.w])) rfl
    rw [← this]; rfl
  have h1 : (1 : A₀ ⟶ A₀) ≫ f₀ = 1 := by
    rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  have hc : z ≫ ((1 : A ⟶ A) ≫ φ) = 1 := by
    apply eq_one_of_grpPullback hB
    rw [← Category.assoc, comp_one, Over.comp_left, ← h1, Over.comp_left, Category.assoc, ← hφ,
      ← Category.assoc, hu]
  obtain ⟨f, hfdef⟩ : ∃ f : A ⟶ B, f = φ * ((1 : A ⟶ A) ≫ φ)⁻¹ := ⟨_, rfl⟩
  have hηf : η[A] ≫ f = η[B] := by
    have e : η[A] ≫ ((1 : A ⟶ A) ≫ φ) = η[A] ≫ φ := by
      rw [← Category.assoc, comp_one, one_eq_unit]
    rw [hfdef, comp_mul, GrpObj.comp_inv, e, mul_inv_cancel, one_eq_unit]
  have hf : IsMonHom f := GlobalTheory.rigidity_holds (Sp R) A B hAab hBab f hηf
  have hfl : i ≫ f.left = f₀.left ≫ j := by
    rw [← hzl, hfdef, comp_mul, GrpObj.comp_inv, hc, inv_one, _root_.mul_one, hzl, hφ]
  refine ⟨f, ⟨hf, hfl⟩, fun g ⟨hg, hgl⟩ => ?_⟩
  obtain ⟨d, hddef⟩ : ∃ d : A ⟶ B, d = g * f⁻¹ := ⟨_, rfl⟩
  have hzg : z ≫ g = z ≫ f := Over.OverMorphism.ext (by rw [hzl, hzl, hgl, hfl])
  have hzd : z ≫ d = 1 := by rw [hddef, comp_mul, GrpObj.comp_inv, hzg, mul_inv_cancel]
  have hηd : η[A] ≫ d = η[B] := by
    rw [hddef, comp_mul, GrpObj.comp_inv, hηf, IsMonHom.one_hom, mul_inv_cancel, one_eq_unit]
  have key := GlobalTheory.Rigidity.eq_comp_section R R₀ π hπ hnil A B A₀ i hA.1 hAab.smooth hAab.proper
    hAab.geomConnected (η[A] : 𝟙_ (Over (Sp R)) ⟶ A).left (Over.w _) d
    (spMap π ≫ (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left) (by
      rw [← hzl, hzd, one_left]
      exact Category.assoc _ _ _)
  have hd : d = 1 := by
    apply Over.OverMorphism.ext
    rw [key, one_left, ← hηd]
    rfl
  rw [hddef] at hd
  exact mul_inv_eq_one.1 hd

end GlobalTheory.HomLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsMonHomLiftStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_isMonHom_lift_of_grpPullback_abelian : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left),
    IsGrpPullback A₀ A (spMap π) i → IsGrpPullback B₀ B (spMap π) j → IsAbelianScheme A → IsAbelianScheme B →
    ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (φ : A ⟶ B), i ≫ φ.left = f₀.left ≫ j → ∃! f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j := by
  first | exact @GlobalTheory.HomLift.existsUnique_isMonHom_lift | exact GlobalTheory.HomLift.existsUnique_isMonHom_lift | (intros; apply GlobalTheory.HomLift.existsUnique_isMonHom_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJointHarmonicsHighestWeightEqBotOfNotShape
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJointHarmonicsHighestWeightEqBotOfNotShape
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg

theorem jointHarm_hw_eq_bot : ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
    ¬ JointShape p q r s μ μ' →
      hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (jointHarm p q r s) = ⊥ :=
  fun _ _ _ _ μ μ' => (GlobalTheory.JointHarm.joint_harmonics μ μ').2

end GlobalTheory.FockAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJointHarmonicsHighestWeightEqBotOfNotShapeStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockJointHarmonics_highestWeight_eq_bot_of_not_shape : ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ), ¬ JointShape p q r s μ μ' → hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓ Submodule.span ℂ (jointHarm p q r s) = ⊥ := by
  first | exact @GlobalTheory.FockAlg.jointHarm_hw_eq_bot | exact GlobalTheory.FockAlg.jointHarm_hw_eq_bot | (intros; apply GlobalTheory.FockAlg.jointHarm_hw_eq_bot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHarishChandraDiscreteSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHarishChandraDiscreteSeries
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section

namespace GlobalTheory.DiscreteSeriesUnitary

def unitaryModule {p q : ℕ} {T : GrpData p q} (D : DSRep T) : UGKMod p q where
  M := D.HK
  ip := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => inner ℂ (D.ι x) (D.ι y))
    (fun x y z => by simp only [map_add (f := _), inner_add_left])
    (fun c x y => by simp only [map_smul, inner_smul_left, smul_eq_mul])
    (fun x y z => by simp only [map_add (f := _), inner_add_right])
    (fun c x y => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply])
  herm x y := inner_conj_symm (D.ι y) (D.ι x)
  pos x hx := by
    have h : D.ι x ≠ 0 := fun h => hx (D.ι_inj (h.trans (map_zero D.ι).symm))
    exact re_inner_self_pos (𝕜 := ℂ).2 h
  adj Z x y := GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint p q T D.U D.HK D.ι D.der Z x y

theorem exists_unitary : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T),
    ∃ M : UGKMod p q, M.M = D.HK :=
  fun _ _ _ D => ⟨unitaryModule D, rfl⟩

end GlobalTheory.DiscreteSeriesUnitary

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHarishChandraDiscreteSeriesStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_harishChandra_discreteSeries : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T), ∃ M : UGKMod p q, M.M = D.HK := by
  first | exact @GlobalTheory.DiscreteSeriesUnitary.exists_unitary | exact GlobalTheory.DiscreteSeriesUnitary.exists_unitary | (intros; apply GlobalTheory.DiscreteSeriesUnitary.exists_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanCompactOrbitLieDerivative
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanCompactOrbitLieDerivative
open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep.KFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem cptRep_lie (k : Kinf E a) (X : Lie E a) (ψ : Sm E a) :
    cptRep E a k (lie E a X ψ) =
      lie E a (toL ((Unitary.toUnits k).val * Matrix.of X * (Unitary.toUnits k)⁻¹.val)) (cptRep E a k ψ) := by
  set y : GL (Fin a) (Cinf E) := Unitary.toUnits k with hy
  set Z : Lie E a := toL (y.val * Matrix.of X * y⁻¹.val) with hZ
  refine Subtype.ext (funext fun g => ?_)
  change lieD X ψ.1 (g * infGL E a y) = lieD Z (fun x => ψ.1 (x * infGL E a y)) g
  rw [← chart_val (lieD X ψ.1) g y, chart_lieD ψ.2 X g (val_mem_invSet y), lieD, chart_rt_inf]
  have e1 : rmul (toL y.val) (oneL E a) = toL y.val := one_mul (Matrix.of (toL y.val))
  rw [fderiv_comp _ (by rw [e1]; exact (contDiffAt_chart ψ.2 g (val_mem_invSet y)).differentiableAt (by simp))
    (rmul (toL y.val)).differentiableAt, ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, e1]
  congr 1
  change (y.val : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of X = (y.val * Matrix.of X * y⁻¹.val) * (y.val : Matrix (Fin a) (Fin a) (Cinf E))
  rw [mul_assoc, Units.inv_mul, mul_one]

theorem kfin_lie (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Lie E a) (φ : Sm E a)
    (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k (lie E a X φ))) := by
  set V := Submodule.span ℂ (Set.range fun k => cptRep E a k φ)
  let b := Module.finBasis ℝ (Lie E a)
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, V.map (lie E a (b i))) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  rw [SetLike.mem_coe]
  change cptRep E a k (lie E a X φ) ∈ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cptRep_lie, ← b.sum_repr (toL _), map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.mem_iSup_of_mem i
    (Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, rfl⟩)))

end GlobalTheory.CuspRep.KFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanCompactOrbitLieDerivativeStatement
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_span_compact_orbit_lieDerivative : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) (φ : GlobalTheory.CuspRep.Sm E a), FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => GlobalTheory.CuspRep.cptRep E a k φ)) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => GlobalTheory.CuspRep.cptRep E a k (GlobalTheory.CuspRep.lie E a X φ))) := by
  first | exact @GlobalTheory.CuspRep.KFin.kfin_lie | exact GlobalTheory.CuspRep.KFin.kfin_lie | (intros; apply GlobalTheory.CuspRep.KFin.kfin_lie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticOnNhdOrbitPol
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticOnNhdOrbitPol
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg


open GlobalTheory.OrbitAnalytic in
theorem analyticOnNhd_orbit_pol : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), ∀ Z ∈ upq (p * r + q * s) (p * s + q * r), ∀ (P : Pol p q r s), AnalyticOnNhd ℝ (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) Set.univ ∧ ∀ k : ℕ, iteratedDeriv k (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) 0 = F.ι ((omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z) ^ k) P) := by
  intro p q r s T0 T1 T2 F Z hZ P
  set Y := Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z with hY
  let f : ℕ → ℝ → F.H := fun k t => F.Om (T0.expt (t • Z)) (F.ι ((omAct p q r s Y ^ k) P))
  have hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t := fun k t =>
    hasDerivAt_orbit (fun t => F.Om (T0.expt (t • Z)))
      (fun s t => by simp only [T0.expt_add Z hZ, map_mul]) _ _
      (by simpa only [pow_succ', Module.End.mul_apply] using F.der Z hZ ((omAct p q r s Y ^ k) P)) t
  have h0 : (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) = f 0 := by
    funext t; simp [f]
  rw [h0]
  refine ⟨fun a _ => ?_, fun k => ?_⟩
  · set S : ℝ := 4 * ∑ l, ∑ l', ‖Y l l'‖ with hS
    have hS0 : 0 ≤ S := by positivity
    refine analyticAt_of_bound f hf ((2 : ℝ) ^ ((P.totalDegree : ℝ) / 2 + 1) * ‖F.ι P‖) (S + 1)⁻¹
      (by positivity) (fun k t => ?_) a
    have hb := (GlobalTheory.T.fockAction_pow_analyticVector_norm_le p q r s F.H F.ι (isFockIsometry_of_fockData F) Y P.totalDegree k P le_rfl).2
    simp only [f]
    rw [F.isom]
    refine hb.trans ?_
    rw [← hS, inv_pow, div_inv_eq_mul]
    calc _ ≤ (S + 1) ^ k * (k.factorial : ℝ) * (2 : ℝ) ^ ((P.totalDegree : ℝ) / 2 + 1) * ‖F.ι P‖ := by
          gcongr; linarith
      _ = _ := by ring
  · have hit : ∀ k, iteratedDeriv k (f 0) = f k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [iteratedDeriv_succ, ih]; funext t; exact (hf k t).deriv
    rw [hit]
    simp [f, T0.expt_zero]

end GlobalTheory.FockAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticOnNhdOrbitPolStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticOnNhd_om_expt_and_iteratedDeriv_zero_eq : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), ∀ Z ∈ upq (p * r + q * s) (p * s + q * r), ∀ (P : Pol p q r s), AnalyticOnNhd ℝ (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) Set.univ ∧ ∀ k : ℕ, iteratedDeriv k (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) 0 = F.ι ((omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z) ^ k) P) := by
  first | exact @GlobalTheory.FockAlg.analyticOnNhd_orbit_pol | exact GlobalTheory.FockAlg.analyticOnNhd_orbit_pol | (intros; apply GlobalTheory.FockAlg.analyticOnNhd_orbit_pol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDetEqLinearCombinationNatNodes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDetEqLinearCombinationNatNodes
open NumberField GlobalTheory.CuspRep

noncomputable section

open Polynomial Finset

namespace GlobalTheory.CuspRep

theorem eval_eq_sum_lagrange_nodes (b : ℕ) (u : ℂ) (f : ℂ[X]) (hf : f.degree < ((b + 1 : ℕ) : WithBot ℕ)) :
    f.eval u = ∑ j : Fin (b + 1),
      (Lagrange.basis univ (fun j : Fin (b + 1) => ((j : ℕ) : ℂ)) j).eval u * f.eval ((j : ℕ) : ℂ) := by
  have hinj : Set.InjOn (fun j : Fin (b + 1) => ((j : ℕ) : ℂ)) (univ : Finset (Fin (b + 1))) := by
    intro x _ y _ h
    exact Fin.ext (by simpa using h)
  have e := Lagrange.eq_interpolate (s := univ) hinj (f := f) (by simpa using hf)
  conv_lhs => rw [e]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, mul_comm]

theorem cap_eq_sum_nodes (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ) (τ : E →+* ℂ) (u : ℂ) :
    ∃ w : Fin (b + 1) → ℂ, cap (a := b) τ u = ∑ j : Fin (b + 1), w j • cap (a := b) τ ((j : ℕ) : ℂ) := by
  obtain ⟨c, -, hc⟩ := GlobalTheory.qdet_polyMap_monic (Module.End ℂ (Sm E b)) b (Eop τ)
  have hcap : ∀ v : ℂ, cap (a := b) τ v =
      ∑ i ∈ range (b + 1), ((X + C (((b : ℂ) - 1) / 2)) ^ i).eval v • c i := by
    intro v
    rw [cap, hc]
    simp only [eval_pow, eval_add, eval_X, eval_C]
  refine ⟨fun j => (Lagrange.basis univ (fun j : Fin (b + 1) => ((j : ℕ) : ℂ)) j).eval u, ?_⟩
  simp_rw [hcap, smul_sum, smul_smul]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [← sum_smul, ← eval_eq_sum_lagrange_nodes]
  have hi' : i < b + 1 := mem_range.1 hi
  rw [degree_pow, degree_X_add_C]
  simp only [nsmul_eq_mul, mul_one]
  exact_mod_cast hi'

end GlobalTheory.CuspRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDetEqLinearCombinationNatNodesStatement
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliDet_eq_linearCombination_nat_nodes : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ) (τ : E →+* ℂ) (u : ℂ), ∃ w : Fin (b + 1) → ℂ, cap (a := b) τ u = ∑ j : Fin (b + 1), w j • cap (a := b) τ ((j : ℕ) : ℂ) := by
  first | exact @GlobalTheory.CuspRep.cap_eq_sum_nodes | exact GlobalTheory.CuspRep.cap_eq_sum_nodes | (intros; apply GlobalTheory.CuspRep.cap_eq_sum_nodes <;> assumption)
end
end
