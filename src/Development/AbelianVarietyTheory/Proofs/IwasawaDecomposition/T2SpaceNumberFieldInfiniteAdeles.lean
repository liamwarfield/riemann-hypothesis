module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
noncomputable section

namespace GlobalTheory.GaugeEx

open scoped TensorProduct NNReal ENNReal
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Inst

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]

scoped instance modTopTens : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
scoped instance borelTens : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
scoped instance borelHA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    BorelSpace (HA R σ J) := ⟨rfl⟩

variable [FiniteDimensional F E] [IsTopologicalRing R]

scoped instance topRingTens : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _

scoped instance lcTens [LocallyCompactSpace R] : LocallyCompactSpace (R ⊗[F] E) := by
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) R
  exact e.isClosedEmbedding.locallyCompactSpace

scoped instance scTens [SecondCountableTopology R] : SecondCountableTopology (R ⊗[F] E) := by
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) R
  exact e.secondCountableTopology

scoped instance t2Space_scalarTensorExt [T2Space R] : T2Space (R ⊗[F] E) := by
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) R
  exact e.isEmbedding.t2Space

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

scoped instance topGroupHA : IsTopologicalGroup (HA R σ J) :=
  inferInstanceAs (IsTopologicalGroup (HR R σ J))

theorem continuous_mat : Continuous fun g : HA R σ J =>
    ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
  Units.continuous_val.comp continuous_subtype_val

scoped instance contSMulHA (n : ℕ) : ContinuousSMul (HA R σ J) (Fin n → Fin M → R ⊗[F] E) where
  continuous_smul := continuous_pi fun a =>
    ((continuous_mat R σ J).comp continuous_fst).matrix_mulVec
      ((continuous_apply a).comp continuous_snd)

variable [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]

scoped instance lcHA : LocallyCompactSpace (HA R σ J) := (GlobalTheory.AdelicUnitaryTop.lcsc_HA R σ M J).1
scoped instance scHA : SecondCountableTopology (HA R σ J) :=
  (GlobalTheory.AdelicUnitaryTop.lcsc_HA R σ M J).2.1
scoped instance t2HA : T2Space (HA R σ J) := (GlobalTheory.AdelicUnitaryTop.lcsc_HA R σ M J).2.2

end Inst

section AdeleInst

variable (F : Type) [Field F] [NumberField F]

scoped instance borelAF : BorelSpace (AF F) := ⟨rfl⟩
scoped instance borelAinf : BorelSpace (Ainf F) := ⟨rfl⟩
scoped instance borelAf : BorelSpace (Af F) := ⟨rfl⟩
scoped instance borelFv (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (Fv F v) := ⟨rfl⟩
scoped instance lcAF : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
scoped instance scAF : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
scoped instance t2AF : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
scoped instance lcAf : LocallyCompactSpace (Af F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
scoped instance scAf : SecondCountableTopology (Af F) :=
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
scoped instance t2Af : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
scoped instance scAinf : SecondCountableTopology (Ainf F) :=
  GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
scoped instance t2Space_numberFieldInfiniteAdeles : T2Space (Ainf F) := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field F
scoped instance properFv (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (Fv F v) :=
  GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v

end AdeleInst

def Nice (R : Type) [CommRing R] [TopologicalSpace R] : Prop :=
  IsArtinianRing R ∧ IsReduced R ∧ IsOpenUnits R ∧
    ∃ U : Set R, IsOpen U ∧ (1 : R) ∈ U ∧ ∃ s : R → R, ContinuousOn s U ∧ s 1 = 1 ∧ ∀ u ∈ U, s u * s u = u


open Classical in
def modu (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [LocallyCompactSpace S]
    (u : S) : ℝ≥0 :=
  if h : IsUnit u then distribHaarChar S h.unit else 0

def tupMeas {S : Type} [MeasurableSpace S] (lam : Measure S) (n M : ℕ) : Measure (Fin n → Fin M → S) :=
  Measure.pi fun _ => Measure.pi fun _ => lam

def lrAct {S : Type} [CommRing S] {n M : ℕ} (g : Matrix (Fin M) (Fin M) S) (γ : Matrix (Fin n) (Fin n) S)
    (X : Fin n → Fin M → S) : Fin n → Fin M → S :=
  fun a => g.mulVec fun i => ∑ c, X c i * γ c a

section Local

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)

def FibAt [TopologicalSpace R] [MeasurableSpace R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R) (β : R)
    (m : Measure (Fin 1 → Fin M → R ⊗[F] E)) : Prop :=
  ∃ fib : R → Measure (Fin 1 → Fin M → R ⊗[F] E),
    IsFibreFamily μ (fun X => qR R σ J (X 0)) id Set.univ ν {c | IsUnit c} fib ∧ fib β = m

def IsInvTup [TopologicalSpace R] {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (m : Measure (Fin n → Fin M → R ⊗[F] E)) : Prop :=
  ∀ g : HA R σ J, m.map (fun X => g • X) = m

def OnOrbit [TopologicalSpace R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E)
    (m : Measure (Fin 1 → Fin M → R ⊗[F] E)) : Prop :=
  m {y | ¬ ∃ g : HA R σ J, g • ratTup (F := F) R x = y} = 0

def IsSec {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E)
    (s : (Fin 1 → Fin M → R ⊗[F] E) → HA R σ J) : Prop :=
  ∀ y, (∃ g : HA R σ J, g • ratTup (F := F) R x = y) → s y • ratTup (F := F) R x = y

def pairOf {M : ℕ} (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (B : Matrix (Fin (M + 1)) (Fin M) E)
    (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (g : HA R σ J) (y' : Fin 1 → Fin M → R ⊗[F] E) :
    Fin 2 → Fin (M + 1) → R ⊗[F] E :=
  ![y 0, ((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix _ _ (R ⊗[F] E)).mulVec
    ((B.map (inclR R)).mulVec (y' 0))]

def TwoStep [TopologicalSpace R] {M : ℕ} (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E)
    (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E)
    (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E))
    (N : Measure (Fin 2 → Fin (M + 1) → R ⊗[F] E)) : Prop :=
  ∀ f : (Fin 2 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable f → ∀ s, IsSec R σ J x s →
    ∫⁻ X, f X ∂N = ∫⁻ y, ∫⁻ y', f (pairOf R σ J B y (s y) y') ∂m' ∂m

def gram3 {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin 2 → Fin M → R ⊗[F] E) : R × (R ⊗[F] E) × R :=
  (qR R σ J (X 0), hR R σ J (X 0) (X 1), qR R σ J (X 1))

def StepData {M : ℕ} (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (β : F)
    (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) : Prop :=
  IsHermND σ J ∧ β ≠ 0 ∧ hE σ J (x 0) (x 0) = algebraMap F E β ∧
    (∀ j, hE σ J (x 0) (fun i => B i j) = 0) ∧
    J' = Formalism.UG.cT (σ : E →+* E) B * J * B ∧ IsHermND σ J'

def consCol {M : ℕ} (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E) :
    Matrix (Fin (M + 1)) (Fin (M + 1)) E :=
  Matrix.of fun i => Fin.cons (α := fun _ => E) (x 0 i) (B i)

def FrameRelR {M M' : ℕ} (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E)
    (B : Matrix (Fin M) (Fin M') E) (g : HA R σ J) (g' : HA R σ J') : Prop :=
  ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * B.map (inclR R) =
    B.map (inclR R) *
      ((HA.mat R σ J' g' : GL (Fin M') (R ⊗[F] E)) : Matrix (Fin M') (Fin M') (R ⊗[F] E))

end Local

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def prInf : AF F ⊗[F] E →+* Ainf F ⊗[F] E :=
  (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom

def prV (v : HeightOneSpectrum (𝓞 F)) : AF F ⊗[F] E →+* Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom.comp
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

theorem projInf_apply {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n) (i : Fin M) :
    projInf X a i = prInf (X a i) := rfl

theorem projV_apply (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E)
    (a : Fin n) (i : Fin M) : projV v (projFin X) a i = prV v (X a i) := rfl

variable {d : ℕ} (b : Module.Basis (Fin d) F E)

def intV (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v ⊗[F] E) :=
  {y | ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F}

theorem mem_latV_iff (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ} (Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    Y ∈ latV b v ↔ ∀ a i, Y a i ∈ intV b v := Iff.rfl

structure StdMeas where

  lamI : Measure (Ainf F ⊗[F] E)

  lamV : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v ⊗[F] E)

  nuI : Measure (Ainf F)

  nuV : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)
  haar_lamI : lamI.IsAddHaarMeasure
  haar_lamV : ∀ v, (lamV v).IsAddHaarMeasure
  haar_nuI : nuI.IsAddHaarMeasure
  haar_nuV : ∀ v, (nuV v).IsAddHaarMeasure
  lamV_int : ∀ v, lamV v (intV b v) = 1
  nuV_int : ∀ v, nuV v (v.adicCompletionIntegers F : Set (Fv F v)) = 1

def tailProd {n M : ℕ} (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ℝ≥0∞ :=
  ENNReal.ofReal (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (mv v.1 (latV b v.1)).toReal)

def Conv {n M : ℕ} (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) : Prop :=
  IsFiniteMeasureOnCompacts mi ∧ (∀ v, IsFiniteMeasureOnCompacts (mv v)) ∧
    Summable fun v => |(mv v (latV b v)).toReal - 1|

def IsProd {n M : ℕ} (ν : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) : Prop :=
  Conv b mi mv ∧
  ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞),
    Measurable fi → (∀ v, Measurable (fv v)) →
    ∫⁻ X in {X | ∀ v ∉ S, projV v (projFin X) ∈ latV b v},
        fi (projInf X) * ∏ v ∈ S, fv v (projV v (projFin X)) ∂ν =
      (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * tailProd b mv S

variable {b} (s : StdMeas b) (σ : E →ₐ[F] E)

def IsStdX {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (β : F)
    (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) : Prop :=
  ∃ (mi : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E))
    (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
    FibAt (Ainf F) σ J (tupMeas s.lamI 1 M) s.nuI (algebraMap F _ β) mi ∧
    (∀ v, FibAt (Fv F v) σ J (tupMeas (s.lamV v) 1 M) (s.nuV v) (algebraMap F _ β) (mv v)) ∧
    IsProd b ν mi mv

def StepRel {M : ℕ} (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (β : F)
    (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E)
    (μ : Measure (HA (AF F) σ J)) (μ' : Measure (HA (AF F) σ J')) : Prop :=
  ∀ ν, IsStdX s σ J β ν → ∀ e : Hstab (AF F) σ J x ≃* HA (AF F) σ J',
    (∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g)) →
    IsCompatible F E σ (M + 1) J x μ (μ'.map e.symm) ν

end Global

end GlobalTheory.GaugeEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNhdsOneUnitaryGroupRationalPointEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNhdsOneUnitaryGroupRationalPointEqOne
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem exists_nhds_one_rational_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), ∃ U ∈ nhds (1 : HA (AF F) σ J), ∀ g ∈ U, (∃ γ : HFinIn (AF F) σ J, γ • (1 : HA (AF F) σ J) = g) → g = 1 := by
  intro F E _ _ _ _ _ σ M J
  have hd := GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J
  have h1 : ({1} : Set (HFinIn (AF F) σ J)) ∈ nhds (1 : HFinIn (AF F) σ J) :=
    (isOpen_discrete _).mem_nhds rfl
  obtain ⟨U, hU, hsub⟩ := (mem_nhds_subtype _ _ _).1 h1
  refine ⟨U, hU, ?_⟩
  rintro g hg ⟨γ, rfl⟩
  have hγ : γ • (1 : HA (AF F) σ J) = (γ.1 : HR (AF F) σ J) := mul_one (γ.1 : HR (AF F) σ J)
  rw [hγ] at hg ⊢
  have h2 : γ = 1 := hsub hg
  rw [h2]
  rfl

end GlobalTheory.Mem.Vol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNhdsOneUnitaryGroupRationalPointEqOneStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_one_unitaryGroup_rationalPoint_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), ∃ U ∈ nhds (1 : HA (AF F) σ J), ∀ g ∈ U, (∃ γ : HFinIn (AF F) σ J, γ • (1 : HA (AF F) σ J) = g) → g = 1 := by
  first | exact @GlobalTheory.Mem.Vol.exists_nhds_one_rational_eq_one | exact GlobalTheory.Mem.Vol.exists_nhds_one_rational_eq_one | (intros; apply GlobalTheory.Mem.Vol.exists_nhds_one_rational_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEq
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem discreteTopology_subgroup_of_nhds_one {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Γ : Subgroup G) (h : ∃ U ∈ nhds (1 : G), ∀ g ∈ U, (∃ γ : Γ, γ • (1 : G) = g) → g = 1) :
    DiscreteTopology Γ := by
  obtain ⟨U, hU, h⟩ := h
  refine discreteTopology_of_isOpen_singleton_one ?_
  obtain ⟨V, hVU, hV, h1⟩ := mem_nhds_iff.1 hU
  have e : ({1} : Set Γ) = Subtype.val ⁻¹' V := by
    ext γ
    constructor
    · rintro rfl
      exact h1
    · intro hγ
      exact Subtype.ext (h _ (hVU hγ) ⟨γ, by simp [Subgroup.smul_def]⟩)
  rw [e]
  exact hV.preimage continuous_subtype_val

theorem fundamentalDomain_exists_measure_eq_of_discrete {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] :
    (∃ 𝓕, IsFundamentalDomain Γ 𝓕 μ) ∧
      ∀ 𝓕 𝓕', IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Γ 𝓕' μ → μ 𝓕 = μ 𝓕' ∧ μ 𝓕 ≠ 0 := by
  have := GlobalTheory.countable_of_discrete_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup Γ
  exact ⟨⟨D, hD μ⟩, fun 𝓕 𝓕' h h' => ⟨h.measure_eq h', h.measure_ne_zero (NeZero.ne μ)⟩⟩

theorem fundamentalDomain_adelicUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J)), μ.IsHaarMeasure → (∃ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ) ∧ ∀ 𝓕 𝓕', IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕' μ → μ 𝓕 = μ 𝓕' ∧ μ 𝓕 ≠ 0 := by
  intro F E _ _ _ _ _ σ M J μ hμ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have := (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ M J).2.1
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : DiscreteTopology Γ := discreteTopology_subgroup_of_nhds_one Γ (GlobalTheory.T.exists_nhds_one_unitaryGroup_rationalPoint_eq_one F E σ M J)
  exact fundamentalDomain_exists_measure_eq_of_discrete Γ μ

end GlobalTheory.Mem.Vol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEqStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamentalDomain_unitaryAdelic_exists_measure_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J)), μ.IsHaarMeasure → (∃ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ) ∧ ∀ 𝓕 𝓕', IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕' μ → μ 𝓕 = μ 𝓕' ∧ μ 𝓕 ≠ 0 := by
  first | exact @GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary | exact GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary | (intros; apply GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolInfIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem bijective_fam (σ : E →ₐ[F] E) {I : Type} (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ))
    (h : IsCMExt F E σ) (hτ : IsCMFam τ) (hθ : ∀ i, IsInfEmb (τ i) (θ i)) :
    Function.Bijective (fun (z : Ainf F ⊗[F] E) (i : I) => θ i z) := by
  obtain ⟨hF, hE, h2, hσ⟩ := h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc' : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := hσ
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc : c ≠ 1 := by
    intro h1
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc', h1]
    rfl
  choose θ0 h0 h0' using fun φ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) φ
  have hΨ : ∀ φ : E →+* ℂ, φ ∈ Set.range τ ↔ ComplexEmbedding.conjugate φ ∉ Set.range τ := by
    intro φ
    constructor
    · rintro ⟨i, rfl⟩ ⟨j, hj⟩
      have : j = i := hτ.1 (by
        show InfinitePlace.mk (τ j) = InfinitePlace.mk (τ i)
        rw [hj, InfinitePlace.mk_conjugate_eq])
      subst this
      exact hnr _ hj.symm
    · intro hn
      obtain ⟨i, hi⟩ := hτ.2 (InfinitePlace.mk φ)
      rcases InfinitePlace.mk_eq_iff.1 hi with e | e
      · exact ⟨i, e⟩
      · refine absurd ⟨i, ?_⟩ hn
        rw [← e]
        ext x
        simp
  have hb := GlobalTheory.InfAdeleCM.bijective c h2 hc hc' θ0
    (fun φ => GlobalTheory.InfAdeleCM.hom_tmul φ (θ0 φ) (h0 φ) (h0' φ)) (Set.range τ) hΨ
  have hinj : Function.Injective τ := fun i j hij => hτ.1 (by
    show InfinitePlace.mk (τ i) = InfinitePlace.mk (τ j)
    rw [hij])
  let u : I ≃ Set.range τ := Equiv.ofInjective τ hinj
  have he : (fun (z : Ainf F ⊗[F] E) (i : I) => θ i z) =
      (Equiv.arrowCongr u.symm (Equiv.refl ℂ)) ∘ (fun (z : Ainf F ⊗[F] E) (φ : Set.range τ) => θ0 φ.1 z) := by
    funext z i
    rw [GlobalTheory.Mem.VolEmb.infEmb_unique (τ i) (θ i) (θ0 (τ i)) (hθ i) ⟨h0 _, h0' _⟩]
    rfl
  rw [he]
  exact (Equiv.bijective _).comp hb

theorem infEmb_sigR (σ : E →ₐ[F] E) (τ : E →+* ℂ) (θ : Ainf F ⊗[F] E →+* ℂ)
    (h : IsCMExt F E σ) (hθ : IsInfEmb τ θ) (z : Ainf F ⊗[F] E) :
    θ (sigR (Ainf F) σ z) = star (θ z) := by
  obtain ⟨hF, -, -, hσ⟩ := h
  have hθ' := GlobalTheory.InfAdeleCM.hom_tmul τ θ hθ.1 hθ.2
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    show θ (a ⊗ₜ[F] σ x) = starRingEnd ℂ _
    rw [hθ', hθ', map_mul, GlobalTheory.InfAdeleCM.conj_ext, hσ]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, star_add]

theorem exists_infAdele_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)), IsCMExt F E σ → IsCMFam τ → (∀ i, IsInfEmb (τ i) (θ i)) → ∃ e : (Ainf F ⊗[F] E) ≃+* (I → ℂ), (∀ x i, e x i = θ i x) ∧ Continuous e ∧ Continuous e.symm ∧ ∀ x i, e (sigR (Ainf F) σ x) i = star (e x i) := by
  intro F E _ _ _ _ _ σ I _ τ θ h hτ hθ
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)
  haveI : LocallyCompactSpace (Ainf F ⊗[F] E) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e0.secondCountableTopology
  have hb : Function.Bijective (Pi.ringHom θ : Ainf F ⊗[F] E →+* (I → ℂ)) := bijective_fam σ τ θ h hτ hθ
  let e : (Ainf F ⊗[F] E) ≃+* (I → ℂ) := RingEquiv.ofBijective _ hb
  have hc : Continuous e := continuous_pi fun i =>
    IsModuleTopology.continuous_of_ringHom (R := Ainf F) (θ i) (hθ i).2
  have ho : IsOpenMap e :=
    AddMonoidHom.isOpenMap_of_sigmaCompact e.toAddEquiv.toAddMonoidHom e.surjective hc
  refine ⟨e, fun _ _ => rfl, hc, ?_, fun x i => infEmb_sigR σ (τ i) (θ i) h (hθ i) x⟩
  exact (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous

end GlobalTheory.Mem.VolInfIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmTypeStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archAdeleTensor_equiv_complex_cmType : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)), IsCMExt F E σ → IsCMFam τ → (∀ i, IsInfEmb (τ i) (θ i)) → ∃ e : (Ainf F ⊗[F] E) ≃+* (I → ℂ), (∀ x i, e x i = θ i x) ∧ Continuous e ∧ Continuous e.symm ∧ ∀ x i, e (sigR (Ainf F) σ x) i = star (e x i) := by
  first | exact @GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv | exact GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv | (intros; apply GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupModTypePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupModTypePrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.LevMod

open GlobalTheory.CongLevel

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))

def RedTo (g : Sp E n ≃ₗ[E] Sp E n) (hbar : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) : Prop :=
  ∀ x ∈ stdAt E n P, redV P (g x) = hbar.1.mulVec (redV P x)

variable {P}

theorem RedTo.one : RedTo P (1 : Sp E n ≃ₗ[E] Sp E n) 1 := fun x _ => by
  rw [Units.val_one, Matrix.one_mulVec]; rfl

theorem RedTo.mul {g g' : Sp E n ≃ₗ[E] Sp E n} {a b : GL (Fin n) (𝓞 E ⧸ P.asIdeal)} (hg' : g' ∈ GLint E n P)
    (h : RedTo P g a) (h' : RedTo P g' b) : RedTo P (g * g') (a * b) := fun x hx => by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← h' x hx]
  exact h _ ((hg' x).2 hx)

theorem RedTo.inv {g : Sp E n ≃ₗ[E] Sp E n} {a : GL (Fin n) (𝓞 E ⧸ P.asIdeal)} (hg : g ∈ GLint E n P)
    (h : RedTo P g a) : RedTo P g⁻¹ a⁻¹ := fun x hx => by
  have h1 := h _ (((inv_mem hg : g⁻¹ ∈ GLint E n P) x).2 hx)
  rw [show g (g⁻¹ x) = x from g.apply_symm_apply x] at h1
  rw [h1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]


variable (P) in
def redSub (G : Subgroup (Sp E n ≃ₗ[E] Sp E n)) (hG : G ≤ GLint E n P) : Subgroup (GL (Fin n) (𝓞 E ⧸ P.asIdeal)) where
  carrier := {a | ∃ g ∈ G, RedTo P g a}
  one_mem' := ⟨1, one_mem _, RedTo.one⟩
  mul_mem' := fun ⟨g, hg, h⟩ ⟨g', hg', h'⟩ => ⟨g * g', mul_mem hg hg', RedTo.mul (hG hg') h h'⟩
  inv_mem' := fun ⟨g, hg, h⟩ => ⟨g⁻¹, inv_mem hg, h.inv (hG hg)⟩

end Red

theorem unipotentArg_extendByIdOnLastCoords {E : Type} [Field E] {n : ℕ} (c : ℕ) (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    Loc.n1Arg (extE c κ) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [add_assoc, extE_apply, resX_eN]
  simp only [map_zero, sub_self, add_zero]
  unfold Loc.atN Loc.eN
  split_ifs with h1 h2
  · exact absurd h2 (by simp)
  · rfl
  · rfl

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem extE_mem_Cbe (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)) (hw : w ∈ Pr.vGs)
    (hd : ∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E))) (h : AutY X R j)
    (hh : h ∈ stabL X.E _ (lamYat (Pr := Pr) j w)) (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j))
    (hκ : κ ∈ GLint X.E (R.N j) w) (hr : ∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) :
    extE (cOf R j) κ ∈ Loc.Cbe (Jat (Pr := Pr) sharp j w) h := by
  have hq : ((qOf w : ℕ) : X.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero w
  unfold lamYat at hh
  rw [if_pos hw] at hh
  refine ⟨extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ κ, ?_⟩
  have e : (MulAut.conj h⁻¹).toMonoidHom (extE (cOf R j) κ) = h⁻¹ * extE (cOf R j) κ * h := by simp
  show (MulAut.conj h⁻¹).toMonoidHom (extE (cOf R j) κ) ∈ Jat (Pr := Pr) sharp j w
  rw [e]
  have hs := mul_mem (mul_mem (inv_mem hh) (extE_stab w (qOf w) (cOf R j) (fun i => i + 1) κ hκ)) hh
  have hc := conj_cong (qOf w) _ _ h hh (extE_cong w (qOf w) (cOf R j) (fun i => i + 1) hd κ hκ hr)
  unfold Jat
  rw [if_pos hw]
  split_ifs
  · refine ⟨hs, mem_flagU (qOf w) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
    · exact CongLevel.sclLat_le w _ hq _ _ _
    · exact smul_mem_sclLat w _ hq _ _ _ x hx
    · exact bvec_mem w _ hq _ _ _
  · refine ⟨hs, mem_flagU (qOf w) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
    · exact CongLevel.sclLat_le w _ hq _ _ _
    · exact smul_mem_sclLat w _ hq _ _ _ x hx
    · exact bvec_mem w _ hq _ _ _

theorem exists_levG : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j), cst.Ok → P.1 ∈ Pr.vGs → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) → prCat (Pr := Pr) cst.sharp j P.1 h ≤ GLint X.E (R.N j) P.1 → (∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P.1, y x ∈ lamYat (Pr := Pr) (R := R) j P.1) → lamRow Ch mu cst.sharp j P.1 (LinearMap.id + (qOf P.1 : X.E) • y) = 1) → ChiMul Ch sel mu cst j P h → ChiTriv Ch sel mu cst j P h → ∃ lev : Lev (𝓞 X.E ⧸ P.1.asIdeal) X.K (R.N j), GrpG sel mu cst j P h lev ∧ ChrG Ch sel mu cst j P h lev := by
  intro X Pr R Ch sel S mu cst j P h hc hP hdu hh hle hlam hmul htriv
  have hq : ((qOf P.1 : ℕ) : X.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
  have hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)) := fun a ha h0 => by
    have := GlobalTheory.TypePrimeUnif.intAt_div_of_notMem_sq P.1 _ (Ideal.absNorm_mem _) hdu.2 a ha h0
    rwa [map_natCast] at this
  have hone : ∀ κ ∈ GLint X.E (R.N j) P.1, (∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (κ x) = redV P.1 x) →
      chiInv Ch sel mu cst j P h (extE (cOf R j) κ) = 1 := by
    intro κ hκ hr
    unfold lamYat at hh hlam
    rw [if_pos hP] at hh hlam
    have hcong := conj_cong (qOf P.1) _ _ h hh
      (extE_cong P.1 (qOf P.1) (cOf R j) (fun i => i + 1) hd κ hκ hr)
    have h1 := hlam ((qOf P.1 : X.E)⁻¹ • ((h⁻¹ * extE (cOf R j) κ * h : AutY X R j).toLinearMap - LinearMap.id))
      fun x hx => by
        have h2 := hcong x hx
        rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
        exact h2
    rw [smul_inv_smul₀ hq, add_sub_cancel] at h1
    unfold chiInv
    rw [h1, unipotentArg_extendByIdOnLastCoords, hc.psi_int P 0 (by simpa using CongLevel.intAt_nat P.1 0), inv_one, one_mul]
  obtain ⟨lam, hl⟩ := exists_char (H := ↥(redSub P.1 _ hle)) (CAt sel mu cst j P h) (chiInv Ch sel mu cst j P h)
    (fun r a => ∃ g ∈ GLint X.E (R.N j) P.1,
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x)) ∧ RedTo P.1 g a.1)
    hmul.1 hmul.2
    (fun ⟨a, g, hg, hga⟩ => by
      obtain ⟨r, hr, hrg⟩ := id hg
      exact ⟨r, hr, g, hle hg, hrg, hga⟩)
    (by
      rintro r a r' a' ⟨g, hg, h1, h2⟩ ⟨g', hg', h1', h2'⟩
      refine ⟨g * g', mul_mem hg hg', fun x => ?_, RedTo.mul hg' h2 h2'⟩
      show r (r' _) = _
      rw [h1', h1]
      rfl)
    (by
      rintro a r hr r' hr' ⟨g, hg, h1, h2⟩ ⟨g', hg', h1', h2'⟩
      have hκ : g⁻¹ * g' ∈ GLint X.E (R.N j) P.1 := mul_mem (inv_mem hg) hg'
      have hred : ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 ((g⁻¹ * g') x) = redV P.1 x := fun x hx => by
        rw [RedTo.mul hg' (h2.inv hg) h2' x hx, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      have hs : extE (cOf R j) (g⁻¹ * g') ∈ CAt sel mu cst j P h := extE_mem_Cbe _ j P.1 hP hd h hh _ hκ hred
      have ht : (extE (cOf R j) (g⁻¹ * g'))⁻¹ * (r⁻¹ * r') ∈ CAt sel mu cst j P h :=
        mul_mem (inv_mem hs) (mul_mem (inv_mem hr) hr')
      have ht1 := htriv _ ht fun x => by
        show (extE (cOf R j) (g⁻¹ * g')).symm (r.symm (r' _)) = _
        rw [LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq, extE_inX, h1, h1']
        exact congrArg _ (g.apply_symm_apply _).symm
      have e : r' = r * (extE (cOf R j) (g⁻¹ * g') * ((extE (cOf R j) (g⁻¹ * g'))⁻¹ * (r⁻¹ * r'))) := by
        rw [mul_inv_cancel_left, mul_inv_cancel_left]
      have h3 := hmul.2 r hr _ (mul_mem hs ht)
      rw [← e, hmul.2 _ hs _ ht, ht1, hone _ hκ hred, mul_one, mul_one] at h3
      exact h3.symm)
  exact ⟨⟨redSub P.1 _ hle, lam⟩, fun _ => Iff.rfl,
    fun a g r hr h1 h2 => hl a r hr ⟨g, hle ⟨r, hr, h1⟩, h1, h2⟩⟩

end GlobalTheory.Mem.Col2.LevMod

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupModTypePrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelGroup_mod_typePrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j), cst.Ok → P.1 ∈ Pr.vGs → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) → prCat (Pr := Pr) cst.sharp j P.1 h ≤ GLint X.E (R.N j) P.1 → (∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P.1, y x ∈ lamYat (Pr := Pr) (R := R) j P.1) → lamRow Ch mu cst.sharp j P.1 (LinearMap.id + (qOf P.1 : X.E) • y) = 1) → ChiMul Ch sel mu cst j P h → ChiTriv Ch sel mu cst j P h → ∃ lev : Lev (𝓞 X.E ⧸ P.1.asIdeal) X.K (R.N j), GrpG sel mu cst j P h lev ∧ ChrG Ch sel mu cst j P h lev := by
  first | exact @GlobalTheory.Mem.Col2.LevMod.exists_levG | exact GlobalTheory.Mem.Col2.LevMod.exists_levG | (intros; apply GlobalTheory.Mem.Col2.LevMod.exists_levG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSchemeTheoreticallyDominantComplEffCartier
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSchemeTheoreticallyDominantComplEffCartier
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup

namespace GlobalTheory.ProjBlowup

theorem isSchemeTheoreticallyDominant_compl_of_effCartier :
    ∀ (W : Scheme.{0}) (I : W.IdealSheafData), FinalTheorems.EffCartier I →
      IsSchemeTheoreticallyDominant (Scheme.Opens.ι (X := W) I.support.compl) := by
  intro W I hI
  choose U f hxU hf hIU using hI
  refine ⟨le_bot_iff.1 (Scheme.IdealSheafData.le_of_iSup_eq_top U ?_ fun x s hs => ?_)⟩
  · exact top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩
  · have h0 := Scheme.Hom.ideal_ker_le _ (U x) hs
    rw [RingHom.mem_ker, Scheme.Opens.ι_app] at h0
    have hle : W.basicOpen (f x) ≤ (Scheme.Opens.ι (X := W) I.support.compl) ''ᵁ
        ((Scheme.Opens.ι (X := W) I.support.compl) ⁻¹ᵁ (U x).1) := by
      intro y hy
      have hyU : y ∈ (U x).1 := W.basicOpen_le (f x) hy
      have hyc : y ∈ I.support.compl := by
        intro hy'
        have := (Scheme.IdealSheafData.mem_support_iff_of_mem hyU).1 hy'
        rw [Scheme.mem_zeroLocus_iff] at this
        exact this (f x) (by rw [hIU]; exact Ideal.subset_span rfl) hy
      exact ⟨⟨y, hyc⟩, hyU, rfl⟩
    have := (U x).2.isLocalization_basicOpen (f x)
    have hinj := IsLocalization.injective (M := Submonoid.powers (f x)) Γ(W, W.basicOpen (f x))
      ((Submonoid.powers_le).2 (hf x))
    have h1 : algebraMap Γ(W, (U x).1) Γ(W, W.basicOpen (f x)) s = 0 := by
      have h2 := congrArg (W.presheaf.map (homOfLE hle).op).hom h0
      have h3 := h2.trans (map_zero (W.presheaf.map (homOfLE hle).op).hom)
      refine Eq.trans ?_ h3
      erw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    have : s = 0 := hinj (by rw [h1, map_zero])
    simp [this]

end GlobalTheory.ProjBlowup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSchemeTheoreticallyDominantComplEffCartierStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchemeTheoreticallyDominant_compl_effCartier : ∀ (W : Scheme.{0}) (I : W.IdealSheafData), FinalTheorems.EffCartier I → IsSchemeTheoreticallyDominant (Scheme.Opens.ι (X := W) I.support.compl) := by
  first | exact @GlobalTheory.ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier | exact GlobalTheory.ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier | (intros; apply GlobalTheory.ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotDvdDiscrIffRamificationIdx
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mem.RaySplit

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem.Fld

section General

theorem not_dvd_discr_iff_ramificationIdx (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ¬ (p : ℤ) ∣ discr E ↔ ∀ P : Ideal (𝓞 E), P.IsPrime → (p : 𝓞 E) ∈ P → P.ramificationIdx ℤ = 1 := by
  rw [NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) (Nat.prime_iff_prime_int.mp hp)]
  refine forall_congr' fun P => forall_congr' fun hP => ?_
  rw [Int.cast_natCast]
  refine forall_congr' fun hlP => ?_
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hp.ne_zero (by simpa using hlP)
  have := hP.isMaximal hP0
  have : (P.under ℤ).IsMaximal := inferInstance
  have hne : P.under ℤ ≠ ⊥ := by
    intro h0
    have h1 : (p : ℤ) ∈ P.under ℤ := by rw [Ideal.under_def, Ideal.mem_comap]; simpa using hlP
    rw [h0] at h1
    exact hp.ne_zero (by simpa using h1)
  have : Finite (ℤ ⧸ P.under ℤ) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have : Finite (P.under ℤ).ResidueField := inferInstance
  exact Ideal.ramificationIdx_eq_one_iff.symm

theorem not_mem_sq {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 E)} [hP : P.IsPrime]
    (hv : (p : 𝓞 E) ∈ P) (he : P.ramificationIdx ℤ = 1) : (p : 𝓞 E) ∉ P ^ 2 := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hb] at he
  intro h2
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h2

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem exists_under {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 L)) [P.IsPrime] (h : (p : 𝓞 L) ∈ P) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 K), P.LiesOver 𝔭.asIdeal ∧ (p : 𝓞 K) ∈ 𝔭.asIdeal := by
  have h1 : (p : 𝓞 K) ∈ P.under (𝓞 K) := by
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]; exact h
  refine ⟨⟨P.under (𝓞 K), inferInstance, fun h0 => ?_⟩, ⟨rfl⟩, h1⟩
  rw [h0] at h1
  exact hp.ne_zero (by simpa using h1)

theorem not_dvd_discr_of_unramIn [IsGalois K L] {p : ℕ} (hp : p.Prime) (hK : ¬ (p : ℤ) ∣ discr K)
    (hu : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal → UnramIn L 𝔭) : ¬ (p : ℤ) ∣ discr L := by
  rw [not_dvd_discr_iff_ramificationIdx _ hp] at hK ⊢
  intro P hP h
  obtain ⟨𝔭, hPo, h𝔭⟩ := exists_under (K := K) hp P h
  have := 𝔭.isMaximal
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have : P.IsMaximal := hP.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P)
  have h1 : P.inertia (L ≃ₐ[K] L) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun τ hτ => hu 𝔭 h𝔭 τ ⟨P, hP, hPo, hτ⟩
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) 𝔭.asIdeal P
  rw [h1, Subgroup.card_bot, Ideal.ramificationIdxIn_eq_ramificationIdx _ P (L ≃ₐ[K] L)] at h2
  rw [Ideal.ramificationIdx_tower (R := ℤ) 𝔭.asIdeal P, hK _ 𝔭.isPrime h𝔭, ← h2]

theorem heckeIdeal_asIdeal (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔮 : HeightOneSpectrum (𝓞 K)) :
    heckeIdeal L χ 𝔮.asIdeal = heckeVal L χ 𝔮 := by
  classical
  unfold heckeIdeal
  rw [finprod_eq_single _ 𝔮]
  · rw [Associates.count_self 𝔮.associates_irreducible, pow_one]
  · intro 𝔭 hne
    rw [Associates.count_eq_zero_of_ne 𝔭.associates_irreducible 𝔮.associates_irreducible, pow_zero]
    intro h
    exact hne (HeightOneSpectrum.ext (associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 h)))

theorem not_dvd_span {p c : ℕ} (hp : p.Prime) (hc : ¬ p ∣ c) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : (p : 𝓞 K) ∈ 𝔭.asIdeal) : ¬ 𝔭.asIdeal ∣ Ideal.span {(c : 𝓞 K)} := by
  rw [Ideal.dvd_span_singleton]
  intro h'
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hc)
  have h1 := congrArg (Int.cast : ℤ → 𝓞 K) hab
  push_cast at h1
  exact 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (h1 ▸ add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h')))

theorem absNorm_eq_of_span {𝔮 : Ideal (𝓞 K)} (hR : IsRayField K L 𝔮) (hK : IsEmpty (K →+* ℝ))
    (𝔭 : HeightOneSpectrum (𝓞 K)) {π : 𝓞 K} (hπ : 𝔭.asIdeal = Ideal.span {π}) (h1 : π - 1 ∈ 𝔮)
    (P : Ideal (𝓞 L)) [hP : P.IsPrime] [hPo : P.LiesOver 𝔭.asIdeal] :
    Ideal.absNorm P = Ideal.absNorm 𝔭.asIdeal := by
  have := hR.1
  have hcop : IsCoprime 𝔭.asIdeal 𝔮 := by
    rw [hπ]
    exact Ideal.isCoprime_iff_exists.2 ⟨π, Ideal.mem_span_singleton_self _, -(π - 1), neg_mem h1, by ring⟩
  have hnd : ¬ 𝔭.asIdeal ∣ 𝔮 := fun h => 𝔭.prime.not_unit (hcop.isUnit_of_dvd' dvd_rfl h)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact 𝔭.ne_bot (by simpa using hπ)
  have hχ := (hR.2.2.2 𝔭.asIdeal 𝔭.ne_bot hcop).2 ⟨π, 1,
    ⟨hπ0, one_ne_zero, hπ ▸ hcop, by rw [Ideal.span_singleton_one, ← Ideal.one_eq_top]; exact isCoprime_one_left,
      h1, fun φ => hK.elim φ⟩, by simp [hπ]⟩
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have hfP : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have hfv : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have := 𝔭.isPrime
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) P
  have hσ1 : σ = 1 := GlobalTheory.RayMaximal.eq_of_forall_char fun χ => Units.ext (by
    rw [← heckeVal_of_unramIn L χ (hR.2.1 𝔭 hnd) ((isFrob_iff L 𝔭 σ).2 ⟨P, hP, hPo, hσ⟩), ← heckeIdeal_asIdeal,
      hχ χ, map_one, Units.val_one])
  have hle : Nat.card (𝓞 L ⧸ P) ≤ Nat.card (𝓞 K ⧸ 𝔭.asIdeal) := by
    refine card_le_of_pow_eq_self Finite.one_lt_card fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h2 := hσ x
    rw [hσ1, ← hPo.over] at h2
    rw [← map_pow]
    refine (Ideal.Quotient.eq.2 ?_).symm
    simpa using h2
  have hinj : Function.Injective (algebraMap (𝓞 K ⧸ 𝔭.asIdeal) (𝓞 L ⧸ P)) := FaithfulSMul.algebraMap_injective _ _
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_eq_of_bijective _ (hinj.bijective_of_nat_card_le hle)).symm

theorem dvd_of_dvd_discr {c : ℕ} (hR : IsRayField K L (Ideal.span {(c : 𝓞 K)})) {p : ℕ} (hp : p.Prime)
    (h : (p : ℤ) ∣ discr L) : p ∣ c ∨ (p : ℤ) ∣ discr K := by
  have := hR.1
  by_contra hc
  rw [not_or] at hc
  exact not_dvd_discr_of_unramIn hp hc.2 (fun 𝔭 h𝔭 => hR.2.1 𝔭 (not_dvd_span hp hc.1 𝔭 h𝔭)) h

theorem absNorm_eq_of_mul (h2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) {π π' : 𝓞 K} (h : π * π' = p)
    (hu : ¬ IsUnit π) (hu' : ¬ IsUnit π') : Ideal.absNorm (Ideal.span {π}) = p := by
  have h1 : Ideal.absNorm (Ideal.span {π}) * Ideal.absNorm (Ideal.span {π'}) = p ^ 2 := by
    rw [← map_mul, Ideal.span_singleton_mul_span_singleton, h, Ideal.absNorm_span_singleton,
      ← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap, RingOfIntegers.rank, h2]
    simp
  obtain ⟨i, hi, e⟩ := (Nat.dvd_prime_pow hp).1 ⟨_, h1.symm⟩
  interval_cases i
  · exact absurd (Ideal.span_singleton_eq_top.1 (Ideal.absNorm_eq_one_iff.1 (by simpa using e))) hu
  · simpa using e
  · rw [e] at h1
    have h3 := (Nat.mul_eq_left (pow_ne_zero 2 hp.ne_zero)).1 h1
    exact absurd (Ideal.span_singleton_eq_top.1 (Ideal.absNorm_eq_one_iff.1 h3)) hu'

theorem ncard_primesOver_eq {c : ℕ} (hR : IsRayField K L (Ideal.span {(c : 𝓞 K)})) (hK : IsEmpty (K →+* ℝ))
    (h2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr L) {π π' : 𝓞 K} (h : π * π' = p)
    (hu : ¬ IsUnit π) (hu' : ¬ IsUnit π') (hc : (c : 𝓞 K) ∣ π - 1) (hc' : (c : 𝓞 K) ∣ π' - 1) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 L)).ncard = Module.finrank ℚ L := by
  refine GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq L p hp fun P hP hpP => ?_
  refine ⟨?_, not_mem_sq hp hpP ((not_dvd_discr_iff_ramificationIdx L hp).1 hd P hP.isPrime hpP)⟩
  obtain ⟨𝔭, hPo, h𝔭⟩ := exists_under (K := K) hp P hpP
  have key : ∀ a : 𝓞 K, Ideal.absNorm (Ideal.span {a}) = p → (c : 𝓞 K) ∣ a - 1 → a ∈ 𝔭.asIdeal →
      Ideal.absNorm P = p := fun a hN ha hm => by
    have hpr : (Ideal.span {a}).IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hp)
    have hb : Ideal.span {a} ≠ ⊥ := fun h0 => hp.ne_zero (by rw [← hN, h0, Ideal.absNorm_bot])
    have e : Ideal.span {a} = 𝔭.asIdeal :=
      (hpr.isMaximal hb).eq_of_le 𝔭.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hm)
    rw [absNorm_eq_of_span hR hK 𝔭 e.symm (Ideal.mem_span_singleton.2 ha) P, ← e, hN]
  rcases 𝔭.isPrime.mem_or_mem (h ▸ h𝔭) with hm | hm
  · exact key π (absNorm_eq_of_mul h2 hp h hu hu') hc hm
  · exact key π' (absNorm_eq_of_mul h2 hp ((mul_comm _ _).trans h) hu' hu) hc' hm

end General

section Host

variable {R : Ranks} (H : Host R)

abbrev condIdeal : Ideal (𝓞 H.K) := Ideal.span {((H.QS * H.q * H.d : ℕ) : 𝓞 H.K)}

theorem cond_ne_zero : H.QS * H.q * H.d ≠ 0 := by
  have h1 := H.hyp.1.ne_zero
  have h2 := H.hyp.2.1.ne_zero
  have h3 := H.QS_pos.ne'
  positivity

theorem condIdeal_ne_bot : condIdeal H ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast cond_ne_zero H

theorem finrank_K : Module.finrank ℚ H.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos (H.sqd_sq)

theorem discr_K : NumberField.discr H.K = -(H.d : ℤ) :=
  discr_eq_neg_of_sq_eq (finrank_K H) H.hyp.2.1.squarefree (by have := H.hyp.2.2.2.1; omega)
    (Formalism.FrobeniusOrbits.SplitK.bK_sq (H.sqd_sq))

theorem isEmpty_real : IsEmpty (H.K →+* ℝ) := ⟨fun φ => by
  obtain ⟨x, hx⟩ : ∃ x : H.K, x ^ 2 = -(H.d : H.K) := ⟨_, Formalism.FrobeniusOrbits.SplitK.bK_sq (H.sqd_sq)⟩
  have h := congrArg φ hx
  rw [map_pow, map_neg, map_natCast] at h
  have h5 : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  nlinarith [sq_nonneg (φ x)]⟩

variable {H} {M : Type} [Field M] [NumberField M] [Algebra H.K M]

theorem isGalois_of_ray (hM : IsRayField H.K M (condIdeal H)) : IsGalois H.K M :=
  have := hM.1
  inferInstance

theorem comm_of_ray (hM : IsRayField H.K M (condIdeal H)) (σ τ : M ≃ₐ[H.K] M) : σ * τ = τ * σ :=
  have := hM.1
  mul_comm' σ τ

theorem unr_of_ray (hM : IsRayField H.K M (condIdeal H)) (p : ℕ) (hp : p.Prime) (h : (p : ℤ) ∣ discr M) :
    p ∣ H.QS * H.q * H.d := by
  rcases dvd_of_dvd_discr hM hp h with h | h
  · exact h
  · rw [discr_K, dvd_neg] at h
    exact Dvd.dvd.mul_left (by exact_mod_cast h) _

end Host

end GlobalTheory.Mem.RaySplit

end
end
