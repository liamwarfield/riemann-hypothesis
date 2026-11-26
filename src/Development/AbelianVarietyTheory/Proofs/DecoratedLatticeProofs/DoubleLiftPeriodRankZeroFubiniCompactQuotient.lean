module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegrand
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupTwoModelsRationalRealUnipotentDictio
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointNearCuspScale
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSplitPlaceHermitianFrameGLEmbedding
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftPeriodRankZeroFubiniCompactQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftPeriodRankZeroFubiniCompactQuotient
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.LastSteps

variable {D : D7}

theorem flagN_rank_zero {S S₀ : HSp D} (d : HypDec S S₀ 0) {n : GA D S} (hn : n ∈ flagN d) : n = 1 := by
  have hle : flagN d ≤ ⊥ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨-, hg⟩
    have hcol : ∀ i : Fin S.rank, ∀ k, subOne S g k i = 0 := by
      intro i k
      obtain ⟨a, ha⟩ := hg (Pi.single i 1) (Subsingleton.elim _ _)
      have h1 := congrFun ha k
      have hr : ratV (D := D) (Pi.single i (1 : D.host.E)) = Pi.single i 1 := by
        funext j; by_cases h : j = i <;> simp [ratV, Pi.single_apply, h]
      rw [hr] at h1
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1
    have hm : (matHom S g).1 = 1 := by
      have : subOne S g = 0 := by ext k i; exact hcol i k
      simpa [subOne, sub_eq_zero] using this
    have : matHom S g = 1 := Units.ext hm
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  exact Subgroup.mem_bot.1 (hle hn)

theorem per_rank_zero (B : BesLev D 0) (ψ : AddChar (AF D.host.F) ℂ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) :
    B.per ψ φ f = ∫ h in B.vA.𝓕, φ h * f (embA B.d B.o h) ∂B.vA.μ := by
  unfold BesLev.per besPer
  congr 1; funext h
  have e : ∀ n : flagN B.d, besFun ψ 1 B.d B.o B.ζ φ f h n = φ h * f (embA B.d B.o h) := by
    intro n
    have hp : ∀ m, psiBes ψ B.d 1 (vecB B.o B.ζ) m = 1 := fun m => by
      simp [psiBes, simpleSum, upSum, dotProduct, psiE]
    rw [besFun, flagN_rank_zero B.d n.2, one_mul, hp, star_one, mul_one]
  simp_rw [e]
  rw [setIntegral_const]
  simp [Measure.real, B.vN.unit.2.2]

end GlobalTheory.Unf.LastSteps

namespace GlobalTheory.Unf.LastSteps

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem swap_bdd {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] [SecondCountableTopology X] [SecondCountableTopology Y] (μ : Measure X) (ν : Measure Y)
    (s : Set X) (t : Set Y) (hs : μ s < ⊤) (ht : ν t < ⊤) (f : X → Y → ℂ) (hf : Continuous (Function.uncurry f))
    (C : ℝ) (hC : ∀ x y, ‖f x y‖ ≤ C) :
    ∫ x in s, ∫ y in t, f x y ∂ν ∂μ = ∫ y in t, ∫ x in s, f x y ∂μ ∂ν := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs.ne
  have : IsFiniteMeasure (ν.restrict t) := isFiniteMeasure_restrict.2 ht.ne
  exact integral_integral_swap (Integrable.of_bound hf.aestronglyMeasurable C (.of_forall fun p => hC p.1 p.2))

theorem om_bdd {S T A T₀ : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χ χ' om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hA : CoCpt A) (hT : CoCpt T₀) (a : GA D A →* GA D S)
    (b : GA D T₀ →* GA D T) (ha : Continuous a) (hb : Continuous b) (ha' : ∀ γ ∈ GQ A, a γ ∈ GQ S)
    (hb' : ∀ γ ∈ GQ T₀, b γ ∈ GQ T) :
    Continuous (fun p : GA D A × GA D T₀ => om (a p.1, b p.2) f 0) ∧ ∃ C : ℝ, ∀ x y, ‖om (a x, b y) f 0‖ ≤ C := by
  have t0 := EvalCont.tame_om hom hf hA hT a b ha hb ha' hb'
  refine ⟨?_, ?_⟩
  · have := t0.1.comp ((continuous_const (y := (1 : GA D T))).prodMk
      (continuous_id.prodMk (continuous_const (y := (0 : WO S T)))))
    simpa [Function.comp_def] using this
  · obtain ⟨C, hC⟩ := t0.2 1
    exact ⟨C, fun x y => by simpa using hC.self_of_nhds ((x, y), 0)⟩

end GlobalTheory.Unf.LastSteps

namespace GlobalTheory.Unf.LastSteps

open EvalCont

theorem bound_mul {x y : ℂ} {C C' : ℝ} (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C') : ‖x * y‖ ≤ C * C' := by
  rw [norm_mul]; exact mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)

theorem triple {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] [BorelSpace X] [BorelSpace Y] [BorelSpace Z] [SecondCountableTopology X]
    [SecondCountableTopology Y] [SecondCountableTopology Z] (μ : Measure X) (ν : Measure Y) (κ : Measure Z)
    (s : Set X) (u : Set Y) (w : Set Z) (hs : μ s < ⊤) (hu : ν u < ⊤) (hw : κ w < ⊤)
    (φ : X → ℂ) (F : Z → ℂ) (a : X → Y → ℂ) (b : Y → Z → ℂ) (hφ : Continuous φ) (hF : Continuous F)
    (ha : Continuous fun p : X × Y => a p.1 p.2) (hb : Continuous fun p : Y × Z => b p.1 p.2)
    {Cφ CF Ca Cb : ℝ} (hCφ : ∀ x, ‖φ x‖ ≤ Cφ) (hCF : ∀ z, ‖F z‖ ≤ CF) (hCa : ∀ x y, ‖a x y‖ ≤ Ca)
    (hCb : ∀ y z, ‖b y z‖ ≤ Cb) :
    ∫ x in s, φ x * ∫ y in u, a x y * ∫ z in w, b y z * F z ∂κ ∂ν ∂μ =
      ∫ z in w, F z * ∫ y in u, b y z * ∫ x in s, φ x * a x y ∂μ ∂ν ∂κ := by
  have : FirstCountableTopology Y := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  set c : Y → ℂ := fun y => ∫ z in w, b y z * F z ∂κ with hc
  set m : Y → ℂ := fun y => ∫ x in s, φ x * a x y ∂μ with hm
  have hcC : Continuous c :=
    Tame.continuous_integral _ _ hw (F := fun y z => b y z * F z) (tame_of_bounded (C := Cb * CF)
      (hb.mul (hF.comp continuous_snd)) fun y z => bound_mul (hCb y z) (hCF z))
  have hcB : ∀ y, ‖c y‖ ≤ Cb * CF * κ.real w := fun y =>
    norm_setIntegral_le_of_norm_le_const hw fun z _ => bound_mul (hCb y z) (hCF z)
  have hmC : Continuous m :=
    Tame.continuous_integral _ _ hs (F := fun y x => φ x * a x y) (tame_of_bounded (C := Cφ * Ca)
      ((hφ.comp continuous_snd).mul (ha.comp continuous_swap)) fun y x => bound_mul (hCφ x) (hCa x y))
  have hmB : ∀ y, ‖m y‖ ≤ Cφ * Ca * μ.real s := fun y =>
    norm_setIntegral_le_of_norm_le_const hs fun x _ => bound_mul (hCφ x) (hCa x y)
  calc ∫ x in s, φ x * ∫ y in u, a x y * c y ∂ν ∂μ
      = ∫ x in s, ∫ y in u, φ x * (a x y * c y) ∂ν ∂μ := by
        congr 1; funext x; rw [integral_const_mul]
    _ = ∫ y in u, ∫ x in s, φ x * (a x y * c y) ∂μ ∂ν := by
        refine swap_bdd _ _ _ _ hs hu _ ?_ (Cφ * (Ca * (Cb * CF * κ.real w))) fun x y =>
          bound_mul (hCφ x) (bound_mul (hCa x y) (hcB y))
        exact (hφ.comp continuous_fst).mul (ha.mul (hcC.comp continuous_snd))
    _ = ∫ y in u, m y * c y ∂ν := by
        congr 1; funext y; rw [hm]; dsimp only; rw [← integral_mul_const]; congr 1; funext x; ring
    _ = ∫ y in u, ∫ z in w, m y * (b y z * F z) ∂κ ∂ν := by
        congr 1; funext y; rw [hc]; dsimp only; rw [integral_const_mul]
    _ = ∫ z in w, ∫ y in u, m y * (b y z * F z) ∂ν ∂κ := by
        refine swap_bdd _ _ _ _ hu hw _ ?_ (Cφ * Ca * μ.real s * (Cb * CF)) fun y z =>
          bound_mul (hmB y) (bound_mul (hCb y z) (hCF z))
        exact (hmC.comp continuous_fst).mul (hb.mul (hF.comp continuous_snd))
    _ = ∫ z in w, F z * ∫ y in u, b y z * m y ∂ν ∂κ := by
        congr 1; funext z; rw [← integral_const_mul]; congr 1; funext y; ring

end GlobalTheory.Unf.LastSteps

namespace GlobalTheory.Unf.LastSteps


open EvalCont in
theorem lastLaw : ∀ D : D7, LastLaw D := by
  intro D ψ T B t φ Φ₁ Φ₂ F hφ hF hΦ₁ hΦ₂
  obtain ⟨-, iA2, -, -, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  obtain ⟨-, iS2, -, -, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D t.J.W
  obtain ⟨-, iT2, -, -, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  have : BorelSpace (GA D B.A) := ⟨rfl⟩
  have : BorelSpace (GA D t.J.W) := ⟨rfl⟩
  have : BorelSpace (GA D T) := ⟨rfl⟩
  obtain ⟨Cφ, hCφ⟩ := bounded_of_contAut B.cpt hφ
  obtain ⟨CF, hCF⟩ := bounded_of_contAut t.cptT hF
  obtain ⟨ha, Ca, hCa⟩ := om_bdd t.s.weil hΦ₁ B.cpt t.cptS (embA B.d B.o) (MonoidHom.id _)
    (B.d.continuous_embed.comp (continuous_embL B)) continuous_id
    (fun γ hγ => B.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (B.o.emb_mem_GQ hγ (one_mem _))) (fun γ hγ => hγ)
  obtain ⟨hb, Cb, hCb⟩ := om_bdd t.weil hΦ₂ t.cptS t.cptT (MonoidHom.id _) (MonoidHom.id _) continuous_id continuous_id
    (fun γ hγ => hγ) (fun γ hγ => hγ)
  simp only [MonoidHom.id_apply] at ha hCa hb hCb
  have e1 : ∀ h₀, t.s.lift (liftS t.om t.vT.μ t.vT.𝓕 F Φ₂) Φ₁ (embA B.d B.o h₀) =
      ∫ h in t.s.vW.𝓕, t.s.om (embA B.d B.o h₀, h) Φ₁ 0 * ∫ h' in t.vT.𝓕, t.om (h, h') Φ₂ 0 * F h' ∂t.vT.μ ∂t.s.vW.μ :=
    fun h₀ => rfl
  rw [per_rank_zero]
  simp_rw [e1]
  exact triple B.vA.μ t.s.vW.μ t.vT.μ B.vA.𝓕 t.s.vW.𝓕 t.vT.𝓕 (vol_lt_top B.cpt B.vA) (vol_lt_top t.cptS t.s.vW)
    (vol_lt_top t.cptT t.vT) φ F (fun x y => t.s.om (embA B.d B.o x, y) Φ₁ 0) (fun y z => t.om (y, z) Φ₂ 0) hφ.2 hF.2
    ha hb hCφ hCF hCa hCb

end GlobalTheory.Unf.LastSteps

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftPeriodRankZeroFubiniCompactQuotientStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleLiftPeriod_rankZero_fubini_compactQuotient : ∀ D : D7, LastLaw D := by
  first | exact @GlobalTheory.Unf.LastSteps.lastLaw | exact GlobalTheory.Unf.LastSteps.lastLaw | (intros; apply GlobalTheory.Unf.LastSteps.lastLaw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryEveryPointHasCuspScale
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryEveryPointHasCuspScale
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CuspGeo

open Formalism.IndefR.Eqv

theorem norm_mul_mul_apply_le {n : ℕ} (P A Q : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hA : ∀ k l, ‖A k l‖ ≤ c)
    (i j : Fin n) : ‖(P * A * Q) i j‖ ≤ (∑ k, ∑ l, ‖P i k‖ * ‖Q l j‖) * c := by
  simp only [Matrix.mul_apply]
  calc ‖∑ l, (∑ k, P i k * A k l) * Q l j‖ ≤ ∑ l, ∑ k, ‖P i k‖ * c * ‖Q l j‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul, ← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)) (norm_nonneg _)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hA k l) (norm_nonneg _)
    _ = (∑ k, ∑ l, ‖P i k‖ * ‖Q l j‖) * c := by
        rw [Finset.sum_comm, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

theorem norm_uMat_inv_apply {n : ℕ} {ε : Fin n → Bool} (y : Formalism.REAL.UJ ε) (i j : Fin n) :
    ‖uMat y⁻¹ i j‖ = ‖uMat y j i‖ := by
  have hy : (uMat y)ᴴ * Formalism.REAL.Jm ε * uMat y = Formalism.REAL.Jm ε := y.2
  have h1 : uMat y⁻¹ = Formalism.REAL.Jm ε * (uMat y)ᴴ * Formalism.REAL.Jm ε := by
    show (((y : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = _
    refine Units.inv_eq_of_mul_eq_one_left ?_
    calc Formalism.REAL.Jm ε * (uMat y)ᴴ * Formalism.REAL.Jm ε * uMat y
        = Formalism.REAL.Jm ε * ((uMat y)ᴴ * Formalism.REAL.Jm ε * uMat y) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hy, Formalism.REAL.Jm_mul_self]
  rw [h1]
  by_cases hi : ε i <;> by_cases hj : ε j <;>
    simp [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, hi, hj]

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

def frameBound (fr : UI.Frames D V) (τ : D.what₂.Tau) (i j : Fin V.rank) : ℝ :=
  ∑ k, ∑ l, ‖fr.P (Formalism.L2.Host.tauPl D τ) i k‖ * ‖(fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ l j‖

theorem frameBound_nonneg (fr : UI.Frames D V) (τ : D.what₂.Tau) (i j : Fin V.rank) : 0 ≤ frameBound fr τ i j :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

def brgFin (fr : UI.Frames D V) : (UI.instV fr).Gf →* GA D V :=
  (UI.brg fr : (UI.instV fr).GA →* GA D V).comp (MonoidHom.inr _ _)

theorem brgFin_apply (fr : UI.Frames D V) (k : (UI.instV fr).Gf) : brgFin fr k = UI.brg fr (1, k) := rfl

theorem continuous_brgFin (fr : UI.Frames D V) : Continuous (brgFin fr) :=
  (UI.brg fr).continuous.comp (continuous_const.prodMk continuous_id)

theorem brg_entry_bounds (fr : UI.Frames D V)
    (h2 : ∀ (x : (UI.instV fr).GA) (τ : D.what₂.Tau) (A : Matrix (Fin V.rank) (Fin V.rank) ℂ),
      A = uMat (x.1 (Formalism.L2.Host.tauPl D τ)) → infMat D.sp.cm.sig V.gram (θ τ) (UI.brg fr x) =
        fr.P (Formalism.L2.Host.tauPl D τ) * A * (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (y : (UI.instV fr).Ginf) (c : ℝ),
      ((∀ v i j, ‖uMat (y v) i j‖ ≤ c) → normInf θ V (UI.brg fr (y, 1)) ≤ S * c) ∧
      ((∀ v i j, ‖(uMat (y v) - 1) i j‖ ≤ c) →
        ∀ τ i j, ‖(infMat D.sp.cm.sig V.gram (θ τ) (UI.brg fr (y, 1)) - 1) i j‖ ≤ S * c) := by
  have hle : ∀ τ i j, frameBound fr τ i j ≤ ∑ τ, ∑ i, ∑ j, 2 * frameBound fr τ i j := fun τ i j => by
    have h0 := frameBound_nonneg fr
    calc frameBound fr τ i j ≤ 2 * frameBound fr τ i j := by linarith [h0 τ i j]
      _ ≤ ∑ j', 2 * frameBound fr τ i j' :=
          Finset.single_le_sum (f := fun j' => 2 * frameBound fr τ i j') (fun j' _ => by linarith [h0 τ i j'])
            (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', 2 * frameBound fr τ i' j' :=
          Finset.single_le_sum (f := fun i' => ∑ j', 2 * frameBound fr τ i' j')
            (fun i' _ => Finset.sum_nonneg fun j' _ => by linarith [h0 τ i' j']) (Finset.mem_univ i)
      _ ≤ _ :=
          Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', 2 * frameBound fr τ' i' j')
            (fun τ' _ => Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun j' _ => by linarith [h0 τ' i' j'])
            (Finset.mem_univ τ)
  refine ⟨∑ τ, ∑ i, ∑ j, 2 * frameBound fr τ i j,
    Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg zero_le_two (frameBound_nonneg fr τ i j), fun y c => ⟨fun hc => ?_, fun hc τ i j => ?_⟩⟩
  · unfold normInf
    simp only [Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have e1 := norm_mul_mul_apply_le (fr.P (Formalism.L2.Host.tauPl D τ))
      (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ c (fun k l => hc (Formalism.L2.Host.tauPl D τ) k l) i j
    have e2 := norm_mul_mul_apply_le (fr.P (Formalism.L2.Host.tauPl D τ))
      (uMat ((y (Formalism.L2.Host.tauPl D τ))⁻¹) : Matrix (Fin V.rank) (Fin V.rank) ℂ)
      (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ c
      (fun k l => (norm_uMat_inv_apply _ k l).trans_le (hc _ l k)) i j
    rw [← map_inv, h2 _ τ (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) rfl,
      h2 _ τ (uMat ((y (Formalism.L2.Host.tauPl D τ))⁻¹) : Matrix (Fin V.rank) (Fin V.rank) ℂ) rfl]
    unfold frameBound
    linarith
  · have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc (Formalism.L2.Host.tauPl D τ) i j)
    have hdet : IsUnit (fr.P (Formalism.L2.Host.tauPl D τ)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (fr.unit (Formalism.L2.Host.tauPl D τ))
    rw [h2 _ τ (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) rfl]
    have e : fr.P (Formalism.L2.Host.tauPl D τ) * (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) *
        (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ - 1 = fr.P (Formalism.L2.Host.tauPl D τ) *
        ((uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) - 1) *
        (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hdet]
    rw [e]
    exact (norm_mul_mul_apply_le _ _ _ c (hc _) i j).trans (mul_le_mul_of_nonneg_right (hle τ i j) hc0)

theorem near (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) :
    Near θ V := by
  intro U hU
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.unitaryGroup_twoModels_rationalReal_unipotent_dictionary D θ hθ V (UI.framesV D V)
  obtain ⟨S, hS0, hS⟩ := brg_entry_bounds (θ := θ) (UI.framesV D V) h2
  obtain ⟨d, hd⟩ := GlobalTheory.Grow.height_le_normInf_pow (θ := θ) V hθ
  have hKp : IsOpen ((U.comap (brgFin (UI.framesV D V)) : Subgroup _) : Set (UI.instV (UI.framesV D V)).Gf) :=
    hU.preimage (continuous_brgFin _)
  obtain ⟨b, C, δ₀, K, hδ₀, hK, hx⟩ := GlobalTheory.T.adelicPoint_nearCusp_scale (UI.instV (UI.framesV D V)) _ hKp
  obtain ⟨Ck, hCk⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V (hK.image (continuous_brgFin (UI.framesV D V)))
  refine ⟨b * d, max (Ck * (S * C) ^ d) (S * C), δ₀, hδ₀, fun g => ?_⟩
  set fr := UI.framesV D V with hfr
  set x := (UI.brg fr).symm g with hxdef
  have hgx : UI.brg fr x = g := (UI.brg fr).apply_symm_apply g
  obtain ⟨δ, hδ, hδ1, ⟨γ, hγ, hγK, hγb⟩, halt⟩ := hx x
  refine ⟨δ, hδ, hδ1, ?_, ?_⟩
  · have hsplit : γ * x = ((γ * x).1, 1) * (1, (γ * x).2) := Prod.ext (by simp) (by simp)
    have e : UI.brg fr γ * g = UI.brg fr ((γ * x).1, 1) * brgFin fr (γ * x).2 := by
      calc UI.brg fr γ * g = UI.brg fr (γ * x) := by rw [map_mul, hgx]
        _ = UI.brg fr (((γ * x).1, 1) * (1, (γ * x).2)) := congrArg _ hsplit
        _ = _ := map_mul _ _ _
    have hkb := hCk _ ⟨_, hγK, rfl⟩
    have hq : GlobalTheory.Grow.quotHeight V g ≤ GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * Ck := by
      have := GlobalTheory.Grow.quotHeight_le V g ((h1 γ).2 hγ)
      rw [e] at this
      exact this.trans ((GlobalTheory.Grow.height_mul_le V _ _).trans
        (mul_le_mul_of_nonneg_left hkb (GlobalTheory.Grow.height_pos V _).le))
    have hy : ∀ v i j, ‖uMat ((γ * x).1 v) i j‖ ≤ C / δ ^ b := fun v i j =>
      (le_div_iff₀ (pow_pos hδ b)).2 (hγb v i j)
    have hN := (hS (γ * x).1 (C / δ ^ b)).1 hy
    have hN0 : 0 ≤ normInf θ V (UI.brg fr ((γ * x).1, 1)) := by unfold normInf; positivity
    have hNb : normInf θ V (UI.brg fr ((γ * x).1, 1)) * δ ^ b ≤ S * C := by
      calc _ ≤ S * (C / δ ^ b) * δ ^ b := mul_le_mul_of_nonneg_right hN (pow_pos hδ b).le
        _ = S * C := by rw [mul_assoc, div_mul_cancel₀ _ (pow_pos hδ b).ne']
    have hH := hd _ ((brg_mem_GinfC fr ((γ * x).1, 1)).2 rfl)
    have hHb : GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * δ ^ (b * d) ≤ (S * C) ^ d := by
      rw [pow_mul]
      calc _ ≤ normInf θ V (UI.brg fr ((γ * x).1, 1)) ^ d * (δ ^ b) ^ d :=
            mul_le_mul_of_nonneg_right hH (by positivity)
        _ = (normInf θ V (UI.brg fr ((γ * x).1, 1)) * δ ^ b) ^ d := (mul_pow _ _ _).symm
        _ ≤ (S * C) ^ d := pow_le_pow_left₀ (by positivity) hNb d
    have hCk0 : 0 ≤ Ck := zero_le_one.trans ((GlobalTheory.Grow.one_le_height V _).trans hkb)
    calc GlobalTheory.Grow.quotHeight V g * δ ^ (b * d)
        ≤ GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * Ck * δ ^ (b * d) :=
          mul_le_mul_of_nonneg_right hq (by positivity)
      _ = Ck * (GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * δ ^ (b * d)) := by ring
      _ ≤ Ck * (S * C) ^ d := mul_le_mul_of_nonneg_left hHb hCk0
      _ ≤ _ := le_max_left _ _
  · rcases halt with h | ⟨W, hW, hWm⟩
    · exact Or.inl h
    · obtain ⟨r, C₀, hC₀, hNI⟩ := h3 W hW
      refine Or.inr ⟨r, C₀, hC₀, fun m hm => ?_⟩
      have hm' : (UI.brg fr).symm m ∈ (UI.instV fr).NA W :=
        hNI _ (by rwa [(UI.brg fr).apply_symm_apply])
      obtain ⟨γ', hγ', u, k, hk, he, hu⟩ := hWm _ hm'
      refine ⟨UI.brg fr γ', (h1 γ').2 hγ', UI.brg fr (u, 1), brgFin fr k,
        ⟨(brg_mem_GinfC fr (u, 1)).2 rfl, fun τ i j => ?_⟩, hk, (brg_mem_GfC fr (1, k)).2 rfl, ?_⟩
      · calc _ ≤ S * (C * δ) := (hS u (C * δ)).2 hu τ i j
          _ ≤ max (Ck * (S * C) ^ d) (S * C) * δ := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le
      · calc m * g = UI.brg fr ((UI.brg fr).symm m * x) := by rw [map_mul, (UI.brg fr).apply_symm_apply, hgx]
          _ = UI.brg fr (γ' * x * ((u, 1) * (1, k))) := by
            rw [he]; exact congrArg (fun z => UI.brg fr (γ' * x * z)) (Prod.ext (by simp) (by simp))
          _ = UI.brg fr γ' * g * UI.brg fr (u, 1) * brgFin fr k := by
            rw [map_mul, map_mul, map_mul, hgx, ← mul_assoc]; rfl

end GlobalTheory.CuspGeo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryEveryPointHasCuspScaleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitary_every_point_has_cusp_scale : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ V : HSp D, Near θ V := by
  first | exact @GlobalTheory.CuspGeo.near | exact GlobalTheory.CuspGeo.near | (intros; apply GlobalTheory.CuspGeo.near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentRadicalSurjectsUnitriangularCharact
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentRadicalSurjectsUnitriangularCharact
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB.UniRad

variable {D : D7} {σ : ℕ} (B : BesLev D σ)

theorem fourierBesselBasePoint_castSucc_column (i : Fin B.V.rank) (j : Fin σ) : x0 B i (Fin.castSucc j) = B.d.jX i j := by
  simp [x0, xLast, Fin.snoc_castSucc]

theorem fourierBesselBasePoint_last_column (i : Fin B.V.rank) : x0 B i (Fin.last σ) = (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) i := by
  simp [x0, xLast, Fin.snoc_last]

theorem mul_fourierBesselBasePoint_castSucc_column {m : ℕ} (M : Mx D m B.V.rank) (i : Fin m) (j : Fin σ) :
    (M * x0 B) i (Fin.castSucc j) = (M * B.d.jX) i j := by
  simp only [Matrix.mul_apply, fourierBesselBasePoint_castSucc_column]

theorem mul_fourierBesselBasePoint_last_column {m : ℕ} (M : Mx D m B.V.rank) (i : Fin m) :
    (M * x0 B) i (Fin.last σ) = (M *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ))) i := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, fourierBesselBasePoint_last_column]

theorem fourierBesselBasePoint_mul_eq (U : Mx D (σ + 1) (σ + 1)) (i : Fin B.V.rank) (j : Fin (σ + 1)) :
    (x0 B * U) i j = ∑ k : Fin σ, B.d.jX i k * U (Fin.castSucc k) j +
      (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) i * U (Fin.last σ) j := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [fourierBesselBasePoint_castSucc_column, fourierBesselBasePoint_last_column]

theorem besselAnisotropicEmbedding_fixes_basePoint (h : GA D B.A) : mt B.V (embA B.d B.o h) * x0 B = x0 B := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [mul_fourierBesselBasePoint_last_column, fourierBesselBasePoint_last_column, embA_apply, Matrix.mulVec_mulVec, B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec, vecB, ratV_mulVec,
      Matrix.mulVec_mulVec (ratV B.ζ), show rat B.o.iB = B.o.jB from rfl, B.o.emb_jB, mt_one, Matrix.mul_one]
  · rw [mul_fourierBesselBasePoint_castSucc_column, embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclX, fourierBesselBasePoint_castSucc_column]

end GlobalTheory.Unf.FB.UniRad

namespace GlobalTheory.Unf.FB.UniRad

variable {D : D7} {σ : ℕ} (B : BesLev D σ)

theorem upSum_succ (U : Mx D (σ + 1) (σ + 1)) :
    upSum U = upSum (fun i j : Fin σ => U (Fin.castSucc i) (Fin.castSucc j)) +
      ell D σ ⬝ᵥ (fun i => U (Fin.castSucc i) (Fin.last σ)) := by
  have h1 : ∀ j : Fin σ, ¬ (j.1 = σ + 1) := fun j => by omega
  have h2 : ¬ (σ = σ + 1) := by omega
  simp only [upSum, ell, dotProduct, Fin.sum_univ_castSucc, Fin.coe_castSucc, Fin.val_last, h1, h2, if_false,
    Finset.sum_const_zero, add_zero, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : σ = i.1 + 1
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem besselFlagProjection_mul_fourierBesselBasePoint_apply (i : Fin σ) (k : Fin (σ + 1)) : (B.d.pX * x0 B) i k = if k = Fin.castSucc i then 1 else 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [mul_fourierBesselBasePoint_last_column, Matrix.mulVec_mulVec, B.d.pX_j0, Matrix.zero_mulVec, if_neg (Fin.castSucc_lt_last i).ne']
    rfl
  · rw [mul_fourierBesselBasePoint_castSucc_column, B.d.pX_jX, Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h (Fin.castSucc_injective _ e).symm)]

theorem besselFlagProjection_mul_basePoint_mul_apply (U : Mx D (σ + 1) (σ + 1)) (i : Fin σ) (k : Fin (σ + 1)) :
    (B.d.pX * (x0 B * U)) i k = U (Fin.castSucc i) k := by
  rw [← Matrix.mul_assoc, Matrix.mul_apply]
  simp only [besselFlagProjection_mul_fourierBesselBasePoint_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem simpleSum_eq_upSum {n : GA D B.V} {U : Mx D (σ + 1) (σ + 1)} (e : mt B.V n * x0 B = x0 B * U) :
    simpleSum B.d (vecB B.o B.ζ) n = upSum U := by
  have hb : blockX B.d n = fun i j : Fin σ => U (Fin.castSucc i) (Fin.castSucc j) := by
    ext i j
    have h := mul_fourierBesselBasePoint_castSucc_column B (B.d.pX * mt B.V n) i j
    rw [Matrix.mul_assoc, Matrix.mul_assoc] at h
    rw [blockX, ← besselFlagProjection_mul_basePoint_mul_apply B U i, ← e, h]
  have hc : coefX B.d (vecB B.o B.ζ) n = fun i => U (Fin.castSucc i) (Fin.last σ) := by
    ext i
    have h := mul_fourierBesselBasePoint_last_column B (B.d.pX * mt B.V n) i
    rw [Matrix.mul_assoc] at h
    rw [coefX, ← besselFlagProjection_mul_basePoint_mul_apply B U i, ← e, h, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [simpleSum, hb, hc, upSum_succ]

theorem psiBes_eq_psiUni (ψ : AddChar (AF D.host.F) ℂ) {n : GA D B.V} (h : GA D B.A) (u : UX D (σ + 1))
    (e : mt B.V (n * embA B.d B.o h) * x0 B = x0 B * u.1.1) :
    psiBes ψ B.d 1 (vecB B.o B.ζ) n = psiUni ψ u.1 := by
  rw [mt_mul, Matrix.mul_assoc, besselAnisotropicEmbedding_fixes_basePoint] at e
  rw [psiBes, simpleSum_eq_upSum B e, map_one, one_mul, psiUni]

end GlobalTheory.Unf.FB.UniRad

namespace GlobalTheory.Unf.FB.UniRad

variable {D : D7} {σ : ℕ} (B : BesLev D σ)

theorem vecB_ne : vecB B.o B.ζ ≠ 0 := by
  have hζ : B.ζ ≠ 0 := fun h => B.line.2 (by rw [h]; simp)
  intro h
  apply hζ
  have := congrArg (B.o.qB *ᵥ ·) h
  simpa [vecB, Matrix.mulVec_mulVec, B.o.qB_iB] using this

theorem exists_form : ∃ r₀ : Fin B.V₀.rank → D.host.E, ratV r₀ ⬝ᵥ ratV (vecB B.o B.ζ) = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, vecB B.o B.ζ k ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact vecB_ne B (funext hc)
  refine ⟨Pi.single k (vecB B.o B.ζ k)⁻¹, ?_⟩
  rw [dotProduct, Finset.sum_eq_single k]
  · simp only [ratV, Pi.single_eq_same, ← map_mul, inv_mul_cancel₀ hk, map_one]
  · intro l _ hl
    simp only [ratV, Pi.single_eq_of_ne hl, map_zero, zero_mul]
  · exact fun h => absurd (Finset.mem_univ k) h

theorem vecMulVec_mulVec' {m k : ℕ} (w : Fin m → AE D) (r v : Fin k → AE D) (hr : r ⬝ᵥ v = 1) :
    vecMulVec w r *ᵥ v = w := by
  ext i
  simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, mul_assoc, ← Finset.mul_sum] at hr ⊢
  rw [hr, mul_one]

end GlobalTheory.Unf.FB.UniRad

namespace GlobalTheory.Unf.FB.UniRad

variable {D : D7} {σ : ℕ} (B : BesLev D σ)

def blk (U : Mx D (σ + 1) (σ + 1)) : Mx D σ σ := fun i j => U (Fin.castSucc i) (Fin.castSucc j)

theorem det_blk {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1) :
    (blk U).det = 1 := by
  have hT : (blk U).BlockTriangular id := fun i j h => (hU _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h)
  rw [Matrix.det_of_upperTriangular hT]
  exact Finset.prod_eq_one fun i _ => (hU (Fin.castSucc i) (Fin.castSucc i)).2

def blkU {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1) :
    GL (Fin σ) (AE D) :=
  Matrix.nonsingInvUnit (blk U) (by rw [det_blk hU]; exact isUnit_one)

theorem blkU_val {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1) :
    (blkU hU).1 = blk U := rfl

theorem blkU_mem {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1) :
    blkU hU ∈ upperUni σ (AE D) := fun i j =>
  ⟨fun h => (hU (Fin.castSucc i) (Fin.castSucc j)).1 (Fin.castSucc_lt_castSucc_iff.2 h),
    (hU (Fin.castSucc i) (Fin.castSucc i)).2⟩

def blkQ (γ : Matrix (Fin (σ + 1)) (Fin (σ + 1)) D.host.E) : Matrix (Fin σ) (Fin σ) D.host.E :=
  fun i j => γ (Fin.castSucc i) (Fin.castSucc j)

theorem blk_rat (γ : Matrix (Fin (σ + 1)) (Fin (σ + 1)) D.host.E) : blk (rat γ : Mx D (σ + 1) (σ + 1)) = rat (blkQ γ) := rfl

theorem blkU_rat {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1)
    {γ : Matrix (Fin (σ + 1)) (Fin (σ + 1)) D.host.E} (hγ : rat γ = U) :
    (blkU hU).1 ∈ ratMx D σ σ ∧ ((blkU hU)⁻¹).1 ∈ ratMx D σ σ := by
  have ha1 : (blkU hU).1 = rat (blkQ γ) := by rw [blkU_val, ← hγ, blk_rat]
  have hdet : (blkQ γ).det = 1 := by
    apply incA_injective
    rw [map_one, RingHom.map_det]
    have e : (incA D).mapMatrix (blkQ γ) = blk U := by rw [← hγ, blk_rat]; rfl
    rw [e, det_blk hU]
  have e : rat (blkQ γ)⁻¹ * (blkU hU).1 = 1 := by
    rw [ha1, ← rat_mul, Matrix.nonsing_inv_mul _ (by rw [hdet]; exact isUnit_one), rat_one]
  refine ⟨by rw [ha1]; exact rat_mem _, ?_⟩
  have hinv : ((blkU hU)⁻¹).1 = rat (blkQ γ)⁻¹ := by
    calc ((blkU hU)⁻¹).1 = (rat (blkQ γ)⁻¹ * (blkU hU).1) * ((blkU hU)⁻¹).1 := by rw [e, Matrix.one_mul]
      _ = rat (blkQ γ)⁻¹ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [hinv]; exact rat_mem _

theorem rat_vecMulVec {m k : ℕ} (w : Fin m → D.host.E) (r : Fin k → D.host.E) :
    (rat (vecMulVec w r) : Mx D m k) = vecMulVec (ratV w) (ratV r) := by
  ext i j
  simp only [rat, Matrix.map_apply, vecMulVec_apply, ratV, map_mul]

theorem besselFlagElement_mul_basePoint_eq_basePoint_mul {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1)
    (a : GL (Fin σ) (AE D)) (ha : a.1 = blk U) (b : Mx D σ B.V₀.rank)
    (hbz : a.1 *ᵥ (b *ᵥ ratV (vecB B.o B.ζ)) = fun i => U (Fin.castSucc i) (Fin.last σ)) :
    mt B.V (B.d.levi a * B.d.nB b) * x0 B = x0 B * U := by
  have hX : mt B.V (B.d.levi a * B.d.nB b) * B.d.jX = B.d.jX * a.1 := by
    rw [mt_mul, Matrix.mul_assoc, B.d.nB_jX, B.d.levi_jX]
  have h0 : mt B.V (B.d.levi a * B.d.nB b) * B.d.j0 = B.d.j0 + B.d.jX * (a.1 * b) := by
    rw [mt_mul, Matrix.mul_assoc, B.d.nB_j0, Matrix.mul_add, B.d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc, B.d.levi_jX,
      Matrix.mul_assoc]
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [mul_fourierBesselBasePoint_last_column, fourierBesselBasePoint_mul_eq, Matrix.mulVec_mulVec, h0, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hbz, Pi.add_apply, (hU (Fin.last σ) (Fin.last σ)).2, mul_one]
    exact add_comm _ _
  · rw [mul_fourierBesselBasePoint_castSucc_column, fourierBesselBasePoint_mul_eq, hX, (hU (Fin.last σ) (Fin.castSucc j)).1 (Fin.castSucc_lt_last j), mul_zero, add_zero,
      Matrix.mul_apply, ha]
    rfl

theorem exists_flag (u : UX D (σ + 1)) :
    ∃ n ∈ flagN B.d, mt B.V n * x0 B = x0 B * u.1.1 ∧ (u ∈ UXQ D (σ + 1) → n ∈ GQ B.V) := by
  have hU : ∀ i j : Fin (σ + 1), (j < i → u.1.1 i j = 0) ∧ u.1.1 i i = 1 := u.2
  obtain ⟨r₀, hr⟩ := exists_form B
  obtain ⟨c, hc⟩ : ∃ c : Fin σ → AE D, c = fun i => u.1.1 (Fin.castSucc i) (Fin.last σ) := ⟨_, rfl⟩
  have hbz : (blkU hU).1 *ᵥ (vecMulVec (((blkU hU)⁻¹).1 *ᵥ c) (ratV r₀) *ᵥ ratV (vecB B.o B.ζ)) = c := by
    rw [vecMulVec_mulVec' _ _ _ hr, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [hc] at hbz
  refine ⟨_, mul_mem (B.d.levi_mem_NFlag (blkU_mem hU)) (B.d.nB_mem_NFlag _),
    besselFlagElement_mul_basePoint_eq_basePoint_mul B hU (blkU hU) (blkU_val hU) _ hbz, fun hq => ?_⟩
  obtain ⟨γ, hγ⟩ := mem_ratMx.1 hq.1
  have hr' := blkU_rat hU hγ
  have hc' : c = ratV (fun i => γ (Fin.castSucc i) (Fin.last σ)) := by
    rw [hc]; ext i; simp only [ratV, ← hγ, rat, Matrix.map_apply]
  obtain ⟨δ, hδ⟩ := mem_ratMx.1 hr'.2
  have hbq : vecMulVec (((blkU hU)⁻¹).1 *ᵥ c) (ratV r₀) ∈ ratMx D σ B.V₀.rank := by
    rw [← hδ, hc', ← ratV_mulVec, ← rat_vecMulVec]
    exact rat_mem _
  rw [hc] at hbq
  exact mul_mem (B.d.levi_mem_GQ hr'.1 hr'.2) (B.d.nB_mem_GQ hbq)

end GlobalTheory.Unf.FB.UniRad

namespace GlobalTheory.Unf.FB

theorem uniRad_surj_psi : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), (∀ u : UX D (σ + 1), ∃ n ∈ flagN B.d, mt B.V n * x0 B = x0 B * u.1.1 ∧ (u ∈ UXQ D (σ + 1) → n ∈ GQ B.V)) ∧ ∀ (ψ : AddChar (AF D.host.F) ℂ), ∀ n ∈ flagN B.d, ∀ (h : GA D B.A) (u : UX D (σ + 1)), mt B.V (n * embA B.d B.o h) * x0 B = x0 B * u.1.1 → psiBes ψ B.d 1 (vecB B.o B.ζ) n = psiUni ψ u.1 :=
  fun _ _ B => ⟨UniRad.exists_flag B, fun ψ _ _ h u e => UniRad.psiBes_eq_psiUni B ψ h u e⟩

end GlobalTheory.Unf.FB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentRadicalSurjectsUnitriangularCharactStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagUnipotentRadical_surjects_unitriangular_characters_agree : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), (∀ u : UX D (σ + 1), ∃ n ∈ flagN B.d, mt B.V n ⬝ x0 B = x0 B ⬝ u.1.1 ∧ (u ∈ UXQ D (σ + 1) → n ∈ GQ B.V)) ∧ ∀ (ψ : AddChar (AF D.host.F) ℂ), ∀ n ∈ flagN B.d, ∀ (h : GA D B.A) (u : UX D (σ + 1)), mt B.V (n * embA B.d B.o h) ⬝ x0 B = x0 B ⬝ u.1.1 → psiBes ψ B.d 1 (vecB B.o B.ζ) n = psiUni ψ u.1 := by
  first | exact @GlobalTheory.Unf.FB.uniRad_surj_psi | exact GlobalTheory.Unf.FB.uniRad_surj_psi | (intros; apply GlobalTheory.Unf.FB.uniRad_surj_psi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemUnitaryAdelicSupportedSubgro
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemUnitaryAdelicSupportedSubgro
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneCosetEmb

theorem wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (P : Pl D → Prop) (g : GA D S₀), g ∈ grpAt S₀ P → d.emb0 g ∈ grpAt S P := fun _ _ _ _ d _ _ hg => GlobalTheory.IwaPlace.wittCoreEmbedding_preserves_supportedUnitarySubgroup d hg

end GlobalTheory.OneCosetEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemUnitaryAdelicSupportedSubgroStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.emb0_mem_grpAt_of_mem_grpAt : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (P : Pl D → Prop) (g : GA D S₀), g ∈ grpAt S₀ P → d.emb0 g ∈ grpAt S P := by
  first | exact @GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup | exact GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup | (intros; apply GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOfTrivialAtPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOfTrivialAtPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.fixes_latV_of_mem_grpOff : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop), ∀ g ∈ grpOff S P, Moves S g L L P := by
  intro D S L P g hg y hy
  obtain ⟨⟨ε, -, -, -, hAt, hOff⟩, -⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P
  have hmul : ∀ a ∈ idOff D P, ∀ b ∈ idAt D P, a * b = 0 := by
    intro a ha b hb
    rw [← (hAt b).1 hb, ← mul_assoc, mul_comm a ε, (hOff a).1 ha, zero_mul]
  have hker := MonoidHom.mem_ker.1 hg
  have hent : ∀ i j, mt S g i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idOff D P := by
    intro i j
    rw [← Ideal.Quotient.eq]
    have h2 := congrArg (fun u : GL (Fin S.rank) (AE D ⧸ idOff D P) => u.1 i j) hker
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h2
    have h3 : Ideal.Quotient.mk (idOff D P) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
        (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ idOff D P)) i j := by
      by_cases hij : i = j
      · subst hij; simp only [Matrix.one_apply_eq, map_one]
      · simp only [Matrix.one_apply_ne hij, map_zero]
    rw [h3, ← h2]
    rfl
  have hfix : mt S g *ᵥ y = y := by
    funext i
    have e : (mt S g *ᵥ y) i = y i + ∑ j, (mt S g i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j := by
      simp [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply]
    rw [e, Finset.sum_eq_zero (fun j _ => hmul _ (hent i j) _ (hy j)), add_zero]
  rw [hfix]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOfTrivialAtPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carriesLatticeCompletion_of_trivialAtPlaces : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop), ∀ g ∈ grpOff S P, Moves S g L L P := by
  first | exact @GlobalTheory.fixes_latV_of_mem_grpOff | exact GlobalTheory.fixes_latV_of_mem_grpOff | (intros; apply GlobalTheory.fixes_latV_of_mem_grpOff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceStdCharContinuousNontrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceStdCharContinuousNontrivial
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitChar

theorem cont_ne_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → IsStdChar D ψ (-1) →
    Continuous χ ∧ χ ≠ 1 := by
  intro D k _ _ _ _ p ψ χ hχ hψ
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have htr : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun a : k => psiE ψ (p.sec a) := hψ.1.1.comp (htr.comp p.cont_sec)
  refine ⟨?_, ?_⟩
  · have h' : Continuous fun a : k => ((χ a : Circle) : ℂ) := by
      have he : (fun a : k => ((χ a : Circle) : ℂ)) = fun a => psiE ψ (p.sec a) := funext hχ
      rw [he]; exact hc
    first
      | exact Circle.isEmbedding_coe.continuous_iff.2 h'
      | exact continuous_induced_rng.2 h'
  · intro h1
    obtain ⟨a, ha⟩ := GlobalTheory.FinPl.CharNontriv.exists_psiE_sec_ne_one D k p ψ hψ
    apply ha
    rw [← hχ a, h1]
    simp

end GlobalTheory.FinPl.SplitChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceStdCharContinuousNontrivialStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_stdChar_continuous_nontrivial : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → IsStdChar D ψ (-1) → Continuous χ ∧ χ ≠ 1 := by
  first | exact @GlobalTheory.FinPl.SplitChar.cont_ne_one | exact GlobalTheory.FinPl.SplitChar.cont_ne_one | (intros; apply GlobalTheory.FinPl.SplitChar.cont_ne_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CaRepApply
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SrcGl

variable {D : D7}

def CA (A : HSp D) : Submodule ℂ (GA D A → ℂ) where
  carrier := {φ | GlobalTheory.Unf.IsContAut A φ}
  add_mem' {φ ψ} hφ hψ := ⟨fun γ hγ g => by simp [hφ.1 γ hγ g, hψ.1 γ hγ g], hφ.2.add hψ.2⟩
  zero_mem' := ⟨fun _ _ _ => rfl, continuous_const⟩
  smul_mem' c φ hφ := ⟨fun γ hγ g => by simp [hφ.1 γ hγ g], continuous_const.mul hφ.2⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {n : Type} [Fintype n] [DecidableEq n]

theorem rep_mem_CA {A : HSp D} (α : Frame p A n) (g : GL n k) {φ : GA D A → ℂ} (h : φ ∈ CA A) : α.rep g φ ∈ CA A :=
  ⟨fun γ hγ x => by
    change φ (γ * x * α.gl g) = φ (x * α.gl g)
    rw [mul_assoc, h.1 γ hγ], h.2.comp (continuous_mul_const _)⟩

def caRep {A : HSp D} (α : Frame p A n) : Representation ℂ (GL n k) (CA A) where
  toFun g := (α.rep g).restrict fun _ h => rep_mem_CA α g h
  map_one' := by ext φ x; simp
  map_mul' g h := by ext φ x; simp

@[simp] theorem caRep_apply {A : HSp D} (α : Frame p A n) (g : GL n k) (φ : CA A) :
    ((caRep α g φ : CA A) : GA D A → ℂ) = α.rep g φ := rfl

def blkHom : Matrix n n k →* Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) k where
  toFun x := fromBlocks x 0 0 1
  map_one' := by simp
  map_mul' x y := by simp [fromBlocks_multiply]

def blk : GL n k →* GL (n ⊕ Fin 1) k := Units.map blkHom

@[simp] theorem blk_val (g : GL n k) : (blk g).val = fromBlocks g.val (0 : Matrix n (Fin 1) k) 0 1 := rfl

end GlobalTheory.FinPl.SrcGl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FubiniCompactQuotient
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

open scoped Pointwise

namespace GlobalTheory

theorem fubini_compact_quotient : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure] (Γ : Subgroup H), Countable Γ → DiscreteTopology Γ → (∃ K : Set H, IsCompact K ∧ ∀ g, ∃ γ ∈ Γ, γ * g ∈ K) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 μ → ∀ (X : Type) [MeasurableSpace X] (m : Measure X) [SFinite m] (f : H → X → ℂ), Measurable (Function.uncurry f) → (∀ γ ∈ Γ, ∀ h x, f (γ * h) x = f h x) → (∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ h ∈ K, ∫⁻ x, ‖f h x‖ₑ ∂m ≤ B) → Integrable (Function.uncurry f) ((μ.restrict 𝓕).prod m) := by
  intro H _ _ _ _ _ _ _ _ μ _ Γ hΓc hΓd hK 𝓕 h𝓕 X _ m _ f hf hinv hB
  obtain ⟨K, hKc, hKcov⟩ := hK
  obtain ⟨B, hB⟩ := hB K hKc
  haveI : Countable Γ := hΓc

  have hbd : ∀ h, ∫⁻ x, ‖f h x‖ₑ ∂m ≤ B := by
    intro h
    obtain ⟨γ, hγ, hk⟩ := hKcov h
    have := hB _ hk
    simpa only [hinv γ hγ h] using this

  have hfin : μ 𝓕 < ⊤ := by
    have hcover : 𝓕 ⊆ ⋃ g : Γ, (g • K) := by
      intro h _
      obtain ⟨γ, hγ, hk⟩ := hKcov h
      refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩⁻¹, ?_⟩
      refine Set.mem_smul_set.2 ⟨γ * h, hk, ?_⟩
      simp [Subgroup.smul_def]
    have hle : μ 𝓕 ≤ μ K := by
      calc μ 𝓕 = μ ((⋃ g : Γ, (g • K)) ∩ 𝓕) := by
              rw [Set.inter_eq_right.2 hcover]
        _ = μ (⋃ g : Γ, (g • K ∩ 𝓕)) := by rw [Set.iUnion_inter]
        _ ≤ ∑' g : Γ, μ (g • K ∩ 𝓕) := measure_iUnion_le _
        _ = μ K := (h𝓕.measure_eq_tsum K).symm
    exact hle.trans_lt hKc.measure_lt_top
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have hm : AEMeasurable (fun z : H × X => ‖Function.uncurry f z‖ₑ) ((μ.restrict 𝓕).prod m) :=
    hf.enorm.aemeasurable
  rw [HasFiniteIntegral, lintegral_prod _ hm]
  calc ∫⁻ h, ∫⁻ x, ‖Function.uncurry f (h, x)‖ₑ ∂m ∂(μ.restrict 𝓕)
      ≤ ∫⁻ _, (B : ENNReal) ∂(μ.restrict 𝓕) := lintegral_mono (fun h => hbd h)
    _ = B * μ 𝓕 := by simp
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hfin

end GlobalTheory
end
