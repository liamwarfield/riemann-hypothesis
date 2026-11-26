module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
noncomputable section

open scoped NNReal ComplexConjugate
open Filter Topology Set Metric MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.Mem.Th (InfF CptF)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Eis

variable {D : D7} (V : HSp D)

def EisRegularAt (Φ : ℂ → GA D (dblSp V) → ℂ) (s₀ : ℂ) (k : ℕ) : Prop :=
  ∃ (r : ℝ) (H : ℂ → GA D (dblSp V) → ℂ), 0 < r ∧
    (∀ s ∈ ball s₀ r, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * eisCont V Φ s g) ∧
    (∀ g, DifferentiableOn ℂ (H · g) (ball s₀ r)) ∧
    ContinuousOn (fun x : ℂ × GA D (dblSp V) => H x.1 x.2) (ball s₀ r ×ˢ univ) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball s₀ r, ∀ g, ‖H s g‖ ≤ C * Grow.height (dblSp V) g ^ N

def petCoef (m : Measure (GA D V)) (f₁ f₂ : GA D V → ℂ) : GA D V → ℂ := fun g => Cusp.petersson V m (rTr V g f₁) f₂

def BasicIdentity (μ : (AE D)ˣ →* Circle) (m : Measure (GA D V)) (Φ : GA D (dblSp V) → ℂ) (f₁ f₂ : GA D V → ℂ) : Prop :=
  DblConv V μ m (eis V Φ) f₁ f₂ ∧ ZetaConvH D.sp.cm.sig (gram_hdbl V) m Φ (petCoef V m f₁ f₂) ∧
    dblInt V μ m (eis V Φ) f₁ f₂ = zetaH D.sp.cm.sig (gram_hdbl V) m Φ (petCoef V m f₁ f₂)

end GlobalTheory.Eis

namespace GlobalTheory.Published

open GlobalTheory.Eis

def DoublingMethod : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a →
    HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
    ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D μ → ResEta D μ b →
    ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ →
      (EisContinues V (flat V a φ s₁) ∧ ∀ s₀, ∃ k, EisRegularAt V (flat V a φ s₁) s₀ k) ∧
      (V.rank < b → EisPoleLE V (flat V a φ s₁) (((b : ℂ) - V.rank) / 2) 1) ∧
      ∀ θ : InfF D, IsInfFam θ → V.SigOK → ∀ A : CptF V, Cusp.IsCartanFrame V A →
        ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ ∈ Cusp.A0 θ V A, ∀ f₂ ∈ Cusp.A0 θ V A,
          (∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → BasicIdentity V μ m (flat V a φ s₁ s) f₁ f₂) ∧
          ZetaContinues V μ m (flat V a φ s₁) f₁ f₂

end GlobalTheory.Published

namespace GlobalTheory.Eis

theorem dslope_family {X : Type} [TopologicalSpace X] {H : ℂ → X → ℂ} {w : X → ℝ} {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : ∀ x, DifferentiableOn ℂ (H · x) (ball s₀ r))
    (hc : ContinuousOn (fun p : ℂ × X => H p.1 p.2) (ball s₀ r ×ˢ univ))
    (hb : ∀ s ∈ ball s₀ r, ∀ x, ‖H s x‖ ≤ w x) (h0 : ∀ x, H s₀ x = 0) :
    (∀ x, DifferentiableOn ℂ (dslope (H · x) s₀) (ball s₀ (r / 2))) ∧
    ContinuousOn (fun p : ℂ × X => dslope (H · p.2) s₀ p.1) (ball s₀ (r / 2) ×ˢ univ) ∧
    ∀ s ∈ ball s₀ (r / 2), ∀ x, ‖dslope (H · x) s₀ s‖ ≤ w x / r := by
  have hsub : ball s₀ (r / 2) ⊆ ball s₀ r := ball_subset_ball (by linarith)
  have hsub' : closedBall s₀ (r / 2) ⊆ ball s₀ r := closedBall_subset_ball (by linarith)
  have h1 : ∀ x, DifferentiableOn ℂ (dslope (H · x) s₀) (ball s₀ r) := fun x =>
    (Complex.differentiableOn_dslope (ball_mem_nhds _ hr)).2 (hd x)
  refine ⟨fun x => (h1 x).mono hsub, ?_, fun s hs x => Complex.norm_dslope_le_div_of_mapsTo_ball (hd x)
    (fun z hz => by simpa [h0] using hb z hz x) (hsub hs)⟩
  rintro ⟨s₁, x₀⟩ ⟨hs₁, -⟩
  have h2 : ContinuousWithinAt (fun p : ℂ × X => dslope (H · x₀) s₀ p.1) (ball s₀ (r / 2) ×ˢ univ) (s₁, x₀) :=
    (((h1 x₀).continuousOn.continuousAt (isOpen_ball.mem_nhds (hsub hs₁))).comp_of_eq continuousAt_fst rfl).continuousWithinAt
  have h3 : Tendsto (fun p : ℂ × X => dslope (H · p.2) s₀ p.1 - dslope (H · x₀) s₀ p.1)
      (𝓝[ball s₀ (r / 2) ×ˢ univ] (s₁, x₀)) (𝓝 0) := by
    refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε => ?_
    have h4 : ∀ᶠ x in 𝓝 x₀, ∀ z ∈ closedBall s₀ (r / 2), ‖H z x - H z x₀‖ < ε * (r / 4) := by
      refine (isCompact_closedBall s₀ (r / 2)).eventually_forall_of_forall_eventually fun z hz => ?_
      have h5 : ∀ y, ContinuousAt (fun p : ℂ × X => H p.1 p.2) (z, y) := fun y =>
        hc.continuousAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨hsub' hz, trivial⟩)
      have h6 : ContinuousAt (fun p : X × ℂ => ‖H p.2 p.1 - H p.2 x₀‖) (x₀, z) :=
        (((h5 x₀).comp_of_eq (f := fun p : X × ℂ => (p.2, p.1)) (by fun_prop) rfl).sub
          ((h5 x₀).comp_of_eq (f := fun p : X × ℂ => (p.2, x₀)) (by fun_prop) rfl)).norm
      exact h6.eventually (gt_mem_nhds (by simpa using by positivity))
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (continuousAt_snd.eventually h4)] with p hp h4
    have h7 := Complex.norm_dslope_le_div_of_mapsTo_ball (f := fun z => H z p.2 - H z x₀) (R₂ := ε * (r / 4))
      (((hd _).sub (hd _)).mono hsub) (fun z hz => by simpa [h0] using (h4 z (ball_subset_closedBall hz)).le) hp.1
    have h8 : dslope (fun z => H z p.2 - H z x₀) s₀ p.1 = dslope (H · p.2) s₀ p.1 - dslope (H · x₀) s₀ p.1 := by
      rcases eq_or_ne p.1 s₀ with e | e
      · rw [e, dslope_same, dslope_same, dslope_same]
        exact deriv_fun_sub ((hd _).differentiableAt (ball_mem_nhds _ hr)) ((hd _).differentiableAt (ball_mem_nhds _ hr))
      · simp only [dslope_of_ne _ e, slope_def_field]; ring
    rw [← h8]
    refine h7.trans_lt ?_
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hε hr]
  simpa [ContinuousWithinAt] using h3.add h2

variable {D : D7} {V : HSp D} {Φ : ℂ → GA D (dblSp V) → ℂ} {s₀ : ℂ} {j k : ℕ}

theorem EisRegularAt.succ (h : EisRegularAt V Φ s₀ k) : EisRegularAt V Φ s₀ (k + 1) := by
  obtain ⟨r, H, hr, e, hd, hc, C, N, hb⟩ := h
  refine ⟨r, fun s g => (s - s₀) * H s g, hr, fun s hs h0 g => by simp only [e s hs h0]; ring,
    fun g => (differentiableOn_id.sub_const _).mul (hd g), (by fun_prop : ContinuousOn (fun x : ℂ × _ => x.1 - s₀) _).mul hc,
    r * C, N, fun s hs g => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul (mem_ball_iff_norm.1 hs).le (hb s hs g) (norm_nonneg _) hr.le

theorem EisRegularAt.pred (h : EisRegularAt V Φ s₀ (k + 1)) (hp : EisPoleLE V Φ s₀ j) (hj : j ≤ k) :
    EisRegularAt V Φ s₀ k := by
  obtain ⟨r, H, hr, e, hd, hc, C, N, hb⟩ := h
  have h0 : ∀ g, H s₀ g = 0 := fun g => by
    obtain ⟨E, hE, -⟩ := id (hp.2 g)
    obtain ⟨c, hc⟩ := hE.poleLE_iff.1 (hp.2 g)
    have h1 : Tendsto (fun s => (s - s₀) ^ (k + 1 - j)) (𝓝[≠] s₀) (𝓝 0) :=
      (Continuous.tendsto' (by fun_prop) s₀ 0 (by simp; omega)).mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique (((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {s₀}ᶜ))) ((zero_mul c ▸ h1.mul hc).congr' ?_)
    filter_upwards [hE.cont_eventuallyEq, self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₀ hr)]
      with s h2 h3 h4
    rw [e s h4 h3, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega), ← h2]
    rfl
  obtain ⟨h1, h2, h3⟩ := dslope_family hr hd hc hb h0
  refine ⟨r / 2, fun s g => dslope (H · g) s₀ s, half_pos hr, fun s hs hs' g => ?_, h1, h2, C / r, N, fun s hs g => ?_⟩
  · have := sub_ne_zero.2 hs'
    simp only [dslope_of_ne _ hs', slope_def_field, h0, e s (ball_subset_ball (by linarith) hs) hs']
    field_simp
    ring
  · rw [div_mul_eq_mul_div]; exact h3 s hs g

theorem EisRegularAt.of_poleLE (h : EisRegularAt V Φ s₀ k) (hp : EisPoleLE V Φ s₀ j) : EisRegularAt V Φ s₀ j := by
  rcases le_total k j with hk | hk
  · exact Nat.le_induction h (fun _ _ => EisRegularAt.succ) j hk
  · exact Nat.decreasingInduction (motive := fun i _ => j ≤ i → EisRegularAt V Φ s₀ i)
      (fun i _ ih hi => (ih (by omega)).pred hp hi) (fun _ => h) hk le_rfl

theorem EisRegularAt.of_eisValueAt {ψ : GA D (dblSp V) → ℂ} (h : EisRegularAt V Φ s₀ k) (hv : EisValueAt V Φ s₀ ψ) :
    ∃ r : ℝ, 0 < r ∧ (∀ g, DifferentiableOn ℂ (eisCont V Φ · g) (ball s₀ r)) ∧
      ContinuousOn (fun x : ℂ × GA D (dblSp V) => eisCont V Φ x.1 x.2) (ball s₀ r ×ˢ univ) ∧
      ∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball s₀ r, ∀ g, ‖eisCont V Φ s g‖ ≤ C * Grow.height (dblSp V) g ^ N := by
  obtain ⟨r, H, hr, e, hd, hc, C, N, hb⟩ := h.of_poleLE (eisValueAt_iff_eisPoleLE.1 hv).1
  have e' : ∀ s ∈ ball s₀ r, ∀ g, eisCont V Φ s g = H s g := fun s hs g => by
    rcases eq_or_ne s s₀ with rfl | h0
    · refine tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] s)
        ((hv.2 g).analyticAt_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s hr)] with z h1 h2
      rw [e z h2 h1, pow_zero, one_mul]; rfl
    · rw [e s hs h0, pow_zero, one_mul]
  exact ⟨r, hr, fun g => (hd g).congr fun s hs => e' s hs g, hc.congr fun x hx => e' _ hx.1 _, C, N,
    fun s hs g => e' s hs g ▸ hb s hs g⟩

section Consequences

variable (hP : Published.DoublingMethod) (h0 : 0 < V.rank) {a : GL (Fin V.rank) (AE D)} (ha : IsMaj V a)
  (hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a)) {μ : (AE D)ˣ →* Circle} {b : ℕ} (hμ : IsHeckeChar D μ)
  (hb : ResEta D μ b) {s₁ : ℂ} {φ : GA D (dblSp V) → ℂ} (hφ : φ ∈ degPS V a μ s₁)
include hP h0 ha hI hμ hb hφ

end Consequences

end GlobalTheory.Eis

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.Published

def AdmissibleCoefficientsAnalytic : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε π →
    ∀ v w : H, IsKFin ε π v → IsKFin ε π w → AnalyticOnUJ ε fun g => ⟪w, π g v⟫_ℂ

def LeviSubmoduleDense : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
      (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (mats (leviOne ε W)) σ → IsIrredOn (mats (leviOne ε W)) σ →
      ∀ S : Submodule ℂ V, S ≠ ⊥ → (∀ v ∈ S, IsKFinIn (leviOne ε W) σ v) →
        (∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε W)) →
          ∀ v ∈ S, ∃ v' ∈ S, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) v' 0) →
        Dense (S : Set V)

def HarishChandraAnalyticity : Prop := AdmissibleCoefficientsAnalytic ∧ LeviSubmoduleDense

end GlobalTheory.Published

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaMean

variable {D : D7} {A B : HSp D}

def thetaMean {S T : HSp D} (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ν : Measure (GA D T))
    (f : WO S T → ℂ) : GA D S → ℂ :=
  fun g => ⨍ q, AutomorphicL2Unitary.descend (GQ T) (fun h => thetaKO ω g h f) q ∂autMeasure T ν

theorem lagr_add (z z' : WO A B) : lagr A B (z + z') = lagr A B z + lagr A B z' := Matrix.ext fun i k => by
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective k <;>
    simp only [Matrix.add_apply, lagr, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, neg_add]

theorem lagr_rat (γ : Matrix (Fin B.rank) (Fin A.rank) D.host.E) :
    lagr A B (rat γ) = ratW B (dblSp A) (Matrix.of fun i => pairVec finSumFinEquiv (γ i) (-(γ i))) :=
  Matrix.ext fun i k => by
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective k <;>
      simp only [lagr, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, ratW, rat, Matrix.of_apply,
        Matrix.map_apply, pairVec_inl, pairVec_inr, Pi.neg_apply,
        map_neg]

theorem continuous_lagr : Continuous (lagr A B) := continuous_matrix fun i k => by
  obtain ⟨i1, -⟩ := lattice_Mx D B.rank A.rank
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective k
  · simp only [lagr, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inl]
    exact continuous_id.matrix_elem i j
  · simp only [lagr, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inr]
    exact (continuous_neg (G := WO A B)).matrix_elem i j

theorem hO_lagr (z z' : WO A B) : hO (dblSp A) B (lagr A B z) (lagr A B z') = 0 := by
  have hi : (dblSp A).gram⁻¹ = blkMat finSumFinEquiv A.gram⁻¹ (-A.gram⁻¹) := Matrix.inv_eq_left_inv (by
    rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (gram_isUnit_det A), blkMat_one])
  simp only [hO, hi, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, lagr, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, map_zero,
    map_neg, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul, mul_neg, neg_neg, neg_zero,
    Finset.sum_neg_distrib, add_neg_cancel]

theorem symplOH_lagr (z z' : WO A B) : symplOH (dblSp A) B (lagr A B z) (lagr A B z') = 0 := by
  rw [symplOH, symplO, hO_lagr, mul_zero, map_zero, mul_zero]

variable {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : (AE D)ˣ →* Circle}

section Zero

variable {f : WO (dblSp A) B → ℂ} {μ μ' : Measure (WO A B)} {𝓨 𝓨' : Set (WO A B)}
  {ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)}

theorem periodic_lagr (hf : IsThetaFunO ψ (dblSp A) B f) :
    ∀ γ ∈ ratMx D B.rank A.rank, ∀ z, f (lagr A B (γ + z)) = f (lagr A B z) := by
  rintro _ ⟨γ, rfl⟩ z
  change f (lagr A B (rat γ + z)) = _
  rw [lagr_add, lagr_rat, hf.quasi, ← lagr_rat, symplOH_lagr, neg_zero, AddChar.map_zero_eq_one, one_mul]

theorem integrableOn_lagr (hμ : IsCovolOne (ratL B A) μ 𝓨) (hf : IsThetaFunO ψ (dblSp A) B f) :
    IntegrableOn (fun z => f (lagr A B z)) 𝓨 μ :=
  covolOne_integrableOn hμ _ (hf.cont.comp continuous_lagr) (periodic_lagr hf)

end Zero

variable {S T : HSp D} {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {f : WO S T → ℂ}
  (hω : IsWeilDatumO ψ S T χ χ' ω) (hf : IsThetaFunO ψ S T f)
include hω hf

theorem leftInv_theta (g : GA D S) : LeftInv (GQ T) fun h => thetaKO ω g h f := fun γ hγ h => by
  have := hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres (g, h) f hf)
  rwa [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul] at this

variable {ν : Measure (GA D T)} [ν.IsHaarMeasure]

theorem thetaMean_eq {𝓕 : Set (GA D T)} (h𝓕 : IsFundamentalDomain (GQ T) 𝓕 ν) (g : GA D S) :
    thetaMean ω ν f g = ⨍ h in 𝓕, thetaKO ω g h f ∂ν := by
  rw [thetaMean, average_eq, setAverage_eq, integral_quotMeasure h𝓕, measureReal_def, quotMeasure_univ h𝓕]
  simp only [(leftInv_theta hω hf g).descend_mk, measureReal_def]

end GlobalTheory.ThetaMean

namespace GlobalTheory.Published

open GlobalTheory.ThetaMean

def SiegelWeilAnisotropicUnitary : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → 1 ≤ B.rank → IsAniso B →
  ∀ (χB : (AE D)ˣ →* Circle) (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)),
    IsWeilDatumO ψ (dblSp A) B 1 χB ω →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a → HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) →
  ∀ (μ : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) μ 𝓨 →
  ∀ ν : Measure (GA D B), ν.IsHaarMeasure →
  ∀ f : WO (dblSp A) B → ℂ, IsThetaFunO ψ (dblSp A) B f → IsKFinVec ω (Khat A a) f →
    (∀ g, Integrable (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO ω g h f) (autMeasure B ν)) ∧
    Eis.EisValueAt A (flat A a (swSec A B ω μ 𝓨 f) (sZero A B)) (sZero A B)
      ((if A.rank < B.rank then 1 else 2 : ℂ) • thetaMean ω ν f)

end GlobalTheory.Published

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsGlobalCharDetPow
open MeasureTheory Set Filter Matrix Polynomial GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.HCChar
open Formalism.REAL (UJ KG muK Jm)
open Formalism.QuantumDeterminants (IsHCParam IsCRepOn)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsDS UJset)
open GlobalTheory.FlagMeas (IsIsoFlag flagM)
open scoped ENNReal NNReal Topology

noncomputable section

namespace GlobalTheory.HCChar.Model

end GlobalTheory.HCChar.Model
end
end
