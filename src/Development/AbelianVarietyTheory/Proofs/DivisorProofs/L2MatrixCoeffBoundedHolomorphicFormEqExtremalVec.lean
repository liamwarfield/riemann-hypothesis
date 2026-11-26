module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorMatrixCoeffHolomorphicType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueBarCompatibility
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeEqZeroOfTorusLawAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2MatrixCoeffBoundedHolomorphicFormEqExtremalVec
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2MatrixCoeffBoundedHolomorphicFormEqExtremalVec
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.InterpolationCoefficientsInL2

lemma inner_iso_eigen {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (U : K →L[ℂ] K)
    (hU : ∀ x, ‖U x‖ = ‖x‖) {F : K} {c : ℂ} (hc : ‖c‖ = 1) (hF : U F = c • F) (G : K) :
    ⟪F, U G⟫_ℂ = c * ⟪F, G⟫_ℂ := by
  have h := (LinearIsometry.mk (U : K →ₗ[ℂ] K) hU).inner_map_map F G
  change ⟪U F, U G⟫_ℂ = _ at h
  rw [hF, inner_smul_left] at h
  have h1 : c * (starRingEnd ℂ) c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  rw [← h, ← mul_assoc, h1, one_mul]

lemma rep_mul_apply {G K : Type*} [Monoid G] [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : G →* (K →L[ℂ] K))
    (a b : G) (F : K) : ρ (a * b) F = ρ a (ρ b F) := by
  rw [map_mul]; rfl

lemma inner_rep_one {G K : Type*} [Monoid G] [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : G →* (K →L[ℂ] K))
    (F : K) : ⟪F, ρ 1 F⟫_ℂ = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
  rw [map_one, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K]
  simp

section Local

variable {n : ℕ} {ι : Type} [Fintype ι] {Hm : ι → Mt n} {q : ι → ℕ} {x₀ : ι → Mt n} {w : ι → Fin n → ℤ}

lemma holFn_congr {f g : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f) (h : ∀ u ∈ UG Hm, g u = f u) :
    HolFn Hm q x₀ w g := by
  obtain ⟨P, hP, hf⟩ := hf
  exact ⟨P, hP, fun u hu => (h u hu).trans (hf u hu)⟩

lemma holFn_const_mul {f : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f) (c : ℂ) :
    HolFn Hm q x₀ w fun u => c * f u := by
  obtain ⟨P, ⟨hP1, hP2⟩, hf⟩ := hf
  refine ⟨fun x => c * P x, ⟨hP1.const_mul c, fun x hx b hb => ?_⟩, fun u hu => ?_⟩
  · beta_reduce
    rw [hP2 x hx b hb]; ring
  · beta_reduce
    rw [hf u hu]

lemma holFn_sub {f g : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f) (hg : HolFn Hm q x₀ w g) :
    HolFn Hm q x₀ w fun u => f u - g u := by
  obtain ⟨P, ⟨hP1, hP2⟩, hf⟩ := hf
  obtain ⟨Q, ⟨hQ1, hQ2⟩, hg⟩ := hg
  refine ⟨fun x => P x - Q x, ⟨hP1.sub hQ1, fun x hx b hb => ?_⟩, fun u hu => ?_⟩
  · beta_reduce
    rw [hP2 x hx b hb, hQ2 x hx b hb]; ring
  · beta_reduce
    rw [hf u hu, hg u hu]

omit [Fintype ι] in
lemma one_mem_UG : (1 : ι → Mt n) ∈ UG Hm := by
  intro τ
  change (1 : Mt n)ᴴ * Hm τ * 1 = Hm τ
  simp


lemma norm_prod_exp (w : Fin n → ℤ) (s : Fin n → ℝ) :
    ‖∏ a, Complex.exp ((s a : ℂ) * Complex.I) ^ w a‖ = 1 := by
  rw [norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [norm_zpow, Complex.norm_exp_ofReal_mul_I, _root_.one_zpow]

lemma norm_torCh (w : ι → Fin n → ℤ) (s : ι → Fin n → ℝ) : ‖torCh w s‖ = 1 := by
  unfold torCh
  rw [norm_prod]
  exact Finset.prod_eq_one fun τ _ => norm_prod_exp _ _

lemma eq_const_mul [DecidableEq ι] (hO : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {f g : (ι → Mt n) → ℂ} (c : ℂ)
    (hf : HolFn Hm q x₀ w f) (hg : HolFn Hm q x₀ w g)
    (hfl : ∀ u ∈ UG Hm, ∀ s, f (torEl x₀ s * u) = torCh w s * f u)
    (hgl : ∀ u ∈ UG Hm, ∀ s, g (torEl x₀ s * u) = torCh w s * g u) (hf1 : f 1 = c) (hg1 : g 1 = 1) :
    ∀ u ∈ UG Hm, f u = c * g u := fun u hu =>
  sub_eq_zero.1 (GlobalTheory.HolDict.Uniq.eq_zero_of_torus_law n ι Hm q x₀ w hO _ (holFn_sub hf (holFn_const_mul hg c))
    (fun u hu s => by beta_reduce; rw [hfl u hu, hgl u hu]; ring)
    (by beta_reduce; rw [hf1, hg1, mul_one, sub_self]) u hu)

end Local

end GlobalTheory.HolDict.InterpolationCoefficientsInL2


open GlobalTheory.HolDict.InterpolationCoefficientsInL2 in
theorem GlobalTheory.HolDict.inner_reg_eq_coef_extremal : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ (J : Set (GA D V)) (χ φ : GA D V → ℂ) F, HolForm θ M w J χ φ → Repr V μ 𝓕 F φ → ∀ u ∈ GinfC V, ⟪F, ρ u F⟫_ℂ = ((‖F‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (archM V (θ τ) u) (v τ : M.H τ)⟫_ℂ := by
  classical
  intro D θ V S M w v hθ hS hW hv μ 𝓕 ρ hfin hreg J χ φ F hφ hF u₀ hu₀
  refine (GlobalTheory.RealLift.exists_real_lift D θ V hθ).elim fun L hL => ?_
  have hL1 := hL.1
  have hLmul := hL.2.1
  have hUG := hL.2.2.2.1
  have hLinv := hL.2.2.2.2.1
  have hB := (GlobalTheory.HolDict.holFn_coef_extVec D θ V S M w v hθ hS hW hv).1
  have hBt := (GlobalTheory.HolDict.holFn_coef_extVec D θ V S M w v hθ hS hW hv).2
  have hO : ∀ τ, OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) :=
    fun τ => ((GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.2.2 hS).1
  have hU : ∀ τ, IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) := fun τ => (GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.1
  have htm : ∀ s, torEl (x0Mat M) s ∈ UG (gramAt D V) := fun s => by
    simpa using TorusLaw.mul_torEl_mem hO s (one_mem_UG (Hm := gramAt D V))
  have hL0 : L 1 = 1 := by
    have h := hLmul 1 one_mem_UG 1 one_mem_UG
    rw [mul_one] at h
    exact mul_left_cancel (a := L 1) (by rw [← h, mul_one])

  have horb : ∀ x, HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w fun u => φ (x * L u) := by
    intro x
    obtain ⟨f, hf, hfx⟩ := hφ.hol x
    refine holFn_congr hf fun u hu => ?_
    rw [hfx _ (hL1 u hu).1]
    congr 1
    funext τ
    exact (hL1 u hu).2 τ
  have htor : ∀ s x, φ (x * L (torEl (x0Mat M) s)) = torCh w s * φ x := by
    intro s x
    obtain ⟨h1, h2⟩ := GlobalTheory.HolDict.smFn_and_killedFn_of_holFn _ _ _ _ _ _ hO _ (horb x)
    have := GlobalTheory.HolDict.torus_law_of_killed _ _ _ _ _ _ hO _ h1 h2 1 one_mem_UG s
    simpa [hL0] using this
  refine hφ.bdd.elim fun C hC => ?_
  have hR := (GlobalTheory.HolDict.RepresentativeL2.repr_properties D V μ 𝓕 ρ hfin hreg).2.2
  have hR3 := hR.1
  have hR4 := hR.2.1
  have hR5 := hR.2.2.1
  have hR6 := hR.2.2.2
  have hρt : ∀ s, ρ (L (torEl (x0Mat M) s)) F = torCh w s • F := by
    intro s
    have h1 := hR4 F φ (L (torEl (x0Mat M) s)) hF
    have h2 := hR5 F F φ φ (torCh w s - 1) hF hF
    have e1 : (torCh w s - 1) • F + F = torCh w s • F := by rw [sub_smul, one_smul, sub_add_cancel]
    have e2 : (torCh w s - 1) • φ + φ = rTr V (L (torEl (x0Mat M) s)) φ := by
      funext x
      simp only [rTr, htor, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, e2] at h2
    exact hR3 _ _ _ h1 h2
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin.fin
  have hA : HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w fun u => ⟪F, ρ (L u) F⟫_ℂ := by
    have h := GlobalTheory.HolDict.holFn_integral _ _ _ _ _ w hO (GA D V) (μ.restrict 𝓕) (fun x u => star (φ x) * φ (x * L u)) (C * C)
      (fun x => holFn_const_mul (horb x) _)
      (fun x u _ => by
        rw [norm_mul, norm_star]
        exact mul_le_mul (hC _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hC x)))
      (fun u _ => (hR6 F _ φ _ hF (hR4 F φ (L u) hF)).1.aestronglyMeasurable)
    exact holFn_congr h fun u _ => (hR6 F _ φ _ hF (hR4 F φ (L u) hF)).2
  have key := eq_const_mul hO ((‖F‖ ^ 2 : ℝ) : ℂ) hA hB
    (fun u hu s => ((congrArg (fun g => ⟪F, ρ g F⟫_ℂ) (hLmul _ (htm s) _ hu)).trans
      (congrArg (fun G => ⟪F, G⟫_ℂ) (rep_mul_apply ρ _ _ F))).trans
      (inner_iso_eigen _ (hreg.iso _) (norm_torCh w s) (hρt s) _))
    (fun u hu s => by
      have a2 : ∀ τ, ⟪(v τ : M.H τ), M.rep τ ((torEl (x0Mat M) s * u) τ) (v τ : M.H τ)⟫_ℂ =
          (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) * ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ := by
        intro τ
        refine (congrArg (fun T : M.H τ →L[ℂ] M.H τ => ⟪(v τ : M.H τ), T (v τ : M.H τ)⟫_ℂ)
          ((hU τ).1.2 _ (htm s τ) _ (hu τ))).trans ?_
        exact inner_iso_eigen _ ((hU τ).2.1 _ (htm s τ)) (norm_prod_exp _ _) (hBt s τ) _
      exact (Finset.prod_congr rfl fun τ _ => a2 τ).trans Finset.prod_mul_distrib)
    ((congrArg (fun g => ⟪F, ρ g F⟫_ℂ) hL0).trans (inner_rep_one ρ F))
    (Finset.prod_eq_one fun τ _ => by
      refine (congrArg (fun T : M.H τ →L[ℂ] M.H τ => ⟪(v τ : M.H τ), T (v τ : M.H τ)⟫_ℂ) (hU τ).1.1).trans ?_
      change ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = 1
      rw [inner_self_eq_norm_sq_to_K, (hv τ).1]
      simp)
    _ (hUG u₀)
  exact (congrArg (fun g => ⟪F, ρ g F⟫_ℂ) (hLinv u₀ hu₀)).symm.trans key
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2MatrixCoeffBoundedHolomorphicFormEqExtremalVecStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_rho_eq_normSq_mul_prod_of_holForm : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ (J : Set (GA D V)) (χ φ : GA D V → ℂ) F, HolForm θ M w J χ φ → Repr V μ 𝓕 F φ → ∀ u ∈ GinfC V, ⟪F, ρ u F⟫_ℂ = ((‖F‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (archM V (θ τ) u) (v τ : M.H τ)⟫_ℂ := by
  first | exact @GlobalTheory.HolDict.inner_reg_eq_coef_extremal | exact GlobalTheory.HolDict.inner_reg_eq_coef_extremal | (intros; apply GlobalTheory.HolDict.inner_reg_eq_coef_extremal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisLineBundleSectionsProjectiveOverDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisLineBundleSectionsProjectiveOverDvr
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbLaw

theorem sec_eq_zero_of_local {X : Scheme.{0}} {L : LB X} {I : Type} (V : I → X.Opens)
    (hc : ⨆ a, V a = ⊤) (c : I → L.ι) (hV : ∀ a, V a ≤ L.U (c a)) (s : LB.Sec L)
    (h : ∀ a, rs X (hV a) (s.f (c a)) = 0) : s = 0 := by
  apply GlobalTheory.LB.f_injective
  funext i
  refine finSec_eq_zero_of_cover V hc (s.f i) fun a => ?_
  have h₁ : rs X (inf_le_left : L.U i ⊓ V a ≤ L.U i) (s.f i) =
      rs X (inf_le_inf le_rfl (hV a) : L.U i ⊓ V a ≤ L.U i ⊓ L.U (c a)) (L.g i (c a)).val *
        rs X (inf_le_right : L.U i ⊓ V a ≤ V a) (rs X (hV a) (s.f (c a))) := by
    have h := congrArg (rs X (inf_le_inf le_rfl (hV a) : L.U i ⊓ V a ≤ L.U i ⊓ L.U (c a)))
      (s.compat i (c a))
    rw [map_mul] at h
    simp only [rs_rs] at h ⊢
    exact h
  rw [h₁, h a, map_zero, mul_zero]

theorem sec_eq_of_local {X : Scheme.{0}} {L : LB X} {I : Type} (V : I → X.Opens)
    (hc : ⨆ a, V a = ⊤) (c : I → L.ι) (hV : ∀ a, V a ≤ L.U (c a)) (s t : LB.Sec L)
    (h : ∀ a, rs X (hV a) (s.f (c a)) = rs X (hV a) (t.f (c a))) : s = t :=
  sub_eq_zero.1 (sec_eq_zero_of_local V hc c hV _ fun a => by rw [GlobalTheory.LB.sub_f, map_sub, h a, sub_self])

section PerfSec

variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
  {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (Q : Perf f M) {g : R →+* R'} {π : X' ⟶ X}
  {f' : X' ⟶ Spec (CommRingCat.of R')}
  (E : {v : Fin Q.a → R' // (Q.D₀.map g).mulVec v = 0} ≃ LB.Sec (M.pull π))

theorem Perf.iSup_preimage : ⨆ i, π ⁻¹ᵁ Q.W i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, Q.cover]
  exact top_unique fun _ _ => trivial


include Q in
theorem Perf.sec_add
    (hE : ∀ v i, rs X' (le_pull M π (Q.le i)) ((E v).f (fun _ => Q.ch i)) =
        ∑ k, cst f' (π ⁻¹ᵁ Q.W i) (v.1 k) * (π.app (Q.W i)).hom (Q.u k i))
    (v w : {v : Fin Q.a → R' // (Q.D₀.map g).mulVec v = 0}) :
    E ⟨v.1 + w.1, by rw [Matrix.mulVec_add, v.2, w.2, add_zero]⟩ = E v + E w := by
  refine sec_eq_of_local (fun i => π ⁻¹ᵁ Q.W i) Q.iSup_preimage (fun i => fun _ => Q.ch i)
    (fun i => le_pull M π (Q.le i)) _ _ fun i => ?_
  refine (hE _ i).trans (Eq.trans ?_ ((map_add (rs X' (le_pull M π (Q.le i))) ((E v).f fun _ => Q.ch i)
    ((E w).f fun _ => Q.ch i)).trans (congrArg₂ (· + ·) (hE v i) (hE w i))).symm)
  simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]


include Q in
theorem Perf.sec_smul
    (hE : ∀ v i, rs X' (le_pull M π (Q.le i)) ((E v).f (fun _ => Q.ch i)) =
        ∑ k, cst f' (π ⁻¹ᵁ Q.W i) (v.1 k) * (π.app (Q.W i)).hom (Q.u k i))
    (r : R') (v : {v : Fin Q.a → R' // (Q.D₀.map g).mulVec v = 0}) :
    E ⟨r • v.1, by rw [Matrix.mulVec_smul, v.2, smul_zero]⟩ = cst f' ⊤ r • E v := by
  refine sec_eq_of_local (fun i => π ⁻¹ᵁ Q.W i) Q.iSup_preimage (fun i => fun _ => Q.ch i)
    (fun i => le_pull M π (Q.le i)) _ _ fun i => ?_
  have key : rs X' (le_pull M π (Q.le i)) (resG X' le_top (cst f' ⊤ r)) = cst f' (π ⁻¹ᵁ Q.W i) r := by
    change rs X' _ (rs X' le_top _) = _
    rw [rs_rs, rs_cst]
  refine (hE _ i).trans (Eq.trans ?_ ((map_mul (rs X' (le_pull M π (Q.le i))) (resG X' le_top (cst f' ⊤ r))
    ((E v).f fun _ => Q.ch i)).trans (congrArg₂ (· * ·) key (hE v i))).symm)
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, _root_.mul_assoc]

end PerfSec

theorem finSecPullId_add {X : Scheme.{0}} {M : LB X} (s t : LB.Sec M) :
    finSecPullId (s + t) = finSecPullId s + finSecPullId t := by
  apply GlobalTheory.LB.f_injective
  funext j
  exact map_add _ _ _

theorem finSecPullId_smul {X : Scheme.{0}} {M : LB X} (a : Γ(X, ⊤)) (s : LB.Sec M) :
    finSecPullId (a • s) = a • finSecPullId s := by
  apply GlobalTheory.LB.f_injective
  funext j
  exact (map_mul _ _ _).trans (congrArg (· * _) (rs_rs _ _ _))

theorem eq_zero_of_finSecPullId {X : Scheme.{0}} {R : Type} [CommRing R]
    {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (Q : Perf f M) (s : LB.Sec M)
    (hs : finSecPullId s = 0) : s = 0 := by
  refine sec_eq_zero_of_local Q.W Q.cover Q.ch Q.le s fun j => ?_
  have hle : Q.W j ≤ (M.pull (𝟙 X)).U (fun _ => Q.ch j) :=
    le_trans (show Q.W j ≤ (𝟙 X) ⁻¹ᵁ Q.W j from fun _ hx => hx) (le_pull M (𝟙 X) (Q.le j))
  have h := congrArg (fun σ : LB.Sec (M.pull (𝟙 X)) => rs X hle (σ.f (fun _ => Q.ch j))) hs
  refine Eq.trans ?_ (h.trans (map_zero (rs X hle)))
  exact (rs_rs _ _ _).symm

end GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem exists_basis_sec_of_isDiscreteValuationRing : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of W)) (M : LB X), Flat f → GlobalTheory.AbLaw.IsProjBy f → M.IsLB → ∃ (n : ℕ) (t : Fin n → LB.Sec M), ∀ u : LB.Sec M, ∃! c : Fin n → W, u = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (c j) • t j := by
  intro W _ _ _ X f M hf hp hM
  obtain ⟨Q⟩ := nonempty_perf_of_noetherian W X f hf hp M hM
  have hpb : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id W))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.id_horiz f
  obtain ⟨E, hE⟩ := Q.sec W (RingHom.id W) X (𝟙 X) f hpb
  let φ : LB.Sec M → Fin Q.a → W := fun s => (E.symm (finSecPullId s)).1
  have hadd : ∀ s t, φ (s + t) = φ s + φ t := by
    intro s t
    have h := Q.sec_add E hE (E.symm (finSecPullId s)) (E.symm (finSecPullId t))
    rw [E.apply_symm_apply, E.apply_symm_apply, ← finSecPullId_add, ← E.eq_symm_apply] at h
    exact (congrArg Subtype.val h).symm
  have hsmul : ∀ (r : W) s, φ (cst f ⊤ r • s) = r • φ s := by
    intro r s
    have h := Q.sec_smul E hE r (E.symm (finSecPullId s))
    rw [E.apply_symm_apply, ← finSecPullId_smul, ← E.eq_symm_apply] at h
    exact (congrArg Subtype.val h).symm
  have φ0 : φ 0 = 0 := by
    have h := hsmul 0 0
    rwa [smul_zero, zero_smul] at h
  have hinj : ∀ s t, φ s = φ t → s = t := by
    intro s t h
    have hst : finSecPullId s = finSecPullId t := E.symm.injective (Subtype.ext h)
    have e := finSecPullId_add (s - t) t
    rw [sub_add_cancel, hst] at e
    have h2 : finSecPullId (s - t) = 0 := add_right_cancel (e.symm.trans (zero_add _).symm)
    exact sub_eq_zero.1 (eq_zero_of_finSecPullId Q _ h2)
  let N : Submodule W (Fin Q.a → W) :=
    { carrier := Set.range φ
      add_mem' := by
        rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
        exact ⟨s + t, hadd s t⟩
      zero_mem' := ⟨0, φ0⟩
      smul_mem' := by
        rintro r _ ⟨s, rfl⟩
        exact ⟨cst f ⊤ r • s, hsmul r s⟩ }
  have memN : ∀ s, φ s ∈ N := fun s => ⟨s, rfl⟩
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun W (Fin Q.a)) N
  have hb : ∀ j, ∃ s, φ s = (b j).1 := fun j => (b j).2
  choose t ht using hb
  let φh : LB.Sec M →+ (Fin Q.a → W) := { toFun := φ, map_zero' := φ0, map_add' := hadd }
  have hsum : ∀ c : Fin n → W, φ (∑ j, cst f ⊤ (c j) • t j) = ∑ j, c j • (b j).1 := by
    intro c
    change φh _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => (hsmul (c j) (t j)).trans (by rw [ht])
  refine ⟨n, t, fun u => ⟨fun j => b.repr ⟨φ u, memN u⟩ j, ?_, ?_⟩⟩
  · apply hinj
    rw [hsum]
    have h := congrArg Subtype.val (b.sum_repr ⟨φ u, memN u⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  · intro c hc
    have h : (⟨φ u, memN u⟩ : N) = ∑ j, c j • b j := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [← hsum, ← hc]
    funext j
    rw [h, Module.Basis.repr_sum_self]

end GlobalTheory.AbLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisLineBundleSectionsProjectiveOverDvrStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_lineBundleSections_projective_over_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of W)) (M : LB X), Flat f → GlobalTheory.AbLaw.IsProjBy f → M.IsLB → ∃ (n : ℕ) (t : Fin n → LB.Sec M), ∀ u : LB.Sec M, ∃! c : Fin n → W, u = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (c j) • t j := by
  first | exact @GlobalTheory.AbLaw.exists_basis_sec_of_isDiscreteValuationRing | exact GlobalTheory.AbLaw.exists_basis_sec_of_isDiscreteValuationRing | (intros; apply GlobalTheory.AbLaw.exists_basis_sec_of_isDiscreteValuationRing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsoLineBundleSectionsTransfer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsoLineBundleSectionsTransfer
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.BasisMatch
open GlobalTheory.AbLaw GlobalTheory.Cartier TensorProduct

theorem topEquiv_pull {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] {f : X ⟶ Sp R}
    {f' : X' ⟶ Sp R'} {π : X' ⟶ X} {g : R →+* R'} (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g))
    (M : LB X) (x : SecOnR f M ⊤) :
    SecOnR.topEquiv f' (M.pull π) (SecOnR.pull M w ⊤ ⊤ le_top x) = secPull (SecOnR.topEquiv f M x) π := by
  refine DVR.SecOps.sec_ext fun i => ?_
  refine (congrArg (rs X' _) (SecOn.coord_pullLE π le_top x i)).trans ?_
  change (π.appLE _ _ _ ≫ X'.presheaf.map _).hom _ = (X.presheaf.map _ ≫ π.appLE _ _ _).hom _
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  rfl

theorem secMaps_congr {Y : Scheme.{0}} {L N : LB Y} (hL : L.IsLB) (hN : N.IsLB) (w : LB.Iso L N)
    (hw : w.IsGen) (a : L.Sec) :
    SecMaps w a (SecOn.topEquiv N (SecOn.congr hL hN w hw ⊤ ((SecOn.topEquiv L).symm a))) := by
  intro p
  have e := SecOn.coord_congr hL hN w hw ((SecOn.topEquiv L).symm a) p.1 p.2 (O := N.U p.1 ⊓ L.U p.2)
    (le_inf le_top inf_le_left) (le_inf le_top inf_le_right) le_rfl
  rw [SecOn.topEquiv_symm_apply, GlobalTheory.LB.coord_ofSec, rs_self, rs_rs] at e
  rw [SecOn.topEquiv_f]
  exact (rs_rs _ _ _).trans e

theorem topEquiv_sum {X : Scheme.{0}} {R : Type} [CommRing R] (f : X ⟶ Sp R) (M : LB X) {n : ℕ}
    (c : Fin n → R) (x : Fin n → SecOnR f M ⊤) :
    SecOnR.topEquiv f M (∑ j, c j • x j) = ∑ j, cst f ⊤ (c j) • SecOnR.topEquiv f M (x j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, SecOnR.smul_def, map_smul]

theorem sum_f {X : Scheme.{0}} {H : LB X} {m : ℕ} (s : Fin m → H.Sec) (k : H.ι) :
    (∑ j, s j).f k = ∑ j, (s j).f k :=
  map_sum ({ toFun := fun s : H.Sec => s.f k, map_zero' := rfl, map_add' := fun _ _ => rfl } :
    H.Sec →+ Γ(X, H.U k)) s Finset.univ

theorem veryAmpleBy_of_span {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) [UniversallyClosed f]
    (H : LB X) {m n : ℕ} (s₁ : Fin (m + 1) → H.Sec) (s : Fin (n + 1) → H.Sec) (hs₁ : VeryAmpleBy f H s₁)
    (hsp : ∀ i, ∃ c : Fin (n + 1) → R, s₁ i = ∑ k, cst f ⊤ (c k) • s k) : VeryAmpleBy f H s := by
  have E : ∀ {p : ℕ} (u : Fin (p + 1) → H.Sec), VeryAmpleBy f H u ↔ AmpleSpan.EmbedsBy f u :=
    fun u => (AmpleSpan.embedsBy_spec_iff f u).symm
  refine (E s).2 (((E s₁).1 hs₁).of_inSpan fun i => ?_)
  obtain ⟨c, hc⟩ := hsp i
  refine ⟨fun k => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c k), fun k' => ?_⟩
  rw [hc, sum_f]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [GlobalTheory.LB.smul_f]
  congr 1
  change rs X le_top (cst f ⊤ (c k)) = _
  rw [rs_cst]
  simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.appLE, CommRingCat.hom_comp, Scheme.Hom.appTop]
  rfl

end GlobalTheory.BasisMatch

namespace GlobalTheory.BasisMatch
open GlobalTheory.AbLaw GlobalTheory.Cartier TensorProduct

def basisOfExistsUnique {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ} (v : Fin n → V)
    (h : ∀ x, ∃! c : Fin n → R, x = ∑ j, c j • v j) : Module.Basis (Fin n) R V :=
  Module.Basis.mk (v := v)
    (Fintype.linearIndependent_iff.2 fun g hg i => by
      obtain ⟨c, -, hc⟩ := h 0
      exact congrFun ((hc g hg.symm).trans (hc 0 (by simp)).symm) i)
    (fun x _ => (Submodule.mem_span_range_iff_exists_fun R).2 (by
      obtain ⟨c, hc, -⟩ := h x
      exact ⟨c, hc.symm⟩))

theorem basisOfExistsUnique_apply {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
    (v : Fin n → V) (h : ∀ x, ∃! c : Fin n → R, x = ∑ j, c j • v j) (j : Fin n) :
    basisOfExistsUnique v h j = v j := Module.Basis.mk_apply _ _ _

theorem core {K W K' : Type} [Field K] [CommRing W] [Field K'] [Algebra W K'] [Algebra K K']
    [Module.Flat W K'] {XA XG Y : Scheme.{0}} (fA : XA ⟶ Sp K) (fG : XG ⟶ Sp W) (fY : Y ⟶ Sp K')
    (πA : Y ⟶ XA) (πG : Y ⟶ XG) [CompactSpace XA] [CompactSpace XG] [IsSeparated fA] [IsSeparated fG]
    [UniversallyClosed fA]
    (PA : IsPullback πA fY fA (spMap (algebraMap K K'))) (PG : IsPullback πG fY fG (spMap (algebraMap W K')))
    (H : LB XA) (M : LB XG) (w : LB.Iso (M.pull πG) (H.pull πA)) {m : ℕ} (s₁ : Fin (m + 1) → H.Sec)
    {N : ℕ} (t : Fin (N + 1) → M.Sec) (hH : H.IsLB) (hs₁ : VeryAmpleBy fA H s₁) (hM : M.IsLB)
    (hw : w.IsGen) (ht : ∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, cst fG ⊤ (c j) • t j) :
    ∃ (s : Fin (N + 1) → H.Sec) (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K'),
      VeryAmpleBy fA H s ∧ IsUnit g.det ∧
      (∀ j, SecMaps w (secPull (t j) πG) (∑ k, cst fY ⊤ (g j k) • secPull (s k) πA)) ∧
      ∀ c c' : Fin (N + 1) → K', ∑ k, cst fY ⊤ (c k) • secPull (s k) πA =
        ∑ k, cst fY ⊤ (c' k) • secPull (s k) πA → c = c' := by
  have hLy : (M.pull πG).IsLB := LB.isLB_pull hM _
  have hHy : (H.pull πA).IsLB := LB.isLB_pull hH _
  let bcA := LinearEquiv.ofBijective _ (GlobalTheory.PlaceInt.Ext.baseChangeHom_top_bijective hH PA)
  let bcG := LinearEquiv.ofBijective _ (GlobalTheory.PlaceInt.Ext.baseChangeHom_top_bijective hM PG)
  let ψ := SecOnR.linEquiv fY (R := K') (SecOn.congr hLy hHy w hw ⊤)
  have htt : ∀ x : SecOnR fG M ⊤, ∃! c : Fin (N + 1) → W,
      x = ∑ j, c j • (SecOnR.topEquiv fG M).symm (t j) := by
    intro x
    refine (existsUnique_congr fun c => ?_).1 (ht (SecOnR.topEquiv fG M x))
    refine Iff.trans ?_ (SecOnR.topEquiv fG M).injective.eq_iff
    rw [topEquiv_sum]
    simp only [LinearEquiv.apply_symm_apply]
  let bt := basisOfExistsUnique _ htt
  let tY := ((bt.baseChange K').map bcG).map ψ
  have hfr : Module.finrank K (SecOnR fA H ⊤) = N + 1 := by
    rw [← Module.finrank_baseChange (R := K') (S := K), Module.finrank_eq_card_basis (tY.map bcA.symm),
      Fintype.card_fin]
  haveI : Module.Finite K (SecOnR fA H ⊤) := Module.finite_of_finrank_eq_succ hfr
  let bs := Module.finBasisOfFinrankEq K _ hfr
  let s : Fin (N + 1) → H.Sec := fun k => SecOnR.topEquiv fA H (bs k)
  let bV := (bs.baseChange K').map bcA
  have hbV : ∀ k, SecOnR.topEquiv fY (H.pull πA) (bV k) = secPull (s k) πA := fun k => by
    simp only [bV, bcA, Module.Basis.map_apply, Module.Basis.baseChange_apply, LinearEquiv.ofBijective_apply]
    exact (congrArg (SecOnR.topEquiv fY (H.pull πA)) (one_smul K' (SecOnR.pull H PA.w ⊤ ⊤ le_top (bs k)))).trans
      (topEquiv_pull PA.w H _)
  have htY : ∀ j, SecOnR.topEquiv fY (H.pull πA) (tY j) =
      SecOn.topEquiv (H.pull πA) (SecOn.congr hLy hHy w hw ⊤ ((SecOn.topEquiv (M.pull πG)).symm
        (secPull (t j) πG))) := fun j => by
    have e1 : SecOnR.topEquiv fY (M.pull πG) (bcG (1 ⊗ₜ bt j)) = secPull (t j) πG := by
      simp only [bcG, LinearEquiv.ofBijective_apply]
      refine (congrArg (SecOnR.topEquiv fY (M.pull πG))
        (one_smul K' (SecOnR.pull M PG.w ⊤ ⊤ le_top (bt j)))).trans ?_
      rw [topEquiv_pull]
      show secPull (SecOnR.topEquiv fG M (basisOfExistsUnique _ htt j)) πG = _
      rw [basisOfExistsUnique_apply, LinearEquiv.apply_symm_apply]
    rw [← e1]
    simp only [tY, Module.Basis.map_apply, Module.Basis.baseChange_apply]
    show SecOn.topEquiv _ (SecOn.congr hLy hHy w hw ⊤ (bcG (1 ⊗ₜ bt j))) =
      SecOn.topEquiv _ (SecOn.congr hLy hHy w hw ⊤ ((SecOn.topEquiv _).symm (SecOn.topEquiv _ (bcG (1 ⊗ₜ bt j)))))
    exact congrArg (fun z => SecOn.topEquiv (H.pull πA) (SecOn.congr hLy hHy w hw ⊤ z))
      ((SecOn.topEquiv (M.pull πG)).symm_apply_apply _).symm
  let g : Matrix (Fin (N + 1)) (Fin (N + 1)) K' := fun j k => bV.repr (tY j) k
  have hsum : ∀ c : Fin (N + 1) → K', ∑ k, cst fY ⊤ (c k) • secPull (s k) πA =
      SecOnR.topEquiv fY (H.pull πA) (∑ k, c k • bV k) := fun c => by
    rw [topEquiv_sum]
    simp only [hbV]
  refine ⟨s, g, ?_, ?_, fun j => ?_, fun c c' h => ?_⟩
  · refine veryAmpleBy_of_span fA H s₁ s hs₁ fun i => ⟨bs.repr ((SecOnR.topEquiv fA H).symm (s₁ i)), ?_⟩
    conv_lhs => rw [← (SecOnR.topEquiv fA H).apply_symm_apply (s₁ i),
      ← bs.sum_repr ((SecOnR.topEquiv fA H).symm (s₁ i))]
    rw [topEquiv_sum]
  · have : g = Matrix.transpose (bV.toMatrix tY) := by
      ext j k
      rfl
    rw [this, Matrix.det_transpose]
    letI := bV.invertibleToMatrix tY
    exact Matrix.isUnit_det_of_invertible _
  · rw [hsum, bV.sum_repr (tY j), htY]
    exact secMaps_congr hLy hHy w hw _
  · rw [hsum, hsum] at h
    have h3 : bV.equivFun.symm c = bV.equivFun.symm c' := by
      simpa only [Module.Basis.equivFun_symm_apply] using (SecOnR.topEquiv fY (H.pull πA)).injective h
    exact bV.equivFun.symm.injective h3

end GlobalTheory.BasisMatch


open GlobalTheory.AbLaw GlobalTheory.Cartier in
theorem GlobalTheory.BasisMatch.exists_basis_match : ∀ (K W K' : Type) [Field K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra K K'], ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, ∀ (H : LB A.left) (m : ℕ) (s₁ : Fin (m + 1) → H.Sec) (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) (N : ℕ) (t : Fin (N + 1) → M.Sec), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy A.hom H s₁ → M.IsLB → w.IsGen → (∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, GlobalTheory.AbLaw.cst G.hom ⊤ (c j) • t j) → ∃ (s : Fin (N + 1) → H.Sec) (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K'), GlobalTheory.AbLaw.VeryAmpleBy A.hom H s ∧ IsUnit g.det ∧ (∀ j, GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull (t j) (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (g j k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) ∧ ∀ c c' : Fin (N + 1) → K', ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (c k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) = ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (c' k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) → c = c' := by
  intro K W K' _ _ _ _ _ _ _ _ A _ hA G _ hG e H m s₁ M w N t hH hs₁ hM hw ht
  haveI := hA.proper
  haveI := hG.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  haveI : Module.Flat W K' := IsLocalization.flat K' (nonZeroDivisors W)
  have PG : IsPullback (pullback.fst G.hom (spMap (algebraMap W K'))) (pullback.snd G.hom (spMap (algebraMap W K')))
      G.hom (spMap (algebraMap W K')) := IsPullback.of_hasPullback _ _
  have PA : IsPullback (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))
      (pullback.snd G.hom (spMap (algebraMap W K'))) A.hom (spMap (algebraMap K K')) := by
    refine (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K'))).of_iso
      ((Over.forget _).mapIso e).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Functor.mapIso_symm, Iso.symm_hom, Functor.mapIso_inv, Over.forget_map, Iso.refl_hom,
        Category.comp_id]
      rw [← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left]
      exact (Category.id_comp _).symm
    · have := Over.w e.inv
      simp only [Functor.mapIso_symm, Iso.symm_hom, Functor.mapIso_inv, Over.forget_map, Iso.refl_hom,
        Category.comp_id]
      exact this.symm
    · simp
    · simp
  exact GlobalTheory.BasisMatch.core A.hom G.hom _ _ _ PA PG H M w s₁ t hH hs₁ hM hw ht
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsoLineBundleSectionsTransferStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_iso_line_bundle_sections_transfer : ∀ (K W K' : Type) [Field K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra K K'], ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, ∀ (H : LB A.left) (m : ℕ) (s₁ : Fin (m + 1) → H.Sec) (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) (N : ℕ) (t : Fin (N + 1) → M.Sec), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy A.hom H s₁ → M.IsLB → w.IsGen → (∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, GlobalTheory.AbLaw.cst G.hom ⊤ (c j) • t j) → ∃ (s : Fin (N + 1) → H.Sec) (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K'), GlobalTheory.AbLaw.VeryAmpleBy A.hom H s ∧ IsUnit g.det ∧ (∀ j, GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull (t j) (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (g j k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) ∧ ∀ c c' : Fin (N + 1) → K', ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (c k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) = ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (c' k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) → c = c' := by
  first | exact @GlobalTheory.BasisMatch.exists_basis_match | exact GlobalTheory.BasisMatch.exists_basis_match | (intros; apply GlobalTheory.BasisMatch.exists_basis_match <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeFiniteFinrank
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TateFree

open GlobalTheory.PDiv

variable {M : Type} [CommGroup M] {l : ℕ} [Fact l.Prime] {r : ℕ}

theorem lev_sum {I : Type} (s : Finset I) (f : I → Tate l M) (n : ℕ) :
    (∑ i ∈ s, f i).lev n = ∏ i ∈ s, (f i).lev n := by
  let h : Tate l M →+ Additive M :=
    { toFun := fun t => Additive.ofMul (t.lev n), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have := congrArg Additive.toMul (map_sum h f s)
  rw [toMul_sum] at this
  exact this

theorem zpow_pow_comm' (a : M) (k : ℤ) (m : ℕ) : (a ^ k) ^ m = (a ^ m) ^ k := by
  rw [← zpow_natCast, ← zpow_natCast a m, ← zpow_mul, ← zpow_mul, mul_comm]

theorem exists_pow_eq (hc : ∀ n : ℕ, Nat.card {x : M // x ^ (l ^ n) = 1} = l ^ (r * n)) (n : ℕ)
    (x : M) (hx : x ^ l ^ n = 1) : ∃ y : M, y ^ l ^ (n + 1) = 1 ∧ y ^ l = x := by
  have hp : l.Prime := Fact.out
  let K : ℕ → Subgroup M := fun n => (powMonoidHom (l ^ n) : M →* M).ker
  have hmem : ∀ n (y : M), y ∈ K n ↔ y ^ l ^ n = 1 := fun n y => by
    simp [K, MonoidHom.mem_ker, powMonoidHom_apply]
  have hK : ∀ n, Nat.card (K n) = l ^ (r * n) := fun n =>
    (Nat.card_congr (Equiv.subtypeEquivRight fun y => hmem n y)).trans (hc n)
  have hfin : ∀ n, Finite (K n) := fun n =>
    Nat.finite_of_card_ne_zero (by rw [hK n]; exact pow_ne_zero _ hp.ne_zero)
  let φ : K (n + 1) →* M := (powMonoidHom l).comp (K (n + 1)).subtype
  have hφ : ∀ y : K (n + 1), φ y = (y : M) ^ l := fun y => rfl
  have hrange : φ.range ≤ K n := by
    rintro _ ⟨y, rfl⟩
    rw [hmem, hφ, ← pow_mul, ← pow_succ']
    exact (hmem _ _).1 y.2
  have h1 : ∀ z : M, z ^ l = 1 → z ^ l ^ (n + 1) = 1 := fun z h => by
    rw [pow_succ', pow_mul, h, one_pow]
  have hker : Nat.card φ.ker = l ^ (r * 1) := by
    rw [← hc 1]
    refine Nat.card_congr
      { toFun := fun z => ⟨z.1.1, by rw [pow_one, ← hφ]; exact MonoidHom.mem_ker.1 z.2⟩
        invFun := fun z => ⟨⟨z.1, (hmem _ _).2 (h1 _ (by simpa using z.2))⟩,
          MonoidHom.mem_ker.2 (by rw [hφ]; simpa using z.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcard : Nat.card φ.range = l ^ (r * n) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker, hK] at h
    refine Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos (r * 1)) ?_
    rw [← h, ← pow_add]
    ring_nf
  haveI := hfin n
  have heq : φ.range = K n := Subgroup.eq_of_le_of_card_ge hrange (by rw [hcard, hK])
  obtain ⟨y, hy⟩ : x ∈ φ.range := heq ▸ (hmem n x).2 hx
  exact ⟨y.1, (hmem _ _).1 y.2, hy⟩

theorem exists_tate (hc : ∀ n : ℕ, Nat.card {x : M // x ^ (l ^ n) = 1} = l ^ (r * n)) (x : M)
    (hx : x ^ l = 1) : ∃ t : Tate l M, t.lev 1 = x := by
  choose L hL using exists_pow_eq hc
  let u : ∀ m : ℕ, {y : M // y ^ l ^ (m + 1) = 1} := fun m =>
    Nat.rec (motive := fun m => {y : M // y ^ l ^ (m + 1) = 1}) ⟨x, by simpa using hx⟩
      (fun m y => ⟨L (m + 1) y.1 y.2, (hL _ _ _).1⟩) m
  have hu : ∀ m, (u (m + 1)).1 ^ l = (u m).1 := fun m => (hL _ _ _).2
  let s : ℕ → M := fun k => Nat.casesOn k 1 fun m => (u m).1
  refine ⟨Tate.mk s fun k => ⟨?_, ?_⟩, rfl⟩
  · rcases k with _ | m
    · exact one_pow _
    · exact (u m).2
  · rcases k with _ | m
    · exact hx
    · exact hu m

theorem exists_independent (hr : Nat.card {x : M // x ^ l = 1} = l ^ r) :
    ∃ e : Fin r → M, (∀ i, e i ^ l = 1) ∧
      ∀ k : Fin r → ℤ, ∏ i, e i ^ k i = 1 → ∀ i, (l : ℤ) ∣ k i := by
  have hp : l.Prime := Fact.out
  let K : Subgroup M := (powMonoidHom l : M →* M).ker
  have hmem : ∀ y : M, y ∈ K ↔ y ^ l = 1 := fun y => by
    simp [K, MonoidHom.mem_ker, powMonoidHom_apply]
  have hK : Nat.card K = l ^ r :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun y => hmem y)).trans hr
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hp.ne_zero)
  letI : Module (ZMod l) (Additive K) := AddCommGroup.zmodModule fun z => by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [toMul_nsmul, toMul_zero, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact (hmem _).1 (Additive.toMul z).2
  haveI : Finite (Additive K) := inferInstanceAs (Finite K)
  haveI : Fintype (Additive K) := Fintype.ofFinite _
  haveI hMF : Module.Finite (ZMod l) (Additive K) := Module.Finite.of_finite
  haveI hMFr : Module.Free (ZMod l) (Additive K) := Module.Free.of_divisionRing _ _
  have hfr : Module.finrank (ZMod l) (Additive K) = r := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod l) (V := Additive K)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h1
    exact Nat.pow_right_injective hp.two_le (h1.symm.trans hK)
  let b : Module.Basis (Fin r) (ZMod l) (Additive K) :=
    @Module.finBasisOfFinrankEq (ZMod l) (Additive K) _ _ _ hMFr _ hMF r hfr
  let v : Fin r → Additive K := @DFunLike.coe _ _ _ Module.Basis.instFunLike b
  have hv : LinearIndependent (ZMod l) v := b.linearIndependent
  refine ⟨fun i => ((Additive.toMul (v i) : K) : M), fun i => (hmem _).1 (Additive.toMul (v i)).2,
    fun k hk i => ?_⟩
  have hli := Fintype.linearIndependent_iff.1 hv (fun i => (k i : ZMod l)) ?_ i
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hli
  · simp_rw [Int.cast_smul_eq_zsmul]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [toMul_sum]
    simpa [toMul_zsmul] using hk

theorem free_finite_finrank (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (r : ℕ)
    (hc : ∀ n : ℕ, Nat.card {x : M // x ^ (l ^ n) = 1} = l ^ (r * n)) :
    Module.Free ℤ_[l] (Tate l M) ∧ Module.Finite ℤ_[l] (Tate l M) ∧
      Module.finrank ℤ_[l] (Tate l M) = r := by
  have hp : l.Prime := Fact.out
  obtain ⟨e, he1, hind⟩ := exists_independent (M := M) (l := l) (r := r) (by simpa using hc 1)
  choose t ht using fun i => exists_tate hc (e i) (he1 i)

  have key : ∀ n (k : Fin r → ℤ), ∏ i, (t i).lev n ^ k i = 1 → ∀ i, (l : ℤ) ^ n ∣ k i := by
    intro n
    induction n with
    | zero => intro k _ i; simp
    | succ n ih =>
      intro k hk i
      have hl : ∀ j, (t j).lev (n + 1) ^ l ^ n = e j := fun j => by
        rw [add_comm, Tate.lev_add_pow, ht]
      have h1 : ∏ j, e j ^ k j = 1 := by
        have h2 := congrArg (· ^ (l ^ n)) hk
        simp only [one_pow, ← Finset.prod_pow, zpow_pow_comm', hl] at h2
        exact h2
      choose k' hk' using hind k h1
      have h3 : ∏ j, (t j).lev n ^ k' j = 1 := by
        rw [← hk]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [hk' j, zpow_mul, zpow_natCast, Tate.lev_succ]
      rw [hk' i, pow_succ']
      exact mul_dvd_mul_left _ (ih k' h3 i)
  have key2 : ∀ n (k k' : Fin r → ℕ), ∏ i, (t i).lev n ^ k i = ∏ i, (t i).lev n ^ k' i →
      ∀ i, (l : ℤ) ^ n ∣ (k i : ℤ) - k' i := fun n k k' h =>
    key n (fun i => (k i : ℤ) - k' i) (by
      simp only [zpow_sub, zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib, h,
        mul_inv_cancel])

  have hgen : ∀ n (x : M), x ^ l ^ n = 1 → ∃ c : Fin r → ℕ, ∏ i, (t i).lev n ^ c i = x := by
    intro n
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
    haveI : Finite {x : M // x ^ l ^ n = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hc n]; exact pow_ne_zero _ hp.ne_zero)
    let ψ : (Fin r → ZMod (l ^ n)) → {x : M // x ^ l ^ n = 1} := fun c =>
      ⟨∏ i, (t i).lev n ^ (c i).val, by
        rw [← Finset.prod_pow]
        exact Finset.prod_eq_one fun i _ => by
          rw [← pow_mul, mul_comm, pow_mul, Tate.lev_pow, one_pow]⟩
    have hinj : Function.Injective ψ := fun c c' h => funext fun i => by
      have h1 := key2 n _ _ (congrArg Subtype.val h) i
      rw [← sub_eq_zero, ← ZMod.natCast_zmod_val (c i), ← ZMod.natCast_zmod_val (c' i)]
      have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (((c i).val : ℤ) - (c' i).val) (l ^ n)).2
        (by exact_mod_cast h1)
      push_cast at h2
      exact h2
    have hbij := hinj.bijective_of_nat_card_le (by
      rw [hc n, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul,
        mul_comm])
    intro x hx
    obtain ⟨c, hc'⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨fun i => (c i).val, congrArg Subtype.val hc'⟩

  let Φ := Fintype.linearCombination ℤ_[l] t
  have hΦ : ∀ a n, (Φ a).lev n = ∏ i, (t i).lev n ^ digit n (a i) := fun a n => by
    rw [Fintype.linearCombination_apply, lev_sum]
    rfl
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun a ha => funext fun i =>
      PadicInt.ext_of_toZModPow.1 fun n => ?_
    have h1 := key2 n (fun i => digit n (a i)) (fun _ => 0) (by
      rw [← hΦ, ha]
      simp) i
    rw [← cast_digit, Pi.zero_apply, map_zero]
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (digit n (a i) : ℤ) (l ^ n)).2
      (by simpa using h1)
    exact_mod_cast h2
  have hsurj : Function.Surjective Φ := by
    intro x
    choose c hc' using fun n => hgen n (x.lev n) (x.lev_pow n)
    have hdiv : ∀ i n, (l : ℤ) ^ n ∣ ((c (n + 1) i : ℕ) : ℤ) - c n i := fun i n =>
      key2 n (c (n + 1)) (c n) (by
        rw [hc' n, ← x.lev_succ, ← hc' (n + 1), ← Finset.prod_pow]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← pow_mul, mul_comm, pow_mul, Tate.lev_succ]) i
    have hex : ∀ i, ∃ a : ℤ_[l], ∀ n, PadicInt.toZModPow n a = ((c n i : ℤ) : ZMod (l ^ n)) :=
      fun i => ⟨_, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (c n i : ℤ)) l (hdiv i)⟩
    choose a ha using hex
    refine ⟨a, Tate.ext fun n => ?_⟩
    rw [hΦ, ← hc' n]
    refine Finset.prod_congr rfl fun i _ => pow_digit_eq ((t i).lev_pow n) ?_
    rw [ha, Int.cast_natCast]
  let E : (Fin r → ℤ_[l]) ≃ₗ[ℤ_[l]] Tate l M := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  exact ⟨Module.Free.of_equiv E, Module.Finite.equiv E,
    E.finrank_eq.symm.trans (Module.finrank_fin_fun ℤ_[l])⟩

end GlobalTheory.TateFree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingFiniteIdealsOfMaximalIdealPrincipalNilp
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory

theorem localRing_finite_ideals_of_maximalIdeal_principal_nilpotent :
    ∀ (S : Type) [CommRing S] [IsLocalRing S], (IsLocalRing.maximalIdeal S).IsPrincipal →
    IsNilpotent (IsLocalRing.maximalIdeal S) → (Set.univ : Set (Ideal S)).Finite := by
  intro S _ _ hprin hnil
  classical
  obtain ⟨x, hx⟩ := hprin.principal
  obtain ⟨M, hM⟩ := hnil
  set m := IsLocalRing.maximalIdeal S with hm
  have hM' : m ^ M = ⊥ := hM
  have hpow : ∀ n : ℕ, m ^ n = Ideal.span {x ^ n} := by
    intro n
    rw [hx]
    exact Ideal.span_singleton_pow x n
  apply ((Set.finite_Iic M).image fun n => m ^ n).subset
  intro I _
  by_cases hI : I = ⊥
  · exact ⟨M, Set.mem_Iic.mpr le_rfl, by simp only [hM', hI]⟩
  · have hnot : ¬ I ≤ m ^ M := by
      rw [hM']; exact fun h => hI (le_bot_iff.mp h)
    have hex : ∃ k, ¬ I ≤ m ^ k := ⟨M, hnot⟩
    have hk := Nat.find_spec hex
    have hkM : Nat.find hex ≤ M := Nat.find_min' hex hnot
    have hk0 : Nat.find hex ≠ 0 := by
      intro h; apply hk; rw [h, pow_zero]; rw [Ideal.one_eq_top]; exact le_top
    obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := Nat.exists_eq_succ_of_ne_zero hk0
    have hIn : I ≤ m ^ n := by
      by_contra h
      exact Nat.find_min hex (show n < Nat.find hex by omega) h
    rw [hn] at hk
    obtain ⟨a, haI, ha⟩ := SetLike.not_le_iff_exists.mp hk
    have ha' : a ∈ m ^ n := hIn haI
    rw [hpow, Ideal.mem_span_singleton'] at ha'
    obtain ⟨y, rfl⟩ := ha'
    have hy : IsUnit y := by
      by_contra hy
      apply ha
      have hym : y ∈ m := (IsLocalRing.mem_maximalIdeal y).mpr hy
      rw [hx, Ideal.mem_span_singleton'] at hym
      obtain ⟨z, rfl⟩ := hym
      rw [hpow, Ideal.mem_span_singleton']
      exact ⟨z, by ring⟩
    refine ⟨n, Set.mem_Iic.mpr (by omega), ?_⟩
    show m ^ n = I
    apply le_antisymm _ hIn
    rw [hpow, Ideal.span_le, Set.singleton_subset_iff]
    have := I.mul_mem_left ((hy.unit⁻¹ : Sˣ) : S) haI
    rwa [← _root_.mul_assoc, IsUnit.val_inv_mul, _root_.one_mul] at this

end GlobalTheory
end
end
