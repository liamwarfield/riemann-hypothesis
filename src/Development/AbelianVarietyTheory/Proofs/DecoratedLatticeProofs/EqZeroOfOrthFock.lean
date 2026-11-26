module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthRealHeisenbergTranslatesVacuumOfOrthFock
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthRealHeisenbergTranslatesVacuumOfOrthFock
noncomputable section

namespace GlobalTheory.FockRealOrth

section Coord

open Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.FockDensity
open scoped ENNReal ComplexOrder

theorem inner_coord {κ : Type} [Fintype κ] [DecidableEq κ] {Q s : Matrix κ κ ℂ} (hQ : Qᴴ = Q) (hs : s * s = 1)
    (hp : (Q * s).PosDef) {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {ρ : (κ → ℂ) → B →L[ℂ] B} (h : IsHeis (fun x y => (star y ⬝ᵥ Q *ᵥ x).im) ρ) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : B →L[ℂ] H) (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) {Y : Type}
    (T : Y → B →L[ℂ] B) (hT : ∀ y v f, T y (ρ v f) = ρ v (T y f)) (S F : Submodule ℂ B)
    (hS : ∀ f, f ∈ S ↔ Sm ρ f ∧ ∀ y, T y f = f)
    (hF : ∀ z, ∀ f ∈ S, f ∈ F → dH ρ z f - I • dH ρ (I • s *ᵥ z) f ∈ F) {v : B} (hvS : v ∈ S) (hvF : v ∈ F)
    (hv : ∀ z, dH ρ z v + I • dH ρ (I • s *ᵥ z) v = 0) {y : H} (hy : ∀ x ∈ F, inner ℂ y (Φ x) = 0) (w : κ → ℂ) :
    inner ℂ y (Φ (ρ w v)) = 0 := by
  obtain ⟨E, J, hJ, hE, hom⟩ := GlobalTheory.T.exists_euclideanCoords_hermitian_cartanInvolution κ Q s hQ hs hp
  have hρ : IsHeis (omJ J) fun v => ρ (E v) :=
    UnitaryOsc.isHeis_comp h (E : EuclideanSpace ℂ κ →L[ℝ] (κ → ℂ)) fun x y => hom x y
  have hm : ∀ G, G ∈ S ↔ Sm (fun v => ρ (E v)) G ∧ ∀ y, T y G = G :=
    fun G => (hS G).trans (and_congr_left' (UnitaryOsc.sm_comp_iff E _ G).symm)
  have hd : ∀ z, dH (fun v => ρ (E v)) z = dH ρ (E z) := fun z => funext fun G => by
    have := E.comp_right_fderiv (f := fun v => ρ v G) (x := 0)
    rw [map_zero] at this
    exact DFunLike.congr_fun this z
  have a1 : ∀ G ∈ S, Sm (fun v => ρ (E v)) G := fun G hG => ((hm G).1 hG).1
  have a2 : ∀ v, ∀ G ∈ S, dH (fun v => ρ (E v)) v G ∈ S := fun v G hG =>
    (hm _).2 ⟨VacBd.sm_dH hρ (a1 G hG) v, fun y => by
      rw [← (dH_comm (T y) (fun v => hT y (E v)) (a1 G hG)).2, ((hm G).1 hG).2]⟩
  have := inner_translate hJ hρ (fun v => hΦ (E v)) a1 a2 (F.comap S.subtype)
    (fun z x hx => by
      rw [Submodule.mem_comap, Submodule.subtype_apply, coe_cE, hd, hd, hE]
      exact hF (E z) x x.2 hx) (v := ⟨v, hvS⟩) hvF
    (fun z => (aE_eq_zero a1 a2 z _).2 (by rw [hd, hd, hE]; exact hv (E z))) (y := y)
    (fun x hx => hy x hx) (E.symm w)
  simpa only [E.apply_symm_apply] using this

end Coord

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isUnit_det_of_onb {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) : IsUnit B.det := by
  obtain ⟨ε, h1, h2, -⟩ := h
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_mul, Matrix.det_diagonal] at h3
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, mul_zero] at h3
  obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h3.symm
  rcases h1 a with ⟨e, -⟩ | ⟨e, -⟩ <;> simp [e] at ha

theorem cplxO_pm {m n : ℕ} {s : Matrix (Fin n) (Fin n) ℂ} {t : Matrix (Fin m) (Fin m) ℂ} (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) : ∃ b : Bool, ∀ z, cplxO s t z = ((if b then 1 else -1 : ℂ) * Complex.I) • z := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact ⟨true, fun z => by simp [cplxO]⟩
  · exact ⟨false, fun z => by simp [cplxO]⟩
  · exact ⟨false, fun z => by simp [cplxO]⟩
  · exact ⟨true, fun z => by simp [cplxO]⟩

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem crea_fock (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {x : DefSp S} {y : DefSp T} (hx : x.Is) (hy : y.Is)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    ∃ Q, pureTensorO ψ θ S T x.s y.s x.B y.B f Q =
      crea (heisO ψ S T) θ τ (cplxO (x.s τ) (y.s τ)) z (pureTensorO ψ θ S T x.s y.s x.B y.B f P) := by
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ v g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T
      (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B v g) :=
    fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ v Q,
      pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B) f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B v
        (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B) f Q) := fun v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) hadd hsm hth ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hx.cart hy.cart j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hg : IsThetaFunO ψ S T (pureTensorO ψ θ S T x.s y.s x.B y.B f P) :=
    GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ S T) hadd hsm hth hf P
  obtain ⟨c, rfl⟩ : ∃ c : Fin T.rank → Fin S.rank → ℂ,
      z = ∑ i, ∑ j, c i j • Formalism.IndefR.Datum.unitMap (x.B τ) (y.B τ) i j :=
    ⟨_, GlobalTheory.FockCreaDir.eq_sum_unitMap (isUnit_det_of_onb (hy.onb τ).choose_spec)
      (isUnit_det_of_onb (hx.onb τ).choose_spec) z⟩
  obtain ⟨b, hb⟩ := cplxO_pm (hx.pm τ) (hy.pm τ)
  refine ⟨((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if b then c i j else starRingEnd ℂ (c i j)) •
    (MvPolynomial.X (τ, i, j) * P), Eq.symm ?_⟩
  have h1 : ∀ (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) g,
      crea (heisO ψ S T) θ τ (cplxO (x.s τ) (y.s τ)) u g =
        ((fockScale D τ : ℝ) : ℂ) • Formalism.IndefR.Datum.aPlus (heisO ψ S T) θ τ (cplxO (x.s τ) (y.s τ)) u g := fun u g => by
    rw [Formalism.IndefR.Datum.aPlus, smul_smul, mul_inv_cancel₀ (GlobalTheory.FockCreaDir.fockScale_ne_zero D τ), one_smul]
  rw [h1]
  have h2 : pureTensorO ψ θ S T x.s y.s x.B y.B f (((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j,
      (if b then c i j else starRingEnd ℂ (c i j)) • (MvPolynomial.X (τ, i, j) * P)) =
      ((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if b then c i j else starRingEnd ℂ (c i j)) •
        Formalism.IndefR.Datum.aPlus (heisO ψ S T) θ τ (cplxO (x.s τ) (y.s τ))
          (Formalism.IndefR.Datum.unitMap (x.B τ) (y.B τ) i j) (pureTensorO ψ θ S T x.s y.s x.B y.B f P) := by
    unfold pureTensorO
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, hX]
    rfl
  rw [h2]
  congr 1
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ _ _ hg b _ (hb _)


open GlobalTheory.RealWeil GlobalTheory.FockDensity in
theorem inner_toL2_eq_theta_pairing (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) [BorelSpace (WO S T)] [SecondCountableTopology (WO S T)]
    [IsFiniteMeasure (μ.restrict 𝓕)] (G G' : BB ψ S T) :
    inner ℂ (toL2 _ _ (μ.restrict 𝓕) G') (toL2 _ _ (μ.restrict 𝓕) G) = thPair μ 𝓕 (coeL ψ S T G) (coeL ψ S T G') :=
  BoundedContinuousFunction.inner_toLp (μ.restrict 𝓕) G'.1 G.1


open GlobalTheory.RealWeil GlobalTheory.FockDensity GlobalTheory.Mem.Lift GlobalTheory.ChainFr Classical in
theorem orth_real_translate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → (∀ P, thPair v.μ v.𝓕 f (pureTensorO ψ θ S T x.s y.s x.B y.B vac P) = 0) → ∀ u : WO S T, u.map (finPart D) = 0 → thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
  intro D ψ θ hθ S T x y hx hy vac hvac v f hf ho u hu
  have hψ := hvac.1
  have hv := hvac.2.theta
  have hm := v.covol
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨U, hU, hl⟩ := hv.level
  obtain ⟨-, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hm.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : coeL ψ S T (toB hψ vac hv) = vac := coe_toB hψ vac hv
  have e1 : coeL ψ S T (toB hψ f hf) = f := coe_toB hψ f hf
  have e2 : ∀ G : BB ψ S T, inner ℂ (toL2 _ _ (v.μ.restrict v.𝓕) (toB hψ f hf)) (toL2 _ _ (v.μ.restrict v.𝓕) G) = 0 ↔
      thPair v.μ v.𝓕 f (coeL ψ S T G) = 0 := fun G => by
    rw [inner_eq_zero_symm, inner_toL2_eq_theta_pairing, e1]
  have hF : toB hψ vac hv ∈ (GlobalTheory.Size.thetaLevel ψ S T U).comap (coeL ψ S T) := by
    rw [Submodule.mem_comap, e0]
    exact ⟨hv, hl⟩
  have hc := HM_cartan hx.cart hy.cart
  have key := inner_coord HM_herm hc.1 hc.2 (isHeis_rhoB h hψ) (toL2 _ _ (v.μ.restrict v.𝓕))
    (fun w G => by
      rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]
      exact lintegral_rhoB hψ v.μ v.𝓕 hm.1 hm.2.1 _ G)
    (fun u : {u : WO S T // u ∈ U ∧ u.map (infPart D) = 0} => rhoB hψ u.1) (fun u => rhoB_comm h hψ u.2.2) _
    ((LinearMap.range (pureTensorO ψ θ S T x.s y.s x.B y.B vac)).comap (coeL ψ S T))
    (fun G => (mem_level h hψ hU G).trans
      (and_congr_right' ⟨fun a u => a u.1 u.2.1 u.2.2, fun a u h1 h2 => a ⟨u, h1, h2⟩⟩))
    (fun z G hG hF => by
      have hs := ((mem_level h hψ hU G).1 hG).1
      rw [Submodule.mem_comap, map_sub, map_smul, coe_dH h hψ hs, coe_dH h hψ hs, Finset.smul_sum,
        ← Finset.sum_sub_distrib]
      refine sum_mem fun τ _ => ?_
      obtain ⟨P, hP⟩ := hF
      rw [cpt_cplx, ← hP]
      exact crea_fock hψ hθ hx hy hv τ _ P)
    hF ⟨1, (GlobalTheory.FockIndep.pure_one _).trans e0.symm⟩
    (fun z => fderiv_vac h hψ _ ((mem_level h hψ hU _).1 hF).1 x.s y.s
      (by rw [coe_toB]; exact hvac.2.fock) z)
    (y := toL2 _ _ (v.μ.restrict v.𝓕) (toB hψ f hf))
    (fun G hG => by
      obtain ⟨P, hP⟩ := hG
      rw [e2, ← hP]
      exact ho P) (vecL (GlobalTheory.FockCompare.piW θ T S u))
  rw [e2] at key
  have e3 : iotaV σ S T (vecL (GlobalTheory.FockCompare.piW θ T S u)) = u :=
    h.real_ext (V := T) (W := S) (real_iotaV h _) hu (h.pi_iota T S _)
  have e4 := coe_rhoV (σ := σ) hψ (vecL (GlobalTheory.FockCompare.piW θ T S u)) (toB hψ vac hv)
  rw [e3, coe_toB] at e4
  rw [← e4]
  exact key

end GlobalTheory.FockRealOrth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthRealHeisenbergTranslatesVacuumOfOrthFockStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orth_realHeisenbergTranslates_vacuum_of_orth_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → (∀ P, thPair v.μ v.𝓕 f (pureTensorO ψ θ S T x.s y.s x.B y.B vac P) = 0) → ∀ u : WO S T, u.map (finPart D) = 0 → thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
  first | exact @GlobalTheory.FockRealOrth.orth_real_translate | exact GlobalTheory.FockRealOrth.orth_real_translate | (intros; apply GlobalTheory.FockRealOrth.orth_real_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthAllHeisenbergTranslatesOfOrthRealLatticeVacu
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthAllHeisenbergTranslatesOfOrthRealLatticeVacu
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinOrth

variable {D : D7} {S T : HSp D}

theorem setIntegral_add_right {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure (WO S T))
    [μ.IsAddHaarMeasure] {𝓕 : Set (WO S T)} (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {g : WO S T → E}
    (hg : ∀ γ ∈ ratL T S, ∀ w, g (γ + w) = g w) (u : WO S T) :
    ∫ w in 𝓕, g (w + u) ∂μ = ∫ w in 𝓕, g w ∂μ := by
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  have : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  have : Countable (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
    inferInstanceAs (Countable (Fin T.rank → Fin S.rank → D.host.E))
  have : Countable (ratL T S) := (Set.countable_range _).to_subtype
  have : MeasurableConstVAdd (ratL T S) (WO S T) := ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  have : VAddInvariantMeasure (ratL T S) (WO S T) μ := ⟨fun c s _ => measure_preimage_add μ (c : WO S T) s⟩
  have hmp : MeasurePreserving (fun w : WO S T => u + w) μ μ := measurePreserving_add_left μ u
  have hemb : MeasurableEmbedding (fun w : WO S T => u + w) := (MeasurableEquiv.addLeft u).measurableEmbedding
  have hpre : 𝓕 = (fun w : WO S T => u + w) ⁻¹' ((fun w : WO S T => -u + w) ⁻¹' 𝓕) := by
    ext w; simp
  have h𝓕' : IsAddFundamentalDomain (ratL T S) ((fun w : WO S T => -u + w) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv (measurePreserving_add_left μ (-u)).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ w => ?_
    simp only [id, AddSubgroup.vadd_def, vadd_eq_add]
    abel
  have e1 : ∫ w in 𝓕, g (w + u) ∂μ = ∫ w in (fun w : WO S T => u + w) ⁻¹' ((fun w : WO S T => -u + w) ⁻¹' 𝓕),
      g (u + w) ∂μ := by
    rw [← hpre]; simp_rw [add_comm _ u]
  rw [e1, hmp.setIntegral_preimage_emb hemb]
  exact h𝓕'.setIntegral_eq h𝓕 fun γ w => by rw [AddSubgroup.vadd_def, vadd_eq_add]; exact hg γ γ.2 w

theorem star_mul_self_psi {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (a : AF D.host.F) :
    star (ψ a) * ψ a = 1 := by
  rw [Complex.star_def, Complex.conj_mul', hn]; simp

theorem thPair_heisO {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (μ : Measure (WO S T))
    [μ.IsAddHaarMeasure] {𝓕 : Set (WO S T)} (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (u : WO S T) :
    thPair μ 𝓕 (heisO ψ S T u f) (heisO ψ S T u g) = thPair μ 𝓕 f g := by
  have hs := star_mul_self_psi hn
  unfold thPair
  have e : ∀ w, heisO ψ S T u f w * star (heisO ψ S T u g w) = f (w + u) * star (g (w + u)) := by
    intro w
    simp only [heisO, star_mul']
    linear_combination (f (w + u) * star (g (w + u))) * hs (symplOH S T w u)
  simp_rw [e]
  refine setIntegral_add_right μ h𝓕 (g := fun w => f w * star (g w)) ?_ u
  rintro _ ⟨γ, rfl⟩ w
  change f (ratW T S γ + w) * star (g (ratW T S γ + w)) = f w * star (g w)
  rw [hf.quasi, hg.quasi, star_mul']
  linear_combination (f w * star (g w)) * hs (-(symplOH S T (ratW T S γ) w))

theorem thetaNormSq_heisenbergOp_invariant {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (μ : Measure (WO S T))
    [μ.IsAddHaarMeasure] {𝓕 : Set (WO S T)} (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (u : WO S T) : nrm2 μ 𝓕 (heisO ψ S T u f) = nrm2 μ 𝓕 f := by
  unfold nrm2
  have e : ∀ w, ‖heisO ψ S T u f w‖ ^ 2 = ‖f (w + u)‖ ^ 2 := fun w => by
    simp only [heisO, norm_mul, hn, one_mul]
  simp_rw [e]
  refine setIntegral_add_right μ h𝓕 (g := fun w => ‖f w‖ ^ 2) ?_ u
  rintro _ ⟨γ, rfl⟩ w
  change ‖f (ratW T S γ + w)‖ ^ 2 = ‖f w‖ ^ 2
  rw [hf.quasi, norm_mul, hn, one_mul]

theorem thPair_smul_right (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) (c : ℂ) :
    thPair μ 𝓕 f (c • g) = star c * thPair μ 𝓕 f g := by
  unfold thPair
  rw [← integral_const_mul]
  congr 1; funext w
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem orth_all : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) f → (∀ u : WO S T, u.map (finPart D) = 0 → thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0) → ∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
  intro D ψ θ hθ S T x y hx hy vac hvac v f hf hlat hreal u
  have hψ := hvac.1
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  haveI : v.μ.IsAddHaarMeasure := v.covol.1
  have hF : IsAddFundamentalDomain (ratL T S) v.𝓕 v.μ := v.covol.2.1
  have hvt : IsThetaFunO ψ S T vac := hvac.2.theta
  have hvl := hvac.2.lat

  have key : ∀ g : WO S T, heisO ψ S T g f = f → heisO ψ S T g vac = vac → ψ (symplO S T g u) ≠ 1 →
      thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
    intro g hgf hgv hne
    have hc : heisO ψ S T g (heisO ψ S T u vac) = ψ (symplO S T g u) • heisO ψ S T u vac := by
      rw [GlobalTheory.SplitScalar.heisO_comm, hgv]
    have e := thPair_heisO hn v.μ hF hf (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hvt u) g
    rw [hgf, hc, thPair_smul_right] at e
    have hne' : star (ψ (symplO S T g u)) ≠ 1 := by
      intro h; apply hne; rw [← star_star (ψ _), h, star_one]
    have h2 : (1 - star (ψ (symplO S T g u))) * thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
      linear_combination e.symm
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hne'))
  by_cases hA1 : ∀ g ∈ latO S T x.L y.L (fun _ => True), ψ (symplO S T (2 • g) u) = 1
  swap
  · push_neg at hA1
    obtain ⟨g, hg, hne⟩ := hA1
    exact key (2 • g) (hlat.1 g hg) (hvl.1 g hg) hne
  by_cases hA2 : ∀ e, IsSplitIdem D e → ∀ g ∈ latO S T x.L y.L (fun _ => True), IsHalf e g →
      ψ (symplO S T g u) = 1
  swap
  · push_neg at hA2
    obtain ⟨e, he, g, hg, hh, hne⟩ := hA2
    exact key g (hlat.2 e he g hg hh) (hvl.2 e he g hg hh) hne

  obtain ⟨ur, uf, hr, hfi, rfl⟩ : ∃ ur uf : WO S T, ur.map (finPart D) = 0 ∧ uf.map (infPart D) = 0 ∧
      u = ur + uf := by
    refine ⟨GlobalTheory.FinTranslate.eInf D • u, (1 - GlobalTheory.FinTranslate.eInf D) • u, ?_, ?_, ?_⟩
    · ext i j; exact GlobalTheory.ThetaClosed.finPart_eInf_smul (u i j)
    · ext i j; exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul (u i j)
    · rw [← add_smul, add_sub_cancel, one_smul]
  have hlf : ∀ g ∈ latO S T x.L y.L (fun _ => True), g.map (infPart D) = 0 := fun g hg =>
    GlobalTheory.SplitScalar.latO_fin hg
  have hsf : ∀ g : WO S T, g.map (infPart D) = 0 → symplO S T g (ur + uf) = symplO S T g uf := by
    intro g hg
    rw [GlobalTheory.LatVac.symplO_add_right, GlobalTheory.SplitScalar.symplO_skew S T ur g, GlobalTheory.SplitScalar.symplO_real_fin S T hr hg,
      neg_zero, zero_add]
  have hv' : IsVacO ψ θ S T x.s y.s x.L y.L (heisO ψ S T uf vac) := by
    have hv2 := hvac
    obtain ⟨-, hinf, hth, hl, hfock, hnorm⟩ := hv2
    refine ⟨hψ, hinf, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hth uf, ⟨fun g hg => ?_, fun e he g hg hh => ?_⟩,
      fun τ z => ?_, hnorm.1, fun p hp => ?_⟩
    · rw [GlobalTheory.SplitScalar.heisO_comm, hl.1 g hg, ← hsf _ (hlf _ (AddSubgroup.nsmul_mem _ hg 2)), hA1 g hg, one_smul]
    · rw [GlobalTheory.SplitScalar.heisO_comm, hl.2 e he g hg hh, ← hsf _ (hlf g hg), hA2 e he g hg hh, one_smul]
    · have h0 := hfock τ z
      unfold annih at h0 ⊢
      rw [GlobalTheory.FinTranslate.dRho_heisO hinf hfi, GlobalTheory.FinTranslate.dRho_heisO hinf hfi]
      have h1 := congrArg (GlobalTheory.FinTranslate.heisL S T ψ uf) h0
      rw [map_add (f := _), map_smul, map_zero] at h1
      exact h1
    · show nrm2 p.1 p.2 (heisO ψ S T uf vac) = 1
      haveI := hp.1
      rw [thetaNormSq_heisenbergOp_invariant hn p.1 hp.2.1 hth uf]
      exact hnorm.2 p hp
  obtain ⟨c, -, hc⟩ := GlobalTheory.VacUnique.vacUniqueO D ψ θ hψ hθ S T x.s y.s hx.sig hy.sig hx.cart hy.cart x.L y.L
    hx.sd hy.sd vac _ hvac hv'
  have e : heisO ψ S T (ur + uf) vac = c • heisO ψ S T ur vac := by
    rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (GlobalTheory.SplitScalar.symplO_real_fin S T hr hfi), hc,
      GlobalTheory.SplitScalar.heisO_smul]
  rw [e, thPair_smul_right, hreal ur hr, mul_zero]

end GlobalTheory.FinOrth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthAllHeisenbergTranslatesOfOrthRealLatticeVacuStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orth_allHeisenbergTranslates_of_orth_real_latticeVacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) f → (∀ u : WO S T, u.map (finPart D) = 0 → thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0) → ∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
  first | exact @GlobalTheory.FinOrth.orth_all | exact GlobalTheory.FinOrth.orth_all | (intros; apply GlobalTheory.FinOrth.orth_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunEqZeroOfOrthHeisenbergTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunEqZeroOfOrthHeisenbergTranslates
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaIrred

theorem prod_eq_zero {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} (v : VolM D T.rank S.rank)
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (horth : ∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u g) = 0) (u x : WO S T) :
    f x * star (heisO ψ S T u g x) = 0 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  have hμ : v.μ.IsAddHaarMeasure := v.covol.1
  have h𝓕 : IsAddFundamentalDomain (ratL T S) v.𝓕 v.μ := v.covol.2.1
  obtain ⟨l1, l2, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  obtain ⟨hth, hcomp, -⟩ := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hu := hth u g hg
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S)
    (fun γ x => ψ (symplO S T x γ))
    (fun γ => by
      have : Continuous fun x : WO S T => symplOH S T x (γ : WO S T) :=
        GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const
      simp only [← l4]
      exact hψ.1.1.comp (this.add this))
    (fun γ x y => by
      simp only [← l4, l1, AddChar.map_add_eq_mul]
      ring)
    (fun γ γ' x => by
      simp only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]
      ring)
    (fun x => by
      simp only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun γ x => hψ.1.2.1 _)
    (fun x => by
      rw [← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    v.μ v.𝓕 hμ h𝓕 (fun x => f x * star (heisO ψ S T u g x))
    (hf.cont.mul hu.cont.star)
    (fun γ hγ x => GlobalTheory.ThetaSchur.prod_periodic hψ hf hu hγ x)
    (fun γ => by
      have hneg : ∀ x, symplO S T x ((-γ : ratL T S) : WO S T) = -symplO S T x (γ : WO S T) := by
        intro x
        have h0 := l2 x (γ : WO S T) (-(γ : WO S T))
        rw [add_neg_cancel, GlobalTheory.WeilVacMove.symplOH_zero_right] at h0
        simp only [← l4, AddSubgroup.coe_neg]
        linear_combination (-2 : AF D.host.F) * h0
      have e : (fun x => ψ (symplO S T x γ) * (f x * star (heisO ψ S T u g x))) = fun x =>
          star (ψ (symplOH S T (-(γ : WO S T)) u)) * (f x * star (heisO ψ S T (-(γ : WO S T) + u) g x)) := by
        funext x
        have E := congrFun (hcomp (-(γ : WO S T)) u g) x
        rw [GlobalTheory.ThetaSchur.heisO_rat hu (neg_mem γ.2) x, Pi.smul_apply, smul_eq_mul] at E
        have E' := congrArg star E
        rw [star_mul', star_mul'] at E'
        have hs : star (ψ (-symplO S T x (γ : WO S T))) = ψ (symplO S T x (γ : WO S T)) := by
          have h1 := GlobalTheory.ThetaSchur.mul_star_psi hψ (-symplO S T x (γ : WO S T))
          have h2 : ψ (-symplO S T x (γ : WO S T)) * ψ (symplO S T x (γ : WO S T)) = 1 := by
            rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
          linear_combination ψ (symplO S T x (γ : WO S T)) * h1 - star (ψ (-symplO S T x (γ : WO S T))) * h2
        have hn := hneg x
        simp only [AddSubgroup.coe_neg] at hn
        rw [hn] at E'
        linear_combination (f x) * E' - (f x * star (heisO ψ S T u g x)) * hs
      show ∫ x in v.𝓕, ψ (symplO S T x γ) * (f x * star (heisO ψ S T u g x)) ∂v.μ = 0
      rw [e, integral_const_mul]
      have := horth (-(γ : WO S T) + u)
      unfold thPair at this
      rw [this, mul_zero])
  exact congrFun key x

theorem eq_zero_of_orth_heis : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (v : VolM D T.rank S.rank) (f g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → g ≠ 0 → (∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u g) = 0) → f = 0 := by
  intro D ψ hψ S T v f g hf hg hg0 horth
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hg0
  funext x
  have h := prod_eq_zero hψ v hf hg horth (y - x) x
  have hz : ψ (symplOH S T x (y - x)) ≠ 0 := fun h0 => by
    have := hψ.1.2.1 (symplOH S T x (y - x))
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  simp only [heisO, add_sub_cancel, star_mul'] at h
  rcases mul_eq_zero.1 h with h | h
  · exact h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd (star_eq_zero.1 h) hz
    · exact absurd (star_eq_zero.1 h) hy

end GlobalTheory.ThetaIrred

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunEqZeroOfOrthHeisenbergTranslatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFun_eq_zero_of_orth_heisenbergTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (v : VolM D T.rank S.rank) (f g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → g ≠ 0 → (∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u g) = 0) → f = 0 := by
  first | exact @GlobalTheory.ThetaIrred.eq_zero_of_orth_heis | exact GlobalTheory.ThetaIrred.eq_zero_of_orth_heis | (intros; apply GlobalTheory.ThetaIrred.eq_zero_of_orth_heis <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockTotal

theorem eq_zero_of_orth_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) f → (∀ P, thPair v.μ v.𝓕 f (pureTensorO ψ θ S T x.s y.s x.B y.B vac P) = 0) → f = 0 := by
  intro D ψ θ hθ S T x y hx hy vac hvac v f hf hlat horth
  have hne : vac ≠ 0 := by
    intro h0
    have h1 := hvac.2.norm.2 (v.μ, v.𝓕) v.covol
    simp [h0, nrm2] at h1
  exact GlobalTheory.T.thetaFun_eq_zero_of_orth_heisenbergTranslates D ψ hvac.1 S T v f vac hf hvac.2.theta hne
    (GlobalTheory.T.orth_allHeisenbergTranslates_of_orth_real_latticeVacuum D ψ θ hθ S T x y hx hy vac hvac v f hf hlat
      (GlobalTheory.T.orth_realHeisenbergTranslates_vacuum_of_orth_fock D ψ θ hθ S T x y hx hy vac hvac v f hf horth))

end GlobalTheory.FockTotal
