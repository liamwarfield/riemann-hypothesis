module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGoodRowsFiniteGroupAction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjectiveOfIndep
section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeometricConstantEquiv
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (w : WeightFamilies.Wt D ((i : ℕ) + 1))

abbrev Cusp : Type := T.cuspA ((i : ℕ) + 1) (wtA w) w.n

local instance cuspModule : Module T.Q.c.F (Cusp T i w) :=
  (T.cuspA ((i : ℕ) + 1) (wtA w) w.n).module

abbrev res (σ : D.what₂.LL →+* ℂ) : T.Q.c.F →+* ℂ := σ.comp (algebraMap T.Q.c.F D.what₂.LL)

def iotaW : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ T.iota ((i : ℕ) + 1)

def IsLift (g : G) (κ : GA D (Wc D i)) : Prop :=
  Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ

set_option synthInstance.maxHeartbeats 100000

def IsGeo (ρ : G →* Module.End T.Q.c.F (Cusp T i w)) : Prop :=
  ∃ lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La,
    LevIs R i (iotaW T i) T.Q.l.M (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) lev ∧
    ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (fun g => (lev g, LinearMap.id)) ∧
    ∀ g (f : Cusp T i w), ((ρ g f : Cusp T i w) : T.R ((i : ℕ) + 1)) =
      actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (fun g => (lev g, LinearMap.id)) g (f : T.R ((i : ℕ) + 1))

def ReadTwist (ρ : G →* Module.End T.Q.c.F (Cusp T i w)) : Prop :=
  ∀ σ : D.what₂.LL →+* ℂ, GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i,
    ∀ (g : G) (κ : GA D (T.V ((i : ℕ) + 1) (res T σ))), IsLift T R i g (cast (congrArg (GA D) hV) κ) →
      ∀ (f : Cusp T i w) (x : GA D (T.V ((i : ℕ) + 1) (res T σ))),
        T.phiJ ((i : ℕ) + 1) (res T σ) (wtA w) ((ρ g f : Cusp T i w) : T.R ((i : ℕ) + 1)) x =
          σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) *
            T.phiJ ((i : ℕ) + 1) (res T σ) (wtA w) (f : T.R ((i : ℕ) + 1)) (x * κ)

def IsIntegralForm (f : Cusp T i w) : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM ((i : ℕ) + 1) la),
    T.nrmM ((i : ℕ) + 1) la y (f : T.R ((i : ℕ) + 1)) ≤ 1

def KeepsIntegral (ρ : G →* Module.End T.Q.c.F (Cusp T i w)) : Prop :=
  ∀ g f, IsIntegralForm T i w f → IsIntegralForm T i w (ρ g f)

def ConstEquiv : Prop :=
  ∀ σ : D.what₂.LL →+* ℂ, GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i,
    ∀ ρ : G →* Module.End T.Q.c.F (Cusp T i w), IsGeo T R i w ρ →
    ∀ chi : G →* (T.Q.c.F)ˣ,
      (∀ g, algebraMap T.Q.c.F D.what₂.LL (chi g : T.Q.c.F) = (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)) →
    ∀ ℓ : G → GA D (T.V ((i : ℕ) + 1) (res T σ)), (∀ g, IsLift T R i g (cast (congrArg (GA D) hV) (ℓ g))) →
      CEquiv (T.V ((i : ℕ) + 1) (res T σ)) (res T σ)
        ((rdU (T.U ((i : ℕ) + 1) (res T σ))).comp (T.cuspA ((i : ℕ) + 1) (wtA w) w.n).subtype)
        (T.dict ((i : ℕ) + 1) (res T σ)) (T.mu ((i : ℕ) + 1) (res T σ)) (T.cE ((i : ℕ) + 1) (res T σ)) ρ chi ℓ


omit [Algebra T.Q.c.F D.what₂.LL] in
def IsKappa : Prop :=
  ∀ τ : D.what₂.Tau,
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).1, w.aP τ k = aPl D i ((Wc D i).sig (tauE D τ)).1 τ k) ∧
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).2,
      w.aM τ k = aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ k) ∧ w.n = D.R.nV

def GeoActAt : Prop :=
  ∃ ρ : G →* Module.End T.Q.c.F (Cusp T i w), IsGeo T R i w ρ ∧ ReadTwist T R i w ρ ∧ KeepsIntegral T i w ρ

end GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv
end
end

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.GeoActCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.L2.Pj
  Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv (Cusp IsLift IsGeo ReadTwist KeepsIntegral IsIntegralForm ConstEquiv IsKappa GeoActAt)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Model

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem levChi_flag (i : Fin D.R.m) (k : GA D (Wc D i)) : levChi _ (R.βW i) (flagL (R.datWp i R.triv)) k = 1 := by
  simp [levChi, Formalism.L2.DIV.levFn, flagL, withP, LevCh.datWp, datY, LevelP.full]
  first
    | exact subgroupCharExtension_one_apply _ _
    | (unfold Formalism.L2.DIV.ext1; exact dite_eq_right_iff.2 fun _ => rfl)

private theorem wall_apply_mul_eq_levChi_mul_of_mem_levS {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {T : MMap (R.MW i σ)} (hT : T ∈ R.Wall i σ)
    (v : (R.MW i σ).Vec) {k : GA D (Wc D i)} (hk : k ∈ levS _ (R.βW i) (R.datWp i R.triv)) (g : GA D (Wc D i)) :
    T v (g * k) = levChi _ (R.βW i) (R.datWp i R.triv) k * T v g := by
  unfold RealDat.Wall Formalism.IndefR.Mult.Mult at hT
  induction hT using Submodule.span_induction with
  | mem x hx =>
    have hx' : IsMultMap R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i R.triv))
        (levChi _ (R.βW i) (R.datWp i R.triv)) x := hx
    exact hx'.lev v k hk g
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [MultilinearMap.add_apply, Pi.add_apply, hx, hy]
    ring
  | smul a x _ hx =>
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx]
    ring

theorem hasType_e (he : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec) :
    HasType (Wc D i) (R.βW i) (flag1L (R.datWp i R.triv)) ((R.HW i σ).e y v) := by
  have hm : (R.HW i σ).e y ∈ R.Wall i σ := by
    rw [← (he i σ).2.1]
    exact LinearMap.mem_range_self _ y
  intro k hk h
  exact wall_apply_mul_eq_levChi_mul_of_mem_levS R hm v hk h

theorem actW_apply (he : R.models_HW) {i : Fin D.R.m} (σ : D.what₂.LL →+* ℂ) {g : G} {k : GA D (Wc D i)}
    (hk : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec)
    (x : GA D (Wc D i)) : actW R i σ g ((R.HW i σ).e y) v x = (R.HW i σ).e y v (x * k) := by
  have hs := level_action_spec (hasType_e R he i σ y v) ⟨k, hk⟩ k hk x
  rw [levChi_flag R i k, inv_one, one_mul] at hs
  exact hs

end Model

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

variable {T R κ v₀}

end GlobalTheory.GeoActCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContractionIsometricDiscreteSeriesFock
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContractionIsometricDiscreteSeriesFock
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.CoverContr

theorem inner_map_of_norm {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (A : H →L[ℂ] H)
    (hA : ∀ x, ‖A x‖ = ‖x‖) (x y : H) : inner ℂ (A x) (A y) = inner ℂ x y := by
  let L : H →ₗᵢ[ℂ] H := ⟨A.toLinearMap, hA⟩
  exact L.inner_map_map x y

private theorem inner_unitary_apply_eq_inner_inv {G E : Type} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : G →* E →L[ℂ] E) (hU : ∀ g x, ‖U g x‖ = ‖x‖) (g : G) (v w : E) :
    inner ℂ (U g v) w = inner ℂ v (U g⁻¹ w) := by
  have h1 : U g (U g⁻¹ w) = w := by
    have h := congrArg (fun f : E →L[ℂ] E => f w) (map_mul U g g⁻¹)
    simpa using h.symm
  conv_lhs => rw [← h1]
  exact inner_map_of_norm (U g) (hU g) v (U g⁻¹ w)

theorem exists_isCoverIt : ∀ (p q r s : ℕ) (T₀ : GrpData (p * r + q * s) (p * s + q * r)) (T₁ : GrpData p q) (T₂ : GrpData r s) (F : FockData T₀ T₁ T₂) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (Tm : R₁.U.H →L[ℂ] R₂.U.H →L[ℂ] F.H), (∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y') → (∀ g h x y, F.π (g, h) (Tm x y) = Tm (R₁.U.π g x) (R₂.U.π h y)) → ∃ B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H, IsCoverIt R₁ R₂ B := by
  intro p q r s T₀ T₁ T₂ F R₁ R₂ Tm hTm hEq

  have hnorm : ∀ x y, ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
    intro x y
    have h := hTm x x y y
    simp only [inner_self_eq_norm_sq_to_K] at h
    have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by
      rw [mul_pow]; exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) two_ne_zero).1 h2
  have hflip : ∀ y, ‖Tm.flip y‖ ≤ ‖y‖ := fun y =>
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg y) fun x => by
      rw [ContinuousLinearMap.flip_apply, hnorm, mul_comm]

  have hsrc : ∀ (g : T₁.G) (y : R₂.U.H) (v : F.H),
      R₁.U.π g (ContinuousLinearMap.adjoint (Tm.flip y) v) =
        ContinuousLinearMap.adjoint (Tm.flip y) (F.π (g, 1) v) := by
    intro g y v
    apply ext_inner_right ℂ
    intro x
    rw [inner_unitary_apply_eq_inner_inv R₁.U.π R₁.U.isom, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.flip_apply]
    have e1 : Tm (R₁.U.π g⁻¹ x) y = F.π (g⁻¹, 1) (Tm x y) := by
      rw [hEq]; simp
    have e2 : F.π (g, 1) v = F.Om (F.emb (g, 1)) v := rfl
    have e3 : F.π (g⁻¹, 1) (Tm x y) = F.Om (F.emb (g, 1))⁻¹ (Tm x y) := by
      have : ((g⁻¹, 1) : T₁.G × T₂.G) = (g, 1)⁻¹ := by simp
      show F.Om (F.emb (g⁻¹, 1)) (Tm x y) = _
      rw [this, map_inv]
    rw [e1, e2, e3, inner_unitary_apply_eq_inner_inv F.Om F.isom]

  have htgt : ∀ (h : T₂.G) (y : R₂.U.H) (v : F.H),
      ContinuousLinearMap.adjoint (Tm.flip (R₂.U.π h y)) v =
        ContinuousLinearMap.adjoint (Tm.flip y) (F.π (1, h⁻¹) v) := by
    intro h y v
    apply ext_inner_right ℂ
    intro x
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
    have e1 : Tm x (R₂.U.π h y) = F.π (1, h) (Tm x y) := by
      rw [hEq]; simp
    have e2 : F.π (1, h⁻¹) v = F.Om (F.emb (1, h⁻¹)) v := rfl
    have e3 : F.π (1, h) (Tm x y) = F.Om (F.emb (1, h⁻¹))⁻¹ (Tm x y) := by
      have : ((1, h) : T₁.G × T₂.G) = (1, h⁻¹)⁻¹ := by simp
      show F.Om (F.emb (1, h)) (Tm x y) = _
      rw [this, map_inv]
    rw [e1, e2, e3, inner_unitary_apply_eq_inner_inv F.Om F.isom]
  let B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H :=
    { toFun := fun P =>
        { toFun := fun y => ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P)
          map_add' := fun y y' => by simp
          map_smul' := fun c y => by
            rw [map_smul, LinearIsometryEquiv.map_smulₛₗ, ContinuousLinearMap.smul_apply] }
      map_add' := fun P P' => by ext y; simp
      map_smul' := fun c P => by ext y; simp }
  have hB : ∀ P y, B P y = ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P) := fun _ _ => rfl
  refine ⟨B, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro P
    refine ⟨‖F.ι P‖, fun y => ?_⟩
    rw [hB]
    calc ‖ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P)‖
        ≤ ‖ContinuousLinearMap.adjoint (Tm.flip y)‖ * ‖F.ι P‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖Tm.flip y‖ * ‖F.ι P‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ ‖y‖ * ‖F.ι P‖ := by gcongr; exact hflip y
      _ = ‖F.ι P‖ * ‖y‖ := mul_comm _ _
  · intro P y
    rw [R₁.ι_range, hB]
    unfold KFin
    have hk := (GlobalTheory.FockKFin.kfin_fock p q r s T₀ T₁ T₂ F
      (GlobalTheory.FockDegree.Om_Kset_homog p q r s T₀ T₁ T₂ F) P).1
    unfold KFin at hk
    haveI := hk
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.map
      (ContinuousLinearMap.adjoint (Tm.flip y)).toLinearMap
      (Submodule.span ℂ (Set.range fun k : ↥T₁.Kset => F.π ((k : T₁.G), 1) (F.ι P)))) ?_
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, (hsrc _ y _).symm⟩
  · intro y hy
    by_contra hcon
    push_neg at hcon
    haveI := R₁.nontriv
    obtain ⟨x, hx⟩ := exists_ne (0 : R₁.U.H)
    have hz : (fun v : F.H => inner ℂ v (Tm x y)) = fun _ => 0 := by
      refine Continuous.ext_on F.dense (continuous_id.inner continuous_const) continuous_const ?_
      rintro _ ⟨P, rfl⟩
      have h0 : ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P) = 0 := by rw [← hB]; exact hcon P
      have := ContinuousLinearMap.adjoint_inner_left (Tm.flip y) x (F.ι P)
      rw [h0, inner_zero_left, ContinuousLinearMap.flip_apply] at this
      exact this.symm
    have h1 : Tm x y = 0 := inner_self_eq_zero.1 (congrFun hz (Tm x y))
    have h2 := hnorm x y
    rw [h1, norm_zero] at h2
    exact mul_ne_zero (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy) h2.symm
  · intro Z hZ P y
    have hd := (GlobalTheory.T.fock_derived_actions_tensor_members p q r s T₀ T₁ T₂ F).2.1 Z hZ P
    have hc := ((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    have e : (fun t : ℝ => R₁.U.π (T₁.expt (t • Z)) (B P y)) =
        (ContinuousLinearMap.adjoint (Tm.flip y)) ∘
          (fun t : ℝ => F.π (T₁.expt (t • Z), 1) (F.ι P)) := by
      funext t
      rw [hB, Function.comp_apply, hsrc]
    rw [e, hB]
    exact hc
  · intro Z hZ P y
    have hone : T₂.expt ((0 : ℝ) • Z) = 1 := by
      have h := T₂.expt_add Z hZ 0 0
      rw [add_zero] at h
      have h' := congrArg (· * (T₂.expt ((0 : ℝ) • Z))⁻¹) h
      simpa [mul_assoc] using h'.symm
    have hinv : ∀ t : ℝ, (T₂.expt (t • Z))⁻¹ = T₂.expt ((-t) • Z) := by
      intro t
      have h := T₂.expt_add Z hZ (-t) t
      rw [neg_add_cancel, hone] at h
      exact (eq_inv_of_mul_eq_one_left h.symm).symm
    have hd := (GlobalTheory.T.fock_derived_actions_tensor_members p q r s T₀ T₁ T₂ F).2.2 Z hZ P
    have hd' : HasDerivAt (fun u : ℝ => F.π (1, T₂.expt (u • Z)) (F.ι P))
        (F.ι (fockAct2 p q r s Z P)) (-(0 : ℝ)) := by rw [neg_zero]; exact hd
    have hn := hd'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    have hc := ((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hn
    have e : (fun t : ℝ => B P (R₂.U.π (T₂.expt (t • Z)) y)) =
        (ContinuousLinearMap.adjoint (Tm.flip y)) ∘
          ((fun u : ℝ => F.π (1, T₂.expt (u • Z)) (F.ι P)) ∘ fun t : ℝ => -t) := by
      funext t
      rw [hB, htgt, hinv]
      rfl
    have hval : ((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ)
        ((-1 : ℝ) • F.ι (fockAct2 p q r s Z P)) =
        -(ContinuousLinearMap.adjoint (Tm.flip y)) (F.ι (fockAct2 p q r s Z P)) := by
      rw [neg_one_smul, map_neg]
      rfl
    rw [e, hB, ← hval]
    exact hc

end GlobalTheory.Chain.CoverContr

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContractionIsometricDiscreteSeriesFockStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_contraction_isometric_discreteSeries_fock : ∀ (p q r s : ℕ) (T₀ : GrpData (p * r + q * s) (p * s + q * r)) (T₁ : GrpData p q) (T₂ : GrpData r s) (F : FockData T₀ T₁ T₂) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (Tm : R₁.U.H →L[ℂ] R₂.U.H →L[ℂ] F.H), (∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y') → (∀ g h x y, F.π (g, h) (Tm x y) = Tm (R₁.U.π g x) (R₂.U.π h y)) → ∃ B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H, IsCoverIt R₁ R₂ B := by
  first | exact @GlobalTheory.Chain.CoverContr.exists_isCoverIt | exact GlobalTheory.Chain.CoverContr.exists_isCoverIt | (intros; apply GlobalTheory.Chain.CoverContr.exists_isCoverIt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorMaximalCompactMovedBases
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorMaximalCompactMovedBases
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockSubBoth

open GlobalTheory.FockSubst GlobalTheory.FockCompare GlobalTheory.OrientedHeis Complex

theorem unitMap_mul_both {m n : ℕ} (B k : Matrix (Fin n) (Fin n) ℂ) (B' k' : Matrix (Fin m) (Fin m) ℂ) (a : Fin m)
    (c : Fin n) : unitMap (B * k) (B' * k') a c =
      ∑ b : Fin m × Fin n, (k' b.1 a * k⁻¹ c b.2) • unitMap B B' b.1 b.2 := by
  unfold unitMap
  rw [Matrix.mul_inv_rev]
  have key : k' * single a c (1 : ℂ) * k⁻¹ = ∑ b : Fin m × Fin n, (k' b.1 a * k⁻¹ c b.2) • single b.1 b.2 (1 : ℂ) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, Fintype.sum_prod_type, ite_and, Finset.sum_ite_eq,
      Finset.sum_ite_eq', ite_mul, zero_mul]
  calc B' * k' * single a c (1 : ℂ) * (k⁻¹ * B⁻¹) = B' * (k' * single a c (1 : ℂ) * k⁻¹) * B⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [key, Matrix.mul_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Matrix.mul_smul, Matrix.smul_mul]

theorem onb_sign {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) :
    IsUnit B.det ∧ s * B = B * Matrix.diagonal (fun a : Fin k => if a.val < p then (1 : ℂ) else -1) := by
  obtain ⟨ε, hε, hG, hs⟩ := h
  have hdiag : (diagonal fun a => ((ε a : _) : ℂ)) = diagonal fun a : Fin k => if a.val < p then (1 : ℂ) else -1 := by
    congr 1
    funext a
    rcases hε a with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2]
    · simp [h1, not_lt.mpr h2]
  refine ⟨?_, hs.trans (by rw [hdiag])⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  have hd := congrArg Matrix.det hG
  rw [Matrix.det_mul, h0, mul_zero, hdiag, Matrix.det_diagonal] at hd
  have : ∀ a ∈ (Finset.univ : Finset (Fin k)), (if a.val < p then (1 : ℂ) else -1) ≠ 0 := by
    intro a _
    split_ifs <;> norm_num
  exact (Finset.prod_ne_zero_iff.mpr this) hd.symm

theorem cplxO_unitMap_both {m n : ℕ} {G s B : Matrix (Fin n) (Fin n) ℂ} {p : ℕ} (h : IsONBasis G s B p)
    {G' s' B' : Matrix (Fin m) (Fin m) ℂ} {p' : ℕ} (h' : IsONBasis G' s' B' p') (i : Fin m) (j : Fin n) :
    cplxO s s' (unitMap B B' i j) =
      ((if decide (i.val < p' ↔ j.val < p) then 1 else -1 : ℂ) * I) • unitMap B B' i j := by
  obtain ⟨hB, hs⟩ := onb_sign h
  obtain ⟨-, hs'⟩ := onb_sign h'
  have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  have hBi : B⁻¹ * s = diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1) * B⁻¹ := by
    calc B⁻¹ * s = B⁻¹ * s * (B * B⁻¹) := by rw [hBB, Matrix.mul_one]
      _ = B⁻¹ * (s * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * (B * diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1)) * B⁻¹ := by rw [hs]
      _ = _ := by rw [← Matrix.mul_assoc B⁻¹, hinv, Matrix.one_mul]
  have e1 : s' * (B' * single i j (1 : ℂ) * B⁻¹) * s =
      B' * (diagonal (fun a : Fin m => if a.val < p' then (1 : ℂ) else -1) * single i j (1 : ℂ) *
        diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1)) * B⁻¹ := by
    calc s' * (B' * single i j (1 : ℂ) * B⁻¹) * s = (s' * B') * single i j (1 : ℂ) * (B⁻¹ * s) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hs', hBi]; simp only [Matrix.mul_assoc]
  have e2 : diagonal (fun a : Fin m => if a.val < p' then (1 : ℂ) else -1) * single i j (1 : ℂ) *
      diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1) =
      ((if i.val < p' then (1 : ℂ) else -1) * (if j.val < p then (1 : ℂ) else -1)) • single i j (1 : ℂ) := by
    ext x y
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases hxy : i = x ∧ j = y
    · rw [if_pos hxy]
      obtain ⟨rfl, rfl⟩ := hxy
      ring
    · rw [if_neg hxy]
      ring
  unfold cplxO unitMap
  rw [e1, e2, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  by_cases hi : i.val < p' <;> by_cases hj : j.val < p <;> simp [hi, hj]

theorem isKMat_inv_zero {k p : ℕ} {κ : Matrix (Fin k) (Fin k) ℂ} (h : IsKMat p κ) {i j : Fin k}
    (hij : ¬ (i.val < p ↔ j.val < p)) : κ⁻¹ i j = 0 := by
  obtain ⟨hu, hz⟩ := h
  have hinv : κ⁻¹ = star κ := Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp hu)
  rw [hinv, Matrix.star_apply, hz j i (fun h' => hij h'.symm), star_zero]

theorem pureTensorO_fockSub : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → ∀ (τ : D.what₂.Tau) κS κT, IsKMat (pS τ) κS → IsKMat (pT τ) κT → ∀ (BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), BS' τ = BS τ * κS → BT' τ = BT τ * κT → (∀ ρ, ρ ≠ τ → BS' ρ = BS ρ ∧ BT' ρ = BT ρ) → ∀ P, pureTensorO ψ θ S T sS sT BS' BT' f P = pureTensorO ψ θ S T sS sT BS BT f (fockSub τ (pS τ) (pT τ) κS κT P) := by
  intro D ψ θ S T hψ hθ sS BS sT BT pS pT hpS hpT hcS hcT hoS hoT f hf τ κS κT hkS hkT BS' BT' hS hT hne P
  classical
  obtain ⟨-, hkTz⟩ := hkT
  have hτ : ∀ (i : Fin T.rank) (j : Fin S.rank) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (unitMap (BS' τ) (BT' τ) i j) g =
      ∑ b : Fin T.rank × Fin S.rank, (if (i.val < pT τ ↔ j.val < pS τ) then κT b.1 i * κS⁻¹ j b.2
          else starRingEnd ℂ (κT b.1 i * κS⁻¹ j b.2)) •
        aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (unitMap (BS τ) (BT τ) b.1 b.2) g := by
    intro i j g hg
    rw [hS, hT, unitMap_mul_both, GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ (sS τ) (sT τ) hg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ (sS τ) (sT τ) hg (decide (b.1.val < pT τ ↔ b.2.val < pS τ)) _
      (cplxO_unitMap_both (hoS τ) (hoT τ) b.1 b.2)]
    congr 1
    by_cases hw : κT b.1 i * κS⁻¹ j b.2 = 0
    · rw [hw]
      simp
    · have h1 : (b.1.val < pT τ ↔ i.val < pT τ) := by
        by_contra hc
        exact hw (by rw [hkTz b.1 i hc, zero_mul])
      have h2 : (j.val < pS τ ↔ b.2.val < pS τ) := by
        by_contra hc
        exact hw (by rw [isKMat_inv_zero hkS hc, mul_zero])
      by_cases hc : (i.val < pT τ ↔ j.val < pS τ)
      · have hd : decide (b.1.val < pT τ ↔ b.2.val < pS τ) = true := by
          rw [decide_eq_true_iff, h1, ← h2]
          exact hc
        rw [if_pos hd, if_pos hc]
      · have hd : ¬ decide (b.1.val < pT τ ↔ b.2.val < pS τ) = true := by
          rw [decide_eq_true_iff, h1, ← h2]
          exact hc
        rw [if_neg hd, if_neg hc]
  have key := GlobalTheory.FockSubst.pure_subst (ι := FVar D T.rank S.rank) (X := WO S T) (κ := Fin T.rank × Fin S.rank)
    (A := fun k => aPlus (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2))
    (A' := fun k => aPlus (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS' k.1) (BT' k.1) k.2.1 k.2.2))
    (P := IsThetaFunO ψ S T)
    (fun g g' hg hg' => GlobalTheory.OrientedHeis.theta_add hg hg')
    (fun a g hg => GlobalTheory.OrientedHeis.theta_smul a hg)
    (fun k g hg => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ hg)
    (fun k l g hg => GlobalTheory.FockSubst.aPlus_comm hψ hθ _ _ hcS hcT _ _ hg)
    (fun k g g' hg hg' => GlobalTheory.FockSubst.aPlus_add hψ hθ _ _ _ hg hg')
    (fun k a g hg => GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a hg)
    (fun k g hg => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ hg)
    (fun k l g hg => GlobalTheory.FockSubst.aPlus_comm hψ hθ _ _ hcS hcT _ _ hg)
    (fun k g g' hg hg' => GlobalTheory.FockSubst.aPlus_add hψ hθ _ _ _ hg hg')
    (fun k a g hg => GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a hg)
    (fun v b => if v.1 = τ then
        (if (v.2.1.val < pT τ ↔ v.2.2.val < pS τ) then κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2
          else starRingEnd ℂ (κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2))
        else (if b = (v.2.1, v.2.2) then 1 else 0))
    (fun v b => (v.1, b.1, b.2))
    (by
      rintro ⟨ρ, i, j⟩ g hg
      dsimp only
      by_cases hρ : ρ = τ
      · subst hρ
        simp only [if_true]
        exact hτ i j g hg
      · obtain ⟨h1, h2⟩ := hne ρ hρ
        simp [hρ, h1, h2, ite_smul])
    hf P
  have hsub : (MvPolynomial.aeval fun v : FVar D T.rank S.rank => ∑ b : Fin T.rank × Fin S.rank,
      (if v.1 = τ then
        (if (v.2.1.val < pT τ ↔ v.2.2.val < pS τ) then κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2
          else starRingEnd ℂ (κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2))
        else (if b = (v.2.1, v.2.2) then 1 else 0)) •
        (MvPolynomial.X (v.1, b.1, b.2) : MvPolynomial (FVar D T.rank S.rank) ℂ)) P =
      fockSub τ (pS τ) (pT τ) κS κT P := by
    unfold fockSub
    congr 2
    funext y
    obtain ⟨ρ, i, j⟩ := y
    by_cases hρ : ρ = τ
    · subst hρ
      simp only [if_true, Fintype.sum_prod_type, MvPolynomial.smul_eq_C_mul]
    · simp [hρ, ite_smul]
  unfold pureTensorO aPlusAll
  beta_reduce
  rw [key, hsub]

end GlobalTheory.FockSubBoth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorMaximalCompactMovedBasesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVector_maximalCompact_moved_bases : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → ∀ (τ : D.what₂.Tau) κS κT, IsKMat (pS τ) κS → IsKMat (pT τ) κT → ∀ (BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), BS' τ = BS τ * κS → BT' τ = BT τ * κT → (∀ ρ, ρ ≠ τ → BS' ρ = BS ρ ∧ BT' ρ = BT ρ) → ∀ P, pureTensorO ψ θ S T sS sT BS' BT' f P = pureTensorO ψ θ S T sS sT BS BT f (fockSub τ (pS τ) (pT τ) κS κT P) := by
  first | exact @GlobalTheory.FockSubBoth.pureTensorO_fockSub | exact GlobalTheory.FockSubBoth.pureTensorO_fockSub | (intros; apply GlobalTheory.FockSubBoth.pureTensorO_fockSub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphWittFlagCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphWittFlagCoordinates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MixPer

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

def flagCoordMap (d : HypDec S S₀ ρ) (p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ)) : flagN d :=
  ⟨d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2),
    mul_mem (d.levi_mem_NFlag p.1.2) (mul_mem (d.nB_mem_NFlag p.2.1) (d.nC_mem_NFlag p.2.2))⟩

theorem flagCoordMap_bijective (d : HypDec S S₀ ρ) : Function.Bijective (flagCoordMap d) := by
  refine ⟨fun p q h => ?_, fun n => ?_⟩
  · rcases p with ⟨⟨u, hu⟩, b, c⟩
    rcases q with ⟨⟨v, hv⟩, b', c'⟩
    have e : d.levi u * (d.nB b * d.nC c) = d.levi v * (d.nB b' * d.nC c') :=
      congrArg Subtype.val h
    have eX := congrArg (fun g => d.pX * (mt S g * d.jX)) e
    simp only [mt_mul, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX] at eX
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul, Matrix.one_mul] at eX
    have huv : u = v := Units.ext eX
    subst v
    have e' := mul_left_cancel e
    have e0 := congrArg (fun g => d.pX * (mt S g * d.j0)) e'
    simp only [mt_mul, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.pX_j0,
      cancel₂ d.pX_jX, Matrix.one_mul, zero_add] at e0
    subst b'
    have eY := congrArg (fun g => d.pX * (mt S g * d.jY)) (mul_left_cancel e')
    simp only [d.nC_jY, Matrix.mul_add, d.pX_jY, cancel₂ d.pX_jX, Matrix.one_mul, zero_add] at eY
    exact Prod.ext rfl (Prod.ext rfl (Subtype.ext eY))
  · obtain ⟨T, B, hT, hX, h0⟩ := exists_blocks d n.2
    obtain ⟨u, hu, huT⟩ := Decomp.exists_unit hT
    let b := (u⁻¹).1 * B
    let g := d.levi u * d.nB b
    have hgX : mt S g * d.jX = mt S n.1 * d.jX := by
      dsimp only [g]
      rw [mt_mul, Matrix.mul_assoc, d.nB_jX, d.levi_jX, hX, huT, Matrix.mul_add, Matrix.mul_one]
    have hg0 : mt S g * d.j0 = mt S n.1 * d.j0 := by
      dsimp only [g, b]
      rw [mt_mul, Matrix.mul_assoc, d.nB_j0, h0, Matrix.mul_add,
        d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc (mt S (d.levi u)), d.levi_jX,
        Matrix.mul_assoc d.jX, ← Matrix.mul_assoc u.1, Units.mul_inv, Matrix.one_mul]
    let k := g⁻¹ * n.1
    have hkX : mt S k * d.jX = d.jX := by
      dsimp only [k]
      rw [mt_mul, Matrix.mul_assoc, ← hgX, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    have hk0 : mt S k * d.j0 = d.j0 := by
      dsimp only [k]
      rw [mt_mul, Matrix.mul_assoc, ← hg0, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    have gram {m l : ℕ} (X : Mx D S.rank m) (Y : Mx D S.rank l) :
        adj (mt S k * X) * (gA S * (mt S k * Y)) = adj X * (gA S * Y) := by
      rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) _ Y,
        ← Matrix.mul_assoc (adj (mt S k)), GlobalTheory.MixModel.mt_unitary]
    have pY : d.pY * (mt S k * d.jY) = 1 := by
      rw [d.pY_eq, Matrix.mul_assoc, ← hkX, gram, d.gram_XY]
    have p0 : d.p0 * (mt S k * d.jY) = 0 := by
      rw [d.p0_eq, Matrix.mul_assoc, Matrix.mul_assoc, ← hk0, gram, d.gram_0Y, Matrix.mul_zero]
    let C := d.pX * (mt S k * d.jY)
    have hkY : mt S k * d.jY = d.jY + d.jX * C := by
      conv_lhs => rw [← Matrix.one_mul (mt S k * d.jY), ← d.sum_eq_one]
      rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
        pY, p0, Matrix.mul_zero, add_zero, Matrix.mul_one, add_comm]
    have hC := gram d.jY d.jY
    rw [hkY, d.gram_YY] at hC
    simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, d.gram_YY,
      d.gram_XY, cancel₃ d.gram_XX, cancel₃ d.gram_YX, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.one_mul, Matrix.mul_one, add_zero, zero_add] at hC
    let c : skewA D ρ := ⟨C, eq_neg_of_add_eq_zero_left hC⟩
    have hk : k = d.nC c := d.ga_ext (hkX.trans (d.nC_jX c).symm)
      (hk0.trans (d.nC_j0 c).symm) (hkY.trans (d.nC_jY c).symm)
    refine ⟨(⟨u, hu⟩, b, c), Subtype.ext ?_⟩
    change d.levi u * (d.nB b * d.nC c) = n.1
    rw [← mul_assoc, ← hk]
    exact mul_inv_cancel_left g n.1

theorem pX_mt_flagCoord (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) =
      u.1 * (d.pX + c.1 * d.pY + b * d.p0 - (half D • (b * plus S₀ b)) * d.pY) := by
  rw [mt_mul, mt_mul, ← Matrix.mul_assoc, d.pX_levi, Matrix.mul_assoc, ← Matrix.mul_assoc d.pX, d.pX_nB]
  congr 1
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_nC, d.wittDecomp_projAnisotropic_unipotentSkew, d.pY_nC]

theorem flagCoord_jX (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.jX) = u.1 := by
  rw [← Matrix.mul_assoc, pX_mt_flagCoord]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_jX, d.pY_jX, d.p0_jX, Matrix.mul_zero,
    Matrix.mul_one, add_zero, sub_zero]

theorem flagCoordinate_at_base (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.j0) = u.1 * b := by
  rw [← Matrix.mul_assoc, pX_mt_flagCoord]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.mul_zero,
    Matrix.mul_one, add_zero, sub_zero, zero_add]

theorem flagCoord_jY (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.jY) =
      u.1 * (c.1 - half D • (b * plus S₀ b)) := by
  rw [← Matrix.mul_assoc, pX_mt_flagCoord]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_jY, d.pY_jY, d.p0_jY, Matrix.mul_zero,
    Matrix.mul_one, add_zero, zero_add, Matrix.mul_sub]

theorem flagCoord_inv_jX (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c))⁻¹ * d.jX) = (u⁻¹).1 := by
  set g := d.levi u * (d.nB b * d.nC c)
  have h1 : Formalism.L2.Theta.mt S g * d.jX = d.jX * u.1 := by
    simp only [g, mt_mul, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX]
  have h2 : Formalism.L2.Theta.mt S g⁻¹ * d.jX = d.jX * (u⁻¹).1 := by
    calc Formalism.L2.Theta.mt S g⁻¹ * d.jX = Formalism.L2.Theta.mt S g⁻¹ * (d.jX * u.1 * (u⁻¹).1) := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = d.jX * (u⁻¹).1 := by
          rw [← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  rw [h2, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]

end GlobalTheory.MixPer

namespace GlobalTheory.MixPer

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem flagCoord_b (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    (u⁻¹).1 * (d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.j0)) = b := by
  rw [flagCoordinate_at_base, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem flagCoord_c (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    (u⁻¹).1 * (d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.jY)) + half D • (b * plus S₀ b) = c.1 := by
  rw [flagCoord_jY, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, sub_add_cancel]

end GlobalTheory.MixPer

namespace GlobalTheory.MixPer

theorem flagCoord_homeo : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ),
    ∃ e : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) ≃ₜ flagN d,
      ∀ p, (e p : GA D S) = d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2) := by
  intro D S S₀ ρ d
  have := (lattice_Mx D ρ ρ).1
  let e0 := Equiv.ofBijective _ (flagCoordMap_bijective d)
  have key : ∀ n : flagN d, (n : GA D S) =
      d.levi (e0.symm n).1.1 * (d.nB (e0.symm n).2.1 * d.nC (e0.symm n).2.2) := fun n =>
    congrArg Subtype.val (e0.apply_symm_apply n).symm
  have hM : Continuous fun n : flagN d => Formalism.L2.Theta.mt S (n : GA D S) :=
    (continuous_mt S).comp continuous_subtype_val
  have hMi : Continuous fun n : flagN d => Formalism.L2.Theta.mt S (n : GA D S)⁻¹ :=
    (continuous_mt S).comp continuous_subtype_val.inv
  have hU : ∀ n : flagN d, ((e0.symm n).1.1).val = d.pX * (Formalism.L2.Theta.mt S (n : GA D S) * d.jX) := by
    intro n; rw [key n, flagCoord_jX]
  have hUi : ∀ n : flagN d, (((e0.symm n).1.1)⁻¹).val =
      d.pX * (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ * d.jX) := by
    intro n; rw [key n, flagCoord_inv_jX]
  have hB : ∀ n : flagN d, (e0.symm n).2.1 =
      d.pX * (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ * d.jX) * (d.pX * (Formalism.L2.Theta.mt S (n : GA D S) * d.j0)) := by
    intro n; rw [← hUi n]; conv_rhs => rw [key n]
    exact (flagCoord_b d _ _ _).symm
  have hC : ∀ n : flagN d, ((e0.symm n).2.2).val =
      d.pX * (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ * d.jX) * (d.pX * (Formalism.L2.Theta.mt S (n : GA D S) * d.jY)) +
        half D • ((e0.symm n).2.1 * plus S₀ (e0.symm n).2.1) := by
    intro n; rw [← hUi n]; conv_rhs => rw [key n]
    exact (flagCoord_c d _ _ _).symm
  have cU : Continuous fun n : flagN d => ((e0.symm n).1.1).val := by
    simp only [hU]; exact continuous_const.matrix_mul (hM.matrix_mul continuous_const)
  have cUi : Continuous fun n : flagN d => (((e0.symm n).1.1)⁻¹).val := by
    simp only [hUi]; exact continuous_const.matrix_mul (hMi.matrix_mul continuous_const)
  have cB : Continuous fun n : flagN d => (e0.symm n).2.1 := by
    simp only [hB]
    exact (continuous_const.matrix_mul (hMi.matrix_mul continuous_const)).matrix_mul
      (continuous_const.matrix_mul (hM.matrix_mul continuous_const))
  have cC : Continuous fun n : flagN d => ((e0.symm n).2.2).val := by
    have hp : Continuous fun n : flagN d => (e0.symm n).2.1 * plus S₀ (e0.symm n).2.1 :=
      cB.matrix_mul (continuous_const.matrix_mul (continuous_adj.comp cB))
    simp only [hC]
    exact ((continuous_const.matrix_mul (hMi.matrix_mul continuous_const)).matrix_mul
      (continuous_const.matrix_mul (hM.matrix_mul continuous_const))).add (hp.const_smul (half D))
  refine ⟨{ toEquiv := e0, continuous_toFun := ?_, continuous_invFun := ?_ }, fun p => rfl⟩
  · show Continuous (flagCoordMap d)
    exact Continuous.subtype_mk ((d.continuous_levi.comp (continuous_subtype_val.comp continuous_fst)).mul
      ((d.continuous_nB.comp (continuous_fst.comp continuous_snd)).mul
        (d.continuous_nC.comp (continuous_snd.comp continuous_snd)))) _
  · refine Continuous.prodMk ?_ (Continuous.prodMk cB ?_)
    · exact continuous_induced_rng.2 (Units.continuous_iff.2 ⟨cU, cUi⟩)
    · exact continuous_induced_rng.2 cC

end GlobalTheory.MixPer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphWittFlagCoordinatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homeomorph_wittFlagCoordinates : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ e : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) ≃ₜ flagN d, ∀ p, (e p : GA D S) = d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2) := by
  first | exact @GlobalTheory.MixPer.flagCoord_homeo | exact GlobalTheory.MixPer.flagCoord_homeo | (intros; apply GlobalTheory.MixPer.flagCoord_homeo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedModelSelfDualLatticeInvariantLinearFo
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedModelSelfDualLatticeInvariantLinearFo
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {ψ : AddChar L ℂ} {n n' : ℕ}

theorem mem_mixLat_iff {x : Matrix (Fin n') (Fin n) L} : x ∈ mixLat L n' n ↔ ∀ r c,
    (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n / 2 → x r c = 0) ∧ (n' / 2 ≤ r.1 → c.1 < n - n / 2 → x r c ∈ intL L) :=
  Iff.rfl

theorem pairing_mixLat (hσ : ∀ x, σ (σ x) = x) (hv : ∀ x, Valued.v (σ x) = Valued.v x) (hδ : Valued.v δ = 1)
    (hψ0 : ∀ a ∈ intL L, σ a = a → ψ a = 1) {a b : Matrix (Fin n') (Fin n) L} (ha : a ∈ mixLat L n' n)
    (hb : b ∈ mixLat L n' n) : pairing σ δ ψ a b = 1 := by
  have hs : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => mem_intL.2 ((hv x).trans_le hx)
  rw [mem_mixLat_iff] at ha hb
  have hS : ∑ i, ∑ j, a i j * σ (b i.rev j.rev) ∈ intL L := by
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    have hai := ha i j
    have hbi := hb i.rev j.rev
    simp only [Fin.val_rev] at hbi
    have := i.isLt
    have := j.isLt
    by_cases h1 : n' - n' / 2 ≤ i.1 ∨ n' / 2 ≤ i.1 ∧ j.1 < n / 2
    · rw [hai.1 h1, zero_mul]; exact zero_mem _
    by_cases h2 : n' - n' / 2 ≤ n' - (i.1 + 1) ∨ n' / 2 ≤ n' - (i.1 + 1) ∧ n - (j.1 + 1) < n / 2
    · rw [hbi.1 h2, map_zero, mul_zero]; exact zero_mem _
    exact mul_mem (hai.2 (by omega) (by omega)) (hs _ (hbi.2 (by omega) (by omega)))
  have hi : δ * ∑ i, ∑ j, a i j * σ (b i.rev j.rev) ∈ intL L := mul_mem (mem_intL.2 hδ.le) hS
  exact hψ0 _ (add_mem hi (hs _ hi)) (by rw [map_add (f := _), hσ, add_comm])

theorem exists_bad_entry (x : Matrix (Fin n') (Fin n) L)
    (hx : ¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) :
    ∃ r c, x r c ∉ intL L ∧ (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2) := by
  by_contra hc
  refine hx ⟨fun r c => if n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2 then 0 else x r c, fun r c =>
    ⟨fun e => by dsimp only; rw [if_pos (by omega)], fun e e' => by dsimp only; rw [if_pos (by omega)]; exact zero_mem _⟩,
    fun r c => ?_⟩
  show x r c - (if n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2 then 0 else x r c) ∈ intL L
  split_ifs with hb
  · rw [sub_zero]
    by_contra hi
    exact hc ⟨r, c, hi, hb⟩
  · rw [sub_self]; exact zero_mem _

variable {M : Type} [AddCommGroup M] [Module ℂ M]
variable {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M} {ω : GU σ n × GU σ n' →* Module.End ℂ M} {s : M}

theorem IsStd.form_eq_zero (h : IsStd ϖ σ q δ ψ ρ ω s) (ℓ' : M →ₗ[ℂ] ℂ)
    (hℓ' : ∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) (x : Matrix (Fin n') (Fin n) L) (r : Fin n') (c : Fin n)
    (hx : x r c ∉ intL L) (hrc : n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2) : ℓ' (ρ x s) = 0 := by
  obtain ⟨u, hu, hne⟩ := exists_pairing_single_ne h.1.unr h.v_two h.1.delta.1 h.1.psi_ne x hx
  have := r.isLt
  have := c.isLt
  have hyA : Matrix.single r.rev c.rev u ∈ mixLat L n' n := by
    intro r' c'
    rw [Matrix.single_apply]
    split_ifs with he
    · obtain ⟨rfl, rfl⟩ := he
      simp only [Fin.val_rev]
      exact ⟨fun e => by omega, fun _ _ => hu⟩
    · exact ⟨fun _ => rfl, fun _ _ => zero_mem _⟩
  have hyL : Matrix.single r.rev c.rev u ∈ intMat L (Fin n') (Fin n) := by
    intro i j
    rw [Matrix.single_apply]
    split_ifs
    exacts [hu, zero_mem _]
  have e1 := h.isHeis.comm x (Matrix.single r.rev c.rev u) s
  rw [h.fixes _ hyL] at e1
  have e2 := congrArg ℓ' e1
  rw [map_smul, hℓ' _ hyA, smul_eq_mul] at e2
  have e3 : (pairing σ δ ψ x (Matrix.single r.rev c.rev u) - 1) * ℓ' (ρ x s) = 0 := by linear_combination -e2
  rcases mul_eq_zero.1 e3 with h' | h'
  · exact absurd (sub_eq_zero.1 h') hne
  · exact h'

end

theorem exists_mixLat_form : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∃ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 ∧ (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) ∧ (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) ∧ (∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ v, ℓ' v = ℓ' s * ℓ v) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L), ℓ (ρ (embLow n' n z) s) = if z ∈ intMat L (Fin (n' / 2)) (Fin (n / 2)) then 1 else 0 := by
  intro L _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s h
  obtain ⟨ℓ, h1, h2⟩ := GlobalTheory.T.exists_heisenbergInvariant_linearForm_isotropic_vacuum h.isHeis (intMat L (Fin n') (Fin n)) h.selfDual s h.2.1 h.fixes h.2.2.2
    (mixLat L n' n) fun a ha b hb => pairing_mixLat h.1.unr.1 h.1.unr.2.1 h.1.delta.1 h.1.psi_int ha hb
  have hz : ∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ x,
      (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ' (ρ x s) = 0 := fun ℓ' hℓ' x hx => by
    obtain ⟨r, c, hr, hrc⟩ := exists_bad_entry x hx
    exact h.form_eq_zero ℓ' hℓ' x r c hr hrc
  refine ⟨ℓ, h1, h2, hz ℓ h2, fun ℓ' hℓ' => ?_, fun z => ?_⟩
  · have key : ℓ' = ℓ' s • ℓ := LinearMap.ext_on_range h.2.2.2 fun x => ?_
    · exact fun v => LinearMap.congr_fun key v
    show ℓ' (ρ x s) = (ℓ' s • ℓ) (ρ x s)
    by_cases hx : ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)
    · obtain ⟨a, ha, hxa⟩ := hx
      have e := h.isHeis.comp a (x - a) s
      rw [h.fixes _ hxa, show a + (x - a) = x by abel] at e
      have hg := h.isHeis.ne_zero (half h.v_two • a) (x - a)
      have hx' : ρ x s = (pairing σ δ ψ (half h.v_two • a) (x - a))⁻¹ • ρ a s := by
        rw [e, smul_smul, inv_mul_cancel₀ hg, one_smul]
      rw [LinearMap.smul_apply, hx', map_smul, map_smul, hℓ' a ha, h2 a ha, h1, smul_eq_mul, smul_eq_mul, smul_eq_mul,
        mul_one, mul_comm]
    · rw [LinearMap.smul_apply, hz ℓ' hℓ' x hx, hz ℓ h2 x hx, smul_zero]
  · have := (n' / 2).le_refl
    split_ifs with hzi
    · have hm : embLow n' n z ∈ intMat L (Fin n') (Fin n) := fun r c => by
        unfold embLow
        split_ifs
        exacts [hzi _ _, zero_mem _]
      rw [h.fixes _ hm, h1]
    · obtain ⟨i, j, hij⟩ : ∃ i j, z i j ∉ intL L := by
        by_contra hc
        push_neg at hc
        exact hzi hc
      have he : embLow n' n z (hi n' i) (hi n j) = z i j := by
        simp [embLow, hi]
      refine h.form_eq_zero ℓ h2 _ (hi n' i) (hi n j) (by rwa [he]) (Or.inl ?_)
      simp only [hi]
      omega

end GlobalTheory.SphTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedModelSelfDualLatticeInvariantLinearFoStatement
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mixedModelSelfDualLattice_invariant_linearForm : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∃ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 ∧ (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) ∧ (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) ∧ (∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ v, ℓ' v = ℓ' s * ℓ v) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L), ℓ (ρ (embLow n' n z) s) = if z ∈ intMat L (Fin (n' / 2)) (Fin (n / 2)) then 1 else 0 := by
  first | exact @GlobalTheory.SphTheta.exists_mixLat_form | exact GlobalTheory.SphTheta.exists_mixLat_form | (intros; apply GlobalTheory.SphTheta.exists_mixLat_form <;> assumption)
end
end
