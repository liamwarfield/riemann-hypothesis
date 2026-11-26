module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DatumFock

open GlobalTheory.SplitScalar

theorem exists_derivForm : ∃ l : (ℝ → ℂ) →ₗ[ℂ] ℂ, ∀ g, DifferentiableAt ℝ g 0 → l g = deriv g 0 := by
  let p : Submodule ℂ (ℝ → ℂ) :=
    { carrier := {g | DifferentiableAt ℝ g 0}
      add_mem' := fun ha hb => ha.add hb
      zero_mem' := differentiableAt_const _
      smul_mem' := fun c _ hg => hg.const_smul c }
  let d : p →ₗ[ℂ] ℂ :=
    { toFun := fun g => deriv g.1 0
      map_add' := fun g h => deriv_add g.2 h.2
      map_smul' := fun c g => deriv_const_smul c g.2 }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend d
  exact ⟨l, fun g hg => LinearMap.congr_fun hl ⟨g, hg⟩⟩

variable {D : D7}

def alongLine (l : (ℝ → ℂ) →ₗ[ℂ] ℂ) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (L : ℝ → WO S T) :
    (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun g := fun x => l fun t => heisO ψ S T (L t) g x
  map_add' g g' := by
    funext x
    rw [Pi.add_apply, ← map_add (f := _)]
    congr 1
    funext t
    exact congrFun ((heisL ψ S T (L t)).map_add g g') x
  map_smul' c g := by
    funext x
    rw [RingHom.id_apply, Pi.smul_apply, ← map_smul]
    congr 1
    funext t
    exact congrFun ((heisL ψ S T (L t)).map_smul c g) x

theorem alongLine_heisO (l : (ℝ → ℂ) →ₗ[ℂ] ℂ) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {L : ℝ → WO S T}
    (hL : ∀ t, (L t).map (finPart D) = 0) {u : WO S T} (hu : u.map (infPart D) = 0) (g : WO S T → ℂ) :
    alongLine l ψ S T L (heisO ψ S T u g) = heisO ψ S T u (alongLine l ψ S T L g) := by
  funext x
  have hc : ∀ t, heisO ψ S T (L t) (heisO ψ S T u g) = heisO ψ S T u (heisO ψ S T (L t) g) := by
    intro t
    rw [GlobalTheory.SplitScalar.heisO_comm, GlobalTheory.SplitScalar.symplO_real_fin S T (hL t) hu, AddChar.map_zero_eq_one,
      one_smul]
  have key : ∀ h : WO S T → ℂ, heisO ψ S T u h x = ψ (symplOH S T x u) * h (x + u) := fun _ => rfl
  simp only [alongLine, LinearMap.coe_mk, AddHom.coe_mk, hc, key]
  exact l.map_smul (ψ (symplOH S T x u)) (fun t => heisO ψ S T (L t) g (x + u))

private lemma differentiable_of_continuous_additive_char {φ : ℝ → ℂ} (hφ : Continuous φ) (h0 : φ 0 = 1)
    (hmul : ∀ s t, φ (s + t) = φ s * φ t) : Differentiable ℝ φ := by
  set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, φ x with hFdef
  have hF : ∀ b, HasDerivAt F (φ b) b := fun b => (hφ.integral_hasStrictDerivAt 0 b).hasDerivAt
  obtain ⟨δ, hδ⟩ : ∃ δ, F δ ≠ 0 := by
    by_contra hcon
    have hz : F = fun _ => (0:ℂ) := funext fun δ => by
      by_contra h
      exact hcon ⟨δ, h⟩
    have h1 := hF 0
    rw [hz, h0] at h1
    exact one_ne_zero (h1.unique (hasDerivAt_const (0:ℝ) (0:ℂ)))
  have key : ∀ t, φ t = (F (δ + t) - F t) * (F δ)⁻¹ := by
    intro t
    have h1 : ∫ x in (0:ℝ)..δ, φ (x + t) = F (δ + t) - F t := by
      rw [intervalIntegral.integral_comp_add_right, zero_add, hFdef]
      exact (intervalIntegral.integral_interval_sub_left (hφ.intervalIntegrable _ _)
        (hφ.intervalIntegrable _ _)).symm
    have h2 : ∫ x in (0:ℝ)..δ, φ (x + t) = F δ * φ t := by
      simp_rw [hmul]
      exact intervalIntegral.integral_mul_const _ _
    rw [← h1, h2, mul_comm (F δ) (φ t), mul_assoc, mul_inv_cancel₀ hδ, mul_one]
  intro t
  have hd : DifferentiableAt ℝ (fun t => (F (δ + t) - F t) * (F δ)⁻¹) t :=
    ((((hF (δ + t)).differentiableAt).comp t (differentiableAt_id.const_add δ)).sub
      (hF t).differentiableAt).mul_const _
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall key)

theorem exists_annihLin {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {θ : InfFam D} (hθ : IsInfFam θ)
    (S T : HSp D) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    ∃ A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
      (∀ u : WO S T, u.map (infPart D) = 0 → ∀ g, A (heisO ψ S T u g) = heisO ψ S T u (A g)) ∧
      ∀ g, IsThetaFunO ψ S T g → A g = annih (heisO ψ S T) θ τ J z g := by
  obtain ⟨l, hl⟩ := exists_derivForm
  have hex := GlobalTheory.RealLineAt.lineAt_exists D
  unfold LineAtExists at hex
  have hspec : ∀ w : Matrix (Fin T.rank) (Fin S.rank) ℂ, IsLineAt θ τ w (lineAt θ τ w) := by
    intro w
    obtain ⟨L, hL⟩ := hex θ hθ T.rank S.rank τ w
    exact Classical.epsilon_spec ⟨L, hL⟩
  have hfin : ∀ (w : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ), (lineAt θ τ w t).map (finPart D) = 0 := by
    intro w t
    have h := hspec w
    unfold IsLineAt at h
    exact h.2.1 t
  have hcont : ∀ w : Matrix (Fin T.rank) (Fin S.rank) ℂ, Continuous (lineAt θ τ w) := by
    intro w
    have h := hspec w
    unfold IsLineAt at h
    exact h.1
  have hdiff : ∀ g, IsThetaFunO ψ S T g → ∀ (w : Matrix (Fin T.rank) (Fin S.rank) ℂ) (x : WO S T),
      DifferentiableAt ℝ (fun t => heisO ψ S T (lineAt θ τ w t) g x) 0 := by
    intro g hg w x
    obtain ⟨-, -, -, hsm⟩ := hg
    have hgL : DifferentiableAt ℝ (fun t => g (x + lineAt θ τ w t)) 0 := by
      let L1 : (Fin 1 → ℝ) →+ WO S T := (lineAt θ τ w).comp (Pi.evalAddMonoidHom (fun _ : Fin 1 => ℝ) 0)
      have h1 := hsm 1 L1 ((hcont w).comp (continuous_apply 0)) (fun t => hfin w (t 0)) x
      have h2 : (fun t : ℝ => g (x + lineAt θ τ w t)) =
          (fun t : Fin 1 → ℝ => g (x + L1 t)) ∘ (fun t : ℝ => fun _ : Fin 1 => t) := rfl
      rw [h2]
      exact ((h1.differentiable (by simp)) _).comp _ (differentiableAt_pi.2 fun _ => differentiableAt_id)
    have hφ : Differentiable ℝ (fun t => ψ (symplOH S T x (lineAt θ τ w t))) := by
      apply differentiable_of_continuous_additive_char
      · have hc : (fun t => symplOH S T x (lineAt θ τ w t)) =
            fun t => algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T x (lineAt θ τ w t) := rfl
        exact hψ.comp (hc ▸ continuous_const.mul (GlobalTheory.SplitScalar.continuous_symplO S T continuous_const (hcont w)))
      · rw [map_zero]
        show ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T x 0) = 1
        rw [GlobalTheory.SplitScalar.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]
      · intro s t
        rw [map_add (f := _), GlobalTheory.SplitScalar.symplOH_add_right, AddChar.map_add_eq_mul]
    exact (hφ 0).mul hgL
  refine ⟨alongLine l ψ S T (lineAt θ τ z) + Complex.I • alongLine l ψ S T (lineAt θ τ (J z)), ?_, ?_⟩
  · intro u hu g
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    rw [alongLine_heisO l ψ S T (hfin z) hu, alongLine_heisO l ψ S T (hfin (J z)) hu]
    funext x
    unfold heisO
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro g hg
    funext x
    unfold annih Datum.dRho
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, alongLine,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [hl _ (hdiff g hg z x), hl _ (hdiff g hg (J z) x)]

theorem infPart_of_isHalf {S T : HSp D} {e : AE D} (he : infPart D e = 0) {u : WO S T} (hu : IsHalf e u) :
    u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply, ← hu i j, map_mul, he, zero_mul]

theorem isFockVacAt_of_isThetaAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {θ : InfFam D} (hθ : IsInfFam θ)
    {S T : HSp D} {e : AE D} (he : infPart D e = 0) (he' : infPart D (cA D e) = 0) {Λ : AddSubgroup (WO S T)} {c : ℂ}
    {f₀ Φ f : WO S T → ℂ} (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f)
    (h₀ : IsThetaFunO ψ S T f₀) (hf : IsThetaFunO ψ S T f) {τ : D.what₂.Tau}
    {J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ}
    (hv : IsFockVacAt (heisO ψ S T) θ τ J f₀) : IsFockVacAt (heisO ψ S T) θ τ J f := by
  unfold IsThetaAt AllSome at h
  obtain ⟨⟨Tm, hTm⟩, hU⟩ := h
  unfold IsFockVacAt at hv ⊢
  intro z
  obtain ⟨A, hA, hAθ⟩ := exists_annihLin hψ hθ S T τ J z
  have hadd : ∀ (w : WO S T) (g g' : WO S T → ℂ),
      heisO ψ S T w (g + g') = heisO ψ S T w g + heisO ψ S T w g' :=
    fun _ _ _ => funext fun _ => mul_add _ _ _
  have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + A ∘ₗ Tm) := by
    obtain ⟨htr, hmod, hvac⟩ := hTm
    refine ⟨fun Φ' hΦ x hx => ?_, fun Φ' hΦ y hy => ?_, ?_⟩
    · simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [htr Φ' hΦ x hx, hA x (infPart_of_isHalf he hx), hadd]
    · simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [hmod Φ' hΦ y hy, hA y (infPart_of_isHalf he' hy), hadd]
    · simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [hvac, hAθ f₀ h₀, hv z, add_zero]
  have e1 : f = Tm Φ := hU Tm hTm
  have e2 : f = (Tm + A ∘ₗ Tm) Φ := hU _ hTm'
  rw [LinearMap.add_apply, LinearMap.comp_apply, ← e1] at e2
  rw [← hAθ f hf]
  simpa using e2

theorem isFockVacAt_thPVec : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) βS βT Pg Q ξ (f₀ f : WO S T → ℂ), IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f → IsThetaFunO ψ S T f → ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f h hf τ
  obtain ⟨hv, e, he, ht⟩ := h
  unfold IsVacO IsStdChar at hv
  obtain ⟨hs, ⟨hθ, h₀, -, hfock, -⟩⟩ := hv
  have hψ : Continuous ψ := by
    have h1 := hs.1
    unfold IsCharAF at h1
    exact h1.1
  have ho : GlobalTheory.PlaceModelSum.IsOrthSum e := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  exact isFockVacAt_of_isThetaAt hψ hθ ho.conj.infPart_eq ho.conj.conj.infPart_eq ht h₀ hf (hfock τ)

end GlobalTheory.DatumFock

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParahoricCompact

theorem exists_compact_entries {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) :
    ∃ C : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E), IsCompact C ∧ ∀ x : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E),
      Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) : _ →+* _) x ∈ St β → ∀ i j, x.1 i j ∈ C := by
  classical
  haveI : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :=
    IsModuleTopology.isTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) _
  obtain ⟨-, C0, hC0, hC0m⟩ := GlobalTheory.Mass.intTens_open_compact F E
  let s := GlobalTheory.Mass.swapTens F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)

  let b : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := (β : Matrix (Fin n) (Fin n) _).map s.symm
  let c : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :=
    ((β⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map s.symm

  let f : Fin n → Fin n → (Fin n → Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E :=
    fun i j a => ∑ l, (∑ k, b i k * a k l) * c l j
  have hf : ∀ i j, Continuous (f i j) := fun i j =>
    continuous_finsetSum _ fun l _ =>
      (continuous_finsetSum _ fun k _ =>
        continuous_const.mul ((continuous_apply l).comp (continuous_apply k))).mul continuous_const
  have hS : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => C0) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC0
  refine ⟨⋃ i, ⋃ j, f i j '' Set.univ.pi (fun _ : Fin n => Set.univ.pi fun _ : Fin n => C0),
    isCompact_iUnion fun i => isCompact_iUnion fun j => hS.image (hf i j), ?_⟩
  intro x hx i j
  obtain ⟨y, hy⟩ := hx
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j,
    ⟨fun k l => s.symm ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) k l), ?_, ?_⟩⟩⟩
  · intro k _ l _
    apply hC0m
    change (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E →+* E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (s.symm _) ∈ Formalism.L2.Herm.intAf F E
    rw [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) k l).2
  · have hx' : (x : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) i j =
        s.symm (((Formalism.UG.bc (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E →+* E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) x :
          GL (Fin n) (E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) i j) := by
      rw [Formalism.UG.P.bc_coe]
      simp
    have hy' : Formalism.UG.bc (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E →+* E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) x =
        β * Formalism.L2.DIV.intGL F E n y * β⁻¹ := by
      rw [← hy]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx', hy', Units.val_mul, Units.val_mul, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, Matrix.mul_apply, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Formalism.L2.DIV.intGL, Formalism.UG.P.bc_coe]
    rfl

variable {D : D7}

theorem isOpen_comap_lev (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsOpen (((lev D.sp.cm V.gram β L).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  classical
  haveI := (GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V).1
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hκ
  obtain ⟨hU, hS, hR⟩ := hκ
  show finE V κ ∈ lev D.sp.cm V.gram β L
  refine Formalism.L2.DIV.Kg_le_lev (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right ?_
  simp only [Formalism.L2.DIV.Kg, Subgroup.mem_inf, Subgroup.mem_iInf]
  exact ⟨⟨hU, hS⟩, fun PP hPP => Formalism.L2.DIV.mem_princAt.2 ⟨hS, hR PP hPP⟩⟩

theorem exists_compact (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) :
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ k : GA D V, k ∈ GfC V → finE V k ∈ St β → k ∈ C := by
  obtain ⟨C1, hC1, hC1m⟩ := exists_compact_entries (F := D.host.F) (E := D.host.E) β
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨K, hK, hKm⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ 1 C1 hC1

  haveI : T2Space (InfiniteAdeleRing D.host.F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace D.host.F) → v.Completion))
  haveI : T2Space (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    inferInstanceAs (T2Space (RestrictedProduct
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F) => v.adicCompletion D.host.F)
      (fun v => (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F))) Filter.cofinite))
  haveI : T2Space (AF D.host.F) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing D.host.F × FiniteAdeleRing (𝓞 D.host.F) D.host.F))
  obtain ⟨K', hK', hK'm⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.StabCompact.det_gram_ne_zero V) K hK
  refine ⟨K', hK', fun k hk hst => hK'm k fun i j => hKm _ ?_ ?_⟩
  ·
    have hsw : (GlobalTheory.Mass.swapTens D.host.F D.host.E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) : _ →+* _) = swapAE D :=
      RingHom.ext fun _ => rfl
    have hst' : Formalism.UG.bc (GlobalTheory.Mass.swapTens D.host.F D.host.E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) : _ →+* _)
        (finHom V k) ∈ St β := by
      rw [hsw]
      exact hst
    have h := hC1m (finHom V k) hst' i j
    rw [finHom, MonoidHom.comp_apply, Formalism.UG.P.bc_coe] at h
    exact h
  ·
    intro ρ
    have h1 : infHom V k = 1 := hk
    have h2 : infPart D ((HA.mat (AF D.host.F) D.sp.cm.sig V.gram k : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) i j) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := by
      have h3 := congrArg (fun g : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) =>
        (g : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j) h1
      simp only [infHom, MonoidHom.comp_apply, Formalism.UG.P.bc_coe, Units.val_one] at h3
      exact h3
    rw [h2]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq, map_one, norm_one, le_refl]
    · simp only [Matrix.one_apply_ne hij, map_zero, norm_zero, zero_le_one]

theorem isCompact_levG (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsCompact ((levG V β L : Subgroup (GA D V)) : Set (GA D V)) := by
  haveI := (GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V).1
  obtain ⟨C, hC, hCm⟩ := exists_compact V β
  refine hC.of_isClosed_subset ?_ ?_
  · rw [levG, levA, Subgroup.coe_inf]
    exact (GlobalTheory.Ker.CongTop.isClosed_GfC V).inter
      (Subgroup.isClosed_of_isOpen _ (isOpen_comap_lev V β L))
  · intro k hk
    rw [SetLike.mem_coe, levG, levA, Subgroup.mem_inf] at hk
    exact hCm k hk.1 (Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hk.2))

theorem isCompact_flag_and_lift : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), IsCompact ((levG V β (flagL L) : Subgroup (GA D V)) : Set (GA D V)) ∧ ∀ g0 κ, IsLevelLift V β L g0 κ → κ ∈ levG V β (flagL L) := by
  intro D V β L
  refine ⟨isCompact_levG V β (flagL L), fun g0 κ hκ => ?_⟩
  obtain ⟨h1, h2, -⟩ := hκ
  rw [levG, levA, Subgroup.mem_inf]
  refine ⟨h1, ?_⟩
  show finE V κ ∈ lev D.sp.cm V.gram β (flagL L)
  rw [Formalism.L2.DIV.mem_lev]
  exact ⟨h2, Subgroup.mem_top _⟩

end GlobalTheory.ParahoricCompact
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLiftsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_parahoricLevel_and_contains_lifts : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), IsCompact ((levG V β (flagL L) : Subgroup (GA D V)) : Set (GA D V)) ∧ ∀ g0 κ, IsLevelLift V β L g0 κ → κ ∈ levG V β (flagL L) := by
  first | exact @GlobalTheory.ParahoricCompact.isCompact_flag_and_lift | exact GlobalTheory.ParahoricCompact.isCompact_flag_and_lift | (intros; apply GlobalTheory.ParahoricCompact.isCompact_flag_and_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalEmbeddingLePow
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalEmbeddingLePow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EmbHeight

open scoped NNReal TensorProduct
open NumberField IsDedekindDomain GlobalTheory.AdelicU Formalism.UG

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]


open scoped Matrix.Norms.L2Operator in
theorem exists_opNorm_le (J : Matrix n m ℂ) (P : Matrix m n ℂ) (K : Matrix n n ℂ) :
    ∃ c : ℝ≥0, ∀ (x : Matrix m m ℂ) (h : ℝ≥0), 1 ≤ h → opNorm x ≤ h → opNorm (J * x * P + K) ≤ c * h := by
  refine ⟨‖J‖₊ * ‖P‖₊ + ‖K‖₊, fun x h h1 hx => ?_⟩
  have hx' : ‖x‖₊ ≤ h := hx
  calc opNorm (J * x * P + K) = ‖J * x * P + K‖₊ := rfl
    _ ≤ ‖J * x * P‖₊ + ‖K‖₊ := nnnorm_add_le _ _
    _ ≤ ‖J‖₊ * ‖x‖₊ * ‖P‖₊ + ‖K‖₊ := by
        gcongr
        exact (Matrix.l2_opNNNorm_mul _ _).trans (by gcongr; exact Matrix.l2_opNNNorm_mul _ _)
    _ ≤ ‖J‖₊ * h * ‖P‖₊ + ‖K‖₊ * h := by
        gcongr
        exact le_mul_of_one_le_right (by positivity) h1
    _ = (‖J‖₊ * ‖P‖₊ + ‖K‖₊) * h := by ring

theorem htOf_le {R : Type} [CommRing R] {N₁ : Matrix m m R → ℝ≥0} {N : Matrix n n R → ℝ≥0}
    {f : Matrix m m R → Matrix n n R} {c : ℝ≥0} (hc : 1 ≤ c)
    (hN : ∀ (x : Matrix m m R) (h : ℝ≥0), 1 ≤ h → N₁ x ≤ h → N (f x) ≤ c * h)
    (X : GL n R) (x : GL m R) (h1 : (X : Matrix n n R) = f x)
    (h2 : ((X⁻¹ : GL n R) : Matrix n n R) = f (x⁻¹ : GL m R)) : htOf N X ≤ c * htOf N₁ x := by
  have hx1 : 1 ≤ htOf N₁ x := one_le_htOf N₁ x
  have hc1 : 1 ≤ c * htOf N₁ x := one_le_mul_of_one_le_of_one_le hc hx1
  show max 1 (max (N (X : Matrix n n R)) (N ((X⁻¹ : GL n R) : Matrix n n R))) ≤ c * htOf N₁ x
  refine max_le hc1 (max_le ?_ ?_)
  · rw [h1]
    exact hN _ _ hx1 (le_htOf N₁ x)
  · rw [h2]
    exact hN _ _ hx1 (inv_le_htOf N₁ x)

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem exists_normInf_le (w : InfinitePlace F) (J : Matrix n m (w.Completion ⊗[F] E))
    (P : Matrix m n (w.Completion ⊗[F] E)) (K : Matrix n n (w.Completion ⊗[F] E)) :
    ∃ c : ℝ≥0, 1 ≤ c ∧ ∀ (x : Matrix m m (w.Completion ⊗[F] E)) (h : ℝ≥0), 1 ≤ h → normInf F w x ≤ h →
      normInf F w (J * x * P + K) ≤ c * h := by
  classical
  have hτ : ∀ τ : EmbOver E w, ∃ c : ℝ≥0, ∀ (x : Matrix m m ℂ) (h : ℝ≥0), 1 ≤ h → opNorm x ≤ h →
      opNorm (J.map (infEmb τ) * x * P.map (infEmb τ) + K.map (infEmb τ)) ≤ c * h :=
    fun τ => GlobalTheory.EmbHeight.exists_opNorm_le _ _ _
  choose c hc using hτ
  refine ⟨max 1 (Finset.univ.sup c), le_max_left _ _, fun x h h1 hx => ?_⟩
  rw [normInf_le_iff] at hx ⊢
  intro τ
  rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul]
  refine (hc τ _ h h1 (hx τ)).trans ?_
  gcongr
  exact (Finset.le_sup (Finset.mem_univ τ)).trans (le_max_right _ _)

private lemma normFin_add_le_max (v : HeightOneSpectrum (𝓞 F)) {p q : Type} [Fintype p] [Fintype q]
    (a b : Matrix p q (Fv F v ⊗[F] E)) : normFin F v (a + b) ≤ max (normFin F v a) (normFin F v b) := by
  rw [normFin_le_iff]
  intro i j
  exact (absFin_add_le F v _ _).trans (max_le_max (absFin_le_normFin F v a i j) (absFin_le_normFin F v b i j))


omit [DecidableEq m] [DecidableEq n] in
theorem normFin_le (v : HeightOneSpectrum (𝓞 F)) (J : Matrix n m (Fv F v ⊗[F] E))
    (P : Matrix m n (Fv F v ⊗[F] E)) (K : Matrix n n (Fv F v ⊗[F] E))
    (x : Matrix m m (Fv F v ⊗[F] E)) (h : ℝ≥0) (h1 : 1 ≤ h) (hx : normFin F v x ≤ h) :
    normFin F v (J * x * P + K) ≤ max 1 (max (normFin F v J * normFin F v P) (normFin F v K)) * h := by
  calc normFin F v (J * x * P + K) ≤ max (normFin F v (J * x * P)) (normFin F v K) :=
        normFin_add_le_max F v _ _
    _ ≤ max 1 (max (normFin F v J * normFin F v P) (normFin F v K)) * h := by
        refine max_le ?_ ?_
        · calc normFin F v (J * x * P) ≤ normFin F v J * normFin F v x * normFin F v P :=
                (normFin_mul_le F v _ _).trans (by gcongr; exact normFin_mul_le F v _ _)
            _ ≤ normFin F v J * h * normFin F v P := by gcongr
            _ = normFin F v J * normFin F v P * h := by ring
            _ ≤ _ := by
                gcongr
                exact (le_max_left _ _).trans (le_max_right _ _)
        · calc normFin F v K ≤ max 1 (max (normFin F v J * normFin F v P) (normFin F v K)) :=
                (le_max_right _ _).trans (le_max_right _ _)
            _ ≤ _ := le_mul_of_one_le_right (by positivity) h1


omit [DecidableEq m] [DecidableEq n] in
theorem eventually_normFin_le (y : Matrix m n (AF F ⊗[F] E)) :
    ∀ᶠ v in Filter.cofinite, normFin F v (y.map (compFin F E v)) ≤ 1 := by
  have hall : ∀ᶠ v in Filter.cofinite, ∀ p : m × n, absFin F v (compFin F E v (y p.1 p.2)) ≤ 1 :=
    Filter.eventually_all.2 fun p => eventually_absFin_le_one F (y p.1 p.2)
  filter_upwards [hall] with v hv
  rw [normFin_le_iff]
  intro i j
  exact hv (i, j)

private lemma matrix_map_eq_of_eq {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {p q : Type} [Fintype p]
    [Fintype q] (J : Matrix q p R) (P : Matrix p q R) (K : Matrix q q R) (X : Matrix q q R) (x : Matrix p p R)
    (h : X = J * x * P + K) : X.map φ = J.map φ * x.map φ * P.map φ + K.map φ := by
  rw [h, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul]

theorem exists_heightGL_le (J : Matrix n m (AF F ⊗[F] E)) (P : Matrix m n (AF F ⊗[F] E))
    (K : Matrix n n (AF F ⊗[F] E)) :
    ∃ C : ℝ≥0, ∀ (X : GL n (AF F ⊗[F] E)) (x : GL m (AF F ⊗[F] E)),
      (X : Matrix n n (AF F ⊗[F] E)) = J * (x : Matrix m m (AF F ⊗[F] E)) * P + K →
      ((X⁻¹ : GL n (AF F ⊗[F] E)) : Matrix n n (AF F ⊗[F] E)) =
        J * ((x⁻¹ : GL m (AF F ⊗[F] E)) : Matrix m m (AF F ⊗[F] E)) * P + K →
      heightGL F X ≤ C * heightGL F x := by
  classical
  have hinf : ∀ w : InfinitePlace F, ∃ c : ℝ≥0, 1 ≤ c ∧ ∀ (x : Matrix m m (w.Completion ⊗[F] E)) (h : ℝ≥0),
      1 ≤ h → normInf F w x ≤ h →
        normInf F w (J.map (compInf F E w) * x * P.map (compInf F E w) + K.map (compInf F E w)) ≤ c * h :=
    fun w => GlobalTheory.EmbHeight.exists_normInf_le F w _ _ _
  choose c hc1 hc using hinf
  let M : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v =>
    max 1 (max (normFin F v (J.map (compFin F E v)) * normFin F v (P.map (compFin F E v)))
      (normFin F v (K.map (compFin F E v))))
  have hM1 : ∀ v, 1 ≤ M v := fun v => le_max_left _ _
  have hMfin : (Function.mulSupport M).Finite := by
    have h3 := (GlobalTheory.EmbHeight.eventually_normFin_le F J).and
      ((GlobalTheory.EmbHeight.eventually_normFin_le F P).and (GlobalTheory.EmbHeight.eventually_normFin_le F K))
    refine (Filter.eventually_cofinite.1 h3).subset ?_
    intro v hv hv3
    exact hv (max_eq_left (max_le (mul_le_one' hv3.1 hv3.2.1) hv3.2.2))
  refine ⟨(∏ w, c w) * ∏ᶠ v, M v, fun X x hX hXi => ?_⟩
  have key_inf : ∀ w, htInf F w (Formalism.UG.bc (compInf F E w) X) ≤ c w * htInf F w (Formalism.UG.bc (compInf F E w) x) :=
    fun w => GlobalTheory.EmbHeight.htOf_le (hc1 w) (hc w) _ _ (matrix_map_eq_of_eq _ _ _ _ _ _ hX) (matrix_map_eq_of_eq _ _ _ _ _ _ hXi)
  have key_fin : ∀ v, htFin F v (Formalism.UG.bc (compFin F E v) X) ≤ M v * htFin F v (Formalism.UG.bc (compFin F E v) x) :=
    fun v => GlobalTheory.EmbHeight.htOf_le (hM1 v) (fun y h h1 hy => GlobalTheory.EmbHeight.normFin_le F v _ _ _ y h h1 hy) _ _
      (matrix_map_eq_of_eq _ _ _ _ _ _ hX) (matrix_map_eq_of_eq _ _ _ _ _ _ hXi)
  have hfinX := finite_mulSupport_htFin F X
  have hfinx := finite_mulSupport_htFin F x
  have hI : ∏ w, htInf F w (Formalism.UG.bc (compInf F E w) X) ≤
      (∏ w, c w) * ∏ w, htInf F w (Formalism.UG.bc (compInf F E w) x) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod' fun w _ => key_inf w
  have hF : ∏ᶠ v, htFin F v (Formalism.UG.bc (compFin F E v) X) ≤
      (∏ᶠ v, M v) * ∏ᶠ v, htFin F v (Formalism.UG.bc (compFin F E v) x) := by
    rw [← finprod_mul_distrib hMfin hfinx]
    exact finprod_le_finprod' hfinX ((hMfin.union hfinx).subset (Function.mulSupport_mul _ _)) fun v => key_fin v
  unfold heightGL
  calc _ ≤ ((∏ w, c w) * ∏ w, htInf F w (Formalism.UG.bc (compInf F E w) x)) *
        ((∏ᶠ v, M v) * ∏ᶠ v, htFin F v (Formalism.UG.bc (compFin F E v) x)) := mul_le_mul' hI hF
    _ = _ := by ring

theorem height_emb_le : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ (C : ℝ) (a : ℕ),
    ∀ g : GA D A, GlobalTheory.Grow.height S (o.emb (g, 1)) ≤ C * GlobalTheory.Grow.height A g ^ a := by
  intro D S A B o
  obtain ⟨C, hC⟩ := GlobalTheory.EmbHeight.exists_heightGL_le D.host.F o.jA o.pA (o.jB * o.pB)
  refine ⟨(C : ℝ), 1, fun g => ?_⟩
  have e : ∀ a : GA D A, (Formalism.L2.Theta.matHom S (o.emb (a, 1)) :
      Matrix (Fin S.rank) (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) =
      o.jA * (Formalism.L2.Theta.matHom A a : Matrix (Fin A.rank) (Fin A.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) *
        o.pA + o.jB * o.pB := by
    intro a
    have hm := o.mt_emb a 1
    rw [GlobalTheory.MixModel.mt_one, Matrix.mul_one] at hm
    exact hm
  have hinv : o.emb (g⁻¹, 1) = (o.emb (g, 1))⁻¹ := by
    rw [← map_inv, Prod.inv_mk, inv_one]
  have e2 := e g⁻¹
  rw [hinv, map_inv, map_inv] at e2
  have key := hC _ _ (e g) e2
  unfold GlobalTheory.Grow.height
  rw [pow_one]
  exact_mod_cast key

end GlobalTheory.EmbHeight

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalEmbeddingLePowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicHeight_orthogonalEmbedding_le_pow : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ (C : ℝ) (a : ℕ), ∀ g : GA D A, GlobalTheory.Grow.height S (o.emb (g, 1)) ≤ C * GlobalTheory.Grow.height A g ^ a := by
  first | exact @GlobalTheory.EmbHeight.height_emb_le | exact GlobalTheory.EmbHeight.height_emb_le | (intros; apply GlobalTheory.EmbHeight.height_emb_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField

namespace GlobalTheory.Chain.VacVec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

private theorem Jm_mul_Jm_eq_oneFormalDegree {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

private theorem conjTranspose_Jm_eq_Jm {n : ℕ} (ε : Fin n → Bool) :
    Matrix.conjTranspose (Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

private theorem conj_cartan_involution_props {n : ℕ} (F J : Matrix (Fin n) (Fin n) ℂ) (hF : IsUnit F) (hJ : J * J = 1)
    (hJh : Matrix.conjTranspose J = J) :
    F⁻¹ * J * F * (F⁻¹ * J * F) = 1 ∧
      Matrix.conjTranspose (F⁻¹ * J * F) * (Matrix.conjTranspose F * J * F) * (F⁻¹ * J * F) =
        Matrix.conjTranspose F * J * F ∧
      Matrix.conjTranspose F * J * F * (F⁻¹ * J * F) = Matrix.conjTranspose F * F := by
  have hd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp hF
  have hdh : IsUnit (Matrix.conjTranspose F).det := by rw [Matrix.det_conjTranspose]; exact hd.star
  have hJJ : ∀ X : Matrix (Fin n) (Fin n) ℂ, J * (J * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJJ]
    exact Matrix.nonsing_inv_mul F hd
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hJh, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ hdh, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJJ]
  · simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJJ]


open Matrix in
open scoped ComplexOrder in
theorem cart_isCartanInv {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    IsCartanInv (gramAt D V τ) (cart M τ) := by
  unfold IsCartanInv cart
  rw [← M.fr_gram τ]
  obtain ⟨h1, h2, h3⟩ := conj_cartan_involution_props _ _ (M.fr_unit τ) (Jm_mul_Jm_eq_oneFormalDegree (M.ε τ)) (conjTranspose_Jm_eq_Jm (M.ε τ))
  refine ⟨h1, h2, ?_⟩
  rw [h3]
  have hinj : Function.Injective (M.fr τ).mulVec := Matrix.mulVec_injective_iff_isUnit.mpr (M.fr_unit τ)
  simpa only [Matrix.mul_one] using Matrix.PosDef.one.conjTranspose_mul_mul_same hinj

end GlobalTheory.Chain.VacVec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlaceProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlaceProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

theorem idem_eq_locIdem (D : D7) (p : Place D) : idem D p = GlobalTheory.LocWeil.idem D p := by
  rcases p with v | τ
  · rw [GlobalTheory.LocWeil.PlaceIdem.idem_inl]
    rfl
  · rw [GlobalTheory.LocWeil.PlaceIdem.idem_inr]
    simp only [idem, GlobalTheory.LocWeil.PlaceIdem.eInf]
    congr 2

theorem idem_spec : ∀ D : D7, (∀ p, idem D p * idem D p = idem D p) ∧ (∀ p q, p ≠ q → idem D p * idem D q = 0) ∧ (∀ p, cA D (idem D p) = idem D p) ∧ (∀ v : FinPl D, infPart D (idem D (.inl v)) = 0 ∧ finPart D (idem D (.inl v)) ∈ intAE D ∧ IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1))) ∧ (∀ τ : D.what₂.Tau, finPart D (idem D (.inr τ)) = 0) ∧ infPart D (∑ τ : D.what₂.Tau, idem D (.inr τ)) = 1 ∧ ∀ θ : InfFam D, IsInfFam θ → ∀ τ : D.what₂.Tau, θ τ (infPart D (idem D (.inr τ))) = 1 ∧ ∀ τ' : D.what₂.Tau, τ' ≠ τ → θ τ (infPart D (idem D (.inr τ'))) = 0 := by
  intro D
  have hE : ∀ p, idem D p = GlobalTheory.LocWeil.idem D p := idem_eq_locIdem D
  obtain ⟨hOrth, hTheta, hFinInf, hSum, -, -⟩ := GlobalTheory.LocWeil.PlaceIdem.idem_props D
  simp only [hE]
  refine ⟨fun p => GlobalTheory.LocWeil.idem_mul_self p, fun p q hpq => hOrth p q hpq, fun p => GlobalTheory.LocWeil.cA_idem p,
    ?_, hFinInf, hSum, ?_⟩
  · intro v
    rw [GlobalTheory.LocWeil.PlaceIdem.idem_inl, GlobalTheory.LocWeil.PlaceIdem.infPart_algebraMap,
      GlobalTheory.LocWeil.PlaceIdem.finPart_algebraMap]
    refine ⟨?_, ?_, ⟨singleV D.host.F v 1, rfl, GlobalTheory.LocWeil.PlaceIdem.evalV_single_same _ v,
      fun v' h => GlobalTheory.LocWeil.PlaceIdem.evalV_single_ne _ h⟩⟩
    · exact TensorProduct.zero_tmul _ _
    · apply AddSubgroup.subset_closure
      refine ⟨singleV D.host.F v 1, ?_, 1, ?_⟩
      · simp only [intAf, Set.mem_setOf_eq]
        intro u
        rcases eq_or_ne u v with rfl | h
        · rw [GlobalTheory.LocWeil.PlaceIdem.evalV_single_same]
          exact one_mem _
        · rw [GlobalTheory.LocWeil.PlaceIdem.evalV_single_ne _ h]
          exact zero_mem _
      · rfl
  · intro θ hθ τ
    refine ⟨?_, fun τ' h => ?_⟩
    · rw [hTheta θ hθ τ τ, if_pos rfl]
    · rw [hTheta θ hθ τ' τ, if_neg (Ne.symm h)]

end GlobalTheory.PlaceTensor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlacePropertiesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmAdeleIdempotentOfPlace_properties : ∀ D : D7, (∀ p, idem D p * idem D p = idem D p) ∧ (∀ p q, p ≠ q → idem D p * idem D q = 0) ∧ (∀ p, cA D (idem D p) = idem D p) ∧ (∀ v : FinPl D, infPart D (idem D (.inl v)) = 0 ∧ finPart D (idem D (.inl v)) ∈ intAE D ∧ IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1))) ∧ (∀ τ : D.what₂.Tau, finPart D (idem D (.inr τ)) = 0) ∧ infPart D (∑ τ : D.what₂.Tau, idem D (.inr τ)) = 1 ∧ ∀ θ : InfFam D, IsInfFam θ → ∀ τ : D.what₂.Tau, θ τ (infPart D (idem D (.inr τ))) = 1 ∧ ∀ τ' : D.what₂.Tau, τ' ≠ τ → θ τ (infPart D (idem D (.inr τ'))) = 0 := by
  first | exact @GlobalTheory.PlaceTensor.idem_spec | exact GlobalTheory.PlaceTensor.idem_spec | (intros; apply GlobalTheory.PlaceTensor.idem_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero one_le_codiff char_fin_add)
open scoped nonZeroDivisors

namespace GlobalTheory.SplitUnram

variable {F : Type} [Field F] [NumberField F]

theorem mem_adelicIdeal_codiff_iff {ψ : AddChar (AF F) ℂ} (hc : Continuous ψ)
    (h : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ))) (y : Af F) :
    y ∈ adelicIdeal (codiff F) ↔
      ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 (α * y)) = 1 := by
  have h1 : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) = 1 ↔
      Algebra.trace ℚ F x ∈ (algebraMap ℤ ℚ).range := fun x => by
    rw [h, mul_comm, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have := mul_right_cancel₀ Complex.two_pi_I_ne_zero hn
      rw [eq_intCast]
      exact_mod_cast this.symm
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← hn, eq_intCast, Rat.cast_intCast]⟩
  have h2 : ∀ x : F, x ∈ codiff F ↔
      ∀ a : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((a : F) * x))) = 1 := fun x => by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))]
    simp_rw [h1, Algebra.traceForm_apply]
    constructor
    · intro H a
      rw [mul_comm]
      exact H _ ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
    · intro H a ha
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      rw [mul_comm]
      exact H a
  have key : ∀ x : F, x ∈ codiff F ↔ ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) →
      ψ (pairA F 0 (α * algebraMap F (Af F) x)) = 1 := fun x => by
    rw [h2]
    refine ⟨fun H α hα => GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hc x H α hα,
      fun H a => ?_⟩
    rw [map_mul]
    refine H _ fun v => ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, adele_algebraMap_apply, valued_algebraMap]
    exact v.valuation_le_one a
  have hint : ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 α) = 1 :=
    fun α hα => by
      have := (key 1).1 (one_le_codiff (FractionalIdeal.one_mem_one _)) α hα
      rwa [map_one, mul_one] at this
  obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F)) y
  have hx1 := mem_adelicIdeal_one_iff.1 hx
  have hx2 : y - algebraMap F (Af F) x ∈ adelicIdeal (codiff F) := by
    refine (mem_adelicIdeal_iff codiff_ne_zero).2 fun v => (hx1 v).trans ?_
    have := FractionalIdeal.count_mono F v (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))
      (one_le_codiff (F := F))
    rw [FractionalIdeal.count_one] at this
    rw [← exp_zero, exp_le_exp]
    omega
  have e : y = algebraMap F (Af F) x + (y - algebraMap F (Af F) x) := by ring
  rw [e, (adelicIdeal (codiff F)).add_mem_iff_left hx2, algebraMap_mem_adelicIdeal codiff_ne_zero, key]
  refine forall_congr' fun α => forall_congr' fun hα => ?_
  rw [mul_add, char_fin_add, hint (α * (y - algebraMap F (Af F) x))
    fun v => mul_mem (hα v) (hx1 v), mul_one]

theorem not_dvd_different {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 F))
    (hv : (p : 𝓞 F) ∈ v.asIdeal) (h2 : (p : 𝓞 F) ∉ v.asIdeal ^ 2) :
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp'.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {(p : ℤ)}) = Ideal.span {((p : ℕ) : 𝓞 F)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {(p : ℤ)}) ≤ v.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have := v.isPrime
  have : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [not_dvd_differentIdeal_iff]
  apply Ideal.ramificationIdx_eq_one_iff.1
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) v.asIdeal hb]
  by_contra hne
  rw [← ne_eq, Ideal.ramificationIdx'_ne_one_iff hle, hmap, Ideal.span_le] at hne
  exact h2 (by simpa using hne)

theorem count_codiff_eq_zero (v : HeightOneSpectrum (𝓞 F)) (h : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) :
    FractionalIdeal.count F v (codiff F) = 0 := by
  have hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (codiff F)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have h0 : differentIdeal ℤ (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have h1 := FractionalIdeal.count_coe F v h0
  rw [hD, FractionalIdeal.count_inv,
    not_not.1 (mt (Associates.count_ne_zero_iff_dvd h0 v.irreducible).1 h)] at h1
  simpa using h1

theorem not_mem_sq_of_ext {E : Type} [Field E] [NumberField E] [Algebra F E] {p : ℕ}
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → (p : 𝓞 E) ∉ w.asIdeal ^ 2)
    (v : HeightOneSpectrum (𝓞 F)) : (p : 𝓞 F) ∉ v.asIdeal ^ 2 := by
  intro hv
  have := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hb : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  have hle : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ Q :=
    Ideal.map_le_iff_le_comap.2 hQv.over.le
  have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hv
  rw [Ideal.map_pow, map_natCast] at h1
  have h2 : (p : 𝓞 E) ∈ Q ^ 2 := Ideal.pow_right_mono hle 2 h1
  exact h ⟨Q, hQ.isPrime, hb⟩ (Ideal.pow_le_self two_ne_zero h2) h2

end GlobalTheory.SplitUnram

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLiftsToParahoricLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLiftsToParahoricLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FiniteGroupLifts

theorem liftsExist_of_twist_empty :
    ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → L.Q = ∅ → (∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, ¬ IsConjPl PP PP') → LiftsExist V β L := by
  intro D V β L Λ N hB hQ hP

  refine GlobalTheory.T.parahoricLevel_liftsExist V β L Λ N hB ?_ ?_
  · intro PP hPP PP' hPP'
    rcases hPP' with h | h
    · exact hP PP hPP PP' h
    · simp [hQ] at h
  · simp [hQ]

end GlobalTheory.FiniteGroupLifts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLiftsToParahoricLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_group_lifts_to_parahoric_level : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → L.Q = ∅ → (∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, ¬ IsConjPl PP PP') → LiftsExist V β L := by
  first | exact @GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty | exact GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty | (intros; apply GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeHeckeCharOfLocalComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeHeckeCharOfLocalComponents
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaTildeOfComponents

theorem isEtaTilde_of_chrEq : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (η : (AE D)ˣ →* Circle), ChrEq η C.eta → ResEta D η 1 → IsEtaTilde D η := by
  intro D C η hc hres
  have hE := C.isEta

  have hInf : C.eta.HasInfQ (tauE D) (fun _ => (1 / 2 : ℚ)) := by
    refine ⟨fun _ => 1, fun _ => by norm_num, fun k => ?_⟩
    rw [hE.inf k]
    exact (Fintype.prod_equiv D.eTau _ _ (fun _ => rfl)).symm
  have h1 : 1 ∈ intAE D := by
    apply AddSubgroup.subset_closure
    refine ⟨1, fun v => ?_, 1, rfl⟩
    simp [evalV, (v.adicCompletionIntegers D.host.F).one_mem]
  refine ⟨hc.1, ?_, hres, fun τ => GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D η C.eta _ hc hInf τ⟩

  intro x hx1 hx2 hx3
  refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D η C.eta hc ?_ 1 (fun P _ => hE.unr P) x ⟨hx1, hx2, hx3⟩
    ⟨finPart D (x : AE D) - 1, sub_mem hx2 h1, (one_nsmul _).symm⟩
  intro P y hy _
  exact hE.unr P y hy

end GlobalTheory.EtaTildeOfComponents
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeHeckeCharOfLocalComponentsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramifiedEtaTildeHeckeChar_of_local_components : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (η : (AE D)ˣ →* Circle), ChrEq η C.eta → ResEta D η 1 → IsEtaTilde D η := by
  first | exact @GlobalTheory.EtaTildeOfComponents.isEtaTilde_of_chrEq | exact GlobalTheory.EtaTildeOfComponents.isEtaTilde_of_chrEq | (intros; apply GlobalTheory.EtaTildeOfComponents.isEtaTilde_of_chrEq <;> assumption)
end
end
