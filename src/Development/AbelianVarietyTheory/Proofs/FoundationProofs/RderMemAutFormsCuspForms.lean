module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspLie

theorem hasDerivAt_constTermOn {G : Type} [Group G] [TopologicalSpace G] {Γ N : Subgroup G} [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ] [LocallyCompactSpace N]
    (hc : Cocompact Γ N) {φ ψ : G → ℂ} (hφ : LeftInv Γ φ) (hφc : Continuous φ) (hψ : LeftInv Γ ψ) (hψc : Continuous ψ)
    {u : ℝ → G} (hu : Continuous u) (hd : ∀ g t, HasDerivAt (fun s => φ (g * u s)) (ψ (g * u t)) t) (x : G) :
    HasDerivAt (fun s => constTermOn Γ N φ (x * u s)) (constTermOn Γ N ψ (x * u 0)) 0 := by
  have := hc.isProbabilityMeasure
  obtain ⟨K, hK, hs⟩ := id hc
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall (0 : ℝ) 1)).exists_bound_of_continuousOn
    (f := fun p : N × ℝ => ψ (p.1 * (x * u p.2))) (by fun_prop)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := probMeasure Γ N) (bound := fun _ => C)
    (F := fun s q => φ ((q.out : N) * (x * u s))) (F' := fun s q => ψ ((q.out : N) * (x * u s)))
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) (.of_forall fun s => (hc.integrable hφ hφc _).1) (hc.integrable hφ hφc _)
    (hc.integrable hψ hψc _).1 (.of_forall fun q s hs' => ?_) (integrable_const C) (.of_forall fun q s _ => ?_)).2
  · obtain ⟨γ, hγ, hk⟩ := hs q.out
    exact (congrArg norm (leftInv_integrand hψ (x * u s) γ hγ q.out)).ge.trans
      (hC (_, s) ⟨hk, Metric.ball_subset_closedBall hs'⟩)
  · simpa only [mul_assoc] using hd ((q.out : N) * x) s

variable {D : D7} {θ : InfF D} {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} {φ : GA D V → ℂ}

theorem gelf_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (hφ : φ ∈ SmFun θ V) (τ' : D.what₂.Tau) (k : ℕ) :
    gelf θ V τ' k (Rder θ V τ X φ) = Rder θ V τ X (gelf θ V τ' k φ) := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  obtain ⟨c, hc, hg⟩ := GlobalTheory.SmoothForms.exists_gelf R τ'
  let ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, (GlobalTheory.SmoothForms.smooth_iff R φ).1 hφ⟩
  let X' : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X, hX⟩
  have e : ∀ f : GlobalTheory.SmoothForms.SmF θ V, Rder θ V τ X f.1 =
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ X') f).1 := fun f => GlobalTheory.SmoothForms.Rder_eq R τ X' f.1
  have hcomm : Commute (GlobalTheory.SmoothForms.envRep R τ' (c k))
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ X')) := by
    rw [← GlobalTheory.SmoothForms.envRep_ι]
    by_cases h : τ' = τ
    · subst h
      have hm : c k ∈ Subalgebra.center ℂ _ := hc ▸ Algebra.subset_adjoin ⟨k, rfl⟩
      exact Commute.map (Subalgebra.mem_center_iff.1 hm _).symm _
    · exact GlobalTheory.SmoothForms.envRep_comm R h _ _
  change gelf θ V τ' k (Rder θ V τ X ψ.1) = Rder θ V τ X (gelf θ V τ' k ψ.1)
  rw [e ψ, hg, hg, e]
  exact congrArg (fun S : Module.End ℂ (GlobalTheory.SmoothForms.SmF θ V) => (S ψ).1) hcomm.eq

theorem fg_comap {W : Submodule ℂ (GA D V → ℂ)} (hW : FiniteDimensional ℂ W) :
    (W.comap (SmFun θ V).subtype).FG :=
  Module.Finite.iff_fg.1 (FiniteDimensional.of_injective ((SmFun θ V).subtype.restrict (q := W) fun _ hx => hx)
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : W => z.1) h)))

theorem derEnd_coe (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (f : SmFun θ V) : (derEnd hθ τ X f).1 = Rder θ V τ X f.1 :=
  GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hX f.1

theorem isAutFunSm_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (h : IsAutFunSm θ V φ) :
    IsAutFunSm θ V (Rder θ V τ X φ) := by
  refine { left := fun γ hγ => GlobalTheory.Mem.Lift.Rder_left (h.left γ hγ) τ X, level := ?_, cont := ?_,
           smooth := Rder_mem h.smooth hX, zfin := ?_, growth := ?_ }
  · obtain ⟨U, hU, e⟩ := h.level
    refine ⟨U, hU, fun k hk hf g => ?_⟩
    have := congrFun (GlobalTheory.Mem.FinTranslate.Rder_rTr (θ := θ) hf τ X φ) g
    rw [show rTr V k φ = φ from funext (e k hk hf)] at this
    exact this.symm
  · exact GlobalTheory.Size.continuous_rWord hθ h.smooth h.cont (GlobalTheory.Grow.unifModGrowth_of_isAutFunSm hθ h) (l := [(τ, X)])
      fun p hp => by rw [List.mem_singleton.1 hp]; exact hX
  · obtain ⟨W, hW, m, s⟩ := h.zfin
    refine ⟨((W.comap (SmFun θ V).subtype).map (derEnd hθ τ X)).map (SmFun θ V).subtype,
      Module.Finite.iff_fg.2 (((fg_comap hW).map _).map _),
      ⟨_, ⟨⟨φ, h.smooth⟩, m, rfl⟩, derEnd_coe hθ hX _⟩, ?_⟩
    rintro τ' k _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨_, ⟨⟨_, (linOnSm_gelf τ' k).mem _ f.2⟩, s τ' k _ hf, rfl⟩, ?_⟩
    rw [Submodule.subtype_apply, Submodule.subtype_apply, derEnd_coe hθ hX, derEnd_coe hθ hX, gelf_Rder hθ hX f.2]
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using
      hN (l ++ [(τ, X)]) (GlobalTheory.Mem.Lift.append_mem_lie hl hX) x

theorem isKFinite_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) {K : Subgroup (GA D V)} (hK : K ≤ GinfC V)
    (hs : φ ∈ SmFun θ V) (h : GlobalTheory.Doubling.IsKFinite K φ) : GlobalTheory.Doubling.IsKFinite K (Rder θ V τ X φ) := by
  obtain ⟨W, hW, m⟩ := GlobalTheory.Doubling.isKFinite_iff.1 h
  refine GlobalTheory.Doubling.isKFinite_iff.2
    ⟨(Submodule.map₂ (derEnd hθ τ) ⊤ (W.comap (SmFun θ V).subtype)).map (SmFun θ V).subtype,
      Module.Finite.iff_fg.2 ((Submodule.FG.map₂ _ Module.Finite.fg_top (fg_comap hW)).map _), fun k hk => ?_⟩
  have hr : ∀ k ∈ K, IsRealPt θ k := fun k hk => ⟨hK hk, FockCompare.RealAction.infMat_mem_UH hθ V k⟩
  have hi := hr _ (inv_mem hk)
  refine ⟨_, Submodule.apply_mem_map₂ _ (Submodule.mem_top (x := adAt θ k⁻¹ τ X))
    (n := ⟨rTr V k φ, rTr_mem hθ (hr k hk) hs⟩) (m k hk), ?_⟩
  rw [Submodule.subtype_apply, derEnd_coe hθ (adAt_mem hi hX)]
  funext g
  have := congrFun (Rder_rTr hθ hi hX (rTr V k φ)) (g * k)
  rw [show rTr V k⁻¹ (rTr V k φ) = φ from funext fun y => by simp [rTr]] at this
  rw [this, rTr, mul_inv_cancel_right]

theorem isCuspFun_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) :
    IsCuspFun V (Rder θ V τ X φ) := by
  have h' := isAutFunSm_Rder hθ hX h
  refine (isCuspFun_iff h'.left).2 fun W hW => funext fun x => ?_
  have h0 : constTermOn (GQ V) (NA (.single hW)) φ = 0 := (isCuspFun_iff h.left).1 hc W hW
  have := hasDerivAt_constTermOn (cocompact_single hW) h.left h.cont h'.left h'.cont (GlobalTheory.Mem.Lift.continuous_oneP hθ hX)
    (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder h.smooth hX)) x
  rw [h0, GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at this
  exact this.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))

end GlobalTheory.CuspLie

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsParamFunVIffIsSysParamDOfLevel
noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}

theorem isParamVec_iff_isSysParam (hJ : SphOff J χ Sb) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ Sb)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (h : w.under (𝓞 D.host.F) = v) {f : GA D V → ℂ} (h0 : f ≠ 0)
    (hf : ∀ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, ∀ g, f (g * emb D.sp.cm.sig V.gram v k) = f g)
    {c : List ℤ → ℂ} (hc : ∀ d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c d • f) (B : Multiset ℂˣ) :
    IsParamVec D.sp.cm.sig V.gram (frameLat V) h ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v)) f B ↔
      IsSysParam D.sp.cm.sig V.rank h c B := by
  have hx : f ∈ fixed ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v))
      (stabLoc D.sp.cm.sig V.gram (frameLat V) v) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => funext (hf k hk)
  have hs := isEigenSys_of_heckeLin hJ hv h hx hc
  have hL := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hH := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V
  have hspan : Submodule.span D.host.E (frameLat V : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have heq : (frameLat V : Set (Fin V.rank → D.host.E)) =
        V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) :=
      (V.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
    rw [heq, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  have hd := GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D V v
  exact ⟨hs.isSysParam, hs.isParamVec h0 hx
    (fun hv => (SplitChart.exists_isSplitChart (isCMExt_host D) hH hL.fg hspan h hv hd).imp fun _ he => he.1)
    fun hw τ hτ => ((((exists_isInertChart _ (isCMExt_host D) v).2 w h hw).2.2.2.2 τ hτ).2 _ _ _ hH hL.fg
      hspan hd).imp fun _ he => he.1⟩

theorem isParamFunV_iff_isSysParamD (hJ : SphOff J χ Sb) {f : GA D V → ℂ} (h0 : f ≠ 0)
    (hf : ∀ v ∉ Sb, ∀ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, ∀ g, f (g * emb D.sp.cm.sig V.gram v k) = f g)
    {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ}
    (hc : ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = c P d • f) (B : Fam D.host.E) :
    IsParamFunV V Sb f B ↔ IsSysParamD D Sb V.rank c B :=
  forall₂_congr fun v hv => forall₂_congr fun w h => isParamVec_iff_isSysParam hJ hv h h0 (hf v hv) (hc w) (B w)

theorem isParamFunV_iff_isSysParamD_of_level (hJ : SphOff J χ Sb) {f : GA D V → ℂ} (h0 : f ≠ 0)
    (hf : ∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ}
    (hc : ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = c P d • f) (B : Fam D.host.E) :
    IsParamFunV V Sb f B ↔ IsSysParamD D Sb V.rank c B :=
  isParamFunV_iff_isSysParamD hJ h0 (fun _ hv _ hk => fixed_of_level hJ hv hf hk) hc B

variable {S : D.what₂.Tau → SPar} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {M : DSModel V S}

theorem isParamFunV_iff_of_mem_partFull (hJ : SphOff J χ Sb) {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ}
    {T : MMap M} (hT : T ∈ partFull θ M J χ Sb c) {x : M.Vec} (h0 : T x ≠ 0) (B : Fam D.host.E) :
    IsParamFunV V Sb (T x) B ↔ IsSysParamD D Sb V.rank c B :=
  have h := (mem_partFull θ M J χ Sb c T).1 hT
  isParamFunV_iff_isSysParamD_of_level hJ h0 (((GlobalTheory.MultMem.mem_mult_iff ..).1 h.1).lev x)
    (fun P d R hR => h.2 P d R hR x) B

theorem param_iff_sysParam (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ)
    (B : Fam D.host.E) (hJ : SphOff J χ Sb) :
    (∀ f : GA D V → ℂ, f ≠ 0 →
      (∀ v ∉ Sb, ∀ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, ∀ g, f (g * emb D.sp.cm.sig V.gram v k) = f g) →
      (∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = c P d • f) →
      (IsParamFunV V Sb f B ↔ IsSysParamD D Sb V.rank c B)) ∧
    ∀ (S : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S),
      ∀ T ∈ partFull θ M J χ Sb c, ∀ x : M.Vec, T x ≠ 0 →
        (IsParamFunV V Sb (T x) B ↔ IsSysParamD D Sb V.rank c B) :=
  ⟨fun _ h0 hf hc => isParamFunV_iff_isSysParamD hJ h0 hf hc B,
    fun _ _ _ _ hT _ h0 => isParamFunV_iff_of_mem_partFull hJ hT h0 B⟩

theorem sphOff_KsphC (V : HSp D) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    SphOff (KsphC V ∅) (fun _ => 1) Sb := fun P _ => by
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem (comp_finAdEquiv D) P
  exact ⟨e, f, h, fun _ _ => Iff.rfl, fun _ _ _ => rfl⟩

end GlobalTheory.LFun

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardFrameOfDiagonalStages
noncomputable section

namespace GlobalTheory.StdFrameObj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.FWT GlobalTheory.Mem

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_piT_mul {P : PreCh} (L : LevCh P) :
    (star (L.piT P.u₀ : L.host.E) : L.host.E) * (L.piT P.u₀ : L.host.E) = (L.T P.u₀ : L.host.E) := by
  have h : (star (L.piT P.u₀ : L.host.E) : L.host.E) = L.host.conj (L.piT P.u₀ : L.host.E) :=
    bridge_star_holds P.R L.host _
  rw [h, mul_comm]
  exact L.piT_norm _

def coordPre (P : PreCh) (L : LevCh P) : Pre :=
  Pre.ofCh P L (DiagSp.spacesNorm P.R (host_cmData P.R L.host) (L.T P.u₀) (L.T_prime _) _ (star_piT_mul L)) rfl
    (fun j _ τ => DiagSp.spacesNorm_Y_sig _ _ _ _ _ _ j τ)
    (fun j _ hj => DiagSp.spacesNorm_hasFrame _ _ _ _ _ _ j hj) (fun _ _ _ => rfl)
    (DiagSp.spacesNorm_z_norm _ _ _ _ _ _)

theorem diagSpaces_coordPre (P : PreCh) (L : LevCh P) : DiagSpaces (coordPre P L).sp :=
  DiagSp.spacesNorm_coord _ _ _ _ _ _

end GlobalTheory.StdFrameObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurePreservingConj
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal Pointwise

noncomputable section

namespace GlobalTheory.Cusp.Stages

section Alg

variable {G : Type} [Group G] (Γ : Subgroup G) {N N' : Subgroup G}

def pairs (hn : ∀ p ∈ N, ∀ n ∈ N', p * n * p⁻¹ ∈ N') : Subgroup (N × N) where
  carrier := {p | (p.1 : G) ∈ Γ ∧ (p.2 : G) ∈ Γ ∧ (p.1 : G) * (p.2 : G)⁻¹ ∈ N'}
  one_mem' := ⟨one_mem _, one_mem _, by simp⟩
  mul_mem' := fun {p q} hp hq => ⟨mul_mem hp.1 hq.1, mul_mem hp.2.1 hq.2.1, by
    simpa [mul_assoc] using mul_mem (hn _ p.1.2 _ hq.2.2) hp.2.2⟩
  inv_mem' := fun {p} hp => ⟨inv_mem hp.1, inv_mem hp.2.1, by
    simpa [mul_assoc] using hn _ (inv_mem p.1.2) _ (inv_mem hp.2.2)⟩

variable {Γ} {hn : ∀ p ∈ N, ∀ n ∈ N', p * n * p⁻¹ ∈ N'}

instance : MulAction (pairs Γ hn) (N' × N) where
  smul p z := (⟨p.1.1 * z.1 * (p.1.2 : G)⁻¹, by
    simpa [mul_assoc] using mul_mem p.2.2.2 (hn _ p.1.2.2 _ z.1.2)⟩, p.1.2 * z.2)
  one_smul z := Prod.ext (Subtype.ext (by
    change ((1 : N) : G) * _ * ((1 : N) : G)⁻¹ = _; simp)) (one_mul _)
  mul_smul p q z := Prod.ext (Subtype.ext (by
    change ((p.1.1 * q.1.1 : N) : G) * _ * ((p.1.2 * q.1.2 : N) : G)⁻¹ =
      p.1.1 * (q.1.1 * z.1 * (q.1.2 : G)⁻¹) * (p.1.2 : G)⁻¹
    simp [mul_assoc])) (mul_assoc _ _ _)

theorem smul_fst (p : pairs Γ hn) (z : N' × N) : ((p • z).1 : G) = p.1.1 * z.1 * (p.1.2 : G)⁻¹ := rfl

theorem smul_snd (p : pairs Γ hn) (z : N' × N) : (p • z).2 = p.1.2 * z.2 := rfl

theorem existsUnique_prod (hle : N' ≤ N) {A : Set N'} {B : Set N}
    (hA : ∀ m : N', ∃! δ : Γ.subgroupOf N', (δ : N') * m ∈ A)
    (hB : ∀ n : N, ∃! γ : Γ.subgroupOf N, (γ : N) * n ∈ B) (z : N' × N) :
    ∃! p : pairs Γ hn, p • z ∈ A ×ˢ B := by
  obtain ⟨b, hb, hb'⟩ := hB z.2
  obtain ⟨d, hd, hd'⟩ := hA ⟨(b.1 : G) * z.1 * (b.1 : G)⁻¹, hn _ b.1.2 _ z.1.2⟩
  refine ⟨⟨(⟨d.1.1, hle d.1.2⟩ * b.1, b.1), Γ.mul_mem (show d.1.1 ∈ Γ from d.2) (show b.1.1 ∈ Γ from b.2), b.2, by simp⟩, ⟨?_, hb⟩, fun q hq => ?_⟩
  · convert hd using 1
    exact Subtype.ext (by simp [smul_fst, mul_assoc])
  · have e : q.1.2 = b.1 := congrArg Subtype.val (hb' ⟨q.1.2, q.2.2.1⟩ hq.2)
    have e' := hd' ⟨⟨_, q.2.2.2⟩, mul_mem q.2.1 (inv_mem q.2.2.1)⟩ (by
      convert hq.1 using 1
      exact Subtype.ext (by simp [smul_fst, mul_assoc, e]))
    refine Subtype.ext (Prod.ext (Subtype.ext ?_) e)
    simp [← e', e]

theorem existsUnique_shear (hle : N' ≤ N) {A : Set N'} {B : Set N}
    (hA : ∀ m : N', ∃! δ : Γ.subgroupOf N', (δ : N') * m ∈ A)
    (hB : ∀ n : N, ∃! γ : Γ.subgroupOf N, (γ : N) * n ∈ B) (z : N' × N) :
    ∃! p : pairs Γ hn, p • z ∈ (fun z : N' × N => (z.1, Subgroup.inclusion hle z.1 * z.2)) ⁻¹' (A⁻¹ ×ˢ B) := by
  let s : pairs Γ hn → pairs Γ hn := fun p => ⟨p.1.swap, p.2.2.1, p.2.1, by simpa using inv_mem p.2.2.2⟩
  have hs : ∀ p : pairs Γ hn, p • z ∈ (fun z : N' × N => (z.1, Subgroup.inclusion hle z.1 * z.2)) ⁻¹' (A⁻¹ ×ˢ B) ↔
      s p • (z.1⁻¹, Subgroup.inclusion hle z.1 * z.2) ∈ A ×ˢ B := fun p => by
    refine and_congr (Iff.of_eq (congrArg (· ∈ A) (Subtype.ext ?_))) (Iff.of_eq (congrArg (· ∈ B) (Subtype.ext ?_)))
    · simp [smul_fst, s, mul_assoc]
    · simp [smul_fst, smul_snd, s, mul_assoc]
  obtain ⟨p, hp, hp'⟩ := existsUnique_prod (hn := hn) hle hA hB (z.1⁻¹, Subgroup.inclusion hle z.1 * z.2)
  exact ⟨s p, (hs _).2 hp, fun q hq => congrArg s (hp' _ ((hs q).1 hq))⟩

end Alg

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ N N' : Subgroup G} [DiscreteTopology Γ] [LocallyCompactSpace N]
  [LocallyCompactSpace N']

theorem constTermOn_eq' {μ : Measure N} [μ.IsHaarMeasure] {𝓕 : Set N} (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ)
    {φ : G → ℂ} {x : G} (hφ : LeftInv (Γ.subgroupOf N) fun n : N => φ (n * x)) :
    constTermOn Γ N φ x = (μ.real 𝓕)⁻¹ • ∫ n in 𝓕, φ (n * x) ∂μ := by
  rw [constTermOn, probMeasure_eq μ, integral_smul_measure, quotMeasure_univ h, integral_quotMeasure h,
    ENNReal.toReal_inv, measureReal_def]
  exact congrArg _ (integral_congr_ae (.of_forall hφ.descend_mk))

theorem measurePreserving_conj (hc : Cocompact Γ N) (μ : Measure N) [μ.IsHaarMeasure] {γ : G} (hγ : γ ∈ Γ)
    (h1 : ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (h2 : ∀ n ∈ N, γ⁻¹ * n * γ⁻¹⁻¹ ∈ N) :
    MeasurePreserving (fun n : N => (⟨γ * n * γ⁻¹, h1 _ n.2⟩ : N)) μ μ := by
  let e : N ≃ₜ* N :=
    { toFun := fun n => ⟨γ * n * γ⁻¹, h1 _ n.2⟩
      invFun := fun n => ⟨γ⁻¹ * n * γ, by simpa using h2 _ n.2⟩
      left_inv := fun n => by simp [mul_assoc]
      right_inv := fun n => by simp [mul_assoc]
      map_mul' := fun a b => by simp [mul_assoc]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hm : Measurable e := e.continuous.measurable
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) μ
  have he := Measure.isMulLeftInvariant_eq_smul (μ.map e) μ
  have h' : IsFundamentalDomain (Γ.subgroupOf N) (e ⁻¹' stdDom (Γ.subgroupOf N)) μ :=
    h.preimage_of_equiv ⟨hm.aemeasurable, he ▸ Measure.smul_absolutelyContinuous⟩
      (e := fun δ => ⟨e.symm δ, mul_mem (mul_mem (inv_mem hγ) δ.2) hγ⟩)
      ⟨fun a b hab => Subtype.ext (e.symm.injective (congrArg Subtype.val hab)),
        fun δ => ⟨⟨e δ, mul_mem (mul_mem hγ δ.2) (inv_mem hγ)⟩, Subtype.ext (e.symm_apply_apply _)⟩⟩
      fun δ n => (map_mul e _ _).trans (congrArg (· * e n) (e.apply_symm_apply _))
  have h1 := h'.measure_eq h
  rw [← Measure.map_apply hm (measurableSet_stdDom _), he, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul, ENNReal.mul_eq_right (h.measure_ne_zero (NeZero.ne μ)) (hc.measure_ne_top h), ENNReal.coe_eq_one] at h1
  refine ⟨hm, ?_⟩
  change μ.map e = μ
  rw [he, h1, one_smul]

theorem integral_integral (hle : N' ≤ N) (hn : ∀ p ∈ N, ∀ n ∈ N', p * n * p⁻¹ ∈ N') (hc : Cocompact Γ N)
    (hc' : Cocompact Γ N') (μ : Measure N) [μ.IsHaarMeasure] (μ' : Measure N') [μ'.IsHaarMeasure]
    {φ : G → ℂ} (hφ : LeftInv Γ φ) (hφc : Continuous φ) (x : G) :
    ∫ n in stdDom (Γ.subgroupOf N), ∫ m in stdDom (Γ.subgroupOf N'), φ (m * (n * x)) ∂μ' ∂μ =
      μ'.real (stdDom (Γ.subgroupOf N'))⁻¹ • ∫ n in stdDom (Γ.subgroupOf N), φ (n * x) ∂μ := by
  have hp : ∀ p : pairs Γ hn, MeasurePreserving (fun z : N' × N => p • z) (μ'.prod μ) (μ'.prod μ) := fun p => by
    have := ((measurePreserving_mul_left μ' ⟨_, p.2.2.2⟩).comp (measurePreserving_conj hc' μ' p.2.2.1
      (hn _ p.1.2.2) (hn _ (inv_mem p.1.2.2)))).prod (measurePreserving_mul_left μ p.1.2)
    convert this using 1
    funext z
    exact Prod.ext (Subtype.ext (by simp [smul_fst, mul_assoc])) rfl
  have : MeasurableConstSMul (pairs Γ hn) (N' × N) := ⟨fun p => (hp p).measurable⟩
  have : SMulInvariantMeasure (pairs Γ hn) (N' × N) (μ'.prod μ) :=
    ⟨fun p s hs => (hp p).measure_preimage hs.nullMeasurableSet⟩
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : Countable (pairs Γ hn) :=
    Function.Injective.countable (f := fun p : pairs Γ hn => ((⟨_, p.2.1⟩, ⟨_, p.2.2.1⟩) : Γ × Γ)) fun p q h =>
      Subtype.ext (Prod.ext (Subtype.ext (congrArg (fun z : Γ × Γ => z.1.1) h))
        (Subtype.ext (congrArg (fun z : Γ × Γ => z.2.1) h)))
  have hA := measurableSet_stdDom (Γ.subgroupOf N')
  have hB := measurableSet_stdDom (Γ.subgroupOf N)
  have hi : Continuous (Subgroup.inclusion hle) := continuous_subtype_val.subtype_mk _
  have ht : MeasurePreserving (fun z : N' × N => (z.1, Subgroup.inclusion hle z.1 * z.2)) (μ'.prod μ) (μ'.prod μ) :=
    (MeasurePreserving.id μ').skew_product (g := fun m n => Subgroup.inclusion hle m * n)
      (Continuous.measurable (by fun_prop)) (.of_forall fun m => map_mul_left_eq_self μ _)
  have d1 := IsFundamentalDomain.mk' (μ := μ'.prod μ) (hA.prod hB).nullMeasurableSet
    (existsUnique_prod (hn := hn) hle (existsUnique_stdDom _) (existsUnique_stdDom _))
  have d2 := IsFundamentalDomain.mk' (μ := μ'.prod μ) (ht.measurable (hA.inv.prod hB)).nullMeasurableSet
    (existsUnique_shear (hn := hn) hle (existsUnique_stdDom _) (existsUnique_stdDom _))
  have e := d1.setIntegral_eq d2 (f := fun z : N' × N => φ (z.1 * (z.2 * x))) fun p z => by
    rw [smul_fst, smul_snd, ← hφ _ p.2.1 (z.1 * (z.2 * x))]
    simp [mul_assoc]
  have : IsFiniteMeasure (μ.restrict (stdDom (Γ.subgroupOf N))) :=
    isFiniteMeasure_restrict.2 (hc.measure_ne_top (isFundamentalDomain_stdDom _ _))
  have : IsFiniteMeasure (μ'.restrict (stdDom (Γ.subgroupOf N'))) :=
    isFiniteMeasure_restrict.2 (hc'.measure_ne_top (isFundamentalDomain_stdDom _ _))
  obtain ⟨K, hK, hs⟩ := id hc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun n : N => φ (n * x)) (by fun_prop)
  have hb : ∀ n : N, ‖φ (n * x)‖ ≤ C := fun n =>
    let ⟨γ, hγ, hk⟩ := hs n
    (congrArg norm (leftInv_integrand hφ x γ hγ n)).ge.trans (hC _ hk)
  rw [← Measure.prod_restrict, integral_prod_symm _ (.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) C
    (.of_forall fun z => by simpa [mul_assoc] using hb (Subgroup.inclusion hle z.1 * z.2)))] at e
  have e2 := integral_map (f := fun z : N' × N => φ (z.2 * x))
    (ht.restrict_preimage (hA.inv.prod hB)).aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))
  rw [(ht.restrict_preimage (hA.inv.prod hB)).map_eq, ← Measure.prod_restrict,
    integral_fun_snd (fun n : N => φ (n * x)), measureReal_restrict_apply_univ] at e2
  rw [e, e2]
  simp [mul_assoc]

theorem constTermOn_stages (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (Γ N N' : Subgroup G) [DiscreteTopology Γ] [LocallyCompactSpace N] [LocallyCompactSpace N'] (hle : N' ≤ N)
    (hn : ∀ p ∈ N, ∀ n ∈ N', p * n * p⁻¹ ∈ N') (hc : Cocompact Γ N) (hc' : Cocompact Γ N') (φ : G → ℂ)
    (hφ : LeftInv Γ φ) (hφc : Continuous φ) (x : G) :
    constTermOn Γ N φ x = constTermOn Γ N (constTermOn Γ N' φ) x := by
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) Measure.haar
  have h' := isFundamentalDomain_stdDom (Γ.subgroupOf N') Measure.haar
  have h0 := ENNReal.toReal_ne_zero.2 ⟨h.measure_ne_zero (NeZero.ne _), hc.measure_ne_top h⟩
  have h0' := ENNReal.toReal_ne_zero.2 ⟨h'.measure_ne_zero (NeZero.ne _), hc'.measure_ne_top h'⟩
  rw [← measureReal_def] at h0 h0'
  have e1 := integral_integral hle hn hc hc' Measure.haar Measure.haar (φ := fun _ => 1) (fun _ _ _ => rfl)
    continuous_const x
  have e2 : Measure.haar.real (stdDom (Γ.subgroupOf N'))⁻¹ = Measure.haar.real (stdDom (Γ.subgroupOf N')) := by
    simp only [integral_const, measureReal_restrict_apply_univ, smul_smul] at e1
    have := smul_left_injective ℝ (one_ne_zero (α := ℂ)) e1
    rw [mul_comm] at this
    exact (mul_right_cancel₀ h0 this).symm
  rw [constTermOn_eq h hφ, constTermOn_eq' h fun γ hγ n => by
    simp only [Subgroup.coe_mul, mul_assoc]
    exact constTermOn_mul_left_of_normalizer hφ hγ
      (fun m => ⟨hn _ γ.2 m, fun hm => by simpa [mul_assoc] using hn _ (inv_mem γ.2) _ hm⟩) _]
  simp only [constTermOn_eq h' hφ]
  rw [integral_smul, integral_integral hle hn hc hc' _ _ hφ hφc, e2, inv_smul_smul₀ h0']

end GlobalTheory.Cusp.Stages

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtLinearIndependent
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues (IsCoefExt RationalValues RationalValuesAt ValuesIn)
open GlobalTheory.Proof.PlaceExtensionValues

namespace GlobalTheory.RationalValuesObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coef

variable {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} {ι : K →+* K'}
  {I : Type} [Fintype I] {n : ℕ} {lam : I → DomWeight n} {W : Type} [AddCommGroup W] [Module ℂ W]
  {c₀ : VV K lam →ₛₗ[σ] W} {c' c'' : VV K' lam →ₛₗ[σ'] W}

theorem exists_basis_val (lam : I → DomWeight n) (ι : K →+* K') (j : VVIdx lam) :
    ∃ v : VV K lam, ((bVV K' lam j : VV K' lam) : Pol K' I n) = MvPolynomial.map ι (v : Pol K I n) := by
  obtain ⟨F, hF, hj⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc ι lam j
  exact ⟨⟨F, hF⟩, (bVV_coe _ _ _).trans hj⟩

theorem ext_unique (h : IsCoefExt ι lam c₀ c') (h' : IsCoefExt ι lam c₀ c'') : c' = c'' := by
  refine (bVV K' lam).ext fun j => ?_
  obtain ⟨v, hv⟩ := exists_basis_val lam ι j
  rw [h v _ hv, h' v _ hv]

end Coef

section Row

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem existsUnique_c0BC (i : Fin D.R.m) {K' : Type} [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ)
    (hσ : σ'.comp jL = D.what₂.embLL) (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) :
    ∃! c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, CoefficientBaseChange R i jL σ' c₀ c' := by
  obtain ⟨c', hc⟩ := GlobalTheory.Mem.PlaceVal.exists_ext_VV (W := (R.cV i).W) jL σ' hσ (FWT.lamV D i) c₀
  exact ⟨c', hc, fun c'' hc'' => ext_unique ((isCoefExt_iff_c0BC R i jL c₀ c'').2 hc'') ((isCoefExt_iff_c0BC R i jL c₀ c').2 hc)⟩

end Row

end GlobalTheory.RationalValuesObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WittIndexAddOfIsWittLower
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp)
open Module

namespace GlobalTheory.Cusp.WittIdx

section Lin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : Formalism.BasicNotions.HSpace E}

theorem mem_perp' {W : Submodule E V.V} {y : V.V} : y ∈ perp V W ↔ ∀ x ∈ W, V.hT x y = 0 := by
  simp only [perp, Submodule.mem_iInf, LinearMap.mem_ker]

private theorem perp_eq_ker_pi_hT_finBasis (A : Submodule E V.V) :
    perp V A = LinearMap.ker (LinearMap.pi fun k : Fin (finrank E A) =>
      V.hT ((Module.finBasis E A k : A) : V.V)) := by
  ext y
  rw [mem_perp', LinearMap.mem_ker]
  constructor
  · intro h
    funext k
    simpa using h _ (Module.finBasis E A k).2
  · intro h x hx
    have hk : ∀ k, V.hT ((Module.finBasis E A k : A) : V.V) y = 0 := fun k => by
      simpa using congrFun h k
    have hx' : x = ∑ k, (Module.finBasis E A).repr ⟨x, hx⟩ k • ((Module.finBasis E A k : A) : V.V) := by
      have e := congrArg A.subtype ((Module.finBasis E A).sum_repr ⟨x, hx⟩)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Submodule.subtype_apply] at e
      exact e.symm
    rw [hx']
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hk]

private theorem pi_hT_finBasis_range_surjective (A : Submodule E V.V) :
    LinearMap.range (LinearMap.pi fun k : Fin (finrank E A) =>
      V.hT ((Module.finBasis E A k : A) : V.V)) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ, hle⟩ := (LinearMap.range (LinearMap.pi fun k : Fin (finrank E A) =>
      V.hT ((Module.finBasis E A k : A) : V.V))).exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
  have hw : ∀ y, V.hT (∑ k, star (φ fun j => if k = j then (1 : E) else 0) •
      ((Module.finBasis E A k : A) : V.V)) y = 0 := by
    intro y
    have h1 := hle ⟨y, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at h1
    simp only [LinearMap.pi_apply, smul_eq_mul] at h1
    have h2 : ∑ k, (φ fun j => if k = j then (1 : E) else 0) *
        V.hT ((Module.finBasis E A k : A) : V.V) y = 0 := by
      calc _ = ∑ k, V.hT ((Module.finBasis E A k : A) : V.V) y *
            (φ fun j => if k = j then (1 : E) else 0) := Finset.sum_congr rfl fun k _ => mul_comm _ _
        _ = 0 := h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
    exact h2
  have h0 := V.nondeg.1 _ hw
  have h0' : ∑ k, star (φ fun j => if k = j then (1 : E) else 0) • Module.finBasis E A k = 0 := by
    apply Subtype.ext
    simpa using h0
  have hc : ∀ k, φ (fun j => if k = j then (1 : E) else 0) = 0 := fun k => by
    have := Fintype.linearIndependent_iff.1 (Module.finBasis E A).linearIndependent _ h0' k
    simpa using this
  apply hφ
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp [hc]

theorem finrank_add_finrank_perp (A : Submodule E V.V) : finrank E A + finrank E (perp V A) = V.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun k : Fin (finrank E A) =>
      V.hT ((Module.finBasis E A k : A) : V.V))
  rw [pi_hT_finBasis_range_surjective, finrank_top, Module.finrank_fin_fun, ← perp_eq_ker_pi_hT_finBasis, V.rank_eq] at h
  exact h

end Lin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.Cusp.WittIdx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCompactKinfAndConj
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Cusp.KinfCompact

section Mat

variable {p q n : ℕ} {A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ} {B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ}
  {G m : Matrix (Fin n) (Fin n) ℂ}

end Mat

variable {D : D7}

theorem isClosed_realPts (V : HSp D) : IsClosed (GinfC V : Set (GA D V)) := by
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  have : T2Space (Af D.host.F ⊗[D.host.F] D.host.E) := e.isEmbedding.t2Space
  have h : (GinfC V : Set (GA D V)) = {g | (finHom V g).1 = 1} := by
    ext g
    exact Units.ext_iff
  rw [h]
  exact isClosed_eq (GlobalTheory.Member.continuous_finHom_val D V) continuous_const

theorem continuous_realMat {θ : InfF D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    Continuous fun h => infMat D.sp.cm.sig V.gram (θ τ) h := by
  obtain ⟨θ₀, hθ₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  have e : θ τ = θ₀ (tauE D τ) := SmoothForms.RealPts.infEmb_unique _ _ _ (hθ τ) (hθ₀ _)
  rw [e]
  exact ((GlobalTheory.Member.Arch.archM_spec D V θ₀ hθ₀).1 (tauE D τ)).2.2.2.1

end GlobalTheory.Cusp.KinfCompact

end
end
