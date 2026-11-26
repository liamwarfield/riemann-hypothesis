module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.StandardHermitianSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefClassDecompIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryMassLatticeEqGenusMass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
open MeasureTheory GlobalTheory.AutomorphicL2Unitary
open scoped Pointwise Topology

namespace GlobalTheory.AutomorphicL2Local

theorem continuous_integral_inv_mul_of_locallyIntegrable {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] {μ : Measure G} {f φ : G → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hφ : LocallyIntegrable φ μ) :
    (∀ x, Integrable (fun y => f (x⁻¹ * y) * φ y) μ) ∧ Continuous fun x => ∫ y, f (x⁻¹ * y) * φ y ∂μ := by
  have hi : ∀ x, Integrable (fun y => f (x⁻¹ * y) * φ y) μ := fun x =>
    hφ.integrable_smul_left_of_hasCompactSupport (g := fun y => f (x⁻¹ * y)) (by fun_prop)
      (hc.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  refine ⟨hi, continuous_iff_continuousAt.2 fun x₀ => ?_⟩
  obtain ⟨U, hU, hx⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hc
  have hK : IsCompact (U * tsupport f) := hU.mul hc.isCompact
  refine continuousAt_of_dominated (bound := (U * tsupport f).indicator fun y => M * ‖φ y‖)
    (.of_forall fun x => (hi x).1) ?_ ?_ (.of_forall fun y => ?_)
  · filter_upwards [hx] with x hxU
    refine .of_forall fun y => ?_
    by_cases hy : y ∈ U * tsupport f
    · rw [Set.indicator_of_mem hy, norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hy,
        image_eq_zero_of_notMem_tsupport (f := f) fun h => hy ⟨x, hxU, _, h, by simp⟩]
      simp
  · exact (integrable_indicator_iff hK.measurableSet).2 ((hφ.integrableOn_isCompact hK).norm.const_mul M)
  · exact Continuous.continuousAt (by fun_prop)

theorem continuous_convR_lift : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f : G → ℂ, Continuous f → HasCompactSupport f → ∀ F : L2 Γ μ, (∀ x, Integrable (fun y => f y * lift Γ F (x * y)) μ) ∧ Continuous (convR μ f (lift Γ F)) := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ f hf hc F
  have hφ : LocallyIntegrable (lift Γ F) μ :=
    locallyIntegrable_iff.2 fun C hC => (memLp_restrict_compact G Γ μ F C hC).2
  obtain ⟨h1, h2⟩ := continuous_integral_inv_mul_of_locallyIntegrable hf hc hφ
  refine ⟨fun x => ?_, h2.congr fun x => (convR_eq f _ x).symm⟩
  simpa using (h1 x).comp_mul_left x

end GlobalTheory.AutomorphicL2Local
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
noncomputable section

namespace GlobalTheory.Equiv.StdSpace

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem coe_pi_one_eq_intVecs (n : ℕ) :
    ((Submodule.pi Set.univ (fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)) :
      Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.intVecs D n := by
  ext x
  rw [SetLike.mem_coe, Submodule.mem_pi]
  exact ⟨fun k a => Submodule.mem_one.1 (k a trivial), fun k a _ => Submodule.mem_one.2 (k a)⟩

theorem identityClassLattice_eq_selfDualFrameLattice (V : HSp D) : (Bridge.hLat V 1 : Set (Fin V.rank → D.host.E)) = L0c D V := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ hfg hsp).1
  rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, SetLike.coe_set_eq]
  unfold Bridge.hLat
  rw [← Submodule.span_eq (GlobalTheory.Member.latC V)]
  congr 1
  ext x
  rw [SetLike.mem_coe, ← key x, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq,
    show ((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) = 1 from Subtype.ext inv_one]
  show (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ _ ∈
    Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ _
  rw [Matrix.one_mulVec]
  exact Iff.rfl

theorem lattice_clause_iff (V : HSp D) :
    (Bridge.hLat V 1 = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)) ↔
      L0c D V = GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.intVecs D V.rank := by
  rw [← identityClassLattice_eq_selfDualFrameLattice, ← coe_pi_one_eq_intVecs, SetLike.coe_set_eq]

end GlobalTheory.Equiv.StdSpace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReframeVStdOfPosDef
noncomputable section

namespace GlobalTheory.StdFrame

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.FWT
open scoped TensorProduct Matrix

section Space

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def OrthFrame (V : HSpace E) : Prop :=
  (∀ a b, V.hT (V.frame a) (V.frame b) = if a = b then 1 else 0) ∧ ∀ a, V.frame a ∈ V.L0

theorem OrthFrame.gram_eq {V : HSpace E} (h : OrthFrame V) : V.gram = 1 := by
  ext a b
  rw [Matrix.one_apply]
  exact h.1 a b

theorem OrthFrame.mem_iff {V : HSpace E} (h : OrthFrame V) (x : Fin V.rank → E) :
    ∑ a, x a • V.frame a ∈ V.L0 ↔ ∀ a, x a ∈ (1 : Submodule (𝓞 E) E) := by
  constructor
  · intro hx a
    have hd : ∑ a, x a • V.frame a ∈ Formalism.HermitianLatticesTheory.dual V.hT V.L0 := by
      rw [V.baseLattice_isUnimodular]; exact hx
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hd
    have h1 : V.hT (V.frame a) (∑ b, x b • V.frame b) ∈ (1 : Submodule (𝓞 E) E) := hd _ (h.2 a)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, map_smul, h.1] using h1
  · intro hx
    refine Submodule.sum_mem _ fun a _ => ?_
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hx a)
    rw [← ho, algebraMap_smul]
    exact V.L0.smul_mem o (h.2 a)

def reframe (V : HSpace E) (b : Module.Basis (Fin V.rank) E V.V) : HSpace E := { V with frame := b }

theorem exists_orthFrame (V : HSpace E) {n : ℕ} (hn : V.rank = n) (h : Formalism.HermitianLatticesTheory.IsOrthoLattice V.hT V.L0 n) :
    ∃ b, OrthFrame (reframe V b) := by
  subst hn
  obtain ⟨e, h1, h2, h3, h4⟩ := h
  refine ⟨Module.Basis.mk h1 h2.ge, fun (a b : Fin V.rank) => ?_, fun (a : Fin V.rank) => ?_⟩
  · show V.hT (Module.Basis.mk h1 h2.ge a) (Module.Basis.mk h1 h2.ge b) = _
    rw [Module.Basis.mk_apply, Module.Basis.mk_apply, h4]
    rfl
  · show Module.Basis.mk h1 h2.ge a ∈ V.L0
    rw [Module.Basis.mk_apply, h3]
    exact Submodule.subset_span ⟨a, rfl⟩

end Space

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hLat_one {D : D7} (V : HSp D) : Bridge.hLat V 1 = GlobalTheory.Member.latC V := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ hfg hsp).1
  unfold Bridge.hLat
  rw [← Submodule.span_eq (GlobalTheory.Member.latC V)]
  congr 1
  ext x
  rw [SetLike.mem_coe, ← key x, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq,
    show ((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) = 1 from Subtype.ext inv_one]
  show (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ _ ∈
    Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ _
  rw [Matrix.one_mulVec]
  exact Iff.rfl

theorem vStd_iff_gram_and_lattice (D : D7) (i : Fin D.R.m) :
    VStd D i ↔ (Vc D i).gram = 1 ∧
      L0c D (Vc D i) = ((Submodule.pi Set.univ (fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)) :
        Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) : Set (Fin (Vc D i).rank → D.host.E)) := by
  rw [VStd, hLat_one, ← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, SetLike.coe_set_eq]

def FrameChoice (D : D7) (i : Fin D.R.m) : Prop := OrthFrame (D.sp.V ((i : ℕ) + 1))

theorem vStd_of_frameChoice : ∀ (D : D7) (i : Fin D.R.m), FrameChoice D i → VStd D i := by
  intro D i h
  refine (vStd_iff_gram_and_lattice D i).2 ⟨h.gram_eq, ?_⟩
  ext x
  rw [SetLike.mem_coe, Submodule.mem_pi]
  exact (h.mem_iff x).trans ⟨fun k a _ => k a, fun k a => k a trivial⟩

theorem nV_pos (R : Ranks) : 0 < R.nV := by
  have := R.rank_add_five_le
  unfold Ranks.nV
  omega

theorem neg_eq_false_of_vStd (D : D7) (i : Fin D.R.m) (h : VStd D i) : D.sp.Vneg ((i : ℕ) + 1) = false := by
  by_contra hneg
  rw [Bool.not_eq_false] at hneg
  let τ := D.host.φ₀
  have hs := D.sp.V_sig ((i : ℕ) + 1) τ
  rw [factVSig _ _ D.sp _ (by omega) (by omega) τ, if_pos hneg] at hs
  have h1 : Formalism.UG.HasSignature ((Matrix.of fun a b => (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b)).map τ)
      (Vc D i).rank 0 := by
    have h0 : (Matrix.of fun a b => (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b)) = 1 := h.1
    rw [h0, Matrix.map_one _ (map_zero _) (map_one _)]
    simpa using Formalism.UG.P.stdform_sig_one (n := Fin (Vc D i).rank)
  have h2 := (sig_family (Vc D i) τ (D.sp.cm.cmUnram.2.1 τ) _ h1 hs).1
  have := nV_pos D.R
  simp only at h2
  omega

theorem neg_eq_false_of_posDef (D : D7) (i : Fin D.R.m) (h : (Vc D i).IsPosDef) :
    D.sp.Vneg ((i : ℕ) + 1) = false := by
  by_contra hneg
  rw [Bool.not_eq_false] at hneg
  have h1 := factVSig _ _ D.sp ((i : ℕ) + 1) (by omega) (by omega) D.host.φ₀
  rw [if_pos hneg] at h1
  have h2 := congrArg Prod.snd ((h D.host.φ₀).symm.trans h1)
  exact (nV_pos D.R).ne h2

end GlobalTheory.StdFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoubleCosetsMassLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAndMass
noncomputable section

namespace GlobalTheory.DefiniteDecomp

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LevelSubgroupStabilizers GlobalTheory.Mass NumberField
open scoped TensorProduct Matrix

theorem exists_reps {G : Type} [Group G] {Γ K : Subgroup G} (h : FiniteClasses Γ K) :
    ∃ (n : ℕ) (g : Fin n → G), (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g i * k) ∧
      (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j) ∧
      (∀ i, (Unfold.stab Γ K (g i)).Finite) ∧
      ∑ i, ((Nat.card (Unfold.stab Γ K (g i)) : ℝ))⁻¹ = classMass Γ K := by
  haveI := h.1
  obtain ⟨n, ⟨φ⟩⟩ := Finite.exists_equiv_fin (Formalism.UG.ClassSet Γ K)
  have e : ∀ g, Unfold.stab Γ K g = Formalism.UG.stabAt Γ K g := fun g => by
    ext γ; simp only [Unfold.stab, Formalism.UG.stabAt, mul_assoc]
  refine ⟨n, fun i => (φ.symm i).out, fun x => ?_, fun i j γ γ' k k' e => ?_, fun i => ?_, ?_⟩
  · obtain ⟨γ, hγ, k, hk, e⟩ := (@DoubleCoset.eq _ _ Γ K _ x).1 (DoubleCoset.out_eq' (DoubleCoset.mk Γ K x))
    refine ⟨φ (DoubleCoset.mk Γ K x), ⟨γ, hγ⟩, ⟨k, hk⟩, ?_⟩
    exact e.trans (congrArg (fun c : Formalism.UG.ClassSet Γ K => γ * c.out * k) (φ.symm_apply_apply _).symm)
  · apply φ.symm.injective
    rw [← DoubleCoset.out_eq' (φ.symm i), ← DoubleCoset.out_eq' (φ.symm j)]
    refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨(γ'⁻¹ * γ : Γ), (γ'⁻¹ * γ).2, (k * k'⁻¹ : K), (k * k'⁻¹).2, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_assoc, mul_assoc, ← mul_assoc (γ : G), ← mul_assoc, ← mul_assoc,
      mul_assoc _ _ (k : G), e]
    simp [mul_assoc]
  · rw [e]
    exact h.2 _
  · rw [classMass_eq_sum_of_bijective (fun i => (φ.symm i).out)]
    · simp only [e]
    · simp only [DoubleCoset.out_eq']
      exact φ.symm.bijective

section Level

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem levelK_eq {π : HA (AF F) σ J →* HA (Af F) σ J} (hπ : IsFinProj σ J π)
    (Λ : Submodule (𝓞 E) (Fin M → E)) :
    levelK σ J (Λ : Set (Fin M → E)) =
      ((((Formalism.UG.levelAfL σ J Λ).subgroupOf (Formalism.UG.UPts σ J (Af F))).comap
        (swapPts (Af F) σ J : HA (Af F) σ J →* Formalism.UG.UPts σ J (Af F))).comap π) := by
  ext g
  have h1 : g ∈ ((((Formalism.UG.levelAfL σ J Λ).subgroupOf (Formalism.UG.UPts σ J (Af F))).comap
        (swapPts (Af F) σ J : HA (Af F) σ J →* Formalism.UG.UPts σ J (Af F))).comap π) ↔
      (swapPts (Af F) σ J (π g) : GL (Fin M) (E ⊗[F] Af F)) ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := F) Λ) :=
    ⟨fun h => h.2, fun h => ⟨(swapPts (Af F) σ J (π g)).2, h⟩⟩
  rw [h1, coe_swapPts, hπ g]
  have h2 : ∀ y : Fin M → Af F ⊗[F] E, (fun i => GlobalTheory.LevSplit.swp F E ((finMat σ J g *ᵥ y) i)) =
      (finMat σ J g).map (GlobalTheory.LevSplit.swp F E) *ᵥ fun i => GlobalTheory.LevSplit.swp F E (y i) :=
    fun y => funext fun i => RingHom.map_mulVec _ _ _ i
  change (∀ y, y ∈ latHat F E (Λ : Set (Fin M → E)) ↔ finMat σ J g *ᵥ y ∈ latHat F E (Λ : Set (Fin M → E))) ↔
    ∀ x, x ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔
      (finMat σ J g).map (GlobalTheory.LevSplit.swp F E) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Λ
  simp only [GlobalTheory.LevSplit.latHat_iff, h2]
  refine ⟨fun h x => ?_, fun h y => h _⟩
  choose y hy using fun i => (GlobalTheory.LevSplit.swp_bij (F := F) (E := E)).2 (x i)
  have := h y
  simpa only [hy] using this

end Level

section Space

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [inst : StarRing E] [Algebra F E]

theorem standardLattice_span_eq_top (W : HSpace E) :
  Submodule.span E (W.L0 : Set W.V) = ⊤ := by
  let U := Submodule.span E (W.L0 : Set W.V)
  change U = ⊤
  by_contra h
  let e : W.V ≃ₗ⋆[E] W.V :=
    (W.frame.equivFun.trans (starLinearEquiv E)).trans W.frame.equivFun.symm
  let g : W.V →ₗ[E] Module.Dual E U :=
    (LinearMap.domRestrict' U).comp (W.hT.comp e.toLinearMap)
  have hdim : Module.finrank E (Module.Dual E U) < Module.finrank E W.V := by
    rw [Subspace.dual_finrank_eq]
    exact Submodule.finrank_lt h
  obtain ⟨x, hx, hx₀⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
  have hsmul (a : E) : a • e x ∈ W.L0 := by
    rw [← W.baseLattice_isUnimodular, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro y hy
    have hxy : W.hT (e x) y = 0 :=
      congrArg (fun f : Module.Dual E U => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
    have hyx : W.hT y (e x) = 0 := by
      rw [← W.herm.eq, hxy, map_zero]
    simp [hyx]
  let i : E →ₗ[𝓞 E] W.L0 :=
    ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict W.L0 hsmul
  let : Module.Finite (𝓞 E) W.L0 := Module.Finite.iff_fg.mpr W.standardTuple_isLattice.fg
  let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
    smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
  exact RingOfIntegers.not_isField E
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))

theorem mass_coord (hc : CMData F E) (W : HSpace E) (hW : W.SigOK) (hs : ∀ τ, W.sig τ = (W.rank, 0))
    (hσ : ∀ e, (hc.sig : E →+* E) ((hc.sig : E →+* E) e) = e) :
    (letI := Formalism.UG.CS.starOfInv (hc.sig : E →+* E) hσ
    Formalism.HermitianLatticesTheory.mass (Formalism.UG.CS.formJ (hc.sig : E →+* E) hσ W.gram 1) (tMap (Formalism.L2.Herm.crd W) W.L0)) =
      Formalism.HermitianLatticesTheory.mass W.hT W.L0 := by
  let h' : (Fin W.rank → E) →ₗ⋆[E] (Fin W.rank → E) →ₗ[E] E :=
    Matrix.toLinearMapₛₗ₂' E (starRingEnd E) (RingHom.id E) ((1 : E) • W.gram)
  change Formalism.HermitianLatticesTheory.mass h' (tMap (Formalism.L2.Herm.crd W) W.L0) = _
  have he : ∀ x y, h' (Formalism.L2.Herm.crd W x) (Formalism.L2.Herm.crd W y) = W.hT x y := fun x y => by
    rw [Formalism.L2.Herm.hT_crd hc]
    simp only [h', one_smul, Matrix.toLinearMapₛₗ₂'_apply, Formalism.UG.hform, RingHom.id_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change star _ * _ = star _ * _ * _
    ring
  obtain ⟨h1, h2, -⟩ := Formalism.HermitianLatticesTheory.massBasic _ _ W.hT W.herm
    (GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.trace_pos hc.cmUnram.2.1 W hW hs) W.L0
    (by
      letI := W.standardTuple_isLattice
      exact { span_eq_top := standardLattice_span_eq_top W })
  have h3 := mass_transport (Formalism.L2.Herm.crd W).symm (isoSymm _ he) (tMap (Formalism.L2.Herm.crd W) W.L0)
    (by rwa [tMap_symm]) (by rwa [tMap_symm])
  rwa [tMap_symm] at h3

theorem coe_tMap (W : HSpace E) : (tMap (Formalism.L2.Herm.crd W) W.L0 : Set (Fin W.rank → E)) = latCoord W := by
  ext x
  rw [SetLike.mem_coe, mem_tMap]
  change W.frame.equivFun.symm x ∈ W.L0 ↔ _
  rw [Module.Basis.equivFun_symm_apply]
  rfl

theorem finite_and_mass (hc : CMData F E) (W : HSpace E) (hW : W.SigOK) (hs : ∀ τ, W.sig τ = (W.rank, 0))
    (hJ : IsHermND hc.sig W.gram) (hd : Formalism.UG.IsTotDef hc.sig W.gram) :
    FiniteClasses (ratIn (AF F) hc.sig W.gram) (levelW hc W) ∧
      classMass (ratIn (AF F) hc.sig W.gram) (levelW hc W) = Formalism.HermitianLatticesTheory.mass W.hT W.L0 := by
  have hσ : IsCMExt F E hc.sig := ⟨hc.totReal, hc.cmUnram.1, hc.deg2, hc.cmUnram.2.1⟩
  have hL := tMap_lattice (Formalism.L2.Herm.crd W) W.L0 W.standardTuple_isLattice
  have hf : Module.Finite (𝓞 E) (tMap (Formalism.L2.Herm.crd W) W.L0) := Module.Finite.iff_fg.2 hL.fg
  have hsp0 := standardLattice_span_eq_top W
  have hsp : Submodule.span E (tMap (Formalism.L2.Herm.crd W) W.L0 : Set (Fin W.rank → E)) = ⊤ := by
    have h := congrArg (Submodule.map (Formalism.L2.Herm.crd W : W.V →ₗ[E] (Fin W.rank → E))) hsp0
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h
    exact h
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj hc.sig W.gram
  rw [levelW, ← coe_tMap, levelK_eq hπ]
  constructor
  · rw [finiteClasses_comap π _ _ hπ.surjective hπ.injOn, hπ.map_ratIn]
    exact finiteClasses_lattice hσ hJ hd _ hf hsp
  · have hi : ∀ e, (hc.sig : E →+* E) ((hc.sig : E →+* E) e) = e := fun e => star_star e
    rw [← hπ.unitaryMass_eq, unitaryMass_lattice_eq_genus_mass hσ hJ hd hi _ hf hsp]
    exact mass_coord hc W hW hs hi

end Space

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem defClassDecomp : ∀ D : D7, DefClassDecomp D := by
  intro D W hW hs θ hθ A hA
  rw [GlobalTheory.DecompCompare.KSub_eq D W hW hs θ hθ A hA]
  have hd : Formalism.UG.IsTotDef D.sp.cm.sig W.gram := GlobalTheory.DefiniteQuotient.isTotDef_of_posDef W fun τ => by
    have := hW (Formalism.BasicNotions.TH.tauE D τ)
    rw [hs] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  obtain ⟨h1, h2⟩ := finite_and_mass D.sp.cm W hW hs (GlobalTheory.DefiniteQuotient.gram_hermND W) hd
  haveI := Unfold.borelHA D.sp.cm.sig W.gram
  refine ⟨(GlobalTheory.DecompCompare.isOpen_levelW D W).measurableSet, ?_⟩
  rw [← h2]
  exact exists_reps h1

end GlobalTheory.DefiniteDecomp
end
end

namespace GlobalTheory.DefiniteDecompObj

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

theorem doubleCosets_mass : ∀ D : D7, DefClassDecomp D :=
  GlobalTheory.DefiniteDecomp.defClassDecomp

end GlobalTheory.DefiniteDecompObj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableDescendOrbitSum
open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.AutomorphicL2KernelIntegral

theorem integrable_descend_orbitSum {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {μ : Measure G} [μ.IsMulLeftInvariant] {h : G → ℂ} (hh : Integrable h μ) :
    Integrable (descend Γ (orbitSum Γ h)) (AutomorphicL2Unitary.quotMeasure Γ μ) := by
  refine ⟨?_, ?_⟩
  · rw [aestronglyMeasurable_quotMeasure_iff_lift, (leftInv_orbitSum h).lift_descend]
    have hm : ∀ γ : Γ, AEMeasurable (fun x => h (γ * x)) μ := fun γ =>
      hh.1.aemeasurable.comp_quasiMeasurePreserving (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving
    exact (AEMeasurable.tsum hm).aestronglyMeasurable
  · have h1 := lintegral_eq_lintegral_tsum (Γ := Γ) hh.1.enorm
    refine lt_of_le_of_lt ?_ (h1.symm.trans_lt hh.2)
    exact lintegral_mono fun q => enorm_tsum_le_tsum_enorm

theorem convR_eq_integral_kernelQ : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    ∀ f : G → ℂ, Continuous f → HasCompactSupport f → ∀ (F : L2 Γ μ) (x : G),
      Integrable (fun q => kernelQ Γ f (mk Γ x) q * F q) (AutomorphicL2Unitary.quotMeasure Γ μ) ∧
        convR μ f (lift Γ F) x = ∫ q, kernelQ Γ f (mk Γ x) q * F q ∂AutomorphicL2Unitary.quotMeasure Γ μ := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ f hf hc F x
  have hf' : Continuous fun y => f (x⁻¹ * y) := hf.comp (continuous_const_mul _)
  have hc' : HasCompactSupport fun y => f (x⁻¹ * y) := hc.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
  have hloc : LocallyIntegrable (lift Γ F) μ :=
    (locallyIntegrable_iff).2 fun C hC => (GlobalTheory.T.memLp_lift_L2DiscreteQuotient_on_compact G Γ μ F C hC).2
  have hi : Integrable (fun y => f (x⁻¹ * y) * lift Γ F y) μ :=
    hloc.integrable_smul_left_of_hasCompactSupport hf' hc'
  have key : descend Γ (orbitSum Γ fun y => f (x⁻¹ * y) * lift Γ F y) =
      fun q => kernelQ Γ f (mk Γ x) q * F q := by
    funext q
    induction q using Quotient.inductionOn with
    | h y =>
      refine ((leftInv_orbitSum _).descend_mk y).trans ?_
      change _ = kernelQ Γ f (mk Γ x) (mk Γ y) * F (mk Γ y)
      rw [kernelQ_mk, kernel_eq_orbitSum, orbitSum, orbitSum, ← tsum_mul_right]
      exact tsum_congr fun γ => congrArg (fun z => _ * F z) (mk_mul γ y)
  refine ⟨key ▸ integrable_descend_orbitSum hi, ?_⟩
  rw [convR_eq, integral_eq_integral_orbitSum (Γ := Γ) hi, key]

end GlobalTheory.AutomorphicL2KernelIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupMulClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupMulClosed
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_mul_int_left (χ : kˣ →* ℂˣ) {x y : k} (hx : valuation k x ≤ 1) (hy : Triv χ y) :
    Triv χ (x * y) :=
  triv_mono χ y (x * y) (by rw [map_mul]; exact mul_le_of_le_one_left' hx) hy

theorem triv_mul_int_right (χ : kˣ →* ℂˣ) {x y : k} (hy : valuation k y ≤ 1) (hx : Triv χ x) :
    Triv χ (x * y) := by
  rw [mul_comm]; exact triv_mul_int_left χ hy hx

theorem grp_mul {n : ℕ} (ψ : Fin n → kˣ →* ℂˣ) (hψ : Ordered ψ) {a b : GL (Fin n) k}
    (ha : a ∈ grp ψ) (hb : b ∈ grp ψ) : a * b ∈ grp ψ := by
  refine ⟨(KO k (Fin n)).mul_mem ha.1 hb.1, fun i j hij => ?_⟩
  rw [Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_induction _ (fun x => Triv (ψ i / ψ j) x) (fun x y hx hy => triv_add _ x y hx hy)
    (triv_zero _) (fun l _ => ?_)
  rcases le_or_gt l i with hli | hil
  ·
    have h1 : Triv (ψ l / ψ j) (b.val l j) := hb.2 l j (lt_of_le_of_lt hli hij)
    have h2 : Triv (ψ i / ψ j) (b.val l j) := hψ l i j j hli hij.le le_rfl _ h1
    exact triv_mul_int_left _ (GlobalTheory.BlockType.val_le_one_of_mem_KO ha.1 i l) h2
  · rcases lt_or_ge l j with hlj | hjl
    · have h1 : Triv (ψ i / ψ l) (a.val i l * b.val l j) :=
        triv_mul_int_right _ (GlobalTheory.BlockType.val_le_one_of_mem_KO hb.1 l j) (ha.2 i l hil)
      have h2 : Triv (ψ l / ψ j) (a.val i l * b.val l j) :=
        triv_mul_int_left _ (GlobalTheory.BlockType.val_le_one_of_mem_KO ha.1 i l) (hb.2 l j hlj)
      have h3 := triv_mul _ _ _ h1 h2
      rwa [div_mul_div_cancel] at h3
    · have h1 : Triv (ψ i / ψ l) (a.val i l) := ha.2 i l hil
      have h2 : Triv (ψ i / ψ j) (a.val i l) := hψ i i j l le_rfl hij.le hjl _ h1
      exact triv_mul_int_right _ (GlobalTheory.BlockType.val_le_one_of_mem_KO hb.1 l j) h2

theorem grp_mul_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, a * b ∈ grp ψ :=
  fun _ _ _ _ _ _ ψ hψ _ ha _ hb => grp_mul ψ hψ ha hb

end GlobalTheory.PsType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupMulClosedStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesCongruenceSubgroup_mul_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, a * b ∈ grp ψ := by
  first | exact @GlobalTheory.PsType.grp_mul_closed | exact GlobalTheory.PsType.grp_mul_closed | (intros; apply GlobalTheory.PsType.grp_mul_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlaceExtensionValues
section -- merged from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.RationalFormValues
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev lamV (D : D7) (i : Fin D.R.m) : D.what₂.Tau → DomWeight (Vc D i).rank :=
  fun τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ

def IsCoefExt {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (ι : K →+* K')
    {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (c₀ : VV K lam →ₛₗ[σ] W) (c' : VV K' lam →ₛₗ[σ'] W) : Prop :=
  ∀ (v : VV K lam) (v' : VV K' lam), (v' : Pol K' I n) = MvPolynomial.map ι (v : Pol K I n) → c' v' = c₀ v

section Row

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def formFn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (x : A.fam.amb.FL i t) : Bridge.Gf (Vc D i) → (R.cV i).W :=
  (R.HV i t).e (R.jV i t x)

def ValuesIn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {K' : Type} [Field K'] {σ' : K' →+* ℂ}
    (c' : VV K' (lamV D i) →ₛₗ[σ'] (R.cV i).W) : Prop :=
  ∀ (x : A.fam.amb.FL i t) (h : Bridge.Gf (Vc D i)), ∃ v : VV K' (lamV D i), c' v = formFn R i t x h

def RationalValuesAt (R : RealDat D A Ks) : Prop :=
  ∀ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W)
    (c0L : ∀ i : Fin D.R.m, VV D.what₂.LL (lamV D i) →ₛₗ[D.what₂.embLL] (R.cV i).coef.W),
    Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (lamV D) gramR c0R c0L →
    ∀ (i : Fin D.R.m) (t : T) (K' : Type) [Field K'] (ι : D.what₂.LL →+* K') (σ' : K' →+* ℂ), σ'.comp ι = D.what₂.embLL →
      ∀ c' : VV K' (lamV D i) →ₛₗ[σ'] (R.cV i).W, IsCoefExt (W := (R.cV i).W) ι (lamV D i) (c0L i) c' → ValuesIn R i t c'

end Row

def RationalValues : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → RationalValuesAt R

end GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues

namespace GlobalTheory.Proof.PlaceExtensionValues

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coef

variable {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} {ι : K →+* K'}
  {I : Type} [Fintype I] {n : ℕ} {lam : I → DomWeight n} {W : Type} [AddCommGroup W] [Module ℂ W]
  {c₀ : VV K lam →ₛₗ[σ] W} {c' : VV K' lam →ₛₗ[σ'] W}

end Coef

section Reps

variable {Gp Γ : Type} [Group Gp] [Group Γ] {ι : Γ →* Gp} {J : Subgroup Gp}


end Reps

section Row

open Formalism.IndefR.FWT

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
  {K' : Type} [Field K'] {σ' : K' →+* ℂ}

theorem isCoefExt_iff_c0BC (jL : D.what₂.LL →+* K') (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W)
    (c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) :
    IsCoefExt jL (FWT.lamV D i) c₀ c' ↔ CoefficientBaseChange R i jL σ' c₀ c' := by
  constructor
  · intro h v
    exact ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV jL _ _ v.2⟩, rfl, h v _ rfl⟩
  · intro h v v' hv
    obtain ⟨w, hw, hc⟩ := h v
    rw [show v' = w from Subtype.ext (hv.trans hw.symm)]
    exact hc

variable (c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)

variable {R i t c'}

variable {gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E}
  {c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W}
  {c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W} {jL : D.what₂.LL →+* K'}


variable (R)

end Row

end GlobalTheory.Proof.PlaceExtensionValues

end
end
