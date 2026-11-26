module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalVacuaToDoubledLatticeVacuum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimensionalThetaFunctionsLevelFockDegree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedThetaFamilyVectorsLatticesThetaZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ContDiff

namespace GlobalTheory.EisCont.CentreFinite

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isRealLine_conj (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (a : GAd σ J) :
    IsRealLine σ J fun t => a⁻¹ * γ t * a := by
  obtain ⟨w, τ, Z, hZ, hγ⟩ := hγ
  have hu : ∀ x : GArch σ J w, (GlobalTheory.Orb.archMat σ J τ x)ᴴ * J.map τ.1 * GlobalTheory.Orb.archMat σ J τ x = J.map τ.1 :=
    fun x => (archEquiv J h τ x).2
  have h1 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have u1 := hu (projArch σ J w a)
  have u2 := hu (projArch σ J w a)⁻¹
  refine ⟨w, τ, GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a), ?_,
    fun t => ?_⟩
  · generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
    generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
    generalize J.map τ.1 = Q at u1 u2 hZ ⊢
    have e1 : M'ᴴ * Q = Q * M := by
      conv_rhs => rw [← u2, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e2 : Q * M' = Mᴴ * Q := by
      conv_lhs => rw [← u1, Matrix.mul_assoc, h2, Matrix.mul_one]
    calc (M' * Z * M)ᴴ * Q + Q * (M' * Z * M) = Mᴴ * Zᴴ * (M'ᴴ * Q) + (Q * M') * Z * M := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Mᴴ * (Zᴴ * Q + Q * Z) * M := by
          rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨y, e1, e2⟩ := hγ t
    refine ⟨(projArch σ J w a)⁻¹ * y * projArch σ J w a, ?_, ?_⟩
    · show a⁻¹ * γ t * a = _
      rw [e1]
      refine GAd_ext σ J (fun u => ?_) fun v => by simp
      by_cases e : u = w
      · subst e; simp
      · simp [projArch_embArch_ne σ J e]
    · rw [map_mul, map_mul, e2]
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
      have hM : IsUnit M := ⟨⟨M, M', h2, h1⟩, rfl⟩
      rw [← Matrix.inv_eq_left_inv h1, ← Matrix.exp_conj' _ _ hM, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.EisCont.CentreFinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteUnitaryQuotientCompactFundamentalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteUnitaryQuotientCompactFundamentalDomain
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.DefFund

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem exists_measurable_fundamentalDomain_subset [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ]
    {K : Set G} (hK : IsClosed K) (hcov : ∀ x : G, ∃ γ ∈ Γ, γ * x ∈ K) (μ : Measure G) :
    ∃ S ⊆ K, MeasurableSet S ∧ IsFundamentalDomain Γ S μ := by
  classical
  have := GlobalTheory.countable_of_discrete_subgroup Γ
  obtain ⟨D, hD, hu, -⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup Γ
  obtain ⟨c, hc⟩ := exists_injective_nat Γ
  let S : Set G := K ∩ ⋃ g : Γ, ((fun y => g • y) ⁻¹' D ∩ ⋂ h : Γ, ⋂ _ : c h < c g, ((fun y => (h⁻¹ * g) • y) ⁻¹' K)ᶜ)
  have hS : ∀ y, y ∈ S ↔ y ∈ K ∧ ∃ g : Γ, g • y ∈ D ∧ ∀ h : Γ, c h < c g → (h⁻¹ * g) • y ∉ K := fun y => by
    simp only [S, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff]
  have hSm : MeasurableSet S :=
    hK.measurableSet.inter <| MeasurableSet.iUnion fun g => (measurable_const_smul g hD).inter <|
      MeasurableSet.iInter fun h => MeasurableSet.iInter fun _ => (measurable_const_smul _ hK.measurableSet).compl
  refine ⟨S, Set.inter_subset_left, hSm, IsFundamentalDomain.mk' hSm.nullMeasurableSet fun x => ?_⟩
  obtain ⟨d, hd, hdu⟩ := hu x
  have hex : ∃ n, ∃ g : Γ, c g = n ∧ (g⁻¹ * d) • x ∈ K := by
    obtain ⟨γ, hγ, h⟩ := hcov x
    refine ⟨_, d * (⟨γ, hγ⟩ : Γ)⁻¹, rfl, ?_⟩
    rw [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]
    exact h
  obtain ⟨g, hg, hgK⟩ := Nat.find_spec hex
  refine ⟨g⁻¹ * d, (hS _).2 ⟨hgK, g, ?_, fun h hh hK' => ?_⟩, fun k hk => ?_⟩
  · rw [smul_smul, mul_inv_cancel_left]; exact hd
  · refine Nat.find_min hex (hg ▸ hh) ⟨h, rfl, ?_⟩
    rwa [smul_smul, mul_assoc, mul_inv_cancel_left] at hK'
  · obtain ⟨hkK, g', h1, h2⟩ := (hS _).1 hk
    rw [smul_smul] at h1
    have e : g' * k = d := hdu _ h1
    have ek : k = g'⁻¹ * d := by rw [← e, inv_mul_cancel_left]
    have hle : Nat.find hex ≤ c g' := Nat.find_min' hex ⟨g', rfl, ek ▸ hkK⟩
    rcases hle.eq_or_lt with h | h
    · rw [ek, hc (hg.trans h)]
    · refine (h2 g (hg ▸ h) ?_).elim
      rw [smul_smul, mul_assoc, e]
      exact hgK

end GlobalTheory.DefFund

theorem GlobalTheory.DefFund.coCpt_and_fundamentalDomain_subset_compact :
    ∀ (D : D7) (A : HSp D), HSpace.SigOK A → HSpace.IsPosDef A → ∀ m : Measure (GA D A), m.IsHaarMeasure → GlobalTheory.Unf.CoCpt A ∧ ∃ (X K : Set (GA D A)), MeasurableSet X ∧ IsFundamentalDomain (GQ A) X m ∧ IsCompact K ∧ X ⊆ K := by
  intro D A hs hp m hm
  have hc : GlobalTheory.Unf.CoCpt A := (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D A).2 fun τ => by
    have h1 := hs (tauE D τ)
    rw [hp (tauE D τ)] at h1
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature h1
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨K, hK, hcov⟩ := hc
  obtain ⟨X, hXK, hXm, hX⟩ := GlobalTheory.DefFund.exists_measurable_fundamentalDomain_subset (GQ A) hK.isClosed hcov m
  exact ⟨⟨K, hK, hcov⟩, X, K, hXm, hX, hK, hXK⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteUnitaryQuotientCompactFundamentalDomainStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_unitary_quotient_compact_fundamentalDomain : ∀ (D : D7) (A : HSp D), HSpace.SigOK A → HSpace.IsPosDef A → ∀ m : Measure (GA D A), m.IsHaarMeasure → GlobalTheory.Unf.CoCpt A ∧ ∃ (X K : Set (GA D A)), MeasurableSet X ∧ IsFundamentalDomain (GQ A) X m ∧ IsCompact K ∧ X ⊆ K := by
  first | exact @GlobalTheory.DefFund.coCpt_and_fundamentalDomain_subset_compact | exact GlobalTheory.DefFund.coCpt_and_fundamentalDomain_subset_compact | (intros; apply GlobalTheory.DefFund.coCpt_and_fundamentalDomain_subset_compact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelMulConjCuspFormIntegrableOn
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelMulConjCuspFormIntegrableOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.ThetaFirstVar

open GlobalTheory.Size

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}

theorem thetaKO_left_fst (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (h : GA D W) :
    ∀ γ ∈ GQ V, ∀ g, thetaKO ω (γ * g) h f = thetaKO ω g h f := fun γ hγ g => by
  have e : ((γ * g, h) : GA D V × GA D W) = (γ, 1) * (g, h) := by simp
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hf)

theorem thetaKO_continuous_fst (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (h : GA D W) :
    Continuous fun g => thetaKO ω g h f :=
  (hω.om_cont f hf 0).comp (Continuous.prodMk_left h)

theorem thetaKO_modGrowth_fst (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f)
    (h : GA D W) : GlobalTheory.Grow.ModGrowth V fun g => thetaKO ω g h f := by
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne V W
  obtain ⟨C, -, hC⟩ := (H V W rfl rfl).real ψ hθ hU
  refine ⟨C * (sobO ψ θ μ 𝓕 d f).toReal * GlobalTheory.Grow.height W h ^ A, A, fun g => ?_⟩
  rw [mul_assoc _ (GlobalTheory.Grow.height W h ^ A), ← mul_pow, mul_comm (GlobalTheory.Grow.height W h)]
  exact (hC χS χT ω hω μ 𝓕 hμ f hl).2 g h

theorem thetaKO_mul_conj_integrableOn : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ (u : WO S T → ℂ) (y : GA D S → ℂ), IsThetaFunO ψ S T u → IsAutFunSm θ S y → IsCuspFun S y → ∀ (a : GA D S) (x : GA D T), IntegrableOn (fun g => thetaKO om g x u * conj (y (g * a))) 𝓕 ν := by
  intro hP D ψ S T χS χT om hω θ hθ ν 𝓕 hν h𝓕 u y hu hy hc a x
  have : BorelSpace (GA D S) := ⟨rfl⟩
  have hR : GlobalTheory.Grow.RapidDec S fun g => conj (y (g * a)) :=
    ((GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hy hc).mul_right a).conj
  exact hR.integrableOn_modGrowth_mul hν h𝓕 (thetaKO_modGrowth_fst hθ hω hu x) (thetaKO_left_fst hω hu x)
    (thetaKO_continuous_fst hω hu x).measurable.aestronglyMeasurable

end GlobalTheory.ChainOnto.ThetaFirstVar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelMulConjCuspFormIntegrableOnStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_mul_conj_cuspForm_integrableOn : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ (u : WO S T → ℂ) (y : GA D S → ℂ), IsThetaFunO ψ S T u → IsAutFunSm θ S y → IsCuspFun S y → ∀ (a : GA D S) (x : GA D T), IntegrableOn (fun g => thetaKO om g x u * conj (y (g * a))) 𝓕 ν := by
  first | exact @GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_mul_conj_integrableOn | exact GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_mul_conj_integrableOn | (intros; apply GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_mul_conj_integrableOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.LevelFacts

variable {D : D7}

theorem places_of_stage {c : Com D} {j : ℕ} {s : PiLocalization₂ D} (hs : s.Is c j) : s.L.Pg = c.Pg ∧ s.L.Q = ∅ := by
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  rw [hL]
  exact ⟨rfl, rfl⟩

theorem mem_levG_of_red {c : Com D} {j : ℕ} {s : PiLocalization₂ D} (hs : s.Is c j) {k : GA D s.V} (hk : k ∈ GfC s.V)
    (hS : Lev.finE s.V k ∈ St s.β) (hr : ∀ PP ∈ c.Pg, redFn s.β PP (Lev.finE s.V k) = 1) :
    k ∈ Lev.levG s.V s.β s.L ∧ Lev.levChi s.V s.β s.L k = 1 := by
  obtain ⟨hPg, hQ⟩ := places_of_stage hs
  have h' : ∀ PP, PP ∈ s.L.Pg ∨ PP ∈ s.L.Q → redFn s.β PP (Lev.finE s.V k) = 1 := by
    rintro PP (h | h)
    · exact hr PP (hPg ▸ h)
    · rw [hQ] at h; simp at h
  refine ⟨⟨hk, GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm s.V.gram s.β s.L _ (GlobalTheory.LevSplit.finE_mem_UA s.V k) hS h'⟩, ?_⟩
  unfold Lev.levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one s.β s.L _ h', Units.val_one]

theorem finE_mem_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {k : GA D V}
    (hk : k ∈ Lev.levG V β L) : Lev.finE V k ∈ St β :=
  parLev_St (lev_le_parLev hk.2)

theorem emb_mem_GfC (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (k : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v) :
    GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k ∈ GfC V := by
  rw [GlobalTheory.AdelicU.GfC_eq]
  exact GlobalTheory.AdelicU.mem_finPts.2 (by simp)

theorem levChi_norm {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (k : GA D V) :
    ‖Lev.levChi V β L k‖ = 1 := by
  obtain ⟨n, hn, h⟩ := (GlobalTheory.LevSplit.levFn_finOrd β L (Lev.finE V k)).exists_pow_eq_one
  have h2 : (Lev.levChi V β L k) ^ n = 1 := by
    unfold Lev.levChi
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h2 hn.ne'

theorem levChi_mul {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {k k' : GA D V}
    (hk : k ∈ Lev.levG V β L) (hk' : k' ∈ Lev.levG V β L) :
    Lev.levChi V β L (k * k') = Lev.levChi V β L k * Lev.levChi V β L k' := by
  have e := (levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩
  have e' : levFn β L (Lev.finE V k * Lev.finE V k') = levFn β L (Lev.finE V k) * levFn β L (Lev.finE V k') := e
  unfold Lev.levChi
  rw [map_mul, e', Units.val_mul]

end GlobalTheory.ChainOnto.LevelFacts

namespace GlobalTheory.ChainOnto.LevelFacts

theorem levFacts : ∀ D : D7, LevFacts D := by
  intro D c _ j _ s hs
  have hfr := hs.frame
  have hPS : ∀ PP ∈ c.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ c.S := fun PP hPP => by
    classical
    unfold Com.S
    exact Finset.mem_image_of_mem _ hPP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨U, hU, hUk⟩ := GlobalTheory.T.exists_open_principal_congruence_finitely_many_primes D s.V s.β c.Pg
    exact ⟨U, hU, fun k hk hkf => mem_levG_of_red hs hkf (hUk k hk).1 (hUk k hk).2⟩
  · intro v hv k hk
    have hSt : Lev.finE s.V (GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v k) ∈ St s.β := by
      refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D s.V s.β s.Λ hfr _).2 fun w => ?_
      by_cases e : w = v
      · subst e
        rw [GlobalTheory.AdelicU.proj_emb_self]
        exact hk
      · rw [GlobalTheory.AdelicU.proj_emb_ne _ _ e]
        exact one_mem _
    refine mem_levG_of_red hs (emb_mem_GfC s.V v k) hSt fun PP hPP => ?_
    · refine GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D s.V s.β _ PP hSt ?_
      have hne : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := fun e => hv (e ▸ hPS PP hPP)
      exact GlobalTheory.AdelicU.proj_emb_ne _ _ hne k
  · intro k hk v
    exact (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D s.V s.β s.Λ hfr k).1 (finE_mem_St hk) v
  · intro k hkf hint h1
    have hSt : Lev.finE s.V k ∈ St s.β := by
      refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D s.V s.β s.Λ hfr k).2 fun v => ?_
      by_cases hv : v ∈ c.S
      · rw [h1 v hv]; exact one_mem _
      · exact hint v hv
    exact mem_levG_of_red hs hkf hSt fun PP hPP => GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D s.V s.β k PP hSt (h1 _ (hPS PP hPP))
  · intro k hk k' hk'
    exact levChi_mul hk hk'
  · intro k _
    exact levChi_norm s.β s.L k

end GlobalTheory.ChainOnto.LevelFacts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelPropertiesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_level_properties : ∀ D : D7, LevFacts D := by
  first | exact @GlobalTheory.ChainOnto.LevelFacts.levFacts | exact GlobalTheory.ChainOnto.LevelFacts.levFacts | (intros; apply GlobalTheory.ChainOnto.LevelFacts.levFacts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizerInductionLaw
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EisCont

variable {D : D7}

theorem mem_stab_onX_of_mul {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {p : GA D T} {b : GL (Fin r) (AE D)}
    (h : mt T p ⬝ d.jX = d.jX ⬝ b.1) : ∃ hp : p ∈ stab d, onX d ⟨p, hp⟩ = b :=
  ⟨⟨b, h⟩, Units.ext ((eq_of_mul_jX d (mul_jX d ⟨p, ⟨b, h⟩⟩)).trans (eq_of_mul_jX d h).symm)⟩

theorem parFlag_zero_eq_stab {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) :
    (parFlag D.sp.cm.sig T.gram d.e fun _ => 0) = stab d := by
  ext p
  constructor
  · rintro ⟨⟨B, -, hB⟩, B', -, hB'⟩
    change mt T p ⬝ d.jX = d.jX ⬝ B at hB
    change mt T p⁻¹ ⬝ d.jX = d.jX ⬝ B' at hB'
    have e1 : B ⬝ B' = 1 := by
      rw [eq_of_mul_jX d hB]
      simp only [Matrix.mul_assoc]
      rw [← hB', ← Matrix.mul_assoc (mt T p), mt_mul_inv, Matrix.one_mul, d.pX_jX]
    have e2 : B' ⬝ B = 1 := by
      rw [eq_of_mul_jX d hB']
      simp only [Matrix.mul_assoc]
      rw [← hB, ← Matrix.mul_assoc (mt T p⁻¹), mt_inv_mul, Matrix.one_mul, d.pX_jX]
    exact ⟨⟨B, B', e1, e2⟩, hB⟩
  · intro hp
    obtain ⟨α, h⟩ := hp
    obtain ⟨β, h'⟩ := (stab d).inv_mem (show p ∈ stab d from ⟨α, h⟩)
    exact ⟨⟨α.1, fun i j hij => absurd hij (lt_irrefl _), h⟩, β.1, fun i j hij => absurd hij (lt_irrefl _), h'⟩

theorem det_onX_rat {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : stab d) (hq : (q : GA D T) ∈ GQ T) :
    ∃ u : D.host.Eˣ, Units.map (incA D : D.host.E →* AE D) u =
      Matrix.GeneralLinearGroup.det (onX d q) := by
  have hr : ∀ q : stab d, (q : GA D T) ∈ GQ T → (onX d q).1 ∈ ratMx D r r := fun q hq => by
    rw [eq_of_mul_jX d (mul_jX d q)]
    exact ratMx_mul ⟨_, rfl⟩ (ratMx_mul ((mem_GQ_iff T _).1 hq) ⟨_, rfl⟩)
  obtain ⟨A, hA⟩ := hr q hq
  obtain ⟨A', hA'⟩ := hr q⁻¹ ((GQ T).inv_mem hq)
  change rat A = _ at hA
  change rat A' = _ at hA'
  have hAA : A * A' = 1 := by
    apply rat_injective
    rw [rat_mul, rat_one, hA, hA', map_inv, Units.mul_inv]
  have hA'A : A' * A = 1 := by
    apply rat_injective
    rw [rat_mul, rat_one, hA, hA', map_inv, Units.inv_mul]
  refine ⟨⟨A.det, A'.det, by rw [← Matrix.det_mul, hAA, Matrix.det_one], by rw [← Matrix.det_mul, hA'A, Matrix.det_one]⟩,
    Units.ext ?_⟩
  change incA D A.det = (onX d q).1.det
  rw [← hA, RingHom.map_det]
  rfl

theorem indLaw_inv {T T₀ : HSp D} {r : ℕ} {d : HypDec T T₀ r} {μ : (AE D)ˣ →* Circle} {t : ℂ} {φ : GA D T → ℂ}
    (hφ : IndLaw (absDet d) (detChar d μ) t φ) (q : stab d) (h1 : detChar d μ q = 1) (h2 : absDet d q = 1) (g : GA D T) :
    φ (q * g) = φ g := by
  rw [hφ q g, h1, h2]
  simp [npow]

theorem leftInv_leftGrp_of_indLaw {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {μ : (AE D)ˣ →* Circle}
    (hμ : IsHeckeChar D μ) {t : ℂ} {φ : GA D T → ℂ} (hφ : IndLaw (absDet d) (detChar d μ) t φ) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (leftGrp D.sp.cm.sig T.gram d.e fun _ => 0) φ := by
  let H : Subgroup (GA D T) :=
    { carrier := {γ | ∀ g, φ (γ * g) = φ g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {a b} ha hb g => by rw [mul_assoc, ha, hb]
      inv_mem' := fun {a} ha g => by rw [← ha, mul_inv_cancel_left] }
  have hH : (leftGrp D.sp.cm.sig T.gram d.e fun _ => 0) ≤ H := by
    refine sup_le ((Subgroup.closure_le _).2 fun u hu => ?_) fun γ hγ => ?_
    · obtain ⟨A, hA, e⟩ := lower_iff.1 hu.1
      rw [show A = 0 from Matrix.ext fun j i => hA j i le_rfl, Matrix.mul_zero, Matrix.sub_mul, Matrix.one_mul,
        sub_eq_zero] at e
      obtain ⟨hp, h1⟩ := mem_stab_onX_of_mul d (p := u) (b := 1) (e.trans (Matrix.mul_one _).symm)
      refine indLaw_inv hφ ⟨u, hp⟩ ?_ ?_
      · rw [detChar, MonoidHom.comp_apply, MonoidHom.comp_apply, h1, map_one, map_one]
      · rw [absDet, MonoidHom.comp_apply, MonoidHom.comp_apply, h1, map_one, map_one]
    · have hp : γ ∈ stab d := parFlag_zero_eq_stab d ▸ hγ.2
      obtain ⟨u, hu⟩ := det_onX_rat d ⟨γ, hp⟩ hγ.1
      refine indLaw_inv hφ ⟨γ, hp⟩ ?_ ?_
      · rw [detChar, MonoidHom.comp_apply, MonoidHom.comp_apply, ← hu]
        exact hμ.2 u
      · rw [absDet, MonoidHom.comp_apply, MonoidHom.comp_apply, ← hu]
        exact absE_inclR u
  exact fun γ hγ => hH hγ

theorem parFlag_stab_leftInv : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r), (parFlag D.sp.cm.sig T.gram d.e fun _ => 0) = stab d ∧ ratPts D.sp.cm.sig T.gram = GQ T ∧ (∀ (p : GA D T) (b : GL (Fin r) (AE D)), (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram p).1 * adMat D.host.F d.e = adMat D.host.F d.e * b.1 → ∃ hp : p ∈ stab d, onX d ⟨p, hp⟩ = b) ∧ ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (t : ℂ) (φ : GA D T → ℂ), IndLaw (absDet d) (detChar d μ) t φ → GlobalTheory.AutomorphicL2Unitary.LeftInv (leftGrp D.sp.cm.sig T.gram d.e fun _ => 0) φ :=
  fun _ _ _ _ d => ⟨parFlag_zero_eq_stab d, rfl, fun _ _ h => mem_stab_onX_of_mul d h,
    fun _ hμ _ _ hφ => leftInv_leftGrp_of_indLaw d hμ hφ⟩

end GlobalTheory.EisCont

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvari
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvari
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem setIntegral_fd_mul_right : ∀ (D : D7) (S : HSp D) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ F : GA D S → ℂ, (∀ γ ∈ GQ S, ∀ g, F (γ * g) = F g) → ∀ a : GA D S, ∫ g in 𝓕, F (g * a) ∂ν = ∫ g in 𝓕, F g ∂ν := by
  intro D S ν 𝓕 hν h𝓕 F hF a
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : Countable (GQ S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig S.gram
  haveI : ν.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds S ν hν
  exact GlobalTheory.setIntegral_fundamentalDomain_mul_right h𝓕 a F hF

end GlobalTheory.ChainOnto
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvariStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_fundamentalDomain_right_translate_invariant : ∀ (D : D7) (S : HSp D) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ F : GA D S → ℂ, (∀ γ ∈ GQ S, ∀ g, F (γ * g) = F g) → ∀ a : GA D S, ∫ g in 𝓕, F (g * a) ∂ν = ∫ g in 𝓕, F g ∂ν := by
  first | exact @GlobalTheory.ChainOnto.setIntegral_fd_mul_right | exact GlobalTheory.ChainOnto.setIntegral_fd_mul_right | (intros; apply GlobalTheory.ChainOnto.setIntegral_fd_mul_right <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZetaResidueNeZeroOfSimplePoleLiftLFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZetaResidueNeZeroOfSimplePoleLiftLFunction
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Exh

open Filter Topology

theorem residue_ne_zero_of_simplePole : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ (D : D7) (S : Finset (FinPl D)) (r t : ℕ) (c par : GlobalTheory.LFun.Fam D.host.E) (χ : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (S : Set (FinPl D)) r t c par (GlobalTheory.LFun.val (F := D.host.F) χ) (GlobalTheory.LFun.val (F := D.host.F) χ) → ∀ (a b : ℕ) (Z : ℂ → ℂ) (C z : ℂ), C ≠ 0 → EqRight Z (fun s => GlobalTheory.LFun.LSD D S par χ (s + 1 / 2) / GlobalTheory.LFun.dSfun D.host.E (S : Set (FinPl D)) a b s * C) → CoeffAt Z ((t : ℂ) / 2) (-1) z → z ≠ 0 := by
  intro hSP D S r t c par χ hH a b Z C z hC hZ hz
  obtain ⟨-, -, ⟨Z0, hZ0⟩, h4⟩ := hSP D.host.F D.host.E (S : Set (FinPl D)) r t c par
    (GlobalTheory.LFun.val (F := D.host.F) χ) (GlobalTheory.LFun.val (F := D.host.F) χ) hH
  obtain ⟨hmer, -, heq, -, -, ρ, hρ, hlim⟩ := h4 Z0 hZ0
  set R := GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.rhs (S : Set (FinPl D)) c (GlobalTheory.LFun.val (F := D.host.F) χ) t Z0 with hR
  set d := GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E (S : Set (FinPl D)) a b with hd
  obtain ⟨hdan, hdne⟩ := dSfun_analytic_ne_zero D (S : Set (FinPl D)) a b
  have ht : (r : ℝ) + 5 ≤ t := by exact_mod_cast hH.2.1
  have hr0 : (0 : ℝ) ≤ (r : ℝ) / 2 := by positivity
  have htr : (r : ℝ) / 2 < ((t : ℂ) / 2).re := by
    have : ((t : ℂ) / 2).re = (t : ℝ) / 2 := by simp
    rw [this]; linarith
  have hext : IsExtAt (fun s => GlobalTheory.LFun.LSD D S par χ (s + 1 / 2) / d s * C) ((t : ℂ) / 2)
      (fun s => R (s + 1 / 2) / d s * C) := by
    refine ⟨rightOf ((r : ℝ) / 2), htr, isRightDomain_rightOf _, fun s hs => ?_, (t : ℝ) / 2, fun s hs => ?_⟩
    · have hs0 : (r : ℝ) / 2 < s.re := hs
      have hs' : ((r : ℝ) + 1) / 2 < (s + 1 / 2).re := by
        have : (s + 1 / 2).re = s.re + 1 / 2 := by simp
        rw [this]; linarith
      have h1 : MeromorphicAt (fun s => R (s + 1 / 2)) s :=
        MeromorphicAt.comp_analyticAt (g := (· + 1 / 2)) (hmer _ hs') (by fun_prop)
      have h2 : MeromorphicAt d s := (hdan s (show (0 : ℝ) < s.re by linarith)).meromorphicAt
      exact (h1.div h2).mul (MeromorphicAt.const C s)
    · have hs0 : (t : ℝ) / 2 < s.re := hs
      have hs' : ((t : ℝ) + 1) / 2 < (s + 1 / 2).re := by
        have : (s + 1 / 2).re = s.re + 1 / 2 := by simp
        rw [this]; linarith
      show R (s + 1 / 2) / d s * C = GlobalTheory.LFun.LSD D S par χ (s + 1 / 2) / d s * C
      rw [heq _ hs']
  have hext' : IsExtAt Z ((t : ℂ) / 2) (fun s => R (s + 1 / 2) / d s * C) := hext.congr hZ.symm
  have hpos : (0 : ℝ) < ((t : ℂ) / 2).re := lt_of_le_of_lt hr0 htr
  have hd0 : d ((t : ℂ) / 2) ≠ 0 := (hdne _ hpos).1
  have hshift : Tendsto (fun s : ℂ => s + 1 / 2) (𝓝[≠] ((t : ℂ) / 2)) (𝓝[≠] ((1 + (t : ℂ)) / 2)) := by
    have h := (Homeomorph.addRight (1 / 2 : ℂ)).map_punctured_nhds_eq ((t : ℂ) / 2)
    have e : (t : ℂ) / 2 + 1 / 2 = (1 + (t : ℂ)) / 2 := by ring
    have h' : map (fun x : ℂ => x + 1 / 2) (𝓝[≠] ((t : ℂ) / 2)) = 𝓝[≠] ((t : ℂ) / 2 + 1 / 2) := h
    rw [e] at h'
    exact h'.le
  have h2 : Tendsto d (𝓝[≠] ((t : ℂ) / 2)) (𝓝 (d ((t : ℂ) / 2))) :=
    (hdan _ hpos).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim' : Tendsto (fun s => (s - (t : ℂ) / 2) ^ (1 : ℕ) * (R (s + 1 / 2) / d s * C)) (𝓝[≠] ((t : ℂ) / 2))
      (𝓝 (ρ / d ((t : ℂ) / 2) * C)) := by
    refine (((hlim.comp hshift).div h2 hd0).mul_const C).congr fun s => ?_
    simp only [Pi.div_apply, Function.comp_apply, pow_one]
    ring
  have hc := hext'.coeffAt_of_tendsto hlim'
  have e := hz.unique (by simpa using hc)
  rw [e]
  exact mul_ne_zero (div_ne_zero hρ hd0) hC

end GlobalTheory.Core.Rk.Exh

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZetaResidueNeZeroOfSimplePoleLiftLFunctionStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_residue_ne_zero_of_simple_pole_lift_L_function : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ (D : D7) (S : Finset (FinPl D)) (r t : ℕ) (c par : GlobalTheory.LFun.Fam D.host.E) (χ : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (S : Set (FinPl D)) r t c par (GlobalTheory.LFun.val (F := D.host.F) χ) (GlobalTheory.LFun.val (F := D.host.F) χ) → ∀ (a b : ℕ) (Z : ℂ → ℂ) (C z : ℂ), C ≠ 0 → EqRight Z (fun s => GlobalTheory.LFun.LSD D S par χ (s + 1 / 2) / GlobalTheory.LFun.dSfun D.host.E (S : Set (FinPl D)) a b s * C) → CoeffAt Z ((t : ℂ) / 2) (-1) z → z ≠ 0 := by
  first | exact @GlobalTheory.Core.Rk.Exh.residue_ne_zero_of_simplePole | exact GlobalTheory.Core.Rk.Exh.residue_ne_zero_of_simplePole | (intros; apply GlobalTheory.Core.Rk.Exh.residue_ne_zero_of_simplePole <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnisotropicCoreWittFrame
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WittFrameOfDec

theorem form_mulVec {D : D7} {n m : ℕ} (A : Matrix (Fin n) (Fin m) D.host.E) (G : Matrix (Fin n) (Fin n) D.host.E)
    (w : Fin m → D.host.E) : star (A *ᵥ w) ⬝ᵥ (G *ᵥ (A *ᵥ w)) = star w ⬝ᵥ ((Aᴴ * G * A) *ᵥ w) := by
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem isWittFrame_of_hypDec (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (h : IsAniso T₀) :
    IsWittFrame D.sp.cm.sig T.gram d.e d.e' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cT_sig]; exact d.ee
  · rw [cT_sig]; exact d.e'e'
  · rw [cT_sig]
    have h1 := congrArg Matrix.conjTranspose d.e'e
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      gram_conjTranspose, Matrix.conjTranspose_one, ← Matrix.mul_assoc] at h1
    exact h1
  · intro z hX hY hz
    rw [cT_sig] at hX hY
    have hqY : d.qY *ᵥ z = 0 := hX
    have hqX : d.qX *ᵥ z = 0 := hY
    have hz0 : z = d.i₀ *ᵥ (d.q0 *ᵥ z) := by
      have := congrArg (fun M => M *ᵥ z) d.sum_eq_one_rat
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hqX, hqY,
        Matrix.mulVec_zero, zero_add, add_zero] at this
      exact this.symm
    obtain ⟨z₀, hz₀⟩ : ∃ w, w = d.q0 *ᵥ z := ⟨_, rfl⟩
    rw [← hz₀] at hz0
    by_cases h0 : z₀ = 0
    · rw [hz0, h0, Matrix.mulVec_zero]
    exfalso
    have e1 : hE D.sp.cm.sig T.gram z z = star z ⬝ᵥ (T.gram *ᵥ z) := by
      simp only [hE, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mul_assoc]; rfl
    have hzz : star z₀ ⬝ᵥ (T₀.gram *ᵥ z₀) = 0 := by
      rw [← d.iso, ← form_mulVec, ← hz0, ← e1, hz]
    let C : Matrix (Fin T₀.rank) (Fin 1) D.host.E := Matrix.of fun i _ => z₀ i
    apply h 1 C
    refine ⟨Nat.one_pos, ?_, ?_⟩
    · change LinearIndependent D.host.E (fun _ : Fin 1 => z₀)
      exact linearIndependent_unique_iff.2 h0
    · rw [cT_sig]
      ext a b
      fin_cases a; fin_cases b
      have : (Cᴴ * T₀.gram * C) 0 0 = star z₀ ⬝ᵥ (T₀.gram *ᵥ z₀) := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, C, Matrix.of_apply, dotProduct, Matrix.mulVec,
          Pi.star_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      simpa using this.trans hzz

end GlobalTheory.WittFrameOfDec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuesWithModerateGrowthShiftTranslatePow
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuesWithModerateGrowthShiftTranslatePow
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EisCont.Shift

open Set Metric

theorem holValueAt_of_continuousAt {h : ℂ → ℂ} (a : GlobalTheory.Cont.Continues h) {t : ℂ}
    (b : ContinuousAt (GlobalTheory.Cont.cont h) t) : GlobalTheory.Cont.HolValueAt h t (GlobalTheory.Cont.cont h t) := by
  obtain ⟨H₀, hH⟩ := a
  have ha := hH.isExtAt (mem_univ t)
  exact ha.holValueAt_iff.2 ((b.tendsto.mono_left nhdsWithin_le_nhds).congr' ha.cont_eventuallyEq)

theorem differentiable_npow_sub {c : ℝ≥0} (hc : 0 < c) (s₁ : ℂ) : Differentiable ℂ fun s => npow c (s₁ - s) :=
  (GlobalTheory.Eis.differentiable_npow hc).comp (differentiable_const _ |>.sub differentiable_id)

theorem contMod_shift (D : D7) (T : HSp D) (e e' : ℂ → GA D T → ℂ) (x : GA D T) (c : ℝ≥0) (s₁ s₂ : ℂ) (hc : 0 < c)
    (he : ∀ s g, e' s g = npow c (s₁ - s) * e (s + s₂) (g * x)) (hm : ContMod T e) : ContMod T e' := by
  have hd := differentiable_npow_sub hc s₁
  have hfun : ∀ g, (fun z => e' z g) = fun z => npow c (s₁ - z) * (fun w => e w (g * x)) (z + s₂) :=
    fun g => funext fun z => he z g
  refine ⟨fun g => ?_, fun s₀ => ?_⟩
  · obtain ⟨H₀, hH⟩ := hm.1 (g * x)
    rw [GlobalTheory.Cont.isMerExt_univ] at hH
    obtain ⟨σ, hσ⟩ := hH.2
    refine ⟨fun z => npow c (s₁ - z) * H₀ (z + s₂), GlobalTheory.Cont.isMerExt_univ.2 ⟨fun z => ?_, σ - s₂.re, fun z hz => ?_⟩⟩
    · exact (hd.analyticAt z).meromorphicAt.fun_mul
        ((hH.1 (z + s₂)).comp_analyticAt (g := (· + s₂)) (by fun_prop))
    · simp only [he]
      congr 1
      exact hσ (by simpa [GlobalTheory.Cont.mem_rightOf] using sub_lt_iff_lt_add.1 hz)
  · obtain ⟨k, r, H, hr, h1, h2, h3, C, N, h4⟩ := hm.2 (s₀ + s₂)
    have hball : ∀ s ∈ ball s₀ r, s + s₂ ∈ ball (s₀ + s₂) r := fun s hs => by
      simpa [mem_ball, dist_eq_norm] using hs

    have hval : ∀ s ∈ ball s₀ r, s ≠ s₀ → ∀ g,
        GlobalTheory.Cont.cont (fun z => e' z g) s = npow c (s₁ - s) * GlobalTheory.Cont.cont (fun z => e z (g * x)) (s + s₂) := by
      intro s hs hne g
      have hne' : s + s₂ ≠ s₀ + s₂ := fun h => hne (add_right_cancel h)
      have hopen : ball (s₀ + s₂) r ∩ {s₀ + s₂}ᶜ ∈ 𝓝 (s + s₂) :=
        (isOpen_ball.inter isOpen_compl_singleton).mem_nhds ⟨hball s hs, hne'⟩
      have hcont : ContinuousAt (GlobalTheory.Cont.cont fun z => e z (g * x)) (s + s₂) := by
        have hq : ContinuousAt (fun t => H t (g * x) / (t - (s₀ + s₂)) ^ k) (s + s₂) :=
          (((h2 (g * x)).continuousOn.continuousAt (isOpen_ball.mem_nhds (hball s hs)))).div
            (by fun_prop) (pow_ne_zero _ (sub_ne_zero.2 hne'))
        refine hq.congr (Filter.eventually_of_mem hopen fun t ht => ?_)
        have := h1 t ht.1 ht.2 (g * x)
        show H t (g * x) / _ = _
        rw [this, mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.2 ht.2))]
      have hv := holValueAt_of_continuousAt (hm.1 (g * x)) hcont
      have hn : GlobalTheory.Cont.HolValueAt (fun z => npow c (s₁ - z)) s (npow c (s₁ - s)) :=
        GlobalTheory.Cont.IsHolExt.holValueAt ⟨GlobalTheory.Cont.isRightDomain_univ, fun z _ => hd.analyticAt z, .refl _⟩ (mem_univ s)
      have hp := hn.mul hv.comp_add
      rw [hfun g]
      exact hp.valueAt.cont_eq
    obtain ⟨B, hB⟩ := (isCompact_closedBall s₀ r).exists_bound_of_continuousOn hd.continuous.continuousOn
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB s₀ (mem_closedBall_self hr.le))
    refine ⟨k, r, fun s g => npow c (s₁ - s) * H (s + s₂) (g * x), hr, fun s hs hne g => ?_, fun g => ?_, ?_,
      B * |C| * GlobalTheory.Grow.height T x ^ N, N, fun s hs g => ?_⟩
    · show npow c (s₁ - s) * H (s + s₂) (g * x) = _
      rw [hval s hs hne g, h1 _ (hball s hs) (fun h => hne (add_right_cancel h)) (g * x)]
      rw [show s + s₂ - (s₀ + s₂) = s - s₀ by ring]
      ring
    · refine (hd.differentiableOn).mul ((h2 (g * x)).comp (by fun_prop) fun s hs => hball s hs)
    · refine (hd.continuous.comp continuous_fst).continuousOn.mul ?_
      exact h3.comp (f := fun p : ℂ × GA D T => (p.1 + s₂, p.2 * x)) (by fun_prop)
        fun (p : ℂ × GA D T) (hp : p ∈ ball s₀ r ×ˢ univ) => ⟨hball p.1 hp.1, mem_univ _⟩
    · have hH := h4 _ (hball s hs) (g * x)
      have hn := hB s (ball_subset_closedBall hs)
      have hg := GlobalTheory.Grow.height_mul_le T g x
      have hg0 := (GlobalTheory.Grow.height_pos T g).le
      have hx0 := (GlobalTheory.Grow.height_pos T x).le
      have hgx0 := (GlobalTheory.Grow.height_pos T (g * x)).le
      have e1 : ‖H (s + s₂) (g * x)‖ ≤ |C| * (GlobalTheory.Grow.height T g * GlobalTheory.Grow.height T x) ^ N :=
        hH.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hgx0 N)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hgx0 hg N) (abs_nonneg C)))
      rw [norm_mul]
      calc ‖npow c (s₁ - s)‖ * ‖H (s + s₂) (g * x)‖ ≤ B * (|C| * (GlobalTheory.Grow.height T g * GlobalTheory.Grow.height T x) ^ N) :=
            mul_le_mul hn e1 (norm_nonneg _) hB0
        _ = B * |C| * GlobalTheory.Grow.height T x ^ N * GlobalTheory.Grow.height T g ^ N := by rw [mul_pow]; ring

end GlobalTheory.EisCont.Shift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuesWithModerateGrowthShiftTranslatePowStatement
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuesWithModerateGrowth_shift_translate_pow : ∀ (D : D7) (T : HSp D) (e e' : ℂ → GA D T → ℂ) (x : GA D T) (c : ℝ≥0) (s₁ s₂ : ℂ), 0 < c → (∀ s g, e' s g = npow c (s₁ - s) * e (s + s₂) (g * x)) → ContMod T e → ContMod T e' := by
  first | exact @GlobalTheory.EisCont.Shift.contMod_shift | exact GlobalTheory.EisCont.Shift.contMod_shift | (intros; apply GlobalTheory.EisCont.Shift.contMod_shift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorFiniteUnderCompactCommutingCartan
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorFiniteUnderCompactCommutingCartan
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem isKFinVec_of_isFockVec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T) (sS : RealMat S) (sT : RealMat T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ K : Subgroup (GA D S), IsCompact (K : Set (GA D S)) → (∀ k ∈ K, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k)) → ∀ f, IsFockVec ψ θ S T sS sT f → IsKFinVec om K f := by
  intro D ψ θ S T χS χT om sS sT hW hθ hS hT K hK hc f hf
  obtain ⟨hth, N, hN⟩ := hf
  obtain ⟨U, hU, hUK⟩ := GlobalTheory.T.exists_common_level_compact_translates_thetaFunction D ψ S T χS χT om hW (K : Set (GA D S)) hK f hth
  have hfd := GlobalTheory.T.finiteDimensional_thetaFunctions_level_fockDegree D ψ θ S T sS sT hW.std hθ hS hT U hU N
  refine @Submodule.finiteDimensional_of_le _ _ _ _ _ _ _ hfd (Submodule.span_mono ?_)
  rintro g ⟨k, hk, rfl⟩
  exact ⟨hW.om_pres _ f hth, hUK k hk,
    GlobalTheory.T.weilRep_preserves_fockDegree_of_commute_cartan D ψ θ S T χS χT om sS sT hW hθ k (hc k hk) N f hth hN⟩

end GlobalTheory.Core.Rk.IP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorFiniteUnderCompactCommutingCartanStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_vector_finite_under_compact_commuting_cartan : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T) (sS : RealMat S) (sT : RealMat T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ K : Subgroup (GA D S), IsCompact (K : Set (GA D S)) → (∀ k ∈ K, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k)) → ∀ f, IsFockVec ψ θ S T sS sT f → IsKFinVec om K f := by
  first | exact @GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec | exact GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec | (intros; apply GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramEqOfInst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.SBesEx

theorem gram_eq_of_inst {D : D7} (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (hId : ∀ x : I.E, HEq (ιE x) x) (hn : (D.sp.Y 0).rank = I.n)
    (k l : Fin (D.sp.Y 0).rank) :
    ιE (I.J (Fin.cast hn k) (Fin.cast hn l)) = (D.sp.Y 0).gram k l := by
  subst hI
  rw [eq_of_heq (hId _)]
  rfl

theorem cY_isom : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), GlobalTheory.Core.Rk.IdE X → ∀ y y' : (VS D).V, star (GlobalTheory.Core.SBesEx.cY X h y') ⬝ᵥ ((D.sp.Y 0).gram *ᵥ GlobalTheory.Core.SBesEx.cY X h y) = (VS D).hT y' y := by
  intro D X h hId y y'
  set b := X.bas.reindex (finCongr (rank_eq X h)).symm with hb
  have hc : ∀ z, cY X h z = b.repr z := by
    intro z; funext k
    simp [cY, HidaSetting.crd, crdOf, hb, Module.Basis.repr_reindex]
  have hG : (D.sp.Y 0).gram = fun k l => (VS D).hT (b k) (b l) := by
    funext k l
    rw [← gram_eq_of_inst X.B.I h X.ιE hId (rank_eq X h) k l, X.J_eq]
    simp [hb]
  rw [hc, hc, hG]
  conv_rhs => rw [← b.sum_repr y', ← b.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, dotProduct, mulVec,
    Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [starRingEnd_apply]
  ring

end GlobalTheory.Core.SBesEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergThetaMixedModelTarget_of_mixedModel : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.HeisenbergTarget D := by
  first | exact @GlobalTheory.HeisTarget.main | exact GlobalTheory.HeisTarget.main | (intros; apply GlobalTheory.HeisTarget.main <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLaws
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Core.Ht2

theorem family_laws : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws)
    (Z : TC.Later B (I.cols l)), (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).EqP I.chi ∧
      (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).VecP I.chi := by
  intro B X I h _ l Z
  have hcc : TaylorLogMetric.IsCurveIdeal (assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ := ⟨top_ne_bot, by simp⟩
  have hδ := ((I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 h.amb_ok).1
  have hχ : TaylorLogMetric.IsChi (assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi := GlobalTheory.Mem.ChiIdeal.isChi_chiId _ _ I.C.isChi
  exact ⟨GlobalTheory.Mem.NatEqui.eqP _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ,
    (GlobalTheory.NatFamily.family _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ).1⟩

end GlobalTheory.Core.Ht2
end
