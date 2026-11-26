module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelSixth
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsFiniteSumGelfandKirillovMultiplicity

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspFormsApproximatedByThetaLifts
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsSumApproxPureCuspForm
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KFiniteCuspFormFiniteSumExpansion
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GelfandKirillovLocalToGlobal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.GKGlobalise
theorem gelfandKirillov_local_to_global : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ F : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (GA D V → ℂ),
      (∀ u, IsAutFunSm θ V (F u)) ∧ (∀ u, IsCuspFun V (F u)) ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
        ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          (w : M.H τ) = M.rep τ g (u τ) → F (Function.update u τ w) = rTr V (atTau θ V τ g) (F u)) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (u τ : M.H τ)) (w : M.H τ) 0 →
          F (Function.update u τ w) = Rder θ V τ X (F u)) →
      ∃ T : Formalism.IndefR.Mult.MMap M, Formalism.IndefR.Mult.IsMultMap θ M ∅ 1 T ∧
        ∀ u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) = u τ) ∧ T v = F u := by
  intro hP D θ V S M hθ F ⟨haut, hcusp, hK, hL⟩
  have hHC := hP.harishChandraModules
  have hCW := hP.casselmanWallach
  have hk : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ = GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) := fun τ => (kFin_eq M τ).symm
  let e : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) :=
    fun τ => (LinearEquiv.ofEq _ _ (hk τ)).toLinearMap
  let T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M := F.compLinearMap e
  have hupd : ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) τ (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ),
      T₀ (Function.update u τ w) = F (Function.update (fun τ' => e τ' (u τ')) τ (e τ w)) := by
    intro u τ w
    show F (fun τ' => e τ' (Function.update u τ w τ')) = _
    congr 1
    funext τ'
    exact Function.apply_update (fun τ => e τ) u τ w τ'
  have hGK : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M ∅ 1 0 ∅ T₀ := by
    refine ⟨fun u => (haut _).toIsAutFun, fun u => (haut _).smooth, fun u => hcusp _,
      fun u => ?_, fun u => GlobalTheory.Grow.unifModGrowth_of_isAutFunSm hθ (haut _),
      fun u k hk => by simp at hk, ?_, ?_⟩
    · rw [Measure.restrict_zero]; exact memLp_measure_zero
    · intro τ k hkm u w hw
      rw [hupd]
      exact hK τ k (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt_subset M τ hkm) hkm (fun τ' => e τ' (u τ')) (e τ w) hw
    · intro τ X hX u w hw
      rw [hupd]
      refine hL τ X hX (fun τ' => e τ' (u τ')) (e τ w) ?_
      have hsm : (u τ : M.H τ) ∈ GlobalTheory.SmVec.smSub (gramAt D V τ) (GlobalTheory.SmVec.trRep (M.σ τ) (M.fr τ)) := by
        rw [← GlobalTheory.SmVec.sm_eq]; exact kFin_le_sm hHC M τ (u τ).2
      have h1 := GlobalTheory.SmVec.hasDerivAt_dRep hsm (X := X) hX
      show HasDerivAt _ (w : M.H τ) 0
      rw [hw]
      exact h1
  obtain ⟨U, N, hU, hTU⟩ := GlobalTheory.T.exists_common_level_growth_exponent_gKMap hHC D θ hθ V S M ∅ 1 0 ∅ T₀ hGK
  obtain ⟨E, i1, i2, i3, i4, i5, i6, p, ι, hinj, hrange, hp, hπ⟩ :=
    GlobalTheory.T.exists_smoothCuspForm_frechet_moderateGrowth_rep D θ hθ V (GlobalTheory.ChainFr.Fr.ofModel M) U N hU
  choose π dπ hπ using hπ
  have hmem : ∀ u, T₀ u ∈ LinearMap.range ι := fun u => by
    have ha := hGK.1 u
    obtain ⟨x, hx⟩ := (hrange _).2 ⟨ha.cont, ha.left, (hTU u).1, hGK.2.1 u, hGK.2.2.1 u, (hTU u).2⟩
    exact ⟨x, hx⟩
  let eι := LinearEquiv.ofInjective ι hinj
  let T₀' : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) E :=
    eι.symm.toLinearMap.compMultilinearMap (T₀.codRestrict (LinearMap.range ι) hmem)
  have hT₀' : ∀ u, ι (T₀' u) = T₀ u := fun u => by
    have h1 := congrArg Subtype.val (eι.apply_symm_apply ⟨T₀ u, hmem u⟩)
    rw [LinearEquiv.ofInjective_apply] at h1
    exact h1
  have hK' : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ),
      (w : M.H τ) = M.σ τ k (u τ) → T₀' (Function.update u τ w) = π τ k (T₀' u) := by
    intro τ k hk u w hw
    apply hinj
    rw [(hπ τ).2.1 k (GlobalTheory.GKExt.kset_sub hk), hT₀', hT₀']
    have hk' : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := GlobalTheory.GKExt.conj_back (M.fr_unit τ)
    have hmax : (M.fr τ)⁻¹ * k * M.fr τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ := by
      change M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)
      rw [hk']; exact hk
    refine (hGK.2.2.2.2.2.2.1 τ _ hmax u w ?_).trans rfl
    rw [hw]
    show _ = M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹) _
    rw [hk']
  have hL' : ∀ τ, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M)
      (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = dRep (M.σ τ) X (u τ) →
      T₀' (Function.update u τ w) = dπ τ X (T₀' u) := by
    intro τ X hX u w hw
    apply hinj
    rw [(hπ τ).2.2 X hX, hT₀', hT₀']
    have hd : dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) = dRep (M.σ τ) X := by
      funext y
      unfold dRep
      congr 1
      funext t
      show M.σ τ (M.fr τ * NormedSpace.exp (t • ((M.fr τ)⁻¹ * X * M.fr τ)) * (M.fr τ)⁻¹) y = _
      rw [GlobalTheory.GKExt.exp_conj_inv (M.fr_unit τ), GlobalTheory.GKExt.conj_back (M.fr_unit τ)]
    exact hGK.2.2.2.2.2.2.2 τ _ (GlobalTheory.GKExt.conj_mem_lieAt M τ hX) u w (by rw [hw, hd])
  have hcomm : ∀ τ τ', τ ≠ τ' → ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ g' ∈ Formalism.MainNotions.S.UJset (M.ε τ'),
      (π τ g).comp (π τ' g') = (π τ' g').comp (π τ g) := by
    intro τ τ' hne g hg g' hg'
    ext x
    apply hinj
    simp only [ContinuousLinearMap.comp_apply]
    rw [(hπ τ).2.1 g hg, (hπ τ').2.1 g' hg', (hπ τ').2.1 g' hg', (hπ τ).2.1 g hg]
    funext y
    simp only [rTr, mul_assoc]
    exact congrArg (fun z => ι x (y * z)) (GlobalTheory.T.realPlacePoint_commute_of_ne_place D θ hθ V τ τ' hne _
      (GlobalTheory.GKExt.conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) hg) _
      (GlobalTheory.GKExt.conj_mem_UH (M.fr_unit τ') (M.fr_gram τ') hg'))
  obtain ⟨TE, hTE1, hTE2, hTE3⟩ := GlobalTheory.T.multilinear_gKMap_extends_to_smooth_vectors hHC hCW D V S M E p π dπ (fun τ => (hπ τ).1) hcomm T₀' hK' hL'
  obtain ⟨hequiv, hcont⟩ := GlobalTheory.T.casselmanWallach_multMap_equivariant_sobolevContinuous D θ V S M E p ι N π hp
    (fun x d => ((hrange (ι x)).1 ⟨x, rfl⟩).2.2.2.2.2 d) (fun τ => (hπ τ).2.1) TE hTE2 hTE3
  let T : Formalism.IndefR.Mult.MMap M := ι.compMultilinearMap TE
  have hext : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.Extends T T₀ := fun v u h => by
    show ι (TE v) = T₀ u
    rw [hTE1 v u h, hT₀']
  have hMult : Formalism.IndefR.Mult.IsMultMap θ M ∅ 1 T := by
    refine ⟨?_, fun v => ((hrange _).1 ⟨TE v, rfl⟩).2.2.2.2.1, fun v k hk => by simp at hk, hequiv, hcont⟩
    exact GlobalTheory.T.isSmoothAutomorphicForm_multMap_value hHC D θ hθ V S M T U N hU (fun v => by
      have h := (hrange (ι (TE v))).1 ⟨TE v, rfl⟩
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩) hequiv hcont
  refine ⟨T, hMult, fun u => ?_⟩
  let ue : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M := fun τ => ⟨(u τ : M.H τ), by rw [← kFin_eq M τ]; exact (u τ).2⟩
  refine ⟨fun τ => ⟨(u τ : M.H τ), kFin_le_sm hHC M τ (ue τ).2⟩, fun τ => rfl, ?_⟩
  rw [hext _ ue (fun τ => rfl)]
  show F (fun τ => e τ (ue τ)) = F u
  congr 1
end GlobalTheory.GKGlobalise
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandKirillov_globalization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ F : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (GA D V → ℂ),
      (∀ u, IsAutFunSm θ V (F u)) ∧ (∀ u, IsCuspFun V (F u)) ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
        ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          (w : M.H τ) = M.rep τ g (u τ) → F (Function.update u τ w) = rTr V (atTau θ V τ g) (F u)) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (u τ : M.H τ)) (w : M.H τ) 0 →
          F (Function.update u τ w) = Rder θ V τ X (F u)) →
      ∃ T : Formalism.IndefR.Mult.MMap M, Formalism.IndefR.Mult.IsMultMap θ M ∅ 1 T ∧
        ∀ u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) = u τ) ∧ T v = F u := by
  first | exact @_root_.GlobalTheory.GKGlobalise.gelfandKirillov_local_to_global | exact _root_.GlobalTheory.GKGlobalise.gelfandKirillov_local_to_global | (intros; apply _root_.GlobalTheory.GKGlobalise.gelfandKirillov_local_to_global <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.KFinCuspSum
theorem kFinite_cusp_form_eq_sum_values : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ → (∃ W : Submodule ℂ (GA D (G.V i j).V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V i j).V τ), (G.V i j).M.fr τ * g * ((G.V i j).M.fr τ)⁻¹ ∈ Formalism.REAL.Kset ((G.V i j).M.ε τ) → ∀ f ∈ W, Formalism.L2.Theta.rTr (G.V i j).V (Formalism.L2.Theta.atTau R.θ (G.V i j).V τ g) f ∈ W) → ∃ (n : ℕ) (T : Fin n → Formalism.IndefR.Mult.MMap (G.V i j).M) (v : Fin n → (G.V i j).M.Vec), (∀ l, Formalism.IndefR.Mult.IsMultMap R.θ (G.V i j).M ∅ 1 (T l)) ∧ ∀ g, ψ g = ∑ l, T l (v l) g := by
  intro hP D G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i j hi hj ψ hψ hW
  obtain ⟨n, F, u, hF, hsum⟩ :=
    _root_.GlobalTheory.T.cuspForm_gelfandKirillov_finite_decomposition hP R.θ (G.V i j).V (G.V i j).S (G.V i j).M hR.inf ψ hψ.1 hψ.2.1 hψ.2.2 hW
  choose Tm hTm hext using fun l =>
    _root_.GlobalTheory.T.gelfandKirillov_globalization hP R.θ (G.V i j).V (G.V i j).S (G.V i j).M hR.inf (F l) (hF l)
  choose v hv hTv using fun l => hext l (u l)
  refine ⟨n, Tm, v, hTm, fun g => ?_⟩
  rw [hsum g]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hTv l]
end GlobalTheory.KFinCuspSum
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_cusp_form_finite_sum_expansion : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ → (∃ W : Submodule ℂ (GA D (G.V i j).V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V i j).V τ), (G.V i j).M.fr τ * g * ((G.V i j).M.fr τ)⁻¹ ∈ Formalism.REAL.Kset ((G.V i j).M.ε τ) → ∀ f ∈ W, Formalism.L2.Theta.rTr (G.V i j).V (Formalism.L2.Theta.atTau R.θ (G.V i j).V τ g) f ∈ W) → ∃ (n : ℕ) (T : Fin n → Formalism.IndefR.Mult.MMap (G.V i j).M) (v : Fin n → (G.V i j).M.Vec), (∀ l, Formalism.IndefR.Mult.IsMultMap R.θ (G.V i j).M ∅ 1 (T l)) ∧ ∀ g, ψ g = ∑ l, T l (v l) g := by
  first | exact @_root_.GlobalTheory.KFinCuspSum.kFinite_cusp_form_eq_sum_values | exact _root_.GlobalTheory.KFinCuspSum.kFinite_cusp_form_eq_sum_values | (intros; apply _root_.GlobalTheory.KFinCuspSum.kFinite_cusp_form_eq_sum_values <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsKFiniteApproxOfCuspForm
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspFormApproximationSinglePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open MeasureTheory GlobalTheory.Grow GlobalTheory.Size
open scoped ENNReal
namespace GlobalTheory.KFinCuspApprox
theorem kFinite_cusp_approx_at_one_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (τ : D.what₂.Tau) (a : ℕ) (δ : ℝ), 0 < δ → ∃ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e ∧ GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e ∧ ∀ g, ‖φ g - GlobalTheory.KFinCuspApprox.avgN θ N τ e φ g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ δ := by
  intro hP D θ hθ N φ hφ τ a δ hδ
  obtain ⟨hA, hc, -⟩ := id hφ
  obtain ⟨U, hU, hlev⟩ := hA.level
  obtain ⟨d, C, hC⟩ := hP.cuspDecaySobolev D θ hθ N.V U hU 0 a
  have hr := rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ hA hc
  have hη : 0 < δ / ((C : ℝ) + 1) := div_pos hδ (by positivity)
  obtain ⟨e, he, hgrow⟩ := GlobalTheory.KAvgApprox.one_place D θ hθ N.V τ (N.M.ε τ) (N.M.fr τ) (N.M.fr_unit τ) (N.M.fr_gram τ) φ hr d _ hη
  have hec : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  have hav := GlobalTheory.KAvgApprox.avg_rapid D θ hθ N.V τ (N.M.ε τ) (N.M.fr τ) (N.M.fr_unit τ) (N.M.fr_gram τ) e hec φ hr
  set ψ : GA D N.V → ℂ := φ - avgN θ N τ e φ with hψ
  have hψr : RapidDecSm θ N.V ψ := by
    have := hr.add (hav.smul (-1))
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hψc : IsCuspFun N.V ψ := by
    have h2 := _root_.GlobalTheory.T.kFinite_cuspForm_average_approx θ hθ hP N τ e hec φ hA hc
    have := GlobalTheory.MultMem.isCuspFun_add hr.toIsAutFun (hav.smul (-1)).toIsAutFun hc (GlobalTheory.MultMem.isCuspFun_smul (-1) h2)
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hψlev : ∀ k ∈ U, k ∈ GfC N.V → ∀ x, ψ (x * k) = ψ x := by
    intro k hk hk' x
    simp only [hψ, Pi.sub_apply, hlev k hk hk' x]
    congr 1
    show (∫ k', e k' * φ (x * k * _) ∂_) = ∫ k', e k' * φ (x * _) ∂_
    congr 1; funext k'
    rw [mul_assoc, ← Formalism.IndefR.Eqv.Act.comm_inf_fin (Formalism.IndefR.Eqv.Act.atTau_mem θ τ _) hk', ← mul_assoc, hlev k hk hk']
  refine ⟨e, hec, he, fun g => ?_⟩
  have h1 := hC ψ hψr.toIsAutFun hψlev hψr.smooth (GlobalTheory.CuspApproxAll.growthSob_zero_ne_top hψr) hψc
  have h2 : decaySize N.V a ψ ≤ ENNReal.ofReal δ := by
    have h4 : (C : ℝ≥0∞) * growthSob θ N.V d 0 ψ ≤ C * ENNReal.ofReal (δ / ((C : ℝ) + 1)) := by gcongr
    refine h1.trans (h4.trans ?_)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [NNReal.coe_nonneg C]
  have h3 : ENNReal.ofReal (‖ψ g‖ * quotHeight N.V g ^ a) ≤ ENNReal.ofReal δ :=
    (le_iSup (fun x => ENNReal.ofReal (‖ψ x‖ * quotHeight N.V x ^ a)) g).trans h2
  rw [ENNReal.ofReal_le_ofReal_iff hδ.le] at h3
  simpa [hψ] using h3
end GlobalTheory.KFinCuspApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_approximation_single_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (τ : D.what₂.Tau) (a : ℕ) (δ : ℝ), 0 < δ → ∃ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e ∧ GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e ∧ ∀ g, ‖φ g - GlobalTheory.KFinCuspApprox.avgN θ N τ e φ g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ δ := by
  first | exact @_root_.GlobalTheory.KFinCuspApprox.kFinite_cusp_approx_at_one_place | exact _root_.GlobalTheory.KFinCuspApprox.kFinite_cusp_approx_at_one_place | (intros; apply _root_.GlobalTheory.KFinCuspApprox.kFinite_cusp_approx_at_one_place <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KFiniteCuspAverageHasKType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.KFinCuspAvgType
open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined
variable {n : ℕ}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)}
end GlobalTheory.KFinCuspAvgType
end
namespace GlobalTheory.KFinCuspAvgType
open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined
theorem kFinite_average_isTypeAt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK →
    ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e →
    ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ →
    IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  intro hPr D θ hθ N _ τ e _ he φ hφ
  obtain ⟨H, i1, i2, σ, lam, ε', P, hE, hD, hP, hJ, hx⟩ := hφ.2.2 τ
  obtain ⟨-, hε⟩ := GlobalTheory.SignedParTest.isEnum_unique hE (N.M.enum τ)
  subst hε
  haveI : CompleteSpace H := hD.1
  have hσ : Std (N.M.ε τ) σ := std_of_isDS hPr.harishChandraModules hD
  have hσ1 := hσ.1
  set fr := N.M.fr τ with hfr
  have hf := N.M.fr_unit τ
  have hfJ := N.M.fr_gram τ
  rw [← hfr] at hf hfJ
  have hdP := (isUnit_iff_isUnit_det _).1 hP
  have hdf := (isUnit_iff_isUnit_det _).1 hf
  have hG : IsUnit (gramAt D N.V τ) := isUnit_gram hP hJ
  have hc1 : fr * P⁻¹ ∈ UJset (N.M.ε τ) := mul_inv_mem_UH hP hfJ hJ
  have hc2 : P * fr⁻¹ ∈ UJset (N.M.ε τ) := mul_inv_mem_UH hf hJ hfJ
  have e12 : fr * P⁻¹ * (P * fr⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdP, Matrix.mul_nonsing_inv _ hdf]
  have e21 : P * fr⁻¹ * (fr * P⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdf, Matrix.mul_nonsing_inv _ hdP]
  have hconj : ∀ {Q : Mx N.V.rank}, IsUnit Q → Qᴴ * Jm (N.M.ε τ) * Q = gramAt D N.V τ →
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), Q * g * Q⁻¹ ∈ UJset (N.M.ε τ) := fun {Q} hQ hQJ g hg =>
    mul_inv_mem_UH hQ (by
      calc (Q * g)ᴴ * Jm (N.M.ε τ) * (Q * g) = gᴴ * (Qᴴ * Jm (N.M.ε τ) * Q) * g := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D N.V τ := by rw [hQJ]; exact hg) hQJ
  refine ⟨H, i1, i2, σ, lam, N.M.ε τ, fr, hE, hD, hf, hfJ, fun x => ?_⟩
  have h1 := hasTypeAll_iff.2 (hx x)
  have h2 := hasTypeAll_transport _ H H (fun g => σ (P * g * P⁻¹)) σ (gramAt D N.V τ) (Jm (N.M.ε τ)) fr hG hf hfJ
    (uIso hσ1 hc1 hc2 e12 e21) (fun g hg v => by
      rw [uIso_apply, uIso_apply, ← sigma_mul hσ1 hc1 (hconj hP hJ g hg), ← sigma_mul hσ1 (hconj hf hfJ g hg) hc1]
      congr 2
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdP, Matrix.nonsing_inv_mul_cancel_left _ _ hdf]) _ h1
  obtain ⟨S, hS, hc, v, ℓ, C, h⟩ := h2
  have h3 := GlobalTheory.SeriesToClosure.moves_avg hθ hf hfJ hσ he φ x S v ℓ C hS hc h
  have h4 : HasTypeAll (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) σ
      (GlobalTheory.SeriesToClosure.res θ N.V τ fr (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) x) := ⟨S, hS, hc, _, ℓ, C, h3⟩
  have hfi : IsUnit fr⁻¹ := (isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hdf)
  have hfiJ : (fr⁻¹)ᴴ * gramAt D N.V τ * fr⁻¹ = Jm (N.M.ε τ) := by
    rw [← hfJ]
    calc (fr⁻¹)ᴴ * (frᴴ * Jm (N.M.ε τ) * fr) * fr⁻¹ = (fr * fr⁻¹)ᴴ * Jm (N.M.ε τ) * (fr * fr⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hdf]; simp
  have h5 := hasTypeAll_transport _ H H σ (fun g => σ (fr * g * fr⁻¹)) (Jm (N.M.ε τ)) (gramAt D N.V τ) fr⁻¹
    (isUnit_Jm _) hfi hfiJ (LinearIsometryEquiv.refl ℂ H) (fun g _ w => by
      show σ g w = σ (fr * (fr⁻¹ * g * fr⁻¹⁻¹) * fr⁻¹) w
      rw [Matrix.nonsing_inv_nonsing_inv _ hdf]
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdf, Matrix.mul_nonsing_inv _ hdf,
        Matrix.mul_one]) _ h4
  have e5 : (fun y => GlobalTheory.SeriesToClosure.res θ N.V τ fr (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) x (fr⁻¹⁻¹ * y * fr⁻¹)) =
      fun y => GlobalTheory.KFinCuspApprox.avgN θ N τ e φ (x * atTau θ N.V τ y) := funext fun y => by
    rw [Matrix.nonsing_inv_nonsing_inv _ hdf, GlobalTheory.SeriesToClosure.res_conj hf]
  rw [e5] at h5
  exact hasTypeAll_iff.1 h5
end GlobalTheory.KFinCuspAvgType
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_cusp_average_hasKType : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  first | exact @_root_.GlobalTheory.KFinCuspAvgType.kFinite_average_isTypeAt | exact _root_.GlobalTheory.KFinCuspAvgType.kFinite_average_isTypeAt | (intros; apply _root_.GlobalTheory.KFinCuspAvgType.kFinite_average_isTypeAt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KTypePreservedAverageOtherPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AvgOtherPlace
open Formalism.MainNotions.S Formalism.REAL MeasureTheory Matrix GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom
open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open scoped TensorProduct
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
section Avg
variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {τ τ' : D.what₂.Tau} {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ} {e : K → ℂ}
end Avg
section Closure
variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {τ τ' : D.what₂.Tau} {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ} {e : K → ℂ}
end Closure
theorem kFinite_average_isTypeAt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK →
    ∀ (τ τ' : D.what₂.Tau), τ' ≠ τ → ∀ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e →
    ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ →
    IsTypeAt θ N.V τ' (N.S τ') (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  intro hPr D θ hθ N hN τ τ' hne e he _ φ hφ
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  have hU : ∀ k, (N.M.fr τ)⁻¹ * toMK k * N.M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) :=
    fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hκ := GlobalTheory.SeriesToClosure.continuous_conjK (ε := N.M.ε τ) (P := N.M.fr τ)
  have p1 := hPr.discreteSeriesUpqExists
  have p2 := GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hPr.discreteSeriesHermitianUnique
  have p3 := hPr.harishChandraModules
  have p4 := hPr.casselmanWallach
  have hT := GlobalTheory.SeriesToClosure.hasTypeAt_of_isTypeAt θ N.V τ' (N.S τ') φ p1 p2 p3 p4 hθ hN
    (GlobalTheory.NodePar.goodPar_of_sigOK N hN τ') hφ.1 (hφ.2.2 τ')
  have hA := GlobalTheory.RealAverage.isAutFunSm_average D θ hθ N.V τ (KG (N.M.ε τ)) (muK (N.M.ε τ)) _ hκ hU e he φ hφ.1
  exact GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series θ N.V τ' (N.S τ') _ p1 p2 p3 p4 hθ hN (GlobalTheory.NodePar.goodPar_of_sigOK N hN τ') hA
    (hasTypeAt_avgF (muK (N.M.ε τ)) hθ hne hκ hU he hφ.1.cont hT)
end GlobalTheory.AvgOtherPlace
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kType_preserved_average_other_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK → ∀ (τ τ' : D.what₂.Tau), τ' ≠ τ → ∀ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → IsTypeAt θ N.V τ' (N.S τ') (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  first | exact @_root_.GlobalTheory.AvgOtherPlace.kFinite_average_isTypeAt | exact _root_.GlobalTheory.AvgOtherPlace.kFinite_average_isTypeAt | (intros; apply _root_.GlobalTheory.AvgOtherPlace.kFinite_average_isTypeAt <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.KFinCuspApprox
theorem exists_kFinite_approx_of_cusp_form : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ (a : ℕ) (δ : ℝ), 0 < δ → ∃ ψ : GA D (G.V i j).V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ ∧ (∃ W : Submodule ℂ (GA D (G.V i j).V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V i j).V τ), (G.V i j).M.fr τ * g * ((G.V i j).M.fr τ)⁻¹ ∈ Formalism.REAL.Kset ((G.V i j).M.ε τ) → ∀ f ∈ W, Formalism.L2.Theta.rTr (G.V i j).V (Formalism.L2.Theta.atTau R.θ (G.V i j).V τ g) f ∈ W) ∧ ∀ g, ‖φ g - ψ g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ := by
  intro hP D G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i j hi hj φ hφ a δ hδ
  have hθ : IsInfFam R.θ := hR.inf
  have hS : (G.V i j).V.SigOK := GlobalTheory.ThetaLiftTypeTh.sigOK_vert G hG hi hj
  have hA : ∀ τ (e : Formalism.REAL.KG ((G.V i j).M.ε τ) → ℂ), Continuous e → GlobalTheory.TypeSum.KFinFun ((G.V i j).M.ε τ) e →
      ∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ →
        GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) (GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e ψ) := by
    intro τ e he hK ψ hψ
    refine ⟨?_, _root_.GlobalTheory.T.kFinite_cuspForm_average_approx R.θ hθ hP (G.V i j) τ e he ψ hψ.1 hψ.2.1, fun τ' => ?_⟩
    · exact GlobalTheory.T.isSmoothAutomorphicFunction_compactFamily_average D R.θ hθ (G.V i j).V τ (Formalism.REAL.KG ((G.V i j).M.ε τ)) (Formalism.REAL.muK ((G.V i j).M.ε τ)) _
        GlobalTheory.SeriesToClosure.continuous_conjK
        (fun k => GlobalTheory.Published.AutFin.conj_mem_UH ((G.V i j).M.fr_unit τ) ((G.V i j).M.fr_gram τ) k) e he ψ hψ.1
    · by_cases h : τ' = τ
      · subst h
        exact _root_.GlobalTheory.T.kFinite_cusp_average_hasKType hP R.θ hθ (G.V i j) hS τ' e he hK ψ hψ
      · exact _root_.GlobalTheory.T.kType_preserved_average_other_place hP R.θ hθ (G.V i j) hS τ τ' h e he hK ψ hψ
  have hlin : ∀ τ (e : Formalism.REAL.KG ((G.V i j).M.ε τ) → ℂ), Continuous e → ∀ f f' : GA D (G.V i j).V → ℂ,
      Continuous f → Continuous f' → ∀ g, GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e f g -
        GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e f' g = GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e (f - f') g := by
    intro τ e he f f' hf hf' g
    have hk : Continuous fun k : Formalism.REAL.KG ((G.V i j).M.ε τ) =>
        atTau R.θ (G.V i j).V τ (((G.V i j).M.fr τ)⁻¹ * Formalism.REAL.toMK k * (G.V i j).M.fr τ) :=
      (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ (G.V i j).V τ).comp_continuous GlobalTheory.SeriesToClosure.continuous_conjK
        fun k => GlobalTheory.Published.AutFin.conj_mem_UH ((G.V i j).M.fr_unit τ) ((G.V i j).M.fr_gram τ) k
    have c1 : Continuous fun k : Formalism.REAL.KG ((G.V i j).M.ε τ) =>
        e k * f (g * atTau R.θ (G.V i j).V τ (((G.V i j).M.fr τ)⁻¹ * Formalism.REAL.toMK k * (G.V i j).M.fr τ)) :=
      he.mul (hf.comp (continuous_const.mul hk))
    have c2 : Continuous fun k : Formalism.REAL.KG ((G.V i j).M.ε τ) =>
        e k * f' (g * atTau R.θ (G.V i j).V τ (((G.V i j).M.fr τ)⁻¹ * Formalism.REAL.toMK k * (G.V i j).M.fr τ)) :=
      he.mul (hf'.comp (continuous_const.mul hk))
    have i1 := GlobalTheory.ExpansionAverage.integrable_K c1
    have i2 := GlobalTheory.ExpansionAverage.integrable_K c2
    simp only [GlobalTheory.KFinCuspApprox.avgN, GlobalTheory.SeriesToClosure.avg, Pi.sub_apply, mul_sub]
    exact (integral_sub i1 i2).symm
  have key : ∀ l : List D.what₂.Tau, l.Nodup → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ δ : ℝ, 0 < δ →
      ∃ ψ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ ∧ ∃ W : Submodule ℂ (GA D (G.V i j).V → ℂ),
        FiniteDimensional ℂ W ∧ ψ ∈ W ∧ (∀ f ∈ W, Continuous f) ∧ GlobalTheory.KFinCuspApprox.KStab R.θ (G.V i j) {τ | τ ∈ l} W ∧
        ∀ g, ‖φ g - ψ g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ := by
    intro l
    induction l with
    | nil =>
      intro _ φ hφ δ hδ
      refine ⟨φ, hφ, Submodule.span ℂ {φ}, inferInstance, Submodule.mem_span_singleton_self φ, fun f hf => ?_,
        by simpa using GlobalTheory.KFinCuspApprox.kStab_empty R.θ (G.V i j) _, fun g => by simpa using hδ.le⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hf
      exact hφ.1.cont.const_smul c
    | cons τ l ih =>
      intro hnd φ hφ δ hδ
      rw [List.nodup_cons] at hnd
      obtain ⟨e, he, hK, happ⟩ := _root_.GlobalTheory.T.cuspForm_approximation_single_place hP R.θ hθ (G.V i j) φ hφ τ a (δ / 2) (by linarith)
      obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.avgOverMaximalCompact_weighted_supNorm_bound R.θ hθ (G.V i j) τ e he a
      obtain ⟨ψ', hψ', W', hW'f, hψW', hW'c, hW's, hb⟩ := ih hnd.2 φ hφ (δ / (2 * (C + 1))) (by positivity)
      obtain ⟨W, hWf, hWc, hWs, hWm⟩ :=
        GlobalTheory.T.exists_finiteDim_stable_space_maxCompactAverages R.θ hθ (G.V i j) τ e hK {τ | τ ∈ l} hnd.1 W' hW'f hW'c hW's
      refine ⟨_, hA τ e he hK ψ' hψ', W, hWf, hWm ψ' hψW', hWc, by simpa [Set.insert_def] using hWs, fun g => ?_⟩
      have h1 := happ g
      have h2 := hC (φ - ψ') _ hb g
      rw [← hlin τ e he φ ψ' hφ.1.cont hψ'.1.cont g] at h2
      have hq : 0 ≤ GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a := pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le a
      have e1 : φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e ψ' g =
          (φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e φ g) +
            (GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e ψ' g) := by ring
      have h3 : C * (δ / (2 * (C + 1))) ≤ δ / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      calc ‖φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e ψ' g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a
          ≤ (‖φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e φ g‖ +
              ‖GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e ψ' g‖) *
              GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a := by
            rw [e1]; exact mul_le_mul_of_nonneg_right (norm_add_le _ _) hq
        _ ≤ δ / 2 + δ / 2 := by rw [add_mul]; linarith
        _ = δ := by ring
  obtain ⟨ψ, hψ, W, hWf, hψW, -, hWs, hb⟩ := key Finset.univ.toList (Finset.nodup_toList _) φ hφ δ hδ
  refine ⟨ψ, hψ, ⟨W, hWf, hψW, fun τ g hg hk f hf => hWs τ (Finset.mem_toList.2 (Finset.mem_univ τ)) g hg hk f hf⟩, hb⟩
end GlobalTheory.KFinCuspApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_cusp_forms_dense : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ (a : ℕ) (δ : ℝ), 0 < δ → ∃ ψ : GA D (G.V i j).V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ ∧ (∃ W : Submodule ℂ (GA D (G.V i j).V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V i j).V τ), (G.V i j).M.fr τ * g * ((G.V i j).M.fr τ)⁻¹ ∈ Formalism.REAL.Kset ((G.V i j).M.ε τ) → ∀ f ∈ W, Formalism.L2.Theta.rTr (G.V i j).V (Formalism.L2.Theta.atTau R.θ (G.V i j).V τ g) f ∈ W) ∧ ∀ g, ‖φ g - ψ g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ := by
  first | exact @_root_.GlobalTheory.KFinCuspApprox.exists_kFinite_approx_of_cusp_form | exact _root_.GlobalTheory.KFinCuspApprox.exists_kFinite_approx_of_cusp_form | (intros; apply _root_.GlobalTheory.KFinCuspApprox.exists_kFinite_approx_of_cusp_form <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.CuspPureApprox
theorem exists_sum_approx_pure_cusp_form : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ (a : ℕ) (δ : ℝ), 0 < δ → ∃ (n : ℕ) (T : Fin n → Formalism.IndefR.Mult.MMap (G.V i j).M) (v : Fin n → (G.V i j).M.Vec), (∀ l, Formalism.IndefR.Mult.IsMultMap R.θ (G.V i j).M ∅ 1 (T l)) ∧ ∀ g, ‖φ g - ∑ l, T l (v l) g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ := by
  intro hP D G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i j hi hj φ hφ a δ hδ
  obtain ⟨ψ, hψ, hK, hle⟩ := _root_.GlobalTheory.T.kFinite_cusp_forms_dense hP D G₀ Pl0 T A Ks R G hR hG i j hi hj φ hφ a δ hδ
  obtain ⟨n, Tm, v, hT, heq⟩ := _root_.GlobalTheory.T.kFinite_cusp_form_finite_sum_expansion hP D G₀ Pl0 T A Ks R G hR hG i j hi hj ψ hψ hK
  exact ⟨n, Tm, v, hT, fun g => by rw [← heq g]; exact hle g⟩
end GlobalTheory.CuspPureApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_cusp_form_approx_of_twist : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ (a : ℕ) (δ : ℝ), 0 < δ → ∃ (n : ℕ) (T : Fin n → Formalism.IndefR.Mult.MMap (G.V i j).M) (v : Fin n → (G.V i j).M.Vec), (∀ l, Formalism.IndefR.Mult.IsMultMap R.θ (G.V i j).M ∅ 1 (T l)) ∧ ∀ g, ‖φ g - ∑ l, T l (v l) g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ := by
  first | exact @_root_.GlobalTheory.CuspPureApprox.exists_sum_approx_pure_cusp_form | exact _root_.GlobalTheory.CuspPureApprox.exists_sum_approx_pure_cusp_form | (intros; apply _root_.GlobalTheory.CuspPureApprox.exists_sum_approx_pure_cusp_form <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.CuspApproxX
open GlobalTheory.Grow GlobalTheory.Size
end GlobalTheory.CuspApproxX
namespace GlobalTheory.CuspApproxX
open GlobalTheory.Grow GlobalTheory.Size
theorem cusp_form_approx_by_lift (happrox : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ (a : ℕ) (δ : ℝ), 0 < δ → ∃ (n : ℕ) (T : Fin n → Formalism.IndefR.Mult.MMap (G.V i j).M) (v : Fin n → (G.V i j).M.Vec), (∀ l, Formalism.IndefR.Mult.IsMultMap R.θ (G.V i j).M ∅ 1 (T l)) ∧ ∀ g, ‖φ g - ∑ l, T l (v l) g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.V i j).Maps) (v : Fin n → SmT (G.V i j).M), (∀ l, F l ∈ (G.V i j).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * F l (v l) g) (G.meas t i j).fd (G.meas t i j).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F l (v l) g ∂(G.meas t i j).ν‖ < ε := by
  intro _hL hP D _hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC ε hε
  have hM := GlobalTheory.PairLift.haar_vert hRB hG t hi.le hj
  have : BorelSpace (GA D (G.V i j).V) := ⟨rfl⟩
  have hw := (hG.arrows.X i j hi hj).weil
  obtain ⟨K, a, hK⟩ := thetaKO_le_quotHeight hRB.inf hw hΦ
    (hC.image (GlobalTheory.Grid.continuous_ofSgn_symm true (G.V (i + 1) j).V))
  have hK' : ∀ h ∈ C, ∀ g, ‖thetaKO (G.X i j).ω h g Φ‖ ≤ |K| * quotHeight (G.V i j).V g ^ a := by
    intro h hh g
    have key := hK _ ⟨h, hh, rfl⟩ g
    refine le_trans (le_of_eq ?_) (key.trans (mul_le_mul_of_nonneg_right (le_abs_self K)
      (pow_pos (quotHeight_pos _ g) a).le))
    congr 1
  have hI : ∀ ψ' : GA D (G.V i j).V → ℂ, RapidDec (G.V i j).V ψ' → ∀ h,
      IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * ψ' g) (G.meas t i j).fd (G.meas t i j).ν := by
    intro ψ' hr h
    have key := GlobalTheory.Chain.LiftConv.integrableOn_of_rapidDec (GlobalTheory.KernelSeminorm.thetaGrowth D) hRB.inf hw hΦ hM.1
      hM.2 hr ((GlobalTheory.Grid.ofSgn true _).symm h)
    convert key using 3 with g
    simp only [thetaKO, GlobalTheory.Grid.WRep.toSgn, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply,
      MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, MonoidHom.id_apply]
  have hfin := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hM.1 hM.2
  set vol := (G.meas t i j).ν.real (G.meas t i j).fd with hvol
  have hv0 : 0 ≤ vol := measureReal_nonneg
  set δ := ε / (2 * ((|K| + 1) * (vol + 1))) with hδ
  have hpos : 0 < 2 * ((|K| + 1) * (vol + 1)) := by positivity
  have hδ0 : 0 < δ := div_pos hε hpos
  obtain ⟨n, Tm, v, hT, hap⟩ := happrox hP D G₀ Pl0 T A Ks R G hRB hG i j hi.le hj φ hφ a δ hδ0
  have hval : ∀ l, (PiTensorProduct.lift (Tm l)) (PiTensorProduct.tprod ℂ (v l)) = Tm l (v l) := fun l =>
    PiTensorProduct.lift.tprod _
  have hR : ∀ l, RapidDec (G.V i j).V (Tm l (v l)) := fun l =>
    rapidDec_of_cuspForm hP.cuspRapidDecay hRB.inf ((hT l).aut (v l)) ((hT l).cusp (v l))
  refine ⟨n, fun l => PiTensorProduct.lift (Tm l), fun l => PiTensorProduct.tprod ℂ (v l), fun l => ?_, fun l h => ?_,
    fun h hh => ?_⟩
  · rw [Formalism.IndefR.Mult.mem_multT, LinearEquiv.symm_apply_apply]
    exact Submodule.subset_span (hT l)
  · rw [hval]; exact hI _ (hR l) h
  · simp only [hval]
    have hIl : ∀ l, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * Tm l (v l) g) (G.meas t i j).fd
        (G.meas t i j).ν := fun l => hI _ (hR l) h
    rw [← integral_finsetSum _ fun l _ => hIl l, ← integral_sub (hint h) (integrable_finsetSum _ fun l _ => hIl l)]
    have hb : ∀ g ∈ (G.meas t i j).fd, ‖thetaKO (G.X i j).ω h g Φ * φ g -
        ∑ l, thetaKO (G.X i j).ω h g Φ * Tm l (v l) g‖ ≤ |K| * δ := by
      intro g _
      rw [← Finset.mul_sum, ← mul_sub, norm_mul]
      have h1 := hK' h hh g
      have h2 := hap g
      have hq := (pow_pos (quotHeight_pos (G.V i j).V g) a).le
      calc ‖thetaKO (G.X i j).ω h g Φ‖ * ‖φ g - ∑ l, Tm l (v l) g‖
          ≤ |K| * quotHeight (G.V i j).V g ^ a * ‖φ g - ∑ l, Tm l (v l) g‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = |K| * (‖φ g - ∑ l, Tm l (v l) g‖ * quotHeight (G.V i j).V g ^ a) := by ring
        _ ≤ |K| * δ := mul_le_mul_of_nonneg_left h2 (abs_nonneg K)
    refine (norm_setIntegral_le_of_norm_le_const hfin hb).trans_lt ?_
    rw [← hvol]
    have e : |K| * δ * vol ≤ (|K| + 1) * (vol + 1) * δ := by
      have : |K| * vol ≤ (|K| + 1) * (vol + 1) := by nlinarith [abs_nonneg K]
      nlinarith
    have e2 : (|K| + 1) * (vol + 1) * δ = ε / 2 := by
      rw [hδ]; field_simp
    linarith
end GlobalTheory.CuspApproxX
namespace GlobalTheory.CuspApproxX
theorem cusp_form_approx_by_lift_of_type : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.V i j).Maps) (v : Fin n → SmT (G.V i j).M), (∀ l, F l ∈ (G.V i j).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * F l (v l) g) (G.meas t i j).fd (G.meas t i j).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F l (v l) g ∂(G.meas t i j).ν‖ < ε :=
  _root_.GlobalTheory.CuspApproxX.cusp_form_approx_by_lift _root_.GlobalTheory.T.pure_cusp_form_approx_of_twist
end GlobalTheory.CuspApproxX
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_forms_approximated_by_theta_lifts : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.V i j).Maps) (v : Fin n → SmT (G.V i j).M), (∀ l, F l ∈ (G.V i j).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * F l (v l) g) (G.meas t i j).fd (G.meas t i j).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F l (v l) g ∂(G.meas t i j).ν‖ < ε := by
  first | exact @_root_.GlobalTheory.CuspApproxX.cusp_form_approx_by_lift_of_type | exact _root_.GlobalTheory.CuspApproxX.cusp_form_approx_by_lift_of_type | (intros; apply _root_.GlobalTheory.CuspApproxX.cusp_form_approx_by_lift_of_type <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftsDenseInCuspForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.ThetaApproxX
theorem upperArrow_approx : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ F : (G.V i j).Maps, F ∈ (G.V i j).Cusp R.θ → ∀ v : SmT (G.V i j).M, (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * F v g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (f : Fin n → (WO (G.V (i + 1) j).V (G.V i j).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j)), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l)) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F v g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l) (p l)) * F v g ∂(G.meas t i j).ν‖ < ε := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ F hF v hint C hC ε hε
  have hw := (hG.arrows.X i j hi hj).weil
  have hθ : IsInfFam R.θ := hRB.inf
  have hψ : IsStdChar D R.ψ (-1) := hw.std
  let AF := GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel (G.V (i + 1) j).M)
  let BF := GlobalTheory.ChainFr.Fr.ofModel (G.V i j).M
  have hcart : ∀ τ, AF.cart τ = GlobalTheory.Grid.cartS true (G.V (i + 1) j) τ := fun τ => GlobalTheory.PairLift.cart_frSgn true _ τ
  have hpt : ∀ f P, GlobalTheory.ChainFr.ptF R.ψ R.θ AF BF f P = GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f P := by
    intro f P
    unfold GlobalTheory.ChainFr.ptF GlobalTheory.Grid.fock
    rw [show AF.cart = GlobalTheory.Grid.cartS true (G.V (i + 1) j) from funext hcart]
    rfl
  have hfin : ∀ f, GlobalTheory.ChainFr.IsVacF R.ψ R.θ AF BF f → GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f := by
    intro f hf
    refine ⟨hf.1, fun τ => ?_⟩
    have := hf.2 τ
    rwa [hcart τ] at this
  have hk : ∀ h g f, thetaKO (G.X i j).ω h g f =
      thetaKO ((G.X i j).ω.toSgn true) ((GlobalTheory.Grid.ofSgn true _).symm h) g f := by
    intro h g f
    simp only [thetaKO, GlobalTheory.Grid.WRep.toSgn, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply,
      MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, MonoidHom.id_apply]
  obtain ⟨μW, 𝓕W, hμW⟩ := GlobalTheory.Size.exists_isCovolOne (D := D) (V := GlobalTheory.Grid.neg (G.V (i + 1) j).V) (W := (G.V i j).V)
  obtain ⟨U, hU, hΦU, hdense⟩ := GlobalTheory.FockDensity.fockDense D _ _ AF BF R.θ R.ψ hψ hθ μW 𝓕W hμW Φ hΦ
  obtain ⟨Aexp, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (GlobalTheory.Grid.neg (G.V (i + 1) j).V).rank (G.V i j).V.rank
  obtain ⟨Ck, hCk0, hCk⟩ := (H _ _ rfl rfl).real R.ψ hθ hU
  have hFr := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP.cuspRapidDecay D _ _ (G.V i j).M R.θ hθ ∅ 1 F hF v
  have hM := GlobalTheory.PairLift.haar_vert hRB hG t hi.le hj
  have : BorelSpace (GA D (G.V i j).V) := ⟨rfl⟩
  obtain ⟨Hh, hHh⟩ := hC.bddAbove_image
    ((GlobalTheory.Grow.continuous_height _).comp (GlobalTheory.Grid.continuous_ofSgn_symm true (G.V (i + 1) j).V)).continuousOn
  set Hq : ℝ := max Hh 1 with hHq
  have hHC : ∀ h ∈ C, GlobalTheory.Grow.height _ ((GlobalTheory.Grid.ofSgn true (G.V (i + 1) j).V).symm h) ≤ Hq :=
    fun h hh => (hHh ⟨h, hh, rfl⟩).trans (le_max_left _ _)
  have hq1 : (1 : ℝ) ≤ Hq := le_max_right _ _
  have hqm : AEStronglyMeasurable (fun g => ((GlobalTheory.Grow.quotHeight (G.V i j).V g ^ Aexp : ℝ) : ℂ))
      ((G.meas t i j).ν.restrict (G.meas t i j).fd) :=
    (Complex.continuous_ofReal.comp ((GlobalTheory.Grow.continuous_quotHeight _).pow Aexp)).aestronglyMeasurable
  have hQ : IntegrableOn ((fun g => ((GlobalTheory.Grow.quotHeight (G.V i j).V g ^ Aexp : ℝ) : ℂ)) * F v)
      (G.meas t i j).fd (G.meas t i j).ν :=
    hFr.2.2.integrableOn_mul_of_le hM.1 hM.2 hqm (C := 1) (A := Aexp) fun g => by
      rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _), one_mul]
  set K0 : ℝ := ∫ g in (G.meas t i j).fd,
    ‖((fun g => ((GlobalTheory.Grow.quotHeight (G.V i j).V g ^ Aexp : ℝ) : ℂ)) * F v) g‖ ∂(G.meas t i j).ν with hK0def
  have hK0 : 0 ≤ K0 := integral_nonneg fun _ => norm_nonneg _
  set M : ℝ := Ck * 2 ^ Aexp * Hq ^ Aexp * K0 with hMdef
  have hM0 : 0 ≤ M := by positivity
  set δ : ℝ := ε / (M + 1) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨g0, hg0, hg0U, hsob⟩ := hdense d (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
  obtain ⟨n, c, w, hsum⟩ := Submodule.mem_span_set'.1 hg0
  choose f₀ P hvac hlev heq using fun l => (w l).2
  refine ⟨n, f₀, fun l => c l • P l, fun l => hfin _ (hvac l), fun h hh => ?_⟩
  have hg0eq : g0 = ∑ l, GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f₀ l) (c l • P l) := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [heq l, hpt, map_smul]
  have hCA := (hL D hS G₀ Pl0 T A Ks R G hRB hG).X t i j hi hj
  have hintl : ∀ l, IntegrableOn (fun g => thetaKO (G.X i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f₀ l) (c l • P l)) * F v g)
      (G.meas t i j).fd (G.meas t i j).ν := fun l => by
    obtain ⟨F', -, hF'⟩ := hCA (f₀ l) (hfin _ (hvac l)) F hF
    exact (hF' (c l • P l) v h).1
  have hdiff : (∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F v g ∂(G.meas t i j).ν) -
      ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g
        (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f₀ l) (c l • P l)) * F v g ∂(G.meas t i j).ν =
      ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (Φ - g0) * F v g ∂(G.meas t i j).ν := by
    rw [← integral_finsetSum _ (fun l _ => hintl l),
      ← integral_sub (hint h) (integrable_finsetSum _ fun l _ => hintl l)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [thetaKO, hg0eq, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_mul]
  rw [hdiff]
  have hΞ : Φ - g0 ∈ GlobalTheory.Size.thetaLevel R.ψ _ _ U := sub_mem hΦU hg0U
  obtain ⟨hsT, hbd⟩ := hCk _ _ _ hw μW 𝓕W hμW (Φ - g0) hΞ
  set s : ℝ := (GlobalTheory.Size.sobO R.ψ R.θ μW 𝓕W d (Φ - g0)).toReal with hsdef
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hs : s ≤ δ := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsob.le
    rwa [ENNReal.toReal_ofReal hδ.le] at this
  set h' := (GlobalTheory.Grid.ofSgn true (G.V (i + 1) j).V).symm h with hh'
  have hpt' : ∀ g, ‖thetaKO (G.X i j).ω h g (Φ - g0)‖ ≤
      Ck * s * Hq ^ Aexp * 2 ^ Aexp * GlobalTheory.Grow.quotHeight _ g ^ Aexp := by
    intro g
    have hinv : ∀ γ ∈ GQ (G.V i j).V, ∀ g, thetaKO (G.X i j).ω h (γ * g) (Φ - g0) = thetaKO (G.X i j).ω h g (Φ - g0) := by
      intro γ hγ g
      rw [hk, hk]
      exact GlobalTheory.Chain.LiftConv.thetaKO_left hw hΞ.1 h' γ hγ g
    have hb : ∀ g, ‖thetaKO (G.X i j).ω h g (Φ - g0)‖ ≤
        (Ck * s * GlobalTheory.Grow.height _ h' ^ Aexp) * GlobalTheory.Grow.height _ g ^ Aexp := by
      intro g
      have := hbd h' g
      rw [mul_pow, ← mul_assoc] at this
      rw [hk]
      exact this
    refine (GlobalTheory.Grow.norm_le_quotHeight_pow hinv hb g).trans ?_
    have h1 : GlobalTheory.Grow.height _ h' ^ Aexp ≤ Hq ^ Aexp :=
      pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ h').le (hHC h hh) _
    have h2 : 0 ≤ GlobalTheory.Grow.quotHeight (G.V i j).V g ^ Aexp := pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _
    have h3 : 0 ≤ Ck * s := mul_nonneg hCk0 hs0
    have h4 : Ck * s * GlobalTheory.Grow.height _ h' ^ Aexp ≤ Ck * s * Hq ^ Aexp := mul_le_mul_of_nonneg_left h1 h3
    have h5 : (0 : ℝ) ≤ 2 ^ Aexp := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h4 (mul_nonneg h5 h2)]
  calc ‖∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (Φ - g0) * F v g ∂(G.meas t i j).ν‖
      ≤ ∫ g in (G.meas t i j).fd, (Ck * s * Hq ^ Aexp * 2 ^ Aexp) *
          ‖((fun g => ((GlobalTheory.Grow.quotHeight (G.V i j).V g ^ Aexp : ℝ) : ℂ)) * F v) g‖ ∂(G.meas t i j).ν := by
        refine norm_integral_le_of_norm_le (hQ.norm.const_mul _) (Filter.Eventually.of_forall fun g => ?_)
        rw [norm_mul, Pi.mul_apply, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _)]
        calc ‖thetaKO (G.X i j).ω h g (Φ - g0)‖ * ‖F v g‖
            ≤ (Ck * s * Hq ^ Aexp * 2 ^ Aexp * GlobalTheory.Grow.quotHeight _ g ^ Aexp) * ‖F v g‖ :=
              mul_le_mul_of_nonneg_right (hpt' g) (norm_nonneg _)
          _ = _ := by ring
    _ = (Ck * s * Hq ^ Aexp * 2 ^ Aexp) * K0 := integral_const_mul _ _
    _ ≤ (Ck * δ * Hq ^ Aexp * 2 ^ Aexp) * K0 := by gcongr
    _ = δ * M := by rw [hMdef]; ring
    _ < ε := by
        rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith
end GlobalTheory.ThetaApproxX
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lifts_dense_in_cusp_forms : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ F : (G.V i j).Maps, F ∈ (G.V i j).Cusp R.θ → ∀ v : SmT (G.V i j).M, (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * F v g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (f : Fin n → (WO (G.V (i + 1) j).V (G.V i j).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j)), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l)) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F v g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l) (p l)) * F v g ∂(G.meas t i j).ν‖ < ε := by
  first | exact @_root_.GlobalTheory.ThetaApproxX.upperArrow_approx | exact _root_.GlobalTheory.ThetaApproxX.upperArrow_approx | (intros; apply _root_.GlobalTheory.ThetaApproxX.upperArrow_approx <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.CuspTypeApproxX
theorem cuspType_lift_approx_fockSpace : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V (i + 1) j).V (G.V i j).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j)) (F : Fin n → (G.V i j).Maps) (v : Fin n → SmT (G.V i j).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l)) ∧ (∀ l, F l ∈ (G.V i j).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l) (p l)) * F l (v l) g ∂(G.meas t i j).ν‖ < δ := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC δ hδ
  obtain ⟨m, F, v, hF, hFi, hA⟩ := _root_.GlobalTheory.T.cusp_forms_approximated_by_theta_lifts hL hP D hS G₀ Pl0 T A Ks R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC (δ / 2) (by positivity)
  have hB := fun k : Fin m => _root_.GlobalTheory.T.theta_lifts_dense_in_cusp_forms hL hP D hS G₀ Pl0 T A Ks R G hRB hG t i j hi hj Φ hΦ (F k) (hF k) (v k) (hFi k) C hC
    (δ / (2 * (m + 1))) (by positivity)
  choose n f p hf hBk using hB
  refine ⟨∑ k, n k, fun l => f (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2,
    fun l => p (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2, fun l => F (finSigmaFinEquiv.symm l).1,
    fun l => v (finSigmaFinEquiv.symm l).1, fun l => hf _ _, fun l => hF _, fun h hh => ?_⟩
  exact norm_sub_sum_sigma_lt (J := fun k q => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f k q) (p k q)) * F k (v k) g ∂(G.meas t i j).ν) _ _ _ hδ
    (hA h hh) fun k => hBk k h hh
end GlobalTheory.CuspTypeApproxX
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_type_approximation_by_fock_lift : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V (i + 1) j).V (G.V i j).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j)) (F : Fin n → (G.V i j).Maps) (v : Fin n → SmT (G.V i j).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l)) ∧ (∀ l, F l ∈ (G.V i j).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l) (p l)) * F l (v l) g ∂(G.meas t i j).ν‖ < δ := by
  first | exact @_root_.GlobalTheory.CuspTypeApproxX.cuspType_lift_approx_fockSpace | exact _root_.GlobalTheory.CuspTypeApproxX.cuspType_lift_approx_fockSpace | (intros; apply _root_.GlobalTheory.CuspTypeApproxX.cuspType_lift_approx_fockSpace <;> assumption)
end
