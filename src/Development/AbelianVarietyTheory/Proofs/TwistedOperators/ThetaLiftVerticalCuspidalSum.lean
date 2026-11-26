module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentreEigenThetaFunctionFiniteSumFockPolynomials

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealCentralCharacterDefiniteVertexMultipli
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealCentralCharacterDefiniteVertexMultipli
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DefCenChar

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

theorem unframe_mem_UH {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {u : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hu : u ∈ Formalism.MainNotions.S.UJset (M.ε τ)) :
    (M.fr τ)⁻¹ * u * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hJ : uᴴ * Formalism.REAL.Jm (M.ε τ) * u = Formalism.REAL.Jm (M.ε τ) := hu
  have e1 : M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ) = u * M.fr τ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  change ((M.fr τ)⁻¹ * u * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * u * M.fr τ) = gramAt D V τ
  rw [← M.fr_gram τ]
  calc ((M.fr τ)⁻¹ * u * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * ((M.fr τ)⁻¹ * u * M.fr τ)
      = (M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ))ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ)) := by
        rw [Matrix.conjTranspose_mul (M.fr τ)]; simp only [Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ := by
        rw [e1, Matrix.conjTranspose_mul]
        calc (M.fr τ)ᴴ * uᴴ * Formalism.REAL.Jm (M.ε τ) * (u * M.fr τ) = (M.fr τ)ᴴ * (uᴴ * Formalism.REAL.Jm (M.ε τ) * u) * M.fr τ := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hJ]

theorem rep_scalar {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)]
    {a : Matrix (Fin V.rank) (Fin V.rank) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), g * a = a * g) : ∃ c : ℂ, ∀ w, M.rep τ a w = c • w := by
  haveI : Nontrivial (M.H τ) := (M.ds τ).2.1
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  let A : Module.End ℂ (M.H τ) := (M.rep τ a : M.H τ →ₗ[ℂ] M.H τ)
  obtain ⟨c, hcA⟩ := Module.End.exists_eigenvalue A
  refine ⟨c, fun w => ?_⟩
  have hirr := (M.ds τ).2.2.2.1
  have hinv : ∀ u ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ v ∈ A.eigenspace c, M.σ τ u v ∈ A.eigenspace c := by
    intro u hu v hv
    have hg := unframe_mem_UH M τ hu
    have e : M.σ τ u = M.rep τ ((M.fr τ)⁻¹ * u * M.fr τ) := by
      unfold DSModel.rep
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [e]
    show M.rep τ a (M.rep τ _ v) = c • M.rep τ _ v
    rw [← GlobalTheory.ConjMult.rep_mul M τ _ ha _ hg, ← hc _ hg, GlobalTheory.ConjMult.rep_mul M τ _ hg _ ha]
    have hv' : M.rep τ a v = c • v := hv
    rw [hv', map_smul]
  rcases hirr (A.eigenspace c) (Submodule.closed_of_finiteDimensional _) hinv with h | h
  · exact absurd h hcA
  · have hw : w ∈ A.eigenspace c := h ▸ Submodule.mem_top
    exact (Module.End.mem_eigenspace_iff).1 hw

theorem infMat_comm {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {z : GA D V} (hzc : z ∈ Subgroup.center (GA D V))
    (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    g * infMat D.sp.cm.sig V.gram (θ τ) z = infMat D.sp.cm.sig V.gram (θ τ) z * g := by
  have e := congrArg (infMat D.sp.cm.sig V.gram (θ τ)) (Subgroup.mem_center_iff.1 hzc (atTau θ V τ g))
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul,
    (GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg).2.1] at e
  exact e

theorem rTr_atTau_of_scalar {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {c : ℂ} (hc : ∀ w, M.rep τ g w = c • w) (v : M.Vec) :
    rTr V (atTau θ V τ g) (T v) = c • T v := by
  classical
  have e := hT.equiv τ g hg v (c • v τ) (by rw [hc]; rfl)
  rw [← e, T.map_update_smul, Function.update_eq_self]
  rfl

theorem rTr_realAll {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T)
    (Mz : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hM : ∀ ρ, Mz ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ))
    (c : D.what₂.Tau → ℂ) (hc : ∀ ρ w, M.rep ρ (Mz ρ) w = c ρ • w) (v : M.Vec) :
    rTr V (GlobalTheory.RowReal.realAll θ V Mz) (T v) = (∏ ρ, c ρ) • T v := by
  classical
  have key : ∀ s : Finset D.what₂.Tau,
      rTr V (GlobalTheory.RowReal.realAll θ V (fun ρ => if ρ ∈ s then Mz ρ else 1)) (T v) = (∏ ρ ∈ s, c ρ) • T v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : (fun ρ : D.what₂.Tau => if ρ ∈ (∅ : Finset D.what₂.Tau) then Mz ρ else 1) = 1 := by
        funext ρ; simp
      rw [e, GlobalTheory.RowReal.realAll_one hθ, Finset.prod_empty, one_smul]
      funext x; simp [rTr]
    | insert τ s hτ ih =>
      have hMs : ∀ ρ, (fun ρ => if ρ ∈ insert τ s then Mz ρ else 1) ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := fun ρ => by
        dsimp only
        split_ifs
        · exact hM ρ
        · exact GlobalTheory.PointAtPlaceHom.one_mem_UH _
      rw [GlobalTheory.RowReal.realAll_eq_atTau_mul hθ hMs τ]
      have e : Function.update (fun ρ => if ρ ∈ insert τ s then Mz ρ else 1) τ 1 =
          fun ρ => if ρ ∈ s then Mz ρ else 1 := by
        funext ρ
        by_cases h : ρ = τ
        · subst h; simp [hτ]
        · rw [Function.update_of_ne h]; simp [Finset.mem_insert, h]
      rw [e, Finset.prod_insert hτ]
      simp only [Finset.mem_insert_self, if_true]
      funext x
      have i1 := congrFun ih (x * atTau θ V τ (Mz τ))
      have i2 := congrFun (rTr_atTau_of_scalar hT τ (hM τ) (hc τ) v) x
      simp only [rTr, Pi.smul_apply, smul_eq_mul] at i1 i2 ⊢
      rw [← mul_assoc, i1, i2]
      ring
  have e : (fun ρ : D.what₂.Tau => if ρ ∈ (Finset.univ : Finset D.what₂.Tau) then Mz ρ else 1) = Mz := by
    funext ρ; simp
  have := key Finset.univ
  rwa [e] at this

theorem cusp_hasCen : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ν : ℕ) (P : D.what₂.Tau → SPar), N.Is ν 0 P → ∃ χ : GA D N.V → ℂ, ∀ (F : N.Cusp θ) (v : SmT N.M), GlobalTheory.SeeSaw.HasCen N.V χ (F.1 v) := by
  intro D θ hθ N ν P hN
  have hs : N.V.SigOK := hN.sigOK
  have hd : N.V.IsDefinite := fun τ => Or.inl (by rw [hN.sig, hN.rank]; simp)
  have hfd : ∀ τ, FiniteDimensional ℂ (N.M.H τ) := fun τ => GlobalTheory.DefiniteEnd.finiteDimensional_model hs hd N.M τ
  have key : ∀ (z : GA D N.V) (ρ : D.what₂.Tau), ∃ c : ℂ, z ∈ Subgroup.center (GA D N.V) →
      ∀ w, N.M.rep ρ (infMat D.sp.cm.sig N.V.gram (θ ρ) z) w = c • w := by
    intro z ρ
    by_cases hz : z ∈ Subgroup.center (GA D N.V)
    · haveI := hfd ρ
      obtain ⟨c, hc⟩ := rep_scalar N.M ρ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ N.V z ρ)
        (fun g hg => infMat_comm hθ hz ρ hg)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose c hc using key
  refine ⟨fun z => ∏ ρ, c z ρ, fun F v z hz hzc h => ?_⟩
  have hreal : ∀ T : MMap N.M, IsMultMap θ N.M ∅ 1 T → ∀ (u : N.M.Vec) (g : GA D N.V),
      T u (g * z) = (∏ ρ, c z ρ) * T u g := by
    intro T hT u g
    have e : GlobalTheory.RowReal.realAll θ N.V (fun ρ => infMat D.sp.cm.sig N.V.gram (θ ρ) z) = z :=
      GlobalTheory.RowReal.realAll_eq hθ (fun ρ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ N.V z ρ) ⟨hz, fun ρ => rfl⟩
    have := rTr_realAll hθ hT _ (fun ρ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ N.V z ρ) (c z)
      (fun ρ => hc z ρ hzc) u
    rw [e] at this
    exact congrFun this g
  have key2 : ∀ T ∈ Mult θ N.M ∅ 1, ∀ (x : SmT N.M) (g : GA D N.V),
      PiTensorProduct.lift T x (g * z) = (∏ ρ, c z ρ) * PiTensorProduct.lift T x g := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      intro x
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        intro g
        simp only [map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul]
        rw [hreal T hT f g]
        ring
      | add a b ha hb =>
        intro g
        simp only [map_add (f := _), Pi.add_apply]
        rw [ha g, hb g]
        ring
    | zero => intro x g; simp
    | add T T' _ _ h1 h2 =>
      intro x g
      simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply]
      rw [h1 x g, h2 x g]
      ring
    | smul a T _ h =>
      intro x g
      simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      rw [h x g]
      ring
  have hm : PiTensorProduct.lift.symm F.1 ∈ Mult θ N.M ∅ 1 := (mem_multT θ N.M ∅ 1 F.1).1 F.2
  have := key2 _ hm v h
  rw [LinearEquiv.apply_symm_apply] at this
  exact this

end GlobalTheory.DefCenChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealCentralCharacterDefiniteVertexMultipliStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realCentralCharacter_definiteVertexMultiplicity : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ν : ℕ) (P : D.what₂.Tau → SPar), N.Is ν 0 P → ∃ χ : GA D N.V → ℂ, ∀ (F : N.Cusp θ) (v : SmT N.M), GlobalTheory.SeeSaw.HasCen N.V χ (F.1 v) := by
  first | exact @GlobalTheory.DefCenChar.cusp_hasCen | exact GlobalTheory.DefCenChar.cusp_hasCen | (intros; apply GlobalTheory.DefCenChar.cusp_hasCen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftRealCentreAverageEigenvector
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftRealCentreAverageEigenvector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CenAvgOne

open scoped ContDiff

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

def avg1 {K : Type} [MeasurableSpace K] (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (μ : Measure K)
    (j : K → GA D S) (c : K → ℂ) (Φ : WO S T → ℂ) : WO S T → ℂ :=
  fun w => ∫ k, c k * om (j k, 1) Φ w ∂μ

theorem continuous_fam (hom : IsWeilDatumO ψ S T χS χT om) {Φ : WO S T → ℂ} (hΦ : IsThetaFunO ψ S T Φ) {K : Type}
    [TopologicalSpace K] {p : K → GA D S × GA D T} (hp : Continuous p) :
    Continuous fun q : K × WO S T => om (p q.1) Φ q.2 :=
  (GlobalTheory.ThetaJointCont.continuous_om_oriented hom hΦ).comp ((hp.comp continuous_fst).prodMk continuous_snd)

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {j : K → GA D S} {c : K → ℂ} {Φ : WO S T → ℂ}

theorem isThetaFunction_average_compactFamily_weilTranslates (hom : IsWeilDatumO ψ S T χS χT om) (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC S)
    (hc : Continuous c) (hΦ : IsThetaFunO ψ S T Φ) : IsThetaFunO ψ S T (avg1 om μ j c Φ) := by
  have hψ := hom.std
  have hp : Continuous fun k => (j k, (1 : GA D T)) := hjc.prodMk continuous_const
  refine ⟨fun γ w => ?_, ?_, ?_, ?_⟩
  · simp only [avg1]
    rw [← integral_const_mul]
    congr 1
    funext k
    rw [(hom.om_pres _ _ hΦ).quasi]
    ring
  · obtain ⟨U, hU, h⟩ := hΦ.level
    refine ⟨U, hU, fun u hu hu0 => ?_⟩
    funext w
    simp only [heisO, avg1]
    rw [← integral_const_mul]
    congr 1
    funext k
    have := congrFun (hom.om_heis (j k) 1 u Φ hΦ) w
    rw [h u hu hu0, GlobalTheory.FrComb.actO_real (hj k) (GinfC T).one_mem hu0] at this
    rw [this, heisO]
    ring
  · exact GlobalTheory.AvgFam.continuous_avg μ (F := fun k w => c k * om (j k, 1) Φ w)
      ((hc.comp continuous_fst).mul (continuous_fam hom hΦ hp))
  · let gen : Set (K → WO S T → ℂ) := {F | ∃ (c : K → ℂ) (G : WO S T → ℂ), Continuous c ∧ IsThetaFunO ψ S T G ∧
      F = fun k => c k • om (j k, 1) G}
    have h1 : ∀ F ∈ Submodule.span ℂ gen, Continuous fun q : K × WO S T => F q.1 q.2 := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem F h =>
        obtain ⟨c, G, hc, hG, rfl⟩ := h
        exact (hc.comp continuous_fst).mul (continuous_fam hom hG hp)
      | zero => exact continuous_const
      | add F F' _ _ h h' => exact h.add h'
      | smul a F _ h => exact h.const_smul a
    have h2 : ∀ F ∈ Submodule.span ℂ gen, ∀ k, IsThetaFunO ψ S T (F k) := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem F h =>
        obtain ⟨c, G, hc, hG, rfl⟩ := h
        exact fun k => GlobalTheory.WeilVacMove.isTheta_smul _ (hom.om_pres _ _ hG)
      | zero => exact fun _ => GlobalTheory.WeilVacMove.isTheta_zero
      | add F F' _ _ h h' => exact fun k => GlobalTheory.WeilVacMove.isTheta_add (h k) (h' k)
      | smul a F _ h => exact fun k => GlobalTheory.WeilVacMove.isTheta_smul a (h k)
    have h3 : ∀ F ∈ Submodule.span ℂ gen, ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) →
        (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k)) ∈ Submodule.span ℂ gen := by
      intro F hF M hM hM0
      induction hF using Submodule.span_induction with
      | mem F h =>
        obtain ⟨c, G, hc, hG, rfl⟩ := h
        obtain ⟨m, N, e, hN, hN0, he, hexp⟩ := GlobalTheory.HeisLineComb.dLine_om_comb D ψ S T χS χT om hom M hM hM0
        have key : (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (c k • om (j k, 1) G)) =
            ∑ i, fun k => (c k * e i (j k, 1)) • om (j k, 1) (GlobalTheory.WeilVacMove.dLine ψ S T (N i) G) := by
          funext k
          rw [GlobalTheory.CenAvg.dLine_smul, hexp _ _ hG, Finset.smul_sum, Finset.sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul]
        rw [key]
        exact Submodule.sum_mem _ fun i _ => Submodule.subset_span
          ⟨_, _, hc.mul ((he i).comp hp), (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ (hN i) (hN0 i) hG).2, rfl⟩
      | zero =>
        have : (fun k : K => GlobalTheory.WeilVacMove.dLine ψ S T M ((0 : K → WO S T → ℂ) k)) = 0 := by
          funext k x
          simp [GlobalTheory.WeilVacMove.dLine, heisO]
        rw [this]
        exact Submodule.zero_mem _
      | add F F' hF hF' h h' =>
        have : (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M ((F + F') k)) =
            (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k)) + fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F' k) :=
          funext fun k => GlobalTheory.CenAvg.dLine_add hψ hM hM0 (h2 F hF k) (h2 F' hF' k)
        rw [this]
        exact Submodule.add_mem _ h h'
      | smul a F _ h =>
        have : (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M ((a • F) k)) = a • fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k) :=
          funext fun k => GlobalTheory.CenAvg.dLine_smul M a (F k)
        rw [this]
        exact Submodule.smul_mem _ a h
    intro n L hL hL0 w
    have := GlobalTheory.ThetaAvgSmooth.avg_smooth D ψ hψ S T K μ (Submodule.span ℂ gen : Set _) h1 h2 h3 _
      (Submodule.subset_span (show _ ∈ gen from ⟨c, Φ, hc, hΦ, rfl⟩)) n L hL hL0 w
    simpa only [avg1, Pi.smul_apply, smul_eq_mul] using this

theorem weilOperator_average_eq_average_translated [SecondCountableTopology K] [IsTopologicalGroup (GA D S)] [IsTopologicalGroup (GA D T)]
    (hom : IsWeilDatumO ψ S T χS χT om) (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC S)
    (hc : Continuous c) (hΦ : IsThetaFunO ψ S T Φ) (p : GA D S × GA D T) (x : WO S T) :
    om p (avg1 om μ j c Φ) x = ∫ k, c k * om (p * (j k, 1)) Φ x ∂μ := by
  have hp : Continuous fun k => (j k, (1 : GA D T)) := hjc.prodMk continuous_const
  have hm : ∀ k, om p (om (j k, 1) Φ) = om (p * (j k, 1)) Φ := fun k => by
    rw [map_mul, Module.End.mul_apply]
  have := GlobalTheory.CenAvg.om_integral μ hom hc (F := fun k => om (j k, 1) Φ) p (fun k => hom.om_pres _ _ hΦ)
    (continuous_fam hom hΦ hp) (by simp only [hm]; exact continuous_fam hom hΦ (continuous_const.mul hp))
    (isThetaFunction_average_compactFamily_weilTranslates μ hom hjc hj hc hΦ) x
  simp only [hm] at this
  exact this

end GlobalTheory.CenAvgOne

namespace GlobalTheory.CenAvgOne

theorem exists_central_average_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → S.SigOK → S.IsDefinite → ∀ (ν : Measure (GA D S)) (fd : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) fd ν → ∀ (χ φ : GA D S → ℂ), GlobalTheory.SeeSaw.HasCen S χ φ → GlobalTheory.Unf.IsContAut S φ → ∀ Φ, IsThetaFunO ψ S T Φ → (∀ h, IntegrableOn (fun g => thetaKO om g h Φ * φ g) fd ν) → ∃ Φ', IsThetaFunO ψ S T Φ' ∧ (∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → om (z, 1) Φ' = (χ z)⁻¹ • Φ') ∧ ∀ h, ∫ g in fd, thetaKO om g h Φ * φ g ∂ν = ∫ g in fd, thetaKO om g h Φ' * φ g ∂ν := by
  intro D ψ S T χS χT om hom hsig hdef ν fd hν hfd χ φ hcen hφ Φ hΦ hint
  by_cases hz : φ = 0
  · subst hz
    exact ⟨0, GlobalTheory.WeilVacMove.isTheta_zero, fun z _ _ => by simp, fun h => by simp⟩
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D S
  obtain ⟨j1, -, -, -, -, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D T
  let Z : Subgroup (GA D S) := GinfC S ⊓ Subgroup.center (GA D S)
  have hcl : IsClosed (Subgroup.center (GA D S) : Set (GA D S)) := by
    have : (Subgroup.center (GA D S) : Set (GA D S)) = ⋂ g, {a | g * a = a * g} := by
      ext a
      simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_iInter fun g => isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  haveI : CompactSpace Z :=
    isCompact_iff_compactSpace.mp ((Formalism.IndefR.Eqv.isCompact_GinfC hsig hdef).inter_right hcl)
  let m : Measure Z := GlobalTheory.haarProb Z
  obtain ⟨h₀, hh₀⟩ := Function.ne_iff.1 hz
  have hh : φ h₀ ≠ 0 := hh₀
  have hmul : ∀ a b : Z, χ (a * b : Z) = χ a * χ b := by
    intro a b
    apply mul_right_cancel₀ hh
    rw [← hcen _ (a * b).2.1 (a * b).2.2, Subgroup.coe_mul, ← mul_assoc, hcen _ b.2.1 b.2.2, hcen _ a.2.1 a.2.2]
    ring
  have hone : χ 1 = 1 := by
    apply mul_right_cancel₀ hh
    rw [← hcen _ (one_mem _) (one_mem _), mul_one, one_mul]
  have hcont : Continuous fun a : Z => χ a := by
    have : (fun a : Z => χ a) = fun a : Z => φ (h₀ * a) / φ h₀ := by
      funext a
      rw [hcen _ a.2.1 a.2.2, mul_div_cancel_right₀ _ hh]
    rw [this]
    exact (hφ.2.comp (continuous_const.mul continuous_subtype_val)).div_const _
  have hj : ∀ a : Z, (a : GA D S) ∈ GinfC S := fun a => a.2.1
  refine ⟨avg1 om m Subtype.val (fun a => χ a) Φ, isThetaFunction_average_compactFamily_weilTranslates m hom continuous_subtype_val hj hcont hΦ,
    fun a ha1 ha2 => ?_, fun h => ?_⟩
  · let a' : Z := ⟨a, ha1, ha2⟩
    have hne : χ a ≠ 0 := by
      intro h0
      have := hmul a'⁻¹ a'
      rw [inv_mul_cancel, OneMemClass.coe_one, hone] at this
      change 1 = χ (a'⁻¹ : Z) * χ a at this
      rw [h0, mul_zero] at this
      exact one_ne_zero this
    funext u
    rw [weilOperator_average_eq_average_translated m hom continuous_subtype_val hj hcont hΦ]
    simp only [Pi.smul_apply, smul_eq_mul, avg1]
    rw [← integral_mul_left_eq_self (μ := m) (fun b : Z => χ b * om ((b : GA D S), 1) Φ u) a', ← integral_const_mul]
    congr 1
    funext b
    rw [hmul a' b]
    change _ = (χ a)⁻¹ * (χ a * χ b * om ((a * b : GA D S), 1) Φ u)
    rw [Prod.mk_mul_mk, mul_one]
    field_simp
  · haveI : Countable (GQ S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig S.gram
    haveI : ν.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds S ν hν
    have hF_inv : ∀ γ ∈ GQ S, ∀ g, thetaKO om (γ * g) h Φ * φ (γ * g) = thetaKO om g h Φ * φ g := by
      intro γ hγ g
      have : om (γ * g, h) Φ 0 = om (g, h) Φ 0 := by
        rw [show ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) by rw [Prod.mk_mul_mk, one_mul], map_mul,
          Module.End.mul_apply, hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hΦ)]
      simp only [thetaKO, this, hφ.1 γ hγ g]
    have hF_cont : Continuous fun g => thetaKO om g h Φ * φ g :=
      ((hom.om_cont Φ hΦ 0).comp (continuous_id.prodMk continuous_const)).mul hφ.2
    have key : ∀ g, thetaKO om g h (avg1 om m Subtype.val (fun a => χ a) Φ) * φ g =
        ∫ k : Z, thetaKO om (g * k) h Φ * φ (g * k) ∂m := by
      intro g
      unfold thetaKO
      rw [weilOperator_average_eq_average_translated m hom continuous_subtype_val hj hcont hΦ, ← integral_mul_const]
      congr 1
      funext k
      rw [Prod.mk_mul_mk, mul_one, hcen _ k.2.1 k.2.2]
      ring
    simp_rw [key]
    exact (GlobalTheory.Chain.IoLift.AvgLift.setIntegral_average (GQ S) ν hfd m continuous_subtype_val
      (Φ := fun g => thetaKO om g h Φ * φ g) hF_inv hF_cont (hint h)).symm

end GlobalTheory.CenAvgOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftRealCentreAverageEigenvectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaLift_realCentre_average_eigenvector : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → S.SigOK → S.IsDefinite → ∀ (ν : Measure (GA D S)) (fd : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) fd ν → ∀ (χ φ : GA D S → ℂ), GlobalTheory.SeeSaw.HasCen S χ φ → GlobalTheory.Unf.IsContAut S φ → ∀ Φ, IsThetaFunO ψ S T Φ → (∀ h, IntegrableOn (fun g => thetaKO om g h Φ * φ g) fd ν) → ∃ Φ', IsThetaFunO ψ S T Φ' ∧ (∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → om (z, 1) Φ' = (χ z)⁻¹ • Φ') ∧ ∀ h, ∫ g in fd, thetaKO om g h Φ * φ g ∂ν = ∫ g in fd, thetaKO om g h Φ' * φ g ∂ν := by
  first | exact @GlobalTheory.CenAvgOne.exists_central_average_one | exact GlobalTheory.CenAvgOne.exists_central_average_one | (intros; apply GlobalTheory.CenAvgOne.exists_central_average_one <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColFockRed

open GlobalTheory.Grid

theorem isContAut_cusp {D : D7} {θ : InfFam D} {N : Node D} (F : N.Cusp θ) (x : SmT N.M) :
    GlobalTheory.Unf.IsContAut N.V (F.1 x) := by
  have sm : ∀ {f : GA D N.V → ℂ}, GlobalTheory.Unf.IsContAut N.V f → ∀ c : ℂ, GlobalTheory.Unf.IsContAut N.V (c • f) := fun hf c =>
    ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩
  have ad : ∀ {f g : GA D N.V → ℂ}, GlobalTheory.Unf.IsContAut N.V f → GlobalTheory.Unf.IsContAut N.V g → GlobalTheory.Unf.IsContAut N.V (f + g) :=
    fun hf hg => ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩
  obtain ⟨G, hG⟩ := F
  show GlobalTheory.Unf.IsContAut N.V (G x)
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact sm ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add (f := _)]; exact ad hx hy
  | zero => rw [map_zero, LinearMap.zero_apply]; exact ⟨fun _ _ _ => rfl, continuous_const⟩
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact ad (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact sm (h x) c

theorem xp_is {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GlobalTheory.Grid.GridPre R}
    (hG : G.Is) (k : ℕ) (hk : k ≤ D.R.m) : ∃ ν P, (G.Xp k).Is ν 0 P := by
  cases k with
  | zero =>
    have h := hG.spaces.P D.R.m le_rfl
    rw [show (D.R.m - D.R.m + 1) / 2 = 0 by omega] at h
    exact ⟨_, _, h⟩
  | succ k => exact ⟨_, _, hG.spaces.X k hk⟩

theorem measDat_haar_fd {D : D7} {N : Node D} {m : N.MeasDat} {df : Prop} {K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))}
    (h : m.Is df K) : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
  by_cases hd : df
  · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
  · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩

theorem measX_haar_fd {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridPre R}
    (hG : G.Is) (j : ℕ) (hj : j ≤ D.R.m) :
    (G.measX j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.Xp j).V) (G.measX j).fd (G.measX j).ν := by
  cases j with
  | zero => exact measDat_haar_fd (hG.meas.P D.R.m le_rfl)
  | succ j => exact measDat_haar_fd (hG.meas.X j hj)

end GlobalTheory.ColFockRed
