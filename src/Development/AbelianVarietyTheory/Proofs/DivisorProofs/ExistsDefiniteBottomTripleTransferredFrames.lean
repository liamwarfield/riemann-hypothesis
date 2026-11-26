module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedUnitariesMovingBottomTriples
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstMemberMovedDatumSplittingScale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstMemberMovedDatumSplittingScale
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

theorem stdFst_actO {D : D7} {A WW : HSp D} (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E))
    (βA βA' : GL (Fin A.rank) (Lev.EAf D)) (βW βW' : GL (Fin WW.rank) (Lev.EAf D)) (g : GA D A) (h : GA D WW)
    (hfr : ∀ u : WO A WW, IsHalf e u → frMapO A WW βA' βW' (actO A WW g h u) = frMapO A WW βA βW u) (u : WO A WW) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA' βW' (actO A WW g h u) = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW u := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  by_cases hu : IsHalf e u
  · rw [hfr u hu]
    have hu' : IsHalf e (actO A WW g h u) := (GlobalTheory.SchrMove.isHalf_actO_iff g h u).2 hu
    by_cases hr : IsIntM (frMapO A WW βA βW u) ∧
        ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (frMapO A WW βA βW u i j)
    · rw [if_pos ⟨hu', hr⟩, if_pos ⟨hu, hr⟩]
    · rw [if_neg fun hh => hr hh.2, if_neg fun hh => hr hh.2]
  · rw [if_neg fun hh => hu ((GlobalTheory.SchrMove.isHalf_actO_iff g h u).1 hh.1), if_neg fun hh => hu hh.1]

theorem move_fst : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (h : GA D WW) (x y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A WW, IsHalf (Y.e t) u → frMapO A WW Y.rA.β Y.rW.β (actO A WW g h u) = frMapO A WW X.rA.β X.rW.β u) →
    IsThetaAt W.ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO W.ψ (GlobalTheory.Grid.neg A) WW) (Y.e t)
      (latO (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ fun _ => True) 1 Y.vac
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A WW
        X.rA.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) •
        Y.ω t (g⁻¹, h⁻¹) (Y.f t)) := by
  intro D T L sc G W i j A A' WW X Y hX hY t g h x y hsg hstg hdg hsh hsth hdh hfr
  classical
  have hI := hY.is
  have hW : IsWeilDatumO W.ψ (GlobalTheory.Grid.neg A) WW (GlobalTheory.BotFrames.botBeta G i j)
      (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) ((Y.ω t).toSgn true) := hI.weil t
  have hSA : IsSelfDualC (GlobalTheory.Grid.neg A) Y.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hI.rigA.1
  have hSW : IsSelfDualC WW Y.rW.Λ := hI.rigW.1
  let g' : GA D (GlobalTheory.Grid.neg A) := (GlobalTheory.Grid.ofSgn true A).symm g
  have hL : ∀ u, u ∈ (latO (GlobalTheory.Grid.neg A) WW (Y.rA.Λ : Set (Fin A.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) ↔
      actO (GlobalTheory.Grid.neg A) WW g' h u ∈ (latO (GlobalTheory.Grid.neg A) WW (Y.rA.Λ : Set (Fin A.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) :=
    GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D (GlobalTheory.Grid.neg A) WW Y.rA.Λ Y.rW.Λ Y.rA.β Y.rW.β hSA hSW hI.rigA.2.1 hI.rigW.2.1
      g' h hstg hsth
  have hvθ := hI.isVac.2.theta
  have hvL := hI.isVac.2.lat
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hec := (hI.idem t).2
  have h0 : (Y.ω t).toSgn true (g', h) Y.vac =
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) • Y.vac := by
    obtain ⟨ι, P, es, h1, h2, he⟩ := ho
    rw [he] at hec hsg hsh hdg hdh
    have h3 : ∀ a ∈ P, ∀ b ∈ P, es a * cA D (es b) = 0 := fun a ha b hb => by
      rw [← GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 ha, ← GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hb, RingHom.map_mul,
        mul_mul_mul_comm, hec, mul_zero]
    exact GlobalTheory.WeilSplit.om_latVac_sum hW hSA hSW hvθ hvL es P h1 h2 h3 g' h hsg hsh hL x y hdg hdh
  rw [← isStd_lat_eq hY.std hX.std, ← isStd_lat_eq hY.stdW hX.stdW]
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hI.fst t
  refine ⟨⟨T₀, hT₀⟩, fun T' hT' => ?_⟩
  have hth := GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ hW.std (GlobalTheory.Grid.neg A) WW Y.rA.Λ Y.rW.Λ hSA hSW (Y.e t) ho.idem
    ho.infPart_eq Y.vac hvθ T' hT'
  have hc : ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) ≠ 0 :=
    Circle.coe_ne_zero _
  have pm := GlobalTheory.SchrMove.isPlaceModel_move hW hL hT' hth hc h0
  have hf := hall _ pm
  have hΦ : (fun u => GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t)
      (Y.ideal (locPl G) t) A WW Y.rA.β Y.rW.β (actO (GlobalTheory.Grid.neg A) WW g' h u)) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t)
      (Y.ideal (locPl G) t) A WW X.rA.β X.rW.β :=
    funext fun u => stdFst_actO _ _ _ X.rA.β Y.rA.β X.rW.β Y.rW.β g h hfr u
  have e1 : Y.ω t (g⁻¹, h⁻¹) = (Y.ω t).toSgn true (g'⁻¹, h⁻¹) := rfl
  have hf' : Y.f t = ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ)⁻¹ •
      (Y.ω t).toSgn true (g', h) (T' (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t)
      (Y.ideal (locPl G) t) A WW X.rA.β X.rW.β)) := by
    rw [hf, ← hΦ]; rfl
  rw [e1, hf', map_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel,
    Prod.mk_one_one, map_one, Module.End.one_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.BotFrames

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstMemberMovedDatumSplittingScaleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPairFirstMember_movedDatum_splittingScale : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (h : GA D WW) (x y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A WW, IsHalf (Y.e t) u → frMapO A WW Y.rA.β Y.rW.β (actO A WW g h u) = frMapO A WW X.rA.β X.rW.β u) →
    IsThetaAt W.ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO W.ψ (GlobalTheory.Grid.neg A) WW) (Y.e t)
      (latO (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ fun _ => True) 1 Y.vac
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A WW
        X.rA.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) •
        Y.ω t (g⁻¹, h⁻¹) (Y.f t)) := by
  first | exact @GlobalTheory.BotFrames.move_fst | exact GlobalTheory.BotFrames.move_fst | (intros; apply GlobalTheory.BotFrames.move_fst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleWeilMoveRightTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleWeilMoveRightTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotTranslate

open GlobalTheory.Grid (neg sgn ofSgn)

variable {D : D7}

theorem compAt_eq_map (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} (w : Mx D m n) :
    compAt θ τ w = w.map ((θ τ).comp (infPart D)) := rfl

theorem compAt_mt_of_suppAt {e : AE D} (he : infPart D e = 0) (hce : infPart D (cA D e) = 0) {V : HSp D} {g : GA D V}
    (hg : SuppAt e V g) (θ : InfFam D) (τ : D.what₂.Tau) : compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  ext i j
  have h1 := hg i j
  have e1 : Formalism.L2.Theta.mt V g i j = (e + cA D e) * (Formalism.L2.Theta.mt V g - 1) i j + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := by
    rw [h1, Matrix.sub_apply, sub_add_cancel]
  simp only [compAt, Matrix.map_apply]
  rw [e1]
  simp only [map_add, map_mul, he, hce, add_zero, zero_mul, map_zero, zero_add]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [Matrix.one_apply_ne hij]

theorem compAt_mt_inv {V : HSp D} {g : GA D V} {θ : InfFam D} {τ : D.what₂.Tau} (hg : compAt θ τ (Formalism.L2.Theta.mt V g) = 1) :
    compAt θ τ (Formalism.L2.Theta.mt V g⁻¹) = 1 := by
  have hm : Formalism.L2.Theta.mt V g⁻¹ * Formalism.L2.Theta.mt V g = 1 := by
    simp only [Formalism.L2.Theta.mt]
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : compAt θ τ (Formalism.L2.Theta.mt V g⁻¹) * compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
    rw [compAt_eq_map, compAt_eq_map, ← Matrix.map_mul, hm, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [hg, Matrix.mul_one] at h2

theorem integrableOn_mul_right_iff {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (k : G) (hk : Measure.map (fun g => g * k) μ = μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    IntegrableOn (fun g => f (g * k)) 𝓕 μ ↔ IntegrableOn f 𝓕 μ := by
  have hmp : MeasurePreserving (fun g : G => g * k) μ μ := ⟨measurable_mul_const k, hk⟩
  have hemb : MeasurableEmbedding (fun g : G => g * k) := measurableEmbedding_mulRight k
  have h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro γ g
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  rw [h𝓕.integrableOn_iff h2 (fun γ g => by simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]; exact hf γ γ.2 _)]
  exact hmp.integrableOn_comp_preimage hemb

end GlobalTheory.BotTranslate

namespace GlobalTheory.BotTranslate

open GlobalTheory.Grid (neg sgn ofSgn)


set_option maxHeartbeats 2000000 in
theorem translate : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (g : T → GA D A) (g' : T → GA D A') (h : T → GA D WW) (κ κ' : T → ℂ), (∀ t, κ t ≠ 0) → (∀ t, κ' t ≠ 0) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) A (g t) ∧ Formalism.IndefR.Lev.finE A (g t) ∈ Formalism.L2.DIV.St Y.rA.β) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) A' (g' t) ∧ Formalism.IndefR.Lev.finE A' (g' t) ∈ Formalism.L2.DIV.St Y.rA'.β) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) WW (h t) ∧ Formalism.IndefR.Lev.finE WW (h t) ∈ Formalism.L2.DIV.St Y.rW.β) →
    ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c →
      (GlobalTheory.BotFrames.reRig Y X.rA X.rA' X.rW (fun t => κ t • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t))
        (fun t => κ' t • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t))).IsConst W.ψ W.θ fun t => κ t / κ' t * c t := by
  intro D T L sc G W i j A A' WW X Y hX hY g g' h κ κ' hκ hκ' hg hg' hh c hc
  obtain ⟨⟨t₀, hc₀⟩, P, P', H⟩ := hc
  have hYi := hY.is
  have hψ := hYi.isVac.1
  have hθ := hYi.isVac.2.inf
  have sA := GlobalTheory.BotFrames.isStd_s_eq hX.std hY.std
  have sA' := GlobalTheory.BotFrames.isStd_s_eq hX.std' hY.std'
  have sW := GlobalTheory.BotFrames.isStd_s_eq hX.stdW hY.stdW
  have bA := GlobalTheory.BotFrames.isStd_B_eq hX.std hY.std
  have bA' := GlobalTheory.BotFrames.isStd_B_eq hX.std' hY.std'
  have bW := GlobalTheory.BotFrames.isStd_B_eq hX.stdW hY.stdW
  have he := fun t => Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_idemSum (hYi.idem t)
  have hce := fun t => Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_cA_idemSum (hYi.idem t)
  have cg : ∀ t τ, compAt W.θ τ (Formalism.L2.Theta.mt A (g t)⁻¹) = 1 := fun t τ =>
    compAt_mt_inv (compAt_mt_of_suppAt (he t) (hce t) (hg t).1 W.θ τ)
  have cg' : ∀ t τ, compAt W.θ τ (Formalism.L2.Theta.mt A' (g' t)⁻¹) = 1 := fun t τ =>
    compAt_mt_inv (compAt_mt_of_suppAt (he t) (hce t) (hg' t).1 W.θ τ)
  have ch : ∀ t τ, compAt W.θ τ (Formalism.L2.Theta.mt WW (h t)⁻¹) = 1 := fun t τ =>
    compAt_mt_inv (compAt_mt_of_suppAt (he t) (hce t) (hh t).1 W.θ τ)
  set Y₁ := GlobalTheory.BotFrames.reRig Y X.rA X.rA' X.rW (fun t => κ t • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t))
    (fun t => κ' t • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t)) with hY₁

  have hK : ∀ t Q h'' g'', Y₁.ker W.ψ W.θ t Q h'' g'' = κ t * Y.ker W.ψ W.θ t Q (h'' * (h t)⁻¹) (g'' * (g t)⁻¹) := by
    intro t Q h'' g''
    have tf := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (hYi.fst t) hYi.isVac.2.theta
    have c0 : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (neg A) ((ofSgn true A).symm (g t)⁻¹)) = 1 := cg t
    have key := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ ((Y.ω t).toSgn true) (hYi.weil t) hθ
      (fun τ => -Y.rA.s τ) (fun τ => -Y.rA.s τ) Y.rA.B Y.rA.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B
      ((ofSgn true A).symm (g t)⁻¹) (h t)⁻¹ (fun τ => by rw [c0 τ, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [ch t τ, Matrix.mul_one, Matrix.one_mul]) (fun τ => by rw [c0 τ, Matrix.one_mul])
      (fun τ => by rw [ch t τ, Matrix.one_mul]) (Y.f t) tf Q).2
    have key' : Y.ω t ((g t)⁻¹, (h t)⁻¹)
        (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) Q) =
        pureTensorO W.ψ W.θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t)) Q :=
      key
    show thetaKO (Y.ω t) g'' h'' (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
        (κ t • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t)) Q) =
      κ t * thetaKO (Y.ω t) (g'' * (g t)⁻¹) (h'' * (h t)⁻¹)
        (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) Q)
    rw [sA, sW, bA, bW, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul, ← key']
    unfold thetaKO
    rw [map_smul, Pi.smul_apply, smul_eq_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]
  have hK' : ∀ t Q h'' g'', Y₁.ker' W.ψ W.θ t Q h'' g'' = κ' t * Y.ker' W.ψ W.θ t Q (h'' * (h t)⁻¹) (g'' * (g' t)⁻¹) := by
    intro t Q h'' g''
    have tf := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (hYi.snd t) hYi.isVac'.2.theta
    have hw : IsWeilDatumO W.ψ A' WW _ _ (Y.ω' t) := hYi.weil' t
    have key := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ A' WW _ _ (Y.ω' t) hw hθ
      Y.rA'.s Y.rA'.s Y.rA'.B Y.rA'.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B
      (g' t)⁻¹ (h t)⁻¹ (fun τ => by rw [cg' t τ, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [ch t τ, Matrix.mul_one, Matrix.one_mul]) (fun τ => by rw [cg' t τ, Matrix.one_mul])
      (fun τ => by rw [ch t τ, Matrix.one_mul]) (Y.f' t) tf Q).2
    show thetaKO (Y.ω' t) g'' h'' (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B
        (κ' t • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t)) Q) =
      κ' t * thetaKO (Y.ω' t) (g'' * (g' t)⁻¹) (h'' * (h t)⁻¹)
        (pureTensorO W.ψ W.θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) Q)
    rw [sA', sW, bA', bW, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul, ← key]
    unfold thetaKO
    rw [map_smul, Pi.smul_apply, smul_eq_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

  haveI := hYi.meas.1
  haveI := hYi.meas'.1
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D A Y.m hYi.meas.1).1
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D A' Y.m' hYi.meas'.1).1
  have mk : ∀ k : GA D A, Measure.map (fun x => x * k) Y.m = Y.m := fun k => MeasureTheory.map_mul_right_eq_self Y.m k
  have mk' : ∀ k : GA D A', Measure.map (fun x => x * k) Y.m' = Y.m' := fun k => MeasureTheory.map_mul_right_eq_self Y.m' k
  have hI : ∀ t Q h'', Y₁.I W.ψ W.θ t Q h'' = κ t * Y.I W.ψ W.θ t Q (h'' * (h t)⁻¹) := by
    intro t Q h''
    show ∫ x in Y.fd, Y₁.ker W.ψ W.θ t Q h'' x ∂Y.m = κ t * ∫ x in Y.fd, Y.ker W.ψ W.θ t Q (h'' * (h t)⁻¹) x ∂Y.m
    simp_rw [hK]
    rw [integral_const_mul]
    congr 1
    exact GlobalTheory.DownLift.TypeLaw.setIntegral_mul_right_of_fd (GQ A) Y.m Y.fd hYi.meas.2 _ (mk _) _
      (GlobalTheory.SqTower.Normal.ker_left hYi t Q _)
  have hI' : ∀ t Q h'', Y₁.I' W.ψ W.θ t Q h'' = κ' t * Y.I' W.ψ W.θ t Q (h'' * (h t)⁻¹) := by
    intro t Q h''
    show ∫ x in Y.fd', Y₁.ker' W.ψ W.θ t Q h'' x ∂Y.m' = κ' t * ∫ x in Y.fd', Y.ker' W.ψ W.θ t Q (h'' * (h t)⁻¹) x ∂Y.m'
    simp_rw [hK']
    rw [integral_const_mul]
    congr 1
    exact GlobalTheory.DownLift.TypeLaw.setIntegral_mul_right_of_fd (GQ A') Y.m' Y.fd' hYi.meas'.2 _ (mk' _) _
      (GlobalTheory.SqTower.Normal.ker'_left hYi t Q _)
  refine ⟨⟨t₀, mul_ne_zero (div_ne_zero (hκ t₀) (hκ' t₀)) hc₀⟩, P, P', fun t => ⟨fun h'' => ⟨?_, ?_⟩, ?_, fun h'' => ?_⟩⟩
  · show IntegrableOn (Y₁.ker W.ψ W.θ t P h'') Y.fd Y.m
    rw [show Y₁.ker W.ψ W.θ t P h'' = fun x => κ t * Y.ker W.ψ W.θ t P (h'' * (h t)⁻¹) (x * (g t)⁻¹) from funext (hK t P h'')]
    exact ((integrableOn_mul_right_iff (GQ A) Y.m Y.fd hYi.meas.2 _ (mk _) _
      (GlobalTheory.SqTower.Normal.ker_left hYi t P _)).2 ((H t).1 _).1).const_mul _
  · show IntegrableOn (Y₁.ker' W.ψ W.θ t P' h'') Y.fd' Y.m'
    rw [show Y₁.ker' W.ψ W.θ t P' h'' = fun x => κ' t * Y.ker' W.ψ W.θ t P' (h'' * (h t)⁻¹) (x * (g' t)⁻¹) from funext (hK' t P' h'')]
    exact ((integrableOn_mul_right_iff (GQ A') Y.m' Y.fd' hYi.meas'.2 _ (mk' _) _
      (GlobalTheory.SqTower.Normal.ker'_left hYi t P' _)).2 ((H t).1 _).2).const_mul _
  · obtain ⟨h₀, hne⟩ := (H t).2.1
    refine ⟨h₀ * h t, ?_⟩
    rw [hI', mul_inv_cancel_right]
    exact mul_ne_zero (hκ' t) hne
  · rw [hI, hI', (H t).2.2]
    field_simp [hκ' t]

end GlobalTheory.BotTranslate

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleWeilMoveRightTranslateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottomTriple_weilMove_rightTranslate : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (g : T → GA D A) (g' : T → GA D A') (h : T → GA D WW) (κ κ' : T → ℂ), (∀ t, κ t ≠ 0) → (∀ t, κ' t ≠ 0) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) A (g t) ∧ Formalism.IndefR.Lev.finE A (g t) ∈ Formalism.L2.DIV.St Y.rA.β) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) A' (g' t) ∧ Formalism.IndefR.Lev.finE A' (g' t) ∈ Formalism.L2.DIV.St Y.rA'.β) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) WW (h t) ∧ Formalism.IndefR.Lev.finE WW (h t) ∈ Formalism.L2.DIV.St Y.rW.β) →
    ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c →
      (GlobalTheory.BotFrames.reRig Y X.rA X.rA' X.rW (fun t => κ t • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t))
        (fun t => κ' t • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t))).IsConst W.ψ W.θ fun t => κ t / κ' t * c t := by
  first | exact @GlobalTheory.BotTranslate.translate | exact GlobalTheory.BotTranslate.translate | (intros; apply GlobalTheory.BotTranslate.translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleBasisChangeFactorMemField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleBasisChangeFactorMemField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

open _root_.Formalism.L2.JoinChr


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem chr_mem_of_idemSum {K : Type} [Field K] {σ : K →+* ℂ} {D : D7} {c : (AE D)ˣ →* Circle}
    {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) (hχ : LocIn σ χ) {e : AE D}
    {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S) (x : (AE D)ˣ) (d : AE D)
    (hx : (x : AE D) = e * d + (1 - e)) : ((c x : Circle) : ℂ) ∈ σ.fieldRange := by
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have heT : ∀ P, ι (finPart D (∑ PP ∈ S, es PP)) P = if P ∈ S then 1 else 0 := by
    intro P
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, GlobalTheory.FlipCharFormula.fa_sum,
      Finset.sum_congr rfl (fun PP hPP => GlobalTheory.FlipCharFormula.comp_of_isIdemAt ι h1 h2 (hes PP hPP) P)]
    exact Finset.sum_ite_eq S P (fun _ => (1 : HeightOneSpectrum.adicCompletion D.host.E P))
  have hinfT : infPart D (∑ PP ∈ S, es PP) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero (fun PP hPP => GlobalTheory.FlipCharFormula.infPart_of_isIdemAt (hes PP hPP))
  have hinf : infPart D (x : AE D) = 1 := by
    rw [hx, map_add (f := _), map_mul, map_sub, hinfT, map_one, zero_mul, zero_add, sub_zero]
  have hout : ∀ P, P ∉ S → ι (finPart D (x : AE D)) P = 1 := by
    intro P hP
    rw [hx, map_add (f := _), map_mul, map_sub, map_one, map_add (f := _), map_mul, map_sub, map_one, GlobalTheory.FlipCharFormula.fa_add,
      GlobalTheory.FlipCharFormula.fa_mul, GlobalTheory.FlipCharFormula.fa_sub, GlobalTheory.FlipCharFormula.fa_one, heT, if_neg hP]
    simp
  have hne : ∀ P, ι (finPart D (x : AE D)) P ≠ 0 := by
    intro P h0
    have h := congrArg (fun z => ι (finPart D z) P) (Units.mul_inv x)
    simp only [map_mul, map_one, GlobalTheory.FlipCharFormula.fa_mul, GlobalTheory.FlipCharFormula.fa_one, h0, zero_mul] at h
    exact zero_ne_one h
  have hk : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ k : D.host.Eˣ,
      Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k : D.host.E) ∧
      Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k : D.host.E)) ≤
        P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k : D.host.E) := fun P => by
    obtain ⟨k, a, b, -⟩ := GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P _ (hne P)
    exact ⟨k, a, b⟩
  choose k hk1 hk2 using hk
  have hI : Ideal.span {((N : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have key := hprod x hinf (S ∪ (Ideal.finite_factors hI).toFinset) k (fun P _ => ⟨hk1 P, hk2 P⟩)
    (fun P hP => by
      have hPS : P ∉ S := fun h => hP (Finset.mem_union_left _ h)
      refine ⟨by rw [hout P hPS, map_one], fun hNP => hP (Finset.mem_union_right _ ?_)⟩
      rw [Set.Finite.mem_toFinset]
      exact Ideal.dvd_span_singleton.mpr hNP)
  rw [key]
  refine Subfield.prod_mem _ fun P _ => ?_
  rw [← SetLike.mem_coe, RingHom.coe_fieldRange]
  exact hχ P _


set_option maxHeartbeats 800000 in
theorem factor_mem_field : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ)
    (μ₀ : T), L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (Y : Tri T A A' WW),
    IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (g' : GA D A') (h : GA D WW) (x x' y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) A' g' → Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β →
    Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x' →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    ∃ z : D.what₂.LLˣ, D.what₂.embLL z =
      ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) := by
  intro D T L sc G W S μ₀ hL hN i j A A' WW Y hY t g g' h x x' y _ _ hx _ _ hx' _ _ hy
  have he := hY.is.idem t
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have mem : ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → LocIn D.what₂.embLL χ →
      ∀ (u : (AE D)ˣ) (d : AE D), (u : AE D) = Y.e t * d + (1 - Y.e t) → ((c u : Circle) : ℂ) ∈ D.what₂.embLL.fieldRange :=
    fun c χ hc hχ u d hu => chr_mem_of_idemSum hc hχ he u d hu
  have m1 := mem _ _ (hL.mu0 j) (hN.chars.mu0 j)
  have m2 := mem _ _ (hL.xi t) (hN.chars.xi t)
  have m3 := mem _ _ (G.ch.chi_eq _ hm.1 hm.2) (hN.chars.chi _ hm.1 hm.2)
  set a := L.mu0 ((j : ℕ) + 1)
  set b := L.xi t
  set c := G.ch.chi (D.R.m - (i : ℕ))
  set η := L.eta ^ (rankV D i j % 2)
  have hv : ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) =
      ((a x' : ℂ) * b x')⁻¹ * c x' * (((a x : ℂ) * b x)⁻¹ * c x) * ((a y : ℂ) * b y * (c y : ℂ)⁻¹) := by
    have e1 : GlobalTheory.BotFrames.botAlpha L i j t = a * b * η := rfl
    have e2 : GlobalTheory.BotFrames.botBeta G i j = c * η := rfl
    rw [e1, e2]
    simp only [splitFacO, MonoidHom.div_apply, MonoidHom.mul_apply, Circle.coe_mul, Circle.coe_inv, Circle.coe_div]
    have n1 := Circle.coe_ne_zero (a x'); have n2 := Circle.coe_ne_zero (b x'); have n3 := Circle.coe_ne_zero (c x')
    have n4 := Circle.coe_ne_zero (η x'); have n5 := Circle.coe_ne_zero (a x); have n6 := Circle.coe_ne_zero (b x)
    have n7 := Circle.coe_ne_zero (c x); have n8 := Circle.coe_ne_zero (η x); have n9 := Circle.coe_ne_zero (a y)
    have n10 := Circle.coe_ne_zero (b y); have n11 := Circle.coe_ne_zero (c y); have n12 := Circle.coe_ne_zero (η y)
    field_simp
  have hmem : (((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ)) ∈
      D.what₂.embLL.fieldRange := by
    rw [hv]
    refine mul_mem (mul_mem (mul_mem (inv_mem (mul_mem (m1 _ _ hx') (m2 _ _ hx'))) (m3 _ _ hx'))
      (mul_mem (inv_mem (mul_mem (m1 _ _ hx) (m2 _ _ hx))) (m3 _ _ hx)))
      (mul_mem (mul_mem (m1 _ _ hy) (m2 _ _ hy)) (inv_mem (m3 _ _ hy)))
  obtain ⟨z, hz⟩ := hmem
  have hne : ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) ≠ 0 :=
    div_ne_zero (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz
    exact hne hz.symm
  exact ⟨Units.mk0 z hz0, hz⟩

end GlobalTheory.BotFrames

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleBasisChangeFactorMemFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_bottom_triple_basis_change_factor_mem_field : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ)
    (μ₀ : T), L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (Y : Tri T A A' WW),
    IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (g' : GA D A') (h : GA D WW) (x x' y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) A' g' → Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β →
    Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x' →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    ∃ z : D.what₂.LLˣ, D.what₂.embLL z =
      ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) := by
  first | exact @GlobalTheory.BotFrames.factor_mem_field | exact GlobalTheory.BotFrames.factor_mem_field | (intros; apply GlobalTheory.BotFrames.factor_mem_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairSecondEqMovedBottomDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairSecondEqMovedBottomDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotFrames

theorem isThetaAt_stdSnd_move : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g' : GA D A') (h : GA D WW) (x' y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A' g' → Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β →
    Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x' →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A' WW, IsHalf (cA D (Y.e t)) u →
      frMapAdj A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) = frMapAdj A' WW X.rA'.β X.rW.β u) →
    IsThetaAt W.ψ (symplO A' WW) (heisO W.ψ A' WW) (cA D (Y.e t))
      (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) 1 Y.vac'
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t)
        A.rank A' WW X.rA'.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) • Y.ω' t (g'⁻¹, h⁻¹) (Y.f' t)) := by
  intro D T L sc G W i j A A' WW X Y hX hY t g' h x' y hS1 hSt1 hD1 hS2 hSt2 hD2 hfr
  have hi := hY.is
  have hW : IsWeilDatumO W.ψ A' WW (botAlpha L i j t) (botAlpha L i j t / botBeta G i j) (Y.ω' t) :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hi.weil' t)
  have hSA : IsSelfDualC A' Y.rA'.Λ := hi.rigA'.1
  have hSW : IsSelfDualC WW Y.rW.Λ := hi.rigW.1
  have hFA : Formalism.L2.DIV.IsFrame Y.rA'.β Y.rA'.Λ := hi.rigA'.2.1
  have hFW : Formalism.L2.DIV.IsFrame Y.rW.β Y.rW.Λ := hi.rigW.2.1
  have eA : X.rA'.Λ = Y.rA'.Λ := isStd_lat_eq hX.std' hY.std'
  have eW : X.rW.Λ = Y.rW.Λ := isStd_lat_eq hX.stdW hY.stdW
  rw [eA, eW]
  have hL := GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D A' WW Y.rA'.Λ Y.rW.Λ Y.rA'.β Y.rW.β hSA hSW hFA hFW g' h hSt1 hSt2
  have hvac := hi.isVac'
  have hIS := hi.idem t
  obtain ⟨ι, P, es, hsp, horth, hsum⟩ := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hIS
  have hc0 : Y.e t * cA D (Y.e t) = 0 := hIS.2
  have hes : ∀ k ∈ P, es k * Y.e t = es k := by
    intro k hk
    rw [hsum, Finset.mul_sum, Finset.sum_eq_single_of_mem k hk (fun b hb hne => horth k hk b hb hne)]
    exact (hsp k hk).1
  have hecs : ∀ a ∈ P, ∀ b ∈ P, es a * cA D (es b) = 0 := by
    intro a ha b hb
    have h2 : cA D (es b) * cA D (Y.e t) = cA D (es b) := by rw [← map_mul, hes b hb]
    rw [← hes a ha, ← h2]
    calc es a * Y.e t * (cA D (es b) * cA D (Y.e t)) = es a * cA D (es b) * (Y.e t * cA D (Y.e t)) := by ring
      _ = 0 := by rw [hc0, mul_zero]
  have h0 : Y.ω' t (g', h) Y.vac' =
      ((splitFacO (botAlpha L i j t) (botAlpha L i j t / botBeta G i j) x' y : Circle) : ℂ) • Y.vac' := by
    rw [hsum] at hS1 hS2 hD1 hD2
    exact GlobalTheory.WeilSplit.om_latVac_sum hW hSA hSW hvac.2.theta hvac.2.lat es P hsp horth hecs g' h hS1 hS2 hL x' y hD1 hD2
  have hos := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hIS).conj
  have hc : ((splitFacO (botAlpha L i j t) (botAlpha L i j t / botBeta G i j) x' y : Circle) : ℂ) ≠ 0 :=
    Circle.coe_ne_zero _
  have hΦ : (LinearMap.funLeft ℂ ℂ (actO A' WW g' h))
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (botAlpha L i j t / botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW Y.rA'.β Y.rW.β) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (botAlpha L i j t / botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW X.rA'.β X.rW.β := by
    funext u
    rw [LinearMap.funLeft_apply]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd
    by_cases hu : IsHalf (cA D (Y.e t)) u
    · have hd : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) =
          GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW X.rA'.β X.rW.β u := by
        unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord
        rw [hfr u hu]
      rw [hd, GlobalTheory.SchrMove.isHalf_actO_iff]
    · rw [if_neg, if_neg]
      · exact fun hh => hu hh.1
      · exact fun hh => hu ((GlobalTheory.SchrMove.isHalf_actO_iff g' h u).1 hh.1)
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hi.snd t
  refine ⟨⟨T₀, hT₀⟩, fun T' hT' => ?_⟩
  have th1 := GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ hW.std A' WW Y.rA'.Λ Y.rW.Λ hSA hSW (cA D (Y.e t)) hos.idem
    hos.infPart_eq Y.vac' hvac.2.theta T' hT'
  have pm := GlobalTheory.SchrMove.isPlaceModel_move hW hL hT' th1 hc h0
  have hf' := hall _ pm
  have omm : ∀ p q (F : WO A' WW → ℂ), Y.ω' t p (Y.ω' t q F) = Y.ω' t (p * q) F := fun p q F => by
    rw [map_mul]; rfl
  show _ = T' _
  rw [← hΦ, hf']
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]
  rfl

end GlobalTheory.BotFrames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairSecondEqMovedBottomDatumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_pair_second_eq_moved_bottom_datum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g' : GA D A') (h : GA D WW) (x' y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A' g' → Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β →
    Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x' →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A' WW, IsHalf (cA D (Y.e t)) u →
      frMapAdj A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) = frMapAdj A' WW X.rA'.β X.rW.β u) →
    IsThetaAt W.ψ (symplO A' WW) (heisO W.ψ A' WW) (cA D (Y.e t))
      (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) 1 Y.vac'
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t)
        A.rank A' WW X.rA'.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) • Y.ω' t (g'⁻¹, h⁻¹) (Y.f' t)) := by
  first | exact @GlobalTheory.BotFrames.isThetaAt_stdSnd_move | exact GlobalTheory.BotFrames.isThetaAt_stdSnd_move | (intros; apply GlobalTheory.BotFrames.isThetaAt_stdSnd_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteBottomTripleTransferredFrames
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

theorem frames_transfer : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ),
    IsStdChar D W.ψ (-1) → ∀ μ₀ : T, L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
    (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    ∃ Y₁ : Tri T A A' WW, IsBottomTri W i j Y₁ ∧ Y₁.rA = X.rA ∧ Y₁.rA' = X.rA' ∧ Y₁.rW = X.rW ∧
      ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → ∃ u : T → D.what₂.LLˣ, Y₁.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  intro D T L sc G W S _ μ₀ hL hN i j A A' WW X Y hX hY
  choose g g' h x x' y hE using fun t => GlobalTheory.T.exists_supported_unitaries_moving_bottomTriples W i j A A' WW X Y hX hY t
  have hC := fun t => GlobalTheory.T.definite_bottom_triple_basis_change_factor_mem_field W S μ₀ hL hN i j A A' WW Y hY t (g t) (g' t) (h t) (x t) (x' t) (y t)
    (hE t).1.1 (hE t).1.2.1 (hE t).1.2.2 (hE t).2.1.1 (hE t).2.1.2.1 (hE t).2.1.2.2 (hE t).2.2.1.1 (hE t).2.2.1.2.1
    (hE t).2.2.1.2.2
  choose z hz using hC
  have κne : ∀ t, ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t)
      (x t) (y t) : Circle) : ℂ) ≠ 0 := fun t => Circle.coe_ne_zero _
  have κne' : ∀ t, ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j)
      (x' t) (y t) : Circle) : ℂ) ≠ 0 := fun t => Circle.coe_ne_zero _
  have sA := GlobalTheory.BotFrames.isStd_s_eq hX.std hY.std
  have sA' := GlobalTheory.BotFrames.isStd_s_eq hX.std' hY.std'
  have sW := GlobalTheory.BotFrames.isStd_s_eq hX.stdW hY.stdW
  have lA := GlobalTheory.BotFrames.isStd_lat_eq hX.std hY.std
  have lA' := GlobalTheory.BotFrames.isStd_lat_eq hX.std' hY.std'
  have lW := GlobalTheory.BotFrames.isStd_lat_eq hX.stdW hY.stdW
  refine ⟨GlobalTheory.BotFrames.reRig Y X.rA X.rA' X.rW
    (fun t => ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t)
      (x t) (y t) : Circle) : ℂ) • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t))
    (fun t => ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j)
      (x' t) (y t) : Circle) : ℂ) • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t)),
    ⟨hY.rank, hY.rank', hX.std, hX.std', hX.stdW, ?_⟩, rfl, rfl, rfl, fun c hc => ?_⟩
  · have hi := hY.is
    refine ⟨hi.rank, hX.is.rigA, hX.is.rigA', hX.is.rigW, hi.weil, hi.weil', ?_, ?_, hi.idem, hi.expo,
      fun t => GlobalTheory.T.standardPairFirstMember_movedDatum_splittingScale W i j A A' WW X Y hX hY t (g t) (h t) (x t) (y t) (hE t).1.1 (hE t).1.2.1 (hE t).1.2.2 (hE t).2.2.1.1
        (hE t).2.2.1.2.1 (hE t).2.2.1.2.2 (hE t).2.2.2.1,
      fun t => GlobalTheory.T.standard_pair_second_eq_moved_bottom_datum W i j A A' WW X Y hX hY t (g' t) (h t) (x' t) (y t) (hE t).2.1.1 (hE t).2.1.2.1 (hE t).2.1.2.2
        (hE t).2.2.1.1 (hE t).2.2.1.2.1 (hE t).2.2.1.2.2 (hE t).2.2.2.2, hi.meas, hi.meas'⟩
    · show IsVacO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.Λ X.rW.Λ Y.vac
      rw [sA, sW, lA, lW]
      exact hi.isVac
    · show IsVacO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.Λ X.rW.Λ Y.vac'
      rw [sA', sW, lA', lW]
      exact hi.isVac'
  · refine ⟨fun t => (z t)⁻¹, ?_⟩
    have hD := GlobalTheory.T.definiteBottomTriple_weilMove_rightTranslate W i j A A' WW X Y hX hY g g' h _ _ κne κne' (fun t => ⟨(hE t).1.1, (hE t).1.2.1⟩)
      (fun t => ⟨(hE t).2.1.1, (hE t).2.1.2.1⟩) (fun t => ⟨(hE t).2.2.1.1, (hE t).2.2.1.2.1⟩) c hc
    convert hD using 2 with t
    rw [map_units_inv, hz t, inv_div]

end GlobalTheory.BotFrames

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteBottomTripleTransferredFramesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_definiteBottomTriple_transferred_frames : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ),
    IsStdChar D W.ψ (-1) → ∀ μ₀ : T, L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
    (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    ∃ Y₁ : Tri T A A' WW, IsBottomTri W i j Y₁ ∧ Y₁.rA = X.rA ∧ Y₁.rA' = X.rA' ∧ Y₁.rW = X.rW ∧
      ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → ∃ u : T → D.what₂.LLˣ, Y₁.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  first | exact @GlobalTheory.BotFrames.frames_transfer | exact GlobalTheory.BotFrames.frames_transfer | (intros; apply GlobalTheory.BotFrames.frames_transfer <;> assumption)
end
