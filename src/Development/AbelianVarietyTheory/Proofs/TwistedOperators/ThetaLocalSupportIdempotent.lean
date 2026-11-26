module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtEnlargePlaceIdempotentLatticeIndicator

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomSplitPlaceStabiliserVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomSplitPlaceStabiliserVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.StabVacSplit

open GlobalTheory.Grid (neg)


set_option maxHeartbeats 1000000 in
theorem stab_vac_split : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (e : AE D) (he : IsSplitIdem D e)
    (k : GA D WW), k ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ → Formalism.L2.Theta.SuppAt e WW k →
      X.ω t (1, k) X.vac =
        (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e he.1 WW k) : Circle) : ℂ) • X.vac := by
  intro D T L sc G W i j A A' WW X hX t e he k hk hsupp
  set om' := (X.ω t).toSgn true with hom'
  have hW : IsWeilDatumO W.ψ (neg A) WW _ _ om' := hX.is.weil t
  have hsdS : IsSelfDualC (neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hLW : L0c D (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) = (X.rW.Λ : Set (Fin WW.rank → D.host.E)) := by
    ext y
    exact (GlobalTheory.SplitVacAlg.mem_frameLattice_iff_integral_coords WW hX.stdW.1 y).trans (hX.stdW.2.1 y).symm
  have fwd : ∀ h : GA D WW, h ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ →
      ∀ u, u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) →
        actO (neg A) WW 1 h u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) := by
    intro h hh u hu
    have h1 : (1 : AE D) • actO (neg A) WW 1 h u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) :=
      GlobalTheory.HeckeVacuum.smul_actO_mem _ _ 1 h (fun y hy => by
        rw [map_one, one_smul]
        have h2 := (hh.2.1 y).1 (by rw [hLW]; exact hy)
        rw [hLW] at h2
        exact h2) u hu
    rwa [one_smul] at h1
  have hinv : k⁻¹ ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ :=
    (GlobalTheory.SphLabelOps.mem_stabG (V := GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) k⁻¹).1
      (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG (V := GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) k).2 hk))
  have hback : ∀ u : WO (neg A) WW, actO (neg A) WW 1 k⁻¹ (actO (neg A) WW 1 k u) = u := fun u => by
    rw [← GlobalTheory.HeckeVacuum.act_mul (S := neg A) (T := WW) k⁻¹ k u, inv_mul_cancel, GlobalTheory.HeckeVacuum.act_one]
  have hlat : ∀ u, u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) ↔
      actO (neg A) WW 1 k u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) :=
    fun u => ⟨fwd k hk u, fun hu => (hback u) ▸ fwd k⁻¹ hinv _ hu⟩
  have h1 : om' (1, k) X.vac = ((splitFacO _ _ (GlobalTheory.VecInv.detAt e he.1 (neg A) 1) (GlobalTheory.VecInv.detAt e he.1 WW k) : Circle) : ℂ) • X.vac :=
    GlobalTheory.T.splitPlace_weilRep_latticeVacuum_character D W.ψ (neg A) WW X.rA.Λ X.rW.Λ _ _ om' hW hsdS hsdT e he 1 k
      (GlobalTheory.SplitLinear.suppAt_one e _) hsupp hlat _ _ (GlobalTheory.VecInv.isDetAt_detAt e he.1 (neg A) 1)
      (GlobalTheory.VecInv.isDetAt_detAt e he.1 WW k) X.vac hX.is.isVac.2.theta hX.is.isVac.2.lat
  have e1 : X.ω t (1, k) = om' (1, k) := by
    rw [hom']
    show X.ω t (1, k) = X.ω t ((GlobalTheory.Grid.ofSgn true A) 1, k)
    rw [map_one]
  rw [e1, h1, splitFacO, map_one, map_one, inv_one, one_mul]

end GlobalTheory.StabVacSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomSplitPlaceStabiliserVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottom_splitPlace_stabiliser_vacuum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (e : AE D) (he : IsSplitIdem D e)
    (k : GA D WW), k ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ → Formalism.L2.Theta.SuppAt e WW k →
      X.ω t (1, k) X.vac =
        (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e he.1 WW k) : Circle) : ℂ) • X.vac := by
  first | exact @GlobalTheory.StabVacSplit.stab_vac_split | exact GlobalTheory.StabVacSplit.stab_vac_split | (intros; apply GlobalTheory.StabVacSplit.stab_vac_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomSplitHeckeVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomSplitHeckeVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

namespace GlobalTheory.RowEx.BottomHecke

variable {D : D7}

theorem thetaFunO_stdLatSp {ψ : AddChar (AF D.host.F) ℂ} {S V : HSp D} (hV : V.gram = 1) {f : WO S V → ℂ} :
    IsThetaFunO ψ S (GlobalTheory.SplitVacAlg.stdLatSp V hV) f ↔ IsThetaFunO ψ S V f :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

theorem weilDatumO_stdLatSp {ψ : AddChar (AF D.host.F) ℂ} {S V : HSp D} (hV : V.gram = 1) {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)} (h : IsWeilDatumO ψ S V χS χT om) :
    IsWeilDatumO ψ S (GlobalTheory.SplitVacAlg.stdLatSp V hV) χS χT om :=
  { std := h.std,
    hecS := h.hecS,
    hecT := h.hecT,
    resS := h.resS,
    resT := h.resT,
    om_pres := fun p f hf => (thetaFunO_stdLatSp hV).2 (h.om_pres p f ((thetaFunO_stdLatSp hV).1 hf)),
    om_heis := fun g h' w f hf => h.om_heis g h' w f ((thetaFunO_stdLatSp hV).1 hf),
    om_aut := fun γ hγ γ' hγ' f hf => h.om_aut γ hγ γ' hγ' f ((thetaFunO_stdLatSp hV).1 hf),
    om_cont := fun f hf => h.om_cont f ((thetaFunO_stdLatSp hV).1 hf),
    om_unit := fun μ 𝓕 hμ h𝓕 p f hf => h.om_unit μ 𝓕 hμ h𝓕 p f ((thetaFunO_stdLatSp hV).1 hf),
    om_split := fun e he g h' hg hh x y hx hy => by
      obtain ⟨r, hr, H⟩ := h.om_split e he g h' hg hh x y hx hy
      exact ⟨r, hr, fun ℓ hℓ f hf => H ℓ (fun u hu f' hf' => hℓ u hu f' ((thetaFunO_stdLatSp hV).2 hf')) f
        ((thetaFunO_stdLatSp hV).1 hf)⟩ }

theorem vacuum_hecke : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (e : AE D) (he : IsSplitIdem D e)
    (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D WW), Formalism.L2.NTheta.IsHeckeElt (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) e (ϖ : D.host.E) k α →
      ∃ Δ : Finset (WO (GlobalTheory.Grid.neg A) WW), (∀ u ∈ Δ, u.map (infPart D) = 0) ∧
        X.ω t (1, α) X.vac =
          ((((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e he.1 WW α) : Circle) : ℂ) *
            ((Real.sqrt (Δ.card : ℝ) : ℝ) : ℂ)⁻¹) • ∑ u ∈ Δ, heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac := by
  intro D T L sc G W i j A A' WW X hX t e he ϖ k α hα
  obtain ⟨hg, hlat, -⟩ := hX.stdW
  have hS : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := isSelfDualC_neg' hX.is.rigA.1
  have hT : IsSelfDualC (GlobalTheory.SplitVacAlg.stdLatSp WW hg) X.rW.Λ := hX.is.rigW.1
  have hL : (X.rW.Λ : Set (Fin WW.rank → D.host.E)) = L0c D (GlobalTheory.SplitVacAlg.stdLatSp WW hg) :=
    Set.ext fun y => (hlat y).trans (GlobalTheory.SplitVacAlg.mem_frameLattice_iff_integral_coords WW hg y).symm
  obtain ⟨Δ, hΔ⟩ := GlobalTheory.HeckeVacuum.exists_halfReps hS hT hL he hα
  refine ⟨Δ, fun x hx => GlobalTheory.SplitScalar.half_fin (GlobalTheory.SplitScalar.isSplitIdem_conj he) (hΔ.1 x hx).2, ?_⟩
  have hW := weilDatumO_stdLatSp hg (hX.is.weil t)
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) (GlobalTheory.SplitVacAlg.stdLatSp WW hg) X.vac :=
    (thetaFunO_stdLatSp hg).2 hX.is.isVac.2.theta
  have h := GlobalTheory.HeckeVacuum.om_elt hW hS hT hL he hα hf hX.is.isVac.2.lat hΔ
  have e1 : X.ω t (1, α) X.vac = ((X.ω t).toSgn true) ((GlobalTheory.Grid.ofSgn true A).symm 1, α) X.vac := rfl
  rw [e1, map_one]
  exact h

end GlobalTheory.RowEx.BottomHecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomSplitHeckeVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottom_splitHecke_vacuum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (e : AE D) (he : IsSplitIdem D e)
    (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D WW), Formalism.L2.NTheta.IsHeckeElt (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) e (ϖ : D.host.E) k α →
      ∃ Δ : Finset (WO (GlobalTheory.Grid.neg A) WW), (∀ u ∈ Δ, u.map (infPart D) = 0) ∧
        X.ω t (1, α) X.vac =
          ((((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e he.1 WW α) : Circle) : ℂ) *
            ((Real.sqrt (Δ.card : ℝ) : ℝ) : ℂ)⁻¹) • ∑ u ∈ Δ, heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac := by
  first | exact @GlobalTheory.RowEx.BottomHecke.vacuum_hecke | exact GlobalTheory.RowEx.BottomHecke.vacuum_hecke | (intros; apply GlobalTheory.RowEx.BottomHecke.vacuum_hecke <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceUnitaryPointMemHeckeClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceUnitaryPointMemHeckeClosure
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitCartanGen

open Formalism.UG

section Local

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

def dg : (Fin n → (v.adicCompletion F)ˣ) →* GL (Fin n) (v.adicCompletion F) :=
  (Units.map (Matrix.diagonalRingHom (Fin n) (v.adicCompletion F)).toMonoidHom).comp
    MulEquiv.piUnits.symm.toMonoidHom

theorem dg_val (u : Fin n → (v.adicCompletion F)ˣ) :
    (dg u).1 = Matrix.diagonal fun i => (u i : v.adicCompletion F) := rfl

def heckeL (ϖ : v.adicCompletion F) : Set (GL (Fin n) (v.adicCompletion F)) :=
  {x | ∃ k : ℕ, (∀ i j, x.1 i j ∈ Ov F v) ∧ (∀ i j, ϖ * (x⁻¹).1 i j ∈ Ov F v) ∧
    Valued.v x.1.det = Valued.v ϖ ^ k}

theorem single_mem {ϖ : v.adicCompletion F} (h0 : ϖ ≠ 0) (hϖO : ϖ ∈ Ov F v) (i : Fin n) :
    dg (Pi.mulSingle i (Units.mk0 ϖ h0)) ∈ heckeL (n := n) ϖ := by
  classical
  refine ⟨1, fun a b => ?_, fun a b => ?_, ?_⟩
  · rw [dg_val, Matrix.diagonal_apply]
    split_ifs with hab
    · rw [Pi.mulSingle_apply]
      split_ifs
      · simpa using hϖO
      · simpa using one_mem (Ov F v)
    · exact zero_mem _
  · rw [← map_inv, dg_val, Matrix.diagonal_apply]
    split_ifs with hab
    · rw [Pi.inv_apply, Pi.mulSingle_apply]
      split_ifs
      · simpa [h0] using one_mem (Ov F v)
      · simpa using hϖO
    · rw [mul_zero]; exact zero_mem _
  · rw [dg_val, Matrix.det_diagonal, ← Units.coe_prod, Finset.prod_pi_mulSingle']
    simp

theorem local_closure {ϖ : v.adicCompletion F} (hϖ : IsUnifV F v ϖ) (hϖO : ϖ ∈ Ov F v)
    (g : GL (Fin n) (v.adicCompletion F)) :
    g ∈ Submonoid.closure ((GLint (Fin n) (Ov F v) : Set (GL (Fin n) (v.adicCompletion F))) ∪ heckeL ϖ ∪
      {x | x⁻¹ ∈ heckeL ϖ}) := by
  classical
  have h0 : ϖ ≠ 0 := (GlobalTheory.SplitPlace.unif_facts hϖ).1
  set S := ((GLint (Fin n) (Ov F v) : Set (GL (Fin n) (v.adicCompletion F))) ∪ heckeL ϖ ∪
      {x | x⁻¹ ∈ heckeL ϖ}) with hS
  set M := (Submonoid.closure S).comap (dg (v := v) (n := n)) with hM
  have hz : ∀ i (z : ℤ), Pi.mulSingle i (Units.mk0 ϖ h0 ^ z) ∈ M := by
    intro i z
    have hmz := map_zpow (MonoidHom.mulSingle (fun _ : Fin n => (v.adicCompletion F)ˣ) i) (Units.mk0 ϖ h0) z
    simp only [MonoidHom.mulSingle_apply] at hmz
    rw [hmz]
    have m1 : Pi.mulSingle i (Units.mk0 ϖ h0) ∈ M :=
      Submonoid.subset_closure (Or.inl (Or.inr (single_mem h0 hϖO i)))
    have m2 : (Pi.mulSingle i (Units.mk0 ϖ h0))⁻¹ ∈ M := by
      refine Submonoid.subset_closure (Or.inr ?_)
      change (dg _)⁻¹ ∈ heckeL ϖ
      rw [map_inv, inv_inv]
      exact single_mem h0 hϖO i
    rcases z with m | m
    · rw [Int.ofNat_eq_coe, zpow_natCast]; exact pow_mem m1 m
    · rw [zpow_negSucc, ← inv_pow]; exact pow_mem m2 _
  obtain ⟨a, -, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp F v n ϖ hϖO hϖ g
  have hu : (fun i => Units.mk0 ϖ h0 ^ a i) ∈ M := by
    rw [← Finset.univ_prod_mulSingle (fun i => Units.mk0 ϖ h0 ^ a i)]
    exact Submonoid.prod_mem M fun i _ => hz i (a i)
  have hg : g = k₁ * dg (fun i => Units.mk0 ϖ h0 ^ a i) * k₂ := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, dg_val, e]
    congr 2
    simp [diagPow, Units.val_zpow_eq_zpow_val]
  rw [hg]
  exact mul_mem (mul_mem (Submonoid.subset_closure (Or.inl (Or.inl hk₁))) hu)
    (Submonoid.subset_closure (Or.inl (Or.inl hk₂)))

end Local

end GlobalTheory.SplitCartanGen

namespace GlobalTheory.SplitCartanGen

open Formalism.UG GlobalTheory.SplitPlace

theorem supp_mem_closure : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal →
    ϖ ∉ P.asIdeal ^ 2 → ∀ h ∈ GfC V, Formalism.L2.Theta.SuppAt e V h →
      h ∈ Submonoid.closure ({g | g ∈ KsphC V ∅ ∧ Formalism.L2.Theta.SuppAt e V g} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α⁻¹}) := by
  intro D V P e ϖ he hP hP2 h _ hs
  classical
  obtain ⟨v, π, s, h1, h2, h3, h4, h5⟩ := GlobalTheory.SplitCoord.exists_coord e he.1
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_basis V e v π s he.1.1 h2 h3 h4
    (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2
  obtain ⟨hex, hinj⟩ := comp_bij (V := V) (B := B) he.1 h1 h2
  have hK := fun g => K_iff (g := g) he.1 h2 h3 hB
  have hu := isUnif he h4 h5 ϖ hP hP2
  have hH := hecke_iff he.1 h1 h2 h3 h4 hB (unif_facts hu).1
  have hloc := local_closure hu (unif_facts hu).2 (comp V π B h)
  have s1 : Formalism.L2.Theta.SuppAt e V 1 := by
    rw [suppAt_iff, mt_one, sub_self, smul_zero]
  suffices key : ∀ a ∈ Submonoid.closure ((GLint (Fin V.rank) (Ov D.host.F v) : Set (GL (Fin V.rank) (Fv D.host.F v))) ∪
      heckeL (π (finPart D (incA D (ϖ : D.host.E)))) ∪ {x | x⁻¹ ∈ heckeL (π (finPart D (incA D (ϖ : D.host.E))))}),
      ∀ g, Formalism.L2.Theta.SuppAt e V g → comp V π B g = a → g ∈ Submonoid.closure ({g | g ∈ KsphC V ∅ ∧ Formalism.L2.Theta.SuppAt e V g} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α⁻¹}) from key _ hloc h hs rfl
  intro a ha
  induction ha using Submonoid.closure_induction with
  | mem x hx =>
    intro g hg hgx
    apply Submonoid.subset_closure
    rcases hx with (hx | ⟨k, hx⟩) | ⟨k, hx⟩
    · exact Or.inl (Or.inl ⟨(hK g hg).2 (hgx ▸ hx), hg⟩)
    · exact Or.inl (Or.inr ⟨k, (hH k g).2 ⟨hg, hgx ▸ hx⟩⟩)
    · refine Or.inr ⟨k, (hH k g⁻¹).2 ⟨suppAt_inv hg, ?_⟩⟩
      rw [map_inv, hgx]
      exact hx
  | one =>
    intro g hg hg1
    have : g = 1 := hinj _ _ hg s1 (by rw [hg1, map_one])
    rw [this]
    exact one_mem _
  | mul x y _ _ ihx ihy =>
    intro g hg hgxy
    obtain ⟨gx, sx, rfl⟩ := hex x
    obtain ⟨gy, sy, rfl⟩ := hex y
    have : g = gx * gy := hinj _ _ hg (suppAt_mul sx sy) (by rw [hgxy, map_mul])
    rw [this]
    exact mul_mem (ihx gx sx rfl) (ihy gy sy rfl)

end GlobalTheory.SplitCartanGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceUnitaryPointMemHeckeClosureStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_unitaryPoint_mem_heckeClosure : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal →
    ϖ ∉ P.asIdeal ^ 2 → ∀ h ∈ GfC V, Formalism.L2.Theta.SuppAt e V h →
      h ∈ Submonoid.closure ({g | g ∈ KsphC V ∅ ∧ Formalism.L2.Theta.SuppAt e V g} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α⁻¹}) := by
  first | exact @GlobalTheory.SplitCartanGen.supp_mem_closure | exact GlobalTheory.SplitCartanGen.supp_mem_closure | (intros; apply GlobalTheory.SplitCartanGen.supp_mem_closure <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitVacAlg

open GlobalTheory.MovedAlg

theorem isAlg_sqrt_inv (n : ℕ) : IsAlgebraic ℚ (((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹) := by
  have h : IsAlgebraic ℚ (((Real.sqrt (n : ℝ) : ℝ) : ℂ)) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (n : ℚ), Polynomial.X_pow_sub_C_ne_zero (by norm_num) _, ?_⟩
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, eq_ratCast, Rat.cast_natCast]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    simp
  rw [← mem_algebraicClosure_iff] at h ⊢
  exact inv_mem h

section Comb

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f₀ : WO S T → ℂ}

theorem isAlgComb_heis {u : WO S T} (hu : u.map (infPart D) = 0) : IsAlgComb ψ S T f₀ (heisO ψ S T u f₀) :=
  ⟨1, fun _ => 1, fun _ => u, fun _ => isAlgebraic_one, fun _ => hu, by simp⟩

theorem isAlgComb_sum (Δ : Finset (WO S T)) (hΔ : ∀ u ∈ Δ, u.map (infPart D) = 0) :
    IsAlgComb ψ S T f₀ (∑ u ∈ Δ, heisO ψ S T u f₀) := by
  classical
  induction Δ using Finset.induction_on with
  | empty => simpa using (IsAlgComb.zero : IsAlgComb ψ S T f₀ 0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (isAlgComb_heis (hΔ a (Finset.mem_insert_self a s))).add
      (ih fun u hu => hΔ u (Finset.mem_insert_of_mem hu))

theorem isAlgComb_self : IsAlgComb ψ S T f₀ f₀ := by
  have := isAlgComb_heis (ψ := ψ) (f₀ := f₀) (u := (0 : WO S T)) (by simp)
  rwa [GlobalTheory.SplitScalar.heisO_zero ψ S T f₀] at this

end Comb


end GlobalTheory.SplitVacAlg

end
