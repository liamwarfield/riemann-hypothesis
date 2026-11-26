module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CarryWeilUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarUnitModulus
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SetAtOfSizeAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecOfEqIntertwiner
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv.FactorTheta

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem om_theta_eq {ψ : AddChar (AF D.host.F) ℂ} {S' T' : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ)} (hW : IsWeilDatumO ψ S' T' χS χT om) {e : AE D}
    (he : e * e = e) (hinf : infPart D e = 0) {ΛS : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)} (hS : IsSelfDualC S' ΛS) (hT : IsSelfDualC T' ΛT)
    {f₀ : WO S' T' → ℂ} (hf₀ : IsThetaFunO ψ S' T' f₀) (g : GA D S' × GA D T')
    (hΛ : ∀ u, u ∈ latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔
      actO S' T' g.1 g.2 u ∈ latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True))
    {c : ℂ} (hc : c ≠ 0) (h0 : om g f₀ = c • f₀) {Tm : (WO S' T' → ℂ) →ₗ[ℂ] (WO S' T' → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S' T') (heisO ψ S' T') e (latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True)) 1 f₀ Tm)
    {Φ f : WO S' T' → ℂ}
    (hf : IsThetaAt ψ (symplO S' T') (heisO ψ S' T') e (latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True)) 1 f₀ Φ f) :
    om g f = Tm (c • fun x => Φ (actO S' T' g⁻¹.1 g⁻¹.2 x)) := by
  have hΛ' : ∀ u, u ∈ latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔
      actO S' T' g⁻¹.1 g⁻¹.2 u ∈ latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True) := by
    intro u
    have e1 : actO S' T' g.1 g.2 (actO S' T' g⁻¹.1 g⁻¹.2 u) = u := by
      rw [Prod.fst_inv, Prod.snd_inv]; exact GlobalTheory.AdelicLatMove.actO_actO_inv _ _ _ _ u
    rw [hΛ (actO S' T' g⁻¹.1 g⁻¹.2 u), e1]
  have hinv : om g⁻¹ f₀ = c⁻¹ • f₀ := by
    have e2 : om g⁻¹ (om g f₀) = f₀ := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [h0, LinearMap.map_smul] at e2
    calc om g⁻¹ f₀ = c⁻¹ • (c • om g⁻¹ f₀) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = c⁻¹ • f₀ := by rw [e2]
  have hth := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S' T' ΛS ΛT hS hT e he hinf f₀ hf₀ Tm hTm
  have hmod := GlobalTheory.SchrMove.isPlaceModel_move hW hΛ' hTm hth (inv_ne_zero hc) hinv
  have hfe : f = ((c⁻¹)⁻¹ • (om g⁻¹ ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S' T' g⁻¹.1 g⁻¹.2))) Φ := hf.2 _ hmod
  rw [hfe, inv_inv, LinearMap.smul_apply, LinearMap.map_smul, LinearMap.comp_apply, LinearMap.comp_apply,
    ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, LinearMap.map_smul]
  rfl

end GlobalTheory.RowVertexInv.FactorTheta

namespace GlobalTheory.RowVertexInv.FactorTheta

open Matrix

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem keepStd (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (hk : finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le) (v : Fin (G.V (.grid (j + 1) D.R.m)).rank → Formalism.IndefR.Lev.EAf D) :
    v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m))) ↔
      (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (moved S j k)).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m))) :=
  GlobalTheory.T.conjugatedLevelElement_keeps_standardLattice S j hj k hk v

theorem mulVec_mulVec_inv {n : ℕ} {R : Type} [CommRing R] (X : GL (Fin n) R) (v : Fin n → R) :
    X.1 *ᵥ ((X⁻¹).1 *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem keepPair (S : GridChoice W U) {i : ℕ} (hi : i + 1 ≤ D.R.m) (x : GA D (G.V (.grid i D.R.m))) (y : GA D (G.V (.grid (i + 1) D.R.m)))
    (hxf : x ∈ GfC (G.V (.grid i D.R.m))) (hyf : y ∈ GfC (G.V (.grid (i + 1) D.R.m)))
    (hx : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid i D.R.m))) ↔
      (Formalism.IndefR.Lev.finE (G.V (.grid i D.R.m)) x).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid i D.R.m))))
    (hy : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (i + 1) D.R.m))) ↔
      (Formalism.IndefR.Lev.finE (G.V (.grid (i + 1) D.R.m)) y).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (i + 1) D.R.m))))
    (u : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    u ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True) ↔
      actO _ _ (G.toPair (.chi i D.R.m) x y).1 (G.toPair (.chi i D.R.m) x y).2 u ∈
        latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True) := by
  have sdT := S.N.selfDual (X := .grid i D.R.m) ⟨by omega, rfl⟩
  have sdS := S.N.selfDual (X := .grid (i + 1) D.R.m) ⟨hi, rfl⟩
  have hspan {n : ℕ} (B : GL (Fin n) D.host.E) :
      Submodule.span D.host.E (colLat B : Set (Fin n → D.host.E)) = ⊤ := by
    rw [colLat, Submodule.span_span_of_tower]
    change Submodule.span D.host.E (Set.range (B : Matrix (Fin n) (Fin n) D.host.E).col) = ⊤
    rw [← Matrix.range_mulVecLin]
    exact LinearMap.range_eq_top.mpr (Matrix.mulVec_surjective_iff_isUnit.mpr B.isUnit)
  obtain ⟨βT, hβT⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F _ sdT.1.fg (hspan _)
  obtain ⟨βS, hβS⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F _ sdS.1.fg (hspan _)
  have keep : ∀ {V : HSp D} (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)),
      Formalism.L2.DIV.IsFrame β Λ → ∀ X : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D),
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ X.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) → X ∈ Formalism.L2.DIV.St β := by
    intro V Λ β hβ X hX
    refine (GlobalTheory.LevSplit.mem_St_iff β Λ hβ X).2 ⟨fun v hv => (hX v).1 hv, fun v hv => ?_⟩
    refine (hX _).2 ?_
    rw [mulVec_mulVec_inv]
    exact hv
  have stx := keep _ βT hβT _ hx
  have sty := keep _ βS hβS _ hy
  have sty' : Formalism.IndefR.Lev.finE (G.pS (.chi i D.R.m : Pair T)) (negGA _ y) ∈ Formalism.L2.DIV.St βS := sty
  exact GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))
    (S.N.latS (.chi i D.R.m)) (S.N.latT (.chi i D.R.m)) βS βT (isSelfDualC_neg sdS) sdT hβS hβT
    (negGA _ y) x sty' stx u

theorem keepLow (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (hk : finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le) (u : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))) :
    u ∈ latO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T)) (S.N.latS (.chi j D.R.m) : Set _) (S.N.latT (.chi j D.R.m) : Set _) (fun _ => True) ↔
      actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k)).1 (G.toPair (.chi j D.R.m) 1 (moved S j k)).2 u ∈
        latO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T)) (S.N.latS (.chi j D.R.m) : Set _) (S.N.latT (.chi j D.R.m) : Set _) (fun _ => True) := by
  have h1 : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid j D.R.m))) ↔
      (Formalism.IndefR.Lev.finE (G.V (.grid j D.R.m)) 1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid j D.R.m))) := by
    intro v
    have e0 : Formalism.IndefR.Lev.finE (G.V (.grid j D.R.m)) 1 = 1 := MonoidHom.map_one _
    have e1 : (Formalism.IndefR.Lev.finE (G.V (.grid j D.R.m)) 1).1 *ᵥ v = v := by rw [e0]; exact Matrix.one_mulVec v
    rw [e1]
  have h2 : moved S j k ∈ GfC (G.V (.grid (j + 1) D.R.m)) := ((S.N.u (.grid (j + 1) D.R.m))⁻¹ * k * S.N.u _).2
  have h3 := keepStd S j hj k hk
  exact keepPair S (i := j) (by omega) 1 (moved S j k) (one_mem _) h2 h1 h3 u

theorem keepHigh (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (hk : finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le) (u : WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))) :
    u ∈ latO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T)) (S.N.latS (.chi (j + 1) D.R.m) : Set _) (S.N.latT (.chi (j + 1) D.R.m) : Set _) (fun _ => True) ↔
      actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).1 (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2 u ∈
        latO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T)) (S.N.latS (.chi (j + 1) D.R.m) : Set _) (S.N.latT (.chi (j + 1) D.R.m) : Set _) (fun _ => True) := by
  have h1 : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1 + 1) D.R.m))) ↔
      (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1 + 1) D.R.m)) 1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1 + 1) D.R.m))) := by
    intro v
    have e0 : Formalism.IndefR.Lev.finE (G.V (.grid (j + 1 + 1) D.R.m)) 1 = 1 := MonoidHom.map_one _
    have e1 : (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1 + 1) D.R.m)) 1).1 *ᵥ v = v := by rw [e0]; exact Matrix.one_mulVec v
    rw [e1]
  have h2 : moved S j k ∈ GfC (G.V (.grid (j + 1) D.R.m)) := ((S.N.u (.grid (j + 1) D.R.m))⁻¹ * k * S.N.u _).2
  have h3 := keepStd S j hj k hk
  exact keepPair S (i := j + 1) (by omega) (moved S j k) 1 h2 (one_mem _) h3 h1 u

theorem selfDual (S : GridChoice W U) {i : ℕ} (hi : i + 1 ≤ D.R.m) :
    IsSelfDualC (G.pS (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m)) ∧ IsSelfDualC (G.pT (.chi i D.R.m : Pair T)) (S.N.latT (.chi i D.R.m)) :=
  ⟨isSelfDualC_neg (S.N.selfDual (X := .grid (i + 1) D.R.m) ⟨hi, rfl⟩), S.N.selfDual (X := .grid i D.R.m) ⟨by omega, rfl⟩⟩

theorem vacScalar (S : GridChoice W U) {i : ℕ} (hi : i + 1 ≤ D.R.m) (x : FinPt G (.grid i D.R.m)) (y : FinPt G (.grid (i + 1) D.R.m))
    (hΛ : ∀ u, u ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True) ↔
      actO _ _ (G.toPair (.chi i D.R.m) x y).1 (G.toPair (.chi i D.R.m) x y).2 u ∈
        latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True)) :
    ∃ c : ℂ, W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) x y) (S.Z.vac (.chi i D.R.m)) = c • S.Z.vac (.chi i D.R.m) :=
  GlobalTheory.T.chiArrowPair_moves_standardVacuum_by_scalar S hi x y hΛ

end GlobalTheory.RowVertexInv.FactorTheta

namespace GlobalTheory.RowVertexInv.FactorTheta

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem position_theta (S : GridChoice W U) {t : T} {e : AE D} (d : PureDat G t)
    (hd : (∀ j, (d.1 j).e = e ∧ (d.1 j).z = 1) ∧ ∀ i, (d.2 i).e = e ∧ (d.2 i).z = 1)
    (hv : (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) (a : Fin D.R.m ⊕ Fin D.R.m) :
    IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) (S.N.latS (positionPair t D.R.m a) : Set _)
        (S.N.latT (positionPair t D.R.m a) : Set _) fun _ => True) 1 (S.Z.vac (positionPair t D.R.m a)) (fnOf d a) (vecOf S d a) := by
  have key : ∀ {p : Pair T} (x : FinDatum G t p), x.e = e → x.z = 1 → S.Z.HasVec x →
      IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e
        (latO (G.pS p) (G.pT p) (S.N.latS p : Set _) (S.N.latT p : Set _) fun _ => True) 1 (S.Z.vac p) x.fn (S.Z.vec x) := by
    intro p x hxe hxz hx
    obtain ⟨f, hf⟩ := hx
    have h1 : S.Z.vec x = f := by
      rw [Normal.vec, FinDatum.vec_eq W hf, hxz]
      have h2 : W.om p (1, 1) = 1 := map_one _
      rw [h2]; rfl
    rw [h1, ← hxe]; exact hf
  rcases a with j | i
  · exact key (d.1 j) (hd.1 j).1 (hd.1 j).2 (hv.1 j)
  · exact key (d.2 i) (hd.2 i).1 (hd.2 i).2 (hv.2 i)

theorem scalar_ne_zero {p : Pair T} (g : GA D (G.pS p) × GA D (G.pT p)) {c : ℂ} {f : WO (G.pS p) (G.pT p) → ℂ}
    (hf : f ≠ 0) (h : W.om p g f = c • f) : c ≠ 0 := by
  intro hc
  apply hf
  have e1 : W.om p g⁻¹ (W.om p g f) = f := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [h, hc, zero_smul, map_zero] at e1
  exact e1.symm

theorem vac_ne_zero (S : GridChoice W U) {i : ℕ} (hi : i + 1 ≤ D.R.m) : S.Z.vac (.chi i D.R.m) ≠ 0 := by
  intro h0
  obtain ⟨⟨p, hp⟩, hn⟩ := (S.Z.vac_is (.chi i D.R.m) ⟨hi, rfl⟩).2.norm
  have := hn p hp
  simp [nrm2, h0] at this

theorem vecOf_eq_intertwiner : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ}, S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∃ (c₁ c₂ : ℂ) (Tm : ∀ a, FactorFn G t a →ₗ[ℂ] FactorFn G t a), W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) ∧ W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) = c₂ • S.Z.vac (.chi (j + 1) D.R.m) ∧ ∀ d ∈ τ.support, ∀ a, vecOf S d a = Tm a (fnOf d a) ∧ moveV S j hj k (vecOf S d) a = Tm a (scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a) := by
  intro D T L sc G W U S t Φ β τ hexp hvec j hj k hk
  classical
  obtain ⟨e, he, hsupp, -⟩ := hexp
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum he
  let Tm : ∀ a, FactorFn G t a →ₗ[ℂ] FactorFn G t a := fun a =>
    Classical.epsilon (IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) (S.N.latS (positionPair t D.R.m a) : Set _)
        (S.N.latT (positionPair t D.R.m a) : Set _) fun _ => True) 1 (S.Z.vac (positionPair t D.R.m a)))
  have hth : ∀ d ∈ τ.support, ∀ a, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) (S.N.latS (positionPair t D.R.m a) : Set _)
        (S.N.latT (positionPair t D.R.m a) : Set _) fun _ => True) 1 (S.Z.vac (positionPair t D.R.m a)) (fnOf d a) (vecOf S d a) :=
    fun d hd a => position_theta S d ⟨fun j' => ⟨((hsupp d hd).1 j').2.1, ((hsupp d hd).1 j').2.2⟩,
      fun i => ⟨((hsupp d hd).2 i).2.1, ((hsupp d hd).2 i).2.2⟩⟩ (hvec d hd) a
  have hTm : ∀ d ∈ τ.support, ∀ a, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) (S.N.latS (positionPair t D.R.m a) : Set _)
        (S.N.latT (positionPair t D.R.m a) : Set _) fun _ => True) 1 (S.Z.vac (positionPair t D.R.m a)) (Tm a) ∧
      vecOf S d a = Tm a (fnOf d a) := by
    intro d hd a
    have h := hth d hd a
    have hs := Classical.epsilon_spec h.1
    exact ⟨hs, h.2 _ hs⟩
  have hj1 : j + 1 ≤ D.R.m := by omega
  have hj2 : j + 1 + 1 ≤ D.R.m := by omega
  obtain ⟨c₁, hc₁⟩ := vacScalar S hj1 1 ((S.N.u _)⁻¹ * k * S.N.u _) (keepLow S j hj k hk)
  obtain ⟨c₂, hc₂⟩ := vacScalar S hj2 ((S.N.u _)⁻¹ * k * S.N.u _) 1 (keepHigh S j hj k hk)
  refine ⟨c₁, c₂, Tm, hc₁, hc₂, fun d hd a => ⟨(hTm d hd a).2, ?_⟩⟩
  by_cases h2 : a = .inr ⟨j + 1, hj⟩
  · subst h2
    have e1 : moveV S j hj k (vecOf S d) (.inr ⟨j + 1, hj⟩) = W.om (.chi (j + 1) D.R.m)
        (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (vecOf S d (.inr ⟨j + 1, hj⟩)) := by
      unfold moveV; exact Function.update_self _ _ _
    have e2 : scaleAt j hj c₁ c₂ (.inr ⟨j + 1, hj⟩) = c₂ := by unfold scaleAt; exact Function.update_self _ _ _
    have e3 : movFn S j hj k (fnOf d) (.inr ⟨j + 1, hj⟩) = fun x => fnOf d (.inr ⟨j + 1, hj⟩)
        (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1 (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 x) := by
      unfold movFn; exact Function.update_self _ _ _
    rw [e1, e2, e3]
    exact om_theta_eq (W.om_is _ (by simp only [Pair.InRange, Pair.big, Node.InRange]; omega)) hee hinf
      (selfDual S hj2).1 (selfDual S hj2).2 (S.Z.vac_is (.chi (j + 1) D.R.m) ⟨hj2, rfl⟩).2.theta _ (keepHigh S j hj k hk)
      (scalar_ne_zero _ (vac_ne_zero S hj2) hc₂) hc₂ (hTm d hd (.inr ⟨j + 1, hj⟩)).1 (hth d hd (.inr ⟨j + 1, hj⟩))
  by_cases h1 : a = .inr ⟨j, by omega⟩
  · subst h1
    have hne : (Sum.inr ⟨j, by omega⟩ : Fin D.R.m ⊕ Fin D.R.m) ≠ .inr ⟨j + 1, hj⟩ := by simp
    have e1 : moveV S j hj k (vecOf S d) (.inr ⟨j, by omega⟩) = W.om (.chi j D.R.m)
        (G.toPair (.chi j D.R.m) 1 (moved S j k)) (vecOf S d (.inr ⟨j, by omega⟩)) := by
      unfold moveV; exact (Function.update_of_ne hne _ _).trans (Function.update_self _ _ _)
    have e2 : scaleAt j hj c₁ c₂ (.inr ⟨j, by omega⟩) = c₁ := by
      unfold scaleAt; exact (Function.update_of_ne hne _ _).trans (Function.update_self _ _ _)
    have e3 : movFn S j hj k (fnOf d) (.inr ⟨j, by omega⟩) = fun x => fnOf d (.inr ⟨j, by omega⟩)
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2 x) := by
      unfold movFn; exact (Function.update_of_ne hne _ _).trans (Function.update_self _ _ _)
    rw [e1, e2, e3]
    exact om_theta_eq (W.om_is _ (by simp only [Pair.InRange, Pair.big, Node.InRange]; omega)) hee hinf
      (selfDual S hj1).1 (selfDual S hj1).2 (S.Z.vac_is (.chi j D.R.m) ⟨hj1, rfl⟩).2.theta _ (keepLow S j hj k hk)
      (scalar_ne_zero _ (vac_ne_zero S hj1) hc₁) hc₁ (hTm d hd (.inr ⟨j, by omega⟩)).1 (hth d hd (.inr ⟨j, by omega⟩))
  · have e1 : moveV S j hj k (vecOf S d) a = vecOf S d a := by
      unfold moveV; exact (Function.update_of_ne h2 _ _).trans (Function.update_of_ne h1 _ _)
    have e2 : scaleAt j hj c₁ c₂ a = 1 := by
      unfold scaleAt; exact (Function.update_of_ne h2 _ _).trans (Function.update_of_ne h1 _ _)
    have e3 : movFn S j hj k (fnOf d) a = fnOf d a := by
      unfold movFn; exact (Function.update_of_ne h2 _ _).trans (Function.update_of_ne h1 _ _)
    rw [e1, e2, e3, one_smul]
    exact (hTm d hd a).2

end GlobalTheory.RowVertexInv.FactorTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarIdempotentValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.SplitMoveKappa

theorem qbar_of_root {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : ζ ∈ TaylorLogMetric.Qbar := by
  have halg : IsAlgebraic ℚ ζ := by
    refine ⟨Polynomial.X ^ n - Polynomial.C 1, ?_, ?_⟩
    · exact Polynomial.X_pow_sub_C_ne_zero hn 1
    · simp [hζ]
  exact mem_algebraicClosure_iff.2 halg

theorem mod1All_root {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : Mod1All ζ := by
  refine ⟨qbar_of_root hn hζ, fun σ => ?_⟩
  have h1 : (⟨ζ, qbar_of_root hn hζ⟩ : TaylorLogMetric.Qbar) ^ n = 1 := by ext; simpa using hζ
  have h2 : (σ ⟨ζ, qbar_of_root hn hζ⟩) ^ n = 1 := by rw [← map_pow, h1, map_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, h2, norm_one])

theorem lamC_mem {q : ℕ} [Fact q.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[q]) {x : ℂ} (h : x ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam x = lam ⟨x, h⟩ := dif_pos h

theorem unitAt_mul {q : ℕ} [Fact q.Prime] {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar)
    (ux : GlobalTheory.MovedKappaEx.UnitAt q x) (uy : GlobalTheory.MovedKappaEx.UnitAt q y) : GlobalTheory.MovedKappaEx.UnitAt q (x * y) := by
  intro lam
  have e : (⟨x * y, mul_mem hx hy⟩ : TaylorLogMetric.Qbar) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  have hx' := ux lam
  have hy' := uy lam
  rw [lamC_mem lam hx] at hx'
  rw [lamC_mem lam hy] at hy'
  rw [lamC_mem lam (mul_mem hx hy), e, map_mul, norm_mul, hx', hy', one_mul]

theorem unitAt_inv {q : ℕ} [Fact q.Prime] {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar)
    (ux : GlobalTheory.MovedKappaEx.UnitAt q x) : GlobalTheory.MovedKappaEx.UnitAt q x⁻¹ := by
  intro lam
  have e : (⟨x⁻¹, inv_mem hx⟩ : TaylorLogMetric.Qbar) = (⟨x, hx⟩ : TaylorLogMetric.Qbar)⁻¹ := rfl
  have hx' := ux lam
  rw [lamC_mem lam hx] at hx'
  rw [lamC_mem lam (inv_mem hx), e, map_inv₀, norm_inv, hx', inv_one]

theorem unitAt_root (q : ℕ) [Fact q.Prime] {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) :
    GlobalTheory.MovedKappaEx.UnitAt q ζ := by
  intro lam
  have h1 : (⟨ζ, qbar_of_root hn hζ⟩ : TaylorLogMetric.Qbar) ^ n = 1 := by ext; simpa using hζ
  have h2 : (lam ⟨ζ, qbar_of_root hn hζ⟩) ^ n = 1 := by rw [← map_pow, h1, map_one]
  rw [lamC_mem lam (qbar_of_root hn hζ)]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, h2, norm_one])

end GlobalTheory.SplitMoveKappa
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyStagesParamSizeConditions
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.LedSize


set_option maxHeartbeats 1000000 in
theorem evG_exists_sizeRows : EvG fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) → (∀ w j, X.toD7.what₂.Aj j w = 0) → ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := GlobalTheory.EX.szRow_numAt eps h0 h1 C hC
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch ((le_max_left _ _).trans hch)
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)
  refine ⟨max (max x0 x1) (max (44 ^ 4) ((8 : ℝ) ^ (4 / eps))), ?_⟩
  rintro K rfl rfl rfl hs hx hG X hO heta hA
  have hx' := (le_max_left _ _).trans hx
  have hxL := (le_max_right _ _).trans hx
  have hP := K.ok
  have hOk := hG.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK := (Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split
  have hdel : D.s.Del = (GlobalTheory.EX.Delv K.s K.cD : ℚ) := by
    have τ : Tau K.P.R := tauPl D (false, 0)
    have hk := K.P.R.m_add_three_le_k
    have hm := K.P.R.two_le_m
    have hl : 0 + 1 < K.P.R.k - 1 := by omega
    have a1 := D.s.cloud_gap K.P.u₀ τ 0 hl
    have a2 := congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)
    have a3 := a1.symm.trans a2
    have e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1 := by omega
    dsimp only at a3
    rw [e] at a3
    push_cast at a3
    linarith
  obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx') hP.rank hP.val
    (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta (fun u => by
      have e : (D.mem u).A.GamP = K.Lv.GamP := Cc.A_GamP u
      rw [e, K.Gam_eq, GlobalTheory.EX.OB.GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) (fun w _ j _ _ => hA w j)
  obtain ⟨⟨M⟩, -, -⟩ := hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx') e4
    ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
  refine ⟨L, e1, ?_⟩
  have hq : ((GlobalTheory.ChiGrid.q0 D : ℕ) : ℝ) < L.sc.X' := by
    have hmem := hOk.small.1
    rcases hOk.lev _ hmem with ⟨i, hi⟩ | hlt
    · exact absurd hi (hOk.small.2.2.2.1 i)
    · rw [e1]; exact hlt
  have xe : L.sc.x = K.s.x := by rw [e1]
  have ee : L.sc.eps = eps := by rw [e1]; exact hs
  refine GlobalTheory.BigTop.Fun.SetAtModel.sizeRows_of M.params M.parT (M.CnW_eq.trans hC.1.2.2.2.2.2.2.2.1) M.sizes
    M.win.1.1 M.win.2.1.1 M.win.2.1.2 M.win.2.2.1 M.g_le hq M.ccK_top ?_ (by rw [xe]; exact le_of_max_le_left hxL)
  rw [xe, ee]
  have e2 : (8 : ℝ) = ((8 : ℝ) ^ (4 / eps)) ^ (eps / 4) := by
    rw [← Real.rpow_mul (by norm_num), show 4 / eps * (eps / 4) = 1 by field_simp, Real.rpow_one]
  rw [e2]
  exact Real.rpow_le_rpow (by positivity) (le_of_max_le_right hxL) (by positivity)

end GlobalTheory.Mem.R3.LedSize

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodVOfGoodL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
open Formalism.IndefR.CxPass Formalism.IndefR.CxPass.LevelOperators

namespace GlobalTheory.GoodModelVec

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 4000000 in
theorem actL_coord (R : RealDat D A Ks) (hr : R.grp_red_L) (hj : R.models_jV) (i : Fin D.R.m) (hc : (R.cV i).Is) (t : T0)
    (g : G) (x : (A.fam.L i t).S.Forms) (ℓ : (R.cV i).W →ₗ[ℂ] ℂ) :
    actL (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (fun h => ℓ (R.extV i t (R.jV i t x) h)) =
      fun h => ℓ (R.extV i t (R.jV i t ((A.fam.L i t).r g x)) h) := by
  have hT := GlobalTheory.RationalFormsAction.isTranslate_act_V R hr hj i t g x
  have hk : ∃ κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ := by
    obtain ⟨κ, h1, -⟩ := GlobalTheory.LiftEquivariance.exists_adelic_lift hT
    exact ⟨κ, h1⟩
  funext h
  refine (GlobalTheory.SecLift.actL_apply hk _ h).trans ?_
  have hs := hk.choose_spec
  have e1 := finE_eq (Vc D i) hk.choose
  have hq : (finHom (Vc D i)).rangeRestrict hk.choose ∈ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := by
    show Formalism.UG.bc (swapAE D) (finHom (Vc D i) hk.choose) ∈ lev _ _ _ _
    rw [← e1]
    exact ⟨hs.2.1, Subgroup.mem_top _⟩
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.LiftsTo (Vc D i) (R.βV i) (R.datVt i t) ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩ (R.eG g) := by
    show rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) (finHom (Vc D i) hk.choose)) = R.eG g
    rw [← e1]; exact hs.2.2
  have hT2 : ∀ u, (R.HV i t).e ((R.jV i t) (((A.fam.L i t).r g) x)) u =
      ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩)⁻¹ : ℂˣ) : ℂ) •
        (R.HV i t).e ((R.jV i t) x) (u * (finHom (Vc D i)).rangeRestrict hk.choose) := hT.2 _ hl
  have h2 := GlobalTheory.SecLift.coord_translate (R.cV i) hc hs.1 _ hT2 ℓ h
  have ec := GlobalTheory.LiftEquivariance.ch_eq (V := Vc D i) (β := R.βV i) (L := R.datVt i t) ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩
  have e2 : levFn (R.βV i) (flagL (R.datVt i t)) (Formalism.UG.bc (swapAE D) ((finHom (Vc D i)) hk.choose)) =
      levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) hk.choose) := by rw [e1]
  have hc' : ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩ : ℂˣ)) : ℂ) =
      levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) hk.choose := congrArg Units.val (ec.trans e2)
  rw [Units.val_inv_eq_inv_val, hc'] at h2
  exact h2.symm


set_option maxHeartbeats 4000000 in
theorem goodV_of_fix (R : RealDat D A Ks) (hr : R.grp_red_L) (hj : R.models_jV) (i : Fin D.R.m) (hc : (R.cV i).Is)
    (x : (A.fam.L i A.μ0).S.Forms) (hx : opF (A.fam.L i A.μ0).r (idemOf A.X) x = x) :
    GlobalTheory.LiftRows.GoodV R i (R.jV i A.μ0 x) := by
  intro ℓ
  let Φ : (R.HV i A.μ0).H →ₗ[ℂ] (GA D (Vc D i) → ℂ) := ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i A.μ0
  have hΦ : ∀ y, Φ y = fun h => ℓ (R.extV i A.μ0 y h) := fun _ => rfl
  have key : ∀ g, Φ (R.jV i A.μ0 ((A.fam.L i A.μ0).r g x)) =
      actL (Vc D i) (R.βV i) (R.datVt i A.μ0) (R.eG g) (Φ (R.jV i A.μ0 x)) := fun g =>
    (actL_coord R hr hj i hc A.μ0 g x ℓ).symm
  have hs : ∀ a, RealDat.eC (A := A) (sg0 D A) a = D.what₂.embLL ((idemOf A.X).coeff a) := fun a => by
    show sg0 D A _ = _
    rw [sg0, sgAt_mk D.what₂.embLL R.hv0]
  have e1 : Φ (R.jV i A.μ0 (opF (A.fam.L i A.μ0).r (idemOf A.X) x)) =
      gaL (Vc D i) (R.βV i) (R.datVt i A.μ0) R.eG (RealDat.eC (A := A) (sg0 D A)) (Φ (R.jV i A.μ0 x)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [opF, gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, LinearMap.map_smulₛₗ, key, hs, RingHom.id_apply]
    rfl
  rw [← hΦ, ← e1, hx]

noncomputable def goodSub (R : RealDat D A Ks) (i : Fin D.R.m) : Submodule ℂ (R.HV i A.μ0).H :=
  ⨅ ℓ : (R.cV i).W →ₗ[ℂ] ℂ, LinearMap.ker
    (gaL (Vc D i) (R.βV i) (R.datVt i A.μ0) R.eG (RealDat.eC (A := A) (sg0 D A)) ∘ₗ (ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i A.μ0) -
      ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i A.μ0)

theorem mem_goodSub (R : RealDat D A Ks) (i : Fin D.R.m) (y : (R.HV i A.μ0).H) :
    y ∈ goodSub R i ↔ GlobalTheory.LiftRows.GoodV R i y := by
  simp only [goodSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

end GlobalTheory.GoodModelVec


open GlobalTheory.GoodModelVec in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.goodV_of_goodL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ (j : Fin D.R.m) (y : (R.toCx3 F).FLC j A3.A.fam.μ0), y ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j → GoodV R.toRealDat j (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hC _ _ _ j y hy
  have hM := hC.base.models
  have hr := hC.base.grp.red_L
  have hfix : ∀ x ∈ BlockGood.goodR (A3.fam3.F.L j A3.A.fam.μ0) (A3.fam3.F.lvlA F.P0 F.ψ0),
      opF (A3.A.fam.L j A3.A.fam.μ0).r (idemOf A3.A.X) x = x := by
    intro x hx
    rw [goodR_eq] at hx
    obtain ⟨z, rfl⟩ := hx
    have hid := opF_goodAt_idem (A3.A.fam.L j A3.A.fam.μ0).r A3.A.X hok.ok2.irr ⊥ 1
    rw [goodAt_bot] at hid
    show opF _ (idemOf A3.A.X) (opF _ (idemOf A3.A.X * lvlIdem F.P0 F.ψ0⁻¹) z) = opF _ (idemOf A3.A.X * lvlIdem F.P0 F.ψ0⁻¹) z
    rw [opF_mul, LinearMap.comp_apply]
    exact LinearMap.congr_fun hid _
  have hy' : y ∈ Submodule.span ℂ ((R.toCx3 F).jL j A3.A.fam.μ0 ''
      (BlockGood.goodR (A3.fam3.F.L j A3.A.fam.μ0) (A3.fam3.F.lvlA F.P0 F.ψ0) : Set _)) := hy
  rw [← mem_goodSub]
  clear hy
  induction hy' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    exact (mem_goodSub _ _ _).2 (goodV_of_fix R.toRealDat hr hM.jV j (hM.cV j) x (hfix x hx))
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ (Links.cj (twAt D.what₂.embLL A3.A.v0) c) ha
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryInBasisIntegralAtConjugatePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjPlaceIntegerMem
namespace ConjugatePlaceIntegrality
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.ConjPlaceInt

variable {D : D7}

theorem sg_mem_OA {x : GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Ef D} (hx : x ∈ OA D) : sg D x ∈ OA D :=
  Formalism.UG.P.csDual_sig_mem D.sp.cm.sig hx

theorem cpt_sg_mem_integers : ∀ {D : D7} (Q : Pl D.host.E) (z : Lev.EAf D),
    cpt Q z ∈ Q.adicCompletionIntegers D.host.E →
      cpt (GlobalTheory.IdemSupport.cP Q) (sg D z) ∈ (GlobalTheory.IdemSupport.cP Q).adicCompletionIntegers D.host.E := by
  intro D Q z hz
  obtain ⟨e, -, -, h1, h0⟩ := GlobalTheory.StdFrames.exists_idem (D := D) ({Q} : Set (Pl D.host.E))
  have he1 : cpt Q e = 1 := h1 Q rfl
  have hez : e * z ∈ OA D := (mem_OA_iff _).2 fun P => by
    by_cases hP : P = Q
    · subst hP
      rw [map_mul, he1, one_mul]
      exact hz
    · rw [map_mul, h0 P hP, zero_mul]
      exact zero_mem _
  have hs : cpt (GlobalTheory.IdemSupport.cP Q) (sg D e) = 1 := by
    have h2 : cpt (GlobalTheory.IdemSupport.cP Q) (sg D (1 - e)) = 0 :=
      cpt_sg_eq_zero (by rw [cP_cP, map_sub, map_one, he1, sub_self])
    rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at h2
    exact h2.symm
  have h3 := (mem_OA_iff _).1 (sg_mem_OA hez) (GlobalTheory.IdemSupport.cP Q)
  rwa [map_mul, map_mul, hs, one_mul] at h3

end GlobalTheory.CompanionTheory.ConjPlaceInt

end
end

end ConjugatePlaceIntegrality
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryInBasisIntegralAtConjugatePlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjPlaceUnitary

open GlobalTheory.AdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents (cjA inc)

variable {D : D7}

theorem entries_of_mem_GLint {L : Type} [Field L] {n : ℕ} (O : Subring L) {g : GL (Fin n) L}
    (hg : g ∈ Formalism.UG.GLint (Fin n) O) (i j : Fin n) : g.1 i j ∈ O ∧ (g⁻¹).1 i j ∈ O := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨(h.1 i j).2, by rw [← map_inv]; exact ((h⁻¹).1 i j).2⟩

theorem frame_change {n : ℕ} {β β' : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : IsFrame β Λ) (h' : IsFrame β' Λ) (i j : Fin n) : (β⁻¹ * β').1 i j ∈ OA D := by
  have h1 : β'.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := (h' _).2 fun k => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have h2 := (h _).1 h1 i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h2
  exact h2

theorem dual_frame {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsFrame β Λ) (hd : Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ) :
    ∃ β' : GL (Fin V.rank) (Lev.EAf D), Formalism.UG.cT (cjA D) β.val * V.gram.map (inc D) * β'.val = 1 ∧
      (∀ i j, (β⁻¹ * β').1 i j ∈ OA D) ∧ (∀ i j, (β'⁻¹ * β).1 i j ∈ OA D) := by
  have hL := GlobalTheory.DiagLiftFix.isLattice_of_isFrame hβ
  have hsd : IsSelfDualC V Λ := ⟨hL, fun y => by
    have key := GlobalTheory.SDFrameLattice.mem_dualL_iff V Λ y
    rw [hd] at key
    exact key⟩
  obtain ⟨β', h1, -⟩ := exists_dual_frame V β
  have h' : IsFrame β' Λ := by
    intro y
    rw [← hd, ← mem_hat, mem_hat_dualL_iff (selfDual_isFullLattice hsd)]
    rw [← dual_frame_gen (OA D) (cjA D) (fun _ => cjA_mem) h1]
    refine forall_congr' fun x => ?_
    rw [mem_hat, hβ, ← cjA_mem_iff, cjA_hA, hA_eq]
  exact ⟨β', h1, frame_change hβ h', frame_change h' hβ⟩

end GlobalTheory.ConjPlaceUnitary

namespace GlobalTheory.ConjPlaceUnitary

open GlobalTheory.AdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents (cjA inc)

theorem conj_formula_gen {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ}
    (J B Bi B' B'i Z Zi : Matrix (Fin n) (Fin n) A) (hB : B * Bi = 1) (hB' : B' * B'i = 1) (hZ : Z * Zi = 1)
    (h1 : Formalism.UG.cT σ B * J * B' = 1) (hz : Formalism.UG.cT σ Z * J * Z = J) :
    Bi * Z * B = Bi * B' * Formalism.UG.cT σ (Bi * Zi * B) * (B'i * B) := by
  have hcBi : Formalism.UG.cT σ Bi * Formalism.UG.cT σ B = 1 := by
    rw [← GlobalTheory.StdFrames.cT_mul', hB, GlobalTheory.StdFrames.cT_one']
  have hzi : Formalism.UG.cT σ Zi * Formalism.UG.cT σ Z = 1 := by
    rw [← GlobalTheory.StdFrames.cT_mul', hZ, GlobalTheory.StdFrames.cT_one']
  have hM : Formalism.UG.cT σ B * J = B'i := by
    calc Formalism.UG.cT σ B * J = Formalism.UG.cT σ B * J * (B' * B'i) := by rw [hB', Matrix.mul_one]
      _ = B'i := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h1' : B' * (Formalism.UG.cT σ B * J) = 1 := by rw [hM, hB']
  have hz' : Formalism.UG.cT σ Zi * (Formalism.UG.cT σ Z * J * Z) = J * Z := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hzi, Matrix.one_mul]
  rw [GlobalTheory.StdFrames.cT_mul', GlobalTheory.StdFrames.cT_mul', ← hM]
  calc Bi * Z * B = Bi * (B' * (Formalism.UG.cT σ B * J)) * Z * B := by rw [h1', Matrix.mul_one]
    _ = Bi * B' * Formalism.UG.cT σ B * (Formalism.UG.cT σ Zi * (Formalism.UG.cT σ Z * J * Z)) * B := by
        rw [hz']
        simp only [Matrix.mul_assoc]
    _ = Bi * B' * Formalism.UG.cT σ B * (Formalism.UG.cT σ Zi * (Formalism.UG.cT σ Bi * Formalism.UG.cT σ B) * J) * B := by
        rw [hz, hcBi, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

variable {D : D7}

theorem conj_formula {n : ℕ} (J : Matrix (Fin n) (Fin n) (Lev.EAf D)) (β β' z : GL (Fin n) (Lev.EAf D))
    (h1 : Formalism.UG.cT (cjA D) β.val * J * β'.val = 1) (hz : Formalism.UG.cT (cjA D) z.val * J * z.val = J) :
    (β⁻¹ * z * β).val = (β⁻¹ * β').val * Formalism.UG.cT (cjA D) (β⁻¹ * z⁻¹ * β).val * (β'⁻¹ * β).val := by
  simp only [Units.val_mul]
  exact conj_formula_gen (cjA D) J β.val (β⁻¹).val β'.val (β'⁻¹).val z.val (z⁻¹).val
    (Units.mul_inv β) (Units.mul_inv β') (Units.mul_inv z) h1 hz

end GlobalTheory.ConjPlaceUnitary

namespace GlobalTheory.ConjPlaceUnitary

open GlobalTheory.AdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents (cjA inc)

variable {D : D7}

theorem cpt_conj_mem {n : ℕ} (w : Pl D.host.E) (P C M : Matrix (Fin n) (Fin n) (Lev.EAf D))
    (hP : ∀ i j, P i j ∈ OA D) (hM : ∀ i j, M i j ∈ OA D)
    (hC : ∀ i j, cpt w (C i j) ∈ w.adicCompletionIntegers D.host.E) (i j : Fin n) :
    cpt (Formalism.DivisionValues.conjPl w) ((P * Formalism.UG.cT (cjA D) C * M) i j) ∈
      (Formalism.DivisionValues.conjPl w).adicCompletionIntegers D.host.E := by
  rw [GlobalTheory.FunObj.conjPl_eq_cP]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul]
  refine sum_mem fun l _ => mul_mem (sum_mem fun k _ => mul_mem ?_ ?_) ?_
  · exact (mem_OA_iff _).1 (hP i k) _
  · exact ConjugatePlaceIntegrality.GlobalTheory.CompanionTheory.ConjPlaceInt.cpt_sg_mem_integers w (C l k) (hC l k)
  · exact (mem_OA_iff _).1 (hM l j) _

end GlobalTheory.ConjPlaceUnitary

namespace GlobalTheory.ConjPlaceUnitary

open GlobalTheory.AdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents (cjA inc)

theorem inBasis_conjPl_mem_KO : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsFrame β Λ → Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ → ∀ x ∈ UA D.sp.cm V.gram, ∀ w : Pl D.host.E, inBasis rfl β w x ∈ GlobalTheory.SplitWeil.KO (Kw w) (Fin V.rank) → inBasis rfl β (Formalism.DivisionValues.conjPl w) x ∈ GlobalTheory.SplitWeil.KO (Kw (Formalism.DivisionValues.conjPl w)) (Fin V.rank) := by
  intro D V β Λ hβ hd x hx w hw
  obtain ⟨β', h1, hP, hM⟩ := dual_frame hβ hd
  have hu : ∀ z ∈ UA D.sp.cm V.gram, Formalism.UG.cT (cjA D) z.val * V.gram.map (inc D) * z.val = V.gram.map (inc D) :=
    fun z hz => hz
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion] at hw ⊢
  have hC : ∀ a b, cpt w ((β⁻¹ * x * β).val a b) ∈ w.adicCompletionIntegers D.host.E := fun a b =>
    (entries_of_mem_GLint _ hw a b).1
  have hC' : ∀ a b, cpt w ((β⁻¹ * x⁻¹ * β).val a b) ∈ w.adicCompletionIntegers D.host.E := fun a b => by
    have := (entries_of_mem_GLint _ hw a b).2
    rw [← map_inv] at this
    exact this
  refine GlobalTheory.FunObj.mem_GLint_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [GlobalTheory.FunObj.inBasis_apply, conj_formula _ β β' x h1 (hu x hx)]
    exact cpt_conj_mem w _ _ _ hP hM hC' _ _
  · rw [← map_inv, GlobalTheory.FunObj.inBasis_apply]
    have e := conj_formula _ β β' x⁻¹ h1 (hu _ (inv_mem hx))
    rw [inv_inv] at e
    rw [e]
    exact cpt_conj_mem w _ _ _ hP hM hC _ _

end GlobalTheory.ConjPlaceUnitary
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryInBasisIntegralAtConjugatePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryInBasis_integral_at_conjugatePlace : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsFrame β Λ → Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ → ∀ x ∈ UA D.sp.cm V.gram, ∀ w : Pl D.host.E, inBasis rfl β w x ∈ GlobalTheory.SplitWeil.KO (Kw w) (Fin V.rank) → inBasis rfl β (Formalism.DivisionValues.conjPl w) x ∈ GlobalTheory.SplitWeil.KO (Kw (Formalism.DivisionValues.conjPl w)) (Fin V.rank) := by
  first | exact @GlobalTheory.ConjPlaceUnitary.inBasis_conjPl_mem_KO | exact GlobalTheory.ConjPlaceUnitary.inBasis_conjPl_mem_KO | (intros; apply GlobalTheory.ConjPlaceUnitary.inBasis_conjPl_mem_KO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteNodeCartanOrthonormalBasisAllPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteNodeCartanOrthonormalBasisAllPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowReal

section DefOnb

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem gramAt_negSp (V : HSp D) (ρ : D.what₂.Tau) : gramAt D (negSp V) ρ = -gramAt D V ρ := by
  unfold gramAt
  rw [negSp_gram]
  exact Matrix.map_neg _ (map_neg (tauE D ρ)) _

theorem isCartanInv_neg {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : IsCartanInv (-G) (-s) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [neg_mul_neg, h1], ?_, ?_⟩
  · rw [Matrix.conjTranspose_neg, neg_mul_neg, Matrix.mul_neg, h2]
  · rw [neg_mul_neg]; exact h3

theorem defNode_cart_onb {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (X : Node) (hX : DefNode D.R.m X) (ρ : D.what₂.Tau) :
    IsCartanInv (gramAt D (G.V X) ρ) (W.cart X ρ) ∧ IsONBasis (gramAt D (G.V X) ρ) (W.cart X ρ) (W.onb X ρ) (G.V X).rank ∧
    IsCartanInv (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) ∧
      IsONBasis (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) (W.onb X ρ) 0 := by
  have hC := W.cart_is X hX.inRange ρ
  have hP : (W.onb X ρ)ᴴ * gramAt D (G.V X) ρ * W.onb X ρ = 1 := posOnb_of_defNode W μ0 hL hX ρ
  obtain ⟨ε, h1, h2⟩ := W.onb_is X hX.inRange ρ
  have hJ : Formalism.REAL.Jm ε = 1 := h1.symm.trans hP
  rw [hJ, Matrix.mul_one] at h2
  have hn : gramAt D (negSp (G.V X)) ρ = -gramAt D (G.V X) ρ := gramAt_negSp _ _
  refine ⟨hC, ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩, ?_, ⟨fun _ => -1, fun a => Or.inr ⟨rfl, Nat.zero_le _⟩, ?_, ?_⟩⟩
  · rw [hP]; simp [Matrix.diagonal_one]
  · rw [h2]; simp [Matrix.diagonal_one]
  · rw [hn]; exact isCartanInv_neg hC
  · rw [hn, Matrix.mul_neg, Matrix.neg_mul, hP]
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  · rw [Matrix.neg_mul, h2]
    ext i j
    simp [Matrix.mul_diagonal]

theorem defNode_cart_onb_all : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) (X : Node), DefNode D.R.m X → ∀ ρ,
    IsCartanInv (gramAt D (G.V X) ρ) (W.cart X ρ) ∧ IsONBasis (gramAt D (G.V X) ρ) (W.cart X ρ) (W.onb X ρ) (G.V X).rank ∧
    IsCartanInv (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) ∧
      IsONBasis (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) (W.onb X ρ) 0 :=
  fun hL W X hX ρ => defNode_cart_onb hL W X hX ρ

end DefOnb

end GlobalTheory.RowReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteNodeCartanOrthonormalBasisAllPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) (X : Node), DefNode D.R.m X → ∀ ρ,
    IsCartanInv (gramAt D (G.V X) ρ) (W.cart X ρ) ∧ IsONBasis (gramAt D (G.V X) ρ) (W.cart X ρ) (W.onb X ρ) (G.V X).rank ∧
    IsCartanInv (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) ∧
      IsONBasis (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) (W.onb X ρ) 0 := by
  first | exact @GlobalTheory.RowReal.defNode_cart_onb_all | exact GlobalTheory.RowReal.defNode_cart_onb_all | (intros; apply GlobalTheory.RowReal.defNode_cart_onb_all <;> assumption)
end
end
