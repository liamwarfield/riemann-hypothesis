module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiToBesselLocalModel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineContractionSplitPlaceLocalModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosets

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryScalarLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryScalarLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatScal

noncomputable section

open GlobalTheory.LocMod (Place Frame IsOne)
open GlobalTheory.SplitWeil (SB)
open GlobalTheory.SplitFlip (Grid Edge oppositePath gdet)
open GlobalTheory.FlatPlace

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def xiEdge (ξ : kˣ →* ℂˣ) : Edge → kˣ →* ℂˣ
  | .theta _ _ => ξ
  | .ex _ _ => 1

theorem kappa_split (Γ : Grid k) (μ₀ : ℕ → kˣ →* ℂˣ) (ξ : kˣ →* ℂˣ) (h : ∀ j, Γ.mu j = μ₀ j * ξ) (b : Edge) (X : ℕ × ℕ) :
    Γ.kappa b X = ({Γ with mu := μ₀} : Grid k).kappa b X * xiEdge ξ b := by
  cases b with
  | theta i j =>
    show Γ.mu (j + 1) / Γ.eta ^ ((Γ.rank X + 1) % 2) = μ₀ (j + 1) / Γ.eta ^ ((Γ.rank X + 1) % 2) * ξ
    rw [h, mul_div_right_comm]
  | ex i j =>
    show Γ.chi (Γ.m - i) / Γ.eta ^ ((Γ.rank X + 1) % 2) = Γ.chi (Γ.m - i) / Γ.eta ^ ((Γ.rank X + 1) % 2) * 1
    rw [mul_one]

def xiPart (Γ : Grid k) (ξ : kˣ →* ℂˣ) (g : Γ.VertexGroup) : ℂˣ :=
  ((oppositePath Γ.m).map fun b => xiEdge ξ b (gdet (g b.src)) * (xiEdge ξ b (gdet (g b.tgt)))⁻¹).prod

theorem charFactor_split (Γ : Grid k) (μ₀ : ℕ → kˣ →* ℂˣ) (ξ : kˣ →* ℂˣ) (h : ∀ j, Γ.mu j = μ₀ j * ξ)
    (g : Γ.VertexGroup) :
    charFactor Γ g = charFactor ({Γ with mu := μ₀} : Grid k) g * xiPart Γ ξ g := by
  simp only [charFactor, xiPart, kappa_split Γ μ₀ ξ h, ← List.prod_map_mul]
  refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
  simp only [MonoidHom.mul_apply, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

theorem xiPart_mem (Γ : Grid k) (ξ : kˣ →* ℂˣ) (g : Γ.VertexGroup) (H : Subgroup ℂˣ) (hH : ∀ x, ξ x ∈ H) :
    xiPart Γ ξ g ∈ H := by
  refine H.list_prod_mem fun x hx => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
  have e : ∀ u, xiEdge ξ b u ∈ H := fun u => by
    cases b with
    | theta _ _ => exact hH u
    | ex _ _ => exact H.one_mem
  exact H.mul_mem (e _) (H.inv_mem (e _))

theorem prod_edgeFactor (Γ : Grid k) (ε : Γ.VertexGroup) (hε : ∀ X, ε X ∈ GlobalTheory.SplitWeil.KO k _) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one ε)).prod = ((charFactor Γ ε : ℂˣ) : ℂ) := by
  rw [charFactor, ← Units.coeHom_apply, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
  have ha : ∀ X (z : ℂ), GlobalTheory.SplitFlip.apow (gdet (GlobalTheory.SplitFlip.Assignment.one.read (ε X))) z = 1 := fun X z => by
    refine GlobalTheory.SplitFlip.apow_of_valuation_eq_one ?_ z
    rw [show GlobalTheory.SplitFlip.Assignment.one.read (ε X) = GlobalTheory.SplitFlip.invT (ε X) from rfl, GlobalTheory.SplitFlip.gdet_invT,
      Units.val_inv_eq_inv_val, map_inv₀, GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO (hε X), inv_one]
  simp only [Grid.edgeFactor, ha, mul_one, Function.comp, Units.coeHom_apply, Units.val_mul]

theorem charFactor_eq_one (Γ : Grid k) (ε : Γ.VertexGroup) (hε : ∀ X, ε X ∈ GlobalTheory.SplitWeil.KO k _)
    (hrow : ∀ i < Γ.m, ε (i, Γ.m) = 1 ∧ ε (i + 1, Γ.m) = 1)
    (hμ : ∀ j < Γ.m, IsUnram (Γ.mu (j + 1))) (hη : IsUnram Γ.eta) : charFactor Γ ε = 1 := by
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
  simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
  rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · show Γ.kappa _ (i, Γ.m) (gdet (ε (i, Γ.m))) * (Γ.kappa _ (i + 1, Γ.m) (gdet (ε (i + 1, Γ.m))))⁻¹ = 1
    have g1 : ∀ n, gdet (1 : GL (Fin n) k) = 1 := fun _ => map_one _
    rw [(hrow i hi).1, (hrow i hi).2, g1, g1, map_one, map_one, inv_one, mul_one]
  · have hu : ∀ X, Γ.kappa (.theta Γ.m j) X (gdet (ε X)) = 1 := fun X => by
      have hv := GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO (hε X)
      show (Γ.mu (j + 1) / Γ.eta ^ ((Γ.rank X + 1) % 2)) (gdet (ε X)) = 1
      rw [MonoidHom.div_apply, MonoidHom.pow_apply, hμ j hj _ hv, hη _ hv, one_pow, div_one]
    show Γ.kappa _ _ (gdet (ε _)) * (Γ.kappa _ _ (gdet (ε _)))⁻¹ = 1
    rw [hu, hu, inv_one, mul_one]

end Local

section Grid0

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}


variable (G : GridData L sc) in
def grid0 (w : Pl D.host.E) : Grid (Kw w) where
  m := D.R.m
  r := D.R.r
  t := D.R.t
  s := sLen D
  mu j := (muBase L j).loc w
  chi i := (G.ch.chiH i).loc w
  eta := L.C.eta.loc w


open Classical in
def eps0 (G : GridData L sc) (w : Pl D.host.E) : (grid0 G w).VertexGroup :=
  onColumn (G := grid0 G w) fun j => if j ∈ idx D then GlobalTheory.SplitFlip.diagGL fun a =>
    if Odd j ∧ topRank (grid0 G w) j + (D.R.m - 1 - j) / 2 ≤ a.1 then Units.map (Int.castRingHom (Kw w)).toMonoidHom (-1) else 1
    else 1


variable (G : GridData L sc) in
def stair0 (w : Pl D.host.E) : (grid0 G w).VertexGroup :=
  onColumn (G := grid0 G w) fun j => if j + 2 ≤ D.R.m then stair (grid0 G w) (unifAt w) (cosExp G w) j else 1

theorem elt_stair (G : GridData L sc) (t : T) (w : Pl D.host.E)
    (β : Cosets (G := locGrid G t w) one_le_sLen (givenLevel G t w))
    (hβ : ∀ i, β i = DoubleCoset.mk _ _ (stair (locGrid G t w) (unifAt w) (cosExp G w) (i + 1))) :
    (repsAt G t w).elt β = (stair0 G w : (locGrid G t w).VertexGroup) := by
  have hb : β = fun i : Fin _ => DoubleCoset.mk _ _ (stair (locGrid G t w) (unifAt w) (cosExp G w) (i.1 + 1)) := funext hβ
  subst hb
  funext X
  obtain ⟨i, j⟩ := X
  by_cases hi : i = D.R.m
  · subst hi
    have e1 : (stair0 G w : (locGrid G t w).VertexGroup) (D.R.m, j) =
        if j + 2 ≤ D.R.m then stair (locGrid G t w) (unifAt w) (cosExp G w) j else 1 := onColumn_apply (G := grid0 G w) _ j
    rw [e1]
    split_ifs with hj
    · exact through_elt _ hj
    · exact elt_eq_one t w _ (by omega)
  · show onColumn (G := locGrid G t w) _ (i, j) = onColumn (G := grid0 G w) _ (i, j)
    rw [onColumn, onColumn, dite_eq_right (show ¬ (i, j).1 = (locGrid G t w).m from hi),
      dite_eq_right (show ¬ (i, j).1 = (grid0 G w).m from hi)]
    rfl

end Grid0


open Classical in
theorem scal : Big fun ch => ScalP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  refine ⟨fun w => if w ∈ ch.G.pl.W0 then
      ((charFactor (grid0 ch.G w) (eps0 ch.G w) * charFactor (grid0 ch.G w) (stair0 ch.G w) : ℂˣ) : ℂ) else 1,
    fun t w => (xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (epsV ch.G t w) *
      if w ∈ ch.G.pl.W0 then xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (stair0 ch.G w) else 1)⁻¹,
    fun t w => ?_, fun w hw => if_neg hw, fun t w hw β hβ => ?_⟩
  · have hH : ∀ x, (R.toLevCh.xiH t).loc w x ∈ xiVals R.toLevCh t := fun x => Subgroup.subset_closure ⟨w, x, rfl⟩
    refine inv_mem (mul_mem (xiPart_mem _ _ _ _ hH) ?_)
    split_ifs
    · exact xiPart_mem _ _ _ _ hH
    · exact one_mem _
  · have hmu : ∀ j, (locGrid ch.G t w).mu j = (fun j => (muBase R.toLevCh j).loc w) j * (R.toLevCh.xiH t).loc w :=
      fun j => MonoidHom.ext fun _ => rfl
    have hsplit := charFactor_split (locGrid ch.G t w) _ _ hmu
    dsimp only
    unfold zetaLoc
    rw [prod_edgeFactor _ _ (epsV_mem t w)]
    by_cases h0 : w ∈ ch.G.pl.W0
    · have hk : keepAt ch.G w = false := by simp [keepAt, h0]
      rw [hk, if_pos h0, if_pos h0, elt_stair ch.G t w β (hβ h0)]
      have key : charFactor (locGrid ch.G t w) (epsV ch.G t w) * charFactor (locGrid ch.G t w) (stair0 ch.G w) =
          (charFactor (grid0 ch.G w) (eps0 ch.G w) * charFactor (grid0 ch.G w) (stair0 ch.G w)) *
          ((xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (epsV ch.G t w) *
            xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (stair0 ch.G w))⁻¹)⁻¹ := by
        rw [inv_inv, hsplit (epsV ch.G t w), hsplit (stair0 ch.G w)]
        exact mul_mul_mul_comm _ _ _ _
      simp only [Bool.false_eq_true, if_false]
      rw [← Units.val_inv_eq_inv_val, ← Units.val_mul, ← Units.val_mul]
      exact congrArg Units.val key
    · have hk : keepAt ch.G w = true := by simp [keepAt, h0]
      rw [hk, if_neg h0, if_neg h0, if_pos rfl]
      have ha : w.under (𝓞 D.host.F) ∉ ch.G.pl.S0 := by
        rcases GlobalTheory.FunObj.Good.locPl_cases hw with ⟨a, b⟩ | ⟨a, -, -⟩
        · exact absurd (by rw [b]; exact Finset.mem_image_of_mem ch.G.pl.w a) h0
        · exact a
      have hoff : ∀ i j, i ≠ D.R.m → epsV ch.G t w (i, j) = 1 := fun i j hi => by
        show onColumn (G := locGrid ch.G t w) _ (i, j) = 1
        rw [onColumn, dite_eq_right (show ¬ (i, j).1 = (locGrid ch.G t w).m from hi)]
      have h1 : charFactor ({locGrid ch.G t w with mu := fun j => (muBase R.toLevCh j).loc w} : Grid (Kw w))
          (epsV ch.G t w) = 1 := by
        refine charFactor_eq_one _ _ (epsV_mem t w) (fun i hi => ⟨hoff i _ (Nat.ne_of_lt hi), ?_⟩) (fun j hj => ?_) ?_
        · by_cases e : i + 1 = D.R.m
          · show epsV ch.G t w (i + 1, D.R.m) = 1
            rw [show (i + 1, D.R.m) = (D.R.m, D.R.m) by rw [e]]
            exact epsV_eq_one t w (by omega)
          · exact hoff _ _ e
        · replace hj : j < D.R.m := hj
          show IsUnram ((muBase R.toLevCh (j + 1)).loc w)
          rw [muBase, dite_eq_left hj]
          refine GlobalTheory.FunObj.Good.isUnram_loc.2 ((R.toLevCh.C.isMu0 ⟨j, hj⟩).unr w fun k hk => ?_)
          refine ha (ch.G.pl.mem_S0_of_sum_eq.2 (Or.inr ((GlobalTheory.ChiGrid.S1_mem_OmF D).2 ?_)))
          have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
            show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
            rw [map_natCast]; exact hk
          fin_cases k
          · exact Or.inl this
          · exact Or.inr (Or.inl this)
        · exact GlobalTheory.FunObj.Good.isUnram_loc.2 (R.toLevCh.C.isEta.unr w)
      simp only [hsplit (epsV ch.G t w), h1, one_mul, mul_one, Units.val_inv_eq_inv_val, inv_inv]

end

end GlobalTheory.FlatScal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryScalarLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatDictionaryScalar_largeDepth : Big fun ch => ScalP ch := by
  first | exact @GlobalTheory.FlatScal.scal | exact GlobalTheory.FlatScal.scal | (intros; apply GlobalTheory.FlatScal.scal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryDoubleStepAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceDoubleStepFlatContractionExpand
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceDoubleStepFlatContractionExpand
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.DblStepLoc

theorem contr_flat_expand : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → GlobalTheory.SplitWeil.HasConductor ψk 1 → ∀ (σ : ℕ) (B : GlobalTheory.Unf.BesLev D (σ + 1)) (J : GlobalTheory.Unf.JacLev D (σ + 1)) (B' : GlobalTheory.Unf.BesLev D σ) (n₀ : Type) [Fintype n₀] [DecidableEq n₀] (n₁ : Type) [Fintype n₁] [DecidableEq n₁] (n₂ : Type) [Fintype n₂] [DecidableEq n₂] (c : ℕ) (F : GlobalTheory.LocMod.Dbl p B J B' n₀ n₁ n₂ c) (s₁ : GlobalTheory.Unf.StepBF ψ B J) (s₂ : GlobalTheory.Unf.StepFB ψ J B') (l : GlobalTheory.Unf.Link B B'.L B'.ζ) (vL : GlobalTheory.Unf.VolM D B'.L.rank J.W₀.rank) T₁ T₂, p.IsModel ψ F.G₀ F.G₁ T₁ → p.IsModel ψ F.G₁ F.G₂ T₂ → ∀ Φ₁ Φ₂ O₁ O₂, GlobalTheory.LocMod.IsOne O₁ → GlobalTheory.LocMod.IsOne O₂ → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (Ξ₁ : I → GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k)) (Ξ₂ : I → GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k)) (c₁ : I → WO B.A J.W₀ →₀ ℂ) (c₂ : I → WO J.W₀ B'.A →₀ ℂ), (∀ i ∈ S, p.IsCombAt ψ F.F₀ F.F₁ (c₁ i) (Ξ₁ i).1 ∧ p.IsCombAt ψ F.F₁ F.F₂ (c₂ i) (Ξ₂ i).1) → (∀ q, GlobalTheory.LocFlat.contr ψk ν (GlobalTheory.LocFlat.flCol ψk ν (σ + 1 + 1) Φ₁.1) (GlobalTheory.LocFlat.flRow ψk ν (σ + 1) Φ₂.1) q = ∑ i ∈ S, x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2)) → GlobalTheory.Unf.contr l J.W₀ vL (GlobalTheory.Unf.flatBF s₁ (T₁ Φ₁)) (GlobalTheory.Unf.flatFB s₂ (T₂ Φ₂)) = ∑ i ∈ S, x i • biComb ψ B.A J.W₀ B'.A (c₁ i) (c₂ i) (GlobalTheory.Unf.contr l J.W₀ vL (GlobalTheory.Unf.flatBF s₁ (T₁ O₁)) (GlobalTheory.Unf.flatFB s₂ (T₂ O₂))) := by
  intro D k _ _ _ _ _ _ ν hν p ψ hstd ψk hchar hcond σ B J B' n₀ _ _ n₁ _ _ n₂ _ _ c F s₁ s₂ l vL T₁ T₂ hT₁ hT₂
    Φ₁ Φ₂ O₁ O₂ hO₁ hO₂ I S x Ξ₁ Ξ₂ c₁ c₂ hcomb hcontr
  have hcσ : c = 2 * σ := by have := F.bes.1; omega
  have hBF := GlobalTheory.FlatBFLoc.flatBF_of_laws D (GlobalTheory.Unf.Flat.flatLaw D) (GlobalTheory.FinPl.flatLaws_all D) (GlobalTheory.LocOm.omLoc D)
  have hFB := GlobalTheory.LocMod.flatFB_holds D (GlobalTheory.Unf.Flat.flatLaw D) (GlobalTheory.FinPl.flatLaws_all D) (GlobalTheory.LocOm.omLoc D)
  have hCL := GlobalTheory.ContrLocProof.contrLoc D GlobalTheory.LocFlat.contrFactor
  have hψc : Continuous ψk := hcond.continuous
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.LocMod.GValProof.core_of_bes p B F.s F.F₀ F.G₀ F.bes
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.LocMod.GValProof.core_of_bes p B' (F.s * p.xi) F.F₂ F.G₂ F.bes'
  have hjac : p.IsJacFrame J F.s (-p.xi ^ 2 * p.hz B') F.F₁ F.G₁ := by
    rw [← GlobalTheory.LocMod.GValProof.hz_link p B B' l]; exact F.jac
  obtain ⟨U₁, hU₁, hU₁e⟩ := hBF k p ν hν.1 ψ ψk hchar (σ + 1) B J s₁ F.s F.s_ne _ _ (c + 1 + 1) F.F₀ C₀ F.G₀ F.F₁ F.G₁
    hC₀ F.bes F.jac T₁ hT₁
  obtain ⟨U₂, hU₂, hU₂e⟩ := hFB k p ν hν.1 ψ ψk hchar σ J B' s₂ F.s F.s_ne _ _ (c + 1) F.F₁ F.G₁ F.F₂ C₂ F.G₂
    hjac hC₂ F.bes' T₂ hT₂
  obtain ⟨Λ, hΛ, hΛe⟩ := hCL k p ν hν.1 ψ hstd ψk hchar (σ + 1) σ B B' l J.W₀ vL F.s F.s_ne _ _ _ F.F₀ C₀ F.F₁ F.F₂ C₂
    hC₀ hC₂ U₁ U₂ hU₁ hU₂
  have hfl := GlobalTheory.LocFlat.flat_SB_onto k ψk ν hψc hν.1
  have m₁ := fun Φ : GlobalTheory.SplitWeil.SB _ =>
    ((hfl n₁ n₀ (c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 Φ.1 Φ.2
  have m₂ := fun Φ : GlobalTheory.SplitWeil.SB _ =>
    ((hfl n₂ n₁ (c + 1) (σ + 1) (by omega)).2 (by omega)).1 Φ.1 Φ.2
  let Ψ₁ : GlobalTheory.SplitWeil.SB _ := ⟨_, m₁ Φ₁⟩
  let Ψ₂ : GlobalTheory.SplitWeil.SB _ := ⟨_, m₂ Φ₂⟩
  let P₁ : GlobalTheory.SplitWeil.SB _ := ⟨_, m₁ O₁⟩
  let P₂ : GlobalTheory.SplitWeil.SB _ := ⟨_, m₂ O₂⟩
  rw [hU₁e Φ₁ Ψ₁ rfl, hU₂e Φ₂ Ψ₂ rfl, hU₁e O₁ P₁ rfl, hU₂e O₂ P₂ rfl]
  obtain ⟨Ξ, hΞ, e1⟩ := hΛe Ψ₁ Ψ₂
  obtain ⟨ΞO, hΞO, e2⟩ := hΛe P₁ P₂
  rw [e1, e2]
  have hun := GlobalTheory.LocFlat.flat_contr_intIndicator k ψk ν hcond hν
  let Q₁ : GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let Q₂ : GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  have hP₁ : P₁.1 = Set.indicator {x : Matrix n₁ (n₀ ⊕ Unit) k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer}
      fun _ => 1 := by
    simp only [P₁]
    rw [hO₁, (hun n₁ n₀ n₀ (c + 1 + 1) (σ + 1 + 1)).1, if_neg (by omega)]
  have hP₂ : P₂.1 = Set.indicator {x : Matrix (n₂ ⊕ Unit) n₁ k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer}
      fun _ => 1 := by
    simp only [P₂]
    rw [hO₂, (hun n₂ n₁ n₀ (c + 1) (σ + 1)).2.1 (by omega) (by omega)]
  have hΞO' : ∀ q, ΞO.1 q = Q₁.1 q.1 * Q₂.1 q.2 := by
    intro q
    rw [hΞO, hP₁, hP₂]
    exact (hun n₁ n₀ n₂ 0 0).2.2 q
  let Pr : I → GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k × Matrix n₂ n₁ k) := fun i => GlobalTheory.LocFlat.CFac.prodSB (Ξ₁ i) (Ξ₂ i)
  have hPr : ∀ i q, (Pr i).1 q = (Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2 := fun i q => rfl
  have hΞs : Ξ = ∑ i ∈ S, x i • Pr i := by
    apply Subtype.ext
    funext q
    rw [hΞ]
    refine (hcontr q).trans ?_
    rw [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hPr]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hΞs, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul]
  congr 1
  exact (GlobalTheory.BiComb.comb_bimodel_and_line D k p ψ _ _ _).1 B.A J.W₀ B'.A F.F₀ F.F₁ F.F₂ Λ (c₁ i) (c₂ i) (Ξ₁ i) Q₁ (Ξ₂ i) Q₂
    (Pr i) ΞO hΛ (hcomb i hi).1 (hcomb i hi).2 rfl rfl (hPr i) hΞO'

end GlobalTheory.DblStepLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceDoubleStepFlatContractionExpandStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_doubleStep_flatContraction_expand : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → GlobalTheory.SplitWeil.HasConductor ψk 1 → ∀ (σ : ℕ) (B : GlobalTheory.Unf.BesLev D (σ + 1)) (J : GlobalTheory.Unf.JacLev D (σ + 1)) (B' : GlobalTheory.Unf.BesLev D σ) (n₀ : Type) [Fintype n₀] [DecidableEq n₀] (n₁ : Type) [Fintype n₁] [DecidableEq n₁] (n₂ : Type) [Fintype n₂] [DecidableEq n₂] (c : ℕ) (F : GlobalTheory.LocMod.Dbl p B J B' n₀ n₁ n₂ c) (s₁ : GlobalTheory.Unf.StepBF ψ B J) (s₂ : GlobalTheory.Unf.StepFB ψ J B') (l : GlobalTheory.Unf.Link B B'.L B'.ζ) (vL : GlobalTheory.Unf.VolM D B'.L.rank J.W₀.rank) T₁ T₂, p.IsModel ψ F.G₀ F.G₁ T₁ → p.IsModel ψ F.G₁ F.G₂ T₂ → ∀ Φ₁ Φ₂ O₁ O₂, GlobalTheory.LocMod.IsOne O₁ → GlobalTheory.LocMod.IsOne O₂ → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (Ξ₁ : I → GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k)) (Ξ₂ : I → GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k)) (c₁ : I → WO B.A J.W₀ →₀ ℂ) (c₂ : I → WO J.W₀ B'.A →₀ ℂ), (∀ i ∈ S, p.IsCombAt ψ F.F₀ F.F₁ (c₁ i) (Ξ₁ i).1 ∧ p.IsCombAt ψ F.F₁ F.F₂ (c₂ i) (Ξ₂ i).1) → (∀ q, GlobalTheory.LocFlat.contr ψk ν (GlobalTheory.LocFlat.flCol ψk ν (σ + 1 + 1) Φ₁.1) (GlobalTheory.LocFlat.flRow ψk ν (σ + 1) Φ₂.1) q = ∑ i ∈ S, x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2)) → GlobalTheory.Unf.contr l J.W₀ vL (GlobalTheory.Unf.flatBF s₁ (T₁ Φ₁)) (GlobalTheory.Unf.flatFB s₂ (T₂ Φ₂)) = ∑ i ∈ S, x i • biComb ψ B.A J.W₀ B'.A (c₁ i) (c₂ i) (GlobalTheory.Unf.contr l J.W₀ vL (GlobalTheory.Unf.flatBF s₁ (T₁ O₁)) (GlobalTheory.Unf.flatFB s₂ (T₂ O₂))) := by
  first | exact @GlobalTheory.DblStepLoc.contr_flat_expand | exact GlobalTheory.DblStepLoc.contr_flat_expand | (intros; apply GlobalTheory.DblStepLoc.contr_flat_expand <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryDoubleStepAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace

theorem dblP_big : Big fun ch => ChrP ch → ArrP ch → LocP ch → BesP ch → JacP ch → DblP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro hChr hArr hLoc hBes hJac
  intro t w hw p hp β r r₀ h hpts M hM φ v f hvf j hje hj
  have hstd : IsStdChar D ch.W.ψ (-1) := by rw [hch.weil.ψ]; exact s.std
  obtain ⟨hψ, hcond, -⟩ := hChr t w hw p hp
  have hm := D.R.m_even
  have hj' : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m := by
    obtain ⟨a, ha⟩ := hm; obtain ⟨b, hb⟩ := hje; omega
  have hj2 : j + 1 + 1 + 2 * ((D.R.m - 4 - j) / 2) + 2 = D.R.m := by omega
  have h0 : ¬ j + 2 * 0 + 2 = D.R.m := by omega
  have hL := hLoc t w hw p hp β r r₀ h hpts
  have t0 : topRank (locGrid ch.G t w) j + D.R.m = (locGrid ch.G t w).rank (D.R.m, j) + j + 1 :=
    topRank_add (G := locGrid ch.G t w) one_le_sLen j
  have t1 : topRank (locGrid ch.G t w) (j + 1) + D.R.m = (locGrid ch.G t w).rank (D.R.m, j + 1) + (j + 1) + 1 :=
    topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1)
  have t2 : topRank (locGrid ch.G t w) (j + 1 + 1) + D.R.m = (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) + (j + 1 + 1) + 1 :=
    topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1 + 1)
  have hc0 : topRank (locGrid ch.G t w) j + (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, j) := by
    omega
  have hc1 : topRank (locGrid ch.G t w) (j + 1) + (2 * ((D.R.m - 4 - j) / 2) + 1 + 1) =
      (locGrid ch.G t w).rank (D.R.m, j + 1) := by
    omega
  have hc2 : topRank (locGrid ch.G t w) (j + 1 + 1) + (2 * ((D.R.m - 4 - j) / 2) + 1) =
      (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) := by
    omega
  have hodd : Odd (j + 1) := hje.add_one
  have hev2 : Even (j + 1 + 1) := hodd.add_one

  obtain ⟨T₁, hT₁, hO₁, Φ₁, hΦ₁, hTΦ₁⟩ := hArr t w hw p hp φ j (by omega) (v ⟨j, by omega⟩) (f ⟨j, by omega⟩)
    (hvf ⟨j, by omega⟩) (epsV ch.G t w) ((repsAt ch.G t w).elt β) (fun X => epsV_mem (G := ch.G) t w X)
    (h j * r₀ j) ((r₀ j)⁻¹ * r j) (h (j + 1) * r₀ (j + 1)) ((r₀ (j + 1))⁻¹ * r (j + 1))
    (hL j (by omega)).1 (hL (j + 1) (by omega)).1
    (Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1))
    (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1)) (frame hc0) (frame hc1)
  obtain ⟨T₂, hT₂, hO₂, Φ₂, hΦ₂, hTΦ₂⟩ := hArr t w hw p hp φ (j + 1) (by omega) (v ⟨j + 1, by omega⟩) (f ⟨j + 1, by omega⟩)
    (hvf ⟨j + 1, by omega⟩) (epsV ch.G t w) ((repsAt ch.G t w).elt β) (fun X => epsV_mem (G := ch.G) t w X)
    (h (j + 1) * r₀ (j + 1)) ((r₀ (j + 1))⁻¹ * r (j + 1)) (h (j + 1 + 1) * r₀ (j + 1 + 1))
    ((r₀ (j + 1 + 1))⁻¹ * r (j + 1 + 1))
    (hL (j + 1) (by omega)).1 (hL (j + 1 + 1) (by omega)).1
    (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
    (Fin (topRank (locGrid ch.G t w) (j + 1 + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1)) (frame hc1) (frame hc2)

  have hB0 := hBes t w hw p hp M hM j ((D.R.m - 4 - j) / 2 + 1) hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    (h j * r₀ j) ((hL j (by omega)).2.1 hje) _ hc0
  have hJ1 := hJac t w hw p hp M hM j ((D.R.m - 4 - j) / 2 + 1) hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    (h (j + 1) * r₀ (j + 1)) (Or.inr ((hL (j + 1) (by omega)).2.2 hodd)) _ hc1
  have hB2 := hBes t w hw p hp M hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) hj2 (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    (h (j + 1 + 1) * r₀ (j + 1 + 1)) ((hL (j + 1 + 1) (by omega)).2.1 hev2) _ hc2
  intro I S x Ξ₁ Ξ₂ c₁ c₂ hc
  have hxi := Witness.xi_ne p
  have es : (p.xi ^ ((D.R.m - 4 - j) / 2 + 1))⁻¹ * p.xi = (p.xi ^ ((D.R.m - 4 - j) / 2))⁻¹ := by
    rw [pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ hxi, mul_one]
  let Fd : GlobalTheory.LocMod.Dbl p (besAt ch.G hM j ((D.R.m - 4 - j) / 2 + 1) hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) hj2 (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (Fin (topRank (locGrid ch.G t w) j)) (Fin (topRank (locGrid ch.G t w) (j + 1)))
      (Fin (topRank (locGrid ch.G t w) (j + 1 + 1))) (2 * ((D.R.m - 4 - j) / 2)) :=
    ⟨_, inv_ne_zero (pow_ne_zero _ hxi), _, _, _, _, _, _, hB0, hJ1, es ▸ hB2⟩

  obtain ⟨O₁, hOne₁, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Kw w)
    (Y := Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
    (Y' := Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1))
  obtain ⟨O₂, hOne₂, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Kw w)
    (Y := Fin (topRank (locGrid ch.G t w) (j + 1 + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1))
    (Y' := Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
  have hv1 : ch.W.om (.mu t D.R.m j) ((h * r₀) j, (h * r₀) (j + 1)) (v ⟨j, by omega⟩) = T₁ O₁ := (hO₁ O₁ hOne₁).symm
  have hv2 : ch.W.om (.mu t D.R.m (j + 1)) ((h * r₀) (j + 1), (h * r₀) (j + 1 + 1)) (v ⟨j + 1, by omega⟩) = T₂ O₂ :=
    (hO₂ O₂ hOne₂).symm
  have hf1 : ch.W.om (.mu t D.R.m j) ((h * r) j, (h * r) (j + 1)) (f ⟨j, by omega⟩) = T₁ Φ₁ := by
    rw [hTΦ₁]; simp only [Pi.mul_apply, mul_assoc, mul_inv_cancel_left]
  have hf2 : ch.W.om (.mu t D.R.m (j + 1)) ((h * r) (j + 1), (h * r) (j + 1 + 1)) (f ⟨j + 1, by omega⟩) = T₂ Φ₂ := by
    rw [hTΦ₂]; simp only [Pi.mul_apply, mul_assoc, mul_inv_cancel_left]
  have E : ∀ (Φ : SchDown ch.G t) (g : Pts ch.G), conAt ch.W hM Φ g j =
      GlobalTheory.Unf.contr (linkAt hM j _ hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
        (ch.G.V (.top (j + 1))) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
        (GlobalTheory.Unf.flatBF (B := besAt ch.G hM j _ hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
          (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
          (stepAt ch.G ch.W t hM j (by omega) (besDecAt ch.G j _ hj')
            (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega)))
          (ch.W.om (.mu t D.R.m j) (g j, g (j + 1)) (Φ ⟨j, by omega⟩)))
        (GlobalTheory.Unf.flatFB (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
          (B := besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
          (stepAt ch.G ch.W t hM (j + 1) (by omega) (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega))
            (besDecAt ch.G (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega)))
          (ch.W.om (.mu t D.R.m (j + 1)) (g (j + 1), g (j + 1 + 1)) (Φ ⟨j + 1, by omega⟩))) := by
    intro Φ g
    unfold conAt
    rw [dite_eq_right h0]
    exact dif_pos hj'
  rw [E v (h * r₀), E f (h * r)]
  rw [hv1, hv2, hf1, hf2]
  have hz : ∀ (S' : Finset I), (∀ q₁ q₂, ∑ i ∈ S', x i * ((Ξ₁ i).1 q₁ * (Ξ₂ i).1 q₂) = 0) → ∀ q,
      GlobalTheory.LocFlat.contr (psiAt ch.W w) (unitVol w) (GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1 + 1)
        (0 : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
          (Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1)) (Kw w))).1)
        (GlobalTheory.LocFlat.flRow (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1) Φ₂.1) q =
        ∑ i ∈ S', x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2) := by
    intro S' hS' q
    rw [hS' q.1 q.2]
    simp [GlobalTheory.LocFlat.contr, GlobalTheory.LocFlat.flCol, GlobalTheory.RootEx.opE, GlobalTheory.StepData.hat]
  refine ⟨fun hvan => ?_, fun hq => ?_⟩
  · refine Eq.trans (GlobalTheory.T.splitPlace_doubleStep_flatContraction_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ hstd (psiAt ch.W w) hψ hcond
      ((D.R.m - 4 - j) / 2) _ _ _ _ _ _ _ Fd _ _ _ _ T₁ T₂ hT₁ hT₂ 0 Φ₂ O₁ O₂ hOne₁ hOne₂ I S x Ξ₁ Ξ₂ c₁ c₂ hc (hz S hvan)).symm ?_
    exact (GlobalTheory.T.splitPlace_doubleStep_flatContraction_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ hstd (psiAt ch.W w) hψ hcond ((D.R.m - 4 - j) / 2)
      _ _ _ _ _ _ _ Fd _ _ _ _ T₁ T₂ hT₁ hT₂ 0 Φ₂ O₁ O₂ hOne₁ hOne₂ I ∅ x Ξ₁ Ξ₂ c₁ c₂ (by simp)
      (hz ∅ fun _ _ => Finset.sum_empty)).trans Finset.sum_empty
  · have hloc : ∀ q, GlobalTheory.LocFlat.contr (psiAt ch.W w) (unitVol w)
        (GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1 + 1) Φ₁.1)
        (GlobalTheory.LocFlat.flRow (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1) Φ₂.1) q =
        ∑ i ∈ S, x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2) := by
      intro q
      rw [← hq q, show Φ₁.1 = _ from funext hΦ₁, show Φ₂.1 = _ from funext hΦ₂]
      unfold facAt locA
      rw [dite_eq_right (show ¬ j + 2 * 0 + 2 = (locGrid ch.G t w).m from h0),
        dif_pos (show j + 2 * (((locGrid ch.G t w).m - 4 - j) / 2 + 1) + 2 = (locGrid ch.G t w).m from hj')]
      rfl
    exact GlobalTheory.T.splitPlace_doubleStep_flatContraction_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ hstd (psiAt ch.W w) hψ hcond ((D.R.m - 4 - j) / 2)
      _ _ _ _ _ _ _ Fd _ _ _ _ T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ O₁ O₂ hOne₁ hOne₂ I S x Ξ₁ Ξ₂ c₁ c₂ hc hloc

end GlobalTheory.FlatPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryDoubleStepAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatDictionary_doubleStep_at_place : Big fun ch => ChrP ch → ArrP ch → LocP ch → BesP ch → JacP ch → DblP ch := by
  first | exact @GlobalTheory.FlatPlace.dblP_big | exact GlobalTheory.FlatPlace.dblP_big | (intros; apply GlobalTheory.FlatPlace.dblP_big <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFiniteDatumLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFiniteDatumLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ProdDatum

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

section Gen

variable {D : D7} {S T : HSp D}

def tens (a b : AE D) (Φ Ψ : WO S T → ℂ) : WO S T → ℂ :=
  fun y => if IsHalf (a + b) y then Φ (a • y) * Ψ (b • y) else 0

theorem half_iff {a : AE D} {y : WO S T} : IsHalf a y ↔ a • y = y :=
  ⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩

theorem tens_comm (a b : AE D) (Φ Ψ : WO S T → ℂ) : tens a b Φ Ψ = tens b a Ψ Φ := by
  funext y
  unfold tens
  rw [add_comm b a, mul_comm]

def tensL (a b : AE D) (Φ : WO S T → ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := tens a b Φ
  map_add' Ψ Ψ' := by
    funext y
    simp only [tens, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c Ψ := by
    funext y
    simp only [tens, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem half_add_iff {e : AE D} {u : WO S T} (hu : IsHalf e u) (t : WO S T) : IsHalf e (t + u) ↔ IsHalf e t := by
  rw [half_iff] at hu
  rw [half_iff, half_iff, smul_add, hu, add_left_inj]

theorem aux1 {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (a : R) (k l : ℕ) (u : M) :
    a • ((k * l) • u) = k • (l • (a • u)) := by rw [smul_comm a, mul_smul]

theorem aux2 {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {a : R} (ha : a * a = a) (l : ℕ) (u : M) :
    a • (l • (a • u)) = l • (a • u) := by rw [smul_comm a l, smul_smul a, ha]

theorem aux3 {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {a b : R} (k l : ℕ) {t : M} (h : (a + b) • t = t) :
    (k * l) • t = l • (k • (a • t)) + k • (l • (b • t)) := by
  rw [← mul_smul l k, ← mul_smul k l, mul_comm l k, ← smul_add, ← add_smul, h]

theorem aux4 {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {a : R} (k : ℕ) {t : M} (h : a • t = t) :
    a • (k • t) = k • t := by rw [smul_comm, h]

variable {a b : AE D} {Λ : AddSubgroup (WO S T)}

theorem tens_sb (ha : a * a = a) (hb : b * b = b) (hΛa : ∀ u ∈ Λ, a • u ∈ Λ) (hΛb : ∀ u ∈ Λ, b • u ∈ Λ)
    {Φ Ψ : WO S T → ℂ} (hΦ : IsSBHalf a Λ Φ) (hΨ : IsSBHalf b Λ Ψ) : IsSBHalf (a + b) Λ (tens a b Φ Ψ) := by
  obtain ⟨-, k, hk, h2, h3⟩ := hΦ
  obtain ⟨-, l, hl, g2, g3⟩ := hΨ
  refine ⟨fun t ht => ?_, k * l, Nat.mul_pos hk hl, fun u hu hh t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (if_neg h)
  · have hh' : IsHalf (a + b) ((k * l) • u) := half_iff.2 (aux4 _ (half_iff.1 hh))
    unfold tens
    by_cases h : IsHalf (a + b) t
    · rw [if_pos h, if_pos ((half_add_iff hh' t).2 h), smul_add, smul_add]
      have e1 : a • ((k * l) • u) = k • (l • (a • u)) := aux1 a k l u
      have e2 : b • ((k * l) • u) = l • (k • (b • u)) := by rw [mul_comm k l]; exact aux1 b l k u
      rw [e1, e2, h2 _ (nsmul_mem (hΛa u hu) l) (half_iff.2 (aux2 ha l u)),
        g2 _ (nsmul_mem (hΛb u hu) k) (half_iff.2 (aux2 hb k u))]
    · rw [if_neg h, if_neg fun h' => h ((half_add_iff hh' t).1 h')]
  · unfold tens at ht
    by_cases h : IsHalf (a + b) t
    · rw [if_pos h] at ht
      have e : (k * l) • t = l • (k • (a • t)) + k • (l • (b • t)) := aux3 k l (half_iff.1 h)
      rw [e]
      exact add_mem (nsmul_mem (h3 _ (left_ne_zero_of_mul ht)) l) (nsmul_mem (g3 _ (right_ne_zero_of_mul ht)) k)
    · exact absurd (if_neg h) ht

theorem tens_ind (ha : a * a = a) (hb : b * b = b) (hΛa : ∀ u ∈ Λ, a • u ∈ Λ) (hΛb : ∀ u ∈ Λ, b • u ∈ Λ) :
    tens a b (halfInd a Λ) (halfInd b Λ) = halfInd (a + b) Λ := by
  funext y
  have h1 : IsHalf a (a • y) := half_iff.2 (by rw [smul_smul, ha])
  have h2 : IsHalf b (b • y) := half_iff.2 (by rw [smul_smul, hb])
  unfold tens halfInd
  by_cases h : IsHalf (a + b) y
  · rw [if_pos h]
    by_cases hy : y ∈ Λ
    · rw [if_pos ⟨hΛa y hy, h1⟩, if_pos ⟨hΛb y hy, h2⟩, if_pos ⟨hy, h⟩, one_mul]
    · rw [if_neg (fun h' : y ∈ Λ ∧ _ => hy h'.1)]
      by_cases hay : a • y ∈ Λ
      · have : b • y ∉ Λ := fun hby => hy (by
          have := add_mem hay hby
          rwa [← add_smul, half_iff.1 h] at this)
        rw [if_neg (fun h' : b • y ∈ Λ ∧ _ => this h'.1), mul_zero]
      · rw [if_neg (fun h' : a • y ∈ Λ ∧ _ => hay h'.1), zero_mul]
  · rw [if_neg h, if_neg (fun h' : y ∈ Λ ∧ _ => h h'.2)]

theorem tens_model (ψ : AddChar (AF D.host.F) ℂ) (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0)
    (hΛa : ∀ u ∈ Λ, a • u ∈ Λ) (hΛb : ∀ u ∈ Λ, b • u ∈ Λ) {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ Tm) {Φ : WO S T → ℂ} (hΦ : IsSBHalf a Λ Φ) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) b Λ 1 (Tm (tens a b Φ (halfInd b Λ))) (Tm ∘ₗ tensL a b Φ) := by
  refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, by rw [one_smul]; rfl⟩
  · have hx1 : b • x = x := half_iff.1 hx
    have hx0 : a • x = 0 := by rw [← hx1, smul_smul, hab, zero_smul]
    have hx2 : IsHalf (a + b) x := half_iff.2 (by rw [add_smul, hx0, hx1, zero_add])
    have e : tens a b Φ (fun t => Ψ (t + x)) = fun t => tens a b Φ Ψ (t + x) := by
      funext t
      simp only [tens, half_add_iff hx2 t, smul_add, hx0, hx1, add_zero]
    change Tm (tens a b Φ (fun t => Ψ (t + x))) = heisO ψ S T x (Tm (tens a b Φ Ψ))
    rw [e]
    exact hT.trans _ (tens_sb ha hb hΛa hΛb hΦ hΨ) x hx2
  · have hy1 : cA D b • y = y := half_iff.1 hy
    have hy2 : IsHalf (cA D (a + b)) y := half_iff.2 (by
      rw [RingHom.map_add (f := _), add_smul, hy1, ← hy1, smul_smul, ← RingHom.map_mul, hab, RingHom.map_zero, zero_smul, zero_add])
    have e : tens a b Φ (fun t => ψ (symplO S T t y) * Ψ t) = fun t => ψ (symplO S T t y) * tens a b Φ Ψ t := by
      funext t
      simp only [tens]
      rw [symplO_smul, hy1]
      split_ifs <;> ring
    change Tm (tens a b Φ (fun t => ψ (symplO S T t y) * Ψ t)) = heisO ψ S T y (Tm (tens a b Φ Ψ))
    rw [e]
    exact hT.modul _ (tens_sb ha hb hΛa hΛb hΦ hΨ) y hy2

end Gen

theorem orth_of_idemSum {D : D7} {a b : AE D} {P Q R : Finset (Pl D.host.E)} (ha : IsIdemSum a P) (hb : IsIdemSum b Q)
    (h : IsIdemSum (a + b) R) : a * b = 0 ∧ (a + cA D a) * (b + cA D b) = 0 := by
  have a2 := idemSum_mul_self ha
  have b2 := idemSum_mul_self hb
  have s2 := idemSum_mul_self h
  have hab : a * b = 0 := by
    have h2 : incA D 2⁻¹ * (1 + 1) = 1 := by
      rw [← (incA D).map_one, ← RingHom.map_add (f := _), ← RingHom.map_mul]
      congr 1
      norm_num
    linear_combination incA D 2⁻¹ * (s2 - a2 - b2) - a * b * h2
  have h1 := h.2
  rw [RingHom.map_add (f := _)] at h1
  have ha' := ha.2
  have hb' := hb.2
  have k1 : a * cA D b = 0 := by
    linear_combination a * h1 - (cA D a + cA D b) * a2 - ha' - (cA D a + cA D b) * hab
  have k2 : b * cA D a = 0 := by
    linear_combination h1 - ha' - hb' - k1
  have k3 : cA D a * cA D b = 0 := by rw [← RingHom.map_mul, hab, RingHom.map_zero]
  exact ⟨hab, by linear_combination hab + k1 + k2 + k3⟩

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {t : T}


set_option maxHeartbeats 1000000 in
theorem exists_prod {p : Pair T} (hS : IsSelfDualC (G.pS p) (G.latS p)) (hT : IsSelfDualC (G.pT p) (G.latT p))
    (d₁ d₂ : FinDatum G t p) (c₁ c₂ : WO (G.pS p) (G.pT p) →₀ ℂ) (he : IsIdemSum (d₁.e + d₂.e) (d₁.P ∪ d₂.P))
    (h₁ : IsCombOf W d₁ c₁) (h₂ : IsCombOf W d₂ c₂) :
    ∃ (d : FinDatum G t p) (c : WO (G.pS p) (G.pT p) →₀ ℂ), d.P = d₁.P ∪ d₂.P ∧ d.e = d₁.e + d₂.e ∧ IsCombOf W d c ∧
      (∀ y, IsHalf d.e y → d.fn y = d₁.fn (d₁.e • y) * d₂.fn (d₂.e • y)) ∧
      ∀ f, comb W.ψ _ _ c f = comb W.ψ _ _ c₁ (comb W.ψ _ _ c₂ f) := by
  have a2 := idemSum_mul_self d₁.e_is
  have b2 := idemSum_mul_self d₂.e_is
  obtain ⟨hab, horth⟩ := orth_of_idemSum d₁.e_is d₂.e_is he
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True,
      a • u ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True := fun a ha u hu =>
    GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu
  have HC := GlobalTheory.HeisComb.main D W.ψ (G.pS p) (G.pT p)
  obtain ⟨c, hsupp, hc⟩ := HC.1 c₁ c₂
  let d : FinDatum G t p :=
    { P := d₁.P ∪ d₂.P
      P_over := fun w hw => (Finset.mem_union.1 hw).elim (d₁.P_over w) (d₂.P_over w)
      e := d₁.e + d₂.e
      e_is := he
      fn := tens d₁.e d₂.e d₁.fn d₂.fn
      sb := tens_sb a2 b2 (hsm _ a2) (hsm _ b2) d₁.sb d₂.sb
      z := 1
      z_cen := (FinDatum.vacuum G t p).z_cen
      z_supp := (FinDatum.vacuum G t p).z_supp }
  refine ⟨d, c, rfl, rfl, ⟨fun u hu => ?_, fun u hu => ?_, fun f₀ hth hvac => ⟨?_, fun Tm hTm => ?_⟩⟩,
    fun y hy => if_pos hy, hc⟩
  · obtain ⟨x, hx, y, hy, rfl⟩ := hsupp u hu
    rw [Matrix.map_add _ (fun a b => RingHom.map_add _ a b), h₁.1 x hx, h₂.1 y hy, add_zero]
  · obtain ⟨x, hx, y, hy, rfl⟩ := hsupp u hu
    intro i j
    have k1 := h₁.2.1 x hx i j
    have k2 := h₂.2.1 y hy i j
    change (d₁.e + d₂.e + cA D (d₁.e + d₂.e)) * (x i j + y i j) = x i j + y i j
    rw [RingHom.map_add (f := _)]
    linear_combination (1 - d₂.e - cA D d₂.e) * k1 + (1 - d₁.e - cA D d₁.e) * k2 + (x i j + y i j) * horth
  · exact (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _ hS hT d.P d.e d.e_is f₀ hth hvac).1
  · obtain ⟨c', k1, k2⟩ := GlobalTheory.CombsExist.exists_comb_model W.ψ _ _ _ _ d₂.e d₂.fn W.ψ_std hS hT b2 d₂.e_is.2
      (infPart_idemSum d₂.e_is) d₂.sb
    have hT1 : IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) (d₁.e + d₂.e)
      (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) 1 f₀ Tm := hTm
    have hT2 := hT1
    rw [add_comm] at hT2
    have v := hT1.vac
    rw [one_smul] at v
    have m2 := tens_model W.ψ a2 b2 hab (hsm _ a2) (hsm _ b2) hT1 (GlobalTheory.isSBHalf_halfInd d₁.e _)
    rw [tens_ind a2 b2 (hsm _ a2) (hsm _ b2), v] at m2
    have m1 := tens_model W.ψ b2 a2 (by rw [mul_comm, hab]) (hsm _ b2) (hsm _ a2) hT2 (GlobalTheory.isSBHalf_halfInd d₂.e _)
    rw [tens_ind b2 a2 (hsm _ b2) (hsm _ a2), add_comm, v] at m1
    have m3 := tens_model W.ψ a2 b2 hab (hsm _ a2) (hsm _ b2) hT1 d₁.sb
    have e2 : comb W.ψ _ _ c₂ f₀ = comb W.ψ _ _ c' f₀ := ((h₂.2.2 f₀ hth hvac).2 _ m2).trans (k2 f₀ _ m2).symm
    have e1 := (h₁.2.2 f₀ hth hvac).2 _ m1
    have e3 := k2 _ _ m3
    have hcomm := HC.2.1 c₁ c' (fun x hx y hy => HC.2.2.2 _ _ x y
      (by rw [RingHom.map_add (f := _), Formalism.L2.Theta.cA_cA, add_comm]) horth (h₁.2.1 x hx) (k1 y hy).2) f₀
    rw [hc, e2, hcomm, e1]
    refine Eq.trans ?_ e3
    congr 1
    exact congrArg Tm (tens_comm _ _ _ _)

theorem prod_datum : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (j : Fin D.R.m) (d₁ d₂ : FinDatum ch.G t (.top t j)) (c₁ c₂ : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), IsIdemSum (d₁.e + d₂.e) (d₁.P ∪ d₂.P) → IsCombOf ch.W d₁ c₁ → IsCombOf ch.W d₂ c₂ → ∃ (d : FinDatum ch.G t (.top t j)) (c : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), d.P = d₁.P ∪ d₂.P ∧ d.e = d₁.e + d₂.e ∧ IsCombOf ch.W d c ∧ (∀ y, IsHalf d.e y → d.fn y = d₁.fn (d₁.e • y) * d₂.fn (d₂.e • y)) ∧ ∀ f, comb ch.W.ψ _ _ c f = comb ch.W.ψ _ _ c₁ (comb ch.W.ψ _ _ c₂ f) :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ t j d₁ d₂ c₁ c₂ =>
    exists_prod ch.W (p := .top t j) (ch.G.isV (X := .top j) j.2.le fun _ h => by cases h).sd
      (ch.G.isV (X := .top (j + 1)) j.2 fun _ h => by cases h).sd d₁ d₂ c₁ c₂⟩⟩

end GlobalTheory.ProdDatum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFiniteDatumLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productFiniteDatum_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (j : Fin D.R.m) (d₁ d₂ : FinDatum ch.G t (.top t j)) (c₁ c₂ : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), IsIdemSum (d₁.e + d₂.e) (d₁.P ∪ d₂.P) → IsCombOf ch.W d₁ c₁ → IsCombOf ch.W d₂ c₂ → ∃ (d : FinDatum ch.G t (.top t j)) (c : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), d.P = d₁.P ∪ d₂.P ∧ d.e = d₁.e + d₂.e ∧ IsCombOf ch.W d c ∧ (∀ y, IsHalf d.e y → d.fn y = d₁.fn (d₁.e • y) * d₂.fn (d₂.e • y)) ∧ ∀ f, comb ch.W.ψ _ _ c f = comb ch.W.ψ _ _ c₁ (comb ch.W.ψ _ _ c₂ f) := by
  first | exact @GlobalTheory.ProdDatum.prod_datum | exact GlobalTheory.ProdDatum.prod_datum | (intros; apply GlobalTheory.ProdDatum.prod_datum <;> assumption)
end
end
