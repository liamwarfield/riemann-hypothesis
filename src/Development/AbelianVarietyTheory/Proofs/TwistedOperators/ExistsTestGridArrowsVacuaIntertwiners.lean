module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNonzeroRealIntertwinerGridArrow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColIntertwiner
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDownArrowRealIntertwinerWithAdjoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGridCosetDataEqWeilCosetVectors

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainIntertwinersRowZeroUnitVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin.RowArrows

theorem vY_mem_span_core {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (h : GlobalTheory.Hk3.Core R F) (t : T) {k : ℕ} (hk : k + 1 < D.R.m) : R.vY t k ∈ Submodule.span ℂ (Set.range
    fun a : {a : WO (Yc D k) (Yc D (k + 1)) // a.map (infPart D) = 0} => heisO R.ψ _ _ a (R.vac k)) :=
  GlobalTheory.Grid.stepVec_mem_span (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ (by omega)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ hk)) (h.chain.vY t k hk)

theorem vX_mem_span_core {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (h : GlobalTheory.Hk3.Core R F) (t : T) : R.vX t ∈ Submodule.span ℂ (Set.range
    fun a : {a : WO (Yc D (D.R.m - 1)) D.sp.X' // a.map (infPart D) = 0} => heisO R.ψ _ _ a R.vacX) :=
  GlobalTheory.Grid.stepVec_mem_span (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ (by have := D.R.two_le_m; omega)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ h.lev.βX) (h.chain.vX t)

theorem chainIntertwiners_rowZero_unitVacua : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → IsItW R.θ (GlobalTheory.Grid.row0 R j).M (GlobalTheory.Grid.row0 R (j + 1)).M (GlobalTheory.Grid.th0 R t j).ω (GlobalTheory.Grid.fock R.ψ R.θ false (GlobalTheory.Grid.row0 R j) (GlobalTheory.Grid.row0 R (j + 1)) (GlobalTheory.Grid.th0 R t j).vac) (GlobalTheory.Grid.th0 R t j).It := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F h _ G' W _ G _ _ _ _ t j hj
  unfold GlobalTheory.Grid.th0
  by_cases h1 : j + 1 < D.R.m
  · rw [dite_eq_left h1]
    have hc := (GlobalTheory.Grid.ArrS.is_cast (ψ := R.ψ) (θ := R.θ) (ε := false) (a := GlobalTheory.Grid.stepY R t j)
      (χS := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 j))
      (χT := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 (j + 1))) (GlobalTheory.Grid.nodeY_eq_chainVertexAtRowZero_of_lt R (by omega)) (GlobalTheory.Grid.nodeY_eq_chainVertexAtRowZero_of_lt R h1))
    have hω := h.chain.ωY t j h1
    rw [GlobalTheory.Grid.chrStep_eq_muAt] at hω
    exact (hc.2 ⟨hω, (h.chain.vY t j h1).1,
      GlobalTheory.Grid.isItW_of_mem_span hω h.models.inf (h.chain.vY t j h1).1.2.theta (vY_mem_span_core h t h1) (h.chain.ItY t j h1)⟩).intw
  · have h2 : j + 1 = D.R.m := by omega
    rw [dite_eq_right h1, dite_eq_left h2]
    have hc := (GlobalTheory.Grid.ArrS.is_cast (ψ := R.ψ) (θ := R.θ) (ε := false) (a := GlobalTheory.Grid.stepX R t)
      (χS := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 j))
      (χT := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 (j + 1))) (GlobalTheory.Grid.nodeY_pred_eq_chainVertexAtRowZero_last R h2) (GlobalTheory.Grid.nodeX_eq_chainVertexAtRowZero_of_ge R h1))
    have hω := h.chain.ωX t
    rw [(congrArg _ h2.symm).trans (GlobalTheory.Grid.chrStep_eq_muAt R t j)] at hω
    exact (hc.2 ⟨hω, (h.chain.vX t).1,
      GlobalTheory.Grid.isItW_of_mem_span hω h.models.inf (h.chain.vX t).1.2.theta (vX_mem_span_core h t) (h.chain.ItX t)⟩).intw

end GlobalTheory.GridJoin.RowArrows

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowArrowExistsCommonRealIntertwiner
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowArrowExistsCommonRealIntertwiner
noncomputable section

section Gen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix
open GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowThetaIt

theorem itPair_of_par (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules) {D : D7} {V W : HSp D}
    {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') {θ : InfFam D} (hθ : IsInfFam θ)
    (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ)
    (hP : ∀ τ, ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      S τ = dualPar (signed (al ++ be) (ga ++ de) (aT τ)) ∧
      S' τ = dualPar (signed (al ++ Formalism.BasicNotions.TH.block t ++ de) (ga ++ be) (aS τ))) :
    ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, It ≠ 0 ∧
      ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ),
        GlobalTheory.PairLift.IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It := by
  obtain ⟨X, hX, h1, h2⟩ := GlobalTheory.Chain.ItPairObj.exists_record hD hH
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (aS τ) (aT τ) A := fun τ => by
    obtain ⟨t, al, be, ga, de, hd, e1, e2⟩ := hP τ
    exact exists_locIt hX h1 h2 (GlobalTheory.T.thetaModels_eq_coverDiscreteSeries hD hH D) M M' τ hd e1 e2
  choose hr A hA using key
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' aS aT A GlobalTheory.Contr.contraction.2 (GlobalTheory.T.gluing_law_holds D _ _) hA
  refine ⟨It, hI.ne, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
  have hv := fun τ => GlobalTheory.T.thetaVacuumCharacters_atRealPlaces D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
  exact isItW_of_globIt hθ hI hr (GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1)
    fun τ => (hv τ).2.2

end GlobalTheory.RowThetaIt

end Gen

section Par

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid GlobalTheory.PairLift GlobalTheory.SignedHC GlobalTheory.RemoveBlock
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowThetaIt

theorem dataAR_row (D : D7) (hS : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D) (i j : ℕ) (τ : D.what₂.Tau) (hi : i ≤ D.R.m) (hj : j < D.R.m) :
    ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      parV D i j τ = dualPar (signed (al ++ be) (ga ++ de) (att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i (j + 1)))) ∧
      parV D i (j + 1) τ =
        dualPar (signed (al ++ Formalism.BasicNotions.TH.block t ++ de) (ga ++ be) (att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i j))) := by
  have he : (D.hc τ).e ⟨j, hj⟩ = ((grid D τ).e (j + 1) : ℚ) :=
    (GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D) (cen D τ)).2.2 ⟨j, hj⟩
  set G := grid D τ with hG
  set δ : ℚ := if Odd (i + j) then -(1 / 2) else 0 with hδ
  set δ' : ℚ := if Odd (i + (j + 1)) then -(1 / 2) else 0 with hδ'
  have hT : att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i (j + 1)) = -(G.e (j + 1) : ℚ) + δ := by
    simp only [att, he, hδ]
    by_cases h : Odd (i + j)
    · have h' : Odd (rkV D i (j + 1)) := by rw [odd_rkV, show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h, h', if_true]; ring
    · have h' : ¬ Odd (rkV D i (j + 1)) := by rw [odd_rkV, show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h, h', if_false]; ring
  have hS' : att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i j) = -(G.e (j + 1) : ℚ) + δ' := by
    simp only [att, he, hδ']
    by_cases h : Odd (i + j)
    · have h' : Odd (rkV D i j) ↔ False := by rw [odd_rkV]; tauto
      have h'' : Odd (i + (j + 1)) ↔ False := by rw [show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h', h'', if_false]; ring
    · have h' : Odd (rkV D i j) := by rw [odd_rkV]; tauto
      have h'' : Odd (i + (j + 1)) := by rw [show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h', h'', if_true]; ring
  rw [hT, hS']
  set P := shift δ (G.parD i j) with hP
  have hpart := partner_parD D τ i j hi hj δ δ'
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have hN : 1800 < bigN D := by
    have h1 := hS.1
    have h2 : D.R.m ≤ D.R.m * (D.R.t + sLen D + 1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold bigN; unfold Ranks.r at h1
    omega
  have hgap : GapOver P (2 * (bigN D : ℚ) ^ 3) := GlobalTheory.RemoveBlock.gapOver_shift (gapOver_parD D hS τ i j hi hj.le)
  have hgap' : GapOver (partner D.R.t true (-(G.e (j + 1) : ℚ) + δ) (-(G.e (j + 1) : ℚ) + δ') P)
      (2 * (bigN D : ℚ) ^ 3) := by
    rw [hP, ← hpart]; exact GlobalTheory.RemoveBlock.gapOver_shift (gapOver_parD D hS τ i (j + 1) hi hj)
  have hreg : IsRegular P := isRegular_of_gapOver (by positivity) hgap
  have hfar3 : FarFrom (-(G.e (j + 1) : ℚ) + δ) (((D.R.t : ℚ) + 3) / 2) P := farFrom_shift (farFrom_parD D τ i j hi hj)
  have hfar1 : FarFrom (-(G.e (j + 1) : ℚ) + δ) (((D.R.t : ℚ) + 1) / 2) P := fun x hx =>
    le_trans (by linarith) (hfar3 x hx)
  have hne : P.Nonempty := by
    have hv : ((grid D τ).v 2 : ℚ) ∈ (grid D τ).cloud :=
      GridData.mem_cloud.2 ⟨2, le_rfl, by have := D.R.m_add_three_le_k; show 2 ≤ D.R.k; omega, rfl⟩
    have hmem : (((grid D τ).v 2 : ℚ), true) ∈ (grid D τ).parD i j := GridData.mem_parD.2 (Or.inl ⟨hv, rfl⟩)
    exact ⟨_, mem_shift' hmem⟩
  have hcard : P.card + D.R.t ≤ bigN D := by
    rw [hP, card_shift]
    have h0 : (G.parD i j).card ≤ rkV D i j := card_parD_le D τ i j hi
    have a : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
    have b : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
    have c : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
    have d : (j + 1) * D.R.t = j * D.R.t + D.R.t := by ring
    show _ ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    unfold rkV Ranks.r at h0
    omega
  have hcos : InCoset (-(G.e (j + 1) : ℚ) + δ + ((D.R.t : ℚ) + 1) / 2) (GlobalTheory.SignedHC.entries P) := by
    intro x hx
    obtain ⟨s, hs⟩ := mem_entries.1 hx
    have hy := fst_mem_entries (mem_shift.1 hs)
    obtain ⟨z, hz⟩ := int_parD D τ i j _ hy
    simp only at hz
    obtain ⟨q, hq⟩ := D.R.t_odd
    have htq : ((D.R.t : ℚ) + 1) / 2 = q + 1 := by rw [hq]; push_cast; ring
    refine ⟨z + G.e (j + 1) - (q + 1), ?_⟩
    rw [htq]; push_cast; linarith
  obtain ⟨al, be, ga, de, hPe, hP'⟩ :=
    GlobalTheory.T.isRealThetaParameterPair_thetaPartnerSignedParameter D.R.t true _ _ P (bigN D) ht hne hreg hcos hfar1 hcard hN hgap hgap'
  rcases hP' with ⟨hd, hP'⟩ | ⟨-, hP'⟩
  · refine ⟨D.R.t, al, be, ga, de, hd, ?_, ?_⟩
    · rw [← hPe]; rfl
    · rw [← hP', ← hpart]; rfl
  · exfalso
    set c' : ℚ := -(G.e (j + 1) : ℚ) + δ' with hc'
    have hx0 : ((D.R.t : ℚ) - 1) / 2 ∈ Formalism.BasicNotions.TH.block D.R.t :=
      by simp only [Formalism.BasicNotions.TH.block, List.mem_map, List.mem_range]; simp; exact ⟨0, by omega, by simp⟩
    have m1 : (((D.R.t : ℚ) - 1) / 2 + c', false) ∈ partner D.R.t true (-(G.e (j + 1) : ℚ) + δ) c' P := by
      rw [hP']
      simp only [signed, Finset.mem_union, List.mem_toFinset, List.mem_map]
      exact Or.inr ⟨_, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hx0))), rfl⟩
    have m2 : (((D.R.t : ℚ) - 1) / 2 + c', true) ∈ partner D.R.t true (-(G.e (j + 1) : ℚ) + δ) c' P := by
      simp only [partner, Finset.mem_union, Finset.mem_image]
      refine Or.inr ⟨_, mem_block.2 ⟨0, by omega, by push_cast; ring⟩, rfl⟩
    have := hgap' _ m1 _ m2 (by simp)
    simp only [sub_self, abs_zero] at this
    have : (0 : ℚ) ≤ 2 * (bigN D : ℚ) ^ 3 := by positivity
    linarith

end GlobalTheory.RowThetaIt

end Par

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowThetaIt

theorem rowTheta_it : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i + 1 ≤ D.R.m → j < D.R.m → ∀ (ω : T → GlobalTheory.Grid.WRep (G.nV i j).V (G.nV i (j + 1)).V) (f : WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ), (∀ t, GlobalTheory.Grid.IsWeil R.ψ false (G.nV i j).V (G.nV i (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1))) (ω t)) → GlobalTheory.Grid.IsVac R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f → ∃ It : GlobalTheory.Grid.Pol (G.nV i j) (G.nV i (j + 1)) →ₗ[ℂ] SmT (G.nV i (j + 1)).M →ₗ[ℂ] SmT (G.nV i j).M, ∀ t, IsItW R.θ (G.nV i j).M (G.nV i (j + 1)).M (ω t) (GlobalTheory.Grid.fock R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f) It := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hD hH _ hSz F hc _ G' W _ G hSp _ _ _ i j hi hj ω f hω hf
  have hR : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R := ⟨hc.lev, hc.models.inf, hc.models.νY, hc.models.νY', hc.models.νX⟩
  have hV := hSp.vert i j hi hj.le
  have hV' := hSp.vert i (j + 1) hi hj
  obtain ⟨It, -, hIt⟩ := itPair_of_par hD hH (G.nV i j).M (G.nV i (j + 1)).M hR.inf R.ψ
    (fun τ => GlobalTheory.PairLift.att (-(D.hc τ).e ⟨j, hj⟩) (rkV D (i + 1) j))
    (fun τ => GlobalTheory.PairLift.att (-(D.hc τ).e ⟨j, hj⟩) (rkV D (i + 1) (j + 1)))
    (fun τ => by rw [hV.par, hV'.par]; exact dataAR_row D hSz (i + 1) j τ hi hj)
  refine ⟨It, fun t => hIt (ω t) f ⟨_, _, hω t, fun τ =>
    ⟨GlobalTheory.PairLift.hasInfExp_att (GlobalTheory.PairLift.exp_mu hR t hj τ) (GlobalTheory.PairLift.exp_eta hR τ) _,
      GlobalTheory.PairLift.hasInfExp_att (GlobalTheory.PairLift.exp_mu hR t hj τ) (GlobalTheory.PairLift.exp_eta hR τ) _⟩⟩
    ⟨hf.isFinVec.1, GlobalTheory.PairLift.vac_ne hf, hf.isFinVec.2⟩⟩

end GlobalTheory.RowThetaIt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowArrowExistsCommonRealIntertwinerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridRowArrow_exists_common_realIntertwiner : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i + 1 ≤ D.R.m → j < D.R.m → ∀ (ω : T → GlobalTheory.Grid.WRep (G.nV i j).V (G.nV i (j + 1)).V) (f : WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ), (∀ t, GlobalTheory.Grid.IsWeil R.ψ false (G.nV i j).V (G.nV i (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1))) (ω t)) → GlobalTheory.Grid.IsVac R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f → ∃ It : GlobalTheory.Grid.Pol (G.nV i j) (G.nV i (j + 1)) →ₗ[ℂ] SmT (G.nV i (j + 1)).M →ₗ[ℂ] SmT (G.nV i j).M, ∀ t, IsItW R.θ (G.nV i j).M (G.nV i (j + 1)).M (ω t) (GlobalTheory.Grid.fock R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f) It := by
  first | exact @GlobalTheory.RowThetaIt.rowTheta_it | exact GlobalTheory.RowThetaIt.rowTheta_it | (intros; apply GlobalTheory.RowThetaIt.rowTheta_it <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsVacTrueOfAgree
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}

theorem exists_isVac_true_of_agree {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {N₁ N₀ : GlobalTheory.Grid.Node D} {V₁ V₀ : HSp D}
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin V₁.rank → D.host.E)} {Λ₀ : Submodule (𝓞 D.host.E) (Fin V₀.rank → D.host.E)}
    {c₁ : D.what₂.Tau → Matrix (Fin V₁.rank) (Fin V₁.rank) ℂ} {c₀ : D.what₂.Tau → Matrix (Fin V₀.rank) (Fin V₀.rank) ℂ}
    (h₁ : N₁.V = V₁) (hΛ₁ : HEq N₁.Λ Λ₁) (hc₁ : HEq (Formalism.IndefR.Links.cart N₁.M) c₁)
    (h₀ : N₀.V = V₀) (hΛ₀ : HEq N₀.Λ Λ₀) (hc₀ : HEq (Formalism.IndefR.Links.cart N₀.M) c₀)
    {f : WO (negSp V₁) V₀ → ℂ} (hf : IsVacO ψ θ (negSp V₁) V₀ (fun τ => -c₁ τ) c₀ (Λ₁ : Set _) (Λ₀ : Set _) f) :
    ∃ f' : WO N₁.V N₀.V → ℂ, GlobalTheory.Grid.IsVac ψ θ true N₁ N₀ f' := by
  subst h₁ h₀
  obtain rfl := eq_of_heq hΛ₁
  obtain rfl := eq_of_heq hΛ₀
  obtain rfl := eq_of_heq hc₁
  obtain rfl := eq_of_heq hc₀
  exact ⟨f, hf⟩

end GlobalTheory.GridJoin

theorem GlobalTheory.GridJoin.exists_isVac_down : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∃ f : WO (G.P (i + 1)).V (G.P i).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ true (G.P (i + 1)) (G.P i) f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hsp _ i hi
  obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev (p := .core i) (show (GlobalTheory.ChiGrid.Node.core (i + 1)).InRange D.R.m from (by show i + 1 ≤ D.R.m; omega))
  have a₁ := hsp.core (i + 1) (by omega)
  have a₀ := hsp.core i (by omega)
  unfold GlobalTheory.ChiGrid.GridData.Weil.IsVac at hf
  rw [hW.ψ, hW.θ] at hf
  exact GlobalTheory.GridJoin.exists_isVac_true_of_agree a₁.sp a₁.lat a₁.cart a₀.sp a₀.lat a₀.cart hf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsVacThRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GridJoin

theorem isVacO_transport {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) :
    ∀ (S S' S₀ S₀' : HSp D) (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (a' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ)
      (a₀ : D.what₂.Tau → Matrix (Fin S₀.rank) (Fin S₀.rank) ℂ)
      (a₀' : D.what₂.Tau → Matrix (Fin S₀'.rank) (Fin S₀'.rank) ℂ)
      (Λ : Set (Fin S.rank → D.host.E)) (Λ' : Set (Fin S'.rank → D.host.E))
      (Λ₀ : Set (Fin S₀.rank → D.host.E)) (Λ₀' : Set (Fin S₀'.rank → D.host.E)),
      S = S₀ → S' = S₀' → HEq a a₀ → HEq a' a₀' → HEq Λ Λ₀ → HEq Λ' Λ₀' →
      (∃ f, IsVacO ψ θ S₀ S₀' a₀ a₀' Λ₀ Λ₀' f) → ∃ f, IsVacO ψ θ S S' a a' Λ Λ' f := by
  rintro S S' _ _ a a' a₀ a₀' Λ Λ' Λ₀ Λ₀' rfl rfl h1 h2 h3 h4 h
  cases eq_of_heq h1; cases eq_of_heq h2; cases eq_of_heq h3; cases eq_of_heq h4
  exact h

theorem heq_coe_lat {D : D7} {V V' : HSp D} (h : V = V') {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} (hΛ : HEq Λ Λ') :
    HEq (Λ : Set (Fin V.rank → D.host.E)) (Λ' : Set (Fin V'.rank → D.host.E)) := by
  subst h; cases eq_of_heq hΛ; rfl

theorem exists_isVac_th_rows : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i + 1 ≤ D.R.m → j < D.R.m → ∃ f : WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hS _ i j hi hj
  obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev (p := .mu A.μ0 (i + 1) j) ⟨hi, by omega⟩
  have a := hS.vert (i + 1) j hi hj.le
  have b := hS.vert (i + 1) (j + 1) hi hj
  rw [← hW.ψ, ← hW.θ]
  exact isVacO_transport W.ψ W.θ _ _ _ _ _ _ _ _ _ _ _ _ a.sp b.sp a.cart b.cart
    (heq_coe_lat a.sp a.lat) (heq_coe_lat b.sp b.lat) ⟨f, hf⟩

end GlobalTheory.GridJoin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsVacOfNodeAgree
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem exists_isVac_of_nodeAgree {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}
    {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) {N₁ N₂ : GlobalTheory.Grid.Node D} {X₁ X₂ : GlobalTheory.ChiGrid.Node}
    (h₁ : NodeAgree N₁ W X₁) (h₂ : NodeAgree N₂ W X₂) (f : WO (G'.V X₁) (G'.V X₂) → ℂ)
    (hf : IsVacO W.ψ W.θ (G'.V X₁) (G'.V X₂) (W.cart X₁) (W.cart X₂) (G'.Λ X₁ : Set _) (G'.Λ X₂ : Set _) f) :
    ∃ f' : WO N₁.V N₂.V → ℂ, GlobalTheory.Grid.IsVac W.ψ W.θ false N₁ N₂ f' := by
  obtain ⟨V₁, S₁, M₁, Λ₁, β₁⟩ := N₁
  obtain ⟨V₂, S₂, M₂, Λ₂, β₂⟩ := N₂
  obtain ⟨sp₁, lat₁, cart₁, -⟩ := h₁
  obtain ⟨sp₂, lat₂, cart₂, -⟩ := h₂
  dsimp only at sp₁ sp₂ lat₁ lat₂ cart₁ cart₂
  subst sp₁ sp₂
  cases eq_of_heq lat₁
  cases eq_of_heq lat₂
  refine ⟨f, ?_⟩
  have c₁ := eq_of_heq cart₁
  have c₂ := eq_of_heq cart₂
  unfold GlobalTheory.Grid.IsVac GlobalTheory.Grid.cartS
  simp only [GlobalTheory.Grid.sgnM, cond]
  rw [c₁, c₂]
  exact hf

theorem exists_isVac_col : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ j, j < D.R.m → ∃ f : WO (G.Xp j).V (G.nX j).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ false (G.Xp j) (G.nX j) f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hA _ j hj
  have hp : (GlobalTheory.ChiGrid.Pair.top A.μ0 j).InRange D.R.m := by
    simp only [GlobalTheory.ChiGrid.Pair.InRange, GlobalTheory.ChiGrid.Pair.big, GlobalTheory.ChiGrid.Node.InRange]
    omega
  obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev hp
  obtain ⟨f', hf'⟩ := exists_isVac_of_nodeAgree W (hA.top j hj.le) (hA.top (j + 1) hj) f hf
  rw [hW.ψ, hW.θ] at hf'
  exact ⟨f', hf'⟩

end GlobalTheory.GridJoin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsVacX
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin.VacX

variable {D : D7}

theorem transport (ψ ψ' : AddChar (AF D.host.F) ℂ) (θ θ' : InfFam D) (hψ : ψ' = ψ) (hθ : θ' = θ)
    {S S' T T' : HSp D} (hS : S = S') (hT : T = T')
    {cS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {cS' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ}
    (hcS : HEq cS cS')
    {cT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {cT' : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ}
    (hcT : HEq cT cT')
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)}
    (hΛS : HEq ΛS ΛS')
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {ΛT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}
    (hΛT : HEq ΛT ΛT')
    {f : WO (negSp S') T' → ℂ}
    (h : IsVacO ψ' θ' (negSp S') T' (fun τ => -cS' τ) cT' (ΛS' : Set _) (ΛT' : Set _) f) :
    ∃ f' : WO (GlobalTheory.Grid.sgn true S) T → ℂ,
      IsVacO ψ θ (GlobalTheory.Grid.sgn true S) T (fun τ => GlobalTheory.Grid.sgnM true (cS τ)) cT (ΛS : Set _) (ΛT : Set _) f' ∧ HEq f' f := by
  subst hS hT hψ hθ
  obtain rfl := eq_of_heq hcS
  obtain rfl := eq_of_heq hcT
  obtain rfl := eq_of_heq hΛS
  obtain rfl := eq_of_heq hΛT
  exact ⟨f, h, HEq.rfl⟩

end GlobalTheory.GridJoin.VacX

open GlobalTheory.GridJoin.VacX in
theorem GlobalTheory.GridJoin.exists_vacX : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∃ f : WO (G.V (i + 1) j).V (G.V i j).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f ∧ (j = 0 → HEq f (W.vac i)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hag _ i j hi hj
  have hS := hag.vert (i + 1) j (by omega) hj
  have hT := hag.vert i j (by omega) hj
  have key : ∀ f, W.IsVac (.chi i j) f → ∃ f' : WO (G.V (i + 1) j).V (G.V i j).V → ℂ,
      GlobalTheory.Grid.IsVac R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f' ∧ HEq f' f := fun f hf =>
    transport R.ψ W.ψ R.θ W.θ hW.ψ hW.θ hS.sp hT.sp hS.cart hT.cart hS.lat hT.lat hf
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · obtain ⟨f, h1, h2⟩ := key (W.vac i) (W.vac_is i hi)
    exact ⟨f, h1, fun _ => h2⟩
  · obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev (p := .chi i j) ⟨hi, hj⟩
    obtain ⟨f', h1, -⟩ := key f hf
    exact ⟨f', h1, fun h => by omega⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilRowArrow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JoinArrows

theorem weil_arrow_transport {D : D7} {ψ : AddChar (AF ↥D.host.F) ℂ} {S T S' T' : HSp D}
    (hS : S = S') (hT : T = T') {χS χT χS' χT' : (AE D)ˣ →* Circle} (h1 : χS = χS') (h2 : χT = χT')
    (ω' : GlobalTheory.Grid.WRep S' T') (h : IsWeilDatumO ψ S' T' χS' χT' ω') :
    ∃ ω : GlobalTheory.Grid.WRep S T, GlobalTheory.Grid.IsWeil ψ false S T χS χT ω ∧ HEq ω ω' := by
  cases hS
  cases hT
  cases h1
  cases h2
  refine ⟨ω', ?_, HEq.rfl⟩
  rw [GlobalTheory.Grid.isWeil_false]
  exact h

theorem exists_weil_rowArrow : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) i j, i + 1 ≤ D.R.m → j < D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.nV i j).V (G.nV i (j + 1)).V, GlobalTheory.Grid.IsWeil R.ψ false (G.nV i j).V (G.nV i (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1))) ω ∧ HEq ω (W.om (.mu t (i + 1) j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G hSp _ hAg _ t i j hi hj

  have hw := W.om_is (.mu t (i + 1) j) ⟨hi, hj⟩
  rw [hW.ψ] at hw

  have e1 : (G.nV i j).V = G'.V (.grid (i + 1) j) := (hAg.vert (i + 1) j hi (by omega)).sp
  have e2 : (G.nV i (j + 1)).V = G'.V (.grid (i + 1) (j + 1)) := (hAg.vert (i + 1) (j + 1) hi hj).sp

  have r1 : (G'.V (.grid (i + 1) j)).rank = rkV D (i + 1) j := by
    rw [← e1]; exact (hSp.vert i j hi (by omega)).rank
  have r2 : (G'.V (.grid (i + 1) (j + 1))).rank = rkV D (i + 1) (j + 1) := by
    rw [← e2]; exact (hSp.vert i (j + 1) hi hj).rank

  have c1 : GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j) = G'.chrS (.mu t (i + 1) j) := by
    show _ = Formalism.IndefR.Lift.attChr _ _ (G'.V (.grid (i + 1) j)).rank
    rw [r1]
    rfl
  have c2 : GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1)) = G'.chrT (.mu t (i + 1) j) := by
    show _ = Formalism.IndefR.Lift.attChr _ _ (G'.V (.grid (i + 1) (j + 1))).rank
    rw [r2]
    rfl
  exact weil_arrow_transport e1 e2 c1 c2 (W.om (.mu t (i + 1) j)) hw

end GlobalTheory.JoinArrows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWrepOfEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem exists_wrep_of_eq {D : D7} {S T S' T' : HSp D} (hS : S = S') (hT : T = T') (ψ : AddChar (AF D.host.F) ℂ)
    (χ χ' : (AE D)ˣ →* Circle) (om : GA D (negSp S') × GA D T' →* Module.End ℂ (WO (negSp S') T' → ℂ))
    (h : IsWeilDatumO ψ (negSp S') T' χ χ' om) :
    ∃ ω : WRep S T, IsWeil ψ true S T χ χ' ω ∧ HEq (ω.toSgn true) om := by
  subst hS hT
  let ω : WRep S T := om.comp ((ofSgn true S).symm.toMonoidHom.prodMap (MonoidHom.id _))
  have e : ω.toSgn true = om := MonoidHom.ext fun x => rfl
  refine ⟨ω, ?_, heq_of_eq e⟩
  unfold IsWeil
  rw [e]
  exact h

theorem core_arrows_weil : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.P (i + 1)).V (G.P i).V, GlobalTheory.Grid.IsWeil R.ψ true (G.P (i + 1)).V (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i)) ω ∧ HEq (ω.toSgn true) (W.om (.core i)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G _ _ hSp _ i hi
  have h1 : 1 ≤ D.R.m - i := by omega
  have h2 : D.R.m - i ≤ D.R.m := Nat.sub_le _ _
  have hom := W.om_is (.core i) (show (i + 1) ≤ D.R.m by omega)
  rw [(G'.chr_core (by omega : i + 1 ≤ D.R.m)).1, (G'.chr_core (by omega : i + 1 ≤ D.R.m)).2, hW.ψ,
    ← hSp.chi _ h1 h2] at hom
  exact exists_wrep_of_eq (hSp.core (i + 1) (by omega)).sp (hSp.core i (by omega)).sp _ _ _ _ hom

end GlobalTheory.GridJoin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWRepOfNegSp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}

theorem exists_wRep_of_negSp {S T S' T' : HSp D} (hS : S = S') (hT : T = T') (ψ : AddChar (AF D.host.F) ℂ)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D (negSp S') × GA D T' →* Module.End ℂ (WO (negSp S') T' → ℂ))
    (h : IsWeilDatumO ψ (negSp S') T' χS χT om) :
    ∃ ω : GlobalTheory.Grid.WRep S T, GlobalTheory.Grid.IsWeil ψ true S T χS χT ω ∧ HEq (ω.toSgn true) om := by
  subst hS; subst hT
  let ω : GlobalTheory.Grid.WRep S T :=
    om.comp (((GlobalTheory.Grid.ofSgn true S).symm.toMonoidHom.prodMap (MonoidHom.id _) :
      GA D S × GA D T →* GA D (negSp S) × GA D T))
  have e : ω.toSgn true = om := MonoidHom.ext fun _ => rfl
  refine ⟨ω, ?_, heq_of_eq e⟩
  show IsWeilDatumO ψ (GlobalTheory.Grid.sgn true S) T χS χT (ω.toSgn true)
  rw [e]
  exact h

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

theorem exists_omX_of_agree : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.V (i + 1) j).V (G.V i j).V, GlobalTheory.Grid.IsWeil R.ψ true (G.V (i + 1) j).V (G.V i j).V (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j)) ω ∧ HEq (ω.toSgn true) (W.om (.chi i j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G hG _ hsp _ i j hi hj
  have hv1 := (hsp.vert (i + 1) j (by omega) hj).sp
  have hv0 := (hsp.vert i j (by omega) hj).sp
  have hom := W.om_is (.chi i j) ⟨by omega, hj⟩
  rw [hW.ψ] at hom
  obtain ⟨ω, h1, h2⟩ := exists_wRep_of_negSp hv1 hv0 R.ψ _ _ (W.om (.chi i j)) hom
  refine ⟨ω, ?_, h2⟩
  have hchi : G.chi (D.R.m - i) = G'.ch.chi (D.R.m - i) := hsp.chi _ (by omega) (by omega)
  have rS : (G'.V (.grid (i + 1) j)).rank = rkV D (i + 1) j := by
    rw [← hv1]; exact (hG.vert i j (by omega) hj).rank
  have rT : (G'.V (.grid i j)).rank = rkV D i j := by
    rw [← hv0]
    cases i with
    | succ k => exact (hG.vert k j (by omega) hj).rank
    | zero =>
      rw [hv0]
      show (columnBlock R.toLevCh j).sp.rank = _
      simp only [rkV, zero_mul, add_zero]
      rcases hj.eq_or_lt with rfl | hk
      · rw [colY_m]; exact D.sp.X'_rank
      · rw [colY_lt _ hk]
        exact (D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [min_eq_left hk.le]; rfl)
  have cS : G'.chrS (.chi i j) = G.chiAt (D.R.m - i) (rkV D (i + 1) j) := by
    show Formalism.IndefR.Lift.attChr (G'.ch.chi (D.R.m - i)) R.toLevCh.eta (G'.V (.grid (i + 1) j)).rank = _
    rw [rS, ← hchi]
  have cT : G'.chrT (.chi i j) = G.chiAt (D.R.m - i) (rkV D i j) := by
    show Formalism.IndefR.Lift.attChr (G'.ch.chi (D.R.m - i)) R.toLevCh.eta (G'.V (.grid i j)).rank = _
    rw [rT, ← hchi]
  rw [cS, cT] at h1
  exact h1

end GlobalTheory.GridJoin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsWeilOfEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem exists_isWeil_of_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S S' T' Tg : HSp D} (hS : S = S') (hT : Tg = T')
    {χS χT : (AE D)ˣ →* Circle} (ω' : GlobalTheory.Grid.WRep S' T') (h : IsWeilDatumO ψ S' T' χS χT ω') :
    ∃ ω : GlobalTheory.Grid.WRep S Tg, GlobalTheory.Grid.IsWeil ψ false S Tg χS χT ω ∧ HEq ω ω' := by
  subst hS hT
  exact ⟨ω', h, HEq.rfl⟩

theorem omCol_of_weil : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.Xp j).V (G.nX j).V, GlobalTheory.Grid.IsWeil R.ψ false (G.Xp j).V (G.nX j).V (R.toLevCh.mu t (j + 1)) (R.toLevCh.mu t (j + 1)) ω ∧ HEq ω (W.om (.top t j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G _ _ hSp _ t j hj
  have hS : (G.Xp j).V = G'.V (.top j) := (hSp.top j hj.le).sp
  have hT : (G.nX j).V = G'.V (.top (j + 1)) := (hSp.top (j + 1) hj).sp
  have hω := W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)
  have hr : ∀ k, k ≤ D.R.m → Even (G'.V (.top k)).rank := fun k hk => by
    have := (G'.isV (X := .top k) hk (fun _ h => by cases h)).rank
    rw [this]; exact even_rankX D k
  have eS : G'.chrS (.top t j) = R.toLevCh.mu t (j + 1) := by
    simp [GlobalTheory.ChiGrid.GridData.chrS, Formalism.IndefR.Lift.attChr, GlobalTheory.ChiGrid.GridData.chr, Nat.not_odd_iff_even.2 (hr j hj.le)]
  have eT : G'.chrT (.top t j) = R.toLevCh.mu t (j + 1) := by
    simp [GlobalTheory.ChiGrid.GridData.chrT, Formalism.IndefR.Lift.attChr, GlobalTheory.ChiGrid.GridData.chr, Nat.not_odd_iff_even.2 (hr (j + 1) hj)]
  rw [eS, eT, hW.ψ] at hω
  exact exists_isWeil_of_eq hS hT _ hω

end GlobalTheory.GridJoin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepCharactersEqGridRowZeroRanks
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem arrS_cast_weil_vac {D : D7} {S S' T T' : Node D} (hS : S = S') (hT : T = T') (a : ArrS S T)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS χT : (AE D)ˣ →* Circle) {α : Type} (ω' : α)
    (hw : IsWeil ψ false S.V T.V χS χT a.ω) (hv : IsVac ψ θ false S T a.vac) (ho : HEq a.ω ω') :
    IsWeil ψ false S'.V T'.V χS χT (a.cast hS hT).ω ∧ IsVac ψ θ false S' T' (a.cast hS hT).vac ∧
      HEq (a.cast hS hT).ω ω' := by
  subst hS hT
  exact ⟨hw, hv, ho⟩

theorem chainStepCharacters_eq_gridRowZero_ranks {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) (j : ℕ) :
    Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1) =
      (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j), GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) := by
  have hr : Odd D.R.r := by
    have h1 := D.R.k_even; have h2 := D.R.m_even; have h3 := D.R.two_le_m
    unfold Ranks.r; grind
  rw [Lift.chrStep_eq_att _ _ hr D.R.t_odd (Nat.le_add_left 1 j)]
  simp [rkV]

theorem testGridRowZeroArrows_weil_vacua_agree : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → GlobalTheory.Grid.IsWeil R.ψ false (GlobalTheory.Grid.row0 R j).V (GlobalTheory.Grid.row0 R (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) (GlobalTheory.Grid.th0 R t j).ω ∧ GlobalTheory.Grid.IsVac R.ψ R.θ false (GlobalTheory.Grid.row0 R j) (GlobalTheory.Grid.row0 R (j + 1)) (GlobalTheory.Grid.th0 R t j).vac ∧ HEq (GlobalTheory.Grid.th0 R t j).ω (W.om (.mu t 0 j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ _ _ t j hj
  have hc := chainStepCharacters_eq_gridRowZero_ranks R t j
  by_cases h : j + 1 < D.R.m
  · have hw : IsWeil R.ψ false (nodeY R j).V (nodeY R (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j))
        (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) (stepY R t j).ω := by
      have := hR.chain.ωY t j h
      rw [hc] at this
      exact (isWeil_false _ _ _ _ _ _).2 this
    have hv : IsVac R.ψ R.θ false (nodeY R j) (nodeY R (j + 1)) (stepY R t j).vac := (hR.chain.vY t j h).1
    have key := arrS_cast_weil_vac (nodeY_eq_chainVertexAtRowZero_of_lt R (by omega)) (nodeY_eq_chainVertexAtRowZero_of_lt R h) (stepY R t j) R.ψ R.θ _ _ (W.om (.mu t 0 j)) hw hv
      (hW.omY t j h).symm
    unfold th0
    rw [dite_eq_left h]
    exact key
  · have h' : j + 1 = D.R.m := by omega
    have hw : IsWeil R.ψ false (nodeY R (D.R.m - 1)).V (nodeX R).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j))
        (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) (stepX R t).ω := by
      have hc' : Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m =
          (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j), GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) := by
        rw [← h']; exact hc
      have := hR.chain.ωX t
      rw [hc'] at this
      exact (isWeil_false _ _ _ _ _ _).2 this
    have hv : IsVac R.ψ R.θ false (nodeY R (D.R.m - 1)) (nodeX R) (stepX R t).vac := (hR.chain.vX t).1
    have key := arrS_cast_weil_vac (nodeY_pred_eq_chainVertexAtRowZero_last R h') (nodeX_eq_chainVertexAtRowZero_of_ge R h) (stepX R t) R.ψ R.θ _ _ (W.om (.mu t 0 j)) hw hv
      (hW.omX t j h').symm
    unfold th0
    rw [dite_eq_right h, dite_eq_left h']
    exact key

end GlobalTheory.GridJoin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTestGridArrowsVacuaIntertwiners
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

theorem exists_arrows : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∃ X ωT vacT ItT ωC vacC ItC dn ItU vC, (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsArrows ∧ (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsData ∧ ArrAgree (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC) W := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDC hHC hH hS F hR hsc G' W hW G hsp hch hag hcos
  have wX := GlobalTheory.GridJoin.exists_omX_of_agree hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have vX := GlobalTheory.GridJoin.exists_vacX hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have iX := GlobalTheory.T.exists_nonzero_real_intertwiner_grid_arrow hDC hHC hH hS hR hsc W hW G hsp hch hag hcos
  have wT := GlobalTheory.JoinArrows.exists_weil_rowArrow hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have vT := GlobalTheory.GridJoin.exists_isVac_th_rows hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have iT := GlobalTheory.T.gridRowArrow_exists_common_realIntertwiner hDC hHC hH hS hR hsc W hW G hsp hch hag hcos
  have wC := GlobalTheory.GridJoin.omCol_of_weil hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have vC := GlobalTheory.GridJoin.exists_isVac_col hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have iC := GlobalTheory.GridJoin.ColIt.exists_col_intertwiner hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have wD := GlobalTheory.GridJoin.core_arrows_weil hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have vD := GlobalTheory.GridJoin.exists_isVac_down hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have iD := GlobalTheory.T.exists_downArrow_realIntertwiner_with_adjoint hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have r0w := GlobalTheory.GridJoin.testGridRowZeroArrows_weil_vacua_agree hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have r0i := GlobalTheory.GridJoin.RowArrows.chainIntertwiners_rowZero_unitVacua hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have dT := GlobalTheory.T.exists_gridCosetData_eq_weilCosetVectors hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have hXa : ∀ i j, ∃ a : GlobalTheory.Grid.ArrS (G.V (i + 1) j) (G.V i j), i < D.R.m → j ≤ D.R.m →
      a.Is R.ψ R.θ true (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j)) ∧
      HEq (a.ω.toSgn true) (W.om (.chi i j)) ∧ (j = 0 → HEq a.vac (W.vac i)) := by
    intro i j
    by_cases h : i < D.R.m ∧ j ≤ D.R.m
    · obtain ⟨ω, hω, hωa⟩ := wX i j h.1 h.2
      obtain ⟨f, hf, hf0⟩ := vX i j h.1 h.2
      obtain ⟨It, hIt⟩ := iX i j h.1 h.2 ω f hω hf
      exact ⟨⟨ω, f, It⟩, fun _ _ => ⟨⟨hω, hf, hIt⟩, hωa, hf0⟩⟩
    · exact ⟨⟨1, 0, 0⟩, fun a b => absurd ⟨a, b⟩ h⟩
  choose X hX using hXa
  have hTa : ∀ i j, ∃ (ω : T → GlobalTheory.Grid.WRep (G.nV i j).V (G.nV i (j + 1)).V) (f : WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ)
      (It : GlobalTheory.Grid.Pol (G.nV i j) (G.nV i (j + 1)) →ₗ[ℂ] SmT (G.nV i (j + 1)).M →ₗ[ℂ] SmT (G.nV i j).M),
      i + 1 ≤ D.R.m → j < D.R.m → ∀ t, (⟨ω t, f, It⟩ : GlobalTheory.Grid.ArrS (G.nV i j) (G.nV i (j + 1))).Is R.ψ R.θ false
        (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1))) ∧
        HEq (ω t) (W.om (.mu t (i + 1) j)) := by
    intro i j
    by_cases h : i + 1 ≤ D.R.m ∧ j < D.R.m
    · choose ω hω hωa using fun t => wT t i j h.1 h.2
      obtain ⟨f, hf⟩ := vT i j h.1 h.2
      obtain ⟨It, hIt⟩ := iT i j h.1 h.2 ω f hω hf
      exact ⟨ω, f, It, fun _ _ t => ⟨⟨hω t, hf, hIt t⟩, hωa t⟩⟩
    · exact ⟨fun _ => 1, 0, 0, fun a b => absurd ⟨a, b⟩ h⟩
  choose ωT vacT ItT hT using hTa
  have hCa : ∀ j, ∃ (ω : T → GlobalTheory.Grid.WRep (G.Xp j).V (G.nX j).V) (f : WO (G.Xp j).V (G.nX j).V → ℂ)
      (It : GlobalTheory.Grid.Pol (G.Xp j) (G.nX j) →ₗ[ℂ] SmT (G.Xp j).M →ₗ[ℂ] SmT (G.nX j).M),
      j < D.R.m → ∀ t, (⟨ω t, f, It⟩ : GlobalTheory.Grid.ArrT (G.Xp j) (G.Xp (j + 1))).Is R.ψ R.θ false
        (R.toLevCh.mu t (j + 1)) (R.toLevCh.mu t (j + 1)) ∧ HEq (ω t) (W.om (.top t j)) := by
    intro j
    by_cases h : j < D.R.m
    · choose ω hω hωa using fun t => wC t j h
      obtain ⟨f, hf⟩ := vC j h
      obtain ⟨It, hIt⟩ := iC j h ω f hω hf
      exact ⟨ω, f, It, fun _ t => ⟨⟨hω t, hf, hIt t⟩, hωa t⟩⟩
    · exact ⟨fun _ => 1, 0, 0, fun a => absurd a h⟩
  choose ωC vacC ItC hC using hCa
  have hDa : ∀ i, ∃ (a : GlobalTheory.Grid.ArrT (G.P (i + 1)) (G.P i))
      (U : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ⋆[ℂ] SmT (G.P i).M →ₗ[ℂ] SmT (G.P (i + 1)).M), i < D.R.m →
      a.Is R.ψ R.θ true (G.chi (D.R.m - i)) (G.chi (D.R.m - i)) ∧ a.IsAdj U ∧ HEq (a.ω.toSgn true) (W.om (.core i)) := by
    intro i
    by_cases h : i < D.R.m
    · obtain ⟨ω, hω, hωa⟩ := wD i h
      obtain ⟨f, hf⟩ := vD i h
      obtain ⟨It, U, hIt, hU⟩ := iD i h ω f hω hf
      exact ⟨⟨ω, f, It⟩, U, fun _ => ⟨⟨hω, hf, hIt⟩, hU, hωa⟩⟩
    · exact ⟨⟨1, 0, 0⟩, 0, fun a => absurd a h⟩
  choose dn ItU hD using hDa
  have hVa : ∀ i, ∃ v : G.toGridSp.Cos R i → (WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ), i < D.R.m →
      (∀ c, GlobalTheory.Grid.IsCosetVec R.ψ true (G.V (i + 1) 0) (G.V i 0) G.idem (G.lvl R) c (X i 0).vac (v c)) ∧
      (∀ c, ∃ κ, HEq (v c) (W.cosVec i κ)) ∧ ∀ κ, ∃ c, HEq (v c) (W.cosVec i κ) := by
    intro i
    by_cases h : i < D.R.m
    · obtain ⟨v, hv⟩ := dT i h (X i 0).vac ((hX i 0 h (Nat.zero_le _)).2.2 rfl)
      exact ⟨v, fun _ => hv⟩
    · exact ⟨fun _ _ => 0, fun h' => absurd h' h⟩
  choose vCo hvC using hVa
  refine ⟨X, fun t i j => ωT i j t, vacT, ItT, fun t j => ωC j t, vacC, ItC, dn, ItU, vCo,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact fun i j hi hj => (hX i j hi hj).1
  · intro t i j hi hj
    cases i with
    | zero => exact ⟨(r0w t j hj).1, (r0w t j hj).2.1, r0i t j hj⟩
    | succ i => exact (hT i j hi hj t).1
  · exact fun t j hj => (hC j hj t).1
  · exact fun i hi => (hD i hi).1
  · exact fun i hi => (hD i hi).2.1
  · exact fun i hi c => (hvC i hi).1 c
  · exact fun i j hi hj => (hX i j hi hj).2.1
  · intro t i j hi hj
    cases i with
    | zero => exact (r0w t j hj).2.2
    | succ i => exact (hT i j hi hj t).2
  · exact fun t j hj => (hC j hj t).2
  · exact fun i hi => (hD i hi).2.2
  · exact fun i hi => (hX i 0 hi (Nat.zero_le _)).2.2 rfl
  · exact fun i hi => (hvC i hi).2

end GlobalTheory.GridJoin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTestGridArrowsVacuaIntertwinersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_testGrid_arrows_vacua_intertwiners : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∃ X ωT vacT ItT ωC vacC ItC dn ItU vC, (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsArrows ∧ (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsData ∧ ArrAgree (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC) W := by
  first | exact @GlobalTheory.GridJoin.exists_arrows | exact GlobalTheory.GridJoin.exists_arrows | (intros; apply GlobalTheory.GridJoin.exists_arrows <;> assumption)
end
