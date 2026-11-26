module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIndexZeroLevelElementGivenReductionAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReducesToResidueOfLocalLevelElementMovedBack
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReducesToResidueOfLocalLevelElementMovedBack
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZeroFamRead
open GlobalTheory.LevZeroRead


set_option maxHeartbeats 1000000 in
theorem red_of_isLoc : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (b : GA D (c.V 0)) (β : GL (Fin (c.V 0).rank) (Lev.EAf D)), GlobalTheory.LevZero.LocAt G PP b β → b ∈ GfC (c.V 0) → ∀ (hr : D.R.r ≤ (c.V 0).rank) (g : GA D (c.V 0)) (x : G.S.P.J), (ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) g (GlobalTheory.LevZeroGen.upZero G.S (Fin D.R.t) x.1) → finE (c.V 0) (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → GlobalTheory.LevZero.Red G PP x (upperLeftBlock hr (redFn β PP (finE (c.V 0) (b⁻¹ * g * b)))) := by
  intro D c v G PP b β hL hbf hr g x hg hS
  obtain ⟨π', h1, h2, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D G.k G.q PP hL.idem
  obtain ⟨e, he, hM⟩ := hL.frame (G.s + 1) (Nat.zero_add _)
  obtain ⟨m, hm⟩ := hS
  choose f hf using toEAf_onto D
  have hπ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) (Formalism.L2.Theta.AE D)), (Z.map (toEAf D)).map π' = Z.map (GlobalTheory.LocMod.ofSplit G.q).π := fun Z => by
    ext i j; exact h1 _
  have hb : ((β.val.map f).map (toEAf D)) = β.val := by ext i j; exact hf _
  have hM' := hM _ hb
  rw [← hπ, Matrix.map_mul (f := toEAf D), hb, ← finE_val] at hM'
  have hg2 := hg.2
  rw [← hπ, ← finE_val] at hg2
  have hmul : Lev.finE (c.V 0) b * β * intGL _ _ _ m =
      Lev.finE (c.V 0) g * (Lev.finE (c.V 0) b * β) := by
    have : β * intGL _ _ _ m * β⁻¹ = _ := hm
    rw [map_mul, map_mul, map_inv] at this
    rw [mul_assoc, eq_mul_of_mul_inv_eq this]
    group
  have hmul' := congrArg (fun Z : GL (Fin (c.V 0).rank) (Lev.EAf D) => Z.val.map π') hmul
  simp only [Units.val_mul] at hmul'
  rw [Matrix.map_mul (L := _ * _), Matrix.map_mul (M := _ * _), hM', hg2] at hmul'
  have key := matrix_in_frame _ _ (G.FY 0 (G.s + 1) (Nat.zero_add _)).γβ _ _ e
    (x.1.val.submatrix (GlobalTheory.StepData.ixZero _ (Fin D.R.t)).symm (GlobalTheory.StepData.ixZero _ (Fin D.R.t)).symm) _ hmul'
  have hn : (c.V 0).rank ≤ D.R.r := by
    have := Fintype.card_congr e
    simp at this
    have := G.hs
    show _ ≤ D.R.k + D.R.m - 1
    omega
  intro a b a' b' ha hb' z hz
  rw [upperLeftBlock_apply_of_eq hr hn, ← hm, redFn_frGL] at hz
  have ea : e.symm (Fin.castLE hr a') = Sum.inl a := by
    rw [Equiv.symm_apply_eq]; apply Fin.ext; rw [he]; rcases a with a | a <;> exact ha
  have eb : e.symm (Fin.castLE hr b') = Sum.inl b := by
    rw [Equiv.symm_apply_eq]; apply Fin.ext; rw [he]; rcases b with b | b <;> exact hb'
  have k2 := congrFun (congrFun key (Fin.castLE hr a')) (Fin.castLE hr b')
  rw [Matrix.submatrix_apply, ea, eb] at k2
  have k3 : resS D.host.F PP (m.val (Fin.castLE hr a') (Fin.castLE hr b') - oToS D.host.F D.host.E z) = 0 := by
    rw [map_sub, resS_oToS, hz]; exact sub_self _
  have k4 := (h2.ker _).1 k3
  rw [map_sub] at k4
  have k5 : π' (oToS D.host.F D.host.E z).1 = (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) := by
    refine Eq.trans (congrArg π' ?_) (h1 (incA D (z : D.host.E)))
    rfl
  convert k4 using 3
  · exact k2.symm
  · exact k5.symm

end GlobalTheory.LevZeroFamRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReducesToResidueOfLocalLevelElementMovedBackStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducesToResidue_of_localLevelElement_movedBack : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (b : GA D (c.V 0)) (β : GL (Fin (c.V 0).rank) (Lev.EAf D)), GlobalTheory.LevZero.LocAt G PP b β → b ∈ GfC (c.V 0) → ∀ (hr : D.R.r ≤ (c.V 0).rank) (g : GA D (c.V 0)) (x : G.S.P.J), (ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) g (GlobalTheory.LevZeroGen.upZero G.S (Fin D.R.t) x.1) → finE (c.V 0) (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → GlobalTheory.LevZero.Red G PP x (upperLeftBlock hr (redFn β PP (finE (c.V 0) (b⁻¹ * g * b)))) := by
  first | exact @GlobalTheory.LevZeroFamRead.red_of_isLoc | exact GlobalTheory.LevZeroFamRead.red_of_isLoc | (intros; apply GlobalTheory.LevZeroFamRead.red_of_isLoc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIndexZeroLevelElementGivenReductionAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZeroPlace

section Helpers
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod.LevBack
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (framePos)
open GlobalTheory.SymBridge (IsOrd zPos)
open GlobalTheory.AdelicLatMove (finEmb finEmb_mul)
open Formalism.L2.DIV (blockTri blkOf blk2 upperLeftBlock resS oToS idS kP frGL St redFn)

variable {D : D7} {c : Comm D} {v : VCom c}

theorem red_at {PP : Formalism.L2.DIV.Pl D.host.E} (G : GLoc v) {j n : ℕ} (hr : D.R.r ≤ n)
    {e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) j ≃ Fin n} (he : IsOrd zPos e) (π : Lev.EAf D →+* G.k)
    (h1 : ∀ a, π (toEAf D a) = G.q.pr a) (h3 : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, π s ∈ 𝒪[G.k])
    (h4 : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP s = 0 ↔ valuation G.k (π s) < 1)
    (Y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : ∀ a b, ¬ FreeIx G.S.ρ a b → valuation G.k (π (Y.val (e a) (e b)) - (1 : Matrix _ _ G.k) a b) < 1) :
    Formalism.UG.bc (resS D.host.F PP) Y ∈ blockTri (blkOf D.R.r D.R.t) ∧
      ∃ x, GlobalTheory.LevZero.Red G PP x (upperLeftBlock hr (Formalism.UG.bc (resS D.host.F PP) Y)) := by
  haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
  have hs := G.hs
  obtain ⟨c1, x, c2⟩ := red_of_pattern G.S (by unfold Ranks.r; omega) hr he (resS D.host.F PP)
    (π.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) h3 h4 Y hy
  refine ⟨c1, x, fun a b a' b' ha hb z hz => ?_⟩
  have := c2 a b a' b' ha hb (oToS D.host.F D.host.E z) ((Formalism.L2.DIV.resS_oToS PP z).trans hz)
  rwa [show (π.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (oToS D.host.F D.host.E z) =
    (ofSplit G.q).pr (z : D.host.E) from h1 (incA D (z : D.host.E))] at this


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem lev_back {cm : GlobalTheory.ChainOnto.Com D} {st : StAt (c.V 0)} {b : GA D (c.V 0)} {G : cm.Pg → GLoc v}
    (hB : GlobalTheory.LevZero.Bot cm st b G) (PP : cm.Pg) (c' : ℕ) (hc : 0 + c' = (G PP).s + 1) (x : GA D (c.V 0))
    (xk : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin c') (G PP).k)
    (hx : (ofSplit (G PP).q).IsLoc ((G PP).FY 0 c' hc) x xk)
    (hxk : xk ∈ (((G PP).S.T (Fin D.R.t)).lev 0 c' hc).J) :
    b⁻¹ * x * b ∈ levS (c.V 0) st.β st.L := by
  have hs := (G PP).hs
  have hst := hB.mem
  obtain ⟨hr, ξ, hL⟩ := hst.lev
  replace hL : st.L = _ := hL
  obtain ⟨a, ha⟩ := hB.com.split
  obtain ⟨e, he, hmv⟩ := (hB.loc PP).frame c' hc
  obtain ⟨π, h1, h2, h3, h4⟩ := exists_chart (G PP).q (hB.loc PP).idem
  let L := typeFrame (G PP).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) 0 c' hc)
  obtain ⟨hyK, hyP⟩ := (pattern_iter _ _ _ (G PP).S (Fin D.R.t) 0 (L.conj.symm xk)).1 hxk
  have hmap : ∀ M : Matrix (Fin (c.V 0).rank) (Fin (c.V 0).rank) (AE D),
      (M.map (toEAf D)).map π = M.map (G PP).q.pr := fun M => Matrix.ext fun _ _ => h1 _
  have hγ : GeneralLinearGroup.map π (st.β⁻¹ * Lev.finE (c.V 0) (b⁻¹ * x * b) * st.β) =
      reGL e (L.conj.symm xk) := by
    rw [← conj_frame ((G PP).FY 0 c' hc) L e (GeneralLinearGroup.map π (Lev.finE (c.V 0) b * st.β))
      (GeneralLinearGroup.map π (Lev.finE (c.V 0) x)) (L.conj.symm xk) ?_ ?_]
    · rw [MonoidHom.map_mul (Lev.finE (c.V 0)), MonoidHom.map_mul (Lev.finE (c.V 0)), MonoidHom.map_inv, conj_conj,
        MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv]
    · have hb : (st.β.val.map (finEmb D)).map (toEAf D) = st.β.val := Matrix.ext fun _ _ => toEAf_finEmb _
      refine Eq.trans ?_ (hmv _ hb)
      refine Eq.trans ?_ (hmap _)
      rw [Matrix.map_mul, hb]
      rfl
    · rw [MulEquiv.apply_symm_apply]
      exact (hmap _).trans hx.2
  obtain ⟨Y, hY, hYv, hY1⟩ := exists_int (G PP).q π h2 (c.V 0) hst.selfDual hst.frame (t := b) hx.1 (by
    rw [hγ, mem_KO, ← map_inv]
    rw [mem_KO] at hyK
    exact ⟨fun _ _ => hyK.1 _ _, fun _ _ => hyK.2 _ _⟩)
  have hall : ∀ PP' : cm.Pg, Formalism.UG.bc (resS D.host.F PP'.1) Y ∈ blockTri (blkOf D.R.r D.R.t) ∧
      ∃ x, GlobalTheory.LevZero.Red (G PP') PP'.1 x (upperLeftBlock hr (Formalism.UG.bc (resS D.host.F PP'.1) Y)) := fun PP' => by
    by_cases hne : PP' = PP
    · subst hne
      refine red_at (G PP') hr he π h1 h3 h4 Y fun a₁ b₁ hab => ?_
      have e1 : π (Y.val (e a₁) (e b₁)) = (L.conj.symm xk).val a₁ b₁ := by
        rw [hYv]
        refine (congrArg (fun g : GL _ _ => g.val (e a₁) (e b₁)) hγ).trans ?_
        simp only [reGL_val, submatrix_apply, Equiv.symm_apply_apply]
      rw [e1]
      exact hyP a₁ b₁ hab
    · have hs' := (G PP').hs
      obtain ⟨e', he', -⟩ := (hB.loc PP').frame c' (by omega)
      obtain ⟨π', k1, -, k3, k4⟩ := exists_chart (G PP').q (hB.loc PP').idem
      refine red_at (G PP') hr he' π' k1 k3 k4 Y fun a₁ b₁ _ => ?_
      have e1 := congrArg π' (hY1 (e' a₁) (e' b₁))
      rw [RingHom.map_mul, k1, pr_other (G PP).q (G PP').q ha PP.2 PP'.2 (fun h => hne (Subtype.ext h)) (hB.loc PP).idem
        (hB.loc PP').idem, zero_mul, RingHom.map_sub] at e1
      have e2 : π' ((1 : Matrix _ _ (Lev.EAf D)) (e' a₁) (e' b₁)) = (1 : Matrix _ _ (G PP').k) a₁ b₁ := by
        change π' (if e' a₁ = e' b₁ then 1 else 0) = (if a₁ = b₁ then 1 else 0)
        by_cases h : a₁ = b₁
        · simp only [h, if_true, map_one]
        · simp only [h, e'.injective.ne h, if_false, map_zero]
      rw [← e2, ← e1, Valuation.map_zero]
      exact zero_lt_one
  change _ ∈ Lev.levG _ _ st.L
  rw [hL]
  refine ⟨(GfC _).mul_mem ((GfC _).mul_mem ((GfC _).inv_mem hB.fin)
    (GlobalTheory.WeilProduct.mem_GfC_of_suppAt (G PP).q.split hx.1)) hB.fin, ?_⟩
  change Lev.finE (c.V 0) _ ∈ Formalism.L2.DIV.lev _ _ _ _
  refine ⟨Formalism.L2.DIV.mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, ⟨Y, hY⟩, fun PP' hPP' => ?_,
    fun _ h => absurd h (Finset.notMem_empty _)⟩, ?_⟩
  · rw [← hY, Formalism.L2.DIV.redFn_frGL]
    exact (hall ⟨PP', hPP'⟩).1
  · refine (hB.grp _).2 fun PP' => ?_
    change ∃ z, GlobalTheory.LevZero.Red (G PP') PP'.1 z (upperLeftBlock hr (redFn _ PP'.1 _))
    rw [← hY, Formalism.L2.DIV.redFn_frGL]
    exact (hall PP').2

theorem finE_mem_St {cm : GlobalTheory.ChainOnto.Com D} {st : StAt (c.V 0)} {b : GA D (c.V 0)} {G : cm.Pg → GLoc v}
    (hB : GlobalTheory.LevZero.Bot cm st b G) (g : GA D (c.V 0)) (hg : g ∈ levS (c.V 0) st.β st.L) :
    finE (c.V 0) g ∈ St st.β := by
  obtain ⟨hr', ξ, hL⟩ := hB.mem.lev
  replace hL : st.L = _ := hL
  have h1 : g ∈ GfC _ ∧ finE (c.V 0) g ∈ Formalism.L2.DIV.lev D.sp.cm (c.V 0).gram st.β st.L := hg
  rw [hL, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev] at h1
  exact h1.2.1.2.1

theorem red_of_congr (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (x x' : G.S.P.J) (g : GL (Fin D.R.r) (kP PP))
    (h : GlobalTheory.LevZero.Red G PP x' g)
    (hc : (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k)⁻¹ * x.1 ∈ GlobalTheory.SplitWeil.KOne G.k (Fin D.R.k ⊕ Fin (G.s + 1))) :
    GlobalTheory.LevZero.Red G PP x g := by
  intro a b a' b' ha hb z hz
  have h1 := h a b a' b' ha hb z hz
  have hI : GlobalTheory.StepData.IntM (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val :=
    GlobalTheory.StepData.intM_of_mem_KO (G.S.P.le_KO x'.2)
  have hM := hI.mul_maxM (GlobalTheory.StepData.mem_KOne.1 hc)
  have e : (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val *
      (((x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k)⁻¹ * x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - 1) =
      (x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val := by
    rw [Matrix.mul_sub, Units.val_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  rw [e] at hM
  have h2 := hM a b
  rw [Matrix.sub_apply] at h2
  have e2 : (x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) =
      ((x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b) +
      ((x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E)) := by ring
  rw [e2]
  exact (Valuation.map_add _ _ _).trans_lt (max_lt h2 h1)

end Helpers

end GlobalTheory.LevZeroPlace


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.LevZeroPlace.one_place : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ Q : GA D (c.V 0) → Prop, (∀ k ∈ levS (c.V 0) st.β st.L, ∀ k' ∈ levS (c.V 0) st.β st.L, Q k → Q k' → Q (k * k')) → (∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (c.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * n * b)) → (∀ x ∈ GfC (c.X 0), b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b)) → ∀ (PP : cm.Pg) (x : (G PP).S.P.J), ∃ m ∈ levS (c.V 0) st.β st.L, Q m ∧ (∀ hr : D.R.r ≤ (c.V 0).rank, GlobalTheory.LevZero.Red (G PP) PP.1 x (upperLeftBlock hr (redFn st.β PP.1 (finE (c.V 0) m)))) ∧ ∀ PP' ∈ cm.Pg, PP' ≠ PP.1 → redFn st.β PP' (finE (c.V 0) m) = 1 := by
  intro D c v cm st b G h0 hB Q hmul hN hU PP x
  have hst : ∀ w ∈ levS (c.V 0) st.β st.L, finE (c.V 0) w ∈ St st.β := GlobalTheory.LevZeroPlace.finE_mem_St hB
  have hbes := (G PP).bes 0 D.R.rS h0 ((G PP).s + 1) (Nat.zero_add _)
  have hρ : (G PP).S.ρ = D.R.rS := by have := hbes.1; have := (G PP).S.odd; omega
  have hLev := GlobalTheory.LevZeroPlace.lev_back hB PP ((G PP).s + 1) (Nat.zero_add _)
  have hv : ∀ P : cm.Pg, (G P).q.v = IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers D.host.F) P.1 :=
    fun P => (hB.loc P).under
  have horth : ∀ P P' : cm.Pg, P ≠ P' →
      ((G P).q.e + cA D (G P).q.e) * ((G P').q.e + cA D (G P').q.e) = 0 := by
    intro P P' hne
    obtain ⟨ε, hε, hsum⟩ := (G P).q.above
    obtain ⟨ε', hε', hsum'⟩ := (G P').q.above
    have hvv : (G P).q.v ≠ (G P').q.v := by
      rw [hv P, hv P']
      intro h
      exact hne (Subtype.ext (GlobalTheory.LevelPlaces.injOn_under D cm hB.com P.2 P'.2 h))
    rw [hsum, hsum', ← map_mul, GlobalTheory.SingleDatum.BasePair.placeIdem_mul_eq_zero hε' hε hvv, map_zero]
  have hoff : ∀ g : GA D (c.V 0), Formalism.L2.Theta.SuppAt (G PP).q.e (c.V 0) g → b⁻¹ * g * b ∈ levS (c.V 0) st.β st.L →
      ∀ PP' ∈ cm.Pg, PP' ≠ PP.1 → redFn st.β PP' (finE (c.V 0) (b⁻¹ * g * b)) = 1 :=
    fun g hg hl PP' hPP' hne => GlobalTheory.T.reduction_eq_one_of_supportedAt_orthogonal_splitPlace D (G ⟨PP', hPP'⟩).k (G ⟨PP', hPP'⟩).q PP' (hB.loc ⟨PP', hPP'⟩).idem (G PP).q.e
      (horth PP ⟨PP', hPP'⟩ fun h => hne (congrArg Subtype.val h).symm) _ _ _
      (GlobalTheory.PlaceMatch.suppAt_conj' hg _) (hst _ hl)
  obtain ⟨n, γ, hnN, hnJ, hγJ, hc⟩ := GlobalTheory.T.exists_N_embX_inv_mul_mem_KOne' (G PP).k (G PP).s D.R.k (G PP).S x.1 x.2
  obtain ⟨hup1, hup2⟩ := GlobalTheory.T.levelZeroUniformizerFrame_unipotent_and_embedGL (G PP).k (G PP).s D.R.k (G PP).S (Fin D.R.t)
  obtain ⟨hupN, -⟩ := hup1 ⟨n, hnJ⟩ hnN
  rw [hρ] at hupN
  obtain ⟨ν, hν⟩ := GlobalTheory.LocMod.Witness.exists_isLoc (GlobalTheory.LocMod.ofSplit (G PP).q)
    ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) (GlobalTheory.LevZeroGen.upZero (G PP).S (Fin D.R.t) n)
  obtain ⟨η, hη⟩ := GlobalTheory.LocMod.Witness.exists_isLoc (GlobalTheory.LocMod.ofSplit (G PP).q) ((G PP).FX 0 (Nat.zero_le _))
    (GlobalTheory.StepData.reGL (GlobalTheory.LevZeroGen.xZero (Fin D.R.k) (Fin D.R.t)) γ)
  have hη' := GlobalTheory.T.besselFrame_embedding_localElement_eq_embedded_matrix D (G PP).k _ _ _ _ _ _ _ _ hbes η _ hη
  rw [← hup2] at hη'
  have hνl := hLev ν _ hν ((GlobalTheory.LevZeroGen.upZero_mem_lev _ _ _).2 hnJ)
  have hηl := hLev _ _ hη' ((GlobalTheory.LevZeroGen.upZero_mem_lev _ _ _).2 hγJ)
  have hQν := hN PP ν _ (GlobalTheory.LocFlag.mem_flagN D _ _ _ _ _ _ _ _ _ hbes ν _ hupN hν) hupN hν hνl
  have hQη := hU η (GlobalTheory.PlaceMatch.mem_GfC_of_suppAt' (G PP).q.split hη.1) hηl
  have hprod := GlobalTheory.LocGrp.isLoc_mul _ hν hη'
  rw [← map_mul] at hprod
  have e : b⁻¹ * ν * b * (b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o η * b) =
      b⁻¹ * (ν * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o η) * b := by group
  have hl : b⁻¹ * (ν * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o η) * b ∈ levS (c.V 0) st.β st.L :=
    hLev _ _ hprod ((GlobalTheory.LevZeroGen.upZero_mem_lev _ _ _).2 (mul_mem hnJ hγJ))
  refine ⟨_, hl, e ▸ hmul _ hνl _ hηl hQν hQη, fun hr => ?_, hoff _ hprod.1 hl⟩
  exact GlobalTheory.LevZeroPlace.red_of_congr (G PP) PP.1 x ⟨_, mul_mem hnJ hγJ⟩ _
    (GlobalTheory.T.reducesToResidue_of_localLevelElement_movedBack (G PP) PP.1 b st.β (hB.loc PP) hB.fin hr _ ⟨_, mul_mem hnJ hγJ⟩ hprod (hst _ hl)) hc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIndexZeroLevelElementGivenReductionAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_indexZeroLevel_element_given_reduction_at_place : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ Q : GA D (c.V 0) → Prop, (∀ k ∈ levS (c.V 0) st.β st.L, ∀ k' ∈ levS (c.V 0) st.β st.L, Q k → Q k' → Q (k * k')) → (∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (c.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * n * b)) → (∀ x ∈ GfC (c.X 0), b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b)) → ∀ (PP : cm.Pg) (x : (G PP).S.P.J), ∃ m ∈ levS (c.V 0) st.β st.L, Q m ∧ (∀ hr : D.R.r ≤ (c.V 0).rank, GlobalTheory.LevZero.Red (G PP) PP.1 x (upperLeftBlock hr (redFn st.β PP.1 (finE (c.V 0) m)))) ∧ ∀ PP' ∈ cm.Pg, PP' ≠ PP.1 → redFn st.β PP' (finE (c.V 0) m) = 1 := by
  first | exact @GlobalTheory.LevZeroPlace.one_place | exact GlobalTheory.LevZeroPlace.one_place | (intros; apply GlobalTheory.LevZeroPlace.one_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfRhoLt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevZeroUniq
open GlobalTheory.SplitWeil GlobalTheory.StepData

variable {D : D7} {c : Comm D} {v : VCom c} {PP : Formalism.L2.DIV.Pl D.host.E}

def rho (G : GLoc v) : 𝓞 D.host.E →+* G.k := (G.q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem rho_apply (G : GLoc v) (z : 𝓞 D.host.E) : rho G z = (ofSplit G.q).pr (z : D.host.E) := rfl

theorem rho_lt (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {z : 𝓞 D.host.E} (hz : z ∈ PP.asIdeal) :
    valuation G.k (rho G z) < 1 := by
  by_cases h0 : z = 0
  · subst h0; simp
  have h0' : rho G z ≠ 0 := (map_ne_zero (G.q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 h0)
  have h1 := (hid.2 z h0).1 hz
  rw [← G.q.sec_pr, ← G.q.int_iff] at h1
  change (G.q.pr.comp (incA D)) _ ∉ _ at h1
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le] at h1
  exact (one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0'))).1 h1

theorem mem_of_rho_lt (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {z : 𝓞 D.host.E}
    (hz : valuation G.k (rho G z) < 1) : z ∈ PP.asIdeal := by
  by_cases h0 : z = 0
  · subst h0; exact zero_mem _
  have h0' : rho G z ≠ 0 := (map_ne_zero (G.q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 h0)
  refine (hid.2 z h0).2 ?_
  rw [← G.q.sec_pr, ← G.q.int_iff]
  change (G.q.pr.comp (incA D)) _ ∉ _
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le]
  exact (one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0'))).2 hz

def out (y : Formalism.L2.DIV.kP PP) : 𝓞 D.host.E := Function.surjInv (Ideal.Quotient.mk_surjective (I := PP.asIdeal)) y

theorem mk_out (y : Formalism.L2.DIV.kP PP) : Ideal.Quotient.mk PP.asIdeal (out y) = y :=
  Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := PP.asIdeal)) y

theorem rho_sub_lt (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {y : Formalism.L2.DIV.kP PP} {z : 𝓞 D.host.E}
    (hz : Ideal.Quotient.mk PP.asIdeal z = y) : valuation G.k (rho G (out y) - rho G z) < 1 := by
  rw [← map_sub]
  refine rho_lt G hid (Ideal.Quotient.eq.1 ?_)
  rw [mk_out, hz]

def pos (G : GLoc v) : Fin D.R.k ⊕ Fin (G.s + 1) ≃ Fin D.R.r :=
  finSumFinEquiv.trans (finCongr (by have := G.hs; unfold Ranks.r; omega))

theorem pos_val (G : GLoc v) (a : Fin D.R.k ⊕ Fin (G.s + 1)) : (pos G a).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a := by
  rcases a with a | a <;> rfl

def lift (G : GLoc v) (g : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) :
    Matrix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.k ⊕ Fin (G.s + 1)) G.k :=
  fun a b => rho G (out (g (pos G a) (pos G b)))

theorem lift_one (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) :
    MaxM (lift G (1 : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) - 1) := by
  intro a b
  have e : (lift G (1 : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) - 1) a b =
      rho G (out ((1 : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) (pos G a) (pos G b))) -
      rho G (if a = b then 1 else 0) := by
    simp only [Matrix.sub_apply, lift, Matrix.one_apply]
    split_ifs <;> simp
  rw [e]
  refine rho_sub_lt G hid ?_
  simp only [Matrix.one_apply, (pos G).injective.eq_iff]
  split_ifs <;> simp

theorem red_iff (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) (x : G.S.P.J) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)) :
    GlobalTheory.LevZero.Red G PP x g ↔ MaxM ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G g.val) := by
  constructor
  · intro h a b
    have := h a b (pos G a) (pos G b) (pos_val G a) (pos_val G b) _ (mk_out _)
    simpa only [Matrix.sub_apply, lift, rho_apply] using this
  · intro h a b a' b' ha hb z hz
    obtain rfl : a' = pos G a := Fin.ext (ha.trans (pos_val G a).symm)
    obtain rfl : b' = pos G b := Fin.ext (hb.trans (pos_val G b).symm)
    have e : (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E) =
        ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G g.val) a b + (rho G (out (g.val (pos G a) (pos G b))) - rho G z) := by
      simp only [Matrix.sub_apply, lift, rho_apply]; ring
    rw [e]
    exact Valuation.map_add_lt _ (h a b) (rho_sub_lt G hid hz)

theorem intM_J (G : GLoc v) (x : G.S.P.J) : IntM (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val ∧
    IntM ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k)⁻¹).val :=
  mem_KO.1 (G.S.P.le_KO x.2)

theorem red_one (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) : GlobalTheory.LevZero.Red G PP 1 1 := by
  rw [red_iff G hid]
  have := (lift_one G hid).neg
  simpa using this

theorem red_uniq (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {x x' : G.S.P.J} {g g' : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)}
    (hx : GlobalTheory.LevZero.Red G PP x g) (hx' : GlobalTheory.LevZero.Red G PP x' g')
    (hk : x.1⁻¹ * x'.1 ∈ KOne G.k (Fin D.R.k ⊕ Fin (G.s + 1))) : g = g' := by
  rw [red_iff G hid] at hx hx'
  set X := (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k) with hX
  set X' := (x' : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k) with hX'
  have h1 : MaxM ((X⁻¹ * X').val - 1) := mem_KOne.1 hk
  have h2 : MaxM (lift G g'.val - lift G g.val) := by
    have e : lift G g'.val - lift G g.val =
        (X.val - lift G g.val) + -(X'.val - lift G g'.val) + X.val * ((X⁻¹ * X').val - 1) := by
      rw [Matrix.mul_sub, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_one]
      abel
    rw [e]
    exact (hx.add hx'.neg).add ((intM_J G x).1.mul_maxM h1)
  refine Units.ext (Matrix.ext fun a' b' => ?_)
  obtain ⟨a, rfl⟩ := (pos G).surjective a'
  obtain ⟨b, rfl⟩ := (pos G).surjective b'
  have h3 : valuation G.k (rho G (out (g'.val (pos G a) (pos G b)) - out (g.val (pos G a) (pos G b)))) < 1 := by
    rw [map_sub]; simpa only [Matrix.sub_apply, lift] using h2 a b
  have h4 := Ideal.Quotient.eq.2 (mem_of_rho_lt G hid h3)
  rw [mk_out, mk_out] at h4
  exact h4.symm

end GlobalTheory.LevZeroUniq

theorem GlobalTheory.LevZeroUniq.main : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt G.q.e PP → GlobalTheory.LevZero.Red G PP 1 1 ∧ ∀ (x x' : G.S.P.J) (g g' : GL (Fin D.R.r) (kP PP)), GlobalTheory.LevZero.Red G PP x g → GlobalTheory.LevZero.Red G PP x' g' → x.1⁻¹ * x'.1 ∈ GlobalTheory.SplitWeil.KOne G.k (Fin D.R.k ⊕ Fin (G.s + 1)) → g = g' := by
  intro D c v G PP hid
  exact ⟨GlobalTheory.LevZeroUniq.red_one G hid, fun x x' g g' hx hx' hk => GlobalTheory.LevZeroUniq.red_uniq G hid hx hx' hk⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelGeneratedByLocalUnipotents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevZeroInd in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.LevZero.gen : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ Q : GA D (c.V 0) → Prop, (∀ k ∈ levS (c.V 0) st.β st.L, ∀ k' ∈ levS (c.V 0) st.β st.L, Q k → Q k' → Q (k * k')) → (∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (c.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * n * b)) → (∀ x ∈ GfC (c.X 0), b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b)) → (∀ k ∈ levS (c.V 0) st.β st.L, (∀ PP ∈ cm.Pg, redFn st.β PP (finE (c.V 0) k) = 1) → Q k) → ∀ k ∈ levS (c.V 0) st.β st.L, Q k := by
  intro D c v cm st b G h0 hB Q hmul hN hU hred
  classical
  have hst := hB.mem
  obtain ⟨hr, ξ, hL⟩ := hst.lev
  have hn : (c.V 0).rank = D.R.r := by rw [hst.rank]; show D.R.r + 0 * D.R.t = D.R.r; simp
  have key := fun x => GlobalTheory.LevYZero.lev_datY_zero (c.V 0) st.β st.L D.R.r D.R.t hr hn cm.Pg cm.P cm.chi ξ hL
    (Lev.finE (c.V 0) x) (GlobalTheory.LevSplit.finE_mem_UA _ x)
  have hSt : ∀ x ∈ levS (c.V 0) st.β st.L, Lev.finE (c.V 0) x ∈ St st.β := fun x hx => ((key x).1.1 hx.2).1
  have hRed : ∀ x ∈ levS (c.V 0) st.β st.L, ∀ PP : cm.Pg, ∃ z, GlobalTheory.LevZero.Red (G PP) PP.1 z (upperLeftBlock hr (redFn st.β PP.1 (Lev.finE (c.V 0) x))) :=
    fun x hx PP => (hB.grp _).1 ((key x).1.1 hx.2).2 PP
  have hmulm : ∀ x ∈ levS (c.V 0) st.β st.L, ∀ y ∈ levS (c.V 0) st.β st.L, x * y ∈ levS (c.V 0) st.β st.L :=
    fun x hx y hy => Subgroup.mul_mem _ hx hy
  have hinvm : ∀ x ∈ levS (c.V 0) st.β st.L, x⁻¹ ∈ levS (c.V 0) st.β st.L := fun x hx => Subgroup.inv_mem _ hx
  have claim : ∀ s : Finset (Pl D.host.E), ∀ k ∈ levS (c.V 0) st.β st.L,
      (∀ PP ∈ cm.Pg, PP ∉ s → redFn st.β PP (Lev.finE (c.V 0) k) = 1) → Q k := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro k hk h
      exact hred k hk fun PP hPP => h PP hPP (Finset.notMem_empty _)
    · intro a s ha ih k hk h
      by_cases haP : a ∈ cm.Pg
      · obtain ⟨z, hz⟩ := hRed k hk ⟨a, haP⟩
        obtain ⟨m, hm0, hQm, hmr, hmo⟩ := GlobalTheory.T.exists_indexZeroLevel_element_given_reduction_at_place cm st b G h0 hB Q hmul hN hU ⟨a, haP⟩ z
        have e1 : redFn st.β a (Lev.finE (c.V 0) m) = redFn st.β a (Lev.finE (c.V 0) k) :=
          reductionBlock_injective_of_eq hr hn ((GlobalTheory.LevZeroUniq.main (G ⟨a, haP⟩) a (hB.loc ⟨a, haP⟩).idem).2 z z _ _ (hmr hr) hz
            (by rw [inv_mul_cancel]; exact one_mem _))
        have hk1 : m⁻¹ * k ∈ levS (c.V 0) st.β st.L := hmulm _ (hinvm m hm0) k hk
        have hred1 : ∀ PP, redFn st.β PP (Lev.finE (c.V 0) (m⁻¹ * k)) =
            (redFn st.β PP (Lev.finE (c.V 0) m))⁻¹ * redFn st.β PP (Lev.finE (c.V 0) k) := fun PP => by
          rw [map_mul, map_inv, redFn_mul _ _ (inv_mem (hSt m hm0)) (hSt k hk), redFn_inv _ _ (hSt m hm0)]
        have hQ1 := ih (m⁻¹ * k) hk1 fun PP hPP hPs => by
          rw [hred1]
          by_cases hPa : PP = a
          · subst hPa
            rw [e1, inv_mul_cancel]
          · rw [hmo PP hPP hPa, h PP hPP (by simp [hPa, hPs]), inv_one, one_mul]
        have := hmul m hm0 _ hk1 hQm hQ1
        simpa using this
      · exact ih k hk fun PP hPP hPs => h PP hPP (by
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun e => haP (e ▸ hPP), hPs⟩)
  intro k hk
  exact claim cm.Pg k hk fun PP hPP h => absurd hPP h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelGeneratedByLocalUnipotentsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexZeroLevel_generated_by_local_unipotents : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ Q : GA D (c.V 0) → Prop, (∀ k ∈ levS (c.V 0) st.β st.L, ∀ k' ∈ levS (c.V 0) st.β st.L, Q k → Q k' → Q (k * k')) → (∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (c.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * n * b)) → (∀ x ∈ GfC (c.X 0), b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b)) → (∀ k ∈ levS (c.V 0) st.β st.L, (∀ PP ∈ cm.Pg, redFn st.β PP (finE (c.V 0) k) = 1) → Q k) → ∀ k ∈ levS (c.V 0) st.β st.L, Q k := by
  first | exact @GlobalTheory.LevZero.gen | exact GlobalTheory.LevZero.gen | (intros; apply GlobalTheory.LevZero.gen <;> assumption)
end
