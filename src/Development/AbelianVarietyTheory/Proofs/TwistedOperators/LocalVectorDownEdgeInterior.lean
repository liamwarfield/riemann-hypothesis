module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVecCongr
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ChainCol

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open Classical in
def extDat {m n : ℕ} (e e' : AE D) (Λ : AddSubgroup (Mx D m n)) (φ : Mx D m n → ℂ) : Mx D m n → ℂ :=
  fun x => if IsHalf e x ∧ x.map ((e - e') * ·) ∈ Λ then φ (x.map (e' * ·)) else 0

open Classical in
def stepDat (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (LS : LevDat D.host.E ℂ S.rank) (χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (e : AE D) :
    WO S T → ℂ :=
  fun x => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then
      omegaG LS χj (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ Q LS.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x))
    else 0

theorem r_le_colY {T : Type} (L : LevCh D T) (j : ℕ) : D.R.r ≤ (columnBlock L j).sp.rank := by
  rcases j with _ | j
  · exact r_le_Y 0
  · by_cases h : j + 1 < D.R.m
    · rw [colY_lt L h]; exact r_le_Y _
    · rw [show columnBlock L (j + 1) = ⟨D.sp.X', L.ΛX⟩ from if_neg h]; exact r_le_X

def colDat {T : Type} (L : LevCh D T) (t : T) (j : ℕ) : LevDat D.host.E ℂ (columnBlock L j).sp.rank :=
  Formalism.IndefR.Lev.datY _ D.R.r D.R.t j (r_le_colY L j) L.Pg (L.Q t) (LevelP.triv L.Pg D.R.r ℂ) L.chi (L.xiR t) Formalism.IndefR.Lev.Frm.B

theorem lsp_heq {X : LSp D} {S : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (h : X = ⟨S, Λ⟩) :
    X.sp = S ∧ HEq X.lat Λ := by
  subst h; exact ⟨rfl, HEq.rfl⟩

theorem datY_heq {n n' : ℕ} (h : n = n') (r t j : ℕ) (hr : r ≤ n) (hr' : r ≤ n') (Pg Q : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (fr : Formalism.IndefR.Lev.Frm) :
    HEq (Formalism.IndefR.Lev.datY n r t j hr Pg Q P χ ξ fr) (Formalism.IndefR.Lev.datY n' r t j hr' Pg Q P χ ξ fr) := by
  subst h; rfl

theorem stepVec_congr {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S S' T T' : HSp D} (hS : S = S') (hT : T = T')
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {sS' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ} {sT' : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)} {ΛT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}
    {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)} {βS' : GL (Fin S'.rank) (EAf D)} {βT' : GL (Fin T'.rank) (EAf D)}
    {LS : LevDat D.host.E ℂ S.rank} {LS' : LevDat D.host.E ℂ S'.rank} {χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {Q : Finset (Pl D.host.E)} {f₀ f : WO S T → ℂ} {f₀' f' : WO S' T' → ℂ}
    (h1 : HEq sS sS') (h2 : HEq sT sT') (h3 : HEq ΛS ΛS') (h4 : HEq ΛT ΛT') (h5 : HEq βS βS') (h6 : HEq βT βT')
    (h7 : HEq LS LS') (h8 : HEq f₀ f₀') (h9 : HEq f f')
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f) :
    IsStepVecOf ψ θ S' T' sS' sT' ΛS' ΛT' βS' βT' LS' χj Q ξ f₀' f' := by
  subst hS hT
  cases h1; cases h2; cases h3; cases h4; cases h5; cases h6; cases h7; cases h8; cases h9
  exact h

end GlobalTheory.ChainCol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSBHalfGivenFnDown
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun GlobalTheory.ChainCol
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Classical

noncomputable section

namespace GlobalTheory.FlipStart.ColSB

open GlobalTheory.FunObj.Comparison₂

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem stepFn_congr_red' (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) {j : ℕ} (hj : j < D.R.m) (w : Pl D.host.E)
    {a b : ℕ} (ha : a = D.R.r + j * D.R.t) (hb : b = D.R.r + (j + 1) * D.R.t)
    (N N' : Matrix (Fin b) (Fin a) (OA D)) (h : N.map (resS D.host.F w) = N'.map (resS D.host.F w)) :
    stepFn L t w j ((N.map (cptO w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) =
      stepFn L t w j ((N'.map (cptO w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) := by
  by_cases hw : w ∈ GlobalTheory.FlipTop.topPl L t
  · exact GlobalTheory.FlipTop.stepFn_congr_red G hL t hj hw ha hb N N' h
  · have hP : w ∉ L.Pg := fun h => hw (Finset.mem_union_left _ h)
    have hQ : w ∉ L.Q t := fun h => hw (Finset.mem_union_right _ h)
    have hI : ∀ M : Matrix (Fin b) (Fin a) (OA D),
        GlobalTheory.StepData.IntM ((M.map (cptO w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) := by
      intro M i l
      have h1 := (mem_OA_iff _).1 (M (ixOf G t w hb i) (ixOf G t w ha l)).2 w
      show cptO w (M (ixOf G t w hb i) (ixOf G t w ha l)) ∈ _
      rw [cptO_apply]
      exact (vEq w).le_one_iff_le_one.2 h1
    unfold stepFn
    simp only [if_neg hP, if_neg hQ, Set.indicator_apply, Set.mem_setOf_eq, if_pos (hI N), if_pos (hI N'), Pi.one_apply]

def colFn {G : GridData L sc} (B : Frames G) (t : T) (e : AE D) (j : ℕ) (ha : (G.V (.grid 0 j)).rank = D.R.r + j * D.R.t)
    (hb : (G.V (.grid 0 (j + 1))).rank = D.R.r + (j + 1) * D.R.t)
    (x : Mx D (G.V (.grid 0 (j + 1))).rank (G.V (.grid 0 j)).rank) : ℂ :=
  if IsHalf e x ∧ IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) then
    ∏ w ∈ locPl G t, stepFn L t w j
      (((fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))).map (cpt (D := D) w)).submatrix (ixOf G t w hb) (ixOf G t w ha))
  else 0

set_option maxHeartbeats 1000000 in
theorem isSBHalf_colFn (G : GridData L sc) (B : Frames G) {μ₀ : T} (hL : L.Is μ₀) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (j : ℕ) (hj : j < D.R.m) :
    IsSBHalf e (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _)
      fun _ => True) (colFn B t e j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj)) := by
  classical
  have hFS : IsFrame (B.β 0 j) (G.Λ (.grid 0 j)) := B.isFrame_β hL (Nat.zero_le _) hj.le
  have hFT : IsFrame (B.β 0 (j + 1)) (G.Λ (.grid 0 (j + 1))) := B.isFrame_β hL (Nat.zero_le _) hj
  obtain ⟨a, ha, h1⟩ := WeilOver.exists_hom_le (S := G.V (.grid 0 j)) (T := G.V (.grid 0 (j + 1)))
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ (node_isV G hL (X := .grid 0 j) ⟨Nat.zero_le _, hj.le⟩).sd)
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ (node_isV G hL (X := .grid 0 (j + 1)) ⟨Nat.zero_le _, hj⟩).sd)
  obtain ⟨b, hb, h2⟩ := WeilOver.exists_le_hom (S := G.V (.grid 0 j)) (T := G.V (.grid 0 (j + 1)))
    (GlobalTheory.DiagLiftFix.isLattice_of_isFrame hFS) (GlobalTheory.DiagLiftFix.isLattice_of_isFrame hFT)
  obtain ⟨e0, -, -⟩ := cpt_idemSum he
  set 𝔪 : Ideal (𝓞 D.host.E) := ∏ w ∈ locPl G t, w.asIdeal ^ 1 with h𝔪
  have hN : 0 < Ideal.absNorm 𝔪 :=
    Nat.pos_of_ne_zero fun h => CosSB.prod_pow_ne_bot (locPl G t) 1 (Ideal.absNorm_eq_zero_iff.1 h)
  have hle : ∀ w ∈ locPl G t, 𝔪 ≤ w.asIdeal ^ 1 := fun w hw =>
    Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Pl D.host.E => w.asIdeal ^ 1) hw)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = a * (b * Ideal.absNorm 𝔪) := ⟨_, rfl⟩
  refine ⟨fun x hx => ?_, K, by rw [hK]; positivity, fun u hu hh x => ?_, fun x hx => ?_⟩
  · by_contra h
    exact hx (by unfold colFn; rw [if_neg fun H => h H.1])
  · have hk : K • u ∈ hatMx (𝔪 • homLat (G.Λ (.grid 0 j)) (G.Λ (.grid 0 (j + 1)))) := by
      have := nsmul_mem (CosSB.nsmul_mem_hatMx h2 𝔪 hu) a
      rwa [smul_smul, ← hK] at this
    have hk2 := ((mem_hatMx_iff hFS hFT 𝔪 _).1 hk).2
    have hXYZ : fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D)) =
        fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) + fr (B.β 0 (j + 1)) (B.β 0 j) ((K • u).map (toEAf D)) := by
      have hm : (x + K • u).map (toEAf D) = x.map (toEAf D) + (K • u).map (toEAf D) := by
        ext i l
        exact (toEAf D).map_add _ _
      rw [hm, fr_add]
    have hZ : ∀ i l, fr (B.β 0 (j + 1)) (B.β 0 j) ((K • u).map (toEAf D)) i l ∈ OA D := fun i l => by
      obtain ⟨s, -, hs⟩ := hk2 i l
      rw [← hs]
      exact s.2
    have hint : IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D))) ↔
        IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) := by
      refine forall₂_congr fun i l => ?_
      rw [hXYZ, Matrix.add_apply]
      exact ⟨fun h => by simpa using sub_mem h (hZ i l), fun h => add_mem h (hZ i l)⟩
    unfold colFn
    split_ifs with H1 H2 H2
    · refine Finset.prod_congr rfl fun w hw => ?_
      let NX : Matrix (Fin (G.V (.grid 0 (j + 1))).rank) (Fin (G.V (.grid 0 j)).rank) (OA D) :=
        fun i l => ⟨_, H1.2 i l⟩
      let NY : Matrix (Fin (G.V (.grid 0 (j + 1))).rank) (Fin (G.V (.grid 0 j)).rank) (OA D) :=
        fun i l => ⟨_, H2.2 i l⟩
      have eX : (fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D))).map (cpt (D := D) w) = NX.map (cptO w) :=
        Matrix.ext fun i l => (cptO_apply w (NX i l)).symm
      have eY : (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))).map (cpt (D := D) w) = NY.map (cptO w) :=
        Matrix.ext fun i l => (cptO_apply w (NY i l)).symm
      rw [eX, eY]
      refine stepFn_congr_red' G hL t hj w _ _ NX NY (Matrix.ext fun i l => ?_)
      rw [Matrix.map_apply, Matrix.map_apply, ← sub_eq_zero, ← map_sub, (isRed w).ker, cptO_apply]
      obtain ⟨s, hs, hs'⟩ := hk2 i l
      have e3 : ((NX i l - NY i l : OA D) : EAf D) = s.1 := by
        rw [hs', AddSubgroupClass.coe_sub]
        change fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D)) i l -
          fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) i l = _
        rw [hXYZ, Matrix.add_apply, add_sub_cancel_left]
      rw [e3]
      exact (vEq w).lt_one_iff_lt_one.2 ((v_lt_one_iff _).2 (v_le_of_mem_idS (hle w hw) hs))
    · exact absurd ⟨(CosSB.isHalf_add_nsmul K hh).1 H1.1, hint.1 H1.2⟩ H2
    · exact absurd ⟨(CosSB.isHalf_add_nsmul K hh).2 H2.1, hint.2 H2.2⟩ H1
    · rfl
  · obtain ⟨hth, hti⟩ : IsHalf e x ∧ IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) := by
      by_contra h
      exact hx (by unfold colFn; rw [if_neg h])
    have hmem : x ∈ hatMx ((⊤ : Ideal (𝓞 D.host.E)) • homLat (G.Λ (.grid 0 j)) (G.Λ (.grid 0 (j + 1)))) := by
      refine (mem_hatMx_iff hFS hFT ⊤ _).2 ⟨fun i l => ?_, fun i l => ⟨⟨_, hti i l⟩, ?_, rfl⟩⟩
      · rw [← hth i l, map_mul, e0, zero_mul]
      · rw [idS, Ideal.map_top]
        exact Submodule.mem_top
    have := nsmul_mem (CosSB.nsmul_mem_latO h1 ⊤ hmem) (b * Ideal.absNorm 𝔪)
    rwa [smul_smul, mul_comm (b * Ideal.absNorm 𝔪) a, ← hK] at this

theorem givenFn_down_eq_colFn (G : GridData L sc) (B : Frames G) {μ₀ : T} (hL : L.Is μ₀) (t : T) (j : ℕ) (hj : j < D.R.m)
    (Φ : G.Datum) {e : AE D} (he : IsIdemSum e (locPl G t)) :
    GlobalTheory.FlipStart.givenFn B t Φ e (.down t 0 j) = colFn B t e j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj) := by
  have ha := GlobalTheory.FlipTop.rank_col G hj.le
  have hb := GlobalTheory.FlipTop.rank_col G hj
  obtain ⟨-, c1, c0⟩ := cpt_idemSum he
  funext x
  set N := fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) with hN
  have hsubm : ∀ w : Pl D.host.E, GlobalTheory.StepData.IntM ((N.map (cpt (D := D) w)).submatrix (ixOf G t w hb)
      (ixOf G t w ha)) ↔ GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := fun w =>
    ⟨fun h i l => by simpa using h ((ixOf G t w hb).symm i) ((ixOf G t w ha).symm l), fun h i l => h _ _⟩
  have hR : ∀ w, givenDatum t w B Φ (edgeOf (.down t 0 j)) (locArg B t w (.down t 0 j) x) =
      stepFn L t w j ((N.map (cpt (D := D) w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) := by
    intro w
    have hla : locArg B t w (.down t 0 j) x = B.coord t w (X := (0, j + 1)) (Y := (0, j)) ⟨Nat.zero_le _, hj⟩
        ⟨Nat.zero_le _, hj.le⟩ ((x.map (toEAf D)).map (cpt (D := D) w)) := by
      rw [Matrix.map_map]
      exact dif_pos ⟨Nat.zero_le _, hj⟩
    rw [hla]
    exact givenDatum_theta_coord B t w Φ hj ha hb (x.map (toEAf D))
  unfold GlobalTheory.FlipStart.givenFn colFn
  rw [Finset.prod_congr rfl fun w _ => hR w]
  by_cases hx : IsHalf e x
  swap
  · rw [if_neg hx, if_neg fun h => hx h.1]
  have hex : e • x = x := Matrix.ext fun p q => by rw [Matrix.smul_apply, smul_eq_mul]; exact hx p q
  have hNe : N = toEAf D e • N := by
    rw [hN, ← fr_smul]
    congr 1
    conv_lhs => rw [← hex]
    ext p q
    simp [Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul]
  have hint : IsIntM N ↔ ∀ w ∈ locPl G t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := by
    constructor
    · intro h w hw i l
      exact (vEq w).le_one_iff_le_one.2 ((mem_OA_iff _).1 (h i l) w)
    · intro h i l
      refine (mem_OA_iff _).2 fun w => ?_
      by_cases hw : w ∈ locPl G t
      · exact (vEq w).le_one_iff_le_one.1 (h w hw i l)
      · rw [hNe, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, c0 w hw, zero_mul]
        simp
  rw [if_pos hx]
  by_cases H : ∀ w ∈ locPl G t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w))
  · rw [if_pos ⟨hx, hint.2 H⟩]
  · rw [if_neg fun h => H (hint.1 h.2)]
    push_neg at H
    obtain ⟨w, hw, hn⟩ := H
    refine Finset.prod_eq_zero hw ?_
    by_contra h0
    exact hn ((hsubm w).1 (GlobalTheory.FunObj.LocTest.intM_of_stepFn t w j h0))

theorem isSBHalf_givenFn_down : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T},
    L.Is μ₀ → ∀ (t : T) (j : ℕ), j < D.R.m → ∀ (Φ : G.Datum) (e : AE D), IsIdemSum e (locPl G t) →
    IsSBHalf e (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _)
      fun _ => True) (GlobalTheory.FlipStart.givenFn B t Φ e (.down t 0 j)) := by
  intro D T L sc G B μ₀ hL t j hj Φ e he
  rw [givenFn_down_eq_colFn G B hL t j hj Φ he]
  exact isSBHalf_colFn G B hL t he j hj

end GlobalTheory.FlipStart.ColSB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenFnEqExtDat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun GlobalTheory.ChainCol
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Classical

noncomputable section

namespace GlobalTheory.ChainColRead

set_option maxHeartbeats 1000000 in
theorem givenFn_eq_extDat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T}, L.Is μ₀ → L.Pg ⊆ G.pl.W0 → ∀ (t : T) (j : ℕ), j + 1 < D.R.m → ∀ (Φ : G.Datum) (e e' : AE D), IsIdemSum e (locPl G t) → IsIdemSum e' (L.Pg ∪ L.Q t) → (∀ w ∈ locPl G t, w ∉ L.Pg ∪ L.Q t → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ x : WO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)), GlobalTheory.FlipStart.givenFn B t Φ e (.down t 0 j) x = extDat e e' (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _) fun _ => True) (stepDat (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (colFrame L j) (colFrame L (j + 1)) (colDat L t j) (L.chi (j + 1)) (L.xiR t) (L.Q t) e') x := by
  intro D T L sc G B μ₀ hL hPg t j hj1 Φ e e' he he' hAA x
  have hj : j < D.R.m := by omega
  have hsub : L.Pg ∪ L.Q t ⊆ locPl G t := by
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · exact Finset.mem_union_left _ (hPg h)
    · exact Finset.mem_union_right _ h
  obtain ⟨he₁, -⟩ := GlobalTheory.T.isIdemSum_sub_of_subset_and_orthogonal he he' hsub
  have h1 := GlobalTheory.PlaceDatum.idemSum_mul_self he'
  have h2 := GlobalTheory.PlaceDatum.idemSum_mul_self he₁
  obtain ⟨-, c1, c0⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he'
  obtain ⟨-, d1, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₁
  have ha := GlobalTheory.FlipTop.rank_col G hj.le
  have hb := GlobalTheory.FlipTop.rank_col G hj
  unfold GlobalTheory.FlipStart.givenFn extDat
  by_cases hx : IsHalf e x
  swap
  · rw [if_neg hx, if_neg fun h => hx h.1]
  rw [if_pos hx]
  set N := GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) with hN
  have hfr : ∀ a : AE D, GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) ((x.map (a * ·)).map (toEAf D)) = toEAf D a • N := by
    intro a
    rw [hN, ← GlobalTheory.FunObj.Comparison₂.fr_smul]
    congr 1
    ext p q
    simp [Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul]
  have hcomp : ∀ (a : AE D) (w : Pl D.host.E), cpt (D := D) w (toEAf D a) = 1 →
      (GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) ((x.map (a * ·)).map (toEAf D))).map (cpt (D := D) w) = N.map (cpt (D := D) w) := by
    intro a w hw
    rw [hfr]
    ext p q
    simp [Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul, hw]
  have hsubm : ∀ w : Pl D.host.E, GlobalTheory.StepData.IntM ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb)
      (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) ↔ GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := fun w =>
    ⟨fun h i l => by simpa using h ((GlobalTheory.FunObj.Comparison₂.ixOf G t w hb).symm i) ((GlobalTheory.FunObj.Comparison₂.ixOf G t w ha).symm l),
      fun h i l => h _ _⟩
  have hR : ∀ w, givenDatum t w B Φ (edgeOf (.down t 0 j)) (locArg B t w (.down t 0 j) x) =
      stepFn L t w j ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) := by
    intro w
    have hla : locArg B t w (.down t 0 j) x = B.coord t w (X := (0, j + 1)) (Y := (0, j)) ⟨Nat.zero_le _, hj⟩
        ⟨Nat.zero_le _, hj.le⟩ ((x.map (toEAf D)).map (cpt (D := D) w)) := by
      rw [Matrix.map_map]
      exact dif_pos ⟨Nat.zero_le _, hj⟩
    rw [hla]
    exact GlobalTheory.FunObj.Comparison₂.givenDatum_theta_coord B t w Φ hj ha hb (x.map (toEAf D))
  rw [Finset.prod_congr rfl fun w _ => hR w, ← Finset.prod_sdiff hsub]
  have hout : ∀ w ∈ locPl G t \ (L.Pg ∪ L.Q t), stepFn L t w j ((N.map (cpt (D := D) w)).submatrix
      (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) =
      if GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) then 1 else 0 := by
    intro w hw
    obtain ⟨-, hw2⟩ := Finset.mem_sdiff.1 hw
    have hP : w ∉ L.Pg := fun h => hw2 (Finset.mem_union_left _ h)
    have hQ : w ∉ L.Q t := fun h => hw2 (Finset.mem_union_right _ h)
    unfold stepFn
    rw [if_neg hP, if_neg hQ, Set.indicator_apply]
    exact if_congr (hsubm w) rfl rfl
  rw [Finset.prod_congr rfl hout, Finset.prod_boole]

  have hx1 : IsHalf (e - e') (x.map ((e - e') * ·)) := fun p q => by
    simp only [Matrix.map_apply, ← mul_assoc, h2]
  have hS : IsSelfDualC (G.pS (.mu t 0 j)) (G.latS (.mu t 0 j)) := (colY_isV D T L μ₀ hL j hj.le).sd
  have hT : IsSelfDualC (G.pT (.mu t 0 j)) (G.latT (.mu t 0 j)) := (colY_isV D T L μ₀ hL (j + 1) hj).sd
  have hAA' : ∀ w ∈ locPl G t \ (L.Pg ∪ L.Q t), ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := fun w hw =>
    hAA w (Finset.mem_sdiff.1 hw).1 (Finset.mem_sdiff.1 hw).2
  have hlat := GlobalTheory.T.mem_completedHomLattice_iff_integral_on_unit_half hS hT (B.isFrame_β hL (Nat.zero_le _) hj.le) (B.isFrame_β hL (Nat.zero_le _) hj) he₁ hAA'
    (x.map ((e - e') * ·)) hx1
  have k1 : x.map ((e - e') * ·) ∈ latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _)
      (G.latT (.mu t 0 j) : Set _) (fun _ => True) ↔
      ∀ w ∈ locPl G t \ (L.Pg ∪ L.Q t), GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := by
    rw [hlat]
    exact forall₂_congr fun w hw => by rw [hcomp _ w (d1 w hw)]

  have hint : IsIntM (toEAf D e' • N) ↔ ∀ w ∈ L.Pg ∪ L.Q t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := by
    constructor
    · intro h w hw i l
      have := (mem_OA_iff _).1 (h i l) w
      rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, c1 w hw, one_mul] at this
      exact (GlobalTheory.FunObj.Comparison₂.vEq w).le_one_iff_le_one.2 this
    · intro h i l
      refine (mem_OA_iff _).2 fun w => ?_
      rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]
      by_cases hw : w ∈ L.Pg ∪ L.Q t
      · rw [c1 w hw, one_mul]
        exact (GlobalTheory.FunObj.Comparison₂.vEq w).le_one_iff_le_one.1 (h w hw i l)
      · rw [c0 w hw, zero_mul]
        exact zero_mem _
  have hx0 : IsHalf e' (x.map (e' * ·)) := fun p q => by
    simp only [Matrix.map_apply, ← mul_assoc, h1]
  have hfrO : frMapO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (colFrame L j) (colFrame L (j + 1)) (x.map (e' * ·)) =
      toEAf D e' • N := hfr e'
  have k0 : stepDat (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (colFrame L j) (colFrame L (j + 1)) (colDat L t j)
      (L.chi (j + 1)) (L.xiR t) (L.Q t) e' (x.map (e' * ·)) = ∏ w ∈ L.Pg ∪ L.Q t, stepFn L t w j
      ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) := by
    unfold stepDat
    rw [hfrO]
    by_cases H : ∀ w ∈ L.Pg ∪ L.Q t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w))
    · rw [if_pos ⟨hx0, hint.2 H⟩]
      have key := GlobalTheory.FunObj.Comparison₂.omega_eq_prod_stepFn G t hL hj ha hb (r_le_colY L j) (toEAf D e' • N) (hint.2 H)
      refine key.trans (Finset.prod_congr rfl fun w hw => ?_)
      have e1 : (toEAf D e' • N).map (cpt (D := D) w) = N.map (cpt (D := D) w) := by
        rw [← hfr e']; exact hcomp e' w (c1 w hw)
      rw [e1]
    · rw [if_neg fun h => H (hint.1 h.2)]
      push_neg at H
      obtain ⟨w, hw, hn⟩ := H
      refine (Finset.prod_eq_zero hw ?_).symm
      by_contra h0
      exact hn ((hsubm w).1 (GlobalTheory.FunObj.LocTest.intM_of_stepFn t w j h0))
  rw [k0]
  by_cases hl : ∀ w ∈ locPl G t \ (L.Pg ∪ L.Q t), GlobalTheory.StepData.IntM (N.map (cpt (D := D) w))
  · rw [if_pos hl, one_mul, if_pos ⟨hx, k1.2 hl⟩]
  · rw [if_neg hl, zero_mul, if_neg fun h => hl (k1.1 h.2)]

end GlobalTheory.ChainColRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtExtDat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun GlobalTheory.ChainCol
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Classical

noncomputable section

namespace GlobalTheory.ExtDatTheta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {m n : ℕ}

theorem half_of_half {e e' : AE D} (h1 : e * e' = e') {x : Mx D m n} (hx : IsHalf e' x) : IsHalf e x := by
  intro i j
  rw [← hx i j, ← mul_assoc, h1]

theorem map_sub_half {e e' : AE D} (h1 : e * e' = e') (h2 : e' * e' = e') {x : Mx D m n} (hx : IsHalf e' x) :
    x.map ((e - e') * ·) = 0 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  rw [sub_mul, half_of_half h1 hx i j, hx i j, sub_self]

theorem map_half {e' : AE D} {x : Mx D m n} (hx : IsHalf e' x) : x.map (e' * ·) = x := by
  ext i j
  simp only [Matrix.map_apply]
  exact hx i j

theorem map_sub_eq {e e' : AE D} {u : Mx D m n} (hu : IsHalf e u) :
    u.map ((e - e') * ·) = u - u.map (e' * ·) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, sub_mul, hu i j]

theorem half_add_iff {e : AE D} {t x : Mx D m n} (hx : IsHalf e x) : IsHalf e (t + x) ↔ IsHalf e t := by
  constructor
  · intro h i j
    have h' := h i j
    rw [Matrix.add_apply, mul_add, hx i j] at h'
    exact add_right_cancel h'
  · intro h i j
    rw [Matrix.add_apply, mul_add, h i j, hx i j]

theorem map_add_mul (a : AE D) (t x : Mx D m n) : (t + x).map (a * ·) = t.map (a * ·) + x.map (a * ·) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, mul_add]

theorem mul_nsmul_comm' (a x : AE D) (k : ℕ) : a * (k • x) = k • (a * x) := by
  rw [nsmul_eq_mul, nsmul_eq_mul, mul_left_comm]

theorem map_add_nsmul (a : AE D) (t u : Mx D m n) (k : ℕ) :
    (t + k • u).map (a * ·) = t.map (a * ·) + k • u.map (a * ·) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, mul_add, mul_nsmul_comm']

theorem half_map_self {e' : AE D} (h2 : e' * e' = e') (t : Mx D m n) : IsHalf e' (t.map (e' * ·)) := by
  intro i j
  simp only [Matrix.map_apply]
  rw [← mul_assoc, h2]

def extL (e e' : AE D) (Λ : AddSubgroup (Mx D m n)) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun φ := GlobalTheory.ChainCol.extDat e e' Λ φ
  map_add' φ φ' := by
    funext t
    simp only [GlobalTheory.ChainCol.extDat, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c φ := by
    funext t
    simp only [GlobalTheory.ChainCol.extDat, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem extL_apply (e e' : AE D) (Λ : AddSubgroup (Mx D m n)) (φ : Mx D m n → ℂ) :
    extL e e' Λ φ = GlobalTheory.ChainCol.extDat e e' Λ φ := rfl

theorem extDat_trans {e e' : AE D} (h1 : e * e' = e') (h2 : e' * e' = e') (Λ : AddSubgroup (Mx D m n))
    (Φ : Mx D m n → ℂ) {x : Mx D m n} (hx : IsHalf e' x) :
    GlobalTheory.ChainCol.extDat e e' Λ (fun t => Φ (t + x)) = fun t => GlobalTheory.ChainCol.extDat e e' Λ Φ (t + x) := by
  funext t
  have hxe : IsHalf e x := half_of_half h1 hx
  simp only [GlobalTheory.ChainCol.extDat, half_add_iff hxe, map_add_mul, map_sub_half h1 h2 hx, add_zero, map_half hx]

theorem extDat_sb {e e' : AE D} (h1 : e * e' = e') (h2 : e' * e' = e') (Λ : AddSubgroup (Mx D m n))
    (hstab : ∀ u ∈ Λ, u.map (e' * ·) ∈ Λ) {Φ : Mx D m n → ℂ} (hΦ : IsSBHalf e' Λ Φ) :
    IsSBHalf e Λ (GlobalTheory.ChainCol.extDat e e' Λ Φ) := by
  unfold IsSBHalf at hΦ ⊢
  obtain ⟨-, k, hk, hper, hlat⟩ := hΦ
  refine ⟨fun t ht => ?_, k, hk, fun u hu hue t => ?_, fun t ht => ?_⟩
  · by_contra hn
    apply ht
    simp only [GlobalTheory.ChainCol.extDat]
    exact if_neg fun hc => hn hc.1
  · have hku : IsHalf e (k • u) := fun i j => by rw [Matrix.smul_apply, mul_nsmul_comm', hue i j]
    have hsu : u.map ((e - e') * ·) ∈ Λ := by
      rw [map_sub_eq hue]
      exact sub_mem hu (hstab u hu)
    have hmem : (t + k • u).map ((e - e') * ·) ∈ Λ ↔ t.map ((e - e') * ·) ∈ Λ := by
      rw [map_add_nsmul]
      exact add_mem_cancel_right (nsmul_mem hsu k)
    have hval : Φ ((t + k • u).map (e' * ·)) = Φ (t.map (e' * ·)) := by
      rw [map_add_nsmul]
      exact hper _ (hstab u hu) (half_map_self h2 u) _
    simp only [GlobalTheory.ChainCol.extDat, half_add_iff hku, hmem, hval]
  · have hc : IsHalf e t ∧ t.map ((e - e') * ·) ∈ Λ := by
      by_contra hn
      apply ht
      simp only [GlobalTheory.ChainCol.extDat]
      exact if_neg hn
    have hΦt : Φ (t.map (e' * ·)) ≠ 0 := by
      intro h0
      apply ht
      simp only [GlobalTheory.ChainCol.extDat]
      rw [if_pos hc, h0]
    have hsplit : t = t.map (e' * ·) + t.map ((e - e') * ·) := by
      rw [map_sub_eq hc.1]
      abel
    rw [hsplit, nsmul_add]
    exact add_mem (hlat _ hΦt) (nsmul_mem hc.2 k)

theorem symplO_map_eq {S T : HSp D} {e e' : AE D} (h1 : e * e' = e') (h2 : e' * e' = e')
    {t y : WO S T} (ht : IsHalf e t) (hy : IsHalf (cA D e') y) :
    symplO S T (t.map (e' * ·)) y = symplO S T t y := by
  unfold symplO hO
  congr 2
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  have hyc : cA D (y c b) = e' * cA D (y c b) := by
    conv_lhs => rw [← hy c b]
    rw [map_mul, Formalism.IndefR.Fin.cA_cA]
  rw [Matrix.map_apply]
  calc _ = incA D ((HSpace.gram S)⁻¹ a b) * (e' * cA D (y c b)) * incA D (HSpace.gram T c d) * t d a := by ring
    _ = _ := by rw [← hyc]

theorem extDat_modul {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) {e e' : AE D} (h1 : e * e' = e')
    (h2 : e' * e' = e') (Λ : AddSubgroup (WO S T)) (Φ : WO S T → ℂ) {y : WO S T} (hy : IsHalf (cA D e') y) :
    GlobalTheory.ChainCol.extDat e e' Λ (fun t => ψ (symplO S T t y) * Φ t) =
      fun t => ψ (symplO S T t y) * GlobalTheory.ChainCol.extDat e e' Λ Φ t := by
  funext t
  simp only [GlobalTheory.ChainCol.extDat]
  split_ifs with hc
  · rw [symplO_map_eq h1 h2 hc.1 hy]
  · rw [mul_zero]

theorem extDat_halfInd {e e' : AE D} (h2 : e' * e' = e') (Λ : AddSubgroup (Mx D m n))
    (hstab : ∀ u ∈ Λ, u.map (e' * ·) ∈ Λ) :
    GlobalTheory.ChainCol.extDat e e' Λ ((1 : ℂ) • halfInd e' Λ) = (1 : ℂ) • halfInd e Λ := by
  unfold halfInd
  rw [one_smul, one_smul]
  funext t
  simp only [GlobalTheory.ChainCol.extDat]
  by_cases ht : IsHalf e t
  · have hsplit : t = t.map (e' * ·) + t.map ((e - e') * ·) := by
      rw [map_sub_eq ht]
      abel
    have hiff : t ∈ Λ ↔ t.map ((e - e') * ·) ∈ Λ ∧ t.map (e' * ·) ∈ Λ := by
      constructor
      · intro h
        refine ⟨?_, hstab t h⟩
        rw [map_sub_eq ht]
        exact sub_mem h (hstab t h)
      · rintro ⟨ha, hb⟩
        rw [hsplit]
        exact add_mem hb ha
    by_cases hA : t.map ((e - e') * ·) ∈ Λ <;> by_cases hB : t.map (e' * ·) ∈ Λ <;>
      simp [ht, hA, hB, hiff, half_map_self h2 t]
  · simp [ht]

theorem isThetaAt_extDat : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {f₀ φ f : WO S T → ℂ} {e e' : AE D} {P P' : Finset (Pl D.host.E)}, IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsVacO ψ θ S T sS sT ΛS ΛT f₀ → IsIdemSum e P → IsIdemSum e' P' → P' ⊆ P → IsThetaAt ψ (symplO S T) (heisO ψ S T) e' (latO S T ΛS ΛT fun _ => True) 1 f₀ φ f → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ (extDat e e' (latO S T ΛS ΛT fun _ => True) φ) f := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ φ f e e' P P' hS hT hV he he' hP h
  unfold IsThetaAt at h ⊢
  obtain ⟨-, hall⟩ := h
  obtain ⟨hstd, hvac⟩ := hV
  have h1 : e * e' = e' := GlobalTheory.Tow.idemSum_mul_of_subset he' he hP
  have h2 : e' * e' = e' := GlobalTheory.Tow.idemSum_mul_of_subset he' he' (Finset.Subset.refl _)
  have hstab : ∀ u ∈ (latO S T ↑ΛS ↑ΛT fun _ => True),
      u.map (e' * ·) ∈ (latO S T ↑ΛS ↑ΛT fun _ => True) := by
    intro u hu
    have hsm : u.map (e' * ·) = e' • u := by
      ext i j
      simp [Matrix.smul_apply, smul_eq_mul]
    rw [hsm]
    exact GlobalTheory.PlaceModelSum.idem_smul_latO h2 hu
  have hce : cA D e * cA D e' = cA D e' := by
    rw [← map_mul (cA D), h1]
  refine ⟨?_, fun Tm hTm => ?_⟩
  · have hlv : IsLatVac (heisO ψ S T) (latO S T ↑ΛS ↑ΛT fun _ => True) f₀ := hvac.lat
    have hec : e * cA D e = 0 := by
      unfold IsIdemSum at he
      exact he.2
    exact GlobalTheory.PlaceModelSum.IsOrthSum.exists_model hstd hS hT
      (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he) hec hlv
  · have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e' (latO S T ↑ΛS ↑ΛT fun _ => True) 1 f₀
        (Tm ∘ₗ extL e e' (latO S T ↑ΛS ↑ΛT fun _ => True)) := by
      obtain ⟨htr, hmo, hva⟩ := hTm
      refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
      · simp only [LinearMap.comp_apply, extL_apply]
        rw [extDat_trans h1 h2 _ Φ hx]
        exact htr _ (extDat_sb h1 h2 _ hstab hΦ) x (half_of_half h1 hx)
      · simp only [LinearMap.comp_apply, extL_apply]
        rw [extDat_modul ψ h1 h2 _ Φ hy]
        exact hmo _ (extDat_sb h1 h2 _ hstab hΦ) y (half_of_half hce hy)
      · simp only [LinearMap.comp_apply, extL_apply]
        rw [extDat_halfInd h2 _ hstab]
        exact hva
    rw [hall _ hT', LinearMap.comp_apply, extL_apply]

end GlobalTheory.ExtDatTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesSubsetChosenPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun GlobalTheory.ChainCol
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Classical

namespace GlobalTheory.LevelPlacesChosen

theorem levelPlaces_subset_chosenPlaces : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T},
    L.Is μ₀ → L.Pg ⊆ G.pl.W0 := by
  intro D T L sc G μ₀ hμ P hP
  obtain ⟨k, hk⟩ := (hμ.Pg P).1 hP
  have hK : P.under (𝓞 D.host.K) = L.C.P.pb k := hk
  have hgE : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (P.under (𝓞 D.host.K)).asIdeal := by
      rw [hK]; exact L.C.P.pb_over k
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal := h1
    rwa [map_natCast] at h2
  have hgF : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ P.asIdeal
    rw [map_natCast]; exact hgE
  have hS1 : P.under (𝓞 D.host.F) ∈ S1 D := by
    rw [S1_mem_OmF]
    fin_cases k
    · exact Or.inl hgF
    · exact Or.inr (Or.inl hgF)
  have hS0 : P.under (𝓞 D.host.F) ∈ insert G.pl.v0 (S1 D) := Finset.mem_insert_of_mem hS1
  have hwPg : G.pl.w (P.under (𝓞 D.host.F)) ∈ L.Pg := G.pl.w_g _ k hgF
  have hover : (G.pl.w (P.under (𝓞 D.host.F))).under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := G.pl.w_over _ hS0
  have heq : G.pl.w (P.under (𝓞 D.host.F)) = P := by
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hover with h | h
    · exact h
    · exact absurd ((GlobalTheory.GoodPrimes.isConjPl_iff).2 h)
        (GlobalTheory.TypePlaces.not_isConjPl L.C.P L.Pg hμ.Pg P hP _ hwPg)
  unfold Places.W0
  exact Finset.mem_image.2 ⟨_, hS0, heq⟩

end GlobalTheory.LevelPlacesChosen
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainCol

noncomputable section

namespace GlobalTheory.ChainCol

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem locVec_col {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {large₂ : SizeData₂ D}
    (s : HidaSetting large₂ R F) (ch : Choice R) (hch : ch.Is) (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j))
    (hj : (j : ℕ) + 1 < D.R.m) (hg : HEq g (R.vY t j)) (e : AE D) (he : IsIdemSum e (locPl ch.G t)) (Φ : ch.G.Datum) :
    IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) (((1 : ℂˣ) : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) g := by
  classical
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hv := s.core.chain.vY t j hj
  have hvac := hch.vac.1 j hj
  have hw := hch.weil
  obtain ⟨hX1, hX2⟩ := lsp_heq (colY_lt R.toLevCh (j.2 : (j : ℕ) < D.R.m))
  obtain ⟨hY1, hY2⟩ := lsp_heq (colY_lt R.toLevCh hj)
  have hv' : IsStepVecOf R.ψ R.θ (columnBlock R.toLevCh j).sp (columnBlock R.toLevCh (j + 1)).sp (ch.W.cart (.grid 0 j))
      (ch.W.cart (.grid 0 (j + 1))) (columnBlock R.toLevCh j).lat (columnBlock R.toLevCh (j + 1)).lat (colFrame R.toLevCh j)
      (colFrame R.toLevCh (j + 1)) (colDat R.toLevCh t j) (R.chi (j + 1)) (R.Q t) (R.xiR t) (ch.rm.vT 0 j) g :=
    stepVec_congr hX1.symm hY1.symm (hw.cartY j j.2).symm (hw.cartY (j + 1) hj).symm hX2.symm hY2.symm
      (colFrame_lt R.toLevCh j.2).symm (colFrame_lt R.toLevCh hj).symm
      (datY_heq (congrArg (fun V : HSp D => V.rank) hX1.symm) _ _ _ _ _ _ _ _ _ _ _) hvac.symm hg.symm hv
  obtain ⟨hf₀, e', he', hθ'⟩ := hv'
  have hsd := fun k (hk : k ≤ D.R.m) => (colY_isV D T R.toLevCh A.μ0 hL k hk).sd
  have hPg := GlobalTheory.LevelPlacesChosen.levelPlaces_subset_chosenPlaces ch.G hL
  have h1 := GlobalTheory.ExtDatTheta.isThetaAt_extDat (hsd j j.2.le) (hsd (j + 1) hj.le) hf₀ he he' ?_ hθ'
  swap
  · intro x hx
    unfold locPl
    rcases Finset.mem_union.1 hx with h | h
    · exact Finset.mem_union.2 (Or.inl (hPg h))
    · exact Finset.mem_union.2 (Or.inr h)
  have hAA : ∀ w ∈ locPl ch.G t, w ∉ R.toLevCh.Pg ∪ R.toLevCh.Q t →
      ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
        ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
    intro w hw _
    have hb := GlobalTheory.FunObj.Good.badInt_notMem hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hch.guard t) hw
    have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
    have hN := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
    refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_le_one_of_mem h2q (Or.inl ha)
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_nat hN
  have h3 := funext (GlobalTheory.ChainColRead.givenFn_eq_extDat ch.G ch.S.B hL hPg t j hj Φ e e' he he' hAA)
  refine ⟨?_, ?_⟩
  · rw [Units.val_one, one_smul]
    exact GlobalTheory.FlipStart.ColSB.isSBHalf_givenFn_down ch.G ch.S.B hL t j j.2 Φ e he
  · rw [Units.val_one, one_smul, h3, hw.ψ]
    exact h1

end GlobalTheory.ChainCol
