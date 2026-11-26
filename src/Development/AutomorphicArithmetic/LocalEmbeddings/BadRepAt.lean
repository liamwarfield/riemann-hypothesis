module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeOfDetEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverCuspFormPullbackInjectiveDescent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerSemilinear

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.LocalEmbeddings.RankCover
section -- merged from Development.AutomorphicArithmetic.LocalEmbeddings.KeepsOfGood
section -- merged from Development.AutomorphicArithmetic.LocalEmbeddings.RootInCore
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.BadRep

section Forms

open NumberField Formalism.BasicNotions _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.LevPull (CongMod)
open GlobalTheory.LevDesc (transl)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBC


set_option maxHeartbeats 1000000 in
theorem pull_data : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o →
    ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (G : Type) [Group G]
    (lev : G → (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La),
    ActLev (Xo := T.Q.Xo j) T.Q.c (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))) →
    (∀ g, ∀ f ∈ T.cuspA j a n, actLev (Xo := T.Q.Xo j) T.Q.c (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))) g f ∈ T.cuspA j a n) →
    ∀ (θ : LevelAut (T.Q.Dw j) Y.d.l₂ →* G), (∀ γ, CongMod T.Q.l.Mb (liftLa γ) (lev (θ γ))) →
    ∃ π : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n) →ₛₗ[((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle))] Y.V (wtZ a n),
      (∀ (m : ℕ) (b : Fin m → cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)), LinearIndependent T.Q.c.F b →
        LinearIndependent Y.d.c₂.F fun k => π (b k)) ∧
      (∀ γ (v : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)), ∃ hv : actLev (Xo := T.Q.Xo j) T.Q.c (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))) (θ γ) v ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n),
        transl Y.d.Xo₂ Y.d.c₂ γ (π v) = π ⟨_, hv⟩) ∧
      (∀ g : Y.V (wtZ a n), (∀ γ, CongMod T.Q.l.Mb (liftLa γ) LinearMap.id → transl Y.d.Xo₂ Y.d.c₂ γ g = g) →
        g ∈ Submodule.span Y.d.c₂.F (Set.range π)) := by
  intro D T j Y e o hT hj hG a n hD G _ lev hact hkeep θ hθ
  obtain ⟨hL₂, hgal, hP⟩ := GlobalTheory.DeepLaws.laws_galois_pull D T j Y e o hT hj hG hG.unit hG.modelW
  have hL := (GlobalTheory.LevGeo.laws_of_coreJ D T j hT hj).1
  have hpq : (T.Q.Dw j).p ≠ (T.Q.Dw j).q ∧ 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  obtain ⟨π, p1, p2, -, -, p5, -⟩ := GlobalTheory.T.levelCover_cuspForm_pullback_injective_descent D j _ _ _ _ _ Y.c' Y.hle _ _ Y.d _ _ hL hL₂ hG.lev.1 hgal a n hD hD.2
  have hC : ∀ {f}, f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n) ↔ f ∈ T.cuspA j a n := fun {f} => by rw [cuspW_wtZ]
  have s₁ : ∀ {f}, f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n) → f ∈ sec (T.Q.Xo j) T.Q.c a n :=
    fun h => cusp_le_sec _ _ _ a n (hC.1 h)
  have s₂ : ∀ {f}, f ∈ Y.V (wtZ a n) → f ∈ sec Y.d.Xo₂ Y.d.c₂ a n := fun h => by
    rw [Deep.V, cuspW_wtZ] at h
    exact cusp_le_sec _ _ _ a n h
  have hact₂ : ActLev (Xo := Y.d.Xo₂) Y.d.c₂ (GlobalTheory.FormTies.levFull (T.Q.Dw j) Y.d.l₂) :=
    GlobalTheory.FullLevelAction.actLaws_levFull Y.d.Xo₂ Y.d.c₂ hpq.2 (hG.lev.2 ▸ Nat.coprime_one_left _)
  obtain ⟨hact', hbc⟩ := GlobalTheory.FieldBC.actLev_and_actBC D _ _ _ _ _ Y.c' Y.hle G _ hact
  have hO : GlobalTheory.CoverSec.AllOver Y.d := GlobalTheory.CoverSec.allOver_of_overBase Y.d hG.lev.1.1.2.2
    (GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq.1 hL.levA Y.d)
  have geo : ∀ {f f' : Rul (T.Q.Xo j) Y.c'} {u u' : Rul Y.d.Xo₂ Y.d.c₂}, GlobalTheory.LevPull.Pull Y.d f u → GlobalTheory.LevPull.Pull Y.d f' u' →
      f = f' → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra Y.d.c₂.F k] (y : FrPt Y.d.Xo₂ Y.d.c₂ k),
        evR Y.d.Xo₂ Y.d.c₂ u y = evR Y.d.Xo₂ Y.d.c₂ u' y := by
    rintro f _ u u' h h' rfl k _ _ _ y₂
    letI := GlobalTheory.CoverSec.algBelow Y.d k
    obtain ⟨y, hy⟩ := GlobalTheory.CoverSec.exists_frOver_below Y.d (fun _ => rfl) y₂ (hO k (fun _ => rfl) y₂)
    rw [h k (fun _ => rfl) y₂ y hy, h' k (fun _ => rfl) y₂ y hy]
  let act := actLev (Xo := T.Q.Xo j) T.Q.c (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)))
  let π' := (Y.V (wtZ a n)).subtype.comp π
  have hc : ∀ γ (v : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)) (hv : act (θ γ) v ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)),
      (transl Y.d.Xo₂ Y.d.c₂ γ).toLinearMap (π' v) = π' ⟨_, hv⟩ := by
    intro γ v hv'
    have hv := ((GlobalTheory.T.ruleBaseChange_section_values_semilinear _ _ _ _ _ _ _ Y.hle).1 a n _ (s₁ v.2)).1
    have h1 := GlobalTheory.LevPullEquiv.pull_actLev D j _ _ _ _ _ Y.d hpq.2 hG.lev.1 hG.lev.2
      (GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq.1 hL.levA Y.d) G _ lev liftLa hact' hact₂ (θ γ) γ (hθ γ) a n _ hv _
      (s₂ (π v).2) (p1 v)
    refine GlobalTheory.CoverSec.eq_of_geometric (GlobalTheory.LevelEquivCompare.actLev_mem_sec hact₂ γ (s₂ (π v).2)).1 (s₂ (π _).2).1 (geo h1 (p1 ⟨_, hv'⟩) ?_)
    refine GlobalTheory.CoverSec.eq_of_geometric (GlobalTheory.LevelEquivCompare.actLev_mem_sec hact' _ hv).1
      ((GlobalTheory.T.ruleBaseChange_section_values_semilinear _ _ _ _ _ _ _ Y.hle).1 a n _ (s₁ hv')).1.1 fun k _ _ _ y => ?_
    letI := resAlg Y.hle k
    exact (hbc a n (θ γ) 1 _ _ _ hv (fun _ => s₁ v.2) (GlobalTheory.LevelEquivCompare.isBC_rulBC Y.hle (s₁ v.2)) k (fun _ => rfl) y).trans
      (GlobalTheory.LevelEquivCompare.isBC_rulBC Y.hle (s₁ hv') k (fun _ => rfl) y).symm
  refine ⟨π, fun m b hb => p2 m b hb, fun γ v => ⟨hC.2 (hkeep _ _ (hC.1 v.2)), hc γ v _⟩, fun g hg => ?_⟩
  have h1 : GlobalTheory.LevPull.FibConst Y.d g := by
    refine (GlobalTheory.T.fibreConstant_iff_coveringGroup_invariant D j _ _ _ _ _ Y.d hpq.2 hG.lev.1 hG.lev.2 (Or.inl ⟨hpq.1, hL.levA⟩) liftLa (fun γ => LinearMap.ext (liftLa_spec γ)) a n g
      (s₂ g.2)).2 fun γ hγ => hg γ hγ
  exact (p5 g).2 h1

end Forms

section Point

open NumberField Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Pj _root_.Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.BadCount
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed typeEmb grpHR grpGHR transl)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU unitri superDiag)
open GlobalTheory.LevPull (CongMod)
open Formalism.MainNotions.ArithmeticCylinders
open scoped TensorProduct

theorem isUniUp_iff {k : Type} [Field k] {r : ℕ} (g : GL (Fin r) k) :
    IsUniUp (g : Matrix (Fin r) (Fin r) k) ↔ g ∈ unitri r k :=
  ⟨fun h => ⟨fun a b hab => (h a b).1 hab, fun a => (h a a).2 rfl⟩,
    fun h a b => ⟨fun hab => h.1 hab, fun e => e ▸ h.2 a⟩⟩

theorem sum_entN {k : Type} [Field k] {r : ℕ} (M : Matrix (Fin r) (Fin r) k) :
    ∑ i ∈ Finset.range (r - 1), entN M i (i + 1) = superDiag M := by
  have h1 : ∀ i : Fin r, (∑ j : Fin r, if j.val = i.val + 1 then M i j else 0) = entN M i (i + 1) := by
    intro i
    unfold entN
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨i.val + 1, h.2⟩ (fun b _ hb => if_neg fun e => hb (Fin.ext e)) (by simp)]
      simp
    · refine Finset.sum_eq_zero fun j _ => if_neg fun e => h ⟨i.2, by have := j.2; omega⟩
  rw [superDiag, Finset.sum_congr rfl fun i _ => h1 i, Fin.sum_univ_eq_sum_range (fun i => entN M i (i + 1)) r]
  refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.sub_le r 1)) fun x hx hx' => ?_
  simp only [Finset.mem_range] at hx hx'
  unfold entN
  rw [dite_eq_right]
  omega

theorem root_in_core {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (k : Fin 2) :
    ∃ ζ : p.T.Q.c.F, IsPrimitiveRoot ζ (D.host.g k) := by
  have hN0 : p.T.Q.l.M' ≠ 0 := Nat.lcm_ne_zero (by have := p.T.Q.l.three_le; omega) p.T.Q.l.A_pos.ne'
  have hM : p.T.Q.l.M = D.host.g 0 * D.host.g 1 := p.fw.laws.pins.2.1.1
  have hz : IsPrimitiveRoot (⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta p.T.Q.l.M', p.T.Q.c.zeta_mem⟩ : p.T.Q.c.F) p.T.Q.l.M' :=
    IsPrimitiveRoot.of_map_of_injective (f := p.T.Q.c.F.val) (Complex.isPrimitiveRoot_exp _ hN0) Subtype.val_injective
  obtain ⟨c, hc⟩ : D.host.g k ∣ p.T.Q.l.M' :=
    dvd_trans (hM ▸ GlobalTheory.LevDesc.g_dvd k) (Nat.dvd_lcm_left p.T.Q.l.M p.T.Q.l.A)
  exact ⟨_, hz.pow (Nat.pos_of_ne_zero hN0) (hc.trans (mul_comm _ _))⟩

theorem idx_eq {D : D7} {k k' : Fin 2} {X X' : Type} [Semiring X] [Semiring X'] (e : ZMod (D.host.g k) ≃+* X)
    (e' : ZMod (D.host.g k') ≃+* X') (hX : Nat.card X = Nat.card X') : k = k' := by
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  haveI : NeZero (D.host.g k') := ⟨(D.host.g_prime k').ne_zero⟩
  have h : D.host.g k = D.host.g k' := by
    rw [← Nat.card_zmod (D.host.g k), ← Nat.card_zmod (D.host.g k'), Nat.card_congr e.toEquiv, Nat.card_congr e'.toEquiv, hX]
  fin_cases k <;> fin_cases k'
  · rfl
  · exact absurd h D.host.g_ne
  · exact absurd h.symm D.host.g_ne
  · rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}


set_option maxHeartbeats 1000000 in
theorem frame_data (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i) {e : ℕ} {o : ℝ} (hY : Y.Good e o) :
    ∃ (fr : TypeFrame (dat p i) Y.d.l₂) (ε : Sq D.host ≃ p.R.toRealDat.Pg) (iso' : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (ε v).1)
      (t : LevelGroup D.host ≃* p.P.Gp), IsTypeLevel Y.d.l₂ ∧
      (∀ γ, CongMod p.T.Q.l.Mb (liftLa γ) ((p.O i).lev (t (typeRed fr γ)))) ∧
      (∀ γ, CongMod p.T.Q.l.Mb (liftLa γ) LinearMap.id → typeRed fr γ = 1) ∧
      (∀ u v, p.R.toRealDat.eG (t u) (ε v) = Formalism.UG.bc (iso' v : ZMod (D.host.g v.1) →+* kP (ε v).1) (u v)) ∧
      (∀ u, t u ∈ (p.F.lv2.lvl false).P ↔ u ∈ levelU D.host) := by
  have hJ := p.fw.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.succ_pos _, i.2⟩
  have hM : p.T.Q.l.M = D.host.g 0 * D.host.g 1 := hJ.pins.2.1.1
  have hA : p.T.Q.l.A = 1 := hJ.pins.2.1.2
  have hl₂ : IsTypeLevel Y.d.l₂ :=
    (GlobalTheory.LevDesc.isTypeLevel_of_eq hY.lev.2 (hY.lev.1.2.1.trans (by rw [hM])) (hM ▸ hY.lev.1.2.2.1.symm)).1
  have hMb := ((p.pins i).2.tuple ()).half.1
  have hr : (dat p i).p + (dat p i).q = D.R.r := (GlobalTheory.Member.exists_iotaOK D p.T.Q hJ.pins _ hj).2.1
  have hle : Y.d.l₂.Mb ≤ p.T.Q.l.Mb := hY.lev.1.2.2.2.1.le.trans Ideal.mul_le_left
  obtain ⟨fr, ε, iso, h1, h2⟩ := GlobalTheory.T.exists_typeFrame_cover_levelMaps_reductions D _ _ _ _ _ p.R.toRealDat i (p.charW.base.lev.βW i) _ (dat p i) _ Y.d.l₂ _
    (GlobalTheory.LevelAction.latEmb_iotaW p.T hJ i) hr hA hM hl₂ hle hMb _ (p.pins i).2.lift.lev
  obtain ⟨t, ψ, t1, t2, t3, t4⟩ := GlobalTheory.TypeBase.base_level_unip_char D _ _ _ _ _ p.R.toRealDat p.F.lv2 p.charW.base.grp.levels p.charW.base.grp.chiW
    (root_in_core p) ε iso
  exact ⟨fr, ε, iso, t, hl₂, fun γ => h1 γ _ (t1 _), h2, t1, t3⟩

end Point

end GlobalTheory.CovTop.BadRep
end
end

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.BadRep

open NumberField Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Pj _root_.Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.BadCount
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed typeEmb grpHR grpGHR transl levelGU)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU unitri superDiag)
open GlobalTheory.LevPull (CongMod)
open Formalism.MainNotions.ArithmeticCylinders
open scoped TensorProduct

section Group

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 1000000 in
theorem whit_data (R : RealDat D A Ks) (F : Face D A) (hlevels : R.grp_levels F) (c : G ≃* G0g D.nd)
    (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1)
    (hpin : ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (c g kv)) :
    ∃ (Pb : Subgroup (G0g D.nd)) (lam : Pb →* ℂˣ)
      (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), IsWhit D Pb lam ψ ∧
      (∀ g, c g ∈ Pb ↔ g ∈ (F.lvl false).P) ∧
      ∀ g (h : c g ∈ Pb) (h' : g ∈ (F.lvl false).P), ((lam ⟨c g, h⟩ : ℂˣ) : ℂ) =
        D.what₂.embLL (((F.lvl false).ψ⁻¹ ⟨g, h'⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
  classical
  obtain ⟨ψ0, hgen, hlev, -⟩ := hlevels
  let P := (F.lvl false).P
  let Pb : Subgroup (G0g D.nd) := P.map c.toMonoidHom
  have hPb : ∀ g, g ∈ Pb ↔ c.symm g ∈ P := fun g => Subgroup.mem_map_equiv
  let toP : Pb →* P := (c.symm.toMonoidHom.comp Pb.subtype).codRestrict P fun x => (hPb x).1 x.2
  let lam : Pb →* ℂˣ := (Units.map (D.what₂.embLL : D.what₂.LL →* ℂ)).comp ((F.lvl false).ψ⁻¹.comp toP)
  let ψC : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ := fun kv =>
    (ψ0 (plg kv).1).compAddMonoidHom ((iso kv).toAddMonoidHom.comp (-AddMonoidHom.id _))
  have hmemP : ∀ x : G, x ∈ P ↔ ∀ kv, c x kv ∈ unitri D.R.r (ZMod (D.host.g kv.1)) := by
    intro x
    have e1 : x ∈ P ↔ R.eG x ∈ (R.levR F false).H := by
      show _ ↔ R.eG.symm (R.eG x) ∈ P
      rw [MulEquiv.symm_apply_apply]
    rw [e1, hlev, GlobalTheory.TypeBase.mem_lastZeroOrthImageSubspace_iff, ← plg.forall_congr_right]
    refine forall_congr' fun kv => ?_
    rw [hpin, GlobalTheory.TypeBase.bc_mem_unip_iff]
  refine ⟨Pb, lam, ψC, ⟨fun kv h => hgen (plg kv).1 (plg kv).2 (AddChar.ext _ _ fun y => ?_), fun g => ?_, fun g => ?_⟩,
    fun g => by rw [hPb, MulEquiv.symm_apply_apply], fun g h h' => ?_⟩
  · obtain ⟨x, rfl⟩ := (iso kv).surjective y
    have := DFunLike.congr_fun h (-x)
    simpa [ψC] using this
  · rw [hPb, hmemP]
    refine forall_congr' fun kv => ?_
    rw [MulEquiv.apply_symm_apply, isUniUp_iff]
  · have hx : c.symm (g : G0g D.nd) ∈ P := (hPb _).1 g.2
    have hxH : R.eG (c.symm g) ∈ (R.levR F false).H := by
      show R.eG.symm (R.eG _) ∈ P
      rw [MulEquiv.symm_apply_apply]
      exact hx
    have e1 : (R.levR F false).chi ⟨_, hxH⟩ = Units.map (D.what₂.embLL : D.what₂.LL →* ℂ)
        ((F.lvl false).ψ ⟨R.eG.symm (R.eG (c.symm g)), hxH⟩) := rfl
    rw [show (⟨R.eG.symm (R.eG (c.symm g)), hxH⟩ : P) = ⟨c.symm g, hx⟩ from
      Subtype.ext (MulEquiv.symm_apply_apply _ _)] at e1
    have key : ∀ X : LevelP R.Pg D.R.r ℂ, X = P0 R.Pg D.R.r ψ0 → ∀ y (hy : y ∈ X.H),
        ((X.chi ⟨y, hy⟩ : ℂˣ) : ℂ) = ∏ PP : R.Pg, ψ0 PP.1 (edgeSum supEdge (y PP)) := by
      rintro X rfl y hy
      exact GlobalTheory.TypeBase.baseLevelCharacter_eq_prod_superdiagonalSum _ _ _ y hy
    have h3 := key _ hlev _ hxH
    rw [e1] at h3
    have ht : toP g = ⟨c.symm g, hx⟩ := rfl
    show ((Units.map (D.what₂.embLL : D.what₂.LL →* ℂ) ((F.lvl false).ψ⁻¹ (toP g)) : ℂˣ) : ℂ) = _
    rw [ht, MonoidHom.inv_apply, map_inv, Units.val_inv_eq_inv_val, h3, ← plg.prod_comp, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [hpin, MulEquiv.apply_symm_apply, GlobalTheory.TypeBase.edgeSum_bc, sum_entN]
    show _ = ψ0 (plg kv).1 ((iso kv) (-(superDiag _)))
    rw [map_neg, AddChar.map_neg_eq_inv]
    rfl
  · have ht : toP ⟨c g, h⟩ = ⟨g, h'⟩ := Subtype.ext (c.symm_apply_apply g)
    show ((Units.map (D.what₂.embLL : D.what₂.LL →* ℂ) ((F.lvl false).ψ⁻¹ (toP ⟨c g, h⟩)) : ℂˣ) : ℂ) = _
    rw [ht]
    rfl


set_option maxHeartbeats 1000000 in
theorem half_data (R : RealDat D A Ks) (c : G ≃* G0g D.nd)
    (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1)
    (hpin : ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (c g kv))
    (ε : Sq D.host ≃ R.Pg) (iso' : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (ε v).1) (t : LevelGroup D.host ≃* G)
    (t1 : ∀ u v, R.eG (t u) (ε v) = Formalism.UG.bc (iso' v : ZMod (D.host.g v.1) →+* kP (ε v).1) (u v)) (k : Fin 2) :
    ∃ H : Subgroup (G0g D.nd), IsHalf D k H ∧ ∀ u, c (t u) ∈ H ↔ u ∈ levelGU D.host k := by
  refine ⟨Subgroup.pi {kv | kv.1 ≠ k} fun kv => unitri D.R.r (ZMod (D.host.g kv.1)),
    fun g => forall_congr' fun kv => imp_congr_right fun _ => (isUniUp_iff _).symm, fun u => ?_⟩
  refine ((ε.trans plg.symm).forall_congr fun v => ?_).symm
  have he : plg ((ε.trans plg.symm) v) = ε v := plg.apply_symm_apply _
  generalize (ε.trans plg.symm) v = kv at he
  have hk : v.1 = kv.1 := idx_eq (iso' v) (iso kv) (by rw [he])
  show (v.1 ≠ k → _) ↔ (kv.1 ≠ k → _)
  rw [hk]
  refine imp_congr_right fun _ => ?_
  show u v ∈ unitri D.R.r (ZMod (D.host.g v.1)) ↔ c (t u) kv ∈ unitri D.R.r (ZMod (D.host.g kv.1))
  rw [← GlobalTheory.TypeBase.bc_mem_unip_iff (iso' v), ← GlobalTheory.TypeBase.bc_mem_unip_iff (iso kv), ← hpin, ← t1, he]

end Group

section Point

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


set_option maxHeartbeats 1000000 in
theorem keeps_of_good {T : CoreJ D} (hJ : LawsJ T) {j : ℕ} (hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q) (Y : Deep T.toCore j) {e : ℕ}
    {o : ℝ} (hY : Y.Good e o) {G : WTZ D.host.E} (hG : Even G.2) : GlobalTheory.LevDesc.KeepsCusp Y.U G := by
  have hA := hY.lev.2
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [hY.lev.1.2.1, hJ.pins.2.1.1]
  have hχ := fun σ hσ => GlobalTheory.AllWt.Model.chi_modelWt (Y.U σ) (hY.chiTriv σ hσ) G hG
  obtain ⟨ι, hι, -, hpin⟩ := hY.adPin
  refine GlobalTheory.LevelKeeps.keepsCusp_of_isUnf hpq hA hG hY.unf (fun σ hσ k k' => ?_) (fun σ hσ => ?_) hχ
  · obtain ⟨hr, hW⟩ := hY.modelW σ hσ
    exact ⟨(hW k).1.trans (hW k').1.symm, (hW k).2.trans (hW k').2.symm⟩
  · obtain ⟨hr, hW⟩ := hY.modelW σ hσ
    obtain ⟨th, _, hth, hD⟩ := hY.dictU σ hσ
    obtain ⟨x₀, h0, _, g, e, F, ik, φ, th', hth', hL⟩ := hpin σ hσ
    obtain rfl : th = th' := funext fun k => funext fun τ =>
      GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth k τ) (hth' k τ)
    exact GlobalTheory.LevelKeeps.mem_group (hY.unf σ hσ) hA ((hY.unf σ hσ).1 ▸ hpq) hr hW h0 (hM ▸ hY.levelK) hth hD fun h => by
      obtain ⟨γ, -, -, -, h3⟩ := hL.2 h
      exact ⟨_, h3⟩

theorem basis_of_form {K M R V : Type} [Field K] [Field M] [Algebra K M] [AddCommGroup R] [Module K R] [AddCommGroup V]
    [Module K V] [Module M V] {C C' : Submodule K R} (hC : C' = C) {W : Submodule K V} (e : C ≃ₗ[K] W) {n : ℕ} (b : Fin n → V)
    (h1 : ∀ k, b k ∈ W) (h2 : LinearIndependent K b) (h3 : Submodule.span K (Set.range b) = W) :
    ∃ (ε : C' →ₗ[K] V) (b' : Fin n → C'), (∀ (f : C') (h : (f : R) ∈ C), ε f = e ⟨f, h⟩) ∧ (∀ k, ε (b' k) = b k) ∧
      LinearIndependent K b' ∧ Submodule.span K (Set.range b') = ⊤ := by
  subst hC
  have hb : ∀ k, (W.subtype ∘ₗ e.toLinearMap) (e.symm ⟨b k, h1 k⟩) = b k := fun k => by simp
  refine ⟨W.subtype ∘ₗ e.toLinearMap, fun k => e.symm ⟨b k, h1 k⟩, fun f h => rfl, hb, ?_, ?_⟩
  · exact LinearIndependent.of_comp (W.subtype ∘ₗ e.toLinearMap) (by convert h2 using 1; exact funext hb)
  · refine Submodule.map_injective_of_injective (f := W.subtype ∘ₗ e.toLinearMap)
      (W.injective_subtype.comp e.injective) ?_
    rw [Submodule.map_span, ← Set.range_comp, show (W.subtype ∘ₗ e.toLinearMap) ∘ (fun k => e.symm ⟨b k, h1 k⟩) = b from funext hb,
      h3, Submodule.map_top, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]


set_option maxHeartbeats 1000000 in
theorem rank_gen {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (fw : FWTie T R κ v₀) (Fc : Face D A) (i : Fin D.R.m) (act : G → T.R ((i : ℕ) + 1) →ₗ[T.Q.c.F] T.R ((i : ℕ) + 1))
    (hρ : ActRho R i (T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) (fw.e i) act)
    {C : Submodule T.Q.c.F (T.R ((i : ℕ) + 1))} (hC : C = T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n)
    {F V Γ G' : Type} [Field F] [Algebra F ℂ] [AddCommGroup V] [Module F V] [Group Γ] [Finite Γ] [Group G']
    {j : T.Q.c.F →+* F} (hj : ∀ a, algebraMap F ℂ (j a) = T.σ₀ a) (π : C →ₛₗ[j] V) (τ : Representation F Γ V) (θ : Γ →* G)
    (q1 : ∀ (m : ℕ) (b : Fin m → C), LinearIndependent T.Q.c.F b → LinearIndependent F fun k => π (b k))
    (q2 : ∀ γ (v : C), ∃ hv : act (θ γ) v ∈ C, τ γ (π v) = π ⟨_, hv⟩)
    (q3 : ∀ v, (∀ γ, θ γ = 1 → τ γ v = v) → v ∈ Submodule.span F (Set.range π))
    (c : G ≃* G') (s : G' →* Γ) (hs : ∀ g, θ (s (c g)) = g) (Q : Subgroup Γ)
    (hQ : ∀ γ, γ ∈ Q ↔ θ γ ∈ (Fc.lvl false).P) (lamb : Q →* ℂˣ)
    (hlam : ∀ γ : Q, ((lamb γ : ℂˣ) : ℂ) =
      D.what₂.embLL (((Fc.lvl false).ψ⁻¹ ⟨θ γ, (hQ _).1 γ.2⟩ : D.what₂.LLˣ) : D.what₂.LL))
    (e0 : MonoidAlgebra ℂ G') (he : ∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = e0.coeff (c g)) :
    ∃ (ρ : Representation ℂ Γ (ℂ ⊗[F] V)) (χ : Γ →* ℂˣ),
      (∀ (g : Γ) (v : V), ρ g ((1 : ℂ) ⊗ₜ[F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[F] τ g v)) ∧
      Formalism.HN.rkK (latType R Fc i) = Module.finrank ℂ (eig ρ Q lamb) ∧
      Formalism.HN.rkK (CovTop.latBad R Fc i) = Module.finrank ℂ (eig ρ Q lamb ⊓
        LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ G' (ℂ ⊗[F] V)) e0) :
          Submodule ℂ (ℂ ⊗[F] V)) := by
  obtain ⟨n, b, b1, b2, b3, b4, b5⟩ := fw.ks i
  obtain ⟨ε, b', e1, e2, e3, e4⟩ := basis_of_form (M := D.what₂.LL) hC (fw.e i) b b1 b2 b3
  have H := GlobalTheory.BadCount.RankRead.finrank_eq (M := ℂ) D.what₂.embLL
    (fun a => (RingHom.congr_fun (res_embLL T fw.alg_eq fw.laws.pins.2.2.1) a).trans (hj a).symm) ε π b' e4
    (by simpa only [e2] using b4) (by simpa only [e2] using b5) (q1 n b' e3)
    (R.FW i).ρ (R.FW i).chi τ θ c s hs
    (fun γ f => by
      obtain ⟨hv, h⟩ := q2 γ f
      have hf : (f : T.R ((i : ℕ) + 1)) ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := hC ▸ f.2
      obtain ⟨hf', h'⟩ := hρ (θ γ) ⟨f, hf⟩
      exact ⟨⟨_, hv⟩, by rw [e1 f hf, e1 ⟨_, hv⟩ hf']; exact h'.symm, h⟩)
    q3 (Fc.lvl false).P (Fc.lvl false).ψ⁻¹ Q hQ lamb hlam (spType R Fc i) (fun _ => Iff.rfl)
    (fun g => (idemOf A.X).coeff g) e0 he
  have hM := GlobalTheory.GoodLat.Obj.mkFull_of_tie fw i
  refine ⟨_, _, fun g v => GlobalTheory.BadCount.RankRead.twistExt_tmul _ _ _ _ _,
    (GlobalTheory.BadCount.RankRead.rkK_inf _ (fw.ks i) hM _).trans H.1, Eq.trans ?_ H.2⟩
  rw [← GlobalTheory.BadCount.RankRead.rkK_inf _ (fw.ks i) hM, Submodule.restrictScalars_inf, ← inf_assoc]
  rfl


set_option maxHeartbeats 1000000 in
theorem rep_data {T : CoreJ D} (hT : LawsJ T) {j : ℕ} (hj : InR D j) (Y : Deep T.toCore j) {e : ℕ} {o : ℝ} (hY : Y.Good e o)
    {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom a n) {G : Type} [Group G]
    (lev : G → (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)
    (hact : ActLev (Xo := T.Q.Xo j) T.Q.c (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))))
    (hk : ∀ g, ∀ f ∈ T.cuspA j a n, actLev (Xo := T.Q.Xo j) T.Q.c
      (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))) g f ∈ T.cuspA j a n)
    (θ : LevelAut (T.Q.Dw j) Y.d.l₂ →* G) (h1 : ∀ γ, CongMod T.Q.l.Mb (liftLa γ) (lev (θ γ)))
    (h2 : ∀ γ, CongMod T.Q.l.Mb (liftLa γ) LinearMap.id → θ γ = 1) :
    ∃ (π : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n) →ₛₗ[((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle))]
        Y.V (wtZ a n)) (τ : Representation Y.d.c₂.F (LevelAut (T.Q.Dw j) Y.d.l₂) (Y.V (wtZ a n))),
      (∀ g v, (τ g v : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v) ∧
      (∀ (m : ℕ) (b : Fin m → cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)), LinearIndependent T.Q.c.F b →
        LinearIndependent Y.d.c₂.F fun k => π (b k)) ∧
      (∀ γ (v : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)), ∃ hv : actLev (Xo := T.Q.Xo j) T.Q.c
        (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))) (θ γ) v ∈
          cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n), τ γ (π v) = π ⟨_, hv⟩) ∧
      (∀ v, (∀ γ, θ γ = 1 → τ γ v = v) → v ∈ Submodule.span Y.d.c₂.F (Set.range π)) := by
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    have hL := (GlobalTheory.LevGeo.laws_of_coreJ D T j hT hj).1
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  have hA' : Y.d.l₂.A.Coprime Y.d.l₂.M := by rw [hY.lev.2]; exact Nat.coprime_one_left _
  have hKC : GlobalTheory.LevDesc.KeepsCusp Y.U (wtZ a n) := keeps_of_good hT hpq Y hY ((Int.even_coe_nat _).2 hD.2)
  obtain ⟨π, q1, q2, q3⟩ := pull_data D T j Y e o hT hj hY a n hD G lev hact hk θ h1
  have hτ := GlobalTheory.LevDesc.coe_cuspRep Y.U (wtZ a n) hpq hA' hKC
  exact ⟨π, _, hτ, q1, fun γ v => (q2 γ v).imp fun hv h => Subtype.ext ((hτ γ _).trans h),
    fun v hv => q3 v fun γ hγ => (hτ γ v).symm.trans (congrArg Subtype.val (hv γ (h2 γ hγ)))⟩

end Point

end GlobalTheory.CovTop.BadRep
end
end

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.BadRep

open NumberField Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Pj _root_.Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.BadCount
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed typeEmb grpHR grpGHR transl levelGU)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU unitri superDiag)
open GlobalTheory.LevPull (CongMod)
open Formalism.MainNotions.ArithmeticCylinders
open scoped TensorProduct

section Mid

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


set_option maxHeartbeats 1000000 in
theorem rank_cover {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (fw : FWTie T R κ v₀) (Fc : Face D A) (i : Fin D.R.m) (Y : Deep T.toCore ((i : ℕ) + 1)) {e : ℕ} {o : ℝ} (hY : Y.Good e o)
    (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)
    (hact : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c
      (fun g => (lev g, (LinearMap.id : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))))
    (hρ : ActRho R i (T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) (fw.e i) (actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c
      (fun g => (lev g, (LinearMap.id : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)))))
    (θ : LevelAut (T.Q.Dw ((i : ℕ) + 1)) Y.d.l₂ →* G) (h1 : ∀ γ, CongMod T.Q.l.Mb (liftLa γ) (lev (θ γ)))
    (h2 : ∀ γ, CongMod T.Q.l.Mb (liftLa γ) LinearMap.id → θ γ = 1) {G' : Type} [Group G']
    (c : G ≃* G') (s : G' →* LevelAut (T.Q.Dw ((i : ℕ) + 1)) Y.d.l₂) (hs : ∀ g, θ (s (c g)) = g)
    (Q : Subgroup (LevelAut (T.Q.Dw ((i : ℕ) + 1)) Y.d.l₂))
    (hQ : ∀ γ, γ ∈ Q ↔ θ γ ∈ (Fc.lvl false).P) (lamb : Q →* ℂˣ)
    (hlam : ∀ γ : Q, ((lamb γ : ℂˣ) : ℂ) =
      D.what₂.embLL (((Fc.lvl false).ψ⁻¹ ⟨θ γ, (hQ _).1 γ.2⟩ : D.what₂.LLˣ) : D.what₂.LL))
    (e0 : MonoidAlgebra ℂ G') (he : ∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = e0.coeff (c g)) :
    ∃ (ρ : Representation ℂ (LevelAut (T.Q.Dw ((i : ℕ) + 1)) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (wtZ (wtA (κ i)) (κ i).n)))
      (χ : (LevelAut (T.Q.Dw ((i : ℕ) + 1)) Y.d.l₂) →* ℂˣ),
      (∀ (g : (LevelAut (T.Q.Dw ((i : ℕ) + 1)) Y.d.l₂)) (v w : Y.V (wtZ (wtA (κ i)) (κ i).n)),
        (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v →
        ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) ∧
      Formalism.HN.rkK (latType R Fc i) = Module.finrank ℂ (eig ρ Q lamb) ∧
      Formalism.HN.rkK (CovTop.latBad R Fc i) = Module.finrank ℂ (eig ρ Q lamb ⊓
        LinearMap.ker (Representation.asAlgebraHom
          (ρ.comp s : Representation ℂ G' (ℂ ⊗[Y.d.c₂.F] Y.V (wtZ (wtA (κ i)) (κ i).n))) e0) :
          Submodule ℂ (ℂ ⊗[Y.d.c₂.F] Y.V (wtZ (wtA (κ i)) (κ i).n))) := by
  have hk : ∀ g, ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c
      (fun g => (lev g, (LinearMap.id : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))) g f ∈
        T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := fun g f hf => by
    obtain ⟨h, -⟩ := hρ g ⟨f, hf⟩
    exact h
  have hI : InR D ((i : ℕ) + 1) := ⟨Nat.succ_pos _, i.2⟩
  have hC : cuspW (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.U ((i : ℕ) + 1)) (wtZ (wtA (κ i)) (κ i).n) =
      T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := cuspW_wtZ _ _
  have hj : ∀ a, algebraMap Y.d.c₂.F ℂ (((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle)) a) = T.σ₀ a :=
    fun a => rfl
  have H := rep_data fw.laws hI Y hY (dom_wtA (κ i)) lev hact hk θ h1 h2
  refine H.elim fun π h => h.elim fun τ a => ?_
  have H' := rank_gen fw Fc i _ hρ hC hj π τ θ a.2.1 a.2.2.1 a.2.2.2 c s hs Q hQ lamb hlam e0 he
  refine H'.imp fun ρ h' => h'.imp fun χ b => ⟨fun g v w hw => ?_, b.2⟩
  rw [b.1, show τ g v = w from Subtype.ext ((a.1 g v).trans hw.symm)]

end Mid

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}


set_option maxHeartbeats 1000000 in
theorem rank_data (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i) {e : ℕ} {o : ℝ} (hY : Y.Good e o)
    (θ : LevelAut (dat p i) Y.d.l₂ →* p.P.Gp) (h1 : ∀ γ, CongMod p.T.Q.l.Mb (liftLa γ) ((p.O i).lev (θ γ)))
    (h2 : ∀ γ, CongMod p.T.Q.l.Mb (liftLa γ) LinearMap.id → θ γ = 1) {G' : Type} [Group G'] (c : p.P.Gp ≃* G')
    (s : G' →* LevelAut (dat p i) Y.d.l₂) (hs : ∀ g, θ (s (c g)) = g) (Q : Subgroup (LevelAut (dat p i) Y.d.l₂))
    (hQ : ∀ γ, γ ∈ Q ↔ θ γ ∈ (p.F.lv2.lvl false).P) (lamb : Q →* ℂˣ)
    (hlam : ∀ γ : Q, ((lamb γ : ℂˣ) : ℂ) =
      D.what₂.embLL (((p.F.lv2.lvl false).ψ⁻¹ ⟨θ γ, (hQ _).1 γ.2⟩ : D.what₂.LLˣ) : D.what₂.LL))
    (e0 : MonoidAlgebra ℂ G') (he : ∀ g, D.what₂.embLL ((idemOf p.P.A3.A.X).coeff g) = e0.coeff (c g)) :
    ∃ (ρ : Representation ℂ (LevelAut (dat p i) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (χ : (LevelAut (dat p i) Y.d.l₂) →* ℂˣ),
      (∀ (g : (LevelAut (dat p i) Y.d.l₂)) (v w : Y.V (Gk p i)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v →
        ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) ∧
      Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ Q lamb) ∧
      Formalism.HN.rkK (CovTop.latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ Q lamb ⊓
        LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ G' (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) e0) :
          Submodule ℂ (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) :=
  rank_cover p.fw p.F.lv2 i Y hY (p.O i).lev (p.pins i).2.act.1 ((p.rhoGeo i).1 fun g =>
    GlobalTheory.LevelCusp.actLev_mem_cuspA_of_actLev p.T p.κ i _ p.fw.laws (p.pins i).2.act.1 g fun _ => rfl)
    θ h1 h2 c s hs Q hQ lamb hlam e0 he

end Point

end GlobalTheory.CovTop.BadRep
end
end

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.BadRep

open NumberField Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Pj _root_.Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.BadCount
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed typeEmb grpHR grpGHR transl levelGU)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU unitri superDiag)
open GlobalTheory.LevPull (CongMod)
open Formalism.MainNotions.ArithmeticCylinders
open scoped TensorProduct

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}


set_option maxHeartbeats 2000000 in
theorem badRep_at (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i) (hY : GoodCov p i Y) :
    ∃ (fr : TypeFrame (dat p i) Y.d.l₂) (π : (LevelAut (dat p i) Y.d.l₂) →* G0g D.nd) (s : G0g D.nd →* (LevelAut (dat p i) Y.d.l₂)) (ρ : Representation ℂ (LevelAut (dat p i) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (χ : (LevelAut (dat p i) Y.d.l₂) →* ℂˣ) (Pb : Subgroup (G0g D.nd)) (lam : Pb →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g D.nd)), IsSplit π s ∧ IsWhit D Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧ (∀ k, IsHalf D k (H k)) ∧ Pb.comap π = grpHR fr ∧ (∀ k, (H k).comap π = grpGHR fr k) ∧ (∀ (g : (LevelAut (dat p i) Y.d.l₂)) (v w : Y.V (Gk p i)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v → ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) ∧ Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧ Formalism.HN.rkK (CovTop.latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g D.nd) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) D.ntypes.e0) : Submodule ℂ (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) := by
  refine (frame_data p i Y hY.1).elim fun fr h => h.elim fun ε h => h.elim fun iso' h => h.elim fun t h => ?_
  refine p.grpRecPin.elim fun plg h' => h'.elim fun iso h' => ?_
  have hl₂ := h.1
  have hpin := h'.2.2.2
  let c : p.P.Gp ≃* G0g D.nd := p.R.eG.trans p.cG
  let θ : LevelAut (dat p i) Y.d.l₂ →* p.P.Gp := t.toMonoidHom.comp (typeRed fr)
  let π : LevelAut (dat p i) Y.d.l₂ →* G0g D.nd := c.toMonoidHom.comp θ
  let s : G0g D.nd →* LevelAut (dat p i) Y.d.l₂ := (typeEmb hl₂ fr).comp (t.symm.toMonoidHom.comp c.symm.toMonoidHom)
  have hs : ∀ g, θ (s (c g)) = g := fun g => by
    show t (typeRed fr (typeEmb hl₂ fr (t.symm (c.symm (c g))))) = g
    rw [GlobalTheory.LevDesc.typeRed_typeEmb, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  have hsp : IsSplit π s := by
    refine ⟨fun g => ?_, fun g γ hγ => ?_⟩
    · show c (t (typeRed fr (typeEmb hl₂ fr (t.symm (c.symm g))))) = g
      rw [GlobalTheory.LevDesc.typeRed_typeEmb, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    · have h0 : c (t (typeRed fr γ)) = 1 := hγ
      rw [EmbeddingLike.map_eq_one_iff, EmbeddingLike.map_eq_one_iff, GlobalTheory.LevDesc.typeRed_eq_one] at h0
      exact hl₂.commute (GlobalTheory.LevDesc.typeEmb_mem hl₂ fr _) h0
  refine (whit_data p.R.toRealDat p.F.lv2 p.charW.base.grp.levels c plg iso hpin).elim fun Pb w => w.elim fun lam w =>
    w.elim fun ψ w => ?_
  have hH := fun k => half_data p.R.toRealDat c plg iso hpin ε iso' t h.2.2.2.1 k
  have hQ : ∀ γ, γ ∈ Pb.comap π ↔ θ γ ∈ (p.F.lv2.lvl false).P := fun γ => w.2.1 (θ γ)
  refine (rank_data p i Y hY.1 θ h.2.1 (fun γ hγ => (congrArg t (h.2.2.1 γ hγ)).trans (map_one t)) c s hs (Pb.comap π) hQ
    (lam.comp (π.subgroupComap Pb)) (fun γ => w.2.2 (θ γ) γ.2 _) D.ntypes.e0 h'.2.1).elim fun ρ r => r.elim fun χ r => ?_
  exact ⟨fr, π, s, ρ, χ, Pb, lam, ψ, lam.comp (π.subgroupComap Pb), fun k => (hH k).choose, hsp, w.1, fun _ => rfl,
    fun k => (hH k).choose_spec.1, Subgroup.ext fun γ => (hQ γ).trans (h.2.2.2.2 _),
    fun k => Subgroup.ext fun γ => (hH k).choose_spec.2 _, r⟩

end Point

end GlobalTheory.CovTop.BadRep
