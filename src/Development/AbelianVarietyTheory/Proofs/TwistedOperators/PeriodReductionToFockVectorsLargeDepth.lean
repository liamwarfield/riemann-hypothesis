module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowUnfoldingBasicHypotheses
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnRealDatumFockCombinationLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefinitePeriodDependsOnProductFunction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedVectorsAreCombinationsOfVacuaOfLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedFiniteDatumEqHeisenbergCombinationVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedFiniteDatumEqHeisenbergCombinationVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MovedComb

open GlobalTheory.FinPl (Moves Lat)

variable {D : D7}

theorem moves_of_hat (V : HSp D) (g : GA D V) (Λ M : Lat V)
    (h : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ (Lev.finE V g).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) M) :
    Moves V g Λ M (fun _ => True) := by
  intro y hy
  have hy' : ∀ i, (mt V g *ᵥ y) i ∈ GlobalTheory.FinPl.idAt D (fun _ => True) := fun i => GlobalTheory.VacMove.mulVec_mem_idAt _ hy i
  constructor
  · intro hyΛ
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V M _ _ hy' ?_
    rw [GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat]
    exact (h _).1 (GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ y hyΛ)
  · intro hyM
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ y hy ?_
    refine (h _).2 ?_
    rw [← GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat]
    exact GlobalTheory.LatVHat.latV_mem_hatL D V M _ _ hyM

theorem negGA_mem_GfC (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  rw [GfC, MonoidHom.mem_ker] at hg ⊢
  exact hg

theorem datum_fixed {S T : HSp D} {e a a' : AE D} (ha : e * (a + cA D a) = 0) (ha' : e * (a' + cA D a') = 0)
    {b : GA D S} {b' : GA D T} (hb : SuppAt a S b) (hb' : SuppAt a' T b') {Φ : WO S T → ℂ} (hΦ : ∀ x, Φ x ≠ 0 → IsHalf e x) :
    (fun x => Φ (actO S T b⁻¹ b'⁻¹ x)) = Φ := by
  funext x
  by_cases hx : IsHalf e x
  · rw [GlobalTheory.StdHalfLat.actO_eq_self_of_half ha ha' (GlobalTheory.StdHalfLat.suppAt_inv' hb) (GlobalTheory.StdHalfLat.suppAt_inv' hb') hx]
  · have h0 : Φ x = 0 := by
      by_contra hne
      exact hx (hΦ x hne)
    rw [h0]
    by_contra hne
    exact hx (GlobalTheory.MovedVac.halfBack D S T _ _ e x (hΦ _ hne))

private theorem actO_actO_inv_inv (S T : HSp D) (g : GA D S) (h : GA D T) (u : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := by
  have h1 : mt T h * mt T h⁻¹ = 1 := by
    rw [← GlobalTheory.VacMove.mt_mul₀, mul_inv_cancel, GlobalTheory.VacMove.mt_one₀]
  have h2 : mt S g * mt S g⁻¹ = 1 := by
    rw [← GlobalTheory.VacMove.mt_mul₀, mul_inv_cancel, GlobalTheory.VacMove.mt_one₀]
  rw [GlobalTheory.VacMove.actO_eq, GlobalTheory.VacMove.actO_eq, inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul,
    Matrix.mul_assoc, h2, Matrix.mul_one]

private theorem actO_two_nsmul' (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (2 • x) = 2 • actO S T g h x := by
  rw [two_nsmul, two_nsmul, GlobalTheory.VacMove.actO_eq, GlobalTheory.VacMove.actO_eq, Matrix.mul_add, Matrix.add_mul]

theorem isLatVac_move {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T} (hb : Moves S b Λ M fun _ => True)
    (hb' : Moves T b' Λ' M' fun _ => True) {f₀ : WO S T → ℂ} (hf : IsThetaFunO ψ S T f₀)
    (hv : IsLatVac (heisO ψ S T) (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) f₀) :
    IsLatVac (heisO ψ S T) (latO S T (M : Set _) (M' : Set _) fun _ => True) (om (b, b') f₀) := by
  obtain ⟨hv1, hv2⟩ := hv
  have key : ∀ w c : WO S T, actO S T b b' c = w → heisO ψ S T c f₀ = f₀ →
      heisO ψ S T w (om (b, b') f₀) = om (b, b') f₀ := by
    intro w c hc hfix
    rw [← hc, ← hW.om_heis b b' c f₀ hf, hfix]
  refine ⟨fun u hu => ?_, fun e he u hu hue => ?_⟩
  · have hu0 := GlobalTheory.VacMove.actO_mem_latO hM hΛ hM' hΛ' (GlobalTheory.VacMove.moves_inv hb) (GlobalTheory.VacMove.moves_inv hb') hu
    refine key _ (2 • actO S T b⁻¹ b'⁻¹ u) ?_ (hv1 _ hu0)
    rw [actO_two_nsmul', actO_actO_inv_inv]
  · have hu0 := GlobalTheory.VacMove.actO_mem_latO hM hΛ hM' hΛ' (GlobalTheory.VacMove.moves_inv hb) (GlobalTheory.VacMove.moves_inv hb') hu
    have hc : IsHalf e (actO S T b⁻¹ b'⁻¹ u) := by
      apply GlobalTheory.MovedVac.halfBack D S T b b' e
      rw [actO_actO_inv_inv]
      exact hue
    exact key u _ (actO_actO_inv_inv S T b b' u) (hv2 e he _ hu0 hc)

theorem om_eq_of_isThetaAt {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T} (hbf : b ∈ GfC S) (hbf' : b' ∈ GfC T)
    (hb : Moves S b Λ M fun _ => True) (hb' : Moves T b' Λ' M' fun _ => True) {e a a' : AE D} {P : Finset (Pl D.host.E)}
    (he : IsIdemSum e P) (ha : e * (a + cA D a) = 0) (ha' : e * (a' + cA D a') = 0) (hs : SuppAt a S b) (hs' : SuppAt a' T b')
    {Φ f₀ f g : WO S T → ℂ} (hΦ : IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ) (hf₀ : IsThetaFunO ψ S T f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) 1 f₀ Φ f)
    (hg : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 (om (b, b') f₀) Φ g) :
    om (b, b') f = g := by
  have hstd : IsStdChar D ψ (-1) := hW.std
  obtain ⟨θ, hθ⟩ := hstd.2.1
  have hfT : IsThetaFunO ψ S T f := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hstd hθ hf hf₀
  have hth := GlobalTheory.VacMove.isThetaAt_moveLat D ψ S T χS χT om hW Λ M Λ' M' hΛ hM hΛ' hM' b hbf b' hbf' hb hb' e Φ f₀ f
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_idemSum he) hf₀ hfT hf
  rw [datum_fixed ha ha' hs hs' hΦ.1] at hth
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  rw [hall Tm hTm, hg.2 Tm hTm]

private theorem isThetaFunO_and_isLatVac_of_isVacO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT ΛS ΛT f) :
    IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f := by
  exact ⟨h.2.theta, h.2.lat⟩

private theorem moves_negSp_negGA_of_moves {V : HSp D} {g : GA D V} {Λ M : Lat V} (h : Moves V g Λ M fun _ => True) :
    Moves (negSp V) (negGA V g) Λ M fun _ => True := by
  intro y hy
  rw [GlobalTheory.ChiGrid.mt_negGA]
  exact h y hy

private theorem suppAt_negSp_negGA_of_suppAt {V : HSp D} {a : AE D} {g : GA D V} (h : SuppAt a V g) :
    SuppAt a (negSp V) (negGA V g) := by
  intro i j
  rw [GlobalTheory.ChiGrid.mt_negGA]
  exact h i j

private theorem moved_core_lemma_3 {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T} (hbf : b ∈ GfC S) (hbf' : b' ∈ GfC T)
    (hb : Moves S b Λ M fun _ => True) (hb' : Moves T b' Λ' M' fun _ => True) {e : AE D} {P : Finset (Pl D.host.E)}
    (he : IsIdemSum e P) (hk : ∃ a, e * (a + cA D a) = 0 ∧ SuppAt a S b)
    (hk' : ∃ a', e * (a' + cA D a') = 0 ∧ SuppAt a' T b') {Φ f₀ f : WO S T → ℂ}
    (hΦ : IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ) (hf₀ : IsThetaFunO ψ S T f₀)
    (hv : IsLatVac (heisO ψ S T) (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) 1 f₀ Φ f)
    (c : WO S T →₀ ℂ)
    (hc : ∀ g₀, IsThetaFunO ψ S T g₀ → IsLatVac (heisO ψ S T) (latO S T (M : Set _) (M' : Set _) fun _ => True) g₀ →
      IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 g₀ Φ (comb ψ S T c g₀)) :
    om (b, b') f = comb ψ S T c (om (b, b') f₀) := by
  obtain ⟨a, ha, hs⟩ := hk
  obtain ⟨a', ha', hs'⟩ := hk'
  exact om_eq_of_isThetaAt hW hΛ hM hΛ' hM' hbf hbf' hb hb' he ha ha' hs hs' hΦ hf₀ hf
    (hc _ (hW.om_pres _ _ hf₀) (isLatVac_move hW hΛ hM hΛ' hM' hb hb' hf₀ hv))

theorem movedVec_eq_comb : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ (d : FinDatum ch.G t p) (c : WO (ch.G.pS p) (ch.G.pT p) →₀ ℂ), d.z = 1 → ch.S.Z.HasVec d → IsCombOf ch.W d c → movedVec t ch.S.toGridChoice d = comb ch.W.ψ _ _ c (ch.W.om p (ch.G.toPair p (ch.S.N.u p.small).1 (ch.S.N.u p.big).1) (ch.S.Z.vac p)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F hset ch _ t p hp d c hz hvec hcomb
  have hL := hset.core.lev
  have hnodes := GlobalTheory.FunObj.DefPair.nodes hp
  obtain ⟨f, hf⟩ := hvec
  have hvd : ch.S.Z.vec d = f := by
    unfold GlobalTheory.FunObj.Normal.vec
    rw [GlobalTheory.FunObj.FinDatum.vec_eq ch.W hf, hz, ← Prod.one_eq_mk, map_one]
    rfl
  unfold movedVec
  rw [hvd]
  cases p with
  | chi i j =>
    have hX := hnodes.1
    have hY := hnodes.2
    obtain ⟨hf₀, hv⟩ := isThetaFunO_and_isLatVac_of_isVacO (ch.S.Z.vac_is (.chi i j) hp)
    exact moved_core_lemma_3 (ch.W.om_is (.chi i j) (by simp only [DefPair, Pair.InRange, Node.InRange] at hp ⊢; omega))
      (GlobalTheory.ChiGrid.isSelfDualC_neg (GlobalTheory.FunObj.Std.selfDual ch.S.N hY))
      (GlobalTheory.ChiGrid.isSelfDualC_neg (GlobalTheory.FunObj.DefNode.selfDual ch.G hL hY))
      (GlobalTheory.FunObj.Std.selfDual ch.S.N hX) (GlobalTheory.FunObj.DefNode.selfDual ch.G hL hX)
      (negGA_mem_GfC _ (ch.S.N.u _).2) (ch.S.N.u _).2
      (moves_negSp_negGA_of_moves (moves_of_hat _ _ _ _ (ch.S.N.u_lat _ hY))) (moves_of_hat _ _ _ _ (ch.S.N.u_lat _ hX))
      d.e_is
      (by
        obtain ⟨a, ha, hs⟩ := GlobalTheory.StdHalfLat.exists_kill ch.S.N (Set.mem_univ t) d hY
        exact ⟨a, ha, suppAt_negSp_negGA_of_suppAt hs⟩)
      (GlobalTheory.StdHalfLat.exists_kill ch.S.N (Set.mem_univ t) d hX)
      d.sb hf₀ hv hf c hcomb.2.2
  | mu t' i j => exact False.elim hp
  | core i => exact False.elim hp
  | top t' j =>
    have hX := hnodes.1
    have hY := hnodes.2
    obtain ⟨hf₀, hv⟩ := isThetaFunO_and_isLatVac_of_isVacO (ch.S.Z.vac_is (.top t' j) hp)
    exact moved_core_lemma_3 (ch.W.om_is (.top t' j) (by simp only [DefPair, Pair.InRange, Node.InRange] at hp ⊢; omega))
      (GlobalTheory.FunObj.Std.selfDual ch.S.N hX) (GlobalTheory.FunObj.DefNode.selfDual ch.G hL hX)
      (GlobalTheory.FunObj.Std.selfDual ch.S.N hY) (GlobalTheory.FunObj.DefNode.selfDual ch.G hL hY)
      (ch.S.N.u _).2 (ch.S.N.u _).2
      (moves_of_hat _ _ _ _ (ch.S.N.u_lat _ hX)) (moves_of_hat _ _ _ _ (ch.S.N.u_lat _ hY))
      d.e_is (GlobalTheory.StdHalfLat.exists_kill ch.S.N (Set.mem_univ t) d hX)
      (GlobalTheory.StdHalfLat.exists_kill ch.S.N (Set.mem_univ t) d hY)
      d.sb hf₀ hv hf c hcomb.2.2

end GlobalTheory.MovedComb

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedFiniteDatumEqHeisenbergCombinationVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedFiniteDatum_eq_heisenbergCombination_vacuum : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ (d : FinDatum ch.G t p) (c : WO (ch.G.pS p) (ch.G.pT p) →₀ ℂ), d.z = 1 → ch.S.Z.HasVec d → IsCombOf ch.W d c → movedVec t ch.S.toGridChoice d = comb ch.W.ψ _ _ c (ch.W.om p (ch.G.toPair p (ch.S.N.u p.small).1 (ch.S.N.u p.big).1) (ch.S.Z.vac p)) := by
  first | exact @GlobalTheory.MovedComb.movedVec_eq_comb | exact GlobalTheory.MovedComb.movedVec_eq_comb | (intros; apply GlobalTheory.MovedComb.movedVec_eq_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowMovedVacuumEqUnitMulChosen
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowMovedVacuumEqUnitMulChosen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.RowVac

set_option synthInstance.maxHeartbeats 400000

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {U : Set T}

private lemma eToEAf_mem_hatL_of_mem {n : ℕ} (C : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (s : Fin n → D.host.E) (hs : s ∈ C) :
    (fun j => Formalism.IndefR.Datum.eToEAf D (s j)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS
  exact Submodule.subset_span ⟨s, hs, rfl⟩

theorem fwd_gen (V : HSp D) (k : Formalism.L2.Theta.GA D V) (C Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hb : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (s : Fin V.rank → D.host.E) (hs : s ∈ C) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((Formalism.L2.Theta.mt V k *ᵥ fun j => incA D (s j)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  rw [GlobalTheory.MovedHomLat.bridge]
  exact (hb _).1 (eToEAf_mem_hatL_of_mem C s hs)


set_option maxHeartbeats 1000000 in
theorem bwd_gen (V : HSp D) (k : Formalism.L2.Theta.GA D V) (C Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hb : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (s : Fin V.rank → D.host.E) (hs : s ∈ Λ) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((Formalism.L2.Theta.mt V k⁻¹ *ᵥ fun j => incA D (s j)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) C := by
  apply GlobalTheory.MovedHomLat.bwd V k C s
  rw [GlobalTheory.MovedHomLat.mem_globLat_iff]
  apply (hb _).2
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  exact eToEAf_mem_hatL_of_mem Λ s hs

theorem isVacO_om (W : G.Weil) (p : Pair T) (hp : p.InRange D.R.m) (g : Formalism.L2.Theta.GA D (G.pS p)) (h : Formalism.L2.Theta.GA D (G.pT p))
    (hg : g ∈ GfC (G.pS p)) (hh : h ∈ GfC (G.pT p)) (AS BS : Set (Fin (G.pS p).rank → D.host.E))
    (AT BT : Set (Fin (G.pT p).rank → D.host.E))
    (hact : ∀ w' ∈ latO _ _ BS BT (fun _ => True), ∃ w ∈ latO _ _ AS AT (fun _ => True), actO _ _ g h w = w')
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) AS AT f) :
    IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) BS BT (W.om p (g, h) f) := by
  have hW := W.om_is p hp
  unfold IsVacO at hf ⊢
  obtain ⟨hstd, hvac⟩ := hf
  obtain ⟨hθ, hth, hlat, hfock, hnrm⟩ := hvac
  obtain ⟨-, -, -, -, -, hpres, hint, -, -, hunit, -⟩ := hW
  have hth' := hpres (g, h) f hth
  have ⟨_, _, hc, _⟩ := hth
  have ⟨_, _, hc', _⟩ := hth'
  refine ⟨hstd, hθ, hth', ⟨?_, ?_⟩, ?_, ?_⟩
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := hact u hu
    rw [← GlobalTheory.WeilVacMove.actO_two_nsmul, ← hint g h _ f hth, hlat.1 w hw]
  · intro e he u hu hhalf
    obtain ⟨w, hw, rfl⟩ := hact u hu
    have hw' : IsHalf e w := by
      have := GlobalTheory.WeilVacMove.isHalf_actO e g⁻¹ h⁻¹ hhalf
      rwa [GlobalTheory.WeilVacMove.actO_inv_actO] at this
    rw [← hint g h _ f hth, hlat.2 e he w hw hw']
  · intro τ
    have hg1 := GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ hg τ
    have hh1 := GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ hh τ
    have hgi : compAt W.θ τ (Formalism.L2.Theta.mt _ g⁻¹) = 1 := by
      have := GlobalTheory.WeilVacMove.compAt_mt_mul_inv W.θ τ _ g
      rwa [hg1, one_mul] at this
    have key : ∀ z', W.om p (g, h) (Formalism.IndefR.Datum.dRho (heisO W.ψ _ _) W.θ τ z' f) =
        Formalism.IndefR.Datum.dRho (heisO W.ψ _ _) W.θ τ z' (W.om p (g, h) f) := by
      intro z'
      have := GlobalTheory.WeilVacMove.om_dRho (W.om_is p hp) hθ g h τ z' hth
      rwa [hh1, hgi, Matrix.one_mul, Matrix.mul_one] at this
    have h0 := hfock τ
    unfold IsFockVacAt at h0 ⊢
    intro z
    have h1 := h0 z
    unfold annih at h1 ⊢
    rw [← key, ← key, ← map_smul, ← map_add (f := _), h1, map_zero]
  · refine ⟨hnrm.1, fun a ha => ?_⟩
    have h1 : nrm2 a.1 a.2 f = 1 := hnrm.2 a ha
    show nrm2 a.1 a.2 _ = 1
    unfold IsCovolOne at ha
    obtain ⟨hμ, hF, -⟩ := ha
    rw [GlobalTheory.WeilVacMove.sqNormIntegralFundamentalDomain_eq_l2Norm_sq _ _ hc] at h1
    rw [GlobalTheory.WeilVacMove.sqNormIntegralFundamentalDomain_eq_l2Norm_sq _ _ hc', hunit a.1 a.2 hμ hF (g, h) f hth]
    exact h1

theorem neg_mem_GfC (V : HSp D) {g : Formalism.L2.Theta.GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  unfold GfC at hg ⊢
  rw [MonoidHom.mem_ker] at hg ⊢
  exact hg


set_option maxHeartbeats 1000000 in
theorem moved_isVac (W : G.Weil) (N : Std G U) (Z : Normal W N) (i : ℕ) (hi : i < D.R.m) :
    W.IsVac (.chi i D.R.m) (W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (N.u (Pair.chi i D.R.m : Pair T).small).1
      (N.u (Pair.chi i D.R.m : Pair T).big).1) (Z.vac (.chi i D.R.m))) := by
  have hdp : DefPair D.R.m (Pair.chi i D.R.m : Pair T) := ⟨hi, rfl⟩
  have hbig : DefNode D.R.m (Node.grid (i + 1) D.R.m) := ⟨hi, rfl⟩
  have hsmall : DefNode D.R.m (Node.grid i D.R.m) := ⟨hi.le, rfl⟩
  have hp : (Pair.chi i D.R.m : Pair T).InRange D.R.m := ⟨hi, le_rfl⟩
  have hU := N.u_lat _ hbig
  have hV := N.u_lat _ hsmall
  have hg : negGA (G.V (.grid (i + 1) D.R.m)) (N.u (.grid (i + 1) D.R.m)).1 ∈ GfC (negSp (G.V (.grid (i + 1) D.R.m))) :=
    neg_mem_GfC (G.V (.grid (i + 1) D.R.m)) (N.u (.grid (i + 1) D.R.m)).2
  have hh : (N.u (.grid i D.R.m)).1 ∈ GfC (G.V (.grid i D.R.m)) := (N.u (.grid i D.R.m)).2
  have hv := Z.vac_is _ hdp
  have hact : ∀ w' ∈ latO (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (G.latS (.chi i D.R.m) : Set _)
      (G.latT (.chi i D.R.m) : Set _) (fun _ => True), ∃ w ∈ latO (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m))
      (N.latS (.chi i D.R.m) : Set _) (N.latT (.chi i D.R.m) : Set _) (fun _ => True),
      actO (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (negGA (G.V (.grid (i + 1) D.R.m)) (N.u (.grid (i + 1) D.R.m)).1)
        (N.u (.grid i D.R.m)).1 w = w' := by
    refine (GlobalTheory.MovedHomLat.actO_latO_onto _ _ _ _ (N.latS (.chi i D.R.m)) (G.latS (.chi i D.R.m))
      (N.latT (.chi i D.R.m)) (G.latT (.chi i D.R.m)) ?_ ?_ ?_ ?_).2
    · intro s hs
      rw [mt_negGA]
      exact fwd_gen _ _ _ _ hU s hs
    · intro t ht
      exact fwd_gen _ _ _ _ hV t ht
    · intro s hs
      rw [← map_inv, mt_negGA]
      exact bwd_gen _ _ _ _ hU s hs
    · intro t ht
      exact bwd_gen _ _ _ _ hV t ht
  exact isVacO_om W (.chi i D.R.m) hp _ _ hg hh _ _ _ _ hact _ hv

private lemma sigOK_and_isSelfDualC_grid {μ₀ : T} (hL : L.Is μ₀) (a b : ℕ) (ha : a ≤ D.R.m) (hb : b ≤ D.R.m) :
    (G.V (.grid a b)).SigOK ∧ IsSelfDualC (G.V (.grid a b)) (G.Λ (.grid a b)) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · show (columnBlock L b).sp.SigOK ∧ IsSelfDualC (columnBlock L b).sp (columnBlock L b).lat
    rcases lt_or_eq_of_le hb with hb' | rfl
    · rw [colY_lt L hb']
      exact ⟨D.sp.Y_sig _, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ (hL.βY b hb')⟩
    · rw [colY_m L]
      exact ⟨D.sp.X'_sig, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ hL.βX⟩
  · have hv := G.isV (X := .grid a b) ⟨ha, hb⟩ (by intro j h; injection h with h1 h2; omega)
    exact ⟨hv.sigOK, hv.sd⟩

theorem isVac_unique (W : G.Weil) {μ₀ : T} (hL : L.Is μ₀) (i j : ℕ) (hp : (Pair.chi i j : Pair T).InRange D.R.m) {f f'}
    (hf : W.IsVac (.chi i j) f) (hf' : W.IsVac (.chi i j) f') : ∃ κ : ℂˣ, f' = (κ : ℂ) • f := by
  unfold GridData.Weil.IsVac at hf hf'
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hs1, hd1⟩ := sigOK_and_isSelfDualC_grid hL (i + 1) j hp1 hp2
  obtain ⟨hs2, hd2⟩ := sigOK_and_isSelfDualC_grid hL i j (by omega) hp2
  have key := VacUnique.vacUniqueO D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ (GlobalTheory.GridWeil.sigOK_neg hs1) hs2
    (fun τ => GlobalTheory.ChiGrid.isCartanInv_neg (W.cart_is (.grid (i + 1) j) ⟨hp1, hp2⟩ τ))
    (W.cart_is (.grid i j) ⟨by omega, hp2⟩) _ _
    (isSelfDualC_neg hd1) hd2 f f' hf hf'
  obtain ⟨c, hc, hcf⟩ := key
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  exact ⟨Units.mk0 c hc0, hcf⟩

theorem moved_vac_eq : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ i : ℕ, i < D.R.m → ∃ κ : ℂˣ, ch.W.om (.chi i D.R.m) (ch.G.toPair (.chi i D.R.m) (ch.S.N.u (Pair.chi i D.R.m : Pair T).small).1 (ch.S.N.u (Pair.chi i D.R.m : Pair T).big).1) (ch.S.Z.vac (.chi i D.R.m)) = (κ : ℂ) • ch.rm.vX i D.R.m := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F hS ch hch i hi
  have hL : R.toLevCh.Is A.μ0 := by
    obtain ⟨-, -, -, -, hcore, -⟩ := hS
    exact hcore.lev
  exact isVac_unique ch.W hL i D.R.m ⟨hi, le_rfl⟩ (ch.rm.vX_is i D.R.m hi le_rfl)
    (moved_isVac ch.W ch.S.N ch.S.Z i hi)

end GlobalTheory.RowVac
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowMovedVacuumEqUnitMulChosenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRow_moved_vacuum_eq_unit_mul_chosen : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ i : ℕ, i < D.R.m → ∃ κ : ℂˣ, ch.W.om (.chi i D.R.m) (ch.G.toPair (.chi i D.R.m) (ch.S.N.u (Pair.chi i D.R.m : Pair T).small).1 (ch.S.N.u (Pair.chi i D.R.m : Pair T).big).1) (ch.S.Z.vac (.chi i D.R.m)) = (κ : ℂ) • ch.rm.vX i D.R.m := by
  first | exact @GlobalTheory.RowVac.moved_vac_eq | exact GlobalTheory.RowVac.moved_vac_eq | (intros; apply GlobalTheory.RowVac.moved_vac_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedVectorsAreCombinationsOfVacuaOfLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

theorem comb_smul_heis {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (a • f) = a • comb ψ S T c f := by
  have h : ∀ u, heisO ψ S T u (a • f) = a • heisO ψ S T u f := fun u => by
    funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
  unfold comb
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun u _ => by rw [h, smul_comm]

theorem movedAt_big : Big fun ch => MovedAt ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs _ => ?_⟩⟩
  obtain ⟨v, hv, κ, z, hz, hcol⟩ := GlobalTheory.T.exists_columnUnitVacuaFamily_moved large₂ F hS ch hIs
  choose κ' hκ' using fun i : Fin D.R.m => GlobalTheory.T.lastRow_moved_vacuum_eq_unit_mul_chosen large₂ F hS ch hIs i i.2
  refine ⟨v, hv, κ, fun i => if h : i < D.R.m then κ' ⟨i, h⟩ else 1, z, hz,
    fun t a β τ c hSum hExp hC d hd => ⟨fun j => ?_, fun i => ?_⟩⟩
  · have hvec := ((hSum.vec β τ hExp d hd).1 j)
    obtain ⟨e, -, hd1, -⟩ := hExp
    have hz1 := ((hd1 d hd).1 j).2.2
    rw [GlobalTheory.T.movedFiniteDatum_eq_heisenbergCombination_vacuum large₂ F hS ch hIs t (.top t j) (show DefPair D.R.m (Pair.top t (j : ℕ) : Pair T) from j.2) (d.1 j) ((c d).1 j) hz1 hvec ((hC d hd).1 j),
      hcol t j j.2, comb_smul_heis]
  · have hvec := ((hSum.vec β τ hExp d hd).2 i)
    obtain ⟨e, -, hd1, -⟩ := hExp
    have hz1 := ((hd1 d hd).2 i).2.2
    rw [GlobalTheory.T.movedFiniteDatum_eq_heisenbergCombination_vacuum large₂ F hS ch hIs t (.chi i D.R.m) (show DefPair D.R.m (Pair.chi (i : ℕ) D.R.m : Pair T) from ⟨i.2, rfl⟩) (d.2 i) ((c d).2 i) hz1 hvec ((hC d hd).2 i),
      hκ' i, comb_smul_heis]
    simp only [dif_pos i.2, combR]

end GlobalTheory.RowVal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedVectorsAreCombinationsOfVacuaOfLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedVectorsAreCombinationsOfVacua_of_large_depth : Big fun ch => MovedAt ch := by
  first | exact @GlobalTheory.RowVal.movedAt_big | exact GlobalTheory.RowVal.movedAt_big | (intros; apply GlobalTheory.RowVal.movedAt_big <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodReductionToFockVectorsLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockRed

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem opPow_smul {ι X : Type} (A : ι → (X → ℂ) → X → ℂ) (hA : ∀ i (c : ℂ) g, A i (c • g) = c • A i g)
    (k : ι →₀ ℕ) (c : ℂ) (f : X → ℂ) : opPow A k (c • f) = c • opPow A k f := by
  unfold opPow
  induction (Finsupp.toMultiset k).toList with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, hA]

theorem pureTensorL_smul {ι X : Type} (A : ι → (X → ℂ) → X → ℂ) (hA : ∀ i (c : ℂ) g, A i (c • g) = c • A i g)
    (c : ℂ) (f : X → ℂ) : pureTensorL A (c • f) = c • pureTensorL A f := by
  refine (MvPolynomial.basisMonomials ι ℂ).ext fun k => ?_
  simp only [pureTensorL, Module.Basis.constr_basis, LinearMap.smul_apply, opPow_smul A hA]

theorem dRho_smul {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → Mx D m n → ℂ)
    (hhs : ∀ w (c : ℂ) g, hs w (c • g) = c • hs w g) (θ : InfFam D) (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ)
    (c : ℂ) (g : Mx D m n → ℂ) : Datum.dRho hs θ τ z (c • g) = c • Datum.dRho hs θ τ z g := by
  funext x
  simp only [Datum.dRho, hhs, Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field c

theorem aPlusAll_smul {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → Mx D m n → ℂ)
    (hhs : ∀ w (c : ℂ) g, hs w (c • g) = c • hs w g) (θ : InfFam D) J B B' (k : FVar D m n) (c : ℂ) (g : Mx D m n → ℂ) :
    aPlusAll hs θ J B B' k (c • g) = c • aPlusAll hs θ J B B' k g := by
  simp only [aPlusAll, aPlus, crea, dRho_smul hs hhs, smul_comm _ c, smul_sub]

theorem fock_smul (W : G.Weil) (p : Pair T) (c : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ) (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    W.fock p (c • f) Q = c • W.fock p f Q := by
  have hh : ∀ w (c : ℂ) g, heisO W.ψ (G.pS p) (G.pT p) w (c • g) = c • heisO W.ψ (G.pS p) (G.pT p) w g := by
    intro w c g; funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
  simp only [GridData.Weil.fock, pureTensorO]
  rw [pureTensorL_smul _ (fun i c g => aPlusAll_smul _ hh _ _ _ _ i c g)]
  rfl

end GlobalTheory.FockRed

namespace GlobalTheory.FockRed

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem liftA_smul_left (W : G.Weil) (M : Vol G) (a : Arrow T) (f : Sch G a) (c : ℂ) (F : Fn G a.src) :
    liftA W M a f (c • F) = c • liftA W M a f F := by
  funext g
  simp only [liftA, Formalism.IndefR.Lift.liftInt, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext h; ring

theorem liftA_smul_right (W : G.Weil) (M : Vol G) (a : Arrow T) (ha : ∀ i, a ≠ .coreUp i) (c : ℂ) (f : Sch G a)
    (F : Fn G a.src) : liftA W M a (c • f) F = c • liftA W M a f F := by
  funext g
  simp only [liftA, Formalism.IndefR.Lift.liftInt, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext h
  cases a with
  | coreUp i => exact absurd rfl (ha i)
  | _ => simp only [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_smul, LinearMap.smul_apply, Module.End.smul_def, Pi.smul_apply, smul_eq_mul]; ring

theorem pathLift_column_smul_univ (W : G.Weil) (M : Vol G) (t : T) : ∀ (n : ℕ) (s : Fin n → ℂ) (g : ∀ j : Fin n, Sch G (.col t j))
    (φ : Fn G (.top 0)), liftP W M (colPath t n) (colFam t n fun j => s j • g j) φ =
      (∏ j, s j) • liftP W M (colPath t n) (colFam t n g) φ
  | 0, s, g, φ => by simp [colPath, liftP]
  | n + 1, s, g, φ => by
    show liftA W M (.col t n) (s (Fin.last n) • g (Fin.last n))
        (liftP W M (colPath t n) (colFam t n fun j => s j.castSucc • g j.castSucc) φ) =
      (∏ j, s j) • liftA W M (.col t n) (g (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => g j.castSucc) φ)
    rw [pathLift_column_smul_univ W M t n (fun j => s j.castSucc) (fun j => g j.castSucc) φ, liftA_smul_left,
      liftA_smul_right W M _ (fun i h => by cases h), Fin.prod_univ_castSucc, smul_smul, mul_comm]

theorem pathLift_row_smul_univ (W : G.Weil) (M : Vol G) (m : ℕ) : ∀ (n : ℕ) (s : Fin n → ℂ) (g : ∀ i : Fin n, Sch G (.right i m))
    (F : Fn G (.grid 0 m)), liftP W M (rowPath T m n) (rowFam m n fun i => s i • g i) F =
      (∏ i, s i) • liftP W M (rowPath T m n) (rowFam m n g) F
  | 0, s, g, F => by simp [rowPath, liftP]
  | n + 1, s, g, F => by
    show liftA W M (.right n m) (s (Fin.last n) • g (Fin.last n))
        (liftP W M (rowPath T m n) (rowFam m n fun i => s i.castSucc • g i.castSucc) F) =
      (∏ i, s i) • liftA W M (.right n m) (g (Fin.last n)) (liftP W M (rowPath T m n) (rowFam m n fun i => g i.castSucc) F)
    rw [pathLift_row_smul_univ W M m n (fun i => s i.castSucc) (fun i => g i.castSucc) F, liftA_smul_left,
      liftA_smul_right W M _ (fun i h => by cases h), Fin.prod_univ_castSucc, smul_smul, mul_comm]

end GlobalTheory.FockRed

namespace GlobalTheory.FockRed

theorem defPer_of_smul {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (M : Vol G) (Q : PolCol G) (P : PolRow G) (d : PureDat G t) (φ : Fn G (.top 0))
    (F : Fn G (.grid 0 D.R.m)) (s s' : Fin D.R.m → ℂ) (g : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))) → ℂ)
    (f : SchRow G) (h1 : ∀ j : Fin D.R.m, movedVec t S (d.1 j) = s j • g j) (h2 : ∀ i : Fin D.R.m, movedVec t S (d.2 i) = s' i • f i) :
    defPer t S M (Q, P) d φ F = ((∏ j, s j) * ∏ i, s' i) * ∫ h in M.fd (.grid D.R.m D.R.m),
      liftP W M (colPath t D.R.m) (colFam t D.R.m fun j => W.fock (.top t j) (g j) (Q j)) φ (stabilizerEmbedding G.sp.topDec h) *
        liftP W M (rowPath T D.R.m D.R.m) (rowFam D.R.m D.R.m fun i => W.fock (.chi i D.R.m) (f i) (P i)) F h
        ∂M.ν (.grid D.R.m D.R.m) := by
  have e1 : (fun j : Fin D.R.m => (W.fock (.top t j) (movedVec t S (d.1 j)) (Q j) : Sch G (.col t j))) =
      fun j : Fin D.R.m => s j • (W.fock (.top t j) (g j) (Q j) : Sch G (.col t j)) := funext fun j => by
    rw [h1 j]; exact fock_smul W (.top t j) _ _ _
  have e2 : (fun i : Fin D.R.m => (W.fock (.chi i D.R.m) (movedVec t S (d.2 i)) (P i) : Sch G (.right i D.R.m))) =
      fun i : Fin D.R.m => s' i • (W.fock (.chi i D.R.m) (f i) (P i) : Sch G (.right i D.R.m)) := funext fun i => by
    rw [h2 i]; exact fock_smul W (.chi i D.R.m) _ _ _
  have e3 := (congrArg (fun x => liftP W M (colPath t D.R.m) (colFam t D.R.m x) φ) e1).trans
    (pathLift_column_smul_univ W M t D.R.m s (fun j => W.fock (.top t j) (g j) (Q j)) φ)
  have e4 := (congrArg (fun x => liftP W M (rowPath T D.R.m D.R.m) (rowFam D.R.m D.R.m x) F) e2).trans
    (pathLift_row_smul_univ W M D.R.m D.R.m s' (fun i => W.fock (.chi i D.R.m) (f i) (P i)) F)
  unfold defPer
  rw [← integral_const_mul]
  congr 1
  funext h
  have e5 := congrFun e3 (stabilizerEmbedding G.sp.topDec h)
  have e6 := congrFun e4 h
  simp only [Pi.smul_apply, smul_eq_mul] at e5 e6
  refine (congrArg₂ (· * ·) e5 e6).trans ?_
  ring

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}


set_option maxHeartbeats 1600000 in
theorem fockAt_of_steps (ch : Choice R) (hB : BasicAt ch) (hMv : MovedAt ch) (hCF : ColFock ch)
    (hL : ∀ (t : T) (M : Vol ch.G), IsHaarDef M → ∀ (f : SchRow ch.G), (∀ i, IsThetaFunO ch.W.ψ _ _ (f i)) →
      ∀ (P : PolRow ch.G) (y : (R.HX t).H), GlobalTheory.Unf.IsContAut _ (liftP ch.W M (rowPath T D.R.m D.R.m)
        (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (f i) (P i)) (formTop ch t y))) : FockAt ch := by
  classical
  obtain ⟨_, _, _, _, _, hBgood', _⟩ := hB
  obtain ⟨v, hv, κ, κ', z, hz, hmv⟩ := hMv
  refine ⟨fun t => ∏ j : Fin D.R.m, z t j, fun t => Subgroup.prod_mem _ fun j _ => hz t j, ?_⟩
  intro C hC P
  obtain ⟨σc, hσc⟩ := hCF v hv C hC
  obtain ⟨K, hK⟩ : ∃ K : ℂ, K = (∏ j : Fin D.R.m, ((κ j : ℂˣ) : ℂ))⁻¹ * (∏ i : Fin D.R.m, ((κ' i : ℂˣ) : ℂ))⁻¹ := ⟨_, rfl⟩
  refine ⟨K • σc.mapDomain (fun Q => (Q, P)), ?_⟩
  intro t a β M hM hS τ c hτ hc y
  obtain ⟨Z, hZ⟩ : ∃ Z : ℂ, Z = ∏ j : Fin D.R.m, ((z t j : ℂˣ) : ℂ) := ⟨_, rfl⟩
  have hone : Z⁻¹ * K * ((∏ j : Fin D.R.m, ((κ j * z t j : ℂˣ) : ℂ)) * ∏ i : Fin D.R.m, ((κ' i : ℂˣ) : ℂ)) = 1 := by
    have n1 : (∏ j : Fin D.R.m, ((κ j : ℂˣ) : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (κ j).ne_zero
    have n2 : (∏ j : Fin D.R.m, ((κ' j : ℂˣ) : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (κ' j).ne_zero
    have n3 : (∏ j : Fin D.R.m, ((z t j : ℂˣ) : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (z t j).ne_zero
    simp only [Units.val_mul, Finset.prod_mul_distrib]
    rw [hK, hZ]
    field_simp
  have key : ∀ d ∈ τ.support, per ch.W M t (combC ch.W (c d) C) (combR ch.rm (c d)) P (colFn ch a) (formTop ch t y) =
      σc.sum fun Q x => x * (Z⁻¹ * K * defPer t ch.S.toGridChoice M (Q, P) d (colFn ch a) (formTop ch t y)) := by
    intro d hd
    obtain ⟨h1, h2⟩ := hmv t a β τ c hS hτ hc d hd
    have hfin : ∀ j, j < D.R.m → IsFinComb ((c d).1 j) := fun j hj => ((hc d hd).1 ⟨j, hj⟩).1
    have hth := (hBgood' C hC (c d) hfin).2
    refine (hσc t M hM a (c d) hfin _ (hL t M hM (combR ch.rm (c d)) hth P y)).trans ?_
    refine Finset.sum_congr rfl fun Q _ => ?_
    dsimp only
    rw [defPer_of_smul ch.S.toGridChoice t M Q P d (colFn ch a) (formTop ch t y) (fun j => ((κ j * z t j : ℂˣ) : ℂ))
      (fun i => ((κ' i : ℂˣ) : ℂ)) (fun j => comb ch.W.ψ _ _ ((c d).1 j) (v j)) (combR ch.rm (c d)) h1 h2,
      ← mul_assoc (Z⁻¹ * K), hone, one_mul]
  rw [defTot_smul, Units.coe_prod, ← hZ]
  unfold defTot
  rw [Finsupp.sum_mapDomain_index_inj (fun Q Q' h => (Prod.ext_iff.1 h).1), Finsupp.sum_comm]
  simp only [Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [key d hd, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q _ => ?_
  ring

end

theorem fockAt_big : Big fun ch => FockAt ch := by
  obtain ⟨a0, ha⟩ := Big.and (Big.and GlobalTheory.T.lastRow_unfolding_basicHypotheses GlobalTheory.T.movedVectorsAreCombinationsOfVacua_of_large_depth) GlobalTheory.T.columnRealDatum_fockCombination_largeDepth
  refine ⟨a0, fun ε CF hC => ?_⟩
  obtain ⟨x, hx⟩ := ha ε CF hC
  refine ⟨x, fun D large₂ he hxx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc => ?_⟩
  obtain ⟨⟨hB, hMv⟩, hCF⟩ := hx D large₂ he hxx Γ Pl0 T A Ks R F s ch hch hsc
  refine fockAt_of_steps ch hB hMv hCF fun t M hM f hf P y => ?_
  have hN : ∀ X, DefNode D.R.m X → X ≠ .top D.R.m → GlobalTheory.RowTens.Nice M X := fun X hX hX' => by
    refine ⟨?_, hM X hX hX'⟩
    rcases X with ⟨i, j⟩ | i | j
    all_goals first
      | exact hX.elim
      | exact GlobalTheory.DefConv.posDef_of_node ch.G s.core.lev hX rfl
      | (obtain ⟨h1, rfl⟩ := hX
         exact GlobalTheory.DefConv.posDef_of_node ch.G s.core.lev ⟨h1, le_rfl⟩ (by simp [Node.neg]))
  have := GlobalTheory.RowTens.row_invCont ch.W hN (hB.2.1 t y) D.R.m le_rfl _
    fun k : Fin D.R.m => GlobalTheory.RowTens.fock_theta ch.W _ (hf k) (P k)
  exact ⟨this.2, this.1⟩

end GlobalTheory.FockRed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodReductionToFockVectorsLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodReductionToFockVectors_large_depth : Big fun ch => FockAt ch := by
  first | exact @GlobalTheory.FockRed.fockAt_big | exact GlobalTheory.FockRed.fockAt_big | (intros; apply GlobalTheory.FockRed.fockAt_big <;> assumption)
end
