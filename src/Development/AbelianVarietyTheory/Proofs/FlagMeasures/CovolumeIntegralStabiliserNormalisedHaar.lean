module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ChartCG
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatLinkPoints
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LatBAsm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinates
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitriangularFramesGramEqCellPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StMatIntIff
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserIffRationalCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInvPowDifferentIffLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInvPowDifferentIffLocal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.HL
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BBTie

namespace GlobalTheory.DiffLoc

theorem ddS_ne (D : D7) : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · exact FaithfulSMul.algebraMap_injective _ _

theorem mem_ddPow_neg_iff : ∀ (D : D7) (Z : LocDat D) (n : ℕ), n ≤ D.R.rS → ∀ y : D.host.E,
    y ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔
      ∀ p : PlF D, (D.s.atP p).ιE y * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) *
        (D.s.atP p).ιE (uP p : D.host.E)) ^ n ∈ (Z.M p).L.O := by
  intro D Z n hn y
  let a : Fin (D.R.rS + 1) := ⟨D.R.rS - n, by omega⟩
  have he : ((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = n := by
    show ((D.R.rS : ℤ) - ((D.R.rS - n : ℕ) : ℤ)) = n
    rw [Nat.cast_sub hn]; ring
  have hspan : ∀ p : PlF D, Submodule.span (Z.M p).L.O ((D.s.atP p).ιE ''
      ((ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)) =
      Submodule.span (Z.M p).L.O {frFac Z.δ p a} := by
    intro p
    have h := locDiffC_holds D Z p a
    rw [he] at h
    exact h
  have hf : ∀ p : PlF D, frFac Z.δ p a * btT Z p ^ n = 1 := by
    intro p
    rw [bt_frFac_eq Z p a]
    have hk : D.R.rS - a.val = n := by show D.R.rS - (D.R.rS - n) = n; omega
    rw [hk]
    set U := (bt_T_unit Z p).unit
    have hU : (U : (D.s.atP p).Ep) = btT Z p := IsUnit.unit_spec _
    rw [← hU, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
  have hinv : ∀ z : D.host.E, z ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔
      ∀ d ∈ ddS D ^ n, z * d ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro z
    rw [zpow_neg, zpow_natCast, FractionalIdeal.mem_inv_iff (pow_ne_zero n (ddS_ne D))]
  constructor
  · intro hy p
    have hm : (D.s.atP p).ιE y ∈ Submodule.span (Z.M p).L.O {frFac Z.δ p a} := by
      rw [← hspan p]; exact Submodule.subset_span ⟨y, hy, rfl⟩
    obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 hm
    change (D.s.atP p).ιE y * btT Z p ^ n ∈ (Z.M p).L.O
    rw [← ho, Subring.smul_def, smul_eq_mul, mul_assoc, hf p, mul_one]
    exact o.2
  · intro h
    rw [hinv]
    intro d hd
    rw [FractionalIdeal.mem_one_iff]
    have hloc : ∀ p : PlF D, (D.s.atP p).ιE (y * d) ∈ (Z.M p).L.O := by
      intro p
      have hmem : ∀ x ∈ Submodule.span (Z.M p).L.O ((D.s.atP p).ιE ''
          ((ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)),
          (D.s.atP p).ιE d * x ∈ (Z.M p).L.O := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨z, hz, rfl⟩ := hx
          obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 ((hinv z).1 hz d hd)
          rw [← map_mul, mul_comm, ← ho]
          exact bt_iota_int Z p o
        | zero => rw [mul_zero]; exact Subring.zero_mem _
        | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
        | smul o x _ hx => rw [Subring.smul_def, smul_eq_mul, mul_left_comm]; exact mul_mem o.2 hx
      have hdf : (D.s.atP p).ιE d * frFac Z.δ p a ∈ (Z.M p).L.O :=
        hmem _ (by rw [hspan p]; exact Submodule.subset_span (Set.mem_singleton _))
      have hyp : (D.s.atP p).ιE y * btT Z p ^ n ∈ (Z.M p).L.O := h p
      have e : (D.s.atP p).ιE (y * d) =
          ((D.s.atP p).ιE y * btT Z p ^ n) * ((D.s.atP p).ιE d * frFac Z.δ p a) := by
        calc (D.s.atP p).ιE (y * d) = (D.s.atP p).ιE y * (D.s.atP p).ιE d * (frFac Z.δ p a * btT Z p ^ n) := by
              rw [hf p, mul_one, map_mul]
          _ = _ := by ring
      rw [e]
      exact mul_mem hyp hdf
    obtain ⟨o, ho⟩ := ((GlobalTheory.HL.PlacesInt.integers_local (placesOf Z)).1 (y * d)).1 hloc
    exact ⟨o, ho⟩

end GlobalTheory.DiffLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInvPowDifferentIffLocalStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.HL
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_inv_pow_different_iff_local : ∀ (D : D7) (Z : LocDat D) (n : ℕ), n ≤ D.R.rS → ∀ y : D.host.E, y ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔ ∀ p : PlF D, (D.s.atP p).ιE y * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^ n ∈ (Z.M p).L.O := by
  first | exact @GlobalTheory.DiffLoc.mem_ddPow_neg_iff | exact GlobalTheory.DiffLoc.mem_ddPow_neg_iff | (intros; apply GlobalTheory.DiffLoc.mem_ddPow_neg_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemStabilizerSpanIffUnitriangularIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemStabilizerSpanIffUnitriangularIntegral
open Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise

namespace GlobalTheory.HL

theorem span_pointwise_le_of_int {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N m : ℕ} (v : Fin m → Fin N → E)
    (h : (Fin N → E) ≃ₗ[E] (Fin N → E)) (M : Matrix (Fin m) (Fin m) E) (hM : IsIntM L M)
    (hv : ∀ b, h (v b) = ∑ a, M a b • v a) :
    h • Submodule.span L.O (Set.range v) ≤ Submodule.span L.O (Set.range v) := by
  rw [Submodule.smul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  show h (v b) ∈ _
  rw [hv b]
  refine Submodule.sum_mem _ fun a _ => ?_
  have : M a b • v a = (⟨M a b, hM a b⟩ : L.O) • v a := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem unistab_iff : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N m : ℕ} (v : Fin m → Fin N → E), LinearIndependent E v → ∀ (g : (Fin N → E) ≃ₗ[E] (Fin N → E)) (M : Matrix (Fin m) (Fin m) E), IsUni M → (∀ b, g (v b) = ∑ a, M a b • v a) → (g ∈ MulAction.stabilizer ((Fin N → E) ≃ₗ[E] (Fin N → E)) (Submodule.span L.O (Set.range v)) ↔ IsIntM L M) := by
  intro F _ _ _ E _ _ _ L N m v hli g M hU hg
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hst a b
    have hmem : g (v b) ∈ Submodule.span L.O (Set.range v) := by
      rw [← hst]
      exact Submodule.smul_mem_pointwise_smul (v b) g _ (Submodule.subset_span ⟨b, rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hmem
    rw [hg b] at hc
    have h0 : ∑ i, (M i b - (c i : E)) • v i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hc]
      simp [Subring.smul_def]
    have := (Fintype.linearIndependent_iff.1 hli) _ h0 a
    rw [sub_eq_zero] at this
    rw [this]
    exact (c a).2
  · intro hM
    have hdet : M.det = 1 := by
      rw [Matrix.det_of_upperTriangular (fun i j hij => hU.1 i j hij)]
      simp [hU.2]
    let M₀ : Matrix (Fin m) (Fin m) L.O := fun i j => ⟨M i j, hM i j⟩
    have hM₀ : M₀.map L.O.subtype = M := by ext i j; rfl
    have hadj : IsIntM L M.adjugate := by
      intro i j
      have e := congrFun (congrFun (RingHom.map_adjugate L.O.subtype M₀) i) j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at e
      rw [hM₀] at e
      rw [← e]
      exact (M₀.adjugate i j).2
    have hinv : ∀ b, g⁻¹ (v b) = ∑ a, M.adjugate a b • v a := by
      intro b
      have key : g (∑ a, M.adjugate a b • v a) = v b := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, hg, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        have : ∀ c, ∑ a, (M.adjugate a b * M c a) • v c = (M * M.adjugate) c b • v c := by
          intro c
          rw [← Finset.sum_smul, Matrix.mul_apply]
          congr 1
          exact Finset.sum_congr rfl fun a _ => mul_comm _ _
        simp only [this, Matrix.mul_adjugate, hdet, one_smul]
        simp [Matrix.one_apply]
      rw [← key]
      exact g.symm_apply_apply _
    apply le_antisymm
    · exact span_pointwise_le_of_int L v g M hM hg
    · intro x hx
      have hx' : g⁻¹ • x ∈ Submodule.span L.O (Set.range v) :=
        span_pointwise_le_of_int L v g⁻¹ M.adjugate hadj hinv
          (Submodule.smul_mem_pointwise_smul x g⁻¹ _ hx)
      have := Submodule.smul_mem_pointwise_smul (g⁻¹ • x) g _ hx'
      rwa [smul_inv_smul] at this

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemStabilizerSpanIffUnitriangularIntegralStatement
open Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_stabilizer_span_iff_unitriangular_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N m : ℕ} (v : Fin m → Fin N → E), LinearIndependent E v → ∀ (g : (Fin N → E) ≃ₗ[E] (Fin N → E)) (M : Matrix (Fin m) (Fin m) E), IsUni M → (∀ b, g (v b) = ∑ a, M a b • v a) → (g ∈ MulAction.stabilizer ((Fin N → E) ≃ₗ[E] (Fin N → E)) (Submodule.span L.O (Set.range v)) ↔ IsIntM L M) := by
  first | exact @GlobalTheory.HL.unistab_iff | exact GlobalTheory.HL.unistab_iff | (intros; apply GlobalTheory.HL.unistab_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserIffRationalCoords
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.StabIntCoord

theorem mem_maxUnramifiedSubfield_conj_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) (r k : ℕ) (S : Frames L r k)
    (x : S.GLV) (hx : x ∈ S.St) (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : IsUni s) (hs' : IsUni s')
    (h1 : ∀ j, x (S.f j) = ∑ i, s i j • S.f i) (h2 : ∀ j, x (S.f' j) = ∑ i, s' i j • S.f' i) :
    x ∈ S.K0 ↔ IsIntM L s' := by
  have heq := ((GlobalTheory.HL.FrameStab.stab_eq L r k S).2 s s' hs hs').2 ⟨x, hx, h1, h2⟩
  have hint := ((GlobalTheory.HL.BlockStab.stabiliser_blockDiag L r k S).1 s s' hs hs' heq).2
  have hli := (GlobalTheory.FrameBasic.main L r k S).1
  have hl1 : LinearIndependent E S.f := hli.comp Sum.inl Sum.inl_injective
  have hl2 : LinearIndependent E S.f' := hli.comp Sum.inr Sum.inr_injective
  have e1 := GlobalTheory.T.mem_stabilizer_span_iff_unitriangular_integral L S.f hl1 x s hs h1
  have e2 := GlobalTheory.T.mem_stabilizer_span_iff_unitriangular_integral L S.f' hl2 x s' hs' h2
  unfold Frames.K0
  simp only [Subgroup.mem_inf]
  rw [e1, e2, hint]
  tauto

end GlobalTheory.HL.StabIntCoord

namespace GlobalTheory.HL.StabIntCoord

open IsDedekindDomain

theorem loc_act {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    (A : Places F E sig) {n r : ℕ} (p : HeightOneSpectrum (𝓞 F)) (c : ((A.loc p).Fp)ˣ)
    (x : (Fin n → E) ≃ₗ[E] (Fin n → E)) (g' : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))
    (hE : A.Ext p x g') (v : Fin (r + 1) → Fin n → E) (vl : Fin (r + 1) → Fin n → (A.loc p).Ep)
    (hv : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - (a : ℕ))) • vl a = A.bc p (v a))
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hM : ∀ b : Fin (r + 1), x (v b) = ∑ a, M a b • v a) (b : Fin (r + 1)) :
    g' (vl b) = ∑ a : Fin (r + 1), (algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - (a : ℕ)) /
      (c : (A.loc p).Fp) ^ (r - (b : ℕ))) * (A.loc p).ιE (M a b)) • vl a := by
  have hc : ∀ m : ℕ, ((c : (A.loc p).Fp) ^ m) ≠ 0 := fun m => pow_ne_zero _ c.ne_zero
  have hvl : ∀ a : Fin (r + 1), vl a = algebraMap (A.loc p).Fp (A.loc p).Ep (((c : (A.loc p).Fp) ^ (r - (a : ℕ)))⁻¹) • A.bc p (v a) := by
    intro a
    rw [← hv a, smul_smul, ← map_mul, inv_mul_cancel₀ (hc _), map_one, one_smul]
  have hbc : ∀ (l : Fin (r + 1) → E) (w : Fin (r + 1) → Fin n → E),
      A.bc p (∑ a, l a • w a) = ∑ a, (A.loc p).ιE (l a) • A.bc p (w a) := by
    intro l w
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Places.bc, Finset.sum_apply, map_sum, smul_eq_mul, map_mul]
  rw [hvl b, map_smul, hE, hM b, hbc, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hv a, smul_smul, smul_smul]
  congr 1
  rw [div_eq_mul_inv, map_mul]
  ring

end GlobalTheory.HL.StabIntCoord

namespace GlobalTheory.HL.StabIntCoord


set_option maxHeartbeats 1000000 in
theorem integralStabiliser_iff_rational_coords_alt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ x ∈ G.St, ∀ B : Formalism.L2.SG.PairVal.MatR D, (∀ b, x (G.f' b) = ∑ a, B a b • G.f' a) → (x ∈ G.K0 ↔ ∀ a b : Fin (D.R.rS + 1), a < b → B a b ∈ ((ddS D ^ (-((b : ℤ) - (a : ℤ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))) := by
  intro D X Y u u' _ _ w F00 F'0 FP _ _ _ G c x hx B hB
  obtain ⟨s, s', hs, hs', hsf, hsf'⟩ := GlobalTheory.T.globalFrameStabilizer_acts_unitriangular _ _ _ G x hx
  have key : ∀ p : PlF D, (∃ g' ∈ (G.S p).K0, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p x g') ↔
      ∀ a b : Fin (D.R.rS + 1), a < b → (D.s.atP p).ιE (B a b) * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Y.δ p) *
        (D.s.atP p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) ∈ (Y.M p).L.O := by
    intro p
    haveI := (D.s.atP p).lf
    haveI := (D.s.atP p).char0
    haveI : IsNonarchimedeanLocalField ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp := (D.s.atP p).lf
    haveI : CharZero ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp := (D.s.atP p).char0
    obtain ⟨xp, hxp, hExt⟩ := hx p
    have huniq := ((GlobalTheory.HL.RatExt.rational_extend (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ p).2.2.1 x)
    have hK : (∃ g' ∈ (G.S p).K0, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p x g') ↔ xp ∈ (G.S p).K0 := by
      constructor
      · rintro ⟨g', hg', hgE⟩
        rwa [huniq.unique hExt hgE]
      · intro h; exact ⟨xp, h, hExt⟩
    rw [hK]
    have h1 := loc_act (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) p (G.c p) x xp hExt G.f (G.S p).f (G.f_eq p) s hsf
    have h2 := loc_act (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) p (G.c p) x xp hExt G.f' (G.S p).f' (G.f'_eq p) s' hsf'
    have h3 := loc_act (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) p (G.c p) x xp hExt G.f' (G.S p).f' (G.f'_eq p) B hB
    have hceq : algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (G.c p).val = algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (Y.δ p) *
        ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (uP p : D.host.E) := c.c_eq p
    show _ ↔ ∀ a b : Fin (D.R.rS + 1), a < b → ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (B a b) * (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (Y.δ p) *
        ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) ∈ (Y.M p).L.O
    have hcne : ∀ m : ℕ, ((G.c p).val ^ m) ≠ 0 := fun m => pow_ne_zero _ (G.c p).ne_zero
    have huni : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsUni M →
        IsUni (fun a b : Fin (D.R.rS + 1) => algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep
          ((G.c p).val ^ (D.R.rS - (a : ℕ)) / (G.c p).val ^ (D.R.rS - (b : ℕ))) *
            ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (M a b)) := by
      intro M hM
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · simp [hM.1 i j hij]
      · simp [hM.2 i, div_self (hcne _)]
    rw [mem_maxUnramifiedSubfield_conj_iff _ _ _ (G.S p) xp hxp _ _ (huni s hs) (huni s' hs') h1 h2]
    have hli : LinearIndependent ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (G.S p).f' :=
      (GlobalTheory.FrameBasic.main _ _ _ (G.S p)).1.comp Sum.inr Sum.inr_injective
    have hsB : ∀ a b, ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (s' a b) = ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (B a b) := by
      intro a b
      have e := (h2 b).symm.trans (h3 b)
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at e
      simp_rw [← sub_smul] at e
      have h0 := Fintype.linearIndependent_iff.1 hli _ e a
      have hu : IsUnit (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep
          ((G.c p).val ^ (D.R.rS - (a : ℕ)) / (G.c p).val ^ (D.R.rS - (b : ℕ)))) :=
        (isUnit_iff_ne_zero.2 (div_ne_zero (hcne _) (hcne _))).map _
      rw [← mul_sub, hu.mul_right_eq_zero, sub_eq_zero] at h0
      exact h0
    have hent : ∀ a b : Fin (D.R.rS + 1), a < b → algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep
        ((G.c p).val ^ (D.R.rS - (a : ℕ)) / (G.c p).val ^ (D.R.rS - (b : ℕ))) *
          ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (s' a b) = ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (B a b) * (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (Y.δ p) *
            ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) := by
      intro a b hab
      have hab' : (a : ℕ) < b := hab
      have hb := b.isLt
      rw [show D.R.rS - (a : ℕ) = (D.R.rS - b) + ((b : ℕ) - a) by omega, pow_add,
        mul_div_cancel_left₀ _ (hcne _), map_pow, hceq, hsB, mul_comm]
    constructor
    · intro h a b hab
      rw [← hent a b hab]
      exact h a b
    · intro h a b
      rcases lt_trichotomy a b with hab | rfl | hab
      · beta_reduce
        rw [hent a b hab]
        exact h a b hab
      · show _ ∈ _
        simp [hs'.2 a, div_self (hcne _)]
      · show _ ∈ _
        simp [hs'.1 a b hab]
  have hK0 : x ∈ G.K0 ↔ ∀ p, ∃ g' ∈ (G.S p).K0, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p x g' := Iff.rfl
  rw [hK0, forall_congr' key]
  have hI : ∀ a b : Fin (D.R.rS + 1), a < b → (B a b ∈ ((ddS D ^ (-((b : ℤ) - (a : ℤ))) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔
      ∀ p : PlF D, (D.s.atP p).ιE (B a b) * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Y.δ p) *
        (D.s.atP p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) ∈ (Y.M p).L.O) := by
    intro a b hab
    have hab' : (a : ℕ) < b := hab
    have hb := b.isLt
    have hn : (b : ℕ) - (a : ℕ) ≤ D.R.rS := by omega
    have e : (-((b : ℤ) - (a : ℤ))) = -((((b : ℕ) - (a : ℕ) : ℕ)) : ℤ) := by
      rw [Nat.cast_sub hab'.le]
    rw [e]
    exact GlobalTheory.T.mem_inv_pow_different_iff_local D ⟨Y.δ, Y.M, Y.agree⟩ _ hn (B a b)
  constructor
  · intro h a b hab
    exact (hI a b hab).2 fun p => h p a b hab
  · intro h p a b hab
    exact (hI a b hab).1 (h a b hab) p

end GlobalTheory.HL.StabIntCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserIffRationalCoordsStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralStabiliser_iff_rational_coords : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ x ∈ G.St, ∀ B : Formalism.L2.SG.PairVal.MatR D, (∀ b, x (G.f' b) = ∑ a, B a b • G.f' a) → (x ∈ G.K0 ↔ ∀ a b : Fin (D.R.rS + 1), a < b → B a b ∈ ((ddS D ^ (-((b : ℤ) - (a : ℤ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))) := by
  first | exact @GlobalTheory.HL.StabIntCoord.integralStabiliser_iff_rational_coords_alt | exact GlobalTheory.HL.StabIntCoord.integralStabiliser_iff_rational_coords_alt | (intros; apply GlobalTheory.HL.StabIntCoord.integralStabiliser_iff_rational_coords_alt <;> assumption)
end
end

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.StIntLat

theorem stMat_int_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ y : InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ, (∃ x ∈ G.K0, y = fun v p => Formalism.L2.SG.Pf.VolPinAsm.phiV X v (GlobalTheory.HL.TraceConjugationCover.stMat G x p.1.1 p.1.2)) ↔ ∀ p : Formalism.L2.SG.RealObj.FreeE w, (fun v => y v p) ∈ ((((ddS D ^ (-(((p.1.2.val - p.1.1.val : ℕ)) : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup).map (Formalism.L2.SG.NGCut.SplitEmbedding.embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) 1)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAB G c y
  have hT : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u').ne'
  have hli : LinearIndependent D.host.E G.f' := by
    have h0 : LinearIndependent D.host.E (frame F'0) := Formalism.L2.SG.Pf.StabilizerIndexVolumes.frame_indep F'0.fl hT
    have h1 := h0.map' (c.e : (VS D).V →ₗ[D.host.E] G.V) c.e.ker
    have e : G.f' = (c.e : (VS D).V →ₗ[D.host.E] G.V) ∘ frame F'0 := by
      funext a; exact c.f'_eq a
    rw [e]; exact h1
  have hStCo := GlobalTheory.T.rationalCommonStabiliser_unitriangular_coords D X Y u u' hSt hk w F00 F'0 FP hZ hG hAB G c
  have hK := GlobalTheory.T.integralStabiliser_iff_rational_coords D X Y u u' hSt hk w F00 F'0 FP hZ hG hAB G c
  have hexp : ∀ a b : Fin (D.R.rS + 1), a < b →
      (-(((b.val - a.val : ℕ)) : ℤ)) = -((b : ℤ) - (a : ℤ)) := by
    intro a b hab
    have : a.val ≤ b.val := le_of_lt hab
    rw [Nat.cast_sub this]
  constructor
  · rintro ⟨x, hx, rfl⟩ p
    have hxSt : x ∈ G.St := by
      intro q
      obtain ⟨g', hg', he⟩ := hx q
      exact ⟨g', hg'.1.1, he⟩
    obtain ⟨B, -, hB, -⟩ := hStCo.1 x hxSt
    have hspec := GlobalTheory.HL.TraceConjugationCover.stMat_spec G x ⟨B, hB⟩
    have hmem := (hK x hxSt _ hspec).1 hx p.1.1 p.1.2 p.2.1
    refine ⟨GlobalTheory.HL.TraceConjugationCover.stMat G x p.1.1 p.1.2, ?_, ?_⟩
    · rw [hexp _ _ p.2.1]; exact hmem
    · funext v; simp [Formalism.L2.SG.NGCut.SplitEmbedding.embS]
  · intro h
    choose lam hlam hlamE using h
    let B : Formalism.L2.SG.PairVal.MatR D := fun a b =>
      if a = b then 1 else if hab : a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1
        then lam ⟨(a, b), hab⟩ else 0
    have hBU : IsUpUni B := by
      intro i j
      refine ⟨fun hji => ?_, fun hij => ?_⟩
      · have h1 : i ≠ j := fun h => (lt_irrefl j) (h ▸ hji)
        have h2 : ¬ (i < j ∧ Formalism.L2.SG.RealObj.blkOf w.1 i.1 = Formalism.L2.SG.RealObj.blkOf w.1 j.1) := fun h => (lt_asymm hji) h.1
        simp only [B, if_neg h1, dif_neg h2]
      · simp only [B, if_pos hij]
    have hBblk : ∀ a b : Fin (D.R.rS + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 →
        B a b = 0 := by
      intro a b hne
      have h1 : a ≠ b := fun h => hne (h ▸ rfl)
      have h2 : ¬ (a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1) := fun h => hne h.2
      simp only [B, if_neg h1, dif_neg h2]
    obtain ⟨x, ⟨hxSt, hxB⟩, -⟩ := hStCo.2 B hBU hBblk
    have hxK : x ∈ G.K0 := by
      refine (hK x hxSt B hxB).2 fun a b hab => ?_
      have h1 : a ≠ b := ne_of_lt hab
      by_cases h2 : a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1
      · simp only [B, if_neg h1, dif_pos h2]
        have := hlam ⟨(a, b), h2⟩
        rw [hexp _ _ hab] at this
        exact this
      · simp only [B, if_neg h1, dif_neg h2]
        exact FractionalIdeal.mem_coe.1 (Submodule.zero_mem _)
    have hspec := GlobalTheory.HL.TraceConjugationCover.stMat_spec G x ⟨B, hxB⟩
    have hM : GlobalTheory.HL.TraceConjugationCover.stMat G x = B := by
      funext a b
      have e2 : ∑ d, (GlobalTheory.HL.TraceConjugationCover.stMat G x d b - B d b) • G.f' d = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, ← hspec b, ← hxB b, sub_self]
      exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ e2 a)
    refine ⟨x, hxK, ?_⟩
    funext v p
    have e1 := congrFun (hlamE p) v
    simp only [Formalism.L2.SG.NGCut.SplitEmbedding.embS, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_mul] at e1
    rw [hM, ← e1]
    have h1 : p.1.1 ≠ p.1.2 := ne_of_lt p.2.1
    simp only [B, if_neg h1, dif_pos p.2]
    all_goals first | rfl | (congr 1)

end GlobalTheory.HL.StIntLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralStabiliserNormalisedHaar
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.Cov0


open Formalism.L2.SG.RealObj Formalism.L2.S.Pv.Chart Formalism.MainNotions.S.ThB Formalism.L2.SG.LocWSOf in
theorem chart_of {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : TauC Y u u')
    (w : Point D.host.E (D.R.rS + 1)) (γw s s' : X.B.I.Ginf) (hrep : IsPtRep X u u' w γw) (hs : s ∈ X.SinfU u)
    (hs' : s' ∈ X.SinfU u') (hpt : t.pt.1 = s * γw * s'⁻¹) :
    ∃ BX : FreeE w → (FreeE w → ℂ) → (FreeE w → ℂ) → ℂ,
        (∀ p, Measurable (fun z : (FreeE w → ℂ) × (FreeE w → ℂ) => BX p z.1 z.2)) ∧
        (∀ p (x x' y y' : FreeE w → ℂ), (∀ q, Formalism.L2.SG.NGCut.StabilizerCovolume.ht q < Formalism.L2.SG.NGCut.StabilizerCovolume.ht p →
          x q = x' q ∧ y q = y' q) → BX p x y = BX p x' y') ∧
        (∀ p (x : FreeE w → ℂ), BX p x 0 = 0) ∧
        Measurable (stCoord X u' w γw) ∧
        MeasurableSet (StInf X u u' γw) ∧
        Set.InjOn (stCoord X u' w γw) (StInf X u u' γw) ∧
        (∀ x, ∃ z ∈ StInf X u u' γw, stCoord X u' w γw z = x) ∧
        (∀ z₁ ∈ StInf X u u' γw, ∀ z₂ ∈ StInf X u u' γw,
          z₁ * z₂ ∈ StInf X u u' γw ∧
          stCoord X u' w γw (z₁ * z₂) =
            Formalism.L2.SG.NGCut.SplitEmbedding.lawX BX (stCoord X u' w γw z₁) (stCoord X u' w γw z₂)) ∧
        (∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, s⁻¹ * r * s ∈ StInf X u u' γw) := by
  have : Nonempty D.what₂.Word := ⟨u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  have hτ : ∀ v : InfinitePlace X.B.I.F, ∃ τ, vOf X τ = v := fun v => ⟨X.pl v, X.pl.symm_apply_apply v⟩
  have hpl : ∀ z ∈ StInf X u u' γw, ∀ v, z v ∈ Formalism.L2.SG.NGPin.StV X u u' γw v := by
    intro z hz v
    rw [Formalism.L2.SG.NGPin.stInf_eq_pi] at hz
    exact hz v (Set.mem_univ _)
  refine ⟨BX, fun p => BX_measurable p, fun p x x' y y' h => BX_lower p x x' y y' h, fun p x => BX_zero p x,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Formalism.L2.SG.NGPin.stCoord_eq]
    refine Measurable.of_eval fun v => ?_
    obtain ⟨τ, rfl⟩ := hτ v
    exact (stCoordV_meas C u' w γw τ).comp (measurable_pi_apply _)
  · rw [Formalism.L2.SG.NGPin.stInf_eq_pi]
    exact MeasurableSet.univ_pi fun v => (isClosed_stV X u u' γw v).measurableSet
  · intro z₁ h₁ z₂ h₂ heq
    rw [Formalism.L2.SG.NGPin.stCoord_eq] at heq
    funext v
    obtain ⟨τ, rfl⟩ := hτ v
    exact stCoordV_inj C u u' w γw τ hrep (hpl z₁ h₁ _) (hpl z₂ h₂ _) (congrFun heq (vOf X τ))
  · intro x
    have hex : ∀ v, ∃ y ∈ Formalism.L2.SG.NGPin.StV X u u' γw v,
        Formalism.L2.SG.NGPin.stCoordV X u' w γw v y = x v := by
      intro v
      obtain ⟨τ, rfl⟩ := hτ v
      exact stCoordV_surj C u u' w γw τ hrep (x (vOf X τ))
    choose y hy hyx using hex
    refine ⟨y, ?_, ?_⟩
    · rw [Formalism.L2.SG.NGPin.stInf_eq_pi]; exact fun v _ => hy v
    · rw [Formalism.L2.SG.NGPin.stCoord_eq]; funext v; exact hyx v
  · intro z₁ h₁ z₂ h₂
    refine ⟨?_, ?_⟩
    · have hN := Formalism.L2.SG.Pf.psiInfChar_holds D X u
      have hN' := Formalism.L2.SG.Pf.psiInfChar_holds D X u'
      refine ⟨(hN.2.1 _ h₁.1 _ h₂.1).1, ?_⟩
      have e : γw⁻¹ * (z₁ * z₂) * γw = (γw⁻¹ * z₁ * γw) * (γw⁻¹ * z₂ * γw) := by group
      rw [e]
      exact (hN'.2.1 _ h₁.2 _ h₂.2).1
    · rw [Formalism.L2.SG.NGPin.stCoord_eq]
      funext v p
      exact stCoordV_mul X v (hpl z₁ h₁ v) (hpl z₂ h₂ v) p
  · intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    refine ⟨?_, ?_⟩
    · have := Formalism.L2.SG.Pf.FormTranspose.sinf_conj X u (Formalism.L2.SG.Pf.Sinf.sinf_inv' X u hs) hr1
      simpa only [inv_inv] using this
    · have hγ : γw = s⁻¹ * t.pt.1 * s' := by rw [hpt]; group
      have := Formalism.L2.SG.Pf.FormTranspose.sinf_conj X u' (Formalism.L2.SG.Pf.Sinf.sinf_inv' X u' hs') hr2
      rw [hγ]
      convert this using 1
      group

end GlobalTheory.HL.Cov0

end

noncomputable section
namespace GlobalTheory.HL.Cov0

theorem const_entry : ∀ (D : D7) (X : HidaSetting D) (h : ℕ), ddS D ≠ 0 ∧ (D.host.ka / (X.B.g : ℝ) / Real.pi) ^ Fintype.card (InfinitePlace X.B.I.F) * ((FractionalIdeal.absNorm (ddS D ^ (-(h : ℤ))) : ℚ) : ℝ) * 2⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) * √|(discr D.host.E : ℝ)| * ((D.host.rdE : ℝ) ^ h) ^ (2 * Fintype.card (InfinitePlace X.B.I.F)) = ((X.B.g : ℝ) ^ D.R.f)⁻¹ := by
  intro D X h
  have hrd : 0 < D.host.rdE := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
  have hN := GlobalTheory.RealPlaces.absNorm_ddS D
  have hdd : ddS D ≠ 0 := by
    intro h0
    rw [h0, map_zero, Rat.cast_zero] at hN
    exact (pow_pos hrd _).ne' hN.symm
  refine ⟨hdd, ?_⟩
  rw [Formalism.L2.SG.LatBAsm.factor_eq X _ h, map_zpow₀, Rat.cast_zpow, hN]
  have hg : (0 : ℝ) < X.B.g := by
    rw [X.g_eq]
    exact_mod_cast Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  rw [zpow_neg, zpow_natCast, ← pow_mul]
  field_simp

end GlobalTheory.HL.Cov0
end

noncomputable section
namespace GlobalTheory.HL.Cov0

theorem grp_conj {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (D.sp.Y 0) D.R.rS T} {F0' : LFlag (D.sp.Y 0) D.R.rS T'}
    {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k}
    (c : GCoord Z F0 F0' FP G) (ρ t n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    c.grp (ρ * t) (t⁻¹ * n * t) = c.grp ρ n := LinearEquiv.ext fun x => by
  simp only [GCoord.grp, LinearEquiv.trans_apply, LinearEquiv.mul_apply, LinearEquiv.symm_trans_apply]
  show c.e (ρ (t (t.symm (n (t (t.symm (ρ.symm (c.e.symm x)))))))) = _
  simp

theorem realPoints_integralIsometries_subset_stabilizer : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → ∀ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, c.grp ρ n ∈ G.K0 → (∃ x, RatLink X x n) ∧ ∀ x, RatLink X x n → x.1 ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀ := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv hrel n hn
  have hgrp := GlobalTheory.HL.GrpCoord.grp_coords D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv
  have hL := GlobalTheory.RatIsomPoint.ratLink_points D X
  have hN : c.grp ρ n ∈ G.N := fun p => by
    obtain ⟨g', hg', hext⟩ := hn p
    exact ⟨g', hg'.1.1.1, hext⟩
  have hN' : c.grp ρ n ∈ G.N' := fun p => by
    obtain ⟨g', hg', hext⟩ := hn p
    exact ⟨g', hg'.1.1.2, hext⟩
  have hnR : n ∈ NRat (lf D (X.Fu u)) := (hgrp.1 n).2 hN
  have hmR : t₀.lin⁻¹ * n * t₀.lin ∈ NRat (lf D (X.Fu u')) :=
    (hgrp.2.1 _).2 (by rw [grp_conj]; exact hN')
  obtain ⟨x0, hx0, -⟩ := hL.1 n hnR.1
  refine ⟨⟨x0, hx0⟩, fun x hx => ⟨(hL.2.2 u x n hx).1.1 hnR, ?_⟩⟩
  have htl : RatLink X t₀.pt t₀.lin := t₀.rep.2.1
  have h1 := (hL.2.1 _ _ _ _ ((hL.2.1 _ _ _ _ htl htl).2.1) hx).1
  have h2 := (hL.2.1 _ _ _ _ h1 htl).1
  exact (hL.2.2 u' _ _ h2).1.1 hmR

end GlobalTheory.HL.Cov0
end

noncomputable section
namespace GlobalTheory.HL.Cov0


open Formalism.L2.SG.NGCut.SplitEmbedding Formalism.L2.SG.NGCut.StabilizerCovolume Formalism.L2.SG.RealObj in
theorem covolume_integralStabiliser_normalisedHaar_alt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → ∀ μR, Formalism.L2.SG.VolPin.IsPinnedR t₀ w μR → ∃ K : Set X.B.I.Ginf, (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀, ∃! s, s ∈ realPts X {σ | c.grp ρ σ ∈ G.K0} ∧ s * y ∈ K) ∧ μR K = ENNReal.ofReal (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv hrel μR hPin
  obtain ⟨γw, s, s', μw, hIs, hs, hs', hpt, hHaar, hmap, rfl⟩ := hPin
  obtain ⟨BX, hBm, hBd, hB0, hstm, hStm, hinj, hsurj, hmul, hconj⟩ :=
    chart_of X Y u u' t₀ w γw s s' hIs hs hs' hpt
  have hTC := Formalism.MainNotions.InterlacingSignCuts.host_totallyComplex D
  have : IsEmpty {w : InfinitePlace D.host.E // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1)) w.2⟩
  obtain ⟨σι, hφ⟩ := Formalism.L2.SG.LatBAsm.exists_sigma X
  set St := StInf X u u' γw with hStdef
  set sc := stCoord X u' w γw with hscdef
  set φ := Formalism.L2.SG.Pf.VolPinAsm.phiV X with hφdef
  set Γ := realPts X {σ | c.grp ρ σ ∈ G.K0} with hΓdef
  have hT1 := realPoints_integralIsometries_subset_stabilizer D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv hrel
  have hΓR : ∀ y ∈ Γ, y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀ := by
    rintro y ⟨x, n, hx, rfl, hn⟩
    exact (hT1 n hn).2 x hx
  have hgrp_inv : ∀ n, c.grp ρ n⁻¹ = (c.grp ρ n)⁻¹ := fun n => LinearEquiv.ext fun x => rfl
  have hΓinv : ∀ y ∈ Γ, y⁻¹ ∈ Γ := by
    rintro y ⟨x, n, hx, rfl, hn⟩
    refine ⟨x⁻¹, n⁻¹, ((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x x n n hx hx).2.1, rfl, ?_⟩
    show c.grp ρ n⁻¹ ∈ G.K0
    rw [hgrp_inv]; exact G.K0.inv_mem hn
  have hgSt : ∀ y ∈ Γ, s⁻¹ * y * s ∈ St := fun y hy => hconj _ (hΓR y hy)

  obtain ⟨σ, hσn, A, hA, hcoord⟩ :=
    GlobalTheory.HL.CovDict.dict_coords D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv hrel γw s s' hIs hs hs' hpt
  have hT4 := GlobalTheory.HL.StIntLat.stMat_int_iff D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c
  have hrd : 0 < (D.host.rdE : ℝ) := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.rd_pos (D := D)
  have hσ0 : ∀ p, σ p ≠ 0 := fun p h => by
    have := hσn p
    rw [h, norm_zero] at this
    exact (pow_pos hrd _).ne' this.symm
  have hAu : ∀ v, Formalism.L2.SG.NGCut.StabilizerCovolume.IsUni ht (A v) := fun v x x' p hxx => hA v x x' p hxx
  choose B hAB hBA hBu using fun v => uni_inv ht (hAu v)
  have hdd : ddS D ≠ 0 := (const_entry D X 0).1
  let I : FreeE w → (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)ˣ :=
    fun p => Units.mk0 (ddS D ^ (-((ht p : ℕ) : ℤ))) (zpow_ne_zero _ hdd)
  let Λ : FreeE w → AddSubgroup D.host.E :=
    fun p => ((I p : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup
  let τ : FreeE w → (InfinitePlace X.B.I.F → FreeE w → ℂ) → (InfinitePlace X.B.I.F → ℂ) :=
    fun p x v => x v p - B v (x v) p
  let Aset : FreeE w → AddSubgroup (InfinitePlace X.B.I.F → ℂ) := fun p => (Λ p).map (embS φ (σ p))
  have hτ : ∀ p (x x' : InfinitePlace X.B.I.F → FreeE w → ℂ),
      (∀ q, ht q < ht p → ∀ v, x v q = x' v q) → τ p x = τ p x' := by
    intro p x x' hxx
    funext v
    have h1 := hBu v (x v) (x' v) p fun r hr => hxx r hr v
    show x v p - B v (x v) p = x' v p - B v (x' v) p
    linear_combination -h1
  have hdiff : ∀ p x, (fun v => x v p) - τ p x = fun v => B v (x v) p := by
    intro p x; funext v; show x v p - (x v p - B v (x v) p) = B v (x v) p; ring
  have hmemiff : ∀ p (z : InfinitePlace X.B.I.F → ℂ),
      (fun v => σ p * z v) ∈ Aset p ↔ z ∈ (Λ p).map (embS φ 1) := by
    intro p z
    simp only [Aset, AddSubgroup.mem_map]
    constructor
    · rintro ⟨a, ha, hae⟩
      refine ⟨a, ha, ?_⟩
      funext v
      have := congrFun hae v
      simp only [Formalism.L2.SG.NGCut.SplitEmbedding.embS, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_mul] at this ⊢
      exact mul_left_cancel₀ (hσ0 p) this
    · rintro ⟨a, ha, hae⟩
      refine ⟨a, ha, ?_⟩
      funext v
      have := congrFun hae v
      simp only [Formalism.L2.SG.NGCut.SplitEmbedding.embS, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_mul] at this ⊢
      rw [this]
  have hset : ∀ x, (∀ p, (fun v => x v p) - τ p x ∈ Aset p) ↔ ∃ y ∈ Γ, x = sc (s⁻¹ * y * s) := by
    intro x
    constructor
    · intro hx
      set y0 : InfinitePlace X.B.I.F → FreeE w → ℂ := fun v p => (σ p)⁻¹ * B v (x v) p with hy0
      have hy0m : ∀ p, (fun v => y0 v p) ∈ (Λ p).map (embS φ 1) := by
        intro p
        rw [← hmemiff]
        have := hx p
        rw [hdiff] at this
        convert this using 1
        funext v
        show σ p * ((σ p)⁻¹ * B v (x v) p) = B v (x v) p
        field_simp [hσ0 p]
      obtain ⟨g, hg, hgy⟩ := (hT4 y0).2 hy0m
      set e := ρ.trans c.e with he
      set n : (VS D).V ≃ₗ[D.host.E] (VS D).V := (e.trans g).trans e.symm with hn
      have hgn : c.grp ρ n = g := by
        apply LinearEquiv.ext; intro z
        show e (e.symm (g (e (e.symm z)))) = g z
        simp
      obtain ⟨x0, hx0⟩ := (hT1 n (by rw [hgn]; exact hg)).1
      refine ⟨x0.1, ⟨x0, n, hx0, rfl, by show c.grp ρ n ∈ G.K0; rw [hgn]; exact hg⟩, ?_⟩
      funext v
      rw [show sc (s⁻¹ * x0.1 * s) v = _ from hcoord x0 n hx0 (by rw [hgn]; exact hg) v, hgn]
      have : (fun p => σ p * φ v (GlobalTheory.HL.TraceConjugationCover.stMat G g p.1.1 p.1.2)) = B v (x v) := by
        funext p
        have := congrFun (congrFun hgy v) p
        simp only [hy0] at this
        rw [← this]
        field_simp [hσ0 p]
      rw [this, hAB v]
    · rintro ⟨y, ⟨x0, n, hx0, rfl, hn⟩, rfl⟩
      intro p
      rw [hdiff]
      have hxv : ∀ v, sc (s⁻¹ * x0.1 * s) v = A v (fun p => σ p * φ v (GlobalTheory.HL.TraceConjugationCover.stMat G (c.grp ρ n) p.1.1 p.1.2)) :=
        fun v => hcoord x0 n hx0 hn v
      have e1 : (fun v => B v (sc (s⁻¹ * x0.1 * s) v) p) =
          fun v => σ p * φ v (GlobalTheory.HL.TraceConjugationCover.stMat G (c.grp ρ n) p.1.1 p.1.2) := by
        funext v; rw [hxv v, hBA v]
      rw [e1, hmemiff]
      exact (hT4 _).1 ⟨c.grp ρ n, hn, rfl⟩ p

  have hBd' : ∀ p (x x' y y' : FreeE w → ℂ), (∀ q, ht q < ht p → x q = x' q ∧ y q = y' q) →
      BX p x y = BX p x' y' := hBd
  have hinv : ∀ γ, (∀ p, (fun v => γ v p) - τ p γ ∈ Aset p) → ∃ γ', (∀ p, (fun v => γ' v p) - τ p γ' ∈ Aset p) ∧
      ∀ x, lawX BX γ' (lawX BX γ x) = x ∧ lawX BX γ (lawX BX γ' x) = x := by
    intro γ hγ
    obtain ⟨y, hy, rfl⟩ := (hset γ).1 hγ
    refine ⟨sc (s⁻¹ * y⁻¹ * s), (hset _).2 ⟨y⁻¹, hΓinv y hy, rfl⟩, fun x => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hsurj x
    have hg1 := hgSt y hy
    have hg2 := hgSt y⁻¹ (hΓinv y hy)
    have h1 := hmul _ hg1 z hz
    have h1' := hmul _ hg2 z hz
    constructor
    · have h2 := hmul _ hg2 _ h1.1
      rw [← h1.2, ← h2.2]
      congr 1; group
    · have h2 := hmul _ hg1 _ h1'.1
      rw [← h1'.2, ← h2.2]
      congr 1; group

  have hfd : ∀ p, ∃ F : Set (InfinitePlace X.B.I.F → ℂ), MeasurableSet F ∧
      ∀ v, ∃! b : Aset p, (b : InfinitePlace X.B.I.F → ℂ) + v ∈ F := by
    intro p
    obtain ⟨F, hF, hFd⟩ := exists_fd D.host.E (InfinitePlace X.B.I.F) φ σι hφ (I p) (Λ p)
      (fun a ha => ha) (by simp [Λ]) (σ p) (hσ0 p)
    refine ⟨F, hF, fun v => ?_⟩
    obtain ⟨a, ha, hau⟩ := hFd v
    refine ⟨⟨embS φ (σ p) a, AddSubgroup.mem_map_of_mem _ a.2⟩, ha, ?_⟩
    rintro ⟨y, hy⟩ hyF
    obtain ⟨a', ha', rfl⟩ := AddSubgroup.mem_map.1 hy
    have := hau ⟨a', ha'⟩ hyF
    apply Subtype.ext
    show embS φ (σ p) a' = embS φ (σ p) a
    rw [show a' = (a : D.host.E) from congrArg Subtype.val this]
  choose F hF hFd using hfd
  set K' : Set (InfinitePlace X.B.I.F → FreeE w → ℂ) := {y | ∀ p, (fun v => y v p) ∈ F p} with hK'def
  have hK'm : MeasurableSet K' := by
    rw [hK'def, Set.ofPred_forall]
    exact MeasurableSet.iInter fun p =>
      (Measurable.of_eval fun v => (measurable_pi_apply p).comp (measurable_pi_apply v)) (hF p)
  have hKd := box_fundX ht BX hBd' τ hτ Aset F hFd
  have hcov := pi_measure_eq_prod_absNorm_mul_sqrt_discr D.host.E (InfinitePlace X.B.I.F) φ σι hφ (FreeE w) ht BX hBm hBd' hB0
    (D.host.ka / (X.B.g : ℝ) / Real.pi) (by
      have e : D.host.ka = Real.pi / (D.host.rdE / 2) := rfl
      rw [e]
      exact div_nonneg (div_nonneg (div_nonneg Real.pi_pos.le (div_nonneg hrd.le zero_le_two)) (Nat.cast_nonneg _))
        Real.pi_pos.le) I Λ (fun p a ha => ha) (fun _ => 1) (by intro p; simp [Λ])
    (fun _ => one_ne_zero) σ hσ0 τ hτ hinv K' hK'm hKd

  have hQm : Measurable (fun y : X.B.I.Ginf => s⁻¹ * y * s) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  set KA := (fun y : X.B.I.Ginf => s⁻¹ * y * s) ⁻¹' (St ∩ sc ⁻¹' K') with hKAdef
  have hKAm : MeasurableSet KA := hQm (hStm.inter (hstm hK'm))
  refine ⟨KA, ⟨hKAm, fun y hy => ?_⟩, ?_⟩
  · set z := s⁻¹ * y * s with hzdef
    have hz : z ∈ St := hconj _ hy
    obtain ⟨γ, ⟨hγΓ, hγK⟩, hγu⟩ := hKd (sc z)
    obtain ⟨y0, hy0, rfl⟩ := (hset γ).1 hγΓ
    refine ⟨y0, ⟨hy0, ?_⟩, ?_⟩
    · show s⁻¹ * (y0 * y) * s ∈ St ∩ sc ⁻¹' K'
      have e : s⁻¹ * (y0 * y) * s = (s⁻¹ * y0 * s) * z := by rw [hzdef]; group
      rw [e]
      have h1 := hmul _ (hgSt y0 hy0) z hz
      exact ⟨h1.1, by show sc _ ∈ K'; rw [h1.2]; exact hγK⟩
    · rintro y1 ⟨hy1, hy1K⟩
      have hK2 : s⁻¹ * (y1 * y) * s ∈ St ∩ sc ⁻¹' K' := hy1K
      have e : s⁻¹ * (y1 * y) * s = (s⁻¹ * y1 * s) * z := by rw [hzdef]; group
      rw [e] at hK2
      have h1 := hmul _ (hgSt y1 hy1) z hz
      have hin : lawX BX (sc (s⁻¹ * y1 * s)) (sc z) ∈ K' := by rw [← h1.2]; exact hK2.2
      have heq := hγu (sc (s⁻¹ * y1 * s)) ⟨(hset _).2 ⟨y1, hy1, rfl⟩, hin⟩
      have hgg : s⁻¹ * y1 * s = s⁻¹ * y0 * s := hinj (hgSt y1 hy1) (hgSt y0 hy0) heq
      have := congrArg (fun g => s * g * s⁻¹) hgg
      simpa [mul_assoc] using this
  · have hs1m : Measurable (fun y : X.B.I.Ginf => s * y * s⁻¹) :=
      ((continuous_const.mul continuous_id).mul continuous_const).measurable
    rw [Measure.map_apply hs1m hKAm]
    have hset' : (fun y : X.B.I.Ginf => s * y * s⁻¹) ⁻¹' KA = St ∩ sc ⁻¹' K' := by
      ext y
      simp only [Set.mem_preimage, hKAdef]
      have e : s⁻¹ * (s * y * s⁻¹) * s = y := by group
      rw [e]
    rw [hset', Set.inter_comm, measure_inter_conull hHaar.2.2.1, ← Measure.map_apply hstm hK'm, hmap]
    unfold Formalism.L2.SG.RealObj.muStab
    rw [hcov]
    have hterm : ∀ p : FreeE w, ENNReal.ofReal ((D.host.ka / (X.B.g : ℝ) / Real.pi) ^ Fintype.card (InfinitePlace X.B.I.F) *
        (((fun _ => 1 : FreeE w → ℕ) p : ℕ) : ℝ) *
        ((FractionalIdeal.absNorm ((I p : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) : ℚ) : ℝ) *
        2⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) * √|(discr D.host.E : ℝ)| *
        ‖σ p‖ ^ (2 * Fintype.card (InfinitePlace X.B.I.F))) = ENNReal.ofReal (((X.B.g : ℝ) ^ D.R.f)⁻¹) := by
      intro p
      congr 1
      have h5 := (const_entry D X (ht p)).2
      rw [hσn p]
      simp only [I, Units.val_mk0, Nat.cast_one, mul_one]
      exact h5
    rw [Finset.prod_congr rfl fun p _ => hterm p, Finset.prod_const, Finset.card_univ,
      ← ENNReal.ofReal_pow (by positivity), inv_pow, ← pow_mul]

end GlobalTheory.HL.Cov0
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralStabiliserNormalisedHaarStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_integralStabiliser_normalisedHaar : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → ∀ μR, Formalism.L2.SG.VolPin.IsPinnedR t₀ w μR → ∃ K : Set X.B.I.Ginf, (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀, ∃! s, s ∈ realPts X {σ | c.grp ρ σ ∈ G.K0} ∧ s * y ∈ K) ∧ μR K = ENNReal.ofReal (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) := by
  first | exact @GlobalTheory.HL.Cov0.covolume_integralStabiliser_normalisedHaar_alt | exact GlobalTheory.HL.Cov0.covolume_integralStabiliser_normalisedHaar_alt | (intros; apply GlobalTheory.HL.Cov0.covolume_integralStabiliser_normalisedHaar_alt <;> assumption)
end
