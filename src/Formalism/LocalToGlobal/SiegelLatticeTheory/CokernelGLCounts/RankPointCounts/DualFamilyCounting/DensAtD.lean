module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AbsNormSmallFinite
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowLatEx
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieLG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RepresentationIndependence.FrameOKMap

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensAtD
open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def EtaLocAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ p : PlF D, (if ∀ x : (D.s.atP p).Ep, x ≠ 0 → IsUnit x then (-1 : ℝ) else 1) = etaF D.host.E D.host.F p.asIdeal

theorem etaLocAt_of_tied {D : Formalism.BasicNotions.D7} (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) : EtaLocAt D := fun p => Formalism.L2.SG.Pf.AlTieLG.etaLoc_of_tied hL p

def DensProdValAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (p : PlF D) (c : ℕ), c ≤ 2 * (D.R.rS + 1) →
      Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[(D.s.atP p).Fp])
                (if ∀ x : (D.s.atP p).Ep, x ≠ 0 → IsUnit x then -1 else 1) D.R.r (2 * (D.R.rS + 1)) c =
        alphaStd D.host.E p.asIdeal D.R.r / alphaStd D.host.E p.asIdeal (D.R.k - 1 - c)

def DensMultIntAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
      ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → Multipliable (densP L δ ϖ (Tn u) (Tn u') Z)

theorem densProdValAt_of {D : Formalism.BasicNotions.D7} (hη : EtaLocAt D) : DensProdValAt D := by
  intro δ M _ p c hc
  obtain ⟨hK, hF, -⟩ := field_dictionary_holds D
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hq := Formalism.L2.SG.Pf.LocModel.resCard_loc (D.s.atP p)
  have hmax : p.asIdeal.IsMaximal := p.isMaximal
  have hpos := alphaStd_pos hK hF hmax (D.R.k - 1 - c)
  rw [eq_div_iff hpos.ne', alpha_split' (K := D.host.E) p.asIdeal (show D.R.k - 1 - c ≤ D.R.r by omega), mul_comm]
  congr 1
  unfold Formalism.L2.SG.DensExact.densProd
  rw [hq, hη p, show D.R.r + 1 - (2 * (D.R.rS + 1) + c) = D.R.k - 1 - c + 1 by omega]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [zpow_neg, zpow_natCast]

theorem densValAt_of (h1 : LocSelfDual) (h2 : GaPlusDiag) {D : Formalism.BasicNotions.D7} (h5 : DensProdValAt D) :
    ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
      ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → ∀ p : PlF D,
          densP L δ ϖ (Tn u) (Tn u') Z p =
            alphaStd D.host.E p.asIdeal D.R.r /
              alphaStd D.host.E p.asIdeal (D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal) := by
  intro δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI p
  obtain ⟨A, a, hAO, hAdet, hG, hc⟩ := h2 D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI p
  have hSD := h1 D δ M hA L p
  obtain ⟨-, -, hUr, -⟩ := perpendicular_definition_holds D u u' hT F0 what₂ hR Z F' hz hZ hP
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hcard : Fintype.card (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) ≤ Module.finrank (D.s.atP p).Ep (L.V p) := by
    rw [L.rank p, Fintype.card_sum, Fintype.card_fin]
    omega
  have hcle : cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal ≤ 2 * (D.R.rS + 1) := by
    have := Formalism.L2.SG.Pf.Asm.cJ_le (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal
    rw [hUr, hm] at this
    exact this
  unfold densP
  rw [hG, local_density_corank (D.s.atP p).Fp (D.s.atP p).Ep (M p) (D.s.atP p).lf (D.s.atP p).char0 (L.V p)
    (L.H p) (lattice₂ L p (VS D).L0) hSD (ϖ p) (hϖ p) _ A a hAO hAdet hcard, L.rank p, Fintype.card_sum,
    Fintype.card_fin, hc, show D.R.rS + 1 + (D.R.rS + 1) = 2 * (D.R.rS + 1) by ring]
  exact h5 δ M hA p _ hcle

theorem densMultIntAt_of (h1 : LocSelfDual) (h2 : GaPlusDiag) {D : Formalism.BasicNotions.D7} (h5 : DensProdValAt D) :
    DensMultIntAt D := by
  intro δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI
  have hval := densValAt_of h1 h2 h5 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI
  obtain ⟨-, -, hUr, -⟩ := perpendicular_definition_holds D u u' hT F0 what₂ hR Z F' hz hZ hP
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hs : Summable (fun p : PlF D => densP L δ ϖ (Tn u) (Tn u') Z p - 1) := by
    refine Summable.of_norm_bounded_eventually ((PI.UnitaryGroupMassFormula.CntFormula.prime_zeta_two D.host.F).mul_left 6) ?_
    filter_upwards [(absNorm_small_finite D).compl_mem_cofinite] with p hp
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hp
    have hcle : cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal ≤ 2 * (D.R.rS + 1) := by
      have := Formalism.L2.SG.Pf.Asm.cJ_le (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal
      rw [hUr, hm] at this
      exact this
    obtain ⟨-, hup, hlow⟩ := Formalism.L2.SG.Pf.DensLoc.ratio_bounds (K := D.host.E) p.asIdeal (by linarith)
      (j := D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal) (n := D.R.r) (s := 2)
      (by omega) (by omega) (by norm_num)
    have hlow' := hlow hp
    rw [hval p, Real.norm_eq_abs]
    set x : ℝ := ((Ideal.absNorm p.asIdeal : ℝ))⁻¹ with hx
    have hx0 : 0 ≤ x := inv_nonneg.2 (by linarith)
    have hx3 : x ≤ 1 / 3 := by rw [hx, one_div]; exact inv_anti₀ (by norm_num) hp
    have hx2 : x ^ 2 ≤ 1 / 9 := by nlinarith
    have hx2n : 0 ≤ x ^ 2 := sq_nonneg x
    have h2n : (0 : ℝ) ≤ 2 * x ^ 2 := by positivity
    have h3n : (0 : ℝ) ≤ 3 * x ^ 2 := by positivity
    have e1 := Real.abs_exp_sub_one_le (x := 2 * x ^ 2) (by rw [abs_of_nonneg h2n]; linarith)
    have e2 := Real.abs_exp_sub_one_le (x := -(3 * x ^ 2)) (by rw [abs_neg, abs_of_nonneg h3n]; linarith)
    rw [abs_of_nonneg h2n] at e1
    rw [abs_neg, abs_of_nonneg h3n] at e2
    have hq : 6 * (1 / ((Ideal.absNorm p.asIdeal : ℝ) ^ 2)) = 6 * x ^ 2 := by rw [hx, inv_pow, one_div]
    rw [hq, abs_le]
    constructor
    · have := (abs_le.mp e2).1
      linarith
    · have := (abs_le.mp e1).2
      linarith
  have := Real.multipliable_one_add_of_summable hs
  simpa using this

theorem densAllAt_of_steps (h1 : LocSelfDual) (h2 : GaPlusDiag) (h3 : NotIntDens) {D : Formalism.BasicNotions.D7}
    (h5 : DensProdValAt D) (h6 : DensMultIntAt D) : Formalism.L2.SG.Pf.DensLoc.DensAllAt D := by
  intro δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP
  exact ⟨fun hI => ⟨densValAt_of h1 h2 h5 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI,
      h6 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI⟩,
    fun hI => h3 D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI⟩

theorem densAllAt_of_tied {D : Formalism.BasicNotions.D7} (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) : Formalism.L2.SG.Pf.DensLoc.DensAllAt D := by
  have h1 : LocSelfDual := local_self_dual_holds
  have hF : DualityBasisChange.FrameBasisL := DualityBasisChange.frameBasisL_holds
  have h2 : GaPlusDiag := DualityBasisChange.gaPlusDiag_of hF jordan_decomposition_holds
  have h5 : DensProdValAt D := densProdValAt_of (etaLocAt_of_tied hL)
  exact densAllAt_of_steps h1 h2 (DualityBasisChange.not_integral_density_of_self_dual h1 hF) h5 (densMultIntAt_of h1 h2 h5)

theorem densLocBound_of_tied {D : Formalism.BasicNotions.D7} (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) : Formalism.L2.SG.DataCut.DensLocBound D := Formalism.L2.SG.Pf.DensLoc.densLocBound_at (densAllAt_of_tied hL)

def DensInputT : Prop := ∀ D : Formalism.BasicNotions.D7, Formalism.L2.SG.Pf.LocCP.LocTied D → Formalism.L2.SG.DataInst.DensInputAt D

theorem densInputT_holds : DensInputT := fun D hL => Formalism.L2.SG.DataCut.densInputAt_of_loc (densLocBound_of_tied hL)

end Formalism.L2.SG.Pf.Cnt
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.BaseLatticeLe
noncomputable section

open NumberField Formalism.BasicNotions
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.SplitPrimeNormLemmas.IntG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem base_lattice_le : X.Lb ≤ (VS D).L0 := by
  rw [X.Lam_split]
  exact le_sup_of_le_left le_sup_right

theorem Lb_le_aaLbS (b : Fin D.R.rS) : X.Lb ≤ aaLbS X b := fun l hl =>
  Submodule.subset_span ⟨1, one_mem_aaD b, l, hl, by rw [one_smul]⟩

theorem aaLbS_le_span (b : Fin D.R.rS) :
    aaLbS X b ≤ (Submodule.span D.host.E (X.Lb : Set (VS D).V)).restrictScalars (𝓞 D.host.E) := by
  unfold aaLbS
  rw [Submodule.span_le]
  rintro _ ⟨c, -, l, hl, rfl⟩
  exact Submodule.smul_mem _ c (Submodule.subset_span hl)

theorem span_aaLbS (b : Fin D.R.rS) :
    Submodule.span D.host.E (aaLbS X b : Set (VS D).V) = Submodule.span D.host.E (X.Lb : Set (VS D).V) :=
  le_antisymm (Submodule.span_le.2 (aaLbS_le_span X b)) (Submodule.span_mono (Lb_le_aaLbS X b))

theorem aaD_ne_zero' (b : Fin D.R.rS) : aaD D b ≠ 0 := by
  unfold aaD
  exact zpow_ne_zero _ ddS_ne_zero

theorem fg_aaLbS (b : Fin D.R.rS) : (aaLbS X b).FG := by
  set N : ℕ := Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) ^ (D.R.rS - (b : ℕ)) with hNdef
  have hN : ((N : ℕ) : D.host.E) ∈ (aaD D b)⁻¹ := mem_aaD_inv b
  have hN0 : N ≠ 0 := by
    rw [hNdef]
    refine pow_ne_zero _ ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact differentIdeal_ne_bot
  let f : (VS D).V →ₗ[𝓞 D.host.E] (VS D).V := (N : 𝓞 D.host.E) • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : ((N : 𝓞 D.host.E) : D.host.E) • x = ((N : 𝓞 D.host.E) : D.host.E) • y := by
      rw [algebraMap_smul, algebraMap_smul]
      exact hxy
    have h2 : ((N : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
      push_cast
      exact_mod_cast hN0
    exact smul_right_injective _ h2 h1
  have hle : (aaLbS X b).map f ≤ (VS D).L0 := by
    unfold aaLbS
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨c, hc, l, hl, rfl⟩, rfl⟩
    have hmul : ((N : ℕ) : D.host.E) * c ∈ ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Set D.host.E) := by
      have := FractionalIdeal.mul_mem_mul hN hc
      rwa [inv_mul_cancel₀ (aaD_ne_zero' b)] at this
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hmul
    have e : f (c • l) = o • l := by
      show (N : 𝓞 D.host.E) • (c • l) = o • l
      rw [← algebraMap_smul D.host.E (N : 𝓞 D.host.E), smul_smul, ← algebraMap_smul D.host.E o l, ho]
      push_cast
      rfl
    rw [e]
    exact base_lattice_le X (X.Lb.smul_mem o hl)
  haveI : IsNoetherian (𝓞 D.host.E) (VS D).L0 := isNoetherian_of_fg_of_noetherian _ (VS D).standardTuple_isLattice.fg
  have hfg : ((aaLbS X b).map f).FG := (isNoetherian_submodule.1 inferInstance) _ hle
  exact Submodule.fg_of_fg_map_injective f hf hfg

end Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CntIso
open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in
open PI.RepsIndep.Tr in
theorem ci_EZ_map {D : Formalism.BasicNotions.D7} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {Z : MatZ D} {F' : LFlag (D.sp.Y 0) D.R.rS T'} (h : F' ∈ EZ T' F0 Λ Z) :
    mapL β hβ F' ∈ EZ T' (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) Z := by
  have hlf : lf D (mapF β hβ F0) = mapL β hβ (lf D F0) := lflag_ext rfl rfl
  unfold EZ at h ⊢
  rw [Set.mem_setOf_eq] at h ⊢
  rw [hlf]
  obtain ⟨⟨hL, ⟨ξ, hξ⟩, hG⟩, hA, hGen, hF, hZ⟩ := h
  have hG' : Gval (mapL β hβ (lf D F0)) (mapL β hβ F') ≠ 0 := by
    show Formalism.MainNotions.S.Gflag (mapF β hβ F0) (mapF β hβ F'.fl) ≠ 0
    simp only [Formalism.MainNotions.S.Gflag, Formalism.MainNotions.S.Dl, Zhat_mapF hβ]
    exact hG
  have hZ' : ZhatL (mapL β hβ (lf D F0)) (mapL β hβ F') = Z := by
    show Formalism.MainNotions.S.Zhat (mapF β hβ F0) (mapF β hβ F'.fl) = Z
    rw [Zhat_mapF hβ]
    exact hZ
  exact ⟨⟨IsLift_map hβ hL, ⟨ξ, AdmWit_map hβ hξ⟩, hG'⟩, AdmWit_map hβ hA, IsGeneric_map hβ hGen,
    FrameOK_map hβ hF, hZ'⟩

set_option maxHeartbeats 2000000 in
open PI.RepsIndep.Tr in
theorem ci_rel_map {D : Formalism.BasicNotions.D7} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {F' F'' : LFlag (D.sp.Y 0) D.R.rS T'} (h : NilradicalFlagMoved F0 Λ F' F'') :
    NilradicalFlagMoved (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F') (mapL β hβ F'') := by
  have hlf : lf D (mapF β hβ F0) = mapL β hβ (lf D F0) := lflag_ext rfl rfl
  obtain ⟨n, ⟨hnL, hne, hnz⟩, h1, h2⟩ := h
  have hN : conj β n ∈ NLam (Formalism.HermitianLatticesTheory.gmap β Λ) (lf D (mapF β hβ F0)) := by
    rw [hlf]; exact NLam_conj hβ hnL
  refine ⟨conj β n, ⟨hN, fun a => ?_, ?_⟩, fun a => ?_, ?_⟩
  · show β (n (β.symm (β (F0.e a)))) = β (F0.e a)
    rw [LinearEquiv.symm_apply_apply, hne]
  · show β (n (β.symm (β F0.z))) = β F0.z
    rw [LinearEquiv.symm_apply_apply, hnz]
  · show β (n (β.symm (β (F'.fl.e a)))) = β (F''.fl.e a)
    rw [LinearEquiv.symm_apply_apply, h1]
  · show β (n (β.symm (β F'.fl.z))) = β F''.fl.z
    rw [LinearEquiv.symm_apply_apply, h2]

open PI.RepsIndep.Tr in
theorem ci_mapF_symm {D : Formalism.BasicNotions.D7} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : mapF β.symm (iso_symm hβ) (mapF β hβ F0) = F0 :=
  flag_ext (funext fun a => LinearEquiv.symm_apply_apply β (F0.e a)) (LinearEquiv.symm_apply_apply β F0.z)

open PI.RepsIndep.Tr in
theorem counting_iso_inverse : CntIsoInv := by
  intro D β hβ T T' F0 Λ Z
  have hβ' := iso_symm hβ
  have hΛ : Formalism.HermitianLatticesTheory.gmap β.symm (Formalism.HermitianLatticesTheory.gmap β Λ) = Λ := gmap_symm_gmap β Λ
  have hF : Formalism.L2.SG.Saturated.mapFlag β hβ F0 = mapF β hβ F0 := flag_ext rfl rfl
  rw [hF]
  show Formalism.MainNotions.S.Cnt.cntCl (EZ T' (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) Z) (NilradicalFlagMoved (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ)) =
    Formalism.MainNotions.S.Cnt.cntCl (EZ T' F0 Λ Z) (NilradicalFlagMoved F0 Λ)
  refine cntCl_equiv (mapL β hβ) (mapL β.symm hβ') (mapL_symm hβ) (mapL_symm' hβ hβ') _ _ _ _
    (fun F' => ⟨fun h => ?_, fun h => ci_EZ_map hβ h⟩) (fun F' F'' => ⟨fun h => ?_, fun h => ci_rel_map hβ h⟩)
  · have e := ci_EZ_map hβ' h
    rw [mapL_symm hβ, ci_mapF_symm hβ, hΛ] at e
    exact e
  · have e := ci_rel_map hβ' h
    rw [mapL_symm hβ, mapL_symm hβ, ci_mapF_symm hβ, hΛ] at e
    exact e

end Formalism.L2.SG.Pf.Cnt
end
end
