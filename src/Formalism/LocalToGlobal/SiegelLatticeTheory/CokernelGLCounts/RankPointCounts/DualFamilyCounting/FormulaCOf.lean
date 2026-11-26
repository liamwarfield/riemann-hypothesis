module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibCut
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.JordanDecompositionExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PjFrameRow

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaCOf
open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def OrbitFiniteR : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (_L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ Z : MatZ D, ∀ Λ ∈ what₂, cntE (Tn u') F0 Λ Z ≠ ⊤

def RowLatExists : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u : D.what₂.Word), ∃ Λ, IsRowLat D (T.X.Fu u) Λ

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem cExpl_pos' (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : IsRowReps D F0 what₂) (hne : what₂.Nonempty) :
    0 < cExpl D F0 what₂ := by
  obtain ⟨hK, hF, -⟩ := field_dictionary_holds D
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hc := (Formalism.L2.SG.Pf.Asm.cMass_spec hK hF (D.R.k - 1) (by omega)).1
  have hd : 0 < |(NumberField.discr D.host.F : ℝ)| ^
      (-((2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) : ℕ) : ℤ)) := by
    apply zpow_pos
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.F)
  have hL : 0 < ∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i := by
    apply Finset.prod_pos
    intro i hi
    have hi2 : 2 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
    rw [← lValEta_eq_lValEtaF hK hF i hi2]
    exact lValEta_pos hK i hi2
  have hA : Formalism.L2.SG.PairVal.AutFin D F0 what₂ := by
    intro Λ hΛ
    exact _root_.automorphism_lattice_finite D (D.sp.Y_sig 0) (D.mem u).A.T (D.mem u).A.T_prime.pos F0 Λ (hR.1 Λ hΛ)
  have hm := Formalism.L2.SG.PairVal.massRows_pos D F0 what₂ hA hne
  unfold cExpl
  positivity


end Formalism.L2.SG.Pf.Cnt
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowVZero
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hJ_add_l {n : ℕ} (ε : Fin n → Bool) (x y z : Fin n → ℂ) : hJ ε (x + y) z = hJ ε x z + hJ ε y z := by
  first
    | simp only [hJ, star_add, Matrix.add_dotProduct]
    | simp only [hJ, star_add, add_dotProduct]
    | simp [hJ, Matrix.add_dotProduct]
    | simp [hJ, add_dotProduct]

theorem hJ_conj' {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε y x = star (hJ ε x y) := by
  simp only [hJ, Formalism.REAL.Jm, dotProduct, Matrix.mulVec_diagonal, star_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ε i <;> simp [h, mul_comm]

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem emb_star (v : InfinitePlace X.B.I.F) (t : D.host.E) :
    embS D (X.pl v) (star t) = star (embS D (X.pl v) t) := by
  first
    | exact NumberField.IsCMField.complexEmbedding_complexConj _ t
    | (simp only [Formalism.MainNotions.S.embS]; exact NumberField.IsCMField.complexEmbedding_complexConj _ t)
    | (haveI := D.host.isCMField_hostE
       rw [show (star t : D.host.E) = NumberField.IsCMField.complexConj D.host.E t from rfl]
       exact NumberField.IsCMField.complexEmbedding_complexConj _ _ t)
    | (haveI := D.host.isCMField_hostE
       exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E (embS D (X.pl v)) t)

theorem rowV_add (x y : (VS D).V) : rowV X u (x + y) = rowV X u x + rowV X u y := by
  funext v j
  have hc : X.crd (x + y) = X.crd x + X.crd y := by
    first
      | exact Formalism.L2.SG.Pf.Vanish2.crd_add X x y
      | exact Formalism.L2.SG.HidaSetting.crd_add X x y
      | (funext i; simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf])
  have hr : rv X.B.I v (X.crd x + X.crd y) = rv X.B.I v (X.crd x) + rv X.B.I v (X.crd y) := by
    unfold rv
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp only [Pi.add_apply, map_add]
  simp only [rowV, Pi.add_apply, hc, hr]
  split_ifs <;> exact hJ_add_l _ _ _ _

theorem rowV_zero : rowV X u 0 = 0 := by
  have h := rowV_add X u 0 0
  rw [add_zero] at h
  simpa using h

theorem rowV_neg (x : (VS D).V) : rowV X u (-x) = -rowV X u x := by
  rw [eq_neg_iff_add_eq_zero, add_comm (rowV X u (-x)), ← rowV_add, add_neg_cancel, rowV_zero]

theorem rowV_sub (x y : (VS D).V) : rowV X u (x - y) = rowV X u x - rowV X u y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, rowV_add, rowV_neg]

def rowHom : (VS D).V →+ (InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :=
  AddMonoidHom.mk' (rowV X u) (rowV_add X u)

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibRat
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.Full Formalism.L2.SG.Pf.Slab Formalism.L2.SG.Pf.Vanish2 Formalism.L2.SG.Pf.SlabCoverPf
open Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_base_lattice_iff_adelic {D : D7} (X : HidaSetting D) (y : (VS D).V) :
    y ∈ (VS D).L0 ↔ incl X.B.I (X.crd y) ∈ X.B.I.Lf := by
  rw [Formalism.L2.SG.Pf.LatDict.mem_hermitianStandardLattice_iff_pairing_integral X y]
  exact ⟨fun h => Formalism.L2.SG.Pf.Level.incl_mem_Lf X _ h,
    fun h => Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.mem_L_of_inclE_mem X.B.I _ h⟩

theorem noratC_holds : NOratC := by
  intro D X u s
  constructor
  · rintro ⟨γ, hG, rfl, hN, hF, hk⟩
    have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties X
    have hγK : γ.2 ∈ X.B.I.Kset := by
      have h1 : (X.xu u)⁻¹ * γ.2 * X.xu u ∈ X.B.I.Kset := hK2.2.1 _ hk
      have e : γ.2 = X.xu u * ((X.xu u)⁻¹ * γ.2 * X.xu u) * (X.xu u)⁻¹ := by group
      rw [e]
      exact unitaryCongruence.K_mul X.B.I (unitaryCongruence.K_mul X.B.I (X.xu_K u) h1) (unitaryCongruence.K_inv X.B.I (X.xu_K u))
    obtain ⟨M, hM, hinf, hfin⟩ := hG
    refine ⟨γ, matEC X M, ⟨M, hM, hinf, hfin, matE_crdC X M⟩, rfl, ?_⟩
    obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
    have hGv : ∀ y, uMat (γ.1 v) *ᵥ rvHom X.B.I v y = rvHom X.B.I v ((M : Matrix _ _ _) *ᵥ y) := by
      intro y
      rw [rvHom_apply, rvHom_apply, hinf v]
      exact rv_mulVec X v _ y
    have hsub : ∀ y, (uMat (γ.1 v) - 1) *ᵥ rv X.B.I v y = rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ y) :=
      fun y => tr_sub (rvHom X.B.I v) _ _ hGv y
    have hcrdn : ∀ y, X.crd (matEC X M y - y) = ((M : Matrix _ _ _) - 1) *ᵥ X.crd y := by
      intro y
      rw [crd_sub', matE_crdC, Matrix.sub_mulVec, Matrix.one_mulVec]
    have hback : ∀ (y : (VS D).V) (T : Set (Fin D.R.rS)),
        ((M : Matrix _ _ _) - 1) *ᵥ X.crd y ∈ Submodule.span X.B.I.E (X.eR '' T) →
        matEC X M y - y ∈ Submodule.span D.host.E (X.eX '' T) := by
      intro y T hy
      rw [← hcrdn] at hy
      have := toV_span X hy
      rwa [toV_crd] at this
    have hInN := hN v
    refine ⟨⟨matE_isomC X M hM, ?_⟩, ?_, ?_⟩
    · have key : ∀ y, matEC X M y ∈ (VS D).L0 ↔ y ∈ (VS D).L0 := by
        intro y
        rw [mem_base_lattice_iff_adelic, mem_base_lattice_iff_adelic, matE_inclC, ← hfin]
        exact (Formalism.L2.SG.Pf.UnipB.kset_apply X hγK _).symm
      show Formalism.HermitianLatticesTheory.gmap (matEC X M) (VS D).L0 = (VS D).L0
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (key z).2 hz
      · intro hy
        refine ⟨(matEC X M).symm y, (key _).1 (by simpa using hy), ?_⟩
        simp
    · intro j x hx
      change x ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j + 1}) at hx
      change _ ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j})
      rw [X.Fu_e] at hx ⊢
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        have h1 := hInN.1.1 a
        rw [hsub] at h1
        have h2 : rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ X.eR a) ∈
            Submodule.span ℂ (rv X.B.I v '' (X.eR '' {b | b.1 < a.1})) := by
          rw [Set.image_image]; exact h1
        have h3 := rv_desc X v _ _ h2
        have h4 : ((M : Matrix _ _ _) - 1) *ᵥ X.crd (X.eX a) ∈
            Submodule.span X.B.I.E (X.eR '' {b | b.1 < j}) := by
          refine Submodule.span_mono (Set.image_mono fun b hb => ?_) h3
          have : a.1 < j + 1 := ha
          show b.1 < j
          have : b.1 < a.1 := hb
          omega
        exact hback _ _ h4
      | zero => simp
      | add a b _ _ ha hb =>
        rw [map_add (f := _), add_sub_add_comm]
        exact add_mem ha hb
      | smul c a _ ha =>
        rw [map_smul, ← smul_sub]
        exact Submodule.smul_mem _ _ ha
    · intro x hx
      change x ∈ orth (VS D) (Submodule.span D.host.E (Set.range (X.Fu u).e)) at hx
      change _ ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)
      rw [X.Fu_e] at hx ⊢
      have hzero : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.crd x)) = 0 := by
        intro a
        rw [hJ_rv]
        have h0 : hE X (X.eR a) (X.crd x) = 0 := by
          apply X.ιE.injective
          rw [iota_hE, map_zero, HidaSetting.eR, toV_crd, toV_crd]
          exact (mem_orth_iff _ _).1 hx _ (Submodule.subset_span ⟨a, rfl⟩)
        rw [h0, map_zero]
      have h1 := hInN.2 _ hzero
      rw [hsub] at h1
      have huniv : {b : Fin D.R.rS | b.1 < D.R.rS} = Set.univ := Set.eq_univ_of_forall fun b => b.2
      have h2 : rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ X.crd x) ∈
          Submodule.span ℂ (rv X.B.I v '' (X.eR '' {b | b.1 < D.R.rS})) := by
        rw [Set.image_image]; exact h1
      have h3 := hback x _ (rv_desc X v _ _ h2)
      rwa [huniv, Set.image_univ] at h3
  · rintro ⟨x, n, hx, rfl, hn⟩
    have hNf := nLamNfin_holds D X u _ x n hx hn
    have hlat : ∀ y : (VS D).V, y ∈ (VS D).L0 ↔
        X.B.I.fmat (((1 : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf := by
      intro y
      rw [mem_base_lattice_iff_adelic]
      simp only [OneMemClass.coe_one, one_mul]
      exact Formalism.L2.SG.Pf.UnipB.kset_apply X (unitaryCongruence.K_inv X.B.I (X.xu_K u)) _
    have hc := (Formalism.L2.SG.Pf.VanishNConj.core X u (Formalism.L2.SG.Pf.unipotent_in_level X u) 1 hlat hn hx).1
    simp only [OneMemClass.coe_one, one_mul] at hc
    exact ⟨x, ratLink_mem X hx, rfl, nLamNinf_holds D X u _ x n hx hn, hNf, hc⟩

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibFibT
namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

theorem thetaEx_holds : ThetaEx := by
  intro D
  refine ⟨(1 + D.host.sqd) / 2, Formalism.BasicNotions.Examples₂.isIntegral_halfB D.host, ?_⟩
  rw [Formalism.BasicNotions.Examples₂.conj_half, Formalism.BasicNotions.Examples₂.conj_bE]
  ring

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibLatCut
namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.BasicNotions Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DictLatF : Prop :=
  ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    NFl X u n → Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0 → LatQ X (Xq X n) (xq X n) (Mq X n)

def DictLatB : Prop :=
  ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    NFl X u n → LatQ X (Xq X n) (xq X n) (Mq X n) → Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0

theorem dictLat_of (hF : DictLatF) (hB : DictLatB) : DictLat :=
  fun X u n hn => ⟨hF X u n hn, hB X u n hn⟩

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowParseval
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def gC {D : D7} (u : D.what₂.Word) (c : Fin (D.R.k + 1)) : ℂ :=
  if c.val < D.R.k then 1 else -(1 / ((Formalism.L2.SG.RealObj.Tw u : ℝ) : ℂ))

def RowParseval : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (x y : (VS D).V),
    (∀ a, (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0) →
    (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) →
    ∀ v : InfinitePlace X.B.I.F,
      ∑ c, rowV X u x v c * star (rowV X u y v c) * gC u c = X.B.I.φ v (X.ιE.symm ((VS D).hT x y))

def RowRank : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (b : Fin D.R.rS),
    Nonempty (Module.Basis (Fin (Module.finrank ℚ D.host.E * (D.R.k + 1))) ℤ ((aaLbS X b).restrictScalars ℤ))

def TraceRe : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (t : D.host.E),
    ∑ v : InfinitePlace X.B.I.F, (X.B.I.φ v (X.ιE.symm t)).re = ((Algebra.trace ℚ D.host.E t : ℚ) : ℝ) / 2

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InWLeft
noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem h_symm (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := ((VS D).herm.eq x y).symm

theorem h_fe (a b : Fin D.R.rS) : (VS D).hT (X.fY a) (X.eX b) = if a = b then 1 else 0 := by
  rw [h_symm, X.ef b a]
  by_cases h : b = a
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

theorem inW_pW (y : (VS D).V) : InW X (pW X y) := by
  intro c
  unfold pW
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_smul, smul_eq_mul, X.ee, X.ef, h_fe, X.ff, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, sub_zero]
  constructor
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]

theorem decomp (y : (VS D).V) :
    y = ∑ c, (VS D).hT (X.fY c) y • X.eX c + ∑ c, (VS D).hT (X.eX c) y • X.fY c + pW X y := by
  unfold pW
  abel

theorem inW_left {w : (VS D).V} (hw : InW X w) (a : Fin D.R.rS) :
    (VS D).hT w (X.eX a) = 0 ∧ (VS D).hT w (X.fY a) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [h_symm, (hw a).1, star_zero]
  · rw [h_symm, (hw a).2, star_zero]

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNBoxHolds
namespace Formalism.L2.SG.Pf.NcReal.JX

theorem refNBox_holds : RefNBox := refNBox_of FR.frameRow_holds

end Formalism.L2.SG.Pf.NcReal.JX
end
