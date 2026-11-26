module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompactAdele

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.IsWeilDatum
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.IndefR.Heis

section Law

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

@[ext] structure HeisG (B : M →ₗ[R] M →ₗ[R] R) where

  w : M

  t : R

namespace HeisG

variable {B : M →ₗ[R] M →ₗ[R] R} [Invertible (2 : R)]

end HeisG

end Law

section Rat

variable {E : Type*} [Field E] [NumberField E] (c : E →+* E)

structure HermSp where

  n : ℕ

  J : Matrix (Fin n) (Fin n) E
  herm : J.transpose = J.map c
  nondeg : J.det ≠ 0

variable {c}

def hf (V : HermSp c) (v u : Fin V.n → E) : E := ∑ i, ∑ j, v i * V.J i j * c (u j)

end Rat

section Ad

variable {𝔸 WA : Type*} [CommRing 𝔸] [AddCommGroup WA] [Module 𝔸 WA]

variable [Invertible (2 : 𝔸)] (ψ : AddChar 𝔸 ℂ) (B : WA →ₗ[𝔸] WA →ₗ[𝔸] 𝔸)

end Ad

section D7

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Hth (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Submodule ℂ (WA V W → ℂ) where
  carrier := {f | IsThetaFun ψ V W f}
  zero_mem' := by
    refine ⟨fun γ w => by simp, ⟨⊤, isOpen_univ, fun u _ _ => ?_⟩, continuous_const, fun k L _ _ w => contDiff_const⟩
    funext w; simp [Heisenberg₂]
  add_mem' := by
    intro f g hf hg
    obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨U', hU', hUg⟩ := hg.level
    refine ⟨fun γ w => ?_, ⟨U ⊓ U', ?_, fun u hu h0 => ?_⟩, hf.cont.add hg.cont, fun k L hL hL0 w => ?_⟩
    · simp only [Pi.add_apply, hf.quasi γ w, hg.quasi γ w, mul_add]
    · rw [AddSubgroup.coe_inf]; exact hU.inter hU'
    · funext w
      have e1 := congrFun (hUf u hu.1 h0) w
      have e2 := congrFun (hUg u hu.2 h0) w
      simp only [Heisenberg₂, Pi.add_apply] at e1 e2 ⊢
      rw [mul_add, e1, e2]
    · exact (hf.smooth k L hL hL0 w).add (hg.smooth k L hL hL0 w)
  smul_mem' := by
    intro a f hf
    obtain ⟨U, hU, hUf⟩ := hf.level
    refine ⟨fun γ w => ?_, ⟨U, hU, fun u hu h0 => ?_⟩, continuous_const.mul hf.cont, fun k L hL hL0 w => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf.quasi γ w]; ring
    · funext w
      have e1 := congrFun (hUf u hu h0) w
      simp only [Heisenberg₂, Pi.smul_apply, smul_eq_mul] at e1 ⊢
      rw [mul_left_comm, e1]
    · exact contDiff_const.mul (hf.smooth k L hL hL0 w)

def FinCovol (V W : HSp D) : Prop :=
  (∃ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL V W) 𝓕 μ) ∧
    ∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V W) 𝓕 μ → μ 𝓕 < ⊤

end D7

end Formalism.IndefR.Heis

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

namespace Formalism.IndefR.RationalEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev inst : Formalism.MainNotions.S.AutInst := Formalism.L2.SG.InstExistsPf.instOf D

def iota : GA D (D.sp.Y 0) ≃ₜ* (inst D).GA :=
  (Formalism.L2.SG.AdBridge.toHA (inst D) (Formalism.L2.SG.Closed.adelic_isomorphism_statement (inst D)).1).symm

theorem iota_symm_isBridge : Formalism.L2.SG.AdBridge.IsBridge (inst D) (iota D).symm :=
  Formalism.L2.SG.AdBridge.toHA_isBridge (inst D) (Formalism.L2.SG.Closed.adelic_isomorphism_statement (inst D)).1

theorem iota_rat (g : GA D (D.sp.Y 0)) : g ∈ GQ (D.sp.Y 0) ↔ iota D g ∈ (inst D).GFset := by
  have hS := Formalism.L2.SG.Closed.adelic_isomorphism_statement (inst D)
  have hb := Formalism.L2.SG.AdBridge.toHA_isBridge (inst D) hS.1
  have hGF := hS.2.1 _ hb
  have hg : Formalism.L2.SG.AdBridge.toHA (inst D) hS.1 (iota D g) = g :=
    (Formalism.L2.SG.AdBridge.toHA (inst D) hS.1).apply_symm_apply g
  rw [← (Formalism.L2.SG.AdBridge.toHA (inst D) hS.1).injective.mem_set_image (a := iota D g)
    (s := (inst D).GFset), hGF, hg]
  exact Iff.rfl

end Formalism.IndefR.RationalEmbedding

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.CxToPkgFamIn
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section Concrete

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def crdOf (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) : Crd A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) where
  toR Zs b t := match b with
    | false => (A.fam.R t).toF (A.fam.lvl P0 ψ0) (Zs.Z t)
    | true => (A.fam.R t).toF (A.fam.lvl P1 ψ1) (Zs.Z t)
  toL Zs b j t := match b with
    | false => (A.fam.L j t).toF (A.fam.lvlA P0 ψ0) (Zs.Zl j t)
    | true => (A.fam.L j t).toF (A.fam.lvlA P1 ψ1) (Zs.Zl j t)

end Concrete

end Formalism.IndefR.Cx
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.InjectiveDecompositionAction
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.InjectiveDecompositionAction

variable {D : D7}

def FirstPropositionFrame (D : D7) : Subgroup (AE D)ˣ where
  carrier := {x | (x : AE D) * cA D (x : AE D) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at *
    calc (a : AE D) * b * (cA D a * cA D b) = (a * cA D a) * (b * cA D b) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h1 : ((a⁻¹ : (AE D)ˣ) : AE D) * a = 1 := by simp
    have h2 : cA D ((a⁻¹ : (AE D)ˣ) : AE D) * cA D (a : AE D) = 1 := by rw [← map_mul, h1, map_one]
    calc ((a⁻¹ : (AE D)ˣ) : AE D) * cA D ((a⁻¹ : (AE D)ˣ) : AE D)
        = ((a⁻¹ : (AE D)ˣ) : AE D) * cA D ((a⁻¹ : (AE D)ˣ) : AE D) * ((a : AE D) * cA D (a : AE D)) := by
          rw [ha, mul_one]
      _ = (((a⁻¹ : (AE D)ˣ) : AE D) * a) * (cA D ((a⁻¹ : (AE D)ˣ) : AE D) * cA D (a : AE D)) := by ring
      _ = 1 := by rw [h1, h2, one_mul]

def SuppAtU (D : D7) (e : AE D) (x : (AE D)ˣ) : Prop :=
  (e + cA D e) * ((x : AE D) - 1) = (x : AE D) - 1

end Formalism.IndefR.InjectiveDecompositionAction

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.PHeisFCA
noncomputable section

open MeasureTheory IsDedekindDomain NumberField Topology
open scoped RestrictedProduct Classical

namespace Formalism.IndefR.PHeisFC

variable (F : Type) [Field F] [NumberField F]

abbrev eM : InfiniteAdeleRing F ≃+* mixedEmbedding.mixedSpace F := InfiniteAdeleRing.ringEquiv_mixedSpace F

theorem eM_apply (x : InfiniteAdeleRing F) :
    eM F x = ((fun v : {w : InfinitePlace F // w.IsReal} =>
        InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v.1)),
      fun v : {w : InfinitePlace F // w.IsComplex} => InfinitePlace.Completion.extensionEmbedding v.1 (x v.1)) :=
  InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x

def Pinf : Set (InfiniteAdeleRing F) := eM F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)

theorem eM_algebraMap (a : F) : eM F (algebraMap F (InfiniteAdeleRing F) a) = mixedEmbedding F a := by
  first
  | exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp).symm
  | exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm
  | exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (x := a)).symm

theorem inf_exU (x : InfiniteAdeleRing F) : ∃! a : 𝓞 F, algebraMap F (InfiniteAdeleRing F) (a : F) + x ∈ Pinf F := by
  have key : ∀ a : 𝓞 F, (algebraMap F (InfiniteAdeleRing F) (a : F) + x ∈ Pinf F) ↔
      mixedEmbedding F (a : F) + eM F x ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F) := by
    intro a
    show eM F (algebraMap F (InfiniteAdeleRing F) (a : F) + x) ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F) ↔ _
    rw [map_add (f := _), eM_algebraMap]
  have hmem : ∀ a : 𝓞 F, mixedEmbedding F (a : F) ∈
      Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F)) := by
    intro a
    rw [mixedEmbedding.mem_span_latticeBasis]
    exact ⟨a, rfl⟩
  obtain ⟨v, hv, hu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (mixedEmbedding.latticeBasis F) (eM F x)
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 F, mixedEmbedding F (a : F) = (v : mixedEmbedding.mixedSpace F) := by
    have hv2 := v.2
    rw [mixedEmbedding.mem_span_latticeBasis] at hv2
    obtain ⟨a, ha⟩ := hv2
    exact ⟨a, ha⟩
  refine ⟨a, ?_, ?_⟩
  · show algebraMap F (InfiniteAdeleRing F) (a : F) + x ∈ Pinf F
    rw [key, ha]
    simpa [Submodule.vadd_def] using hv
  · intro b hb0
    have hb : algebraMap F (InfiniteAdeleRing F) (b : F) + x ∈ Pinf F := hb0
    rw [key] at hb
    have h1 : (⟨mixedEmbedding F (b : F), hmem b⟩ :
        Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F))) = v := by
      apply hu
      simpa [Submodule.vadd_def] using hb
    have h2 : mixedEmbedding F (b : F) = mixedEmbedding F (a : F) := by
      rw [ha]
      exact congrArg Subtype.val h1
    have h3 : (b : F) = (a : F) := mixedEmbedding_injective F h2
    first | exact RingOfIntegers.ext h3 | exact RingOfIntegers.coe_injective h3 | exact Subtype.ext h3

theorem measurableSet_Pinf : MeasurableSet (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) :=
  ZSpan.fundamentalDomain_measurableSet _

theorem Pinf_sub_compact : ∃ K : Set (InfiniteAdeleRing F), IsCompact K ∧ Pinf F ⊆ K := by
  obtain ⟨R, hR⟩ := (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis F)).subset_closedBall 0
  refine ⟨Set.pi Set.univ (fun w => (InfinitePlace.Completion.extensionEmbedding w) ⁻¹' Metric.closedBall 0 R),
    ?_, ?_⟩
  · refine isCompact_univ_pi fun w => ?_
    have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
    first
    | exact hi.isClosedEmbedding.isCompact_preimage (isCompact_closedBall 0 R)
    | exact hi.closedEmbedding.isCompact_preimage (isCompact_closedBall 0 R)
  · intro x hx
    have hx' : ‖eM F x‖ ≤ R := mem_closedBall_zero_iff.mp (hR (show eM F x ∈ _ from hx))
    show ∀ w ∈ (Set.univ : Set (InfinitePlace F)),
      x w ∈ (InfinitePlace.Completion.extensionEmbedding w) ⁻¹' Metric.closedBall 0 R
    intro w _
    have hn : ‖InfinitePlace.Completion.extensionEmbedding w (x w)‖ = ‖x w‖ :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (x w)
    show InfinitePlace.Completion.extensionEmbedding w (x w) ∈ Metric.closedBall 0 R
    rw [mem_closedBall_zero_iff, hn]
    by_cases hw : w.IsReal
    · have hr : ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x w)‖ = ‖x w‖ :=
        (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) (x w)
      have e : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x w) = (eM F x).1 ⟨w, hw⟩ := by
        rw [eM_apply]
      rw [← hr, e]
      exact ((norm_le_pi_norm _ _).trans (norm_fst_le _)).trans hx'
    · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have e : InfinitePlace.Completion.extensionEmbedding w (x w) = (eM F x).2 ⟨w, hc⟩ := by
        rw [eM_apply]
      rw [← hn, e]
      exact ((norm_le_pi_norm _ _).trans (norm_snd_le _)).trans hx'

abbrev Ohat : Set (FiniteAdeleRing (𝓞 F) F) := (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F : Set (FiniteAdeleRing (𝓞 F) F))

theorem isOpen_Ohat : IsOpen (Ohat F) := by
  first | exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.isOpen_intAd F | exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.isOpen_intAd

theorem isCompact_Ohat : IsCompact (Ohat F) := Formalism.L2.Col.rlt_isCompact_intAd

def F0 : Set (AdeleRing (𝓞 F) F) := {x | x.1 ∈ Pinf F ∧ x.2 ∈ Ohat F}

theorem ad_exU (x : AdeleRing (𝓞 F) F) : ∃! q : F, algebraMap F (AdeleRing (𝓞 F) F) q + x ∈ F0 F := by
  have hOa : ∀ a : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F := by
    intro a
    show ∀ v : HeightOneSpectrum (𝓞 F), (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v ∈ v.adicCompletionIntegers F
    intro v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v = ((a : F) : v.adicCompletion F) := rfl
    rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    first
    | exact HeightOneSpectrum.valuation_le_one v a
    | (rw [show (a : F) = algebraMap (𝓞 F) F a from rfl, HeightOneSpectrum.valuation_of_algebraMap];
       exact HeightOneSpectrum.intValuation_le_one v a)
  have hint : ∀ q : F, algebraMap F (FiniteAdeleRing (𝓞 F) F) q ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F →
      ∃ a : 𝓞 F, (a : F) = q := by
    intro q hq
    have hr := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) q (by
      intro v
      have h1 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) q) v ∈ v.adicCompletionIntegers F := hq v
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1
      have h2 : Valued.v ((q : v.adicCompletion F)) ≤ 1 := h1
      rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h2)
    obtain ⟨a, ha⟩ := hr
    first | exact ⟨a, ha⟩ | exact ⟨a, by simpa using ha⟩
  obtain ⟨u, hu⟩ : ∃ u : F, x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) u ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F := by
    first
    | exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd F x.2
    | exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd x.2
  obtain ⟨a, ha, hauniq⟩ := inf_exU F (algebraMap F (InfiniteAdeleRing F) (-u) + x.1)
  refine ⟨-u + (a : F), ?_, ?_⟩
  · simp only [F0, Set.mem_setOf_eq]
    constructor
    · change algebraMap F (InfiniteAdeleRing F) (-u + (a : F)) + x.1 ∈ Pinf F
      have e : algebraMap F (InfiniteAdeleRing F) (-u + (a : F)) + x.1 =
          algebraMap F (InfiniteAdeleRing F) (a : F) + (algebraMap F (InfiniteAdeleRing F) (-u) + x.1) := by
        rw [map_add (f := _)]; abel
      rw [e]; exact ha
    · change algebraMap F (FiniteAdeleRing (𝓞 F) F) (-u + (a : F)) + x.2 ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F
      have e : algebraMap F (FiniteAdeleRing (𝓞 F) F) (-u + (a : F)) + x.2 =
          (x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) u) + algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) := by
        rw [map_add (f := _), map_neg]; abel
      rw [e]; exact add_mem hu (hOa a)
  · intro q hq
    simp only [F0, Set.mem_setOf_eq] at hq
    obtain ⟨h1, h2⟩ := hq
    have h2' : algebraMap F (FiniteAdeleRing (𝓞 F) F) q + x.2 ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F := h2
    have h1' : algebraMap F (InfiniteAdeleRing F) q + x.1 ∈ Pinf F := h1
    have h3 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (q + u) ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F := by
      have h4 := sub_mem h2' hu
      have e : algebraMap F (FiniteAdeleRing (𝓞 F) F) (q + u) =
          algebraMap F (FiniteAdeleRing (𝓞 F) F) q + x.2 - (x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) u) := by
        rw [map_add (f := _)]; abel
      rw [e]; exact h4
    obtain ⟨b, hb⟩ := hint (q + u) h3
    have h5 : algebraMap F (InfiniteAdeleRing F) (b : F) + (algebraMap F (InfiniteAdeleRing F) (-u) + x.1) ∈ Pinf F := by
      have e : algebraMap F (InfiniteAdeleRing F) (b : F) + (algebraMap F (InfiniteAdeleRing F) (-u) + x.1) =
          algebraMap F (InfiniteAdeleRing F) q + x.1 := by
        rw [hb, map_add (f := _), map_neg]; abel
      rw [e]; exact h1'
    have hba : b = a := hauniq b h5
    rw [hba] at hb
    rw [hb]; ring

theorem fundamental_set_subset_compact : ∃ K : Set (AdeleRing (𝓞 F) F), IsCompact K ∧ F0 F ⊆ K := by
  obtain ⟨K1, hK1, hsub⟩ := Pinf_sub_compact F
  refine ⟨K1 ×ˢ Ohat F, hK1.prod (isCompact_Ohat F), ?_⟩
  intro x hx
  simp only [F0, Set.mem_setOf_eq] at hx
  exact ⟨hsub hx.1, hx.2⟩

instance instT2SpaceFiniteAdeles : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ (v : HeightOneSpectrum (𝓞 F)), [v.adicCompletion F, v.adicCompletionIntegers F]))

instance t2Space_numberFieldInfiniteAdeles : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

instance t2AF : T2Space (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

instance wlcAfin : WeaklyLocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) where
  exists_compact_mem_nhds x := by
    refine ⟨(fun y => x + y) '' Ohat F, (isCompact_Ohat F).image (continuous_const.add continuous_id), ?_⟩
    have ho : IsOpen ((fun y => y - x) ⁻¹' Ohat F) := (isOpen_Ohat F).preimage (continuous_id.sub continuous_const)
    refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
    · show x - x ∈ Ohat F
      rw [sub_self]; exact zero_mem (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F)
    · intro y hy
      exact ⟨y - x, hy, by simp⟩

instance lcAfin : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := WeaklyLocallyCompactSpace.locallyCompactSpace

instance lcAF : LocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end Formalism.IndefR.PHeisFC

end
end
