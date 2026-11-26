module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGF
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ExtendByIdentitySymmFixOrth
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Assemble
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Asm

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

section Gen

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem cJ_le (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : cJ h X L 𝔭 ≤ finrank K X := by
  unfold cJ
  by_cases hS : ∃ b a, IsJordanIn h X L 𝔭 b a
  · obtain ⟨b, a, hJ⟩ := hS
    refine (Nat.sInf_le (show cJof 𝔭 a ∈ {c | ∃ b a, IsJordanIn h X L 𝔭 b a ∧ c = cJof 𝔭 a} from
      ⟨b, a, hJ, rfl⟩)).trans ?_
    unfold cJof
    exact (Finset.card_filter_le _ _).trans (by simp)
  · have he : {c | ∃ b a, IsJordanIn h X L 𝔭 b a ∧ c = cJof 𝔭 a} = ∅ := by
      ext c
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨b, a, hJ, -⟩
      exact hS ⟨b, a, hJ⟩
    rw [he, Nat.sInf_empty]
    exact Nat.zero_le _

theorem integral_of_unimod {h : V →ₗ⋆[K] V →ₗ[K] K} {Λ : Submodule (𝓞 K) V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular h Λ) : Formalism.HermitianLatticesTheory.IsIntegralLat h Λ := by
  intro x hx y hy
  have hy' : y ∈ Formalism.HermitianLatticesTheory.dual h Λ := by rw [hU]; exact hy
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hy'
  exact hy' x hx

theorem glueSet_eq_empty {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {M : Submodule (𝓞 K) V}
    (hM : ¬ Formalism.HermitianLatticesTheory.IsIntegralLat h M) : GlueSet h U M = ∅ := by
  ext Λ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, hU, hΛ⟩
  apply hM
  intro x hx y hy
  rw [← hΛ] at hx hy
  exact integral_of_unimod hU x (Submodule.mem_inf.mp hx).1 y (Submodule.mem_inf.mp hy).1

theorem isGlueReps_empty {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {M : Submodule (𝓞 K) V}
    (hE : GlueSet h U M = ∅) : IsGlueReps h U M ∅ := by
  refine ⟨fun Λ hΛ => absurd hΛ (Finset.notMem_empty Λ), fun Λ hΛ => ?_,
    fun Λ hΛ => absurd hΛ (Finset.notMem_empty Λ)⟩
  rw [hE] at hΛ
  exact absurd hΛ (Set.notMem_empty Λ)

end Gen

section Mass

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem cOne_spec (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    0 < cOne K F ∧ MassConst K F 1 (cOne K F) := by
  obtain ⟨c₁, hc₁, hall⟩ := massConst_all hermRepUnram liStat hK hF
  have he : Finset.Icc 2 1 = ∅ := Finset.Icc_eq_empty (by norm_num)
  have h1 := hall 1 le_rfl
  rw [he, Finset.prod_empty, mul_one] at h1
  have hex : ∃ c : ℝ, 0 < c ∧ MassConst K F 1 c := ⟨c₁, hc₁, h1⟩
  unfold cOne
  rw [dite_eq_left hex]
  exact hex.choose_spec

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem cMass_spec (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    ∀ m : ℕ, 1 ≤ m → 0 < cMass K F m ∧ MassConst K F m (cMass K F m) := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · have he : Finset.Icc 2 (0 + 1) = ∅ := Finset.Icc_eq_empty (by norm_num)
      unfold cMass
      rw [he, Finset.prod_empty, mul_one]
      exact cOne_spec hK hF
    · obtain ⟨h0, hc⟩ := ih hpos
      have hstep := massConst_succ hermRepUnram liStat hK hF (m := m + 1) (by omega) h0
        (by simpa using hc)
      have hr := massRatio_pos hK (m + 1) (by omega)
      have heq : cMass K F (m + 1) = cMass K F m * Formalism.HermitianLatticesTheory.massRatioRightSide K (m + 1) := by
        unfold cMass
        rw [Finset.prod_Icc_succ_top (by omega), mul_assoc]
      rw [heq]
      exact ⟨mul_pos h0 hr, hstep⟩

theorem hasProd_lF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (i : ℕ) (hi : 2 ≤ i) :
    HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} =>
      (1 - etaF K F 𝔭.1 ^ i * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(i : ℤ)))⁻¹) (lValEtaF K F i) := by
  let π := fun x : {P : Ideal (𝓞 K) // P.IsMaximal} =>
    (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), Regroup.comap_isMaximal x.2⟩ :
      {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
  have hf := multipliable_eulerFac hK i hi
  have h1 : HasProd (fun p : (Σ b, {x // π x = b}) =>
      Formalism.HermitianLatticesTheory.eulerFac K i (Equiv.sigmaFiberEquiv π p).1) (Formalism.HermitianLatticesTheory.lValEta K i) :=
    (Equiv.sigmaFiberEquiv π).hasProd_iff.2 hf.hasProd
  have h2 := HasProd.sigma h1 (Regroup.hasProd_fibre hK hF i (by omega))
  rw [← lValEta_eq_lValEtaF hK hF i hi]
  exact h2

theorem alpha_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k r : ℕ} (hk : 1 ≤ k) (hkr : k - 1 ≤ r) :
    alphaStd K 𝔭 (k - 1) = alphaStd K 𝔭 r *
      ∏ i ∈ Finset.Icc k r, (1 - etaF K F 𝔭 ^ i * (Ideal.absNorm 𝔭 : ℝ) ^ (-(i : ℤ)))⁻¹ := by
  have hsplit : alphaStd K 𝔭 r = alphaStd K 𝔭 (k - 1) *
      ∏ i ∈ Finset.Icc k r, (1 - etaF K F 𝔭 ^ i * (Ideal.absNorm 𝔭 : ℝ) ^ (-(i : ℤ))) := by
    unfold alphaStd
    rw [← Finset.prod_union]
    · congr 1
      ext i
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega
    · rw [Finset.disjoint_left]
      intro i hi hi'
      simp only [Finset.mem_Icc] at hi hi'
      omega
  have hpos := alphaStd_pos hK hF h𝔭 r
  have hne : (∏ i ∈ Finset.Icc k r,
      (1 - etaF K F 𝔭 ^ i * (Ideal.absNorm 𝔭 : ℝ) ^ (-(i : ℤ)))) ≠ 0 := by
    intro h0
    rw [hsplit, h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  rw [hsplit, Finset.prod_inv_distrib, mul_assoc, mul_inv_cancel₀ hne, mul_one]

def plEquiv : IsDedekindDomain.HeightOneSpectrum (𝓞 F) ≃ {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} where
  toFun P := ⟨P.asIdeal, P.isMaximal⟩
  invFun 𝔭 := ⟨𝔭.1, 𝔭.2.isPrime, fun h =>
    NumberField.RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr (h ▸ 𝔭.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Mass

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.L2.SG.Pf.Asm

namespace Formalism.L2.SG.Pf

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.Asm

attribute [local instance] Formalism.BasicNotions.Host.cmStar


end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PerpendicularDefinitionHolds
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PairSpanDimension

variable {D : Formalism.BasicNotions.D7}

theorem totPos_ne_zero {x : D.host.E} (hx : TotPos x) : x ≠ 0 := by
  have : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; have := D.R.two_le_m; have := D.R.m_le_f
    unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n; omega)
  obtain ⟨τ⟩ := this
  intro h
  have := hx τ
  rw [h, map_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

def fam {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V :=
  Sum.elim F0.fvec F'.fl.fvec

variable {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')

theorem upair_eq : UPair D F0 F' = Submodule.span D.host.E (Set.range (fam F0 F')) := by
  unfold UPair fam
  rw [Set.Sum.elim_range]

theorem hT_fam (a b : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) :
    (VS D).hT (fam F0 F' a) (fam F0 F' b) = Ga T T' (ZhatL (lf D F0) F') a b := by
  have hs : ∀ x y, star ((VS D).hT x y) = (VS D).hT y x := by
    intro x y
    rw [← starRingEnd_apply]
    first
      | exact (VS D).herm.eq x y
      | exact (VS D).herm x y
  have hze : ∀ j, (VS D).hT F0.z (F0.e j) = 0 := fun j => by rw [← hs, F0.z_orth, star_zero]
  have hze' : ∀ j, (VS D).hT F'.fl.z (F'.fl.e j) = 0 := fun j => by rw [← hs, F'.fl.z_orth, star_zero]
  rcases a with a | a <;> rcases b with b | b
  · simp only [fam, Sum.elim_inl, Ga, Matrix.fromBlocks_apply₁₁, Matrix.of_apply]
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp [FlagG.fvec, F0.e_iso, F0.z_orth, F0.z_norm, hze]
  · simp only [fam, Sum.elim_inl, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₁₂]
    rfl
  · simp only [fam, Sum.elim_inl, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]
    show _ = star ((VS D).hT (F0.fvec b) (F'.fl.fvec a))
    rw [hs]
  · simp only [fam, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp [FlagG.fvec, F'.fl.e_iso, F'.fl.z_orth, F'.fl.z_norm, hze']

theorem eq_zero_of_orth (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0)
    (c : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → D.host.E)
    (h : ∀ a, (VS D).hT (fam F0 F' a) (∑ i, c i • fam F0 F' i) = 0) : c = 0 := by
  have hdet : (Ga T T' (ZhatL (lf D F0) F')).det ≠ 0 := by
    rw [PI.UnitaryGroupMassFormula.CntFormula.DetGa.det_Ga]
    refine mul_ne_zero ?_ hG
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.sumComm (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)))) with h1 | h1 <;>
      rw [h1] <;> simp
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  funext a
  have ha := h a
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul, hT_fam] at ha
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  rw [← ha]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem fam_li (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0) : LinearIndependent D.host.E (fam F0 F') := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 := eq_zero_of_orth F0 F' hG c (fun a => by rw [hc, map_zero])
  intro i
  exact congrFun h0 i

theorem mem_orthK {U : Submodule D.host.E (VS D).V} {x : (VS D).V} :
    x ∈ orthK (VS D).hT U ↔ ∀ u ∈ U, (VS D).hT u x = 0 := by
  simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker]

theorem inf_orth (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0) :
    UPair D F0 F' ⊓ orthK (VS D).hT (UPair D F0 F') = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hxU, hxO⟩ := hx
  rw [upair_eq, Submodule.mem_span_range_iff_exists_fun] at hxU
  obtain ⟨c, rfl⟩ := hxU
  have hc := eq_zero_of_orth F0 F' hG c (fun a => (mem_orthK.mp hxO) _
    (by rw [upair_eq]; exact Submodule.subset_span ⟨a, rfl⟩))
  rw [Submodule.mem_bot, hc]
  simp

theorem isCompl (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0) :
    IsCompl (UPair D F0 F') (orthK (VS D).hT (UPair D F0 F')) := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff]
    exact inf_orth F0 F' hG
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    let Φ : ((Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) → D.host.E) →ₗ[D.host.E]
        ((Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) → D.host.E) :=
      { toFun := fun c a => (VS D).hT (fam F0 F' a) (∑ i, c i • fam F0 F' i)
        map_add' := by
          intro c d
          ext a
          simp [add_smul, Finset.sum_add_distrib]
        map_smul' := by
          intro s c
          ext a
          simp [mul_smul, ← Finset.smul_sum, mul_add] }
    have hinj : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro c hc
      exact eq_zero_of_orth F0 F' hG c (fun a => congrFun hc a)
    obtain ⟨c, hc⟩ := (LinearMap.injective_iff_surjective.mp hinj) (fun a => (VS D).hT (fam F0 F' a) v)
    have hu : ∑ i, c i • fam F0 F' i ∈ UPair D F0 F' := by
      rw [upair_eq]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    have hw : v - ∑ i, c i • fam F0 F' i ∈ orthK (VS D).hT (UPair D F0 F') := by
      rw [mem_orthK]
      intro u hu'
      rw [upair_eq] at hu'
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        have h1 := congrFun hc a
        simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h1
        rw [map_sub, h1, sub_self]
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
      | smul s x _ hx => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]
    have hv : v = ∑ i, c i • fam F0 F' i + (v - ∑ i, c i • fam F0 F' i) := by abel
    rw [hv]
    exact Submodule.add_mem_sup hu hw

theorem finrank_upair (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0) :
    finrank D.host.E (UPair D F0 F') = D.R.m := by
  rw [upair_eq, finrank_span_eq_card (fam_li F0 F' hG)]
  simp only [Fintype.card_sum, Fintype.card_fin]
  have := D.R.rS_two
  omega

theorem finrank_V : finrank D.host.E (VS D).V = D.R.r := by
  rw [(VS D).rank_eq, D.sp.Y_rank 0 (Nat.zero_le _)]
  simp [Formalism.BasicNotions.Ranks.rankY]

theorem X_le_upair : F0.X ≤ UPair D F0 F' := by
  unfold FlagG.X UPair
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  left
  exact ⟨i.castSucc, by simp [FlagG.fvec]⟩

theorem z_mem_upair : F0.z ∈ UPair D F0 F' := by
  unfold UPair
  exact Submodule.subset_span (Or.inl ⟨Fin.last _, by simp [FlagG.fvec]⟩)

theorem Xplus_le_upair : F0.Xplus ≤ UPair D F0 F' := by
  unfold FlagG.Xplus
  exact sup_le (X_le_upair F0 F') ((Submodule.span_singleton_le_iff_mem _ _).mpr (z_mem_upair F0 F'))

end PairSpanDimension


open PairSpanDimension in
theorem perpendicular_definition_holds : PerpDef := by
  intro D u u' _ F0 what₂ _ Z F' _ hZ hP
  have hG : GZ (Tn u) (Tn u') (ZhatL (lf D F0) F') ≠ 0 := by rw [hZ]; exact totPos_ne_zero hP
  have hC := PairSpanDimension.isCompl F0 F' hG
  have hU := PairSpanDimension.finrank_upair F0 F' hG
  have hW : finrank D.host.E (orthK (VS D).hT (UPair D F0 F')) = D.R.k - 1 := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hC
    have h2 := D.R.r_eq
    rw [PairSpanDimension.finrank_V, hU] at h1
    omega
  refine ⟨hC, ?_, hU, hW⟩
  intro x hx hx0 φ
  have hpos := Formalism.MainNotions.LatticeGluingRadicals.p_posX D (D.mem u).A.T (D.mem u).A.T_prime.pos (lf D F0)
  have hxO : x ∈ orth (VS D) (Xplus (lf D F0)) := by
    rw [Formalism.MainNotions.LatticeGluingRadicals.p_mem_orth]
    intro w hw
    exact (PairSpanDimension.mem_orthK.1 hx) w (PairSpanDimension.Xplus_le_upair F0 F' hw)
  have hxX : x ∉ Xsp (lf D F0) := by
    intro hxX
    have : x ∈ UPair D F0 F' ⊓ orthK (VS D).hT (UPair D F0 F') := ⟨PairSpanDimension.X_le_upair F0 F' hxX, hx⟩
    rw [PairSpanDimension.inf_orth F0 F' hG] at this
    exact hx0 ((Submodule.mem_bot _).1 this)
  exact hpos φ x hxO hxX

end Formalism.L2.SG.Pf.Cnt
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FieldDictionaryHolds
namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem field_dictionary_holds : HostDict := by
  intro D
  refine ⟨D.sp.cm.cmUnram, ?_, ?_⟩
  · intro a
    rw [D.sp.cm.fixed a, RingHom.mem_range, Set.mem_range]
  · intro x hx
    exact (D.sp.Y 0).nondeg.1 x hx

end Formalism.L2.SG.Pf.Cnt
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemSpanIffSpanS
open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem form_sum_orth {ι : Type} [Fintype ι] {b : ι → V} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (c : ι → K) (i : ι) : h (b i) (∑ j, c j • b j) = c i * h (b i) (b i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [ho i j (Ne.symm hji), mul_zero])
    (fun hi => absurd (Finset.mem_univ i) hi)]

end

end Formalism.L2.SG.Pf.G3
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ProjectionIntoHolds
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_dual_iff {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {v : V} :
    v ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y v ∈ (1 : Submodule (𝓞 K) K) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

theorem form_ozmul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 K) (y v : V) : h y (c • v) = c • h y v := by
  rw [← algebraMap_smul K c v, LinearMap.map_smul, algebraMap_smul]

theorem form_ozmul_left_mem (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 K) {y v : V}
    (hy : h y v ∈ (1 : Submodule (𝓞 K) K)) : h (c • y) v ∈ (1 : Submodule (𝓞 K) K) := by
  rw [← algebraMap_smul K c y, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  obtain ⟨c0, hc0⟩ := Submodule.mem_one.mp (VecSplit.star_alg_mem_one c)
  obtain ⟨z0, hz0⟩ := Submodule.mem_one.mp hy
  exact Submodule.mem_one.mpr ⟨c0 * z0, by rw [map_mul, hc0, hz0]⟩

theorem mem_locF_dualIn {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) V}
    (hL : L.FG) (𝔭 : Ideal (𝓞 F)) {v : V} (hv : v ∈ X)
    (H : ∀ y ∈ L, h y v ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) : v ∈ locF 𝔭 (dualIn h X L) := by
  classical
  obtain ⟨s, hs⟩ := hL
  have H' : ∀ y ∈ s, ∃ t ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s},
      t • h y v ∈ (1 : Submodule (𝓞 K) K) := by
    intro y hy
    exact H y (hs ▸ Submodule.subset_span hy)
  choose! t ht using H'
  refine ⟨∏ y ∈ s, t y, Submonoid.prod_mem _ fun y hy => (ht y hy).1, ?_⟩
  refine ⟨X.restrictScalars (𝓞 K) |>.smul_mem _ hv, ?_⟩
  show (∏ y ∈ s, t y) • v ∈ Formalism.HermitianLatticesTheory.dual h L
  rw [mem_dual_iff]
  intro y hy
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [form_ozmul_right, ← Finset.prod_erase_mul s t hy, mul_smul]
    exact Submodule.smul_mem _ _ (ht y hy).2
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add (f := _), LinearMap.add_apply]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact form_ozmul_left_mem h c ha

theorem projection_into_holds : ProjInto := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd X Y hc hXY L hL 𝔭 h𝔭 Λ hΛ0 hΛd hΛX x hx
  apply mem_locF_dualIn hL.1 𝔭 (Submodule.projection_apply_mem hc x)
  intro y hy
  have hyΛ : y ∈ Λ := by
    have : y ∈ locF 𝔭 L := LocalizedFibreSets.le_locF 𝔭 L hy
    rw [← hΛX] at this
    exact this.1
  have hyX : y ∈ X := le_of_isLatIn hL y hy
  have e := Submodule.projection_add_projection_eq_self hc x
  have h0 : h y (Y.projection X hc.symm x) = 0 := hXY y hyX _ (Submodule.projection_apply_mem _ x)
  have hx' : x ∈ dualF h 𝔭 Λ := by rw [hΛd]; exact hx
  have := hx' y hyΛ
  rw [← e, map_add (f := _), h0, add_zero] at this
  exact this

end Formalism.L2.SG.Pf.G6
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NondegOnOfCompl
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans

def IsGlueData {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) {n m : ℕ} (a : Fin n → 𝓞 F)
    (π : 𝓞 F) (w : Fin m → V) (c : Fin m → F) (τ : Fin n → Fin m) : Prop :=
  (∀ j, w j ∈ orthK h U) ∧ (∀ j k, j ≠ k → h (w j) (w k) = 0) ∧
  (∀ j, h (w j) (w j) = algebraMap F K (c j) ∧ c j ≠ 0) ∧
  (∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k) ∧
  (∃ s₀ : 𝓞 F, IsUnif0 𝔭 π s₀) ∧
  (∀ i, vF 𝔭 (a i) ≠ 0 →
    InP 𝔭 (2 * vF 𝔭 (a i)) (algebraMap F K ((a i : F) + c (τ i)))) ∧
  (∀ j, (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) →
    InP 𝔭 0 (algebraMap F K (c j)) ∧ InP 𝔭 0 (algebraMap F K (c j)⁻¹))

def GlueVecs : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    cJof 𝔭 a < finrank K (orthK h U) →
      ∃ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
        (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ

def GlueAssemble : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ →
      ∃ T : Submodule (𝓞 K) V, (∃ A : Submodule (𝓞 K) V, Submodule.IsLattice K A ∧ locF 𝔭 A = T) ∧
        dualF h 𝔭 T = T ∧ T ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem nondegOn_of_compl {h : V →ₗ⋆[K] V →ₗ[K] K} (hnd : Nondeg h) {U : Submodule K V}
    (hUc : IsCompl U (orthK h U)) : NondegOn h U := by
  intro x hx hxU
  apply hnd
  intro y
  have hy : y ∈ U ⊔ orthK h U := by rw [hUc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
  have hz' : h x z = 0 := by
    have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hz x) hx
    exact LinearMap.mem_ker.1 this
  rw [map_add (f := _), hxU u hu, hz', add_zero]

theorem glueLocal_of_of (hJ : JordanExists) (hV : GlueVecs) (hA : GlueAssemble) :
    Formalism.L2.SG.Pf.G7.GlueLocal := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 hc
  have hne : {c | ∃ b a, IsJordanIn h U M 𝔭 b a ∧ c = cJof 𝔭 a}.Nonempty := by
    obtain ⟨b, a, hba⟩ := (hJ K F V hK hF h hs).1 U M (nondegOn_of_compl hnd hUc) hM hMi 𝔭 h𝔭
    exact ⟨_, b, a, hba, rfl⟩
  obtain ⟨b, a, hba, hca⟩ := Nat.sInf_mem hne
  have hc' : cJof 𝔭 a < finrank K (orthK h U) := by
    rw [← hca]; exact hc
  obtain ⟨π, w, c, τ, hg⟩ := hV K F V hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc'
  exact hA K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg

end Formalism.L2.SG.Pf.GluingBases
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantNormShapes
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

def skSet (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    Set (Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :=
  {X | Xᴴ * diagQ K 𝔭 k a * X = diagQ K 𝔭 k a}

def udPre (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) : Type :=
  {Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) //
    (∃ P, P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y) ∧
    ∃ W, Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a}

def udSetoid (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    Setoid (udPre K 𝔭 k a) where
  r Y Y' := ∃ Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), Y.1 - Y'.1 = Z * diagQ K 𝔭 k a
  iseqv := {
    refl := fun Y => ⟨0, by simp⟩
    symm := fun ⟨Z, hZ⟩ => ⟨-Z, by rw [Matrix.neg_mul, ← hZ, neg_sub]⟩
    trans := fun ⟨Z, hZ⟩ ⟨Z', hZ'⟩ => ⟨Z + Z', by rw [Matrix.add_mul, ← hZ, ← hZ', sub_add_sub_cancel]⟩ }

def udQ (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) : Type :=
  Quotient (udSetoid K 𝔭 k a)

def UDModel : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h →
    ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L → Formalism.HermitianLatticesTheory.IsIntegralLat h L →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h ⊤ L 𝔭 b a →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → discAut h ⊤ L 𝔭 = Nat.card (udQ K 𝔭 k a)

def OrbitCount : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k →
      Nat.card (skSet K 𝔭 k a) = Nat.card (udQ K 𝔭 k a) * Nat.card (kerSet K 𝔭 k a)

section

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem linearIndependent_of_jordan {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} {b : Fin (finrank K (⊤ : Submodule K V)) → V}
    {a : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F} (hb : IsJordanIn h ⊤ L 𝔭 b a) :
    LinearIndependent K b := by
  obtain ⟨-, -, horth, hdiag, hne⟩ := hb
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h1 : h (b i) (∑ j ∈ s, g j • b j) = 0 := by rw [hg, map_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single i] at h1
  · rw [map_smul, smul_eq_mul, hdiag] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd (by simpa using h2) (hne i)
  · intro j _ hji
    rw [map_smul, horth i j (Ne.symm hji), smul_zero]
  · intro hi'
    exact absurd hi hi'

variable [Fact (IsFixF K F)]

theorem akCount_eq_skSet {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {b : Fin (finrank K (⊤ : Submodule K V)) → V}
    {a : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F} (hb : IsJordanIn h ⊤ L 𝔭 b a) (k : ℕ) :
    akCount h L 𝔭 k = Nat.card (skSet K 𝔭 k a) := by
  have hli := linearIndependent_of_jordan hb
  have hcard : Fintype.card (Fin (finrank K (⊤ : Submodule K V))) = finrank K V := by
    simp [finrank_top]
  have hB : ⇑(Basis.mk hli (le_of_eq (hli.span_eq_top_of_card_eq_finrank' hcard).symm)) = b :=
    Basis.coe_mk _ _
  have hH : ∀ i j, algebraMap (𝓞 K) K
      ((Matrix.diagonal fun i => algebraMap (𝓞 F) (𝓞 K) (a i)) i j) =
      h (Basis.mk hli (le_of_eq (hli.span_eq_top_of_card_eq_finrank' hcard).symm) i)
        (Basis.mk hli (le_of_eq (hli.span_eq_top_of_card_eq_finrank' hcard).symm) j) := by
    intro i j
    rw [hB]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, hb.2.2.2.1 i]
      rfl
    · rw [Matrix.diagonal_apply_ne _ hij, map_zero]
      exact (hb.2.2.1 i j hij).symm
  rw [integralBasisSpans.akCount_eq h h𝔭 _ (by
    have h2 := hb.2.1
    rw [← hB] at h2
    exact h2) hH k]
  have hd : (Matrix.diagonal fun i => algebraMap (𝓞 F) (𝓞 K) (a i)).map
      (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = diagQ K 𝔭 k a := by
    rw [diagQ, Matrix.diagonal_map (map_zero _)]
  rw [hd]
  rfl

end

theorem discOnto_of (hU : UDModel) (hO : OrbitCount) : DiscOnto := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ _ hK h hsymm hpos L hL hint 𝔭 h𝔭 b a hb k hk
  have ha : ∀ i, a i ≠ 0 := by
    obtain ⟨-, -, -, -, h5⟩ := hb
    exact h5
  rw [akCount_eq_skSet h𝔭 hb k, hO K F hK 𝔭 h𝔭 _ a ha k hk,
    hU K F V hK h hsymm hpos L hL hint 𝔭 h𝔭 b a hb k hk]

end Formalism.L2.SG.Pf.discriminantNormShapes
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcTieCOf
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NormalizingConstantEq
noncomputable section

namespace Formalism.L2.SG.Pf.NcCut

open Formalism.FourierDecayAlt.S3

variable {P : Type} [Fintype P] (B : MassData P)

theorem MM_eq (hP : B.Pos) (hO : B.InOrdinary) (hT : B.InTyped) :
    B.MM = B.unitLevelVolume * B.μK * B.μKnat / (B.μS * B.μS') := by
  obtain ⟨hp, -, -, -, -, hU0, -⟩ := hP
  have h0 : B.Mo = B.localVolumeArchimedean * (B.μKo * B.μKo) / (B.μSo * B.μSo') := by
    have h := hO
    unfold MassData.InOrdinary at h
    rw [div_eq_iff hU0.ne'] at h
    rw [h]
    ring
  have h1 : ∀ p, B.Mp p = B.localVolumeAtPlace p * (B.μKp p * B.μKnatp p) / (B.μSp p * B.μSp' p) := by
    intro p
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hU⟩ := hp p
    have h := (hT p).1
    rw [div_eq_iff hU.ne'] at h
    rw [h]
    ring
  unfold MassData.MM MassData.unitLevelVolume MassData.μK MassData.μKnat MassData.μS MassData.μS'
  simp only [h0, h1, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  rw [div_mul_div_comm]
  congr 1 <;> ring

theorem normalizing_constant_eq (hP : B.Pos) (hM : B.InMass) (hMs : B.InMasses) (hL : B.InLevelS) (hO : B.InOrdinary)
    (hT : B.InTyped) (hV : B.volNa = 1 ∧ B.volNa' = 1) :
    B.n0c = B.volB / B.volHa * B.Coo * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) * B.μKnat / B.μH' := by
  have hMM := MM_eq B hP hO hT
  obtain ⟨hp, hKo, -, -, -, -, hH, hH', -, -, hN, hN', hZZ, -, -, -, hHa, -, -, -, hB, hVH, -, -, -,
    hCoo, -, -, -, hr0, -⟩ := hP
  obtain ⟨hρ, hNa, -, hNa'⟩ := hMs
  obtain ⟨hS, -, hS', -⟩ := hL
  have hK : 0 < B.μK := by
    unfold MassData.μK
    exact mul_pos hKo (Finset.prod_pos fun p _ => (hp p).2.2.2.2.2.1)
  have hvN : B.volN = 1 / B.μN := by
    rw [eq_div_iff hN.ne', ← hNa, hV.1]
  have hvN' : B.volN' = 1 / B.μN' := by
    rw [eq_div_iff hN'.ne', ← hNa', hV.2]
  have hM' : B.n0c * B.ρ0 = B.AA := hM
  unfold MassData.AA at hM'
  rw [hMM, hS, hS'] at hM'
  have hn := eq_div_of_mul_eq hr0.ne' hM'
  rw [hn, hρ, hvN, hvN']
  have h1 := hK.ne'
  have h2 := hH.ne'
  have h3 := hH'.ne'
  have h4 := hN.ne'
  have h5 := hN'.ne'
  have h6 := hZZ.ne'
  have h7 := hHa.ne'
  have h8 := hVH.ne'
  field_simp

theorem nc_iff (hP : B.Pos) (hM : B.InMass) (hMs : B.InMasses) (hL : B.InLevelS) (hO : B.InOrdinary)
    (hT : B.InTyped) (hV : B.volNa = 1 ∧ B.volNa' = 1) (c ng kap : ℝ) (hkap : kap ≠ 0) :
    c = B.n0c * ng / (B.al * kap) ↔
      c * B.al * kap = B.volB / B.volHa * B.Coo * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) *
        B.μKnat / B.μH' * ng := by
  rw [normalizing_constant_eq B hP hM hMs hL hO hT hV]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hal, -⟩ := hP
  rw [eq_div_iff (mul_ne_zero hal.ne' hkap)]
  constructor <;> intro h <;> linear_combination h

end Formalism.L2.SG.Pf.NcCut
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcAsm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

def NcValueC : Prop :=
  Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂ * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).al =
    Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH *
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN *
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN' *
      ((bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).unitLevelVolume /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volZZ) *
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnat /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' * ngFac D

theorem ncTieC_of
    (hP : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos)
    (hM : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMass)
    (hMs : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMasses)
    (hL : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InLevelS)
    (hO : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InOrdinary)
    (hT : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InTyped)
    (hV : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InVolumes)
    (hVG : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG)
    (hCoo : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Coo =
      Formalism.L2.SG.MassDataConc.kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1)
    (hkap : Formalism.L2.SG.MassDataConc.kapN D ≠ 0)
    (hval : NcValueC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) := by
  unfold NcTieC
  set B := bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq with hB
  rw [Formalism.L2.SG.Pf.NcCut.nc_iff B hP hM hMs hL hO hT ⟨hV.2.1, hV.2.2⟩ _ (ngFac D) (Formalism.L2.SG.MassDataConc.kapN D) hkap]
  have hG : 0 < B.volG := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hHa : 0 < B.volHa := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBH : B.volB / B.volHa = 1 := by
    have h1 := hV.1
    rw [hVG] at h1
    have : B.volB = B.volHa := by
      have := mul_right_cancel₀ hG.ne' h1
      exact this
    rw [this, div_self hHa.ne']
  rw [hBH, hCoo]
  unfold NcValueC at hval
  rw [← hB] at hval
  linear_combination (Formalism.L2.SG.MassDataConc.kapN D) * hval

theorem kapN_ne (D : D7) : Formalism.L2.SG.MassDataConc.kapN D ≠ 0 := by
  unfold Formalism.L2.SG.MassDataConc.kapN
  have h1 := (Formalism.BasicNotions.rdE_pos_le D).1
  have hg : (0 : ℝ) < (Formalism.MainNotions.S.Lat.gS D : ℝ) := by
    have h0 := (D.host.g_prime 0).pos
    have h1' := (D.host.g_prime 1).pos
    unfold Formalism.MainNotions.S.Lat.gS
    exact_mod_cast Nat.mul_pos h0 h1'
  exact mul_ne_zero (pow_ne_zero _ h1.ne') (inv_ne_zero (pow_ne_zero _ hg.ne'))

theorem coo_bCF : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Coo =
    Formalism.L2.SG.MassDataConc.kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 := rfl

theorem ncTieC_of'
    (hP : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos)
    (hM : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMass)
    (hMs : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMasses)
    (hL : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InLevelS)
    (hO : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InOrdinary)
    (hT : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InTyped)
    (hV : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InVolumes)
    (hVG : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG)
    (hval : NcValueC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) :=
  ncTieC_of X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hP hM hMs hL hO hT hV hVG
    (coo_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq) (kapN_ne D) hval

end Formalism.L2.SG.Pf.NcAsm
end
end
