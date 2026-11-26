module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapExactMiddle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetMassEqRelIndexMulMass
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DiagonalQuotientEigen
public import Formalism.LocalToGlobal.CharacterGerms.RowTieCartAdd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupMonomialHolderLogConvex
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupMonomialHolderLogConvex
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime]

theorem gA_teichmuller (ρ : ℝ) (y : Formalism.Per.Fl l) :
    gA l ρ (Formalism.Per.tm y) = ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have h : ∀ n : ℕ, ‖((((Formalism.Per.tm y : Formalism.Per.Ainf l).coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^
      ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n = if n = 0 then ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ else 0 := by
    intro n
    split_ifs with h
    · subst h
      simp
    · rw [WittVector.teichmuller_coeff_pos l y n (Nat.pos_of_ne_zero h), GlobalTheory.GaussSlope.untilt_zero]
      have : (1 : ℝ) / (l : ℝ) ^ n ≠ 0 := by positivity
      simp only [ZeroMemClass.coe_zero, norm_zero, Real.zero_rpow this, zero_mul]
  unfold gA
  simp only [h]
  have hall : ∀ n : ℕ, (if n = 0 then ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ else 0) ≤
      ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := fun n => by split_ifs <;> simp
  exact le_antisymm (ciSup_le hall)
    (le_ciSup_of_le (f := fun n : ℕ => if n = 0 then ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ else 0)
      ⟨_, Set.forall_mem_range.2 hall⟩ 0 (by simp))

theorem isGauss_unit_eq_one {ρ : ℝ} (hρ : 0 < ρ) {N : Formalism.Per.Acris l → ℝ} (hN : IsGauss l ρ N)
    {x : Formalism.Per.Acris l} (hx : IsUnit x) : N x = 1 := by
  obtain ⟨h01, -, -, hmul, halg⟩ := hN
  have hl : N (l : Formalism.Per.Acris l) = ρ := by
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, halg]
    exact GlobalTheory.GaussSlope.gauss_l l hρ.le
  have h1 : N 1 = 1 := by
    have := hmul (l : Formalism.Per.Acris l) 1
    rw [mul_one, hl] at this
    exact (mul_left_cancel₀ hρ.ne' (this.symm.trans (mul_one ρ).symm))
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h2 := hmul x y
  rw [hy, h1] at h2
  refine le_antisymm (h01 x).2 ?_
  rw [h2]
  exact mul_le_of_le_one_right (h01 x).1 (h01 y).2

theorem gC_basic_values : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ 1 = 1 ∧ gC l ρ (l : Formalism.Per.Acris l) = ρ ∧ (∀ c : ℤ_[l], c ≠ 0 → gC l ρ (zc l c) = ρ ^ c.valuation) ∧ (∀ y : Formalism.Per.Fl l, gC l ρ (tc l y) = ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖) ∧ ∀ a : Formalism.Per.Ainf l, IsUnit a → gC l ρ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) = 1 := by
  intro l _ ρ h0 h1
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hρ : 0 < ρ := (inv_pos.2 hl0).trans_le h0
  have hN := isGauss_gC_of_le l ρ h0 h1
  have hl : gC l ρ (l : Formalism.Per.Acris l) = ρ := by
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, hN.2.2.2.2]
    exact GlobalTheory.GaussSlope.gauss_l l hρ.le
  refine ⟨isGauss_unit_eq_one hρ hN isUnit_one, hl, fun c hc => ?_, fun y => ?_,
    fun a ha => isGauss_unit_eq_one hρ hN (ha.map _)⟩
  · have e : zc l c = (l : Formalism.Per.Acris l) ^ c.valuation * zc l (PadicInt.unitCoeff hc : ℤ_[l]) := by
      conv_lhs => rw [PadicInt.unitCoeff_spec hc]
      rw [map_mul, map_pow, map_natCast, mul_comm]
    rw [e, GlobalTheory.GaussSlope.map_pow_mul _ hN.2.2.2.1, hl,
      isGauss_unit_eq_one hρ hN ((PadicInt.unitCoeff hc).isUnit.map (zc l)), mul_one]
  · rw [tc, hN.2.2.2.2, gA_teichmuller]

end GlobalTheory.PMon.Gauss

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupMonomialHolderLogConvexStatement
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussNormAcris_basic_values : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ 1 = 1 ∧ gC l ρ (l : Formalism.Per.Acris l) = ρ ∧ (∀ c : ℤ_[l], c ≠ 0 → gC l ρ (zc l c) = ρ ^ c.valuation) ∧ (∀ y : Formalism.Per.Fl l, gC l ρ (tc l y) = ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖) ∧ ∀ a : Formalism.Per.Ainf l, IsUnit a → gC l ρ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) = 1 := by
  first | exact @GlobalTheory.PMon.Gauss.gC_basic_values | exact GlobalTheory.PMon.Gauss.gC_basic_values | (intros; apply GlobalTheory.PMon.Gauss.gC_basic_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPreimageOfInjectiveFinDimRepModelHom
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPreimageOfInjectiveFinDimRepModelHom
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.SubModel

variable {k G : Type} [Field k] [Group G]

theorem exists_ker (A B : Ob k G) (g : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hg : IsHom A B g) :
    ∃ (K : Ob k G) (i : (Fin K.m → k) →ₗ[k] (Fin A.m → k)),
      IsHom K A i ∧ Function.Injective i ∧ Function.Exact i g := by
  have hst : ∀ s : G, LinearMap.ker g ≤ (LinearMap.ker g).comap (A.ρ s) := by
    intro s x hx
    simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
    rw [hg, hx, map_zero]
  obtain ⟨K, e, he⟩ := exists_ob (A.ρ.subrepresentation (LinearMap.ker g) hst)
  refine ⟨K, (LinearMap.ker g).subtype ∘ₗ e.symm.toLinearMap, ?_, ?_, ?_⟩
  · intro s x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← he]
    simp [Representation.subrepresentation]
  · exact (LinearMap.ker g).injective_subtype.comp e.symm.injective
  · intro y
    constructor
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp⟩
    · rintro ⟨x, rfl⟩
      exact (e.symm x).2

theorem exists_coker (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hf : IsHom A B f) :
    ∃ (Q : Ob k G) (q : (Fin B.m → k) →ₗ[k] (Fin Q.m → k)),
      IsHom B Q q ∧ Function.Surjective q ∧ Function.Exact f q := by
  have hst : ∀ s : G, LinearMap.range f ≤ (LinearMap.range f).comap (B.ρ s) := by
    rintro s _ ⟨x, rfl⟩
    exact ⟨A.ρ s x, hf s x⟩
  obtain ⟨Q, e, he⟩ := exists_ob (B.ρ.quotient (LinearMap.range f) hst)
  refine ⟨Q, e.toLinearMap ∘ₗ (LinearMap.range f).mkQ, ?_, ?_, ?_⟩
  · intro s x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]
    simp [Representation.quotient]
  · exact e.surjective.comp (LinearMap.range f).mkQ_surjective
  · intro y
    simp [Submodule.Quotient.mk_eq_zero]

theorem IsHom.comp' {A B C : Ob k G} {f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    {g : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} (hf : IsHom A B f) (hg : IsHom B C g) : IsHom A C (g ∘ₗ f) := by
  intro s x
  simp only [LinearMap.comp_apply]
  rw [hf, hg]

theorem model_pre : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (N : Lats k n B.m), IsHom A B f → Function.Injective f → M.Model B N → M.Model A (F.pre A B f N) := by
  intro k G _ _ l n _ _ _ R F r Dt M A B f N hf hfi hN
  obtain ⟨C, Nb, A₁, j, p, hb, hj, hji, hp, hps, rfl⟩ := hN
  obtain ⟨Q, q, hq, hqs, hfq⟩ := exists_coker A B f hf
  have hqp : IsHom A₁ Q (q ∘ₗ p) := IsHom.comp' hp hq
  obtain ⟨K, i, hi, hii, hex⟩ := exists_ker A₁ Q (q ∘ₗ p) hqp
  have hr : ∀ x, (p ∘ₗ i) x ∈ LinearMap.range f := fun x => (hfq _).1 ((hex _).2 ⟨x, rfl⟩)
  let p' : (Fin K.m → k) →ₗ[k] (Fin A.m → k) :=
    (LinearEquiv.ofInjective f hfi).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ (p ∘ₗ i) hr
  have hfp : ∀ x, f (p' x) = p (i x) := by
    intro x
    have := congrArg Subtype.val ((LinearEquiv.ofInjective f hfi).apply_symm_apply
      (LinearMap.codRestrict _ (p ∘ₗ i) hr x))
    exact this
  have hp' : IsHom K A p' := by
    intro s x
    apply hfi
    rw [hfp, hf, hfp, hi, hp]
  have hp's : Function.Surjective p' := by
    intro a
    obtain ⟨y, hy⟩ := hps (f a)
    have : (q ∘ₗ p) y = 0 := by
      rw [LinearMap.comp_apply, hy]
      exact (hfq _).2 ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := (hex _).1 this
    exact ⟨x, hfi (by rw [hfp, hy])⟩
  have oC : F.Obj C := M.base_obj _ _ hb
  have o1 : F.Obj A₁ := F.obj_sub _ _ _ hj hji oC
  have oB : F.Obj B := F.obj_quot _ _ _ hp hps o1
  have oA : F.Obj A := F.obj_sub _ _ _ hf hfi oB
  have oK : F.Obj K := F.obj_sub _ _ _ hi hii o1
  have oQ : F.Obj Q := F.obj_quot _ _ _ hq hqs oB
  have hcomm : f ∘ₗ p' = p ∘ₗ i := LinearMap.ext hfp
  have hsq : ∀ a x, F.map A B f a (F.map K A p' a x) = F.map A₁ B p a (F.map K A₁ i a x) := by
    intro a x
    have h1 := F.map_comp K A B p' f oK oA oB hp' hf a
    have h2 := F.map_comp K A₁ B i p oK o1 oB hi hp a
    rw [hcomm, h2] at h1
    exact (LinearMap.congr_fun h1 x).symm
  have e1 := GlobalTheory.T.exact_map_of_exact F A B Q f q oB hf hq hfi hqs hfq
  have e2 := GlobalTheory.T.exact_map_of_exact F K A₁ Q i (q ∘ₗ p) o1 hi hqp hii (hqs.comp hps) hex
  refine ⟨C, Nb, K, j ∘ₗ i, p', hb, IsHom.comp' hi hj, hji.comp hii, hp', hp's, ?_⟩
  funext a
  ext x
  simp only [DFun.pre, DFun.push, Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply,
    F.map_comp K A₁ C i j oK o1 oC hi hj a, LinearMap.comp_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : F.map A₁ Q (q ∘ₗ p) a y = 0 := by
      rw [F.map_comp A₁ B Q p q o1 oB oQ hp hq a, LinearMap.comp_apply, hyx]
      exact (e1 a _).2 ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := (e2 a _).1 this
    exact ⟨z, hy, F.map_inj A B f oA oB hf hfi a (by rw [hsq, hyx])⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, hz, (hsq a z).symm⟩

end GlobalTheory.Models.SubModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPreimageOfInjectiveFinDimRepModelHomStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (N : Lats k n B.m), IsHom A B f → Function.Injective f → M.Model B N → M.Model A (F.pre A B f N) := by
  first | exact @GlobalTheory.Models.SubModel.model_pre | exact GlobalTheory.Models.SubModel.model_pre | (intros; apply GlobalTheory.Models.SubModel.model_pre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityAdditiveExactSequence
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityAdditiveExactSequence
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem sen_eq_sen_pre_add_sen_push : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (N : Lats k n B.m), F.Obj B → IsHom A B f → IsHom B C p → Function.Injective f → Function.Surjective p → Function.Exact f p → ∀ i, IsLat (N i) → CondC ((F.D B).γ i) (N i) → ∀ x, sen ((F.D B).γ i) (N i) x = sen ((F.D A).γ i) (F.pre A B f N i) x + sen ((F.D C).γ i) (F.push B C p N i) x := by
  intro k G _ _ l n _ _ _ R F A B C f p N hB hf hp hfi hps hex i hN hc x
  have hA : F.Obj A := F.obj_sub A B f hf hfi hB
  have hC : F.Obj C := F.obj_quot B C p hp hps hB
  exact GlobalTheory.PhiGam.SenAdd.main R ((F.D B).γ i) ((F.D A).γ i) ((F.D C).γ i) (F.map A B f i) (F.map B C p i)
    ((F.D B).γ_semi i) (F.map_inj A B f hA hB hf hfi i) (F.map_surj B C p hB hC hp hps i)
    (GlobalTheory.Models.DFun.map_exact_middle F A B C f p hB hf hp hfi hps hex i) (F.map_γ A B f hA hB hf i) (F.map_γ B C p hB hC hp i)
    (N i) hN hc x

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityAdditiveExactSequenceStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.senMultiplicity_additive_exact_sequence : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (N : Lats k n B.m), F.Obj B → IsHom A B f → IsHom B C p → Function.Injective f → Function.Surjective p → Function.Exact f p → ∀ i, IsLat (N i) → CondC ((F.D B).γ i) (N i) → ∀ x, sen ((F.D B).γ i) (N i) x = sen ((F.D A).γ i) (F.pre A B f N i) x + sen ((F.D C).γ i) (F.push B C p N i) x := by
  first | exact @GlobalTheory.Models.sen_eq_sen_pre_add_sen_push | exact GlobalTheory.Models.sen_eq_sen_pre_add_sen_push | (intros; apply GlobalTheory.Models.sen_eq_sen_pre_add_sen_push <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HcLCExistsPowSmulEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HcLCExistsPowSmulEqZero
open ReciprocityTheory.Gal
open Formalism.NG
namespace GlobalTheory

theorem hcLC_exists_pow_smul_eq_zero : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M) (ϖ : O),
    (∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0) → ∀ x ∈ ReciprocityTheory.ChartRestriction.T2.HcLC ρ, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  intro O _ G _ _ _ M _ _ ρ ϖ hM x hx
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.1 hx
  have hlc : IsLocallyConstant (c : G → M) := hc
  classical
  let f : M → ℕ := fun m => Classical.choose (hM m)
  have hf : ∀ m, ϖ ^ f m • m = 0 := fun m => Classical.choose_spec (hM m)
  have hfin : (Set.range (c : G → M)).Finite := hlc.range_finite
  obtain ⟨N, hN⟩ := (hfin.image f).bddAbove
  refine ⟨N, ?_⟩
  have hc0 : ϖ ^ N • c = 0 := by
    apply Subtype.ext
    funext g
    have hk : f ((c : G → M) g) ≤ N := hN ⟨_, ⟨g, rfl⟩, rfl⟩
    show ϖ ^ N • (c : G → M) g = 0
    rw [← Nat.sub_add_cancel hk, pow_add, mul_smul, hf, smul_zero]
  rw [← LinearMap.map_smul, hc0, map_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HcLCExistsPowSmulEqZeroStatement
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_eq_zero_of_mem_HcLC_of_torsion : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M) (ϖ : O),
    (∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0) → ∀ x ∈ ReciprocityTheory.ChartRestriction.T2.HcLC ρ, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  first | exact @GlobalTheory.hcLC_exists_pow_smul_eq_zero | exact GlobalTheory.hcLC_exists_pow_smul_eq_zero | (intros; apply GlobalTheory.hcLC_exists_pow_smul_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanOfLocalCohomologyShape
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanOfLocalCohomologyShape
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC

namespace GlobalTheory.ContCocycleDualLattice

universe u

section

variable {O G VT VT' : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] (D : LatData O G VT VT')

theorem mem_dualLat_iff_of_span (s : Finset VT) (hs : Submodule.span O (s : Set VT) = D.T) (f : VT') :
    f ∈ D.T' ↔ ∀ x ∈ s, D.bT x f ∈ Set.range (algebraMap O (FractionRing O)) := by
  constructor
  · intro hf x hx
    have := hf x (hs ▸ Submodule.subset_span hx)
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 this
    exact ⟨y, hy⟩
  · intro hf x hx
    rw [← hs] at hx
    have hle : Submodule.span O (s : Set VT) ≤
        (1 : Submodule O (FractionRing O)).comap (D.bT.flip f) := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨y, hy⟩ := hf x hx
      exact Submodule.mem_one.2 ⟨y, hy⟩
    exact hle hx

theorem isOpen_dualLat (hO : IsOpen (Set.range (algebraMap O (FractionRing O)))) (hT : D.T.FG) :
    IsOpen (D.T' : Set VT') := by
  obtain ⟨s, hs⟩ := hT
  have e : (D.T' : Set VT') = ⋂ x ∈ s, (fun f => D.bT x f) ⁻¹' Set.range (algebraMap O (FractionRing O)) := by
    ext f
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
    exact mem_dualLat_iff_of_span D s hs f
  rw [e]
  refine isOpen_biInter_finset fun x _ => hO.preimage ?_
  exact D.contbT.comp (continuous_const.prodMk continuous_id)

theorem exists_smul_mem_dualLat (hT : D.T.FG) (f : VT') : ∃ c : O, c ≠ 0 ∧ c • f ∈ D.T' := by
  obtain ⟨s, hs⟩ := hT
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) s (fun x => D.bT x f)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, (mem_dualLat_iff_of_span D s hs _).2 fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := hb x hx
  refine ⟨y, ?_⟩
  rw [map_smul]
  exact hy

theorem exists_smul_subset_dualLat (hO : IsOpen (Set.range (algebraMap O (FractionRing O))))
    (hT : D.T.FG) {S : Set VT'} (hS : IsCompact S) : ∃ c : O, c ≠ 0 ∧ ∀ f ∈ S, c • f ∈ D.T' := by
  classical
  choose c hc0 hc using exists_smul_mem_dualLat D hT
  have hopen : IsOpen (D.T' : Set VT') := isOpen_dualLat D hO hT
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun v => (fun w : VT' => c v • w) ⁻¹' (D.T' : Set VT'))
    (fun v => hopen.preimage (continuous_const_smul (c v))) (fun f _ => Set.mem_iUnion.2 ⟨f, hc f⟩)
  refine ⟨∏ v ∈ t, c v, Finset.prod_ne_zero_iff.2 fun v _ => hc0 v, fun f hf => ?_⟩
  obtain ⟨v, hv, hfv⟩ := Set.mem_iUnion₂.1 (ht hf)
  rw [← Finset.mul_prod_erase t c hv, mul_comm, mul_smul]
  exact D.T'.smul_mem _ hfv

theorem exists_smul_mem_range_j' [CompactSpace G]
    (hO : IsOpen (Set.range (algebraMap O (FractionRing O)))) (hT : D.T.FG) (y : H1 D.ρT') :
    ∃ c : O, c ≠ 0 ∧ c • y ∈ LinearMap.range D.j' := by
  induction y using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨c, hc0, hc⟩ := exists_smul_subset_dualLat D hO hT (isCompact_range z.2.1)
    let z' : Z1 D.ρTl' := ⟨fun g => ⟨c • z.1 g, hc _ ⟨g, rfl⟩⟩,
      Continuous.subtype_mk (z.2.1.const_smul c) _, fun g h => by
        apply Subtype.ext
        show c • z.1 (g * h) = c • z.1 g + D.ρT' g (c • z.1 h)
        rw [z.2.2 g h, map_smul, smul_add]⟩
    refine ⟨c, hc0, Submodule.Quotient.mk z', ?_⟩
    rw [← Submodule.Quotient.mk_smul]
    rfl

end

end GlobalTheory.ContCocycleDualLattice

namespace GlobalTheory

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC

theorem jSpan_holds : ReciprocityTheory.ChartRestriction.T2.JSpan := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ _ hF i D hD y
  haveI : IsGalois K (PadicAlgCl p) := by
    have : IsGalois ℚ_[p] (PadicAlgCl p) := inferInstance
    infer_instance
  haveI : CompactSpace (Formalism.GaloisCohomology.GK p K) := inferInstance
  haveI : CompactSpace G := i.symm.surjective.compactSpace i.symm.continuous
  exact ContCocycleDualLattice.exists_smul_mem_range_j' D hF.emb.isOpen_range hD.lat.1 y

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanOfLocalCohomologyShapeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_of_local_cohomology_shape : ReciprocityTheory.ChartRestriction.T2.JSpan := by
  first | exact @GlobalTheory.jSpan_holds | exact GlobalTheory.jSpan_holds | (intros; apply GlobalTheory.jSpan_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateInvariantsTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsOfSubgroup
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial

noncomputable section

namespace GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem descent_act_chiC {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (hact : IsActC act)
    (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (g h : GQ l) : act g (chiC χ i h) = chiC χ i h := by
  unfold chiC
  rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l), ← PadicComplex.coe_eq, hact.1,
    AlgEquiv.commutes]

theorem descent_chiC_mul (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (g h : GQ l) :
    chiC χ i (g * h) = chiC χ i g * chiC χ i h := by
  unfold chiC
  rw [map_mul, mul_zpow, Units.val_mul, map_mul]

theorem descent_chiC_pow (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (n : ℕ) (g : GQ l) :
    chiC χ (i * n) g = chiC χ i g ^ n := by
  unfold chiC
  rw [zpow_mul, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]

theorem descent_chiC_zero (χ : GQ l →* ℚ_[l]ˣ) (g : GQ l) : chiC χ 0 g = 1 := by
  simp [chiC]

theorem descent_chiC_one (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) : chiC χ i 1 = 1 := by
  simp [chiC]

theorem descent_conj {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (hact : IsActC act)
    (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (H : Subgroup (GQ l)) (y : PadicComplex l)
    (hy : ∀ g ∈ H, chiC χ i g * act g y = y) :
    ∃ F : GQ l ⧸ H → PadicComplex l, F ((1 : GQ l) : GQ l ⧸ H) = y ∧
      (∀ q, F q = 0 → y = 0) ∧ ∀ (g : GQ l) q, chiC χ i g * act g (F q) = F (g • q) := by
  have key : ∀ g σ : GQ l, chiC χ i (g * σ) * act (g * σ) y
      = chiC χ i g * act g (chiC χ i σ * act σ y) := by
    intro g σ
    rw [descent_chiC_mul, map_mul act, map_mul (act g), descent_act_chiC hact, mul_assoc]
    rfl
  refine ⟨fun q => Quotient.liftOn' q (fun σ => chiC χ i σ * act σ y) ?_, ?_, ?_, ?_⟩
  · intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have := key a (a⁻¹ * b)
    rw [hy _ hab, mul_inv_cancel_left] at this
    exact this.symm
  · change chiC χ i 1 * act 1 y = y
    rw [descent_chiC_one, map_one, one_mul]
    rfl
  · intro q
    induction q using QuotientGroup.induction_on with
    | H σ =>
      intro h
      change chiC χ i σ * act σ y = 0 at h
      have := key σ⁻¹ σ
      rw [h, map_zero, mul_zero, inv_mul_cancel, descent_chiC_one, map_one, one_mul] at this
      exact this
  · intro g q
    induction q using QuotientGroup.induction_on with
    | H σ => exact (key g σ).symm

theorem invariants_of_subgroup {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
    (hact : IsActC act) (χ : GQ l →* ℚ_[l]ˣ) (G : Subgroup (GQ l))
    (E : IntermediateField ℚ_[l] (Om l))
    (hG : ∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ G, chiC χ i g * act g y = y) →
      (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC E))
    (K : FinExt l) (i : ℤ) (y : PadicComplex l) (hy : ∀ g ∈ GK K, chiC χ i g * act g y = y) :
    (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC K.1) := by
  classical
  haveI := K.2
  haveI : IsGalois ℚ_[l] (Om l) := {}
  haveI : (GK K).FiniteIndex := ⟨by
    rw [GK, ← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'⟩
  haveI : Fintype (GQ l ⧸ GK K) := Fintype.ofFinite _
  obtain ⟨F, hF1, hF0, hF⟩ := descent_conj hact χ i (GK K) y hy
  constructor
  · intro hi
    have hN := (hG (i * (Fintype.card (GQ l ⧸ GK K) : ℕ)) (∏ q, F q) (fun g _ => by
      rw [descent_chiC_pow, map_prod, ← Finset.card_univ, ← Finset.prod_const,
        ← Finset.prod_mul_distrib]
      simp only [hF]
      exact Equiv.prod_comp (MulAction.toPerm g) F)).1
      (mul_ne_zero hi (by exact_mod_cast Fintype.card_ne_zero))
    obtain ⟨q, -, hq⟩ := Finset.prod_eq_zero_iff.1 hN
    exact hF0 q hq
  · rintro rfl
    simp only [descent_chiC_zero, one_mul] at hF hy
    set P : (PadicComplex l)[X] := ∏ q, (X - C (F q)) with hP
    have hmon : P.Monic := monic_prod_of_monic _ _ fun q _ => monic_X_sub_C _
    have hmap : ∀ g : GQ l, P.map (act g : PadicComplex l →+* PadicComplex l) = P := by
      intro g
      rw [hP, Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C, RingHom.coe_coe, hF]
      exact Equiv.prod_comp (MulAction.toPerm g) fun q => (X - C (F q) : (PadicComplex l)[X])
    have hlift : P ∈ lifts (algebraMap (Om l) (PadicComplex l)) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      obtain ⟨x, -, hx⟩ := (hG 0 (P.coeff n) (fun g _ => by
        rw [descent_chiC_zero, one_mul]
        conv_rhs => rw [← hmap g, coeff_map]
        rfl)).2 rfl
      exact ⟨x, hx⟩
    obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_degree_eq_and_monic hlift hmon
    have hint : IsIntegral (Om l) y := by
      refine ⟨Q, hQm, ?_⟩
      rw [← eval_map, hQ, hP, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ ((1 : GQ l) : GQ l ⧸ GK K)) (by simp [hF1])
    obtain ⟨x, rfl⟩ := minpoly.mem_range_of_degree_eq_one (Om l) y
      (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hint))
    refine ⟨x, ?_, rfl⟩
    rw [← InfiniteGalois.fixedField_fixingSubgroup K.1]
    refine (IntermediateField.mem_fixedField_iff _ _).2 fun g hg => ?_
    have := hy g hg
    rw [← PadicComplex.coe_eq, hact.1] at this
    exact (algebraMap (Om l) (PadicComplex l)).injective this

end GlobalTheory.Cyc
end
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem tate_invariants_twist : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ GK K, chiC χ i g * act g y = y) → (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC K.1) :=
  fun l _ act χ hact hχ K =>
    invariants_of_subgroup hact χ (Gj K 2) (Ks K 2)
      (GlobalTheory.CyclotomicTowerSubgroupInclusions.invariants_twist l act χ hact hχ K 2 ⟨by norm_num, fun _ => le_rfl⟩) K

end GlobalTheory.Cyc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonomialLtOfBoundedIntervalEnds
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonomialLtOfBoundedIntervalEnds
noncomputable section

open scoped Formalism.Per
open Filter Topology

namespace GlobalTheory.PMon.Gauss

theorem iSup_monomial_logConvex (c : ℕ → ℝ) (h0 : ∀ n, 0 ≤ c n) (h1 : ∀ n, c n ≤ 1)
    {ρ₁ ρ₂ t : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hρ₁1 : ρ₁ ≤ 1) (hρ₂1 : ρ₂ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (⨆ n, c n * (ρ₁ ^ t * ρ₂ ^ (1 - t)) ^ n) ≤
      (⨆ n, c n * ρ₁ ^ n) ^ t * (⨆ n, c n * ρ₂ ^ n) ^ (1 - t) := by
  have hb : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → BddAbove (Set.range fun n => c n * ρ ^ n) := fun ρ h0' h1' =>
    ⟨1, Set.forall_mem_range.2 fun n => mul_le_one₀ (h1 n) (pow_nonneg h0' n) (pow_le_one₀ h0' h1')⟩
  apply ciSup_le
  intro n
  have hc : c n = c n ^ t * c n ^ (1 - t) := by
    rw [← Real.rpow_add' (h0 n) (by norm_num), add_sub_cancel, Real.rpow_one]
  have e : c n * (ρ₁ ^ t * ρ₂ ^ (1 - t)) ^ n = (c n * ρ₁ ^ n) ^ t * (c n * ρ₂ ^ n) ^ (1 - t) := by
    rw [Real.mul_rpow (h0 n) (pow_nonneg hρ₁ n), Real.mul_rpow (h0 n) (pow_nonneg hρ₂ n), mul_pow,
      Real.rpow_pow_comm hρ₁, Real.rpow_pow_comm hρ₂]
    conv_lhs => rw [hc]
    ring
  rw [e]
  have ht1' : 0 ≤ 1 - t := by linarith
  exact mul_le_mul
    (Real.rpow_le_rpow (mul_nonneg (h0 n) (pow_nonneg hρ₁ n)) (le_ciSup (hb ρ₁ hρ₁ hρ₁1) n) ht0)
    (Real.rpow_le_rpow (mul_nonneg (h0 n) (pow_nonneg hρ₂ n)) (le_ciSup (hb ρ₂ hρ₂ hρ₂1) n) ht1')
    (Real.rpow_nonneg (mul_nonneg (h0 n) (pow_nonneg hρ₂ n)) _)
    (Real.rpow_nonneg ((mul_nonneg (h0 n) (pow_nonneg hρ₁ n)).trans (le_ciSup (hb ρ₁ hρ₁ hρ₁1) n)) _)

theorem gA_logConvex (l : ℕ) [Fact l.Prime] (a : Formalism.Per.Ainf l) {ρ₁ ρ₂ t : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (hρ₁1 : ρ₁ ≤ 1) (hρ₂1 : ρ₂ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gA l (ρ₁ ^ t * ρ₂ ^ (1 - t)) a ≤ gA l ρ₁ a ^ t * gA l ρ₂ a ^ (1 - t) :=
  iSup_monomial_logConvex _ (fun n => by positivity)
    (fun n => Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity))
    hρ₁ hρ₂ hρ₁1 hρ₂1 ht0 ht1

theorem rpow_mul_rpow_one_sub_self {a t : ℝ} (ha : 0 ≤ a) : a ^ t * a ^ (1 - t) = a := by
  rw [← Real.rpow_add' ha (by norm_num), add_sub_cancel, Real.rpow_one]

theorem gC_logConvex : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (ρ₁ ρ₂ t : ℝ), (l : ℝ)⁻¹ ≤ ρ₁ → ρ₁ ≤ ρ₂ →
    ρ₂ < 1 → 0 ≤ t → t ≤ 1 → gC l (ρ₁ ^ t * ρ₂ ^ (1 - t)) x ≤ gC l ρ₁ x ^ t * gC l ρ₂ x ^ (1 - t) := by
  intro l _ x ρ₁ ρ₂ t h1 h12 h2 ht0 ht1
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hρ₁ : 0 < ρ₁ := (inv_pos.2 hl0).trans_le h1
  have hρ₂ : 0 < ρ₂ := hρ₁.trans_le h12
  have ht1' : 0 ≤ 1 - t := by linarith
  set ρ := ρ₁ ^ t * ρ₂ ^ (1 - t) with hρdef
  have hρlo : ρ₁ ≤ ρ := by
    calc ρ₁ = ρ₁ ^ t * ρ₁ ^ (1 - t) := (rpow_mul_rpow_one_sub_self hρ₁.le).symm
      _ ≤ ρ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hρ₁.le h12 ht1') (Real.rpow_nonneg hρ₁.le _)
  have hρhi : ρ ≤ ρ₂ := by
    calc ρ ≤ ρ₂ ^ t * ρ₂ ^ (1 - t) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hρ₁.le h12 ht0) (Real.rpow_nonneg hρ₂.le _)
      _ = ρ₂ := rpow_mul_rpow_one_sub_self hρ₂.le
  have hρ0 : 0 < ρ := hρ₁.trans_le hρlo
  have G : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → IsGauss l σ (gC l σ) := fun σ a b => isGauss_gC_of_le l σ a b
  have Gl : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → gC l σ (l : Formalism.Per.Acris l) = σ := by
    intro σ a b
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, (G σ a b).2.2.2.2]
    exact GlobalTheory.GaussSlope.gauss_l l ((inv_pos.2 hl0).le.trans a)
  have g : IsGauss l ρ (gC l ρ) := G ρ (h1.trans hρlo) (hρhi.trans_lt h2)
  have g₁ : IsGauss l ρ₁ (gC l ρ₁) := G ρ₁ h1 (h12.trans_lt h2)
  have g₂ : IsGauss l ρ₂ (gC l ρ₂) := G ρ₂ (h1.trans h12) h2

  have P : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → ∀ (k : ℕ) (y : Formalism.Per.Acris l),
      gC l σ ((l : Formalism.Per.Acris l) ^ k * y) = σ ^ k * gC l σ y := by
    intro σ a b k y
    rw [GlobalTheory.GaussSlope.map_pow_mul _ (G σ a b).2.2.2.1, Gl σ a b]

  have hs : ∀ s : Formalism.Per.Acris0 l, gC l ρ (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) ≤
      gC l ρ₁ (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) ^ t *
        gC l ρ₂ (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) ^ (1 - t) := by
    intro s
    obtain ⟨k, a, ha⟩ := GlobalTheory.GaussSlope.exists_pow_mul_eq l s
    set y := algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s
    have e : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → σ ^ k * gC l σ y = gA l σ a := by
      intro σ a' b
      rw [← P σ a' b, ha, (G σ a' b).2.2.2.2]
    have key := gA_logConvex l a hρ₁.le hρ₂.le (h12.trans h2.le) h2.le ht0 ht1
    rw [← e ρ (h1.trans hρlo) (hρhi.trans_lt h2), ← e ρ₁ h1 (h12.trans_lt h2), ← e ρ₂ (h1.trans h12) h2,
      Real.mul_rpow (pow_nonneg hρ₁.le _) (g₁.1 y).1, Real.mul_rpow (pow_nonneg hρ₂.le _) (g₂.1 y).1,
      ← Real.rpow_pow_comm hρ₁.le, ← Real.rpow_pow_comm hρ₂.le] at key
    have e2 : (ρ₁ ^ t) ^ k * gC l ρ₁ y ^ t * ((ρ₂ ^ (1 - t)) ^ k * gC l ρ₂ y ^ (1 - t)) =
        ρ ^ k * (gC l ρ₁ y ^ t * gC l ρ₂ y ^ (1 - t)) := by
      rw [hρdef, mul_pow]; ring
    rw [e2] at key
    exact le_of_mul_le_mul_left key (pow_pos hρ0 k)

  have F : ∀ r : ℕ, gC l ρ x ≤ max (max (gC l ρ₁ x) (ρ₁ ^ r) ^ t * max (gC l ρ₂ x) (ρ₂ ^ r) ^ (1 - t)) (ρ ^ r) := by
    intro r
    obtain ⟨s, z, hx⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x r
    set y := algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s
    have hz : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → gC l σ ((l : Formalism.Per.Acris l) ^ r * z) ≤ σ ^ r := by
      intro σ a b
      rw [P σ a b]
      exact mul_le_of_le_one_right (pow_nonneg ((inv_pos.2 hl0).le.trans a) _) ((G σ a b).1 z).2
    have hy : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → gC l σ y ≤ max (gC l σ x) (σ ^ r) := by
      intro σ a b
      have : y = x + -((l : Formalism.Per.Acris l) ^ r * z) := by rw [hx]; ring
      rw [this]
      refine ((G σ a b).2.1 _ _).trans (max_le_max le_rfl ?_)
      rw [(G σ a b).2.2.1]
      exact hz σ a b
    conv_lhs => rw [hx]
    refine (g.2.1 _ _).trans (max_le_max ?_ (hz ρ (h1.trans hρlo) (hρhi.trans_lt h2)))
    refine (hs s).trans (mul_le_mul (Real.rpow_le_rpow (g₁.1 y).1 (hy ρ₁ h1 (h12.trans_lt h2)) ht0)
      (Real.rpow_le_rpow (g₂.1 y).1 (hy ρ₂ (h1.trans h12) h2) ht1') (Real.rpow_nonneg (g₂.1 y).1 _)
      (Real.rpow_nonneg ((g₁.1 x).1.trans (le_max_left _ _)) _))
  have T : Tendsto (fun r : ℕ => max (max (gC l ρ₁ x) (ρ₁ ^ r) ^ t * max (gC l ρ₂ x) (ρ₂ ^ r) ^ (1 - t)) (ρ ^ r))
      atTop (𝓝 (max (max (gC l ρ₁ x) 0 ^ t * max (gC l ρ₂ x) 0 ^ (1 - t)) 0)) := by
    have t1 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ₁.le (h12.trans_lt h2)
    have t2 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ₂.le h2
    have t0 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le (hρhi.trans_lt h2)
    exact ((((tendsto_const_nhds.max t1).rpow_const (Or.inr ht0)).mul
      ((tendsto_const_nhds.max t2).rpow_const (Or.inr ht1'))).max t0)
  have := ge_of_tendsto' T F
  rwa [max_eq_left (g₁.1 x).1, max_eq_left (g₂.1 x).1,
    max_eq_left (mul_nonneg (Real.rpow_nonneg (g₁.1 x).1 _) (Real.rpow_nonneg (g₂.1 x).1 _))] at this

end GlobalTheory.PMon.Gauss

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonomialLtOfBoundedIntervalEndsStatement
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussNormAcris_logConvex_in_radius : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (ρ₁ ρ₂ t : ℝ), (l : ℝ)⁻¹ ≤ ρ₁ → ρ₁ ≤ ρ₂ → ρ₂ < 1 → 0 ≤ t → t ≤ 1 → gC l (ρ₁ ^ t * ρ₂ ^ (1 - t)) x ≤ gC l ρ₁ x ^ t * gC l ρ₂ x ^ (1 - t) := by
  first | exact @GlobalTheory.PMon.Gauss.gC_logConvex | exact GlobalTheory.PMon.Gauss.gC_logConvex | (intros; apply GlobalTheory.PMon.Gauss.gC_logConvex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEqOfApply
noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.SenLines GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen

namespace GlobalTheory.SenLines.Coords

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

def zc (c : F⟦X⟧) (n : ℤ) : F := if 0 ≤ n then coeff n.toNat c else 0

theorem zc_nat (c : F⟦X⟧) (n : ℕ) : zc c n = coeff n c := by
  simp [zc]

theorem zc_neg (c : F⟦X⟧) {n : ℤ} (h : n < 0) : zc c n = 0 := by
  unfold zc
  rw [if_neg (not_le.mpr h)]

theorem zc_add (c c' : F⟦X⟧) (n : ℤ) : zc (c + c') n = zc c n + zc c' n := by
  unfold zc
  split_ifs <;> simp [map_add (f := _)]

theorem zc_mul (f c : F⟦X⟧) (n : ℤ) (N : ℕ) (h : n < N) :
    zc (f * c) n = ∑ j ∈ Finset.range N, coeff j f * zc c (n - j) := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [zc_neg _ hn]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [zc_neg _ (by omega), mul_zero]
  · lift n to ℕ using hn
    have hN : n < N := by exact_mod_cast h
    rw [zc_nat, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j c),
      ← Finset.sum_range_add_sum_Ico _ (show n + 1 ≤ N by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico (n + 1) N) ?_, add_zero]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [show ((n : ℤ) - (j : ℤ)) = ((n - j : ℕ) : ℤ) by omega, zc_nat]
    · intro j hj
      rw [Finset.mem_Ico] at hj
      rw [zc_neg _ (by omega), mul_zero]

def lines {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (c : Fin r → F⟦X⟧) : ℤ → M :=
  ∑ k, serLine (u k) (d k) (c k)

theorem lines_apply {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (c : Fin r → F⟦X⟧) (m : ℤ) :
    lines u d c m = ∑ k, zc (c k) (m + u k) • d k := by
  unfold lines
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [serLine, zc]
  split_ifs <;> simp

theorem lines_add {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (c c' : Fin r → F⟦X⟧) :
    lines u d (c + c') = lines u d c + lines u d c' := by
  funext m
  simp only [lines_apply, Pi.add_apply, zc_add, add_smul, Finset.sum_add_distrib]

theorem lines_zero {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) :
    lines u d (0 : Fin r → F⟦X⟧) = 0 := by
  funext m
  rw [lines_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have : zc (0 : F⟦X⟧) (m + u k) = 0 := by
    unfold zc
    split_ifs <;> simp
  rw [Pi.zero_apply, this, zero_smul]

theorem lines_sum {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) {ι : Type} (s : Finset ι)
    (c : ι → Fin r → F⟦X⟧) : lines u d (∑ j ∈ s, c j) = ∑ j ∈ s, lines u d (c j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, lines_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, lines_add, ih]

theorem coeff_eq_of_apply {r : ℕ} (u : Fin r → ℤ) {d : Fin r → M} (hd : LinearIndependent F d)
    (c c' : Fin r → F⟦X⟧) (a : F) (m : ℤ) (h : lines u d c m = a • lines u d c' m) (k : Fin r) :
    zc (c k) (m + u k) = a * zc (c' k) (m + u k) := by
  rw [lines_apply, lines_apply, Finset.smul_sum] at h
  have h2 : ∑ k, (zc (c k) (m + u k) - a * zc (c' k) (m + u k)) • d k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
    rw [h, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hd _ h2 k)

theorem lines_injective {r : ℕ} (u : Fin r → ℤ) {d : Fin r → M} (hd : LinearIndependent F d) :
    Function.Injective (lines (F := F) u d) := by
  intro c c' h
  funext k
  ext n
  have := coeff_eq_of_apply u hd c c' 1 ((n : ℤ) - u k) (by rw [h, one_smul]) k
  rwa [sub_add_cancel, one_mul, zc_nat, zc_nat] at this

theorem serAct_lines {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (f : F⟦X⟧) (c : Fin r → F⟦X⟧) :
    serAct f (lines u d c) = lines u d (f • c) := by
  funext m
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k, m + u k < N := by
    refine ⟨(Finset.univ.sup fun k => (m + u k).toNat) + 1, fun k => ?_⟩
    have h1 : (m + u k).toNat ≤ Finset.univ.sup fun k => (m + u k).toNat :=
      Finset.le_sup (f := fun k => (m + u k).toNat) (Finset.mem_univ k)
    have h2 := Int.self_le_toNat (m + u k)
    push_cast
    omega
  have hsupp : (Function.support fun j : ℕ => coeff j f • lines u d c (m - j)) ⊆ ↑(Finset.range N) := by
    intro j hj
    rw [Function.mem_support] at hj
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hjN
    apply hj
    rw [lines_apply, Finset.sum_eq_zero, smul_zero]
    intro k _
    rw [zc_neg _ (by have := hN k; omega), zero_smul]
  unfold serAct
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  simp_rw [lines_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [zc_mul f (c k) (m + u k) N (hN k), Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show m - (j : ℤ) + u k = m + u k - j by ring]

theorem exists_coords : ∀ {F M A N : Type} [Field F] [AddCommGroup M] [Module F M] [CommRing A] [AddCommGroup N] [Module A N] (lev : A → F⟦X⟧) (L : N →+ (ℤ → M)) {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M), LinearIndependent F d → (∀ a x, L (a • x) = serAct (lev a) (L x)) → SpanIsLines L u d F → ∃ e : N →+ (Fin r → F⟦X⟧), (∀ a x, e (a • x) = lev a • e x) ∧ Submodule.span F⟦X⟧ (Set.range e) = ⊤ ∧ ∀ (χ : F) (x y : N), χ ≠ 0 → (∀ k : ℤ, L y k = χ ^ k • L x k) → ∀ k, e y k = C (χ ^ (-u k)) * rescale χ (e x k) := by
  intro F M A N _ _ _ _ _ _ lev L r u d hd hL hS
  have hex : ∀ x, ∃ c : Fin r → F⟦X⟧, L x = lines u d c := by
    intro x
    obtain ⟨c, hc⟩ := (hS (L x)).mp ⟨1, fun _ => x, fun _ => 1, by simp only [Fin.sum_univ_one, serAct_one]⟩
    exact ⟨c, hc⟩
  choose e he using hex
  have hinj := lines_injective (F := F) u hd
  have eadd : ∀ x y, e (x + y) = e x + e y := fun x y =>
    hinj (by rw [← he, lines_add, ← he, ← he, map_add (f := _)])
  refine ⟨AddMonoidHom.mk' e eadd, ?_, ?_, ?_⟩
  · intro a x
    show e (a • x) = lev a • e x
    apply hinj
    rw [← he, hL, he x, serAct_lines]
  · rw [eq_top_iff]
    intro c _
    obtain ⟨s, x, f, hy⟩ := (hS (lines u d c)).mpr ⟨c, rfl⟩
    have hc : c = ∑ j, f j • e (x j) := by
      apply hinj
      rw [hy, lines_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [he, serAct_lines]
    rw [hc]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x j, rfl⟩)
  · intro χ x y hχ hxy k
    show e y k = C (χ ^ (-u k)) * rescale χ (e x k)
    ext n
    have h1 : lines u d (e y) ((n : ℤ) - u k) = χ ^ ((n : ℤ) - u k) • lines u d (e x) ((n : ℤ) - u k) := by
      rw [← he, ← he]
      exact hxy _
    have h2 := coeff_eq_of_apply u hd (e y) (e x) _ _ h1 k
    rw [sub_add_cancel, zc_nat, zc_nat] at h2
    rw [h2, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, zpow_sub₀ hχ, zpow_neg, zpow_natCast]
    ring

end GlobalTheory.SenLines.Coords
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Main
namespace GlobalTheory.ScalarStatement

open Formalism.L2.FormalSeriesBounds

theorem main : (let d1 : {C : Type} → [inst : Field C] → Formalism.L2.FormalSeriesBounds.VF C → (ℕ → C) → Prop := @(fun {C : Type} [Field C] (V : Formalism.L2.FormalSeriesBounds.VF C) (s : ℕ → C) ↦ ∃ (K : ℝ), ∀ (n : ℕ), Formalism.L2.FormalSeriesBounds.VF.Ge V K (s n)); ∀ {C : Type} [inst : Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {ι : Type} (S : Finset ι) {s : ι → ℕ → C}, (∀ i ∈ S, d1 V (s i)) → d1 V fun (n : ℕ) ↦ ∑ i ∈ S, s i n) := by
  intro d1 C _ V ι S s h
  classical
  have h' : ∀ i, ∃ K : ℝ, i ∈ S → ∀ n, Formalism.L2.FormalSeriesBounds.VF.Ge V K (s i n) := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨K, hK⟩ := h i hi
      exact ⟨K, fun _ => hK⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose K hK using h'
  refine ⟨-(∑ i ∈ S, |K i|), fun n => ?_⟩
  refine Formalism.L2.FormalSeriesBounds.VF.Ge.sum fun i hi => (hK i hi n).mono ?_
  have h1 : |K i| ≤ ∑ j ∈ S, |K j| :=
    Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _) hi
  have h2 : -|K i| ≤ K i := neg_abs_le _
  linarith

end GlobalTheory.ScalarStatement
end
