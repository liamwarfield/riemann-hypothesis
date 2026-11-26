module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardTypeVectorOfParabolicTypeVector
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardTypeVectorOfParabolicTypeVector
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LevelType
open Matrix

theorem exists_stdVec_of_parVec : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ Fin r) (a : α) (θ : (ZMod p)ˣ →* ℂˣ) (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL (Fin r) (ZMod p)) U) (v : U), Fintype.card (m a) = 1 → v ≠ 0 → ParVec ρ e a θ v → ∃ (c : ℕ) (v' : U), c < r ∧ v' ≠ 0 ∧ StdVec ρ c θ v' := by
  intro p _ r α _ _ m _ _ e a θ U _ _ ρ v hm hv hpar
  obtain ⟨k0⟩ : Nonempty (m a) := Fintype.card_pos_iff.1 (by omega)
  let σ := Tuple.sort (blk e)
  let i₀ := e ⟨a, k0⟩
  have hi₀ : blk e i₀ = a := blk_apply e a k0
  have hmono := Tuple.monotone_sort (blk e)
  have hlt : ∀ i, blk e i < a → σ.symm i < σ.symm i₀ := fun i h => hmono.reflect_lt (by
    show blk e (σ (σ.symm i)) < blk e (σ (σ.symm i₀))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hi₀]; exact h)
  have hgt : ∀ i, a < blk e i → σ.symm i₀ < σ.symm i := fun i h => hmono.reflect_lt (by
    show blk e (σ (σ.symm i₀)) < blk e (σ (σ.symm i))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hi₀]; exact h)
  have hlo : ∀ i, (σ.symm i).val ≤ (σ.symm i₀).val → blk e i ≤ a := fun i h => by
    by_contra h'
    exact absurd h (not_le.2 (Fin.lt_def.1 (hgt i (not_le.1 h'))))
  have hhi : ∀ j, (σ.symm i₀).val ≤ (σ.symm j).val → a ≤ blk e j := fun j h => by
    by_contra h'
    exact absurd h (not_le.2 (Fin.lt_def.1 (hlt j (not_le.1 h'))))
  refine ⟨(σ.symm i₀).val, ρ (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm) v, (σ.symm i₀).isLt, ?_, ?_⟩
  · intro h0
    apply hv
    have := congrArg (ρ (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm)⁻¹) h0
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at this
  · intro x hx
    set y := (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm)⁻¹ * x * GlobalTheory.Parabolic.permGL (ZMod p) σ.symm with hy
    have hyij : ∀ i j, ¬ (blk e i ≤ a ∧ a ≤ blk e j) → y.val i j = if i = j then 1 else 0 := by
      intro i j hij
      have hyv : y.val i j = x.val (σ.symm i) (σ.symm j) := by
        rw [← GlobalTheory.Parabolic.conj_permGL_apply σ.symm y i j, hy]
        congr 2
        group
      rw [hyv, hx _ _ (fun h => hij ⟨hlo i h.1, hhi j h.2⟩)]
      simp
    have hyP : y ∈ parab (ZMod p) e := mem_parab.2 fun i j hji => by
      rw [hyij i j (fun h => absurd (h.1.trans h.2) (not_le.2 hji)), if_neg]
      rintro rfl
      exact lt_irrefl _ hji
    have hlev : ∀ b, b ≠ a → leviProj (ZMod p) e ⟨y, hyP⟩ b = 1 := by
      intro b hb
      refine Units.ext (Matrix.ext fun k l => ?_)
      rw [leviProj_apply, Units.val_one]
      rw [hyij _ _ (fun h => hb (le_antisymm (by simpa using h.1) (by simpa using h.2)))]
      simp [Matrix.one_apply]
    have h1 := hpar ⟨y, hyP⟩ hlev
    change ρ y v = (θ (GeneralLinearGroup.det y) : ℂ) • v at h1
    have hdet : GeneralLinearGroup.det y = GeneralLinearGroup.det x := by
      rw [hy, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
    have hxP : x * GlobalTheory.Parabolic.permGL (ZMod p) σ.symm = GlobalTheory.Parabolic.permGL (ZMod p) σ.symm * y := by rw [hy]; group
    rw [← Module.End.mul_apply, ← map_mul, hxP, map_mul, Module.End.mul_apply, h1, hdet, map_smul]

end GlobalTheory.LevelType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardTypeVectorOfParabolicTypeVectorStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardTypeVector_of_parabolicTypeVector : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ Fin r) (a : α) (θ : (ZMod p)ˣ →* ℂˣ) (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL (Fin r) (ZMod p)) U) (v : U), Fintype.card (m a) = 1 → v ≠ 0 → ParVec ρ e a θ v → ∃ (c : ℕ) (v' : U), c < r ∧ v' ≠ 0 ∧ StdVec ρ c θ v' := by
  first | exact @GlobalTheory.LevelType.exists_stdVec_of_parVec | exact GlobalTheory.LevelType.exists_stdVec_of_parVec | (intros; apply GlobalTheory.LevelType.exists_stdVec_of_parVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetSubquotientDetCharacterFactorsIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetSubquotientDetCharacterFactorsIntegral
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

open GlobalTheory.SmGL.DepthZero ValuativeRel Matrix

theorem factor_eq_det_of_isSubquotient_jac : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n β : Type) [Fintype n] [DecidableEq n] [Fintype β] [LinearOrder β] (c : β → ℕ) (f : (Σ j, Fin (c j)) ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL n F) V) (ψ : Fˣ →* ℂˣ) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), Nonempty (σ.Equiv (detRep n ψ)) → IsSubquotient (piTensor fun j => (s j).ρ) (GlobalTheory.SmGL.jac f σ) → ∀ j, ∀ g ∈ KO F (Fin (c j)), ∀ v, (s j).ρ g v = (ψ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
  intro F _ _ _ _ n β _ _ _ _ c f V _ _ σ ψ s ⟨E⟩ hsub j g hg v
  classical

  have hσ : ∀ (h : GL n F) (x : V), σ h x = (ψ (GeneralLinearGroup.det h) : ℂ) • x := by
    intro h x
    apply E.toLinearEquiv.injective
    have h1 := E.toIntertwiningMap.isIntertwining σ (detRep n ψ) h x
    have h2 : E.toLinearEquiv (σ h x) = E.toIntertwiningMap (σ h x) := rfl
    have h3 : E.toLinearEquiv x = E.toIntertwiningMap x := rfl
    rw [h2, h1, map_smul, h3]
    simp [detRep]

  have hval : ∀ {d : Type} [Fintype d] [DecidableEq d] {h : GL d F}, h ∈ KO F d →
      valuation F (GeneralLinearGroup.det h : F) = 1 := by
    intro d _ _ h hh
    obtain ⟨h, rfl⟩ := hh
    have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[F] F) h) : Fˣ) : F) =
        algebraMap 𝒪[F] F (GeneralLinearGroup.det h : 𝒪[F]ˣ) :=
      ((algebraMap 𝒪[F] F).map_det _).symm
    rw [h1]
    exact (Valuation.integer.integers (valuation F)).one_of_isUnit (Units.isUnit _)
  set l : Levi F (fun j => Fin (c j)) := Pi.mulSingle j g with hl
  have hlK : ∀ b, l b ∈ KO F (Fin (c b)) := by
    intro b
    by_cases hb : b = j
    · subst hb; simp [l, hg]
    · simp [l, Pi.mulSingle_eq_of_ne hb, one_mem]
  have hdet : GeneralLinearGroup.det (leviEmb F f l) = GeneralLinearGroup.det g := by
    rw [det_leviEmb, Finset.prod_eq_single j]
    · simp [l]
    · intro b _ hb; simp [l, Pi.mulSingle_eq_of_ne hb]
    · simp
  have hδ : deltaHalf F (fun j => Fin (c j)) l = 1 := by
    rw [deltaHalf_apply]
    exact Finset.prod_eq_one fun b _ => isUnram_absPow F _ _ (hval (hlK b))

  have hjac : ∀ x, GlobalTheory.SmGL.jac f σ l x = (ψ (GeneralLinearGroup.det g) : ℂ) • x := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [jac_mk, hδ, inv_one, Units.val_one, one_smul, hσ, hdet, Submodule.Quotient.mk_smul]

  have hT := Model.scalar_of_isSubquotient hsub hjac

  have hnt : ∀ b, Nontrivial (s b).V := fun b => Model.nontrivial_of_isIrreducible (s b).irr
  have hφ : ∀ b, ∃ x : (s b).V, ∃ φ : (s b).V →ₗ[ℂ] ℂ, φ x ≠ 0 := by
    intro b
    obtain ⟨x, hx⟩ := exists_ne (0 : (s b).V)
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (s b).V, φ x ≠ 0 := by
      by_contra! h
      exact hx ((Module.forall_dual_apply_eq_zero_iff ℂ x).1 h)
    exact ⟨x, φ, hφ⟩
  choose x φ hxφ using hφ
  let y : ∀ b, (s b).V := Function.update x j v
  have hc : (∏ b ∈ Finset.univ.erase j, φ b (y b)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun b hb => ?_
    rw [show y b = x b from Function.update_of_ne (Finset.ne_of_mem_erase hb) _ _]
    exact hxφ b
  have hyj : y j = v := Function.update_self _ _ _
  have key := contract_piTensor (fun b => (s b).ρ) φ j g (PiTensorProduct.tprod ℂ y)
  rw [hT, map_smul, contract_tprod, hyj, map_smul] at key
  rw [smul_comm] at key
  exact (smul_right_injective _ hc key).symm

end GlobalTheory.LevelType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetSubquotientDetCharacterFactorsIntegralStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetSubquotient_detCharacter_factors_integral : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n β : Type) [Fintype n] [DecidableEq n] [Fintype β] [LinearOrder β] (c : β → ℕ) (f : (Σ j, Fin (c j)) ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL n F) V) (ψ : Fˣ →* ℂˣ) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), Nonempty (σ.Equiv (detRep n ψ)) → IsSubquotient (piTensor fun j => (s j).ρ) (jac f σ) → ∀ j, ∀ g ∈ KO F (Fin (c j)), ∀ v, (s j).ρ g v = (ψ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
  first | exact @GlobalTheory.LevelType.factor_eq_det_of_isSubquotient_jac | exact GlobalTheory.LevelType.factor_eq_det_of_isSubquotient_jac | (intros; apply GlobalTheory.LevelType.factor_eq_det_of_isSubquotient_jac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdParabolicTwistedTraceSumNeZeroOfVector
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdParabolicTwistedTraceSumNeZeroOfVector
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LevelType

theorem StdBlock.mul {p r : ℕ} {a : ℕ} {x y : GL (Fin r) (ZMod p)} (hx : StdBlock a x) (hy : StdBlock a y) :
    StdBlock a (x * y) := by
  intro i j hij
  rw [Units.val_mul, Matrix.mul_apply]
  by_cases hi : i.val ≤ a
  · have hj : ¬ a ≤ j.val := fun h => hij ⟨hi, h⟩
    have : ∀ k, y.val k j = if k = j then 1 else 0 := fun k => hy k j (fun h => hj h.2)
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hx i j hij
  · have : ∀ k, x.val i k = if i = k then 1 else 0 := fun k => hx i k (fun h => hi h.1)
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hy i j hij

theorem stdBlock_one {p r : ℕ} (a : ℕ) : StdBlock a (1 : GL (Fin r) (ZMod p)) := by
  intro i j _
  simp [Matrix.one_apply]

theorem stdTrace_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (r a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (v : ρ), v ≠ 0 → StdVec ρ.ρ a θ v → stdTrace a θ ρ.character ≠ 0 := by
  intro p _ r a θ ρ v hv0 hv
  classical
  set S : Finset (GL (Fin r) (ZMod p)) := Finset.univ.filter (StdBlock a) with hS
  set c : GL (Fin r) (ZMod p) → ℂ := fun x => (((θ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) with hc
  have hcm : ∀ x y, c (x * y) = c x * c y := fun x y => by
    simp [hc, map_mul, mul_inv, Units.val_mul, mul_comm]
  set E : Module.End ℂ ρ := ∑ x ∈ S, c x • ρ.ρ x with hE
  have htr : stdTrace a θ ρ.character = LinearMap.trace ℂ ρ E := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hE, map_sum, stdTrace, hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp [FDRep.character, hc]
  have himg : ∀ x ∈ S, S.image (x * ·) = S := fun x hx => by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
      exact hx.mul hy
    · rw [Finset.card_image_of_injective _ (mul_right_injective x)]
  have hEE : E * E = (S.card : ℂ) • E := by
    have : ∀ x ∈ S, (c x • ρ.ρ x) * E = E := fun x hx => by
      rw [hE, Finset.mul_sum]
      conv_rhs => rw [← himg x hx]
      rw [Finset.sum_image (fun y _ z _ h => mul_left_cancel h)]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [smul_mul_smul_comm, ← map_mul, hcm x y]
    calc E * E = ∑ x ∈ S, (c x • ρ.ρ x) * E := by rw [hE, Finset.sum_mul]
      _ = ∑ x ∈ S, E := Finset.sum_congr rfl this
      _ = (S.card : ℂ) • E := by rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hEv : E v = (S.card : ℂ) • v := by
    rw [hE, LinearMap.sum_apply, Finset.sum_congr rfl (g := fun _ => v), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    intro x hx
    rw [LinearMap.smul_apply, hv x (by simpa [hS] using hx), smul_smul]
    simp [hc]
  have hcard : (S.card : ℂ) ≠ 0 := by
    have : (1 : GL (Fin r) (ZMod p)) ∈ S := by simpa [hS] using stdBlock_one (p := p) (r := r) a
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem this)
  set P : Module.End ℂ ρ := (S.card : ℂ)⁻¹ • E with hP
  have hPP : IsIdempotentElem P := by
    rw [IsIdempotentElem, hP, smul_mul_smul_comm, hEE, smul_smul]
    congr 1
    field_simp
  have hPv : P v = v := by
    rw [hP, LinearMap.smul_apply, hEv, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hP0 : P ≠ 0 := fun h => hv0 (by rw [← hPv, h, LinearMap.zero_apply])
  have htP : LinearMap.trace ℂ ρ P ≠ 0 := fun h => hP0 ((LinearMap.IsIdempotentElem.trace_eq_zero_iff hPP).1 h)
  rw [htr]
  have : E = (S.card : ℂ) • P := by rw [hP, smul_smul, mul_inv_cancel₀ hcard, one_smul]
  rw [this, map_smul, smul_eq_mul]
  exact mul_ne_zero hcard htP

end GlobalTheory.LevelType

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdParabolicTwistedTraceSumNeZeroOfVectorStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdParabolicTwistedTraceSum_ne_zero_of_vector : ∀ (p : ℕ) [Fact p.Prime] (r a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (v : ρ), v ≠ 0 → StdVec ρ.ρ a θ v → stdTrace a θ ρ.character ≠ 0 := by
  first | exact @GlobalTheory.LevelType.stdTrace_ne_zero | exact GlobalTheory.LevelType.stdTrace_ne_zero | (intros; apply GlobalTheory.LevelType.stdTrace_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLabelRootOfHarishChandraConstituent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLabelRootOfHarishChandraConstituent
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GLq.DetSplit

open GlobalTheory.GLq Polynomial
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem ip_hc_mono_left (m k n : ℕ) (hn : n = m + k) (ψ : Gn g n → ℂ) (hψ : IsIrr ψ)
    (α A : Gn g m → ℂ) (hα : IsIrr α) (hA : IsChar A) (hαA : ip α A ≠ 0)
    (β : Gn g k → ℂ) (hβ : IsChar β) (h : ip ψ (hc m k α β n) ≠ 0) : ip ψ (hc m k A β n) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hα hA hαA
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_left]
  have hc := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g m k n hn).1
  exact GlobalTheory.GLq.DetRoot.ip_add_ne_zero hψ (hc α β (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hα) hβ) (hc R β hR hβ) h

theorem ip_hc_mono_right (m k n : ℕ) (hn : n = m + k) (ψ : Gn g n → ℂ) (hψ : IsIrr ψ)
    (α : Gn g m → ℂ) (hα : IsChar α) (β B : Gn g k → ℂ) (hβ : IsIrr β) (hB : IsChar B) (hβB : ip β B ≠ 0)
    (h : ip ψ (hc m k α β n) ≠ 0) : ip ψ (hc m k α B n) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hβ hB hβB
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_right]
  have hc := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g m k n hn).1
  exact GlobalTheory.GLq.DetRoot.ip_add_ne_zero hψ (hc α β hα (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hβ)) (hc α R hα hR) h

theorem hcL_append_of (K₁ K₂ : List (Pc g)) (h₁ : ∀ q ∈ K₁, IsCusp q.2) (h₂ : ∀ q ∈ K₂, IsCusp q.2)
    (m₁ m₂ n : ℕ) (e₁ : degL K₁ = m₁) (e₂ : degL K₂ = m₂) (hn : n = m₁ + m₂) :
    hcL (K₁ ++ K₂) n = hc m₁ m₂ (hcL K₁ m₁) (hcL K₂ m₂) n := by
  subst e₁ e₂
  exact GlobalTheory.GLq.LabelMul.hcL_append K₁ K₂ (fun q hq => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (h₁ q hq))
    (fun q hq => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (h₂ q hq)) n hn

theorem root_of_constituent : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r a c : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (u : ZMod p) (f : Polynomial (ZMod p)) (ψ : GlobalTheory.GLq.Gn p r → ℂ) (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ) (β : GlobalTheory.GLq.Gn p c → ℂ) (σ : GlobalTheory.GLq.Gn p a → ℂ), r = a + 1 + c → GlobalTheory.GLq.IsIrr ψ → GlobalTheory.GLq.IsIrr α → GlobalTheory.GLq.IsIrr β → GlobalTheory.GLq.IsIrr σ → GlobalTheory.GLq.HasLabel L ψ f → GlobalTheory.GLp.IsCharLab L θ u → GlobalTheory.GLq.ip ψ (GlobalTheory.GLq.hc (a + 1) c α β r) ≠ 0 → GlobalTheory.GLq.ip α (GlobalTheory.GLq.hc a 1 σ (fun y : GlobalTheory.GLq.Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (a + 1)) ≠ 0 → f.IsRoot u := by
  intro p _ L r a c θ u f ψ α β σ hr hψ hα hβ hσ hL hlab hψαβ hασ
  obtain ⟨Q, hQ, hQd, rfl, hQi⟩ := hL
  obtain ⟨Kσ, hKσ, hKσd, hKσi⟩ := GlobalTheory.GLq.SuppCusp.exists_cusp_list p a σ hσ
  obtain ⟨Kβ, hKβ, hKβd, hKβi⟩ := GlobalTheory.GLq.SuppCusp.exists_cusp_list p c β hβ
  have hθI : IsIrr (fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    GlobalTheory.GLq.LabelDet.isIrr_hom (θ.comp Matrix.GeneralLinearGroup.det)
  have hθC := GlobalTheory.GLq.LabelMul.isChar_of_isIrr hθI
  have hθcusp : IsCusp (fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    ⟨one_pos, hθI, fun a h1 h2 => by omega⟩
  have hQc : ∀ q ∈ Q.map Prod.snd, IsCusp q.2 := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    exact (hQ q' hq').2.1
  have hA := GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hQc _ hQd
  have fin : ∀ K' : List (Pc p), (Q.map Prod.snd).Perm K' →
      (⟨1, fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc p) ∈ K' →
      ((Q.map Prod.fst).prod).IsRoot u := by
    intro K' hp hm
    obtain ⟨⟨P, s⟩, hq, hs⟩ := List.mem_map.1 (hp.mem_iff.2 hm)
    dsimp only at hs
    subst hs
    have hP := GlobalTheory.GLq.DetRoot.eq_of_isCuspOf_det L θ u hlab P (hQ _ hq)
    have hdvd : P ∣ (Q.map Prod.fst).prod := List.dvd_prod (List.mem_map.2 ⟨_, hq, rfl⟩)
    exact Polynomial.IsRoot.dvd (by rw [hP]; exact root_X_sub_C.2 rfl) hdvd
  generalize (fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) = θd at hθI hθC hθcusp hασ fin
  have h1 := GlobalTheory.GLq.DetRoot.ip_hc_left a α hα σ hσ θd hθC Kσ hKσ hKσd hKσi hασ
  have hT : ∀ q ∈ [(⟨1, θd⟩ : Pc p)], IsCusp q.2 := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hθcusp
  have hTd : degL [(⟨1, θd⟩ : Pc p)] = 1 := by simp [degL]
  have eα : hcL (Kσ ++ [(⟨1, θd⟩ : Pc p)]) (a + 1) = hc a 1 (hcL Kσ a) θd (a + 1) := by
    rw [hcL_append_of Kσ _ hKσ hT a 1 (a + 1) hKσd hTd rfl,
      GlobalTheory.GLq.IpCuspProd.hcL_single 1 θd (GlobalTheory.GLq.IpCuspProd.isClass_of_isChar hθC)]
  rw [← eα] at h1
  have hKα : ∀ q ∈ Kσ ++ [(⟨1, θd⟩ : Pc p)], IsCusp q.2 := by
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hKσ q hq
    · exact hT q hq
  have hKαd : degL (Kσ ++ [(⟨1, θd⟩ : Pc p)]) = a + 1 := by
    rw [GlobalTheory.GLq.LabelMul.degL_append, hKσd, hTd]
  have hAα := GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKα _ hKαd
  have h2 := ip_hc_mono_left (a + 1) c r hr ψ hψ α _ hα hAα h1 β (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hβ) hψαβ
  have h3 := ip_hc_mono_right (a + 1) c r hr ψ hψ _ hAα β (hcL Kβ c) hβ
    (GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKβ _ hKβd) hKβi h2
  rw [← hcL_append_of _ Kβ hKα hKβ (a + 1) c r hKαd hKβd hr] at h3
  have hKall : ∀ q ∈ (Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ, IsCusp q.2 := by
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hKα q hq
    · exact hKβ q hq
  have hKd : degL ((Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ) = r := by
    rw [GlobalTheory.GLq.LabelMul.degL_append, hKαd, hKβd, hr]
  have hB := GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKall _ hKd
  have hAB := GlobalTheory.GLq.DetRoot.ip_ne_zero_of_common hψ hA hB hQi h3
  refine fin ((Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ) ?_ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))))
  by_contra hn
  exact hAB ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp p _ _ _ hQd hKd hQc hKall).1 hn)

end GlobalTheory.GLq.DetSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLabelRootOfHarishChandraConstituentStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLabel_root_of_harishChandraConstituent : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r a c : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (u : ZMod p) (f : Polynomial (ZMod p)) (ψ : GlobalTheory.GLq.Gn p r → ℂ) (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ) (β : GlobalTheory.GLq.Gn p c → ℂ) (σ : GlobalTheory.GLq.Gn p a → ℂ), r = a + 1 + c → GlobalTheory.GLq.IsIrr ψ → GlobalTheory.GLq.IsIrr α → GlobalTheory.GLq.IsIrr β → GlobalTheory.GLq.IsIrr σ → GlobalTheory.GLq.HasLabel L ψ f → GlobalTheory.GLp.IsCharLab L θ u → GlobalTheory.GLq.ip ψ (GlobalTheory.GLq.hc (a + 1) c α β r) ≠ 0 → GlobalTheory.GLq.ip α (GlobalTheory.GLq.hc a 1 σ (fun y : GlobalTheory.GLq.Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (a + 1)) ≠ 0 → f.IsRoot u := by
  first | exact @GlobalTheory.GLq.DetSplit.root_of_constituent | exact GlobalTheory.GLq.DetSplit.root_of_constituent | (intros; apply GlobalTheory.GLq.DetSplit.root_of_constituent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleDetTwistOfStdTraceTwoBlock
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleDetTwistOfStdTraceTwoBlock
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LevelType.RestrictionTwo

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

theorem stdBlock_iff (a : ℕ) (y : Gn p (a + 1)) :
    StdBlock a y ↔ InPar a (y : Mt p (a + 1)) ∧ tl a (y : Mt p (a + 1)) = 1 := by
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_⟩
    · rw [h i j (by omega)]
      have : i ≠ j := fun e => by rw [e] at hi; omega
      simp [this]
    · ext i j
      have hi : (i : ℕ) < a + 1 := by omega
      have hj : (j : ℕ) < a + 1 := by omega
      have := h ⟨i, hi⟩ ⟨j, hj⟩ (by first | omega | simp | (simp; omega))
      simp only [tl, entN, hi, hj, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff] at this ⊢
      exact this
  · rintro ⟨h1, h2⟩ i j hij
    have hj : (j : ℕ) < a := by omega
    by_cases hi : (i : ℕ) < a
    · have := congrFun (congrFun h2 ⟨i, hi⟩) ⟨j, hj⟩
      have hi' : (i : ℕ) < a + 1 := by omega
      have hj' : (j : ℕ) < a + 1 := by omega
      simp only [tl, entN, hi', hj', and_self, dif_pos, Matrix.one_apply, Fin.ext_iff] at this
      simp only [Fin.ext_iff]
      exact this
    · have hne : i ≠ j := fun e => by rw [e] at hi; omega
      rw [if_neg hne]
      exact h1 i j hj (by omega)

theorem det_eq_of_stdBlock (a : ℕ) (y : Gn p (a + 1)) (h : StdBlock a y) :
    Matrix.GeneralLinearGroup.det y = Matrix.GeneralLinearGroup.det (toG (br a 1 (y : Mt p (a + 1)))) := by
  obtain ⟨h1, h2⟩ := (stdBlock_iff a y).1 h
  rw [GlobalTheory.GLq.LabelDet.det_par a 1 y h1, h2, GlobalTheory.GLq.LabelDet.toG_one, map_one, one_mul]

theorem br_eq_iff (a : ℕ) (y : Gn p (a + 1)) (h : InPar a (y : Mt p (a + 1))) (x : Gn p 1) :
    br a 1 (y : Mt p (a + 1)) = (x : Mt p 1) ↔ x = toG (br a 1 (y : Mt p (a + 1))) := by
  have hd := GlobalTheory.GLq.LabelDet.det_inPar a 1 _ h
  have h0 : (tl a (y : Mt p (a + 1))).det * (br a 1 (y : Mt p (a + 1))).det ≠ 0 := hd ▸ y.det_ne_zero
  have hu : IsUnit (br a 1 (y : Mt p (a + 1))) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (right_ne_zero_of_mul h0))
  have hv : ((toG (br a 1 (y : Mt p (a + 1))) : Gn p 1) : Mt p 1) = br a 1 (y : Mt p (a + 1)) := by
    unfold toG; rw [dif_pos hu]; exact IsUnit.unit_spec hu
  constructor
  · intro e; apply Units.ext; rw [hv, e]
  · intro e; rw [e, hv]

theorem sum_res_eq (a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (α : Gn p (a + 1) → ℂ) :
    ∑ x : Gn p 1, ((θ⁻¹ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res a 1 α 1 x =
      ((p : ℂ) ^ a)⁻¹ * stdTrace a θ α := by
  rw [stdTrace, Finset.mul_sum]
  unfold res
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hs : StdBlock a y
  · obtain ⟨h1, h2⟩ := (stdBlock_iff a y).1 hs
    rw [if_pos hs]
    have e : ∀ x : Gn p 1, ((θ⁻¹ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * (((p : ℂ) ^ (a * 1))⁻¹ *
        if InPar a (y : Mt p (a + 1)) ∧ tl a (y : Mt p (a + 1)) = ((1 : Gn p a) : Mt p a) ∧
          br a 1 (y : Mt p (a + 1)) = (x : Mt p 1) then α y else 0) =
        if x = toG (br a 1 (y : Mt p (a + 1))) then
          ((p : ℂ) ^ a)⁻¹ * ((((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * α y) else 0 := by
      intro x
      by_cases hx : x = toG (br a 1 (y : Mt p (a + 1)))
      · rw [if_pos ⟨h1, by rw [h2, Units.val_one], (br_eq_iff a y h1 x).2 hx⟩, if_pos hx, det_eq_of_stdBlock a y hs, ← hx,
          MonoidHom.inv_apply, Nat.mul_one]
        ring
      · rw [if_neg (fun h => hx ((br_eq_iff a y h1 x).1 h.2.2)), if_neg hx, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_ite_eq']
    simp
  · rw [if_neg hs, mul_zero]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg, mul_zero, mul_zero]
    rintro ⟨h1, h2, -⟩
    exact hs ((stdBlock_iff a y).2 ⟨h1, by rw [h2, Units.val_one]⟩)

theorem exists_irr_hc_of_stdTrace_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ)
    (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ), GlobalTheory.GLq.IsIrr α → stdTrace a θ α ≠ 0 →
    ∃ σ : GlobalTheory.GLq.Gn p a → ℂ, GlobalTheory.GLq.IsIrr σ ∧ GlobalTheory.GLq.ip α (GlobalTheory.GLq.hc a 1 σ
      (fun y : GlobalTheory.GLq.Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (a + 1)) ≠ 0 := by
  intro p _ a θ α hα hne
  have key : ∑ x : Gn p 1, ((θ⁻¹ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res a 1 α 1 x ≠ 0 := by
    rw [sum_res_eq]
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))) hne
  obtain ⟨σ, hσ, h⟩ := (GlobalTheory.GLq.HCFrobWeight.exists_irr_hc_thetaInv p a α hα θ⁻¹).1 key
  exact ⟨σ, hσ, by simpa only [inv_inv] using h⟩

end GlobalTheory.LevelType.RestrictionTwo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleDetTwistOfStdTraceTwoBlockStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_detTwist_of_stdTrace_twoBlock : ∀ (p : ℕ) [Fact p.Prime] (a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ), GlobalTheory.GLq.IsIrr α → stdTrace a θ α ≠ 0 → ∃ σ : GlobalTheory.GLq.Gn p a → ℂ, GlobalTheory.GLq.IsIrr σ ∧ GlobalTheory.GLq.ip α (GlobalTheory.GLq.hc a 1 σ (fun y : GlobalTheory.GLq.Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (a + 1)) ≠ 0 := by
  first | exact @GlobalTheory.LevelType.RestrictionTwo.exists_irr_hc_of_stdTrace_ne_zero | exact GlobalTheory.LevelType.RestrictionTwo.exists_irr_hc_of_stdTrace_ne_zero | (intros; apply GlobalTheory.LevelType.RestrictionTwo.exists_irr_hc_of_stdTrace_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedParahoricBlockVectorOfIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedParahoricBlockVectorOfIdempotent
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockIdem

open ValuativeRel Matrix GlobalTheory.StepData

theorem conv_sum {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (T : G → W →ₗ[ℂ] W) (f : G → W)
    (hT : ∀ g h, T g (f h) = f (g * h)) (a b : MonoidAlgebra ℂ G) :
    (a.coeff.sum fun g c => c • T g (b.coeff.sum fun h d => d • f h)) = (a * b).coeff.sum fun k c => c • f k := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' ha ha' =>
    rw [add_mul, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add, Finsupp.sum_add_index', Finsupp.sum_add_index', ha, ha']
      <;> intros <;> simp [add_smul]
  | single g c =>
    rw [MonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp)]
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' hb hb' =>
      rw [mul_add, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add, Finsupp.sum_add_index', Finsupp.sum_add_index',
        map_add (f := _), smul_add, hb, hb'] <;> intros <;> simp [add_smul]
    | single h d =>
      rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
        Finsupp.sum_single_index, Finsupp.sum_single_index, map_smul, hT, smul_smul] <;> simp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {r t : ℕ}

def ee (r t : ℕ) : Fin r ⊕ Fin t ≃ Fin (r + t) := stdSum (rfl : r + t = r + t)

theorem ee_inl (i : Fin r) : ee r t (Sum.inl i) = Fin.castAdd t i := by ext; simp [ee]

theorem ee_inr (j : Fin t) : ee r t (Sum.inr j) = Fin.natAdd r j := by ext; simp [ee]


variable (F) in
def dg (r t : ℕ) : GL (Fin r) F →* GL (Fin (r + t)) F := (emb₂ F (ee r t)).comp (MonoidHom.inl _ _)


variable (F) in
def bl (r t : ℕ) : GL (Fin (r + t)) F →* GL (Fin r ⊕ Fin t) F := reix F (ee r t).symm

theorem bl_apply (g : GL (Fin (r + t)) F) (a b : Fin r ⊕ Fin t) : (bl F r t g).val a b = g.val (ee r t a) (ee r t b) := by
  rw [bl, val_reix, Equiv.symm_symm]

theorem eq_of_bl {g g' : GL (Fin (r + t)) F} (H : (bl F r t g).val = (bl F r t g').val) : g = g' := by
  apply Units.ext
  ext a b
  obtain ⟨a, rfl⟩ := (ee r t).surjective a
  obtain ⟨b, rfl⟩ := (ee r t).surjective b
  have := congrFun (congrFun H a) b
  rwa [bl_apply, bl_apply] at this

theorem dg_bl (A : GL (Fin r) F) : (bl F r t (dg F r t A)).val = fromBlocks A.val 0 0 1 := by
  ext a b
  rw [bl_apply]
  have := val_emb₂ F (ee r t) (A, 1)
  simp only [dg, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply]
  rw [this, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

theorem bl_21 (g : GL (Fin (r + t)) F) (i : Fin t) (j : Fin r) :
    (bl F r t g).val.toBlocks₂₁ i j = g.val (Fin.natAdd r i) (Fin.castAdd t j) := by
  simp only [toBlocks₂₁, of_apply, bl_apply, ee_inr, ee_inl]

theorem bl_11 (g : GL (Fin (r + t)) F) (i j : Fin r) :
    (bl F r t g).val.toBlocks₁₁ i j = g.val (Fin.castAdd t i) (Fin.castAdd t j) := by
  simp only [toBlocks₁₁, of_apply, bl_apply, ee_inl]

theorem bl_22 (g : GL (Fin (r + t)) F) :
    (bl F r t g).val.toBlocks₂₂ = g.val.submatrix (Fin.natAdd r) (Fin.natAdd r) := by
  ext i j
  simp only [toBlocks₂₂, of_apply, bl_apply, ee_inr, submatrix_apply]

theorem intM_dg {A : GL (Fin r) F} (hA : IntM A.val) : IntM (dg F r t A).val := by
  intro a b
  obtain ⟨a, rfl⟩ := (ee r t).surjective a
  obtain ⟨b, rfl⟩ := (ee r t).surjective b
  have := congrFun (congrFun (dg_bl (t := t) A) a) b
  rw [bl_apply] at this
  rw [this]
  exact intM_fromBlocks.2 ⟨hA, intM_zero, intM_zero, intM_one⟩ a b

theorem dg_mem_KO {A : GL (Fin r) F} (hA : A ∈ KO F (Fin r)) : dg F r t A ∈ KO F (Fin (r + t)) :=
  GlobalTheory.StepData.mem_KO.2 ⟨intM_dg (GlobalTheory.StepData.mem_KO.1 hA).1,
    by rw [← map_inv]; exact intM_dg (GlobalTheory.StepData.mem_KO.1 hA).2⟩

end GlobalTheory.BlockIdem

namespace GlobalTheory.BlockIdem

open ValuativeRel Matrix GlobalTheory.StepData

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {r t : ℕ}
  {χ : Fˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin (r + t)) F) W}

theorem isBlockVec_add {v w : W} (hv : IsBlockVec χ π v) (hw : IsBlockVec χ π w) : IsBlockVec χ π (v + w) :=
  fun h hh h1 h2 u hu => by rw [map_add (f := _), hv h hh h1 h2 u hu, hw h hh h1 h2 u hu, smul_add]

theorem isBlockVec_smul (c : ℂ) {v : W} (hv : IsBlockVec χ π v) : IsBlockVec χ π (c • v) :=
  fun h hh h1 h2 u hu => by rw [map_smul, hv h hh h1 h2 u hu, smul_comm]

theorem isBlockVec_zero : IsBlockVec χ π (0 : W) := fun _ _ _ _ _ _ => by simp

theorem dg_fix {v : W} (hv : IsBlockVec χ π v) {κ : GL (Fin r) F} (hκ : κ ∈ KOne F (Fin r)) :
    π (dg F r t κ) v = v := by
  have key := hv _ (dg_mem_KO (GlobalTheory.StepData.KOne_le_KO hκ))
    (fun i j => by rw [← bl_21, dg_bl, toBlocks_fromBlocks₂₁]; simp)
    (fun i j => by
      rw [← bl_11, dg_bl, toBlocks_fromBlocks₁₁]
      have := (GlobalTheory.StepData.mem_KOne.1 hκ) i j
      rwa [Matrix.sub_apply, Matrix.one_apply] at this)
    1 (by rw [← bl_22, dg_bl, toBlocks_fromBlocks₂₂, det_one, Units.val_one])
  rw [key, map_one, Units.val_one, one_smul]

theorem dg_isBlockVec {v : W} (hv : IsBlockVec χ π v) {κ : GL (Fin r) F} (hκ : κ ∈ KO F (Fin r)) :
    IsBlockVec χ π (π (dg F r t κ) v) := by
  intro h hh h1 h2 u hu
  have hd := dg_mem_KO (t := t) hκ
  have hK : (dg F r t κ)⁻¹ * h * dg F r t κ ∈ KO F (Fin (r + t)) := mul_mem (mul_mem (inv_mem hd) hh) hd
  obtain ⟨A, B, C, D, hE⟩ : ∃ A B C D, (bl F r t h).val = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩
  have hΦ : (bl F r t ((dg F r t κ)⁻¹ * h * dg F r t κ)).val =
      fromBlocks ((κ⁻¹).val * A * κ.val) ((κ⁻¹).val * B) (C * κ.val) D := by
    rw [← map_inv (dg F r t) κ, map_mul, map_mul, Units.val_mul, Units.val_mul, dg_bl, dg_bl, hE,
      fromBlocks_multiply, fromBlocks_multiply]
    simp [Matrix.mul_assoc]
  have hC : MaxM C := fun i j => by
    rw [show C i j = h.val (Fin.natAdd r i) (Fin.castAdd t j) by rw [← bl_21, hE, toBlocks_fromBlocks₂₁]]
    exact h1 i j
  have hA : MaxM (A - 1) := fun i j => by
    rw [Matrix.sub_apply, Matrix.one_apply]
    rw [show A i j = h.val (Fin.castAdd t i) (Fin.castAdd t j) by rw [← bl_11, hE, toBlocks_fromBlocks₁₁]]
    exact h2 i j
  have key := hv _ hK
    (fun i j => by rw [← bl_21, hΦ, toBlocks_fromBlocks₂₁]; exact hC.mul_intM (intM_of_mem_KO hκ) i j)
    (fun i j => by
      rw [← bl_11, hΦ, toBlocks_fromBlocks₁₁]
      have e : (κ⁻¹).val * A * κ.val - 1 = (κ⁻¹).val * (A - 1) * κ.val := by
        rw [mul_sub, sub_mul, mul_one, Units.inv_mul]
      have := ((((GlobalTheory.StepData.mem_KO.1 hκ).2).mul_maxM hA).mul_intM (intM_of_mem_KO hκ)) i j
      rw [← e, Matrix.sub_apply, Matrix.one_apply] at this
      exact this)
    u (by
      rw [← bl_22, hΦ, toBlocks_fromBlocks₂₂]
      rw [← bl_22, hE, toBlocks_fromBlocks₂₂] at hu
      exact hu)
  have hh' : h * dg F r t κ = dg F r t κ * ((dg F r t κ)⁻¹ * h * dg F r t κ) := by group
  calc π h (π (dg F r t κ) v) = π (dg F r t κ) (π ((dg F r t κ)⁻¹ * h * dg F r t κ) v) := by
        rw [← Module.End.mul_apply, ← map_mul, hh', map_mul, Module.End.mul_apply]
    _ = (χ u : ℂ) • π (dg F r t κ) v := by rw [key, map_smul]

theorem exists_of_isLiftN {p : ℕ} {g : GL (Fin r) (ZMod p)} {h : GL (Fin (r + t)) F} (H : IsLiftN g h) :
    ∃ A : GL (Fin r) F, dg F r t A = h ∧ IsLift g A := by
  set M : Matrix (Fin r) (Fin r) F := fun i j => h.val (Fin.castAdd t i) (Fin.castAdd t j) with hM
  have hΦ : (bl F r t h).val = fromBlocks M 0 0 1 := by
    ext (a | a) (b | b)
    · rw [bl_apply, ee_inl, ee_inl, fromBlocks_apply₁₁]
    · have := H (Fin.castAdd t a) (Fin.natAdd r b)
      rw [dite_eq_right (by simp only [Fin.coe_castAdd, Fin.coe_natAdd]; omega)] at this
      have hne : Fin.castAdd t a ≠ Fin.natAdd r b := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      simp [bl_apply, ee_inl, ee_inr, this, hne]
    · have := H (Fin.natAdd r a) (Fin.castAdd t b)
      rw [dite_eq_right (by simp only [Fin.coe_castAdd, Fin.coe_natAdd]; omega)] at this
      have hne : Fin.natAdd r a ≠ Fin.castAdd t b := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      simp [bl_apply, ee_inl, ee_inr, this, hne]
    · have := H (Fin.natAdd r a) (Fin.natAdd r b)
      rw [dite_eq_right (by simp only [Fin.coe_castAdd, Fin.coe_natAdd]; omega)] at this
      simp [bl_apply, ee_inr, this, Matrix.one_apply]
  have hdet : IsUnit M.det := by
    have h1 : IsUnit (bl F r t h).val.det := (Matrix.isUnit_iff_isUnit_det _).1 (bl F r t h).isUnit
    rwa [hΦ, Matrix.det_fromBlocks_zero₂₁, det_one, mul_one] at h1
  refine ⟨Matrix.nonsingInvUnit M hdet, eq_of_bl ?_, fun a b => ?_⟩
  · rw [dg_bl, hΦ]; rfl
  · have := H (Fin.castAdd t a) (Fin.castAdd t b)
    rw [dite_eq_left (show ((Fin.castAdd t a : Fin (r + t)) : ℕ) < r ∧ ((Fin.castAdd t b : Fin (r + t)) : ℕ) < r
      from ⟨a.isLt, b.isLt⟩)] at this
    exact this

end GlobalTheory.BlockIdem

namespace GlobalTheory.BlockIdem

open ValuativeRel Matrix GlobalTheory.StepData

theorem exists_fixed_blockVec : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (r t : ℕ) (χ : Fˣ →* ℂˣ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) F) W) (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (x : W), resCard F = p → z * z = z → IsBlockVec χ π x → NotKilled π z x → ∃ y : W, y ≠ 0 ∧ IsBlockVec χ π y ∧ ∃ ℓ : GL (Fin r) (ZMod p) → GL (Fin r) F, (∀ g, IsLift g (ℓ g)) ∧ (z.coeff.sum fun g c => c • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) = y := by
  intro F _ _ _ _ p _ r t χ W _ _ π z x hp hz hx hnk
  obtain ⟨ℓ', hℓ', hne⟩ := hnk
  have hA : ∀ g, ∃ A : GL (Fin r) F, dg F r t A = ℓ' g ∧ IsLift g A := fun g => exists_of_isLiftN (hℓ' g)
  choose ℓ hℓ1 hℓ2 using hA
  have hx1 : ∀ h ∈ KOne F (Fin r), (π.comp (dg F r t)) h x = x := fun h hh => dg_fix hx hh
  have hT : ∀ g h, π (dg F r t (ℓ g)) (π (dg F r t (ℓ h)) x) = π (dg F r t (ℓ (g * h))) x := by
    intro g h
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul]
    exact IsLift.apply_eq hp (π := π.comp (dg F r t)) hx1 ((hℓ2 g).mul hp (hℓ2 h)) (hℓ2 (g * h))
  refine ⟨z.coeff.sum fun g c => c • π (dg F r t (ℓ g)) x, ?_, ?_, ℓ, hℓ2, ?_⟩
  · simpa only [hℓ1] using hne
  · rw [Finsupp.sum]
    exact Finset.sum_induction _ _ (fun a b => isBlockVec_add) isBlockVec_zero
      (fun g _ => isBlockVec_smul _ (dg_isBlockVec hx ((hℓ2 g).mem_KO hp)))
  · have := conv_sum (fun g => π (dg F r t (ℓ g))) (fun h => π (dg F r t (ℓ h)) x) hT z z
    rw [hz] at this
    exact this

end GlobalTheory.BlockIdem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedParahoricBlockVectorOfIdempotentStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixed_parahoricBlockVector_of_idempotent : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (r t : ℕ) (χ : Fˣ →* ℂˣ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) F) W) (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (x : W), resCard F = p → z * z = z → IsBlockVec χ π x → NotKilled π z x → ∃ y : W, y ≠ 0 ∧ IsBlockVec χ π y ∧ ∃ ℓ : GL (Fin r) (ZMod p) → GL (Fin r) F, (∀ g, IsLift g (ℓ g)) ∧ (z.coeff.sum fun g c => c • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) = y := by
  first | exact @GlobalTheory.BlockIdem.exists_fixed_blockVec | exact GlobalTheory.BlockIdem.exists_fixed_blockVec | (intros; apply GlobalTheory.BlockIdem.exists_fixed_blockVec <;> assumption)
end
end
