module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlIntertwinerOfResidualSpanEqTop

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

def IsUnrExt (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) : Prop :=
  K'.q = K.q ^ d ∧ (∀ x, φ (K.c x) = K'.c (φ x)) ∧ (∀ x, val K'.O (φ x) = val K.O x) ∧ (K.Odd → K'.Odd) ∧
    @Module.finrank K.E K'.E _ _ (φ.toAlgebra).toModule = d

variable {K K' : UQ}

def overExt (φ : K.E →+* K'.E) (B : InvAlg K) (ψ : K'.E →+* B.A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) : InvAlg K' :=
  letI : Algebra K'.E B.A := ψ.toAlgebra
  letI : Algebra K'.O B.A := (ψ.comp (algebraMap K'.O K'.E)).toAlgebra
  haveI : IsScalarTower K'.O K'.E B.A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite K'.E B.A := by
    obtain ⟨S, hS⟩ := B.fd.fg_top
    refine ⟨⟨S, eq_top_iff.2 fun y hy0 => ?_⟩⟩
    clear hy0
    have hy : y ∈ Submodule.span K.E (S : Set B.A) := hS ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul e x _ hx =>
      have h : e • x = (φ e) • x := by
        rw [Algebra.smul_def, Algebra.smul_def, ← hψ e]; rfl
      rw [h]; exact Submodule.smul_mem _ _ hx
  { A := B.A
    σ := B.σ
    σ_σ := B.σ_σ
    σ_alg := hσ
    g := B.g }

end GlobalTheory.UnitLemma.Unr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariants
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariants
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.NormalFormL

variable {k : Type} [Field k] {r : ℕ}

def ev (r : ℕ) (k : Type) [Field k] (i : ℕ) : Fin r → k := fun j => if (j : ℕ) = i then 1 else 0

theorem ev_eq_single (i : ℕ) (hi : i < r) : ev r k i = Pi.single (⟨i, hi⟩ : Fin r) 1 := by
  funext j
  simp only [ev, Pi.single_apply, Fin.ext_iff]

theorem sum_mulVec' {ι : Type} (s : Finset ι) (M : ι → Matrix (Fin r) (Fin r) k) (v : Fin r → k) :
    (∑ i ∈ s, M i) *ᵥ v = ∑ i ∈ s, M i *ᵥ v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mulVec, ih]

theorem pow_card_eq (M : Matrix (Fin r) (Fin r) k) :
    M ^ r = - ∑ l ∈ Finset.range r, M.charpoly.coeff l • M ^ l := by
  have h0 := aeval_self_charpoly M
  rw [Polynomial.aeval_eq_sum_range, charpoly_natDegree_eq_dim, Fintype.card_fin,
    Finset.sum_range_succ] at h0
  have h1 : M.charpoly.coeff r = 1 := by
    have := (charpoly_monic M).leadingCoeff
    rwa [Polynomial.leadingCoeff, charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  rw [h1, one_smul] at h0
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h0

theorem companion_mulVec_ev (p : Fin r → k) (i : ℕ) (hi : i + 1 < r) :
    companion p *ᵥ ev r k i = ev r k (i + 1) := by
  rw [ev_eq_single i (by omega)]
  funext j
  simp only [mulVec_single, companion, of_apply, mul_one, ev]
  have : ¬ (i + 1 = r) := by omega
  simp [this]

theorem companion_mulVec_last (p : Fin r → k) (i : ℕ) (hi : i + 1 = r) :
    companion p *ᵥ ev r k i = - p := by
  rw [ev_eq_single i (by omega)]
  funext j
  simp [mulVec_single, companion, hi]

theorem companion_pow_ev (p : Fin r → k) (i : ℕ) (hi : i < r) :
    companion p ^ i *ᵥ ev r k 0 = ev r k i := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', ← mulVec_mulVec, ih (by omega), companion_mulVec_ev p i hi]

theorem companion_pow_card (p : Fin r → k) (hr : 0 < r) :
    companion p ^ r *ᵥ ev r k 0 = - p := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [pow_succ', ← mulVec_mulVec, companion_pow_ev p m (by omega), companion_mulVec_last p m rfl]

theorem charpoly_companion_coeff (p : Fin r → k) (i : Fin r) :
    (companion p).charpoly.coeff i = p i := by
  have hr : 0 < r := i.pos
  have h := pow_card_eq (companion p)
  have h2 := congrArg (fun M => M *ᵥ ev r k 0) h
  simp only [companion_pow_card p hr, neg_mulVec, sum_mulVec', smul_mulVec] at h2
  have h3 := congrFun h2 i
  simp only [Pi.neg_apply, neg_inj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3
  rw [h3, Finset.sum_eq_single (i : ℕ)]
  · simp [companion_pow_ev p i i.2, ev]
  · intro b hb hne
    rw [companion_pow_ev p b (Finset.mem_range.mp hb)]
    simp [ev, Ne.symm hne]
  · intro h; exact absurd (Finset.mem_range.mpr i.2) h

end GlobalTheory.JR.NormalFormL

namespace GlobalTheory.JR.NormalFormL

variable {k : Type} [Field k] {r : ℕ}

theorem inv_act' (g : GL (Fin r) k) (Y : Gl r k) : inv (act g Y) = inv Y := by
  obtain ⟨A, b, c, l⟩ := Y
  simp only [inv, act, mom, Prod.mk.injEq, and_true]
  refine ⟨?_, ?_⟩
  · funext i
    rw [Matrix.coe_units_inv, charpoly_units_conj]
  · funext i
    rw [Units.conj_pow, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
    congr 2
    simp [mul_assoc]

theorem act_mul' (g h : GL (Fin r) k) (Y : Gl r k) : act (g * h) Y = act g (act h Y) := by
  obtain ⟨A, b, c, l⟩ := Y
  simp only [act, _root_.mul_inv_rev, Units.val_mul, mulVec_mulVec, vecMul_vecMul, Prod.mk.injEq, and_true]
  try simp [mul_assoc]

theorem inv_sec' (a : Inv r k) : inv (sec a) = a := by
  obtain ⟨p, m, l⟩ := a
  simp only [inv, sec, Prod.mk.injEq, and_true]
  refine ⟨funext fun i => charpoly_companion_coeff p i, funext fun i => ?_⟩
  have he : (fun i : Fin r => if (i : ℕ) = 0 then (1 : k) else 0) = ev r k 0 := rfl
  simp only [mom, he, companion_pow_ev p i i.2, ev_eq_single (i : ℕ) i.2, dotProduct_single, mul_one]

theorem charpoly_companion_inv (Y : Gl r k) : (companion (inv Y).1).charpoly = Y.1.charpoly := by
  apply Polynomial.ext
  intro n
  rcases lt_trichotomy n r with h | h | h
  · exact charpoly_companion_coeff _ ⟨n, h⟩
  · subst h
    have h1 := (charpoly_monic (companion (inv Y).1)).leadingCoeff
    have h2 := (charpoly_monic Y.1).leadingCoeff
    rw [Polynomial.leadingCoeff, charpoly_natDegree_eq_dim, Fintype.card_fin] at h1 h2
    rw [h1, h2]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt] <;>
      simpa using h

theorem dot_pow_eq_sum (M : Matrix (Fin r) (Fin r) k) (hr : 0 < r) (b c : Fin r → k) (n : ℕ) :
    c ⬝ᵥ (M ^ n *ᵥ b) = ∑ i ∈ Finset.range r,
      ((Polynomial.X ^ n) %ₘ M.charpoly).coeff i * (c ⬝ᵥ (M ^ i *ᵥ b)) := by
  have hmon := charpoly_monic M
  have hdeg : M.charpoly.natDegree = r := by simp
  have hne : M.charpoly ≠ 1 := by
    intro h; rw [h, Polynomial.natDegree_one] at hdeg; omega
  have hM : M ^ n = Polynomial.aeval M ((Polynomial.X ^ n) %ₘ M.charpoly) := by
    rw [Polynomial.aeval_modByMonic_eq_self_of_root (aeval_self_charpoly M)]
    simp
  rw [hM, Polynomial.aeval_eq_sum_range' (n := r)
    (by have := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ n) hmon hne; omega), sum_mulVec', dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem mom_sec_inv (Y : Gl r k) (n : ℕ) : mom (sec (inv Y)) n = mom Y n := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp [mom, dotProduct]
  have hs := inv_sec' (inv Y)
  simp only [mom]
  rw [dot_pow_eq_sum _ hr, dot_pow_eq_sum _ hr]
  have hc : (sec (inv Y)).1.charpoly = Y.1.charpoly := charpoly_companion_inv Y
  rw [hc]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  have := congrFun (congrArg (fun a : Inv r k => a.2.1) hs) ⟨i, Finset.mem_range.mp hi⟩
  simpa [inv, mom] using this

theorem hankel_eq (Y : Gl r k) : Cm Y * Bm Y = hankel (inv Y) := by
  ext i j
  simp only [mul_apply, Cm, Bm, hankel, of_apply, mom_sec_inv]
  simp only [mom]
  rw [pow_add, ← mulVec_mulVec, dotProduct_mulVec]
  rfl

end GlobalTheory.JR.NormalFormL

namespace GlobalTheory.JR.NormalFormL

variable {k : Type} [Field k] {r : ℕ}

theorem mul_Bm (Y : Gl r k) : Y.1 * Bm Y = Bm Y * companion (inv Y).1 := by
  ext i j
  have hl : (Y.1 * Bm Y) i j = (Y.1 ^ ((j : ℕ) + 1) *ᵥ Y.2.1) i := by
    rw [pow_succ', ← mulVec_mulVec]
    simp [Matrix.mul_apply, Bm, mulVec, dotProduct]
  rw [hl, Matrix.mul_apply]
  by_cases hj : (j : ℕ) + 1 = r
  · simp only [companion, of_apply, hj, if_true, Bm, inv]
    rw [pow_card_eq Y.1, neg_mulVec, sum_mulVec']
    simp only [Pi.neg_apply, Finset.sum_apply, smul_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun l => (Y.1 ^ l *ᵥ Y.2.1) i * -Y.1.charpoly.coeff l),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  · have hj' : (j : ℕ) + 1 < r := by omega
    rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hj'⟩ : Fin r)]
    · simp [companion, hj, Bm]
    · intro l _ hne
      have : ¬ ((l : ℕ) = (j : ℕ) + 1) := fun h => hne (Fin.ext h)
      simp [companion, hj, this]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem vecMul_Bm (Y : Gl r k) : Y.2.2.1 ᵥ* Bm Y = (inv Y).2.1 := by
  funext j
  simp [vecMul, dotProduct, Bm, inv, mom, mulVec]

theorem det_Bm_ne (Y : Gl r k) (h : Delta (inv Y) ≠ 0) : (Bm Y).det ≠ 0 := by
  intro h0
  apply h
  rw [Delta, ← hankel_eq, det_mul, h0, mul_zero]

theorem unique_conj (Y Y₁ : Gl r k) (hΔ : Delta (inv Y) ≠ 0) (hI : inv Y₁ = inv Y) :
    ∃! g : GL (Fin r) k, act g Y = Y₁ ∧ (g : Matrix (Fin r) (Fin r) k) * Bm Y = Bm Y₁ := by
  have hB : IsUnit (Bm Y) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_Bm_ne Y hΔ))
  have hB₁ : IsUnit (Bm Y₁) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_Bm_ne Y₁ (hI ▸ hΔ)))
  set u := hB.unit with hu
  set u₁ := hB₁.unit with hu₁
  have eu : (u : Matrix (Fin r) (Fin r) k) = Bm Y := hB.unit_spec
  have eu₁ : (u₁ : Matrix (Fin r) (Fin r) k) = Bm Y₁ := hB₁.unit_spec
  refine ⟨u₁ * u⁻¹, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨A, b, c, l⟩ := Y
    obtain ⟨A₁, b₁, c₁, l₁⟩ := Y₁
    have hAB := mul_Bm (A, b, c, l)
    have hAB₁ := mul_Bm (A₁, b₁, c₁, l₁)
    have hc := vecMul_Bm (A, b, c, l)
    have hc₁ := vecMul_Bm (A₁, b₁, c₁, l₁)
    rw [hI] at hAB₁ hc₁
    rw [← eu] at hAB hc
    rw [← eu₁] at hAB₁ hc₁
    have hl : l₁ = l := congrArg (fun a : Inv r k => a.2.2) hI
    simp only [act, _root_.mul_inv_rev, inv_inv, Units.val_mul, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, hl.symm⟩
    · calc (u₁ : Matrix (Fin r) (Fin r) k) * ↑u⁻¹ * A * (↑u * ↑u₁⁻¹)
            = ↑u₁ * (↑u⁻¹ * (A * ↑u)) * ↑u₁⁻¹ := by simp only [mul_assoc]
          _ = ↑u₁ * companion (inv (A, b, c, l)).1 * ↑u₁⁻¹ := by
            rw [hAB, Units.inv_mul_cancel_left]
          _ = A₁ := by rw [← hAB₁, Units.mul_inv_cancel_right]
    · rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; funext i; exact i.elim0
      have e0 : ∀ (B : Matrix (Fin r) (Fin r) k) (Z : Gl r k), B = Bm Z →
          B *ᵥ Pi.single (⟨0, hr⟩ : Fin r) 1 = Z.2.1 := by
        intro B Z hBZ; subst hBZ; funext i; simp [mulVec_single, Bm, Function.swap]
      have hb : (u : Matrix (Fin r) (Fin r) k) *ᵥ Pi.single (⟨0, hr⟩ : Fin r) 1 = b :=
        e0 _ (A, b, c, l) eu
      have hb₁ : (u₁ : Matrix (Fin r) (Fin r) k) *ᵥ Pi.single (⟨0, hr⟩ : Fin r) 1 = b₁ :=
        e0 _ (A₁, b₁, c₁, l₁) eu₁
      rw [← hb, mulVec_mulVec, mul_assoc, Units.inv_mul, mul_one, hb₁]
    · have hc' : c ᵥ* (u : Matrix (Fin r) (Fin r) k) = c₁ ᵥ* (u₁ : Matrix (Fin r) (Fin r) k) :=
        hc.trans hc₁.symm
      rw [← vecMul_vecMul, hc', vecMul_vecMul, Units.mul_inv, vecMul_one]
  · rw [Units.val_mul, mul_assoc, eu.symm, Units.inv_mul, mul_one, eu₁]
  · rintro g ⟨_, hg⟩
    apply Units.ext
    rw [Units.val_mul, eu₁, ← hg, ← eu, mul_assoc, Units.mul_inv, mul_one]

end GlobalTheory.JR.NormalFormL

theorem GlobalTheory.JR.normalForm_invariants : ∀ (k : Type) [Field k] (r : ℕ), (∀ (g : GL (Fin r) k) (Y : Gl r k), inv (act g Y) = inv Y) ∧ (∀ a : Inv r k, inv (sec a) = a) ∧ (∀ Y : Gl r k, Cm Y * Bm Y = hankel (inv Y)) ∧ (∀ (g h : GL (Fin r) k) (Y : Gl r k), act (g * h) Y = act g (act h Y)) ∧ ∀ Y Y₁ : Gl r k, Delta (inv Y) ≠ 0 → inv Y₁ = inv Y → ∃! g : GL (Fin r) k, act g Y = Y₁ ∧ (g : Matrix (Fin r) (Fin r) k) * Bm Y = Bm Y₁ := by
  intro k _ r
  exact ⟨GlobalTheory.JR.NormalFormL.inv_act', GlobalTheory.JR.NormalFormL.inv_sec', GlobalTheory.JR.NormalFormL.hankel_eq,
    GlobalTheory.JR.NormalFormL.act_mul', GlobalTheory.JR.NormalFormL.unique_conj⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariantsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants : ∀ (k : Type) [Field k] (r : ℕ), (∀ (g : GL (Fin r) k) (Y : Gl r k), inv (act g Y) = inv Y) ∧ (∀ a : Inv r k, inv (sec a) = a) ∧ (∀ Y : Gl r k, Cm Y * Bm Y = hankel (inv Y)) ∧ (∀ (g h : GL (Fin r) k) (Y : Gl r k), act (g * h) Y = act g (act h Y)) ∧ ∀ Y Y₁ : Gl r k, Delta (inv Y) ≠ 0 → inv Y₁ = inv Y → ∃! g : GL (Fin r) k, act g Y = Y₁ ∧ (g : Matrix (Fin r) (Fin r) k) * Bm Y = Bm Y₁ := by
  first | exact @GlobalTheory.JR.normalForm_invariants | exact GlobalTheory.JR.normalForm_invariants | (intros; apply GlobalTheory.JR.normalForm_invariants <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow
noncomputable section
namespace GlobalTheory.PhiGam.Window
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem bij_of_gmult_zero {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (P Q : Submodule k U) (hP : ∀ p ∈ P, T p ∈ P) (hQ : ∀ p ∈ Q, T p ∈ Q)
    [hfin : FiniteDimensional k (P.map Q.mkQ)] (x : k) (h : gmult T P Q x = 0) :
    (∀ p ∈ P, T p - x • p ∈ Q → p ∈ Q) ∧ ∀ y ∈ P, ∃ p ∈ P, y - (T p - x • p) ∈ Q := by
  have hinj : ∀ p ∈ P, T p - x • p ∈ Q → p ∈ Q := by
    intro p hp hq
    unfold gmult at h
    set P' := P ⊓ ⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k U) x) ^ m) with hP'
    have hker : LinearMap.ker (Q.mkQ ∘ₗ P'.subtype) = Q.submoduleOf P' := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]; rfl
    have hle : LinearMap.range (Q.mkQ ∘ₗ P'.subtype) ≤ P.map Q.mkQ := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      exact Submodule.map_mono inf_le_left
    haveI : FiniteDimensional k (LinearMap.range (Q.mkQ ∘ₗ P'.subtype)) :=
      Submodule.finiteDimensional_of_le hle
    haveI : FiniteDimensional k (↥P' ⧸ Q.submoduleOf P') := by
      rw [← hker]
      exact LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange _).symm
    have hsub : Subsingleton (↥P' ⧸ Q.submoduleOf P') := Module.finrank_zero_iff.mp h
    have hmem : p ∈ P' := by
      refine ⟨hp, ?_⟩
      refine Submodule.mem_iSup_of_mem 1 ?_
      simpa [Module.algebraMap_end_apply] using hq
    have : (Submodule.Quotient.mk (⟨p, hmem⟩ : P') : ↥P' ⧸ Q.submoduleOf P') = 0 := Subsingleton.elim _ _
    exact (Submodule.Quotient.mk_eq_zero (Q.submoduleOf P')).mp this
  refine ⟨hinj, ?_⟩
  let S : U →ₗ[k] U := T - x • LinearMap.id
  have hS : ∀ p, S p = T p - x • p := fun p => rfl
  have hSQ : Q ≤ Q.comap S := fun p hp => by
    rw [Submodule.mem_comap, hS]; exact Q.sub_mem (hQ p hp) (Q.smul_mem _ hp)
  let Sq := Q.mapQ Q S hSQ
  have hSq : ∀ z ∈ P.map Q.mkQ, Sq z ∈ P.map Q.mkQ := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨S p, P.sub_mem (hP p hp) (P.smul_mem _ hp), rfl⟩
  have hi : Function.Injective (Sq.restrict hSq) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨_, p, hp, rfl⟩ hz
    have h1 : Q.mkQ (S p) = 0 := congrArg Subtype.val hz
    have h2 : p ∈ Q := hinj p hp ((Submodule.Quotient.mk_eq_zero _).mp h1)
    exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h2)
  have hs := LinearMap.injective_iff_surjective.mp hi
  intro y hy
  obtain ⟨⟨_, p, hp, rfl⟩, hz⟩ := hs ⟨Q.mkQ y, y, hy, rfl⟩
  have h1 : Q.mkQ (S p) = Q.mkQ y := congrArg Subtype.val hz
  exact ⟨p, hp, (Submodule.Quotient.eq _).mp h1.symm⟩

variable {k : Type} [Field k]

theorem vv_coe : vv k = ((PowerSeries.X : k⟦X⟧) : k⸨X⸩) := by
  simp [vv]

theorem vv_ne_zero : vv k ≠ 0 := by
  simp [vv]

theorem gam_zpow {l : ℕ} (R : RingPG k l) (b : ℤ) :
    ∃ c : k⟦X⟧, R.γ (vv k ^ b) = vv k ^ b * (1 - (b : k⸨X⸩) * vv k + (c : k⸨X⸩) * vv k ^ 2) := by
  obtain ⟨κ, hκ, hγ⟩ := R.γ_v
  obtain ⟨c0, hc0⟩ : (PowerSeries.X : k⟦X⟧) ∣ κ - 1 := by
    rw [PowerSeries.X_dvd_iff]; simp [hκ]
  have hκ' : κ = 1 + PowerSeries.X * c0 := by rw [← hc0]; ring
  have hu : IsUnit (1 - κ * PowerSeries.X : k⟦X⟧) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  obtain ⟨w', hw'⟩ := hu.exists_right_inv
  let ι : k⟦X⟧ →+* k⸨X⸩ := HahnSeries.ofPowerSeries ℤ k
  have hι : ∀ c : k⟦X⟧, (c : k⸨X⸩) = ι c := fun _ => rfl
  have hv : vv k = ι PowerSeries.X := vv_coe
  set w : k⸨X⸩ := 1 - (κ : k⸨X⸩) * vv k with hw
  have hw1 : w = 1 - vv k - ι c0 * vv k ^ 2 := by
    rw [hw, hι, hκ', hv]; simp only [map_add (f := _), map_mul, map_one]; ring
  have hww : w * ι w' = 1 := by
    have := congrArg ι hw'
    simp only [map_mul, map_sub, map_one] at this
    rw [hw, hv, hι]; exact this
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hww
  have hinv : w⁻¹ = ι w' := (eq_inv_of_mul_eq_one_right hww).symm
  have key : ∃ c : k⟦X⟧, w ^ b = 1 - (b : k⸨X⸩) * vv k + ι c * vv k ^ 2 := by
    induction b using Int.induction_on with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨(n : k⟦X⟧) - c0 + (n : k⟦X⟧) * c0 * PowerSeries.X + c * (1 - PowerSeries.X - c0 * PowerSeries.X ^ 2), ?_⟩
      rw [zpow_add_one₀ hw0, hc, hw1]
      simp only [map_add (f := _), map_sub, map_mul, map_one, map_pow, map_natCast, ← hv]
      push_cast
      ring
    | pred n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨w' * (c + ((n : k⟦X⟧) + 1) + c0 + ((n : k⟦X⟧) + 1) * c0 * PowerSeries.X), ?_⟩
      rw [zpow_sub_one₀ hw0, hc, hinv]
      simp only [map_add (f := _), map_sub, map_mul, map_one, map_pow, map_natCast, ← hv]
      push_cast
      rw [hw1] at hww
      linear_combination (1 + ((n : k⸨X⸩) + 1) * vv k) * hww
  obtain ⟨c, hc⟩ := key
  exact ⟨c, by rw [map_zpow₀, hγ, mul_zpow, hc]⟩

variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem mem_sh_iff {a : ℤ} {N : Submodule k⟦X⟧ V} {x : V} :
    x ∈ sh a N ↔ ∃ n ∈ N, vv k ^ a • n = x := Iff.rfl

theorem coe_smul_eq (c : k⟦X⟧) (x : V) : (c : k⸨X⸩) • x = c • x :=
  algebraMap_smul k⸨X⸩ c x

theorem v_smul_mem {N : Submodule k⟦X⟧ V} {n : V} (hn : n ∈ N) : vv k • n ∈ N := by
  rw [vv_coe, coe_smul_eq]; exact N.smul_mem _ hn

theorem sh_succ_le (a : ℤ) (N : Submodule k⟦X⟧ V) : sh (a + 1) N ≤ sh a N := by
  rintro _ ⟨n, hn, rfl⟩
  refine mem_sh_iff.mpr ⟨vv k • n, v_smul_mem hn, ?_⟩
  show _ = vv k ^ (a + 1) • n
  rw [smul_smul, zpow_add_one₀ vv_ne_zero]

theorem sh_add_le (a : ℤ) (m : ℕ) (N : Submodule k⟦X⟧ V) : sh (a + m) N ≤ sh a N := by
  induction m with
  | zero => simp
  | succ m ih =>
    refine le_trans ?_ ih
    rw [Nat.cast_succ, ← add_assoc]; exact sh_succ_le _ _

theorem nab_eq (g : V →ₗ[k] V) (x : V) : nab g x = (vv k)⁻¹ • (g x - x) := rfl

theorem nab_mem {g : V →ₗ[k] V} {N : Submodule k⟦X⟧ V} (hC : CondC g N) {n : V} (hn : n ∈ N) :
    nab g n ∈ N := by
  obtain ⟨n', hn', h⟩ := mem_sh_iff.mp (hC n hn)
  rw [nab_eq, ← h, smul_smul, zpow_one, inv_mul_cancel₀ vv_ne_zero, one_smul]; exact hn'

theorem shift_identity {K W : Type} [Field K] [AddCommGroup W] [Module K W] {v : K} (hv : v ≠ 0)
    (u b c : K) (n t : W) :
    v⁻¹ • ((u * (1 - b * v + c * v ^ 2)) • (n + v • t) - u • n) =
      u • (t - b • n + v • (c • (n + v • t) - b • t)) := by
  match_scalars <;> field_simp <;> ring

theorem nab_shift {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hC : CondC g N) (b : ℤ) {n : V} (hn : n ∈ N) :
    ∃ n' ∈ N, nab g (vv k ^ b • n) = vv k ^ b • (nab g n - (b : k) • n + vv k • n') := by
  obtain ⟨c, hc⟩ := gam_zpow R b
  have hv : vv k ≠ 0 := vv_ne_zero
  have hgn : g n = n + vv k • nab g n := by
    rw [nab_eq, smul_smul, mul_inv_cancel₀ hv, one_smul]; abel
  have hm := nab_mem hC hn
  refine ⟨c • (n + vv k • nab g n) - b • nab g n,
    N.sub_mem (N.smul_mem _ (N.add_mem hn (v_smul_mem hm))) (zsmul_mem hm _), ?_⟩
  rw [nab_eq g (vv k ^ b • n), hg, hc, hgn, Int.cast_smul_eq_zsmul, ← coe_smul_eq,
    ← Int.cast_smul_eq_zsmul k⸨X⸩ b n, ← Int.cast_smul_eq_zsmul k⸨X⸩ b (nab g n)]
  exact shift_identity hv _ _ _ _ _

theorem nab_mem_sh {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hC : CondC g N) (b : ℤ) {x : V} (hx : x ∈ sh b N) : nab g x ∈ sh b N := by
  obtain ⟨n, hn, rfl⟩ := mem_sh_iff.mp hx
  obtain ⟨n', hn', h⟩ := nab_shift R hg hC b hn
  refine mem_sh_iff.mpr ⟨_, ?_, h.symm⟩
  exact N.add_mem (N.sub_mem (nab_mem hC hn) ((N.restrictScalars k).smul_mem _ hn)) (v_smul_mem hn')

theorem finite_quot {N : Submodule k⟦X⟧ V} (hN : N.FG) :
    FiniteDimensional k ((N.restrictScalars k).map ((sh 1 N).restrictScalars k).mkQ) := by
  obtain ⟨s, hs⟩ := hN
  set Q := (sh 1 N).restrictScalars k with hQ
  have hle : (N.restrictScalars k).map Q.mkQ ≤ Submodule.span k (Q.mkQ '' (s : Set V)) := by
    rintro _ ⟨n, hn, rfl⟩
    have hn' : n ∈ Submodule.span k⟦X⟧ (s : Set V) := by rw [hs]; exact hn
    clear hn
    induction hn' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul c x hx ih =>
      have hxN : x ∈ N := by rw [← hs]; exact hx
      obtain ⟨c', hc'⟩ : (PowerSeries.X : k⟦X⟧) ∣ c - algebraMap k k⟦X⟧ (PowerSeries.constantCoeff c) := by
        rw [PowerSeries.X_dvd_iff]; simp
      have : Q.mkQ (c • x) = PowerSeries.constantCoeff c • Q.mkQ x := by
        rw [← map_smul]
        refine (Submodule.Quotient.eq _).mpr ?_
        refine mem_sh_iff.mpr ⟨c' • x, N.smul_mem _ hxN, ?_⟩
        rw [zpow_one, vv_coe, coe_smul_eq, smul_smul, ← hc', sub_smul, algebraMap_smul]
      rw [this]; exact Submodule.smul_mem _ _ ih
  haveI : FiniteDimensional k (Submodule.span k (Q.mkQ '' (s : Set V))) :=
    FiniteDimensional.span_of_finite k (s.finite_toSet.image _)
  exact Submodule.finiteDimensional_of_le hle

theorem graded {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (b : ℤ) (h : sen g N (b : k) = 0) :
    (∀ x ∈ sh b N, nab g x ∈ sh (b + 1) N → x ∈ sh (b + 1) N) ∧
      ∀ y ∈ sh b N, ∃ x ∈ sh b N, y - nab g x ∈ sh (b + 1) N := by
  haveI := finite_quot hN
  obtain ⟨h1, h2⟩ := bij_of_gmult_zero (nab g) (N.restrictScalars k) ((sh 1 N).restrictScalars k)
    (fun p hp => nab_mem hC hp) (fun p hp => nab_mem_sh R hg hC 1 hp) (b : k) h
  have hv : vv k ≠ 0 := vv_ne_zero
  constructor
  · intro x hx hx'
    obtain ⟨n, hn, rfl⟩ := mem_sh_iff.mp hx
    obtain ⟨n', hn', e⟩ := nab_shift R hg hC b hn
    obtain ⟨t, ht, e'⟩ := mem_sh_iff.mp hx'
    rw [e, zpow_add_one₀ hv, mul_smul] at e'
    have e2 := smul_right_injective V (zpow_ne_zero b hv) e'
    have : n ∈ sh 1 N := h1 n hn (mem_sh_iff.mpr ⟨t - n', N.sub_mem ht hn', by
      rw [zpow_one, smul_sub, e2]; abel⟩)
    obtain ⟨r, hr, rfl⟩ := mem_sh_iff.mp this
    exact mem_sh_iff.mpr ⟨r, hr, by rw [zpow_add₀ hv, mul_smul]⟩
  · intro y hy
    obtain ⟨n, hn, rfl⟩ := mem_sh_iff.mp hy
    obtain ⟨p, hp, hq⟩ := h2 n hn
    obtain ⟨r, hr, e'⟩ := mem_sh_iff.mp hq
    obtain ⟨n', hn', e⟩ := nab_shift R hg hC b hp
    refine ⟨vv k ^ b • p, mem_sh_iff.mpr ⟨p, hp, rfl⟩, mem_sh_iff.mpr ⟨r - n', N.sub_mem hr hn', ?_⟩⟩
    rw [zpow_one] at e'
    rw [e, zpow_add_one₀ hv, mul_smul, ← smul_sub, smul_sub (vv k), e']
    congr 1; abel

theorem nab_bijective_window : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (m : ℕ), (∀ j : ℕ, j < m → sen g N ((a + j : ℤ) : k) = 0) → (∀ x ∈ sh a N, nab g x ∈ sh (a + m) N → x ∈ sh (a + m) N) ∧ ∀ y ∈ sh a N, ∃ x ∈ sh a N, y - nab g x ∈ sh (a + m) N := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hN hC a m
  induction m with
  | zero =>
    intro _
    refine ⟨fun x hx _ => by simpa using hx, fun y hy => ⟨0, Submodule.zero_mem _, by simpa using hy⟩⟩
  | succ m ih =>
    intro h
    obtain ⟨i1, i2⟩ := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    obtain ⟨g1, g2⟩ := graded R hg hN.1 hC (a + m) (h m (Nat.lt_succ_self m))
    rw [Nat.cast_succ, ← add_assoc]
    refine ⟨fun x hx hx' => g1 x (i1 x hx (sh_succ_le _ _ hx')) hx', fun y hy => ?_⟩
    obtain ⟨x, hx, hx'⟩ := i2 y hy
    obtain ⟨z, hz, hz'⟩ := g2 _ hx'
    refine ⟨x + z, Submodule.add_mem _ hx (sh_add_le a m N hz), ?_⟩
    rw [map_add (f := _), ← sub_sub]; exact hz'

end GlobalTheory.PhiGam.Window
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
open Matrix

noncomputable section

namespace GlobalTheory.JR.Step

section Alg
variable {r : ℕ} {k : Type} [CommRing k]

def eL (r : ℕ) (k : Type) [CommRing k] : Fin (r + 1) → k := Pi.single (Fin.last r) 1

def blocks (A : Matrix (Fin (r + 1)) (Fin (r + 1)) k) : Gl r k :=
  (A.submatrix Fin.castSucc Fin.castSucc, fun i => A (Fin.castSucc i) (Fin.last r),
    fun j => A (Fin.last r) (Fin.castSucc j), A (Fin.last r) (Fin.last r))

def lift (Z : Gl r k) (μ l : k) : Gl (r + 1) k := (full Z, μ • eL r k, eL r k, l)

def embHom (r : ℕ) (k : Type) [CommRing k] :
    Matrix (Fin r) (Fin r) k →* Matrix (Fin (r + 1)) (Fin (r + 1)) k where
  toFun g := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 1)
  map_one' := by
    rw [Matrix.fromBlocks_one]
    exact Matrix.submatrix_one_equiv _
  map_mul' g h := by
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

def emb (r : ℕ) (k : Type) [CommRing k] : GL (Fin r) k →* GL (Fin (r + 1)) k := Units.map (embHom r k)

def glMap {k' : Type} [CommRing k'] (φ : k →+* k') (Y : Gl r k) : Gl r k' :=
  (Y.1.map φ, fun i => φ (Y.2.1 i), fun i => φ (Y.2.2.1 i), φ Y.2.2.2)

end Alg

section Herm
variable {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]

theorem full_toGl_isSelfAdjoint (X : Hn r F E) (hl : star (algebraMap F E X.2.2) = algebraMap F E X.2.2) :
    IsSelfAdjoint (full X.toGl) := by
  have hA : X.1.1ᴴ = X.1.1 := X.1.2
  unfold IsSelfAdjoint full Hn.toGl
  simp only [Matrix.star_eq_conjTranspose, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.fromBlocks_conjTranspose, hA]
  congr 1
  congr 1
  all_goals (ext i j; simp [hl])

end Herm

section Unr
variable {r : ℕ} {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] [Unram F E]

def liftH (X : Hn r F E) (ν : E) (l : F) : Hn (r + 1) F E :=
  (⟨full X.toGl, full_toGl_isSelfAdjoint X (Unram.star_fix _)⟩, ν • eL r E, l)

def uEmb (r : ℕ) (E : Type) [Field E] [StarRing E] :
    Matrix.unitaryGroup (Fin r) E →* Matrix.unitaryGroup (Fin (r + 1)) E where
  toFun g := ⟨embHom r E g.1, by
    have hs : star (embHom r E g.1) = embHom r E (star g.1) := by
      simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.star_eq_conjTranspose, Matrix.reindex_apply,
        Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
        Matrix.conjTranspose_one]
    rw [Matrix.mem_unitaryGroup_iff, hs, ← map_mul, Matrix.mem_unitaryGroup_iff.mp g.2, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ _ _)

end Unr

end GlobalTheory.JR.Step
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KappaSumZeroAndStableSumMulZeroOfNotIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KappaSumZeroAndStableSumMulZeroOfNotIntegral
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem _root_.GlobalTheory.UnitLemma.isIntegral_of_isLat_stable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A]
    [Algebra E A] (L : Submodule O A) (hL : _root_.GlobalTheory.UnitLemma.IsLat O E L) (g : A) (hg : ∀ y ∈ L, g * y ∈ L) :
    IsIntegral O g := by
  obtain ⟨hfg, hspan⟩ := hL
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hfg
  let f : Module.End O L := (LinearMap.mulLeft O g).restrict hg
  have hpow : ∀ (n : ℕ) (y : L), ((f ^ n) y : A) = g ^ n * y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih => intro y; rw [pow_succ', Module.End.mul_apply, pow_succ', mul_assoc, ← ih]; rfl
  have hact : ∀ (q : O[X]) (y : L), ((aeval f q) y : A) = aeval g q * y := by
    intro q y
    induction q using Polynomial.induction_on' with
    | add p q hp' hq' => simp [add_mul, hp', hq']
    | monomial n c => simp [aeval_monomial, hpow, Algebra.smul_def, mul_assoc]
  obtain ⟨p, hmon, hp⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  have hzero : ∀ y ∈ Submodule.span E (L : Set A), aeval g p * y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => rw [← hact p ⟨x, hx⟩, hp]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul e x _ hx => rw [mul_smul_comm, hx, smul_zero]
  refine ⟨p, hmon, ?_⟩
  have h1 := hzero 1 (hspan ▸ Submodule.mem_top)
  rw [mul_one] at h1
  rwa [← aeval_def]

private lemma latticeCount_eq_zero_of_not_isIntegral_lemma (K : _root_.GlobalTheory.UnitLemma.UQ)
    (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (hB : ¬ IsIntegral K.O B.g) (k : B.Cl) :
    B.N k.rep = 0 := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.N _root_.GlobalTheory.UnitLemma.orbSum _root_.GlobalTheory.UnitLemma.InvAlg.X
  refine finsum_eq_zero_of_forall_eq_zero fun o => absurd ?_ hB
  obtain ⟨hfull, hstab, -⟩ := (Quot.out o).2
  exact _root_.GlobalTheory.UnitLemma.isIntegral_of_isLat_stable _ hfull _ hstab

private lemma stableLatticeCountSum_eq_zero_of_not_isIntegral_lemma_2 (K : _root_.GlobalTheory.UnitLemma.UQ)
    (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (hB : ¬ IsIntegral K.O B.g) :
    B.stSum = 0 := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.stSum
  exact finsum_eq_zero_of_forall_eq_zero fun k => latticeCount_eq_zero_of_not_isIntegral_lemma K B hB k

theorem _root_.GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral :
    ∀ (K : _root_.GlobalTheory.UnitLemma.UQ) (B₁ B₂ : _root_.GlobalTheory.UnitLemma.InvAlg K),
      ¬ (IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g) →
      _root_.GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ = 0 ∧
        B₁.stSum * B₂.stSum = 0 := by
  intro K B₁ B₂ h
  have hprod : ¬ IsIntegral K.O (B₁.prod B₂).g := by
    intro hi
    have hi' : IsIntegral K.O ((B₁.g, B₂.g) : B₁.A × B₂.A) := hi
    apply h
    exact ⟨hi'.map (AlgHom.fst K.O B₁.A B₂.A), hi'.map (AlgHom.snd K.O B₁.A B₂.A)⟩
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.UnitLemma.InvAlg.kapSum
    refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
    rw [latticeCount_eq_zero_of_not_isIntegral_lemma K _ hprod k, mul_zero]
  · by_cases h₁ : IsIntegral K.O B₁.g
    · rw [stableLatticeCountSum_eq_zero_of_not_isIntegral_lemma_2 K B₂ fun h₂ => h ⟨h₁, h₂⟩, mul_zero]
    · rw [stableLatticeCountSum_eq_zero_of_not_isIntegral_lemma_2 K B₁ h₁, zero_mul]

end GlobalTheory.UnitLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KappaSumZeroAndStableSumMulZeroOfNotIntegralStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappaSum_zero_and_stableSum_mul_zero_of_not_integral : ∀ (K : UQ) (B₁ B₂ : InvAlg K), ¬ (IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g) → InvAlg.kapSum B₁ B₂ = 0 ∧ B₁.stSum * B₂.stSum = 0 := by
  first | exact @GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral | exact GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral | (intros; apply GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorKrylovDet
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorKrylovDet
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.TransferFactor

variable {k : Type} [CommRing k] {r : ℕ}

theorem full_cc (Y : Gl r k) (a b : Fin r) : full Y (Fin.castSucc a) (Fin.castSucc b) = Y.1 a b := by
  simp [full, finSumFinEquiv_symm_apply_castSucc]

theorem full_lc (Y : Gl r k) (b : Fin r) : full Y (Fin.last r) (Fin.castSucc b) = Y.2.2.1 b := by
  simp [full, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

def vrow (Y : Gl r k) (i : ℕ) : Fin (r + 1) → k := Pi.single (Fin.last r) (1 : k) ᵥ* (full Y ^ i)

theorem vrow_succ_cast (Y : Gl r k) (i : ℕ) (j : Fin r) :
    vrow Y (i + 1) (Fin.castSucc j) =
      ((fun l => vrow Y i (Fin.castSucc l)) ᵥ* Y.1) j + vrow Y i (Fin.last r) * Y.2.2.1 j := by
  simp only [vrow, pow_succ, ← Matrix.vecMul_vecMul]
  rw [Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc]
  simp only [full_cc, full_lc]
  rfl

theorem vrow_poly (Y : Gl r k) (i : ℕ) : ∃ p : Polynomial k, p.coeff i = 1 ∧ (∀ N, i < N → p.coeff N = 0) ∧
    (fun l => vrow Y (i + 1) (Fin.castSucc l)) = Y.2.2.1 ᵥ* Polynomial.aeval Y.1 p := by
  induction i with
  | zero =>
    refine ⟨1, by simp, fun N hN => ?_, ?_⟩
    · rw [Polynomial.coeff_one]; simp; omega
    · funext l
      rw [vrow_succ_cast]
      simp [vrow, Pi.single_apply, Fin.castSucc_ne_last, Matrix.vecMul, dotProduct, Matrix.one_apply_ne' (Fin.castSucc_ne_last _), Matrix.one_apply]
  | succ i ih =>
    obtain ⟨p, h1, h2, h3⟩ := ih
    refine ⟨p * Polynomial.X + Polynomial.C (vrow Y (i + 1) (Fin.last r)), ?_, fun N hN => ?_, ?_⟩
    · rw [Polynomial.coeff_add, Polynomial.coeff_mul_X, Polynomial.coeff_C, h1]; simp
    · rw [Polynomial.coeff_add, Polynomial.coeff_C]
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      rw [Polynomial.coeff_mul_X, h2 M (by omega)]; simp
    · funext l
      rw [vrow_succ_cast, h3]
      simp [map_add (f := _), Polynomial.aeval_X, Polynomial.aeval_C, Matrix.vecMul_add, Matrix.vecMul_vecMul,
        Algebra.algebraMap_eq_smul_one, Matrix.vecMul_smul, mul_comm]

theorem lastDet_eq (Y : Gl r k) : lastDet Y = (-1) ^ r * (Cm Y).det := by
  classical
  choose p hp1 hp2 hp3 using vrow_poly Y
  let T : Matrix (Fin r) (Fin r) k := Matrix.of fun i j => (p i).coeff j
  have hT : T.det = 1 := by
    rw [Matrix.det_of_lowerTriangular T (fun i j hij => hp2 i j hij)]
    exact Finset.prod_eq_one fun i _ => hp1 i
  have hmin : (Matrix.of fun (i j : Fin r) => vrow Y ((i : ℕ) + 1) (Fin.castSucc j)) = T * Cm Y := by
    ext i j
    have hd : (p i).natDegree < r := lt_of_le_of_lt
      (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (hp2 i)) i.2
    rw [Matrix.of_apply, congrFun (hp3 i) j, Polynomial.aeval_eq_sum_range' hd, Finset.sum_range
      (fun l => (p i).coeff l • Y.1 ^ l), Matrix.vecMul_sum]
    simp [Matrix.mul_apply, T, Cm, Matrix.vecMul_smul, Finset.sum_apply, mul_comm]
  unfold lastDet
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_castSucc]
  have hz : ∀ j : Fin r, (Matrix.of fun (i j : Fin (r + 1)) =>
      (Pi.single (Fin.last r) (1 : k) ᵥ* (full Y ^ (i : ℕ))) j) 0 (Fin.castSucc j) = 0 := by
    intro j; simp [Pi.single_apply, Fin.castSucc_ne_last, Matrix.one_apply_ne' (Fin.castSucc_ne_last _)]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  rw [show (Matrix.of fun (i j : Fin (r + 1)) =>
      (Pi.single (Fin.last r) (1 : k) ᵥ* (full Y ^ (i : ℕ))) j) 0 (Fin.last r) = 1 by simp]
  rw [Fin.succAbove_last]
  have hs : ((Matrix.of fun (i j : Fin (r + 1)) =>
      (Pi.single (Fin.last r) (1 : k) ᵥ* (full Y ^ (i : ℕ))) j).submatrix Fin.succ Fin.castSucc) =
      Matrix.of fun (i j : Fin r) => vrow Y ((i : ℕ) + 1) (Fin.castSucc j) := by
    ext i j; simp [vrow]
  rw [hs, hmin, Matrix.det_mul, hT, Fin.val_last]; ring

theorem Cm_act (g : GL (Fin r) k) (Y : Gl r k) :
    Cm (act g Y) = Cm Y * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  ext i j
  simp only [Cm, act, Matrix.of_apply, Units.conj_pow, Matrix.mul_apply]
  rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_vecMul _ _ (g : Matrix (Fin r) (Fin r) k)]
  rw [show ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * (g : Matrix (Fin r) (Fin r) k) = 1 from
    Units.inv_mul g, Matrix.vecMul_one]
  simp [Matrix.vecMul, dotProduct, Cm]

end GlobalTheory.JR.TransferFactor

theorem GlobalTheory.JR.transfer_factor_lemma : ∀ (k : Type) [CommRing k] (r : ℕ), (∀ Y : Gl r k, lastDet Y = (-1) ^ r * (Cm Y).det) ∧ ∀ (g : GL (Fin r) k) (Y : Gl r k), Cm (act g Y) = Cm Y * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) :=
  fun _ _ _ => ⟨GlobalTheory.JR.TransferFactor.lastDet_eq, GlobalTheory.JR.TransferFactor.Cm_act⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorKrylovDetStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det : ∀ (k : Type) [CommRing k] (r : ℕ), (∀ Y : Gl r k, lastDet Y = (-1) ^ r * (Cm Y).det) ∧ ∀ (g : GL (Fin r) k) (Y : Gl r k), Cm (act g Y) = Cm Y * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  first | exact @GlobalTheory.JR.transfer_factor_lemma | exact GlobalTheory.JR.transfer_factor_lemma | (intros; apply GlobalTheory.JR.transfer_factor_lemma <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowTEqRowS
noncomputable section

namespace GlobalTheory.PMonE

open Finset

variable {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

def rowS {h : ℕ} (ϖ : F) (lam : Fin h → F) (L U : ℕ) (x : Fin h → F) (r : Fin h) : F :=
  ∑ j, ∑ n ∈ Icc (-(L : ℤ)) U, term p ϖ lam x r j n

def winPt {h : ℕ} (π : Fin h → F) (L : ℕ) (z : Fin h → F) : Fin h → F :=
  fun j => π j * z j ^ (p ^ h) ^ (L - 1)

def coefB {h : ℕ} (ϖ : F) (lam π : Fin h → F) (L U m : ℕ) : Matrix (Fin h) (Fin h) F :=
  Matrix.of fun r j => if m ≤ L + U then
    (term p ϖ lam π r j ((m : ℤ) - L) / (lam r * π r ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) else 0

theorem rowT_eq_rowS {h : ℕ} (ϖ : F) (lam : Fin h → F) (K : ℕ) (x : Fin h → F) (r : Fin h) :
    rowT p ϖ lam K x r = rowS p ϖ lam K K x r := rfl

end GlobalTheory.PMonE
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgEquivXAddC
noncomputable section

open PowerSeries GlobalTheory.NB.LT

namespace GlobalTheory.NB.LT

open scoped PowerSeries.WithPiTopology in
theorem exists_algHom_X_add_C {O : Type} [CommRing O] (I : Ideal O) [h : IsAdicComplete I O]
    (c : O) (hc : c ∈ I) : ∃ t : O⟦X⟧ →ₐ[O] O⟦X⟧, t X = X + C c := by
  let : WithIdeal O := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨h1, h2⟩ := hI.isAdicComplete_iff.mp h
  have ha : PowerSeries.HasEval c := WithIdeal.isTopologicallyNilpotent_of_mem hc
  have hC : PowerSeries.HasEval (C c : O⟦X⟧) :=
    ha.map (φ := (C : O →+* O⟦X⟧)) PowerSeries.WithPiTopology.continuous_C
  have : IsLinearTopology O⟦X⟧ O⟦X⟧ :=
    inferInstance
  have hX : PowerSeries.HasEval (X + C c : O⟦X⟧) := PowerSeries.HasEval.X.add hC
  have : ContinuousSMul O O⟦X⟧ := ⟨by
    have : (fun p : O × O⟦X⟧ => p.1 • p.2) = fun p => C p.1 * p.2 := by
      funext p; rw [smul_eq_C_mul]
    rw [this]
    exact (PowerSeries.WithPiTopology.continuous_C.comp continuous_fst).mul continuous_snd⟩
  refine ⟨PowerSeries.aeval hX, ?_⟩
  rw [PowerSeries.coe_aeval, PowerSeries.eval₂_X]

theorem exists_algEquiv_X_add_C : ∀ {O : Type} [CommRing O] (I : Ideal O) [IsAdicComplete I O] (c : O), c ∈ I → ∃ lev : O⟦X⟧ ≃ₐ[O] O⟦X⟧, lev X = X + C c := by
  intro O _ I _ c hc
  obtain ⟨s, hs⟩ := exists_algHom_X_add_C I c hc
  obtain ⟨t, ht⟩ := exists_algHom_X_add_C I (-c) (neg_mem hc)
  have hC : ∀ (u : O⟦X⟧ →ₐ[O] O⟦X⟧) (a : O), u (C a) = C a := fun u a => u.commutes a
  have h1 : (s.comp t) X = X := by
    rw [AlgHom.comp_apply, ht, map_add (f := _), hs, hC, map_neg]; ring
  have h2 : (t.comp s) X = X := by
    rw [AlgHom.comp_apply, hs, map_add (f := _), ht, hC, map_neg]; ring
  exact ⟨AlgEquiv.ofAlgHom s t (algHom_ext_X _ _ h1 (by rw [h1])) (algHom_ext_X _ _ h2 (by rw [h2])), hs⟩

end GlobalTheory.NB.LT
end
end
