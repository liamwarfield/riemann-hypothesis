module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardLatticeQuotIdeal
open NumberField IsDedekindDomain Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MatrixLatticeIndex

theorem card_matIn (D : D7) (a d : ℕ) (A B : Submodule (𝓞 D.host.E) D.host.E) :
    Nat.card (matIn D a d A ⧸ (matIn D a d B).addSubgroupOf (matIn D a d A)) =
      (B.toAddSubgroup.relIndex A.toAddSubgroup) ^ (a * d) := by
  let Q := A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup
  let f : matIn D a d A →+ (Fin d → Fin a → Q) :=
    { toFun := fun z i j => QuotientAddGroup.mk (⟨z.1 i j, z.2 i j⟩ : A.toAddSubgroup)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    intro y
    refine ⟨⟨fun i j => ((y i j).out : A.toAddSubgroup), fun i j => (y i j).out.2⟩, ?_⟩
    funext i j
    exact QuotientAddGroup.out_eq' (y i j)
  have hker : f.ker = (matIn D a d B).addSubgroupOf (matIn D a d A) := by
    ext z
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h i j
      exact (QuotientAddGroup.eq_zero_iff _).1 (congrFun (congrFun h i) j)
    · intro h
      funext i j
      exact (QuotientAddGroup.eq_zero_iff _).2 (h i j)
  rw [← hker, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv,
    Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a), Nat.card_eq_fintype_card (α := Fin d),
    Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  rfl

theorem relIndex_smul {K : Type} [Field K] [NumberField K]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0) (q : Ideal (𝓞 K)) (hq : q ≠ ⊥) :
    (q • (J : Submodule (𝓞 K) K)).toAddSubgroup.relIndex (J : Submodule (𝓞 K) K).toAddSubgroup =
      Ideal.absNorm q := by
  have hq' : (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hq
  have hle : (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J ≤ J := by
    calc (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J ≤ 1 * J :=
          mul_le_mul' FractionalIdeal.coeIdeal_le_one le_rfl
      _ = J := one_mul J
  have h := Formalism.L2.LamCM.Dx.absNorm_eq_relIndex_mul J _ (mul_ne_zero hq' hJ) hle
  have he : (((q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) = q • (J : Submodule (𝓞 K) K) := by
    apply le_antisymm
    · rw [FractionalIdeal.coe_mul]
      refine Submodule.mul_le.2 fun x hx y hy => ?_
      obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem_smul hb hy
    · refine Submodule.smul_le.2 fun b hb y hy => ?_
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hb) hy
  rw [he, map_mul, FractionalIdeal.coeIdeal_absNorm] at h
  have h0 : FractionalIdeal.absNorm J ≠ 0 := fun h' => hJ (FractionalIdeal.absNorm_eq_zero_iff.1 h')
  exact_mod_cast (mul_right_cancel₀ h0 h).symm


open GlobalTheory.NormSum.MovedLattice in
theorem coefLat_eq (D : D7) (cc : Ideal (𝓞 D.host.K)) :
    coefLat D cc = ((ext D cc * D.host.AA0 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨c, hc, m, hm, rfl⟩
    exact FractionalIdeal.mul_mem_mul (mem_ext D hc) hm
  · rw [FractionalIdeal.coe_mul]
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
    clear hx
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨c, hc, rfl⟩ := hb
      exact Submodule.subset_span ⟨c, hc, y, hy, rfl⟩
    | zero => rw [map_zero, zero_mul]; exact zero_mem _
    | add b b' _ _ hb hb' => rw [map_add (f := _), add_mul]; exact add_mem hb hb'
    | smul r b _ hb =>
      rw [smul_eq_mul, map_mul, mul_assoc, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r hb

end GlobalTheory.MatrixLatticeIndex
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexStandardInfSkewThetaLatticeEqAbsNormPow
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.SkewIndex

open GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs GlobalTheory.ThetaLatticePoints GlobalTheory.MatrixLatticeIndex GlobalTheory.NormSum.MovedLattice

theorem one_inf_div {E : Type} [Field E] [NumberField E] (𝔪 𝔫 : Ideal (𝓞 E)) (h𝔫 : 𝔫 ≠ ⊥)
    (hc : IsCoprime 𝔪 𝔫) :
    (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ⊓ ((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) / 𝔫) = 𝔪 := by
  have h𝔫' : (𝔫 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔫
  apply le_antisymm
  · obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 (inf_le_left : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ⊓ _ ≤ 1)
    rw [← hI]
    have h2 : (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≤ (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) / 𝔫 := hI ▸ inf_le_right
    rw [FractionalIdeal.le_div_iff_mul_le h𝔫', ← FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_le_coeIdeal] at h2
    rw [FractionalIdeal.coeIdeal_le_coeIdeal]
    have hs : 𝔪 ⊔ 𝔫 = ⊤ := Ideal.isCoprime_iff_sup_eq.1 hc
    calc I = I * (𝔪 ⊔ 𝔫) := by rw [hs, Ideal.mul_top]
      _ = I * 𝔪 ⊔ I * 𝔫 := Ideal.mul_sup _ _ _
      _ ≤ 𝔪 := sup_le (by first | exact Ideal.mul_le_right | exact Ideal.mul_le_left) h2
  · refine le_inf FractionalIdeal.coeIdeal_le_one ?_
    rw [FractionalIdeal.le_div_iff_mul_le h𝔫']
    calc (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * 𝔫 ≤ 𝔪 * 1 := mul_le_mul' le_rfl FractionalIdeal.coeIdeal_le_one
      _ = 𝔪 := mul_one _

theorem mul_inf {E : Type} [Field E] [NumberField E] (A X Y : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hA : A ≠ 0) : A * (X ⊓ Y) = A * X ⊓ A * Y := by
  apply le_antisymm
  · exact le_inf (mul_le_mul' le_rfl inf_le_left) (mul_le_mul' le_rfl inf_le_right)
  · have e : A * X ⊓ A * Y = A * (A⁻¹ * (A * X ⊓ A * Y)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hA, one_mul]
    rw [e]
    refine mul_le_mul' le_rfl (le_inf ?_ ?_)
    · calc A⁻¹ * (A * X ⊓ A * Y) ≤ A⁻¹ * (A * X) := mul_le_mul' le_rfl inf_le_left
        _ = X := by rw [← mul_assoc, inv_mul_cancel₀ hA, one_mul]
    · calc A⁻¹ * (A * X ⊓ A * Y) ≤ A⁻¹ * (A * Y) := mul_le_mul' le_rfl inf_le_right
        _ = Y := by rw [← mul_assoc, inv_mul_cancel₀ hA, one_mul]

variable (D : D7)

def skewEnt (𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) /
    ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)

theorem mem_skewLat_iff (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) (x : Fin N → D.host.E) :
    x ∈ skewLat D 𝔪 N ↔ ∀ i, x i ∈ (skewEnt D 𝔪 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp only [skewLat, skewEnt, Submodule.mem_pi, Set.mem_univ, true_implies]

theorem mem_YYl_skew_iff (𝔪 : Ideal (𝓞 D.host.E)) (a d : ℕ) (x : Matrix (Fin d) (Fin a) D.host.E) :
    x ∈ YYl D (stdL D a) (skewLat D 𝔪 d) ↔
      ∀ i j, x i j ∈ ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨c, hc, A, hA, rfl⟩ := hB
      have hAe : ∀ i j, A i j ∈ (skewEnt D 𝔪 : Submodule (𝓞 D.host.E) D.host.E) := by
        induction hA using Submodule.span_induction with
        | mem A hA =>
          intro i j
          have hj : (Pi.single j (1 : D.host.E) : Fin a → D.host.E) ∈ stdL D a := by
            simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies]
            intro k
            by_cases hk : k = j
            · subst hk; simp [Submodule.one_eq_range]
            · simp [Pi.single_apply, hk]
          have h := (mem_skewLat_iff D 𝔪 d _).1 (hA _ hj) i
          simpa [Matrix.mulVec_single] using h
        | zero => intro i j; simp
        | add A B _ _ h1 h2 => intro i j; simpa using add_mem (h1 i j) (h2 i j)
        | smul r A _ h => intro i j; simpa using Submodule.smul_mem _ r (h i j)
      intro i j
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact FractionalIdeal.mul_mem_mul hc (hAe i j)
    | zero => intro i j; simp
    | add A B _ _ h1 h2 => intro i j; simpa using add_mem (h1 i j) (h2 i j)
    | smul r A _ h => intro i j; simpa using Submodule.smul_mem _ r (h i j)
  · intro hx
    rw [Matrix.matrix_eq_sum_single x]
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    have hij := hx i j
    rw [FractionalIdeal.coe_mul] at hij
    refine Submodule.mul_induction_on (C := fun r => Matrix.single i j r ∈ YYl D (stdL D a) (skewLat D 𝔪 d)) hij ?_ ?_
    · intro m hm n hn
      refine Submodule.subset_span ⟨m, hm, Matrix.single i j n, Submodule.subset_span fun v hv => ?_, ?_⟩
      · refine (mem_skewLat_iff D 𝔪 d _).2 fun k => ?_
        have hvj : v j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
          simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hv
          exact hv j
        obtain ⟨o, ho⟩ := Submodule.mem_one.1 hvj
        by_cases hk : k = i
        · subst hk
          simp only [Matrix.mulVec, dotProduct, Matrix.single_apply, true_and]
          rw [Finset.sum_eq_single j (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
          simp only [if_true]
          rw [← ho, mul_comm, ← Algebra.smul_def]
          exact Submodule.smul_mem _ o hn
        · have hk' : i ≠ k := Ne.symm hk
          simp [Matrix.mulVec, dotProduct, Matrix.single_apply, hk']
      · rw [Matrix.smul_single, smul_eq_mul]
    · intro x y hx hy
      simpa [Matrix.single_add] using add_mem hx hy

theorem La_skew_eq_map (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) (a d : ℕ) :
    La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) =
      (matIn D a d ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E)).map (ptHom D ⊤ δ a d) := by
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, A, hA, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ w).1 hw
    refine ⟨((c : D.host.K) : D.host.E) • A, fun i j => ?_, ptHom_smul D ⊤ δ a d c A⟩
    have := (mem_YYl_skew_iff D 𝔪 a d A).1 hA i j
    rw [Matrix.smul_apply, smul_eq_mul, ← coe_alg, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ this
  · rintro _ ⟨z, hz, rfl⟩
    refine AddSubgroup.subset_closure ⟨δ, (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ δ).2 ⟨1, trivial, by simp⟩, z,
      (mem_YYl_skew_iff D 𝔪 a d z).2 hz, ?_⟩
    rfl

end GlobalTheory.SkewIndex

namespace GlobalTheory.SkewIndex

open GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs GlobalTheory.ThetaLatticePoints GlobalTheory.MatrixLatticeIndex GlobalTheory.NormSum.MovedLattice

theorem index_inter_skew : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ (a d : ℕ), ((La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))).index = Ideal.absNorm 𝔪 ^ (a * d) := by
  intro D δ hC 𝔪 h𝔪 hcop a d
  have hδ : δ ≠ 0 := (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 ⊤ δ hC).2.1
  have hN : Ideal.absNorm (D.host.conj • 𝔪) = Ideal.absNorm 𝔪 := UnusedSlot33.HK.absNorm_smul D.host 𝔪
  have h𝔫 : (D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) ≠ ⊥ := by
    intro h
    apply h𝔪
    rw [← Ideal.absNorm_eq_zero_iff, ← hN, h, Ideal.absNorm_bot]
  have hA := inverseHalfDifferent_ne_zero D
  have h𝔪' : (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 h𝔪
  have h𝔫' : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 h𝔫
  have hJ : D.host.AA0 * skewEnt D 𝔪 ≠ 0 := mul_ne_zero hA (div_ne_zero h𝔪' h𝔫')
  have hcoef : coefLat D ⊤ = (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [coefLat_eq, ext, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]

  have hF : D.host.AA0 ⊓ D.host.AA0 * skewEnt D 𝔪 =
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
        (D.host.AA0 * skewEnt D 𝔪) := by
    rw [show D.host.AA0 ⊓ D.host.AA0 * skewEnt D 𝔪 = D.host.AA0 * 1 ⊓ D.host.AA0 * skewEnt D 𝔪 by rw [mul_one]]
    rw [← mul_inf _ _ _ hA, skewEnt, one_inf_div 𝔪 _ h𝔫 hcop, mul_left_comm, mul_div_cancel₀ _ h𝔫']
  have he : ∀ J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E,
      ((((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * J :
        FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E) =
        (D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) • (J : Submodule (𝓞 D.host.E) D.host.E) := by
    intro J
    apply le_antisymm
    · rw [FractionalIdeal.coe_mul]
      refine Submodule.mul_le.2 fun x hx y hy => ?_
      obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem_smul hb hy
    · refine Submodule.smul_le.2 fun b hb y hy => ?_
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hb) hy
  have hinf : (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup ⊓
      ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup =
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) • ((D.host.AA0 * skewEnt D 𝔪 :
        FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)).toAddSubgroup := by
    rw [← he, ← hF, FractionalIdeal.coe_inf]
    rfl
  show (La0 D (tor0 D ⊤ δ) a d).relIndex (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) = _
  rw [La0_eq_map, La_skew_eq_map, AddSubgroup.relIndex_map_map_of_injective _ _ (ptHom_injective D ⊤ hδ a d)]
  have hc := card_matIn D a d ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    Submodule (𝓞 D.host.E) D.host.E) (coefLat D ⊤)
  rw [hcoef, ← AddSubgroup.inf_relIndex_right, hinf, relIndex_smul _ hJ _ h𝔫, hN] at hc
  rw [show lat0 D ⊤ a d = matIn D a d (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) by rw [lat0, hcoef]]
  exact hc

end GlobalTheory.SkewIndex
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexStandardInfSkewThetaLatticeEqAbsNormPowStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.index_standard_inf_skewThetaLattice_eq_absNorm_pow : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ (a d : ℕ), ((La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))).index = Ideal.absNorm 𝔪 ^ (a * d) := by
  first | exact @GlobalTheory.SkewIndex.index_inter_skew | exact GlobalTheory.SkewIndex.index_inter_skew | (intros; apply GlobalTheory.SkewIndex.index_inter_skew <;> assumption)
end
