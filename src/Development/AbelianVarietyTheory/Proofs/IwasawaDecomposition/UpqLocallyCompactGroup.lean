module

public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import ReciprocityTheory.DualLattices.Imports
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
noncomputable section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.UpqTopology

variable {P Q : ℕ}

theorem jpq_sq : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem left_inv {u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ}
    (h : uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q) : Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q * u = 1 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, h, jpq_sq]

theorem mat_unitary (b : UpqT P Q) : (UpqT.mat b)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat b = Formalism.UG.Jpq P Q := b.2

theorem continuous_mat : Continuous (UpqT.mat (P := P) (Q := Q)) :=
  Units.continuous_val.comp continuous_subtype_val

theorem range_mat : Set.range (UpqT.mat (P := P) (Q := Q)) =
    {u | uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q} := by
  ext u
  constructor
  · rintro ⟨b, rfl⟩
    exact mat_unitary b
  · intro h
    exact ⟨(⟨⟨u, Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q, mul_eq_one_comm.1 (left_inv h), left_inv h⟩, h⟩ :
      Formalism.UG.Upq P Q), rfl⟩

theorem isInducing_mat : IsInducing (UpqT.mat (P := P) (Q := Q)) := by
  let f : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ →
      Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ × (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᵐᵒᵖ :=
    fun g => (g, MulOpposite.op (Formalism.UG.Jpq P Q * gᴴ * Formalism.UG.Jpq P Q))
  have hf : Continuous f :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
  have hcomp : f ∘ UpqT.mat =
      Units.embedProduct _ ∘ (Subtype.val : Formalism.UG.Upq P Q → GL (Fin P ⊕ Fin Q) ℂ) := by
    funext g
    refine Prod.ext rfl (congrArg MulOpposite.op ?_)
    exact (Units.inv_eq_of_mul_eq_one_left (left_inv (mat_unitary g))).symm
  refine IsInducing.of_comp continuous_mat hf ?_
  rw [hcomp]
  exact Units.isEmbedding_embedProduct.isInducing.comp IsInducing.subtypeVal

theorem isClosedEmbedding_mat : IsClosedEmbedding (UpqT.mat (P := P) (Q := Q)) := by
  refine ⟨⟨isInducing_mat, fun _ _ h => Subtype.ext (Units.ext h)⟩, ?_⟩
  rw [range_mat]
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem upq_lcsc : ∀ P Q : ℕ, IsTopologicalGroup (UpqT P Q) ∧ T2Space (UpqT P Q) ∧
    LocallyCompactSpace (UpqT P Q) ∧ SecondCountableTopology (UpqT P Q) ∧ BorelSpace (UpqT P Q) ∧
    Topology.IsClosedEmbedding (UpqT.mat : UpqT P Q → Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := by
  intro P Q
  have : LocallyCompactSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  have : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  exact ⟨inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q)), isClosedEmbedding_mat.isEmbedding.t2Space,
    isClosedEmbedding_mat.locallyCompactSpace, isClosedEmbedding_mat.isEmbedding.secondCountableTopology,
    ⟨rfl⟩, isClosedEmbedding_mat⟩

end GlobalTheory.UpqTopology
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.ThetaD

section general
variable {R : Type} [CommRing R] (I : Ideal R)

theorem factorPow_evalₐ {m n : ℕ} (h : m ≤ n) (y : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n y) = AdicCompletion.evalₐ I m y := by
  induction y using AdicCompletion.induction_on with
  | _ x =>
    simp only [AdicCompletion.evalₐ_mk]
    rw [← AdicCompletion.Ideal.mk_eq_mk I h x]
    rfl

theorem isUnit_evalₐ (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) (n : ℕ) :
    IsUnit (AdicCompletion.evalₐ I n y) := by
  have key : IsUnit (AdicCompletion.evalₐ I (n + 1) y) := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
    rw [← factorPow_evalₐ I (show 1 ≤ n + 1 by omega), ← ha] at hy
    obtain ⟨b, hb⟩ := hy.exists_right_inv
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : a * b - 1 ∈ I ^ 1 := by
      rw [← Ideal.Quotient.eq]
      exact hb
    rw [pow_one] at h1
    have hn : IsNilpotent (Ideal.Quotient.mk (I ^ (n + 1)) (a * b - 1)) :=
      ⟨n + 1, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow h1 _⟩
    have hu := hn.isUnit_add_one
    rw [map_sub, map_one, sub_add_cancel, map_mul] at hu
    rw [← ha]
    exact isUnit_of_mul_isUnit_left hu
  rw [← factorPow_evalₐ I (Nat.le_succ n)]
  exact key.map _

theorem isUnit_of_evalₐ (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) :
    IsUnit y := by
  let f : (n : ℕ) → Localization.Away y →+* R ⧸ I ^ n := fun n =>
    IsLocalization.Away.lift (g := (AdicCompletion.evalₐ I n).toRingHom) y (isUnit_evalₐ I y hy n)
  have hf0 : ∀ n x, f n (algebraMap _ _ x) = AdicCompletion.evalₐ I n x := fun n x =>
    IsLocalization.Away.lift_eq y _ x
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m := by
    intro m n hle
    refine IsLocalization.ringHom_ext (Submonoid.powers y) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, hf0, factorPow_evalₐ]
  have e : AdicCompletion.liftRingHom I f hf (algebraMap _ _ y) = y :=
    AdicCompletion.ext_evalₐ fun n => by rw [AdicCompletion.evalₐ_liftRingHom, hf0]
  rw [← e]
  exact (IsLocalization.Away.algebraMap_isUnit y).map _

end general

variable (l : ℕ) [Fact l.Prime]

theorem frob_surj : Function.Surjective (frobenius (ModP (Per.OC l) l) l) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hl : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ_[l]) hl
  have hb1 : b ∈ 𝓞_ℂ_[l] := by
    rw [GlobalTheory.RingBasics.mem_OC]
    have := (GlobalTheory.RingBasics.mem_OC _).1 a.2
    rw [← hb, norm_pow] at this
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hl.ne').1 this
  refine ⟨Ideal.Quotient.mk _ ⟨b, hb1⟩, ?_⟩
  rw [frobenius_def, ← map_pow]
  exact congrArg _ (Subtype.ext hb)

theorem θ_surj : Function.Surjective (Per.θ l) := surjective_fontaineTheta (frob_surj l)

theorem fontaineTheta_algebraMap₂ (a : Per.Ainf l) : Per.θP l (algebraMap _ _ a) = (Per.θ l a : ℂ_[l]) :=
  GlobalTheory.RingIface.fontaineTheta_algebraMap l a

theorem fontaineTheta_eq_zero (a : Per.AinfP l) : Per.θP l a = 0 ↔ a ∈ Per.kerP l := by
  refine ⟨fun h => ?_, fun h => GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l a (by rwa [pow_one])⟩
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (Submonoid.powers (l : Per.Ainf l)) a
  have hs := IsLocalization.map_units (Per.AinfP l) s
  have h1 := congrArg (Per.θP l) hx
  rw [map_mul, h, zero_mul, fontaineTheta_algebraMap₂] at h1
  have h2 : Per.θ l x = 0 := Subtype.ext h1.symm
  have h3 := GlobalTheory.RingIface.alg_mem_kerP l h2
  have h4 : a * algebraMap (Per.Ainf l) (Per.AinfP l) (s : Per.Ainf l) ∈ Per.kerP l := by
    rw [hx]; exact h3
  exact (Ideal.mul_unit_mem_iff_mem _ hs).1 h4

theorem fontaineTheta_surjective' : Function.Surjective (Per.θP l) := by
  intro c
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(l : ℂ_[l]) ^ n * c‖ ≤ 1 := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (l : ℂ_[l])) GlobalTheory.RingBasics.norm_p_lt).mul_const ‖c‖
    rw [zero_mul] at h
    obtain ⟨n, hn⟩ := (h.eventually (ge_mem_nhds one_pos)).exists
    exact ⟨n, by rwa [norm_mul, norm_pow]⟩
  obtain ⟨a, ha⟩ := θ_surj l ⟨_, (GlobalTheory.RingBasics.mem_OC _).2 hn⟩
  obtain ⟨u, hu⟩ := ((GlobalTheory.RingBasics.isUnit_l l).pow n).exists_left_inv
  refine ⟨u * algebraMap _ _ a, ?_⟩
  have h := congrArg (Per.θP l) hu
  rw [map_mul, map_pow, map_natCast, map_one] at h
  rw [map_mul, fontaineTheta_algebraMap₂, ha]
  change _ * (_ * c) = c
  rw [← mul_assoc, h, one_mul]

theorem θP_σ (g : Per.Gq l) (a : Per.AinfP l) :
    Per.θP l (Per.extP (Per.σA g) a) = Per.σC g (Per.θP l a) := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (l : Per.Ainf l))
    (j := (Per.θP l).comp (Per.extP (Per.σA g))) (k := (Per.σC g).comp (Per.θP l))
    (RingHom.ext fun y => ?_)) a
  simp only [RingHom.comp_apply, GlobalTheory.RingBasics.awayMap_algebraMap₂, fontaineTheta_algebraMap₂, GlobalTheory.RingBasics.θ_σA]
  exact GlobalTheory.RingIface.sigO_coe l g _

theorem θD_of_ev (y : Per.BdRp l) (a : Per.AinfP l) (h : Ideal.Quotient.mk _ a = Per.ev l 1 y) :
    Per.θD l y = Per.θP l a := by
  have h1 : y - algebraMap (Per.AinfP l) (Per.BdRp l) a ∈ Per.FilP l 1 := by
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_sub, GlobalTheory.RingIface.ev_alg, h, sub_self]
  have h2 := GlobalTheory.RingIface.thetaD_of_mem_FilP l h1
  rwa [map_sub, GlobalTheory.RingIface.thetaD_alg, sub_eq_zero] at h2

theorem θD_alg (a : Per.AinfP l) : Per.θD l (algebraMap _ _ a) = Per.θP l a :=
  GlobalTheory.RingIface.thetaD_alg l a

end GlobalTheory.MemLoc.ThetaD


open GlobalTheory.MemLoc.ThetaD in
theorem GlobalTheory.MemLoc.thetaD_props : ∀ (l : ℕ) [Fact l.Prime], Function.Surjective (Per.θD l) ∧ (∀ y : Per.BdRp l, Per.θD l y = 0 ↔ y ∈ Per.FilP l 1) ∧ (∀ y : Per.BdRp l, Per.θD l y ≠ 0 → IsUnit y) ∧ (∀ a : Per.Ainf l, Per.θD l (aDp l a) = (Per.θ l a : ℂ_[l])) ∧ ∀ (g : Per.Gq l) (y : Per.BdRp l), Per.θD l (Per.σDp g y) = Per.σC g (Per.θD l y) := by
  intro l _
  refine ⟨fun c => ?_, fun y => ?_, fun y hy => ?_, fun a => ?_, fun g y => ?_⟩
  · obtain ⟨a, rfl⟩ := fontaineTheta_surjective' l c
    exact ⟨_, θD_alg l a⟩
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (Per.ev l 1 y)
    rw [θD_of_ev l y a ha, fontaineTheta_eq_zero, GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, ← ha,
      Ideal.Quotient.eq_zero_iff_mem, pow_one]
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (Per.ev l 1 y)
    rw [θD_of_ev l y a ha] at hy
    obtain ⟨b, hb⟩ := fontaineTheta_surjective' l (Per.θP l a)⁻¹
    have h1 : a * b - 1 ∈ Per.kerP l ^ 1 := by
      rw [pow_one, ← fontaineTheta_eq_zero, map_sub, map_mul, hb, map_one, mul_inv_cancel₀ hy, sub_self]
    have hu : IsUnit (Per.ev l 1 y) := by
      rw [← ha]
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ b) ?_
      rw [← map_mul, ← map_one (Ideal.Quotient.mk (Per.kerP l ^ 1)), Ideal.Quotient.eq]
      exact h1
    obtain ⟨e, -, he⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
    rw [← he] at hu
    have h2 := (isUnit_of_evalₐ (Per.kerP l) (e y) hu).map e.symm
    rwa [RingEquiv.symm_apply_apply] at h2
  · exact (θD_alg l _).trans (fontaineTheta_algebraMap₂ l a)
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (Per.ev l 1 y)
    rw [θD_of_ev l y a ha, ← θP_σ]
    exact θD_of_ev l _ _ (GlobalTheory.RingIface.ev_sigDp l g 1 y a ha.symm).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariantStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant : ∀ (l : ℕ) [Fact l.Prime], Function.Surjective (Per.θD l) ∧ (∀ y : Per.BdRp l, Per.θD l y = 0 ↔ y ∈ Per.FilP l 1) ∧ (∀ y : Per.BdRp l, Per.θD l y ≠ 0 → IsUnit y) ∧ (∀ a : Per.Ainf l, Per.θD l (aDp l a) = (Per.θ l a : ℂ_[l])) ∧ ∀ (g : Per.Gq l) (y : Per.BdRp l), Per.θD l (Per.σDp g y) = Per.σC g (Per.θD l y) := by
  first | exact @GlobalTheory.MemLoc.thetaD_props | exact GlobalTheory.MemLoc.thetaD_props | (intros; apply GlobalTheory.MemLoc.thetaD_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.PrincipalCompletion

variable {R : Type} [CommRing R] (a : R)

theorem fg : (Ideal.span {a}).FG := Submodule.fg_span_singleton a

theorem eval_eq_zero_iff (n : ℕ) (x : AdicCompletion (Ideal.span {a}) R) :
    AdicCompletion.eval (Ideal.span {a}) R n x = 0 ↔
      (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ n ∣ x := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval (fg a),
    Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, rfl⟩
    exact ⟨b, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, trivial, by rw [Algebra.smul_def, map_pow]⟩

theorem complete :
    IsAdicComplete (Ideal.span {algebraMap R (AdicCompletion (Ideal.span {a}) R) a})
      (AdicCompletion (Ideal.span {a}) R) := by
  have h := AdicCompletion.isAdicComplete (M := R) (fg a)
  rw [← IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (Ideal.span {a}) R),
    Ideal.map_span, Set.image_singleton] at h
  exact h

theorem dense (x : AdicCompletion (Ideal.span {a}) R) (r : ℕ) :
    ∃ (s : R) (z : AdicCompletion (Ideal.span {a}) R),
      x = algebraMap R _ s + (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ r * z := by
  obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (Ideal.span {a}) R r x)
  have : AdicCompletion.eval (Ideal.span {a}) R r (x - algebraMap R _ s) = 0 := by
    rw [map_sub, ← hs, sub_eq_zero]
    rfl
  obtain ⟨z, hz⟩ := (eval_eq_zero_iff a r _).1 this
  exact ⟨s, z, by rw [← hz]; ring⟩

theorem dvd_iff (s : R) (r : ℕ) :
    (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ r ∣ algebraMap R _ s ↔ a ^ r ∣ s := by
  rw [← eval_eq_zero_iff]
  have : AdicCompletion.eval (Ideal.span {a}) R r (algebraMap R _ s) = Submodule.Quotient.mk s := rfl
  rw [this, Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem torsionFree (ha : ∀ s : R, a * s = 0 → s = 0) (x : AdicCompletion (Ideal.span {a}) R)
    (hx : algebraMap R (AdicCompletion (Ideal.span {a}) R) a * x = 0) : x = 0 := by
  refine AdicCompletion.ext fun n => ?_
  change AdicCompletion.eval (Ideal.span {a}) R n x = 0
  rw [eval_eq_zero_iff]
  obtain ⟨s, z, rfl⟩ := dense a x n
  refine dvd_add ?_ (dvd_mul_right _ _)
  rw [dvd_iff]
  have h1 : (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ (n + 1) ∣
      algebraMap R _ (a * s) := ⟨-z, by rw [map_mul]; linear_combination hx⟩
  obtain ⟨t, ht⟩ := (dvd_iff a _ _).1 h1
  exact ⟨t, sub_eq_zero.1 (ha _ (by linear_combination ht))⟩

theorem basic_of_equiv_pt (p : ℕ) (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    (hp : ∀ s : R, (p : R) * s = 0 → s = 0)
    (e : A ≃+* AdicCompletion (Ideal.span {(p : R)}) R)
    (he : ∀ s, e (algebraMap R A s) = algebraMap R _ s) :
    IsAdicComplete (Ideal.span {(p : A)}) A ∧
    (∀ x : A, (p : A) * x = 0 → x = 0) ∧
    (∀ (x : A) (r : ℕ), ∃ (s : R) (z : A), x = algebraMap R A s + (p : A) ^ r * z) ∧
    ∀ (s : R) (r : ℕ), (p : A) ^ r ∣ algebraMap R A s ↔ (p : R) ^ r ∣ s := by
  have hpe : e (p : A) = algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R) (p : R) := by
    rw [map_natCast, map_natCast]
  refine ⟨?_, fun x hx => ?_, fun x r => ?_, fun s r => ?_⟩
  · have h := complete (p : R)
    rw [← IsAdicComplete.congr_ringEquiv _ e, Ideal.map_span, Set.image_singleton, hpe]
    exact h
  · apply e.injective
    rw [map_zero]
    apply torsionFree _ hp
    rw [← hpe, ← map_mul, hx, map_zero]
  · obtain ⟨s, z, hz⟩ := dense (p : R) (e x) r
    refine ⟨s, e.symm z, e.injective ?_⟩
    rw [map_add (f := _), map_mul, map_pow, he, hpe, RingEquiv.apply_symm_apply]
    exact hz
  · rw [← dvd_iff (p : R) s r, ← hpe, ← he, ← map_pow, map_dvd_iff]

end GlobalTheory.PrincipalCompletion

namespace GlobalTheory.MemLoc

theorem acris0_torsionFree (l : ℕ) [Fact l.Prime] (s : Per.Acris0 l)
    (hs : (l : Per.Acris0 l) * s = 0) : s = 0 := by
  have hu : IsUnit (l : Per.AinfP l) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Per.AinfP l) (l : Per.Ainf l)
    rwa [map_natCast] at this
  have h : (l : Per.AinfP l) * (s : Per.AinfP l) = 0 := by
    simpa using congrArg Subtype.val hs
  exact Subtype.ext ((hu.mul_right_eq_zero).1 h)

theorem acris_basic : ∀ (l : ℕ) [Fact l.Prime], IsAdicComplete (Ideal.span {(l : Per.Acris l)}) (Per.Acris l) ∧ (∀ x : Per.Acris l, (l : Per.Acris l) * x = 0 → x = 0) ∧ (∀ (x : Per.Acris l) (r : ℕ), ∃ (s : Per.Acris0 l) (z : Per.Acris l), x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ r * z) ∧ ∀ (s : Per.Acris0 l) (r : ℕ), (l : Per.Acris l) ^ r ∣ algebraMap (Per.Acris0 l) (Per.Acris l) s ↔ (l : Per.Acris0 l) ^ r ∣ s :=
  fun l _ => by
    obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
    exact GlobalTheory.PrincipalCompletion.basic_of_equiv_pt l (Per.Acris0 l) (Per.Acris l)
      (acris0_torsionFree l) e he

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsData
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsData
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem core_isEps : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, IsEps C.ε := by
  intro l _ C
  refine ⟨?_, ?_⟩
  · have h := C.ε_root 0
    rw [C.ζ_zero, map_one] at h
    exact Subtype.ext h
  · intro h1
    have h := C.ε_root 1
    have h2 : rootT C.ε 1 = 1 := h1
    rw [h2] at h
    apply C.ζ_one
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_one, ← h]
    rfl

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsDataStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, IsEps C.ε := by
  first | exact @GlobalTheory.MemLoc.core_isEps | exact GlobalTheory.MemLoc.core_isEps | (intros; apply GlobalTheory.MemLoc.core_isEps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem IsEps.isPrimitiveRoot_untilt {l : ℕ} [hl : Fact l.Prime] {e : Per.Fl l} (h : IsEps e) :
    IsPrimitiveRoot ((frobeniusEquiv (Per.Fl l) l).symm e).untilt l := by
  have hp : ((frobeniusEquiv (Per.Fl l) l).symm e).untilt ^ l = 1 := by
    rw [← map_pow, frobeniusEquiv_symm_pow_p, h.1]
  have ho := orderOf_eq_prime hp h.2
  have := IsPrimitiveRoot.orderOf ((frobeniusEquiv (Per.Fl l) l).symm e).untilt
  rwa [ho] at this

theorem ker_theta_eq_span_xi {l : ℕ} [Fact l.Prime] {e : Per.Fl l} (h : IsEps e) :
    RingHom.ker (Per.θ l) = Ideal.span {xi e} := by
  obtain ⟨⟨pf, hpf⟩, -, -, hX, -⟩ :=
    ReciprocityTheory.PGsh.a0 l ℂ_[l] Valued.v (Per.OC l) (PadicComplexInt.integers l)
  exact ((hX e (PadicComplexInt.integers l) h.isPrimitiveRoot_untilt).2.2.2 pf hpf).1

theorem theta_eq_zero_iff_xi_dvd (l : ℕ) [Fact l.Prime] :
    ∀ e : Per.Fl l, IsEps e → ∀ a : Per.Ainf l, Per.θ l a = 0 ↔ xi e ∣ a := by
  intro e h a
  rw [← RingHom.mem_ker, ker_theta_eq_span_xi h, Ideal.mem_span_singleton]

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvdStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaineTheta_eq_zero_iff_fontaineXiElement_dvd : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ a : Per.Ainf l, Per.θ l a = 0 ↔ xi e ∣ a := by
  first | exact @GlobalTheory.MemLoc.theta_eq_zero_iff_xi_dvd | exact GlobalTheory.MemLoc.theta_eq_zero_iff_xi_dvd | (intros; apply GlobalTheory.MemLoc.theta_eq_zero_iff_xi_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
noncomputable section
namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

theorem zeta_pow_iter {M : Type*} [Monoid M] {p : ℕ} {ζ : ℕ → M} (hζ : ∀ n, ζ (n + 1) ^ p = ζ n)
    (m n : ℕ) : ζ (m + n) ^ p ^ n = ζ m := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, hζ, ih]

theorem zeta_exists_system (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] (p : ℕ)
    [hp : Fact p.Prime] :
    ∃ ζ : ℕ → K, ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ p = ζ m) ∧ ζ 1 ≠ 1 := by
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.2 hp.out.ne_zero⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p K)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos p K hp.out.pos))
  have hzp : IsPrimitiveRoot z p := Polynomial.isRoot_cyclotomic_iff.1 hz
  choose r hr using fun x : K => IsAlgClosed.exists_pow_nat_eq x hp.out.pos
  refine ⟨fun n => Nat.casesOn n 1 (fun m => r^[m] z), rfl, fun n => ?_,
    hzp.ne_one hp.out.one_lt⟩
  cases n with
  | zero => exact hzp.pow_eq_one
  | succ m =>
    show r^[m + 1] z ^ p = r^[m] z
    rw [Function.iterate_succ_apply', hr]

section Tilt

variable {p : ℕ} [hp : Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]

theorem zeta_coeff_root_iterate (x : PreTilt O p) (n m : ℕ) :
    PreTilt.coeff m ((frobeniusEquiv (PreTilt O p) p).symm^[n] x) = PreTilt.coeff (m + n) x := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', PreTilt.coeff_frobeniusEquiv_symm, ih]
    congr 2
    omega

theorem zeta_exists_tilt [IsAdicComplete (Ideal.span {(p : O)}) O] (x : ℕ → O)
    (hx : ∀ n, x (n + 1) ^ p = x n) :
    ∃ e : PreTilt O p, ∀ n, ((frobeniusEquiv (PreTilt O p) p).symm^[n] e).untilt = x n := by
  let e : PreTilt O p := ⟨fun n => Ideal.Quotient.mk (Ideal.span {(p : O)}) (x n), fun n => by
    show (Ideal.Quotient.mk (Ideal.span {(p : O)}) (x (n + 1))) ^ p = _
    rw [← map_pow, hx]⟩
  refine ⟨e, fun n => Perfection.teichmuller_spec fun m => ⟨x (n + m), ?_, by rw [zeta_pow_iter hx]⟩⟩
  have := zeta_coeff_root_iterate e n m
  rw [add_comm] at this
  exact this.symm

end Tilt

theorem exists_zeta_eps (l : ℕ) [hl : Fact l.Prime] :
    ∃ (ζ : ℕ → Om l) (ε : Per.Fl l), ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ l = ζ m) ∧ ζ 1 ≠ 1 ∧
      ∀ m, (rootT ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ζ m) := by
  obtain ⟨ζ, h0, hs, h1⟩ := zeta_exists_system (Om l) l
  have hmem : ∀ m, algebraMap (Om l) ℂ_[l] (ζ m) ∈ PadicComplexInt l := fun m => by
    have h : algebraMap (Om l) ℂ_[l] (ζ m) ^ l ^ m = 1 := by
      have := zeta_pow_iter hs 0 m
      rw [zero_add, h0] at this
      rw [← map_pow, this, map_one]
    have h2 : Valued.v (algebraMap (Om l) ℂ_[l] (ζ m)) ^ l ^ m ≤ 1 := by
      rw [← map_pow, h, map_one]
    change Valued.v (algebraMap (Om l) ℂ_[l] (ζ m)) ≤ 1
    exact (pow_le_one_iff_of_nonneg zero_le (pow_ne_zero _ hl.out.ne_zero)).1 h2
  obtain ⟨e, he⟩ := zeta_exists_tilt (p := l) (O := Per.OC l)
    (fun m => ⟨algebraMap (Om l) ℂ_[l] (ζ m), hmem m⟩) (fun m => Subtype.ext (by
      show algebraMap (Om l) ℂ_[l] (ζ (m + 1)) ^ l = algebraMap (Om l) ℂ_[l] (ζ m)
      rw [← map_pow, hs]))
  exact ⟨ζ, e, h0, hs, h1, fun m => congrArg Subtype.val (he m)⟩

end GlobalTheory.MemLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadicStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic : ∀ (l : ℕ) [Fact l.Prime], ∃ (ζ : ℕ → Om l) (ε : Per.Fl l), ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ l = ζ m) ∧ ζ 1 ≠ 1 ∧ ∀ m, (rootT ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ζ m) := by
  first | exact @GlobalTheory.MemLoc.exists_zeta_eps | exact GlobalTheory.MemLoc.exists_zeta_eps | (intros; apply GlobalTheory.MemLoc.exists_zeta_eps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgEquivRootOfUnityEqPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

open IsLocalRing

theorem exists_algEquiv_rootOfUnity_eq_pow (V K : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (hfin : Finite (V ⧸ maximalIdeal V)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Algebra V Ω] [IsScalarTower V K Ω] :
    ∃ φ : Ω ≃ₐ[K] Ω, ∀ (x : Ω) (m : ℕ), (m : V) ∉ maximalIdeal V → x ^ m = 1 →
      φ x = x ^ Nat.card (V ⧸ maximalIdeal V) := by
  have : IsGalois K Ω := {}
  have hc : SMulCommClass (Ω ≃ₐ[K] Ω) V Ω := ⟨fun g v x => by
    rw [← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]
    exact map_smul g _ _⟩
  let : TopologicalSpace (integralClosure V Ω) := ⊥
  have : DiscreteTopology (integralClosure V Ω) := ⟨rfl⟩
  have : ContinuousSMul (Ω ≃ₐ[K] Ω) (integralClosure V Ω) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := K) (x : Ω)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  have : Algebra.IsInvariant V (integralClosure V Ω) (Ω ≃ₐ[K] Ω) := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (b : Ω)).2
      fun g => congrArg Subtype.val (hb g)
    have hint : IsIntegral V k := by
      have h2 : IsIntegral V (algebraMap K Ω k) := hk ▸ b.2
      exact (isIntegral_algebraMap_iff ).1 h2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨v, Subtype.ext ?_⟩
    rw [← hk, ← hv, ← IsScalarTower.algebraMap_apply]
    rfl
  have hinj : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  have : FaithfulSMul V (integralClosure V Ω) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  obtain ⟨Q, hQ, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := integralClosure V Ω) (maximalIdeal V)
  let : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _
  let : Field (integralClosure V Ω ⧸ Q) := Ideal.Quotient.field _
  let : Fintype (V ⧸ maximalIdeal V) := Fintype.ofFinite _
  have : Algebra.IsAlgebraic (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ Q) := by
    have hi : Algebra.IsIntegral (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ Q) :=
      Ideal.Quotient.algebra_isIntegral_of_liesOver _ _
    exact hi.isAlgebraic
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[K] Ω)
    (maximalIdeal V) Q
    (FiniteField.frobeniusAlgEquivOfAlgebraic (V ⧸ maximalIdeal V) _)
  have hu : Q.under V = maximalIdeal V := hQo.over.symm
  have hF : IsArithFrobAt V σ.1 Q := by
    intro x
    have h := DFunLike.congr_fun hσ (Ideal.Quotient.mk _ x)
    rw [← Ideal.Quotient.eq, map_pow, hu, Nat.card_eq_fintype_card]
    exact h
  refine ⟨σ.1, fun x m hm hx => ?_⟩
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (by simp))
  have hxi : IsIntegral V x := IsIntegral.of_pow hm0 (by rw [hx]; exact isIntegral_one)
  have hmQ : ((m : ℕ) : integralClosure V Ω) ∉ Q := by
    intro h
    apply hm
    rw [← hu, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact h
  have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hF (ζ := ⟨x, hxi⟩) (m := m)
    (Subtype.ext hx) hmQ
  rw [hu] at h
  exact congrArg Subtype.val h

theorem exists_frobenius_Kur (l : ℕ) [Fact l.Prime] :
    ∃ σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l),
      ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l := by
  have e : (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) ≃+* ZMod l := PadicInt.residueField
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hcard : Nat.card (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = l := by
    rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
  obtain ⟨φ, hφ⟩ := exists_algEquiv_rootOfUnity_eq_pow ℤ_[l] ℚ_[l]
    (Finite.of_equiv _ e.symm.toEquiv) (Om l)
  rw [hcard] at hφ
  have hφ' : ∀ (x : Om l) (m : ℕ), ¬ l ∣ m → x ^ m = 1 → φ x = x ^ l := by
    intro x m hm hx
    refine hφ x m (fun h => hm ?_) hx
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at h
    exact h
  have hle : (MaximalUnramifiedExtension l).map (φ : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨x, ⟨m, hm, hlm, hx⟩, rfl⟩
    exact ⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩
  refine ⟨((φ : Om l →ₐ[ℚ_[l]] Om l).comp (MaximalUnramifiedExtension l).val).codRestrict (MaximalUnramifiedExtension l).toSubalgebra
    (fun x => hle ⟨x, x.2, rfl⟩), fun c m _ hlm hc => Subtype.ext ?_⟩
  exact hφ' c m hlm (congrArg Subtype.val hc)

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerTiltMinusOnePowDivEnvelope
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerTiltMinusOnePowDivEnvelope
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem pow_sub_one_pow_congr_geom_sum_pow {R : Type} [CommRing R] {l : ℕ} (hl : l.Prime) (x : R) :
    (l : R) ∣ (x ^ l - 1) ^ (l - 1) - (∑ i ∈ Finset.range l, x ^ i) ^ l := by
  have key : (l : Polynomial ℤ) ∣ (Polynomial.X ^ l - 1) ^ (l - 1) -
      (∑ i ∈ Finset.range l, (Polynomial.X : Polynomial ℤ) ^ i) ^ l := by
    set y : Polynomial ℤ := Polynomial.X - 1 with hy
    have hy0 : y ≠ 0 := Polynomial.X_sub_C_ne_zero (1 : ℤ)
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl y 1
    have hX : y + 1 = Polynomial.X := by rw [hy]; ring
    rw [hX, one_pow] at hr
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, (Nat.sub_add_cancel hl.one_le).symm⟩
    set s : Polynomial ℤ := ∑ i ∈ Finset.range (k + 1), (Polynomial.X : Polynomial ℤ) ^ i with hs
    have h1 : s * y = Polynomial.X ^ (k + 1) - 1 := geom_sum_mul _ _
    have h2 : s = y ^ k + ((k + 1 : ℕ) : Polynomial ℤ) * r := by
      refine mul_right_cancel₀ hy0 ?_
      rw [h1, hr]; ring
    have h3 : ((k + 1 : ℕ) : Polynomial ℤ) ∣ s - y ^ k := ⟨r, by rw [h2]; ring⟩
    have h4 : ((k + 1 : ℕ) : Polynomial ℤ) ∣ (Polynomial.X ^ (k + 1) - 1) - y ^ (k + 1) :=
      ⟨y * r, by rw [hr]; ring⟩
    have h5 := h3.trans (sub_dvd_pow_sub_pow s (y ^ k) (k + 1))
    have h6 := h4.trans (sub_dvd_pow_sub_pow _ (y ^ (k + 1)) k)
    have h7 := dvd_sub h6 h5
    rw [← pow_mul, ← pow_mul, mul_comm k (k + 1), sub_sub_sub_cancel_right] at h7
    simpa using h7
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum] using map_dvd (Polynomial.aeval (R := ℤ) x) key

theorem exists_div_prime_pow_dvd {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {l : ℕ} (hl : l.Prime)
    (hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : A)) (S : Subalgebra R A) (η z : R)
    (hη : ∀ n : ℕ, ∃ g ∈ S, ((n.factorial : ℕ) : A) * g = algebraMap R A η ^ n)
    (hz : ∀ n : ℕ, ∃ g ∈ S, ((n.factorial : ℕ) : A) * g = algebraMap R A z ^ n) :
    ∃ w : S, (l : A) * (w : A) = algebraMap R A (η ^ l + l * z) ∧ (l : S) ∣ w ^ l := by
  obtain ⟨g₁, m₁, h₁⟩ := hη l
  obtain ⟨g₂, m₂, h₂⟩ := hη (l * l)
  obtain ⟨g₃, m₃, h₃⟩ := hz l
  have hf : ((l.factorial : ℕ) : A) = (l : A) * ((l - 1).factorial : ℕ) := by
    rw [← Nat.mul_factorial_pred hl.ne_zero]; push_cast; rfl
  have hb : (((l * l).factorial : ℕ) : A) =
      (Nat.uniformBell l l : A) * ((l.factorial : ℕ) : A) ^ l * ((l.factorial : ℕ) : A) := by
    rw [← Nat.uniformBell_mul_eq l hl.ne_zero]; push_cast; rfl
  have hg : g₁ ^ l = (Nat.uniformBell l l : A) * ((l.factorial : ℕ) : A) * g₂ := by
    refine ((hu l).pow l).mul_left_cancel ?_
    rw [← mul_pow, h₁, ← pow_mul, ← h₂, hb]; ring
  let a : S := (((l - 1).factorial : ℕ) : S) * ⟨g₁, m₁⟩
  let b : S := algebraMap R S z
  refine ⟨a + b, ?_, ?_⟩
  · rw [map_add (f := _), map_mul, map_pow, map_natCast, ← h₁, hf]
    simp only [a, b]
    push_cast
    ring
  · obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl a b
    have ha : (l : S) ∣ a ^ l := by
      refine ⟨(((l - 1).factorial : ℕ) : S) ^ l * (Nat.uniformBell l l : S) * (((l - 1).factorial : ℕ) : S) *
        ⟨g₂, m₂⟩, Subtype.ext ?_⟩
      simp only [a]
      push_cast
      rw [mul_pow, hg, hf]; ring
    have hb : (l : S) ∣ b ^ l := by
      refine ⟨(((l - 1).factorial : ℕ) : S) * ⟨g₃, m₃⟩, Subtype.ext ?_⟩
      simp only [b]
      push_cast
      rw [← h₃, hf]; ring
    rw [hr]
    exact dvd_add (dvd_add ha hb) ⟨a * b * r, by ring⟩

theorem exists_dividedPower_mem_Acris0 (l : ℕ) [Fact l.Prime] (x : Per.Ainf l) (hx : Per.θ l x = 0) (n : ℕ) :
    ∃ g ∈ Per.Acris0 l, ((n.factorial : ℕ) : Per.AinfP l) * g = algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n := by
  obtain ⟨u, hu⟩ := (GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero).exists_right_inv
  have h : ((n.factorial : ℕ) : Per.AinfP l) * (u * algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n) =
      algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n := by rw [← mul_assoc, hu, one_mul]
  refine ⟨_, ?_, h⟩
  apply GlobalTheory.RingIface.dividedPower_mem_Acris0 <;> assumption

theorem tm_root_pow (l : ℕ) [Fact l.Prime] (e : Per.Fl l) :
    Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) ^ l = Per.tm e := by
  rw [← map_pow]
  congr 1
  exact frobeniusEquiv_symm_pow_p (Per.Fl l) l e

theorem exists_mu_pow_div_of_isEps (l : ℕ) [hl : Fact l.Prime] (e : Per.Fl l) (he : IsEps e) :
    ∃ w : Per.Acris0 l, (l : Per.AinfP l) * (w : Per.AinfP l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1) ∧ (l : Per.Acris0 l) ∣ w ^ l := by
  set x := Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) with hx
  have hxl : x ^ l = Per.tm e := tm_root_pow l e
  have hmu : mu e = x ^ l - 1 := by rw [hxl]; rfl
  have hθmu : Per.θ l (x ^ l - 1) = 0 := by
    rw [hxl, map_sub, map_one, WittVector.fontaineTheta_teichmuller, he.1, sub_self]
  have hθx : Per.θ l (x - 1) ≠ 0 := by
    rw [hx, map_sub, map_one, WittVector.fontaineTheta_teichmuller, sub_ne_zero]
    exact he.2
  have hη : Per.θ l (∑ i ∈ Finset.range l, x ^ i) = 0 := by
    rw [← geom_sum_mul, map_mul] at hθmu
    exact (mul_eq_zero.1 hθmu).resolve_right hθx
  obtain ⟨z, hz⟩ := pow_sub_one_pow_congr_geom_sum_pow hl.out x
  have hθz : Per.θ l z = 0 := by
    have h := congrArg (Per.θ l) hz
    have h1 : l - 1 ≠ 0 := by have := hl.out.two_le; omega
    rw [map_sub, map_pow, map_pow, hθmu, hη, zero_pow h1, zero_pow hl.out.ne_zero, sub_self, map_mul,
      map_natCast] at h
    refine (mul_eq_zero.1 h.symm).resolve_left ?_
    exact_mod_cast hl.out.ne_zero
  obtain ⟨w, hw, hd⟩ := exists_div_prime_pow_dvd hl.out
    (fun n => GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero) (Per.Acris0 l) _ z
    (exists_dividedPower_mem_Acris0 l _ hη) (exists_dividedPower_mem_Acris0 l _ hθz)
  refine ⟨w, ?_, hd⟩
  rw [hw, ← hz, add_sub_cancel, map_pow, hmu]

theorem exists_mu_pow_div : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, e.untilt = 1 →
    ∃ w : Per.Acris0 l, (l : Per.AinfP l) * (w : Per.AinfP l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1) ∧ (l : Per.Acris0 l) ∣ w ^ l := by
  intro l hl e he
  have step : ∀ m : ℕ, ∀ e : Per.Fl l, e.untilt = 1 →
      (((frobeniusEquiv (Per.Fl l) l).symm)^[m] e).untilt ≠ 1 →
      ∃ w : Per.Acris0 l, (l : Per.AinfP l) * (w : Per.AinfP l) =
        algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1) ∧ (l : Per.Acris0 l) ∣ w ^ l := by
    intro m
    induction m with
    | zero => exact fun e h1 h2 => absurd h1 h2
    | succ m ih =>
      intro e h1 h2
      by_cases h : ((frobeniusEquiv (Per.Fl l) l).symm e).untilt = 1
      · obtain ⟨w, hw, hd⟩ := ih _ h h2
        have hmu : mu e = xi e * mu ((frobeniusEquiv (Per.Fl l) l).symm e) := by
          rw [xi, mu, mu, geom_sum_mul, tm_root_pow]
        refine ⟨algebraMap _ _ (xi e ^ (l - 1)) * w, ?_, ?_⟩
        · rw [hmu, map_mul, mul_pow, ← hw, ← map_pow, Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
          ring
        · rw [mul_pow]
          exact hd.mul_left _
      · exact exists_mu_pow_div_of_isEps l e ⟨h1, h⟩
  by_cases h : ∃ m : ℕ, (((frobeniusEquiv (Per.Fl l) l).symm)^[m] e).untilt ≠ 1
  · obtain ⟨m, hm⟩ := h
    exact step m e he hm
  · push Not at h
    have h1 : e = 1 := by
      refine Perfection.ext fun n => ?_
      have h2 := PreTilt.mk_untilt_eq_coeff_zero (((frobeniusEquiv (Per.Fl l) l).symm)^[n] e)
      rw [h n, map_one, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add] at h2
      exact h2.symm.trans (map_one (PreTilt.coeff (O := Per.OC l) (p := l) n)).symm
    have h0 : l - 1 ≠ 0 := by have := hl.out.two_le; omega
    refine ⟨0, ?_, by rw [zero_pow hl.out.ne_zero]; exact dvd_zero _⟩
    have hm : mu e = 0 := by
      rw [h1]
      exact sub_eq_zero.2 (map_one (WittVector.teichmuller l))
    rw [hm, map_zero, zero_pow h0]
    simp

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerTiltMinusOnePowDivEnvelopeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_teichmullerTiltMinusOne_pow_div_envelope : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, e.untilt = 1 → ∃ w : Per.Acris0 l, (l : Per.AinfP l) * (w : Per.AinfP l) = algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1) ∧ (l : Per.Acris0 l) ∣ w ^ l := by
  first | exact @GlobalTheory.MemLoc.exists_mu_pow_div | exact GlobalTheory.MemLoc.exists_mu_pow_div | (intros; apply GlobalTheory.MemLoc.exists_mu_pow_div <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfIsDomainAndAinfInvPInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfIsDomainAndAinfInvPInjective
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem ainf_isDomain_and_injective : ∀ (l : ℕ) [Fact l.Prime], IsDomain (Per.Ainf l) ∧ IsDomain (Per.AinfP l) ∧
    Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) := by
  intro l _
  have : IsDomain (Per.Fl l) := inferInstance
  have h : IsDomain (Per.Ainf l) := inferInstance
  have hp : (l : Per.Ainf l) ≠ 0 := WittVector.p_nonzero l _
  have hle : Submonoid.powers (l : Per.Ainf l) ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hp
  exact ⟨h, IsLocalization.isDomain_of_le_nonZeroDivisors (Per.AinfP l) hle, IsLocalization.injective _ hle⟩

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfIsDomainAndAinfInvPInjectiveStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.usage : ∀ (l : ℕ) [Fact l.Prime], IsDomain (Per.Ainf l) ∧ IsDomain (Per.AinfP l) ∧ Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) := by
  first | exact @GlobalTheory.MemLoc.ainf_isDomain_and_injective | exact GlobalTheory.MemLoc.ainf_isDomain_and_injective | (intros; apply GlobalTheory.MemLoc.ainf_isDomain_and_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffEqMkRootT
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem coeff_eq_mk_rootT {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (n : ℕ) :
    PreTilt.coeff n e = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (rootT e n) := by
  have h2 := PreTilt.mk_untilt_eq_coeff_zero (((frobeniusEquiv (Per.Fl l) l).symm^[n]) e)
  have h3 := PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n e
  rw [zero_add] at h3
  rw [← h3, ← h2]
  rfl

theorem eps_coeff : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (n : ℕ),
    PreTilt.coeff n C.ε = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (rootT C.ε n) :=
  fun _ _ C n => coeff_eq_mk_rootT C.ε n

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Imports
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.UpqHaarRight

theorem isMulRightInvariant :
    ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)), μ.IsHaarMeasure → μ.IsMulRightInvariant :=
  fun P Q μ hμ => GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure P Q μ hμ

end GlobalTheory.UpqHaarRight
end
