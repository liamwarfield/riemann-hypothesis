module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsMulMulConjTransposeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryModuleStandardOpensIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFilteredColimitRingsFinitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureProjectiveOverStandardOpenRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomothetyLatSum
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.HomothetyLatSum

variable {E : Type} [Field E] [NumberField E]

def mulQ (α : E) : Quotient (unitRel (E := E)) → Quotient (unitRel (E := E)) :=
  Quotient.map (fun x => α * x) (by rintro x x' ⟨u, h⟩; exact ⟨u, by rw [h]; ring⟩)

theorem mulQ_mk (α x : E) : mulQ α (Quotient.mk _ x) = Quotient.mk (unitRel (E := E)) (α * x) := rfl

theorem mulQ_mulQ (a b : E) (q : Quotient (unitRel (E := E))) : mulQ a (mulQ b q) = mulQ (a * b) q := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rw [mulQ_mk, mulQ_mk, mulQ_mk, mul_assoc]

theorem mulQ_one (q : Quotient (unitRel (E := E))) : mulQ 1 q = q := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rw [mulQ_mk, one_mul]

theorem mulQ_mem {α : E} (hα : α ≠ 0) {L : Set E} {q : Quotient (unitRel (E := E))} (hq : q ∈ modUnits L) :
    mulQ α q ∈ modUnits ((fun x => α * x) '' L) := by
  obtain ⟨x, hx, h0, rfl⟩ := hq
  exact ⟨α * x, ⟨x, hx, rfl⟩, mul_ne_zero hα h0, rfl⟩

theorem mulQ_inv_mem {α : E} (hα : α ≠ 0) {L : Set E} {q : Quotient (unitRel (E := E))}
    (hq : q ∈ modUnits ((fun x => α * x) '' L)) : mulQ α⁻¹ q ∈ modUnits L := by
  obtain ⟨_, ⟨x, hx, rfl⟩, h0, rfl⟩ := hq
  refine ⟨x, hx, fun h => h0 (by simp [h]), ?_⟩
  rw [mulQ_mk, inv_mul_cancel_left₀ hα]

def mulEquiv {α : E} (hα : α ≠ 0) (L : Set E) : modUnits L ≃ modUnits ((fun x => α * x) '' L) where
  toFun q := ⟨mulQ α q.1, mulQ_mem hα q.2⟩
  invFun q := ⟨mulQ α⁻¹ q.1, mulQ_inv_mem hα q.2⟩
  left_inv q := Subtype.ext (by simp only; rw [mulQ_mulQ, inv_mul_cancel₀ hα, mulQ_one])
  right_inv q := Subtype.ext (by simp only; rw [mulQ_mulQ, mul_inv_cancel₀ hα, mulQ_one])

variable {I : Type} [Fintype I]

theorem term_out_mulQ [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (α : E)
    (q : Quotient (unitRel (E := E))) :
    term φ (2 * s) κ σ (mulQ α q).out = term φ (2 * s) κ σ α * term φ (2 * s) κ σ q.out := by
  have h1 : mulQ α q = Quotient.mk _ (α * q.out) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  obtain ⟨u, hu⟩ := Quotient.exact ((Quotient.out_eq _).trans h1)
  rw [← term_mul, hu, (TermUnit.term_unit_and_norm E I φ hφ s κ σ _).1 u]

theorem term_eq_lamInf [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (α : Eˣ) :
    term φ (2 * s) κ σ α =
      (lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) := by
  have key : ∀ i, ((‖φ i α‖ : ℝ) : ℂ) ^ (-2 * σ) = (((‖φ i α‖ ^ 2 : ℝ)) : ℂ) ^ (-σ) := fun i => by
    have hp : 0 < ‖φ i α‖ := by simp
    have : (((‖φ i α‖ ^ 2 : ℝ)) : ℂ) = ((‖φ i α‖ : ℝ) : ℂ) * ((‖φ i α‖ : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.mul_cpow_ofReal_nonneg hp.le hp.le,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hp.ne')]
    congr 1; ring
  rw [← TermUnit.prod_norm_sq hφ, ← TermUnit.prod_cpow _ _ (fun i => by positivity)]
  unfold term lamInf
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [key]
  have gen : ∀ (a c N : ℂ) (m n : ℕ), a⁻¹ ^ m * c ^ n * N = (a ^ m * c⁻¹ ^ n)⁻¹ * N := by
    intro a c N m n
    rw [mul_inv, inv_pow, inv_pow, inv_inv]
  exact gen _ _ _ _ _

theorem homothety (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (L : Set E) : Homothety φ (2 * s) L := by
  intro κ α S hS
  have hα : (α : E) ≠ 0 := α.ne_zero
  have hN : ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]; exact hα
  have key : IsLatSum φ (2 * s) κ ((fun x => (α : E) * x) '' L)
      (fun σ => (lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) * S σ) := by
    refine ⟨?_, fun σ hσ => ?_⟩
    · exact ((differentiable_neg.const_cpow (Or.inl hN)).const_mul _).mul hS.1
    · have h1 := (hS.2 σ hσ).mul_left
        ((lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ))
      have hf : ((fun q' : modUnits ((fun x => (α : E) * x) '' L) => term φ (2 * s) κ σ q'.1.out) ∘ mulEquiv hα L) =
          fun q : modUnits L => (lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) *
            term φ (2 * s) κ σ q.1.out := funext fun q => by
        show term φ (2 * s) κ σ (mulQ (α : E) q.1).out = _
        rw [term_out_mulQ hφ, term_eq_lamInf hφ]
      rw [← (mulEquiv hα L).hasSum_iff, hf]
      exact h1
  refine ⟨key, fun S' hS' => ?_⟩
  rw [hS'.unique key]
  simp

end GlobalTheory.HomothetyLatSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorLowerBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorLowerBound
open NumberField IsDedekindDomain GlobalTheory.SUVol
open Matrix

namespace GlobalTheory.SUVol

theorem ncard_image_lifts_eq_card_specialUnitaryGroup {O : Type*} [CommRing O] (w : Ideal O)
    [StarRing (O ⧸ w)] (c : O → O)
    (hc : ∀ x, star (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x)) (r : ℕ) :
    Set.ncard ((fun g : Matrix (Fin r) (Fin r) O => g.map (Ideal.Quotient.mk w)) ''
      {g | g.det - 1 ∈ w ∧ ∀ a b, (gᵀ * g.map c - 1) a b ∈ w}) =
      Nat.card (Matrix.specialUnitaryGroup (Fin r) (O ⧸ w)) := by
  have key : ∀ g : Matrix (Fin r) (Fin r) O,
      (g.det - 1 ∈ w ∧ ∀ a b, (gᵀ * g.map c - 1) a b ∈ w) ↔
        (g.map (Ideal.Quotient.mk w))ᵀ ∈ Matrix.specialUnitaryGroup (Fin r) (O ⧸ w) := by
    intro g
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, Matrix.det_transpose,
      and_comm]
    refine and_congr ?_ ?_
    · rw [← Matrix.ext_iff]
      refine forall_congr' fun a => forall_congr' fun b => ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub, sub_eq_zero]
      have e1 : Ideal.Quotient.mk w ((gᵀ * g.map c) a b) =
          ((g.map (Ideal.Quotient.mk w))ᵀ * star (g.map (Ideal.Quotient.mk w))ᵀ) a b := by
        simp [Matrix.mul_apply, Matrix.star_apply, hc]
      have e2 : Ideal.Quotient.mk w ((1 : Matrix (Fin r) (Fin r) O) a b) =
          (1 : Matrix (Fin r) (Fin r) (O ⧸ w)) a b := by
        simp only [Matrix.one_apply]; split_ifs <;> simp
      rw [e1, e2]
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_one, RingHom.map_det,
        RingHom.mapMatrix_apply]
  have himg : ((fun g : Matrix (Fin r) (Fin r) O => g.map (Ideal.Quotient.mk w)) ''
      {g | g.det - 1 ∈ w ∧ ∀ a b, (gᵀ * g.map c - 1) a b ∈ w}) =
      Matrix.transpose '' (Matrix.specialUnitaryGroup (Fin r) (O ⧸ w) : Set _) := by
    ext A
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨_, (key g).1 hg, Matrix.transpose_transpose _⟩
    · rintro ⟨B, hB, rfl⟩
      choose s hs using Ideal.Quotient.mk_surjective (I := w)
      have e : (Bᵀ.map s).map (Ideal.Quotient.mk w) = Bᵀ := by
        ext a b; simp [hs]
      refine ⟨Bᵀ.map s, (key _).2 ?_, e⟩
      rw [e, Matrix.transpose_transpose]; exact hB
  rw [himg, Set.ncard_image_of_injective _ Matrix.transpose_injective, ← Nat.card_coe_set_eq]
  rfl

theorem exists_star_ne_of_not_surjective {K A : Type*} [Field K] [Finite K] [StarRing K]
    (f : A → K) (hadd : ∀ x : K, ∃ a, f a = x + star x) (hmul : ∀ x : K, ∃ a, f a = x * star x)
    (hf : ¬ Function.Surjective f) : ∃ a : K, star a ≠ a := by
  by_contra h
  push Not at h
  apply hf
  intro x
  by_cases h2 : (2 : K) = 0
  · have hinj : Function.Injective (fun y : K => y * y) := by
      intro y z hyz
      simp only at hyz
      have : (y - z) * (y - z) = 0 := by linear_combination hyz + (z * z - y * z) * h2
      exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
    obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj x
    obtain ⟨a, ha⟩ := hmul y
    exact ⟨a, by rw [ha, h y]; exact hy⟩
  · obtain ⟨a, ha⟩ := hadd (x / 2)
    exact ⟨a, by rw [ha, h]; field_simp; ring⟩

theorem prod_le_locFactor_of_isPrime (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hr : 1 ≤ r)
    (hw : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime) :
    ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ locFactor E r v := by
  classical
  unfold locFactor resOrder
  rw [if_pos hw]
  set w := v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) with hwdef
  set c := IsCMField.ringOfIntegersComplexConj E with hcdef
  have hcc : ∀ x, c (c x) = x := fun x => by
    ext; simp [hcdef]
  have hfix : ∀ a, c (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) = algebraMap _ _ a :=
    fun a => (IsCMField.ringOfIntegersComplexConj_eq_self_iff E _).2 ⟨a, rfl⟩
  have hle : w ≤ w.comap (c : 𝓞 E →+* 𝓞 E) := by
    rw [hwdef, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change c _ ∈ _
    rw [hfix]
    exact Ideal.mem_map_of_mem _ ha
  have hw0 : w ≠ ⊥ := by
    rw [hwdef, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  haveI hmax : w.IsMaximal := hw.isMaximal hw0
  letI : Field (𝓞 E ⧸ w) := Ideal.Quotient.field w
  haveI : Finite (𝓞 E ⧸ w) := Ideal.finiteQuotientOfFreeOfNeBot w hw0
  let σ : (𝓞 E ⧸ w) →+* (𝓞 E ⧸ w) := Ideal.quotientMap w (c : 𝓞 E →+* 𝓞 E) hle
  have hσ : ∀ x, σ (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x) := fun x => rfl
  letI : StarRing (𝓞 E ⧸ w) :=
    { star := σ
      star_involutive := fun x => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        change σ (σ _) = _
        rw [hσ, hσ, hcc]
      star_mul := fun x y => by
        change σ (x * y) = σ y * σ x
        rw [map_mul, mul_comm]
      star_add := fun x y => map_add σ x y }
  have hstar : ∀ x, star (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x) := hσ
  rw [ncard_image_lifts_eq_card_specialUnitaryGroup w c hstar r]
  set q := Ideal.absNorm v.asIdeal with hq
  have hK : Nat.card (𝓞 E ⧸ w) = q ^ 2 := by
    have h := Ideal.absNorm_algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) v.asIdeal
    rw [← IsFractionRing.finrank_eq (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) (𝓞 E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two, Ideal.absNorm_apply (Ideal.map _ _),
      Submodule.cardQuot_apply] at h
    exact h
  have hq2 : 2 ≤ q := GlobalTheory.FiniteOrders.two_le_of_card_eq_sq hK
  have hs : ∃ a : 𝓞 E ⧸ w, star a ≠ a := by
    let f : (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) →+* (𝓞 E ⧸ w) :=
      Ideal.quotientMap w (algebraMap _ _) Ideal.le_comap_map
    have hf : ∀ a, f (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk w (algebraMap _ _ a) :=
      fun a => rfl
    refine exists_star_ne_of_not_surjective f (fun x => ?_) (fun x => ?_) (fun hsurj => ?_)
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E (y + c y)).1
        (by change c _ = _; rw [map_add (f := _), hcc, add_comm])
      exact ⟨Ideal.Quotient.mk _ a, by rw [hf, ha, hstar, map_add (f := _)]⟩
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E (y * c y)).1
        (by change c _ = _; rw [map_mul, hcc, mul_comm])
      exact ⟨Ideal.Quotient.mk _ a, by rw [hf, ha, hstar, map_mul]⟩
    · haveI : Finite (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) :=
        Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
      have h1 := Nat.card_le_card_of_surjective f hsurj
      have h2 : Nat.card (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) = q := by
        rw [hq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [hK, h2] at h1
      nlinarith
  have h := GlobalTheory.FiniteOrders.card_specialUnitaryGroup hK hs (Fin r) (Fintype.card_fin r) hr
  have h' := congrArg (Rat.cast : ℚ → ℝ) h
  push_cast at h'
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hq0 : (0 : ℝ) < q := by linarith
  rw [le_div_iff₀ (by positivity)]
  refine le_of_le_of_eq ?_ h'.symm
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_))
    (by positivity)
  · exact sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hq1))
  · have hp : (0 : ℝ) ≤ ((q : ℝ) ^ i)⁻¹ := by positivity
    rcases neg_one_pow_eq_or ℝ i with h1 | h1 <;> rw [h1] <;> linarith

end GlobalTheory.SUVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorLowerBoundStatement
open NumberField IsDedekindDomain GlobalTheory.SUVol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_factor_lower_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), 1 ≤ r →
    (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime →
    ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ locFactor E r v := by
  first | exact @GlobalTheory.SUVol.prod_le_locFactor_of_isPrime | exact GlobalTheory.SUVol.prod_le_locFactor_of_isPrime | (intros; apply GlobalTheory.SUVol.prod_le_locFactor_of_isPrime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedDualRegularFormsFiniteCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRegularFormsOfWedgePairingPerfect
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRegularFormsOfWedgePairingPerfect
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

section Wedge

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem omB_smul_mem (B : Subalgebra k K) (q : ℕ) {c : K} (hc : c ∈ B) {z : DR k K}
    (hz : z ∈ omB k K B q) : c • z ∈ omB k K B q := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hz
    exact Submodule.subset_span ⟨c * b, B.mul_mem hc hb, v, hv, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

def topCoefBasis {n : ℕ} (b : Module.Basis (Fin n) K Ω[K⁄k]) : DR k K →ₗ[K] K :=
  ExteriorAlgebra.liftAlternating (fun i => if h : i = n then h ▸ b.det else 0)

theorem topCoefBasis_ιMulti {n : ℕ} (b : Module.Basis (Fin n) K Ω[K⁄k]) (v : Fin n → Ω[K⁄k]) :
    topCoefBasis b (ExteriorAlgebra.ιMulti K n v) = b.det v := by
  simp [topCoefBasis, ExteriorAlgebra.liftAlternating_apply_ιMulti]

theorem topCoefBasis_mem (B : Subalgebra k K) {n : ℕ} (b : Module.Basis (Fin n) K Ω[K⁄k]) (f : K)
    (hf : ∀ (v : B) (j : Fin n), ∃ c : B, f * b.repr (D k K (v : K)) j = c)
    {z : DR k K} (hz : z ∈ omB k K B n) : ∃ e : B, f ^ n * topCoefBasis b z = e := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b0, hb0, v, hv, rfl⟩ := hz
    choose M hM using fun i j => hf ⟨v j, hv j⟩ i
    have hmat : f • b.toMatrix (fun j => D k K (v j)) = (B.val : B →+* K).mapMatrix (Matrix.of M) := by
      ext i j
      simp [Module.Basis.toMatrix_apply, ← hM]
    have hdet := congrArg Matrix.det hmat
    rw [Matrix.det_smul, Fintype.card_fin, ← RingHom.map_det] at hdet
    refine ⟨⟨b0, hb0⟩ * (Matrix.of M).det, ?_⟩
    rw [map_smul, topCoefBasis_ιMulti, Module.Basis.det_apply, smul_eq_mul, mul_left_comm, hdet]
    simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨e1, h1⟩ := hx
    obtain ⟨e2, h2⟩ := hy
    exact ⟨e1 + e2, by rw [map_add (f := _), mul_add, h1, h2]; simp⟩
  | smul r x _ hx =>
    obtain ⟨e, he⟩ := hx
    exact ⟨r • e, by rw [LinearMap.map_smul_of_tower, mul_smul_comm, he]; simp⟩

theorem eq_sum_exteriorPower_basis {n q : ℕ} (b : Module.Basis (Fin n) K Ω[K⁄k]) (Y : ⋀[K]^q Ω[K⁄k]) :
    (Y : DR k K) = ∑ t, (b.exteriorPower q).repr Y t •
      ExteriorAlgebra.ιMulti K q (b ∘ (Set.powersetCard.ofFinEmbEquiv.symm t)) := by
  conv_lhs => rw [← (b.exteriorPower q).sum_repr Y]
  simp [exteriorPower.coe_basis, exteriorPower.ιMulti_family]

theorem wedge_coef_mem (B : Subalgebra k K) {p q : ℕ} (b : Module.Basis (Fin (p + q)) K Ω[K⁄k])
    (u : Fin (p + q) → B) (hb : ∀ j, b j = D k K (u j : K)) (f : K)
    (hf : ∀ (v : B) (j : Fin (p + q)), ∃ c : B, f * b.repr (D k K (v : K)) j = c)
    (Y : ⋀[K]^q Ω[K⁄k]) (hmul : ∀ a ∈ omB k K B p, a * (Y : DR k K) ∈ omB k K B (p + q))
    (s : Set.powersetCard (Fin (p + q)) q) :
    ∃ e : B, f ^ (p + q) * (b.exteriorPower q).repr Y s = e := by
  classical
  have hcard : (s.val)ᶜ.card = p := by
    rw [Finset.card_compl, Fintype.card_fin, s.prop]; omega
  set g := Finset.orderEmbOfFin (s.val)ᶜ hcard with hg
  set a : DR k K := ExteriorAlgebra.ιMulti K p (b ∘ g) with ha_def
  have ha : a ∈ omB k K B p :=
    Submodule.subset_span ⟨1, B.one_mem, fun j => (u (g j) : K), fun j => (u (g j)).2,
      by simp [a, Function.comp_def, hb]⟩
  obtain ⟨e, he⟩ := topCoefBasis_mem B b f hf (hmul a ha)
  have happ : ∀ h : Fin q → Fin (p + q),
      Fin.append (b ∘ g) (b ∘ h) = b ∘ Fin.append (fun i => g i) h := by
    intro h; funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  have hterm : ∀ t, t ≠ s → topCoefBasis b
      (a * ExteriorAlgebra.ιMulti K q (b ∘ (Set.powersetCard.ofFinEmbEquiv.symm t))) = 0 := by
    intro t hts
    obtain ⟨i, hit, his⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne t s).mp hts
    have hi1 : i ∈ Set.range g := by
      rw [hg, Finset.range_orderEmbOfFin]; simpa using his
    have hi2 : i ∈ Set.range (Set.powersetCard.ofFinEmbEquiv.symm t) :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t i).mpr hit
    obtain ⟨a1, ha1⟩ := hi1
    obtain ⟨a2, ha2⟩ := hi2
    rw [ha_def, ExteriorAlgebra.ιMulti_mul_ιMulti, topCoefBasis_ιMulti, happ]
    refine b.det.map_eq_zero_of_eq _ (i := Fin.castAdd q a1) (j := Fin.natAdd p a2) ?_ ?_
    · simp [ha1, ha2]
    · intro h; have := congrArg Fin.val h; simp at this; omega
  have hdiag : ∃ ε : ℤˣ, topCoefBasis b
      (a * ExteriorAlgebra.ιMulti K q (b ∘ (Set.powersetCard.ofFinEmbEquiv.symm s))) = ((ε : ℤ) : K) := by
    set h := Fin.append (fun i => g i) (Set.powersetCard.ofFinEmbEquiv.symm s) with hh
    have hinj : Function.Injective h := by
      rw [hh, Fin.append_injective_iff]
      refine ⟨g.injective, (Set.powersetCard.ofFinEmbEquiv.symm s).injective, fun i j hij => ?_⟩
      have h1 : g i ∈ (s.val)ᶜ := by
        rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin (s.val)ᶜ hcard]; exact ⟨i, rfl⟩
      have h2 : Set.powersetCard.ofFinEmbEquiv.symm s j ∈ s.val :=
        (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨j, rfl⟩
      rw [hij] at h1
      exact (Finset.mem_compl.mp h1) h2
    set σ := Equiv.ofBijective h (Finite.injective_iff_bijective.mp hinj)
    refine ⟨Equiv.Perm.sign σ, ?_⟩
    rw [ha_def, ExteriorAlgebra.ιMulti_mul_ιMulti, topCoefBasis_ιMulti, happ]
    have : b ∘ h = b ∘ σ := rfl
    rw [this, b.det.map_perm, Module.Basis.det_self, Units.smul_def, zsmul_eq_mul, mul_one]
  obtain ⟨ε, hε⟩ := hdiag
  have hsum : topCoefBasis b (a * (Y : DR k K)) = (b.exteriorPower q).repr Y s * ((ε : ℤ) : K) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_exteriorPower_basis b Y, Finset.mul_sum, map_sum, Finset.sum_eq_single s]
    · rw [mul_smul_comm, map_smul, hε, smul_eq_mul]
    · intro t _ hts; rw [mul_smul_comm, map_smul, hterm t hts, smul_zero]
    · intro h; exact absurd (Finset.mem_univ s) h
  refine ⟨e * ((ε : ℤ) : B), ?_⟩
  have hεε : ((ε : ℤ) : K) * ((ε : ℤ) : K) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  push_cast
  rw [← he, hsum]
  calc f ^ (p + q) * (b.exteriorPower q).repr Y s
      = f ^ (p + q) * (b.exteriorPower q).repr Y s * (((ε : ℤ) : K) * ((ε : ℤ) : K)) := by rw [hεε, mul_one]
    _ = _ := by ring

theorem mem_omB_of_mul_mem_omB :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K]
      [Algebra.Smooth k B] (d p q : ℕ), Module.finrank K Ω[K⁄k] = d → p + q = d →
      ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K B p, a * y ∈ omB k K B d) → y ∈ omB k K B q := by
  intro k K _ _ _ B _ _ d p q hd hpq y hy hmul
  classical
  subst hpq
  let I : Ideal B :=
    { carrier := {c | (c : K) • y ∈ omB k K B q}
      add_mem' := fun {a c} ha hc => by
        simp only [Set.mem_setOf_eq, Subalgebra.coe_add, add_smul] at *
        exact Submodule.add_mem _ ha hc
      zero_mem' := by simp
      smul_mem' := fun a c hc => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, mul_smul] at *
        exact omB_smul_mem B q a.2 hc }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨f, u, b, hfP, hb, hf⟩ := GlobalTheory.T.exists_local_kaehlerD_basis_smooth_subalgebra k K B (p + q) hd P
    apply hfP
    refine hP.isPrime.mem_of_pow_mem (p + q) (hIP ?_)
    show ((f ^ (p + q) : B) : K) • y ∈ omB k K B q
    have hy' := eq_sum_exteriorPower_basis b ⟨y, hy⟩
    simp only at hy'
    rw [hy', Finset.smul_sum]
    refine Submodule.sum_mem _ fun t _ => ?_
    obtain ⟨e, he⟩ := wedge_coef_mem B b u hb (f : K) hf ⟨y, hy⟩ hmul t
    rw [smul_smul, SubmonoidClass.coe_pow, he]
    exact Submodule.subset_span ⟨e, e.2, fun j => (u (Set.powersetCard.ofFinEmbEquiv.symm t j) : K),
      fun j => (u _).2,
      by simp [Function.comp_def, hb]⟩
  have h1 : (1 : B) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

end Wedge

end GlobalTheory.PD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRegularFormsOfWedgePairingPerfectStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_regularForms_of_wedge_pairing_perfect : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (d p q : ℕ), Module.finrank K Ω[K⁄k] = d → p + q = d → ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K B p, a * y ∈ omB k K B d) → y ∈ omB k K B q := by
  first | (exact @GlobalTheory.PD.mem_omB_of_mul_mem_omB) | (exact GlobalTheory.PD.mem_omB_of_mul_mem_omB) | (intros; apply GlobalTheory.PD.mem_omB_of_mul_mem_omB  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedDualRegularFormsFiniteCover
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem twistedDual_omB : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ p q : ℕ, p + q = d → ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K (rB k K x I) p, Algebra.trace F K (τ (a * y)) ∈ omA k x I) ↔ y ∈ omB k K (rB k K x I) q := by
  intro k _ _ F K _ _ _ _ _ _ d x hc τ hτ I hI p q hpq y hy
  obtain ⟨-, hfr, hsm⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hc I hI
  have hrk : Module.finrank K Ω[K⁄k] = d := by
    obtain ⟨b, -⟩ := hc.exists_basis
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have htop := (GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms k F K d x hc).2 τ hτ
  constructor
  · intro h
    refine GlobalTheory.T.mem_regularForms_of_wedge_pairing_perfect k K (rB k K x I) d p q hrk hpq y hy fun a ha => ?_
    have haG : a ∈ ⋀[K]^p Ω[K⁄k] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).2.1 a ha).2.2.1
    have hay : a * y ∈ ⋀[K]^d Ω[K⁄k] := hpq ▸ SetLike.mul_mem_graded haG hy
    have hz : ∀ b ∈ rB k K x I, Algebra.trace F K (τ (a * y) * b) ∈ omA k x I := by
      intro b hb
      have hba : b • a ∈ omB k K (rB k K x I) p := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).2.1 a ha).2.2.2 b hb
      have e : τ (a * y) * b = τ ((b • a) * y) := by
        rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]
      rw [e]
      exact h _ hba
    obtain ⟨y', hy', e'⟩ := (GlobalTheory.T.complementaryModule_standardOpens_iff k F K d x hc τ hτ I hI (τ (a * y))).1 hz
    have hy'G : y' ∈ ⋀[K]^d Ω[K⁄k] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) d q).2.1 y' hy').2.2.1
    rw [htop _ hay, ← e', ← htop _ hy'G]
    exact hy'
  · intro h a ha
    have hay : a * y ∈ omB k K (rB k K x I) d := hpq ▸ (GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).1 a ha y h
    have := (GlobalTheory.T.complementaryModule_standardOpens_iff k F K d x hc τ hτ I hI (τ (a * y))).2 ⟨a * y, hay, rfl⟩ 1 (Subalgebra.one_mem _)
    rwa [mul_one] at this

end GlobalTheory.PD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedDualRegularFormsFiniteCoverStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDual_regularForms_finiteCover : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ p q : ℕ, p + q = d → ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K (rB k K x I) p, Algebra.trace F K (τ (a * y)) ∈ omA k x I) ↔ y ∈ omB k K (rB k K x I) q := by
  first | (exact @GlobalTheory.PD.twistedDual_omB) | (exact GlobalTheory.PD.twistedDual_omB) | (intros; apply GlobalTheory.PD.twistedDual_omB  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaConstTermEqRationalValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaConstTermEqRationalValue
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem constTerm_eq_zetaVal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ), 1 ≤ k → ZetaVals k z → IsPartialZeta C Z → (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) = ((z C / 2 ^ Module.finrank ℚ F : ℚ) : ℂ) := by
  intro F _ _ _ k z C Z hk hz hZ
  obtain ⟨Z', hZ', e⟩ := hz C
  have hne : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
    have : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    simpa using this
  have h : Z (1 - (k : ℂ)) = Z' (1 - (k : ℂ)) :=
    GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.IsClassZeta.eqOn (C := C) (Z := Z) (Z' := Z') hZ hZ' hne
  rw [h, e]
  push_cast
  rw [div_eq_mul_inv, mul_comm, inv_pow]

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaConstTermEqRationalValueStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialZeta_constTerm_eq_rational_value : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ), 1 ≤ k → ZetaVals k z → IsPartialZeta C Z → (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) = ((z C / 2 ^ Module.finrank ℚ F : ℚ) : ℂ) := by
  first | exact @GlobalTheory.HilbFam.constTerm_eq_zetaVal | exact GlobalTheory.HilbFam.constTerm_eq_zetaVal | (intros; apply GlobalTheory.HilbFam.constTerm_eq_zetaVal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedEmptyOfUniversallyClosedOfLeJacobson
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedEmptyOfUniversallyClosedOfLeJacobson
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

theorem closed_empty_of_universallyClosed_of_le_jacobson :
  ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), UniversallyClosed p → ∀ Z : Set X, IsClosed Z → (∀ x ∈ Z, ¬ I ≤ (p x).asIdeal) → Z = ∅ := by
  intro R _ I hI X p hp Z hZ hmiss
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hcl : IsClosed (p.base '' Z) := p.isClosedMap _ hZ
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ (p x).isPrime.ne_top
  let q : Spec (CommRingCat.of R) := ⟨m, hm.isPrime⟩
  have hq : q ∈ closure {p.base x} := (PrimeSpectrum.le_iff_mem_closure _ _).mp hle
  have hq' : q ∈ p.base '' Z :=
    closure_minimal (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem p.base hx)) hcl hq
  obtain ⟨y, hy, hyq⟩ := hq'
  apply hmiss y hy
  have hmy : (p y).asIdeal = m := by
    show (p.base y).asIdeal = m
    rw [hyq]
  rw [hmy]
  refine hI.trans ?_
  exact sInf_le ⟨bot_le, hm⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedEmptyOfUniversallyClosedOfLeJacobsonStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_empty_of_isClosed_of_universallyClosed_of_le_jacobson : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), UniversallyClosed p → ∀ Z : Set X, IsClosed Z → (∀ x ∈ Z, ¬ I ≤ (p x).asIdeal) → Z = ∅ := by
  first | exact @GlobalTheory.closed_empty_of_universallyClosed_of_le_jacobson | exact GlobalTheory.closed_empty_of_universallyClosed_of_le_jacobson | (intros; apply GlobalTheory.closed_empty_of_universallyClosed_of_le_jacobson <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedPartialDerivConstMulReindex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedPartialDerivConstMulReindex
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem iterD_const_mul_reindex : ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (e : I ≃ J) (u : List I) (h : (J → ℂ) → ℂ) (A : ℂ) (z : I → ℂ), iterD u (fun z ↦ A * h (fun j ↦ z (e.symm j))) z = A * iterD (u.map e) h (fun j ↦ z (e.symm j)) := by
  intro I J _ _ _ _ e u h A z
  have key : ∀ v : List I, iterD v (fun z ↦ A * h (fun j ↦ z (e.symm j))) =
      fun z ↦ A * iterD (v.map e) h (fun j ↦ z (e.symm j)) := by
    intro v
    induction v with
    | nil => rfl
    | cons i v ih =>
      funext z
      show partialD i (iterD v _) z = A * partialD (e i) (iterD (v.map e) h) _
      rw [ih]
      simp only [partialD, lineDeriv]
      have hpath : (fun t : ℂ ↦ A * iterD (v.map e) h (fun j ↦ (z + t • (Pi.single i 1 : I → ℂ)) (e.symm j))) =
          fun t ↦ A * iterD (v.map e) h ((fun j ↦ z (e.symm j)) + t • (Pi.single (e i) 1 : J → ℂ)) := by
        funext t
        congr 2
        funext j
        simp [Pi.single_apply, Equiv.symm_apply_eq]
      rw [hpath, deriv_const_mul_field]
  exact congrFun (key u) z

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedPartialDerivConstMulReindexStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedPartialDeriv_const_mul_reindex : ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (e : I ≃ J) (u : List I) (h : (J → ℂ) → ℂ) (A : ℂ) (z : I → ℂ), iterD u (fun z ↦ A * h (fun j ↦ z (e.symm j))) z = A * iterD (u.map e) h (fun j ↦ z (e.symm j)) := by
  first | exact @GlobalTheory.HilbFam.iterD_const_mul_reindex | exact GlobalTheory.HilbFam.iterD_const_mul_reindex | (intros; apply GlobalTheory.HilbFam.iterD_const_mul_reindex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulMatSmulOneIff
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem mem_mulMat_smul_one_iff {F : Type} [Field F] [NumberField F] (L : Lat F) (c : ℤ) (v : Fin 2 → F) :
    v ∈ mulMat L (c • (1 : Matrix (Fin 2) (Fin 2) ℤ)) ↔ ∃ y ∈ L, v = (c : 𝓞 F) • y := by
  have h : ∀ y : Fin 2 → F,
      Matrix.vecMul y ((c • (1 : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → F)) = (c : 𝓞 F) • y := by
    intro y
    have hm : (c • (1 : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → F) = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
      ext i j
      rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [Int.cast_smul_eq_zsmul, hm, Matrix.vecMul_smul, Matrix.vecMul_one]
  unfold mulMat
  simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.vecMulLinear_apply, h]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

theorem twist_one_of_hasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F),
    HasLevel N L → twist N L 1 = L := by
  intro F _ _ _ N L hL
  have h1 : (1 : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ℤ)
      = (ZMod.cast (1 : ZMod N) : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  unfold twist
  rw [h1]
  apply le_antisymm
  · refine sup_le (fun v hv ↦ ?_) (fun v hv ↦ ?_)
    · obtain ⟨y, hy, rfl⟩ := (mem_mulMat_smul_one_iff _ _ _).1 hv
      exact L.smul_mem _ hy
    · obtain ⟨y, hy, rfl⟩ := (mem_mulMat_smul_one_iff _ _ _).1 hv
      simpa using hL.1 y hy
  · intro v hv
    by_cases hN : N = 1
    · subst hN
      refine Submodule.mem_sup_right ((mem_mulMat_smul_one_iff _ _ _).2 ⟨v, hL.2 hv, by simp⟩)
    · have hc : (ZMod.cast (1 : ZMod N) : ℤ) = 1 := by
        rcases N with _ | _ | N
        · rfl
        · exact absurd rfl hN
        · rw [ZMod.cast_eq_val, ZMod.val_one'' hN]; simp
      rw [hc]
      exact Submodule.mem_sup_left ((mem_mulMat_smul_one_iff _ _ _).2 ⟨v, hv, by simp⟩)

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeValueEqOfIsValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeValueEqOfIsValue
set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem isGVal_unique' {F : Type} [Field F] [NumberField F] {k : ℕ}
    {L : _root_.GlobalTheory.HilbFam.Lat F} {b a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ} {G G' : ℂ}
    (h : _root_.GlobalTheory.HilbFam.IsGVal k L b a G)
    (h' : _root_.GlobalTheory.HilbFam.IsGVal k L b a G') : G = G' := by
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨h₁', h₂'⟩ := h'
  by_cases hk : k = 2
  · subst hk
    obtain ⟨H, hH, hsum, rfl⟩ := h₂ rfl
    obtain ⟨H', hH', hsum', rfl⟩ := h₂' rfl
    have hU : IsOpen {σ : ℂ | -1 / 2 < σ.re} := isOpen_lt continuous_const Complex.continuous_re
    have hC : IsPreconnected {σ : ℂ | -1 / 2 < σ.re} := (convex_halfSpace_re_gt _).isPreconnected
    have hone : (1 : ℂ) ∈ {σ : ℂ | -1 / 2 < σ.re} := by
      simp only [Set.mem_setOf_eq, Complex.one_re]; norm_num
    have hzero : (0 : ℂ) ∈ {σ : ℂ | -1 / 2 < σ.re} := by
      simp only [Set.mem_setOf_eq, Complex.zero_re]; norm_num
    have hev : H =ᶠ[nhds 1] H' := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (0 : ℝ) < (1 : ℂ).re by simp)] with σ hσ
      exact (hsum σ hσ).unique (hsum' σ hσ)
    exact (hH.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hH'.analyticOnNhd hU) hC
      hone hev hzero
  · exact (h₁ hk).unique (h₁' hk)


set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.gval_eq_of_isGVal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F) (b a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (G : ℂ),
    _root_.GlobalTheory.HilbFam.IsGVal k L b a G → _root_.GlobalTheory.HilbFam.gval k L b a = G := by
  intro F _ _ _ k L b a G hG
  have h : ∃ G, _root_.GlobalTheory.HilbFam.IsGVal k L b a G := ⟨G, hG⟩
  rw [_root_.GlobalTheory.HilbFam.gval, dite_eq_left h]
  exact isGVal_unique' h.choose_spec hG

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeValueEqOfIsValueStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisensteinLatticeValue_eq_of_isValue : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L : Lat F) (b a : Emb F → ℂ) (G : ℂ), IsGVal k L b a G → gval k L b a = G := by
  first | exact @GlobalTheory.HilbFam.gval_eq_of_isGVal | exact GlobalTheory.HilbFam.gval_eq_of_isGVal | (intros; apply GlobalTheory.HilbFam.gval_eq_of_isGVal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousCofilteredAffineLimit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousCofilteredAffineLimit
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

abbrev isoSpecSp (X : Scheme.{0}) [IsAffine X] : sch.obj X ⟶ sp Γ(X, ⊤) := sch.map X.isoSpec.hom

theorem pull_isoSpecSp_inv (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (X : Scheme.{0}) [IsAffine X]
    (x : H R (sch.obj X) F n) : pull R (isoSpecSp X) F n (pull R (sch.map X.isoSpec.inv) F n x) = x := by
  rw [← pull_comp, ← sch.map_comp, Iso.hom_inv_id, sch.map_id, pull_id]

theorem pull_isoSpecSp_inv' (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (X : Scheme.{0}) [IsAffine X]
    (x : H R (sp Γ(X, ⊤)) F n) : pull R (sch.map X.isoSpec.inv) F n (pull R (isoSpecSp X) F n x) = x := by
  rw [← pull_comp, ← sch.map_comp, Iso.inv_hom_id, sch.map_id, pull_id]

theorem isoSpecSp_naturality {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    isoSpecSp X ≫ spMap f.appTop.hom = sch.map f ≫ isoSpecSp Y := by
  simp only [isoSpecSp, spMap, CommRingCat.ofHom_hom, ← sch.map_comp, Scheme.isoSpec_hom_naturality]

theorem pull_isoSpecSp_naturality (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (z : H R (sp Γ(Y, ⊤)) F n) :
    pull R (sch.map f) F n (pull R (isoSpecSp Y) F n z) = pull R (isoSpecSp X) F n (pull R (spMap f.appTop.hom) F n z) := by
  rw [← pull_comp, ← pull_comp, isoSpecSp_naturality]

theorem contCone_of_affine_limit : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i)) → ContCone R F (sch.mapCone c) := by
  intro R _ F hF I _ _ G c hc hG
  haveI : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let c' : Cocone (G ⋙ Scheme.Γ.rightOp).leftOp := coconeLeftOpOfCone (Scheme.Γ.rightOp.mapCone c)
  have hc' : IsColimit c' := isColimitCoconeLeftOpOfCone _ (isLimitOfPreserves Scheme.Γ.rightOp hc)
  have hb := GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary R F hF Iᵒᵖ _ c' hc'
  intro n
  obtain ⟨h1, h2⟩ := hb n
  refine ⟨fun x => ?_, fun i y hy => ?_⟩
  · obtain ⟨j, y', hy'⟩ := h1 (pull R (sch.map c.pt.isoSpec.inv) F n x)
    refine ⟨j.unop, pull R (isoSpecSp (G.obj j.unop)) F n y', ?_⟩
    change pull R (sch.map (c.π.app j.unop)) F n _ = x
    refine (pull_isoSpecSp_naturality R F n (X := c.pt) (Y := G.obj j.unop) (c.π.app j.unop) y').trans ?_
    change pull R (isoSpecSp c.pt) F n (pull R (spMap (c'.ι.app j).hom) F n y') = x
    rw [hy', pull_isoSpecSp_inv]
  · change pull R (sch.map (c.π.app i)) F n y = 0 at hy
    let y' : H R (sp Γ(G.obj i, ⊤)) F n := pull R (sch.map (G.obj i).isoSpec.inv) F n y
    have hyy : y = pull R (isoSpecSp (G.obj i)) F n y' := (pull_isoSpecSp_inv R F n _ y).symm
    have hz : pull R (spMap (c'.ι.app (op i)).hom) F n y' = 0 := by
      have e : pull R (isoSpecSp c.pt) F n (pull R (spMap (c.π.app i).appTop.hom) F n y') = 0 := by
        rw [← pull_isoSpecSp_naturality R F n (X := c.pt) (Y := G.obj i) (c.π.app i) y', ← hyy]
        exact hy
      have e2 := congrArg (pull R (sch.map c.pt.isoSpec.inv) F n) e
      rw [pull_isoSpecSp_inv', map_zero] at e2
      exact e2
    obtain ⟨k, f, hk⟩ := h2 (op i) y' hz
    refine ⟨k.unop, f.unop, ?_⟩
    change pull R (sch.map (G.map f.unop)) F n y = 0
    rw [hyy]
    refine (pull_isoSpecSp_naturality R F n (X := G.obj k.unop) (Y := G.obj i) (G.map f.unop) y').trans ?_
    change pull R (isoSpecSp (G.obj k.unop)) F n (pull R (spMap ((G ⋙ Scheme.Γ.rightOp).leftOp.map f).hom) F n y') = 0
    rw [hk]
    exact AddMonoidHom.map_zero _

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousCofilteredAffineLimitStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i)) → ContCone R F (sch.mapCone c) := by
  first
  | exact @GlobalTheory.EtC.contCone_of_affine_limit
  | exact GlobalTheory.EtC.contCone_of_affine_limit
  | (intros; apply GlobalTheory.EtC.contCone_of_affine_limit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountWordWithLetterMultiplicities
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem count_word_eq (I : Type) [Fintype I] [DecidableEq I] (κ : I → ℕ) (i : I) :
    (word κ).count i = κ i := by
  unfold word
  rw [List.count_flatMap]
  simp [List.count_replicate, Function.comp_def]

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPFlat
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.PDivGroup

theorem mulP_flat : ∀ (p : ℕ) (R : Type) [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) (n : ℕ),
    RingHom.Flat ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  intro p R _ G n
  obtain ⟨hassoc, hcounit, hsurj⟩ := G.transl_free n
  obtain ⟨-, -, hff, -⟩ := GlobalTheory.HopfQuot.finite_faithfullyFlat_ker (G.transl n) hassoc hcounit hsurj
  set B₀ := AlgHom.equalizer (G.transl n)
    (Algebra.TensorProduct.includeLeft : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1) with hB₀
  let f : G.A n →ₐ[R] B₀ := AlgHom.codRestrict (G.mulP n : G.A n →ₐ[R] G.A (n + 1)) B₀
    (fun a => by
      show G.transl n (G.mulP n a) = G.mulP n a ⊗ₜ[R] 1
      exact G.transl_mulP n a)
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => Test.mulP_injective G n (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨e, he⟩ := G.exists_mulP_eq_of_transl_eq n y.1 y.2
    exact ⟨e, Subtype.ext he⟩
  have h1 : RingHom.Flat (algebraMap B₀ (G.A (n + 1))) := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have h2 : RingHom.Flat (f : G.A n →+* B₀) := RingHom.Flat.of_bijective hf
  have h3 := RingHom.Flat.comp h2 h1
  convert h3 using 1
  exact RingHom.ext fun a => rfl
end GlobalTheory.PDivGroup
end
