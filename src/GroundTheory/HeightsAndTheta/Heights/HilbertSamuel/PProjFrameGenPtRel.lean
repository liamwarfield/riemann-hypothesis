module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeDegree
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameFibrePt

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameGenPtRel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section


open ProjFrameFibrePt in
theorem ProjFrameGenPtRel.proof : ProjFrameGenPtRel.Statement := by
  intro D Ω _ _ κ _ x e _ hF G
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro n hn
    have h1 : (C (n : ℤ) : MRing (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1))))) ∈ graphP x e := by
      rw [graphP, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_C, eq_intCast, Int.cast_natCast]
      exact hn
    rw [graphP, graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_C, eq_intCast, Int.cast_natCast,
      ← map_natCast (C : (MRing (GlobalTheory κ) ⧸ coordIdeal ℤ x) →+* MvPolynomial Unit _), C_eq_zero,
      ← map_natCast (Ideal.Quotient.mk (coordIdeal ℤ x)), Ideal.Quotient.eq_zero_iff_mem, coordIdeal,
      RingHom.mem_ker, map_natCast, ← map_natCast (Polynomial.C : Ω →+* Polynomial Ω), Polynomial.C_eq_zero] at h1
    exact_mod_cast h1
  ·
    have hker : ∀ h : MRing (GlobalTheory κ),
        aeval (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) h = 0 ↔ h ∈ coordIdeal ℤ x := by
      intro h
      constructor
      · intro h0
        have h2 : rename (fun p : Ix κ => aV D p.2) h ∈ graphP x e := by
          rw [graphP, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_rename]
          exact h0
        rwa [graphP, graphIdeal, RingHom.mem_ker, graphMap_rename_inl, C_eq_zero,
          Ideal.Quotient.eq_zero_iff_mem] at h2
      · intro hh
        exact aeval_inl_eq_zero G hh
    ext f
    have hu : f ∈ coordIdeal ℤ (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) ↔
        ∀ d, homogeneousComponent d f ∈ coordIdeal ℤ x := by
      rw [coordIdeal, RingHom.mem_ker, Polynomial.ext_iff]
      simp only [coeff_coneMap, Polynomial.coeff_zero, hker]
    rw [hu]
    constructor
    · intro h
      rw [← sum_homogeneousComponent f]
      exact Ideal.sum_mem _ fun d _ => h d
    · intro h d
      exact coordIdeal_isHomogIdeal ℤ x f h d
  ·
    intro k
    have h := x'_frame_mul G (e := e) k
    change G.x' (bV κ k) * G.x' (aV D (e 0).2) = G.x' (bV κ 0) * G.x' (aV D (e k).2)
    linear_combination -h
  ·
    apply le_antisymm
    · intro y hy
      rw [RingHom.mem_fieldRange] at hy
      obtain ⟨c, rfl⟩ := hy
      obtain ⟨f, g, _, rfl⟩ := G.gen c
      have key : ∀ h : MRing (GlobalTheory (Fin (D + 1))), algebraMap G.Φ G.Φ' (aeval G.x h) ∈
          Subfield.closure (Set.range fun k : Fin (D + 1) => G.x' ⟨Sum.inr (), k⟩) := by
        intro h
        induction h using MvPolynomial.induction_on with
        | C a =>
          rw [aeval_C, eq_intCast, map_intCast]
          exact intCast_mem _ a
        | add p q hp hq =>
          rw [map_add (f := _), map_add (f := _)]
          exact add_mem hp hq
        | mul_X p i hp =>
          rw [map_mul, map_mul, aeval_X]
          exact mul_mem hp (Subfield.subset_closure ⟨i.2, G.compat i⟩)
      rw [map_div₀]
      exact div_mem (key f) (key g)
    · rw [Subfield.closure_le]
      rintro _ ⟨k, rfl⟩
      exact ⟨G.x ⟨(), k⟩, (G.compat ⟨(), k⟩).symm⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeNullModP
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

theorem exists_natMul_mem_of_map_rat_mem {σ : Type} (I : Ideal (MvPolynomial σ ℤ)) (f : MvPolynomial σ ℤ)
    (hf : map (Int.castRingHom ℚ) f ∈ Ideal.map (map (Int.castRingHom ℚ)) I) :
    ∃ M : ℕ, M ≠ 0 ∧ (M : MvPolynomial σ ℤ) * f ∈ I := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := σ) (R := ℤ) (S := ℚ)
  have hA : (map (Int.castRingHom ℚ) : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ) =
      algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ) := by
    rw [algebraMap_def, algebraMap_int_eq]
  rw [hA, IsLocalization.mem_map_algebraMap_iff ((nonZeroDivisors ℤ).map (C (σ := σ)))] at hf
  obtain ⟨⟨⟨g, hg⟩, ⟨_, m, hm, rfl⟩⟩, h⟩ := hf
  have hinj : Function.Injective (algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ)) := by
    rw [← hA]; exact map_injective _ Int.cast_injective
  have h' : C m * f = g := by rw [mul_comm]; exact hinj (by simpa using h)
  obtain ⟨t, ht⟩ : m ∣ (m.natAbs : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
  refine ⟨m.natAbs, Int.natAbs_ne_zero.mpr (nonZeroDivisors.ne_zero hm), ?_⟩
  have : (m.natAbs : MvPolynomial σ ℤ) = C (m.natAbs : ℤ) := (map_natCast C _).symm
  rw [this, ht, C_mul, mul_comm (C m), mul_assoc, h']
  exact I.mul_mem_left _ hg

theorem PullConeNullModP.proof : PullConeNullModP.Statement := by
  classical
  intro K _ ι _ Ω _ y D L hL p hp hbad
  have : Fact p.Prime := ⟨hp⟩
  have hQ : coneNullIdeal y L = (coneNullIdealZ y L).map (map (Int.castRingHom ℚ)) := by
    rw [coneNullIdeal, coneNullIdealZ, Ideal.map_span, Set.image_union, ← Set.range_comp]; rfl
  set I := coneNullIdealZ y L
  let π := Ideal.Quotient.mk I
  obtain ⟨N₁, hN₁⟩ := PullConeNull.proof K ι Ω y D L hL

  have key : ∀ c : ∀ k, ι k, ∃ N M : ℕ, ¬ p ∣ M ∧
      (M : MRing ι ⧸ I) * π (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N = 0 := by
    intro c
    set u := π (∏ k, (X ⟨k, c k⟩ : MRing ι))

    obtain ⟨M₁, hM₁, h₁⟩ := exists_natMul_mem_of_map_rat_mem I ((∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N₁)
      (by rw [← hQ]; simpa [map_prod] using hN₁ c)
    have e₁ : (M₁ : MRing ι ⧸ I) * u ^ N₁ = 0 := by
      rw [← map_natCast π, ← map_pow, ← map_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h₁

    obtain ⟨N₂, h, e₂⟩ : ∃ N₂ h, u ^ N₂ = (p : MRing ι ⧸ I) * h := by
      let φ : MRing ι →+* MvPolynomial (Σ k, ι k) (ZMod p) := map (Int.castRingHom (ZMod p))
      have hrad : φ (∏ k, (X ⟨k, c k⟩ : MRing ι)) ∈ (I.map φ).radical := by
        rw [← IsJacobsonRing.out inferInstance (Ideal.radical_isRadical (I.map φ)), Ideal.jacobson, Submodule.mem_sInf]
        rintro m ⟨hJm, hm⟩
        letI := Ideal.Quotient.field m
        have := finite_of_finite_type_of_isJacobsonRing (ZMod p) (MvPolynomial (Σ k, ι k) (ZMod p) ⧸ m)
        let ψ := IsAlgClosed.lift (R := ZMod p) (M := AlgebraicClosure (ZMod p))
          (S := MvPolynomial (Σ k, ι k) (ZMod p) ⧸ m)
        let z : (Σ k, ι k) → AlgebraicClosure (ZMod p) := fun q => ψ (Ideal.Quotient.mk m (X q))
        have hev : ∀ f : MRing ι, eval z (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f) =
            ψ (Ideal.Quotient.mk m (φ f)) := by
          intro f
          have e : (eval z).comp (map (Int.castRingHom (AlgebraicClosure (ZMod p)))) =
              ((ψ : _ →+* AlgebraicClosure (ZMod p)).comp (Ideal.Quotient.mk m)).comp φ := by
            refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
            · exact RingHom.congr_fun (RingHom.ext_int
                (((eval z).comp (map (Int.castRingHom (AlgebraicClosure (ZMod p))))).comp C)
                ((((ψ : _ →+* AlgebraicClosure (ZMod p)).comp (Ideal.Quotient.mk m)).comp φ).comp C)) r
            · simp [z, φ]
          exact RingHom.congr_fun e f
        have hker : ∀ f : MRing ι, f ∈ I → ψ (Ideal.Quotient.mk m (φ f)) = 0 := fun f hf => by
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hJm (Ideal.le_radical (Ideal.mem_map_of_mem φ hf))), map_zero]
        by_contra hc
        refine hbad ⟨z, fun k => ⟨c k, fun h0 => hc ?_⟩, fun f hf => ?_, fun j => ?_⟩
        · rw [map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
          refine Ideal.mul_mem_right _ m (Ideal.Quotient.eq_zero_iff_mem.mp (ψ.injective ?_))
          simpa [z, φ] using h0
        · rw [hev]; exact hker f (Ideal.subset_span (Or.inl hf))
        · rw [hev]; exact hker _ (Ideal.subset_span (Or.inr ⟨j, rfl⟩))
      obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
      rw [← map_pow, ← Ideal.mem_comap,
        Ideal.comap_map_of_surjective φ (map_surjective _ ZMod.intCast_surjective)] at hn
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hn
      have hb' : b ∈ RingHom.ker φ := by simpa [RingHom.mem_ker] using hb
      rw [ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
        Ideal.mem_span_singleton'] at hb'
      obtain ⟨h, rfl⟩ := hb'
      refine ⟨n, π h, ?_⟩
      rw [← map_pow, ← hab, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, map_mul, map_natCast C p,
        map_natCast, mul_comm]

    obtain ⟨a, M₀, hM₀, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM₁ p hp.ne_one
    refine ⟨a * N₂ + N₁, M₀, hM₀, ?_⟩
    rw [pow_add, pow_mul', e₂, mul_pow]
    push_cast at e₁
    linear_combination h ^ a * e₁
  choose Nc Mc hMc hc using key
  refine ⟨Finset.univ.sup Nc, ∏ c, Mc c, ?_, fun c => ?_⟩
  · exact fun hdvd => (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd |>.elim fun c ⟨_, h⟩ => hMc c h
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ c),
      ← Nat.add_sub_cancel' (Finset.le_sup (f := Nc) (Finset.mem_univ c)), pow_add]
    push_cast
    linear_combination ((∏ c' ∈ Finset.univ.erase c, (Mc c' : MRing ι ⧸ I)) *
      π (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ (Finset.univ.sup Nc - Nc c)) * hc c

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockStepBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Module

noncomputable section

namespace TwoBlockStepBound

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem relIndex_le_pow {H K : Submodule ℤ Ω} [Module.Finite ℤ K] {N : ℕ} (hN : 0 < N)
    (hNK : ∀ u ∈ K, (N : Ω) * u ∈ H) :
    H.toAddSubgroup.relIndex K.toAddSubgroup ≠ 0 ∧
      H.toAddSubgroup.relIndex K.toAddSubgroup ≤ N ^ finrank ℤ K := by
  have : Module.Finite ℤ (AddSubgroup.toIntSubmodule K.toAddSubgroup) := ‹Module.Finite ℤ K›
  have : Module.Free ℤ (AddSubgroup.toIntSubmodule K.toAddSubgroup) := Module.free_of_finite_type_torsion_free'
  have key := AddSubgroup.relIndex_map_nsmul N K.toAddSubgroup
  have hsub : K.toAddSubgroup.map (nsmulAddMonoidHom (α := Ω) N) ≤ H.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [nsmul_eq_mul] using hNK y hy
  have hne : (K.toAddSubgroup.map (nsmulAddMonoidHom (α := Ω) N)).relIndex K.toAddSubgroup ≠ 0 := by
    rw [key]
    exact pow_ne_zero _ hN.ne'
  refine ⟨fun h0 => hne (AddSubgroup.relIndex_eq_zero_of_le_left hsub h0), ?_⟩
  calc H.toAddSubgroup.relIndex K.toAddSubgroup ≤ _ := AddSubgroup.relIndex_le_of_le_left hsub hne
    _ = N ^ finrank ℤ K := key

theorem pow_mul_mem_sec {x x' : Ix κ → Ω} {M : ℕ} (hM : ∀ s ∈ sec ℤ x' 1, (M : Ω) * s ∈ sec ℤ x 1) :
    ∀ n : ℕ, ∀ s ∈ sec ℤ x' n, (M : Ω) ^ n * s ∈ sec ℤ x n
  | 0, s, hs => by
    rw [sec_zero'] at hs ⊢
    simpa using hs
  | n + 1, s, hs => by
    rw [← sec_mul_sec] at hs ⊢
    induction hs using Submodule.mul_induction_on' with
    | mem_mul_mem u hu v hv =>
      have := Submodule.mul_mem_mul (pow_mul_mem_sec hM n u hu) (hM v hv)
      convert this using 1
      ring
    | add u _ v _ hu hv =>
      rw [mul_add]
      exact add_mem hu hv

theorem exists_finrank_sec_le (hRank : RankOfSections.Statement) {x : Ix κ → Ω} {D : ℕ}
    (hX : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ m : ℕ, 1 ≤ m → (finrank ℤ (sec ℤ x m) : ℝ) ≤ R * (m : ℝ) ^ D := by
  obtain ⟨hqP, hqd⟩ := GenericFibre.proof Ω κ x D hX
  obtain ⟨C, hC⟩ := hRank κ _ D hqP hqd
  set δ : ℝ := (GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ
    ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ : Fin D => fun _ => (1 : ℤ)) : ℝ)
  refine ⟨|δ| + |C| * 2 ^ D, by positivity, fun m hm => ?_⟩
  have e : (GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory κ)
      ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (m : ℤ)) : ℝ) =
      (finrank ℤ (sec ℤ x m) : ℝ) := by exact_mod_cast SectionsRank.proof Ω κ x m
  have h := (abs_le.mp (hC m)).2
  rw [e] at h
  have ht : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℝ) ≤ (m : ℝ) ^ D := by positivity
  have h1 : ((m : ℝ) + 1) ^ ((D : ℝ) - 1) ≤ ((m : ℝ) + 1) ^ D := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : ((m : ℝ) + 1) ^ D ≤ 2 ^ D * (m : ℝ) ^ D := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) D
  have h3 : δ * (m : ℝ) ^ D / D.factorial ≤ |δ| * (m : ℝ) ^ D := by
    have hf : (1 : ℝ) ≤ D.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero D)
    rw [div_le_iff₀ (by linarith)]
    calc δ * (m : ℝ) ^ D ≤ |δ| * (m : ℝ) ^ D := mul_le_mul_of_nonneg_right (le_abs_self δ) hp
      _ ≤ |δ| * (m : ℝ) ^ D * D.factorial := le_mul_of_one_le_right (by positivity) hf
  have h4 : C * ((m : ℝ) + 1) ^ ((D : ℝ) - 1) ≤ |C| * (2 ^ D * (m : ℝ) ^ D) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg C))
  nlinarith

end TwoBlockStepBound


open TwoBlockStepBound in
theorem TwoBlockStepBound.proof (hRank : RankOfSections.Statement) : TwoBlockStepBound.Statement := by
  intro D Ω _ _ κ _ x B hX _ _ hsp
  set x' := matAct B x
  obtain ⟨M, hM0, hM⟩ := ChangeOfLatticeNested.exists_mul_mem_sec_one x B
  obtain ⟨R, hR0, hR⟩ := exists_finrank_sec_le hRank hX
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM0)
  refine ⟨R * Real.log M, fun a b => ?_⟩
  have hsp1 : sec ℤ x 1 ≤ sec ℤ x' 1 := by
    rw [sec_one', sec_one']
    exact hsp
  have eH : sec ℤ x (a + 1) * sec ℤ x' b = sec ℤ x a * sec ℤ x' b * sec ℤ x 1 := by
    rw [← sec_mul_sec x a 1, mul_right_comm]
  have eK : sec ℤ x a * sec ℤ x' (b + 1) = sec ℤ x a * sec ℤ x' b * sec ℤ x' 1 := by
    rw [← sec_mul_sec x' b 1, mul_assoc]
  have hKQ : sec ℤ x a * sec ℤ x' (b + 1) ≤ sec ℤ x' (a + b + 1) := by
    rw [add_assoc, ← sec_mul_sec x' a (b + 1)]
    exact mul_le_mul' (ChangeOfLattice.sec_mono hsp a) le_rfl
  have : Module.Finite ℤ (sec ℤ x a * sec ℤ x' (b + 1)) :=
    Module.Finite.iff_fg.mpr ((sec_fg x a).mul (sec_fg x' (b + 1)))
  obtain ⟨hne, hle⟩ := relIndex_le_pow (H := sec ℤ x (a + 1) * sec ℤ x' b)
    (K := sec ℤ x a * sec ℤ x' (b + 1)) hM0 (by rw [eH, eK]; exact mul_mem_of_forall hM _)
  have hMn : ((M : Ω) ^ (a + b + 1)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hM0.ne')
  let f := (LinearMap.mulLeft ℤ ((M : Ω) ^ (a + b + 1))).restrict (pow_mul_mem_sec hM (a + b + 1))
  have hf : Function.Injective f := fun s t hst =>
    Subtype.ext (mul_left_cancel₀ hMn (congrArg Subtype.val hst))
  have hrk : finrank ℤ (sec ℤ x a * sec ℤ x' (b + 1)) ≤ finrank ℤ (sec ℤ x (a + b + 1)) :=
    (Submodule.finrank_mono hKQ).trans (LinearMap.finrank_le_finrank_of_injective hf)
  have hpos : (0 : ℝ) ≤ twoBlockStep x x' a b :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne)
  have ht : ((a + b : ℝ) + 1) = ((a + b + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [abs_of_nonneg hpos, ht]
  unfold twoBlockStep
  calc Real.log ((sec ℤ x (a + 1) * sec ℤ x' b).toAddSubgroup.relIndex (sec ℤ x a * sec ℤ x' (b + 1)).toAddSubgroup)
      ≤ Real.log ((M ^ finrank ℤ (sec ℤ x a * sec ℤ x' (b + 1)) : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hne) (by exact_mod_cast hle)
    _ = finrank ℤ (sec ℤ x a * sec ℤ x' (b + 1)) * Real.log M := by
        push_cast
        rw [Real.log_pow]
    _ ≤ finrank ℤ (sec ℤ x (a + b + 1)) * Real.log M :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hrk) hlogM
    _ ≤ R * ((a + b + 1 : ℕ) : ℝ) ^ D * Real.log M :=
        mul_le_mul_of_nonneg_right (hR _ (by omega)) hlogM
    _ = R * Real.log M * ((a + b + 1 : ℕ) : ℝ) ^ D := by ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
