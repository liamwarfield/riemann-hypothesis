module

public import GroundTheory.AutomorphicForms.TraceClass
public import GroundTheory.AutomorphicForms.SmoothRep
public import GroundTheory.AutomorphicForms.DixmierMalliavinBasic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsCharNeOne

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.TraceNormComp
namespace GroundTheory.Automorphic

open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem eq_zero_of_hsNormSq_eq_zero {T : H →L[ℂ] H} (h : hsNormSq T = 0) : T = 0 := by
  ext x
  have hx := enorm_apply_sq_le T x
  rw [h, zero_mul, nonpos_iff_eq_zero, pow_eq_zero_iff two_ne_zero, enorm_eq_zero] at hx
  simpa using hx

theorem eq_zero_of_hsNorm_eq_zero {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (h : hsNorm T = 0) :
    T = 0 := by
  refine eq_zero_of_hsNormSq_eq_zero ?_
  rw [hsNorm, Real.sqrt_eq_zero ENNReal.toReal_nonneg, ENNReal.toReal_eq_zero_iff] at h
  exact h.resolve_right hT.ne

theorem traceNorm_comp_le {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) : (traceNorm (A.comp B)).toReal ≤ hsNorm A * hsNorm B := by
  have key : ∀ t : ℝ, 0 < t → 2 * (traceNorm (A.comp B)).toReal ≤
      t ^ 2 * hsNorm A ^ 2 + (t⁻¹) ^ 2 * hsNorm B ^ 2 := by
    intro t ht
    have hAB : A.comp B = ((t : ℂ) • A).comp (((t⁻¹ : ℝ) : ℂ) • B) := by
      ext x
      simp only [comp_apply, smul_apply, map_smul, smul_smul]
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne', Complex.ofReal_one, one_smul]
    have h := two_mul_traceNorm_comp_le ((t : ℂ) • A) (((t⁻¹ : ℝ) : ℂ) • B)
    rw [← hAB, hsNormSq_smul, hsNormSq_smul] at h
    have hfin : ‖(t : ℂ)‖ₑ ^ 2 * hsNormSq A + ‖((t⁻¹ : ℝ) : ℂ)‖ₑ ^ 2 * hsNormSq B ≠ ∞ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) hA.ne, ENNReal.mul_ne_top (by simp) hB.ne⟩
    have h' := ENNReal.toReal_mono hfin h
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) hA.ne)
      (ENNReal.mul_ne_top (by simp) hB.ne), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_pow, toReal_enorm, toReal_enorm, ← hsNorm_sq,
      ← hsNorm_sq, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos ht, abs_of_pos (inv_pos.2 ht)] at h'
    simpa using h'
  rcases (hsNorm_nonneg A).eq_or_lt with ha | ha
  · rw [eq_zero_of_hsNorm_eq_zero hA ha.symm, zero_comp, traceNorm_zero, ENNReal.toReal_zero]
    exact mul_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _)
  rcases (hsNorm_nonneg B).eq_or_lt with hb | hb
  · rw [eq_zero_of_hsNorm_eq_zero hB hb.symm, comp_zero, traceNorm_zero, ENNReal.toReal_zero]
    exact mul_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _)
  have h := key (Real.sqrt (hsNorm B / hsNorm A)) (Real.sqrt_pos.2 (div_pos hb ha))
  rw [inv_pow, Real.sq_sqrt (div_nonneg hb.le ha.le)] at h
  have e : hsNorm B / hsNorm A * hsNorm A ^ 2 + (hsNorm B / hsNorm A)⁻¹ * hsNorm B ^ 2 =
      2 * (hsNorm A * hsNorm B) := by
    field_simp
    ring
  linarith

end

end GroundTheory.Automorphic
end

section -- merged from GroundTheory.AutomorphicForms.SmoothRepSchur
noncomputable section

namespace GroundTheory.Automorphic

open Polynomial Cardinal

section Schur

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

theorem exists_ne_zero_of_isIrreducible [ρ.IsIrreducible] : ∃ v : V, v ≠ 0 := by
  by_contra h
  push Not at h
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  change (⊥ : Submodule ℂ V) = ⊤
  ext v
  simp [h v]

theorem injective_of_ne_zero [ρ.IsIrreducible] {f : Representation.IntertwiningMap ρ ρ}
    (hf : f ≠ 0) : Function.Injective f :=
  ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf).1

theorem exists_eq_algebraMap_of_aeval_eq_zero [ρ.IsIrreducible]
    (φ : Representation.IntertwiningMap ρ ρ) {p : ℂ[X]} (hp : p ≠ 0) (hφ : aeval φ p = 0) :
    ∃ c : ℂ, φ = algebraMap ℂ (Representation.IntertwiningMap ρ ρ) c := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := ρ)
  induction hn : p.natDegree generalizing p with
  | zero =>
    rw [Polynomial.natDegree_eq_zero] at hn
    obtain ⟨a, rfl⟩ := hn
    have ha : a ≠ 0 := by
      rintro rfl
      simp at hp
    rw [aeval_C] at hφ
    have h1 : a • v = 0 := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hφ
    exact absurd h1 (smul_ne_zero ha hv)
  | succ n ih =>
    have hdeg : p.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hp, hn]
      exact_mod_cast Nat.succ_ne_zero n
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hdeg
    set q := p /ₘ (X - C r)
    have hpq : (X - C r) * q = p := mul_divByMonic_eq_iff_isRoot.2 hr
    have hq : q ≠ 0 := by
      intro hq
      rw [hq, mul_zero] at hpq
      exact hp hpq.symm
    have hqdeg : q.natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C, hn]
      rfl
    by_cases hφr : φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) r = 0
    · exact ⟨r, sub_eq_zero.1 hφr⟩
    · refine ih hq ?_ hqdeg
      have hinj := injective_of_ne_zero hφr
      rw [← hpq, map_mul, map_sub, aeval_X, aeval_C] at hφ
      refine DFunLike.ext _ _ fun w => hinj ?_
      have h1 := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f w) hφ
      change (φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) r) ((aeval φ q) w) =
        (φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) r) 0
      rw [map_zero]
      exact h1

theorem algebraMap_intertwiningMap_bijective_of_rank_le_aleph0 [ρ.IsIrreducible]
    (hV : Module.rank ℂ V ≤ ℵ₀) :
    Function.Bijective (algebraMap ℂ (Representation.IntertwiningMap ρ ρ)) := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := ρ)
  constructor
  · intro a b hab
    have h1 : a • v = b • v :=
      congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hab
    exact smul_left_injective ℂ hv h1
  · intro φ
    by_contra hne
    push Not at hne
    have hsub : ∀ c : ℂ, φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) c ≠ 0 :=
      fun c h => hne c (sub_eq_zero.1 h).symm
    have htr : ∀ p : ℂ[X], p ≠ 0 → aeval φ p ≠ 0 := fun p hp h => by
      obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_aeval_eq_zero φ hp h
      exact hne c hc.symm
    have hsurj : ∀ c : ℂ,
        Function.Surjective (φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) c) :=
      fun c => ((Representation.IsIrreducible.bijective_or_eq_zero _).resolve_right (hsub c)).2
    choose w hw using fun c => hsurj c v
    have sum_apply : ∀ (s : Finset ℂ) (f : ℂ → Representation.IntertwiningMap ρ ρ) (x : V),
        (∑ j ∈ s, f j) x = ∑ j ∈ s, f j x := by
      intro s f x
      have h1 := congrFun (map_sum (Representation.IntertwiningMap.coeFnAddMonoidHom ρ ρ) f s) x
      rw [Finset.sum_apply] at h1
      exact h1
    have hli : LinearIndependent ℂ w := by
      rw [linearIndependent_iff']
      intro s a hsum i hi
      have key : ∀ j ∈ s, aeval φ (∏ k ∈ s, (X - C k)) (w j) =
          aeval φ (∏ k ∈ s.erase j, (X - C k)) v := by
        intro j hj
        rw [← Finset.prod_erase_mul _ _ hj, map_mul]
        change (aeval φ (∏ k ∈ s.erase j, (X - C k))) ((aeval φ (X - C j)) (w j)) = _
        rw [map_sub, aeval_X, aeval_C, hw j]
      set P : ℂ[X] := ∑ j ∈ s, a j • ∏ k ∈ s.erase j, (X - C k) with hPdef
      have hP : aeval φ P v = 0 := by
        have h0 := congrArg (aeval φ (∏ k ∈ s, (X - C k))) hsum
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_zero] at h0
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hPdef, map_sum, sum_apply]
        rw [← h0]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [map_smul, map_smul, key j hj]
        rfl
      have hP0 : P = 0 := by
        by_contra hP0
        exact hv (injective_of_ne_zero (htr P hP0) (hP.trans (map_zero _).symm))
      have h1 := congrArg (Polynomial.eval i) hP0
      rw [hPdef, eval_finsetSum, eval_zero, Finset.sum_eq_single i] at h1
      · rw [eval_smul, eval_prod, smul_eq_mul] at h1
        refine (mul_eq_zero.1 h1).resolve_right ?_
        refine Finset.prod_ne_zero_iff.2 fun k hk => ?_
        rw [eval_sub, eval_X, eval_C]
        exact sub_ne_zero.2 (Finset.ne_of_mem_erase hk).symm
      · intro j _ hji
        rw [eval_smul, eval_prod, Finset.prod_eq_zero (i := i) (Finset.mem_erase.2 ⟨Ne.symm hji, hi⟩)
          (by rw [eval_sub, eval_X, eval_C, sub_self]), smul_zero]
      · intro h
        exact absurd hi h
    have h1 := hli.cardinal_lift_le_rank
    rw [Cardinal.mk_complex, Cardinal.lift_continuum] at h1
    have h2 : Cardinal.lift.{0} (Module.rank ℂ V) ≤ ℵ₀ := Cardinal.lift_le_aleph0.2 hV
    exact (not_le.2 Cardinal.aleph0_lt_continuum) (h1.trans h2)

end Schur

section Smooth

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace.SeparableSpace G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

theorem rank_le_aleph0_of_isSmooth (hρ : IsSmooth ρ) [ρ.IsIrreducible] :
    Module.rank ℂ V ≤ ℵ₀ := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := ρ)
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense G
  have hstable : ∀ g : G, Submodule.span ℂ (Set.range fun h : G => ρ h v) ≤
      (Submodule.span ℂ (Set.range fun h : G => ρ h v)).comap (ρ g) := by
    intro g
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span ⟨g * h, by simp [map_mul, Module.End.mul_apply]⟩
  let W : Subrepresentation ρ :=
    ⟨Submodule.span ℂ (Set.range fun h : G => ρ h v), fun g _ hx => hstable g hx⟩
  have hW : W = ⊤ := (eq_bot_or_eq_top W).resolve_left fun h => hv (by
    have hvW : v ∈ W.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
    rw [h] at hvW
    exact (Submodule.mem_bot ℂ).1 hvW)
  have hspan : Submodule.span ℂ (Set.range fun h : G => ρ h v) = ⊤ :=
    congrArg Subrepresentation.toSubmodule hW
  have hsub : Set.range (fun h : G => ρ h v) ⊆ Set.range (fun d : D => ρ (d : G) v) := by
    rintro _ ⟨g, rfl⟩
    have hU : IsOpen ((fun x : G => g⁻¹ * x) ⁻¹' (stabilizerOf ρ v : Set G)) :=
      (hρ v).preimage (by fun_prop)
    obtain ⟨d, hdD, hdU⟩ := hDd.exists_mem_open hU ⟨g, by simp⟩
    refine ⟨⟨d, hdD⟩, ?_⟩
    have hd : ρ (g⁻¹ * d) v = v := hdU
    change ρ d v = ρ g v
    conv_rhs => rw [← hd]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have htop : Submodule.span ℂ (Set.range fun d : D => ρ (d : G) v) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    exact Submodule.span_mono hsub
  have : Countable D := hDc.to_subtype
  have : Countable (Set.range fun d : D => ρ (d : G) v) := (Set.countable_range _).to_subtype
  calc Module.rank ℂ V = Module.rank ℂ (⊤ : Submodule ℂ V) := (rank_top ℂ V).symm
    _ = Module.rank ℂ (Submodule.span ℂ (Set.range fun d : D => ρ (d : G) v)) := by rw [htop]
    _ ≤ #(Set.range fun d : D => ρ (d : G) v) := rank_span_le _
    _ ≤ ℵ₀ := Cardinal.mk_le_aleph0

theorem algebraMap_intertwiningMap_bijective_of_isSmooth (hρ : IsSmooth ρ) [ρ.IsIrreducible] :
    Function.Bijective (algebraMap ℂ (Representation.IntertwiningMap ρ ρ)) :=
  algebraMap_intertwiningMap_bijective_of_rank_le_aleph0 (rank_le_aleph0_of_isSmooth hρ)

theorem exists_central_character (hρ : IsSmooth ρ) [ρ.IsIrreducible] {z : G}
    (hz : z ∈ Submonoid.center G) : ∃ c : ℂ, ∀ v : V, ρ z v = c • v := by
  obtain ⟨c, hc⟩ := (algebraMap_intertwiningMap_bijective_of_isSmooth hρ).2
    (Representation.IntertwiningMap.centralMul ρ z hz)
  exact ⟨c, fun v => (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hc).symm⟩

end Smooth

end GroundTheory.Automorphic
end
end

section -- merged from GroundTheory.AutomorphicForms.CompactAbelianCharacters
set_option maxSynthPendingDepth 1

open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace GroundTheory.Automorphic.CompactAbelianFourier

noncomputable section

set_option linter.unusedSectionVars false

variable {C : Type*} [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C]
  [T2Space C]

section Metrizable

variable [SecondCountableTopology C] [MeasurableSpace C] [BorelSpace C]
  (μ : Measure C) [μ.IsHaarMeasure]

def transl (h : C) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x => h * x) (measurePreserving_mul_left μ h)).toContinuousLinearMap

variable (ψ : C(C, ℝ))


end Metrizable

theorem exists_char_ne_one {g : C} (hg : g ≠ 1) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 :=
  _root_.UpperTheory.Reformulated.B.CharactersSeparatePoints.exists_char_ne_one hg

theorem exists_char_ne {x y : C} (hxy : x ≠ y) : ∃ χ : C →ₜ* Circle, χ x ≠ χ y := by
  obtain ⟨χ, hχ⟩ := exists_char_ne_one (g := x * y⁻¹) (fun h => hxy (mul_inv_eq_one.1 h))
  refine ⟨χ, fun h => hχ ?_⟩
  rw [map_mul, map_inv, h, mul_inv_cancel]

def charCM (χ : C →ₜ* Circle) : C(C, ℂ) := ⟨fun x => (χ x : ℂ), continuous_subtype_val.comp χ.continuous⟩

theorem charCM_apply (χ : C →ₜ* Circle) (x : C) : charCM χ x = (χ x : ℂ) := rfl

theorem charCM_mul (χ χ' : C →ₜ* Circle) : charCM (χ * χ') = charCM χ * charCM χ' := by
  ext x
  simp [charCM_apply]

theorem charCM_one : charCM (1 : C →ₜ* Circle) = 1 := by
  ext x
  simp [charCM_apply]

theorem star_charCM (χ : C →ₜ* Circle) : star (charCM χ) = charCM χ⁻¹ := by
  ext x
  change conj ((χ x : Circle) : ℂ) = (((χ x)⁻¹ : Circle) : ℂ)
  rw [Circle.coe_inv_eq_conj]

def charAlgebra : StarSubalgebra ℂ C(C, ℂ) :=
  { (Submodule.span ℂ (Set.range (charCM (C := C)))).toSubalgebra
      (Submodule.subset_span ⟨1, charCM_one⟩)
      (fun a b ha hb => by
        induction ha using Submodule.span_induction with
        | mem x hx =>
          induction hb using Submodule.span_induction with
          | mem y hy =>
            obtain ⟨χ, rfl⟩ := hx
            obtain ⟨χ', rfl⟩ := hy
            exact Submodule.subset_span ⟨χ * χ', charCM_mul χ χ'⟩
          | zero => rw [mul_zero]; exact Submodule.zero_mem _
          | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
          | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
        | zero => rw [zero_mul]; exact Submodule.zero_mem _
        | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
        | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx) with
    star_mem' := fun {a} ha => by
      change a ∈ Submodule.span ℂ (Set.range (charCM (C := C))) at ha
      change star a ∈ Submodule.span ℂ (Set.range (charCM (C := C)))
      induction ha using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨χ, rfl⟩ := hx
        exact Submodule.subset_span ⟨χ⁻¹, (star_charCM χ).symm⟩
      | zero => rw [star_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx }

theorem charAlgebra_separatesPoints : (charAlgebra (C := C)).SeparatesPoints := by
  intro x y hxy
  obtain ⟨χ, hχ⟩ := exists_char_ne hxy
  exact ⟨charCM χ, ⟨charCM χ, Submodule.subset_span ⟨χ, rfl⟩, rfl⟩, fun h => hχ (Circle.coe_injective h)⟩

theorem span_charCM_dense :
    (Submodule.span ℂ (Set.range (charCM (C := C)))).topologicalClosure = ⊤ := by
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (charAlgebra_separatesPoints (C := C))
  rw [eq_top_iff]
  intro f _
  have hf : f ∈ (charAlgebra (C := C)).topologicalClosure := by rw [h]; trivial
  exact hf

section L2

variable [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure]

variable [IsProbabilityMeasure μ]

end L2

end

end GroundTheory.Automorphic.CompactAbelianFourier
end

section -- merged from GroundTheory.AutomorphicForms.SmoothRepContragredient
noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology

section General

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)

theorem dual_apply_apply (g : G) (f : Module.Dual ℂ V) (v : V) :
    Representation.dual ρ g f v = f (ρ g⁻¹ v) := rfl


variable {ρ} in
theorem mem_fixedVectors_dual {H : Subgroup G} {f : Module.Dual ℂ V} :
    f ∈ fixedVectors (Representation.dual ρ) H ↔ ∀ h ∈ H, ∀ v, f (ρ h v) = f v := by
  constructor
  · intro hf h hh v
    have := LinearMap.congr_fun (hf h⁻¹ (inv_mem hh)) v
    rwa [dual_apply_apply, inv_inv] at this
  · intro hf h hh
    ext v
    rw [dual_apply_apply]
    exact hf _ (inv_mem hh) v

variable [TopologicalSpace G] [IsTopologicalGroup G]


variable {ρ} in
theorem mem_smoothVectors_of_mem_fixedVectors {H : Subgroup G} (hH : IsOpen (H : Set G))
    {v : V} (hv : v ∈ fixedVectors ρ H) : v ∈ smoothVectors ρ :=
  Subgroup.isOpen_mono (mem_fixedVectors_iff_le.1 hv) hH

variable {ρ} in
theorem mem_fixedVectors_smoothPart {H : Subgroup G} {x : smoothVectors ρ} :
    x ∈ fixedVectors (smoothPart ρ) H ↔ (x : V) ∈ fixedVectors ρ H := by
  simp only [mem_fixedVectors, Subtype.ext_iff, coe_smoothPart_apply]

def contragredient : Representation ℂ G (smoothVectors (Representation.dual ρ)) :=
  smoothPart (Representation.dual ρ)

theorem contragredient_apply_apply (g : G) (x : smoothVectors (Representation.dual ρ)) (v : V) :
    ((contragredient ρ g x : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v =
      (x : Module.Dual ℂ V) (ρ g⁻¹ v) := rfl

theorem isSmooth_contragredient : IsSmooth (contragredient ρ) :=
  isSmooth_smoothPart _

variable {ρ} in
theorem mem_fixedVectors_contragredient {H : Subgroup G}
    {x : smoothVectors (Representation.dual ρ)} :
    x ∈ fixedVectors (contragredient ρ) H ↔
      ∀ h ∈ H, ∀ v, (x : Module.Dual ℂ V) (ρ h v) = (x : Module.Dual ℂ V) v :=
  mem_fixedVectors_smoothPart.trans mem_fixedVectors_dual

def restrictFixed (H : Subgroup G) :
    fixedVectors (contragredient ρ) H →ₗ[ℂ] Module.Dual ℂ (fixedVectors ρ H) :=
  (fixedVectors ρ H).subtype.dualMap ∘ₗ (smoothVectors (Representation.dual ρ)).subtype ∘ₗ
    (fixedVectors (contragredient ρ) H).subtype

theorem restrictFixed_apply (H : Subgroup G) (x : fixedVectors (contragredient ρ) H)
    (v : fixedVectors ρ H) :
    restrictFixed ρ H x v =
      ((x : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v := rfl

def evalSmooth : V →ₗ[ℂ] Module.Dual ℂ (smoothVectors (Representation.dual ρ)) :=
  (smoothVectors (Representation.dual ρ)).subtype.dualMap ∘ₗ Module.Dual.eval ℂ V

theorem evalSmooth_apply (v : V) (x : smoothVectors (Representation.dual ρ)) :
    evalSmooth ρ v x = (x : Module.Dual ℂ V) v := rfl


variable {ρ} in
theorem evalSmooth_mem {v : V} (hv : v ∈ smoothVectors ρ) :
    evalSmooth ρ v ∈ smoothVectors (Representation.dual (contragredient ρ)) := by
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf ρ v) (fun g hg => ?_) hv
  rw [mem_stabilizerOf] at hg ⊢
  ext x
  rw [dual_apply_apply, evalSmooth_apply, evalSmooth_apply, contragredient_apply_apply, inv_inv,
    hg]


variable {ρ} in
def toDoubleContragredient (hρ : IsSmooth ρ) :
    Representation.IntertwiningMap ρ (contragredient (contragredient ρ)) where
  toLinearMap := (evalSmooth ρ).codRestrict _ fun v => evalSmooth_mem (hρ v)
  isIntertwining' g := by
    refine LinearMap.ext fun v => Subtype.ext (LinearMap.ext fun x => ?_)
    change (x : Module.Dual ℂ V) (ρ g v) = (x : Module.Dual ℂ V) (ρ g⁻¹⁻¹ v)
    rw [inv_inv]

end General

section LocallyProfinite

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}

def extendFixed (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (μ : Module.Dual ℂ (fixedVectors ρ K)) : fixedVectors (contragredient ρ) K :=
  have hinv : ∀ k ∈ K, ∀ v, (μ ∘ₗ fixedProj ρ hρ hKc hKo) (ρ k v) =
      (μ ∘ₗ fixedProj ρ hρ hKc hKo) v := fun k hk v => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, fixedProj_apply_act hρ hKc hKo hk]
  ⟨⟨μ ∘ₗ fixedProj ρ hρ hKc hKo,
    mem_smoothVectors_of_mem_fixedVectors hKo (mem_fixedVectors_dual.2 hinv)⟩,
    mem_fixedVectors_contragredient.2 hinv⟩

variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo

theorem restrictFixed_bijective : Function.Bijective (restrictFixed ρ K) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hx' : ((x : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) = 0 :=
      eq_of_invariant_of_eqOn hρ hKc hKo (mem_fixedVectors_contragredient.1 x.2)
        (fun _ _ _ => rfl) fun v hv => LinearMap.congr_fun hx ⟨v, hv⟩
    exact Subtype.ext (Subtype.ext hx')
  · intro μ
    refine ⟨extendFixed hρ hKc hKo μ, LinearMap.ext fun v => ?_⟩
    change μ (fixedProj ρ hρ hKc hKo v) = μ v
    rw [Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo v.2)]

def fixedContragredientEquiv :
    fixedVectors (contragredient ρ) K ≃ₗ[ℂ] Module.Dual ℂ (fixedVectors ρ K) :=
  LinearEquiv.ofBijective (restrictFixed ρ K) (restrictFixed_bijective hρ hKc hKo)

theorem fixedContragredientEquiv_apply (x : fixedVectors (contragredient ρ) K) :
    fixedContragredientEquiv hρ hKc hKo x = restrictFixed ρ K x := rfl

end LocallyProfinite

section Admissible

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem isAdmissible_contragredient (h : IsAdmissible ρ) : IsAdmissible (contragredient ρ) := by
  refine ⟨isSmooth_contragredient ρ, fun K hKc hKo => ?_⟩
  have := h.2 K hKc hKo
  exact LinearEquiv.finiteDimensional (fixedContragredientEquiv h.1 hKc hKo).symm

theorem toDoubleContragredient_bijective (h : IsAdmissible ρ) :
    Function.Bijective (toDoubleContragredient h.1) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    obtain ⟨K, hKc, hKo, hvK⟩ := (isSmooth_iff_forall_exists ρ).1 h.1 v
    set e := fixedContragredientEquiv h.1 hKc hKo
    have hzero : (⟨v, hvK⟩ : fixedVectors ρ K) = 0 := by
      refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun μ => ?_
      have h1 : (((e.symm μ : fixedVectors (contragredient ρ) K) :
          smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v = 0 := by
        have := congrArg (fun Φ : smoothVectors (Representation.dual (contragredient ρ)) =>
          (Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ)))
            (e.symm μ : fixedVectors (contragredient ρ) K)) hv
        exact this
      have h2 : e (e.symm μ) = μ := e.apply_symm_apply μ
      rw [← h2, fixedContragredientEquiv_apply, restrictFixed_apply]
      exact h1
    simpa using congrArg Subtype.val hzero
  · intro Φ
    obtain ⟨K, hKc, hKo, hΦK⟩ := (mem_smoothVectors_iff _).1 Φ.2
    set e := fixedContragredientEquiv h.1 hKc hKo
    have := h.2 K hKc hKo
    let ψ : Module.Dual ℂ (Module.Dual ℂ (fixedVectors ρ K)) :=
      (Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ))) ∘ₗ
        (fixedVectors (contragredient ρ) K).subtype ∘ₗ e.symm.toLinearMap
    set w := (Module.evalEquiv ℂ (fixedVectors ρ K)).symm ψ
    have hw : ∀ μ : Module.Dual ℂ (fixedVectors ρ K), μ w = ψ μ := fun μ =>
      LinearMap.congr_fun ((Module.evalEquiv ℂ (fixedVectors ρ K)).apply_symm_apply ψ) μ
    refine ⟨(w : V), Subtype.ext ?_⟩
    refine eq_of_invariant_of_eqOn (isSmooth_contragredient ρ) hKc hKo (fun k hk x => ?_)
      (mem_fixedVectors_dual.1 hΦK) fun x hx => ?_
    · change (x : Module.Dual ℂ V) (ρ k⁻¹ w) = (x : Module.Dual ℂ V) w
      rw [w.2 _ (inv_mem hk)]
    · have h1 : (Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ))) x =
          ψ (e ⟨x, hx⟩) := by
        simp [ψ]
      rw [h1, ← hw]
      rfl

end Admissible

end GroundTheory.Automorphic
end
end

section -- merged from GroundTheory.AutomorphicForms.HermitianOrthogonal
noncomputable section

namespace GroundTheory.Automorphic

open Module

section Conj

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

instance finiteDimensional_of_isQuadraticExtension : FiniteDimensional F E :=
  Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two F E)

theorem conjHom_apply (x : E) : conjHom F E x = conj F E x :=
  rfl

theorem exists_not_mem_range : ∃ ζ : E, ζ ∉ Set.range (algebraMap F E) := by
  by_contra H
  push Not at H
  have hbij : Function.Bijective (Algebra.linearMap F E) :=
    ⟨(algebraMap F E).injective, fun y => H y⟩
  have h1 := (LinearEquiv.ofBijective _ hbij).finrank_eq
  rw [Module.finrank_self, Algebra.IsQuadraticExtension.finrank_eq_two] at h1
  exact absurd h1 (by norm_num)

theorem conj_eq_self_iff [Algebra.IsSeparable F E] {x : E} :
    conj F E x = x ↔ x ∈ Set.range (algebraMap F E) := by
  refine ⟨fun hx => ?_, fun ⟨c, hc⟩ => hc ▸ conj_algebraMap c⟩
  by_contra hne
  rw [conj_apply] at hx
  have h2 : algebraMap F E (Algebra.trace F E x) = 2 * x := by linear_combination hx
  by_cases h2E : (2 : E) = 0
  · have htx : Algebra.trace F E x = 0 := by
      apply (algebraMap F E).injective
      rw [h2, h2E, zero_mul, map_zero]
    have ht1 : Algebra.trace F E 1 = 0 := by
      have := trace_algebraMap_quadratic (F := F) (E := E) 1
      rw [map_one, mul_one] at this
      rw [this]
      apply (algebraMap F E).injective
      rw [map_ofNat, h2E, map_zero]
    apply Algebra.trace_ne_zero F E
    refine (basisOneOf hne).ext fun i => ?_
    fin_cases i
    · simp [basisOneOf_zero, ht1]
    · simp [basisOneOf_one, htx]
  · apply hne
    refine ⟨2⁻¹ * Algebra.trace F E x, ?_⟩
    rw [map_mul, h2, map_inv₀, map_ofNat, ← mul_assoc, inv_mul_cancel₀ h2E, one_mul]

end Conj

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' V'' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  [AddCommGroup V''] [Module E V'']

namespace HermitianForm

def Isometric (h : HermitianForm F E V) (h' : HermitianForm F E V') : Prop :=
  ∃ e : V ≃ₗ[E] V', ∀ x y, h'.toSesq (e x) (e y) = h.toSesq x y

theorem conj_toSesq (h : HermitianForm F E V) (x y : V) :
    conj F E (h.toSesq x y) = h.toSesq y x :=
  h.isSymm.eq x y

namespace Isometric

end Isometric

section Separable

variable [Algebra.IsSeparable F E]

end Separable

end HermitianForm

end GroundTheory.Automorphic

end
end

section -- merged from GroundTheory.AutomorphicForms.UnitaryGroupScheme
namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

section Transport

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Type*} [CommRing A] [CommRing B]


omit [DecidableEq ι] in
theorem map_unitaryExpr (φ : A →+* B) {sA : A →+* A} {sB : B →+* B}
    (hs : ∀ x, φ (sA x) = sB (φ x)) (H M : Matrix ι ι A) :
    ((M.map sA)ᵀ * H * M).map φ = ((M.map φ).map sB)ᵀ * H.map φ * M.map φ := by
  have hc : (φ : A → B) ∘ sA = sB ∘ φ := funext hs
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_map, hc]

theorem map_mem_unitaryGroupMatrix (φ : A →+* B) {sA : A →+* A} {sB : B →+* B}
    (hs : ∀ x, φ (sA x) = sB (φ x)) {HA : Matrix ι ι A} {HB : Matrix ι ι B}
    (hH : HA.map φ = HB) {g : GL ι A} (hg : g ∈ unitaryGroupMatrix sA HA) :
    Matrix.GeneralLinearGroup.map φ g ∈ unitaryGroupMatrix sB HB := by
  rw [mem_unitaryGroupMatrix] at *
  have := congrArg (fun M => M.map φ) hg
  rw [map_unitaryExpr φ hs, hH] at this
  exact this

noncomputable def unitaryGroupMatrixCongr (e : A ≃+* B) {sA : A →+* A} {sB : B →+* B}
    (hs : ∀ x, e (sA x) = sB (e x)) {HA : Matrix ι ι A} {HB : Matrix ι ι B}
    (hH : HA.map e = HB) : unitaryGroupMatrix sA HA ≃* unitaryGroupMatrix sB HB where
  toFun g := ⟨Matrix.GeneralLinearGroup.map (e : A →+* B) g,
    map_mem_unitaryGroupMatrix (e : A →+* B) hs hH g.2⟩
  invFun g := ⟨Matrix.GeneralLinearGroup.map (e.symm : B →+* A) g,
    map_mem_unitaryGroupMatrix (e.symm : B →+* A)
      (fun x => by
        apply e.injective
        simp only [RingHom.coe_coe, RingEquiv.apply_symm_apply]
        rw [hs, RingEquiv.apply_symm_apply])
      (by rw [← hH, Matrix.map_map]; ext i j; simp) g.2⟩
  left_inv g := by
    apply Subtype.ext; apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map]
  right_inv g := by
    apply Subtype.ext; apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map]
  map_mul' a b := by
    apply Subtype.ext
    simp

end Transport

variable (F E : Type*) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

section BaseChange

variable (R S T : Type*) [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
  [CommRing T] [Algebra F T]

noncomputable def conjBase : R ⊗[F] E →+* R ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.id R R) (conj F E).toAlgHom).toRingHom

variable {F E R S T}

@[simp]
theorem conjBase_tmul (r : R) (e : E) : conjBase F E R (r ⊗ₜ e) = r ⊗ₜ conj F E e := rfl


variable (E) in
noncomputable def tensorMap (f : R →ₐ[F] S) : R ⊗[F] E →ₐ[F] S ⊗[F] E :=
  Algebra.TensorProduct.map f (AlgHom.id F E)

omit [Algebra.IsQuadraticExtension F E] in
@[simp]
theorem tensorMap_tmul (f : R →ₐ[F] S) (r : R) (e : E) :
    tensorMap E f (r ⊗ₜ e) = f r ⊗ₜ e := rfl

theorem tensorMap_conjBase (f : R →ₐ[F] S) (z : R ⊗[F] E) :
    tensorMap E f (conjBase F E R z) = conjBase F E S (tensorMap E f z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r e => rw [conjBase_tmul, tensorMap_tmul, tensorMap_tmul, conjBase_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

omit [Algebra.IsQuadraticExtension F E] in
theorem tensorMap_includeRight (f : R →ₐ[F] S) (e : E) :
    tensorMap E f (Algebra.TensorProduct.includeRight e) =
      (Algebra.TensorProduct.includeRight e : S ⊗[F] E) := by
  simp [Algebra.TensorProduct.includeRight_apply]



end BaseChange

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

section Points

variable (R S T : Type*) [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
  [CommRing T] [Algebra F T]

noncomputable def unitaryPoints : Subgroup (GL ι (R ⊗[F] E)) :=
  unitaryGroupMatrix (conjBase F E R)
    (H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E))

variable {F E H R S T}

omit [Algebra.IsQuadraticExtension F E] [Fintype ι] [DecidableEq ι] in
theorem map_includeRight_tensorMap (f : R →ₐ[F] S) :
    (H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E)).map
      ((tensorMap E f : R ⊗[F] E →ₐ[F] S ⊗[F] E) : R ⊗[F] E →+* S ⊗[F] E) =
      H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] S ⊗[F] E) := by
  rw [Matrix.map_map]
  congr 1
  funext e
  exact tensorMap_includeRight f e


variable (F E H) in
noncomputable def unitaryMap (f : R →ₐ[F] S) : unitaryPoints F E H R →* unitaryPoints F E H S :=
  ((Matrix.GeneralLinearGroup.map
      ((tensorMap E f : R ⊗[F] E →ₐ[F] S ⊗[F] E) : R ⊗[F] E →+* S ⊗[F] E)).comp
    (unitaryPoints F E H R).subtype).codRestrict _ fun g =>
    map_mem_unitaryGroupMatrix _ (tensorMap_conjBase f) (map_includeRight_tensorMap f) g.2

end Points

section Functor

open CategoryTheory

universe u

variable (F E : Type u) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  {ι : Type u} [Fintype ι] [DecidableEq ι]

end Functor

section Rational

variable {F E H}

theorem lid_conjBase (z : F ⊗[F] E) :
    Algebra.TensorProduct.lid F E (conjBase F E F z) = conj F E (Algebra.TensorProduct.lid F E z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r e =>
    simp only [conjBase_tmul, Algebra.TensorProduct.lid_tmul, map_smul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

omit [Algebra.IsQuadraticExtension F E] [Fintype ι] [DecidableEq ι] in
theorem map_includeRight_lid :
    (H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] F ⊗[F] E)).map
      ((Algebra.TensorProduct.lid F E : F ⊗[F] E ≃ₐ[F] E) : F ⊗[F] E ≃+* E) = H := by
  rw [Matrix.map_map]
  conv_rhs => rw [← Matrix.map_id H]
  congr 1
  funext e
  simp [Algebra.TensorProduct.includeRight_apply]


variable (F E H) in
noncomputable def unitaryPointsRationalEquiv :
    unitaryPoints F E H F ≃* unitaryGroupMatrix (conjHom F E) H :=
  unitaryGroupMatrixCongr ((Algebra.TensorProduct.lid F E).toRingEquiv)
    (fun z => lid_conjBase z) map_includeRight_lid

variable {V : Type*} [AddCommGroup V] [Module E V]


variable (F E) in
noncomputable def unitaryPointsRationalEquivHermitian (h : HermitianForm F E V)
    (v : Basis ι E V) : unitaryPoints F E (gram h.toSesq v) F ≃* h.unitaryGroup :=
  (unitaryPointsRationalEquiv F E (gram h.toSesq v)).trans (unitaryGroupEquivMatrix h v).symm

end Rational

end GroundTheory.Automorphic
end

section -- merged from GroundTheory.AutomorphicForms.RealGroupsKAK
namespace GroundTheory.Automorphic

open Matrix Polynomial
open scoped MatrixOrder ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

theorem exists_KAK (g : GL n 𝕜) :
    ∃ k₁ k₂ : unitaryGroup n 𝕜, ∃ a : n → ℝ, (∀ i, 0 < a i) ∧
      (g : Matrix n n 𝕜) = (k₁ : Matrix n n 𝕜) * diagonal (fun i => (a i : 𝕜)) * k₂ := by
  have hp : (polarPos g).PosDef := polarPos_posDef g
  have hH : (polarPos g).IsHermitian := hp.isHermitian
  refine ⟨⟨polarUnitary g, polarUnitary_mem g⟩ * hH.eigenvectorUnitary, star hH.eigenvectorUnitary,
    hH.eigenvalues, hp.eigenvalues_pos, ?_⟩
  have hs := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  calc (g : Matrix n n 𝕜) = polarUnitary g * polarPos g := (polarUnitary_mul_polarPos g).symm
    _ = polarUnitary g * ((hH.eigenvectorUnitary : Matrix n n 𝕜) *
          diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star (hH.eigenvectorUnitary : Matrix n n 𝕜)) := by
        rw [← hs]
    _ = _ := by simp [Matrix.mul_assoc, Function.comp_def]

end GroundTheory.Automorphic
end
