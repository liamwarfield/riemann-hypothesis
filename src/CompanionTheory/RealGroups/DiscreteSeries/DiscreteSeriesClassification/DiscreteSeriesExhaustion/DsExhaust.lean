module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeDuality.DualModuleFacts
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeUnits.Unitarity
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeBackward
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.DecayEstimate
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.FarRegularExhaustion
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ExhaustionFiniteLength
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ClassLit
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.ScalarCharacters.ScalCharOfSimple

@[expose] public section

section -- merged from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.InfinitesimalCharacterShift
section -- merged from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.SimpleBackwardTransfer.FwdSimpleOfb
noncomputable section

open Finset

namespace CompanionTheory.RgExh.Hk

open Formalism.REAL (GlRel qdet)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (tensVd eeVd)

variable {n : ℕ}

section maps
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem fsb_pow_map (f : V →ₗ[ℂ] W) (T : Module.End ℂ V) (T' : Module.End ℂ W)
    (h : ∀ v, f (T v) = T' (f v)) : ∀ (k : ℕ) (v : V), f ((T ^ k) v) = (T' ^ k) (f v) := by
  intro k
  induction k with
  | zero => intro v; simp
  | succ k ih =>
    intro v
    rw [pow_succ', Module.End.mul_apply, h, ih, pow_succ', Module.End.mul_apply]

theorem fsb_ofFn_map (f : V →ₗ[ℂ] W) : ∀ (t : ℕ) (g : Fin t → Module.End ℂ V) (g' : Fin t → Module.End ℂ W),
    (∀ k v, f (g k v) = g' k (f v)) → ∀ v, f ((List.ofFn g).prod v) = (List.ofFn g').prod (f v) := by
  intro t
  induction t with
  | zero => intro g g' _ v; simp
  | succ t ih =>
    intro g g' hg v
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, hg,
      ih (fun i => g i.succ) (fun i => g' i.succ) (fun k w => hg k.succ w), List.ofFn_succ, List.prod_cons,
      Module.End.mul_apply]

theorem fsb_qdet_map {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ W}
    (f : V →ₗ[ℂ] W) (hf : ∀ a b v, f (E a b v) = E' a b (f v)) (x : ℂ) (v : V) :
    f (qdet E x v) = qdet E' x (f v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.intCast_apply, Module.End.intCast_apply,
    map_zsmul]
  congr 1
  refine fsb_ofFn_map f n _ _ (fun k w => ?_) v
  simp only [Formalism.REAL.Tm, LinearMap.add_apply, map_add (f := _), hf]
  split_ifs <;> simp

theorem fsb_glRel_surj {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ W}
    (f : V →ₗ[ℂ] W) (hs : Function.Surjective f) (hf : ∀ a b v, f (E a b v) = E' a b (f v)) (hE : GlRel E) :
    GlRel E' := by
  intro a b c d
  have key := hE a b c d
  ext w
  obtain ⟨v, rfl⟩ := hs w
  have key' := congrArg (fun T => f (T v)) key
  split_ifs at key' ⊢ <;> simpa [hf] using key'

end maps

theorem fsb_hasChar_inj (M1 M2 : GMod n) (f : M1.V →ₗ[ℂ] M2.V) (hf : ∀ a b v, f (M1.E a b v) = M2.E a b (f v))
    (hi : Function.Injective f) (χ : Fin n → ℂ) (h : HasChar M2 χ) : HasChar M1 χ := by
  have hT : ∀ (u c : ℂ) (w : M1.V), f ((Formalism.REAL.qdet M1.E u - c • (1 : Module.End ℂ M1.V)) w) =
      (Formalism.REAL.qdet M2.E u - c • (1 : Module.End ℂ M2.V)) (f w) := by
    intro u c w
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, fsb_qdet_map f hf, LinearMap.smul_apply,
      LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, map_smul]
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun Y => ?_⟩
  ext v
  apply hi
  rw [fsb_pow_map f _ _ (hT _ _) k v, hk Y]
  simp

theorem fsb_hasChar_surj (M1 M2 : GMod n) (f : M1.V →ₗ[ℂ] M2.V) (hf : ∀ a b v, f (M1.E a b v) = M2.E a b (f v))
    (hs : Function.Surjective f) (χ : Fin n → ℂ) (h : HasChar M1 χ) : HasChar M2 χ := by
  have hT : ∀ (u c : ℂ) (w : M1.V), f ((Formalism.REAL.qdet M1.E u - c • (1 : Module.End ℂ M1.V)) w) =
      (Formalism.REAL.qdet M2.E u - c • (1 : Module.End ℂ M2.V)) (f w) := by
    intro u c w
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, fsb_qdet_map f hf, LinearMap.smul_apply,
      LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, map_smul]
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun Y => ?_⟩
  ext w
  obtain ⟨v, rfl⟩ := hs w
  rw [← fsb_pow_map f _ _ (hT _ _) k v, hk Y]
  simp

theorem fsb_omD_apply (M : GMod n) (g : Fin n → M.V) (a : Fin n) : omD M g a = -∑ c, M.E a c (g c) := by
  simp only [omD, eeVd, LinearMap.pi_apply, LinearMap.neg_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

theorem fsb_tensVd_apply (M : GMod n) (a b : Fin n) (g : Fin n → M.V) (d : Fin n) :
    tensVd M.E a b g d = M.E a b (g d) - if d = b then g a else 0 := by
  simp only [tensVd, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  split_ifs <;> simp

theorem fsb_omD_map (M1 M2 : GMod n) (f : M1.V →ₗ[ℂ] M2.V) (hf : ∀ a b v, f (M1.E a b v) = M2.E a b (f v))
    (g : Fin n → M1.V) : f.compLeft (Fin n) (omD M1 g) = omD M2 (f.compLeft (Fin n) g) := by
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.compLeft_apply, Function.comp_apply, fsb_omD_apply, map_neg, map_sum, hf]

theorem fsb_aeval_map (M1 M2 : GMod n) (f : M1.V →ₗ[ℂ] M2.V) (hf : ∀ a b v, f (M1.E a b v) = M2.E a b (f v))
    (p : Polynomial ℂ) (g : Fin n → M1.V) :
    f.compLeft (Fin n) (Polynomial.aeval (omD M1) p g) = Polynomial.aeval (omD M2) p (f.compLeft (Fin n) g) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul,
      fsb_pow_map (f.compLeft (Fin n)) (omD M1) (omD M2) (fun v => fsb_omD_map M1 M2 f hf v) k g]

theorem fsb_gen_map (M1 M2 : GMod n) (f : M1.V →ₗ[ℂ] M2.V) (hf : ∀ a b v, f (M1.E a b v) = M2.E a b (f v))
    (μ : ℂ) (g : Fin n → M1.V) (hg : g ∈ (omD M1).maxGenEigenspace μ) :
    f.compLeft (Fin n) g ∈ (omD M2).maxGenEigenspace μ := by
  rw [Module.End.mem_maxGenEigenspace] at hg ⊢
  obtain ⟨k, hk⟩ := hg
  refine ⟨k, ?_⟩
  have h1 : ∀ v, f.compLeft (Fin n) ((omD M1 - μ • 1) v) = (omD M2 - μ • 1) (f.compLeft (Fin n) v) := by
    intro v
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, fsb_omD_map M1 M2 f hf, LinearMap.smul_apply,
      LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, map_smul]
  rw [← fsb_pow_map _ _ _ h1 k g, hk, map_zero]

def fsbQuot (M : GMod n) (Z : Submodule ℂ M.V) (hZ : ∀ a b, ∀ x ∈ Z, M.E a b x ∈ Z) : GMod n where
  V := M.V ⧸ Z
  E := fun a b => Z.mapQ Z (M.E a b) (fun x hx => hZ a b x hx)
  gl := fsb_glRel_surj Z.mkQ (Submodule.mkQ_surjective Z) (fun a b v => by simp) M.gl

private theorem exists_mem_backSub_compLeft_eq_of_surjective (hD : DualFacts) (S Q : GMod n) (χ' : Fin n → ℂ) (s : Fin n) (z : ℂ)
    (hz : χ' s = z) (h1 : ∀ t, t ≠ s → χ' t ≠ z) (hS : HasChar S χ') (f : S.V →ₗ[ℂ] Q.V)
    (hs : Function.Surjective f) (hf : ∀ a b v, f (S.E a b v) = Q.E a b (f v)) (y : Fin n → Q.V)
    (hy : y ∈ backSub Q z) : ∃ x ∈ backSub S z, f.compLeft (Fin n) x = y := by
  obtain ⟨K, hK⟩ := (hD n S χ' hS).1
  have hP : Polynomial.aeval (omD S)
      ((List.ofFn fun t => (Polynomial.X - Polynomial.C (-χ' t - cn n))).prod ^ K) = 0 := by
    rw [map_pow, map_list_prod, List.map_ofFn]
    have hfun : (⇑(Polynomial.aeval (omD S)) ∘ fun t => Polynomial.X - Polynomial.C (-χ' t - cn n)) =
        fun t => omD S - (-χ' t - cn n) • 1 := by
      funext t
      rw [Function.comp_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    rw [hfun]
    exact hK
  rw [List.prod_ofFn, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ s), hz, mul_pow] at hP
  have hcop : IsCoprime (Polynomial.X - Polynomial.C (-z - cn n))
      (∏ t ∈ Finset.univ.erase s, (Polynomial.X - Polynomial.C (-χ' t - cn n))) := by
    apply IsCoprime.prod_right
    intro t ht
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    apply Ne.isUnit
    intro h0
    apply h1 t (Finset.ne_of_mem_erase ht)
    linear_combination h0
  generalize (∏ t ∈ Finset.univ.erase s, (Polynomial.X - Polynomial.C (-χ' t - cn n))) = R at hP hcop
  have hy' := hy
  rw [backSub, Module.End.mem_maxGenEigenspace] at hy'
  obtain ⟨k, hk⟩ := hy'
  obtain ⟨A', B', hAB⟩ := hcop.pow (m := k) (n := K)
  choose x0 hx0 using fun d => hs (y d)
  have hx0' : f.compLeft (Fin n) x0 = y := by
    funext d
    rw [LinearMap.compLeft_apply, Function.comp_apply, hx0]
  refine ⟨Polynomial.aeval (omD S) (B' * R ^ K) x0, ?_, ?_⟩
  · rw [backSub, Module.End.mem_maxGenEigenspace]
    refine ⟨K, ?_⟩
    have e1 : (omD S - (-z - cn n) • 1) ^ K =
        Polynomial.aeval (omD S) ((Polynomial.X - Polynomial.C (-z - cn n)) ^ K) := by
      rw [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    rw [e1, ← Module.End.mul_apply, ← map_mul,
      show (Polynomial.X - Polynomial.C (-z - cn n)) ^ K * (B' * R ^ K) =
        B' * ((Polynomial.X - Polynomial.C (-z - cn n)) ^ K * R ^ K) by ring,
      map_mul, hP, mul_zero, LinearMap.zero_apply]
  · rw [fsb_aeval_map S Q f hf, hx0']
    have e3 : Polynomial.aeval (omD Q) ((Polynomial.X - Polynomial.C (-z - cn n)) ^ k) y = 0 := by
      have e4 : Polynomial.aeval (omD Q) ((Polynomial.X - Polynomial.C (-z - cn n)) ^ k) =
          (omD Q - (-z - cn n) • 1) ^ k := by
        rw [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
      rw [e4]
      exact hk
    calc Polynomial.aeval (omD Q) (B' * R ^ K) y
        = Polynomial.aeval (omD Q) (A' * (Polynomial.X - Polynomial.C (-z - cn n)) ^ k + B' * R ^ K) y := by
          rw [map_add (f := _), LinearMap.add_apply,
            map_mul (Polynomial.aeval (omD Q)) A' ((Polynomial.X - Polynomial.C (-z - cn n)) ^ k),
            Module.End.mul_apply, e3, map_zero, zero_add]
      _ = y := by rw [hAB, map_one, Module.End.one_apply]

private theorem apply_mem_of_mem_backSub_of_iso_simple (hD : DualFacts) (X S : GMod n) (χ' : Fin n → ℂ) (s : Fin n) (z : ℂ)
    (hz : χ' s = z) (hX : IsSimple X) (hS : HasChar S χ') (h2 : ∀ r, χ' r ≠ z - 1)
    (hB : ∀ a b, ∀ x ∈ backSub S z, (tensD S).E a b x ∈ backSub S z)
    (hI : Iso (back S z hB) X) (Z : Submodule ℂ S.V) (hZ : ∀ a b, ∀ x ∈ Z, S.E a b x ∈ Z) (hZb : Z ≠ ⊥) :
    ∀ g ∈ backSub S z, ∀ d, g d ∈ Z := by
  obtain ⟨e, he⟩ := hI
  have hZc : HasChar (S.sub Z hZ) χ' :=
    fsb_hasChar_inj (S.sub Z hZ) S Z.subtype (fun a b v => rfl) Z.injective_subtype χ' hS
  haveI : Nontrivial (S.sub Z hZ).V := Submodule.nontrivial_iff_ne_bot.mpr hZb
  have hne := (hD n (S.sub Z hZ) χ' hZc).2.2 s inferInstance (fun r => by rw [hz]; exact h2 r)
  rw [hz] at hne
  obtain ⟨g0, hg0, hg0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hmem : Z.subtype.compLeft (Fin n) g0 ∈ backSub S z :=
    fsb_gen_map (S.sub Z hZ) S Z.subtype (fun a b v => rfl) _ g0 hg0
  let W : Submodule ℂ ↥(backSub S z) := (Submodule.pi Set.univ fun _ => Z).comap (backSub S z).subtype
  have hWmem : ∀ x : ↥(backSub S z), x ∈ W ↔ ∀ d, (x : Fin n → S.V) d ∈ Z := by
    intro x
    simp only [W, Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.subtype_apply]
  have hWinv : ∀ a b, ∀ x ∈ W, (back S z hB).E a b x ∈ W := by
    intro a b x hx
    have hx : ∀ d, (x : Fin n → S.V) d ∈ Z := (hWmem x).mp hx
    refine (hWmem ((back S z hB).E a b x)).mpr fun d => ?_
    show (tensVd S.E a b (x : Fin n → S.V)) d ∈ Z
    rw [fsb_tensVd_apply S a b]
    split_ifs
    · exact Z.sub_mem (hZ a b _ (hx d)) (hx a)
    · simpa using hZ a b _ (hx d)
  let W' : Submodule ℂ X.V := W.comap (e.symm : X.V →ₗ[ℂ] (back S z hB).V)
  have hW'mem : ∀ x : X.V, x ∈ W' ↔ e.symm x ∈ W := fun x => Iff.rfl
  have key : ∀ a b (x : X.V), e.symm (X.E a b x) = (back S z hB).E a b (e.symm x) := by
    intro a b x
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hW'inv : ∀ a b, ∀ x ∈ W', X.E a b x ∈ W' := by
    intro a b x hx
    rw [hW'mem, key]
    exact hWinv a b _ hx
  rcases hX.2 W' hW'inv with h | h
  · exfalso
    apply hg0ne
    have hw : (⟨_, hmem⟩ : ↥(backSub S z)) ∈ W := by
      rw [hWmem]
      intro d
      exact (g0 d).2
    have hw' : e ⟨_, hmem⟩ ∈ W' :=
      (hW'mem _).mpr (Eq.mpr (congrArg (fun x => x ∈ W) (e.symm_apply_apply _)) hw)
    rw [h, Submodule.mem_bot] at hw'
    have hw0 : (⟨_, hmem⟩ : ↥(backSub S z)) = 0 := e.injective (hw'.trans (map_zero e).symm)
    funext d
    apply Subtype.ext
    exact congrFun (congrArg Subtype.val hw0) d
  · intro g hg d
    have hw' : e ⟨g, hg⟩ ∈ W' := by rw [h]; trivial
    have hw2 : (⟨g, hg⟩ : ↥(backSub S z)) ∈ W :=
      Eq.mp (congrArg (fun x => x ∈ W) (e.symm_apply_apply ⟨g, hg⟩)) ((hW'mem _).mp hw')
    exact (hWmem ⟨g, hg⟩).mp hw2 d

theorem fsb_simple_of_back (hD : DualFacts) (X S : GMod n) (χ' : Fin n → ℂ) (s : Fin n) (z : ℂ) (hz : χ' s = z)
    (hX : IsSimple X) (hS : HasChar S χ') (h1 : ∀ t, t ≠ s → χ' t ≠ z) (h2 : ∀ r, χ' r ≠ z - 1)
    (hB : ∀ a b, ∀ x ∈ backSub S z, (tensD S).E a b x ∈ backSub S z)
    (hI : Iso (back S z hB) X) : IsSimple S := by
  haveI hnt : Nontrivial ↥(backSub S z) := by
    obtain ⟨e, -⟩ := hI
    haveI := hX.1
    exact e.symm.injective.nontrivial
  refine ⟨?_, fun Z hZ => ?_⟩
  · obtain ⟨⟨g, hg⟩, hne⟩ := exists_ne (0 : ↥(backSub S z))
    have hg0 : g ≠ 0 := fun h0 => hne (Subtype.ext h0)
    obtain ⟨d, hd⟩ := Function.ne_iff.mp hg0
    exact ⟨⟨g d, 0, hd⟩⟩
  · by_cases hZb : Z = ⊥
    · exact Or.inl hZb
    · right
      by_contra hZt
      have hA := apply_mem_of_mem_backSub_of_iso_simple hD X S χ' s z hz hX hS h2 hB hI Z hZ hZb
      have hQc : HasChar (fsbQuot S Z hZ) χ' :=
        fsb_hasChar_surj S (fsbQuot S Z hZ) Z.mkQ (fun a b v => rfl) (Submodule.mkQ_surjective Z) χ' hS
      obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hZt)
      haveI : Nontrivial (fsbQuot S Z hZ).V :=
        ⟨⟨Submodule.Quotient.mk v, 0, fun h0 => hv ((Submodule.Quotient.mk_eq_zero Z).mp h0)⟩⟩
      have hne := (hD n (fsbQuot S Z hZ) χ' hQc).2.2 s inferInstance (fun r => by rw [hz]; exact h2 r)
      rw [hz] at hne
      obtain ⟨y, hy, hyne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      obtain ⟨x, hx, hxy⟩ := exists_mem_backSub_compLeft_eq_of_surjective hD S (fsbQuot S Z hZ) χ' s z hz h1 hS Z.mkQ
        (Submodule.mkQ_surjective Z) (fun a b v => rfl) y hy
      apply hyne
      rw [← hxy]
      funext d
      show Z.mkQ (x d) = 0
      exact (Submodule.Quotient.mk_eq_zero Z).mpr (hA x hx d)

theorem forward_simple_of_tensor_facts : QdetTens → BackStable → DualFacts → Unit → FwdSimple := by
  intro hQ hB hD hU n X χ s hX hSc h1 h2 h3
  have hXc : HasChar X χ := ⟨1, fun Y => by rw [pow_one, hSc Y, sub_self]⟩
  refine fsb_simple_of_back hD X (step X (χ s)) (χ + Pi.single s 1) s (χ s + 1) (by simp) hX
    (GlobalTheory.T.InfinitesimalCharacterStatement n X χ s hXc) ?_ ?_ (hB n _ _) (hU n X χ s hB hSc h1 h2 h3)
  · intro t ht
    simpa [Pi.single_apply, ht] using h1 t
  · intro r
    by_cases hr : r = s
    · subst hr
      simp
    · simpa [Pi.single_apply, hr] using h2 r hr

end CompanionTheory.RgExh.Hk
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OmegaScalar
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OmegaScalar
noncomputable section

open Finset Polynomial

namespace GlobalTheory.CompanionTheory.RgExhHecke.OmScalP

open Formalism.REAL (qdet qminor Tm)
open _root_.CompanionTheory.RgExh
open _root_.CompanionTheory.RgExh.Hk

section Poly

variable {A : Type*} [Ring A] [Algebra ℂ A]

def evAt (u : ℂ) : A[X] →+* A :=
  eval₂RingHom' (RingHom.id A) (algebraMap ℂ A u) fun a => (Algebra.commutes u a).symm

theorem evAt_apply (u : ℂ) (p : A[X]) : evAt u p = eval₂ (RingHom.id A) (algebraMap ℂ A u) p := rfl

def tmPoly {n : ℕ} (E : Fin n → Fin n → A) (v : ℂ) (a b : Fin n) : A[X] :=
  (if a = b then X - C (algebraMap ℂ A v) else 0) + C (E a b)

theorem evAt_tmPoly {n : ℕ} (E : Fin n → Fin n → A) (v u : ℂ) (a b : Fin n) :
    evAt u (tmPoly E v a b) = Tm E (u - v) a b := by
  unfold tmPoly Tm
  by_cases h : a = b <;> simp [h, evAt_apply, map_sub]

def qdetPoly {n : ℕ} (E : Fin n → Fin n → A) : A[X] :=
  ∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A[X]) *
    (List.ofFn fun k : Fin n => tmPoly E ((k : ℕ) : ℂ) (σ k) k).prod

theorem evAt_qdetPoly {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) : evAt u (qdetPoly E) = qdet E u := by
  unfold qdet qminor qdetPoly
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  simp [Function.comp_def, evAt_tmPoly]

end Poly

theorem cont {M : Type*} [AddCommGroup M] [Module ℂ M] (p : (Module.End ℂ M)[X]) (q : ℂ[X]) (h : M) (b : ℂ)
    (H : ∀ u, u ≠ b → evAt u p h = q.eval u • h) : evAt b p h = q.eval b • h := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  set r : ℂ[X] := ∑ k ∈ p.support, monomial k (φ (p.coeff k h)) - q * C (φ h) with hr
  have hev : ∀ u, r.eval u = φ (evAt u p h - q.eval u • h) := by
    intro u
    have e1 : evAt u p h = ∑ k ∈ p.support, u ^ k • p.coeff k h := by
      rw [evAt_apply, eval₂_eq_sum, Polynomial.sum_def, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← map_pow, RingHom.id_apply, ← Algebra.commutes, ← Algebra.smul_def]
      rfl
    rw [e1, hr]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [eval_finsetSum, map_sum, eval_monomial, mul_comm]
  have hz : r = 0 := by
    refine eq_zero_of_infinite_isRoot r ?_
    refine Set.Infinite.mono (s := {b}ᶜ) ?_ (Set.finite_singleton b).infinite_compl
    intro u hu
    have hu' : u ≠ b := hu
    change r.eval u = 0
    rw [hev, H u hu', sub_self, map_zero]
  rw [← hev, hz, eval_zero]

theorem compLeft_smul_one {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (c : ℂ) (w : Fin n → V) :
    (c • (1 : Module.End ℂ V)).compLeft (Fin n) w = c • w := by
  funext i
  simp [LinearMap.compLeft_apply]

theorem tens_apply {n : ℕ} (X : GMod n) (χ : Fin n → ℂ) (hS : ScalChar X χ) (u : ℂ) (w : Fin n → X.V) :
    qdet (tensE X) u (u • w + om X w) =
      Formalism.QuantumDeterminants.capP χ (u - cn n) • ((u + 1) • w + om X w) := by
  have hq : qdet X.E u = Formalism.QuantumDeterminants.capP χ (u - cn n) • (1 : Module.End ℂ X.V) := by
    have := hS (u - cn n)
    rwa [show u - cn n + ((n : ℂ) - 1) / 2 = u by unfold cn; ring] at this
  have h := LinearMap.congr_fun (GlobalTheory.T.QuantumDeterminantTensor n X u) w
  rw [hq] at h
  simpa [Module.End.mul_apply, compLeft_smul_one] using h

theorem core {n : ℕ} (X : GMod n) (χ : Fin n → ℂ) (s : Fin n) (hS : ScalChar X χ)
    (hs : ∀ r, r ≠ s → χ r ≠ χ s) (g : Fin n → X.V)
    (h2 : om X (om X g - (χ s - cn n) • g) = (χ s - cn n) • (om X g - (χ s - cn n) • g)) :
    om X g - (χ s - cn n) • g = 0 := by
  set a : ℂ := χ s - cn n with ha
  set h : Fin n → X.V := om X g - a • g with hh
  set ct : ℂ → ℂ := fun u => ∏ t ∈ univ.erase s, (u - cn n + χ t) with hct
  have hc : ∀ u, Formalism.QuantumDeterminants.capP χ (u - cn n) = (u + a) * ct u := by
    intro u
    have := Finset.mul_prod_erase univ (fun t => u - cn n + χ t) (mem_univ s)
    simp only [Formalism.QuantumDeterminants.capP, hct]
    rw [← this, ha]
    ring_nf
  set q : ℂ[X] := (∏ t ∈ univ.erase s, (Polynomial.X - C (cn n) + C (χ t))) * (Polynomial.X + C (a + 1)) with hq
  have hqe : ∀ u, q.eval u = ct u * (u + (a + 1)) := by
    intro u
    simp [hq, hct, eval_prod]
  have hne : ∀ u, u ≠ -a → evAt u (qdetPoly (tensE X)) h = q.eval u • h := by
    intro u hu
    have hw : u + a ≠ 0 := fun e => hu (eq_neg_of_add_eq_zero_left e)
    have e := tens_apply X χ hS u h
    rw [h2, hc] at e
    rw [evAt_qdetPoly, hqe]
    have e1 : u • h + a • h = (u + a) • h := (add_smul _ _ _).symm
    have e2 : (u + 1) • h + a • h = (u + (a + 1)) • h := by rw [← add_smul]; ring_nf
    rw [e1, e2, map_smul, smul_smul, mul_assoc, ← smul_smul] at e
    exact smul_right_injective _ hw e
  have hb := cont _ q h (-a) hne
  rw [evAt_qdetPoly, hqe] at hb
  have hzero : qdet (tensE X) (-a) h = 0 := by
    have e := tens_apply X χ hS (-a) g
    rw [hc] at e
    have e0 : (-a) • g + om X g = h := by rw [hh, neg_smul]; abel
    rw [e0] at e
    rw [e]
    simp
  rw [hzero] at hb
  have hct0 : ct (-a) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun t ht => ?_
    have ht' : t ≠ s := Finset.ne_of_mem_erase ht
    have : -a - cn n + χ t = χ t - χ s := by rw [ha]; ring
    rw [this]
    exact sub_ne_zero.2 (hs t ht')
  have hfin : ct (-a) • h = 0 := by
    have : ct (-a) * (-a + (a + 1)) = ct (-a) := by ring
    rw [this] at hb
    exact hb.symm
  exact (smul_eq_zero.1 hfin).resolve_left hct0

theorem omScal : OmScal := by
  intro n X χ s hS hs f hf
  set T : Module.End ℂ (Fin n → X.V) := om X - (χ s - cn n) • (1 : Module.End ℂ (Fin n → X.V)) with hT
  have hTa : ∀ w, T w = om X w - (χ s - cn n) • w := fun w => by simp [hT]
  have key : ∀ k : ℕ, (T ^ (k + 1)) f = 0 → T f = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      refine ih ?_
      have h2 : T (T ((T ^ k) f)) = 0 := by
        rw [← hk, pow_succ' T (k + 1), pow_succ' T k]
        rfl
      have h3 := core X χ s hS hs ((T ^ k) f) (by
        rw [hTa] at h2
        rw [← hTa]
        exact sub_eq_zero.1 h2)
      rw [← hTa] at h3
      rw [pow_succ' T k]
      exact h3
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hf
  have hk' : (T ^ (k + 1)) f = 0 := by
    rw [pow_succ' T k, Module.End.mul_apply]
    have : (T ^ k) f = 0 := hk
    rw [this, map_zero]
  have := key k hk'
  rw [hTa] at this
  exact sub_eq_zero.1 this

end GlobalTheory.CompanionTheory.RgExhHecke.OmScalP
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OmegaScalarStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.OmegaScalar : CompanionTheory.RgExh.Hk.OmScal := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.omScal | exact GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.omScal | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.omScal <;> assumption)
end
end

section -- merged from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.TensorReflections.PiIsoTensVd
noncomputable section

namespace CompanionTheory.RgExh.Hk

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

variable {n : ℕ}

theorem iso_symm' {X X' : GMod n} (h : Iso X X') : Iso X' X := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun a b x => ?_⟩
  apply e.injective
  rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem iso_trans' {X X' X'' : GMod n} (h : Iso X X') (h' : Iso X' X'') : Iso X X'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun a b x => by simp [he, he']⟩

theorem map_maxGen {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    (φ : M ≃ₗ[ℂ] M') (T : Module.End ℂ M) (T' : Module.End ℂ M') (hφ : ∀ x, φ (T x) = T' (φ x)) (μ : ℂ) :
    (T.maxGenEigenspace μ).map (φ : M →ₗ[ℂ] M') = T'.maxGenEigenspace μ := by
  have key : ∀ (k : ℕ) (x : M), φ (((T - μ • (1 : Module.End ℂ M)) ^ k) x) =
      ((T' - μ • (1 : Module.End ℂ M')) ^ k) (φ x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
      simp [hφ]
  ext y
  rw [Submodule.mem_map_equiv, Module.End.mem_maxGenEigenspace, Module.End.mem_maxGenEigenspace]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have := key k (φ.symm y)
    rw [hk, map_zero, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply φ.injective
    rw [key, LinearEquiv.apply_symm_apply, hk, map_zero]

theorem iso_sub' {X X' : GMod n} (φ : X.V ≃ₗ[ℂ] X'.V) (hφ : ∀ a b x, φ (X.E a b x) = X'.E a b (φ x))
    (S : Submodule ℂ X.V) (S' : Submodule ℂ X'.V) (hS : S.map (φ : X.V →ₗ[ℂ] X'.V) = S')
    (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S) (h' : ∀ a b, ∀ x ∈ S', X'.E a b x ∈ S') :
    Iso (X.sub S h) (X'.sub S' h') :=
  ⟨φ.ofSubmodules S S' hS, fun a b x => Subtype.ext (hφ a b x.1)⟩

def piIso {X X' : GMod n} (e : X.V ≃ₗ[ℂ] X'.V) : (Fin n → X.V) ≃ₗ[ℂ] (Fin n → X'.V) :=
  LinearEquiv.piCongrRight fun _ : Fin n => e

theorem piIso_tensVd {X X' : GMod n} (e : X.V ≃ₗ[ℂ] X'.V) (he : ∀ a b x, e (X.E a b x) = X'.E a b (e x))
    (a b : Fin n) (f : Fin n → X.V) : piIso e (tensVd X.E a b f) = tensVd X'.E a b (piIso e f) := by
  funext d
  by_cases hd : d = b
  · subst hd
    simp [piIso, tensVd, he]
  · simp [piIso, tensVd, he, hd]

theorem piIso_eeVd {X X' : GMod n} (e : X.V ≃ₗ[ℂ] X'.V) (he : ∀ a b x, e (X.E a b x) = X'.E a b (e x))
    (f : Fin n → X.V) : piIso e (eeVd X.E f) = eeVd X'.E (piIso e f) := by
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp [piIso, eeVd, he, map_sum]

theorem iso_back' {Y Y' : GMod n} (hY : Iso Y Y') (z : ℂ)
    (h : ∀ a b, ∀ x ∈ backSub Y z, (tensD Y).E a b x ∈ backSub Y z)
    (h' : ∀ a b, ∀ x ∈ backSub Y' z, (tensD Y').E a b x ∈ backSub Y' z) :
    Iso (back Y z h) (back Y' z h') := by
  obtain ⟨e, he⟩ := hY
  exact iso_sub' (X := tensD Y) (X' := tensD Y') (piIso e) (fun a b f => piIso_tensVd e he a b f) _ _
    (map_maxGen (piIso e) (omD Y) (omD Y') (fun f => piIso_eeVd e he f) _) h h'

theorem reflect_of' : QdetTens → OmScal → BackStable → DualFacts → Unit → Reflect := by
  intro _ hOm hB _ hU n X X' χ s hX hX' hfree hsimp hiso
  have h1 := hU n X χ s hB hX hfree hsimp (hOm n X χ s hX hsimp)
  have h2 := hU n X' χ s hB hX' hfree hsimp (hOm n X' χ s hX' hsimp)
  exact iso_trans' (iso_symm' h1) (iso_trans' (iso_back' hiso _ _ _) h2)

end CompanionTheory.RgExh.Hk
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeBackwardStable
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeBackwardStable
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgHeckeBack

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (tensVd eeVd)
open _root_.CompanionTheory.RgExh _root_.CompanionTheory.RgExh.Hk

variable {n : ℕ}

theorem tensVd_apply (X : GMod n) (a b : Fin n) (f : Fin n → X.V) (i : Fin n) :
    tensVd X.E a b f i = X.E a b (f i) - if i = b then f a else 0 := by
  by_cases h : i = b <;> simp [tensVd, h]

theorem eeVd_apply (X : GMod n) (f : Fin n → X.V) (a : Fin n) :
    eeVd X.E f a = -∑ c, X.E a c (f c) := by
  simp [eeVd]

theorem commute_tensVd_eeVd (X : GMod n) (c d : Fin n) : Commute (tensVd X.E c d) (eeVd X.E) := by
  refine LinearMap.ext fun f => funext fun a => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.End.mul_apply, tensVd_apply, eeVd_apply, map_neg, map_sum, map_sub]
  simp only [comm_apply X c d a _ _, sum_sub_distrib, sum_add_distrib, apply_ite (X.E a _), map_zero]
  by_cases h : a = d
  · subst h
    simp
    abel
  · simp [h, Ne.symm h]

theorem backStable : BackStable := fun _ X z a b _ hx =>
  Module.End.mapsTo_maxGenEigenspace_of_comm (commute_tensVd_eeVd X a b).symm (-z - cn _) hx

end GlobalTheory.CompanionTheory.RgHeckeBack
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeBackwardStableStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HeckeBackwardStable : CompanionTheory.RgExh.Hk.BackStable := by
  first | exact @GlobalTheory.CompanionTheory.RgHeckeBack.backStable | exact GlobalTheory.CompanionTheory.RgHeckeBack.backStable | (intros; apply GlobalTheory.CompanionTheory.RgHeckeBack.backStable <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonScalar
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonScalar
noncomputable section

open Finset Polynomial

namespace GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof

open _root_.CompanionTheory.RgExh _root_.CompanionTheory.RgExh.Hk ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

section Poly

variable {A : Type*} [Ring A] [Algebra ℂ A]

def IsP (g : ℂ → A) : Prop := ∃ p : A[X], ∀ t, g t = p.eval (algebraMap ℂ A t)

theorem IsP.const (a : A) : IsP (fun _ : ℂ => a) := ⟨C a, fun t => by simp⟩

theorem IsP.lin (a b : A) : IsP (fun t : ℂ => a + b * algebraMap ℂ A t) :=
  ⟨C a + C b * X, fun t => by simp [eval_mul_X]⟩

theorem IsP.mul {f g : ℂ → A} (hf : IsP f) (hg : IsP g) : IsP (fun t => f t * g t) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨p * q, fun t => ?_⟩
  show f t * g t = _
  rw [hp, hq]
  exact (eval₂_mul_noncomm (RingHom.id A) (algebraMap ℂ A t)
    (fun k => (Algebra.commutes t _).symm)).symm

theorem IsP.sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → A} (hf : ∀ i, IsP (f i)) :
    IsP (fun t => ∑ i ∈ s, f i t) := by
  choose p hp using hf
  exact ⟨∑ i ∈ s, p i, fun t => by simp [Polynomial.eval_finsetSum, hp]⟩

theorem IsP.listProd (l : List (ℂ → A)) (h : ∀ f ∈ l, IsP f) :
    IsP (fun t => (l.map fun f => f t).prod) := by
  induction l with
  | nil => simpa using IsP.const (1 : A)
  | cons f l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h f (by simp)).mul (ih fun g hg => h g (by simp [hg]))

theorem isPolynomial_capelliEntry {n : ℕ} (E : Fin n → Fin n → A) (x₀ : ℂ) (a b : Fin n) :
    IsP (fun t : ℂ => capEntry E (x₀ + t) a b) := by
  by_cases h : a = b
  · have := IsP.lin (E a b + algebraMap ℂ A x₀) (1 : A)
    convert this using 2 with t
    simp [capEntry, h, map_add (f := _), add_assoc]
  · have := IsP.const (E a b)
    convert this using 2 with t
    simp [capEntry, h]

theorem isPolynomial_capelliMinor {n p : ℕ} (E : Fin n → Fin n → A) (R S : Fin p → Fin n) (x₀ : ℂ) :
    IsP (fun t : ℂ => cminor E R S (x₀ + t)) := by
  unfold cminor
  refine IsP.sum _ fun σ => ?_
  have h := (IsP.const ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A))).mul
    (IsP.listProd (List.ofFn fun j : Fin p => fun t : ℂ =>
      capEntry E (x₀ - ((j : ℕ) : ℂ) + t) (R (σ j)) (S j)) (fun f hf => by
        obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hf
        exact isPolynomial_capelliEntry E _ _ _))
  convert h using 2 with t
  rw [zsmul_eq_mul, List.map_ofFn]
  congr 2
  refine congrArg List.ofFn (funext fun j => ?_)
  simp only [Function.comp]
  congr 1
  ring

end Poly

theorem coeff_extract {W : Type*} [AddCommGroup W] [Module ℂ W] (T : Module.End ℂ W) (k : ℕ) (hk : 2 ≤ k)
    (w : ℕ → W) (P : ℂ[X]) (u : W) (hP : (X : ℂ[X]) ^ 2 ∣ P)
    (h : ∀ t : ℂ, T (∑ i ∈ range k, t ^ i • w i) + t • ∑ i ∈ range k, t ^ i • w i = P.eval t • u) :
    T (w 0) = 0 ∧ T (w 1) + w 0 = 0 := by
  have hP' := (X_pow_dvd_iff (f := P) (n := 2)).1 hP
  have hP0 := hP' 0 (by norm_num)
  have hP1 := hP' 1 (by norm_num)
  have key : ∀ φ : Module.Dual ℂ W, φ (T (w 0)) = 0 ∧ φ (T (w 1) + w 0) = 0 := by
    intro φ
    have hQ : (∑ i ∈ range k, C (φ (T (w i))) * X ^ i) + X * (∑ i ∈ range k, C (φ (w i)) * X ^ i)
        - C (φ u) * P = 0 := by
      refine Polynomial.funext fun t => ?_
      have := congrArg φ (h t)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul] at this
      simp only [eval_sub, eval_add, eval_mul, Polynomial.eval_finsetSum, eval_C, eval_X, eval_pow, eval_zero]
      rw [sub_eq_zero, mul_comm (φ u)]
      simp only [mul_comm (φ _) (t ^ _)]
      exact this
    have c0 := congrArg (fun q : ℂ[X] => q.coeff 0) hQ
    have c1 := congrArg (fun q : ℂ[X] => q.coeff 1) hQ
    have k0 : 0 ∈ range k := mem_range.2 (by omega)
    have k1 : 1 ∈ range k := mem_range.2 (by omega)
    simp only [coeff_sub, coeff_add, Polynomial.finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero,
      mul_ite, mul_one, mul_zero, coeff_X_mul, coeff_X_mul_zero, hP0, hP1] at c0 c1
    simp [k0, k1] at c0 c1
    exact ⟨c0, by rw [map_add (f := _)]; exact c1⟩
  exact ⟨(Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => (key φ).1,
    (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => (key φ).2⟩

theorem om_nnPlus {m : ℕ} (X : GMod (m + 1)) (y : Fin (m + 1) → ℂ) (x : ℂ) (v : X.V) :
    om X (nnPlus X.E y x v) + x • nnPlus X.E y x v = fun b => y b • capelliC X.E x v := by
  have hE' : GlRelR X.E := X.gl
  funext b
  have key : ∀ c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
      X.E d b (cminor X.E d.succAbove c.succAbove (x - 1) v) +
      (x * (-1 : ℂ) ^ ((b : ℕ) + (c : ℕ))) • cminor X.E b.succAbove c.succAbove (x - 1) v =
      (if b = c then capelliC X.E x else 0) v := by
    intro c
    have h := LinearMap.congr_fun (capelli_expand_plus X.E hE' x b c) v
    rw [LinearMap.sum_apply] at h
    simp only [LinearMap.smul_apply, Module.End.mul_apply, capEntry, LinearMap.add_apply, smul_add,
      Finset.sum_add_distrib] at h
    have h2 : ∑ z : Fin (m + 1), ((-1 : ℂ) ^ ((z : ℕ) + (c : ℕ))) •
        (if z = b then algebraMap ℂ (Module.End ℂ X.V) x else 0) (cminor X.E z.succAbove c.succAbove (x - 1) v) =
        (x * (-1 : ℂ) ^ ((b : ℕ) + (c : ℕ))) • cminor X.E b.succAbove c.succAbove (x - 1) v := by
      rw [Finset.sum_eq_single b]
      · simp [Module.algebraMap_end_apply, smul_smul, mul_comm]
      · intro d _ hd; simp [hd]
      · simp
    rw [h2] at h
    exact h
  have hR : y b • capelliC X.E x v = ∑ c, y c • (if b = c then capelliC X.E x else 0) v := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  show om X (nnPlus X.E y x v) b + x • nnPlus X.E y x v b = y b • capelliC X.E x v
  rw [hR, om_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [nnPlus, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← key c, smul_add, Finset.smul_sum]
  simp only [smul_smul]
  rw [mul_left_comm]

theorem nonScal : NonScal := by
  intro n X χ s hS hN hfree ⟨r, hrs, hr⟩
  cases n with
  | zero => exact s.elim0
  | succ m =>
  have hE' : GlRelR X.E := X.gl
  set ω : ℂ := cn (m + 1) - χ s with hω

  have hC : ∀ x : ℂ, capelliC X.E x = Formalism.QuantumDeterminants.capP χ (x - cn (m + 1)) • (1 : Module.End ℂ X.V) := by
    intro x
    have h := hS (x - cn (m + 1))
    have e : x - cn (m + 1) + (((m + 1 : ℕ) : ℂ) - 1) / 2 = x := by simp [cn]
    rw [e, GlobalTheory.CompanionTheory.RgExhHecke.qdetEq] at h
    exact h

  set P : ℂ[X] := ∏ q : Fin (m + 1), (Polynomial.X + C (χ q - χ s)) with hPdef
  have hPe : ∀ t : ℂ, P.eval t = Formalism.QuantumDeterminants.capP χ (ω + t - cn (m + 1)) := by
    intro t
    simp only [hPdef, eval_prod, eval_add, eval_X, eval_C, Formalism.QuantumDeterminants.capP]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [hω]; ring
  have hPd : (Polynomial.X : ℂ[X]) ^ 2 ∣ P := by
    have hs : s ∈ (univ : Finset (Fin (m + 1))) := mem_univ s
    have hr' : r ∈ (univ.erase s) := mem_erase.2 ⟨hrs, mem_univ r⟩
    rw [hPdef, ← Finset.mul_prod_erase univ _ hs, ← Finset.mul_prod_erase _ _ hr', hr, sub_self, C_0, add_zero,
      ← mul_assoc, pow_two]
    exact Dvd.intro _ rfl

  obtain ⟨v, hv⟩ := exists_ne (0 : X.V)
  have hc1 : Formalism.QuantumDeterminants.capP χ (ω - 1 - cn (m + 1)) ≠ 0 := by
    simp only [Formalism.QuantumDeterminants.capP]
    refine Finset.prod_ne_zero_iff.2 fun q _ hq => hfree q ?_
    rw [hω] at hq
    linear_combination hq
  obtain ⟨d, hd⟩ : ∃ d : Fin (m + 1), cminor X.E s.succAbove d.succAbove (ω - 1) v ≠ 0 := by
    by_contra hall
    push_neg at hall
    have h := LinearMap.congr_fun (capelli_expand_minus X.E hE' (ω - 1) s s) v
    rw [LinearMap.sum_apply, if_pos rfl, hC] at h
    have h0 : ∑ d : Fin (m + 1), (((-1 : ℂ) ^ ((d : ℕ) + (s : ℕ))) •
        (capEntry X.E (ω - 1 - (m : ℂ)) s d * cminor X.E s.succAbove d.succAbove (ω - 1))) v = 0 :=
      Finset.sum_eq_zero fun d _ => by simp [Module.End.mul_apply, hall d]
    rw [h0] at h
    have h1 : Formalism.QuantumDeterminants.capP χ (ω - 1 - cn (m + 1)) • v = 0 := by simpa using h.symm
    exact (smul_ne_zero hc1 hv) h1
  set y : Fin (m + 1) → ℂ := Pi.single d 1 with hy
  choose p hp using fun a b : Fin (m + 1) => isPolynomial_capelliMinor X.E a.succAbove b.succAbove (ω - 1)
  set k : ℕ := (univ.sup fun ab : Fin (m + 1) × Fin (m + 1) => (p ab.1 ab.2).natDegree) + 2 with hk
  have hdeg : ∀ a b, (p a b).natDegree < k := fun a b => by
    have := Finset.le_sup (f := fun ab : Fin (m + 1) × Fin (m + 1) => (p ab.1 ab.2).natDegree)
      (mem_univ (a, b))
    simp only at this
    omega
  set w : ℕ → Fin (m + 1) → X.V :=
    fun i a => ∑ c, (y c * (-1) ^ ((a : ℕ) + (c : ℕ))) • ((p a c).coeff i) v with hw
  have hexp : ∀ (a c : Fin (m + 1)) (t : ℂ), cminor X.E a.succAbove c.succAbove (ω + t - 1) v =
      ∑ i ∈ range k, t ^ i • ((p a c).coeff i) v := by
    intro a c t
    have e : ω + t - 1 = ω - 1 + t := by ring
    have hp' : cminor X.E a.succAbove c.succAbove (ω - 1 + t) = _ := hp a c t
    rw [e, hp', eval_eq_sum_range' (hdeg a c), LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_pow, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
  have hNt : ∀ t : ℂ, nnPlus X.E y (ω + t) v = ∑ i ∈ range k, t ^ i • w i := by
    intro t
    funext a
    simp only [nnPlus, hexp, Finset.sum_apply, Pi.smul_apply, hw, Finset.smul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => smul_comm _ _ _
  set T : Module.End ℂ (Fin (m + 1) → X.V) := om X + ω • 1 with hT
  have hid : ∀ t : ℂ, T (∑ i ∈ range k, t ^ i • w i) + t • ∑ i ∈ range k, t ^ i • w i =
      P.eval t • (fun b => y b • v) := by
    intro t
    rw [← hNt]
    have h := om_nnPlus X y (ω + t) v
    have e : T (nnPlus X.E y (ω + t) v) + t • nnPlus X.E y (ω + t) v =
        om X (nnPlus X.E y (ω + t) v) + (ω + t) • nnPlus X.E y (ω + t) v := by
      simp [hT, add_smul, add_assoc]
    rw [e, h, hC, ← hPe]
    funext b
    simp only [LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply]
    exact smul_comm _ _ _
  obtain ⟨h0, h1⟩ := coeff_extract T k (by omega) w P _ hPd hid
  have hw0 : w 0 = nnPlus X.E y ω v := by
    have := hNt 0
    rw [add_zero] at this
    rw [this, Finset.sum_eq_single 0]
    · simp
    · intro i _ hi; simp [hi]
    · intro h; exact absurd (mem_range.2 (by omega)) h
  have hw0ne : w 0 ≠ 0 := by
    intro h
    rw [hw0] at h
    have h2 := congrFun h s
    simp only [nnPlus, Pi.zero_apply] at h2
    rw [Finset.sum_eq_single d] at h2
    · simp [hy] at h2
      exact hd h2
    · intro c _ hc; simp [hy, hc]
    · simp
  have hTa : ∀ f, T f = 0 ↔ om X f = (χ s - cn (m + 1)) • f := by
    intro f
    have : χ s - cn (m + 1) = -ω := by rw [hω]; ring
    rw [this, hT, neg_smul, eq_neg_iff_add_eq_zero]
    simp
  refine ⟨w 1, ?_, fun h => hw0ne ?_⟩
  · have ha : χ s - (((m + 1 : ℕ) : ℂ) - 1) / 2 = -ω := by rw [hω]; simp [cn]
    show w 1 ∈ (om X).maxGenEigenspace (χ s - (((m + 1 : ℕ) : ℂ) - 1) / 2)
    rw [ha, Module.End.mem_maxGenEigenspace]
    refine ⟨2, ?_⟩
    have e : om X - (-ω) • (1 : Module.End ℂ (Fin (m + 1) → X.V)) = T := by simp [hT]
    have e2 : T (w 1) = - w 0 := eq_neg_of_add_eq_zero_left h1
    rw [e, pow_two, Module.End.mul_apply, e2, map_neg, h0, neg_zero]
  · have := (hTa _).2 h
    rw [this, zero_add] at h1
    exact h1

end GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonScalarStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HeckeNonScalar : CompanionTheory.RgExh.Hk.NonScal := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.nonScal | exact GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.nonScal | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.nonScal <;> assumption)
end
end

namespace CompanionTheory.RgExh.Hk

theorem unitarity : Unit := UnitB.unit_of_dualFacts dual_module_facts

theorem reflection_symmetry : Reflect :=
  reflect_of' GlobalTheory.T.QuantumDeterminantTensor GlobalTheory.T.OmegaScalar GlobalTheory.T.HeckeBackwardStable dual_module_facts unitarity

theorem forward_simple_module : FwdSimple :=
  forward_simple_of_tensor_facts GlobalTheory.T.QuantumDeterminantTensor GlobalTheory.T.HeckeBackwardStable dual_module_facts unitarity

theorem infinitesimal_character_shift : CompanionTheory.RgExh.StepChar := GlobalTheory.T.InfinitesimalCharacterStatement

theorem hecke_algebra_exhaustion : CompanionTheory.RgExh.Hecke :=
  hecke_of' GlobalTheory.T.QuantumDeterminantEquality GlobalTheory.T.InfinitesimalCharacterStatement GlobalTheory.T.CayleyHamiltonHk GlobalTheory.T.HeckeNonVanishing GlobalTheory.T.HeckeNonScalar GlobalTheory.T.HeckeBackward GlobalTheory.T.OmegaScalar
    forward_simple_module reflection_symmetry

end CompanionTheory.RgExh.Hk
end

namespace CompanionTheory.RgExh

theorem dsExhaust : GlobalTheory.Dec.DSExhaust :=
  Fin.exhaustion_finite_length Hk.infinitesimal_character_shift Hk.hecke_algebra_exhaustion (Dec.decay_estimate Hk.infinitesimal_character_shift) U.far_regular_exhaustion

theorem discreteSeriesClassification : GlobalTheory.Published.DiscreteSeriesClassification :=
  Fin.discreteSeriesClassification_of dsExhaust

theorem discreteSeriesCover : GlobalTheory.Published.DiscreteSeriesCover := Fin.discreteSeriesCover_of dsExhaust

end CompanionTheory.RgExh
