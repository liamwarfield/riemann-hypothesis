module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.GOpsEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ValInvAnti
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.IndicatorEqOneOfTrue
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.SplitLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.AdmissibleTraceRegular
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.QuaternionStableSideTraceIdentity

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.PosSpec
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.TrPos
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceNil
open Module

namespace UpperTheory.V.Z.Sym.Tf

variable {Λ M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]

private theorem iter_lemma (n : Λ → End ℂ M) (Θ : End ℂ M) (σ : Λ → Λ) (h : ∀ a, Θ * n a = n (σ a) * Θ) :
    ∀ (k : ℕ) (b : Λ), Θ ^ k * n b = n (σ^[k] b) * Θ ^ k := by
  intro k
  induction k with
  | zero => intro b; simp
  | succ k ih =>
    intro b
    rw [pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc, Function.iterate_succ_apply]

private theorem mul_pow_eq_prod_range_iterate_mul_pow_of_semiconj (n : Λ → End ℂ M) (Θ : End ℂ M) (σ : Λ → Λ) (h : ∀ a, Θ * n a = n (σ a) * Θ)
    (a : Λ) : ∀ k : ℕ, (n a * Θ) ^ k = ((List.range k).map (fun i => n (σ^[i] a))).prod * Θ ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, mul_assoc, ← mul_assoc (Θ ^ k), iter_lemma n Θ σ h]
    simp [List.range_succ, pow_succ, mul_assoc]

private theorem list_prod_mem_ideal_pow_length {R : Type} [CommRing R] (I : Ideal R) :
    ∀ l : List R, (∀ x ∈ l, x ∈ I) → l.prod ∈ I ^ l.length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x l ih =>
    intro hl
    rw [List.prod_cons, List.length_cons, pow_succ']
    exact Ideal.mul_mem_mul (hl x (by simp)) (ih fun y hy => hl y (by simp [hy]))

private theorem exists_prod_range_iterate_eq_zero_of_commute_of_isNilpotent (n : Λ → End ℂ M) (σ : Λ → Λ) (hc : ∀ a b, Commute (n a) (n b))
    (hn : ∀ a, IsNilpotent (n a)) (a : Λ) :
    ∃ m : ℕ, ((List.range m).map (fun i => n (σ^[i] a))).prod = 0 := by
  let A := Algebra.adjoin ℂ (Set.range n)
  letI : IsMulCommutative A := Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _
    exact hc x y)
  letI : CommRing A := by
    open scoped IsMulCommutative in
    exact inferInstance
  haveI : IsArtinianRing A := IsArtinianRing.of_finite ℂ A
  obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_nilradical A
  let g : ℕ → A := fun i => ⟨n (σ^[i] a), Algebra.subset_adjoin ⟨σ^[i] a, rfl⟩⟩
  have hmem : ∀ i, g i ∈ nilradical A := by
    intro i
    obtain ⟨k, hk⟩ := hn (σ^[i] a)
    exact ⟨k, Subtype.ext (by simpa [g] using hk)⟩
  have hP := list_prod_mem_ideal_pow_length (nilradical A) ((List.range m).map g) (by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hmem i)
  simp only [List.length_map, List.length_range, hm, Ideal.zero_eq_bot, Ideal.mem_bot] at hP
  refine ⟨m, ?_⟩
  have h2 := congrArg A.val hP
  rw [map_list_prod, map_zero, List.map_map] at h2
  exact h2

theorem trace_nil (n : Λ → End ℂ M) (Θ : End ℂ M) (σ : Λ → Λ) (hc : ∀ a b, Commute (n a) (n b)) (hn : ∀ a, IsNilpotent (n a))
    (h : ∀ a, Θ * n a = n (σ a) * Θ) (a : Λ) : LinearMap.trace ℂ M (n a * Θ) = 0 := by
  obtain ⟨m, hm⟩ := exists_prod_range_iterate_eq_zero_of_commute_of_isNilpotent n σ hc hn a
  have hnil : IsNilpotent (n a * Θ) := ⟨m, by rw [mul_pow_eq_prod_range_iterate_mul_pow_of_semiconj n Θ σ h a m, hm, zero_mul]⟩
  exact (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero

abbrev Vg (u : Λ → End ℂ M) (χ : Λ → ℂ) : Submodule ℂ M := ⨅ a, (u a).maxGenEigenspace (χ a)

theorem Vg_maps {u : Λ → End ℂ M} (hc : ∀ a b, Commute (u a) (u b)) (a : Λ) (χ : Λ → ℂ) : Set.MapsTo (u a) (Vg u χ) (Vg u χ) := by
  intro v hv
  simp only [Vg, SetLike.mem_coe, Submodule.mem_iInf] at hv ⊢
  intro b
  exact Module.End.mapsTo_maxGenEigenspace_of_comm (hc b a) (χ b) (hv b)

theorem Vg_indep {u : Λ → End ℂ M} (hc : ∀ a b, Commute (u a) (u b)) : iSupIndep (Vg u) :=
  End.independent_iInf_maxGenEigenspace_of_forall_mapsTo u fun i j φ => End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ

theorem Vg_int [DecidableEq (Λ → ℂ)] {u : Λ → End ℂ M} (hc : ∀ a b, Commute (u a) (u b)) : DirectSum.IsInternal (Vg u) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (Vg_indep hc)
  exact Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute u
    (fun i j _ => hc i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top (u i))

theorem trace_Vg {u : Λ → End ℂ M} (hc : ∀ a b, Commute (u a) (u b)) (χ : Λ → ℂ) (Θ : End ℂ M) (σ : Λ → Λ)
    (hΘ : Set.MapsTo Θ (Vg u χ) (Vg u χ)) (h : ∀ a, ∀ v ∈ Vg u χ, Θ (u a v) = u (σ a) (Θ v)) (hχ : ∀ a, χ (σ a) = χ a) (a : Λ)
    (h' : Set.MapsTo (u a * Θ) (Vg u χ) (Vg u χ)) :
    LinearMap.trace ℂ (Vg u χ) ((u a * Θ).restrict h') = LinearMap.trace ℂ (Vg u χ) (Θ.restrict hΘ) * χ a := by
  have key : ∀ (f : End ℂ M) (hf : Set.MapsTo f (Vg u χ) (Vg u χ)) (x : Vg u χ),
      ((f.restrict hf x : Vg u χ) : M) = f x := fun _ _ _ => rfl
  have hNm : ∀ b, Set.MapsTo (u b - algebraMap ℂ (End ℂ M) (χ b)) (Vg u χ) (Vg u χ) := by
    intro b v hv
    have h1 := Vg_maps hc b χ hv
    simp only [SetLike.mem_coe] at h1 hv ⊢
    simp only [LinearMap.sub_apply, Module.algebraMap_end_apply]
    exact Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ hv)
  let N : Λ → End ℂ (Vg u χ) := fun b => (u b - algebraMap ℂ (End ℂ M) (χ b)).restrict (hNm b)
  let T : End ℂ (Vg u χ) := Θ.restrict hΘ
  have hNc : ∀ b c, Commute (N b) (N c) := by
    intro b c
    show N b * N c = N c * N b
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    have e := LinearMap.congr_fun (hc b c).eq (w : M)
    simp only [Module.End.mul_apply] at e
    simp only [N, Module.End.mul_apply, key, LinearMap.sub_apply,
      Module.algebraMap_end_apply, map_sub, map_smul, e]
    module
  have hNn : ∀ b, IsNilpotent (N b) := by
    intro b
    exact Module.End.isNilpotent_restrict_of_le (q := (u b).maxGenEigenspace (χ b)) (iInf_le _ b)
      ((u b).isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (χ b))
  have hTN : ∀ b, T * N b = N (σ b) * T := by
    intro b
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    have e := h b w w.2
    simp only [T, N, Module.End.mul_apply, key, LinearMap.sub_apply,
      Module.algebraMap_end_apply, map_sub, map_smul, e]
    rw [hχ]
  have hsplit : (u a * Θ).restrict h' = N a * T + χ a • T := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp only [N, T, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Submodule.coe_add, Submodule.coe_smul, key, LinearMap.sub_apply,
      Module.algebraMap_end_apply]
    abel
  rw [hsplit, map_add (f := _), map_smul, trace_nil N T σ hNc hNn hTN a, zero_add, smul_eq_mul, mul_comm]

end UpperTheory.V.Z.Sym.Tf
end

open Module in
theorem UpperTheory.V.Z.Sym.Tf.trPos :
    UpperTheory.V.Z.Sym.Tf.TrPos := by
  intro Λ M _ _ _ u hc
  classical
  have hint := UpperTheory.V.Z.Sym.Tf.Vg_int (u := u) hc
  have hfin : {χ | UpperTheory.V.Z.Sym.Tf.Vg u χ ≠ ⊥}.Finite := by
    have := (UpperTheory.V.Z.Sym.Tf.Vg_indep hc).fintypeNeBotOfFiniteDimensional
    exact Set.finite_coe_iff.mp (@Finite.of_fintype _ this)
  refine ⟨hfin.toFinset, fun χ => Module.finrank ℂ (UpperTheory.V.Z.Sym.Tf.Vg u χ), ?_, ?_, ?_⟩
  · intro χ
    simp [Set.Finite.mem_toFinset, UpperTheory.V.Z.Sym.IsGenEig]
  · intro χ hχ
    rw [Set.Finite.mem_toFinset] at hχ
    exact Submodule.one_le_finrank_iff.mpr hχ
  · intro a
    rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin (fun χ => UpperTheory.V.Z.Sym.Tf.Vg_maps hc a χ)]
    refine Finset.sum_congr rfl fun χ _ => ?_
    have h1 : Set.MapsTo ⇑(1 : Module.End ℂ M) ↑(UpperTheory.V.Z.Sym.Tf.Vg u χ) ↑(UpperTheory.V.Z.Sym.Tf.Vg u χ) :=
      fun v hv => hv
    have key := UpperTheory.V.Z.Sym.Tf.trace_Vg hc χ 1 id h1 (fun b v _ => by simp) (fun b => rfl) a
      (by simpa using UpperTheory.V.Z.Sym.Tf.Vg_maps hc a χ)
    simp only [mul_one] at key
    rw [key]
    have h2 : LinearMap.restrict (1 : Module.End ℂ M) h1 = 1 := by
      ext v
      rfl
    rw [h2, LinearMap.trace_one, mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.Extract
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Artin
theorem UpperTheory.Reformulated.B.Qh30.artin :
    ∀ {P : Type} [inst : Mul P] (T : Finset (P → ℂ))
    (c : (P → ℂ) → ℂ),
    (∀ χ ∈ T, χ ≠ (0 : P → ℂ) ∧ ∀ (p q : P), χ (p * q) = χ p * χ q) →
      (∀ (p : P), ∑ χ ∈ T, c χ * χ p = (0 : ℂ)) → ∀ χ ∈ T, c χ = (0 : ℂ) := by
  intro P inst T
  classical
  induction T using Finset.induction_on with
  | empty => intro c _ _ χ hχ; simp at hχ
  | insert ψ T hψ ih =>
    intro c hT h
    have hψm := hT ψ (Finset.mem_insert_self ψ T)
    have hT' : ∀ χ ∈ T, χ ≠ (0 : P → ℂ) ∧ ∀ (p q : P), χ (p * q) = χ p * χ q :=
      fun χ hχ => hT χ (Finset.mem_insert_of_mem hχ)
    have key : ∀ q : P, ∀ χ ∈ T, c χ * (χ q - ψ q) = 0 := by
      intro q
      refine ih (fun χ => c χ * (χ q - ψ q)) hT' ?_
      intro p
      have h1 := h (q * p)
      have h2 := h p
      rw [Finset.sum_insert hψ] at h1 h2
      have h3 : ∑ χ ∈ T, c χ * (χ q - ψ q) * χ p
          = ∑ χ ∈ T, c χ * χ (q * p) - ψ q * ∑ χ ∈ T, c χ * χ p := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun χ hχ => ?_
        rw [(hT' χ hχ).2]
        ring
      rw [hψm.2] at h1
      rw [h3]
      linear_combination h1 - ψ q * h2
    have hc : ∀ χ ∈ T, c χ = 0 := by
      intro χ hχ
      by_contra hne
      have : χ = ψ := by
        funext q
        exact sub_eq_zero.mp ((mul_eq_zero.mp (key q χ hχ)).resolve_left hne)
      exact hψ (this ▸ hχ)
    have hcψ : c ψ = 0 := by
      by_contra hne
      apply hψm.1
      funext p
      have h2 := h p
      rw [Finset.sum_insert hψ, Finset.sum_eq_zero (fun χ hχ => by rw [hc χ hχ, zero_mul]),
        add_zero] at h2
      exact (mul_eq_zero.mp h2).resolve_left hne
    intro χ hχ
    rcases Finset.mem_insert.mp hχ with rfl | hχ
    · exact hcψ
    · exact hc χ hχ
end

private theorem artin {P : Type} [Mul P] (T : Finset (P → ℂ)) : ∀ c : (P → ℂ) → ℂ,
    (∀ χ ∈ T, χ ≠ 0 ∧ ∀ p q, χ (p * q) = χ p * χ q) → (∀ p, ∑ χ ∈ T, c χ * χ p = 0) → ∀ χ ∈ T, c χ = 0 :=
  _root_.UpperTheory.Reformulated.B.Qh30.artin T

private theorem grp {P I : Type} [DecidableEq (P → ℂ)] (S : Finset I) (a : I → ℂ) (α : I → P → ℂ) (T : Finset (P → ℂ))
    (h : ∀ i ∈ S, α i ≠ 0 → α i ∈ T) (p : P) :
    ∑ χ ∈ T, (∑ i ∈ S.filter (fun i => α i = χ), a i) * χ p = ∑ i ∈ S, a i * α i p := by
  simp only [Finset.sum_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases h0 : α i = 0
  · rw [h0]; simp only [Pi.zero_apply, mul_zero]
    refine Finset.sum_eq_zero fun χ _ => ?_
    split_ifs with e
    · subst e; simp
    · simp
  · rw [Finset.sum_eq_single (α i) (fun χ _ e => by simp [e.symm]) fun e => absurd (h i hi h0) e]; simp

theorem UpperTheory.V.Z.Sym.Tf.extract :
    UpperTheory.V.Z.Sym.Tf.Extract := by
  classical
  intro P I J _ S S' a b α β hα hβ h χ hχ hb
  by_contra hn
  push Not at hn
  set T := (S.image α ∪ S'.image β).filter (· ≠ 0) with hT
  have key := artin T (fun χ => ∑ i ∈ S.filter (fun i => α i = χ), a i - ∑ j ∈ S'.filter (fun j => β j = χ), b j)
    (fun ψ hψ => by
      simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_image] at hψ
      refine ⟨hψ.2, ?_⟩
      rcases hψ.1 with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      exacts [hα i hi, hβ i hi])
    (fun p => by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [grp S a α T (fun i hi h0 => by simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_image]; exact ⟨.inl ⟨i, hi, rfl⟩, h0⟩),
        grp S' b β T (fun i hi h0 => by simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_image]; exact ⟨.inr ⟨i, hi, rfl⟩, h0⟩),
        h, sub_self])
  obtain ⟨j, hj, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  have hj' := Finset.mem_filter.1 hj
  have := key χ (by simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_image]; exact ⟨.inr ⟨j, hj'.1, hj'.2⟩, hχ⟩)
  rw [Finset.sum_eq_zero (s := S.filter _) fun i hi => by
    by_contra e; exact hn i (Finset.mem_filter.1 hi).1 e (Finset.mem_filter.1 hi).2, zero_sub, neg_eq_zero] at this
  exact hb (by convert this)
end

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma mul_of_genEig {P M : Type} [CommSemigroup P] [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (u : P → Module.End ℂ M) (hu : ∀ p q, u (p * q) = u p * u q) (hc : ∀ p q, Commute (u p) (u q))
    (ψ : P → ℂ) (h : IsGenEig u ψ) (p q : P) : ψ (p * q) = ψ p * ψ q := by
  obtain ⟨v, hv0, hv⟩ := (Tf.eigVec P M u hc ψ).1 h
  have h1 := hv (p * q)
  rw [hu, Module.End.mul_apply, hv q, map_smul, hv p, smul_smul] at h1
  rw [mul_comm (ψ p)]
  exact (smul_left_injective ℂ hv0 h1).symm

theorem UpperTheory.V.Z.Sym.So.posSpec :
    UpperTheory.V.Z.Sym.So.PosSpec := by
  unfold UpperTheory.V.Z.Sym.So.PosSpec
  intro P N I J _ _ _ _ _ Mi _ _ _ u w hu hw X b β hβ a c ha htr χ hχ hex
  have hcu : ∀ j p q, Commute (u j p) (u j q) := fun j p q => by
    unfold Commute SemiconjBy
    rw [← hu, ← hu, mul_comm]
  have hcw : ∀ p q, Commute (w p) (w q) := fun p q => by
    unfold Commute SemiconjBy
    rw [← hw, ← hw, mul_comm]
  by_cases hN : ∃ v, v ≠ 0 ∧ ∀ p, w p v = χ p • v
  · exact Or.inr hN
  left
  choose XX dd hXX hdd htrj using fun j => Tf.trPos P (Mi j) (u j) (hcu j)
  obtain ⟨XN, dN, hXN, hdN, htrN⟩ := Tf.trPos P N w hcw
  obtain ⟨j0, v0, hv0, hv0'⟩ := hex
  have hχj0 : χ ∈ XX j0 :=
    (hXX j0 χ).2 ((Tf.eigVec P (Mi j0) (u j0) (hcu j0) χ).2 ⟨v0, hv0, hv0'⟩)
  have hχN : χ ∉ XN := fun h => hN ((Tf.eigVec P N w hcw χ).1 ((hXN χ).1 h))
  let T : Option J → Finset (P → ℂ) := fun o => Option.elim o XN XX
  let S' : Finset (Σ _ : Option J, P → ℂ) := Finset.univ.sigma T
  let b' : (Σ _ : Option J, P → ℂ) → ℂ := fun k =>
    Option.elim k.1 ((c : ℂ) * (dN k.2 : ℂ)) (fun j => (a : ℂ) * (dd j k.2 : ℂ))
  let β' : (Σ _ : Option J, P → ℂ) → P → ℂ := fun k => k.2
  refine Tf.extract P I (Σ _ : Option J, P → ℂ) X S' b b' β β' hβ ?_ ?_ χ hχ ?_
  · rintro ⟨o, ψ⟩ hk p q
    simp only [S', Finset.mem_sigma, Finset.mem_univ, true_and] at hk
    cases o with
    | none => exact mul_of_genEig w hw hcw ψ ((hXN ψ).1 hk) p q
    | some j => exact mul_of_genEig (u j) (hu j) (hcu j) ψ ((hXX j ψ).1 hk) p q
  · intro p
    rw [htr p, htrN p]
    simp only [htrj, S', Finset.sum_sigma, Fintype.sum_option, T, b', β', Option.elim,
      Finset.mul_sum, mul_assoc]
    exact add_comm _ _
  · open ComplexOrder in
    · refine (Finset.sum_pos ?_ ⟨⟨some j0, χ⟩, ?_⟩).ne'
      · rintro ⟨o, ψ⟩ hk
        simp only [S', β', Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and] at hk
        obtain ⟨hk1, rfl⟩ := hk
        cases o with
        | none => exact absurd hk1 hχN
        | some j =>
          simp only [b', Option.elim]
          exact mul_pos (Complex.zero_lt_real.2 ha) (by exact_mod_cast hdd j ψ hk1)
      · simp [S', β', T, hχj0]

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.TFId0
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.QuotSumCongr
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IsScal
open NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem tau_eq {K : Type} [Field K] {Δ τ τ' : K} (hr : τ ^ 2 - 4 ≠ 0) {γ : DX Δ} {j} (hγ : HasTr γ τ) (hj : IsEmb τ γ j)
    {z : (Etau K τ)ˣ} (hz : (z : Etau K τ) = 1 + QuadraticAlgebra.omega) (y : DX Δ)
    (h : (mt (y⁻¹ * j z * y)).trace ^ 2 = algebraMap K _ (2 + τ') * (mt (y⁻¹ * j z * y)).det) : τ' = τ := by
  have e : mt (y⁻¹ * j z * y) = mt y⁻¹ * mt (j z) * mt y := rfl
  have e' : mt y * mt y⁻¹ = 1 := by
    change mt (y * y⁻¹) = 1
    rw [mul_inv_cancel]; rfl
  have e1 : mt (j z) = 1 + mt γ := by rw [hj, hz]; simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have h1 := hγ.1
  have h2 := hγ.2
  rw [Matrix.det_fin_two] at h1
  rw [Matrix.trace_fin_two] at h2
  have t1 : (mt (j z)).trace = algebraMap K _ (2 + τ) := by
    rw [e1, Matrix.trace_fin_two, map_add (f := _), map_ofNat, ← h2]; simp; ring
  have t2 : (mt (j z)).det = algebraMap K _ (2 + τ) := by
    rw [e1, Matrix.det_fin_two, map_add (f := _), map_ofNat, ← h2]; simp; linear_combination h1
  rw [e, Matrix.trace_mul_cycle, e', one_mul, Matrix.det_mul, mul_comm _ (mt y).det, Matrix.det_mul, ← mul_assoc (mt y).det,
    ← Matrix.det_mul, e', Matrix.det_one, one_mul, t1, t2, ← map_pow, ← map_mul] at h
  have h3 := (algebraMap K (Lsq K Δ)).injective h
  have h4 : 2 + τ ≠ 0 := fun e => hr (by linear_combination (τ - 2) * e)
  exact mul_right_cancel₀ h4 (by linear_combination -h3)

theorem UpperTheory.V.Z.Sym.Glob.gqK :
    UpperTheory.V.Z.Sym.Glob.GqK := by
  classical
  intro F _ _ Δ D hD ι hι t ht τ hτ γ j hγ hj z hz
  haveI := hD.real
  have hr := cm_ne hτ
  have htr : ∀ v, HasTr ((ι γ).1 v) (cv v τ) := fun v => hasTr_map _ (hι γ v) hγ
  have f1 : ∀ v ∈ D.Sg, D.fKv t v = (D.S v).fK (t v) := fun v hv => funext fun g => if_pos hv
  have f2 : ∀ v ∉ D.Sg, D.fKv t v = fZD (Ov v) (D.χ v) := fun v hv => funext fun g => if_neg hv
  have J1 : ∀ v ∈ D.Sg, D.J2v v = (D.S v).J2 := fun v hv => if_pos hv
  have J2 : ∀ v ∉ D.Sg, D.J2v v = KD _ (Ov v) := fun v hv => if_neg hv
  choose zv hzv using fun v => zEx (cv_reg hr v)
  have ez : ∀ v jv, IsEmb (cv v τ) ((ι γ).1 v) jv → (ι (j z)).1 v = jv (zv v) := fun v jv hjv =>
    dx_ext ((hι (j z) v).trans (emb_map _ (hι γ v) hj hjv z _ (by
      rw [hzv, hz]; ext <;> simp [emap, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one])).symm)
  have k1 : ∀ v ∉ D.Sg, ∀ k ∈ KD _ (Ov v), fZD (Ov v) (D.χ v) k = 1 := fun v hv k hk => by
    have := (Loc.fzdLaw _ _ _ (hD.off v hv) _ (hD.chi v).1).2 1 1 k (by simp [IsScal, mt]) hk
    simpa using this
  by_cases hA : D.admitted t τ
  · rw [show one (D.admitted t τ) = 1 from if_pos hA, one_mul]
    refine gqD D hD ι hι t ht τ hτ hA γ j hγ hj (j z) (D.fKv t) (fun v => ?_) _ _ fun v jv hjv => ?_
    · by_cases hv : v ∈ D.Sg
      · rw [f1 v hv, J1 v hv]
        intro u hu x
        rw [(((hD.sig v hv).K_inv _ (ht v hv)).1 u hu _).2, (((hD.sig v hv).K_inv _ (ht v hv)).1 _ (inv_mem hu) _).1]
      · rw [f2 v hv, J2 v hv]
        exact fZD_conj _ (hD.off v hv) _ (hD.chi v).1
    · rw [ez v jv hjv]
      refine ⟨fun s => by rw [← map_mul, ← map_mul, mul_comm], ?_⟩
      by_cases hv : v ∈ D.Sg
      · rw [f1 v hv, J1 v hv]
        obtain ⟨-, h1, -, h3, -⟩ := (hD.sig v hv).D_orb _ (ht v hv) _ _ _ (cv_reg hr v) (htr v) hjv _ (hzv v)
        exact ⟨h1, fun _ => by rw [h3, show one (Ind _ _ _) = 1 from if_pos (hA v hv), mul_one], fun h => absurd hv h⟩
      · rw [f2 v hv, J2 v hv]
        refine ⟨(Loc.finD _ _ _ _ (hD.off v hv) (cv_reg hr v) _ _ (htr v) hjv).2.1 _ (hzv v) _, fun h => absurd h hv, fun _ =>
          ⟨(locD _ _ _ _ (hD.off v hv) (cv_reg hr v) _ _ (htr v) hjv _ (hD.chi v).1 _ (hzv v)).2, fun h1 h2 => ?_⟩⟩
        obtain ⟨h3, h4⟩ := (Loc.oneD _ _ _ _ (hD.off v hv) (cv_reg hr v) _ _ (htr v) hjv h1 h2).2.2 _ (hzv v)
        refine ⟨k1 v hv _ h3, fun y hy => h4 y ?_⟩
        by_contra h
        exact hy ((Loc.fzdLaw _ _ _ (hD.off v hv) _ (hD.chi v).1).1 _ h)
  · rw [show one (D.admitted t τ) = 0 from if_neg hA, zero_mul, mul_zero]
    refine gqOn_zero _ _ _ _ fun y => ?_
    obtain ⟨v, hv⟩ := not_forall.1 hA
    obtain ⟨hv, hI⟩ := Classical.not_imp.1 hv
    refine fin_mulSupp (D.fKv t) D.Sg (fun v hv k hk => by rw [f2 v hv]; exact k1 v hv k hk) _ (v := v) ?_
    rw [f1 v hv]
    by_contra h
    haveI : CharZero (Kv v) := algebraRat.charZero _
    obtain ⟨jv, hjv⟩ := (embAlg (Kv v) _ _ ((map_ne_zero _).2 hD.ne0) (cv_reg hr v) _ (htr v)).1
    have h' : (D.S v).fK (t v) ((y.out.1 v)⁻¹ * (ι (j z)).1 v * y.out.1 v) ≠ 0 := h
    rw [ez v jv hjv] at h'
    obtain ⟨τ', h1, h2⟩ := (hD.sig v hv).K_supp _ (ht v hv) _ h'
    exact hI (tau_eq (cv_reg hr v) (htr v) hjv (hzv v) _ h2 ▸ h1)
end

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc MulAction

private theorem quot_sum_congr {Y : Type} (s s' : Setoid Y) (h : s = s') (k k' : Y → ℂ) (hk : k = k') :
    (∑ᶠ o : Quotient s, k o.out) = ∑ᶠ o : Quotient s', k' o.out := by
  subst h; subst hk; rfl

private theorem gqOn_surj {H' H G : Type} [Group H'] [Group H] [Group G] (e : H' →* H) (he : Function.Surjective e)
    (j : H →* G) (H₀ : Subgroup H) (U : Subgroup G) (k : G ⧸ U → ℂ) :
    gqOn (j.comp e) (H₀.comap e) U k = gqOn j H₀ U k := by
  letI a : MulAction H (G ⧸ U) := MulAction.compHom _ j
  letI a' : MulAction H' (G ⧸ U) := MulAction.compHom _ (j.comp e)
  have hs : ∀ (x : H') (y : G ⧸ U), x • y = e x • y := fun _ _ => rfl
  refine quot_sum_congr (orbitRel H' (G ⧸ U)) (orbitRel H (G ⧸ U)) ?_
    (fun y => k y / ((H₀.comap e).relIndex (stabilizer H' y) : ℂ)) (fun y => k y / (H₀.relIndex (stabilizer H y) : ℂ)) ?_
  · ext x y
    rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨e g, hg⟩
    · rintro ⟨g, hg⟩
      obtain ⟨g', rfl⟩ := he g
      exact ⟨g', hg⟩
  · funext y
    have : stabilizer H' y = (stabilizer H y).comap e := by
      ext x; simp only [mem_stabilizer_iff, Subgroup.mem_comap, hs]
    rw [this, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective he]

section Field

variable {K : Type} [Field K] {Δ : K}

private theorem mem_DX_k (g : GL (Fin 2) (Lsq K Δ)) : g ∈ DX Δ ↔
    ((g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 1 1 = star ((g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0) ∧
    (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 1 0 = - star ((g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 1)) := by
  have e : g ∈ DX Δ ↔ (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd _) =
      !![0, -1; 1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0] := by
    unfold DX
    exact Units.ext_iff
  rw [e]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, starRingEnd_apply] at h00 h01
    exact ⟨h00.symm, by rw [h01, neg_neg]⟩
  · rintro ⟨h1, h2⟩
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [starRingEnd_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, h1, h2]

private theorem tr_det_rat (g : DX Δ) : ∃ a b : K, (mt g).trace = algebraMap K _ a ∧ (mt g).det = algebraMap K _ b ∧ b ≠ 0 := by
  obtain ⟨h1, h2⟩ : mt g 1 1 = star (mt g 0 0) ∧ mt g 1 0 = - star (mt g 0 1) := (mem_DX_k _).1 g.2
  have hd : (mt g).det = algebraMap K _ (QuadraticAlgebra.norm (mt g 0 0) + QuadraticAlgebra.norm (mt g 0 1)) := by
    rw [Matrix.det_fin_two, h1, h2, map_add (f := _), QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    ring
  refine ⟨2 * (mt g 0 0).re, _, ?_, hd, ?_⟩
  · rw [Matrix.trace_fin_two, h1]
    ext <;> simp [two_mul]
  · intro h
    rw [h, map_zero] at hd
    exact (Matrix.isUnits_det_units (g : GL (Fin 2) (Lsq K Δ))).ne_zero hd

private theorem mt_mul (a b : DX Δ) : mt (a * b) = mt a * mt b := rfl

private theorem mt_inj {a b : DX Δ} (h : mt a = mt b) : a = b := Subtype.ext (Units.ext h)

private theorem tr_conj (x g : DX Δ) : (mt (x⁻¹ * g * x)).trace = (mt g).trace := by
  rw [mt_mul, Matrix.trace_mul_comm, ← mt_mul, ← mul_assoc, mul_inv_cancel, one_mul]

private theorem det_conj (x g : DX Δ) : (mt (x⁻¹ * g * x)).det = (mt g).det := by
  rw [mt_mul, Matrix.det_mul_comm, ← mt_mul, ← mul_assoc, mul_inv_cancel, one_mul]

private theorem mem_ZD (z : DX Δ) : z ∈ ZD Δ ↔ ∃ s : Kˣ, mt z = algebraMap K (Lsq K Δ) s • 1 := by
  unfold ZD
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  refine exists_congr fun s => ?_
  rw [← Units.val_inj, eq_comm]
  have : ((((GeneralLinearGroup.scalar (Fin 2)).comp (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ))) s : GL (Fin 2) (Lsq K Δ)) :
      Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = algebraMap K (Lsq K Δ) s • 1 := by
    ext i j : 1
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  rw [this]

private theorem alg_inj : Function.Injective (algebraMap K (Lsq K Δ)) := (algebraMap K (Lsq K Δ)).injective

private theorem one_add {τ : K} {γ : DX Δ} {j : (Etau K τ)ˣ →* DX Δ} (hj : IsEmb τ γ j) {z : (Etau K τ)ˣ}
    (hz : (z : Etau K τ) = 1 + QuadraticAlgebra.omega) : mt (j z) = 1 + mt γ := by
  rw [hj z, hz]
  simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem det_one_add (M : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) : (1 + M).det = 1 + M.trace + M.det := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply, Matrix.one_apply]
  simp
  ring

private theorem tr_det_one_add {τ : K} {γ δ : DX Δ} (hγ : HasTr γ τ) (h : mt δ = 1 + mt γ) :
    (mt δ).trace = algebraMap K _ (2 + τ) ∧ (mt δ).det = algebraMap K _ (2 + τ) := by
  rw [h, det_one_add, Matrix.trace_add, hγ.1, hγ.2, Matrix.trace_one, map_add (f := _), map_ofNat]
  refine ⟨by simp, by ring⟩

private theorem rel_inj {a b : K} (hb : b ≠ 0) {δ δ' x z : DX Δ} (hz : z ∈ ZD Δ)
    (h1 : (mt δ).trace = algebraMap K _ a) (h2 : (mt δ).det = algebraMap K _ a)
    (h1' : (mt δ').trace = algebraMap K _ b) (h2' : (mt δ').det = algebraMap K _ b)
    (h : δ' = x⁻¹ * δ * x * z) : a = b ∧ z = 1 := by
  obtain ⟨s, hs⟩ := (mem_ZD z).1 hz
  have e : mt δ' = algebraMap K (Lsq K Δ) s • mt (x⁻¹ * δ * x) := by
    rw [h, mt_mul, hs, Matrix.mul_smul, Matrix.mul_one]
  rw [e, Matrix.trace_smul, tr_conj, h1, smul_eq_mul, ← map_mul] at h1'
  rw [e, Matrix.det_smul, det_conj, h2, Fintype.card_fin, ← map_pow, ← map_mul] at h2'
  have e1 := alg_inj h1'
  have e2 := alg_inj h2'
  have hs1 : (s : K) = 1 := by
    apply mul_right_cancel₀ hb
    rw [one_mul]
    calc (s : K) * b = s * (s * a) := by rw [e1]
      _ = b := by rw [← e2]; ring
  refine ⟨by rw [← e1, hs1, one_mul], mt_inj ?_⟩
  rw [hs, hs1, map_one, one_smul]
  rfl

private theorem scal_ex (s : Kˣ) : ∃ z ∈ ZD Δ, mt z = algebraMap K (Lsq K Δ) s • 1 := by
  have hd : IsUnit (algebraMap K (Lsq K Δ) s • (1 : Matrix (Fin 2) (Fin 2) (Lsq K Δ))) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, mul_one]
    exact (s.isUnit.map _).pow _
  have hm : hd.unit ∈ DX Δ := by
    rw [mem_DX_k, IsUnit.unit_spec]
    constructor
    · ext <;> simp
    · simp
  exact ⟨⟨hd.unit, hm⟩, (mem_ZD _).2 ⟨s, rfl⟩, rfl⟩

private theorem cover {τ a b : K} {g : DX Δ} (h1 : (mt g).trace = algebraMap K _ a) (h2 : (mt g).det = algebraMap K _ b)
    (hb : b ≠ 0) (hτ : 2 + τ ≠ 0) (h : a ^ 2 = (2 + τ) * b) :
    ∃ γ : DX Δ, HasTr γ τ ∧ ∃ z ∈ ZD Δ, mt g = (1 + mt γ) * mt z := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hτ hb (by rw [← h]; ring)
  have hs : a / (2 + τ) ≠ 0 := div_ne_zero ha hτ
  obtain ⟨z, hz, hz'⟩ := scal_ex (Δ := Δ) (Units.mk0 _ hs)
  set r : K := (2 + τ) / a with hr
  have hra : r * a = 2 + τ := by rw [hr]; field_simp
  have hrb : r ^ 2 * b = 2 + τ := by
    rw [hr, div_pow, h]; field_simp
  set M : Matrix (Fin 2) (Fin 2) (Lsq K Δ) := algebraMap K (Lsq K Δ) r • mt g - 1 with hM
  have hM1 : 1 + M = algebraMap K (Lsq K Δ) r • mt g := by rw [hM]; abel
  have htr : M.trace = algebraMap K _ τ := by
    rw [hM, Matrix.trace_sub, Matrix.trace_smul, h1, smul_eq_mul, ← map_mul, hra, Matrix.trace_one, map_add (f := _), map_ofNat]
    simp
  have hdet : M.det = 1 := by
    have := det_one_add M
    rw [hM1, Matrix.det_smul, h2, Fintype.card_fin, ← map_pow, ← map_mul, hrb, htr, map_add (f := _), map_ofNat] at this
    linear_combination -this
  have hd : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact isUnit_one
  obtain ⟨k1, k2⟩ : mt g 1 1 = star (mt g 0 0) ∧ mt g 1 0 = - star (mt g 0 1) := (mem_DX_k _).1 g.2
  have hst : star (algebraMap K (Lsq K Δ) r) = algebraMap K (Lsq K Δ) r := by ext <;> simp
  have hm : hd.unit ∈ DX Δ := by
    rw [mem_DX_k, IsUnit.unit_spec, hM]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, k1, k2, star_sub, star_mul', hst]
    simp
  refine ⟨⟨hd.unit, hm⟩, ⟨hdet, htr⟩, z, hz, ?_⟩
  change mt g = (1 + M) * mt z
  rw [hM1, hz', Matrix.mul_smul, Matrix.mul_one, smul_smul, ← map_mul, Units.val_mk0]
  have : a / (2 + τ) * r = 1 := by rw [hr]; field_simp
  rw [this, map_one, one_smul]

private theorem unit_ex {τ : K} (hτ : 2 + τ ≠ 0) : ∃ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + QuadraticAlgebra.omega := by
  have : (1 + QuadraticAlgebra.omega : Etau K τ) * ⟨(1 + τ) / (2 + τ), -1 / (2 + τ)⟩ = 1 := by
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring
  exact ⟨Units.mkOfMulEqOne _ _ this, rfl⟩

private theorem two_add_ne {τ : K} (h : τ ^ 2 - 4 ≠ 0) : 2 + τ ≠ 0 := fun e => h (by linear_combination (τ - 2) * e)

private theorem reg_of_not_int {O : Type} [CommRing O] [Algebra O K] {τ : K} (h : ¬ IsIntegral O τ) : τ ^ 2 - 4 ≠ 0 := by
  intro e
  have h2 : IsIntegral O (2 : K) := by
    have := (isIntegral_one (R := O) (B := K)).add (isIntegral_one (R := O) (B := K))
    rwa [one_add_one_eq_two] at this
  have : (τ - 2) * (τ + 2) = 0 := by linear_combination e
  rcases mul_eq_zero.1 this with e | e
  · exact h (by rw [sub_eq_zero.1 e]; exact h2)
  · exact h (by rw [eq_neg_of_add_eq_zero_left e]; exact h2.neg)

private theorem lmap_alg {K' : Type} [Field K'] (f : K →+* K') (a : K) :
    lmap f Δ (algebraMap K (Lsq K Δ) a) = algebraMap K' (Lsq K' (f Δ)) (f a) := by
  ext <;> simp [lmap]

private theorem local_tau {K' : Type} [Field K'] (f : K →+* K') {g : DX Δ} {g' y : DX (f Δ)} (hg : mt g' = (mt g).map (lmap f Δ))
    {a b : K} (h1 : (mt g).trace = algebraMap K _ a) (h2 : (mt g).det = algebraMap K _ b) (hb : b ≠ 0) {τ : K'}
    (h : (mt (y⁻¹ * g' * y)).trace ^ 2 = algebraMap K' _ (2 + τ) * (mt (y⁻¹ * g' * y)).det) : f (a ^ 2 / b - 2) = τ := by
  have e1 : (mt g').trace = algebraMap K' _ (f a) := by
    rw [hg, ← lmap_alg, ← h1]
    simp [Matrix.trace_fin_two]
  have e2 : (mt g').det = algebraMap K' _ (f b) := by
    rw [hg, ← lmap_alg, ← h2]
    simp [Matrix.det_fin_two]
  rw [tr_conj, det_conj, e1, e2, ← map_pow, ← map_mul] at h
  have e := alg_inj h
  have hb' : f b ≠ 0 := (map_ne_zero f).2 hb
  rw [map_sub, map_div₀, map_pow, map_ofNat, e]
  field_simp
  ring

private theorem term_eq [CharZero K] {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (B : Base (DX Δ) G V) (hΓ : B.Γ₀ = ZD Δ)
    (hΔ : Δ ≠ 0) {τ : K} (hτ : τ ^ 2 - 4 ≠ 0) {γ : DX Δ} (hγ : HasTr γ τ) {j : (Etau K τ)ˣ →* DX Δ} (hj : IsEmb τ γ j)
    {z : (Etau K τ)ˣ} (hz : (z : Etau K τ) = 1 + QuadraticAlgebra.omega) (f : G → ℂ) :
    (Base.Tw.one B).term f (j z) = LinearMap.trace ℂ V (B.W (j z)) *
      gqOn (B.ι.comp j) (scalE τ) B.U (fun y => f (y.out⁻¹ * B.ι (j z) * y.out)) := by
  obtain ⟨-, h2, h3⟩ := (embAlg K Δ τ hΔ hτ γ hγ).2.1 j hj
  have hδ := one_add hj hz
  obtain ⟨t1, t2⟩ := tr_det_one_add hγ hδ
  have hc : ∀ x, x ∈ (Base.Tw.one B).Cent (j z) ↔ x ∈ j.range := fun x => by
    constructor
    · rintro ⟨w, hw, e⟩
      change x⁻¹ * j z * x = j z * w at e
      rw [hΓ] at hw
      have e' : j z = x⁻¹ * j z * x * w⁻¹ := by rw [e, mul_inv_cancel_right]
      have hw1 := (rel_inj (two_add_ne hτ) (inv_mem hw) t1 t2 t1 t2 e').2
      rw [hw1, mul_one, mul_assoc, eq_inv_mul_iff_mul_eq] at e'
      have e2 := congrArg mt e'
      rw [mt_mul, mt_mul, hδ, mul_add, add_mul, mul_one, one_mul, add_right_inj] at e2
      exact (h2 x).2 (mt_inj e2)
    · rintro ⟨w, rfl⟩
      refine ⟨1, one_mem _, ?_⟩
      change (j w)⁻¹ * j z * j w = j z * 1
      rw [← map_inv, ← map_mul, ← map_mul, mul_one, mul_right_comm, inv_mul_cancel, one_mul]
  let e : (Etau K τ)ˣ →* (Base.Tw.one B).Cent (j z) := j.codRestrict _ fun w => (hc _).2 ⟨w, rfl⟩
  have he : Function.Surjective e := fun x => by
    obtain ⟨w, hw⟩ := (hc x).1 x.2
    exact ⟨w, Subtype.ext hw⟩
  have key := gqOn_surj e he (B.ι.comp ((Base.Tw.one B).Cent (j z)).subtype) (B.Γ₀.subgroupOf _) B.U ((Base.Tw.one B).ker f (j z))
  have k2 : (B.Γ₀.subgroupOf ((Base.Tw.one B).Cent (j z))).comap e = scalE τ := by
    rw [← h3, hΓ]
    rfl
  rw [k2] at key
  unfold Base.Tw.term
  rw [← key]
  rfl

end Field

section Global

variable {F : Type} [Field F] [NumberField F] {Δ : F} {D : Dat Δ}

private theorem supp (hD : D.Ok) (t : Dat.Par F) (g : DA Δ) (h : D.FK t g ≠ 0) (v : Pl F) (hv : v ∈ D.Sg) :
    (D.S v).fK (t v) (g.1 v) ≠ 0 := by
  classical
  have hfin : (Function.mulSupport fun v => D.fKv t v (g.1 v)).Finite := by
    refine (D.Sg.finite_toSet.union (Filter.eventually_cofinite.1 ((rpg _ _).ae g))).subset fun w hw => ?_
    by_contra hn
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
    apply hw
    have := (fzdLaw (Ov w) (Kv w) (cv w Δ) (hD.off w hn.1) (D.χ w) (hD.chi w).1).2 1 1 (g.1 w) (by simp [IsScal]) hn.2
    have hw' : w ∉ D.Sg := hn.1
    rw [one_mul] at this
    simp only [Dat.fKv, if_neg hw', this, map_one, inv_one, Units.val_one]
  intro h0
  apply h
  unfold Dat.FK
  refine finprod_eq_zero _ v ?_ hfin
  simp only [Dat.fKv, if_pos hv, h0]

private theorem real_emb (hD : D.Ok) : Nonempty (F →+* ℝ) := by
  have := hD.real
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact ⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)⟩

private theorem cover_glob (hD : D.Ok) {ι : DX Δ →* DA Δ} (hι : IsIotaD ι) {t : Dat.Par F} (ht : D.Cone t) (g : DX Δ) (y : DA Δ)
    (h : D.FK t (y⁻¹ * ι g * y) ≠ 0) :
    ∃ τ, D.Good t τ ∧ ∃ γ : DX Δ, HasTr γ τ ∧ ∃ z ∈ ZD Δ, mt g = (1 + mt γ) * mt z := by
  obtain ⟨a, b, h1, h2, hb⟩ := tr_det_rat g
  have hadm : ∀ v ∈ D.Sg, Ind (D.S v).H (cv v (a ^ 2 / b - 2)) (t v) := fun v hv => by
    obtain ⟨τ, hτ, e⟩ := (hD.sig v hv).K_supp (t v) (ht v hv) _ (supp hD t _ h v hv)
    have e' : (y⁻¹ * ι g * y).1 v = (y.1 v)⁻¹ * (ι g).1 v * y.1 v := rfl
    rw [e'] at e
    rw [local_tau (cv v) (hι g v) h1 h2 hb e]
    exact hτ
  have hreg : (a ^ 2 / b - 2) ^ 2 - 4 ≠ 0 := by
    obtain ⟨v, hv⟩ := hD.ne
    have := reg_of_not_int ((hD.sig v hv).reg (t v) (ht v hv) _ (hadm v hv)).2
    intro e
    apply this
    have e2 := congrArg (cv v) e
    rwa [map_sub, map_pow, map_ofNat, map_zero] at e2
  obtain ⟨γ, hγ, r⟩ := cover h1 h2 hb (two_add_ne hreg) (by field_simp; ring)
  exact ⟨_, ⟨(embEx F Δ D hD _).2 γ hγ hreg, hadm⟩, γ, hγ, r⟩

end Global

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob in
theorem UpperTheory.V.Z.Sym.Glob.sideK :
    UpperTheory.V.Z.Sym.Glob.SideK := by
  classical
  intro F _ _ Δ D hD
  refine ⟨∏ v ∈ D.Sg, (D.S v).cK, Finset.prod_pos fun v hv => (hD.sig v hv).cK, ?_⟩
  intro V _ _ _ ch B hB t ht
  obtain ⟨σ⟩ := real_emb hD
  have hΔ : Δ ≠ 0 := fun e => by
    have := hD.neg σ
    rw [e, map_zero] at this
    exact lt_irrefl _ this
  have hreg : ∀ i : {τ // D.Good t τ}, i.1 ^ 2 - 4 ≠ 0 := fun i e => by
    have := i.2.1 σ
    rw [e, map_zero] at this
    exact lt_irrefl _ this
  choose γ hγ using fun i : {τ // D.Good t τ} => (embEx F Δ D hD i.1).1 i.2.1
  choose j hj using fun i : {τ // D.Good t τ} => (embAlg F Δ i.1 hΔ (hreg i) (γ i) (hγ i)).1
  choose z hz using fun i : {τ // D.Good t τ} => unit_ex (two_add_ne (hreg i))
  have hδ := fun i => one_add (hj i) (hz i)
  have htd := fun i => tr_det_one_add (hγ i) (hδ i)
  obtain ⟨hfin, htest⟩ := finK F Δ D hD V ch B hB
  have hι : IsIotaD B.ι := hB.ι
  have key := (Tf.trace _ _ V B hfin (Base.Tw.one B) (D.FK t) (htest t ht) {τ // D.Good t τ} (fun i => j i (z i)) ?_ ?_).2
  · rw [key]
    have e : ∀ i : {τ // D.Good t τ}, (Base.Tw.one B).term (D.FK t) (j i (z i)) =
        ((∏ v ∈ D.Sg, (D.S v).cK : ℝ) : ℂ) * (ch i.1 * ms i.1 * D.nK i.1) := fun i => by
      rw [term_eq B hB.Γ₀ hΔ (hreg i) (hγ i) (hj i) (hz i), hB.tr _ _ (htd i).1 (htd i).2, hB.U,
        gqK F Δ D hD B.ι hι t ht i.1 i.2.1 (γ i) (j i) (hγ i) (hj i) (z i) (hz i)]
      have : one (D.admitted t i.1) = 1 := if_pos i.2.2
      rw [this]
      push_cast
      ring
    rw [finsum_congr e, ← mul_finsum, Dat.sumK,
      finsum_subtype_eq_finsum_cond (f := fun τ => ch τ * ms τ * D.nK τ) (p := D.Good t)]
    congr 1
    refine finsum_congr fun τ => ?_
    rw [finsum_eq_if, one]
    split_ifs <;> simp
  · rintro i i' ⟨x, w, hw, e⟩
    rw [hB.Γ₀] at hw
    have := (rel_inj (two_add_ne (hreg i')) hw (htd i).1 (htd i).2 (htd i').1 (htd i').2 e).1
    exact Subtype.ext (add_left_cancel this)
  · rintro g ⟨y, hy⟩
    obtain ⟨τ, hτ, γ', hγ', w, hw, e⟩ := cover_glob hD hι ht g y.out hy
    obtain ⟨x, hx⟩ := (embAlg F Δ τ hΔ (hreg ⟨τ, hτ⟩) (γ ⟨τ, hτ⟩) (hγ ⟨τ, hτ⟩)).2.2 γ' hγ'
    refine ⟨⟨τ, hτ⟩, x, w, hB.Γ₀ ▸ hw, mt_inj ?_⟩
    change mt g = mt (x⁻¹ * j ⟨τ, hτ⟩ (z ⟨τ, hτ⟩) * x * w)
    have hx1 : mt x⁻¹ * mt x = 1 := by rw [← mt_mul, inv_mul_cancel]; rfl
    rw [e, hx, mt_mul, mt_mul, mt_mul, mt_mul, mt_mul, hδ, mul_add (mt x⁻¹), add_mul _ _ (mt x), mul_one, hx1]
end
end

open UpperTheory.V.Z.Sym.Glob

private theorem alg {g e c k : ℝ} (hc : 0 < c) (hk : 0 < k) {A B C S K : ℂ} (h1 : A = g * (S + e * K)) (h2 : B = c * S) (h3 : C = k * K) :
    A = ((g / c : ℝ) : ℂ) * B + ((g * e / k : ℝ) : ℂ) * C := by
  subst h1 h2 h3
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  field_simp

set_option maxHeartbeats 1000000 in
theorem UpperTheory.V.Z.Sym.Glob.tFId0 : TFId0 := by
  unfold TFId0
  intro F iF iN Δ D hD x₀ hx
  obtain ⟨cG, hG⟩ := @sideG F iF iN Δ D hD
  obtain ⟨e, hG⟩ := hG
  obtain ⟨cK, hK⟩ := @sideK F iF iN Δ D hD
  obtain ⟨n, hS⟩ := @split_side_identity_unitary F iF iN Δ D hD x₀ hx
  obtain ⟨x, hS⟩ := hS
  obtain ⟨cS, hS⟩ := hS
  refine ⟨n, x, cG / cS, cG * e / cK, hS.1, hS.2.1, div_pos hG.1 hS.2.2.1, ?_⟩
  intro VG VS VK a1 a2 a3 a4 a5 a6 a7 a8 a9 ch BG s BS BK hBG hBS hBK t ht
  exact alg hS.2.2.1 hK.1 (@hG.2 VG a1 a2 a3 ch BG s hBG t ht) (@hS.2.2.2 VS a4 a5 a6 ch BS hBS t ht) (@hK.2 VK a7 a8 a9 ch BK hBK t ht)
end

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem unif_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    valuation k (unif k : k) < 1 := by
  rw [GlAx.unif_spec]
  exact ValuativeRel.uniformizer_lt_one

variable {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ)

private def coneS : Subsemigroup (Dat.Par F) where
  carrier := {t | A.Cone t}
  mul_mem' {a b} ha hb v hv := by
    have h1 := ha v hv
    have h2 := hb v hv
    have h3 : valuation (Kv v) (unif (Kv v) : Kv v) ^ 2 ≤ 1 := pow_le_one₀ zero_le (le_of_lt (unif_lt_one _))
    rw [Pi.mul_apply, Units.val_mul, map_mul]
    exact (mul_le_of_le_one_right' (h2.le.trans h3)).trans_lt h1

private theorem exS_ne (a : Chs F) : (fun p : coneS A => A.exS a p.1) ≠ 0 := by
  intro h
  have hp : A.Cone fun v => unif (Kv v) ^ 3 := fun v _ => by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _))) (unif_lt_one _) (by norm_num)
  have := congrFun h ⟨_, hp⟩
  exact Finset.prod_ne_zero_iff.2 (fun v _ => ((expoEq (Kv v) (a v)).2.2 2 _).1 _) this

private theorem elS (hA : A.Ok) (t : Dat.Par F) : ∃ g : SA Δ, A.IsElD g (SD.dS t) := by
  have h := elEx F Δ A hA
  have h2 := (h.2.1 (SD.dS t)).exists
  exact h2.elim fun g hg => ⟨⟨g, h.2.2.2.2 g t hg⟩, hg⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem eigS (hA : A.Ok) (ch : F → ℂ) (x : DA Δ) (B : Base (SU Δ) (SA Δ) V) (hx : A.dat.Off x) (hB : A.dat.IsBS ch x B)
    (a : Chs F) (φ : B.Forms) (hE : A.EigS B.U φ.1 a) (t : Dat.Par F) (ht : A.Cone t) :
    (Base.Tw.one B).R (A.dat.FSx t x) φ = A.exS a t • φ := by
  obtain ⟨g, hg⟩ := elS A hA t
  apply Subtype.ext
  rw [(sOps F Δ A hA V ch x B hx hB).2.1 t g ht hg φ]
  exact hE t g ht hg

private theorem bases (D : Dat Δ) (hD : D.Ok) (ch : F → ℂ) {n : ℕ} (y : Fin (n + 1) → DA Δ) (B : Base (SU Δ) (SA Δ) V)
    (hB : D.IsBS ch (y 0) B) : ∃ B' : Fin (n + 1) → Base (SU Δ) (SA Δ) V, (∀ i, D.IsBS ch (y i) (B' i)) ∧ B' 0 = B := by
  classical
  have hW := fun i => baseS F Δ D hD V B.W ch hB.tr (y i)
  refine ⟨fun i => if i = 0 then B else (hW i).choose, fun i => ?_, by simp⟩
  by_cases h : i = 0
  · subst h
    simpa using hB
  · simp only [h, ↓reduceIte]
    exact (hW i).choose_spec.1

theorem UpperTheory.V.Z.Sym.So.specF : SpecF := by
  intro F _ _ Δ A hA VG VS VK _ _ _ _ _ _ _ _ _ ch BG s x BS BK hG hx hS hK a φ hφ h0 hE
  have hD := (datOk F Δ A hA).1
  have hC := (datOk F Δ A hA).2.1
  refine (tFId0 F Δ A.dat hD x hx).elim fun n H => H.elim fun y H => H.elim fun c₁ H => H.elim fun c₂ H => ?_
  have hy := H.2.1
  refine (bases A.dat hD ch y BS (H.1 ▸ hS)).elim fun B' hB => ?_
  have hB' := hB.1
  have e0 := hB.2
  subst e0
  haveI : FiniteDimensional ℂ BG.Forms := Tf.formsFin _ _ _ BG (finG F Δ A.dat hD VG ch BG s hG).1
  haveI : FiniteDimensional ℂ BK.Forms := Tf.formsFin _ _ _ BK (finK F Δ A.dat hD VK ch BK hK).1
  haveI : ∀ i, FiniteDimensional ℂ (B' i).Forms := fun i => Tf.formsFin _ _ _ (B' i) (finS F Δ A.dat hD VS ch (y i) (B' i) (hB' i)).1
  refine (gOpsEx F Δ A hA VG ch BG s hG).elim fun u hu => hu.elim fun Θ hu => ?_
  refine (gSpec F Δ A hA VG BG s u Θ hu).elim fun I h => h.elim fun X h => h.elim fun b h => h.elim fun β h => ?_
  have k := kSpec F Δ A hA VK ch BK hK
  have key := posSpec (coneS A) BK.Forms I (Fin (n + 1)) (fun i => (B' i).Forms)
    (fun i p => (Base.Tw.one (B' i)).R (A.dat.FSx p.1 (y i))) (fun p => (Base.Tw.one BK).R (A.dat.FK p.1))
    (fun i p q => (sOps F Δ A hA VS ch (y i) (B' i) (hy i) (hB' i)).2.2 p.1 q.1 p.2 q.2) (fun p q => k.1 p.1 q.1 p.2 q.2)
    X b (fun i p => β i p.1) (fun i hi p q => h.1 i hi p.1 q.1 p.2 q.2) c₁ c₂ H.2.2.1
    (fun p => (h.2.1 p.1 p.2).symm.trans (H.2.2.2 VG VS VK ch BG s B' BK hG hB' hK p.1 ((hC _).2 p.2))) _ (exS_ne A a)
    ⟨0, ⟨φ, hφ⟩, fun h => h0 (congrArg Subtype.val h), fun p => eigS A hA ch (y 0) (B' 0) (hy 0) (hB' 0) a ⟨φ, hφ⟩ hE p.1 p.2⟩
  refine key.elim (fun e => e.elim fun i e => ?_) fun e => e.elim fun v e => ?_
  · exact Or.inl (h.2.2 i e.1 e.2.1 a fun t ht => congrFun e.2.2 ⟨t, ht⟩)
  · exact Or.inr ⟨v.1, v.2, fun h => e.1 (Subtype.ext h), k.2 a v fun t ht => e.2 ⟨t, ht⟩⟩

end
