module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpRoots
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairMapOfAlgHom

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.PairRel
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsDiagonalization
theorem UpperTheory.Reformulated.B.ExistsDiagonalization.exists_diag :
    ∀ {K : Type} [inst : Field K] {n : ℕ}
    (P : Matrix (Fin n) (Fin n) K) (α : Fin n → K),
    Function.Injective α →
      P.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : K → Polynomial K) (α i)) →
        ∃ (V : Matrix (Fin n) (Fin n) K), IsUnit V ∧ P * V = V * Matrix.diagonal α := by
  intro K _ n P α hα hP
  have h1 : ∀ i, ∃ v : Fin n → K, v ≠ 0 ∧ P.mulVec v = α i • v := by
    intro i
    have h0 : P.charpoly.eval (α i) = 0 := by
      rw [hP, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    rw [Matrix.eval_charpoly] at h0
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv0
    rw [← hv0]
    ext j
    simp [Matrix.mulVec_diagonal]
  choose v hv0 hv using h1
  have hli : LinearIndependent K v := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' P) α hα v ?_
    intro i
    refine ⟨?_, hv0 i⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa using hv i
  refine ⟨(Matrix.of v).transpose, ?_, ?_⟩
  · exact Matrix.linearIndependent_cols_iff_isUnit.mp hli
  · ext j i
    have h := congrFun (hv i) j
    rw [Matrix.mul_diagonal]
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using h
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem prod_conj {K : Type} [Field K] {n : ℕ} (V : Matrix (Fin n) (Fin n) K) :
    ∀ (m : ℕ) (F : Fin m → Matrix (Fin n) (Fin n) K) (d : Fin m → Fin n → K),
      (∀ k, F k * V = V * Matrix.diagonal (d k)) →
      (List.ofFn F).prod * V = V * Matrix.diagonal (fun j => ∏ k, d k j) := by
  intro m
  induction m with
  | zero => intro F d _; simp
  | succ m ih =>
    intro F d h
    rw [List.ofFn_succ, List.prod_cons, mul_assoc, ih (fun k => F k.succ) (fun k => d k.succ) (fun k => h _),
      ← mul_assoc, h 0, mul_assoc, Matrix.diagonal_mul_diagonal]
    simp only [Fin.prod_univ_succ]

private theorem exists_diag {K : Type} [Field K] {n : ℕ} (P : Matrix (Fin n) (Fin n) K) (α : Fin n → K)
    (hα : Function.Injective α)
    (hP : P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i))) :
    ∃ V : Matrix (Fin n) (Fin n) K, IsUnit V ∧ P * V = V * Matrix.diagonal α :=
  _root_.UpperTheory.Reformulated.B.ExistsDiagonalization.exists_diag P α hα hP

theorem UpperTheory.V.Pa.Lev.pairRel :
    ∀ (K : Type) [Field K] (n : ℕ) (P T : Matrix (Fin n) (Fin n) K) (α β : Fin n → K), Function.Injective α → P * T = T * P → P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i)) → (∀ a : ℕ, (P ^ a * T).trace = ∑ i, α i ^ a * β i) → ∀ i, (List.ofFn fun i' => if i' = i then 1 else P - α i' • (1 : Matrix (Fin n) (Fin n) K)).prod * (T - β i • (1 : Matrix (Fin n) (Fin n) K)) = 0 := by
  intro K _ n P T α β hα hc hP htr i
  obtain ⟨V, hV, hPV⟩ := exists_diag P α hα hP
  obtain ⟨V', h1, h2⟩ := isUnit_iff_exists.1 hV
  obtain ⟨S, hS⟩ : ∃ S, S = V' * T * V := ⟨_, rfl⟩
  have hTV : T * V = V * S := by
    rw [hS, ← mul_assoc, ← mul_assoc, h1, one_mul]
  have hSD : Matrix.diagonal α * S = S * Matrix.diagonal α := by
    refine hV.mul_left_cancel ?_
    rw [← mul_assoc, ← hPV, mul_assoc, ← hTV, ← mul_assoc, hc, mul_assoc, hPV, ← mul_assoc, hTV,
      mul_assoc]
  have hSd : S = Matrix.diagonal (fun j => S j j) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.diagonal_apply_ne _ hab]
      have := congrFun (congrFun hSD a) b
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm] at this
      by_contra h0
      exact hab (hα (mul_left_cancel₀ h0 this))
  have hpow : ∀ a : ℕ, P ^ a * V = V * Matrix.diagonal α ^ a := by
    intro a
    induction a with
    | zero => simp
    | succ a ih => rw [pow_succ, mul_assoc, hPV, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  have htr' : ∀ a : ℕ, ∑ j, α j ^ a * S j j = ∑ j, α j ^ a * β j := by
    intro a
    rw [← htr a]
    have e : P ^ a * T = V * (Matrix.diagonal α ^ a * S) * V' := by
      rw [← mul_assoc, ← hpow, mul_assoc (P ^ a), ← hTV, mul_assoc, mul_assoc, h1, mul_one]
    rw [e, Matrix.trace_mul_cycle, h2, one_mul, Matrix.diagonal_pow]
    simp [Matrix.trace, Matrix.diagonal_mul]
  have hβ : (fun j => S j j - β j) = 0 := by
    refine Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hα (fun a => ?_)
    simp only [sub_mul, Finset.sum_sub_distrib, sub_eq_zero]
    simpa only [mul_comm] using htr' a
  have hSβ : S = Matrix.diagonal β := by
    rw [hSd]
    congr 1
    ext j
    exact sub_eq_zero.1 (congrFun hβ j)
  have hE := prod_conj V n
    (fun i' => if i' = i then 1 else P - α i' • (1 : Matrix (Fin n) (Fin n) K))
    (fun k j => if k = i then 1 else α j - α k) (by
      intro k
      by_cases hk : k = i
      · simp [hk]
      · simp only [if_neg hk]
        rw [sub_mul, hPV, smul_mul_assoc, one_mul]
        ext a b
        simp [Matrix.mul_diagonal, mul_sub, mul_comm])
  have hT : (T - β i • (1 : Matrix (Fin n) (Fin n) K)) * V = V * Matrix.diagonal (fun j => β j - β i) := by
    rw [sub_mul, hTV, hSβ, smul_mul_assoc, one_mul]
    ext a b
    simp [Matrix.mul_diagonal, mul_sub, mul_comm]
  refine hV.mul_right_cancel ?_
  rw [mul_assoc, hT, ← mul_assoc, hE, mul_assoc, Matrix.diagonal_mul_diagonal, zero_mul]
  have : (fun j => (∏ k, if k = i then 1 else α j - α k) * (β j - β i)) = fun _ => (0 : K) := by
    ext j
    by_cases hj : j = i
    · simp [hj]
    · rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), zero_mul]
  rw [this, Matrix.diagonal_zero, mul_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ArtinEl
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ellC_index (l : ℕ) [hl : Fact l.Prime] (M : Type) [CommGroup M] [Finite M] :
    ∃ n : ℕ, (ellC l M).index = l ^ n := by
  have hp : IsPGroup l (M ⧸ ellC l M) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' l hl.out.ne_one
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have h1 : orderOf (x ^ l ^ e) ∣ m := orderOf_dvd_of_pow_eq_one (by
      rw [← pow_mul, ← he, pow_orderOf_eq_one])
    exact Nat.Coprime.coprime_dvd_left h1 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hm).symm
  exact IsPGroup.iff_card.1 hp

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem isUnit_iff_val (p : 𝒪[k]) : IsUnit p ↔ valuation k (p : k) = 1 :=
  (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one

private theorem unif_of_ord {x : kˣ} (hx : ord k x = 1) : IsUnif x := by
  have hv : valuation k (x : k) = uniformizer k := by
    obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact uniformizer_ne_zero hy.symm
    have h1 : ord k (Units.mk0 y hy0) = 1 := ord_eq_one hy
    have h2 := ord_mul k (x * (Units.mk0 y hy0)⁻¹) (Units.mk0 y hy0)
    rw [inv_mul_cancel_right, hx, h1] at h2
    have h3 := ord_eq_zero_iff.1 (show ord k (x * (Units.mk0 y hy0)⁻¹) = 0 by omega)
    have h4 : (x : k) = ((x * (Units.mk0 y hy0)⁻¹ : kˣ) : k) * y := by simp [hy0]
    rw [h4, map_mul, h3, one_mul, hy]
  have hlt : valuation k (x : k) < 1 := hv ▸ uniformizer_lt_one
  refine ⟨⟨x, hlt.le⟩, ⟨fun h => hlt.ne ((isUnit_iff_val _).1 h), fun a b hab => ?_⟩, rfl⟩
  by_contra hn
  rw [not_or, isUnit_iff_val, isUnit_iff_val] at hn
  have ha : valuation k (a : k) < 1 := lt_of_le_of_ne a.2 hn.1
  have hb : valuation k (b : k) ≤ uniformizer k := le_uniformizer_iff.2 (lt_of_le_of_ne b.2 hn.2)
  have h5 : valuation k (x : k) = valuation k (a : k) * valuation k (b : k) := by
    rw [← map_mul]; exact congrArg (fun z : 𝒪[k] => valuation k (z : k)) hab
  have h6 : valuation k (a : k) * valuation k (b : k) < 1 * uniformizer k :=
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos ha hb zero_le (zero_lt_iff.2 uniformizer_ne_zero)
  rw [← h5, hv, one_mul] at h6
  exact lt_irrefl _ h6

private theorem exists_lift {H : Type} [Group H] [TopologicalSpace H] (f : H →* kˣ) (hf : Continuous f)
    (h1 : ∀ s, valuation k (f s : k) = 1) :
    ∃ g : H →* 𝒪[k]ˣ, (∀ s, Units.map (algebraMap 𝒪[k] k).toMonoidHom (g s) = f s) ∧
      IsOpen (((Units.map (residue 𝒪[k]).toMonoidHom).comp g).ker : Set H) := by
  let g0 : H →* 𝒪[k] :=
    { toFun := fun s => ⟨f s, (h1 s).le⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun s t => Subtype.ext (by simp) }
  refine ⟨g0.toHomUnits, fun s => Units.ext rfl, ?_⟩
  have e : (((Units.map (residue 𝒪[k]).toMonoidHom).comp g0.toHomUnits).ker : Set H) =
      (fun s => (f s : k) - 1) ⁻¹' {x : k | valuation k x < 1} := by
    ext s
    have e1 : (s ∈ ((Units.map (residue 𝒪[k]).toMonoidHom).comp g0.toHomUnits).ker) ↔ residue 𝒪[k] (g0 s - 1) = 0 := by
      rw [MonoidHom.mem_ker, Units.ext_iff, map_sub, map_one, sub_eq_zero]; rfl
    rw [SetLike.mem_coe, e1, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_val]
    exact ⟨fun h => lt_of_le_of_ne (g0 s - 1).2 h, fun h => ne_of_lt h⟩
  rw [e]
  refine IsOpen.preimage ((Units.continuous_val.comp hf).sub continuous_const) ?_
  simpa only [Valuation.restrict_lt_iff_lt_embedding, map_one] using
    (Valuation.isOpen_ball (v := valuation k) 1)

end Loc

theorem UpperTheory.V.Pa.Lev.artinEl :
    GlobalTheory.Published.TameLocal → ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Bq : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hB : IsPlaceOver Bq w), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (a : Weil hB →* (w.adicCompletion E)ˣ), IsLocalArtin hB a → ∀ fr τ : G E Ω, fr ∈ Dec (F := E) Bq → IsFrob (F := E) Bq (normV w) fr⁻¹ → GlobalTheory.TameQuot.IsProGen E Bq l τ → resCard (w.adicCompletion E) = normV w ∧ ∃ (h1 : fr ∈ Weil hB) (h2 : τ ∈ Weil hB), IsUnif (a ⟨fr, h1⟩) ∧ IsGenMod _ (ellC l _) (a ⟨τ, h2⟩) ∧ (∀ (σ : G E Ω) (h3 : σ ∈ Weil hB), σ ∈ GlobalTheory.TameQuot.ineKer E Bq l → a ⟨σ, h3⟩ ∈ unitsC _ (ellC l _)) ∧ (τ ^ normV w)⁻¹ * (fr⁻¹ * τ * fr) ∈ GlobalTheory.TameQuot.ineKer E Bq l := by
  intro hT l _ E Ω _ _ _ _ _ Bq w hB hl a ha fr τ hfr hF hτ
  have h0 : fr⁻¹ ∈ Weil hB := mem_Weil_of_isFrob hB hF
  have h1 : fr ∈ Weil hB := (inv_mem_iff (H := Weil hB)).1 h0
  have hval : ∀ s : Ine (F := E) Bq,
      valuation (w.adicCompletion E) ((a.comp (ineIncl hB) s : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := fun s => by
    refine ord_eq_zero_iff.1 ?_
    rw [MonoidHom.comp_apply, ha.ord_eq, deg_eq_zero_iff.2 s.2, neg_zero]
  obtain ⟨g, hg, hop⟩ := exists_lift (a.comp (ineIncl hB)) ha.cont hval
  set r := (Units.map (residue 𝒪[w.adicCompletion E]).toMonoidHom).comp g with hr
  have hrs : Function.Surjective r := fun y => by
    obtain ⟨d, rfl⟩ := surjective_units_map_of_local_ringHom (residue 𝒪[w.adicCompletion E]) residue_surjective
      inferInstance y
    obtain ⟨s, hs⟩ := ha.surj (Units.map (algebraMap 𝒪[w.adicCompletion E] (w.adicCompletion E)).toMonoidHom d)
    have hs0 : deg s = 0 := by
      have := ha.ord_eq s
      rw [hs, ord_eq_zero ((isUnit_iff_val _).1 d.isUnit)] at this
      omega
    refine ⟨⟨s, deg_eq_zero_iff.1 hs0⟩, ?_⟩
    have h5 := (hg ⟨s, deg_eq_zero_iff.1 hs0⟩).trans hs
    have h6 : g ⟨s, deg_eq_zero_iff.1 hs0⟩ = d := Units.ext (Subtype.ext (congrArg Units.val h5))
    rw [hr, MonoidHom.comp_apply, h6]
  have hopen : ∀ C : Subgroup 𝓀[w.adicCompletion E]ˣ, IsOpen ((C.comap r : Subgroup _) : Set (Ine (F := E) Bq)) :=
    fun C => Subgroup.isOpen_mono (fun s hs => by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hs]; exact C.one_mem) hop
  have hker : GlobalTheory.TameQuot.proKer l (Ine (F := E) Bq) ≤ (ellC l _).comap r := fun s hs =>
    GlobalTheory.TameQuot.mem_proKer.1 hs _ inferInstance (hopen _) (by
      rw [Subgroup.index_comap_of_surjective _ hrs]; exact ellC_index l _)
  refine ⟨resCard_eq_normV _, h1, Ine_le_Weil hB hτ.1, unif_of_ord ?_, ⟨g ⟨τ, hτ.1⟩, hg _, ?_⟩, fun σ h3 hσ => ?_, ?_⟩
  · have h2 : deg (⟨fr, h1⟩ : Weil hB)⁻¹ = 1 := deg_eq_one_iff.2 hF
    rw [ha.ord_eq, ← deg_inv, h2]
  · refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨s, rfl⟩ := hrs y
    set C := Subgroup.zpowers (r ⟨τ, hτ.1⟩) ⊔ ellC l _ with hC
    have hle : Subgroup.zpowers τ ⊔ GlobalTheory.TameQuot.ineKer E Bq l ≤ (C.comap r).map (Ine (F := E) Bq).subtype := by
      refine sup_le ((Subgroup.zpowers_le).2 ⟨⟨τ, hτ.1⟩, ?_, rfl⟩) (Subgroup.map_mono (hker.trans ?_))
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.comap_mono le_sup_right
    have h4 : (s : G E Ω) ∈ closure (Subtype.val '' ((C.comap r : Subgroup _) : Set (Ine (F := E) Bq))) :=
      closure_mono (fun z hz => hle hz) (hτ.2 s.2)
    have h5 : s ∈ closure ((C.comap r : Subgroup _) : Set (Ine (F := E) Bq)) := closure_subtype.2 h4
    rw [(Subgroup.isClosed_of_isOpen _ (hopen C)).closure_eq] at h5
    exact h5
  · obtain ⟨s, hs, rfl⟩ := hσ
    exact ⟨g s, hker hs, hg s⟩
  · have hτd : τ ∈ Dec (F := E) Bq := Weil_le_Dec hB (Ine_le_Weil hB hτ.1)
    have := ((hT.1 E Ω l Bq w hB hl).2.2.2.2.2 ⟨fr⁻¹, inv_mem hfr⟩ ⟨τ, hτd⟩ hF hτ).2.1
    simpa using this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.PsLinSmall
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem psLin_span {A κ : Type} [CommRing A] (d : ℕ) (s : Finset κ) :
    ∀ f : MvPowerSeries κ A, (∀ e : κ →₀ ℕ, (∀ i ∈ s, e i < d) → MvPowerSeries.coeff e f = 0) →
      f ∈ Ideal.span (Set.range fun i : κ => (MvPowerSeries.X i : MvPowerSeries κ A) ^ d) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro f hf
    have h0 : f = 0 := by
      ext e
      simpa using hf e (by simp)
    rw [h0]
    exact Ideal.zero_mem _
  · intro a s _ ih f hf
    let g : MvPowerSeries κ A := fun e => MvPowerSeries.coeff (e + Finsupp.single a d) f
    let r : MvPowerSeries κ A := fun e => if e a < d then MvPowerSeries.coeff e f else 0
    have hfr : f = (MvPowerSeries.X a) ^ d * g + r := by
      ext e
      rw [map_add (f := _), MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul]
      by_cases h : e a < d
      · have h' : ¬ (Finsupp.single a d ≤ e) := by
          rw [Finsupp.single_le_iff]
          omega
        rw [if_neg h']
        show _ = 0 + (if e a < d then MvPowerSeries.coeff e f else 0)
        rw [if_pos h, zero_add]
      · have h' : Finsupp.single a d ≤ e := by
          rw [Finsupp.single_le_iff]
          omega
        rw [if_pos h']
        show _ = 1 * MvPowerSeries.coeff (e - Finsupp.single a d + Finsupp.single a d) f +
          (if e a < d then MvPowerSeries.coeff e f else 0)
        rw [if_neg h, tsub_add_cancel_of_le h', one_mul, add_zero]
    rw [hfr]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, rfl⟩)) (ih r ?_)
    intro e he
    show (if e a < d then MvPowerSeries.coeff e f else 0) = 0
    split_ifs with h
    · exact hf e (fun i hi => by
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact h
        · exact he i hi)
    · rfl

private theorem psLin_small {Λ A M κ : Type} [CommRing Λ] [CommRing A] [AddCommGroup M] [Module Λ M]
    (act : MvPowerSeries κ A →+* Module.End Λ M) (I : Ideal Λ) (d : ℕ) (m : M)
    (h : ∀ i, (act (MvPowerSeries.X i) ^ d) m ∈ (I • ⊤ : Submodule Λ M)) (f : MvPowerSeries κ A)
    (hf : f ∈ Ideal.span (Set.range fun i : κ => (MvPowerSeries.X i : MvPowerSeries κ A) ^ d)) :
    act f m ∈ (I • ⊤ : Submodule Λ M) := by
  have hT : ∀ (T : Module.End Λ M) (y : M), y ∈ (I • ⊤ : Submodule Λ M) →
      T y ∈ (I • ⊤ : Submodule Λ M) :=
    fun T y hy => Submodule.smul_top_le_comap_smul_top I T hy
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [map_pow]
    exact h i
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), LinearMap.add_apply]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, map_mul, Module.End.mul_apply]
    exact hT _ _ hx

theorem UpperTheory.V.Pa.Lev.psLin :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] (A M M' κ : Type) [CommRing A] [AddCommGroup M] [Module Λ M] [AddCommGroup M'] [Module Λ M'] [Module.Finite Λ M] [Module.Finite Λ M'] [Fintype κ] (act : MvPowerSeries κ A →+* Module.End Λ M) (act' : MvPowerSeries κ A →+* Module.End Λ M') (φ : M →ₗ[Λ] M'), topNil (maximalIdeal Λ) (fun i => act (MvPowerSeries.X i)) = ⊤ → topNil (maximalIdeal Λ) (fun i => act' (MvPowerSeries.X i)) = ⊤ → (∀ a m, φ (act (MvPowerSeries.C a) m) = act' (MvPowerSeries.C a) (φ m)) → (∀ i m, φ (act (MvPowerSeries.X i) m) = act' (MvPowerSeries.X i) (φ m)) → ∀ f m, φ (act f m) = act' f (φ m) := by
  intro Λ _ _ _ _ A M M' κ _ _ _ _ _ _ _ _ act act' φ hN hN' hC hX f m
  classical
  have hpoly : ∀ P : MvPolynomial κ A, ∀ y,
      φ (act (P : MvPowerSeries κ A) y) = act' (P : MvPowerSeries κ A) (φ y) := by
    intro P
    refine MvPolynomial.induction_on
      (motive := fun P => ∀ y, φ (act (P : MvPowerSeries κ A) y) = act' (P : MvPowerSeries κ A) (φ y))
      P ?_ ?_ ?_
    · intro a y
      rw [MvPolynomial.coe_C]
      exact hC a y
    · intro p q hp hq y
      rw [MvPolynomial.coe_add, map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, map_add (f := _),
        hp, hq]
    · intro p i hp y
      rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, map_mul, Module.End.mul_apply,
        Module.End.mul_apply, hp, hX]
  rw [← sub_eq_zero]
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M') (maximalIdeal Λ)
    (IsLocalRing.maximalIdeal.isMaximal Λ).ne_top
  have hmem : φ (act f m) - act' f (φ m) ∈ ⨅ k, (maximalIdeal Λ) ^ k • (⊤ : Submodule Λ M') := by
    rw [Submodule.mem_iInf]
    intro k
    have ev1 : ∀ᶠ r in Filter.atTop, ∀ i,
        (act (MvPowerSeries.X i) ^ r) m ∈ (maximalIdeal Λ) ^ k • (⊤ : Submodule Λ M) :=
      Filter.eventually_all.mpr fun i =>
        (mem_topNil (I := maximalIdeal Λ) (T := fun i => act (MvPowerSeries.X i)) (m := m)).mp
          (by rw [hN]; exact Submodule.mem_top) i k
    have ev2 : ∀ᶠ r in Filter.atTop, ∀ i,
        (act' (MvPowerSeries.X i) ^ r) (φ m) ∈ (maximalIdeal Λ) ^ k • (⊤ : Submodule Λ M') :=
      Filter.eventually_all.mpr fun i =>
        (mem_topNil (I := maximalIdeal Λ) (T := fun i => act' (MvPowerSeries.X i)) (m := φ m)).mp
          (by rw [hN']; exact Submodule.mem_top) i k
    obtain ⟨d, hd1, hd2, hd0⟩ := (ev1.and (ev2.and (Filter.eventually_ge_atTop 1))).exists
    let n0 : κ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => d - 1
    let P := MvPowerSeries.trunc' A n0 f
    have hr : f - (P : MvPowerSeries κ A) ∈
        Ideal.span (Set.range fun i : κ => (MvPowerSeries.X i : MvPowerSeries κ A) ^ d) := by
      apply psLin_span d Finset.univ
      intro e he
      have hle : e ≤ n0 := Finsupp.le_def.mpr fun i => by
        have := he i (Finset.mem_univ i)
        show e i ≤ d - 1
        omega
      rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', if_pos hle, sub_self]
    have h1 := psLin_small act ((maximalIdeal Λ) ^ k) d m hd1 _ hr
    have h2 := psLin_small act' ((maximalIdeal Λ) ^ k) d (φ m) hd2 _ hr
    have h3 := Submodule.smul_top_le_comap_smul_top ((maximalIdeal Λ) ^ k) φ h1
    have hsplit : φ (act f m) - act' f (φ m) =
        φ (act (f - ↑P) m) - act' (f - ↑P) (φ m) := by
      simp only [map_sub, LinearMap.sub_apply, hpoly P m, sub_sub_sub_cancel_right]
    rw [hsplit]
    exact Submodule.sub_mem _ h3 h2
  rw [hbot] at hmem
  exact (Submodule.mem_bot Λ).mp hmem
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.PsModule
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem psm_mem_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem psm_prec_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun f hf => ?_⟩
  have key : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
    IsPrecomplete.prec' (I := I) (fun n => f n i) fun {m n} hmn => by
      have h := hf hmn
      rw [SModEq.sub_mem, psm_mem_pi] at h
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact h i
  choose L hL using key
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, psm_mem_pi]
  intro i
  have h := hL i n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h

private theorem psm_prec_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' R M
  haveI := psm_prec_pi I r
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨z, rfl⟩ := AdicCompletion.map_surjective I hπ y
  obtain ⟨w, rfl⟩ := AdicCompletion.of_surjective I (Fin r → R) z
  exact ⟨π w, (AdicCompletion.map_of I π w).symm⟩

private theorem psm_ev {R S σ : Type} [CommRing R] [CommRing S] [Finite σ] (m : Ideal S) [IsAdicComplete m S]
    (f : R →+* S) (a : σ → S) (ha : ∀ s, a s ∈ m.radical) :
    ∃ F : MvPowerSeries σ R →+* S, (∀ x, F (MvPowerSeries.C x) = f x) ∧ ∀ s, F (MvPowerSeries.X s) = a s := by
  letI : UniformSpace R := ⊥
  haveI : DiscreteUniformity R := ⟨rfl⟩
  letI : WithIdeal S := ⟨m⟩
  have hm : IsAdic m := rfl
  obtain ⟨h1, h2⟩ := hm.isAdicComplete_iff.1 inferInstance
  haveI : IsLinearTopology S S := Ideal.isLinearTopology m
  have hf : Continuous f := continuous_of_discreteTopology
  have hE : MvPowerSeries.HasEval a := by
    refine ⟨fun s => ?_, by simp⟩
    rw [IsTopologicallyNilpotent, hm.hasBasis_nhds_zero.tendsto_right_iff]
    intro n _
    obtain ⟨e, he⟩ := ha s
    filter_upwards [Filter.eventually_ge_atTop (e * n)] with k hk
    have h3 := Ideal.pow_mem_pow he n
    rw [← pow_mul] at h3
    exact Ideal.pow_mem_of_pow_mem _ h3 hk
  exact ⟨MvPowerSeries.eval₂Hom hf hE,
    fun x => by rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C],
    fun s => by rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]⟩

private theorem psm_rad {Λ B M : Type} [CommRing Λ] [CommRing B] [Algebra Λ B] [AddCommGroup M] [Module Λ M]
    [Module.Finite Λ M] (I : Ideal Λ) (ι : B →ₐ[Λ] Module.End Λ M) (hι : Function.Injective ι) (b : B)
    (hb : ∀ x : M, ∀ᶠ r : ℕ in Filter.atTop, (ι b ^ r) x ∈ (I • ⊤ : Submodule Λ M)) :
    b ∈ (I.map (algebraMap Λ B)).radical := by
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := Λ) (M := M)
  obtain ⟨r, hr⟩ := (Filter.eventually_all.2 fun i => hb (v i)).exists
  have h1 : LinearMap.range (ι b ^ r) ≤ I • ⊤ := by
    rw [LinearMap.range_eq_map, ← hv, Submodule.map_span, Submodule.span_le, hv]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hr i
  obtain ⟨p, hp, -, hc, h0⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero Λ (ι b ^ r) I h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_pow, Polynomial.aeval_algHom_apply, map_eq_zero_iff _ hι, hp.as_sum, map_add (f := _), map_sum,
    add_eq_zero_iff_eq_neg, map_pow, Polynomial.aeval_X, ← pow_mul] at h0
  refine ⟨_, h0 ▸ neg_mem (Ideal.sum_mem _ fun k hk => ?_)⟩
  rw [map_mul, Polynomial.aeval_C]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
  exact Ideal.pow_le_self (Nat.sub_ne_zero_of_lt (Finset.mem_range.1 hk)) (hc k)

private theorem psm_abs {Λ A B M κ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
    [IsAdicComplete (maximalIdeal Λ) Λ] [CommRing A] [CommRing B] [AddCommGroup M] [Module Λ M]
    [Module.Finite Λ M] [Finite κ] (g : Λ →+* B) (f : A →+* B) (ι : B →+* Module.End Λ M)
    (hι : Function.Injective ι) (hg : ∀ c, ι (g c) = algebraMap Λ _ c) (b : κ → B)
    (hb : topNil (maximalIdeal Λ) (fun i => ι (b i)) = ⊤) :
    ∃ F : MvPowerSeries κ A →+* B, (∀ x, F (MvPowerSeries.C x) = f x) ∧ ∀ s, F (MvPowerSeries.X s) = b s := by
  letI : Algebra Λ B := g.toAlgebra
  let ι' : B →ₐ[Λ] Module.End Λ M := { ι with commutes' := hg }
  haveI : Module.Finite Λ B := Module.Finite.of_injective ι'.toLinearMap hι
  haveI : IsPrecomplete (maximalIdeal Λ) B := psm_prec_finite _
  haveI : IsAdicComplete ((maximalIdeal Λ).map (algebraMap Λ B)) B :=
    { toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 inferInstance
      toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 inferInstance }
  refine psm_ev ((maximalIdeal Λ).map (algebraMap Λ B)) f b fun s => psm_rad _ ι' hι _ fun x => ?_
  have h := mem_topNil.1 (hb.ge (Submodule.mem_top (x := x))) s 1
  rwa [pow_one] at h

theorem UpperTheory.V.Pa.Lev.psModule :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] (A M κ : Type) [CommRing A] [Algebra Λ A] [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower Λ A M] [Module.Finite Λ M] [Fintype κ] (T : κ → Module.End A M), (∀ i j, Commute (T i) (T j)) → topNil (maximalIdeal Λ) (fun i => (T i).restrictScalars Λ) = ⊤ → ∃ act : MvPowerSeries κ A →ₐ[A] Module.End A M, ∀ i, act (MvPowerSeries.X i) = T i := by
  intro Λ _ _ _ _ A M κ _ _ _ _ _ _ _ _ T hT htop
  let B := Algebra.adjoin A (Set.range T)
  have hcomm : IsMulCommutative B := Algebra.isMulCommutative_adjoin A (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    intro _
    exact hT i j)
  letI : CommRing B := { (inferInstance : Ring B) with mul_comm := fun x y => hcomm.is_comm.comm x y }
  let ι : B →+* Module.End Λ M :=
    { toFun := fun x => (x : Module.End A M).restrictScalars Λ
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun x y h =>
    Subtype.ext (LinearMap.ext fun m => LinearMap.congr_fun h m)
  obtain ⟨F, hC, hX⟩ := psm_abs (A := A) ((algebraMap A B).comp (algebraMap Λ A)) (algebraMap A B) ι hι
    (fun c => LinearMap.ext fun m => algebraMap_smul A c m)
    (fun i => ⟨T i, Algebra.subset_adjoin ⟨i, rfl⟩⟩) htop
  refine ⟨{ (B.val : B →+* Module.End A M).comp F with commutes' := fun c => ?_ }, fun i => ?_⟩
  · show ((F (MvPowerSeries.C c) : B) : Module.End A M) = _
    rw [hC]; rfl
  · show ((F (MvPowerSeries.X i) : B) : Module.End A M) = _
    rw [hX]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.OpTransport
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ot_inv {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (e : G.Hom G') (hi : Function.Injective e.p) :
    ∃ k : G'.Hom G, ∀ g, k.p (e.p g) = g := by
  let eq : G.Γ ≃* G'.Γ := MulEquiv.ofBijective e.p ⟨hi, e.surj⟩
  have hk : ∀ x, e.p (eq.symm x) = x := fun x => eq.apply_symm_apply x
  have hcont : Continuous (eq.symm : G'.Γ → G.Γ) :=
    (Continuous.homeoOfEquivCompactToT2 (f := eq.toEquiv) e.cont).symm.continuous
  refine ⟨Glob.Hom.mk eq.symm.toMonoidHom hcont eq.symm.surjective (fun g => ?_) ?_ (fun g => ?_)
    (fun v g => ?_) (fun v g => ?_), fun g => eq.symm_apply_apply g⟩
  · show G.η (eq.symm g) = G'.η g
    rw [← e.η, hk]
  · show eq.symm G'.c = G.c
    apply hi
    rw [hk, e.c]
  · show G.ε (eq.symm g) = G'.ε g
    rw [← e.ε, hk]
  · show eq.symm _ = _
    apply hi
    rw [hk, e.φ]
  · show eq.symm _ = _
    apply hi
    rw [hk, e.φu]

private theorem ot_tr_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (y : MonoidAlgebra A H) : (D.comap φ).tr y = D.tr (MonoidAlgebra.mapDomainRingHom A φ y) := by
  have key : ∀ z : MonoidAlgebra A H, MonoidAlgebra.mapDomainRingHom (Polynomial A) φ
      (MonoidAlgebra.mapRingHom H Polynomial.C z) =
      MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom A φ z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | single m r => simp [MonoidAlgebra.mapRingHom_single]
  show (-1) ^ 1 * ((D.D (Polynomial A)) (MonoidAlgebra.mapDomainRingHom (Polynomial A) φ
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom H Polynomial.C y))).coeff (n - 1) =
    (-1) ^ 1 * ((D.D (Polynomial A)) (MonoidAlgebra.single 1 Polynomial.X -
      MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom A φ y))).coeff (n - 1)
  rw [map_sub, key]
  simp

private theorem ot_comap_comap {n : ℕ} {A G H K : Type} [CommRing A] [Group G] [Group H] [Group K] (D : GDet n A G)
    (φ : H →* G) (ψ : K →* H) : (D.comap φ).comap ψ = D.comap (φ.comp ψ) := by
  apply GDet.ext
  intro B _ _ x
  show (D.D B) (MonoidAlgebra.mapDomainRingHom B φ (MonoidAlgebra.mapDomainRingHom B ψ x)) =
    (D.D B) (MonoidAlgebra.mapDomainRingHom B (φ.comp ψ) x)
  rw [MonoidAlgebra.mapDomainRingHom_comp, RingHom.comp_apply]

private theorem ot_single {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G) (g : H) (a : A) :
    MonoidAlgebra.mapDomainRingHom A φ (MonoidAlgebra.single g a) = MonoidAlgebra.single (φ g) a := by simp

private theorem mapDomain_charpoly_element {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G) (g : H) (u : Fin n → A) :
    MonoidAlgebra.mapDomainRingHom A φ (q1El g u) = q1El (φ g) u := by
  simp only [q1El, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, ot_single, map_one]

private theorem mapDomain_partial_charpoly_element {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G) (g t : H) (u : Fin n → A)
    (i : Fin n) (y : A) : MonoidAlgebra.mapDomainRingHom A φ (q2El g t u i y) = q2El (φ g) (φ t) u i y := by
  simp only [q2El, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, ot_single, apply_ite,
    map_one]

private theorem ot_pair {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (k : G'.Hom G) {O : Type} [CommRing O]
    [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid G.frame O n} {r' : Resid G'.frame O n} (hc : Glob.Compat k r' r)
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R) :
    ∃ p' : Pair r' R, p'.D = p.D.comap k.p₀ ∧ p'.ψ = p.ψ := by
  let fh : FHom G'.frame G.frame :=
    { π := k.p, π_cont := k.cont, hη := k.η, hc := k.c, hε := k.ε, vl := id,
      gv := fun _ => MonoidHom.id _, gv_cont := fun _ => continuous_id,
      hφ := fun v g => (k.φ v g).symm, hI := fun _ _ hg => hg }
  have hπ : fh.π₀ = k.p₀ := rfl
  obtain ⟨h1, h2, h3⟩ := hc
  have hfc : fh.Compat r' r := by
    refine ⟨fun i => by rw [hπ]; exact h1 i, fun v i => ?_, fun v i g hg => ?_, fun u g hg => ?_⟩
    · rw [h2]
      rfl
    · rw [h3]
      rfl
    · right
      refine ⟨u, ?_⟩
      obtain ⟨hgI, hgk⟩ := Subgroup.mem_inf.mp hg
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hgI
        refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
        exact Subtype.ext (k.φu u x).symm
      · rw [Subgroup.mem_iInf] at hgk ⊢
        intro i
        have := hgk i
        rw [MonoidHom.mem_ker, h1 i] at this
        rw [MonoidHom.mem_ker, hπ]
        exact this
  obtain ⟨p', hD, hψ⟩ := exists_determinantPair_pullback l G'.frame G.frame fh O n r' r hfc
    (fun h0 => (p.isEmpty_of_zero h0).1) R p
  exact ⟨p', hD, funext fun v => funext fun i => by rw [hψ]; rfl⟩

theorem UpperTheory.V.Pa.Lev.opTransport :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (G G' : Glob l L) (e : G.Hom G') (h : G.Hom G0) (h' : G'.Hom G0) (q N : ℕ) (A : OpMod b h q N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (ex : ℕ), Function.Injective e.p → (∀ g, h'.p (e.p g) = h.p g) → OpRel A Nq ph ta ex → ∃ A' : OpMod b h' q N, OpRel A' Nq (fun j => e.p₀ (ph j)) (fun j => e.p₀ (ta j)) ex := by
  intro l _ L G0 O _ _ _ _ _ n r B _ _ _ u J D b G G' e h h' q N A Nq ph ta ex hi hh hR
  obtain ⟨k, hk⟩ := ot_inv e hi
  have hek : ∀ x, e.p (k.p x) = x := fun x => by
    obtain ⟨y, rfl⟩ := e.surj x
    rw [hk]
  have hcomp : h.p₀.comp k.p₀ = h'.p₀ := MonoidHom.ext fun g => Subtype.ext (by
    show h.p (k.p (g : G'.Γ)) = h'.p (g : G'.Γ)
    rw [← hh, hek])
  have hpe : ∀ x, h'.p₀ (e.p₀ x) = h.p₀ x := fun x => Subtype.ext (hh (x : G.Γ))
  have hke : ∀ x, k.p₀ (e.p₀ x) = x := fun x => Subtype.ext (hk (x : G.Γ))
  obtain ⟨rN', hc'⟩ := Core.resPull l L G' G0 h' n O r
  have hck : Glob.Compat k rN' A.rN := by
    obtain ⟨h1, h2, h3⟩ := hc'
    obtain ⟨a1, a2, a3⟩ := A.compat
    refine ⟨fun i => ?_, h2.trans a2.symm, h3.trans a3.symm⟩
    rw [h1 i, a1 i, MonoidHom.comp_assoc, hcomp]
  obtain ⟨p', hpD, hpψ⟩ := ot_pair k hck A.p
  have hmc : ∀ {S : Type} [CommRing S] (f : A.R →+* S), (A.p.D.comap k.p₀).map f = (A.p.D.map f).comap k.p₀ :=
    fun _ => rfl
  have hlam : ∀ j : Fin D, (algebraMap (abelian₂ O Empty D) A.R) (MvPowerSeries.X (Sum.inr j)) =
      (algebraMap O A.R) (b.wt.c j) * ↑((p'.ψ (b.wt.v j) (b.wt.i j)) (b.wt.γ j)) - 1 := by
    intro j
    rw [hpψ]
    exact A.segmentWeightExponent j
  have hβ : p'.Maps A.β.toRingHom (u.D.comap h'.p₀) u.ψ := by
    refine ⟨?_, fun v i => ?_⟩
    · rw [hpD, hmc, A.β_pair.1, ot_comap_comap, hcomp]
    · rw [hpψ]
      exact A.β_pair.2 v i
  refine ⟨{ A with
              rN := rN'
              compat := hc'
              p := p'
              segmentWeightExponent := hlam
              β_pair := hβ }, ?_⟩
  refine ⟨?_, fun j g => ?_, fun j i g => ?_⟩
  · dsimp only
    simp only [hpe]
    exact hR.two
  · dsimp only
    rw [hpD, hmc, ot_tr_comap, map_mul, ot_single, mapDomain_charpoly_element]
    simp only [hke]
    exact hR.rel1 j (k.p₀ g)
  · dsimp only
    rw [hpD, hmc, ot_tr_comap, map_mul, ot_single, mapDomain_partial_charpoly_element]
    simp only [hke]
    exact hR.rel2 j i (k.p₀ g)
end
