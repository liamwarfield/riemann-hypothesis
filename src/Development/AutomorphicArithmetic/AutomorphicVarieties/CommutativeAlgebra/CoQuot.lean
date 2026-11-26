module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoboundaryCriterion

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem prec_of_surj {R R' : Type} [CommRing R] [CommRing R'] (p : R →+* R')
    (hp : Function.Surjective p) (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete (I.map p) R' := ⟨fun f hf => by
  have hd : ∀ n, ∃ d ∈ I ^ n, p d = f (n + 1) - f n := fun n => by
    have h := (hf (Nat.le_succ n)).symm
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow] at h
    exact (Ideal.mem_map_iff_of_surjective p hp).1 h
  choose d hdI hd using hd
  obtain ⟨x, hx⟩ := hp (f 0)
  have hg : ∀ n, p (x + ∑ i ∈ Finset.range n, d i) = f n := fun n => by
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [Finset.sum_range_succ, ← add_assoc, map_add (f := _), ih, hd]; ring
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun n => x + ∑ i ∈ Finset.range n, d i) (fun {m n} hmn => by
    apply SModEq.symm
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, add_sub_add_left_eq_sub, ← Finset.sum_Ico_eq_sub _ hmn]
    exact Ideal.sum_mem _ fun i hi => Ideal.pow_le_pow_right (Finset.mem_Ico.1 hi).1 (hdI i))
  refine ⟨p L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h ⊢
  rw [← hg n, ← map_sub, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem p h⟩

theorem UpperTheory.V.Alg.co_quot :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [Nontrivial R'] (p : R →ₐ[O] R'), Function.Surjective p → IsCO O R' := by
  intro O _ _ R _ _ _ R' _ _ _ p hp
  have hp' : Function.Surjective (p : R →+* R') := hp
  haveI hL : IsLocalRing R' := IsLocalRing.of_surjective' (p : R →+* R') hp'
  haveI hN : IsNoetherianRing R' := isNoetherianRing_of_surjective R R' (p : R →+* R') hp'
  haveI hH : IsLocalHom (p : R →+* R') := IsLocalHom.of_surjective _ hp'
  have hm : (maximalIdeal R).map (p : R →+* R') = maximalIdeal R' :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hp'
  have hP : IsPrecomplete (maximalIdeal R') R' := hm ▸ prec_of_surj (p : R →+* R') hp' (maximalIdeal R)
  refine { complete := { toIsHausdorff := inferInstance, toIsPrecomplete := hP }
           isLocalHom := ⟨fun a ha => ?_⟩
           res_surj := fun y => ?_ }
  · rw [← p.commutes] at ha
    exact IsLocalHom.map_nonunit (f := algebraMap O R) a (IsLocalHom.map_nonunit (f := (p : R →+* R')) _ ha)
  · obtain ⟨x, rfl⟩ := hp y
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
    refine ⟨a, ?_⟩
    rw [← p.commutes, ← map_sub, ← hm]
    exact Ideal.mem_map_of_mem _ ha
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem mvPowerSeries_mem_span_X_of_constantCoeff_zero {σ R : Type} [Finite σ] [CommRing R] (h : MvPowerSeries σ R)
    (h0 : MvPowerSeries.constantCoeff h = 0) :
    h ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) := by
  classical
  have := Fintype.ofFinite σ
  have hex : ∀ d : σ →₀ ℕ, ∃ o : Option σ, d ≠ 0 → ∃ s, o = some s ∧ d s ≠ 0 := by
    intro d
    by_cases hd : d = 0
    · exact ⟨none, fun h => (h hd).elim⟩
    · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
        by_contra H
        push_neg at H
        exact hd (Finsupp.ext H)
      exact ⟨some s, fun _ => ⟨s, rfl, hs⟩⟩
  choose sel hsel using hex
  let g : σ → MvPowerSeries σ R := fun s e =>
    if sel (e + Finsupp.single s 1) = some s then MvPowerSeries.coeff (e + Finsupp.single s 1) h
    else 0
  have key : h = ∑ s, MvPowerSeries.X s * g s := by
    ext d
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
    by_cases hd : d = 0
    · subst hd
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
      refine (Finset.sum_eq_zero fun s _ => ?_).symm
      rw [if_neg]
      simp [Finsupp.single_le_iff]
    · obtain ⟨s0, hs0, hds0⟩ := hsel d hd
      have hle0 : Finsupp.single s0 1 ≤ d := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hds0)
      rw [Finset.sum_eq_single s0]
      · rw [if_pos hle0]
        show _ = (if sel (d - Finsupp.single s0 1 + Finsupp.single s0 1) = some s0 then
          MvPowerSeries.coeff (d - Finsupp.single s0 1 + Finsupp.single s0 1) h else 0)
        rw [tsub_add_cancel_of_le hle0, if_pos hs0]
      · intro s _ hs
        split_ifs with hle
        · show (if sel (d - Finsupp.single s 1 + Finsupp.single s 1) = some s then
            MvPowerSeries.coeff (d - Finsupp.single s 1 + Finsupp.single s 1) h else 0) = 0
          rw [tsub_add_cancel_of_le hle, hs0, if_neg]
          intro h'
          exact hs (Option.some_injective _ h').symm
        · rfl
      · simp
  rw [key]
  exact Ideal.sum_mem _ fun s _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s, rfl⟩)

private theorem mvPowerSeries_exists_polynomial_sub_mem_span_X_pow {σ R : Type} [Finite σ] [CommRing R] (n : ℕ) (g : MvPowerSeries σ R) :
    ∃ p : MvPolynomial σ R, g - (p : MvPowerSeries σ R) ∈
      (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R))) ^ n := by
  classical
  have := Fintype.ofFinite σ
  induction n generalizing g with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    have h1 : g - MvPowerSeries.C (MvPowerSeries.constantCoeff g) ∈
        Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) :=
      mvPowerSeries_mem_span_X_of_constantCoeff_zero _ (by simp)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPowerSeries σ R)).mp h1
    choose p hp using fun s => ih (c s)
    refine ⟨MvPolynomial.C (MvPowerSeries.constantCoeff g) + ∑ s, p s * MvPolynomial.X s, ?_⟩
    have hsum : ((∑ s, p s * MvPolynomial.X s : MvPolynomial σ R) : MvPowerSeries σ R) =
        ∑ s, (p s : MvPowerSeries σ R) * MvPowerSeries.X s := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
      simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply]
    have e : g - ((MvPolynomial.C (MvPowerSeries.constantCoeff g) + ∑ s, p s * MvPolynomial.X s :
        MvPolynomial σ R) : MvPowerSeries σ R) =
        ∑ s, (c s - (p s : MvPowerSeries σ R)) * MvPowerSeries.X s := by
      rw [MvPolynomial.coe_add, hsum, MvPolynomial.coe_C, ← sub_sub, ← hc]
      simp [sub_mul, smul_eq_mul, Finset.sum_sub_distrib]
    rw [e, pow_succ]
    exact Ideal.sum_mem _ fun s _ => Ideal.mul_mem_mul (hp s) (Ideal.subset_span ⟨s, rfl⟩)

theorem UpperTheory.V.Alg.co_ev :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (σ : Type) [Finite σ] (f : R →ₐ[O] R') (a : σ → R'), (∀ s, a s ∈ maximalIdeal R') →
      ∃! F : MvPowerSeries σ R →ₐ[O] R', (∀ x, F (C x) = f x) ∧ ∀ s, F (X s) = a s := by
  intro O _ _ R _ _ _ R' _ _ _ σ _ f a ha
  classical
  letI : WithIdeal R' := ⟨maximalIdeal R'⟩
  have hcs : CompleteSpace R' ∧ T2Space R' :=
    (IsAdic.isAdicComplete_iff (R := R') (I := maximalIdeal R') rfl).mp (IsCO.complete (O := O))
  haveI := hcs.1
  haveI := hcs.2
  have hE : MvPowerSeries.HasEval a :=
    ⟨fun s => WithIdeal.isTopologicallyNilpotent_of_mem (ha s), by simp [Filter.cofinite_eq_bot]⟩
  let E : MvPowerSeries σ R →+* R' :=
    (MvPowerSeries.aeval hE).toRingHom.comp (MvPowerSeries.map f.toRingHom)
  have hEC : ∀ x, E (C x) = f x := by
    intro x
    simp [E, MvPowerSeries.coe_aeval, MvPowerSeries.eval₂_C, MvPowerSeries.map_C]
  have hEX : ∀ s, E (X s) = a s := by
    intro s
    simp [E, MvPowerSeries.coe_aeval, MvPowerSeries.eval₂_X, MvPowerSeries.map_X]
  let F : MvPowerSeries σ R →ₐ[O] R' :=
    { E with
      commutes' := fun r => by
        change E (algebraMap O (MvPowerSeries σ R) r) = _
        rw [MvPowerSeries.algebraMap_apply, hEC]
        simp }
  refine ⟨F, ⟨hEC, hEX⟩, ?_⟩
  rintro G ⟨hGC, hGX⟩
  have hpoly : ∀ (H : MvPowerSeries σ R →ₐ[O] R'), (∀ x, H (C x) = f x) → (∀ s, H (X s) = a s) →
      ∀ p : MvPolynomial σ R, H (p : MvPowerSeries σ R) = MvPolynomial.eval₂ f.toRingHom a p := by
    intro H hC hX p
    induction p using MvPolynomial.induction_on with
    | C c => simp [MvPolynomial.coe_C, hC]
    | add p q hp hq => simp [MvPolynomial.coe_add, hp, hq]
    | mul_X p s hp => simp [MvPolynomial.coe_mul, MvPolynomial.coe_X, hp, hX]
  have hJ : ∀ (H : MvPowerSeries σ R →ₐ[O] R'), (∀ s, H (X s) = a s) → ∀ n,
      ∀ y ∈ (Ideal.span (Set.range (X : σ → MvPowerSeries σ R))) ^ n, H y ∈ maximalIdeal R' ^ n := by
    intro H hX n y hy
    have h1 : Ideal.map H (Ideal.span (Set.range (X : σ → MvPowerSeries σ R))) ≤ maximalIdeal R' := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
      rw [hX]
      exact ha s
    have h2 := Ideal.mem_map_of_mem H hy
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 n h2
  have hH : IsHausdorff (maximalIdeal R') R' := (IsCO.complete (O := O)).toIsHausdorff
  ext g
  rw [← sub_eq_zero]
  refine hH.haus _ fun n => ?_
  obtain ⟨p, hp⟩ := mvPowerSeries_exists_polynomial_sub_mem_span_X_pow n g
  have e1 : G g - F g = G (g - p) - F (g - p) := by
    rw [map_sub, map_sub, hpoly G hGC hGX, hpoly F (fun x => hEC x) (fun s => hEX s)]
    ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, e1]
  exact Ideal.sub_mem _ (hJ G hGX n _ hp) (hJ F (fun s => hEX s) n _ hp)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem complete_of_sq {R : Type} [CommRing R] (I : Ideal R) (h : I ^ 2 = ⊥) :
    IsAdicComplete I R := by
  have h0 : ∀ x : R, x ∈ (I ^ 2 • ⊤ : Submodule R R) → x = 0 := by
    intro x hx
    rw [Ideal.smul_eq_mul, Ideal.mul_top, h] at hx
    exact (Submodule.mem_bot R).mp hx
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hx2 := hx 2
    rw [SModEq.sub_mem, sub_zero] at hx2
    exact h0 x hx2
  · intro f hf
    refine ⟨f 2, fun n => ?_⟩
    rcases le_or_gt 2 n with hn | hn
    · have hfn := hf hn
      rw [SModEq.sub_mem] at hfn
      have e : f 2 = f n := sub_eq_zero.mp (h0 _ hfn)
      rw [SModEq.sub_mem, e, sub_self]
      exact Submodule.zero_mem _
    · exact hf hn.le

theorem UpperTheory.V.Alg.co_res :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], IsCO O (ResidueField O) ∧ IsCO O (DualNumber (ResidueField O)) := by
  intro O _ _
  constructor
  · refine IsCO.mk ?_ ?_ ?_
    · apply complete_of_sq
      rw [maximalIdeal_eq_bot, pow_two, Ideal.bot_mul]
    · show IsLocalHom (residue O)
      infer_instance
    · intro x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨a, ?_⟩
      have h : x - algebraMap O (ResidueField O) a = 0 := sub_eq_zero.mpr ha.symm
      rw [h]
      exact zero_mem _
  · have hm : ∀ x : DualNumber (ResidueField O), x ∈ maximalIdeal _ ↔ x.fst = 0 := by
      intro x
      rw [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero,
        not_not]
    have hfst : ∀ a : O, (algebraMap O (DualNumber (ResidueField O)) a).fst =
        algebraMap O (ResidueField O) a :=
      fun a => (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).commutes a
    refine IsCO.mk ?_ ?_ ?_
    · apply complete_of_sq
      rw [pow_two]
      refine le_bot_iff.mp (Ideal.mul_le.mpr fun r hr s hs => ?_)
      rw [hm] at hr hs
      refine Ideal.mem_bot.mpr (TrivSqZeroExt.ext ?_ ?_) <;> simp [hr, hs]
    · refine ⟨fun a ha => ?_⟩
      have h1 := ha.map (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O))
      rw [(TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).commutes] at h1
      exact isUnit_of_map_unit (residue O) a h1
    · intro x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.fst
      refine ⟨a, ?_⟩
      rw [hm, TrivSqZeroExt.fst_sub, hfst]
      exact sub_eq_zero.mpr ha.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.co_surj :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'), maximalIdeal R' ≤ (maximalIdeal R).map f ⊔ maximalIdeal R' ^ 2 → Function.Surjective f := by
  intro O _ _ R _ _ _ R' _ _ _ f hf
  have hle : (maximalIdeal R).map f ≤ maximalIdeal R' := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← res_eq_zero_iff O R', res_map, res_eq_zero_iff]
    exact hx
  have heq : (maximalIdeal R).map (f : R →+* R') = maximalIdeal R' := by
    refine le_antisymm hle ?_
    have hfg : (maximalIdeal R').FG := IsNoetherian.noetherian _
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg (maximalIdeal_le_jacobson _) ?_
    rw [smul_eq_mul, ← pow_two]
    exact hf
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  haveI : IsAdicComplete (maximalIdeal R') R' := IsCO.complete (O := O)
  haveI : IsHausdorff ((maximalIdeal R).map (f : R →+* R')) R' := by
    rw [heq]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (I := maximalIdeal R) (f : R →+* R')
  intro y
  obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) y0
  refine ⟨algebraMap O R a, ?_⟩
  show Ideal.Quotient.mk _ ((f : R →+* R') (algebraMap O R a)) = Ideal.Quotient.mk _ y0
  rw [Ideal.Quotient.eq, heq, AlgHom.coe_toRingHom, AlgHom.commutes, ← neg_sub]
  exact neg_mem ha
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.part_span :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (W : WPres O X R) (S : Set (W.σ →₀ ℕ)) (j : X), (∀ n ∈ S, Finsupp.weight W.wt n = j) →
      ∃ μ : Finset (W.σ →₀ ℕ), (μ : Set _) ⊆ S ∧ ∀ f : MvPowerSeries W.σ O, (∀ n, n ∉ S → coeff n f = 0) →
        ∃ b : (W.σ →₀ ℕ) → MvPowerSeries W.σ O, (∀ m, b m ∈ wtPart O W.wt 0) ∧ f = ∑ m ∈ μ, b m * monomial m 1 := by
  intro O R _ _ _ X _ _ _ W S j hS
  classical
  haveI := W.fin
  have hMfin : {m : W.σ →₀ ℕ | Minimal (· ∈ S) m}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOf_minimal_antichain _)
  have hex : ∀ n ∈ S, ∃ m ∈ {m : W.σ →₀ ℕ | Minimal (· ∈ S) m}, m ≤ n := by
    intro n hn
    obtain ⟨b, hb, hmin⟩ := (Set.isPWO_of_wellQuasiOrderedLE S).exists_le_minimal hn
    exact ⟨b, hmin, hb⟩
  choose! c hcM hcle using hex
  refine ⟨hMfin.toFinset, ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact fun m hm => hm.1
  · intro f hf
    obtain ⟨b, hb⟩ : ∃ b : (W.σ →₀ ℕ) → MvPowerSeries W.σ O, ∀ m k,
        coeff k (b m) = if k + m ∈ S ∧ c (k + m) = m then coeff (k + m) f else 0 :=
      ⟨fun m k => if k + m ∈ S ∧ c (k + m) = m then coeff (k + m) f else 0, fun _ _ => rfl⟩
    refine ⟨b, ?_, ?_⟩
    · intro m k hk
      rw [hb, if_neg]
      rintro ⟨h1, h2⟩
      apply hk
      have hm : Finsupp.weight W.wt m = j := hS m (by rw [← h2]; exact (hcM _ h1).1)
      have hkm := hS _ h1
      rw [map_add (f := _), hm] at hkm
      simpa using hkm
    · ext n
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_congr rfl
        (g := fun m => if c n = m then (if n ∈ S then coeff n f else 0) else 0), Finset.sum_ite_eq]
      · by_cases hn : n ∈ S
        · rw [if_pos ((Set.Finite.mem_toFinset hMfin).2 (hcM n hn)), if_pos hn]
        · rw [hf n hn]
          simp
      · intro m _
        rw [MvPowerSeries.coeff_mul_monomial, mul_one]
        by_cases hmn : m ≤ n
        · rw [if_pos hmn, hb, tsub_add_cancel_of_le hmn]
          by_cases h1 : n ∈ S <;> by_cases h2 : c n = m <;> simp [h1, h2]
        · rw [if_neg hmn]
          by_cases h1 : n ∈ S
          · have h3 : c n ≠ m := fun h => hmn (h ▸ hcle n h1)
            simp [h3]
          · simp [h1]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
noncomputable section

open IsLocalRing MvPowerSeries

namespace UpperTheory.V.Alg

structure IsNVal (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    (v : K → ℝ) : Prop where
  mul : ∀ x y, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y
  add : ∀ x y, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → min (v x) (v y) ≤ v (x + y)
  base : ∀ c : O, c ≠ 0 → v (algebraMap O K c) = ((IsDiscreteValuationRing.addVal O c).toNat : ℝ)

abbrev tz {K : Type} [CommRing K] (t : Kˣ) : Multiplicative ℤ →* Kˣ := zpowersHom Kˣ t

section Data

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]

structure IsWRing [IsLocalRing O] (x : A →ₐ[O] O) : Prop where
  co : IsCO O (𝒜 0)
  gen : ∃ s : Finset A, (∀ z ∈ s, z ∈ 𝒜 (-2) ∨ z ∈ 𝒜 (-1) ∨ z ∈ 𝒜 1 ∨ z ∈ 𝒜 2) ∧
    Algebra.adjoin O ((𝒜 0 : Set A) ∪ s) = ⊤
  fixed : ∀ j, j ≠ 0 → ∀ f ∈ 𝒜 j, x f = 0

variable {K : Type} [Field K] [Algebra O K]

def OnS (I : Ideal A) (ξ : A →ₐ[O] K) : Prop := ∀ f ∈ I, ξ f = 0

def NegZero (ξ : A →ₐ[O] K) : Prop := ∀ j < 0, ∀ f ∈ 𝒜 j, ξ f = 0

def PosZero (ξ : A →ₐ[O] K) : Prop := ∀ j > 0, ∀ f ∈ 𝒜 j, ξ f = 0

def TwoSigned (ξ : A →ₐ[O] K) : Prop := ¬ NegZero 𝒜 ξ ∧ ¬ PosZero 𝒜 ξ

def Same0 (ξ ξ' : A →ₐ[O] K) : Prop := ∀ b ∈ 𝒜 0, ξ b = ξ' b

def SameOrbit (ξ ξ' : A →ₐ[O] K) : Prop := ∃ t : Kˣ, ξ' = act 𝒜 (tz t) ξ

def M2 (I : Ideal A) : Prop := ((𝒜 0).map (Ideal.Quotient.mkₐ O I).toLinearMap).FG


variable (K)

def M3 (x : A →ₐ[O] O) (I : Ideal A) : Prop :=
  ∀ x₁ : A →ₐ[O] K, OnS I x₁ → NegZero 𝒜 x₁ → PosZero 𝒜 x₁ → x₁ ≠ (Algebra.ofId O K).comp x →
    (¬ ∃ ξ : A →ₐ[O] K, OnS I ξ ∧ NegZero 𝒜 ξ ∧ ¬ PosZero 𝒜 ξ ∧ Same0 𝒜 ξ x₁) ∨
    (¬ ∃ ξ : A →ₐ[O] K, OnS I ξ ∧ PosZero 𝒜 ξ ∧ ¬ NegZero 𝒜 ξ ∧ Same0 𝒜 ξ x₁)


def M4 (I : Ideal A) : Prop :=
  ∀ ξ : A →ₐ[O] K, OnS I ξ → TwoSigned 𝒜 ξ → ∀ D ∈ PtDer ξ K, ∀ D' ∈ PtDer ξ K, (∀ f ∈ I, D f = 0) →
    (∀ f ∈ I, D' f = 0) → ∃ c c' : K, (c ≠ 0 ∨ c' ≠ 0) ∧ c • D + c' • D' = 0



def M5 (x : A →ₐ[O] O) (I : Ideal A) (a : A) : Prop :=
  a ∈ 𝒜 0 ∧ x a = 0 ∧ ∀ ξ : A →ₐ[O] K, OnS I ξ → TwoSigned 𝒜 ξ → ξ a ≠ 0

variable {K}

def Covers (I : Ideal A) (T : Finset (A →ₐ[O] K)) : Prop :=
  (∀ ξ ∈ T, OnS I ξ ∧ TwoSigned 𝒜 ξ) ∧ ∀ ξ, OnS I ξ → TwoSigned 𝒜 ξ → ∃ ξ' ∈ T, SameOrbit 𝒜 ξ' ξ

end Data

structure IsChart {O A X τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup X]
    (𝒜 : X → Submodule O A) (x : A →ₐ[O] O) (wt : τ → X) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) : Prop where
  graded : ∀ j, ∀ f ∈ 𝒜 j, φ f ∈ wtPart (FractionRing O) wt j
  const : ∀ f, constantCoeff (φ f) = algebraMap O (FractionRing O) (x f)
  onto : ∀ i, ∃ f : A, coeff (Finsupp.single i 1) (φ f) ≠ 0 ∧ ∀ i', i' ≠ i → coeff (Finsupp.single i' 1) (φ f) = 0
  inj : ∀ f, x f = 0 → (∀ i, coeff (Finsupp.single i 1) (φ f) = 0) → f ∈ satSq x

def SmoothPt {O A X : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup X]
    (𝒜 : X → Submodule O A) (x : A →ₐ[O] O) (n : X → ℕ) : Prop :=
  ∃ (τ : Type) (_ : Fintype τ) (wt : τ → X) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)),
    IsChart 𝒜 x wt φ ∧ ∀ j, Nat.card {i // wt i = j} = n j

structure Eqns {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) (x : A →ₐ[O] O)
    (r s r' s' m : ℕ) where
  F : Fin (r + 1) → A
  G : Fin s → A
  E : Fin r' → A
  E' : Fin s' → A
  Z : Fin m → A
  hF : ∀ i, F i ∈ 𝒜 (-1)
  hG : ∀ i, G i ∈ 𝒜 (-2)
  hE : ∀ i, E i ∈ 𝒜 1
  hE' : ∀ i, E' i ∈ 𝒜 2
  hZ : ∀ i, Z i ∈ 𝒜 0 ∧ x (Z i) = 0

def Eqns.ideal {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {𝒜 : ℤ → Submodule O A} {x : A →ₐ[O] O}
    {r s r' s' m : ℕ} (Q : Eqns 𝒜 x r s r' s' m) : Ideal A :=
  Ideal.span (Set.range Q.F ∪ Set.range Q.G ∪ Set.range Q.E ∪ Set.range Q.E' ∪ Set.range Q.Z)

def mDims (r s r' s' m : ℕ) (j : ℤ) : ℕ :=
  if j = -1 then r else if j = -2 then s else if j = 1 then r' + 1 else if j = 2 then s' + 1 else
    if j = 0 then m else 0

def M1 {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] {𝒜 : ℤ → Submodule O A} {x : A →ₐ[O] O}
    {r s r' s' m : ℕ} (Q : Eqns 𝒜 x r s r' s' m) : Prop :=
  1 ≤ r ∧ SmoothPt 𝒜 x (mDims r s r' s' m) ∧ SpansCot x 𝒜 (-1) Q.F ∧ SpansCot x 𝒜 (-2) Q.G ∧ SpansCot x 𝒜 0 Q.Z

def LemmaM : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
  ∀ (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O), IsWRing 𝒜 x →
  ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m) (a : A),
    M1 Q → M2 𝒜 Q.ideal → M3 𝒜 K x Q.ideal → M4 𝒜 K Q.ideal → M5 𝒜 K x Q.ideal a →
    (∃ T : Finset (A →ₐ[O] K), Covers 𝒜 Q.ideal T) ∧ cotLen x 𝒜 (-1) Q.F ≠ ⊤ ∧
    ∀ T : Finset (A →ₐ[O] K), Covers 𝒜 Q.ideal T → ((cotLen x 𝒜 (-1) Q.F).toNat : ℝ) ≤ 2 * ∑ ξ ∈ T, v (ξ a)

def LemmaM' : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (A X : Type) [CommRing A] [Algebra O A] [AddCommGroup X] [DecidableEq X] (𝒜 : X → Submodule O A) [GradedAlgebra 𝒜]
    (x : A →ₐ[O] O) (j : X), (∀ f ∈ 𝒜 j, x f = 0) →
  ∀ (ι : Type) (F : ι → A), (∀ i, F i ∈ 𝒜 j) →
  ∀ (c : O), c ≠ 0 → ∀ (M : Type) [AddCommGroup M] [Module O M] (D : M →+ (A →ₗ[O] O ⧸ Ideal.span {c})),
    Function.Injective D → (∀ μ i, D μ (F i) = 0) →
    (∀ μ, ∃ D' ∈ PtDer x O, HasWt 𝒜 j D' ∧ ∀ f, D μ f = Ideal.Quotient.mk _ (D' f)) →
    Module.length O M ≤ cotLen x 𝒜 j F

end UpperTheory.V.Alg
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoFinite
noncomputable section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun {f} hf => ?_⟩
  have hc : ∀ i : Fin r, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec' (f := fun n => f n i) ?_
    intro m n hmn
    have h := hf hmn
    rw [SModEq.sub_mem] at h ⊢
    rw [mem_smul_top_pi] at h
    have := h i
    simpa [Ideal.smul_top_eq_map, smul_eq_mul, Ideal.mul_top] using this
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have := hL i n
  rw [SModEq.sub_mem] at this
  simpa [smul_eq_mul, Ideal.mul_top] using this

private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, φ, hφ⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I r
  have himg : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R M) = Submodule.map φ (I ^ n • ⊤) := by
    intro n
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hφ]
  refine ⟨fun {f} hf => ?_⟩
  have hmem : ∀ n, f (n + 1) - f n ∈ (I ^ n • ⊤ : Submodule R M) := by
    intro n
    have := SModEq.sub_mem.1 (hf (Nat.le_succ n))
    rw [← neg_sub]
    exact neg_mem this
  have hd : ∀ n, ∃ d : Fin r → R, d ∈ (I ^ n • ⊤ : Submodule R (Fin r → R)) ∧ φ d = f (n + 1) - f n := by
    intro n
    have := hmem n
    rw [himg n, Submodule.mem_map] at this
    exact this
  choose d hdmem hdφ using hd
  obtain ⟨y0, hy0⟩ := hφ (f 0)
  set g : ℕ → (Fin r → R) := fun n => y0 + ∑ k ∈ Finset.range n, d k with hg
  have hgφ : ∀ n, φ (g n) = f n := by
    intro n
    induction n with
    | zero => simp [hg, hy0]
    | succ n ih =>
      have : g (n + 1) = g n + d n := by
        simp only [hg, Finset.sum_range_succ]; abel
      rw [this, map_add (f := _), ih, hdφ]; abel
  have hgc : ∀ {m n : ℕ}, m ≤ n → g m ≡ g n [SMOD (I ^ m • ⊤ : Submodule R (Fin r → R))] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    have : g m - g n = -∑ k ∈ Finset.Ico m n, d k := by
      rw [Finset.sum_Ico_eq_sub _ hmn]; simp only [hg]; abel
    rw [this]
    refine neg_mem (Submodule.sum_mem _ fun k hk => ?_)
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Finset.mem_Ico.1 hk).1) (hdmem k)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' g hgc
  refine ⟨φ L, fun n => ?_⟩
  have h1 := (hL n).map φ
  rw [hgφ, ← himg n] at h1
  exact h1

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := by
  have hsm : ∀ (K : Ideal R) (x : R), x ∈ (K • (⊤ : Submodule R R)) ↔ x ∈ K := by
    intro K x
    simp [smul_eq_mul, Ideal.mul_top]
  have he' : I ^ (e + 1) ≤ J := le_trans (Ideal.pow_le_pow_right (Nat.le_succ e)) he
  have hpow : ∀ k, I ^ ((e + 1) * k) ≤ J ^ k := by
    intro k
    rw [pow_mul]
    exact Ideal.pow_right_mono he' k
  refine ⟨fun {f} hf => ?_⟩
  have hgc : ∀ {m n : ℕ}, m ≤ n →
      f ((e + 1) * m) ≡ f ((e + 1) * n) [SMOD (J ^ m • ⊤ : Submodule R R)] := by
    intro m n hmn
    have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
    rw [SModEq.sub_mem, hsm] at h ⊢
    exact hpow m h
  obtain ⟨L, hL⟩ := hJ.prec' (fun k => f ((e + 1) * k)) hgc
  refine ⟨L, fun n => ?_⟩
  have h1 := hf (show n ≤ (e + 1) * n by nlinarith)
  have h2 := hL n
  rw [SModEq.sub_mem, hsm] at h1 h2 ⊢
  have h3 : f ((e + 1) * n) - L ∈ I ^ n := Ideal.pow_right_mono hJI n h2
  have := Ideal.add_mem _ h1 h3
  simpa using this

theorem UpperTheory.V.Alg.co_finite :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [Algebra R R'] [IsScalarTower O R R'] [Module.Finite R R'] [IsLocalRing R'],
      (∀ x : R', ∃ a : O, x - algebraMap O R' a ∈ maximalIdeal R') → IsCO O R' := by
  intro O _ _ R _ _ _ R' _ _ _ _ _ _ hres
  haveI : IsNoetherianRing R := IsCO.toIsNoetherian (O := O)
  haveI : IsNoetherian R R' := inferInstance
  haveI hN : IsNoetherianRing R' := isNoetherian_of_tower R this
  haveI : Algebra.IsIntegral R R' := inferInstance
  haveI hcompl : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hcomap : ∀ P : Ideal R', P.IsPrime → maximalIdeal R ≤ P.comap (algebraMap R R') → P = maximalIdeal R' := by
    intro P hP hle
    have hcm : (P.comap (algebraMap R R')).IsMaximal := by
      have hne : P.comap (algebraMap R R') ≠ ⊤ := (Ideal.IsPrime.comap (algebraMap R R')).ne_top
      have : P.comap (algebraMap R R') = maximalIdeal R :=
        le_antisymm (IsLocalRing.le_maximalIdeal hne) hle
      rw [this]; infer_instance
    haveI := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R R')
      (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) P hcm
    exact IsLocalRing.eq_maximalIdeal this
  have hcm' : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal R'))
  have hloc : IsLocalHom (algebraMap R R') := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).2 hna
    rw [← hcm', Ideal.mem_comap] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 this ha
  set J : Ideal R' := (maximalIdeal R).map (algebraMap R R') with hJdef
  have hJI : J ≤ maximalIdeal R' := by
    rw [hJdef, Ideal.map_le_iff_le_comap, hcm']
  have hrad : maximalIdeal R' ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨hJP, hPp⟩ := hP
    rw [hcomap P hPp (Ideal.map_le_iff_le_comap.1 hJP)]
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  haveI : IsPrecomplete (maximalIdeal R) R' := isPrecomplete_finite (R := R) (M := R') (maximalIdeal R)
  have hJp : IsPrecomplete J R' := by
    rw [hJdef]
    exact IsPrecomplete.map_algebraMap_iff.2 this
  have hprec : IsPrecomplete (maximalIdeal R') R' := prec_cofinal hJI he hJp
  haveI : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hlocO : IsLocalHom (algebraMap O R') := by
    rw [IsScalarTower.algebraMap_eq O R R']
    infer_instance
  exact
    { complete := { toIsHausdorff := inferInstance, toIsPrecomplete := hprec }
      isLocalHom := hlocO
      res_surj := hres }
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerHom
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.der_hom :
    ∀ (O A B Q : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing B] [Algebra O B] [AddCommGroup Q] [Module O Q] [Module B Q] [Module Bᵐᵒᵖ Q] [IsCentralScalar B Q] [IsScalarTower O B Q] [Module Oᵐᵒᵖ Q] [IsCentralScalar O Q] [IsScalarTower O Bᵐᵒᵖ Q] (x : A →ₐ[O] B) (D : A → Q),
      (∃ D' ∈ PtDer x Q, ⇑D' = D) ↔ ∃ y : A →ₐ[O] TrivSqZeroExt B Q, ∀ f, (y f).fst = x f ∧ (y f).snd = D f := by
  intro O A B Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ x D
  constructor
  · rintro ⟨D', hD', rfl⟩
    have hL : ∀ f g : A, D' (f * g) = x f • D' g + x g • D' f := hD'
    have h1 : D' 1 = 0 := by
      have h := hL 1 1
      simp only [mul_one, map_one, one_smul] at h
      exact left_eq_add.mp h
    refine ⟨{ toFun := fun f => TrivSqZeroExt.inl (x f) + TrivSqZeroExt.inr (D' f)
              map_one' := ?_
              map_mul' := ?_
              map_zero' := ?_
              map_add' := ?_
              commutes' := ?_ }, fun f => ?_⟩
    · ext <;> simp [h1]
    · intro f g
      ext
      · simp
      · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add,
          TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inl,
          TrivSqZeroExt.fst_inr, add_zero, zero_add, op_smul_eq_smul, hL]
    · ext <;> simp
    · intro f g
      ext <;> simp [add_add_add_comm]
    · intro r
      rw [TrivSqZeroExt.algebraMap_eq_inl']
      have h0 : D' (algebraMap O A r) = 0 := by
        rw [Algebra.algebraMap_eq_smul_one, D'.map_smul, h1, smul_zero]
      ext <;> simp [h0]
    · simp
  · rintro ⟨y, hy⟩
    have hD : ∀ f, D f = (y f).snd := fun f => (hy f).2.symm
    have hX : ∀ f, x f = (y f).fst := fun f => (hy f).1.symm
    refine ⟨{ toFun := D
              map_add' := ?_
              map_smul' := ?_ }, ?_, rfl⟩
    · intro f g
      simp only [hD, map_add (f := _), TrivSqZeroExt.snd_add]
    · intro r f
      simp only [hD, map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply]
    · show ∀ f g : A, _ = _
      intro f g
      show D (f * g) = x f • D g + x g • D f
      rw [hD, hD, hD, hX, hX, map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul, add_comm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HomogSpan
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem wcomp_mul_homog (O : Type) [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X)
    {w : X} {e : MvPowerSeries σ O} (he : e ∈ wtPart O wt w) (G : MvPowerSeries σ O) (j : X) :
    wcomp O wt j (G * e) = wcomp O wt (j - w) G * e := by
  classical
  ext n
  rw [coeff_wcomp, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = w
    · rw [coeff_wcomp, if_pos]
      rw [← h, ← hp', map_add (f := _), h2, add_sub_cancel_right]
    · rw [he _ h2, mul_zero, mul_zero]
  · symm
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = w
    · rw [coeff_wcomp, if_neg, zero_mul]
      intro h1
      apply h
      rw [← hp', map_add (f := _), h1, h2, sub_add_cancel]
    · rw [he _ h2, mul_zero]

theorem UpperTheory.V.Alg.homog_span :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] (W : WPres O X R) (κ : Type) [Finite κ] (g : κ → W.A) (c : κ → X), (∀ i, g i ∈ W.gr (c i)) →
      IsHomog O W.wt ((Ideal.span (Set.range fun i => (g i : R))).comap W.π) ∧
      ∀ x : W.A, (x : R) ∈ Ideal.span (Set.range fun i => (g i : R)) ↔ x ∈ Ideal.span (Set.range g) := by
  intro O R _ _ _ X _ W κ _ g c hg
  classical
  cases nonempty_fintype κ
  have hback : ∀ x : W.A, x ∈ Ideal.span (Set.range g) →
      (x : R) ∈ Ideal.span (Set.range fun i => (g i : R)) := by
    intro x hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hx
    refine Ideal.mem_span_range_iff_exists_fun.2 ⟨fun i => (a i : R), ?_⟩
    rw [← ha]
    simp
  have hg' : ∀ i, ∃ e ∈ wtPart O W.wt (c i), W.π e = (g i : R) := fun i => hg i
  choose e he heg using hg'
  have key : ∀ f, W.π f ∈ Ideal.span (Set.range fun i => (g i : R)) → ∀ j,
      ∃ y ∈ Ideal.span (Set.range g), (y : R) = W.π (wcomp O W.wt j f) := by
    intro f hf j
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hf
    choose G hG using fun i => W.surj (a i)
    have h1 : f - ∑ i, G i * e i ∈ RingHom.ker W.π := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [RingHom.mem_ker, map_sub, ← ha, map_sum]
      simp [hG, heg]
    have h2 := W.homog _ h1 j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero, map_sum, map_sum] at h2
    have hm : ∀ i, W.π (wcomp O W.wt (j - c i) (G i)) ∈ W.A := fun i =>
      W.part_le_A (j := j - c i) ⟨_, wcomp_mem O W.wt _ _, rfl⟩
    refine ⟨∑ i, ⟨_, hm i⟩ * g i, Ideal.mem_span_range_iff_exists_fun.2 ⟨fun i => ⟨_, hm i⟩, rfl⟩, ?_⟩
    rw [h2, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [wcomp_mul_homog O W.wt (he i), map_mul, heg]
    rfl
  refine ⟨fun f hf j => ?_, fun x => ⟨fun hx => ?_, hback x⟩⟩
  · obtain ⟨y, hy, hy'⟩ := key f hf j
    rw [Ideal.mem_comap, ← hy']
    exact hback y hy
  · have hx' : (x : R) ∈ ⨆ j, W.part j := x.2
    have hl : ∃ f, W.π f = (x : R) ∧ ∃ s : Finset X, ∀ n, Finsupp.weight W.wt n ∉ s → coeff n f = 0 := by
      refine Submodule.iSup_induction W.part
        (motive := fun z : R => ∃ f, W.π f = z ∧
          ∃ s : Finset X, ∀ n, Finsupp.weight W.wt n ∉ s → coeff n f = 0) hx' ?_ ?_ ?_
      · rintro i _ ⟨f, hf, rfl⟩
        exact ⟨f, rfl, {i}, fun n hn => hf n (by simpa using hn)⟩
      · exact ⟨0, map_zero _, ∅, fun n _ => map_zero _⟩
      · rintro a b ⟨f, hf, s, hs⟩ ⟨f', hf', s', hs'⟩
        refine ⟨f + f', by rw [map_add (f := _), hf, hf'], s ∪ s', fun n hn => ?_⟩
        rw [Finset.mem_union, not_or] at hn
        rw [map_add (f := _), hs n hn.1, hs' n hn.2, add_zero]
    obtain ⟨f, hf, s, hs⟩ := hl
    have hsum : f = ∑ j ∈ s, wcomp O W.wt j f := by
      ext n
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [coeff_wcomp]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · exact hs n h
    choose y hy hy' using key f (hf ▸ hx)
    have : x = ∑ j ∈ s, y j := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum, ← hf]
      conv_lhs => rw [hsum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => (hy' j).symm
    rw [this]
    exact Ideal.sum_mem _ fun j _ => hy j
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoExt
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem co_ext_approx {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (m : Ideal R)
    (A : Subalgebra O R) (T : Set R) (h0 : ∀ x : R, ∃ a : O, x - algebraMap O R a ∈ m)
    (hT : ∀ t ∈ T, t ∈ A ∧ t ∈ m) (hm : m ≤ Ideal.span T ⊔ m ^ 2) (N : ℕ) (x : R) :
    ∃ a ∈ A, x - a ∈ m ^ N :=
  _root_.UpperTheory.Reformulated.B.LayerApproximation.co_ext_approx m A T h0 hT hm N x

theorem UpperTheory.V.Alg.co_ext :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (R' : Type) [CommRing R'] [Algebra O R'] (I : Ideal R') [IsHausdorff I R'] (i : B →ₐ[O] R) (S : Set R), S ⊆ maximalIdeal R → maximalIdeal R ≤ Ideal.span S ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 →
      ∀ f f' : R →ₐ[O] R', (∃ n : ℕ, ∀ x ∈ maximalIdeal R ^ n, f x ∈ I ∧ f' x ∈ I) → f.comp i = f'.comp i → (∀ s ∈ S, f s = f' s) → f = f' := by
  intro O _ _ R _ _ _ B _ _ _ R' _ _ I _ i S hS hm f f' ⟨n, hn⟩ hi hs
  have hT : ∀ t ∈ S ∪ i '' (maximalIdeal B : Set B), t ∈ AlgHom.equalizer f f' ∧ t ∈ maximalIdeal R := by
    rintro t (ht | ⟨b, hb, rfl⟩)
    · exact ⟨hs t ht, hS ht⟩
    · refine ⟨DFunLike.congr_fun hi b, ?_⟩
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hb
  have hm' : maximalIdeal R ≤ Ideal.span (S ∪ i '' (maximalIdeal B : Set B)) ⊔ maximalIdeal R ^ 2 := by
    rw [Ideal.span_union]
    exact hm
  have key : ∀ g : R →ₐ[O] R', (∀ x ∈ maximalIdeal R ^ n, g x ∈ I) →
      ∀ k : ℕ, ∀ x ∈ maximalIdeal R ^ (n * k), g x ∈ I ^ k := by
    intro g hg k x hx
    rw [pow_mul] at hx
    have hle : (maximalIdeal R ^ n) ^ k ≤ (I ^ k).comap (g : R →+* R') :=
      le_trans (Ideal.pow_right_mono (fun y hy => hg y hy) k) (Ideal.le_comap_pow _ k)
    exact hle hx
  ext x
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) inferInstance _ fun k => ?_
  obtain ⟨a, ha, h⟩ := co_ext_approx (maximalIdeal R) (AlgHom.equalizer f f') _
    (IsCO.res_surj (O := O)) hT hm' (n * k) x
  have ha' : f a = f' a := ha
  have : f x - f' x = f (x - a) - f' (x - a) := by rw [map_sub, map_sub, ha']; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, this]
  exact sub_mem (key f (fun y hy => (hn y hy).1) k _ h) (key f' (fun y hy => (hn y hy).2) k _ h)
end
