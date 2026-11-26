module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SmoothCompl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ChartChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsLiftFactorCompactSubalgebra
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerExtend

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.GradedChart
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

section SlopeTestRemainingChoices
open MvPowerSeries

private theorem gc_mem_max {E σ : Type} [Field E] (a : MvPowerSeries σ E) :
    a ∈ maximalIdeal _ ↔ constantCoeff a = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

private theorem gc_order_of_mem {E σ : Type} [Field E] (N : ℕ) :
    ∀ g ∈ maximalIdeal (MvPowerSeries σ E) ^ N, (N : ℕ∞) ≤ g.order := by
  induction N with
  | zero => intro g _; simp
  | succ n ih =>
    intro g hg
    rw [pow_succ] at hg
    refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) ?_
    · refine le_trans ?_ (le_order_mul)
      push_cast
      exact add_le_add (ih a ha) (one_le_order_iff_constCoeff_eq_zero.2 ((gc_mem_max b).1 hb))
    · intro f g hf hg
      exact le_trans (le_min hf hg) (min_order_le_add)

private theorem gc_mem_pow_iff {E σ : Type} [Field E] [Finite σ] (N : ℕ) (g : MvPowerSeries σ E) :
    g ∈ maximalIdeal (MvPowerSeries σ E) ^ N ↔ ∀ d : σ →₀ ℕ, d.degree < N → coeff d g = 0 := by
  classical
  haveI := Fintype.ofFinite σ
  constructor
  · intro hg d hd
    exact coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) (gc_order_of_mem N g hg))
  · induction N generalizing g with
    | zero =>
      intro _
      simp
    | succ N ih =>
      intro hg
      rcases isEmpty_or_nonempty σ with hσ | hσ
      · have h0 : g = 0 := by
          ext e
          have he : e = 0 := Subsingleton.elim _ _
          subst he
          simpa using hg 0 (by simp)
        rw [h0]
        exact Ideal.zero_mem _
      · obtain ⟨i0⟩ := hσ
        let pick : (σ →₀ ℕ) → σ := fun e => if h : ∃ i, e i ≠ 0 then Classical.choose h else i0
        have hpick : ∀ e : σ →₀ ℕ, e ≠ 0 → e (pick e) ≠ 0 := by
          intro e he
          have h : ∃ i, e i ≠ 0 := by
            by_contra hh
            push_neg at hh
            exact he (Finsupp.ext hh)
          simp only [pick, dif_pos h]
          exact Classical.choose_spec h
        let gi : σ → MvPowerSeries σ E := fun i e =>
          if pick (e + Finsupp.single i 1) = i then coeff (e + Finsupp.single i 1) g else 0
        have hgi : ∀ i e, coeff e (gi i) =
            if pick (e + Finsupp.single i 1) = i then coeff (e + Finsupp.single i 1) g else 0 :=
          fun i e => rfl
        have hdecomp : g = ∑ i, X i * gi i := by
          ext e
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          simp only [X, coeff_monomial_mul, one_mul]
          by_cases he : e = 0
          · subst he
            have hz : ∀ i : σ, ¬ Finsupp.single i 1 ≤ (0 : σ →₀ ℕ) := by
              intro i hle
              have := hle i
              simp at this
            simp only [hz, if_false, Finset.sum_const_zero]
            exact hg 0 (by simp)
          · have hle : Finsupp.single (pick e) 1 ≤ e := by
              intro k
              by_cases hk : k = pick e
              · subst hk
                simp only [Finsupp.single_eq_same]
                exact Nat.one_le_iff_ne_zero.mpr (hpick e he)
              · rw [Finsupp.single_apply, if_neg (Ne.symm hk)]
                exact Nat.zero_le _
            rw [Finset.sum_eq_single (pick e)]
            · rw [if_pos hle, hgi, tsub_add_cancel_of_le hle, if_pos rfl]
            · intro i _ hi
              split_ifs with hle'
              · rw [hgi, tsub_add_cancel_of_le hle', if_neg (fun h => hi h.symm)]
              · rfl
            · intro h
              exact absurd (Finset.mem_univ _) h
        rw [hdecomp]
        refine Ideal.sum_mem _ (fun i _ => ?_)
        rw [pow_succ']
        refine Ideal.mul_mem_mul ((gc_mem_max _).mpr (by simp)) (ih (gi i) ?_)
        intro d hd
        rw [hgi]
        split_ifs
        · apply hg
          rw [map_add (f := _), Finsupp.degree_single]
          omega
        · rfl

private theorem gc_coeff_single_mul {E σ : Type} [CommRing E] (i : σ) (f g : MvPowerSeries σ E) :
    coeff (Finsupp.single i 1) (f * g) =
      constantCoeff f * coeff (Finsupp.single i 1) g + constantCoeff g * coeff (Finsupp.single i 1) f := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single]
  simp [Finset.Nat.antidiagonal_succ, coeff_zero_eq_constantCoeff_apply]
  ring

private theorem gc_lin {A σ : Type} [CommRing A] [Fintype σ] (f : MvPowerSeries σ A) (d : σ →₀ ℕ)
    (hd : d.degree < 2) :
    coeff d (f - algebraMap A _ (constantCoeff f) - ∑ i, coeff (Finsupp.single i 1) f • (X i : MvPowerSeries σ A)) = 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp [MvPowerSeries.algebraMap_apply, coeff_C, coeff_X, map_sum]
  by_cases hd0 : d = 0
  · subst hd0
    have hne : ∀ x : σ, ¬ (0 : σ →₀ ℕ) = Finsupp.single x 1 :=
      fun x h => one_ne_zero (Finsupp.single_eq_zero.mp h.symm)
    simp [hne, coeff_zero_eq_constantCoeff_apply]
  · have h1 : Finsupp.degree d = 1 := by
      have : Finsupp.degree d ≠ 0 := fun h => hd0 ((Finsupp.degree_eq_zero_iff d).mp h)
      omega
    obtain ⟨j, rfl⟩ := (Finsupp.sum_eq_one_iff d).mp h1
    simp [Finsupp.single_left_inj one_ne_zero]

variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {Y : Type} [AddCommGroup Y]

private lemma gc_exists_order (W : WPres O Y R) (h : W.HasOrigin) (n : ℕ) :
    ∀ x ∈ RingHom.ker (W.origin h) ^ n, ∃ f, W.π f = x ∧ (n : ℕ∞) ≤ f.order := by
  intro x hx
  refine Submodule.pow_induction_on_left' (C := fun n x _ => ∃ f, W.π f = x ∧ (n : ℕ∞) ≤ f.order)
    _ ?_ ?_ ?_ hx
  · intro r
    obtain ⟨f, hf⟩ := W.surj (algebraMap R R r)
    exact ⟨f, hf, by simp⟩
  · rintro a b i - - ⟨f, hf, hfo⟩ ⟨g, hg, hgo⟩
    exact ⟨f + g, by rw [map_add (f := _), hf, hg], le_trans (le_min hfo hgo) min_order_le_add⟩
  · rintro m hm i a - ⟨f, hf, hfo⟩
    obtain ⟨g, rfl⟩ := W.surj m
    have hg0 : constantCoeff g = 0 := by
      rw [RingHom.mem_ker, W.origin_π] at hm
      exact hm
    refine ⟨g * f, by rw [map_mul, hf], ?_⟩
    have h1 : (1 : ℕ∞) ≤ g.order := one_le_order_iff_constCoeff_eq_zero.mpr hg0
    calc ((i.succ : ℕ) : ℕ∞) = 1 + (i : ℕ∞) := by push_cast; ring
      _ ≤ g.order + f.order := add_le_add h1 hfo
      _ ≤ (g * f).order := le_order_mul

private lemma origin_at_generator_eq_zero (W : WPres O Y R) (h : W.HasOrigin) (i : W.σ) : W.origin h (W.z i) = 0 := by
  rw [WPres.z, W.origin_π]
  simp

private lemma gc_sat (x : R →ₐ[O] O) {y p : R} (hp : y * p = 0) (N : ℕ) :
    (x y) ^ N • p ∈ RingHom.ker x ^ N := by
  set t := algebraMap O R (x y) - y with ht_def
  have htk : t ∈ RingHom.ker x := by
    rw [RingHom.mem_ker, ht_def, map_sub, AlgHom.commutes]
    simp
  have ht : t * p = algebraMap O R (x y) * p := by
    rw [ht_def, sub_mul, hp, sub_zero]
  have key : ∀ M : ℕ, t ^ M * p = algebraMap O R (x y) ^ M * p := by
    intro M
    induction M with
    | zero => simp
    | succ M ih => rw [pow_succ, mul_assoc, ht, mul_left_comm, ih, ← mul_assoc, ← pow_succ']
  rw [Algebra.smul_def, map_pow, ← key]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow htk N)

variable {E : Type} [Field E] [Algebra O E] {τ : Type}

private lemma gc_low (W : WPres O Y R) (h : W.HasOrigin) {P : Ideal R} {φ : R →ₐ[O] MvPowerSeries τ E}
    (hφ : IsCompl P (W.origin h) φ) {N : ℕ} {g : MvPowerSeries W.σ O} (hg : (N : ℕ∞) ≤ g.order) :
    φ (W.π g) ∈ maximalIdeal (MvPowerSeries τ E) ^ N := by
  haveI := W.fin
  have hX : ∀ i, (φ.comp W.π) (MvPowerSeries.X i) ∈ maximalIdeal (MvPowerSeries τ E) := by
    intro i
    rw [gc_mem_max, AlgHom.comp_apply, hφ.const]
    have := origin_at_generator_eq_zero W h i
    simp only [WPres.z] at this
    rw [this, map_zero]
  exact GlobalTheory.algHom_mem_pow_of_le_order (φ.comp W.π) hX hg

private lemma gc_unsmul [IsDomain O] [FaithfulSMul O E] [Finite τ] {c : O} (hc : c ≠ 0) {N : ℕ}
    {g : MvPowerSeries τ E} (hg : c • g ∈ maximalIdeal (MvPowerSeries τ E) ^ N) :
    g ∈ maximalIdeal (MvPowerSeries τ E) ^ N := by
  have hu : algebraMap O E c ≠ 0 := by
    intro h0
    exact hc ((FaithfulSMul.algebraMap_injective O E) (by rw [h0, map_zero]))
  have key : g = algebraMap E (MvPowerSeries τ E) (algebraMap O E c)⁻¹ * (c • g) := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O E (MvPowerSeries τ E), ← mul_assoc,
      ← map_mul, inv_mul_cancel₀ hu, map_one, one_mul]
  rw [key]
  exact Ideal.mul_mem_left _ _ hg

private lemma gc_homog [IsDomain O] [FaithfulSMul O E] [Finite τ] (W : WPres O Y R) (h : W.HasOrigin) {P : Ideal R}
    {φ : R →ₐ[O] MvPowerSeries τ E} (hφ : IsCompl P (W.origin h) φ)
    (hy : ∃ y, W.origin h y ≠ 0 ∧ ∀ a ∈ P, y * a = 0) {N : ℕ} {f : MvPowerSeries W.σ O}
    (hf : φ (W.π f) ∈ maximalIdeal (MvPowerSeries τ E) ^ N) (k : Y) :
    φ (W.π (wcomp O W.wt k f)) ∈ maximalIdeal (MvPowerSeries τ E) ^ N := by
  obtain ⟨y, hy0, hyP⟩ := hy
  obtain ⟨c, hc, hcmem⟩ := hφ.inj N (W.π f) hf
  obtain ⟨k1, hk1, p, hp, hsum⟩ := Submodule.mem_sup.mp hcmem
  have hd : (W.origin h y) ^ N * c ≠ 0 := mul_ne_zero (pow_ne_zero _ hy0) hc
  have hmem : ((W.origin h y) ^ N * c) • W.π f ∈ RingHom.ker (W.origin h) ^ N := by
    rw [mul_smul, ← hsum, smul_add]
    refine Ideal.add_mem _ ?_ (gc_sat (W.origin h) (hyP p hp) N)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ hk1
  obtain ⟨g, hg, hgo⟩ := gc_exists_order W h N _ hmem
  have hker : g - ((W.origin h y) ^ N * c) • f ∈ RingHom.ker W.π := by
    rw [RingHom.mem_ker, map_sub, hg, map_smul, sub_self]
  have hk := W.homog _ hker k
  rw [map_sub, map_smul, RingHom.mem_ker, map_sub, map_smul, sub_eq_zero] at hk
  have hgo' : (N : ℕ∞) ≤ (wcomp O W.wt k g).order := by
    refine le_order (fun e he => ?_)
    rw [coeff_wcomp]
    split_ifs
    · exact coeff_of_lt_order (lt_of_lt_of_le he hgo)
    · rfl
  have hlow := gc_low W h hφ hgo'
  rw [hk, map_smul] at hlow
  exact gc_unsmul hd hlow

private lemma gc_wcomp_ne {σ : Type} (wt : σ → Y) {j k : Y} (hjk : j ≠ k) {f : MvPowerSeries σ O}
    (hf : f ∈ wtPart O wt j) : wcomp O wt k f = 0 := by
  ext n
  rw [coeff_wcomp, map_zero]
  split_ifs with hn
  · exact hf n (by rw [hn]; exact fun h => hjk h.symm)
  · rfl

private theorem finsupp_prod_X_pow_eq_monomial_mapDomain {A σ' τ' : Type} [CommSemiring A] (u : τ' → σ') (e : τ' →₀ ℕ) :
    (e.prod fun i k => (X (u i) : MvPowerSeries σ' A) ^ k) = monomial (e.mapDomain u) 1 := by
  classical
  refine Finsupp.induction e ?_ ?_
  · simp [Finsupp.mapDomain_zero, monomial_zero_eq_C_apply]
  · intro a b g _ _ ih
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    rw [Finsupp.prod_single_index (by simp), ih, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      X_pow_eq, monomial_mul_monomial, one_mul]

private theorem weight_mapDomain_eq_weight_comp {σ' τ' Y' : Type} [AddCommGroup Y'] (wt : σ' → Y') (u : τ' → σ')
    (e : τ' →₀ ℕ) :
    Finsupp.weight wt (e.mapDomain u) = Finsupp.weight (fun i => wt (u i)) e := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (h := fun i c => c • wt i) (by simp) (by intros; simp [add_smul])]

private theorem wcomp_monomial_eq_ite_weight {A σ' Y' : Type} [CommRing A] [AddCommGroup Y'] [DecidableEq Y']
    (wt : σ' → Y') (k : Y') (m : σ' →₀ ℕ) (c : A) :
    wcomp A wt k (monomial m c) = if Finsupp.weight wt m = k then monomial m c else 0 := by
  classical
  ext n
  rw [coeff_wcomp, coeff_monomial]
  by_cases hn : n = m
  · subst hn
    rw [if_pos rfl]
    split_ifs <;> simp
  · rw [if_neg hn]
    split_ifs <;> simp [coeff_monomial, hn]

private lemma gc_graded [IsDomain O] [IsFractionRing O E] [Finite τ] (W : WPres O Y R) (h : W.HasOrigin)
    {P : Ideal R} {φ : R →ₐ[O] MvPowerSeries τ E} (hφ : IsCompl P (W.origin h) φ)
    (hy : ∃ y, W.origin h y ≠ 0 ∧ ∀ a ∈ P, y * a = 0) (u : τ → W.σ) (hu : ∀ i, φ (W.z (u i)) = X i)
    (j : Y) (a : R) (ha : a ∈ W.part j) : φ a ∈ wtPart E (fun i => W.wt (u i)) j := by
  classical
  haveI : FaithfulSMul O E :=
    (faithfulSMul_iff_algebraMap_injective O E).mpr (IsFractionRing.injective O E)
  haveI := Fintype.ofFinite τ
  have hinj := IsFractionRing.injective O E
  obtain ⟨f, hf, rfl⟩ := ha
  have hu' : ∀ i, φ (W.π (X (u i))) = X i := hu
  have hcs : ∀ (c : O) e (g : MvPowerSeries τ E), coeff e (c • g) = c • coeff e g := fun c e g => rfl
  intro e he
  change coeff e (φ (W.π f)) = 0
  have hjk : j ≠ Finsupp.weight (fun i => W.wt (u i)) e := fun h => he h.symm
  set N := Finsupp.degree e + 1 with hN
  set T : Finset (τ →₀ ℕ) := Finset.Iic (Finsupp.equivFunOnFinite.symm (fun _ : τ => N)) with hT
  have hTmem : ∀ e' : τ →₀ ℕ, Finsupp.degree e' < N → e' ∈ T := by
    intro e' he'
    rw [hT, Finset.mem_Iic]
    intro i
    have hle : e' i ≤ Finsupp.degree e' := by
      have hs : Finsupp.single i (e' i) ≤ e' := by
        intro k
        by_cases hk : k = i
        · subst hk
          simp
        · rw [Finsupp.single_apply, if_neg (Ne.symm hk)]
          exact Nat.zero_le _
      have := congrArg Finsupp.degree (tsub_add_cancel_of_le hs)
      rw [map_add (f := _), Finsupp.degree_single] at this
      omega
    simp
    omega
  obtain ⟨b', hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) T
    (fun e' => coeff e' (φ (W.π f)))
  set d : O := (b' : O) with hd_def
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero b'.2
  have hb : ∀ e' ∈ T, ∃ b : O, algebraMap O E b = d • coeff e' (φ (W.π f)) :=
    fun e' he' => hd e' he'
  choose! a ha using hb
  set Pm : (τ →₀ ℕ) → MvPowerSeries W.σ O := fun e' => e'.prod fun i k => X (u i) ^ k with hPm
  have hψ : ∀ e', φ (W.π (Pm e')) = monomial e' 1 := by
    intro e'
    simp only [hPm, Finsupp.prod, map_prod, map_pow, hu']
    have := finsupp_prod_X_pow_eq_monomial_mapDomain (A := E) (id : τ → τ) e'
    rw [Finsupp.mapDomain_id] at this
    simpa [Finsupp.prod] using this
  have hF : φ (W.π (d • f - ∑ e' ∈ T, a e' • Pm e')) ∈ maximalIdeal (MvPowerSeries τ E) ^ N := by
    rw [gc_mem_pow_iff]
    intro e'' he''
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sub, map_sum, map_sum, map_smul, map_smul, map_sub, map_sum, hcs]
    simp only [map_smul, hψ, hcs, coeff_monomial, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq T e'' (fun e' => a e' • (1 : E)), if_pos (hTmem e'' he''),
      ← Algebra.algebraMap_eq_smul_one, ha e'' (hTmem e'' he''), sub_self]
  have hwP : ∀ e', wcomp O W.wt (Finsupp.weight (fun i => W.wt (u i)) e) (Pm e') =
      if Finsupp.weight (fun i => W.wt (u i)) e' = Finsupp.weight (fun i => W.wt (u i)) e
      then Pm e' else 0 := by
    intro e'
    simp only [hPm]
    rw [finsupp_prod_X_pow_eq_monomial_mapDomain, wcomp_monomial_eq_ite_weight, weight_mapDomain_eq_weight_comp]
  have hwF : wcomp O W.wt (Finsupp.weight (fun i => W.wt (u i)) e) (d • f - ∑ e' ∈ T, a e' • Pm e') =
      -∑ e' ∈ T.filter (fun e' => Finsupp.weight (fun i => W.wt (u i)) e' =
        Finsupp.weight (fun i => W.wt (u i)) e), a e' • Pm e' := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_filter, map_sub, map_smul, map_sum, gc_wcomp_ne W.wt hjk hf, smul_zero, zero_sub]
    congr 1
    refine Finset.sum_congr rfl (fun e' _ => ?_)
    rw [map_smul, hwP, smul_ite, smul_zero]
  have hW := gc_homog W h hφ hy hF (Finsupp.weight (fun i => W.wt (u i)) e)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hwF, map_neg, map_neg, Ideal.neg_mem_iff, map_sum, map_sum] at hW
  have hc := (gc_mem_pow_iff N _).mp hW e (by omega)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, hψ, map_sum, hcs, coeff_monomial, smul_ite, smul_zero] at hc
  rw [Finset.sum_ite_eq _ e (fun e' => a e' • (1 : E))] at hc
  have heT : e ∈ T.filter (fun e' => Finsupp.weight (fun i => W.wt (u i)) e' =
      Finsupp.weight (fun i => W.wt (u i)) e) :=
    Finset.mem_filter.mpr ⟨hTmem e (by omega), rfl⟩
  rw [if_pos heT, ← Algebra.algebraMap_eq_smul_one, ha e (hTmem e (by omega)), Algebra.smul_def] at hc
  exact (mul_eq_zero.mp hc).resolve_left (fun h0 => hd0 (hinj (by rw [h0, map_zero])))

private lemma gc_deg_single {σ : Type} (i : σ) : (Finsupp.single i 1 : σ →₀ ℕ).degree < 2 := by simp

private lemma gc_span [IsDomain O] [FaithfulSMul O E] {n : ℕ} (W : WPres O Y R) (h : W.HasOrigin)
    {P : Ideal R} {φ : R →ₐ[O] MvPowerSeries (Fin n) E} (hφ : IsCompl P (W.origin h) φ) :
    ∃ u : Fin n → W.σ, Submodule.span E
      (Set.range fun i j : Fin n => coeff (Finsupp.single j 1) (φ (W.z (u i)))) = ⊤ := by
  classical
  haveI := W.fin
  let lin : MvPowerSeries (Fin n) E →ₗ[E] (Fin n → E) :=
    LinearMap.pi (fun j => coeff (Finsupp.single j 1))
  have hlin : ∀ f j, lin f j = coeff (Finsupp.single j 1) f := fun f j => rfl
  have hlin2 : ∀ f ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2, lin f = 0 := by
    intro f hf
    funext j
    rw [hlin]
    exact (gc_mem_pow_iff 2 f).mp hf _ (gc_deg_single j)
  have hlinO : ∀ (c : O) f, lin (c • f) = algebraMap O E c • lin f := by
    intro c f
    funext j
    rw [Pi.smul_apply, hlin, hlin, smul_eq_mul, ← Algebra.smul_def]
    rfl
  set v : W.σ → (Fin n → E) := fun k j => coeff (Finsupp.single j 1) (φ (W.z k)) with hv_def
  have hv : ∀ k, lin (φ (W.z k)) ∈ Submodule.span E (Set.range v) :=
    fun k => Submodule.subset_span ⟨k, rfl⟩
  have hC : ∀ r : O, lin (algebraMap O (MvPowerSeries (Fin n) E) r) = 0 := by
    intro r
    funext j
    rw [hlin, MvPowerSeries.algebraMap_apply, coeff_C,
      if_neg (fun h => one_ne_zero (Finsupp.single_eq_zero.mp h))]
    rfl
  have key : ∀ g, lin (φ (W.π g)) ∈ Submodule.span E (Set.range v) := by
    intro g
    have hg_eq : g = (g - algebraMap O _ (constantCoeff g) -
        ∑ k, coeff (Finsupp.single k 1) g • (X k : MvPowerSeries W.σ O)) +
        algebraMap O _ (constantCoeff g) + ∑ k, coeff (Finsupp.single k 1) g • X k := by
      abel
    rw [hg_eq, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _)]
    refine add_mem (add_mem ?_ ?_) ?_
    · rw [hlin2 _ (gc_low W h hφ (nat_le_order (fun d hd => gc_lin g d hd)))]
      exact zero_mem _
    · rw [AlgHom.commutes, AlgHom.commutes, hC]
      exact zero_mem _
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, map_sum]
      refine Submodule.sum_mem _ (fun k _ => ?_)
      rw [map_smul, map_smul, hlinO]
      exact Submodule.smul_mem _ _ (hv k)
  have hS : Submodule.span E (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have he : ∀ j : Fin n, (fun k => if j = k then (1 : E) else 0) ∈ Submodule.span E (Set.range v) := by
      intro j
      obtain ⟨a, c, hc, hca⟩ := hφ.dense 2 (X j)
      obtain ⟨g, rfl⟩ := W.surj a
      have h1 := hlin2 _ hca
      rw [map_sub, hlinO, sub_eq_zero] at h1
      have hX : lin (X j) = fun k => if j = k then (1 : E) else 0 := by
        funext k
        rw [hlin, coeff_X]
        by_cases hjk : j = k
        · subst hjk
          simp
        · rw [if_neg, if_neg hjk]
          intro h
          exact hjk ((Finsupp.single_left_inj one_ne_zero).mp h).symm
      rw [hX] at h1
      have hc' : algebraMap O E c ≠ 0 := fun h0 =>
        hc ((FaithfulSMul.algebraMap_injective O E) (by rw [h0, map_zero]))
      have := Submodule.smul_mem _ (algebraMap O E c)⁻¹ (h1 ▸ key g)
      rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
    rw [pi_eq_sum_univ w]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (he j))
  obtain ⟨f, hfs, hfspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq E (Set.range v)
  have hk : finrank E (Submodule.span E (Set.range v)) = n := by
    rw [hS, finrank_top, Module.finrank_fin_fun]
  have hu : ∀ i : Fin n, ∃ k, v k = f (Fin.cast hk.symm i) := fun i => hfs _
  choose u hu using hu
  refine ⟨u, ?_⟩
  have hr : Set.range (fun i => v (u i)) = Set.range f := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, (hu i).symm⟩
    · rintro ⟨i, rfl⟩
      refine ⟨Fin.cast hk i, ?_⟩
      show v (u (Fin.cast hk i)) = f i
      rw [hu]
      simp
  show Submodule.span E (Set.range fun i => v (u i)) = ⊤
  rw [hr, hfspan, hS]

private lemma gc_der [IsDomain O] [IsFractionRing O E] [Fintype τ] (x : R →ₐ[O] O)
    {P : Ideal R} {φ : R →ₐ[O] MvPowerSeries τ E} (hφ : IsCompl P x φ)
    (hy : ∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a = 0) (z : τ → R) (hz : ∀ i, φ (z i) = X i)
    {D : R →ₗ[O] E} (hD : D ∈ PtDer ((Algebra.ofId O E).comp x) E) (h0 : ∀ i, D (z i) = 0) : D = 0 := by
  classical
  have hinj := IsFractionRing.injective O E
  have hDm : ∀ f g, D (f * g) = algebraMap O E (x f) * D g + algebraMap O E (x g) * D f :=
    fun f g => hD f g
  have hD1 : D 1 = 0 := by
    have := hDm 1 1
    simp only [map_one, one_mul] at this
    linear_combination -this
  have hDc : ∀ r : O, D (algebraMap O R r) = 0 := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hD1, smul_zero]
  have hDk2 : ∀ a ∈ RingHom.ker x ^ 2, D a = 0 := by
    intro a ha
    rw [pow_two] at ha
    refine Submodule.mul_induction_on (C := fun a => D a = 0) ha ?_ ?_
    · intro u hu v hv
      rw [RingHom.mem_ker] at hu hv
      rw [hDm, hu, hv, map_zero, zero_mul, zero_mul, add_zero]
    · intro u v hu hv
      rw [map_add (f := _), hu, hv, add_zero]
  obtain ⟨y, hy0, hyP⟩ := hy
  have hDP : ∀ p ∈ P, D p = 0 := by
    intro p hp
    have hxp : x p = 0 := by
      apply hinj
      rw [← hφ.const, map_zero]
      rw [← hφ.ker] at hp
      rw [RingHom.mem_ker.mp hp, map_zero]
    have := hDm y p
    rw [hyP p hp, map_zero, hxp, map_zero, zero_mul, add_zero] at this
    have hne : algebraMap O E (x y) ≠ 0 := fun h => hy0 (hinj (by rw [h, map_zero]))
    exact (mul_eq_zero.mp this.symm).resolve_left hne
  have hDs : ∀ a ∈ RingHom.ker x ^ 2 ⊔ P, D a = 0 := by
    intro a ha
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp ha
    rw [map_add (f := _), hDk2 u hu, hDP v hv, add_zero]
  refine LinearMap.ext (fun a => ?_)
  rw [LinearMap.zero_apply]
  obtain ⟨b', hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset τ) (fun i => coeff (Finsupp.single i 1) (φ a))
  have hb : ∀ i, ∃ b : O, algebraMap O E b = (b' : O) • coeff (Finsupp.single i 1) (φ a) :=
    fun i => hd i (Finset.mem_univ _)
  choose b hb using hb
  set d : O := (b' : O) with hd_def
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero b'.2
  have hcs : ∀ e (f : MvPowerSeries τ E), coeff e (d • f) = d • coeff e f := fun e f => rfl
  set F' : MvPowerSeries τ E := d • φ a with hF'
  have key : φ (d • a - algebraMap O R (d * x a) - ∑ i, b i • z i) =
      F' - algebraMap E _ (constantCoeff F') - ∑ i, coeff (Finsupp.single i 1) F' • X i := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sub, map_sum, map_smul, AlgHom.commutes]
    congr 1
    · congr 1
      rw [IsScalarTower.algebraMap_apply O E (MvPowerSeries τ E)]
      congr 1
      rw [hF', ← coeff_zero_eq_constantCoeff_apply, hcs, coeff_zero_eq_constantCoeff_apply, hφ.const,
        Algebra.smul_def, map_mul]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul, hz, hF', hcs, ← hb i, algebraMap_smul]
  have hmem : φ (d • a - algebraMap O R (d * x a) - ∑ i, b i • z i) ∈
      maximalIdeal (MvPowerSeries τ E) ^ 2 :=
    (gc_mem_pow_iff 2 _).mpr (fun e he => by rw [key]; exact gc_lin F' e he)
  obtain ⟨c, hc, hcm⟩ := hφ.inj 2 _ hmem
  have h1 := hDs _ hcm
  rw [map_smul, Algebra.smul_def] at h1
  have h2 := (mul_eq_zero.mp h1).resolve_left (fun h => hc (hinj (by rw [h, map_zero])))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sub, map_sum, hDc, map_smul] at h2
  simp only [map_smul, h0, smul_zero, Finset.sum_const_zero, sub_zero] at h2
  rw [Algebra.smul_def] at h2
  exact (mul_eq_zero.mp h2).resolve_left (fun h => hd0 (hinj (by rw [h, map_zero])))

private lemma gc_count [IsDomain O] [IsFractionRing O E] [Fintype τ] (x : R →ₐ[O] O) (𝒜 : Y → Submodule O R)
    {P : Ideal R} {φ : R →ₐ[O] MvPowerSeries τ E} (hφ : IsCompl P x φ)
    (hy : ∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a = 0) (z : τ → R) (hz : ∀ i, φ (z i) = X i) (w : τ → Y)
    (hw : ∀ i, z i ∈ 𝒜 (w i)) (hg : ∀ j, ∀ f ∈ 𝒜 j, φ f ∈ wtPart E w j) (j : Y) :
    Nat.card {i // w i = j} = finrank E ↥(wtDer 𝒜 x E j) := by
  classical
  have hcs : ∀ (c : O) e (f : MvPowerSeries τ E), coeff e (c • f) = c • coeff e f := fun c e f => rfl
  let L : ↥(wtDer 𝒜 x E j) →ₗ[E] ({i // w i = j} → E) :=
    { toFun := fun D i => (D : R →ₗ[O] E) (z i.1)
      map_add' := fun D1 D2 => by
        funext i
        simp
      map_smul' := fun c D => by
        funext i
        simp }
  have hinjL : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).mpr (fun D hD => ?_)
    apply Subtype.ext
    have h0 : ∀ i, (D : R →ₗ[O] E) (z i) = 0 := by
      intro i
      by_cases hi : w i = j
      · exact congrFun hD ⟨i, hi⟩
      · exact D.2.2 (w i) hi (z i) (hw i)
    exact gc_der x hφ hy z hz D.2.1 h0
  have hsurjL : Function.Surjective L := by
    intro v
    let Dv : R →ₗ[O] E :=
      { toFun := fun a => ∑ i0 : {i // w i = j}, v i0 * coeff (Finsupp.single i0.1 1) (φ a)
        map_add' := by
          intro a b
          simp only [map_add (f := _), mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro c a
          simp only [map_smul, RingHom.id_apply]
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun i0 _ => ?_)
          rw [hcs, mul_smul_comm] }
    have hDv : ∀ a, Dv a = ∑ i0 : {i // w i = j}, v i0 * coeff (Finsupp.single i0.1 1) (φ a) :=
      fun a => rfl
    have hmem : Dv ∈ wtDer 𝒜 x E j := by
      refine ⟨fun f g => ?_, fun i' hi' f hf => ?_⟩
      · show Dv (f * g) = algebraMap O E (x f) * Dv g + algebraMap O E (x g) * Dv f
        rw [hDv, hDv, hDv, map_mul]
        simp only [gc_coeff_single_mul, hφ.const, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun _ _ => ?_)
        ring
      · rw [hDv]
        refine Finset.sum_eq_zero (fun i0 _ => ?_)
        have hwt : Finsupp.weight w (Finsupp.single i0.1 1) = j := by
          simp [Finsupp.weight_apply, Finsupp.sum_single_index, i0.2]
        rw [hg i' f hf (Finsupp.single i0.1 1) (by rw [hwt]; exact fun h => hi' h.symm), mul_zero]
    refine ⟨⟨Dv, hmem⟩, ?_⟩
    funext i
    show Dv (z i.1) = v i
    rw [hDv, hz]
    simp [coeff_X, Finsupp.single_left_inj one_ne_zero]
    rw [Finset.sum_eq_single i (fun b _ hb => if_neg (fun h => hb (Subtype.ext h)))
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]
  let e := LinearEquiv.ofBijective L ⟨hinjL, hsurjL⟩
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Loc.gradedChart :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] {X : Type} [AddCommGroup X] (W : WPres O X R) (h : W.HasOrigin) (P : Ideal R) {n : ℕ} (φ : R →ₐ[O] MvPowerSeries (Fin n) E), UpperTheory.V.Loc.IsCompl P (W.origin h) φ → (∃ y, W.origin h y ≠ 0 ∧ ∀ a ∈ P, y * a = 0) → ∃ (w : Fin n → X) (φ' : R →ₐ[O] MvPowerSeries (Fin n) E), UpperTheory.V.Loc.IsCompl P (W.origin h) φ' ∧ (∀ j, ∀ f ∈ W.part j, φ' f ∈ wtPart E w j) ∧ ∀ j, Nat.card {i // w i = j} = finrank E ↥(wtDer W.part (W.origin h) E j) := by
  intro l _ O _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ R _ _ _ X _ W h P n φ hφ hy
  haveI : FaithfulSMul O E :=
    (faithfulSMul_iff_algebraMap_injective O E).mpr (IsFractionRing.injective O E)
  obtain ⟨u, hu⟩ := gc_span W h hφ
  have hz0 : ∀ i, W.origin h ((fun i => W.z (u i)) i) = 0 := fun i => origin_at_generator_eq_zero W h (u i)
  obtain ⟨φ', hφ', hX⟩ := chartChange n P (W.origin h) φ (fun i => W.z (u i)) hφ hz0 hu
  have hgr : ∀ j, ∀ f ∈ W.part j, φ' f ∈ wtPart E (fun i => W.wt (u i)) j :=
    fun j f hf => gc_graded W h hφ' hy u hX j f hf
  refine ⟨fun i => W.wt (u i), φ', hφ', hgr, fun j => ?_⟩
  exact gc_count (W.origin h) W.part hφ' hy (fun i => W.z (u i)) hX (fun i => W.wt (u i))
    (fun i => W.z_mem (u i)) hgr j
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.HomExt
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

private theorem hx_finite {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O]
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B]
    (x : R →ₐ[O] B) : Module.Finite O x.range := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  haveI : IsNoetherianRing x.range := isNoetherianRing_of_surjective R _ x.rangeRestrict.toRingHom
    x.rangeRestrict_surjective
  have hfin : ∀ m : MaximalSpectrum B, Module.Finite ℤ_[l] (integralClosure ℤ_[l] (B ⧸ m.asIdeal)) := fun m => by
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact IsIntegralClosure.finite ℤ_[l] ℚ_[l] (B ⧸ m.asIdeal) _
  let v : x.range →ₐ[ℤ_[l]] B := x.range.val.restrictScalars ℤ_[l]
  have hint : ∀ (m : MaximalSpectrum B) (z : x.range),
      ((Ideal.Quotient.mkₐ ℤ_[l] m.asIdeal).comp v) z ∈ integralClosure ℤ_[l] (B ⧸ m.asIdeal) := by
    rintro m ⟨_, a, rfl⟩
    haveI := m.isMaximal
    exact ((ptCont (l := l) R (B ⧸ m.asIdeal) ((Ideal.Quotient.mkₐ O m.asIdeal).comp x)).2
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 m.isMaximal)).1 a
  let g : x.range →ₐ[ℤ_[l]] ∀ m : MaximalSpectrum B, integralClosure ℤ_[l] (B ⧸ m.asIdeal) :=
    Pi.algHom _ _ fun m => AlgHom.codRestrict _ _ (hint m)
  haveI : Module.Finite ℤ_[l] g.range :=
    Module.Finite.of_injective g.range.val.toLinearMap Subtype.val_injective
  haveI : Module.Finite ℤ_[l] x.range := by
    refine Module.finite_of_surjective_of_ker_le_nilradical g.rangeRestrict g.rangeRestrict_surjective ?_
      (IsNoetherian.noetherian _)
    intro z hz
    have hz' : g z = 0 := congrArg Subtype.val hz
    have hj : (z : B) ∈ Ideal.jacobson (⊥ : Ideal B) := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      rintro I ⟨-, hI⟩
      have := congrArg Subtype.val (congrFun hz' ⟨I, hI⟩)
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
    refine ⟨n, Subtype.ext ?_⟩
    have := Ideal.pow_mem_pow hj n
    rw [hn] at this
    simpa using this
  exact Module.Finite.of_restrictScalars_finite ℤ_[l] O x.range

private theorem hx_pow {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    {A : Type} [CommRing A] [Algebra O A] [Module.Finite O A] (y : R →ₐ[O] A) :
    ∃ N : ℕ, ∀ a ∈ maximalIdeal R ^ N, y a ∈ (maximalIdeal O).map (algebraMap O A) := by
  have h1 : (maximalIdeal R).map y ≤ ((maximalIdeal O).map (algebraMap O A)).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro P ⟨hP, hPp⟩
    have hc : (P.comap (algebraMap O A)).IsMaximal := by
      rw [← (maximalIdeal.isMaximal _).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
        (Ideal.map_le_iff_le_comap.1 hP)]
      infer_instance
    haveI : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under P hc
    have hi : (y : R →+* A).IsIntegral := by
      refine RingHom.IsIntegral.tower_top (algebraMap O R) _ ?_
      rw [AlgHom.comp_algebraMap]
      exact fun a => Algebra.IsIntegral.isIntegral (R := O) a
    have := eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' (y : R →+* A) hi P)
    rw [Ideal.map_le_iff_le_comap, ← this]
    exact le_rfl
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h1 (Ideal.FG.map (IsNoetherian.noetherian _) _)
  refine ⟨N, fun a ha => hN ?_⟩
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem y ha

theorem UpperTheory.V.Loc.homExt :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R), ρ.Generates → ∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f f' : R →ₐ[O] B), (∀ g a b, f (ρ.hom g a b) = f' (ρ.hom g a b)) → f = f' := by
  intro l _ O _ _ _ _ _ _ _ Γ ι _ _ _ _ rbar R _ _ _ ρ hρ B _ _ _ _ _ _ _ f f' h
  choose c hc using IsCO.res_surj (O := O) (R := R)
  let S : Set R := Set.range fun s : Γ × ι × ι => ρ.hom s.1 s.2.1 s.2.2 - algebraMap O R (c (ρ.hom s.1 s.2.1 s.2.2))
  have hS : S ⊆ maximalIdeal R := by
    rintro _ ⟨s, rfl⟩
    exact hc _
  have hspan := co_span O R O (Algebra.ofId O R) S hS fun u u' _ hu => by
    haveI := (co_res O).2
    refine hρ _ u u' (Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => ?_))
    have := hu _ ⟨(g, a, b), rfl⟩
    simp only [map_sub, AlgHom.commutes, sub_left_inj] at this
    exact this
  haveI := hx_finite (l := l) f
  haveI := hx_finite (l := l) f'
  let A : Subalgebra O B := f.range ⊔ f'.range
  haveI : Module.Finite O A := Subalgebra.finite_sup _ _
  let u : R →ₐ[O] A := f.codRestrict A fun a => (le_sup_left : f.range ≤ A) ⟨a, rfl⟩
  let u' : R →ₐ[O] A := f'.codRestrict A fun a => (le_sup_right : f'.range ≤ A) ⟨a, rfl⟩
  haveI : IsHausdorff (maximalIdeal O) A := inferInstance
  haveI : IsHausdorff ((maximalIdeal O).map (algebraMap O A)) A := IsHausdorff.map_algebraMap_iff.2 this
  obtain ⟨N, hN⟩ := hx_pow u
  obtain ⟨N', hN'⟩ := hx_pow u'
  have key : u = u' := by
    refine co_ext O R O A ((maximalIdeal O).map (algebraMap O A)) (Algebra.ofId O R) S hS hspan u u'
      ⟨N + N', fun x hx => ⟨hN x (Ideal.pow_le_pow_right (Nat.le_add_right _ _) hx),
        hN' x (Ideal.pow_le_pow_right (Nat.le_add_left _ _) hx)⟩⟩ (Subsingleton.elim _ _) ?_
    rintro _ ⟨s, rfl⟩
    rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj]
    exact Subtype.ext (h _ _ _)
  ext a
  exact congrArg Subtype.val (DFunLike.congr_fun key a)
end

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

private theorem coeff_single_mul {E σ : Type} [CommRing E] (i : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
      MvPowerSeries.constantCoeff g * MvPowerSeries.coeff (Finsupp.single i 1) f := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, mul_comm]

private theorem hasWeight_of_generators {O R X Q : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (W : WPres O X R) (h : W.HasOrigin) [AddCommGroup Q] [Module O Q] (D : R →ₗ[O] Q)
    (hD : D ∈ PtDer (W.origin h) Q) (j : X) (hz : ∀ s, W.wt s ≠ j → D (W.z s) = 0) : HasWt W.part j D := by
  classical
  let W' := WPres.free O W.wt
  have h' : W'.HasOrigin := fun f hf => by
    have : f = 0 := hf
    rw [this, map_zero]
  have ho : ∀ f, W'.origin h' f = MvPowerSeries.constantCoeff f := fun f => W'.origin_π h' f
  let D' : MvPowerSeries W.σ O →ₗ[O] Q := D ∘ₗ W.π.toLinearMap -
    ∑ s, (MvPowerSeries.coeff (Finsupp.single s 1) : MvPowerSeries W.σ O →ₗ[O] O).smulRight (D (W.z s))
  have hD' : ∀ f, D' f = D (W.π f) - ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f • D (W.z s) := fun f => by
    simp [D']
  have h0 := (der_extend O _ X W' h' Q).2 D' (fun f g => by
    have h1 : D (W.π f * W.π g) = W.origin h (W.π f) • D (W.π g) + W.origin h (W.π g) • D (W.π f) := hD _ _
    rw [hD', hD', hD', ho, ho, map_mul, h1, W.origin_π, W.origin_π]
    simp only [coeff_single_mul, add_smul, mul_smul, Finset.sum_add_distrib, smul_sub, Finset.smul_sum]
    abel) (fun (s : W.σ) => by
    show D' (MvPowerSeries.X s) = 0
    rw [hD']
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj, WPres.z])
  rintro i hi _ ⟨f, hf, rfl⟩
  have h1 := hD' f
  rw [h0, LinearMap.zero_apply, eq_comm, sub_eq_zero] at h1
  refine h1.trans (Finset.sum_eq_zero fun s _ => ?_)
  by_cases hs : W.wt s = j
  · rw [hf (Finsupp.single s 1) (by simpa [Finsupp.weight_single, hs] using hi.symm), zero_smul]
  · rw [hz s hs, smul_zero]

private theorem origin_eq {O R X : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing R] [Algebra O R] [AddCommGroup X] (W : WPres O X R) (x : R →ₐ[O] O)
    (hx : ∀ s, x (W.z s) = 0) : ∃ h : W.HasOrigin, W.origin h = x := by
  have key : ∀ f, x (W.π f) = MvPowerSeries.constantCoeff f := by
    let F : MvPowerSeries W.σ O →ₐ[O] O :=
      { (MvPowerSeries.constantCoeff : MvPowerSeries W.σ O →+* O) with
        commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] }
    have := (co_ev O O O W.σ (AlgHom.id O O) 0 (fun _ => zero_mem _)).unique (y₁ := x.comp W.π) (y₂ := F)
      ⟨fun a => (x.comp W.π).commutes a, hx⟩ ⟨fun a => F.commutes a, fun s => MvPowerSeries.constantCoeff_X s⟩
    exact fun f => DFunLike.congr_fun this f
  refine ⟨fun f hf => by rw [← key, hf, map_zero], AlgHom.ext fun a => ?_⟩
  obtain ⟨f, rfl⟩ := W.surj a
  exact (W.origin_π _ f).trans (key f).symm

private theorem qcont_lin {l : ℕ} [Fact l.Prime] {V W X : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [AddCommGroup W] [Module ℚ_[l] W] [TopologicalSpace X] {φ : X → V} (hφ : QCont l φ) (ψ : V →ₗ[ℚ_[l]] W) :
    QCont l fun g => ψ (φ g) := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd ℚ_[l] W
  exact (IsModuleTopology.continuous_of_linearMap ψ).comp hφ

private theorem qcont_add {l : ℕ} [Fact l.Prime] {V X : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [TopologicalSpace X] {φ ψ : X → V} (hφ : QCont l φ) (hψ : QCont l ψ) : QCont l fun g => φ g + ψ g := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd ℚ_[l] V
  exact Continuous.add hφ hψ

private theorem qcont_dual {l : ℕ} [Fact l.Prime] {X E : Type} [TopologicalSpace X] [Field E] [Algebra ℚ_[l] E]
    (f : X → DualNumber E) (h1 : QCont l fun x => (f x).fst) (h2 : QCont l fun x => (f x).snd) : QCont l f := by
  have e : f = fun x => ((TrivSqZeroExt.inlAlgHom ℚ_[l] E E).toLinearMap (f x).fst) +
      (((TrivSqZeroExt.inrHom E E).restrictScalars ℚ_[l]) (f x).snd) :=
    funext fun x => (TrivSqZeroExt.inl_fst_add_inr_snd_eq _).symm
  rw [e]
  exact qcont_add (qcont_lin h1 _) (qcont_lin h2 _)

theorem UpperTheory.V.Loc.liftChart :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (w : ι → X) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R) (Q : ∀ (B : Type) [CommRing B] [Algebra O B], (Γ →* Matrix ι ι B) → Prop),
    (∀ (B B' : Type) [CommRing B] [Algebra O B] [CommRing B'] [Algebra O B'] (f : B →ₐ[O] B') (r : Γ →* Matrix ι ι B), (Q B r → Q B' (mapRep (f : B →+* B') r)) ∧ (Function.Injective f → Q B' (mapRep (f : B →+* B') r) → Q B r)) →
    Represents (fun R' _ _ _ r => Q R' r.hom) ρ → ρ.TStable w →
    ∀ ρ₀ : Lift O rbar O, Q O ρ₀.hom → (∀ g a b, w a ≠ w b → ρ₀.hom g a b = 0) →
    (∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (B' : Type) [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra O B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] O B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower O E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ r' : Γ →* Matrix ι ι B', mapRep (π' : B' →+* E) r' = mapRep (algebraMap O E) ρ₀.hom → (∀ a b, QCont l fun g => r' g a b) → Q B' r' → ∃ r : Γ →* Matrix ι ι B, (∀ a b, QCont l fun g => r g a b) ∧ Q B r ∧ mapRep (p : B →+* B') r = r') →
    ∃ (x : R →ₐ[O] O) (P : Ideal R) (n : ℕ) (u : Fin n → X) (φ : R →ₐ[O] MvPowerSeries (Fin n) E), ρ.map x = ρ₀ ∧ UpperTheory.V.Loc.IsCompl P x φ ∧ (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a = 0) ∧ (∀ g a b, φ (ρ.hom g a b) ∈ wtPart E u (w a - w b)) ∧
      ∀ j, ∃ S : Submodule E (Γ → Matrix ι ι E), Nat.card {i // u i = j} = finrank E ↥S ∧ ∀ s, s ∈ S ↔ (∃ r' : Γ →* Matrix ι ι (DualNumber E), (∀ g a b, r' g a b = ⟨algebraMap O E (ρ₀.hom g a b), s g a b⟩) ∧ Q (DualNumber E) r') ∧ (∀ a b, QCont l fun g => s g a b) ∧ ∀ g a b, w a - w b ≠ j → s g a b = 0 := by
  intro l _ O _ _ _ _ _ _ _ Γ ι _ _ _ _ _ _ rbar X _ _ _ w E _ _ _ _ _ _ _ _ R _ _ _ ρ Q hQ hrep hst ρ₀ hQ0 hd hlift
  have hgen : ρ.Generates := fun R' _ _ _ f f' h =>
    ((hrep R').2 _ ((hrep R').1 f')).unique h rfl
  have hQρ : Q R ρ.hom := (hrep R).1 (AlgHom.id O R)
  obtain ⟨x, hx, -⟩ := (hrep O).2 ρ₀ hQ0
  have hxe : ∀ g a b, x (ρ.hom g a b) = ρ₀.hom g a b := fun g a b => by rw [← hx]; rfl
  have hpt : ∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
      [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B]
      [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (r : Γ →* Matrix ι ι B),
      (∀ g a b, π (r g a b) = algebraMap O E (ρ₀.hom g a b)) → (∀ a b, QCont l fun g => r g a b) → Q B r →
      ∃ f : R →ₐ[O] B, ∀ g a b, f (ρ.hom g a b) = r g a b := by
    intro B _ _ _ _ _ _ _ _ _ _ π hπ r h1 h2 h3
    obtain ⟨C, hC, ρ', hρ'⟩ := exists_lift_factor_compact_subalgebra (l := l) rbar R ρ E B π hπ ((Algebra.ofId O E).comp x) r
      (fun g a b => by rw [h1, ← hxe]; rfl) h2
    have e : mapRep (C.val : C →+* B) ρ'.hom = r := MonoidHom.ext fun g => Matrix.ext fun a b => hρ' g a b
    obtain ⟨f, hf, -⟩ := (hrep C).2 ρ' ((hQ C B C.val ρ'.hom).2 Subtype.val_injective (e ▸ h3))
    refine ⟨C.val.comp f, fun g a b => ?_⟩
    rw [← hρ', ← hf]
    rfl
  have hc : ∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
      [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : R →ₐ[O] B) a b,
      QCont l fun g => f (ρ.hom g a b) := fun B _ _ _ _ _ _ _ f a b =>
    (ptCont (l := l) R B f).1 Γ _ (ρ.cont a b)
  obtain ⟨n, P, φ₀, hφ₀, -, ⟨y, hy, hyP⟩, -⟩ := smoothCompl (l := l) E R ⊥ x bot_le (by
    intro B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hpc f' _ hf'
    obtain ⟨r, h1, h2, h3⟩ := hlift B π hπ B' π' hπ' p hp hpc (mapRep (f' : R →+* B') ρ.hom)
      (MonoidHom.ext fun g => Matrix.ext fun a b => (hf' _).trans (congrArg _ (hxe g a b)))
      (hc B' f') ((hQ R B' f' _).1 hQρ)
    have h4 : ∀ g a b, p (r g a b) = f' (ρ.hom g a b) := fun g a b =>
      congrFun (congrFun (DFunLike.congr_fun h3 g) a) b
    obtain ⟨f, hf⟩ := hpt B π hπ r (fun g a b => by rw [← hpc, AlgHom.comp_apply, h4, hf', hxe]) h1 h2
    have := homExt (l := l) rbar R ρ hgen B' ((p.restrictScalars O).comp f) f' fun g a b => by
      rw [← h4, ← hf]; rfl
    exact ⟨f, bot_le, fun a => DFunLike.congr_fun this a⟩)
  obtain ⟨W, hW, hWz⟩ := lift_grading O X Γ ι rbar w R ρ (fun g => ρ₀.hom g)
    (fun g a b => by rw [← ρ₀.red]; exact ((res O O).commutes _).symm) hd hgen hst
  obtain ⟨h, rfl⟩ := origin_eq W x fun s => by
    obtain ⟨g, a, b, e, -⟩ := hWz s
    rw [e, map_sub, hxe, AlgHom.commutes]
    exact sub_self _
  obtain ⟨u, φ, hφ, hφw, hu⟩ := gradedChart (l := l) E R W h P φ₀ hφ₀ ⟨y, hy, hyP⟩
  refine ⟨_, P, n, u, φ, hx, hφ, ⟨y, hy, hyP⟩, fun g a b => hφw _ _ (hW g a b), fun j => ?_⟩
  haveI : Module.Finite E (DualNumber E) := inferInstanceAs (Module.Finite E (E × E))
  haveI : Module.Finite ℚ_[l] (DualNumber E) := inferInstanceAs (Module.Finite ℚ_[l] (E × E))
  let ev : (R →ₗ[O] E) →ₗ[E] (Γ → Matrix ι ι E) :=
    { toFun := fun δ g => Matrix.of fun a b => δ (ρ.hom g a b)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ∀ δ g a b, ev δ g a b = δ (ρ.hom g a b) := fun _ _ _ _ => rfl
  have hder : ∀ D : R → E, (∃ D' ∈ PtDer ((Algebra.ofId O E).comp (W.origin h)) E, ⇑D' = D) ↔
      ∃ y : R →ₐ[O] DualNumber E, ∀ f, (y f).fst = algebraMap O E (W.origin h f) ∧ (y f).snd = D f := by
    letI : Module Oᵐᵒᵖ E := Module.compHom E (RingEquiv.toOpposite O).symm.toRingHom
    haveI : IsCentralScalar O E := ⟨fun _ _ => rfl⟩
    exact der_hom O R E E ((Algebra.ofId O E).comp (W.origin h))
  have hO : ∀ δ ∈ PtDer ((Algebra.ofId O E).comp (W.origin h)) E, δ ∈ PtDer (W.origin h) E := fun δ hδ f g => by
    rw [hδ f g]
    simp [Algebra.smul_def]
  have hz : ∀ δ ∈ PtDer (W.origin h) E, ∀ g a b c, δ (ρ.hom g a b - algebraMap O R c) = δ (ρ.hom g a b) := by
    intro δ hδ g a b c
    have h1 : δ (1 * 1) = W.origin h 1 • δ 1 + W.origin h 1 • δ 1 := hδ 1 1
    rw [mul_one, map_one (W.origin h), one_smul, left_eq_add] at h1
    rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero, sub_zero]
  refine ⟨(wtDer W.part (W.origin h) E j).map ev, (hu j).trans ?_, fun s => ⟨?_, ?_⟩⟩
  · classical
    rw [← Submodule.range_subtype (wtDer W.part (W.origin h) E j), ← LinearMap.range_comp, Submodule.range_subtype,
      LinearMap.finrank_range_of_inj]
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro δ hδ
    refine Subtype.ext ((der_extend O R X W h E).2 δ.1 (hO _ δ.2.1) fun s => ?_)
    obtain ⟨g, a, b, e, -⟩ := hWz s
    rw [e, hz _ (hO _ δ.2.1)]
    exact congrFun (congrFun (congrFun hδ g) a) b
  · rintro ⟨δ, ⟨h1, h2⟩, rfl⟩
    obtain ⟨F, hF⟩ := (hder δ).1 ⟨δ, h1, rfl⟩
    refine ⟨⟨mapRep (F : R →+* DualNumber E) ρ.hom, fun g a b => TrivSqZeroExt.ext ?_ (hF _).2,
      (hQ R _ F _).1 hQρ⟩, fun a b => ?_, fun g a b hab => h2 _ hab _ (hW g a b)⟩
    · exact (hF _).1.trans (congrArg (algebraMap O E) (hxe g a b))
    · have := qcont_lin (hc (DualNumber E) F a b) (LinearMap.snd ℚ_[l] E E)
      simp only [hev, ← (hF _).2]
      exact this
  · rintro ⟨⟨r', h1, h2⟩, h3, h4⟩
    obtain ⟨F, hF⟩ := hpt (DualNumber E) (TrivSqZeroExt.fstHom E E E)
      (fun a ha => TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst.2 (by rw [show a.fst = 0 from ha]; exact IsNilpotent.zero))
      r' (fun g a b => by rw [h1]; rfl) (fun a b => qcont_dual _ (by
        simp only [h1, ← hxe]
        exact hc E ((Algebra.ofId O E).comp (W.origin h)) a b) (by
        simp only [h1]
        exact h3 a b)) h2
    have hfst := homExt (l := l) rbar R ρ hgen E (((TrivSqZeroExt.fstHom E E E).restrictScalars O).comp F)
      ((Algebra.ofId O E).comp (W.origin h)) fun g a b => by
        show (F _).fst = algebraMap O E (W.origin h _)
        rw [hF, h1, hxe]
        rfl
    obtain ⟨δ, hδ, e⟩ := (hder fun f => (F f).snd).2 ⟨F, fun f => ⟨DFunLike.congr_fun hfst f, rfl⟩⟩
    have he : ∀ g a b, δ (ρ.hom g a b) = s g a b := fun g a b => by
      rw [e]
      show (F _).snd = _
      rw [hF, h1]
      rfl
    refine ⟨δ, ⟨hδ, hasWeight_of_generators W h δ (hO _ hδ) j fun t ht => ?_⟩, funext fun g => Matrix.ext (he g)⟩
    obtain ⟨g, a, b, e1, e2⟩ := hWz t
    rw [e1, hz _ (hO _ hδ), he, h4 g a b (e2 ▸ ht)]
