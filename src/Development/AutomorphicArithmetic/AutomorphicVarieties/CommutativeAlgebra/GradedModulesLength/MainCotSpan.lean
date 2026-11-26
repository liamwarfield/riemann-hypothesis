module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.AlgMemCoef
public import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.CutHolds
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.IftSubstLow
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section SlopeTestRemainingChoices

open MvPowerSeries Formalism.FG.SolveVAux

variable {E σ τ Y : Type} [CommRing E] [AddCommGroup Y]

private theorem ift_P_mem {w : σ → Y} {w' : τ → Y} {k : σ → MvPowerSeries τ E}
    (hw : ∀ i, k i ∈ wtPart E w' (w i)) (e : σ →₀ ℕ) : P k e ∈ wtPart E w' (Finsupp.weight w e) := by
  induction e using Finsupp.induction_linear with
  | zero => rw [P_zero, map_zero]; exact one_mem_wtPart E w'
  | add e₁ e₂ h₁ h₂ => rw [P_add, map_add (f := _)]; exact mul_mem_wtPart E w' h₁ h₂
  | single i n =>
    rw [P_single, Finsupp.weight_single]
    exact SetLike.pow_mem_graded n (hw i)

private theorem ift_subst_mem [Finite σ] {w : σ → Y} {w' : τ → Y} {k : σ → MvPowerSeries τ E}
    (hk : ∀ i, Low 1 (k i)) (hw : ∀ i, k i ∈ wtPart E w' (w i)) {j : Y} {g : MvPowerSeries σ E}
    (hg : g ∈ wtPart E w j) : subst k g ∈ wtPart E w' j := by
  intro n hn
  rw [coeff_subst (hasSubst_of_low hk)]
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  by_cases he : Finsupp.weight w e = j
  · have := ift_P_mem hw e n (he ▸ hn)
    simp only [P] at this
    rw [this, smul_zero]
  · rw [hg e he, zero_smul]

private theorem ift_subst_low [Finite σ] {k : σ → MvPowerSeries τ E} (hk : ∀ i, Low 1 (k i)) {N : ℕ}
    {g : MvPowerSeries σ E} (hg : Low N g) : Low N (subst k g) := by
  intro d hd
  rw [coeff_subst (hasSubst_of_low hk)]
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  rcases lt_or_ge e.degree N with he | he
  · rw [hg e he, zero_smul]
  · have := low_P hk e d (by omega)
    simp only [P] at this
    rw [this, smul_zero]

private theorem ift_lim_mem [Finite σ] {w : σ → Y} {w' : τ → Y} {G : σ → MvPowerSeries τ E}
    {g : σ → MvPowerSeries σ E} (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j))
    (hGw : ∀ i, G i ∈ wtPart E w' (w i)) (hgw : ∀ i, g i ∈ wtPart E w (w i)) (i : σ) :
    Formalism.FG.SolveVAux.lim G g i ∈ wtPart E w' (w i) := by
  have hs : ∀ n i, Formalism.FG.SolveVAux.seq G g n i ∈ wtPart E w' (w i) := by
    intro n
    induction n with
    | zero => exact fun i => zero_mem _
    | succ n ih =>
      intro i
      rw [seq_succ]
      exact sub_mem (hGw i) (ift_subst_mem (seq_low hG hg n) ih (hgw i))
  intro d hd
  rw [coeff_lim]
  exact hs _ i d hd

private theorem ift_low_two {p : MvPowerSeries σ E} (h0 : constantCoeff p = 0)
    (h1 : ∀ i, coeff (Finsupp.single i 1) p = 0) : Low 2 p := by
  intro d hd
  rcases Nat.lt_succ_iff_lt_or_eq.1 hd with h | h
  · exact (low_one_iff p).2 h0 d h
  · obtain ⟨i, rfl⟩ := degree_eq_one d h
    exact h1 i

private theorem ift_coeff_X [DecidableEq σ] (i j : σ) :
    coeff (Finsupp.single i 1) (X j : MvPowerSeries σ E) = if i = j then 1 else 0 := by
  classical
  rw [coeff_X]
  simp [Finsupp.single_left_inj one_ne_zero]

private theorem ift_expand [Fintype σ] (g : MvPowerSeries σ E) :
    Low 2 (g - (constantCoeff g • 1 + ∑ s, coeff (Finsupp.single s 1) g • X s)) := by
  classical
  refine ift_low_two (by simp [map_sum]) fun i => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, ift_coeff_X, coeff_one]

end SlopeTestRemainingChoices

private theorem ift_span {E ι κ M : Type} [Field E] [Fintype ι] [Fintype κ] [DecidableEq κ] [AddCommGroup M]
    [Module E M] (hc : Fintype.card κ = Fintype.card ι) (c : Matrix κ ι E) (L : Matrix ι κ E) (h : c * L = 1)
    (v : ι → M) (hv : ∀ i, ∑ k, c i k • v k = 0) (k : ι) : v k = 0 := by
  classical
  have h' : L * c = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hc)).1 h
  have : ∑ i, L k i • ∑ k', c i k' • v k' = ∑ k', (L * c) k k' • v k' := by
    simp only [Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  simpa [hv, h', Matrix.one_apply] using this.symm

open MvPowerSeries Formalism.FG.SolveVAux in
theorem UpperTheory.V.Alg.M.ift_holds :
    ∀ (E τ ι X : Type) [Field E] [Fintype τ] [Fintype ι] [AddCommGroup X] (wt : τ → X) (z : ι → MvPowerSeries τ E),
      (∀ k, z k ∈ wtPart E wt 0 ∧ MvPowerSeries.constantCoeff (z k) = 0) → Nat.card {i // wt i = 0} = Fintype.card ι →
      (∀ i, wt i = 0 → ∃ c : ι → E, ∀ i', MvPowerSeries.coeff (Finsupp.single i' 1) (∑ k, c k • z k) =
        MvPowerSeries.coeff (Finsupp.single i' 1) (MvPowerSeries.X i : MvPowerSeries τ E)) →
      ∃ ψ : MvPowerSeries τ E →ₐ[E] MvPowerSeries {i // wt i ≠ 0} E,
        (∀ j, ∀ g ∈ wtPart E wt j, ψ g ∈ wtPart E (fun i : {i // wt i ≠ 0} => wt i) j) ∧ (∀ k, ψ (z k) = 0) ∧
        (∀ g, MvPowerSeries.constantCoeff (ψ g) = MvPowerSeries.constantCoeff g) ∧
        ∀ g (i : {i // wt i ≠ 0}), MvPowerSeries.coeff (Finsupp.single i 1) (ψ g) = MvPowerSeries.coeff (Finsupp.single i.1 1) g := by
  intro E τ ι Y _ _ _ _ wt z hz hcard hc
  classical
  choose c hc using hc
  let G : τ → MvPowerSeries {i // wt i ≠ 0} E := fun i => if h : wt i = 0 then 0 else X ⟨i, h⟩
  let g : τ → MvPowerSeries τ E := fun i => if h : wt i = 0 then ∑ k, c i h k • z k - X i else 0
  have hG : ∀ j, Low 1 (G j) := fun j => by
    rw [low_one_iff]
    simp only [G]
    split_ifs <;> simp
  have hg : ∀ j, Low 2 (g j) := fun j => by
    simp only [g]
    split_ifs with h
    · refine ift_low_two (by simp [map_sum, fun k => (hz k).2]) fun i => ?_
      rw [map_sub, hc, sub_self]
    · exact low_of_zero _
  have hGw : ∀ i, G i ∈ wtPart E (fun i : {i // wt i ≠ 0} => wt i) (wt i) := fun i => by
    simp only [G]
    split_ifs with h
    · exact zero_mem _
    · exact X_mem_wtPart E (fun i : {i // wt i ≠ 0} => wt i) ⟨i, h⟩
  have hgw : ∀ i, g i ∈ wtPart E wt (wt i) := fun i => by
    simp only [g]
    split_ifs with h
    · refine sub_mem (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_) (X_mem_wtPart E wt i)
      rw [h]; exact (hz k).1
    · exact zero_mem _
  have hl := lim_low hG hg
  have hs := hasSubst_of_low hl
  let ψ : MvPowerSeries τ E →ₐ[E] MvPowerSeries {i // wt i ≠ 0} E := substAlgHom hs
  have hψ : ∀ f, ψ f = subst (Formalism.FG.SolveVAux.lim G g) f := fun f => substAlgHom_apply hs f
  have hX : ∀ i, ψ (X i) = G i - ψ (g i) := fun i => by
    rw [hψ, hψ, subst_X hs]; exact (lim_fixed hG hg i).symm
  have hlow : ∀ f, Low 2 f → Low 2 (ψ f) := fun f hf => by rw [hψ]; exact ift_subst_low hl hf
  have key : ∀ f (d : {i // wt i ≠ 0} →₀ ℕ), d.degree < 2 → coeff d (ψ f) =
      constantCoeff f * coeff d (1 : MvPowerSeries {i // wt i ≠ 0} E) +
        ∑ s, coeff (Finsupp.single s 1) f * coeff d (G s) := fun f d hd => by
    have := hlow _ (ift_expand f) d hd
    rw [map_sub, map_sub, sub_eq_zero] at this
    rw [this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_smul, map_one, map_sum, hX, map_sub, hlow _ (hg _) d hd, sub_zero, smul_eq_mul]
  refine ⟨ψ, fun j f hf => ?_, ?_, fun f => ?_, fun f i => ?_⟩
  · rw [hψ]; exact ift_subst_mem hl (ift_lim_mem hG hg hGw hgw) hf
  · refine ift_span (E := E) (κ := {i // wt i = 0}) (by rw [← hcard, Nat.card_eq_fintype_card])
      (Matrix.of fun i k => c i.1 i.2 k) (Matrix.of fun k i => coeff (Finsupp.single i.1 1) (z k)) ?_
      (fun k => ψ (z k)) fun i => ?_
    · ext i i'
      have := hc i.1 i.2 i'.1
      rw [ift_coeff_X] at this
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul] at this
      simp only [Matrix.mul_apply, Matrix.of_apply, this, Matrix.one_apply, Subtype.ext_iff, eq_comm]
    · have := hX i.1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [G, g, dif_pos i.2, map_sub, map_sum, map_smul] at this
      simp only [Matrix.of_apply]
      linear_combination this
  · have := key f 0 (by simp)
    rw [← coeff_zero_eq_constantCoeff_apply, this]
    simp [fun s => hG s 0 (by simp)]
  · rw [key f _ (by simp), Finset.sum_eq_single i.1]
    · simp [G, i.2, coeff_one]
    · intro s _ hs
      simp only [G]
      split_ifs with h
      · simp
      · rw [ift_coeff_X, if_neg (fun h' => hs (by rw [h'])), mul_zero]
    · simp
end

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem lin_mul {E τ : Type} [CommRing E] (i : τ) (f g : MvPowerSeries τ E)
    (hf : MvPowerSeries.constantCoeff f = 0) (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  by_cases h1 : p.1 = 0
  · rw [h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul]
  · have h2 : p.2 = 0 := by
      have hd := congrArg Finsupp.degree h
      rw [map_add (f := _), Finsupp.degree_single] at hd
      have : Finsupp.degree p.1 ≠ 0 := fun h0 => h1 ((Finsupp.degree_eq_zero_iff _).1 h0)
      exact (Finsupp.degree_eq_zero_iff _).1 (by omega)
    rw [h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg, mul_zero]

private theorem lin_smul {O A τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (n : τ →₀ ℕ) (c : O) (f : A) :
    MvPowerSeries.coeff n (φ (c • f)) = algebraMap O (FractionRing O) c * MvPowerSeries.coeff n (φ f) := by
  rw [map_smul, ← algebraMap_smul (FractionRing O) c, map_smul, smul_eq_mul]

private theorem lin_sat {O A τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] (x : A →ₐ[O] O)
    (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O))
    (hc : ∀ f, MvPowerSeries.constantCoeff (φ f) = algebraMap O (FractionRing O) (x f)) (i : τ) (f : A)
    (hf : f ∈ satSq x) : MvPowerSeries.coeff (Finsupp.single i 1) (φ f) = 0 := by
  obtain ⟨c, hc0, h⟩ := hf
  have key : ∀ g ∈ RingHom.ker x * RingHom.ker x, MvPowerSeries.coeff (Finsupp.single i 1) (φ g) = 0 := by
    intro g hg
    refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [map_mul]
      exact lin_mul i _ _ (by rw [hc, (RingHom.mem_ker).1 ha, map_zero]) (by rw [hc, (RingHom.mem_ker).1 hb, map_zero])
    · rw [map_add (f := _), map_add (f := _), ha, hb, add_zero]
  have h2 := key _ (by rwa [sq] at h)
  rw [lin_smul] at h2
  exact (mul_eq_zero.1 h2).resolve_left fun h0 => hc0 (IsFractionRing.injective O (FractionRing O) (by rw [h0, map_zero]))

private theorem lin_proj {O A τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O))
    (hg : ∀ j, ∀ f ∈ 𝒜 j, φ f ∈ wtPart (FractionRing O) wt j) (i : τ) (hi : wt i = 0) (f : A) :
    MvPowerSeries.coeff (Finsupp.single i 1) (φ (DirectSum.decompose 𝒜 f 0 : A)) =
      MvPowerSeries.coeff (Finsupp.single i 1) (φ f) := by
  induction f using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous j a =>
    by_cases hj : j = 0
    · subst hj
      rw [DirectSum.decompose_of_mem_same 𝒜 a.2]
    · rw [DirectSum.decompose_of_mem_ne 𝒜 a.2 hj, map_zero, map_zero]
      exact (hg j a a.2 _ (by simp [Finsupp.weight_single, hi, Ne.symm hj])).symm
  | add a b ha hb => simp [DirectSum.decompose_add, ha, hb]

private theorem lin_span {O A τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O) (wt : τ → ℤ)
    (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (h : IsChart 𝒜 x wt φ) {m : ℕ} (Z : Fin m → A)
    (hZ : SpansCot x 𝒜 0 Z) (i : τ) (hi : wt i = 0) :
    ∃ c : Fin m → FractionRing O, ∀ i', MvPowerSeries.coeff (Finsupp.single i' 1) (∑ k, c k • φ (Z k)) =
        MvPowerSeries.coeff (Finsupp.single i' 1) (MvPowerSeries.X i : MvPowerSeries τ (FractionRing O)) := by
  classical
  obtain ⟨f, hf, hf'⟩ := h.onto i
  set f0 : A := (DirectSum.decompose 𝒜 f 0 : A) with hf0
  have hm0 : f0 ∈ 𝒜 0 := (DirectSum.decompose 𝒜 f 0).2
  set g : A := f0 - algebraMap O A (x f0) with hgdef
  have hg0 : g ∈ 𝒜 0 := sub_mem hm0 (SetLike.algebraMap_mem_graded 𝒜 _)
  have hgx : x g = 0 := by simp [hgdef]
  have hgl : ∀ i', MvPowerSeries.coeff (Finsupp.single i' 1) (φ g) =
      MvPowerSeries.coeff (Finsupp.single i' 1) (φ f0) := by
    intro i'
    rw [hgdef, map_sub, map_sub, AlgHom.commutes, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, if_neg (by simp),
      sub_zero]
  obtain ⟨c, hc, hs⟩ := hZ _ ⟨g, ⟨hg0, hgx⟩, rfl⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hs
  have hsat : (∑ k, a k • Z k) - c • g ∈ satSq x := by
    rw [← Submodule.Quotient.eq]
    show (satSq x).mkQ _ = (satSq x).mkQ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_smul, ← ha]
    simp only [map_smul]
  have hc' : algebraMap O (FractionRing O) c ≠ 0 := fun h0 =>
    hc (IsFractionRing.injective O (FractionRing O) (by rw [h0, map_zero]))
  refine ⟨fun k => (algebraMap O (FractionRing O) c * MvPowerSeries.coeff (Finsupp.single i 1) (φ f))⁻¹ *
    algebraMap O (FractionRing O) (a k), fun i' => ?_⟩
  have h1 := lin_sat x φ h.const i' _ hsat
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sub, sub_eq_zero, lin_smul, map_sum, map_sum, hgl] at h1
  simp only [lin_smul] at h1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum, h1, MvPowerSeries.coeff_X]
  by_cases hii : i' = i
  · subst hii
    rw [if_pos rfl, hf0, lin_proj 𝒜 wt φ h.graded i' hi, inv_mul_cancel₀ (mul_ne_zero hc' hf)]
  · rw [if_neg (fun h0 => hii (Finsupp.single_left_injective one_ne_zero h0))]
    have : MvPowerSeries.coeff (Finsupp.single i' 1) (φ f0) = 0 := by
      by_cases hw : wt i' = 0
      · rw [hf0, lin_proj 𝒜 wt φ h.graded i' hw, hf' i' hii]
      · exact h.graded 0 f0 hm0 _ (by simpa [Finsupp.weight_single] using hw)
    rw [this, mul_zero, mul_zero]

theorem UpperTheory.V.Alg.M.cut_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    M1 Q → ∃ (τ : Type) (_ : Fintype τ) (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ ∧
      (∀ i, φ (Q.Z i) = 0) ∧ ∀ j, Nat.card {i // wt i = j} = mDims r s r' s' 0 j := by
  classical
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x _ r s r' s' m Q ⟨_, ⟨τ, _, wt, φ, h, hcard⟩, _, _, hZ⟩
  obtain ⟨ψ, hψ1, hψ2, hψ3, hψ4⟩ := ift_holds (FractionRing O) τ (Fin m) ℤ wt (fun k => φ (Q.Z k))
    (fun k => ⟨h.graded 0 _ (Q.hZ k).1, by rw [h.const, (Q.hZ k).2, map_zero]⟩)
    (by rw [hcard 0]; simp [mDims]) (lin_span 𝒜 x wt φ h Q.Z hZ)
  refine ⟨{i // wt i ≠ 0}, inferInstance, fun i => wt i, (ψ.restrictScalars O).comp φ,
    ⟨fun j f hf => hψ1 j _ (h.graded j f hf), fun f => (hψ3 _).trans (h.const f), fun i => ?_, fun i => ?_⟩,
    hψ2, fun j => ?_⟩
  · obtain ⟨f, hf, hf'⟩ := h.onto i.1
    refine ⟨f, fun h0 => hf ((hψ4 _ i).symm.trans h0), fun i' hi' => (hψ4 _ i').trans (hf' _ fun h0 => hi' (Subtype.ext h0))⟩
  · have h1 : Nat.card {i' // wt i' = wt i} ≠ 0 := by
      haveI : Nonempty {i' // wt i' = wt i} := ⟨⟨i, rfl⟩⟩
      exact Nat.card_pos.ne'
    rw [hcard] at h1
    have h2 := i.2
    by_contra hn
    push Not at hn
    simp [mDims, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, h2] at h1
  · by_cases hj : j = 0
    · subst hj
      haveI : IsEmpty {i : {i // wt i ≠ 0} // wt i = 0} := ⟨fun i => i.1.2 i.2⟩
      simp [mDims]
    · have : mDims r s r' s' 0 j = mDims r s r' s' m j := by simp [mDims, hj]
      rw [this, ← hcard]
      exact Nat.card_congr ⟨fun i => ⟨i.1.1, i.2⟩, fun i => ⟨⟨i.1, by rw [i.2]; exact hj⟩, i.2⟩, fun _ => rfl, fun _ => rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FinHolds
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem UpperTheory.V.Alg.M.fin_gen {O A K : Type} [CommRing O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [Field K] [Algebra O K] (ξ : A →ₐ[O] K) (j : ℤ) (s : Finset A)
    (hs : Submodule.span (𝒜 0) (s : Set A) = oz 𝒜 j) (h : ∃ f ∈ 𝒜 j, ξ f ≠ 0) : ∃ f ∈ s, ξ f ≠ 0 := by
  obtain ⟨f, hf, hξ⟩ := h
  by_contra hne
  push_neg at hne
  have hf' : f ∈ Submodule.span (𝒜 0) (s : Set A) := by
    rw [hs]
    exact (mem_oz 𝒜).2 hf
  apply hξ
  clear hξ hf
  induction hf' using Submodule.span_induction with
  | mem y hy => exact hne y hy
  | zero => exact map_zero ξ
  | add y z _ _ hy hz => rw [map_add (f := _), hy, hz, add_zero]
  | smul a y _ hy => rw [Algebra.smul_def, map_mul, hy, mul_zero]

private theorem UpperTheory.V.Alg.M.fin_act {O A K : Type} [CommRing O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [Field K] [Algebra O K] (t : Kˣ) (ξ : A →ₐ[O] K) {j : ℤ} {a : A}
    (ha : a ∈ 𝒜 j) : act 𝒜 (tz t) ξ a = ((t ^ j : Kˣ) : K) * ξ a := act_of_mem 𝒜 _ ξ ha

private theorem UpperTheory.V.Alg.M.fin_inv {O A K : Type} [CommRing O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [Field K] [Algebra O K] (t : Kˣ) (ξ : A →ₐ[O] K) :
    ξ = act 𝒜 (tz t⁻¹) (act 𝒜 (tz t) ξ) := by
  classical
  ext a
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm := SetLike.coe_mem (DirectSum.decompose 𝒜 a i)
  rw [fin_act 𝒜 t⁻¹ _ hm, fin_act 𝒜 t ξ hm, ← mul_assoc, ← Units.val_mul, ← mul_zpow, inv_mul_cancel,
    one_zpow, Units.val_one, one_mul]

private theorem UpperTheory.V.Alg.M.fin_onS {O A K : Type} [CommRing O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [Field K] [Algebra O K] (t : Kˣ) (ξ : A →ₐ[O] K) (I : Ideal A)
    (hI : I.IsHomogeneous 𝒜) (h : OnS I ξ) : OnS I (act 𝒜 (tz t) ξ) := by
  classical
  intro f hf
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← DirectSum.sum_support_decompose 𝒜 f, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [fin_act 𝒜 _ _ (DirectSum.decompose 𝒜 f j).2, h _ (hI j hf), mul_zero]

theorem UpperTheory.V.Alg.M.fin_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ I : Ideal A, I.IsHomogeneous 𝒜 → M2 𝒜 I → M4 𝒜 K I → ∃ T : Finset (A →ₐ[O] K), Covers 𝒜 I T := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hx I hI h2 h4
  obtain ⟨s, hs⟩ := fg_holds O A 𝒜 x hx (-2)
  obtain ⟨s', hs'⟩ := fg_holds O A 𝒜 x hx 2
  have hsm : ∀ f ∈ s, f ∈ 𝒜 (-2) := by
    intro f hf
    rw [← mem_oz 𝒜, ← hs]
    exact Submodule.subset_span hf
  have hsm' : ∀ g ∈ s', g ∈ 𝒜 2 := by
    intro g hg
    rw [← mem_oz 𝒜, ← hs']
    exact Submodule.subset_span hg
  let S : Set (A →ₐ[O] K) := ⋃ f ∈ (s : Set A), ⋃ g ∈ (s' : Set A),
    {ξ | OnS I ξ ∧ ξ f = 1 ∧ ξ g ≠ 0 ∧ TwoSigned 𝒜 ξ}
  have hS : S.Finite := by
    refine s.finite_toSet.biUnion fun f hf => s'.finite_toSet.biUnion fun g hg => ?_
    exact (slice_holds O K A 𝒜 x hx I hI h2 h4 f (hsm f hf) g (hsm' g hg)).1.subset
      fun ξ hξ => ⟨hξ.1, hξ.2.1, hξ.2.2.1⟩
  refine ⟨hS.toFinset, fun ξ hξ => ?_, fun ξ hon htw => ?_⟩
  · rw [Set.Finite.mem_toFinset] at hξ
    simp only [S, Set.mem_iUnion, Set.mem_setOf_eq] at hξ
    obtain ⟨f, -, g, -, h1, -, -, h3⟩ := hξ
    exact ⟨h1, h3⟩
  · obtain ⟨f0, hf0, hξf0⟩ := (sign_holds O A 𝒜 x hx K ξ).1.1 htw.1
    obtain ⟨g0, hg0, hξg0⟩ := (sign_holds O A 𝒜 x hx K ξ).2.1 htw.2
    obtain ⟨f, hf, hξf⟩ := fin_gen 𝒜 ξ (-2) s hs ⟨f0, hf0, hξf0⟩
    obtain ⟨g, hg, hξg⟩ := fin_gen 𝒜 ξ 2 s' hs' ⟨g0, hg0, hξg0⟩
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (ξ f) (by norm_num : 0 < 2)
    have hr0 : r ≠ 0 := by
      rintro rfl
      apply hξf
      rw [← hr]
      ring
    have e1 : act 𝒜 (tz (Units.mk0 r hr0)) ξ f = 1 := by
      rw [fin_act 𝒜 _ ξ (hsm f hf), ← hr, Units.val_zpow_eq_zpow_val, Units.val_mk0, zpow_neg, zpow_ofNat,
        inv_mul_cancel₀ (pow_ne_zero _ hr0)]
    have e2 : act 𝒜 (tz (Units.mk0 r hr0)) ξ g ≠ 0 := by
      rw [fin_act 𝒜 _ ξ (hsm' g hg)]
      exact mul_ne_zero (Units.ne_zero _) hξg
    have e3 : TwoSigned 𝒜 (act 𝒜 (tz (Units.mk0 r hr0)) ξ) :=
      ⟨(sign_holds O A 𝒜 x hx K _).1.2 ⟨f, hsm f hf, by rw [e1]; exact one_ne_zero⟩,
        (sign_holds O A 𝒜 x hx K _).2.2 ⟨g, hsm' g hg, e2⟩⟩
    refine ⟨act 𝒜 (tz (Units.mk0 r hr0)) ξ, ?_, (Units.mk0 r hr0)⁻¹, fin_inv 𝒜 _ ξ⟩
    rw [Set.Finite.mem_toFinset]
    simp only [S, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨f, hf, g, hg, fin_onS 𝒜 _ ξ I hI hon, e1, e2, e3⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LinPartApply
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section

variable {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]

private theorem rk_fin [IsNoetherianRing O] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O) (j : ℤ)
    (hx : ∀ f ∈ 𝒜 j, x f = 0) (hfg : (oz 𝒜 j).FG) : Module.Finite O (cotLat x 𝒜 j) := by
  classical
  obtain ⟨S, hS⟩ := hfg
  rw [Module.Finite.iff_fg]
  refine ⟨S.image (satSq x).mkQ, ?_⟩
  rw [Finset.coe_image]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    have hsA : s ∈ 𝒜 j := by
      have : s ∈ oz 𝒜 j := hS ▸ Submodule.subset_span hs
      exact this
    exact ⟨s, ⟨hsA, hx s hsA⟩, rfl⟩
  · rintro _ ⟨f, ⟨hf, -⟩, rfl⟩
    have hf' : f ∈ Submodule.span (𝒜 0) (S : Set A) := by
      rw [hS]
      exact hf
    clear hf
    induction hf' using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span ⟨s, hs, rfl⟩
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add (f := _)]
      exact add_mem ha hb
    | smul a b hb ih =>
      have hbA : b ∈ 𝒜 j := by
        have : b ∈ oz 𝒜 j := hS ▸ hb
        exact this
      have hxb : x b = 0 := hx b hbA
      have e : (satSq x).mkQ (a • b) = (satSq x).mkQ (x (a : A) • b) := by
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        refine ⟨1, one_ne_zero, ?_⟩
        rw [one_smul, pow_two]
        have h1 : ((a : A) - algebraMap O A (x (a : A))) ∈ RingHom.ker x := by
          rw [RingHom.mem_ker]
          simp
        have h2 : b ∈ RingHom.ker x := by
          rw [RingHom.mem_ker]
          exact hxb
        have e2 : a • b - x (a : A) • b = ((a : A) - algebraMap O A (x (a : A))) * b := by
          rw [sub_mul, ← Algebra.smul_def]
          rfl
        rw [e2]
        exact Ideal.mul_mem_mul h1 h2
      rw [e, map_smul]
      exact Submodule.smul_mem _ _ ih

private noncomputable def linPart {τ : Type} (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) :
    A →ₗ[O] FractionRing O :=
  ((MvPowerSeries.coeff (Finsupp.single i 1)).restrictScalars O) ∘ₗ φ.toLinearMap

private theorem linPart_apply {τ : Type} (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) (f : A) :
    linPart φ i f = MvPowerSeries.coeff (Finsupp.single i 1) (φ f) := rfl

private theorem linPart_sat {τ : Type} {𝒜 : ℤ → Submodule O A} {x : A →ₐ[O] O} {wt : τ → ℤ}
    {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)} (h : IsChart 𝒜 x wt φ) (i : τ) :
    ∀ f ∈ satSq x, linPart φ i f = 0 := by
  intro f hf
  obtain ⟨c, hc, hcf⟩ := hf
  have hker : ∀ g ∈ RingHom.ker x ^ 2, linPart φ i g = 0 := by
    intro g hg
    rw [pow_two] at hg
    refine Submodule.mul_induction_on hg ?_ ?_
    · intro a ha b hb
      rw [linPart_apply, map_mul]
      apply MvPowerSeries.coeff_of_lt_order
      have ha0 : MvPowerSeries.constantCoeff (φ a) = 0 := by
        rw [h.const, RingHom.mem_ker.mp ha, map_zero]
      have hb0 : MvPowerSeries.constantCoeff (φ b) = 0 := by
        rw [h.const, RingHom.mem_ker.mp hb, map_zero]
      have hA := (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero).mpr ha0
      have hB := (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero).mpr hb0
      calc (((Finsupp.single i 1).degree : ℕ) : ℕ∞) = 1 := by simp
        _ < 1 + 1 := by norm_num
        _ ≤ (φ a).order + (φ b).order := add_le_add hA hB
        _ ≤ ((φ a) * (φ b)).order := MvPowerSeries.le_order_mul
    · intro a b ha hb
      rw [map_add (f := _), ha, hb, add_zero]
  have h0 := hker _ hcf
  rw [map_smul, Algebra.smul_def, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd ((IsFractionRing.injective O (FractionRing O)) (h0.trans (map_zero _).symm)) hc
  · exact h0

private theorem linPart_wt {τ : Type} {𝒜 : ℤ → Submodule O A} {x : A →ₐ[O] O} {wt : τ → ℤ}
    {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)} (h : IsChart 𝒜 x wt φ) (i : τ) {j : ℤ} (hij : wt i ≠ j)
    {f : A} (hf : f ∈ 𝒜 j) : linPart φ i f = 0 := by
  rw [linPart_apply]
  apply h.graded j f hf
  simpa [Finsupp.weight_apply, Finsupp.sum_single_index] using hij

private theorem linPart_proj {τ : Type} {𝒜 : ℤ → Submodule O A} [GradedAlgebra 𝒜] {x : A →ₐ[O] O} {wt : τ → ℤ}
    {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)} (h : IsChart 𝒜 x wt φ) (i : τ) {j : ℤ} (hij : wt i = j) (f : A) :
    linPart φ i (DirectSum.decompose 𝒜 f j) = linPart φ i f := by
  classical
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 f]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  by_cases hj : j ∈ (DirectSum.decompose 𝒜 f).support
  · rw [Finset.sum_eq_single j]
    · intro k _ hk
      exact linPart_wt h i (by rw [hij]; exact fun e => hk e.symm) (DirectSum.decompose 𝒜 f k).2
    · intro hn
      exact absurd hj hn
  · rw [DFinsupp.notMem_support_iff] at hj
    rw [hj]
    simp only [ZeroMemClass.coe_zero, map_zero]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k ≠ j := by
      rintro rfl
      exact (DFinsupp.mem_support_iff.mp hk) hj
    exact linPart_wt h i (by rw [hij]; exact fun e => hk' e.symm) (DirectSum.decompose 𝒜 f k).2

end

theorem UpperTheory.V.Alg.M.rk_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ n : ℤ → ℕ, SmoothPt 𝒜 x n → Module.Finite O (cotLat x 𝒜 (-1)) ∧ Module.finrank O (cotLat x 𝒜 (-1)) = n (-1) := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW n hS
  obtain ⟨τ, _, wt, φ, hc, hn⟩ := hS
  classical
  have hfin : Module.Finite O (cotLat x 𝒜 (-1)) :=
    rk_fin 𝒜 x (-1) (hW.fixed (-1) (by norm_num)) (fg_holds O A 𝒜 x hW (-1))
  refine ⟨hfin, ?_⟩
  let Lq : (A ⧸ satSq x) →ₗ[O] ({i // wt i = -1} → FractionRing O) :=
    (satSq x).liftQ (LinearMap.pi fun i : {i // wt i = -1} => linPart φ i.1) (by
      intro f hf
      rw [LinearMap.mem_ker]
      funext i
      exact linPart_sat hc i.1 f hf)
  let L : cotLat x 𝒜 (-1) →ₗ[O] ({i // wt i = -1} → FractionRing O) := Lq ∘ₗ (cotLat x 𝒜 (-1)).subtype
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨q, hq⟩ hLq
    obtain ⟨f, ⟨hf1, hf2⟩, rfl⟩ := hq
    have hx0 : x f = 0 := RingHom.mem_ker.mp hf2
    have hall : ∀ i : τ, MvPowerSeries.coeff (Finsupp.single i 1) (φ f) = 0 := by
      intro i
      rw [← linPart_apply]
      by_cases hi : wt i = -1
      · exact congrFun hLq ⟨i, hi⟩
      · exact linPart_wt hc i hi hf1
    have hs := hc.inj f hx0 hall
    apply Subtype.ext
    show (satSq x).mkQ f = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hs
  haveI : Module.IsTorsionFree O (FractionRing O) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (IsFractionRing.injective O _)
  haveI : Module.IsTorsionFree O (cotLat x 𝒜 (-1)) :=
    Function.Injective.moduleIsTorsionFree (⇑L) hinj (fun r m => L.map_smul r m)
  have hup : Module.finrank O (cotLat x 𝒜 (-1)) ≤ Fintype.card {i // wt i = -1} := by
    let B := Module.Free.chooseBasis O (cotLat x 𝒜 (-1))
    have hli : LinearIndependent O (L ∘ B) := B.linearIndependent.map' L (LinearMap.ker_eq_bot.mpr hinj)
    have hli' := (LinearIndependent.iff_fractionRing O (FractionRing O)).mp hli
    have h1 := hli'.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at h1
    rw [Module.finrank_eq_card_chooseBasisIndex]
    exact h1
  choose F hF0 hF1 using fun i : {i // wt i = -1} => hc.onto i.1
  have hmem : ∀ k : {i // wt i = -1},
      (satSq x).mkQ (DirectSum.decompose 𝒜 (F k) (-1) : A) ∈ cotLat x 𝒜 (-1) := fun k =>
    ⟨_, ⟨(DirectSum.decompose 𝒜 (F k) (-1)).2,
      RingHom.mem_ker.mpr (hW.fixed (-1) (by norm_num) _ (DirectSum.decompose 𝒜 (F k) (-1)).2)⟩, rfl⟩
  let g : {i // wt i = -1} → cotLat x 𝒜 (-1) := fun k => ⟨_, hmem k⟩
  have hgv : ∀ k i : {i // wt i = -1}, L (g k) i = linPart φ i.1 (F k) := by
    intro k i
    show linPart φ i.1 (DirectSum.decompose 𝒜 (F k) (-1) : A) = _
    exact linPart_proj hc i.1 i.2 (F k)
  have hli : LinearIndependent O g := by
    apply LinearIndependent.of_comp L
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have h1 := congrFun ha i
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, hgv, Pi.zero_apply] at h1
    rw [Finset.sum_eq_single i] at h1
    · rw [linPart_apply, Algebra.smul_def, mul_eq_zero] at h1
      rcases h1 with h2 | h2
      · exact (IsFractionRing.injective O (FractionRing O)) (h2.trans (map_zero _).symm)
      · exact absurd h2 (hF0 i)
    · intro k _ hk
      rw [linPart_apply, hF1 k i.1 (fun e => hk (Subtype.ext e.symm)), smul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hlow : Fintype.card {i // wt i = -1} ≤ Module.finrank O (cotLat x 𝒜 (-1)) :=
    hli.fintype_card_le_finrank
  rw [← hn (-1), Nat.card_eq_fintype_card]
  exact le_antisymm hup hlow
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.SmHolds
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem sm_smith {O P : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup P]
    [Module O P] [Module.Finite O P] [Module.IsTorsionFree O P] {r : ℕ} (hr : Module.finrank O P = r)
    (N : Submodule O P) (hN : Module.finrank O N = Module.finrank O P) (ϖ : O) (hϖ : Irreducible ϖ) :
    ∃ (y : Fin r → P) (c : Fin r → ℕ), Submodule.span O (Set.range fun i => ϖ ^ c i • y i) = N ∧
      Module.length O (P ⧸ N) = ((∑ i, c i : ℕ) : ℕ∞) := by
  classical
  let b := Module.finBasisOfFinrankEq O P hr
  have ha := fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (Submodule.smithNormalFormCoeffs_ne_zero b hN i) hϖ
  choose c u hu using ha
  refine ⟨fun i => (u i : O) • Submodule.smithNormalFormTopBasis b hN i, c, ?_, ?_⟩
  · have h1 : (fun i => ϖ ^ c i • (u i : O) • Submodule.smithNormalFormTopBasis b hN i) =
        N.subtype ∘ Submodule.smithNormalFormBotBasis b hN := by
      funext i
      simp only [Function.comp, Submodule.subtype_apply]
      rw [Submodule.smithNormalFormBotBasis_def, hu i, smul_smul, mul_comm]
    rw [h1, Set.range_comp, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]
  · rw [(N.quotientEquivPiSpan b hN).length_eq, Module.length_pi_of_fintype, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Ideal.span {Submodule.smithNormalFormCoeffs b hN i} = maximalIdeal O ^ c i := by
      rw [hu i, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit (u i).isUnit]
    rw [this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

private theorem sm_lift {O P : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup P]
    [Module O P] {r : ℕ} (φ : (Fin (r + 1) → O) →ₗ[O] P) (hr : Module.finrank O (LinearMap.range φ) = r)
    (n : Fin r → P) (hn : Submodule.span O (Set.range n) = LinearMap.range φ) :
    ∃ v : Fin (r + 1) → (Fin (r + 1) → O), Submodule.span O (Set.range v) = ⊤ ∧
      (∀ i : Fin r, φ (v i.castSucc) = n i) ∧ φ (v (Fin.last r)) = 0 := by
  have hw : ∀ i, ∃ w, φ w = n i := fun i => by
    have : n i ∈ LinearMap.range φ := hn ▸ Submodule.subset_span ⟨i, rfl⟩
    exact this
  choose w hw using hw
  have hk : Module.finrank O (LinearMap.ker φ) = 1 := by
    have h1 := (LinearMap.ker φ).finrank_quotient_add_finrank
    rw [φ.quotKerEquivRange.finrank_eq, hr, Module.finrank_fin_fun] at h1
    omega
  let b := Module.finBasisOfFinrankEq O (LinearMap.ker φ) hk
  refine ⟨Fin.snoc (α := fun _ => Fin (r + 1) → O) w (b 0 : Fin (r + 1) → O), ?_, fun i => by simp [hw], by simp⟩
  rw [eq_top_iff]
  intro u _
  have h1 : φ u ∈ Submodule.span O (Set.range n) := hn ▸ LinearMap.mem_range_self φ u
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 h1
  have h2 : u - ∑ i, a i • w i ∈ LinearMap.ker φ := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [LinearMap.mem_ker, map_sum, hw, ha]
  have h3 := congrArg Subtype.val (b.sum_repr ⟨_, h2⟩)
  simp only [Fin.sum_univ_one, Submodule.coe_smul] at h3
  rw [← sub_add_cancel u (∑ i, a i • w i), ← h3]
  refine add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last r, by simp⟩)) ?_
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.castSucc, by simp⟩)

theorem UpperTheory.V.Alg.M.sm_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (A : Type) [CommRing A] [Algebra O A]
      (𝒜 : ℤ → Submodule O A) (x : A →ₐ[O] O), (∀ f ∈ 𝒜 (-1), x f = 0) → ∀ (r : ℕ) (F : Fin (r + 1) → A), (∀ i, F i ∈ 𝒜 (-1)) →
      Module.Finite O (cotLat x 𝒜 (-1)) → Module.finrank O (cotLat x 𝒜 (-1)) = r → SpansCot x 𝒜 (-1) F →
      ∀ ϖ : O, Irreducible ϖ → ∃ (F' : Fin (r + 1) → A) (y : Fin r → A) (c : Fin r → ℕ),
        Submodule.span O (Set.range F') = Submodule.span O (Set.range F) ∧
        (∀ i, y i ∈ 𝒜 (-1) ∧ F' i.castSucc - ϖ ^ c i • y i ∈ satSq x) ∧ F' (Fin.last r) ∈ satSq x ∧
        cotLen x 𝒜 (-1) F = ((∑ i, c i : ℕ) : ℕ∞) := by
  intro O _ _ _ A _ _ 𝒜 x hx r F hF hfin hr hs ϖ hϖ
  classical
  haveI : Module.IsTorsionFree O (A ⧸ satSq x) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun c p h => ?_
    obtain ⟨f, rfl⟩ := (satSq x).mkQ_surjective p
    by_cases hc : c = 0
    · exact Or.inl hc
    right
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨d, hd, h⟩ := h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨d * c, mul_ne_zero hd hc, by rwa [mul_smul]⟩
  have hle : cotSpan x F ≤ cotLat x 𝒜 (-1) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨F i, ⟨hF i, hx _ (hF i)⟩, rfl⟩
  set N := (cotSpan x F).comap (cotLat x 𝒜 (-1)).subtype with hNdef
  have hN : Module.finrank O N = Module.finrank O (cotLat x 𝒜 (-1)) := by
    have h1 := N.finrank_quotient_add_finrank
    have h2 : Module.finrank O (cotLat x 𝒜 (-1) ⧸ N) = 0 := by
      rw [Module.finrank_eq_zero_iff]
      intro q
      obtain ⟨p, rfl⟩ := N.mkQ_surjective q
      obtain ⟨c, hc, hp⟩ := hs p.1 p.2
      refine ⟨c, hc, ?_⟩
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hp
    omega
  obtain ⟨y, c, hy, hlen⟩ := sm_smith hr N hN ϖ hϖ
  let ψ : (Fin (r + 1) → O) →ₗ[O] A := Fintype.linearCombination O F
  have hψ : LinearMap.range ψ = Submodule.span O (Set.range F) := Fintype.range_linearCombination O F
  have hφ : LinearMap.range ((satSq x).mkQ ∘ₗ ψ) = cotSpan x F := by
    rw [LinearMap.range_comp, hψ, Submodule.map_span, ← Set.range_comp]
    rfl
  have hmap : N.map (cotLat x 𝒜 (-1)).subtype = cotSpan x F := by
    rw [hNdef, Submodule.map_comap_subtype, inf_eq_right.2 hle]
  obtain ⟨v, hv, hv1, hv2⟩ := sm_lift ((satSq x).mkQ ∘ₗ ψ)
    (by rw [hφ]; exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq.symm.trans (hN.trans hr))
    (fun i => ϖ ^ c i • (y i : A ⧸ satSq x))
    (by rw [hφ, ← hmap, ← hy, Submodule.map_span, ← Set.range_comp]; rfl)
  have hz : ∀ i, ∃ z ∈ 𝒜 (-1), (satSq x).mkQ z = y i := fun i => by
    obtain ⟨z, hz, h⟩ := (y i).2
    exact ⟨z, hz.1, h⟩
  choose z hz hz' using hz
  refine ⟨ψ ∘ v, z, c, ?_, fun i => ⟨hz i, ?_⟩, ?_, hlen⟩
  · rw [Set.range_comp, ← Submodule.map_span, hv, Submodule.map_top, hψ]
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_smul, hz', sub_eq_zero]
    exact hv1 i
  · rw [← Submodule.Quotient.mk_eq_zero]
    exact hv2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.NzCoeffMul
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem nz_coeff_mul {τ E : Type} [CommRing E] (i : τ) (f g : MvPowerSeries τ E)
    (hf : MvPowerSeries.constantCoeff f = 0) (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd := congrArg Finsupp.degree h
  rw [map_add (f := _), Finsupp.degree_single] at hd
  by_cases h1 : Finsupp.degree p.1 = 0
  · rw [(Finsupp.degree_eq_zero_iff _).1 h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul]
  · have h2 : Finsupp.degree p.2 = 0 := by omega
    rw [(Finsupp.degree_eq_zero_iff _).1 h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg, mul_zero]

private theorem nz_comp {O A τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O) (wt : τ → ℤ)
    (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (h : IsChart0 𝒜 x wt φ) (i : τ) :
    ∃ f ∈ 𝒜 (wt i), MvPowerSeries.coeff (Finsupp.single i 1) (φ f) ≠ 0 := by
  classical
  obtain ⟨f, hf, -⟩ := h.onto i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← DirectSum.sum_support_decompose 𝒜 f, map_sum, map_sum] at hf
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hf
  have hm := (DirectSum.decompose 𝒜 f j).2
  have hw : wt i = j := by
    by_contra hne
    exact hj (h.graded j _ hm _ (by simpa [Finsupp.weight_single] using hne))
  exact ⟨_, hw ▸ hm, hj⟩

theorem UpperTheory.V.Alg.M.nz_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    1 ≤ Nat.card {i // wt i = -1} → 1 ≤ Nat.card {i // wt i = 1} → SpansCot x 𝒜 (-1) Q.F →
    ∀ a ∈ 𝒜 0, ∃ a' ∈ 𝒜 0, a' - a ∈ Q.ideal ∧ x a' = x a ∧ φ a' ≠ 0 := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q τ _ wt φ hφ hn hp hS a ha
  by_cases h0 : φ a = 0
  swap
  · exact ⟨a, ha, by simp, rfl, h0⟩
  obtain ⟨⟨i, hi⟩⟩ := (Nat.card_pos_iff.1 hn).1
  obtain ⟨⟨i', hi'⟩⟩ := (Nat.card_pos_iff.1 hp).1
  obtain ⟨f, hf, hf0⟩ := nz_comp 𝒜 x wt φ hφ i
  obtain ⟨g, hg, hg0⟩ := nz_comp 𝒜 x wt φ hφ i'
  rw [hi] at hf
  rw [hi'] at hg
  have hg1 : φ g ≠ 0 := fun h => hg0 (by rw [h, map_zero])
  have hinj : ∀ c : O, c ≠ 0 → ∀ y : FractionRing O, c • y = 0 → y = 0 := fun c hc y hy => by
    rw [Algebra.smul_def] at hy
    exact (mul_eq_zero.1 hy).resolve_left fun h => hc (IsFractionRing.injective O _ (h.trans (map_zero _).symm))
  have hF : ∃ k, φ (Q.F k) ≠ 0 := by
    by_contra hall
    push Not at hall
    let L : A →ₗ[O] FractionRing O :=
      ((MvPowerSeries.coeff (Finsupp.single i 1)).restrictScalars O) ∘ₗ φ.toLinearMap
    have hL : ∀ y, L y = MvPowerSeries.coeff (Finsupp.single i 1) (φ y) := fun _ => rfl
    have hsq : ∀ y ∈ RingHom.ker x ^ 2, L y = 0 := by
      intro y hy
      rw [sq] at hy
      refine Submodule.mul_induction_on hy (fun u hu v hv => ?_) (fun u v hu hv => by rw [map_add (f := _), hu, hv, add_zero])
      have hu' : x u = 0 := hu
      have hv' : x v = 0 := hv
      rw [hL, map_mul]
      exact nz_coeff_mul _ _ _ (by rw [hφ.const, hu', map_zero]) (by rw [hφ.const, hv', map_zero])
    have hk : satSq x ≤ LinearMap.ker L := by
      rintro y ⟨c, hc, hy⟩
      have := hsq _ hy
      rw [map_smul] at this
      exact hinj c hc _ this
    have hsp : cotSpan x Q.F ≤ LinearMap.ker ((satSq x).liftQ L hk) := by
      rw [cotSpan, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      show L (Q.F k) = 0
      rw [hL, hall k, map_zero]
    obtain ⟨c, hc, hcf⟩ := hS ((satSq x).mkQ f) ⟨f, ⟨hf, hW.fixed (-1) (by norm_num) f hf⟩, rfl⟩
    have := hsp hcf
    rw [LinearMap.mem_ker, map_smul] at this
    exact hf0 (hinj c hc _ this)
  obtain ⟨k, hk⟩ := hF
  have hm : g * Q.F k ∈ 𝒜 0 := by simpa using SetLike.GradedMul.mul_mem hg (Q.hF k)
  refine ⟨a + g * Q.F k, add_mem ha hm, ?_, ?_, ?_⟩
  · rw [add_sub_cancel_left]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · rw [map_add (f := _), map_mul, hW.fixed 1 one_ne_zero g hg, zero_mul, add_zero]
  · rw [map_add (f := _), h0, zero_add, map_mul]
    exact mul_ne_zero hg1 hk
end

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem UpperTheory.V.Alg.M.main_cotSpan {O A ι : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    (x : A →ₐ[O] O) (F : ι → A) : cotSpan x F = (Submodule.span O (Set.range F)).map (satSq x).mkQ := by
  unfold cotSpan
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

private theorem UpperTheory.V.Alg.M.main_span {O A ι : Type} [CommRing O] [CommRing A] [Algebra O A]
    {F F' : ι → A} (h : Submodule.span O (Set.range F') = Submodule.span O (Set.range F)) :
    Ideal.span (Set.range F') = Ideal.span (Set.range F) := by
  have key : ∀ {G G' : ι → A}, Submodule.span O (Set.range G') ≤ Submodule.span O (Set.range G) →
      Ideal.span (Set.range G') ≤ Ideal.span (Set.range G) := by
    intro G G' hle
    rw [Ideal.span_le]
    intro y hy
    have h1 : y ∈ Submodule.span O (Set.range G) := hle (Submodule.subset_span hy)
    have h2 : Submodule.span O (Set.range G) ≤ (Ideal.span (Set.range G)).restrictScalars O :=
      Submodule.span_le.mpr Ideal.subset_span
    exact h2 h1
  exact le_antisymm (key h.le) (key h.ge)

theorem UpperTheory.V.Alg.M.main_holds :
    LemmaM := by
  intro O _ _ _ _ _ K _ _ _ _ v hv A _ _ 𝒜 _ x hW r s r' s' m Q a h1 h2 h3 h4 h5
  haveI := hW.co
  obtain ⟨hr, hsm, hF, hG, hZ⟩ := h1
  obtain ⟨hfin, hrk⟩ := rk_holds O A 𝒜 x hW _ hsm
  have hrk' : Module.finrank O (cotLat x 𝒜 (-1)) = r := by rw [hrk]; simp [mDims]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨F', y, c, hspan, hy, hlast, hlen⟩ :=
    sm_holds O A 𝒜 x (hW.fixed _ (by norm_num)) r Q.F Q.hF hfin hrk' hF ϖ hϖ
  have hF'mem : ∀ i, F' i ∈ 𝒜 (-1) := fun i => by
    have : F' i ∈ Submodule.span O (Set.range Q.F) := hspan ▸ Submodule.subset_span ⟨i, rfl⟩
    exact (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact Q.hF j)) this
  let Q' : Eqns 𝒜 x r s r' s' m := { Q with F := F', hF := hF'mem }
  have hI : Q'.ideal = Q.ideal := by
    simp only [Eqns.ideal, Ideal.span_union]
    rw [show Ideal.span (Set.range Q'.F) = Ideal.span (Set.range Q.F) from main_span hspan]
  have hF' : SpansCot x 𝒜 (-1) Q'.F := by
    intro p hp
    obtain ⟨d, hd, hp'⟩ := hF p hp
    refine ⟨d, hd, ?_⟩
    rw [main_cotSpan] at hp' ⊢
    exact hspan ▸ hp'
  have h1' : M1 Q' := ⟨hr, hsm, hF', hG, hZ⟩
  obtain ⟨τ, _, wt, φ, hφ, hφZ, hcard⟩ := cut_holds O A 𝒜 x hW r s r' s' m Q' h1'
  obtain ⟨a', ha'0, ha'I, ha'x, ha'φ⟩ := nz_holds O A 𝒜 x hW r s r' s' m Q' τ wt φ hφ
    (by rw [hcard]; simpa [mDims] using hr) (by rw [hcard]; simp [mDims]) hF' a h5.1
  rw [hI] at ha'I
  have hval : ∀ ξ : A →ₐ[O] K, OnS Q.ideal ξ → ξ a' = ξ a := fun ξ hξ => by
    have := hξ _ ha'I
    rwa [map_sub, sub_eq_zero] at this
  have h5' : M5 𝒜 K x Q.ideal a' :=
    ⟨ha'0, ha'x.trans h5.2.1, fun ξ hξ ht => by rw [hval ξ hξ]; exact h5.2.2 ξ hξ ht⟩
  refine ⟨?_, by rw [hlen]; exact ENat.coe_ne_top _, fun T hT => ?_⟩
  · exact fin_holds O K A 𝒜 x hW _ (hom_holds O A 𝒜 x hW r s r' s' m Q).1 h2 h4
  · have := core_holds O K v hv A 𝒜 x hW r s r' s' m Q' τ wt φ hφ hφZ hr hcard ϖ hϖ y c hy hlast hF' hG
      (hI ▸ h2) (hI ▸ h3) (hI ▸ h4) a' (hI ▸ h5') ha'φ T (hI ▸ hT)
    rw [hlen, ENat.toNat_coe]
    rwa [Finset.sum_congr rfl fun ξ hξ => congrArg v (hval ξ (hT.1 ξ hξ).1)] at this
