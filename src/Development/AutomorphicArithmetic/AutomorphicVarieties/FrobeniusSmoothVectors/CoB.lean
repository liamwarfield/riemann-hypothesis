module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerExtend
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KrullDimQuotientComapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrpOfMemSucc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrNorm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContMap
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem mon_part {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
    {R : Type} [CommRing R] [Algebra O R] (ρ : NRep F n R) (W : WPres O ℤ R)
    (h : ∀ g i j, ρ.r g i j ∈ W.part (w n i - w n j)) {j : ℤ} {x : R} (hx : x ∈ ρ.mon j) : x ∈ W.part j := by
  obtain ⟨L, hL, rfl⟩ := hx
  rw [← hL]
  exact SetLike.list_prod_map_mem_graded L _ _ fun s _ => h s.1 s.2.1 s.2.2

private theorem mono_lemma {l : ℕ} [Fact l.Prime] {K : Type} [Field K] {F : Frame l K} {n : ℕ}
    {R : Type} [CommRing R] (ρ : NRep F n R) {a b : ℤ} {x y : R} (hx : x ∈ ρ.mon a) (hy : y ∈ ρ.mon b) :
    x * y ∈ ρ.mon (a + b) := by
  obtain ⟨L1, h1, rfl⟩ := hx
  obtain ⟨L2, h2, rfl⟩ := hy
  exact ⟨L1 ++ L2, by simp [h1, h2], by simp⟩

private theorem mono_lemma_2 {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {K : Type} [Field K] {F : Frame l K} {n : ℕ}
    {R : Type} [CommRing R] [Algebra O R] (ρ : NRep F n R) (W : WPres O ℤ R) (D : Subalgebra O R)
    (h : ∀ s, (∃ g i j, W.z s = ρ.r g i j ∧ W.wt s = w n i - w n j) ∨ (W.wt s = 0 ∧ W.z s ∈ D)) (s : W.σ) (e : ℕ) :
    ∃ b ∈ D, ∃ x ∈ ρ.mon (e • W.wt s), W.z s ^ e = b * x := by
  induction e with
  | zero => exact ⟨1, D.one_mem, 1, ⟨[], by simp, by simp⟩, by simp⟩
  | succ e ih =>
    obtain ⟨b, hb, x, hx, hbx⟩ := ih
    rcases h s with ⟨g, i, j, hz, hw⟩ | ⟨hw, hz⟩
    · have hs : ρ.r g i j ∈ ρ.mon (W.wt s) := ⟨[(g, i, j)], by simp [hw], by simp⟩
      refine ⟨b, hb, x * ρ.r g i j, ?_, ?_⟩
      · rw [succ_nsmul]
        exact mono_lemma ρ hx hs
      · rw [pow_succ, hbx, hz]
        ring
    · refine ⟨b * W.z s, D.mul_mem hb hz, x, ?_, ?_⟩
      · simpa [hw] using hx
      · rw [pow_succ, hbx]
        ring

private theorem mono {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
    {R : Type} [CommRing R] [Algebra O R] (ρ : NRep F n R) (W : WPres O ℤ R) (D : Subalgebra O R)
    (h : ∀ s, (∃ g i j, W.z s = ρ.r g i j ∧ W.wt s = w n i - w n j) ∨ (W.wt s = 0 ∧ W.z s ∈ D)) (m : W.σ →₀ ℕ) :
    ∃ b ∈ D, ∃ x ∈ ρ.mon (Finsupp.weight W.wt m), W.π (MvPowerSeries.monomial m 1) = b * x := by
  induction m using Finsupp.induction with
  | zero => exact ⟨1, D.one_mem, 1, ⟨[], by simp, by simp⟩, by simp⟩
  | single_add a e f _ _ ih =>
    obtain ⟨b, hb, x, hx, hbx⟩ := ih
    obtain ⟨b', hb', x', hx', hbx'⟩ := mono_lemma_2 ρ W D h a e
    refine ⟨b' * b, D.mul_mem hb' hb, x' * x, ?_, ?_⟩
    · have hw : Finsupp.weight W.wt (Finsupp.single a e) = e • W.wt a := by
        simp [Finsupp.weight_apply, Finsupp.sum_single_index]
      rw [map_add (f := _), hw]
      exact mono_lemma ρ hx' hx
    · have hm : MvPowerSeries.monomial (Finsupp.single a e + f) (1 : O) =
          MvPowerSeries.X a ^ e * MvPowerSeries.monomial f 1 := by
        rw [MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul]
      simp only [WPres.z] at hbx'
      rw [hm, map_mul, map_pow, hbx, hbx']
      ring

private theorem dense {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] (W : WPres O ℤ R)
    (hz : ∀ s, W.z s ∈ maximalIdeal R) (D : Subalgebra O R)
    (hD : ∀ m, Finsupp.weight W.wt m = 0 → W.π (MvPowerSeries.monomial m 1) ∈ D) {y : R} (hy : y ∈ W.part 0) :
    y ∈ adicClosure D := by
  haveI := W.fin
  classical
  simp only [WPres.part, Submodule.mem_map] at hy
  obtain ⟨f, hf, rfl⟩ := hy
  have hf' : ∀ m, Finsupp.weight W.wt m ≠ 0 → MvPowerSeries.coeff m f = 0 := hf
  have key : ∀ m, W.π (MvPowerSeries.monomial m (MvPowerSeries.coeff m f)) ∈ D := by
    intro m
    by_cases hm : Finsupp.weight W.wt m = 0
    · have e : MvPowerSeries.monomial m (MvPowerSeries.coeff m f) =
          MvPowerSeries.coeff m f • MvPowerSeries.monomial m (1 : O) := by
        rw [← LinearMap.map_smul, smul_eq_mul, mul_one]
      rw [e, map_smul]
      exact D.smul_mem (hD m hm) _
    · rw [hf' m hm, map_zero, map_zero]
      exact D.zero_mem
  simp only [AlgHom.toLinearMap_apply]
  show ∀ N : ℕ, ∃ d ∈ D, W.π f - d ∈ maximalIdeal R ^ N
  intro N
  let c : W.σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N
  let low := ∑ m ∈ Finset.Iic c, MvPowerSeries.monomial m (MvPowerSeries.coeff m f)
  let S : Set (W.σ →₀ ℕ) := {m | Finsupp.weight W.wt m = 0 ∧ ∃ s, N ≤ m s}
  have hg : ∀ m ∉ S, MvPowerSeries.coeff m (f - low) = 0 := by
    intro m hm
    simp only [S, Set.mem_setOf_eq, not_and, not_exists, not_le] at hm
    have hl : MvPowerSeries.coeff m low = if m ∈ Finset.Iic c then MvPowerSeries.coeff m f else 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [low, map_sum, MvPowerSeries.coeff_monomial]
    rw [map_sub, hl]
    by_cases hw : Finsupp.weight W.wt m = 0
    · have hmc : m ∈ Finset.Iic c := by
        rw [Finset.mem_Iic]
        intro s
        exact (hm hw s).le.trans_eq (by simp [c])
      simp [hmc]
    · simp [hf' m hw]
  obtain ⟨μ, hμ, hspan⟩ := part_span O R ℤ W S 0 (fun m hm => hm.1)
  obtain ⟨b, hb, hfb⟩ := hspan (f - low) hg
  refine ⟨W.π low, ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Subalgebra.sum_mem _ fun m _ => key m
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sub, hfb, map_sum]
    refine Ideal.sum_mem _ fun m hm => ?_
    obtain ⟨s, hs⟩ := (hμ (Finset.mem_coe.mpr hm)).2
    have e : MvPowerSeries.monomial m (1 : O) =
        MvPowerSeries.X s ^ N * MvPowerSeries.monomial (m - Finsupp.single s N) 1 := by
      rw [MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul,
        add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hs)]
    rw [map_mul, e, map_mul, map_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hz s) N))

private theorem cont_map {O Γ R R' : Type} [CommRing O] [IsLocalRing O] [TopologicalSpace Γ] [CommRing R] [Algebra O R]
    [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (c : R') {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => c * f (a g) := by
  have hm : Ideal.map f.toRingHom (maximalIdeal R) ≤ maximalIdeal R' := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    show f x ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O R', res_map, res_eq_zero_iff]
    exact hx
  intro N
  have hN : maximalIdeal R ^ N ≤ Ideal.comap f.toRingHom (maximalIdeal R' ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hm N
  have e : (fun g => Ideal.Quotient.mk (maximalIdeal R' ^ N) (c * f (a g))) =
      (fun q => Ideal.Quotient.mk (maximalIdeal R' ^ N) c *
        Ideal.quotientMap (maximalIdeal R' ^ N) f.toRingHom hN q) ∘
        (fun g => Ideal.Quotient.mk (maximalIdeal R ^ N) (a g)) := by
    funext g
    simp [Ideal.quotientMap_mk]
  rw [e]
  exact (ha N).comp _

private theorem twist_lemma {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
    {n : ℕ} (S : Space O F n) (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : S.R →ₐ[O] C)
    (c : Fin n → Fin n → C) (hc : ∀ i, c i i = 1) (ρ' : NRep F n C)
    (hr : ∀ g i j, ρ'.r g i j = c i j * f (S.ρ.r g i j)) (hψ : ∀ v i g, (ρ'.ψ v i g : C) = f (S.ρ.ψ v i g)) :
    IsLift O ρ' := by
  obtain ⟨⟨hc1, hc2⟩, ⟨hb1, hb2⟩, hd⟩ := S.lift
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, ⟨fun g i => ?_, fun v i g => ?_⟩, fun g i j hij => ?_⟩
  · simpa only [hr] using cont_map f (c i j) (hc1 i j)
  · simpa only [hψ, one_mul] using cont_map f 1 (hc2 v i)
  · show (res O C) (ρ'.r g i i) = _
    rw [hr, hc, one_mul, res_map]
    exact hb1 g i
  · show (res O C) ((ρ'.ψ v i g : Cˣ) : C) = _
    rw [hψ, res_map]
    exact hb2 v i g
  · show (res O C) (ρ'.r g i j) = 0
    rw [hr, map_mul, res_map]
    have h0 : (res O S.R) (S.ρ.r g i j) = 0 := hd g i j hij
    rw [h0, mul_zero]

private theorem twist {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
    {n : ℕ} (S : Space O F n) (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : S.R →ₐ[O] C) (u : Cˣ) :
    ∃ f' : S.R →ₐ[O] C, (∀ g i j, f' (S.ρ.r g i j) = ((u ^ (w n i - w n j) : Cˣ) : C) * f (S.ρ.r g i j)) ∧
      ∀ v i g, f' (S.ρ.ψ v i g) = f (S.ρ.ψ v i g) := by
  obtain ⟨ρ', hr, hψ⟩ := alg_twist u (S.ρ.map (f : S.R →+* C))
  have hl : IsLift O ρ' := twist_lemma S C f (fun i j => ((u ^ (w n i - w n j) : Cˣ) : C)) (by simp) ρ'
    (fun g i j => by rw [hr]; rfl) (fun v i g => by rw [hψ]; rfl)
  obtain ⟨f', hf', -⟩ := S.univ C ρ' hl
  refine ⟨f', fun g i j => ?_, fun v i g => ?_⟩
  · calc f' (S.ρ.r g i j) = (S.ρ.map (f' : S.R →+* C)).r g i j := rfl
      _ = ρ'.r g i j := by rw [hf']
      _ = _ := by rw [hr]; rfl
  · calc f' (S.ρ.ψ v i g : S.R) = (((S.ρ.map (f' : S.R →+* C)).ψ v i g : Cˣ) : C) := rfl
      _ = (ρ'.ψ v i g : C) := by rw [hf']
      _ = _ := by rw [hψ]; rfl

private theorem uniq {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
    {n : ℕ} (S : Space O F n) (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f f' : S.R →ₐ[O] C)
    (h1 : ∀ g i j, f (S.ρ.r g i j) = f' (S.ρ.r g i j)) (h2 : ∀ v i g, f (S.ρ.ψ v i g) = f' (S.ρ.ψ v i g)) :
    f = f' := by
  have hl : IsLift O (S.ρ.map (f : S.R →+* C)) := twist_lemma S C f (fun _ _ => 1) (fun _ => rfl) _
    (fun g i j => by rw [one_mul]; rfl) (fun v i g => rfl)
  refine (S.univ C _ hl).unique rfl (NRep.ext ?_ ?_)
  · exact MonoidHom.ext fun g => Matrix.ext fun i j => (h1 g i j).symm
  · funext v i
    exact MonoidHom.ext fun g => Units.ext (h2 v i g).symm

private theorem coord {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] {F : Frame l (ResidueField O)} {n : ℕ} (S : Space O F n) :
    ∃ W : WPres O ℤ S.R, (∀ s, W.z s ∈ maximalIdeal S.R) ∧ (∀ g i j, S.ρ.r g i j ∈ W.part (w n i - w n j)) ∧
      (∀ v i g, (S.ρ.ψ v i g : S.R) ∈ W.part 0) ∧
      ∀ s, (∃ g i j, W.z s = S.ρ.r g i j ∧ W.wt s = w n i - w n j) ∨
        (W.wt s = 0 ∧ W.z s ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)})) := by
  classical
  let a : S.R → O := fun x => Classical.choose (IsCO.res_surj (O := O) x)
  have ha : ∀ x, x - algebraMap O S.R (a x) ∈ maximalIdeal S.R := fun x =>
    Classical.choose_spec (IsCO.res_surj (O := O) x)
  let e : (F.G0 × Fin n × Fin n) ⊕ (Σ v : F.V, Fin n × F.Gv v) → S.R := Sum.elim
    (fun p => if p.2.1 = p.2.2 then S.ρ.r p.1 p.2.1 p.2.2 - algebraMap O S.R (a (S.ρ.r p.1 p.2.1 p.2.2))
      else S.ρ.r p.1 p.2.1 p.2.2)
    (fun q => (S.ρ.ψ q.1 q.2.1 q.2.2 : S.R) - algebraMap O S.R (a (S.ρ.ψ q.1 q.2.1 q.2.2)))
  let wt : (F.G0 × Fin n × Fin n) ⊕ (Σ v : F.V, Fin n × F.Gv v) → ℤ := Sum.elim
    (fun p => w n p.2.1 - w n p.2.2) (fun _ => 0)
  have eon : ∀ g i, e (Sum.inl (g, i, i)) = S.ρ.r g i i - algebraMap O S.R (a (S.ρ.r g i i)) :=
    fun g i => if_pos rfl
  have eoff : ∀ g i j, i ≠ j → e (Sum.inl (g, i, j)) = S.ρ.r g i j := fun g i j h => if_neg h
  have eψ : ∀ v i g, e (Sum.inr ⟨v, i, g⟩) =
      (S.ρ.ψ v i g : S.R) - algebraMap O S.R (a (S.ρ.ψ v i g)) := fun v i g => rfl
  have hoff : ∀ g i j, i ≠ j → S.ρ.r g i j ∈ maximalIdeal S.R := fun g i j h =>
    (res_eq_zero_iff O S.R _).mp (by exact S.lift.2.2 g i j h)
  have he : ∀ s, e s ∈ maximalIdeal S.R := by
    rintro (⟨g, i, j⟩ | ⟨v, i, g⟩)
    · by_cases h : i = j
      · subst h
        rw [eon]
        exact ha _
      · rw [eoff g i j h]
        exact hoff g i j h
    · rw [eψ]
      exact ha _
  have huniq : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : S.R →ₐ[O] R'),
      (∀ s, f (e s) = f' (e s)) → f = f' := by
    intro R' _ _ _ f f' h
    apply uniq S R' f f'
    · intro g i j
      by_cases hij : i = j
      · subst hij
        have h1 := h (Sum.inl (g, i, i))
        rw [eon, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes] at h1
        exact sub_left_injective h1
      · have h1 := h (Sum.inl (g, i, j))
        rw [eoff g i j hij] at h1
        exact h1
    · intro v i g
      have h1 := h (Sum.inr ⟨v, i, g⟩)
      rw [eψ, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes] at h1
      exact sub_left_injective h1
  have htw : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : S.R →ₐ[O] R')
      (t : Multiplicative ℤ →* R'ˣ), (∀ j, res O R' (t j) = 1) →
      ∃ f' : S.R →ₐ[O] R', ∀ s, f' (e s) = (t (Multiplicative.ofAdd (wt s)) : R') * f (e s) := by
    intro R' _ _ _ f t _
    obtain ⟨f', h1, h2⟩ := twist S R' f (t (Multiplicative.ofAdd 1))
    have ht : ∀ k : ℤ, t (Multiplicative.ofAdd k) = t (Multiplicative.ofAdd 1) ^ k := by
      intro k
      rw [← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
    refine ⟨f', ?_⟩
    rintro (⟨g, i, j⟩ | ⟨v, i, g⟩)
    · by_cases hij : i = j
      · subst hij
        show f' (e (Sum.inl (g, i, i))) = (t (Multiplicative.ofAdd (w n i - w n i)) : R') * _
        rw [sub_self, eon, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, h1]
        simp
      · show f' (e (Sum.inl (g, i, j))) = (t (Multiplicative.ofAdd (w n i - w n j)) : R') * _
        rw [eoff g i j hij, h1, ht (w n i - w n j)]
    · show f' (e (Sum.inr ⟨v, i, g⟩)) = (t (Multiplicative.ofAdd 0) : R') * _
      rw [eψ, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, h2]
      simp
  obtain ⟨W, u, hWu, hpart⟩ := coord_grading O ℤ S.R _ e wt he huniq htw
  have h1mem : ∀ c : O, algebraMap O S.R c ∈ W.part 0 := fun c => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c SetLike.GradedOne.one_mem
  refine ⟨W, fun s => by rw [(hWu s).1]; exact he _, ?_, ?_, ?_⟩
  · intro g i j
    by_cases hij : i = j
    · subst hij
      have hp : S.ρ.r g i i - algebraMap O S.R (a (S.ρ.r g i i)) ∈ W.part 0 := by
        have := hpart (Sum.inl (g, i, i))
        rw [eon] at this
        simpa [wt] using this
      rw [sub_self, ← sub_add_cancel (S.ρ.r g i i) (algebraMap O S.R (a (S.ρ.r g i i)))]
      exact add_mem hp (h1mem _)
    · have hp := hpart (Sum.inl (g, i, j))
      rw [eoff g i j hij] at hp
      exact hp
  · intro v i g
    have hp : (S.ρ.ψ v i g : S.R) - algebraMap O S.R (a (S.ρ.ψ v i g)) ∈ W.part 0 :=
      hpart (Sum.inr ⟨v, i, g⟩)
    rw [← sub_add_cancel (S.ρ.ψ v i g : S.R) (algebraMap O S.R (a (S.ρ.ψ v i g)))]
    exact add_mem hp (h1mem _)
  · intro s
    obtain ⟨hz, hw⟩ := hWu s
    rcases hs : u s with ⟨g, i, j⟩ | ⟨v, i, g⟩
    · rw [hs] at hz hw
      by_cases hij : i = j
      · subst hij
        right
        refine ⟨by rw [hw]; exact sub_self _, ?_⟩
        rw [hz, eon]
        exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (Or.inl ⟨[(g, i, i)], by simp, by simp⟩))
          (Subalgebra.algebraMap_mem _ _)
      · left
        exact ⟨g, i, j, by rw [hz, eoff g i j hij], hw⟩
    · rw [hs] at hz hw
      right
      refine ⟨hw, ?_⟩
      rw [hz, eψ]
      exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (Or.inr ⟨v, i, g, rfl⟩))
        (Subalgebra.algebraMap_mem _ _)

private theorem val_prod {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
    {n : ℕ} (S : Space O F n) (L : List (F.G0 × Fin n × Fin n)) :
    (((L.map fun s => S.u.r s.1 s.2.1 s.2.2).prod : S.A) : S.R) = (L.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, Subalgebra.coe_mul, ih]
    rfl

theorem UpperTheory.V.Fr.wpres :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∃ W : WPres O ℤ S.R, (∀ s, W.z s ∈ maximalIdeal S.R) ∧ (∀ g i j, S.ρ.r g i j ∈ W.part (w n i - w n j)) ∧ (∀ y, y ∈ S.B ↔ y ∈ W.part 0) ∧ S.A = W.A ∧ ∀ j (a : S.A), a ∈ S.gr j ↔ (a : S.R) ∈ W.part j := by
  intro l _ O _ _ _ _ F C₀ n _ _ S
  obtain ⟨W, hz, hr, hψ, hgen⟩ := coord S
  let D : Subalgebra O S.R := Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)})
  have hmon : ∀ m, ∃ b ∈ D, ∃ x ∈ S.ρ.mon (Finsupp.weight W.wt m),
      W.π (MvPowerSeries.monomial m 1) = b * x := mono S.ρ W D hgen
  have hD : ∀ m, Finsupp.weight W.wt m = 0 → W.π (MvPowerSeries.monomial m 1) ∈ D := by
    intro m hm
    obtain ⟨b, hb, x, hx, e⟩ := hmon m
    rw [e]
    rw [hm] at hx
    exact D.mul_mem hb (Algebra.subset_adjoin (Or.inl hx))
  have P0 : ∀ y, y ∈ W.part 0 → y ∈ S.B := fun y hy => dense W hz D hD hy
  let P : Subalgebra O S.R := (W.part 0).toSubalgebra SetLike.GradedOne.one_mem (fun x y hx hy => by
    have := SetLike.GradedMul.mul_mem hx hy
    rwa [add_zero] at this)
  have BP : ∀ y, y ∈ S.B → y ∈ W.part 0 := by
    intro y hy
    have hDP : D ≤ P := Algebra.adjoin_le (by
      rintro x (hx | ⟨v, i, g, rfl⟩)
      · exact mon_part S.ρ W hr hx
      · exact hψ v i g)
    have hy' : ∀ N : ℕ, ∃ d ∈ D, y - d ∈ maximalIdeal S.R ^ N := hy
    refine part_closed O ℤ S.R W hz 0 y fun N => ?_
    obtain ⟨d, hd, hyd⟩ := hy' N
    exact ⟨d, hDP hd, hyd⟩
  have dec : ∀ j y, y ∈ W.part j → ∃ μ : Finset (W.σ →₀ ℕ), ∃ c x : (W.σ →₀ ℕ) → S.R,
      (∀ m, c m ∈ S.B) ∧ (∀ m ∈ μ, x m ∈ S.ρ.mon j) ∧ y = ∑ m ∈ μ, c m * x m := by
    intro j y hy
    simp only [WPres.part, Submodule.mem_map] at hy
    obtain ⟨f, hf, rfl⟩ := hy
    obtain ⟨μ, hμ, hspan⟩ := part_span O S.R ℤ W {m | Finsupp.weight W.wt m = j} j (fun m hm => hm)
    obtain ⟨b, hb, hfb⟩ := hspan f (fun m hm => hf m hm)
    choose B hB X hX hBX using hmon
    refine ⟨μ, fun m => W.π (b m) * B m, X,
      fun m => S.B.mul_mem (P0 _ (Submodule.mem_map_of_mem (hb m))) (le_adicClosure D (hB m)),
      fun m hm => ?_, ?_⟩
    · have := hX m
      have hw : Finsupp.weight W.wt m = j := hμ (Finset.mem_coe.mpr hm)
      rwa [hw] at this
    · simp only [AlgHom.toLinearMap_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hfb, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, hBX, mul_assoc]
  refine ⟨W, hz, hr, fun y => ⟨BP y, P0 y⟩, ?_, ?_⟩
  · apply le_antisymm
    · refine Algebra.adjoin_le ?_
      rintro x (hx | ⟨g, i, j, rfl⟩)
      · exact W.part_le_A (BP x hx)
      · exact W.part_le_A (hr g i j)
    · intro x hx
      have hx' : x ∈ ⨆ j, W.part j := hx
      have hle : (⨆ j, W.part j) ≤ Subalgebra.toSubmodule S.A := by
        refine iSup_le fun j y hy => ?_
        rw [Subalgebra.mem_toSubmodule]
        obtain ⟨μ, c, X, hc, hX, rfl⟩ := dec j y hy
        refine Subalgebra.sum_mem _ fun m hm => S.A.mul_mem (Algebra.subset_adjoin (Or.inl (hc m))) ?_
        obtain ⟨L, -, hXL⟩ := hX m hm
        rw [hXL, ← val_prod S L]
        exact SetLike.coe_mem _
      exact hle hx'
  · intro j a
    constructor
    · intro ha
      refine Submodule.span_induction (p := fun (a : S.A) _ => (a : S.R) ∈ W.part j) ?_ ?_ ?_ ?_
        (show a ∈ Submodule.span S.B (S.u.mon j) from ha)
      · rintro x ⟨L, hL, rfl⟩
        rw [val_prod]
        exact mon_part S.ρ W hr ⟨L, hL, rfl⟩
      · simp
      · intro x y _ _ hx hy
        simpa using add_mem hx hy
      · intro b x _ hx
        have := SetLike.GradedMul.mul_mem (BP b b.2) hx
        rw [zero_add] at this
        have hbx : ((b • x : S.A) : S.R) = (b : S.R) * (x : S.R) := by
          first | rfl | simp [Algebra.smul_def] | simp [Subalgebra.smul_def]
        rw [hbx]
        exact this
    · intro ha
      obtain ⟨μ, c, X, hc, hX, e⟩ := dec j _ ha
      have hXu : ∀ m ∈ μ, ∃ a' ∈ S.u.mon j, (a' : S.R) = X m := by
        intro m hm
        obtain ⟨L, hL, e'⟩ := hX m hm
        exact ⟨_, ⟨L, hL, rfl⟩, by rw [val_prod, e']⟩
      choose! A' hA' hA'e using hXu
      have hsum : a = ∑ m ∈ μ, (⟨c m, hc m⟩ : S.B) • A' m := by
        apply Subtype.ext
        rw [e]
        simp only [AddSubmonoidClass.coe_finsetSum]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [← hA'e m hm]
        rfl
      rw [hsum]
      exact Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (Submodule.subset_span (hA' m hm))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.co_B :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∃ h : IsCO O S.B, @maximalIdeal _ _ h.toIsLocalRing = S.mB := by
  intro l _ O _ _ _ _ F C₀ n hF hn S
  obtain ⟨W, hz, -, hB, -, -⟩ := UpperTheory.V.Fr.wpres hF hn S
  haveI h0 : IsCO O (W.gr 0) := UpperTheory.V.Alg.wPres_gr_zero_isCO_of_mem_maximalIdeal O ℤ S.R W hz
  let p : W.gr 0 →ₐ[O] S.B :=
    { toFun := fun b => ⟨((b : W.A) : S.R), (hB _).2 b.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hp : Function.Surjective p := fun y =>
    ⟨⟨⟨y.1, W.part_le_A ((hB _).1 y.2)⟩, (hB _).1 y.2⟩, rfl⟩
  haveI h : IsCO O S.B := UpperTheory.V.Alg.co_quot O (W.gr 0) S.B p hp
  refine ⟨h, ?_⟩
  ext b
  show _ ↔ S.B.val b ∈ maximalIdeal S.R
  rw [← res_eq_zero_iff O, ← res_eq_zero_iff O, res_map]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem isInternal_congr {ι M σ σ' : Type} [DecidableEq ι] [AddCommMonoid M] [SetLike σ M]
    [AddSubmonoidClass σ M] [SetLike σ' M] [AddSubmonoidClass σ' M] (A : ι → σ) (A' : ι → σ')
    (h : ∀ i x, x ∈ A' i ↔ x ∈ A i) (hA : DirectSum.IsInternal A) : DirectSum.IsInternal A' := by
  let e : ∀ i, A' i ≃+ A i := fun i =>
    { toFun := fun x => ⟨x.1, (h i _).1 x.2⟩
      invFun := fun x => ⟨x.1, (h i _).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let E : DirectSum ι (fun i => A' i) ≃+ DirectSum ι (fun i => A i) := DFinsupp.mapRange.addEquiv e
  have hE : DirectSum.coeAddMonoidHom A' = (DirectSum.coeAddMonoidHom A).comp E.toAddMonoidHom := by
    refine DirectSum.addHom_ext fun i x => ?_
    have h1 : E (DirectSum.of (fun i => A' i) i x) = DirectSum.of (fun i => A i) i (e i x) :=
      DFinsupp.mapRange_single (hf := fun i => (e i).map_zero)
    show _ = DirectSum.coeAddMonoidHom A (E (DirectSum.of (fun i => A' i) i x))
    rw [h1, DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    rfl
  unfold DirectSum.IsInternal
  rw [hE]
  exact hA.comp E.bijective

private theorem gr_transfer (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O ℤ R)
    (hz : ∀ s, W.z s ∈ maximalIdeal R) (B A : Subalgebra O R) [Algebra B A]
    (halg : ∀ b : B, ((algebraMap B A b : A) : R) = b) (gr : ℤ → Submodule B A)
    (hB : ∀ y, y ∈ B ↔ y ∈ W.part 0) (hA : A = W.A) (hgr : ∀ j (a : A), a ∈ gr j ↔ (a : R) ∈ W.part j) :
    DirectSum.IsInternal gr ∧ SetLike.GradedMonoid gr ∧ gr 0 = 1 ∧ (∀ j, (gr j).FG) ∧ Algebra.FiniteType B A ∧
      IsNoetherianRing A := by
  subst hA
  obtain ⟨h1, h2, h3⟩ := gr_noeth O ℤ R W hz
  have h0 : ∀ a : W.A, a ∈ W.gr 0 → ∃ b : B, algebraMap B W.A b = a := fun a ha =>
    ⟨⟨a, (hB _).2 ha⟩, Subtype.ext (halg _)⟩
  refine ⟨isInternal_congr W.gr gr hgr (gr_internal O ℤ R W), ?_, ?_, fun j => ?_, ?_, h1⟩
  · exact
      { one_mem := (hgr _ _).2 (SetLike.GradedOne.one_mem : (1 : R) ∈ W.part 0)
        mul_mem := fun _ _ _ _ ha hb => (hgr _ _).2 (SetLike.mul_mem_graded ((hgr _ _).1 ha) ((hgr _ _).1 hb)) }
  · ext a
    rw [Submodule.mem_one, hgr]
    refine ⟨h0 a, ?_⟩
    rintro ⟨b, rfl⟩
    rw [halg]
    exact (hB _).1 b.2
  · obtain ⟨s, hs, hs'⟩ := h3 j
    refine ⟨s, le_antisymm (Submodule.span_le.2 fun a ha => (hgr _ _).2 (hs a ha)) fun a ha => ?_⟩
    have ha' : a ∈ W.gr j := (hgr _ _).1 ha
    rw [hs'] at ha'
    refine Submodule.mul_induction_on ha' (fun x hx y hy => ?_) fun x y hx hy => add_mem hx hy
    obtain ⟨b, rfl⟩ := h0 x hx
    rw [← Algebra.smul_def]
    refine Submodule.smul_mem _ _ ?_
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul c y _ hy =>
      obtain ⟨b, hb⟩ := h0 _ (SetLike.algebraMap_mem_graded W.gr c)
      rw [Algebra.smul_def, ← hb, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hy
  · obtain ⟨s, hs⟩ := h2.out
    refine ⟨⟨s, ?_⟩⟩
    rw [eq_top_iff]
    intro a ht
    clear ht
    have ha : a ∈ Algebra.adjoin (W.gr 0) (s : Set W.A) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem y hy => exact Algebra.subset_adjoin hy
    | algebraMap r =>
      obtain ⟨b, hb⟩ := h0 r.1 r.2
      have : algebraMap (W.gr 0) W.A r = algebraMap B W.A b := hb.symm
      rw [this]
      exact Subalgebra.algebraMap_mem _ b
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb

theorem UpperTheory.V.Fr.gr_A :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, DirectSum.IsInternal S.gr ∧ SetLike.GradedMonoid S.gr ∧ S.gr 0 = 1 ∧ (∀ j, (S.gr j).FG) ∧ Algebra.FiniteType S.B S.A ∧ IsNoetherianRing S.A ∧ ∀ g i j, S.u.r g i j ∈ S.gr (w n i - w n j) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S
  obtain ⟨W, hz, hr, hB, hA, hgr⟩ := UpperTheory.V.Fr.wpres hF hn S
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := gr_transfer O S.R W hz S.B S.A (fun _ => rfl) S.gr hB hA hgr
  exact ⟨h1, h2, h3, h4, h5, h6, fun g i j => (hgr _ _).2 (hr g i j)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MemPowSmulLe
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : UpperTheory.V.Fr.Frame l (ResidueField O)} {n : ℕ}
  (S : Space O F n)

end

theorem UpperTheory.V.Fr.cont_u :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, S.u.Cont S.x0 ∧ (∀ i, AdicCont S.mB fun g => S.aB g i) ∧ (∀ v i, AdicCont S.mB (S.ψB v i)) ∧ ∀ j (N : ℕ), ∃ M : ℕ, ∀ a ∈ S.gr j, (a : S.R) ∈ maximalIdeal S.R ^ M → a ∈ S.mB ^ N • S.gr j := by
  intro l _ O _ _ _ _ F C₀ n hF hn S
  obtain ⟨W, hz, hr, hB, hA, hgr⟩ := wpres hF hn S
  have hAW : ∀ (j : ℤ) (q : S.R), q ∈ W.part j → q ∈ S.A := by
    intro j q hq
    rw [hA]
    exact Submodule.mem_iSup_of_mem j hq
  have hmulB : ∀ (N : ℕ) (Q : Submodule O S.R),
      (∀ y ∈ Q, ∃ b : S.B, (b : S.R) = y ∧ b ∈ S.mB ^ N) →
      ∀ y ∈ Q * W.part 0, ∃ b : S.B, (b : S.R) = y ∧ b ∈ S.mB ^ N := by
    intro N Q hQ y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro p hp q hq
      obtain ⟨p', rfl, hp'⟩ := hQ p hp
      have hq0 : q ∈ S.B := (hB q).2 hq
      exact ⟨p' * ⟨q, hq0⟩, rfl, Ideal.mul_mem_right _ _ hp'⟩
    · rintro x z ⟨x', rfl, hx'⟩ ⟨z', rfl, hz'⟩
      exact ⟨x' + z', rfl, Ideal.add_mem _ hx' hz'⟩
  have hP : ∀ (N : ℕ) (y : S.R), y ∈ (W.part 0 ⊓ Submodule.restrictScalars O (maximalIdeal S.R)) ^ N →
      ∃ b : S.B, (b : S.R) = y ∧ b ∈ S.mB ^ N := by
    intro N
    induction N with
    | zero =>
      intro y hy
      rw [pow_zero, Submodule.mem_one] at hy
      obtain ⟨o, rfl⟩ := hy
      exact ⟨algebraMap O S.B o, rfl, by simp⟩
    | succ N ih =>
      intro y hy
      rw [pow_succ] at hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro p hp q hq
        obtain ⟨p', rfl, hp'⟩ := ih p hp
        have hq0 : q ∈ S.B := (hB q).2 hq.1
        have hqm : (⟨q, hq0⟩ : S.B) ∈ S.mB := by
          show q ∈ maximalIdeal S.R
          exact hq.2
        refine ⟨p' * ⟨q, hq0⟩, rfl, ?_⟩
        rw [pow_succ]
        exact Ideal.mul_mem_mul hp' hqm
      · rintro x z ⟨x', rfl, hx'⟩ ⟨z', rfl, hz'⟩
        exact ⟨x' + z', rfl, Ideal.add_mem _ hx' hz'⟩
  have hT : ∀ (N : ℕ) (j : ℤ) (y : S.R),
      y ∈ (W.part 0 ⊓ Submodule.restrictScalars O (maximalIdeal S.R)) ^ N * W.part 0 * W.part j →
      ∃ a : S.A, (a : S.R) = y ∧ a ∈ S.mB ^ N • S.gr j ∧ a ∈ S.x0 ^ N := by
    intro N j y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro p hp q hq
      obtain ⟨b, rfl, hb⟩ := hmulB N _ (hP N) p hp
      have hqA : q ∈ S.A := hAW j q hq
      refine ⟨b • (⟨q, hqA⟩ : S.A), rfl, Submodule.smul_mem_smul hb ((hgr j ⟨q, hqA⟩).2 hq), ?_⟩
      have hib : S.inc b ∈ S.x0 ^ N := by
        rw [Space.x0, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hb
      show S.inc b * ⟨q, hqA⟩ ∈ S.x0 ^ N
      exact Ideal.mul_mem_right _ _ hib
    · rintro x z ⟨x', rfl, hx1, hx2⟩ ⟨z', rfl, hz1, hz2⟩
      exact ⟨x' + z', rfl, Submodule.add_mem _ hx1 hz1, Ideal.add_mem _ hx2 hz2⟩
  have hcA : ∀ {Γ : Type} [TopologicalSpace Γ] (j : ℤ) (f : Γ → S.A), (∀ g, (f g : S.R) ∈ W.part j) →
      AdicCont (maximalIdeal S.R) (fun g => (f g : S.R)) → AdicCont S.x0 f := by
    intro Γ _ j f hf hc N
    obtain ⟨M, hM⟩ := part_filt O ℤ S.R W hz j N
    have hcM := hc M
    rw [IsLocallyConstant.iff_eventually_eq] at hcM ⊢
    intro x
    filter_upwards [hcM x] with y hy
    rw [Ideal.Quotient.eq] at hy ⊢
    obtain ⟨a, ha, -, ha2⟩ := hT N j _ (hM ⟨Submodule.sub_mem _ (hf y) (hf x), hy⟩)
    have hax : f y - f x = a := Subtype.ext (by rw [ha]; rfl)
    rw [hax]
    exact ha2
  have hcB : ∀ {Γ : Type} [TopologicalSpace Γ] (f : Γ → S.B),
      AdicCont (maximalIdeal S.R) (fun g => (f g : S.R)) → AdicCont S.mB f := by
    intro Γ _ f hc N
    obtain ⟨M, hM⟩ := part_filt O ℤ S.R W hz 0 N
    have hcM := hc M
    rw [IsLocallyConstant.iff_eventually_eq] at hcM ⊢
    intro x
    filter_upwards [hcM x] with y hy
    rw [Ideal.Quotient.eq] at hy ⊢
    have hd : ((f y : S.R) - f x) ∈ W.part 0 := (hB _).1 (S.B.sub_mem (f y).2 (f x).2)
    obtain ⟨b, hb, hb2⟩ := hmulB N _ (hmulB N _ (hP N)) _ (hM ⟨hd, hy⟩)
    have hbx : f y - f x = b := Subtype.ext (by rw [hb]; rfl)
    rw [hbx]
    exact hb2
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, fun i => ?_, fun v i => ?_, fun j N => ?_⟩
  · exact hcA (w n i - w n j) (fun g => S.u.r g i j) (fun g => hr g i j) (S.lift.1.1 i j)
  · exact hcA 0 (fun g => (S.u.ψ v i g : S.A)) (fun g => (hB _).1 (S.ψB v i g).2) (S.lift.1.2 v i)
  · exact hcB (fun g => S.aB g i) (S.lift.1.1 i i)
  · exact hcB (S.ψB v i) (S.lift.1.2 v i)
  · obtain ⟨M, hM⟩ := part_filt O ℤ S.R W hz j N
    refine ⟨M, fun a ha hm => ?_⟩
    obtain ⟨b, hb, hb1, -⟩ := hT N j _ (hM ⟨(hgr j a).1 ha, hm⟩)
    have hba : b = a := Subtype.ext hb
    rw [← hba]
    exact hb1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExistsMemStrSNeZeroOfFrameOk
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem lc_of_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] (f : G →* H)
    (hf : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f hf

theorem UpperTheory.exists_mem_strS_ne_zero_of_frameOk :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∃ b ∈ F.strS k, b ≠ 0 := by
  intro l _ k _ _ F C₀ h
  have hχ0 : ∀ g : F.G0, (F.Ψ⁻¹ ^ 2 * F.delK k) g = (F.Ψ g)⁻¹ ^ 2 := fun g => by
    have : F.del g = 1 := g.2
    simp [Frame.delK, this]
  have hχ : ∀ g : F.G0, (((F.Ψ⁻¹ ^ 2 * F.delK k) g : kˣ) : k) = ((F.Ψ g : k))⁻¹ ^ 2 := fun g => by
    rw [hχ0]; simp
  have hc : (F.Ψ⁻¹ ^ 2 * F.delK k) F.c = -1 := by
    apply Units.ext
    simp [Frame.delK, h.Ψ_c, h.del_c]
  obtain ⟨x, x1, x2, x3, x4, g₁, x5⟩ := UpperTheory.smooth_vector_fixed_by_open_subgroup h (F.Ψ⁻¹ ^ 2 * F.delK k) hc (fun v => by
    obtain ⟨s, hs⟩ := h.f3 v
    refine ⟨s, fun e => hs ?_⟩
    have e' := (hχ0 (F.loc0 v s)).symm.trans e
    rw [inv_pow, inv_eq_one] at e'
    exact e') h.f4'
  have x0 : x 1 = 0 := by
    have := x2 1 1
    rw [mul_one, map_one] at this
    simpa using this
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right h.c_sq
  refine ⟨fun g => x g * F.Ψ g, ⟨?_, fun g g' => ?_, fun g => ?_, fun v => ?_⟩, fun e => ?_⟩
  · exact (x1.mul ((lc_of_ker F.Ψ h.Ψ_open).comp Units.val)).comp_continuous continuous_subtype_val
  · have := (F.Ψ g).ne_zero
    simp only [Subgroup.coe_mul, x2, hχ, map_mul, Units.val_mul, smul_eq_mul, Units.val_inv_eq_inv_val]
    field_simp
  · have hs : ((F.star g : F.G0) : F.Γ) = F.c * ((g : F.Γ)⁻¹ * F.c) := by
      rw [← mul_assoc]
      nth_rewrite 2 [← hci]
      rfl
    have h0 := (F.Ψ g).ne_zero
    have e1 := x2 g (g : F.Γ)⁻¹
    rw [mul_inv_cancel, x0, hχ] at e1
    show x (F.star g) * F.Ψ (F.star g) = x g * F.Ψ g
    have hstar : F.Ψ (F.star g) = (F.Ψ g)⁻¹ := by
      rw [hs, map_mul, map_mul, map_inv, h.Ψ_c]
      simp
    rw [hstar, hs, x2, x2, x3, hc, Units.val_inv_eq_inv_val]
    have e2 : x g = -((F.Ψ g : k)⁻¹ ^ 2 * x (g : F.Γ)⁻¹) := by linear_combination -e1
    rw [e2]
    simp only [Units.val_neg, Units.val_one]
    field_simp
    ring
  · obtain ⟨Y, hY⟩ := x4 v
    refine ⟨-Y, fun s => ?_⟩
    have h0 := (F.Ψ (F.loc v s)).ne_zero
    have e : (((F.Ψ⁻¹ ^ 2 * F.delK k) (F.loc v s) : kˣ) : k) = ((F.Ψ (F.loc v s) : k))⁻¹ ^ 2 := hχ (F.loc0 v s)
    show x (F.loc v s) * F.Ψ (F.loc v s) = _
    rw [hY, e, Units.val_inv_eq_inv_val, smul_eq_mul]
    field_simp
    ring
  · exact mul_ne_zero x5 (F.Ψ g₁).ne_zero (congrFun e g₁)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ValSubOneMap
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrMu
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_mu :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C'' : Type) [CommRing C''] [Algebra O C''] [IsCO O C''] (K : Ideal C') (q : C' →ₐ[O] C'') (u : K →ₗ[O] ResidueField O), maximalIdeal C' * K = ⊥ → K ≤ maximalIdeal C' → Function.Surjective q → (∀ y : K, u y = 0 → q y = 0) → ∃ μ : ResidueField O →+ C'', IsSq O μ ∧ (∀ y : K, μ (u y) = q y) ∧ ∀ c, ∃ y : K, μ c = q y := by
  intro O _ _ C' _ _ _ C'' _ _ _ K q u hmK hKm hq hker
  classical
  have hwd : ∀ y y' : K, u y = u y' → q y = q y' := by
    intro y y' h
    have h0 : u (y - y') = 0 := by rw [map_sub, h, sub_self]
    have h1 := hker _ h0
    rw [Submodule.coe_sub, map_sub, sub_eq_zero] at h1
    exact h1
  have hmem : ∀ y : K, q y ∈ maximalIdeal C'' := by
    intro y
    rw [← res_eq_zero_iff O C'', res_map, res_eq_zero_iff]
    exact hKm y.2
  by_cases hu : ∀ y, u y = 0
  · refine ⟨0, ⟨fun a c => by simp, fun c => by simp⟩, fun y => ?_, fun c => ⟨0, by simp⟩⟩
    show (0 : C'') = q y
    exact (hker y (hu y)).symm
  · push_neg at hu
    obtain ⟨y0, hy0⟩ := hu
    have hsurj : Function.Surjective u := by
      intro c
      obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (c * (u y0)⁻¹)
      refine ⟨o • y0, ?_⟩
      rw [map_smul, Algebra.smul_def]
      show residue O o * u y0 = c
      rw [ho, mul_assoc, inv_mul_cancel₀ hy0, mul_one]
    let s := Function.surjInv hsurj
    have hs : ∀ c, u (s c) = c := Function.surjInv_eq hsurj
    let μ : ResidueField O →+ C'' :=
      { toFun := fun c => q (s c)
        map_zero' := by
          show q (s 0 : C') = 0
          rw [hwd (s 0) 0 (by rw [hs, map_zero])]
          simp
        map_add' := by
          intro c d
          show q (s (c + d) : C') = q (s c : C') + q (s d : C')
          rw [hwd (s (c + d)) (s c + s d) (by rw [hs, map_add (f := _), hs, hs]), Submodule.coe_add, map_add (f := _)] }
    have hμ : ∀ c, μ c = q (s c) := fun c => rfl
    refine ⟨μ, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro a c
      obtain ⟨b, rfl⟩ := hq a
      obtain ⟨o, ho⟩ := IsCO.res_surj (O := O) b
      have hby : b * (s c : C') = o • (s c : C') := by
        have hz : (b - algebraMap O C' o) * (s c : C') = 0 := by
          have hin : (b - algebraMap O C' o) * (s c : C') ∈ maximalIdeal C' * K :=
            Ideal.mul_mem_mul ho (s c).2
          rw [hmK] at hin
          simpa using hin
        rw [Algebra.smul_def]
        linear_combination hz
      have hres : res O C' b = algebraMap O (ResidueField O) o := by
        rw [← AlgHom.commutes (res O C') o, ← sub_eq_zero, ← map_sub, res_eq_zero_iff]
        exact ho
      have hw := hwd (s (res O C'' (q b) * c)) (o • s c)
        (by rw [hs, res_map, hres, map_smul, hs, Algebra.smul_def])
      rw [hμ, hμ, hw, Submodule.coe_smul_of_tower, ← hby, map_mul]
    · intro c
      rw [hμ]
      exact hmem _
    · intro y
      rw [hμ]
      exact hwd _ _ (hs _)
    · intro c
      exact ⟨s c, rfl⟩
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] [IsLocalRing O] {C' : Type} [CommRing C'] [Algebra O C'] [IsCO O C']
  {C'' : Type} [CommRing C''] [Algebra O C''] [IsCO O C'']

private theorem mem_max_iff (q : C' →ₐ[O] C'') (x : C') : q x ∈ maximalIdeal C'' ↔ x ∈ maximalIdeal C' := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem adicCont_map {Γ : Type} [TopologicalSpace Γ] (q : C' →ₐ[O] C'') {f : Γ → C'}
    (hf : AdicCont (maximalIdeal C') f) : AdicCont (maximalIdeal C'') fun g => q (f g) := by
  intro N
  have hle : maximalIdeal C' ^ N ≤ (maximalIdeal C'' ^ N).comap (q : C' →+* C'') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    exact (mem_max_iff q y).2 hy
  exact (hf N).comp (Ideal.quotientMap _ (q : C' →+* C'') hle)

private theorem map_sgnAct {m : ℕ} {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A') (s : ℤˣ)
    (g : GL (Fin m) A) :
    GeneralLinearGroup.map f (sgnAct m A s g) = sgnAct m A' s (GeneralLinearGroup.map f g) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [sgnAct_one, sgnAct_one]
  · rw [sgnAct_neg_one, sgnAct_neg_one, map_theta]

private theorem val_sub_one_map {m : ℕ} {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A')
    (g : GL (Fin m) A) (i j : Fin m) :
    (((GeneralLinearGroup.map f g : GL (Fin m) A') : Matrix (Fin m) (Fin m) A') - 1) i j =
      f (((g : Matrix (Fin m) (Fin m) A) - 1) i j) := by
  have e : ((GeneralLinearGroup.map f g : GL (Fin m) A') : Matrix (Fin m) (Fin m) A') - 1 =
      f.mapMatrix ((g : Matrix (Fin m) (Fin m) A) - 1) := by
    rw [map_sub, map_one]
    rfl
  rw [e]
  rfl

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
  {R : Type} [CommRing R] [Algebra O R] {B : Box F n R}

private noncomputable def push (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R) (D : SetLift (p''.comp q) B) :
    SetLift p'' B where
  r s := GeneralLinearGroup.map (q : C' →+* C'') (D.r s)
  r_cont i j := adicCont_map q (D.r_cont i j)
  r_map s := D.r_map s
  g v := GeneralLinearGroup.map (q : C' →+* C'') (D.g v)
  g_map v := D.g_map v
  t v s := GeneralLinearGroup.map (q : C' →+* C'') (D.t v s)
  t_cont v i j := adicCont_map q (D.t_cont v i j)
  t_tri v s i j h := (congrArg q (D.t_tri v s i j h)).trans (map_zero q)
  t_map v s := D.t_map v s

private theorem push_om (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R) (D : SetLift (p''.comp q) B)
    (x : F.Γ × F.Γ) (i j : Fin n) : (push q p'' D).om x i j = q (D.om x i j) := by
  refine Eq.trans ?_ (val_sub_one_map (q : C' →+* C'') _ i j)
  rw [map_mul, map_mul, map_inv, map_sgnAct]
  rfl

private theorem push_a (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R) (D : SetLift (p''.comp q) B)
    (v : F.V) (s : F.Gv v) (i j : Fin n) : (push q p'' D).a v s i j = q (D.a v s i j) := by
  refine Eq.trans ?_ (val_sub_one_map (q : C' →+* C'') _ i j)
  rw [map_mul, map_inv, map_mul, map_mul, map_inv]
  rfl

end SlopeTestRemainingChoices

theorem UpperTheory.V.Fr.pr_obs :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) (B : Box F n R), ρ.Univ O → B.Of ρ → B.Cont (maximalIdeal R) → (ρ.bar O).Good → ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (p : C' →ₐ[O] R) (D : SetLift p B) (u : RingHom.ker p →ₗ[O] ResidueField O), maximalIdeal C' * RingHom.ker p = ⊥ → D.co u ∈ continuousCoboundaries2 F.loc (B.bar O).ad (B.bar O).b → ∀ (C'' : Type) [CommRing C''] [Algebra O C''] [IsCO O C''] (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R), p''.comp q = p → Function.Surjective q → (∀ y : RingHom.ker p, u y = 0 → q y = 0) → ∃ s : R →ₐ[O] C'', p''.comp s = AlgHom.id O R := by
  intro l _ k _ _ F C₀ n hF O _ _ R _ _ _ ρ B hU hOf hC hG C' _ _ _ p D u hsm hco C'' _ _ _ q p'' hpq hq hu
  subst hpq
  have hK : RingHom.ker (p''.comp q) ≤ maximalIdeal C' := fun y hy => by
    rw [← mem_max_iff (p''.comp q), (RingHom.mem_ker).1 hy]
    exact zero_mem _
  obtain ⟨μ, hμ, hμu, hμq⟩ := pr_mu O C' C'' _ q u hsm hK hq hu
  obtain ⟨hom, ha, -, -⟩ := pr_omk hF O C' R (p''.comp q) B D hsm
  obtain ⟨β, Y, hβ, h1, h2⟩ := hco
  have hev : ∀ y ∈ RingHom.ker (p''.comp q), q y = μ (evK _ u y) := fun y hy => by
    rw [evK_of_mem u hy, hμu]
  have hp0 : ∀ c, p'' (μ c) = 0 := fun c => by
    obtain ⟨y, hy⟩ := hμq c
    rw [hy]
    exact y.2
  obtain ⟨B', hB'c, hB'm, -⟩ := pr_correct hF O C'' R p'' B (push q p'' D) μ hμ hp0 β Y (D.co u).2 hβ
    (fun x => by
      rw [← h1]
      ext i j
      rw [push_om, hev _ (hom x i j)]
      rfl)
    (fun v s => by
      ext i j
      rw [push_a, hev _ (ha v s i j)]
      rfl) h2
  have hsm'' : maximalIdeal C'' * RingHom.ker p'' = ⊥ := by
    refine le_bot_iff.1 (Ideal.mul_le.2 fun a ha' b hb => ?_)
    obtain ⟨a, rfl⟩ := hq a
    obtain ⟨b, rfl⟩ := hq b
    have hab : a * b ∈ maximalIdeal C' * RingHom.ker (p''.comp q) :=
      Ideal.mul_mem_mul ((mem_max_iff q a).1 ha') hb
    rw [hsm, Ideal.mem_bot] at hab
    rw [← map_mul, hab, map_zero]
    exact zero_mem _
  obtain ⟨-, ρ', -, hρm, hρc, -, -⟩ := pr_norm hF O C'' R p'' ρ B' hsm'' hG (hB'm ▸ hOf) hB'c
  have hbar : ρ'.bar O = ρ.bar O := by
    have e : (res O C'' : C'' →+* ResidueField O) =
        (res O R : R →+* ResidueField O).comp (p'' : C'' →+* R) :=
      RingHom.ext fun x => (res_map p'' x).symm
    show ρ'.map _ = ρ.map _
    rw [e, ← NRep.map_map, hρm]
  obtain ⟨g, hg, -⟩ := hU.univ C'' ρ' hρc hbar
  obtain ⟨g', -, hg'⟩ := hU.univ R ρ hU.cont rfl
  refine ⟨g, (hg' _ ?_).trans (hg' _ rfl).symm⟩
  show ρ.map ((p'' : C'' →+* R).comp (g : R →+* C'')) = ρ
  rw [← NRep.map_map, hg, hρm]
end
