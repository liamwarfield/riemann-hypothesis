module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExpMemUJ
open Matrix Finset Filter Topology Set

noncomputable section

namespace GlobalTheory.CompanionTheory.DSStabLink

open PI.UpqRep CompanionTheory.D.DSIC

theorem flow_mem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (T : ℝ → (H →L[ℂ] H)) (h0 : ∀ v, T 0 v = v)
    (hadd : ∀ s t v, T (s + t) v = T s (T t v)) (hiso : ∀ t v, ‖T t v‖ = ‖v‖)
    (hder : ∀ w ∈ W, ∃ z ∈ W, HasDerivAt (fun t => T t w) z 0) (u : H) (hu : u ∈ W) :
    T 1 u ∈ W := by
  set Q : H →L[ℂ] H := Wᗮ.starProjection with hQ
  have hQW : ∀ w ∈ W, Q w = 0 := fun w hw => Submodule.starProjection_orthogonal_apply_eq_zero hw
  have hQs : ∀ x, x - Q x ∈ W := fun x => by
    have := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) x
    rwa [Submodule.orthogonal_orthogonal] at this
  have hQn : ∀ x, ‖Q x‖ ≤ ‖x‖ := fun x => Submodule.norm_starProjection_apply_le _ x
  have hcont : Continuous fun t => T t u := by
    rw [continuous_iff_continuousAt]
    intro t
    obtain ⟨z, -, hz⟩ := hder u hu
    have h1 : ContinuousAt (fun s : ℝ => T (s - t) u) t := by
      have h2 : ContinuousAt (fun s : ℝ => s - t) t := by fun_prop
      exact ContinuousAt.comp_of_eq (g := fun t => T t u) hz.continuousAt h2 (by simp)
    have h3 : ContinuousAt (fun s : ℝ => T t (T (s - t) u)) t :=
      (T t).continuous.continuousAt.comp h1
    convert h3 using 2 with s
    rw [← hadd]; simp
  have key : ∀ ⦃x⦄, x ∈ Icc (0 : ℝ) 1 → ‖Q (T x u)‖ ≤ 0 := by
    refine image_le_of_liminf_slope_right_le_deriv_boundary (f := fun t => ‖Q (T t u)‖)
      (B := fun _ => 0) (B' := fun _ => 0) ?_ ?_ continuousOn_const
      (fun x _ => hasDerivWithinAt_const _ _ _) ?_
    · exact ((Q.continuous.comp hcont).norm).continuousOn
    · simp [h0, hQW u hu]
    · intro x _ r hr
      set w := T x u - Q (T x u) with hw
      obtain ⟨z, hzW, hz⟩ := hder w (hQs _)
      have hg : HasDerivAt (fun t => Q (T t w)) 0 0 := by
        have := (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hz
        simpa [hQW z hzW, Function.comp_def] using this
      have hg2 : HasDerivAt (fun s : ℝ => Q (T (s - x) w)) 0 x := by
        have h2 : HasDerivAt (fun s : ℝ => s - x) 1 x := (hasDerivAt_id x).sub_const x
        have := HasDerivAt.scomp_of_eq (g₁ := fun t => Q (T t w)) x hg h2 (by simp)
        simpa [Function.comp_def] using this
      have hsl := (hasDerivAt_iff_tendsto_slope.1 hg2).norm
      rw [norm_zero] at hsl
      have hev : ∀ᶠ s in 𝓝[>] x, ‖slope (fun s : ℝ => Q (T (s - x) w)) x s‖ < r :=
        (hsl.eventually (gt_mem_nhds hr)).filter_mono (nhdsWithin_mono _ fun s hs => ne_of_gt hs)
      refine (hev.and self_mem_nhdsWithin).frequently.mono ?_
      rintro s ⟨hs, hsx⟩
      have hpos : 0 < s - x := sub_pos.2 hsx
      refine lt_of_le_of_lt ?_ hs
      rw [slope_def_field, slope_def_module, norm_smul, sub_self, h0, hQW w (hQs _), sub_zero,
        Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos), div_eq_inv_mul]
      refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hpos).le
      have e : Q (T s u) = Q (T (s - x) w) + Q (T (s - x) (Q (T x u))) := by
        rw [← map_add (f := _), ← map_add (f := _), hw, sub_add_cancel, ← hadd, sub_add_cancel]
      have e2 : ‖Q (T (s - x) (Q (T x u)))‖ ≤ ‖Q (T x u)‖ := (hQn _).trans (hiso _ _).le
      have e3 := norm_add_le (Q (T (s - x) w)) (Q (T (s - x) (Q (T x u))))
      rw [← e] at e3
      linarith
  have h1 := norm_le_zero_iff.1 (key (x := 1) ⟨zero_le_one, le_rfl⟩)
  simpa [h1] using hQs (T 1 u)

theorem deriv_mem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (c : ℝ → H) (z : H) (hc : ∀ t, c t ∈ W) (hz : HasDerivAt c z 0) :
    z ∈ W := by
  set Q : H →L[ℂ] H := Wᗮ.starProjection with hQ
  have hQW : ∀ w ∈ W, Q w = 0 := fun w hw => Submodule.starProjection_orthogonal_apply_eq_zero hw
  have hQs : ∀ x, x - Q x ∈ W := fun x => by
    have := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) x
    rwa [Submodule.orthogonal_orthogonal] at this
  have h1 : HasDerivAt (fun t => Q (c t)) (Q z) 0 :=
    (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hz
  have h2 : (fun t => Q (c t)) = fun _ => 0 := funext fun t => hQW _ (hc t)
  rw [h2] at h1
  have h3 : Q z = 0 := h1.unique (hasDerivAt_const _ _)
  simpa [h3] using hQs z

variable {n : ℕ}

theorem inK_iff (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inK ε X ↔ (∀ c d, ε c ≠ ε d → X c d = 0) ∧ ∀ c d, star (X d c) = -X c d := by
  unfold inK inG Jm
  simp only [← Matrix.ext_iff, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply, Matrix.zero_apply]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : ∀ c d, ε c ≠ ε d → X c d = 0 := by
      intro c d h
      have := h2 c d
      cases hc : ε c <;> cases hd : ε d <;> simp [hc, hd] at h this <;>
        first | linear_combination this / 2 | linear_combination -this / 2
    refine ⟨h3, fun c d => ?_⟩
    have := h1 c d
    by_cases h : ε c = ε d
    · cases hc : ε c <;> cases hd : ε d <;> simp [hc, hd] at h this ⊢ <;>
        first | linear_combination this | linear_combination -this
    · simp [h3 c d h, h3 d c (Ne.symm h)]
  · rintro ⟨h1, h2⟩
    constructor
    · intro c d
      by_cases h : ε c = ε d
      · rw [h2, h]; ring
      · simp [h1 c d h, h1 d c (Ne.symm h)]
    · intro c d
      by_cases h : ε c = ε d
      · rw [h]; ring
      · simp [h1 c d h]

theorem inK_smul (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    inK ε ((t : ℂ) • X) := by
  rw [inK_iff] at hX ⊢
  refine ⟨fun c d h => by simp [hX.1 c d h], fun c d => ?_⟩
  have := hX.2 c d
  simp only [Matrix.smul_apply, smul_eq_mul, star_mul', this]
  simp

theorem exp_mem_K (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε :=
  (Formalism.REAL.maximal_compact_facts n ε).2.2.2.1 _ (inK_smul ε hX t)

theorem exp_mem_UJ (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε :=
  Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t

theorem stabLink : KExp → StabLink := by
  intro hK n ε H _ _ σ S E hσ hS U hU
  constructor
  · intro hst g hg v hv
    obtain ⟨X, hX, rfl⟩ := hK n ε g hg
    have := flow_mem (U.map S.subtype) (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)))
      ?_ ?_ ?_ ?_ v hv
    · simpa using this
    · intro v
      simp [hσ.1.1]
    · intro s t v
      have hc : Commute ((s : ℂ) • X) ((t : ℂ) • X) := ((Commute.refl X).smul_left _).smul_right _
      simp only [Complex.ofReal_add, add_smul]
      rw [Matrix.exp_add_of_commute _ _ hc,
        hσ.1.2 _ (exp_mem_UJ ε hX.1 s) _ (exp_mem_UJ ε hX.1 t)]
      rfl
    · intro t v
      exact hσ.2.1 _ (exp_mem_UJ ε hX.1 t) v
    · rintro _ ⟨w, hw, rfl⟩
      refine ⟨_, ?_, hS.real X hX.1 w⟩
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      by_cases h : ε a = ε b
      · exact Submodule.smul_mem _ _ ⟨_, hst a b h w hw, rfl⟩
      · simp [((inK_iff ε X).1 hX).1 a b h]
  · intro hst a b hab v hv
    have hL : ∀ X, inK ε X → ∑ c, ∑ d, X c d • (E c d v : H) ∈ U.map S.subtype := fun X hX =>
      deriv_mem _ _ _ (fun t => hst _ (exp_mem_K ε hX t) _ ⟨v, hv, rfl⟩) (hS.real X hX.1 v)
    have hs : ∀ (p q : Fin n) (z : ℂ),
        ∑ c, ∑ d, (Matrix.single p q z) c d • (E c d v : H) = z • (E p q v : H) := by
      intro p q z
      simp [Matrix.single_apply, ite_and]
    have hoff : ∀ (p q : Fin n) (z : ℂ), ε p = ε q → ∀ c d, ε c ≠ ε d →
        Matrix.single p q z c d = 0 := by
      intro p q z h c d hcd
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hcd h
    have hZ : ∀ z : ℂ, z • (E a b v : H) - star z • (E b a v : H) ∈ U.map S.subtype := by
      intro z
      have hin : inK ε (Matrix.single a b z - Matrix.single b a (star z)) := by
        rw [inK_iff]
        refine ⟨fun c d h => by simp [hoff a b z hab c d h, hoff b a _ hab.symm c d h], fun c d => ?_⟩
        simp only [Matrix.sub_apply, Matrix.single_apply, star_sub, apply_ite star, star_star,
          star_zero, neg_sub, and_comm]
      have := hL _ hin
      simpa only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, hs] using this
    have h1 := hZ 1
    have h2 := hZ Complex.I
    have h3 := Submodule.add_mem _ (Submodule.smul_mem _ (1 / 2 : ℂ) h1)
      (Submodule.smul_mem _ (-Complex.I / 2 : ℂ) h2)
    have e : (1 / 2 : ℂ) • ((1 : ℂ) • (E a b v : H) - star (1 : ℂ) • (E b a v : H)) +
        (-Complex.I / 2 : ℂ) • (Complex.I • (E a b v : H) - star Complex.I • (E b a v : H)) =
        (E a b v : H) := by
      simp only [star_one, Complex.star_def, Complex.conj_I]
      match_scalars
      · linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
      · linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
    rw [e] at h3
    obtain ⟨y, hy, hye⟩ := h3
    have : y = E a b v := Subtype.ext hye
    exact this ▸ hy

end GlobalTheory.CompanionTheory.DSStabLink
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BlkBijective
open Finset Equiv

noncomputable section

namespace GlobalTheory.CompanionTheory.CapelliBlocks

open Formalism.REAL CompanionTheory.D.DSIC

theorem qminor_equiv {A : Type} [Ring A] [Algebra ℂ A] {m n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (τ : Fin m ≃ Fin n) (u : ℂ) : qminor E τ τ u = qdet E u := by
  obtain rfl : m = n := Fin.equiv_iff_eq.mp ⟨τ⟩
  have hr := qSkewRow A m m E id (τ : Fin m → Fin m) τ u
  have hc := qSkewCol A m m E hE id id τ u
  simp only [Function.id_comp] at hr hc
  rw [hr, hc, ← mul_assoc, ← Int.cast_mul, qdet]
  have : ((Perm.sign τ : ℤˣ) : ℤ) * (Perm.sign τ : ℤˣ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  rw [this, Int.cast_one, one_mul]

theorem qminor_sum {A : Type} [Ring A] [Algebra ℂ A] {n q p : ℕ} (E : Fin n → Fin n → A)
    (r : Fin q ⊕ Fin p → Fin n) (u : ℂ) :
    qminor E (r ∘ finSumFinEquiv.symm) (r ∘ finSumFinEquiv.symm) u =
      ∑ σ : Perm (Fin q ⊕ Fin p), ((Perm.sign σ : ℤ) : A) *
        ((List.ofFn fun k : Fin q => Tm E (u - (k : ℂ)) (r (σ (Sum.inl k))) (r (Sum.inl k))).prod *
         (List.ofFn fun k : Fin p => Tm E (u - (q : ℂ) - (k : ℂ)) (r (σ (Sum.inr k))) (r (Sum.inr k))).prod) := by
  rw [qminor, ← (finSumFinEquiv (m := q) (n := p)).permCongr.sum_comp]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Perm.sign_permCongr, List.ofFn_add, List.prod_append]
  congr 4
  · funext k
    have : (Fin.castLE (Nat.le_add_right q p) k) = Fin.castAdd p k := rfl
    simp [this]
  · funext k
    simp [sub_sub]

theorem prod_mem {V : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V) :
    ∀ l : List (Module.End ℂ V), (∀ T ∈ l, ∀ v ∈ P, T v ∈ P) → (∃ T ∈ l, ∀ v, T v ∈ P) → ∀ v, l.prod v ∈ P := by
  intro l
  induction l with
  | nil =>
    intro _ h _
    simp at h
  | cons T l ih =>
    intro h1 h2 v
    rw [List.prod_cons, Module.End.mul_apply]
    obtain ⟨S, hS, hS'⟩ := h2
    rcases List.mem_cons.mp hS with rfl | hS
    · exact hS' _
    · exact h1 T List.mem_cons_self _
        (ih (fun T hT => h1 T (List.mem_cons_of_mem _ hT)) ⟨S, hS, hS'⟩ v)

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def pplus (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ V where
  carrier := {v | ∃ w : NC ε → V, v = ∑ i : NC ε, E i.1.1 i.1.2 (w i)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩
    exact ⟨w + w', by simp [Finset.sum_add_distrib]⟩
  smul_mem' := by
    rintro c _ ⟨w, rfl⟩
    exact ⟨c • w, by simp [Finset.smul_sum]⟩

theorem mem_pplus (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) {a b : Fin n}
    (ha : ε a = true) (hb : ε b = false) (v : V) : E a b v ∈ pplus ε E := by
  classical
  refine ⟨Pi.single (⟨(a, b), ha, hb⟩ : NC ε) v, ?_⟩
  rw [Finset.sum_eq_single (⟨(a, b), ha, hb⟩ : NC ε)]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · simp

theorem stab_pplus (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) {c d : Fin n}
    (hc : ε c = false) (hd : ε d = false) : ∀ v ∈ pplus ε E, E c d v ∈ pplus ε E := by
  rintro _ ⟨w, rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨⟨a, b⟩, ha, hb⟩ := i
  dsimp only at ha hb ⊢
  generalize w _ = x
  have h := LinearMap.congr_fun (hE c d a b) x
  have hda : d ≠ a := by rintro rfl; simp [ha] at hd
  rw [if_neg hda, zero_sub, LinearMap.sub_apply, sub_eq_iff_eq_add, LinearMap.neg_apply,
    Module.End.mul_apply, Module.End.mul_apply] at h
  rw [h]
  refine Submodule.add_mem _ (Submodule.neg_mem _ ?_) (mem_pplus ε E ha hb _)
  split_ifs
  · exact mem_pplus ε E ha hd _
  · simp

theorem Tm_mem (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) {a b : Fin n}
    (ha : ε a = true) (hb : ε b = false) (u : ℂ) (v : V) : Tm E u a b v ∈ pplus ε E := by
  have hab : a ≠ b := by rintro rfl; simp [ha] at hb
  rw [Tm, if_neg hab, zero_add]
  exact mem_pplus ε E ha hb v

theorem Tm_stab (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (a : Fin n) {b : Fin n}
    (hb : ε b = false) (u : ℂ) : ∀ v ∈ pplus ε E, Tm E u a b v ∈ pplus ε E := by
  intro v hv
  cases ha : ε a
  · rw [Tm, LinearMap.add_apply]
    refine Submodule.add_mem _ ?_ (stab_pplus ε E hE ha hb v hv)
    split_ifs
    · rw [Module.algebraMap_end_apply]
      exact Submodule.smul_mem _ _ hv
    · simp
  · exact Tm_mem ε E ha hb u v

theorem block_mem (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) {q p : ℕ}
    (r : Fin q ⊕ Fin p → Fin n) (hl : ∀ k, ε (r (Sum.inl k)) = false) (hr : ∀ k, ε (r (Sum.inr k)) = true)
    (u : ℂ) (v : V) :
    qminor E (r ∘ finSumFinEquiv.symm) (r ∘ finSumFinEquiv.symm) u v -
      (qminor E (r ∘ Sum.inl) (r ∘ Sum.inl) u * qminor E (r ∘ Sum.inr) (r ∘ Sum.inr) (u - (q : ℂ))) v ∈
        pplus ε E := by
  classical
  rw [qminor_sum]
  set f : Perm (Fin q ⊕ Fin p) → Module.End ℂ V := fun σ => ((Perm.sign σ : ℤ) : Module.End ℂ V) *
        ((List.ofFn fun k : Fin q => Tm E (u - (k : ℂ)) (r (σ (Sum.inl k))) (r (Sum.inl k))).prod *
         (List.ofFn fun k : Fin p => Tm E (u - (q : ℂ) - (k : ℂ)) (r (σ (Sum.inr k))) (r (Sum.inr k))).prod)
    with hf
  set s : Finset (Perm (Fin q ⊕ Fin p)) :=
    univ.image fun σ : Perm (Fin q) × Perm (Fin p) => Perm.sumCongrHom _ _ σ with hs
  have h1 : qminor E (r ∘ Sum.inl) (r ∘ Sum.inl) u * qminor E (r ∘ Sum.inr) (r ∘ Sum.inr) (u - (q : ℂ)) =
      ∑ σ ∈ s, f σ := by
    rw [hs, Finset.sum_image (fun x _ y _ h => Perm.sumCongrHom_injective h), qminor, qminor,
      Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    simp only [hf, Perm.sumCongrHom_apply, Perm.sign_sumCongr, Units.val_mul, Int.cast_mul,
      Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr, Function.comp_apply, mul_assoc]
    congr 1
    rw [← mul_assoc, ← (Int.cast_commute _ _).eq, mul_assoc]
  rw [h1, ← Finset.sum_add_sum_compl s, LinearMap.add_apply, add_sub_cancel_left, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun σ hσ => ?_
  have h2 : ∃ k j, σ (Sum.inl k) = Sum.inr j := by
    by_contra hcon
    push Not at hcon
    apply Finset.mem_compl.mp hσ
    have : σ ∈ (Perm.sumCongrHom (Fin q) (Fin p)).range := by
      apply Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
      rintro _ ⟨k, rfl⟩
      cases h : σ (Sum.inl k) with
      | inl j => exact ⟨j, rfl⟩
      | inr j => exact absurd h (hcon k j)
    obtain ⟨τ, hτ⟩ := this
    exact Finset.mem_image.mpr ⟨τ, Finset.mem_univ _, hτ⟩
  obtain ⟨k, j, hkj⟩ := h2
  simp only [hf, Module.End.mul_apply, Module.End.intCast_apply]
  refine Submodule.smul_of_tower_mem _ _ (prod_mem _ _ ?_ ?_ _)
  · intro T hT
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hT
    exact Tm_stab ε E hE _ (hl i) _
  · refine ⟨_, List.mem_ofFn.mpr ⟨k, rfl⟩, fun v => Tm_mem ε E ?_ (hl k) _ v⟩
    rw [hkj]
    exact hr j

theorem blk_val (ε : Fin n → Bool) (s : Bool) (k : Fin (nb ε s)) : ε (blk ε s k) = s := by
  have := Finset.orderEmbOfFin_mem (univ.filter fun a => ε a = s) rfl k
  exact (Finset.mem_filter.mp this).2

theorem blk_bijective (ε : Fin n → Bool) : Function.Bijective (Sum.elim (blk ε false) (blk ε true)) := by
  have hinj : ∀ s, Function.Injective (blk ε s) := fun s =>
    ((univ.filter fun a => ε a = s).orderEmbOfFin rfl).injective
  have hsur : ∀ a, ∃ k, blk ε (ε a) k = a := fun a => by
    have : a ∈ Set.range ((univ.filter fun b => ε b = ε a).orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      simp
    exact this
  constructor
  · refine Function.Injective.sumElim (hinj false) (hinj true) fun a b h => ?_
    have h1 := blk_val ε false a
    rw [h, blk_val ε true b] at h1
    exact absurd h1 (by simp)
  · intro a
    have h := hsur a
    cases ha : ε a
    · rw [ha] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨Sum.inl k, hk⟩
    · rw [ha] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨Sum.inr k, hk⟩

theorem co0 : CompanionTheory.D.DSIC.CapelliDeterminantBlockProduct := by
  intro n ε V _ _ E hE u v
  have h := block_mem ε E hE (Sum.elim (blk ε false) (blk ε true)) (blk_val ε false) (blk_val ε true) u v
  have h2 := qminor_equiv E hE (finSumFinEquiv.symm.trans (Equiv.ofBijective _ (blk_bijective ε))) u
  rw [← h2]
  exact h

end GlobalTheory.CompanionTheory.CapelliBlocks
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CarImpFrel
open Finset CompanionTheory.D.DSIC

noncomputable section

namespace GlobalTheory.CompanionTheory.DSICFRel

def bil {ι A : Type} [Fintype ι] [Ring A] [Algebra ℂ A] (c a : ι → A) (m : ι → ι → ℂ) : A :=
  ∑ i, ∑ j, m i j • (c i * a j)

theorem pair_comm {ι A : Type} [DecidableEq ι] [Ring A] (c a : ι → A)
    (haa : ∀ i j, a i * a j + a j * a i = 0) (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (i j k l : ι) :
    (c i * a j) * (c k * a l) - (c k * a l) * (c i * a j) =
      (if j = k then c i * a l else 0) - (if l = i then c k * a j else 0) := by
  have h1 : a j * c k = (if j = k then 1 else 0) - c k * a j := eq_sub_of_add_eq (hac j k)
  have h2 : a l * c i = (if l = i then 1 else 0) - c i * a l := eq_sub_of_add_eq (hac l i)
  have h3 : c k * c i = - (c i * c k) := eq_neg_of_add_eq_zero_left (hcc k i)
  have h4 : a l * a j = - (a j * a l) := eq_neg_of_add_eq_zero_left (haa l j)
  have e1 : (c i * a j) * (c k * a l) = (if j = k then c i * a l else 0) - (c i * c k) * (a j * a l) := by
    rw [mul_assoc, ← mul_assoc (a j), h1]
    split_ifs <;> noncomm_ring
  have e2 : (c k * a l) * (c i * a j) = (if l = i then c k * a j else 0) - (c k * c i) * (a l * a j) := by
    rw [mul_assoc, ← mul_assoc (a l), h2]
    split_ifs <;> noncomm_ring
  rw [e1, e2, h3, h4]
  noncomm_ring

theorem bil_comm {ι A : Type} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A] (c a : ι → A)
    (haa : ∀ i j, a i * a j + a j * a i = 0) (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (m m' : ι → ι → ℂ) :
    bil c a m * bil c a m' - bil c a m' * bil c a m =
      bil c a (fun i l => ∑ k, m i k * m' k l - ∑ k, m' i k * m k l) := by
  have e1 : bil c a m * bil c a m' =
      ∑ i, ∑ j, ∑ k, ∑ l, (m i j * m' k l) • ((c i * a j) * (c k * a l)) := by
    unfold bil
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm]
  have e2 : bil c a m' * bil c a m =
      ∑ i, ∑ j, ∑ k, ∑ l, (m i j * m' k l) • ((c k * a l) * (c i * a j)) := by
    unfold bil
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm, mul_comm (m' k l)]
  have e3 : ∑ i, ∑ j, ∑ k, ∑ l, (m i j * m' k l) • (if j = k then c i * a l else 0) =
      ∑ i, ∑ l, (∑ k, m i k * m' k l) • (c i * a l) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm (f := fun l k => (m i k * m' k l) • (c i * a l))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    simp
  have e4 : ∑ i, ∑ j, ∑ k, ∑ l, (m i j * m' k l) • (if l = i then c k * a j else 0) =
      ∑ i, ∑ l, (∑ k, m' i k * m k l) • (c i * a l) := by
    have : ∀ i j k, ∑ l, (m i j * m' k l) • (if l = i then c k * a j else 0) =
        (m' k i * m i j) • (c k * a j) := by
      intro i j k
      simp [mul_comm]
    simp only [this, Finset.sum_smul]
    calc ∑ i, ∑ j, ∑ k, (m' k i * m i j) • (c k * a j)
        = ∑ j, ∑ i, ∑ k, (m' k i * m i j) • (c k * a j) := Finset.sum_comm
      _ = ∑ j, ∑ k, ∑ i, (m' k i * m i j) • (c k * a j) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [e1, e2]
  simp only [← Finset.sum_sub_distrib, ← smul_sub, pair_comm c a haa hcc hac]
  simp only [smul_sub, Finset.sum_sub_distrib, e3, e4, bil, sub_smul]

variable {n : ℕ}

def dl (x y : Fin n) : ℂ := if x = y then 1 else 0

theorem dl_comm (x y : Fin n) : dl x y = dl y x := by
  simp only [dl, eq_comm]

def mm (c d : Fin n) (x y : Fin n × Fin n) : ℂ :=
  dl x.1 c * dl y.1 d * dl x.2 y.2 - dl x.2 d * dl y.2 c * dl x.1 y.1

theorem gop_eq (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (c d : Fin n) :
    (Gop ε c d : Module.End ℂ (Ch ε V)) = bil cre ann (fun i j : NC ε => mm c d i.1 j.1) := by
  unfold Gop bil
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [mm, dl, ite_and, mul_ite, mul_one, mul_zero]
  split_ifs <;> simp_all

theorem sum_pt (ε : Fin n → Bool) (x y : Fin n) (hx : ε x = true) (hy : ε y = false)
    (f : Fin n × Fin n → ℂ) : ∑ k : NC ε, dl k.1.1 x * dl k.1.2 y * f k.1 = f (x, y) := by
  rw [Finset.sum_eq_single (⟨(x, y), hx, hy⟩ : NC ε)]
  · simp [dl]
  · rintro ⟨⟨u, v⟩, h⟩ _ hne
    by_cases h1 : u = x
    · by_cases h2 : v = y
      · subst h1 h2; exact absurd rfl hne
      · simp [dl, h2]
    · simp [dl, h1]
  · simp

theorem sum_mm (ε : Fin n → Bool) (a b : Fin n) (hab : ε a = ε b) (i : NC ε) (f : Fin n × Fin n → ℂ) :
    ∑ k : NC ε, mm a b i.1 k.1 * f k.1 = dl i.1.1 a * f (b, i.1.2) - dl i.1.2 b * f (i.1.1, a) := by
  have e : ∀ k : NC ε, mm a b i.1 k.1 * f k.1 =
      dl i.1.1 a * (dl k.1.1 b * dl k.1.2 i.1.2 * f k.1) - dl i.1.2 b * (dl k.1.1 i.1.1 * dl k.1.2 a * f k.1) := by
    intro k
    rw [mm, dl_comm i.1.2 k.1.2, dl_comm i.1.1 k.1.1]; ring
  simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  · by_cases h : i.1.1 = a
    · rw [sum_pt ε b i.1.2 (by rw [← hab, ← h]; exact i.2.1) i.2.2]
    · simp [dl, h]
  · by_cases h : i.1.2 = b
    · rw [sum_pt ε i.1.1 a i.2.1 (by rw [hab, ← h]; exact i.2.2)]
    · simp [dl, h]

theorem gop_rel (h : CAR) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] :
    KRel ε (Gop ε : Fin n → Fin n → Module.End ℂ (Ch ε V)) := by
  intro a b c d hab hcd
  have hr : ∀ (x y : Fin n) (T : Module.End ℂ (Ch ε V)), (if x = y then T else 0) = dl x y • T := by
    intro x y T; unfold dl; split_ifs <;> simp
  simp only [gop_eq, hr]
  rw [bil_comm cre ann (fun i j => (h n ε V i j).1) (fun i j => (h n ε V i j).2.1)
    (fun i j => by convert (h n ε V i j).2.2)]
  simp only [bil, Finset.smul_sum, ← Finset.sum_sub_distrib, smul_smul, ← sub_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [Finset.sum_sub_distrib, sum_mm ε a b hab i (fun k => mm c d k j.1), sum_mm ε c d hcd i (fun k => mm a b k j.1)]
  simp only [mm]
  rw [dl_comm b j.1.1, dl_comm d j.1.1, dl_comm a j.1.2, dl_comm c j.1.2, dl_comm a d, dl_comm c b]
  ring

section

variable {ε : Fin n → Bool} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem lift_gop (T : Module.End ℂ V) (c d : Fin n) :
    Commute (lift ε T : Module.End ℂ (Ch ε V)) (Gop ε c d) := by
  have ha : ∀ i : NC ε, Commute (lift ε T : Module.End ℂ (Ch ε V)) (ann i) := by
    intro i
    refine LinearMap.ext fun x => funext fun A => ?_
    by_cases h : i ∈ A <;> simp [ann, h]
  have hc : ∀ i : NC ε, Commute (lift ε T : Module.End ℂ (Ch ε V)) (cre i) := by
    intro i
    refine LinearMap.ext fun x => funext fun A => ?_
    by_cases h : i ∈ A <;> simp [cre, h]
  unfold Gop
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ =>
    ((hc i).mul_right (ha j)).smul_right _

theorem lift_rel (E : Fin n → Fin n → Module.End ℂ V) (hE : KRel ε E) :
    KRel ε (fun c d => (lift ε (E c d) : Module.End ℂ (Ch ε V))) := by
  intro a b c d hab hcd
  refine LinearMap.ext fun x => funext fun A => ?_
  have := LinearMap.congr_fun (hE a b c d hab hcd) (x A)
  split_ifs at this ⊢ <;> simpa using this

end

theorem add_rel {A : Type} [Ring A] (ε : Fin n → Bool) (L G : Fin n → Fin n → A) (hL : KRel ε L) (hG : KRel ε G)
    (hc : ∀ a b c d, Commute (L a b) (G c d)) : KRel ε (fun c d => L c d + G c d) := by
  intro a b c d hab hcd
  have h1 := hL a b c d hab hcd
  have h2 := hG a b c d hab hcd
  have h3 := (hc a b c d).eq
  have h4 := (hc c d a b).eq
  have : (L a b + G a b) * (L c d + G c d) - (L c d + G c d) * (L a b + G a b) =
      (L a b * L c d - L c d * L a b) + (G a b * G c d - G c d * G a b) := by
    simp only [mul_add, add_mul, h3, h4]; abel
  simp only []
  rw [this, h1, h2]
  split_ifs <;> abel

theorem neg_rel {A : Type} [Ring A] (ε : Fin n → Bool) (G : Fin n → Fin n → A) (hG : KRel ε G) :
    KRel ε (fun c d => -G d c) := by
  intro a b c d hab hcd
  have h := hG b a d c hab.symm hcd.symm
  simp only [neg_mul_neg]
  rw [h]
  simp only [eq_comm (a := a) (b := d), eq_comm (a := c) (b := b)]
  split_ifs <;> abel

theorem frel_of_car (h : CAR) : FRel := by
  intro n ε V _ _ E hE
  refine ⟨add_rel ε _ _ (lift_rel E hE) (gop_rel h ε V) fun a b c d => lift_gop _ c d, ?_⟩
  have := add_rel ε _ _ (lift_rel E hE) (neg_rel ε _ (gop_rel h ε V)) fun a b c d => (lift_gop _ d c).neg_right
  simp only [← sub_eq_add_neg] at this
  exact this

theorem car_imp_frel : CompanionTheory.D.DSIC.CAR → CompanionTheory.D.DSIC.FRel := frel_of_car

end GlobalTheory.CompanionTheory.DSICFRel
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasDerivAtExpMul
open Matrix Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.WtLinkPf

open PI.UpqRep

variable {n : ℕ}

def tor (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))

lemma tor_add (θ η : Fin n → ℝ) : tor (θ + η) = tor θ * tor η := by
  unfold tor
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply]
  push_cast
  ring

lemma tor_zero : tor (0 : Fin n → ℝ) = 1 := by
  unfold tor
  simp

lemma star_exp_mul (x : ℝ) : star (Complex.exp ((x : ℂ) * Complex.I)) * Complex.exp ((x : ℂ) * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp

lemma tor_mem_UJ (ε : Fin n → Bool) (θ : Fin n → ℝ) : tor θ ∈ UJset ε := by
  show (tor θ).conjTranspose * PI.UpqRep.Jm ε * tor θ = PI.UpqRep.Jm ε
  unfold tor PI.UpqRep.Jm
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  rw [Pi.star_apply, mul_right_comm, star_exp_mul, one_mul]

lemma tor_mem_K (ε : Fin n → Bool) (θ : Fin n → ℝ) : tor θ ∈ Kset ε := by
  show tor θ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ tor θ * PI.UpqRep.Jm ε = PI.UpqRep.Jm ε * tor θ
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    unfold tor
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      show (1 : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun _ => 1) from Matrix.diagonal_one.symm]
    congr 1
    funext a
    rw [Pi.star_apply]
    exact star_exp_mul (θ a)
  · unfold tor PI.UpqRep.Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

lemma diag_inG (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    inG ε (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  show (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I).conjTranspose * PI.UpqRep.Jm ε +
      PI.UpqRep.Jm ε * Matrix.diagonal (fun a => (θ a : ℂ) * Complex.I) = 0
  unfold PI.UpqRep.Jm
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_add, ← Matrix.diagonal_zero]
  congr 1
  funext a
  rw [Pi.star_apply, Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

lemma exp_diag (θ : Fin n → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) = tor (t • θ) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  unfold tor
  congr 1
  funext a
  rw [← Complex.exp_eq_exp_ℂ]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma deriv_zero {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ S} (h : CompanionTheory.D.DSIC.IsSmMod ε σ S E) (θ : Fin n → ℝ) (v : S) :
    HasDerivAt (fun t : ℝ => σ (tor (t • θ)) v) (∑ a, ((θ a : ℂ) * Complex.I) • (E a a v : H)) 0 := by
  have h1 := h.real (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) (diag_inG ε θ) v
  simp only [exp_diag] at h1
  convert h1 using 1
  simp [Matrix.diagonal_apply]

lemma hasDerivAt_exp_mul (c : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * c)) (Complex.exp ((s : ℂ) * c) * c) s := by
  have := ((hasDerivAt_id s).ofReal_comp.mul_const c).cexp
  simpa using this

lemma one_param (φ : ℝ → (H →L[ℂ] H)) (hadd : ∀ s t, φ (s + t) = φ s * φ t) (h0 : φ 0 = 1) (v : H) (c : ℂ)
    (hd : HasDerivAt (fun t => φ t v) (c • v) 0) : φ 1 v = Complex.exp c • v := by
  have hder : ∀ s : ℝ, HasDerivAt (fun t => φ t v) (c • φ s v) s := by
    intro s
    have h1 : HasDerivAt (fun u => φ s (φ u v)) (φ s (c • v)) 0 := by
      have := ((φ s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt (fun u => φ s (φ u v)) (φ s (c • v)) (s - s) := by
      rwa [sub_self]
    have h3 := HasDerivAt.comp_sub_const s s h2
    rw [map_smul] at h3
    convert h3 using 1
    funext t
    show φ t v = φ s (φ (t - s) v)
    rw [← ContinuousLinearMap.mul_apply, ← hadd, show s + (t - s) = t by ring]
  have hg : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * -c) • φ t v) 0 s := by
    intro s
    have := (hasDerivAt_exp_mul (-c) s).smul (hder s)
    convert (preTransparency := .reducible) this using 1
    · funext t
      rfl
    · rw [smul_smul, ← add_smul]
      simp
  have hdiff : Differentiable ℝ (fun t : ℝ => Complex.exp ((t : ℂ) * -c) • φ t v) :=
    fun s => (hg s).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun s => (hg s).deriv) 1 0
  have hfinal : Complex.exp (-c) • φ 1 v = v := by
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, Complex.exp_zero, one_smul, h0,
      ContinuousLinearMap.one_apply] at hconst
    exact hconst
  calc φ 1 v = Complex.exp c • (Complex.exp (-c) • φ 1 v) := by
        rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
    _ = Complex.exp c • v := by rw [hfinal]

end

theorem wtLink : CompanionTheory.D.DSIC.WtLink := by
  intro n ε H _ _ σ S E hrep h μ v
  have hG : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, σ (a * b) = σ a * σ b := by
    intro a ha b hb
    rw [ContinuousLinearMap.mul_def]
    exact hrep.1.2 a ha b hb
  have h1 : σ 1 = 1 := hrep.1.1
  constructor
  · intro hw θ _
    have hw' : ∀ a, E a a v = (μ a : ℂ) • v := hw
    let φ : ℝ → (H →L[ℂ] H) := fun t => σ (tor (t • θ))
    have hadd : ∀ s t, φ (s + t) = φ s * φ t := by
      intro s t
      show σ (tor ((s + t) • θ)) = σ (tor (s • θ)) * σ (tor (t • θ))
      rw [add_smul, tor_add]
      exact hG _ (tor_mem_UJ ε _) _ (tor_mem_UJ ε _)
    have hz : φ 0 = 1 := by
      show σ (tor ((0 : ℝ) • θ)) = 1
      rw [zero_smul, tor_zero]
      exact h1
    have hd : HasDerivAt (fun t => φ t (v : H))
        ((((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • (v : H)) 0 := by
      have := deriv_zero h θ v
      convert this using 1
      simp only [hw', Submodule.coe_smul, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    have key := one_param φ hadd hz (v : H) _ hd
    show σ (tor θ) (v : H) = _
    rw [show tor θ = tor ((1 : ℝ) • θ) by rw [one_smul]]
    exact key
  · intro hK a
    apply Subtype.ext
    rw [Submodule.coe_smul]
    let θ : Fin n → ℝ := Pi.single a 1
    have hf : (fun t : ℝ => σ (tor (t • θ)) (v : H)) =
        fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H) := by
      funext t
      have ht := hK (t • θ) (tor_mem_K ε _)
      rw [show tor (t • θ) = Matrix.diagonal (fun b => Complex.exp ((((t • θ) b : ℝ) : ℂ) * Complex.I)) from rfl, ht]
      congr 2
      simp [θ, Pi.single_apply]
      try (push_cast; ring)
    have d1 := deriv_zero h θ v
    rw [hf] at d1
    have d2 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H))
        (((μ a : ℂ) * Complex.I) • (v : H)) 0 := by
      have := (hasDerivAt_exp_mul ((μ a : ℂ) * Complex.I) 0).smul_const (v : H)
      simpa using this
    have hu := d1.unique d2
    have hsum : ∑ b, ((θ b : ℂ) * Complex.I) • (E b b v : H) = Complex.I • (E a a v : H) := by
      rw [Finset.sum_eq_single a]
      · simp [θ]
      · intro b _ hb
        simp [θ, Pi.single_apply, hb]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    rw [hsum] at hu
    calc (E a a v : H) = (-Complex.I * Complex.I) • (E a a v : H) := by
          rw [show -Complex.I * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul]
      _ = (-Complex.I) • (Complex.I • (E a a v : H)) := by rw [smul_smul]
      _ = (-Complex.I) • (((μ a : ℂ) * Complex.I) • (v : H)) := by rw [hu]
      _ = (μ a : ℂ) • (v : H) := by
          rw [smul_smul]
          congr 1
          rw [show -Complex.I * ((μ a : ℂ) * Complex.I) = (μ a : ℂ) * -(Complex.I * Complex.I) by ring,
            Complex.I_mul_I, neg_neg, mul_one]

end GlobalTheory.CompanionTheory.WtLinkPf
end
end
