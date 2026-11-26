module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Descend

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.GspLift
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lc_mat {S Q : Type} [TopologicalSpace S] {f : S → M4 Q}
    (h : ∀ i j, IsLocallyConstant fun s => f s i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have : ∀ᶠ t in nhds s, ∀ i j, f t i j = f s i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq s
  exact this.mono fun t ht => Matrix.ext ht

private def corr {A : Type} [CommRing A] (c n : A) (y : M4 A) : M4 A := y * (1 - c • (adj y * y - n • 1))

private theorem corr_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (c n : A) (y : M4 A) :
    (corr c n y).map f = corr (f c) (f n) (y.map f) := by
  obtain ⟨-, -, -, -, -, hm, -⟩ := grp A
  rw [corr, corr, hm, ← Matrix.map_mul, Matrix.map_mul]
  generalize adj y * y = w
  congr 1
  ext i j
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

private theorem corr_gsp {A : Type} [CommRing A] (c n : A) (y : M4 A) (hc : 2 * c * n = 1)
    (hE : (adj y * y - n • 1) * (adj y * y - n • 1) = 0) : IsGSp n (corr c n y) := by
  obtain ⟨hmul, hadj, hadd, hsm, h1, -⟩ := grp A
  unfold IsGSp corr
  obtain ⟨E, hE'⟩ : ∃ E, E = adj y * y - n • 1 := ⟨_, rfl⟩
  have a1 : adj E = E := by
    rw [hE', sub_eq_add_neg, ← neg_smul, hadd, hsm, h1, hmul, hadj]
  have a2 : adj y * y = E + n • 1 := by rw [hE', sub_add_cancel]
  rw [← hE'] at hE ⊢
  have a3 : adj (1 - c • E) = 1 - c • E := by
    rw [sub_eq_add_neg, ← neg_smul, hadd, hsm, h1, a1]
  rw [hmul, a3, mul_assoc, ← mul_assoc (adj y), a2]
  simp only [mul_sub, sub_mul, add_mul, mul_add, mul_smul_comm, smul_mul_assoc, hE, one_mul, mul_one, smul_zero,
    smul_add, smul_sub, smul_smul, zero_add, sub_zero]
  have : E = (2 * c * n) • E := by rw [hc, one_smul]
  linear_combination (norm := module) this

private theorem up_mul {A : Type} [CommRing A] {X Y : M4 A} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases e : k < i
  · rw [hX i k e, zero_mul]
  · rw [hY k j (lt_of_lt_of_le h (not_lt.1 e)), mul_zero]

private theorem corr_up {A : Type} [CommRing A] (c n : A) {y : M4 A} (hy : IsUp y) : IsUp (corr c n y) := by
  have a : IsUp (adj y) := fun i j h => by
    rw [adj_apply, hy _ _ (Fin.rev_lt_rev.2 h), smul_zero]
  refine up_mul hy fun i j h => ?_
  simp [up_mul a hy i j h, Matrix.one_apply_ne h.ne']

theorem UpperTheory.V.Ws.X1.gspLift :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ], IsUnit (2 : Λ) → ∀ {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (S : Type) [TopologicalSpace S] (ν : S → Λˣ) (x : S → M4 R), AdicCont (maximalIdeal Λ) (fun s => (ν s : Λ)) → (∀ i j, AdicCont (maximalIdeal R) fun s => x s i j) → (∀ s, IsGSp (algebraMap Λ R (ν s)) (x s)) → ∃ y : S → M4 A, (∀ i j, AdicCont (maximalIdeal A) fun s => y s i j) ∧ (∀ s, IsGSp (algebraMap Λ A (ν s)) (y s)) ∧ (∀ s, (y s).map p = x s) ∧ ((∀ s, IsUp (x s)) → ∀ s, IsUp (y s)) := by
  intro Λ _ _ _ _ h2 A R _ _ _ _ _ _ p hp hs S _ ν x hν hx hg
  classical
  choose z z1 z2 using fun i j => (UpperTheory.V.Ws.X1.contLift p hp hs).1 S (fun s => x s i j) (hx i j)
  let y0 : S → M4 A := fun s => Matrix.of fun i j => if ∀ t, x t i j = 0 then 0 else z i j s
  have b0 : ∀ i j, AdicCont (maximalIdeal A) fun s => y0 s i j := fun i j => by
    by_cases e : ∀ t, x t i j = 0
    · simp only [y0, Matrix.of_apply, if_pos e]
      exact fun _ => IsLocallyConstant.const _
    · simp only [y0, Matrix.of_apply, if_neg e]
      exact z1 i j
  have b1 : ∀ s, (y0 s).map p = x s := fun s => by
    ext i j
    by_cases e : ∀ t, x t i j = 0
    · simp only [y0, Matrix.map_apply, Matrix.of_apply, if_pos e, map_zero, e s]
    · simp only [y0, Matrix.map_apply, Matrix.of_apply, if_neg e, z2]
  obtain ⟨u, hu⟩ := h2.exists_right_inv
  have hk : ∀ a b : A, p a = 0 → p b = 0 → a * b = 0 := fun a b ha hb => by
    have ha' : a ∈ maximalIdeal A := fun h => by
      have := h.map p
      rw [ha] at this
      exact not_isUnit_zero this
    have : a * b ∈ maximalIdeal A * RingHom.ker p := Ideal.mul_mem_mul ha' hb
    rwa [hs, Ideal.mem_bot] at this
  have hE : ∀ s i j, p ((adj (y0 s) * y0 s - algebraMap Λ A (ν s) • (1 : M4 A)) i j) = 0 := fun s i j => by
    obtain ⟨-, -, -, -, -, hm, -⟩ := grp A
    have e1 : (adj (y0 s) * y0 s).map p = algebraMap Λ R (ν s) • (1 : M4 R) := by
      have := hm R (p : A →+* R) (y0 s)
      simp only [RingHom.coe_coe] at this
      rw [Matrix.map_mul, ← this, b1]
      exact hg s
    have e2 := congrFun (congrFun e1 i) j
    rw [Matrix.map_apply] at e2
    rw [Matrix.sub_apply, map_sub, e2]
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  refine ⟨fun s => corr (algebraMap Λ A (u * ((ν s)⁻¹ : Λˣ))) (algebraMap Λ A (ν s)) (y0 s), fun i j N => ?_,
    fun s => corr_gsp _ _ _ ?_ ?_, fun s => ?_, fun h s => corr_up _ _ fun i j e => ?_⟩
  · let q := Ideal.Quotient.mk (maximalIdeal A ^ N)
    have c1 : IsLocallyConstant fun s => (y0 s).map q := lc_mat fun i j => b0 i j N
    have c2 : IsLocallyConstant fun s => q (algebraMap Λ A (ν s)) := by
      have hle : maximalIdeal Λ ^ N ≤ (maximalIdeal A ^ N).comap (algebraMap Λ A) :=
        (Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.1 (map_maximalIdeal_le (algebraMap Λ A))) N).trans
          (Ideal.le_comap_pow _ N)
      exact (hν N).comp (Ideal.quotientMap _ _ hle)
    have c3 : ∀ s, q (algebraMap Λ A (u * ((ν s)⁻¹ : Λˣ))) =
        q (algebraMap Λ A u) * Ring.inverse (q (algebraMap Λ A (ν s))) := fun s => by
      rw [map_mul, map_mul]
      congr 1
      exact (Ring.inverse_unit (Units.map (q.comp (algebraMap Λ A)).toMonoidHom (ν s))).symm
    have c4 := (c1.prodMk c2).comp fun w => corr (q (algebraMap Λ A u) * Ring.inverse w.2) w.2 w.1 i j
    convert c4 using 2 with s
    simp only [Function.comp_apply]
    rw [← c3, ← corr_map]
    rfl
  · rw [← map_ofNat (algebraMap Λ A) 2, ← map_mul, ← map_mul, ← mul_assoc, hu, one_mul, Units.inv_mul, map_one]
  · ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => hk _ _ (hE s i k) (hE s k j)
  · have := corr_map (p : A →+* R) (algebraMap Λ A (u * ((ν s)⁻¹ : Λˣ))) (algebraMap Λ A (ν s)) (y0 s)
    simp only [RingHom.coe_coe] at this
    have g := hg s
    unfold IsGSp at g
    rw [this, b1, corr, g, p.commutes (ν s), sub_self, smul_zero, sub_zero, mul_one]
  · simp only [y0, Matrix.of_apply, if_pos fun t => h t i j e]
end

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem isLocallyConstant_finset_sum {S Y ι : Type} [TopologicalSpace S] [AddCommMonoid Y] (t : Finset ι)
    (f : ι → S → Y) (h : ∀ i ∈ t, IsLocallyConstant (f i)) : IsLocallyConstant fun x => ∑ i ∈ t, f i x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsLocallyConstant.const (0 : Y)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact IsLocallyConstant.comp₂ (h a (Finset.mem_insert_self a t))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) (· + ·)

private theorem cont_conj {S R : Type} [TopologicalSpace S] [CommRing R] (I : Ideal R) (x : S → M4 R) (a b : M4 R)
    (h : ∀ i j, AdicCont I fun s => x s i j) (i j : Fin 4) : AdicCont I fun s => (a * x s * b) i j := by
  intro N
  have e : (fun s => Ideal.Quotient.mk (I ^ N) ((a * x s * b) i j)) = fun s =>
      ∑ l, (∑ k, Ideal.Quotient.mk (I ^ N) (a i k) * Ideal.Quotient.mk (I ^ N) (x s k l)) *
        Ideal.Quotient.mk (I ^ N) (b l j) := by
    funext s
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, map_sum, map_mul]
  show IsLocallyConstant (fun s => Ideal.Quotient.mk (I ^ N) ((a * x s * b) i j))
  rw [e]
  refine isLocallyConstant_finset_sum _ _ fun l _ => ?_
  refine IsLocallyConstant.comp₂ ?_ (IsLocallyConstant.const _) (· * ·)
  refine isLocallyConstant_finset_sum _ _ fun k _ => ?_
  exact IsLocallyConstant.comp₂ (IsLocallyConstant.const _) (h k l N) (· * ·)

private theorem cont_push {Λ S A A' : Type} [CommRing Λ] [IsLocalRing Λ] [TopologicalSpace S] [CommRing A] [Algebra Λ A]
    [IsCO Λ A] [CommRing A'] [Algebra Λ A'] [IsCO Λ A'] (p : A →ₐ[Λ] A') (x : S → A)
    (h : AdicCont (maximalIdeal A) x) : AdicCont (maximalIdeal A') fun s => p (x s) := by
  intro N
  have hm : Ideal.map p (maximalIdeal A) ≤ maximalIdeal A' := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, ← res_eq_zero_iff Λ A', res_map, res_eq_zero_iff]
    exact hy
  have hle : maximalIdeal A ^ N ≤ Ideal.comap p (maximalIdeal A' ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact pow_le_pow_left' hm N
  have e : (fun s => Ideal.Quotient.mk (maximalIdeal A' ^ N) (p (x s))) =
      fun s => Ideal.quotientMap (maximalIdeal A' ^ N) (p : A →+* A') hle (Ideal.Quotient.mk (maximalIdeal A ^ N) (x s)) := by
    funext s
    rfl
  show IsLocallyConstant (fun s => Ideal.Quotient.mk (maximalIdeal A' ^ N) (p (x s)))
  rw [e]
  exact (h N).comp _

private theorem gsp_conj {R : Type} [CommRing R] {c : R} {x n : M4 R} (hx : IsGSp c x) (hn : IsGSp 1 n) :
    IsGSp c (adj n * x * n) := by
  obtain ⟨hmul, hadj, -⟩ := grp R
  have hn1 : adj n * n = 1 := by
    have := hn
    unfold IsGSp at this
    rw [this, one_smul]
  have hn2 : n * adj n = 1 := mul_eq_one_comm.mp hn1
  have hx' : adj x * x = c • 1 := hx
  show adj (adj n * x * n) * (adj n * x * n) = c • 1
  rw [hmul, hmul, hadj]
  calc adj n * (adj x * n) * (adj n * x * n) = adj n * (adj x * (n * adj n) * x) * n := by
        simp only [Matrix.mul_assoc]
    _ = c • 1 := by
        rw [hn2, Matrix.mul_one, hx', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hn1]

private theorem gsp_push {Λ A A' : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] [CommRing A'] [Algebra Λ A']
    (p : A →ₐ[Λ] A') {c : Λ} {x : M4 A} (hx : IsGSp (algebraMap Λ A c) x) : IsGSp (algebraMap Λ A' c) (x.map p) := by
  have := isGSp_map (p : A →+* A') hx
  rwa [AlgHom.coe_toRingHom, AlgHom.commutes] at this

theorem UpperTheory.V.Ws.X1.slEx :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ], IsUnit (2 : Λ) → ∀ {Γ V : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →* Γ), (∀ v, Continuous (loc v)) → ∀ {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (ν : Γ →* Λˣ) (r : Γ →* M4 R) (n : V → M4 R), AdicCont (maximalIdeal Λ) (fun g => (ν g : Λ)) → WP loc (fun g => algebraMap Λ R (ν g)) r n → (∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) → ∃ D : SL loc ν r n p, ∀ (A' : Type) [CommRing A'] [Algebra Λ A'] [IsCO Λ A'] (p' : A →ₐ[Λ] A') (p'' : A' →ₐ[Λ] R), p''.comp p' = p → ∃ D' : SL loc ν r n p'', (∀ s t, D'.om s t = (D.om s t).map p') ∧ ∀ v s, D'.de v s = (D.de v s).map p' := by
  intro Λ _ _ _ _ h2 Γ V _ _ _ Gv _ _ _ loc hloc A R _ _ _ _ _ _ p hp hker ν r n hν hW hr
  obtain ⟨yr, hyc, hym, hyp, -⟩ := X1.gspLift h2 p hp hker Γ (fun g => ν g) (fun g => r g) hν hr hW.mult
  letI : TopologicalSpace V := ⊥
  haveI : DiscreteTopology V := ⟨rfl⟩
  obtain ⟨yn, -, hnm, hnp, -⟩ := X1.gspLift h2 p hp hker V (fun _ => 1) n
    (by intro N; exact IsLocallyConstant.of_discrete _)
    (by intro i j N; exact IsLocallyConstant.of_discrete _)
    (fun v => by simpa using hW.sp v)
  have hnm' : ∀ v, IsGSp 1 (yn v) := fun v => by simpa using hnm v
  have ht : ∀ v, ∃ y : Gv v → M4 A, (∀ i j, AdicCont (maximalIdeal A) fun s => y s i j) ∧
      (∀ s, IsGSp (algebraMap Λ A (ν (loc v s))) (y s)) ∧
      (∀ s, (y s).map p = adj (n v) * r (loc v s) * n v) ∧ ∀ s, IsUp (y s) := by
    intro v
    obtain ⟨y, h1, h2', h3, h4⟩ := X1.gspLift h2 p hp hker (Gv v) (fun s => ν (loc v s))
      (fun s => adj (n v) * r (loc v s) * n v)
      (by intro N; exact (hν N).comp_continuous (hloc v))
      (by
        intro i j
        exact cont_conj _ _ _ _ (fun i j N => (hr i j N).comp_continuous (hloc v)) i j)
      (fun s => gsp_conj (hW.mult _) (hW.sp v))
    exact ⟨y, h1, h2', h3, h4 (hW.flag v)⟩
  choose yt hyt using ht
  let D : SL loc ν r n p := ⟨yr, hyc, hym, hyp, yn, hnm', hnp, yt, fun v => (hyt v).1, fun v => (hyt v).2.1,
    fun v => (hyt v).2.2.2, fun v => (hyt v).2.2.1⟩
  refine ⟨D, ?_⟩
  intro A' _ _ _ p' p'' hpp
  have hc : ∀ a, p'' (p' a) = p a := fun a => by rw [← hpp]; rfl
  have hmap : ∀ X : M4 A, (X.map p').map p'' = X.map p := fun X => by
    ext i j
    simp [hc]
  have hm1 : ∀ X Y : M4 A, (X * Y).map p' = X.map p' * Y.map p' := fun X Y => by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, map_sum]
  have hm2 : ∀ X Y : M4 A, (X - Y).map p' = X.map p' - Y.map p' := fun X Y => by
    ext i j
    simp
  have hadj : ∀ X : M4 A, adj (X.map p') = (adj X).map p' := fun X => adj_map (p' : A →+* A') X
  refine ⟨⟨fun g => (yr g).map p', ?_, ?_, ?_, fun v => (yn v).map p', ?_, ?_, fun v s => (yt v s).map p',
    ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i j
    exact cont_push p' _ (hyc i j)
  · intro g
    exact gsp_push p' (hym g)
  · intro g
    rw [hmap, hyp]
  · intro v
    have := isGSp_map (p' : A →+* A') (hnm' v)
    simpa using this
  · intro v
    rw [hmap, hnp]
  · intro v i j
    exact cont_push p' _ ((hyt v).1 i j)
  · intro v s
    exact gsp_push p' ((hyt v).2.1 s)
  · intro v s i j hij
    simp [(hyt v).2.2.2 s i j hij]
  · intro v s
    rw [hmap]
    exact (hyt v).2.2.1 s
  · intro s t
    show (yr s).map p' * (yr t).map p' - (yr (s * t)).map p' = (yr s * yr t - yr (s * t)).map p'
    rw [hm2, hm1]
  · intro v s
    show (yr (loc v s)).map p' - (yn v).map p' * (yt v s).map p' * adj ((yn v).map p') =
      (yr (loc v s) - yn v * yt v s * adj (yn v)).map p'
    rw [hm2, hm1, hm1, hadj]
