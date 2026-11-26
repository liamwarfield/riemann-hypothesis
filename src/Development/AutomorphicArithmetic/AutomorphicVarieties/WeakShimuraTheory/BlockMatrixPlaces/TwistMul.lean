module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.GwCount

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.CocT
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.PrimEx
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.DivStep
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem mem_lev_iff {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {T : Type} [AddCommGroup T]
    [Module A T] {t : A} (ht : Irreducible t) (n : ℕ) (x : T) : x ∈ lev A T n ↔ ∃ w, t ^ n • w = x := by
  have hm : maximalIdeal A = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht
  show x ∈ maximalIdeal A ^ n • (⊤ : Submodule A T) ↔ _
  rw [hm, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

private theorem mem_of_bij {A : Type} [CommRing A] {T : Type} [AddCommGroup T] [Module A T] [Module.Finite A T]
    (f : T →ₗ[A] T) (hf : Function.Surjective f) (Q : Submodule A T) (hQ : Q ≤ Q.comap f) {y : T} (hy : f y ∈ Q) :
    y ∈ Q := by
  let g := Q.mapQ Q f hQ
  have hs : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨w, rfl⟩ := hf x
    exact ⟨Q.mkQ w, by simp [g]⟩
  have hi := OrzechProperty.injective_of_surjective_endomorphism g hs
  have h0 : g (Q.mkQ y) = g 0 := by
    simp only [g, Submodule.mkQ_apply, Submodule.mapQ_apply, map_zero]
    exact (Submodule.Quotient.mk_eq_zero Q).2 hy
  have h1 := hi h0
  simpa using h1

theorem UpperTheory.V.Ws.Bl.divStep :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), Lat ρ H P → ∀ t : A, Irreducible t → ∀ n, ∀ z ∈ Zn ρ c N H P (n + 1), ¬ Prim z →
          ∃ z' ∈ Zn ρ c N H P n, ∀ g x, (lev A T n).mkQ x = z' g → (lev A T (n + 1)).mkQ (t • x) = z g := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hL t ht n z hz hnp
  obtain ⟨y, hzy⟩ := hz
  have ht0 : t ≠ 0 := ht.ne_zero
  have hinjt : Function.Injective (fun x : T => t • x) := smul_right_injective T ht0
  have hlev := fun k x => mem_lev_iff (T := T) ht k x
  have hφ : lev A T n ≤ (lev A T (n + 1)).comap (t • LinearMap.id) := by
    intro x hx
    obtain ⟨w, rfl⟩ := (hlev n x).1 hx
    rw [Submodule.mem_comap]
    refine (hlev (n + 1) _).2 ⟨w, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, pow_succ', mul_smul]
  let φ := (lev A T n).mapQ (lev A T (n + 1)) (t • LinearMap.id) hφ
  have hφmk : ∀ x, φ ((lev A T n).mkQ x) = (lev A T (n + 1)).mkQ (t • x) := fun x => rfl
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective a
    rw [hφmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at ha
    obtain ⟨w, hw⟩ := (hlev (n + 1) _).1 ha
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine (hlev n x).2 ⟨w, hinjt ?_⟩
    simp only
    rw [← hw, pow_succ', mul_smul]
  have hφP : ∀ a, φ a ∈ Submodule.map (lev A T (n + 1)).mkQ P →
      a ∈ Submodule.map (lev A T n).mkQ P := by
    intro a ha
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective a
    obtain ⟨q, hq, hqe⟩ := Submodule.mem_map.1 ha
    rw [hφmk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hqe
    obtain ⟨v, hv⟩ := (hlev (n + 1) _).1 hqe
    have hq' : t • (x + t ^ n • v) ∈ P := by
      have e : t • (x + t ^ n • v) = q := by
        rw [smul_add, ← mul_smul, ← pow_succ', hv]
        abel
      rw [e]
      exact hq
    have hxP := hL.sat t _ ht0 hq'
    refine Submodule.mem_map.2 ⟨x + t ^ n • v, hxP, ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact (hlev n _).2 ⟨v, by abel⟩
  have hφρ : ∀ g a, φ (modRep ρ n g a) = modRep ρ (n + 1) g (φ a) := by
    intro g a
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective a
    rw [modRep_mk, hφmk, hφmk, modRep_mk, LinearMap.map_smul (ρ g) t x]
  have hz1 : ∀ g, z g ∈ Submodule.map (lev A T (n + 1)).mkQ (lev A T 1) := by
    intro g
    by_contra hc
    exact hnp ⟨g, hc⟩
  have hrange : ∀ g, ∃ a, φ a = z g := by
    intro g
    obtain ⟨u, hu, hue⟩ := Submodule.mem_map.1 (hz1 g)
    obtain ⟨w, rfl⟩ := (hlev 1 u).1 hu
    refine ⟨(lev A T n).mkQ w, ?_⟩
    rw [hφmk, ← hue, pow_one]
  choose z' hz' using hrange
  obtain ⟨s, hsH, hsb⟩ := hL.fr
  obtain ⟨y0, rfl⟩ := (lev A T (n + 1)).mkQ_surjective y
  have hle1 : lev A T (n + 1) ≤ lev A T 1 :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
  have hy0 : y0 ∈ P ⊔ lev A T 1 := by
    let f : T →ₗ[A] T := ρ s - LinearMap.id
    have hfs : Function.Surjective f := hsb.2
    apply mem_of_bij f hfs
    · intro x hx
      rw [Submodule.mem_comap]
      show ρ s x - x ∈ _
      apply Submodule.sub_mem _ _ hx
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
      refine Submodule.mem_sup.2 ⟨ρ s p, hL.stab s hsH p hp, ρ s q, ?_, (map_add _ _ _).symm⟩
      obtain ⟨w, rfl⟩ := (hlev 1 q).1 hq
      exact (hlev 1 _).2 ⟨ρ s w, (map_smul _ _ _).symm⟩
    · show ρ s y0 - y0 ∈ _
      have hloc : z s - (modRep ρ (n + 1) s ((lev A T (n + 1)).mkQ y0) - (lev A T (n + 1)).mkQ y0)
          ∈ Submodule.map (lev A T (n + 1)).mkQ P := hzy.loc s hsH
      obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hloc
      obtain ⟨u, hu, hue⟩ := Submodule.mem_map.1 (hz1 s)
      rw [modRep_mk, ← hue, ← map_sub, ← map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq] at hpe
      have e : ρ s y0 - y0 = ((p - (u - (ρ s y0 - y0))) + u) - p := by abel
      rw [e]
      apply Submodule.sub_mem _ _ (Submodule.mem_sup_left hp)
      apply Submodule.add_mem _ (Submodule.mem_sup_right (hle1 hpe)) (Submodule.mem_sup_right hu)
  obtain ⟨p0, hp0, q0, hq0, hpq⟩ := Submodule.mem_sup.1 hy0
  obtain ⟨w0, rfl⟩ := (hlev 1 q0).1 hq0
  subst hpq
  have hcomp : ⇑φ ∘ z' = z := funext hz'
  refine ⟨z', ⟨(lev A T n).mkQ w0, ?_⟩, ?_⟩
  · refine ⟨IsLocallyConstant.desc z' φ (by rw [hcomp]; exact hzy.lc) hφinj, ?_, ?_, ?_, ?_⟩
    · intro g h
      show z' (g * h) = z' g + modRep ρ n g (z' h)
      apply hφinj
      rw [hz', map_add (f := _), hφρ, hz', hz']
      exact hzy.coc g h
    · apply hφinj
      rw [hz', map_zero]
      exact hzy.cz
    · intro g hg
      apply hφinj
      rw [hz', map_zero]
      exact hzy.kill g hg
    · intro h hh
      show z' h - (modRep ρ n h ((lev A T n).mkQ w0) - (lev A T n).mkQ w0)
        ∈ Submodule.map (lev A T n).mkQ P
      apply hφP
      rw [map_sub, map_sub, hφρ, hz', hφmk]
      have hloc : z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0))
          - (lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0)) ∈ Submodule.map (lev A T (n + 1)).mkQ P :=
        hzy.loc h hh
      have e : z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (t • w0)) - (lev A T (n + 1)).mkQ (t • w0))
          = (z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0))
            - (lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0))) + (lev A T (n + 1)).mkQ (ρ h p0 - p0) := by
        simp only [pow_one, map_add (f := _), map_sub, modRep_mk]
        abel
      rw [e]
      exact Submodule.add_mem _ hloc
        (Submodule.mem_map_of_mem (Submodule.sub_mem _ (hL.stab h hh p0 hp0) hp0))
  · intro g x hx
    rw [← hφmk, hx, hz']
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.primEx :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), Lat ρ H P → (∀ n, (Zn ρ c N H P n).Finite) → (∀ n, n ≤ Nat.card (Zn ρ c N H P n)) → ∀ n, 0 < n → ∃ z ∈ Zn ρ c N H P n, Prim z := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hL hfin hcard n hn
  by_contra hne
  push_neg at hne
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hA : ∀ k, ∀ z ∈ Zn ρ c N H P (n + k), ¬Prim z := by
    intro k
    induction k with
    | zero => exact hne
    | succ k ih =>
      intro z hz hpz
      obtain ⟨y, hy⟩ := hz
      have hr := redMem A T Γ ρ c N H P (n + k) z y hy
      exact ih _ ⟨_, hr.1⟩ (hr.2.1 hpz (by omega))
  have hB : ∀ k, Nat.card (Zn ρ c N H P (n + k + 1)) ≤ Nat.card (Zn ρ c N H P (n + k)) := by
    intro k
    haveI := (hfin (n + k)).to_subtype
    have key : ∀ z : Zn ρ c N H P (n + k + 1), ∃ z' : Zn ρ c N H P (n + k),
        ∀ g x, (lev A T (n + k)).mkQ x = z'.1 g → (lev A T (n + k + 1)).mkQ (t • x) = z.1 g := by
      intro z
      obtain ⟨z', hz', h⟩ := divStep A T Γ ρ c N H P hL t ht (n + k) z.1 z.2 (hA (k + 1) z.1 z.2)
      exact ⟨⟨z', hz'⟩, h⟩
    choose f hf using key
    refine Nat.card_le_card_of_injective f ?_
    intro z1 z2 h12
    apply Subtype.ext
    funext g
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (lev A T (n + k)) ((f z1).1 g)
    rw [← hf z1 g x hx, hf z2 g x (by rw [hx, h12])]
  have hC : ∀ k, Nat.card (Zn ρ c N H P (n + k)) ≤ Nat.card (Zn ρ c N H P n) := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hB k).trans ih
  have h1 := hcard (n + (Nat.card (Zn ρ c N H P n) + 1))
  have h2 := hC (Nat.card (Zn ρ c N H P n) + 1)
  omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.Compat
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

open CategoryTheory in
private theorem seq_ex (S : ℕ → Type) (hf : ∀ n, Finite (S n)) (hn : ∀ n, Nonempty (S n)) (t : ∀ n, S (n + 1) → S n) :
    ∃ u : ∀ n, S n, ∀ n, t n (u (n + 1)) = u n :=
  _root_.UpperTheory.Reformulated.B.Qj7.seq_ex S hf hn t

theorem UpperTheory.V.Ws.Bl.compat :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), (∀ n, Finite (T ⧸ lev A T n)) → (∀ n, (Zn ρ c N H P n).Finite) → (∀ n, 0 < n → ∃ z ∈ Zn ρ c N H P n, Prim z) →
          ∃ (z : ∀ n, Γ → T ⧸ lev A T n) (y : ∀ n, T ⧸ lev A T n), (∀ n, IsZn ρ c N H P n (z n) (y n)) ∧ (∀ n g, redn A T n (z (n + 1) g) = z n g) ∧ (∀ n, redn A T n (y (n + 1)) = y n) ∧ Prim (z 1) := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hT hZ hP
  let S : ℕ → Type := fun n =>
    {p : (Γ → T ⧸ lev A T n) × (T ⧸ lev A T n) // IsZn ρ c N H P n p.1 p.2 ∧ (0 < n → Prim p.1)}
  let t : ∀ n, S (n + 1) → S n := fun n p =>
    ⟨(fun g => redn A T n (p.1.1 g), redn A T n p.1.2),
      (redMem A T Γ ρ c N H P n _ _ p.2.1).1,
      (redMem A T Γ ρ c N H P n _ _ p.2.1).2.1 (p.2.2 n.succ_pos)⟩
  have hf : ∀ n, Finite (S n) := fun n => by
    have := hT n
    have h : ((Zn ρ c N H P n) ×ˢ (Set.univ : Set (T ⧸ lev A T n))).Finite := (hZ n).prod Set.finite_univ
    have h' : {p : (Γ → T ⧸ lev A T n) × (T ⧸ lev A T n) |
        IsZn ρ c N H P n p.1 p.2 ∧ (0 < n → Prim p.1)}.Finite :=
      h.subset (by
        intro p hp
        exact ⟨⟨p.2, hp.1⟩, trivial⟩)
    exact h'.to_subtype
  have hn : ∀ n, Nonempty (S n) := fun n => by
    obtain ⟨z, ⟨y, hz⟩, hp⟩ := hP (n + 1) n.succ_pos
    exact ⟨t n ⟨(z, y), hz, fun _ => hp⟩⟩
  obtain ⟨u, hu⟩ := seq_ex S hf hn t
  exact ⟨fun n => (u n).1.1, fun n => (u n).1.2, fun n => (u n).2.1,
    fun n g => congrArg (fun p : S n => p.1.1 g) (hu n),
    fun n => congrArg (fun p : S n => p.1.2) (hu n), (u 1).2.2 Nat.one_pos⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.IsPrecompleteFinite
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

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
  refine ⟨fun f hf => ?_⟩
  have key : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
    IsPrecomplete.prec' (I := I) (fun n => f n i) fun {m n} hmn => by
      have h := hf hmn
      rw [SModEq.sub_mem, mem_smul_top_pi] at h
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact h i
  choose L hL using key
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have h := hL i n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h

private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I r
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨z, rfl⟩ := AdicCompletion.map_surjective I hπ y
  obtain ⟨w, rfl⟩ := AdicCompletion.of_surjective I (Fin r → R) z
  exact ⟨π w, (AdicCompletion.map_of I π w).symm⟩

private theorem lift_seq {A : Type} [CommRing A] [IsLocalRing A] {T : Type} [AddCommGroup T] [Module A T]
    [IsPrecomplete (maximalIdeal A) T] (x : ∀ n, T ⧸ lev A T n) (hx : ∀ n, redn A T n (x (n + 1)) = x n) :
    ∃ L : T, ∀ n, (lev A T n).mkQ L = x n := by
  choose f hf using fun n => (lev A T n).mkQ_surjective (x n)
  have h1 : ∀ n, f n - f (n + 1) ∈ lev A T n := fun n => by
    rw [← Submodule.Quotient.eq]
    have := hx n
    rw [← hf (n + 1), redn_mk, ← hf n] at this
    exact this.symm
  have h2 : ∀ m n, m ≤ n → f m - f n ∈ lev A T m := fun m n hmn => by
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h3 : lev A T n ≤ lev A T m := Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)
      simpa using (lev A T m).add_mem ih (h3 (h1 n))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal A) f fun {m n} hmn => SModEq.sub_mem.2 (h2 m n hmn)
  exact ⟨L, fun n => Eq.trans (SModEq.def.1 (hL n).symm) (hf n)⟩

private theorem mem_of_lev {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {T : Type} [AddCommGroup T]
    [Module A T] [Module.Finite A T] (P : Submodule A T) (x : T)
    (hx : ∀ n, (lev A T n).mkQ x ∈ P.map (lev A T n).mkQ) : x ∈ P := by
  rw [← Submodule.Quotient.mk_eq_zero]
  refine IsHausdorff.haus' (I := maximalIdeal A) _ fun n => ?_
  obtain ⟨p, hp, e⟩ := hx n
  have e' : p - x ∈ lev A T n := (Submodule.Quotient.eq _).1 e
  have h1 : P.mkQ (p - x) ∈ (lev A T n).map P.mkQ := Submodule.mem_map_of_mem e'
  rw [Submodule.map_smul'', map_sub, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).2 hp, zero_sub,
    neg_mem_iff] at h1
  rw [SModEq.zero]
  exact Submodule.smul_mono le_rfl le_top h1

private theorem eq_of_lev {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {T : Type} [AddCommGroup T]
    [Module A T] [Module.Finite A T] (x y : T)
    (hx : ∀ n, (lev A T n).mkQ x = (lev A T n).mkQ y) : x = y := by
  rw [← sub_eq_zero, ← Submodule.mem_bot A]
  refine mem_of_lev ⊥ _ fun n => ?_
  rw [map_sub, hx n, sub_self]
  exact zero_mem _

theorem UpperTheory.V.Ws.Bl.limit :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), IsAdicComplete (maximalIdeal A) A → ∀ (z : ∀ n, Γ → T ⧸ lev A T n) (y : ∀ n, T ⧸ lev A T n), (∀ n, IsZn ρ c N H P n (z n) (y n)) → (∀ n g, redn A T n (z (n + 1) g) = z n g) → (∀ n, redn A T n (y (n + 1)) = y n) → Prim (z 1) →
          ∃ (z' : Γ → T) (y' : T), IsZT ρ c N H P z' y' ∧ z' ≠ 0 := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hA z y hZ hz hy hP
  haveI : IsPrecomplete (maximalIdeal A) T := isPrecomplete_finite _
  choose z' hz' using fun g => lift_seq (fun n => z n g) fun n => hz n g
  obtain ⟨y', hy'⟩ := lift_seq y hy
  refine ⟨z', y', ⟨fun n => ?_, fun g h => ?_, ?_, fun g hg => ?_, fun h hh => ?_⟩, ?_⟩
  · simp only [hz']
    exact (hZ n).lc
  · refine eq_of_lev (A := A) _ _ fun n => ?_
    rw [map_add (f := _), ← modRep_mk, hz', hz', hz']
    exact (hZ n).coc g h
  · refine eq_of_lev (A := A) _ _ fun n => ?_
    rw [hz', map_zero]
    exact (hZ n).cz
  · refine eq_of_lev (A := A) _ _ fun n => ?_
    rw [hz', map_zero]
    exact (hZ n).kill g hg
  · refine mem_of_lev P _ fun n => ?_
    rw [map_sub, map_sub, ← modRep_mk, hz', hy']
    exact (hZ n).loc h hh
  · rintro rfl
    obtain ⟨g, hg⟩ := hP
    apply hg
    rw [← hz' g 1, Pi.zero_apply, map_zero]
    exact zero_mem _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.CardP
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.cardP :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (P : Submodule A T), (∀ (a : A) (x : T), a ≠ 0 → a • x ∈ P → x ∈ P) → P ≠ ⊥ →
          ∀ n, Finite (T ⧸ lev A T n) ∧ n ≤ Nat.card (P.map (lev A T n).mkQ) := by
  intro A _ _ _ _ T _ _ _ _ P hsat hP n
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hm : maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hL : ∀ (k : ℕ) (z : T), z ∈ lev A T k ↔ ∃ t, ϖ ^ k • t = z := by
    intro k z
    show z ∈ maximalIdeal A ^ k • (⊤ : Submodule A T) ↔ _
    rw [hm, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp
  have hfin : ∀ k, Finite (T ⧸ lev A T k) := by
    intro k
    have h1 : (maximalIdeal A).FG := IsNoetherian.noetherian _
    haveI : Finite (A ⧸ maximalIdeal A) := (inferInstance : Finite (ResidueField A))
    haveI := Ideal.finite_quotient_pow h1 k
    haveI : Finite (T ⧸ (⊤ : Submodule A T)) := inferInstance
    exact Submodule.finite_quotient_smul _ (Module.finite_def.mp inferInstance)
  obtain ⟨y, hyP, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hx : ∃ x ∈ P, x ∉ lev A T 1 := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ k : ℕ, ∀ z ∈ P, z ∈ lev A T k := by
      intro k
      induction k with
      | zero =>
        intro z _
        exact (hL 0 z).mpr ⟨z, by simp⟩
      | succ k ih =>
        intro z hz
        obtain ⟨t, rfl⟩ := (hL 1 z).mp (hcon z hz)
        have htP : t ∈ P := hsat _ _ (pow_ne_zero 1 hϖ0) hz
        obtain ⟨s, rfl⟩ := (hL k t).mp (ih t htP)
        exact (hL (k + 1) _).mpr ⟨s, by rw [smul_smul, ← pow_add, add_comm 1 k]⟩
    have hmem : y ∈ (⨅ i : ℕ, maximalIdeal A ^ i • (⊤ : Submodule A T)) :=
      Submodule.mem_iInf _ |>.mpr (fun i => hall i y hyP)
    rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _
      (IsLocalRing.maximalIdeal.isMaximal A).ne_top] at hmem
    exact hy0 ((Submodule.mem_bot A).mp hmem)
  obtain ⟨x, hxP, hx1⟩ := hx
  refine ⟨hfin n, ?_⟩
  haveI := hfin n
  have key : ∀ i j : ℕ, i < j → j < n → ϖ ^ i • x - ϖ ^ j • x ∉ lev A T n := by
    intro i j hij hjn hmem
    obtain ⟨s, hs⟩ := (hL n _).mp hmem
    have e1 : ϖ ^ i • (ϖ ^ (n - i) • s) = ϖ ^ i • (x - ϖ ^ (j - i) • x) := by
      rw [smul_smul, ← pow_add, Nat.add_sub_cancel' (by omega), hs, smul_sub, smul_smul,
        ← pow_add, Nat.add_sub_cancel' hij.le]
    have e2 : ϖ ^ (n - i) • s = x - ϖ ^ (j - i) • x :=
      smul_right_injective T (pow_ne_zero i hϖ0) e1
    apply hx1
    rw [hL 1]
    refine ⟨ϖ ^ (n - i - 1) • s + ϖ ^ (j - i - 1) • x, ?_⟩
    rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add,
      Nat.add_sub_cancel' (by omega : 1 ≤ n - i), Nat.add_sub_cancel' (by omega : 1 ≤ j - i),
      e2, sub_add_cancel]
  let f : Fin n → P.map (lev A T n).mkQ := fun i =>
    ⟨(lev A T n).mkQ (ϖ ^ (i : ℕ) • x), Submodule.mem_map_of_mem (P.smul_mem _ hxP)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h' : (lev A T n).mkQ (ϖ ^ (i : ℕ) • x) = (lev A T n).mkQ (ϖ ^ (j : ℕ) • x) :=
      congrArg Subtype.val hij
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h'
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · exact absurd h' (key _ _ h j.2)
    · exact Fin.ext h
    · have h'' := (lev A T n).neg_mem h'
      rw [neg_sub] at h''
      exact absurd h'' (key _ _ h i.2)
  calc n = Nat.card (Fin n) := by simp
    _ ≤ _ := Nat.card_le_card_of_injective f hf
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.cocT :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (ρ : Representation A (G ℚ Ω) T) (P : Submodule A T) (K : Subgroup (G ℚ Ω)),
          IsAdicComplete (maximalIdeal A) A → (l : A) ∈ maximalIdeal A → Lat ρ (Dec (F := ℚ) B) P → (Function.Bijective fun x => ρ s x - x) → (∀ x, ρ c x = -x) → K ≤ ρ.ker → (∀ A', Raw.Away S A' → Ine (F := ℚ) A' ≤ K) →
          ∃ (z : G ℚ Ω → T) (y : T), IsZT ρ c (neSet l K) (Dec (F := ℚ) B) P z y ∧ z ≠ 0 := by
  intro hC Ω _ _ _ l _ S c s B hP A _ _ _ _ T _ _ _ _ ρ P K hA hl hL hs hc hK hU
  have hcard := cardP A T P hL.sat hL.ne
  have hfin : ∀ n, Finite (T ⧸ lev A T n) := fun n => (hcard n).1
  have htor : ∀ n, ∀ m : T ⧸ lev A T n, (l ^ n) • m = 0 := by
    intro n m
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul A, Nat.cast_pow]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hl n) Submodule.mem_top
  have hlc : ∀ n, ∀ m : T ⧸ lev A T n, IsLocallyConstant fun g => modRep ρ n g m := by
    intro n m
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    exact hL.cont n x
  have hker : ∀ n, K ≤ (modRep ρ n).ker := by
    intro n g hg
    have h1 : ρ g = 1 := hK hg
    refine LinearMap.ext fun m => ?_
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    rw [modRep_mk, h1]
    rfl
  have hneg : ∀ n, ∀ m : T ⧸ lev A T n, modRep ρ n c m = -m := by
    intro n m
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    rw [modRep_mk, hc, map_neg]
  have hbij : ∀ n, Function.Bijective fun m : T ⧸ lev A T n => modRep ρ n s m - m := by
    intro n
    haveI := hfin n
    refine Finite.surjective_iff_bijective.1 fun m => ?_
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    obtain ⟨y, rfl⟩ := hs.2 x
    exact ⟨(lev A T n).mkQ y, by simp only [modRep_mk, map_sub]⟩
  have hstab : ∀ n, ∀ h ∈ Dec (F := ℚ) B, ∀ x ∈ P.map (lev A T n).mkQ, modRep ρ n h x ∈ P.map (lev A T n).mkQ := by
    rintro n h hh _ ⟨x, hx, rfl⟩
    exact ⟨ρ h x, hL.stab h hh x hx, rfl⟩
  have hZ : ∀ n, (Zn ρ c (neSet l K) (Dec (F := ℚ) B) P n).Finite := fun n => by
    haveI := hfin n
    exact zcFin hC.gf S c s B hP A _ (modRep ρ n) n (htor n) (hlc n) K (hker n) hU _
  have hge : ∀ n, n ≤ Nat.card (Zn ρ c (neSet l K) (Dec (F := ℚ) B) P n) := fun n => by
    haveI := hfin n
    exact (hcard n).2.trans
      (gwCount hC S c s B hP A _ (modRep ρ n) n (htor n) (hlc n) K (hker n) hU (hneg n) (hbij n) _ (hstab n))
  obtain ⟨z, y, h1, h2, h3, h4⟩ := compat A T _ ρ c _ _ P hfin hZ (primEx A T _ ρ c _ _ P hL hZ hge)
  exact limit A T _ ρ c _ _ P hA z y h1 h2 h3 h4
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.UpSupUp
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.FlagVec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem unit_add_mem {R : Type} [CommRing R] [IsLocalRing R] {a b : R} (ha : IsUnit a)
    (hb : b ∈ maximalIdeal R) : IsUnit (a + b) := by
  by_contra h
  have h1 : a + b ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have h2 : a ∈ maximalIdeal R := by simpa using (maximalIdeal R).sub_mem h1 hb
  exact (IsLocalRing.mem_maximalIdeal _).mp h2 ha

private theorem two_kill {R : Type} [CommRing R] [IsLocalRing R] {p q r s a b : R} (hp : IsUnit p) (hs : IsUnit s)
    (hq : q ∈ maximalIdeal R) (e1 : p * a + q * b = 0) (e2 : r * a + s * b = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨s', hs'⟩ := hs.exists_right_inv
  have hb : b = -(s' * r) * a := by linear_combination s' * e2 - b * hs'
  have hm : q * s' * r ∈ maximalIdeal R :=
    (maximalIdeal R).mul_mem_right _ ((maximalIdeal R).mul_mem_right _ hq)
  have hu : IsUnit (p + -(q * s' * r)) := unit_add_mem hp ((maximalIdeal R).neg_mem hm)
  have ha : a = 0 := (hu.mul_right_eq_zero).mp (by linear_combination e1 - q * hb)
  refine ⟨ha, ?_⟩
  rw [hb, ha]
  ring

private theorem cols {R : Type} [CommRing R] [IsLocalRing R] (X u U : M4 R) (hb : IsBlock X) (hs : Sep X)
    (e : X * u = u * U) (hU : IsUp U) (hc : ∀ i, U i i - X i i ∈ maximalIdeal R) :
    ∃ y, u 0 1 = y * u 0 0 ∧ u 2 1 = y * u 2 0 := by
  have h01 : IsUnit (X 0 0 - X 1 1) := hs.unit 0 1 (by decide)
  have h21 : IsUnit (X 2 2 - X 1 1) := hs.unit 2 1 (by decide)
  have p0 : IsUnit (X 0 0 - U 1 1) := by
    have := unit_add_mem h01 (neg_mem (hc 1))
    convert this using 1; ring
  have p2 : IsUnit (X 2 2 - U 1 1) := by
    have := unit_add_mem h21 (neg_mem (hc 1))
    convert this using 1; ring
  have pU : IsUnit (U 0 0 - U 1 1) := by
    have := unit_add_mem p0 (hc 0)
    convert this using 1; ring
  obtain ⟨w, hw⟩ := pU.exists_left_inv
  have z01 := hb 0 1 (by decide)
  have z03 := hb 0 3 (by decide)
  have z21 := hb 2 1 (by decide)
  have z23 := hb 2 3 (by decide)
  have y10 := hU 1 0 (by decide)
  have y20 := hU 2 0 (by decide)
  have y30 := hU 3 0 (by decide)
  have y21 := hU 2 1 (by decide)
  have y31 := hU 3 1 (by decide)
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e20 := congrFun (congrFun e 2) 0
  have e21 := congrFun (congrFun e 2) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_four, z01, z03, z21, z23, y10, y20, y30, y21, y31, zero_mul, mul_zero,
    add_zero] at e00 e01 e20 e21
  have := two_kill (a := u 0 1 - U 0 1 * w * u 0 0) (b := u 2 1 - U 0 1 * w * u 2 0) (r := X 2 0) p0 p2
    (hs.off 0 2 (by decide))
    (by linear_combination e01 - U 0 1 * w * e00 - U 0 1 * u 0 0 * hw)
    (by linear_combination e21 - U 0 1 * w * e20 - U 0 1 * u 2 0 * hw)
  exact ⟨U 0 1 * w, sub_eq_zero.mp this.1, sub_eq_zero.mp this.2⟩

private theorem entries_one_three_zero_eq_zero_of_intertwine_up {R : Type} [CommRing R] [IsLocalRing R] (X u U : M4 R) (hb : IsBlock X)
    (hs : Sep X) (e : X * u = u * U) (hU : IsUp U) (hc : ∀ i, U i i - X i i ∈ maximalIdeal R) :
    u 1 0 = 0 ∧ u 3 0 = 0 := by
  have X10 : X 1 0 = 0 := hb 1 0 (by simp [lamW])
  have coord_mul_inv_coord_eq_one : X 1 2 = 0 := hb 1 2 (by simp [lamW])
  have X30 : X 3 0 = 0 := hb 3 0 (by simp [lamW])
  have X32 : X 3 2 = 0 := hb 3 2 (by simp [lamW])
  have U10 : U 1 0 = 0 := hU 1 0 (by decide)
  have U20 : U 2 0 = 0 := hU 2 0 (by decide)
  have U30 : U 3 0 = 0 := hU 3 0 (by decide)
  have r10 := congrFun (congrFun e 1) 0
  have r30 := congrFun (congrFun e 3) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_four, X10, coord_mul_inv_coord_eq_one, X30, X32, U10, U20, U30,
    zero_mul, mul_zero, add_zero, zero_add] at r10 r30
  have hc0 := hc 0
  have hp : IsUnit (X 1 1 - U 0 0) := by
    have e' : X 1 1 - U 0 0 = (X 1 1 - X 0 0) + -(U 0 0 - X 0 0) := by ring
    rw [e']
    exact unit_add_mem (hs.unit 1 0 (by simp [lamW])) ((maximalIdeal R).neg_mem hc0)
  have hs' : IsUnit (X 3 3 - U 0 0) := by
    have e' : X 3 3 - U 0 0 = (X 3 3 - X 0 0) + -(U 0 0 - X 0 0) := by ring
    rw [e']
    exact unit_add_mem (hs.unit 3 0 (by simp [lamW])) ((maximalIdeal R).neg_mem hc0)
  have hq : X 1 3 ∈ maximalIdeal R := hs.off 1 3 (by decide)
  exact two_kill (r := X 3 1) (a := u 1 0) (b := u 3 0) hp hs' hq
    (by linear_combination r10) (by linear_combination r30)

theorem UpperTheory.V.Ws.Bl.flagVec :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X u : M4 R), IsBlock X → Sep X → IsGSp 1 u → IsUp (adj u * X * u) → (∀ i, (adj u * X * u) i i - X i i ∈ maximalIdeal R) → uPlus u ≠ ⊥ := by
  intro R _ _ X u hb hs hg hup hc
  have hinv : adj u * u = 1 := by simpa [IsGSp] using hg
  have e : X * u = u * (adj u * X * u) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_eq_one_comm.mp hinv, Matrix.one_mul]
  obtain ⟨y, hy1, hy2⟩ := cols X u _ hb hs e hup hc
  obtain ⟨h10, h30⟩ := entries_one_three_zero_eq_zero_of_intertwine_up X u _ hb hs e hup hc
  have I10 := congrFun (congrFun hinv 1) 0
  have I11 := congrFun (congrFun hinv 1) 1
  have I00 := congrFun (congrFun hinv 0) 0
  have I31 := congrFun (congrFun hinv 3) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev] at I10 I11 I00 I31
  have iso : u 0 0 * u 3 1 = u 2 0 * u 1 1 := by
    linear_combination I31 - u 2 1 * h10 + u 0 1 * h30
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → R, w = ![0, u 1 1, 0, u 3 1] := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin 4 → R, φ = ![u 2 0, 0, -u 0 0, 0] := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y : M4 R, Y = Matrix.vecMulVec w φ := ⟨_, rfl⟩
  have hYm : Y ∈ uM R := by
    show Y ∈ hAB R ⊓ sp4 R
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · show ∀ i j, ¬ lamW i < lamW j → Y i j = 0
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [lamW, Matrix.vecMulVec_apply]
    · show adj Y = -Y
      ext i j
      fin_cases i <;> fin_cases j <;>
        (try simp [hYd, hw, hφ, adj_apply, sgn, Fin.rev, Matrix.vecMulVec_apply]) <;>
        first
          | linear_combination iso
          | linear_combination (-1 : R) * iso
  have hv : w = Matrix.mulVec u ![-y, 1, 0, 0] := by
    funext i
    fin_cases i <;> simp [hw, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      first
        | linear_combination (-1 : R) * hy1
        | linear_combination y * h10
        | linear_combination (-1 : R) * hy2
        | linear_combination y * h30
        | linear_combination hy1
        | linear_combination hy2
        | linear_combination (-y) * h10
        | linear_combination (-y) * h30
  have hA : Matrix.mulVec (adj u) w = ![-y, 1, 0, 0] := by
    rw [hv, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hB0 : Matrix.vecMul φ u 0 = 0 := by
    simp [hφ, Matrix.vecMul, dotProduct, Fin.sum_univ_four] <;> ring
  have hB1 : Matrix.vecMul φ u 1 = 0 := by
    simp [hφ, Matrix.vecMul, dotProduct, Fin.sum_univ_four] <;>
      linear_combination u 2 0 * hy1 - u 0 0 * hy2
  have hN : adj u * Y * u = Matrix.vecMulVec ![-y, 1, 0, 0] (Matrix.vecMul φ u) := by
    rw [hYd, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hA]
  have hsup : IsSUp (adj u * Y * u) := by
    intro i j hji
    rw [hN, Matrix.vecMulVec_apply]
    fin_cases i <;> fin_cases j <;>
      first
        | (simp [hB0, hB1]; done)
        | (exfalso; simp at hji; done)
        | (exfalso; revert hji; decide)
  rw [Submodule.ne_bot_iff]
  refine ⟨⟨Y, hYm⟩, ?_, ?_⟩
  · exact hsup
  · intro hY0
    have hY : Y = 0 := congrArg Subtype.val hY0
    have f1 : u 1 1 * u 2 0 = 0 := by
      have h := congrFun (congrFun hY 1) 0
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have f2 : u 1 1 * u 0 0 = 0 := by
      have h := congrFun (congrFun hY 1) 2
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero, -neg_eq_zero, -mul_neg] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have f3 : u 3 1 * u 2 0 = 0 := by
      have h := congrFun (congrFun hY 3) 0
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have f4 : u 3 1 * u 0 0 = 0 := by
      have h := congrFun (congrFun hY 3) 2
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero, -neg_eq_zero, -mul_neg] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have J : u 2 2 * u 1 1 - u 0 2 * u 3 1 = 1 := by
      linear_combination I11 - u 3 2 * hy1 + u 1 2 * hy2 - y * I10 + y * u 2 2 * h10 -
        y * u 0 2 * h30
    have z00 : u 0 0 = 0 := by linear_combination (-u 0 0) * J + u 2 2 * f2 - u 0 2 * f4
    have z20 : u 2 0 = 0 := by linear_combination (-u 2 0) * J + u 2 2 * f1 - u 0 2 * f3
    have h1 : (1 : R) = 0 := by
      linear_combination (-1 : R) * I00 + u 3 3 * z00 + u 2 3 * h10 - u 1 3 * z20 - u 0 3 * h30
    exact one_ne_zero h1
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

namespace UpperTheory.V.Ws.Bl

end UpperTheory.V.Ws.Bl

private theorem mem_ideal_smul_module_of_entries_mem {A : Type} [CommRing A] (I : Ideal A) (Y : uM A)
    (hY : ∀ i j, (Y : M4 A) i j ∈ I) : Y ∈ I • (⊤ : Submodule A (uM A)) := by
  have h1 : (!![0,0,0,0; 1,0,0,0; 0,0,0,0; 0,0,-1,0] : M4 A) ∈ uM A := by
    refine ⟨fun i j h => ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [adj, sgn]
  have h2 : (!![0,0,0,0; 0,0,1,0; 0,0,0,0; 0,0,0,0] : M4 A) ∈ uM A := by
    refine ⟨fun i j h => ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [adj, sgn]
  have h3 : (!![0,0,0,0; 0,0,0,0; 0,0,0,0; 1,0,0,0] : M4 A) ∈ uM A := by
    refine ⟨fun i j h => ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [adj, sgn]
  obtain ⟨hz, ha⟩ := Y.2
  have h32 : (Y : M4 A) 3 2 = -(Y : M4 A) 1 0 := by
    have h := congrFun (congrFun ha 3) 2
    simp [adj, sgn] at h
    rw [h, neg_neg]
  have hd : Y = (Y : M4 A) 1 0 • (⟨_, h1⟩ : uM A) + (Y : M4 A) 1 2 • (⟨_, h2⟩ : uM A)
      + (Y : M4 A) 3 0 • (⟨_, h3⟩ : uM A) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h32] <;> exact hz _ _ (by decide)
  rw [hd]
  exact add_mem (add_mem (Submodule.smul_mem_smul (hY 1 0) trivial)
    (Submodule.smul_mem_smul (hY 1 2) trivial)) (Submodule.smul_mem_smul (hY 3 0) trivial)

private theorem isLocallyConstant_mkQ_adU_of_adicCont {A : Type} [CommRing A] [IsLocalRing A] {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] [ContinuousInv Γ] (r : Γ →* M4 A) (hb : BG r)
    (hc : ∀ i j, AdicCont (maximalIdeal A) fun g => r g i j) (n : ℕ) (x : uM A) :
    IsLocallyConstant fun g => (lev A (uM A) n).mkQ ((adU hb g) x) := by
  let φ := (Ideal.Quotient.mk (maximalIdeal A ^ n)).mapMatrix (m := Fin 4)
  have hq : ∀ (f : Γ → M4 A), (∀ i j, AdicCont (maximalIdeal A) fun g => f g i j) →
      IsLocallyConstant fun g => φ (f g) := by
    intro f hf
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro M
    have hM : (fun g => φ (f g)) ⁻¹' {M} =
        ⋂ i, ⋂ j, (fun g => Ideal.Quotient.mk (maximalIdeal A ^ n) (f g i j)) ⁻¹' {M i j} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
      constructor
      · intro h i j
        rw [← h]
        rfl
      · intro h
        ext i j
        exact h i j
    rw [hM]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hf i j n).isOpen_fiber _
  have hP : IsLocallyConstant fun g => (φ (r g), φ (r g⁻¹)) :=
    (hq _ hc).prodMk (hq (fun g => r g⁻¹) fun i j N => (hc i j N).comp_continuous continuous_inv)
  have key : ∀ g' g : Γ, (φ (r g'), φ (r g'⁻¹)) = (φ (r g), φ (r g⁻¹)) →
      (lev A (uM A) n).mkQ ((adU hb g') x) = (lev A (uM A) n).mkQ ((adU hb g) x) := by
    intro g' g hgg
    obtain ⟨e1, e2⟩ := Prod.mk.inj hgg
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    apply mem_ideal_smul_module_of_entries_mem
    intro i j
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h0 : φ ((↑((adU hb g') x - (adU hb g) x) : M4 A)) = 0 := by
      rw [Submodule.coe_sub]
      change φ (r g' * (x : M4 A) * r g'⁻¹ - r g * (x : M4 A) * r g⁻¹) = 0
      simp only [map_sub, map_mul, e1, e2, sub_self]
    simpa [φ] using congrFun (congrFun h0 i) j
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  have hy : (fun g => (lev A (uM A) n).mkQ ((adU hb g) x)) ⁻¹' {y} =
      ⋃ g ∈ (fun g => (lev A (uM A) n).mkQ ((adU hb g) x)) ⁻¹' {y},
        (fun g => (φ (r g), φ (r g⁻¹))) ⁻¹' {(φ (r g), φ (r g⁻¹))} := by
    ext g'
    constructor
    · intro h
      exact Set.mem_biUnion h rfl
    · intro h
      obtain ⟨g, hg, hgg⟩ := Set.mem_iUnion₂.1 h
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg hgg ⊢
      rw [← hg]
      exact key g' g hgg
  rw [hy]
  exact isOpen_biUnion fun g _ => hP.isOpen_fiber _

private theorem isSUp_mul_mul_of_isUp_isSUp_isUp {A : Type} [CommRing A] (P N Q : M4 A) (hP : IsUp P) (hN : IsSUp N)
    (hQ : IsUp Q) : IsSUp (P * N * Q) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hli : l < i
  · rw [hP i l hli, zero_mul, zero_mul]
  by_cases hkl : k ≤ l
  · rw [hN l k hkl, mul_zero, zero_mul]
  rw [hQ k j (by omega), mul_zero]

theorem UpperTheory.V.Ws.Bl.latU :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (r : G ℚ Ω →* M4 A) (u : M4 A) (h : BlockDiagonalOrdinaryGSpRep S c s B r u),
          Lat (adU h.bg) (Dec (F := ℚ) B) (uPlus u) ∧ (∀ Y, adU h.bg c Y = -Y) ∧ r.ker ≤ (adU h.bg).ker := by
  intro Ω _ _ _ l _ S c s B hp A _ _ _ r u h
  have hinv : ∀ g, r g = 1 → r g⁻¹ = 1 := by
    intro g hg
    calc r g⁻¹ = r g⁻¹ * r g := by rw [hg, mul_one]
      _ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have huu : u * adj u = 1 := by
    have h1 : adj u * u = 1 := by
      have := h.sp
      simpa [IsGSp] using this
    exact mul_eq_one_comm.1 h1
  refine ⟨⟨fun n x => isLocallyConstant_mkQ_adU_of_adicCont r h.bg h.cont n x, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg Y hY
    have hg' : g⁻¹ ∈ Dec (F := ℚ) B := (Dec (F := ℚ) B).inv_mem hg
    change IsSUp (adj u * (r g * (Y : M4 A) * r g⁻¹) * u)
    have he : adj u * (r g * (Y : M4 A) * r g⁻¹) * u
        = (adj u * r g * u) * (adj u * (Y : M4 A) * u) * (adj u * r g⁻¹ * u) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc u (adj u), huu, Matrix.one_mul, ← Matrix.mul_assoc u (adj u), huu,
        Matrix.one_mul]
    rw [he]
    exact isSUp_mul_mul_of_isUp_isSUp_isUp _ _ _ (h.flag g hg) hY (h.flag _ hg')
  · intro a Y ha hY
    change IsSUp (adj u * ((a • Y : uM A) : M4 A) * u) at hY
    change IsSUp (adj u * (Y : M4 A) * u)
    intro i j hij
    have h0 := hY i j hij
    rw [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.1 h0).resolve_left ha
  · exact flagVec A (r s) u (h.bg.blk s) h.sep h.sp (h.flag s hp.dec) h.char
  · exact ⟨s, hp.dec, adBij A (G ℚ Ω) r h.bg s h.sep⟩
  · intro Y
    have hc2 : r c * r c = 1 := by
      rw [h.cc]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [eAB]
    have hci : r c⁻¹ = r c := by
      calc r c⁻¹ = r c⁻¹ * (r c * r c) := by rw [hc2, Matrix.mul_one]
        _ = r (c⁻¹ * c) * r c := by rw [map_mul, Matrix.mul_assoc]
        _ = r c := by rw [inv_mul_cancel, map_one, Matrix.one_mul]
    obtain ⟨hz, _⟩ := Y.2
    apply Subtype.ext
    change r c * (Y : M4 A) * r c⁻¹ = -(Y : M4 A)
    rw [hci, h.cc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eAB, hz 0 0 (by decide), hz 0 1 (by decide), hz 0 2 (by decide), hz 0 3 (by decide),
        hz 1 1 (by decide), hz 1 3 (by decide), hz 2 0 (by decide), hz 2 1 (by decide),
        hz 2 2 (by decide), hz 2 3 (by decide), hz 3 1 (by decide), hz 3 3 (by decide)]
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply LinearMap.ext
    intro Y
    apply Subtype.ext
    change r g * (Y : M4 A) * r g⁻¹ = (Y : M4 A)
    rw [hg, hinv g hg, Matrix.one_mul, Matrix.mul_one]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem ac_mul {S A : Type} [TopologicalSpace S] [CommRing A] {I : Ideal A}
    {M N : S → M4 A} (hM : ∀ a b, AdicCont I fun s => M s a b) (hN : ∀ a b, AdicCont I fun s => N s a b) :
    ∀ a b, AdicCont I fun s => (M s * N s) a b := by
  intro a b n
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, Fin.sum_univ_four, map_add (f := _)]
  exact ((((hM a 0 n).mul (hN 0 b n)).add ((hM a 1 n).mul (hN 1 b n))).add ((hM a 2 n).mul (hN 2 b n))).add
    ((hM a 3 n).mul (hN 3 b n))

private theorem twist_mul {R Γ : Type} [CommRing R] [Group Γ] {r : Γ →* M4 R} (hb : ∀ g, IsBlock (r g)) {z : Γ → M4 R}
    (hz : ∀ g, z g ∈ hAB R) (coc : ∀ g h, z (g * h) = z g + r g * z h * r g⁻¹) (g h : Γ) :
    (1 + z (g * h)) * r (g * h) = (1 + z g) * r g * ((1 + z h) * r h) := by
  have e : r g⁻¹ * r g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have e0 : z g * (r g * z h * r h) = 0 := hAB_mul_hAB (hz g) (hAB_mul_mul (hb g) (hz h) (hb h))
  have e1 : r g * z h * r g⁻¹ * (r g * r h) = r g * z h * r h := by
    rw [mul_assoc, ← mul_assoc (r g⁻¹), e, one_mul]
  rw [coc, map_mul, ← add_assoc, add_mul, e1]
  calc _ = (1 + z g) * (r g * r h) + r g * z h * r h + z g * (r g * z h * r h) := by rw [e0, add_zero]
    _ = _ := by noncomm_ring

theorem UpperTheory.V.Ws.Bl.cocA :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] (r : G ℚ Ω →* M4 A) (u : M4 A), IsAdicComplete (maximalIdeal A) A → (l : A) ∈ maximalIdeal A → BlockDiagonalOrdinaryGSpRep S c s B r u →
          ∃ (r' : G ℚ Ω →* M4 A) (z : G ℚ Ω → M4 A) (y : M4 A), (∀ g, r' g = (1 + z g) * r g) ∧ (∀ i j, AdicCont (maximalIdeal A) fun g => r' g i j) ∧ (∀ g, z g ∈ uM A) ∧ y ∈ uM A ∧
            (∀ g i j, z g i j ∈ maximalIdeal A) ∧ z c = 0 ∧ (∀ g ∈ neSet l r.ker, z g = 0) ∧ (∀ h ∈ Dec (F := ℚ) B, IsSUp (adj u * (z h - (r h * y * r h⁻¹ - y)) * u)) ∧ z ≠ 0 := by
  intro hP Ω _ _ _ l _ S c s B hpos A _ _ _ _ r u hc hl hb
  obtain ⟨hfin, hfree, hI⟩ := uMFacts A
  obtain ⟨hlat, hcc, hker⟩ := latU S c s B hpos A r u hb
  obtain ⟨z, y, hz, hne⟩ := cocT hP S c s B hpos A (uM A) (adU hb.bg) (uPlus u) r.ker hc hl hlat
    (adBij A _ r hb.bg s hb.sep) hcc hker hb.unr
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  have htm : t ∈ maximalIdeal A := ht.not_isUnit
  have coc : ∀ g h, (t • z (g * h)).1 = (t • z g).1 + r g * (t • z h).1 * r g⁻¹ := fun g h => by
    rw [hz.coc, smul_add, ← map_smul, Submodule.coe_add, adU_val]
  have z1 : z 1 = 0 := by
    have := hz.coc 1 1
    rw [mul_one, map_one, Module.End.one_apply] at this
    exact left_eq_add.mp this
  have zc : ∀ i j, AdicCont (maximalIdeal A) fun g => (1 + (t • z g).1) i j := fun i j n => by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (hz.cont n) g] with g' e
    have e1 : z g' - z g ∈ lev A (uM A) n := (Submodule.Quotient.eq _).1 e
    have e2 := (hI _ _).1 (Submodule.smul_mem _ t e1) i j
    rw [Ideal.Quotient.eq]
    convert e2 using 1
    simp [smul_sub, mul_sub]
  refine ⟨MonoidHom.mk ⟨fun g => (1 + (t • z g).1) * r g, by simp [z1]⟩
      (twist_mul hb.bg.blk (fun g => (t • z g).2.1) coc), fun g => (t • z g).1, (t • y).1, fun _ => rfl,
    ac_mul zc hb.cont, fun g => (t • z g).2, (t • y).2, fun g i j => ?_, by simp [hz.cz], fun g hg => by simp [hz.kill g hg],
    fun h hh => ?_, fun e => hne (funext fun g => ?_)⟩
  · exact Ideal.mul_mem_right _ _ htm
  · have := (uPlus u).smul_mem t (hz.loc h hh)
    rw [smul_sub, smul_sub, ← map_smul] at this
    exact this
  · have e1 : t • (z g).1 = 0 := congrFun e g
    exact Subtype.ext ((smul_eq_zero.1 e1).resolve_left ht.ne_zero)
