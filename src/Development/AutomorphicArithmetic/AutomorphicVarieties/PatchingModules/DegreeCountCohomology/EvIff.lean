module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.EvIff
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem ev_iff {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ} {Z : Matrix (Fin n) (Fin n) R} :
    Z ∈ Ev A R n a ↔ ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j = 0 := by
  show (∀ i j : Fin n, ((((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ (⊤ : Submodule A R)) ∧
      (¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ (⊥ : Submodule A R))) ↔ _
  simp only [Submodule.mem_top, Submodule.mem_bot, implies_true, true_and]

private theorem od_iff {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ} {Z : Matrix (Fin n) (Fin n) R} :
    Z ∈ Od A R n a ↔ ∀ i j : Fin n, (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j = 0 := by
  show (∀ i j : Fin n, ((((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ (⊥ : Submodule A R)) ∧
      (¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ (⊤ : Submodule A R))) ↔ _
  simp only [Submodule.mem_top, Submodule.mem_bot, implies_true, and_true]

private theorem sandwich {R : Type} [CommRing R] {n a : ℕ} {P Q Z : Matrix (Fin n) (Fin n) R}
    (hP : ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → P i j = 0)
    (hQ : ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Q i j = 0) (i j : Fin n)
    (hZ : ∀ i' j' : Fin n, (((i : ℕ) < a) ↔ ((i' : ℕ) < a)) → (((j' : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i' j' = 0) :
    (P * Z * Q) i j = 0 := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun m _ => ?_
  by_cases h1 : (((i : ℕ) < a) ↔ ((m : ℕ) < a))
  · by_cases h2 : (((k : ℕ) < a) ↔ ((j : ℕ) < a))
    · rw [hZ m k h1 h2]
      ring
    · rw [hQ k j h2]
      ring
  · rw [hP i m h1]
    ring

theorem UpperTheory.V.Pa.okX :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (χ : G.Γ →* x.A), AdOk G.frame (fun g => x.ρX X (h.p₀ g)) (fun g => algebraMap x.A X (χ g)) (Ev x.A X n x.a) ∧ AdOk G.frame (fun g => x.ρX X (h.p₀ g)) (fun g => algebraMap x.A X (χ g)) (Od x.A X n x.a) := by
  intro l _ L G G0 h n x X _ _ χ
  classical
  have hblk : ∀ g : G0.frame.G₀, ∀ i j : Fin n, ¬ (((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)) →
      x.ρX X g i j = 0 := by
    intro g i j hij
    have hz := ev_iff.mp (x.blk g) i j hij
    simp [NP.ρX, Matrix.map_apply, hz]
  have hconj : ∀ g : G.frame.G₀, h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := by
    intro g
    apply Subtype.ext
    simp [GFrame.conj, Glob.Hom.p₀, map_mul, map_inv, h.c]
  have key : ∀ (M : Matrix (Fin n) (Fin n) x.A) (E : (x.A)ˣ),
      M = (E : x.A) • (1 : Matrix (Fin n) (Fin n) x.A) →
        ∃ u : Xˣ, M.map (algebraMap x.A X) = (u : X) • (1 : Matrix (Fin n) (Fin n) X) := by
    rintro M E rfl
    refine ⟨Units.map (algebraMap x.A X).toMonoidHom E, ?_⟩
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hform : ∀ g : G.frame.G₀, ∃ u : Xˣ,
      (x.ρX X (h.p₀ g))ᵀ * x.ρX X (h.p₀ (G.frame.conj g)) =
        (u : X) • (1 : Matrix (Fin n) (Fin n) X) := by
    intro g
    have hf := x.form (h.p₀ g)
    simp only [Units.val_one, Matrix.mul_one] at hf
    obtain ⟨u, hu⟩ := key _ _ hf
    refine ⟨u, ?_⟩
    rw [← hu, hconj]
    simp only [NP.ρX, Matrix.transpose_map, Matrix.map_mul]
  refine ⟨⟨?_, ?_, hform, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, hform, ?_, ?_, ?_, ?_⟩⟩
  all_goals try (simp [NP.ρX, Matrix.map_mul]; done)
  · intro g Z hZ
    rw [ev_iff] at hZ ⊢
    intro i j hij
    rw [Matrix.smul_apply, sandwich (hblk _) (hblk _) i j
      (fun i' j' h1 h2 => hZ i' j' (fun h3 => hij (h1.trans (h3.trans h2)))), smul_zero]
  · intro Z hZ
    rw [ev_iff] at hZ ⊢
    intro i j hij
    rw [Matrix.smul_apply, Matrix.transpose_apply, hZ j i (fun h3 => hij h3.symm), smul_zero]
  · intro g Z hZ
    rw [od_iff] at hZ ⊢
    intro i j hij
    rw [Matrix.smul_apply, sandwich (hblk _) (hblk _) i j
      (fun i' j' h1 h2 => hZ i' j' (h1.symm.trans (hij.trans h2.symm))), smul_zero]
  · intro Z hZ
    rw [od_iff] at hZ ⊢
    intro i j hij
    rw [Matrix.smul_apply, Matrix.transpose_apply, hZ j i hij.symm, smul_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PhiSub
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem phi_sub (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (hΦ : PhiCond (Γ := Γ) l) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ)) : PhiCond (Γ := H) l := by
  intro K hK
  have hK' : IsOpen ((K.map H.subtype : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.coe_map]
    exact hH.isOpenMap_subtype_val _ hK
  haveI := hΦ _ hK'
  let e : K ≃* K.map H.subtype := K.equivMapOfInjective H.subtype H.subtype_injective
  have hc : Continuous (e.symm : K.map H.subtype → K) := by
    have hind : Topology.IsInducing (fun k : K => ((k : H) : Γ)) :=
      Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
    rw [hind.continuous_iff]
    have hfun : (fun k : K => ((k : H) : Γ)) ∘ e.symm = fun γ : K.map H.subtype => (γ : Γ) := by
      funext γ
      have h1 := K.coe_equivMapOfInjective_apply H.subtype H.subtype_injective (e.symm γ)
      simp only [Function.comp_apply]
      rw [← H.coe_subtype, ← h1]
      simp [e]
    rw [hfun]
    exact continuous_subtype_val
  refine Finite.of_injective
    (β := {ψ : (K.map H.subtype) →* Multiplicative (ZMod l) // IsOpen (ψ.ker : Set (K.map H.subtype))})
    (fun φ => ⟨φ.1.comp e.symm.toMonoidHom, ?_⟩) ?_
  · have hk : ((φ.1.comp e.symm.toMonoidHom).ker : Set (K.map H.subtype)) = e.symm ⁻¹' (φ.1.ker : Set K) := by
      ext γ
      exact Iff.rfl
    rw [hk]
    exact φ.2.preimage hc
  · intro φ φ' h
    apply Subtype.ext
    ext k
    have h2 := congrArg (fun ψ => ψ.1 (e k)) h
    simpa using h2

private theorem finite_addMonoidHom_zmod_of_finite (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Finite M] :
    Finite (M →+ ZMod l) := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  exact Finite.of_injective (fun f : M →+ ZMod l => (f : M → ZMod l)) DFunLike.coe_injective

private theorem eq_zero_of_forall_hom_zmod_eq_zero_of_l_smul (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] (hl : ∀ m : M, l • m = 0)
    (m : M) (h : ∀ f : M →+ ZMod l, f m = 0) : m = 0 := by
  letI : Module (ZMod l) M := AddCommGroup.zmodModule hl
  let b := Module.Basis.ofVectorSpace (ZMod l) M
  apply b.repr.injective
  ext i
  have := h (b.coord i).toAddMonoidHom
  rw [LinearEquiv.map_zero, Finsupp.coe_zero, Pi.zero_apply]
  simpa using this

theorem UpperTheory.V.Pa.finZ :
    ∀ (l : ℕ) [Fact l.Prime] (R Γ M : Type) [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R Γ M), PhiCond (Γ := Γ) l → LC ρ → (∀ m : M, l • m = 0) → Finite (Zl ρ) ∧ ∀ H : Subgroup Γ, IsOpen (H : Set Γ) → PhiCond (Γ := H) l := by
  intro l _ R Γ M _ _ _ _ _ _ _ _ ρ hΦ hρ hl
  refine ⟨?_, fun H hH => phi_sub l hΦ H hH⟩
  let N : Subgroup Γ :=
    { carrier := {g | ∀ m, ρ g m = m}
      mul_mem' := by
        intro a b ha hb m
        simp only [Set.mem_setOf_eq] at ha hb
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by
        intro m
        simp
      inv_mem' := by
        intro a ha m
        simp only [Set.mem_setOf_eq] at ha
        have h1 := ha (ρ a⁻¹ m)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h1
        exact h1.symm }
  have hN : IsOpen (N : Set Γ) := by
    have hset : (N : Set Γ) = ⋂ m : M, (fun g => ρ g m) ⁻¹' {m} := by
      ext g
      simp [N]
    rw [hset]
    exact isOpen_iInter_of_finite (fun m => (hρ m).isOpen_fiber m)
  haveI : Finite (Γ ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
  haveI : Finite (M →+ ZMod l) := finite_addMonoidHom_zmod_of_finite l M
  haveI := hΦ N hN
  have z1 : ∀ z ∈ Zl ρ, z 1 = 0 := by
    intro z hz
    have h := ((mem_Zl ρ).1 hz).2 1 1
    simpa using h
  have zN : ∀ z ∈ Zl ρ, ∀ a b : Γ, a ∈ N → z (a * b) = z a + z b := by
    intro z hz a b ha
    rw [((mem_Zl ρ).1 hz).2, ha]
  refine Finite.of_injective
    (β := (Γ ⧸ N → M) × ((M →+ ZMod l) →
      {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)}))
    (fun z => (fun q => z.1 q.out, fun f =>
      ⟨⟨⟨fun k => Multiplicative.ofAdd (f (z.1 k)), ?_⟩, ?_⟩, ?_⟩)) ?_
  · show Multiplicative.ofAdd (f (z.1 ((1 : N) : Γ))) = 1
    rw [Subgroup.coe_one, z1 _ z.2, map_zero, ofAdd_zero]
  · intro k k'
    show Multiplicative.ofAdd (f (z.1 ((k * k' : N) : Γ))) =
      Multiplicative.ofAdd (f (z.1 k)) * Multiplicative.ofAdd (f (z.1 k'))
    rw [Subgroup.coe_mul, zN _ z.2 _ _ k.2, map_add (f := _), ofAdd_add]
  · have hlc : IsLocallyConstant (fun k : N => Multiplicative.ofAdd (f (z.1 k))) :=
      (((mem_Zl ρ).1 z.2).1.comp_continuous continuous_subtype_val).comp _
    rw [MonoidHom.coe_ker]
    exact hlc.isOpen_fiber 1
  · intro z z' h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    apply Subtype.ext
    funext g
    have key : ∀ k : N, z.1 k = z'.1 k := by
      intro k
      have hf : ∀ f : M →+ ZMod l, f (z.1 k - z'.1 k) = 0 := by
        intro f
        have h3 := congrArg (fun ψ : {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)} =>
          Multiplicative.toAdd (ψ.1 k)) (congrFun h2 f)
        simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] at h3
        rw [map_sub, h3, sub_self]
      exact sub_eq_zero.1 (eq_zero_of_forall_hom_zmod_eq_zero_of_l_smul l M hl _ hf)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul N g
    have hg : g = (QuotientGroup.mk g : Γ ⧸ N).out * ((k⁻¹ : N) : Γ) := by
      rw [hk]
      simp [mul_assoc]
    have h1' : z.1 (QuotientGroup.mk g : Γ ⧸ N).out = z'.1 (QuotientGroup.mk g : Γ ⧸ N).out :=
      congrFun h1 (QuotientGroup.mk g)
    rw [hg, ((mem_Zl ρ).1 z.2).2, ((mem_Zl ρ).1 z'.2).2, key, h1']
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.TyCard
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem tc_perm {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (w : GL (Fin n) R) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, w (σ i) i ≠ 0 := by
  by_contra h
  push Not at h
  have hd : (w : Matrix (Fin n) (Fin n) R).det = 0 := by
    rw [Matrix.det_apply]
    refine Finset.sum_eq_zero fun σ _ => ?_
    obtain ⟨i, hi⟩ := h σ
    have hp : ∏ j, (w : Matrix (Fin n) (Fin n) R) (σ j) j = 0 :=
      Finset.prod_eq_zero (f := fun j => (w : Matrix (Fin n) (Fin n) R) (σ j) j) (Finset.mem_univ i) hi
    rw [hp, smul_zero]
  have hu : IsUnit (w : Matrix (Fin n) (Fin n) R).det := (Matrix.isUnit_iff_isUnit_det _).1 w.isUnit
  exact hu.ne_zero hd

private theorem tc_inv {R : Type} [CommRing R] {n : ℕ} (w : GL (Fin n) R) (b t : Fin n → Bool)
    (h : ∀ i j, b i ≠ t j → w i j = 0) (i j : Fin n) (e : t i ≠ b j) : (w⁻¹ : GL (Fin n) R) i j = 0 := by
  classical
  set M : Matrix (Fin n) (Fin n) R := (w : Matrix (Fin n) (Fin n) R) with hM
  set N : Matrix (Fin n) (Fin n) R := ((w⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) with hN
  let Dt : Matrix (Fin n) (Fin n) R := Matrix.diagonal fun k => if t k then 1 else 0
  let Db : Matrix (Fin n) (Fin n) R := Matrix.diagonal fun k => if b k then 1 else 0
  have hc : M * Dt = Db * M := by
    ext p q
    simp only [Dt, Db, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hpq : b p = t q
    · rw [hpq]; ring
    · rw [show M p q = 0 from h p q hpq]; simp
  have hNM : N * M = 1 := Units.inv_mul w
  have hMN : M * N = 1 := Units.mul_inv w
  have key : Dt * N = N * Db := by
    calc Dt * N = N * M * Dt * N := by rw [hNM, Matrix.one_mul]
      _ = N * (M * Dt) * N := by simp only [Matrix.mul_assoc]
      _ = N * (Db * M) * N := by rw [hc]
      _ = N * Db * (M * N) := by simp only [Matrix.mul_assoc]
      _ = N * Db := by rw [hMN, Matrix.mul_one]
  have hij := congrFun (congrFun key i) j
  simp only [Dt, Db, Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
  cases hti : t i <;> cases hbj : b j <;> simp [hti, hbj] at hij e ⊢ <;>
    first | exact hij | exact hij.symm

private theorem tc_same {n : ℕ} (t : Fin n → Bool) :
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 = t p.2).card =
      (Finset.univ.filter fun i => t i = true).card.choose 2 +
        (Finset.univ.filter fun i => ¬ t i = true).card.choose 2 := by
  classical
  have hU : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 = t p.2) =
      ((Finset.univ.filter fun i => t i = true) ×ˢ (Finset.univ.filter fun i => t i = true)).filter
          (fun p => p.1 < p.2) ∪
        ((Finset.univ.filter fun i => ¬ t i = true) ×ˢ
          (Finset.univ.filter fun i => ¬ t i = true)).filter (fun p => p.1 < p.2) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_product]
    cases t x <;> cases t y <;> simp
  rw [hU, Finset.card_union_of_disjoint, Finset.card_product_filter_lt,
    Finset.card_product_filter_lt]
  rw [Finset.disjoint_left]
  rintro ⟨x, y⟩ h1 h2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at h1 h2
  exact h2.1.1 h1.1.1

private theorem tc_diff {n : ℕ} (t : Fin n → Bool) :
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 ≠ t p.2).card =
      (Finset.univ.filter fun i => t i = true).card *
        (Finset.univ.filter fun i => ¬ t i = true).card := by
  classical
  have hsplit : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 = t p.2).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 ≠ t p.2).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      tauto
    · rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact h2.2.2 h1.2.2
  have htot : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card = n.choose 2 := by
    simpa using Fintype.card_product_filter_lt (α := Fin n)
  have hcard : (Finset.univ.filter fun i => t i = true).card +
      (Finset.univ.filter fun i => ¬ t i = true).card = n := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  have hch : ∀ a b : ℕ, (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
    intro a b
    induction b with
    | zero => simp
    | succ k ih =>
      rw [← Nat.add_assoc, Nat.choose_succ_succ', Nat.choose_succ_succ' k, Nat.choose_one_right,
        Nat.choose_one_right, ih]
      ring
  have hh := hch (Finset.univ.filter fun i => t i = true).card
    (Finset.univ.filter fun i => ¬ t i = true).card
  rw [hcard] at hh
  rw [htot, tc_same t] at hsplit
  linarith

theorem UpperTheory.V.Pa.tyCard :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (v : F.Vl) (g : ℕ), (Finset.univ.filter fun i => x.ty v i = true).card = x.a ∧ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x.ty v p.1 = x.ty v p.2).card + g * (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x.ty v p.1 ≠ x.ty v p.2).card = nu n x.a g ∧ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x.ty v p.1 ≠ x.ty v p.2).card = x.a * (n - x.a) ∧ ∀ i j : Fin n, x.ty v i ≠ decide ((j : ℕ) < x.a) → ((x.w v)⁻¹ : GL (Fin n) x.A) i j = 0 := by
  intro l _ F n x v g
  classical
  obtain ⟨σ, hσ⟩ := tc_perm (x.w v)
  have hty : ∀ j, x.ty v j = decide (((σ j : Fin n) : ℕ) < x.a) := by
    intro j
    by_contra hne
    exact hσ j (x.w_blk v (σ j) j (Ne.symm hne))
  have hT : (Finset.univ.filter fun i => x.ty v i = true).card = x.a := by
    rw [← Fintype.card_subtype, ← Fintype.card_fin_lt_of_le x.a_le]
    refine Fintype.card_congr (Equiv.subtypeEquiv σ fun j => ?_)
    rw [hty j]
    simp
  have hF : (Finset.univ.filter fun i => ¬ x.ty v i = true).card = n - x.a := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => x.ty v i = true)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  refine ⟨hT, ?_, ?_, ?_⟩
  · rw [tc_same, tc_diff, hT, hF]
    simp [nu]
  · rw [tc_diff, hT, hF]
  · intro i j e
    exact tc_inv (x.w v) (fun k => decide ((k : ℕ) < x.a)) (x.ty v)
      (fun p q hpq => x.w_blk v p q hpq) i j e
end
