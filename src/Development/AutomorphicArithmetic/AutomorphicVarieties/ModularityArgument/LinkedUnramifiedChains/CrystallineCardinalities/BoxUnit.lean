module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.SelLow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ZpowWNe

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.RankTwo
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

private theorem tors_card {O : Type} [CommRing O] (I : Ideal O) [Finite (O ⧸ I)] (c : O)
    [Finite (O ⧸ Ideal.span {c})] :
    Nat.card {x : O ⧸ I // c • x = 0} ≤ Nat.card (O ⧸ Ideal.span {c}) := by
  let φ : (O ⧸ I) →ₗ[O] (O ⧸ I) := c • LinearMap.id
  have hφ : ∀ x, φ x = c • x := fun x => rfl
  have hker : Nat.card {x : O ⧸ I // c • x = 0} = Nat.card (LinearMap.ker φ) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [LinearMap.mem_ker, hφ]))
  have hA1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ)
  have hA2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range φ)
  have hq : Nat.card ((O ⧸ I) ⧸ LinearMap.ker φ) = Nat.card (LinearMap.range φ) :=
    Nat.card_congr (φ.quotKerEquivRange).toEquiv
  have hpos : 0 < Nat.card (LinearMap.range φ) := Nat.card_pos
  have heq : Nat.card (LinearMap.ker φ) = Nat.card ((O ⧸ I) ⧸ LinearMap.range φ) := by
    rw [hq] at hA1
    have h : Nat.card (LinearMap.range φ) * Nat.card (LinearMap.ker φ) =
        Nat.card (LinearMap.range φ) * Nat.card ((O ⧸ I) ⧸ LinearMap.range φ) := by
      rw [mul_comm, ← hA1, hA2]
    exact Nat.eq_of_mul_eq_mul_left hpos h
  rw [hker, heq]
  let g : O →ₗ[O] (O ⧸ I) ⧸ LinearMap.range φ := (LinearMap.range φ).mkQ ∘ₗ (Submodule.mkQ I)
  have hg : Submodule.span O {c} ≤ LinearMap.ker g := by
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    simp only [g, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨Submodule.Quotient.mk 1, ?_⟩
    rw [hφ, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  refine Nat.card_le_card_of_surjective ((Submodule.span O {c}).liftQ g hg) ?_
  intro z
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨o, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact ⟨Submodule.Quotient.mk o, rfl⟩

private theorem hom_alt {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    (hfin : ∀ c : O, c ≠ 0 → Finite (O ⧸ Ideal.span {c}))
    (Q : Type) [AddCommGroup Q] [Module O Q] [Module.Finite O Q] :
    (∃ f g : Q →ₗ[O] O, ∃ x y : Q, f x = 1 ∧ g x = 0 ∧ f y = 0 ∧ g y = 1) ∨
    ∃ C : ℕ, ∀ I : Ideal O, Finite (O ⧸ I) → Nat.card (Q →ₗ[O] O ⧸ I) ≤ Nat.card (O ⧸ I) * C := by
  classical
  obtain ⟨n, ι, _, p, hp, e, ⟨E⟩⟩ := Module.equiv_free_prod_directSum O Q
  by_cases hn : 2 ≤ n
  · left
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    refine ⟨(Finsupp.lapply i0) ∘ₗ (LinearMap.fst O _ _) ∘ₗ E.toLinearMap,
      (Finsupp.lapply i1) ∘ₗ (LinearMap.fst O _ _) ∘ₗ E.toLinearMap,
      E.symm (Finsupp.single i0 1, 0), E.symm (Finsupp.single i1 1, 0), ?_, ?_, ?_, ?_⟩ <;>
    simp [i0, i1, Finsupp.single_apply]
  · right
    have hq : ∀ i, p i ^ e i ≠ 0 := fun i => pow_ne_zero _ (hp i).ne_zero
    haveI : ∀ i, Finite (O ⧸ Ideal.span {p i ^ e i}) := fun i => hfin _ (hq i)
    refine ⟨∏ i, Nat.card (O ⧸ Ideal.span {p i ^ e i}), fun I hI => ?_⟩
    have htor : ∀ (φ : Q →ₗ[O] O ⧸ I) (i : ι), (p i ^ e i) • φ (E.symm (0,
        DirectSum.lof O ι (fun i => O ⧸ O ∙ p i ^ e i) i (Submodule.Quotient.mk 1))) = 0 := by
      intro φ i
      rw [← map_smul, ← map_smul, Prod.smul_mk, smul_zero, ← map_smul, ← Submodule.Quotient.mk_smul,
        smul_eq_mul, mul_one, (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self _),
        map_zero, Prod.mk_zero_zero, map_zero, map_zero]
    let F : (Q →ₗ[O] O ⧸ I) → (Fin n → O ⧸ I) × ((i : ι) → {x : O ⧸ I // (p i ^ e i) • x = 0}) :=
      fun φ => (fun j => φ (E.symm (Finsupp.single j 1, 0)), fun i => ⟨_, htor φ i⟩)
    have hF : Function.Injective F := by
      intro φ ψ h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      have key : φ ∘ₗ E.symm.toLinearMap = ψ ∘ₗ E.symm.toLinearMap := by
        apply LinearMap.prod_ext
        · apply Finsupp.lhom_ext
          intro j b
          have hj := congrFun h1 j
          rw [← Finsupp.smul_single_one, map_smul, map_smul]
          exact congrArg (b • ·) hj
        · apply DirectSum.linearMap_ext
          intro i
          apply Submodule.linearMap_qext
          apply LinearMap.ext_ring
          exact congrArg Subtype.val (congrFun h2 i)
      ext x
      simpa using LinearMap.congr_fun key (E x)
    have hcard := Nat.card_le_card_of_injective F hF
    rw [Nat.card_prod, Nat.card_pi, Nat.card_pi, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hcard
    have hP : ∏ i, Nat.card {x : O ⧸ I // (p i ^ e i) • x = 0} ≤
        ∏ i, Nat.card (O ⧸ Ideal.span {p i ^ e i}) :=
      Finset.prod_le_prod' (fun i _ => tors_card I (p i ^ e i))
    have hpos : 0 < Nat.card (O ⧸ I) := Nat.card_pos
    have hpow : Nat.card (O ⧸ I) ^ n ≤ Nat.card (O ⧸ I) :=
      calc Nat.card (O ⧸ I) ^ n ≤ Nat.card (O ⧸ I) ^ 1 := Nat.pow_le_pow_right hpos (by omega)
        _ = Nat.card (O ⧸ I) := pow_one _
    exact hcard.trans (Nat.mul_le_mul hpow hP)

private def rel {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (ξ : R →ₐ[O] O) (T : Set R) : Submodule O R :=
  Submodule.span O ({x | ∃ a b, x = a * b - (ξ a • b + ξ b • a)} ∪ T)

private theorem rel_le {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (ξ : R →ₐ[O] O) (T : Set R)
    {X : Type} [AddCommGroup X] [Module O X] (δ : R →ₗ[O] X) :
    rel ξ T ≤ LinearMap.ker δ ↔ (∀ a b, δ (a * b) = ξ a • δ b + ξ b • δ a) ∧ ∀ a ∈ T, δ a = 0 := by
  unfold rel
  rw [Submodule.span_le, Set.union_subset_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a b => ?_, fun a ha => LinearMap.mem_ker.mp (h2 ha)⟩
    have h := h1 ⟨a, b, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_add (f := _), map_smul, map_smul, sub_eq_zero] at h
    exact h
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun a ha => LinearMap.mem_ker.mpr (h2 a ha)⟩
    rintro x ⟨a, b, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_add (f := _), map_smul, map_smul, sub_eq_zero]
    exact h1 a b

private theorem rel_fin {O R : Type} [CommRing O] [CommRing R] [Algebra O R] [IsNoetherianRing R] (ξ : R →ₐ[O] O)
    (T : Set R) : Module.Finite O (R ⧸ rel ξ T) := by
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian (RingHom.ker ξ) : (RingHom.ker ξ).FG)
  have hS' : Ideal.span (S : Set R) = RingHom.ker ξ := hS
  have hrel : ∀ a b, a * b - (ξ a • b + ξ b • a) ∈ rel ξ T := fun a b =>
    Submodule.subset_span (Or.inl ⟨a, b, rfl⟩)
  have hmm : ∀ a b, ξ a = 0 → ξ b = 0 → a * b ∈ rel ξ T := by
    intro a b ha hb
    have h := hrel a b
    rwa [ha, hb, zero_smul, zero_smul, add_zero, sub_zero] at h
  have hker : ∀ x, x ∈ Ideal.span (S : Set R) → x ∈ Submodule.span O (S : Set R) ⊔ rel ξ T := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.mem_sup_left (Submodule.subset_span hx)
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul r x hxS hx =>
      have hxk : ξ x = 0 := by
        have h := hxS
        rw [hS, RingHom.mem_ker] at h
        exact h
      have h1 : r • x = ξ r • x + (r - ξ r • 1) * x := by
        rw [smul_eq_mul, sub_mul, smul_mul_assoc, one_mul]
        abel
      rw [h1]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ hx) (Submodule.mem_sup_right (hmm _ _ ?_ hxk))
      simp
  have h1 : (1 : R) ∈ rel ξ T := by
    have h := hrel 1 1
    rw [map_one, one_smul, mul_one] at h
    have h2 : (1 : R) - (1 + 1) = -1 := by ring
    rw [h2] at h
    exact neg_mem_iff.mp h
  have htop : ∀ r : R, r ∈ Submodule.span O (S : Set R) ⊔ rel ξ T := by
    intro r
    have hmem : r - ξ r • 1 ∈ Ideal.span (S : Set R) := by
      rw [hS', RingHom.mem_ker]
      simp
    rw [← sub_add_cancel r (ξ r • 1)]
    exact Submodule.add_mem _ (hker _ hmem) (Submodule.mem_sup_right (Submodule.smul_mem _ _ h1))
  haveI : Module.Finite O (Submodule.span O (S : Set R)) := Module.Finite.span_of_finite O S.finite_toSet
  refine Module.Finite.of_surjective ((rel ξ T).mkQ ∘ₗ (Submodule.span O (S : Set R)).subtype) ?_
  intro q
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨n, hn, m, hm, hnm⟩ := Submodule.mem_sup.mp (htop r)
  refine ⟨⟨n, hn⟩, ?_⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply]
  rw [← hnm]
  exact (Submodule.Quotient.eq _).mpr (by simpa using hm)

end UpperTheory.V.Z.J

private theorem finite_linearMap_of_finite_module_finite {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N]
    [Module O N] [Module.Finite O M] [Finite N] : Finite (M →ₗ[O] N) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := M)
  refine Finite.of_injective (fun φ : M →ₗ[O] N => fun x : (s : Set M) => φ x) ?_
  intro φ ψ h
  exact LinearMap.ext_on hs (fun x hx => congrFun h ⟨x, hx⟩)

theorem UpperTheory.V.Z.J.rankTwo :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (ξ : R →ₐ[O] O) (T : Set R) (C : ℕ), (l : O) ≠ 0 → (∀ k, 0 < k → ∀ X : Set (R →ₗ[O] Ok l O k), X = {δ | (∀ a b, δ (a * b) = ξ a • δ b + ξ b • δ a) ∧ ∀ a ∈ T, δ a = 0} → X.Finite → Nat.card (Ok l O k) ^ 2 ≤ C * X.ncard) → ∃ δ δ' : R →ₗ[O] O, (∀ a b, δ (a * b) = ξ a • δ b + ξ b • δ a) ∧ (∀ a ∈ T, δ a = 0) ∧ (∀ a b, δ' (a * b) = ξ a • δ' b + ξ b • δ' a) ∧ (∀ a ∈ T, δ' a = 0) ∧ LinearIndependent O ![δ, δ'] := by
  intro l _ O _ _ _ _ _ R _ _ _ ξ T C hl hX
  obtain ⟨hOk, hfin, -, h2k, -, -, -⟩ := okFin l O hl
  haveI : Module.Finite O (R ⧸ rel ξ T) := rel_fin ξ T
  have hder : ∀ {Y : Type} [AddCommGroup Y] [Module O Y] (φ : (R ⧸ rel ξ T) →ₗ[O] Y),
      (∀ a b, (φ ∘ₗ (rel ξ T).mkQ) (a * b) =
        ξ a • (φ ∘ₗ (rel ξ T).mkQ) b + ξ b • (φ ∘ₗ (rel ξ T).mkQ) a) ∧
      ∀ a ∈ T, (φ ∘ₗ (rel ξ T).mkQ) a = 0 := by
    intro Y _ _ φ
    refine (rel_le ξ T (φ ∘ₗ (rel ξ T).mkQ)).mp ?_
    intro x hx
    simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero _).mpr hx]
  rcases hom_alt hfin (R ⧸ rel ξ T) with ⟨f, g, x, y, hfx, hgx, hfy, hgy⟩ | ⟨C', hC'⟩
  · obtain ⟨x0, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine ⟨f ∘ₗ (rel ξ T).mkQ, g ∘ₗ (rel ξ T).mkQ, (hder f).1, (hder f).2, (hder g).1, (hder g).2, ?_⟩
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun δ => δ x0) hst
    have h2 := congrArg (fun δ => δ y0) hst
    simp [hfx, hgx, hfy, hgy] at h1 h2
    exact ⟨h1, h2⟩
  · exfalso
    obtain ⟨D, hD⟩ : ∃ D, D = C * C' := ⟨_, rfl⟩
    obtain ⟨k, hkD⟩ : ∃ k, k = D + 1 := ⟨_, rfl⟩
    have hk : 0 < k := by omega
    haveI := hOk k
    haveI : Finite ((R ⧸ rel ξ T) →ₗ[O] Ok l O k) := finite_linearMap_of_finite_module_finite
    let Φ : ((R ⧸ rel ξ T) →ₗ[O] Ok l O k) → (R →ₗ[O] Ok l O k) := fun φ => φ ∘ₗ (rel ξ T).mkQ
    have hΦinj : Function.Injective Φ := fun φ ψ h => Submodule.linearMap_qext _ h
    have hrange : Set.range Φ = {δ : R →ₗ[O] Ok l O k | (∀ a b, δ (a * b) = ξ a • δ b + ξ b • δ a) ∧
        ∀ a ∈ T, δ a = 0} := by
      ext δ
      constructor
      · rintro ⟨φ, rfl⟩
        exact hder φ
      · intro hδ
        exact ⟨(rel ξ T).liftQ δ ((rel_le ξ T δ).mpr hδ), Submodule.liftQ_mkQ _ _ _⟩
    have hcard := hX k hk (Set.range Φ) hrange (Set.finite_range Φ)
    rw [Set.ncard_range_of_injective hΦinj] at hcard
    have hbound := hC' (Ideal.span {(l : O) ^ k}) (hOk k)
    have hpos : 0 < Nat.card (Ok l O k) := Nat.card_pos
    have h2 := h2k k
    have hle : Nat.card (Ok l O k) ≤ D := by
      have h3 : Nat.card (Ok l O k) * Nat.card (Ok l O k) ≤ Nat.card (Ok l O k) * D := by
        calc Nat.card (Ok l O k) * Nat.card (Ok l O k) = Nat.card (Ok l O k) ^ 2 := (sq _).symm
          _ ≤ C * Nat.card ((R ⧸ rel ξ T) →ₗ[O] Ok l O k) := hcard
          _ ≤ C * (Nat.card (Ok l O k) * C') := Nat.mul_le_mul_left _ hbound
          _ = Nat.card (Ok l O k) * D := by rw [hD]; ring
      exact Nat.le_of_mul_le_mul_left h3 hpos
    have h4 : k < 2 ^ k := Nat.lt_two_pow_self
    omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LiftOfBar
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

private theorem sq_exp {C Q : Type} [CommRing C] [CommRing Q] (n : ℕ) (π : C →+* Q) (μ : Q →+ C)
    (hm : ∀ a c, μ (π a * c) = a * μ c) (h0 : ∀ c, π (μ c) = 0) :
    ∃ e : Matrix (Fin n) (Fin n) Q → GL (Fin n) C, (∀ X, (e X : Matrix (Fin n) (Fin n) C) = 1 + X.map μ) ∧
      (∀ X Y, e (X + Y) = e X * e Y) ∧ (∀ X, (e X)⁻¹ = e (-X)) ∧
      ∀ (x : GG (m := n) (R := C)) (X : Matrix (Fin n) (Fin n) Q),
        x * GG.ofGL (e X) = GG.ofGL (e ((GG.map π x).adFun X)) * x := by
  have hL : ∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) Q),
      A * X.map μ = (A.map π * X).map μ := fun A X => by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, hm]
  have hR : ∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) Q),
      X.map μ * A = (X * A.map π).map μ := fun A X => by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (X i k), hm, mul_comm]
  have h1 : ∀ X Y : Matrix (Fin n) (Fin n) Q, X.map μ * Y.map μ = 0 := fun X Y => by
    rw [hL]
    have : (X.map μ).map π = 0 := by
      ext i j
      exact h0 _
    rw [this, Matrix.zero_mul]
    ext i j
    simp
  have hadd : ∀ X Y : Matrix (Fin n) (Fin n) Q,
      (1 + X.map μ) * (1 + Y.map μ) = 1 + (X + Y).map μ := fun X Y => by
    have : (X + Y).map μ = X.map μ + Y.map μ := by
      ext i j
      simp
    rw [this, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h1]
    simp only [Matrix.one_mul, Matrix.mul_one]
    abel
  have hz : (0 : Matrix (Fin n) (Fin n) Q).map μ = 0 := by
    ext i j
    simp
  let e : Matrix (Fin n) (Fin n) Q → GL (Fin n) C := fun X =>
    ⟨1 + X.map μ, 1 + (-X).map μ, by rw [hadd, add_neg_cancel, hz, add_zero],
      by rw [hadd, neg_add_cancel, hz, add_zero]⟩
  have he : ∀ X, (e X : Matrix (Fin n) (Fin n) C) = 1 + X.map μ := fun X => rfl
  have hinv : ∀ X, (e X)⁻¹ = e (-X) := fun X => Units.ext rfl
  have hconj : ∀ (a : GL (Fin n) C) (X : Matrix (Fin n) (Fin n) Q),
      a * e X = e ((a : Matrix (Fin n) (Fin n) C).map π * X *
        (((GeneralLinearGroup.map π a)⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) Q)) * a := fun a X => by
    apply Units.ext
    have h1 : (((GeneralLinearGroup.map π a)⁻¹ : GL (Fin n) _) :
          Matrix (Fin n) (Fin n) Q) * (a : Matrix (Fin n) (Fin n) C).map π = 1 :=
      (GeneralLinearGroup.map π a).inv_mul
    rw [Units.val_mul, Units.val_mul, he, he, Matrix.mul_add, Matrix.add_mul, hL, hR, Matrix.mul_assoc,
      h1, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul]
  have hth : ∀ X, theta (e X) = e (thetaLie X) := fun X => by
    apply Units.ext
    have hJ : (Jmat C n).map π = Jmat Q n := Jmat_map π n
    rw [theta_val, hinv, he, he, Matrix.transpose_add, Matrix.transpose_one, ← Matrix.transpose_map,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Jmat_mul_Jmat, hL, hR, hJ, thetaLie,
      Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul]
  refine ⟨e, he, fun X Y => Units.ext (hadd X Y).symm, hinv, ?_⟩
  rintro ⟨a, s⟩ X
  have hm : ((-1 : ℤˣ) = 1) = False := by decide
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      sgnAct_one, GG.adFun, GG.map_right]
    rcases Int.units_eq_one_or s with rfl | rfl
    · simp only [sgnAct_one, if_true]
      exact hconj a X
    · simp only [sgnAct_neg_one, hm, if_false, hth]
      exact hconj a _
  · simp

private theorem upT_mul {C : Type} [CommRing C] {n : ℕ} {A B : Matrix (Fin n) (Fin n) C} (hA : UpT A) (hB : UpT B) :
    UpT (A * B) ∧ ∀ i, (A * B) i i = A i i * B i i := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rcases lt_or_ge b i with h' | h'
    · rw [hA i b h', zero_mul]
    · rw [hB b j (lt_of_lt_of_le h h'), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h' | h'
      · rw [hA i b h', zero_mul]
      · rw [hB b i h', mul_zero]
    · simp

private theorem box_def {l : ℕ} [Fact l.Prime] {κ : Type} [Field κ] {F : Frame l κ} {n : ℕ}
    {C Q : Type} [CommRing C] [CommRing Q] (π : C →+* Q) (μ : Q →+ C)
    (hm : ∀ a c, μ (π a * c) = a * μ c) (h0 : ∀ c, π (μ c) = 0) (B : Box F n C)
    (z : F.Γ → Matrix (Fin n) (Fin n) Q) (hz : ∀ s t, z (s * t) = z s + (B.map π).ad s (z t))
    (z' : ∀ v, F.Gv v → Matrix (Fin n) (Fin n) Q) (Y : F.V → Matrix (Fin n) (Fin n) Q)
    (hz' : ∀ v s, UpT (z' v s))
    (hY : ∀ v s, z (F.loc v s) = ((((B.map π).g v)⁻¹ : GL (Fin n) Q) : Matrix (Fin n) (Fin n) Q) * z' v s *
      ((B.map π).g v : Matrix (Fin n) (Fin n) Q) + ((B.map π).ad (F.loc v s) (Y v) - Y v)) :
    ∃ B' : Box F n C, (∀ s, (B'.r s).mat = (1 + (z s).map μ) * (B.r s).mat) ∧
      ∀ v s i, ((B'.g v : Matrix (Fin n) (Fin n) C) * (B'.r (F.loc v s)).mat *
        (((B'.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) i i =
        (1 + μ (z' v s i i)) * ((B.g v : Matrix (Fin n) (Fin n) C) * (B.r (F.loc v s)).mat *
        (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) i i := by
  obtain ⟨e, e1, e2, e3, e4⟩ := sq_exp n π μ hm h0
  have e5 : ∀ s X, B.r s * GG.ofGL (e X) = GG.ofGL (e ((B.map π).ad s X)) * B.r s := fun s X => e4 _ X
  have z1 : z 1 = 0 := by
    have := hz 1 1
    rw [mul_one, map_one, Module.End.one_apply] at this
    exact left_eq_add.1 this
  have e0 : e 0 = 1 := by
    have := e2 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  let r : F.Γ →* GG (m := n) (R := C) :=
    { toFun := fun s => GG.ofGL (e (z s)) * B.r s
      map_one' := by rw [z1, e0, map_one, map_one, mul_one]
      map_mul' := fun s t => by
        rw [hz, e2, map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (B.r s), e5, mul_assoc] }
  have hl : ∀ s, (r s).left = e (z s) * (B.r s).left := fun s => by
    show (GG.ofGL (e (z s)) * B.r s).left = _
    simp
  have hloc : ∀ v s, (B.r (F.loc v s)).right = 1 := fun v s => (B.nu _).trans (F.loc0 v s).2
  have key : ∀ v s, (B.g v * e (Y v)) * (r (F.loc v s)).left * (B.g v * e (Y v))⁻¹ =
      e (z' v s) * (B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹) := fun v s => by
    have a1 : (B.r (F.loc v s)).left * e (-Y v) = e (-(B.map π).ad (F.loc v s) (Y v)) * (B.r (F.loc v s)).left := by
      have := congrArg SemidirectProduct.left (e5 (F.loc v s) (-Y v))
      simpa [hloc] using this
    have a2 : ∀ X, B.g v * e X = e (((B.map π).g v : Matrix (Fin n) (Fin n) Q) * X *
        ((((B.map π).g v)⁻¹ : GL (Fin n) Q) : Matrix (Fin n) (Fin n) Q)) * B.g v := fun X => by
      have := congrArg SemidirectProduct.left (e4 (GG.ofGL (B.g v)) X)
      simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
        sgnAct_one, GG.adFun, GG.map_right, if_true] at this
      exact this
    have a3 : Y v + (z (F.loc v s) + -(B.map π).ad (F.loc v s) (Y v)) =
        ((((B.map π).g v)⁻¹ : GL (Fin n) Q) : Matrix (Fin n) (Fin n) Q) * z' v s *
          ((B.map π).g v : Matrix (Fin n) (Fin n) Q) := by
      rw [hY]
      abel
    calc _ = B.g v * (e (Y v) * (e (z (F.loc v s)) * ((B.r (F.loc v s)).left * e (-Y v)))) * (B.g v)⁻¹ := by
          rw [hl, _root_.mul_inv_rev, e3]
          simp only [mul_assoc]
      _ = B.g v * e (Y v + (z (F.loc v s) + -(B.map π).ad (F.loc v s) (Y v))) *
          (B.r (F.loc v s)).left * (B.g v)⁻¹ := by
          rw [a1, e2, e2]
          simp only [mul_assoc]
      _ = _ := by
          rw [a3, a2]
          simp only [mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Units.mul_inv_cancel_left]
  have key' : ∀ v s, ((B.g v * e (Y v) : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) * (r (F.loc v s)).mat *
      (((B.g v * e (Y v))⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) = (1 + (z' v s).map μ) *
      ((B.g v : Matrix (Fin n) (Fin n) C) * (B.r (F.loc v s)).mat *
        (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) := fun v s => by
    rw [← e1]
    exact congrArg Units.val (key v s)
  have hu : ∀ v s, UpT (1 + (z' v s).map μ) := fun v s i j h => by
    rw [Matrix.add_apply, Matrix.map_apply, hz' v s i j h, map_zero, add_zero, Matrix.one_apply_ne h.ne']
  refine ⟨⟨r, fun s => ?_, fun v => B.g v * e (Y v), fun v s => ?_⟩, fun s => ?_, fun v s i => ?_⟩
  · show (GG.ofGL (e (z s)) * B.r s).right = _
    simp [B.nu]
  · rw [key']
    exact (upT_mul (hu v s) (B.tri v s)).1
  · rw [← e1]
    exact congrArg Units.val (hl s)
  · dsimp only
    rw [key', (upT_mul (hu v s) (B.tri v s)).2]
    simp

private theorem ac_map {O R R' Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] [TopologicalSpace Γ] (f : R →ₐ[O] R') {u : Γ → R}
    (h : AdicCont (maximalIdeal R) u) : AdicCont (maximalIdeal R') fun g => f (u g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  exact (h N).comp (Ideal.quotientMap _ (f : R →+* R') hle)

private theorem ac_lc {X C : Type} [TopologicalSpace X] [CommRing C] {n : ℕ} (I : Ideal C)
    (a m : X → Matrix (Fin n) (Fin n) C) (ha : IsLocallyConstant a) (hm : ∀ i j, AdicCont I fun s => m s i j)
    (i j : Fin n) : AdicCont I fun s => (a s * m s) i j := by
  intro N
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h : ∀ᶠ y in nhds x, ∀ p q, Ideal.Quotient.mk (I ^ N) (m y p q) = Ideal.Quotient.mk (I ^ N) (m x p q) :=
    Filter.eventually_all.2 fun p => Filter.eventually_all.2 fun q =>
      (IsLocallyConstant.iff_eventually_eq _).1 (hm p q N) x
  refine (h.and ((IsLocallyConstant.iff_eventually_eq _).1 ha x)).mono fun y hy => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, hy.1, hy.2]

private theorem lift_of_bar {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
    {n : ℕ} {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']
    (f : R →ₐ[O] R') (ρ : NRep F n R) :
    (ρ.map (f : R →+* R')).map (res O R' : R' →+* ResidueField O) = ρ.map (res O R : R →+* ResidueField O) := by
  rw [NRep.map_map]
  congr 1
  exact RingHom.ext fun x => res_map f x

private theorem sq_mul {O Q : Type} [CommRing O] [CommRing Q] [Algebra O Q] [Module Oᵐᵒᵖ Q] [IsCentralScalar O Q] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) Q) (A : Matrix (Fin n) (Fin n) O) (i j : Fin n) :
    (((1 + X.map (TrivSqZeroExt.inr : Q → TrivSqZeroExt O Q)) * A.map TrivSqZeroExt.inl :
      Matrix (Fin n) (Fin n) (TrivSqZeroExt O Q)) i j) =
      TrivSqZeroExt.inl (A i j) + TrivSqZeroExt.inr ((X * A.map (algebraMap O Q)) i j) := by
  rw [Matrix.add_mul, Matrix.one_mul]
  ext
  · simp [Matrix.mul_apply, TrivSqZeroExt.fst_sum]
  · simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum, Algebra.smul_def, mul_comm]

private theorem sq_facts {O Q : Type} [CommRing O] [CommRing Q] [Algebra O Q] [Module Oᵐᵒᵖ Q] [IsCentralScalar O Q] :
    (∀ (a : TrivSqZeroExt O Q) (c : Q), TrivSqZeroExt.inr (algebraMap O Q a.fst * c) = a * TrivSqZeroExt.inr c) ∧
    (∀ (a : O) (c : Q), (TrivSqZeroExt.inl a + TrivSqZeroExt.inr c : TrivSqZeroExt O Q).fst = a) ∧
    (∀ (a : O) (c : Q), (TrivSqZeroExt.inl a + TrivSqZeroExt.inr c : TrivSqZeroExt O Q).snd = c) ∧
    (∀ (a : O) (c : Q), ((1 + TrivSqZeroExt.inr c) * TrivSqZeroExt.inl a : TrivSqZeroExt O Q).fst = a) ∧
    (∀ a : O, ((1 + TrivSqZeroExt.inr (0 : Q)) * TrivSqZeroExt.inl a : TrivSqZeroExt O Q).snd = 0) :=
  ⟨fun a c => by ext <;> simp [Algebra.smul_def], by simp, by simp, by simp, by simp⟩

theorem UpperTheory.V.Z.J.derOf :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (S : Space O F 3) (ξ : S.R →ₐ[O] O) (B : Box F 3 O), B.Of (S.ρ.map (ξ : S.R →+* O)) → B.Cont (maximalIdeal O) → ∀ k, 0 < k → ∀ z ∈ ZN B k, ∃ δ ∈ WDer S.ρ ξ (Ok l O k), ∀ (s : F.G0) i j, δ (S.ρ.r s i j) = (z s * ((boxK B k).r s).mat) i j := by
  intro l _ O _ _ _ _ _ F C₀ hF _ S ξ B hB hC k _ z hz
  obtain ⟨⟨⟨z1, z2⟩, z3⟩, z4, z5⟩ := hz
  choose z' hz' Y hY using z3
  let Q := Ok l O k
  let C := TrivSqZeroExt O Q
  obtain ⟨q1, q2, q3, q4, q5⟩ := sq_facts (O := O) (Q := Q)
  haveI : IsCO O C := co_sqz O O Q fun _ => rfl
  let φ : C →ₐ[O] O := TrivSqZeroExt.fstHom O O Q
  let ι : O →ₐ[O] C := Algebra.ofId O C
  let π : C →+* Q := (Ideal.Quotient.mk _).comp (φ : C →+* O)
  let μ : Q →+ C := (TrivSqZeroExt.inrHom O Q).toAddMonoidHom
  have hm : ∀ a c, μ (π a * c) = a * μ c := q1
  obtain ⟨B', b1, b2⟩ := box_def π μ hm (fun c => map_zero (Ideal.Quotient.mk _)) (B.map (ι : O →+* C)) z z2 z' Y
    (fun v => (hz' v).2.2.1) hY
  have b3 : ∀ s i j, (B'.r s).mat i j = TrivSqZeroExt.inl ((B.r s).mat i j) +
      TrivSqZeroExt.inr ((z s * ((boxK B k).r s).mat) i j) := fun s i j => by
    rw [b1]
    exact sq_mul (z s) (B.r s).mat i j
  obtain ⟨ρ', h1, h2⟩ := pr_ofbox hF C (maximalIdeal C) B'
    (by
      refine Matrix.ext fun i j => ?_
      rw [b3, z4, hB.atc, Matrix.zero_mul, Matrix.zero_apply, TrivSqZeroExt.inr_zero, add_zero]
      by_cases h : i = j <;> simp [h, Matrix.one_apply])
    (fun i j h => by
      have a1 := z5 i j h
      have a2 := (S.ρ.map (ξ : S.R →+* O)).diag i j h
      rw [← hB.res, ← hB.res] at a2
      rw [Matrix.sub_apply, sub_eq_zero] at a1 a2 ⊢
      rw [b3, b3, a1, a2])
    (fun i j => by
      simp only [b1]
      exact ac_lc _ _ _ (z1.comp fun M => 1 + M.map μ) (fun p q => ac_map ι (hC p q)) i j)
  have b4 : ∀ v s i, (ρ'.ψ v i s : C) = (1 + TrivSqZeroExt.inr (z' v s i i)) *
      TrivSqZeroExt.inl (ξ (S.ρ.ψ v i s : S.R)) := fun v s i => by
    rw [← h1.psi, ← h1.res]
    refine (b2 v s i).trans ?_
    congr 1
    have hψ := hB.psi v i s
    rw [← hB.res] at hψ
    calc
      _ = ((ι : O →+* C).mapMatrix
          ((B.g v : Matrix (Fin 3) (Fin 3) O) * (B.r (F.loc v s)).mat *
            (((B.g v)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O))) i i := by
        rw [map_mul, map_mul]
        rfl
      _ = _ := congrArg ι hψ
  have h3 : ρ'.map (φ : C →+* O) = S.ρ.map (ξ : S.R →+* O) := by
    refine NRep.ext (MonoidHom.ext fun s => Matrix.ext fun i j => ?_)
      (funext fun v => funext fun i => MonoidHom.ext fun s => Units.ext ?_)
    · show (ρ'.r s i j).fst = _
      rw [← h1.res, b3, ← hB.res]
      exact q2 _ _
    · show (ρ'.ψ v i s : C).fst = ξ (S.ρ.ψ v i s : S.R)
      rw [b4]
      exact q4 _ _
  have h4 : ρ'.map (res O C : C →+* ResidueField O) = S.ρ.map (res O S.R : S.R →+* ResidueField O) := by
    rw [← lift_of_bar φ, h3, lift_of_bar]
  obtain ⟨f, hf, -⟩ := S.univ C ρ' ⟨h2, by rw [h4]; exact S.lift.2⟩
  obtain ⟨g, -, hg⟩ := S.univ O (S.ρ.map (ξ : S.R →+* O))
    ⟨⟨fun i j => ac_map ξ (S.lift.1.1 i j), fun v i => ac_map ξ (S.lift.1.2 v i)⟩, by
      rw [lift_of_bar]; exact S.lift.2⟩
  have h5 : φ.comp f = ξ := (hg _ (by rw [← h3, ← hf]; rfl)).trans (hg ξ rfl).symm
  have h6 : ∀ a, (f a).fst = ξ a := fun a => AlgHom.congr_fun h5 a
  refine ⟨(TrivSqZeroExt.sndHom O Q).comp f.toLinearMap, ⟨fun a b => ?_, fun v j s hs => ?_⟩, fun s i j => ?_⟩
  · show (f (a * b)).snd = ξ a • (f b).snd + ξ b • (f a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, h6, h6, op_smul_eq_smul]
  · show ((S.ρ.map (f : S.R →+* C)).ψ v j s : C).snd = 0
    rw [hf, b4, (hz' v).2.2.2 s hs]
    exact q5 _
  · show ((S.ρ.map (f : S.R →+* C)).r s i j).snd = _
    rw [hf, ← h1.res, b3]
    exact q3 _ _
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
  {F : Frame l (ResidueField O)}

private theorem adicCont_comp_ringHom_of_map_le {Γ R R' : Type} [TopologicalSpace Γ] [CommRing R] [CommRing R'] (f : R →+* R')
    {I : Ideal R} {J : Ideal R'} (hIJ : I.map f ≤ J) {a : Γ → R} (ha : AdicCont I a) :
    AdicCont J (fun g => f (a g)) := by
  intro N
  have h : I ^ N ≤ (J ^ N).comap f := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hIJ N
  have := (ha N).comp (Ideal.quotientMap (J ^ N) f h)
  convert this using 1
  funext g
  simp [Ideal.quotientMap_mk]

private theorem lift_pt (S : Space O F 3) (ξ : S.R →ₐ[O] O) : UpperTheory.V.Fr.IsLift O (S.ρ.map (ξ : S.R →+* O)) := by
  have hres : (res O O : O →+* ResidueField O).comp (ξ : S.R →+* O) = (res O S.R : S.R →+* ResidueField O) :=
    RingHom.ext fun x => res_map ξ x
  have hm : (maximalIdeal S.R).map (ξ : S.R →+* O) ≤ maximalIdeal O := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← res_eq_zero_iff O O]
    have := (res_eq_zero_iff O S.R x).2 hx
    simpa [res_map] using this
  obtain ⟨hc, hb, hd⟩ := S.lift
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, ?_, ?_⟩
  · exact adicCont_comp_ringHom_of_map_le _ hm (hc.1 i j)
  · exact adicCont_comp_ringHom_of_map_le _ hm (hc.2 v i)
  · rw [NRep.map_map, hres]
    exact hb
  · rw [NRep.map_map, hres]
    exact hd

private theorem box_pt {C₀ : ℕ} (hF : F.Ok C₀) (S : Space O F 3) (ξ : S.R →ₐ[O] O) :
    ∃ B : Box F 3 O, B.Of (S.ρ.map (ξ : S.R →+* O)) ∧ B.Cont (maximalIdeal O) := by
  have e : NRep.map ((ξ : S.R →+* O).comp (S.A.val : S.A →+* S.R)) S.u = S.ρ.map (ξ : S.R →+* O) := by
    apply NRep.ext
    · rfl
    · funext v i
      ext g
      rfl
  refine pr_box hF O (maximalIdeal O) _ (lift_pt S ξ).1 fun v => ?_
  rw [← e]
  exact flag hF (Or.inr rfl) S O _ v

private theorem box_unit [Algebra ℤ_[l] O] {ρ : NRep F 3 O} {B₀ : Box F 3 O} (h : B₀.Of ρ)
    (hc : B₀.Cont (maximalIdeal O)) (v : F.V) (i : Fin 2) (hu : UnitAt ρ v i) :
    ∃ B : Box F 3 O, B.Of ρ ∧ B.Cont (maximalIdeal O) ∧
      UnitStep (F.Iv v) (F.eps.comp (F.loc v)) (triOf B v) i := by
  classical
  obtain ⟨g, t, ht, hup, hdiag, hstep⟩ := hu
  have hr : ∀ s : F.Gv v, (B₀.r ((F.loc v) s)).mat = ρ.r ((F.loc0 v) s) := fun s => h.res ((F.loc0 v) s)
  let B : Box F 3 O :=
    { r := B₀.r
      nu := B₀.nu
      g := Function.update B₀.g v g
      tri := by
        intro w s
        by_cases hw : w = v
        · subst hw
          rw [Function.update_self, hr s, ← ht s]
          exact hup s
        · rw [Function.update_of_ne hw]
          exact B₀.tri w s }
  have hBg : B.g v = g := by
    show Function.update B₀.g v g v = g
    exact Function.update_self _ _ _
  have hBw : ∀ w, w ≠ v → B.g w = B₀.g w := fun w hw => by
    show Function.update B₀.g v g w = B₀.g w
    exact Function.update_of_ne hw _ _
  have htri : triOf B v = t := by
    ext s : 1
    apply Units.ext
    show (B.g v : Matrix (Fin 3) (Fin 3) O) * (B₀.r ((F.loc v) s)).mat * ((B.g v)⁻¹ : GL (Fin 3) O) = _
    rw [hBg, hr s, ht s]
  refine ⟨B, ⟨h.atc, h.res, fun w j s => ?_⟩, hc, ?_⟩
  · by_cases hw : w = v
    · subst hw
      show ((B.g w : Matrix (Fin 3) (Fin 3) O) * ρ.r ((F.loc0 w) s) * ((B.g w)⁻¹ : GL (Fin 3) O)) j j = _
      rw [hBg, ← ht s]
      exact hdiag s j
    · show ((B.g w : Matrix (Fin 3) (Fin 3) O) * ρ.r ((F.loc0 w) s) * ((B.g w)⁻¹ : GL (Fin 3) O)) j j = _
      rw [hBw w hw]
      exact h.psi w j s
  · rw [htri]
    exact hstep

private theorem zn_ext {C₀ : ℕ} (hF : F.Ok C₀) (B : Box F 3 O) (k : ℕ) {z z' : F.Γ → Matrix (Fin 3) (Fin 3) (Ok l O k)}
    (hz : z ∈ ZN B k) (hz' : z' ∈ ZN B k)
    (h : ∀ s : F.G0, z s * ((boxK B k).r s).mat = z' s * ((boxK B k).r s).mat) : z = z' := by
  have hG : ∀ s : F.G0, z s = z' s := by
    intro s
    have hu : ((boxK B k).r s).mat * ((((boxK B k).r s).left⁻¹ : GL (Fin 3) (Ok l O k)) : Matrix (Fin 3) (Fin 3) (Ok l O k)) = 1 :=
      Units.mul_inv _
    calc z s = z s * (((boxK B k).r s).mat * ((((boxK B k).r s).left⁻¹ : GL (Fin 3) (Ok l O k)) : Matrix (Fin 3) (Fin 3) (Ok l O k))) := by
          rw [hu, mul_one]
      _ = z' s * (((boxK B k).r s).mat * ((((boxK B k).r s).left⁻¹ : GL (Fin 3) (Ok l O k)) : Matrix (Fin 3) (Fin 3) (Ok l O k))) := by
          rw [← mul_assoc, h s, mul_assoc]
      _ = z' s := by rw [hu, mul_one]
  funext s
  have hc : ∀ y ∈ ZN B k, y (s * F.c) = y s := fun y hy => by
    rw [hy.1.1.2 s F.c, hy.2.1, map_zero, add_zero]
  rcases Int.units_eq_one_or (F.del s) with hs | hs
  · exact hG ⟨s, MonoidHom.mem_ker.mpr hs⟩
  · have hsc : F.del (s * F.c) = 1 := by
      rw [map_mul, hs, hF.del_c]
      rfl
    rw [← hc z hz, ← hc z' hz']
    exact hG ⟨s * F.c, MonoidHom.mem_ker.mpr hsc⟩

end

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.tan :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ cw : F.Inf → F.Γ, (∀ w, cw w * cw w = 1 ∧ F.del (cw w) = -1) → GWL { F with cw := cw } → LocE F → ∀ (S : Space O F 3) (ξ : S.R →ₐ[O] O) (v : F.V) (i : Fin 2), UnitAt (S.ρ.map (ξ : S.R →+* O)) v i → ∃ δ ∈ WDer S.ρ ξ O, ∃ δ' ∈ WDer S.ρ ξ O, LinearIndependent O ![δ, δ'] := by
  intro l _ O _ _ _ _ _ F C₀ hF hl cw hcw hGWL hL S ξ v i hu
  obtain ⟨B₀, hB₀, hc₀⟩ := box_pt hF S ξ
  obtain ⟨B, hB, hc, hstep⟩ := box_unit hB₀ hc₀ v i hu
  obtain ⟨C, hC⟩ := selLow l O F C₀ hF hl _ B (lift_pt S ξ) hB hc cw hcw hGWL hL v i hstep
  let T : Set S.R := {a | ∃ (w : F.V) (j : Fin 3) (s : F.Gv w), s ∈ F.Iv w ∧ a = ((S.ρ.ψ w j s : S.Rˣ) : S.R)}
  obtain ⟨δ, δ', hd, hdT, hd', hdT', hli⟩ := rankTwo l O S.R ξ T C hl (by
    intro k hk X hX hXf
    classical
    refine (hC k hk).2.trans (Nat.mul_le_mul_left C ?_)
    have hex : ∀ z ∈ ZN B k, ∃ δ ∈ X,
        ∀ (s : F.G0) (a b : Fin 3), δ (S.ρ.r s a b) = (z s * ((boxK B k).r s).mat) a b := by
      intro z hz
      obtain ⟨δ, ⟨h1, h2⟩, h3⟩ := derOf l O F C₀ hF hl S ξ B hB hc k hk z hz
      refine ⟨δ, ?_, h3⟩
      rw [hX]
      refine ⟨h1, ?_⟩
      rintro a ⟨w, j, s, hs, rfl⟩
      exact h2 w j s hs
    let f : (F.Γ → Matrix (Fin 3) (Fin 3) (Ok l O k)) → (S.R →ₗ[O] Ok l O k) := fun z =>
      if hz : z ∈ ZN B k then (hex z hz).choose else 0
    refine Set.ncard_le_ncard_of_injOn f (fun z hz => ?_) (fun z hz z' hz' he => ?_) hXf
    · simp only [f, dif_pos hz]
      exact (hex z hz).choose_spec.1
    · apply zn_ext hF B k hz hz'
      intro s
      ext a b
      have h1 := (hex z hz).choose_spec.2 s a b
      have h2 := (hex z' hz').choose_spec.2 s a b
      simp only [f, dif_pos hz, dif_pos hz'] at he
      rw [← h1, ← h2, he])
  exact ⟨δ, ⟨hd, fun w j s hs => hdT _ ⟨w, j, s, hs, rfl⟩⟩, δ', ⟨hd', fun w j s hs => hdT' _ ⟨w, j, s, hs, rfl⟩⟩, hli⟩
