module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemOfCoeffNeZero
noncomputable section

open GlobalTheory.Toroidal GlobalTheory.LocM

namespace GlobalTheory.PolFan

namespace ConeMeet

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m m' : ℕ}

theorem inCone {n : ℕ} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ' : IsCone bar φ γ')
    {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X) (hβp : ∀ i y, 0 ≤ β i y y)
    {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (γ' j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • γ' j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ'.strict
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (γ' j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β γ') (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (γ' j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ γ').1 hγ'.linear b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he

theorem apply_sum_nsmul {L : Type} [AddCommGroup L] (F : L →ₗ[ℤ] ℤ) {p : ℕ} (n : Fin p → ℕ) (v : Fin p → L) :
    F (∑ j, n j • v j) = ∑ j, (n j : ℤ) * F (v j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_nsmul]

theorem ray {γ : Fin m → LinearMap.BilinForm ℤ X} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ : IsCone bar φ γ)
    (hγ' : IsCone bar φ γ') {i : Fin m} {k : ℕ} {d : Fin m' → ℕ} (hk : 0 < k) (hkd : k • γ i = ∑ j, d j • γ' j)
    (hback : ∀ j, d j ≠ 0 → ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ kj • γ' j = ∑ l, e l • γ l) :
    ∃ j, γ i = γ' j := by
  classical
  let g : Fin m → balForms bar X := fun l => ⟨γ l, hγ.mem l⟩
  let g' : Fin m' → balForms bar X := fun l => ⟨γ' l, hγ'.mem l⟩
  obtain ⟨f, hf⟩ := hγ.basis.exists_dual
  obtain ⟨f', hf'⟩ := hγ'.basis.exists_dual
  have hf : ∀ a b, f a (g b) = if a = b then 1 else 0 := hf
  have hf' : ∀ a b, f' a (g' b) = if a = b then 1 else 0 := hf'
  have H1 : k • g i = ∑ j, d j • g' j := Subtype.ext (by simpa [g, g', Submodule.coe_sum] using hkd)
  have H2 : ∀ j, d j ≠ 0 → ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ kj • g' j = ∑ l, e l • g l := fun j hj => by
    obtain ⟨kj, e, hkj, he⟩ := hback j hj
    exact ⟨kj, e, hkj, Subtype.ext (by simpa [g, g', Submodule.coe_sum] using he)⟩

  have coord : ∀ j, d j ≠ 0 → ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ kj • g' j = ∑ l, e l • g l ∧
      ∀ l, (kj : ℤ) * f l (g' j) = e l := fun j hj => by
    obtain ⟨kj, e, hkj, he⟩ := H2 j hj
    refine ⟨kj, e, hkj, he, fun l => ?_⟩
    have t := congrArg (f l) he
    rw [map_nsmul, apply_sum_nsmul] at t
    simpa [hf] using t
  have Z : ∀ l, l ≠ i → ∀ j, d j ≠ 0 → f l (g' j) = 0 := by
    intro l hl
    have s := congrArg (f l) H1
    rw [map_nsmul, apply_sum_nsmul, hf, if_neg hl, smul_zero] at s
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ (d j : ℤ) * f l (g' j) := fun j _ => by
      by_cases hd : d j = 0
      · simp [hd]
      · obtain ⟨kj, e, hkj, -, he⟩ := coord j hd
        have : 0 ≤ (kj : ℤ) * f l (g' j) := (he l).symm ▸ Int.natCast_nonneg _
        exact mul_nonneg (Int.natCast_nonneg _) ((mul_nonneg_iff_of_pos_left (by exact_mod_cast hkj)).1 this)
    intro j hd
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 s.symm j (Finset.mem_univ _)
    exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hd)
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra hc
    push_neg at hc
    have : k • g i = 0 := by rw [H1]; simp [hc]
    have s := congrArg (f i) this
    rw [map_nsmul, hf, if_pos rfl, map_zero] at s
    simp at s
    omega
  obtain ⟨kj, e, hkj, he, hc⟩ := coord j hj
  have hel : ∀ l, l ≠ i → e l = 0 := fun l hl => by
    have := hc l
    rw [Z l hl j hj, mul_zero] at this
    exact_mod_cast this.symm
  have he' : kj • g' j = e i • g i := by
    rw [he, Finset.sum_eq_single i (fun l _ hl => by rw [hel l hl, zero_smul]) (by simp)]
  have t := congrArg (f' j) he'
  rw [map_nsmul, map_nsmul, hf', if_pos rfl] at t
  simp only [nsmul_eq_mul, mul_one] at t
  have hx := hc i
  have hx0 : 0 ≤ f i (g' j) := (mul_nonneg_iff_of_pos_left (by exact_mod_cast hkj)).1 (hx ▸ Int.natCast_nonneg _)
  have hxy : f i (g' j) * f' j (g i) = 1 := by
    have : (kj : ℤ) * (f i (g' j) * f' j (g i)) = kj * 1 := by
      rw [← mul_assoc, hx, mul_one]; exact_mod_cast t.symm
    exact mul_left_cancel₀ (by exact_mod_cast hkj.ne') this
  have hx1 : f i (g' j) = 1 := Int.eq_one_of_mul_eq_one_right hx0 hxy
  have hei : e i = kj := by rw [hx1, mul_one] at hx; exact_mod_cast hx.symm
  rw [hei] at he'
  refine ⟨j, LinearMap.ext₂ fun a b => ?_⟩
  have := LinearMap.congr_fun₂ (congrArg Subtype.val he') a b
  simp [g, g'] at this
  rcases this with h | h
  · exact h.symm
  · omega

theorem mem_of_coeff_ne_zero {γ : Fin m → LinearMap.BilinForm ℤ X} {γ' : Fin m' → LinearMap.BilinForm ℤ X}
    (hγ : IsCone bar φ γ) (hγ' : IsCone bar φ γ') {c : Fin m → ℝ} {c' : Fin m' → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hc' : ∀ j, 0 ≤ c' j) (hrel : ∑ i, c i • toReal (γ i) = ∑ j, c' j • toReal (γ' j)) (i : Fin m) (hi : c i ≠ 0) :
    ∃ j, γ i = γ' j := by
  classical
  obtain ⟨k, d, hk, hkd⟩ := inCone hγ' hγ.mem hγ.nonneg hc hc' ((linearOn_iff φ γ).1 hγ.linear c hc) hrel i hi
  refine ray hγ hγ' hk hkd fun j hj => ?_
  refine inCone (a := fun j => (d j : ℝ)) (b := Pi.single i (k : ℝ)) hγ hγ'.mem hγ'.nonneg
    (fun j => Nat.cast_nonneg _) (fun l => by by_cases h : l = i <;> simp [h])
    ((linearOn_iff φ γ').1 hγ'.linear _ fun j => Nat.cast_nonneg _) ?_ j (by exact_mod_cast hj)
  refine LinearMap.ext₂ fun a b => ?_
  have := LinearMap.congr_fun₂ hkd a b
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, nsmul_eq_mul] at this ⊢
  simp only [Pi.single_apply, ite_smul, zero_smul, LinearMap.smul_apply, toReal_apply, smul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
  exact_mod_cast this.symm

end ConeMeet


open ConeMeet in
theorem cone_meet : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin m' → LinearMap.BilinForm ℤ X)
    (c : Fin m → ℝ) (c' : Fin m' → ℝ), IsCone bar φ γ → IsCone bar φ γ' → (∀ i, 0 ≤ c i) → (∀ j, 0 ≤ c' j) →
    ∑ i, c i • toReal (γ i) = ∑ j, c' j • toReal (γ' j) → ∀ i, c i ≠ 0 → ∃ j, γ i = γ' j ∧ c i = c' j := by
  intro O _ bar φ X _ _ _ m m' γ γ' c c' hγ hγ' hc hc' hrel i hi
  classical
  obtain ⟨j, hj⟩ := mem_of_coeff_ne_zero hγ hγ' hc hc' hrel i hi
  refine ⟨j, hj, ?_⟩
  let g : Fin m → balForms bar X := fun l => ⟨γ l, hγ.mem l⟩
  let g' : Fin m' → balForms bar X := fun l => ⟨γ' l, hγ'.mem l⟩
  obtain ⟨f', hf'⟩ := hγ'.basis.exists_dual
  have hf' : ∀ a b, f' a (g' b) = if a = b then 1 else 0 := hf'
  have s := sum_mul_eq_zero_of_sum_toReal (X := X) (j := (balForms bar X).subtype) Subtype.val_injective (f' j)
    (β := Sum.elim g g') (c := Sum.elim c (-c')) (by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Submodule.subtype_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib,
        g, g', hrel, add_neg_cancel])
  rw [Fintype.sum_sum_type] at s
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, hf', Int.cast_ite,
    Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at s
  have h1 : ∑ l, c l * (f' j (g l) : ℝ) = c i := by
    rw [Finset.sum_eq_single i]
    · have : g i = g' j := Subtype.ext hj
      rw [this, hf', if_pos rfl, Int.cast_one, mul_one]
    · intro l _ hl
      by_cases hcl : c l = 0
      · rw [hcl, zero_mul]
      · obtain ⟨p, hp⟩ := mem_of_coeff_ne_zero hγ hγ' hc hc' hrel l hcl
        have : g l = g' p := Subtype.ext hp
        rw [this, hf', if_neg, Int.cast_zero, mul_zero]
        rintro rfl
        exact hl (hγ.injective (hp.trans hj.symm))
    · simp
  linarith

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPartOfBasisOfInjective
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem isPartOfBasis_of_injective {L L' : Type} [AddCommGroup L] [AddCommGroup L'] {m : ℕ} (f : L →ₗ[ℤ] L')
    (hf : Function.Injective f) {v : Fin m → L} (h : IsPartOfBasis fun i => f (v i)) : IsPartOfBasis v := by
  classical
  obtain ⟨ψ, hψ⟩ := h.exists_dual
  obtain ⟨n', b, -⟩ := h
  let π : L →ₗ[ℤ] (Fin m → ℤ) := LinearMap.pi fun i => ψ i ∘ₗ f
  let s : (Fin m → ℤ) →ₗ[ℤ] L := ∑ i, (LinearMap.proj i : (Fin m → ℤ) →ₗ[ℤ] ℤ).smulRight (v i)
  have hs : ∀ c, s c = ∑ i, c i • v i := fun c => by simp [s, LinearMap.sum_apply]
  have hπ : ∀ c, π (s c) = c := fun c => by
    ext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [π, hs, map_sum, hψ]
  let K := LinearMap.ker π
  obtain ⟨n, bK'⟩ := Submodule.basisOfPid b (K.map f)
  let bK := bK'.map (Submodule.equivMapOfInjective f hf K).symm
  have hinj : Function.Injective (s.coprod K.subtype) := by
    refine (injective_iff_map_eq_zero _).2 ?_
    rintro ⟨c, k⟩ h0
    have h1 : s c + (k : L) = 0 := by simpa using h0
    have h2 : π (k : L) = 0 := k.2
    have h3 : c = 0 := by simpa [h2, hπ] using congrArg π h1
    subst h3
    have h4 : (k : L) = 0 := by simpa using h1
    exact Prod.ext rfl (Subtype.ext h4)
  have hsurj : Function.Surjective (s.coprod K.subtype) := fun x =>
    ⟨(π x, ⟨x - s (π x), by simp [K, LinearMap.mem_ker, hπ]⟩), by simp⟩
  let E : ((Fin m → ℤ) × K) ≃ₗ[ℤ] L := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine ⟨n, ((Pi.basisFun ℤ (Fin m)).prod bK).map E, fun i => ?_⟩
  have h1 : E (Pi.single i 1, 0) = v i := by
    change (s.coprod K.subtype) (Pi.single i 1, 0) = v i
    simp [hs, Pi.single_apply]
  simpa using h1

theorem isCone_of_pull : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X X₁ : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] (r : X →ₗ[O] X₁) (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X₁), Function.Surjective r → IsCone bar φ (fun i => pull r (γ i)) →
    IsCone bar φ γ := by
  intro O _ bar φ X X₁ _ _ _ _ _ _ r m γ hr h
  have hmem : ∀ i, γ i ∈ balForms bar X₁ := fun i => by
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · obtain ⟨y, rfl⟩ := hr y
      obtain ⟨z, rfl⟩ := hr z
      exact (h.mem i).1 y z
    · obtain ⟨y, rfl⟩ := hr y
      obtain ⟨z, rfl⟩ := hr z
      simpa only [pull_apply, map_smul] using (h.mem i).2 a y z
  have hinj : Function.Injective (pullBal bar r) := fun β β' e =>
    Subtype.ext (LinearMap.ext₂ fun a b => by
      obtain ⟨a, rfl⟩ := hr a
      obtain ⟨b, rfl⟩ := hr b
      exact LinearMap.congr_fun₂ (congrArg Subtype.val e) a b)
  refine ⟨hmem, fun i y => ?_, isPartOfBasis_of_injective (pullBal bar r) hinj h.basis,
    (linearOn_pull_iff hr).1 h.linear, IsStrict.of_pull hr h.strict⟩
  obtain ⟨y, rfl⟩ := hr y
  exact h.nonneg i y

end GlobalTheory.PolFan
end

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem apply_eq_zero_of_diag {X : Type} [AddCommGroup X] {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y)
    (hp : ∀ y, 0 ≤ β y y) {y : X} (hy : β y y = 0) (z : X) : β y z = 0 := by
  by_contra hb
  have hA := hp z
  have h := hp (z + (-(β z z + 1) * β y z) • y)
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hy, hs z y] at h
  have hb2 : 1 ≤ β y z * β y z := mul_self_pos.2 hb
  have h3 := mul_nonneg (by linarith : 0 ≤ β z z + 1) (sub_nonneg.2 hb2)
  nlinarith [h3]

theorem exists_pull_eq {O : Type} [CommRing O] {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]
    {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y)
    (hk : ∀ y, r y = 0 → ∀ z, β y z = 0) : ∃ β' : LinearMap.BilinForm ℤ X₁, pull r β' = β := by
  have key1 : ∀ a a' b, r a = r a' → β a b = β a' b := fun a a' b h => by
    have := hk (a - a') (by rw [map_sub, h, sub_self]) b
    rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
  have key : ∀ a a' b b', r a = r a' → r b = r b' → β a b = β a' b' := fun a a' b b' h h' => by
    rw [key1 a a' b h, hs a' b, key1 b b' a' h', hs]
  have hs' : ∀ a, r (Function.surjInv hr a) = a := Function.surjInv_eq hr
  refine ⟨LinearMap.mk₂ ℤ (fun a b => β (Function.surjInv hr a) (Function.surjInv hr b)) ?_ ?_ ?_ ?_,
    LinearMap.ext₂ fun a b => ?_⟩
  · intro a a' b
    rw [← LinearMap.add_apply, ← map_add (f := _)]
    exact key _ _ _ _ (by rw [map_add (f := _), hs', hs', hs']) rfl
  · intro n a b
    rw [← LinearMap.smul_apply, ← map_smul]
    exact key _ _ _ _ (by rw [map_zsmul r, hs', hs']) rfl
  · intro a b b'
    rw [← map_add (f := _)]
    exact key _ _ _ _ rfl (by rw [map_add (f := _), hs', hs', hs'])
  · intro n a b
    rw [← map_smul]
    exact key _ _ _ _ rfl (by rw [map_zsmul r, hs', hs'])
  · simpa using key _ _ _ _ (hs' (r a)) (hs' (r b))

theorem isCone_pull_of_surjective : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (φ : InvFun O) (X₁ : Type) [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] (r : X →ₗ[O] X₁) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X₁), IsPolFanOn bar φ X → Function.Surjective r → IsCone bar φ γ → IsCone bar φ (fun i => pull r (γ i)) := by
  intro O _ _ _ _ bar X _ _ _ φ X₁ _ _ _ r m γ hF hr hγ
  classical
  have hx := GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone O bar X m (fun i => pull r (γ i)) (fun _ => 1) (fun i => pull_mem r (hγ.mem i))
    (fun i y => hγ.nonneg i _) (fun _ => zero_le_one)
  obtain ⟨m₂, σ, c, hσ, hc, hsum⟩ := hF.cover _ hx
  let J : Finset (Fin m₂) := Finset.univ.filter fun j => c j ≠ 0
  let t : Fin J.card ↪ Fin m₂ := (J.orderEmbOfFin rfl).toEmbedding
  have hpos : ∀ k, c (t k) ≠ 0 := fun k => (Finset.mem_filter.1 (J.orderEmbOfFin_mem rfl k)).2
  have hout : ∀ j, j ∉ Set.range t → c j = 0 := fun j hj => by
    by_contra h0
    refine hj ?_
    have : j ∈ Set.range (J.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩)
    exact this
  have hδ := hF.face _ _ σ t hσ
  have hsum' : ∑ i, (1 : ℝ) • toReal (pull r (γ i)) = ∑ k, c (t k) • toReal (σ (t k)) :=
    hsum.trans (Fintype.sum_of_injective t t.injective _ _ (fun j hj => by simp [hout j hj]) fun _ => rfl).symm
  have hvan : ∀ k y, r y = 0 → σ (t k) y y = 0 := fun k y hy => by
    have h1 := LinearMap.congr_fun₂ hsum' y y
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply, hy, map_zero, LinearMap.zero_apply,
      Int.cast_zero, smul_zero, smul_eq_mul, mul_zero, Finset.sum_const_zero] at h1
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hc (t k))
      (by exact_mod_cast hσ.nonneg (t k) y : (0 : ℝ) ≤ (σ (t k) y y : ℝ))).1 h1.symm k (Finset.mem_univ _)
    exact_mod_cast (mul_eq_zero.1 h2).resolve_left (hpos k)
  have hex : ∀ k, ∃ β' : LinearMap.BilinForm ℤ X₁, pull r β' = σ (t k) := fun k =>
    exists_pull_eq hr (hσ.mem (t k)).1 fun y hy z =>
      apply_eq_zero_of_diag (hσ.mem (t k)).1 (hσ.nonneg (t k)) (hvan k y hy) z
  choose δ hδ' using hex
  have hδc : IsCone bar φ δ := GlobalTheory.PolFan.isCone_of_pull O bar φ X X₁ r _ δ hr (by simpa only [hδ'] using hδ)
  have hsum₁ : ∑ i, (1 : ℝ) • toReal (γ i) = ∑ k, c (t k) • toReal (δ k) := LinearMap.ext₂ fun a b => by
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    have h1 := LinearMap.congr_fun₂ hsum' a b
    simp only [← hδ'] at h1
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply] using h1
  have hmeet := GlobalTheory.PolFan.cone_meet O bar φ X₁ m _ γ δ (fun _ => 1) (fun k => c (t k)) hγ hδc (fun _ => zero_le_one)
    (fun k => hc _) hsum₁
  choose j hj using fun i => hmeet i one_ne_zero
  have hinj : Function.Injective j := fun i i' h =>
    hγ.injective ((hj i).1.trans ((congrArg δ h).trans (hj i').1.symm))
  have hfin := hF.face _ _ _ ⟨j, hinj⟩ hδ
  have heq : (fun i => pull r (γ i)) = fun i => σ (t (j i)) := funext fun i => by rw [(hj i).1, hδ']
  rw [heq]
  exact hfin

end GlobalTheory.PolFan
