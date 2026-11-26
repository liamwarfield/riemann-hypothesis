module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PExtP
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pExtP :
    ExtP := by
  intro Γ X X₂ V _ _ _ _ _ ι K K₂ ξ φ h1 h2
  let F : X × X₂ → V := fun p =>
    if h : ∃ γ : Γ, (ι γ).2⁻¹ * p.2 ∈ K₂ then ξ h.choose (φ ((ι h.choose).1⁻¹ * p.1)) else 0
  have key : ∀ (γ : Γ) (g : X) (g₂ : X₂), (ι γ).2⁻¹ * g₂ ∈ K₂ →
      F (g, g₂) = ξ γ (φ ((ι γ).1⁻¹ * g)) := by
    intro γ g g₂ hγ
    have h : ∃ γ : Γ, (ι γ).2⁻¹ * g₂ ∈ K₂ := ⟨γ, hγ⟩
    dsimp only [F]
    rw [dite_eq_left h]
    have hδ := h.choose_spec
    generalize h.choose = δ at hδ ⊢
    have hε : (ι (δ⁻¹ * γ)).2 ∈ K₂ := by
      have e : (ι (δ⁻¹ * γ)).2 = ((ι δ).2⁻¹ * g₂) * ((ι γ).2⁻¹ * g₂)⁻¹ := by
        simp only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv]
        group
      rw [e]
      exact K₂.mul_mem hδ (K₂.inv_mem hγ)
    have e2 : (ι (δ⁻¹ * γ)).1 * ((ι γ).1⁻¹ * g) = (ι δ).1⁻¹ * g := by
      simp only [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv]
      group
    rw [← e2, h1 _ hε, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have zero : ∀ (g : X) (g₂ : X₂), (¬ ∃ γ : Γ, (ι γ).2⁻¹ * g₂ ∈ K₂) → F (g, g₂) = 0 := by
    intro g g₂ h
    dsimp only [F]
    rw [dite_eq_right h]
  have mem : F ∈ forms ι (K.prod K₂) ξ := by
    refine ⟨fun γ p => ?_, fun k hk p => ?_⟩
    · obtain ⟨g, g₂⟩ := p
      have e : ι γ * (g, g₂) = ((ι γ).1 * g, (ι γ).2 * g₂) := rfl
      rw [e]
      by_cases h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂
      · obtain ⟨δ, hδ⟩ := h
        have hs : (ι (γ * δ)).2⁻¹ * ((ι γ).2 * g₂) ∈ K₂ := by
          simpa [map_mul, mul_assoc] using hδ
        rw [key δ g g₂ hδ, key (γ * δ) _ _ hs, ← Module.End.mul_apply, ← map_mul]
        congr 2
        simp [mul_assoc]
      · rw [zero g g₂ h, map_zero]
        apply zero
        rintro ⟨δ, hδ⟩
        apply h
        refine ⟨γ⁻¹ * δ, ?_⟩
        simpa [map_mul, mul_assoc] using hδ
    · obtain ⟨g, g₂⟩ := p
      obtain ⟨k1, k2⟩ := k
      rw [Subgroup.mem_prod] at hk
      have hk1 : k1 ∈ K := hk.1
      have hk2 : k2 ∈ K₂ := hk.2
      have e : (g, g₂) * (k1, k2) = (g * k1, g₂ * k2) := rfl
      rw [e]
      by_cases h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂
      · obtain ⟨δ, hδ⟩ := h
        have hs : (ι δ).2⁻¹ * (g₂ * k2) ∈ K₂ := by
          rw [← mul_assoc]
          exact K₂.mul_mem hδ hk2
        rw [key δ g g₂ hδ, key δ (g * k1) (g₂ * k2) hs, ← mul_assoc, h2 k1 hk1]
      · rw [zero g g₂ h, zero]
        rintro ⟨δ, hδ⟩
        apply h
        refine ⟨δ, ?_⟩
        have := K₂.mul_mem hδ (K₂.inv_mem hk2)
        simpa [mul_assoc] using this
  refine ⟨⟨F, mem⟩, fun g => ?_, fun g₂ => ?_⟩
  · show F (g, 1) = φ g
    rw [key 1 g 1 (by simp)]
    simp
  · by_cases h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂
    · obtain ⟨δ, hδ⟩ := h
      exact Or.inr ⟨δ, fun g => key δ g g₂ hδ⟩
    · exact Or.inl fun g => zero g g₂ h
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfAct
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem typeFunction_mul_mem {M : Type} [Group M] (J : Subgroup M) (ψ : J →* ℂˣ) (a b : M) (hb : b ∈ J) :
    tyFn J ψ (a * b) = tyFn J ψ a * (((ψ ⟨b, hb⟩)⁻¹ : ℂˣ) : ℂ) := by
  unfold tyFn
  by_cases ha : a ∈ J
  · have hab : a * b ∈ J := J.mul_mem ha hb
    rw [dite_eq_left ha, dite_eq_left hab]
    have : (⟨a * b, hab⟩ : J) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul, mul_inv, Units.val_mul]
  · have hab : a * b ∉ J := fun h => ha (by simpa using J.mul_mem h (J.inv_mem hb))
    rw [dite_eq_right ha, dite_eq_right hab, zero_mul]

private theorem typeFunction_one {M : Type} [Group M] (J : Subgroup M) (ψ : J →* ℂˣ) : tyFn J ψ 1 = 1 := by
  unfold tyFn
  rw [dite_eq_left J.one_mem]
  have : (⟨1, J.one_mem⟩ : J) = 1 := rfl
  rw [this, map_one, inv_one, Units.val_one]

private theorem doubleCosetIndicator_central {X : Type} [Group X] (K : Subgroup X) (a z w : X) (hz : ∀ g, z * g = g * z) :
    dosetInd ℂ K (a * z) (z * w) = dosetInd ℂ K a w := by
  have key : z * w ∈ DoubleCoset.doubleCoset (a * z) (K : Set X) (K : Set X) ↔
      w ∈ DoubleCoset.doubleCoset a (K : Set X) (K : Set X) := by
    simp only [DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨x, hx, y, hy, e⟩
      refine ⟨x, hx, y, hy, ?_⟩
      have e' : z * w = z * (x * a * y) := by
        rw [e, hz (x * a * y)]
        have h1 : x * (a * z) * y = x * a * (z * y) := by group
        rw [h1, hz y]
        group
      exact mul_left_cancel e'
    · rintro ⟨x, hx, y, hy, e⟩
      refine ⟨x, hx, y, hy, ?_⟩
      rw [e, hz (x * a * y)]
      have h1 : x * (a * z) * y = x * a * (z * y) := by group
      rw [h1, hz y]
      group
  unfold dosetInd
  by_cases hw : w ∈ DoubleCoset.doubleCoset a (K : Set X) (K : Set X)
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (key.mpr hw)]; rfl
  · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem (fun h => hw (key.mp h))]

theorem UpperTheory.Gal.W2.Seed.pTfAct :
    (∀ (X V : Type) [Group X] [AddCommGroup V] [Module ℂ V] (K K₀ : Subgroup X), K₀ ≤ K → K₀.relIndex K ≠ 0 → ∀ Ψ : X → V, (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ x : X ⧸ K₀, Ψ x.out = ((K₀.relIndex K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ K, Ψ y.out) → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (V : Type) [AddCommGroup V] [Module ℂ V] (Ψ : X → V), (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ y : X ⧸ K, dosetInd ℂ K (L'.loc t) y.out • Ψ y.out = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out)) → TfAdm → TfAct := by
  intro hidx hfac hadm X M M' _ _ _ T L' Kw hF hAp t z hz V _ _ Φ hΦ g
  have hh : T.L.pr (L'.loc t * z) = 1 := by rw [map_mul, hAp.1 t, hz.2, one_mul]
  obtain ⟨-, hinv⟩ := hadm X M T _ hh
  have hc0 : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr T.idx
  have h0 : ∀ k ∈ T.K, ∀ x, T.tf (L'.loc t * z) (x * k) • Φ (g * (x * k)) =
      T.tf (L'.loc t * z) x • Φ (g * x) := by
    intro k hk x
    rw [(hinv k hk x).2, ← mul_assoc, hΦ k hk, smul_smul, mul_right_comm, Units.inv_mul, one_mul]
  let F : X → V := fun y =>
    (tyFn T.J T.ψ (T.L.pr y) * dosetInd ℂ T.K (L'.loc t * z) y) • Φ (g * y)
  have hF1 : ∀ y, ((T.K₀.relIndex T.K : ℕ) : ℂ) • (T.tf (L'.loc t * z) y • Φ (g * y)) = F y := by
    intro y
    simp only [F, TyLev.tf]
    rw [smul_smul, mul_assoc, mul_inv_cancel_left₀ hc0]
  have hFinv : ∀ (y : X) (k : T.K), F (y * k) = F y := by
    intro y k
    rw [← hF1, ← hF1, h0 k k.2 y]
  let Ψ : X → V := fun y => tyFn T.J T.ψ (T.L.pr y) • Φ (g * z * y)
  have hΨ : ∀ k ∈ T.K, ∀ y, Ψ (y * k) = Ψ y := by
    intro k hk y
    simp only [Ψ]
    rw [map_mul, typeFunction_mul_mem T.J T.ψ _ _ (T.fact.2 k hk), ← mul_assoc, hΦ k hk, smul_smul,
      mul_assoc, Units.inv_mul, mul_one]
  have e1 := hidx X V T.K T.K₀ T.le T.idx (fun x => T.tf (L'.loc t * z) x • Φ (g * x)) h0
  have e2 := hfac X M' L' T.K Kw hF t V Ψ hΨ
  calc hAct T.K₀ (T.tf (L'.loc t * z)) Φ g
      = ((T.K₀.relIndex T.K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ T.K, T.tf (L'.loc t * z) y.out • Φ (g * y.out) := e1
    _ = ∑ᶠ y : X ⧸ T.K, F y.out := by
        rw [smul_finsum]
        exact finsum_congr fun y => hF1 _
    _ = ∑ᶠ y : X ⧸ T.K, F (z * y.out) := (Formalism.UG.P.finsum_out_mul T.K z F hFinv).symm
    _ = ∑ᶠ y : X ⧸ T.K, dosetInd ℂ T.K (L'.loc t) y.out • Ψ y.out := by
        refine finsum_congr fun y => ?_
        simp only [F, Ψ]
        rw [doubleCosetIndicator_central T.K _ z _ hz.1, map_mul, hz.2, one_mul, smul_smul, ← mul_assoc g z,
          mul_comm]
    _ = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out) := e2
    _ = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Φ (g * z * L'.loc x.out) := by
        refine finsum_congr fun x => ?_
        simp only [Ψ]
        rw [hAp.1, typeFunction_one, one_smul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfMulR
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem tyFn_mul_of_mem {M : Type} [Group M] (J : Subgroup M) (ψ : J →* ℂˣ) (a b : M)
    (ha : a ∈ J) : tyFn J ψ a * tyFn J ψ b = tyFn J ψ (a * b) := by
  unfold tyFn
  by_cases hb : b ∈ J
  · have hab : a * b ∈ J := J.mul_mem ha hb
    rw [dite_eq_left ha, dite_eq_left hb, dite_eq_left hab]
    have e : (⟨a * b, hab⟩ : J) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul, mul_inv, Units.val_mul, mul_comm]
  · have hab : a * b ∉ J := fun h => hb (by simpa using J.mul_mem (J.inv_mem ha) h)
    rw [dite_eq_right hb, dite_eq_right hab, mul_zero]

private theorem mem_doubleCoset_loc_mul_of_mem_of_pr_eq_one {X M' : Type} [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X)
    (Kw : Subgroup M') (hF : L'.Fact K Kw)
    (hC : ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔
      L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧
        (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K)
    (t : M') (r g y : X) (hr : L'.pr r = 1) (hy : y ∈ DoubleCoset.doubleCoset r (K : Set X) K)
    (hz : y⁻¹ * g ∈ DoubleCoset.doubleCoset (L'.loc t) (K : Set X) K) :
    g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ∧
      y⁻¹ * ((L'.loc (L'.pr g))⁻¹ * g) ∈ K := by
  obtain ⟨hn, hk⟩ := (hC t 1 (map_one _) (y⁻¹ * g)).1 (by rw [mul_one]; exact hz)
  obtain ⟨ha, hy'⟩ := (hC 1 r hr y).1 (by rw [map_one, one_mul]; exact hy)
  have haK : L'.pr y ∈ Kw := by
    obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 ha
    rw [e, mul_one]
    exact Kw.mul_mem hu hv
  have hkK : (L'.loc (L'.pr (y⁻¹ * g)))⁻¹ * (y⁻¹ * g) ∈ K := by
    obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hk
    rw [e, mul_one]
    exact K.mul_mem hu hv
  generalize hkd : (L'.loc (L'.pr (y⁻¹ * g)))⁻¹ * (y⁻¹ * g) = k at hkK
  generalize hyd : (L'.loc (L'.pr y))⁻¹ * y = y' at hy'
  have hm : L'.pr g = L'.pr y * L'.pr (y⁻¹ * g) := by simp
  generalize had : L'.pr y = a at haK hm hyd
  generalize hnd : L'.pr (y⁻¹ * g) = n at hn hm hkd
  have hpy' : L'.pr y' = 1 := by
    rw [← hyd, map_mul, map_inv, L'.pr_loc, had, inv_mul_cancel]
  have hcomm : ∀ x, L'.loc x * y' = y' * L'.loc x := fun x => L'.comm x y' hpy'
  have hy1 : y = L'.loc a * y' := by rw [← hyd]; group
  have hg : g = L'.loc a * y' * (L'.loc n * k) := by
    rw [← hkd, ← hy1]; group
  have hy0 : (L'.loc (L'.pr g))⁻¹ * g = y' * k := by
    rw [hm, map_mul, hg, mul_assoc (L'.loc a), ← mul_assoc y', ← hcomm n]
    group
  refine ⟨(hC t r hr g).2 ⟨?_, ?_⟩, ?_⟩
  · rw [hm]
    obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hn
    exact DoubleCoset.mem_doubleCoset.2 ⟨a * u, Kw.mul_mem haK hu, v, hv, by rw [e]; group⟩
  · rw [hy0]
    obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hy'
    exact DoubleCoset.mem_doubleCoset.2 ⟨u, hu, v * k, K.mul_mem hv hkK, by rw [e]; group⟩
  · rw [hy0]
    have e : y⁻¹ * (y' * k) = (L'.loc a)⁻¹ * k := by
      calc y⁻¹ * (y' * k) = y'⁻¹ * ((L'.loc a)⁻¹ * y') * k := by rw [hy1]; group
        _ = y'⁻¹ * (y' * (L'.loc a)⁻¹) * k := by rw [← map_inv, hcomm]
        _ = (L'.loc a)⁻¹ * k := by group
    rw [e]
    exact K.mul_mem (K.inv_mem (hF.1 a haK)) hkK

private theorem mem_doubleCosets_of_dosetInd_mul_ne_zero {X : Type} [Group X] (K : Subgroup X) (a b : ℂ) (r s x g : X)
    (h : a * dosetInd ℂ K r x * (b * dosetInd ℂ K s (x⁻¹ * g)) ≠ 0) :
    x ∈ DoubleCoset.doubleCoset r (K : Set X) K ∧
      x⁻¹ * g ∈ DoubleCoset.doubleCoset s (K : Set X) K := by
  constructor
  · by_contra hn
    apply h
    simp [dosetInd, Set.indicator_apply, hn]
  · by_contra hn
    apply h
    simp [dosetInd, Set.indicator_apply, hn]

theorem UpperTheory.Gal.W2.Seed.pTfMulR :
    (∀ (X V : Type) [Group X] [AddCommGroup V] [Module ℂ V] (K K₀ : Subgroup X), K₀ ≤ K → K₀.relIndex K ≠ 0 → ∀ Ψ : X → V, (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ x : X ⧸ K₀, Ψ x.out = ((K₀.relIndex K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ K, Ψ y.out) → TfAdm → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔ L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧ (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K) → TfMulR := by
  intro hA hAdm hC X M M' _ _ _ T L' Kw hF hAp t r hr hr'
  funext g
  have hloc : T.L.pr (L'.loc t) = 1 := hAp.1 t
  have hinv : ∀ k ∈ T.K, ∀ x : X,
      T.tf r (x * k) * T.tf (L'.loc t) ((x * k)⁻¹ * g) = T.tf r x * T.tf (L'.loc t) (x⁻¹ * g) := by
    intro k hk x
    have h1 := ((hAdm X M T r hr).2 k hk x).2
    have h2 := ((hAdm X M T (L'.loc t) hloc).2 k⁻¹ (T.K.inv_mem hk) (x⁻¹ * g)).1
    rw [show (x * k)⁻¹ * g = k⁻¹ * (x⁻¹ * g) by group, h1, h2]
    have p1 : T.L.pr k ∈ T.J := T.fact.2 k hk
    have p2 : T.L.pr k⁻¹ ∈ T.J := T.fact.2 k⁻¹ (T.K.inv_mem hk)
    have e : (⟨T.L.pr k⁻¹, p2⟩ : T.J) = (⟨T.L.pr k, p1⟩ : T.J)⁻¹ := Subtype.ext (map_inv _ _)
    rw [e, map_inv, inv_inv]
    have hu := Units.inv_mul (T.ψ ⟨T.L.pr k, p1⟩)
    linear_combination (T.tf r x * T.tf (L'.loc t) (x⁻¹ * g)) * hu
  have hsum := hA X ℂ T.K T.K₀ T.le T.idx (fun x => T.tf r x * T.tf (L'.loc t) (x⁻¹ * g)) hinv
  beta_reduce at hsum
  unfold conv
  rw [hsum]
  have hc : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0 := by exact_mod_cast T.idx
  by_cases hg : g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (T.K : Set X) T.K
  · obtain ⟨hm, hy0⟩ := (hC X M' L' T.K Kw hF t r hr' g).1 hg
    obtain ⟨y₀, hy0d⟩ : ∃ y₀, y₀ = (L'.loc (L'.pr g))⁻¹ * g := ⟨_, rfl⟩
    rw [← hy0d] at hy0
    have hp0 : L'.pr y₀ = 1 := by rw [hy0d, map_mul, map_inv, L'.pr_loc, inv_mul_cancel]
    have hcomm : L'.loc (L'.pr g) * y₀ = y₀ * L'.loc (L'.pr g) := L'.comm _ _ hp0
    have hg0 : g = L'.loc (L'.pr g) * y₀ := by rw [hy0d]; group
    have hz0 : y₀⁻¹ * g = L'.loc (L'.pr g) := by
      calc y₀⁻¹ * g = y₀⁻¹ * (L'.loc (L'.pr g) * y₀) := by rw [← hg0]
        _ = L'.loc (L'.pr g) := by rw [hcomm]; group
    have hzK : y₀⁻¹ * g ∈ DoubleCoset.doubleCoset (L'.loc t) (T.K : Set X) T.K := by
      rw [hz0]
      obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hm
      exact DoubleCoset.mem_doubleCoset.2
        ⟨L'.loc u, hF.1 u hu, L'.loc v, hF.1 v hv, by rw [e, map_mul, map_mul]⟩
    have hJ : T.L.pr y₀ ∈ T.J := by
      obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hy0
      rw [e, map_mul, map_mul, hr, mul_one]
      exact T.J.mul_mem (T.fact.2 u hu) (T.fact.2 v hv)
    rw [finsum_eq_single _ (QuotientGroup.mk y₀ : X ⧸ T.K)]
    · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul T.K y₀
      rw [hk, hinv k k.2 y₀]
      have hτ := tyFn_mul_of_mem T.J T.ψ _ (T.L.pr (y₀⁻¹ * g)) hJ
      rw [← map_mul, mul_inv_cancel_left] at hτ
      simp only [TyLev.tf, dosetInd, Set.indicator_of_mem hy0, Set.indicator_of_mem hzK,
        Set.indicator_of_mem hg, Pi.one_apply]
      rw [smul_eq_mul, ← hτ]
      field_simp
    · intro q hq
      by_contra hne
      apply hq
      simp only [TyLev.tf] at hne
      have hm1 := mem_doubleCosets_of_dosetInd_mul_ne_zero T.K _ _ r (L'.loc t) q.out g hne
      have hK := (mem_doubleCoset_loc_mul_of_mem_of_pr_eq_one L' T.K Kw hF (hC X M' L' T.K Kw hF) t r g q.out hr' hm1.1 hm1.2).2
      rw [← hy0d] at hK
      have h := (QuotientGroup.eq (s := T.K)).2 hK
      rwa [QuotientGroup.out_eq'] at h
  · rw [finsum_eq_zero_of_forall_eq_zero]
    · simp [TyLev.tf, dosetInd, hg]
    · intro q
      by_contra hne
      apply hg
      simp only [TyLev.tf] at hne
      have hm1 := mem_doubleCosets_of_dosetInd_mul_ne_zero T.K _ _ r (L'.loc t) q.out g hne
      exact (mem_doubleCoset_loc_mul_of_mem_of_pr_eq_one L' T.K Kw hF (hC X M' L' T.K Kw hF) t r g q.out hr' hm1.1 hm1.2).1
end
