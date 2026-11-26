module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Formalism.PolynomialDimension.WeylDim

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderUnipotentModTwoPrimes
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.Neat

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

lemma apply_mem_smul_top (I : Ideal R) (T : Module.End R M) {y : M}
    (hy : y ∈ I • (⊤ : Submodule R M)) : T y ∈ I • (⊤ : Submodule R M) := by
  have h : (I • (⊤ : Submodule R M)).map T ≤ I • (⊤ : Submodule R M) := by
    rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
  exact h ⟨y, hy, rfl⟩

lemma pow_add_sub_pow_mem (I : Ideal R) (A B : Module.End R M)
    (hB : ∀ x, B x ∈ I • (⊤ : Submodule R M)) (n : ℕ) :
    ∀ x, ((A + B) ^ n - A ^ n) x ∈ I • (⊤ : Submodule R M) := by
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    have : (A + B) ^ (n + 1) - A ^ (n + 1) = ((A + B) ^ n - A ^ n) * A + (A + B) ^ n * B := by
      rw [pow_succ, pow_succ]; noncomm_ring
    rw [this, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply]
    exact Submodule.add_mem _ (ih _) (apply_mem_smul_top I _ (hB x))

lemma pow_prime_pow_unipotent (I : Ideal R) (α : Module.End R M) {p : ℕ} (hp : p.Prime)
    (hpI : (p : R) ∈ I) (a r : ℕ) (h : ∀ x, ((α - 1) ^ r) x ∈ I • (⊤ : Submodule R M)) :
    ∀ x, ((α ^ p ^ a - 1) ^ r) x ∈ I • (⊤ : Submodule R M) := by
  obtain ⟨F, hF⟩ := (Commute.one_right (α - 1)).exists_add_pow_prime_pow_eq hp a
  have hγ : α ^ p ^ a - 1 = (α - 1) ^ p ^ a + (p : Module.End R M) * ((α - 1) * (1 * F)) := by
    rw [sub_add_cancel, one_pow] at hF; rw [hF, mul_assoc, mul_assoc]; abel
  have hB : ∀ x, ((p : Module.End R M) * ((α - 1) * (1 * F))) x ∈ I • (⊤ : Submodule R M) := by
    intro x
    rw [Module.End.mul_apply, Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul R]
    exact Submodule.smul_mem_smul hpI trivial
  intro x
  have h1 := pow_add_sub_pow_mem I ((α - 1) ^ p ^ a) _ hB r x
  rw [← hγ, LinearMap.sub_apply] at h1
  have hle : r ≤ p ^ a * r := Nat.le_mul_of_pos_left r (pow_pos hp.pos a)
  have h2 : (((α - 1) ^ p ^ a) ^ r) x ∈ I • (⊤ : Submodule R M) := by
    rw [← pow_mul, ← Nat.add_sub_cancel' hle, pow_add, Module.End.mul_apply]
    exact h _
  have := Submodule.add_mem _ h1 h2
  simpa using this

end GlobalTheory.Neat

namespace GlobalTheory.Neat

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

lemma eq_one_of_unipotent_mod_of_unit [IsDomain R] [IsNoetherianRing R] [Module.Finite R M]
    [Module.IsTorsionFree R M] (I : Ideal R) (hI : I ≠ ⊤) (γ : Module.End R M) (b r : ℕ)
    (hb : γ ^ b = 1) (c : R) (hc : 1 - c * (b : R) ^ (r + 1) ∈ I)
    (h : ∀ x, ((γ - 1) ^ r) x ∈ I • (⊤ : Submodule R M)) : γ = 1 := by
  have hSN : (∑ i ∈ Finset.range b, γ ^ i) * (γ - 1) = 0 := by
    rw [geom_sum_mul, hb, sub_self]
  have hE : (b : Module.End R M) - ∑ i ∈ Finset.range b, γ ^ i
      = (γ - 1) * -∑ i ∈ Finset.range b, ∑ j ∈ Finset.range i, γ ^ j := by
    rw [mul_neg, Finset.mul_sum]
    simp only [mul_geom_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    abel
  have hcomm : Commute (γ - 1) (-∑ i ∈ Finset.range b, ∑ j ∈ Finset.range i, γ ^ j) := by
    refine Commute.neg_right (Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_)
    exact ((Commute.refl γ).sub_left (Commute.one_left γ)).pow_right j
  set Q := -∑ i ∈ Finset.range b, ∑ j ∈ Finset.range i, γ ^ j with hQ
  set e : Module.End R M := (b : Module.End R M) - ∑ i ∈ Finset.range b, γ ^ i with he
  set P : Submodule R M := LinearMap.range (γ - 1) with hP
  have hPI : P ≤ I • P := by
    rintro y ⟨z, rfl⟩
    have he1 : ∀ w ∈ P, e w = (b : R) • w := by
      rintro w ⟨v, rfl⟩
      rw [he, LinearMap.sub_apply, Module.End.natCast_apply, ← Module.End.mul_apply, hSN,
        LinearMap.zero_apply, sub_zero, Nat.cast_smul_eq_nsmul]
    have hek : ∀ k : ℕ, (e ^ k) ((γ - 1) z) = (b : R) ^ k • (γ - 1) z := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, Module.End.mul_apply, he1 _ ⟨z, rfl⟩, map_smul, ih, smul_smul, pow_succ,
          mul_comm]
    have hrange : LinearMap.range e ≤ P := by
      rw [hE, Module.End.mul_eq_comp]; exact LinearMap.range_comp_le_range _ _
    have hmap : ∀ w ∈ I • (⊤ : Submodule R M), e w ∈ I • P := by
      intro w hw
      have : (I • (⊤ : Submodule R M)).map e ≤ I • P := by
        rw [Submodule.map_smul'', Submodule.map_top]; exact Submodule.smul_mono le_rfl hrange
      exact this ⟨w, hw, rfl⟩
    have hr : (e ^ r) ((γ - 1) z) ∈ I • (⊤ : Submodule R M) := by
      rw [hE, hcomm.mul_pow, Module.End.mul_apply]; exact h _
    have hbig : (b : R) ^ (r + 1) • (γ - 1) z ∈ I • P := by
      rw [← hek, pow_succ', Module.End.mul_apply]; exact hmap _ hr
    have hsplit : (γ - 1) z = (1 - c * (b : R) ^ (r + 1)) • (γ - 1) z
        + c • ((b : R) ^ (r + 1) • (γ - 1) z) := by
      rw [smul_smul, ← add_smul, sub_add_cancel, one_smul]
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hc ⟨z, rfl⟩) (Submodule.smul_mem _ c hbig)
  obtain ⟨t, ht1, ht0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I P
    (IsNoetherian.noetherian P) hPI
  have htne : t ≠ 0 := by
    rintro rfl
    apply hI
    rw [Ideal.eq_top_iff_one]
    simpa using I.neg_mem ht1
  ext x
  have hx := ht0 _ (LinearMap.mem_range_self (γ - 1) x)
  rw [smul_eq_zero_iff_right htne, LinearMap.sub_apply, sub_eq_zero] at hx
  simpa using hx

end GlobalTheory.Neat

theorem GlobalTheory.eq_one_of_finite_order_unipotent_mod_two_primes : ∀ (E : Type) [Field E] [NumberField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Finite (𝓞 E) Λ] [Module.IsTorsionFree (𝓞 E) Λ] (α : Λ →ₗ[𝓞 E] Λ) (m r g₁ g₂ : ℕ) (I₁ I₂ : Ideal (𝓞 E)), 0 < m → α ^ m = 1 → g₁.Prime → g₂.Prime → g₁ ≠ g₂ → I₁ ≠ ⊤ → I₂ ≠ ⊤ → (g₁ : 𝓞 E) ∈ I₁ → (g₂ : 𝓞 E) ∈ I₂ → (∀ x, ((α - 1) ^ r) x ∈ I₁ • (⊤ : Submodule (𝓞 E) Λ)) → (∀ x, ((α - 1) ^ r) x ∈ I₂ • (⊤ : Submodule (𝓞 E) Λ)) → α = 1 := by
  intro E _ _ Λ _ _ _ _ α m r g₁ g₂ I₁ I₂ hm hαm hg₁ hg₂ hne hI₁ hI₂ hg₁I hg₂I h₁ h₂
  have key : ∀ (p : ℕ) (I : Ideal (𝓞 E)), p.Prime → I ≠ ⊤ → (p : 𝓞 E) ∈ I →
      (∀ x, ((α - 1) ^ r) x ∈ I • (⊤ : Submodule (𝓞 E) Λ)) → ∃ a : ℕ, α ^ p ^ a = 1 := by
    intro p I hp hI hpI h
    obtain ⟨a, b, hpb, hmab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp.one_lt.ne'
    refine ⟨a, ?_⟩
    have hcop : Nat.Coprime p (b ^ (r + 1)) :=
      Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd).2 hpb)
    obtain ⟨u, v, huv⟩ := Nat.Coprime.cast (R := 𝓞 E) hcop
    refine GlobalTheory.Neat.eq_one_of_unipotent_mod_of_unit I hI (α ^ p ^ a) b r ?_ v ?_
      (GlobalTheory.Neat.pow_prime_pow_unipotent I α hp hpI a r h)
    · rw [← pow_mul, ← hmab, hαm]
    · have : 1 - v * (b : 𝓞 E) ^ (r + 1) = u * p := by
        rw [← huv]; push_cast; ring
      rw [this]; exact I.mul_mem_left u hpI
  obtain ⟨a, ha⟩ := key g₁ I₁ hg₁ hI₁ hg₁I h₁
  obtain ⟨c, hc⟩ := key g₂ I₂ hg₂ hI₂ hg₂I h₂
  have hcop : Nat.Coprime (g₁ ^ a) (g₂ ^ c) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hg₁ hg₂).2 hne)
  have hd : orderOf α ∣ Nat.gcd (g₁ ^ a) (g₂ ^ c) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one hc)
  rw [hcop.gcd_eq_one] at hd
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_one hd)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemSmulTopOfNeatLevel
open NumberField

namespace GlobalTheory.NeatLevel

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

lemma val_pow_apply (W : Submodule R M) (S : Module.End R W) (T : Module.End R M)
    (hST : ∀ y : W, ((S y : W) : M) = T y) (k : ℕ) (y : W) :
    (((S ^ k) y : W) : M) = (T ^ k) y := by
  induction k generalizing y with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hST]

end GlobalTheory.NeatLevel

theorem GlobalTheory.sub_mem_smul_top_of_neat_level : ∀ (E : Type) [Field E] [NumberField E] (La Λ Q : Type) [AddCommGroup La] [Module (𝓞 E) La] [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Q] [Module (𝓞 E) Q] (J : Ideal (𝓞 E)) (n N m g₁ g₂ : ℕ) (I₁ I₂ : Ideal (𝓞 E)) (ev : La →ₗ[𝓞 E] Q) (ψ : Λ →ₗ[𝓞 E] Q) (θ : Q →ₗ[𝓞 E] Q) (F : Λ →ₗ[𝓞 E] Λ) (gM : La →ₗ[𝓞 E] La), Module.Finite (𝓞 E) Λ → Module.IsTorsionFree (𝓞 E) Λ → 0 < n → (n : 𝓞 E) ∈ J → (∀ a, ev a = 0 ↔ a ∈ J • (⊤ : Submodule (𝓞 E) La)) → (∀ q : Q, (∀ c ∈ J, c • q = 0) → ∃ a, ev a = q) → (∀ b, ψ b = 0 ↔ ∃ b', b = n • b') → (∀ q : Q, n • q = 0 → ∃ b, ψ b = q) → (∀ b, ψ (F b) = θ (ψ b)) → (∀ a, θ (ev (gM a)) = ev a) → 0 < N → F ^ N = 1 → g₁.Prime → g₂.Prime → g₁ ≠ g₂ → I₁ ≠ ⊤ → I₂ ≠ ⊤ → (g₁ : 𝓞 E) ∈ I₁ → (g₂ : 𝓞 E) ∈ I₂ → J ≤ I₁ → J ≤ I₂ → (∀ x, ((gM - 1) ^ m) x ∈ I₁ • (⊤ : Submodule (𝓞 E) La)) → (∀ x, ((gM - 1) ^ m) x ∈ I₂ • (⊤ : Submodule (𝓞 E) La)) → ∀ a, gM a - a ∈ J • (⊤ : Submodule (𝓞 E) La) := by

  intro E _ _ La Λ Q _ _ _ _ _ _ J n N m g₁ g₂ I₁ I₂ ev ψ θ F gM hfin htf hn hnJ hev hevs hψ hψs hFθ hθ hN hFN hg₁ hg₂ hg hI₁ hI₂ hgI₁ hgI₂ hJI₁ hJI₂ hu₁ hu₂
  have hevJ : ∀ c : 𝓞 E, c ∈ J → ∀ a, c • ev a = 0 := by
    intro c hc a
    rw [← map_smul, hev]
    exact Submodule.smul_mem_smul hc trivial
  have hevψ : ∀ a, ∃ μ, ψ μ = ev a := by
    intro a; apply hψs
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact hevJ _ hnJ a
  set G := F ^ (N - 1) with hGdef
  have hGF : G * F = 1 := by
    rw [hGdef, ← pow_succ, Nat.sub_add_cancel hN, hFN]
  have hFG : F * G = 1 := by
    rw [hGdef, ← pow_succ', Nat.sub_add_cancel hN, hFN]
  have hFGl : ∀ l, F (G l) = l := fun l => by
    rw [← Module.End.mul_apply, hFG, Module.End.one_apply]
  have hGFl : ∀ l, G (F l) = l := fun l => by
    rw [← Module.End.mul_apply, hGF, Module.End.one_apply]
  have hkey : ∀ (l : Λ) (a : La), ψ l = ev a → ψ (G l) = ev (gM a) := by
    intro l a hla
    obtain ⟨μ, hμ⟩ := hevψ (gM a)
    have h1 : ψ (F (μ - G l)) = 0 := by
      rw [map_sub, map_sub, hFθ, hμ, hθ, hFGl, hla, sub_self]
    obtain ⟨b', hb'⟩ := (hψ _).1 h1
    have h2 : μ - G l = n • G b' := by
      rw [← map_nsmul, ← hb', hGFl]
    have h3 : ψ (μ - G l) = 0 := (hψ _).2 ⟨G b', h2⟩
    rw [map_sub, sub_eq_zero] at h3
    rw [← h3, hμ]
  let W : Submodule (𝓞 E) Λ := (LinearMap.range ev).comap ψ
  have hGW : ∀ l ∈ W, G l ∈ W := by
    rintro l ⟨a, ha⟩; exact ⟨gM a, (hkey l a ha.symm).symm⟩
  obtain ⟨J', hJ'⟩ : J ∣ Ideal.span {(n : 𝓞 E)} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hnJ)
  have hJ'W : ∀ c' : 𝓞 E, c' ∈ J' → ∀ l, c' • l ∈ W := by
    intro c' hc' l
    obtain ⟨a, ha⟩ := hevs (ψ (c' • l)) (by
      intro c hc
      have hcc : c * c' ∈ Ideal.span {(n : 𝓞 E)} := by rw [hJ']; exact Ideal.mul_mem_mul hc hc'
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hcc
      rw [← map_smul, smul_smul, ← hr, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
      exact (hψ _).2 ⟨_, rfl⟩)
    exact ⟨a, ha⟩
  have hnW : ∀ I : Ideal (𝓞 E), J ≤ I → ∀ l : Λ, n • l ∈ I • W := by
    intro I hJI l
    have h1 : (n : 𝓞 E) • l ∈ (J * J') • (⊤ : Submodule (𝓞 E) Λ) :=
      Submodule.smul_mem_smul (by rw [← hJ']; exact Ideal.mem_span_singleton_self _) trivial
    rw [Submodule.mul_smul, Nat.cast_smul_eq_nsmul] at h1
    exact Submodule.smul_mono hJI (Submodule.smul_le.2 fun c' hc' l _ => hJ'W c' hc' l) h1
  have hpow : ∀ k (l : Λ) (a : La), ψ l = ev a → ψ (((G - 1 : Module.End (𝓞 E) Λ) ^ k) l) = ev (((gM - 1 : Module.End (𝓞 E) La) ^ k) a) := by
    intro k
    induction k with
    | zero => intro l a h; simpa using h
    | succ k ih =>
      intro l a h
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      apply ih
      simp [map_sub, hkey l a h, h]
  have hunipW : ∀ I : Ideal (𝓞 E), J ≤ I → (∀ x, ((gM - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) La)) →
      ∀ l ∈ W, ((G - 1) ^ m) l ∈ I • W := by
    rintro I hJI hu l ⟨a, ha⟩
    have hx := hpow m l a ha.symm
    have hmem : ev (((gM - 1) ^ m) a) ∈ (I • W).map ψ := by
      have h1 : ev (((gM - 1) ^ m) a) ∈ (I • (⊤ : Submodule (𝓞 E) La)).map ev := ⟨_, hu a, rfl⟩
      rw [Submodule.map_smul'', Submodule.map_top] at h1
      rw [Submodule.map_smul'']
      refine Submodule.smul_mono le_rfl ?_ h1
      rintro _ ⟨b, rfl⟩
      obtain ⟨μ, hμ⟩ := hevψ b
      exact ⟨μ, ⟨b, hμ.symm⟩, hμ⟩
    obtain ⟨z, hz, hzx⟩ := hmem
    have hd : ψ (((G - 1) ^ m) l - z) = 0 := by rw [map_sub, hzx, hx, sub_self]
    obtain ⟨b', hb'⟩ := (hψ _).1 hd
    have : ((G - 1) ^ m) l = z + n • b' := by rw [← hb']; abel
    rw [this]; exact Submodule.add_mem _ hz (hnW I hJI b')
  haveI := hfin; haveI := htf
  let Gr : Module.End (𝓞 E) W := G.restrict hGW
  have hGr : ∀ y : W, ((Gr y : W) : Λ) = G y := fun y => rfl
  have hGr1 : ∀ y : W, (((Gr - 1) y : W) : Λ) = (G - 1) y := fun y => rfl
  have hGN : G ^ N = 1 := by
    rw [hGdef, ← pow_mul, mul_comm, pow_mul, hFN, one_pow]
  have hGrN : Gr ^ N = 1 := by
    apply LinearMap.ext; intro y; apply Subtype.ext
    rw [GlobalTheory.NeatLevel.val_pow_apply W Gr G hGr, hGN]; rfl
  have hsub : ∀ I : Ideal (𝓞 E), J ≤ I → (∀ x, ((gM - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) La)) →
      ∀ y : W, ((Gr - 1) ^ m) y ∈ I • (⊤ : Submodule (𝓞 E) W) := by
    intro I hJI hu y
    have h1 : ((((Gr - 1) ^ m) y : W) : Λ) ∈ (I • (⊤ : Submodule (𝓞 E) W)).map W.subtype := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top, GlobalTheory.NeatLevel.val_pow_apply W (Gr - 1) (G - 1) hGr1]
      exact hunipW I hJI hu y y.2
    obtain ⟨z, hz, hzy⟩ := h1
    have hzz : z = ((Gr - 1) ^ m) y := Subtype.ext hzy
    rwa [← hzz]
  have hGr1' : Gr = 1 := GlobalTheory.eq_one_of_finite_order_unipotent_mod_two_primes E W Gr N m g₁ g₂ I₁ I₂
    hN hGrN hg₁ hg₂ hg hI₁ hI₂ hgI₁ hgI₂ (hsub I₁ hJI₁ hu₁) (hsub I₂ hJI₂ hu₂)
  intro a
  obtain ⟨l, hl⟩ := hevψ a
  have hlW : l ∈ W := ⟨a, hl.symm⟩
  have hGl : G l = l := by
    have := congrArg (fun T : Module.End (𝓞 E) W => ((T ⟨l, hlW⟩ : W) : Λ)) hGr1'
    exact (hGr ⟨l, hlW⟩).symm.trans (by simpa using this)
  have h := hkey l a hl
  rw [hGl, hl] at h
  rw [← hev, map_sub, ← h, sub_self]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemSmulTopOfNeatLevelStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_mem_smul_top_of_neat_level_alt : ∀ (E : Type) [Field E] [NumberField E] (La Λ Q : Type) [AddCommGroup La] [Module (𝓞 E) La] [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Q] [Module (𝓞 E) Q] (J : Ideal (𝓞 E)) (n N m g₁ g₂ : ℕ) (I₁ I₂ : Ideal (𝓞 E)) (ev : La →ₗ[𝓞 E] Q) (ψ : Λ →ₗ[𝓞 E] Q) (θ : Q →ₗ[𝓞 E] Q) (F : Λ →ₗ[𝓞 E] Λ) (gM : La →ₗ[𝓞 E] La), Module.Finite (𝓞 E) Λ → Module.IsTorsionFree (𝓞 E) Λ → 0 < n → (n : 𝓞 E) ∈ J → (∀ a, ev a = 0 ↔ a ∈ J • (⊤ : Submodule (𝓞 E) La)) → (∀ q : Q, (∀ c ∈ J, c • q = 0) → ∃ a, ev a = q) → (∀ b, ψ b = 0 ↔ ∃ b', b = n • b') → (∀ q : Q, n • q = 0 → ∃ b, ψ b = q) → (∀ b, ψ (F b) = θ (ψ b)) → (∀ a, θ (ev (gM a)) = ev a) → 0 < N → F ^ N = 1 → g₁.Prime → g₂.Prime → g₁ ≠ g₂ → I₁ ≠ ⊤ → I₂ ≠ ⊤ → (g₁ : 𝓞 E) ∈ I₁ → (g₂ : 𝓞 E) ∈ I₂ → J ≤ I₁ → J ≤ I₂ → (∀ x, ((gM - 1) ^ m) x ∈ I₁ • (⊤ : Submodule (𝓞 E) La)) → (∀ x, ((gM - 1) ^ m) x ∈ I₂ • (⊤ : Submodule (𝓞 E) La)) → ∀ a, gM a - a ∈ J • (⊤ : Submodule (𝓞 E) La) := by
  first | exact @GlobalTheory.sub_mem_smul_top_of_neat_level | exact GlobalTheory.sub_mem_smul_top_of_neat_level | (intros; apply GlobalTheory.sub_mem_smul_top_of_neat_level <;> assumption)
end
