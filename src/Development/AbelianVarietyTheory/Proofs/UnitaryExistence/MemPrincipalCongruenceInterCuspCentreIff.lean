module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DerivativeAlongTangentCombinationModuli
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntMulMem
namespace GlobalTheory.IntMulMem

open NumberField

theorem exists_int_mul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V]
    [Module E V] [Module (RingOfIntegers E) V] [IsScalarTower (RingOfIntegers E) E V]
    (Λ : Submodule (RingOfIntegers E) V) :
    ∀ v ∈ Submodule.span E (↑Λ : Set V), ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ (↑N : E) • v ∈ Λ := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simpa using Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, hNx⟩ := hx
    obtain ⟨M, hM, hMy⟩ := hy
    refine ⟨N * M, mul_ne_zero hN hM, ?_⟩
    have h1 : ((N * M : ℤ) : E) • x = ((M : ℤ) : RingOfIntegers E) • ((N : E) • x) := by
      rw [← algebraMap_smul E ((M : ℤ) : RingOfIntegers E), smul_smul]
      congr 1
      simp [mul_comm]
    have h2 : ((N * M : ℤ) : E) • y = ((N : ℤ) : RingOfIntegers E) • ((M : E) • y) := by
      rw [← algebraMap_smul E ((N : ℤ) : RingOfIntegers E), smul_smul]
      congr 1
      simp
    rw [smul_add, h1, h2]
    exact Λ.add_mem (Λ.smul_mem _ hNx) (Λ.smul_mem _ hMy)
  | smul c x _ hx =>
    obtain ⟨N, hN, hNx⟩ := hx
    have halg : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ c)
    obtain ⟨y, hy0, hyi⟩ := halg.exists_integral_multiple
    let a : RingOfIntegers E := ⟨y • c, hyi⟩
    refine ⟨y * N, mul_ne_zero hy0 hN, ?_⟩
    have h : ((y * N : ℤ) : E) • (c • x) = a • ((N : E) • x) := by
      rw [← algebraMap_smul E a, smul_smul, smul_smul]
      congr 1
      show _ = (y • c) * (N : E)
      rw [zsmul_eq_mul]; push_cast; ring
    rw [h]
    exact Λ.smul_mem _ hNx

end GlobalTheory.IntMulMem
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.SatDual

theorem exists_int_extension {L V : Type} [AddCommGroup L] [AddCommGroup V] [Module.Finite ℤ L]
    [Module.IsTorsionFree ℤ V] (q : L →ₗ[ℤ] V) (f : L →ₗ[ℤ] ℚ)
    (hf : ∀ x, q x = 0 → ∃ n : ℤ, f x = n) :
    ∃ g : L →ₗ[ℤ] ℤ, ∀ x, q x = 0 → (g x : ℚ) = f x := by
  haveI : Module.Finite ℤ (LinearMap.range q) := inferInstance
  haveI : Module.Free ℤ (LinearMap.range q) := Module.free_of_finite_type_torsion_free'
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property q.rangeRestrict LinearMap.id
    q.surjective_rangeRestrict
  let p : L →ₗ[ℤ] L := LinearMap.id - σ ∘ₗ q.rangeRestrict
  have hp : ∀ x, q (p x) = 0 := by
    intro x
    have h := congrArg Subtype.val (LinearMap.congr_fun hσ (q.rangeRestrict x))
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.codRestrict_apply] at h
    simp only [p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
    exact sub_eq_zero.2 h.symm
  have hp' : ∀ x, q x = 0 → p x = x := by
    intro x hx
    have : q.rangeRestrict x = 0 := Subtype.ext hx
    simp [p, this]
  choose n hn using fun x => hf (p x) (hp x)
  refine ⟨AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' n ?_), ?_⟩
  · intro a b
    have : ((n (a + b) : ℤ) : ℚ) = ((n a + n b : ℤ) : ℚ) := by
      push_cast
      rw [← hn, ← hn, ← hn, map_add (f := _), map_add (f := _)]
    exact_mod_cast this
  · intro x hx
    change ((n x : ℤ) : ℚ) = f x
    rw [← hn, hp' x hx]

variable {E : Type} [Field E] [NumberField E]

theorem exists_int_smul_mem {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (Λ : Submodule (𝓞 E) V) (v : V)
    (hv : v ∈ Submodule.span E (Λ : Set V)) : ∃ N : ℤ, N ≠ 0 ∧ (N : E) • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntMulMem.exists_int_mul_mem
  | exact _root_.GlobalTheory.IntMulMem.exists_int_mul_mem
  | (apply _root_.GlobalTheory.IntMulMem.exists_int_mul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntMulMem.exists_int_mul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntMulMem.exists_int_mul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntMulMem.exists_int_mul_mem ..)

variable [IsCMField E]

theorem herm_smul_snd {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) (a : E) :
    FD.herm G x (a • y) = FD.herm G x y * FD.cc a := by
  simp only [FD.herm, FD.cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pairing_pseudoBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (s : ℕ) (e : Fin s → (Fin r → E)) (c : Fin s → FractionalIdeal (𝓞 E)⁰ E), FD.cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → LinearIndependent E e → (∀ a : Fin s → E, (∑ b, a b • e b) ∈ LinearMap.range φ ↔ ∀ b, a b ∈ c b) → ∀ y : Fin s → E, (∃ x, ∀ b, ξ * FD.herm Gm (φ x) (e b) = y b) ↔ ∀ b, ∀ a ∈ c b, ∃ n : ℤ, Algebra.trace ℚ E (y b * FD.cc a) = n := by
  intro E _ _ _ H D r ξ Gm φ s e c _ hφ he hc y
  obtain ⟨hinj, hspan, -, -, hEF⟩ := hφ
  have hsingle : ∀ (b : Fin s) (a : E), ∑ b', (Pi.single b a : Fin s → E) b' • e b' = a • e b := by
    intro b a
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      simp [Pi.single_eq_of_ne hb']
    · simp
  have hmem : ∀ (b : Fin s) (a : E), a • e b ∈ LinearMap.range φ ↔ a ∈ c b := by
    intro b a
    rw [← hsingle, hc]
    constructor
    · intro h
      simpa using h b
    · intro h b'
      by_cases hb : b' = b
      · subst hb
        simpa using h
      · rw [Pi.single_eq_of_ne hb]
        exact FractionalIdeal.zero_mem _
  constructor
  · rintro ⟨x, hx⟩ b a ha
    obtain ⟨z, hz⟩ := (hmem b a).2 ha
    refine ⟨D.EF x z, ?_⟩
    rw [hEF, hz, herm_smul_snd, ← _root_.mul_assoc, hx]
  · intro hy
    haveI := D.fin
    haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
    let j : (Fin s → E) →ₗ[E] (Fin r → E) := Fintype.linearCombination E e
    have hj : LinearMap.ker j = ⊥ :=
      LinearMap.ker_eq_bot.2 he.fintypeLinearCombination_injective
    obtain ⟨π, hπ⟩ := j.exists_leftInverse_of_injective hj
    have hπ' : ∀ a, π (j a) = a := fun a => LinearMap.congr_fun hπ a
    let q : D.La →ₗ[ℤ] (Fin r → E) := AddMonoidHom.toIntLinearMap
      (AddMonoidHom.mk' (fun x => φ x - j (π (φ x))) (by
        intro a b
        simp only [map_add (f := _)]
        abel))
    let f : D.La →ₗ[ℤ] ℚ := AddMonoidHom.toIntLinearMap
      (AddMonoidHom.mk' (fun x => ∑ b, Algebra.trace ℚ E (y b * FD.cc (π (φ x) b))) (by
        intro a b
        simp only [map_add (f := _), Pi.add_apply, FD.cc, mul_add, Finset.sum_add_distrib]))
    have hq : ∀ x, q x = φ x - j (π (φ x)) := fun _ => rfl
    have hf : ∀ x, f x = ∑ b, Algebra.trace ℚ E (y b * FD.cc (π (φ x) b)) := fun _ => rfl
    obtain ⟨g, hg⟩ := exists_int_extension q f (by
      intro x hx
      rw [hq, sub_eq_zero] at hx
      have h1 : ∀ b, π (φ x) b ∈ c b := (hc _).1 ⟨x, hx⟩
      choose n hn using fun b => hy b _ (h1 b)
      refine ⟨∑ b, n b, ?_⟩
      rw [hf]
      push_cast
      exact Finset.sum_congr rfl fun b _ => hn b)
    obtain ⟨x, hx⟩ := D.unimod.2 g
    refine ⟨x, fun b => ?_⟩
    have key : ∀ a ∈ c b,
        Algebra.trace ℚ E ((ξ * FD.herm Gm (φ x) (e b) - y b) * FD.cc a) = 0 := by
      intro a ha
      obtain ⟨z, hz⟩ := (hmem b a).2 ha
      have hz' : φ z = j (Pi.single b a) := by
        rw [hz, ← hsingle]
        rfl
      have h1 := hg z (by rw [hq, hz', hπ', sub_self])
      rw [← hx, hEF, hz, herm_smul_snd, hf, hz', hπ', Finset.sum_eq_single b] at h1
      · rw [sub_mul, map_sub, _root_.mul_assoc, h1]
        simp
      · intro b' _ hb'
        simp [Pi.single_eq_of_ne hb', FD.cc]
      · simp
    rw [← sub_eq_zero]
    refine (traceForm_nondegenerate ℚ E).1 _ fun t => ?_
    obtain ⟨N, hN, hNt⟩ := exists_int_smul_mem (E := E) (LinearMap.range φ) (FD.cc t • e b)
      (by rw [LinearMap.coe_range, hspan]; trivial)
    rw [smul_smul, hmem] at hNt
    have h2 := key _ hNt
    have h3 : FD.cc ((N : E) * FD.cc t) = (N : ℚ) • t := by
      simp [FD.cc, Algebra.smul_def]
    rw [h3, mul_smul_comm, map_smul, smul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact absurd (by exact_mod_cast h2) hN
    · rw [Algebra.traceForm_apply]
      exact h2

end GlobalTheory.SatDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemPrincipalCongruenceInterCuspCentreIff
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem zMatE_congr_of_entries (X : Data E r) (N : ℕ) (cu : FJ.CuspFD X ρ)
    (c : Fin ρ → FractionalIdeal (𝓞 E)⁰ E)
    (hd : ∀ v ∈ X.Λ, ∀ b, ∀ a' ∈ c b, ∃ n : ℤ,
      Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v (cu.e b) * cc a') = n)
    (hc : ∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ c b)
    (β : Matrix (Fin ρ) (Fin ρ) E)
    (hβ : ∀ a b (y : E), (∀ a' ∈ c b, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) →
      ∃ z ∈ c a, β a b / X.ξ0 * y = (N : E) * z) :
    ∀ v ∈ X.Λ, ∃ w ∈ X.Λ, FJ.zMatE X cu.e β *ᵥ v = v + N • w := by
  intro v hv
  choose z hz hz' using fun a b => hβ a b _ (hd v hv b)
  refine ⟨∑ a, (∑ b, -z a b) • cu.e a, (hc _).2 fun a => ?_, ?_⟩
  · exact (c a : Submodule (𝓞 E) E).sum_mem fun b _ => (c a : Submodule (𝓞 E) E).neg_mem (hz a b)
  · rw [zMatE_mulVec, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    have h := hz' a b
    have h0 := X.ξ0_ne
    rw [mul_neg, ← h]
    field_simp

theorem mem_zGam_principal_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (r ρ : ℕ) (X : Data E r) (N : ℕ) (D : Datum H) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), LinearMap.range φ = X.Λ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (X.Gm a b) = X.Gm b a) ∧ X.Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ x) (φ y))) → (∀ γ : GL (Fin r) E, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧ ∀ v ∈ X.Λ, ∃ w ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + N • w) → (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) → ∀ β, β ∈ FJ.zGam X cu ↔ FJ.IsSkew β ∧ ∀ a b (y : E), (∀ a' ∈ cc' b, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) → ∃ z ∈ cc' a, β a b / X.ξ0 * y = (N : E) * z := by
  intro E _ _ _ H r ρ X N D φ cu c hΛ hφ hΓ hc β
  have hsd := GlobalTheory.SatDual.pairing_pseudoBasis E H D r (-X.ξ0) X.Gm φ ρ cu.e c
    (by rw [cc_neg', X.ξ0_im]) hφ cu.ind (by rw [hΛ]; exact hc)
  have hd : ∀ v ∈ X.Λ, ∀ b, ∀ a' ∈ c b, ∃ n : ℤ,
      Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v (cu.e b) * cc a') = n := by
    intro v hv
    rw [← hΛ] at hv
    obtain ⟨x, rfl⟩ := hv
    exact (hsd fun b => -X.ξ0 * herm X.Gm (φ x) (cu.e b)).1 ⟨x, fun _ => rfl⟩
  have h0 := X.ξ0_ne
  constructor
  · rintro ⟨hs, γ, hγ, e⟩
    refine ⟨hs, fun a b y hy => ?_⟩
    obtain ⟨x, hx⟩ := (hsd (Pi.single b y)).2 (by
      intro b' a' ha'
      by_cases hb : b' = b
      · subst hb
        simpa using hy a' ha'
      · exact ⟨0, by simp [Pi.single_eq_of_ne hb]⟩)
    obtain ⟨w, hw, hw'⟩ := ((hΓ γ).1 hγ).2 (φ x) (hΛ ▸ ⟨x, rfl⟩)
    rw [e, zMatE_mulVec, add_right_inj] at hw'
    have h1 : ∀ a, ∑ b', β a b' * herm X.Gm (φ x) (cu.e b') = -(β a b / X.ξ0 * y) := by
      intro a
      rw [Finset.sum_eq_single b]
      · have h2 := hx b
        rw [Pi.single_eq_same] at h2
        rw [← h2]
        field_simp
      · intro b' _ hb'
        have h2 := hx b'
        rw [Pi.single_eq_of_ne hb', mul_eq_zero, neg_eq_zero] at h2
        rw [h2.resolve_left h0, mul_zero]
      · simp
    simp only [h1] at hw'
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      rw [zero_smul] at hw'
      have h3 := Fintype.linearIndependent_iff.1 cu.ind _ hw' a
      exact ⟨0, FractionalIdeal.zero_mem _, by rw [mul_zero]; exact neg_eq_zero.1 h3⟩
    · have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
      have h3 : ∑ a, ((N : E)⁻¹ * (β a b / X.ξ0 * y)) • cu.e a = -w := by
        have h4 : w = (N : E)⁻¹ • (N • w) := by
          rw [← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ hN', one_smul]
        rw [h4, ← hw', Finset.smul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [smul_smul, ← neg_smul, mul_neg, neg_neg]
      refine ⟨_, (hc _).1 (h3 ▸ X.Λ.neg_mem hw) a, ?_⟩
      rw [mul_inv_cancel_left₀ hN']
  · rintro ⟨hs, hβ⟩
    have h1 := zMatE_congr_of_entries X N cu c hd hc β hβ
    have h2 := zMatE_congr_of_entries X N cu c hd hc (-β) (by
      intro a b y hy
      obtain ⟨z, hz, hz'⟩ := hβ a b y hy
      refine ⟨-z, (c a : Submodule (𝓞 E) E).neg_mem hz, ?_⟩
      rw [Matrix.neg_apply, neg_div, neg_mul, hz', mul_neg])
    have hm : FJ.zMatE X cu.e β * FJ.zMatE X cu.e (-β) = 1 := by
      rw [← zMatE_add, add_neg_cancel, zMatE_zero]
    have hm' : FJ.zMatE X cu.e (-β) * FJ.zMatE X cu.e β = 1 := by
      rw [← zMatE_add, neg_add_cancel, zMatE_zero]
    refine ⟨hs, ⟨_, _, hm, hm'⟩, (hΓ _).2 ⟨⟨zMatE_unitary X cu β hs, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩, h1⟩, rfl⟩
    · obtain ⟨w, hw, hw'⟩ := h1 x hx
      change FJ.zMatE X cu.e β *ᵥ x ∈ X.Λ
      rw [hw']
      exact X.Λ.add_mem hx (nsmul_mem hw N)
    · obtain ⟨w, hw, hw'⟩ := h2 _ hx
      change FJ.zMatE X cu.e β *ᵥ x ∈ X.Λ at hx
      change FJ.zMatE X cu.e (-β) *ᵥ (FJ.zMatE X cu.e β *ᵥ x) = FJ.zMatE X cu.e β *ᵥ x + _ at hw'
      rw [Matrix.mulVec_mulVec, hm', Matrix.one_mulVec] at hw'
      rw [hw']
      exact X.Λ.add_mem hx (nsmul_mem hw N)

end GlobalTheory.CuspCentre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemPrincipalCongruenceInterCuspCentreIffStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_principalCongruence_inter_cuspCentre_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (r ρ : ℕ) (X : Data E r) (N : ℕ) (D : Datum H) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), LinearMap.range φ = X.Λ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (X.Gm a b) = X.Gm b a) ∧ X.Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ x) (φ y))) → (∀ γ : GL (Fin r) E, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧ ∀ v ∈ X.Λ, ∃ w ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + N • w) → (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) → ∀ β, β ∈ FJ.zGam X cu ↔ FJ.IsSkew β ∧ ∀ a b (y : E), (∀ a' ∈ cc' b, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) → ∃ z ∈ cc' a, β a b / X.ξ0 * y = (N : E) * z := by
  first | exact @GlobalTheory.CuspCentre.mem_zGam_principal_iff | exact GlobalTheory.CuspCentre.mem_zGam_principal_iff | (intros; apply GlobalTheory.CuspCentre.mem_zGam_principal_iff <;> assumption)
end
