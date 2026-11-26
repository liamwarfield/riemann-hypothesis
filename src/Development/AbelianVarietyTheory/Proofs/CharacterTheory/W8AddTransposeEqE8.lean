module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
open Matrix Polynomial
open scoped BigOperators

namespace GlobalTheory

def E8 : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

def W8 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  1,  0, -1,  0,  0,  0,  0,  0;
       0,  1,  0, -1,  0,  0,  0,  0;
       0,  0,  1, -1,  0,  0,  0,  0;
       0,  0,  0,  1, -1,  0,  0,  0;
       0,  0,  0,  0,  1, -1,  0,  0;
       0,  0,  0,  0,  0,  1, -1,  0;
       0,  0,  0,  0,  0,  0,  1, -1;
       0,  0,  0,  0,  0,  0,  0,  1]

def E8inv : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  4,  5,  7, 10,  8,  6,  4,  2;
       5,  8, 10, 15, 12,  9,  6,  3;
       7, 10, 14, 20, 16, 12,  8,  4;
      10, 15, 20, 30, 24, 18, 12,  6;
       8, 12, 16, 24, 20, 15, 10,  5;
       6,  9, 12, 18, 15, 12,  8,  4;
       4,  6,  8, 12, 10,  8,  6,  3;
       2,  3,  4,  6,  5,  4,  3,  2]

def w8 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  4,  5,  3, -2, -2, -2, -2, -2;
       5,  8,  5, -3, -3, -3, -3, -3;
       7, 10,  7, -4, -4, -4, -4, -4;
      10, 15, 10, -5, -6, -6, -6, -6;
       8, 12,  8, -4, -4, -5, -5, -5;
       6,  9,  6, -3, -3, -3, -4, -4;
       4,  6,  4, -2, -2, -2, -2, -3;
       2,  3,  2, -1, -1, -1, -1, -1]

def E8roots : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  1,  2, -2,  0,  0,  0,  0,  0;
      -1,  2,  2, -2,  0,  0,  0,  0;
      -1,  0,  0,  2, -2,  0,  0,  0;
      -1,  0,  0,  0,  2, -2,  0,  0;
      -1,  0,  0,  0,  0,  2, -2,  0;
      -1,  0,  0,  0,  0,  0,  2, -2;
      -1,  0,  0,  0,  0,  0,  0,  2;
       1,  0,  0,  0,  0,  0,  0,  0]

theorem w8_add_transpose_eq_e8 : W8 + W8ᵀ = E8 := by decide

theorem e8_transpose : E8ᵀ = E8 := CartanMatrix.E₈_transpose

theorem e8_det_eq_one : E8.det = 1 := CartanMatrix.E₈_det

theorem e8inv_mul_e8 : E8inv * E8 = 1 := by decide

theorem e8_mul_e8inv : E8 * E8inv = 1 := by decide

theorem E8roots_transpose_mul_self : E8rootsᵀ * E8roots = (4 : ℤ) • E8 := by decide

theorem e8_posDef : (E8.map (fun x : ℤ => (x : ℝ))).PosDef := by
  set f : ℤ →+* ℝ := Int.castRingHom ℝ with hf
  change (E8.map f).PosDef
  have h : E8.map f = ((1 / 2 : ℝ) • E8roots.map f)ᴴ * ((1 / 2 : ℝ) • E8roots.map f) := by
    have h4 : (E8roots.map f)ᵀ * E8roots.map f = (4 : ℝ) • E8.map f := by
      rw [← Matrix.transpose_map, ← Matrix.map_mul, E8roots_transpose_mul_self]
      ext i j
      rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
        smul_eq_mul, map_mul]
      simp [hf]
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, h4, smul_smul, smul_smul]
    norm_num
  have hs : (E8.map f).PosSemidef := by
    rw [h]; exact Matrix.posSemidef_conjTranspose_mul_self _
  rw [hs.posDef_iff_det_ne_zero]
  have : (E8.map f).det = f E8.det := (RingHom.map_det f E8).symm
  rw [this, e8_det_eq_one, map_one]
  exact one_ne_zero

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.Imports
namespace GlobalTheory.UnimodularLatticeLemma

theorem main {L : Type} [Field L] [IsAlgClosed L] {ι V : Type} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] [Nontrivial V] (f : ι → Module.End L V)
    (hc : ∀ (a b : ι), f a * f b = f b * f a) :
    ∃ (v : V), v ≠ (0 : V) ∧ ∀ (b : ι), ∃ (μ : L), (f b : V → V) v = μ • v := by
  classical
  let S : Set (Submodule L V) := {W | W ≠ ⊥ ∧ ∀ b, ∀ x ∈ W, f b x ∈ W}
  have hS : (⊤ : Submodule L V) ∈ S := ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top⟩
  obtain ⟨W, hW, hmin⟩ := (wellFounded_lt (α := Submodule L V)).has_min S ⟨⊤, hS⟩
  have key : ∀ b, ∃ μ : L, ∀ x ∈ W, f b x = μ • x := by
    intro b
    have hWb : ∀ x ∈ W, f b x ∈ W := hW.2 b
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW.1
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((f b).restrict hWb)
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hw1 : (f b).restrict hWb w = μ • w := hw.apply_eq_smul
    have hw0 : w ≠ 0 := hw.2
    let W' : Submodule L V := W ⊓ LinearMap.ker (f b - μ • 1)
    have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ f b x = μ • x := by
      intro x
      simp only [W', Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    have hW'S : W' ∈ S := by
      refine ⟨?_, ?_⟩
      · intro h
        apply hw0
        have : (w : V) ∈ W' := by
          rw [hmem]
          refine ⟨w.2, ?_⟩
          have := congrArg Subtype.val hw1
          simpa using this
        rw [h, Submodule.mem_bot] at this
        exact Subtype.ext this
      · intro c x hx
        rw [hmem] at hx ⊢
        refine ⟨hW.2 c x hx.1, ?_⟩
        have h1 : f b (f c x) = (f b * f c) x := rfl
        rw [h1, hc b c, Module.End.mul_apply, hx.2, map_smul]
    have hle : W' ≤ W := inf_le_left
    have heq : W' = W := by
      by_contra hne
      exact hmin W' hW'S (lt_of_le_of_ne hle hne)
    refine ⟨μ, fun x hx => ?_⟩
    have : x ∈ W' := heq ▸ hx
    exact ((hmem x).1 this).2
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW.1
  refine ⟨v, hv0, fun b => ?_⟩
  obtain ⟨μ, hμ⟩ := key b
  exact ⟨μ, hμ v hvW⟩

end GlobalTheory.UnimodularLatticeLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
namespace GlobalTheory

theorem exists_common_eigenvector_of_commute {L : Type} [Field L] [IsAlgClosed L] {ι : Type}
    {V : Type} [AddCommGroup V] [Module L V] [FiniteDimensional L V] [Nontrivial V]
    (f : ι → Module.End L V) (hf : ∀ a b, f a * f b = f b * f a) :
    ∃ v : V, v ≠ 0 ∧ ∀ b, ∃ μ : L, f b v = μ • v := by
  apply _root_.GlobalTheory.UnimodularLatticeLemma.main <;> assumption

theorem exists_character_eigenvector_of_commute :
    ∀ (L : Type) [Field L] [IsAlgClosed L] (B : Type) [Group B] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] [Nontrivial V] (ρ : Representation L B V), (∀ a b, ρ a * ρ b = ρ b * ρ a) → ∃ (lam : B →* Lˣ) (v : V), v ≠ 0 ∧ ∀ b, ρ b v = (lam b : L) • v := by
  intro L _ _ B _ V _ _ _ _ ρ h
  obtain ⟨v, hv0, hv⟩ := exists_common_eigenvector_of_commute (fun b => ρ b) h
  choose μ hμ using hv
  have hinj : Function.Injective fun c : L => c • v := smul_left_injective L hv0
  let χ : B →* L :=
    { toFun := μ
      map_one' := hinj (by
        have := hμ 1
        simp only [map_one, Module.End.one_apply] at this
        simpa using this.symm)
      map_mul' := fun a b => hinj (by
        have h1 := hμ (a * b)
        simp only [map_mul, Module.End.mul_apply] at h1
        have h2 := hμ a
        have h3 := hμ b
        simp only at h2 h3 ⊢
        rw [← h1, h3, map_smul, h2, smul_smul, mul_comm]) }
  exact ⟨χ.toHomUnits, v, hv0, fun b => hμ b⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentatStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_character_eigenvector_of_commuting_representation : ∀ (L : Type) [Field L] [IsAlgClosed L] (B : Type) [Group B] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] [Nontrivial V] (ρ : Representation L B V), (∀ a b, ρ a * ρ b = ρ b * ρ a) → ∃ (lam : B →* Lˣ) (v : V), v ≠ 0 ∧ ∀ b, ρ b v = (lam b : L) • v := by
  first | exact @GlobalTheory.exists_character_eigenvector_of_commute | exact GlobalTheory.exists_character_eigenvector_of_commute | (intros; apply GlobalTheory.exists_character_eigenvector_of_commute <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.AsAlgebraHomSurjectiveOfFinrankIntertwiningMapEq
namespace GlobalTheory

open scoped MonoidAlgebra

theorem asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one :
    ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (τ : Representation K G V), Module.finrank K (Representation.IntertwiningMap τ τ) = 1 → Nontrivial V ∧ Function.Surjective τ.asAlgebraHom := by
  intro K _ _ G _ _ V _ _ _ τ h
  classical
  have : NeZero (Nat.card G : K) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hV : Nontrivial V := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : Subsingleton (Representation.IntertwiningMap τ τ) :=
      ⟨fun f g => Representation.IntertwiningMap.ext (Subsingleton.elim _ _)⟩
    rw [Module.finrank_zero_of_subsingleton] at h
    exact zero_ne_one h
  refine ⟨hV, ?_⟩
  have : Nontrivial τ.asModule := hV
  have hE : Module.finrank K (Module.End K[G] τ.asModule) = 1 := by
    rw [← (Representation.IntertwiningMap.equivAlgEnd τ).toLinearEquiv.finrank_eq]
    exact h
  have hscalar : ∀ φ : Module.End K[G] τ.asModule, ∃ c : K, c • (1 : Module.End K[G] τ.asModule) = φ :=
    (finrank_eq_one_iff_of_nonzero' _ one_ne_zero).mp hE
  have : IsScalarTower K (Module.End K[G] τ.asModule) τ.asModule := ⟨fun _ _ _ => rfl⟩
  have : Module.Finite (Module.End K[G] τ.asModule) τ.asModule :=
    Module.Finite.of_restrictScalars_finite K _ _
  intro f
  let F : Module.End (Module.End K[G] τ.asModule) τ.asModule :=
    { toFun := fun m => f m
      map_add' := fun x y => f.map_add x y
      map_smul' := fun φ m => by
        obtain ⟨c, rfl⟩ := hscalar φ
        exact f.map_smul c m }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := K[G]) (M := τ.asModule) F
  refine ⟨a, LinearMap.ext fun v => ?_⟩
  exact congrArg (fun g => g v) ha

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.OneMemOfMulMemOfForallPrimeNotDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.OneMemOfMulMemOfForallPrimeNotDvd
namespace GlobalTheory

theorem one_mem_of_mul_mem_of_forall_prime_not_dvd (X : Type) [Finite X]
    (S : AddSubgroup (X → ℤ)) (hmul : ∀ f ∈ S, ∀ g ∈ S, f * g ∈ S)
    (hp : ∀ (x : X) (p : ℕ), p.Prime → ∃ f ∈ S, ¬ (p : ℤ) ∣ f x) : (1 : X → ℤ) ∈ S := by
  classical
  have h1 : ∀ x : X, ∃ f ∈ S, f x = 1 := by
    intro x
    obtain ⟨d, hd⟩ := Int.subgroup_cyclic (S.map (Pi.evalAddMonoidHom (fun _ : X => ℤ) x))
    have hd1 : (d : ℤ).natAbs = 1 := by
      rw [Nat.eq_one_iff_not_exists_prime_dvd]
      intro p pp hpd
      obtain ⟨f, hf, hnd⟩ := hp x p pp
      apply hnd
      have hmem : f x ∈ AddSubgroup.zmultiples (d : ℤ) := by
        obtain ⟨z, hz⟩ := hd ⟨f x, ⟨f, hf, rfl⟩⟩
        rw [Int.mem_zmultiples_iff]
        refine ⟨z, ?_⟩
        simpa [zsmul_eq_mul, mul_comm] using (congrArg Subtype.val hz).symm
      exact (Int.natCast_dvd.mpr hpd).trans (Int.mem_zmultiples_iff.mp hmem)
    have : (1 : ℤ) ∈ AddSubgroup.zmultiples (d : ℤ) := by
      rw [Int.mem_zmultiples_iff]
      exact isUnit_iff_dvd_one.mp (Int.isUnit_iff_natAbs_eq.mpr hd1)
    have hmap : (1 : ℤ) ∈ S.map (Pi.evalAddMonoidHom (fun _ : X => ℤ) x) := by
      obtain ⟨z, hz⟩ := Int.mem_zmultiples_iff.mp this
      have hzmem : z • (d : ℤ) ∈ S.map (Pi.evalAddMonoidHom (fun _ : X => ℤ) x) :=
        AddSubgroup.zsmul_mem _ d.property z
      simpa [hz, mul_comm] using hzmem
    obtain ⟨f, hf, hfx⟩ := hmap
    exact ⟨f, hf, hfx⟩
  choose f hfS hf1 using h1
  have key : ∀ s : Finset X, 1 - ∏ x ∈ s, (1 - f x) ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have e : 1 - (1 - f a) * ∏ x ∈ s, (1 - f x)
          = f a + (1 - ∏ x ∈ s, (1 - f x)) - f a * (1 - ∏ x ∈ s, (1 - f x)) := by ring
      rw [e]
      exact S.sub_mem (S.add_mem (hfS a) ih) (hmul _ (hfS a) _ ih)
  haveI := Fintype.ofFinite X
  have h0 : ∏ x : X, (1 - f x) = 0 := by
    funext y
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ y) (by simp [hf1])
  simpa [h0] using key Finset.univ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.OneMemOfMulMemOfForallPrimeNotDvdStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_mem_of_mul_mem_of_forall_prime_exists_not_dvd : ∀ (X : Type) [Finite X] (S : AddSubgroup (X → ℤ)), (∀ f ∈ S, ∀ g ∈ S, f * g ∈ S) → (∀ (x : X) (p : ℕ), p.Prime → ∃ f ∈ S, ¬ (p : ℤ) ∣ f x) → (1 : X → ℤ) ∈ S := by
  first | exact @GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd | exact GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd | (intros; apply GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd <;> assumption)
end
end
