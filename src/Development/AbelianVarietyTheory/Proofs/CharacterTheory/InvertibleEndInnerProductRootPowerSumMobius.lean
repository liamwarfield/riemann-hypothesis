module

public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassMobiusInverseMonicEq
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobi
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInductionIrreducible
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleCharacterLinearOrInducedAbelianByPrim
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIsCharEqAddOfPairNeZeroStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumMobius
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumMobius
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem IsAdditive.map_pow_monic {F : Type} [Field F] {s : F[X] → ℂ} (hs : IsAdditive s) {f : F[X]}
    (hf : f.Monic) (m : ℕ) : s (f ^ m) = m * s f := by
  induction m with
  | zero =>
    have h := hs 1 1 monic_one monic_one
    rw [mul_one] at h
    rw [pow_zero, Nat.cast_zero, zero_mul]
    linear_combination -h
  | succ m ih =>
    rw [pow_succ, hs _ _ (hf.pow m) hf, ih]
    push_cast
    ring

theorem ipGL_psi_rootSum (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (hn : 0 < Module.finrank F V)
    (k l : ℕ) :
    ipGL (psi (rootSum θ k) V) (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) =
      glCard F (Module.finrank F V) * (((Finset.range (Module.finrank F V)).filter
        (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ Module.finrank F V - 1)])).card : ℂ) := by
  classical
  set n := Module.finrank F V with hn_def
  set q := Nat.card F with hq_def
  have hq : 1 < q := Finite.one_lt_card
  have hN : 0 < q ^ n - 1 := by
    have : 1 < q ^ n := Nat.one_lt_pow hn.ne' hq
    omega
  obtain ⟨hadd, -⟩ := GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k
  have hclass : IsClassFn (psi (rootSum θ k) V) := fun e g => GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F _ V V e g
  have hprim := GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V _ hadd
  rw [GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_eq_torusSum F V θ _ hclass hprim hn l]

  have hS : {α : AlgebraicClosure F | α ^ (q ^ n - 1) = 1} =
      ↑((nthRoots (q ^ n - 1) (1 : AlgebraicClosure F)).toFinset) := by
    ext α
    simp [Polynomial.mem_nthRoots hN]
  rw [hS, finsum_mem_coe_finset]

  have key : ∀ α ∈ (nthRoots (q ^ n - 1) (1 : AlgebraicClosure F)).toFinset,
      ((n / (minpoly F α).natDegree : ℕ) : ℂ) *
          mass (psi (rootSum θ k) V) (minpoly F α ^ (n / (minpoly F α).natDegree)) * star (θ α ^ l) =
        glCard F n / ((q : ℂ) ^ n - 1) * ∑ i ∈ Finset.range n, θ α ^ (k * q ^ i) * star (θ α ^ l) := by
    intro α hα
    have hα' : α ∈ {α : AlgebraicClosure F | α ^ (q ^ n - 1) = 1} := by
      rw [hS]; exact hα
    obtain ⟨hdvd, -, hroot⟩ := GlobalTheory.T.frobeniusTorus_minpoly_degree_rootPowerSum F θ n hn α hα'
    have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
    have hmon : (minpoly F α).Monic := minpoly.monic hint
    have hirr : Irreducible (minpoly F α) := minpoly.irreducible hint
    have hd : 0 < (minpoly F α).natDegree := minpoly.natDegree_pos hint
    have hm : 0 < n / (minpoly F α).natDegree := Nat.div_pos (Nat.le_of_dvd hn hdvd) hd
    have hdeg : (minpoly F α ^ (n / (minpoly F α).natDegree)).natDegree = n := by
      rw [hmon.natDegree_pow]
      exact Nat.div_mul_cancel hdvd
    rw [GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V _ hadd _ (hmon.pow _) hdeg, hdeg,
      (GlobalTheory.T.additive_eq_polynomialVonMangoldt_convolution_one F _ hadd).2.1 _ _ hmon hirr hm]
    have h1 : ((n / (minpoly F α).natDegree : ℕ) : ℂ) * rootSum θ k (minpoly F α) =
        ∑ i ∈ Finset.range n, θ α ^ (k * q ^ i) := by
      rw [← IsAdditive.map_pow_monic hadd hmon, hroot]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_pow, ← pow_mul, Nat.mul_comm]
    rw [← Finset.sum_mul, ← h1]
    ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, Finset.sum_comm]

  have h2 : ∀ i, ∑ α ∈ (nthRoots (q ^ n - 1) (1 : AlgebraicClosure F)).toFinset,
      θ α ^ (k * q ^ i) * star (θ α ^ l) =
        if k * q ^ i ≡ l [MOD q ^ n - 1] then ((q ^ n - 1 : ℕ) : ℂ) else 0 := by
    intro i
    rw [← finsum_mem_coe_finset, ← hS]
    exact (GlobalTheory.T.frobeniusTorus_character_orthogonality F θ hθ n hn).2 _ _
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  have hc : ((q ^ n - 1 : ℕ) : ℂ) = (q : ℂ) ^ n - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hne : (q : ℂ) ^ n - 1 ≠ 0 := by
    rw [← hc]
    exact_mod_cast hN.ne'
  rw [hc]
  field_simp

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumMobiusStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_mobius : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → 0 < Module.finrank F V → ∀ k l : ℕ, ipGL (psi (rootSum θ k) V) (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) = glCard F (Module.finrank F V) * (((Finset.range (Module.finrank F V)).filter (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ Module.finrank F V - 1)])).card : ℂ) := by
  first | exact @GlobalTheory.CuspGL.ipGL_psi_rootSum | exact GlobalTheory.CuspGL.ipGL_psi_rootSum | (intros; apply GlobalTheory.CuspGL.ipGL_psi_rootSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfVirtualAndCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfVirtualAndCharacter
open GlobalTheory.BI
namespace GlobalTheory.BI

private theorem isChar_of_isIrrChar (K L : Type) [Field K] [Field L]
    [Algebra K L] {G : Type} [Group G] (φ : G → L) (hφ : _root_.GlobalTheory.BI.IsIrrChar K L φ) :
    _root_.GlobalTheory.BI.IsChar K L φ := by
  obtain ⟨n, ρ, _, hρ⟩ := hφ
  exact ⟨n, ρ, hρ⟩

theorem _root_.GlobalTheory.BI.isChar_of_isChar_of_mem_virt (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L]
    (G : Type) [Group G] [Finite G] (χ : G → L) (hχ : _root_.GlobalTheory.BI.IsChar L L χ) (hv : χ ∈ _root_.GlobalTheory.BI.Virt K L G) :
    _root_.GlobalTheory.BI.IsChar K L χ := by
  obtain ⟨a, b, ha, hb, hab⟩ := (_root_.GlobalTheory.BI.mem_virt_iff_sub K L G χ).1 hv
  obtain ⟨hadd, hnat, hpos, -⟩ := _root_.GlobalTheory.BI.pair_add_nat_pos_symm K L G
  obtain ⟨-, hnatL, -, -⟩ := _root_.GlobalTheory.BI.pair_add_nat_pos_symm L L G
  have key : ∀ c : G → L, _root_.GlobalTheory.BI.IsChar K L c →
      ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → a = χ + c → _root_.GlobalTheory.BI.IsChar K L χ := by
    refine _root_.GlobalTheory.BI.isChar_induction K L G _ ?_ ?_
    · intro a ha h
      rw [add_zero] at h
      exact h ▸ ha
    · intro φ c hφ hc ih a ha h
      have hφc := isChar_of_isIrrChar K L φ hφ
      obtain ⟨n₁, h₁⟩ := hnatL χ φ hχ (_root_.GlobalTheory.BI.isChar_baseChange K L G φ hφc)
      obtain ⟨n₂, hn₂, h₂⟩ := hpos φ hφ
      obtain ⟨n₃, h₃⟩ := hnat c φ hc hφc
      have hne : _root_.GlobalTheory.BI.pair a φ ≠ 0 := by
        rw [h, hadd, hadd, h₁, h₂, h₃]
        exact_mod_cast (by omega : n₁ + (n₂ + n₃) ≠ 0)
      obtain ⟨a', ha', ha'eq⟩ := _root_.GlobalTheory.BI.exists_isChar_eq_add_of_pair_ne_zero K L G φ a hφ ha hne
      refine ih a' ha' ?_
      have : φ + a' = φ + (χ + c) := by
        rw [← ha'eq, h]
        abel
      exact add_left_cancel this
  exact key b hb a ha (by rw [hab]; abel)

end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfVirtualAndCharacterStatement
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacterOverSubfield_of_virtual_and_character : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (χ : G → L), IsChar L L χ → χ ∈ Virt K L G → IsChar K L χ := by
  first | exact @GlobalTheory.BI.isChar_of_isChar_of_mem_virt | exact GlobalTheory.BI.isChar_of_isChar_of_mem_virt | (intros; apply GlobalTheory.BI.isChar_of_isChar_of_mem_virt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldAbelianByPrimePower
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldLinearOfPrimitiveRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldLinearOfPrimitiveRoot
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem isChar_linear : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (m : ℕ) (ζ : K) (lam : G →* Lˣ), m ≠ 0 → IsPrimitiveRoot ζ m → (∀ g : G, g ^ m = 1) → IsChar K L (fun g => (lam g : L)) := by
  intro K L _ _ _ G _ m ζ lam hm hζ hG
  haveI : NeZero m := ⟨hm⟩
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  have hζ' : IsPrimitiveRoot (algebraMap K L ζ) m := hζ.map_of_injective hinj
  have h : ∀ g : G, ∃ x : K, algebraMap K L x = (lam g : L) := by
    intro g
    have h1 : (lam g : L) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hG, map_one, Units.val_one]
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h1
    exact ⟨ζ ^ i, by rw [map_pow, hi]⟩
  choose μ hμ using h
  let μ' : G →* K :=
    { toFun := μ
      map_one' := hinj (by rw [hμ]; simp)
      map_mul' := fun a b => hinj (by rw [map_mul (algebraMap K L), hμ, hμ, hμ]; simp) }
  refine ⟨1, ((algebraMap K (Module.End K (Fin 1 → K))).toMonoidHom).comp μ', fun g => ?_⟩
  have : Representation.character (((algebraMap K (Module.End K (Fin 1 → K))).toMonoidHom).comp μ' : Representation K G (Fin 1 → K)) g = μ g := by
    change LinearMap.trace K (Fin 1 → K) (algebraMap K (Module.End K (Fin 1 → K)) (μ g)) = μ g
    rw [Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.trace_one]
    simp
  rw [this, hμ]
end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldLinearOfPrimitiveRootStatement
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacterOverSubfield_linear_of_primitiveRoot : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (m : ℕ) (ζ : K) (lam : G →* Lˣ), m ≠ 0 → IsPrimitiveRoot ζ m → (∀ g : G, g ^ m = 1) → IsChar K L (fun g => (lam g : L)) := by
  first | exact @GlobalTheory.BI.isChar_linear | exact GlobalTheory.BI.isChar_linear | (intros; apply GlobalTheory.BI.isChar_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldAbelianByPrimePower
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem isChar_of_abByP : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → AbByP G → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
  intro K L _ _ _ _ _ _ m ζ hm hζ
  have key : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → (∀ g : G, g ^ m = 1) → AbByP G →
      ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G _ _ hn hG hA χ hχ
      refine GlobalTheory.T.isCharacterOverSubfield_induction_irreducible L L G (fun a => IsChar K L a) (GlobalTheory.T.isCharacterOverSubfield_zero_and_add K L G).1 ?_ χ hχ
      intro φ c hφ _ hc
      refine (GlobalTheory.T.isCharacterOverSubfield_zero_and_add K L G).2 φ c ?_ hc
      rcases GlobalTheory.T.irreducibleCharacter_linear_or_induced_abelianByPrimePower L G φ hA hφ with ⟨lam, hlam⟩ | ⟨T, hT, ψ, hψ, rfl⟩
      · have : φ = fun g => (lam g : L) := funext hlam
        rw [this]
        exact GlobalTheory.T.isCharacterOverSubfield_linear_of_primitiveRoot K L G m ζ lam hm hζ hG
      · have hlt : Nat.card T < n := by
          rw [← hn]
          exact lt_of_le_of_ne (Subgroup.card_le_card_group T)
            (fun h => hT (Subgroup.eq_top_of_card_eq T h))
        refine GlobalTheory.T.isCharacterOverSubfield_inducedClassFunction K L G T ψ (ih _ hlt T rfl ?_ (GlobalTheory.T.isAbelianByPrimePowerGroup_subgroup G T hA) ψ hψ)
        intro g
        exact Subtype.ext (by simpa using hG g)
  intro G _ _
  exact key _ G rfl
end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldAbelianByPrimePowerStatement
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacterOverSubfield_abelianByPrimePower : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → AbByP G → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
  first | exact @GlobalTheory.BI.isChar_of_abByP | exact GlobalTheory.BI.isChar_of_abByP | (intros; apply GlobalTheory.BI.isChar_of_abByP <;> assumption)
end
end
