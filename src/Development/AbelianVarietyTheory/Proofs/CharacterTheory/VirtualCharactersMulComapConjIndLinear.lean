module

public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersIffSubCharacters

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterQuotientOfInjectiveIntertwining
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.LinearMapShortExactCommute
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.LinearMapShortExactCommute
namespace GlobalTheory

theorem trace_eq_add_of_shortExact (K : Type) [Field K]
    (U : Type) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (i : U →ₗ[K] V) (p : V →ₗ[K] W) (a : U →ₗ[K] U) (b : V →ₗ[K] V) (c : W →ₗ[K] W)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : LinearMap.range i = LinearMap.ker p)
    (hb : b ∘ₗ i = i ∘ₗ a) (hc : p ∘ₗ b = c ∘ₗ p) :
    LinearMap.trace K V b = LinearMap.trace K U a + LinearMap.trace K W c := by
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
  obtain ⟨r₀, hr₀⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  have hs' : ∀ w, p (s w) = w := fun w => LinearMap.congr_fun hs w
  have hr' : ∀ u, r₀ (i u) = u := fun u => LinearMap.congr_fun hr₀ u
  have hpi : ∀ u, p (i u) = 0 := fun u => by
    have : i u ∈ LinearMap.ker p := hex ▸ LinearMap.mem_range_self i u
    exact this
  have hb' : ∀ u, b (i u) = i (a u) := fun u => LinearMap.congr_fun hb u
  have hc' : ∀ v, p (b v) = c (p v) := fun v => LinearMap.congr_fun hc v
  let r : V →ₗ[K] U := r₀ ∘ₗ (LinearMap.id - s ∘ₗ p)
  have hri : ∀ u, r (i u) = u := fun u => by
    simp [r, hpi, hr']
  have hir : ∀ v, i (r v) = v - s (p v) := fun v => by
    have : v - s (p v) ∈ LinearMap.range i := by
      rw [hex, LinearMap.mem_ker, map_sub, hs', sub_self]
    obtain ⟨u, hu⟩ := this
    have h2 : r v = u := by
      show r₀ (v - s (p v)) = u
      rw [← hu, hr']
    rw [h2, hu]
  have hdec : b = (b ∘ₗ i) ∘ₗ r + (b ∘ₗ s) ∘ₗ p := by
    ext v
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hir, map_sub, sub_add_cancel]
  have h1 : r ∘ₗ (b ∘ₗ i) = a := by
    ext u
    simp only [LinearMap.comp_apply, hb', hri]
  have h2 : p ∘ₗ (b ∘ₗ s) = c := by
    ext w
    simp only [LinearMap.comp_apply, hc', hs']
  calc LinearMap.trace K V b
      = LinearMap.trace K V ((b ∘ₗ i) ∘ₗ r) + LinearMap.trace K V ((b ∘ₗ s) ∘ₗ p) := by
        rw [← map_add (f := _), ← hdec]
    _ = LinearMap.trace K U a + LinearMap.trace K W c := by
        rw [LinearMap.trace_comp_comm' r (b ∘ₗ i), LinearMap.trace_comp_comm' p (b ∘ₗ s), h1, h2]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.LinearMapShortExactCommuteStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_map_short_exact_commute : ∀ (K : Type) [Field K] (U : Type) [AddCommGroup U] [Module K U] [FiniteDimensional K U] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (i : U →ₗ[K] V) (p : V →ₗ[K] W) (a : U →ₗ[K] U) (b : V →ₗ[K] V) (c : W →ₗ[K] W), Function.Injective i → Function.Surjective p → LinearMap.range i = LinearMap.ker p → b ∘ₗ i = i ∘ₗ a → p ∘ₗ b = c ∘ₗ p → LinearMap.trace K V b = LinearMap.trace K U a + LinearMap.trace K W c := by
  first | exact @GlobalTheory.trace_eq_add_of_shortExact | exact GlobalTheory.trace_eq_add_of_shortExact | (intros; apply GlobalTheory.trace_eq_add_of_shortExact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterQuotientOfInjectiveIntertwining
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem exists_isChar_eq_add_of_injective : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W) (f : Representation.IntertwiningMap σ ρ), Function.Injective f → ∃ c : G → L, IsChar K L c ∧ ∀ g, algebraMap K L (ρ.character g) = algebraMap K L (σ.character g) + c g := by
  intro K L _ _ _ G _ V _ _ _ W _ _ _ ρ σ f hf
  have hcomm : ∀ g, ρ g ∘ₗ f.toLinearMap = f.toLinearMap ∘ₗ σ g := fun g =>
    (f.isIntertwining' g).symm
  have hle : ∀ g, LinearMap.range f.toLinearMap ≤ (LinearMap.range f.toLinearMap).comap (ρ g) := by
    rintro g _ ⟨w, rfl⟩
    exact ⟨σ g w, (LinearMap.congr_fun (hcomm g) w).symm⟩
  refine ⟨fun g => algebraMap K L ((ρ.quotient _ hle).character g),
    (GlobalTheory.T.isCharacterOverSubfield_of_representation K L G _ (ρ.quotient _ hle)).1, fun g => ?_⟩
  rw [← map_add (f := _)]
  congr 1
  refine GlobalTheory.T.linear_map_short_exact_commute K W V _ f.toLinearMap (LinearMap.range f.toLinearMap).mkQ (σ g) (ρ g)
    (ρ.quotient _ hle g) hf (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _).symm (hcomm g) ?_
  ext v
  rfl
end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterQuotientOfInjectiveIntertwiningStatement
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_character_quotient_of_injective_intertwining : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W) (f : Representation.IntertwiningMap σ ρ), Function.Injective f → ∃ c : G → L, IsChar K L c ∧ ∀ g, algebraMap K L (ρ.character g) = algebraMap K L (σ.character g) + c g := by
  first | exact @GlobalTheory.BI.exists_isChar_eq_add_of_injective | exact GlobalTheory.BI.exists_isChar_eq_add_of_injective | (intros; apply GlobalTheory.BI.exists_isChar_eq_add_of_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.isChar_mem_virt_complex {G : Type} [Group G] {χ : G → ℂ}
    (h : _root_.GlobalTheory.BI.IsChar ℂ ℂ χ) : χ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G :=
  AddSubgroup.subset_closure h

theorem _root_.GlobalTheory.BI.isChar_mul_complex {G : Type} [Group G] {a b : G → ℂ}
    (ha : _root_.GlobalTheory.BI.IsChar ℂ ℂ a) (hb : _root_.GlobalTheory.BI.IsChar ℂ ℂ b) :
    _root_.GlobalTheory.BI.IsChar ℂ ℂ (a * b) := by
  obtain ⟨n, ρ, hρ⟩ := ha
  obtain ⟨m, σ, hσ⟩ := hb
  have key := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G _ (Representation.tprod ρ σ)).1
  convert key using 1
  funext g
  simp [Representation.char_tensor, hρ, hσ]

private lemma trace_mulLeft_complex_lemma (z : ℂ) :
    LinearMap.trace ℂ ℂ (Algebra.lmul ℂ ℂ z) = z := by
  have hz : (Algebra.lmul ℂ ℂ z : ℂ →ₗ[ℂ] ℂ) = z • LinearMap.id := by
    ext x
    simp
  rw [hz, map_smul, LinearMap.trace_id]
  simp

theorem _root_.GlobalTheory.BI.isChar_monoidHom_complex {G : Type} [Group G] (lam : G →* ℂˣ) :
    _root_.GlobalTheory.BI.IsChar ℂ ℂ (fun g => (lam g : ℂ)) := by
  let ρ : Representation ℂ G ℂ :=
    (Algebra.lmul ℂ ℂ).toMonoidHom.comp ((Units.coeHom ℂ).comp lam)
  have key := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G ℂ ρ).1
  convert key using 1
  funext g
  simpa [ρ, Representation.character] using (trace_mulLeft_complex_lemma (lam g : ℂ)).symm

theorem _root_.GlobalTheory.BI.subgroupFunctionExtendByZero_add {G : Type} [Group G] (H : Subgroup G) (a b : H → ℂ)
    (g : G) :
    _root_.GlobalTheory.BI.ext0 H (a + b) g =
      _root_.GlobalTheory.BI.ext0 H a g + _root_.GlobalTheory.BI.ext0 H b g := by
  unfold _root_.GlobalTheory.BI.ext0
  split_ifs <;> simp

noncomputable def indAddHomComplex {G : Type} [Group G] [Finite G] (H : Subgroup G) : (H → ℂ) →+ (G → ℂ) :=
  AddMonoidHom.mk' (ind H) (fun a b => by
    funext g
    haveI := Fintype.ofFinite G
    simp only [ind, Pi.add_apply, subgroupFunctionExtendByZero_add, finsum_eq_sum_of_fintype, Finset.sum_add_distrib, mul_add])

theorem _root_.GlobalTheory.BI.virt_mul_comap_conj_ind_linear : ∀ (G : Type) [Group G] [Finite G],
    (∀ a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G, ∀ b ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G,
      a * b ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G) ∧
    (∀ a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G, ∀ (H : Type) [Group H] (f : H →* G),
      (fun h => a (f h)) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ H) ∧
    (∀ a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G, ∀ g x : G, a (x⁻¹ * g * x) = a g) ∧
    (∀ (H : Subgroup G) (ψ : H → ℂ), ψ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ H →
      _root_.GlobalTheory.BI.ind H ψ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G) ∧
    ∀ lam : G →* ℂˣ, (fun g => (lam g : ℂ)) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G := by
  intro G _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    induction ha using AddSubgroup.closure_induction with
    | mem a ha' =>
      induction hb using AddSubgroup.closure_induction with
      | mem b hb' => exact AddSubgroup.subset_closure (_root_.GlobalTheory.BI.isChar_mul_complex ha' hb')
      | zero => simpa using zero_mem _
      | add b c _ _ hb hc => simpa [mul_add] using add_mem hb hc
      | neg b _ hb => simpa [mul_neg] using neg_mem hb
    | zero => simpa using zero_mem _
    | add a c _ _ ha hc => simpa [add_mul] using add_mem ha hc
    | neg a _ ha => simpa [neg_mul] using neg_mem ha
  · intro a ha H _ f
    induction ha using AddSubgroup.closure_induction with
    | mem a ha' =>
      exact AddSubgroup.subset_closure
        ((_root_.GlobalTheory.isChar_restrict_conj_one ℂ ℂ G a ha').1 H f)
    | zero => exact zero_mem _
    | add a c _ _ ha hc => exact add_mem ha hc
    | neg a _ ha => exact neg_mem ha
  · intro a ha g x
    induction ha using AddSubgroup.closure_induction with
    | mem a ha' => exact (_root_.GlobalTheory.isChar_restrict_conj_one ℂ ℂ G a ha').2.1 g x
    | zero => rfl
    | add a c _ _ ha hc => simp [ha, hc]
    | neg a _ ha => simp [ha]
  · intro H ψ hψ
    change _root_.GlobalTheory.BI.indAddHomComplex H ψ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G
    induction hψ using AddSubgroup.closure_induction with
    | mem ψ hψ' =>
      exact AddSubgroup.subset_closure
        (_root_.GlobalTheory.BI.isChar_ind ℂ ℂ G H ψ hψ')
    | zero => simpa using zero_mem _
    | add ψ φ _ _ hψ hφ => simpa [map_add (f := _)] using add_mem hψ hφ
    | neg ψ _ hψ => simpa [map_neg] using neg_mem hψ
  · intro lam
    exact _root_.GlobalTheory.BI.isChar_mem_virt_complex (_root_.GlobalTheory.BI.isChar_monoidHom_complex lam)

end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinearStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.virtualCharacters_mul_comap_conj_ind_linear : ∀ (G : Type) [Group G] [Finite G], (∀ a ∈ Virt ℂ ℂ G, ∀ b ∈ Virt ℂ ℂ G, a * b ∈ Virt ℂ ℂ G) ∧ (∀ a ∈ Virt ℂ ℂ G, ∀ (H : Type) [Group H] (f : H →* G), (fun h => a (f h)) ∈ Virt ℂ ℂ H) ∧ (∀ a ∈ Virt ℂ ℂ G, ∀ g x : G, a (x⁻¹ * g * x) = a g) ∧ (∀ (H : Subgroup G) (ψ : H → ℂ), ψ ∈ Virt ℂ ℂ H → ind H ψ ∈ Virt ℂ ℂ G) ∧ ∀ lam : G →* ℂˣ, (fun g => (lam g : ℂ)) ∈ Virt ℂ ℂ G := by
  first | exact @GlobalTheory.BI.virt_mul_comap_conj_ind_linear | exact GlobalTheory.BI.virt_mul_comap_conj_ind_linear | (intros; apply GlobalTheory.BI.virt_mul_comap_conj_ind_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InnerProductRootPowerSumEqOfFrobeniusModEq
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InnerProductRootPowerSumEqOfFrobeniusModEq
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem exists_algEquiv_pow_card_pow (F : Type) [Field F] [Finite F] (i : ℕ) :
    ∃ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, ∀ α, σ α = α ^ (Nat.card F ^ i) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  refine ⟨FiniteField.frobeniusAlgEquivOfAlgebraic F (AlgebraicClosure F) ^ i, fun α => ?_⟩
  induction i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, FiniteField.frobeniusAlgEquivOfAlgebraic_apply, ← pow_mul,
      Nat.card_eq_fintype_card, ← pow_succ]

theorem ipGL_rootSum_eq_of_modEq (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ) (φ : Module.End F V → ℂ) (hc : IsClassFn φ)
    (hp : IsPrimitive φ) (hn : 0 < Module.finrank F V) (k l i : ℕ)
    (h : k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ Module.finrank F V - 1)]) :
    ipGL φ (fun g : Module.End F V => rootSum θ k (LinearMap.charpoly g)) =
      ipGL φ (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_algEquiv_pow_card_pow F i
  rw [GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_eq_torusSum F V θ φ hc hp hn k, GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_eq_torusSum F V θ φ hc hp hn l]
  set N := Nat.card F ^ Module.finrank F V - 1 with hN
  have hmem : ∀ α : AlgebraicClosure F, α ^ N = 1 ↔ σ α ^ N = 1 := by
    intro α
    rw [← map_pow]
    exact ⟨fun h => by rw [h, map_one], fun h => σ.injective (by rw [h, map_one])⟩
  have hbij : Set.BijOn σ {α : AlgebraicClosure F | α ^ N = 1} {α : AlgebraicClosure F | α ^ N = 1} := by
    refine ⟨fun α hα => (hmem α).1 hα, σ.injective.injOn, fun β hβ => ⟨σ.symm β, ?_, σ.apply_symm_apply β⟩⟩
    show (σ.symm β) ^ N = 1
    rw [hmem, σ.apply_symm_apply]
    exact hβ
  refine (finsum_mem_eq_of_bijOn σ hbij fun α hα => ?_).symm
  have hα' : α ^ N = 1 := hα
  have hm : minpoly F (σ α) = minpoly F α := minpoly.algEquiv_eq σ α
  have hθ : θ α ^ N = 1 := by rw [← map_pow, hα', map_one]
  have key : ∀ a : ℕ, θ α ^ a = θ α ^ (a % N) := by
    intro a
    conv_lhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, hθ, one_pow, mul_one]
  have hpow : θ α ^ (Nat.card F ^ i * k) = θ α ^ l := by
    rw [key, key l, mul_comm]
    exact congrArg _ h
  rw [hm, hσ, map_pow, ← pow_mul, hpow]

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InnerProductRootPowerSumEqOfFrobeniusModEqStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.innerProduct_rootPowerSum_eq_of_frobenius_modEq : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ) (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V → ∀ k l i : ℕ, k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ Module.finrank F V - 1)] → ipGL φ (fun g : Module.End F V => rootSum θ k (LinearMap.charpoly g)) = ipGL φ (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) := by
  first | exact @GlobalTheory.CuspGL.ipGL_rootSum_eq_of_modEq | exact GlobalTheory.CuspGL.ipGL_rootSum_eq_of_modEq | (intros; apply GlobalTheory.CuspGL.ipGL_rootSum_eq_of_modEq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIsCharEqAddOfPairNeZero
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem exists_isChar_eq_add_of_pair_ne_zero : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (φ a : G → L), IsIrrChar K L φ → IsChar K L a → pair a φ ≠ 0 → ∃ c : G → L, IsChar K L c ∧ a = φ + c := by
  intro K L _ _ _ _ _ G _ _ φ a hφ ha hp
  obtain ⟨m, σ, hσ, hφ⟩ := hφ
  obtain ⟨n, ρ, ha⟩ := ha
  have hφ' : φ = fun g => algebraMap K L (σ.character g) := funext hφ
  have ha' : a = fun g => algebraMap K L (ρ.character g) := funext ha
  have h := GlobalTheory.T.finiteGroupFunctionPairing_character_eq_finrank_intertwining K L G (Fin m → K) (Fin n → K) σ ρ
  rw [← hφ', ← ha'] at h
  have hex : ∃ f : Representation.IntertwiningMap σ ρ, f ≠ 0 := by
    by_contra hne
    push_neg at hne
    haveI : Subsingleton (Representation.IntertwiningMap σ ρ) :=
      ⟨fun x y => (hne x).trans (hne y).symm⟩
    apply hp
    rw [h, Module.finrank_zero_of_subsingleton, Nat.cast_zero]
  obtain ⟨f, hf⟩ := hex
  haveI := hσ
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  obtain ⟨c, hc, hc'⟩ := GlobalTheory.T.exists_character_quotient_of_injective_intertwining K L G (Fin n → K) (Fin m → K) ρ σ f hi
  refine ⟨c, hc, funext fun g => ?_⟩
  rw [Pi.add_apply, ha g, hφ g, hc' g]

end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumMobiusInverseCharpolyInvariantLe
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumMobiusInverseCharpolyInvariantLe
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem finsum_psi_le (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (A : Submodule F V) (g : Module.End F V)
    (hg : ∀ x ∈ A, g x ∈ A) :
    ∑ᶠ W : {W : Submodule F V // W ≤ A ∧ ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2.2)
      = s (LinearMap.charpoly (g.restrict hg)) := by
  rw [GlobalTheory.T.apply_charpoly_eq_finsum_psi_invariant_submodules F A s (g.restrict hg)]
  let e : {W : Submodule F V // W ≤ A ∧ ∀ x ∈ W, g x ∈ W} ≃
      {W' : Submodule F A // ∀ x ∈ W', g.restrict hg x ∈ W'} :=
    { toFun := fun W => ⟨W.1.comap A.subtype, fun x hx => by
        simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.coe_restrict_apply] at hx ⊢
        exact W.2.2 _ hx⟩
      invFun := fun W' => ⟨W'.1.map A.subtype, Submodule.map_subtype_le _ _, fun x hx => by
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
        exact Submodule.mem_map.2 ⟨_, W'.2 y hy, rfl⟩⟩
      left_inv := fun W => Subtype.ext (by
        change (W.1.comap A.subtype).map A.subtype = W.1
        rw [Submodule.map_comap_subtype]
        exact inf_eq_right.2 W.2.1)
      right_inv := fun W' => Subtype.ext (Submodule.comap_map_eq_of_injective A.injective_subtype _) }
  rw [← finsum_comp_equiv e]
  congr 1
  funext W
  have hc : (Submodule.comapSubtypeEquivOfLe W.2.1).conj
      ((g.restrict hg).restrict (e W).2) = g.restrict W.2.2 := by
    ext x
    simp [LinearEquiv.conj_apply, Submodule.comapSubtypeEquivOfLe]
  rw [← hc, GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj]
  rfl

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumMobiusInverseCharpolyInvariantLeStatement
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_mobiusInverseCharpoly_invariant_le : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ) (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A), ∑ᶠ W : {W : Submodule F V // W ≤ A ∧ ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2.2) = s (LinearMap.charpoly (g.restrict hg)) := by
  first | exact @GlobalTheory.CuspGL.finsum_psi_le | exact GlobalTheory.CuspGL.finsum_psi_le | (intros; apply GlobalTheory.CuspGL.finsum_psi_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIrrCharAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIrrCharAdd
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem exists_irreducible_subrepresentation {K G V : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K G V) :
    ∃ S : Subrepresentation ρ, S.toRepresentation.IsIrreducible := by
  classical
  have hex : ∃ m : ℕ, ∃ S : Subrepresentation ρ, S.toSubmodule ≠ ⊥ ∧
      Module.finrank K S.toSubmodule = m :=
    ⟨_, ⟨⊤, fun _ _ _ => Submodule.mem_top⟩, top_ne_bot, rfl⟩
  obtain ⟨S, hS, hm⟩ := Nat.find_spec hex
  have hmin : ∀ T : Subrepresentation ρ, T.toSubmodule ≠ ⊥ →
      Module.finrank K S.toSubmodule ≤ Module.finrank K T.toSubmodule := by
    intro T hT
    rw [hm]
    exact Nat.find_min' hex ⟨T, hT, rfl⟩
  have : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hS
  refine ⟨S, ?_⟩
  have : Nontrivial (Subrepresentation S.toRepresentation) :=
    ⟨⊥, ⊤, fun h => by
      have h' : (⊥ : Submodule K S.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top h'⟩
  refine ⟨fun T => ?_⟩
  by_cases hT : T.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hT)
  · right
    let T' : Subrepresentation ρ := ⟨T.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨S.toRepresentation g v, T.apply_mem_toSubmodule g hv, rfl⟩⟩
    have hT' : T'.toSubmodule ≠ ⊥ := by
      intro h
      apply hT
      have h2 : T.toSubmodule.map S.toSubmodule.subtype = ⊥ := h
      rwa [← Submodule.map_bot S.toSubmodule.subtype,
        (Submodule.map_injective_of_injective S.toSubmodule.injective_subtype).eq_iff] at h2
    have h1 := hmin T' hT'
    have h2 : Module.finrank K T'.toSubmodule = Module.finrank K T.toSubmodule :=
      Submodule.finrank_map_subtype_eq _ _
    have h3 : T.toSubmodule = ⊤ :=
      Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (h2 ▸ h1))
    exact Subrepresentation.toSubmodule_injective h3

theorem exists_irrChar_add : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (a : G → L), IsChar K L a → a ≠ 0 → ∃ φ c : G → L, IsIrrChar K L φ ∧ IsChar K L c ∧ a = φ + c := by
  intro K L _ _ _ G _ a ha h0
  obtain ⟨n, ρ, hρ⟩ := ha
  have hn : Nontrivial (Fin n → K) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply h0
    funext g
    have : ρ g = 0 := Subsingleton.elim _ _
    simp [hρ, Representation.character, this]
  obtain ⟨S, hS⟩ := exists_irreducible_subrepresentation ρ
  let f : Representation.IntertwiningMap S.toRepresentation ρ :=
    ⟨S.toSubmodule.subtype, fun g => by ext v; rfl⟩
  obtain ⟨c, hc, hcg⟩ := GlobalTheory.T.exists_character_quotient_of_injective_intertwining K L G _ _ ρ S.toRepresentation f
    S.toSubmodule.injective_subtype
  refine ⟨_, c, (GlobalTheory.T.isCharacterOverSubfield_of_representation K L G _ S.toRepresentation).2 hS, hc, ?_⟩
  funext g
  rw [hρ, hcg]
  rfl

end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIrrCharAddStatement
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isIrrChar_add_isChar_of_ne_zero : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (a : G → L), IsChar K L a → a ≠ 0 → ∃ φ c : G → L, IsIrrChar K L φ ∧ IsChar K L c ∧ a = φ + c := by
  first | exact @GlobalTheory.BI.exists_irrChar_add | exact GlobalTheory.BI.exists_irrChar_add | (intros; apply GlobalTheory.BI.exists_irrChar_add <;> assumption)
end
end
