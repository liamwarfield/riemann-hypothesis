module

public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusMinpolyDegreeRootPowerSum
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsUnitIffCharpolyCoeffZeroNe
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePow
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SmulOneLeAndLeSmulOneIffEigenvalues

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersIffSubCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersIffSubCharacters
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem mem_virt_iff_sub (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (f : G → L) :
    f ∈ Virt K L G ↔ ∃ a b : G → L, IsChar K L a ∧ IsChar K L b ∧ f = a - b := by
  obtain ⟨h0, hadd⟩ := GlobalTheory.T.isCharacterOverSubfield_zero_and_add K L G
  unfold Virt
  constructor
  · intro hf
    induction hf using AddSubgroup.closure_induction with
    | mem x hx => exact ⟨x, 0, hx, h0, (sub_zero x).symm⟩
    | zero => exact ⟨0, 0, h0, h0, (sub_zero 0).symm⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨a, b, ha, hb, rfl⟩ := ihx
      obtain ⟨c, d, hc, hd, rfl⟩ := ihy
      exact ⟨a + c, b + d, hadd a c ha hc, hadd b d hb hd, by abel⟩
    | neg x _ ih =>
      obtain ⟨a, b, ha, hb, rfl⟩ := ih
      exact ⟨b, a, hb, ha, by abel⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact AddSubgroup.sub_mem _ (AddSubgroup.subset_closure ha) (AddSubgroup.subset_closure hb)
end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersIffSubCharactersStatement
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_virtualCharacters_iff_sub_characters : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (f : G → L), f ∈ Virt K L G ↔ ∃ a b : G → L, IsChar K L a ∧ IsChar K L b ∧ f = a - b := by
  first | exact @GlobalTheory.BI.mem_virt_iff_sub | exact GlobalTheory.BI.mem_virt_iff_sub | (intros; apply GlobalTheory.BI.mem_virt_iff_sub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseOneProdIco
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.SumGaussianMulProd
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.QBinomialSum

lemma prod_succ_succ (x : ℂ) (n a : ℕ) :
    ∏ i ∈ Finset.range (a + 1), (x ^ (n + 1) - x ^ i)
      = (x ^ (n + 1) - 1) * x ^ a * ∏ i ∈ Finset.range a, (x ^ n - x ^ i) := by
  rw [Finset.prod_range_succ']
  have : ∀ i, x ^ (n + 1) - x ^ (i + 1) = x * (x ^ n - x ^ i) := fun i => by ring
  simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  ring

lemma den_ne (x : ℂ) (hx : x ≠ 0) (h1 : ∀ k : ℕ, x ^ (k + 1) - 1 ≠ 0) (a : ℕ) :
    ∏ i ∈ Finset.range a, (x ^ a - x ^ i) ≠ 0 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [prod_succ_succ]
    exact mul_ne_zero (mul_ne_zero (h1 a) (pow_ne_zero _ hx)) ih

lemma sum_eq (x : ℂ) (hx : x ≠ 0) (h1 : ∀ k : ℕ, x ^ (k + 1) - 1 ≠ 0) (n : ℕ) :
    ∑ a ∈ Finset.range n,
      (∏ i ∈ Finset.range (a + 1), (x ^ n - x ^ i)) /
        (∏ i ∈ Finset.range (a + 1), (x ^ (a + 1) - x ^ i)) *
        ∏ i ∈ Finset.range a, (1 - x ^ (i + 1)) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    set c : ℕ → ℂ := fun a => (∏ i ∈ Finset.range a, (x ^ n - x ^ i)) /
        (∏ i ∈ Finset.range a, (x ^ a - x ^ i)) *
        ∏ i ∈ Finset.range a, (1 - x ^ (i + 1)) with hc
    have key : ∀ a, (∏ i ∈ Finset.range (a + 1), (x ^ (n + 1) - x ^ i)) /
        (∏ i ∈ Finset.range (a + 1), (x ^ (a + 1) - x ^ i)) *
        ∏ i ∈ Finset.range a, (1 - x ^ (i + 1)) =
        (∏ i ∈ Finset.range (a + 1), (x ^ n - x ^ i)) /
        (∏ i ∈ Finset.range (a + 1), (x ^ (a + 1) - x ^ i)) *
        (∏ i ∈ Finset.range a, (1 - x ^ (i + 1))) + (c a - c (a + 1)) := by
      intro a
      simp only [hc]
      rw [prod_succ_succ x n a, prod_succ_succ x a a,
        Finset.prod_range_succ (fun i => x ^ n - x ^ i),
        Finset.prod_range_succ (fun i => 1 - x ^ (i + 1))]
      have hd := den_ne x hx h1 a
      have h2 := h1 a
      have h3 := pow_ne_zero a hx
      generalize ∏ i ∈ Finset.range a, (x ^ a - x ^ i) = D at *
      generalize ∏ i ∈ Finset.range a, (x ^ n - x ^ i) = P at *
      generalize ∏ i ∈ Finset.range a, (1 - x ^ (i + 1)) = F at *
      field_simp
      ring
    have hz : ∏ i ∈ Finset.range (n + 1), (x ^ n - x ^ i) = 0 :=
      Finset.prod_eq_zero (Finset.self_mem_range_succ n) (sub_self _)
    simp only [key]
    rw [Finset.sum_add_distrib, Finset.sum_range_sub', Finset.sum_range_succ, ih, hz]
    have h0 : c 0 = 1 := by simp [hc]
    have hn : c (n + 1) = 0 := by simp only [hc, hz]; simp
    rw [h0, hn]
    push_cast
    simp

theorem sum_gaussian_mul_prod : ∀ (q n : ℕ) (N : ℕ → ℕ), 2 ≤ q → (∀ a, a ≤ n → N a * ∏ i ∈ Finset.range a, (q ^ a - q ^ i) = ∏ i ∈ Finset.range a, (q ^ n - q ^ i)) → ∑ a ∈ Finset.Icc 1 n, (N a : ℂ) * ∏ i ∈ Finset.Ico 1 a, (1 - (q : ℂ) ^ i) = n := by
  intro q n N hq hN
  have hx : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have h1 : ∀ k : ℕ, (q : ℂ) ^ (k + 1) - 1 ≠ 0 := by
    intro k h
    have h' : (q : ℂ) ^ (k + 1) = 1 := sub_eq_zero.mp h
    have h'' : q ^ (k + 1) = 1 := by exact_mod_cast h'
    have := Nat.one_lt_pow (n := k + 1) (a := q) (by omega) (by omega)
    omega
  have cast : ∀ m a, a ≤ m → ((∏ i ∈ Finset.range a, (q ^ m - q ^ i) : ℕ) : ℂ)
      = ∏ i ∈ Finset.range a, ((q : ℂ) ^ m - (q : ℂ) ^ i) := by
    intro m a ha
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by omega) (by omega))]
    push_cast
    rfl
  rw [← sum_eq (q : ℂ) hx h1 n, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' := Finset.mem_range.mp ha
  rw [Finset.prod_Ico_eq_prod_range, add_comm 1 a]
  simp only [Nat.add_sub_cancel]
  have h := congrArg (Nat.cast : ℕ → ℂ) (hN (a + 1) (by omega))
  rw [Nat.cast_mul, cast _ _ le_rfl, cast _ _ (by omega)] at h
  rw [← h, mul_div_cancel_right₀ _ (den_ne _ hx h1 (a + 1))]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [add_comm]

end GlobalTheory.QBinomialSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseOneProdIco
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

noncomputable def oneValue (q a : ℕ) : ℂ :=
  if a = 0 then 0 else ∏ i ∈ Finset.Ico 1 a, (1 - (q : ℂ) ^ i)

theorem sum_oneValue_finrank (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Fintype (Submodule F V)] :
    ∑ W : Submodule F V, oneValue (Nat.card F) (Module.finrank F W) = (Module.finrank F V : ℂ) := by
  classical
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have h := GlobalTheory.QBinomialSum.sum_gaussian_mul_prod (Nat.card F) (Module.finrank F V)
    (fun a => Nat.card {W : Submodule F V // Module.finrank F W = a}) hq
    (fun a ha => GlobalTheory.T.card_subspaces_of_finrank_mul_card_bases F V a ha)
  rw [← h, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.Icc 0 (Module.finrank F V))
    (g := fun W : Submodule F V => Module.finrank F W)
    (fun W _ => Finset.mem_Icc.2 ⟨Nat.zero_le _, W.finrank_le⟩)]
  have h2 : ∀ a : ℕ, ∑ W ∈ Finset.univ.filter (fun W : Submodule F V => Module.finrank F W = a),
      oneValue (Nat.card F) (Module.finrank F W) =
      (Nat.card {W : Submodule F V // Module.finrank F W = a} : ℂ) * oneValue (Nat.card F) a := by
    intro a
    rw [Finset.sum_congr rfl (g := fun _ => oneValue (Nat.card F) a)
      (fun W hW => by rw [(Finset.mem_filter.1 hW).2]), Finset.sum_const, nsmul_eq_mul,
      Nat.card_eq_fintype_card (α := {W : Submodule F V // Module.finrank F W = a}), Fintype.card_subtype]
  simp only [h2]
  symm
  refine Finset.sum_subset_zero_on_sdiff (Finset.Icc_subset_Icc_left (Nat.zero_le 1)) ?_ ?_
  · intro a ha
    have : a = 0 := by
      simp only [Finset.mem_sdiff, Finset.mem_Icc] at ha
      omega
    simp [this, oneValue]
  · intro a ha
    have : a ≠ 0 := by
      simp only [Finset.mem_Icc] at ha
      omega
    simp [this, oneValue]

theorem psi_one_eq_oneValue (F : Type) [Field F] [Finite F] (s : F[X] → ℂ)
    (hs : ∀ j : ℕ, s ((X - C 1) ^ j) = j) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.finrank F V = n →
      psi s V 1 = oneValue (Nat.card F) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ hn
    classical
    haveI : Finite V := Module.finite_of_finite F
    haveI : Fintype (Submodule F V) := Fintype.ofFinite _
    have hc : LinearMap.charpoly (1 : Module.End F V) = (X - C 1) ^ n := by
      rw [LinearMap.charpoly_one, hn, C_1]
    rw [psi_eq, hc, hs]
    have h1 : ∀ W : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, (1 : Module.End F V) x ∈ W},
        psi s W.1 ((1 : Module.End F V).restrict W.2.2) = oneValue (Nat.card F) (Module.finrank F W.1) := by
      intro W
      have : (1 : Module.End F V).restrict W.2.2 = (1 : Module.End F W.1) := by
        ext x
        rfl
      rw [this]
      exact ih _ (hn ▸ Submodule.finrank_lt W.2.1) _ rfl
    rw [finsum_congr h1, finsum_eq_sum_of_fintype,
      ← Finset.sum_subtype (Finset.univ.erase (⊤ : Submodule F V)) (by intro W; simp)
        (fun W : Submodule F V => oneValue (Nat.card F) (Module.finrank F W))]
    have h2 := sum_oneValue_finrank F V
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⊤ : Submodule F V)), finrank_top, hn] at h2
    rw [← h2]
    ring

theorem psi_one (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (s : F[X] → ℂ) (hs : ∀ j : ℕ, s ((X - C 1) ^ j) = j) (h : 0 < Module.finrank F V) :
    psi s V 1 = ∏ i ∈ Finset.Ico 1 (Module.finrank F V), (1 - (Nat.card F : ℂ) ^ i) := by
  rw [psi_one_eq_oneValue F s hs _ V rfl, oneValue, if_neg h.ne']

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseOneProdIcoStatement
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantSubspaceMobiusInverse_one_prod_Ico : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), (∀ j : ℕ, s ((X - C 1) ^ j) = j) → 0 < Module.finrank F V → psi s V 1 = ∏ i ∈ Finset.Ico 1 (Module.finrank F V), (1 - (Nat.card F : ℂ) ^ i) := by
  first | exact @GlobalTheory.CuspGL.psi_one | exact GlobalTheory.CuspGL.psi_one | (intros; apply GlobalTheory.CuspGL.psi_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInducedClassFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterFinsumConjSubgroupFunctionExtendByZer
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterFinsumConjSubgroupFunctionExtendByZer
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

private theorem trace_block_permutation (K : Type) [Field K] (X : Type) [Fintype X] [DecidableEq X]
    (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (π : X → X)
    (A : X → W →ₗ[K] W) :
    LinearMap.trace K (X → W) (LinearMap.pi fun q => A q ∘ₗ LinearMap.proj (π q))
      = ∑ q, if π q = q then LinearMap.trace K W (A q) else 0 := by
  have hdec : (LinearMap.pi fun q => A q ∘ₗ LinearMap.proj (π q) : (X → W) →ₗ[K] (X → W))
      = ∑ q, LinearMap.single K (fun _ : X => W) q ∘ₗ (A q ∘ₗ LinearMap.proj (π q)) := by
    apply LinearMap.ext
    intro f
    funext p
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hdec, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  split_ifs with h
  · have hid : LinearMap.proj (π q) ∘ₗ LinearMap.single K (fun _ : X => W) q = LinearMap.id := by
      apply LinearMap.ext
      intro w
      simp [h]
    rw [hid, LinearMap.comp_id]
  · have hz : LinearMap.proj (π q) ∘ₗ LinearMap.single K (fun _ : X => W) q = 0 := by
      apply LinearMap.ext
      intro w
      simp [h]
    rw [hz, LinearMap.comp_zero, map_zero]

section
variable {G : Type} [Group G] (H : Subgroup G)

theorem cosetCocycle_mem (g : G) (q : G ⧸ H) : q.out⁻¹ * g * (g⁻¹ • q).out ∈ H := by
  have h : ((g⁻¹ * q.out : G) : G ⧸ H) = (((g⁻¹ • q).out : G) : G ⧸ H) := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  have hm := QuotientGroup.eq.mp h
  simpa [mul_assoc] using hm

def cosetCocycle (g : G) (q : G ⧸ H) : H := ⟨_, cosetCocycle_mem H g q⟩

theorem cosetCocycle_one (q : G ⧸ H) : cosetCocycle H 1 q = 1 := by
  apply Subtype.ext
  simp [cosetCocycle]

theorem cosetCocycle_mul (a b : G) (q : G ⧸ H) :
    cosetCocycle H (a * b) q = cosetCocycle H a q * cosetCocycle H b (a⁻¹ • q) := by
  apply Subtype.ext
  simp only [cosetCocycle, Subgroup.coe_mul]
  rw [mul_inv_rev, mul_smul]
  group

theorem inv_smul_eq_iff_conj_mem (g : G) (q : G ⧸ H) :
    g⁻¹ • q = q ↔ q.out⁻¹ * g * q.out ∈ H := by
  have hs : g⁻¹ • q = ((g⁻¹ * q.out : G) : G ⧸ H) := by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  calc g⁻¹ • q = q ↔ ((g⁻¹ * q.out : G) : G ⧸ H) = ((q.out : G) : G ⧸ H) := by
        rw [hs, QuotientGroup.out_eq']
    _ ↔ q.out⁻¹ * g * q.out ∈ H := by
        rw [QuotientGroup.eq]
        simp [mul_assoc]

def cosetIndRep {K W : Type} [Field K] [AddCommGroup W] [Module K W] (σ : Representation K H W) :
    Representation K G (G ⧸ H → W) where
  toFun g := LinearMap.pi fun q => σ (cosetCocycle H g q) ∘ₗ LinearMap.proj (g⁻¹ • q)
  map_one' := by
    apply LinearMap.ext
    intro f
    funext q
    simp [cosetCocycle_one]
  map_mul' a b := by
    apply LinearMap.ext
    intro f
    funext q
    simp [cosetCocycle_mul, mul_smul]
end

theorem isChar_finsum_conj_ext0_of_isChar :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), IsChar K L ψ → IsChar K L (fun g : G => ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out)) := by
  intro K L _ _ _ G _ _ H ψ hψ
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  obtain ⟨n, σ, hσ⟩ := hψ
  obtain ⟨m, ρ, hρ⟩ :=
    (isChar_and_isIrrChar_of_rep K L G (G ⧸ H → Fin n → K) (cosetIndRep H σ)).1
  refine ⟨m, ρ, fun g => ?_⟩
  have hg := hρ g
  simp only at hg
  rw [← hg]
  show (∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out)) = _
  have hc : (cosetIndRep H σ).character g
      = ∑ q, if g⁻¹ • q = q then LinearMap.trace K (Fin n → K) (σ (cosetCocycle H g q)) else 0 :=
    trace_block_permutation K (G ⧸ H) (Fin n → K) (fun q => g⁻¹ • q)
      (fun q => σ (cosetCocycle H g q))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [finsum_eq_sum_of_fintype, hc, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : g⁻¹ • q = q
  · have hm : q.out⁻¹ * g * q.out ∈ H := (inv_smul_eq_iff_conj_mem H g q).mp h
    have he : (⟨q.out⁻¹ * g * q.out, hm⟩ : H) = cosetCocycle H g q :=
      Subtype.ext (by simp [cosetCocycle, h])
    rw [if_pos h, ext0, dite_eq_left hm, hσ, he]
    rfl
  · have hm : q.out⁻¹ * g * q.out ∉ H := fun hm => h ((inv_smul_eq_iff_conj_mem H g q).mpr hm)
    rw [if_neg h, ext0, dite_eq_right hm, map_zero]

end GlobalTheory.BI
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterFinsumConjSubgroupFunctionExtendByZerStatement
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacter_finsum_conj_subgroupFunctionExtendByZero : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), IsChar K L ψ → IsChar K L (fun g : G => ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out)) := by
  first | exact @GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar | exact GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar | (intros; apply GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInducedClassFunction
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem isChar_ind : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L]
    (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L),
    IsChar K L ψ → IsChar K L (ind H ψ) := by
  intro K L _ _ _ _ _ G _ _ H ψ h
  have hcl : ∀ a x : H, ψ (x⁻¹ * a * x) = ψ a := (GlobalTheory.T.isCharacterOverSubfield_restrict_classFunction_one K L H ψ h).2.1
  have e : ind H ψ = fun g : G => ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out) :=
    funext (GlobalTheory.T.inducedClassFunctionFromSubgroup_eq_finsum_cosets L G H ψ hcl)
  rw [e]
  exact GlobalTheory.T.isCharacter_finsum_conj_subgroupFunctionExtendByZero K L G H ψ h
end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInducedClassFunctionStatement
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacterOverSubfield_inducedClassFunction : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), IsChar K L ψ → IsChar K L (ind H ψ) := by
  first | exact @GlobalTheory.BI.isChar_ind | exact GlobalTheory.BI.isChar_ind | (intros; apply GlobalTheory.BI.isChar_ind <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyEqFinsumPsi
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyEqFinsumPsi
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem charpoly_eq_finsum_psi (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (g : Module.End F V) :
    s (LinearMap.charpoly g) =
      ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2) := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) := Finite.of_injective _ (SetLike.coe_injective (A := Submodule F V))
  haveI := Fintype.ofFinite {W : Submodule F V // ∀ x ∈ W, g x ∈ W}
  haveI := Fintype.ofFinite {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W}
  let T : {W : Submodule F V // ∀ x ∈ W, g x ∈ W} := ⟨⊤, fun _ _ => Submodule.mem_top⟩
  have hT : psi s T.1 (g.restrict T.2) = psi s V g := by
    rw [← psi_conj F s T.1 V Submodule.topEquiv (g.restrict T.2)]
    congr 1
  rw [finsum_eq_sum_of_fintype, ← Finset.add_sum_erase _ _ (Finset.mem_univ T), hT, psi_eq,
    finsum_eq_sum_of_fintype]
  rw [sub_add, eq_comm, sub_eq_self, sub_eq_zero]
  refine Finset.sum_bij (fun W _ => ⟨W.1, W.2.2⟩) ?_ ?_ ?_ ?_
  · intro W _
    refine Finset.mem_erase.2 ⟨fun h => W.2.1 (congrArg Subtype.val h), Finset.mem_univ _⟩
  · intro a _ b _ h
    exact Subtype.ext (Subtype.mk.inj h)
  · intro b hb
    exact ⟨⟨b.1, fun h => (Finset.mem_erase.1 hb).1 (Subtype.ext h), b.2⟩, Finset.mem_univ _, rfl⟩
  · intro a _
    rfl

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyEqFinsumPsiStatement
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.apply_charpoly_eq_finsum_psi_invariant_submodules : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ) (g : Module.End F V), s (LinearMap.charpoly g) = ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2) := by
  first | exact @GlobalTheory.CuspGL.charpoly_eq_finsum_psi | exact GlobalTheory.CuspGL.charpoly_eq_finsum_psi | (intros; apply GlobalTheory.CuspGL.charpoly_eq_finsum_psi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveExtendZeroOfSumUnipotentRadical
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveExtendZeroOfSumUnipotentRadical
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.CuspGL

theorem exists_linearEquiv_mem_iff_of_finrank_eq {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A B : Submodule F V) (h : Module.finrank F A = Module.finrank F B) :
    ∃ e : V ≃ₗ[F] V, ∀ x, e x ∈ B ↔ x ∈ A := by
  obtain ⟨A', hA⟩ := A.exists_isCompl
  obtain ⟨B', hB⟩ := B.exists_isCompl
  have h' : Module.finrank F A' = Module.finrank F B' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hA
    have h2 := Submodule.finrank_add_eq_of_isCompl hB
    omega
  let e1 := LinearEquiv.ofFinrankEq A B h
  let e2 := LinearEquiv.ofFinrankEq A' B' h'
  refine ⟨(Submodule.prodEquivOfIsCompl A A' hA).symm ≪≫ₗ (e1.prodCongr e2) ≪≫ₗ
    Submodule.prodEquivOfIsCompl B B' hB, fun x => ?_⟩
  obtain ⟨⟨a, a'⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl A A' hA).surjective x
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  simp only [LinearEquiv.prodCongr_apply, Submodule.coe_prodEquivOfIsCompl']
  rw [B.add_mem_iff_right (e1 a).2, A.add_mem_iff_right a.2,
    Submodule.mem_left_iff_eq_zero_of_disjoint hB.disjoint,
    Submodule.mem_left_iff_eq_zero_of_disjoint hA.disjoint]
  simp

theorem finsum_nilRad_extZero_eq_zero (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ)
    (hχ : IsChar ℂ ℂ χ) (A : Submodule F (Fin d → F)) (H : Subgroup (GL (Fin d) F))
    (hb : Set.BijOn (fun u : GL (Fin d) F => Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1)
      (H : Set (GL (Fin d) F)) (nilRad A))
    (h0 : ∑ᶠ u ∈ (H : Set (GL (Fin d) F)), χ u = 0)
    (g : Module.End F (Fin d → F)) (hg : ∀ x ∈ A, g x ∈ A) :
    ∑ᶠ h ∈ nilRad A, extZero χ (g + h) = 0 := by
  obtain ⟨e1, e2, -, -⟩ := GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties F d χ
  by_cases hu : IsUnit g
  · have hm : IsUnit (LinearMap.toMatrix' g) := by
      have := hu.map (LinearMap.toMatrixAlgEquiv' (R := F) (n := Fin d))
      exact this
    obtain ⟨x, hx⟩ := hm
    have hgx : Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) = g := by
      rw [hx, Matrix.toLin'_toMatrix']
    have : Finite (Module.End F (Fin d → F)) := Module.finite_of_finite F
    have hb2 : Set.BijOn (fun h : Module.End F (Fin d → F) => g * h) (nilRad A) (nilRad A) := by
      refine ((Set.toFinite _).injOn_iff_bijOn_of_mapsTo ?_).1 ?_
      · intro h hh
        exact ⟨fun y => hg _ (hh.1 y), fun y hy => by simp [hh.2 y hy]⟩
      · intro a _ b _ hab
        exact hu.mul_left_cancel hab
    have h1 := GlobalTheory.T.character_coset_sum_eq_zero_of_subgroup_sum _ χ hχ H
      ((finsum_set_coe_eq_finsum_mem (f := χ) (H : Set (GL (Fin d) F))).trans h0) x
    have h2 := (finsum_set_coe_eq_finsum_mem (f := fun u => χ (x * u)) (H : Set (GL (Fin d) F))).symm.trans h1
    rw [← h2]
    symm
    refine finsum_mem_eq_of_bijOn _ (hb2.comp hb) fun u _ => ?_
    rw [← e1]
    congr 1
    simp only [Function.comp, Units.val_mul, Matrix.toLin'_mul, hgx, mul_sub, mul_one]
    rw [add_sub_cancel]
    rfl
  · refine finsum_mem_of_eqOn_zero fun h hh => ?_
    refine e2 _ fun hu' => hu ?_
    have hc := (GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F _ A g hg).2 h hh
    rw [LinearMap.isUnit_iff_isUnit_det, LinearMap.det_eq_sign_charpoly_coeff] at hu' ⊢
    rwa [hc] at hu'

theorem isPrimitive_extZero_of_sum_unipotent : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ), IsChar ℂ ℂ χ → (∀ a : ℕ, 0 < a → a < d → ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}, χ u = 0) → IsPrimitive (extZero χ) := by
  intro F _ _ d χ hχ hs A hA0 hA1 g hg
  have ha0 : 0 < Module.finrank F A := by
    rw [Nat.pos_iff_ne_zero]
    exact fun h => hA0 (Submodule.finrank_eq_zero.1 h)
  have ha1 : Module.finrank F A < d := by
    have := Submodule.finrank_lt hA1
    simpa using this
  obtain ⟨B, H, hB, hH, hb⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F d _ ha1.le
  have h0 := hs _ ha0 ha1
  rw [← hH] at h0
  obtain ⟨e, he⟩ := exists_linearEquiv_mem_iff_of_finrank_eq A B hB.symm
  have hcl := (GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties F d χ).2.2.2 (GlobalTheory.isChar_restrict_conj_one ℂ ℂ _ χ hχ).2.1
  have key := finsum_nilRad_extZero_eq_zero F d χ hχ B H hb h0 (e.conj g) (fun x hx => by
    rw [LinearEquiv.conj_apply_apply, he]
    apply hg
    rw [← he]
    simpa using hx)
  rw [← key]
  refine finsum_mem_eq_of_bijOn (fun h => e.conj h) ⟨fun h hh => ⟨fun y => ?_, fun y hy => ?_⟩,
    e.conj.injective.injOn, fun h hh => ⟨e.symm.conj h, ⟨fun y => ?_, fun y hy => ?_⟩, by ext y; simp [LinearEquiv.conj_apply_apply]⟩⟩ fun h _ => ?_
  · rw [LinearEquiv.conj_apply_apply, he]
    exact hh.1 _
  · rw [LinearEquiv.conj_apply_apply, hh.2 _ (by rw [← he]; simpa using hy), map_zero]
  · rw [← he, LinearEquiv.conj_apply_apply]
    simpa using hh.1 _
  · rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, hh.2 _ ((he y).2 hy), map_zero]
  · rw [← map_add (f := _), hcl]

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveExtendZeroOfSumUnipotentRadicalStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrimitive_extendZero_of_sum_unipotentRadical : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ), IsChar ℂ ℂ χ → (∀ a : ℕ, 0 < a → a < d → ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}, χ u = 0) → IsPrimitive (extZero χ) := by
  first | exact @GlobalTheory.CuspGL.isPrimitive_extZero_of_sum_unipotent | exact GlobalTheory.CuspGL.isPrimitive_extZero_of_sum_unipotent | (intros; apply GlobalTheory.CuspGL.isPrimitive_extZero_of_sum_unipotent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumEqTorusSum
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteMonicNatDegree
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

private theorem torus_iff {F : Type} [Field F] [Finite F] (n : ℕ) (α : AlgebraicClosure F) (h0 : α ≠ 0) :
    α ^ (Nat.card F ^ n - 1) = 1 ↔ (minpoly F α).natDegree ∣ n := by
  have hi : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  rw [(minpoly.irreducible hi).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, minpoly.dvd_iff]
  have hq : 0 < Nat.card F ^ n := pow_pos Nat.card_pos _
  simp only [map_sub, map_pow, aeval_X, sub_eq_zero]
  obtain ⟨k, hk⟩ : ∃ k, Nat.card F ^ n = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hq).symm⟩
  rw [hk, Nat.add_sub_cancel, pow_succ]
  constructor
  · intro h; rw [h, one_mul]
  · intro h; exact mul_right_cancel₀ h0 (h.trans (one_mul α).symm)

private theorem finite_monic_natDegree {F : Type} [Field F] [Finite F] (n : ℕ) :
    {P : F[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0}.Finite := by
  have : Finite (Polynomial.degreeLT F (n + 1)) := Finite.of_equiv _ (degreeLTEquiv F (n + 1)).symm.toEquiv
  have h : (Polynomial.degreeLT F (n + 1) : Set F[X]).Finite := Set.toFinite _
  refine h.subset fun P hP => ?_
  simp only [SetLike.mem_coe, mem_degreeLT]
  exact (degree_le_of_natDegree_le hP.2.1.le).trans_lt (by exact_mod_cast Nat.lt_succ_self n)

private theorem finite_torus {F : Type} [Field F] [Finite F] (n : ℕ) (hn : 0 < n) :
    {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}.Finite := by
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  refine (Polynomial.nthRootsFinset (Nat.card F ^ n - 1) (1 : AlgebraicClosure F)).finite_toSet.subset
    fun α hα => ?_
  exact Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset (by omega) _).2 hα)

theorem sum_poly_eq_sum_torus : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (n : ℕ), 0 < n → ∀ (c : F[X] → ℂ) (l : ℕ), (∀ P : F[X], P.Monic → P.natDegree = n → (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) → c P = 0) → ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0}, c P * star (rootSum θ l P) = ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, ((n / (minpoly F α).natDegree : ℕ) : ℂ) * c (minpoly F α ^ (n / (minpoly F α).natDegree)) * star (θ α ^ l) := by
  intro F _ _ θ n hn c l hc
  classical
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  have hi : ∀ α : AlgebraicClosure F, IsIntegral F α := fun α => Algebra.IsIntegral.isIntegral α
  have hne : ∀ α : AlgebraicClosure F, α ^ (Nat.card F ^ n - 1) = 1 → α ≠ 0 := by
    rintro α h rfl
    rw [zero_pow (by omega)] at h
    exact zero_ne_one h
  rw [finsum_mem_eq_finite_toFinset_sum _ (finite_monic_natDegree n),
    finsum_mem_eq_finite_toFinset_sum _ (finite_torus n hn),
    ← Finset.sum_fiberwise_of_maps_to (s := (finite_torus (F := F) n hn).toFinset) (t := (finite_monic_natDegree (F := F) n).toFinset)
      (g := fun α => minpoly F α ^ (n / (minpoly F α).natDegree))]
  swap
  · intro α hα
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hα ⊢
    have hm := minpoly.monic (hi α)
    refine ⟨hm.pow _, ?_, ?_⟩
    · rw [hm.natDegree_pow, Nat.div_mul_cancel ((torus_iff n α (hne α hα)).1 hα)]
    · rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
      exact pow_ne_zero _ (minpoly.coeff_zero_ne_zero (hi α) (hne α hα))
  refine Finset.sum_congr rfl fun P hP => ?_
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
  obtain ⟨hP, hd, h0⟩ := hP
  by_cases hex : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m
  swap
  · rw [hc P hP hd hex, zero_mul]
    refine (Finset.sum_eq_zero fun α hα => ?_).symm
    rw [(Finset.mem_filter.1 hα).2, hc P hP hd hex, mul_zero, zero_mul]
  obtain ⟨f, m, hf, hirr, hm, rfl⟩ := hex
  rw [hf.natDegree_pow] at hd
  have hdiv : n / f.natDegree = m := by
    rw [← hd, Nat.mul_div_cancel _ hirr.natDegree_pos]
  have hmp : ∀ α : AlgebraicClosure F, aeval α f = 0 → minpoly F α = f := fun α h =>
    (minpoly.eq_of_irreducible_of_monic hirr h hf).symm
  have hfib : Finset.filter (fun α : AlgebraicClosure F => minpoly F α ^ (n / (minpoly F α).natDegree) = f ^ m)
      (finite_torus (F := F) n hn).toFinset = (f.map (algebraMap F (AlgebraicClosure F))).roots.toFinset := by
    ext α
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Multiset.mem_toFinset]
    rw [mem_roots (hf.map _).ne_zero, IsRoot.def, eval_map_algebraMap]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : n / (minpoly F α).natDegree ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd hn ((torus_iff n α (hne α h1)).1 h1)) (minpoly.natDegree_pos (hi α))).ne'
      have h4 := congrArg (aeval α) h2
      rw [map_pow, map_pow, minpoly.aeval, zero_pow h3] at h4
      exact pow_eq_zero_iff hm.ne' |>.1 h4.symm
    · intro h
      have hα : α ≠ 0 := by
        rintro rfl
        apply h0
        rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
        rw [aeval_def, eval₂_at_zero, map_eq_zero] at h
        rw [h, zero_pow hm.ne']
      rw [torus_iff n α hα, hmp α h, hdiv]
      exact ⟨Dvd.intro_left _ hd, rfl⟩
  have hsep : f.Separable := PerfectField.separable_of_irreducible hirr
  have hnd : (f.map (algebraMap F (AlgebraicClosure F))).roots.Nodup := nodup_roots hsep.map
  rw [hfib, rootSum, Polynomial.map_pow, roots_pow, Multiset.map_nsmul, Multiset.sum_nsmul,
    ← Multiset.dedup_eq_self.2 hnd, ← Multiset.toFinset_val, ← Finset.sum_eq_multiset_sum,
    Finset.val_toFinset, Finset.smul_sum, star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Multiset.mem_toFinset, mem_roots (hf.map _).ne_zero, IsRoot.def, eval_map_algebraMap] at hα
  rw [hmp α hα, hdiv, star_nsmul, nsmul_eq_mul]
  ring

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumEqTorusSum
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem ipGL_rootSum_eq_sum_torus : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ) (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V → ∀ l : ℕ, ipGL φ (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) = ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ Module.finrank F V - 1) = 1}, ((Module.finrank F V / (minpoly F α).natDegree : ℕ) : ℂ) * mass φ (minpoly F α ^ (Module.finrank F V / (minpoly F α).natDegree)) * star (θ α ^ l) := by
  intro F _ _ V _ _ _ θ φ hcl hprim hpos l
  rw [ipGL_charpoly_eq_finsum_mass F V φ (rootSum θ l)]
  refine sum_poly_eq_sum_torus F θ (Module.finrank F V) hpos (mass φ) l ?_

  intro P _ _ hP
  unfold mass
  rw [finsum_mem_def]
  refine finsum_eq_zero_of_forall_eq_zero fun g => ?_
  by_cases hg : LinearMap.charpoly g = P
  · rw [Set.indicator_of_mem (show g ∈ {g : Module.End F V | LinearMap.charpoly g = P} from hg)]
    exact GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow F V φ hcl hprim hpos g (hg ▸ hP)
  · exact Set.indicator_of_notMem (show g ∉ {g : Module.End F V | LinearMap.charpoly g = P} from hg) _

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumEqTorusSumStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_eq_torusSum : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ) (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V → ∀ l : ℕ, ipGL φ (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) = ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ Module.finrank F V - 1) = 1}, ((Module.finrank F V / (minpoly F α).natDegree : ℕ) : ℂ) * mass φ (minpoly F α ^ (Module.finrank F V / (minpoly F α).natDegree)) * star (θ α ^ l) := by
  first | exact @GlobalTheory.CuspGL.ipGL_rootSum_eq_sum_torus | exact GlobalTheory.CuspGL.ipGL_rootSum_eq_sum_torus | (intros; apply GlobalTheory.CuspGL.ipGL_rootSum_eq_sum_torus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharTraceMulIdempotent
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.isChar_trace_mul_idempotent :
    ∀ (L : Type) [Field L] (T : Type) [Group T] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L T V) (e : Module.End L V), e * e = e → (∀ t, ρ t * e = e * ρ t) → _root_.GlobalTheory.BI.IsChar L L (fun t => LinearMap.trace L V (ρ t * e)) := by
  intro L _ T _ V _ _ _ ρ e he hc
  have hfix : ∀ v ∈ LinearMap.range e, e v = v := by
    rintro _ ⟨w, rfl⟩
    rw [← Module.End.mul_apply, he]
  let W : Subrepresentation ρ :=
    ⟨LinearMap.range e, fun t v hv => by
      obtain ⟨w, rfl⟩ := hv
      exact ⟨ρ t w, by rw [← Module.End.mul_apply e, ← hc t, Module.End.mul_apply]⟩⟩
  have key := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep L L T _ W.toRepresentation).1
  convert key using 2 with t
  rw [Algebra.algebraMap_self, RingHom.id_apply, Representation.character,
    ← LinearMap.trace_restrict_eq_of_forall_mem (LinearMap.range e) (ρ t * e)
      (fun x => ⟨ρ t x, by rw [hc t]; rfl⟩)]
  congr 1
  ext ⟨v, hv⟩
  change (ρ t * e) v = ρ t v
  rw [Module.End.mul_apply, hfix v hv]

end GlobalTheory.BI
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumUnipotentRadicalEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumUnipotentRadicalEqZero
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem IsPrimitive.finsum_unipotentRadical_eq_zero (F : Type) [Field F] [Finite F] (d : ℕ)
    (φ : Module.End F (Fin d → F) → ℂ) (hφ : IsPrimitive φ) (a : ℕ) (ha : 0 < a) (had : a < d) :
    ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d,
      (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)},
      φ (Matrix.toLin' (u : Matrix (Fin d) (Fin d) F)) = 0 := by
  obtain ⟨A, H, hA, hH, hbij⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F d a had.le
  have hbot : A ≠ ⊥ := by
    rintro rfl
    rw [finrank_bot] at hA
    omega
  have htop : A ≠ ⊤ := by
    rintro rfl
    rw [finrank_top, Module.finrank_fin_fun] at hA
    omega
  rw [← hH, ← hφ A hbot htop 1 (fun x hx => hx)]
  refine finsum_mem_eq_of_bijOn _ hbij fun u _ => ?_
  simp only [add_sub_cancel]

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumUnipotentRadicalEqZeroStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_unipotent_radical_eq_zero_of_isPrimitive : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (φ : Module.End F (Fin d → F) → ℂ), IsPrimitive φ → ∀ a : ℕ, 0 < a → a < d → ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}, φ (Matrix.toLin' (u : Matrix (Fin d) (Fin d) F)) = 0 := by
  first | exact @GlobalTheory.CuspGL.IsPrimitive.finsum_unipotentRadical_eq_zero | exact GlobalTheory.CuspGL.IsPrimitive.finsum_unipotentRadical_eq_zero | (intros; apply GlobalTheory.CuspGL.IsPrimitive.finsum_unipotentRadical_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterEsymmRootsCharpoly
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

def compoundRep {G : Type} [Group G] {n : ℕ} (j : ℕ) (ρ : G →* GL (Fin n) ℂ) :
    Representation ℂ G (Set.powersetCard (Fin n) j → ℂ) where
  toFun g := Matrix.toLin' (GlobalTheory.compoundMatrix j (ρ g : Matrix (Fin n) (Fin n) ℂ))
  map_one' := by
    rw [map_one, Units.val_one, GlobalTheory.compoundMatrix_one, Matrix.toLin'_one]; rfl
  map_mul' a b := by
    rw [map_mul, Units.val_mul, GlobalTheory.compoundMatrix_mul, Matrix.toLin'_mul]; rfl

private lemma det_submatrix_subsetEnum_eq_det_submatrix_val {n j : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (S : Set.powersetCard (Fin n) j) :
    (A.submatrix (_root_.GlobalTheory.subsetEnum S) (_root_.GlobalTheory.subsetEnum S)).det =
      (A.submatrix (Subtype.val : {x // x ∈ S.1} → Fin n) Subtype.val).det := by
  have hmem : ∀ i, _root_.GlobalTheory.subsetEnum S i ∈ S.1 := fun i => by
    have : _root_.GlobalTheory.subsetEnum S i ∈ Set.range (_root_.GlobalTheory.subsetEnum S) :=
      ⟨i, rfl⟩
    rw [_root_.GlobalTheory.range_subsetEnum] at this
    exact_mod_cast this
  let σ : Fin j ≃ {x // x ∈ S.1} := Equiv.ofBijective
    (fun i => ⟨_root_.GlobalTheory.subsetEnum S i, hmem i⟩)
    ⟨fun a b hab => _root_.GlobalTheory.subsetEnum_injective S (congrArg Subtype.val hab),
      fun x => by
        have hx : x.1 ∈ ((S.1 : Finset (Fin n)) : Set (Fin n)) := x.2
        rw [← _root_.GlobalTheory.range_subsetEnum] at hx
        obtain ⟨i, hi⟩ := hx
        exact ⟨i, Subtype.ext hi⟩⟩
  have hsub : A.submatrix (_root_.GlobalTheory.subsetEnum S) (_root_.GlobalTheory.subsetEnum S) =
      (A.submatrix (Subtype.val : {x // x ∈ S.1} → Fin n) Subtype.val).submatrix σ σ := rfl
  rw [hsub, Matrix.det_submatrix_equiv_self]

private lemma trace_compoundMatrix_eq_sum_principal_minors {n : ℕ} (j : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (_root_.GlobalTheory.compoundMatrix j A).trace = ∑ s ∈ Finset.powersetCard j Finset.univ,
      (A.submatrix (Subtype.val : s → Fin n) Subtype.val).det := by
  rw [Finset.sum_subtype (p := fun s : Finset (Fin n) => s ∈ Set.powersetCard (Fin n) j) _
    (fun s => by simp [Finset.mem_powersetCard, Set.powersetCard])]
  unfold _root_.GlobalTheory.compoundMatrix
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
  exact Finset.sum_congr rfl fun S _ => det_submatrix_subsetEnum_eq_det_submatrix_val A S

private lemma esymm_roots_charpoly_eq_sum_principal_minors {n : ℕ} (j : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    M.charpoly.roots.esymm j = ∑ s ∈ Finset.powersetCard j Finset.univ,
      (M.submatrix (Subtype.val : s → Fin n) Subtype.val).det := by
  have hdeg : M.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hcard : M.charpoly.roots.card = M.charpoly.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits _)
  rcases le_or_gt j n with hj | hj
  · have h1 := coeff_eq_esymm_roots_of_card hcard (k := n - j) (by omega)
    have h2 := M.charpoly_coeff_eq_sum_minors j (by simp [hj])
    rw [hdeg, Nat.sub_sub_self hj, M.charpoly_monic.leadingCoeff, one_mul] at h1
    rw [Fintype.card_fin, h1] at h2
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) h2
  · rw [Finset.powersetCard_eq_empty.mpr (by simp [hj]), Finset.sum_empty, Multiset.esymm,
      Multiset.powersetCard_eq_empty _ (by omega)]
    simp

theorem _root_.GlobalTheory.BI.isChar_esymm_roots_charpoly :
    ∀ (G : Type) [Group G] (n j : ℕ) (ρ : G →* GL (Fin n) ℂ), _root_.GlobalTheory.BI.IsChar ℂ ℂ
      (fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots.esymm j) := by
  intro G _ n j ρ
  have h := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G _ (_root_.GlobalTheory.BI.compoundRep j ρ)).1
  have heq : (fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots.esymm j) =
      fun g => algebraMap ℂ ℂ ((_root_.GlobalTheory.BI.compoundRep j ρ).character g) := by
    funext g
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    change _ = LinearMap.trace ℂ _
      (Matrix.toLin' (_root_.GlobalTheory.compoundMatrix j (ρ g : Matrix (Fin n) (Fin n) ℂ)))
    rw [Matrix.trace_toLin'_eq, trace_compoundMatrix_eq_sum_principal_minors, esymm_roots_charpoly_eq_sum_principal_minors]
  rw [heq]
  exact h

end GlobalTheory.BI
end
end
