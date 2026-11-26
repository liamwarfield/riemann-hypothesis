module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetAverageProdFundamentalDomainPlaneLatticePow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfProdFunEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.Radical

section
variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

def Uni (b : ι → ℕ) (M : Matrix ι ι k) : Prop :=
  ∀ r s, b s ≤ b r → M r s = (1 : Matrix ι ι k) r s

omit [Fintype ι] in
theorem Uni.blockTri {b : ι → ℕ} {M : Matrix ι ι k} (h : Uni b M) : M.BlockTriangular b := by
  intro r s hrs
  rw [h r s hrs.le, Matrix.one_apply_ne]
  rintro rfl
  exact lt_irrefl _ hrs

theorem Uni.mul {b : ι → ℕ} {M M' : Matrix ι ι k} (h : Uni b M) (h' : Uni b M') :
    Uni b (M * M') := by
  intro r s hrs
  have : (M * M') r s = ((1 : Matrix ι ι k) * M') r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (b t) (b r) with ht | ht
    · rw [h r t ht]
    · rw [h'.blockTri (show b s < b t from lt_of_le_of_lt hrs ht), mul_zero, mul_zero]
  rw [this, Matrix.one_mul, h' r s hrs]

theorem Uni.det {b : ι → ℕ} {M : Matrix ι ι k} (h : Uni b M) : M.det = 1 := by
  rw [h.blockTri.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock b a = 1 := by
    ext ⟨r, hr⟩ ⟨s, hs⟩
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    rw [h r s (by rw [hr, hs])]
    simp [Matrix.one_apply]
  rw [this, Matrix.det_one]

theorem Uni.inv {b : ι → ℕ} {g : GL ι k} (h : Uni b g.val) : Uni b (g⁻¹).val := by
  have hb : (g⁻¹).val.BlockTriangular b := by
    letI : Invertible g.val := g.invertible
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular h.blockTri
  intro r s hrs
  have : ((g⁻¹).val * g.val) r s = ((g⁻¹).val * (1 : Matrix ι ι k)) r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (b s) (b t) with ht | ht
    · rw [h t s ht]
    · rw [hb (show b t < b r from lt_of_lt_of_le ht hrs), zero_mul, zero_mul]
  rw [Matrix.mul_one, Units.inv_mul] at this
  exact this.symm

theorem Uni.mul_apply_succ {b : ι → ℕ} {M M' : Matrix ι ι k} (h : Uni b M) (h' : Uni b M')
    {r s : ι} (hrs : b s = b r + 1) : (M * M') r s = M r s + M' r s := by
  have e : (M * M') r s = (M * (1 : Matrix ι ι k)) r s + ((1 : Matrix ι ι k) * M') r s := by
    simp only [Matrix.mul_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (b t) (b r) with ht | ht
    · have hts : t ≠ s := by
        rintro rfl
        omega
      rw [h r t ht, Matrix.one_apply_ne hts, mul_zero, zero_add]
    · have hrt : r ≠ t := by
        rintro rfl
        omega
      rw [h' t s (by omega), Matrix.one_apply_ne hrt, zero_mul, add_zero]
  rw [e, Matrix.mul_one, Matrix.one_mul]

end

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem mem_N_iff (g : GL (n ⊕ Fin c) k) : g ∈ N k n c p ↔ InN p g := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => intro r s _; rfl
    | mul x y _ _ hx hy => exact Uni.mul (b := lev p) hx hy
    | inv x _ hx => exact Uni.inv (b := lev p) hx
  · intro hg
    exact Subgroup.subset_closure hg

theorem simpleSum_mul {g h : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) (hh : h ∈ N k n c p) :
    simpleSum (g * h) = simpleSum g + simpleSum h := by
  rw [mem_N_iff] at hg hh
  simp only [simpleSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · exact Uni.mul_apply_succ (b := lev p) hg hh (by simp [lev, hij])
  · simp

theorem embX_val (x : GL n k) : (embX c x).val = fromBlocks x.val 0 0 1 := rfl

theorem toBlocks₁₁_of_mem {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) :
    g.val.toBlocks₁₁ = 1 := by
  rw [mem_N_iff] at hg
  ext r s
  simp only [Matrix.toBlocks₁₁, Matrix.of_apply]
  rw [hg _ _ (by simp [lev])]
  simp [Matrix.one_apply]

theorem conj_val (x : GL n k) (g : GL (n ⊕ Fin c) k) :
    (embX c x * g * (embX c x)⁻¹).val =
      fromBlocks (x.val * g.val.toBlocks₁₁ * (x⁻¹).val) (x.val * g.val.toBlocks₁₂)
        (g.val.toBlocks₂₁ * (x⁻¹).val) g.val.toBlocks₂₂ := by
  rw [← map_inv, Units.val_mul, Units.val_mul, embX_val, embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks g.val]
  simp only [fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.one_mul, Matrix.mul_one]

theorem conj_mem (x : GL n k) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) :
    embX c x * g * (embX c x)⁻¹ ∈ N k n c p := by
  have h11 := toBlocks₁₁_of_mem hg
  rw [mem_N_iff] at hg ⊢
  intro r s hrs
  rw [conj_val, h11, Matrix.mul_one, Units.mul_inv]
  rcases r with r | r <;> rcases s with s | s
  · simp [Matrix.one_apply]
  · rw [fromBlocks_apply₁₂, Matrix.mul_apply, Matrix.one_apply_ne (by simp)]
    refine Finset.sum_eq_zero fun t _ => ?_
    have := hg (Sum.inl t) (Sum.inr s) hrs
    rw [Matrix.one_apply_ne (by simp)] at this
    simp [Matrix.toBlocks₁₂, this]
  · rw [fromBlocks_apply₂₁, Matrix.mul_apply, Matrix.one_apply_ne (by simp)]
    refine Finset.sum_eq_zero fun t _ => ?_
    have := hg (Sum.inr r) (Sum.inl t) hrs
    rw [Matrix.one_apply_ne (by simp)] at this
    simp [Matrix.toBlocks₂₁, this]
  · rw [fromBlocks_apply₂₂]
    exact hg _ _ hrs

theorem simpleSum_conj (x : GL n k) (g : GL (n ⊕ Fin c) k) :
    simpleSum (embX c x * g * (embX c x)⁻¹) = simpleSum g := by
  simp only [simpleSum, conj_val, fromBlocks_apply₂₂]
  rfl

theorem exists_of_mem_R {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c p) :
    ∃ x : GL n k, ∃ g ∈ N k n c p, r = embX c x * g := by
  let S : Subgroup (GL (n ⊕ Fin c) k) :=
    { carrier := {r | ∃ x : GL n k, ∃ g ∈ N k n c p, r = embX c x * g}
      one_mem' := ⟨1, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨x, g, hg, rfl⟩ ⟨y, h, hh, rfl⟩
        refine ⟨x * y, _, mul_mem (conj_mem y⁻¹ hg) hh, ?_⟩
        rw [map_mul, map_inv]
        group
      inv_mem' := by
        rintro _ ⟨x, g, hg, rfl⟩
        refine ⟨x⁻¹, _, conj_mem x (inv_mem hg), ?_⟩
        rw [map_inv]
        group }
  have : R k n c p ≤ S := by
    refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨x, 1, one_mem _, (mul_one _).symm⟩
    · intro g hg
      exact ⟨1, g, hg, by simp⟩
  exact this hr

theorem toBlocks₁₁_embX_mul (x : GL n k) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) :
    (embX c x * g).val.toBlocks₁₁ = x.val := by
  rw [Units.val_mul, embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks g.val]
  simp [fromBlocks_multiply, toBlocks₁₁_of_mem hg]

theorem existsUnique_of_mem_R {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c p) :
    ∃! xg : GL n k × N k n c p, r = embX c xg.1 * (xg.2 : GL (n ⊕ Fin c) k) := by
  obtain ⟨x, g, hg, rfl⟩ := exists_of_mem_R hr
  refine ⟨(x, ⟨g, hg⟩), rfl, ?_⟩
  rintro ⟨y, h, hh⟩ e
  have hxy : y = x := by
    apply Units.ext
    rw [← toBlocks₁₁_embX_mul x hg, ← toBlocks₁₁_embX_mul y hh]
    exact congrArg (fun u : GL (n ⊕ Fin c) k => u.val.toBlocks₁₁) e.symm
  subst hxy
  have : g = h := mul_left_cancel e
  subst this
  rfl

theorem simpleSum_eq_zero {g : GL (n ⊕ Fin c) k}
    (h : ∀ i j, g.val (Sum.inr i) (Sum.inr j) = (1 : Matrix (Fin c) (Fin c) k) i j) :
    simpleSum g = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with hij
  · rw [h, Matrix.one_apply_ne]
    rintro rfl
    omega
  · rfl

theorem rowE_mem {l : ℕ} (u : n → k) (hl : l < p) : rowE c l u ∈ N k n c p := by
  rw [mem_N_iff]
  intro r s hrs
  rcases r with r | r <;> rcases s with s | s
  · simp [rowE, lowU, Matrix.one_apply]
  · simp [rowE, lowU]
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    have : ¬ (r.val + 1 = l) := by omega
    simp [rowE, lowU, this]
  · simp [rowE, lowU, Matrix.one_apply]

theorem colE_mem {i : ℕ} (β : n → k) (hi : p < i) : colE c i β ∈ N k n c p := by
  rw [mem_N_iff]
  intro r s hrs
  rcases r with r | r <;> rcases s with s | s
  · simp [colE, upU, Matrix.one_apply]
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    have : ¬ (s.val + 1 = i) := by omega
    simp [colE, upU, this]
  · simp [colE, upU]
  · simp [colE, upU, Matrix.one_apply]

theorem unipotent_radical_basic : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), (∀ g : GL (n ⊕ Fin c) k, g ∈ N k n c p ↔ InN p g) ∧ (∀ g ∈ N k n c p, ∀ h ∈ N k n c p, simpleSum (g * h) = simpleSum g + simpleSum h) ∧ (∀ g ∈ N k n c p, Matrix.GeneralLinearGroup.det g = 1) ∧ (∀ (x : GL n k), ∀ g ∈ N k n c p, embX c x * g * (embX c x)⁻¹ ∈ N k n c p ∧ simpleSum (embX c x * g * (embX c x)⁻¹) = simpleSum g) ∧ (∀ r ∈ R k n c p, ∃! xg : GL n k × N k n c p, r = embX c xg.1 * (xg.2 : GL (n ⊕ Fin c) k)) ∧ (∀ (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k), (∀ r s, lev p s ≤ lev p r → M r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) → M.det = 1) ∧ (∀ (l : ℕ) (u : n → k), l < p → rowE c l u ∈ N k n c p ∧ simpleSum (rowE c l u) = 0) ∧ ∀ (i : ℕ) (β : n → k), p < i → colE c i β ∈ N k n c p ∧ simpleSum (colE c i β) = 0 := by
  intro k _ n _ _ c p
  refine ⟨mem_N_iff, fun g hg h hh => simpleSum_mul hg hh, fun g hg => ?_,
    fun x g hg => ⟨conj_mem x hg, simpleSum_conj x g⟩, fun r hr => existsUnique_of_mem_R hr,
    fun M hM => Uni.det (b := lev p) hM,
    fun l u hl => ⟨rowE_mem u hl, simpleSum_eq_zero fun _ _ => rfl⟩,
    fun i β hi => ⟨colE_mem β hi, simpleSum_eq_zero fun _ _ => rfl⟩⟩
  apply Units.ext
  exact Uni.det (b := lev p) ((mem_N_iff g).1 hg)

end GlobalTheory.RootEx.Radical
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

namespace GlobalTheory.SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in
theorem one_lt_resCard : 1 < resCard k := Finite.one_lt_card

theorem nabs_le_of_valuation_le {x y : kˣ} (h : valuation k (x : k) ≤ valuation k (y : k)) :
    nabs k x ≤ nabs k y := by
  borelize k
  obtain ⟨ν, hν, h1⟩ := exists_isUnitVol k
  have hx := measureReal_cball ν x
  have hy := measureReal_cball ν y
  have h2 : ν.real (𝒪[k] : Set k) = 1 := by rw [Measure.real, h1]; simp
  rw [h2, mul_one] at hx hy
  rw [← hx, ← hy]
  have h3 : cball x ⊆ cball y := fun z hz => le_trans (show valuation k z ≤ _ from hz) h
  exact measureReal_mono h3 (isCompact_cball y).measure_lt_top.ne

theorem nabs_lt_of_valuation_lt {x y : kˣ} (h : valuation k (x : k) < valuation k (y : k)) :
    nabs k x < nabs k y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  have hy0 : 0 < valuation k (y : k) := by simp [zero_lt_iff]
  have hlt : valuation k ((x : k) * (y : k)⁻¹) < 1 := by
    rw [map_mul, map_inv₀, mul_inv_lt_iff₀ hy0, one_mul]; exact h
  let z : 𝒪[k] := ⟨(x : k) * (y : k)⁻¹, (Valuation.mem_integer_iff _ _).mpr hlt.le⟩
  have hz : z ∈ 𝓂[k] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hlt
  have h1 : valuation k ((x : k) * (y : k)⁻¹) ≤ valuation k (ϖ : k) :=
    (mem_cball_uniformiser hϖ (x := Units.mk0 _ h0) rfl z).mpr hz
  have h2 : valuation k (x : k) ≤ valuation k ((Units.mk0 _ h0 * y : kˣ) : k) := by
    rw [map_mul, map_inv₀, mul_inv_le_iff₀ hy0] at h1
    rw [Units.val_mul, map_mul]
    exact h1
  have h3 := nabs_le_of_valuation_le h2
  rw [nabs_mul, nabs_uniformiser hϖ (x := Units.mk0 _ h0) rfl] at h3
  refine h3.trans_lt (mul_lt_of_lt_one_left (nabs_pos k y) (inv_lt_one_of_one_lt₀ ?_))
  exact_mod_cast one_lt_resCard k

theorem nabs_le_iff (x y : kˣ) : nabs k x ≤ nabs k y ↔ valuation k (x : k) ≤ valuation k (y : k) :=
  ⟨fun h => not_lt.mp fun h' => absurd h (not_le.mpr (nabs_lt_of_valuation_lt h')),
    nabs_le_of_valuation_le⟩

theorem nabs_eq_iff (x y : kˣ) : nabs k x = nabs k y ↔ valuation k (x : k) = valuation k (y : k) := by
  rw [le_antisymm_iff, le_antisymm_iff, nabs_le_iff, nabs_le_iff]

theorem nabs_eq_one_iff (x : kˣ) : nabs k x = 1 ↔ valuation k (x : k) = 1 := by
  rw [← nabs_one k, nabs_eq_iff, Units.val_one, map_one]

variable (k) in
theorem isLocallyConstant_nabs : IsLocallyConstant (nabs k) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  have h1 : (fun z : kˣ => (z : k) - x) ⁻¹' cball (Units.mk0 r hr0 * x) ∈ 𝓝 x :=
    ((isOpen_cball _).preimage (Units.continuous_val.sub continuous_const)).mem_nhds (by simp [cball])
  filter_upwards [h1] with z hz
  rw [nabs_eq_iff]
  have h2 : valuation k ((z : k) - x) ≤ valuation k (r * x) := hz
  refine Valuation.map_eq_of_sub_lt _ (h2.trans_lt ?_)
  rw [map_mul]
  exact mul_lt_of_lt_one_left (by simp [zero_lt_iff]) hr1

theorem nabs_properties : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ x y : kˣ, nabs k (x * y) = nabs k x * nabs k y) ∧ (∀ x : kˣ, 0 < nabs k x) ∧ (∀ x y : kˣ, nabs k x ≤ nabs k y ↔ valuation k (x : k) ≤ valuation k (y : k)) ∧ (∀ x : kˣ, nabs k x = 1 ↔ valuation k (x : k) = 1) ∧ (∀ (ϖ : 𝒪[k]) (x : kˣ), Irreducible ϖ → (x : k) = (ϖ : k) → nabs k x = (resCard k : ℝ)⁻¹) ∧ IsLocallyConstant (nabs k) ∧ 1 < resCard k :=
  fun k _ _ _ _ => ⟨nabs_mul k, nabs_pos k, nabs_le_iff, nabs_eq_one_iff,
    fun _ _ h h' => nabs_uniformiser h h', isLocallyConstant_nabs k, one_lt_resCard k⟩

end GlobalTheory.SplitWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_cball_addChar_eq_one (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ s : kˣ, ∀ y ∈ cball s, ψ y = 1 := by
  have hU : ψ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (0 : k) := by
    refine ((Circle.isOpen_centeredArc _).preimage hψ).mem_nhds ?_
    rw [Set.mem_preimage, AddChar.map_zero_eq_one]
    exact ⟨0, by simpa using Real.pi_pos, by simp⟩
  obtain ⟨s, hs⟩ := exists_cball_subset hU
  refine ⟨s, fun y hy => Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ => ?_⟩
  rw [← AddChar.map_nsmul_eq_pow]
  refine hs ?_
  clear * - hy
  induction n with
  | zero => simp [cball]
  | succ n ih => rw [succ_nsmul]; exact add_mem_cball ih hy

theorem exists_hasConductor_of_continuous (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1) :
    ∃ c : kˣ, HasConductor ψ c := by
  classical
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  obtain ⟨y₀, hy₀⟩ : ∃ y, ψ y ≠ 1 := by
    by_contra h
    push Not at h
    exact h1 (by ext y; simp [h y])
  have hy0 : y₀ ≠ 0 := by
    rintro rfl
    exact hy₀ (AddChar.map_zero_eq_one ψ)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  have hlt : ∀ y : 𝒪[k], y ∈ 𝓂[k] ↔ valuation k (y : k) < 1 := fun y => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
  have hϖ1 : valuation k (ϖ : k) < 1 := (hlt ϖ).mp hϖ.not_isUnit
  have hex : ∃ n : ℕ, ∀ y, valuation k y ≤ valuation k (y₀ * (ϖ : k) ^ n) → ψ y = 1 := by
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ1
      (Units.mk0 (valuation k (y₀⁻¹ * s)) (by simp [hy0]))
    refine ⟨n, fun y hy => hs y (show valuation k y ≤ valuation k (s : k) from hy.trans ?_)⟩
    rw [Units.val_mk0, map_mul, map_inv₀, lt_inv_mul_iff₀ (by simp [zero_lt_iff, hy0])] at hn
    rw [map_mul, map_pow]
    exact hn.le
  have hspec := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hspec
    exact hy₀ (hspec y₀ (by simp))
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hmin := Nat.find_min hex (m := m) (by omega)
  rw [hm] at hspec
  refine ⟨Units.mk0 (y₀ * (ϖ : k) ^ (m + 1)) (mul_ne_zero hy0 (pow_ne_zero _ h0)), fun x => ⟨fun h => ?_,
    fun h y hy => hspec y (hy.trans h)⟩⟩
  by_contra hx
  rw [Units.val_mk0, not_le] at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hxp : 0 < valuation k x := by simp [zero_lt_iff, hx0]
  have hxi : valuation k (x⁻¹ * (y₀ * (ϖ : k) ^ (m + 1))) < 1 := by
    rw [map_mul, map_inv₀, inv_mul_lt_iff₀ hxp, mul_one]
    exact hx
  have h2 : valuation k (x⁻¹ * (y₀ * (ϖ : k) ^ (m + 1))) ≤ valuation k (ϖ : k) :=
    (mem_cball_uniformiser hϖ (x := Units.mk0 _ h0) rfl
      ⟨_, (Valuation.mem_integer_iff _ _).mpr hxi.le⟩).mpr ((hlt _).mpr hxi)
  rw [map_mul, map_inv₀, inv_mul_le_iff₀ hxp, pow_succ, ← mul_assoc, map_mul,
    mul_le_mul_iff_left₀ (by simp [zero_lt_iff, h0])] at h2
  exact hmin fun y hy => h y (hy.trans h2)

theorem conductor_exists :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [MeasurableSpace k] [BorelSpace k],
      (∀ ψ : AddChar k Circle, Continuous ψ → ψ ≠ 1 → ∃ c : kˣ, HasConductor ψ c) ∧
      (∃ ψ : AddChar k Circle, Continuous ψ ∧ ψ ≠ 1 ∧ HasConductor ψ 1) ∧
      ∃ ν : Measure k, IsUnitVol ν := by
  intro k _ _ _ _ _ _
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar k Circle, HasConductor ψ 1 := exists_hasConductor_one k
  exact ⟨exists_hasConductor_of_continuous, ⟨ψ, hψ.continuous, hψ.ne_one, hψ⟩, exists_isUnitVol k⟩

end GlobalTheory.SplitWeil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

namespace GlobalTheory.SplitWeil

section
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem om_smul_add (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) (z : ℂ) (Φ Ψ : Matrix b a k → ℂ) :
    om μ g h (z • Φ + Ψ) = z • om μ g h Φ + om μ g h Ψ := by
  funext x
  simp only [om, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem eventually_comp_sideMul_eq {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB (Matrix b a k)) :
    ∀ᶠ gh : GL a k × GL b k in 𝓝 1, ∀ x, Φ (sideMul gh.1 gh.2 x) = Φ x := by
  have hc : Continuous fun q : (GL a k × GL b k) × Matrix b a k => sideMul q.1.1 q.1.2 q.2 := by
    show Continuous fun q : (GL a k × GL b k) × Matrix b a k =>
      (q.1.2⁻¹ : GL b k).val * q.2 * q.1.1.val
    exact ((Units.continuous_coe_inv.comp (continuous_snd.comp continuous_fst)).matrix_mul
      continuous_snd).matrix_mul (Units.continuous_val.comp (continuous_fst.comp continuous_fst))
  have h1 : ∀ᶠ gh : GL a k × GL b k in 𝓝 1, ∀ x ∈ tsupport Φ, Φ (sideMul gh.1 gh.2 x) = Φ x := by
    refine IsCompact.eventually_forall_of_forall_eventually hΦ.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : (GL a k × GL b k) × Matrix b a k =>
        (Φ (sideMul q.1.1 q.1.2 q.2), Φ q.2) :=
      (hΦ.1.comp_continuous hc).prodMk (hΦ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (1, x)] with q hq
    simp only [Prod.mk.injEq] at hq
    rw [hq.1, hq.2]
    congr 1
    show ((1 : GL b k)⁻¹ : GL b k).val * x * (1 : GL a k).val = x
    simp
  have h2 : ∀ᶠ gh : GL a k × GL b k in 𝓝 1,
      ∀ x ∈ tsupport Φ, Φ (sideMul gh⁻¹.1 gh⁻¹.2 x) = Φ x := by
    have ht : Filter.Tendsto (fun gh : GL a k × GL b k => gh⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv (G := GL a k × GL b k)).tendsto 1
    exact ht.eventually h1
  filter_upwards [h1, h2] with gh hs hs' x
  by_cases hx : x ∈ tsupport Φ
  · exact hs x hx
  by_cases hx' : sideMul gh.1 gh.2 x ∈ tsupport Φ
  · rw [← hs' _ hx']
    congr 1
    have := (sideMul gh.1 gh.2).left_inv x
    refine Eq.trans ?_ this
    show (gh.2⁻¹⁻¹ : GL b k).val * sideMul gh.1 gh.2 x * (gh.1⁻¹ : GL a k).val = _
    rw [inv_inv]
    rfl
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem isOpen_valuation_eq_one : IsOpen {x : kˣ | valuation k (x : k) = 1} := by
  have : {x : kˣ | valuation k (x : k) = 1} =
      (fun x : kˣ => (x : k)) ⁻¹' (𝒪[k] : Set k) ∩ (fun x : kˣ => ((x⁻¹ : kˣ) : k)) ⁻¹' (𝒪[k] : Set k) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe,
      Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀]
    rw [inv_le_one₀ (by simp [zero_lt_iff])]
    exact le_antisymm_iff
  rw [this]
  exact ((isOpen_int k).preimage Units.continuous_val).inter
    ((isOpen_int k).preimage Units.continuous_coe_inv)

theorem eventually_det_trivial (n : Type*) [Fintype n] [DecidableEq n] {μ : kˣ →* ℂˣ}
    (hμ : IsOpen (μ.ker : Set kˣ)) :
    ∀ᶠ g : GL n k in 𝓝 1, μ (Matrix.GeneralLinearGroup.det g) = 1 ∧
      nabs k (Matrix.GeneralLinearGroup.det g) = 1 := by
  have hU := (hμ.inter isOpen_valuation_eq_one).preimage
    (Matrix.GeneralLinearGroup.continuous_det (n := n) (R := k))
  filter_upwards [hU.mem_nhds (x := 1) (by simp)] with g hg
  exact ⟨hg.1, nabs_eq_one_of_valuation_eq_one hg.2⟩

theorem isOpen_stabilizer_om {μ : kˣ →* ℂˣ} (hμ : IsOpen (μ.ker : Set kˣ)) {Φ : Matrix b a k → ℂ}
    (hΦ : Φ ∈ SB (Matrix b a k)) : IsOpen {gh : GL a k × GL b k | om μ gh.1 gh.2 Φ = Φ} := by
  let S : Subgroup (GL a k × GL b k) :=
    { carrier := {gh | om μ gh.1 gh.2 Φ = Φ}
      one_mem' := om_one μ Φ
      mul_mem' := fun {x y} hx hy => by
        show om μ (x.1 * y.1) (x.2 * y.2) Φ = Φ
        rw [om_mul, hy, hx]
      inv_mem' := fun {x} hx => by
        show om μ x.1⁻¹ x.2⁻¹ Φ = Φ
        conv_lhs => rw [← hx]
        rw [← om_mul, inv_mul_cancel, inv_mul_cancel, om_one] }
  refine S.isOpen_of_mem_nhds (g := 1) ?_
  have h1 := (continuous_fst.tendsto (1 : GL a k × GL b k)).eventually (eventually_det_trivial a hμ)
  have h2 := (continuous_snd.tendsto (1 : GL a k × GL b k)).eventually (eventually_det_trivial b hμ)
  filter_upwards [h1, h2, eventually_comp_sideMul_eq hΦ] with gh hg hh hs
  show om μ gh.1 gh.2 Φ = Φ
  funext x
  have := hs x
  simp only [om, hg.1, hg.2, hh.1, hh.2, Real.one_rpow, inv_one, Units.val_one, Complex.ofReal_one,
    one_mul]
  exact this

end

theorem om_isSmoothRepresentation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)), (∀ Φ : Matrix b a k → ℂ, om μ 1 1 Φ = Φ) ∧ (∀ (g g' : GL a k) (h h' : GL b k) (Φ : Matrix b a k → ℂ), om μ (g * g') (h * h') Φ = om μ g h (om μ g' h' Φ)) ∧ (∀ (g : GL a k) (h : GL b k) (z : ℂ) (Φ Ψ : Matrix b a k → ℂ), om μ g h (z • Φ + Ψ) = z • om μ g h Φ + om μ g h Ψ) ∧ (∀ (g : GL a k) (h : GL b k), ∀ Φ ∈ SB (Matrix b a k), om μ g h Φ ∈ SB (Matrix b a k)) ∧ ∀ Φ ∈ SB (Matrix b a k), IsOpen {gh : GL a k × GL b k | om μ gh.1 gh.2 Φ = Φ} :=
  fun _ _ _ _ _ _ _ _ _ _ _ μ hμ =>
    ⟨om_one μ, om_mul μ, om_smul_add μ, fun g h _ hΦ => om_mem_SB μ g h hΦ,
      fun _ hΦ => isOpen_stabilizer_om hμ hΦ⟩

end GlobalTheory.SplitWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

namespace GlobalTheory.RootEx

open scoped Topology Pointwise in
theorem _root_.GlobalTheory.RootEx.exists_isOpen_addSubgroup_add_eq {X : Type*}
    [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] {Φ : X → ℂ} (hlc : IsLocallyConstant Φ) (hcs : IsCompact (tsupport Φ)) :
    ∃ Λ : AddSubgroup X, IsOpen (Λ : Set X) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  classical
  obtain ⟨t, ht⟩ := hcs.elim_finite_subcover (fun c : ℂ => {x | Φ x = c})
    (fun c => hlc.isOpen_fiber c) (fun x _ => Set.mem_iUnion.2 ⟨Φ x, rfl⟩)
  have hV : ∀ c : ℂ, ∃ V ∈ 𝓝 (0 : X), c ≠ 0 → {x | Φ x = c} + V ⊆ {x | Φ x = c} := by
    intro c
    by_cases hc : c = 0
    · exact ⟨Set.univ, Filter.univ_mem, fun h => (h hc).elim⟩
    · have hsub : {x | Φ x = c} ⊆ tsupport Φ := fun x hx =>
        subset_tsupport Φ (by
          rw [Function.mem_support]
          rw [Set.mem_setOf_eq] at hx
          rw [hx]
          exact hc)
      obtain ⟨V, hV0, hVs⟩ := compact_open_separated_add_right
        (hcs.of_isClosed_subset (hlc.isClosed_fiber c) hsub) (hlc.isOpen_fiber c) le_rfl
      exact ⟨V, hV0, fun _ => hVs⟩
  choose V hV0 hVsub using hV
  have hW : (⋂ c ∈ t, (V c ∩ -V c)) ∈ 𝓝 (0 : X) :=
    (Filter.biInter_finset_mem t).2 fun c _ =>
      Filter.inter_mem (hV0 c) (neg_mem_nhds_zero X (hV0 c))
  have hstep : ∀ x, ∀ v ∈ (⋂ c ∈ t, (V c ∩ -V c)), Φ (x + v) = Φ x := by
    intro x v hv
    have hv' : ∀ c ∈ t, v ∈ V c ∧ -v ∈ V c := by
      intro c hc
      have h := Set.mem_iInter₂.1 hv c hc
      exact ⟨h.1, Set.mem_neg.1 h.2⟩
    by_cases h0 : Φ x = 0
    · by_contra hne
      have hne' : Φ (x + v) ≠ 0 := by rwa [h0] at hne
      have hxK : x + v ∈ tsupport Φ := subset_tsupport Φ hne'
      obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hxK)
      have hc' : Φ (x + v) = c := hc
      have hc0 : c ≠ 0 := hc' ▸ hne'
      have h := hVsub c hc0 (Set.add_mem_add hc (hv' c hct).2)
      have h' : Φ (x + v + -v) = c := h
      rw [add_neg_cancel_right] at h'
      exact hc0 (h'.symm.trans h0)
    · have hxK : x ∈ tsupport Φ := subset_tsupport Φ h0
      obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hxK)
      have hc' : Φ x = c := hc
      have hc0 : c ≠ 0 := hc' ▸ h0
      have h := hVsub c hc0 (Set.add_mem_add hc (hv' c hct).1)
      have h' : Φ (x + v) = c := h
      exact h'.trans hc'.symm
  refine ⟨AddSubgroup.closure (⋂ c ∈ t, (V c ∩ -V c)),
    AddSubgroup.isOpen_of_mem_nhds _ (g := 0)
      (Filter.mem_of_superset hW AddSubgroup.subset_closure), ?_⟩
  intro x y hy
  induction hy using AddSubgroup.closure_induction generalizing x with
  | mem y hy => exact hstep x y hy
  | zero => simp
  | add y z _ _ hy hz => rw [← add_assoc, hz, hy]
  | neg y _ hy =>
    have h := hy (x + -y)
    rw [neg_add_cancel_right] at h
    exact h.symm

open scoped Topology Pointwise in
theorem _root_.GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (a b : Type) [Fintype a] [Fintype b], ∀ Φ ∈ _root_.GlobalTheory.SplitWeil.SB (Matrix a b k),
      ∃ Λ : AddSubgroup (Matrix a b k), IsOpen (Λ : Set (Matrix a b k)) ∧
        ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  intro k _ _ _ _ a b _ _ Φ hΦ
  obtain ⟨hlc, hcs⟩ := hΦ
  exact _root_.GlobalTheory.RootEx.exists_isOpen_addSubgroup_add_eq hlc hcs

end GlobalTheory.RootEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatMatrixExistsOpenAddSubgroupInvariaStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_matrix_exists_open_addSubgroup_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a] [Fintype b], ∀ Φ ∈ SB (Matrix a b k), ∃ Λ : AddSubgroup (Matrix a b k), IsOpen (Λ : Set (Matrix a b k)) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  first | exact @GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup | exact GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup | (intros; apply GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingAffPtUncurry
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology

noncomputable section
namespace GlobalTheory.RootEx

theorem integral_mul_mem_SB {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [R1Space X]
    [MeasurableSpace E] (μ : Measure E) (G : X × E → ℂ) (hG : G ∈ SB (X × E)) (χ : E → ℂ) :
    (fun x => ∫ e, G (x, e) * χ e ∂μ) ∈ SB X := by
  obtain ⟨h1, h2⟩ := hG
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x₀
    have hK : IsCompact (Prod.snd '' tsupport G) := h2.isCompact.image continuous_snd
    have h := hK.eventually_forall_of_forall_eventually (x₀ := x₀)
      (P := fun x y => G (x, y) = G (x₀, y)) (by
        intro y _
        have ha := h1.eventually_eq (x₀, y)
        have hc : Continuous fun z : X × E => ((x₀, z.2) : X × E) := by fun_prop
        have hb := (h1.comp_continuous hc).eventually_eq (x₀, y)
        filter_upwards [ha, hb] with z hz hz'
        exact hz.trans hz'.symm)
    filter_upwards [h] with x hx
    congr 1
    funext e
    by_cases he : e ∈ Prod.snd '' tsupport G
    · rw [hx e he]
    · have : ∀ x', G (x', e) = 0 := fun x' =>
        image_eq_zero_of_notMem_tsupport fun h' => he ⟨_, h', rfl⟩
      rw [this, this]
  · refine HasCompactSupport.intro (h2.isCompact.image continuous_fst) fun x hx => ?_
    have : ∀ e, G (x, e) = 0 := fun e =>
      image_eq_zero_of_notMem_tsupport fun h' => hx ⟨_, h', rfl⟩
    simp [this]

section
variable {k : Type*} [Field k] {n n' : Type*} {c : ℕ}

theorem affPt_of_free (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}) :
    affPt p x₀ e rs.1.1 rs.1.2 = basePt c (0 : Matrix n n' k) rs.1.1 rs.1.2 + e rs := by
  obtain ⟨⟨r, s⟩, h⟩ := rs
  simp only [affPt, Matrix.add_apply, Matrix.of_apply, dif_pos h]
  congr 1
  rcases r with r | r <;> rcases s with s | s
  · exact h.elim
  all_goals rfl

theorem affPt_inl_inl (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) (r : n) (s : n') :
    affPt p x₀ e (Sum.inl r) (Sum.inl s) = x₀ r s := by
  simp [affPt, basePt, Free]

variable [TopologicalSpace k] [IsTopologicalRing k]

theorem continuous_affPt_uncurry (p : ℕ) :
    Continuous fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
      affPt p z.1 z.2 := by
  refine continuous_matrix fun r s => ?_
  by_cases h : Free p (r, s)
  · have := fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
      affPt_of_free p z.1 z.2 ⟨(r, s), h⟩
    simp only at this
    simp only [this]
    fun_prop
  · simp only [affPt, Matrix.add_apply, Matrix.of_apply, dif_neg h, add_zero]
    rcases r with r | r <;> rcases s with s | s
    · exact continuous_fst.matrix_elem r s
    all_goals exact continuous_const

theorem isClosedEmbedding_affPt_uncurry [T2Space k] (p : ℕ) :
    IsClosedEmbedding
      fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
        affPt p z.1 z.2 := by
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k =>
      ((Matrix.of fun r s => M (Sum.inl r) (Sum.inl s) : Matrix n n' k),
        fun rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} =>
          M rs.1.1 rs.1.2 - basePt c (0 : Matrix n n' k) rs.1.1 rs.1.2)) ?_ ?_
    (continuous_affPt_uncurry p)
  · rintro ⟨x, e⟩
    refine Prod.ext ?_ ?_
    · ext r s
      simp [affPt_inl_inl]
    · funext rs
      simp [affPt_of_free]
  · refine Continuous.prodMk (continuous_matrix fun r s => continuous_id.matrix_elem _ _) ?_
    exact continuous_pi fun rs => (continuous_id.matrix_elem _ _).sub continuous_const

theorem comp_affPt_mem_SB [T2Space k] (p : ℕ) {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    (fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
        Φ (affPt p z.1 z.2)) ∈ SB _ :=
  ⟨hΦ.1.comp_continuous (continuous_affPt_uncurry p),
    hΦ.2.comp_isClosedEmbedding (isClosedEmbedding_affPt_uncurry p)⟩

end

section
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c : ℕ}

open scoped Classical in
open Classical in
theorem integrable_opE_integrand (p : ℕ) {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k)
    [ν.IsAddHaarMeasure] {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (x₀ : Matrix n n' k) :
    Integrable (fun e => Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ)) (Measure.pi fun _ => ν) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc : Continuous fun e => affPt (c := c) p x₀ e :=
    (continuous_affPt_uncurry p).comp (Continuous.prodMk_right x₀)
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · refine (hΦ.1.continuous.comp hc).mul (continuous_subtype_val.comp (hψ.comp (Continuous.neg ?_)))
    exact continuous_finsetSum _ fun i _ => hc.matrix_elem _ _
  · refine HasCompactSupport.mul_right ?_
    have h2 := (comp_affPt_mem_SB p hΦ).2
    refine HasCompactSupport.intro (h2.isCompact.image continuous_snd) fun e he => ?_
    exact image_eq_zero_of_notMem_tsupport
      (f := fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
        Φ (affPt p z.1 z.2)) (x := (x₀, e)) fun h' => he ⟨_, h', rfl⟩

omit [BorelSpace k] [DecidableEq n] [DecidableEq n'] in
theorem opE_mem_SB (p : ℕ) (ψ : AddChar k Circle) (ν : Measure k)
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) : opE ψ ν p Φ ∈ SB (Matrix n n' k) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  exact integral_mul_mem_SB _ _ (comp_affPt_mem_SB p hΦ)
    (fun e => (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ))

theorem opE_smul_add (p : ℕ) {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k)
    [ν.IsAddHaarMeasure] (z : ℂ) {Φ Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (hΨ : Ψ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    opE ψ ν p (z • Φ + Ψ) = z • opE ψ ν p Φ + opE ψ ν p Ψ := by
  funext x₀
  have h1 := (integrable_opE_integrand p hψ ν hΦ x₀).const_mul z
  have h2 := integrable_opE_integrand p hψ ν hΨ x₀
  simp only [opE, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_add h1 h2]
  congr 1
  funext e
  ring

end

theorem opE_SB_and_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure], (∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), opE ψ ν p Φ ∈ SB (Matrix n n' k)) ∧ ∀ (z : ℂ), ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ Ψ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), opE ψ ν p (z • Φ + Ψ) = z • opE ψ ν p Φ + opE ψ ν p Ψ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ p ψ hψ ν _ =>
    ⟨fun _ hΦ => opE_mem_SB p ψ ν hΦ, fun z _ hΦ _ hΨ => opE_smul_add p hψ ν z hΦ hΨ⟩

end GlobalTheory.RootEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumTupleProdOfSummableNormComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumTupleProdOfSummableNormComplex
open scoped InnerProductSpace

namespace GlobalTheory

open Filter Topology

theorem hasSum_pi_prod_of_summable_norm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (J : ι → Type) (f : ∀ i, J i → ℂ), (∀ i, Summable (fun j => ‖f i j‖)) → HasSum (fun j : ∀ i, J i => ∏ i, f i (j i)) (∏ i, ∑' j, f i j) := by
  intro ι _ _ J f hf
  classical
  have hnorm : Summable fun j : ∀ i, J i => ‖∏ i, f i (j i)‖ := by
    have := splitHeight_summable_pi_prod (α := J) (f := fun i x => ‖f i x‖)
      (fun i x => norm_nonneg (f i x)) hf
    refine this.congr fun j => ?_
    exact (norm_prod _ _).symm
  have hs : Summable fun j : ∀ i, J i => ∏ i, f i (j i) := hnorm.of_norm
  have hcof : Tendsto (fun S : ∀ i, Finset (J i) => Fintype.piFinset S) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun t => ⟨fun i => t.image (· i), fun S hS => ?_⟩
    intro x hx
    exact Fintype.mem_piFinset.2 fun i => hS i (Finset.mem_image_of_mem _ hx)
  have h1 : Tendsto (fun S : ∀ i, Finset (J i) => ∑ x ∈ Fintype.piFinset S, ∏ i, f i (x i))
      atTop (𝓝 (∑' j : ∀ i, J i, ∏ i, f i (j i))) := hs.hasSum.comp hcof
  have hproj : ∀ i, Tendsto (fun S : ∀ i, Finset (J i) => S i) atTop atTop := by
    intro i
    refine Filter.tendsto_atTop_atTop.2 fun b =>
      ⟨Function.update (fun j => (∅ : Finset (J j))) i b, fun S hS => ?_⟩
    have := hS i
    simpa using this
  have h2 : Tendsto (fun S : ∀ i, Finset (J i) => ∏ i, ∑ x ∈ S i, f i x)
      atTop (𝓝 (∏ i, ∑' j, f i j)) :=
    tendsto_finsetProd _ fun i _ => ((hf i).of_norm.hasSum).comp (hproj i)
  have h3 : (fun S : ∀ i, Finset (J i) => ∑ x ∈ Fintype.piFinset S, ∏ i, f i (x i)) =
      fun S => ∏ i, ∑ x ∈ S i, f i x := by
    funext S; exact (Finset.prod_univ_sum S fun i x => f i x).symm
  rw [h3] at h1
  have := tendsto_nhds_unique h1 h2
  rw [← this]; exact hs.hasSum

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumTupleProdOfSummableNormComplexStatement
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_tuple_prod_of_summable_norm_complex : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (J : ι → Type) (f : ∀ i, J i → ℂ), (∀ i, Summable (fun j => ‖f i j‖)) → HasSum (fun j : ∀ i, J i => ∏ i, f i (j i)) (∏ i, ∑' j, f i j) := by
  first | exact @GlobalTheory.hasSum_pi_prod_of_summable_norm | exact GlobalTheory.hasSum_pi_prod_of_summable_norm | (intros; apply GlobalTheory.hasSum_pi_prod_of_summable_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfProdFunEqStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multilinearMap_sum_eq_of_sum_prod_eval_eq : ∀ {ι κ : Type} [Fintype ι] {X : ι → Type} (V : ∀ l, Submodule ℂ (X l → ℂ))
    (Φ : (∀ l, V l) →ₘₗ[ℂ] ℂ) (a : κ →₀ ℂ) (f g : κ → ∀ l, V l),
    (∀ z : ∀ l, X l, (a.sum fun c b => b * ∏ l, (f c l : X l → ℂ) (z l)) = a.sum fun c b => b * ∏ l, (g c l : X l → ℂ) (z l)) →
    (a.sum fun c b => b * Φ (f c)) = a.sum fun c b => b * Φ (g c) := by
  exact @GlobalTheory.multilinear_sum_eq_of_prod_fun_eq
end
