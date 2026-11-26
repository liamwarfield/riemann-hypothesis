module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCrystallineBlockDataOfReductionPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachLatticesRankOneModelsReducedFiltration

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineBlockLatticesOverPowerSeriesRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasesBlockTriangularOfReducedEtaleFiltrat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEntryOfSemilinearModSubspace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEntryOfSemilinearModSubspace
open PowerSeries

namespace GlobalTheory

theorem diagonal_entry_of_semilinear_mod_subspace : ∀ (F : Type) [Field F] (n : ℕ) (θ : PowerSeries F →+* PowerSeries F) (A : Matrix (Fin n) (Fin n) (PowerSeries F)) (W' W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (f' e' f e : Fin n → PowerSeries F) (w' w : (PowerSeries F)ˣ) (k' k m : ℤ) (d : PowerSeries F) (α : LaurentSeries F), ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ≠ 0 → (∀ y : Fin n → PowerSeries F, (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((A.mulVec (fun c => θ (y c)) a : PowerSeries F) : LaurentSeries F)) ∈ W) → (fun a => ((f' a : PowerSeries F) : LaurentSeries F)) - (((w' : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k') • (fun a => ((e' a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((f a : PowerSeries F) : LaurentSeries F)) - (((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k) • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∉ W → (fun a => ((A.mulVec (fun c => θ (f' c)) a : PowerSeries F) : LaurentSeries F)) - ((d : PowerSeries F) : LaurentSeries F) • (fun a => ((f a : PowerSeries F) : LaurentSeries F)) ∈ W → (((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m) • (fun a => ((A.mulVec (fun c => θ (e' c)) a : PowerSeries F) : LaurentSeries F)) - α • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → ((θ (w' : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k' * α = ((d : PowerSeries F) : LaurentSeries F) * ((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m := by
  intro F _ n θ A W' W f' e' f e w' w k' k m d α hξ hT hf' hf he hTf hTe
  have hx : ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ≠ 0 := by
    intro h
    apply PowerSeries.X_ne_zero (R := F)
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa using h
  set x : LaurentSeries F := ((PowerSeries.X : PowerSeries F) : LaurentSeries F) with hxdef
  set ξ : LaurentSeries F := ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) with hξdef
  obtain ⟨N, j, hj⟩ : ∃ N j : ℕ, (j : ℤ) = (N : ℤ) + k' := ⟨k'.natAbs, (k'.natAbs + k').toNat, by omega⟩
  set a : PowerSeries F := (w' : PowerSeries F) * PowerSeries.X ^ j with hadef
  have ha : ((a : PowerSeries F) : LaurentSeries F) = (w' : LaurentSeries F) * x ^ N * x ^ k' := by
    rw [hadef, PowerSeries.coe_mul, PowerSeries.coe_pow, ← zpow_natCast, hj, zpow_add₀ hx, zpow_natCast, mul_assoc]
  have hθa : ((θ a : PowerSeries F) : LaurentSeries F) = ((θ (w' : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ξ ^ N * ξ ^ k' := by
    rw [hadef, map_mul, map_pow, PowerSeries.coe_mul, PowerSeries.coe_pow, ← zpow_natCast, hj, zpow_add₀ hξ, zpow_natCast, mul_assoc]
  let y : Fin n → PowerSeries F := fun c => PowerSeries.X ^ N * f' c - a * e' c
  have hy : (fun c => ((y c : PowerSeries F) : LaurentSeries F)) ∈ W' := by
    have : (fun c => ((y c : PowerSeries F) : LaurentSeries F)) = (x ^ N) • ((fun a => ((f' a : PowerSeries F) : LaurentSeries F)) - (((w' : PowerSeries F) : LaurentSeries F) * x ^ k') • (fun a => ((e' a : PowerSeries F) : LaurentSeries F))) := by
      funext c
      simp only [y, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, PowerSeries.coe_sub, PowerSeries.coe_mul, PowerSeries.coe_pow, ha, ← hxdef]
      ring
    rw [this]; exact W'.smul_mem _ hf'
  have hvec : A.mulVec (fun c => θ (y c)) = (θ PowerSeries.X) ^ N • A.mulVec (fun c => θ (f' c)) - θ a • A.mulVec (fun c => θ (e' c)) := by
    have : (fun c => θ (y c)) = (θ PowerSeries.X) ^ N • (fun c => θ (f' c)) - θ a • (fun c => θ (e' c)) := by
      ext c; simp [y]
    rw [this, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hTy := hT y hy
  set P : Fin n → LaurentSeries F := fun i => ((A.mulVec (fun c => θ (f' c)) i : PowerSeries F) : LaurentSeries F) with hP
  set Q : Fin n → LaurentSeries F := fun i => ((A.mulVec (fun c => θ (e' c)) i : PowerSeries F) : LaurentSeries F) with hQ
  set E : Fin n → LaurentSeries F := fun i => ((e i : PowerSeries F) : LaurentSeries F) with hE
  set Fv : Fin n → LaurentSeries F := fun i => ((f i : PowerSeries F) : LaurentSeries F) with hFv
  have h4 : ξ ^ N • P - ((θ a : PowerSeries F) : LaurentSeries F) • Q ∈ W := by
    have : (fun i => ((A.mulVec (fun c => θ (y c)) i : PowerSeries F) : LaurentSeries F)) = ξ ^ N • P - ((θ a : PowerSeries F) : LaurentSeries F) • Q := by
      funext i
      simp only [hvec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, PowerSeries.coe_sub, PowerSeries.coe_mul, PowerSeries.coe_pow, hP, hQ, hξdef]
    rw [← this]; exact hTy
  set c : LaurentSeries F := ((θ a : PowerSeries F) : LaurentSeries F) * α - x ^ m * ξ ^ N * ((d : PowerSeries F) : LaurentSeries F) * ((w : PowerSeries F) : LaurentSeries F) * x ^ k with hc
  have hcE : c • E ∈ W := by
    have h := W.sub_mem (W.sub_mem (W.add_mem (W.smul_mem (x ^ m * ξ ^ N) hTf) (W.smul_mem (x ^ m * ξ ^ N * ((d : PowerSeries F) : LaurentSeries F)) hf)) (W.smul_mem (((θ a : PowerSeries F) : LaurentSeries F)) hTe)) (W.smul_mem (x ^ m) h4)
    convert h using 1
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, hc]
    ring
  have hc0 : c = 0 := by
    by_contra hne
    apply he
    have := W.smul_mem c⁻¹ hcE
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hξN : ξ ^ N ≠ 0 := pow_ne_zero _ hξ
  rw [hc, hθa, sub_eq_zero] at hc0
  apply mul_right_cancel₀ hξN
  linear_combination hc0

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEntryOfSemilinearModSubspaceStatement
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_entry_of_semilinear_mod_subspace_alt : ∀ (F : Type) [Field F] (n : ℕ) (θ : PowerSeries F →+* PowerSeries F) (A : Matrix (Fin n) (Fin n) (PowerSeries F)) (W' W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (f' e' f e : Fin n → PowerSeries F) (w' w : (PowerSeries F)ˣ) (k' k m : ℤ) (d : PowerSeries F) (α : LaurentSeries F), ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ≠ 0 → (∀ y : Fin n → PowerSeries F, (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((A.mulVec (fun c => θ (y c)) a : PowerSeries F) : LaurentSeries F)) ∈ W) → (fun a => ((f' a : PowerSeries F) : LaurentSeries F)) - (((w' : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k') • (fun a => ((e' a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((f a : PowerSeries F) : LaurentSeries F)) - (((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k) • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∉ W → (fun a => ((A.mulVec (fun c => θ (f' c)) a : PowerSeries F) : LaurentSeries F)) - ((d : PowerSeries F) : LaurentSeries F) • (fun a => ((f a : PowerSeries F) : LaurentSeries F)) ∈ W → (((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m) • (fun a => ((A.mulVec (fun c => θ (e' c)) a : PowerSeries F) : LaurentSeries F)) - α • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → ((θ (w' : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k' * α = ((d : PowerSeries F) : LaurentSeries F) * ((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m := by
  first | exact @GlobalTheory.diagonal_entry_of_semilinear_mod_subspace | exact GlobalTheory.diagonal_entry_of_semilinear_mod_subspace | (intros; apply GlobalTheory.diagonal_entry_of_semilinear_mod_subspace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedIntegralBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedIntegralBasis
open PowerSeries

namespace GlobalTheory.LaurentFlagBasis

variable {F : Type} [Field F]

noncomputable def red {n : ℕ} (y : Fin n → PowerSeries F) : Fin n → F := fun a => constantCoeff (y a)

noncomputable def lift {n : ℕ} (y : Fin n → PowerSeries F) : Fin n → LaurentSeries F :=
  fun a => (y a : LaurentSeries F)

lemma exists_primitive {n : ℕ} (u : Fin n → LaurentSeries F) (hu : u ≠ 0) :
    ∃ (i : Fin n) (y : Fin n → PowerSeries F), lift y = (u i)⁻¹ • u ∧ y i = 1 := by
  obtain ⟨l, hl⟩ : ∃ l, u l ≠ 0 := by
    by_contra h; push Not at h; exact hu (funext h)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun a => Valued.v (u a))
    ⟨l, Finset.mem_univ _⟩
  have hvl : Valued.v (u l) ≠ 0 := (Valuation.ne_zero_iff _).mpr hl
  have hvi : 0 < Valued.v (u i) := by
    have := hi l (Finset.mem_univ _)
    exact lt_of_lt_of_le (zero_lt_iff.mpr hvl) this
  have hui : u i ≠ 0 := (Valuation.ne_zero_iff _).mp hvi.ne'
  have key : ∀ a, ∃ P : PowerSeries F, (P : LaurentSeries F) = (u i)⁻¹ * u a := by
    intro a
    have := (LaurentSeries.val_le_one_iff_eq_coe F ((u i)⁻¹ * u a)).mp (by
      rw [map_mul, map_inv₀, inv_mul_le_one₀ hvi]
      exact hi a (Finset.mem_univ _))
    exact this
  choose y hy using key
  refine ⟨i, y, funext fun a => ?_, ?_⟩
  · simp [lift, hy]
  · apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [hy, inv_mul_cancel₀ hui, map_one]

lemma exists_indep {n : ℕ} : ∀ (d : ℕ) (U : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)),
    d ≤ Module.finrank (LaurentSeries F) U →
    ∃ y : Fin d → (Fin n → PowerSeries F), (∀ b, lift (y b) ∈ U) ∧
      LinearIndependent F (fun b => red (y b)) := by
  intro d
  induction d with
  | zero =>
    intro U _
    exact ⟨Fin.elim0, fun b => b.elim0, linearIndependent_empty_type⟩
  | succ d ih =>
    intro U hd
    have hU : U ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hd
      omega
    obtain ⟨u, huU, hu0⟩ : ∃ u : Fin n → LaurentSeries F, u ∈ U ∧ u ≠ 0 :=
      Submodule.exists_mem_ne_zero_of_ne_bot hU
    obtain ⟨i, y0, hy0, hy0i⟩ := exists_primitive u hu0
    let f : U →ₗ[LaurentSeries F] LaurentSeries F := (LinearMap.proj i).comp U.subtype
    let U' : Submodule (LaurentSeries F) (Fin n → LaurentSeries F) := (LinearMap.ker f).map U.subtype
    have hU' : d ≤ Module.finrank (LaurentSeries F) U' := by
      have h1 := LinearMap.finrank_range_add_finrank_ker f
      have h2 : Module.finrank (LaurentSeries F) (LinearMap.range f) ≤ 1 := by
        simpa using Submodule.finrank_le (LinearMap.range f)
      have h3 : Module.finrank (LaurentSeries F) U' =
          Module.finrank (LaurentSeries F) (LinearMap.ker f) :=
        (Submodule.equivMapOfInjective _ U.injective_subtype _).finrank_eq.symm
      omega
    obtain ⟨y, hyU, hyi⟩ := ih U' hU'
    refine ⟨Fin.cons y0 y, ?_, ?_⟩
    · intro b
      refine Fin.cases ?_ (fun b => ?_) b
      · simp only [Fin.cons_zero]; rw [hy0]; exact U.smul_mem _ huU
      · simp only [Fin.cons_succ]
        obtain ⟨z, -, hz⟩ := Submodule.mem_map.mp (hyU b)
        rw [← hz]; exact z.2
    · have e : (fun b => red ((Fin.cons y0 y : Fin (d+1) → Fin n → PowerSeries F) b)) =
          Fin.cons (red y0) (fun b => red (y b)) := by
        ext b; refine Fin.cases ?_ (fun b => ?_) b <;> simp
      rw [e, linearIndependent_finCons]
      refine ⟨hyi, fun hmem => ?_⟩
      have hsub : Submodule.span F (Set.range fun b => red (y b)) ≤
          LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : Fin n => F) i) := by
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        obtain ⟨z, hz, hzz⟩ := Submodule.mem_map.mp (hyU b)
        have hz0 : (z : Fin n → LaurentSeries F) i = 0 := hz
        have h0 : ((y b i : PowerSeries F) : LaurentSeries F) = 0 := by
          have := congrFun hzz i
          simp only [Submodule.subtype_apply] at this
          rw [← hz0, this]; rfl
        have h00 : y b i = 0 := by
          apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
          rw [map_zero]; exact h0
        simp [red, h00]
      have := hsub hmem
      simp [red, hy0i] at this

lemma greedy {n : ℕ} (V : ℕ → Submodule (LaurentSeries F) (Fin n → LaurentSeries F))
    (hV : ∀ j, j < n → j < Module.finrank (LaurentSeries F) (V j)) :
    ∀ m, m ≤ n → ∃ c : Fin m → (Fin n → PowerSeries F), (∀ j : Fin m, lift (c j) ∈ V j) ∧
      LinearIndependent F (fun j => red (c j)) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨Fin.elim0, fun j => j.elim0, linearIndependent_empty_type⟩
  | succ m ih =>
    intro hm
    obtain ⟨c, hcV, hci⟩ := ih (Nat.le_of_succ_le hm)
    obtain ⟨y, hyV, hyi⟩ := exists_indep (Module.finrank (LaurentSeries F) (V m)) (V m) le_rfl
    have : ∃ b, red (y b) ∉ Submodule.span F (Set.range fun j => red (c j)) := by
      by_contra h; push Not at h
      have h1 : Submodule.span F (Set.range fun b => red (y b)) ≤
          Submodule.span F (Set.range fun j => red (c j)) :=
        Submodule.span_le.mpr (by rintro _ ⟨b, rfl⟩; exact h b)
      have h2 := Submodule.finrank_mono h1
      rw [finrank_span_eq_card hyi, finrank_span_eq_card hci] at h2
      simp at h2
      have := hV m (by omega)
      omega
    obtain ⟨b, hb⟩ := this
    refine ⟨Fin.snoc (α := fun _ => Fin n → PowerSeries F) c (y b), ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [Fin.snoc_last, Fin.val_last]; exact hyV b
      · simp only [Fin.snoc_castSucc, Fin.val_castSucc]; exact hcV j
    · have e : (fun j => red ((Fin.snoc (α := fun _ => Fin n → PowerSeries F) c (y b)) j)) =
          Fin.snoc (α := fun _ => Fin n → F) (fun j => red (c j)) (red (y b)) := by
        ext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
      rw [e, linearIndependent_finSnoc]
      exact ⟨hci, hb⟩

end GlobalTheory.LaurentFlagBasis


open GlobalTheory.LaurentFlagBasis in
theorem GlobalTheory.LaurentFlagBasis.adapted_integral_basis : ∀ (F : Type) [Field F] (n R : ℕ)
    (W : Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F)), Monotone W →
    ∃ g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ, ∀ (k : Fin (R + 1)) (j : Fin n),
      (j : ℕ) < Module.finrank (LaurentSeries F) (W k) →
      (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) :
        LaurentSeries F)) ∈ W k := by
  intro F _ n R W hW
  let V : ℕ → Submodule (LaurentSeries F) (Fin n → LaurentSeries F) := fun j =>
    ⨅ (k : Fin (R + 1)) (_ : j < Module.finrank (LaurentSeries F) (W k)), W k
  have hV : ∀ j, j < n → j < Module.finrank (LaurentSeries F) (V j) := by
    intro j hj
    by_cases h : ∃ k, j < Module.finrank (LaurentSeries F) (W k)
    · obtain ⟨k, hk⟩ := h
      obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image
        (Finset.univ.filter fun k => j < Module.finrank (LaurentSeries F) (W k)) id
        ⟨k, by simp [hk]⟩
      have hle : W k0 ≤ V j := le_iInf₂ fun k hk => hW (hmin k (by simp [hk]))
      have := Submodule.finrank_mono hle
      simp at hk0
      omega
    · push Not at h
      have hle : ⊤ ≤ V j := le_iInf₂ fun k hk => absurd hk (not_lt.mpr (h k))
      have := Submodule.finrank_mono hle
      rw [finrank_top, Module.finrank_fin_fun] at this
      omega
  obtain ⟨c, hcV, hci⟩ := greedy V hV n le_rfl
  let g : Matrix (Fin n) (Fin n) (PowerSeries F) := Matrix.of fun a j => c j a
  have hunit : IsUnit g := by
    rw [Matrix.isUnit_iff_isUnit_det, PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det,
      ← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_col_iff_isUnit]
    convert hci using 1
    funext j a
    simp [g, red, Matrix.col]
  refine ⟨hunit.unit, fun k j hj => ?_⟩
  have hmem := hcV j
  have hVk : V j ≤ W k := iInf₂_le k hj
  exact hVk hmem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedIntegralBasisStatement
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_matrix_adapted_to_flag : ∀ (F : Type) [Field F] (n R : ℕ) (W : Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F)), Monotone W → ∃ g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ, ∀ (k : Fin (R + 1)) (j : Fin n), (j : ℕ) < Module.finrank (LaurentSeries F) (W k) → (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W k := by
  first | exact @GlobalTheory.LaurentFlagBasis.adapted_integral_basis | exact GlobalTheory.LaurentFlagBasis.adapted_integral_basis | (intros; apply GlobalTheory.LaurentFlagBasis.adapted_integral_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentSeriesAdaptedBasisCoordsVanishBeyondFinra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentSeriesAdaptedBasisCoordsVanishBeyondFinra
open PowerSeries

namespace GlobalTheory

theorem inv_mulVec_coord_eq_zero_of_adapted_columns_injective {R K : Type} [CommRing R] [Field K] (φ : R →+* K)
    (hφ : Function.Injective φ) (n : ℕ) (W : Submodule K (Fin n → K))
    (g : (Matrix (Fin n) (Fin n) R)ˣ)
    (hg : ∀ j : Fin n, (j : ℕ) < Module.finrank K W →
      (fun a => φ ((g : Matrix (Fin n) (Fin n) R) a j)) ∈ W)
    (y : Fin n → R) (hy : (fun a => φ (y a)) ∈ W)
    (a : Fin n) (ha : Module.finrank K W ≤ (a : ℕ)) :
    (((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R).mulVec y) a = 0 := by
  classical
  have hr : Module.finrank K W ≤ n := by
    have := Submodule.finrank_le W
    simpa using this
  set r := Module.finrank K W with hrdef
  let G : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) R).map φ
  let H : Matrix (Fin n) (Fin n) K := ((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R).map φ
  have hHG : H * G = 1 := by
    calc H * G = (RingHom.mapMatrix φ) (((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) * (g : Matrix (Fin n) (Fin n) R)) :=
          ((RingHom.mapMatrix φ).map_mul _ _).symm
      _ = 1 := by rw [Units.inv_mul, map_one]
  let e : Fin r → (Fin n → K) := fun i => Pi.single (Fin.castLE hr i) 1
  let v : Fin r → (Fin n → K) := fun i => fun b => G b (Fin.castLE hr i)
  have hHv : ∀ i, H.mulVec (v i) = e i := by
    intro i
    have : v i = G.mulVec (Pi.single (Fin.castLE hr i) 1) := by
      ext b; simp [v, Matrix.mulVec_single]
    rw [this, Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec]
  have hcomp : (Matrix.toLin' H) ∘ v = e := by
    funext i; simp only [Function.comp_apply, Matrix.toLin'_apply, hHv]
  have hli : LinearIndependent K v := by
    apply LinearIndependent.of_comp (Matrix.toLin' H)
    rw [hcomp]
    exact (Pi.linearIndependent_single_one (Fin n) K).comp _ (Fin.castLE_injective hr)
  have hle : Submodule.span K (Set.range v) ≤ W := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    exact hg (Fin.castLE hr i) (by simp)
  have heq : Submodule.span K (Set.range v) = W := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hy' : (fun b => φ (y b)) ∈ Submodule.span K (Set.range v) := heq ▸ hy
  have hmap : H.mulVec (fun b => φ (y b)) ∈ Submodule.span K (Set.range e) := by
    have := Submodule.mem_map_of_mem (f := Matrix.toLin' H) hy'
    rw [Submodule.map_span, ← Set.range_comp, hcomp, Matrix.toLin'_apply] at this
    exact this
  have hker : Submodule.span K (Set.range e) ≤ LinearMap.ker (LinearMap.proj a) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, e]
    apply Pi.single_eq_of_ne
    intro h
    have : ((Fin.castLE hr i : Fin n) : ℕ) = a := by rw [h]
    simp at this
    omega
  have h0 : (H.mulVec (fun b => φ (y b))) a = 0 := hker hmap
  have hcoe : φ ((((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R).mulVec y) a) =
      (H.mulVec (fun b => φ (y b))) a := by
    rw [RingHom.map_mulVec]
    rfl
  rw [h0] at hcoe
  exact (injective_iff_map_eq_zero φ).mp hφ _ hcoe

theorem adapted_coords_vanish (F : Type) [Field F] (n : ℕ)
    (W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F))
    (g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ)
    (hg : ∀ j : Fin n, (j : ℕ) < Module.finrank (LaurentSeries F) W →
      (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W)
    (y : Fin n → PowerSeries F) (hy : (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W)
    (a : Fin n) (ha : Module.finrank (LaurentSeries F) W ≤ (a : ℕ)) :
    (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec y) a = 0 :=
  inv_mulVec_coord_eq_zero_of_adapted_columns_injective (HahnSeries.ofPowerSeries ℤ F) HahnSeries.ofPowerSeries_injective n W g hg y hy a ha

theorem adapted_coords_vanish_stmt : ∀ (F : Type) [Field F] (n : ℕ) (W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ), (∀ j : Fin n, (j : ℕ) < Module.finrank (LaurentSeries F) W → (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W) → ∀ y : Fin n → PowerSeries F, (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W → ∀ a : Fin n, Module.finrank (LaurentSeries F) W ≤ (a : ℕ) → (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec y) a = 0 :=
  fun F _ n W g hg y hy a ha => adapted_coords_vanish F n W g hg y hy a ha

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentSeriesAdaptedBasisCoordsVanishBeyondFinraStatement
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentSeries_adapted_basis_coords_vanish_beyond_finrank : ∀ (F : Type) [Field F] (n : ℕ) (W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ), (∀ j : Fin n, (j : ℕ) < Module.finrank (LaurentSeries F) W → (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W) → ∀ y : Fin n → PowerSeries F, (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W → ∀ a : Fin n, Module.finrank (LaurentSeries F) W ≤ (a : ℕ) → (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec y) a = 0 := by
  first | exact @GlobalTheory.adapted_coords_vanish_stmt | exact GlobalTheory.adapted_coords_vanish_stmt | (intros; apply GlobalTheory.adapted_coords_vanish_stmt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasesBlockTriangularOfReducedEtaleFiltrat
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.ExpFrame PowerSeries Formalism.CohomologicalDescent.FrobeniusPeriodChange

namespace GlobalTheory.WachBlock

theorem finrank_sup_span_singleton_of_not_mem : ∀ (K : Type) [Field K] (n : ℕ) (W : Submodule K (Fin n → K)) (x : Fin n → K), x ∉ W → Module.finrank K ↥(W ⊔ Submodule.span K {x}) = Module.finrank K W + 1 := by
  intro K _ n W x hx
  have hx0 : x ≠ 0 := fun h => hx (h ▸ W.zero_mem)
  have hinf : W ⊓ Submodule.span K {x} = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzW, hzs⟩ := Submodule.mem_inf.1 hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hzs
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd (by simpa [hc] using W.smul_mem c⁻¹ hzW) hx
  have := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span K {x})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hx0] at this
  exact this

theorem laurent_eq_unit_mul_X_zpow : ∀ (F : Type) [Field F] (x : LaurentSeries F), x ≠ 0 → ∃ (w : (PowerSeries F)ˣ) (k : ℤ), x = ((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k := by
  intro F _ x hx
  have hsingle : ∀ k : ℤ, (HahnSeries.single k (1 : F) : LaurentSeries F) = ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k := by
    intro k
    rcases Int.eq_nat_or_neg k with ⟨j, rfl | rfl⟩
    · rw [zpow_natCast, ← map_pow, HahnSeries.ofPowerSeries_X_pow]
      try simp
    · rw [zpow_neg, zpow_natCast, ← map_pow, HahnSeries.ofPowerSeries_X_pow]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [HahnSeries.single_mul_single]
      simp
  have hunit : IsUnit x.powerSeriesPart := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      LaurentSeries.powerSeriesPart_coeff, Nat.cast_zero, add_zero]
    exact isUnit_iff_ne_zero.2 (fun h => hx (HahnSeries.coeff_order_eq_zero.1 h))
  refine ⟨hunit.unit, x.order, ?_⟩
  rw [IsUnit.unit_spec, ← hsingle, mul_comm]
  exact (LaurentSeries.single_order_mul_powerSeriesPart x).symm

theorem sub_coord_smul_col_mem : ∀ (F : Type) [Field F] (n : ℕ) (U : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) (z : Fin n → PowerSeries F) (p : Fin n), (∀ a : Fin n, a ≠ p → (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec z) a ≠ 0 → (fun c => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) c a : PowerSeries F) : LaurentSeries F)) ∈ U) → (fun c => ((z c : PowerSeries F) : LaurentSeries F)) - (((((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec z) p : PowerSeries F) : LaurentSeries F) • (fun c => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) c p : PowerSeries F) : LaurentSeries F)) ∈ U := by
  intro F _ n U g z p h
  set v := (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F))).mulVec z with hv
  have hz : z = (g : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec v := by
    rw [hv, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hsum : (fun c => ((z c : PowerSeries F) : LaurentSeries F)) =
      ∑ a, ((v a : PowerSeries F) : LaurentSeries F) • (fun c => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) c a : PowerSeries F) : LaurentSeries F)) := by
    funext c
    conv_lhs => rw [hz]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, map_sum, mul_comm]
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ p), add_sub_cancel_left]
  refine U.sum_mem fun a ha => ?_
  by_cases h0 : v a = 0
  · simp [h0]
  · exact U.smul_mem _ (h a (Finset.ne_of_mem_erase ha) h0)

theorem adapted_bases_of_redFilt : ∀ (ι : Type) (σ : Equiv.Perm ι) (l n t : ℕ) (F : Type) [Field F] (un : PowerSeries F) (P D : ι → Matrix (Fin n) (Fin n) (PowerSeries F)) (Pψ Dψ : Fin t → ι → PowerSeries F), 0 < l → Nonempty ι → GlobalTheory.WachBlock.RedFilt σ l un P D Pψ Dψ → ∃ (g : ι → (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) (b : Fin n → ℕ) (pos : Fin t → Fin n) (w : ι → Fin t → (PowerSeries F)ˣ) (kap : ι → Fin t → ℤ), (Function.Injective pos ∧ ∀ s j, b j = b (pos s) → j = pos s) ∧ (∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i)).BlockTriangular b) ∧ (∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i)).BlockTriangular b) ∧ (∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.frob0 l (w (σ i) s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ ((l : ℤ) * kap (σ i) s) * ((Pψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ kap i s) ∧ (∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gam0 0 un (w i s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gamSer 0 un : PowerSeries F) : LaurentSeries F) ^ kap i s * ((1 + PowerSeries.X * Dψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ kap i s) := by
  intro ι σ l n t F _ un P D Pψ Dψ hl hne hR
  classical
  obtain ⟨R, V, rs, e, m, hrs, hV, hdim, hphi, hgam, hline, hrelP, hrelG⟩ := hR
  obtain ⟨i0⟩ := hne
  let K := LaurentSeries F
  let d : Fin (R + 1) → ℕ := fun k => Module.finrank K (V i0 k)
  have hdi : ∀ i k, Module.finrank K (V i k) = d k := fun i k => hdim k i i0
  have hdmono : Monotone d := fun a b hab => Submodule.finrank_mono ((hV i0).2.2 hab)
  have hdlast : d (Fin.last R) = n := by
    show Module.finrank K (V i0 (Fin.last R)) = n
    rw [(hV i0).2.1, finrank_top, Module.finrank_fin_fun]
  have hdle : ∀ k, d k ≤ n := fun k => hdlast ▸ hdmono (Fin.le_last k)

  choose g hg using fun i => GlobalTheory.T.exists_unit_matrix_adapted_to_flag F n R (V i) (hV i).2.2
  have hg' : ∀ i k (j : Fin n), (j : ℕ) < d k → lau (fun a => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) a j) ∈ V i k :=
    fun i k j hj => hg i k j (by rw [hdi]; exact hj)

  have hex : ∀ j : Fin n, ∃ k, ∃ h : k < R + 1, (j : ℕ) < d ⟨k, h⟩ :=
    fun j => ⟨R, Nat.lt_succ_self R, by have := hdlast; simp only [Fin.last] at this; rw [this]; exact j.2⟩
  let b : Fin n → ℕ := fun j => Nat.find (hex j)
  have hbR : ∀ j, b j < R + 1 := fun j => (Nat.find_spec (hex j)).1
  have hb : ∀ (j : Fin n) (k : Fin (R + 1)), (j : ℕ) < d k ↔ b j ≤ (k : ℕ) := by
    intro j k
    constructor
    · intro h
      exact Nat.find_min' (hex j) ⟨k.2, h⟩
    · intro h
      obtain ⟨h1, h2⟩ := Nat.find_spec (hex j)
      exact lt_of_lt_of_le h2 (hdmono (show (⟨b j, h1⟩ : Fin (R + 1)) ≤ k from h))

  have hentP : ∀ i (a j : Fin n), Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i) a j =
      (((g i)⁻¹ : (Matrix (Fin n) (Fin n) F⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) F⟦X⟧).mulVec
        (phiV l (P i) (fun c => (g (σ i) : Matrix (Fin n) (Fin n) F⟦X⟧) c j)) a := by
    intro i a j
    simp only [Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi, phiV, Matrix.mulVec_mulVec]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  have hentG : ∀ i (a j : Fin n), Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i) a j =
      (((g i)⁻¹ : (Matrix (Fin n) (Fin n) F⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) F⟦X⟧).mulVec
        (gamV un (D i) (fun c => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) c j)) a := by
    intro i a j
    simp only [Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam, gamV, Matrix.mulVec_mulVec]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  have hbtP : ∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i)).BlockTriangular b := by
    intro i a j hlt
    rw [hentP]
    have hmem := hphi i ⟨b j, hbR j⟩ _ (hg' (σ i) ⟨b j, hbR j⟩ j ((hb j _).2 le_rfl))
    refine GlobalTheory.T.laurentSeries_adapted_basis_coords_vanish_beyond_finrank F n (V i ⟨b j, hbR j⟩) (g i) (fun j' hj' => hg i _ j' hj') _ hmem a ?_
    rw [hdi]
    exact Nat.le_of_not_lt (fun h => absurd ((hb a _).1 h) (Nat.not_le.2 hlt))
  have hbtG : ∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i)).BlockTriangular b := by
    intro i a j hlt
    rw [hentG]
    have hmem := hgam i ⟨b j, hbR j⟩ _ (hg' i ⟨b j, hbR j⟩ j ((hb j _).2 le_rfl))
    refine GlobalTheory.T.laurentSeries_adapted_basis_coords_vanish_beyond_finrank F n (V i ⟨b j, hbR j⟩) (g i) (fun j' hj' => hg i _ j' hj') _ hmem a ?_
    rw [hdi]
    exact Nat.le_of_not_lt (fun h => absurd ((hb a _).1 h) (Nat.not_le.2 hlt))

  have hstep : ∀ s, d (rs s).succ = d (rs s).castSucc + 1 := by
    intro s
    show Module.finrank K (V i0 (rs s).succ) = Module.finrank K (V i0 (rs s).castSucc) + 1
    rw [(hline i0 s).2]
    exact finrank_sup_span_singleton_of_not_mem K n _ _ (hline i0 s).1
  let pos : Fin t → Fin n := fun s => ⟨d (rs s).castSucc, by have := hstep s; have := hdle (rs s).succ; omega⟩
  have hpos_lt : ∀ s, (pos s : ℕ) < d (rs s).succ := fun s => by simp only [pos]; rw [hstep]; omega
  have hpos_nlt : ∀ s, ¬ (pos s : ℕ) < d (rs s).castSucc := fun s => by simp [pos]
  have hsing : ∀ s j, b j = b (pos s) → j = pos s := by
    intro s j h
    have h1 : (j : ℕ) < d (rs s).succ := (hb j _).2 (h ▸ (hb (pos s) _).1 (hpos_lt s))
    have h2 : ¬ (j : ℕ) < d (rs s).castSucc := fun hj => hpos_nlt s ((hb (pos s) _).2 (h ▸ (hb j _).1 hj))
    rw [hstep] at h1
    ext
    simp only [pos]
    omega
  have hbpos : ∀ s, b (pos s) = (rs s : ℕ) + 1 := by
    intro s
    have h1 := (hb (pos s) _).1 (hpos_lt s)
    have h2 : ¬ b (pos s) ≤ ((rs s).castSucc : ℕ) := fun h => hpos_nlt s ((hb (pos s) _).2 h)
    simp only [Fin.val_succ, Fin.coe_castSucc] at h1 h2
    omega
  have hinj : Function.Injective pos := by
    intro s s' h
    have h' : b (pos s) = b (pos s') := by rw [h]
    rw [hbpos, hbpos] at h'
    exact hrs (Fin.ext (by omega))

  have hcoef : ∀ i s, ∃ c : K, c ≠ 0 ∧ lau (fun a => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) a (pos s)) - c • lau (e i s) ∈
      V i (rs s).castSucc := by
    intro i s
    have hmem := hg' i (rs s).succ (pos s) (hpos_lt s)
    rw [(hline i s).2, Submodule.mem_sup] at hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    refine ⟨c, ?_, ?_⟩
    · rintro rfl
      rw [zero_smul, add_zero] at hyz
      have h0 := GlobalTheory.T.laurentSeries_adapted_basis_coords_vanish_beyond_finrank F n (V i (rs s).castSucc) (g i) (fun j' hj' => hg i _ j' hj') _ (hyz ▸ hy) (pos s)
        (by rw [hdi] <;> exact Nat.le_of_not_lt (hpos_nlt s))
      have h1 : (((g i)⁻¹ : (Matrix (Fin n) (Fin n) F⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) F⟦X⟧).mulVec
          (fun a => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) a (pos s)) (pos s) = 1 := by
        have := congrFun (congrFun (Units.inv_mul (g i)) (pos s)) (pos s)
        simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
      rw [h1] at h0
      exact one_ne_zero h0
    · rw [← hyz, add_sub_cancel_right]
      exact hy
  choose c hc0 hc using hcoef
  choose w k hwk using fun i s => laurent_eq_unit_mul_X_zpow F (c i s) (hc0 i s)
  have hc' : ∀ i s, lau (fun a => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) a (pos s)) -
      (((w i s : F⟦X⟧) : K) * ((X : F⟦X⟧) : K) ^ k i s) • lau (e i s) ∈ V i (rs s).castSucc :=
    fun i s => hwk i s ▸ hc i s
  have hcoe : ∀ p : F⟦X⟧, p ≠ 0 → ((p : F⟦X⟧) : K) ≠ 0 := fun p hp h =>
    hp (HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm))
  have hX : ((X : F⟦X⟧) : K) ≠ 0 := hcoe _ X_ne_zero
  have hlow : ∀ s (a : Fin n), a ≠ pos s → ¬ b (pos s) < b a → (a : ℕ) < d (rs s).castSucc := by
    intro s a ha hlt
    refine (hb a _).2 ?_
    have h1 : b a ≠ b (pos s) := fun h => ha (hsing s a h)
    have h2 := hbpos s
    simp only [Fin.coe_castSucc]
    omega

  let θF : F⟦X⟧ →+* F⟦X⟧ := (PowerSeries.substAlgHom (PowerSeries.HasSubst.X_pow (R := F) hl.ne')).toRingHom
  have hθF : ∀ y, θF y = frob0 l y := fun y => by simp [θF, frob0, PowerSeries.coe_substAlgHom]
  have hθFX : θF X = X ^ l := by
    rw [hθF, frob0, PowerSeries.subst_X (PowerSeries.HasSubst.X_pow hl.ne')]
  have hrelF : ∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.frob0 l (w (σ i) s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ ((l : ℤ) * (k (σ i) s + m (σ i) s)) * ((Pψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ (k i s + m i s) := by
    intro i s
    have hdP := sub_coord_smul_col_mem F n (V i (rs s).castSucc) (g i) (phiV l (P i) (fun c => (g (σ i) : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s))) (pos s)
      (fun a ha hne => hg' i _ a (hlow s a ha (fun h => hne (by rw [← hentP]; exact hbtP i h))))
    rw [← hentP] at hdP
    have hθFe : ⇑θF = frob0 l := funext hθF
    have key := GlobalTheory.T.diagonal_entry_of_semilinear_mod_subspace_alt F n θF (P i) (V (σ i) (rs s).castSucc) (V i (rs s).castSucc)
      (fun c => (g (σ i) : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s)) (e (σ i) s)
      (fun c => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s)) (e i s)
      (w (σ i) s) (w i s) (k (σ i) s) (k i s) (m i s) (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i) (pos s) (pos s))
      (((X : F⟦X⟧) : K) ^ ((l : ℤ) * m (σ i) s) * ((Pψ s i : F⟦X⟧) : K))
      (by rw [hθFX]; exact hcoe _ (pow_ne_zero _ X_ne_zero))
      (fun y hy => by rw [hθFe]; exact hphi i _ y hy) (hc' (σ i) s) (hc' i s) (hline i s).1
      (by rw [hθFe]; exact hdP) (by rw [hθFe]; exact hrelP i s)
    rw [hθFX, hθF] at key
    simp only [map_pow] at key
    rw [mul_add, zpow_add₀ hX, zpow_add₀ hX, zpow_mul, zpow_natCast]
    linear_combination key

  have hgs : (gamSer 0 un : F⟦X⟧) ≠ 0 := by
    refine mul_ne_zero X_ne_zero (fun h => ?_)
    have := congrArg PowerSeries.constantCoeff h
    simp at this
  have hgc : MvPowerSeries.constantCoeff (gamSer 0 un : F⟦X⟧) = 0 := by
    show PowerSeries.constantCoeff (gamSer 0 un : F⟦X⟧) = 0
    simp [gamSer]
  let θG : F⟦X⟧ →+* F⟦X⟧ := (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero hgc)).toRingHom
  have hθG : ∀ y, θG y = gam0 0 un y := fun y => by simp [θG, gam0, PowerSeries.coe_substAlgHom]
  have hθGX : θG X = gamSer 0 un := by
    rw [hθG, gam0, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hgc)]
  have hrelΓ : ∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gam0 0 un (w i s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gamSer 0 un : PowerSeries F) : LaurentSeries F) ^ (k i s + m i s) * ((1 + PowerSeries.X * Dψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ (k i s + m i s) := by
    intro i s
    have hdG := sub_coord_smul_col_mem F n (V i (rs s).castSucc) (g i) (gamV un (D i) (fun c => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s))) (pos s)
      (fun a ha hne => hg' i _ a (hlow s a ha (fun h => hne (by rw [← hentG]; exact hbtG i h))))
    rw [← hentG] at hdG
    have hθGe : ⇑θG = gam0 0 un := funext hθG
    have key := GlobalTheory.T.diagonal_entry_of_semilinear_mod_subspace_alt F n θG (1 + (X : F⟦X⟧) • D i) (V i (rs s).castSucc) (V i (rs s).castSucc)
      (fun c => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s)) (e i s)
      (fun c => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s)) (e i s)
      (w i s) (w i s) (k i s) (k i s) (m i s) (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i) (pos s) (pos s))
      (((gamSer 0 un : F⟦X⟧) : K) ^ m i s * ((1 + X * Dψ s i : F⟦X⟧) : K))
      (by rw [hθGX]; exact hcoe _ hgs)
      (fun y hy => by rw [hθGe]; exact hgam i _ y hy) (hc' i s) (hc' i s) (hline i s).1
      (by rw [hθGe]; exact hdG) (by rw [hθGe]; exact hrelG i s)
    rw [hθGX, hθG] at key
    rw [zpow_add₀ (hcoe _ hgs), zpow_add₀ hX]
    linear_combination key
  exact ⟨g, b, pos, w, fun i s => k i s + m i s, ⟨hinj, hsing⟩, hbtP, hbtG, hrelF, hrelΓ⟩

end GlobalTheory.WachBlock

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasesBlockTriangularOfReducedEtaleFiltratStatement
open NumberField GlobalTheory.ExpFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedBases_blockTriangular_of_reducedEtaleFiltration : ∀ (ι : Type) (σ : Equiv.Perm ι) (l n t : ℕ) (F : Type) [Field F] (un : PowerSeries F) (P D : ι → Matrix (Fin n) (Fin n) (PowerSeries F)) (Pψ Dψ : Fin t → ι → PowerSeries F), 0 < l → Nonempty ι → GlobalTheory.WachBlock.RedFilt σ l un P D Pψ Dψ → ∃ (g : ι → (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) (b : Fin n → ℕ) (pos : Fin t → Fin n) (w : ι → Fin t → (PowerSeries F)ˣ) (kap : ι → Fin t → ℤ), (Function.Injective pos ∧ ∀ s j, b j = b (pos s) → j = pos s) ∧ (∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i)).BlockTriangular b) ∧ (∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i)).BlockTriangular b) ∧ (∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.frob0 l (w (σ i) s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ ((l : ℤ) * kap (σ i) s) * ((Pψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ kap i s) ∧ (∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gam0 0 un (w i s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gamSer 0 un : PowerSeries F) : LaurentSeries F) ^ kap i s * ((1 + PowerSeries.X * Dψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ kap i s) := by
  first | exact @GlobalTheory.WachBlock.adapted_bases_of_redFilt | exact GlobalTheory.WachBlock.adapted_bases_of_redFilt | (intros; apply GlobalTheory.WachBlock.adapted_bases_of_redFilt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineBlockLatticesOverPowerSeriesRing
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.WachBlock

theorem wach_inputs : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → BlockPair E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (Wl : Formalism.CohomologicalDescent.FrobeniusPeriodChange.WLat (E →+* PadicAlgCl l) t n O' F) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (kap : (E →+* PadicAlgCl l) → Fin t → ℤ) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), Formalism.CohomologicalDescent.FrobeniusPeriodChange.NInputs Wl σ l h u c J (fun i s => bot i + ((s : ℕ) : ℤ)) kap I ζ em jj := by
  intro hBS E Ω _ _ _ _ _ _ l _ hl2 hdisc σ hσ n t h J bot hJ hbot hBP
  obtain ⟨O', F, L', i1, i2, i3, i4, i5, i6, I, i7, red, un, N, Npsi, u, c, ζ, em, jj, hU, hR, hN, hψ, hF⟩ :=
    GlobalTheory.T.wachLattices_rankOne_models_reducedFiltration hBS E Ω l hl2 hdisc σ hσ n t h J bot hJ hbot (GlobalTheory.T.integralCrystallineBlockData_of_reductionPair E Ω l n t J bot hBP)
  obtain ⟨g, b, pos, w, kap, hpos, hP, hG, hPd, hGd⟩ :=
    GlobalTheory.T.adaptedBases_blockTriangular_of_reducedEtaleFiltration _ σ l n t F _ _ _ _ _ (Fact.out : l.Prime).pos inferInstance hF
  exact ⟨O', F, L', i1, i2, i3, i4, i5, i6, I, i7, ⟨red, un, N, Npsi, g, b, pos, w⟩, u, c, kap, ζ, em, jj,
    ⟨hU, hJ, hbot, hpos, hP, hG, hPd, hGd⟩, hR, hN, hψ⟩

end GlobalTheory.WachBlock

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineBlockLatticesOverPowerSeriesRingStatement
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_block_lattices_over_power_series_ring : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → BlockPair E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (Wl : Formalism.CohomologicalDescent.FrobeniusPeriodChange.WLat (E →+* PadicAlgCl l) t n O' F) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (kap : (E →+* PadicAlgCl l) → Fin t → ℤ) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), Formalism.CohomologicalDescent.FrobeniusPeriodChange.NInputs Wl σ l h u c J (fun i s => bot i + ((s : ℕ) : ℤ)) kap I ζ em jj := by
  first | exact @GlobalTheory.WachBlock.wach_inputs | exact GlobalTheory.WachBlock.wach_inputs | (intros; apply GlobalTheory.WachBlock.wach_inputs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithFrobeniusEmbeddingPermCmConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithFrobeniusEmbeddingPermCmConj
open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.FrobEmb

theorem norm_le_one_of_isIntegral {C : Type*} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

def compPerm {E C : Type} [Field E] [Field C] (f : C ≃+* C) : Equiv.Perm (E →+* C) where
  toFun τ := f.toRingHom.comp τ
  invFun τ := f.symm.toRingHom.comp τ
  left_inv τ := by ext x; simp
  right_inv τ := by ext x; simp

theorem exists_frobPerm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime], ¬ (l : ℤ) ∣ NumberField.discr E →
    ∃ σ : Equiv.Perm (E →+* PadicAlgCl l), IsFrobPerm σ ∧ ∀ τ, σ (cj τ) = cj (σ τ) := by
  intro E _ _ _ l _ _
  obtain ⟨Fr, hFr⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_isFrob (p := l) (K := ReciprocityTheory.DiscreteGroups.LocalClassField.Q0 l) ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_base_field
  refine ⟨compPerm Fr.toRingEquiv, ?_, fun τ => rfl⟩
  intro τ x
  have hx : ‖τ (x : E)‖ ≤ 1 := norm_le_one_of_isIntegral (map_isIntegral_int τ x.isIntegral_coe)
  have h := hFr (τ (x : E)) hx
  rw [ReciprocityTheory.DiscreteGroups.LocalClassField.residue_cardinality_base_field] at h
  exact h

end GlobalTheory.FrobEmb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithFrobeniusEmbeddingPermCmConjStatement
open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arithFrobenius_embedding_perm_cmConj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime], ¬ (l : ℤ) ∣ NumberField.discr E → ∃ σ : Equiv.Perm (E →+* PadicAlgCl l), IsFrobPerm σ ∧ ∀ τ, σ (cj τ) = cj (σ τ) := by
  first | exact @GlobalTheory.FrobEmb.exists_frobPerm | exact GlobalTheory.FrobEmb.exists_frobPerm | (intros; apply GlobalTheory.FrobEmb.exists_frobPerm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineLatticeLinkOfBlockData
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpLink

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

theorem cj_cj (τ : E →+* PadicAlgCl l) : cj (cj τ) = τ := by
  ext x; simp [cj, IsCMField.complexConj_apply_apply]

theorem cj_injective : Function.Injective (cj : (E →+* PadicAlgCl l) → (E →+* PadicAlgCl l)) := fun a b h => by
  rw [← cj_cj a, h, cj_cj]


open Classical in
def glue {ι X : Type} [Inhabited X] (inc : ι → (E →+* PadicAlgCl l)) (f g : ι → X) (i : E →+* PadicAlgCl l) : X :=
  if h : ∃ τ, inc τ = i then f h.choose else if h' : ∃ τ, cj (inc τ) = i then g h'.choose else default

theorem glue_inc {ι X : Type} [Inhabited X] {inc : ι → (E →+* PadicAlgCl l)} (hH : IsHalf inc) (f g : ι → X) (τ : ι) :
    glue inc f g (inc τ) = f τ := by
  have h : ∃ τ', inc τ' = inc τ := ⟨τ, rfl⟩
  rw [glue, dite_eq_left h]
  exact congrArg f (hH.1 h.choose_spec)

theorem glue_cj {ι X : Type} [Inhabited X] {inc : ι → (E →+* PadicAlgCl l)} (hH : IsHalf inc) (f g : ι → X) (τ : ι) :
    glue inc f g (cj (inc τ)) = g τ := by
  have h : ¬ ∃ τ', inc τ' = cj (inc τ) := fun ⟨τ', h'⟩ => hH.2.1 τ τ' h'.symm
  have h' : ∃ τ', cj (inc τ') = cj (inc τ) := ⟨τ, rfl⟩
  rw [glue, dite_eq_right h, dite_eq_left h']
  exact congrArg g (hH.1 (cj_injective h'.choose_spec))

def labels {ι : Type} (inc : ι → (E →+* PadicAlgCl l)) (P : Par) (W : Wts ι) (mu : ι → ℕ → ℕ) :
    Formalism.CohomologicalDescent.WorkedExample.Labels (E →+* PadicAlgCl l) P.Nr where
  cc := cj
  Φ := Set.range inc
  U := glue inc (fun τ a => W.U P τ (a : ℕ)) (fun τ a => (h0 P : ℤ) - W.U P τ ((Fin.rev a : Fin P.Nr) : ℕ))
  U' := glue inc (fun τ a => Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ) (a : ℕ))
    (fun τ a => (h0 P : ℤ) - Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ) ((Fin.rev a : Fin P.Nr) : ℕ))
  bot := glue inc (fun τ => W.bot P τ) (fun τ => (h0 P : ℤ) - (W.bot P τ + (P.t : ℤ) - 1))

theorem U_block {ι : Type} {P : Par} {W : Wts ι} (hOk : W.Ok P) (τ : ι) (s : ℕ) (hs : s < P.t) :
    W.U P τ (kc P + W.j τ + P.t - 1 - s) = W.bot P τ + (s : ℤ) := by
  have h1 := hOk.block τ (kc P + W.j τ + P.t - 1 - s) (by omega) (by omega)
  have h2 := hOk.block τ (kc P + W.j τ + P.t - 1) (by omega) (by omega)
  simp only [Wts.bot, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN, h1, h2]
  omega

theorem latticeLink_of_blockFor : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (ι : Type) (inc : ι → (E →+* PadicAlgCl l)), IsHalf inc → ∃ (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool), ∀ (P : Par) (W : Wts ι), P.Hyp → W.Ok P → (∀ τ a, a < P.Nr → 0 ≤ W.U P τ a ∧ W.U P τ a ≤ (h0 P : ℤ)) → ∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  intro hBS E Ω _ _ _ _ _ _ l _ hl2 hdisc ι inc hH
  obtain ⟨σ, hσF, hσc⟩ := GlobalTheory.T.exists_arithFrobenius_embedding_perm_cmConj E l hdisc
  choose hf hb using hH.2.2
  classical
  set fr : ℕ → ι → ι := fun _ τ => hf (σ (inc τ)) with hfr
  set cjj : ℕ → ι → Bool := fun _ τ => decide (σ (inc τ) ≠ inc (hf (σ (inc τ)))) with hcjj
  refine ⟨fr, cjj, ?_⟩
  intro P W hP hOk hbox mu hLk hBF τ
  obtain ⟨ep, J, bot, hep, hBP, hJ⟩ := hBF
  have hall : ∀ i, ∃ τ', i = ep (inc τ') ∨ i = ep (cj (inc τ')) := by
    intro i
    rcases hep with rfl | rfl
    · rcases hb i with h | h
      · exact ⟨hf i, Or.inl h⟩
      · exact ⟨hf i, Or.inr h⟩
    · rcases hb i with h | h
      · exact ⟨hf i, Or.inr (by rw [cj_cj]; exact h)⟩
      · exact ⟨hf i, Or.inl h⟩
  have hUN : ∀ τ' (a : Fin P.Nr), 0 ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') a ∧
      Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') a ≤ (h0 P : ℤ) := by
    intro τ' a
    have h1 := ((hLk τ').2.2.1 a).2
    have ha := a.2
    have h2 := hbox τ' 0 (by omega)
    simp only [Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN] at h2 ⊢
    constructor <;> omega
  have hJb : ∀ i a, 0 ≤ J i a ∧ J i a ≤ (h0 P : ℤ) := by
    intro i a
    obtain ⟨τ', h | h⟩ := hall i <;> subst h
    · rw [((hJ τ').1 a).1]; exact hUN τ' a
    · rw [((hJ τ').1 a).2]
      have := hUN τ' (Fin.rev a)
      constructor <;> linarith [this.1, this.2]
  have hbb : ∀ i (s : Fin P.t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ (h0 P : ℤ) := by
    intro i s
    have hs := s.2
    have hr := hOk.what₂
    obtain ⟨τ', h | h⟩ := hall i <;> subst h
    · rw [(hJ τ').2.1]
      have e := U_block hOk τ' s hs
      have b := hbox τ' (kc P + W.j τ' + P.t - 1 - s) (by have := hr τ'; omega)
      rw [e] at b; exact b
    · rw [(hJ τ').2.2]
      have e := U_block hOk τ' (P.t - 1 - s) (by omega)
      have b := hbox τ' (kc P + W.j τ' + P.t - 1 - (P.t - 1 - s)) (by have := hr τ'; omega)
      rw [e] at b
      constructor <;> omega
  obtain ⟨O', F, L', _, _, _, _, _, _, I, _, Wl, u, c, kap, ζ, em, jj, hN⟩ :=
    GlobalTheory.T.crystalline_block_lattices_over_power_series_ring hBS E Ω l hl2 hdisc σ hσF P.Nr P.t (h0 P) J bot hJb hbb hBP
  have hn : kc P + (reFr W fr cjj).j τ + P.t + (reFr W fr cjj).q τ = P.Nr := hOk.what₂ τ
  unfold LatticeLink
  rw [hn]
  refine ⟨E →+* PadicAlgCl l, inferInstance, σ, ‹_›, O', F, L', ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, I, ‹_›, Wl, u, c,
    labels inc P W mu, fun _ => 1 - (P.Nr : ℤ), ep, J, bot, kap, ζ, em, jj, inc, ?_⟩
  refine ⟨?_, ?_, ?_, hN, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨cj_cj, fun i => hσc i, ?_, ?_, ?_, ?_⟩
    · intro i
      rcases hb i with h | h
      · exact Or.inl ⟨hf i, h.symm⟩
      · exact Or.inr ⟨hf i, by show inc (hf i) = cj i; rw [← cj_cj (inc (hf i)), ← h]⟩
    · intro i a
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH, glue_cj hH]
      · simp only [labels, glue_inc hH, glue_cj hH, cj_cj, Fin.rev_rev, sub_sub_cancel]
    · intro i a
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH, glue_cj hH]
      · simp only [labels, glue_inc hH, glue_cj hH, cj_cj, Fin.rev_rev, sub_sub_cancel]
    · intro i
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH, glue_cj hH]
      · simp only [labels, glue_inc hH, glue_cj hH, cj_cj]; ring
  ·
    rintro _ ⟨τ', rfl⟩
    have hr := hOk.what₂ τ'
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      have hab' : (a : ℕ) < b := hab
      have h1 := hOk.anti τ' a b hab'.le b.2
      simp only [labels, glue_inc hH, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN]
      omega
    · intro a b hab
      have hab' : (a : ℕ) < b := hab
      have h1 := (hLk τ').1 hab.le
      simp only [Formalism.CohomologicalDescent.LD.res] at h1
      simp only [labels, glue_inc hH, Formalism.CohomologicalDescent.UnitNormBounds.UN]
      omega
    · intro s
      have hs := s.2
      refine ⟨⟨kc P + W.j τ' + P.t - 1 - s, by omega⟩, ?_⟩
      simp only [labels, glue_inc hH]
      exact U_block hOk τ' s hs
    · have hp := congrArg (Polynomial.map (ZMod.castHom (dvd_refl l) F)) (hLk τ').2.2.2
      simp only [Polynomial.map_prod, Polynomial.map_add (f := _), Polynomial.map_X, Polynomial.map_C] at hp
      simp only [map_intCast] at hp
      have e1 : ∀ a : Fin P.Nr, (((W.U P τ' (a : ℕ) + (1 - (P.Nr : ℤ)) : ℤ) : F)) =
          ((((W.lam τ' a : ℤ) - ((a : ℕ) : ℤ) : ℤ)) : F) := by
        intro a; congr 1; simp only [Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN]; ring
      have e2 : ∀ a : Fin P.Nr, (((Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') (a : ℕ) + (1 - (P.Nr : ℤ)) : ℤ) : F)) =
          ((((mu τ' a : ℤ) - ((a : ℕ) : ℤ) : ℤ)) : F) := by
        intro a; congr 1; simp only [Formalism.CohomologicalDescent.UnitNormBounds.UN]; ring
      simp only [labels, glue_inc hH, e1, e2]
      exact hp
  ·
    refine ⟨hep, fun i => ?_, fun i => ?_⟩
    · funext a
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH]; exact ((hJ τ').1 a).1
      · simp only [labels, glue_cj hH]; exact ((hJ τ').1 a).2
    · obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH]; exact (hJ τ').2.1
      · simp only [labels, glue_cj hH]; exact (hJ τ').2.2
  · intro τ' a
    simp only [labels, glue_inc hH]
    rfl
  · intro τ'
    simp only [labels, glue_inc hH]
    rfl
  ·
    show σ (inc τ) = if decide (σ (inc τ) ≠ inc (hf (σ (inc τ)))) = true then cj (inc (hf (σ (inc τ))))
      else inc (hf (σ (inc τ)))
    by_cases h : σ (inc τ) = inc (hf (σ (inc τ)))
    · rw [decide_eq_false (not_not.mpr h), if_neg Bool.false_ne_true]; exact h
    · rcases hb (σ (inc τ)) with h' | h'
      · exact absurd h' h
      · rw [decide_eq_true h, if_pos rfl]; exact h'
  · intro a a' haa'
    obtain rfl : a = a' := Fin.ext haa'
    simp only [labels, glue_inc hH, Formalism.CohomologicalDescent.UnitNormBounds.UN, Formalism.CohomologicalDescent.LD.res]
  · have hs := (hLk τ).2.1
    have h2 : (∑ a : Fin P.Nr, (mu τ a : ℤ)) = ∑ a : Fin P.Nr, (W.lam τ a : ℤ) := by exact_mod_cast hs
    simp only [labels, glue_inc hH, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    linarith [h2]

end GlobalTheory.ExpLink
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineLatticeLinkOfBlockDataStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLatticeLink_of_blockData : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (ι : Type) (inc : ι → (E →+* PadicAlgCl l)), IsHalf inc → ∃ (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool), ∀ (P : Par) (W : Wts ι), P.Hyp → W.Ok P → (∀ τ a, a < P.Nr → 0 ≤ W.U P τ a ∧ W.U P τ a ≤ (h0 P : ℤ)) → ∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  first | exact @GlobalTheory.ExpLink.latticeLink_of_blockFor | exact GlobalTheory.ExpLink.latticeLink_of_blockFor | (intros; apply GlobalTheory.ExpLink.latticeLink_of_blockFor <;> assumption)
end
