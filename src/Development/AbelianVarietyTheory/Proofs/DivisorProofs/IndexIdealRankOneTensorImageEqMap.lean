module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedPiTensor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Dets
set_option autoImplicit false

noncomputable section

open NumberField

namespace GlobalTheory.IdxTensor

def dets (F : Type) [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F)) : Submodule (𝓞 F) F :=
  Submodule.span (𝓞 F) {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ L) ∧ d = (Matrix.of y).det}

end GlobalTheory.IdxTensor

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeterminantIndexIdealMapInjectiveEqColon
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeterminantIndexIdealMapInjectiveEqColon
set_option autoImplicit false
noncomputable section
open NumberField

namespace GlobalTheory.IdxMap

theorem dets_eq_detSpan (F : Type) [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F)) :
    GlobalTheory.IdxTensor.dets F p L = GlobalTheory.BetaEx.detSpan L := by
  unfold GlobalTheory.IdxTensor.dets GlobalTheory.BetaEx.detSpan
  congr 1
  ext d
  rw [GlobalTheory.BetaEx.mem_detSet]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Matrix.of y, hy, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩

theorem idx_map_eq_colon_dets : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] (p : ℕ) (φ : (Fin p → F) →ₗ[F] V), Function.Injective φ →
    ∀ (L N : Submodule (𝓞 F) (Fin p → F)),
    GlobalTheory.FlatCM.idx F p (L.map (φ.restrictScalars (𝓞 F))) (N.map (φ.restrictScalars (𝓞 F))) =
      (GlobalTheory.IdxTensor.dets F p N).colon (GlobalTheory.IdxTensor.dets F p L : Set F) := by
  intro F V _ _ _ _ _ _ p φ hφ L N
  set v : Fin p → V := fun i => φ (Pi.basisFun F (Fin p) i) with hv
  have hli : LinearIndependent F v :=
    (Pi.basisFun F (Fin p)).linearIndependent.map' φ (LinearMap.ker_eq_bot.2 hφ)
  have hcoord : φ.restrictScalars (𝓞 F) = GlobalTheory.LatIndexDeg.coordMap F v := by
    refine LinearMap.ext fun x => ?_
    rw [GlobalTheory.LatIndexDeg.coordMap_apply, LinearMap.restrictScalars_apply]
    conv_lhs => rw [← (Pi.basisFun F (Fin p)).sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hv, map_sum, map_smul]
  have hω := GlobalTheory.LatIndexDeg.ιMulti_ne_zero_of_li v hli
  have hℓ : Function.Injective (GlobalTheory.LatIndexDeg.lineMap F (exteriorPower.ιMulti F p v)) :=
    fun s t e => smul_left_injective F hω e
  unfold GlobalTheory.FlatCM.idx
  rw [hcoord, GlobalTheory.LatIndexDeg.detSpan_map_coord, GlobalTheory.LatIndexDeg.detSpan_map_coord,
    GlobalTheory.LatIndexDeg.colon_map_of_injective _ hℓ, dets_eq_detSpan, dets_eq_detSpan]

end GlobalTheory.IdxMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeterminantIndexIdealMapInjectiveEqColonStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeDeterminantIndexIdeal_map_injective_eq_colon : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] (p : ℕ) (φ : (Fin p → F) →ₗ[F] V), Function.Injective φ →
    ∀ (L N : Submodule (𝓞 F) (Fin p → F)),
    GlobalTheory.FlatCM.idx F p (L.map (φ.restrictScalars (𝓞 F))) (N.map (φ.restrictScalars (𝓞 F))) =
      (GlobalTheory.IdxTensor.dets F p N).colon (GlobalTheory.IdxTensor.dets F p L : Set F) := by
  first | exact @GlobalTheory.IdxMap.idx_map_eq_colon_dets | exact GlobalTheory.IdxMap.idx_map_eq_colon_dets | (intros; apply GlobalTheory.IdxMap.idx_map_eq_colon_dets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentImagesOfRankOneLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentImagesOfRankOneLattice
open NumberField

namespace GlobalTheory

theorem linearIndependent_images_of_rankOne_lattice :
    ∀ {K : Type} [Field K] [NumberField K] {p m n : ℕ} (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (v : Fin m → K), v ≠ 0 → ∀ (𝔟 : Submodule (𝓞 K) K),
    𝔟 ≠ ⊥ → (∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v) → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K
      ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    LinearIndependent K (fun a => M a v) := by
  intro K _ _ p m n ell M v hv 𝔟 h𝔟 hell hinj hind
  obtain ⟨β, hβ, hβ0⟩ := (Submodule.ne_bot_iff 𝔟).1 h𝔟
  refine hind.linearIndependent _ (fun a => ?_) (fun a => ?_)
  · have hmem : M a (β • v) ∈ Submodule.span K
        ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) :=
      Submodule.subset_span ⟨β • v, (hell _).2 ⟨β, hβ, rfl⟩, rfl⟩
    have : M a v = β⁻¹ • M a (β • v) := by
      rw [map_smul, smul_smul, inv_mul_cancel₀ hβ0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hmem
  · intro h
    exact hv ((hinj a) (by rw [h, map_zero]))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentImagesOfRankOneLatticeStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_images_of_iSupIndep_rankOne : ∀ {K : Type} [Field K] [NumberField K] {p m n : ℕ} (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (v : Fin m → K), v ≠ 0 → ∀ (𝔟 : Submodule (𝓞 K) K),
    𝔟 ≠ ⊥ → (∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v) → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K
      ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    LinearIndependent K (fun a => M a v) := by
  first | exact @GlobalTheory.linearIndependent_images_of_rankOne_lattice | exact GlobalTheory.linearIndependent_images_of_rankOne_lattice | (intros; apply GlobalTheory.linearIndependent_images_of_rankOne_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneFgLatticeEqFractionalIdealSmulVector
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneFgLatticeEqFractionalIdealSmulVector
open NumberField

namespace GlobalTheory

theorem latRank_one_eq_ideal_smul {K : Type} [Field K] [NumberField K] {m : ℕ}
    (ell : Submodule (𝓞 K) (Fin m → K)) :
    ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → ell.FG →
    ∃ v : Fin m → K, v ≠ 0 ∧ ∃ 𝔟 : Submodule (𝓞 K) K, 𝔟.FG ∧ 𝔟 ≠ ⊥ ∧
      ∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v := by
  intro hr hfg
  unfold ReciprocityTheory.GeometryOfNumbersTheory.latRank at hr
  obtain ⟨w, hw0, hw⟩ := (finrank_eq_one_iff').mp hr
  have hvW : (w : Fin m → K) ≠ 0 := by
    intro h; exact hw0 (Subtype.ext h)
  have hmul : ∀ e ∈ ell, ∃ β : K, e = β • (w : Fin m → K) := by
    intro e he
    obtain ⟨c, hc⟩ := hw ⟨e, Submodule.subset_span he⟩
    refine ⟨c, ?_⟩
    have := congrArg Subtype.val hc
    exact this.symm
  let f : K →ₗ[𝓞 K] (Fin m → K) :=
    { toFun := fun β => β • (w : Fin m → K)
      map_add' := fun a b => add_smul a b _
      map_smul' := fun r b => by
        simp only [RingHom.id_apply]
        exact smul_assoc r b _ }
  have hf : ∀ β, f β = β • (w : Fin m → K) := fun _ => rfl
  have finj : Function.Injective f := by
    intro a b hab
    rw [hf, hf] at hab
    have : (a - b) • (w : Fin m → K) = 0 := by rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hvW
  refine ⟨w, hvW, ell.comap f, ?_, ?_, ?_⟩
  · apply Submodule.fg_of_fg_map_injective f finj
    have : (ell.comap f).map f = ell := by
      apply le_antisymm (Submodule.map_comap_le _ _)
      intro e he
      obtain ⟨β, rfl⟩ := hmul e he
      exact ⟨β, he, rfl⟩
    rw [this]; exact hfg
  · intro hbot
    apply hw0
    have hell : ell = ⊥ := by
      rw [eq_bot_iff]; intro e he
      obtain ⟨β, rfl⟩ := hmul e he
      have : β ∈ ell.comap f := he
      rw [hbot, Submodule.mem_bot] at this
      simp [this]
    have hW : Submodule.span K (ell : Set (Fin m → K)) = ⊥ := by simp [hell]
    have h0 : ∀ x ∈ Submodule.span K (ell : Set (Fin m → K)), x = 0 := by
      rw [hW]; intro x hx; exact (Submodule.mem_bot K).mp hx
    exact Subtype.ext (h0 _ w.2)
  · intro e
    constructor
    · intro he
      obtain ⟨β, rfl⟩ := hmul e he
      exact ⟨β, he, rfl⟩
    · rintro ⟨β, hβ, rfl⟩
      exact hβ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneFgLatticeEqFractionalIdealSmulVectorStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankOne_fg_lattice_eq_fractionalIdeal_smul_vector : ∀ {K : Type} [Field K] [NumberField K] {m : ℕ} (ell : Submodule (𝓞 K) (Fin m → K)),
    ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → ell.FG →
    ∃ v : Fin m → K, v ≠ 0 ∧ ∃ 𝔟 : Submodule (𝓞 K) K, 𝔟.FG ∧ 𝔟 ≠ ⊥ ∧
      ∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v := by
  first | exact @GlobalTheory.latRank_one_eq_ideal_smul | exact GlobalTheory.latRank_one_eq_ideal_smul | (intros; apply GlobalTheory.latRank_one_eq_ideal_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColonOneSpanImageEqMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColonOneSpanImageEqMap
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

open NumberField in
open scoped nonZeroDivisors in
private theorem one_mem_colon_one_smul_of_fg {E : Type} [Field E] [NumberField E]
    (A : Submodule (𝓞 E) E) (hA : A.FG) (h1 : (1 : E) ∈ A) :
    (1 : E) ∈ ((1 : Submodule (𝓞 E) E).colon (A : Set E)) • A := by
  set Af : FractionalIdeal (𝓞 E)⁰ E := ⟨A, FractionalIdeal.isFractional_of_fg hA⟩ with hAf
  have hne : Af ≠ 0 := by
    intro h
    have : (1 : E) ∈ Af := h1
    rw [h, FractionalIdeal.mem_zero_iff] at this
    exact one_ne_zero this
  have hmem : (1 : E) ∈ ((Af * Af⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
    rw [mul_inv_cancel₀ hne]; exact FractionalIdeal.one_mem_one _
  rw [FractionalIdeal.coe_mul] at hmem
  refine Submodule.mul_induction_on hmem (fun a ha x hx => ?_) (fun _ _ => add_mem)
  have hinv : ∀ y ∈ A, x * y ∈ (1 : Submodule (𝓞 E) E) := by
    intro y hy
    have := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coe.mp hx) (show y ∈ Af from hy)
    rw [inv_mul_cancel₀ hne] at this
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one] at this
    exact this
  obtain ⟨i, rfl⟩ := Submodule.mem_one.mp (by simpa using hinv 1 h1)
  have hi : i ∈ (1 : Submodule (𝓞 E) E).colon (A : Set E) := by
    rw [Submodule.mem_colon]
    intro s hs
    rw [Algebra.smul_def]
    exact hinv s hs
  rw [mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem_smul hi ha


open NumberField in
open scoped nonZeroDivisors in
theorem _root_.GlobalTheory.colon_one_span_image_eq_map {E K : Type} [Field E] [NumberField E] [Field K]
    [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K))
    (A : Submodule (𝓞 E) E) (hA : A.FG) (h1 : (1 : E) ∈ A) :
    (1 : Submodule (𝓞 K) K).colon (Submodule.span (𝓞 K) (τE '' A) : Set K) =
      ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ := by
  have key := one_mem_colon_one_smul_of_fg A hA h1
  apply le_antisymm
  · intro r hr
    rw [Submodule.mem_colon] at hr
    have hb : ∀ a ∈ A, ∃ u : 𝓞 K, (u : K) = (r : K) * τE a := by
      intro a ha
      obtain ⟨u, hu⟩ := Submodule.mem_one.mp (hr _ (Submodule.subset_span ⟨a, ha, rfl⟩))
      rw [Algebra.smul_def] at hu
      exact ⟨u, hu⟩
    have hP : ∀ x ∈ ((1 : Submodule (𝓞 E) E).colon (A : Set E)) • A,
        ∃ t ∈ ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ, (t : K) = (r : K) * τE x := by
      intro x hx
      refine Submodule.smul_induction_on
        (p := fun x => ∃ t ∈ ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ,
          (t : K) = (r : K) * τE x) hx (fun i hi a ha => ?_) ?_
      · obtain ⟨u, hu⟩ := hb a ha
        refine ⟨τ i * u, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem τ hi), ?_⟩
        rw [Algebra.smul_def, map_mul]
        change ((τ i : 𝓞 K) : K) * (u : K) = (r : K) * (τE (i : E) * τE a)
        rw [hu, hτ]
        ring
      · rintro x y ⟨t, ht, hte⟩ ⟨t', ht', hte'⟩
        refine ⟨t + t', add_mem ht ht', ?_⟩
        rw [map_add (f := _), mul_add, ← hte, ← hte']
        rfl
    obtain ⟨t, ht, hte⟩ := hP 1 key
    rw [map_one, mul_one] at hte
    have htr : t = r := by exact_mod_cast hte
    rwa [← htr]
  · rw [Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, Submodule.mem_colon]
    intro s hs
    rw [SetLike.mem_coe] at hs
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨a, ha, rfl⟩ := hs
      obtain ⟨y, hy⟩ := Submodule.mem_one.mp ((Submodule.mem_colon.mp hi) a ha)
      refine Submodule.mem_one.mpr ⟨τ y, ?_⟩
      rw [Algebra.smul_def] at hy ⊢
      change (y : E) = (i : E) * a at hy
      change ((τ y : 𝓞 K) : K) = ((τ i : 𝓞 K) : K) * τE a
      rw [← hτ, ← hτ, hy, map_mul]
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColonOneSpanImageEqMapStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colon_one_span_image_eq_map_colon : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K), (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
    ∀ (A : Submodule (𝓞 E) E), A.FG → (1 : E) ∈ A →
    (1 : Submodule (𝓞 K) K).colon (Submodule.span (𝓞 K) (τE '' A) : Set K) =
      ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ := by
  first | exact @GlobalTheory.colon_one_span_image_eq_map | exact GlobalTheory.colon_one_span_image_eq_map | (intros; apply GlobalTheory.colon_one_span_image_eq_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColonPowMulCancelFgFractional
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColonPowMulCancelFgFractional
open NumberField

namespace GlobalTheory.ColonPowCancel

theorem exists_inv {K : Type} [Field K] [NumberField K] (𝔟 : Submodule (𝓞 K) K)
    (hfg : 𝔟.FG) (h0 : 𝔟 ≠ ⊥) : ∃ 𝔠 : Submodule (𝓞 K) K, 𝔠 * 𝔟 = 1 := by
  let I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    ⟨𝔟, FractionalIdeal.isFractional_of_fg hfg⟩
  have hI : I ≠ 0 := by
    intro h
    apply h0
    have : (I : Submodule (𝓞 K) K) = ((0 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) := by rw [h]
    rw [FractionalIdeal.coe_zero] at this
    exact this
  refine ⟨((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K), ?_⟩
  have h1 : I⁻¹ * I = 1 := inv_mul_cancel₀ hI
  have h2 := congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K => (J : Submodule (𝓞 K) K)) h1
  simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one] at h2
  exact h2

theorem mem_colon_iff {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    (N A : Submodule R K) (r : R) :
    r ∈ N.colon (A : Set K) ↔ Submodule.span R {algebraMap R K r} * A ≤ N := by
  rw [Submodule.mem_colon]
  constructor
  · intro h
    rw [Submodule.mul_le]
    intro m hm a ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hm
    rw [smul_mul_assoc, ← Algebra.smul_def]
    exact N.smul_mem c (h a ha)
  · intro h a ha
    rw [Algebra.smul_def]
    exact h (Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _) ha)

theorem colon_pow_mul_cancel {K : Type} [Field K] [NumberField K] (𝔟 : Submodule (𝓞 K) K)
    (hfg : 𝔟.FG) (h0 : 𝔟 ≠ ⊥) (p : ℕ) (A N : Submodule (𝓞 K) K) :
    (𝔟 ^ p * N).colon ((𝔟 ^ p * A : Submodule (𝓞 K) K) : Set K) = N.colon (A : Set K) := by
  obtain ⟨𝔠, hc⟩ := exists_inv 𝔟 hfg h0
  have hp : 𝔠 ^ p * 𝔟 ^ p = 1 := by rw [← mul_pow, hc, one_pow]
  ext r
  rw [mem_colon_iff, mem_colon_iff, mul_left_comm]
  constructor
  · intro h
    have h' : 𝔠 ^ p * (𝔟 ^ p * (Submodule.span (𝓞 K) {algebraMap (𝓞 K) K r} * A))
        ≤ 𝔠 ^ p * (𝔟 ^ p * N) := by gcongr
    rwa [← mul_assoc, ← mul_assoc (𝔠 ^ p), hp, one_mul, one_mul] at h'
  · intro h
    gcongr

end GlobalTheory.ColonPowCancel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColonPowMulCancelFgFractionalStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colon_pow_mul_cancel_fg_fractional : ∀ {K : Type} [Field K] [NumberField K] (𝔟 : Submodule (𝓞 K) K), 𝔟.FG → 𝔟 ≠ ⊥ →
    ∀ (p : ℕ) (A N : Submodule (𝓞 K) K),
    (𝔟 ^ p * N).colon ((𝔟 ^ p * A : Submodule (𝓞 K) K) : Set K) = N.colon (A : Set K) := by
  first | exact @GlobalTheory.ColonPowCancel.colon_pow_mul_cancel | exact GlobalTheory.ColonPowCancel.colon_pow_mul_cancel | (intros; apply GlobalTheory.ColonPowCancel.colon_pow_mul_cancel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeterminantSpanSpanEqGeneratorDets
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeterminantSpanSpanEqGeneratorDets
open NumberField

namespace GlobalTheory.IdxTensor

theorem dets_span_eq {F : Type} [Field F] [NumberField F] (p : ℕ) (S : Set (Fin p → F)) :
    GlobalTheory.IdxTensor.dets F p (Submodule.span (𝓞 F) S) =
      Submodule.span (𝓞 F) {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ S) ∧ d = (Matrix.of y).det} := by
  set T : Set F := {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ S) ∧ d = (Matrix.of y).det} with hT
  apply le_antisymm
  · unfold dets
    rw [Submodule.span_le]
    rintro d ⟨y, hy, rfl⟩
    have key : ∀ s : Finset (Fin p), ∀ y : Fin p → Fin p → F,
        (∀ i, y i ∈ Submodule.span (𝓞 F) S) → (∀ i, i ∉ s → y i ∈ S) →
          (Matrix.of y).det ∈ Submodule.span (𝓞 F) T := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro y _ h
        exact Submodule.subset_span ⟨y, fun i => h i (Finset.notMem_empty i), rfl⟩
      | insert a s ha ih =>
        intro y hy hs
        have upd : ∀ v, Matrix.of (Function.update y a v) = Matrix.updateRow (Matrix.of y) a v := fun v => rfl
        have hv : ∀ v ∈ Submodule.span (𝓞 F) S,
            (Matrix.updateRow (Matrix.of y) a v).det ∈ Submodule.span (𝓞 F) T := by
          intro v hv
          induction hv using Submodule.span_induction with
          | mem x hx =>
            rw [← upd]
            apply ih
            · intro i
              by_cases h : i = a
              · subst h; simpa using Submodule.subset_span hx
              · simpa [Function.update_of_ne h] using hy i
            · intro i hi
              by_cases h : i = a
              · subst h; simpa using hx
              · simpa [Function.update_of_ne h] using hs i (by simp [h, hi])
          | zero =>
            rw [Matrix.det_eq_zero_of_row_eq_zero a (by intro j; simp)]
            exact Submodule.zero_mem _
          | add x z _ _ hx hz =>
            rw [Matrix.det_updateRow_add]
            exact Submodule.add_mem _ hx hz
          | smul r x _ hx =>
            rw [← algebraMap_smul F r x, Matrix.det_updateRow_smul, ← Algebra.smul_def]
            exact Submodule.smul_mem _ r hx
        have := hv (y a) (hy a)
        rwa [← upd, Function.update_eq_self] at this
    exact key Finset.univ y hy (by simp)
  · unfold dets
    apply Submodule.span_mono
    rintro d ⟨y, hy, rfl⟩
    exact ⟨y, fun i => Submodule.subset_span (hy i), rfl⟩

end GlobalTheory.IdxTensor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeterminantSpanSpanEqGeneratorDetsStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeDeterminantSpan_span_eq_generator_dets : ∀ {F : Type} [Field F] [NumberField F] (p : ℕ) (S : Set (Fin p → F)),
    GlobalTheory.IdxTensor.dets F p (Submodule.span (𝓞 F) S) =
      Submodule.span (𝓞 F) {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ S) ∧ d = (Matrix.of y).det} := by
  first | exact @GlobalTheory.IdxTensor.dets_span_eq | exact GlobalTheory.IdxTensor.dets_span_eq | (intros; apply GlobalTheory.IdxTensor.dets_span_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanScaledMappedRowDetsEqPowMulSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanScaledMappedRowDetsEqPowMulSpan
open NumberField

open Pointwise
namespace GlobalTheory

theorem twistDet_rows {E K : Type} [Field E] [Field K] (τE : E →+* K) {p : ℕ}
    (β : Fin p → K) (c : Fin p → Fin p → E) :
    (Matrix.of fun i => β i • fun a => τE (c i a)).det = (∏ i, β i) * τE (Matrix.of c).det := by
  have h : (Matrix.of fun i => β i • fun a => τE (c i a)) =
      Matrix.diagonal β * (Matrix.of c).map τE := by
    ext i j
    simp [Matrix.diagonal_mul]
  rw [h, Matrix.det_mul, Matrix.det_diagonal, RingHom.map_det]
  rfl

theorem pow_eq_span_prod_set {K : Type} [Field K] [NumberField K] (p : ℕ) (𝔟 : Submodule (𝓞 K) K) :
    𝔟 ^ p = Submodule.span (𝓞 K) (∏ _i ∈ (Finset.univ : Finset (Fin p)), (𝔟 : Set K)) := by
  rw [← Submodule.prod_span]
  simp [Finset.prod_const]

theorem span_twistDets_eq {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) (p : ℕ)
    (𝔟 : Submodule (𝓞 K) K) (Λ : Submodule (𝓞 E) (Fin p → E)) :
    Submodule.span (𝓞 K) {d | ∃ y : Fin p → Fin p → K,
        (∀ i, y i ∈ {x : Fin p → K | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) ∧ d = (Matrix.of y).det} =
      𝔟 ^ p * Submodule.span (𝓞 K) (τE '' GlobalTheory.IdxTensor.dets E p Λ) := by
  set S : Set K := {d | ∃ y : Fin p → Fin p → K,
        (∀ i, y i ∈ {x : Fin p → K | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) ∧ d = (Matrix.of y).det}
    with hS
  have hpow := pow_eq_span_prod_set p 𝔟
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro d ⟨y, hy, rfl⟩
    choose β hβ c hc hyc using hy
    have hy' : y = fun i => β i • fun a => τE (c i a) := funext hyc
    subst hy'
    rw [twistDet_rows]
    refine Submodule.mul_mem_mul ?_ ?_
    · rw [hpow]
      refine Submodule.subset_span ?_
      rw [Set.mem_finsetProd]
      exact ⟨β, fun {i} _ => hβ i, rfl⟩
    · exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, hc, rfl⟩, rfl⟩
  · rw [Submodule.mul_le]

    have key : ∀ c : Fin p → Fin p → E, (∀ i, c i ∈ Λ) →
        ∀ m ∈ 𝔟 ^ p, m * τE (Matrix.of c).det ∈ Submodule.span (𝓞 K) S := by
      intro c hc m hm
      rw [hpow] at hm
      induction hm using Submodule.span_induction with
      | mem x hx =>
        rw [Set.mem_finsetProd] at hx
        obtain ⟨β, hβ, rfl⟩ := hx
        refine Submodule.subset_span ⟨fun i => β i • fun a => τE (c i a), fun i => ?_, ?_⟩
        · exact ⟨β i, hβ (Finset.mem_univ i), c i, hc i, rfl⟩
        · rw [twistDet_rows]
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
      | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx
    have key2 : ∀ e ∈ GlobalTheory.IdxTensor.dets E p Λ, ∀ m ∈ 𝔟 ^ p,
        m * τE e ∈ Submodule.span (𝓞 K) S := by
      intro e he
      induction he using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨c, hc, rfl⟩ := hx
        exact key c hc
      | zero => intro m _; simp
      | add x y _ _ hx hy =>
        intro m hm; rw [map_add (f := _), mul_add]; exact add_mem (hx m hm) (hy m hm)
      | smul a x _ hx =>
        intro m hm
        rw [Algebra.smul_def, map_mul]
        have : τE (algebraMap (𝓞 E) E a) = ((τ a : 𝓞 K) : K) := hτ a
        rw [this, mul_left_comm, ← Algebra.smul_def (τ a)]
        · exact Submodule.smul_mem _ (τ a) (hx m hm)
    intro m hm n hn
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨e, he, rfl⟩ := hx
      exact key2 e he m hm
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanScaledMappedRowDetsEqPowMulSpanStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_scaled_mapped_row_dets_eq_pow_mul_span : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K), (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) → ∀ (p : ℕ)
    (𝔟 : Submodule (𝓞 K) K) (Λ : Submodule (𝓞 E) (Fin p → E)),
    Submodule.span (𝓞 K) {d | ∃ y : Fin p → Fin p → K,
        (∀ i, y i ∈ {x : Fin p → K | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) ∧ d = (Matrix.of y).det} =
      𝔟 ^ p * Submodule.span (𝓞 K) (τE '' GlobalTheory.IdxTensor.dets E p Λ) := by
  first | exact @GlobalTheory.span_twistDets_eq | exact GlobalTheory.span_twistDets_eq | (intros; apply GlobalTheory.span_twistDets_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexIdealRankOneTensorImageEqMap
set_option autoImplicit false

noncomputable section

open NumberField

namespace GlobalTheory.IdxTensor
theorem cut_idxmap : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] (p : ℕ) (φ : (Fin p → F) →ₗ[F] V), Function.Injective φ →
    ∀ (L N : Submodule (𝓞 F) (Fin p → F)),
    GlobalTheory.FlatCM.idx F p (L.map (φ.restrictScalars (𝓞 F))) (N.map (φ.restrictScalars (𝓞 F))) =
      (GlobalTheory.IdxTensor.dets F p N).colon (GlobalTheory.IdxTensor.dets F p L : Set F) := GlobalTheory.T.latticeDeterminantIndexIdeal_map_injective_eq_colon

theorem cut_detsspan : ∀ {F : Type} [Field F] [NumberField F] (p : ℕ) (S : Set (Fin p → F)),
    GlobalTheory.IdxTensor.dets F p (Submodule.span (𝓞 F) S) =
      Submodule.span (𝓞 F) {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ S) ∧ d = (Matrix.of y).det} := GlobalTheory.T.latticeDeterminantSpan_span_eq_generator_dets

theorem cut_rankone : ∀ {K : Type} [Field K] [NumberField K] {m : ℕ} (ell : Submodule (𝓞 K) (Fin m → K)),
    ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → ell.FG →
    ∃ v : Fin m → K, v ≠ 0 ∧ ∃ 𝔟 : Submodule (𝓞 K) K, 𝔟.FG ∧ 𝔟 ≠ ⊥ ∧
      ∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v := GlobalTheory.T.rankOne_fg_lattice_eq_fractionalIdeal_smul_vector

theorem cut_linindep : ∀ {K : Type} [Field K] [NumberField K] {p m n : ℕ} (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (v : Fin m → K), v ≠ 0 → ∀ (𝔟 : Submodule (𝓞 K) K),
    𝔟 ≠ ⊥ → (∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v) → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K
      ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    LinearIndependent K (fun a => M a v) := GlobalTheory.T.linearIndependent_images_of_iSupIndep_rankOne

theorem cut_cancel : ∀ {K : Type} [Field K] [NumberField K] (𝔟 : Submodule (𝓞 K) K), 𝔟.FG → 𝔟 ≠ ⊥ →
    ∀ (p : ℕ) (A N : Submodule (𝓞 K) K),
    (𝔟 ^ p * N).colon ((𝔟 ^ p * A : Submodule (𝓞 K) K) : Set K) = N.colon (A : Set K) := GlobalTheory.T.colon_pow_mul_cancel_fg_fractional

theorem cut_extend : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K), (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
    ∀ (A : Submodule (𝓞 E) E), A.FG → (1 : E) ∈ A →
    (1 : Submodule (𝓞 K) K).colon (Submodule.span (𝓞 K) (τE '' A) : Set K) =
      ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ := GlobalTheory.T.colon_one_span_image_eq_map_colon

theorem cut_twistgens : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K), (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) → ∀ (p : ℕ)
    (𝔟 : Submodule (𝓞 K) K) (Λ : Submodule (𝓞 E) (Fin p → E)),
    Submodule.span (𝓞 K) {d | ∃ y : Fin p → Fin p → K,
        (∀ i, y i ∈ {x : Fin p → K | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) ∧ d = (Matrix.of y).det} =
      𝔟 ^ p * Submodule.span (𝓞 K) (τE '' GlobalTheory.IdxTensor.dets E p Λ) := GlobalTheory.T.span_scaled_mapped_row_dets_eq_pow_mul_span

theorem span_image_one {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) :
    Submodule.span (𝓞 K) (τE '' (1 : Submodule (𝓞 E) E)) = 1 := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.mem_one.1 hy
    exact Submodule.mem_one.2 ⟨τ z, (hτ z).symm⟩
  · rw [Submodule.one_le]
    apply Submodule.subset_span
    exact ⟨1, Submodule.mem_one.2 ⟨1, map_one _⟩, map_one τE⟩

theorem one_mem_dets {F : Type} [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F))
    (h : ∀ a, (Pi.single a (1 : F) : Fin p → F) ∈ L) : (1 : F) ∈ dets F p L := by
  unfold dets
  apply Submodule.subset_span
  refine ⟨fun a => Pi.single a 1, h, ?_⟩
  have hI : Matrix.of (fun a : Fin p => (Pi.single a (1 : F) : Fin p → F)) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Pi.single_apply, Matrix.one_apply, hij, Ne.symm hij]
  rw [hI, Matrix.det_one]

theorem dets_std {F : Type} [Field F] [NumberField F] (p : ℕ) :
    dets F p (Submodule.span (𝓞 F) (Set.range fun a => (Pi.single a (1 : F) : Fin p → F))) = 1 := by
  rw [cut_detsspan]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro d ⟨y, hy, rfl⟩
    choose f hf using fun i => Set.mem_range.1 (hy i)
    have hM : Matrix.of y =
        (Matrix.of fun i j => (Pi.single (f i) (1 : 𝓞 F) : Fin p → 𝓞 F) j).map (algebraMap (𝓞 F) F) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.map_apply]
      rw [← hf i]
      by_cases hij : j = f i
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    rw [hM]
    exact Submodule.mem_one.2 ⟨_, RingHom.map_det _ _⟩
  · rw [Submodule.one_le]
    apply Submodule.subset_span
    refine ⟨fun a => Pi.single a 1, fun i => ⟨i, rfl⟩, ?_⟩
    have hI : Matrix.of (fun a : Fin p => (Pi.single a (1 : F) : Fin p → F)) = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, Matrix.one_apply, hij, Ne.symm hij]
    rw [hI, Matrix.det_one]

theorem big_eq_map {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (τE : E →+* K) {p m n : ℕ}
    (ell : Submodule (𝓞 K) (Fin m → K)) (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K)))
    (Λ : Submodule (𝓞 E) (Fin p → E)) (v : Fin m → K) (𝔟 : Submodule (𝓞 K) K)
    (hell : ∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v) :
    Submodule.span (𝓞 K) {w | ∃ c ∈ Λ, ∃ e ∈ ell, w = ∑ a, τE (c a) • M a e} =
      (Submodule.span (𝓞 K) {x | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}).map
        ((Fintype.linearCombination K (fun a => M a v)).restrictScalars (𝓞 K)) := by
  rw [Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨c, hc, e, he, rfl⟩
    obtain ⟨β, hβ, rfl⟩ := (hell e).1 he
    refine ⟨β • fun a => τE (c a), ⟨β, hβ, c, hc, rfl⟩, ?_⟩
    rw [LinearMap.coe_restrictScalars, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, map_smul, smul_smul, smul_eq_mul, mul_comm]
  · rintro ⟨x, ⟨β, hβ, c, hc, rfl⟩, rfl⟩
    refine ⟨c, hc, β • v, (hell _).2 ⟨β, hβ, rfl⟩, ?_⟩
    rw [LinearMap.coe_restrictScalars, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, map_smul, smul_smul, smul_eq_mul, mul_comm]

private lemma sum_single_smul_eq_apply {E K : Type} [Field E] [Field K] (τE : E →+* K) {p m n : ℕ}
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (b : Fin p) (e : Fin m → K) :
    ∑ a, τE ((Pi.single b (1 : E) : Fin p → E) a) • M a e = M b e := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ hab
    simp [Pi.single_apply, hab]
  · simp

theorem small_eq_big_std {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) {p m n : ℕ}
    (ell : Submodule (𝓞 K) (Fin m → K)) (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) :
    (⨆ a, ell.map ((M a).restrictScalars (𝓞 K))) =
      Submodule.span (𝓞 K) {w | ∃ c ∈ Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)),
        ∃ e ∈ ell, w = ∑ a, τE (c a) • M a e} := by
  apply le_antisymm
  · refine iSup_le fun b => ?_
    rintro w ⟨e, he, rfl⟩
    exact Submodule.subset_span
      ⟨Pi.single b 1, Submodule.subset_span ⟨b, rfl⟩, e, he, (sum_single_smul_eq_apply τE M b e).symm⟩
  · rw [Submodule.span_le]
    rintro w ⟨c, hc, e, he, rfl⟩
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      beta_reduce
      rw [sum_single_smul_eq_apply τE M b e]
      exact Submodule.mem_iSup_of_mem b ⟨e, he, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]
      exact add_mem hx hy
    | smul r x _ hx =>
      have key : ∀ a, τE ((r • x) a) • M a e = τ r • (τE (x a) • M a e) := by
        intro a
        rw [Pi.smul_apply, Algebra.smul_def r (x a), map_mul, mul_smul, ← algebraMap_smul K (τ r)]
        congr 1
        exact hτ r
      rw [Finset.sum_congr rfl (fun a _ => key a), ← Finset.smul_sum]
      exact Submodule.smul_mem _ _ hx

theorem dets_fg {F : Type} [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F)) (h : L.FG) :
    (dets F p L).FG := by
  obtain ⟨S, rfl⟩ := h
  rw [cut_detsspan]
  apply Submodule.fg_span
  refine ((Set.Finite.pi (fun _ : Fin p => S.finite_toSet)).image
    (fun y : Fin p → Fin p → F => (Matrix.of y).det)).subset ?_
  rintro d ⟨y, hy, rfl⟩
  exact ⟨y, fun i _ => hy i, rfl⟩

theorem dets_twist {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) (p : ℕ)
    (𝔟 : Submodule (𝓞 K) K) (Λ : Submodule (𝓞 E) (Fin p → E)) :
    dets K p (Submodule.span (𝓞 K) {x | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) =
      𝔟 ^ p * Submodule.span (𝓞 K) (τE '' dets E p Λ) := by
  rw [cut_detsspan]
  exact cut_twistgens τ τE hτ p 𝔟 Λ

theorem idx_image_eq_map : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K),
    (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) → ∀ (p m n : ℕ) (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (Λ : Submodule (𝓞 E) (Fin p → E)),
    ell.FG → ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    Λ.FG → (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) →
    GlobalTheory.FlatCM.idx K p (Submodule.span (𝓞 K) {w | ∃ c ∈ Λ, ∃ e ∈ ell, w = ∑ a, τE (c a) • M a e})
                 (⨆ a, ell.map ((M a).restrictScalars (𝓞 K))) =
      (GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)))).map τ := by
  intro E K _ _ _ _ τ τE hτ p m n ell M Λ hfg hrk hinj hind hΛfg hΛ
  obtain ⟨v, hv, 𝔟, h𝔟fg, h𝔟, hell⟩ := cut_rankone ell hrk hfg
  have hφ : Function.Injective (Fintype.linearCombination K (fun a => M a v)) :=
    (cut_linindep ell M v hv 𝔟 h𝔟 hell hinj hind).fintypeLinearCombination_injective
  have hsing : ∀ a, (Pi.single a (1 : E) : Fin p → E) ∈ Λ := by
    intro a
    have h1 := hΛ (Pi.single a 1)
    convert h1 using 1
    funext b
    by_cases hab : b = a
    · subst hab; simp
    · simp [Pi.single_apply, hab]
  have hD1 : (1 : E) ∈ GlobalTheory.IdxTensor.dets E p Λ := one_mem_dets p Λ hsing
  have hDfg : (GlobalTheory.IdxTensor.dets E p Λ).FG := dets_fg p Λ hΛfg
  have hR := cut_idxmap (V := Fin p → E) p (LinearMap.id) Function.injective_id Λ
    (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)))
  have hmapid : ∀ L : Submodule (𝓞 E) (Fin p → E),
      L.map ((LinearMap.id : (Fin p → E) →ₗ[E] (Fin p → E)).restrictScalars (𝓞 E)) = L := by
    intro L
    ext x
    simp
  rw [hmapid, hmapid] at hR
  rw [hR, small_eq_big_std τ τE hτ ell M, big_eq_map τE ell M Λ v 𝔟 hell, big_eq_map τE ell M _ v 𝔟 hell,
    cut_idxmap p _ hφ, dets_twist τ τE hτ, dets_twist τ τE hτ, dets_std, span_image_one τ τE hτ,
    cut_cancel 𝔟 h𝔟fg h𝔟 p _ 1]
  exact cut_extend τ τE hτ _ hDfg hD1

end GlobalTheory.IdxTensor

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexIdealRankOneTensorImageEqMapStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexIdeal_rankOne_tensor_image_eq_map : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K),
    (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) → ∀ (p m n : ℕ) (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (Λ : Submodule (𝓞 E) (Fin p → E)),
    ell.FG → ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    Λ.FG → (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) →
    GlobalTheory.FlatCM.idx K p (Submodule.span (𝓞 K) {w | ∃ c ∈ Λ, ∃ e ∈ ell, w = ∑ a, τE (c a) • M a e})
                 (⨆ a, ell.map ((M a).restrictScalars (𝓞 K))) =
      (GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)))).map τ := by
  first | exact @GlobalTheory.IdxTensor.idx_image_eq_map | exact GlobalTheory.IdxTensor.idx_image_eq_map | (intros; apply GlobalTheory.IdxTensor.idx_image_eq_map <;> assumption)
end
