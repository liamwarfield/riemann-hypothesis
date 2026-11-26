module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameOnto
open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mem_unipOn {n : ℕ} {A B : Submodule E (Fin n → E)} (hBA : B ≤ A)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (h1 : ∀ v ∈ A, g v - v ∈ B) (h2 : ∀ v ∈ A, g⁻¹ v - v ∈ B) :
    g ∈ unipOn A B := by
  refine ⟨fun v => ⟨fun hv => ?_, fun hv => ?_⟩, h1⟩
  · have h3 := A.add_mem (hBA (h2 _ hv)) hv
    have h4 : g⁻¹ (g v) = v := g.symm_apply_apply v
    rwa [h4, sub_add_cancel] at h3
  · simpa using A.add_mem (hBA (h1 _ hv)) hv

theorem spanTo_mono (g : Fin (r + 1) → S.V) {a b : ℕ} (h : a ≤ b) : S.spanTo g a ≤ S.spanTo g b :=
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)

theorem mem_spanTo (g : Fin (r + 1) → S.V) {i : Fin (r + 1)} {a : ℕ} (h : (i : ℕ) < a) :
    g i ∈ S.spanTo g a := Submodule.subset_span ⟨i, h, rfl⟩

theorem hf_spanTo (g : Fin (r + 1) → S.V) {a : ℕ} {v w : S.V} (hv : v ∈ S.spanTo g a)
    (h : ∀ i : Fin (r + 1), (i : ℕ) < a → hf L S.Hm (g i) w = 0) : hf L S.Hm v w = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; exact h i hi
  | zero => simp [hf]
  | add x y _ _ hx hy => rw [hf_add_l, hx, hy, add_zero]
  | smul c x _ hx => rw [hf_smul_l, hx, mul_zero]

theorem coords (g : Fin (r + 1) → S.V) {a : ℕ} {v : S.V} (hv : v ∈ S.spanTo g a) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), a ≤ (i : ℕ) → c i = 0) ∧ v = ∑ i, c i • g i := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨Pi.single i 1, fun j hj => ?_, ?_⟩
    · have hi' : (i : ℕ) < a := hi
      rw [Pi.single_eq_of_ne]
      rintro rfl
      omega
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨c + d, fun i hi => by simp [hc i hi, hd i hi], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul t x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨t • c, fun i hi => by simp [hc i hi], by simp [Finset.smul_sum, smul_smul]⟩

variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (T : Fˣ)
  (gram : ∀ a b, hf L S.Hm (g a) (g b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
  (dual : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)

include gram in
theorem mem_perp (j : Fin (r + 1)) : g j ∈ perp L S.Hm (S.spanTo g r) := by
  intro y hy
  rw [← hf_cj L S.herm.1, hf_spanTo S g hy, map_zero]
  intro i hi
  rw [gram, if_neg]
  rintro ⟨rfl, -⟩
  simp at hi

include gram in
theorem spanTo_le_perp : S.spanTo g r ≤ perp L S.Hm (S.spanTo g r) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, -, rfl⟩
  exact mem_perp S g T gram i


include gram in
theorem exists_matrix (n : S.GLV) (hn : n ∈ S.Nof g) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, n (g j) = ∑ i, s i j • g i := by
  have key : ∀ j : Fin (r + 1), n (g j) - g j ∈ S.spanTo g j := by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · exact hn.2.2 _ (mem_perp S g T gram _)
    · exact (Subgroup.mem_iInf.1 hn.1.2 j).2 _ (mem_spanTo S g (by simp))
  choose c hc hc' using fun j => coords S g (key j)
  refine ⟨fun i j => c j i + if i = j then 1 else 0, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · simp [hc j i hij.le, hij.ne']
  · simp [hc i i le_rfl]
  · simp [add_smul, Finset.sum_add_distrib, ← hc' j]

include gram dual in
theorem exists_dual (j : Fin (r + 1)) : ∃ u : S.V, ∀ i, hf L S.Hm (g i) u = if i = j then 1 else 0 := by
  refine Fin.lastCases ?_ (fun j => ⟨gs j, fun i => dual i j⟩) j
  refine ⟨algebraMap F E (-(T : F)⁻¹) • g (Fin.last r), fun i => ?_⟩
  rw [hf_smul_r, gram, AlgEquiv.commutes]
  by_cases h : i = Fin.last r
  · simp [h, ← map_mul]
  · simp [h]


include gram dual in
theorem exists_step [IsNonarchimedeanLocalField F] [CharZero F] (j : Fin (r + 1)) (x : S.V)
    (hx : x ∈ S.spanTo g j) :
    ∃ n ∈ S.Nof g, n (g j) = g j + x ∧ (∀ i, i ≠ j → n (g i) = g i) ∧
      ∀ v ∈ S.spanTo g j, n v = v := by
  obtain ⟨u, hu⟩ := exists_dual S g gs T gram dual j
  have hjr : (j : ℕ) ≤ r := Nat.lt_succ_iff.1 j.2
  have hxX : x ∈ S.spanTo g r := spanTo_mono S g hjr hx
  have hlow : ∀ v ∈ S.spanTo g j, hf L S.Hm v u = 0 := fun v hv =>
    hf_spanTo S g hv fun i hi => by
      rw [hu, if_neg]
      rintro rfl
      omega
  have hux : hf L S.Hm u x = 0 := by rw [← hf_cj L S.herm.1, hlow x hx, map_zero]
  have hs : algebraMap F E 2⁻¹ * hf L S.Hm u u + L.cj (algebraMap F E 2⁻¹ * hf L S.Hm u u) =
      hf L S.Hm u u := by
    rw [map_mul, AlgEquiv.commutes, hf_cj L S.herm.1, ← add_mul, ← map_add (f := _)]
    norm_num
  obtain ⟨n, hn, h1, h2⟩ := eichler_isometry L S.Hm S.herm x u _
    (spanTo_le_perp S g T gram hxX x hxX) hux hs
  have e1 : ∀ v ∈ perp L S.Hm (S.spanTo g r), n v - v = hf L S.Hm v u • x := fun v hv => by
    rw [h1, eich, hv x hxX]; simp
  have e2 : ∀ v ∈ perp L S.Hm (S.spanTo g r), n⁻¹ v - v = -(hf L S.Hm v u • x) := fun v hv => by
    rw [h2, eich, hv x hxX, hf_neg_r]; simp
  have e3 : ∀ l : Fin r, ∀ v ∈ S.spanTo g (l + 1), hf L S.Hm v u • x ∈ S.spanTo g l := by
    intro l v hv
    by_cases h : (j : ℕ) ≤ l
    · exact Submodule.smul_mem _ _ (spanTo_mono S g h hx)
    · rw [hlow v (spanTo_mono S g (by omega) hv)]; simp
  refine ⟨n, ⟨⟨hn, Subgroup.mem_iInf.2 fun l => ?_⟩, ?_⟩, ?_, fun i hi => ?_, fun v hv => ?_⟩
  · have hl : S.spanTo g (l + 1) ≤ perp L S.Hm (S.spanTo g r) :=
      (spanTo_mono S g l.2).trans (spanTo_le_perp S g T gram)
    refine mem_unipOn (spanTo_mono S g (Nat.le_succ _)) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [e1 v (hl hv)]; exact e3 l v hv
    · rw [e2 v (hl hv)]; exact Submodule.neg_mem _ (e3 l v hv)
  · refine mem_unipOn (spanTo_le_perp S g T gram) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [e1 v hv]; exact Submodule.smul_mem _ _ hxX
    · rw [e2 v hv]; exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hxX)
  · have := e1 _ (mem_perp S g T gram j)
    rw [hu, if_pos rfl, one_smul] at this
    rw [← this]; abel
  · have := e1 _ (mem_perp S g T gram i)
    rw [hu, if_neg hi, zero_smul] at this
    exact sub_eq_zero.1 this
  · have := e1 _ (spanTo_le_perp S g T gram (spanTo_mono S g hjr hv))
    rw [hlow v hv, zero_smul] at this
    exact sub_eq_zero.1 this

include gram dual in
theorem exists_upto [IsNonarchimedeanLocalField F] [CharZero F] (x : Fin (r + 1) → S.V)
    (hx : ∀ j : Fin (r + 1), x j ∈ S.spanTo g j) (m : ℕ) :
    ∃ n ∈ S.Nof g, ∀ j : Fin (r + 1), n (g j) = if (j : ℕ) < m then g j + x j else g j := by
  induction m with
  | zero => exact ⟨1, one_mem _, fun j => by simp⟩
  | succ m ih =>
    obtain ⟨n, hn, h⟩ := ih
    by_cases hm : m < r + 1
    · obtain ⟨e, he, h1, h2, h3⟩ := exists_step S g gs T gram dual ⟨m, hm⟩ _ (hx ⟨m, hm⟩)
      refine ⟨e * n, mul_mem he hn, fun j => ?_⟩
      change e (n (g j)) = _
      rw [h]
      rcases lt_trichotomy (j : ℕ) m with hj | hj | hj
      · rw [if_pos hj, if_pos (by omega)]
        exact h3 _ (add_mem (mem_spanTo S g hj) (spanTo_mono S g hj.le (hx j)))
      · obtain rfl : j = ⟨m, hm⟩ := Fin.ext hj
        rw [if_neg (by simp), if_pos (by simp), h1]
      · rw [if_neg (by omega), if_neg (by omega)]
        exact h2 j fun hh => by rw [hh] at hj; simp at hj
    · refine ⟨n, hn, fun j => ?_⟩
      have := j.2
      rw [h, if_pos (by omega), if_pos (by omega)]


include gram dual in
theorem exists_elt [IsNonarchimedeanLocalField F] [CharZero F]
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) :
    ∃ n ∈ S.Nof g, ∀ j, n (g j) = ∑ i, s i j • g i := by
  have hx : ∀ j : Fin (r + 1), ∑ i ∈ Finset.univ.erase j, s i j • g i ∈ S.spanTo g j := by
    intro j
    refine Submodule.sum_mem _ fun i hi => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h | h
    · exact Submodule.smul_mem _ _ (mem_spanTo S g h)
    · rw [hs.1 i j h]; simp
  obtain ⟨n, hn, h⟩ := exists_upto S g gs T gram dual _ hx (r + 1)
  refine ⟨n, hn, fun j => ?_⟩
  rw [h, if_pos j.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), hs.2, one_smul]

end

theorem unipotent_onto : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ n ∈ S.N, ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ∀ j, n (S.f j) = ∑ i, s i j • S.f i) ∧ (∀ n ∈ S.N', ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ∀ j, n (S.f' j) = ∑ i, s i j • S.f' i) ∧ ∀ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) → (∃ n ∈ S.N, ∀ j, n (S.f j) = ∑ i, s i j • S.f i) ∧ ∃ n ∈ S.N', ∀ j, n (S.f' j) = ∑ i, s i j • S.f' i := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  exact ⟨exists_matrix S S.f S.T S.gram, exists_matrix S S.f' S.T' S.gram', fun s hs =>
    ⟨exists_elt S S.f S.es S.T S.gram S.dual s hs, exists_elt S S.f' S.es' S.T' S.gram' S.dual' s hs⟩⟩

end GlobalTheory.HL.FrameOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.UnramVal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem zpow_mul_unit_mem_iff {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (k : ℤ) (u : (𝒪[F])ˣ) :
    (ϖ : F) ^ k * ((u : 𝒪[F]) : F) ∈ 𝒪[F] ↔ 0 ≤ k := by
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  constructor
  · intro h
    by_contra hk
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -((n : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    refine hϖ.not_isUnit (IsUnit.of_mul_eq_one (ϖ ^ n * ⟨_, h⟩ * ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F])) ?_)
    apply Subtype.ext
    have hu : ((u : 𝒪[F]) : F) * (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    have h1 : (ϖ : F) * (ϖ : F) ^ n * (ϖ : F) ^ (-((n : ℤ) + 1)) = 1 := by
      rw [zpow_neg, zpow_add_one₀ h0, zpow_natCast]
      field_simp
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_one]
    linear_combination (((u : 𝒪[F]) : F) * (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F)) * h1 + hu
  · intro hk
    lift k to ℕ using hk
    rw [zpow_natCast]
    exact Subring.mul_mem _ (Subring.pow_mem _ ϖ.2 k) (u : 𝒪[F]).2

variable [IsNonarchimedeanLocalField F]

theorem vE_zpow_mul_unit (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (k : ℤ)
    (u : (𝒪[F])ˣ) : vE L ϖ (algebraMap F E ((ϖ : F) ^ k * ((u : 𝒪[F]) : F))) = k := by
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hset : {m : ℤ | ∃ y ∈ L.O, algebraMap F E ((ϖ : F) ^ k * ((u : 𝒪[F]) : F))
      = algebraMap F E ((ϖ : F) ^ m) * y} = Set.Iic k := by
    ext m
    have hsplit : (ϖ : F) ^ k * ((u : 𝒪[F]) : F)
        = (ϖ : F) ^ m * ((ϖ : F) ^ (k - m) * ((u : 𝒪[F]) : F)) := by
      rw [← mul_assoc, ← zpow_add₀ h0]; congr 2; ring
    have hun : IsUnit (algebraMap F E ((ϖ : F) ^ m)) :=
      (IsUnit.mk0 _ (zpow_ne_zero m h0)).map _
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    rw [hsplit, map_mul, ← sub_nonneg, ← zpow_mul_unit_mem_iff hϖ (k - m) u,
      ← GlobalTheory.UnramOrder.algebraMap_mem_iff L]
    constructor
    · rintro ⟨y, hy, h⟩
      rw [hun.mul_left_cancel h]; exact hy
    · intro h; exact ⟨_, h, rfl⟩
  rw [vE, hset, csSup_Iic]

theorem exists_eq_zpow_mul_unit {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {x : F} (hx : x ≠ 0) :
    ∃ (k : ℤ) (u : (𝒪[F])ˣ), x = (ϖ : F) ^ k * ((u : 𝒪[F]) : F) := by
  obtain ⟨k, u, h⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hx
  refine ⟨k, u, ?_⟩
  rw [h, mul_comm]; rfl

theorem vE_valuation : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → (∀ x y : F, x ≠ 0 → y ≠ 0 → vE L ϖ (algebraMap F E (x * y)) = vE L ϖ (algebraMap F E x) + vE L ϖ (algebraMap F E y)) ∧ vE L ϖ (algebraMap F E (ϖ : F)) = 1 ∧ (∀ x : F, x ≠ 0 → (0 ≤ vE L ϖ (algebraMap F E x) ↔ x ∈ 𝒪[F])) ∧ (∀ x : F, x ≠ 0 → ∃ u : (𝒪[F])ˣ, x = (ϖ : F) ^ (vE L ϖ (algebraMap F E x)) * ((u : 𝒪[F]) : F)) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨fun x y hx hy => ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨k, u, rfl⟩ := exists_eq_zpow_mul_unit hϖ hx
    obtain ⟨l, v, rfl⟩ := exists_eq_zpow_mul_unit hϖ hy
    have : (ϖ : F) ^ k * ((u : 𝒪[F]) : F) * ((ϖ : F) ^ l * ((v : 𝒪[F]) : F))
        = (ϖ : F) ^ (k + l) * (((u * v : (𝒪[F])ˣ) : 𝒪[F]) : F) := by
      rw [zpow_add₀ h0, Units.val_mul, Subring.coe_mul]; ring
    rw [this, vE_zpow_mul_unit L hϖ, vE_zpow_mul_unit L hϖ, vE_zpow_mul_unit L hϖ]
  · simpa using vE_zpow_mul_unit L hϖ 1 1
  · obtain ⟨k, u, rfl⟩ := exists_eq_zpow_mul_unit hϖ hx
    rw [vE_zpow_mul_unit L hϖ, zpow_mul_unit_mem_iff hϖ]
  · obtain ⟨k, u, rfl⟩ := exists_eq_zpow_mul_unit hϖ hx
    exact ⟨u, by rw [vE_zpow_mul_unit L hϖ]⟩

end GlobalTheory.UnramVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFrameClassProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFrameClassProperties
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameClass

theorem exists_inv {E : Type} [CommRing E] {σ : Type} [SetLike σ E] [SubringClass σ E] (O : σ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) E) (hO : ∀ i j, A i j ∈ O) (ht : ∀ i j, j < i → A i j = 0)
    (hd : ∀ i, A i i = 1) :
    ∃ B : Matrix (Fin n) (Fin n) E, (∀ i j, B i j ∈ O) ∧ (∀ i j, j < i → B i j = 0) ∧ (∀ i, B i i = 1) ∧
      A * B = 1 ∧ B * A = 1 := by
  let M : Matrix (Fin n) (Fin n) O := fun i j => ⟨A i j, hO i j⟩
  have hM : M.BlockTriangular id := fun i j h => Subtype.ext (ht i j h)
  have hMd : ∀ i, M i i = 1 := fun i => Subtype.ext (hd i)
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hM]; simp [hMd]
  have hu : IsUnit M.det := by rw [hdet]; exact isUnit_one
  let _ : Invertible M := Matrix.invertibleOfIsUnitDet M hu
  have hI : (M⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hM
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hu
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hu
  have hA : M.map (SubringClass.subtype O) = A := rfl
  refine ⟨(M⁻¹).map (SubringClass.subtype O), fun i j => (M⁻¹ i j).2, fun i j h => ?_, fun i => ?_, ?_, ?_⟩
  · have : M⁻¹ i j = 0 := hI h
    simp [Matrix.map_apply, this]
  · have h := congrFun (congrFun h1 i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hMd, one_mul] at h
    · simp [Matrix.map_apply, h]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · have : M i k = 0 := hM hk
        rw [this, zero_mul]
      · have : M⁻¹ k i = 0 := hI hk
        rw [this, mul_zero]
    · simp
  · rw [← hA, ← Matrix.map_mul, h1]; simp
  · rw [← hA, ← Matrix.map_mul, h2]; simp

theorem sum_comp {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) E) (g p q : Fin n → V) (hp : ∀ j, p j = ∑ i, A i j • g i)
    (hq : ∀ j, q j = ∑ i, B i j • p i) (j : Fin n) : q j = ∑ i, (A * B) i j • g i := by
  rw [hq]
  simp only [hp, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem th_ne_zero : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · intro h
    exact S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

theorem intM_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : IsIntM L A) (hB : IsIntM L B) :
    IsIntM L (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

theorem cong_iff {n : ℕ} (t : E) (A A' : Matrix (Fin n) (Fin n) E) :
    (∀ i j, ∃ c ∈ L.O, A' i j - A i j = t * c) ↔ ∃ C, IsIntM L C ∧ A' - A = t • C := by
  constructor
  · intro h
    choose C hC hC' using h
    exact ⟨C, hC, by ext i j; exact hC' i j⟩
  · rintro ⟨C, hC, h⟩ i j
    exact ⟨C i j, hC i j, congrFun (congrFun h i) j⟩

theorem refl_mem (g g' : Fin (r + 1) → S.V) : (g, g') ∈ S.frameCls g g' := by
  have h1 : IsIntM L (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  refine ⟨1, 1, h1, h1, fun i j h => ?_, fun i => by simp, fun i j => ⟨0, zero_mem _, by simp⟩, fun j => ?_,
    fun j => ?_⟩
  · simp [Matrix.one_apply_ne h.ne']
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply]

omit [TopologicalSpace E] in
theorem tri_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) : ∀ i j, j < i → (A * B) i j = 0 := fun i j h => by
  have hA' : A.BlockTriangular id := fun i j h => hA i j h
  have hB' : B.BlockTriangular id := fun i j h => hB i j h
  exact hA'.mul hB' h

omit [TopologicalSpace E] in
theorem diag_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with hl | hl
    · rw [hA i l hl, zero_mul]
    · rw [hB l i hl, mul_zero]
  · simp

theorem trans_mem {g g' : Fin (r + 1) → S.V} {p q : S.FrP} (hp : p ∈ S.frameCls g g')
    (hq : q ∈ S.frameCls p.1 p.2) : q ∈ S.frameCls g g' := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  obtain ⟨B, B', hB, hB', kt, kd, kc, k1, k2⟩ := hq
  obtain ⟨C, hC, hc⟩ := (cong_iff _ _ _).1 hc
  obtain ⟨D, hD, kc⟩ := (cong_iff _ _ _).1 kc
  refine ⟨A * B, A' * B', intM_mul hA hB, intM_mul hA' hB', fun i j h => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩, ?_,
    sum_comp A B g p.1 q.1 h1 k1, sum_comp A' B' g' p.2 q.2 h2 k2⟩
  · exact tri_mul (fun i j h => (ht i j h).1) (fun i j h => (kt i j h).1) i j h
  · exact tri_mul (fun i j h => (ht i j h).2) (fun i j h => (kt i j h).2) i j h
  · rw [diag_mul (fun i j h => (ht i j h).1) (fun i j h => (kt i j h).1), (hd i).1, (kd i).1, one_mul]
  · rw [diag_mul (fun i j h => (ht i j h).2) (fun i j h => (kt i j h).2), (hd i).2, (kd i).2, one_mul]
  · refine (cong_iff _ _ _).2 ⟨C * B' + A * D, fun i j => ?_, ?_⟩
    · exact add_mem (intM_mul hC hB' i j) (intM_mul hA hD i j)
    · rw [smul_add, ← Matrix.smul_mul, ← Matrix.mul_smul, ← hc, ← kc, sub_mul, mul_sub]; abel

theorem symm_mem {g g' : Fin (r + 1) → S.V} {p : S.FrP} (hp : p ∈ S.frameCls g g') :
    (g, g') ∈ S.frameCls p.1 p.2 := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  obtain ⟨C, hC, hc⟩ := (cong_iff _ _ _).1 hc
  obtain ⟨B, hB, bt, bd, hAB, hBA⟩ := exists_inv L.O A hA (fun i j h => (ht i j h).1) (fun i => (hd i).1)
  obtain ⟨B', hB', bt', bd', hAB', hBA'⟩ :=
    exists_inv L.O A' hA' (fun i j h => (ht i j h).2) (fun i => (hd i).2)
  refine ⟨B, B', hB, hB', fun i j h => ⟨bt i j h, bt' i j h⟩, fun i => ⟨bd i, bd' i⟩, ?_, fun j => ?_,
    fun j => ?_⟩
  · refine (cong_iff _ _ _).2 ⟨-(B' * C * B), fun i j => ?_, ?_⟩
    · exact neg_mem (intM_mul (intM_mul hB' hC) hB i j)
    · rw [smul_neg, ← Matrix.smul_mul, ← Matrix.mul_smul, ← hc, mul_sub, sub_mul, hBA', mul_assoc, hAB]
      simp
  · have := sum_comp A B g p.1 (fun j => ∑ i, B i j • p.1 i) h1 (fun _ => rfl) j
    rw [this, hAB]; simp [Matrix.one_apply]
  · have := sum_comp A' B' g' p.2 (fun j => ∑ i, B' i j • p.2 i) h2 (fun _ => rfl) j
    rw [this, hAB']; simp [Matrix.one_apply]

theorem Mof_le {g g' : Fin (r + 1) → S.V} {p : S.FrP} (hp : p ∈ S.frameCls g g') :
    S.Mof p.1 p.2 ≤ S.Mof g g' := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  have hsm : ∀ c ∈ L.O, ∀ v ∈ S.Mof g g', c • v ∈ S.Mof g g' := fun c hc v hv =>
    (S.Mof g g').smul_mem ⟨c, hc⟩ hv
  have hg : ∀ i, g i ∈ S.Mof g g' := fun i => Submodule.subset_span (Or.inl ⟨i, rfl⟩)
  have hg' : ∀ i, algebraMap F E S.th⁻¹ • (g' i - g i) ∈ S.Mof g g' := fun i =>
    Submodule.subset_span (Or.inr ⟨i, rfl⟩)
  have hth : algebraMap F E S.th⁻¹ * algebraMap F E S.th = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (th_ne_zero S), map_one]
  choose C hC hC' using hc
  refine Submodule.span_le.2 ?_
  rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · rw [h1]
    exact sum_mem fun i _ => hsm _ (hA i j) _ (hg i)
  · have : algebraMap F E S.th⁻¹ • (p.2 j - p.1 j) =
        ∑ i, (A' i j • (algebraMap F E S.th⁻¹ • (g' i - g i)) + C i j • g i) := by
      rw [h1, h2, ← Finset.sum_sub_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hCi : C i j = algebraMap F E S.th⁻¹ * (A' i j - A i j) := by
        rw [hC', ← mul_assoc, hth, one_mul]
      rw [hCi]; module
    show algebraMap F E S.th⁻¹ • (p.2 j - p.1 j) ∈ S.Mof g g'
    rw [this]
    exact sum_mem fun i _ => add_mem (hsm _ (hA' i j) _ (hg' i)) (hsm _ (hC i j) _ (hg i))

theorem smul_mem (h : S.GLV) {g g' : Fin (r + 1) → S.V} {p : S.FrP} (hp : p ∈ S.frameCls g g') :
    h • p ∈ S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  refine ⟨A, A', hA, hA', ht, hd, hc, fun j => ?_, fun j => ?_⟩
  · show h (p.1 j) = _
    rw [h1]; simp
  · show h (p.2 j) = _
    rw [h2]; simp

theorem smul_cls (h : S.GLV) (g g' : Fin (r + 1) → S.V) :
    h • S.frameCls g g' = S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact smul_mem S h hq
  · intro hp
    have := smul_mem S h⁻¹ hp
    refine ⟨h⁻¹ • p, ?_, smul_inv_smul h p⟩
    have e : ∀ v : S.V, h⁻¹ (h v) = v := fun v => h.symm_apply_apply v
    simpa only [e] using this

theorem frame_classes : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ g g' : Fin (r + 1) → S.V, (g, g') ∈ S.frameCls g g' ∧ (∀ p ∈ S.frameCls g g', S.frameCls p.1 p.2 = S.frameCls g g' ∧ S.Mof p.1 p.2 = S.Mof g g') ∧ ∀ h : S.GLV, h • S.frameCls g g' = S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S g g'
  refine ⟨refl_mem S g g', fun p hp => ⟨?_, ?_⟩, fun h => smul_cls S h g g'⟩
  · ext q
    exact ⟨fun hq => trans_mem S hp hq, fun hq => trans_mem S (symm_mem S hp) hq⟩
  · exact le_antisymm (Mof_le S hp) (Mof_le S (p := (g, g')) (symm_mem S hp))

end GlobalTheory.HL.FrameClass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFrameClassPropertiesStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDoubleCosetFrameClass_properties : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ g g' : Fin (r + 1) → S.V, (g, g') ∈ S.frameCls g g' ∧ (∀ p ∈ S.frameCls g g', S.frameCls p.1 p.2 = S.frameCls g g' ∧ S.Mof p.1 p.2 = S.Mof g g') ∧ ∀ h : S.GLV, h • S.frameCls g g' = S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by
  first | exact @GlobalTheory.HL.FrameClass.frame_classes | exact GlobalTheory.HL.FrameClass.frame_classes | (intros; apply GlobalTheory.HL.FrameClass.frame_classes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspace
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspace
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.DualInter

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

noncomputable def hfL (y : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun x := hf L Hm x y
  map_add' a b := by simp [hf, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [hf, Finset.mul_sum, mul_assoc]

noncomputable def hfR (x : Fin n → E) : (Fin n → E) →+ E where
  toFun y := hf L Hm x y
  map_add' a b := by simp [hf, mul_add, Finset.sum_add_distrib]
  map_zero' := by simp [hf]

theorem sub_l (a b y : Fin n → E) : hf L Hm (a - b) y = hf L Hm a y - hf L Hm b y :=
  (hfL L Hm y).map_sub a b

theorem smul_l (c : E) (a y : Fin n → E) : hf L Hm (c • a) y = c * hf L Hm a y :=
  (hfL L Hm y).map_smul c a

theorem sum_l {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, a i) y = ∑ i ∈ s, hf L Hm (a i) y :=
  map_sum (hfL L Hm y) a s

theorem sub_r (x a b : Fin n → E) : hf L Hm x (a - b) = hf L Hm x a - hf L Hm x b :=
  (hfR L Hm x).map_sub a b

theorem sum_r {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (x : Fin n → E) :
    hf L Hm x (∑ i ∈ s, a i) = ∑ i ∈ s, hf L Hm x (a i) :=
  map_sum (hfR L Hm x) a s

theorem smul_r (c : E) (x a : Fin n → E) : hf L Hm x (c • a) = L.cj c * hf L Hm x a := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {L Hm}

theorem cj_hf (h : IsHermND L Hm) (x y : Fin n → E) : L.cj (hf L Hm x y) = hf L Hm y x := by
  have hH : ∀ i j, L.cj (Hm i j) = Hm j i := fun i j => congrFun (congrFun h.1 j) i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, hH, L.cj_cj]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem eq_zero_of_hf (h : IsHermND L Hm) {y : Fin n → E} (hy : ∀ x, hf L Hm x y = 0) : y = 0 := by
  have h1 : Hm.mulVec (fun j => L.cj (y j)) = 0 := by
    funext i
    have := hy (Pi.single i 1)
    simpa [hf, Pi.single_apply, Finset.sum_ite_eq, Matrix.mulVec, dotProduct, ite_mul] using this
  have h2 : (fun j => L.cj (y j)) = 0 := by
    have := congrArg (Hm⁻¹.mulVec) h1
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.2, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
  funext j
  exact L.cj.injective (by simpa using congrFun h2 j)

theorem hf_eq_zero_of_span {S : Set (Fin n → E)} {y : Fin n → E} (hy : ∀ x ∈ S, hf L Hm x y = 0) :
    ∀ x ∈ Submodule.span E S, hf L Hm x y = 0 := fun x hx =>
  (Submodule.span_le (p := LinearMap.ker (hfL L Hm y))).2 hy hx

variable [IsNonarchimedeanLocalField F]

theorem exists_denom (L : LocE F E) (x : E) : ∃ d ∈ L.O, IsUnit d ∧ d * x ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have hx : IsAlgebraic 𝒪[F] x :=
    (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨d, hd0, hd⟩ := hx.exists_integral_multiple
  refine ⟨algebraMap F E d, (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 d.2,
    (IsUnit.mk0 (d : F) fun h => hd0 (Subtype.ext h)).map _, (L.O_def _).2 ?_⟩
  rwa [Algebra.smul_def] at hd

theorem exists_denom_fg {Λ : Submodule L.O (Fin n → E)} (hΛ : Λ.FG) (y : Fin n → E) :
    ∃ d ∈ L.O, IsUnit d ∧ ∀ x ∈ Λ, d * hf L Hm x y ∈ L.O := by
  induction Λ, hΛ using Submodule.fg_induction with
  | singleton v =>
    obtain ⟨d, h1, h2, h3⟩ := exists_denom L (hf L Hm v y)
    refine ⟨d, h1, h2, fun x hx => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have : hf L Hm (a • v) y = a * hf L Hm v y := smul_l L Hm a v y
    rw [this, mul_left_comm]
    exact L.O.mul_mem a.2 h3
  | sup A B _ _ hA hB =>
    obtain ⟨d, h1, h2, h3⟩ := hA
    obtain ⟨e, k1, k2, k3⟩ := hB
    refine ⟨d * e, L.O.mul_mem h1 k1, h2.mul k2, fun x hx => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    have : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := (hfL L Hm y).map_add a b
    rw [this, show d * e * (hf L Hm a y + hf L Hm b y)
      = e * (d * hf L Hm a y) + d * (e * hf L Hm b y) by ring]
    exact L.O.add_mem (L.O.mul_mem k1 (h3 a ha)) (L.O.mul_mem h1 (k3 b hb))

theorem exists_primitive [CharZero F] (h : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)}
    (hΛ : IsSD L Hm Λ) {y : Fin n → E} (hy : ∀ s : E, s • y = 0 → s = 0) :
    ∃ t : E, IsUnit t ∧ t • y ∈ Λ ∧ ∃ c ∈ Λ, hf L Hm (t • y) c = 1 := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hP : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1
  obtain ⟨d, -, hd, hdx⟩ := exists_denom_fg (Hm := Hm) hΛ.1.1 y
  let I : Ideal L.O :=
    { carrier := {r | ∃ x ∈ Λ, (r : E) = d * hf L Hm x y}
      zero_mem' := ⟨0, Λ.zero_mem, by simp [hf]⟩
      add_mem' := by
        rintro r s ⟨a, ha, hr⟩ ⟨b, hb, hs⟩
        refine ⟨a + b, Λ.add_mem ha hb, ?_⟩
        have : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := (hfL L Hm y).map_add a b
        rw [this, Subring.coe_add, hr, hs, mul_add]
      smul_mem' := by
        rintro s r ⟨a, ha, hr⟩
        refine ⟨s • a, Λ.smul_mem s ha, ?_⟩
        have : hf L Hm (s • a) y = s * hf L Hm a y := smul_l L Hm s a y
        rw [this, smul_eq_mul, Subring.coe_mul, hr, mul_left_comm] }
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal I).principal
  obtain ⟨c, hc, hgc⟩ : g ∈ I := by rw [hg]; exact Submodule.mem_span_singleton_self g
  have hdiv : ∀ x ∈ Λ, ∃ r ∈ L.O, hf L Hm x y = r * hf L Hm c y := by
    intro x hx
    have : (⟨_, hdx x hx⟩ : L.O) ∈ I := ⟨x, hx, rfl⟩
    rw [hg] at this
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
    have hr' : (r : E) * g = d * hf L Hm x y := congrArg Subtype.val hr
    refine ⟨r, r.2, hd.mul_left_cancel ?_⟩
    rw [← hr', hgc]; ring
  have hu : IsUnit (hf L Hm c y) := by
    refine IsArtinianRing.isUnit_of_mem_nonZeroDivisors (mem_nonZeroDivisors_iff_right.2 ?_)
    intro s hs
    have h1 : L.cj s • y = 0 := eq_zero_of_hf h fun x =>
      hf_eq_zero_of_span (S := Λ) (fun z hz => by
        obtain ⟨r, -, hr⟩ := hdiv z hz
        rw [smul_r, L.cj_cj, hr, mul_left_comm, hs, mul_zero]) x (by rw [hΛ.1.2]; trivial)
    exact L.cj.injective (by simpa using hy _ h1)
  obtain ⟨u, hu'⟩ := hu.exists_left_inv
  refine ⟨L.cj u, (IsUnit.of_mul_eq_one _ hu').map _, (hΛ.2 _).1 fun x hx => ?_, c, hc, ?_⟩
  · obtain ⟨r, hr0, hr⟩ := hdiv x hx
    rw [smul_r, L.cj_cj, hr, mul_left_comm, hu', mul_one]
    exact hr0
  · rw [← cj_hf h, smul_r, L.cj_cj, hu', map_one]

theorem exists_dual_family [CharZero F] (h : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)}
    (hΛ : IsSD L Hm Λ) (m : ℕ) (y : Fin m → Fin n → E) (hy : LinearIndependent E y) :
    ∃ b c : Fin m → Fin n → E, (∀ i, b i ∈ Λ) ∧ (∀ j, c j ∈ Λ) ∧
      Submodule.span E (Set.range b) = Submodule.span E (Set.range y) ∧
      ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0 := by
  induction m with
  | zero => exact ⟨y, y, fun i => i.elim0, fun i => i.elim0, rfl, fun i => i.elim0⟩
  | succ m ih =>
    obtain ⟨b, c, hb, hc, hspan, hbc⟩ := ih (Fin.tail y) (hy.comp _ (Fin.succ_injective m))
    set w := ∑ j, hf L Hm (y 0) (c j) • b j with hw
    have hwm : w ∈ Submodule.span E (Set.range b) :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hz : ∀ j, hf L Hm (y 0 - w) (c j) = 0 := fun j => by
      simp [hw, sub_l, sum_l, smul_l, hbc]
    obtain ⟨t, ht, htm, c', hc', htc⟩ := exists_primitive h hΛ (y := y 0 - w) (fun s hs => by
      refine hy.eq_zero_of_smul_mem_span 0 s ?_
      rw [smul_sub, sub_eq_zero] at hs
      rw [hs]
      refine Submodule.smul_mem _ _ (Submodule.span_mono ?_ (hspan ▸ hwm))
      rintro _ ⟨j, rfl⟩
      exact ⟨j.succ, by simp, rfl⟩)
    have hc0 : c' - ∑ j, hf L Hm c' (b j) • c j ∈ Λ :=
      Λ.sub_mem hc' (Λ.sum_mem fun j _ => Λ.smul_mem ⟨_, (hΛ.2 _).2 (hb j) _ hc'⟩ (hc j))
    refine ⟨Fin.cons (t • (y 0 - w)) b, Fin.cons (c' - ∑ j, hf L Hm c' (b j) • c j) c,
      fun i => Fin.cases htm hb i, fun i => Fin.cases hc0 hc i, ?_, fun i j => ?_⟩
    · rw [Fin.range_cons, Fin.range_fin_succ y, Submodule.span_insert, Submodule.span_insert,
        ← hspan, ← Submodule.span_singleton_smul_eq ht (y 0)]
      have hwt := Submodule.smul_mem _ t hwm
      rw [smul_sub]
      refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right) <;>
        rw [Submodule.span_singleton_le_iff_mem]
      · exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
          (Submodule.mem_sup_right hwt)
      · have := Submodule.add_mem _ (Submodule.mem_sup_left
          (Submodule.mem_span_singleton_self (t • y 0 - t • w))) (Submodule.mem_sup_right hwt)
        rwa [sub_add_cancel] at this
    · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cons_zero, sub_r, sum_r, smul_r, htc]
        simp [smul_l L Hm t, hz]
      · simp [smul_l L Hm t, hz, (Fin.succ_ne_zero j).symm]
      · simp [sub_r, sum_r, smul_r, hbc, cj_hf h]
      · simp [hbc]

theorem dual_inter : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (y : Fin m → Fin n → E), LinearIndependent E y → perp L Hm (perp L Hm (Submodule.span E (Set.range y))) = (Submodule.span E (Set.range y)) ∧ (∀ v, (∀ x ∈ Λ, x ∈ perp L Hm (Submodule.span E (Set.range y)) → hf L Hm x v ∈ L.O) ↔ ∃ a ∈ Λ, v - a ∈ (Submodule.span E (Set.range y))) ∧ (∀ v, (∀ x ∈ Λ, x ∈ (Submodule.span E (Set.range y)) → hf L Hm x v ∈ L.O) ↔ ∃ a ∈ Λ, v - a ∈ perp L Hm (Submodule.span E (Set.range y))) ∧ ∃ b : Fin m → Fin n → E, ∃ c : Fin m → Fin n → E, Λ ⊓ (Submodule.span E (Set.range y)).restrictScalars L.O = Submodule.span L.O (Set.range b) ∧ (∀ j, c j ∈ Λ) ∧ ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0 := by
  intro F _ _ _ _ _ E _ _ _ L n Hm h Λ hΛ m y hy
  obtain ⟨b, c, hb, hc, hspan, hbc⟩ := exists_dual_family h hΛ m y hy
  rw [← hspan]
  set Y := Submodule.span E (Set.range b) with hY
  have hbY : ∀ j, b j ∈ Y := fun j => Submodule.subset_span ⟨j, rfl⟩
  have hsym : ∀ x v, hf L Hm x v = 0 → hf L Hm v x = 0 := fun x v hx => by
    rw [← cj_hf h, hx, map_zero]
  have hperp : ∀ x, (∀ i, hf L Hm (b i) x = 0) → x ∈ perp L Hm Y := fun x hx v hv =>
    hsym _ _ (hf_eq_zero_of_span (by rintro _ ⟨i, rfl⟩; exact hx i) v hv)
  have hproj : ∀ x, x - ∑ j, hf L Hm x (b j) • c j ∈ perp L Hm Y := fun x =>
    hperp _ fun i => by simp [sub_r, sum_r, smul_r, hbc, cj_hf h]
  have hadj : ∀ x v, hf L Hm x (v - ∑ j, hf L Hm v (c j) • b j)
      = hf L Hm (x - ∑ j, hf L Hm x (b j) • c j) v := fun x v => by
    simp [sub_r, sum_r, smul_r, sub_l, sum_l, smul_l, cj_hf h, mul_comm]
  have hsum : ∀ v, ∑ j, hf L Hm v (c j) • b j ∈ Y := fun v =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbY j)
  have hpp : ∀ v, (∀ x ∈ perp L Hm Y, hf L Hm x v = 0) → v = ∑ j, hf L Hm v (c j) • b j :=
    fun v hv => sub_eq_zero.1 (eq_zero_of_hf h fun x => by rw [hadj]; exact hv _ (hproj x))
  refine ⟨?_, fun v => ⟨fun hv => ?_, ?_⟩, fun v => ⟨fun hv => ?_, ?_⟩, b, c, ?_, hc, hbc⟩
  · ext v
    refine ⟨fun hv => ?_, fun hv x hx => hsym _ _ (hx v hv)⟩
    rw [hpp v fun x hx => hsym _ _ (hv x hx)]
    exact hsum v
  · refine ⟨v - ∑ j, hf L Hm v (c j) • b j, (hΛ.2 _).1 fun x hx => ?_, by simpa using hsum v⟩
    rw [hadj]
    refine hv _ (Λ.sub_mem hx (Λ.sum_mem fun j _ => ?_)) (hproj x)
    exact Λ.smul_mem ⟨_, (hΛ.2 _).2 (hb j) _ hx⟩ (hc j)
  · rintro ⟨a, ha, hva⟩ x hx hxp
    have := hxp _ hva
    rw [sub_r, sub_eq_zero] at this
    rw [this]
    exact (hΛ.2 _).2 ha x hx
  · refine ⟨_, Λ.sum_mem fun j _ => ?_, hproj v⟩
    have : hf L Hm v (b j) ∈ L.O := by
      rw [← cj_hf h]
      exact GlobalTheory.UnramOrder.cj_mem L (hv _ (hb j) (hbY j))
    exact Λ.smul_mem ⟨_, this⟩ (hc j)
  · rintro ⟨a, ha, hva⟩ x hx hxp
    have := hsym _ _ (hva x hxp)
    rw [sub_r, sub_eq_zero] at this
    rw [this]
    exact (hΛ.2 _).2 ha x hx
  · refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rintro v ⟨hv, hvY⟩
      rw [hpp v fun x hx => hx v hvY]
      refine Submodule.sum_mem _ fun j _ => ?_
      exact Submodule.smul_mem (Submodule.span L.O (Set.range b))
        ⟨_, (hΛ.2 _).2 (hc j) _ hv⟩ (Submodule.subset_span ⟨j, rfl⟩)
    · rintro _ ⟨j, rfl⟩
      exact ⟨hb j, hbY j⟩

end GlobalTheory.HL.DualInter
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspaceStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_inter_selfDualHermitianLattice_subspace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (y : Fin m → Fin n → E), LinearIndependent E y → perp L Hm (perp L Hm (Submodule.span E (Set.range y))) = (Submodule.span E (Set.range y)) ∧ (∀ v, (∀ x ∈ Λ, x ∈ perp L Hm (Submodule.span E (Set.range y)) → hf L Hm x v ∈ L.O) ↔ ∃ a ∈ Λ, v - a ∈ (Submodule.span E (Set.range y))) ∧ (∀ v, (∀ x ∈ Λ, x ∈ (Submodule.span E (Set.range y)) → hf L Hm x v ∈ L.O) ↔ ∃ a ∈ Λ, v - a ∈ perp L Hm (Submodule.span E (Set.range y))) ∧ ∃ b : Fin m → Fin n → E, ∃ c : Fin m → Fin n → E, Λ ⊓ (Submodule.span E (Set.range y)).restrictScalars L.O = Submodule.span L.O (Set.range b) ∧ (∀ j, c j ∈ Λ) ∧ ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.HL.DualInter.dual_inter | exact GlobalTheory.HL.DualInter.dual_inter | (intros; apply GlobalTheory.HL.DualInter.dual_inter <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormAdditiveCharacterTypePrimeEqOne
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FramePsi

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def pairL (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    (Fin n → E) →ₗ[E] E where
  toFun x := hf L Hm x y
  map_add' a b := by simp [hf, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_span_right (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x : Fin n → E)
    (s : Set (Fin n → E)) (hs : ∀ y ∈ s, hf L Hm x y = 0) :
    ∀ y ∈ Submodule.span E s, hf L Hm x y = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y h => exact hs y h
  | zero => simp [hf]
  | add a b _ _ ha hb =>
    have : hf L Hm x (a + b) = hf L Hm x a + hf L Hm x b := by
      simp [hf, mul_add, Finset.sum_add_distrib]
    rw [this, ha, hb, add_zero]
  | smul c a _ ha =>
    have : hf L Hm x (c • a) = L.cj c * hf L Hm x a := by
      simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this, ha, mul_zero]

theorem coef_mul {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (gs : Fin r → S.V) (t : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (a : S.GLV) (ha : a ∈ S.Nof g) (b : S.GLV) (hb : b ∈ S.Nof g) (j : Fin r) :
    S.coef g gs (a * b) j = S.coef g gs a j + S.coef g gs b j := by
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf] at ha hb
  obtain ⟨⟨-, ha1⟩, -⟩ := ha
  obtain ⟨⟨-, hb1⟩, hb2⟩ := hb
  have hA : b (g j.succ) - g j.succ ∈ S.spanTo g (j + 1) := by
    by_cases hj : (j : ℕ) + 1 < r
    · refine (hb1 ⟨j + 1, hj⟩).2 _ (Submodule.subset_span ⟨j.succ, ?_, rfl⟩)
      simp
    · have hr : (j : ℕ) + 1 = r := by have := j.2; omega
      rw [hr]
      refine hb2.2 _ ?_
      refine hf_span_right L S.Hm _ _ ?_
      rintro _ ⟨i, hi, rfl⟩
      rw [hg, if_neg]
      rintro ⟨-, rfl⟩
      simp at hi
  have hB := (ha1 j).2 _ hA
  have hK : S.spanTo g j ≤ LinearMap.ker (pairL L S.Hm (gs j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    change hf L S.Hm (g i) (gs j) = 0
    rw [hd, if_neg]
    rintro rfl
    simp at hi
  have h0 : pairL L S.Hm (gs j) (g j.succ) = 0 := by
    change hf L S.Hm (g j.succ) (gs j) = 0
    rw [hd, if_neg]
    intro h
    have := congrArg Fin.val h
    simp at this
  have h1 := LinearMap.mem_ker.1 (hK hB)
  change pairL L S.Hm (gs j) (a (b (g j.succ))) =
    pairL L S.Hm (gs j) (a (g j.succ)) + pairL L S.Hm (gs j) (b (g j.succ))
  simp only [map_sub] at h1
  linear_combination h1 - h0

theorem exists_nsmul_mem [IsNonarchimedeanLocalField F] (L : LocE F E) (y : E) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : E) * y ∈ L.O := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have hyF : IsAlgebraic F y := Algebra.IsAlgebraic.isAlgebraic y
  have hy : IsAlgebraic 𝒪[F] y := (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 hyF
  obtain ⟨c, hc, hcy⟩ := hy.exists_integral_multiple
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  have hp : ((Nat.card 𝓀[F] : ℕ) : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    have := Fintype.ofFinite 𝓀[F]
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hp
  have hdv : c ∣ ((Nat.card 𝓀[F] ^ m : ℕ) : 𝒪[F]) := by
    rw [hu, Nat.cast_pow, Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd hp m
  obtain ⟨d, hd⟩ := hdv
  refine ⟨Nat.card 𝓀[F] ^ m, pow_ne_zero _ Nat.card_pos.ne', (L.O_def _).2 ?_⟩
  have : ((Nat.card 𝓀[F] ^ m : ℕ) : E) * y = d • (c • y) := by
    rw [smul_smul, mul_comm d c, ← hd, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  rw [this]
  exact hcy.smul d

theorem norm_additiveCharacter_typePrime_eq_one [IsNonarchimedeanLocalField F] (L : LocE F E) (y : E) : ‖L.psi0 y‖ = 1 := by
  obtain ⟨n, hn, hy⟩ := exists_nsmul_mem L y
  have h1 : L.psi0 ((n : E) * y) = 1 := by
    simpa using (L.additive_character_dual_ring _).2 hy 1 L.O.one_mem
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow] at h1
  have h2 := congrArg norm h1
  rw [norm_pow, norm_one] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2

theorem psi_unitary_character : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ a ∈ S.N, ∀ b ∈ S.N, S.psi (a * b) = S.psi a * S.psi b) ∧ (∀ a ∈ S.N', ∀ b ∈ S.N', S.psi' (a * b) = S.psi' a * S.psi' b) ∧ (∀ a, ‖S.psi a‖ = 1 ∧ ‖S.psi' a‖ = 1) ∧ ∀ y : E, ‖L.psi0 y‖ = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  refine ⟨fun a ha b hb => ?_, fun a ha b hb => ?_,
    fun a => ⟨norm_additiveCharacter_typePrime_eq_one L _, norm_additiveCharacter_typePrime_eq_one L _⟩, norm_additiveCharacter_typePrime_eq_one L⟩
  · simp only [Frames.psi, Frames.psiOf]
    rw [← AddChar.map_add_eq_mul, ← mul_add, ← Finset.sum_add_distrib]
    simp only [coef_mul S S.f S.es _ S.gram S.dual a ha b hb]
  · simp only [Frames.psi', Frames.psiOf]
    rw [← AddChar.map_add_eq_mul, ← mul_add, ← Finset.sum_add_distrib]
    simp only [coef_mul S S.f' S.es' _ S.gram' S.dual' a ha b hb]

end GlobalTheory.FramePsi
end
