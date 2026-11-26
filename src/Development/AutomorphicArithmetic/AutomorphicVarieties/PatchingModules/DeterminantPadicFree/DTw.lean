module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DTw
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DerEv
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem single_mem_ev_of_same_block {F : Type} [CommRing F] {n a : ℕ} (p q : Fin n) (c : F)
    (h : ((p : ℕ) < a ↔ (q : ℕ) < a)) : Matrix.single p q c ∈ Ev F F n a := by
  intro i j
  refine ⟨fun _ => Submodule.mem_top, fun hij => ?_⟩
  rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hij h

theorem UpperTheory.V.Pa.Det.derEv :
    ∀ {F : Type} [CommRing F] {n a : ℕ} (d : Matrix (Fin n) (Fin n) F →ₗ[F] Matrix (Fin n) (Fin n) F), (∀ x ∈ Ev F F n a, ∀ y ∈ Ev F F n a, d (x * y) = d x * y + x * d y) → ∃ Y, ∀ x ∈ Ev F F n a, d x = Y * x - x * Y := by
  intro F _ n a d hd
  let β : Fin n → Fin n := fun i =>
    if h : (i : ℕ) < a then ⟨0, lt_of_le_of_lt (Nat.zero_le _) i.isLt⟩
    else ⟨a, lt_of_le_of_lt (not_lt.mp h) i.isLt⟩
  have hβ : ∀ i : Fin n, ((i : ℕ) < a ↔ (β i : ℕ) < a) := by
    intro i
    by_cases h : (i : ℕ) < a
    · simp only [β, dif_pos h]
      exact ⟨fun _ => Nat.zero_lt_of_lt h, fun _ => h⟩
    · simp only [β, dif_neg h]
      exact ⟨fun h' => absurd h' h, fun h' => absurd h' (lt_irrefl _)⟩
  have hβeq : ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) → β i = β j := by
    intro i j h
    by_cases hi : (i : ℕ) < a
    · have hj := h.mp hi
      simp only [β, dif_pos hi, dif_pos hj]
    · have hj : ¬ (j : ℕ) < a := fun hj => hi (h.mpr hj)
      simp only [β, dif_neg hi, dif_neg hj]
  let E : Fin n → Fin n → Matrix (Fin n) (Fin n) F := fun i j => Matrix.single i j 1
  let u : Fin n → Matrix (Fin n) (Fin n) F := fun k => E k (β k)
  let v : Fin n → Matrix (Fin n) (Fin n) F := fun k => E (β k) k
  have hu : ∀ k, u k ∈ Ev F F n a := fun k => single_mem_ev_of_same_block _ _ _ (hβ k)
  let Y := ∑ k, d (u k) * v k
  have hsum : ∑ k, u k * v k = 1 := by
    simp only [u, v, E, Matrix.single_mul_single_same, mul_one]
    exact Matrix.sum_single_one
  have key : ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) →
      d (E i j) = Y * E i j - E i j * Y := by
    intro i j hij
    have hE : E i j ∈ Ev F F n a := single_mem_ev_of_same_block i j 1 hij
    have h1 : Y * E i j = d (u i) * v j := by
      simp only [Y, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_eq_single i]
      · simp only [v, E, u]
        rw [Matrix.single_mul_single_same, mul_one, hβeq i j hij]
      · intro k _ hk
        simp only [v, E]
        rw [Matrix.single_mul_single_of_ne _ _ _ _ hk _, mul_zero]
      · simp
    have hk : ∀ k, E i j * d (u k) = d (E i j * u k) - d (E i j) * u k := by
      intro k
      rw [hd _ hE _ (hu k)]
      abel
    have hEu : ∀ k, E i j * u k = if j = k then u i else 0 := by
      intro k
      split_ifs with h
      · subst h
        simp only [E, u]
        rw [Matrix.single_mul_single_same, mul_one, hβeq i j hij]
      · exact Matrix.single_mul_single_of_ne _ _ _ _ h _
    have h2 : E i j * Y = d (u i) * v j - d (E i j) := by
      calc E i j * Y = ∑ k, (d (E i j * u k) * v k - d (E i j) * (u k * v k)) := by
            simp only [Y, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← mul_assoc, hk, sub_mul, mul_assoc]
        _ = d (u i) * v j - d (E i j) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_one]
            congr 1
            rw [Finset.sum_eq_single j]
            · rw [hEu, if_pos rfl]
            · intro k _ hk
              rw [hEu, if_neg (Ne.symm hk), map_zero, zero_mul]
            · simp
    rw [h1, h2]
    abel
  refine ⟨Y, fun x hx => ?_⟩
  let D' : Matrix (Fin n) (Fin n) F →ₗ[F] Matrix (Fin n) (Fin n) F :=
    d - (LinearMap.mulLeft F Y - LinearMap.mulRight F Y)
  have hD : D' x = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.matrix_eq_sum_single x, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hij : ((i : ℕ) < a ↔ (j : ℕ) < a)
    · have hs : Matrix.single i j (x i j) = x i j • E i j := by
        simp only [E, Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_smul]
      simp only [D', LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        key i j hij, sub_self, smul_zero]
    · have h0 : x i j = 0 := (Submodule.mem_bot F).mp ((hx i j).2 hij)
      rw [h0, Matrix.single_zero, map_zero]
  simp only [D', LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    sub_eq_zero] at hD
  exact hD
end

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem exists_factor {F A M : Type} [Field F] [AddCommGroup A] [Module F A] [AddCommGroup M] [Module F M]
    (T S : A →ₗ[F] M) (h : LinearMap.ker T ≤ LinearMap.ker S) : ∃ d : M →ₗ[F] M, ∀ c, d (T c) = S c := by
  let S' : LinearMap.range T →ₗ[F] M :=
    ((LinearMap.ker T).liftQ S h).comp T.quotKerEquivRange.symm.toLinearMap
  obtain ⟨d, hd⟩ := LinearMap.exists_extend S'
  refine ⟨d, fun c => ?_⟩
  have h1 : d (T c) = S' ⟨T c, LinearMap.mem_range_self T c⟩ := by
    rw [← hd]
    rfl
  have h2 : T.quotKerEquivRange.symm ⟨T c, LinearMap.mem_range_self T c⟩ = Submodule.Quotient.mk c := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [LinearMap.quotKerEquivRange_apply_mk]
  rw [h1]
  simp only [S', LinearMap.comp_apply, LinearEquiv.coe_coe, h2, Submodule.liftQ_apply]

theorem UpperTheory.V.Pa.Det.der :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (z : G → Matrix (Fin n) (Fin n) F), TwCoc (fun _ => 1) D.r D.G' z → (∀ i j, D.KillsRel z i j) → ∃ Y, ∀ g ∈ D.G', z g = dTw (fun _ => 1) D.r Y g := by
  intro F G _ _ n D z hz hk
  let A := Finsupp.supported F F (D.G' : Set G)
  let T : A →ₗ[F] Matrix (Fin n) (Fin n) F :=
    (Finsupp.linearCombination F (fun g => D.r g)).comp A.subtype
  let S : A →ₗ[F] Matrix (Fin n) (Fin n) F :=
    (Finsupp.linearCombination F (fun g => z g * D.r g)).comp A.subtype
  have hTS : LinearMap.ker T ≤ LinearMap.ker S := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    ext i j
    have hsupp : ∀ g ∈ (c : G →₀ F).support, g ∈ D.G' := fun g hg =>
      (Finsupp.mem_supported F _).1 c.2 hg
    have := hk i j (c : G →₀ F) hsupp (by simpa [T, Finsupp.linearCombination_apply] using hc)
    simpa [S, Finsupp.linearCombination_apply] using this
  obtain ⟨d, hd⟩ := exists_factor T S hTS
  have hdr : ∀ g ∈ D.G', d (D.r g) = z g * D.r g := by
    intro g hg
    have := hd ⟨Finsupp.single g 1, Finsupp.single_mem_supported F 1 hg⟩
    simpa [T, S] using this
  have hr1 : ∀ g, D.r g⁻¹ * D.r g = 1 := fun g => by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hgen : ∀ g ∈ D.G', ∀ h ∈ D.G',
      d (D.r g * D.r h) = d (D.r g) * D.r h + D.r g * d (D.r h) := by
    intro g hg h hh
    rw [← D.r.map_mul, hdr _ (D.G'.mul_mem hg hh), hdr g hg, hdr h hh, hz g hg h hh, D.r.map_mul]
    simp only [one_smul, Matrix.add_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (D.r g⁻¹) (D.r g) (D.r h), hr1, Matrix.one_mul]
  have hder : ∀ x ∈ Ev F F n D.a, ∀ y ∈ Ev F F n D.a, d (x * y) = d x * y + x * d y := by
    intro x hx y hy
    rw [← D.span] at hx hy
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨g, hg, rfl⟩ := hx'
      induction hy using Submodule.span_induction with
      | mem y hy' =>
        obtain ⟨h, hh, rfl⟩ := hy'
        exact hgen g hg h hh
      | zero => simp
      | add y1 y2 _ _ h1 h2 =>
        simp only [Matrix.mul_add, map_add (f := _), h1, h2]
        abel
      | smul a y _ h1 =>
        simp only [Matrix.mul_smul, map_smul, h1, smul_add]
    | zero => simp
    | add x1 x2 _ _ h1 h2 =>
      simp only [Matrix.add_mul, map_add (f := _), h1, h2]
      abel
    | smul a x _ h1 =>
      simp only [Matrix.smul_mul, map_smul, h1, smul_add]
  obtain ⟨Y, hY⟩ := Det.derEv d hder
  refine ⟨-Y, fun g hg => ?_⟩
  have h1 := hY (D.r g) (D.ev g)
  rw [hdr g hg] at h1
  have h2 : z g = (Y * D.r g - D.r g * Y) * D.r g⁻¹ := by
    rw [← h1, Matrix.mul_assoc, ← D.r.map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
  rw [h2]
  simp only [dTw, one_smul, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rw [← D.r.map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
  abel
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SpanInt
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanImageDenominators
theorem UpperTheory.Reformulated.B.SpanImageDenominators.exists_ne_zero_smul_mem_span_image :
    ∀ {A F M N : Type} [inst : CommRing A]
    [IsDomain A] [inst_2 : Field F] [inst_3 : Algebra A F] [IsFractionRing A F] [inst_5 : AddCommGroup M]
    [inst_6 : _root_.Module A M] [inst_7 : AddCommGroup N] [inst_8 : _root_.Module A N] [inst_9 : _root_.Module F N]
    [IsScalarTower A F N] (φ : M →ₗ[A] N) (T : Set M),
    ∀ y ∈ Submodule.span F ((⇑φ : M → N) '' T),
      ∃ (d : A), d ≠ (0 : A) ∧ ∃ w ∈ Submodule.span A T, d • y = (φ : M → N) w := by
  intro A F M N _ _ _ _ _ _ _ _ _ _ _ φ T y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨1, one_ne_zero, m, Submodule.subset_span hm, one_smul _ _⟩
  | zero => exact ⟨1, one_ne_zero, 0, Submodule.zero_mem _, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨d, hd, w, hw, e⟩ := hx
    obtain ⟨d', hd', w', hw', e'⟩ := hz
    refine ⟨d * d', mul_ne_zero hd hd', d' • w + d • w',
      Submodule.add_mem _ (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hw'), ?_⟩
    rw [map_add (f := _), map_smul, map_smul, ← e, ← e', smul_add, smul_smul, smul_smul, mul_comm d' d]
  | smul c x _ hx =>
    obtain ⟨d, hd, w, hw, e⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) c
    refine ⟨b * d, mul_ne_zero (nonZeroDivisors.ne_zero b.2) hd, a • w,
      Submodule.smul_mem _ _ hw, ?_⟩
    have hab' : c * algebraMap A F b = algebraMap A F a := hab
    rw [map_smul, ← e, ← algebraMap_smul F ((b : A) * d), ← algebraMap_smul F a,
      ← algebraMap_smul F d, smul_smul, smul_smul, ← hab', map_mul]
    congr 1
    ring
end

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem UpperTheory.V.Pa.Det.exists_ne_zero_smul_mem_span_image {A F M N : Type} [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module F N]
    [IsScalarTower A F N] (φ : M →ₗ[A] N) (T : Set M) (y : N)
    (hy : y ∈ Submodule.span F (φ '' T)) :
    ∃ d : A, d ≠ 0 ∧ ∃ w ∈ Submodule.span A T, d • y = φ w :=
  _root_.UpperTheory.Reformulated.B.SpanImageDenominators.exists_ne_zero_smul_mem_span_image φ T y hy

theorem UpperTheory.V.Pa.Det.spanInt :
    ∀ {K ι : Type} [Field K] {n a : ℕ} (r : ι → Matrix (Fin n) (Fin n) (PowerSeries K)) (S : Set ι), Submodule.span (FractionRing (PowerSeries K)) ((fun i => (r i).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) '' S) = Ev (FractionRing (PowerSeries K)) (FractionRing (PowerSeries K)) n a → ∀ Z ∈ Ev (PowerSeries K) (PowerSeries K) n a, ∃ s : ℕ, (PowerSeries.X : PowerSeries K) ^ s • Z ∈ Submodule.span (PowerSeries K) (r '' S) := by
  intro K ι _ n a r S h Z hZ
  let φ : Matrix (Fin n) (Fin n) (PowerSeries K) →ₗ[PowerSeries K]
      Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K)) :=
    (Algebra.linearMap (PowerSeries K) (FractionRing (PowerSeries K))).mapMatrix
  have hφ : ∀ Y, φ Y = Y.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) := fun _ => rfl
  have hinj : Function.Injective φ :=
    Matrix.map_injective (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))
  have hmem : φ Z ∈ Submodule.span (FractionRing (PowerSeries K)) (φ '' (r '' S)) := by
    rw [Set.image_image]
    simp only [hφ]
    rw [h]
    intro i j
    refine ⟨fun _ => Submodule.mem_top, fun hij => ?_⟩
    have : Z i j = 0 := (Submodule.mem_bot _).1 ((hZ i j).2 hij)
    simp [this]
  obtain ⟨d, hd, w, hw, e⟩ := UpperTheory.V.Pa.Det.exists_ne_zero_smul_mem_span_image φ _ _ hmem
  rw [← map_smul] at e
  have e' := hinj e
  obtain ⟨s, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd
    (PowerSeries.X_irreducible (R := K))
  refine ⟨s, ?_⟩
  have : (PowerSeries.X : PowerSeries K) ^ s • Z = (↑u⁻¹ : PowerSeries K) • w := by
    rw [← e', smul_smul, Units.inv_mul_cancel_left]
  rw [this]
  exact Submodule.smul_mem _ _ hw
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.OmDense
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa.Det

open Polynomial

private noncomputable def dsc {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : R :=
  resultant M.charpoly (derivative M.charpoly) n n

private theorem dsc_map {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (φ : R →+* S) (M : Matrix (Fin n) (Fin n) R) :
    dsc (M.map φ) = φ (dsc M) := by
  unfold dsc
  rw [Matrix.charpoly_map, derivative_map, resultant_map_map]

private theorem dsc_ne_iff {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    dsc M ≠ 0 ↔ M.charpoly.Separable := by
  have hm : M.charpoly.Monic := Matrix.charpoly_monic M
  have hd : M.charpoly.natDegree = n := by simp [Matrix.charpoly_natDegree_eq_dim]
  have hle : (derivative M.charpoly).natDegree ≤ n :=
    (natDegree_derivative_le _).trans (by omega)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  have hc : M.charpoly.coeff n = 1 := by
    have := hm.coeff_natDegree
    rwa [hd] at this
  have h1 : dsc M = resultant M.charpoly (derivative M.charpoly) := by
    unfold dsc
    have := resultant_add_right_deg M.charpoly (derivative M.charpoly) n (derivative M.charpoly).natDegree k le_rfl
    rw [← hk, hc, one_pow, one_mul] at this
    rw [this, hd]
  rw [h1, ← isUnit_iff_ne_zero, isUnit_resultant_iff_isCoprime hm]
  rfl

private theorem sep_iff {A : Type} [CommRing A] [IsDomain A] {n : ℕ} (M : Matrix (Fin n) (Fin n) A) :
    (M.charpoly.map (algebraMap A (FractionRing A))).Separable ↔ dsc M ≠ 0 := by
  rw [← Matrix.charpoly_map, ← dsc_ne_iff, dsc_map]
  exact (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A)))

private theorem sep_open {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) :
    IsOpen {σ : F.G₀ | ((mat x.ρ σ).charpoly.map (algebraMap x.A (FractionRing x.A))).Separable} := by
  simp only [sep_iff]
  rw [isOpen_iff_mem_nhds]
  intro s hs
  have hN : ∃ N : ℕ, dsc (mat x.ρ s) ∉ maximalIdeal x.A ^ N := by
    by_contra hc
    push Not at hc
    have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal x.A) (maximalIdeal.isMaximal _).ne_top
    have h2 : dsc (mat x.ρ s) ∈ ⨅ N : ℕ, maximalIdeal x.A ^ N := Submodule.mem_iInf _ |>.2 hc
    rw [this] at h2
    exact hs (by simpa using h2)
  obtain ⟨N, hN⟩ := hN
  have hev : ∀ᶠ g in nhds s, ∀ i j, Ideal.Quotient.mk (maximalIdeal x.A ^ N) (mat x.ρ g i j)
      = Ideal.Quotient.mk (maximalIdeal x.A ^ N) (mat x.ρ s i j) := by
    simp only [Filter.eventually_all]
    intro i j
    exact (x.cont i j N).eventually_eq s
  filter_upwards [hev] with g hg h0
  apply hN
  have hM : (mat x.ρ g).map (Ideal.Quotient.mk (maximalIdeal x.A ^ N))
      = (mat x.ρ s).map (Ideal.Quotient.mk (maximalIdeal x.A ^ N)) := by
    ext i j; exact hg i j
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← dsc_map, ← hM, dsc_map, h0, map_zero]

end UpperTheory.V.Pa.Det

theorem UpperTheory.V.Pa.Det.omDense :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n h : ℕ} (x : Fin h → NP F n), (∀ i, (x i).N3) → (F.G' : Set F.G₀) ⊆ closure {σ : F.G₀ | σ ∈ F.G' ∧ ∀ i, ((mat (x i).ρ σ).charpoly.map (algebraMap (x i).A (FractionRing (x i).A))).Separable} := by
  intro l _ F n h x hx σ hσ
  rw [mem_closure_iff]
  intro U hU hσU
  have key : ∀ S : Finset (Fin h), ∃ τ ∈ U ∩ (F.G' : Set F.G₀), ∀ i ∈ S,
      ((mat (x i).ρ τ).charpoly.map (algebraMap (x i).A (FractionRing (x i).A))).Separable := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨σ, ⟨hσU, hσ⟩, by simp⟩
    | insert a S ha ih =>
      obtain ⟨τ, ⟨h1, h2⟩, h3⟩ := ih
      have ho : IsOpen (U ∩ ⋂ i ∈ S, {σ : F.G₀ | ((mat (x i).ρ σ).charpoly.map
          (algebraMap (x i).A (FractionRing (x i).A))).Separable}) :=
        hU.inter (isOpen_biInter_finset fun i _ => UpperTheory.V.Pa.Det.sep_open (x i))
      obtain ⟨τ', ⟨⟨g1, g2⟩, g3⟩, g4⟩ := hx a _ ho ⟨τ, ⟨h1, Set.mem_iInter₂.2 h3⟩, h2⟩
      refine ⟨τ', ⟨g1, g3⟩, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact g4
      · exact Set.mem_iInter₂.1 g2 i hi
  obtain ⟨τ, ⟨h1, h2⟩, h3⟩ := key Finset.univ
  exact ⟨τ, h1, h2, fun i => h3 i (Finset.mem_univ i)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ConjCont
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem adicCont_iff_eventually_sub_mem_pow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (f : Γ → R) :
    UpperTheory.V.Alg.AdicCont I f ↔ ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f y - f x ∈ I ^ N := by
  unfold UpperTheory.V.Alg.AdicCont
  simp only [IsLocallyConstant.iff_eventually_eq, Ideal.Quotient.eq]

private theorem eventually_mul_sub_mem_pow_of_eventually_sub_mem {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (f g : Γ → R)
    (hf : ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f y - f x ∈ I ^ N)
    (hg : ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, g y - g x ∈ I ^ N) :
    ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f y * g y - f x * g x ∈ I ^ N := by
  intro N x
  filter_upwards [hf N x, hg N x] with y h1 h2
  have e : f y * g y - f x * g x = f y * (g y - g x) + (f y - f x) * g x := by ring
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_right _ _ h1)

private theorem eventually_sum_sub_mem_pow_of_eventually_sub_mem {Γ R ι : Type} [TopologicalSpace Γ] [CommRing R] [Fintype ι] (I : Ideal R)
    (f : ι → Γ → R) (hf : ∀ i (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f i y - f i x ∈ I ^ N) :
    ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, (∑ i, f i y) - ∑ i, f i x ∈ I ^ N := by
  intro N x
  filter_upwards [Filter.eventually_all.2 (fun i => hf i N x)] with y hy
  rw [← Finset.sum_sub_distrib]
  exact Ideal.sum_mem _ (fun i _ => hy i)

private theorem eventually_sub_mem_maxIdeal_pow_of_const_mul {Γ K' : Type} [TopologicalSpace Γ] [Field K'] (c : PowerSeries K') (hc : c ≠ 0)
    (f : Γ → PowerSeries K')
    (h : ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, c * f y - c * f x ∈ maximalIdeal (PowerSeries K') ^ N) :
    ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f y - f x ∈ maximalIdeal (PowerSeries K') ^ N := by
  intro N x
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (fun h0 => hc (PowerSeries.order_eq_top.1 h0))
  filter_upwards [h (N + k) x] with y hy
  rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy ⊢
  rw [← mul_sub, PowerSeries.X_pow_dvd_iff] at hy
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  have h1 : ((N + k : ℕ) : ℕ∞) ≤ (c * (f y - f x)).order :=
    PowerSeries.le_order _ _ (fun i hi => hy i (by exact_mod_cast hi))
  rw [PowerSeries.order_mul, ← hk] at h1
  apply PowerSeries.coeff_of_lt_order
  by_cases h3 : (f y - f x).order = ⊤
  · rw [h3]
    exact ENat.coe_lt_top m
  · obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 h3
    rw [← hr] at h1 ⊢
    have h4 : N + k ≤ k + r := by exact_mod_cast h1
    exact_mod_cast (by omega : m < r)

theorem UpperTheory.V.Pa.Det.conjCont :
    ∀ {K K' G : Type} [Field K] [Field K'] [TopologicalSpace G] {n : ℕ} (j : PowerSeries K →+* PowerSeries K') (ρ : G → Matrix (Fin n) (Fin n) (PowerSeries K)) (Q : GL (Fin n) (FractionRing (PowerSeries K'))) (ρ' : G → Matrix (Fin n) (Fin n) (PowerSeries K')), IsLocalHom j → (∀ a b, AdicCont (maximalIdeal (PowerSeries K)) fun g => ρ g a b) → (∀ g, (ρ g).map ((algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))).comp j) * (Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) = (Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) * (ρ' g).map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K')))) → ∀ a b, AdicCont (maximalIdeal (PowerSeries K')) fun g => ρ' g a b := by
  intro K K' G _ _ _ n j ρ Q ρ' hj hρ hQ a b
  have hX : PowerSeries.X ∈ maximalIdeal (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.mem_span_singleton_self _
  have hjX : j PowerSeries.X ∈ maximalIdeal (PowerSeries K') := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hX (isUnit_of_map_unit j _ hu)
  have hjr : ∀ k l (N : ℕ) (x : G), ∀ᶠ y in nhds x,
      j (ρ y k l) - j (ρ x k l) ∈ maximalIdeal (PowerSeries K') ^ N := by
    intro k l N x
    filter_upwards [(adicCont_iff_eventually_sub_mem_pow _ _).1 (hρ k l) N x] with y hy
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy
    obtain ⟨t, ht⟩ := hy
    rw [← map_sub, ht, map_mul, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hjX N)
  obtain ⟨b1, hb1⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (PowerSeries K'))
    (fun p : Fin n × Fin n => (↑(Q⁻¹) : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) p.1 p.2)
  obtain ⟨b2, hb2⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (PowerSeries K'))
    (fun p : Fin n × Fin n => (↑Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) p.1 p.2)
  choose P hP using fun p => RingHom.mem_rangeS.1 (hb1 p)
  choose R hR using fun p => RingHom.mem_rangeS.1 (hb2 p)
  have hconj : ∀ g, (ρ' g).map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) =
      (↑(Q⁻¹) : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) *
        (ρ g).map ((algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))).comp j) *
        (↑Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) := by
    intro g
    rw [Matrix.mul_assoc, hQ g, ← Matrix.mul_assoc, Q.inv_mul, Matrix.one_mul]
  have key : ∀ g, ((b1 : PowerSeries K') * (b2 : PowerSeries K')) * ρ' g a b =
      ∑ l, ∑ k, P (a, k) * j (ρ g k l) * R (l, b) := by
    intro g
    apply IsFractionRing.injective (PowerSeries K') (FractionRing (PowerSeries K'))
    have e := congrFun (congrFun (hconj g) a) b
    simp only [Matrix.map_apply, Matrix.mul_apply, RingHom.comp_apply] at e
    rw [map_mul, e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hP, hR, Algebra.smul_def, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [adicCont_iff_eventually_sub_mem_pow]
  refine eventually_sub_mem_maxIdeal_pow_of_const_mul ((b1 : PowerSeries K') * (b2 : PowerSeries K'))
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero b1) (nonZeroDivisors.coe_ne_zero b2)) _ ?_
  simp only [key]
  refine eventually_sum_sub_mem_pow_of_eventually_sub_mem _ (fun l y => ∑ k, P (a, k) * j (ρ y k l) * R (l, b)) ?_
  intro l
  refine eventually_sum_sub_mem_pow_of_eventually_sub_mem _ (fun k y => P (a, k) * j (ρ y k l) * R (l, b)) ?_
  intro k
  refine eventually_mul_sub_mem_pow_of_eventually_sub_mem _ (fun y => P (a, k) * j (ρ y k l)) (fun _ => R (l, b)) ?_ (fun N x => by simp)
  exact eventually_mul_sub_mem_pow_of_eventually_sub_mem _ (fun _ => P (a, k)) (fun y => j (ρ y k l)) (fun N x => by simp) (hjr k l)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ClosedOfComb
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem char_of_padic {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Finite K] (f : ℤ_[l] →+* K) :
    (l : K) = 0 := by
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : p.Prime := CharP.char_is_prime K p
  have hpl : p = l := by
    by_contra hne
    have hunit : IsUnit (p : ℤ_[l]) := by
      by_contra hnu
      have hlt : ‖((p : ℤ) : ℤ_[l])‖ < 1 := by
        rw [Int.cast_natCast]
        exact PadicInt.mem_nonunits.mp hnu
      rw [PadicInt.norm_int_lt_one_iff_dvd, Int.natCast_dvd_natCast] at hlt
      exact hne ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp).mp hlt).symm
    have h := hunit.map f
    rw [map_natCast, CharP.cast_eq_zero] at h
    exact not_isUnit_zero h
  subst hpl
  exact CharP.cast_eq_zero K p

private theorem closed_of_comb {A G ι : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [TopologicalSpace G] [Fintype ι] (ρ : ι → G → A) (hρ : ∀ a, AdicCont (maximalIdeal A) (ρ a))
    (q : ι → FractionRing A) (ψ : G → A)
    (h : ∀ g, algebraMap A (FractionRing A) (ψ g) = ∑ a, q a * algebraMap A (FractionRing A) (ρ a g)) :
    IsClosed {g | ψ g = 1} := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A) Finset.univ q
  choose c hc using fun a => hb a (Finset.mem_univ a)
  have key : ∀ g, ψ g = 1 ↔ ∑ a, c a * ρ a g - (b : A) = 0 := by
    intro g
    have h1 : algebraMap A (FractionRing A) ((b : A) * ψ g) =
        algebraMap A (FractionRing A) (∑ a, c a * ρ a g) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_mul, h g, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, hc a, Algebra.smul_def, mul_assoc]
    have h2 := IsFractionRing.injective A (FractionRing A) h1
    have hb0 : (b : A) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    rw [sub_eq_zero, ← h2]
    constructor
    · intro h
      rw [h, mul_one]
    · intro h
      exact mul_left_cancel₀ hb0 (h.trans (mul_one _).symm)
  have hset : {g | ψ g = 1} =
      ⋂ N : ℕ, {g | Ideal.Quotient.mk (maximalIdeal A ^ N) (∑ a, c a * ρ a g - (b : A)) = 0} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Ideal.Quotient.eq_zero_iff_mem, key]
    constructor
    · intro h N
      rw [h]
      exact Ideal.zero_mem _
    · intro h
      have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top
      have hmem : ∑ a, c a * ρ a g - (b : A) ∈ ⨅ i, maximalIdeal A ^ i := Submodule.mem_iInf _ |>.mpr h
      rw [hbot] at hmem
      exact (Submodule.mem_bot A).mp hmem
  rw [hset]
  refine isClosed_iInter fun N => ?_
  have hF : IsLocallyConstant (fun g => fun a => Ideal.Quotient.mk (maximalIdeal A ^ N) (ρ a g)) := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro y
    have hy : (fun g => fun a => Ideal.Quotient.mk (maximalIdeal A ^ N) (ρ a g)) ⁻¹' {y} =
        ⋂ a, {g | Ideal.Quotient.mk (maximalIdeal A ^ N) (ρ a g) = y a} := by
      ext g
      simp [funext_iff]
    rw [hy]
    exact isOpen_iInter_of_finite fun a => (hρ a N).isOpen_fiber (y a)
  have hG := (hF.comp (fun w => ∑ a, Ideal.Quotient.mk (maximalIdeal A ^ N) (c a) * w a -
    Ideal.Quotient.mk (maximalIdeal A ^ N) (b : A))).isClopen_fiber 0
  convert hG.isClosed using 1
  ext g
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sub, map_sum, map_mul]

theorem UpperTheory.V.Pa.Det.psiMu :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (x : Point r) (v : F.Vl) (i : Fin n) (g : F.Gv v), g ∈ F.mu v → x.ψ v i g = 1 := by
  intro l _ F O _ _ _ n r x v i g hg
  have hl : (l : x.K) = 0 := char_of_padic ((algebraMap O x.K).comp (algebraMap ℤ_[l] O))
  haveI : CharP x.K l := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hl
  haveI : CharP (PowerSeries x.K) l :=
    charP_of_injective_algebraMap (algebraMap x.K (PowerSeries x.K)).injective l
  obtain ⟨P, hP⟩ := x.flag v
  have hclosed : IsClosed {s : F.Gv v | ((x.ψ v i s : (PowerSeries x.K)ˣ) : PowerSeries x.K) = 1} := by
    refine closed_of_comb (ι := Fin n × Fin n) (fun ab s => (mat x.ρ) (F.φ v s) ab.1 ab.2) ?_
      (fun ab => (P : Matrix (Fin n) (Fin n) _) i ab.1 * ((P⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) ab.2 i)
      _ ?_
    · intro ab N
      exact (x.cont ab.1 ab.2 N).comp_continuous (F.φ_cont v)
    · intro s
      have hs := (hP s).2 i
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at hs
      rw [← hs]
      simp only [pushRep, mat, MonoidHom.comp_apply, Units.coeHom_apply, Units.val_mul, Matrix.mul_apply,
        Finset.sum_mul, Fintype.sum_prod_type, Matrix.GeneralLinearGroup.map_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
  have hker : (commutator (F.Gv v)).topologicalClosure ≤ (x.ψ v i).ker := by
    apply Subgroup.topologicalClosure_minimal
    · exact Abelianization.commutator_subset_ker (x.ψ v i)
    · convert hclosed using 1
      ext s
      rw [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq, Units.val_eq_one]
  obtain ⟨k, hk⟩ := CommGroup.mem_primaryComponent.mp (Subgroup.mem_comap.mp hg)
  have hgk : g ^ l ^ k ∈ (commutator (F.Gv v)).topologicalClosure := by
    rw [← QuotientGroup.eq_one_iff]
    simpa using hk
  have h1 : x.ψ v i g ^ l ^ k = 1 := by
    rw [← map_pow]
    exact hker hgk
  have h2 : ((x.ψ v i g : PowerSeries x.K) - 1) ^ l ^ k = 0 := by
    rw [sub_pow_char_pow, one_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, sub_self]
  have h3 : (x.ψ v i g : PowerSeries x.K) - 1 = 0 := pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.mp h2
  exact Units.ext (sub_eq_zero.mp h3)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.EllClosed
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section
variable {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S}

private theorem ac_const (c : R) : AdicCont I fun _ : Γ => c := fun _ => IsLocallyConstant.const _

private theorem ac_add {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s + g s := by
  intro N
  have := (hf N).comp₂ (hg N) (· + ·)
  simpa [Function.comp_def, map_add (f := _)] using this

private theorem ac_mul {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s * g s := by
  intro N
  have := (hf N).comp₂ (hg N) (· * ·)
  simpa [Function.comp_def, map_mul] using this

private theorem ac_sum {ι : Type} (T : Finset ι) {f : ι → Γ → R} (hf : ∀ i, AdicCont I (f i)) :
    AdicCont I fun s => ∑ i ∈ T, f i s := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using ac_const (I := I) (Γ := Γ) 0
  | insert a T ha ih => simpa only [Finset.sum_insert ha] using ac_add (hf a) ih

private theorem ac_map (L : R → S) (hL : ∀ (N : ℕ) a b, a - b ∈ I ^ N → L a - L b ∈ J ^ N) {f : Γ → R}
    (hf : AdicCont I f) : AdicCont J fun s => L (f s) := by
  intro N
  have h : IsLocallyConstant fun s => Ideal.Quotient.mk (I ^ N) (f s) := hf N
  show IsLocallyConstant fun s => Ideal.Quotient.mk (J ^ N) (L (f s))
  rw [IsLocallyConstant.iff_eventually_eq] at h ⊢
  intro x
  filter_upwards [h x] with y hy
  rw [Ideal.Quotient.eq] at hy ⊢
  exact hL N _ _ hy

private theorem ac_hom (L : R →+* S) (t : R) {f : Γ → R}
    (hf : AdicCont (Ideal.span {t}) f) : AdicCont (Ideal.span {L t}) fun s => L (f s) := by
  refine ac_map L (fun N a b h => ?_) hf
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h ⊢
  obtain ⟨c, hc⟩ := h
  exact ⟨L c, by rw [← map_pow, ← map_mul, hc, map_sub]⟩

private theorem ac_eta {g : ℕ} (t : R) {f : Γ → DD R g}
    (hf : AdicCont (Ideal.span {(DD.C t : DD R g)}) f) : AdicCont (Ideal.span {t}) fun s => (f s).eta := by
  refine ac_map (fun x : DD R g => x.eta) (fun N a b h => ?_) hf
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  obtain ⟨c, hc⟩ := h
  refine ⟨c.eta, ?_⟩
  have e : (a - b).eta = a.eta - b.eta := rfl
  rw [← e, ← hc, ← map_pow, show (DD.C (t ^ N) : DD R g) = ⟨t ^ N, 0, 0, 0⟩ from rfl]
  simp

private theorem sum_comp {g : ℕ} {ι : Type} (T : Finset ι) (f : ι → DD R g) :
    (∑ i ∈ T, f i).a = ∑ i ∈ T, (f i).a ∧ (∀ j, (∑ i ∈ T, f i).ep j = ∑ i ∈ T, (f i).ep j) ∧
      (∀ j, (∑ i ∈ T, f i).ep' j = ∑ i ∈ T, (f i).ep' j) ∧ (∑ i ∈ T, f i).eta = ∑ i ∈ T, (f i).eta := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨rfl, fun _ => rfl, fun _ => rfl, rfl⟩
  | insert i T hi ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [Finset.sum_insert hi]
    exact ⟨by rw [← h1]; rfl, fun j => by rw [← h2 j]; rfl, fun j => by rw [← h3 j]; rfl, by rw [← h4]; rfl⟩

private theorem epM_eq {g n : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) R) (a b : Fin n) :
    DD.epM Z a b = ∑ j, DD.C (Z j a b) * (⟨0, Pi.single j 1, 0, 0⟩ : DD R g) := by
  classical
  have hC : ∀ c : R, (DD.C c : DD R g) = ⟨c, 0, 0, 0⟩ := fun _ => rfl
  obtain ⟨h1, h2, h3, h4⟩ := sum_comp Finset.univ (fun j => DD.C (Z j a b) * (⟨0, Pi.single j 1, 0, 0⟩ : DD R g))
  apply DD.ext
  · rw [h1]
    change (0 : R) = _
    simp [hC]
  · funext j
    rw [h2 j]
    change Z j a b = _
    simp [hC, Pi.single_apply]
  · funext j
    rw [h3 j]
    change (0 : R) = _
    simp [hC]
  · rw [h4]
    change (0 : R) = _
    simp [hC]

end

theorem UpperTheory.V.Pa.Det.ellClosed :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (z : F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)), z ∈ TwZ k x.A → IsClosed {σ : F.G₀ | ell k x.A σ z = 0} := by
  intro l _ F n x k z hz
  unfold TwZ at hz
  obtain ⟨-, hzc, -, -⟩ := hz
  have hmul : ∀ M N : F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g),
      (∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => M s i j) →
      (∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => N s i j) →
      ∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => (M s * N s) i j := by
    intro M N hM hN i j
    simp only [Matrix.mul_apply]
    exact ac_sum _ fun m => ac_mul (hM i m) (hN m j)
  have hρ : ∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => x.ρX (DD x.A k.g) s i j := by
    intro i j
    have h := x.cont i j
    rw [PowerSeries.maximalIdeal_eq_span_X] at h
    exact ac_hom DD.C x.t h
  have hκ : ∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)})
      fun s => DD.epM (fun m => (k.κ m s).map ⇑(algebraMap x.A x.A)) i j := by
    intro i j
    simp only [epM_eq]
    refine ac_sum _ fun m => ac_mul ?_ (ac_const _)
    have hm := k.mem m
    unfold SelZ at hm
    obtain ⟨-, hc, -⟩ := hm
    exact ac_hom DD.C x.t (hc i j)
  have hρ1 : ∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => k.ρ1 x.A s i j := by
    have := hmul (fun s => 1 + DD.epM fun m => (k.κ m s).map ⇑(algebraMap x.A x.A))
      (fun s => x.ρX (DD x.A k.g) s)
      (fun i j => by simpa only [Matrix.add_apply] using ac_add (ac_const _) (hκ i j)) hρ
    intro i j
    exact this i j
  have hprod := hmul z (fun s => k.ρ1 x.A s) hzc hρ1
  have htr : AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => (z s * k.ρ1 x.A s).trace := by
    simp only [Matrix.trace, Matrix.diag]
    exact ac_sum _ fun i => hprod i i
  have hf : AdicCont (Ideal.span {x.t}) fun s => ell k x.A s z := ac_eta x.t htr
  have sep : ∀ a : x.A, (∀ N : ℕ, Ideal.Quotient.mk (Ideal.span {x.t} ^ N) a = 0) → a = 0 := by
    intro a ha
    refine PowerSeries.ext fun m => ?_
    have h := ha (m + 1)
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
    obtain ⟨c, hc⟩ := h
    rw [show x.t = PowerSeries.X from rfl] at hc
    rw [← hc, PowerSeries.coeff_mul_X_pow']
    simp
  have hset : {σ : F.G₀ | ell k x.A σ z = 0} =
      ⋂ N : ℕ, {s | Ideal.Quotient.mk (Ideal.span {x.t} ^ N) (ell k x.A s z) = 0} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h N
      rw [h, map_zero]
    · exact sep _
  rw [hset]
  exact isClosed_iInter fun N =>
    ((show IsLocallyConstant fun s => Ideal.Quotient.mk (Ideal.span {x.t} ^ N) (ell k x.A s z) from hf N).isClopen_fiber 0).isClosed
end
