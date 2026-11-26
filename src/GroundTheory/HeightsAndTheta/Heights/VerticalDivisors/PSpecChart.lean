module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowFormHomog
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecAlgField

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecChartBack
section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecChartIso
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

set_option linter.unusedSectionVars false

namespace SpecChart

theorem solve_inl {L : Type*} [CommRing L] {u x ci S : L} (h : u * x + S = 0) (hc : ci * x = 1) :
    -(ci * S) = u := by
  linear_combination (-ci) * h + u * hc

theorem solve_inr {L : Type*} [CommRing L] {u x ci S : L} (h : u * x + S = 1) (hc : ci * x = 1) :
    ci * (1 - S) = u := by
  linear_combination (-ci) * h + u * hc

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
  (j : Fin n)

abbrev FreePar : Type := (Fin e × {m : Fin n // m ≠ j}) ⊕ {m : Fin n // m ≠ j}

def FreePar.val : FreePar e j → Par e n
  | .inl (i, m) => .inl (i, m.1)
  | .inr m => .inr m.1

abbrev Base : Type := ChartDomain.Base (integralModel I) j

abbrev Poly : Type := MvPolynomial (FreePar e j) (Base I j)

def toBase : MvPolynomial (Fin n) (𝓞 K) →+* Base I j :=
  (algebraMap _ (Base I j)).comp (Ideal.Quotient.mk (integralModel I))

def cx (l : Fin n) : Poly e I j := C (toBase I j (X l))

def cinv : Poly e I j := C (IsLocalization.Away.invSelf (Ideal.Quotient.mk (integralModel I) (X j)))

theorem cinv_mul_cx : cinv e I j * cx e I j j = 1 := by
  rw [cinv, cx, ← map_mul, toBase, RingHom.comp_apply, mul_comm, IsLocalization.Away.mul_invSelf, map_one]

def val : Par e n → Poly e I j
  | .inl (i, l) => if h : l = j then -(cinv e I j * ∑ m : {m : Fin n // m ≠ j}, X (.inl (i, m)) * cx e I j m)
      else X (.inl (i, ⟨l, h⟩))
  | .inr l => if h : l = j then cinv e I j * (1 - ∑ m : {m : Fin n // m ≠ j}, X (.inr m) * cx e I j m)
      else X (.inr ⟨l, h⟩)

theorem val_free (y : FreePar e j) : val e I j (FreePar.val e j y) = X y := by
  rcases y with ⟨i, m⟩ | m <;> simp [FreePar.val, val, m.2]

def σ : MvPolynomial (Par e n) (𝓞 K) →+* Poly e I j :=
  eval₂Hom (C.comp ((toBase I j).comp C)) (val e I j)

theorem σ_X (p : Par e n) : σ e I j (X p) = val e I j p := eval₂Hom_X' _ _ _

theorem σ_C (c : 𝓞 K) : σ e I j (C c) = C (toBase I j (C c)) := by simp [σ]

theorem sum_val_inl (i : Fin e) : ∑ m, val e I j (.inl (i, m)) * cx e I j m = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j]
  have h : ∀ m : {m : Fin n // m ≠ j}, val e I j (.inl (i, m.1)) = X (.inl (i, m)) := fun m => by
    simp [val, m.2]
  simp only [h]
  simp only [val, dite_true]
  linear_combination (-(∑ m : {m : Fin n // m ≠ j}, X (.inl (i, m)) * cx e I j m)) * cinv_mul_cx e I j

theorem sum_val_inr : ∑ m, val e I j (.inr m) * cx e I j m - 1 = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j]
  have h : ∀ m : {m : Fin n // m ≠ j}, val e I j (.inr m.1) = X (.inr m) := fun m => by
    simp [val, m.2]
  simp only [h]
  simp only [val, dite_true]
  linear_combination (1 - ∑ m : {m : Fin n // m ≠ j}, X (.inr m) * cx e I j m) * cinv_mul_cx e I j

variable (W : Ideal (MvPolynomial (Fin n) (𝓞 K)))

def Wb : Ideal (Base I j) :=
  (W.map (Ideal.Quotient.mk (integralModel I))).map (algebraMap _ (Base I j))

def Q : Ideal (Poly e I j) :=
  RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk (Wb I j W)) :
    Poly e I j →+* MvPolynomial (FreePar e j) (Base I j ⧸ Wb I j W))

theorem Q_eq : Q e I j W = (Wb I j W).map C := by
  rw [Q, MvPolynomial.ker_map, Ideal.mk_ker]

variable {I W}

theorem mem_of_mk_mem [W.IsPrime] (hPW : integralModel I ≤ W) {g : MvPolynomial (Fin n) (𝓞 K)}
    (h : Ideal.Quotient.mk (integralModel I) g ∈ W.map (Ideal.Quotient.mk _)) : g ∈ W := by
  have h2 : g ∈ Ideal.comap (Ideal.Quotient.mk (integralModel I)) (W.map (Ideal.Quotient.mk _)) := h
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.mpr hPW] at h2
  exact h2

theorem map_mk_isPrime [W.IsPrime] (hPW : integralModel I ≤ W) :
    (W.map (Ideal.Quotient.mk (integralModel I))).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

theorem disjoint_powers [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W) :
    Disjoint (↑(Submonoid.powers (Ideal.Quotient.mk (integralModel I) (X j))) :
        Set (MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I))
      ↑(W.map (Ideal.Quotient.mk (integralModel I))) := by
  rw [Set.disjoint_left]
  rintro _ ⟨k, rfl⟩ hk
  simp only [SetLike.mem_coe] at hk
  rw [← map_pow] at hk
  exact hXj (Ideal.IsPrime.mem_of_pow_mem ‹_› k (mem_of_mk_mem hPW hk))

theorem Wb_isPrime [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W) : (Wb I j W).IsPrime :=
  have := map_mk_isPrime hPW
  IsLocalization.isPrime_of_isPrime_disjoint _ _ _ this (disjoint_powers j hPW hXj)

theorem mem_of_toBase_mem [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W)
    {g : MvPolynomial (Fin n) (𝓞 K)} (h : toBase I j g ∈ Wb I j W) : g ∈ W := by
  have := map_mk_isPrime hPW
  have h2 := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers _) (Base I j) this
    (disjoint_powers j hPW hXj)
  apply mem_of_mk_mem hPW
  rw [← h2]
  exact h

theorem Q_isPrime [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W) : (Q e I j W).IsPrime := by
  have := Wb_isPrime j hPW hXj
  exact RingHom.ker_isPrime _

theorem C_toBase_mem_Q {g : MvPolynomial (Fin n) (𝓞 K)} (hg : g ∈ W) : C (toBase I j g) ∈ Q e I j W := by
  rw [Q_eq]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hg))

theorem mem_of_C_toBase_mem_Q [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W)
    {g : MvPolynomial (Fin n) (𝓞 K)} (h : C (toBase I j g) ∈ Q e I j W) : g ∈ W := by
  rw [Q, RingHom.mem_ker, map_C, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h
  exact mem_of_toBase_mem j hPW hXj h

variable {v : HeightOneSpectrum (𝓞 K)}

theorem toSecB_le : integralModel I ≤ RingHom.ker (toSecB e I v) := fun g hg => by
  rw [RingHom.mem_ker, toSecB, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg))

theorem secB_secForm (i : Fin e) :
    ∑ m, algebraMap (ParDVR e n v) (SecB e I v) (parY e n v (.inl (i, m))) * toSecB e I v (X m) = 0 := by
  have h : Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (secForm (parY e n v) i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h, secForm, linForm, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul]
  congr 1
  simp [toSecB]

theorem secB_chartForm :
    ∑ m, algebraMap (ParDVR e n v) (SecB e I v) (parY e n v (.inr m)) * toSecB e I v (X m) = 1 := by
  have h : Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (chartForm (parY e n v)) = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h, chartForm, linForm, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul]
  congr 1
  simp [toSecB]

variable (𝔫 : Ideal (SecB e I v)) [𝔫.IsPrime]

def quotToBn : MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I →+* Localization.AtPrime 𝔫 :=
  Ideal.Quotient.lift _ ((algebraMap (SecB e I v) (Localization.AtPrime 𝔫)).comp (toSecB e I v))
    (fun g hg => by rw [RingHom.comp_apply, RingHom.mem_ker.mp (toSecB_le e hg), map_zero])

theorem quotToBn_mk (g : MvPolynomial (Fin n) (𝓞 K)) :
    quotToBn e 𝔫 (Ideal.Quotient.mk _ g) = algebraMap _ (Localization.AtPrime 𝔫) (toSecB e I v g) :=
  Ideal.Quotient.lift_mk _ _ _

def parB (p : Par e n) : Localization.AtPrime 𝔫 :=
  algebraMap (SecB e I v) _ (algebraMap (ParDVR e n v) (SecB e I v) (parY e n v p))

variable {e j 𝔫}

def baseToBn (hj : toSecB e I v (X j) ∉ 𝔫) : Base I j →+* Localization.AtPrime 𝔫 :=
  IsLocalization.Away.lift (Ideal.Quotient.mk (integralModel I) (X j)) (g := quotToBn e 𝔫)
    (by
      rw [quotToBn_mk]
      exact IsLocalization.map_units (Localization.AtPrime 𝔫) (⟨toSecB e I v (X j), hj⟩ : 𝔫.primeCompl))

theorem baseToBn_toBase (hj : toSecB e I v (X j) ∉ 𝔫) (g : MvPolynomial (Fin n) (𝓞 K)) :
    baseToBn hj (toBase I j g) = algebraMap _ _ (toSecB e I v g) := by
  rw [toBase, RingHom.comp_apply, baseToBn, IsLocalization.Away.lift_eq, quotToBn_mk]

def Φ (hj : toSecB e I v (X j) ∉ 𝔫) : Poly e I j →+* Localization.AtPrime 𝔫 :=
  eval₂Hom (baseToBn hj) fun y => parB e 𝔫 (FreePar.val e j y)

theorem Φ_C (hj : toSecB e I v (X j) ∉ 𝔫) (b : Base I j) : Φ hj (C b) = baseToBn hj b := eval₂Hom_C _ _ _

theorem Φ_X (hj : toSecB e I v (X j) ∉ 𝔫) (y : FreePar e j) : Φ hj (X y) = parB e 𝔫 (FreePar.val e j y) :=
  eval₂Hom_X' _ _ _

theorem Φ_cx (hj : toSecB e I v (X j) ∉ 𝔫) (l : Fin n) :
    Φ hj (cx e I j l) = algebraMap _ _ (toSecB e I v (X l)) := by
  rw [cx, Φ_C, baseToBn_toBase]

theorem Φ_cinv_mul (hj : toSecB e I v (X j) ∉ 𝔫) :
    Φ hj (cinv e I j) * algebraMap _ _ (toSecB e I v (X j)) = 1 := by
  rw [← Φ_cx hj, ← map_mul, cinv_mul_cx, map_one]

theorem Φ_val (hj : toSecB e I v (X j) ∉ 𝔫) (p : Par e n) : Φ hj (val e I j p) = parB e 𝔫 p := by
  have hc := Φ_cinv_mul hj
  rcases p with ⟨i, l⟩ | l
  · by_cases hl : l = j
    · subst hl
      have h := congrArg (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)) (secB_secForm e (I := I) (v := v) i)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero, Fintype.sum_eq_add_sum_subtype_ne _ l] at h
      simp only [map_mul] at h
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [val, dite_true, map_neg, map_mul, map_sum, Φ_X, Φ_cx, FreePar.val, parB]
      exact solve_inl (L := Localization.AtPrime 𝔫) h hc
    · simp only [val, hl, dite_false, Φ_X, FreePar.val]
  · by_cases hl : l = j
    · subst hl
      have h := congrArg (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)) (secB_chartForm e (I := I) (v := v))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_one, Fintype.sum_eq_add_sum_subtype_ne _ l] at h
      simp only [map_mul] at h
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [val, dite_true, map_sub, map_one, map_mul, map_sum, Φ_X, Φ_cx, FreePar.val, parB]
      exact solve_inr (L := Localization.AtPrime 𝔫) h hc
    · simp only [val, hl, dite_false, Φ_X, FreePar.val]

theorem Φ_σ (hj : toSecB e I v (X j) ∉ 𝔫) :
    (Φ hj).comp (σ e I j) = (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)).comp
      ((algebraMap (ParDVR e n v) (SecB e I v)).comp (algebraMap _ (ParDVR e n v))) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, σ_C, Φ_C, baseToBn_toBase, toSecB_C]
  · intro p
    simp only [RingHom.comp_apply, σ_X, Φ_val, parB, parY]

end SpecChart

end

end GroundTheory.Heights₂.Heights.Vertical
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

set_option linter.unusedSectionVars false

namespace SpecChart

variable {K : Type} [Field K] [NumberField K] {n e : ℕ} {I : Ideal (MvPolynomial (Fin n) K)} {j : Fin n}
  {v : HeightOneSpectrum (𝓞 K)} {W : Ideal (MvPolynomial (Fin n) (𝓞 K))}

theorem Q_le_comap {𝔫 : Ideal (SecB e I v)} [𝔫.IsPrime] (hj : toSecB e I v (X j) ∉ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) :
    Q e I j W ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫)).comap (Φ hj) := by
  rw [Q_eq, Ideal.map_le_iff_le_comap, Ideal.comap_comap, Wb, Ideal.map_le_iff_le_comap,
    Ideal.comap_comap, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  intro w hw
  rw [Ideal.mem_comap]
  change Φ hj (C (toBase I j w)) ∈ _
  rw [Φ_C, baseToBn_toBase, IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔫) 𝔫, ← h𝔫]
  exact Ideal.mem_map_of_mem _ hw

theorem σ_not_mem {𝔫 : Ideal (SecB e I v)} [𝔫.IsPrime] (hj : toSecB e I v (X j) ∉ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) (s : MvPolynomial (Par e n) (𝓞 K))
    (hs : s ∈ (parPrime e n v).primeCompl) : σ e I j s ∉ Q e I j W := by
  intro hQ
  have h1 := Q_le_comap hj h𝔫 hQ
  rw [Ideal.mem_comap, ← RingHom.comp_apply, Φ_σ] at h1
  simp only [RingHom.comp_apply] at h1
  have hu : IsUnit (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) s) :=
    IsLocalization.map_units (ParDVR e n v) (⟨s, hs⟩ : (parPrime e n v).primeCompl)
  exact IsLocalRing.notMem_maximalIdeal.mpr ((hu.map _).map _) h1

section Back

variable [(Q e I j W).IsPrime]

def ρ (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) :
    ParDVR e n v →+* Localization.AtPrime (Q e I j W) :=
  IsLocalization.lift (M := (parPrime e n v).primeCompl)
    (g := (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))).comp (σ e I j)) fun s => by
      rw [RingHom.comp_apply, ← IsLocalRing.notMem_maximalIdeal,
        IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Q e I j W)]
      exact hσ s s.2

theorem ρ_algebraMap (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (s : MvPolynomial (Par e n) (𝓞 K)) :
    ρ hσ (algebraMap _ (ParDVR e n v) s) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (σ e I j s) :=
  IsLocalization.lift_eq _ _

theorem ρ_parY (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) (p : Par e n) :
    ρ hσ (parY e n v p) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (val e I j p) := by
  rw [parY, ρ_algebraMap, σ_X]

def G' (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) :
    MvPolynomial (Fin n) (ParDVR e n v) →+* Localization.AtPrime (Q e I j W) :=
  eval₂Hom (ρ hσ) fun l => algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (cx e I j l)

theorem G'_map (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (g : MvPolynomial (Fin n) (𝓞 K)) :
    G' hσ (g.map (algebraMap (𝓞 K) (ParDVR e n v))) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (C (toBase I j g)) := by
  have h : (G' hσ).comp (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v))) =
      (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))).comp (C.comp (toBase I j)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, map_C, G', eval₂Hom_C]
      rw [IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v),
        ρ_algebraMap, MvPolynomial.algebraMap_eq, σ_C]
    · intro l
      simp only [RingHom.comp_apply, map_X, G', eval₂Hom_X', cx]
  exact RingHom.congr_fun h g

theorem G'_kills (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) :
    secIdeal (modelR e I v) (parY e n v) ≤ RingHom.ker (G' hσ) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [modelR, Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker, G'_map, toBase, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero, map_zero, map_zero]
  · rw [Ideal.span_le, Set.range_subset_iff]
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [SetLike.mem_coe, RingHom.mem_ker, secForm, linForm, map_sum]
    simp only [map_mul, G', eval₂Hom_C, eval₂Hom_X', ρ_parY]
    have h := congrArg (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))) (sum_val_inl e I j i)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_mul, map_zero] using h
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [SetLike.mem_coe, RingHom.mem_ker, chartForm, linForm, map_sub, map_sum, map_one]
    simp only [map_mul, G', eval₂Hom_C, eval₂Hom_X', ρ_parY]
    have h := congrArg (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))) (sum_val_inr e I j)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_mul, map_sub, map_one, map_zero] using h

def G (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) :
    SecB e I v →+* Localization.AtPrime (Q e I j W) :=
  Ideal.Quotient.lift _ (G' hσ) fun _ ha => RingHom.mem_ker.mp (G'_kills hσ ha)

theorem G_toSecB (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (g : MvPolynomial (Fin n) (𝓞 K)) : G hσ (toSecB e I v g) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (C (toBase I j g)) := by
  rw [toSecB, RingHom.comp_apply, G, Ideal.Quotient.lift_mk, G'_map]

theorem G_algebraMap (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (r : ParDVR e n v) : G hσ (algebraMap _ (SecB e I v) r) = ρ hσ r := by
  rw [← Ideal.Quotient.mk_algebraMap, G, Ideal.Quotient.lift_mk, MvPolynomial.algebraMap_eq, G', eval₂Hom_C]

theorem G_mem (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    {𝔫 : Ideal (SecB e I v)} (h𝔫 : W.map (toSecB e I v) = 𝔫) {b : SecB e I v} (hb : b ∈ 𝔫) :
    G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) := by
  rw [← h𝔫] at hb
  have h : W.map (toSecB e I v) ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W))).comap (G hσ) := by
    rw [Ideal.map_le_iff_le_comap]
    intro w hw
    rw [Ideal.mem_comap, Ideal.mem_comap, G_toSecB, IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Q e I j W)]
    exact C_toBase_mem_Q e j hw
  exact h hb

theorem mem_of_toSecB_mem [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    {𝔫 : Ideal (SecB e I v)} (h𝔫 : W.map (toSecB e I v) = 𝔫) {g : MvPolynomial (Fin n) (𝓞 K)}
    (hg : toSecB e I v g ∈ 𝔫) : g ∈ W := by
  have h := G_mem hσ h𝔫 hg
  rw [G_toSecB, IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Q e I j W)] at h
  exact mem_of_C_toBase_mem_Q e j hPW hXj h

theorem mem_of_G_mem (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    {𝔫 : Ideal (SecB e I v)} [𝔫.IsMaximal] (h𝔫 : W.map (toSecB e I v) = 𝔫) {b : SecB e I v}
    (hb : G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W))) : b ∈ 𝔫 := by
  have h : 𝔫 = (IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W))).comap (G hσ) :=
    Ideal.IsMaximal.eq_of_le ‹_› (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
      (fun _ hb => G_mem hσ h𝔫 hb)
  rw [h]
  exact hb

variable {𝔫 : Ideal (SecB e I v)} [𝔫.IsPrime]

def Gloc (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫) :
    Localization.AtPrime 𝔫 →+* Localization.AtPrime (Q e I j W) :=
  IsLocalization.lift (M := 𝔫.primeCompl) (g := G hσ) fun b =>
    IsLocalRing.notMem_maximalIdeal.mp fun h => b.2 (hG _ h)

theorem Gloc_algebraMap (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (b : SecB e I v) : Gloc hσ hG (algebraMap _ _ b) = G hσ b :=
  IsLocalization.lift_eq _ _

theorem Gloc_max (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) {x : Localization.AtPrime 𝔫}
    (hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫)) :
    Gloc hσ hG x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal] at hx
  have h : 𝔫.map (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)) ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W))).comap (Gloc hσ hG) := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, Ideal.mem_comap, Gloc_algebraMap]
    exact G_mem hσ h𝔫 hb
  exact h hx

theorem Gloc_Φ (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫) :
    (Gloc hσ hG).comp (Φ hj) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, Φ_C]
    have h : (Gloc hσ hG).comp (baseToBn hj) =
        (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))).comp C := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (integralModel I) (X j)))
      apply Ideal.Quotient.ringHom_ext
      refine RingHom.ext fun g => ?_
      change Gloc hσ hG (baseToBn hj (toBase I j g)) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (C (toBase I j g))
      rw [baseToBn_toBase, Gloc_algebraMap, G_toSecB]
    exact RingHom.congr_fun h b
  · intro y
    simp only [RingHom.comp_apply, Φ_X, parB, Gloc_algebraMap, G_algebraMap, ρ_parY, val_free]

theorem Φ_isUnit (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) (c : Poly e I j) (hc : c ∈ (Q e I j W).primeCompl) :
    IsUnit (Φ hj c) := by
  by_contra hu
  rw [← IsLocalRing.notMem_maximalIdeal, not_not] at hu
  have h2 := Gloc_max hσ hG h𝔫 hu
  rw [← RingHom.comp_apply, Gloc_Φ, IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Q e I j W)] at h2
  exact hc h2

def Φloc (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : Localization.AtPrime (Q e I j W) →+* Localization.AtPrime 𝔫 :=
  IsLocalization.lift (M := (Q e I j W).primeCompl) (g := Φ hj) fun c => Φ_isUnit hj hσ hG h𝔫 c c.2

theorem Φloc_algebraMap (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) (c : Poly e I j) :
    Φloc hj hσ hG h𝔫 (algebraMap _ _ c) = Φ hj c :=
  IsLocalization.lift_eq _ _

theorem Gloc_Φloc (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : (Gloc hσ hG).comp (Φloc hj hσ hG h𝔫) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Q e I j W).primeCompl
  refine RingHom.ext fun c => ?_
  simp only [RingHom.comp_apply, Φloc_algebraMap, RingHom.id_apply]
  rw [← RingHom.comp_apply, Gloc_Φ]

theorem Φloc_Gloc (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : (Φloc hj hσ hG h𝔫).comp (Gloc hσ hG) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext 𝔫.primeCompl
  have hρ : (Φloc hj hσ hG h𝔫).comp (ρ hσ) =
      (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)).comp (algebraMap (ParDVR e n v) (SecB e I v)) := by
    apply IsLocalization.ringHom_ext (parPrime e n v).primeCompl
    refine RingHom.ext fun s => ?_
    simp only [RingHom.comp_apply, ρ_algebraMap, Φloc_algebraMap]
    rw [← RingHom.comp_apply (Φ hj), Φ_σ]
    rfl
  have h : (Φloc hj hσ hG h𝔫).comp (G hσ) = algebraMap (SecB e I v) (Localization.AtPrime 𝔫) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      have := RingHom.congr_fun hρ r
      simp only [RingHom.comp_apply] at this ⊢
      rw [G, Ideal.Quotient.lift_mk, G', eval₂Hom_C, this, ← Ideal.Quotient.mk_algebraMap,
        MvPolynomial.algebraMap_eq]
    · intro l
      simp only [RingHom.comp_apply]
      rw [G, Ideal.Quotient.lift_mk, G', eval₂Hom_X', Φloc_algebraMap, Φ_cx]
      simp [toSecB]
  refine RingHom.ext fun b => ?_
  simp only [RingHom.comp_apply, Gloc_algebraMap, RingHom.id_apply]
  exact RingHom.congr_fun h b

theorem quotToBn_flat (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : RingHom.Flat (R := MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I) (S := Localization.AtPrime 𝔫) (quotToBn e 𝔫) := by
  have h : quotToBn e 𝔫 = (Φloc hj hσ hG h𝔫).comp
      ((algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))).comp
        ((C : Base I j →+* Poly e I j).comp
          (algebraMap (MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I) (Base I j)))) := by
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun g => ?_
    change quotToBn e 𝔫 (Ideal.Quotient.mk _ g) =
      Φloc hj hσ hG h𝔫 (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (C (toBase I j g)))
    rw [quotToBn_mk, Φloc_algebraMap, Φ_C, baseToBn_toBase]
  have hbij : Function.Bijective (Φloc hj hσ hG h𝔫) :=
    Function.bijective_iff_has_inverse.mpr ⟨Gloc hσ hG,
      fun x => RingHom.congr_fun (Gloc_Φloc hj hσ hG h𝔫) x,
      fun y => RingHom.congr_fun (Φloc_Gloc hj hσ hG h𝔫) y⟩
  have h1 : (algebraMap (MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I) (Base I j)).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (Base I j) (Submonoid.powers (Ideal.Quotient.mk (integralModel I) (X j))))
  have h2 : (C : Base I j →+* Poly e I j).Flat := by
    rw [← MvPolynomial.algebraMap_eq]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have h3 : RingHom.Flat (R := Poly e I j) (S := Localization.AtPrime (Q e I j W))
      (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))) :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization.AtPrime (Q e I j W)) (Q e I j W).primeCompl)
  rw [h]
  exact RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.comp h1 h2) h3) (RingHom.Flat.of_bijective hbij)

end Back

theorem contraction_and_flat [W.IsPrime] (𝔫 : Ideal (SecB e I v)) [𝔫.IsMaximal]
    (hPW : integralModel I ≤ W) (h𝔫 : W.map (toSecB e I v) = 𝔫) :
    (∀ g, toSecB e I v g ∈ 𝔫 → g ∈ W) ∧ RingHom.Flat (R := MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I) (S := Localization.AtPrime 𝔫) (quotToBn e 𝔫) := by
  obtain ⟨j, hj⟩ := exists_secCoord_not_mem e I v 𝔫 (Ideal.IsMaximal.ne_top ‹_›)
  have hXj : X j ∉ W := fun h => hj (h𝔫 ▸ Ideal.mem_map_of_mem _ h)
  have := Q_isPrime e j hPW hXj
  have hσ := σ_not_mem hj h𝔫
  have hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫 :=
    fun b hb => mem_of_G_mem hσ h𝔫 hb
  exact ⟨fun g hg => mem_of_toSecB_mem hPW hXj hσ h𝔫 hg, quotToBn_flat hj hσ hG h𝔫⟩

end SpecChart

end

end GroundTheory.Heights₂.Heights.Vertical
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem SpecChart.proof : SpecChart.Statement := by
  intro K _ _ n e I v _ 𝔫 W _ hW h𝔫
  have := 𝔫.isMaximal
  have hPW : integralModel I ≤ W := le_trans le_sup_left hW.1.1.2
  have h𝔫' : W.map (toSecB e I v) = 𝔫.asIdeal := by rw [← secIdealOf_eq_map]; exact h𝔫
  obtain ⟨hcontr, hflat⟩ := SpecChart.contraction_and_flat 𝔫.asIdeal hPW h𝔫'
  have hunit : ∀ s : W.primeCompl, IsUnit (((algebraMap (SecB e I v)
      (Localization.AtPrime 𝔫.asIdeal)).comp (toSecB e I v)) s) := fun s =>
    IsLocalization.map_units (Localization.AtPrime 𝔫.asIdeal)
      (⟨toSecB e I v s, fun h => s.2 (hcontr _ h)⟩ : 𝔫.asIdeal.primeCompl)
  let ψ0 : Localization.AtPrime W →+* Localization.AtPrime 𝔫.asIdeal :=
    IsLocalization.lift (M := W.primeCompl) hunit
  have hψ0 : ∀ g, ψ0 (algebraMap _ (Localization.AtPrime W) g) =
      algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal) (toSecB e I v g) :=
    fun g => IsLocalization.lift_eq hunit g
  have hker : (integralModel I).map (algebraMap _ (Localization.AtPrime W)) ≤ RingHom.ker ψ0 := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker, hψ0, RingHom.mem_ker.mp (SpecChart.toSecB_le e hg), map_zero]
  have hker' : ∀ a ∈ (integralModel I).map (algebraMap _ (Localization.AtPrime W)), ψ0 a = 0 :=
    fun a ha => RingHom.mem_ker.mp (hker ha)
  let ψ := Ideal.Quotient.lift _ ψ0 hker'
  have hψ : ∀ g, ψ (Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime W) g)) =
      algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal) (toSecB e I v g) := fun g => by
    show Ideal.Quotient.lift _ ψ0 hker' (Ideal.Quotient.mk _ _) = _
    rw [Ideal.Quotient.lift_mk, hψ0]
  have hmax : (IsLocalRing.maximalIdeal (Localization.AtPrime W)).map (ψ.comp (Ideal.Quotient.mk _)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫.asIdeal) := by
    have hcomp : (ψ.comp (Ideal.Quotient.mk _)).comp (algebraMap _ (Localization.AtPrime W)) =
        (algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)).comp (toSecB e I v) :=
      RingHom.ext fun g => hψ g
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := W), Ideal.map_map, hcomp, ← Ideal.map_map, h𝔫',
      Localization.AtPrime.map_eq_maximalIdeal]
  refine ⟨ψ, fun g => ?_, ?_, ?_, hmax⟩
  · rw [hψ]
    rfl
  · exact ((IsLocalRing.local_hom_tfae (ψ.comp (Ideal.Quotient.mk _))).out 3 1).mp hmax.le
  · have := SpecChart.isLocalization_quot W (integralModel I)
    refine SpecChart.flat_of_isLocalization_comp (R := MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I)
      (S := Localization.AtPrime W ⧸ (integralModel I).map (algebraMap _ (Localization.AtPrime W)))
      (T := Localization.AtPrime 𝔫.asIdeal) (W.primeCompl.map (Ideal.Quotient.mk (integralModel I))) ψ ?_
    have h : ψ.comp (algebraMap (MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I)
        (Localization.AtPrime W ⧸ (integralModel I).map (algebraMap _ (Localization.AtPrime W)))) =
        SpecChart.quotToBn e 𝔫.asIdeal := by
      apply Ideal.Quotient.ringHom_ext
      refine RingHom.ext fun g => ?_
      simp only [RingHom.comp_apply]
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient, hψ, SpecChart.quotToBn_mk]
    rw [h]
    exact hflat

end

end GroundTheory.Heights₂.Heights.Vertical
