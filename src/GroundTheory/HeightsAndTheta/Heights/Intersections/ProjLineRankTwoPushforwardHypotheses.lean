module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedG
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Pull

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]

def pullHerm {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) (A : HermLine ι) :
    HermLine ι' where
  a := pullDeg κ A.a
  h z := A.h fun p => z (v p)
  pos z hz := A.pos _ fun k => by
    obtain ⟨i', hi'⟩ := hz (κ k)
    obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
    obtain ⟨pk, pi⟩ := p
    simp only at h2
    subst h2
    exact ⟨pi, by rw [hp]; exact hi'⟩
  smul c z hc := by
    show A.h (fun p => c (v p).1 * z (v p)) = (∏ k', ‖c k'‖ ^ pullDeg κ A.a k') * A.h (fun p => z (v p))
    have e1 : (fun p => c (v p).1 * z (v p)) = fun p : Σ k, ι k => (fun k => c (κ k)) p.1 * z (v p) := by
      funext p
      rw [hv.2.2.1 p]
    rw [e1, A.smul _ _ fun k => hc (κ k)]
    congr 1
    refine Fintype.prod_of_injective κ hv.1 _ _ (fun k' hk' => ?_) (fun k => ?_)
    · rw [pullDeg, Function.extend_apply' _ _ _ (by simpa using hk')]
      simp
    · rw [pullDeg, hv.1.extend_apply]

omit [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem isPullHerm_pullHerm {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (A : HermLine ι) : IsPullHerm κ v A (pullHerm hv A) :=
  ⟨rfl, fun _ => rfl⟩

end Pull

section Bundles

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev FnField (P : Ideal (MRing ι)) : Type := FractionRing (MRing ι ⧸ P)

def genPt (P : Ideal (MRing ι)) : (Σ k, ι k) → FnField P :=
  fun p => algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P (X p))

abbrev PBlk (ι : K → Type) (N1 : ℕ) : K ⊕ Unit → Type := Sum.elim ι fun _ => Fin N1

abbrev PluckerBlocks (N1 n : ℕ) : Fin (n - 1) → Type := fun j => {S : Finset (Fin N1) // S.card = j + 1}

def flagMinor {R : Type} [CommRing R] {n N1 : ℕ} (M : Matrix (Fin n) (Fin N1) R) (j : Fin (n - 1))
    (S : PluckerBlocks N1 n j) : R :=
  (M.submatrix (Fin.castLE (by have := j.2; omega)) (S.1.orderEmbOfFin S.2)).det

def genMat (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) R) :=
  Matrix.of fun a b => X (a, b)

def flagDim (n : ℕ) : ℕ := n * (n - 1) / 2

end Bundles

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.LocRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def locRing {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)) :
    Subring (FractionRing (MRing ι ⧸ P)) :=
  Subring.closure {x | ∃ (u v : MRing ι) (a : K → ℕ)
    (hv : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P)),
    v ∉ W ∧ IsMultiHomog u a ∧ IsMultiHomog v a ∧
      x = IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hv⟩}

def locIdeal {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι))
    (y : FractionRing (MRing ι ⧸ P)) : Ideal (locRing P W) :=
  Ideal.span {z | (z : FractionRing (MRing ι ⧸ P)) = y}

theorem locIdeal_eq_span {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)}
    {y : FractionRing (MRing ι ⧸ P)} (hy : y ∈ locRing P W) :
    locIdeal P W y = Ideal.span {(⟨y, hy⟩ : locRing P W)} := by
  unfold locIdeal
  congr 1
  ext z
  simp only [Set.mem_singleton_iff]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAbsIntegrable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def PtsAbsIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (A : HermLine ι)
    (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSectionOn P A s →
    Integrable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, |sheetDensity P Ψ (pot L) (logNorm A s) y w|)

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Cycles

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_of_mem_divSupp' {P W : Ideal (MRing ι)} {f : MRing ι} (hW : W ∈ divSupp P f) : f ∈ W :=
  hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))

theorem mem_divSupp_mul_left' {P W : Ideal (MRing ι)} (hP : P.IsPrime) {f g : MRing ι}
    (hgP : g ∉ P) (hW : W ∈ divSupp P f) : W ∈ divSupp P (f * g) := by
  refine ⟨⟨⟨hW.1.1.1, (sup_span_mul_le P f g).trans hW.1.1.2⟩, fun Q hQ hQW => ?_⟩, hW.2⟩
  have hfg : f * g ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rcases hQ.1.mem_or_mem hfg with hf | hg
  · exact hW.1.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2) (Ideal.span_singleton_le_iff_mem _ |>.mpr hf)⟩
      hQW
  · exact (eq_of_le_of_mem_minimalPrimes hP hW.1 hQ.1 (le_sup_left.trans hQ.2) hg hgP hQW).ge

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_divSupp_of_mul' {P W : Ideal (MRing ι)} {f g : MRing ι}
    (hW : W ∈ divSupp P (f * g)) (hf : f ∈ W) : W ∈ divSupp P f :=
  ⟨⟨⟨hW.1.1.1, sup_le (le_sup_left.trans hW.1.1.2) (Ideal.span_singleton_le_iff_mem _ |>.mpr hf)⟩,
    fun _ hQ hQW => hW.1.2 ⟨hQ.1, (sup_span_mul_le P f g).trans hQ.2⟩ hQW⟩, hW.2⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem multAt_eq' (J W : Ideal (MRing ι)) (hW : W.IsPrime) :
    multAt J W = (ReciprocityTheory.ChartRestriction.G.AI.locLen (MRing ι ⧸ J) ⟨W, hW⟩).toNat := by
  simp [multAt, hW, ReciprocityTheory.ChartRestriction.G.AI.locLen]

theorem divCycle_mul' {P : Ideal (MRing ι)} (hP : P.IsPrime) {f g : MRing ι}
    (hf : f ∉ P) (hg : g ∉ P) : divCycle P (f * g) = divCycle P f + divCycle P g := by
  classical
  ext W
  simp only [Finsupp.add_apply, divCycle, Finsupp.ofSupportFinite_coe]
  by_cases h : W ∈ divSupp P (f * g)
  · have hWp := h.1.1.1
    have h' : W ∈ divSupp P (g * f) := by rwa [mul_comm]
    have key := locLen_mul hP hf g ⟨W, hWp⟩
    have hfin := locLen_ne_top h.1
    rw [key] at hfin
    rw [if_pos h, multAt_eq' _ _ hWp, key]
    by_cases hfW : f ∈ W <;> by_cases hgW : g ∈ W
    · rw [if_pos (mem_divSupp_of_mul' h hfW), if_pos (mem_divSupp_of_mul' h' hgW),
        multAt_eq' _ _ hWp, multAt_eq' _ _ hWp, ENat.toNat_add (WithTop.add_ne_top.mp hfin).1
          (WithTop.add_ne_top.mp hfin).2, add_comm]
    · rw [if_pos (mem_divSupp_of_mul' h hfW), if_neg fun h2 => hgW (mem_of_mem_divSupp' h2),
        multAt_eq' _ _ hWp, locLen_quot_eq_zero _ hgW, zero_add, add_zero]
    · rw [if_neg fun h2 => hfW (mem_of_mem_divSupp' h2), if_pos (mem_divSupp_of_mul' h' hgW),
        multAt_eq' _ _ hWp, locLen_quot_eq_zero (V := P) (g := f) _ hfW, add_zero, zero_add]
    · exact absurd (hWp.mem_or_mem (mem_of_mem_divSupp' h)) (by tauto)
  · rw [if_neg h, if_neg fun h2 => h (mem_divSupp_mul_left' hP hg h2),
      if_neg fun h2 => h (by rw [mul_comm]; exact mem_divSupp_mul_left' hP hf h2)]


open Classical in
def cycWeight (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) {n : ℕ}
    (L : Fin n → HermLine ι) (W : Ideal (MRing ι)) : ℝ :=
  if IsHorizontal W then I W n L else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)

theorem cycR_eq_sum (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) :
    cycR I P L s = (divCycle P s).sum fun W m => (m : ℝ) * cycWeight I L W := by
  classical
  unfold cycR
  rw [finsum_mem_def, finsum_eq_sum_of_support_subset _ (s := (divCycle P s).support)]
  · refine Finset.sum_congr rfl fun W _ => ?_
    by_cases h : W ∈ divSupp P s
    · simp [Set.indicator, h, divCycle, Finsupp.ofSupportFinite_coe, cycWeight]
    · simp [Set.indicator, h, divCycle, Finsupp.ofSupportFinite_coe]
  · intro W hW
    rw [Function.mem_support] at hW
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    apply hW
    by_cases h : W ∈ divSupp P s
    · have : multAt (P ⊔ Ideal.span {s}) W = 0 := by
        simpa [divCycle, Finsupp.ofSupportFinite_coe, h] using h0
      simp [Set.indicator, h, this]
    · simp [Set.indicator, h]

theorem cycR_mul (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) {P : Ideal (MRing ι)}
    (hP : P.IsPrime) {n : ℕ} (L : Fin n → HermLine ι) {s t : MRing ι} (hs : s ∉ P) (ht : t ∉ P) :
    cycR I P L (s * t) = cycR I P L s + cycR I P L t := by
  rw [cycR_eq_sum, cycR_eq_sum, cycR_eq_sum, divCycle_mul' hP hs ht]
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)

end Cycles

section NoHorizontal

theorem not_isHorizontal_of_dimOne (h0 : ArithVarZeroStatement) {P : Ideal (MRing ι)} {A : HermLine ι}
    {s : MRing ι} {W : Ideal (MRing ι)} (hP : IsArithVar P 1) (hs : IsSectionOn P A s)
    (hW : W ∈ divSupp P s) : ¬ IsHorizontal W := fun hh =>
  h0 K ι W ((divSuppArith K ι P 0 A s W hP hs hW).1 hh)

theorem eval_ne_zero_of_dimOne (h0 : ArithVarZeroStatement) {P : Ideal (MRing ι)} {A : HermLine ι}
    {s : MRing ι} (hP : IsArithVar P 1) (hs : IsSectionOn P A s) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) : eval z (map (Int.castRingHom ℂ) s) ≠ 0 := by
  intro hzero
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hQ : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hle : P ⊔ Ideal.span {s} ≤ RingHom.ker φ := by
    refine sup_le (fun f hf => ?_) ?_
    · rw [RingHom.mem_ker]
      exact hz.2 f hf
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
      exact hzero
  obtain ⟨W, hW, hWQ⟩ := Ideal.exists_minimalPrimes_le hle
  have hrel : IsRelevant W := fun k => by
    obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, fun hX => hi ?_⟩
    have h1 := hWQ hX
    rw [RingHom.mem_ker] at h1
    simpa [φ] using h1
  have hhor : IsHorizontal W := by
    unfold IsHorizontal
    refine eq_bot_iff.mpr fun n hn => ?_
    rw [Ideal.mem_comap] at hn
    have h1 := hWQ hn
    rw [RingHom.mem_ker] at h1
    simp [φ] at h1
    simp [h1]
  exact not_isHorizontal_of_dimOne h0 hP hs ⟨hW, hrel⟩ hhor

end NoHorizontal

section Integral

theorem ptsIntegral_add_of_dimOne (hFF : FibreFiniteStatement) {P : Ideal (MRing ι)}
    (hP : IsArithVar P 1) (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) {g g₁ g₂ : ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ z ∈ mcPts P, g z = g₁ z + g₂ z) :
    ptsIntegral P φ g = ptsIntegral P φ g₁ + ptsIntegral P φ g₂ := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [MeasureTheory.integral_unique, MeasureTheory.integral_unique, MeasureTheory.integral_unique,
      ← smul_add]
    congr 1
    have hfin : ∀ y, (ReciprocityTheory.ChartRestriction.G.Geo.fibre P hΨ.choose y).Finite := hFF K ι P 0 hΨ.choose hP hΨ.choose_spec
    refine Eq.trans ?_ (finsum_mem_add_distrib' ((hfin _).subset Set.inter_subset_left)
      ((hfin _).subset Set.inter_subset_left))
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · have hz : ∀ y : Fin 0 → ℂ, hγ.choose y ∈ mcPts P := fun y =>
        (Subsingleton.elim _ y) ▸ hγ.choose_spec.2.self_of_nhds.2.1
      rw [h _ (hz _), add_mul]
    · simp
  · simp

end Integral

theorem SpecIntHeightFormula.proof (h0 : ArithVarZeroStatement) : SpecIntHeightFormula.Statement := by
  intro K _ ι _ I P A s hP _ hs
  rw [recR_eq]
  congr 1
  unfold cycR vertR
  refine finsum_mem_congr rfl fun W hW => ?_
  simp [not_isHorizontal_of_dimOne h0 hP hs hW]

theorem cycR_eq_vertR_of_dimOne (h0 : ArithVarZeroStatement) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    {P : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι} (hP : IsArithVar P 1) (hs : IsSectionOn P A s) :
    cycR I P (Fin.elim0 : Fin 0 → HermLine ι) s = vertR P (Fin.elim0 : Fin 0 → HermLine ι) s := by
  unfold cycR vertR
  refine finsum_mem_congr rfl fun W hW => ?_
  simp [not_isHorizontal_of_dimOne h0 hP hs hW]

theorem RegularityIndependence.proof (h0 : ArithVarZeroStatement) (hFF : FibreFiniteStatement)
    (hPF : RegularityProductFormula.Statement) : RegularityIndependence.Statement := by
  intro K _ ι _ I P A s t hP hs ht
  obtain ⟨a, ha, hsa, hsP⟩ := id hs
  obtain ⟨b, hb, htb, htP⟩ := id ht
  have hab : b = a := funext fun k => by exact_mod_cast (hb k).symm.trans (ha k)
  subst hab
  have hφ : (fun (j : Fin 0) (z : (Σ k, ι k) → ℂ) => Real.log (((Fin.elim0 : Fin 0 → HermLine ι) j).h z)) =
      (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) := funext fun j => j.elim0
  have hsplit : arInt P s A (Fin.elim0 : Fin 0 → HermLine ι) =
      ptsIntegral P (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ)
        (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ / ‖eval z (map (Int.castRingHom ℂ) t)‖)) +
      arInt P t A (Fin.elim0 : Fin 0 → HermLine ι) := by
    unfold arInt
    rw [hφ]
    refine ptsIntegral_add_of_dimOne hFF hP _ fun z hz => ?_
    have hs0 := norm_ne_zero_iff.mpr (eval_ne_zero_of_dimOne h0 hP hs hz)
    have ht0 := norm_ne_zero_iff.mpr (eval_ne_zero_of_dimOne h0 hP ht hz)
    have hA := (A.pos z hz.1).ne'
    unfold logNorm
    rw [← Real.log_mul (div_ne_zero hs0 ht0) (div_ne_zero ht0 hA)]
    congr 1
    field_simp
  have hpf := hPF K ι P s t b hP hsa htb hsP htP
  rw [recR_eq, recR_eq, cycR_eq_vertR_of_dimOne h0 I hP hs, cycR_eq_vertR_of_dimOne h0 I hP ht, hsplit]
  linarith

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermTensor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isSmoothHerm_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) :=
  ContDiffOn.mul hA hB

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.RegLine
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

set_option linter.unusedSectionVars false

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def secNorm (E : HermLine ι) (t : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  ‖eval z (map (Int.castRingHom ℂ) t)‖ / E.h z

theorem logNorm_eq_log_secNorm (E : HermLine ι) (t : MRing ι) (z : (Σ k, ι k) → ℂ) :
    logNorm E t z = Real.log (secNorm E t z) := rfl

theorem secNorm_smul {E : HermLine ι} {t : MRing ι} {a : K → ℕ} (hE : ∀ k, E.a k = a k)
    (ht : IsMultiHomog t a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    secNorm E t (fun p => c p.1 * z p) = secNorm E t z := by
  have he := eval_bsmul_of_isMultiHomog ht c z
  have hh : E.h (bsmul c z) = (∏ k, ‖c k‖ ^ E.a k) * E.h z := E.smul c z hc
  have hpos : 0 < ∏ k, ‖c k‖ ^ E.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
  have hn : ‖∏ k, c k ^ a k‖ = ∏ k, ‖c k‖ ^ E.a k := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow, hE k, zpow_natCast]
  change ‖eval (bsmul c z) (map (Int.castRingHom ℂ) t)‖ / E.h (bsmul c z) = _
  rw [he, hh, norm_mul, hn, mul_div_mul_left _ _ hpos.ne']
  rfl

def regLine (E : HermLine ι) (t : MRing ι) (ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a)
    (ε : ℝ) : HermLine ι :=
  HermLine.ofWeight (fun z => -(Real.log (secNorm E t z ^ 2 + ε) / 2)) (by
    intro c z hc
    obtain ⟨a, hE, hta⟩ := ht
    simp only [secNorm_smul hE hta hc z])

variable {E : HermLine ι} {t : MRing ι} {ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a}
  {ε : ℝ}

theorem regLine_a : (regLine E t ht ε).a = 0 := rfl

theorem regLine_h (z : (Σ k, ι k) → ℂ) :
    (regLine E t ht ε).h z = Real.exp (Real.log (secNorm E t z ^ 2 + ε) / 2) := by
  simp [regLine, HermLine.ofWeight]

theorem log_regLine_h (z : (Σ k, ι k) → ℂ) :
    Real.log ((regLine E t ht ε).h z) = Real.log (secNorm E t z ^ 2 + ε) / 2 := by
  rw [regLine_h, Real.log_exp]

theorem contDiff_eval_map (t : MRing ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => eval z (map (Int.castRingHom ℂ) t)) := by
  induction t using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p v hp => simpa using hp.mul (contDiff_apply ℝ (fun _ => ℂ) v)

theorem isSmoothHerm_regLine (hE : IsSmoothHerm E) (hε : 0 < ε) : IsSmoothHerm (regLine E t ht ε) := by
  unfold IsSmoothHerm
  have hn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (Σ k, ι k) → ℂ => ‖eval z (map (Int.castRingHom ℂ) t)‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_eval_map t)
  have hq : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => ‖eval z (map (Int.castRingHom ℂ) t)‖ ^ 2 / E.h z ^ 2 + ε)
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (hn.contDiffOn.div (hE.pow 2) fun z hz => pow_ne_zero _ (E.pos z hz).ne').add contDiffOn_const
  have hl := (hq.log fun z hz => (add_pos_of_nonneg_of_pos
    (div_nonneg (sq_nonneg _) (sq_nonneg _)) hε).ne').div_const 2
  refine (Real.contDiff_exp.comp_contDiffOn hl).congr fun z _ => ?_
  rw [regLine_h, secNorm, div_pow]
  rfl

theorem logNorm_le_log_regLine_h (hε : 0 ≤ ε) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (ht0 : eval z (map (Int.castRingHom ℂ) t) ≠ 0) :
    logNorm E t z ≤ Real.log ((regLine E t ht ε).h z) := by
  rw [log_regLine_h, logNorm_eq_log_secNorm]
  have hpos : 0 < secNorm E t z := div_pos (norm_pos_iff.mpr ht0) (E.pos z hz)
  have h2 : Real.log (secNorm E t z) = Real.log (secNorm E t z ^ 2) / 2 := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [h2]
  exact div_le_div_of_nonneg_right (Real.log_le_log (by positivity) (by linarith)) (by norm_num)

end Objects

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ConservationDegreeFormOfExistence
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace Conservation

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem ptsIntegral_const {e : ℕ} (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun _ => c) = c * ptsIntegral P φ (fun _ => 1) := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs <;> simp
  · simp


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem C_not_mem {P : Ideal (MRing ι)} (hP : IsHorizontal P) {a : ℤ} (ha : a ≠ 0) : C a ∉ P := by
  intro h
  have : a ∈ P.comap (C : ℤ →+* MRing ι) := Ideal.mem_comap.mpr h
  rw [show P.comap (C : ℤ →+* MRing ι) = ⊥ from hP, Ideal.mem_bot] at this
  exact ha this


omit [Fintype K] in
theorem isMultiHomog_C (a : ℤ) : IsMultiHomog (C a : MRing ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h
  · subst h; simp
  · exact absurd rfl hm


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem comap_eq_of_mem {P W : Ideal (MRing ι)} {p : ℕ} (hp : p.Prime) (hW : W ∈ divSupp P (C (p : ℤ))) :
    W.comap (C : ℤ →+* MRing ι) = Ideal.span {(p : ℤ)} := by
  have hWp : W.IsPrime := hW.1.1.1
  have hpW : (p : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) :=
    Ideal.mem_comap.mpr (hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  have hmax := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  exact (hmax.eq_of_le (Ideal.IsPrime.comap C).ne_top
    ((Ideal.span_singleton_le_iff_mem _).mpr hpW)).symm


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem not_horizontal {P W : Ideal (MRing ι)} {p : ℕ} (hp : p.Prime) (hW : W ∈ divSupp P (C (p : ℤ))) :
    ¬ IsHorizontal W := by
  intro h
  have := comap_eq_of_mem hp hW
  rw [show W.comap (C : ℤ →+* MRing ι) = ⊥ from h, eq_comm, Ideal.span_singleton_eq_bot] at this
  exact hp.ne_zero (by exact_mod_cast this)


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem charOf_eq {P W : Ideal (MRing ι)} {p : ℕ} (hp : p.Prime) (hW : W ∈ divSupp P (C (p : ℤ))) :
    charOf W = p := by
  have h := comap_eq_of_mem hp hW
  unfold charOf
  have hg : Ideal.span {Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))} =
      Ideal.span {(p : ℤ)} := by
    rw [← h]; exact Submodule.IsPrincipal.span_singleton_generator _
  rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at hg
  simpa using hg

theorem vertR_C_prime (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) {p : ℕ} (hp : p.Prime) :
    vertR P L (C (p : ℤ)) = Real.log p * ∑ V ∈ (divSupp_finite P (C (p : ℤ))).toFinset,
      (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) * (geoNum n V (fun j => (L j).a) : ℝ) := by
  unfold vertR
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [Set.Finite.mem_toFinset] at hV
  rw [if_neg (not_horizontal hp hV), charOf_eq hp hV]
  ring

end Conservation

theorem Conservation.statement_holds : Conservation.Statement := by
  unfold Conservation.Statement ConservationStatement
  intro K _ ι _ I hI P n L p hP hL hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hA : IsSmoothHerm (constLine (ι := ι) (-Real.log p)) := contDiffOn_const
  have ha : ∀ k, (constLine (ι := ι) (-Real.log p)).a k = ((0 : K → ℕ) k : ℤ) := fun _ => rfl
  have hpot : (fun j z => Real.log ((L j).h z)) = pot L := rfl
  constructor
  · rw [hI.2.2 P n L _ (C (p : ℤ)) 0 hP hL hA ha (Conservation.isMultiHomog_C _)
      (Conservation.C_not_mem hP.2.2.1 (by exact_mod_cast hp.ne_zero))]
    have hlog : logNorm (constLine (ι := ι) (-Real.log p)) (C (p : ℤ)) = fun _ => 0 := by
      funext z
      show Real.log (‖eval z (map (Int.castRingHom ℂ) (C (p : ℤ)))‖ / Real.exp (-(-Real.log p))) = 0
      rw [map_C, eval_C, neg_neg, Real.exp_log hp0]
      simp [hp0.ne']
    unfold recR vertR arInt
    rw [hlog, Conservation.ptsIntegral_const, zero_mul, sub_zero]
    refine finsum_mem_congr rfl fun W hW => ?_
    rw [if_neg (Conservation.not_horizontal hp hW), if_neg (Conservation.not_horizontal hp hW)]
  · rw [hI.2.2 P n L _ (C 1) 0 hP hL hA ha (Conservation.isMultiHomog_C _)
      (Conservation.C_not_mem hP.2.2.1 one_ne_zero)]
    have hlog : logNorm (constLine (ι := ι) (-Real.log p)) (C 1) = fun _ => -Real.log p := by
      funext z
      show Real.log (‖eval z (map (Int.castRingHom ℂ) (C 1))‖ / Real.exp (-(-Real.log p))) = _
      rw [map_C, eval_C, neg_neg, Real.exp_log hp0]
      simp [Real.log_inv]
    have hempty : divSupp P (C 1 : MRing ι) = ∅ := by
      ext W
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hW
      have hle := hW.1.1.2
      rw [C_1, Ideal.span_singleton_one, sup_top_eq, top_le_iff] at hle
      exact hW.1.1.1.ne_top hle
    unfold recR arInt
    rw [hempty, finsum_mem_empty, hlog, Conservation.ptsIntegral_const, hpot]
    ring

theorem Conservation.conservation_degree_form_of_existence (hE : ThmIExists.Statement) (hC : Conservation.Statement) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Conservation.Statement := by
  intro K _ ι _ P n L p hP hL hp
  obtain ⟨I, hI⟩ := hE
  obtain ⟨h1, h2⟩ := hC K ι (I K ι) (hI K ι) P n L p hP hL hp
  have h := h1.symm.trans h2
  rw [Conservation.vertR_C_prime P L hp] at h
  exact mul_left_cancel₀ (Real.log_pos (by exact_mod_cast hp.one_lt)).ne' h

theorem Conservation.conservation_iff_degree_statement :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Conservation.Statement ↔ DegreeStatement := by
  constructor
  · intro h K _ ι _ P e L p hP hL hp
    rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)]
    exact (h K ι P e L p hP hL hp).symm
  · intro h K _ ι _ P e L p hP hL hp
    have h' := h K ι P e L p hP hL hp
    rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)] at h'
    exact h'.symm

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ExMapAlt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

def pointFormRank_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (d n : ℕ)
    (F : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y : Fin n → ℂ),
    IsArithVar Q d → d ≤ n → AnalyticAt ℂ F y → (∀ᶠ y' in 𝓝 y, F y' ∈ mcPts Q) →
    ∃ x : Fin n → ℂ, x ≠ 0 ∧ ∃ c : K → ℂ, fderiv ℂ F y x = bsmul c (F y)

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ExMap
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

def pointFormEuler_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι) (n : ℕ)
    (F : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y x : Fin n → ℂ) (c : K → ℂ),
    IsSmoothHerm A → AnalyticAt ℂ F y → (∀ k, ∃ i, F y ⟨k, i⟩ ≠ 0) → fderiv ℂ F y x = bsmul c (F y) →
    cxHessian (fun y' => Real.log (A.h (F y'))) y *ᵥ star x = 0

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StHorizNotMem
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def HorizNotMem.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (s s' : MRing ι) (W : Ideal (MRing ι)),
    IsArithVar P d → s ∉ P → s' ∉ P →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    W ∈ divSupp P s → IsHorizontal W → s' ∉ W

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StSheetHessPSD
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped ComplexOrder

def SheetHessPSD.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (M : HermLine ι) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ),
    IsSmoothHerm M → IsSemiPosHerm M → IsSheet P Ψ y w γ →
    (cxHessian (fun y' => Real.log (M.h (γ y'))) y).PosSemidef

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAddFirst
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PtsAddFirst.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → HermLine ι) (M N E : HermLine ι) (t : MRing ι),
    IsArithVar Q (e + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm M → IsSmoothHerm N →
    IsSmoothHerm E → IsSectionOn Q E t →
    ptsIntegral Q (Fin.cons (fun z => Real.log ((M.tensor N).h z)) (pot L)) (logNorm E t) =
      ptsIntegral Q (Fin.cons (fun z => Real.log (M.h z)) (pot L)) (logNorm E t) +
        ptsIntegral Q (Fin.cons (fun z => Real.log (N.h z)) (pot L)) (logNorm E t)

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StRatioAlgDep
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def RatioAlgDep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (d : ℕ)
    (c : ∀ k, ι k) (p : Fin d → Σ k, ι k),
    IsArithVar Q d →
    ∃ f : MvPolynomial (Fin d) ℤ, f ≠ 0 ∧
      ∀ z : (Σ k, ι k) → ℂ, (∀ g ∈ Q, eval z (map (Int.castRingHom ℂ) g) = 0) →
        (∀ k, z ⟨k, c k⟩ ≠ 0) →
          eval (fun j => z (p j) / z ⟨(p j).1, c (p j).1⟩) (map (Int.castRingHom ℂ) f) = 0

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagFormDiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalFormDivisor

set_option linter.unusedSectionVars false

section Generic

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]

theorem aeval_scale (u : K → Φ) (c : (Σ k, ι k) → Φ) (s : MRing ι) (β : K → ℕ) (hs : IsMultiHomog s β) :
    aeval (fun p => u p.1 * c p) s = (∏ k, u k ^ β k) * aeval c s := by
  have h1 := congrArg (MvPolynomial.eval u) (DiagRAux.multiConeMap_of_homog c s β hs)
  have h2 : (MvPolynomial.eval u).comp (T.multiConeMap c) =
      (aeval (fun p => u p.1 * c p) : MRing ι →ₐ[ℤ] Φ).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp [T.multiConeMap]) (fun p => by simp [T.multiConeMap, mul_comm])
  rw [← RingHom.comp_apply, h2, map_mul, eval_C, map_prod] at h1
  simp only [map_pow, eval_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1
  rw [h1, mul_comm]

end Generic

section Geometry

variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
  [Algebra Ω Φ]

end Geometry

end DiagonalFormDivisor


end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.DeEqZeroOfSemiPosOff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {n : ℕ}
  {A A' : HermLine ι} {s s' : MRing ι}

theorem De_eq_zero_of_semiPos (hLe : DeLeSemiPos.Statement) {L : Fin n → HermLine ι}
    (hP : IsArithVar P (n + 2)) (hL : ∀ j, IsSmoothHerm (L j)) (hLp : ∀ j, IsSemiPosHerm (L j))
    (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A') (hs : IsSectionOn P A s) (hs' : IsSectionOn P A' s')
    (hnc : ∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) :
    De P L A A' s s' = 0 := by
  have h1 := hLe K ι P n L A A' s s' hP hL hLp hA hA' hs hs' hnc
  have h2 := hLe K ι P n L A' A s' s hP hL hLp hA' hA hs' hs (fun W h h' => hnc W h' h)
  rw [De_swap] at h2
  linarith

theorem De_eq_zero_of_semiPos_off (hAdd : DeSlotAdd.Statement) (hTw : SemiPosTwist.Statement)
    (hLe : DeLeSemiPos.Statement) (hP : IsArithVar P (n + 2)) (hA : IsSmoothHerm A)
    (hA' : IsSmoothHerm A') (hs : IsSectionOn P A s) (hs' : IsSectionOn P A' s')
    (hnc : ∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) (S : Finset (Fin n)) :
    ∀ L : Fin n → HermLine ι, (∀ j, IsSmoothHerm (L j)) → (∀ j, j ∉ S → IsSemiPosHerm (L j)) →
      De P L A A' s s' = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro L hL hLp
    exact De_eq_zero_of_semiPos hLe hP hL (fun j => hLp j (Finset.notMem_empty j)) hA hA' hs hs' hnc
  | @insert j S hj ih =>
    intro L hL hLp
    obtain ⟨T, hT, hTp, hLTp⟩ := hTw K ι (L j) (hL j)
    have hadd := hAdd K ι P n L j (L j) T A A' s s' hP hL (hL j) hT hA hA' hs hs' hnc
    rw [Function.update_eq_self] at hadd
    have hsm : ∀ X : HermLine ι, IsSmoothHerm X → ∀ i, IsSmoothHerm (Function.update L j X i) := by
      intro X hX i
      rcases eq_or_ne i j with rfl | hij
      · simpa using hX
      · rw [Function.update_of_ne hij]
        exact hL i
    have hpos : ∀ X : HermLine ι, IsSemiPosHerm X → ∀ i, i ∉ S →
        IsSemiPosHerm (Function.update L j X i) := by
      intro X hX i hi
      rcases eq_or_ne i j with rfl | hij
      · simpa using hX
      · rw [Function.update_of_ne hij]
        exact hLp i (by simp [Finset.mem_insert, hij, hi])
    rw [ih _ (hsm _ (isSmoothHerm_tensor (hL j) hT)) (hpos _ hLTp),
      ih _ (hsm _ hT) (hpos _ hTp)] at hadd
    linarith

theorem ProjectiveLineTwo.proof (hAdd : DeSlotAdd.Statement) (hTw : SemiPosTwist.Statement)
    (hLe : DeLeSemiPos.Statement) : SectionSpaceSymmetry := by
  intro K _ ι _ P n L A A' s s' hP hL hA hA' hs hs' hnc
  have h := De_eq_zero_of_semiPos_off hAdd hTw hLe hP hA hA' hs hs' hnc Finset.univ L hL
    (fun j hj => absurd (Finset.mem_univ j) hj)
  unfold De at h
  linarith

end GroundTheory.Heights₂.Heights.Inter
end
