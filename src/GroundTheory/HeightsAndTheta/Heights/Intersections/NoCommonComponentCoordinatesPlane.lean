module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PGeoNumCut

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def IsSemiPosHerm (M : HermLine ι) : Prop :=
  ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ v : (Σ k, ι k) → ℂ,
    0 ≤ Δ (fun t : ℂ => Real.log (M.h (z + t • v))) 0

def De (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A A' : HermLine ι) (s s' : MRing ι) : ℝ :=
  ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (logNorm A' s')) +
      ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s)) -
    ((∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s'}) W : ℝ) * ptsIntegral W (pot L) (logNorm A s)) +
      ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s'))

theorem De_swap (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A A' : HermLine ι)
    (s s' : MRing ι) : De P L A' A s' s = -De P L A A' s s' := by
  unfold De
  ring

end Objects

def DeSlotAdd.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (j : Fin n) (M N A A' : HermLine ι) (s s' : MRing ι),
    IsArithVar P (n + 2) → (∀ i, IsSmoothHerm (L i)) → IsSmoothHerm M → IsSmoothHerm N →
    IsSmoothHerm A → IsSmoothHerm A' → IsSectionOn P A s → IsSectionOn P A' s' →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    De P (Function.update L j (M.tensor N)) A A' s s' =
      De P (Function.update L j M) A A' s s' + De P (Function.update L j N) A A' s s'

def SemiPosTwist.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (M : HermLine ι),
    IsSmoothHerm M → ∃ T : HermLine ι, IsSmoothHerm T ∧ IsSemiPosHerm T ∧ IsSemiPosHerm (M.tensor T)

def DeLeSemiPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A A' : HermLine ι) (s s' : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSemiPosHerm (L j)) →
    IsSmoothHerm A → IsSmoothHerm A' → IsSectionOn P A s → IsSectionOn P A' s' →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    De P L A A' s s' ≤ 0

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]


variable (ι) in
abbrev Family := Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ

def AllSmooth {n : ℕ} (L : Fin n → HermLine ι) : Prop := ∀ j, IsSmoothHerm (L j)

def degs {n : ℕ} (L : Fin n → HermLine ι) : Fin n → K → ℤ := fun j => (L j).a

def pots {n : ℕ} (L : Fin n → HermLine ι) : Fin n → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z => Real.log ((L j).h z)



end Objects

def Conservation.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (p : ℕ), IsArithVar P (n + 1) → AllSmooth L → p.Prime →
    ∑ V ∈ (divSupp_finite P (C (p : ℤ))).toFinset,
        (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) * (geoNum n V (degs L) : ℝ) =
      ptsIntegral P (pots L) (fun _ => 1)

section Inhabitants

abbrev GlobalTheory (n : ℕ) : Unit → Type := fun _ => Fin n

abbrev Xb (n : ℕ) (i : Fin n) : MRing (GlobalTheory n) := X ⟨(), i⟩

theorem isArithVar_bot (n : ℕ) : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (n + 1)))) (n + 1) := by
  refine ⟨⟨()⟩, ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun _ => ⟨0, ?_⟩⟩, ?_, ?_⟩
  · rw [Ideal.mem_bot]
    exact X_ne_zero _
  · exact Ideal.comap_bot_of_injective _ (C_injective _ _)
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
    simp [Nat.card_eq_fintype_card]
    exact add_comm _ _

theorem isMultiHomog_Xb (n : ℕ) (i : Fin n) : IsMultiHomog (Xb n i) fun _ => 1 := by
  intro m hm k
  rw [support_X] at hm
  simp only [Finset.mem_singleton] at hm
  subst hm
  cases k
  simp [Finsupp.single_apply]

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIUnique
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace ThmIUnique

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem recR_congr {I J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (h : ∀ W ∈ divSupp P s, IsHorizontal W → I W n L = J W n L) :
    recR I P L A s = recR J P L A s := by
  classical
  unfold recR
  congr 1
  refine finsum_mem_congr rfl fun W hW => ?_
  by_cases hh : IsHorizontal W
  · rw [if_pos hh, if_pos hh, h W hW hh]
  · rw [if_neg hh, if_neg hh]

theorem isMultiHomog_one' : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem isMultiHomog_mul' {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]


open Classical in
theorem isMultiHomog_X' (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, this, h, Pi.single_apply]

theorem isMultiHomog_pow' {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (isMultiHomog_one' (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul' ih hf

theorem isMultiHomog_coordMonomial (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) d := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ d k)
      (∑ k ∈ s, d k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (isMultiHomog_one' (ι := ι))
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact isMultiHomog_mul' (isMultiHomog_pow' (isMultiHomog_X' k (c k)) _) ih
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [e] at this

theorem coordMonomial_not_mem {P : Ideal (MRing ι)} (hP : P.IsPrime) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (d : K → ℕ) :
    (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) ∉ P := by
  intro h
  obtain ⟨k, -, hk⟩ := (hP.prod_mem_iff).mp h
  exact hc k (hP.mem_of_pow_mem _ hk)

theorem eq_of_lower {I J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsRFamily I) (hJ : IsRFamily J) {P : Ideal (MRing ι)} {m : ℕ}
    (L : Fin m → HermLine ι) (A : HermLine ι) (hP : IsArithVar P (m + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hlow : ∀ W, IsArithVar W m → I W m L = J W m L) :
    I P (m + 1) (Fin.snoc L A) = J P (m + 1) (Fin.snoc L A) := by
  classical
  have hPp : P.IsPrime := hP.2.1.1
  choose c hc using hP.2.1.2.2

  let b : K → ℕ := fun k => (-A.a k).toNat
  let e : K → ℕ := fun k => (A.a k + (b k : ℤ)).toNat
  let B : HermLine ι := HermLine.sqMetric b
  have hB : IsSmoothHerm B := isSmoothHerm_sqMetric b
  have hC : IsSmoothHerm (A.tensor B) := isSmoothHerm_tensor hA hB
  have hBa : ∀ k, B.a k = (b k : ℤ) := fun k => rfl
  have hCa : ∀ k, (A.tensor B).a k = (e k : ℤ) := by
    intro k
    have h0 : (0 : ℤ) ≤ A.a k + ((-A.a k).toNat : ℤ) := by
      rw [Int.toNat_eq_max]
      omega
    exact (Int.toNat_of_nonneg h0).symm
  let sB : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ b k
  let sC : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k
  have hsB : IsMultiHomog sB b := isMultiHomog_coordMonomial c b
  have hsC : IsMultiHomog sC e := isMultiHomog_coordMonomial c e
  have hsBP : sB ∉ P := coordMonomial_not_mem hPp c hc b
  have hsCP : sC ∉ P := coordMonomial_not_mem hPp c hc e

  have diff : ∀ F : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ, IsRFamily F →
      F P (m + 1) (Fin.snoc L A) = recR F P L (A.tensor B) sC - recR F P L B sB := by
    intro F hF
    have h1 := hF.1 P m L A B hP hL hA hB
    rw [hF.2 P m L (A.tensor B) sC e hP hL hC hCa hsC hsCP,
      hF.2 P m L B sB b hP hL hB hBa hsB hsBP] at h1
    linarith
  have hor : ∀ (X' : HermLine ι) (s : MRing ι), IsSectionOn P X' s →
      ∀ W ∈ divSupp P s, IsHorizontal W → I W m L = J W m L := fun X' s hs W hW hh =>
    hlow W ((divSuppArith K ι P m X' s W hP hs hW).1 hh)
  rw [diff I hI, diff J hJ,
    recR_congr P L (A.tensor B) sC (hor _ sC ⟨e, hCa, hsC, hsCP⟩),
    recR_congr P L B sB (hor _ sB ⟨b, hBa, hsB, hsBP⟩)]

end ThmIUnique

theorem ThmIUnique.proof (h₀ : ArithVarZeroStatement) : ThmIUnique.Statement := by
  unfold ThmIUnique.Statement UniqueStatement
  intro K _ ι _ I J hI hJ
  have key : ∀ (m : ℕ) (P : Ideal (MRing ι)) (L : Fin (m + 1) → HermLine ι), IsArithVar P (m + 1) →
      (∀ j, IsSmoothHerm (L j)) → I P (m + 1) L = J P (m + 1) L := by
    intro m
    induction m with
    | zero =>
      intro P L hP hL
      rw [← Fin.snoc_init_self L]
      exact ThmIUnique.eq_of_lower hI hJ _ _ hP (fun j => hL j.castSucc) (hL _)
        fun W hW => absurd hW (h₀ K ι W)
    | succ m ih =>
      intro P L hP hL
      rw [← Fin.snoc_init_self L]
      exact ThmIUnique.eq_of_lower hI hJ _ _ hP (fun j => hL j.castSucc) (hL _)
        fun W hW => ih W _ hW fun j => hL j.castSucc
  intro P n L hn hP hL
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact key m P L hP hL

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOrd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalOrder

section Orders

variable {K : Type} {ι : K → Type}

theorem multAt_eq_zero_of_not_le {J W : Ideal (MRing ι)} (hW : W.IsPrime) (h : ¬ J ≤ W) : multAt J W = 0 := by
  have := hW
  unfold multAt
  rw [dite_eq_left hW, Module.length_eq_zero_iff.mpr (NumbersDVR.localizedQuot_subsingleton_of_not_le _ W h)]
  rfl

theorem multAt_sup_span_eq {P W : Ideal (MRing ι)} [P.IsPrime] (hW : W.IsPrime) (hPW : P ≤ W)
    {g h u v : MRing ι} (hu : u ∉ W) (hv : v ∉ W) (hm : u * g - v * h ∈ P) :
    multAt (P ⊔ Ideal.span {g}) W = multAt (P ⊔ Ideal.span {h}) W := by
  have := hW
  have hlen : ∀ {s w : MRing ι}, w ∉ W →
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRing ι ⧸ (P ⊔ Ideal.span {w * s}))) =
        Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRing ι ⧸ (P ⊔ Ideal.span {s}))) := by
    intro s w hw
    rw [NumbersDVR.length_localizedQuot_sup_span_mul P W s (fun h' => hw (hPW h')),
      Module.length_eq_zero_iff.mpr (NumbersDVR.localizedQuot_subsingleton_of_not_le _ W
        (fun hle => hw (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self w))))), add_zero]
  have heq : P ⊔ Ideal.span {u * g} = P ⊔ Ideal.span {v * h} := by
    apply le_antisymm
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : u * g = (u * g - v * h) + v * h := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hm) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : v * h = u * g - (u * g - v * h) := by ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hm)
  unfold multAt
  rw [dite_eq_left hW, dite_eq_left hW, ← hlen (s := g) hu, heq, hlen hv]

end Orders

section Diagonal

variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]



end Diagonal

end DiagonalOrder


end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIMultilin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace ThmIMultilin

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smooth_update {n : ℕ} {L : Fin n → HermLine ι} (hL : ∀ i, IsSmoothHerm (L i)) (j : Fin n)
    {X : HermLine ι} (hX : IsSmoothHerm X) : ∀ i, IsSmoothHerm (Function.update L j X i) := by
  intro i
  by_cases h : i = j
  · subst h
    simpa using hX
  · simpa [Function.update_of_ne h] using hL i


omit [∀ k, Fintype (ι k)] in
theorem update_comp_swap {m : ℕ} (L : Fin (m + 1) → HermLine ι) (j : Fin (m + 1)) (X : HermLine ι) :
    Function.update L j X ∘ Equiv.swap j (Fin.last m) =
      Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  · have hne : Equiv.swap j (Fin.last m) i.castSucc ≠ j := by
      intro h
      have h' : Equiv.swap j (Fin.last m) i.castSucc = Equiv.swap j (Fin.last m) (Fin.last m) := by
        rw [h, Equiv.swap_apply_right]
      exact Fin.castSucc_ne_last i ((Equiv.swap j (Fin.last m)).injective h')
    simp [Function.update_of_ne hne]

end ThmIMultilin

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.JacMinorC
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

theorem pderiv_facts_charZero {F : Type*} [Field F] [CharZero F] {σ : Type*} (p : MvPolynomial σ F) (j : σ) (hj : 0 < degreeOf j p) :
    pderiv j p ≠ 0 ∧ degreeOf j (pderiv j p) < degreeOf j p ∧
      (pderiv j p).vars ⊆ p.vars := by
  classical
  have hsupp : ∀ m ∈ (pderiv j p).support, m + Finsupp.single j 1 ∈ p.support := by
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    rw [mem_support_iff]
    exact left_ne_zero_of_mul hm
  refine ⟨?_, ?_, ?_⟩
  · have : ¬ degreeOf j p < 1 := by omega
    rw [degreeOf_lt_iff one_pos] at this
    push_neg at this
    obtain ⟨m, hm, hmj⟩ := this
    have hle : Finsupp.single j 1 ≤ m := Finsupp.single_le_iff.mpr hmj
    intro h0
    have hc := congr_arg (AddMonoidAlgebra.coeff · (m - Finsupp.single j 1)) h0
    rw [coeff_pderiv, tsub_add_cancel_of_le hle, AddMonoidAlgebra.coeff_zero] at hc
    rw [mem_support_iff] at hm
    exact mul_ne_zero hm (Nat.cast_add_one_ne_zero _) hc
  · rw [degreeOf_lt_iff hj]
    intro m hm
    have := monomial_le_degreeOf j (hsupp m hm)
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  · intro i hi
    rw [MvPolynomial.mem_vars_iff_mem_support] at hi ⊢
    obtain ⟨m, hm, him⟩ := hi
    refine ⟨m + Finsupp.single j 1, hsupp m hm, ?_⟩
    rw [Finsupp.mem_support_iff] at him ⊢
    simp only [Finsupp.add_apply]
    omega

theorem exists_jacobian_minor_not_mem_charZero {F : Type} [Field F] [CharZero F] {σ : Type} [Fintype σ]
    (𝔭 : Ideal (MvPolynomial σ F)) [𝔭.IsPrime] {t : ℕ}
    (G : Fin t → MvPolynomial σ F) (hG : Ideal.span (Set.range G) = 𝔭) (d : ℕ)
    (hd : ringKrullDim (MvPolynomial σ F ⧸ 𝔭) = d) :
    ∃ (a : Fin (Fintype.card σ - d) → Fin t) (b : Fin (Fintype.card σ - d) → σ),
      Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i))) ∉ 𝔭 := by
  classical
  let A := MvPolynomial σ F ⧸ 𝔭
  haveI : IsDomain A := Ideal.Quotient.isDomain 𝔭
  let K := FractionRing A
  let π : MvPolynomial σ F →+* K := (algebraMap A K).comp (Ideal.Quotient.mk 𝔭)
  have hπ : ∀ f, π f = 0 ↔ f ∈ 𝔭 := by
    intro f
    simp only [π, RingHom.comp_apply]
    rw [IsFractionRing.to_map_eq_zero_iff (R := A) (K := K), Ideal.Quotient.eq_zero_iff_mem]
  let xb : σ → A := fun s => Ideal.Quotient.mk 𝔭 (X s)
  have hmk : Ideal.Quotient.mkₐ F 𝔭 = aeval xb := MvPolynomial.algHom_ext fun s => by
    rw [aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  have hmk' : ∀ f, Ideal.Quotient.mk 𝔭 f = aeval xb f := fun f => by
    rw [← hmk, Ideal.Quotient.mkₐ_eq_mk]

  haveI : Algebra.FiniteType F A := inferInstance
  obtain ⟨s0, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := F) (A := A)
  have hs0 : s0 = d := by
    have : (s0 : WithBot ℕ∞) = (d : WithBot ℕ∞) := hs1.symm.trans hd
    exact_mod_cast this
  subst hs0

  haveI : FaithfulSMul F A :=
    (faithfulSMul_iff_algebraMap_injective F A).mpr (algebraMap F A).injective
  have hadj : Algebra.adjoin F (Set.range xb) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, ← hmk]
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective F 𝔭 x
    exact ⟨y, rfl⟩
  haveI : Algebra.IsAlgebraic (Algebra.adjoin F (Set.range xb)) A := by
    constructor
    intro a
    have ha : a ∈ Algebra.adjoin F (Set.range xb) := by rw [hadj]; trivial
    exact isAlgebraic_algebraMap (R := Algebra.adjoin F (Set.range xb)) (A := A)
      (⟨a, ha⟩ : Algebra.adjoin F (Set.range xb))
  obtain ⟨u, hu, hub⟩ := exists_isTranscendenceBasis_subset (R := F) (Set.range xb)
  haveI : Finite u := ((Set.finite_range xb).subset hu).to_subtype
  haveI : Fintype u := Fintype.ofFinite u
  have hcardu : Fintype.card u = s0 := by
    have h1 := hub.cardinalMk_eq_trdeg
    rw [hs2, Cardinal.mk_fintype] at h1
    exact_mod_cast h1
  let g : u → σ := fun y => (hu y.2).choose
  have hg : ∀ y, xb (g y) = y := fun y => (hu y.2).choose_spec
  have hginj : Function.Injective g := by
    intro y y' h
    apply Subtype.ext
    rw [← hg y, ← hg y', h]

  have hind : ∀ Q : MvPolynomial σ F, (↑Q.vars : Set σ) ⊆ Set.range g → Q ∈ 𝔭 → Q = 0 := by
    intro Q hQ hQp
    obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range Q g hginj hQ
    have h0 : aeval ((↑) : u → A) q = 0 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, hmk', aeval_rename] at hQp
      have hfun : ((↑) : u → A) = xb ∘ g := funext fun y => (hg y).symm
      rw [hfun]
      exact hQp
    rw [hub.1.eq_zero_of_aeval_eq_zero q h0, map_zero]

  have hrel : ∀ j, j ∉ Set.range g → ∃ Q : MvPolynomial σ F,
      Q ∈ 𝔭 ∧ Q ≠ 0 ∧ (↑Q.vars : Set σ) ⊆ insert j (Set.range g) := by
    intro j hj
    let w : Option u → A := fun o => o.elim (xb j) ((↑) : u → A)
    have hw : ¬ AlgebraicIndependent F w := by
      intro h
      rw [AlgebraicIndependent.option_iff] at h
      exact h.2 (hub.isAlgebraic.isAlgebraic (xb j))
    rw [algebraicIndependent_iff] at hw
    push_neg at hw
    obtain ⟨p, hp0, hp⟩ := hw
    let h : Option u → σ := fun o => o.elim j g
    have hinj : Function.Injective h := by
      rintro (_ | y) (_ | y') hyy
      · rfl
      · exact absurd ⟨y', hyy.symm⟩ hj
      · exact absurd ⟨y, hyy⟩ hj
      · exact congr_arg some (hginj hyy)
    refine ⟨rename h p, ?_, ?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, hmk', aeval_rename]
      have hfun : xb ∘ h = w := by
        funext o
        cases o with
        | none => rfl
        | some y => exact hg y
      rw [hfun]
      exact hp0
    · exact fun h0 => hp ((rename_injective h hinj) (h0.trans (map_zero _).symm))
    · intro i hi
      have := vars_rename h p (Finset.mem_coe.mp hi)
      obtain ⟨o, -, rfl⟩ := Finset.mem_image.mp this
      cases o with
      | none => exact Set.mem_insert _ _
      | some y => exact Set.mem_insert_of_mem _ ⟨y, rfl⟩

  have hT : Fintype.card {j // j ∉ Set.range g} = Fintype.card σ - s0 := by
    rw [Fintype.card_subtype_compl, ← hcardu]
    congr 1
    rw [← Set.card_range_of_injective hginj]
  let e : {j // j ∉ Set.range g} ≃ Fin (Fintype.card σ - s0) := Fintype.equivFinOfCardEq hT
  let b : Fin (Fintype.card σ - s0) → σ := fun k => (e.symm k).1
  have hb : ∀ k, b k ∉ Set.range g := fun k => (e.symm k).2
  have hbinj : Function.Injective b := fun k k' h => e.symm.injective (Subtype.ext h)
  let M : Matrix (Fin t) (Fin (Fintype.card σ - s0)) K := Matrix.of fun i k => π (pderiv (b k) (G i))
  have hM : ∀ c, M.mulVec c = 0 → c = 0 := by
    intro c hc
    let D : MvPolynomial σ F → K := fun f => ∑ k, π (pderiv (b k) f) * c k
    have hDG : ∀ i, D (G i) = 0 := fun i => by
      have := congr_fun hc i
      simpa [Matrix.mulVec, dotProduct, M, D] using this
    have hDp : ∀ f ∈ 𝔭, D f = 0 := by
      intro f hf
      rw [← hG] at hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact hDG i
      | zero => simp [D]
      | add x y _ _ hx hy =>
        have : D (x + y) = D x + D y := by
          simp only [D, map_add (f := _), add_mul, Finset.sum_add_distrib]
        rw [this, hx, hy, add_zero]
      | smul a x hx' hx =>
        have hx0 : π x = 0 := (hπ x).2 (hG ▸ hx')
        have : D (a • x) = π a * D x := by
          simp only [D, smul_eq_mul, Derivation.leibniz, map_add (f := _), map_mul, hx0, zero_mul,
            add_zero, Finset.mul_sum, mul_assoc]
        rw [this, hx, mul_zero]
    funext k0
    let j := b k0
    have hj : j ∉ Set.range g := hb k0
    have hex : ∃ n, ∃ Q : MvPolynomial σ F, Q ∈ 𝔭 ∧ Q ≠ 0 ∧
        (↑Q.vars : Set σ) ⊆ insert j (Set.range g) ∧ degreeOf j Q = n := by
      obtain ⟨Q, h1, h2, h3⟩ := hrel j hj
      exact ⟨_, Q, h1, h2, h3, rfl⟩
    obtain ⟨Q, hQp, hQ0, hQv, hQd⟩ := Nat.find_spec hex
    have hmin : ∀ Q' : MvPolynomial σ F, Q' ∈ 𝔭 → Q' ≠ 0 →
        (↑Q'.vars : Set σ) ⊆ insert j (Set.range g) → degreeOf j Q ≤ degreeOf j Q' := by
      intro Q' h1 h2 h3
      rw [hQd]
      exact Nat.find_min' hex ⟨Q', h1, h2, h3, rfl⟩
    have hpos : 0 < degreeOf j Q := by
      by_contra h0
      push_neg at h0
      apply hQ0
      apply hind Q _ hQp
      intro i hi
      rcases hQv hi with rfl | hi'
      · exfalso
        rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support] at hi
        obtain ⟨m, hm, him⟩ := hi
        have := monomial_le_degreeOf j hm
        rw [Finsupp.mem_support_iff] at him
        omega
      · exact hi'
    obtain ⟨hd0, hdlt, hdv⟩ := pderiv_facts_charZero Q j hpos
    have hnot : π (pderiv j Q) ≠ 0 := by
      rw [Ne, hπ]
      intro hmem
      have := hmin _ hmem hd0 (fun i hi => hQv (Finset.mem_coe.mpr (hdv (Finset.mem_coe.mp hi))))
      omega
    have hDQ : D Q = π (pderiv j Q) * c k0 := by
      simp only [D]
      rw [Finset.sum_eq_single k0]
      · intro k _ hk
        have : pderiv (b k) Q = 0 := by
          apply pderiv_eq_zero_of_notMem_vars
          intro hv
          rcases hQv (Finset.mem_coe.mpr hv) with h | h
          · exact hk (hbinj h)
          · exact hb k h
        rw [this, map_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ k0) h
    have := hDp Q hQp
    rw [hDQ] at this
    simpa using (mul_eq_zero.mp this).resolve_left hnot
  obtain ⟨a, ha⟩ := ReciprocityTheory.AnForm.R.gs_exists_rows_det_ne_zero M hM
  refine ⟨a, b, fun hmem => ha ?_⟩
  have h1 := (hπ _).2 hmem
  rw [RingHom.map_det] at h1
  have hM' : M.submatrix a id = π.mapMatrix (Matrix.of fun i j => pderiv (b j) (G (a i))) := by
    ext i k
    rfl
  rw [hM']
  exact h1

section Minors

open ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {R : Type} [CommRing R]

end Minors

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsExtraAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

def VerticalEmbedding.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (f g : MRing ι) (a : K → ℕ) (x : funField P),
    IsArithVar P 1 → IsMultiHomog f a → IsMultiHomog g a → f ∉ P → g ∉ P →
    (x : FractionRing (MRing ι ⧸ P)) *
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) →
    vertR P (Fin.elim0 : Fin 0 → HermLine ι) f - vertR P (Fin.elim0 : Fin 0 → HermLine ι) g =
      ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ x‖

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagDiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalDivisor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem divCycle_of_mem {P W : Ideal (MRing ι)} {s : MRing ι} (hW : W ∈ divSupp P s) :
    divCycle P s W = multAt (P ⊔ Ideal.span {s}) W := by
  unfold divCycle
  simp [Finsupp.ofSupportFinite_coe, hW]

theorem divCycle_of_not_mem {P W : Ideal (MRing ι)} {s : MRing ι} (hW : W ∉ divSupp P s) :
    divCycle P s W = 0 := by
  unfold divCycle
  simp [Finsupp.ofSupportFinite_coe, hW]


open Classical in
theorem divCycle_eq_ite {P : Ideal (MRing ι)} [P.IsPrime] {s u : MRing ι} (hu : u ∉ P)
    (W : Ideal (MRing ι)) :
    divCycle P s W = if W ∈ divSupp P (s * u) then multAt (P ⊔ Ideal.span {s}) W else 0 := by
  by_cases hW : W ∈ divSupp P (s * u)
  · rw [if_pos hW]
    by_cases hWs : W ∈ divSupp P s
    · exact divCycle_of_mem hWs
    rw [divCycle_of_not_mem hWs]
    have hWp : W.IsPrime := hW.1.1.1
    by_cases hsW : s ∈ W
    · exfalso
      refine hWs ⟨⟨⟨hWp, sup_le (le_sup_left.trans hW.1.1.2)
        ((Ideal.span_singleton_le_iff_mem _).mpr hsW)⟩, fun Q hQ hQW => hW.1.2 ⟨hQ.1, ?_⟩ hQW⟩, hW.2⟩
      exact (sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mul_mem_right u _ (Ideal.mem_span_singleton_self s))) P).trans hQ.2
    · have hnle : ¬ P ⊔ Ideal.span {s} ≤ W := fun h => hsW (h (Ideal.mem_sup_right (Ideal.subset_span rfl)))
      unfold multAt
      rw [dite_eq_left hWp, Module.length_eq_zero_iff.mpr
        (NumbersDVR.localizedQuot_subsingleton_of_not_le _ W hnle)]
      rfl
  · rw [if_neg hW]
    refine divCycle_of_not_mem fun hWs => hW ⟨?_, hWs.2⟩
    exact NumbersDVR.mem_minimalPrimes_sup_span_mul hu hWs.1

end DiagonalDivisor


end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PWellDefined
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem divSupp_disjoint_of_not_mem {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {u a : MRing ι} (h : ∀ W ∈ divSupp P u, a ∉ W) :
    ∀ W, W ∈ divSupp P u → W ∉ divSupp P a :=
  fun W hW hW' => h W hW (hW'.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))

theorem isMultiProjPrime_of_mem_divSupp {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} (hP : IsMultiProjPrime P) {u : MRing ι} {b : K → ℕ} (hu : IsMultiHomog u b)
    {W : Ideal (MRing ι)} (hW : W ∈ divSupp P u) : IsMultiProjPrime W :=
  ⟨hW.1.isPrime, ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes hP.2.1 hu hW.1, hW.2⟩

theorem WellDefined.proof (h₁ : Swap.Statement) (h₂ : RPositionAdd.Statement) :
    WellDefined.Statement := by
  intro K _ ι _ I P n L B s t hR hA hP hL hB hs ht
  classical
  obtain ⟨bs, hbs, hsH, hsP⟩ := hs
  obtain ⟨bt, hbt, htH, htP⟩ := ht
  have hPm : IsMultiProjPrime P := hP.2.1
  set S : Set (Ideal (MRing ι)) := divSupp P s ∪ divSupp P t ∪ {P} with hSdef
  have hSf : S.Finite :=
    ((divSupp_finite P s).union (divSupp_finite P t)).union (Set.finite_singleton P)
  have hS' : ∀ W ∈ S, IsMultiProjPrime W := by
    rintro W ((hW | hW) | hW)
    · exact isMultiProjPrime_of_mem_divSupp hPm hsH hW
    · exact isMultiProjPrime_of_mem_divSupp hPm htH hW
    · rw [Set.mem_singleton_iff.mp hW]
      exact hPm
  obtain ⟨d₀, hd₀⟩ := AvoidRing.exists_form_avoid S hSf hS'
  set M := L (Fin.last n) with hM
  set k : ℕ := ∑ l, (d₀ l + (M.a l).natAbs) with hkdef
  have hk1 : ∀ l, d₀ l + (M.a l).natAbs ≤ k := fun l =>
    Finset.single_le_sum (f := fun l => d₀ l + (M.a l).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ l)
  set b : K → ℕ := fun l => (M.a l + k).toNat with hbdef
  have hb : ∀ l, (b l : ℤ) = M.a l + k := fun l =>
    Int.toNat_of_nonneg (by have := hk1 l; omega)
  have hbd : d₀ ≤ b := fun l => by
    have h1 := hk1 l
    have h2 := hb l
    show d₀ l ≤ b l
    omega
  have hkd : d₀ ≤ fun _ => k := fun l => by
    have := hk1 l
    show d₀ l ≤ k
    omega
  obtain ⟨a1, ha1H, ha1S⟩ := hd₀ b hbd
  obtain ⟨a2, ha2H, ha2S⟩ := hd₀ _ hkd
  set H : HermLine ι := HermLine.sqMetric (fun _ => k) with hH
  have hHs : IsSmoothHerm H := isSmoothHerm_sqMetric _
  have hMs : IsSmoothHerm M := hL _
  have hA1s : IsSmoothHerm (M.tensor H) := isSmoothHerm_tensor hMs hHs
  have hL' : ∀ j, IsSmoothHerm (Fin.init L j) := fun j => hL _
  have hPS : P ∈ S := Or.inr rfl
  have hsec1 : IsSectionOn P (M.tensor H) a1 :=
    ⟨b, fun l => by rw [hb l]; rfl, ha1H, ha1S P hPS⟩
  have hsec2 : IsSectionOn P H a2 := ⟨fun _ => k, fun l => rfl, ha2H, ha2S P hPS⟩
  have hsecs : IsSectionOn P B s := ⟨bs, hbs, hsH, hsP⟩
  have hsect : IsSectionOn P B t := ⟨bt, hbt, htH, htP⟩
  have d1s := divSupp_disjoint_of_not_mem fun W hW => ha1S W (Or.inl (Or.inl hW))
  have d1t := divSupp_disjoint_of_not_mem fun W hW => ha1S W (Or.inl (Or.inr hW))
  have d2s := divSupp_disjoint_of_not_mem fun W hW => ha2S W (Or.inl (Or.inl hW))
  have d2t := divSupp_disjoint_of_not_mem fun W hW => ha2S W (Or.inl (Or.inr hW))
  have e1s := h₁ K ι I P n (Fin.init L) B (M.tensor H) s a1 hR hP hL' hB hA1s hsecs hsec1 d1s
  have e1t := h₁ K ι I P n (Fin.init L) B (M.tensor H) t a1 hR hP hL' hB hA1s hsect hsec1 d1t
  have e2s := h₁ K ι I P n (Fin.init L) B H s a2 hR hP hL' hB hHs hsecs hsec2 d2s
  have e2t := h₁ K ι I P n (Fin.init L) B H t a2 hR hP hL' hB hHs hsect hsec2 d2t
  have fs := h₂ K ι I P n (Fin.init L) M H B s hA hP hL' hMs hHs hB hsecs
  have ft := h₂ K ι I P n (Fin.init L) M H B t hA hP hL' hMs hHs hB hsect
  have hLeq : L = Fin.snoc (Fin.init L) M := (Fin.snoc_init_self L).symm
  rw [hLeq]
  linarith

end

end GroundTheory.Heights₂.Heights.Inter
end
