module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatNoetherFrame
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResVolume
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreDim
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConjInvariantHZcomb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Topology
open GroundTheory.Heights₂.Heights.Inter (famExt famExt_apply famExt_basis hermZpow hermLine_eq_of isSmoothHerm_tensor
  isSmoothHerm_hermZpow fam_update_eq_snoc fam_snoc_zpow isSmoothHerm_ofMetrics_fs)

noncomputable section

set_option linter.unusedSectionVars false

section Scaling

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem zcomb_eq_tensor (A X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (q : ℕ) :
    HermLine.zcomb A X q 1 = (hermZpow A q).tensor X :=
  hermLine_eq_of (by funext k; simp [HermLine.zcomb, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, hermZpow])
    (by funext z; simp [HermLine.zcomb, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, hermZpow])

theorem isSmoothHerm_zcomb {A X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (q : ℕ) :
    IsSmoothHerm (HermLine.zcomb A X q 1) := by
  rw [zcomb_eq_tensor]
  exact isSmoothHerm_tensor (isSmoothHerm_hermZpow hA q) hX

theorem isConjInvariantH_zcomb {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsConjInvariantH A) (hB : IsConjInvariantH B) (p q : ℤ) :
    IsConjInvariantH (HermLine.zcomb A B p q) := by
  intro z
  show A.h _ ^ p * B.h _ ^ q = A.h z ^ p * B.h z ^ q
  rw [hA z, hB z]

theorem isConjInvariantH_fsH : IsConjInvariantH (fsH ι) := by
  intro z
  simp [fsH, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]

variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}

theorem fam_update_zcomb (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (a : Fin (n + 1)) {A X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (q : ℕ) :
    I P (n + 1) (Function.update L a (HermLine.zcomb A X q 1)) =
      q * I P (n + 1) (Function.update L a A) + I P (n + 1) (Function.update L a X) := by
  rw [zcomb_eq_tensor]
  have hAq := isSmoothHerm_hermZpow hA (q : ℤ)
  have hR : ∀ i : Fin n, IsSmoothHerm ((fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) i) :=
    fun i => hL _
  rw [fam_update_eq_snoc hI hP L hL a (isSmoothHerm_tensor hAq hX), fam_update_eq_snoc hI hP L hL a hA,
    fam_update_eq_snoc hI hP L hL a hX, hI.2.1 P n _ _ _ hP hR hAq hX, fam_snoc_zpow hI hP _ hR hA (q : ℤ)]
  push_cast
  ring

theorem fam_eq_famExt_zcomb (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {A X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (q : ℕ) (T : Finset (Fin (n + 1))) (t : Fin (n + 1) → Fin 2) :
    I P (n + 1) (fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (t j)) =
      famExt I P (n + 1) ![X, A] (fun j => if j ∈ T then ![1, (q : ℝ)] else Pi.single (t j) 1) := by
  have hsm : ∀ i, IsSmoothHerm (![X, A] i) := Fin.forall_fin_two.mpr ⟨hX, hA⟩
  induction T using Finset.induction_on generalizing t with
  | empty =>
    simp only [Finset.notMem_empty, if_false]
    exact (famExt_basis ![X, A] t).symm
  | insert a T ha ih =>
    have hins : ∀ {β : Type} (w : β) (F : Fin 2 → β),
        (fun j => if j ∈ insert a T then w else F (t j)) =
          Function.update (fun j => if j ∈ T then w else F (t j)) a w := by
      intro β w F
      funext j
      rcases eq_or_ne j a with rfl | h
      · simp
      · simp [h]
    have hupd : ∀ {β : Type} (w : β) (F : Fin 2 → β) (i : Fin 2),
        Function.update (fun j => if j ∈ T then w else F (t j)) a (F i) =
          fun j => if j ∈ T then w else F (Function.update t a i j) := by
      intro β w F i
      funext j
      rcases eq_or_ne j a with rfl | h
      · simp [ha]
      · simp [Function.update_of_ne h]
    have hL : ∀ j, IsSmoothHerm ((fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (t j)) j) := by
      intro j
      dsimp only
      split_ifs
      · exact isSmoothHerm_zcomb hA hX q
      · exact hsm (t j)
    have eL : (fun j => if j ∈ insert a T then HermLine.zcomb A X q 1 else ![X, A] (t j)) =
        Function.update (fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (t j)) a
          (HermLine.zcomb A X q 1) :=
      hins _ _
    have eV : (fun j => if j ∈ insert a T then (![1, (q : ℝ)] : Fin 2 → ℝ) else Pi.single (t j) 1) =
        Function.update (fun j => if j ∈ T then (![1, (q : ℝ)] : Fin 2 → ℝ) else Pi.single (t j) 1) a
          ![1, (q : ℝ)] :=
      hins (![1, (q : ℝ)] : Fin 2 → ℝ) fun i => Pi.single i 1
    have hA1 : Function.update (fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (t j)) a A =
        fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (Function.update t a 1 j) :=
      hupd _ ![X, A] 1
    have hX0 : Function.update (fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (t j)) a X =
        fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (Function.update t a 0 j) :=
      hupd _ ![X, A] 0
    have hV1 : Function.update (fun j => if j ∈ T then (![1, (q : ℝ)] : Fin 2 → ℝ) else Pi.single (t j) 1) a
        (Pi.single 1 1) = fun j => if j ∈ T then ![1, (q : ℝ)] else Pi.single (Function.update t a 1 j) 1 :=
      hupd (![1, (q : ℝ)] : Fin 2 → ℝ) (fun i => Pi.single i 1) 1
    have hV0 : Function.update (fun j => if j ∈ T then (![1, (q : ℝ)] : Fin 2 → ℝ) else Pi.single (t j) 1) a
        (Pi.single 0 1) = fun j => if j ∈ T then ![1, (q : ℝ)] else Pi.single (Function.update t a 0 j) 1 :=
      hupd (![1, (q : ℝ)] : Fin 2 → ℝ) (fun i => Pi.single i 1) 0
    have hw : (![1, (q : ℝ)] : Fin 2 → ℝ) = (q : ℝ) • Pi.single 1 1 + (1 : ℝ) • Pi.single 0 1 := by
      funext i
      fin_cases i <;> simp
    rw [eL, eV, fam_update_zcomb hI hP _ hL a hA hX q, hA1, hX0, ih, ih,
      congrArg (Function.update (fun j => if j ∈ T then (![1, (q : ℝ)] : Fin 2 → ℝ) else Pi.single (t j) 1) a) hw,
      MultilinearMap.map_update_add, MultilinearMap.map_update_smul, MultilinearMap.map_update_smul, hV1, hV0,
      smul_eq_mul, smul_eq_mul]
    simp only [RingHom.id_apply]
    ring

theorem tendsto_fam_zcomb (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {A X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) :
    Tendsto (fun q : ℕ => I P (n + 1) (fun _ => HermLine.zcomb A X q 1) / (q : ℝ) ^ (n + 1)) atTop
      (𝓝 (I P (n + 1) (fun _ => A))) := by
  have hfull : ∀ q : ℕ, I P (n + 1) (fun _ => HermLine.zcomb A X q 1) =
      famExt I P (n + 1) ![X, A] (fun _ => ![1, (q : ℝ)]) := by
    intro q
    simpa using fam_eq_famExt_zcomb hI hP hA hX q Finset.univ (fun _ => 0)
  have hscale : ∀ q : ℕ, q ≠ 0 → famExt I P (n + 1) ![X, A] (fun _ => ![1, (q : ℝ)]) / (q : ℝ) ^ (n + 1) =
      famExt I P (n + 1) ![X, A] (fun _ => ![1 / (q : ℝ), 1]) := by
    intro q hq
    have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
    have e : (fun _ : Fin (n + 1) => (![1, (q : ℝ)] : Fin 2 → ℝ)) =
        fun i => (fun _ : Fin (n + 1) => (q : ℝ)) i • (![1 / (q : ℝ), 1] : Fin 2 → ℝ) := by
      funext i j
      fin_cases j <;> simp [hq']
    rw [e, MultilinearMap.map_smul_univ, smul_eq_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    field_simp
    simp only [RingHom.id_apply]
    ring
  have hlim : Tendsto (fun q : ℕ => famExt I P (n + 1) ![X, A] (fun _ => ![1 / (q : ℝ), 1])) atTop
      (𝓝 (famExt I P (n + 1) ![X, A] (fun _ => ![0, 1]))) := by
    simp only [famExt_apply]
    refine tendsto_finsetSum _ fun s _ => Tendsto.const_mul _ (tendsto_finsetProd _ fun j _ => ?_)
    generalize s j = i
    fin_cases i
    · simpa using (tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun q : ℕ => 1 / (q : ℝ)) atTop (𝓝 0))
    · simp
  have hval : famExt I P (n + 1) ![X, A] (fun _ => ![0, 1]) = I P (n + 1) (fun _ => A) := by
    have e : (fun _ : Fin (n + 1) => (![0, 1] : Fin 2 → ℝ)) = fun j => Pi.single ((fun _ => (1 : Fin 2)) j) 1 := by
      funext j i
      fin_cases i <;> simp
    rw [e, famExt_basis]
    rfl
  rw [hval] at hlim
  refine hlim.congr' ((eventually_ge_atTop 1).mono fun q hq => ?_)
  dsimp only
  rw [hfull, hscale q (by omega)]

end Scaling

theorem ArithmeticVolumeNef.proof (hS : MonomialShift.Statement) (hPM : PerturbMonomial.Statement)
    (hU : UpperNormalisation.Statement) : ArithmeticVolumeNef.Statement := by
  intro K _ ι _ Ω _ y D a A P0 II hD hII hY hbir ha hP0 hsemi hmon hconj
  set F : ℝ := ((D + 1).factorial : ℝ) with hF
  have hFpos : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos _
  let f : ℕ → ℝ := fun τ =>
    smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ / ((τ : ℝ) ^ (D + 1) / F)
  show limsup f atTop ≤ II K ι (mCoordIdeal y) (D + 1) (fun _ => A)
  have hcnt : ∀ (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (La : ℕ → AddSubgroup Ω) (τ : ℕ),
      0 ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y B) La τ := fun B La τ => by
    unfold smallSectionCount
    exact Real.log_natCast_nonneg _
  have hf0 : ∀ τ, 0 ≤ f τ := fun τ => div_nonneg (hcnt _ _ _) (div_nonneg (by positivity) hFpos.le)

  have key : ∀ q : ℕ, 1 ≤ q → ∀ ε : ℝ, 0 < ε → limsup f atTop ≤
      (II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.zcomb A (fsH ι) q 1) + ε) / (q : ℝ) ^ (D + 1) := by
    intro q hq ε hε
    set B := HermLine.zcomb A (fsH ι) q 1 with hBdef
    set c := II K ι (mCoordIdeal y) (D + 1) (fun _ => B) + ε with hc
    have hsg : IsSmallGeneratedDatum P0 y D B := hPM K ι Ω y D a A P0 q hD hY hbir ha hP0 hsemi hmon hq
    have hBconj : IsConjInvariantH B := isConjInvariantH_zcomb hconj isConjInvariantH_fsH _ _
    have hBa : ∀ k, 1 ≤ B.a k := by
      intro k
      simp only [hBdef, HermLine.zcomb, fsH, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics, ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.one_apply, mul_one]
      nlinarith [show (0 : ℤ) ≤ (q : ℤ) * (a k : ℤ) by positivity]
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hU K ι Ω y D B P0 II hD hII hY hbir hsg hBconj hBa ε hε)
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hbound : ∀ᶠ τ : ℕ in atTop, f τ ≤ c / (q : ℝ) ^ (D + 1) * (1 + q / (τ : ℝ)) ^ (D + 1) := by
      filter_upwards [eventually_ge_atTop (q * N + 1)] with τ hτ
      have hτpos : (0 : ℝ) < τ := by exact_mod_cast (show 0 < τ by omega)
      have hdm := Nat.div_add_mod τ q
      have hmod := Nat.mod_lt τ (show 0 < q by omega)
      have hqn : τ ≤ q * (τ / q + 1) := by rw [Nat.mul_add, mul_one]; omega
      have hnN : N ≤ τ / q + 1 := by
        have : N ≤ τ / q := (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; omega)
        omega
      have hnq : (((τ / q + 1 : ℕ) : ℝ)) * q ≤ τ + q := by
        have := Nat.div_mul_le_self τ q
        have h' : (τ / q + 1) * q ≤ τ + q := by rw [Nat.add_mul, one_mul]; omega
        exact_mod_cast h'
      have h1 : smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ ≤
          c * ((((τ / q + 1 : ℕ) : ℝ)) ^ (D + 1) / F) :=
        (hS K ι Ω y D a A P0 q τ (τ / q + 1) hY hbir ha hP0 hsemi hmon hq hqn).trans (hN _ hnN)
      have hc0 : 0 ≤ c := by
        have hpos : 0 < (((τ / q + 1 : ℕ) : ℝ)) ^ (D + 1) / F := by positivity
        exact (mul_nonneg_iff_of_pos_right hpos).mp ((hcnt _ _ _).trans h1)
      have hnle : (((τ / q + 1 : ℕ) : ℝ)) ≤ (τ + q) / q := by rw [le_div_iff₀ hqpos]; exact hnq
      have h2 : (((τ / q + 1 : ℕ) : ℝ)) ^ (D + 1) ≤ ((τ + q) / q) ^ (D + 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hnle _
      have e : c / (q : ℝ) ^ (D + 1) * (1 + q / (τ : ℝ)) ^ (D + 1) =
          c * ((((τ : ℝ) + q) / q) ^ (D + 1) / F) / ((τ : ℝ) ^ (D + 1) / F) := by
        rw [show (1 : ℝ) + q / τ = (τ + q) / τ by field_simp]
        simp only [div_pow]
        field_simp
      show smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ / ((τ : ℝ) ^ (D + 1) / F) ≤ _
      rw [e, div_le_div_iff_of_pos_right (by positivity)]
      calc _ ≤ c * ((((τ / q + 1 : ℕ) : ℝ)) ^ (D + 1) / F) := h1
        _ ≤ c * ((((τ : ℝ) + q) / q) ^ (D + 1) / F) := by gcongr
    have hlim : Tendsto (fun τ : ℕ => c / (q : ℝ) ^ (D + 1) * (1 + q / (τ : ℝ)) ^ (D + 1)) atTop
        (𝓝 (c / (q : ℝ) ^ (D + 1))) := by
      have h0 : Tendsto (fun τ : ℕ => (q : ℝ) / τ) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h0).pow (D + 1) |>.const_mul (c / (q : ℝ) ^ (D + 1))
    calc limsup f atTop ≤ limsup (fun τ : ℕ => c / (q : ℝ) ^ (D + 1) * (1 + q / (τ : ℝ)) ^ (D + 1)) atTop :=
          limsup_le_limsup hbound (isCoboundedUnder_le_of_le atTop hf0) hlim.isBoundedUnder_le
      _ = c / (q : ℝ) ^ (D + 1) := hlim.limsup_eq

  have hT := tendsto_fam_zcomb (hII K ι) hY hsemi.1 (show IsSmoothHerm (fsH ι) from isSmoothHerm_ofMetrics_fs 1)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hev : ∀ᶠ q : ℕ in atTop, limsup f atTop - ε ≤
      II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.zcomb A (fsH ι) q 1) / (q : ℝ) ^ (D + 1) := by
    filter_upwards [eventually_ge_atTop 1] with q hq
    have hk := key q hq ε hε
    have hq1 : (1 : ℝ) ≤ (q : ℝ) ^ (D + 1) := one_le_pow₀ (by exact_mod_cast hq)
    have hεq : ε / (q : ℝ) ^ (D + 1) ≤ ε := div_le_self hε.le hq1
    rw [add_div] at hk
    linarith
  have := ge_of_tendsto hT hev
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNmSectionsRankBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def NmSectionsRankBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ τ : ℕ, Module.Finite ℤ (chartLatNm y a τ)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℕ, (Module.finrank ℤ (chartLatNm y a τ) : ℝ) ≤ C * ((τ : ℝ) + 1) ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartLatQCech
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ChartLatQCech.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (b : K → ℤ),
    IsArithVar (mCoordIdeal y) d →
    Nonempty (chartLatQ y b 1 ≃ₗ[ℚ]
      KH.cechHc ι (KH.quotPart ℚ ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))) b 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenerationOfH1Vanishing.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ),
    IsNoetherianRing S →
    (∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
      (𝓜 : (K → ℤ) → Submodule S M),
      Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
      ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1)) →
    H1GenAmple S V N

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartDenominator
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ChartDenominator.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (b : K → ℤ) (τ : ℕ) (s : Ω),
    s ∈ chartLatQ y b τ → ∃ n : ℕ, 1 ≤ n ∧ (n : Ω) * s ∈ chartLat y b τ

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockImageArith.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (r : ℕ) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (x : Ix (Fin r) → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsBlockImage y k₀ M N x →
      LinearIndependent ℤ x → IsArithVar (ι := GlobalTheory (Fin r)) (coordIdeal ℤ x) (D + 1)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormPullback
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormPullback.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∃ (n : ℕ) (M₀ : ℝ), 1 ≤ n ∧ 1 ≤ M₀ ∧
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, s ≠ 0 →
        ∃ F : MvPolynomial (Fin (D + 1)) ℤ, F ≠ 0 ∧ F.IsHomogeneous (n * q * τ) ∧
          ∀ ζ : Fin (D + 1) → ℂ, ζ ≠ 0 →
          ∀ S : Finset ((Σ k, ι k) → ℂ),
            (∀ z ∈ mcPts (mCoordIdeal y),
              (∃ t : ℂ, ∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) →
              ∃ z' ∈ S, ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * z' p) →
          ∀ M : ℝ, 0 ≤ M →
            (∀ z ∈ S, z ∈ mcPts (mCoordIdeal y) →
              ∃ (dg dh : K → ℕ) (g h : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g dg ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h dh ∧
                (∀ k, dg k = dh k + τ * (q * e k)) ∧ aeval y g = s * aeval y h ∧
                eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
                ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
                  M * ‖fun j => eval z (map (Int.castRingHom ℂ) (L j))‖ ^ (q * τ) *
                    ‖eval z (map (Int.castRingHom ℂ) h)‖) →
            ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ M₀ ^ τ * ‖ζ‖ ^ (n * q * τ) * M ^ n


end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem GenericFibre.proof : GenericFibre.Statement := by
  intro Ω _ _ κ _ x D hP
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : (coordIdeal ℤ x).IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Ix κ) ℤ) ∈ coordIdeal ℤ x → m = 0 := by
    intro m hm
    have h1 : m ∈ (coordIdeal ℤ x).comap (C : ℤ →+* MRing (GlobalTheory κ)) := hm
    rw [show (coordIdeal ℤ x).comap (C : ℤ →+* MRing (GlobalTheory κ)) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec (coordIdeal ℤ x) hchar
  have hq : ReciprocityTheory.AnForm.R.extQ (coordIdeal ℤ x) =
      (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff]
    refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [hq, hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · rw [hdim] at hform
    simp only [Fintype.card_unit] at hform
    refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq (D + 1) _ ?_
    rw [hform]
    push_cast
    rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNonvanishingDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem NonvanishingDense.aeval_map_rat {σ : Type} (z : σ → ℂ) (g : MvPolynomial σ ℤ) :
    aeval z (map (Int.castRingHom ℚ) g) = eval z (map (Int.castRingHom ℂ) g) := by
  rw [aeval_def, eval₂_map, eval_map]
  congr 1

theorem NonvanishingDense.proof (h : RatPrimeDense.Statement) : NonvanishingDense.Statement := by
  intro K _ ι _ P d f hP hf z hz
  obtain ⟨_, ⟨hprime, -, -⟩, hhor, -⟩ := hP
  let _ : Algebra (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) := algebraMvPolynomial
  have hφ : ∀ g, algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) g =
      map (Int.castRingHom ℚ) g := fun g => by
    change map (algebraMap ℤ ℚ) g = _
    congr 1
  have hdisj : Disjoint ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)) : Set (MRing ι)) ↑P := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, hn, rfl⟩ hnP
    have : n ∈ P.comap (C : ℤ →+* MRing ι) := hnP
    rw [hhor, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hn this
  set Pq := Ideal.map (algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ)) P
  have hPq : Pq.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint ((nonZeroDivisors ℤ).map C) _ P hprime hdisj
  have hunder : Pq.comap (algebraMap _ _) = P :=
    IsLocalization.under_map_of_isPrime_disjoint ((nonZeroDivisors ℤ).map C) _ hprime hdisj
  have hfq : map (Int.castRingHom ℚ) f ∉ Pq := fun h' => hf (by
    rw [← hunder, Ideal.mem_comap, hφ]; exact h')

  have hzero : ∀ w : (Σ k, ι k) → ℂ, (∀ g ∈ P, eval w (map (Int.castRingHom ℂ) g) = 0) →
      ∀ g ∈ Pq, aeval w g = 0 := by
    intro w hw g hg
    have hle : Pq ≤ RingHom.ker (aeval w : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] ℂ).toRingHom := by
      refine Ideal.map_le_iff_le_comap.mpr fun g' hg' => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, hφ]
      change aeval w (map (Int.castRingHom ℚ) g') = 0
      rw [NonvanishingDense.aeval_map_rat]
      exact hw g' hg'
    exact hle hg
  have hz' : z ∈ closure {w : (Σ k, ι k) → ℂ | (∀ g ∈ Pq, aeval w g = 0) ∧
      aeval w (map (Int.castRingHom ℚ) f) ≠ 0} := h _ Pq _ hPq hfq (hzero z hz.2)
  have hU : IsOpen {w : (Σ k, ι k) → ℂ | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  refine closure_mono ?_ (hU.inter_closure ⟨hz.1, hz'⟩)
  rintro w ⟨hwU, hwP, hwf⟩
  refine ⟨⟨hwU, fun g hg => ?_⟩, ?_⟩
  · rw [← NonvanishingDense.aeval_map_rat, ← hφ]
    exact hwP _ (Ideal.mem_map_of_mem _ hg)
  · rwa [← NonvanishingDense.aeval_map_rat]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTopConstantTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

set_option linter.unusedSectionVars false

namespace TopConstantTwistAlt

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

theorem cxHessian_add_const (f : (Fin e → ℂ) → ℝ) (C : ℝ) (y : Fin e → ℂ) :
    cxHessian (fun y' => f y' + C) y = cxHessian f y := by
  have h : fderiv ℝ (fun y' => f y' + C) = fderiv ℝ f := funext fun _ => fderiv_add_const _
  unfold cxHessian
  rw [h]

theorem ptsIntegral_congr_add_const (P : Ideal (MRing ι)) (φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (C : Fin e → ℝ) (h : ∀ j z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → φ j z = φ' j z + C j)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : ptsIntegral P φ g = ptsIntegral P φ' g := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    congr 1
    funext y
    refine finsum_congr fun w => finsum_congr fun _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · congr 1
      unfold maDensity
      congr 3
      funext j
      have hev : (fun y' => φ j (hγ.choose y')) =ᶠ[𝓝 y] (fun y' => φ' j (hγ.choose y') + C j) := by
        filter_upwards [hγ.choose_spec.2] with y' hy'
        exact h j _ hy'.2.1.1
      rw [cxHessian_congr hev, cxHessian_add_const]
    · rfl
  · rfl

theorem ptsIntegral_const_weight (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun _ => c) = c * ptsIntegral P φ (fun _ => 1) := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
    refine finsum_congr fun w => ?_
    congr 1
    funext _
    unfold sheetDensity
    split_ifs <;> ring
  · ring

theorem ptsIntegral_twist_term (P : Ideal (MRing ι)) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) (D i : ℕ) :
    ptsIntegral P (pot fun j : Fin D => if (j : ℕ) < i then A.tensor (constLine c) else A) (fun _ => c) =
      c * geomDeg P A D := by
  rw [ptsIntegral_const_weight, geomDeg]
  congr 1
  refine ptsIntegral_congr_add_const P _ _ (fun j => if (j : ℕ) < i then -c else 0) (fun j z hz => ?_) _
  unfold pot
  dsimp only
  split_ifs
  · show Real.log (A.h z * Real.exp (-c)) = Real.log (A.h z) + -c
    rw [Real.log_mul (A.pos z hz).ne' (Real.exp_pos _).ne', Real.log_exp]
  · simp

end TopConstantTwistAlt


open TopConstantTwistAlt in
theorem TopConstantTwist.proof : TopConstantTwist.Statement := by
  intro K _ ι _ P D A c II hII hP hA
  have h : II K ι P (D + 1) (fun _ => A.tensor (constLine c)) - II K ι P (D + 1) (fun _ => A) =
      -∑ i ∈ Finset.range (D + 1),
        ptsIntegral P (pot fun j : Fin D => if (j : ℕ) < i then A.tensor (constLine c) else A) (fun _ => c) :=
    GroundTheory.Heights₂.Heights.Telescope.proof K ι (II K ι) (hII K ι) P D A (fun _ => c) (fun _ _ _ => rfl) hP hA
      contDiffOn_const
  simp only [ptsIntegral_twist_term, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  push_cast at h ⊢
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsScaledFSHProps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def ScaledFSHProps.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)),
    IsSemipositiveRel P0 P (scaledFSH ι) ∧ IsConjInvariantH (scaledFSH ι) ∧
      MonomialsBounded P (scaledFSH ι) (fun _ => 1)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def GeneratedPow.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (n : K → ℤ) (t : ℕ),
    KH.GeneratedV S V n → KH.GeneratedV S V (t • n)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionImageSup
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def ResolutionImageSup.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MvPolynomial (Ix κ) ℂ, f.IsHomogeneous n →
      ∀ y : d.R.X, ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockRealGramComparison
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def BlockRealGramComparison.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    (fun n => blockChi d n - blockCChi d n) =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefPlusAmpleDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def NefPlusAmpleDegree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (a : K → ℤ),
    IsArithVar P (D + 1) → NefOnGenericDeg P a →
    ∀ q : ℕ, 0 < genDeg P D ((q : ℤ) • a + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftBirationalAmple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def LiftBirationalAmple.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (N : K → ℤ) (c : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → 1 ≤ c →
    KH.AmpleV ℚ (KH.genIdeal y) (c • N - fun _ => 1) →
    ∃ q t₀ : ℕ, 1 ≤ q ∧ ∀ t : ℕ, t₀ ≤ t →
      ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * q) • N) 1) ∧
        Birational (fun p : Σ _ : Unit, Fin r => x' p.2)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftSpread
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def LiftSpread.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (N : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → KH.AmpleV ℚ (KH.genIdeal y) N →
    ∃ q m t₀ : ℕ, 1 ≤ q ∧ 1 ≤ m ∧ ∀ t : ℕ, t₀ ≤ t →
      ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * q) • N) 1) ∧
        ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (e : ℕ) (u : Fin r → Ω), (∀ j, u j ∈ chartRingZ y c) ∧
          ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-((t * q) • N) k)) = (m : Ω) ^ e

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftAtPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def LiftAtPrime.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (N : K → ℤ) (p : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → p.Prime → KH.AmpleV (ZMod p) (fibreIdeal p y) N →
    ∃ q t₀ : ℕ, 1 ≤ q ∧ ∀ t : ℕ, t₀ ≤ t →
      ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * q) • N) 1) ∧
        ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (u : Fin r → Ω) (v : Ω), (∀ j, u j ∈ chartRingZ y c) ∧
          v ∈ chartRingZ y c ∧ ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-((t * q) • N) k)) + p * v = 1

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsSide
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def H1GenerationDevissage.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ),
    IsNoetherianRing S → (∀ P : Ideal (MRingOver S ι), IsMultiProjPrime P → V ≤ P → H1GenAmple S P N) →
    H1GenAmple S V N

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenerationOfH1GenAmple.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ),
    IsMultiHomogIdeal V → H1GenAmple S V N →
    ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → KH.GeneratedV S V (e + c • N)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResChiIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ResChiIndex.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d d' : HSMDatum D Ω κ)
    (B : Matrix (Ix κ) (Ix κ) ℚ), IsInvMat B → d'.x = matAct B d.x →
    (∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), resGram d' n b = resGram d n fun k => matSubst B (b k)) →
    ∀ n : ℕ, resChi d' n - resChi d n = latLogIndex d.x d'.x n

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
